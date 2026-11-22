import EpiFormal.WindowNoShortCFRealize

/-!
# Continued-fraction stopping-rule realization for `thm:windows` (`b = 1` prescribed-count branch)

Constructs the concrete stopped-cylinder tree `cfPrescribedTree m M par0` for any bounded
sequence of positive integers `1 ≤ m j ≤ M` and any initial parity `par0 : Bool` at the paper's
actual scale `H_j = ⌊Q_j √j⌋` (`WindowPaperScale.Hpaper`), discharging EVERY hypothesis of
`WindowPaperScale.dimH_ge_half_prescribed_paper_scale` unconditionally, and closing the
pointwise regular CF identification via `WindowCFBridge.stopped_word_tree_cf_bridge`:

1. **Stage invariant & transition (`PrescribedInv`)**:
   - Positive digits, nonempty, `4/3 * H_j ≤ u ≤ 5/2 * H_j`, `0 < v < u`, and `v < H_j`.
   - Initialized at `j0Prescribed M := max 6 (5 * Nat.fib (M + 1))` with `initWordAt` matching
     the arbitrary initial parity `par0`.
   - Each stage appends `m j - 1` ones (yielding `u_* ≤ F_{M+1} u < H_{j+1} / 2`) followed by
     any eligible digit `a ∈ Icc ⌈(4/3) T / u_*⌉ (⌊(5/2) T / u_*⌋ - 1)` (always `a ≥ 2`),
     giving `≥ j / F_{M+1}` prefix-incomparable children of length `w.length + m j`.
2. **Concrete tree & dimension discharge**:
   - `dimH_ge_half_cfPrescribedTree`: unconditional
     `ENNReal.ofReal (1 / 2) ≤ dimH (cantorSet (cfPrescribedTree m M par0) (j0Prescribed M))`.
3. **End-to-end pointwise regular CF theorems (`thm:windows` `b = 1` branch)**:
   - `mem_cantorSet_cfPrescribedTree_cf`: every `x` in the Cantor set of `cfPrescribedTree`
     is irrational in `(0, 1)` with initial parity `((cfStopIdx x j0) % 2 == 1) = par0` and
     exact window increments `cfStopIdx x (j + 1) - cfStopIdx x j = m j` for all `j ≥ j0`.
   - `prescribedIncSetAt m J0 par0`: fixed-starting-index target set (so `par0 = true` and
     `par0 = false` are provably disjoint: `prescribedIncSetAt_disjoint`), with
     `dimH_ge_half_prescribedIncSetAt` at `J0 = j0Prescribed M` (independent of `par0`) and
     `exists_start_dimH_ge_half_prescribedIncSetAt`.
   - `dimH_ge_half_prescribedIncSet`: `ENNReal.ofReal (1 / 2) ≤ dimH (prescribedIncSet m)`.
   - `dimH_ge_half_boundedIncSet`: `ENNReal.ofReal (1 / 2) ≤ dimH boundedIncSet`.

Only Lean core axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace WindowPrescribedCFRealize

open Matrix Set Filter Finset ENNReal Metric Real Cylinder WindowCFRealize WindowCFBridge
  WindowNoShortCFRealize
open scoped NNReal BigOperators Topology MeasureTheory

/-! ### Part 1: Stage invariant, prelude-of-ones, and eligible final digits -/

/-- Stage-`j` invariant for the `b = 1` prescribed-count CF construction (Paper 2 L2515–L2531). -/
def PrescribedInv (j : ℕ) (w : List ℕ) : Prop :=
  PosDigits w ∧
  w ≠ [] ∧
  (4 / 3 : ℝ) * WindowPaperScale.Hpaper j ≤ ((cfProd (0 :: w)) 1 0 : ℝ) ∧
  ((cfProd (0 :: w)) 1 0 : ℝ) ≤ (5 / 2 : ℝ) * WindowPaperScale.Hpaper j ∧
  0 < (cfProd (0 :: w)) 1 1 ∧
  (cfProd (0 :: w)) 1 1 < (cfProd (0 :: w)) 1 0 ∧
  ((cfProd (0 :: w)) 1 1 : ℝ) < WindowPaperScale.Hpaper j

/-- Starting stage `j0Prescribed M = max 6 (5 * F_{M+1})`. -/
def j0Prescribed (M : ℕ) : ℕ :=
  max 6 (5 * Nat.fib (M + 1))

theorem j0Prescribed_ge_six (M : ℕ) : 6 ≤ j0Prescribed M := le_max_left _ _

theorem initWordAt_prescribedInv (par0 : Bool) {j0 : ℕ} (hj0 : 6 ≤ j0) :
    PrescribedInv j0 (initWordAt (fun _ => par0) j0) := by
  have h := initWordAt_inv (fun _ => par0) hj0
  have hHpos := WindowPaperScale.Hpaper_pos j0
  have hv_lt4 : (4 : ℝ) * ((cfProd (0 :: initWordAt (fun _ => par0) j0)) 1 1 : ℝ) <
      ((cfProd (0 :: initWordAt (fun _ => par0) j0)) 1 0 : ℝ) := by
    exact_mod_cast h.2.2.2.2.2.2
  exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    by linarith [h.2.2.2.2.2.1, h.2.2.2.2.2.2], by linarith [h.2.2.2.2.1]⟩

/-- Prelude word after appending `m j - 1` ones to `w`. -/
def prescPrelude (m : ℕ → ℕ) (j : ℕ) (w : List ℕ) : List ℕ :=
  w ++ List.replicate (m j - 1) 1

/-- Scale ratio `X(j, w) = Hpaper (j + 1) / u_*` after appending `m j - 1` ones. -/
noncomputable def prescRatio (m : ℕ → ℕ) (j : ℕ) (w : List ℕ) : ℝ :=
  WindowPaperScale.Hpaper (j + 1) / ((cfProd (0 :: prescPrelude m j w)) 1 0 : ℝ)

/-- Lower and upper endpoints of the eligible final-digit interval. -/
noncomputable def prescDigitLo (m : ℕ → ℕ) (j : ℕ) (w : List ℕ) : ℕ :=
  Nat.ceil ((4 / 3 : ℝ) * prescRatio m j w)

noncomputable def prescDigitHi (m : ℕ → ℕ) (j : ℕ) (w : List ℕ) : ℕ :=
  Nat.floor ((5 / 2 : ℝ) * prescRatio m j w) - 1

/-- Finite set of eligible final digits `a` at stage `j → j + 1`. -/
noncomputable def prescDigits (m : ℕ → ℕ) (j : ℕ) (w : List ℕ) : Finset ℕ :=
  Finset.Icc (prescDigitLo m j w) (prescDigitHi m j w)

/-- Child word `w ++ replicate (m j - 1) 1 ++ [a]`. -/
def makePrescChild (m : ℕ → ℕ) (j : ℕ) (w : List ℕ) (a : ℕ) : List ℕ :=
  prescPrelude m j w ++ [a]

/-- Finite set of stopped child words of `w` at stage `j → j + 1`. -/
noncomputable def prescWordChild (m : ℕ → ℕ) (j : ℕ) (w : List ℕ) : Finset (List ℕ) :=
  (prescDigits m j w).image (makePrescChild m j w)

/-- Stage-`j` stopped words for the prescribed-count construction. -/
noncomputable def prescWordAtomsAux (m : ℕ → ℕ) (M : ℕ) (par0 : Bool) : ℕ → Finset (List ℕ)
  | 0 => {initWordAt (fun _ => par0) (j0Prescribed M)}
  | d + 1 => (prescWordAtomsAux m M par0 d).biUnion (prescWordChild m (j0Prescribed M + d))

noncomputable def prescWordAtoms (m : ℕ → ℕ) (M : ℕ) (par0 : Bool) (j : ℕ) : Finset (List ℕ) :=
  if j0Prescribed M ≤ j then prescWordAtomsAux m M par0 (j - j0Prescribed M) else ∅

theorem prescWordAtoms_base (m : ℕ → ℕ) (M : ℕ) (par0 : Bool) :
    prescWordAtoms m M par0 (j0Prescribed M) = {initWordAt (fun _ => par0) (j0Prescribed M)} := by
  simp [prescWordAtoms, prescWordAtomsAux]

theorem prescWordAtoms_succ (m : ℕ → ℕ) (M : ℕ) (par0 : Bool) {j : ℕ} (hj : j0Prescribed M ≤ j) :
    prescWordAtoms m M par0 (j + 1) =
      (prescWordAtoms m M par0 j).biUnion (prescWordChild m j) := by
  have hj1 : j0Prescribed M ≤ j + 1 := by omega
  have hsub : j + 1 - j0Prescribed M = (j - j0Prescribed M) + 1 := by omega
  have hadd : j0Prescribed M + (j - j0Prescribed M) = j := by omega
  simp only [prescWordAtoms, hj, hj1, ↓reduceIte, hsub, prescWordAtomsAux, hadd]

/-- Denominator upper bound after appending `m j - 1` ones: `u_* ≤ F_{M+1} * u`. -/
theorem prescPrelude_bounds {m : ℕ → ℕ} {M j : ℕ} (hm1 : 1 ≤ m j) (hmM : m j ≤ M)
    {w : List ℕ} (hw : PrescribedInv j w) :
    let w' := prescPrelude m j w
    0 < (cfProd (0 :: w')) 1 0 ∧
    0 < (cfProd (0 :: w')) 1 1 ∧
    (cfProd (0 :: w')) 1 1 < (cfProd (0 :: w')) 1 0 ∧
    ((cfProd (0 :: w')) 1 0 : ℝ) ≤
      (Nat.fib (M + 1) : ℝ) * ((cfProd (0 :: w)) 1 0 : ℝ) := by
  have hHj := WindowPaperScale.Hpaper_pos j
  have hu_posR : (0 : ℝ) < ((cfProd (0 :: w)) 1 0 : ℝ) := by linarith [hw.2.2.1]
  have hu_posZ : 0 < (cfProd (0 :: w)) 1 0 := by exact_mod_cast hu_posR
  have hv_posZ : 0 < (cfProd (0 :: w)) 1 1 := hw.2.2.2.2.1
  have hv_ltZ : (cfProd (0 :: w)) 1 1 < (cfProd (0 :: w)) 1 0 := hw.2.2.2.2.2.1
  obtain ⟨hu_le, _, hv'_pos, hv'_lt⟩ := prelude_den_bounds (m j - 1) hu_posZ hv_posZ hv_ltZ
  have hcons : (0 :: prescPrelude m j w) = (0 :: w) ++ List.replicate (m j - 1) 1 := rfl
  have hu'_eq : (cfProd (0 :: prescPrelude m j w)) 1 0 =
      (cfProd (0 :: w)) 1 0 * (Nat.fib (m j - 1 + 1) : ℤ) +
      (cfProd (0 :: w)) 1 1 * (Nat.fib (m j - 1) : ℤ) := by
    rw [hcons, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two,
      (cfProd_replicate_one (m j - 1)).1, (cfProd_replicate_one (m j - 1)).2]
  have hu'_le_fib : (cfProd (0 :: prescPrelude m j w)) 1 0 ≤
      (Nat.fib (m j + 1) : ℤ) * (cfProd (0 :: w)) 1 0 := by
    have hadd : m j + 1 = (m j - 1) + 2 := by omega
    rw [hu'_eq, hadd, Nat.fib_add_two]
    have hnn : (0 : ℤ) ≤ (Nat.fib (m j - 1) : ℤ) := by exact_mod_cast Nat.zero_le _
    push_cast
    nlinarith
  have hfib_mono : Nat.fib (m j + 1) ≤ Nat.fib (M + 1) := Nat.fib_mono (by omega)
  have hu'_le_M : ((cfProd (0 :: prescPrelude m j w)) 1 0 : ℝ) ≤
      (Nat.fib (M + 1) : ℝ) * ((cfProd (0 :: w)) 1 0 : ℝ) := by
    have h1 : ((cfProd (0 :: prescPrelude m j w)) 1 0 : ℝ) ≤
        (Nat.fib (m j + 1) : ℝ) * ((cfProd (0 :: w)) 1 0 : ℝ) := by exact_mod_cast hu'_le_fib
    have h2 : (Nat.fib (m j + 1) : ℝ) ≤ (Nat.fib (M + 1) : ℝ) := by exact_mod_cast hfib_mono
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (le_of_lt hu_posR))
  exact ⟨lt_of_lt_of_le hu_posZ hu_le, hv'_pos, hv'_lt, hu'_le_M⟩

/-- Scale ratio lower bound: `(6 / (5 F_{M+1})) * j ≤ prescRatio m j w` and `6 ≤ prescRatio`. -/
theorem prescRatio_ge {m : ℕ → ℕ} {M j : ℕ} (hj : j0Prescribed M ≤ j)
    (hm1 : 1 ≤ m j) (hmM : m j ≤ M) {w : List ℕ} (hw : PrescribedInv j w) :
    (6 / (5 * (Nat.fib (M + 1) : ℝ))) * (j : ℝ) ≤ prescRatio m j w ∧
    (6 : ℝ) ≤ prescRatio m j w := by
  have hj6 : 6 ≤ j := le_trans (j0Prescribed_ge_six M) hj
  have hHj := WindowPaperScale.Hpaper_pos j
  have hHj1 := WindowPaperScale.Hpaper_pos (j + 1)
  have hFpos : (0 : ℝ) < (Nat.fib (M + 1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos M)
  obtain ⟨hu'_posZ, _, _, hu'_le_M⟩ := prescPrelude_bounds hm1 hmM hw
  have hu'_posR : (0 : ℝ) < ((cfProd (0 :: prescPrelude m j w)) 1 0 : ℝ) := by
    exact_mod_cast hu'_posZ
  have hu'_ub : ((cfProd (0 :: prescPrelude m j w)) 1 0 : ℝ) ≤
      (Nat.fib (M + 1) : ℝ) * ((5 / 2 : ℝ) * WindowPaperScale.Hpaper j) :=
    le_trans hu'_le_M (mul_le_mul_of_nonneg_left hw.2.2.2.1 (le_of_lt hFpos))
  have hrat := WindowPaperScale.Rpaper_ge_three_mul (by omega : 1 ≤ j)
  have hstep : (6 / (5 * (Nat.fib (M + 1) : ℝ))) * (j : ℝ) ≤ prescRatio m j w := by
    unfold prescRatio
    have hdiv := div_le_div_of_nonneg_left (le_of_lt hHj1) hu'_posR hu'_ub
    have hHj_ne : WindowPaperScale.Hpaper j ≠ 0 := ne_of_gt hHj
    have hF_ne : (Nat.fib (M + 1) : ℝ) ≠ 0 := ne_of_gt hFpos
    have h1 : (6 / (5 * (Nat.fib (M + 1) : ℝ))) * (j : ℝ) ≤
        WindowPaperScale.Hpaper (j + 1) /
          ((Nat.fib (M + 1) : ℝ) * (5 / 2 * WindowPaperScale.Hpaper j)) := by
      have hmul := mul_le_mul_of_nonneg_left hrat
        (by positivity : (0 : ℝ) ≤ 2 / (5 * (Nat.fib (M + 1) : ℝ)))
      unfold WindowPaperScale.Rpaper at hmul
      have hL : 2 / (5 * (Nat.fib (M + 1) : ℝ)) * (3 * (j : ℝ)) =
          (6 / (5 * (Nat.fib (M + 1) : ℝ))) * (j : ℝ) := by ring
      have hR : 2 / (5 * (Nat.fib (M + 1) : ℝ)) *
            (WindowPaperScale.Hpaper (j + 1) / WindowPaperScale.Hpaper j) =
          WindowPaperScale.Hpaper (j + 1) /
            ((Nat.fib (M + 1) : ℝ) * (5 / 2 * WindowPaperScale.Hpaper j)) := by
        field_simp
      linarith
    linarith
  have hj5F : (5 * (Nat.fib (M + 1) : ℝ)) ≤ (j : ℝ) := by
    exact_mod_cast le_trans (le_max_right 6 (5 * Nat.fib (M + 1))) hj
  have h6 : (6 : ℝ) ≤ (6 / (5 * (Nat.fib (M + 1) : ℝ))) * (j : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hj5F
      (by positivity : (0 : ℝ) ≤ 6 / (5 * (Nat.fib (M + 1) : ℝ)))
    have hF_ne : (Nat.fib (M + 1) : ℝ) ≠ 0 := ne_of_gt hFpos
    have heq : 6 / (5 * (Nat.fib (M + 1) : ℝ)) * (5 * (Nat.fib (M + 1) : ℝ)) = 6 := by
      field_simp
    linarith
  exact ⟨hstep, le_trans h6 hstep⟩

/-- Number of eligible digits `a` is at least `j / Nat.fib (M + 1)`. -/
theorem prescDigits_card_ge {m : ℕ → ℕ} {M j : ℕ} (hj : j0Prescribed M ≤ j)
    (hm1 : 1 ≤ m j) (hmM : m j ≤ M) {w : List ℕ} (hw : PrescribedInv j w) :
    j / Nat.fib (M + 1) ≤ (prescDigits m j w).card := by
  obtain ⟨hX_j, hX_6⟩ := prescRatio_ge hj hm1 hmM hw
  set X : ℝ := prescRatio m j w
  have hlo_lt : (prescDigitLo m j w : ℝ) < (4 / 3 : ℝ) * X + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have hfl_gt : (5 / 2 : ℝ) * X - 1 < (Nat.floor ((5 / 2 : ℝ) * X) : ℝ) := by
    have := Nat.lt_floor_add_one ((5 / 2 : ℝ) * X); linarith
  have hfl_ge1 : 1 ≤ Nat.floor ((5 / 2 : ℝ) * X) := by
    have : (1 : ℝ) ≤ (Nat.floor ((5 / 2 : ℝ) * X) : ℝ) := by linarith
    exact_mod_cast this
  have hhi_gt : (5 / 2 : ℝ) * X - 2 < (prescDigitHi m j w : ℝ) := by
    unfold prescDigitHi
    rw [Nat.cast_sub hfl_ge1, Nat.cast_one]
    linarith
  have hle : prescDigitLo m j w ≤ prescDigitHi m j w := by
    have : (prescDigitLo m j w : ℝ) ≤ (prescDigitHi m j w : ℝ) := by linarith
    exact_mod_cast this
  have hcard_eq : (prescDigits m j w).card = prescDigitHi m j w + 1 - prescDigitLo m j w := by
    unfold prescDigits
    exact Nat.card_Icc _ _
  have hcardR : (5 / 6 : ℝ) * X < ((prescDigits m j w).card : ℝ) := by
    rw [hcard_eq, Nat.cast_sub (by omega : prescDigitLo m j w ≤ prescDigitHi m j w + 1)]
    push_cast
    linarith
  have hFpos : (0 : ℝ) < (Nat.fib (M + 1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos M)
  have hdiv_le : ((j / Nat.fib (M + 1) : ℕ) : ℝ) ≤ (j : ℝ) / (Nat.fib (M + 1) : ℝ) :=
    WindowMobiusCount.nat_div_cast_upper j (Nat.fib (M + 1)) (Nat.fib_pos.mpr (Nat.succ_pos M))
  have h56 : (j : ℝ) / (Nat.fib (M + 1) : ℝ) ≤ (5 / 6 : ℝ) * X := by
    have hmul := mul_le_mul_of_nonneg_left hX_j (by norm_num : (0 : ℝ) ≤ 5 / 6)
    have hF_ne : (Nat.fib (M + 1) : ℝ) ≠ 0 := ne_of_gt hFpos
    have heq : 5 / 6 * (6 / (5 * (Nat.fib (M + 1) : ℝ)) * (j : ℝ)) =
        (j : ℝ) / (Nat.fib (M + 1) : ℝ) := by field_simp
    linarith
  have hnatR : ((j / Nat.fib (M + 1) : ℕ) : ℝ) < ((prescDigits m j w).card : ℝ) :=
    lt_of_le_of_lt (le_trans hdiv_le h56) hcardR
  exact le_of_lt (by exact_mod_cast hnatR)

/-- Transition step for the `b = 1` prescribed-count branch:
    every eligible `a ∈ prescDigits m j w` has `2 ≤ a` and restores `PrescribedInv (j + 1)`. -/
theorem prescChild_transition {m : ℕ → ℕ} {M j : ℕ} (hj : j0Prescribed M ≤ j)
    (hm1 : 1 ≤ m j) (hmM : m j ≤ M) {w : List ℕ} (hw : PrescribedInv j w)
    {a : ℕ} (ha : a ∈ prescDigits m j w) :
    2 ≤ a ∧ PrescribedInv (j + 1) (makePrescChild m j w a) := by
  obtain ⟨_, hX_6⟩ := prescRatio_ge hj hm1 hmM hw
  obtain ⟨hu'_posZ, hv'_posZ, hv'_ltZ, _⟩ := prescPrelude_bounds hm1 hmM hw
  set w' := prescPrelude m j w
  set u' : ℤ := (cfProd (0 :: w')) 1 0
  set v' : ℤ := (cfProd (0 :: w')) 1 1
  set T : ℝ := WindowPaperScale.Hpaper (j + 1)
  have hu'_posR : (0 : ℝ) < (u' : ℝ) := by exact_mod_cast hu'_posZ
  have hv'_posR : (0 : ℝ) < (v' : ℝ) := by exact_mod_cast hv'_posZ
  have hv'_ltR : (v' : ℝ) < (u' : ℝ) := by exact_mod_cast hv'_ltZ
  have hTpos : 0 < T := WindowPaperScale.Hpaper_pos (j + 1)
  have hXu' : prescRatio m j w * (u' : ℝ) = T := div_mul_cancel₀ T (ne_of_gt hu'_posR)
  simp only [prescDigits, Finset.mem_Icc] at ha
  have ha_lo : (4 / 3 : ℝ) * prescRatio m j w ≤ (a : ℝ) := by
    have h1 : (prescDigitLo m j w : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.1
    have h2 : (4 / 3 : ℝ) * prescRatio m j w ≤ (prescDigitLo m j w : ℝ) := Nat.le_ceil _
    linarith
  have ha2 : 2 ≤ a := by
    have : (2 : ℝ) ≤ (a : ℝ) := by linarith
    exact_mod_cast this
  have ha_hi : (a : ℝ) + 1 ≤ (5 / 2 : ℝ) * prescRatio m j w := by
    have hfl_ge1 : 1 ≤ Nat.floor ((5 / 2 : ℝ) * prescRatio m j w) := by
      have hgt : (5 / 2 : ℝ) * prescRatio m j w - 1 <
          (Nat.floor ((5 / 2 : ℝ) * prescRatio m j w) : ℝ) := by
        have := Nat.lt_floor_add_one ((5 / 2 : ℝ) * prescRatio m j w); linarith
      have : (1 : ℝ) ≤ (Nat.floor ((5 / 2 : ℝ) * prescRatio m j w) : ℝ) := by linarith
      exact_mod_cast this
    have h1 : (a : ℝ) ≤ (prescDigitHi m j w : ℝ) := by exact_mod_cast ha.2
    have h2 : (prescDigitHi m j w : ℝ) + 1 = (Nat.floor ((5 / 2 : ℝ) * prescRatio m j w) : ℝ) := by
      unfold prescDigitHi
      rw [Nat.cast_sub hfl_ge1, Nat.cast_one]; ring
    have h3 : (Nat.floor ((5 / 2 : ℝ) * prescRatio m j w) : ℝ) ≤
        (5 / 2 : ℝ) * prescRatio m j w := Nat.floor_le (by linarith)
    linarith
  have hcons : (0 :: makePrescChild m j w a) = (0 :: w') ++ [a] := rfl
  have hu_new : (cfProd (0 :: makePrescChild m j w a)) 1 0 = (a : ℤ) * u' + v' := by
    rw [hcons, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfProd, cfMat, u', v']; ring
  have hv_new : (cfProd (0 :: makePrescChild m j w a)) 1 1 = u' := by
    rw [hcons, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfProd, cfMat, u']
  have hu'_lt_T : (u' : ℝ) < T := by nlinarith
  refine ⟨ha2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold makePrescChild prescPrelude
    exact posDigits_append.mpr
      ⟨posDigits_append.mpr ⟨hw.1, posDigits_replicate_one _⟩,
        posDigits_cons.mpr ⟨by omega, posDigits_nil⟩⟩
  · unfold makePrescChild
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil a [])
  · rw [hu_new]; push_cast; nlinarith
  · rw [hu_new]; push_cast; nlinarith
  · rw [hv_new]; exact hu'_posZ
  · rw [hu_new, hv_new]
    have haZ : (2 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha2
    nlinarith
  · rw [hv_new]; exact hu'_lt_T

/-- Distinct digits `a₁ ≠ a₂` produce prefix-incomparable child words (same length). -/
theorem prescChild_incomparable {m : ℕ → ℕ} {j : ℕ} {w : List ℕ} {a₁ a₂ : ℕ} (hne : a₁ ≠ a₂) :
    ¬ (makePrescChild m j w a₁ <+: makePrescChild m j w a₂) := by
  intro ⟨suf, hsuf⟩
  have hlen : (makePrescChild m j w a₁).length = (makePrescChild m j w a₂).length := by
    simp [makePrescChild]
  have hsuf_nil : suf = [] := by
    have := congrArg List.length hsuf
    rw [List.length_append, hlen] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hsuf_nil
  rw [List.append_nil] at hsuf
  unfold makePrescChild at hsuf
  have htail := List.append_cancel_left hsuf
  injection htail with ha_eq
  exact hne ha_eq

/-- Every word in `prescWordAtoms m M par0 j` satisfies `PrescribedInv j` and distinct words
    at stage `j` are prefix-incomparable. -/
theorem prescWordAtoms_inv_and_incomp (m : ℕ → ℕ) (M : ℕ) (par0 : Bool)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ M) :
    ∀ j ≥ j0Prescribed M,
      (∀ w ∈ prescWordAtoms m M par0 j, PrescribedInv j w) ∧
      (∀ w₁ ∈ prescWordAtoms m M par0 j, ∀ w₂ ∈ prescWordAtoms m M par0 j,
        w₁ ≠ w₂ → ¬ (w₁ <+: w₂)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    rw [prescWordAtoms_base]
    refine ⟨fun w hw => ?_, fun w₁ h1 w₂ h2 hne => ?_⟩
    · rw [Finset.mem_singleton.mp hw]; exact initWordAt_prescribedInv par0 (j0Prescribed_ge_six M)
    · rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2] at hne
      exact absurd rfl hne
  | succ j hj ih =>
    obtain ⟨ih_inv, ih_inc⟩ := ih
    rw [prescWordAtoms_succ m M par0 hj]
    constructor
    · intro c hc
      obtain ⟨w, hw, hcw⟩ := Finset.mem_biUnion.mp hc
      simp only [prescWordChild, Finset.mem_image] at hcw
      obtain ⟨a, ha, rfl⟩ := hcw
      exact (prescChild_transition hj (hm j).1 (hm j).2 (ih_inv w hw) ha).2
    · intro c₁ hc₁ c₂ hc₂ hne hpref
      obtain ⟨w₁, hw₁, hcw₁⟩ := Finset.mem_biUnion.mp hc₁
      obtain ⟨w₂, hw₂, hcw₂⟩ := Finset.mem_biUnion.mp hc₂
      simp only [prescWordChild, Finset.mem_image] at hcw₁ hcw₂
      obtain ⟨a₁, _, rfl⟩ := hcw₁
      obtain ⟨a₂, _, rfl⟩ := hcw₂
      by_cases hw_eq : w₁ = w₂
      · subst hw_eq
        have ha_ne : a₁ ≠ a₂ := fun h => hne (by subst h; rfl)
        exact prescChild_incomparable ha_ne hpref
      · have hw1_pre : w₁ <+: makePrescChild m j w₁ a₁ := by
          unfold makePrescChild prescPrelude
          rw [List.append_assoc]; exact List.prefix_append w₁ _
        have hw2_pre : w₂ <+: makePrescChild m j w₂ a₂ := by
          unfold makePrescChild prescPrelude
          rw [List.append_assoc]; exact List.prefix_append w₂ _
        have hw1_in_c2 : w₁ <+: makePrescChild m j w₂ a₂ := List.IsPrefix.trans hw1_pre hpref
        rcases List.prefix_or_prefix_of_prefix hw1_in_c2 hw2_pre with h12 | h21
        · exact ih_inc w₁ hw₁ w₂ hw₂ hw_eq h12
        · exact ih_inc w₂ hw₂ w₁ hw₁ (Ne.symm hw_eq) h21

/-- `cylPair` is injective on `prescWordAtoms m M par0 j`. -/
theorem cylPair_injOn_prescAtoms (m : ℕ → ℕ) (M : ℕ) (par0 : Bool)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ M) {j : ℕ} (hj : j0Prescribed M ≤ j) :
    Set.InjOn cylPair ↑(prescWordAtoms m M par0 j) := by
  obtain ⟨hinv, hinc⟩ := prescWordAtoms_inv_and_incomp m M par0 hm j hj
  intro w₁ hw₁ w₂ hw₂ heq
  by_contra hne
  have h1 := Finset.mem_coe.mp hw₁
  have h2 := Finset.mem_coe.mp hw₂
  have hdisj := cylPair_disj_of_incomparable (hinv w₁ h1).1 (hinv w₂ h2).1
    (hinc w₁ h1 w₂ h2 hne) (hinc w₂ h2 w₁ h1 (Ne.symm hne))
  rw [heq] at hdisj
  have hlen := cylPair_len_bounds (WindowPaperScale.Hpaper_pos j) (hinv w₂ h2).1 (hinv w₂ h2).2.1
    (hinv w₂ h2).2.2.1 (hinv w₂ h2).2.2.2.1
    (by exact_mod_cast le_of_lt (hinv w₂ h2).2.2.2.2.1)
    (by exact_mod_cast le_of_lt (hinv w₂ h2).2.2.2.2.2.1)
  have hlt : (cylPair w₂).1 < (cylPair w₂).2 := by
    have : (0 : ℝ) < (2 / 25 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 := by
      have := WindowPaperScale.Hpaper_pos j; positivity
    linarith [hlen.1]
  have hmid : ((cylPair w₂).1 + (cylPair w₂).2) / 2 ∈
      Set.Ioo (cylPair w₂).1 (cylPair w₂).2 := ⟨by linarith, by linarith⟩
  exact Set.disjoint_left.mp hdisj hmid hmid

/-! ### Part 2: Concrete tree `cfPrescribedTree` & dimension `≥ 1/2` discharge -/

open Classical in
/-- Concrete `StoppedTree.TreeData` realizing Paper 2's `b = 1` prescribed-count CF tree. -/
noncomputable def cfPrescribedTree (m : ℕ → ℕ) (M : ℕ) (par0 : Bool) : StoppedTree.TreeData where
  atoms := fun j => (prescWordAtoms m M par0 j).image cylPair
  child := fun j I =>
    if h : ∃ w ∈ prescWordAtoms m M par0 j, cylPair w = I then
      (prescWordChild m j (Classical.choose h)).image cylPair
    else ∅

/-- Unconditional Hausdorff dimension lower bound `1 / 2 ≤ dimH` for `cfPrescribedTree`:
    discharges all hypotheses of `WindowPaperScale.dimH_ge_half_prescribed_paper_scale`. -/
theorem dimH_ge_half_cfPrescribedTree (m : ℕ → ℕ) (M : ℕ) (par0 : Bool)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ M) :
    ENNReal.ofReal (1 / 2) ≤
      dimH (WindowTreePrune.cantorSet (cfPrescribedTree m M par0) (j0Prescribed M)) := by
  classical
  let j0 := j0Prescribed M
  let F := Nat.fib (M + 1)
  have hFposN : 0 < F := Nat.fib_pos.mpr (Nat.succ_pos M)
  have hFpos : (0 : ℝ) < (F : ℝ) := by exact_mod_cast hFposN
  let B : ℕ → ℕ := fun j => j / F
  have hB1 : ∀ j ≥ j0, 1 ≤ B j := by
    intro j hj
    have hj5F : 5 * F ≤ j := le_trans (le_max_right 6 (5 * F)) hj
    have hdiv : 5 ≤ j / F := (Nat.le_div_iff_mul_le hFposN).mpr (by omega)
    dsimp only [B]
    omega
  have hc : (0 : ℝ) < 4 / (5 * (F : ℝ)) := by positivity
  have hbranch : ∀ j ≥ j0, (4 / (5 * (F : ℝ))) * (j : ℝ) ≤ (B j : ℝ) := by
    intro j hj
    have hj5F : (5 * (F : ℝ)) ≤ (j : ℝ) := by
      exact_mod_cast le_trans (le_max_right 6 (5 * F)) hj
    have hlow := WindowMobiusCount.nat_div_cast_lower j F hFposN
    have hFne : (F : ℝ) ≠ 0 := ne_of_gt hFpos
    have h1 : (1 : ℝ) ≤ (j : ℝ) / (5 * (F : ℝ)) := by
      rw [one_le_div (by positivity)]; exact hj5F
    have hsub : (j : ℝ) / (F : ℝ) - (j : ℝ) / (5 * (F : ℝ)) =
        (4 / (5 * (F : ℝ))) * (j : ℝ) := by field_simp; ring
    linarith
  have hchoose_eq : ∀ j ≥ j0, ∀ w ∈ prescWordAtoms m M par0 j,
      ∀ h : ∃ w' ∈ prescWordAtoms m M par0 j, cylPair w' = cylPair w,
        Classical.choose h = w := by
    intro j hj w hw h
    obtain ⟨hw', heq⟩ := Classical.choose_spec h
    exact cylPair_injOn_prescAtoms m M par0 hm hj
      (Finset.mem_coe.mpr hw') (Finset.mem_coe.mpr hw) heq
  have hne0 : ((cfPrescribedTree m M par0).atoms j0).Nonempty := by
    refine ⟨cylPair (initWordAt (fun _ => par0) j0), ?_⟩
    simp [cfPrescribedTree, j0, prescWordAtoms_base]
  have hlen : ∀ j ≥ j0, ∀ I ∈ (cfPrescribedTree m M par0).atoms j,
      (2 / 25 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 ≤ I.2 - I.1 ∧
      I.2 - I.1 ≤ (9 / 16 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 := by
    intro j hj I hI
    simp only [cfPrescribedTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hinv := (prescWordAtoms_inv_and_incomp m M par0 hm j hj).1 w hw
    exact cylPair_len_bounds (WindowPaperScale.Hpaper_pos j) hinv.1 hinv.2.1
      hinv.2.2.1 hinv.2.2.2.1
      (by exact_mod_cast le_of_lt hinv.2.2.2.2.1)
      (by exact_mod_cast le_of_lt hinv.2.2.2.2.2.1)
  have htriv : ∀ j ≥ j0, ∀ I ∈ (cfPrescribedTree m M par0).atoms j, I.1 < I.2 := by
    intro j hj I hI
    have h1 := (hlen j hj I hI).1
    have hpos : (0 : ℝ) < (2 / 25 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 := by
      have := WindowPaperScale.Hpaper_pos j; positivity
    linarith
  have hdisj : ∀ j ≥ j0, ∀ I ∈ (cfPrescribedTree m M par0).atoms j,
      ∀ J ∈ (cfPrescribedTree m M par0).atoms j,
      I ≠ J → Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2) := by
    intro j hj I hI J hJ hne
    simp only [cfPrescribedTree, Finset.mem_image] at hI hJ
    obtain ⟨w₁, hw₁, rfl⟩ := hI
    obtain ⟨w₂, hw₂, rfl⟩ := hJ
    have hw_ne : w₁ ≠ w₂ := fun h => hne (by subst h; rfl)
    obtain ⟨hinv, hinc⟩ := prescWordAtoms_inv_and_incomp m M par0 hm j hj
    exact cylPair_disj_of_incomparable (hinv w₁ hw₁).1 (hinv w₂ hw₂).1
      (hinc w₁ hw₁ w₂ hw₂ hw_ne) (hinc w₂ hw₂ w₁ hw₁ (Ne.symm hw_ne))
  have hchild_mem : ∀ j ≥ j0, ∀ I ∈ (cfPrescribedTree m M par0).atoms j,
      (cfPrescribedTree m M par0).child j I ⊆ (cfPrescribedTree m M par0).atoms (j + 1) := by
    intro j hj I hI c hc
    simp only [cfPrescribedTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hex : ∃ w' ∈ prescWordAtoms m M par0 j, cylPair w' = cylPair w := ⟨w, hw, rfl⟩
    simp only [cfPrescribedTree, hex, ↓reduceDIte, hchoose_eq j hj w hw hex, Finset.mem_image]
      at hc ⊢
    obtain ⟨cw, hcw, rfl⟩ := hc
    refine ⟨cw, ?_, rfl⟩
    rw [prescWordAtoms_succ m M par0 hj]
    exact Finset.mem_biUnion.mpr ⟨w, hw, hcw⟩
  have hchild_card : ∀ j ≥ j0, ∀ I ∈ (cfPrescribedTree m M par0).atoms j,
      B j ≤ ((cfPrescribedTree m M par0).child j I).card := by
    intro j hj I hI
    simp only [cfPrescribedTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hex : ∃ w' ∈ prescWordAtoms m M par0 j, cylPair w' = cylPair w := ⟨w, hw, rfl⟩
    have hinv := (prescWordAtoms_inv_and_incomp m M par0 hm j hj).1 w hw
    simp only [cfPrescribedTree, hex, ↓reduceDIte, hchoose_eq j hj w hw hex]
    have hsub_atoms : prescWordChild m j w ⊆ prescWordAtoms m M par0 (j + 1) := by
      intro c hc
      rw [prescWordAtoms_succ m M par0 hj]
      exact Finset.mem_biUnion.mpr ⟨w, hw, hc⟩
    have hinj_cyl : Set.InjOn cylPair ↑(prescWordChild m j w) :=
      (cylPair_injOn_prescAtoms m M par0 hm (by omega : j0 ≤ j + 1)).mono
        (Finset.coe_subset.mpr hsub_atoms)
    rw [Finset.card_image_of_injOn hinj_cyl]
    unfold prescWordChild
    have hinj_a : Set.InjOn (makePrescChild m j w) ↑(prescDigits m j w) := by
      intro a₁ _ a₂ _ heq
      by_contra hne
      exact prescChild_incomparable hne (by rw [heq])
    rw [Finset.card_image_of_injOn hinj_a]
    exact prescDigits_card_ge hj (hm j).1 (hm j).2 hinv
  have hdisj_child : ∀ j ≥ j0, ∀ I₁ ∈ (cfPrescribedTree m M par0).atoms j,
      ∀ I₂ ∈ (cfPrescribedTree m M par0).atoms j, I₁ ≠ I₂ →
      Disjoint ((cfPrescribedTree m M par0).child j I₁)
        ((cfPrescribedTree m M par0).child j I₂) := by
    intro j hj I₁ hI₁ I₂ hI₂ hne
    simp only [cfPrescribedTree, Finset.mem_image] at hI₁ hI₂
    obtain ⟨w₁, hw₁, rfl⟩ := hI₁
    obtain ⟨w₂, hw₂, rfl⟩ := hI₂
    have hw_ne : w₁ ≠ w₂ := fun h => hne (by subst h; rfl)
    have hex₁ : ∃ w' ∈ prescWordAtoms m M par0 j, cylPair w' = cylPair w₁ := ⟨w₁, hw₁, rfl⟩
    have hex₂ : ∃ w' ∈ prescWordAtoms m M par0 j, cylPair w' = cylPair w₂ := ⟨w₂, hw₂, rfl⟩
    simp only [cfPrescribedTree, hex₁, hex₂, ↓reduceDIte,
      hchoose_eq j hj w₁ hw₁ hex₁, hchoose_eq j hj w₂ hw₂ hex₂]
    rw [Finset.disjoint_left]
    intro c hc₁ hc₂
    simp only [Finset.mem_image] at hc₁ hc₂
    obtain ⟨c₁, hc₁', rfl⟩ := hc₁
    obtain ⟨c₂, hc₂', heq⟩ := hc₂
    have hc₁_atoms : c₁ ∈ prescWordAtoms m M par0 (j + 1) := by
      rw [prescWordAtoms_succ m M par0 hj]; exact Finset.mem_biUnion.mpr ⟨w₁, hw₁, hc₁'⟩
    have hc₂_atoms : c₂ ∈ prescWordAtoms m M par0 (j + 1) := by
      rw [prescWordAtoms_succ m M par0 hj]; exact Finset.mem_biUnion.mpr ⟨w₂, hw₂, hc₂'⟩
    have hc_eq : c₁ = c₂ :=
      cylPair_injOn_prescAtoms m M par0 hm (by omega : j0 ≤ j + 1)
        (Finset.mem_coe.mpr hc₁_atoms) (Finset.mem_coe.mpr hc₂_atoms) heq.symm
    subst hc_eq
    simp only [prescWordChild, Finset.mem_image] at hc₁' hc₂'
    obtain ⟨a₁, _, ha₁_eq⟩ := hc₁'
    obtain ⟨a₂, _, ha₂_eq⟩ := hc₂'
    have hpre₁ : w₁ <+: c₁ := by
      rw [← ha₁_eq]; unfold makePrescChild prescPrelude
      rw [List.append_assoc]; exact List.prefix_append w₁ _
    have hpre₂ : w₂ <+: c₁ := by
      rw [← ha₂_eq]; unfold makePrescChild prescPrelude
      rw [List.append_assoc]; exact List.prefix_append w₂ _
    have hinc := (prescWordAtoms_inv_and_incomp m M par0 hm j hj).2
    rcases List.prefix_or_prefix_of_prefix hpre₁ hpre₂ with h12 | h21
    · exact hinc w₁ hw₁ w₂ hw₂ hw_ne h12
    · exact hinc w₂ hw₂ w₁ hw₁ (Ne.symm hw_ne) h21
  have hnest : ∀ j ≥ j0, ∀ I ∈ (cfPrescribedTree m M par0).atoms j,
      ∀ C ∈ (cfPrescribedTree m M par0).child j I, Set.Icc C.1 C.2 ⊆ Set.Icc I.1 I.2 := by
    intro j hj I hI C hC
    simp only [cfPrescribedTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hex : ∃ w' ∈ prescWordAtoms m M par0 j, cylPair w' = cylPair w := ⟨w, hw, rfl⟩
    simp only [cfPrescribedTree, hex, ↓reduceDIte, hchoose_eq j hj w hw hex, Finset.mem_image] at hC
    obtain ⟨cw, hcw, rfl⟩ := hC
    have hinv_w := (prescWordAtoms_inv_and_incomp m M par0 hm j hj).1 w hw
    have hinv_cw := (prescWordAtoms_inv_and_incomp m M par0 hm (j + 1) (by omega)).1 cw
      (by rw [prescWordAtoms_succ m M par0 hj]; exact Finset.mem_biUnion.mpr ⟨w, hw, hcw⟩)
    simp only [prescWordChild, Finset.mem_image] at hcw
    obtain ⟨a, _, rfl⟩ := hcw
    unfold makePrescChild prescPrelude at hinv_cw ⊢
    rw [List.append_assoc] at hinv_cw ⊢
    exact cylPair_nest hinv_w.1 hinv_w.2.1 (posDigits_append.mp hinv_cw.1).2
  have hj03 : 3 ≤ j0 := le_trans (by norm_num : 3 ≤ 6) (j0Prescribed_ge_six M)
  exact WindowPaperScale.dimH_ge_half_prescribed_paper_scale
    (T := cfPrescribedTree m M par0) (j0 := j0) hj03 hB1 hc hbranch
    hne0 htriv hlen hdisj hchild_mem hchild_card hdisj_child hnest

/-! ### Part 3: Pointwise regular CF bridge & end-to-end `thm:windows` (`b = 1`) -/

/-- Fixed-starting-index target set for `thm:windows`: irrationals `x ∈ (0, 1)` with
    prescribed initial parity `k(J0) ≡ par0 (mod 2)` at the FIXED starting index `J0` and
    exact window increments `r_j(x) = m j` for all `j ≥ J0`. -/
def prescribedIncSetAt (m : ℕ → ℕ) (J0 : ℕ) (par0 : Bool) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 |
    Irrational x ∧
      ((cfStopIdx x J0) % 2 == 1) = par0 ∧
      ∀ j ≥ J0, cfStopIdx x (j + 1) - cfStopIdx x j = m j}

/-- The two initial-parity branches at any fixed starting index `J0` are disjoint. -/
theorem prescribedIncSetAt_disjoint (m : ℕ → ℕ) (J0 : ℕ) :
    Disjoint (prescribedIncSetAt m J0 true) (prescribedIncSetAt m J0 false) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have h1 := hx1.2.2.1
  have h2 := hx2.2.2.1
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Target set for prescribed eventual window increments `r_j(x) = m j`. -/
def prescribedIncSet (m : ℕ → ℕ) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 |
    Irrational x ∧ ∃ J0 : ℕ, ∀ j ≥ J0, cfStopIdx x (j + 1) - cfStopIdx x j = m j}

/-- Target set for eventually bounded window increments `r_j(x)`. -/
def boundedIncSet : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 |
    Irrational x ∧ ∃ B J0 : ℕ, ∀ j ≥ J0, cfStopIdx x (j + 1) - cfStopIdx x j ≤ B}

/-- Pointwise regular CF bridge for `cfPrescribedTree m M par0`:
    every `x ∈ cantorSet (cfPrescribedTree m M par0) (j0Prescribed M)` is irrational in `(0, 1)`
    with initial parity `par0` at `j0Prescribed M` and exact window increment
    `cfStopIdx x (j + 1) - cfStopIdx x j = m j` for all `j ≥ j0Prescribed M`. -/
theorem mem_cantorSet_cfPrescribedTree_cf (m : ℕ → ℕ) (M : ℕ) (par0 : Bool)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ M) {x : ℝ}
    (hx : x ∈ WindowTreePrune.cantorSet (cfPrescribedTree m M par0) (j0Prescribed M)) :
    x ∈ Set.Ioo (0 : ℝ) 1 ∧
    Irrational x ∧
    ((cfStopIdx x (j0Prescribed M)) % 2 == 1) = par0 ∧
    ∀ j ≥ j0Prescribed M, cfStopIdx x (j + 1) - cfStopIdx x j = m j := by
  have hbridge := stopped_word_tree_cf_bridge
    (wordAtoms := prescWordAtoms m M par0) (wordChild := prescWordChild m)
    (T := cfPrescribedTree m M par0) (j0 := j0Prescribed M)
    (by have := j0Prescribed_ge_six M; omega)
    (fun _ _ => rfl)
    (fun j hj => prescWordAtoms_succ m M par0 hj)
    (fun j hj w hw =>
      let h := (prescWordAtoms_inv_and_incomp m M par0 hm j hj).1 w hw
      ⟨h.1, h.2.1⟩)
    (fun j hj => (prescWordAtoms_inv_and_incomp m M par0 hm j hj).2)
    (fun j hj w hw => by
      have h := (prescWordAtoms_inv_and_incomp m M par0 hm j hj).1 w hw
      have hHpos := WindowPaperScale.Hpaper_pos j
      exact ⟨le_of_lt h.2.2.2.2.2.2, by linarith [h.2.2.1]⟩)
    (fun j hj w hw c hc => by
      simp only [prescWordChild, Finset.mem_image] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      have hinv := (prescWordAtoms_inv_and_incomp m M par0 hm j hj).1 w hw
      obtain ⟨ha2, _⟩ := prescChild_transition hj (hm j).1 (hm j).2 hinv ha
      refine ⟨List.replicate (m j - 1) 1 ++ [a], ?_, ?_, ?_⟩
      · simp [makePrescChild, prescPrelude, List.append_assoc]
      · exact posDigits_append.mpr
          ⟨posDigits_replicate_one _, posDigits_cons.mpr ⟨by omega, posDigits_nil⟩⟩
      · by_cases hm_eq : m j = 1
        · right
          refine ⟨a, ?_, ha2⟩
          simp [hm_eq]
        · left
          have : 1 ≤ m j - 1 := by have := (hm j).1; omega
          simp; omega)
    hx
  obtain ⟨hunit, hirr, w, hw_mem, hw_child, _, _, hstop⟩ := hbridge
  have hw0_eq : w (j0Prescribed M) = initWordAt (fun _ => par0) (j0Prescribed M) := by
    have h0 := hw_mem (j0Prescribed M) le_rfl
    rw [prescWordAtoms_base] at h0
    exact Finset.mem_singleton.mp h0
  have hpar0 : ((cfStopIdx x (j0Prescribed M)) % 2 == 1) = par0 := by
    rw [(hstop (j0Prescribed M) le_rfl).2, hw0_eq]
    exact (initWordAt_inv (fun _ => par0) (j0Prescribed_ge_six M)).2.2.1
  refine ⟨hunit, hirr, hpar0, ?_⟩
  intro j hj
  have hst := (hstop j hj).2
  have hst1 := (hstop (j + 1) (by omega)).2
  have hch := hw_child j hj
  simp only [prescWordChild, Finset.mem_image] at hch
  obtain ⟨a, _, ha_eq⟩ := hch
  have hlen_j : 1 ≤ (w j).length := by
    have hne := ((prescWordAtoms_inv_and_incomp m M par0 hm j hj).1 (w j) (hw_mem j hj)).2.1
    exact List.length_pos_of_ne_nil hne
  rw [hst, hst1, ← ha_eq]
  unfold makePrescChild prescPrelude
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  have hm1 := (hm j).1
  omega

theorem cantorSet_cfPrescribedTree_subset_prescribedIncSetAt (m : ℕ → ℕ) (M : ℕ) (par0 : Bool)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ M) :
    WindowTreePrune.cantorSet (cfPrescribedTree m M par0) (j0Prescribed M) ⊆
      prescribedIncSetAt m (j0Prescribed M) par0 := by
  intro x hx
  obtain ⟨hunit, hirr, hpar0, hinc⟩ := mem_cantorSet_cfPrescribedTree_cf m M par0 hm hx
  exact ⟨hunit, hirr, hpar0, hinc⟩

/-- End-to-end unconditional `thm:windows` (`b = 1` fixed-starting-index initial-parity branch):
    at the explicit starting index `j0Prescribed M` (independent of `par0`), either initial
    parity `par0 : Bool` can be imposed while keeping `ENNReal.ofReal (1 / 2) ≤ dimH`. -/
theorem dimH_ge_half_prescribedIncSetAt (m : ℕ → ℕ) (M : ℕ) (par0 : Bool)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ M) :
    ENNReal.ofReal (1 / 2) ≤ dimH (prescribedIncSetAt m (j0Prescribed M) par0) :=
  le_trans (dimH_ge_half_cfPrescribedTree m M par0 hm)
    (dimH_mono (cantorSet_cfPrescribedTree_subset_prescribedIncSetAt m M par0 hm))

/-- At a sufficiently large starting index `J0` (independent of `par0`), either initial parity
    of `k(J0)` can be imposed on a set of Hausdorff dimension `≥ 1/2`. -/
theorem exists_start_dimH_ge_half_prescribedIncSetAt (m : ℕ → ℕ) (M : ℕ)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ M) :
    ∃ J0 : ℕ, ∀ par0 : Bool, ENNReal.ofReal (1 / 2) ≤ dimH (prescribedIncSetAt m J0 par0) :=
  ⟨j0Prescribed M, fun par0 => dimH_ge_half_prescribedIncSetAt m M par0 hm⟩

/-- End-to-end unconditional `thm:windows` (`b = 1` prescribed eventual increments):
    for any bounded sequence `1 ≤ m j ≤ M`,
    `ENNReal.ofReal (1 / 2) ≤ dimH (prescribedIncSet m)`. -/
theorem dimH_ge_half_prescribedIncSet (m : ℕ → ℕ) (M : ℕ)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ M) :
    ENNReal.ofReal (1 / 2) ≤ dimH (prescribedIncSet m) :=
  le_trans (dimH_ge_half_prescribedIncSetAt m M true hm)
    (dimH_mono fun _ ⟨hunit, hirr, _, hinc⟩ => ⟨hunit, hirr, j0Prescribed M, hinc⟩)

/-- End-to-end unconditional `thm:windows` (eventually bounded `r_j` lower bound):
    `ENNReal.ofReal (1 / 2) ≤ dimH boundedIncSet`. -/
theorem dimH_ge_half_boundedIncSet :
    ENNReal.ofReal (1 / 2) ≤ dimH boundedIncSet := by
  refine le_trans (dimH_ge_half_prescribedIncSet (fun _ => 1) 1 (fun _ => ⟨le_rfl, le_rfl⟩)) ?_
  refine dimH_mono fun x ⟨hunit, hirr, J0, hinc⟩ => ?_
  exact ⟨hunit, hirr, 1, J0, fun j hj => le_of_eq (hinc j hj)⟩

#print axioms WindowPrescribedCFRealize.initWordAt_prescribedInv
#print axioms WindowPrescribedCFRealize.prescPrelude_bounds
#print axioms WindowPrescribedCFRealize.prescRatio_ge
#print axioms WindowPrescribedCFRealize.prescDigits_card_ge
#print axioms WindowPrescribedCFRealize.prescChild_transition
#print axioms WindowPrescribedCFRealize.prescChild_incomparable
#print axioms WindowPrescribedCFRealize.prescWordAtoms_inv_and_incomp
#print axioms WindowPrescribedCFRealize.cylPair_injOn_prescAtoms
#print axioms WindowPrescribedCFRealize.dimH_ge_half_cfPrescribedTree
#print axioms WindowPrescribedCFRealize.prescribedIncSetAt_disjoint
#print axioms WindowPrescribedCFRealize.mem_cantorSet_cfPrescribedTree_cf
#print axioms WindowPrescribedCFRealize.cantorSet_cfPrescribedTree_subset_prescribedIncSetAt
#print axioms WindowPrescribedCFRealize.dimH_ge_half_prescribedIncSetAt
#print axioms WindowPrescribedCFRealize.exists_start_dimH_ge_half_prescribedIncSetAt
#print axioms WindowPrescribedCFRealize.dimH_ge_half_prescribedIncSet
#print axioms WindowPrescribedCFRealize.dimH_ge_half_boundedIncSet

end WindowPrescribedCFRealize
