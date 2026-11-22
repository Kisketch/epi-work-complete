import EpiFormal.WindowBoundedUpper
import EpiFormal.WindowAndResidueCore

/-!
# General-Modulus Continued-Fraction Residue Sets and Countable Shift Invariance

Proves the Category-1 unconditional general-modulus continued-fraction dimension theorems for
arbitrary modulus `m ≥ 2` and arbitrary residue sequences `r : ℕ → ℕ`:

1. Complete regular continued-fraction digit–real bijection on `(0, 1) \ ℚ`:
   `cfDigit x i`, `cfTail x i`, and `cfVal a` with exact Möbius remainder relation
   `x = mobius (cfProd (0 :: cfPrefixList (cfDigit x) n)) (cfTail x n)` and prefix-shift identity
   `cfDigit (mobius (cfProd (0 :: w)) t) (w.length + k) = cfDigit t k`.
2. **Uniform Lipschitz Equivalence for Arbitrary Shifts (`lipschitzOnWith_cfShift`)**:
   For ANY `2 ≤ m`, any `r : ℕ → ℕ` (`∀ i, 1 ≤ r i`), and ANY shift `c : ℕ → ℕ`, the digit-shift map
   `cfShiftMap c : x ↦ cfVal (fun i => cfDigit x i + c i)` is `24`-Lipschitz on
   `residueSeqSet m r = {x ∈ (0, 1) | Irrational x ∧ ∀ i, r i ≤ a_i ∧ a_i ≡ r i [MOD m]}`
   with image `residueSeqSet m (fun i => r i + c i)`.
3. **General-Modulus Sandwich Theorem (`dimH_residueSeqSet_sandwich`)**:
   `dimH (residueConstSet m m) ≤ dimH (residueSeqSet m r) ≤ dimH (residueConstSet m 1)`
   for every `2 ≤ m` and every sequence `r : ℕ → ℕ` with `∀ i, 1 ≤ r i ≤ m`.
4. **Countable Eventually Periodic Family Theorem (`dimH_eventuallyPeriodicResidueSet_eq`)**:
   `dimH (eventuallyPeriodicResidueSet m) = dimH (residueConstSet m 1)` for every `m ≥ 2`,
   via bi-Lipschitz Möbius prefix invariance (`dimH_mobius_prefix_eq`) and countable sigma
   parametrization of eventually periodic residue sequences into `{1, ..., m}`.
-/

namespace ResidueModGeneral

open Matrix Set Filter Finset ENNReal Metric Real MeasureTheory
open Cylinder WindowCFRealize WindowCFBridge WindowBoundedUpper
open scoped NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Part 1: Regular CF digits, matrix entry bounds, and real realization -/

/-- The `i`-th partial quotient `a_{i+1} ∈ ℕ` of a real number `x ∈ (0, 1)` (`i ≥ 0`). -/
def cfDigit (x : ℝ) (i : ℕ) : ℕ :=
  ((GenContFract.of x).s.get? i).elim 0 (fun gp => Int.toNat ⌊gp.b⌋)

/-- The `n`-prefix `[a 0, ..., a (n - 1)]` of a digit stream `a : ℕ → ℕ`. -/
def cfPrefixList (a : ℕ → ℕ) (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => a i)

@[simp]
lemma cfPrefixList_zero (a : ℕ → ℕ) : cfPrefixList a 0 = [] := by
  simp [cfPrefixList]

@[simp]
lemma cfPrefixList_length (a : ℕ → ℕ) (n : ℕ) : (cfPrefixList a n).length = n := by
  simp [cfPrefixList]

lemma cfPrefixList_succ (a : ℕ → ℕ) (n : ℕ) :
    cfPrefixList a (n + 1) = cfPrefixList a n ++ [a n] := by
  refine List.ext_getElem (by simp [cfPrefixList]) fun i hi1 hi2 => ?_
  simp only [cfPrefixList, List.getElem_ofFn, List.getElem_append, List.length_ofFn]
  split_ifs with h
  · rfl
  · have hi_eq : i = n := by
      rw [cfPrefixList_length] at hi1
      omega
    subst hi_eq
    simp

lemma cfPrefixList_add (a : ℕ → ℕ) (m n : ℕ) :
    cfPrefixList a (m + n) = cfPrefixList a m ++ cfPrefixList (fun i => a (m + i)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 by omega, cfPrefixList_succ, ih, List.append_assoc,
      cfPrefixList_succ (fun i => a (m + i)) n]

lemma posDigits_cfPrefixList {a : ℕ → ℕ} (ha : ∀ i, 1 ≤ a i) (n : ℕ) :
    PosDigits (cfPrefixList a n) := by
  intro d hd
  rw [cfPrefixList, List.mem_ofFn] at hd
  obtain ⟨i, rfl⟩ := hd
  exact ha i

lemma cfProd_nonneg_zero_cons (w : List ℕ) (i j : Fin 2) :
    0 ≤ (cfProd (0 :: w)) i j :=
  cfProd_nonneg (0 :: w) i j

/-- For every positive-digit word `w`, `q_{|w|} ≥ |w|` and for `w ≠ []`, `q_{|w|-1} ≥ 1`. -/
lemma cfProd_zero_cons_den_ge {w : List ℕ} (hw : PosDigits w) :
    (w.length : ℤ) ≤ (cfProd (0 :: w)) 1 0 ∧
    (w ≠ [] → 1 ≤ (cfProd (0 :: w)) 1 1) := by
  induction w using List.reverseRecOn with
  | nil =>
    simp [cfProd, cfMat]
  | append_singleton w a ih =>
    rw [posDigits_append] at hw
    obtain ⟨ih_len, ih_p⟩ := ih hw.1
    have ha : 1 ≤ a := hw.2 a (by simp)
    have hcons : (0 :: (w ++ [a])) = (0 :: w) ++ [a] := rfl
    rw [hcons, cfProd_append_single, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [cfMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero]
    have hq_nn : 0 ≤ (cfProd (0 :: w)) 1 0 := cfProd_nonneg (0 :: w) 1 0
    have hp_nn : 0 ≤ (cfProd (0 :: w)) 1 1 := cfProd_nonneg (0 :: w) 1 1
    have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    have hq_pos : 1 ≤ (cfProd (0 :: w)) 1 0 := by
      cases w with
      | nil => simp [cfProd, cfMat]
      | cons b rest =>
        have hcol := cfProd_col0_pos hw.1 (List.cons_ne_nil b rest)
        have hr1 := cfProd_zero_cons_row1 (b :: rest)
        linarith
    have haq : (cfProd (0 :: w)) 1 0 ≤ (cfProd (0 :: w)) 1 0 * (a : ℤ) := by nlinarith
    cases w with
    | nil =>
      simp only [List.length_nil, Nat.cast_zero, List.nil_append, cfProd, cfMat,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, mul_one, add_zero] at *
      have hlen1 : (([a] : List ℕ).length : ℤ) = 1 := rfl
      rw [hlen1, one_mul]
      exact ⟨by exact_mod_cast ha, fun _ => le_rfl⟩
    | cons b rest =>
      have hp1 : 1 ≤ (cfProd (0 :: b :: rest)) 1 1 := ih_p (List.cons_ne_nil b rest)
      rw [List.length_append, List.length_singleton]
      exact ⟨by push_cast; linarith, fun _ => hq_pos⟩

/-- In row 0 of `cfProd w` (for `PosDigits w`), column 1 is at most column 0. -/
lemma cfProd_col1_le_col0 {w : List ℕ} (hw : PosDigits w) :
    (cfProd w) 0 1 ≤ (cfProd w) 0 0 := by
  induction w using List.reverseRecOn with
  | nil => simp [cfProd]
  | append_singleton w a ih =>
    rw [posDigits_append] at hw
    have ha : 1 ≤ a := hw.2 a (by simp)
    rw [cfProd_append_single, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [cfMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero]
    have h00 : 0 ≤ (cfProd w) 0 0 := cfProd_nonneg w 0 0
    have h01 : 0 ≤ (cfProd w) 0 1 := cfProd_nonneg w 0 1
    have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    have hmul : (cfProd w) 0 0 ≤ (cfProd w) 0 0 * (a : ℤ) := by nlinarith
    linarith

lemma cfProd_zero_cons_col1_le_col0 {w : List ℕ} (hw : PosDigits w) :
    (cfProd (0 :: w)) 1 1 ≤ (cfProd (0 :: w)) 1 0 := by
  have hr := cfProd_zero_cons_row1 w
  rw [hr.1, hr.2]
  exact cfProd_col1_le_col0 hw

/-- Monotonicity of every entry of `cfProd (0 :: prefix a n)` under `∀ i, a i ≤ b i`. -/
lemma cfProd_mono_of_le {a b : ℕ → ℕ} (hle : ∀ i, a i ≤ b i) (n : ℕ) (i j : Fin 2) :
    (cfProd (0 :: cfPrefixList a n)) i j ≤ (cfProd (0 :: cfPrefixList b n)) i j := by
  induction n generalizing i j with
  | zero => simp [cfPrefixList]
  | succ n ih =>
    rw [cfPrefixList_succ, cfPrefixList_succ]
    change (cfProd ((0 :: cfPrefixList a n) ++ [a n])) i j ≤
      (cfProd ((0 :: cfPrefixList b n) ++ [b n])) i j
    rw [cfProd_append_single, cfProd_append_single, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_two]
    have hmn : ∀ p q : Fin 2, (cfMat (a n)) p q ≤ (cfMat (b n)) p q := by
      intro p q
      fin_cases p <;> fin_cases q
      · change (a n : ℤ) ≤ (b n : ℤ); exact_mod_cast hle n
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
    have hnnA : ∀ p q : Fin 2, 0 ≤ (cfProd (0 :: cfPrefixList a n)) p q :=
      cfProd_nonneg _
    have hnnM : ∀ p q : Fin 2, 0 ≤ (cfMat (b n)) p q := by
      intro p q; fin_cases p <;> fin_cases q <;> simp [cfMat]
    have t0 : (cfProd (0 :: cfPrefixList a n)) i 0 * (cfMat (a n)) 0 j ≤
        (cfProd (0 :: cfPrefixList b n)) i 0 * (cfMat (b n)) 0 j :=
      mul_le_mul (ih i 0) (hmn 0 j) (by fin_cases j <;> simp [cfMat]) (by
        have := hnnA i 0; linarith [ih i 0])
    have t1 : (cfProd (0 :: cfPrefixList a n)) i 1 * (cfMat (a n)) 1 j ≤
        (cfProd (0 :: cfPrefixList b n)) i 1 * (cfMat (b n)) 1 j :=
      mul_le_mul (ih i 1) (hmn 1 j) (by fin_cases j <;> simp [cfMat]) (by
        have := hnnA i 1; linarith [ih i 1])
    exact add_le_add t0 t1

lemma mobius_cfProd_snoc_one_div (w : List ℕ) (a : ℕ) (ha : 1 ≤ a)
    {t : ℝ} (ht0 : 0 < t) :
    mobius (cfProd (0 :: (w ++ [a]))) t =
      mobius (cfProd (0 :: w)) (1 / ((a : ℝ) + t)) := by
  have hcons : (0 :: (w ++ [a])) = (0 :: w) ++ [a] := rfl
  rw [hcons, cfProd_append_single]
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hdenN : ((cfProd [a] 0 0 : ℝ) + (cfProd [a] 0 1 : ℝ) * t) ≠ 0 := by
    simp only [cfProd, Matrix.mul_one, cfMat, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Int.cast_natCast, Int.cast_one]
    linarith
  have hm := mobius_mul (cfProd (0 :: w)) (cfProd [a]) t
  change mobius (cfProd (0 :: w) * cfMat a) t = _
  rw [show cfMat a = cfProd [a] by simp [cfProd]]
  rw [hm hdenN]
  simp only [cfProd, cfMat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Int.cast_natCast, Int.cast_one, Int.cast_zero, zero_mul, add_zero, mul_one, one_mul]

lemma mobius_cfProd_zero_nil (t : ℝ) : mobius (cfProd [0]) t = t := by
  simp [mobius, cfProd, cfMat]

/-- Fractional remainder at step `n` of the regular continued fraction of `x`. -/
def cfTail (x : ℝ) (n : ℕ) : ℝ :=
  (GenContFract.IntFractPair.stream x n).elim 0 (fun p => p.fr)

/-- Exact finite-step identity for arbitrary irrationals `x ∈ (0, 1)`. -/
theorem irrational_cf_stream_spec {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hirr : Irrational x) :
    ∀ n : ℕ, ∃ p : GenContFract.IntFractPair ℝ,
      GenContFract.IntFractPair.stream x n = some p ∧
      0 < p.fr ∧ p.fr < 1 ∧
      cfTail x n = p.fr ∧
      1 ≤ cfDigit x n ∧
      (cfDigit x n : ℝ) = ⌊p.fr⁻¹⌋ ∧
      cfTail x n = 1 / ((cfDigit x n : ℝ) + cfTail x (n + 1)) ∧
      x = mobius (cfProd (0 :: cfPrefixList (cfDigit x) n)) (cfTail x n) := by
  have hnt : ¬ (GenContFract.of x).Terminates := by
    intro hterm
    rcases (GenContFract.terminates_iff_rat x).mp hterm with ⟨q, hq⟩
    exact hirr ⟨q, hq.symm⟩
  have hstream : ∀ n : ℕ, ∃ p : GenContFract.IntFractPair ℝ,
      GenContFract.IntFractPair.stream x n = some p ∧ 0 < p.fr ∧ p.fr < 1 := by
    intro n
    induction n with
    | zero =>
      have hfl : ⌊x⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simp [le_of_lt hx0], by simp [hx1]⟩
      refine ⟨GenContFract.IntFractPair.of x, GenContFract.IntFractPair.stream_zero x, ?_, ?_⟩
      · simpa [GenContFract.IntFractPair.of, Int.fract, hfl] using hx0
      · simpa [GenContFract.IntFractPair.of, Int.fract, hfl] using hx1
    | succ n ih =>
      obtain ⟨p, hp, hp0, hp1⟩ := ih
      have hsucc := GenContFract.IntFractPair.stream_succ_of_some hp (ne_of_gt hp0)
      set p' := GenContFract.IntFractPair.of p.fr⁻¹
      have hp'1 : p'.fr < 1 := Int.fract_lt_one _
      have hp'0 : 0 < p'.fr := by
        have hnn : 0 ≤ p'.fr := Int.fract_nonneg _
        refine lt_of_le_of_ne hnn ?_
        intro hzero
        have hnone := GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero hsucc hzero.symm
        exact hnt ⟨n + 1,
          (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).mpr hnone⟩
      exact ⟨p', hsucc, hp'0, hp'1⟩
  have hstep : ∀ n : ℕ, ∃ p : GenContFract.IntFractPair ℝ,
      GenContFract.IntFractPair.stream x n = some p ∧
      0 < p.fr ∧ p.fr < 1 ∧
      1 ≤ cfDigit x n ∧
      (cfDigit x n : ℝ) = (⌊p.fr⁻¹⌋ : ℝ) ∧
      cfTail x n = 1 / ((cfDigit x n : ℝ) + cfTail x (n + 1)) := by
    intro n
    obtain ⟨p, hp, hp0, hp1⟩ := hstream n
    have hsucc := GenContFract.IntFractPair.stream_succ_of_some hp (ne_of_gt hp0)
    have hget := GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hsucc
    have hbZ : 1 ≤ ⌊p.fr⁻¹⌋ := by
      rw [Int.le_floor, Int.cast_one]
      exact le_of_lt ((one_lt_inv₀ hp0).mpr hp1)
    have hdig : cfDigit x n = Int.toNat ⌊p.fr⁻¹⌋ := by
      simp [cfDigit, hget, GenContFract.IntFractPair.of]
    have hdig1 : 1 ≤ cfDigit x n := by
      rw [hdig]
      omega
    have hdig_cast : (cfDigit x n : ℝ) = (⌊p.fr⁻¹⌋ : ℝ) := by
      rw [hdig]
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ ⌊p.fr⁻¹⌋)
    have htail_n : cfTail x n = p.fr := by simp [cfTail, hp]
    have htail_s : cfTail x (n + 1) = Int.fract p.fr⁻¹ := by
      simp [cfTail, hsucc, GenContFract.IntFractPair.of]
    have hinv_eq : p.fr⁻¹ = (cfDigit x n : ℝ) + cfTail x (n + 1) := by
      rw [hdig_cast, htail_s, Int.fract]
      ring
    have hden_pos : 0 < (cfDigit x n : ℝ) + cfTail x (n + 1) := by
      rw [← hinv_eq]
      exact inv_pos.mpr hp0
    have htail_eq : cfTail x n = 1 / ((cfDigit x n : ℝ) + cfTail x (n + 1)) := by
      rw [htail_n, ← hinv_eq, one_div, inv_inv]
    exact ⟨p, hp, hp0, hp1, hdig1, hdig_cast, htail_eq⟩
  have hmob_eq : ∀ n : ℕ, x = mobius (cfProd (0 :: cfPrefixList (cfDigit x) n)) (cfTail x n) := by
    intro n
    induction n with
    | zero =>
      have ht0 : cfTail x 0 = x := by
        have hfl : ⌊x⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simp [le_of_lt hx0], by simp [hx1]⟩
        simp [cfTail, GenContFract.IntFractPair.stream_zero, GenContFract.IntFractPair.of,
          Int.fract, hfl]
      rw [ht0, cfPrefixList_zero, mobius_cfProd_zero_nil]
    | succ n ih =>
      obtain ⟨_, _, _, _, hdig0, _, hstep0⟩ := hstep n
      obtain ⟨_, _, hp1_pos, _, _, _, _⟩ := hstep (n + 1)
      have htail_pos : 0 < cfTail x (n + 1) := by
        obtain ⟨p1, hp1s, hp1_0, _⟩ := hstream (n + 1)
        simpa [cfTail, hp1s] using hp1_0
      rw [cfPrefixList_succ, mobius_cfProd_snoc_one_div _ _ hdig0 htail_pos, ← hstep0, ← ih]
  intro n
  obtain ⟨p, hp, hp0, hp1, hdig1, hdig_cast, htail_eq⟩ := hstep n
  exact ⟨p, hp, hp0, hp1, by simp [cfTail, hp], hdig1, hdig_cast, htail_eq, hmob_eq n⟩

lemma cfDigit_ge_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hirr : Irrational x) (i : ℕ) :
    1 ≤ cfDigit x i :=
  (irrational_cf_stream_spec hx0 hx1 hirr i).choose_spec.2.2.2.2.1

lemma cfTail_mem_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hirr : Irrational x) (n : ℕ) :
    0 < cfTail x n ∧ cfTail x n < 1 := by
  have hs := (irrational_cf_stream_spec hx0 hx1 hirr n).choose_spec
  rw [hs.2.2.2.1]
  exact ⟨hs.2.1, hs.2.2.1⟩

lemma cfTail_recurrence {x : ℝ} (hx0 : 0 < x) (hx1 : 1 > x) (hirr : Irrational x) (n : ℕ) :
    cfTail x n = 1 / ((cfDigit x n : ℝ) + cfTail x (n + 1)) :=
  (irrational_cf_stream_spec hx0 hx1 hirr n).choose_spec.2.2.2.2.2.2.1

lemma eq_mobius_cfPrefix_cfTail {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hirr : Irrational x) (n : ℕ) :
    x = mobius (cfProd (0 :: cfPrefixList (cfDigit x) n)) (cfTail x n) :=
  (irrational_cf_stream_spec hx0 hx1 hirr n).choose_spec.2.2.2.2.2.2.2

/-- Nested cylinder interval intersection realizing any stream `a : ℕ → ℕ` (`∀ i, 1 ≤ a i`). -/
lemma nonempty_iInter_cylPair_prefix {a : ℕ → ℕ} (ha : ∀ i, 1 ≤ a i) :
    (⋂ n : ℕ, Set.Icc (cylPair (cfPrefixList a (n + 1))).1
      (cylPair (cfPrefixList a (n + 1))).2).Nonempty := by
  let S : ℕ → Set ℝ := fun n =>
    Set.Icc (cylPair (cfPrefixList a (n + 1))).1 (cylPair (cfPrefixList a (n + 1))).2
  have hS_ne : ∀ n, (S n).Nonempty := fun n =>
    ⟨mobius (cfProd (0 :: cfPrefixList a (n + 1))) (1 / 2),
      mobius_mem_cylPair (posDigits_cfPrefixList ha (n + 1))
        (by intro h; have := cfPrefixList_length a (n + 1); rw [h] at this; simp at this)
        (by norm_num) (by norm_num)⟩
  have hS_comp : ∀ n, IsCompact (S n) := fun _ => isCompact_Icc
  have hS_closed : ∀ n, IsClosed (S n) := fun _ => isClosed_Icc
  have hS_anti : Antitone S := by
    refine antitone_nat_of_succ_le fun n => ?_
    change Set.Icc (cylPair (cfPrefixList a (n + 2))).1
        (cylPair (cfPrefixList a (n + 2))).2 ⊆
      Set.Icc (cylPair (cfPrefixList a (n + 1))).1
        (cylPair (cfPrefixList a (n + 1))).2
    rw [show n + 2 = (n + 1) + 1 by omega, cfPrefixList_succ]
    exact cylPair_nest (posDigits_cfPrefixList ha (n + 1))
      (by intro h; have := cfPrefixList_length a (n + 1); rw [h] at this; simp at this)
      (fun d hd => by rw [List.mem_singleton] at hd; rw [hd]; exact ha (n + 1))
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S (fun i => hS_anti (Nat.le_succ i)) hS_ne (hS_comp 0) hS_closed

/-- The real number `[0; a 0, a 1, ...]` corresponding to a positive sequence `a : ℕ → ℕ`. -/
def cfVal (a : ℕ → ℕ) : ℝ :=
  if h : ∀ i, 1 ≤ a i then Classical.choose (nonempty_iInter_cylPair_prefix h) else 0

lemma cfVal_mem_cylPair_Ioo {a : ℕ → ℕ} (ha : ∀ i, 1 ≤ a i) {n : ℕ} (hn : 1 ≤ n) :
    cfVal a ∈ Set.Ioo (cylPair (cfPrefixList a n)).1 (cylPair (cfPrefixList a n)).2 := by
  have hspec := Classical.choose_spec (nonempty_iInter_cylPair_prefix ha)
  have hval : cfVal a = Classical.choose (nonempty_iInter_cylPair_prefix ha) := by
    simp [cfVal, ha]
  rw [hval]
  have hmem := Set.mem_iInter.mp hspec (n + 1)
  have hlen : n + 2 = n + 2 := rfl
  have hsplit : cfPrefixList a (n + 2) =
      cfPrefixList a n ++ cfPrefixList (fun i => a (n + i)) 2 :=
    cfPrefixList_add a n 2
  have hmem' : Classical.choose (nonempty_iInter_cylPair_prefix ha) ∈
      Set.Icc (cylPair (cfPrefixList a n ++ cfPrefixList (fun i => a (n + i)) 2)).1
        (cylPair (cfPrefixList a n ++ cfPrefixList (fun i => a (n + i)) 2)).2 := by
    simpa only [← hsplit] using hmem
  exact cylPair_nest_strict (posDigits_cfPrefixList ha n)
    (by intro h; have hl := cfPrefixList_length a n; rw [h] at hl; simp at hl; omega)
    (posDigits_cfPrefixList (fun i => ha (n + i)) 2)
    (Or.inl (by simp [cfPrefixList_length]))
    hmem'

lemma cfVal_spec {a : ℕ → ℕ} (ha : ∀ i, 1 ≤ a i) :
    cfVal a ∈ Set.Ioo (0 : ℝ) 1 ∧ Irrational (cfVal a) ∧ ∀ i, cfDigit (cfVal a) i = a i := by
  have hx1 := cfVal_mem_cylPair_Ioo ha (n := 1) le_rfl
  have hunit : cfVal a ∈ Set.Ioo (0 : ℝ) 1 :=
    Ioo_cylPair_subset_Ioo_unit (posDigits_cfPrefixList ha 1)
      (by intro h; have hl := cfPrefixList_length a 1; rw [h] at hl; simp at hl) hx1
  have hdig_n : ∀ n : ℕ, ∀ i < n, cfDigit (cfVal a) i = a i := by
    intro n i hi
    have hn : 1 ≤ n := by omega
    have hxn := cfVal_mem_cylPair_Ioo ha hn
    obtain ⟨t, ht, hmob⟩ := exists_mobius_of_mem_Ioo_cylPair (posDigits_cfPrefixList ha n)
      (by intro h; have hl := cfPrefixList_length a n; rw [h] at hl; simp at hl; omega) hxn
    have hsm := stream_mobius_spec (cfPrefixList a n) (posDigits_cfPrefixList ha n) ht.1 ht.2
    dsimp only at hsm
    rw [hmob] at hsm
    have hget := hsm.2.1 i (by simpa [cfPrefixList_length] using hi)
    simp only [cfPrefixList, List.getElem_ofFn] at hget
    simp [cfDigit, hget]
  have hirr : Irrational (cfVal a) := by
    intro ⟨q, hq⟩
    obtain ⟨N, hN⟩ := (GenContFract.terminates_iff_rat (cfVal a)).mpr ⟨q, hq.symm⟩
    have hn1 : N + 1 ≤ N + 1 := le_rfl
    have hxn := cfVal_mem_cylPair_Ioo ha (n := N + 1) (by omega)
    obtain ⟨t, ht, hmob⟩ := exists_mobius_of_mem_Ioo_cylPair (posDigits_cfPrefixList ha (N + 1))
      (by intro h; have hl := cfPrefixList_length a (N + 1); rw [h] at hl; simp at hl) hxn
    have hnot := not_terminatedAt_mobius (posDigits_cfPrefixList ha (N + 1))
      ht.1 ht.2 (k := N) (by rw [cfPrefixList_length]; omega)
    rw [hmob] at hnot
    exact hnot hN
  exact ⟨hunit, hirr, fun i => hdig_n (i + 1) i (by omega)⟩

theorem cfVal_cfDigit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hirr : Irrational x) :
    cfVal (cfDigit x) = x := by
  have ha : ∀ i, 1 ≤ cfDigit x i := cfDigit_ge_one hx0 hx1 hirr
  by_contra hne
  have hpos : 0 < |cfVal (cfDigit x) - x| := abs_sub_pos.mpr hne
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / |cfVal (cfDigit x) - x|)
  have hN1 : 1 ≤ max N 1 := le_max_right _ _
  set w := cfPrefixList (cfDigit x) (max N 1)
  have hw_pd : PosDigits w := posDigits_cfPrefixList ha _
  have hw_ne : w ≠ [] := by
    intro h
    have hl := cfPrefixList_length (cfDigit x) (max N 1)
    change w.length = max N 1 at hl
    rw [h] at hl
    simp at hl
    omega
  have hx_in : x ∈ Set.Ioo (cylPair w).1 (cylPair w).2 := by
    rw [eq_mobius_cfPrefix_cfTail hx0 hx1 hirr (max N 1)]
    have ht := cfTail_mem_Ioo hx0 hx1 hirr (max N 1)
    exact mobius_mem_Ioo_cylPair hw_pd hw_ne ht.1 ht.2
  have hv_in : cfVal (cfDigit x) ∈ Set.Ioo (cylPair w).1 (cylPair w).2 :=
    cfVal_mem_cylPair_Ioo ha hN1
  have hdiff_lt : |cfVal (cfDigit x) - x| ≤ (cylPair w).2 - (cylPair w).1 := by
    rw [abs_le]
    exact ⟨by linarith [hv_in.1, hx_in.2], by linarith [hv_in.2, hx_in.1]⟩
  have hden := (cfProd_zero_cons_den_ge hw_pd).1
  have hlen_w : w.length = max N 1 := cfPrefixList_length _ _
  have hq_ge : ((max N 1 : ℕ) : ℝ) ≤ ((cfProd (0 :: w)) 1 0 : ℝ) := by
    exact_mod_cast hlen_w ▸ hden
  have hq_pos : (0 : ℝ) < ((cfProd (0 :: w)) 1 0 : ℝ) := by
    have : (1 : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast hN1
    linarith
  have hp_nn : (0 : ℝ) ≤ ((cfProd (0 :: w)) 1 1 : ℝ) := by
    exact_mod_cast cfProd_nonneg (0 :: w) 1 1
  have hlen_le : (cylPair w).2 - (cylPair w).1 ≤ 1 / ((cfProd (0 :: w)) 1 0 : ℝ) := by
    rw [cylPair_len hw_pd hw_ne]
    refine one_div_le_one_div_of_le hq_pos ?_
    calc ((cfProd (0 :: w)) 1 0 : ℝ)
        = 1 * ((cfProd (0 :: w)) 1 0 : ℝ) := (one_mul _).symm
      _ ≤ ((cfProd (0 :: w)) 1 0 : ℝ) * (((cfProd (0 :: w)) 1 0 : ℝ) +
            ((cfProd (0 :: w)) 1 1 : ℝ)) := by
          refine mul_le_mul ?_ (by linarith) (le_of_lt hq_pos) (by positivity)
          have : (1 : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast hN1
          linarith
  have hlt_inv : 1 / ((max N 1 : ℕ) : ℝ) < |cfVal (cfDigit x) - x| := by
    have hm_pos : (0 : ℝ) < ((max N 1 : ℕ) : ℝ) := by exact_mod_cast hN1
    have hgt : 1 / |cfVal (cfDigit x) - x| < ((max N 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le hN (by exact_mod_cast le_max_left N 1)
    rw [div_lt_iff₀ hpos] at hgt
    rw [div_lt_iff₀ hm_pos]
    linarith
  have hinv_le : 1 / ((cfProd (0 :: w)) 1 0 : ℝ) ≤ 1 / ((max N 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast hN1) hq_ge
  linarith

/-- One-step regular CF digit shift under Gauss inverse map `x = 1 / (a + t)`. -/
lemma cfDigit_one_div_add {a : ℕ} (ha : 1 ≤ a) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (k : ℕ) :
    cfDigit (1 / ((a : ℝ) + t)) (k + 1) = cfDigit t k := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  set x : ℝ := 1 / ((a : ℝ) + t)
  have hx0 : 0 < x := div_pos zero_lt_one (by linarith)
  have hx1 : x < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hfl_x : ⌊x⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simp [le_of_lt hx0], by simp [hx1]⟩
  have hfr_x : Int.fract x = x := by simp [Int.fract, hfl_x]
  have hinv_x : (Int.fract x)⁻¹ = (a : ℝ) + t := by
    rw [hfr_x]; dsimp [x]; rw [one_div, inv_inv]
  have hfl_at : ⌊(a : ℝ) + t⌋ = (a : ℤ) :=
    Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  have hfr_at : Int.fract ((a : ℝ) + t) = t := by simp [Int.fract, hfl_at]
  have hfr_t : Int.fract t = t := by
    have hfl_t : ⌊t⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simp [le_of_lt ht0], by simp [ht1]⟩
    simp [Int.fract, hfl_t]
  have hget : (GenContFract.of x).s.get? (k + 1) = (GenContFract.of t).s.get? k := by
    rw [GenContFract.of_s_succ, hinv_x]
    cases k with
    | zero =>
      change (GenContFract.of ((a : ℝ) + t)).s.head = (GenContFract.of t).s.head
      rw [GenContFract.of_s_head (by rw [hfr_at]; exact ne_of_gt ht0),
        GenContFract.of_s_head (by rw [hfr_t]; exact ne_of_gt ht0), hfr_at, hfr_t]
    | succ k =>
      rw [GenContFract.of_s_succ, GenContFract.of_s_succ, hfr_at, hfr_t]
  simp [cfDigit, hget]

lemma cfDigit_mobius_add {w : List ℕ} (hw : PosDigits w) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (k : ℕ) :
    cfDigit (mobius (cfProd (0 :: w)) t) (w.length + k) = cfDigit t k := by
  induction w generalizing t k with
  | nil =>
    rw [mobius_cfProd_zero_nil]
    simp
  | cons a w ih =>
    obtain ⟨ha, hw'⟩ := posDigits_cons.mp hw
    have hy := mobius_cfProd_zero_mem_Ioo hw' ht0 ht1
    rw [mobius_cfProd_zero_cons ha hw' ht0 ht1, List.length_cons,
      Nat.add_right_comm w.length 1 k,
      cfDigit_one_div_add ha hy.1 hy.2 (w.length + k)]
    exact ih hw' ht0 ht1 k

lemma mobius_cfProd_zero_injOn {w : List ℕ} (hw : PosDigits w) :
    Set.InjOn (mobius (cfProd (0 :: w))) (Set.Ioo (0 : ℝ) 1) := by
  intro t₁ ht₁ t₂ ht₂ heq
  set M := cfProd (0 :: w)
  have hden : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < (M 1 0 : ℝ) + (M 1 1 : ℝ) * t := by
    intro t ht
    have hq : (1 : ℝ) ≤ (M 1 0 : ℝ) := by
      cases w with
      | nil => simp [M, cfProd, cfMat]
      | cons b rest =>
        have hc := cfProd_col0_pos hw (List.cons_ne_nil b rest)
        have hr := cfProd_zero_cons_row1 (b :: rest)
        exact_mod_cast (by linarith [hc.1, hr.1] : (1 : ℤ) ≤ M 1 0)
    have hp : (0 : ℝ) ≤ (M 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg (0 :: w) 1 1
    nlinarith [ht.1]
  have hsub := mobius_sub M t₁ t₂ (ne_of_gt (hden t₁ ht₁)) (ne_of_gt (hden t₂ ht₂))
  have hzero : mobius M t₁ - mobius M t₂ = 0 := sub_eq_zero.mpr heq
  rw [hsub] at hzero
  have hdet_ne : ((M.det : ℤ) : ℝ) ≠ 0 := by exact_mod_cast cfProd_det_ne_zero (0 :: w)
  have hden_prod : ((M 1 0 : ℝ) + (M 1 1 : ℝ) * t₁) *
      ((M 1 0 : ℝ) + (M 1 1 : ℝ) * t₂) ≠ 0 :=
    mul_ne_zero (ne_of_gt (hden t₁ ht₁)) (ne_of_gt (hden t₂ ht₂))
  rcases div_eq_zero_iff.mp hzero with hnum | hdenz
  · have hndet : -(M.det : ℝ) ≠ 0 := neg_ne_zero.mpr hdet_ne
    rcases mul_eq_zero.mp hnum with hd | hdiff
    · exact absurd hd hndet
    · linarith
  · exact absurd hdenz hden_prod

lemma irrational_mobius_iff {w : List ℕ} (hw : PosDigits w) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    Irrational (mobius (cfProd (0 :: w)) t) ↔ Irrational t := by
  set M := cfProd (0 :: w)
  have hden_pos : 0 < (M 1 0 : ℝ) + (M 1 1 : ℝ) * t := by
    have hq : (1 : ℝ) ≤ (M 1 0 : ℝ) := by
      cases w with
      | nil => simp [M, cfProd, cfMat]
      | cons b rest =>
        have hc := cfProd_col0_pos hw (List.cons_ne_nil b rest)
        have hr := cfProd_zero_cons_row1 (b :: rest)
        exact_mod_cast (by linarith [hc.1, hr.1] : (1 : ℤ) ≤ M 1 0)
    have hp : (0 : ℝ) ≤ (M 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg (0 :: w) 1 1
    nlinarith
  have hdet_ne : M.det ≠ 0 := cfProd_det_ne_zero (0 :: w)
  constructor
  · intro hirr ⟨q, hq⟩
    apply hirr
    have hqR : t = (q : ℝ) := hq.symm
    refine ⟨((M 0 0 : ℚ) + (M 0 1 : ℚ) * q) / ((M 1 0 : ℚ) + (M 1 1 : ℚ) * q), ?_⟩
    push_cast
    rw [← hqR]
    rfl
  · intro hirr ⟨q, hq⟩
    apply hirr
    have hqR : mobius M t = (q : ℝ) := hq.symm
    have hlin : (M 0 0 : ℝ) + (M 0 1 : ℝ) * t =
        (q : ℝ) * ((M 1 0 : ℝ) + (M 1 1 : ℝ) * t) := by
      unfold mobius at hqR
      exact (div_eq_iff (ne_of_gt hden_pos)).mp hqR
    have hcoeff : ((M 0 1 : ℝ) - (q : ℝ) * (M 1 1 : ℝ)) * t =
        (q : ℝ) * (M 1 0 : ℝ) - (M 0 0 : ℝ) := by linarith
    have hcoeff_ne : (M 0 1 : ℝ) - (q : ℝ) * (M 1 1 : ℝ) ≠ 0 := by
      intro hz
      have hz2 : (q : ℝ) * (M 1 0 : ℝ) - (M 0 0 : ℝ) = 0 := by
        rw [hz, zero_mul] at hcoeff
        exact hcoeff.symm
      have hdet0 : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) = 0 := by
        have hm01 : (M 0 1 : ℝ) = (q : ℝ) * (M 1 1 : ℝ) := sub_eq_zero.mp hz
        have hm00 : (M 0 0 : ℝ) = (q : ℝ) * (M 1 0 : ℝ) := (sub_eq_zero.mp hz2).symm
        rw [hm00, hm01]
        ring
      have hd : (M.det : ℝ) = 0 := by rw [Matrix.det_fin_two]; exact_mod_cast hdet0
      exact hdet_ne (by exact_mod_cast hd)
    refine ⟨((q * (M 1 0 : ℚ) - (M 0 0 : ℚ)) / ((M 0 1 : ℚ) - q * (M 1 1 : ℚ))), ?_⟩
    push_cast
    exact ((eq_div_iff hcoeff_ne).mpr (by rw [mul_comm]; exact hcoeff)).symm

/-! ### Part 2: General-modulus residue sets and uniform Lipschitz shift invariance -/

/-- Points in `(0, 1)` irrational whose partial quotients satisfy `a_i ≥ r_i` and
    `a_i ≡ r_i [MOD m]` at every position `i`. -/
def residueSeqSet (m : ℕ) (r : ℕ → ℕ) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 | Irrational x ∧ ∀ i, r i ≤ cfDigit x i ∧ cfDigit x i % m = r i % m}

/-- Stationary constant-residue set `F_{m, r} = residueSeqSet m (fun _ => r)`. -/
def residueConstSet (m r : ℕ) : Set ℝ :=
  residueSeqSet m (fun _ => r)

/-- Eventually residue-restricted set (`∃ N, ∀ i ≥ N, a_i ≥ r_i ∧ a_i ≡ r_i [MOD m]`). -/
def eventualResidueSeqSet (m : ℕ) (r : ℕ → ℕ) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 |
    Irrational x ∧ ∃ N, ∀ i ≥ N, r i ≤ cfDigit x i ∧ cfDigit x i % m = r i % m}

/-- Predicate that a residue sequence `r : ℕ → ℕ` is eventually periodic. -/
def IsEventuallyPeriodic (r : ℕ → ℕ) : Prop :=
  ∃ N p, 1 ≤ p ∧ ∀ i ≥ N, r (i + p) = r i

/-- Union of all `eventualResidueSeqSet m r` over sequences eventually periodic into `{1,...,m}`. -/
def eventuallyPeriodicResidueSet (m : ℕ) : Set ℝ :=
  ⋃ (r : ℕ → ℕ)
    (_ : ∃ N p, 1 ≤ p ∧ ∀ i ≥ N, 1 ≤ r i ∧ r i ≤ m ∧ r (i + p) = r i),
    eventualResidueSeqSet m r

/-- Perturbation map adding `c i` to the `i`-th partial quotient. -/
def cfShiftMap (c : ℕ → ℕ) (x : ℝ) : ℝ :=
  cfVal (fun i => cfDigit x i + c i)

lemma cfShiftMap_image {m : ℕ} {r : ℕ → ℕ} (hr : ∀ i, 1 ≤ r i) (c : ℕ → ℕ) :
    cfShiftMap c '' residueSeqSet m r = residueSeqSet m (fun i => r i + c i) := by
  ext y
  constructor
  · rintro ⟨x, ⟨⟨hx0, hx1⟩, hirr, hres⟩, rfl⟩
    have ha : ∀ i, 1 ≤ cfDigit x i + c i := fun i =>
      le_trans (cfDigit_ge_one hx0 hx1 hirr i) (Nat.le_add_right _ _)
    obtain ⟨hy01, hyirr, hdig⟩ := cfVal_spec ha
    refine ⟨hy01, hyirr, fun i => ?_⟩
    unfold cfShiftMap
    rw [hdig i]
    obtain ⟨hle, hmod⟩ := hres i
    refine ⟨Nat.add_le_add_right hle (c i), ?_⟩
    rw [Nat.add_mod, hmod, ← Nat.add_mod]
  · rintro ⟨⟨hy0, hy1⟩, hyirr, hres⟩
    let a : ℕ → ℕ := fun i => cfDigit y i - c i
    have ha_ge : ∀ i, r i ≤ a i := fun i => by
      have h1 : r i + c i ≤ cfDigit y i := (hres i).1
      dsimp only [a]
      omega
    have ha1 : ∀ i, 1 ≤ a i := fun i => le_trans (hr i) (ha_ge i)
    have hmod_a : ∀ i, a i % m = r i % m := by
      intro i
      have h1 : r i + c i ≤ cfDigit y i := (hres i).1
      have hmod := (hres i).2
      have hadd : a i + c i = cfDigit y i := by dsimp only [a]; omega
      rw [← hadd] at hmod
      have hme : (a i : ℤ) + (c i : ℤ) ≡ (r i : ℤ) + (c i : ℤ) [ZMOD m] := by
        rw [Int.ModEq, ← Int.natCast_add, ← Int.natCast_add]
        exact_mod_cast hmod
      exact_mod_cast (Int.ModEq.add_right_cancel' (c i : ℤ) hme).eq
    set x := cfVal a
    obtain ⟨hx01, hxirr, hdx⟩ := cfVal_spec ha1
    refine ⟨x, ⟨hx01, hxirr, fun i => ?_⟩, ?_⟩
    · rw [hdx i]
      exact ⟨ha_ge i, hmod_a i⟩
    · unfold cfShiftMap
      have hfun : (fun i => cfDigit x i + c i) = cfDigit y := by
        funext i
        rw [hdx i]
        exact Nat.sub_add_cancel (le_trans (Nat.le_add_left _ _) (hres i).1)
      rw [hfun, cfVal_cfDigit hy0 hy1 hyirr]

/-- Auxiliary ordered tail bound at first differing digit `a_n < a'_n` with `2 ≤ a'_n - a_n`. -/
private lemma diff_shift_bound_ordered {a_n a'_n c_n : ℕ} {u u' v v' : ℝ}
    (ha_pos : 1 ≤ a_n) (hlt : a_n + 2 ≤ a'_n)
    (hu : 0 < u ∧ u < 1) (hu' : 0 < u' ∧ u' < 1)
    (hv : 0 < v ∧ v < 1) (hv' : 0 < v' ∧ v' < 1) :
    let t : ℝ := 1 / ((a_n : ℝ) + u)
    let t' : ℝ := 1 / ((a'_n : ℝ) + u')
    let s : ℝ := 1 / (((a_n + c_n : ℕ) : ℝ) + v)
    let s' : ℝ := 1 / (((a'_n + c_n : ℕ) : ℝ) + v')
    |s - s'| ≤ 6 * |t - t'| := by
  intro t t' s s'
  have haR : (1 : ℝ) ≤ (a_n : ℝ) := by exact_mod_cast ha_pos
  have ha'_ge : (a_n : ℝ) + 2 ≤ (a'_n : ℝ) := by exact_mod_cast hlt
  have ha'_pos : (0 : ℝ) < (a'_n : ℝ) := by linarith
  set D : ℝ := (a'_n : ℝ) - (a_n : ℝ)
  have hD2 : 2 ≤ D := by dsimp [D]; linarith
  have hden_t : 1 / ((a_n : ℝ) + 1) < t :=
    one_div_lt_one_div_of_lt (by linarith [hu.1]) (by linarith [hu.2])
  have hden_t' : t' < 1 / (a'_n : ℝ) :=
    one_div_lt_one_div_of_lt ha'_pos (by linarith [hu'.1])
  have ht_sub : D / (4 * (a_n : ℝ) * (a'_n : ℝ)) ≤ t - t' := by
    have hdiff : t - t' ≥ 1 / ((a_n : ℝ) + 1) - 1 / (a'_n : ℝ) := by linarith
    have halg : 1 / ((a_n : ℝ) + 1) - 1 / (a'_n : ℝ) =
        (D - 1) / (((a_n : ℝ) + 1) * (a'_n : ℝ)) := by
      have ha1 : (a_n : ℝ) + 1 ≠ 0 := by linarith
      have ha'0 : (a'_n : ℝ) ≠ 0 := ne_of_gt ha'_pos
      dsimp [D]; field_simp; ring
    have hnum : D / 2 ≤ D - 1 := by linarith
    have hden_le : ((a_n : ℝ) + 1) * (a'_n : ℝ) ≤ 2 * (a_n : ℝ) * (a'_n : ℝ) := by nlinarith
    have h1 : (D / 2) / (((a_n : ℝ) + 1) * (a'_n : ℝ)) ≤
        (D - 1) / (((a_n : ℝ) + 1) * (a'_n : ℝ)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    have h2 : (D / 2) / (2 * (a_n : ℝ) * (a'_n : ℝ)) ≤
        (D / 2) / (((a_n : ℝ) + 1) * (a'_n : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden_le
    have h3 : (D / 2) / (2 * (a_n : ℝ) * (a'_n : ℝ)) = D / (4 * (a_n : ℝ) * (a'_n : ℝ)) := by
      ring
    linarith
  have ht_pos : 0 < t - t' := lt_of_lt_of_le (by positivity) ht_sub
  have ht_abs : |t - t'| = t - t' := abs_of_pos ht_pos
  have hc_nn : (0 : ℝ) ≤ (c_n : ℝ) := Nat.cast_nonneg c_n
  have hb_ge : (a_n : ℝ) ≤ ((a_n + c_n : ℕ) : ℝ) := by push_cast; linarith
  have hb'_ge : (a'_n : ℝ) ≤ ((a'_n + c_n : ℕ) : ℝ) := by push_cast; linarith
  have hb'_diff : ((a'_n + c_n : ℕ) : ℝ) - ((a_n + c_n : ℕ) : ℝ) = D := by
    push_cast; dsimp [D]; ring
  have hs_up : s < 1 / ((a_n + c_n : ℕ) : ℝ) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith [hv.1])
  have hs_lo : 1 / (((a_n + c_n : ℕ) : ℝ) + 1) < s :=
    one_div_lt_one_div_of_lt (by linarith [hv.1]) (by linarith [hv.2])
  have hs'_up : s' < 1 / ((a'_n + c_n : ℕ) : ℝ) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith [hv'.1])
  have hs'_lo : 1 / (((a'_n + c_n : ℕ) : ℝ) + 1) < s' :=
    one_div_lt_one_div_of_lt (by linarith [hv'.1]) (by linarith [hv'.2])
  have hs'_lt_s : s' < s := by
    have hsep : 1 / ((a'_n + c_n : ℕ) : ℝ) ≤ 1 / (((a_n + c_n : ℕ) : ℝ) + 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith [hb'_diff, hD2])
    linarith
  have hs_abs : |s - s'| = s - s' := abs_of_pos (sub_pos.mpr hs'_lt_s)
  have hs_le : s - s' ≤ (3 / 2 : ℝ) * D / ((a_n : ℝ) * (a'_n : ℝ)) := by
    have hdiff : s - s' ≤ 1 / ((a_n + c_n : ℕ) : ℝ) - 1 / (((a'_n + c_n : ℕ) : ℝ) + 1) := by
      linarith
    have halg : 1 / ((a_n + c_n : ℕ) : ℝ) - 1 / (((a'_n + c_n : ℕ) : ℝ) + 1) =
        (D + 1) / (((a_n + c_n : ℕ) : ℝ) * (((a'_n + c_n : ℕ) : ℝ) + 1)) := by
      have hbn : ((a_n + c_n : ℕ) : ℝ) ≠ 0 := by linarith
      have hb'1 : ((a'_n + c_n : ℕ) : ℝ) + 1 ≠ 0 := by linarith
      rw [← hb'_diff]; field_simp; ring
    have hnum : D + 1 ≤ (3 / 2 : ℝ) * D := by linarith
    have hden_ge : (a_n : ℝ) * (a'_n : ℝ) ≤
        ((a_n + c_n : ℕ) : ℝ) * (((a'_n + c_n : ℕ) : ℝ) + 1) :=
      mul_le_mul hb_ge (by linarith) (le_of_lt ha'_pos) (by linarith)
    have h1 : (D + 1) / (((a_n + c_n : ℕ) : ℝ) * (((a'_n + c_n : ℕ) : ℝ) + 1)) ≤
        ((3 / 2 : ℝ) * D) / (((a_n + c_n : ℕ) : ℝ) * (((a'_n + c_n : ℕ) : ℝ) + 1)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    have h2 : ((3 / 2 : ℝ) * D) / (((a_n + c_n : ℕ) : ℝ) * (((a'_n + c_n : ℕ) : ℝ) + 1)) ≤
        ((3 / 2 : ℝ) * D) / ((a_n : ℝ) * (a'_n : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
    linarith
  rw [hs_abs, ht_abs]
  calc s - s' ≤ (3 / 2 : ℝ) * D / ((a_n : ℝ) * (a'_n : ℝ)) := hs_le
    _ = 6 * (D / (4 * (a_n : ℝ) * (a'_n : ℝ))) := by ring
    _ ≤ 6 * (t - t') := by linarith

private lemma cfShift_lip_lt {m : ℕ} (hm : 2 ≤ m) {r : ℕ → ℕ} (_hr : ∀ i, 1 ≤ r i)
    (c : ℕ → ℕ) {x x' : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hxirr : Irrational x)
    (hxr : ∀ i, r i ≤ cfDigit x i ∧ cfDigit x i % m = r i % m)
    (hx'0 : 0 < x') (hx'1 : x' < 1) (hx'irr : Irrational x')
    (hx'r : ∀ i, r i ≤ cfDigit x' i ∧ cfDigit x' i % m = r i % m)
    (n : ℕ) (hn_lt : ∀ i < n, cfDigit x i = cfDigit x' i)
    (hord : cfDigit x n < cfDigit x' n) :
    |cfShiftMap c x - cfShiftMap c x'| ≤ 24 * |x - x'| := by
  -- `cfDigit x n < cfDigit x' n` with same residue mod `m ≥ 2` gives `x_n + 2 ≤ x'_n`
  have hmod : cfDigit x n % m = cfDigit x' n % m := by
    rw [(hxr n).2, (hx'r n).2]
  have hsep : cfDigit x n + 2 ≤ cfDigit x' n := by
    have hdiv_eq : cfDigit x n / m < cfDigit x' n / m := by
      by_contra hge
      have hle_div : cfDigit x' n / m ≤ cfDigit x n / m := by omega
      have ha1 := Nat.div_add_mod (cfDigit x n) m
      have ha2 := Nat.div_add_mod (cfDigit x' n) m
      nlinarith
    have ha1 := Nat.div_add_mod (cfDigit x n) m
    have ha2 := Nat.div_add_mod (cfDigit x' n) m
    nlinarith
  have hpref_eq : cfPrefixList (cfDigit x) n = cfPrefixList (cfDigit x') n := by
    refine List.ext_getElem (by simp [cfPrefixList_length]) fun i hi _ => ?_
    simp only [cfPrefixList, List.getElem_ofFn]
    rw [cfPrefixList_length] at hi
    exact hn_lt i hi
  set p := cfPrefixList (cfDigit x) n
  set pShift := cfPrefixList (fun i => cfDigit x i + c i) n
  set y := cfShiftMap c x
  set y' := cfShiftMap c x'
  have ha_x : ∀ i, 1 ≤ cfDigit x i + c i := fun i =>
    le_trans (cfDigit_ge_one hx0 hx1 hxirr i) (Nat.le_add_right _ _)
  have ha_x' : ∀ i, 1 ≤ cfDigit x' i + c i := fun i =>
    le_trans (cfDigit_ge_one hx'0 hx'1 hx'irr i) (Nat.le_add_right _ _)
  obtain ⟨hy01, hyirr, hydig⟩ := cfVal_spec ha_x
  obtain ⟨hy'01, hy'irr, hy'dig⟩ := cfVal_spec ha_x'
  have hpref_y : cfPrefixList (cfDigit y) n = pShift := by
    refine List.ext_getElem (by simp [pShift, cfPrefixList_length]) fun i hi _ => ?_
    simp only [pShift, cfPrefixList, List.getElem_ofFn, y, cfShiftMap]
    exact hydig i
  have hpref_y' : cfPrefixList (cfDigit y') n = pShift := by
    refine List.ext_getElem (by simp [pShift, cfPrefixList_length]) fun i hi _ => ?_
    simp only [pShift, cfPrefixList, List.getElem_ofFn, y', cfShiftMap]
    rw [cfPrefixList_length] at hi
    rw [hy'dig i, ← hn_lt i hi]
  set M := cfProd (0 :: p)
  set MShift := cfProd (0 :: pShift)
  have hx_eq : x = mobius M (cfTail x n) := eq_mobius_cfPrefix_cfTail hx0 hx1 hxirr n
  have hx'_eq : x' = mobius M (cfTail x' n) := by
    simpa only [M, hpref_eq] using eq_mobius_cfPrefix_cfTail hx'0 hx'1 hx'irr n
  have hy_eq : y = mobius MShift (cfTail y n) := by
    change cfVal (fun i => cfDigit x i + c i) =
      mobius (cfProd (0 :: pShift)) (cfTail (cfVal (fun i => cfDigit x i + c i)) n)
    have h0 := eq_mobius_cfPrefix_cfTail hy01.1 hy01.2 hyirr n
    have hp0 : cfPrefixList (cfDigit (cfVal (fun i => cfDigit x i + c i))) n = pShift := by
      simpa only [y, cfShiftMap] using hpref_y
    rwa [hp0] at h0
  have hy'_eq : y' = mobius MShift (cfTail y' n) := by
    change cfVal (fun i => cfDigit x' i + c i) =
      mobius (cfProd (0 :: pShift)) (cfTail (cfVal (fun i => cfDigit x' i + c i)) n)
    have h0 := eq_mobius_cfPrefix_cfTail hy'01.1 hy'01.2 hy'irr n
    have hp0 : cfPrefixList (cfDigit (cfVal (fun i => cfDigit x' i + c i))) n = pShift := by
      simpa only [y', cfShiftMap] using hpref_y'
    rwa [hp0] at h0
  have hp_pd : PosDigits p := posDigits_cfPrefixList (cfDigit_ge_one hx0 hx1 hxirr) n
  have hpShift_pd : PosDigits pShift := posDigits_cfPrefixList ha_x n
  have hM10_pos : (1 : ℝ) ≤ (M 1 0 : ℝ) := by
    have h0 := (cfProd_zero_cons_den_ge hp_pd).1
    cases n with
    | zero =>
      have hp0 : p = [] := by simp [p]
      change (1 : ℝ) ≤ ((cfProd (0 :: p)) 1 0 : ℝ)
      rw [hp0]
      simp [cfProd, cfMat]
    | succ k =>
      have h1 : (1 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos k
      have h0' : ((k + 1 : ℕ) : ℤ) ≤ M 1 0 := by
        simpa only [M, p, cfPrefixList_length] using h0
      exact_mod_cast le_trans h1 h0'
  have hM11_le : (0 : ℝ) ≤ (M 1 1 : ℝ) ∧ (M 1 1 : ℝ) ≤ (M 1 0 : ℝ) :=
    ⟨by exact_mod_cast cfProd_nonneg (0 :: p) 1 1,
     by exact_mod_cast cfProd_zero_cons_col1_le_col0 hp_pd⟩
  have hM10_le_MShift : (M 1 0 : ℝ) ≤ (MShift 1 0 : ℝ) := by
    exact_mod_cast cfProd_mono_of_le (fun i => Nat.le_add_right (cfDigit x i) (c i)) n 1 0
  have hMShift11_nn : (0 : ℝ) ≤ (MShift 1 1 : ℝ) := by
    exact_mod_cast cfProd_nonneg (0 :: pShift) 1 1
  have htx := cfTail_mem_Ioo hx0 hx1 hxirr n
  have htx' := cfTail_mem_Ioo hx'0 hx'1 hx'irr n
  have hty : 0 < cfTail y n ∧ cfTail y n < 1 := by
    simpa only [y, cfShiftMap] using cfTail_mem_Ioo hy01.1 hy01.2 hyirr n
  have hty' : 0 < cfTail y' n ∧ cfTail y' n < 1 := by
    simpa only [y', cfShiftMap] using cfTail_mem_Ioo hy'01.1 hy'01.2 hy'irr n
  have hden_tx : 0 < (M 1 0 : ℝ) + (M 1 1 : ℝ) * cfTail x n := by nlinarith [htx.1]
  have hden_tx' : 0 < (M 1 0 : ℝ) + (M 1 1 : ℝ) * cfTail x' n := by nlinarith [htx'.1]
  have hden_ty : 0 < (MShift 1 0 : ℝ) + (MShift 1 1 : ℝ) * cfTail y n := by
    nlinarith [hty.1, hM10_pos, hM10_le_MShift]
  have hden_ty' : 0 < (MShift 1 0 : ℝ) + (MShift 1 1 : ℝ) * cfTail y' n := by
    nlinarith [hty'.1, hM10_pos, hM10_le_MShift]
  have hMdet : |(M.det : ℝ)| = 1 := by
    have hd := cfProd_det (0 :: p)
    rcases neg_one_pow_eq_or ℤ (0 :: p).length with h | h <;> simp [M, hd]
  have hMShiftdet : |(MShift.det : ℝ)| = 1 := by
    have hd := cfProd_det (0 :: pShift)
    rcases neg_one_pow_eq_or ℤ (0 :: pShift).length with h | h <;> simp [MShift, hd]
  have hx_diff : |cfTail x n - cfTail x' n| / (4 * (M 1 0 : ℝ) ^ 2) ≤ |x - x'| := by
    conv_rhs => rw [hx_eq, hx'_eq]
    rw [mobius_sub M _ _ (ne_of_gt hden_tx) (ne_of_gt hden_tx'),
      abs_div, abs_mul, abs_neg, hMdet, one_mul,
      abs_of_pos (mul_pos hden_tx hden_tx')]
    have hbd1 : (M 1 0 : ℝ) + (M 1 1 : ℝ) * cfTail x n ≤ 2 * (M 1 0 : ℝ) := by
      nlinarith [htx.2, hM11_le.2]
    have hbd2 : (M 1 0 : ℝ) + (M 1 1 : ℝ) * cfTail x' n ≤ 2 * (M 1 0 : ℝ) := by
      nlinarith [htx'.2, hM11_le.2]
    have hprod_le : ((M 1 0 : ℝ) + (M 1 1 : ℝ) * cfTail x n) *
        ((M 1 0 : ℝ) + (M 1 1 : ℝ) * cfTail x' n) ≤ 4 * (M 1 0 : ℝ) ^ 2 := by
      have := mul_le_mul hbd1 hbd2 (le_of_lt hden_tx') (by linarith)
      linarith
    exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hden_tx hden_tx') hprod_le
  have hy_diff : |y - y'| ≤ |cfTail y n - cfTail y' n| / (M 1 0 : ℝ) ^ 2 := by
    conv_lhs => rw [hy_eq, hy'_eq]
    rw [mobius_sub MShift _ _ (ne_of_gt hden_ty) (ne_of_gt hden_ty'),
      abs_div, abs_mul, abs_neg, hMShiftdet, one_mul,
      abs_of_pos (mul_pos hden_ty hden_ty')]
    have hbd1 : (M 1 0 : ℝ) ≤ (MShift 1 0 : ℝ) + (MShift 1 1 : ℝ) * cfTail y n := by
      nlinarith [hty.1]
    have hbd2 : (M 1 0 : ℝ) ≤ (MShift 1 0 : ℝ) + (MShift 1 1 : ℝ) * cfTail y' n := by
      nlinarith [hty'.1]
    have hprod_ge : (M 1 0 : ℝ) ^ 2 ≤ ((MShift 1 0 : ℝ) + (MShift 1 1 : ℝ) * cfTail y n) *
        ((MShift 1 0 : ℝ) + (MShift 1 1 : ℝ) * cfTail y' n) := by
      have := mul_le_mul hbd1 hbd2 (by linarith) (by linarith)
      linarith
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hprod_ge
  have hrec_tx := cfTail_recurrence hx0 hx1 hxirr n
  have hrec_tx' := cfTail_recurrence hx'0 hx'1 hx'irr n
  have hrec_ty : cfTail y n = 1 / ((cfDigit x n + c n : ℕ) + cfTail y (n + 1)) := by
    simpa only [y, cfShiftMap, hydig n] using cfTail_recurrence hy01.1 hy01.2 hyirr n
  have hrec_ty' : cfTail y' n = 1 / ((cfDigit x' n + c n : ℕ) + cfTail y' (n + 1)) := by
    simpa only [y', cfShiftMap, hy'dig n] using cfTail_recurrence hy'01.1 hy'01.2 hy'irr n
  have htail_lip := diff_shift_bound_ordered (c_n := c n)
    (cfDigit_ge_one hx0 hx1 hxirr n) hsep
    (cfTail_mem_Ioo hx0 hx1 hxirr (n + 1))
    (cfTail_mem_Ioo hx'0 hx'1 hx'irr (n + 1))
    (by simpa only [y, cfShiftMap] using cfTail_mem_Ioo hy01.1 hy01.2 hyirr (n + 1))
    (by simpa only [y', cfShiftMap] using cfTail_mem_Ioo hy'01.1 hy'01.2 hy'irr (n + 1))
  dsimp only at htail_lip
  dsimp only [y, y', cfShiftMap] at hrec_ty hrec_ty'
  rw [← hrec_tx, ← hrec_tx', ← hrec_ty, ← hrec_ty'] at htail_lip
  change |cfTail y n - cfTail y' n| ≤ 6 * |cfTail x n - cfTail x' n| at htail_lip
  have hdiv_le : |cfTail y n - cfTail y' n| / (M 1 0 : ℝ) ^ 2 ≤
      24 * (|cfTail x n - cfTail x' n| / (4 * (M 1 0 : ℝ) ^ 2)) := by
    have hsq_pos : 0 < (M 1 0 : ℝ) ^ 2 := by positivity
    rw [show 24 * (|cfTail x n - cfTail x' n| / (4 * (M 1 0 : ℝ) ^ 2)) =
        (6 * |cfTail x n - cfTail x' n|) / (M 1 0 : ℝ) ^ 2 by ring]
    exact div_le_div_of_nonneg_right htail_lip (le_of_lt hsq_pos)
  exact hy_diff.trans (hdiv_le.trans (mul_le_mul_of_nonneg_left hx_diff (by norm_num)))

/-- **Uniform `24`-Lipschitz Equivalence** (`K = 24 ≤ 48`):
    for EVERY modulus `m ≥ 2`, ANY `r : ℕ → ℕ` with `∀ i, 1 ≤ r i`, and ANY shift `c : ℕ → ℕ`,
    `cfShiftMap c` is `24`-Lipschitz on `residueSeqSet m r`. -/
theorem lipschitzOnWith_cfShift {m : ℕ} (hm : 2 ≤ m) {r : ℕ → ℕ} (hr : ∀ i, 1 ≤ r i)
    (c : ℕ → ℕ) :
    LipschitzOnWith 24 (cfShiftMap c) (residueSeqSet m r) := by
  intro x hx x' hx'
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
    ← ENNReal.ofReal_coe_nnreal, NNReal.coe_ofNat,
    ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  by_cases heq : x = x'
  · subst heq; simp
  rcases hx with ⟨⟨hx0, hx1⟩, hxirr, hxr⟩
  rcases hx' with ⟨⟨hx'0, hx'1⟩, hx'irr, hx'r⟩
  have hex_diff : ∃ i : ℕ, cfDigit x i ≠ cfDigit x' i := by
    by_contra hall
    push Not at hall
    have hfun : cfDigit x = cfDigit x' := funext hall
    apply heq
    rw [← cfVal_cfDigit hx0 hx1 hxirr, hfun, cfVal_cfDigit hx'0 hx'1 hx'irr]
  classical
  let n : ℕ := Nat.find hex_diff
  have hn_ne : cfDigit x n ≠ cfDigit x' n := Nat.find_spec hex_diff
  have hn_lt : ∀ i < n, cfDigit x i = cfDigit x' i := fun i hi =>
    of_not_not (Nat.find_min hex_diff hi)
  rcases lt_trichotomy (cfDigit x n) (cfDigit x' n) with hlt | heqn | hgt
  · exact cfShift_lip_lt hm hr c hx0 hx1 hxirr hxr hx'0 hx'1 hx'irr hx'r n hn_lt hlt
  · exact absurd heqn hn_ne
  · rw [abs_sub_comm (cfShiftMap c x), abs_sub_comm x]
    exact cfShift_lip_lt hm hr c hx'0 hx'1 hx'irr hx'r hx0 hx1 hxirr hxr n
      (fun i hi => (hn_lt i hi).symm) hgt

/-- Hausdorff dimension monotonicity under arbitrary nonnegative coordinate shifts (`m ≥ 2`). -/
theorem dimH_residueSeqSet_add_le {m : ℕ} (hm : 2 ≤ m) {r : ℕ → ℕ} (hr : ∀ i, 1 ≤ r i)
    (c : ℕ → ℕ) :
    dimH (residueSeqSet m (fun i => r i + c i)) ≤ dimH (residueSeqSet m r) := by
  rw [← cfShiftMap_image hr c]
  exact (lipschitzOnWith_cfShift hm hr c).dimH_image_le

/-- **Category-1 Unconditional General-Modulus Sandwich Theorem (`m ≥ 2`)**:
    for EVERY modulus `m ≥ 2` and EVERY sequence `r : ℕ → ℕ` with `∀ i, 1 ≤ r i ∧ r i ≤ m`,
    `dimH F_{m,m} ≤ dimH F_m(r) ≤ dimH F_{m,1}`. -/
theorem dimH_residueSeqSet_sandwich {m : ℕ} (hm : 2 ≤ m) {r : ℕ → ℕ}
    (hr : ∀ i, 1 ≤ r i ∧ r i ≤ m) :
    dimH (residueConstSet m m) ≤ dimH (residueSeqSet m r) ∧
      dimH (residueSeqSet m r) ≤ dimH (residueConstSet m 1) := by
  have h1 : ∀ i : ℕ, 1 ≤ (1 : ℕ) := fun _ => le_rfl
  constructor
  · have hsum : (fun i => r i + (m - r i)) = (fun _ => m) := by
      funext i; exact Nat.add_sub_of_le (hr i).2
    simpa only [residueConstSet, hsum] using
      dimH_residueSeqSet_add_le hm (fun i => (hr i).1) (fun i => m - r i)
  · have hsum : (fun i => 1 + (r i - 1)) = r := by
      funext i
      have hri := (hr i).1
      omega
    have hle := dimH_residueSeqSet_add_le hm (m := m) (r := fun _ => 1) h1 (fun i => r i - 1)
    simpa only [residueConstSet, hsum] using hle

/-- Möbius prefix map preserves Hausdorff dimension on any `S ⊆ (0, 1)`. -/
theorem dimH_mobius_prefix_eq {w : List ℕ} (hw : PosDigits w) {S : Set ℝ}
    (hS : S ⊆ Set.Ioo (0 : ℝ) 1) :
    dimH (mobius (cfProd (0 :: w)) '' S) = dimH S := by
  set M := cfProd (0 :: w)
  have hM10 : (1 : ℝ) ≤ (M 1 0 : ℝ) := by
    cases w with
    | nil => simp [M, cfProd, cfMat]
    | cons b rest =>
      have hc := cfProd_col0_pos hw (List.cons_ne_nil b rest)
      have hr := cfProd_zero_cons_row1 (b :: rest)
      exact_mod_cast (by linarith [hc.1, hr.1] : (1 : ℤ) ≤ M 1 0)
  have hM11 : (0 : ℝ) ≤ (M 1 1 : ℝ) ∧ (M 1 1 : ℝ) ≤ (M 1 0 : ℝ) :=
    ⟨by exact_mod_cast cfProd_nonneg (0 :: w) 1 1,
     by exact_mod_cast cfProd_zero_cons_col1_le_col0 hw⟩
  have hdet : |(M.det : ℝ)| = 1 := by
    have hd := cfProd_det (0 :: w)
    rcases neg_one_pow_eq_or ℤ (0 :: w).length with h | h <;> simp [M, hd]
  have hfwd : LipschitzOnWith 1 (mobius M) S := by
    intro t ht t' ht'
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ENNReal.coe_one, one_mul]
    apply ENNReal.ofReal_le_ofReal
    have ht01 := hS ht
    have ht'01 := hS ht'
    have hd1 : (1 : ℝ) ≤ (M 1 0 : ℝ) + (M 1 1 : ℝ) * t := by nlinarith [ht01.1]
    have hd2 : (1 : ℝ) ≤ (M 1 0 : ℝ) + (M 1 1 : ℝ) * t' := by nlinarith [ht'01.1]
    rw [mobius_sub M t t' (by linarith) (by linarith), abs_div, abs_mul, abs_neg, hdet, one_mul,
      abs_of_pos (mul_pos (lt_of_lt_of_le zero_lt_one hd1) (lt_of_lt_of_le zero_lt_one hd2))]
    exact div_le_self (abs_nonneg _) (by nlinarith [hd1, hd2])
  have hle : dimH (mobius M '' S) ≤ dimH S := hfwd.dimH_image_le
  -- Inverse on `mobius M '' S`
  let q : ℕ := Int.toNat (M 1 0)
  have hqR : (q : ℝ) = (M 1 0 : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (cfProd_nonneg (0 :: w) 1 0)
  let K : ℝ≥0 := ⟨4 * ((q : ℝ) ^ 2), by positivity⟩
  let g : ℝ → ℝ := fun y => if hy : ∃ t ∈ S, mobius M t = y then Classical.choose hy else 0
  have hg_img : g '' (mobius M '' S) = S := by
    ext t
    constructor
    · rintro ⟨y, ⟨t', ht', rfl⟩, rfl⟩
      have hex : ∃ s ∈ S, mobius M s = mobius M t' := ⟨t', ht', rfl⟩
      simpa only [g, hex, ↓reduceDIte] using (Classical.choose_spec hex).1
    · intro ht
      refine ⟨mobius M t, ⟨t, ht, rfl⟩, ?_⟩
      have hex : ∃ s ∈ S, mobius M s = mobius M t := ⟨t, ht, rfl⟩
      rw [show g (mobius M t) = Classical.choose hex by simp only [g, hex, ↓reduceDIte]]
      have hspec := Classical.choose_spec hex
      exact mobius_cfProd_zero_injOn hw (hS hspec.1) (hS ht) hspec.2
  have hg_lip : LipschitzOnWith K g (mobius M '' S) := by
    rintro y₁ ⟨t₁, ht₁, rfl⟩ y₂ ⟨t₂, ht₂, rfl⟩
    have hex1 : ∃ s ∈ S, mobius M s = mobius M t₁ := ⟨t₁, ht₁, rfl⟩
    have hex2 : ∃ s ∈ S, mobius M s = mobius M t₂ := ⟨t₂, ht₂, rfl⟩
    have hg1 : g (mobius M t₁) = t₁ := by
      rw [show g (mobius M t₁) = Classical.choose hex1 by simp only [g, hex1, ↓reduceDIte]]
      exact mobius_cfProd_zero_injOn hw (hS (Classical.choose_spec hex1).1) (hS ht₁)
        (Classical.choose_spec hex1).2
    have hg2 : g (mobius M t₂) = t₂ := by
      rw [show g (mobius M t₂) = Classical.choose hex2 by simp only [g, hex2, ↓reduceDIte]]
      exact mobius_cfProd_zero_injOn hw (hS (Classical.choose_spec hex2).1) (hS ht₂)
        (Classical.choose_spec hex2).2
    rw [hg1, hg2, edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg K)]
    apply ENNReal.ofReal_le_ofReal
    have ht₁01 := hS ht₁
    have ht₂01 := hS ht₂
    have hd1_nn : 0 < (M 1 0 : ℝ) + (M 1 1 : ℝ) * t₁ := by nlinarith [ht₁01.1]
    have hd2_nn : 0 < (M 1 0 : ℝ) + (M 1 1 : ℝ) * t₂ := by nlinarith [ht₂01.1]
    have hd1 : (M 1 0 : ℝ) + (M 1 1 : ℝ) * t₁ ≤ 2 * (M 1 0 : ℝ) := by
      nlinarith [ht₁01.2, hM11.2]
    have hd2 : (M 1 0 : ℝ) + (M 1 1 : ℝ) * t₂ ≤ 2 * (M 1 0 : ℝ) := by
      nlinarith [ht₂01.2, hM11.2]
    rw [mobius_sub M t₁ t₂ (ne_of_gt hd1_nn) (ne_of_gt hd2_nn), abs_div, abs_mul, abs_neg,
      hdet, one_mul, abs_of_pos (mul_pos hd1_nn hd2_nn)]
    have hK_eq : (K : ℝ) = 4 * (M 1 0 : ℝ) ^ 2 := by
      change 4 * (q : ℝ) ^ 2 = 4 * (M 1 0 : ℝ) ^ 2
      rw [hqR]
    rw [hK_eq]
    have hprod_le : ((M 1 0 : ℝ) + (M 1 1 : ℝ) * t₁) *
        ((M 1 0 : ℝ) + (M 1 1 : ℝ) * t₂) ≤ 4 * (M 1 0 : ℝ) ^ 2 := by
      have := mul_le_mul hd1 hd2 (le_of_lt hd2_nn) (by linarith)
      linarith
    have hden_pos : 0 < ((M 1 0 : ℝ) + (M 1 1 : ℝ) * t₁) *
        ((M 1 0 : ℝ) + (M 1 1 : ℝ) * t₂) := mul_pos hd1_nn hd2_nn
    rw [mul_div_assoc', le_div_iff₀ hden_pos, mul_comm (4 * (M 1 0 : ℝ) ^ 2) |t₁ - t₂|]
    exact mul_le_mul_of_nonneg_left hprod_le (abs_nonneg _)
  have hge : dimH S ≤ dimH (mobius M '' S) := by
    calc dimH S = dimH (g '' (mobius M '' S)) := by rw [hg_img]
      _ ≤ dimH (mobius M '' S) := hg_lip.dimH_image_le
  exact le_antisymm hle hge

theorem dimH_eventualResidueSeqSet_le {m : ℕ} (hm : 2 ≤ m) {r : ℕ → ℕ}
    (hr : ∃ N₀, ∀ i ≥ N₀, 1 ≤ r i ∧ r i ≤ m) :
    dimH (eventualResidueSeqSet m r) ≤ dimH (residueConstSet m 1) := by
  obtain ⟨N₀, hN₀⟩ := hr
  have hcov : eventualResidueSeqSet m r ⊆
      ⋃ (N : ℕ) (w : Fin (N₀ + N) → ℕ+),
        mobius (cfProd (0 :: pnatWord w)) ''
          residueSeqSet m (fun i => r ((N₀ + N) + i)) := by
    intro x ⟨⟨hx0, hx1⟩, hirr, N, htail⟩
    let M : ℕ := N + N₀
    have hM_ge : N ≤ N₀ + N := by omega
    have hM_ge₀ : ∀ i ≥ N₀ + N, 1 ≤ r i ∧ r i ≤ m := fun i hi => hN₀ i (by omega)
    let w : Fin (N₀ + N) → ℕ+ := fun i =>
      ⟨cfDigit x i, Nat.pos_of_ne_zero (by have := cfDigit_ge_one hx0 hx1 hirr i; omega)⟩
    have hpw : pnatWord w = cfPrefixList (cfDigit x) (N₀ + N) := by
      refine List.ext_getElem (by simp [pnatWord_length, cfPrefixList_length]) fun i hi _ => ?_
      rw [pnatWord_length] at hi
      simp [pnatWord, cfPrefixList, w]
    set t := cfTail x (N₀ + N)
    have ht01 := cfTail_mem_Ioo hx0 hx1 hirr (N₀ + N)
    have hxt : x = mobius (cfProd (0 :: pnatWord w)) t := by
      rw [hpw]
      exact eq_mobius_cfPrefix_cfTail hx0 hx1 hirr (N₀ + N)
    have ht_irr : Irrational t :=
      (irrational_mobius_iff (posDigits_pnatWord w) ht01.1 ht01.2).mp (hxt ▸ hirr)
    have ht_mem : t ∈ residueSeqSet m (fun i => r ((N₀ + N) + i)) := by
      refine ⟨ht01, ht_irr, fun i => ?_⟩
      have hdig := cfDigit_mobius_add (posDigits_pnatWord w) ht01.1 ht01.2 i
      rw [← hxt, pnatWord_length] at hdig
      rw [← hdig]
      exact htail ((N₀ + N) + i) (by omega)
    exact Set.mem_iUnion.mpr ⟨N, Set.mem_iUnion.mpr ⟨w, t, ht_mem, hxt.symm⟩⟩
  refine le_trans (dimH_mono hcov) ?_
  rw [dimH_iUnion]
  refine iSup_le fun N => ?_
  rw [dimH_iUnion]
  refine iSup_le fun w => ?_
  rw [dimH_mobius_prefix_eq (posDigits_pnatWord w) (fun _ hx => hx.1)]
  exact (dimH_residueSeqSet_sandwich hm (fun i => hN₀ ((N₀ + N) + i) (by omega))).2

/-- Countable parameterization index for sequences eventually periodic into `{1, ..., m}`. -/
private structure EPRep (m : ℕ) where
  N : ℕ
  p : ℕ+
  per : Fin p → Fin m

private def epEval {m : ℕ} (rep : EPRep m) (i : ℕ) : ℕ :=
  if i < rep.N then 1 else (rep.per ⟨(i - rep.N) % rep.p, Nat.mod_lt _ rep.p.2⟩).1 + 1

private instance {m : ℕ} : Countable (EPRep m) := by
  let e : EPRep m → Σ N : ℕ, Σ p : ℕ+, Fin p → Fin m :=
    fun rep => ⟨rep.N, rep.p, rep.per⟩
  refine Function.Injective.countable (f := e) ?_
  intro a b hab
  cases a; cases b
  simp only [e, Sigma.mk.inj_iff] at hab
  rcases hab with ⟨rfl, hp⟩
  rw [heq_eq_eq, Sigma.mk.inj_iff] at hp
  rcases hp with ⟨rfl, hper⟩
  rw [heq_eq_eq] at hper
  subst hper
  rfl

/-- **Category-1 Unconditional General-Modulus Eventually Periodic Theorem (`m ≥ 2`)**:
    the countable union of all eventually periodic modulus-`m` residue sets has the exact same
    Hausdorff dimension as `residueConstSet m 1`:
    `dimH (eventuallyPeriodicResidueSet m) = dimH (residueConstSet m 1)`. -/
theorem dimH_eventuallyPeriodicResidueSet_eq {m : ℕ} (hm : 2 ≤ m) :
    dimH (eventuallyPeriodicResidueSet m) = dimH (residueConstSet m 1) := by
  have hm_pos : 0 < m := by omega
  apply le_antisymm
  · have hcov : eventuallyPeriodicResidueSet m ⊆
        ⋃ rep : EPRep m, eventualResidueSeqSet m (epEval rep) := by
      intro x hx
      rw [eventuallyPeriodicResidueSet, Set.mem_iUnion] at hx
      obtain ⟨r, hx⟩ := hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨⟨N, p, hp1, hr⟩, hxr⟩ := hx
      have hp_pos : 0 < p := by omega
      let per : Fin p → Fin m := fun j =>
        ⟨r (N + j.1) - 1, by
          have hj := hr (N + j.1) (by omega)
          omega⟩
      let rep : EPRep m := ⟨N, ⟨p, hp_pos⟩, per⟩
      refine Set.mem_iUnion.mpr ⟨rep, ?_⟩
      rcases hxr with ⟨hx01, hirr, N₁, hN₁⟩
      refine ⟨hx01, hirr, max N N₁, fun i hi => ?_⟩
      have hgeN : N ≤ i := le_trans (le_max_left _ _) hi
      have hgeN₁ : N₁ ≤ i := le_trans (le_max_right _ _) hi
      have hev_eq : epEval rep i = r i := by
        have hnot : ¬ i < N := by omega
        simp only [epEval, rep, hnot, ↓reduceIte, per, PNat.mk_coe]
        have h1 : 1 ≤ r (N + (i - N) % p) := (hr (N + (i - N) % p) (by omega)).1
        have hsub : r (N + (i - N) % p) - 1 + 1 = r (N + (i - N) % p) := Nat.sub_add_cancel h1
        rw [hsub]
        have hper_step : ∀ k : ℕ, ∀ j ≥ N, r (j + k * p) = r j := by
          intro k j hj
          induction k with
          | zero => simp
          | succ k ihk =>
            rw [Nat.add_mul, one_mul, ← Nat.add_assoc, (hr (j + k * p) (by omega)).2.2, ihk]
        have hi_eq : i = N + (i - N) % p + ((i - N) / p) * p := by
          calc i = N + (i - N) := (Nat.add_sub_cancel' hgeN).symm
            _ = N + (p * ((i - N) / p) + (i - N) % p) := by rw [Nat.div_add_mod]
            _ = N + (i - N) % p + ((i - N) / p) * p := by ring
        conv_rhs => rw [hi_eq]
        exact (hper_step ((i - N) / p) (N + (i - N) % p) (by omega)).symm
      rw [hev_eq]
      exact hN₁ i hgeN₁
    refine le_trans (dimH_mono hcov) ?_
    rw [dimH_iUnion]
    refine iSup_le fun rep => dimH_eventualResidueSeqSet_le hm ⟨rep.N, fun i hi => ?_⟩
    have hnot : ¬ i < rep.N := by omega
    simp only [epEval, hnot, ↓reduceIte]
    exact ⟨by omega, (rep.per _).2⟩
  · refine dimH_mono fun x hx => ?_
    rw [eventuallyPeriodicResidueSet, Set.mem_iUnion]
    refine ⟨fun _ => 1, Set.mem_iUnion.mpr
      ⟨⟨0, 1, le_rfl, fun _ _ => ⟨le_rfl, le_trans (by decide : 1 ≤ 2) hm, rfl⟩⟩, ?_⟩⟩
    exact ⟨hx.1, hx.2.1, 0, fun i _ => hx.2.2 i⟩

end

end ResidueModGeneral

#print axioms ResidueModGeneral.cfVal_cfDigit
#print axioms ResidueModGeneral.lipschitzOnWith_cfShift
#print axioms ResidueModGeneral.dimH_residueSeqSet_add_le
#print axioms ResidueModGeneral.dimH_residueSeqSet_sandwich
#print axioms ResidueModGeneral.dimH_mobius_prefix_eq
#print axioms ResidueModGeneral.dimH_eventualResidueSeqSet_le
#print axioms ResidueModGeneral.dimH_eventuallyPeriodicResidueSet_eq
