import EpiFormal.WindowPrescribedCFRealize

/-!
# Upper Hausdorff dimension `1/2` for bounded-window CF sets (`thm:windows`)

Closes the remaining upper-bound side of Paper 2's `thm:windows` (lines 2575–2609) in Lean 4
with ZERO unproved hypotheses beyond Lean core axioms (`propext`, `Classical.choice`,
`Quot.sound`), upgrading the `b = 1` branches of `thm:windows` to exact identities `dimH = 1/2`:

1. **Finite positive-digit denominator bounds**:
   - `cfProd_den_ge_length`: `l.length ≤ (cfProd (0 :: l)) 1 0` for `PosDigits l`.
   - `cfProd_den_ge_prod`: `(∏ i : Fin n, ((w i : ℕ) : ℝ)) ≤ ((cfProd (0 :: list w)) 1 0 : ℝ)`.
   - `Hpaper_ge_fact`: `((Nat.factorial (j - 1) : ℕ) : ℝ) ≤ WindowPaperScale.Hpaper j` for `1 ≤ j`.
2. **Super-exponential denominator growth on `boundedIncSet`**:
   - `boundedIncSet_dens_exp_growth`: for any `x ∈ boundedIncSet` and any `M > 0`,
     eventually `Real.exp (M * n) ≤ (GenContFract.of x).dens n`.
3. **Covering by level-`n` CF cylinders & `ENNReal` `tsum` bound**:
   - `exists_word_of_irrational`: every irrational `x ∈ (0, 1)` lies in the open level-`n`
     cylinder of its first `n` partial quotients `w : Fin n → ℕ+`, with `(GenContFract.of x).dens n`
     equal to `(cfProd (0 :: List.ofFn ...)) 1 0`.
   - `tsum_cfProd_den_rpow_le`: for `1 / 2 < t`,
     `∑' w : Fin n → ℕ+, ENNReal.ofReal (d_n(w)^(-2t)) ≤ (zetaTerm t)^n < ⊤`.
4. **Hausdorff measure zero & exact `= 1/2` theorems**:
   - `hausdorffMeasure_tailSet_zero`: `μH[s] (tailSet M N1) = 0` for large `M`.
   - `dimH_boundedIncSet_le_half`: `dimH boundedIncSet ≤ ENNReal.ofReal (1 / 2)`.
   - `dimH_boundedIncSet_eq_half`: `dimH boundedIncSet = ENNReal.ofReal (1 / 2)`.
   - `dimH_prescribedIncSet_eq_half`: `dimH (prescribedIncSet m) = ENNReal.ofReal (1 / 2)`.
   - `dimH_prescribedIncSetAt_eq_half`:
     `dimH (prescribedIncSetAt m (j0Prescribed M) par0) = ENNReal.ofReal (1 / 2)`.
-/

namespace WindowBoundedUpper

open Matrix Set Filter Finset ENNReal Metric Real Cylinder WindowCFRealize WindowCFBridge
  WindowNoShortCFRealize WindowPrescribedCFRealize
open scoped NNReal BigOperators Topology MeasureTheory

/-! ### Part 1: Denominator product/length bounds & factorial growth of `H_j` -/

/-- Canonical CF word as `List ℕ` for `w : Fin n → ℕ+`. -/
def pnatWord {n : ℕ} (w : Fin n → ℕ+) : List ℕ :=
  List.ofFn (fun i => (w i : ℕ))

theorem posDigits_pnatWord {n : ℕ} (w : Fin n → ℕ+) : PosDigits (pnatWord w) := by
  intro a ha
  unfold pnatWord at ha
  rw [List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  exact (w i).pos

theorem pnatWord_length {n : ℕ} (w : Fin n → ℕ+) : (pnatWord w).length = n := by
  simp [pnatWord]

/-- Denominator is at least word length for any `PosDigits` list (together with `1 ≤ u`). -/
theorem cfProd_den_ge_length_aux (l : List ℕ) (hl : PosDigits l) :
    1 ≤ (cfProd (0 :: l)) 1 0 ∧
    (l.length : ℤ) ≤ (cfProd (0 :: l)) 1 0 ∧
    (l ≠ [] → 1 ≤ (cfProd (0 :: l)) 1 1) := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [cfProd, cfMat], by simp [cfProd, cfMat], fun h => absurd rfl h⟩
  | append_singleton l a ih =>
    have hla := posDigits_append.mp hl
    have hl_dig : PosDigits l := hla.1
    have ha1 : 1 ≤ a := (posDigits_cons.mp hla.2).1
    obtain ⟨hu1, hulen, _⟩ := ih hl_dig
    have hcons : (0 :: (l ++ [a])) = (0 :: l) ++ [a] := rfl
    have h10 : (cfProd (0 :: (l ++ [a]))) 1 0 =
        (a : ℤ) * (cfProd (0 :: l)) 1 0 + (cfProd (0 :: l)) 1 1 := by
      rw [hcons, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
      simp [cfProd, cfMat]; ring
    have h11 : (cfProd (0 :: (l ++ [a]))) 1 1 = (cfProd (0 :: l)) 1 0 := by
      rw [hcons, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
      simp [cfProd, cfMat]
    have hv_nn : 0 ≤ (cfProd (0 :: l)) 1 1 := cfProd_nonneg (0 :: l) 1 1
    have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha1
    have hmul : (cfProd (0 :: l)) 1 0 ≤ (a : ℤ) * (cfProd (0 :: l)) 1 0 := by nlinarith
    have hu_new_pos : 1 ≤ (cfProd (0 :: (l ++ [a]))) 1 0 := by linarith
    have hlen_new : ((l ++ [a]).length : ℤ) ≤ (cfProd (0 :: (l ++ [a]))) 1 0 := by
      rw [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one, h10]
      by_cases hl0 : l = []
      · subst hl0; simp only [List.length_nil, Nat.cast_zero, zero_add]; linarith
      · have hv1 := (ih hl_dig).2.2 hl0
        linarith
    exact ⟨hu_new_pos, hlen_new, fun _ => by rw [h11]; exact hu1⟩

/-- Denominator of `0 :: l` is at least `l.length` for any positive-digit word. -/
theorem cfProd_den_ge_length {l : List ℕ} (hl : PosDigits l) :
    (l.length : ℝ) ≤ ((cfProd (0 :: l)) 1 0 : ℝ) := by
  exact_mod_cast (cfProd_den_ge_length_aux l hl).2.1

/-- Product lower bound on denominators: `∏ a ∈ l, a ≤ (cfProd (0 :: l)) 1 0`. -/
theorem list_prod_le_cfProd_den (l : List ℕ) (hl : PosDigits l) :
    (l.map (fun k : ℕ => (k : ℝ))).prod ≤ ((cfProd (0 :: l)) 1 0 : ℝ) := by
  induction l using List.reverseRecOn with
  | nil => simp [cfProd, cfMat]
  | append_singleton l a ih =>
    have hla := posDigits_append.mp hl
    have hl_dig : PosDigits l := hla.1
    have ha1 : 1 ≤ a := (posDigits_cons.mp hla.2).1
    have hih := ih hl_dig
    have hcons : (0 :: (l ++ [a])) = (0 :: l) ++ [a] := rfl
    have h10 : ((cfProd (0 :: (l ++ [a]))) 1 0 : ℝ) =
        (a : ℝ) * ((cfProd (0 :: l)) 1 0 : ℝ) + ((cfProd (0 :: l)) 1 1 : ℝ) := by
      rw [hcons, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
      simp [cfProd, cfMat]; ring
    have hv_nn : (0 : ℝ) ≤ ((cfProd (0 :: l)) 1 1 : ℝ) := by
      exact_mod_cast cfProd_nonneg (0 :: l) 1 1
    have ha_nn : (0 : ℝ) ≤ (a : ℝ) := by positivity
    have hprod_step :
        ((l ++ [a]).map (fun k : ℕ => (k : ℝ))).prod =
          (l.map (fun k : ℕ => (k : ℝ))).prod * (a : ℝ) := by
      simp [List.map_append]
    rw [hprod_step, h10]
    nlinarith

/-- Product lower bound indexed by `Fin n → ℕ+`. -/
theorem cfProd_den_ge_prod {n : ℕ} (w : Fin n → ℕ+) :
    (∏ i : Fin n, ((w i : ℕ) : ℝ)) ≤ ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) := by
  have h1 := list_prod_le_cfProd_den (pnatWord w) (posDigits_pnatWord w)
  have hprod : ((pnatWord w).map (fun k : ℕ => (k : ℝ))).prod =
      ∏ i : Fin n, ((w i : ℕ) : ℝ) := by
    unfold pnatWord
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  linarith [h1, hprod]

/-- Factorial lower bound on `WindowPaperScale.Hpaper j` from `3 * j ≤ H_{j+1} / H_j`. -/
theorem Hpaper_ge_fact {j : ℕ} (hj : 1 ≤ j) :
    (Nat.factorial (j - 1) : ℝ) ≤ WindowPaperScale.Hpaper j := by
  induction j, hj using Nat.le_induction with
  | base =>
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one]
    exact le_max_left _ _
  | succ j hj ih =>
    have hrat := WindowPaperScale.Rpaper_ge_three_mul hj
    have hHj : 0 < WindowPaperScale.Hpaper j := WindowPaperScale.Hpaper_pos j
    have hstep : 3 * (j : ℝ) * WindowPaperScale.Hpaper j ≤ WindowPaperScale.Hpaper (j + 1) :=
      (le_div_iff₀ hHj).mp hrat
    have hfac : Nat.factorial j = j * Nat.factorial (j - 1) :=
      (Nat.mul_factorial_pred (by omega : j ≠ 0)).symm
    have hsub : j + 1 - 1 = j := by omega
    rw [hsub, hfac, Nat.cast_mul]
    have hj_nn : (0 : ℝ) ≤ (j : ℝ) := by positivity
    have h1 : (j : ℝ) * (Nat.factorial (j - 1) : ℝ) ≤ (j : ℝ) * WindowPaperScale.Hpaper j :=
      mul_le_mul_of_nonneg_left ih hj_nn
    have h2 : (j : ℝ) * WindowPaperScale.Hpaper j ≤ 3 * (j : ℝ) * WindowPaperScale.Hpaper j := by
      nlinarith
    exact le_trans h1 (le_trans h2 hstep)

/-- Elementary factorial lower bound: `(K + 1) ^ (m - K) ≤ m!` for `K ≤ m`. -/
theorem nat_pow_le_factorial {K m : ℕ} (hKm : K ≤ m) :
    ((K + 1 : ℕ) : ℝ) ^ (m - K) ≤ (Nat.factorial m : ℝ) := by
  induction m, hKm using Nat.le_induction with
  | base =>
    simp only [Nat.sub_self, pow_zero]
    exact_mod_cast Nat.factorial_pos K
  | succ m hKm ih =>
    have hsub : m + 1 - K = (m - K) + 1 := by omega
    rw [hsub, pow_succ', Nat.factorial_succ, Nat.cast_mul]
    have hK_le : ((K + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : K + 1 ≤ m + 1)
    have hpow_nn : (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ (m - K) := by positivity
    have hfac_nn : (0 : ℝ) ≤ (Nat.factorial m : ℝ) := by positivity
    exact mul_le_mul hK_le ih hpow_nn (by positivity)

/-! ### Part 2: Irrational CF prefix extraction & super-exponential denominator growth -/

/-- Every irrational `x ∈ (0, 1)` admits a `Fin n → ℕ+` partial-quotient prefix and
    irrational remainder `t ∈ (0, 1)` with `x = mobius (cfProd (0 :: pnatWord w)) t`. -/
theorem exists_word_of_irrational :
    ∀ (n : ℕ) {x : ℝ}, Irrational x → 0 < x → x < 1 →
      ∃ (w : Fin n → ℕ+) (t : ℝ),
        Irrational t ∧ 0 < t ∧ t < 1 ∧ x = mobius (cfProd (0 :: pnatWord w)) t
  | 0, x, hirr, hx0, hx1 => by
    refine ⟨Fin.elim0, x, hirr, hx0, hx1, ?_⟩
    have hnil : pnatWord (Fin.elim0 : Fin 0 → ℕ+) = [] := by
      simp [pnatWord]
    rw [hnil]
    simp [mobius, cfProd, cfMat]
  | n + 1, x, hirr, hx0, hx1 => by
    set y : ℝ := x⁻¹
    have hy1 : 1 < y := (one_lt_inv₀ hx0).mpr hx1
    have hy_irr : Irrational y := hirr.inv
    set a : ℕ := ⌊y⌋₊
    have ha1 : 1 ≤ a := Nat.le_floor (by exact_mod_cast le_of_lt hy1)
    have ha_le : (a : ℝ) ≤ y := Nat.floor_le (by linarith)
    have hy_lt : y < (a : ℝ) + 1 := Nat.lt_floor_add_one y
    have hflZ : ⌊y⌋ = (a : ℤ) :=
      Int.floor_eq_iff.mpr ⟨by exact_mod_cast ha_le, by exact_mod_cast hy_lt⟩
    set t' : ℝ := Int.fract y
    have ht'_eq : t' = y - (a : ℝ) := by
      dsimp only [t']
      rw [Int.fract, hflZ, Int.cast_natCast]
    have ht'_ge : 0 ≤ t' := Int.fract_nonneg y
    have ht'_lt : t' < 1 := Int.fract_lt_one y
    have ht'_ne : t' ≠ 0 := by
      intro h0
      rw [ht'_eq] at h0
      exact hy_irr.ne_nat a (by linarith)
    have ht'_pos : 0 < t' := lt_of_le_of_ne ht'_ge (Ne.symm ht'_ne)
    have ht'_irr : Irrational t' := by
      rw [ht'_eq]
      exact hy_irr.sub_natCast a
    have hx_eq : x = 1 / ((a : ℝ) + t') := by
      have hay : (a : ℝ) + t' = y := by linarith [ht'_eq]
      rw [hay]
      dsimp only [y]
      rw [one_div, inv_inv]
    obtain ⟨w', t, ht_irr, ht0, ht1, ht'_mob⟩ :=
      exists_word_of_irrational n ht'_irr ht'_pos ht'_lt
    let aPos : ℕ+ := ⟨a, ha1⟩
    let w : Fin (n + 1) → ℕ+ := Fin.cons aPos w'
    have hw_eq : pnatWord w = a :: pnatWord w' := by
      unfold pnatWord
      rw [List.ofFn_succ]
      rfl
    refine ⟨w, t, ht_irr, ht0, ht1, ?_⟩
    rw [hw_eq, mobius_cfProd_zero_cons ha1 (posDigits_pnatWord w') ht0 ht1, ← ht'_mob, ← hx_eq]

/-- Every irrational `x ∈ (0, 1)` lies in the closed level-`n` CF cylinder of its first `n`
    partial quotients, with `(GenContFract.of x).dens n` equal to the word's denominator. -/
theorem exists_word_cover_of_irrational {x : ℝ} (hirr : Irrational x) (hx0 : 0 < x) (hx1 : x < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ w : Fin n → ℕ+,
      x ∈ Set.Icc (cylPair (pnatWord w)).1 (cylPair (pnatWord w)).2 ∧
      (GenContFract.of x).dens n = ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) := by
  obtain ⟨w, t, _, ht0, ht1, hmob⟩ := exists_word_of_irrational n hirr hx0 hx1
  have hne : pnatWord w ≠ [] := by
    intro h
    have hlen := pnatWord_length w
    rw [h] at hlen
    simp at hlen
    omega
  have hx_mem : x ∈ Set.Ioo (cylPair (pnatWord w)).1 (cylPair (pnatWord w)).2 := by
    rw [hmob]
    exact mobius_mem_Ioo_cylPair (posDigits_pnatWord w) hne ht0 ht1
  have hdens : (GenContFract.of x).dens n = ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) := by
    rw [hmob]
    have htop := (dens_mobius_top_and_penult (posDigits_pnatWord w) hne ht0 ht1).1
    rwa [pnatWord_length w] at htop
  exact ⟨w, Set.Ioo_subset_Icc_self hx_mem, hdens⟩

/-- Every irrational `x ∈ (0, 1)` satisfies `(n : ℝ) ≤ (GenContFract.of x).dens n`. -/
theorem nat_le_dens_of_irrational {x : ℝ} (hirr : Irrational x) (hx0 : 0 < x) (hx1 : x < 1)
    (n : ℕ) : (n : ℝ) ≤ (GenContFract.of x).dens n := by
  obtain ⟨w, t, _, ht0, ht1, hmob⟩ := exists_word_of_irrational n hirr hx0 hx1
  have hdens : (GenContFract.of x).dens n = ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) := by
    rw [hmob]
    have h := dens_mobius_eq (posDigits_pnatWord w) ht0 ht1 (k := n) (by rw [pnatWord_length])
    rwa [List.take_of_length_le (le_of_eq (pnatWord_length w))] at h
  rw [hdens]
  have hlen := cfProd_den_ge_length (posDigits_pnatWord w)
  rwa [pnatWord_length w] at hlen

/-- If `cfStopIdx x j < n` for irrational `x ∈ (0, 1)`, then `NoShortDim.H j < dens n`. -/
theorem H_lt_dens_of_cfStopIdx_lt {x : ℝ} (hirr : Irrational x) (hx0 : 0 < x) (hx1 : x < 1)
    {j n : ℕ} (hlt : cfStopIdx x j < n) :
    ((NoShortDim.H j : ℕ) : ℝ) < (GenContFract.of x).dens n := by
  by_contra hle
  push Not at hle
  have hbdd : BddAbove {k : ℕ | (GenContFract.of x).dens k ≤ ((NoShortDim.H j : ℕ) : ℝ)} := by
    refine ⟨NoShortDim.H j, fun k hk => ?_⟩
    have hkd : (k : ℝ) ≤ (GenContFract.of x).dens k := nat_le_dens_of_irrational hirr hx0 hx1 k
    have hleR : (k : ℝ) ≤ ((NoShortDim.H j : ℕ) : ℝ) := le_trans hkd hk
    exact_mod_cast hleR
  have hn_le : n ≤ cfStopIdx x j := le_csSup hbdd hle
  omega

/-- Super-exponential denominator growth on `boundedIncSet`:
    for any `x ∈ boundedIncSet` and any `M > 0`, eventually
    `exp (M * n) ≤ (GenContFract.of x).dens n`. -/
theorem boundedIncSet_dens_exp_growth {x : ℝ} (hx : x ∈ boundedIncSet) {M : ℝ} (hM : 0 < M) :
    ∃ N1 : ℕ, ∀ n ≥ N1, Real.exp (M * (n : ℝ)) ≤ (GenContFract.of x).dens n := by
  obtain ⟨hx01, hirr, B, J0, hB⟩ := hx
  have hx0 : 0 < x := hx01.1
  have hx1 : x < 1 := hx01.2
  have hdiff_le : ∀ d : ℕ, cfStopIdx x (J0 + d) ≤ cfStopIdx x J0 + B * d := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have hstep := hB (J0 + d) (by omega)
      have hadd : J0 + (d + 1) = J0 + d + 1 := by omega
      have hmul : B * (d + 1) = B * d + B := by ring
      rw [hadd, hmul]
      omega
  set C : ℕ := max 1 (cfStopIdx x J0 + B)
  have hC1 : 1 ≤ C := le_max_left _ _
  set N0 : ℕ := max 1 J0
  have hN01 : 1 ≤ N0 := le_max_left _ _
  have hlin : ∀ j ≥ N0, cfStopIdx x j ≤ C * j := by
    intro j hj
    have hj_ge_J0 : J0 ≤ j := le_trans (le_max_right _ _) hj
    have hj_ge_1 : 1 ≤ j := le_trans hN01 hj
    have hd := hdiff_le (j - J0)
    have hadd : J0 + (j - J0) = j := by omega
    rw [hadd] at hd
    have h1 : cfStopIdx x J0 ≤ cfStopIdx x J0 * j := Nat.le_mul_of_pos_right _ hj_ge_1
    have h2 : B * (j - J0) ≤ B * j := Nat.mul_le_mul_left B (Nat.sub_le j J0)
    have h3 : cfStopIdx x J0 + B ≤ C := le_max_right _ _
    have h4 : (cfStopIdx x J0 + B) * j ≤ C * j := Nat.mul_le_mul_right j h3
    calc cfStopIdx x j ≤ cfStopIdx x J0 + B * (j - J0) := hd
      _ ≤ cfStopIdx x J0 * j + B * j := Nat.add_le_add h1 h2
      _ = (cfStopIdx x J0 + B) * j := by ring
      _ ≤ C * j := h4
  set A : ℝ := Real.exp (8 * (C : ℝ) * M)
  have hA1 : 1 ≤ A := Real.one_le_exp (by positivity)
  set K : ℕ := Nat.ceil (A ^ 2) + 1
  have hA2_le : A ^ 2 ≤ ((K + 1 : ℕ) : ℝ) := by
    have hc : A ^ 2 ≤ (Nat.ceil (A ^ 2) : ℝ) := Nat.le_ceil _
    have hc1 : (Nat.ceil (A ^ 2) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (A ^ 2) ≤ K + 1)
    linarith
  set N1 : ℕ := max (2 * C * N0) (2 * C * (2 * K + 2))
  refine ⟨N1, fun n hn => ?_⟩
  set j : ℕ := n / (2 * C)
  have h2C_pos : 0 < 2 * C := by omega
  have hj_N0 : N0 ≤ j := (Nat.le_div_iff_mul_le h2C_pos).mpr
    (by rw [mul_comm]; exact le_trans (le_max_left _ _) hn)
  have hj_2K : 2 * K + 2 ≤ j := (Nat.le_div_iff_mul_le h2C_pos).mpr
    (by rw [mul_comm]; exact le_trans (le_max_right _ _) hn)
  have hj1 : 1 ≤ j := by omega
  have hj2 : 2 ≤ j := by omega
  have hstop_lt : cfStopIdx x j < n := by
    have hcj := hlin j hj_N0
    have h2cj : 2 * C * j ≤ n := Nat.mul_div_le n (2 * C)
    have hlt_mul : C * j < 2 * C * j := by nlinarith
    omega
  have hH_lt := H_lt_dens_of_cfStopIdx_lt hirr hx0 hx1 hstop_lt
  rw [← WindowPaperScale.Hpaper_eq hj1] at hH_lt
  have hH_fact := Hpaper_ge_fact hj1
  have hKm : K ≤ j - 1 := by omega
  have hpow_fact := nat_pow_le_factorial hKm
  have hmod : n = 2 * C * j + n % (2 * C) := (Nat.div_add_mod n (2 * C)).symm
  have hrem : n % (2 * C) < 2 * C := Nat.mod_lt n h2C_pos
  have hn_le_nat : n ≤ 8 * C * (j - 1) := by
    have hj_step : j + 1 ≤ 4 * (j - 1) := by omega
    calc n = 2 * C * j + n % (2 * C) := hmod
      _ ≤ 2 * C * j + 2 * C := by omega
      _ = 2 * C * (j + 1) := by ring
      _ ≤ 2 * C * (4 * (j - 1)) := Nat.mul_le_mul_left _ hj_step
      _ = 8 * C * (j - 1) := by ring
  have hn_leR : (n : ℝ) ≤ 8 * (C : ℝ) * ((j - 1 : ℕ) : ℝ) := by
    exact_mod_cast hn_le_nat
  have hexp_le : Real.exp (M * (n : ℝ)) ≤ A ^ (j - 1) := by
    have hMn_le : M * (n : ℝ) ≤ ((j - 1 : ℕ) : ℝ) * (8 * (C : ℝ) * M) := by
      have h1 := mul_le_mul_of_nonneg_left hn_leR (le_of_lt hM)
      linarith
    calc Real.exp (M * (n : ℝ)) ≤ Real.exp (((j - 1 : ℕ) : ℝ) * (8 * (C : ℝ) * M)) :=
          Real.exp_le_exp.mpr hMn_le
      _ = A ^ (j - 1) := by rw [Real.exp_nat_mul]
  have h2m_le : j - 1 ≤ 2 * (j - 1 - K) := by omega
  have hA_pow : A ^ (j - 1) ≤ ((K + 1 : ℕ) : ℝ) ^ (j - 1 - K) := by
    calc A ^ (j - 1) ≤ A ^ (2 * (j - 1 - K)) := pow_le_pow_right₀ hA1 h2m_le
      _ = (A ^ 2) ^ (j - 1 - K) := by rw [pow_mul]
      _ ≤ ((K + 1 : ℕ) : ℝ) ^ (j - 1 - K) := pow_le_pow_left₀ (by positivity) hA2_le _
  have h_final := le_trans hexp_le (le_trans hA_pow (le_trans hpow_fact hH_fact))
  exact le_of_lt (lt_of_le_of_lt h_final hH_lt)

/-! ### Part 3: Zeta sum, cylinder diameter bound, and `ENNReal` `tsum` bound -/

/-- Cylinder diameter bound in `ENNReal`:
    `ediam (Icc (cylPair l)) ≤ ofReal ((cfProd (0 :: l)) 1 0 ^ (-2))`. -/
theorem ediam_cylPair_le {l : List ℕ} (hl : PosDigits l) (hne : l ≠ []) :
    Metric.ediam (Set.Icc (cylPair l).1 (cylPair l).2) ≤
      ENNReal.ofReal (((cfProd (0 :: l)) 1 0 : ℝ) ^ (-(2 : ℝ))) := by
  have hu_posZ : 0 < (cfProd (0 :: l)) 1 0 := by
    have h0 := (cfProd_zero_cons_row1 l).1
    have hp := (cfProd_col0_pos hl hne).1
    linarith
  have hu_pos : (0 : ℝ) < ((cfProd (0 :: l)) 1 0 : ℝ) := by exact_mod_cast hu_posZ
  have hv_nn : (0 : ℝ) ≤ ((cfProd (0 :: l)) 1 1 : ℝ) := by
    exact_mod_cast cfProd_nonneg (0 :: l) 1 1
  have hlen := cylPair_len hl hne
  have hsub_le :
      (cylPair l).2 - (cylPair l).1 ≤ ((cfProd (0 :: l)) 1 0 : ℝ) ^ (-(2 : ℝ)) := by
    rw [hlen]
    have hpow :
        ((cfProd (0 :: l)) 1 0 : ℝ) ^ (-(2 : ℝ)) = 1 / ((cfProd (0 :: l)) 1 0 : ℝ) ^ 2 := by
      rw [Real.rpow_neg (le_of_lt hu_pos), Real.rpow_two, one_div]
    rw [hpow]
    have hden_le : ((cfProd (0 :: l)) 1 0 : ℝ) ^ 2 ≤
        ((cfProd (0 :: l)) 1 0 : ℝ) *
          (((cfProd (0 :: l)) 1 0 : ℝ) + ((cfProd (0 :: l)) 1 1 : ℝ)) := by
      nlinarith
    exact one_div_le_one_div_of_le (by positivity) hden_le
  rw [Real.ediam_Icc]
  exact ENNReal.ofReal_le_ofReal hsub_le

/-- `ζ(2t)` as an `ENNReal` `tsum` over `ℕ+`. -/
noncomputable def zetaTerm (t : ℝ) : ENNReal :=
  ∑' (a : ℕ+), ENNReal.ofReal (((a : ℕ) : ℝ) ^ (-(2 * t)))

theorem zetaTerm_ne_top {t : ℝ} (ht : 1 / 2 < t) : zetaTerm t ≠ ⊤ := by
  have h2t : 1 < 2 * t := by linarith
  have hsum_nat : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * t))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr h2t
  have hsum_nat' : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * t))) := by
    refine hsum_nat.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  have hsum_pnat : Summable (fun a : ℕ+ => ((a : ℕ) : ℝ) ^ (-(2 * t))) :=
    hsum_nat'.comp_injective PNat.coe_injective
  have htsum_ne : ∑' a : ℕ+, ENNReal.ofReal (((a : ℕ) : ℝ) ^ (-(2 * t))) ≠ ⊤ := by
    have hnn : ∀ a : ℕ+, 0 ≤ ((a : ℕ) : ℝ) ^ (-(2 * t)) := fun a => by positivity
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum_pnat]
    exact ENNReal.ofReal_ne_top
  exact htsum_ne

/-- Product `tsum` over `Fin n → ℕ+`:
    `∑' w : Fin n → ℕ+, ENNReal.ofReal (∏ i, (w i)^(-(2t))) = (zetaTerm t) ^ n`. -/
theorem tsum_prod_rpow_eq (t : ℝ) (n : ℕ) :
    (∑' w : Fin n → ℕ+, ENNReal.ofReal (∏ i : Fin n, ((w i : ℕ) : ℝ) ^ (-(2 * t)))) =
      (zetaTerm t) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, tsum_fintype, Fintype.sum_unique]
    simp
  | succ n ih =>
    let e : ℕ+ × (Fin n → ℕ+) ≃ (Fin (n + 1) → ℕ+) := Fin.consEquiv (fun _ => ℕ+)
    rw [← Equiv.tsum_eq e]
    have hsplit : (fun p : ℕ+ × (Fin n → ℕ+) =>
        ENNReal.ofReal (∏ i : Fin (n + 1), ((e p i : ℕ) : ℝ) ^ (-(2 * t)))) =
        fun p : ℕ+ × (Fin n → ℕ+) =>
          ENNReal.ofReal (((p.1 : ℕ) : ℝ) ^ (-(2 * t))) *
          ENNReal.ofReal (∏ i : Fin n, ((p.2 i : ℕ) : ℝ) ^ (-(2 * t))) := by
      ext ⟨a, w⟩
      have hprod : (∏ i : Fin (n + 1), ((e (a, w) i : ℕ) : ℝ) ^ (-(2 * t))) =
          ((a : ℕ) : ℝ) ^ (-(2 * t)) * ∏ i : Fin n, ((w i : ℕ) : ℝ) ^ (-(2 * t)) := by
        rw [Fin.prod_univ_succ]
        rfl
      rw [hprod, ENNReal.ofReal_mul (by positivity)]
    rw [hsplit, ENNReal.tsum_prod (f := fun (a : ℕ+) (w : Fin n → ℕ+) =>
      ENNReal.ofReal (((a : ℕ) : ℝ) ^ (-(2 * t))) *
      ENNReal.ofReal (∏ i : Fin n, ((w i : ℕ) : ℝ) ^ (-(2 * t))))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ih, ENNReal.tsum_mul_right, pow_succ']
    rfl

/-- `ENNReal` `tsum` bound for level-`n` cylinder `(-2t)`-weights:
    `∑' w : Fin n → ℕ+, ENNReal.ofReal ((d_n w)^(-(2t))) ≤ (zetaTerm t) ^ n`. -/
theorem tsum_cfProd_den_rpow_le {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (∑' w : Fin n → ℕ+, ENNReal.ofReal (((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 * t)))) ≤
      (zetaTerm t) ^ n := by
  rw [← tsum_prod_rpow_eq t n]
  refine ENNReal.tsum_le_tsum fun w => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hprod_pos : 0 < ∏ i : Fin n, ((w i : ℕ) : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast (w i).pos
  have hle := cfProd_den_ge_prod w
  have hrpow := Real.rpow_le_rpow_of_nonpos hprod_pos hle (by linarith : -(2 * t) ≤ 0)
  have hprod_eq : (∏ i : Fin n, ((w i : ℕ) : ℝ)) ^ (-(2 * t)) =
      ∏ i : Fin n, ((w i : ℕ) : ℝ) ^ (-(2 * t)) := by
    rw [← Real.finsetProd_rpow Finset.univ _ (fun i _ => by positivity)]
  linarith [hprod_eq]

/-! ### Part 4: Tail set `μH[s] = 0`, `dimH ≤ 1/2`, and exact `1/2` theorems -/

/-- Points `x ∈ (0, 1)` irrational with `(GenContFract.of x).dens n ≥ exp (M * n)` for `n ≥ N1`. -/
def tailSet (M : ℝ) (N1 : ℕ) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 |
    Irrational x ∧ ∀ n ≥ N1, Real.exp (M * (n : ℝ)) ≤ (GenContFract.of x).dens n}

/-- For `s > 1/2` and `t = (s + 1/2)/2`, if `M` satisfies
    `zetaTerm t * ofReal (exp (-2 M (s - t))) < 1`, then `μH[s] (tailSet M N1) = 0`. -/
theorem hausdorffMeasure_tailSet_zero {s t M : ℝ}
    (_hs : 1 / 2 < s) (ht_lo : 1 / 2 < t) (ht_hi : t < s) (hM : 0 < M)
    (hbase : zetaTerm t * ENNReal.ofReal (Real.exp (-(2 * M * (s - t)))) < 1)
    (N1 : ℕ) :
    μH[s] (tailSet M N1) = 0 := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  let base : ENNReal := zetaTerm t * ENNReal.ofReal (Real.exp (-(2 * M * (s - t))))
  have hbase_lt : base < 1 := hbase
  have htend_base : Filter.Tendsto (fun n : ℕ => base ^ n) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hbase_lt
  have htend_rad : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(2 * M * (n : ℝ)))))
      Filter.atTop (nhds 0) := by
    have hr : Filter.Tendsto (fun n : ℕ => -(2 * M * (n : ℝ))) Filter.atTop Filter.atBot := by
      rw [Filter.tendsto_atTop_atBot]
      intro b
      obtain ⟨N, hN⟩ := exists_nat_gt (-b / (2 * M))
      refine ⟨N, fun n hn => ?_⟩
      have hnR : -b / (2 * M) < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
      have h1 : -b < 2 * M * (n : ℝ) :=
        ((div_lt_iff₀ (by positivity : 0 < 2 * M)).mp hnR).trans_eq (mul_comm _ _)
      linarith
    have hexp := Real.tendsto_exp_atBot.comp hr
    simpa [Function.comp_def] using ENNReal.tendsto_ofReal hexp
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine le_antisymm ?_ bot_le
  refine iSup₂_le fun r hr => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [zero_add]
  have hε_pos : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := ENNReal.coe_pos.mpr hε
  have hr_ev : ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (Real.exp (-(2 * M * (n : ℝ)))) ≤ r :=
    htend_rad.eventually (ge_mem_nhds hr)
  have hε_ev : ∀ᶠ n : ℕ in Filter.atTop, base ^ n ≤ (ε : ℝ≥0∞) :=
    htend_base.eventually (ge_mem_nhds hε_pos)
  obtain ⟨N_r, hN_r⟩ := Filter.eventually_atTop.mp hr_ev
  obtain ⟨N_e, hN_e⟩ := Filter.eventually_atTop.mp hε_ev
  let n : ℕ := max (max N_r N_e) (max N1 1)
  have hn_rad : ENNReal.ofReal (Real.exp (-(2 * M * (n : ℝ)))) ≤ r :=
    hN_r n (le_trans (le_max_left _ _) (le_max_left _ _))
  have hn_eps : base ^ n ≤ (ε : ℝ≥0∞) :=
    hN_e n (le_trans (le_max_right _ _) (le_max_left _ _))
  have hn1 : 1 ≤ n := le_trans (le_max_right N1 1) (le_max_right _ _)
  have hnN1 : N1 ≤ n := le_trans (le_max_left N1 1) (le_max_right _ _)
  let enc : Encodable (Fin n → ℕ+) := Encodable.ofCountable (Fin n → ℕ+)
  let u : (Fin n → ℕ+) → Set ℝ := fun w =>
    if Real.exp (M * (n : ℝ)) ≤ ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) then
      Set.Icc (cylPair (pnatWord w)).1 (cylPair (pnatWord w)).2
    else ∅
  let cov : ℕ → Set ℝ := fun k =>
    match @Encodable.decode (Fin n → ℕ+) enc k with
    | some w => if @Encodable.encode (Fin n → ℕ+) enc w = k then u w else ∅
    | none => ∅
  have hcov_sub : tailSet M N1 ⊆ ⋃ k, cov k := by
    intro x hx
    obtain ⟨hx01, hirr, hgrowth⟩ := hx
    obtain ⟨w, hmem, hdens⟩ := exists_word_cover_of_irrational hirr hx01.1 hx01.2 hn1
    have hg := hgrowth n hnN1
    rw [hdens] at hg
    refine Set.mem_iUnion.mpr ⟨@Encodable.encode (Fin n → ℕ+) enc w, ?_⟩
    simp only [cov, @Encodable.encodek _ enc, ↓reduceIte, u, hg]
    exact hmem
  have hcov_diam : ∀ k : ℕ, Metric.ediam (cov k) ≤ r := by
    intro k
    dsimp only [cov]
    cases hdec : @Encodable.decode (Fin n → ℕ+) enc k with
    | none => simp
    | some w =>
      dsimp only
      split_ifs with henc
      · by_cases hden : Real.exp (M * (n : ℝ)) ≤ ((cfProd (0 :: pnatWord w)) 1 0 : ℝ)
        · simp only [u, hden, ↓reduceIte]
          have hne : pnatWord w ≠ [] := by
            intro h; have := pnatWord_length w; rw [h] at this; simp at this; omega
          have hd1 := ediam_cylPair_le (posDigits_pnatWord w) hne
          have hrpow : ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 : ℝ)) ≤
              Real.exp (-(2 * M * (n : ℝ))) := by
            have h1 : ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 : ℝ)) ≤
                (Real.exp (M * (n : ℝ))) ^ (-(2 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hden (by norm_num)
            have h2 : (Real.exp (M * (n : ℝ))) ^ (-(2 : ℝ)) = Real.exp (-(2 * M * (n : ℝ))) := by
              rw [← Real.exp_mul]; congr 1; ring
            exact h1.trans_eq h2
          exact le_trans hd1 (le_trans (ENNReal.ofReal_le_ofReal hrpow) hn_rad)
        · simp [u, hden]
      · simp
  refine iInf₂_le_of_le cov hcov_sub (iInf_le_of_le hcov_diam ?_)
  let f : ℕ → ENNReal := fun k => ⨆ (_ : (cov k).Nonempty), Metric.ediam (cov k) ^ s
  have hsupp : Function.support f ⊆ Set.range (@Encodable.encode (Fin n → ℕ+) enc) := by
    intro k hk
    rw [Function.mem_support] at hk
    by_contra hnot
    apply hk
    dsimp only [f, cov]
    cases hdec : @Encodable.decode (Fin n → ℕ+) enc k with
    | none => simp
    | some w =>
      have hne_enc : @Encodable.encode (Fin n → ℕ+) enc w ≠ k := fun h => hnot ⟨w, h⟩
      simp [hne_enc]
  have htsum_eq : (∑' k : ℕ, f k) =
      ∑' w : Fin n → ℕ+, f (@Encodable.encode (Fin n → ℕ+) enc w) :=
    (@Encodable.encode_injective (Fin n → ℕ+) enc).tsum_eq hsupp |>.symm
  change (∑' k : ℕ, f k) ≤ (ε : ℝ≥0∞)
  rw [htsum_eq]
  have hterm_le : ∀ w : Fin n → ℕ+,
      f (@Encodable.encode (Fin n → ℕ+) enc w) ≤
        ENNReal.ofReal (Real.exp (-(2 * M * (s - t) * (n : ℝ)))) *
        ENNReal.ofReal (((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 * t))) := by
    intro w
    dsimp only [f, cov]
    rw [@Encodable.encodek _ enc]
    simp only [↓reduceIte]
    by_cases hden : Real.exp (M * (n : ℝ)) ≤ ((cfProd (0 :: pnatWord w)) 1 0 : ℝ)
    · simp only [u, hden, ↓reduceIte]
      have hne : pnatWord w ≠ [] := by
        intro h; have := pnatWord_length w; rw [h] at this; simp at this; omega
      have hne_set : (Set.Icc (cylPair (pnatWord w)).1 (cylPair (pnatWord w)).2).Nonempty := by
        have hlen := cylPair_len (posDigits_pnatWord w) hne
        have hu_pos : (0 : ℝ) < ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) :=
          lt_of_lt_of_le (Real.exp_pos _) hden
        have hv_nn : (0 : ℝ) ≤ ((cfProd (0 :: pnatWord w)) 1 1 : ℝ) := by
          exact_mod_cast cfProd_nonneg (0 :: pnatWord w) 1 1
        have hpos_len : 0 < (cylPair (pnatWord w)).2 - (cylPair (pnatWord w)).1 := by
          rw [hlen]; positivity
        exact ⟨(cylPair (pnatWord w)).1, le_rfl, by linarith⟩
      rw [ciSup_pos hne_set]
      have hd1 : Metric.ediam (Set.Icc (cylPair (pnatWord w)).1 (cylPair (pnatWord w)).2) ^ s ≤
          ENNReal.ofReal (((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 : ℝ))) ^ s :=
        ENNReal.rpow_le_rpow (ediam_cylPair_le (posDigits_pnatWord w) hne) (le_of_lt hs0)
      have hu_pos : (0 : ℝ) < ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) :=
        lt_of_lt_of_le (Real.exp_pos _) hden
      have hd_eq : ENNReal.ofReal (((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 : ℝ))) ^ s =
          ENNReal.ofReal (((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 * s))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (le_of_lt hs0),
          ← Real.rpow_mul (le_of_lt hu_pos)]
        congr 2; ring
      refine le_trans hd1 ?_
      rw [hd_eq, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hsplit_exp : ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 * s)) =
          ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 * (s - t))) *
          ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 * t)) := by
        rw [← Real.rpow_add hu_pos]
        congr 1; ring
      have hst_neg : -(2 * (s - t)) ≤ 0 := by linarith
      have hdn_st : ((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 * (s - t))) ≤
          (Real.exp (M * (n : ℝ))) ^ (-(2 * (s - t))) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hden hst_neg
      have hexp_eq : (Real.exp (M * (n : ℝ))) ^ (-(2 * (s - t))) =
          Real.exp (-(2 * M * (s - t) * (n : ℝ))) := by
        rw [← Real.exp_mul]; congr 1; ring
      rw [hsplit_exp]
      exact mul_le_mul_of_nonneg_right (hdn_st.trans_eq hexp_eq) (by positivity)
    · simp [u, hden]
  have htsum_le1 :
      (∑' w : Fin n → ℕ+, f (@Encodable.encode (Fin n → ℕ+) enc w)) ≤
      ENNReal.ofReal (Real.exp (-(2 * M * (s - t) * (n : ℝ)))) *
      (∑' w : Fin n → ℕ+, ENNReal.ofReal (((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 * t)))) := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hterm_le
  have htsum_le2 :
      ENNReal.ofReal (Real.exp (-(2 * M * (s - t) * (n : ℝ)))) *
      (∑' w : Fin n → ℕ+, ENNReal.ofReal (((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 * t)))) ≤
      base ^ n := by
    have hpow_exp : ENNReal.ofReal (Real.exp (-(2 * M * (s - t) * (n : ℝ)))) =
        ENNReal.ofReal (Real.exp (-(2 * M * (s - t)))) ^ n := by
      have h1 : Real.exp (-(2 * M * (s - t) * (n : ℝ))) =
          (Real.exp (-(2 * M * (s - t)))) ^ n := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      rw [h1, ENNReal.ofReal_pow (le_of_lt (Real.exp_pos _))]
    calc ENNReal.ofReal (Real.exp (-(2 * M * (s - t) * (n : ℝ)))) *
          (∑' w : Fin n → ℕ+, ENNReal.ofReal (((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 * t))))
        = ENNReal.ofReal (Real.exp (-(2 * M * (s - t)))) ^ n *
          (∑' w : Fin n → ℕ+,
            ENNReal.ofReal (((cfProd (0 :: pnatWord w)) 1 0 : ℝ) ^ (-(2 * t)))) := by
          rw [hpow_exp]
      _ ≤ ENNReal.ofReal (Real.exp (-(2 * M * (s - t)))) ^ n * (zetaTerm t) ^ n :=
          mul_le_mul_of_nonneg_left (tsum_cfProd_den_rpow_le ht0 n) (by positivity)
      _ = base ^ n := by dsimp only [base]; rw [← mul_pow, mul_comm]
  exact le_trans htsum_le1 (le_trans htsum_le2 hn_eps)

/-- For every `s > 1 / 2`, `μH[s] boundedIncSet = 0`. -/
theorem hausdorffMeasure_boundedIncSet_zero {s : ℝ} (hs : 1 / 2 < s) :
    μH[s] boundedIncSet = 0 := by
  set t : ℝ := (s + 1 / 2) / 2
  have ht_lo : 1 / 2 < t := by dsimp only [t]; linarith
  have ht_hi : t < s := by dsimp only [t]; linarith
  have hz_ne : zetaTerm t ≠ ⊤ := zetaTerm_ne_top ht_lo
  set Z : ℝ := (zetaTerm t).toReal
  have hZ_nn : 0 ≤ Z := ENNReal.toReal_nonneg
  have hZ_coe : ENNReal.ofReal Z = zetaTerm t := ENNReal.ofReal_toReal hz_ne
  set M : ℝ := (Real.log (Z + 2)) / (2 * (s - t))
  have hZ2_gt : 1 < Z + 2 := by linarith
  have hlog_pos : 0 < Real.log (Z + 2) := Real.log_pos hZ2_gt
  have hM_pos : 0 < M := div_pos hlog_pos (by linarith)
  have hbase_lt : zetaTerm t * ENNReal.ofReal (Real.exp (-(2 * M * (s - t)))) < 1 := by
    have hexp_eq : Real.exp (-(2 * M * (s - t))) = (Z + 2)⁻¹ := by
      have harg : -(2 * M * (s - t)) = -Real.log (Z + 2) := by
        dsimp only [M]
        have hst : 2 * (s - t) ≠ 0 := by linarith
        field_simp [hst]
      rw [harg, Real.exp_neg, Real.exp_log (by linarith)]
    rw [← hZ_coe, hexp_eq, ← ENNReal.ofReal_mul hZ_nn]
    have hprod_lt : Z * (Z + 2)⁻¹ < 1 := by
      have hpos : 0 < Z + 2 := by linarith
      rw [← div_eq_mul_inv, div_lt_one hpos]
      linarith
    exact ENNReal.ofReal_lt_one.mpr hprod_lt
  have hsub : boundedIncSet ⊆ ⋃ N1 : ℕ, tailSet M N1 := by
    intro x hx
    obtain ⟨N1, hN1⟩ := boundedIncSet_dens_exp_growth hx hM_pos
    exact Set.mem_iUnion.mpr ⟨N1, hx.1, hx.2.1, hN1⟩
  have hnull : μH[s] (⋃ N1 : ℕ, tailSet M N1) = 0 :=
    MeasureTheory.measure_iUnion_null fun N1 =>
      hausdorffMeasure_tailSet_zero hs ht_lo ht_hi hM_pos hbase_lt N1
  exact le_antisymm ((MeasureTheory.measure_mono hsub).trans (le_of_eq hnull)) bot_le

/-- Hausdorff dimension upper bound for `boundedIncSet`:
    `dimH boundedIncSet ≤ ENNReal.ofReal (1 / 2)`. -/
theorem dimH_boundedIncSet_le_half :
    dimH boundedIncSet ≤ ENNReal.ofReal (1 / 2) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε_posR : 0 < (ε : ℝ) := NNReal.coe_pos.mpr hε
  set s : ℝ := 1 / 2 + (ε : ℝ)
  have hs_gt : 1 / 2 < s := by dsimp only [s]; linarith
  have hs_pos : 0 < s := by dsimp only [s]; linarith
  have hmu := hausdorffMeasure_boundedIncSet_zero hs_gt
  set d : ℝ≥0 := ⟨s, le_of_lt hs_pos⟩
  have hmu_d : μH[(d : ℝ)] boundedIncSet = 0 := hmu
  have hle_d : dimH boundedIncSet ≤ (d : ℝ≥0∞) := by
    rw [dimH_eq_iInf]
    exact iInf₂_le d hmu_d
  have hd_eq : (d : ℝ≥0∞) = ENNReal.ofReal (1 / 2) + (ε : ℝ≥0∞) := by
    have h1 : (d : ℝ≥0∞) = ENNReal.ofReal s := by
      simp only [d, ENNReal.ofReal]
      congr 1
      exact (Real.toNNReal_of_nonneg (le_of_lt hs_pos)).symm
    have h2 : ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞) := by simp
    rw [h1]
    dsimp only [s]
    rw [ENNReal.ofReal_add (by norm_num) (le_of_lt hε_posR), h2]
  rwa [hd_eq] at hle_d

/-! ### Part 5: Exact `1/2` Hausdorff dimension theorems (`thm:windows`) -/

/-- Exact Hausdorff dimension `dimH boundedIncSet = ENNReal.ofReal (1 / 2)`. -/
theorem dimH_boundedIncSet_eq_half :
    dimH boundedIncSet = ENNReal.ofReal (1 / 2) :=
  le_antisymm dimH_boundedIncSet_le_half dimH_ge_half_boundedIncSet

/-- Exact Hausdorff dimension `dimH (prescribedIncSet m) = ENNReal.ofReal (1 / 2)`
    for every bounded sequence `1 ≤ m j ≤ M`. -/
theorem dimH_prescribedIncSet_eq_half (m : ℕ → ℕ) (M : ℕ)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ M) :
    dimH (prescribedIncSet m) = ENNReal.ofReal (1 / 2) := by
  have hsub : prescribedIncSet m ⊆ boundedIncSet := by
    intro x ⟨hx01, hirr, J0, hJ0⟩
    exact ⟨hx01, hirr, M, J0, fun j hj => by rw [hJ0 j hj]; exact (hm j).2⟩
  exact le_antisymm
    (le_trans (dimH_mono hsub) dimH_boundedIncSet_le_half)
    (dimH_ge_half_prescribedIncSet m M hm)

/-- Exact Hausdorff dimension
    `dimH (prescribedIncSetAt m (j0Prescribed M) par0) = ENNReal.ofReal (1 / 2)`
    at the fixed starting index `j0Prescribed M` for either initial parity `par0 : Bool`. -/
theorem dimH_prescribedIncSetAt_eq_half (m : ℕ → ℕ) (M : ℕ) (par0 : Bool)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ M) :
    dimH (prescribedIncSetAt m (j0Prescribed M) par0) = ENNReal.ofReal (1 / 2) := by
  have hsub : prescribedIncSetAt m (j0Prescribed M) par0 ⊆ prescribedIncSet m :=
    fun _ ⟨hx01, hirr, _, hinc⟩ => ⟨hx01, hirr, j0Prescribed M, hinc⟩
  exact le_antisymm
    (le_trans (dimH_mono hsub) (le_of_eq (dimH_prescribedIncSet_eq_half m M hm)))
    (dimH_ge_half_prescribedIncSetAt m M par0 hm)

#print axioms WindowBoundedUpper.cfProd_den_ge_length_aux
#print axioms WindowBoundedUpper.cfProd_den_ge_length
#print axioms WindowBoundedUpper.list_prod_le_cfProd_den
#print axioms WindowBoundedUpper.cfProd_den_ge_prod
#print axioms WindowBoundedUpper.Hpaper_ge_fact
#print axioms WindowBoundedUpper.nat_pow_le_factorial
#print axioms WindowBoundedUpper.exists_word_of_irrational
#print axioms WindowBoundedUpper.exists_word_cover_of_irrational
#print axioms WindowBoundedUpper.nat_le_dens_of_irrational
#print axioms WindowBoundedUpper.H_lt_dens_of_cfStopIdx_lt
#print axioms WindowBoundedUpper.boundedIncSet_dens_exp_growth
#print axioms WindowBoundedUpper.ediam_cylPair_le
#print axioms WindowBoundedUpper.zetaTerm_ne_top
#print axioms WindowBoundedUpper.tsum_prod_rpow_eq
#print axioms WindowBoundedUpper.tsum_cfProd_den_rpow_le
#print axioms WindowBoundedUpper.hausdorffMeasure_tailSet_zero
#print axioms WindowBoundedUpper.hausdorffMeasure_boundedIncSet_zero
#print axioms WindowBoundedUpper.dimH_boundedIncSet_le_half
#print axioms WindowBoundedUpper.dimH_boundedIncSet_eq_half
#print axioms WindowBoundedUpper.dimH_prescribedIncSet_eq_half
#print axioms WindowBoundedUpper.dimH_prescribedIncSetAt_eq_half

end WindowBoundedUpper
