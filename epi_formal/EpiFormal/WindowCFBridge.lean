import EpiFormal.WindowCFRealize

/-!
# Pointwise Regular Continued-Fraction Bridge (`WindowCFBridge`)

Closes the pointwise identification between Cantor limit points of any concrete
stopped-cylinder CF word tree and mathlib's regular continued fraction `GenContFract.of x`:

1. **Strict cylinder nesting & open-cylinder Möbius inversion**:
   - `mobius_mem_Ioo_cylPair`: `t ∈ (0, 1) → mobius (cfProd (0 :: w)) t ∈ Ioo (cylPair w)`.
   - `cylPair_nest_strict`: extending `w` by `u` with `2 ≤ u.length ∨ ∃ a, u = [a] ∧ 2 ≤ a`
     nests `Icc (cylPair (w ++ u)) ⊆ Ioo (cylPair w)` strictly.
   - `exists_mobius_of_mem_Ioo_cylPair`: every `x ∈ Ioo (cylPair w)` equals
     `mobius (cfProd (0 :: w)) t` for some `t ∈ (0, 1)`.
2. **Exact identification with mathlib's `GenContFract.of x`**:
   - `mobius_cfProd_zero_cons`:
     `mobius (cfProd (0 :: a :: w)) t = 1 / (a + mobius (cfProd (0 :: w)) t)`.
   - `intFractPair_stream_mobius`: identifies `IntFractPair.stream x`, `(GenContFract.of x).h = 0`,
     `(GenContFract.of x).s.get? i = some ⟨1, w[i]⟩` for `i < w.length`, and non-termination up to
     `w.length`.
   - `contsAux_mobius_eq` / `dens_mobius_eq`: proves
     `(GenContFract.of x).dens k = (cfProd (0 :: w.take k)) 1 0`
     for all `k ≤ w.length`, matching `q_{w.length}(x)` and `q_{w.length - 1}(x)` literally.
   - `dens_of_mono`: monotonicity of `(GenContFract.of x).dens`.
3. **Regular CF stopping index `cfStopIdx` & generic word-tree Cantor bridge**:
   - `cfStopIdx x j := sSup {n | (GenContFract.of x).dens n ≤ (NoShortDim.H j : ℝ)}`.
   - `stopped_word_tree_cf_bridge`: for every `x` in the Cantor set of a stopped CF word tree,
     `x ∈ (0, 1)`, `Irrational x`, and there is a unique nested word sequence `w j` whose
     regular CF denominators match `cfProd (0 :: w j)` and whose stopping index satisfies
     `cfStopIdx x j = (w j).length - 1`.
4. **End-to-end `thm:windows` parity theorem**:
   - `mem_cantorSet_cfWindowsTree_cf`: every `x ∈ cantorSet (cfWindowsTree ε) (10^6)` is
     irrational in `(0, 1)` with `((cfStopIdx x j) % 2 == 1) = ε j` for all `j ≥ 10^6`.
   - `dimH_prescribedParitySet_eq_one`: unconditional `dimH (prescribedParitySet ε) = 1`
     using only Lean core axioms.
-/

namespace WindowCFBridge

open Matrix Set Filter Finset ENNReal Metric Real Cylinder WindowCFRealize
open scoped NNReal BigOperators Topology MeasureTheory

/-! ### Part 1: Strict cylinder nesting & open-cylinder Möbius inversion -/

/-- For any `t ∈ (0, 1)`, `mobius (cfProd (0 :: w)) t` lies in `Ioo (cylPair w)`. -/
theorem mobius_mem_Ioo_cylPair {w : List ℕ} (hw : PosDigits w) (hne : w ≠ [])
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mobius (cfProd (0 :: w)) t ∈ Set.Ioo (cylPair w).1 (cylPair w).2 := by
  set M := cfProd (0 :: w)
  have hu_pos : (0 : ℝ) < (M 1 0 : ℝ) := by
    have h0 := (cfProd_zero_cons_row1 w).1
    have hp := (cfProd_col0_pos hw hne).1
    exact_mod_cast (by linarith : (0 : ℤ) < M 1 0)
  have hv_nn : (0 : ℝ) ≤ (M 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg (0 :: w) 1 1
  have hd0 : (0 : ℝ) < (M 1 0 : ℝ) + (M 1 1 : ℝ) * 0 := by linarith
  have hdt : (0 : ℝ) < (M 1 0 : ℝ) + (M 1 1 : ℝ) * t := by nlinarith
  have hd1 : (0 : ℝ) < (M 1 0 : ℝ) + (M 1 1 : ℝ) * 1 := by linarith
  have hsub0 := mobius_sub M t 0 (ne_of_gt hdt) (ne_of_gt hd0)
  have hsub1 := mobius_sub M 1 t (ne_of_gt hd1) (ne_of_gt hdt)
  have hdet_pm : M.det = 1 ∨ M.det = -1 := by
    have hd : M.det = (-1 : ℤ) ^ (0 :: w).length := cfProd_det (0 :: w)
    rw [hd]; exact neg_one_pow_eq_or ℤ (0 :: w).length
  simp only [cylPair, Set.mem_Ioo]
  rcases hdet_pm with hdet | hdet
  · have h1 : mobius M t < mobius M 0 := by
      have : mobius M t - mobius M 0 < 0 := by
        rw [hsub0, hdet, Int.cast_one]
        exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)
      linarith
    have h2 : mobius M 1 < mobius M t := by
      have : mobius M 1 - mobius M t < 0 := by
        rw [hsub1, hdet, Int.cast_one]
        exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)
      linarith
    exact ⟨lt_of_le_of_lt (min_le_right _ _) h2, lt_of_lt_of_le h1 (le_max_left _ _)⟩
  · have h1 : mobius M 0 < mobius M t := by
      have : 0 < mobius M t - mobius M 0 := by
        rw [hsub0, hdet, Int.cast_neg, Int.cast_one]
        exact div_pos (by nlinarith) (by positivity)
      linarith
    have h2 : mobius M t < mobius M 1 := by
      have : 0 < mobius M 1 - mobius M t := by
        rw [hsub1, hdet, Int.cast_neg, Int.cast_one]
        exact div_pos (by nlinarith) (by positivity)
      linarith
    exact ⟨lt_of_le_of_lt (min_le_left _ _) h1, lt_of_lt_of_le h2 (le_max_right _ _)⟩

/-- Every open cylinder of a nonempty positive-digit word lies inside `(0, 1)`. -/
theorem Ioo_cylPair_subset_Ioo_unit {w : List ℕ} (hw : PosDigits w) (hne : w ≠ []) :
    Set.Ioo (cylPair w).1 (cylPair w).2 ⊆ Set.Ioo (0 : ℝ) 1 := by
  set M := cfProd (0 :: w)
  have hu_pos : (0 : ℝ) < (M 1 0 : ℝ) := by
    have h0 := (cfProd_zero_cons_row1 w).1
    have hp := (cfProd_col0_pos hw hne).1
    exact_mod_cast (by linarith : (0 : ℤ) < M 1 0)
  have hv_nn : (0 : ℝ) ≤ (M 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg (0 :: w) 1 1
  have h00_nn : (0 : ℝ) ≤ (M 0 0 : ℝ) := by exact_mod_cast cfProd_nonneg (0 :: w) 0 0
  have h01_nn : (0 : ℝ) ≤ (M 0 1 : ℝ) := by exact_mod_cast cfProd_nonneg (0 :: w) 0 1
  obtain ⟨hr0, hr1⟩ := cfProd_row1_le_row0 hw hne
  have h00_le : (M 0 0 : ℝ) ≤ (M 1 0 : ℝ) := by
    have ha := (cfProd_zero_cons_row0 w).1
    have hb := (cfProd_zero_cons_row1 w).1
    exact_mod_cast (by linarith : M 0 0 ≤ M 1 0)
  have h01_le : (M 0 1 : ℝ) ≤ (M 1 1 : ℝ) := by
    have ha := (cfProd_zero_cons_row0 w).2
    have hb := (cfProd_zero_cons_row1 w).2
    exact_mod_cast (by linarith : M 0 1 ≤ M 1 1)
  have hm0_lo : 0 ≤ mobius M 0 := by
    unfold mobius; simp only [mul_zero, add_zero]
    exact div_nonneg h00_nn (le_of_lt hu_pos)
  have hm0_hi : mobius M 0 ≤ 1 := by
    unfold mobius; simp only [mul_zero, add_zero]
    exact (div_le_one hu_pos).mpr h00_le
  have hm1_lo : 0 ≤ mobius M 1 := by
    unfold mobius; simp only [mul_one]
    exact div_nonneg (by linarith) (by linarith)
  have hm1_hi : mobius M 1 ≤ 1 := by
    unfold mobius; simp only [mul_one]
    exact (div_le_one (by linarith)).mpr (by linarith)
  intro x hx
  simp only [cylPair, Set.mem_Ioo] at hx ⊢
  exact ⟨lt_of_le_of_lt (le_min hm0_lo hm1_lo) hx.1, lt_of_lt_of_le hx.2 (max_le hm0_hi hm1_hi)⟩

/-- Strict cylinder nesting: appending a positive-digit suffix `u` of length `≥ 2`
    or a single digit `a ≥ 2` maps the closed child cylinder strictly inside the open parent. -/
theorem cylPair_nest_strict {w u : List ℕ} (hw : PosDigits w) (hwne : w ≠ [])
    (hu : PosDigits u) (hstrict : 2 ≤ u.length ∨ ∃ a, u = [a] ∧ 2 ≤ a) :
    Set.Icc (cylPair (w ++ u)).1 (cylPair (w ++ u)).2 ⊆
      Set.Ioo (cylPair w).1 (cylPair w).2 := by
  set M := cfProd (0 :: w)
  set N := cfProd u
  have hMN : cfProd (0 :: (w ++ u)) = M * N := by
    have hcons : (0 :: (w ++ u)) = (0 :: w) ++ u := rfl
    rw [hcons, cfProd_append]
  have hN_props : 0 < N 1 0 ∧ N 1 0 < N 0 0 ∧ N 1 1 ≤ N 0 1 := by
    rcases hstrict with hlen | ⟨a, rfl, ha2⟩
    · rcases u with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · simp at hlen
      · simp at hlen
      · obtain ⟨ha, hbr⟩ := posDigits_cons.mp hu
        obtain ⟨hb0, hb1⟩ := cfProd_col0_pos hbr (List.cons_ne_nil b rest)
        have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
        have hN00 : (cfProd (a :: b :: rest)) 0 0 =
            (a : ℤ) * (cfProd (b :: rest)) 0 0 + (cfProd (b :: rest)) 1 0 := by
          rw [cfProd, Matrix.mul_apply, Fin.sum_univ_two]
          simp [cfMat]
        have hN10 : (cfProd (a :: b :: rest)) 1 0 = (cfProd (b :: rest)) 0 0 := by
          rw [cfProd, Matrix.mul_apply, Fin.sum_univ_two]
          simp [cfMat]
        have hr := (cfProd_row1_le_row0 hu (List.cons_ne_nil a (b :: rest))).2
        dsimp only [N]
        exact ⟨by linarith, by nlinarith, hr⟩
    · have hN00 : (cfProd [a]) 0 0 = (a : ℤ) := by simp [cfProd, cfMat]
      have hN10 : (cfProd [a]) 1 0 = 1 := by simp [cfProd, cfMat]
      have hN01 : (cfProd [a]) 0 1 = 1 := by simp [cfProd, cfMat]
      have hN11 : (cfProd [a]) 1 1 = 0 := by simp [cfProd, cfMat]
      have haZ : (2 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha2
      dsimp only [N]
      exact ⟨by linarith, by linarith, by linarith⟩
  have hN10_pos : (0 : ℝ) < (N 1 0 : ℝ) := by exact_mod_cast hN_props.1
  have hN_lt : (N 1 0 : ℝ) < (N 0 0 : ℝ) := by exact_mod_cast hN_props.2.1
  have hN11_le : (N 1 1 : ℝ) ≤ (N 0 1 : ℝ) := by exact_mod_cast hN_props.2.2
  have hN01_nn : (0 : ℝ) ≤ (N 0 1 : ℝ) := by exact_mod_cast cfProd_nonneg u 0 1
  have hN11_nn : (0 : ℝ) ≤ (N 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg u 1 1
  have hend : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      mobius (M * N) s ∈ Set.Ioo (cylPair w).1 (cylPair w).2 := by
    intro s hs0 _
    have hden : (0 : ℝ) < (N 0 0 : ℝ) + (N 0 1 : ℝ) * s := by nlinarith
    rw [mobius_mul M N s (ne_of_gt hden)]
    refine mobius_mem_Ioo_cylPair hw hwne ?_ ?_
    · exact div_pos (by nlinarith) hden
    · exact (div_lt_one hden).mpr (by nlinarith)
  have he0 := hend 0 le_rfl zero_le_one
  have he1 := hend 1 zero_le_one le_rfl
  intro x hx
  simp only [cylPair, hMN, Set.mem_Icc, Set.mem_Ioo] at hx ⊢
  simp only [Set.mem_Ioo] at he0 he1
  exact ⟨lt_of_lt_of_le (lt_min he0.1 he1.1) hx.1, lt_of_le_of_lt hx.2 (max_lt he0.2 he1.2)⟩

/-- Algebraic inversion of `mobius` on an open cylinder: every `x ∈ Ioo (cylPair w)`
    equals `mobius (cfProd (0 :: w)) t` for some `t ∈ (0, 1)`. -/
theorem exists_mobius_of_mem_Ioo_cylPair {w : List ℕ} (hw : PosDigits w) (hne : w ≠ [])
    {x : ℝ} (hx : x ∈ Set.Ioo (cylPair w).1 (cylPair w).2) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, mobius (cfProd (0 :: w)) t = x := by
  set M := cfProd (0 :: w)
  have hu_pos : (0 : ℝ) < (M 1 0 : ℝ) := by
    have h0 := (cfProd_zero_cons_row1 w).1
    have hp := (cfProd_col0_pos hw hne).1
    exact_mod_cast (by linarith : (0 : ℤ) < M 1 0)
  have hv_nn : (0 : ℝ) ≤ (M 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg (0 :: w) 1 1
  have hden0 : (0 : ℝ) < (M 1 0 : ℝ) := hu_pos
  have hden1 : (0 : ℝ) < (M 1 0 : ℝ) + (M 1 1 : ℝ) := by linarith
  have hdet_ne : (M.det : ℝ) ≠ 0 := by exact_mod_cast cfProd_det_ne_zero (0 :: w)
  set A : ℝ := x * (M 1 0 : ℝ) - (M 0 0 : ℝ)
  set B : ℝ := ((M 0 0 : ℝ) + (M 0 1 : ℝ)) - x * ((M 1 0 : ℝ) + (M 1 1 : ℝ))
  have hmob0 : mobius M 0 = (M 0 0 : ℝ) / (M 1 0 : ℝ) := by simp [mobius]
  have hmob1 : mobius M 1 = ((M 0 0 : ℝ) + (M 0 1 : ℝ)) / ((M 1 0 : ℝ) + (M 1 1 : ℝ)) := by
    simp [mobius]
  simp only [cylPair, Set.mem_Ioo] at hx
  have hAB : (0 < A ∧ 0 < B) ∨ (A < 0 ∧ B < 0) := by
    rcases le_total (mobius M 0) (mobius M 1) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hx
      left
      have hA : (M 0 0 : ℝ) < x * (M 1 0 : ℝ) := by
        have := hx.1; rw [hmob0, div_lt_iff₀ hden0] at this; exact this
      have hB : x * ((M 1 0 : ℝ) + (M 1 1 : ℝ)) < (M 0 0 : ℝ) + (M 0 1 : ℝ) := by
        have := hx.2; rw [hmob1, lt_div_iff₀ hden1] at this; exact this
      exact ⟨by linarith, by linarith⟩
    · rw [min_eq_right hle, max_eq_left hle] at hx
      right
      have hA : x * (M 1 0 : ℝ) < (M 0 0 : ℝ) := by
        have := hx.2; rw [hmob0, lt_div_iff₀ hden0] at this; exact this
      have hB : (M 0 0 : ℝ) + (M 0 1 : ℝ) < x * ((M 1 0 : ℝ) + (M 1 1 : ℝ)) := by
        have := hx.1; rw [hmob1, div_lt_iff₀ hden1] at this; exact this
      exact ⟨by linarith, by linarith⟩
  set t : ℝ := A / (A + B)
  have ht_mem : t ∈ Set.Ioo (0 : ℝ) 1 := by
    rcases hAB with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact ⟨div_pos hA (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩
    · have hABneg : A + B < 0 := by linarith
      exact ⟨div_pos_of_neg_of_neg hA hABneg,
        (div_lt_one_of_neg hABneg).mpr (by linarith)⟩
  have hAB_ne : A + B ≠ 0 := by
    rcases hAB with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> linarith
  have hden_t : (0 : ℝ) < (M 1 0 : ℝ) + (M 1 1 : ℝ) * t := by
    nlinarith [ht_mem.1]
  refine ⟨t, ht_mem, ?_⟩
  unfold mobius
  rw [div_eq_iff (ne_of_gt hden_t)]
  have hdet_eq : (M.det : ℝ) = (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) := by
    rw [Matrix.det_fin_two]; push_cast; ring
  dsimp only [t]
  field_simp [hAB_ne]
  dsimp only [A, B]
  ring

/-! ### Part 2: Exact identification with mathlib's `GenContFract.of` -/

/-- For any positive-digit word `w` (including `[]`) and `t ∈ (0, 1)`,
    `mobius (cfProd (0 :: w)) t ∈ (0, 1)`. -/
theorem mobius_cfProd_zero_mem_Ioo {w : List ℕ} (hw : PosDigits w)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mobius (cfProd (0 :: w)) t ∈ Set.Ioo (0 : ℝ) 1 := by
  cases w with
  | nil =>
    have hmob : mobius (cfProd [0]) t = t := by
      simp [mobius, cfProd, cfMat]
    rw [hmob]
    exact ⟨ht0, ht1⟩
  | cons a rest =>
    exact Ioo_cylPair_subset_Ioo_unit hw (List.cons_ne_nil a rest)
      (mobius_mem_Ioo_cylPair hw (List.cons_ne_nil a rest) ht0 ht1)

/-- Gauss-map step: `mobius (cfProd (0 :: a :: w)) t = 1 / (a + mobius (cfProd (0 :: w)) t)`. -/
theorem mobius_cfProd_zero_cons {a : ℕ} (ha : 1 ≤ a) {w : List ℕ} (hw : PosDigits w)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mobius (cfProd (0 :: a :: w)) t = 1 / ((a : ℝ) + mobius (cfProd (0 :: w)) t) := by
  set N := cfProd w
  have hN00_pos : (0 : ℝ) < (N 0 0 : ℝ) := by
    cases w with
    | nil => simp [N, cfProd]
    | cons b rest => exact_mod_cast (cfProd_col0_pos hw (List.cons_ne_nil b rest)).1
  have hN01_nn : (0 : ℝ) ≤ (N 0 1 : ℝ) := by exact_mod_cast cfProd_nonneg w 0 1
  have hdenN : (0 : ℝ) < (N 0 0 : ℝ) + (N 0 1 : ℝ) * t := by nlinarith
  have hy_pos : 0 < mobius (cfProd (0 :: w)) t := (mobius_cfProd_zero_mem_Ioo hw ht0 ht1).1
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hden_rhs : (0 : ℝ) < (a : ℝ) + mobius (cfProd (0 :: w)) t := by linarith
  have h0w_r0 := cfProd_zero_cons_row0 w
  have h0w_r1 := cfProd_zero_cons_row1 w
  have h0aw_00 : (cfProd (0 :: a :: w)) 0 0 = N 0 0 := by
    rw [cfProd, cfProd, Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfMat, Matrix.mul_apply, Fin.sum_univ_two, N]
  have h0aw_01 : (cfProd (0 :: a :: w)) 0 1 = N 0 1 := by
    rw [cfProd, cfProd, Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfMat, Matrix.mul_apply, Fin.sum_univ_two, N]
  have h0aw_10 : (cfProd (0 :: a :: w)) 1 0 = (a : ℤ) * N 0 0 + N 1 0 := by
    rw [cfProd, cfProd, Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfMat, Matrix.mul_apply, Fin.sum_univ_two, N]
  have h0aw_11 : (cfProd (0 :: a :: w)) 1 1 = (a : ℤ) * N 0 1 + N 1 1 := by
    rw [cfProd, cfProd, Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfMat, Matrix.mul_apply, Fin.sum_univ_two, N]
  unfold mobius
  rw [h0aw_00, h0aw_01, h0aw_10, h0aw_11, h0w_r0.1, h0w_r0.2, h0w_r1.1, h0w_r1.2]
  dsimp only [N]
  push_cast
  have hden_lhs : (0 : ℝ) <
      ((a : ℝ) * ((cfProd w) 0 0 : ℝ) + ((cfProd w) 1 0 : ℝ)) +
      ((a : ℝ) * ((cfProd w) 0 1 : ℝ) + ((cfProd w) 1 1 : ℝ)) * t := by
    have h10_nn : (0 : ℝ) ≤ ((cfProd w) 1 0 : ℝ) := by exact_mod_cast cfProd_nonneg w 1 0
    have h11_nn : (0 : ℝ) ≤ ((cfProd w) 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg w 1 1
    nlinarith
  have hdenN' : (0 : ℝ) < ((cfProd w) 0 0 : ℝ) + ((cfProd w) 0 1 : ℝ) * t := hdenN
  have hden_mid : (0 : ℝ) < (a : ℝ) +
      (((cfProd w) 1 0 : ℝ) + ((cfProd w) 1 1 : ℝ) * t) /
        (((cfProd w) 0 0 : ℝ) + ((cfProd w) 0 1 : ℝ) * t) := by
    have h10_nn : (0 : ℝ) ≤ ((cfProd w) 1 0 : ℝ) := by exact_mod_cast cfProd_nonneg w 1 0
    have h11_nn : (0 : ℝ) ≤ ((cfProd w) 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg w 1 1
    have hq_nn : 0 ≤ (((cfProd w) 1 0 : ℝ) + ((cfProd w) 1 1 : ℝ) * t) /
        (((cfProd w) 0 0 : ℝ) + ((cfProd w) 0 1 : ℝ) * t) :=
      div_nonneg (by nlinarith) (le_of_lt hdenN')
    linarith
  rw [div_eq_div_iff (ne_of_gt hden_lhs) (ne_of_gt hden_mid)]
  field_simp [ne_of_gt hdenN']
  ring

/-- One-step shift for `IntFractPair.stream` under `x = 1 / (a + y)` with `a ≥ 1, y ∈ (0, 1)`. -/
theorem intFractPair_stream_one_div_add {a : ℕ} (ha : 1 ≤ a) {y : ℝ}
    (hy0 : 0 < y) (hy1 : y < 1) :
    let x : ℝ := 1 / ((a : ℝ) + y)
    0 < x ∧ x < 1 ∧
    GenContFract.IntFractPair.stream x 0 = some ⟨0, x⟩ ∧
    GenContFract.IntFractPair.stream x 1 = some ⟨(a : ℤ), y⟩ ∧
    ∀ k : ℕ, GenContFract.IntFractPair.stream x (k + 2) =
      GenContFract.IntFractPair.stream y (k + 1) := by
  intro x
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hden : (1 : ℝ) < (a : ℝ) + y := by linarith
  have hx0 : 0 < x := div_pos zero_lt_one (by linarith)
  have hx1 : x < 1 := (div_lt_one (by linarith)).mpr hden
  have hfl_x : ⌊x⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simp [le_of_lt hx0], by simp [hx1]⟩
  have hfr_x : Int.fract x = x := by simp [Int.fract, hfl_x]
  have hinv_x : (Int.fract x)⁻¹ = (a : ℝ) + y := by
    rw [hfr_x]; simp [x]
  have hfl_ay : ⌊(a : ℝ) + y⌋ = (a : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨by push_cast; linarith, by push_cast; linarith⟩
  have hfr_ay : Int.fract ((a : ℝ) + y) = y := by
    simp [Int.fract, hfl_ay]
  have hfl_y : ⌊y⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simp [le_of_lt hy0], by simp [hy1]⟩
  have hfr_y : Int.fract y = y := by simp [Int.fract, hfl_y]
  have hs0 : GenContFract.IntFractPair.stream x 0 = some ⟨0, x⟩ := by
    simp [GenContFract.IntFractPair.stream_zero, GenContFract.IntFractPair.of, hfl_x, hfr_x]
  have hs1 : GenContFract.IntFractPair.stream x 1 = some ⟨(a : ℤ), y⟩ := by
    rw [GenContFract.IntFractPair.stream_succ (by rw [hfr_x]; exact ne_of_gt hx0) 0, hinv_x]
    simp [GenContFract.IntFractPair.stream_zero, GenContFract.IntFractPair.of, hfl_ay, hfr_ay]
  refine ⟨hx0, hx1, hs0, hs1, ?_⟩
  intro k
  rw [GenContFract.IntFractPair.stream_succ (by rw [hfr_x]; exact ne_of_gt hx0) (k + 1), hinv_x]
  rw [GenContFract.IntFractPair.stream_succ (by rw [hfr_ay]; exact ne_of_gt hy0) k, hfr_ay]
  rw [GenContFract.IntFractPair.stream_succ (by rw [hfr_y]; exact ne_of_gt hy0) k, hfr_y]

/-- Exact stream and partial-quotient identification for `x = mobius (cfProd (0 :: w)) t`. -/
theorem stream_mobius_spec (w : List ℕ) (hw : PosDigits w) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    let x := mobius (cfProd (0 :: w)) t
    (GenContFract.of x).h = 0 ∧
    (∀ (i : ℕ) (hi : i < w.length), (GenContFract.of x).s.get? i = some ⟨1, (w[i] : ℝ)⟩) ∧
    (∃ b : ℤ, GenContFract.IntFractPair.stream x w.length = some ⟨b, t⟩) := by
  dsimp only
  induction w with
  | nil =>
    have hmob : mobius (cfProd [0]) t = t := by simp [mobius, cfProd, cfMat]
    have hfl : ⌊t⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simp [le_of_lt ht0], by simp [ht1]⟩
    have hfr : Int.fract t = t := by simp [Int.fract, hfl]
    refine ⟨?_, (fun i hi => nomatch hi), ⟨0, ?_⟩⟩
    · simp [hmob, GenContFract.of_h_eq_floor, hfl]
    · simp [hmob, GenContFract.IntFractPair.stream_zero, GenContFract.IntFractPair.of, hfl, hfr]
  | cons a rest ih =>
    obtain ⟨ha, hrest⟩ := posDigits_cons.mp hw
    obtain ⟨ih_h, ih_s, b, ih_str⟩ := ih hrest
    set y := mobius (cfProd (0 :: rest)) t
    have hy := mobius_cfProd_zero_mem_Ioo hrest ht0 ht1
    have hstep := mobius_cfProd_zero_cons ha hrest ht0 ht1
    obtain ⟨hx0, hx1, _, hs1, hs_shift⟩ := intFractPair_stream_one_div_add ha hy.1 hy.2
    have hfl_x : ⌊mobius (cfProd (0 :: a :: rest)) t⌋ = 0 := by
      rw [hstep, Int.floor_eq_iff]
      exact ⟨by rw [Int.cast_zero]; exact le_of_lt hx0,
        by rw [Int.cast_zero, zero_add]; exact hx1⟩
    refine ⟨by rw [GenContFract.of_h_eq_floor, hfl_x, Int.cast_zero], ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        rw [hstep]
        simpa using GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hs1
      | succ k =>
        have hk : k < rest.length := by simpa using hi
        have hy_k := ih_s k hk
        obtain ⟨ifp, hstr_y, hb_eq⟩ :=
          GenContFract.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some hy_k
        have hstr_x : GenContFract.IntFractPair.stream (1 / ((a : ℝ) + y)) (k + 2) = some ifp := by
          rw [hs_shift k, hstr_y]
        have hget := GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hstr_x
        rw [hstep, hget]
        simp only [Option.some.injEq, GenContFract.Pair.mk.injEq, true_and]
        have hget_elem : (a :: rest)[k + 1] = rest[k] := rfl
        rw [hget_elem]
        simpa using hb_eq
    · cases rest with
      | nil =>
        have hy_eq : mobius (cfProd [0]) t = t := by simp [mobius, cfProd, cfMat]
        refine ⟨(a : ℤ), ?_⟩
        rw [hstep]
        simpa only [List.length_singleton, hy_eq] using hs1
      | cons c tail =>
        refine ⟨b, ?_⟩
        have hlen : (a :: c :: tail).length = tail.length + 2 := rfl
        have hlen' : (c :: tail).length = tail.length + 1 := rfl
        rw [hstep, hlen, hs_shift tail.length, ← hlen']
        exact ih_str

/-- Non-termination of `GenContFract.of (mobius (cfProd (0 :: w)) t)` up to index `w.length`. -/
theorem not_terminatedAt_mobius {w : List ℕ} (hw : PosDigits w)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {k : ℕ} (hk : k ≤ w.length) :
    ¬ (GenContFract.of (mobius (cfProd (0 :: w)) t)).TerminatedAt k := by
  obtain ⟨_, _, b, hstr⟩ := stream_mobius_spec w hw ht0 ht1
  have hsucc : GenContFract.IntFractPair.stream (mobius (cfProd (0 :: w)) t) (w.length + 1) =
      some (GenContFract.IntFractPair.of t⁻¹) :=
    GenContFract.IntFractPair.stream_succ_of_some hstr (ne_of_gt ht0)
  have hnot_top : ¬ (GenContFract.of (mobius (cfProd (0 :: w)) t)).TerminatedAt w.length := by
    rw [GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, hsucc]
    simp
  intro hterm
  exact hnot_top (GenContFract.terminated_stable hk hterm)

/-- Identification of `contsAux` along prefixes `k ≤ w.length` with `cfProd (0 :: w.take k)`. -/
theorem contsAux_mobius_eq {w : List ℕ} (hw : PosDigits w)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ k ≤ w.length,
      (GenContFract.of (mobius (cfProd (0 :: w)) t)).contsAux k =
        ⟨((cfProd (0 :: w.take k)) 0 1 : ℝ), ((cfProd (0 :: w.take k)) 1 1 : ℝ)⟩ ∧
      (GenContFract.of (mobius (cfProd (0 :: w)) t)).contsAux (k + 1) =
        ⟨((cfProd (0 :: w.take k)) 0 0 : ℝ), ((cfProd (0 :: w.take k)) 1 0 : ℝ)⟩ := by
  obtain ⟨hh, hs, _⟩ := stream_mobius_spec w hw ht0 ht1
  set x := mobius (cfProd (0 :: w)) t
  intro k hk
  induction k with
  | zero =>
    constructor
    · simp only [GenContFract.contsAux, List.take_zero, cfProd, cfMat, Matrix.mul_one,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Int.cast_one, Int.cast_zero]
    · simp only [GenContFract.contsAux, hh, List.take_zero, cfProd, cfMat, Matrix.mul_one,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Nat.cast_zero, Int.cast_one, Int.cast_zero]
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih (by omega)
    have htake : w.take (k + 1) = w.take k ++ [w[k]] := List.take_succ_eq_append_getElem hk
    have hprod : cfProd (0 :: w.take (k + 1)) = cfProd (0 :: w.take k) * cfMat w[k] := by
      have hcons : (0 :: (w.take k ++ [w[k]])) = (0 :: w.take k) ++ [w[k]] := rfl
      rw [htake, hcons, cfProd_append]
      simp [cfProd]
    have hget : (GenContFract.of x).s.get? k = some ⟨1, (w[k] : ℝ)⟩ := hs k hk
    have hrec := GenContFract.contsAux_recurrence hget ih0 ih1
    constructor
    · rw [ih1, hprod]
      congr 1 <;> simp [Matrix.mul_apply, Fin.sum_univ_two, cfMat]
    · rw [hrec, hprod]
      congr 1 <;> (simp [Matrix.mul_apply, Fin.sum_univ_two, cfMat]; ring)

/-- Exact identification of mathlib's regular CF convergent denominators `dens k` with `cfProd`. -/
theorem dens_mobius_eq {w : List ℕ} (hw : PosDigits w)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {k : ℕ} (hk : k ≤ w.length) :
    (GenContFract.of (mobius (cfProd (0 :: w)) t)).dens k =
      ((cfProd (0 :: w.take k)) 1 0 : ℝ) := by
  have h := (contsAux_mobius_eq hw ht0 ht1 k hk).2
  rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, h]

/-- At the full word length `w.length`, `dens w.length` equals `(cfProd (0 :: w)) 1 0`
    and (for `w ≠ []`) `dens (w.length - 1)` equals `(cfProd (0 :: w)) 1 1`. -/
theorem dens_mobius_top_and_penult {w : List ℕ} (hw : PosDigits w) (hne : w ≠ [])
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (GenContFract.of (mobius (cfProd (0 :: w)) t)).dens w.length = ((cfProd (0 :: w)) 1 0 : ℝ) ∧
    (GenContFract.of (mobius (cfProd (0 :: w)) t)).dens (w.length - 1) =
      ((cfProd (0 :: w)) 1 1 : ℝ) := by
  have h := contsAux_mobius_eq hw ht0 ht1 w.length le_rfl
  rw [List.take_length] at h
  have hlen1 : 1 ≤ w.length := List.length_pos_of_ne_nil hne
  constructor
  · rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, h.2]
  · rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
    have hsub : w.length - 1 + 1 = w.length := by omega
    rw [hsub, h.1]

/-- Monotonicity of regular CF convergent denominators `(GenContFract.of x).dens` for `x : ℝ`. -/
theorem dens_of_mono (x : ℝ) : Monotone (GenContFract.of x).dens := by
  have hstep : ∀ n : ℕ, 0 ≤ ((GenContFract.of x).contsAux n).b ∧
      ((GenContFract.of x).contsAux n).b ≤ ((GenContFract.of x).contsAux (n + 1)).b := by
    intro n
    induction n with
    | zero => simp [GenContFract.contsAux]
    | succ n ih =>
      refine ⟨le_trans ih.1 ih.2, ?_⟩
      cases hget : (GenContFract.of x).s.get? n with
      | none =>
        have heq : (GenContFract.of x).contsAux (n + 2) = (GenContFract.of x).contsAux (n + 1) :=
          GenContFract.contsAux_stable_of_terminated (Nat.le_succ _) hget
        rw [heq]
      | some gp =>
        have hrec := GenContFract.contsAux_recurrence hget rfl rfl
        rw [hrec]
        obtain ⟨ifp, hstr, hb_eq⟩ :=
          GenContFract.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some hget
        have ha1 : gp.a = 1 := by
          have hs := GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hstr
          rw [hget] at hs
          injection hs with hpair
          rw [hpair]
        have hb1 : (1 : ℝ) ≤ gp.b := by
          obtain ⟨ifp_prev, hstr_prev, hfr_ne, hof_eq⟩ :=
            GenContFract.IntFractPair.succ_nth_stream_eq_some_iff.mp hstr
          have hfr_rng := GenContFract.IntFractPair.nth_stream_fr_nonneg_lt_one hstr_prev
          have hfr_pos : 0 < ifp_prev.fr := lt_of_le_of_ne hfr_rng.1 (Ne.symm hfr_ne)
          have hinv_gt : (1 : ℝ) < ifp_prev.fr⁻¹ := (one_lt_inv₀ hfr_pos).mpr hfr_rng.2
          have hb_ge1 : (1 : ℤ) ≤ ifp.b := by
            rw [← hof_eq]
            exact Int.le_floor.mpr (by exact_mod_cast le_of_lt hinv_gt)
          rw [← hb_eq]
          exact_mod_cast hb_ge1
        have hdn1_nn : 0 ≤ ((GenContFract.of x).contsAux (n + 1)).b := le_trans ih.1 ih.2
        rw [ha1]
        dsimp only
        nlinarith [ih.1, hdn1_nn, hb1]
  refine monotone_nat_of_le_succ fun n => ?_
  rw [GenContFract.den_eq_conts_b, GenContFract.den_eq_conts_b,
    GenContFract.nth_cont_eq_succ_nth_contAux, GenContFract.nth_cont_eq_succ_nth_contAux]
  exact (hstep (n + 1)).2

/-! ### Part 3: Regular CF stopping index `cfStopIdx` & generic word-tree bridge -/

/-- Regular CF stopping index `k(j)(x)`: the largest convergent index `n` with
    `(GenContFract.of x).dens n ≤ (NoShortDim.H j : ℝ)` (Paper 2's `H_j = ⌊Q_j √j⌋`). -/
noncomputable def cfStopIdx (x : ℝ) (j : ℕ) : ℕ :=
  sSup {n : ℕ | (GenContFract.of x).dens n ≤ ((NoShortDim.H j : ℕ) : ℝ)}

/-- If `dens K ≤ H_j < dens (K + 1)`, then `dens n ≤ H_j ↔ n ≤ K` and
    `cfStopIdx x j = K`. -/
theorem cfStopIdx_eq_of_bracket {x : ℝ} {j K : ℕ}
    (hle : (GenContFract.of x).dens K ≤ ((NoShortDim.H j : ℕ) : ℝ))
    (hgt : ((NoShortDim.H j : ℕ) : ℝ) < (GenContFract.of x).dens (K + 1)) :
    (∀ n : ℕ, (GenContFract.of x).dens n ≤ ((NoShortDim.H j : ℕ) : ℝ) ↔ n ≤ K) ∧
    cfStopIdx x j = K := by
  have hiff : ∀ n : ℕ, (GenContFract.of x).dens n ≤ ((NoShortDim.H j : ℕ) : ℝ) ↔ n ≤ K := by
    intro n
    constructor
    · intro hn
      by_contra hlt
      have hK1 : K + 1 ≤ n := by omega
      have hmono := dens_of_mono x hK1
      linarith
    · intro hn
      exact le_trans (dens_of_mono x hn) hle
  refine ⟨hiff, ?_⟩
  unfold cfStopIdx
  have hset : {n : ℕ | (GenContFract.of x).dens n ≤ ((NoShortDim.H j : ℕ) : ℝ)} = Set.Iic K := by
    ext n; exact hiff n
  rw [hset]
  exact csSup_Iic

/-- Helper: if `x ∈ Ioo a b ∩ Icc c d` with `c < d`, then `Ioo a b`, `Ioo c d` meet. -/
private theorem not_disjoint_Ioo_of_mem_Ioo_Icc {a b c d x : ℝ}
    (h1 : x ∈ Set.Ioo a b) (h2 : x ∈ Set.Icc c d) (hcd : c < d) :
    ¬ Disjoint (Set.Ioo a b) (Set.Ioo c d) := by
  intro hdisj
  rcases lt_or_eq_of_le h2.1 with hcx | hcx
  · rcases lt_or_eq_of_le h2.2 with hxd | hxd
    · exact Set.disjoint_left.mp hdisj h1 ⟨hcx, hxd⟩
    · let m : ℝ := (max a c + x) / 2
      have hmax_lt : max a c < x := max_lt h1.1 hcx
      have hm1 : m ∈ Set.Ioo a b :=
        ⟨by dsimp only [m]; linarith [le_max_left a c, hmax_lt],
         by dsimp only [m]; linarith [hmax_lt, h1.2]⟩
      have hm2 : m ∈ Set.Ioo c d :=
        ⟨by dsimp only [m]; linarith [le_max_right a c, hmax_lt],
         by dsimp only [m]; linarith [hmax_lt, hxd]⟩
      exact Set.disjoint_left.mp hdisj hm1 hm2
  · let m : ℝ := (x + min b d) / 2
    have hlt_min : x < min b d := lt_min h1.2 (by linarith)
    have hm1 : m ∈ Set.Ioo a b :=
      ⟨by dsimp only [m]; linarith [hlt_min, h1.1],
       by dsimp only [m]; linarith [min_le_left b d, hlt_min]⟩
    have hm2 : m ∈ Set.Ioo c d :=
      ⟨by dsimp only [m]; linarith [hlt_min, hcx],
       by dsimp only [m]; linarith [min_le_right b d, hlt_min]⟩
    exact Set.disjoint_left.mp hdisj hm1 hm2

/-- Generic pointwise regular continued-fraction bridge for any stopped CF word tree.
    Every `x` in the Cantor set is irrational in `(0, 1)` and admits a nested sequence of
    stopped words `w j` whose regular CF convergent denominators match `cfProd (0 :: w j)`
    and whose stopping indices satisfy `cfStopIdx x j = (w j).length - 1`. -/
theorem stopped_word_tree_cf_bridge
    {wordAtoms : ℕ → Finset (List ℕ)} {wordChild : ℕ → List ℕ → Finset (List ℕ)}
    {T : StoppedTree.TreeData} {j0 : ℕ} (hj0 : 1 ≤ j0)
    (hatoms : ∀ j ≥ j0, T.atoms j = (wordAtoms j).image cylPair)
    (hsucc : ∀ j ≥ j0, wordAtoms (j + 1) = (wordAtoms j).biUnion (wordChild j))
    (hpos : ∀ j ≥ j0, ∀ w ∈ wordAtoms j, PosDigits w ∧ w ≠ [])
    (hinc : ∀ j ≥ j0, ∀ w₁ ∈ wordAtoms j, ∀ w₂ ∈ wordAtoms j, w₁ ≠ w₂ → ¬ (w₁ <+: w₂))
    (hbracket : ∀ j ≥ j0, ∀ w ∈ wordAtoms j,
      ((cfProd (0 :: w)) 1 1 : ℝ) ≤ WindowPaperScale.Hpaper j ∧
      WindowPaperScale.Hpaper j < ((cfProd (0 :: w)) 1 0 : ℝ))
    (hchild_ext : ∀ j ≥ j0, ∀ w ∈ wordAtoms j, ∀ c ∈ wordChild j w,
      ∃ ext, c = w ++ ext ∧ PosDigits ext ∧ (2 ≤ ext.length ∨ ∃ a, ext = [a] ∧ 2 ≤ a))
    {x : ℝ} (hx : x ∈ WindowTreePrune.cantorSet T j0) :
    x ∈ Set.Ioo (0 : ℝ) 1 ∧
    Irrational x ∧
    ∃ w : ℕ → List ℕ,
      (∀ j ≥ j0, w j ∈ wordAtoms j) ∧
      (∀ j ≥ j0, w (j + 1) ∈ wordChild j (w j)) ∧
      (∀ j ≥ j0, x ∈ Set.Ioo (cylPair (w j)).1 (cylPair (w j)).2) ∧
      (∀ j ≥ j0, ∀ k ≤ (w j).length,
        (GenContFract.of x).dens k = ((cfProd (0 :: (w j).take k)) 1 0 : ℝ)) ∧
      (∀ j ≥ j0,
        (∀ n : ℕ, (GenContFract.of x).dens n ≤ ((NoShortDim.H j : ℕ) : ℝ) ↔
          n ≤ (w j).length - 1) ∧
        cfStopIdx x j = (w j).length - 1) := by
  classical
  have hcyl_lt : ∀ j ≥ j0, ∀ w ∈ wordAtoms j, (cylPair w).1 < (cylPair w).2 := by
    intro j hj w hw
    obtain ⟨hpd, hne⟩ := hpos j hj w hw
    have hlen := cylPair_len hpd hne
    have hu_pos : (0 : ℝ) < ((cfProd (0 :: w)) 1 0 : ℝ) :=
      lt_trans (WindowPaperScale.Hpaper_pos j) (hbracket j hj w hw).2
    have hv_nn : (0 : ℝ) ≤ ((cfProd (0 :: w)) 1 1 : ℝ) := by
      exact_mod_cast cfProd_nonneg (0 :: w) 1 1
    have hpos_len : 0 < (cylPair w).2 - (cylPair w).1 := by rw [hlen]; positivity
    linarith
  have huniq : ∀ j ≥ j0, ∀ u ∈ wordAtoms j, ∀ v ∈ wordAtoms j,
      x ∈ Set.Ioo (cylPair u).1 (cylPair u).2 →
      x ∈ Set.Icc (cylPair v).1 (cylPair v).2 → u = v := by
    intro j hj u hu v hv hxu hxv
    by_contra hne
    have hdisj := cylPair_disj_of_incomparable (hpos j hj u hu).1 (hpos j hj v hv).1
      (hinc j hj u hu v hv hne) (hinc j hj v hv u hu (Ne.symm hne))
    exact not_disjoint_Ioo_of_mem_Ioo_Icc hxu hxv (hcyl_lt j hj v hv) hdisj
  have hex_open : ∀ j ≥ j0, ∃ w ∈ wordAtoms j, x ∈ Set.Ioo (cylPair w).1 (cylPair w).2 := by
    intro j hj
    have hx1 := Set.mem_iInter.mp (Set.mem_iInter.mp hx (j + 1)) (by omega)
    obtain ⟨I, hI, hxI⟩ := Set.mem_iUnion₂.mp hx1
    rw [hatoms (j + 1) (by omega), Finset.mem_image] at hI
    obtain ⟨c, hc, rfl⟩ := hI
    rw [hsucc j hj, Finset.mem_biUnion] at hc
    obtain ⟨p, hp, hcp⟩ := hc
    obtain ⟨ext, rfl, hext_pos, hext_str⟩ := hchild_ext j hj p hp c hcp
    exact ⟨p, hp, cylPair_nest_strict (hpos j hj p hp).1 (hpos j hj p hp).2 hext_pos hext_str hxI⟩
  let w : ℕ → List ℕ := fun j =>
    if h : j0 ≤ j then Classical.choose (hex_open j h) else []
  have hw_mem : ∀ j ≥ j0, w j ∈ wordAtoms j := by
    intro j hj
    simp only [w, hj, ↓reduceDIte]
    exact (Classical.choose_spec (hex_open j hj)).1
  have hw_Ioo : ∀ j ≥ j0, x ∈ Set.Ioo (cylPair (w j)).1 (cylPair (w j)).2 := by
    intro j hj
    simp only [w, hj, ↓reduceDIte]
    exact (Classical.choose_spec (hex_open j hj)).2
  have hw_child : ∀ j ≥ j0, w (j + 1) ∈ wordChild j (w j) := by
    intro j hj
    have hc : w (j + 1) ∈ wordAtoms (j + 1) := hw_mem (j + 1) (by omega)
    rw [hsucc j hj, Finset.mem_biUnion] at hc
    obtain ⟨p, hp, hcp⟩ := hc
    obtain ⟨ext, hceq, hext_pos, hext_str⟩ := hchild_ext j hj p hp (w (j + 1)) hcp
    have hx_c_Icc : x ∈ Set.Icc (cylPair (w (j + 1))).1 (cylPair (w (j + 1))).2 :=
      Set.Ioo_subset_Icc_self (hw_Ioo (j + 1) (by omega))
    rw [hceq] at hx_c_Icc
    have hx_p_Ioo : x ∈ Set.Ioo (cylPair p).1 (cylPair p).2 :=
      cylPair_nest_strict (hpos j hj p hp).1 (hpos j hj p hp).2 hext_pos hext_str hx_c_Icc
    have hp_eq : p = w j := huniq j hj p hp (w j) (hw_mem j hj) hx_p_Ioo
      (Set.Ioo_subset_Icc_self (hw_Ioo j hj))
    rwa [← hp_eq]
  have hx_unit : x ∈ Set.Ioo (0 : ℝ) 1 :=
    Ioo_cylPair_subset_Ioo_unit (hpos j0 le_rfl (w j0) (hw_mem j0 le_rfl)).1
      (hpos j0 le_rfl (w j0) (hw_mem j0 le_rfl)).2 (hw_Ioo j0 le_rfl)
  have hlen_grow : ∀ d : ℕ, d + 1 ≤ (w (j0 + d)).length := by
    intro d
    induction d with
    | zero =>
      have hne := (hpos j0 le_rfl (w j0) (hw_mem j0 le_rfl)).2
      exact List.length_pos_of_ne_nil hne
    | succ d ih =>
      have hj : j0 ≤ j0 + d := by omega
      have hch := hw_child (j0 + d) hj
      obtain ⟨ext, heq, _, hstr⟩ := hchild_ext (j0 + d) hj (w (j0 + d)) (hw_mem _ hj) _ hch
      have hext_pos_len : 1 ≤ ext.length := by
        rcases hstr with h2 | ⟨a, rfl, _⟩
        · omega
        · simp
      have hadd : j0 + (d + 1) = (j0 + d) + 1 := by omega
      rw [hadd, heq, List.length_append]
      omega
  have hirr : Irrational x := by
    intro ⟨q, hq⟩
    have hterm : (GenContFract.of x).Terminates :=
      (GenContFract.terminates_iff_rat x).mpr ⟨q, hq.symm⟩
    obtain ⟨N, hN⟩ := hterm
    have hj : j0 ≤ j0 + N := by omega
    have hpd := hpos (j0 + N) hj (w (j0 + N)) (hw_mem (j0 + N) hj)
    obtain ⟨t, ht, hmob⟩ := exists_mobius_of_mem_Ioo_cylPair hpd.1 hpd.2 (hw_Ioo (j0 + N) hj)
    have hnot := not_terminatedAt_mobius hpd.1 ht.1 ht.2 (k := N) (by have := hlen_grow N; omega)
    rw [hmob] at hnot
    exact hnot hN
  have hdens : ∀ j ≥ j0, ∀ k ≤ (w j).length,
      (GenContFract.of x).dens k = ((cfProd (0 :: (w j).take k)) 1 0 : ℝ) := by
    intro j hj k hk
    have hpd := hpos j hj (w j) (hw_mem j hj)
    obtain ⟨t, ht, hmob⟩ := exists_mobius_of_mem_Ioo_cylPair hpd.1 hpd.2 (hw_Ioo j hj)
    rw [← hmob]
    exact dens_mobius_eq hpd.1 ht.1 ht.2 hk
  have hstop : ∀ j ≥ j0,
      (∀ n : ℕ, (GenContFract.of x).dens n ≤ ((NoShortDim.H j : ℕ) : ℝ) ↔
        n ≤ (w j).length - 1) ∧
      cfStopIdx x j = (w j).length - 1 := by
    intro j hj
    have hpd := hpos j hj (w j) (hw_mem j hj)
    obtain ⟨t, ht, hmob⟩ := exists_mobius_of_mem_Ioo_cylPair hpd.1 hpd.2 (hw_Ioo j hj)
    obtain ⟨hd_top, hd_pen⟩ := dens_mobius_top_and_penult hpd.1 hpd.2 ht.1 ht.2
    rw [hmob] at hd_top hd_pen
    obtain ⟨hbr_le, hbr_gt⟩ := hbracket j hj (w j) (hw_mem j hj)
    rw [WindowPaperScale.Hpaper_eq (le_trans hj0 hj)] at hbr_le hbr_gt
    have hlen1 : 1 ≤ (w j).length := List.length_pos_of_ne_nil hpd.2
    have hsub : (w j).length - 1 + 1 = (w j).length := by omega
    exact cfStopIdx_eq_of_bracket (K := (w j).length - 1)
      (by rw [hd_pen]; exact hbr_le)
      (by rw [hsub, hd_top]; exact hbr_gt)
  exact ⟨hx_unit, hirr, w, hw_mem, hw_child, hw_Ioo, hdens, hstop⟩

/-- Every subset of `(0, 1)` in `ℝ` has Hausdorff dimension at most `1`. -/
theorem dimH_le_one_of_subset_Ioo_unit {S : Set ℝ} (hS : S ⊆ Set.Ioo (0 : ℝ) 1) :
    dimH S ≤ (1 : ℝ≥0∞) := by
  refine dimH_le_of_hausdorffMeasure_ne_top ?_
  have h1 : μH[(1 : ℝ)] S ≤ μH[(1 : ℝ)] (Set.Ioo (0 : ℝ) 1) := MeasureTheory.measure_mono hS
  have hvol : μH[(1 : ℝ)] (Set.Ioo (0 : ℝ) 1) = (1 : ℝ≥0∞) := by
    rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Ioo]
    norm_num
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (hvol ▸ h1)

/-! ### Part 4: End-to-end `thm:windows` parity set (`prescribedParitySet`) -/

/-- The paper's prescribed-eventual-parity target set in `thm:windows`:
    irrationals `x ∈ (0, 1)` whose regular CF stopping index `k(j)(x)` eventually satisfies
    `k(j)(x) ≡ ε j (mod 2)`. -/
def prescribedParitySet (ε : ℕ → Bool) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 |
    Irrational x ∧ ∃ J0 : ℕ, ∀ j ≥ J0, ((cfStopIdx x j) % 2 == 1) = ε j}

/-- Pointwise regular continued-fraction bridge for `cfWindowsTree ε`:
    every `x ∈ cantorSet (cfWindowsTree ε) (10^6)` is irrational in `(0, 1)` and has
    regular CF convergent denominators and stopping indices `k(j)(x)` matching the nested
    words of `cfWordAtoms ε`, with `((cfStopIdx x j) % 2 == 1) = ε j` for all `j ≥ 10^6`. -/
theorem mem_cantorSet_cfWindowsTree_cf (ε : ℕ → Bool) {x : ℝ}
    (hx : x ∈ WindowTreePrune.cantorSet (cfWindowsTree ε) j0CF) :
    x ∈ Set.Ioo (0 : ℝ) 1 ∧
    Irrational x ∧
    ∃ w : ℕ → List ℕ,
      (∀ j ≥ j0CF, w j ∈ cfWordAtoms ε j) ∧
      (∀ j ≥ j0CF, w (j + 1) ∈ cfWordChild ε j (w j)) ∧
      (∀ j ≥ j0CF, ∀ k ≤ (w j).length,
        (GenContFract.of x).dens k = ((cfProd (0 :: (w j).take k)) 1 0 : ℝ)) ∧
      (∀ j ≥ j0CF,
        cfStopIdx x j = (w j).length - 1 ∧ ((cfStopIdx x j) % 2 == 1) = ε j) := by
  have hbridge := stopped_word_tree_cf_bridge
    (wordAtoms := cfWordAtoms ε) (wordChild := cfWordChild ε)
    (T := cfWindowsTree ε) (j0 := j0CF) (by unfold j0CF; omega)
    (fun _ _ => rfl)
    (fun j hj => cfWordAtoms_succ ε hj)
    (fun j hj w hw =>
      let h := (cfWordAtoms_inv_and_incomp ε j hj).1 w hw
      ⟨h.1, h.2.1⟩)
    (fun j hj => (cfWordAtoms_inv_and_incomp ε j hj).2)
    (fun j hj w hw => by
      have h := (cfWordAtoms_inv_and_incomp ε j hj).1 w hw
      have hHpos := WindowPaperScale.Hpaper_pos j
      have hv_lt : (4 : ℝ) * ((cfProd (0 :: w)) 1 1 : ℝ) < ((cfProd (0 :: w)) 1 0 : ℝ) := by
        exact_mod_cast h.2.2.2.2.2.2
      exact ⟨by linarith [h.2.2.2.2.1], by linarith [h.2.2.2.1]⟩)
    (fun j hj w hw c hc => by
      simp only [cfWordChild, Finset.mem_image, Finset.mem_filter] at hc
      obtain ⟨p, ⟨hp_box, hgcd⟩, rfl⟩ := hc
      have hinv := (cfWordAtoms_inv_and_incomp ε j hj).1 w hw
      have hR_lo : (10 ^ 6 : ℝ) ≤ parentScale j w := by
        have h1 := parentScale_ge hinv
        have h2 := WindowPaperScale.Rpaper_ge_three_mul (by unfold j0CF at hj; omega : 1 ≤ j)
        have h3 : (10 ^ 6 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        linarith
      have hn1 := (WindowMobiusCount.box_mem_pos _ p hp_box).2
      have hnm : p.2 < p.1 := by
        obtain ⟨hm, hn⟩ := (WindowMobiusCount.box_mem_iff _ p).mp hp_box
        simp only [Finset.mem_Icc] at hm hn
        have h1 : ((WindowMobiusCount.Mlo (parentScale j w) : ℕ) : ℝ) ≤ (p.1 : ℝ) := by
          exact_mod_cast hm.1
        have h2 : 0.34 * parentScale j w < ((Nat.floor (0.34 * parentScale j w) : ℕ) : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        have h3 : (p.2 : ℝ) ≤ ((WindowMobiusCount.Nhi (parentScale j w) : ℕ) : ℝ) := by
          exact_mod_cast hn.2
        have h4 : ((Nat.floor (0.22 * parentScale j w) : ℕ) : ℝ) ≤ 0.22 * parentScale j w :=
          Nat.floor_le (by linarith)
        simp only [WindowMobiusCount.Mlo, WindowMobiusCount.Nhi, Nat.cast_add, Nat.cast_one]
          at h1 h3
        exact_mod_cast (by linarith : (p.2 : ℝ) < (p.1 : ℝ))
      obtain ⟨ht_pos, ht_ne, _, _, _⟩ :=
        chooseParityCF_props hn1 hnm hgcd (targetTailParity ε j w)
      refine ⟨chooseParityCF p.1 p.2 (targetTailParity ε j w) ++ [4], ?_, ?_, Or.inl ?_⟩
      · simp [makeChildWord, List.append_assoc]
      · exact posDigits_append.mpr ⟨ht_pos, posDigits_cons.mpr ⟨by omega, posDigits_nil⟩⟩
      · have hlen1 : 1 ≤ (chooseParityCF p.1 p.2 (targetTailParity ε j w)).length :=
          List.length_pos_of_ne_nil ht_ne
        simp; omega)
    hx
  obtain ⟨hunit, hirr, w, hw_mem, hw_child, _, hdens, hstop⟩ := hbridge
  refine ⟨hunit, hirr, w, hw_mem, hw_child, hdens, ?_⟩
  intro j hj
  have hst := (hstop j hj).2
  have hpar := ((cfWordAtoms_inv_and_incomp ε j hj).1 (w j) (hw_mem j hj)).2.2.1
  exact ⟨hst, by rw [hst]; exact hpar⟩

/-- `cantorSet (cfWindowsTree ε) (10^6)` is contained in `prescribedParitySet ε`. -/
theorem cantorSet_cfWindowsTree_subset_prescribedParitySet (ε : ℕ → Bool) :
    WindowTreePrune.cantorSet (cfWindowsTree ε) j0CF ⊆ prescribedParitySet ε := by
  intro x hx
  obtain ⟨hunit, hirr, _, _, _, _, hstop⟩ := mem_cantorSet_cfWindowsTree_cf ε hx
  exact ⟨hunit, hirr, j0CF, fun j hj => (hstop j hj).2⟩

/-- End-to-end unconditional `thm:windows` (full-dimensional parity branch):
    for any prescribed parity sequence `ε : ℕ → Bool`, the set of irrationals `x ∈ (0, 1)`
    with `k(j)(x) ≡ ε j (mod 2)` eventually has Hausdorff dimension `≥ 1`. -/
theorem dimH_ge_one_prescribedParitySet (ε : ℕ → Bool) :
    (1 : ℝ≥0∞) ≤ dimH (prescribedParitySet ε) :=
  le_trans (dimH_ge_one_cfWindowsTree ε)
    (dimH_mono (cantorSet_cfWindowsTree_subset_prescribedParitySet ε))

/-- Exact dimension `dimH (prescribedParitySet ε) = 1` for `thm:windows`. -/
theorem dimH_prescribedParitySet_eq_one (ε : ℕ → Bool) :
    dimH (prescribedParitySet ε) = 1 :=
  le_antisymm (dimH_le_one_of_subset_Ioo_unit fun _ hx => hx.1)
    (dimH_ge_one_prescribedParitySet ε)

#print axioms WindowCFBridge.mobius_mem_Ioo_cylPair
#print axioms WindowCFBridge.Ioo_cylPair_subset_Ioo_unit
#print axioms WindowCFBridge.cylPair_nest_strict
#print axioms WindowCFBridge.exists_mobius_of_mem_Ioo_cylPair
#print axioms WindowCFBridge.mobius_cfProd_zero_mem_Ioo
#print axioms WindowCFBridge.mobius_cfProd_zero_cons
#print axioms WindowCFBridge.intFractPair_stream_one_div_add
#print axioms WindowCFBridge.stream_mobius_spec
#print axioms WindowCFBridge.not_terminatedAt_mobius
#print axioms WindowCFBridge.contsAux_mobius_eq
#print axioms WindowCFBridge.dens_mobius_eq
#print axioms WindowCFBridge.dens_mobius_top_and_penult
#print axioms WindowCFBridge.dens_of_mono
#print axioms WindowCFBridge.cfStopIdx_eq_of_bracket
#print axioms WindowCFBridge.stopped_word_tree_cf_bridge
#print axioms WindowCFBridge.dimH_le_one_of_subset_Ioo_unit
#print axioms WindowCFBridge.mem_cantorSet_cfWindowsTree_cf
#print axioms WindowCFBridge.cantorSet_cfWindowsTree_subset_prescribedParitySet
#print axioms WindowCFBridge.dimH_ge_one_prescribedParitySet
#print axioms WindowCFBridge.dimH_prescribedParitySet_eq_one

end WindowCFBridge
