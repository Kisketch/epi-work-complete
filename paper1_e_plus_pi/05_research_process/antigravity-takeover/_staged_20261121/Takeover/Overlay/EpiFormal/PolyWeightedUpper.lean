import Mathlib
import EpiFormal.PolyGaugeAndPhaseTransition
import EpiFormal.WeightedPhase

/-! Upper half of the subcritical phase transition for polynomial recurrences.
Use the recurrence defect to count successor pairs, reusing the critical-gauge
intervals, and use the existing factorial lower bound to bound the cover cost. -/

open Real Filter Topology Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace PolyWeightedUpper
open TrichotomyAndPolyExtension PolyGaugeAndPhaseTransition SpectralGap

noncomputable section

private lemma defect_bound (P : PolyRecData) {α t x : ℝ} {j : ℕ}
    (hα : α ≤ P.r) (_ht : 0 ≤ t) (hj : P.J₀ + 1 ≤ j)
    (hx : P.polyWeightedSeq α x j ≤ t) :
    |(P.polyDefect x j : ℝ)| ≤ (polyKUpper P * t + 1) * (j : ℝ) ^ ((P.r : ℝ) - α) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hjp : (0 : ℝ) < j := by linarith
  have hjα : 0 < (j : ℝ) ^ α := Real.rpow_pos_of_pos hjp _
  have hA0 : 0 ≤ (P.A j : ℝ) := by
    exact_mod_cast (show 0 ≤ P.A j from (by norm_num : (0 : ℤ) ≤ 2).trans
      (P.A_ge_two (by omega : P.J₀ ≤ j)))
  have hA : (P.A j : ℝ) ≤ polyKUpper P * (j : ℝ) ^ P.r := by
    have heq : (P.A j : ℝ) = (P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ) := by
      unfold PolyRecData.A; push_cast; ring
    rw [heq]
    have h := (P.poly_Q_ratio_bounds hj).2.2
    unfold polyKUpper
    linarith
  have he : |P.polyEps x j| ≤ t / (j : ℝ) ^ α := by
    apply (le_div_iff₀ hjα).2
    simpa [PolyRecData.polyWeightedSeq, P.abs_polyEps_eq_dist, mul_comm] using hx
  have hm : |(P.A j : ℝ) * P.polyEps x j| ≤
      (polyKUpper P * t) * (j : ℝ) ^ ((P.r : ℝ) - α) := by
    rw [abs_mul, abs_of_nonneg hA0]
    calc _ ≤ (polyKUpper P * (j : ℝ) ^ P.r) * (t / (j : ℝ) ^ α) :=
              mul_le_mul hA he (abs_nonneg _) (mul_nonneg (polyKUpper_pos P).le (by positivity))
         _ = _ := by
              rw [Real.rpow_sub hjp, Real.rpow_natCast]
              ring
  have hpow : 1 ≤ (j : ℝ) ^ ((P.r : ℝ) - α) := Real.one_le_rpow hj1 (sub_nonneg.mpr hα)
  rw [P.poly_defect_identity x (by omega : P.J₀ ≤ j)]
  calc _ ≤ |(P.A j : ℝ) * P.polyEps x j| + |P.polyEps x (j + 1)| +
             |P.polyEps x (j - 1)| :=
          (abs_add_le ..).trans (add_le_add (by simpa [sub_eq_add_neg] using abs_add_le ((P.A j : ℝ) * P.polyEps x j) (-P.polyEps x (j+1))) le_rfl)
       _ ≤ (polyKUpper P * t + 1) * (j : ℝ) ^ ((P.r : ℝ) - α) := by
          nlinarith only [hm, hpow, P.abs_polyEps_le_half x (j+1),
            P.abs_polyEps_le_half x (j-1)]

private def digits (C θ : ℝ) (j : ℕ) : Finset ℤ :=
  Finset.Icc (-⌊C * (j : ℝ) ^ θ⌋) ⌊C * (j : ℝ) ^ θ⌋

private lemma mem_digits {C θ : ℝ} {d : ℤ} {j : ℕ}
    (h : |(d : ℝ)| ≤ C * (j : ℝ) ^ θ) : d ∈ digits C θ j := by
  rw [digits, Finset.mem_Icc]
  have habs := abs_le.mp h
  constructor
  · have hl : -d ≤ ⌊C * (j : ℝ) ^ θ⌋ := Int.le_floor.mpr (by push_cast; linarith)
    omega
  · exact Int.le_floor.mpr habs.2

private lemma card_digits_le {C θ : ℝ} (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    {j : ℕ} (hj : 1 ≤ j) : ((digits C θ j).card : ℝ) ≤ (2*C+1) * (j : ℝ) ^ θ := by
  have hpow : 1 ≤ (j : ℝ) ^ θ := Real.one_le_rpow (by exact_mod_cast hj) hθ
  let T : ℝ := C * (j : ℝ) ^ θ
  have hT : 0 ≤ T := mul_nonneg hC (by linarith)
  have hf : 0 ≤ ⌊T⌋ := Int.floor_nonneg.mpr hT
  have hcard : ((digits C θ j).card : ℝ) = 2 * (⌊T⌋ : ℝ) + 1 := by
    change ((Finset.Icc (-⌊T⌋) ⌊T⌋).card : ℝ) = _
    have hc : ((Int.toNat (⌊T⌋ + 1 - -⌊T⌋) : ℕ) : ℝ) =
        ((⌊T⌋ + 1 - -⌊T⌋ : ℤ) : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ ⌊T⌋ + 1 - -⌊T⌋))
    rw [Int.card_Icc, hc]
    push_cast
    ring
  rw [hcard]
  have hfloor := Int.floor_le T
  dsimp [T] at hfloor
  nlinarith only [hfloor, hpow]

private def tree (P : PolyRecData) (C θ : ℝ) (N : ℕ) (u v : ℤ) : ℕ → Finset (ℤ × ℤ)
  | 0 => {(u,v)}
  | n+1 => (tree P C θ N u v n).biUnion fun p =>
      (digits C θ (N+n+1)).image fun d => (p.2, P.A (N+n+1) * p.2 + p.1 + d)

private lemma tree_count (P : PolyRecData) {C θ : ℝ} (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (N : ℕ) (u v : ℤ) (n : ℕ) :
    ((tree P C θ N u v n).card : ℝ) ≤
      (2*C+1)^n * (Nat.factorial (N+n) : ℝ) ^ θ := by
  induction n with
  | zero =>
    simp only [tree, Finset.card_singleton, Nat.cast_one, pow_zero, one_mul, Nat.add_zero]
    exact Real.one_le_rpow (by exact_mod_cast Nat.factorial_pos N) hθ
  | succ n ih =>
    let j := N+n+1
    have hcard : (tree P C θ N u v (n+1)).card ≤
        (tree P C θ N u v n).card * (digits C θ j).card := by
      change ((tree P C θ N u v n).biUnion _).card ≤ _
      exact Finset.card_biUnion_le_card_mul _ _ _ (fun _ _ => Finset.card_image_le)
    have hcard' : ((tree P C θ N u v (n+1)).card : ℝ) ≤
        ((tree P C θ N u v n).card : ℝ) * ((digits C θ j).card : ℝ) := by exact_mod_cast hcard
    have hj : 1 ≤ j := by omega
    calc _ ≤ ((tree P C θ N u v n).card : ℝ) * ((digits C θ j).card : ℝ) := hcard'
         _ ≤ ((2*C+1)^n * (Nat.factorial (N+n) : ℝ)^θ) * ((2*C+1) * (j : ℝ)^θ) :=
          mul_le_mul ih (card_digits_le hC hθ hj) (by positivity) (by positivity)
         _ = _ := by
          rw [show N+(n+1) = (N+n)+1 by omega, Nat.factorial_succ, Nat.cast_mul,
            Real.mul_rpow (by positivity) (by positivity), pow_succ]
          change ((2*C+1)^n * (Nat.factorial (N+n) : ℝ)^θ) * ((2*C+1) * (j : ℝ)^θ) =
            (2*C+1)^n * (2*C+1) * ((j : ℝ)^θ * (Nat.factorial (N+n) : ℝ)^θ)
          ring

private def tail (P : PolyRecData) (α t : ℝ) (N : ℕ) (u v : ℤ) : Set ℝ :=
  {x | round ((P.Q N : ℝ)*x) = u ∧ round ((P.Q (N+1) : ℝ)*x) = v ∧
    ∀ j ≥ N, P.polyWeightedSeq α x j ≤ t}

private lemma cover (P : PolyRecData) {α t : ℝ} (hα : α ≤ P.r) (ht : 0 ≤ t)
    (N : ℕ) (hN : P.J₁ ≤ N) (u v : ℤ) (n : ℕ) :
    tail P α t N u v ⊆
      ⋃ z : (tree P (polyKUpper P * t + 1) ((P.r : ℝ)-α) N u v n : Set (ℤ × ℤ)),
        polyGaugeInterv P (N+n) z.1.1 := by
  intro x hx
  let M (j : ℕ) := round ((P.Q j : ℝ)*x)
  have hm : ∀ k, (M (N+k),M (N+k+1)) ∈
      tree P (polyKUpper P * t + 1) ((P.r : ℝ)-α) N u v k := by
    intro k
    induction k with
    | zero => simp [M,tree,hx.1,hx.2.1]
    | succ k ih =>
      have hJ := P.J₁_ge_J₀_succ
      have hm := mem_digits (defect_bound P hα ht (show P.J₀+1 ≤ N+k+1 by omega)
        (hx.2.2 (N+k+1) (by omega)))
      refine Finset.mem_biUnion.mpr ⟨_, ih, Finset.mem_image.mpr ⟨P.polyDefect x (N+k+1),hm,?_⟩⟩
      apply Prod.ext
      · rfl
      · change P.A (N+k+1)*M (N+k+1)+M (N+k)+P.polyDefect x (N+k+1) = M (N+(k+1)+1)
        unfold PolyRecData.polyDefect
        rw [show N+k+1+1 = N+(k+1)+1 by omega, show N+k+1-1=N+k by omega]
        change _ + (M _ - _ - _) = _
        ring
  exact Set.mem_iUnion.mpr ⟨⟨_,hm n⟩,mem_polyGaugeInterv_round P x _⟩

private lemma content_tendsto (P : PolyRecData) {α s : ℝ} (hα : α ≤ P.r)
    (hs : (P.r : ℝ)-α < (P.r : ℝ)*s) (C : ℝ) (hC : 1 ≤ C)
    (N : ℕ) (hN : P.J₁ ≤ N) :
    Tendsto (fun n : ℕ => C^n * (Nat.factorial (N+n) : ℝ)^((P.r : ℝ)-α) *
      (1 / (P.Q (N+n) : ℝ))^s) atTop (nhds 0) := by
  have hr : (0 : ℝ) < P.r := by exact_mod_cast (show 0 < P.r by have := P.hr; omega)
  have hs0 : 0 ≤ s := by by_contra! h; nlinarith [mul_neg_of_pos_of_neg hr h]
  let B : ℝ := (P.c : ℝ) / 2^(P.r+1)
  have hB : 0 < B := by
    have hpc : (0 : ℝ) < P.c := by exact_mod_cast (show 0 < P.c by have := P.hc; omega)
    dsimp [B]
    positivity
  let D := C / B^s
  have hD : 0 ≤ D := div_nonneg (le_trans zero_le_one hC) (Real.rpow_nonneg hB.le _)
  have hcore := WeightedPhase.content_core_tendsto D hD (1-((P.r : ℝ)-α)) ((P.r : ℝ)*s) (by linarith)
  have hcore' : Tendsto (fun m : ℕ => D^m * (Nat.factorial m : ℝ)^((P.r : ℝ)-α-(P.r : ℝ)*s))
      atTop (nhds 0) := by convert hcore using 4; ring
  have hshift : Tendsto (fun n : ℕ => N+n) atTop atTop :=
    (tendsto_add_atTop_nat N).congr (fun j => Nat.add_comm j N)
  have hlim := (hcore'.comp hshift).const_mul (1/P.C_J₁^s)
  simp only [mul_zero, Function.comp_def] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · refine Eventually.of_forall (fun n => ?_)
    have hQ : (0 : ℝ) < P.Q (N+n) := by exact_mod_cast P.hQ_pos (N+n)
    positivity
  · refine Eventually.of_forall (fun n => ?_)
    let m := N+n
    have hm : P.J₁ ≤ m := by omega
    have hQ : (0 : ℝ) < P.Q m := by exact_mod_cast P.hQ_pos m
    have hF : (0 : ℝ) < Nat.factorial m := by exact_mod_cast Nat.factorial_pos m
    have hA := P.C_J₁_pos
    have hgt := P.poly_Q_ge_factorial hm
    change _ * (1 / (P.Q m : ℝ))^s ≤ _
    have hq : (1 / (P.Q m : ℝ))^s ≤
        (1 / (P.C_J₁ * B^m * (Nat.factorial m : ℝ)^P.r))^s :=
      Real.rpow_le_rpow (by positivity) (one_div_le_one_div_of_le (by positivity) hgt) hs0
    have hBS : (B^m)^s = (B^s)^m := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le, mul_comm, Real.rpow_mul hB.le,
        Real.rpow_natCast]
    have hFS : ((Nat.factorial m : ℝ)^P.r)^s = (Nat.factorial m : ℝ)^((P.r : ℝ)*s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hF.le]
    calc _ ≤ C^m * (Nat.factorial m : ℝ)^((P.r : ℝ)-α) *
        (1/(P.C_J₁ * B^m * (Nat.factorial m : ℝ)^P.r))^s := by
          gcongr
          exact Nat.le_add_left n N
      _ = _ := by
        change _ = 1 / P.C_J₁^s * (D^m * (Nat.factorial m : ℝ)^((P.r : ℝ)-α-(P.r : ℝ)*s))
        rw [Real.div_rpow zero_le_one (by positivity), Real.one_rpow,
          Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), hBS, hFS, Real.rpow_sub hF]
        dsimp [D]
        rw [div_pow]
        field_simp
        rw [← Real.rpow_add hF, ← Real.rpow_add hF]
        congr 1
        ring

private lemma tail_measure_zero (P : PolyRecData) {α t s : ℝ} (hα : α ≤ P.r)
    (ht : 0 ≤ t) (hs : (P.r : ℝ)-α < (P.r : ℝ)*s) (N : ℕ) (hN : P.J₁ ≤ N) (u v : ℤ) :
    μH[s] (tail P α t N u v) = 0 := by
  have hr : (0 : ℝ) < P.r := by exact_mod_cast (show 0 < P.r by have := P.hr; omega)
  have hs0 : 0 ≤ s := by by_contra! h; nlinarith [mul_neg_of_pos_of_neg hr h]
  let C := polyKUpper P * t + 1
  have hC : 0 ≤ C := add_nonneg (mul_nonneg (polyKUpper_pos P).le ht) zero_le_one
  have hC1 : 1 ≤ 2*C+1 := by linarith
  let F n := tree P C ((P.r : ℝ)-α) N u v n
  let radius n := ENNReal.ofReal (1/(P.Q (N+n) : ℝ))
  have hshift : Tendsto (fun n : ℕ => N+n) atTop atTop :=
    (tendsto_add_atTop_nat N).congr (fun j => Nat.add_comm j N)
  have hrad : Tendsto radius atTop (nhds 0) := by
    simpa [radius, Function.comp_def] using ENNReal.tendsto_ofReal ((P.poly_Q_tendsto_atTop.comp hshift).const_div_atTop 1)
  let cov (n : ℕ) (z : (F n : Set (ℤ × ℤ))) := polyGaugeInterv P (N+n) z.1.1
  have hmain := mkMetric_le_liminf_of_seq_cover (tail P α t N u v) radius hrad cov
    (Eventually.of_forall (fun n z => ediam_polyGaugeInterv_le P (N+n) z.1.1))
    (Eventually.of_forall (cover P hα ht N hN u v)) (fun x => x ^ s)
    (fun _ _ h => ENNReal.rpow_le_rpow h hs0)
  have hbound : ∀ n,
      ((Fintype.card (F n : Set (ℤ × ℤ)) : ℕ) : ℝ≥0∞) * radius n ^ s ≤
      ENNReal.ofReal ((2*C+1)^n * (Nat.factorial (N+n) : ℝ)^((P.r : ℝ)-α) *
        (1/(P.Q (N+n) : ℝ))^s) := by
    intro n
    have hQ : (0 : ℝ) < P.Q (N+n) := by exact_mod_cast P.hQ_pos (N+n)
    have hd := one_div_nonneg.mpr hQ.le
    have hcard := Fintype.card_coe (F n)
    change Fintype.card {z // z ∈ F n} = (F n).card at hcard
    change (↑(Fintype.card {z // z ∈ F n}) : ℝ≥0∞) * (ENNReal.ofReal (1/(P.Q (N+n) : ℝ)))^s ≤ _
    rw [hcard, ← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg hd hs0,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (tree_count P hC (sub_nonneg.mpr hα) N u v n) (Real.rpow_nonneg hd _))
  have hzero := ENNReal.tendsto_ofReal (content_tendsto P hα hs (2*C+1) hC1 N hN)
  simp only [ENNReal.ofReal_zero] at hzero
  have hlim := Filter.liminf_le_liminf (f := atTop) (Eventually.of_forall hbound)
    (by isBoundedDefault) (by isBoundedDefault)
  rw [hzero.liminf_eq] at hlim
  exact le_antisymm (hmain.trans hlim) bot_le

private lemma global_measure_zero (P : PolyRecData) {α c s : ℝ} (hα : α ≤ P.r)
    (hs : (P.r : ℝ)-α < (P.r : ℝ)*s) :
    μH[s] {x : ℝ | P.polyWeightedExponent α x ≤ ENNReal.ofReal c} = 0 := by
  let t := max c 0 + 1
  have ht : 0 < t := by dsimp [t]; linarith [le_max_right c (0:ℝ)]
  let X := {x : ℝ | P.polyWeightedExponent α x ≤ ENNReal.ofReal c}
  have hsub : X ⊆ ⋃ N : {N : ℕ // P.J₁ ≤ N}, ⋃ uv : ℤ × ℤ, tail P α t N.1 uv.1 uv.2 := by
    intro x hx
    have hc : ENNReal.ofReal c < ENNReal.ofReal t :=
      (ENNReal.ofReal_lt_ofReal_iff ht).2 (by dsimp [t]; linarith [le_max_left c (0:ℝ)])
    have hev := eventually_lt_of_limsup_lt ((show P.polyWeightedExponent α x ≤ ENNReal.ofReal c from hx).trans_lt hc)
    obtain ⟨N0,hN0⟩ := eventually_atTop.mp hev
    let N := max P.J₁ N0
    refine Set.mem_iUnion.mpr ⟨⟨N,le_max_left _ _⟩,Set.mem_iUnion.mpr
      ⟨(round ((P.Q N : ℝ)*x), round ((P.Q (N+1) : ℝ)*x)),rfl,rfl,?_⟩⟩
    intro j hj
    exact ((ENNReal.ofReal_lt_ofReal_iff ht).mp (hN0 j ((le_max_right _ _).trans hj))).le
  refine measure_mono_null hsub (measure_iUnion_null ?_)
  intro N
  exact measure_iUnion_null (fun uv => tail_measure_zero P hα ht.le hs N.1 N.2 uv.1 uv.2)

/-- The formal upper bound in the subcritical dimension transition. -/
theorem dimH_polyWeightedExponent_le (P : PolyRecData) (α c : ℝ) (hα : α ≤ P.r) :
    dimH {x : ℝ | P.polyWeightedExponent α x ≤ ENNReal.ofReal c} ≤
      ENNReal.ofReal (1 - α / P.r) := by
  have hr : (0 : ℝ) < P.r := by exact_mod_cast (show 0 < P.r by have := P.hr; omega)
  rw [dimH_eq_iInf]
  apply le_of_forall_gt
  intro d hd
  have hdim : ENNReal.ofReal (1-α/P.r) < ⊤ := ENNReal.ofReal_lt_top
  obtain ⟨s,hs₁,hs₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hd
  have hsub : 0 ≤ 1-α/P.r := sub_nonneg.mpr ((div_le_iff₀ hr).mpr (by simpa using hα))
  have hsreal : 1-α/P.r < (s : ℝ) := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top ENNReal.coe_ne_top).2 hs₁
    simpa [ENNReal.toReal_ofReal hsub] using h
  have hmul := mul_lt_mul_of_pos_right hsreal hr
  have hid : (1-α/P.r)*(P.r : ℝ) = (P.r : ℝ)-α := by field_simp
  rw [hid, mul_comm] at hmul
  have hle : (⨅ (d : ℝ≥0) (_ : μH[(d : ℝ)] {x : ℝ |
      P.polyWeightedExponent α x ≤ ENNReal.ofReal c} = 0), (d : ℝ≥0∞)) ≤ (s : ℝ≥0∞) :=
    iInf₂_le s (global_measure_zero P (c := c) hα hmul)
  exact hle.trans_lt hs₂

end
end PolyWeightedUpper

#print axioms PolyWeightedUpper.dimH_polyWeightedExponent_le






