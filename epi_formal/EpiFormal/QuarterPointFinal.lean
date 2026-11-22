import Mathlib
import EpiFormal.QuarterPointTail
import EpiFormal.ThresholdAttained

open Real Filter Topology Set Classification QuarterPoint QuarterPointTail

namespace QuarterPointFinal

noncomputable section

/-- r_j = M_j/Q_j。 -/
def r (j : ℕ) : ℝ := (Mseq j : ℝ) / (Qsel j : ℝ)
def d (j : ℕ) : ℝ := r (j + 1) - r j
def x0 : ℝ := ∑' j, d j

-- 复用已验证装配（同证明，独立命名空间）
lemma summable_d : Summable d := by
  have hshift : Summable (fun j : ℕ => 1 / (Qsel (j + 1) : ℝ)) :=
    (summable_nat_add_iff 1).mpr summable_inv_Qsel
  have hnorm : ∀ᶠ j in atTop, ‖d j‖ ≤ 1 / (Qsel (j + 1) : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have h := ratio_diff_le j hj
    have hd : d j = (Mseq (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) - (Mseq j : ℝ) / (Qsel j : ℝ) := rfl
    rw [Real.norm_eq_abs, hd]
    exact h
  exact Summable.of_norm_bounded_eventually_nat hshift hnorm

lemma r_eq_sum (n : ℕ) : r n = ∑ j ∈ Finset.range n, d j := by
  have h := Finset.sum_range_sub r n
  have hr0 : r 0 = 0 := by simp [r, Mseq_zero]
  have heq : ∑ j ∈ Finset.range n, d j = ∑ i ∈ Finset.range n, (r (i + 1) - r i) := by
    apply Finset.sum_congr rfl; intro i _; rfl
  rw [heq, h, hr0]; ring

lemma x0_sub_r (n : ℕ) : x0 - r n = ∑' j, d (j + n) := by
  have hsplit := summable_d.sum_add_tsum_nat_add n
  rw [← r_eq_sum] at hsplit
  unfold x0; linarith [hsplit]

lemma Qsel_geom (j : ℕ) (hj : 1 ≤ j) (m : ℕ) :
    (2 : ℝ) ^ m * (Qsel j : ℝ) ≤ (Qsel (j + m) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hjm : 1 ≤ j + m := by omega
      have h2 := Qsel_real_ge_two (j + m) hjm
      have hs : j + (m + 1) = (j + m) + 1 := by omega
      rw [hs]
      calc (2 : ℝ) ^ (m + 1) * (Qsel j : ℝ)
          = 2 * ((2 : ℝ) ^ m * (Qsel j : ℝ)) := by ring
        _ ≤ 2 * (Qsel (j + m) : ℝ) := by gcongr
        _ ≤ (Qsel ((j + m) + 1) : ℝ) := h2

lemma r_tail_bound (j : ℕ) (hj : 1 ≤ j) (m : ℕ) :
    r (j + m) ≤ r j + 2 / (Qsel (j + 1) : ℝ) * (1 - (2 : ℝ) ^ (-(m : ℤ))) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hjm : 1 ≤ j + m := by omega
      have hstep := ratio_diff_le (j + m) hjm
      have hpos : (0 : ℝ) < (Qsel (j + m + 1) : ℝ) := by
        exact_mod_cast Qsel_pos (j + m + 1) (by omega)
      have hgeom := Qsel_geom (j + 1) (by omega) m
      have hQpos : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by
        exact_mod_cast Qsel_pos (j + 1) (by omega)
      have hs : j + (m + 1) = (j + m) + 1 := by omega
      rw [hs]
      have hle : r (j + m + 1) - r (j + m) ≤ 1 / (Qsel (j + m + 1) : ℝ) :=
        le_trans (le_abs_self _) hstep
      have hgeom' : (Qsel (j + m + 1) : ℝ) ≥ (2 : ℝ) ^ m * (Qsel (j + 1) : ℝ) := by
        have hs2 : j + 1 + m = j + m + 1 := by omega
        rw [← hs2]; exact hgeom
      have hfrac : 1 / (Qsel (j + m + 1) : ℝ) ≤
          (2 : ℝ) ^ (-(m : ℤ)) / (Qsel (j + 1) : ℝ) := by
        have h2m : (2 : ℝ) ^ (-(m : ℤ)) = ((2 : ℝ) ^ m)⁻¹ := by
          rw [zpow_neg, zpow_natCast]
        have h2pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
        have hinv := inv_le_inv₀ hpos (mul_pos h2pos hQpos) |>.mpr hgeom'
        rw [h2m]
        simp only [one_mul, div_eq_mul_inv]
        rw [← mul_inv_rev, mul_comm ((Qsel (j + 1) : ℝ)) ((2 : ℝ) ^ m)]
        exact hinv
      have hcoef : 2 / (Qsel (j + 1) : ℝ) * (1 - (2 : ℝ) ^ (-((m + 1 : ℕ) : ℤ))) =
          2 / (Qsel (j + 1) : ℝ) * (1 - (2 : ℝ) ^ (-(m : ℤ))) +
            (2 : ℝ) ^ (-(m : ℤ)) / (Qsel (j + 1) : ℝ) := by
        have hz : (2 : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(m : ℤ)) / 2 := by
          have hcast : (-((m + 1 : ℕ) : ℤ)) = (-(m : ℤ)) - 1 := by push_cast; ring
          rw [hcast, zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring
        rw [hz]; field_simp; ring
      linarith [ih, hle, hfrac, hcoef]

lemma x0_sub_r_le (j : ℕ) (hj : 1 ≤ j) : x0 - r j ≤ 2 / (Qsel (j + 1) : ℝ) := by
  have hsum_shift : Summable (fun m => d (m + j)) :=
    (summable_d.comp_injective (add_left_injective j))
  have hlim_r : Tendsto (fun m => r (j + m)) atTop (nhds x0) := by
    have ht := hsum_shift.tendsto_sum_tsum_nat
    have hx : x0 - r j = ∑' i, d (i + j) := x0_sub_r j
    have heq : (fun m => r (j + m)) = (fun m => r j + ∑ i ∈ Finset.range m, d (i + j)) := by
      funext m
      have h1 := r_eq_sum (j + m)
      have h2 := r_eq_sum j
      rw [h1]
      have hIco : ∑ i ∈ Finset.Ico j (j + m), d i = ∑ i ∈ Finset.range m, d (i + j) := by
        rw [Finset.sum_Ico_eq_sum_range]
        have hsub : j + m - j = m := by omega
        rw [hsub]
        apply Finset.sum_congr rfl; intro i _; congr 1; omega
      have hdecomp : ∑ i ∈ Finset.range (j + m), d i =
          ∑ i ∈ Finset.range j, d i + ∑ i ∈ Finset.Ico j (j + m), d i := by
        rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_add_right j m)]
      rw [hdecomp, hIco, ← h2]
    rw [heq]
    have := ht.const_add (r j)
    have hgoal : r j + ∑' i, d (i + j) = x0 := by linarith [hx]
    rw [hgoal] at this
    exact this
  have hbound : ∀ m, r (j + m) ≤ r j + 2 / (Qsel (j + 1) : ℝ) * (1 - (2 : ℝ) ^ (-(m : ℤ))) :=
    fun m => r_tail_bound j hj m
  have hlim_bound : Tendsto (fun m : ℕ => r j + 2 / (Qsel (j + 1) : ℝ) * (1 - (2 : ℝ) ^ (-(m : ℤ))))
      atTop (nhds (r j + 2 / (Qsel (j + 1) : ℝ))) := by
    have hz : Tendsto (fun m : ℕ => (2 : ℝ) ^ (-(m : ℤ))) atTop (nhds 0) := by
      have hcast : (fun m : ℕ => (2 : ℝ) ^ (-(m : ℤ))) = (fun m : ℕ => ((1 / 2 : ℝ) ^ m)) := by
        funext m
        rw [zpow_neg, zpow_natCast, div_pow, one_pow, one_div]
        <;> field_simp
      rw [hcast]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h1 : Tendsto (fun m : ℕ => 1 - (2 : ℝ) ^ (-(m : ℤ))) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hz
    have h2 := h1.const_mul (2 / (Qsel (j + 1) : ℝ))
    have h3 := h2.const_add (r j)
    have hgoal : r j + 2 / (Qsel (j + 1) : ℝ) * (1 - 0) = r j + 2 / (Qsel (j + 1) : ℝ) := by ring
    rw [hgoal] at h3
    exact h3
  have hle := le_of_tendsto_of_tendsto' hlim_r hlim_bound hbound
  linarith [hle]

/-! ## 最终段：ε 界、舍入一致、defect≡1、Λ=1/4 -/

/-- Q_j x0 − M_j = Q_j (x0 − r_j)。 -/
lemma Qx0_sub_M (j : ℕ) (hj : 1 ≤ j) :
    (Qsel j : ℝ) * x0 - (Mseq j : ℝ) = (Qsel j : ℝ) * (x0 - r j) := by
  have hQ : (Qsel j : ℝ) ≠ 0 := by
    have := Qsel_pos j hj; positivity
  simp only [r]
  field_simp

/-- 0 ≤ Q_j x0 − M_j（尾和非负，因 W>0）。 -/
lemma Qx0_sub_M_nonneg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ (Qsel j : ℝ) * x0 - (Mseq j : ℝ) := by
  rw [Qx0_sub_M j hj]
  have hQ : (0 : ℝ) ≤ (Qsel j : ℝ) := by exact_mod_cast le_of_lt (Qsel_pos j hj)
  apply mul_nonneg hQ
  -- x0 − r_j = ∑' d(·+j) ≥ 0，因 d_k = W_k/(Q_kQ_{k+1}) > 0（k≥1）
  rw [x0_sub_r]
  apply tsum_nonneg
  intro i
  have hk : 1 ≤ i + j := by omega
  have hdpos : 0 ≤ d (i + j) := by
    have hW := Wseq_pos (i + j) hk
    have hQ1 : (0 : ℝ) < (Qsel (i + j) : ℝ) := by exact_mod_cast Qsel_pos (i + j) hk
    have hQ2 : (0 : ℝ) < (Qsel (i + j + 1) : ℝ) := by exact_mod_cast Qsel_pos (i + j + 1) (by omega)
    have hrw : d (i + j) = (Wseq (i + j) : ℝ) / ((Qsel (i + j) : ℝ) * (Qsel (i + j + 1) : ℝ)) := by
      simp only [d, r]
      exact ratio_diff (i + j) hk
    rw [hrw]
    apply div_nonneg
    · exact_mod_cast le_of_lt hW
    · exact le_of_lt (mul_pos hQ1 hQ2)
  exact hdpos

/-- **ε 界**：|Q_j x0 − M_j| ≤ 1/(2j)（j≥1）。 -/
lemma eps_bound (j : ℕ) (hj : 1 ≤ j) :
    |(Qsel j : ℝ) * x0 - (Mseq j : ℝ)| ≤ 1 / (2 * (j : ℝ)) := by
  have hnn := Qx0_sub_M_nonneg j hj
  rw [abs_of_nonneg hnn, Qx0_sub_M j hj]
  have hQ : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have htail := x0_sub_r_le j hj
  have hfour := Qsel_succ_ge_four j hj
  have hfourR : (4 * (j : ℝ)) * (Qsel j : ℝ) ≤ (Qsel (j + 1) : ℝ) := by exact_mod_cast hfour
  have hQ1 : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  calc (Qsel j : ℝ) * (x0 - r j)
      ≤ (Qsel j : ℝ) * (2 / (Qsel (j + 1) : ℝ)) := by gcongr
    _ = 2 * (Qsel j : ℝ) / (Qsel (j + 1) : ℝ) := by ring
    _ ≤ 2 * (Qsel j : ℝ) / (4 * (j : ℝ) * (Qsel j : ℝ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hfourR
    _ = 1 / (2 * (j : ℝ)) := by field_simp; ring

/-- **GAP2 舍入一致**：j≥2 时 round(Q_j x0) = M_j。 -/
lemma round_eq_M (j : ℕ) (hj : 2 ≤ j) :
    round ((Qsel j : ℝ) * x0) = Mseq j := by
  have hj1 : 1 ≤ j := by omega
  have hb := eps_bound j hj1
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hj2R : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hsmall : 1 / (2 * (j : ℝ)) < 1 / 2 := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith [hj2R]
  have habs : |(Qsel j : ℝ) * x0 - (Mseq j : ℝ)| < 1 / 2 := lt_of_le_of_lt hb hsmall
  have hnn := Qx0_sub_M_nonneg j hj1
  rw [abs_of_nonneg hnn] at habs
  rw [round_eq_iff]
  constructor
  · linarith
  · linarith

/-- **defect ≡ 1**（j≥3，最终）。 -/
lemma defect_eventually_one : ∀ᶠ j in atTop, defect x0 j = 1 := by
  filter_upwards [eventually_ge_atTop 3] with j hj
  have h1 : round ((Qsel (j + 1) : ℝ) * x0) = Mseq (j + 1) := round_eq_M (j + 1) (by omega)
  have h2 : round ((Qsel j : ℝ) * x0) = Mseq j := round_eq_M j (by omega)
  have h3 : round ((Qsel (j - 1) : ℝ) * x0) = Mseq (j - 1) := round_eq_M (j - 1) (by omega)
  unfold defect nearestInt
  rw [h1, h2, h3]
  -- M_{j+1} − (4j+2)M_j − M_{j−1} = 1
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have hs : k + 2 - 1 = k + 1 := by omega
  rw [hs, Mseq_rec]
  ring

/-- ε_j(x0) → 0（|ε|≤1/(2j)→0）。 -/
lemma eps_tendsto_zero : Tendsto (eps x0) atTop (nhds 0) := by
  have hb : ∀ᶠ j in atTop, |eps x0 j| ≤ 1 / (2 * (j : ℝ)) := by
    filter_upwards [eventually_ge_atTop 3] with j hj
    have hr := round_eq_M j (by omega)
    simp only [eps, nearestInt, hr]
    exact eps_bound j (by omega)
  have hz : Tendsto (fun j : ℕ => 1 / (2 * (j : ℝ))) atTop (nhds 0) := by
    have h : (fun j : ℕ => 1 / (2 * (j : ℝ))) = (fun j : ℕ => (1 / 2 : ℝ) / (j : ℝ)) := by
      funext k; ring
    rw [h]
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hneg : Tendsto (fun j : ℕ => -(1 / (2 * (j : ℝ)))) atTop (nhds 0) := by
    have := hz.neg; simpa using this
  have hlo : ∀ᶠ (j : ℕ) in atTop, -(1 / (2 * (j : ℝ))) ≤ eps x0 j := by
    filter_upwards [hb] with (j : ℕ) hj
    exact (abs_le.mp hj).1
  have hhi : ∀ᶠ (j : ℕ) in atTop, eps x0 j ≤ 1 / (2 * (j : ℝ)) := by
    filter_upwards [hb] with (j : ℕ) hj
    exact (abs_le.mp hj).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hz hlo hhi

/-- **主定理：Λ(x0) = 1/4**（阈值可达）。 -/
theorem lambda_x0_eq_quarter :
    Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x0))
      atTop (nhds (1 / 4 : ℝ)) :=
  ThresholdAttained.apprSeq_tendsto_quarter x0 defect_eventually_one eps_tendsto_zero

end

end QuarterPointFinal

#print axioms QuarterPointFinal.eps_bound
#print axioms QuarterPointFinal.round_eq_M
#print axioms QuarterPointFinal.defect_eventually_one
#print axioms QuarterPointFinal.eps_tendsto_zero
#print axioms QuarterPointFinal.lambda_x0_eq_quarter
