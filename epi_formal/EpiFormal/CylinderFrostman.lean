import Mathlib

open MeasureTheory Set Filter Finset ENNReal Metric
open scoped NNReal BigOperators Topology MeasureTheory

namespace Cylinder

noncomputable section

/-- `0 < s ≤ 1` 时次可加性：`(a + b)^s ≤ a^s + b^s`（Frostman 直径分裂用）。 -/
lemma rpow_add_le_add_rpow {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (a + b) ^ s ≤ a ^ s + b ^ s := by
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    rw [ha0, hb0, add_zero, Real.zero_rpow (ne_of_gt hs0), add_zero]
  · have hpos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
    have hp : 0 < (a + b) ^ s := Real.rpow_pos_of_pos hpos s
    have ha_le : a / (a + b) ≤ 1 := (div_le_one hpos).mpr (by linarith)
    have hb_le : b / (a + b) ≤ 1 := (div_le_one hpos).mpr (by linarith)
    have ha_nn : 0 ≤ a / (a + b) := div_nonneg ha (le_of_lt hpos)
    have hb_nn : 0 ≤ b / (a + b) := div_nonneg hb (le_of_lt hpos)
    have h1 : a / (a + b) ≤ (a / (a + b)) ^ s := by
      by_cases ha0 : a = 0
      · simp [ha0, Real.zero_rpow (ne_of_gt hs0)]
      · calc a / (a + b) = (a / (a + b)) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (a / (a + b)) ^ s := Real.rpow_le_rpow_of_exponent_ge (div_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hpos) ha_le hs1
    have h2 : b / (a + b) ≤ (b / (a + b)) ^ s := by
      by_cases hb0 : b = 0
      · simp [hb0, Real.zero_rpow (ne_of_gt hs0)]
      · calc b / (a + b) = (b / (a + b)) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (b / (a + b)) ^ s := Real.rpow_le_rpow_of_exponent_ge (div_pos (lt_of_le_of_ne hb (Ne.symm hb0)) hpos) hb_le hs1
    have hsum : (1 : ℝ) ≤ (a / (a + b)) ^ s + (b / (a + b)) ^ s := by
      have hdiv : a / (a + b) + b / (a + b) = 1 := by field_simp
      linarith
    have hmul := mul_le_mul_of_nonneg_right hsum (le_of_lt hp)
    rw [one_mul, add_mul, Real.div_rpow ha (le_of_lt hpos) s, Real.div_rpow hb (le_of_lt hpos) s,
      div_mul_cancel₀ _ (ne_of_gt hp), div_mul_cancel₀ _ (ne_of_gt hp)] at hmul
    exact hmul

/-- 开膨胀直径上界（ℝ 半径版，包装 mathlib 的 NNReal 版）。 -/
lemma ediam_thickening_le {A : Set ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Metric.ediam (Metric.thickening ρ A) ≤ Metric.ediam A + 2 * ENNReal.ofReal ρ := by
  rw [Metric.ediam_le_iff]
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := Metric.mem_thickening_iff.mp hx
  obtain ⟨b, hb, hyb⟩ := Metric.mem_thickening_iff.mp hy
  have h1 : edist x a ≤ ENNReal.ofReal ρ := by
    rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (le_of_lt hxa)
  have h2 : edist b y ≤ ENNReal.ofReal ρ := by
    rw [edist_comm, edist_dist]; exact ENNReal.ofReal_le_ofReal (le_of_lt hyb)
  have h3 : edist a b ≤ Metric.ediam A := Metric.edist_le_ediam_of_mem ha hb
  calc edist x y ≤ edist x a + edist a b + edist b y := edist_triangle4 x a b y
    _ ≤ ENNReal.ofReal ρ + Metric.ediam A + ENNReal.ofReal ρ := by gcongr
    _ = Metric.ediam A + 2 * ENNReal.ofReal ρ := by ring

set_option maxHeartbeats 800000 in
/-- Frostman 通用核心：紧集 K 上，若每个有限开覆盖都有重数受控的计数下界
（接口 `Hinter`，由计数应用方 discharge），则 `s` 维 Hausdorff 测度 `≥ 1`。
骨架 = S1（反设）→ S2（开膨胀）→ S3（有限子覆盖）→ 接口 → S8（分裂/级数）→ S9（矛盾）。 -/
theorem frostman_of_count_thresh
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hK : IsCompact K)
    (r0R : ℝ) (hr0R : 0 < r0R)
    (Hinter : ∀ (ι : Type) (V : ι → Set ℝ) (F : Finset ι),
      (∀ i, IsOpen (V i)) → K ⊆ ⋃ i ∈ F, V i →
      ∃ (Kc : ι → ℕ) (M : ℝ), 0 < M ∧
        (1 : ℝ) ≤ ∑ i ∈ F, ((Kc i : ℝ) / M) ∧
        (∀ i ∈ F, ((Kc i : ℝ) / M) ≤ (Metric.diam (V i)) ^ s))
    : 1 ≤ MeasureTheory.Measure.hausdorffMeasure s K := by
  set r0 : ℝ≥0∞ := ENNReal.ofReal r0R with hr0def
  have hr0 : 0 < r0 := by rw [hr0def]; exact ENNReal.ofReal_pos.mpr hr0R
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine le_trans ?_ (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
    ⨅ (t : ℕ → Set ℝ) (_ : K ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s) r0 hr0)
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
  by_contra hlt
  push_neg at hlt
  set S : ℝ≥0∞ := ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s with hSdef
  have hS_ne_top : S ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hlt le_top)
  have hSR_lt : S.toReal < 1 := by
    have h1 := (ENNReal.toReal_lt_toReal hS_ne_top ENNReal.one_ne_top).mpr hlt
    simpa using h1
  set δ0 : ℝ := (1 - S.toReal) / 2 with hδ0def
  have hδ0 : 0 < δ0 := by linarith
  -- S2：开膨胀
  let ρ : ℕ → ℝ := fun i => ((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s)) / 2
  have hρ_pos : ∀ i, 0 < ρ i := fun i => by
    have hpos1 : 0 < δ0 / (2 : ℝ) ^ (i + 1) := by positivity
    have hpos2 : 0 < (δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) := Real.rpow_pos_of_pos hpos1 (1 / s)
    have h : ρ i = ((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s)) / 2 := rfl
    rw [h]; linarith
  have h2ρ_rpow : ∀ i, (2 * ρ i) ^ s ≤ δ0 / (2 : ℝ) ^ (i + 1) := fun i => by
    have hpos1 : 0 < δ0 / (2 : ℝ) ^ (i + 1) := by positivity
    have h1 : 2 * ρ i = (δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) := by
      have h : ρ i = ((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s)) / 2 := rfl
      rw [h]; ring
    calc (2 * ρ i) ^ s
        ≤ (((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s)) ^ s) :=
          Real.rpow_le_rpow (by linarith [hρ_pos i]) h1.le (le_of_lt hs0)
      _ = (δ0 / (2 : ℝ) ^ (i + 1)) ^ ((1 / s) * s) :=
          (Real.rpow_mul (le_of_lt hpos1) (1 / s) s).symm
      _ = δ0 / (2 : ℝ) ^ (i + 1) := by rw [one_div_mul_cancel (ne_of_gt hs0), Real.rpow_one]
  let V : ℕ → Set ℝ := fun i => Metric.thickening (ρ i) (t i)
  have hV_open : ∀ i, IsOpen (V i) := fun i => Metric.isOpen_thickening
  have hV_cov : K ⊆ ⋃ i : {i : ℕ // (t i).Nonempty}, V i.1 := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    refine Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, ?_⟩
    exact Metric.self_subset_thickening (hρ_pos i) (t i) hi
  -- S3：有限子覆盖
  obtain ⟨F, hFcov⟩ := hK.elim_finite_subcover
    (fun i : {i : ℕ // (t i).Nonempty} => V i.1) (fun i => hV_open i.1) hV_cov
  -- 接口：计数下界 + 阈值桥
  obtain ⟨Kc, M, hM, Hcount, Hthresh⟩ := Hinter _
    (fun i : {i : ℕ // (t i).Nonempty} => V i.1) F (fun i => hV_open i.1) hFcov
  -- S8a：逐点分裂界
  have hdiam_bound : ∀ i ∈ F, Metric.diam (V i.1) ^ s ≤
      (Metric.ediam (t i.1) ^ s).toReal + δ0 / (2 : ℝ) ^ (i.1 + 1) := by
    intro i _
    have ht_ne_top : Metric.ediam (t i.1) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (hdiam i.1) ENNReal.ofReal_lt_top)
    have hdiam_le_add : Metric.diam (V i.1) ≤ (Metric.ediam (t i.1)).toReal + 2 * ρ i.1 := by
      unfold Metric.diam
      have h1 : Metric.ediam (V i.1) ≤ Metric.ediam (t i.1) + ENNReal.ofReal (2 * ρ i.1) := by
        have h2 : 2 * ENNReal.ofReal (ρ i.1) = ENNReal.ofReal (2 * ρ i.1) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
        rw [← h2]
        exact ediam_thickening_le (le_of_lt (hρ_pos i.1))
      have htop : Metric.ediam (t i.1) + ENNReal.ofReal (2 * ρ i.1) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨ht_ne_top, ENNReal.ofReal_ne_top⟩
      have htoR := ENNReal.toReal_mono htop h1
      rw [ENNReal.toReal_add ht_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by linarith [hρ_pos i.1])] at htoR
      exact htoR
    have hpow_le : Metric.diam (V i.1) ^ s ≤
        (Metric.ediam (t i.1)).toReal ^ s + (2 * ρ i.1) ^ s := by
      calc Metric.diam (V i.1) ^ s
          ≤ ((Metric.ediam (t i.1)).toReal + 2 * ρ i.1) ^ s :=
            Real.rpow_le_rpow Metric.diam_nonneg hdiam_le_add (le_of_lt hs0)
        _ ≤ (Metric.ediam (t i.1)).toReal ^ s + (2 * ρ i.1) ^ s :=
            rpow_add_le_add_rpow ENNReal.toReal_nonneg (by linarith [hρ_pos i.1]) hs0 hs1
    have htoR_rpow : (Metric.ediam (t i.1)).toReal ^ s = (Metric.ediam (t i.1) ^ s).toReal :=
      ENNReal.toReal_rpow (Metric.ediam (t i.1)) s
    rw [htoR_rpow] at hpow_le
    linarith [h2ρ_rpow i.1]
  -- S8b：有限和 vs 级数
  have hsum_t : ∑ i ∈ F, (Metric.ediam (t i.1) ^ s).toReal ≤ S.toReal := by
    let G : Finset ℕ := F.image Subtype.val
    have hG_eq : ∑ i ∈ F, (Metric.ediam (t i.1) ^ s).toReal =
        ∑ n ∈ G, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s).toReal := by
      rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
      apply Finset.sum_congr rfl
      intro i _
      simp [i.2]
    rw [hG_eq]
    have hleE : ∑ n ∈ G, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s) ≤ S :=
      ENNReal.sum_le_tsum G
    have hsum_ne_top : ∀ n ∈ G, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s) ≠ ⊤ := by
      intro n hn
      have hle := le_trans (Finset.single_le_sum (fun _ _ => bot_le) hn) hleE
      exact ne_of_lt (lt_of_le_of_lt hle (lt_of_lt_of_le hlt le_top))
    rw [← ENNReal.toReal_sum hsum_ne_top]
    exact ENNReal.toReal_mono hS_ne_top hleE
  -- S8c：几何级数
  have hsum_geom : ∑ i ∈ F, δ0 / (2 : ℝ) ^ (i.1 + 1) ≤ δ0 := by
    let G : Finset ℕ := F.image Subtype.val
    have hG_eq : ∑ i ∈ F, δ0 / (2 : ℝ) ^ (i.1 + 1) = ∑ n ∈ G, δ0 * ((1 / 2 : ℝ) ^ (n + 1)) := by
      rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
      apply Finset.sum_congr rfl
      intro i _
      rw [one_div, inv_pow, div_eq_mul_inv]
    rw [hG_eq, ← Finset.mul_sum]
    have hgeom : ∑ n ∈ G, ((1 / 2 : ℝ) ^ (n + 1)) ≤ 1 := by
      have hsumm : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
        have h1 := summable_geometric_two
        have h2 : (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) = fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
          funext n; rw [pow_succ']
        rw [h2]; exact h1.mul_left _
      have hle := hsumm.sum_le_tsum G (fun _ _ => by positivity)
      have htsum : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = 1 := by
        have h2 : (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) = fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
          funext n; rw [pow_succ']
        rw [h2, tsum_mul_left, tsum_geometric_two]; norm_num
      linarith
    nlinarith
  -- S9：矛盾
  have htotal_lt : ∑ i ∈ F, Metric.diam (V i.1) ^ s < 1 := by
    calc ∑ i ∈ F, Metric.diam (V i.1) ^ s
        ≤ ∑ i ∈ F, ((Metric.ediam (t i.1) ^ s).toReal + δ0 / (2 : ℝ) ^ (i.1 + 1)) :=
          Finset.sum_le_sum hdiam_bound
      _ = (∑ i ∈ F, (Metric.ediam (t i.1) ^ s).toReal) + ∑ i ∈ F, δ0 / (2 : ℝ) ^ (i.1 + 1) :=
          Finset.sum_add_distrib
      _ ≤ S.toReal + δ0 := add_le_add hsum_t hsum_geom
      _ < 1 := by linarith
  have hle : ∑ i ∈ F, ((Kc i : ℝ) / M) ≤ ∑ i ∈ F, (Metric.diam (V i.1)) ^ s :=
    Finset.sum_le_sum (fun i hi => Hthresh i hi)
  linarith [Hcount, hle, htotal_lt]

/-- Frostman 推论：计数/阈值接口成立 ⇒ `ENNReal.ofReal s ≤ dimH K`。 -/
theorem frostman_dimH_le
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hK : IsCompact K)
    (r0R : ℝ) (hr0R : 0 < r0R)
    (Hinter : ∀ (ι : Type) (V : ι → Set ℝ) (F : Finset ι),
      (∀ i, IsOpen (V i)) → K ⊆ ⋃ i ∈ F, V i →
      ∃ (Kc : ι → ℕ) (M : ℝ), 0 < M ∧
        (1 : ℝ) ≤ ∑ i ∈ F, ((Kc i : ℝ) / M) ∧
        (∀ i ∈ F, ((Kc i : ℝ) / M) ≤ (Metric.diam (V i)) ^ s))
    : ENNReal.ofReal s ≤ dimH K := by
  have hmu : 1 ≤ μH[s] K :=
    frostman_of_count_thresh hs0 hs1 hK r0R hr0R Hinter
  have hmu_ne : μH[s] K ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hmu)
  set d : ℝ≥0 := ⟨s, le_of_lt hs0⟩
  have hdimK : (d : ℝ≥0∞) ≤ dimH K :=
    le_dimH_of_hausdorffMeasure_ne_zero hmu_ne
  have hd_eq : (d : ℝ≥0∞) = ENNReal.ofReal s := by
    simp only [d, ENNReal.ofReal]
    congr 1
    exact (Real.toNNReal_of_nonneg (le_of_lt hs0)).symm
  rw [hd_eq] at hdimK
  exact hdimK

end

end Cylinder

#print axioms Cylinder.rpow_add_le_add_rpow
#print axioms Cylinder.ediam_thickening_le
#print axioms Cylinder.frostman_of_count_thresh
#print axioms Cylinder.frostman_dimH_le
