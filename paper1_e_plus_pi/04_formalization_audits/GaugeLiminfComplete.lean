import EpiFormal.GaugeCircle

/-! Staged Lean verification for the oscillating-gauge corollaries. -/

open Filter Topology Set MeasureTheory Classification SpectralGap GaugeNull GaugeExact
open scoped ENNReal

namespace GaugeLiminf

noncomputable section

def gaugeScale (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (Qsel n : ℝ))

def normalizedGaugeCost (b : ℕ) (g : ℝ≥0∞ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ((b ^ n : ℕ) : ℝ≥0∞) * g (gaugeScale n)

/-- An upper bound from covers with at most b^n members at radius 1/Q_(N+n). -/
private theorem mkMetric_le_liminf_of_covers (S : Set ℝ) (N b : ℕ) (hb : 1 ≤ b)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (ι : ℕ → Type) [∀ n, Fintype (ι n)] (cov : ∀ n, ι n → Set ℝ)
    (hcover : ∀ n, S ⊆ ⋃ p : ι n, cov n p)
    (hdiam : ∀ n (p : ι n), Metric.ediam (cov n p) ≤ gaugeScale (N + n))
    (hcard : ∀ n, Fintype.card (ι n) ≤ b ^ n) :
    Measure.mkMetric g S ≤ liminf (normalizedGaugeCost b g) atTop := by
  have hmain := Measure.mkMetric_le_liminf_sum S
    (fun n => gaugeScale (N + n)) (tendsto_inv_Qsel_shift N) cov
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover) g
  have hsum : ∀ n, (∑ p : ι n, g (Metric.ediam (cov n p))) ≤
      normalizedGaugeCost b g (N + n) := by
    intro n
    calc
      ∑ p : ι n, g (Metric.ediam (cov n p))
          ≤ ∑ _p : ι n, g (gaugeScale (N + n)) :=
        Finset.sum_le_sum (fun p _ => hg (hdiam n p))
      _ = (Fintype.card (ι n) : ℝ≥0∞) * g (gaugeScale (N + n)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ normalizedGaugeCost b g (N + n) := by
        apply mul_le_mul_of_nonneg_right _ bot_le
        exact_mod_cast (hcard n).trans (Nat.pow_le_pow_right (by omega) (by omega))
  calc
    Measure.mkMetric g S ≤
        liminf (fun n => ∑ p : ι n, g (Metric.ediam (cov n p))) atTop := hmain
    _ ≤ liminf (fun n => normalizedGaugeCost b g (N + n)) atTop :=
      liminf_le_liminf (Eventually.of_forall hsum)
    _ = liminf (normalizedGaugeCost b g) atTop := by
      simpa only [Nat.add_comm N] using liminf_nat_add (normalizedGaugeCost b g) N

theorem mkMetric_digitClass_le_liminf (k N : ℕ) (m₀ m₁ : ℤ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g) :
    Measure.mkMetric g (digitClass k N m₀ m₁) ≤
      liminf (normalizedGaugeCost (2 * k + 1) g) atTop := by
  let ι (n : ℕ) := {p // p ∈ pairTree k N m₀ m₁ n}
  apply mkMetric_le_liminf_of_covers _ N (2 * k + 1) (by omega) g hg ι
    (fun n p => gaugeInterv (N + n) p.1.1)
  · exact digitClass_cover k N m₀ m₁
  · exact fun n p => ediam_gaugeInterv_le (N + n) p.1.1
  · intro n
    simpa [ι] using card_pairTree_le k N m₀ m₁ n

theorem mkMetric_binaryDigitClass_le_liminf (k N : ℕ) (m₀ m₁ : ℤ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g) :
    Measure.mkMetric g (binaryDigitClass k N m₀ m₁) ≤
      liminf (normalizedGaugeCost 2 g) atTop := by
  let ι (n : ℕ) := {p // p ∈ binaryPairTree k N m₀ m₁ n}
  apply mkMetric_le_liminf_of_covers _ N 2 (by omega) g hg ι
    (fun n p => gaugeInterv (N + n) p.1.1)
  · exact binaryDigitClass_cover k N m₀ m₁
  · exact fun n p => ediam_gaugeInterv_le (N + n) p.1.1
  · intro n
    simpa [ι] using card_binaryPairTree_le k N m₀ m₁ n

theorem mkMetric_levelSet_null_of_liminf_zero (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hzero : liminf (normalizedGaugeCost (2 * k + 1) g) atTop = 0) :
    Measure.mkMetric g {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} = 0 := by
  apply measure_mono_null (levelSet_quarter_subset_iUnion_digitClass k)
  apply measure_iUnion_digitClass_null k (Measure.mkMetric g)
  intro N _ m₀ m₁
  exact le_antisymm ((mkMetric_digitClass_le_liminf k N m₀ m₁ g hg).trans_eq hzero) bot_le

theorem mkMetric_unsignedExactLimit_null_of_liminf_zero (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hzero : liminf (normalizedGaugeCost 2 g) atTop = 0) :
    Measure.mkMetric g (unsignedExactLimitSet k) = 0 := by
  apply measure_mono_null (unsignedExactLimitSet_subset_iUnion_binaryDigitClass k)
  apply measure_iUnion_null
  intro N
  apply measure_iUnion_null
  intro m₀
  apply measure_iUnion_null
  intro m₁
  exact le_antisymm ((mkMetric_binaryDigitClass_le_liminf k N.1 m₀ m₁ g hg).trans_eq hzero) bot_le

theorem levelSet_countable_cover_of_liminf_lt_top (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hfinite : liminf (normalizedGaugeCost (2 * k + 1) g) atTop < ⊤) :
    ∃ E : ({N : ℕ // 1 ≤ N} × ℤ × ℤ) → Set ℝ,
      {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  refine ⟨fun i => digitClass k i.1.1 i.2.1 i.2.2, ?_, ?_⟩
  · intro x hx
    have hmem := levelSet_quarter_subset_iUnion_digitClass k hx
    rcases Set.mem_iUnion.mp hmem with ⟨N, h1⟩
    rcases Set.mem_iUnion.mp h1 with ⟨m₀, h2⟩
    rcases Set.mem_iUnion.mp h2 with ⟨m₁, h3⟩
    exact Set.mem_iUnion.mpr ⟨(N, m₀, m₁), h3⟩
  · intro i
    exact (mkMetric_digitClass_le_liminf k i.1.1 i.2.1 i.2.2 g hg).trans_lt hfinite

theorem unsignedExactLimit_countable_cover_of_liminf_lt_top (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hfinite : liminf (normalizedGaugeCost 2 g) atTop < ⊤) :
    ∃ E : ({N : ℕ // 1 ≤ N} × ℤ × ℤ) → Set ℝ,
      unsignedExactLimitSet k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  refine ⟨fun i => binaryDigitClass k i.1.1 i.2.1 i.2.2, ?_, ?_⟩
  · intro x hx
    have hmem := unsignedExactLimitSet_subset_iUnion_binaryDigitClass k hx
    rcases Set.mem_iUnion.mp hmem with ⟨N, h1⟩
    rcases Set.mem_iUnion.mp h1 with ⟨m₀, h2⟩
    rcases Set.mem_iUnion.mp h2 with ⟨m₁, h3⟩
    exact Set.mem_iUnion.mpr ⟨(N, m₀, m₁), h3⟩
  · intro i
    exact (mkMetric_binaryDigitClass_le_liminf k i.1.1 i.2.1 i.2.2 g hg).trans_lt hfinite

end

end GaugeLiminf

#print axioms GaugeLiminf.mkMetric_digitClass_le_liminf
#print axioms GaugeLiminf.mkMetric_binaryDigitClass_le_liminf
#print axioms GaugeLiminf.mkMetric_levelSet_null_of_liminf_zero
#print axioms GaugeLiminf.mkMetric_unsignedExactLimit_null_of_liminf_zero
#print axioms GaugeLiminf.levelSet_countable_cover_of_liminf_lt_top
#print axioms GaugeLiminf.unsignedExactLimit_countable_cover_of_liminf_lt_top


open Filter Topology Set MeasureTheory GaugeNull GaugeExact
open scoped ENNReal NNReal

namespace GaugeScaleComparison

noncomputable section

def scale (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / (Qsel n : ℝ))

/-- Monotonicity extends comparisons between consecutive endpoints to every small radius. -/
theorem small_radius_le_of_adjacent_scale_le
    (h g : ℝ≥0∞ → ℝ≥0∞) (hh : Monotone h) (hg : Monotone g) (hzero : h 0 = 0)
    (N : ℕ) (c : ℝ≥0∞)
    (hle : ∀ n ≥ N, h (scale n) ≤ c * g (scale (n + 1))) :
    ∀ r ≤ scale N, h r ≤ c * g r := by
  intro r hrN
  by_cases hr : r = 0
  · subst r
    rw [hzero]
    exact bot_le
  have ht : Tendsto (fun m => scale (N + 1 + m)) atTop (nhds 0) :=
    tendsto_inv_Qsel_shift (N + 1)
  have hex : ∃ m, scale (N + 1 + m) < r :=
    ((tendsto_order.1 ht).2 r (pos_iff_ne_zero.mpr hr)).exists
  let m := Nat.find hex
  have hright : scale (N + m + 1) ≤ r := by
    have hspec := Nat.find_spec hex
    change scale (N + 1 + m) < r at hspec
    simpa only [Nat.add_right_comm N m 1] using hspec.le
  have hleft : r ≤ scale (N + m) := by
    cases hcase : m with
    | zero => simpa [hcase] using hrN
    | succ i =>
      have hi : i < Nat.find hex := by
        change i < m
        omega
      have hmin := le_of_not_gt (Nat.find_min hex hi)
      have heq : N + (i + 1) = N + 1 + i := by omega
      simpa only [Nat.succ_eq_add_one, heq] using hmin
  exact (hh hleft).trans ((hle (N + m) (by omega)).trans
    (mul_le_mul_of_nonneg_left (hg hright) bot_le))

theorem not_countable_union_finite_of_adjacent_scale_ratio
    (h g : ℝ≥0∞ → ℝ≥0∞) (hh : Monotone h) (hg : Monotone g) (hzero : h 0 = 0)
    (hratio : ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ,
      ∀ n ≥ N, h (scale n) ≤ (ε : ℝ≥0∞) * g (scale (n + 1)))
    {S : Set ℝ} (hpos : 0 < Measure.mkMetric h S) :
    Measure.mkMetric g S = ⊤ ∧
    ¬ ∃ E : ℕ → Set ℝ, S ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  apply not_countable_union_finite_of_ratio_tendsto_zero h g _ hpos
  intro ε hε
  obtain ⟨N, hN⟩ := hratio ε hε
  have hNpos : 0 < scale N := by
    apply ENNReal.ofReal_pos.mpr
    exact one_div_pos.mpr (by exact_mod_cast Classification.Qsel_pos N)
  exact ⟨scale N, hNpos, small_radius_le_of_adjacent_scale_le h g hh hg hzero N ε hN⟩

end

end GaugeScaleComparison

#print axioms GaugeScaleComparison.small_radius_le_of_adjacent_scale_le
#print axioms GaugeScaleComparison.not_countable_union_finite_of_adjacent_scale_ratio


open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace GaugeScaleComparison

noncomputable section

private theorem adjacent_bound_of_normalized_lower (b : ℕ) (hb : 0 < b)
    (h g : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hc : 0 < c)
    (n : ℕ) (hn : h (scale n) ≤ ((b ^ n : ℕ) : ℝ≥0∞)⁻¹)
    (hlower : (b : ℝ≥0∞) / (c : ℝ≥0∞) ≤
      GaugeLiminf.normalizedGaugeCost b g (n + 1)) :
    h (scale n) ≤ (c : ℝ≥0∞) * g (scale (n + 1)) := by
  let p : ℝ≥0∞ := ((b ^ n : ℕ) : ℝ≥0∞)
  let q : ℝ≥0∞ := ((b ^ (n + 1) : ℕ) : ℝ≥0∞)
  have hp0 : p ≠ 0 := by
    have hpos : 0 < p := by
      dsimp only [p]
      exact_mod_cast (Nat.pow_pos (n := n) hb)
    exact hpos.ne'
  have hpT : p ≠ ⊤ := by simp [p]
  have hq0 : q ≠ 0 := by
    have hpos : 0 < q := by
      dsimp only [q]
      exact_mod_cast (Nat.pow_pos (n := n + 1) hb)
    exact hpos.ne'
  have hqT : q ≠ ⊤ := by simp [q]
  have hq : q = (b : ℝ≥0∞) * p := by
    simp [p, q, pow_succ']
  have hproduct : (b : ℝ≥0∞) ≤
      (c : ℝ≥0∞) * (q * g (scale (n + 1))) :=
    (ENNReal.div_le_iff' (by exact_mod_cast hc.ne') (by simp)).mp hlower
  have hmul : q * p⁻¹ ≤ q * ((c : ℝ≥0∞) * g (scale (n + 1))) := by
    calc
      q * p⁻¹ = (b : ℝ≥0∞) := by
        rw [hq, mul_assoc, ENNReal.mul_inv_cancel hp0 hpT, mul_one]
      _ ≤ (c : ℝ≥0∞) * (q * g (scale (n + 1))) := hproduct
      _ = q * ((c : ℝ≥0∞) * g (scale (n + 1))) := by ac_rfl
  have hcancel := mul_le_mul_of_nonneg_left hmul (show 0 ≤ q⁻¹ from bot_le)
  rw [ENNReal.inv_mul_cancel_left hq0 hqT, ENNReal.inv_mul_cancel_left hq0 hqT] at hcancel
  exact hn.trans hcancel

theorem exists_small_radius_comparison_of_lt_liminf (b : ℕ) (hb : 0 < b)
    (h g : ℝ≥0∞ → ℝ≥0∞) (hh : Monotone h) (hg : Monotone g) (hzero : h 0 = 0)
    (hcal : ∀ n ≥ 1, h (scale n) ≤ ((b ^ n : ℕ) : ℝ≥0∞)⁻¹)
    (c : ℝ≥0) (hc : 0 < c)
    (hlim : (b : ℝ≥0∞) / (c : ℝ≥0∞) <
      liminf (GaugeLiminf.normalizedGaugeCost b g) atTop) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ r ≤ δ, h r ≤ (c : ℝ≥0∞) * g r := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hlim)
  let N' := max N 1
  have hNpos : 0 < scale N' := by
    apply ENNReal.ofReal_pos.mpr
    exact one_div_pos.mpr (by exact_mod_cast Classification.Qsel_pos N')
  refine ⟨scale N', hNpos, small_radius_le_of_adjacent_scale_le h g hh hg hzero N' c ?_⟩
  intro n hn
  exact adjacent_bound_of_normalized_lower b hb h g c hc n (hcal n (by omega))
    (hN (n + 1) (by omega)).le

theorem exists_small_radius_comparison_of_liminf_pos (b : ℕ) (hb : 0 < b)
    (h g : ℝ≥0∞ → ℝ≥0∞) (hh : Monotone h) (hg : Monotone g) (hzero : h 0 = 0)
    (hcal : ∀ n ≥ 1, h (scale n) ≤ ((b ^ n : ℕ) : ℝ≥0∞)⁻¹)
    (hlim : 0 < liminf (GaugeLiminf.normalizedGaugeCost b g) atTop)
    : ∃ (c : ℝ≥0) (δ : ℝ≥0∞), 0 < δ ∧
      ∀ r ≤ δ, h r ≤ (c : ℝ≥0∞) * g r := by
  obtain ⟨a, ha, halim⟩ := exists_between hlim
  have haT : a ≠ ⊤ := (halim.trans_le le_top).ne
  let d : ℝ≥0∞ := (b : ℝ≥0∞) * a⁻¹
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb.ne'
  have hd : d ≠ ⊤ := by
    exact (ENNReal.mul_lt_top (by simp) (ENNReal.inv_lt_top.mpr ha)).ne
  have hd0 : d ≠ 0 := mul_ne_zero hb0 (ENNReal.inv_ne_zero.mpr haT)
  let c := d.toNNReal
  have hcE : (c : ℝ≥0∞) = d := ENNReal.coe_toNNReal hd
  have hc0 : 0 < c := by
    apply pos_iff_ne_zero.mpr
    intro h
    apply hd0
    simpa [h] using hcE.symm
  have hratio : (b : ℝ≥0∞) / (c : ℝ≥0∞) ≤ a := by
    rw [hcE]
    apply (ENNReal.div_le_iff hd0 hd).mpr
    change (b : ℝ≥0∞) ≤ a * ((b : ℝ≥0∞) * a⁻¹)
    rw [show a * ((b : ℝ≥0∞) * a⁻¹) = (b : ℝ≥0∞) * (a * a⁻¹) by ac_rfl,
      ENNReal.mul_inv_cancel ha.ne' haT, mul_one]
  obtain ⟨δ, hδ, hcomp⟩ :=
    exists_small_radius_comparison_of_lt_liminf b hb h g hh hg hzero hcal c hc0
      (hratio.trans_lt halim)
  exact ⟨c, δ, hδ, hcomp⟩

theorem mkMetric_eq_top_of_liminf_pos (b : ℕ) (hb : 0 < b)
    (h g : ℝ≥0∞ → ℝ≥0∞) (hh : Monotone h) (hg : Monotone g) (hzero : h 0 = 0)
    (hcal : ∀ n ≥ 1, h (scale n) ≤ ((b ^ n : ℕ) : ℝ≥0∞)⁻¹)
    (hlim : 0 < liminf (GaugeLiminf.normalizedGaugeCost b g) atTop)
    {S : Set ℝ} (hS : Measure.mkMetric h S = ⊤) : Measure.mkMetric g S = ⊤ := by
  obtain ⟨c, δ, hδ, hcomp⟩ :=
    exists_small_radius_comparison_of_liminf_pos b hb h g hh hg hzero hcal hlim
  by_contra hne
  have hbound := mkMetric_le_mul_of_eventually_le h g c hδ hcomp S
  rw [hS] at hbound
  exact (not_lt_of_ge hbound) (ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr hne))

theorem not_countable_union_finite_of_liminf_top (b : ℕ) (hb : 0 < b)
    (h g : ℝ≥0∞ → ℝ≥0∞) (hh : Monotone h) (hg : Monotone g) (hzero : h 0 = 0)
    (hcal : ∀ n ≥ 1, h (scale n) ≤ ((b ^ n : ℕ) : ℝ≥0∞)⁻¹)
    (hlim : liminf (GaugeLiminf.normalizedGaugeCost b g) atTop = ⊤)
    {S : Set ℝ} (hpos : 0 < Measure.mkMetric h S) :
    Measure.mkMetric g S = ⊤ ∧
    ¬ ∃ E : ℕ → Set ℝ, S ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  apply not_countable_union_finite_of_ratio_tendsto_zero h g _ hpos
  intro c hc
  apply exists_small_radius_comparison_of_lt_liminf b hb h g hh hg hzero hcal c hc
  rw [hlim]
  exact ENNReal.div_lt_top (by simp) (by exact_mod_cast hc.ne')

end

end GaugeScaleComparison

#print axioms GaugeScaleComparison.exists_small_radius_comparison_of_lt_liminf
#print axioms GaugeScaleComparison.not_countable_union_finite_of_liminf_top

#print axioms GaugeScaleComparison.mkMetric_eq_top_of_liminf_pos


namespace GaugeLiminf

open GaugeScaleComparison

noncomputable section

private theorem ofReal_zpow_neg_nat (b n : ℕ) (hb : 0 < b) :
    ENNReal.ofReal ((b : ℝ) ^ (-(n : ℤ))) = ((b ^ n : ℕ) : ℝ≥0∞)⁻¹ := by
  have hpos : 0 < (b : ℝ) := by exact_mod_cast hb
  rw [zpow_neg, zpow_natCast, ENNReal.ofReal_inv_of_pos (pow_pos hpos n),
    ENNReal.ofReal_pow hpos.le]
  simp

/-- A continuous calibrated reference gauge has infinite measure on the exact real level. -/
theorem calibrated_exactLevel_eq_top (k : ℕ) (hk : 1 ≤ k)
    (h : ℝ≥0∞ → ℝ≥0∞) (hh : Monotone h) (hcont : Continuous h)
    (hcal : ∀ n ≥ 1, h (scale n) = (((2 * k + 1) ^ n : ℕ) : ℝ≥0∞)⁻¹) :
    Measure.mkMetric h {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} = ⊤ := by
  let b : ℝ := 2 * (k : ℝ) + 1
  have hb : 0 < b := by positivity
  have hformula (n : ℕ) (hn : 1 ≤ n) :
      h (scale n) = ENNReal.ofReal (b ^ (-(n : ℤ))) := by
    rw [hcal n hn, ← ofReal_zpow_neg_nat (2 * k + 1) n (by omega)]
    simp [b]
  apply GaugeExact.mkMetric_exactLevel_eq_top k hk h hh hcont 1 b⁻¹ (inv_pos.mpr hb)
  · intro n hn
    exact (hformula n hn).le.trans_eq (by simp [b])
  · intro n
    change ENNReal.ofReal (b⁻¹ * b ^ (-(n : ℤ))) ≤ h (scale (n + 1))
    rw [hformula (n + 1) (by omega)]
    apply ENNReal.ofReal_le_ofReal
    apply Eq.le
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, pow_succ]
    field_simp

theorem exactLevel_eq_top_of_liminf_pos (k : ℕ) (hk : 1 ≤ k)
    (h g : ℝ≥0∞ → ℝ≥0∞) (hh : Monotone h) (hcont : Continuous h) (hzero : h 0 = 0)
    (hg : Monotone g)
    (hcal : ∀ n ≥ 1, h (scale n) = (((2 * k + 1) ^ n : ℕ) : ℝ≥0∞)⁻¹)
    (hlim : 0 < liminf (normalizedGaugeCost (2 * k + 1) g) atTop) :
    Measure.mkMetric g {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} = ⊤ :=
  mkMetric_eq_top_of_liminf_pos (2 * k + 1) (by omega) h g hh hg hzero
    (fun n hn => (hcal n hn).le) hlim
    (calibrated_exactLevel_eq_top k hk h hh hcont hcal)

theorem exactLevel_not_countable_union_finite_of_liminf_top (k : ℕ) (hk : 1 ≤ k)
    (h g : ℝ≥0∞ → ℝ≥0∞) (hh : Monotone h) (hcont : Continuous h) (hzero : h 0 = 0)
    (hg : Monotone g)
    (hcal : ∀ n ≥ 1, h (scale n) = (((2 * k + 1) ^ n : ℕ) : ℝ≥0∞)⁻¹)
    (hlim : liminf (normalizedGaugeCost (2 * k + 1) g) atTop = ⊤) :
    ¬ ∃ E : ℕ → Set ℝ,
      {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  have hpos : 0 < Measure.mkMetric h
      {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} := by
    rw [calibrated_exactLevel_eq_top k hk h hh hcont hcal]
    exact ENNReal.zero_lt_top
  exact (not_countable_union_finite_of_liminf_top (2 * k + 1) (by omega) h g hh hg hzero
    (fun n hn => (hcal n hn).le) hlim hpos).2

end

end GaugeLiminf

#print axioms GaugeLiminf.calibrated_exactLevel_eq_top
#print axioms GaugeLiminf.exactLevel_eq_top_of_liminf_pos
#print axioms GaugeLiminf.exactLevel_not_countable_union_finite_of_liminf_top


namespace GaugeLiminf

open GaugeCircle GaugeScaleComparison

noncomputable section

private theorem critGauge_calibration (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    critGauge k (scale n) ≤ (((2 * k + 1) ^ n : ℕ) : ℝ≥0∞)⁻¹ := by
  change critGauge k (ENNReal.ofReal (1 / (Qsel n : ℝ))) ≤ _
  rw [critGauge_at_inv_Qsel k hk hn, ← ofReal_zpow_neg_nat (2 * k + 1) n (by omega)]
  simp

private theorem binaryGauge_calibration (n : ℕ) (hn : 1 ≤ n) :
    binaryGauge (scale n) ≤ ((2 ^ n : ℕ) : ℝ≥0∞)⁻¹ := by
  change binaryGauge (ENNReal.ofReal (1 / (Qsel n : ℝ))) ≤ _
  rw [binaryGauge_at_inv_Qsel hn, ← ofReal_zpow_neg_nat 2 n (by omega)]
  norm_num

private theorem circle_measure_eq_top_of_liminf_pos (b : ℕ) (hb : 0 < b)
    (h g : ℝ≥0∞ → ℝ≥0∞) (hh : Monotone h) (hg : Monotone g) (hzero : h 0 = 0)
    (hcal : ∀ n ≥ 1, h (scale n) ≤ ((b ^ n : ℕ) : ℝ≥0∞)⁻¹)
    (hlim : 0 < liminf (normalizedGaugeCost b g) atTop)
    {S : Set UnitAddCircle} (hS : Measure.mkMetric h S = ⊤) :
    Measure.mkMetric g S = ⊤ := by
  obtain ⟨c, δ, hδ, hcomp⟩ :=
    exists_small_radius_comparison_of_liminf_pos b hb h g hh hg hzero hcal hlim
  by_contra hne
  have hbound := mkMetric_le_mul_of_eventually_le_circle h g c hδ hcomp S
  rw [hS] at hbound
  exact (not_lt_of_ge hbound) (ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr hne))

private theorem circle_no_finite_cover_of_liminf_top (b : ℕ) (hb : 0 < b)
    (h g : ℝ≥0∞ → ℝ≥0∞) (hh : Monotone h) (hg : Monotone g) (hzero : h 0 = 0)
    (hcal : ∀ n ≥ 1, h (scale n) ≤ ((b ^ n : ℕ) : ℝ≥0∞)⁻¹)
    (hlim : liminf (normalizedGaugeCost b g) atTop = ⊤)
    {S : Set UnitAddCircle} (hS : Measure.mkMetric h S = ⊤) :
    ¬ ∃ E : ℕ → Set UnitAddCircle, S ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  have hpos : 0 < Measure.mkMetric h S := by rw [hS]; exact ENNReal.zero_lt_top
  apply (not_countable_union_finite_of_ratio_tendsto_zero_circle h g ?_ hpos).2
  intro c hc
  apply exists_small_radius_comparison_of_lt_liminf b hb h g hh hg hzero hcal c hc
  rw [hlim]
  exact ENNReal.div_lt_top (by simp) (by exact_mod_cast hc.ne')

/-- Full liminf classification for the exact critical level on the circle.
    The zero case gives the stronger conclusion on the entire sublevel. -/
theorem circleExactLevel_liminf_trichotomy (k : ℕ) (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g) :
    let ρ := liminf (normalizedGaugeCost (2 * k + 1) g) atTop
    (ρ = 0 → Measure.mkMetric g (circleLevelSet k) = 0) ∧
    (ρ < ⊤ → ∃ E : ({N : ℕ // 1 ≤ N} × ℤ × ℤ) → Set UnitAddCircle,
      circleLevelSet k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
    (0 < ρ → ∀ U : Set UnitAddCircle, IsOpen U → U.Nonempty →
      Measure.mkMetric g (circleExactLevel k ∩ U) = ⊤) ∧
    (ρ = ⊤ → ∀ U : Set UnitAddCircle, IsOpen U → U.Nonempty →
      ¬ ∃ E : ℕ → Set UnitAddCircle, circleExactLevel k ∩ U ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    rw [circleLevelSet_eq_image]
    exact le_antisymm ((mkMetric_circleProj_image_le g hg _).trans_eq
      (mkMetric_levelSet_null_of_liminf_zero k g hg hzero)) bot_le
  · intro hfin
    obtain ⟨E, hcov, hE⟩ := levelSet_countable_cover_of_liminf_lt_top k g hg hfin
    refine ⟨fun i => circleProj '' E i, ?_, fun i =>
      (mkMetric_circleProj_image_le g hg _).trans_lt (hE i)⟩
    rw [circleLevelSet_eq_image]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
  · intro hpos U hU hUne
    exact circle_measure_eq_top_of_liminf_pos (2 * k + 1) (by omega)
      (critGauge k) g (critGauge_mono k hk) hg (critGauge_zero k)
      (critGauge_calibration k hk) hpos
      (mkMetric_critGauge_circleExactLevel_inter_open_eq_top k hk hU hUne)
  · intro htop U hU hUne
    exact circle_no_finite_cover_of_liminf_top (2 * k + 1) (by omega)
      (critGauge k) g (critGauge_mono k hk) hg (critGauge_zero k)
      (critGauge_calibration k hk) htop
      (mkMetric_critGauge_circleExactLevel_inter_open_eq_top k hk hU hUne)

/-- Full liminf classification for the unsigned exact limit set on the circle. -/
theorem circleUnsignedExactLimit_liminf_trichotomy (k : ℕ) (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g) :
    let ρ := liminf (normalizedGaugeCost 2 g) atTop
    (ρ = 0 → Measure.mkMetric g (circleUnsignedExactLimitSet k) = 0) ∧
    (ρ < ⊤ → ∃ E : ({N : ℕ // 1 ≤ N} × ℤ × ℤ) → Set UnitAddCircle,
      circleUnsignedExactLimitSet k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
    (0 < ρ → ∀ U : Set UnitAddCircle, IsOpen U → U.Nonempty →
      Measure.mkMetric g (circleUnsignedExactLimitSet k ∩ U) = ⊤) ∧
    (ρ = ⊤ → ∀ U : Set UnitAddCircle, IsOpen U → U.Nonempty →
      ¬ ∃ E : ℕ → Set UnitAddCircle, circleUnsignedExactLimitSet k ∩ U ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    exact le_antisymm ((mkMetric_circleProj_image_le g hg _).trans_eq
      (mkMetric_unsignedExactLimit_null_of_liminf_zero k g hg hzero)) bot_le
  · intro hfin
    obtain ⟨E, hcov, hE⟩ := unsignedExactLimit_countable_cover_of_liminf_lt_top k g hg hfin
    refine ⟨fun i => circleProj '' E i, ?_, fun i =>
      (mkMetric_circleProj_image_le g hg _).trans_lt (hE i)⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
  · intro hpos U hU hUne
    exact circle_measure_eq_top_of_liminf_pos 2 (by omega)
      binaryGauge g binaryGauge_mono hg binaryGauge_zero binaryGauge_calibration hpos
      (mkMetric_binaryGauge_circleUnsignedExactLimit_inter_open_eq_top k hk hU hUne)
  · intro htop U hU hUne
    exact circle_no_finite_cover_of_liminf_top 2 (by omega)
      binaryGauge g binaryGauge_mono hg binaryGauge_zero binaryGauge_calibration htop
      (mkMetric_binaryGauge_circleUnsignedExactLimit_inter_open_eq_top k hk hU hUne)

end

end GaugeLiminf

#print axioms GaugeLiminf.circleExactLevel_liminf_trichotomy
#print axioms GaugeLiminf.circleUnsignedExactLimit_liminf_trichotomy



namespace GaugeLiminf

open GaugeCircle

noncomputable section

/-- A finite liminf at a branching base forces a zero liminf at every smaller positive base. -/
theorem liminf_normalizedGaugeCost_zero_of_smaller_base (a b : ℕ) (hb : 0 < b)
    (hab : a < b) (g : ℝ≥0∞ → ℝ≥0∞)
    (hfin : liminf (normalizedGaugeCost b g) atTop < ⊤) :
    liminf (normalizedGaugeCost a g) atTop = 0 := by
  obtain ⟨C, hC, hCT⟩ := exists_between hfin
  have hCfreq : ∃ᶠ n : ℕ in atTop, normalizedGaugeCost b g n < C :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hC
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb.ne'
  have hbT : (b : ℝ≥0∞) ≠ ⊤ := by simp
  have hratio : (a : ℝ≥0∞) / (b : ℝ≥0∞) < 1 := by
    apply (ENNReal.div_lt_iff (Or.inl hb0) (Or.inl hbT)).mpr
    simpa using (show (a : ℝ≥0∞) < (b : ℝ≥0∞) by exact_mod_cast hab)
  have ht : Tendsto (fun n : ℕ => ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ n * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio) (Or.inr hCT.ne)
  have hidentity (n : ℕ) : normalizedGaugeCost a g n =
      ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ n * normalizedGaugeCost b g n := by
    simp only [normalizedGaugeCost, Nat.cast_pow, div_eq_mul_inv, mul_pow, mul_assoc]
    rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel_left (pow_ne_zero n hb0) (by simp)]
  apply le_antisymm _ bot_le
  by_contra! hpos
  obtain ⟨ε, hε, hεlim⟩ := exists_between hpos
  have hev := (tendsto_order.1 ht).2 ε hε
  have hsmall : ∃ᶠ n : ℕ in atTop, normalizedGaugeCost a g n ≤ ε := by
    refine (hCfreq.and_eventually hev).mono ?_
    intro n hn
    rw [hidentity n]
    exact (mul_le_mul_of_nonneg_left hn.1.le bot_le).trans hn.2.le
  exact hεlim.not_ge (liminf_le_of_frequently_le' hsmall)

theorem mkMetric_circleStrictLevel_null_of_liminf_lt_top (k : ℕ) (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hfin : liminf (normalizedGaugeCost (2 * k + 1) g) atTop < ⊤) :
    Measure.mkMetric g (circleStrictLevel k) = 0 := by
  have hlim := liminf_normalizedGaugeCost_zero_of_smaller_base
    (2 * (k - 1) + 1) (2 * k + 1) (by omega) (by omega) g hfin
  have hℝ : Measure.mkMetric g {x : ℝ | apprExponent x < ENNReal.ofReal ((k : ℝ) / 4)} = 0 := by
    apply measure_mono_null (strictLevel_subset_iUnion_digitClass k hk)
    apply measure_iUnion_digitClass_null (k - 1) (Measure.mkMetric g)
    intro N _ m₀ m₁
    exact le_antisymm
      ((mkMetric_digitClass_le_liminf (k - 1) N m₀ m₁ g hg).trans_eq hlim) bot_le
  rw [circleStrictLevel_eq_image]
  exact le_antisymm ((mkMetric_circleProj_image_le g hg _).trans_eq hℝ) bot_le

end

end GaugeLiminf

#print axioms GaugeLiminf.liminf_normalizedGaugeCost_zero_of_smaller_base
#print axioms GaugeLiminf.mkMetric_circleStrictLevel_null_of_liminf_lt_top

