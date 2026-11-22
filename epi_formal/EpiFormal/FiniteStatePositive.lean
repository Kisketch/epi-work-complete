import EpiFormal.FiniteStateTail
import Mathlib

/-!
# Finite-state tail: positive lower bound at Perron base `λ > 1`

Paper: `thm:finite-state-tail`, positive-measure part of the proof
(paper L1755–L1798: Perron path probabilities, `(1-p)^m` block avoidance,
pushforward full mass, cylinder estimate, mass distribution).

## What is verified here

* `perron_word_mass_sum` / `perron_word_mass_bound`: the finite-word Perron
  identities (paper L1766–L1767, "path-cylinder mass telescopes"). Proved from
  the already-verified `walkMass_of_eigenvector` / `walkCount_bounds`. This
  certifies that the interface constants below (`C0`, `ρ`) are realizable.
* `muRestricted_elem_le`: every small-diameter set meeting the tail carries
  `μ`-mass at most `K · hlam(ediam)`, from the cylinder interface.
* `muRestrict_le_mkMetric_hlam`: Frostman comparison via mathlib's
  `Measure.le_mkMetric`.
* `one_le_mkMetric_scaled` / `pos_mkMetric_scaled`: the scaled critical gauge
  measure of the tail set is `≥ 1`, hence positive. The gauge carries the
  explicit constant `K = 3 * C0 * Kgeo`; scaling a gauge by a positive
  constant does not change positivity, so this is the paper's
  `H^{h_λ}(S_k(G)) > 0` up to the documented constant.

## Explicit paper interfaces (honest)

* `Hcyl`: per-cylinder `μ`-mass bound `C0 * ρ ^ m` (paper L1767, L1790–1792;
  the finite-word formula is verified, the path-space construction is paper).
* `Hmeet`: every small set meets at most 3 length-appropriate cylinders with
  the `ρ ^ m ≤ Kgeo * hlam` comparison (paper L1786–L1793 coding geometry).
* `hμfull : μ S = 1`: pushforward gives full mass (paper L1783–1784).
* `hSmeas : MeasurableSet S`: Borel regularity (paper L1800).
* The `(1-p)^m` block-avoidance / a.e. marked-edge crossing, the Haar
  local-infinitude contradiction (paper L1809–L1820), and the multi-component
  assembly (paper L1822–L1847) stay paper-side.

No `sorry`. No new axioms beyond Lean + Mathlib + the file's explicit
interface hypotheses (which appear as theorem premises, not axioms).
-/

open Filter Topology Set MeasureTheory FiniteStateGauge
open scoped ENNReal BigOperators

namespace FiniteStateGauge

noncomputable section

universe u

/-- Endpoint vertex of a finite labelled walk. -/
def endVertex {V : Type u} [Fintype V] (edges : V → V → Finset ℤ) :
    ∀ {n : ℕ} {v : V}, Path edges n v → V
  | 0, v, _ => v
  | _ + 1, _, ⟨_, _, q⟩ => endVertex edges q

/-- Finite-word Perron identity: endpoint weights sum to the Perron growth
(paper L1766–1767). From the verified `walkMass_of_eigenvector`. -/
theorem perron_word_mass_sum {V : Type u} [Fintype V]
    (edges : V → V → Finset ℤ) (w : V → ℝ) (growth : ℝ)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    (n : ℕ) (v : V) :
    ∑ q : Path edges n v, w (endVertex edges q) = growth ^ n * w v := by
  induction n generalizing v with
  | zero =>
    have he : Path edges 0 v ≃ PUnit := Equiv.refl _
    have hc : Fintype.card (Path edges 0 v) = 1 := by
      rw [Fintype.card_congr he, Fintype.card_unique]
    simp [endVertex, hc]
  | succ n ih =>
    have hword : ∀ (u : V),
        ∑ _h : {a // a ∈ edges v u}, ∑ q' : Path edges n u,
          w (endVertex edges q') = adjacency edges v u * (growth ^ n * w u) := by
      intro u
      rw [← ih]
      simp only [Finset.sum_const, Fintype.card_coe, nsmul_eq_mul,
        Finset.card_univ]
      rfl
    show ∑ _q : (Σ u : V, {a // a ∈ edges v u} × Path edges n u),
        w (endVertex edges _) = _
    rw [Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type]
    calc ∑ u : V, ∑ _h : {a // a ∈ edges v u}, ∑ q' : Path edges n u,
            w (endVertex edges q')
        = ∑ u : V, adjacency edges v u * (growth ^ n * w u) :=
          Finset.sum_congr rfl (fun u _ => hword u)
      _ = growth ^ n * (∑ u, adjacency edges v u * w u) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          ring
      _ = growth ^ (n + 1) * w v := by rw [hw v, pow_succ, mul_assoc]

/-- Per-word normalized mass bound (consistency of the interface constants
`C0 = hi / lo`, `ρ = 1 / growth` with the verified Perron data). -/
theorem perron_word_mass_bound {V : Type u} [Fintype V]
    (edges : V → V → Finset ℤ) (w : V → ℝ) (growth : ℝ)
    (lo hi : ℝ) (hlo : 0 < lo)
    (hl : ∀ u, lo ≤ w u) (hu : ∀ u, w u ≤ hi)
    (hgrowth : 0 < growth) (n : ℕ) (v : V) (q : Path edges n v) :
    w (endVertex edges q) / (growth ^ n * w v) ≤ (hi / lo) * (1 / growth) ^ n := by
  have hwv : 0 < w v := hlo.trans_le (hl v)
  have hD : (0 : ℝ) < growth ^ n * w v := mul_pos (pow_pos hgrowth n) hwv
  have hhi : (0 : ℝ) < hi := lt_of_lt_of_le hwv (hu v)
  have h1 : (1 : ℝ) ≤ w v / lo := by
    rw [le_div_iff₀ hlo]
    linarith [hl v]
  have h2 : ((1 : ℝ) / growth) ^ n * growth ^ n = 1 := by
    have hginv : ((1 : ℝ) / growth) ^ n = (growth ^ n)⁻¹ := by
      rw [one_div, inv_pow]
    rw [hginv, inv_mul_cancel₀ (ne_of_gt (pow_pos hgrowth n))]
  have hbig : w (endVertex edges q) ≤ hi * (w v / lo) := by
    calc w (endVertex edges q) ≤ hi := hu _
      _ = hi * 1 := (mul_one _).symm
      _ ≤ hi * (w v / lo) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hhi)
  have heq : ((hi / lo) * (1 / growth) ^ n) * (growth ^ n * w v)
      = hi * (w v / lo) := by
    calc ((hi / lo) * (1 / growth) ^ n) * (growth ^ n * w v)
        = (hi / lo) * w v * (((1 / growth) ^ n * growth ^ n)) := by ring
      _ = (hi / lo) * w v * 1 := by rw [h2]
      _ = hi * (w v / lo) := by ring
  rw [div_le_iff₀ hD, heq]
  exact hbig

/-- Covering-cost estimate: a small-diameter set meeting the tail carries
`μ`-mass at most `K · hlam(ediam)` (paper L1786–L1793). -/
theorem muRestricted_elem_le
    (μ : Measure ℝ) (S : Set ℝ) (C : ℕ → Finset (Set ℝ))
    (C0 Kgeo ρ rN : ℝ≥0∞) (hlam : ℝ≥0∞ → ℝ≥0∞)
    (Hcyl : ∀ (m : ℕ) (c : Set ℝ), c ∈ C m → μ c ≤ C0 * ρ ^ m)
    (Hmeet : ∀ T : Set ℝ, Metric.ediam T ≤ rN →
      ∃ F : Finset (Set ℝ), F.card ≤ 3 ∧ T ∩ S ⊆ ⋃ c ∈ F, c ∧
        ∀ c ∈ F, ∃ m : ℕ, c ∈ C m ∧ ρ ^ m ≤ Kgeo * hlam (Metric.ediam T))
    (T : Set ℝ) (hT : Metric.ediam T ≤ rN) :
    μ (T ∩ S) ≤ 3 * C0 * Kgeo * hlam (Metric.ediam T) := by
  obtain ⟨F, hcard, hsub, hF⟩ := Hmeet T hT
  have hper : ∀ c ∈ F, μ c ≤ C0 * Kgeo * hlam (Metric.ediam T) := by
    intro c hc
    obtain ⟨m, hcm, hρm⟩ := hF c hc
    calc μ c ≤ C0 * ρ ^ m := Hcyl m c hcm
      _ ≤ C0 * (Kgeo * hlam (Metric.ediam T)) :=
          mul_le_mul_of_nonneg_left hρm bot_le
      _ = C0 * Kgeo * hlam (Metric.ediam T) := by ring
  calc μ (T ∩ S) ≤ ∑ c ∈ F, μ c :=
        le_trans (measure_mono hsub) (measure_biUnion_finset_le F _)
    _ ≤ ∑ _c ∈ F, C0 * Kgeo * hlam (Metric.ediam T) :=
        Finset.sum_le_sum hper
    _ ≤ 3 * C0 * Kgeo * hlam (Metric.ediam T) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard' : (F.card : ℝ≥0∞) ≤ 3 := by exact_mod_cast hcard
        have hX : (0 : ℝ≥0∞) ≤ C0 * Kgeo * hlam (Metric.ediam T) := bot_le
        calc (F.card : ℝ≥0∞) * (C0 * Kgeo * hlam (Metric.ediam T))
            ≤ 3 * (C0 * Kgeo * hlam (Metric.ediam T)) :=
              mul_le_mul_of_nonneg_right hcard' hX
          _ = 3 * C0 * Kgeo * hlam (Metric.ediam T) := by ring

/-- Frostman comparison: the restricted measure sits below the scaled
critical-gauge outer measure (mathlib `Measure.le_mkMetric`). -/
theorem muRestrict_le_mkMetric_hlam
    (μ : Measure ℝ) (S : Set ℝ) (C : ℕ → Finset (Set ℝ))
    (C0 Kgeo ρ rN : ℝ≥0∞) (hlam : ℝ≥0∞ → ℝ≥0∞)
    (hrN : 0 < rN) (hSmeas : MeasurableSet S)
    (Hcyl : ∀ (m : ℕ) (c : Set ℝ), c ∈ C m → μ c ≤ C0 * ρ ^ m)
    (Hmeet : ∀ T : Set ℝ, Metric.ediam T ≤ rN →
      ∃ F : Finset (Set ℝ), F.card ≤ 3 ∧ T ∩ S ⊆ ⋃ c ∈ F, c ∧
        ∀ c ∈ F, ∃ m : ℕ, c ∈ C m ∧ ρ ^ m ≤ Kgeo * hlam (Metric.ediam T)) :
    μ.restrict S ≤ Measure.mkMetric (fun r => 3 * C0 * Kgeo * hlam r) := by
  apply Measure.le_mkMetric _ _ _ hrN
  intro T hT
  show (μ.restrict S) T ≤ 3 * C0 * Kgeo * hlam (Metric.ediam T)
  rw [Measure.restrict_apply' hSmeas]
  exact muRestricted_elem_le μ S C C0 Kgeo ρ rN hlam Hcyl Hmeet T hT

/-- Positive scaled critical gauge measure of the tail set
(paper L1797: `H^{h_λ}(S_k(G)) > 0` up to the explicit constant). -/
theorem one_le_mkMetric_scaled
    (μ : Measure ℝ) (S : Set ℝ) (C : ℕ → Finset (Set ℝ))
    (C0 Kgeo ρ rN : ℝ≥0∞) (hlam : ℝ≥0∞ → ℝ≥0∞)
    (hrN : 0 < rN) (hSmeas : MeasurableSet S) (hμfull : μ S = 1)
    (Hcyl : ∀ (m : ℕ) (c : Set ℝ), c ∈ C m → μ c ≤ C0 * ρ ^ m)
    (Hmeet : ∀ T : Set ℝ, Metric.ediam T ≤ rN →
      ∃ F : Finset (Set ℝ), F.card ≤ 3 ∧ T ∩ S ⊆ ⋃ c ∈ F, c ∧
        ∀ c ∈ F, ∃ m : ℕ, c ∈ C m ∧ ρ ^ m ≤ Kgeo * hlam (Metric.ediam T)) :
    1 ≤ Measure.mkMetric (fun r => 3 * C0 * Kgeo * hlam r) S := by
  have hle := muRestrict_le_mkMetric_hlam μ S C C0 Kgeo ρ rN hlam
    hrN hSmeas Hcyl Hmeet
  have hself : (μ.restrict S) S = μ S := Measure.restrict_apply_self μ S
  calc (1 : ℝ≥0∞) = μ S := hμfull.symm
    _ = (μ.restrict S) S := hself.symm
    _ ≤ Measure.mkMetric (fun r => 3 * C0 * Kgeo * hlam r) S := hle S

/-- Positivity form of the lower bound. -/
theorem pos_mkMetric_scaled
    (μ : Measure ℝ) (S : Set ℝ) (C : ℕ → Finset (Set ℝ))
    (C0 Kgeo ρ rN : ℝ≥0∞) (hlam : ℝ≥0∞ → ℝ≥0∞)
    (hrN : 0 < rN) (hSmeas : MeasurableSet S) (hμfull : μ S = 1)
    (Hcyl : ∀ (m : ℕ) (c : Set ℝ), c ∈ C m → μ c ≤ C0 * ρ ^ m)
    (Hmeet : ∀ T : Set ℝ, Metric.ediam T ≤ rN →
      ∃ F : Finset (Set ℝ), F.card ≤ 3 ∧ T ∩ S ⊆ ⋃ c ∈ F, c ∧
        ∀ c ∈ F, ∃ m : ℕ, c ∈ C m ∧ ρ ^ m ≤ Kgeo * hlam (Metric.ediam T)) :
    0 < Measure.mkMetric (fun r => 3 * C0 * Kgeo * hlam r) S :=
  lt_of_lt_of_le zero_lt_one
    (one_le_mkMetric_scaled μ S C C0 Kgeo ρ rN hlam hrN hSmeas hμfull Hcyl Hmeet)

#print axioms FiniteStateGauge.perron_word_mass_sum
#print axioms FiniteStateGauge.perron_word_mass_bound
#print axioms FiniteStateGauge.muRestricted_elem_le
#print axioms FiniteStateGauge.muRestrict_le_mkMetric_hlam
#print axioms FiniteStateGauge.one_le_mkMetric_scaled
#print axioms FiniteStateGauge.pos_mkMetric_scaled

end

end FiniteStateGauge
