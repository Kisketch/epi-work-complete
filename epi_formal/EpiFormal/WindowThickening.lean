import Mathlib
import EpiFormal.CylinderFrostman

/-!
# Thickening facts for the Frostman S3 step (paper §7 direct assembly).

Two self-contained prerequisites for the finite-subcover stage:
- boundedness of thickenings from an ediam bound on the covered set;
- positivity of the diameter of a thickening of a nonempty set (needs only a
  ball inside + boundedness, no level structure).
-/

namespace WindowThickening

open MeasureTheory Set Filter Finset ENNReal Metric Topology

/-- Thickenings of ediam-bounded sets are bounded. -/
theorem isBounded_thickening_of_ediam {s : Set ℝ} {r : ℝ≥0∞} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hs : Metric.ediam s ≤ r) (hr : r ≠ ⊤) :
    Bornology.IsBounded (Metric.thickening δ s) := by
  rw [Metric.isBounded_iff_ediam_ne_top]
  have h := Cylinder.ediam_thickening_le (A := s) (ρ := δ) hδ0
  -- h : ediam (thickening δ s) ≤ ediam s + 2 * ofReal δ
  have htop : Metric.ediam s + 2 * ENNReal.ofReal δ ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    refine ⟨?_, ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top⟩
    exact ne_of_lt (lt_of_le_of_lt hs (lt_top_iff_ne_top.mpr hr))
  exact ne_of_lt (lt_of_le_of_lt h (lt_top_iff_ne_top.mpr htop))

/-- A thickening of a nonempty set has positive diameter (contains a ball). -/
theorem diam_thickening_pos {s : Set ℝ} {δ : ℝ} (hne : s.Nonempty) (hδ : 0 < δ)
    (hbdd : Bornology.IsBounded (Metric.thickening δ s)) :
    0 < Metric.diam (Metric.thickening δ s) := by
  obtain ⟨x, hx⟩ := hne
  have hball : Metric.ball x δ ⊆ Metric.thickening δ s :=
    Metric.ball_subset_thickening hx δ
  have hy1 : x - δ / 2 ∈ Metric.thickening δ s := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : |x - δ / 2 - x| = δ / 2 := by
      have e1 : x - δ / 2 - x = -(δ / 2) := by ring
      rw [e1, abs_neg, abs_of_pos (half_pos hδ)]
    rw [h1]; linarith
  have hy2 : x + δ / 2 ∈ Metric.thickening δ s := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have h2 : |x + δ / 2 - x| = δ / 2 := by
      have e2 : x + δ / 2 - x = δ / 2 := by ring
      rw [e2, abs_of_pos (half_pos hδ)]
    rw [h2]; linarith
  have hdist : (δ : ℝ) ≤ dist (x - δ / 2) (x + δ / 2) := by
    have e : (x - δ / 2) - (x + δ / 2) = -δ := by ring
    rw [Real.dist_eq, e, abs_neg, abs_of_pos hδ]
  have hle := Metric.dist_le_diam_of_mem hbdd hy1 hy2
  linarith [Metric.diam_nonneg (s := Metric.thickening δ s)]

#print axioms WindowThickening.isBounded_thickening_of_ediam
#print axioms WindowThickening.diam_thickening_pos

end WindowThickening
