import EpiFormal.GaugeCircle

/-!
Path-count estimates for the finite-state defect constraint in the companion paper.
The inputs are the adjacency matrix and a strictly positive right eigenvector.
-/

open scoped BigOperators

namespace FiniteStateGauge

noncomputable section

variable {V : Type*} [Fintype V]

/-- Weighted number of walks of a specified length, starting at a vertex. -/
def walkMass (A : V → V → ℝ) (w : V → ℝ) : ℕ → V → ℝ
  | 0, v => w v
  | n + 1, v => ∑ u, A v u * walkMass A w n u

theorem walkMass_mono (A : V → V → ℝ) (hA : ∀ v u, 0 ≤ A v u)
    {w₁ w₂ : V → ℝ} (hw : ∀ v, w₁ v ≤ w₂ v) (n : ℕ) (v : V) :
    walkMass A w₁ n v ≤ walkMass A w₂ n v := by
  induction n generalizing v with
  | zero => exact hw v
  | succ n ih =>
    exact Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (ih u) (hA v u)

theorem walkMass_smul (A : V → V → ℝ) (w : V → ℝ) (c : ℝ) (n : ℕ) (v : V) :
    walkMass A (fun u => c * w u) n v = c * walkMass A w n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [walkMass, ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring

theorem walkMass_of_eigenvector (A : V → V → ℝ) (w : V → ℝ) (growth : ℝ)
    (hw : ∀ v, (∑ u, A v u * w u) = growth * w v) (n : ℕ) (v : V) :
    walkMass A w n v = growth ^ n * w v := by
  induction n generalizing v with
  | zero => simp [walkMass]
  | succ n ih =>
    calc
      walkMass A w (n + 1) v = ∑ u, A v u * (growth ^ n * w u) := by
        simp only [walkMass, ih]
      _ = growth ^ n * ∑ u, A v u * w u := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = growth ^ (n + 1) * w v := by rw [hw, pow_succ, mul_assoc]

/-- The unweighted path count is bounded above and below by the Perron scale. -/
theorem walkCount_bounds (A : V → V → ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (w : V → ℝ) (growth lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hw : ∀ v, (∑ u, A v u * w u) = growth * w v)
    (hl : ∀ v, lo ≤ w v) (hu : ∀ v, w v ≤ hi) (n : ℕ) (v : V) :
    (growth ^ n * w v) / hi ≤ walkMass A (fun _ => 1) n v ∧
    walkMass A (fun _ => 1) n v ≤ (growth ^ n * w v) / lo := by
  have hleft := walkMass_mono A hA (w₁ := fun _ => lo * 1) (w₂ := w)
    (fun u => by simpa using hl u) n v
  have hright := walkMass_mono A hA (w₁ := w) (w₂ := fun _ => hi * 1)
    (fun u => by simpa using hu u) n v
  rw [walkMass_smul, walkMass_of_eigenvector A w growth hw] at hleft hright
  exact ⟨(div_le_iff₀ hhi).2 (by simpa [mul_comm] using hright),
    (le_div_iff₀ hlo).2 (by simpa [mul_comm] using hleft)⟩

end

end FiniteStateGauge

#print axioms FiniteStateGauge.walkMass_of_eigenvector
#print axioms FiniteStateGauge.walkCount_bounds
