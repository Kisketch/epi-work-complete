import EpiFormal.WindowMuImplication

/-!
# F2：逐集上界实例化（质量 × 交数 → μU ≤ C·h^s）

paper2 §7 thm:windows 的 Frostman 组装件：将 `mu_window_le`（窗内质量 ≤ N·m0）
与数值阈值接口 `hthresh : N*m0 ≤ C·diam^s` 拼成 F1 主定理所需的逐集上界形状
`μ U ≤ ofReal (C * diam U ^ s)`。阈值本身由 `exp_ratio_bound` + `window_overlap_le`
在应用点 discharge，本文件只做无条件组装。

命名空间 `WindowMuBound`；仅依赖 Lean 基础公理。
-/

namespace WindowMuBound

open scoped ENNReal

/-- 逐集上界：交窗原子数 ≤ N、每原子质量 ≤ m0、阈值成立 ⇒ μU ≤ C·h^s。 -/
theorem mu_le_of_overlap_thresh
    {ι : Type} (μ : MeasureTheory.Measure ℝ) (A : ι → Set ℝ) (G : Finset ι)
    (U : Set ℝ) (N : ℕ) (m0 C s : ℝ)
    (hcard : G.card ≤ N)
    (hcover : U ⊆ ⋃ i ∈ G, A i)
    (hbound : ∀ i ∈ G, μ (A i) ≤ ENNReal.ofReal m0)
    (hthresh : (N : ℝ) * m0 ≤ C * (Metric.diam U) ^ s) :
    μ U ≤ ENNReal.ofReal (C * (Metric.diam U) ^ s) := by
  have h1 := WindowMu.mu_window_le A G U N m0 hcard hcover hbound
  have hcast : ((N : ℝ≥0∞) * ENNReal.ofReal m0)
      = ENNReal.ofReal ((N : ℝ) * m0) := by
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  calc μ U ≤ ((N : ℝ≥0∞) * ENNReal.ofReal m0) := h1
    _ = ENNReal.ofReal ((N : ℝ) * m0) := hcast
    _ ≤ ENNReal.ofReal (C * (Metric.diam U) ^ s) :=
        ENNReal.ofReal_le_ofReal hthresh

end WindowMuBound

#print axioms WindowMuBound.mu_le_of_overlap_thresh
