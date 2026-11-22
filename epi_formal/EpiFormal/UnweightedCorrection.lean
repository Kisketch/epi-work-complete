import EpiFormal.QuarterPointFinal

open Filter Topology QuarterPointFinal Classification QuarterPoint QuarterPointTail

namespace UnweightedCorrection

theorem witness :
    ∃ x : ℝ, Tendsto (fun j : ℕ => distToNearestInt ((Qsel j : ℝ) * x)) atTop (nhds 0)
      ∧ x ∉ latticeL := by
  refine ⟨x0, ?_, ?_⟩
  · simpa [eps, nearestInt, distToNearestInt] using QuarterPointFinal.eps_tendsto_zero.abs
  · intro hx
    have h := tendsto_nhds_unique QuarterPointFinal.lambda_x0_eq_quarter (theorem2_sufficiency x0 hx)
    norm_num at h

#print axioms witness
end UnweightedCorrection
