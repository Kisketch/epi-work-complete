<!-- NON-CANONICAL until gate passed / DO NOT CITE -->
# THM-0005 (sharpness of THM-0003)
Setup: Q_0 = Q_1 = 1, P_0 = 1, P_1 = 3, u_{j+1} = (4j+2)u_j + u_{j-1}; given P_j/Q_j → e; L = ℤ + ℤ(e+1)/2.
Claim: κ := inf_{z∉L} limsup_j j‖Q_j z‖ = 1/4, and the infimum is attained. Explicitly, let n_0 = n_1 = 0, n_{j+1} = (4j+2)n_j + n_{j-1} + m_j with m_j = 1 for even j ≥ 2 and m_j = 0 otherwise, and z* = lim n_j/Q_j. Then z* ∉ L and j‖Q_j z*‖ → 1/4 along even j and → 0 along odd j.
Category: candidate 1 (novelty NOT checked; literature search TODO). The lower bound is THM-0003 (category 5).

## Lean coverage (Round 3)
- Lean (`EpiFormal/KappaSharp.lean`): `kappa_eq_quarter` = [∀ z ∉ L, ∀ c < 1/4, ¬ eventually j‖Q_j z‖ ≤ c] ∧ [∃ z ∉ L, ∀ c > 1/4, eventually j‖Q_j z‖ ≤ c]; `kappa_sharp` gives the witness z* (same defect sequence) with "frequently ≥ 1/5". Together: κ = 1/4, attained. Statement fidelity: fresh-evaluator PASS (R3).
- NOT in Lean: the finer claim "→ 1/4 along even j, → 0 along odd j" (paper proof only). The identification of Qsel with the actual CF convergents of e is a recurrence definition, not a Lean theorem (statement.md assumes P_j/Q_j → e, and the project proves Psel/Qsel → e).
