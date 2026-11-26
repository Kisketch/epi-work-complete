<!-- NON-CANONICAL / DO NOT CITE -->
# THM-0002 upper bound: worker Q-R1-02 audit (Round 1)
Verdict: correct with repairable gaps; no fatal gap.

Repaired argument (worker):
1. Q_0 = Q_1 = 1 and Q_{j+1} = (4j+2)Q_j + Q_{j-1}. By induction Q_{j-1} ≤ Q_j, hence 4j+2 ≤ Q_{j+1}/Q_j ≤ 4j+3, with equality at j = 1.
2. Q_n ≥ ∏_{j=1}^{n-1}(4j+2) ≥ 4^{n-1}(n-1)!, so log Q_n ≥ n log n + (log 4 − 1)n − log(4n) (Stirling).
3. F_τ = ⋃_{C,N∈ℕ} E_{C,N}, where E_{C,N} = {x : ‖Q_j x‖ ≤ C j^{-τ} for all j ≥ N}.
4. The chain map x ↦ (k_N, …, k_n) with k_j = round(Q_j x) lies in {0, …, Q_j}. Consecutive centres satisfy |k_{j+1}/Q_{j+1} − k_j/Q_j| ≤ r_j + r_{j+1}, by the triangle inequality through x.
5. The number of children is ≤ 1 + 2(r_j + r_{j+1})Q_{j+1} ≤ (1+16C) j^{1−τ}. This uses 0 ≤ τ ≤ 1 and 4j+3 ≤ 7j.
6. The number of chains is ≤ (Q_N+1)(1+16C)^n n^{(1−τ)n}. For s > 1 − τ: log[#chains·(2r_n)^s] ≤ −(s−(1−τ)) n log n + O(n) → −∞. Hence H^s(E_{C,N}) = 0, and countable stability gives dim_H F_τ ≤ 1 − τ.
7. For τ > 1, F_τ ⊂ F_1, and at τ = 1 the chain count is exp(O(n)), giving dimension 0. For τ = 0 the bound is trivial.

Gaps in the paper (all repairable):
- (1) Q_{j-1} ≤ Q_j is unproved.
- (2) Stirling and the base case are not stated.
- (3) The range of k, the closed intervals and overlap are not addressed.
- (4) "Chain" is undefined.
- (5) The triangle-inequality step is not stated.
- (6) Constants are implicit and the use of τ ≤ 1 is not flagged.
- (7) The Q_N+1 start count is not stated.
- (8) The product bound needs τ ≤ 1.
- (9) The H^s quantifiers are not spelled out.
- (10) Convergence is numerically slow.
- (11) "0 ∈ F_τ" is misplaced.
- (12) F_0 = [0,1] is not needed here.

Numerics: the worker reported mpmath runs (ratio check j ≤ 398, M_j ≤ (1+16C)j^{1−τ} check). The scripts were NOT retained in the workspace. This is a missing certificate (AGENTS.md §6), so the numerics are not relied on. The proof does not depend on them.
Category: 5 (check and reproduction). Novelty: literature check not done.
