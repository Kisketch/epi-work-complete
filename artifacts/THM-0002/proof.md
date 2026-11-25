<!-- NON-CANONICAL until gate passed / DO NOT CITE -->
# THM-0002 Proof (repaired; combined from Round 1 audits Q-R1-02 and Q-R1-03)

## 0. Growth
By induction Q_{j-1} ≤ Q_j (base: Q_1 = Q_0; step: Q_{j+1} ≥ (4j+2)Q_j > Q_j). Hence ρ_j := Q_{j+1}/Q_j ∈ [4j+2, 4j+3] for j ≥ 1. The sequence Q_j is strictly increasing for j ≥ 1. Q_n ≥ ∏_{j=1}^{n-1}(4j+2) ≥ 4^{n-1}(n−1)!, so log Q_n ≥ n log n + (log 4 − 1)n − log(4n) (Stirling). Also Q_n ≤ ∏(4j+3) ≤ 7^{n} n!, so log Q_n = n log n + O(n).

## 1. Upper bound dim_H F_τ ≤ max(1−τ, 0)
- τ = 0: trivial, since F_0 ⊂ [0,1]. τ > 1: j^{-τ} ≤ j^{-1}, so F_τ ⊂ F_1. It therefore suffices to treat 0 < τ ≤ 1.
- F_τ = ⋃_{C,N∈ℕ, N≥1} E_{C,N}, where E_{C,N} = {x ∈ [0,1] : ‖Q_j x‖ ≤ C j^{-τ} for all j ≥ N}. Put r_j = C j^{-τ}/Q_j (C, N integers, WLOG by rounding up).
- For x ∈ E_{C,N} and j ≥ N let k_j = round(Q_j x) ∈ {0, …, Q_j}. Then |x − k_j/Q_j| ≤ r_j, so x ∈ I_j(k_j) := [k_j/Q_j − r_j, k_j/Q_j + r_j].
- Consecutive indices: |k_{j+1}/Q_{j+1} − k_j/Q_j| ≤ r_j + r_{j+1} (triangle inequality through x). So k_{j+1} is an integer in a closed interval of length 2(r_j + r_{j+1})Q_{j+1}. The number of possible k_{j+1} given k_j is M_j ≤ 1 + 2(r_j + r_{j+1})Q_{j+1}.
- 2r_jQ_{j+1} ≤ 2C j^{-τ}(4j+3) ≤ 14C j^{1−τ}, and 2r_{j+1}Q_{j+1} ≤ 2C. Since 1 − τ ≥ 0, M_j ≤ (1+16C) j^{1−τ}.
- The number of tuples (k_N, …, k_n) is ≤ (Q_N+1)(1+16C)^n n^{(1−τ)n}. These tuples index a cover of E_{C,N} by intervals of diameter 2r_n → 0.
- For s > 1 − τ: log[#·(2r_n)^s] ≤ log(Q_N+1) + n log(1+16C) + (1−τ)n log n + s log(2C) − sτ log n − s log Q_n ≤ −(s − (1−τ)) n log n + O(n) → −∞. Hence H^s(E_{C,N}) = 0, so dim_H E_{C,N} ≤ s. By countable stability dim_H F_τ ≤ 1 − τ. At τ = 1 the count is exp(O(n)), so the dimension is 0.

## 2. Lower bound dim_H F_τ ≥ 1−τ for 0 < τ < 1 (τ = 0: F_0 = [0,1]; τ ≥ 1: trivial since 0 ∈ F_τ)
- Take C = 1/8 and r_j = j^{-τ}/(8Q_j). Then 2r_n Q_n ≤ 1/4, so retained intervals at level n (centres in (1/Q_n)ℤ) are separated by gaps ≥ (3/4)/Q_n.
- Whole children of a parent I_j(k) are the I_{j+1}(k') ⊂ I_j(k), i.e. the k' with k'/Q_{j+1} ∈ [k/Q_j − (r_j − r_{j+1}), k/Q_j + (r_j − r_{j+1})]. The number of such integers is ≥ ⌊ℓ_j⌋ > ℓ_j − 1, where ℓ_j := 2(r_j − r_{j+1})Q_{j+1}.
- r_{j+1}/r_j ≤ Q_j/Q_{j+1} ≤ 1/(4j+2), so r_j > r_{j+1}. And ℓ_j = 2C[ρ_j j^{-τ} − (j+1)^{-τ}] ≥ 2C(4j+1) j^{-τ} > j^{1−τ} for C = 1/8.
- Set c = 1/2 and b_j = ⌊c j^{1−τ}⌋. Since b_j ≤ j^{1−τ}/2 < j^{1−τ} < ℓ_j and b_j ∈ ℤ, b_j ≤ ⌊ℓ_j⌋ ≤ (number of whole children) for every j ≥ 1. [R1 checker fix] b_j ≥ 2 for j ≥ 4^{1/(1−τ)} (only j ≥ N is used; e.g. b_1 = 0). [R1 evaluator fix] Choose N ≥ 4^{1/(1−τ)}, N ≥ 2, and one start interval I_N(k) with 1 ≤ k ≤ Q_N − 1, which lies in (0,1).
- Build nested compact sets E_n, n ≥ N: each retained level-j interval keeps exactly b_j whole children. Distinct children are disjoint, since 1/Q_{j+1} > 2r_{j+1}. Every x ∈ ⋂E_n satisfies ‖Q_j x‖ ≤ Q_j r_j = j^{-τ}/8 for j ≥ N, so ⋂E_n ⊂ F_τ.
- Mass: give each level-n interval mass 1/M_n, where M_n = ∏_{j=N}^{n-1} b_j. This is consistent and defines a Borel probability measure μ supported on ⋂E_n (Kolmogorov extension / weak limit). log M_n = (1−τ) n log n + O(n).
- Let I be an interval of length h with Q_{n+1}^{-1} ≤ h < Q_n^{-1} (n ≥ N). These ranges partition (0, Q_N^{-1}). I meets at most 2 level-n retained intervals: meeting 3 would need length ≥ 2/Q_n − 2r_n ≥ 1.75/Q_n. Hence μ(I) ≤ 2/M_n.
- For 0 < s < 1−τ: log(2/M_n) + s log Q_{n+1} ≤ −(1−τ−s) n log n + O(n) → −∞, so 2/M_n ≤ Q_{n+1}^{-s} ≤ h^s for n ≥ n_0(s, τ, N). (n_0 can be very large, e.g. n_0 = 729551 at τ = 0.5, s = 0.4, N = 16; checker scripts logs/verification/R1/checker{3,4}_THM-0002_c.py.) Intervals with h ≥ Q_N^{-1} are irrelevant to the mass distribution principle.
- Mass distribution principle: H^s(⋂E_n) ≥ μ(⋂E_n)/1 > 0, so dim_H F_τ ≥ s. Letting s ↑ 1−τ gives the claim. ∎

## Corrections to the paper text
- "at most three retained intervals" → at most two (the original is true but not sharp).
- "absolute c" → c = 1/2 with the τ-dependent threshold j_0 = 2^{1/(1−τ)}.
- Plus the 12 expository gaps listed in upper_bound_audit.md.

## Category
Category 5 (reproduction and repair of the paper's own proof). Novelty unchecked: a literature search for lacunary/exact-approximation dimension results is TODO. This theorem says nothing about the point π.

Numerics (category 4, illustrative only): logs/verification/R1/Q-R1-03_a.py, Q-R1-03_b.py.
