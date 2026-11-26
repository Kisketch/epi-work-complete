<!-- NON-CANONICAL until gate passed / DO NOT CITE -->
# THM-0006 Proof (worker Q-R2-03, Round 2)
(a) Casoratian C_j := P_jQ_{j+1} − P_{j+1}Q_j = −C_{j-1}, so C_j = (−1)^j D.
(b) Q_j ≥ 1 for j ≥ 1, Q_{j+1} ≥ a_jQ_j, and Q_j → ∞. Q_{k+2} > Q_k, so Q_kQ_{k+1} is strictly increasing for k ≥ 1.
(c) P_{k+1}/Q_{k+1} − P_k/Q_k = −(−1)^k D/(Q_kQ_{k+1}). This is alternating with decreasing terms → 0, so θ exists, |θ − P_j/Q_j| ≤ |D|/(Q_jQ_{j+1}), and |δ_j| ≤ |D|/Q_{j+1} for j ≥ 1 (alternation from k = 1). For j = 0: if Q_0 = 0 then |δ_0| = |P_0| = |D|/Q_1; if Q_0 ≥ 1 the same argument applies since Q_2 > Q_0. [R2 checker fix]
(d) θ irrational: if θ = p/q, then qδ_j ∈ ℤ and → 0, so δ_j = 0 eventually. Running the recurrence backwards gives δ_0 = δ_1 = 0, so D = 0, a contradiction.
(e) δ satisfies the recurrence, and Q_jδ_{j+1} − Q_{j+1}δ_j = (−1)^j D ≠ 0, so (Q, δ) is a basis.
Lemma 1: if γQ_j + εP_j ∈ ℤ at two consecutive indices, then at all j ≥ 0 (forward and backward recurrence with integer a_j). So Λ := {(γ,ε) : γQ_j + εP_j ∈ ℤ ∀j} = M^{-1}ℤ² with M = [[Q_0,P_0],[Q_1,P_1]], and L = {γ + εθ : (γ,ε) ∈ Λ} = (ℤδ_0 + ℤδ_1)/D.
(A) z = γ + εθ with (γ,ε) ∈ Λ: n_j := γQ_j + εP_j ∈ ℤ and Q_jz − n_j = εδ_j, so a_j‖Q_jz‖ ≤ |εD| a_j/Q_{j+1} ≤ |εD|/Q_j → 0.
(B) Suppose limsup a_j‖Q_jz‖ < c < 1.
 1. Let y_j = Q_jz − n_j (nearest integer), so |y_j| < c/a_j for j ≥ J_1.
 2. m_j := n_{j+1} − a_jn_j − n_{j-1} ∈ ℤ, and |m_j| ≤ |y_{j+1}| + a_j|y_j| + |y_{j-1}| < c/a_{j+1} + c + c/a_{j-1} < 1 for large j, so m_j = 0 for j ≥ J.
 3. Then y_j = αQ_j + βδ_j for j ≥ J−1; y_j → 0 and Q_j → ∞ force α = 0.
 4. n_j = (z − βθ)Q_j + βP_j. Lemma 1 (valid for real γ, ε) gives directly (γ,ε) ∈ Λ, so z ∈ L. ∎
(C) w_j‖Q_jz‖ = (w_j/a_j)·a_j‖Q_jz‖; a limsup ≥ 1 (including ∞) scales to ≥ κ, and 0 stays 0.
Specialisation: D = −2, (δ_0 − δ_1)/D = −1, so L = ℤ + ℤ(e−1)/2 = ℤ + ℤ(e+1)/2. w_j = j and a_j = 4j+2 give κ = 1/4.
Numerics (category 4): logs/verification/R2/R2_03_check.py (e-case; general example a_j = j²+1, (Q_0,Q_1,P_0,P_1) = (2,1,1,4), D = −7, index 7).
Not proved: behaviour when a_j does not tend to ∞; single-index sufficiency; sharpness of threshold 1 in general.
