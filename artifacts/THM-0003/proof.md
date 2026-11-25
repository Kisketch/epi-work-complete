<!-- NON-CANONICAL until gate passed / DO NOT CITE -->
# THM-0003 / THM-0004 proofs (worker Q-R1-05, Round 1)

## 0. Preliminaries
(F1) Q_{j+1} ≥ (4j+2)Q_j ≥ 6Q_j for j ≥ 1, so Q_i/Q_j ≤ 6^{-(j−i)} for 1 ≤ i < j, and Q_j → ∞.
(F2) The coefficients 4j+2 are even, so u_{j+1} ≡ u_{j-1} (mod 2). All Q_j and P_j are odd.
(F3) P_jQ_{j+1} − P_{j+1}Q_j = 2(−1)^{j+1} ≠ 0, so (Q, P) is a basis of the real solutions. δ satisfies the recurrence and δ_jQ_{j+1} − δ_{j+1}Q_j = 2(−1)^j ≠ 0, so (Q, δ) is also a basis.
(F4) P_{j+1}/Q_{j+1} − P_j/Q_j = 2(−1)^j/(Q_jQ_{j+1}). These terms alternate and decrease in absolute value, and P_j/Q_j → e. Hence |e − P_j/Q_j| ≤ 2/(Q_jQ_{j+1}) and |δ_j| ≤ 2/Q_{j+1}.

## THM-0003
Case z = a + b(e+1)/2 ∈ L: Q_j a ∈ ℤ, and Q_j b(e+1)/2 = b(P_j + Q_j + δ_j)/2 with P_j + Q_j even. So Q_j z ≡ bδ_j/2 (mod 1), giving ‖Q_j z‖ ≤ |b|/Q_{j+1} and j‖Q_j z‖ → 0.

Case limsup j‖Q_j z‖ < 1/4 ⇒ z ∈ L:
1. Pick c < 1/4 and J ≥ 2 such that for j ≥ J: j‖Q_j z‖ ≤ c and c(4 + 2/j + 1/(j+1) + 1/(j−1)) < 1.
2. Let n_j = round(Q_j z) and y_j = Q_j z − n_j, so |y_j| ≤ c/j. For j ≥ J+1 put m_j = n_{j+1} − (4j+2)n_j − n_{j-1} ∈ ℤ. Then y_{j+1} − (4j+2)y_j − y_{j-1} = −m_j and |m_j| < 1, so m_j = 0.
3. By (F3) applied to the tail j ≥ J (y satisfies the recurrence there), y_j = αQ_j + βδ_j for j ≥ J. [R1 checker fix] Since y_j, δ_j → 0 and Q_j → ∞, α = 0.
4. n_j = γQ_j + εP_j by Cramer's rule with determinant ±2, so 2γ, 2ε ∈ ℤ.
5. (z − γ − βe)Q_j + (β − ε)P_j = 0 at j = J, J+1. The determinant is nonzero, so z = γ + εe = (g + he)/2 with g, h ∈ ℤ.
6. n_J = (gQ_J + hP_J)/2 ∈ ℤ with Q_J, P_J odd, so g + h is even. Then z = (g−h)/2 + h(e+1)/2 ∈ L. ∎

## THM-0004
Lemma: for arcs A_j of length λ_j and E_j = {x ∈ ℝ/ℤ : N_j x ∈ A_j} with N_j = BQ_j, |E_j| = λ_j and ||E_i∩E_j| − |E_i||E_j|| ≤ 2λ_j N_i/N_j for i < j. (E_i is a union of N_i arcs. Count the cells of length 1/N_j meeting or contained in each arc.)
- Convergence: |E_j| = 2ψ(j); apply Borel–Cantelli.
- Divergence: Σ_{i<j≤n}|P(E_iE_j) − P_iP_j| ≤ Σ_j 4ψ(j) Σ_{i<j} 6^{-(j−i)} ≤ (2/5)S_n. So E[X_n²] ≤ S_n + S_n² + (4/5)S_n. Paley–Zygmund gives P(X_n ≥ θS_n) ≥ (1−θ)² S_n²/E[X_n²] → (1−θ)². By reverse Fatou, P(limsup{X_n ≥ θS_n}) ≥ (1−θ)², and on that event X_∞ = ∞, so |W| ≥ (1−θ)². Indices j ≥ 1 (Q_0 = Q_1 duplicates E_1). W is 1-periodic, so measure on ℝ/ℤ transfers to ℝ. [R1 checker fix] Letting θ → 0 gives |W| = 1. ∎

## Relevance to P1
THM-0003 holds for every real z, so it says nothing about π. For z = Bπ, "limsup ≥ 1/4 ∀B" ⇔ P1 (category 3). THM-0004 is metric, so a single point is not excluded.

Categories: THM-0003 is category 5 (independent paper reproduction of the project's corollary3_gap, which is author-reported as kernel-checked). THM-0004 is category 5 (a standard-type lacunary Borel–Cantelli argument; citations 未核到). Numerics: logs/verification/R1/Q-R1-05_c.py (category 4).
