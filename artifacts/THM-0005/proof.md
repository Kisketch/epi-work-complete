<!-- NON-CANONICAL until gate passed / DO NOT CITE -->
# THM-0005 Proof (worker Q-R2-01, Round 2)
Facts (index ranges: G1 for j ≥ 1, G2 for j ≥ 2; J ≥ 4 even, S_0 = 0): (G1) (4j+2)Q_j ≤ Q_{j+1} ≤ (4j+3)Q_j for j ≥ 1. (G2) Q_{j+1} ≥ (4j+2)(4j−2)Q_{j-1}. (G3) Σ_{i≥i_0} 1/Q_{i+1} ≤ (6/5)/Q_{i_0+1} (ratio ≥ 6).

Lower bound κ ≥ 1/4: this is THM-0003 (artifacts/THM-0003/proof.md).

Upper bound and attainment:
1. Define n_j as in the statement. E_j := n_{j+1}Q_j − n_jQ_{j+1} satisfies E_j = −E_{j-1} + m_jQ_j with E_0 = 0. Hence E_j = (−1)^j S_j with S_j = Σ_{even i, 2≤i≤j} Q_i.
2. By (G1), Q_i/Q_{i-2} ≥ 36 for even i ≥ 4 (actual minimum 143; Q_0 does not occur in S_j) [R2 checker fix], so Q_{j'} ≤ S_j ≤ (36/35)Q_{j'}, where j' is the largest even index ≤ j.
3. n_{j+1}/Q_{j+1} − n_j/Q_j = E_j/(Q_jQ_{j+1}), and |·| ≤ (36/35)/Q_{j+1} is summable, so z* exists. Writing t_i = S_i/(Q_iQ_{i+1}), y_j := Q_jz* − n_j = Q_j Σ_{i≥j} (−1)^i t_i.
4. Tail: Σ_{i>j} t_i ≤ (36/35)Σ_{i>j}1/Q_{i+1} ≤ (36/35)(6/5)/Q_{j+2} ≤ 1.24/Q_{j+2} (G3). [R2 checker fix]
5. Even J: t_J = (Q_J + S_{J-2})/(Q_JQ_{J+1}) with S_{J-2} ≤ 1.03Q_{J-2}. So y_J = (Q_J/Q_{J+1})(1 + η_J) with |η_J| ≤ 1.03/((4J−2)(4J−6)) + 1.24/(4J+2) → 0. For large J, 0 < y_J < 1/2, so ‖Q_Jz*‖ = y_J and J‖Q_Jz*‖ → 1/4.
6. Odd j: S_j = S_{j-1} ≤ 1.03Q_{j-1}, so |y_j| ≤ 1.03Q_{j-1}/Q_{j+1} + 1.24Q_j/Q_{j+2} = O(1/j²). Hence j‖Q_jz*‖ → 0.
7. Therefore limsup = 1/4 > 0. By the L-half of THM-0003 (z ∈ L ⇒ j‖Q_jz‖ → 0), z* ∉ L. So κ ≤ 1/4, and κ = 1/4 is attained. ∎

Numerics (category 4): logs/verification/R2/R2_01_even_defects.py. z* ≈ 0.014041639566949028405640892454. J‖Q_Jz*‖ = 0.2439 at J = 20 and 0.24793 at J = 60; odd j values are ~j^{-2}.
Dependency: the lower bound rests on THM-0003 (paper proof, double-checked). Does NOT: say anything about π or e+π. It is a sharpness statement for the single family Q_j z.
