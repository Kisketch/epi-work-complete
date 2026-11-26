<!-- NON-CANONICAL until gate passed / DO NOT CITE -->
# THM-0003 (Theorem A, exact dichotomy) and THM-0004 (Theorem B, metric)
Setup: P_0 = 1, P_1 = 3, Q_0 = Q_1 = 1, and u_{j+1} = (4j+2)u_j + u_{j-1} (j ≥ 1). Given input: P_j/Q_j → e. δ_j = Q_j e − P_j. L = ℤ + ℤ(e+1)/2.
THM-0003: For every real z, either z ∈ L and j‖Q_j z‖ → 0, or z ∉ L and limsup_j j‖Q_j z‖ ≥ 1/4.
THM-0004: For integer B ≥ 1 and ψ: ℕ → [0, 1/2], W(ψ) = {x : ‖BQ_j x‖ < ψ(j) i.o.} is null if Σψ < ∞ and of full measure if Σψ = ∞ (no monotonicity assumption).
Category (AGENTS.md §2): THM-0003 is 5 (paper reproduction of corollary3_gap; Lean claim author-reported, not re-run); with respect to P1 it is 3. THM-0004 is 5 (citations 未核到).
