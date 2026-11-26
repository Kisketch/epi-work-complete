<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# Blueprint v1 (frozen 2026-11-25, Round 1)

## Target
P1: ∀B∈ℕ, B≥1 ⇒ Bπ ∉ L, where L = ℤ + ℤ(e+1)/2.

## Definitions
D1 L (Classification.latticeL). D2 Q_j, the selected e-convergent denominators, with Q_{j+1}=(4j+2)Q_j+Q_{j-1}. D3 ‖·‖, the distance to the nearest integer. D4 F_τ = {x∈[0,1]: ‖Q_j x‖ = O(j^{-τ})}.

## Nodes and DAG
- N1 [kernel, author-reported] corollary3_gap: x∉L ⇒ limsup j‖Q_j x‖ ≥ 1/4.
- N2 [kernel, author-reported] reduction_to_lattice; P1_imp_irrational (depends on N1).
- N3 [paper] Rational span: ⋃_B B⁻¹L = ℚ+ℚe. **THM-0001 candidate.**
- N4 [paper ⇒ from N3] P1 ⇔ LinearIndependent ℚ ![1,e,π]. **THM-0001.**
- N5 [paper] thm:eventual-dimension: dim_H F_τ = max(1−τ, 0). **THM-0002 candidate.** Independent of N1–N4.
- N6 [OPEN, core] π ∉ ℚ+ℚe. Equivalent to P1 via N4. Open problem; no known route.
- N7 [route audit] Each of the 8 audited routes in Paper 1 §feasibility → route eliminated or OPEN.

DAG: N1→N2; N3→N4; N4,N6→P1; N5 is independent; N7 audits N6.

## Round 1 goals
G1 Double-checked written proof of N3/N4 (THM-0001).
G2 Line-by-line check of the N5 paper proof (THM-0002).
G3 One blind attempt wave on N6 to classify failure modes; the expected outcome is OPEN.
