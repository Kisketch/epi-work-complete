<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# Full-text check (user-supplied PDFs; not stored in repo), 2026-11-25

## Verified from full text
- **Kraaikamp, Liardet**, "Good approximations and continued fractions", Proc. Amer. Math. Soc. 112 (1991), no. 2, 303–309. (DOI 10.1090/S0002-9939-1991-1062392-7 from Crossref; not printed on the PDF.)
  - Thm 1: β ∈ αℤ+ℤ ⇔ ∃n_0 ∀n ≥ n_0, ‖q_nβ‖ ≤ θ_n/4, with θ_n = q_n‖q_nα‖.
  - Thm 1′: β ∈ αℤ+ℤ ⇔ ‖q_nβ‖ = o(θ_n).
  - Thm 2: bounded type ⇒ β ∈ αℚ+ℚ ⇔ finitely many limit points.
  - Thm 3 and Prop.: E(α) is uncountable iff α is unbounded.
  - No sharpness example and no optimality claim for 1/4.
- **Larcher**, "A convergence problem connected with continued fractions", Proc. Amer. Math. Soc. 103 (1988), no. 3, 718–722.
  - Thm 1: bounded type ⇒ (‖q_nβ‖ → 0 ⇔ β ∈ ℤα+ℤ).
  - Thm 2: counterexample for unbounded partial quotients.
  - Lemma 1 constant 1/(4K). No sharpness.
- **Philipp**, "Some metrical theorems in number theory", Pacific J. Math. 20 (1967), no. 1, 109–127 (last numbered page seen: 127).
  - Thm 2A/B/C: counting for T x = {ax} (integer a > 1), the Gauss map, and {θx}, with arbitrary intervals I_n (no monotonicity).
  - Thm 3: quasi-independence |E_n∩E_m| ≤ |E_n||E_m| + |E_n|C_{n−m}, ΣC_k < ∞.
  - No statement for general lacunary n_k or for BQ_j.

## Key structural fact (numerical, category 4)
Q_j (THM-0003) equal the regular-CF denominators q_j of α = (e−1)/2 = [0;1,6,10,14,…] (checked for 14 partial quotients / 12 denominators at 400 digits). So L = ℤ + ℤ(e+1)/2 = αℤ + ℤ. The classical CF of (e−1)/2 is 未核到 (source not opened).

## Label consequences (commander decision)
| Result | New label | Reason |
|---|---|---|
| THM-0003 | category 5; the dichotomy is implied by KL Thm 1′. Our constant (limsup j‖Q_jz‖ ≥ 1/4, i.e. a_j-weight threshold 1) is 4× KL's 1/16 | KL full text |
| THM-0004 | category 5; precedent 未核到; Philipp does NOT cover BQ_j | Philipp full text |
| THM-0005 | category 1 candidate: sharpness of the improved constant; negative search (KL, Larcher, Philipp) only | full texts |
| THM-0006 | category 5 for D = ±1 CF case (KL Thm 1′); threshold 1 (vs KL 1/4·θ) and weight form (C) are improvements, candidate pending Stewart etc. | KL full text |
Not opened: Stewart [KL ref S, Thm 3]; Eggleston; Erdős–Taylor.
