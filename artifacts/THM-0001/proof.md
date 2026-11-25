<!-- NON-CANONICAL until gate passed / DO NOT CITE -->
# THM-0001 Proof (worker Q-R1-01, Round 1)

## (a) ⋃_{B≥1} B⁻¹L = ℚ+ℚe
⊆: If Bx = a + b(e+1)/2 with a, b ∈ ℤ, then x = (a + b/2)/B + (b/(2B))e ∈ ℚ+ℚe.
⊇: Let x = r + se with r, s ∈ ℚ. Take B = lcm(den r, den s) ≥ 1, so Br, Bs ∈ ℤ. Then
Bx = B(r−s) + 2Bs·(e+1)/2, because B(r−s) + Bs(e+1) = Br + Bse.
Here B(r−s) = Br − Bs ∈ ℤ and 2Bs ∈ ℤ, so Bx ∈ L. ∎

## (b)
Step 0. For B ≥ 1, Bπ ∈ L ⇔ π ∈ B⁻¹L. Hence ¬P1 ⇔ π ∈ ⋃B⁻¹L = ℚ+ℚe, so P1 ⇔ π ∉ ℚ+ℚe.

(Independence ⇒ P1.) If P1 fails, then π = r + se with r, s ∈ ℚ. This gives (−r)·1 + (−s)·e + 1·π = 0, a nontrivial relation, which is a contradiction.

(P1 ⇒ independence.) Suppose p + qe + tπ = 0 with p, q, t ∈ ℚ.
- If t ≠ 0, then π = −(p+qe)/t ∈ ℚ+ℚe, which contradicts P1.
- If t = 0 and q ≠ 0, then e = −p/q ∈ ℚ, which contradicts the irrationality of e.
- If t = q = 0, then p = 0.
Hence p = q = t = 0. ∎

Corollary (paper's final sentence): if B(e+π) = A with A ∈ ℤ and B ∈ ℤ≥1, then Bπ = (A+B) − 2B·(e+1)/2 ∈ L. So P1 ⇒ e+π ∉ ℚ. This is one direction only.

## Gaps noted in the paper's original text (repairable, none fatal)
1. "Nontrivial" is undefined.
2. The t = 0 case is compressed.
3. The reduction P1 ⇔ π ∉ ℚ+ℚe is not written out.
4. The notation mixes B ∈ ℕ and B ≥ 1.
5. "Clearing denominators" is unspecific.
6. A ∈ ℤ is implicit.
7. ⊆ is asserted without computation.

## What this does NOT do
It does not prove P1. It does not touch e+π irrationality, which remains open. It is an equivalent restatement only.
