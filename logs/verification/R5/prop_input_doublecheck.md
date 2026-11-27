<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# Double-check of prop:input (THM-0005 note, Section sec:input) — R5, 2026-11-26

Two independent Sonnet checkers, read-only, each with its own instructions.

| Checker | Scope | Verdict | Issues raised |
|---|---|---|---|
| A (adversarial, line by line) | proof of prop:input; KL comparison remark; circularity; residual "unproved" wording | PASS-with-minor-fixes | (1) CF uniqueness used tails x_k without proving they converge; (2) "Numerically, θ_j(4j+2)→1 …" sentence was stale after the limit was proved; (3) θ_j = Q_j‖Q_jα‖ and the complete-quotient identity need j ≥ 1; (4) optional: make the hypotheses explicit when citing prop:dich(d) |
| B (independent re-derivation + reran script + honesty audit) | re-derived proof blind, then compared; ran input_prop_chk.py (output identical to .out); AGENTS.md honesty audit | PASS-with-minor-fixes | (1) same tails gap; (2) same j ≥ 1 indexing; (3) abstract should say the CF identification is paper-only; (4) script tested the weaker bound e/(4^j j!) instead of (e−1)/(4^j j!) |

Both checkers found no circularity: prop:dich does not use sec:input. Both found no overclaim (no novelty claimed for the classical expansion; Lean claims match LEAN-THM-0005.log; nothing about π or e+π).

All issues fixed in commit 73c9ec1:
- the tails' convergence is proved via the determinant relation, q'_k → ∞, and the alternating-series argument of prop:dich(c), then x_k = c_k + 1/x_{k+1} by passing to the limit;
- irrationality is now argued directly from (i), with prop:dich(d) as an explicit alternative;
- the KL remark is restricted to j ≥ 1 with explicit bounds 4j+2 < 1/θ_j < 4j+4;
- the stale numerics sentence is rewritten (monotonicity of jθ_j/4 not proved);
- the abstract states the identification is paper-only;
- the script checks (e−1)/(4^j j!) and was rerun, with all checks True.

Not checked by either checker: the full texts of KL/Larcher/BDS citations (no source opened in R5).
