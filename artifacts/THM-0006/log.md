<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# THM-0006 log (generated from the append-only ledgers; ledgers are authoritative)

- [ledger-R2.jsonl] Q-R2-03 — OPEN (prev None): dispatch worker
- [ledger-R2.jsonl] Q-R2-03 — PARTIAL (prev OPEN): complete proof returned; awaiting double-check
- [ledger-R2.jsonl] Q-R2-03 — PROVED (prev PARTIAL): double-check gate: R2-c PASS, R2-d PASS (edge cases Q_0=0, D<0, a_j=1 finitely often); paper proof
- [ledger-R2.jsonl] THM-0005,THM-0006 — NEEDS-LEAN (prev PROVED): evaluator PASS on paper; THM-0005 category 1 candidate (novelty unchecked); THM-0006 category 5
- [ledger-R4.jsonl] THM-0006 — NEEDS-LEAN (prev NEEDS-LEAN): standalone module (narrow Mathlib imports) checked locally by formalizer: base+whitelist axioms only (sanity_D: propext only); not formalized: irrationality of theta, part (C) weights, rank/index of L; awaiting CI full build + gate
- [ledger-R4.jsonl] THM-0006 — PROVED (prev NEEDS-LEAN): CI run 45763704930: full build 9393 jobs; gate PASS; base+whitelist axioms; fidelity PASS (partial scope: (C), structure of L not formalized)
