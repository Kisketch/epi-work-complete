<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# THM-0005 log (generated from the append-only ledgers; ledgers are authoritative)

- [ledger-R2.jsonl] Q-R2-01 — OPEN (prev None): dispatch worker
- [ledger-R2.jsonl] Q-R2-01 — PARTIAL (prev OPEN): complete proof returned; awaiting double-check
- [ledger-R2.jsonl] Q-R2-01 — PROVED (prev PARTIAL): double-check gate: R2-a PASS, R2-b PASS (sign of y_J, tail, z* notin L checked; 1500-digit numerics); paper proof; novelty unchecked
- [ledger-R2.jsonl] THM-0005,THM-0006 — NEEDS-LEAN (prev PROVED): evaluator PASS on paper; THM-0005 category 1 candidate (novelty unchecked); THM-0006 category 5
- [ledger-R2.jsonl] Q-R2-04 — PARTIAL (prev OPEN): near precedent: Kraaikamp-Liardet 1991 lemma (secondary statements verified; original full text 403). THM-0003/0006 same family; THM-0005 no precedent found (negative search only)
- [ledger-R3.jsonl] Q-R3-01 — PARTIAL (prev OPEN): metadata verified; full text blocked (paywall/Cloudflare, not bypassed); KL paraphrase is bounded-type only; BDS 2001 read (open access), no sharp constant
- [ledger-R3.jsonl] THM-0005 — NEEDS-LEAN (prev NEEDS-LEAN): source complete, no sorry/admit/axiom; checked only against a shim (stubbed Classification theorems) because native import of Mathlib exceeded 590s under memory pressure; real-project compile delegated to GitHub CI (full lake build + siege axiom gate)
- [ledger-R3.jsonl] THM-0005 — PROVED (prev NEEDS-LEAN): Lean gate PASS via CI run 45759959535: full lake build 9392 jobs; base+whitelist axioms only; no sorry; statement fidelity PASS (fresh-evaluator)
- [ledger-R4.jsonl] PAPER-NOTE-0005 — PARTIAL (prev OPEN): double-check: math checker PASS all sections (numerics reproduced; KL 1/16 confirmed numerically); honesty checker FAIL->fixed (title, abstract qualification, Psel evidence logged, gate-scope wording); LaTeX balanced but NOT compiled (no TeX locally)
