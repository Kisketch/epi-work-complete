<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
Round 1: worker#01 wrote the proof. Checker#1 PASS (cosmetic: say "assume independence"; state A∈ℤ, B≥1). Checker#2 PASS. Lean gate BLOCKED (environment). Category 3.

- [ledger-R1.jsonl] Q-R1-01 — OPEN (prev None): dispatch worker
- [ledger-R1.jsonl] Q-R1-01 — PARTIAL (prev OPEN): complete written proof returned; awaiting double-check gate
- [ledger-R1.jsonl] Q-R1-01 — PROVED (prev PARTIAL): double-check gate: checker#1 PASS (cosmetic only), checker#2 PASS (edge cases r=0,s=0,B<0 checked); paper proof only, Lean gate blocked
- [ledger-R1.jsonl] THM-0001..0004 — NEEDS-LEAN (prev PROVED): evaluator: paper proofs correct, categories honest; canonical admission needs Lean gate (environment BLOCKED)
- [ledger-R2.jsonl] THM-0001 — PROVED (prev NEEDS-LEAN): Lean gate PASS (module-level build; key theorem base+whitelist axioms only; sorry grep empty; evaluator PASS)
