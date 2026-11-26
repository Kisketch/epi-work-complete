<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# Siege Protocol (SKILL)

## Roles (all subagents: model "sonnet", spawned per call via the Agent tool)
| Agent | Tools (enforced by prompt) | Isolation | Job |
|---|---|---|---|
| siege-judge | Read/Write/Grep/Glob | none | Writes self-contained queries; appends ledger lines. One step per launch. |
| siege-worker | Read/Grep/Glob, Bash(lean/lake/python verify only), no canonical writes | worktree | Answers one query; returns the final answer only. |
| siege-worker-deep | same, larger budget | worktree | Escalation rounds only. |
| lean-formalizer | Read/Write/Edit/Bash/Grep/Glob | worktree | THM → Lean, one step at a time (lean-proof skill). |
| fresh-evaluator | Read/Grep | none | PASS / FAIL / NEEDS-LEAN from the clean statement plus evidence paths only. |
| registry-clerk | Read, Write to registry/shards only | none | Merges shards. |

Implementation note: the host Agent tool takes no programmatic `agents` definitions. Each role is passed as `subagent_type: general-purpose` with an explicit `model: "sonnet"` and a role prompt carrying the tool restrictions above.

## Loop per round
Judge → worker wave (parallel, blind) → double-check gate (2 fresh checkers per claimed complete proof) → escalation (from round 3: deep workers; ≥ all-but-2 queries on the single missing statement) → fresh-evaluator → finalization (proof.md with Status) → handoff `logs/handoffs/ROUND-<id>.md` plus `logs/MEMORY.md`.

## Lean gate (all required)
Pinned toolchain; `lake build` clean; `rg -n "\bsorry\b|\badmit\b" lean/` returns only registered exceptions; `#print axioms` lists no unregistered axiom; the statement maps 1:1 to statement.md; `logs/verification/LEAN-<id>.log` exists; fresh-evaluator returns PASS.

## Ledger
`logs/ledger/ledger-<round>.jsonl`, append-only. Fields: Q-ID, statement, round, worker, status, evidence_path, checker_1, checker_1_result, checker_2, checker_2_result, failure_class, next_action. Status changes append a new line with `prev_status` and `reason`.

## Failure taxonomy
route error / granularity error / formalization-interface error / missing literature / missing certificate / context drift / premature convergence / Lean unreachable.

## Honesty overlay (AGENTS.md takes precedence)
Every result carries one of the 5 categories. P1 ⇔ ℚ-linear independence of {1, e, π}, which is open. No worker output can mark P1 PROVED without the double-check gate, and any such claim triggers additional adversarial review because the prior probability of a correct proof is negligible.

## Handoff template
Ledger delta | gates closed | OPEN steps + why | failure counts | blueprint changes | evaluator verdicts | commander decisions needed | next-round recommendation.
