<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# Round 3 evaluator verdicts
- THM-0005 Lean statement fidelity: PASS. Qsel indexing matches; distToNearestInt = |x − round x|; witness zs = z* (m_j = 1 for even j ≥ 2, no shift). No sorry/axiom/native_decide/unsafe/opaque/set_option in KappaSharp.lean.
- Caveats: (i) axiom tiers are pending the CI `#print axioms` gate; (ii) the subsequence-limit side claim is not formalized; (iii) the EulerConvergents.lean header docstring also calls the deltaSel lemmas axioms (documentation drift; queued).
- Queued doc fix: EulerConvergents.lean header l.19/l.24 still call deltaSel_tendsto_zero / abs_deltaSel_lt "公理化（未验证）"; they are proved theorems (l.514–540). Deferred because editing this low-level file invalidates most of the CI build cache; batch with the next substantive EulerConvergents change.
