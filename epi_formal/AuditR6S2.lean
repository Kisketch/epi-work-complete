import EpiFormal.R6S2Main
/-! Audit entry for R6-S2 (main theorem) and R6-S1 (a)–(d). Each line must print only
`[propext, Classical.choice, Quot.sound]` (or a subset). -/
#print axioms R6S2.main
#print axioms R6S2.lower
#print axioms R6S2.upper
#print axioms R6S2.S1_all
#print axioms R6S2.S1a
#print axioms R6S2.S1b
#print axioms R6S2.S1c
#print axioms R6S2.S1d
#print axioms R6S2.lemma0
#print axioms R6S2.cor0'
#print axioms R6S2.cstar_ge_quarter_irrational
#print axioms R6S2.cstar_only_W'
#print axioms R6S2.nu_bounds
#print axioms R6S2.main_example11
#print axioms R6S2.nu_one_one
#print axioms R6S2.cstar_example11

/-! Statement pin: the main theorem proves literally the aligned statement of `R6S2Kl.lean`. -/
open R6S2 in
example : ∀ X : BH, cstar X.a = ENNReal.ofReal (R6S7.nu X.W) ∧
    ∃ β : ℝ, β ∉ lattice (alpha X.a) ∧ KL X.a β = ENNReal.ofReal (R6S7.nu X.W) := main
