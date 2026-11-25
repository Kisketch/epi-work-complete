-- Independent audit entry for the unconditional core-axiom proof of μ(e) = 2 (2026-11-25).
-- Not part of Audit.lean (937-entry bijection untouched). Run: lake env lean AuditMuEEqTwo.lean
import EpiFormal.MuEEqTwo

#print axioms MuEEqTwo.Psel_Qsel_coprime
#print axioms MuEEqTwo.two_pow_le_Qsel
#print axioms MuEEqTwo.Qsel_succ_le
#print axioms MuEEqTwo.inv_Qsel_succ_le_abs_deltaSel
#print axioms MuEEqTwo.exists_Qsel_bracket
#print axioms MuEEqTwo.abs_exp_sub_rat_ge
#print axioms MuEEqTwo.two_le_mu_e
#print axioms MuEEqTwo.mu_e_le_two
#print axioms mu_e_eq_two_proved
