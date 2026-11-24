import EpiFormal.ResidueMultiAsymptotic

/-!
# Independent Axiom Audit for `EpiFormal.ResidueMultiAsymptotic`

Exports `#print axioms` across Parts 1–6 (continuant multiplicativity, Bowen-free
Poincaré-abscissa dimension, multi-residue phase transition, Euler–Mascheroni expansion,
master three-term subcritical asymptotics, and supercritical power-law convergence rate).
-/

-- Part 1: Continuant multiplicativity & Poincaré abscissa
#print axioms ResidueMultiAsymptotic.wordSum_add_le
#print axioms ResidueMultiAsymptotic.wordSum_add_ge
#print axioms ResidueMultiAsymptotic.summable_wordSum_of_poincareAbscissa_lt
#print axioms ResidueMultiAsymptotic.not_summable_wordSum_of_lt_poincareAbscissa
#print axioms ResidueMultiAsymptotic.one_le_wordSum_poincareAbscissa
#print axioms ResidueMultiAsymptotic.wordSum_poincareAbscissa_le

-- Part 2: Multi-branch resolvent & Bowen-free Poincaré-abscissa dimension
#print axioms ResidueMultiAsymptotic.multiResolventV_branch_eq
#print axioms ResidueMultiAsymptotic.dimH_cfAlphabetSet_finset_eq_poincareAbscissa

-- Part 3: Multi-residue phase transition at 1/2 & concrete witnesses
#print axioms ResidueMultiAsymptotic.tendsto_dimH_multiResidueSet
#print axioms ResidueMultiAsymptotic.subcritical_pair_two_three
#print axioms ResidueMultiAsymptotic.supercritical_pair_one_two

-- Part 4: Euler–Mascheroni zeta expansion & logarithmic moments
#print axioms ResidueMultiAsymptotic.abs_tsum_rpow_sub_inv_sub_eulerMascheroni_le
#print axioms ResidueMultiAsymptotic.multiC_one_add_bounds

-- Part 5: Master three-term subcritical asymptotics & single/two-digit corollaries
#print axioms ResidueMultiAsymptotic.dimH_multiResidueSet_asymp_three_term
#print axioms ResidueMultiAsymptotic.tendsto_m2_residual_multiResidue
#print axioms ResidueMultiAsymptotic.tendsto_dimH_multiResidue_ratio
#print axioms ResidueMultiAsymptotic.dimH_residueConstSet_asymp_three_term
#print axioms ResidueMultiAsymptotic.dimH_residueConstSet_mm_asymp_three_term
#print axioms ResidueMultiAsymptotic.dimH_multiResidueSet_two_three_asymp

-- Part 6: Supercritical power-law convergence rate Θ(m^(-2 s₀))
#print axioms ResidueMultiAsymptotic.multiC_supercritical_le
#print axioms ResidueMultiAsymptotic.dimH_multiResidueSet_supercritical_upper
#print axioms ResidueMultiAsymptotic.dimH_multiResidueSet_supercritical_lower
#print axioms ResidueMultiAsymptotic.dimH_multiResidueSet_supercritical_rate
#print axioms ResidueMultiAsymptotic.dimH_multiResidueSet_one_two_supercritical_rate
