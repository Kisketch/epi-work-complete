-- Independent audit entry for PerronFrobenius (2026-11-25).
-- Not part of Audit.lean (937-entry bijection untouched). Run: lake env lean AuditPerronFrobenius.lean
import EpiFormal.PerronFrobenius

/-!
# Independent Axiom Audit for `EpiFormal.PerronFrobenius`

Exports `#print axioms` across:
1. Matrix operators & Perron eigenvalue uniqueness (`PerronFrobenius.perron_eigenvalue_unique`)
2. Brouwer-free Perron-Frobenius theorems (`perron_frobenius_pos`, `perron_frobenius_ge_one`)
3. Unconditional finite-state tail theorems (`FiniteStateUnconditional.*`) on `ℝ` and `UnitAddCircle`
-/

-- Part 1: Matrix operators & eigenvalue uniqueness
#print axioms PerronFrobenius.matPow_succ_right
#print axioms PerronFrobenius.matPow_nonneg
#print axioms PerronFrobenius.linOp_matPow_eigenvector
#print axioms PerronFrobenius.perron_eigenvalue_unique

-- Part 2: Brouwer-free finite-dimensional Perron-Frobenius
#print axioms PerronFrobenius.perron_frobenius_pos
#print axioms PerronFrobenius.perron_frobenius_ge_one

-- Part 3: Unconditional finite-state tail theorems (ℝ and UnitAddCircle)
#print axioms FiniteStateUnconditional.markedComponent_perron_eigenvector
#print axioms FiniteStateUnconditional.componentPerronRoot
#print axioms FiniteStateUnconditional.thm_finite_state_tail_joint_unconditional
#print axioms FiniteStateUnconditional.thm_finite_state_tail_unconditional
#print axioms FiniteStateUnconditional.thm_finite_state_tail_circle_unconditional
#print axioms FiniteStateUnconditional.thm_finite_state_tail_trichotomy
#print axioms FiniteStateUnconditional.thm_finite_state_tail_circle_trichotomy
