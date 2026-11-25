# verify_c2_discrepancy_20261124.py
# Category 4 (finite computation). Supports Remark rem:naive-C2-false in
# split/src_sections/sec-critical-scaling.tex.
#
# Claim checked: for S = {2,3}, the fixed-eta form of the old conjecture C2
# would require kappa/eta == C_S(1). It does not: the ratio is 1.19.
#
# Inputs are the constants recorded by critical_scaling_check_20261124.py
# (kappa, eta) and verify_residue_multi_asymptotic.py (C_S(1)); this script
# only does the arithmetic and prints it, so the assertion is reproducible.
from mpmath import mp, mpf, sqrt

mp.dps = 30

# S = {2,3}: recorded values (critical_scaling_check_20261124_output_v2.md,
# table row [2, 3]; C_S(1) from tab:multi-residue-asymptotic, d=2).
s0 = mpf("0.337436781")
eta = mpf("0.3251264")
kappa = mpf("1.0685189")
C_S_1 = mpf("3.921382875")

ratio = C_S_1 / (kappa / eta)

print("S = {2,3}")
print(f"s0           = {s0}")
print(f"eta=1-2s0    = {eta}")
print(f"kappa(S)     = {kappa}")
print(f"C_S(1)       = {C_S_1}")
print(f"kappa/eta    = {kappa/eta}")
print(f"C_S(1)/(k/eta)= {ratio}")
print()
print("Old fixed-eta C2 would need kappa/eta == C_S(1); ratio != 1, so C2")
print("is false for fixed eta. Consistent with Remark rem:naive-C2-false.")
print()

# Scaling function sanity check: Phi(x) = (-x + sqrt(x^2+4 d kappa))/2 solves
# Phi(Phi+x) = d kappa exactly; Phi(0) = sqrt(d kappa).
for d, x in [(2, mpf("0")), (5, mpf("0")), (5, mpf("1")), (5, mpf("-1"))]:
    Phi = (-x + sqrt(x**2 + 4*d*kappa)) / 2
    resid = Phi*(Phi + x) - d*kappa
    print(f"d={d}, x={x}: Phi={mp.nstr(Phi, 12)}, residual={mp.nstr(resid, 3)}")
