from fractions import Fraction
import json
import os
import pathlib
import sys
import mpmath as mp

mp.mp.dps = 50

print("=== 1. PAPER 2 TAB:RESIDUES-GENERAL EXACT RATIONALS vs BENCHMARKS ===")
p2_brackets = [
    (2, 1, Fraction(105, 128), Fraction(421, 512)),
    (2, 2, Fraction(23, 32), Fraction(369, 512)),
    (3, 1, Fraction(95, 128), Fraction(381, 512)),
    (3, 3, Fraction(41, 64), Fraction(329, 512)),
    (4, 1, Fraction(357, 512), Fraction(179, 256)),
    (4, 4, Fraction(309, 512), Fraction(155, 256)),
    (5, 1, Fraction(171, 256), Fraction(343, 512)),
    (5, 5, Fraction(149, 256), Fraction(299, 512)),
    (6, 1, Fraction(331, 512), Fraction(83, 128)),
    (6, 6, Fraction(291, 512), Fraction(73, 128)),
]
for m, r, lo, hi in p2_brackets:
    print(f"F_{{{m},{r}}}: [{lo}={float(lo):.9f}, {hi}={float(hi):.9f}], width={hi-lo}")

print("CLU {1,4,7,...} bound 0.743586 inside F_{3,1} bracket?:", float(Fraction(95, 128)) <= 0.743586 <= float(Fraction(381, 512)))

cln_12 = (0.531277, 0.531281)
brown_12 = (0.531280506277203, 0.531280506277205)
print("Brown {1,2} nested in CLN {1,2}?:", cln_12[0] <= brown_12[0] <= brown_12[1] <= cln_12[1])
print("Paper 2 s0({1,2}) ~ 0.531280506 inside Brown {1,2} to 9 digits?:", abs(0.531280506 - brown_12[0]) < 1e-9)

cluw_2dcf = (1.149576 - 5.5e-6, 1.149576 + 5.5e-6)
brown_2dcf = (1.14955, 1.14959)
print(f"CLUW 2D CF: [{cluw_2dcf[0]:.7f}, {cluw_2dcf[1]:.7f}] nested in Brown 2D CF {brown_2dcf}?:",
      brown_2dcf[0] <= cluw_2dcf[0] <= cluw_2dcf[1] <= brown_2dcf[1])

print("\n=== 2. ZETA & FLINT HILLS CONSTANTS (50-DIGIT MPMATH) ===")
flsz_lhs = mp.sqrt(4 * mp.zeta(2) * mp.zeta(3) / mp.zeta(6))
flsz_rhs = 3 * mp.sqrt(70 * mp.zeta(3)) / (mp.pi ** 2)
print("FLSZ sqrt(4*z2*z3/z6)     =", mp.nstr(flsz_lhs, 20))
print("FLSZ 3*sqrt(70*z3)/pi^2   =", mp.nstr(flsz_rhs, 20))
print("FLSZ |lhs - rhs|          =", mp.nstr(abs(flsz_lhs - flsz_rhs), 10))

lam = Fraction(37, 40)
eps = Fraction(79, 1600)
c = Fraction(75, 4)
rho_fauzan = Fraction(6933, 500)
rho_giraudin = Fraction(909, 100)
print("Giraudin eps - lam/c      =", eps - lam / c, "(expected 1/24000)")
print("Fauzan rho*lam/eps        =", rho_fauzan * lam / eps, "=", float(rho_fauzan * lam / eps))
print("Fauzan rho*c              =", rho_fauzan * c, "=", float(rho_fauzan * c))
print("Giraudin rho*lam/eps      =", rho_giraudin * lam / eps, "=", float(rho_giraudin * lam / eps))
print("Giraudin rho*c            =", rho_giraudin * c, "=", float(rho_giraudin * c))

M_zz = mp.mpf("7.103205334137")
M_bai = mp.mpf("7.101862832357")
s_zz = 2 * (M_zz - 1)
s_bai = 2 * (M_bai - 1)
print("Flint Hills t=2 window ZZ =", mp.nstr(s_zz, 15), "dim(D_{s,2}) =", mp.nstr(4 / (s_zz + 2), 12))
print("Flint Hills t=2 window Bai=", mp.nstr(s_bai, 15), "dim(D_{s,2}) =", mp.nstr(4 / (s_bai + 2), 12))

print("\n=== 3. DEDUPLICATED CACHE COUNTS ===")
cache_arg = sys.argv[1] if len(sys.argv) > 1 else os.environ.get("EVIDENCE_CACHE_DIR", "").strip()
scratch = pathlib.Path(cache_arg) if cache_arg else None
if scratch and scratch.exists():
    for name in ["arxiv_verified.json", "load_bearing_graph_audit.json", "extra_load_bearing_audit.json", "extra_audit_round2.json", "verify_conflicts_and_github.json"]:
        p = scratch / name
        if p.exists():
            d = json.loads(p.read_text(encoding="utf-8"))
            if isinstance(d, list):
                print(f"{name}: list len={len(d)}")
            elif isinstance(d, dict):
                summary = {k: (len(v) if isinstance(v, (list, dict)) else type(v).__name__) for k, v in d.items()}
                print(f"{name}: {summary}")
        else:
            print(f"{name}: NOT PRESENT IN CACHE DIR")
else:
    print("External scratch JSON cache skipped (pass path arg or set EVIDENCE_CACHE_DIR to inspect).")
