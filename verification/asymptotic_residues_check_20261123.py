"""Falsifiable numerical test of paper 2, thm:residues-asymptotic (iii)-(iv) (2026-11-23).

Claim tested: for fixed r >= 1, as m -> infinity,
    dimH F_{m,r} = 1/2 + C_r/(2m) - C_r^2 log m/(2 m^2) + O(m^-2),   C_r = sum_{n>=0} 1/q_n(r),
    dimH F_{m,m} = 1/2 + 1/(2m)  - log m/(2 m^2)       + O(m^-2),
with q_0 = 1, q_1 = r, q_{n+2} = r q_{n+1} + q_n.  If m^2 * (dim - two-term) were unbounded in m,
the theorem would be false.

Method (NON-RIGOROUS, numerical classification "有限计算"): Chebyshev collocation of the
transfer operator L_s f(x) = sum_{k>=0} (mk+r+x)^{-2s} f(1/(mk+r+x)) on polynomials
f(y) = sum_j b_j y^j, using the exact identity
    L_s(y^j)(x) = m^{-(2s+j)} * zeta(2s+j, (r+x)/m)        (Hurwitz zeta, whole infinite alphabet),
so there is no alphabet truncation.  dimH = the s with spectral radius 1 (Bowen / Mauldin-Urbanski).
Validation: the 20 kernel-checked brackets of tab:residues-general (m=2..6) must contain the
estimates, and estimates at two collocation sizes n must agree.

v2 (2026-11-24): bracketed Illinois root finding on s>1/2, n=16/24, dps=30, streamed per-job output.
Usage: python asymptotic_residues_check_20261123.py [workers]   -> writes .json and .log next to it.
"""
import json
import sys
from fractions import Fraction
from multiprocessing import Pool
from pathlib import Path

from mpmath import mp, mpf, zeta, log, matrix, lu_solve, eig, findroot, chebyt  # noqa: F401

DPS = 30
HERE = Path(__file__).resolve().parent


def nodes(n):
    return [(1 + mp.cos(mp.pi * (2 * i + 1) / (2 * n))) / 2 for i in range(n)]


def rho(m, r, s, n):
    """Spectral radius of the n-point collocation of L_s for the alphabet {mk + r : k >= 0}."""
    xs = nodes(n)
    M = matrix(n, n)
    V = matrix(n, n)
    for i, x in enumerate(xs):
        a = (r + x) / m
        for j in range(n):
            M[i, j] = mpf(m) ** (-(2 * s + j)) * zeta(2 * s + j, a)
            V[i, j] = x ** j
    A = M * V ** -1
    ev = eig(A, left=False, right=False)
    return max(abs(e) for e in ev)


def dim_estimate(m, r, n, guess, width="0.05", iters=60):
    """Bisection root of rho(s) = 1 on s > 1/2 (v2: guaranteed convergence).

    rho is decreasing in s and rho -> infinity as s -> 1/2+ (zeta pole), so a sign change
    exists; the bracket is checked explicitly and widened to (1/2, 0.999) if needed.
    """
    f = lambda s: rho(m, r, s, n) - 1
    lo = max(mpf("0.5") + mpf(10) ** -12, mpf(guess) - mpf(width))
    hi = min(mpf("0.999"), mpf(guess) + mpf(width))
    if not (f(lo) > 0 > f(hi)):
        lo, hi = mpf("0.5") + mpf(10) ** -12, mpf("0.999")
        assert f(lo) > 0 > f(hi), ("no sign change", m, r, n)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def C(r, terms=400):
    q0, q1, tot = mpf(1), mpf(r), mpf(1)
    for _ in range(terms):
        tot += 1 / q1
        q0, q1 = q1, r * q1 + q0
    return tot


def two_term(m, r):
    if r == m:
        return mpf(1) / 2 + mpf(1) / (2 * m) - log(m) / (2 * mpf(m) ** 2)
    c = C(r)
    return mpf(1) / 2 + c / (2 * m) - c ** 2 * log(m) / (2 * mpf(m) ** 2)


def job(args):
    m, r, guess = args
    mp.dps = DPS
    d1 = dim_estimate(m, r, 16, guess)
    d2 = dim_estimate(m, r, 24, d1, width="0.0005")
    tt = two_term(m, r) if (r == m or m > 2 * r) else None
    out = dict(m=m, r=r, dim_n18=str(d1), dim_n26=str(d2), n_diff=float(abs(d1 - d2)))  # keys kept; n=16/24 in v2
    if tt is not None:
        out.update(two_term=str(tt), m2_residual=float((d2 - tt) * m * m),
                   m_excess=float((d2 - mpf(1) / 2) * m))
    return out


def main():
    mp.dps = DPS
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    cert = json.loads((HERE / "residue_certificate_general_N512.json").read_text())["certificates"]
    jobs = [(e["modulus"], e["residue"], (Fraction(e["lower"]) + Fraction(e["upper"])) / 2) for e in cert]
    ms = [8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024]
    for m in ms:
        for r in (1, 2, 3, m):
            g = two_term(m, r) if (r == m or m > 2 * r) else mpf("0.55")
            jobs.append((m, r, float(g)))
    stem = HERE / "asymptotic_residues_check_20261123"
    part = stem.with_suffix(".partial.jsonl")
    part.write_text("")
    done = {}
    with Pool(workers) as p:  # v2: results streamed to disk as they finish
        for rr in p.imap_unordered(job, [(m, r, float(g)) for m, r, g in jobs]):
            done[(rr["m"], rr["r"])] = rr
            with open(part, "a") as fh:
                fh.write(json.dumps(rr) + "\n")
    res = [done[(m, r)] for m, r, _ in jobs]
    lines = ["# NON-RIGOROUS collocation estimates (mpmath dps=%d); classification: 有限计算 / numerical evidence" % DPS]
    ok = True
    for e, rr in zip(cert, res[:len(cert)]):
        lo, up = Fraction(e["lower"]), Fraction(e["upper"])
        d = Fraction(rr["dim_n26"][:30])
        inside = lo <= d <= up
        ok &= inside
        lines.append(f"validate m={e['modulus']} r={e['residue']}: est={float(d):.12f} in "
                     f"[{float(lo):.6f},{float(up):.6f}] -> {inside}; |n18-n26|={rr['n_diff']:.1e}")
    lines.append(f"VALIDATION {'PASS' if ok else 'FAIL'} (all 20 kernel-checked brackets contain the estimates)")
    for rr in res[len(cert):]:
        if "m2_residual" in rr:
            lines.append(f"m={rr['m']:5d} r={'m' if rr['r'] == rr['m'] else rr['r']}: dim={float(mpf(rr['dim_n26'])):.12f} "
                         f"two-term={float(mpf(rr['two_term'])):.12f} m^2*resid={rr['m2_residual']:+.6f} "
                         f"m*(dim-1/2)={rr['m_excess']:.6f} |n18-n26|={rr['n_diff']:.1e}")
    for r in (1, 2, 3):
        lines.append(f"C_{r}/2 = {float(C(r) / 2):.10f}   (limit of m*(dim F_m,r - 1/2))")
    lines.append("limit of m*(dim F_m,m - 1/2) should be 1/2")
    stem.with_suffix(".json").write_text(json.dumps(res, indent=1))
    stem.with_suffix(".log").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
