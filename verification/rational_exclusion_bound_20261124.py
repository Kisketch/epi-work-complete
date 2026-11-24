"""Rigorous finite exclusion: "if X = p/q then q >= Q_min", X in {e+pi, e*pi, e-pi, pi/e} (2026-11-24).

Classification (AGENTS.md): 有限计算或有限排除 -- it excludes rationals with small denominators
only and says nothing about irrationality.

Method.
1. Arb ball arithmetic (python-flint) gives an interval I = [lo, hi] with exact dyadic endpoints
   that rigorously contains X (Arb's error bounds are rigorous by construction).
2. If X = p/q then p/q lies in I, hence q >= den(s), where s is the unique rational of minimal
   denominator in I (the Stern-Brocot "simplest" rational).  s is computed EXACTLY from the
   rational endpoints by the classical continued-fraction algorithm for the simplest rational in a
   closed interval, using GMP integers (gmpy2 if present, else Python ints).
3. Hence: X is not a rational number with denominator < den(s).

Self-test (--selftest): at small precision the simplest rational is recomputed with an independent
fractions.Fraction implementation and the common continued-fraction prefix is compared with
mpmath's identify-free CF of a 3x-higher-precision value; all must agree.

Usage:  python rational_exclusion_bound_20261124.py --selftest
        python rational_exclusion_bound_20261124.py CONST DIGITS [--out FILE]
CONST in {epi_sum, epi_prod, epi_diff, pi_over_e}.  Appends one JSON line per run to --out.
"""
import json
import math
import sys
import time
from fractions import Fraction

import flint

try:
    import gmpy2
    Z = gmpy2.mpz
except ImportError:  # pragma: no cover
    gmpy2 = None
    Z = int

CONSTS = {
    "epi_sum": lambda: flint.arb.pi() + flint.arb(1).exp(),
    "epi_prod": lambda: flint.arb.pi() * flint.arb(1).exp(),
    "epi_diff": lambda: flint.arb.pi() - flint.arb(1).exp(),
    "pi_over_e": lambda: flint.arb.pi() / flint.arb(1).exp(),
}


def exact_dyadic(x):
    """Exact rational (num, den) with den a power of 2, for an exact arb (radius 0)."""
    m, e = x.man_exp()
    m, e = Z(int(m)), int(e)
    if e >= 0:
        return m << e, Z(1)
    return m, Z(1) << (-e)


def enclosure(name, digits):
    flint.ctx.prec = int(digits * math.log2(10)) + 128
    x = CONSTS[name]()
    lo = x.mid() - x.rad()
    hi = x.mid() + x.rad()
    lo_n, lo_d = exact_dyadic(lo.mid())
    hi_n, hi_d = exact_dyadic(hi.mid())
    # lo.mid()/hi.mid() are exact sums of exact dyadics only if radius rounding is outward; widen
    # by one ulp of the working precision to be safe (keeps rigor, costs nothing).
    ulp_den = Z(1) << (flint.ctx.prec + 8)
    lo_n, lo_d = lo_n * ulp_den - lo_d, lo_d * ulp_den
    hi_n, hi_d = hi_n * ulp_den + hi_d, hi_d * ulp_den
    assert x.rad() < flint.arb(10) ** (-(digits - 5))
    return (lo_n, lo_d), (hi_n, hi_d), x


def simplest_rational(a, b, cf_record=40):
    """Minimal-denominator rational in the closed interval [a, b], 0 < a < b, exact.

    Returns (h, k, steps, prefix) with h/k the simplest rational and prefix the first
    cf_record common continued-fraction terms of a and b.
    """
    an, ad = a
    bn, bd = b
    assert an * bd < bn * ad and an > 0
    h1, h2 = Z(1), Z(0)
    k1, k2 = Z(0), Z(1)
    steps, prefix = 0, []
    while True:
        t, r = divmod(an, ad)
        if r == 0:                       # a is an integer: it is the simplest rational
            term = t
            break
        if (t + 1) * bd <= bn:           # an integer t+1 lies in (a, b]
            term = t + 1
            break
        # common integer part t: continue with (1/(b-t), 1/(a-t))
        if len(prefix) < cf_record:
            prefix.append(int(t))
        h1, h2 = t * h1 + h2, h1
        k1, k2 = t * k1 + k2, k1
        an, ad, bn, bd = bd, bn - t * bd, ad, an - t * ad
        steps += 1
    h = term * h1 + h2
    k = term * k1 + k2
    return h, k, steps, prefix


def simplest_fraction_reference(a, b):
    """Independent recursive reference implementation on Fractions (small inputs only)."""
    fl = a.numerator // a.denominator
    if Fraction(fl) == a:
        return a
    if fl + 1 <= b:
        return Fraction(fl + 1)
    return fl + 1 / simplest_fraction_reference(1 / (b - fl), 1 / (a - fl))


def ndigits(k):
    return len(str(k)) if gmpy2 is None else int(gmpy2.num_digits(k, 10))


def run(name, digits, out=None):
    t0 = time.time()
    lo, hi, x = enclosure(name, digits)
    t1 = time.time()
    h, k, steps, prefix = simplest_rational(lo, hi)
    t2 = time.time()
    # sanity: the simplest rational really lies in the interval
    assert lo[0] * k <= h * lo[1] and h * hi[1] <= hi[0] * k
    rec = dict(const=name, digits=digits, prec_bits=flint.ctx.prec,
               python_flint=flint.__version__, gmpy2=(gmpy2.version() if gmpy2 else None),
               min_denominator_digits=ndigits(k), cf_common_steps=steps, cf_prefix=prefix,
               leading_digits_of_min_denominator=str(k)[:20] if digits <= 20000 else None,
               t_arb_s=round(t1 - t0, 2), t_cf_s=round(t2 - t1, 2))
    line = json.dumps(rec)
    print(line, flush=True)
    if out:
        with open(out, "a") as f:
            f.write(line + "\n")
    return rec, (h, k), lo, hi


def selftest():
    import mpmath
    ok = True
    for name in CONSTS:
        for digits in (60, 300, 1500):
            rec, (h, k), lo, hi = run(name, digits)
            a = Fraction(int(lo[0]), int(lo[1]))
            b = Fraction(int(hi[0]), int(hi[1]))
            ref = simplest_fraction_reference(a, b) if digits <= 300 else None
            same = ref is None or (ref.numerator == int(h) and ref.denominator == int(k))
            mpmath.mp.dps = 3 * digits + 50
            v = {"epi_sum": mpmath.e + mpmath.pi, "epi_prod": mpmath.e * mpmath.pi,
                 "epi_diff": mpmath.pi - mpmath.e, "pi_over_e": mpmath.pi / mpmath.e}[name]
            cf = []
            y = v
            for _ in range(len(rec["cf_prefix"])):
                t = int(mpmath.floor(y)); cf.append(t); y = 1 / (y - t)
            agree = cf == rec["cf_prefix"]
            print(f"SELFTEST {name} digits={digits}: reference_match={same} cf_prefix_match={agree}")
            ok &= same and agree
    print("SELFTEST", "PASS" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(0 if selftest() else 1)
    out = None
    if "--out" in sys.argv:
        out = sys.argv[sys.argv.index("--out") + 1]
    run(sys.argv[1], int(sys.argv[2]), out)
