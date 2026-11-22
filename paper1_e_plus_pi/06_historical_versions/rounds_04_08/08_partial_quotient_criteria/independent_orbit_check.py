"""Independently enclose the normalized error directly from the two orbit points."""

from fractions import Fraction as Q
from math import isqrt


def atan_bounds(n, count):
    term = Q(1, n)
    total = Q(0)
    for k in range(count):
        total += term
        term *= Q(-(2 * k + 1), (2 * k + 3) * n * n)
    return min(total, total + term), max(total, total + term)


def transform(z):
    return (103993 * z + 355) / (33102 * z + 113)


# The tangent addition formula gives pi/4 = atan(1/2) + atan(1/3).
lo2, hi2 = atan_bounds(2, 90)
lo3, hi3 = atan_bounds(3, 90)
pi_lo, pi_hi = 4 * (lo2 + lo3), 4 * (hi2 + hi3)
scale = 10**55
root = isqrt(5 * scale**2)
sqrt_lo, sqrt_hi = Q(root, scale), Q(root + 1, scale)

def orbit_bounds(z_lo, z_hi):
    assert (33102 * z_lo + 113) * (33102 * z_hi + 113) > 0
    return sorted((transform(z_lo), transform(z_hi)))


lo, hi = orbit_bounds((1 + sqrt_lo) / 2, (1 + sqrt_hi) / 2)
conj_lo, conj_hi = orbit_bounds((1 - sqrt_hi) / 2, (1 - sqrt_lo) / 2)
assert conj_hi < lo and hi < pi_lo or pi_hi < lo and hi < conj_lo
distances = [abs(p - b) for p in (pi_lo, pi_hi) for b in (lo, hi)]
gaps = [abs(b - c) for b in (lo, hi) for c in (conj_lo, conj_hi)]
lower, upper = 2 * min(distances) / max(gaps), 2 * max(distances) / min(gaps)
assert Q(14695421944, 10**12) < lower < upper < Q(14695421945, 10**12)
assert 32 * 36 * 6**2 == 41472
print("Independent pi and conjugate enclosures verified the published decimal interval.")
print("The coefficient in the golden-orbit lower bound is 32 * 36 * 6^2 = 41472.")
