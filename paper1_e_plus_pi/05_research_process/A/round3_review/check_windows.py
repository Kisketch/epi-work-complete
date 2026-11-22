"""Exact interval checks of the window proofs on selected affine models."""
from bisect import bisect_right
from fractions import Fraction
from itertools import accumulate
from math import factorial, gcd, isqrt

LIMIT = 235

# The geometric bound on the tail is strictly less than 2/901!.
e_lower = sum(Fraction(1, factorial(k)) for k in range(901))
e_upper = e_lower + Fraction(2, factorial(901))

p_hermite, q_hermite = [1, 3], [1, 1]
for j in range(1, LIMIT):
    p_hermite.append((4 * j + 2) * p_hermite[-1] + p_hermite[-2])
    q_hermite.append((4 * j + 2) * q_hermite[-1] + q_hermite[-2])
cutoffs = [isqrt(j * q * q) for j, q in enumerate(q_hermite)]


def certified_convergents(lo, hi):
    """Extract common digits until the first denominator above every cutoff."""
    p_prev, p_prevprev = 1, 0
    q_prev, q_prevprev = 0, 1
    convergents = []
    while q_prev <= cutoffs[-1]:
        digit = lo.numerator // lo.denominator
        assert digit == hi.numerator // hi.denominator
        p_prev, p_prevprev = digit * p_prev + p_prevprev, p_prev
        q_prev, q_prevprev = digit * q_prev + q_prevprev, q_prev
        convergents.append((p_prev, q_prev, digit))
        if q_prev <= cutoffs[-1]:
            lo, hi = 1 / (hi - digit), 1 / (lo - digit)
    return convergents


def check(A, B, C):
    lo, hi = sorted([(A + C * e_lower) / B, (A + C * e_upper) / B])
    cfs = certified_convergents(lo, hi)
    denominators = [q for _, q, _ in cfs]
    indices = [bisect_right(denominators, h) - 1 for h in cutoffs]
    first = (9 * B * B) // 4 + 1 if C == -B else 80
    period = 2 * B * B
    digits = [a for _, _, a in cfs]
    checked_shifts, multiple_content = 0, None
    for j in range(first, LIMIT):
        p, q = p_hermite[j], q_hermite[j]
        content = gcd(A * q + C * p, B * q)
        v = cfs[indices[j]][:2]
        w = cfs[indices[j + 1]][:2]
        assert v == ((A * q + C * p) // content, B * q // content)
        slope = ((Fraction(*w) - Fraction(*v))
                 / (Fraction(p_hermite[j + 1], q_hermite[j + 1]) - Fraction(p, q)))
        assert slope == Fraction(C, B)
        if C != -B:
            continue
        assert (indices[j] + j) % 2 == 1
        r = indices[j + 1] - indices[j]
        assert r >= 3 and r % 2 == 1, (A, B, j, r, v, w, indices[j:j+2])
        D = abs(v[0] * w[1] - v[1] * w[0])
        assert D % 2 == 0
        if j > first and j + period < LIMIT:
            a = tuple(digits[indices[j] + 1 : indices[j + 1] + 1])
            b = tuple(digits[indices[j + period] + 1 : indices[j + period + 1] + 1])
            assert b == (a[0] + 4 * content**2,) + a[1:]
            checked_shifts += 1
            if content > 1 and multiple_content is None:
                multiple_content = (j, content, a, b)
    print(f"({A},{B},{C}): range={first}..{LIMIT - 1}, shifted checks={checked_shifts}, "
          f"sample with content>1={multiple_content}")


for params in [(6, 1, -1), (11, 2, -2), (17, 3, -3), (-7, 4, -4),
               (43, 7, -7), (12, 2, -2), (6, 1, -2), (1, 2, 1)]:
    check(*params)



