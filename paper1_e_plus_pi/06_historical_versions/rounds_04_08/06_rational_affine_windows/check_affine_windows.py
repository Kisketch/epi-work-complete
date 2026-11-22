"""Check the affine-window identities using exact enclosing intervals for e."""
from bisect import bisect_right
from fractions import Fraction
from math import factorial, gcd, isqrt

LAST = 235
LOWER = sum(Fraction(1, factorial(n)) for n in range(901))
UPPER = LOWER + Fraction(2, factorial(901))
P, Q = [1, 3], [1, 1]
for j in range(1, LAST + 1):
    P.append((4 * j + 2) * P[-1] + P[-2])
    Q.append((4 * j + 2) * Q[-1] + Q[-2])
H = [isqrt(j * q * q) for j, q in enumerate(Q)]

def certified_convergents(lower, upper):
    """Retain the common digits through the first denominator above H[-1]."""
    old_p, p, old_q, q = 0, 1, 1, 0
    rows = []
    while q <= H[-1]:
        digit = lower.numerator // lower.denominator
        assert digit == upper.numerator // upper.denominator
        old_p, p = p, digit * p + old_p
        old_q, q = q, digit * q + old_q
        rows.append((p, q, digit))
        if q <= H[-1]:
            lower, upper = 1 / (upper - digit), 1 / (lower - digit)
    return rows

def check(A, B, C):
    endpoints = sorted(((A + C * LOWER) / B, (A + C * UPPER) / B))
    cf = certified_convergents(*endpoints)
    ends = [bisect_right([entry[1] for entry in cf], h) - 1 for h in H]
    threshold, period = max(B, abs(C))**2, 2 * B * abs(C)
    content = [gcd(A * q + C * p, B * q) for p, q in zip(P, Q)]
    singletons = shifts = 0
    for j in range(threshold + 1, LAST + 1):
        assert cf[ends[j]][:2] == ((A * Q[j] + C * P[j]) // content[j],
                                   B * Q[j] // content[j])
        p, q, _ = cf[ends[j]]
        p_next, q_next, _ = cf[ends[j + 1]]
        r = ends[j + 1] - ends[j]
        assert r % 2 == 1
        determinant = abs(p * q_next - p_next * q)
        assert determinant * content[j] * content[j + 1] == period
        assert (r == 1) == (determinant == 1)
        singletons += r == 1
        if j + period <= LAST:
            word = tuple(a for _, _, a in cf[ends[j] + 1:ends[j + 1] + 1])
            next_word = tuple(a for _, _, a in
                              cf[ends[j + period] + 1:ends[j + period + 1] + 1])
            assert len(next_word) == len(word)
            if j - 1 > threshold:
                assert next_word == (word[0] + 4 * content[j]**2,) + word[1:]
                shifts += 1
    print(f"{(A, B, C)}: {LAST-threshold} windows, {singletons} singletons, {shifts} digit shifts")
    return shifts

models = [(1,2,1), (1,2,-1), (1,4,1), (1,4,3), (1,8,3),
          (2,4,2), (6,1,-1), (6,1,-2), (-7,4,4), (17,3,-3), (3,2,9)]
print(f"Exact period shifts checked: {sum(check(*model) for model in models)}")

def check_singleton_classification(bound):
    """Evaluate a complete Hermite residue period for each small primitive triple."""
    triples = 0
    for B in range(1, bound + 1):
        for C in range(-bound, bound + 1):
            if C == 0:
                continue
            period = 2 * B * abs(C)
            p0, p1, q0, q1 = 1, 3, 1, 1
            pairs = [(p1, q1)]
            for j in range(1, period + 1):
                p0, p1 = p1, ((4*j + 2)*p1 + p0) % period
                q0, q1 = q1, ((4*j + 2)*q1 + q0) % period
                pairs.append((p1, q1))
            for A in range(B):
                if gcd(gcd(A, B), C) != 1:
                    continue
                values = [gcd(gcd(A*q + C*p, B*q), B*abs(C)) for p,q in pairs]
                all_single = all(a*b == period for a,b in zip(values, values[1:]))
                assert all_single == (abs(C) == 1 and B in (2, 4) and A % 2 == 1)
                triples += 1
    print(f"Complete residue periods checked for primitive triples: {triples}")

check_singleton_classification(16)
