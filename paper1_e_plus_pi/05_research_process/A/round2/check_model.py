"""Exact regression check of the three-term-block example, using only integers."""
from math import gcd, isqrt


def convergents(last, perturbed):
    a, b, c, d = 0, 1, 1, 0
    result = []
    digits = [3]
    for j in range(1, last + 1):
        extra = isqrt(j) if perturbed and j >= 2 and j & (j - 1) == 0 else 0
        digits.extend((3 if j == 1 else 2*j + extra, 1, 1))
    for digit in digits:
        a, c = c, a + digit*c
        b, d = d, b + digit*d
        result.append((c, d))
    return result


def check(last):
    base = convergents(last, False)
    pert = convergents(last, True)
    old, q = 1, 1
    previous_end = None
    misses = []
    for j in range(1, last+1):
        i = 3*j-3
        assert base[i][1] == q
        assert gcd(*pert[i]) == 1
        if previous_end:
            p, d = pert[i]
            r, s = previous_end
            assert abs(p*s-r*d) == 2
        previous_end = pert[i]
        H = isqrt(j*q*q)
        if not pert[i][1] <= H < pert[i+1][1]:
            misses.append(j)
        old, q = q, (4*j+2)*q + old
    print("range:", (1,last), "index exceptions:", misses, "base and determinant checks: passed")


if __name__ == "__main__":
    check(512)
