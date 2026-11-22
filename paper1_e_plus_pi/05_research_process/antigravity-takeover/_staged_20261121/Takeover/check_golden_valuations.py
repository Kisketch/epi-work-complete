"""Exact finite checks for affine gcd valuations and adjacent window scales."""
from math import gcd


def prime_powers(n):
    p = 2
    while p * p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            yield p, exponent
        p += 1
    if n > 1:
        yield n, 1


def valuation_capped(n, prime, cap):
    """Compute min(v_prime(n), cap), also for n = 0."""
    result = 0
    while result < cap and n % prime == 0:
        n //= prime
        result += 1
    return result


def affine_gcd_from_valuations(a, b, p_j, q_j, factors):
    result = 1
    for prime, u in factors:
        s = valuation_capped(q_j, prime, u + 1)
        exponent = min(u, s)
        if s == u:
            power = prime ** u
            exponent += valuation_capped(a * (q_j // power) - (b // power) * p_j, prime, u)
        result *= prime ** exponent
    return result


def hermite_pairs(last_index):
    p_j, p_next = 1, 3
    q_j, q_next = 1, 1
    yield p_j, q_j
    for j in range(1, last_index + 1):
        yield p_next, q_next
        factor = 4 * j + 2
        p_j, p_next = p_next, factor * p_next + p_j
        q_j, q_next = q_next, factor * q_next + q_j


def main():
    pairs = list(hermite_pairs(180))
    count = 0
    for b in range(1, 65):
        factors = list(prime_powers(b))
        for a in range(1, b + 1):
            if gcd(a, b) != 1:
                continue
            previous = 1
            for j, (p_j, q_j) in enumerate(pairs):
                g = gcd(b, q_j)
                expected = gcd(a * q_j - b * p_j, b * q_j)
                assert expected == g * gcd(a * (q_j // g) - (b // g) * p_j, g)
                assert expected == affine_gcd_from_valuations(a, b, p_j, q_j, factors)
                assert b**2 % (previous * expected) == 0
                # The same answer is determined by P_j, Q_j modulo B^2.
                assert expected == gcd(a * (q_j % b**2) - b * (p_j % b**2),
                                       b * (q_j % b**2), b**2)
                previous = expected
                count += 1
    print(f"{count} exact cases passed, all reduced residues for B=1..64, j=0..180.")


if __name__ == "__main__":
    main()
