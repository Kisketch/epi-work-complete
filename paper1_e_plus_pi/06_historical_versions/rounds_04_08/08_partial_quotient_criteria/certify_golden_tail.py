"""Certify a finite golden-tail approximation to pi, using standard Python only."""

from fractions import Fraction
from math import isqrt


def atan_inverse_bounds(base, terms):
    """The two consecutive alternating partial sums enclose atan(1/base)."""
    total = Fraction(0)
    for k in range(terms):
        total += Fraction((-1) ** k, (2 * k + 1) * base ** (2 * k + 1))
    other = total + Fraction((-1) ** terms, (2 * terms + 1) * base ** (2 * terms + 1))
    return min(total, other), max(total, other)


def common_digits(low, high, count):
    digits = []
    for _ in range(count):
        digit = low // 1
        assert digit == high // 1 and low > digit
        digits.append(digit)
        low, high = 1 / (high - digit), 1 / (low - digit)
    return digits


def convergent_matrix(prefix):
    p, previous_p, q, previous_q = 1, 0, 0, 1
    for digit in prefix:
        p, previous_p = digit * p + previous_p, p
        q, previous_q = digit * q + previous_q, q
    return p, previous_p, q, previous_q


def main():
    lower5, upper5 = atan_inverse_bounds(5, 128)
    lower239, upper239 = atan_inverse_bounds(239, 128)
    # Machin's identity is pi = 16 atan(1/5) - 4 atan(1/239).
    pi_low, pi_high = 16 * lower5 - 4 * upper239, 16 * upper5 - 4 * lower239
    digits = common_digits(pi_low, pi_high, 100)
    start = next(i for i in range(1, len(digits) - 2) if digits[i:i + 3] == [1, 1, 1])
    assert digits[start - 1] != 1 and digits[start + 3] != 1
    p, previous_p, q, previous_q = convergent_matrix(digits[:start])
    determinant = p * previous_q - q * previous_p
    assert abs(determinant) == 1

    # Substitute t=(previous_p-previous_q*x)/(q*x-p) in t^2-t-1
    # and clear its squared denominator.  The phi branch has derivative
    # 2*a*x+b = determinant*sqrt(5), by the chain rule.
    a = previous_q**2 + previous_q*q - q**2
    b = -2*previous_p*previous_q - previous_p*q - previous_q*p + 2*q*p
    c = previous_p**2 + previous_p*p - p**2
    assert b*b - 4*a*c == 5

    scale = 10**100
    root_floor = isqrt(5 * scale**2)
    sqrt_low, sqrt_high = Fraction(root_floor, scale), Fraction(root_floor + 1, scale)
    assert sqrt_low**2 < 5 < sqrt_high**2
    derivative = sorted((2*a*pi_low+b, 2*a*pi_high+b))
    signed_root = sorted((determinant*sqrt_low, determinant*sqrt_high))
    residual_low, residual_high = derivative[0]-signed_root[1], derivative[1]-signed_root[0]
    assert residual_low * residual_high > 0
    absolute_low, absolute_high = sorted((abs(residual_low), abs(residual_high)))
    bound_low, bound_high = absolute_low / sqrt_high, absolute_high / sqrt_low
    precision = 10**12
    left = (bound_low * precision) // 1
    right = -((-bound_high * precision) // 1)
    assert Fraction(left, precision) < bound_low <= bound_high < Fraction(right, precision)

    print("Machin enclosure: 128 alternating terms per arctangent; exact rational arithmetic")
    print("Certified digits a[0] through a[99]:", *digits)
    print("First maximal run of three ones: indices", start, "through", start+2)
    print("Prefix before this run:", *digits[:start])
    print(f"Matrix with consecutive convergent columns: [[{p}, {previous_p}], [{q}, {previous_q}]]")
    print("determinant and branch sign s:", determinant)
    print("Coefficients (a,b,c) of a*x^2+b*x+c:", a, b, c)
    print("Discriminant:", b*b-4*a*c)
    print(f"{left}/{precision} < abs(2*a*pi+b-s*sqrt(5))/sqrt(5) < {right}/{precision}")


if __name__ == "__main__":
    main()
