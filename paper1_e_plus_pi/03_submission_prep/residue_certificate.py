"""Exact integer checks for pressure bounds for digits 1 modulo 4."""

from fractions import Fraction
from functools import lru_cache


GRID = 256
FIRST_TAIL_INDEX = 64
FINITE_DIGITS = 2**24
SCALE = 10**13


@lru_cache(maxsize=None)
def enclose_power(base, power):
    """Return integer bounds for SCALE * base**(-power)."""
    p, q = power.numerator, power.denominator
    proposal = int(SCALE * float(base) ** (-float(power)))
    rhs = SCALE**q * base.denominator**p
    factor = base.numerator**p
    lo, hi = max(0, proposal - 1), proposal + 2
    if not lo**q * factor <= rhs <= hi**q * factor:
        raise ArithmeticError("The floating-point proposal failed the integer check")
    return lo, hi


def cell(a, endpoint):
    return min(GRID - 1, GRID**2 // (a * GRID + endpoint))


def coefficients(s):
    power = 2 * s
    integral_factor = 1 / (4 * (power - 1))
    lower_start, _ = enclose_power(Fraction(4 * FIRST_TAIL_INDEX + 2), power - 1)
    _, upper_end = enclose_power(Fraction(4 * FINITE_DIGITS + 2), power - 1)
    _, upper_start = enclose_power(Fraction(4 * FIRST_TAIL_INDEX - 3), power - 1)
    lower_tail = int(integral_factor * (lower_start - upper_end))
    upper_tail = int(-(-integral_factor * upper_start // 1))
    assert lower_tail > 0 and 4 * FIRST_TAIL_INDEX + 1 > GRID
    rows = []
    for j in range(GRID):
        row = []
        for k in range(FIRST_TAIL_INDEX):
            a = 4 * k + 1
            lo, _ = enclose_power(Fraction(a * GRID + j + 1, GRID), power)
            _, hi = enclose_power(Fraction(a * GRID + j, GRID), power)
            row.append((lo, hi, cell(a, j + 1), cell(a, j)))
        rows.append(row)
    return rows, lower_tail, upper_tail


def provisional_vector(rows, tail):
    """Find a positive test vector. Its quality is checked separately."""
    vector = [1.0] * GRID
    for _ in range(40):
        nxt = [
            (sum((lo + hi) * (vector[left] + vector[right]) / 4
                 for lo, hi, left, right in row) + tail * vector[0]) / SCALE
            for row in rows
        ]
        vector = [value / nxt[0] for value in nxt]
    return [max(1, round(10**9 * value)) for value in vector]


def certify(s, side):
    rows, lower_tail, upper_tail = coefficients(s)
    vector = provisional_vector(rows, (lower_tail + upper_tail) // 2)
    margin = []
    for j, row in enumerate(rows):
        bound = SCALE * vector[j]
        if side == "lower":
            value = sum(lo * min(vector[left:right + 1])
                        for lo, hi, left, right in row)
            margin.append(Fraction(value + lower_tail * vector[0] - bound, bound))
        else:
            value = sum(hi * max(vector[left:right + 1])
                        for lo, hi, left, right in row)
            margin.append(Fraction(bound - value - upper_tail * vector[0], bound))
    result = min(margin)
    print(f"{side} s={s}  min relative margin={float(result):+.9f}  exact={result}",
          flush=True)
    enclose_power.cache_clear()
    return result


if __name__ == "__main__":
    lower = Fraction(357, 512)
    upper = Fraction(359, 512)
    smaller_margin = certify(lower, "lower")
    larger_margin = certify(upper, "upper")
    if smaller_margin <= 0 or larger_margin <= 0:
        raise SystemExit("At least one pressure sign failed the integer checks")
    print(f"Certified: {lower} < dimension < {upper}; interval width = {upper - lower}")
