"""Exact finite evaluation of the golden-ratio orbit spectrum for rational affine images of e."""

from argparse import ArgumentParser
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache, total_ordering
from math import ceil, gcd, isqrt, lcm


@total_ordering
@dataclass(frozen=True)
class Quadratic:
    """a + b sqrt(delta), with rational coefficients."""

    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)
    delta: int = 5

    def coerce(self, value):
        if isinstance(value, Quadratic):
            if value.delta != self.delta:
                raise ValueError("incompatible quadratic radicands")
            return value
        return Quadratic(Fraction(value), delta=self.delta)

    def __add__(self, other):
        other = self.coerce(other)
        return Quadratic(self.a + other.a, self.b + other.b, self.delta)

    __radd__ = __add__

    def __neg__(self):
        return Quadratic(-self.a, -self.b, self.delta)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        return Quadratic(self.a * other.a + self.delta * self.b * other.b,
                         self.a * other.b + self.b * other.a, self.delta)

    __rmul__ = __mul__

    def conjugate(self):
        return Quadratic(self.a, -self.b, self.delta)

    def __truediv__(self, other):
        other = self.coerce(other)
        norm = other.a * other.a - self.delta * other.b * other.b
        return self * Quadratic(other.a / norm, -other.b / norm, self.delta)

    def __rtruediv__(self, other):
        return self.coerce(other) / self

    def sign(self):
        if self.a == 0:
            return (self.b > 0) - (self.b < 0)
        if self.b == 0 or (self.a > 0) == (self.b > 0):
            return (self.a > 0) - (self.a < 0)
        dominant = self.a * self.a > self.delta * self.b * self.b
        positive = self.a > 0 if dominant else self.b > 0
        return 1 if positive else -1

    def __eq__(self, other):
        if not isinstance(other, (int, Fraction, Quadratic)):
            return NotImplemented
        if isinstance(other, Quadratic) and other.delta != self.delta:
            return self.b == 0 and other.b == 0 and self.a == other.a
        other = self.coerce(other)
        return (self.a, self.b) == (other.a, other.b)

    def __hash__(self):
        return hash(self.a) if self.b == 0 else hash((self.a, self.b, self.delta))

    def __lt__(self, other):
        return (self - other).sign() < 0

    def __abs__(self):
        return -self if self.sign() < 0 else self

    def floor(self):
        d = isqrt(self.delta)
        lower = self.a + min(d * self.b, (d + 1) * self.b)
        upper = self.a + max(d * self.b, (d + 1) * self.b)
        lo, hi = lower.numerator // lower.denominator, upper.numerator // upper.denominator + 1
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if self < mid:
                hi = mid
            else:
                lo = mid
        return lo

    def decimal(self):
        return float(self.a) + float(self.b) * self.delta**0.5

    def __str__(self):
        return f"{self.a} + ({self.b}) sqrt({self.delta})"


ROOT5 = Quadratic(Fraction(0), Fraction(1))
PHI = (1 + ROOT5) / 2


@lru_cache(maxsize=None)
def in_orbit(x):
    """Decide membership by the exact eventually periodic continued fraction."""
    if x.b == 0:
        return False
    leading = lcm((2 * x.a).denominator,
                  (x.a * x.a - 5 * x.b * x.b).denominator)
    if 20 * (leading * x.b) ** 2 != 5:
        return False
    seen = set()
    while x not in seen:
        if x == PHI:
            return True
        seen.add(x)
        x = 1 / (x - x.floor())
    return False


def prefix(x, length):
    digits = []
    for _ in range(length):
        digit = x.floor()
        digits.append(digit)
        x = 1 / (x - digit)
    return tuple(digits)


def height(x):
    return 2 / abs(x - x.conjugate())


def rational_cf(p, q, j, slope):
    digits = []
    while q:
        digit, remainder = divmod(p, q)
        digits.append(digit)
        p, q = q, remainder
    # The sign of the slope determines the parity of the locked convergent.
    if (len(digits) - 1 + j) % 2 != int(slope < 0):
        assert len(digits) > 1 and digits[-1] >= 2
        digits[-1:] = [digits[-1] - 1, 1]
    return tuple(digits)


def phase_data(a, b, slope):
    assert b > 0 and slope != 0 and gcd(a, b, slope) == 1
    start = max(b, abs(slope)) ** 2 + 3
    period = 2 * b * abs(slope)
    expansions = {}
    pp, p, qq, q = 1, 3, 1, 1
    for j in range(1, start + 2 * period + 1):
        if j >= start - 1:
            numerator, denominator = a * q + slope * p, b * q
            g = gcd(numerator, denominator)
            expansions[j] = (rational_cf(numerator // g, denominator // g, j, slope), g)
        pp, p, qq, q = p, (4 * j + 2) * p + pp, q, (4 * j + 2) * q + qq
    windows = {}
    for j in range(start - 1, start + 2 * period):
        pre, g = expansions[j]
        nxt, _ = expansions[j + 1]
        assert pre == nxt[:len(pre)]
        word = nxt[len(pre):]
        assert len(word) % 2 == 1
        windows[j] = (word, g)
    for j in range(start - 1, start + period):
        word, g = windows[j]
        shifted, shifted_g = windows[j + period]
        assert shifted_g == g and shifted == (word[0] + 4 * g * g, *word[1:])
    return { (windows[j-1][0][1:], windows[j][0][1:]) for j in range(start, start + period) }


def finite_cf(digits):
    value = Fraction(digits[-1])
    for digit in reversed(digits[:-1]):
        value = digit + 1 / value
    return value


def signed_divisors(number):
    number = abs(number)
    assert number
    for d in range(1, isqrt(number) + 1):
        if number % d == 0:
            yield d
            yield -d
            if d * d != number:
                yield number // d
                yield -(number // d)


def suffix_limits(suffix, cap):
    u = finite_cf(suffix)
    D, q = u.numerator, u.denominator
    # m is signed and normalized by the unimodular determinant.
    lower = -(-((1 - cap) * D * ROOT5)).floor()
    upper = ((1 + cap) * D * ROOT5).floor()
    found = set()
    for m in range(lower, upper + 1):
        product4 = m * m - 5 * D * D
        if product4 % 4:
            continue
        for signed_norm in signed_divisors(product4 // 4):
            for orientation in (-1, 1):
                ratio = orientation * (m - D * ROOT5) / (2 * signed_norm)
                eta = D / (q + ratio)
                if eta in found or eta <= 1 or not in_orbit(eta):
                    continue
                if prefix(eta, len(suffix)) == suffix:
                    continue
                value = height(eta) * abs(u - eta) * abs(eta.conjugate()) / u
                if value == abs(m / (D * ROOT5) - 1) and value <= cap:
                    found.add(eta)
                    yield value, f"suffix={suffix}, eta={eta}"


@lru_cache(maxsize=None)
def unit_tails(leading_bound):
    """List orbit points in (0,1) of primitive discriminant 5 and bounded height."""
    found = set()
    for a in range(1, leading_bound + 1):
        for b in range(-2 * a - 3, 4):
            if (b * b - 5) % (4 * a):
                continue
            for sign in (-1, 1):
                theta = (-b + sign * ROOT5) / (2 * a)
                if 0 < theta < 1 and in_orbit(theta):
                    found.add(theta)
    return found


def head_limits(previous, suffix, cap):
    r = 1 / finite_cf(suffix) if suffix else Fraction(0)
    z = finite_cf((0, *reversed(previous)))
    if suffix:
        bound = (cap * ROOT5 / (2 * min(r, 1-r))).floor()
    else:
        # At the boundary d=-1 use the discriminant-5 norm at 1.
        bound = max((cap * ROOT5 / 2).floor(), (5 * cap * (cap + 2)) // 4)
    # A positive conjugate gives h*q <= cap for the fixed-integer branch.
    fixed_bound = (cap * ROOT5 / 2).floor()
    fixed_tails = unit_tails(fixed_bound) | {PHI - 1}
    integer_cap = ceil(2 * cap + 2)
    for theta in fixed_tails:
        for q in range(1, integer_cap + 1):
            value = height(theta) * abs(q + theta.conjugate() + z)
            if value <= cap:
                yield value, f"fixed head alternative q={q}, theta={theta}, z={z}"
    for theta in unit_tails(bound):
        for d in range(-integer_cap, integer_cap + 1):
            if d != 0:
                value = height(theta) * abs(r - d - theta)
                if value <= cap:
                    yield value, f"moving head offset d={d}, theta={theta}, r={r}"


def spectrum(a, b, cap, slope=None):
    if cap <= 0:
        raise ValueError("cap must be positive")
    phases = phase_data(a, b, -b if slope is None else slope)
    witnesses = {}
    for suffix in sorted({suffix for _, suffix in phases if suffix}):
        for value, witness in suffix_limits(suffix, cap):
            witnesses.setdefault(value, witness)
    for previous, suffix in sorted(phases):
        for value, witness in head_limits(previous, suffix, cap):
            witnesses.setdefault(value, witness)
    return sorted(witnesses), witnesses


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("model", nargs="*", type=int, metavar="A_or_B")
    parser.add_argument("--slope", type=int, metavar="C", help="use x=(A+C*e)/B (default C=-B)")
    parser.add_argument("--cap", type=Fraction, default=Fraction(1))
    parser.add_argument("--all", action="store_true", help="print every limit at or below the cap")
    args = parser.parse_args()
    if args.cap <= 0:
        parser.error("--cap must be positive")
    if len(args.model) not in (0, 2):
        parser.error("give both A and B, or omit them for the reference suite")
    if args.slope is not None and (not args.model or args.slope == 0):
        parser.error("--slope requires A, B and a nonzero C")
    if args.model:
        a, b = args.model
        c = -b if args.slope is None else args.slope
        if b <= 0 or gcd(a, b, c) != 1:
            parser.error("B must be positive and (A,B,C) must be primitive")
    expected = {
        (6, 1): (1 - 2 / ROOT5, 4 / ROOT5 - 1),
        (11, 2): (9 / (4 * ROOT5) - 1, 1 - 7 / (4 * ROOT5)),
        (10, 3): (1 - 20 / (9 * ROOT5), 22 / (9 * ROOT5) - 1),
        (11, 3): (1 - 20 / (9 * ROOT5), 22 / (9 * ROOT5) - 1),
        (13, 4): (1 - 35 / (16 * ROOT5), 1 - 33 / (16 * ROOT5)),
        (15, 4): (1 - 35 / (16 * ROOT5), 1 - 33 / (16 * ROOT5)),
    }
    expected.update({(a, 5): (56 / (25 * ROOT5) - 1, 1 - 54 / (25 * ROOT5))
                     for a in range(16, 20)})
    expected.update({(a, 6): (1 - 79 / (36 * ROOT5), 1 - 77 / (36 * ROOT5))
                     for a in (19, 23)})
    expected[(22, 7)] = (110 / (49 * ROOT5) - 1, 1 - 108 / (49 * ROOT5))
    inputs = [tuple(args.model)] if args.model else list(expected)
    for a, b in inputs:
        cap = args.cap
        values, witnesses = spectrum(a, b, cap, args.slope)
        if not args.model and len(values) < 2:
            cap = Fraction(3)
            values, witnesses = spectrum(a, b, cap, args.slope)
        if not args.model:
            assert len(values) >= 2
            if (a, b) in expected:
                assert tuple(values[:2]) == expected[a, b], (a, b, values[:2])
        model = f"{a}/{b}-e" if args.slope is None else f"({a}{args.slope:+d}*e)/{b}"
        print(f"{model}: {len(values)} distinct finite limits <= {cap}")
        reported = values if args.all else values[:2]
        for index, value in enumerate(reported, 1):
            print(f"  #{index}: {value}  ({value.decimal():.15g})")
            print(f"      witness: {witnesses[value]}")
