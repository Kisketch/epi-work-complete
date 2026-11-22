"""Exact finite-phase enumeration from the three families in the paper."""

from fractions import Fraction as F
from math import gcd, isqrt, lcm

from golden_finite_spectrum import PHI, Quadratic, finite_cf, height, phase_data, prefix, spectrum


def normal_cycle(x):
    steps, digits = {}, []
    while x not in steps:
        steps[x] = len(digits)
        d = x.floor()
        digits.append(d)
        x = 1 / (x - d)
    period = tuple(digits[steps[x]:])
    return min(period[i:] + period[:i] for i in range(len(period)))


def algebraic_tails(delta, a_max, upper, cycles):
    """Enumerate primitive polynomials before checking their orbit classes."""
    root = Quadratic(F(0), F(1), delta)
    margin = isqrt(delta) + 1
    for a in range(1, a_max + 1):
        for b in range((-2 * a * upper).floor() - margin, margin + 1):
            numerator = b*b - delta
            if numerator % (4*a) or gcd(a, b, numerator // (4*a)) != 1:
                continue
            for sign in (-1, 1):
                theta = (-b + sign*root)/(2*a)
                if 0 < theta <= upper and normal_cycle(theta) in cycles:
                    yield theta


def finite_slice(tau, phases, cap):
    # The radicand represents the primitive discriminant of the input orbit.
    norm = tau.a * tau.a - tau.delta * tau.b * tau.b
    leading = lcm((2*tau.a).denominator, norm.denominator)
    if 4 * (leading * tau.b)**2 != 1:
        raise ValueError("use the primitive discriminant as the quadratic radicand")
    root = Quadratic(F(0), F(1), tau.delta)
    unit = Quadratic(F(1), delta=tau.delta)
    cycles = frozenset([normal_cycle(tau), normal_cycle(tau.conjugate())])
    # Materialize each finite enumeration locally. The number of phases is finite.
    samples = {}
    def tails(a_max, upper):
        key = (a_max, upper)
        if key not in samples:
            samples[key] = tuple(algebraic_tails(tau.delta, a_max, upper, cycles))
        return samples[key]

    M = cap * root / 2
    values = set()
    for previous, suffix in phases:
        r = 1 / finite_cf(suffix) if suffix else F(0)
        v = finite_cf((0, *reversed(previous)))
        if suffix:
            u = finite_cf(suffix)
            t = 2*u*M
            cutoff = max((2*root).floor(), (u.denominator**2*t*(t + root)).floor())
            upper = max(1 + root, unit*u + u*M)
            for eta in tails(cutoff, upper):
                if eta > 1 and prefix(eta, len(suffix)) != suffix:
                    values.add(height(eta)*abs(u-eta)*abs(eta.conjugate())/u)
        cutoff = max((2*root).floor(), (2*M).floor())
        for theta in tails(cutoff, unit):
            for q in range(1, (M+root).floor()+1):
                values.add(height(theta)*abs(q+theta.conjugate()+v))
        offset = (1+M).floor()
        cutoff = (r.denominator**2*M*(M+root)).floor()
        for theta in tails(cutoff, unit):
            for d in range(-offset, offset+1):
                if d:
                    values.add(height(theta)*abs(r-d-theta))
    return sorted(value for value in values if value <= cap)


if __name__ == "__main__":
    golden_phases = phase_data(6, 1, -1)
    assert finite_slice(PHI, golden_phases, F(1,4)) == spectrum(6,1,F(1,4))[0]
    print("Delta 5: independent general enumeration matches existing golden output.")
    for a in (1, 2, 3, 4, 5):
        delta = a*a+4
        root = Quadratic(F(0), F(1), delta)
        tau = (a+root)/2
        cap = F(2)
        lo, hi = -(-(1-cap)*root).floor(), ((1+cap)*root).floor()
        expected = sorted(abs(1-m/root) for m in range(lo,hi+1) if m%2 == a%2)
        assert finite_slice(tau, {((), ())}, cap) == expected
        print(f"Delta {delta}: {len(expected)} exact pure-head values through {cap}.")
    tau = (2+Quadratic(F(0), F(1), 12))/4
    mixed_phases = phase_data(1, 6, 1)
    values = finite_slice(tau, mixed_phases, F(1,2))
    assert values
    D = lcm(*(finite_cf(s).numerator for _, s in mixed_phases if s),
            *((1/finite_cf(s)).denominator for _, s in mixed_phases if s),
            *(finite_cf((0, *s[::-1])).denominator for s, _ in mixed_phases))
    assert all(value.a in (-1, 1) and (tau.delta*D*value.b).denominator==1 for value in values)
    print(f"Delta 12, mixed affine target: {len(values)} values through 1/2, lattice denominator {D}.")
    for value in values:
        print("   ", value)
