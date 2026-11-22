"""Exact checks for the new affine phases, using the published enumerator."""
from fractions import Fraction
from math import lcm

from golden_finite_spectrum import ROOT5, finite_cf, phase_data, spectrum

pure_cap = Fraction(3)
pure = sorted({
    abs(1 - m / ROOT5) for m in range(-11, 11, 2)
    if abs(1 - m / ROOT5) <= pure_cap
})
for b in (2, 4):
    for c in (-1, 1):
        assert phase_data(1, b, c) == {((), ())}
        values, _ = spectrum(1, b, pure_cap, c)
        assert values == pure
        print(f'Pure-head model (1,{b},{c}) matches all {len(pure)} odd-lattice values through {pure_cap}.')

mixed = sorted(abs(1 - m / (3 * ROOT5)) for m in range(1, 14, 2))
for c in (-1, 1):
    phases = phase_data(1, 6, c)
    assert any(not s for _, s in phases) and any(s for _, s in phases)
    values, _ = spectrum(1, 6, Fraction(1), c)
    assert values == mixed
    print(f'Mixed model (1,6,{c}) matches all {len(mixed)} values through 1.')

for a, b, c in [(1, 3, 2), (-1, 8, 1), (3, 5, -2), (4, 9, 2)]:
    phases = phase_data(a, b, c)
    pieces = [finite_cf(s).numerator for _, s in phases if s]
    pieces += [(1 / finite_cf(s)).denominator for _, s in phases if s]
    pieces += [finite_cf((0, *s[::-1])).denominator for s, _ in phases]
    D = lcm(*pieces)
    values, _ = spectrum(a, b, Fraction(1), c)
    assert all(value.a in (-1, 1) and (5 * D * value.b).denominator == 1 for value in values)
    print(f'Affine model ({a},{b},{c}) gives {len(values)} limits through 1, all on the D={D} lattice.')
