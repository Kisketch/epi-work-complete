from fractions import Fraction
for weight, radius, frequency in [(1, 2, Fraction(1, 3)), (3, 3, Fraction(2, 5))]:
    assert radius**2 - radius - 2*weight == 0
    assert Fraction(2*weight, radius*(2*radius-1)) == frequency
    print(f"e^t={weight}, Perron root={radius}, frequency={frequency}")
assert 1-Fraction(2,5) == Fraction(3,5)
print("Tilted entropy at e^t=3 is (3/5) log(3).")
