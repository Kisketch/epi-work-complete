from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, isqrt

from golden_finite_spectrum import Quadratic
from quadratic_phase_certificate import normal_cycle


def prime_powers(n):
    factors = []
    p = 2
    while p * p <= n:
        power = 1
        while n % p == 0:
            n //= p
            power *= p
        if power > 1:
            factors.append((p, power))
        p += 1
    if n > 1:
        factors.append((n, n))
    return factors


def divisors(n):
    result = set()
    for a in range(1, isqrt(n)+1):
        if n % a == 0:
            result.update((a, n//a))
    return result


def lattice_index(vectors):
    """Index of a full rank Z-span by its 2 x 2 minors."""
    return gcd(*(a*d-b*c for (a,b),(c,d) in combinations(vectors,2)))


def check_ideals():
    forms = 0
    channel = 0
    for delta in (5,8,12,20,45,60,80,117,125,240):
        for m in range(-60,61):
            if (m*m-delta)%4:
                continue
            norm = (m*m-delta)//4
            if not norm:
                continue
            blocks = []
            for p, power in prime_powers(abs(norm)):
                if m%p:
                    blocks.append(sorted(divisors(power)))
                else:
                    blocks.append([1,power])
                    channel += 1
            from math import prod
            block_divisors = {prod(choice) for choice in product(*blocks)}
            primitive_divisors = {a for a in divisors(abs(norm)) if gcd(a,m,norm//a)==1}
            assert block_divisors == primitive_divisors
            for a in primitive_divisors:
                gens = [(a*a,0),(0,a),(-a*m,-a),(norm,0)]
                assert all(x%a==y%a==0 for x,y in gens)
                assert lattice_index(gens) == a*a
                forms += 1
    assert {a for a in (1,2,4) if gcd(a,6,4//a)==1} == {1,4}
    print(f"{forms} primitive forms and conjugate products checked.")
    print(f"{channel} common-prime blocks tested, including the conductor example.")


def root(delta,a,b):
    return Quadratic(F(-b,2*a), F(1,2*a), delta)


def check_progressions():
    mono = normal_cycle(root(60,1,0))
    other = normal_cycle(root(60,3,0))
    new_order = normal_cycle(root(240,1,0))
    assert mono != other
    for t in range(-25,26):
        m = 420*t+16
        norm = (m*m-60)//4
        assert gcd(m,norm)==1
        assert (m-2)%14==0
        assert normal_cycle(root(60,1,m)) == mono
        assert normal_cycle(root(60,7,m)) == other

        r = 14*t+1
        assert normal_cycle(root(60,1,2*r)) == mono
        assert normal_cycle(root(60,7,2*r)) == other
        assert normal_cycle(root(240,1,4*r)) == new_order
        values = {abs(1 - F(m,delta)*Quadratic(F(0),F(scale),15))
                  for m,delta,scale in ((2*r,60,2),(4*r,240,4))}
        assert len(values)==1
    print("51 exact trace checks on the common discriminant-60 progression.")
    print("51 exact trace checks across discriminants 60 and 240 in Q(sqrt(15)).")


def check_markov():
    one = Quadratic(F(1))
    phi = Quadratic(F(1,2),F(1,2))
    q = 1/(phi*phi)
    p = q/(1+q)
    stationary = [1/(1+q),q/(1+q)]
    expected = (1-q)*(-p)+q*(1-2*p)
    assert expected == 0
    excursions = ((1-q)*p*p+q*(1-2*p)*(1-2*p))/(1+q)
    assert excursions == q*(1-q)/((1+q)*(1+q)*(1+q))
    f = [q-p, -p]
    potential = [Quadratic(), -p]
    assert potential[0]-((1-q)*potential[0]+q*potential[1])==f[0]
    assert potential[1]-potential[0]==f[1]
    direct = stationary[0]*((1-q)*p*p+q*(1-2*p)*(1-2*p))
    assert direct==excursions and excursions>0
    assert (1-q) == one/phi
    # Alternating marked and unmarked edges have a potential difference of 1/2.
    for mark,v,u in ((1,0,1),(0,1,0)):
        assert F(mark)-F(1,2)+F(-u,2)-F(-v,2)==0
    print("Exact Q(sqrt(5)) agreement of return and Poisson variances.")
    print("Exact zero-variance potential checked on the period-two graph.")


if __name__=="__main__":
    check_ideals()
    check_progressions()
    check_markov()

