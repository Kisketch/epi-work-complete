from fractions import Fraction
from math import factorial, comb, isqrt
from pathlib import Path
import re

def indices(x, windows):
    a, b = x.numerator, x.denominator
    q0, q = 1, 0
    den = []
    while b and q <= windows[-1]:
        z, r = divmod(a, b)
        q0, q = q, z*q + q0
        den.append(q)
        a, b = b, r
    return [max(i for i, v in enumerate(den) if v <= h) for h in windows]

P, Q = [1, 3], [1, 1]
for j in range(1, 160):
    P.append((4*j+2)*P[-1]+P[-2])
    Q.append((4*j+2)*Q[-1]+Q[-2])
for j in range(len(P)):
    terms = [comb(j+t, 2*t)*factorial(2*t)//factorial(t) for t in range(j+1)]
    assert (P[j],Q[j]) == (sum(terms),sum((-1)**(j+t)*v for t,v in enumerate(terms)))
for T in range(2, 132, 2):
    assert all((v[j+T]-v[j])%T == 0 for v in (P,Q) for j in range(len(v)-T))
H = [isqrt(j*Q[j]**2) for j in range(1,86)]
e0 = sum((Fraction(1,factorial(i)) for i in range(401)), Fraction(0))
x = Fraction(17,3)-e0
i1, i2 = indices(x,H), indices(x-Fraction(2,factorial(401)),H)
assert i1 == i2
word = [i1[j]-i1[j-1] for j in range(37,55)]
for j in range(22,85):
    assert i1[j]-i1[j-1] == word[(j-1)%18]
assert all(any(word[i]!=word[(i+t)%18] for i in range(18)) for t in (1,2,3,6,9))
src = next(Path.cwd().glob('*e_plus_pi.tex')).read_text(encoding='utf-8-sig')
assert ','.join(map(str, word))+'.' in src
print('P,Q closed form: 161 pairs. Congruence: all even moduli 2..130.')
print('17/3-e: 85 interval-certified cutoff indices. Least period of theorem word: 18.')
print(word)
