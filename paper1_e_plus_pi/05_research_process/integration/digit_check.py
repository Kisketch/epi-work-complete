"""Exact interval checks for the window-digit formula, from the project root."""
from fractions import Fraction
from math import factorial, gcd, isqrt
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "C" / "round2"))
from verify import atan, cv

def hermite(limit):
    P, Q = [1, 3], [1, 1]
    for j in range(1, limit):
        P.append((4*j+2)*P[-1]+P[-2])
        Q.append((4*j+2)*Q[-1]+Q[-2])
    return P, Q

def blocks(lo, hi, Q):
    H = [isqrt(j*q*q) for j,q in enumerate(Q)]
    digits = cv(lo, hi, H[-1])
    cuts = [max(i for i, (_,d,_) in enumerate(digits) if d <= h) for h in H[1:]]
    return {j: tuple(a for _,_,a in digits[cuts[j-1]+1:cuts[j]+1])
            for j in range(1,len(cuts))}

P, Q = hermite(150)
e0 = sum((Fraction(1,factorial(i)) for i in range(701)),Fraction(0))
for A, B in [(6,1),(11,2),(17,3),(23,4),(29,5),(5,2)]:
    hi = Fraction(A,B)-e0
    words = blocks(hi-Fraction(2,factorial(701)),hi,Q)
    count = 0
    for j,u in words.items():
        T = 2*B*B
        if 4*(j-1)<=9*B*B or j+T not in words:
            continue
        v = words[j+T]
        M = gcd(A*Q[j]-B*P[j], B*Q[j])
        assert v == (u[0]+4*M*M,)+u[1:]
        count += 1
    print(A,B,'exact word comparisons:',count)
a,b = atan(5,800)
c,d = atan(239,300)
words = blocks(16*a-4*d,16*b-4*c,Q)
for j,u in words.items():
    B = 3
    v = words.get(j+18,())
    if 4*(j-1)>81 and len(u)==len(v) and len(u)%2 and (v[0]-u[0])%4:
        print('pi, B=3:',j,j+18,u,v)
        break
else:
    raise AssertionError('no example')
