"""Exact checks of the metric bounds and the locked slopes on rational affine models."""
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "C" / "round2"))
from verify import cv

assert F(3,5)**13 > F(51,100)**10
assert F(5,6)**10 / F(11,2)**3 > F(49,100)**10
u = F(5,2)
for x, bounds in [(0,(619,90,41,224)), (1,(464,115,57,346))]:
    y = 1+x/u
    powers = [(y/(a+x+1/u))**10 for a in (1,5,9)]
    powers.append(F(7,12)**7*y**10/(9+x+1/u)**3)
    assert all(power < F(b,1000)**7 for power,b in zip(powers,bounds))
print("Both lower-bound and eight endpoint inequalities passed by rational arithmetic.")
e0 = sum((F(1,factorial(k)) for k in range(351)), F(0))
P, Q = [1,3],[1,1]
for j in range(1,70):
    P.append((4*j+2)*P[-1]+P[-2])
    Q.append((4*j+2)*Q[-1]+Q[-2])
for A,C,B in [(6,-2,1),(17,-1,3),(1,2,5),(-3,1,2)]:
    lo,hi=sorted(((A+C*e0)/B,(A+C*(e0+F(2,factorial(351))))/B))
    conv=cv(lo,hi,isqrt(70*Q[-1]**2))
    count=0
    prev=None
    for j in range(1,71):
        H=isqrt(j*Q[j]**2)
        p,d,_=next(r for r in reversed(conv) if r[1]<=H)
        model=F(A*Q[j]+C*P[j],B*Q[j])
        if j>=30:
            assert F(p,d)==model
            if prev is not None:
                assert (model-prev)/(F(P[j],Q[j])-F(P[j-1],Q[j-1]))==F(C,B)
                count+=1
            prev=model
    print((A,C,B),count,'exact slopes',F(C,B))
