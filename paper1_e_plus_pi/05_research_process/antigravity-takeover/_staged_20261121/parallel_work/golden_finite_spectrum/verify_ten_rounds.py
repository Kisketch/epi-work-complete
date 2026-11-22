"""Exact checks for the arithmetic and finite-state examples."""

from fractions import Fraction as F
from math import gcd

from golden_finite_spectrum import PHI, Quadratic, height, signed_divisors
from quadratic_phase_certificate import finite_slice, normal_cycle


def trace_subset(tau, cap):
    root = Quadratic(F(0), F(1), tau.delta)
    cycles = {normal_cycle(tau), normal_cycle(tau.conjugate())}
    lo, hi = -(-(1-cap)*root).floor(), ((1+cap)*root).floor()
    accepted = []
    for m in range(lo, hi+1):
        if (m*m-tau.delta) % 4:
            continue
        norm = (m*m-tau.delta)//4
        for a in sorted(d for d in signed_divisors(norm) if d>0):
            if gcd(a, m, norm//a) == 1 and normal_cycle((-m+root)/(2*a)) in cycles:
                accepted.append(m)
                break
    values = sorted(abs(1-m/root) for m in accepted)
    assert values == finite_slice(tau, {((),())}, cap)
    return accepted, values


root = Quadratic(F(0), F(1), 60)
for tau, period, ticks in (
    (root/2, (1,6), [4,6,8,10]),
    (root/6, (2,3), [6,10]),
):
    assert normal_cycle(tau) == normal_cycle(tau.conjugate()) == period
    accepted, values = trace_subset(tau, F(1,2))
    assert accepted == ticks
    print("Delta 60, cyclic period", period, "trace slice", accepted, "minimum", values[0])
assert (8*8-60)//4 == 1 and (4*4-60)//4 == -11

for delta in (5,8,12,13,21,60):
    root = Quadratic(F(0), F(1), delta)
    tau = (delta % 2 + root) / 2
    ticks, values = trace_subset(tau, F(1))
    lo, hi = -(-(1-F(1))*root).floor(), ((1+F(1))*root).floor()
    assert ticks == [m for m in range(lo,hi+1) if m%2==delta%2]
    print(f"Monic discriminant {delta}: {len(values)} values through 1")

# In x=[0;2,3,4,...], r at each growing head is 0 in the limit.
# Here the entire real normalized error lies between the two rational
# forward-quotient endpoints because the fixed-head factor is monotone.
q_prev, q = 0, 1
limit = height(PHI)*abs(PHI.conjugate())
for j in range(1,81):
    b = j+1
    z = F(q_prev,q)
    T_lo, T_hi = F(b), F(b) + F(1,b+1)
    f = lambda T: height(PHI)*abs(T-PHI)*abs(PHI.conjugate()+z)/(T+z)
    assert max(abs(f(T_lo)-limit),abs(f(T_hi)-limit)) <= F(10,j)
    q_prev, q = q, b*q+q_prev
print("Growing-head rate: eighty exact error intervals lie within 10/j of the named limit.")

# Graph with two marked parallel transitions 0 -> 1 and one return 1 -> 0.
# The loop 0 -> 0 is unmarked. The two maximizing cycles alternate.
edges = [(0,0,0),(0,1,1),(0,1,1),(1,0,0)]
def tight(p, direction):
    w = [direction*(F(label)-p) for _,_,label in edges]
    potentials = [F(0),F(0)]
    for u in (0,1):  # simple paths in a two-vertex graph use at most one edge
        potentials[u] = max([F(0)]+[d for (a,b,_),d in zip(edges,w) if a==u and b!=u])
    slack = [potentials[a] - d - potentials[b] for (a,b,_),d in zip(edges,w)]
    assert min(slack) >= 0
    return [i for i,s in enumerate(slack) if s==0]

loss, gain = tight(F(0),-1), tight(F(1,2),1)
assert loss == [0,3] and gain == [1,2,3]
f = [F(0),F(1,4),F(1,4),F(1,2)]
assert sum(f)==1 and sum(a*m for a,(_,_,m) in zip(f,edges))==F(1,2)
for v in (0,1):
    assert sum(f[i] for i,e in enumerate(edges) if e[0]==v)==sum(f[i] for i,e in enumerate(edges) if e[1]==v)
assert sum(f[i] for i in (1,2)) == F(1,2) and f[1]==f[2]
print("Tight edge indices",loss,gain,": recurrent endpoint roots 1 and sqrt(2), p_max=1/2.")
