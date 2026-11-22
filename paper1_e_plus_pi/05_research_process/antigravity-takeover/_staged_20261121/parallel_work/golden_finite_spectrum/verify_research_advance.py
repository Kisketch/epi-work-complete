from pathlib import Path
from fractions import Fraction as F
from math import comb, factorial, gcd, sqrt, cos, sin, pi
from itertools import groupby

from golden_finite_spectrum import Quadratic
from quadratic_phase_certificate import normal_cycle


def atan_bounds(base, length):
    value = sum((F((-1)**i, (2*i+1)*base**(2*i+1)) for i in range(length)), F(0))
    endpoint = value + F((-1)**length, (2*length+1)*base**(2*length+1))
    return min(value, endpoint), max(value, endpoint)


def certified_floor(lo, hi):
    assert lo // 1 == hi // 1, "Increase interval precision"
    return lo // 1


def convergents(lo, hi, cutoff):
    p, d, old_p, old_d = 1, 0, 0, 1
    results = []
    while d <= cutoff:
        a = certified_floor(lo, hi)
        p, d, old_p, old_d = a*p+old_p, a*d+old_d, p, d
        results.append((p, d, a))
        if d > cutoff:
            break
        lo, hi = 1/(hi-a), 1/(lo-a)
    return results


def e_windows(n):
    old_p, p, old_q, q = 1, 3, 1, 1
    for j in range(1, n+1):
        yield j, p, q
        p, old_p = (4*j+2)*p+old_p, p
        q, old_q = (4*j+2)*q+old_q, q


def strip_checks(pi_lo, pi_hi, e_lo, e_hi):
    windows = list(e_windows(100))
    cutoff = 2*windows[-1][0]*windows[-1][2]
    targets = [('pi', pi_lo, pi_hi, None, None)]
    targets.extend((f"{a}/{b}-e", F(a,b)-e_hi, F(a,b)-e_lo, a, b)
                   for a,b in [(6,1), (17,3), (43,7)])
    for name,lo,hi,a,b in targets:
        c = convergents(lo,hi,cutoff)
        hist = {bb: [] for bb in range(1,13)} if b is None else {b: []}
        strong_hist = {bb: [] for bb in hist}
        budget_windows = 0
        simple = []
        for j,P,q in windows:
            for ((p,d,_),(_,s,_)) in zip(c,c[1:]):
                if d > 2*j*q:
                    break
                if 2*q <= d <= j*q:
                    simple.append(j)
                budget = F(d,2*j*q)+F(q,s)
                factor = gcd(q*d,d*P+q*p)
                for bb,ind in hist.items():
                    if bb*budget <= factor:
                        if b is not None:
                            assert b*q*p == d*(a*q-b*P)
                        elif (bb*q)%d and j not in strong_hist[bb]:
                            strong_hist[bb].append(j)
                    if bb*budget <= 1:
                        budget_windows += 1
                        if b is not None:
                            assert b*q*p == d*(a*q-b*P)
                        if b is None and (bb*q) % d and j not in ind:
                            ind.append(j)
        if b is None:
            assert simple and hist[1]
            print(f"Pi, j <= 100, simple B=1 strip hit at {len(set(simple))} indices.")
            print("Budget contradictions by B=1..12:",
                  [len(hist[bb]) for bb in range(1,13)])
            print("Budget contradictions using gcd, same finite search:",
                  [len(strong_hist[bb]) for bb in range(1,13)])
            subs = hist[1]
            print("First/last indices for B=1:", subs[:3], subs[-3:])
            runs = [len(list(block)) for a,block in groupby(row[2] for row in c) if a==1]
            print(f"Pi, {len(c)} certified partial quotients including integer part; longest ones run {max(runs)}.")
        else:
            assert budget_windows
            print(f"{name}: {budget_windows} exact checks of the locking identity.")


def digits(lo, hi, largest):
    xfact = factorial(1)
    prev = certified_floor(xfact*lo, xfact*hi)
    result = []
    for n in range(1,largest+1):
        xfact *= n+1
        cur = certified_floor(xfact*lo, xfact*hi)
        digit = cur-(n+1)*prev
        assert 0 <= digit <= n
        result.append((n,digit))
        prev = cur
    return result


def factorial_checks(pi_lo, pi_hi, e_lo, e_hi):
    act = digits(-pi_hi,-pi_lo,240)
    different = [n for n,d in act if d!=1]
    print(f"-pi, n <= 240: {len(different)} digits different from 1, last at n={different[-1]}.")
    for k,r in [(0,F(13,17)),(1,F(-11,6)),(4,F(9,14))]:
        vals = digits(k*e_lo+r,k*e_hi+r,240)
        for n,d in vals:
            if n>=max(r.denominator,k+2):
                assert d==k
    print("Three factorial controls with k=0,1,4 certified.")


def trace_checks():
    delta = 60
    t = Quadratic(F(0),F(1,6),delta)
    target = (3-2*t)/(t-2)
    root = Quadratic(F(0),F(1),delta)
    assert target == (-16+root)/14
    assert not any(x*x%5==2 for x in range(5))
    assert not any(x*x%3==2 for x in range(3))
    mono, nonmono = normal_cycle(root/2), normal_cycle(t)
    assert nonmono != mono
    assert [normal_cycle((-16+root)/(2*a)) for a in (1,7,49)] == [mono,nonmono,mono]
    print("Discriminant 60, m=16, a=1,7,49: exact cycles", mono,nonmono,mono)


def closed_walks(height, a, b, steps):
    state = [0]*(2*height+1)
    state[height] = 1
    for _ in range(steps):
        new = [0]*len(state)
        for idx,count in enumerate(state):
            if idx>0:
                new[idx-1] += b*count
            if idx+1<len(state):
                new[idx+1] += a*count
        state=new
    return state[height]


def strip_graph_checks():
    a,b=2,3
    for m in range(1,21):
        assert closed_walks(1,a,b,2*m) == (2*a*b)**m
        assert closed_walks(m,a,b,2*m) == comb(2*m,m)*(a*b)**m
    for h in range(1,9):
        size=2*h+1
        phase=pi/(size+1)
        sym = sqrt(a*b)
        eigenvalue=2*sym*cos(phase)
        diagonal=[sin(i*phase) for i in range(size+2)]
        for i in range(1,size+1):
            assert abs(sym*(diagonal[i-1]+diagonal[i+1])-eigenvalue*diagonal[i]) < 1e-12
    print("Width-1 and unconstrained closed-walk counts checked exactly at 20 even lengths.")
    print("Explicit sine eigenpair checked at widths 1..8 (floating-point regression).")


if __name__=='__main__':
    atan5=atan_bounds(5,600)
    atan239=atan_bounds(239,240)
    pi_lo,pi_hi=16*atan5[0]-4*atan239[1],16*atan5[1]-4*atan239[0]
    e_lo=sum((F(1,factorial(i)) for i in range(440)),F(0))
    e_hi=e_lo+F(2,factorial(440))
    strip_checks(pi_lo,pi_hi,e_lo,e_hi)
    factorial_checks(pi_lo,pi_hi,e_lo,e_hi)
    trace_checks()
    strip_graph_checks()


