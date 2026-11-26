from mpmath import mp, mpf, e, nint, pi
from fractions import Fraction as F
import random
mp.dps = 1500
N = 40
P = [1, 3]; Q = [1, 1]
for j in range(1, N):
    P.append((4*j+2)*P[j]+P[j-1]); Q.append((4*j+2)*Q[j]+Q[j-1])
d = lambda k: Q[k]*e-P[k]
for j in range(N):
    assert P[j]*Q[j+1]-P[j+1]*Q[j] == 2*(-1)**(j+1), j
    assert abs(d(j)*Q[j+1]-d(j+1)*Q[j]-2*(-1)**j) < mpf(10)**-300
    assert P[j] % 2 == 1 and Q[j] % 2 == 1
    assert abs(d(j)) <= mpf(2)/Q[j+1], j
    assert abs(e-mpf(P[j])/Q[j]) <= mpf(2)/(Q[j]*Q[j+1])
    if j >= 1: assert Q[j] >= 6**(j-1)
    if 1 <= j and j+1 < N: assert Q[j+1] >= (4*j+2)*Q[j]
print("det, parity, |delta|<=2/Q_{j+1}, F1 OK; P",P[:5],"Q",Q[:5],"err",mp.nstr(abs(e-mpf(P[N-1])/Q[N-1]),5))

def arcs(Nn, lam):
    return [(F(k, Nn)-lam/(2*Nn), F(k, Nn)+lam/(2*Nn)) for k in range(Nn)]
def inter(a, b): return max(F(0), min(a[1], b[1])-max(a[0], b[0]))
bad = 0; worst = F(0); cnt = 0
for t in range(400):
    B = random.choice([1, 2, 3]); i = random.choice([1, 2]); j = i+random.choice([1, 2])
    Ni = B*Q[i]; Nj = B*Q[j]
    if Nj > 300: continue
    li = F(random.randint(0, 100), 100); lj = F(random.randint(0, 100), 100)
    tot = F(0)
    for a in arcs(Ni, li):
        for k in range(Nj):
            for s in (-1, 0, 1):
                b = (F(k, Nj)-lj/(2*Nj)+s, F(k, Nj)+lj/(2*Nj)+s)
                tot += inter(a, b)
    err = abs(tot-li*lj); bound = 2*lj*F(Ni, Nj); cnt += 1
    if err > bound: bad += 1
    if bound: worst = max(worst, err/bound)
print("lemma trials", cnt, "violations", bad, "worst err/bound", float(worst))
print("sum 6^-k <= 1/5:", sum(F(1, 6**k) for k in range(1, 80)) <= F(1, 5))
c = mpf('0.249')
J = next(j for j in range(2, 10**5) if c*(4+mpf(2)/j+mpf(1)/(j+1)+mpf(1)/(j-1)) < 1)
print("c=.249 first J =", J)
nd = lambda x: abs(x-nint(x))
for name, z in [("1/2", mpf(1)/2), ("e/2", e/2), ("(e+1)/2", (e+1)/2), ("e", e), ("1/3", mpf(1)/3), ("pi", pi), ("3e+7", 3*e+7), ("(3e+5)/2", (3*e+5)/2)]:
    print(name, [mp.nstr(j*nd(Q[j]*z), 4) for j in (5, 10, 15, 20)])
