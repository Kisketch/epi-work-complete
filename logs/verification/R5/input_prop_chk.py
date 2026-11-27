# LOG-ONLY / NON-CANONICAL / DO NOT CITE
# Finite checks for the input proposition of artifacts/THM-0005/paper_draft.tex
# (prop:input: Hermite integral J_n, delta_j = (-1)^j J_j, P_j/Q_j -> e,
#  P_j = Q_j + 2 p_j, and (e-1)/2 = [0;1,6,10,14,...]).
# These are finite computations; they corroborate but do not replace the paper proof.
from fractions import Fraction
from math import factorial
from mpmath import mp, mpf, e, quad, exp, floor, fabs, nstr

mp.dps = 300
NMAX = 40

# ---- 1. exact polynomial identity  f_{n+1}'' = f_{n-1} - (4n+2) f_n,  f_n = (x(1-x))^n / n!
def pmul(a, b):
    r = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r
def padd(a, b):
    n = max(len(a), len(b)); a = a + [Fraction(0)] * (n - len(a)); b = b + [Fraction(0)] * (n - len(b))
    return [x + y for x, y in zip(a, b)]
def pscale(a, c): return [c * x for x in a]
def pder(a): return [i * a[i] for i in range(1, len(a))] or [Fraction(0)]
def trim(a):
    while len(a) > 1 and a[-1] == 0: a = a[:-1]
    return a
g = [Fraction(0), Fraction(1), Fraction(-1)]          # x - x^2
gp = pder(g)
assert trim(padd(pmul(gp, gp), pscale(g, Fraction(4)))) == [Fraction(1)], "g'^2 = 1 - 4g failed"
f = [[Fraction(1)]]
for n in range(1, NMAX + 2):
    f.append(pscale(pmul(f[-1], g), Fraction(1, n)))
ok_id = all(trim(padd(pder(pder(f[n + 1])), pscale(padd(f[n - 1], pscale(f[n], Fraction(-(4 * n + 2)))), Fraction(-1))))
            == [Fraction(0)] for n in range(1, NMAX + 1))
print("exact identity f_{n+1}'' = f_{n-1} - (4n+2) f_n for n=1..%d:" % NMAX, ok_id)
# boundary values f_m(0)=f_m(1)=f_m'(0)=f_m'(1)=0 for m>=2
def pev(a, x): return sum(c * x ** i for i, c in enumerate(a))
ok_bd = all(pev(f[m], 0) == 0 and pev(f[m], 1) == 0 and pev(pder(f[m]), 0) == 0 and pev(pder(f[m]), 1) == 0
            for m in range(2, NMAX + 2))
print("boundary values vanish for m=2..%d:" % (NMAX + 1), ok_bd)

# ---- 2. integer sequences
N = 400
Q = [1, 1]; P = [1, 3]
for j in range(1, N):
    Q.append((4 * j + 2) * Q[j] + Q[j - 1]); P.append((4 * j + 2) * P[j] + P[j - 1])
# regular-CF convergents of [0;1,6,10,14,...]: c_0=0, c_1=1, c_{k+1}=4k+2 (k>=1)
c = [0, 1] + [4 * k + 2 for k in range(1, N)]
p_m1, p0 = 1, c[0]; q_m1, q0 = 0, 1
p = [p0]; q = [q0]
pp, pc, qq, qc = p_m1, p0, q_m1, q0
for k in range(1, N + 1):
    pp, pc = pc, c[k] * pc + pp; qq, qc = qc, c[k] * qc + qq
    p.append(pc); q.append(qc)
print("q_j == Q_j for j=0..%d:" % (N - 1), all(q[j] == Q[j] for j in range(N)))
print("P_j == Q_j + 2 p_j for j=0..%d:" % (N - 1), all(P[j] == Q[j] + 2 * p[j] for j in range(N)))

# ---- 3. delta_j = Q_j e - P_j  vs  (-1)^j J_j,  J_j = (1/j!) int_0^1 (x(1-x))^j e^x dx
E = +e
worst = mpf(0); ok_sign = True; ok_bound = True
for j in range(0, 31):
    J = quad(lambda x: (x * (1 - x)) ** j * exp(x), [0, mpf(1) / 2, 1]) / factorial(j)
    d = Q[j] * E - P[j]
    rel = fabs(d - (-1) ** j * J) / fabs(J)
    worst = max(worst, rel)
    ok_sign &= (J > 0)
    ok_bound &= (J <= (E - 1) / (mpf(4) ** j * factorial(j)))
print("max rel. err |delta_j - (-1)^j J_j|/J_j, j=0..30:", nstr(worst, 5))
print("J_j > 0 and J_j <= (e-1)/(4^j j!) for j=0..30:", ok_sign and ok_bound)
print("J_0 = e-1:", nstr(quad(lambda x: exp(x), [0, 1]) - (E - 1), 5),
      " J_1 = 3-e:", nstr(quad(lambda x: x * (1 - x) * exp(x), [0, 1]) - (3 - E), 5))
print("P_j/Q_j - e at j=1,2,3,5,10:", [nstr(mpf(P[j]) / Q[j] - E, 6) for j in (1, 2, 3, 5, 10)])

# ---- 4. regular CF of (e-1)/2 computed independently by the Gauss algorithm
mp.dps = 3000
al = (+e - 1) / 2; x = al; a = []
for _ in range(80):
    ip = int(floor(x)); a.append(ip); x = 1 / (x - ip)
print("first 12 CF digits of (e-1)/2:", a[:12])
print("CF digits match [0;1,6,10,...] for 80 terms:", a == c[:80])
print("2/(e-1) digits (first 8):", end=" ")
x = 2 / (+e - 1); b = []
for _ in range(8):
    ip = int(floor(x)); b.append(ip); x = 1 / (x - ip)
print(b)
