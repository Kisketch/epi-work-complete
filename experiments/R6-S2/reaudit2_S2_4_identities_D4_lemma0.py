"""reaudit2 (R6-S2 after repair round 2) -- self-written by the isolated skeptic.

Exact checks of the elementary ingredients used by the round-2 bounds:
  (A1) block propagation, (A2) splitting identity, (A2b) left recursion   -- exhaustive small words
  D4 (i)/(ii) with extreme partial quotients (all ones, l = 0, N = 0)     -- exact Fractions
  D2  theta_n < 1/a_{n+1}, |eps_n| < 1/q_{n+1}                             -- mpmath
  Lemma 0 step 0.1-0.2: m_n = y_{n+1} - a_{n+1} y_n - y_{n-1} and |m_n| < 3/4 under the hypothesis,
      tested on beta = u alpha + v + delta with tiny delta (hypothesis holds) and on random beta.
Category 4 (finite computation).
"""
import itertools, math, random
from fractions import Fraction as Fr
import mpmath as mp
random.seed(7)

def cont(ws):
    a, b = 0, 1
    for w in ws:
        a, b = b, w * b + a
    return b

def Kseg(x, a, b):  # 1-based K(x_a..x_b), length b-a+1 >= -1
    if b == a - 2: return 0
    if b == a - 1: return 1
    return cont(x[a - 1:b])

bad = 0; n = 0
# (A2) and (A2b)
for m in range(1, 7):
    for x in itertools.product(range(1, 5), repeat=m):
        for i in range(1, m + 1):
            n += 1
            if cont(x) != Kseg(x, 1, i - 1) * Kseg(x, i, m) + Kseg(x, 1, i - 2) * Kseg(x, i + 1, m): bad += 1
            n += 1
            if Kseg(x, i, m) != x[i - 1] * Kseg(x, i + 1, m) + Kseg(x, i + 2, m): bad += 1
print(f'(A2)/(A2b): {n} identities, failures {bad}'); TOT = bad

# (A1): random integer X_{n_k}, X_{n_k+1}, propagate with w's
bad = 0; n = 0
for l in range(0, 7):
    for W in itertools.product(range(1, 4), repeat=l):
        X0, X1 = random.randint(-50, 50), random.randint(-50, 50)
        X = [X0, X1]
        for j in range(1, l + 1):
            X.append(W[j - 1] * X[-1] + X[-2])
        for j in range(0, l + 1):
            n += 1
            if X[1 + j] != Kseg(W, 1, j) * X1 + Kseg(W, 2, j) * X0: bad += 1
print(f'(A1): {n} instances, failures {bad}'); TOT += bad

# D4 with exact q's
def qs(a):
    q = [1]; qm = 0
    for nn in range(1, len(a)):
        q.append(a[nn] * q[-1] + (q[-2] if nn >= 2 else qm))
    return q
bad = 0; n = 0; worst_i = Fr(0); worst_ii = Fr(0)
for (W, N, Akind) in [((), 0, 'ones'), ((1,), 0, 'ones'), ((1, 1), 0, 'ones'), ((), 3, 'ones'), ((2,), 0, 'lin'), ((1,) * 5, 1, 'ones')]:
    KB = 40
    a = [0] + [1] * N
    for k in range(1, KB + 1):
        a.append(1 if Akind == 'ones' else k); a.extend(W)
    q = qs(a); l = len(W)
    nk = lambda k: N + (k - 1) * (l + 1)
    for k in range(1, KB - 5):
        s1 = sum(q[nk(j)] for j in range(1, k + 1))
        n += 1
        if s1 > 4 * q[nk(k)]: bad += 1
        worst_i = max(worst_i, Fr(s1, q[nk(k)]))
        s2 = sum(Fr(1, q[nk(j) + 1]) for j in range(k + 1, KB))   # finite partial sum (lower bound of full)
        n += 1
        if s2 > Fr(4, q[nk(k + 1) + 1]): bad += 1
        worst_ii = max(worst_ii, s2 * q[nk(k + 1) + 1])
print(f'D4: {n} checks, failures {bad}; max ratio (i) {float(worst_i):.6f} (<=4), max ratio (ii) partial {float(worst_ii):.6f} (<=4)'); TOT += bad

# D2 and Lemma 0
def cfdata(a):
    p = [a[0]]; q = [1]
    for nn in range(1, len(a)):
        p.append(a[nn] * p[-1] + (p[-2] if nn >= 2 else 1))
        q.append(a[nn] * q[-1] + (q[-2] if nn >= 2 else 0))
    return p, q
bad = 0; n = 0; maxm = 0
for trial in range(60):
    a = [random.randint(-3, 3)] + [random.choice([1, 1, 2, 3, 50, 1000]) for _ in range(70)]
    p, q = cfdata(a); M = len(a) - 1
    mp.mp.dps = int(2 * math.log10(q[M]) + 50)
    x = mp.mpf(a[M])
    for nn in range(M - 1, -1, -1): x = a[nn] + 1 / x
    eps = [q[nn] * x - p[nn] for nn in range(M + 1)]
    th = [q[nn] * abs(eps[nn]) for nn in range(M + 1)]
    for nn in range(0, M - 30):
        n += 2
        if not th[nn] < mp.mpf(1) / a[nn + 1]: bad += 1
        if not abs(eps[nn]) < mp.mpf(1) / q[nn + 1]: bad += 1
    # Lemma 0
    u, v = random.randint(-9, 9), random.randint(-9, 9)
    for delta in (mp.mpf(10) ** (-int(math.log10(q[M - 30])) * 2 - 5), mp.mpf(random.random())):
        beta = u * x + v + delta
        rho = [int(mp.nint(q[nn] * beta)) for nn in range(M - 30)]
        y = [q[nn] * beta - rho[nn] for nn in range(M - 30)]
        hyp = [abs(y[nn]) < th[nn] / 4 for nn in range(M - 30)]
        for nn in range(1, M - 31):
            mval = a[nn + 1] * rho[nn] + rho[nn - 1] - rho[nn + 1]
            n += 1
            if abs(mval - (y[nn + 1] - a[nn + 1] * y[nn] - y[nn - 1])) > mp.mpf(10) ** -20: bad += 1
            if hyp[nn - 1] and hyp[nn] and hyp[nn + 1]:
                n += 1; maxm = max(maxm, abs(mval))
                if mval != 0: bad += 1
print(f'D2 + Lemma 0 (0.1-0.2): {n} checks, failures {bad}; max |m_n| when hypothesis holds locally: {maxm}')
TOT += bad
print('ALL CHECKS PASSED' if TOT == 0 else 'FAILURES', 'total failures', TOT)
