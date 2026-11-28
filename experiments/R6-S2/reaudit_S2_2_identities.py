"""reaudit_S2_2: exact checks of the algebraic steps of proofs/R6-S2.md (independent rewrite; no reuse of common.py).

  A1  block propagation  X_{n_k+1+j} = K[1,j] X_{n_k+1} + K[2,j] X_{n_k}   (X = q, p, D(m,.))
  A2  splitting identity K(x1..xm) = K(x1..x_{i-1})K(x_i..x_m) + K(x1..x_{i-2})K(x_{i+1}..x_m)
  A2b left recurrence
  F2/D3  determinant, D(m,m)=0, D(m,m+1)=(-1)^m, recurrence of D(m,.)
  D4  sum_{j<=k} q_{n_j} <= 4 q_{n_k};  sum_{j>k} 1/q_{n_j+1} <= 4/q_{n_{k+1}+1}  (worst case: all digits 1)
  B1  1/theta_{n_k} in OPEN interval (A_k, A_k+2); report extremal observed values; q_{n-1}/q_n = 1 reachable
  B4  limit identity  K_{[i,l]}/c_i' + K_{[1,i-2]}/c_i = K/(c_i c_i')   (exact Fractions)
  gcd(sigma,K)=1 (stated in S.1, not used by the proof)
All exact integer / Fraction arithmetic except B1 (mpmath, dps 60, with exact rational complete quotients).
"""
import itertools, random
from fractions import Fraction
from math import gcd

def K(ws):
    a, b = 0, 1
    for w in ws:
        a, b = b, w * b + a
    return b

def Kint(W, a, b):  # K_{[a,b]} with 1-based inclusive, b >= a-2
    if b == a - 2:
        return 0
    return K(W[a - 1:b])

fails = {k: 0 for k in ["A1", "A2", "A2b", "F2", "D3", "D4i", "D4ii", "B4", "gcd", "B1"]}
counts = {k: 0 for k in fails}

def words(maxlen, maxdig):
    for l in range(0, maxlen + 1):
        for W in itertools.product(range(1, maxdig + 1), repeat=l):
            yield W

# A2 / A2b / B4 / gcd: exhaustive small words
for W in words(6, 5):
    l = len(W)
    Kw = K(W)
    for i in range(1, l + 1):
        counts["A2"] += 1
        lhs = Kw
        rhs = K(W[:i - 1]) * K(W[i - 1:]) + (K(W[:i - 2]) if i >= 2 else 0) * K(W[i:])
        if lhs != rhs: fails["A2"] += 1
        counts["A2b"] += 1
        if Kint(W, i, l) != W[i - 1] * Kint(W, i + 1, l) + Kint(W, i + 2, l): fails["A2b"] += 1
        ci, cpi = Kint(W, 1, i - 1), Kint(W, i + 1, l)
        counts["B4"] += 1
        if Fraction(Kint(W, i, l), cpi) + Fraction(Kint(W, 1, i - 2), ci) != Fraction(Kw, ci * cpi): fails["B4"] += 1
    if l >= 1:
        counts["gcd"] += 1
        if gcd(Kint(W, 1, l - 1), Kw) != 1: fails["gcd"] += 1

def cf_pq(a):
    p, q = [a[0]], [1]
    pm, qm = 1, 0
    for n in range(1, len(a)):
        p.append(a[n] * p[-1] + (p[-2] if n >= 2 else pm))
        q.append(a[n] * q[-1] + (q[-2] if n >= 2 else qm))
    return p, q

random.seed(1)
for trial in range(400):
    l = random.randint(0, 5)
    W = tuple(random.randint(1, 6) for _ in range(l))
    N = random.randint(0, 3)
    a0 = random.randint(-3, 3)
    pre = [random.randint(1, 4) for _ in range(N)]
    nblocks = 8
    A = [random.randint(1, 3) * k for k in range(1, nblocks + 2)]  # slow and fast, includes A_1 possibly =1
    a = [a0] + pre
    for k in range(nblocks + 1):
        a.append(A[k]); a.extend(W)
    p, q = cf_pq(a)
    nk = lambda k: N + (k - 1) * (l + 1)
    for n in range(0, len(a) - 1):
        counts["F2"] += 1
        if p[n + 1] * q[n] - p[n] * q[n + 1] != (-1) ** n: fails["F2"] += 1
    def D(m, n): return q[m] * p[n] - p[m] * q[n]
    for m in range(0, len(a) - 3):
        counts["D3"] += 1
        bad = D(m, m) != 0 or D(m, m + 1) != (-1) ** m
        for n in range(1, len(a) - 1):
            if D(m, n + 1) != a[n + 1] * D(m, n) + D(m, n - 1): bad = True
        if bad: fails["D3"] += 1
    for k in range(1, nblocks):
        for X in (q, p, [D(nk(1), n) for n in range(len(a))], [3 * q[n] - 7 * p[n] for n in range(len(a))]):
            for j in range(0, l + 1):
                counts["A1"] += 1
                if X[nk(k) + 1 + j] != Kint(W, 1, j) * X[nk(k) + 1] + Kint(W, 2, j) * X[nk(k)]: fails["A1"] += 1

# D4 worst case: geometric growth slowest when all partial quotients are 1 (Fibonacci); test l=0 and others
for l in range(0, 4):
    for N in range(0, 3):
        a = [0] + [1] * (N + 60 * (l + 1) + 5)
        p, q = cf_pq(a)
        nk = lambda k: N + (k - 1) * (l + 1)
        kmax = 55
        worst_i = worst_ii = Fraction(0)
        for k in range(1, kmax - 3):
            counts["D4i"] += 1
            r = Fraction(sum(q[nk(j)] for j in range(1, k + 1)), q[nk(k)])
            worst_i = max(worst_i, r)
            if r > 4: fails["D4i"] += 1
            counts["D4ii"] += 1
            s = sum(Fraction(1, q[nk(j) + 1]) for j in range(k + 1, kmax)) * q[nk(k + 1) + 1]
            worst_ii = max(worst_ii, s)
            if s > 4: fails["D4ii"] += 1
        print(f"D4 all-ones digits l={l} N={N}: max ratio (i) {float(worst_i):.6f}, (ii) {float(worst_ii):.6f} (bound 4)")

# B1 open interval, exact complete quotients via long finite tail, mpmath for division
import mpmath as mp
mp.mp.dps = 60
minlo = mp.inf; maxhi = -mp.inf; ratio_one_seen = False
random.seed(7)
for trial in range(300):
    l = random.randint(0, 4)
    W = tuple(random.randint(1, 4) for _ in range(l))
    N = random.choice([0, 0, 1, 2])
    pre = [1] * N
    a = [0] + pre
    A = [random.choice([1, 1, 2, 5]) + (k - 1) for k in range(1, 30)]
    for k in range(29):
        a.append(A[k]); a.extend(W)
    p, q = cf_pq(a)
    # complete quotients alpha_m from the truncated tail (tail error << 1e-40 at the indices used)
    x = mp.mpf(a[-1]); cq = {}
    for m in range(len(a) - 2, 0, -1):
        x = a[m] + 1 / x; cq[m] = x
    for k in range(1, 12):
        n = N + (k - 1) * (l + 1)
        inv = cq[n + 1] + (Fraction(q[n - 1], q[n]) if n >= 1 else 0)
        inv = mp.mpf(inv) if not isinstance(inv, mp.mpf) else inv
        inv = cq[n + 1] + (mp.mpf(q[n - 1]) / q[n] if n >= 1 else 0)
        Ak = A[k - 1]
        counts["B1"] += 1
        lo, hi = inv - Ak, Ak + 2 - inv
        minlo = min(minlo, lo); maxhi = max(maxhi, -hi)
        if not (lo > 0 and hi > 0): fails["B1"] += 1
        if n >= 1 and q[n - 1] == q[n]: ratio_one_seen = True
print("B1: min (1/theta - A_k) =", mp.nstr(minlo, 8), "; max (1/theta - A_k - 2) =", mp.nstr(maxhi, 8))
print("B1: case q_{n_k-1}/q_{n_k} = 1 occurred (so the closed bound [0,1] is attained):", ratio_one_seen)

print()
for k in fails:
    print(f"{k:5s}: cases {counts[k]:7d}  failures {fails[k]}")
print("ALL PASS:", all(v == 0 for v in fails.values()))
