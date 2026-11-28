"""R6-S2 repair round 2: numerical cross-checks of the inequalities newly written in proofs/R6-S2.md (section 8, (d3)).

These checks are side evidence only; the proof derives every inequality symbolically.

Part A (audit m1).  Section 5.6: T_k := K tau_k, T'_1 := T_1 + sigma*r0~ (r0~ in [0,K)), T'_k := T_k (k>=2),
  T_max := max(sup_k |T_k|, |T'_1|), tau'_k := T'_k / K, tau'_max := sup_k |tau'_k|, tau_max := sup_k |tau_k|.
  A1: exhaustive exact check of  T_max <= K tau_max + sigma (K-1)  (worst case tau_max = |tau_1|; triangle inequality).
  A2: end-to-end: build beta of section 5.6 and compare |K g'_k|  (g'_k := E^past_{n_k+1} + E^fut_{n_k+1},
      computed as K q_{n_k+1} beta - s_k reduced mod K) against
        (i)   8 K tau'_max / min(A_k, A_{k+1})                         [new primary form]
        (ii)  8 (K tau_max + sigma (K-1)) / min(A_k, A_{k+1})           [new alternative form]
        (iii) 8 K tau_max / min(A_k, A_{k+1})                           [the WRONG form of repair round 1; must fail
                                                                         on the audit counterexample at k = 1]
Part B (audit m4).  Section 5.2-5.4 for a beta (here: generic random beta, and section-5.6 betas), with
  s_k := nearest integer to K y_{n_k+1}, g_k := y_{n_k+1} - s_k/K, r_k := s_k mod K, e_{k,i} := c_i g_k + K_[2,i-1] y_{n_k}:
  B1: |K g_k| <= |y_{n_{k+1}}| + K_[2,l] |y_{n_k}|  <  Rb (1/A_{k+1} + K_[2,l]/A_k),          Rb := max(R_{n_k}, R_{n_{k+1}})
  B2: | |y_{n_k+i}| - d_K(c_i r_k)/K | <= |e_{k,i}| <= c_i|g_k| + K_[2,i-1]|y_{n_k}|
        <  Rb ( (c_i/K)(1/A_{k+1} + K_[2,l]/A_k) + K_[2,i-1]/A_k )
  B3: dist(t_{k+1} - (r_{k+1} - sigma r_k)/K, Z) <= |g_{k+1}| + |e_{k,l}|
  B4: |t_k| < R_{n_k}
  (with R_n <= Kc+1 for n >= n_{k0}, Rb <= Kc+1, which is the form written in section 8.)
Exact integers for p_n, q_n, D(m,n); mpmath with dps ~ 2.2 log10 q_M + 60.
"""
import math, random, itertools
from fractions import Fraction as F
import mpmath as mp

OUT = []
def P(s=""):
    OUT.append(s); print(s, flush=True)

def cont(ws):
    a, b = 0, 1
    for w in ws: a, b = b, w * b + a
    return b

def Kint(W, a, b):           # K_[a,b] (1-based, inclusive); b = a-1 -> 1, b = a-2 -> 0
    if b == a - 2: return 0
    return cont(W[a - 1:b])

def centred(x, K):
    x %= K
    return x - K if 2 * x > K else x

def dK(x, K):
    x %= K
    return min(x, K - x)

# ---------------------------------------------------------------- Part A1
P("== Part A1: exhaustive check  T_max <= K tau_max + sigma (K-1)  (exact integers) ==")
words = [()]
for L in range(1, 5):
    words += list(itertools.product(range(1, 6), repeat=L))
cnt = 0; viol = 0; tight = 0
for W in words:
    K = cont(W); sigma = cont(W[:-1]) if len(W) >= 1 else 1
    for r0 in range(K):
        for r1 in range(K):
            base = (r1 - sigma * r0) % K
            for m in range(-3, 4):                     # T_1 = base + m K  (tau_1 = T_1/K in (r1 - sigma r0)/K + Z)
                T1 = base + m * K
                # worst case for the right side: tau_max = |tau_1| (other tau_k smaller); also test tau_max larger
                for extra in (0, 1, 5):
                    Ktau_max = abs(T1) + extra * K
                    Tp1 = T1 + sigma * r0
                    Tmax = max(Ktau_max, abs(Tp1))     # sup_k |T_k| = K tau_max ; T_max = max(that, |T'_1|)
                    rhs = Ktau_max + sigma * (K - 1)
                    cnt += 1
                    if Tmax > rhs: viol += 1
                    if Tmax == rhs and sigma * (K - 1) > 0: tight += 1
P(f"words: {len(words)} (all words over {{1..5}} of length <= 4, plus empty); cases: {cnt}; violations: {viol}; "
  f"cases with equality (and sigma(K-1)>0): {tight}")
assert viol == 0

# ---------------------------------------------------------------- helpers for A2 / B
def build(W, N_blocks, A, a0=0, head=()):
    """alpha = [a0; head, A_1, W, A_2, W, ...] truncated after N_blocks blocks."""
    a = [a0] + list(head)
    for k in range(N_blocks): a += [A[k]] + list(W)
    p = [a[0]]; q = [1]
    pm, qm = 1, 0
    for n in range(1, len(a)):
        p.append(a[n] * p[-1] + (p[-2] if n >= 2 else pm))
        q.append(a[n] * q[-1] + (q[-2] if n >= 2 else qm))
    return a, p, q

def setup(W, N_blocks, A, head=()):
    a, p, q = build(W, N_blocks, A, head=head)
    M = len(a) - 1
    mp.mp.dps = int(2.2 * math.log10(q[M])) + 60
    alpha = mp.mpf(p[M]) / q[M]
    eps = [q[n] * alpha - p[n] for n in range(M + 1)]
    theta = [abs(q[n] * eps[n]) for n in range(M + 1)]
    return a, p, q, M, eps, theta

def ynear(x):
    return x - mp.nint(x)

# ---------------------------------------------------------------- Part A2
P()
P("== Part A2: end-to-end, section 5.6 construction; |K g'_k| vs three bounds ==")
def partA2(W, r0, rs, taus, A, KT, tag):
    l = len(W); K = cont(W); sigma = cont(W[:-1]) if l >= 1 else 1
    a, p, q, M, eps, theta = setup(W, KT + 1, A)
    nk = lambda k: (k - 1) * (l + 1)
    T = [None] + [int(taus[k] * K) for k in range(1, KT + 1)]
    for k in range(1, KT + 1):
        assert F(T[k], 1) == taus[k] * K
        prev = r0 if k == 1 else rs[k - 1]
        assert (T[k] - (rs[k] - sigma * prev)) % K == 0
    Tp = list(T); Tp[1] = T[1] + sigma * (r0 % K)
    tau_max = max(abs(taus[k]) for k in range(1, KT + 1))
    taup_max = max(abs(F(Tp[k], K)) for k in range(1, KT + 1))
    Tmax = max(max(abs(x) for x in T[1:]), abs(Tp[1]))
    beta = sum(Tp[k] * abs(eps[nk(k)]) for k in range(1, KT + 1)) / K
    D = lambda m, n: q[m] * p[n] - p[m] * q[n]
    x = [None] + [(-1) ** nk(k) * Tp[k] for k in range(1, KT + 1)]
    P(f"[{tag}] W={W} K={K} sigma={sigma} r0={r0} tau_1={taus[1]} T_1={T[1]} T'_1={Tp[1]} "
      f"K tau_max={K*tau_max} K tau'_max={K*taup_max} T_max={Tmax} K tau_max+sigma(K-1)={K*tau_max + sigma*(K-1)}")
    ok_i = ok_ii = True; fail_iii = []
    for k in range(1, KT - 1):
        s_k = sum(x[j] * D(nk(j), nk(k) + 1) for j in range(1, k + 1))   # = P^{(k)}_{n_k+1}
        Kg = K * q[nk(k) + 1] * beta - s_k                                 # = K g'_k + K*(integer)... reduce:
        # K q beta = s_k + K g'_k  exactly (q beta = P/K + E^past + E^fut, g'_k := E^past + E^fut); no reduction needed
        Kgp = Kg
        mA = min(A[k - 1], A[k])
        b_i = 8 * K * mp.mpf(taup_max.numerator) / taup_max.denominator / mA
        b_ii = mp.mpf(8 * (K * tau_max + sigma * (K - 1))) / mA
        b_iii = 8 * K * mp.mpf(tau_max.numerator) / tau_max.denominator / mA
        if not abs(Kgp) <= b_i: ok_i = False
        if not abs(Kgp) <= b_ii: ok_ii = False
        if not abs(Kgp) <= b_iii: fail_iii.append(k)
        if k <= 3:
            lab = int(mp.nint(K * ynear(q[nk(k) + 1] * beta))) % K
            P(f"   k={k}: |K g'_k|={mp.nstr(abs(Kgp), 6)}  (i) {mp.nstr(b_i, 6)}  (ii) {mp.nstr(b_ii, 6)}  "
              f"(iii) {mp.nstr(b_iii, 6)}  label={lab} given={rs[k] % K}")
    P(f"   all k in 1..{KT-2}: (i) holds: {ok_i};  (ii) holds: {ok_ii};  (iii) fails at k in {fail_iii}")
    return ok_i, ok_ii, fail_iii

# audit counterexample
W = (1, 9, 9); K = cont(W); sigma = cont(W[:-1]); KT = 14
A = [1000 + k for k in range(1, KT + 3)]
rs = [None] + [0] * KT
r0 = 90
taus = [None]
for k in range(1, KT + 1):
    prev = r0 if k == 1 else rs[k - 1]
    taus.append(F(centred(rs[k] - sigma * prev, K), K))
oi, oii, fiii = partA2(W, r0, rs, taus, A, KT, "audit counterexample")
assert oi and oii and 1 in fiii
allok = True
rng = random.Random(20261127)
for trial in range(12):
    L = rng.randint(1, 4)
    W = tuple(rng.randint(1, 9) for _ in range(L))
    K = cont(W); sigma = cont(W[:-1])
    KT = 10
    A = [rng.randint(20, 200) * k for k in range(1, KT + 3)]
    r0 = rng.randrange(K)
    rs = [None] + [rng.randrange(K) for _ in range(KT)]
    taus = [None]
    for k in range(1, KT + 1):
        prev = r0 if k == 1 else rs[k - 1]
        taus.append(F(centred(rs[k] - sigma * prev, K) + K * rng.randint(-1, 1), K))
    oi, oii, _ = partA2(W, r0, rs, taus, A, KT, f"random {trial}")
    allok = allok and oi and oii
P(f"Part A2 random trials: (i) and (ii) hold in all: {allok}")
assert allok

# ---------------------------------------------------------------- Part B
P()
P("== Part B: section 5.2-5.4 bounds (B1-B4) per block, Rb := max of the R_n actually used ==")
def partB(W, A, KT, beta_fn, tag):
    l = len(W); K = cont(W); sigma = cont(W[:-1])
    a, p, q, M, eps, theta = setup(W, KT + 1, A)
    beta = beta_fn(eps, theta, q)
    nk = lambda k: (k - 1) * (l + 1)
    y = [ynear(q[n] * beta) for n in range(M + 1)]
    R = [abs(y[n]) / theta[n] for n in range(M)]   # theta_M = 0 for the truncated alpha; only n < M is used
    c = [None] + [Kint(W, 1, i - 1) for i in range(1, l + 1)]
    K2l = Kint(W, 2, l)
    nviol = 0; nchk = 0; maxdist = mp.mpf(0)
    data = {}
    for k in range(1, KT):
        Ky = K * y[nk(k) + 1]; s = int(mp.nint(Ky)); g = y[nk(k) + 1] - mp.mpf(s) / K; r = s % K
        data[k] = (s, g, r)
    for k in range(1, KT - 1):
        s, g, r = data[k]
        Rb = max(R[nk(k)], R[nk(k + 1)])
        Ak, Ak1 = A[k - 1], A[k]
        # B1
        mid = abs(y[nk(k + 1)]) + K2l * abs(y[nk(k)])
        rhs = Rb * (mp.mpf(1) / Ak1 + mp.mpf(K2l) / Ak)
        nchk += 1; nviol += not (abs(K * g) <= mid * (1 + mp.mpf(10) ** (-30)) and mid < rhs)
        maxdist = max(maxdist, abs(K * g))
        # B2
        for i in range(1, l + 1):
            e = c[i] * g + Kint(W, 2, i - 1) * y[nk(k)]
            lhs = abs(abs(y[nk(k) + i]) - mp.mpf(dK(c[i] * r, K)) / K)
            mid2 = c[i] * abs(g) + Kint(W, 2, i - 1) * abs(y[nk(k)])
            rhs2 = Rb * (mp.mpf(c[i]) / K * (mp.mpf(1) / Ak1 + mp.mpf(K2l) / Ak) + mp.mpf(Kint(W, 2, i - 1)) / Ak)
            nchk += 1
            nviol += not (lhs <= abs(e) * (1 + mp.mpf(10) ** (-30)) + mp.mpf(10) ** (-40)
                          and abs(e) <= mid2 * (1 + mp.mpf(10) ** (-30)) and mid2 < rhs2)
        # B3
        s1, g1, r1 = data[k + 1]
        t1 = A[k] * y[nk(k + 1)]
        val = t1 - mp.mpf(r1 - sigma * r) / K
        dist = abs(val - mp.nint(val))
        eKl = c[l] * g + Kint(W, 2, l - 1) * y[nk(k)]
        nchk += 1; nviol += not (dist <= (abs(g1) + abs(eKl)) * (1 + mp.mpf(10) ** (-30)) + mp.mpf(10) ** (-40))
        # B4
        tk = A[k - 1] * y[nk(k)]
        nchk += 1; nviol += not (abs(tk) < R[nk(k)])
    P(f"[{tag}] W={W} K={K} K_[2,l]={K2l}: checks={nchk} violations={nviol} max|K g_k|={mp.nstr(maxdist, 4)}")
    return nviol

tot = 0
rng = random.Random(7)
for trial in range(10):
    L = rng.randint(1, 4)
    W = tuple(rng.randint(1, 9) for _ in range(L))
    KT = 12
    A = [rng.randint(5, 60) * k + 3 for k in range(1, KT + 3)]
    # generic random beta (Kc may be large / labels arbitrary: the inequalities B1-B4 are unconditional)
    bv = mp.mpf(rng.random())
    tot += partB(W, A, KT, lambda eps, theta, q, bv=bv: bv, f"generic {trial}")
    # section-5.6 beta (finite Kc)
    K = cont(W); sigma = cont(W[:-1]); l = len(W)
    Tp = [None] + [rng.randint(-2 * K, 2 * K) for _ in range(KT + 1)]
    nk = lambda k, l=l: (k - 1) * (l + 1)
    tot += partB(W, A, KT, lambda eps, theta, q, Tp=Tp, K=K, nk=nk:
                 sum(Tp[k] * abs(eps[nk(k)]) for k in range(1, KT + 1)) / K, f"constructed {trial}")
P(f"Part B total violations: {tot}")
assert tot == 0
P()
P("ALL CHECKS PASSED")
with open(__file__.replace(".py", ".out"), "w", encoding="utf-8") as f:
    f.write("\n".join(OUT) + "\n")
