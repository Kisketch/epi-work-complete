"""v2audit_S2_3: exact-integer checks of D1-D4, (A1), (d2)(i)(ii) and the c_i s_k congruence,
Lemma B1 open interval (A_k, A_k+2) (exact rationals via finite-CF sandwich), Lemma 0 constant 3/4.
Adversarial data: A_k starting at 1, slow growth, N=0, a_0!=0, K=1, K=2, even K, random r_0, T_k."""
import random
from fractions import Fraction as F
random.seed(20261127)

def Kc(w):
    a, b = 0, 1
    for x in w: a, b = b, x * b + a
    return b

def build(a0, head, W, A):
    a = [a0] + list(head)
    N = len(head); l = len(W); nk = []
    for k, Ak in enumerate(A, start=1):
        nk.append(len(a) - 1)  # n_k: a_{n_k+1}=A_k
        a.append(Ak); a.extend(W)
    for k in range(1, len(A) + 1):
        assert nk[k - 1] == N + (k - 1) * (l + 1)
    return a, nk

def pq(a):
    p = [1, a[0]]; q = [0, 1]  # index shift: p[n+1] = p_n
    for n in range(1, len(a)):
        p.append(a[n] * p[-1] + p[-2]); q.append(a[n] * q[-1] + q[-2])
    return p, q  # p_n = p[n+1]

fails = 0
def check(c, m):
    global fails
    if not c:
        fails += 1
        if fails < 30: print("FAIL", m)

words = [(), (1,), (2,), (1, 1), (3,), (1, 2), (2, 2), (5, 1, 5), (1, 1, 1), (2, 1, 2), (4,), (3, 1, 1, 3), (1, 3, 1)]
trials = 0
for W in words:
    l = len(W); K = Kc(W); sigma = Kc(W[:l - 1]) if l >= 1 else 1
    c = [Kc(W[:i - 1]) for i in range(1, l + 1)]
    for trial in range(40):
        trials += 1
        a0 = random.choice([0, 0, -3, 7]); N = random.choice([0, 0, 1, 3])
        head = [random.randint(1, 4) for _ in range(N)]
        M = 14
        mode = trial % 4
        if mode == 0: A = list(range(1, M + 1))
        elif mode == 1: A = [1] * 3 + [2 + k // 3 for k in range(M - 3)]
        elif mode == 2: A = [random.randint(1, 50) for _ in range(M)]
        else: A = [k * k for k in range(1, M + 1)]
        a, nk = build(a0, head, W, A)
        p, q = pq(a); P = lambda n: p[n + 1]; Q = lambda n: q[n + 1]
        L = len(a) - 1
        # F2
        for n in range(-1, L):
            check(P(n + 1) * Q(n) - P(n) * Q(n + 1) == (-1) ** n, "F2")
        # D1
        for n in range(0, L):
            check(Q(n + 1) >= a[n + 1] * Q(n) and Q(n + 1) >= Q(n) >= 1, "D1")
        for m in range(0, L - 1):
            check(Q(m + 2) >= 2 * Q(m), "D1b")
        # D4 (finite truncations: (ii) checked on partial sums, which only makes it easier; also tail-free)
        for k in range(1, M + 1):
            check(sum(Q(nk[j]) for j in range(k)) <= 4 * Q(nk[k - 1]), "D4i")
        for k in range(1, M - 1):
            s = sum(F(1, Q(nk[j] + 1)) for j in range(k, M))
            check(s <= F(4, Q(nk[k] + 1)), "D4ii")
        D = lambda m, n: Q(m) * P(n) - P(m) * Q(n)
        # (A1) for q and for D(m',.)
        for k in range(1, M):
            for j in range(0, l + 1):
                n0 = nk[k - 1]
                check(Q(n0 + 1 + j) == Kc(W[:j]) * Q(n0 + 1) + (Kc(W[1:j]) if j >= 1 else 0) * Q(n0), "A1 q")
                mp = random.randint(0, L - 1)
                check(D(mp, n0 + 1 + j) == Kc(W[:j]) * D(mp, n0 + 1) + (Kc(W[1:j]) if j >= 1 else 0) * D(mp, n0), "A1 D")
        # (d2): random data r_0..r_M, T_k = r_k - sigma r_{k-1} + K*m (random, possibly large)
        r = [random.randrange(K) for _ in range(M + 1)]
        T = [None] + [(r[k] - sigma * r[k - 1]) % K + K * random.randint(-3, 3) for k in range(1, M + 1)]
        Tp = T[:]; Tp[1] = T[1] + sigma * r[0]
        x = [None] + [(-1) ** nk[k - 1] * Tp[k] for k in range(1, M + 1)]
        for k in range(1, M + 1):
            Pk = lambda n: sum(x[j] * D(nk[j - 1], n) for j in range(1, k + 1))
            n0 = nk[k - 1]
            check(Pk(n0) % K == 0, f"d2(i) W={W} k={k}")
            sk = Pk(n0 + 1)
            check((sk - r[k]) % K == 0, f"d2(ii) W={W} k={k}")
            for i in range(1, l + 1):
                check((Pk(n0 + i) - c[i - 1] * sk) % K == 0, "d2 c_i s_k")
        # Lemma B1: 1/theta_{n_k} in (A_k, A_k+2): theta_n = 1/(alpha_{n+1}+q_{n-1}/q_n).
        # alpha_{n+1} lies strictly between the two truncations [a_{n+1};...,a_m] (m=L-1, L) -> exact bracket
        def cf(seq):
            v = F(seq[-1])
            for t in reversed(seq[:-1]): v = t + 1 / v
            return v
        for k in range(1, M - 1):
            n0 = nk[k - 1]
            lo_hi = [cf(a[n0 + 1:L]) + F(Q(n0 - 1), Q(n0)), cf(a[n0 + 1:L + 1]) + F(Q(n0 - 1), Q(n0))]
            lo, hi = min(lo_hi), max(lo_hi)
            check(A[k - 1] < lo and hi < A[k - 1] + 2, f"B1 W={W} k={k}")
print("trials:", trials, "FAILS:", fails)

# Lemma 0, step 0.2 constant: sup of theta_{n+1}+a_{n+1}theta_n+theta_{n-1} over random CFs (must be < 3)
mx = 0
for _ in range(3000):
    a = [random.randint(0, 3)] + [random.choice([1, 1, 1, 2, random.randint(1, 1000)]) for _ in range(40)]
    p, q = pq(a); Q = lambda n: q[n + 1]
    def cf(seq):
        v = F(seq[-1])
        for t in reversed(seq[:-1]): v = t + 1 / v
        return v
    def th(n):  # upper estimate of theta_n using the truncation that makes it larger
        b1 = cf(a[n + 1:40]); b2 = cf(a[n + 1:41])
        return 1 / (min(b1, b2) + F(Q(n - 1), Q(n)))
    for n in range(1, 30):
        mx = max(mx, float(th(n + 1) + a[n + 1] * th(n) + th(n - 1)))
print("Lemma 0.2: max of theta_{n+1}+a_{n+1}theta_n+theta_{n-1} (upper estimates) =", mx, "(<3 needed)")
