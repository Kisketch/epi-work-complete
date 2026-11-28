# audit_new_1_to_4.py -- skeptic audit of paper_draft.tex, NEW-1 .. NEW-4 (category 4: finite computation)
# Independent code (does not import experiments/R6-S2/*). Run: python3 -I audit_new_1_to_4.py > audit_new_1_to_4.out
import itertools, random
from fractions import Fraction as Fr
import mpmath as mp

mp.mp.dps = 1200

def cf_of(x, n):
    """first n partial quotients of the real x (mpmath, Gauss algorithm)"""
    out = []
    for _ in range(n):
        a = int(mp.floor(x)); out.append(a)
        fr = x - a
        if fr == 0: break
        x = 1 / fr
    return out

def convergents(a):
    p, q = [1, a[0]], [0, 1]          # index shift: p[1]=p_0, p[0]=p_{-1}
    for k in range(1, len(a)):
        p.append(a[k] * p[-1] + p[-2]); q.append(a[k] * q[-1] + q[-2])
    return p[1:], q[1:], p[0], q[0]    # p_n, q_n (n>=0), p_{-1}, q_{-1}

def distZ(x):
    return abs(x - mp.nint(x))

print("=== NEW-1: theta_n = q_n |q_n a - p_n| equals q_n ||q_n a|| for n>=1 (not nec. n=0) ===")
random.seed(1)
bad_n_ge_1 = 0; n0_diff = 0; trials = 0
for t in range(300):
    a = [random.randint(-3, 3)] + [random.choice([1, 1, 1, 2, 3, 5, 9, 40]) for _ in range(60)]
    # value of the infinite CF approximated by the truncation: tail irrelevant for first 50 indices at dps 1200
    x = mp.mpf(a[-1])
    for c in reversed(a[:-1]): x = c + 1 / x
    p, q, _, _ = convergents(a)
    for n in range(0, 50):
        e1 = abs(q[n] * x - p[n]); e2 = distZ(q[n] * x)
        if n >= 1 and abs(e1 - e2) > mp.mpf(10) ** (-1000): bad_n_ge_1 += 1
        if n == 0 and abs(e1 - e2) > mp.mpf(10) ** (-1000): n0_diff += 1
    trials += 1
print(f"random alphas: {trials}; mismatches for 1<=n<50: {bad_n_ge_1}; alphas with mismatch at n=0: {n0_diff}")
x = mp.mpf(7) / 10 + mp.sqrt(2) / 1000
print(f"explicit n=0 example alpha={mp.nstr(x,8)}: |q0 a - p0|={mp.nstr(abs(x - mp.floor(x)),8)}, ||a||={mp.nstr(distZ(x),8)}")
print("also check q_{n+1} >= 2 for n>=1 (min over trials): ", min(convergents([0]+[1]*5)[1][2:]))

print("\n=== NEW-3: alpha=(e-1)/2 ===")
alpha = (mp.e - 1) / 2
J = 220
a = cf_of(alpha, J + 2)
expect = [0, 1] + [4 * k - 2 for k in range(2, J + 2)]
print("partial quotients match [0;1,6,10,...] for first", len(a), ":", a == expect[:len(a)])
p, q, _, _ = convergents(a)
Q = [1, 1]
for j in range(1, J + 1): Q.append((4 * j + 2) * Q[j] + Q[j - 1])
print("q_j == Q_j for 0<=j<=", J, ":", all(q[j] == Q[j] for j in range(J + 1)))
# block-Hurwitz parametrisation: N=1, a0=0, a1=1, W=(), n_k = N+(k-1)(l+1) = k, A_k = a_{n_k+1}
N, ell = 1, 0
okA = all(a[(N + (k - 1) * (ell + 1)) + 1] == 4 * k + 2 for k in range(1, J))
print("a_{n_k+1} == 4k+2 with n_k=k for 1<=k<", J, ":", okA)
viol = []; minlow = mp.inf; minup = mp.inf
for j in range(1, J):
    th = q[j] * abs(q[j] * alpha - p[j])
    inv = 1 / th
    lo = inv - (4 * j + 2); up = (4 * j + 4) - inv
    minlow = min(minlow, lo); minup = min(minup, up)
    if not (lo > 0 and up > 0): viol.append(j)
print(f"4j+2 < 1/theta_j < 4j+4 for 1<=j<{J}: violations={viol}; min margins: lower {mp.nstr(minlow,6)}, upper {mp.nstr(minup,6)}")
for j in [1, 2, 10, 100, 200]:
    th = q[j] * abs(q[j] * alpha - p[j])
    print(f"  j={j}: 1/theta_j={mp.nstr(1/th,12)}, j*theta_j={mp.nstr(j*th,12)}")
print("(e+1)/2 - alpha - 1 =", mp.nstr((mp.e + 1) / 2 - alpha - 1, 5), " (so Z+Z(e+1)/2 = Z alpha + Z)")
# (iii) identity j||Q_j z|| = (j theta_j) R_j termwise, and limsup ratio -> 1/4 on a few z
random.seed(3)
for z in [mp.mpf(1) / 2, mp.sqrt(3), alpha / 3, mp.pi]:
    rows = []
    for j in range(150, 200):
        th = q[j] * abs(q[j] * alpha - p[j]); R = distZ(q[j] * z) / th
        lhs = j * distZ(Q[j] * z)
        rows.append(abs(lhs - j * th * R))
    print(f"  z={mp.nstr(z,6)}: max |j||Q_j z|| - (j theta_j) R_j| over 150<=j<200 = {mp.nstr(max(rows),3)}")
# beta_0 with KL=1: witness from Thm A for W=empty is the loop at 0 with t=1, i.e. tau_k=1, T'_k = K*tau_k = 1
K = 1
beta0 = sum(abs(q[n] * alpha - p[n]) for n in range(1, J)) / K   # n_k = k, T'_k=1, x_k eps = |eps|
Rs = [distZ(q[n] * beta0) / (q[n] * abs(q[n] * alpha - p[n])) for n in range(150, 200)]
ks = [n * distZ(Q[n] * beta0) for n in range(150, 200)]
print(f"  beta0=sum_k |eps_k| (Lemma S1(d), all T'_k=1): R_n over 150<=n<200 in [{mp.nstr(min(Rs),8)},{mp.nstr(max(Rs),8)}];"
      f" j||Q_j beta0|| in [{mp.nstr(min(ks),8)},{mp.nstr(max(ks),8)}] (predicted 1 and 1/4)")

print("\n=== NEW-2: nu for W in {(), (1), (1,1)} by brute force over simple cycles (independent code) ===")
def cont(w):
    a, b = 1, 0   # K() = 1, K(len -1) = 0
    for x in w: a, b = x * a + b, a
    return a
def dK(x, K): return min(abs(x - s * K) for s in range(x // K - 2, x // K + 3)) if K > 0 else None
def nu_brute(W):
    l = len(W); K = cont(W)
    sig = cont(W[:l - 1]) if l >= 1 else 1
    c = [cont(W[:i - 1]) for i in range(1, l + 1)]; cp = [cont(W[i:]) for i in range(1, l + 1)]
    v = {r: (max(Fr(dK(c[i] * r, K), c[i] * cp[i]) for i in range(l)) if l else Fr(0)) for r in range(K)}
    def labels(r, rp):   # all t in (rp - sig r)/K + Z with |t| <= 1
        base = Fr(rp - sig * r, K); out = []
        for m in range(-3, 4):
            t = base + m
            if abs(t) <= 1: out.append(t)
        return out
    best = None
    verts = list(range(K))
    for L in range(1, min(K, 4) + 1):
        for cyc in itertools.permutations(verts, L):
            if cyc[0] != min(cyc): continue
            edges = [(cyc[m], cyc[(m + 1) % L]) for m in range(L)]
            for ts in itertools.product(*[labels(a_, b_) for a_, b_ in edges]):
                if L == 1 and cyc[0] == 0 and ts[0] == 0: continue  # trivial loop
                cost = max([v[r] for r in cyc] + [abs(t) for t in ts])
                if best is None or cost < best: best = cost
    return K, sig, c, cp, v, best
for W in [(), (1,), (1, 1), (2,), (5, 1, 5), (3, 1, 3)]:
    K, sig, c, cp, v, best = nu_brute(W)
    print(f"W={W}: K={K} sigma={sig} c={c} c'={cp} v={ {r: str(x) for r, x in v.items()} if K<=8 else '...'} nu(simple cycles, K<=4-cycles)={best}")
print("(for K>4 only cycles of length <=4 are enumerated: an upper bound only; the K<=2 cases are exhaustive)")

print("\n=== NEW-4: e = [2;1,2,1,1,4,...] as block-Hurwitz with N=1, W=(1,1), A_k=2k (numerical, category 4) ===")
ae = cf_of(mp.e, 400)
N, W = 1, (1, 1); ell = 2
ok = ae[0] == 2 and ae[1] == 1
for k in range(1, 120):
    nk = N + (k - 1) * (ell + 1)
    ok &= ae[nk + 1] == 2 * k and ae[nk + 2] == 1 and ae[nk + 3] == 1
print("first 362 partial quotients of e fit the pattern:", ok, "(finite check; NOT a proof of the expansion)")
p, q, _, _ = convergents(ae)
for k in [10, 50, 100]:
    nk = N + (k - 1) * 3
    w = [1 / (q[nk + i] * abs(q[nk + i] * mp.e - p[nk + i])) for i in range(3)]
    print(f"  k={k}: A_k theta_nk={mp.nstr(2*k/w[0],10)}, 1/theta_(nk+1)={mp.nstr(w[1],10)}, 1/theta_(nk+2)={mp.nstr(w[2],10)} (Lemma B: 1, 2, 2)")
# Lean example11: W=(1,1), A_k=k, N=0, a0=0 -> [0;1,1,1,2,1,1,3,...]
seq = [0]
for k in range(1, 4): seq += [k, 1, 1]
print("example11 first terms (N=0, A_k=k, W=(1,1)):", seq[:10])
