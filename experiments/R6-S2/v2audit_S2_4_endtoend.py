"""v2audit_S2_4: end-to-end high-precision test of the S1(d) construction and of Step 9/10.
For each W: find an optimal simple cycle C* (brute force, exact), build beta = (1/K) sum T'_k |eps_{n_k}|
on a truncated alpha (mpmath, dps large enough), and report: labels round(K y_{n_k+1}) mod K vs r_k,
t_k - tau_k, block maxima M_k vs nu(W), and the Lemma B limits 1/theta_{n_k+i} vs K/(c_i c_i').
Category 4 (finite computation) evidence only."""
import mpmath as mp
from fractions import Fraction as F
import random, functools
print = functools.partial(print, flush=True)
random.seed(7)
mp.mp.dps = 2500

def Kc(w):
    a, b = 0, 1
    for x in w: a, b = b, x * b + a
    return b

def dK(x, K):
    r = x % K; return min(r, K - r)

def setup(W):
    l = len(W); K = Kc(W); s = Kc(W[:l - 1]) if l >= 1 else 1
    c = [Kc(W[:i - 1]) for i in range(1, l + 1)]; cp = [Kc(W[i:]) for i in range(1, l + 1)]
    v = [max([F(dK(c[i] * r, K), c[i] * cp[i]) for i in range(l)], default=F(0)) for r in range(K)]
    return l, K, s, c, cp, v

def best_cycle(W):
    """threshold method: smallest lambda such that G_lambda has a closed walk through a
    nontrivial edge; the walk is reconstructed by BFS (it is a simple cycle plus the edge)."""
    l, K, s, c, cp, v = setup(W)
    E = []
    for a in range(K):
        for b in range(K):
            base = (b - s * a) % K
            for m in range(-2, 3):
                t = F(base + K * m, K)
                if abs(t) <= 1: E.append((a, b, t))
    cands = sorted(set(v) | {abs(e[2]) for e in E})
    for lam in cands:
        Ev = [e for e in E if abs(e[2]) <= lam and v[e[0]] <= lam and v[e[1]] <= lam]
        adj = {}
        for e in Ev: adj.setdefault(e[0], []).append(e)
        for e in Ev:
            if e[0] == 0 and e[1] == 0 and e[2] == 0: continue
            # BFS from e[1] to e[0]
            prev = {e[1]: None}; queue = [e[1]]; found = (e[1] == e[0])
            while queue and not found:
                nq = []
                for x in queue:
                    for g in adj.get(x, []):
                        if g[1] not in prev:
                            prev[g[1]] = g; nq.append(g[1])
                            if g[1] == e[0]: found = True
                queue = nq
            if found:
                path = []; x = e[0]
                while x != e[1]:
                    g = prev[x]; path.append(g); x = g[0]
                path.reverse()
                edges_ = [e] + path
                verts = [g[0] for g in edges_]; ts = [g[2] for g in edges_]
                return lam, verts, ts
    return None

def run(W, A, a0, head, cyc=None, label=""):
    l, K, s, c, cp, v = setup(W)
    if cyc is None:
        nu, verts, ts = best_cycle(W)
    else:
        verts, ts = cyc; nu = max([v[x] for x in verts] + [abs(t) for t in ts])
    # C* = edges e_m : r^{m-1} -> r^m with t^m; our list verts[0..L-1] with edge verts[i]->verts[i+1]
    L = len(verts)
    rr = [verts[(m) % L] for m in range(L + 1)]  # r^0..r^L
    tt = [None] + [ts[m - 1] for m in range(1, L + 1)]  # t^m for edge r^{m-1}->r^m
    M = len(A)
    a = [a0] + list(head); nk = []
    for Ak in A:
        nk.append(len(a) - 1); a.append(Ak); a.extend(W)
    a.extend([1] * 5)
    alpha = mp.mpf(a[-1])
    for t in reversed(a[:-1]): alpha = t + 1 / alpha
    p = [1, a[0]]; q = [0, 1]
    for n in range(1, len(a)):
        p.append(a[n] * p[-1] + p[-2]); q.append(a[n] * q[-1] + q[-2])
    P = lambda n: p[n + 1]; Q = lambda n: q[n + 1]
    eps = lambda n: Q(n) * alpha - P(n)
    r = [rr[k % L] for k in range(M + 1)]; r[0] = rr[0]
    tau = [None] + [tt[(k - 1) % L + 1] for k in range(1, M + 1)]
    T = [None] + [int(tau[k] * K) for k in range(1, M + 1)]
    for k in range(1, M + 1):
        assert (T[k] - (r[k] - s * r[k - 1])) % K == 0
    Tp = T[:]; Tp[1] = T[1] + s * r[0]
    beta = sum(mp.mpf(Tp[k]) * abs(eps(nk[k - 1])) for k in range(1, M + 1)) / K
    rows = []
    for k in range(1, M - 3):
        n0 = nk[k - 1]
        Rs = []; lab = None; tk = None
        for i in range(0, l + 1):
            n = n0 + i
            x = Q(n) * beta; y = x - mp.nint(x)
            th = Q(n) * abs(eps(n))
            Rs.append(abs(y) / th)
            if i == 0: tk = A[k - 1] * y
        x = Q(n0 + 1) * beta; y1 = x - mp.nint(x)
        lab = int(mp.nint(K * y1)) % K
        rows.append((k, lab, r[k], float(tk - tau[k]), float(max(Rs))))
    print(f"--- {label} W={W} K={K} sigma={s} nu(cycle)={nu} cycle verts={verts} t={[str(t) for t in ts]}")
    print("    A=", A[:6], "... N=", len(head), "a0=", a0)
    for row in rows[-6:]:
        print(f"    k={row[0]:3d} label={row[1]} r_k={row[2]} t_k-tau_k={row[3]: .3e} M_k={row[4]:.6f}")
    late = rows[len(rows) // 2:]
    ok_lab = all(rw[1] == rw[2] for rw in late)
    print(f"    late labels match: {ok_lab}; late max M_k = {max(rw[4] for rw in late[-L:] ):.6f} vs nu = {float(nu):.6f}")
    # Lemma B
    k = M - 5; n0 = nk[k - 1]
    for i in range(1, l + 1):
        th = Q(n0 + i) * abs(eps(n0 + i))
        print(f"    LemmaB i={i}: 1/theta={float(1/th):.8f} limit K/(c c')={K/(c[i-1]*cp[i-1]):.8f}")
    return ok_lab

M = 60
cases = [
    ((), list(range(1, M + 1)), 0, []),
    ((1,), [k * k for k in range(1, M + 1)], 2, [3]),
    ((1, 1), [k * k for k in range(1, M + 1)], 2, []),
    ((2,), [1, 1] + [k * k for k in range(3, M + 1)], -1, [1, 1]),
    ((2, 2), [k * k for k in range(1, M + 1)], 0, []),
    ((5, 1, 5), [k * k for k in range(1, M + 1)], 0, []),
    ((5, 1, 5), [k ** 3 for k in range(1, M + 1)], 5, [2, 7, 1]),
    ((3, 1, 1, 3), [k ** 3 for k in range(1, M + 1)], 0, []),
    ((1, 4, 1), [k ** 3 for k in range(1, M + 1)], 0, []),
]
allok = True
for W, A, a0, head in cases:
    allok &= run(W, A, a0, head)
# C_1 cycle: vertex 0, t=+1 and t=-1, also on W=(5,1,5)
allok &= run((5, 1, 5), [k ** 3 for k in range(1, M + 1)], 0, [], cyc=([0], [F(1)]), label="C_1(t=+1)")
allok &= run((2, 2), [k ** 3 for k in range(1, M + 1)], 0, [], cyc=([0], [F(-1)]), label="C_1(t=-1)")
# r_0 != 0 (T'_1 shift exercised): start the cycle at a nonzero vertex
allok &= run((5, 1, 5), [k ** 3 for k in range(1, M + 1)], 0, [], cyc=([5, 0], [F(1, 7), F(1, 7)]), label="r_0=5")
# zero-jump sigma-orbit 1->2->4->3->1 on W=(2,2) (K=5, sigma=2), all t=0, plus a t=-4/5 variant
allok &= run((2, 2), [k ** 3 for k in range(1, M + 1)], 3, [1], cyc=([1, 2, 4, 3], [F(0), F(0), F(0), F(0)]), label="sigma-orbit r_0=1")
allok &= run((2, 2), [k ** 3 for k in range(1, M + 1)], 0, [], cyc=([1, 2, 4, 3], [F(0), F(-1), F(0), F(0)]), label="orbit with t=-1 jump")
print("ALL LATE LABELS MATCH:", allok)
