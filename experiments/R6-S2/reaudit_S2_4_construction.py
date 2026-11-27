"""reaudit_S2_4: end-to-end test of the realization S1(d) (proof section 5.6) and of the block-limit formula
(section 7.1 steps 2-4 / 7.2 step 9), independent rewrite (mpmath + exact integers).

For each test case:
  alpha = [a0; pre, A_1, W, A_2, W, ...] truncated after KT blocks (A_k given by a rule, incl. slow A_k = k),
  data (r_k, tau_k) = periodic walk around a minimal closed walk C* (threshold method) or random data,
  beta  = (1/K) sum_{k<=KT} T'_k |eps_{n_k}|  exactly as in 5.6 (T'_1 = T_1 + sigma*r0~).
Checks (k up to KMAX << KT):
  (d2)  P^(k)_{n_k} = 0 mod K and s_k := P^(k)_{n_k+1} = r_k mod K   (exact integers)
  label r_k(beta) := round(K y_{n_k+1}) mod K equals the given r_k from some k on (report first k after which always equal)
  |K g_k| vs the section-8 bound 4T/A_k + 4T/A_{k+1}   (g_k := q_{n_k+1} beta - s_k/K - nearest integer)
  A_k*|K E^past_rest(n_k)| <= 4T/A_{k-1},  A_k*|K E^fut(n_k)| <= 4T/A_{k+1}   (5.6 (d3))
  |t_k - tau_k| -> 0
  |M_k - max(|tau_k|, v(r_k))| -> 0  and  last-window max of M_k vs nu(W) (for C* data: should approach nu).
Category 4 evidence only.
"""
import random, math
from fractions import Fraction as F
import mpmath as mp

def Kc(ws):
    a, b = 0, 1
    for w in ws:
        a, b = b, w * b + a
    return b

def data(W):
    l = len(W); K = Kc(W)
    c = [Kc(W[:i - 1]) for i in range(1, l + 1)]
    cp = [Kc(W[i:]) for i in range(1, l + 1)]
    sigma = c[-1] if l else 1
    return K, c, cp, sigma

def dK(x, K):
    x %= K
    return min(x, K - x)

def vcost(W):
    K, c, cp, s = data(W)
    return [max([F(dK(ci * r, K), ci * cpi) for ci, cpi in zip(c, cp)], default=F(0)) for r in range(K)]

def min_edge(W, a, b):
    K, c, cp, s = data(W)
    base = F((b - s * a) % K, K)
    ts = [base + m for m in (-2, -1, 0, 1)]
    ts = [t for t in ts if not (a == 0 and b == 0 and t == 0)]
    return min(ts, key=abs)

def min_cycle(W):
    """threshold method + explicit cycle extraction; returns (nu, list of (r_prev, r, t))."""
    K, c, cp, s = data(W); v = vcost(W)
    cands = sorted(set([x for x in v if x <= 1] + [F(d, K) for d in range(0, K + 1)]))
    for lam in cands:
        nodes = {r for r in range(K) if v[r] <= lam}
        adj = {a: {b for b in nodes if abs(min_edge(W, a, b)) <= lam} for a in nodes}
        changed = True
        while changed:
            changed = False
            for x in list(nodes):
                if not (adj[x] & nodes) or not any(x in adj[y] for y in nodes):
                    nodes.discard(x); changed = True
        if nodes:
            x = min(nodes); seen = []
            while x not in seen:
                seen.append(x); x = min(adj[x] & nodes)
            cyc = seen[seen.index(x):] + [x]
            walk = [(cyc[i], cyc[i + 1], min_edge(W, cyc[i], cyc[i + 1])) for i in range(len(cyc) - 1)]
            cost = max([v[a] for a, _, _ in walk] + [abs(t) for _, _, t in walk])
            assert cost == lam
            return lam, walk
    raise RuntimeError

def run(W, a0, pre, Arule, mode, KT=110, KMAX=95, seed=0, label=""):
    rng = random.Random(seed)
    K, c, cp, sigma = data(W); l = len(W); v = vcost(W); N = len(pre)
    A = [Arule(k) for k in range(1, KT + 2)]
    a = [a0] + list(pre)
    for k in range(KT + 1):
        a.append(A[k]); a.extend(W)
    M = len(a) - 1
    p = [a0]; q = [1]; pm, qm = 1, 0
    for n in range(1, M + 1):
        p.append(a[n] * p[-1] + (p[-2] if n >= 2 else pm)); q.append(a[n] * q[-1] + (q[-2] if n >= 2 else qm))
    nk = lambda k: N + (k - 1) * (l + 1)
    dps = int(2.2 * math.log10(q[M])) + 60
    mp.mp.dps = dps
    alpha = mp.mpf(p[M]) / q[M]
    eps = [q[n] * alpha - p[n] for n in range(M + 1)]
    theta = [q[n] * abs(eps[n]) for n in range(M + 1)]
    # data
    if mode == "cycle":
        nu, walk = min_cycle(W); L = len(walk)
        r0 = walk[-1][1]
        rs = [r0] + [walk[(k - 1) % L][1] for k in range(1, KT + 1)]
        taus = [None] + [walk[(k - 1) % L][2] for k in range(1, KT + 1)]
    else:
        nu, _ = min_cycle(W)
        rs = [rng.randrange(K) for _ in range(KT + 1)]
        taus = [None]
        for k in range(1, KT + 1):
            base = F((rs[k] - sigma * rs[k - 1]) % K, K)
            taus.append(base + rng.choice([-2, -1, 0, 1]) if mode == "random" else base - (1 if base > F(1, 2) else 0))
    T = [None] + [int(t * K) for t in taus[1:]]
    Tp = list(T); Tp[1] = T[1] + sigma * (rs[0] % K)
    Tmax = max(abs(x) for x in Tp[1:])
    x = [None] + [(-1) ** nk(k) * Tp[k] for k in range(1, KT + 1)]
    beta = sum(Tp[k] * abs(eps[nk(k)]) for k in range(1, KT + 1)) / K
    def D(m, n): return q[m] * p[n] - p[m] * q[n]
    def y(n):
        z = q[n] * beta
        return z - mp.nint(z)
    bad_d2 = 0; first_ok = None; maxKg_ratio = 0; maxpast = 0; maxfut = 0
    tdev = []; Mdev = []; Mvals = []
    for k in range(1, KMAX + 1):
        P_nk = sum(x[j] * D(nk(j), nk(k)) for j in range(1, k + 1))
        s_k = sum(x[j] * D(nk(j), nk(k) + 1) for j in range(1, k + 1))
        if P_nk % K != 0 or (s_k - rs[k]) % K != 0:
            bad_d2 += 1
        # label
        if l >= 1:
            yk1 = y(nk(k) + 1)
            lab = int(mp.nint(K * yk1)) % K
            Kg = K * (q[nk(k) + 1] * beta - mp.mpf(s_k) / K)
            Kg = Kg - K * mp.nint(Kg / K)  # remove K*z_k
            bound = mp.mpf(4 * Tmax) / A[k - 1] + mp.mpf(4 * Tmax) / A[k]
            maxKg_ratio = max(maxKg_ratio, abs(Kg) / bound)
        else:
            lab = 0
        if lab == rs[k] % K:
            if first_ok is None: first_ok = k
        else:
            first_ok = None
        # n_k error terms
        n = nk(k)
        past_rest = sum(x[j] * q[nk(j)] for j in range(1, k)) * eps[n]
        fut = sum(x[j] * q[n] * eps[nk(j)] for j in range(k + 1, KT + 1))
        if k >= 2:
            maxpast = max(maxpast, A[k - 1] * abs(past_rest) / (mp.mpf(4 * Tmax) / A[k - 2]))
        maxfut = max(maxfut, A[k - 1] * abs(fut) / (mp.mpf(4 * Tmax) / A[k]))
        tk = A[k - 1] * y(n)
        tdev.append(abs(tk - mp.mpf(taus[k].numerator) / taus[k].denominator))
        Mk = max(abs(y(nk(k) + i)) / theta[nk(k) + i] for i in range(0, l + 1))
        pred = max(abs(taus[k]), v[rs[k] % K]) if lab == rs[k] % K else None
        if pred is not None:
            Mdev.append((k, abs(Mk - mp.mpf(pred.numerator) / pred.denominator)))
        Mvals.append(Mk)
    win = Mvals[-20:]
    print(f"[{label}] W={W} K={K} sigma={sigma} N={N} a0={a0} mode={mode} nu={nu} Tmax={Tmax} dps={dps}")
    print(f"   (d2) exact congruence failures: {bad_d2}/{KMAX}")
    print(f"   canonical label equals given r_k for all k >= {first_ok} (up to KMAX={KMAX})")
    if l >= 1:
        print(f"   max |K g_k| / (4T/A_k + 4T/A_k+1) over k<=KMAX: {mp.nstr(maxKg_ratio, 6)}  (must be < 1)")
    print(f"   max A_k|K E^past_rest| / (4T/A_(k-1)): {mp.nstr(maxpast, 6)};  max A_k|K E^fut| / (4T/A_(k+1)): {mp.nstr(maxfut, 6)}  (must be < 1; note |E| here is w/o the 1/K, so ratio uses K*E/K)")
    print(f"   |t_k - tau_k| at k=10,40,KMAX: {mp.nstr(tdev[9],4)}, {mp.nstr(tdev[39],4)}, {mp.nstr(tdev[-1],4)}")
    if Mdev:
        print(f"   |M_k - max(|tau_k|, v(r_k))| at last k={Mdev[-1][0]}: {mp.nstr(Mdev[-1][1],4)}; max over last 20: {mp.nstr(max(d for _, d in Mdev[-20:]),4)}")
    print(f"   max M_k over last 20 blocks: {mp.nstr(max(win),8)}   nu = {float(nu):.8f}   (cycle data: -> nu; random data: >= nu - o(1))")
    return dict(bad=bad_d2, Kg=maxKg_ratio, past=maxpast, fut=maxfut, winmax=max(win), nu=nu)

# Note: the bounds in 5.6 (d3) are for K*E; past_rest and fut computed above are sum x_j ... without 1/K, i.e. already K*E.
res = []
res.append(run((5, 1, 5), 0, [], lambda k: k, "cycle", label="slow A_k=k"))
res.append(run((5, 1, 5), 3, [2, 7, 1], lambda k: k + 3, "cycle", label="prefix, A_k=k+3"))
res.append(run((1, 1), 0, [], lambda k: k, "cycle", label="e-type, K=2 even"))
res.append(run((2, 2), 0, [1], lambda k: k, "cycle", label="K=5"))
res.append(run((1, 3, 1), 1, [], lambda k: 2 * k, "cycle", label="K=5, sigma=4"))
res.append(run((3, 1, 3), 0, [], lambda k: k, "cycle", label="min nu in table"))
res.append(run((2,), 0, [], lambda k: k, "cycle", label="K=2, l=1"))
res.append(run((), 0, [], lambda k: k, "cycle", label="l=0"))
res.append(run((1,), -2, [4], lambda k: k, "cycle", label="K=1, l=1"))
res.append(run((5, 1, 5), 0, [], lambda k: k, "random", seed=3, label="random data"))
res.append(run((3, 1, 3), 0, [1, 1], lambda k: k + 1, "random", seed=5, label="random data"))
res.append(run((1, 1), 0, [], lambda k: k, "minimal", seed=8, label="minimal-|t| random labels, K=2 (label K/2 occurs)"))
res.append(run((1, 2, 1), 0, [], lambda k: k, "minimal", seed=9, label="K=4 even, random labels incl. K/2"))
res.append(run((2, 1, 2), 0, [3], lambda k: k, "minimal", seed=10, label="K=8 even, random labels incl. K/2"))
print()
print("summary: all (d2) exact:", all(r["bad"] == 0 for r in res),
      "| all |Kg| bound ratios < 1:", all(r["Kg"] < 1 for r in res),
      "| all E^past/E^fut ratios < 1:", all(r["past"] < 1 and r["fut"] < 1 for r in res))
