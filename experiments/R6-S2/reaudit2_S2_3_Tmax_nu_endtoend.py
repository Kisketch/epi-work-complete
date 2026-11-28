"""reaudit2 (R6-S2 after repair round 2) -- self-written by the isolated skeptic.

Part A  sec 8 (tau): T_max <= K tau_max + sigma (K-1), exact integers, exhaustive over all words of
        length <= 5 with entries <= 4 (and length 6 entries <= 3), all r0~ in [0,K), all T_1 in [-2K, 2K],
        with the tightest admissible tau_max = |T_1|/K (sup over k>=2 taken = 0 or = tau_1).
        Also: equality attained; the bound cannot be lowered to K tau_max + sigma(K-1) - 1 (K>=2);
        gcd(sigma,K)=1; sigma = K(w_1..w_{l-1}).
Part B  independent nu(W) (bottleneck search with exact Fractions), witness cycle.
Part C  end-to-end: build beta from the witness cycle by sec 5.6 (r0 = r^0), alpha_W with A_k = 300 k,
        and report max_{n in block k} R_n for late k  (should approach nu(W));
        also per-vertex limits R_{n_k+i} -> d_K(c_i r_k)/(c_i c_i') and R_{n_k} - |tau_k| -> 0.
Category 4 (finite computation) evidence only.
"""
import itertools, math
from fractions import Fraction as Fr
import mpmath as mp
import numpy as np

def cont(ws):
    a, b = 0, 1
    for w in ws:
        a, b = b, w * b + a
    return b

def data(W):
    l = len(W); K = cont(W)
    c = [cont(W[:i - 1]) for i in range(1, l + 1)]
    cp = [cont(W[i:]) for i in range(1, l + 1)]
    s = c[-1] if l else 1
    return K, c, cp, s

def dK(x, K):
    x %= K
    return min(x, K - x)

# ---------------- Part A ----------------
def partA():
    words = []
    for L in range(0, 6):
        words += list(itertools.product(range(1, 5), repeat=L))
    words += list(itertools.product(range(1, 4), repeat=6))
    n = viol = eq = 0; nolower = 0; nK2 = 0; gcdbad = 0
    for W in words:
        K, c, cp, s = data(W)
        if math.gcd(s, K) != 1: gcdbad += 1
        if len(W) >= 1: assert s == cont(W[:-1])
        r0 = np.arange(K, dtype=np.int64)[:, None]
        T1 = np.arange(-2 * K, 2 * K + 1, dtype=np.int64)[None, :]
        Ktaumax = np.abs(T1)                      # tightest admissible tau_max = |T1|/K
        Tp1 = T1 + s * r0
        Tmax = np.maximum(Ktaumax, np.abs(Tp1))
        bound = Ktaumax + s * (K - 1)
        n += Tmax.size
        viol += int((Tmax > bound).sum())
        e = int((Tmax == bound).sum()); eq += e
        tight_found = e > 0
        if K >= 2:
            nK2 += 1
            if tight_found: nolower += 1
    print(f'[A] words={len(words)} cases={n} violations={viol} equality_cases={eq}')
    print(f'[A] words with K>=2: {nK2}; of these, bound attained (so cannot be lowered by 1): {nolower}')
    print(f'[A] gcd(sigma,K)!=1 count: {gcdbad}')
    return viol == 0 and nolower == nK2 and gcdbad == 0

# ---------------- Part B ----------------
def v(W, r):
    K, c, cp, s = data(W)
    if not W: return Fr(0)
    return max(Fr(dK(ci * r, K), ci * cpi) for ci, cpi in zip(c, cp))

def edge_min(K, s, r, rp):
    x = (rp - s * r) % K
    return Fr(min(x, K - x), K)

def nu(W):
    K, c, cp, s = data(W)
    V = [v(W, r) for r in range(K)]
    cand = sorted(set(V) | {Fr(j, K) for j in range(0, K + 1)})
    for lam in cand:
        alive = [r for r in range(K) if V[r] <= lam]
        aset = set(alive)
        adj = {r: [rp for rp in alive if edge_min(K, s, r, rp) <= lam] for r in alive}
        # nontrivial edges: any (r,rp) in adj except (0,0) with t=0; (0,0) nontrivial iff lam>=1
        nontriv = [(r, rp) for r in alive for rp in adj[r] if (r, rp) != (0, 0)]
        if 0 in aset and lam >= 1: nontriv.append((0, 0))
        for (u, w) in nontriv:
            # path w -> u in restricted graph
            prev = {w: None}; st = [w]
            while st:
                x = st.pop()
                for y in adj[x]:
                    if y not in prev: prev[y] = x; st.append(y)
            if u in prev:
                path = [u]
                while path[-1] != w: path.append(prev[path[-1]])
                path.reverse()       # w ... u
                cyc = [u] + path     # u -> w -> ... -> u  (vertex sequence, closed)
                # edge t values: nearest coset rep; for (0,0) nontrivial use t=1
                ts = []
                for a, b in zip(cyc[:-1], cyc[1:]):
                    x = (b - s * a) % K
                    t = Fr(x, K) if x <= K - x else Fr(x - K, K)
                    ts.append(t)
                if (u, w) == (0, 0) and ts[0] == 0: ts[0] = Fr(1)
                cost = max([V[r] for r in cyc] + [abs(t) for t in ts])
                assert cost <= lam
                return lam, cyc, ts
    raise RuntimeError

# ---------------- Part C ----------------
def endtoend(W, cyc, ts, nuW, blocks=16, scale=300):
    K, c, cp, s = data(W); l = len(W)
    L = len(ts)
    a = [0]
    for k in range(1, blocks + 1):
        a.append(scale * k); a.extend(W)
    M = len(a) - 1
    p = [a[0]]; q = [1]
    for nn in range(1, M + 1):
        p.append(a[nn] * p[-1] + (p[-2] if nn >= 2 else 1))
        q.append(a[nn] * q[-1] + (q[-2] if nn >= 2 else 0))
    mp.mp.dps = int(2 * math.log10(q[M]) + 60)
    x = mp.mpf(a[M])
    for nn in range(M - 1, -1, -1): x = a[nn] + 1 / x
    eps = [q[nn] * x - p[nn] for nn in range(M + 1)]
    th = [q[nn] * abs(eps[nn]) for nn in range(M + 1)]
    nk = lambda k: (k - 1) * (l + 1)
    # r_k = r^{k mod L}, tau_k = t^m (k = m mod L, m in 1..L), r0 = r^0
    rr = lambda k: cyc[k % L]
    tau = lambda k: ts[((k - 1) % L)]
    T = [int(tau(k) * K) for k in range(1, blocks + 1)]
    r0t = cyc[0] % K
    Tp = list(T); Tp[0] += s * r0t
    beta = sum(Tp[k - 1] * abs(eps[nk(k)]) for k in range(1, blocks + 1)) / K
    y = [q[nn] * beta - mp.nint(q[nn] * beta) for nn in range(M + 1)]
    R = [abs(y[nn]) / th[nn] if th[nn] != 0 else None for nn in range(M + 1)]
    rows = []
    for k in range(2, blocks - 3):
        Mk = max(R[nk(k) + i] for i in range(l + 1))
        # per-vertex deviations
        dev = abs(R[nk(k)] - abs(tau(k)))
        for i in range(1, l + 1):
            dev = max(dev, abs(R[nk(k) + i] - mp.mpf(dK(c[i - 1] * rr(k), K)) / (c[i - 1] * cp[i - 1])))
        lab = int(mp.nint(K * y[nk(k) + 1])) % K if l else 0
        rows.append((k, mp.nstr(Mk, 10), mp.nstr(dev, 3), lab == rr(k) % K))
    return rows

def main():
    okA = partA()
    print()
    Ws = [(), (1,), (1, 1), (2,), (5, 1, 5), (1, 9, 9), (2, 1, 1, 2), (3, 1, 4), (1, 1, 1, 1, 1), (4, 4, 4)]
    for W in Ws:
        lam, cyc, ts = nu(W)
        print(f'[B] W={W} K={data(W)[0]} sigma={data(W)[3]} nu={lam} witness vertices={cyc} t={[str(t) for t in ts]}')
        rows = endtoend(W, cyc, ts, lam)
        last = rows[-len(cyc) - 1:]
        print(f'[C]   late blocks (k, max_block R_n, max per-vertex deviation, label correct):')
        for r in last: print('        ', r)
        mx = max(float(r[1]) for r in last)
        print(f'[C]   max over last full period = {mx:.10f}  vs nu = {float(lam):.10f}  diff = {mx - float(lam):.3e}')
    print()
    print('PART A', 'PASSED' if okA else 'FAILED')

if __name__ == '__main__':
    main()
