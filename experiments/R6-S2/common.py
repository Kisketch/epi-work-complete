"""R6-S2 shared helpers: continuants, local graph G_W, exact nu(W) and nu_0(W).

Definitions follow PLAN_GRAPH.md S.1 verbatim:
  K() = 1, K(w1) = w1, K(w1..wm) = wm K(w1..w_{m-1}) + K(w1..w_{m-2}); length -1 -> 0.
  K := K(W); c_i := K(w1..w_{i-1}); c_i' := K(w_{i+1}..w_l); sigma := c_l (l>=1), sigma := 1 (l=0).
  d_K(x) := min_s |x - sK|.
  v(r) := max_i d_K(c_i r)/(c_i c_i')  (v == 0 when l = 0).
  edge r -> r' with real t, t == (r' - sigma r)/K mod 1, cost |t|;
  trivial loop := loop at 0 with t = 0.
  nu(W) := min over closed walks not consisting only of trivial loops of max(vertex/edge costs).
All comparisons that decide nu are exact (integer cross-multiplication / Fraction).
"""
from fractions import Fraction
import numpy as np


def cont(ws):
    """Continuant K(ws) (exact int)."""
    a, b = 0, 1  # K of length -1, K of length 0
    for w in ws:
        a, b = b, w * b + a
    return b


def block_data(W):
    l = len(W)
    K = cont(W)
    c = [cont(W[: i - 1]) for i in range(1, l + 1)]      # c_i, i=1..l
    cp = [cont(W[i:]) for i in range(1, l + 1)]          # c_i'
    sigma = c[-1] if l >= 1 else 1
    return K, c, cp, sigma


def dK(x, K):
    x = x % K
    return np.minimum(x, K - x)


def vertex_costs(W):
    """Return K, sigma, num[r], den[r] with v(r) = num/den exactly (vectorised, int64)."""
    K, c, cp, sigma = block_data(W)
    r = np.arange(K, dtype=np.int64)
    num = np.zeros(K, dtype=np.int64)
    den = np.ones(K, dtype=np.int64)
    for ci, cpi in zip(c, cp):
        d = dK(ci * r, K)
        dd = np.int64(ci * cpi)
        better = d * den > num * dd          # d/dd > num/den  (exact)
        num = np.where(better, d, num)
        den = np.where(better, dd, den)
    return K, sigma, num, den


def v_exact(W, r):
    K, c, cp, sigma = block_data(W)
    if not c:
        return Fraction(0)
    return max(Fraction(min((ci * r) % K, K - (ci * r) % K), ci * cpi) for ci, cpi in zip(c, cp))


def edge_cost_exact(K, sigma, r, rp):
    x = (rp - sigma * r) % K
    return Fraction(min(x, K - x), K)


def nu0(W):
    """nu_0(W) = min_{r != 0} max_{j>=0} v(sigma^j r) (zero-jump closed walks). Exact."""
    K, sigma, num, den = vertex_costs(W)
    if K == 1:
        return None, None, None
    seen = np.zeros(K, dtype=bool)
    seen[0] = True
    best, best_orbit = None, None
    maxlen = 0
    for r0 in range(1, K):
        if seen[r0]:
            continue
        orb = []
        r = r0
        while not seen[r]:
            seen[r] = True
            orb.append(r)
            r = (sigma * r) % K
        maxlen = max(maxlen, len(orb))
        m = max(Fraction(int(num[x]), int(den[x])) for x in orb)
        if best is None or m < best:
            best, best_orbit = m, orb
    return best, best_orbit, maxlen


def _alive_after_peel(K, sigma, alive, L):
    """Peel vertices with zero in- or out-degree in H (window graph), trivial loop removed.
    Edge r->r' (both alive) iff d_K(r' - sigma r) <= L.  Returns final alive mask."""
    alive = alive.copy()
    r = np.arange(K, dtype=np.int64)
    sr = (sigma * r) % K
    inv = np.empty(K, dtype=np.int64)
    inv[sr] = r                      # sigma^{-1}
    offs = np.arange(-L, L + 1, dtype=np.int64)
    while True:
        a = alive.astype(np.int64)
        ext = np.concatenate([a, a, a])
        cs = np.concatenate([[0], np.cumsum(ext)])

        def wsum(center):  # sum of arr over [center-L, center+L] mod K, using ext = arr repeated 3x
            if 2 * L + 1 >= K:
                return np.full(center.shape, int(a.sum()), dtype=np.int64)
            lo = center - L + K
            hi = center + L + K + 1
            return cs[hi] - cs[lo]
        outdeg = wsum(sr)
        # in-degree of r': #alive r with sigma r in r' +- L  -> sum of B over window, B[s] = alive[inv[s]]
        B = a[inv]
        extB = np.concatenate([B, B, B])
        csB = np.concatenate([[0], np.cumsum(extB)])
        if 2 * L + 1 >= K:
            indeg = np.full(K, int(B.sum()), dtype=np.int64)
        else:
            indeg = csB[r + L + K + 1] - csB[r - L + K]
        # remove trivial loop at 0 (0 -> 0 with t = 0 is always inside the window)
        if alive[0]:
            outdeg[0] -= 1
            indeg[0] -= 1
        kill = alive & ((outdeg <= 0) | (indeg <= 0))
        if not kill.any():
            return alive
        alive[kill] = False


def has_cycle(K, sigma, num, den, P, Q):
    """Predicate: H_lambda (lambda = P/Q < 1) contains a nontrivial closed walk."""
    alive = (num * Q <= P * den)                 # v(r) <= P/Q, exact
    L = (P * K) // Q                             # edge d <= lambda K
    L = min(L, K // 2)
    fin = _alive_after_peel(K, sigma, alive, int(L))
    return fin.any(), fin


def find_cycle(K, sigma, fin, L):
    """Follow out-edges inside surviving set to extract an explicit closed walk."""
    alive_set = set(np.nonzero(fin)[0].tolist())
    start = next(x for x in sorted(alive_set) if x != 0) if any(x != 0 for x in alive_set) else 0
    path, pos = [], {}
    r = start
    while r not in pos:
        pos[r] = len(path)
        path.append(r)
        nxt = None
        for d in range(0, L + 1):
            for s in ((d,) if d == 0 else (d, -d)):
                rp = (sigma * r + s) % K
                if rp in alive_set and not (r == 0 and rp == 0 and s == 0):
                    nxt = rp
                    break
            if nxt is not None:
                break
        assert nxt is not None
        r = nxt
    return path[pos[r]:] + [r]


def nu(W):
    """Exact nu(W) with witness closed walk [r0, r1, ..., r0] (edges use minimal |t|).
    Returns (nu: Fraction, witness: list or 'loop0_t=+-1', mstar: Fraction or None)."""
    K, sigma, num, den = vertex_costs(W)
    if K == 1:
        return Fraction(1), "loop0_t=+-1", None
    # m* = min_{r != 0} v(r)
    vals = num[1:] / den[1:]
    i = int(np.argmin(vals)) + 1
    # exact min over ties
    cand = np.nonzero(np.isclose(vals, vals[i - 1], rtol=0, atol=1e-12))[0] + 1
    mstar = min(Fraction(int(num[j]), int(den[j])) for j in cand)
    if mstar >= 1:
        return Fraction(1), "loop0_t=+-1", mstar
    if mstar >= Fraction(1, 2):
        r = min(int(j) for j in cand if Fraction(int(num[j]), int(den[j])) == mstar)
        w = [r, r]
        cost = max(v_exact(W, r), edge_cost_exact(K, sigma, r, r))
        assert cost == mstar
        return mstar, w, mstar
    # binary search over candidate thresholds in [mstar, 1/2]
    cands = set()
    for j in range(1, K):
        f = Fraction(int(num[j]), int(den[j]))
        if mstar <= f <= Fraction(1, 2):
            cands.add(f)
    for d in range(0, K // 2 + 1):
        f = Fraction(d, K)
        if mstar <= f <= Fraction(1, 2):
            cands.add(f)
    cands = sorted(cands)
    lo, hi = 0, len(cands) - 1
    ok, _ = has_cycle(K, sigma, num, den, cands[hi].numerator, cands[hi].denominator)
    assert ok
    while lo < hi:
        mid = (lo + hi) // 2
        ok, _ = has_cycle(K, sigma, num, den, cands[mid].numerator, cands[mid].denominator)
        if ok:
            hi = mid
        else:
            lo = mid + 1
    lam = cands[lo]
    ok, fin = has_cycle(K, sigma, num, den, lam.numerator, lam.denominator)
    assert ok
    L = min((lam.numerator * K) // lam.denominator, K // 2)
    walk = find_cycle(K, sigma, fin, int(L))
    cost = walk_cost(W, walk)
    assert cost <= lam, (W, walk, cost, lam)
    return cost, walk, mstar


def walk_cost(W, walk):
    K, c, cp, sigma = block_data(W)
    cost = Fraction(0)
    for a, b in zip(walk[:-1], walk[1:]):
        cost = max(cost, v_exact(W, a), v_exact(W, b), edge_cost_exact(K, sigma, a, b))
        if a == 0 and b == 0 and edge_cost_exact(K, sigma, a, b) == 0:
            raise ValueError("trivial loop used in witness")
    return cost


def nu_bruteforce(W):
    """Independent O(K^3) bottleneck-closure computation, Fractions only (small K)."""
    K, c, cp, sigma = block_data(W)
    if K == 1:
        return Fraction(1)
    v = [v_exact(W, r) for r in range(K)]
    INF = Fraction(10 ** 9)
    # B[u][x] = min over walks u -> x (>=1 edge, minimal-|t| edges, trivial loop allowed) of max cost
    B = [[max(v[u], v[x], edge_cost_exact(K, sigma, u, x)) for x in range(K)] for u in range(K)]
    for m in range(K):
        Bm = B[m]
        for u in range(K):
            bum = B[u][m]
            Bu = B[u]
            for x in range(K):
                cnd = bum if bum > Bm[x] else Bm[x]
                if cnd < Bu[x]:
                    Bu[x] = cnd
    best = Fraction(1)  # loop at 0 with t = +-1
    for u in range(K):
        for x in range(K):
            if u == 0 and x == 0:
                continue  # minimal edge 0->0 is the trivial loop; non-trivial 0->0 edges cost 1
            e = edge_cost_exact(K, sigma, u, x)
            back = Fraction(0) if (x == u) else B[x][u]
            best = min(best, max(e, v[u], v[x], back))
    return best
