"""v2audit_S2_2: independent computation of nu(W) under three readings of '有向闭路'
(closed walk / closed trail(=walk here, see note) / simple cycle), checks (C0)-(C3),
calibrations nu(())=nu((1))=nu((1,1))=1, the 'not done' remark nu(5,1,5)=5/6,
1/4<=nu<=1, gcd(sigma,K)=1, (A2a)/(A2b) identities. Exact rational arithmetic only."""
from fractions import Fraction as F
from itertools import product
from math import gcd
import sys, functools
print = functools.partial(print, flush=True)

def Kc(w):
    a, b = 0, 1  # K(len -1)=0, K()=1
    for x in w:
        a, b = b, x * b + a
    return b

def data(W):
    l = len(W); K = Kc(W)
    c = [Kc(W[:i - 1]) for i in range(1, l + 1)]
    cp = [Kc(W[i:]) for i in range(1, l + 1)]
    sigma = Kc(W[:l - 1]) if l >= 1 else 1
    return l, K, c, cp, sigma

def dK(x, K):
    r = x % K
    return min(r, K - r)

def vcost(W):
    l, K, c, cp, s = data(W)
    return [max([F(dK(c[i] * r, K), c[i] * cp[i]) for i in range(l)], default=F(0)) for r in range(K)]

def edges(W):
    """all edges with |t|<=1: (r, r2, t)"""
    l, K, c, cp, s = data(W)
    E = []
    for r in range(K):
        for r2 in range(K):
            base = (r2 - s * r) % K  # t = (base + K m)/K
            for m in range(-2, 3):
                t = F(base + K * m, K)
                if abs(t) <= 1:
                    E.append((r, r2, t))
    return E

def trivial(e):
    return e[0] == 0 and e[1] == 0 and e[2] == 0

def nu_walk(W):
    """min over closed walks containing >=1 nontrivial edge; threshold method:
    for lambda, closed walk with cost<=lambda through nontrivial edge (a,b,t) exists iff
    v(a),v(b),|t|<=lambda and b reaches a in subgraph G_lambda."""
    v = vcost(W); E = edges(W); K = len(v)
    cands = sorted(set(v) | {abs(e[2]) for e in E})
    for lam in cands:
        Ev = [e for e in E if abs(e[2]) <= lam and v[e[0]] <= lam and v[e[1]] <= lam]
        adj = {r: set() for r in range(K)}
        for e in Ev:
            adj[e[0]].add(e[1])
        def reach(x):
            seen = {x}; st = [x]
            while st:
                y = st.pop()
                for z in adj[y]:
                    if z not in seen:
                        seen.add(z); st.append(z)
            return seen
        R = {r: reach(r) for r in range(K)}
        for e in Ev:
            if not trivial(e) and e[0] in R[e[1]]:
                return lam
    return None

def nu_simple(W):
    """brute force over simple cycles (distinct vertices), multigraph edges labelled by t"""
    v = vcost(W); E = edges(W); K = len(v)
    best_edge = {}  # (a,b) -> list of t sorted by |t|
    for e in E:
        best_edge.setdefault((e[0], e[1]), []).append(e[2])
    best = None
    def cyc_cost(seq):
        cost = max(v[x] for x in seq)
        L = len(seq)
        for i in range(L):
            a, b = seq[i], seq[(i + 1) % L]
            ts = best_edge[(a, b)]
            if L == 1 and a == 0:
                ts = [t for t in ts if t != 0]
            cost = max(cost, min(abs(t) for t in ts))
        return cost
    # enumerate simple cycles with smallest vertex first
    def dfs(start, path, used):
        nonlocal best
        c = cyc_cost(path)
        if best is None or c < best:
            best = c
        for x in range(start + 1, K):
            if x not in used:
                used.add(x); path.append(x)
                dfs(start, path, used)
                path.pop(); used.discard(x)
    for s0 in range(K):
        dfs(s0, [s0], {s0})
    return best

def nu_walk_bruteforce(W, maxlen):
    """direct enumeration of closed walks up to length maxlen (tiny K only)."""
    v = vcost(W); E = edges(W); K = len(v)
    out = {r: [e for e in E if e[0] == r] for r in range(K)}
    best = None
    def rec(start, cur, cost, nontriv, L):
        nonlocal best
        if L > 0 and cur == start and nontriv:
            if best is None or cost < best: best = cost
        if L == maxlen: return
        for e in out[cur]:
            c2 = max(cost, abs(e[2]), v[e[1]])
            if best is not None and c2 >= best: continue
            rec(start, e[1], c2, nontriv or not trivial(e), L + 1)
    for r in range(K):
        rec(r, r, v[r], False, 0)
    return best

fails = 0
def check(cond, msg):
    global fails
    if not cond:
        fails += 1; print("FAIL:", msg)

# calibration and the remark
for W in [(), (1,), (1, 1), (5, 1, 5)]:
    l, K, c, cp, s = data(W)
    print(f"W={W}: K={K} sigma={s} nu_walk={nu_walk(W)} nu_simple={nu_simple(W) if K<=8 else 'skip'}")
check(nu_walk(()) == 1 and nu_walk((1,)) == 1 and nu_walk((1, 1)) == 1, "calibration")
check(nu_walk((5, 1, 5)) == F(5, 6), "remark nu(5,1,5)=5/6")

# exhaustive over words
count = 0; minnu = None; argmin = None; hist = {}
for l in range(0, 6):
    for W in product(range(1, 7), repeat=l):
        l_, K, c, cp, s = data(W)
        if K > 40: continue  # cap: G_W has ~2K^2 edges
        # identities
        if l >= 1:
            check(gcd(s, K) == 1, f"gcd {W}")
            for i in range(1, l + 1):
                Kil = Kc(W[i - 1:]); Ki2 = Kc(W[:i - 2]) if i >= 2 else 0
                check(K == c[i - 1] * Kil + Ki2 * cp[i - 1], f"A2a {W} i={i}")
                Kip1 = Kc(W[i:]); Kip2 = Kc(W[i + 1:]) if i + 1 <= l else (1 if i == l - 1 else 0)
                if i == l: Kip2 = 0
                elif i == l - 1: Kip2 = 1
                check(Kil == W[i - 1] * Kip1 + Kip2, f"A2b {W} i={i}")
        v = vcost(W)
        check(v[0] == 0, f"C0 {W}")
        nw = nu_walk(W)
        check(F(1, 4) <= nw <= 1, f"1/4<=nu<=1 fails {W}: {nw}")
        if K <= 8:
            ns = nu_simple(W)
            check(ns == nw, f"C3 walk vs simple {W}: {nw} vs {ns}")
            if K <= 4:
                nb = nu_walk_bruteforce(W, K + 2)
                check(nb == nw, f"walk bruteforce {W}: {nb} vs {nw}")
        count += 1
        hist[nw] = hist.get(nw, 0) + 1
        if minnu is None or nw < minnu:
            minnu, argmin = nw, W
print("(cap: words with K<=40; simple-cycle brute force K<=8; direct walk enumeration K<=4)")
print("words checked:", count, " min nu:", minnu, "at", argmin)
print("nu histogram (value:count), smallest 8:", sorted(hist.items())[:8])
print("FAILS:", fails)
