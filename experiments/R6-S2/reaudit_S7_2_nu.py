#!/usr/bin/env python3
"""R6 side-track Step 4 re-audit: Corollary 2 of proofs/R6-S7-mstar.md,
nu(W) = min(1, m*) for K>=2 and nu = 1 for K=1, under BOTH readings of
"directed closed path" in PLAN_GRAPH S.1 (closed walk / simple cycle).

Independent implementation (isolated skeptic); does not import project helpers.
Graph G_W (S.1): vertices Z/K; vertex cost v(r)=max_i d_K(c_i r)/(c_i c'_i)
(v == 0 if l=0); edge r->r' carries real t with t == (r'-sigma r)/K mod 1,
cost |t|; the trivial loop is t=0 at vertex 0; nu = min over closed paths not
consisting only of trivial loops of max(vertex costs, edge costs).

Three independent evaluators of nu:
  M1 closed walks: minimax Floyd-Warshall (exact Fractions), K <= K_FLOYD.
  M2 closed walks: threshold bisection + "peel sources/sinks" cycle test.
  M3 simple cycles: exhaustive DFS over all simple cycles (incl. loops), K <= K_SIMPLE.
For the minimax only the minimal |t| per (r,r') matters, except at 0->0 where the
minimal NON-trivial |t| is 1; in M3 we additionally enumerate t in {tmin, tmin+-1}
restricted to |t|<=1 to make sure nothing is lost by taking the minimal |t|.
"""
from fractions import Fraction
import random
import itertools
import sys

random.seed(1127)


def K_right(w):
    a, b = 0, 1
    for x in w:
        a, b = b, x * b + a
    return b


def dK(x, K):
    x %= K
    return min(x, K - x)


def graph(w):
    l = len(w)
    K = K_right(w)
    c = [None] + [K_right(w[:i - 1]) for i in range(1, l + 1)]
    cp = [None] + [K_right(w[i:]) for i in range(1, l + 1)]
    sigma = c[l] if l >= 1 else 1
    if l == 0:
        v = [Fraction(0)] * K
    else:
        v = [max(Fraction(dK(c[i] * r, K), c[i] * cp[i]) for i in range(1, l + 1))
             for r in range(K)]
    return K, sigma, v


def tmin(r, r2, K, sigma):
    """minimal |t| over t == (r2 - sigma r)/K mod 1"""
    return Fraction(dK(r2 - sigma * r, K), K)


def nu_floyd(K, sigma, v):
    INF = Fraction(10**9)
    B = [[None] * K for _ in range(K)]
    for i in range(K):
        for j in range(K):
            e = tmin(i, j, K, sigma)
            if i == 0 and j == 0:
                e = Fraction(1)  # only non-trivial loop at 0
            B[i][j] = max(v[i], v[j], e)
    for k in range(K):
        Bk = B[k]
        for i in range(K):
            bik = B[i][k]
            Bi = B[i]
            for j in range(K):
                cand = bik if bik >= Bk[j] else Bk[j]
                if cand < Bi[j]:
                    Bi[j] = cand
    return min(B[i][i] for i in range(K))


def has_nontrivial_cycle(K, sigma, v, lam):
    V = [r for r in range(K) if v[r] <= lam]
    Vs = set(V)
    out = {r: set() for r in V}
    inn = {r: set() for r in V}
    for i in V:
        for j in V:
            if i == 0 and j == 0:
                ok = lam >= 1
            else:
                ok = tmin(i, j, K, sigma) <= lam
            if ok:
                out[i].add(j)
                inn[j].add(i)
    alive = set(V)
    changed = True
    while changed:
        changed = False
        for r in list(alive):
            if not (out[r] & alive) or not (inn[r] & alive):
                alive.discard(r)
                changed = True
    return bool(alive)


def nu_threshold(K, sigma, v):
    cands = set(v)
    for i in range(K):
        for j in range(K):
            cands.add(tmin(i, j, K, sigma))
    cands.add(Fraction(1))
    cands = sorted(cands)
    lo, hi = 0, len(cands) - 1
    assert has_nontrivial_cycle(K, sigma, v, cands[hi])
    while lo < hi:
        mid = (lo + hi) // 2
        if has_nontrivial_cycle(K, sigma, v, cands[mid]):
            hi = mid
        else:
            lo = mid + 1
    return cands[lo]


def edge_ts(i, j, K, sigma):
    """all t with |t|<=1 in the class (j - sigma i)/K + Z"""
    base = Fraction((j - sigma * i) % K, K)  # in [0,1)
    return [t for t in (base - 1, base, base + 1) if abs(t) <= 1]


def nu_simple_cycles(K, sigma, v):
    best = None
    # self-loops
    for r in range(K):
        for t in edge_ts(r, r, K, sigma):
            if r == 0 and t == 0:
                continue
            cost = max(v[r], abs(t))
            best = cost if best is None or cost < best else best
    # simple cycles of length >= 2: fix smallest vertex as start
    for L in range(2, K + 1):
        for start in range(K):
            for rest in itertools.permutations([x for x in range(start + 1, K)], L - 1):
                cyc = (start,) + rest
                cost = max(v[x] for x in cyc)
                for a in range(L):
                    i, j = cyc[a], cyc[(a + 1) % L]
                    cost = max(cost, min(abs(t) for t in edge_ts(i, j, K, sigma)))
                if best is None or cost < best:
                    best = cost
    return best


def words_with_K_le(KMAX):
    out = [()]
    stack = [()]
    while stack:
        w = stack.pop()
        for x in range(1, KMAX + 1):
            nw = w + (x,)
            if K_right(nw) > KMAX:
                break
            out.append(nw)
            stack.append(nw)
    return out


def predicted(K, v):
    if K == 1:
        return Fraction(1)
    mstar = min(v[1:])
    return min(Fraction(1), mstar)


K_FLOYD = int(sys.argv[1]) if len(sys.argv) > 1 else 30
K_SIMPLE = int(sys.argv[2]) if len(sys.argv) > 2 else 8
fails = 0
n_f = n_t = n_s = 0
below1 = 0
allw = words_with_K_le(K_FLOYD)
print(f"words with K <= {K_FLOYD}: {len(allw)}")
for w in allw:
    K, sigma, v = graph(w)
    p = predicted(K, v)
    if p < Fraction(1, 2):
        print("PREDICTED < 1/2 !", w, p)
        fails += 1
    a = nu_floyd(K, sigma, v); n_f += 1
    b = nu_threshold(K, sigma, v); n_t += 1
    if not (a == b == p):
        print("MISMATCH (walk)", w, "floyd", a, "thr", b, "pred", p)
        fails += 1
    if K <= K_SIMPLE:
        s = nu_simple_cycles(K, sigma, v); n_s += 1
        if s != p:
            print("MISMATCH (simple)", w, "simple", s, "pred", p)
            fails += 1
    if p < 1:
        below1 += 1
print(f"Floyd checks {n_f}, threshold checks {n_t}, simple-cycle checks {n_s}; nu<1 in {below1}")

# random larger words, threshold method only
print("== random words with 30 < K <= 160 (threshold method)")
pool = [w for w in words_with_K_le(160) if K_right(w) > K_FLOYD]
sample = random.sample(pool, 250)
# plus deliberate ones
sample += [(5, 1, 5), (5, 1, 1, 1, 5), (6, 1, 1, 1, 5), (3, 1, 3), (1,) * 9, (1,) * 10,
           (2, 1, 1, 2), (100,), (1, 100), (100, 1), (7, 1, 1, 7), (4, 1, 4)]
nsm = 0
minnu = None
for w in sample:
    K, sigma, v = graph(w)
    p = predicted(K, v)
    b = nu_threshold(K, sigma, v)
    nsm += 1
    if b != p:
        print("MISMATCH (thr, random)", w, b, p)
        fails += 1
    minnu = b if minnu is None or b < minnu else minnu
    if w in [(5, 1, 5), (5, 1, 1, 1, 5), (3, 1, 3), (1,) * 9]:
        print(f"  W={w}: K={K}, nu={b}, min(1,m*)={p}")
print("random/deliberate checks:", nsm, " min nu seen:", minnu)
# K=1 words explicitly
for w in [(), (1,)]:
    K, sigma, v = graph(w)
    print(f"  W={w}: K={K}, sigma={sigma}, floyd={nu_floyd(K, sigma, v)}, "
          f"thr={nu_threshold(K, sigma, v)}, simple={nu_simple_cycles(K, sigma, v)}")
print("FAILURES:", fails)
