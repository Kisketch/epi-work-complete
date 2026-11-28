"""Audit §6 Lemma C (C0-C3; interpretive convention I2): nu over closed walks == nu over simple cycles.

Self-contained (no local imports). Exact Fractions.
  nu_walk  : bottleneck closure over closed walks (Floyd-Warshall in (min,max) semiring), all edges with |t|<=1
             included explicitly (multigraph: every t in coset, |t|<=1), trivial loop excluded.
  nu_simple: brute force over all simple directed cycles (vertex sequences without repetition), each edge
             chosen among the parallel edges; loops = cycles of length 1.
Also checks (C1): any closed walk with an edge |t|>1 costs >1 >= nu, and edge-cost set is finite.
Words: all W with K(W) <= 9 among l<=6, letters 1..9 (simple-cycle enumeration is K! scale).
"""
import itertools
from fractions import Fraction


def cont(ws):
    a, b = 0, 1
    for w in ws:
        a, b = b, w * b + a
    return b


def data(W):
    l = len(W)
    K = cont(W)
    c = [cont(W[:i - 1]) for i in range(1, l + 1)]
    cp = [cont(W[i:]) for i in range(1, l + 1)]
    sigma = c[-1] if l >= 1 else 1
    return K, c, cp, sigma


def v(W, r):
    K, c, cp, _ = data(W)
    if not c:
        return Fraction(0)
    return max(Fraction(min((ci * r) % K, K - (ci * r) % K), ci * cpi) for ci, cpi in zip(c, cp))


def edges(K, sigma, a, b):
    """all t with t == (b - sigma a)/K mod 1 and |t| <= 1, excluding the trivial loop."""
    base = Fraction((b - sigma * a) % K, K)
    out = []
    for z in (-2, -1, 0, 1):
        t = base + z
        if abs(t) <= 1 and not (a == 0 and b == 0 and t == 0):
            out.append(t)
    return out


def nu_walk(W):
    K, c, cp, sigma = data(W)
    V = [v(W, r) for r in range(K)]
    INF = Fraction(10 ** 6)
    best_edge = [[min((max(V[a], V[b], abs(t)) for t in edges(K, sigma, a, b)), default=INF) for b in range(K)] for a in range(K)]
    # closure including the trivial loop as a free (cost v(0)=0) edge for connectivity
    B = [[best_edge[a][b] for b in range(K)] for a in range(K)]
    B[0][0] = min(B[0][0], V[0])  # trivial loop usable inside a walk
    for m in range(K):
        for a in range(K):
            for b in range(K):
                cand = max(B[a][m], B[m][b])
                if cand < B[a][b]:
                    B[a][b] = cand
    best = INF
    for a in range(K):
        for b in range(K):
            e = best_edge[a][b]  # a non-trivial edge a->b
            if e == INF:
                continue
            back = V[a] if a == b else B[b][a]
            best = min(best, max(e, back))
    return best


def nu_simple(W):
    K, c, cp, sigma = data(W)
    V = [v(W, r) for r in range(K)]
    best = None
    for L in range(1, K + 1):
        for seq in itertools.permutations(range(K), L):
            if seq[0] != min(seq):
                continue
            cost = max(V[x] for x in seq)
            ok = True
            for a, b in zip(seq, seq[1:] + seq[:1]):
                es = edges(K, sigma, a, b)
                if not es:
                    ok = False
                    break
                cost = max(cost, min(abs(t) for t in es))
            if ok and (best is None or cost < best):
                best = cost
    return best


words = set()
for l in range(0, 7):
    for W in itertools.product(range(1, 10), repeat=l):
        if cont(W) <= 9:
            words.add(W)
words = sorted(words, key=lambda w: (cont(w), len(w), w))
mism = []
c0 = []
for W in words:
    a, b = nu_walk(W), nu_simple(W)
    if a != b:
        mism.append((W, a, b))
    K, c, cp, sigma = data(W)
    if v(W, 0) != 0:
        c0.append(W)
print("=== audit_S2_6: Lemma C3 (closed walks vs simple cycles), C0 ===")
print(f"words tested: {len(words)} (all W with K(W)<=9, l<=6, letters 1..9)")
print(f"C0 failures (v(0)!=0): {len(c0)}")
print(f"nu_walk != nu_simple: {len(mism)}")
for m in mism[:20]:
    print("  ", m)
from collections import Counter
print("distribution of nu over tested words:", dict(Counter(str(nu_walk(W)) for W in words)))
print("category 4: finite exact computation, not a proof.")


# ---- Part 2: words with nu < 1 (where C3 is non-vacuous). For every W with l<=5, letters 1..5, K<=60:
# compute nu_walk exactly; if nu_walk < 1, search (DFS) for a SIMPLE cycle, using only vertices/edges of
# cost <= nu_walk and at least one non-trivial edge, whose cost is <= nu_walk.  (nu_simple >= nu_walk is trivial.)
def simple_cycle_at_most(W, lam):
    K, c, cp, sigma = data(W)
    V = [v(W, r) for r in range(K)]
    ok = [V[r] <= lam for r in range(K)]
    adj = {a: [] for a in range(K) if ok[a]}
    for a in adj:
        for b in adj:
            es = [t for t in edges(K, sigma, a, b) if abs(t) <= lam]
            if es:
                adj[a].append((b, min(es, key=abs)))
    # loops
    for a in adj:
        for (b, t) in adj[a]:
            if b == a:
                return [(a, a, t)]
    # longer simple cycles: DFS from each start s over vertices > s
    for s in sorted(adj):
        stack = [(s, [s], [])]
        while stack:
            u, path, es = stack.pop()
            for (b, t) in adj[u]:
                if b == s and len(path) >= 2:
                    return list(zip(path, path[1:] + [s], es + [t]))
                if b > s and b not in path:
                    stack.append((b, path + [b], es + [t]))
    return None


cnt = 0; sub1 = 0; fail = []
for l in range(0, 6):
    for W in itertools.product(range(1, 6), repeat=l):
        if cont(W) > 60:
            continue
        cnt += 1
        nw = nu_walk(W)
        if nw < 1:
            sub1 += 1
            cyc = simple_cycle_at_most(W, nw)
            if cyc is None:
                fail.append((W, nw))
            else:
                # exact cost check of the returned simple cycle
                cost = max(max(v(W, a), v(W, b), abs(t)) for (a, b, t) in cyc)
                vs = [a for (a, b, t) in cyc]
                assert len(set(vs)) == len(vs) and cost <= nw
print(f"Part 2: words (l<=5, letters 1..5, K<=60): {cnt}; with nu_walk<1: {sub1}; "
      f"no simple cycle of cost<=nu_walk: {len(fail)}")
for f in fail[:10]:
    print("  FAIL", f)

# ---- Part 3 (optional, needs experiments/R6-S2/common.py from Step 2): cross-check nu_walk vs common.nu
try:
    import os, sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from common import nu as nu_common
    mm = 0; n3 = 0
    for l in range(0, 6):
        for W in itertools.product(range(1, 6), repeat=l):
            if cont(W) > 60:
                continue
            n3 += 1
            if nu_walk(W) != nu_common(W)[0]:
                mm += 1
                print("  MISMATCH vs common.nu", W)
    print(f"Part 3: nu_walk (this file) vs common.nu (Step-2 script): {n3} words, mismatches = {mm}")
except ImportError:
    print("Part 3 skipped (common.py not found)")
