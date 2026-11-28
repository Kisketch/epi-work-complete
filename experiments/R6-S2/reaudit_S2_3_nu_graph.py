"""reaudit_S2_3: lemma C (C0-C3) and the bounds 1/4 <= nu(W) <= 1, independent implementation (Fractions only).

Three independent evaluations of nu(W) from the S.1 definition:
  (W)  brute force over ALL closed walks of length <= Lmax using every edge with |t| <= 1
       (multi-edges included; trivial loop allowed inside a walk, walk must contain a non-trivial edge);
  (S)  brute force over all SIMPLE cycles (distinct vertices; every parallel edge choice);
  (T)  threshold method: smallest candidate lambda such that the graph of vertices v<=lambda and
       non-trivial edges |t|<=lambda contains a directed cycle (via iterative source/sink peeling).
(W)=(S) is lemma C3 (I2); (T) is used for larger K.  Calibration nu(empty)=nu((1))=nu((1,1))=1.
Also checks C1 claim: for |t|<=1 there are finitely many edges and t in (1/K)Z.
"""
import itertools
from fractions import Fraction as F

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

def edges(W):
    """all edges (r, r2, t) with |t| <= 1, t = (r2 - sigma r)/K mod 1."""
    K, c, cp, s = data(W)
    E = []
    for r in range(K):
        for r2 in range(K):
            base = F((r2 - s * r) % K, K)  # in [0,1)
            for m in range(-2, 2):
                t = base + m
                if abs(t) <= 1:
                    E.append((r, r2, t))
    return E

def trivial(e):
    return e[0] == 0 and e[1] == 0 and e[2] == 0

def nu_walks(W, Lmax):
    v = vcost(W); E = edges(W)
    out = {}
    for e in E: out.setdefault(e[0], []).append(e)
    best = None
    def dfs(start, cur, path_cost, length, nontriv):
        nonlocal best
        for e in out.get(cur, []):
            c2 = max(path_cost, abs(e[2]), v[e[1]])
            nt = nontriv or not trivial(e)
            if best is not None and c2 >= best:
                continue
            if e[1] == start and nt:
                best = c2 if best is None else min(best, c2)
            if length + 1 < Lmax:
                dfs(start, e[1], c2, length + 1, nt)
    for r in range(len(v)):
        dfs(r, r, v[r], 0, False)
    return best

def nu_simple(W):
    v = vcost(W); E = edges(W); K = len(v)
    best = None
    emap = {}
    for e in E:
        if not trivial(e):
            emap.setdefault((e[0], e[1]), []).append(abs(e[2]))
    for L in range(1, K + 1):
        for verts in itertools.permutations(range(K), L):
            if verts[0] != min(verts):
                continue
            cost = max(v[x] for x in verts)
            ok = True
            for a, b in zip(verts, verts[1:] + verts[:1]):
                if (a, b) not in emap: ok = False; break
                cost = max(cost, min(emap[(a, b)]))
            if ok:
                best = cost if best is None else min(best, cost)
    return best

def has_cycle(nodes, adj):
    nodes = set(nodes)
    changed = True
    while changed:
        changed = False
        for x in list(nodes):
            outs = [y for y in adj.get(x, ()) if y in nodes]
            ins = [y for y in nodes if x in adj.get(y, ())]
            if not outs or not ins:
                nodes.discard(x); changed = True
    return bool(nodes)

def nu_threshold(W):
    v = vcost(W); E = [e for e in edges(W) if not trivial(e)]
    cands = sorted(set([x for x in v if x <= 1] + [abs(e[2]) for e in E]))
    for lam in cands:
        nodes = [r for r in range(len(v)) if v[r] <= lam]
        adj = {}
        for (a, b, t) in E:
            if abs(t) <= lam and v[a] <= lam and v[b] <= lam:
                adj.setdefault(a, set()).add(b)
        if has_cycle(nodes, adj):
            return lam
    return None

report = []
# calibration
for W in [(), (1,), (1, 1)]:
    print("calibration", W, "K=", Kc(W), "nu_walk=", nu_walks(W, 4), "nu_simple=", nu_simple(W), "nu_thr=", nu_threshold(W))

# C1: edge count and t in (1/K)Z
mismatch = 0; tested = 0; minnu = F(10); maxnu = F(0); argmin = None
for l in range(0, 5):
    for W in itertools.product(range(1, 5), repeat=l):
        K = Kc(W)
        if K > 7:
            continue
        E = edges(W)
        assert all((e[2] * K).denominator == 1 for e in E)
        a = nu_walks(W, min(2 * K + 2, 8)); b = nu_simple(W); c = nu_threshold(W)
        tested += 1
        if not (a == b == c):
            mismatch += 1
            print("MISMATCH", W, a, b, c)
print(f"C3/consistency: words with K<=7 (l<=4, digits<=4): {tested}, mismatches walk/simple/threshold: {mismatch}")

# bounds 1/4 <= nu <= 1 over a larger family via threshold
cnt = 0
for l in range(0, 6):
    for W in itertools.product(range(1, 7), repeat=l):
        K = Kc(W)
        if K > 60:
            continue
        nu = nu_threshold(W)
        cnt += 1
        if nu < minnu: minnu, argmin = nu, W
        maxnu = max(maxnu, nu)
        assert F(1, 4) <= nu <= 1, (W, nu)
print(f"bounds: {cnt} words (l<=5, digits<=6, K<=60): min nu = {minnu} at W={argmin}, max nu = {maxnu}; all in [1/4,1]")
print("nu(5,1,5) =", nu_threshold((5, 1, 5)))
