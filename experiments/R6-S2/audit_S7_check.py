#!/usr/bin/env python3
"""
R6 side-track Step 4 audit (skeptic, independent): proofs/R6-S7-mstar.md
Claim: for every block word W with K(W) >= 2, m*(W) := min_{r != 0 mod K} v(r) >= 1/2,
       and nu(W) = min(1, m*(W)); for K(W) = 1, nu(W) = 1.

Written from the definitions in PLAN_GRAPH.md S.1 only.  Does NOT import or read
the prover's scripts (R6_R6-S7_*) or proofs/R6-S2.md.  Exact integer / Fraction arithmetic.
Category 4 (finite computation) -- not a proof.

Parts:
  A. Step-by-step identity checks (R), (L), splitting identity, gcd(p,K)=1,
     duality c_j == (-1)^(j-1) lambda c'_j (mod K), monotonicity, boundary values.
  B. Proposition 1: v(r) >= 1/2 for every r != 0, plus the proof's own index choice
     (Step 6): case (i) iff |u| = K/2, and in case (ii) d_K(u c'_j) = |u| c'_j and ratio >= 1/2.
  C. Corollary 2: nu(W) by an independent brute-force minimax over closed walks
     (graph reachability at every candidate threshold), compared with min(1, m*).
  D. Word families: exhaustive small, all-ones (Fibonacci), large entries, random,
     (w,1^k,w), palindromes, and a greedy/random search trying to drive m* down toward 1/2.
"""
import itertools
import random
import sys
from fractions import Fraction
from math import gcd

HALF = Fraction(1, 2)


def cont(ws):
    """Continuant K(w_1..w_m) per S.1: K()=1, K(w1)=w1, K(...)=w_m K(..m-1)+K(..m-2); K(len -1)=0."""
    a, b = 0, 1  # K(len -1), K()
    for w in ws:
        a, b = b, w * b + a
    return b


def data(W):
    """K, c_i, c'_i (1..l) straight from the definitions (subword continuants), sigma."""
    l = len(W)
    K = cont(W)
    c = {i: cont(W[: i - 1]) for i in range(1, l + 1)}
    cp = {i: cont(W[i:]) for i in range(1, l + 1)}
    sigma = c[l] if l >= 1 else 1
    return K, c, cp, sigma


def dK(x, K):
    x %= K
    return min(x, K - x)


def vertex_costs(W):
    K, c, cp, sigma = data(W)
    l = len(W)
    v = []
    for r in range(K):
        if l == 0:
            v.append(Fraction(0))
            continue
        v.append(max(Fraction(dK(c[i] * r, K), c[i] * cp[i]) for i in range(1, l + 1)))
    return v


# ---------------------------------------------------------------- Part A
def check_identities(W):
    """Return list of failure strings (empty = all pass)."""
    fails = []
    l = len(W)
    K = cont(W)
    if l == 0:
        return fails
    # extended c_j, c'_j for 0..l+1 via the length -1 convention
    def cx(j):  # K_[1, j-1]
        if j - 1 < 0:
            return 0  # length -1
        return cont(W[: j - 1])

    def cpx(j):  # K_[j+1, l]
        if j + 1 > l + 1:
            return 0
        return cont(W[j:])

    C = [cx(j) for j in range(l + 2)]
    Cp = [cpx(j) for j in range(l + 2)]
    if not (C[0] == 0 and C[1] == 1 and C[l + 1] == K and Cp[0] == K and Cp[l] == 1 and Cp[l + 1] == 0):
        fails.append(f"boundary values C={C} Cp={Cp}")
    for j in range(1, l + 1):
        w = W[j - 1]
        if C[j + 1] != w * C[j] + C[j - 1]:
            fails.append(f"(R) j={j}")
        if Cp[j - 1] != w * Cp[j] + Cp[j + 1]:
            fails.append(f"(L) j={j}")
    for j in range(0, l + 1):
        if C[j + 1] * Cp[j] + C[j] * Cp[j + 1] != K:
            fails.append(f"split j={j}")
    for j in range(1, l + 1):
        if C[j + 1] < C[j]:
            fails.append(f"monotone j={j}")
        if Cp[j] < 1 or C[j] < 1:
            fails.append(f"positivity j={j}")
    p = Cp[1]
    if gcd(p, K) != 1:
        fails.append("gcd(p,K)!=1")
        return fails
    lam = pow(p, -1, K) if K > 1 else 0
    for j in range(0, l + 2):
        if (C[j] - (-1) ** ((j - 1) % 2) * lam * Cp[j]) % K != 0:
            fails.append(f"duality j={j}")
    # sigma relation (S.1 claims gcd(sigma,K)=1)
    sigma = C[l]
    if gcd(sigma, K) != 1:
        fails.append("gcd(sigma,K)!=1")
    return fails


# ---------------------------------------------------------------- Part B
def check_prop1(W, want_detail=False):
    """Check v(r) >= 1/2 for r != 0 and the proof's Step-6 index choice.
    Returns (fails, mstar, n_case_i)."""
    K, c, cp, sigma = data(W)
    l = len(W)
    fails = []
    if K < 2:
        return fails, None, 0
    p = cp[1]
    lam = pow(p, -1, K)
    C = [0] + [c[i] for i in range(1, l + 1)] + [K]  # C[0..l+1]
    mstar = None
    ncase_i = 0
    for r in range(1, K):
        vr = max(Fraction(dK(c[i] * r, K), c[i] * cp[i]) for i in range(1, l + 1))
        if vr < HALF:
            fails.append(f"v({r})={vr}<1/2")
        mstar = vr if mstar is None or vr < mstar else mstar
        # proof's index choice
        u = (lam * r) % K
        if u > K // 2:
            u -= K  # representative with 1 <= |u| <= K/2
        au = abs(u)
        if not (1 <= au and 2 * au <= K):
            fails.append(f"rep u r={r}")
        # Step 5: d_K(c_j r) == d_K(u c'_j)
        for j in range(1, l + 1):
            if dK(c[j] * r, K) != dK(u * cp[j], K):
                fails.append(f"step5 r={r} j={j}")
        S = [j for j in range(1, l + 2) if C[j] > 2 * au]
        if not S:
            ncase_i += 1
            if 2 * au != K:
                fails.append(f"case(i) but |u|!=K/2 r={r}")
            j = l
            if Fraction(dK(c[j] * r, K), c[j] * cp[j]) < HALF:
                fails.append(f"case(i) ratio<1/2 r={r}")
        else:
            J = min(S)
            if J < 2:
                fails.append(f"J<2 r={r}")
                continue
            j = J - 1
            if not (C[j] <= 2 * au < C[j + 1]):
                fails.append(f"bracket r={r}")
            if not (2 * au * cp[j] < K):
                fails.append(f"|u c'_j|<K/2 fails r={r}")
            if dK(u * cp[j], K) != au * cp[j]:
                fails.append(f"dK(u c'_j)!=|u|c'_j r={r}")
            if Fraction(dK(c[j] * r, K), c[j] * cp[j]) < HALF:
                fails.append(f"case(ii) ratio<1/2 r={r}")
        if 2 * au == K and S:
            fails.append(f"|u|=K/2 but case(ii) r={r}")  # impossible: C[l+1]=K not > K
    return fails, mstar, ncase_i


def mstar_fast(W):
    """Integer-only m* (as Fraction) for larger K; also returns whether all v(r)>=1/2."""
    K, c, cp, sigma = data(W)
    l = len(W)
    best = None
    ok = True
    for r in range(1, K):
        # v(r) = max_i dK(c_i r)/(c_i c'_i)
        bn, bd = -1, 1
        for i in range(1, l + 1):
            n = dK(c[i] * r, K)
            d = c[i] * cp[i]
            if n * bd > bn * d:
                bn, bd = n, d
        if 2 * bn < bd:
            ok = False
        if best is None or bn * best[1] < best[0] * bd:
            best = (bn, bd)
    return Fraction(*best), ok


# ---------------------------------------------------------------- Part C
def nu_bruteforce(W):
    """Independent minimax over closed walks in G_W (S.1 definition).
    Edge r->r' carries t in (r'-sigma r)/K + Z, cost |t|; vertex cost v(r).
    Walk must not consist only of trivial loops (vertex 0, t=0).
    For a threshold T: allowed vertices v<=T, allowed edges with some admissible t, |t|<=T,
    excluding the trivial loop t=0 at 0 (the loop at 0 with |t|=1 is allowed iff T>=1).
    nu = least T at which a non-trivial closed walk exists."""
    K, c, cp, sigma = data(W)
    v = vertex_costs(W)
    # minimal |t| on each edge
    def tmin(r, rp):
        return Fraction(dK(rp - sigma * r, K), K)

    tm = [[tmin(r, rp) for rp in range(K)] for r in range(K)]
    cands = sorted(set(v) | {x for row in tm for x in row} | {Fraction(1)})

    def feasible(T):
        verts = [r for r in range(K) if v[r] <= T]
        if T >= 1:
            return True  # loop at vertex 0 (v(0)=0) with t=+-1
        adj = {r: [rp for rp in verts if (r, rp) != (0, 0) and tm[r][rp] <= T] for r in verts}
        color = {r: 0 for r in verts}
        for s in verts:
            if color[s]:
                continue
            stack = [(s, iter(adj[s]))]
            color[s] = 1
            while stack:
                node, it = stack[-1]
                nxt = next(it, None)
                if nxt is None:
                    color[node] = 2
                    stack.pop()
                elif color[nxt] == 1:
                    return True
                elif color[nxt] == 0:
                    color[nxt] = 1
                    stack.append((nxt, iter(adj[nxt])))
        return False

    lo, hi = 0, len(cands) - 1  # feasible(cands[hi]) is True (cands[hi] >= 1)
    assert feasible(cands[hi])
    while lo < hi:
        mid = (lo + hi) // 2
        if feasible(cands[mid]):
            hi = mid
        else:
            lo = mid + 1
    return cands[lo]


# ---------------------------------------------------------------- driver
def main():
    out = []
    P = out.append
    random.seed(20261127)
    P("# audit_S7_check.py -- independent skeptic audit of proofs/R6-S7-mstar.md (category 4)")
    P(f"# python {sys.version.split()[0]}")

    # ---- word families
    fams = {}
    small = []
    for l in range(0, 6):
        for W in itertools.product(range(1, 8), repeat=l):
            if cont(W) <= 400:
                small.append(tuple(W))
    fams["exhaustive l<=5, w<=7, K<=400"] = small
    fams["all-ones l=0..24"] = [tuple([1] * l) for l in range(0, 25)]
    fams["single letter (w)"] = [(w,) for w in [1, 2, 3, 4, 5, 10, 99, 1000, 4097]]
    big = [(1000,), (1000, 1), (1, 1000), (1, 1000, 1), (2, 1000, 2), (500, 1, 500), (1, 1, 300, 1, 1),
           (300, 1, 1, 1, 1), (1, 1, 1, 1, 300), (2, 2, 2, 2, 2, 2, 2), (3,) * 6, (1, 2) * 5,
           (2, 1) * 5, (50, 50), (1, 50, 1, 50, 1), (99, 1, 99), (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2)]
    fams["large-entry / structured"] = big
    wk = []
    for w in range(1, 40):
        for k in range(0, 6):
            W = (w,) + (1,) * k + (w,)
            if cont(W) <= 20000:
                wk.append(W)
    fams["(w,1^k,w)"] = wk
    rnd = []
    while len(rnd) < 3000:
        l = random.randint(1, 10)
        W = tuple(random.choice([1, 1, 1, 2, 2, 3, 4, 5, 7, 11, 30]) for _ in range(l))
        if cont(W) <= 3000:
            rnd.append(W)
    fams["random (K<=3000)"] = rnd

    total_words = 0
    global_min = None
    global_arg = None
    all_ok = True
    for name, ws in fams.items():
        nA = nB = 0
        fam_min = None
        fam_arg = None
        ncase_i_tot = 0
        for W in ws:
            total_words += 1
            fa = check_identities(W)
            if fa:
                nA += 1
                all_ok = False
                if nA <= 5:
                    P(f"  [A FAIL] W={W}: {fa[:4]}")
            K = cont(W)
            if K < 2:
                continue
            if K <= 25000:
                fb, ms, nci = check_prop1(W)
                ncase_i_tot += nci
            else:
                ms, ok = mstar_fast(W)
                fb = [] if ok else ["v<1/2 somewhere"]
            if fb:
                nB += 1
                all_ok = False
                if nB <= 5:
                    P(f"  [B FAIL] W={W}: {fb[:4]}")
            if fam_min is None or ms < fam_min:
                fam_min, fam_arg = ms, W
        P(f"[{name}] words={len(ws)}  A-fail={nA}  B-fail={nB}  case(i) hits={ncase_i_tot}  "
          f"min m*={fam_min} (~{float(fam_min) if fam_min is not None else None:.6f}) at W={fam_arg}"
          if fam_min is not None else f"[{name}] words={len(ws)} A-fail={nA} (all K=1)")
        if fam_min is not None and (global_min is None or fam_min < global_min):
            global_min, global_arg = fam_min, fam_arg

    # ---- all-ones detail
    P("all-ones detail (l, K, m*):")
    for l in range(2, 25):
        W = (1,) * l
        ms, ok = mstar_fast(W)
        P(f"  l={l:2d} K={cont(W):6d} m*={ms} ~{float(ms):.6f} all>=1/2:{ok}")

    # ---- Part C: nu brute force vs min(1, m*)
    P("Part C: nu by brute-force closed-walk minimax vs min(1,m*)  (K<=120)")
    cw = [W for W in small if cont(W) <= 120] + [W for W in rnd if cont(W) <= 120][:400] + \
         [(), (1,), (1, 1), (5, 1, 5), (5, 1, 1, 1, 5), (2,), (2, 2), (1, 1, 1, 1, 1, 1, 1, 1, 1)]
    seen = set()
    nC = nCbad = 0
    for W in cw:
        if W in seen:
            continue
        seen.add(W)
        K = cont(W)
        nu = nu_bruteforce(W)
        if K == 1:
            pred = Fraction(1)
        else:
            v = vertex_costs(W)
            pred = min(Fraction(1), min(v[1:]))
        nC += 1
        if nu != pred:
            nCbad += 1
            all_ok = False
            if nCbad <= 10:
                P(f"  [C MISMATCH] W={W} K={K} nu_bf={nu} min(1,m*)={pred}")
    P(f"  words={nC}  mismatches={nCbad}")
    for W in [(), (1,), (1, 1), (5, 1, 5), (5, 1, 1, 1, 5), (2,), (1, 1, 1, 1, 1, 1, 1, 1, 1)]:
        P(f"  nu{W} = {nu_bruteforce(W)}")

    # ---- Part D: adversarial search for small m*
    P("Part D: adversarial local search minimising m* (K<=6000)")
    alphabet = [1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 15, 25]
    best = (Fraction(2), None)
    for trial in range(120):
        W = list(random.choice(rnd))
        cur, _ = mstar_fast(tuple(W)) if cont(W) >= 2 else (Fraction(5), True)
        for step in range(80):
            W2 = W[:]
            mv = random.random()
            if mv < 0.4 and W2:
                W2[random.randrange(len(W2))] = random.choice(alphabet)
            elif mv < 0.7 and len(W2) < 14:
                W2.insert(random.randrange(len(W2) + 1), random.choice(alphabet))
            elif len(W2) > 1:
                del W2[random.randrange(len(W2))]
            K = cont(W2)
            if K < 2 or K > 6000:
                continue
            ms, ok = mstar_fast(tuple(W2))
            if not ok:
                all_ok = False
                P(f"  [D FAIL] W={W2} has v<1/2")
            if ms <= cur:
                W, cur = W2, ms
        if cur < best[0]:
            best = (cur, tuple(W))
    P(f"  best m* found = {best[0]} ~{float(best[0]):.6f} at W={best[1]}")
    if global_min is None or best[0] < global_min:
        global_min, global_arg = best

    # ---- non-load-bearing remark (proof l.99)
    # (a) naive nearest-integer version: d_K(c_j p) == c'_j ?  (expected to FAIL sometimes)
    # (b) KL version per S.1 (theta_n = q_n |q_n alpha - p_n| with convergent numerator p_n):
    #     for alpha = p/K = [0; w_1..w_l], q_{j-1} = c_j and theta_{j-1} == c_j c'_j / K ?
    P("Remark check (proof line 99, non-load-bearing)")
    bad_a, bad_b, n = [], [], 0
    for W in small:
        K, c, cp, s = data(W)
        if K < 2:
            continue
        n += 1
        p = cp[1]
        assert Fraction(p, K) == Fraction(p, K)
        # convergents of [0; w_1..w_l]
        pm2, pm1, qm2, qm1 = 1, 0, 0, 1   # p_{-1}... standard: p_{-1}=1,p_0=a0=0; q_{-1}=0,q_0=1
        P_, Q_ = [pm1], [qm1]             # index 0 -> (p_0,q_0)
        for w in W:
            pm2, pm1 = pm1, w * pm1 + pm2
            qm2, qm1 = qm1, w * qm1 + qm2
            P_.append(pm1); Q_.append(qm1)
        assert Fraction(P_[-1], Q_[-1]) == Fraction(p, K), (W,)
        for j in range(1, len(W) + 1):
            if dK(c[j] * p, K) != cp[j]:
                bad_a.append((W, j)); break
        for j in range(1, len(W) + 1):
            q, pn = Q_[j - 1], P_[j - 1]
            if q != c[j] or abs(q * p - pn * K) != cp[j]:
                bad_b.append((W, j)); break
    P(f"  (a) nearest-integer form fails on {len(bad_a)} of {n} words, e.g. {bad_a[:3]}")
    P(f"  (b) convergent-numerator (S.1 theta) form fails on {len(bad_b)} of {n} words")

    P(f"TOTAL words checked = {total_words}; global min m* = {global_min} (~{float(global_min):.6f}) at W={global_arg}")
    P(f"OVERALL: {'ALL CHECKS PASS' if all_ok else 'FAILURES PRESENT'}")
    print("\n".join(out))


if __name__ == "__main__":
    main()
