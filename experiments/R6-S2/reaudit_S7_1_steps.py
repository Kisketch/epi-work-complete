#!/usr/bin/env python3
"""R6 side-track Step 4 re-audit (repair round 1) of proofs/R6-S7-mstar.md.

Independent script written by an isolated skeptic. Does NOT import common.py /
cfdata.py or any R6_R6-S7_* / audit_S7_* script.

Checks, with exact integer / Fraction arithmetic, on
  (a) all words with K(W) <= KMAX_EXH (exhaustive enumeration),
  (b) random words (identities only when K is huge; full r-scan when K small),
  (c) hand-picked extreme words (empty, (1), all-ones, huge entries, K in {1,2}):
  Step 0  (N) nonnegativity, (RR) length-1 case, (LL) left recursion;
          continuants recomputed independently via 2x2 matrix products.
  Step 1  (R), (L) with the extended indices c_0=0, c_{l+1}=K, c'_0=K, c'_{l+1}=0.
  Step 2  D_j = c_{j+1}c'_j + c_j c'_{j+1} = K for 0<=j<=l; also D_j-D_{j-1}=0.
  Step 3  gcd(K, c'_1) = 1.
  Step 4  c_j == (-1)^{j-1} lambda c'_j (mod K), 0<=j<=l+1.
  Step 5/6 for every r != 0: the index j chosen by the proof's rule satisfies
          d_K(c_j r)/(c_j c'_j) >= 1/2 and d_K(u c'_j) = |u| c'_j in case (ii);
          and directly v(r) >= 1/2 (computed from the S.1 definition, no duality).
  Step 7  K(W)=1  <=>  W in {(), (1,)} (exhaustive over small words).
Counts case (i) (|u| = K/2) occurrences explicitly.
"""
from fractions import Fraction
from math import gcd
import random
import sys

random.seed(20261127)


def K_right(w):
    """Continuant by the S.1 right recursion, with K()=1 and length -1 -> 0."""
    a, b = 0, 1  # K(length -1), K(length 0)
    for x in w:
        a, b = b, x * b + a
    return b


def K_of(w, lo, hi):
    """K(w_lo..w_hi), 1-based inclusive; length hi-lo+1 may be 0 or -1."""
    L = hi - lo + 1
    if L == -1:
        return 0
    if L < -1:
        raise ValueError("length < -1 undefined")
    return K_right(w[lo - 1:hi])


def K_matrix(w):
    """Independent: (1,1) entry of prod [[x,1],[1,0]] (empty product -> I)."""
    M = [[1, 0], [0, 1]]
    for x in w:
        M = [[M[0][0] * x + M[0][1], M[0][0]],
             [M[1][0] * x + M[1][1], M[1][0]]]
    return M[0][0]


def dK(x, K):
    x %= K
    return min(x, K - x)


def data(w):
    l = len(w)
    K = K_right(w)
    c = {j: K_of(w, 1, j - 1) for j in range(0, l + 2)}
    cp = {j: K_of(w, j + 1, l) for j in range(0, l + 2)}
    return l, K, c, cp


fails = []
stats = dict(words=0, rscan_words=0, r_checked=0, case_i=0, case_ii=0,
             identity_words=0, min_mstar=None, min_mstar_word=None)


def fail(msg):
    fails.append(msg)
    if len(fails) <= 20:
        print("FAIL:", msg)


def check_identities(w):
    l, K, c, cp = data(w)
    stats["identity_words"] += 1
    # matrix cross-check of K and of all c_j, c'_j
    if K_matrix(w) != K:
        fail(f"matrix K mismatch {w}")
    for j in range(1, l + 2):
        if K_matrix(w[:j - 1]) != c[j]:
            fail(f"matrix c_{j} mismatch {w}")
    for j in range(0, l + 1):
        if K_matrix(w[j:]) != cp[j]:
            fail(f"matrix c'_{j} mismatch {w}")
    # boundary values
    if not (c[0] == 0 and c[1] == 1 and c[l + 1] == K and cp[0] == K and cp[l + 1] == 0):
        if l >= 1:
            fail(f"boundary values {w}")
    if l >= 1 and cp[l] != 1:
        fail(f"c'_l != 1 {w}")
    # (N)
    for j in range(0, l + 2):
        if c[j] < 0 or cp[j] < 0:
            fail(f"(N) negative {w}")
    for j in range(1, l + 2):
        if c[j] < 1:
            fail(f"(N) c_{j}<1 {w}")
    for j in range(0, l + 1):
        if cp[j] < 1:
            fail(f"(N) c'_{j}<1 {w}")
    # (LL) on every nonempty subword
    for a in range(1, l + 1):
        for b in range(a, l + 1):
            m = b - a + 1
            lhs = K_of(w, a, b)
            rhs = w[a - 1] * K_of(w, a + 1, b) + K_of(w, a + 2, b)
            if lhs != rhs:
                fail(f"(LL) {w} [{a},{b}]")
            if m == 1 and lhs != w[a - 1]:
                fail(f"(RR) len1 {w}")
    # reversal symmetry (matrix-route remark)
    if K_right(w[::-1]) != K:
        fail(f"reversal {w}")
    # (R), (L)
    for j in range(1, l + 1):
        if c[j + 1] != w[j - 1] * c[j] + c[j - 1]:
            fail(f"(R) j={j} {w}")
        if cp[j - 1] != w[j - 1] * cp[j] + cp[j + 1]:
            fail(f"(L) j={j} {w}")
    # Step 2
    D = {j: c[j + 1] * cp[j] + c[j] * cp[j + 1] for j in range(0, l + 1)}
    for j in range(0, l + 1):
        if D[j] != K:
            fail(f"D_{j}!=K {w}")
        if c[j + 1] * cp[j] > K:
            fail(f"c_{j+1}c'_{j}>K {w}")
    # monotonicity
    for j in range(1, l + 1):
        if c[j + 1] < c[j]:
            fail(f"monotone {w}")
    if l >= 1:
        # Step 3
        if gcd(K, cp[1]) != 1:
            fail(f"gcd {w}")
        # Step 4
        if K >= 2:
            lam = pow(cp[1], -1, K)
            for j in range(0, l + 2):
                sgn = 1 if (j - 1) % 2 == 0 else -1
                if (c[j] - sgn * lam * cp[j]) % K != 0:
                    fail(f"duality j={j} {w}")
        # sigma, gcd(sigma,K)=1 (S.1 remark, not used by the proof)
        if gcd(c[l], K) != 1:
            fail(f"gcd(sigma,K) {w}")
    return l, K, c, cp


def check_prop1(w):
    l, K, c, cp = data(w)
    if K < 2:
        return None
    stats["rscan_words"] += 1
    lam = pow(cp[1], -1, K)
    mstar = None
    for r in range(1, K):
        # direct definition of v(r)
        v = max(Fraction(dK(c[i] * r, K), c[i] * cp[i]) for i in range(1, l + 1))
        if v < Fraction(1, 2):
            fail(f"PROP1 FALSE: v({r})={v} for {w}")
        mstar = v if mstar is None or v < mstar else mstar
        # proof's index choice
        u = (lam * r) % K
        if u > K // 2:
            u -= K
        if not (1 <= abs(u) <= K / 2):
            fail(f"u repr {w} r={r}")
        for jj in range(1, l + 1):
            if dK(c[jj] * r, K) != dK(u * cp[jj], K):
                fail(f"step5 d_K mismatch {w} r={r} j={jj}")
        Js = [j for j in range(1, l + 2) if c[j] > 2 * abs(u)]
        if not Js:
            stats["case_i"] += 1
            if 2 * abs(u) != K:
                fail(f"case(i) but |u|!=K/2 {w} r={r}")
            j = l
            ratio = Fraction(dK(c[j] * r, K), c[j] * cp[j])
            if dK(u, K) * 2 != K or cp[l] != 1:
                fail(f"case(i) details {w} r={r}")
        else:
            stats["case_ii"] += 1
            J = min(Js)
            if J < 2:
                fail(f"J<2 {w} r={r}")
            j = J - 1
            if not (c[j] <= 2 * abs(u) < c[j + 1]):
                fail(f"bracket {w} r={r}")
            if 2 * abs(u) * cp[j] >= K:
                fail(f"|u c'_j| not < K/2 {w} r={r}")
            if dK(u * cp[j], K) != abs(u) * cp[j]:
                fail(f"d_K(u c'_j) != |u|c'_j {w} r={r}")
            ratio = Fraction(dK(c[j] * r, K), c[j] * cp[j])
        if ratio < Fraction(1, 2):
            fail(f"chosen-index ratio <1/2 {w} r={r}")
        stats["r_checked"] += 1
    if stats["min_mstar"] is None or mstar < stats["min_mstar"]:
        stats["min_mstar"] = mstar
        stats["min_mstar_word"] = tuple(w)
    return mstar


def words_with_K_le(KMAX):
    """All positive-integer words (incl. empty) with K(W) <= KMAX (DFS; K grows)."""
    out = [()]
    stack = [()]
    while stack:
        w = stack.pop()
        for x in range(1, KMAX + 1):
            nw = w + (x,)
            if K_right(nw) > KMAX:
                break  # K increasing in last letter
            out.append(nw)
            stack.append(nw)
    return out


KMAX_EXH = int(sys.argv[1]) if len(sys.argv) > 1 else 120
print(f"== (a) exhaustive: all words with K(W) <= {KMAX_EXH}")
W_all = words_with_K_le(KMAX_EXH)
print("number of words:", len(W_all))
k1 = []
for w in W_all:
    stats["words"] += 1
    check_identities(w)
    if K_right(w) == 1:
        k1.append(w)
    check_prop1(w)
print("words with K=1 among them:", k1)
if sorted(k1) != sorted([(), (1,)]):
    fail(f"K=1 characterisation: {k1}")
# K=1 <=> W in {(),(1)} also for all words of length <= 6 with entries <= 6 (independent of KMAX)
import itertools
cnt = 0
for L in range(0, 7):
    for w in itertools.product(range(1, 7), repeat=L):
        cnt += 1
        if (K_right(w) == 1) != (w in [(), (1,)]):
            fail(f"K=1 char {w}")
        if len(w) >= 2 and K_right(w) < w[0] * w[1] + 1:
            fail(f"K>=c_3 {w}")
print("K=1 characterisation also checked on", cnt, "words (len<=6, entries<=6)")
print("min m* over exhaustive set:", stats["min_mstar"], float(stats["min_mstar"]),
      "at", stats["min_mstar_word"])
print("case (i) count:", stats["case_i"], " case (ii) count:", stats["case_ii"])

print("== (b) random words")
rnd_small = 0
for _ in range(4000):
    L = random.randint(1, 9)
    mx = random.choice([2, 3, 5, 10])
    w = tuple(random.randint(1, mx) for _ in range(L))
    check_identities(w)
    if K_right(w) <= 3000:
        check_prop1(w)
        rnd_small += 1
for _ in range(1500):
    L = random.randint(1, 40)
    w = tuple(random.choice([1, 1, 1, 2, 3, 7, 50, 10**6]) for _ in range(L))
    check_identities(w)  # huge K: identities only
print("random words with full r-scan:", rnd_small)

print("== (c) extreme words")
ext = [(), (1,), (2,), (1, 1), (3,), (1, 2), (2, 1), (1, 1, 1), (2, 2), (1, 1, 1, 1)]
ext += [tuple([1] * n) for n in range(5, 21)]            # Fibonacci K
ext += [(1000,), (1000, 1), (1, 1000), (1000, 1, 1000), (999, 1, 1, 999),
        (5, 1, 5), (5, 1, 1, 1, 5), (2, 1, 1, 2), (1, 2, 1), (2, 1, 2)]
ext += [(w, 1, w) for w in (2, 3, 4, 10, 37)]
ext += [(1, n) for n in (2, 50, 997)] + [(n, 1) for n in (2, 50, 997)]
ext += [(10**12,), (10**9, 1, 10**9), tuple([10**6] * 8)]
for w in ext:
    l, K, c, cp = check_identities(w)
    tag = ""
    if K <= 5000:
        m = check_prop1(w)
        tag = f"m*={m}" if m is not None else "K=1 (no r!=0)"
    else:
        tag = "K too large for r-scan (identities only)"
    print(f"  W={w if len(w) <= 8 else str(w[:4])+'...len'+str(len(w))}: K={K if K < 10**8 else 'big'} {tag}")

# K=2 words: exactly (2) and (1,1)
k2 = [w for w in W_all if K_right(w) == 2]
print("words with K=2:", k2)

print("== summary")
print({k: (str(v) if isinstance(v, Fraction) else v) for k, v in stats.items()})
print("FAILURES:", len(fails))
