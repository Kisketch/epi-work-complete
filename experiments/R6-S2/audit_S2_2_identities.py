"""Audit R6-S2 step checks (exact integers / high precision): §2.3 D1-D4, §2.4 (A1)(A2)(A2a)(A2b),
§3 Lemma B (B1 non-asymptotic bound, B2-B4 limits), F2/D3.

Words: all W with l<=4 letters in 1..4, plus E-list and boundary words.  Prefixes: N=0 (empty) and
random prefixes with small letters; A_k sequences: 10k, k (slow), and A_1=1 start (A_k = k).
"""
import itertools, random, sys
from fractions import Fraction
import mpmath as mp

sys.path.insert(0, __import__("os").path.dirname(__file__))
from common import cont, block_data

random.seed(20261127)
mp.mp.dps = 400


def Kint(ws):
    return cont(list(ws))


def Kseg(W, a, b):
    """K_[a,b] with 1-based inclusive indices; b=a-1 -> 1, b=a-2 -> 0."""
    if b == a - 2:
        return 0
    if b == a - 1:
        return 1
    assert b >= a
    return Kint(W[a - 1:b])


fails = []
words = [()] + [w for l in range(1, 5) for w in itertools.product(range(1, 5), repeat=l)]
words += [(5, 1, 5), (2, 3), (1, 1, 1), (7, 1, 1, 7, 2)]

# (A2) split identity for every word and every split position; (A2a); (A2b)
nA2 = 0
for W in words:
    l = len(W)
    for i in range(1, l + 1):
        lhs = Kint(W)
        rhs = Kseg(W, 1, i - 1) * Kseg(W, i, l) + Kseg(W, 1, i - 2) * Kseg(W, i + 1, l)
        nA2 += 1
        if lhs != rhs:
            fails.append(("A2", W, i))
        # A2b
        if Kseg(W, i, l) != W[i - 1] * Kseg(W, i + 1, l) + Kseg(W, i + 2, l):
            fails.append(("A2b", W, i))
    K, c, cp, sigma = block_data(W)
    if l >= 1:
        import math
        if math.gcd(sigma, K) != 1:
            fails.append(("gcd(sigma,K)", W))
print(f"(A2)/(A2a)/(A2b) exact checks: {nA2} split identities")


def build(prefix, W, Aseq, kmax):
    a = [prefix[0]] + list(prefix[1:])
    N = len(prefix) - 1
    for k in range(1, kmax + 1):
        a.append(Aseq(k)); a.extend(W)
    return a, N


def convergents(a):
    p = [a[0]]; q = [1]
    pm, qm = 1, 0
    for n in range(1, len(a)):
        p.append(a[n] * p[-1] + (p[-2] if n >= 2 else pm))
        q.append(a[n] * q[-1] + (q[-2] if n >= 2 else qm))
    return p, q


def value(a):
    x = mp.mpf(a[-1])
    for t in reversed(a[:-1]):
        x = t + 1 / x
    return x


cases = 0
worst = {}
for W in [(), (1,), (2,), (1, 1), (1, 2), (2, 3), (5, 1, 5), (1, 1, 1), (3, 1, 4, 1)]:
    l = len(W)
    K, c, cp, sigma = block_data(W)
    for prefix in [(0,), (3,), (0, 1), (-2, 1, 1, 7), (1, 5, 1)]:
        for name, Aseq in [("10k", lambda k: 10 * k), ("k", lambda k: k), ("k^2", lambda k: k * k)]:
            kmax = 40
            a, N = build(prefix, W, Aseq, kmax)
            p, q = convergents(a)
            M = len(a) - 1
            # F2 exact
            for n in range(0, M):
                if p[n + 1] * q[n] - p[n] * q[n + 1] != (-1) ** n:
                    fails.append(("F2", W, prefix, n))
            # D1 exact
            for m in range(0, M - 1):
                if not (q[m + 2] >= 2 * q[m] and q[m + 1] >= a[m + 1] * q[m]):
                    fails.append(("D1", W, prefix, m))
            alpha = value(a)  # truncation: a long tail; only n << M used
            nk = [N + (k - 1) * (l + 1) for k in range(1, kmax + 1)]
            for k in range(1, kmax + 1):
                assert a[nk[k - 1] + 1] == Aseq(k)
                for i in range(1, l + 1):
                    assert a[nk[k - 1] + 1 + i] == W[i - 1]
            Mu = nk[30]  # use indices well inside the truncation
            eps = [q[n] * alpha - p[n] for n in range(Mu + 2)]
            # D3 exact relation (integer part)
            for (m, n) in [(nk[3], nk[5] + 1), (nk[2], nk[2]), (nk[1], nk[1] + 1)]:
                D = q[m] * p[n] - p[m] * q[n]
                if mp.fabs(q[n] * eps[m] - q[m] * eps[n] - D) > mp.mpf(10) ** (-300):
                    fails.append(("D3", W, prefix, m, n))
            # D4 (i),(ii) exact rational
            for k in range(1, 25):
                s1 = sum(q[nk[j - 1]] for j in range(1, k + 1))
                if s1 > 4 * q[nk[k - 1]]:
                    fails.append(("D4i", W, prefix, k))
                s2 = sum(Fraction(1, q[nk[j - 1] + 1]) for j in range(k + 1, kmax + 1))
                if s2 > Fraction(4, q[nk[k] + 1]):
                    fails.append(("D4ii", W, prefix, k))
            # (A1) exact for X = q, p, D(m',.)
            for k in range(1, 25):
                n0 = nk[k - 1]
                mprime = nk[max(0, k - 3)]
                for X in (q, p, [q[mprime] * p[n] - p[mprime] * q[n] for n in range(len(q))]):
                    for j in range(0, l + 1):
                        if X[n0 + 1 + j] != Kseg(W, 1, j) * X[n0 + 1] + Kseg(W, 2, j) * X[n0]:
                            fails.append(("A1", W, prefix, k, j))
            # Lemma B: B1 non-asymptotic, B4 limit
            for k in range(1, 30):
                n0 = nk[k - 1]
                th = q[n0] * mp.fabs(eps[n0])
                inv = 1 / th
                if not (Aseq(k) < inv < Aseq(k) + 2):
                    fails.append(("B1", W, prefix, name, k, float(inv)))
                for i in range(1, l + 1):
                    thi = q[n0 + i] * mp.fabs(eps[n0 + i])
                    lim = Fraction(K, c[i - 1] * cp[i - 1])
                    err = mp.fabs(1 / thi - mp.mpf(lim.numerator) / lim.denominator)
                    key = (W, name)
                    if k == 29:
                        worst[key] = max(worst.get(key, 0), float(err * Aseq(k)))
            cases += 1

print(f"cases (W x prefix x A-sequence): {cases}")
print("B4: at k=29, A_k * |1/theta_{n_k+i} - K/(c_i c_i')| (max over prefixes, i) -- should be O(1):")
for key in sorted(worst, key=str):
    print(f"   W={key[0]!s:14} A={key[1]:4}  {worst[key]:.4f}")
print(f"FAILURES: {len(fails)}")
for f in fails[:30]:
    print("  ", f)
