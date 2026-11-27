"""reaudit_S2_5: (i) Lemma 0 / Corollary 0' sanity (category 4); (ii) the closed-walk extraction of 7.1 steps 5-7.

(i) For several irrationals alpha (block Hurwitz with A_k=k, sqrt2, golden ratio) and beta = u*alpha + v + delta
    (delta tiny, nonzero) we check that R_n := ||q_n beta|| / theta_n exceeds 1/4 again and again beyond any
    index reached (Lemma 0 contrapositive), and that for delta = 0, R_n -> 0.
    Also checks 0.2: |m_n| < 3/4 forces m_n = 0 whenever R_{n-1},R_n,R_{n+1} < 1/4 (integer identity m_n = y_{n+1}-a y_n - y_{n-1}).
(ii) Random finite edge sequences e_k = (r_{k-1} -> r_k, tau_k) in G_W (tau_k in the right coset): the procedure
    "take two occurrences k<k' of a non-trivial edge f, read e_k..e_{k'-1}" always gives a closed walk,
    containing f, with cost <= max over the segment of max(|tau|, v(endpoints)); hence nu <= that max.
"""
import random, math
from fractions import Fraction as F
import mpmath as mp

def cfq(a):
    p, q = [a[0]], [1]; pm, qm = 1, 0
    for n in range(1, len(a)):
        p.append(a[n] * p[-1] + (p[-2] if n >= 2 else pm)); q.append(a[n] * q[-1] + (q[-2] if n >= 2 else qm))
    return p, q

mp.mp.dps = 400
cases = {}
W = (5, 1, 5); a = [0]
for k in range(1, 40): a += [k] + list(W)
cases["block (5,1,5), A_k=k"] = a
cases["sqrt2"] = [1] + [2] * 300
cases["golden"] = [1] * 420
for name, a in cases.items():
    p, q = cfq(a); M = len(a) - 1
    alpha = mp.mpf(p[M]) / q[M]
    nmax = M - 40
    for (u, v, dexp) in [(2, -1, None), (3, 5, -60), (0, 0, -80), (1, 0, -100), (0, 0, -1)]:
        beta = u * alpha + v + (mp.mpf(10) ** dexp if dexp is not None else 0)
        R = []; viol = 0
        ys = []
        for n in range(0, nmax):
            z = q[n] * beta; y = z - mp.nint(z); ys.append(y)
            th = q[n] * abs(q[n] * alpha - p[n])
            R.append(abs(y) / th)
        for n in range(1, nmax - 1):
            m = ys[n + 1] - a[n + 1] * ys[n] - ys[n - 1]
            mi = mp.nint(m)
            assert abs(m - mi) < mp.mpf(10) ** -300
            if max(R[n - 1], R[n], R[n + 1]) < 0.25 and mi != 0:
                viol += 1
        last_big = max([n for n in range(nmax) if R[n] >= 0.25], default=None)
        tailmax = max(R[nmax - 30:])
        print(f"{name:22s} u={u} v={v} delta=1e{dexp}: last n with R_n>=1/4: {last_big} (nmax={nmax}); max R over last 30: {mp.nstr(tailmax,5)}; 0.2-violations: {viol}")

# (ii) extraction
def Kc(ws):
    x, y = 0, 1
    for w in ws: x, y = y, w * y + x
    return y
def data(W):
    l = len(W); K = Kc(W)
    c = [Kc(W[:i - 1]) for i in range(1, l + 1)]; cp = [Kc(W[i:]) for i in range(1, l + 1)]
    return K, c, cp, (c[-1] if l else 1)
def vcost(W):
    K, c, cp, s = data(W)
    return [max([F(min((ci * r) % K, K - (ci * r) % K), ci * cpi) for ci, cpi in zip(c, cp)], default=F(0)) for r in range(K)]

rng = random.Random(11); bad = 0; trials = 0
for W in [(5, 1, 5), (3, 1, 3), (1, 1), (2, 2), (1, 2, 1), (), (1,)]:
    K, c, cp, s = data(W); v = vcost(W)
    for trial in range(300):
        L = rng.randint(2, 60)
        rs = [rng.randrange(K) if rng.random() < 0.6 else 0 for _ in range(L + 1)]
        seq = []
        for k in range(1, L + 1):
            base = F((rs[k] - s * rs[k - 1]) % K, K)
            seq.append((rs[k - 1], rs[k], base + rng.choice([-1, 0, 0, 1]) if base else rng.choice([0, 0, 0, 1, -1])))
        nontriv = [i for i, e in enumerate(seq) if not (e[0] == 0 and e[1] == 0 and e[2] == 0)]
        pairs = [(i, j) for i in nontriv for j in nontriv if i < j and seq[i] == seq[j]]
        if not pairs: continue
        i, j = pairs[0]; trials += 1
        walk = seq[i:j]
        closed = walk[0][0] == walk[-1][1] and all(walk[m][1] == walk[m + 1][0] for m in range(len(walk) - 1))
        contains = seq[i] in walk
        cost = max([abs(e[2]) for e in walk] + [v[e[0]] for e in walk] + [v[e[1]] for e in walk])
        segmax = max([abs(e[2]) for e in seq[i:j + 1]] + [v[e[0]] for e in seq[i:j + 1]] + [v[e[1]] for e in seq[i:j + 1]])
        if not (closed and contains and cost <= segmax): bad += 1
print(f"extraction: {trials} trials, failures {bad}")
