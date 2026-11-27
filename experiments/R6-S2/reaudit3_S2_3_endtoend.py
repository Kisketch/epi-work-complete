# reaudit3 script 3: end-to-end numerical test of S1(b)(d) and S2 (both directions) via the S1(d) construction.
# Category 4 (finite computation) evidence only.
# For each word W (incl. l=0, K=1, K=2, even K, nu<1) and each growth regime of A_k (fast / slow A_k=k /
# early A_k=1), build beta = (1/K) sum T'_k |eps_{n_k}|, compute R_n = ||q_n beta||/theta_n in late blocks,
# and compare block maxima M_k with the predicted max(|tau_k|, v(r_k)); check canonical labels and t_k - tau_k.
import sys, os, random
sys.path.insert(0, os.path.dirname(__file__))
from fractions import Fraction as Fr
import mpmath
from reaudit3_S2_common import Kc, params, vcost, nu, dK

random.seed(7)
fails = 0
def chk(c, m):
    global fails
    if not c:
        fails += 1; print('   FAIL', m)

def best_cycle(W):
    """explicit minimal closed walk (list of (r_prev, r, t)) achieving nu(W)."""
    K, c, cp, s = params(W)
    val, (a, b, ec) = nu(W)
    v = vcost(W)
    def tbest(x, y):
        m = (y - s * x) % K
        if x == 0 and y == 0:
            return Fr(1)
        return Fr(m, K) if 2 * m <= K else Fr(m - K, K)
    ok = [v[r] <= val for r in range(K)]
    # BFS b -> a using edges with |t|<=val
    prev = {b: None}; st = [b]
    while st:
        x = st.pop(0)
        if x == a:
            break
        for y in range(K):
            if ok[y] and y not in prev and abs(tbest(x, y)) <= val:
                prev[y] = x; st.append(y)
    path = [a]
    while path[-1] != b:
        path.append(prev[path[-1]])
    path.reverse()                      # b ... a
    verts = [a] + path                  # a -> b -> ... -> a
    if a == b:
        verts = [a, a]
    cyc = []
    for i in range(len(verts) - 1):
        x, y = verts[i], verts[i + 1]
        t = tbest(x, y) if i > 0 or not (x == 0 and y == 0) else Fr(1)
        if i == 0:
            t = ec if not (x == 0 and y == 0) else Fr(1)
            m = (y - s * x) % K
            t = (Fr(m, K) if 2 * m <= K else Fr(m - K, K)) if not (x == 0 and y == 0) else Fr(1)
        cyc.append((x, y, t))
    cost = max(max(abs(t) for _, _, t in cyc), max(v[y] for _, y, _ in cyc))
    assert cost == val, (W, cyc, cost, val)
    return val, cyc

def run_case(W, Aseq, a0, head, r0, rs, taus, label, kb, klo, khi):
    """rs[k-1]=r_k, taus[k-1]=tau_k for k=1..kb ; returns predicted and observed."""
    global fails
    l = len(W); K, c, cp, s = params(W); v = vcost(W); N = len(head)
    seq = [a0] + head
    for k in range(kb + 3):
        seq += [Aseq[k]] + W
    p = [1, seq[0]]; q = [0, 1]
    for a in seq[1:]:
        p.append(a * p[-1] + p[-2]); q.append(a * q[-1] + q[-2])
    digits = 2 * len(str(q[-1])) + 60
    mpmath.mp.dps = digits
    x = mpmath.mpf(0)
    for a in reversed(seq[1:]):
        x = 1 / (a + x)
    alpha = seq[0] + x
    P = lambda n: p[n + 1]; Q = lambda n: q[n + 1]
    eps = lambda n: Q(n) * alpha - P(n)
    nk = lambda k: N + (k - 1) * (l + 1)
    T = [int(K * t) for t in taus]
    for k in range(1, kb + 1):
        assert Fr(T[k-1], K) == taus[k-1]
        prv = r0 if k == 1 else rs[k - 2]
        assert (T[k-1] - (rs[k-1] - s * prv)) % K == 0
    Tp = list(T); Tp[0] = T[0] + s * (r0 % K)
    beta = sum(mpmath.mpf(Tp[k-1]) * abs(eps(nk(k))) for k in range(1, kb + 1)) / K
    def y(n):
        z = Q(n) * beta
        return z - mpmath.nint(z)
    maxerr = 0; maxlab = 0; maxt = 0
    pred = []
    for k in range(klo, khi + 1):
        th = [Q(nk(k) + i) * abs(eps(nk(k) + i)) for i in range(l + 1)]
        R = [abs(y(nk(k) + i)) / th[i] for i in range(l + 1)]
        Mk = max(R)
        pk = max(abs(taus[k-1]), v[rs[k-1]])
        pred.append(pk)
        maxerr = max(maxerr, abs(Mk - pk))
        if l >= 1:
            lab = int(mpmath.nint(K * y(nk(k) + 1))) % K
            if lab != rs[k-1] % K:
                maxlab += 1
        tk = Aseq[k-1] * y(nk(k))
        maxt = max(maxt, abs(tk - taus[k-1]))
    Amin = min(Aseq[klo - 2:khi + 1])
    Tmax = max(abs(t) for t in Tp)
    tol = 20 * (Tmax + 1) * K / Amin + 1e-9
    print('  %-28s W=%-12s K=%-3d pred limsup=%-6s  max|M_k-pred|=%.2e  label errors=%d  max|t_k-tau_k|=%.2e  (tol %.1e)'
          % (label, W, K, str(max(pred)), float(maxerr), maxlab, float(maxt), tol))
    chk(maxerr < tol and maxlab == 0 and maxt < tol, label + str(W))
    return max(pred), float(maxerr)

words = [[], [1], [2], [1, 1], [4], [3, 1], [2, 2], [5, 1, 5], [1, 9, 9], [1, 2, 1], [2, 1, 1, 2]]
regimes = {
    'fast A_k=1000+k': (lambda k: 1000 + k, 40, 30, 36),
    'slow A_k=k':      (lambda k: k,        260, 240, 250),
    'early 1s then 2^k': (lambda k: 1 if k <= 5 else 2 ** min(k, 40), 30, 22, 26),
}
print('=== Part A: optimal cycle (upper bound / attainment), several regimes ===')
for W in words:
    K, c, cp, s = params(W)
    val, cyc = best_cycle(W)
    L = len(cyc)
    for name, (Af, kb, klo, khi) in regimes.items():
        Aseq = [Af(k) for k in range(1, kb + 5)]
        r0 = cyc[-1][1]
        rs = [cyc[(k - 1) % L][1] for k in range(1, kb + 1)]
        taus = [cyc[(k - 1) % L][2] for k in range(1, kb + 1)]
        # check edge congruence
        for k in range(1, kb + 1):
            prv = r0 if k == 1 else rs[k - 2]
            chk((taus[k-1] - Fr(rs[k-1] - s * prv, K)).denominator == 1, 'edge congruence')
        head = [random.randint(1, 4) for _ in range(random.randint(0, 2))]
        pr, err = run_case(W, Aseq, random.randint(-2, 2), head, r0, rs, taus, name, kb, klo, khi)
        chk(pr == val, 'pred == nu')

print('=== Part B: random eventually periodic data (adversarial lower-bound direction) ===')
viol = 0; ncase = 0
for W in words:
    K, c, cp, s = params(W); v = vcost(W); nuW = nu(W)[0]
    for trial in range(6):
        per = random.randint(1, 4)
        cyc_r = [random.randrange(K) for _ in range(per)]
        cyc_t = []
        for m in range(per):
            prv = cyc_r[m - 1]
            base = Fr((cyc_r[m] - s * prv) % K, K)
            cyc_t.append(base + random.choice([-2, -1, 0, 0, 0, 1]))
        kb, klo, khi = 40, 30, 36
        r0 = random.randrange(K)
        rs = []; taus = []
        for k in range(1, kb + 1):
            if k <= 3:   # junk initial segment with large T
                rk = random.randrange(K); rs.append(rk)
                prv = r0 if k == 1 else rs[-2]
                taus.append(Fr((rk - s * prv) % K, K) + random.randint(-50, 50))
            else:
                m = k % per
                rk = cyc_r[m]; rs.append(rk)
                prv = rs[-2]
                base = Fr((rk - s * prv) % K, K)
                # adjust periodic tau to correct class (transition from junk)
                t = cyc_t[m]
                if (t - Fr(rk - s * prv, K)).denominator != 1:
                    t = base
                taus.append(t)
        Aseq = [1000 + k for k in range(1, kb + 5)]
        pr, err = run_case(W, Aseq, 0, [], r0, rs, taus, 'random periodic', kb, klo, khi)
        trivial = all(rs[k-1] == 0 and taus[k-1] == 0 for k in range(klo, khi + 1))
        ncase += 1
        if not trivial and pr < nuW:
            viol += 1; print('   LOWER BOUND VIOLATION', W, pr, nuW)
        if trivial:
            print('     (eventually trivial data: predicted K=0, beta should be a lattice point)')
chk(viol == 0, 'lower bound')
print('Part B: %d cases, lower-bound violations: %d' % (ncase, viol))
print('FAILS:', fails)
print('ALL CHECKS PASSED' if fails == 0 else 'SOME CHECKS FAILED')
