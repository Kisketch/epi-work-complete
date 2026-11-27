"""Audit §5.2-5.4 (S1(b)) and §7.1 Steps 2-7 (lower bound) of proofs/R6-S2.md on beta's that are NOT
produced by the label model: beta := (1/D) sum_k sum_{(i,x) in pattern[k mod P]} x * eps_{n_k+i}
(defects at arbitrary in-block positions i in 0..l, arbitrary denominator D in 1..2K, period P in 1..3).

For each beta (A_k = 1000k, prefix (0,)):
  * canonical labels r_k = round(K y_{n_k+1}) mod K, t_k = A_k y_{n_k};
  * S1(b): max over late k of | |y_{n_k+i}| - d_K(c_i r_k)/K |  and  dist(t_{k+1}-(r_{k+1}-sigma r_k)/K, Z);
  * Step 3: max over late k of |M_k - max(|t_k|, v(r_k))|;
  * Step 4: tau_k = nearest point of (r_k - sigma r_{k-1})/K + Z to t_k; edges e_k;
  * Step 5-7: find k<k' in the window with e_k = e_k' and the walk e_k..e_{k'-1} non-trivial; compute its
    EXACT cost (Fractions) and check  nu(W) <= cost  and  cost <= max_window R_n + delta  (delta = 0.01);
  * Step 6: if every edge in the late window is the trivial loop, check that beta is a lattice point
    (here: all coefficients x vanish after dividing by D, i.e. D | x for all x -- otherwise flag).
Category 4 (finite computation).
"""
import os, sys, random
from fractions import Fraction
import mpmath as mp

sys.path.insert(0, os.path.dirname(__file__))
from common import nu, block_data, v_exact

random.seed(11)
KB = 30          # blocks in alpha used
WIN = range(12, 27)


def setup(W):
    l = len(W)
    a = [0]
    for k in range(1, KB + 8):
        a.append(1000 * k); a.extend(W)
    p = [a[0]]; q = [1]
    for n in range(1, len(a)):
        p.append(a[n] * p[-1] + (p[-2] if n >= 2 else 1))
        q.append(a[n] * q[-1] + (q[-2] if n >= 2 else 0))
    mp.mp.dps = 2 * len(str(q[-1])) + 120
    x = mp.mpf(a[-1])
    for t in reversed(a[:-1]):
        x = t + 1 / x
    eps = [q[n] * x - p[n] for n in range(len(a) - 2)]
    theta = [q[n] * mp.fabs(eps[n]) for n in range(len(eps))]
    nk = {k: (k - 1) * (l + 1) for k in range(1, KB + 8)}
    return a, p, q, eps, theta, nk


def edge_cost(t):
    return abs(t)


stats = dict(betas=0, finiteK_like=0, b1_worst=0.0, coup_worst=0.0, step3_worst=0.0, walks=0,
             nu_gt_cost=0, cost_gt_R=0, trivial_only=0, trivial_only_nonlattice=0, no_repeat=0)
lines = []
for W in [(), (1,), (2,), (1, 1), (1, 2), (2, 3), (5, 1, 5), (3, 1, 4, 1), (1, 2, 1, 2)]:
    l = len(W)
    K, c, cp, sigma = block_data(W)
    nuW = nu(W)[0]
    a, p, q, eps, theta, nk = setup(W)
    for trial in range(400):
        P = random.randint(1, 3)
        D = random.choice([K, K, K, 2 * K, max(1, K // 2), random.randint(1, 2 * K)])
        pattern = []
        for _ in range(P):
            pat = []
            for i in range(0, l + 1):
                if random.random() < 0.6:
                    pat.append((i, random.randint(-2 * D, 2 * D)))
            pattern.append(pat)
        beta = mp.mpf(0)
        allx = []
        for k in range(1, KB + 1):
            for (i, xx) in pattern[k % P]:
                beta += xx * eps[nk[k] + i]
                allx.append(xx)
        beta /= D
        stats["betas"] += 1
        y = lambda n: q[n] * beta - mp.nint(q[n] * beta)
        R = lambda n: mp.fabs(y(n)) / theta[n]
        r, t, M = {}, {}, {}
        # finite-K filter (the lower bound is only non-trivial for K < infinity, Step 1):
        # R_{n_k} ~ A_k * dist(P/D, Z) blows up otherwise; keep beta only if max_window R <= 3
        if max(R(n) for n in range(nk[WIN[0]], nk[WIN[-1] + 1] + l + 1)) > 3:
            continue
        stats["finiteK_like"] += 1
        for k in list(WIN) + [WIN[-1] + 1]:
            r[k] = int(mp.nint(K * y(nk[k] + 1))) % K if l >= 1 else 0
            t[k] = 1000 * k * y(nk[k])
            M[k] = max(R(n) for n in range(nk[k], nk[k] + l + 1))
        # S1(b) first item and coupling, Step 3
        for k in WIN:
            for i in range(1, l + 1):
                d = min((c[i - 1] * r[k]) % K, K - (c[i - 1] * r[k]) % K)
                stats["b1_worst"] = max(stats["b1_worst"], float(mp.fabs(mp.fabs(y(nk[k] + i)) - mp.mpf(d) / K)))
            if k + 1 in r:
                z = t[k + 1] - mp.mpf((r[k + 1] - sigma * r[k]) % K) / K
                stats["coup_worst"] = max(stats["coup_worst"], float(mp.fabs(z - mp.nint(z))))
            vk = v_exact(W, r[k])
            stats["step3_worst"] = max(stats["step3_worst"],
                                       float(mp.fabs(M[k] - max(mp.fabs(t[k]), mp.mpf(vk.numerator) / vk.denominator))))
        # Step 4: edges
        E = {}
        for k in list(WIN)[1:]:
            base = Fraction((r[k] - sigma * r[k - 1]) % K, K)
            tau = base + int(mp.nint(t[k] - mp.mpf(base.numerator) / base.denominator))
            E[k] = (r[k - 1], r[k], tau)
        ks = sorted(E)
        maxR = max(M[k] for k in ks)
        trivial = lambda e: e[0] == 0 and e[1] == 0 and e[2] == 0
        if all(trivial(E[k]) for k in ks):
            stats["trivial_only"] += 1
            if any(xx % D for xx in allx):
                stats["trivial_only_nonlattice"] += 1
                lines.append(f"  TRIVIAL-ONLY but coefficients not divisible by D: W={W} D={D} pattern={pattern}")
            continue
        # Step 5-7 (finite form): latest k' with an earlier k, e_k = e_k', walk non-trivial
        found = None
        for kp in reversed(ks):
            for kk in ks:
                if kk < kp and E[kk] == E[kp]:
                    walk = [E[j] for j in range(kk, kp)]
                    if not all(trivial(e) for e in walk):
                        found = walk
                        break
            if found:
                break
        if not found:
            stats["no_repeat"] += 1
            continue
        stats["walks"] += 1
        # closedness check
        assert found[0][0] == found[-1][1]
        for e1, e2 in zip(found[:-1], found[1:]):
            assert e1[1] == e2[0]
        cost = max(max(v_exact(W, e[0]), v_exact(W, e[1]), abs(e[2])) for e in found)
        if nuW > cost:
            stats["nu_gt_cost"] += 1
            lines.append(f"  NU > COST: W={W} nu={nuW} cost={cost} walk={found}")
        if mp.mpf(cost.numerator) / cost.denominator > maxR + mp.mpf("0.01"):
            stats["cost_gt_R"] += 1
            lines.append(f"  COST > maxR: W={W} cost={cost} maxR={mp.nstr(maxR, 8)}")
print("=== audit_S2_5: S1(b) and lower-bound Steps 2-7 on beta outside the label model (A_k=1000k) ===")
for k, v in stats.items():
    print(f"{k}: {v}")
print("b1_worst = max | |y_{n_k+i}| - d_K(c_i r_k)/K |, coup_worst = max dist(t_{k+1}-(r_{k+1}-sigma r_k)/K, Z),")
print("step3_worst = max |M_k - max(|t_k|, v(r_k))|  over blocks 12..26 (all should be O(1/A_k) ~ 1e-4..1e-2)")
print("no_repeat = windows in which no edge repeats (Step 7 needs infinitely many blocks; skipped, not a failure)")
for x in lines[:20]:
    print(x)
print("category 4: finite computation, not a proof.")
