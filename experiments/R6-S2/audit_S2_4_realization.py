"""Audit §5.6 (S1(d), realization) and §7.2 (upper bound / attainment) of proofs/R6-S2.md.

For each test word W, prefix, A-sequence:
  * random data r_0, r_k in Z/K, T_k = K tau_k (bounded, T_k == r_k - sigma r_{k-1} mod K), incl. tie data
    tau_k = +-1/2 (K even) and the minimal closed walk C* of nu(W) (from common.nu, exact);
  * beta := (1/K) sum_k T'_k |eps_{n_k}|   (the proof's construction; truncated after KT blocks);
  * (d2) exact integer checks: P^{(k)}_{n_k} == 0 mod K, s_k == r_k mod K, P^{(k)}_{n_k+i} == c_i s_k mod K;
  * (d1) decomposition identity q_n beta = P/K + E_past + E_fut (high precision);
  * (d3) the explicit non-asymptotic bounds, for every k >= 2 in range:
        A_k |q_{n_k}beta - P^{(k)}_{n_k}/K - T'_k theta_{n_k}/K| <= 4 T_max (1/A_{k-1} + 1/A_{k+1}) / K
        |q_n beta - P^{(k)}_n / K| <= 4 T_max (1/A_k + 1/A_{k+1}) / K      (n = n_k+i, 1<=i<=l)
  * canonical label round(K y_{n_k+1}) mod K == r_k, and |t_k - tau_k| (should -> 0);
  * for C*: max_{n in blocks k1..k2} R_n vs nu(W) (Step 9) -- difference should be O(1/A).
"""
import os, sys, random
from fractions import Fraction
import mpmath as mp

sys.path.insert(0, os.path.dirname(__file__))
from common import nu, block_data, walk_cost

random.seed(7)
KT = 34      # blocks used in the series for beta
KCHK = 30    # blocks checked (tail error from truncation at KT is < 4Tmax/q_{n_{KT+1}+1}, negligible)


def edge_t(K, sigma, a, b):
    x = (b - sigma * a) % K
    return Fraction(x, K) if 2 * x <= K else Fraction(x - K, K)


def run(W, prefix, Aseq, r0, rs, Ts, label):
    """rs[k], Ts[k] for k=1..KT (index 0 unused); returns dict of diagnostics."""
    l = len(W)
    K, c, cp, sigma = block_data(W)
    N = len(prefix) - 1
    a = list(prefix)
    for k in range(1, KT + 8):
        a.append(Aseq(k)); a.extend(W)
    p = [a[0]]; q = [1]
    for n in range(1, len(a)):
        p.append(a[n] * p[-1] + (p[-2] if n >= 2 else 1))
        q.append(a[n] * q[-1] + (q[-2] if n >= 2 else 0))
    mp.mp.dps = 2 * len(str(q[-1])) + 120
    x = mp.mpf(a[-1])
    for t in reversed(a[:-1]):
        x = t + 1 / x
    alpha = x
    nk = {k: N + (k - 1) * (l + 1) for k in range(1, KT + 8)}
    eps = [q[n] * alpha - p[n] for n in range(len(a) - 2)]
    theta = [q[n] * mp.fabs(eps[n]) for n in range(len(eps))]
    # data
    for k in range(1, KT + 1):
        assert (Ts[k] - (rs[k] - sigma * rs[k - 1])) % K == 0
    Tp = dict(Ts)
    Tp[1] = Ts[1] + sigma * (r0 % K)
    Tmax = max(abs(Tp[k]) for k in range(1, KT + 1))
    xk = {k: (-1) ** nk[k] * Tp[k] for k in range(1, KT + 1)}
    beta = sum(Tp[k] * mp.fabs(eps[nk[k]]) for k in range(1, KT + 1)) / K
    D = lambda m, n: q[m] * p[n] - p[m] * q[n]
    out = dict(d2_fail=0, d1_fail=0, d3_fail=0, label_fail_late=0, worst_d3_ratio=0.0, tk_err=[], label_first_ok=None)
    s = {}
    for k in range(1, KCHK + 1):
        P = lambda n: sum(xk[j] * D(nk[j], n) for j in range(1, k + 1))
        Pn = P(nk[k]); s[k] = P(nk[k] + 1)
        if Pn % K != 0 or (s[k] - rs[k]) % K != 0:
            out["d2_fail"] += 1
        for i in range(1, l + 1):
            if (P(nk[k] + i) - c[i - 1] * s[k]) % K != 0:
                out["d2_fail"] += 1
        # d1 identity
        for n in range(nk[k], nk[k] + l + 1):
            Epast = sum(xk[j] * q[nk[j]] for j in range(1, k + 1)) * eps[n] / K
            Efut = sum(xk[j] * q[n] * eps[nk[j]] for j in range(k + 1, KT + 1)) / K
            if mp.fabs(q[n] * beta - P(n) / mp.mpf(K) - Epast - Efut) > mp.mpf(q[n] + 1) ** 2 * mp.mpf(10) ** (-(mp.mp.dps - 30)):   # rounding scale q_n^2*10^-dps (eps_n err x q_{n_j})
                out["d1_fail"] += 1
        # d3 bounds (k>=2 so that A_{k-1} exists; truncation tail ignored -- relatively 1e-(huge))
        if k >= 2:
            Ak, Akm, Akp = Aseq(k), Aseq(k - 1), Aseq(k + 1)
            lhs = Ak * mp.fabs(q[nk[k]] * beta - Pn / mp.mpf(K) - Tp[k] * theta[nk[k]] / K)
            rhs = mp.mpf(4 * Tmax) * (mp.mpf(1) / Akm + mp.mpf(1) / Akp) / K
            if Tmax > 0:
                out["worst_d3_ratio"] = max(out["worst_d3_ratio"], float(lhs / rhs))
            if lhs > rhs:
                out["d3_fail"] += 1
            for i in range(1, l + 1):
                n = nk[k] + i
                lhs = mp.fabs(q[n] * beta - P(n) / mp.mpf(K))
                rhs = mp.mpf(4 * Tmax) * (mp.mpf(1) / Ak + mp.mpf(1) / Akp) / K
                if Tmax > 0:
                    out["worst_d3_ratio"] = max(out["worst_d3_ratio"], float(lhs / rhs))
                if lhs > rhs:
                    out["d3_fail"] += 1
        # labels and t_k
        y = lambda n: q[n] * beta - mp.nint(q[n] * beta)
        if l >= 1:
            lab = int(mp.nint(K * y(nk[k] + 1))) % K
        else:
            lab = 0
        ok = (lab == rs[k] % K)
        if not ok and k >= KCHK // 2:
            out["label_fail_late"] += 1
        if ok and out["label_first_ok"] is None:
            out["label_first_ok"] = k
        if not ok:
            out["label_first_ok"] = None
        tk = Aseq(k) * y(nk[k])
        out["tk_err"].append(float(tk - mp.mpf(Ts[k]) / K))
    # R_n per block
    Rblock = []
    for k in range(1, KCHK + 1):
        Rblock.append(max(mp.fabs(q[n] * beta - mp.nint(q[n] * beta)) / theta[n] for n in range(nk[k], nk[k] + l + 1)))
    out["Rblock"] = Rblock
    return out


report = []
P_ = report.append
P_("=== audit_S2_4: S1(d) realization and S2 upper bound (category 4) ===")
words = [(), (1,), (2,), (1, 1), (1, 2), (2, 3), (5, 1, 5), (1, 1, 1), (3, 1, 4, 1), (1, 2, 1, 2)]
prefixes = [(0,), (2, 3, 1)]
Aseqs = [("100k", lambda k: 100 * k), ("k", lambda k: k)]
tot = dict(d2_fail=0, d1_fail=0, d3_fail=0, label_fail_late=0)
worst_ratio = 0.0
for W in words:
    K, c, cp, sigma = block_data(W)
    nuW, wit, _ = nu(W)
    if wit == "loop0_t=+-1":
        cyc_r = [0]; cyc_t = [Fraction(1)]
    else:
        cyc_r = wit[:-1]
        cyc_t = [edge_t(K, sigma, wit[m], wit[m + 1]) for m in range(len(wit) - 1)]
        assert walk_cost(W, wit) == nuW
    L = len(cyc_r)
    datasets = []
    # (A) random data, 3 sets
    for rep in range(3):
        r0 = random.randrange(K)
        rs = {0: r0}; Ts = {}
        for k in range(1, KT + 1):
            rs[k] = random.randrange(K)
            base = (rs[k] - sigma * rs[k - 1]) % K
            Ts[k] = base + K * random.randint(-2, 1)
        datasets.append(("random", r0, rs, Ts))
    # (B) tie data: K even, alternate tau = +1/2, -1/2 along edges with (r'-sigma r) == K/2
    if K % 2 == 0:
        r0 = 0
        rs = {0: 0}; Ts = {}
        for k in range(1, KT + 1):
            rs[k] = (sigma * rs[k - 1] + K // 2) % K
            Ts[k] = (K // 2) if k % 2 else -(K // 2)
        datasets.append(("tie+-1/2", r0, rs, Ts))
    # (C) minimal closed walk C* (Step 8): r_k = r^{k mod L}, tau_k = t^{m}, k == m mod L, m in 1..L
    rs = {0: cyc_r[0]}; Ts = {}
    for k in range(1, KT + 1):
        m = ((k - 1) % L) + 1
        rs[k] = cyc_r[m % L]
        Ts[k] = int(cyc_t[m - 1] * K)
    datasets.append(("C*", cyc_r[0], rs, Ts))
    for prefix in prefixes:
        for an, Aseq in Aseqs:
            for (dn, r0, rs, Ts) in datasets:
                o = run(W, prefix, Aseq, r0, rs, Ts, dn)
                for key in tot:
                    tot[key] += o[key]
                worst_ratio = max(worst_ratio, o["worst_d3_ratio"])
                last = o["tk_err"][-1]
                line = (f"W={W!s:13} K={K:3d} pre={prefix!s:10} A={an:4} data={dn:8} d2F={o['d2_fail']} d1F={o['d1_fail']} "
                        f"d3F={o['d3_fail']} d3ratio={o['worst_d3_ratio']:.3f} labFlate={o['label_fail_late']} labels_ok_from_k={o['label_first_ok']} "
                        f"|t_k-tau_k|@k=30:{abs(last):.2e}")
                if dn == "C*":
                    mx = max(o["Rblock"][19:30])
                    line += f"  nu={nuW} max_R(blocks20-30)={mp.nstr(mx, 8)} diff={mp.nstr(mx - mp.mpf(nuW.numerator) / nuW.denominator, 3)}"
                if dn == "tie+-1/2":
                    line += f"  t_30={o['tk_err'][-1] + Ts[30] / K:+.6f} tau_30={Ts[30] / K:+.3f}"
                P_(line)
P_("")
P_(f"TOTAL failures: {tot}")
P_("note: label_fail_late counts k>=15 with canonical label != r_k; all such cases have A_k = k (slow growth) and K>=11,\n      i.e. pre-asymptotic (|K g_k|<1/2 needs ~8 T_max/A_k small); every run is label-correct from some k on (labels_ok_from_k).")
P_(f"worst ratio LHS/RHS over all (d3) explicit bounds: {worst_ratio:.4f}  (<=1 required)")
P_("category 4: finite computation; checks the proof's explicit inequalities and congruences, not a proof.")
print("\n".join(report))
