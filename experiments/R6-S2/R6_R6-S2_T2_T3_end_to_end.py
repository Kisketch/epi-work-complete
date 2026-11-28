"""R6-S2 T2 (zero-jump, end to end), T2' (jump-walk realisation, skeptic addition), T3 (adversarial).

Spec: PLAN_GRAPH.md "当前主攻" T2/T3.  alpha_W = [0; A_1, W, A_2, W, ...], A_k = 10k, k <= 45.
R_n(beta) := ||q_n beta|| / theta_n.

T2 : beta_{a,b} = (a + b alpha)/K, (a,b) in [0,K)^2 \ {0}; finite-type := a q_{n_k} + b p_{n_k} == 0 mod K at all big
     indices of blocks 31..40; m2 := min over finite-type pairs of max_{n in blocks 31..40} R_n; compare with nu_0.
T2': (added by skeptic; T2 never exercises jump edges, which decide nu(W) < nu_0(W) for 5300/5890 words)
     beta = (1/K) sum_{k=k0}^{45} x_k eps_{n_k}, x_k = (-1)^{n_k} * centred(r_k - sigma r_{k-1} mod K), where (r_k)
     enters the nu-witness cycle at block k0=21 and then repeats it.  Labels give t_k = x_k(-1)^{n_k}/K.
     Measure max R_n over blocks 25..40; compare with nu(W).
T3 : beta = N_N / q_N, N_{n+1} = a_{n+1} N_n + N_{n-1} + m_n, N_{-1}=N_0=0, defects m_n in {-2..2} only at indices of
     blocks 31..38; N = last index of block 45.  Objective max_{n in blocks 30..40} R_n.
     (i) random sparse, density 0.02 / 0.1, 5000 samples each; (ii) hill climbing, 200 restarts (+ seeds from T2').
     MINOR FIX (skeptic): "defects not all zero" is replaced by "beta != 0" (N_N != 0): defect patterns of the form
     (1, -a_{j+2}, -1) at (j, j+1, j+2) give G-cancellation and beta = 0 exactly (trivial), whenever a_{j+2} <= 2.
Precision: dps D = 2 log10 q_{N+1} + 100; every reported value recomputed at 1.5 D; must agree to 1e-10.
"""
import sys, time, random
from fractions import Fraction
import numpy as np
import mpmath as mp
from common import nu, nu0, block_data, v_exact, edge_cost_exact
from cfdata import CF

t_start = time.time()
OUT = []
def P(s=""):
    OUT.append(s); print(s, flush=True)

SPEC_W = [(), (1,), (1, 1), (2,), (1, 1, 1), (2, 3), (5, 1, 5),       # E
          (5, 1, 1, 1, 5),                                          # T1 argmin over R1 u R2 (unique)
          (1, 2, 1, 2, 1, 2, 1, 2, 1)]                              # T1 argmin over R2 (first of 9)
EXTRA_W = [(2, 1, 3), (4, 1, 1, 1, 4)]                              # skeptic additions: jump-dominated / runner-up
WORDS = SPEC_W + EXTRA_W
SEED = 20261127
rng = np.random.default_rng(SEED)
random.seed(SEED)
TOL = 0.02
verdict_flags = []


def centred(x, K):
    x %= K
    return x - K if x > K // 2 else x   # tie K/2 -> +K/2 (cost identical)


def dist_mp(x):
    return abs(x - mp.nint(x))


def R_lattice_type(cf, a, b, K, ns, eps, th):
    """R_n for beta=(a+b alpha)/K with exact residues; mp context set by caller."""
    res = []
    for n in ns:
        rho = (a * cf.q[n] + b * cf.p[n]) % K
        val = (mp.mpf(rho) + b * eps[n]) / K
        res.append(dist_mp(val) / th[n])
    return res


for W in WORDS:
    tw = time.time()
    K, c, cp, sigma = block_data(W)
    l = len(W)
    nuW, wit, mstar = nu(W)
    n0, orb0, maxorb = nu0(W)
    cf = CF(W, kmax=45, ktail=60, scale=10)
    D = cf.dps
    D2 = int(1.5 * D)
    nmax = cf.N + 2
    E1, T1 = cf.eps_theta(D, nmax)
    E2, T2 = cf.eps_theta(D2, nmax)
    P("=" * 100)
    P(f"W={W} l={l} K={K} sigma={sigma} nu={nuW} ({float(nuW):.10f}) nu0={n0} witness={wit} "
      f"max sigma-orbit={maxorb} dps={D}/{D2} N={cf.N}")

    # ------------------------------------------------------------------ T2
    if K > 1:
        bigs = [cf.nk(k) for k in range(31, 41)]
        win2 = [n for k in range(31, 41) for n in cf.block(k)]
        pairs = [(a, b) for a in range(K) for b in range(K) if (a, b) != (0, 0)
                 and all((a * cf.q[n] + b * cf.p[n]) % K == 0 for n in bigs)]
        best = None
        with mp.workdps(D):
            for (a, b) in pairs:
                m = max(R_lattice_type(cf, a, b, K, win2, E1, T1))
                if best is None or m < best[0]:
                    best = (m, a, b)
        with mp.workdps(D2):
            m_hi = max(R_lattice_type(cf, best[1], best[2], K, win2, E2, T2))
        agree = abs(best[0] - m_hi) < mp.mpf("1e-10")
        # windowed zero-jump value (orbit restricted to the 10 measured blocks), exact
        r0 = (best[1] * cf.q[cf.nk(31) + 1] + best[2] * cf.p[cf.nk(31) + 1]) % K
        P(f"  T2: #finite-type pairs={len(pairs)} (expected K-1={K-1}); m2={mp.nstr(best[0], 15)} at (a,b)=({best[1]},{best[2]}), "
          f"label r_31={r0}; |m2-nu0|={mp.nstr(abs(best[0]-mp.mpf(n0.numerator)/n0.denominator), 6)}; "
          f"1.5x-precision agree<1e-10: {agree}; orbit<=10 blocks: {maxorb <= 10}")
        if abs(best[0] - mp.mpf(n0.numerator) / n0.denominator) > TOL:
            verdict_flags.append(f"T2 REFUTE-trigger W={W}")
        if not agree:
            verdict_flags.append(f"T2 INVALID precision W={W}")
    else:
        P("  T2: K=1, no pairs (a,b) != 0 in [0,1)^2 -- vacuous")

    # ------------------------------------------------------------------ T2' : realise the nu witness walk
    if wit == "loop0_t=+-1":
        cyc = [0, 0]; tvals = [K]       # loop at 0 with |t| = 1  -> x = +-K
    else:
        cyc = list(wit)
    k0 = 21
    labels = {k0 - 1: 0}
    seq = cyc[:-1]
    for i, k in enumerate(range(k0, 46)):
        labels[k] = seq[i % len(seq)]
    xs = {}
    for k in range(k0, 46):
        if wit == "loop0_t=+-1":
            T = K
        else:
            T = centred(labels[k] - sigma * labels[k - 1], K)
        xs[k] = (-1) ** cf.nk(k) * T
    a_big = -sum(xs[k] * cf.p[cf.nk(k)] for k in xs)
    b_big = sum(xs[k] * cf.q[cf.nk(k)] for k in xs)
    win2p = [n for k in range(25, 41) for n in cf.block(k)]
    with mp.workdps(D):
        Rv = R_lattice_type(cf, a_big, b_big, K, win2p, E1, T1)
        m1 = max(Rv)
    with mp.workdps(D2):
        m1b = max(R_lattice_type(cf, a_big, b_big, K, win2p, E2, T2))
    # predicted cost of the measured part (exact)
    pred = max([v_exact(W, labels[k]) for k in range(25, 41)] +
               [Fraction(abs(xs[k]), K) for k in range(25, 41)])
    # check labels actually realised: r_k := round(K * frac(q_{n_k+1} beta)) mod K must equal the walk label
    def label_at(k):
        n = cf.nk(k) + 1
        rho = (a_big * cf.q[n] + b_big * cf.p[n]) % K
        with mp.workdps(D):
            val = (mp.mpf(rho) + b_big * E1[n]) / K
            fr = val - mp.floor(val)
            return int(mp.nint(K * fr)) % K
    lab_ok = all(label_at(k) == labels[k] % K for k in range(25, 41))
    P(f"  T2': witness walk realised by beta=(1/K)sum x_k eps_(n_k); labels realised: {lab_ok}; "
      f"max R over blocks 25-40 = {mp.nstr(m1, 15)}; predicted (exact) = {pred} = {float(pred):.10f}; "
      f"|diff|={mp.nstr(abs(m1 - mp.mpf(pred.numerator)/pred.denominator), 6)}; 1.5x agree: {abs(m1-m1b) < mp.mpf('1e-10')}")
    if abs(m1 - mp.mpf(nuW.numerator) / nuW.denominator) > TOL or not lab_ok:
        verdict_flags.append(f"T2' mismatch W={W}")
    # actual defects of the T2' beta (for seeding T3): computed in blocks 31..38 only if all within [-2,2]

    # ------------------------------------------------------------------ T3
    N = cf.N
    qN = cf.q[N]
    a = cf.a
    # G_j = K(a_{j+2..N}) = N_N contribution of unit defect at j
    G = [0] * (N + 1)
    G[N - 1] = 1
    G[N - 2] = a[N]
    for j in range(N - 3, -1, -1):
        G[j] = a[j + 2] * G[j + 1] + G[j + 2]
    dpos = [n for k in range(31, 39) for n in cf.block(k)]
    win3 = [n for k in range(30, 41) for n in cf.block(k)]
    Pd, Nw = len(dpos), len(win3)
    SC = 1 << 64
    f = np.empty((Nw, Pd))
    for i, n in enumerate(win3):
        for j, jj in enumerate(dpos):
            f[i, j] = ((cf.q[n] * G[jj]) % qN) * SC // qN / SC
    thf = np.array([float(T1[n]) for n in win3])

    def evalR(M):  # M: Pd x S integer matrix -> maxR (S,)
        Y = f @ M
        Dd = np.abs(Y - np.round(Y))
        return (Dd / thf[:, None]).max(axis=0)

    def exact_maxR(m, dps, TT):
        NN = sum(int(mi) * G[jj] for mi, jj in zip(m, dpos) if mi)
        if NN == 0:
            return None
        with mp.workdps(dps):
            vals = []
            for n in win3:
                rnum = (cf.q[n] * NN) % qN
                d = min(rnum, qN - rnum)
                vals.append(mp.mpf(d) / qN / TT[n])
            return max(vals)

    nuf = float(nuW)
    gmin = (np.inf, None)
    viol = []
    # (i) random sparse
    for dens in (0.02, 0.1):
        S = 5000
        mask = rng.random((Pd, S)) < dens
        vals = rng.choice(np.array([-2, -1, 1, 2]), size=(Pd, S))
        M = np.where(mask, vals, 0)
        nz = M.any(axis=0)
        r = evalR(M)
        r[~nz] = np.inf
        # exact screening of tiny / small values
        small = np.nonzero(r < nuf - TOL + 1e-6)[0]
        nzero_beta = 0
        for s in small:
            ex = exact_maxR(M[:, s], D, T1)
            if ex is None:
                nzero_beta += 1; r[s] = np.inf; continue
            if ex < nuW - Fraction(1, 50):
                viol.append((W, "random", dens, M[:, s].tolist(), ex))
        i = int(np.argmin(r))
        P(f"  T3(i) density {dens}: #samples={S}, #nonzero={int(nz.sum())}, #beta==0 excluded={nzero_beta}, "
          f"min maxR={r[i]:.10f}, #below nu-0.02 (exact)={sum(1 for v in viol if v[1]=='random' and v[2]==dens)}")
        if r[i] < gmin[0]:
            gmin = (r[i], M[:, i].copy())
    # seed from T2' beta: actual round-defects of beta_T2' restricted to window (if representable)
    # (i') exhaustive small support: all patterns with 1..SUPP nonzero defects (values +-1, +-2)
    import itertools
    SUPP = 3 if Pd <= 48 else 2
    vals4 = [-2, -1, 1, 2]
    ex_best = (np.inf, None); ex_count = 0
    for s_ in range(1, SUPP + 1):
        cols = []
        for pos in itertools.combinations(range(Pd), s_):
            for vv in itertools.product(vals4, repeat=s_):
                mm = np.zeros(Pd, dtype=np.int64); mm[list(pos)] = vv
                cols.append(mm)
                if len(cols) == 20000:
                    Mx = np.stack(cols, axis=1); cols = []
                    r = evalR(Mx); r[r < 1e-9] = np.inf; ex_count += Mx.shape[1]
                    k_ = int(np.argmin(r))
                    if r[k_] < ex_best[0]: ex_best = (r[k_], Mx[:, k_].copy())
        if cols:
            Mx = np.stack(cols, axis=1)
            r = evalR(Mx); r[r < 1e-9] = np.inf; ex_count += Mx.shape[1]
            k_ = int(np.argmin(r))
            if r[k_] < ex_best[0]: ex_best = (r[k_], Mx[:, k_].copy())
    exv = exact_maxR(ex_best[1], D, T1)
    if exv is not None and exv < mp.mpf(nuW.numerator) / nuW.denominator - TOL:
        viol.append((W, "exhaustive", SUPP, ex_best[1].tolist(), exv))
    P(f"  T3(i') exhaustive support<= {SUPP}: #patterns={ex_count}, min maxR={ex_best[0]:.10f}")
    if ex_best[0] < gmin[0]:
        gmin = ex_best

    # seeds: closed excursion 0 -> (nu-witness cycle repeated, blocks 31..37) -> 0 at block 38, realised as
    # beta=(1/K) sum x_k eps_{n_k} (a lattice element), converted to round-defects; kept if supported in blocks
    # 31..38 with values in [-2,2].
    seeds = []
    with mp.workdps(D):
        alpha_mp = mp.mpf(0)
        for m_ in range(cf.M, 0, -1):
            alpha_mp = 1 / (cf.a[m_] + alpha_mp)
        alpha_mp = cf.a[0] + alpha_mp
        for shift in range(len(seq)):
            labs = {30: 0}
            for k in range(31, 38):
                labs[k] = seq[(k - 31 + shift) % len(seq)] if wit != "loop0_t=+-1" else 0
            labs[38] = 0
            xk = {}
            for k in range(31, 39):
                T = (K if (wit == "loop0_t=+-1" and k < 38) else centred(labs[k] - sigma * labs[k - 1], K))
                xk[k] = (-1) ** cf.nk(k) * T
            bet = sum(xk[k] * E1[cf.nk(k)] for k in xk) / K
            rnd = [int(mp.nint(cf.q[n] * bet)) for n in range(0, N + 1)]
            dfc = {n: rnd[n + 1] - cf.a[n + 1] * rnd[n] - (rnd[n - 1] if n >= 1 else 0) for n in range(0, N)}
            supp = {n: d for n, d in dfc.items() if d != 0}
            okseed = all(n in dpos for n in supp) and all(-2 <= d <= 2 for d in supp.values()) and supp
            if okseed:
                mm = np.zeros(Pd, dtype=np.int64)
                for n, d in supp.items():
                    mm[dpos.index(n)] = d
                seeds.append(mm)
            else:
                P(f"     seed shift {shift}: not representable (support/range) -> skipped; "
                  f"support blocks {sorted(set((n)//(l+1)+1 for n in supp))[:6]}, max|d|={max([abs(d) for d in supp.values()] or [0])}")
    if seeds:
        rs_ = evalR(np.stack(seeds, axis=1))
        P(f"  T3 seeds from nu-witness closed excursions: {len(seeds)}; their maxR = {np.round(rs_, 8).tolist()}")

    # (ii) hill climbing on smoothed minimax objective (p-norm, p=40), 200 random sparse restarts + seeds
    deltas = np.array([-4, -3, -2, -1, 1, 2, 3, 4])

    def objective(M):
        Y = f @ M
        Dd = np.abs(Y - np.round(Y))
        Rm = Dd / thf[:, None]
        mx = Rm.max(axis=0)
        bad = mx < 1e-9                  # beta == 0 (trivial) -> excluded (checked exactly afterwards)
        mxs = np.where(bad, 1.0, mx)
        pn = mxs * (((Rm / mxs) ** 40).sum(axis=0)) ** (1 / 40)
        pn[bad] = np.inf
        return pn

    RESTARTS = 200
    hc_best = (np.inf, None)
    starts = []
    for rs in range(RESTARTS):
        nnz = int(rng.integers(1, 6))
        m = np.zeros(Pd, dtype=np.int64)
        m[rng.choice(Pd, size=nnz, replace=False)] = rng.choice(np.array([-2, -1, 1, 2]), size=nnz)
        starts.append(m)
    starts += seeds
    for m in starts:
        m = m.copy()
        cur = objective(m[:, None])[0]
        for it in range(400):
            cand = np.repeat(m[:, None], Pd * len(deltas), axis=1)
            jj = np.repeat(np.arange(Pd), len(deltas))
            dd = np.tile(deltas, Pd)
            newv = m[jj] + dd
            ok = (newv >= -2) & (newv <= 2)
            cand[jj, np.arange(cand.shape[1])] = newv
            cand = cand[:, ok]
            ob = objective(cand)
            k = int(np.argmin(ob))
            if ob[k] < cur - 1e-12:
                cur = ob[k]; m = cand[:, k].copy()
            else:
                break
        mx = evalR(m[:, None])[0]
        if 1e-9 < mx < hc_best[0]:
            hc_best = (mx, m.copy())
    if hc_best[0] < gmin[0]:
        gmin = hc_best
    # exact recomputation of overall best sample at D and 1.5D
    exD = exact_maxR(gmin[1], D, T1)
    exD2 = exact_maxR(gmin[1], D2, T2)
    agree3 = exD is not None and abs(exD - exD2) < mp.mpf("1e-10")
    if exD is not None and exD < mp.mpf(nuW.numerator) / nuW.denominator - TOL:
        viol.append((W, "hill", None, gmin[1].tolist(), exD))
    # A-scaling diagnostic: same defect pattern (same block positions) with A_k = 100k, 1000k
    scal = []
    for sc in (100, 1000):
        cfs = CF(W, kmax=45, ktail=60, scale=sc)
        Es, Ts = cfs.eps_theta(cfs.dps, cfs.N + 2)
        Gs = [0] * (cfs.N + 1); Gs[cfs.N - 1] = 1; Gs[cfs.N - 2] = cfs.a[cfs.N]
        for j in range(cfs.N - 3, -1, -1):
            Gs[j] = cfs.a[j + 2] * Gs[j + 1] + Gs[j + 2]
        NN = sum(int(mi) * Gs[jj] for mi, jj in zip(gmin[1], dpos) if mi)
        with mp.workdps(cfs.dps):
            vv = []
            for n in win3:
                rn = (cfs.q[n] * NN) % cfs.q[cfs.N]
                vv.append(mp.mpf(min(rn, cfs.q[cfs.N] - rn)) / cfs.q[cfs.N] / Ts[n])
            scal.append(max(vv))
    P(f"  T3 A-scaling of best pattern: maxR at A_k=10k/100k/1000k = {mp.nstr(exD, 10)} / {mp.nstr(scal[0], 10)} / {mp.nstr(scal[1], 10)}")
    P(f"  T3(ii) hill-climb: {RESTARTS} restarts, best maxR (float) = {hc_best[0]:.10f}")
    P(f"  T3 overall min maxR = {mp.nstr(exD, 15)} (exact beta, dps {D}); 1.5x agree: {agree3}; "
      f"nu - min = {mp.nstr(mp.mpf(nuW.numerator)/nuW.denominator - exD, 8)}; "
      f"#nonzero defects in best={int((gmin[1]!=0).sum())}")
    if viol:
        verdict_flags.append(f"T3 REFUTE-trigger W={W}: {len(viol)} samples")
        for v in viol[:3]:
            P(f"     VIOLATION {v[1]} maxR={mp.nstr(v[4], 12)} defects={v[3]}")
    if not agree3:
        verdict_flags.append(f"T3 INVALID precision W={W}")
    P(f"  ({time.time()-tw:.1f}s)")

P("=" * 100)
P(f"flags: {verdict_flags if verdict_flags else 'none'}")
P(f"total elapsed {time.time()-t_start:.1f}s")
with open("R6_R6-S2_T2_T3_end_to_end.out", "w") as fh:
    fh.write("\n".join(OUT) + "\n")
