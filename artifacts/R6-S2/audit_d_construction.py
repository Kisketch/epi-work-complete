# audit_d_construction.py -- skeptic audit of paper_draft.tex Subsection "Proof of (d)" (lines 673-762)
# Checks the condensed (d2) congruences with the renamed \hat s_k = P^{(k)}_{n_k+1}, and every "<=" bound of (d3),
# including the degenerate cases T'_max = 0 (beta = 0) where the source's strict inequalities fail.
# Exact integer arithmetic for P^{(k)}, D(m,n); mpmath (dps 1500) for eps_n.  Category 4 (finite check).
import random
import mpmath as mp
mp.mp.dps = 1500

def cont(w):
    a, b = 1, 0
    for x in w: a, b = x * a + b, a
    return a

def build(a0, pre, W, A):          # partial quotients a_0, a_1..a_N, A_1, W, A_2, W, ...
    a = [a0] + list(pre)
    for Ak in A: a += [Ak] + list(W)
    return a

def run_case(a0, pre, W, A, r, tau_int, label):
    l = len(W); K = cont(W); N = len(pre)
    sig = cont(W[:l - 1]) if l >= 1 else 1
    a = build(a0, pre, W, A)
    M = len(a)
    p = [1, a0]; q = [0, 1]                      # p[i] = p_{i-1}
    for n in range(1, M): p.append(a[n] * p[-1] + p[-2]); q.append(a[n] * q[-1] + q[-2])
    P = lambda n: p[n + 1]; Qn = lambda n: q[n + 1]
    x = mp.mpf(a[-1])
    for c in reversed(a[:-1]): x = c + 1 / x     # alpha (tail truncated far beyond tested indices)
    eps = lambda n: Qn(n) * x - P(n)
    nk = lambda k: N + (k - 1) * (l + 1)
    kmax = len(A) - 3
    # data: r_0..r_kmax in Z/K, T_k = K tau_k integers with T_k = r_k - sig r_{k-1} mod K
    T = {k: tau_int[k] for k in range(1, kmax + 1)}
    for k in T: assert (T[k] - (r[k] - sig * r[k - 1])) % K == 0
    r0t = r[0] % K
    Tp = dict(T); Tp[1] = T[1] + sig * r0t
    Tmax = max(max(abs(t) for t in T.values()), abs(Tp[1]))
    xk = {k: (-1) ** nk(k) * Tp[k] for k in Tp}
    beta = sum(xk[k] * eps(nk(k)) for k in Tp) / K
    D = lambda m, n: Qn(m) * P(n) - P(m) * Qn(n)
    fails = []
    def chk(cond, msg):
        NCHK[0] += 1
        if not cond: fails.append(msg)
    for k in range(1, kmax - 1):
        Pk = lambda n: sum(xk[j] * D(nk(j), n) for j in range(1, k + 1))
        shat = Pk(nk(k) + 1)
        chk(Pk(nk(k)) % K == 0, f"(d2)(i) k={k}")
        chk((shat - r[k]) % K == 0, f"(d2)(ii) k={k}")
        for i in range(1, l + 1):
            chk((Pk(nk(k) + i) - cont(W[:i - 1]) * shat) % K == 0, f"(d2) P_(nk+i)=c_i shat k={k} i={i}")
        Ak, Ak1 = A[k - 1], A[k]
        # (d1) exact decomposition at n in block k
        for n in range(nk(k), nk(k) + l + 1):
            Epast = sum(xk[j] * Qn(nk(j)) for j in range(1, k + 1)) * eps(n) / K
            Efut = sum(xk[j] * Qn(n) * eps(nk(j)) for j in Tp if j > k) / K
            chk(abs(Qn(n) * beta - (Pk(n) / mp.mpf(K) + Epast + Efut)) < mp.mpf(10) ** -1200, f"(d1) k={k} n={n}")
            if n > nk(k):
                chk(K * abs(Epast) <= 4 * Tmax * mp.mpf(Qn(nk(k))) / Qn(n + 1) + 0, f"Epast1 k={k}")
                chk(4 * Tmax * mp.mpf(Qn(nk(k))) / Qn(n + 1) <= 4 * Tmax * mp.mpf(Qn(nk(k))) / Qn(nk(k) + 1), f"Epast2 k={k}")
                chk(4 * Tmax * mp.mpf(Qn(nk(k))) / Qn(nk(k) + 1) <= mp.mpf(4 * Tmax) / Ak, f"Epast3 k={k}")
                chk(K * abs(Efut) <= mp.mpf(4 * Tmax) / Ak1, f"Efut k={k}")
        # index n_k
        n = nk(k)
        rest = sum(xk[j] * Qn(nk(j)) for j in range(1, k)) * eps(n)
        chk(abs(xk[k] * Qn(n) * eps(n) - Tp[k] * Qn(n) * abs(eps(n))) < mp.mpf(10) ** -1200, f"first term k={k}")
        if k >= 2:
            chk(abs(rest) <= 4 * Tmax * mp.mpf(Qn(nk(k - 1))) / Qn(n + 1), f"rest<=4T q/q k={k}")
            chk(Ak * abs(rest) <= mp.mpf(4 * Tmax) / A[k - 2], f"A_k rest <= 4T/A_(k-1) k={k}")
        else:
            chk(rest == 0, "k=1 empty sum")
        Efut = sum(xk[j] * Qn(n) * eps(nk(j)) for j in Tp if j > k) / K
        chk(Ak * K * abs(Efut) <= mp.mpf(4 * Tmax) / Ak1, f"A_k K Efut k={k}")
        # hat g_k bound (l>=1)
        if l >= 1:
            m = n + 1
            ghat = (sum(xk[j] * Qn(nk(j)) for j in range(1, k + 1)) * eps(m) + sum(xk[j] * Qn(m) * eps(nk(j)) for j in Tp if j > k)) / K
            chk(K * abs(ghat) <= mp.mpf(4 * Tmax) / Ak + mp.mpf(4 * Tmax) / Ak1, f"|K ghat| k={k}")
            if K * abs(ghat) < mp.mpf(1) / 2:
                lab = int(mp.nint(K * (Qn(m) * beta - mp.nint(Qn(m) * beta))))
                chk((lab - r[k]) % K == 0, f"label k={k}")
    # t_k - tau_k at the end
    k = kmax - 3; n = nk(k)
    y = Qn(n) * beta - mp.nint(Qn(n) * beta)
    tk = A[k - 1] * y
    return fails, Tmax, max(abs(t) for t in Tp.values()), float(tk - mp.mpf(T[k]) / K), beta

NCHK = [0]
random.seed(7)
tot = 0; allfails = []
cases = []
for W in [(), (1,), (1, 1), (2, 3), (5, 1, 5), (1, 2, 1), (3, 1, 3)]:
    for trial in range(3):
        K = cont(W); l = len(W); sig = cont(W[:l - 1]) if l >= 1 else 1
        A = [10 * k + random.randint(0, 5) for k in range(1, 16)]
        kmax = len(A) - 3
        r = [random.randrange(K) for _ in range(kmax + 1)]
        tau = [None] + [((r[k] - sig * r[k - 1]) % K) + K * random.randint(-1, 1) for k in range(1, kmax + 1)]
        cases.append((W, A, r, tau, f"random W={W} trial {trial}"))
    # degenerate: r_k = 0 for all k>=1, r_0 arbitrary, T_1 = -sig*r0, T_k = 0 (k>=2) -> T'_max = 0, beta = 0
    K = cont(W); l = len(W); sig = cont(W[:l - 1]) if l >= 1 else 1
    A = [10 * k for k in range(1, 16)]; kmax = len(A) - 3
    r0 = K - 1 if K > 1 else 0
    r = [r0] + [0] * kmax
    tau = [None, -sig * r0] + [0] * (kmax - 1)
    cases.append((W, A, r, tau, f"degenerate T'_max=0, T_max={sig*r0} W={W}"))
    cases.append((W, A, [0] * (kmax + 1), [None] + [0] * kmax, f"degenerate T_max=0 (all data zero) W={W}"))
for W, A, r, tau, lab in cases:
    fails, Tmax, Tpmax, last, beta = run_case(0, [1, 2], W, A, r, tau, lab)
    tot += 1
    print(f"{lab}: Tmax={Tmax} T'max={Tpmax} beta={mp.nstr(beta,5)} t_k-tau_k(k=kmax-3)={last:.3e} fails={fails[:3]}")
    allfails += fails
print(f"cases={tot}; checks executed={NCHK[0]}; total failed checks={len(allfails)}")
