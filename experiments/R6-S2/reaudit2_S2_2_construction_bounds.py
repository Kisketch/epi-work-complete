"""reaudit2 (R6-S2 after repair round 2) -- self-written by the isolated skeptic.

Adversarial check of proofs/R6-S2.md sec 5.6 (d1)-(d4) and sec 8:
  * (d1) exact decomposition q_n beta = P^(k)_n/K + E^past_n + E^fut_n
  * (d2) P^(k)_{n_k} = 0, s_k = r_k, P^(k)_{n_k+i} = c_i s_k   (mod K), exact integers
  * (d3) every displayed bound, with T := T'_max = sup|T'_k| (the (tau') form) and with
         T := K tau_max + sigma (K-1) (the (tau) form); also the WRONG form 8 K tau_max/min(A_k,A_{k+1})
  * g'_k: |K g'_k| <= 4T/A_k + 4T/A_{k+1} <= 8T/min(A_k,A_{k+1});
         |K g'_k| < 1/2  ==>  canonical label r_k(beta) == given r_k   (sufficiency)
  * t_k - tau_k identity of (d3)
  * Lemma B: 1/theta_{n_k} in (A_k, A_k+2)
  * (E1)-(E4) of sec 8, tested with C := max of the R_n that the derivation actually uses
    (C <= K+1 for k >= k_0, so passing with C implies passing with K+1), on constructed beta,
    lattice-shifted beta, random beta and "digit" beta = (1/K') sum_n z_n eps_n.
Extreme inputs: r_0 = K-1, large |T_k|, slowly growing / constant / erratic A_k, W in {(),(1),(2),(1,1),
(1,9,9),(9,9,9),Fibonacci words,(5,1,5),...}.

Numerics: mpmath with dps ~ 2 log10 q_M + 80; alpha from the CF truncated at index M (error < 1/q_M^2);
beta series truncated at block KB (tail <= 4T/(K q_{n_{KB+1}+1})).  Every inequality is reported with its
margin; a margin below TOL is reported as 'INDETERMINATE' (never silently passed).
"""
import math, random, sys
import mpmath as mp

random.seed(20261127)

def cont(ws):
    a, b = 0, 1
    for w in ws:
        a, b = b, w * b + a
    return b

def Kint(W, a, b):  # K_[a,b], 1-based, length b-a+1 ; b=a-1 ->1 ; b=a-2 ->0
    if b == a - 2: return 0
    if b == a - 1: return 1
    return cont(W[a - 1:b])

def dK(x, K):
    x %= K
    return min(x, K - x)

class Inst:
    def __init__(self, W, A, head=(0,), KT=None):
        self.W = tuple(W); l = self.l = len(W)
        self.K = cont(W)
        self.c = [cont(W[:i - 1]) for i in range(1, l + 1)]
        self.cp = [cont(W[i:]) for i in range(1, l + 1)]
        self.sigma = self.c[-1] if l >= 1 else 1
        self.A = list(A)                     # A[k-1] = A_k
        a = list(head)                       # a_0..a_N
        self.N = len(head) - 1
        for Ak in self.A:
            a.append(Ak); a.extend(W)
        self.a = a; M = self.M = len(a) - 1
        p = [a[0]]; q = [1]; pm, qm = 1, 0
        for n in range(1, M + 1):
            p.append(a[n] * p[-1] + (p[-2] if n >= 2 else pm))
            q.append(a[n] * q[-1] + (q[-2] if n >= 2 else qm))
        self.p, self.q = p, q
        mp.mp.dps = int(2 * math.log10(q[M]) + 80)
        x = mp.mpf(a[M])
        for n in range(M - 1, -1, -1):
            x = a[n] + 1 / x
        self.alpha = x
        self.eps = [q[n] * x - p[n] for n in range(M + 1)]
        self.theta = [q[n] * abs(self.eps[n]) for n in range(M + 1)]
        self.KB = len(self.A)                # number of blocks present
        self.alpha_err = mp.mpf(1) / mp.mpf(q[M]) ** 2

    def nk(self, k):
        return self.N + (k - 1) * (self.l + 1)

    def qm1(self, n):
        return self.q[n - 1] if n >= 1 else 0

    def D(self, m, n):  # D(m,n) = q_m p_n - p_m q_n ; n=-1 allowed
        if n == -1: return self.q[m]
        return self.q[m] * self.p[n] - self.p[m] * self.q[n]

TOL = mp.mpf(10) ** -40
stats = {'checks': 0, 'viol': 0, 'indet': 0}
viol_list = []

def chk(name, lhs, rhs, strict=False, ctx=''):
    """record lhs <= rhs (or <)."""
    stats['checks'] += 1
    m = rhs - lhs
    # tolerance: absolute TOL, or relative 1e-25 of the compared magnitudes (working precision is
    # >= 80 digits beyond 2 log10 q_M, so relative numerical error is far below 1e-25)
    tol = mp.mpf(10) ** -25 * max(abs(lhs), abs(rhs))
    if m < -tol:
        stats['viol'] += 1
        viol_list.append((name, ctx, mp.nstr(lhs, 12), mp.nstr(rhs, 12)))
        return False
    if strict and abs(m) <= tol:
        stats['indet'] += 1
        viol_list.append(('INDET ' + name, ctx, mp.nstr(lhs, 12), mp.nstr(rhs, 12)))
    return True

def construct(I, rseq, r0, Tseq):
    """sec 5.6: given r_k (k=1..KB), r0, integers T_k = K tau_k (k=1..KB). Returns beta and data."""
    K, s = I.K, I.sigma
    r0t = r0 % K
    Tp = list(Tseq); Tp[0] = Tseq[0] + s * r0t
    x = [(-1) ** I.nk(k) * Tp[k - 1] for k in range(1, I.KB + 1)]
    beta = sum(Tp[k - 1] * abs(I.eps[I.nk(k)]) for k in range(1, I.KB + 1)) / K
    return beta, Tp, x, r0t

def round_tieaware(z):
    f = mp.floor(z)
    d = z - f
    if abs(d - mp.mpf(0.5)) < TOL:
        return None
    return int(f) if d < 0.5 else int(f) + 1

def run_construction(I, rseq, r0, Tseq, label, ktest):
    K, l, s = I.K, I.l, I.sigma
    beta, Tp, x, r0t = construct(I, rseq, r0, Tseq)
    tau = [mp.mpf(T) / K for T in Tseq]
    tau_max = max(abs(t) for t in tau)
    Tpmax = max(abs(t) for t in Tp)
    T_tau_form = K * tau_max + s * (K - 1)
    T_wrong = K * tau_max
    # tail error of truncated beta series, times q_n for n <= n_ktest+l
    tail = 4 * mp.mpf(Tpmax) / (K * I.q[I.nk(I.KB) + 1]) if I.nk(I.KB) + 1 <= I.M else mp.mpf(0)
    numerr = tail * I.q[I.nk(ktest) + l + 1] + I.alpha_err * I.q[I.M] * 0  # alpha err included via dps
    ctx0 = f'{label} W={I.W} K={K} sig={s} r0={r0t}'
    res = {'labels_ok_when_small': 0, 'small_g': 0, 'big_g': 0, 'big_g_label_wrong': 0,
           'big_g_label_right': 0, 'wrong_form_fail': 0, 'first_wrong_form_fail': None,
           'max_abs_tk_minus_tauk_last': None}
    # exact (d2)
    P = [0] * (I.M + 1)  # P^(k) as function of n, updated incrementally
    for k in range(1, ktest + 1):
        nkk = I.nk(k)
        for n in range(I.M + 1):
            P[n] += x[k - 1] * I.D(nkk, n)
        sk = P[nkk + 1] if nkk + 1 <= I.M else None
        assert P[nkk] % K == 0, ('d2(i)', ctx0, k)
        if l >= 1:
            assert (sk - rseq[k - 1]) % K == 0, ('d2(ii)', ctx0, k)
            for i in range(1, l + 1):
                assert (P[nkk + i] - I.c[i - 1] * sk) % K == 0, ('d2 tail', ctx0, k, i)
        stats['checks'] += 2 + l
        # (d1) + (d3) per n in block k
        Epast = {}; Efut = {}
        for i in range(0, l + 1):
            n = nkk + i
            ep = sum(x[j - 1] * I.q[I.nk(j)] for j in range(1, k + 1)) * I.eps[n] / K
            ef = sum(x[j - 1] * I.eps[I.nk(j)] for j in range(k + 1, I.KB + 1)) * I.q[n] / K
            Epast[i], Efut[i] = ep, ef
            lhs = I.q[n] * beta - (mp.mpf(P[n]) / K + ep + ef)
            chk('d1 identity', abs(lhs), mp.mpf(10) ** -30, ctx=f'{ctx0} k={k} i={i}')
        Ak = I.A[k - 1]; Ak1 = I.A[k] if k < len(I.A) else None
        for Tname, T in (('Tp', Tpmax), ('Ttau', T_tau_form)):
            # n = n_k
            rest = K * Epast[0] - Tp[k - 1] * I.theta[nkk]
            if k >= 2:
                b1 = 4 * mp.mpf(T) * I.q[I.nk(k - 1)] / I.q[nkk + 1]
                chk(f'd3 nk past rest <4Tq/q [{Tname}]', abs(rest), b1, strict=(T > 0), ctx=f'{ctx0} k={k}')
                chk(f'd3 nk A_k*past rest <=4T/A_(k-1) [{Tname}]', Ak * abs(rest), 4 * mp.mpf(T) / I.A[k - 2], ctx=f'{ctx0} k={k}')
            else:
                chk('d3 nk past rest k=1 is 0', abs(rest), mp.mpf(10) ** -30, ctx=f'{ctx0} k=1')
            if Ak1 is not None and I.nk(k + 1) + 1 <= I.M:
                b2 = 4 * mp.mpf(T) * I.q[nkk] / I.q[I.nk(k + 1) + 1]
                chk(f'd3 nk fut [{Tname}]', K * abs(Efut[0]), b2 + numerr, strict=False, ctx=f'{ctx0} k={k}')
                chk(f'd3 nk A_k*fut <=4T/A_(k+1) [{Tname}]', Ak * K * abs(Efut[0]), 4 * mp.mpf(T) / Ak1 + numerr, ctx=f'{ctx0} k={k}')
            for i in range(1, l + 1):
                n = nkk + i
                chk(f'd3 past i>=1 [{Tname}]', K * abs(Epast[i]), 4 * mp.mpf(T) * I.q[nkk] / I.q[n + 1], strict=(T > 0), ctx=f'{ctx0} k={k} i={i}')
                chk(f'd3 past i>=1 <=4T/A_k [{Tname}]', K * abs(Epast[i]), 4 * mp.mpf(T) / Ak, ctx=f'{ctx0} k={k} i={i}')
                if Ak1 is not None:
                    chk(f'd3 fut i>=1 <=4T/A_(k+1) [{Tname}]', K * abs(Efut[i]), 4 * mp.mpf(T) / Ak1 + numerr, ctx=f'{ctx0} k={k} i={i}')
            if l >= 1 and Ak1 is not None:
                Kg = K * (Epast[1] + Efut[1])
                chk(f"g'_k bound 4T/A_k+4T/A_(k+1) [{Tname}]", abs(Kg), 4 * mp.mpf(T) / Ak + 4 * mp.mpf(T) / Ak1 + numerr, ctx=f'{ctx0} k={k}')
                chk(f"g'_k bound 8T/min [{Tname}]", abs(Kg), 8 * mp.mpf(T) / min(Ak, Ak1) + numerr, ctx=f'{ctx0} k={k}')
        # wrong form, labels, t_k - tau_k
        if l >= 1 and Ak1 is not None:
            Kg = K * (Epast[1] + Efut[1])
            if abs(Kg) > 8 * mp.mpf(T_wrong) / min(Ak, Ak1):
                res['wrong_form_fail'] += 1
                if res['first_wrong_form_fail'] is None:
                    res['first_wrong_form_fail'] = (k, mp.nstr(abs(Kg), 6), mp.nstr(8 * mp.mpf(T_wrong) / min(Ak, Ak1), 6))
            y = I.q[nkk + 1] * beta - mp.nint(I.q[nkk + 1] * beta)
            rr = round_tieaware(K * y)
            lab = None if rr is None else rr % K
            if abs(Kg) < 0.5:
                res['small_g'] += 1
                stats['checks'] += 1
                if lab == rseq[k - 1] % K:
                    res['labels_ok_when_small'] += 1
                else:
                    stats['viol'] += 1; viol_list.append(('label sufficiency', ctx0, k, lab))
            else:
                res['big_g'] += 1
                if lab == rseq[k - 1] % K: res['big_g_label_right'] += 1
                else: res['big_g_label_wrong'] += 1
        # t_k - tau_k identity (when |q_nk beta - P/K| < 1/2)
        z = I.q[nkk] * beta - mp.mpf(P[nkk]) / K
        if abs(z) < 0.5:
            yk = I.q[nkk] * beta - mp.nint(I.q[nkk] * beta)
            tk = Ak * yk
            eta = Ak * (K * Epast[0] - Tp[k - 1] * I.theta[nkk] + K * Efut[0]) / K
            rhs = mp.mpf(Tp[k - 1]) / K * (Ak * I.theta[nkk] - 1) + eta + mp.mpf(Tp[k - 1] - Tseq[k - 1]) / K
            chk('t_k - tau_k identity', abs((tk - tau[k - 1]) - rhs), mp.mpf(10) ** -30, ctx=f'{ctx0} k={k}')
            res['max_abs_tk_minus_tauk_last'] = mp.nstr(abs(tk - tau[k - 1]), 6)
        # Lemma B
        inv = 1 / I.theta[nkk]
        chk('LemmaB lower', mp.mpf(Ak), inv, strict=True, ctx=f'{ctx0} k={k}')
        chk('LemmaB upper', inv, mp.mpf(Ak + 2), strict=True, ctx=f'{ctx0} k={k}')
    return beta, res

def E_checks(I, beta, ktest, label):
    """sec 8 (E1)-(E4) with C := max of the R_n the derivation uses."""
    K, l, s = I.K, I.l, I.sigma
    y = [I.q[n] * beta - mp.nint(I.q[n] * beta) for n in range(I.M + 1)]
    R = [abs(y[n]) / I.theta[n] for n in range(I.M)] + [None]
    ctx0 = f'{label} W={I.W}'
    nE3 = nE4 = 0
    for k in range(1, ktest + 1):
        nkk = I.nk(k); Ak = I.A[k - 1]
        # E1 (C = R_{n_k}) ; also with C=R_{n_k}: |y| <= C theta < C/A_k (strict iff C>0)
        C = R[nkk]
        chk('E1 y', abs(y[nkk]), C / Ak, strict=(C > 0), ctx=f'{ctx0} k={k}')
        chk('E1 t', Ak * abs(y[nkk]), C, strict=(C > 0), ctx=f'{ctx0} k={k}')
        if k + 2 > len(I.A): continue
        nk1, nk2 = I.nk(k + 1), I.nk(k + 2)
        Ak1, Ak2 = I.A[k], I.A[k + 1]
        if l >= 1:
            K2l = Kint(I.W, 2, l)
            C2 = max(R[nkk], R[nk1])
            z = K * y[nkk + 1]
            dist = abs(z - mp.nint(z))
            chk('E2 first <=', dist, abs(y[nk1]) + K2l * abs(y[nkk]), ctx=f'{ctx0} k={k}')
            chk('E2', dist, C2 * (mp.mpf(1) / Ak1 + mp.mpf(K2l) / Ak), strict=(C2 > 0), ctx=f'{ctx0} k={k}')
            z1 = K * y[nk1 + 1]; dist1 = abs(z1 - mp.nint(z1))
            if dist < 0.5 - TOL:
                sk = int(mp.nint(z)); gk = y[nkk + 1] - mp.mpf(sk) / K
                for i in range(1, l + 1):
                    ci = I.c[i - 1]; K2i = Kint(I.W, 2, i - 1)
                    e = ci * gk + K2i * y[nkk]
                    # congruence y_{n_k+i} = c_i s_k/K + e (mod 1)
                    dd = y[nkk + i] - (mp.mpf(ci * sk) / K + e)
                    chk('E3 congruence', abs(dd - mp.nint(dd)), mp.mpf(10) ** -30, ctx=f'{ctx0} k={k} i={i}')
                    lhs = abs(abs(y[nkk + i]) - mp.mpf(dK(ci * sk, K)) / K)
                    chk('E3 <= |e|', lhs, abs(e), ctx=f'{ctx0} k={k} i={i}')
                    chk('E3 |e| <= ci|g|+K2|y|', abs(e), ci * abs(gk) + K2i * abs(y[nkk]), ctx=f'{ctx0} k={k} i={i}')
                    rhs = C2 * (mp.mpf(ci) / K * (mp.mpf(1) / Ak1 + mp.mpf(K2l) / Ak) + mp.mpf(K2i) / Ak)
                    chk('E3 final', lhs, rhs, strict=(C2 > 0), ctx=f'{ctx0} k={k} i={i}')
                    nE3 += 1
                if dist1 < 0.5 - TOL:
                    sk1 = int(mp.nint(z1)); gk1 = y[nk1 + 1] - mp.mpf(sk1) / K
                    tk1 = Ak1 * y[nk1]
                    w = tk1 - mp.mpf(sk1 - s * sk) / K
                    lhs = abs(w - mp.nint(w))
                    eL = s * gk + Kint(I.W, 2, l - 1) * y[nkk]
                    chk('E4 <= |g_{k+1}|+|e_{k,l}|', lhs, abs(gk1) + abs(eL), ctx=f'{ctx0} k={k}')
                    C3 = max(R[nkk], R[nk1], R[nk2])
                    rhs = C3 * (mp.mpf(1) / K * (mp.mpf(1) / Ak2 + mp.mpf(K2l) / Ak1)
                                + mp.mpf(s) / K * (mp.mpf(1) / Ak1 + mp.mpf(K2l) / Ak)
                                + mp.mpf(Kint(I.W, 2, l - 1)) / Ak)
                    chk('E4 final', lhs, rhs, strict=(C3 > 0), ctx=f'{ctx0} k={k}')
                    nE4 += 1
        else:
            tk1 = Ak1 * y[nk1]
            lhs = abs(tk1 - mp.nint(tk1))
            chk('E4 l=0 first', lhs, abs(y[nk2]) + abs(y[nkk]), ctx=f'{ctx0} k={k}')
            C3 = max(R[nkk], R[nk2])
            chk('E4 l=0 final', lhs, C3 * (mp.mpf(1) / Ak2 + mp.mpf(1) / Ak), strict=(C3 > 0), ctx=f'{ctx0} k={k}')
            nE4 += 1
    return nE3, nE4

# ---------------- instances ----------------
def Aseq(kind, KB):
    if kind == 'linear': return [k for k in range(1, KB + 1)]
    if kind == 'slow':   return [1 + int(math.log2(k)) for k in range(1, KB + 1)]
    if kind == 'const1': return [1] * KB              # outside hypothesis A_k->oo; finite-k bounds must still hold
    if kind == 'erratic': return [1 if k % 2 else 50 * k for k in range(1, KB + 1)]
    if kind == 'big':    return [1000 + k for k in range(1, KB + 1)]
    if kind == 'fast':   return [2 ** k for k in range(1, KB + 1)]
    raise ValueError

WORDS = [(), (1,), (2,), (12,), (1, 1), (1, 9, 9), (9, 9, 9), (5, 1, 5), (2, 1, 1, 2), (1, 2, 3, 4, 5),
         (1,) * 8, (3, 1, 4, 1, 5)]
HEADS = [(0,), (3, 7, 1, 1), (-2, 1)]

def main():
    out = []
    KB = 18; KTEST = 12
    summary = []
    for W in WORDS:
        for kind in ('linear', 'slow', 'const1', 'erratic', 'big', 'fast'):
            head = random.choice(HEADS)
            I = Inst(W, Aseq(kind, KB), head=head)
            K, s = I.K, I.sigma
            scenarios = []
            # S1: r0 = K-1 (extreme), r_k = 0, minimal tau (audit-type)
            r = [0] * KB
            T = []
            prev = K - 1
            for k in range(KB):
                d = (r[k] - s * prev) % K
                T.append(d if d <= K // 2 else d - K)
                prev = r[k]
            scenarios.append(('r0=K-1,r=0,min tau', r, K - 1, T))
            # S2: random labels, large |T| (up to 5K), r0 random
            r = [random.randrange(K) for _ in range(KB)]; r0 = random.randrange(K)
            T = []; prev = r0
            for k in range(KB):
                d = (r[k] - s * prev) % K
                T.append(d + K * random.randint(-5, 4)); prev = r[k]
            scenarios.append(('random r, |T|<=5K', r, r0, T))
            # S3: beta = 0 degenerate: r0=0, r=0, T=0
            scenarios.append(('beta=0', [0] * KB, 0, [0] * KB))
            # S4: T'_1 = 0 but T_1 != 0 (only possible when sigma*r0t != 0)
            if K > 1:
                r0 = K - 1; T1 = -s * r0
                T = [T1] + [0] * (KB - 1)
                scenarios.append(("T'_1=0,T_1!=0", [0] * KB, r0, T))
            # S5: near-half Kg' attempt: tau_1 large with r0=K-1, rest periodic optimal-ish random
            r = [0] + [random.randrange(K) for _ in range(KB - 1)]
            T = []; prev = K - 1
            for k in range(KB):
                d = (r[k] - s * prev) % K
                T.append(d + (3 * K if k == 0 else 0)); prev = r[k]
            scenarios.append(('r0=K-1, big T_1', r, K - 1, T))
            for (lab, r, r0, T) in scenarios:
                beta, res = run_construction(I, r, r0, T, f'{kind}/{lab}', KTEST)
                e3, e4 = E_checks(I, beta, KTEST, f'{kind}/{lab}/constructed')
                summary.append((W, kind, lab, res))
            # E-checks on other beta families
            for fam in range(3):
                if fam == 0:
                    b = random.choice(scenarios)
                    beta, _ = construct(I, b[1], b[2], b[3])[0], None
                    u, v = random.choice([(1, 0), (-3, 2), (7, -1)])
                    beta = beta + u * I.alpha + v; flab = f'shift u={u}'
                elif fam == 1:
                    beta = mp.mpf(random.random()) + mp.mpf(random.random()) * mp.mpf(10) ** -17; flab = 'random'
                else:
                    Kp = random.randint(1, 7)
                    beta = sum(random.randint(-3, 3) * I.eps[n] for n in range(I.M - 3 * (I.l + 1))) / Kp
                    flab = f'digits/K\'={Kp}'
                E_checks(I, beta, KTEST, f'{kind}/{flab}')
    print('=== summary per (W, A-kind, scenario) ===')
    for (W, kind, lab, res) in summary:
        print(W, kind, lab, res)
    print()
    print('total checks', stats['checks'], ' violations', stats['viol'], ' indeterminate', stats['indet'])
    for v in viol_list[:60]:
        print('  VIOL/INDET:', v)
    print('ALL CHECKS PASSED' if stats['viol'] == 0 and stats['indet'] == 0 else 'SOME CHECKS FAILED/INDETERMINATE')

if __name__ == '__main__':
    main()
