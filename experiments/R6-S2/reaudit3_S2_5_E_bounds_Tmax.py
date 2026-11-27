# reaudit3 script 5: Sec.8 explicit bounds.
#  Part A: (tau) bound T_max <= K tau_max + sigma(K-1): exact exhaustive check on small words, and attainment.
#  Part B: reproduce the M4 counterexample numbers (|K g'_1| ~ 0.818 vs 8 K tau_max/min(A_1,A_2) ~ 0.0799)
#          and check the corrected bounds (tau') and (tau) there.
#  Part C: (E1)-(E4),(E4_0) strict forms for k in [k_1, ...] with minimal admissible k_0, k_1, on
#          constructed beta (random data, big initial T) and on lattice points (incl. beta in Z, u=0).
# Category 4 evidence only.
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(__file__))
from fractions import Fraction as Fr
import mpmath
from reaudit3_S2_common import Kc, Kseg, params, vcost

random.seed(11)
fails = 0
def chk(c, m):
    global fails
    if not c:
        fails += 1; print('  FAIL', m)

print('=== Part A ===')
cases = 0; eq = 0
for l in range(0, 4):
    for W in itertools.product(range(1, 5), repeat=l):
        K, c, cp, s = params(list(W))
        for r0 in range(K):
            for r1 in range(K):
                base = (r1 - s * r0) % K
                for j in range(-3, 4):
                    T1 = base + j * K               # T_1 = K tau_1 in the right class
                    for Trest in [0, 1, K, 2 * K + 1]:   # sup_{k>=2}|T_k| (any value allowed)
                        Tsup = max(abs(T1), Trest)
                        T1p = T1 + s * r0
                        Tmax = max(Tsup, abs(T1p))
                        bound = Tsup + s * (K - 1)   # K tau_max = Tsup
                        chk(Tmax <= bound, ('Tmax', W, r0, r1, T1))
                        cases += 1; eq += (Tmax == bound)
print('  T_max <= K tau_max + sigma(K-1): %d cases, %d equalities, fails so far %d' % (cases, eq, fails))

def build(W, Aseq, a0=0, head=()):
    l = len(W); N = len(head)
    seq = [a0] + list(head)
    for A in Aseq:
        seq += [A] + list(W)
    p = [1, seq[0]]; q = [0, 1]
    for a in seq[1:]:
        p.append(a * p[-1] + p[-2]); q.append(a * q[-1] + q[-2])
    mpmath.mp.dps = 2 * len(str(q[-1])) + 60
    x = mpmath.mpf(0)
    for a in reversed(seq[1:]):
        x = 1 / (a + x)
    alpha = seq[0] + x
    return alpha, (lambda n: p[n + 1]), (lambda n: q[n + 1]), (lambda k: N + (k - 1) * (l + 1))

print('=== Part B ===')
W = [1, 9, 9]; K, c, cp, s = params(W)
kb = 12; Aseq = [1000 + k for k in range(1, kb + 4)]
alpha, P, Q, nk = build(W, Aseq)
eps = lambda n: Q(n) * alpha - P(n)
r0 = 90; T1 = 10; Tp = [T1 + s * r0] + [0] * (kb - 1)
print('  K=%d sigma=%d  T\'_1=%d (=T_1+sigma r0)' % (K, s, Tp[0]))
# K g'_1 = K(E^past_{n_1+1}+E^fut_{n_1+1}) = sum_j x_j q_{n_j} eps_{n} (j<=1) + sum_{j>1} x_j q_n eps_{n_j}
n = nk(1) + 1
x = [(-1) ** nk(j) * Tp[j - 1] for j in range(1, kb + 1)]
Kg = x[0] * Q(nk(1)) * eps(n) + sum(x[j - 1] * Q(n) * eps(nk(j)) for j in range(2, kb + 1))
tau_max = Fr(T1, K); Tmaxp = max(abs(t) for t in Tp)
wrong = 8 * K * tau_max / min(Aseq[0], Aseq[1])
taup = 8 * Tmaxp / min(Aseq[0], Aseq[1])            # (tau') with tau'_max = T'_max/K
taub = 8 * (K * tau_max + s * (K - 1)) / min(Aseq[0], Aseq[1])   # (tau)
print('  |K g\'_1| = %s ; wrong bound 8K tau_max/min = %s ; (tau\') bound = %s ; (tau) bound = %s'
      % (mpmath.nstr(abs(Kg), 6), float(wrong), float(taup), float(taub)))
chk(abs(Kg) > wrong, 'counterexample reproduces')
chk(abs(Kg) <= taup and abs(Kg) <= taub, 'corrected bounds hold')

print('=== Part C: (E1)-(E4),(E4_0) ===')
def Echeck(W, beta_fn, label, Aseq, kb):
    global fails
    K, c, cp, s = params(W); l = len(W)
    alpha, P, Q, nk = build(W, Aseq)
    eps = lambda n: Q(n) * alpha - P(n)
    beta, exact_zero = beta_fn(alpha, P, Q, nk, eps)
    def y(n):
        if exact_zero:
            return mpmath.mpf(0)
        z = Q(n) * beta; return z - mpmath.nint(z)
    th = lambda n: Q(n) * abs(eps(n))
    R = {n: abs(y(n)) / th(n) for n in range(nk(1), nk(kb) + 1)}
    Kest = max(R[n] for n in range(nk(kb - 3), nk(kb)))
    # minimal k0 with R_n <= Kest+1 for all n >= n_{k0} (within window)
    k0 = 1
    while any(R[n] > Kest + 1 for n in range(nk(k0), nk(kb) + 1)):
        k0 += 1
    Kp1 = Kest + 1
    viol = 0; checked = 0
    if l >= 1:
        k1 = k0
        while any(abs(K * y(nk(k) + 1) - mpmath.nint(K * y(nk(k) + 1))) >= 0.5 for k in range(k1, kb - 2)):
            k1 += 1
        for k in range(k1, kb - 3):
            A = lambda j: Aseq[j - 1]
            yk = y(nk(k)); tk = A(k) * yk
            # E1
            viol += not (abs(yk) < Kp1 / A(k) and abs(tk) < Kp1); checked += 2
            # E2
            Ky = K * y(nk(k) + 1); g = (Ky - mpmath.nint(Ky)) / K
            sk = int(mpmath.nint(Ky)); rk = sk % K
            E2 = Kp1 * (mpmath.mpf(1) / A(k + 1) + mpmath.mpf(Kseg(W, 2, l)) / A(k))
            viol += not (abs(K * g) < E2); checked += 1
            # E3
            for i in range(1, l + 1):
                d = min((c[i-1] * rk) % K, K - (c[i-1] * rk) % K)
                lhs = abs(abs(y(nk(k) + i)) - mpmath.mpf(d) / K)
                E3 = Kp1 * (mpmath.mpf(c[i-1]) / K * (mpmath.mpf(1) / A(k + 1) + mpmath.mpf(Kseg(W, 2, l)) / A(k))
                            + mpmath.mpf(Kseg(W, 2, i - 1)) / A(k))
                viol += not (lhs < E3); checked += 1
            # E4
            Ky2 = K * y(nk(k + 1) + 1); rk1 = int(mpmath.nint(Ky2)) % K
            tk1 = A(k + 1) * y(nk(k + 1))
            z = tk1 - mpmath.mpf(rk1 - s * rk) / K
            lhs = abs(z - mpmath.nint(z))
            E4 = Kp1 * (mpmath.mpf(1) / K * (mpmath.mpf(1) / A(k + 2) + mpmath.mpf(Kseg(W, 2, l)) / A(k + 1))
                        + mpmath.mpf(s) / K * (mpmath.mpf(1) / A(k + 1) + mpmath.mpf(Kseg(W, 2, l)) / A(k))
                        + mpmath.mpf(Kseg(W, 2, l - 1)) / A(k))
            viol += not (lhs < E4); checked += 1
    else:
        k1 = None
        for k in range(k0, kb - 3):
            A = lambda j: Aseq[j - 1]
            tk1 = A(k + 1) * y(nk(k + 1))
            lhs = abs(tk1 - mpmath.nint(tk1))
            E40 = Kp1 * (mpmath.mpf(1) / A(k + 2) + mpmath.mpf(1) / A(k))
            viol += not (lhs < E40); checked += 1
            viol += not (abs(y(nk(k))) < Kp1 / A(k) and abs(A(k) * y(nk(k))) < Kp1); checked += 2
    print('  %-26s W=%-10s K_est=%-10s k0=%s k1=%s checked=%d violations=%d'
          % (label, W, mpmath.nstr(Kest, 6), k0, k1, checked, viol))
    chk(viol == 0, label)

for W in [[1, 9, 9], [2], [3, 1], [5, 1, 5], [1, 1], [], [1]]:
    K, c, cp, s = params(W)
    kb = 26
    for regime, Aseq in [('A_k=k+1', [k + 1 for k in range(1, kb + 4)]),
                         ('A_k=50+k', [50 + k for k in range(1, kb + 4)])]:
        T = [random.randint(-300, 300) for _ in range(3)] + [random.randint(-2 * K, 2 * K) for _ in range(kb - 3)]
        def bconstr(alpha, P, Q, nk, eps, T=T):
            return sum(mpmath.mpf(T[k - 1]) * abs(eps(nk(k))) for k in range(1, kb + 1)) / params(W)[0], False
        Echeck(W, bconstr, 'constructed ' + regime, Aseq, kb)
        for (u, v) in [(0, 3), (0, 0), (2, -1)]:
            def blat(alpha, P, Q, nk, eps, u=u, v=v):
                return u * alpha + v, (u == 0)
            Echeck(W, blat, 'lattice u=%d v=%d %s' % (u, v, regime), Aseq, kb)
print('FAILS:', fails)
print('ALL CHECKS PASSED' if fails == 0 else 'SOME CHECKS FAILED')
