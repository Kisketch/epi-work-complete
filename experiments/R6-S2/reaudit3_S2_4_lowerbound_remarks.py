# reaudit3 script 4:
#  Part A: lower bound probe with beta NOT from the S1(d) family: beta=(a*alpha+b)/m, small m.
#          Every non-lattice beta whose late block maxima stay bounded must have late max >= nu(W) - O(1/A).
#  Part B: Sec.8 'finite shift' remark: "adding u*alpha+v changes y_n eventually by u*eps_n" (as reals) -- test.
#  Part C: Sec.8 'ties' remark: "for k>=k_1 ... y_{n_k} is also far from +-1/2" -- probe with minimal admissible k_1.
# Category 4 evidence only.
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from fractions import Fraction as Fr
import mpmath
from reaudit3_S2_common import Kc, params, vcost, nu

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
    P = lambda n: p[n + 1]; Q = lambda n: q[n + 1]
    nk = lambda k: N + (k - 1) * (l + 1)
    return alpha, P, Q, nk

fails = 0
print('=== Part A: beta=(a alpha+b)/m, lower bound probe ===')
for W in [[5, 1, 5], [3, 1], [2, 2], [1, 9, 9], [1, 1], []]:
    K, c, cp, s = params(W); l = len(W); nuW = nu(W)[0]
    kb = 30; Aseq = [1000 + k for k in range(1, kb + 4)]
    alpha, P, Q, nk = build(W, Aseq)
    eps = lambda n: Q(n) * alpha - P(n)
    bounded = 0; minval = None; arg = None; lattice_like = 0
    for m in range(2, 41):
        for a in range(0, m):
            for b in range(0, m):
                if a == 0 and b == 0:
                    continue
                from math import gcd
                if gcd(gcd(a, b), m) != 1:
                    continue
                beta = (a * alpha + b) / m
                Mmax = 0
                for k in range(20, 27):
                    for i in range(l + 1):
                        n = nk(k) + i
                        z = Q(n) * beta; y = z - mpmath.nint(z)
                        Mmax = max(Mmax, abs(y) / (Q(n) * abs(eps(n))))
                if Mmax < 10:
                    bounded += 1
                    if minval is None or Mmax < minval:
                        minval = Mmax; arg = (a, b, m)
    ok = (minval is None) or (minval >= float(nuW) - 0.02)
    if not ok:
        fails += 1
    print('  W=%-10s nu=%-5s  #bounded non-lattice beta=%d  min late max=%s at (a,b,m)=%s  %s'
          % (W, nuW, bounded, None if minval is None else mpmath.nstr(minval, 8), arg, 'OK' if ok else 'VIOLATION'))

print('=== Part B: Sec.8 finite-shift remark ===')
W = [1, 1]; kb = 30; Aseq = [10 + k for k in range(1, kb + 4)]
alpha, P, Q, nk = build(W, Aseq)
eps = lambda n: Q(n) * alpha - P(n)
beta = alpha / 2            # = eps_0/2, i.e. the S1(d) construction with T'_1=1, T_k=0 (k>=2), N=0
u, v = -1, 0
bad = []; Rmax = 0
for n in range(30, nk(kb - 3)):
    z = Q(n) * beta; y = z - mpmath.nint(z)
    z2 = Q(n) * (beta + u * alpha + v); y2 = z2 - mpmath.nint(z2)
    Rmax = max(Rmax, abs(y) / (Q(n) * abs(eps(n))))
    if abs(y2 - (y + u * eps(n))) > mpmath.mpf(10) ** (-50):
        bad.append((n, mpmath.nstr(y, 6), mpmath.nstr(y2, 6), mpmath.nstr(y + u * eps(n), 6)))
print('  W=(1,1), alpha=[0;A_1,1,1,A_2,1,1,...], A_k=10+k, beta=alpha/2 (K_alpha(beta) finite: max R_n over n>=30 = %s)'
      % mpmath.nstr(Rmax, 6))
print('  #n in [30,%d) with y_n(beta-alpha) != y_n(beta) - eps_n (as real numbers): %d' % (nk(kb - 3), len(bad)))
for row in bad[:6]:
    print('    n=%d  y_n(beta)=%s  y_n(beta-alpha)=%s  y_n(beta)-eps_n=%s' % row)
print('  => the remark is false as an identity of real numbers (true only mod 1 / for |y_n|), infinitely often in this example'
      if len(bad) > 5 else '  => no counterexample found')

print('=== Part C: Sec.8 tie remark at minimal admissible k_1 ===')
W = [1, 9, 9]; K, c, cp, s = params(W); l = len(W)
kb = 22
Aseq = [3] + [1000 + k for k in range(2, kb + 4)]
alpha, P, Q, nk = build(W, Aseq)
eps = lambda n: Q(n) * alpha - P(n)
best = None
for T1 in range(-400, 401):
    if T1 == 0:
        continue
    beta = T1 * abs(eps(nk(1))) / K     # S1(d) construction with T'_1=T1, T_k=0 (k>=2)
    ys = {}
    def y(n):
        if n not in ys:
            z = Q(n) * beta; ys[n] = z - mpmath.nint(z)
        return ys[n]
    R = [abs(y(n)) / (Q(n) * abs(eps(n))) for n in range(nk(1), nk(kb - 2))]
    Kest = max(R[-3 * (l + 1):])          # late block max ~ limsup
    k0_ok = all(r <= Kest + 1 for r in R)  # k_0 = 1 admissible
    k1_ok = all(abs(K * y(nk(k) + 1) - mpmath.nint(K * y(nk(k) + 1))) < 0.5 for k in range(1, kb - 2))
    if k0_ok and k1_ok:
        val = abs(y(nk(1)))
        if best is None or val > best[0]:
            best = (val, T1, Kest)
if best:
    print('  W=(1,9,9), A_1=3, A_k=1000+k: among T\'_1 in [-400,400] with k_0=k_1=1 admissible, max |y_{n_1}| = %s (T\'_1=%d, K~%s)'
          % (mpmath.nstr(best[0], 6), best[1], mpmath.nstr(best[2], 6)))
print('FAILS (Part A lower-bound violations):', fails)
print('PART A PASSED' if fails == 0 else 'PART A FAILED')
