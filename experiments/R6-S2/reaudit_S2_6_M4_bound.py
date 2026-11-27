"""reaudit_S2_6: the section-8 (M4) remark.

The proof states  |K g_k| < 4T_max/A_k + 4T_max/A_{k+1} <= 8 T_max / min(A_k, A_{k+1}),  T_max = sup_k |T'_k| (incl. T'_1),
and then: 'if expressed via tau_max := sup_k |tau_k|, the bound is 8 K tau_max / min(A_k, A_{k+1})'.
The second form silently replaces T'_1 = T_1 + sigma*r0~ by K*tau_1; |T'_1| can be ~K^2 while K*tau_max is O(1).
Test: W = (1,9,9) (K=91, sigma=10), r_0 = 90, r_k = 0 (k>=1), tau_1 = 10/91, tau_k = 0 (k>=2), A_k = 1000 + k.
"""
import math
from fractions import Fraction as F
import mpmath as mp

def Kc(ws):
    a, b = 0, 1
    for w in ws: a, b = b, w * b + a
    return b

W = (1, 9, 9); l = 3; K = Kc(W); sigma = Kc(W[:-1])
r0 = 90
base = F((0 - sigma * r0) % K, K); tau1 = base if base <= F(1, 2) else base - 1
print("K =", K, "sigma =", sigma, "tau_1 =", tau1)
KT = 40
A = [1000 + k for k in range(1, KT + 2)]
a = [0]
for k in range(KT + 1): a += [A[k]] + list(W)
p, q = [a[0]], [1]; pm, qm = 1, 0
for n in range(1, len(a)):
    p.append(a[n] * p[-1] + (p[-2] if n >= 2 else pm)); q.append(a[n] * q[-1] + (q[-2] if n >= 2 else qm))
M = len(a) - 1
mp.mp.dps = int(2.2 * math.log10(q[M])) + 50
alpha = mp.mpf(p[M]) / q[M]
eps = [q[n] * alpha - p[n] for n in range(M + 1)]
nk = lambda k: (k - 1) * (l + 1)
T = [None, int(tau1 * K)] + [0] * (KT - 1)
Tp = list(T); Tp[1] = T[1] + sigma * r0
tau_max = abs(tau1)
Tmax = max(abs(x) for x in Tp[1:])
print("T_1 =", T[1], " T'_1 =", Tp[1], " T_max (with T'_1) =", Tmax, " K*tau_max =", float(K * tau_max))
beta = sum(Tp[k] * abs(eps[nk(k)]) for k in range(1, KT + 1)) / K
def D(m, n): return q[m] * p[n] - p[m] * q[n]
x = [None] + [(-1) ** nk(k) * Tp[k] for k in range(1, KT + 1)]
for k in range(1, 6):
    s_k = sum(x[j] * D(nk(j), nk(k) + 1) for j in range(1, k + 1))
    Kg = K * (q[nk(k) + 1] * beta) - s_k
    Kg = Kg - K * mp.nint(Kg / K)
    bT = mp.mpf(8 * Tmax) / min(A[k - 1], A[k])
    btau = 8 * K * mp.mpf(tau_max.numerator) / tau_max.denominator / min(A[k - 1], A[k])
    y = q[nk(k) + 1] * beta; y = y - mp.nint(y)
    lab = int(mp.nint(K * y)) % K
    print(f"k={k}: |K g_k| = {mp.nstr(abs(Kg),6)};  8T_max/minA = {mp.nstr(bT,6)} (holds: {abs(Kg) < bT});  "
          f"8K tau_max/minA = {mp.nstr(btau,6)} (holds: {abs(Kg) < btau});  label={lab} (given 0)")
