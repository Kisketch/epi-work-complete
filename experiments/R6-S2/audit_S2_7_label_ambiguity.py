"""Audit interpretive convention I1 (proof §0.4): is the label sequence in S1(b) unique?

Self-contained. W=(1,2): K=3, sigma=c_2=K(1)=1, c_1=c_2=1, c_1'=K(2)=2, c_2'=1.
beta := (1/3) * sum_k T'_k |eps_{n_k}| with T'_1 = 1, T'_k = 0 (k>=2)  -> canonical labels r_k = 1 (all k),
t_k -> 0.  We check numerically that BOTH constant sequences r_k == 1 and r'_k == 2 (= -1 mod 3) satisfy all
three items of S1(b):  | |y_{n_k+i}| - d_K(c_i r_k)/K | -> 0  and  dist(t_{k+1} - (r_{k+1}-sigma r_k)/K, Z) -> 0.
Consequence: 'the label' in S1(c)(d) is not determined by S1(b); under the reading 'every (b)-witness equals
r_k eventually', S1(d) is false (r_k == 1 and r'_k == 2 both witness).  The proof's canonical label (I1)
is therefore a genuine definitional choice that should be written into the statement.
"""
import mpmath as mp

W = (1, 2); K = 3; sigma = 1; c = [1, 1]
a = [0]
for k in range(1, 40):
    a.append(1000 * k); a.extend(W)
p = [a[0]]; q = [1]
for n in range(1, len(a)):
    p.append(a[n] * p[-1] + (p[-2] if n >= 2 else 1))
    q.append(a[n] * q[-1] + (q[-2] if n >= 2 else 0))
mp.mp.dps = 2 * len(str(q[-1])) + 100
x = mp.mpf(a[-1])
for t in reversed(a[:-1]):
    x = t + 1 / x
eps = [q[n] * x - p[n] for n in range(len(a) - 2)]
nk = {k: (k - 1) * 3 for k in range(1, 40)}
beta = mp.fabs(eps[nk[1]]) / 3
y = lambda n: q[n] * beta - mp.nint(q[n] * beta)
dK = lambda z: min(z % K, K - z % K)
for rc in (1, 2):
    e1 = max(abs(float(mp.fabs(y(nk[k] + i)) - mp.mpf(dK(c[i - 1] * rc)) / K)) for k in range(20, 30) for i in (1, 2))
    e2 = 0.0
    for k in range(20, 30):
        z = 1000 * (k + 1) * y(nk[k + 1]) - mp.mpf((rc - sigma * rc) % K) / K
        e2 = max(e2, abs(float(z - mp.nint(z))))
    print(f"constant label {rc}: max item-1 error (k=20..29) = {e1:.3e}; max coupling error = {e2:.3e}")
print("canonical label round(K y_{n_k+1}) mod K at k=20..29:",
      [int(mp.nint(K * y(nk[k] + 1))) % K for k in range(20, 30)])
print("category 4: finite computation; shows non-uniqueness of (b)-witnesses for this beta.")
