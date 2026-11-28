"""reaudit2 (R6-S2 after repair round 2) -- self-written by the isolated skeptic.
Degenerate case beta = v in Z (u = 0, so beta is in Z alpha + Z):
  sec 5.4 claims |t_k| = (A_k theta_{n_k}) R_{n_k} < R_{n_k}           (strict)
  sec 5.5 (=>) claims |u eps_n| < |u|/q_{n+1}  and  |t_k| < |u|/q_{n_k}  (strict)
Here y_n = 0 exactly, so all sides are 0 and the strict inequalities are false (0 < 0).
Also checks that the sec 8 (E1) form |t_k| < K+1 is unaffected.  Exact rational arithmetic.
"""
from fractions import Fraction as Fr
W = (1, 9, 9); l = len(W); KB = 8
a = [0]
for k in range(1, KB + 1):
    a.append(k); a.extend(W)
p = [a[0]]; q = [1]
for n in range(1, len(a)):
    p.append(a[n] * p[-1] + (p[-2] if n >= 2 else 1)); q.append(a[n] * q[-1] + (q[-2] if n >= 2 else 0))
alpha = Fr(p[-1], q[-1])            # any irrational-ish proxy; y_n below does not depend on alpha
v = 3; u = 0; beta = u * alpha + v
viol54 = viol55a = viol55b = 0; e1ok = True
for k in range(1, KB - 1):
    nk = (k - 1) * (l + 1)
    y = q[nk] * beta - round(q[nk] * beta)
    eps = q[nk] * alpha - p[nk]; theta = q[nk] * abs(eps)
    R = abs(y) / theta
    t = k * y
    if not (abs(t) < R): viol54 += 1
    if not (abs(u * eps) < Fr(abs(u), q[nk + 1])): viol55a += 1
    if not (abs(t) < Fr(abs(u), q[nk])): viol55b += 1
    Kfun = 0                         # KL functional of an integer beta is 0
    if not (abs(t) < Kfun + 1): e1ok = False
print(f'beta = {beta}: y_(n_k) = 0 for all tested k')
print(f'sec 5.4 strict |t_k| < R_(n_k) false in {viol54}/{KB-2} blocks (0 < 0)')
print(f'sec 5.5 strict |u eps_n| < |u|/q_(n+1) false in {viol55a}/{KB-2}; |t_k| < |u|/q_(n_k) false in {viol55b}/{KB-2}')
print(f'sec 8 (E1) |t_k| < K+1 holds: {e1ok}')
print('CONCLUSION: strict inequalities in sec 5.4 / 5.5(=>) fail in the degenerate case u=0 / y_(n_k)=0; "<" must be "<=" (conclusions unaffected).')
