"""repair3 (R6-S2, prover repair round 3) -- side evidence only, not part of the proof.

Degenerate lattice case beta = u*alpha + v (u, v integers), in particular u = 0 (y_n == 0, K_functional = 0).
Part A: sec 5.4 / 5.5(=>) -- the repaired '<=' forms hold; the old strict forms fail exactly when u = 0.
Part B: sec 8 (E1)-(E4), (E4_0) -- strict forms hold with K_functional = 0 (so 'K+1' = 1), also for y == 0.
Part C: sec 5.6 (d3) note -- T_max > 0 but T'_max = 0 is possible (beta = 0); strict bounds with T_max hold,
        with T'_max they fail (0 < 0), '<=' holds.
alpha: block Hurwitz number [0; A_1, W, A_2, W, ...], A_k = 10 + k, truncated at 60 blocks, mpmath 400 digits.
Exact zero handling: for u = 0 all y_n are the exact integer 0 (q_n * v is an integer).
"""
from mpmath import mp, mpf, nint, fabs
from common import cont

mp.dps = 400
NB_TRUNC, NB_TEST = 60, 14


def setup(W):
    l = len(W)
    a = [0]
    for k in range(1, NB_TRUNC + 1):
        a.append(10 + k); a.extend(W)
    p, q = [a[0]], [1]
    pm, qm = 1, 0
    for n in range(1, len(a)):
        p.append(a[n] * p[-1] + (p[-2] if n >= 2 else pm)); q.append(a[n] * q[-1] + (q[-2] if n >= 2 else qm))
    alpha = mpf(p[-1]) / q[-1]
    eps = [q[n] * alpha - p[n] for n in range(len(a) - 5)]
    nk = lambda k: (k - 1) * (l + 1)
    A = lambda k: 10 + k
    return l, a, p, q, eps, nk, A


def Kint(W, a_, b_):  # K_[a,b] (1-based, inclusive); length -1 -> 0
    if b_ == a_ - 2:
        return 0
    return cont(W[a_ - 1:b_])


def y_lattice(u, v, eps, n):
    if u == 0:
        return 0  # exact: q_n*v is an integer
    x = u * eps[n]
    return x - nint(x)


def dist_Z(x):
    return fabs(x - nint(x)) if x != 0 else 0


fails = []


def check(name, cond):
    if not cond:
        fails.append(name)


print('Part A: sec 5.4 / 5.5(=>) in the lattice case')
for W in [(1, 9, 9), (2,), ()]:
    l, a, p, q, eps, nk, A = setup(W)
    for (u, v) in [(0, 3), (0, 0), (1, 0), (-2, 1), (5, -7)]:
        s54_le = s54_lt = s55a_le = s55a_lt = s55b_le = s55b_lt = 0
        tot = 0
        for k in range(3, NB_TEST):
            n = nk(k); y = y_lattice(u, v, eps, n); th = q[n] * fabs(eps[n]); R = fabs(y) / th
            t = A(k) * y
            s54_le += fabs(t) <= R; s54_lt += fabs(t) < R
            ue = fabs(u * eps[n])
            s55a_le += ue <= mpf(abs(u)) / q[n + 1]; s55a_lt += ue < mpf(abs(u)) / q[n + 1]
            s55b_le += fabs(t) <= mpf(abs(u)) / q[n]; s55b_lt += fabs(t) < mpf(abs(u)) / q[n]
            tot += 1
        print(f'  W={W} u={u} v={v}: <= forms hold {s54_le}/{tot},{s55a_le}/{tot},{s55b_le}/{tot};'
              f' strict forms hold {s54_lt}/{tot},{s55a_lt}/{tot},{s55b_lt}/{tot}')
        check(f'A le W={W} u={u}', s54_le == s55a_le == s55b_le == tot)
        exp_strict = 0 if u == 0 else tot
        check(f'A strict pattern W={W} u={u}', s54_lt == s55a_lt == s55b_lt == exp_strict)

print('Part B: (E1)-(E4), (E4_0) strict with K_functional = 0 (K+1 = 1)')
for W in [(1, 9, 9), (2,), (3, 1), ()]:
    l, a, p, q, eps, nk, A = setup(W)
    K = cont(W); sigma = cont(W[:-1]) if l >= 1 else 1
    c = [cont(W[:i - 1]) for i in range(1, l + 1)]
    for (u, v) in [(0, 3), (1, 0), (-2, 1), (5, -7)]:
        Kp1 = 1  # K_functional(beta) = 0 for beta in the lattice (sec 5.5 =>)
        # k0: R_n <= K+1 = 1 for n >= n_{k0}; here R_n = |u|/q_n eventually
        k0 = None
        for k in range(1, NB_TEST):
            if all(fabs(y_lattice(u, v, eps, n)) / (q[n] * fabs(eps[n])) <= Kp1 for n in range(nk(k), nk(NB_TEST))):
                k0 = k; break
        Y = lambda n: y_lattice(u, v, eps, n)
        cnt = 0
        for k in range(k0, NB_TEST - 3):
            n = nk(k); th = q[n] * fabs(eps[n])
            t = A(k) * Y(n)
            check(f'E1a W={W} u={u} k={k}', fabs(Y(n)) < mpf(Kp1) / A(k))
            check(f'E1b W={W} u={u} k={k}', fabs(t) < Kp1)
            if l == 0:
                t1 = A(k + 1) * Y(nk(k + 1))
                lhs = dist_Z(t1)
                check(f'E4_0 W={W} u={u} k={k}', lhs <= fabs(Y(nk(k + 2))) + fabs(Y(n)))
                check(f'E4_0s W={W} u={u} k={k}', lhs < Kp1 * (mpf(1) / A(k + 2) + mpf(1) / A(k)))
                cnt += 1
                continue
            K2l = Kint(W, 2, l)
            dK_ = lambda x: min(x % K, K - x % K)

            def gs(kk):
                yy = K * Y(nk(kk) + 1); s = int(nint(yy)); return s, Y(nk(kk) + 1) - mpf(s) / K
            s_k, g_k = gs(k); s_k1, g_k1 = gs(k + 1)
            dist2 = dist_Z(K * Y(n + 1))
            E2 = Kp1 * (mpf(1) / A(k + 1) + mpf(K2l) / A(k))
            check(f'E2 W={W} u={u} k={k}', dist2 < E2 and dist2 < mpf(1) / 2)
            for i in range(1, l + 1):
                ci = c[i - 1]; K2i = Kint(W, 2, i - 1)
                e = ci * g_k + K2i * Y(n)
                lhs = fabs(fabs(Y(n + i)) - mpf(dK_(ci * (s_k % K))) / K)
                E3 = Kp1 * (mpf(ci) / K * (mpf(1) / A(k + 1) + mpf(K2l) / A(k)) + mpf(K2i) / A(k))
                check(f'E3 W={W} u={u} k={k} i={i}', lhs <= fabs(e) + mpf(10) ** -300 and fabs(e) < E3)
            e_l = c[l - 1] * g_k + Kint(W, 2, l - 1) * Y(n)
            t1 = A(k + 1) * Y(nk(k + 1))
            lhs4 = dist_Z(t1 - mpf((s_k1 % K) - sigma * (s_k % K)) / K)
            E4 = Kp1 * (mpf(1) / K * (mpf(1) / A(k + 2) + mpf(K2l) / A(k + 1))
                        + mpf(sigma) / K * (mpf(1) / A(k + 1) + mpf(K2l) / A(k)) + mpf(Kint(W, 2, l - 1)) / A(k))
            check(f'E4 W={W} u={u} k={k}', lhs4 <= fabs(g_k1) + fabs(e_l) + mpf(10) ** -300
                  and fabs(g_k1) + fabs(e_l) < E4)
            cnt += 1
        print(f'  W={W} u={u} v={v}: k0={k0}, blocks checked={cnt}')

print("Part C: (d3) note -- T_max > 0, T'_max = 0 (beta = 0)")
W = (1, 9, 9); l, a, p, q, eps, nk, A = setup(W)
K = cont(W); sigma = cont(W[:-1]); r0 = 90; rt0 = r0 % K
T = {1: -sigma * rt0}; T.update({k: 0 for k in range(2, NB_TEST)})
assert (T[1] - (0 - sigma * r0)) % K == 0           # T_1 == r_1 - sigma r_0 (mod K) with r_1 = 0
Tp = dict(T); Tp[1] = T[1] + sigma * rt0
Tmax = max(abs(x) for x in list(T.values()) + [Tp[1]]); Tpmax = max(abs(x) for x in Tp.values())
print(f'  K={K} sigma={sigma} r0={r0}: T_1={T[1]}, T\'_1={Tp[1]}, T_max={Tmax}, T\'_max={Tpmax}; beta = 0 exactly')
okT = okTp_strict = okTp_le = 0; tot = 0
for k in range(2, NB_TEST - 2):
    for rhs_fac in [q[nk(k - 1)] / mpf(q[nk(k) + 1]), q[nk(k)] / mpf(q[nk(k + 1) + 1])]:
        lhs = 0  # all x_j = 0, so every E^past, E^fut term is exactly 0
        okT += lhs < 4 * Tmax * rhs_fac; okTp_strict += lhs < 4 * Tpmax * rhs_fac; okTp_le += lhs <= 4 * Tpmax * rhs_fac
        tot += 1
print(f'  strict with T_max holds {okT}/{tot}; strict with T\'_max holds {okTp_strict}/{tot}; <= with T\'_max holds {okTp_le}/{tot}')
check('C', Tmax > 0 and Tpmax == 0 and okT == tot and okTp_strict == 0 and okTp_le == tot)

print('FAILURES:', fails if fails else 'none')
print('ALL CHECKS PASSED' if not fails else 'SOME CHECKS FAILED')
