"""Audit §4 Lemma 0 (self-proved half of KL 1991 Thm 1), checked in its *local* form used by step 0.2:

  for n >= 1:  m_n := a_{n+1} rho_n + rho_{n-1} - rho_{n+1} (rho = round(q beta))
               equals y_{n+1} - a_{n+1} y_n - y_{n-1}            (identity 0.1)
  and  m_n != 0  ==>  max(R_{n-1}, R_n, R_{n+1}) >= 1/4          (contrapositive of 0.2)

and step 0.3/0.4: if m_n = 0 for all n in a window [n*, M], then rho_n = u p_n + v q_n there with the
(u,v) computed from the unimodular 2x2 system (exact integers).

alpha: golden ratio (bounded type), block-Hurwitz [0;10k,W,...] for several W, random partial quotients.
beta: random reals (mp), random lattice points + tiny perturbation, and lattice points themselves.
All decisive comparisons are made at mp.dps=300 with a 1e-250 safety margin (reported).
"""
import random, sys, os
import mpmath as mp

random.seed(4)
mp.mp.dps = 300
M = 120


def cf_value(a):
    x = mp.mpf(a[-1])
    for t in reversed(a[:-1]):
        x = t + 1 / x
    return x


def alphas():
    yield "golden", [1] * 400
    for W in [(), (1, 1), (5, 1, 5), (2, 3)]:
        a = [0]
        k = 1
        while len(a) < 400:
            a.append(10 * k); a.extend(W); k += 1
        yield f"blockW={W}", a
    for s in range(3):
        yield f"random{s}", [0] + [random.choice([1, 1, 2, 3, 7, 30]) for _ in range(400)]


stats = dict(n_checked=0, nonzero_m=0, viol=0, identity_fail=0, closest_margin=mp.inf, window_tests=0, window_fail=0)
for name, a in alphas():
    p = [a[0]]; q = [1]
    for n in range(1, len(a)):
        p.append(a[n] * p[-1] + (p[-2] if n >= 2 else 1))
        q.append(a[n] * q[-1] + (q[-2] if n >= 2 else 0))
    mp.mp.dps = 3 * len(str(q[M + 3])) + 200   # >= 2 log10 q_{M+3} + margin; tail of a[] far beyond
    alpha = cf_value(a)
    print(f"{name}: dps={mp.mp.dps}, log10 q_M ~ {len(str(q[M]))}")
    theta = [q[n] * mp.fabs(q[n] * alpha - p[n]) for n in range(M + 2)]
    betas = []
    for _ in range(60):
        betas.append(mp.rand() * 3 - 1)
    for _ in range(30):
        u, v = random.randint(-5, 5), random.randint(-5, 5)
        betas.append(u * alpha + v + mp.mpf(10) ** (-random.randint(3, 40)) * (mp.rand() - mp.mpf(0.5)))
    for _ in range(10):
        u, v = random.randint(-5, 5), random.randint(-5, 5)
        betas.append(u * alpha + v)
    # adversarial low-R points: beta = (1/D) sum_j x_j eps_{m_j}  (sparse, small x_j, D in 1..6)
    epsl = [q[n] * alpha - p[n] for n in range(M + 2)]
    for _ in range(80):
        D = random.randint(1, 6)
        js = sorted(random.sample(range(5, M - 5), random.randint(1, 6)))
        betas.append(sum(random.choice([-2, -1, 1, 2]) * epsl[j] for j in js) / D)
    for beta in betas:
        rho = [mp.nint(q[n] * beta) for n in range(M + 2)]
        y = [q[n] * beta - rho[n] for n in range(M + 2)]
        R = [mp.fabs(y[n]) / theta[n] for n in range(M + 2)]
        zero_run_start = None
        for n in range(1, M + 1):
            m = a[n + 1] * rho[n] + rho[n - 1] - rho[n + 1]
            if mp.fabs(m - (y[n + 1] - a[n + 1] * y[n] - y[n - 1])) > mp.mpf(10) ** (-(mp.mp.dps // 3)):
                stats["identity_fail"] += 1
            stats["n_checked"] += 1
            if m != 0:
                stats["nonzero_m"] += 1
                mx = max(R[n - 1], R[n], R[n + 1])
                stats["closest_margin"] = min(stats["closest_margin"], mx - mp.mpf(1) / 4)
                if mx < mp.mpf(1) / 4:
                    stats["viol"] += 1
                    print("VIOLATION", name, n, mp.nstr(mx, 10))
        # 0.3/0.4: take the last maximal run of m_n == 0 of length >= 3 and solve for (u,v)
        ms = [int(a[n + 1] * rho[n] + rho[n - 1] - rho[n + 1]) for n in range(1, M + 1)]
        n_star = None
        for n in range(M, 0, -1):
            if ms[n - 1] != 0:
                n_star = n + 1
                break
        if n_star is None:
            n_star = 1
        if n_star <= M - 3:
            ns = n_star
            det = p[ns] * q[ns + 1] - q[ns] * p[ns + 1]
            r0, r1 = int(rho[ns]), int(rho[ns + 1])
            u = (r0 * q[ns + 1] - q[ns] * r1) // det
            v = (p[ns] * r1 - r0 * p[ns + 1]) // det
            stats["window_tests"] += 1
            ok = all(int(rho[n]) == u * p[n] + v * q[n] for n in range(ns, M + 2))
            if not ok:
                stats["window_fail"] += 1

print("=== audit_S2_3: Lemma 0 (local form) ===")
for k, v in stats.items():
    print(f"{k}: {mp.nstr(v, 8) if isinstance(v, mp.mpf) else v}")
print("closest_margin = min over nonzero m_n of max(R_{n-1},R_n,R_{n+1}) - 1/4  (>=0 required)")
print("category 4: finite numerical check, not a proof.")
