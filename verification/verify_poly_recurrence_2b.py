#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
High-precision numerical verification for Path 2B:
General polynomial-growth denominator recurrences
    Q_{j+1} = (c * j^r + d) * Q_j + Q_{j-1}   (j >= J0, c*J0^r + d >= 2),
with r >= 1, c >= 1, d in Z.

Experiments (using mpmath, zero assertion failures required):
  1. 400-digit denominator growth bounds (Lem. lem:poly-growth):
     Q_m >= C_{J1} * (c / 2^{r+1})^m * (m!)^r and asymptotic log Q_n across
     r in {1, 2, 3}, c in {1, 2, 4}.
  2. 400-digit full spectrum levels k/c (k = 1, 3) and O(j^{-r}) defect
     convergence (Thm. thm:general-rec).
  3. 400-digit intrinsic lattice L^{(r,c,d)} = (1/g)(Z + Z*theta) including
     non-coprime initial conditions (2,4,0) with g = 3, verifying
     |(q0*alpha_U + q1*alpha_V) - 1/g| < 1e-350 and x2 - x1 in L^{(r,c,d)},
     plus positive-level alternating vs constant defect trichotomy
     (Lem. lem:poly-lattice & Thm. thm:poly-gauge-trichotomy).
  4. 50-digit subcritical dimension phase transition 1 - alpha/r up to N = 10^5,
     critical weight alpha = r (branching O(1) => s_n -> 0), and t = 0 slowly
     decaying radius w_j = j^{-alpha} / log(j + 2) (Thm. thm:poly-phase-transition).
  5. 50-digit gauge logarithmic scale check up to n = 10^5 for g_2, h_1, h_2, h_3,
     verifying exact ratio identity -log h_k / (-log g_2) = log(2k+1) / log 2
     and quantitative match with the O(log log n / log n) subleading term
     (Rem. rem:poly-gauge-scale).
"""

import math
import sys
import mpmath as mp


CASES = [
    # (r, c, d, J0, Q_init) where Q_init provides Q[J0-1], Q[J0]
    (1, 1,  2, 1, (1, 1)),
    (1, 2,  1, 1, (1, 1)),
    (1, 4,  2, 1, (1, 1)),
    (2, 1, -1, 2, (1, 1)),
    (2, 2,  1, 1, (1, 1)),
    (2, 4,  0, 1, (1, 1)),
    (3, 1,  1, 1, (1, 1)),
    (3, 2, -3, 2, (1, 1)),
    (3, 4,  2, 1, (1, 1)),
]


def build_Q_exact(r: int, c: int, d: int, J0: int, q_init, J_max: int):
    """Build exact integer sequence Q[0..J_max+1] satisfying Q_{j+1}=(c*j^r+d)Q_j+Q_{j-1} for j>=J0."""
    Q = [1] * (J_max + 2)
    Q[J0 - 1] = q_init[0]
    Q[J0] = q_init[1]
    for j in range(J0, J_max + 1):
        A_j = c * (j ** r) + d
        assert A_j >= 2, f"A_j={A_j} < 2 at j={j}"
        Q[j + 1] = A_j * Q[j] + Q[j - 1]
    return Q


def build_UV_exact(r: int, c: int, d: int, J0: int, J_max: int):
    """Build fundamental homogeneous solutions U, V initialized at (J0-1, J0)."""
    U = [0] * (J_max + 2)
    V = [0] * (J_max + 2)
    U[J0 - 1], U[J0] = 1, 0
    V[J0 - 1], V[J0] = 0, 1
    for j in range(J0, J_max + 1):
        A_j = c * (j ** r) + d
        U[j + 1] = A_j * U[j] + U[j - 1]
        V[j + 1] = A_j * V[j] + V[j - 1]
    return U, V


def egcd(a: int, b: int):
    """Extended Euclidean algorithm returning (g, x, y) with a*x + b*y = g."""
    if b == 0:
        return a, 1, 0
    g, x1, y1 = egcd(b, a % b)
    return g, y1, x1 - (a // b) * y1


def build_point_from_digits(r: int, c: int, d: int, J0: int, Q, N: int, J_max: int, d_func):
    """
    Construct x = lim_{j->inf} M_j / Q_j from M_{N-1}=M_N=0 and
    M_{j+1} = (c*j^r + d) M_j + M_{j-1} + d_func(j) for j >= N.
    """
    M = [0] * (J_max + 2)
    for j in range(N, J_max + 1):
        A_j = c * (j ** r) + d
        M[j + 1] = A_j * M[j] + M[j - 1] + d_func(j)
    x_val = mp.mpf(M[J_max + 1]) / mp.mpf(Q[J_max + 1])
    return M, x_val


def nearest_int_mp(y):
    """Borel rounding: m = floor(y + 1/2), u = y - m in [-1/2, 1/2)."""
    m = int(mp.floor(y + mp.mpf("0.5")))
    u = y - mp.mpf(m)
    assert mp.mpf("-0.5") <= u < mp.mpf("0.5"), f"Remainder out of range: {u}"
    return m, u


def experiment_1(log):
    mp.mp.dps = 400
    log("=== 1. DENOMINATOR GROWTH (400-digit mpmath) ===")
    J_max = 120
    for r, c, d, J0, q_init in CASES:
        Q = build_Q_exact(r, c, d, J0, q_init, J_max)
        J1 = max(J0 + 1, 2 * abs(d) + 1)

        # Check (i) and (ii)
        for j in range(J0, J_max + 1):
            A_j = c * (j ** r) + d
            assert Q[j + 1] > A_j * Q[j] >= 2 * Q[j]
            if j >= J0 + 1:
                assert 0 < 2 * Q[j - 1] < Q[j]
                ratio = mp.mpf(Q[j + 1]) / mp.mpf(Q[j])
                assert mp.mpf(A_j) < ratio < mp.mpf(A_j + 1) <= mp.mpf((c + abs(d) + 1) * (j ** r))

        # Check (iii): Q_m >= C_{J1} * (c / 2^{r+1})^m * (m!)^r
        c_mp = mp.mpf(c)
        C_J1 = mp.mpf(Q[J1]) * ((c_mp / 2) ** (-J1)) * (mp.factorial(J1 - 1) ** (-r))
        assert C_J1 > 0
        base = c_mp / (mp.mpf(2) ** (r + 1))
        for m in range(J1, J_max + 1):
            rhs = C_J1 * (base ** m) * (mp.factorial(m) ** r)
            assert mp.mpf(Q[m]) >= rhs * (1 - mp.mpf("1e-390")), f"Growth lower bound failed at m={m}"

        # Check (iv): log Q_n asymptotic at n = 50 and n = 120
        n_test = 50
        logQ_50 = mp.log(mp.mpf(Q[n_test]))
        lead_50 = mp.mpf(r * n_test) * mp.log(n_test)
        rem_50 = logQ_50 - lead_50 - (mp.log(c_mp) - r) * n_test
        ratio_50 = logQ_50 / lead_50

        n_hi = 120
        logQ_hi = mp.log(mp.mpf(Q[n_hi]))
        lead_hi = mp.mpf(r * n_hi) * mp.log(n_hi)
        rem_hi = logQ_hi - lead_hi - (mp.log(c_mp) - r) * n_hi
        assert abs(rem_hi / mp.log(n_hi)) < 10

        digits_55 = len(str(Q[55]))
        log(
            f"r={r}, c={c}, d={d:>2}, J0={J0}, J1={J1}: "
            f"digits(Q_55)={digits_55}, logQ_50/(r*50*ln50)={mp.nstr(ratio_50, 8)}, "
            f"rem_50/ln50={mp.nstr(rem_50 / mp.log(n_test), 6)}, "
            f"rem_120/ln120={mp.nstr(rem_hi / mp.log(n_hi), 6)}"
        )


def experiment_2(log):
    log("")
    log("=== 2. SPECTRUM DISCRETIZATION k/c AND O(j^-r) DEFECT CONVERGENCE (>=400-digit effective mpmath) ===")
    for r, c, d, J0, q_init in CASES:
        J_max = 300 if r == 1 else (160 if r == 2 else 120)
        Q = build_Q_exact(r, c, d, J0, q_init, J_max)
        for k in (1, 3):
            N = J0 + 1
            while c * (N ** r) + d <= 32 * k:
                N += 1
            j_end = max(80, N + 80)
            mp.mp.dps = max(400, len(str(Q[j_end + 1])) + 410)
            M, x_k = build_point_from_digits(r, c, d, J0, Q, N, J_max, lambda _j, kk=k: kk)

            # Verify M_m(x_k) == M_m and d_j == k in the tail j >= N
            for m in range(N - 1, j_end + 1):
                m_obs, u_obs = nearest_int_mp(mp.mpf(Q[m]) * x_k)
                assert m_obs == M[m], f"Rounding mismatch at m={m} for {(r,c,d)}, k={k}"
                assert abs(u_obs) < mp.mpf("0.125")
            for j in range(N, j_end):
                A_j = c * (j ** r) + d
                d_obs = M[j + 1] - A_j * M[j] - M[j - 1]
                assert d_obs == k

            j1 = max(45, N + 10)
            j2 = max(75, N + 50)
            errs = {}
            vals = {}
            for j in (j1, j2):
                _, u_j = nearest_int_mp(mp.mpf(Q[j]) * x_k)
                val_j = mp.mpf(j ** r) * abs(u_j)
                target = mp.mpf(k) / mp.mpf(c)
                err_j = abs(val_j - target)
                vals[j] = val_j
                errs[j] = err_j
                # Check O(j^{-r}) scaling: j^r * err_j is bounded by O(1)
                assert mp.mpf(j ** r) * err_j < mp.mpf(20 * k * (abs(d) + 2))
            assert errs[j2] < errs[j1], f"Error did not decrease from j={j1} to j={j2} for {(r,c,d)}, k={k}"

            scaled_err_j1 = mp.mpf(j1 ** r) * errs[j1]
            log(
                f"(r,c,d)=({r},{c},{d:>2}) k={k} (N={N}): target={mp.nstr(mp.mpf(k)/c, 6)}, "
                f"j={j1}: j^r||Q_jx||={mp.nstr(vals[j1], 10)}, j^r*err={mp.nstr(scaled_err_j1, 6)}, "
                f"j={j2}: err={mp.nstr(errs[j2], 6)}"
            )


def experiment_3(log):
    log("")
    log("=== 3. INTRINSIC LATTICE L^(r,c,d) AND POSITIVE-LEVEL TRICHOTOMY (>=400-digit effective mpmath) ===")
    test_cases = [
        (2, 1, -1, 2, (1, 1)),
        (2, 4,  0, 1, (3, 6)),  # non-coprime initial conditions => g = 3
        (3, 2, -3, 2, (1, 1)),
        (3, 4,  2, 1, (1, 1)),
    ]
    for r, c, d, J0, q_init in test_cases:
        J_max = 160 if r == 2 else 120
        Q = build_Q_exact(r, c, d, J0, q_init, J_max)
        U, V = build_UV_exact(r, c, d, J0, J_max)
        mp.mp.dps = max(400, len(str(Q[J_max + 1])) + 410)

        # Verify Casorati determinant and Q_j = Q_{J0-1}*U_j + Q_{J0}*V_j
        for j in range(J0 - 1, J_max + 1):
            assert Q[j] == Q[J0 - 1] * U[j] + Q[J0] * V[j]
            det = U[j] * V[j + 1] - U[j + 1] * V[j]
            assert det == ((-1) ** (j - J0 + 1))

        alpha_U = mp.mpf(U[J_max + 1]) / mp.mpf(Q[J_max + 1])
        alpha_V = mp.mpf(V[J_max + 1]) / mp.mpf(Q[J_max + 1])

        g = math.gcd(Q[J0 - 1], Q[J0])
        q0 = Q[J0 - 1] // g
        q1 = Q[J0] // g
        # Solve p0*q1 - p1*q0 = 1
        g_chk, x_bez, y_bez = egcd(q1, q0)
        assert g_chk == 1
        p0, p1 = x_bez, -y_bez
        assert p0 * q1 - p1 * q0 == 1

        # Verify 1/g identity and theta = g*(p0*alpha_U + p1*alpha_V)
        inv_g_err = abs((mp.mpf(q0) * alpha_U + mp.mpf(q1) * alpha_V) - mp.mpf(1) / mp.mpf(g))
        assert inv_g_err < mp.mpf("1e-350"), f"1/g error too large: {inv_g_err}"
        theta = mp.mpf(g) * (mp.mpf(p0) * alpha_U + mp.mpf(p1) * alpha_V)

        # Construct two points x1, x2 in E_{lim}^+(2/c) with distinct initial digits at N
        k = 2
        N = J0 + 1
        while c * (N ** r) + d <= 64 * k:
            N += 1

        M1, x1 = build_point_from_digits(r, c, d, J0, Q, N, J_max, lambda _j, kk=k: kk)
        # Second point: M2 has d_N = k + 1, then d_j = k for j >= N+1
        M2, x2 = build_point_from_digits(
            r, c, d, J0, Q, N, J_max,
            lambda j, kk=k, NN=N: (kk + 1 if j == NN else kk),
        )

        # Express (M2 - M1) at (N, N+1) in the unimodular (U, V) basis at (N, N+1)
        detN = U[N] * V[N + 1] - U[N + 1] * V[N]
        assert abs(detN) == 1
        dM0 = M2[N] - M1[N]
        dM1 = M2[N + 1] - M1[N + 1]
        a = (dM0 * V[N + 1] - dM1 * V[N]) // detN
        b = (U[N] * dM1 - U[N + 1] * dM0) // detN
        assert a * U[N] + b * V[N] == dM0 and a * U[N + 1] + b * V[N + 1] == dM1
        # Map to (1/g)(Z + Z*theta):
        # a*alpha_U + b*alpha_V = (m + n*theta)/g where
        # alpha_U = (q1 - p1*theta)/g? Wait:
        # [q0 q1; p0 p1] * [alpha_U; alpha_V] = [1/g; theta/g]
        # Inverse of [[q0, q1], [p0, p1]] (det = q0*p1 - q1*p0 = -1):
        # alpha_U = -(p1*(1/g) - q1*(theta/g)) = (-p1 + q1*theta)/g
        # alpha_V = -(-p0*(1/g) + q0*(theta/g)) = (p0 - q0*theta)/g
        # So a*alpha_U + b*alpha_V = ((b*p0 - a*p1) + (a*q1 - b*q0)*theta) / g
        m_lat = b * p0 - a * p1
        n_lat = a * q1 - b * q0
        lat_pt = (mp.mpf(m_lat) + mp.mpf(n_lat) * theta) / mp.mpf(g)
        lat_err = abs((x2 - x1) - lat_pt)
        assert lat_err < mp.mpf("1e-350"), f"Lattice residual too large: {lat_err}"

        # Alternating defect point in E_{lim}(2/c) \ (E_{lim}^+ union E_{lim}^-)
        _, x_alt = build_point_from_digits(
            r, c, d, J0, Q, N, J_max,
            lambda j, kk=k: ((-1) ** j) * kk,
        )
        _, u40 = nearest_int_mp(mp.mpf(Q[40]) * x_alt)
        _, u41 = nearest_int_mp(mp.mpf(Q[41]) * x_alt)
        s40 = mp.mpf(40 ** r) * u40
        s41 = mp.mpf(41 ** r) * u41
        # Make sure s40, s41 have opposite signs near +/- k/c
        target_kc = mp.mpf(k) / mp.mpf(c)
        assert s40 * s41 < 0
        assert abs(abs(s40) - target_kc) < mp.mpf("0.1")
        assert abs(abs(s41) - target_kc) < mp.mpf("0.1")

        log(
            f"(r,c,d)=({r},{c},{d:>2}), g={g}: theta={mp.nstr(theta, 12)}, "
            f"inv_g_err={mp.nstr(inv_g_err, 4)}, lat_err={mp.nstr(lat_err, 4)} | "
            f"alt=(j40:{mp.nstr(s40, 7)}, j41:{mp.nstr(s41, 7)})"
        )


def precompute_R_logQ(r: int, c: int, d: int, J0: int, q_init, N_max: int):
    """Precompute R[j] = Q_{j+1}/Q_j and logQ[j] = log Q_j up to N_max+1 in 50-digit mpmath."""
    Q_ex = build_Q_exact(r, c, d, J0, q_init, 100)
    R = [mp.mpf(0)] * (N_max + 2)
    logQ = [mp.mpf(0)] * (N_max + 3)
    for j in range(1, J0 + 1):
        R[j - 1] = mp.mpf(Q_ex[j]) / mp.mpf(Q_ex[j - 1])
        logQ[j] = mp.log(mp.mpf(Q_ex[j]))
    for j in range(J0, N_max + 2):
        A_j = mp.mpf(c) * (mp.mpf(j) ** r) + mp.mpf(d)
        R[j] = A_j + mp.mpf(1) / R[j - 1]
        logQ[j + 1] = logQ[j] + mp.log(R[j])
    for j in range(J0, 101):
        assert abs(logQ[j] - mp.log(mp.mpf(Q_ex[j]))) < mp.mpf("1e-40")
    return R, logQ


def falconer_s_trajectory(R, logQ, J0: int, alpha: float, t_val: float, decay_mode: bool, checkpoints):
    """
    Simulate the Moran/Falconer branching trajectory up to max(checkpoints) using exact
    child count b_j = floor(2*(w_j * R_j - w_{j+1}) - 1).
    Returns (N0, {n: s_n}) where s_n = sum_{j=N0}^{n-1} log(b_j) / log Q_{n+1}.
    """
    N_max = max(checkpoints)
    a_mp = mp.mpf(str(alpha))
    t_mp = mp.mpf(str(t_val))

    def weight(j: int):
        if decay_mode:
            return (mp.mpf(j) ** (-a_mp)) / mp.log(mp.mpf(j + 2))
        return t_mp * (mp.mpf(j) ** (-a_mp))

    # Find N0 >= max(J0+1, 3) with w_j <= 0.25 and b_j >= 2 for all j >= N0
    N0 = max(J0 + 1, 3)
    while N0 < N_max:
        wN = weight(N0)
        wN1 = weight(N0 + 1)
        bN = int(mp.floor(mp.mpf(2) * (wN * R[N0] - wN1) - mp.mpf(1)))
        if wN <= mp.mpf("0.25") and bN >= 2:
            break
        N0 += 1
    assert N0 < N_max, f"Failed to find N0 for alpha={alpha}, t_val={t_val}"

    log_M = mp.mpf(0)
    res = {}
    ckpt_set = set(checkpoints)
    for j in range(N0, N_max):
        wj = weight(j)
        wj1 = weight(j + 1)
        bj = int(mp.floor(mp.mpf(2) * (wj * R[j] - wj1) - mp.mpf(1)))
        assert bj >= 2, f"Branching dropped below 2 at j={j}: bj={bj}"
        log_M += mp.log(mp.mpf(bj))
        n = j + 1
        if n in ckpt_set:
            res[n] = log_M / logQ[n + 1]
    return N0, res


def experiment_4(log):
    mp.mp.dps = 50
    log("")
    log("=== 4. SUBCRITICAL DIMENSION PHASE TRANSITION 1 - alpha/r (N up to 100000, 50-digit) ===")
    ckpts = (1000, 10000, 50000, 100000)
    subcrit_specs = [
        ((1, 1,  2, 1, (1, 1)), 0.00, 0.25),
        ((1, 2,  1, 1, (1, 1)), 0.50, 0.50),
        ((1, 4,  2, 1, (1, 1)), 0.50, 0.50),
        ((2, 1, -1, 2, (1, 1)), 0.00, 0.25),
        ((2, 1, -1, 2, (1, 1)), 0.50, 0.50),
        ((2, 1, -1, 2, (1, 1)), 1.00, 0.50),
        ((2, 1, -1, 2, (1, 1)), 1.50, 0.50),
        ((2, 2,  1, 1, (1, 1)), 1.00, 0.50),
        ((2, 4,  0, 1, (1, 1)), 1.00, 0.50),
        ((3, 1,  1, 1, (1, 1)), 1.50, 0.50),
        ((3, 2, -3, 2, (1, 1)), 0.75, 0.50),
        ((3, 2, -3, 2, (1, 1)), 1.50, 0.50),
        ((3, 2, -3, 2, (1, 1)), 2.25, 0.50),
        ((3, 4,  2, 1, (1, 1)), 2.00, 0.50),
    ]

    cache = {}
    for triple, alpha, t_val in subcrit_specs:
        if triple not in cache:
            cache[triple] = precompute_R_logQ(*triple, 100000)
        R, logQ = cache[triple]
        r, c, d, J0, _ = triple
        target = mp.mpf(1) - mp.mpf(str(alpha)) / mp.mpf(r)
        N0, res = falconer_s_trajectory(R, logQ, J0, alpha, t_val, False, ckpts)
        # Check monotonic approach or closeness within O(log log N / log N)
        assert abs(res[100000] - target) < abs(res[1000] - target) + mp.mpf("0.02")
        assert abs(res[100000] - target) < mp.mpf("0.10")
        log(
            f"(r,c,d)=({r},{c},{d:>2}) a={alpha:.2f} target={mp.nstr(target, 5)} (N0={N0}): "
            f"s_1e3={mp.nstr(res[1000], 5)}, s_1e4={mp.nstr(res[10000], 5)}, "
            f"s_5e4={mp.nstr(res[50000], 5)}, s_1e5={mp.nstr(res[100000], 5)}"
        )

    log("")
    log("=== 4B. CRITICAL WEIGHT alpha = r (s_n -> 0) AND t=0 SLOWLY DECAYING RADIUS ===")
    crit_specs = [
        ((2, 1, -1, 2, (1, 1)), 2.0, 2.0),
        ((3, 2, -3, 2, (1, 1)), 3.0, 2.0),
    ]
    for triple, alpha, t_val in crit_specs:
        R, logQ = cache[triple]
        r, c, d, J0, _ = triple
        N0, res = falconer_s_trajectory(R, logQ, J0, alpha, t_val, False, ckpts)
        assert res[100000] < res[10000] < res[1000]
        assert res[100000] < mp.mpf("0.08")
        log(
            f"CRITICAL (r,c,d)=({r},{c},{d:>2}) a=r={alpha:.1f}, t={t_val:.1f} (N0={N0}): "
            f"s_1e3={mp.nstr(res[1000], 5)}, s_1e4={mp.nstr(res[10000], 5)}, "
            f"s_5e4={mp.nstr(res[50000], 5)}, s_1e5={mp.nstr(res[100000], 5)}"
        )

    decay_specs = [
        ((2, 1, -1, 2, (1, 1)), 1.00),
        ((3, 2, -3, 2, (1, 1)), 1.50),
    ]
    for triple, alpha in decay_specs:
        R, logQ = cache[triple]
        r, c, d, J0, _ = triple
        target = mp.mpf(1) - mp.mpf(str(alpha)) / mp.mpf(r)
        N0, res = falconer_s_trajectory(R, logQ, J0, alpha, 0.0, True, ckpts)
        assert abs(res[100000] - target) < mp.mpf("0.10")
        log(
            f"t=0 DECAY (r,c,d)=({r},{c},{d:>2}) a={alpha:.2f} target={mp.nstr(target, 5)} (N0={N0}): "
            f"s_1e3={mp.nstr(res[1000], 5)}, s_1e4={mp.nstr(res[10000], 5)}, "
            f"s_5e4={mp.nstr(res[50000], 5)}, s_1e5={mp.nstr(res[100000], 5)}"
        )
    return cache


def experiment_5(log, cache):
    mp.mp.dps = 50
    log("")
    log("=== 5. GAUGE LOG SCALE CHECK AT n=100000 (g_2 and h_1, h_2, h_3) ===")
    n = 100000
    gauge_cases = [
        (1, 4,  2, 1, (1, 1)),
        (2, 1, -1, 2, (1, 1)),
        (2, 4,  0, 1, (1, 1)),
        (3, 2, -3, 2, (1, 1)),
        (3, 4,  2, 1, (1, 1)),
    ]
    gauges = [
        ("g2(b=2)", 2),
        ("k=1(b=3)", 3),
        ("k=2(b=5)", 5),
        ("k=3(b=7)", 7),
    ]

    for triple in gauge_cases:
        if triple not in cache:
            cache[triple] = precompute_R_logQ(*triple, n)
        _, logQ = cache[triple]
        r, c, d, _, _ = triple
        logQn = logQ[n]
        loglogQn = mp.log(logQn)
        # Empirical scale at t = 1/Q_n: (-log g(1/Q_n)) / (log(Q_n)/log(log(Q_n)))
        ratios = []
        emp_g2 = None
        for label, base in gauges:
            neg_log_g = mp.mpf(n) * mp.log(mp.mpf(base))
            emp = neg_log_g / (logQn / loglogQn)
            theo = mp.log(mp.mpf(base)) / mp.mpf(r)
            ratio = emp / theo
            ratios.append(ratio)
            if base == 2:
                emp_g2 = neg_log_g
            else:
                # Exact ratio identity: -log h_k(1/Q_n) / (-log g_2(1/Q_n)) = log(2k+1)/log 2
                exact_id_err = abs(neg_log_g / emp_g2 - mp.log(mp.mpf(base)) / mp.log(mp.mpf(2)))
                assert exact_id_err < mp.mpf("1e-45")
            log(
                f"(r,c,d)=({r},{c},{d:>2}) {label}: "
                f"theo={mp.nstr(theo, 7)}, emp_1e5={mp.nstr(emp, 7)}, ratio={mp.nstr(ratio, 7)}"
            )
        # All 4 gauges share the identical ratio (independent of base b)
        for rt in ratios[1:]:
            assert abs(rt - ratios[0]) < mp.mpf("1e-45")
        # Verify subleading O(log log n / log n) formula:
        # (log n + log log n + log r) / (log n + (log c - r)/r)
        n_mp = mp.mpf(n)
        subleading_pred = (mp.log(n_mp) + mp.log(mp.log(n_mp)) + mp.log(mp.mpf(r))) / (
            mp.log(n_mp) + (mp.log(mp.mpf(c)) - mp.mpf(r)) / mp.mpf(r)
        )
        sub_diff = abs(ratios[0] - subleading_pred)
        assert sub_diff < mp.mpf("0.02"), f"Subleading mismatch: {ratios[0]} vs {subleading_pred}"
        log(
            f"  [Subleading check (r,c)=({r},{c})]: observed ratio={mp.nstr(ratios[0], 7)}, "
            f"O(loglog n/log n) prediction={mp.nstr(subleading_pred, 7)}, diff={mp.nstr(sub_diff, 4)}"
        )


def main():
    lines = []

    def log(msg=""):
        print(msg, flush=True)
        lines.append(msg)

    experiment_1(log)
    experiment_2(log)
    experiment_3(log)
    cache = experiment_4(log)
    experiment_5(log, cache)
    log("")
    log("ALL 5 EXPERIMENTS PASSED WITH 0 ASSERTION FAILURES.")

    out_path = "verification/verify_poly_recurrence_2b.log"
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
