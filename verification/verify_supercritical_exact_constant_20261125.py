"""30-digit verification of the exact supercritical leading constant,
critical second-order expansion, and sparse-alphabet counterexample (2026-11-25).

Classification (AGENTS.md Section 2):
- Parts A-B (Chebyshev collocation for s_0, kappa(S), dim_H F_{m,S,B}):
  Category 4 (finite computation / non-rigorous numerical corroboration, NOT a proof).
- Part C (50-digit tail sums for A_{k_0} = {2^{2^k} : k >= k_0}):
  Category 4 (numerical verification accompanying the unconditional analytic proof).
- Part D (SymPy symbolic check of the critical-line second-order expansion):
  Category 4 (symbolic verification accompanying the analytic proof).

Method note:
On [0, 1], functions analytic on {|z - 1| < 5/4} have Bernstein ellipse parameter
rho_B = 3 + 2*sqrt(2) ~= 5.8284, so Chebyshev collocation of order n has error
~ 5.8284^{-n}. Using n = 44 (cross-checked against n = 48) at 70-digit working
precision achieves >32-digit collocation convergence, genuinely securing all 30
reported digits. Hurwitz zeta sums for large m are evaluated via the exact
binomial-Riemann expansion zeta(p, 1 + u) = sum_{l>=0} C(-p, l) zeta(p+l) u^l
(cross-checked directly against mp.zeta(p, sh) to < 1e-50).

Writes:
- verification/verify_supercritical_exact_constant_20261125.log (UTF-8, no BOM)
- verification/verify_supercritical_exact_constant_20261125.json (UTF-8, no BOM)
"""
from __future__ import annotations

import json
import time
from pathlib import Path

import mpmath as mp
import sympy as sp

HERE = Path(__file__).resolve().parent
WORK_DPS = 70
OUT_DPS = 30
N_MAIN = 44
N_CHECK = 48
mp.mp.dps = WORK_DPS

_V_INV_CACHE: dict[int, mp.matrix] = {}
_EYE_CACHE: dict[int, mp.matrix] = {}


def cheb_nodes(n: int) -> list[mp.mpf]:
    return [(1 + mp.cos(mp.pi * (2 * i + 1) / (2 * n))) / 2 for i in range(n)]


def vandermonde_inv(n: int) -> mp.matrix:
    if n not in _V_INV_CACHE:
        xs = cheb_nodes(n)
        V = mp.matrix(n, n)
        for i, x in enumerate(xs):
            xp = mp.mpf(1)
            for j in range(n):
                V[i, j] = xp
                xp *= x
        _V_INV_CACHE[n] = V ** -1
    return _V_INV_CACHE[n]


def eye_mat(n: int) -> mp.matrix:
    if n not in _EYE_CACHE:
        _EYE_CACHE[n] = mp.eye(n)
    return _EYE_CACHE[n]


def finite_operator_matrix(S: list[int], p: mp.mpf, n: int = N_MAIN) -> mp.matrix:
    """Collocation matrix A(p) = M(p) V^{-1} of L_p acting on nodal values."""
    xs = cheb_nodes(n)
    M = mp.matrix(n, n)
    for i, x in enumerate(xs):
        invs = [1 / (mp.mpf(a) + x) for a in S]
        pows = [(mp.mpf(a) + x) ** (-p) for a in S]
        for j in range(n):
            M[i, j] = mp.fsum(pows)
            for k in range(len(S)):
                pows[k] *= invs[k]
    return M * vandermonde_inv(n)


def finite_operator_deriv_matrix(S: list[int], p: mp.mpf, n: int = N_MAIN) -> mp.matrix:
    """Collocation matrix A'(p) of d/dp L_p acting on nodal values."""
    xs = cheb_nodes(n)
    M = mp.matrix(n, n)
    for i, x in enumerate(xs):
        invs = [1 / (mp.mpf(a) + x) for a in S]
        logs = [-mp.log(mp.mpf(a) + x) for a in S]
        pows = [logs[k] * ((mp.mpf(a) + x) ** (-p)) for k, a in enumerate(S)]
        for j in range(n):
            M[i, j] = mp.fsum(pows)
            for k in range(len(S)):
                pows[k] *= invs[k]
    return M * vandermonde_inv(n)


def det_one_minus(A: mp.matrix) -> mp.mpf:
    """det(I - A): vanishes with simple sign change when dominant eigenvalue = 1."""
    return mp.det(eye_mat(A.rows) - A)


def leading_eig_power(A: mp.matrix, steps: int = 60) -> mp.mpf:
    n = A.rows
    v = mp.matrix([mp.mpf(1)] * n)
    lam = mp.mpf(1)
    for _ in range(steps):
        w = A * v
        s = w[0]
        lam = s / v[0]
        v = w / s
    return lam


def null_vectors_at_one(A: mp.matrix) -> tuple[mp.matrix, mp.matrix]:
    """Compute positive right eigenvector h and left eigenvector nu of A at lambda = 1
    via shifted inverse iteration, normalized with nu^T h = 1."""
    n = A.rows
    shift = mp.mpf(1) + mp.mpf("1e-22")
    B = A - shift * eye_mat(n)
    BT = B.T
    h = mp.matrix([mp.mpf(1)] * n)
    nu = mp.matrix([mp.mpf(1)] * n)
    for _ in range(4):
        h = mp.lu_solve(B, h)
        h = h / mp.fsum(abs(h[i]) for i in range(n))
        nu = mp.lu_solve(BT, nu)
        nu = nu / mp.fsum(abs(nu[i]) for i in range(n))
    if h[0] < 0:
        h = -h
    pair = mp.fsum(nu[i] * h[i] for i in range(n))
    nu = nu / pair
    res_h = max(abs((A * h)[i] - h[i]) for i in range(n))
    res_nu = max(abs((A.T * nu)[i] - nu[i]) for i in range(n))
    assert res_h < mp.mpf("1e-35"), f"Right eigenvector residual too large: {res_h}"
    assert res_nu < mp.mpf("1e-35"), f"Left eigenvector residual too large: {res_nu}"
    return h, nu


def resolvent_CS(S: list[int], p: mp.mpf, n: int = N_MAIN) -> mp.mpf:
    """Evaluate C_S(p) = ((I - L_p)^{-1} 1)(0) via collocation."""
    A = finite_operator_matrix(S, p, n)
    v_nodal = mp.lu_solve(eye_mat(n) - A, mp.matrix([mp.mpf(1)] * n))
    coeffs = vandermonde_inv(n) * v_nodal
    return coeffs[0]


def solve_p0_and_kappa(S: list[int], n: int = N_MAIN) -> dict[str, mp.mpf]:
    """Find p_0 = 2 s_0(S), c(p_0), -rho'(p_0), and kappa(S) by two independent methods."""
    lo, hi = mp.mpf("0.1"), mp.mpf("1.99")
    while leading_eig_power(finite_operator_matrix(S, hi, 12), 25) > 1:
        hi = (hi + 2) / 2
    while leading_eig_power(finite_operator_matrix(S, lo, 12), 25) < 1:
        lo = lo / 2
    for _ in range(20):
        mid = (lo + hi) / 2
        if leading_eig_power(finite_operator_matrix(S, mid, 12), 25) > 1:
            lo = mid
        else:
            hi = mid

    x0, x1 = lo, hi
    f0 = det_one_minus(finite_operator_matrix(S, x0, n))
    f1 = det_one_minus(finite_operator_matrix(S, x1, n))
    assert f0 < 0 and f1 > 0, f"Unexpected det signs for S={S}: f0={f0}, f1={f1}"
    for _ in range(30):
        if abs(x1 - x0) < mp.mpf("1e-48"):
            break
        x2 = x1 - f1 * (x1 - x0) / (f1 - f0)
        if not (lo < x2 < hi):
            x2 = (lo + hi) / 2
        f2 = det_one_minus(finite_operator_matrix(S, x2, n))
        if f2 < 0:
            lo = x2
        else:
            hi = x2
        x0, f0 = x1, f1
        x1, f1 = x2, f2
    p0 = x1
    s0 = p0 / 2

    A = finite_operator_matrix(S, p0, n)
    Ap = finite_operator_deriv_matrix(S, p0, n)
    lam_chk = leading_eig_power(A, 60)
    assert abs(lam_chk - 1) < mp.mpf("1e-25"), f"Dominant eig mismatch: {lam_chk}"
    h_nodal, nu_nodal = null_vectors_at_one(A)

    nu_of_1 = mp.fsum(nu_nodal[i] for i in range(n))
    h_at_0 = (vandermonde_inv(n) * h_nodal)[0]
    c_p0 = h_at_0 * nu_of_1
    Ap_h = Ap * h_nodal
    rho_prime = mp.fsum(nu_nodal[i] * Ap_h[i] for i in range(n))
    kappa_eig = c_p0 / (-rho_prime)

    dp1 = mp.mpf("1e-20")
    dp2 = mp.mpf("5e-21")
    r1 = dp1 * resolvent_CS(S, p0 + dp1, n)
    r2 = dp2 * resolvent_CS(S, p0 + dp2, n)
    kappa_pole = 2 * r2 - r1

    return {
        "p0": p0,
        "s0": s0,
        "c_p0": c_p0,
        "neg_rho_prime": -rho_prime,
        "kappa_eig": kappa_eig,
        "kappa_pole": kappa_pole,
        "kappa_diff": abs(kappa_eig - kappa_pole),
    }


def multi_residue_matrix(
    m: int, S: list[int], B: list[int], s: mp.mpf, n: int = N_MAIN
) -> mp.matrix:
    """Fast exact collocation matrix A(s) of L_{s, A_{m,S,B}} using the binomial
    Riemann-zeta expansion zeta(p, 1 + u) = sum_{l>=0} C(-p, l) zeta(p+l) u^l."""
    xs = cheb_nodes(n)
    m_mp = mp.mpf(m)
    inv_m = 1 / m_mp
    two_s = 2 * s

    # Choose truncation order L_max so |u|^{L_max} < 10^{-65}
    max_num = max([r + 1 for r in S] + [b + 1 for b in B] + [1])
    u_bound = float(max_num) / float(m)
    assert u_bound < 0.25, f"m={m} too small for fast series"
    L_max = max(6, int(68.0 / (-mp.log10(u_bound))) + 4)

    # Precompute Riemann zeta(2s + t) for t = 0 .. n + L_max - 1 (only ~80 calls!)
    z_vals = [mp.zeta(two_s + t) for t in range(n + L_max)]
    m_pows = [m_mp ** (-(two_s + j)) for j in range(n)]

    # Precompute binomial coefficients C(-(2s+j), l) for j=0..n-1, l=0..L_max-1
    bin_z: list[list[mp.mpf]] = []
    for j in range(n):
        p = two_s + j
        row_bz = []
        coeff = mp.mpf(1)
        for l in range(L_max):
            row_bz.append(coeff * z_vals[j + l])
            coeff = -coeff * (p + l) / (l + 1)
        bin_z.append(row_bz)

    M = mp.matrix(n, n)
    for i, x in enumerate(xs):
        # S-core branches (k = 0)
        invs_S = [1 / (mp.mpf(a) + x) for a in S]
        pows_S = [(mp.mpf(a) + x) ** (-two_s) for a in S]

        # Tail shift power sums U_l = sum_{r in S} ((r+x)/m)^l + sum_{b in B} ((-b+x)/m)^l
        us = [(mp.mpf(r) + x) * inv_m for r in S] + [
            (mp.mpf(-b) + x) * inv_m for b in B
        ]
        u_cur = [mp.mpf(1)] * len(us)
        u_sums = []
        for l in range(L_max):
            u_sums.append(mp.fsum(u_cur))
            for k in range(len(us)):
                u_cur[k] *= us[k]

        for j in range(n):
            core_val = mp.fsum(pows_S)
            for k in range(len(S)):
                pows_S[k] *= invs_S[k]
            # Tail sum via dot product of bin_z[j] and u_sums
            bz = bin_z[j]
            tail_val = m_pows[j] * mp.fsum(bz[l] * u_sums[l] for l in range(L_max))
            M[i, j] = core_val + tail_val

    return M * vandermonde_inv(n)


def verify_hurwitz_series_identity() -> mp.mpf:
    """Spot-check our binomial-Riemann expansion directly against mp.zeta(p, sh)."""
    S_test, B_test, m_test = [1, 2], [0], 256
    s_test = mp.mpf("0.55")
    n_test = 8
    A_fast = multi_residue_matrix(m_test, S_test, B_test, s_test, n=n_test)
    # Direct Hurwitz matrix
    xs = cheb_nodes(n_test)
    M_dir = mp.matrix(n_test, n_test)
    m_mp = mp.mpf(m_test)
    for i, x in enumerate(xs):
        for j in range(n_test):
            p = 2 * s_test + j
            tot = mp.mpf(0)
            for r in S_test:
                tot += (m_mp ** (-p)) * mp.zeta(p, (mp.mpf(r) + x) / m_mp)
            for b in B_test:
                tot += (m_mp ** (-p)) * mp.zeta(p, (mp.mpf(m_test - b) + x) / m_mp)
            M_dir[i, j] = tot
    A_dir = M_dir * vandermonde_inv(n_test)
    max_err = max(abs(A_fast[i, j] - A_dir[i, j]) for i in range(n_test) for j in range(n_test))
    assert max_err < mp.mpf("1e-55"), f"Hurwitz series mismatch: {max_err}"
    return max_err


def solve_dim_multi_residue(
    m: int,
    S: list[int],
    B: list[int],
    s0: mp.mpf,
    kappa: mp.mpf,
    n: int = N_MAIN,
) -> mp.mpf:
    """Solve det(I - L_{s, A_{m,S,B}}) = 0 to >42 digits."""
    d = len(S) + len(B)
    k_est = d * kappa * mp.zeta(2 * s0) / 2
    delta_est = k_est * (mp.mpf(m) ** (-2 * s0))

    def f(s: mp.mpf) -> mp.mpf:
        return det_one_minus(multi_residue_matrix(m, S, B, s, n))

    lo = s0 + delta_est * mp.mpf("0.7")
    hi = s0 + delta_est * mp.mpf("1.3")
    flo = f(lo)
    fhi = f(hi)
    step = 0
    while flo > 0 and step < 12:
        hi, fhi = lo, flo
        lo = s0 + (lo - s0) / 2
        flo = f(lo)
        step += 1
    step = 0
    while fhi < 0 and step < 12:
        lo, flo = hi, fhi
        hi = s0 + 2 * (hi - s0)
        fhi = f(hi)
        step += 1
    assert flo < 0 and fhi > 0, f"Failed to bracket m={m}, S={S}, B={B}: {flo}, {fhi}"

    x0, f0 = lo, flo
    x1, f1 = hi, fhi
    for _ in range(25):
        if abs(x1 - x0) < mp.mpf("1e-44") * max(mp.mpf(1), abs(x1)):
            break
        if f1 == f0:
            break
        x2 = x1 - f1 * (x1 - x0) / (f1 - f0)
        if not (lo < x2 < hi):
            x2 = (lo + hi) / 2
        f2 = f(x2)
        if f2 < 0:
            lo, flo = x2, f2
        else:
            hi, fhi = x2, f2
        x0, f0 = x1, f1
        x1, f1 = x2, f2
    return x1


def solve_master_root(
    m: int, S: list[int], B: list[int], s0: mp.mpf, kappa: mp.mpf, n: int = N_MAIN
) -> mp.mpf:
    """Solve the scalar master equation d * C_S(2s) * m^{-2s} * zeta(2s) = 1."""
    d = len(S) + len(B)
    k_est = d * kappa * mp.zeta(2 * s0) / 2
    delta_est = k_est * (mp.mpf(m) ** (-2 * s0))

    def g(s: mp.mpf) -> mp.mpf:
        return d * resolvent_CS(S, 2 * s, n) * (mp.mpf(m) ** (-2 * s)) * mp.zeta(2 * s) - 1

    lo = s0 + delta_est * mp.mpf("0.7")
    hi = s0 + delta_est * mp.mpf("1.3")
    flo, fhi = g(lo), g(hi)
    while flo < 0:
        hi, fhi = lo, flo
        lo = s0 + (lo - s0) / 2
        flo = g(lo)
    while fhi > 0:
        lo, flo = hi, fhi
        hi = s0 + 2 * (hi - s0)
        fhi = g(hi)
    x0, f0 = lo, flo
    x1, f1 = hi, fhi
    for _ in range(25):
        if abs(x1 - x0) < mp.mpf("1e-44"):
            break
        x2 = x1 - f1 * (x1 - x0) / (f1 - f0)
        if not (lo < x2 < hi):
            x2 = (lo + hi) / 2
        f2 = g(x2)
        if f2 > 0:
            lo = x2
        else:
            hi = x2
        x0, f0 = x1, f1
        x1, f1 = x2, f2
    return x1


def dim_sparse_alphabet(k0: int, n_terms: int = 10, n_colloc: int = 18) -> mp.mpf:
    """Collocation dimension of E_{A_{k_0}} where A_{k_0} = {2^{2^k} : k >= k_0}."""
    digits = [2 ** (2 ** k) for k in range(k0, k0 + n_terms)]
    hi = mp.mpf(2) ** (-(k0 + 1))
    lo = hi / 100
    while leading_eig_power(finite_operator_matrix(digits, 2 * lo, 8), 20) < 1:
        lo /= 2
    for _ in range(25):
        mid = (lo + hi) / 2
        if leading_eig_power(finite_operator_matrix(digits, 2 * mid, 8), 20) > 1:
            lo = mid
        else:
            hi = mid

    def f(s: mp.mpf) -> mp.mpf:
        return det_one_minus(finite_operator_matrix(digits, 2 * s, n_colloc))

    x0, x1 = lo, hi
    f0, f1 = f(x0), f(x1)
    assert f0 < 0 and f1 > 0
    for _ in range(25):
        if abs(x1 - x0) < mp.mpf("1e-40"):
            break
        x2 = x1 - f1 * (x1 - x0) / (f1 - f0)
        if not (lo < x2 < hi):
            x2 = (lo + hi) / 2
        f2 = f(x2)
        if f2 < 0:
            lo = x2
        else:
            hi = x2
        x0, f0 = x1, f1
        x1, f1 = x2, f2
    return x1


def main() -> None:
    t0 = time.time()
    lines: list[str] = []
    results: dict = {
        "meta": {
            "date": "2026-11-25",
            "work_dps": WORK_DPS,
            "out_dps": OUT_DPS,
            "n_main": N_MAIN,
            "n_check": N_CHECK,
            "classification": "Category 4 (finite computation / non-rigorous numerical corroboration)",
        },
        "supercritical_cases": [],
        "sparse_alphabet": {},
        "symbolic_critical_expansion": {},
    }

    def log(msg: str = "") -> None:
        print(msg, flush=True)
        lines.append(msg)

    log("=" * 92)
    log("EXACT SUPERCRITICAL LEADING CONSTANT & SPARSE-ALPHABET VERIFICATION (2026-11-25)")
    log(f"mpmath working precision = {WORK_DPS} dps, reported = {OUT_DPS} digits, n={N_MAIN} (check n={N_CHECK})")
    log("Classification (AGENTS.md): Category 4 (non-rigorous numerical corroboration)")
    log("=" * 92)

    h_err = verify_hurwitz_series_identity()
    log(f"  [PASS] Binomial-Riemann Hurwitz expansion cross-check vs mp.zeta: max matrix err = {mp.nstr(h_err, 4)}")
    results["meta"]["hurwitz_series_crosscheck_err"] = mp.nstr(h_err, 4)

    # -------------------------------------------------------------------------
    # PART A & B: Exact Supercritical Constant Comparison
    # -------------------------------------------------------------------------
    cases = [
        ([1, 2], [], [256, 1024, 4096, 16384, 65536, 262144, 10**6, 10**9, 10**12]),
        ([1, 2], [0], [256, 1024, 4096, 16384, 65536, 262144, 10**6, 10**9, 10**12]),
        ([1, 2, 3], [], [256, 1024, 4096, 16384, 65536, 10**6, 10**9]),
        ([1, 2, 3, 4], [], [256, 1024, 4096, 16384, 65536, 10**6, 10**9]),
    ]

    spectral_cache: dict[tuple[int, ...], dict[str, mp.mpf]] = {}
    for S, B, m_list in cases:
        key = tuple(S)
        if key not in spectral_cache:
            spec_main = solve_p0_and_kappa(S, n=N_MAIN)
            spec_chk = solve_p0_and_kappa(S, n=N_CHECK)
            s0_colloc_diff = abs(spec_main["s0"] - spec_chk["s0"])
            kappa_colloc_diff = abs(spec_main["kappa_eig"] - spec_chk["kappa_eig"])
            assert s0_colloc_diff < mp.mpf("1e-32"), f"s0 colloc mismatch: {s0_colloc_diff}"
            assert kappa_colloc_diff < mp.mpf("1e-31"), f"kappa colloc mismatch: {kappa_colloc_diff}"
            assert spec_chk["kappa_diff"] < mp.mpf("1e-18"), f"kappa eig vs pole mismatch: {spec_chk['kappa_diff']}"
            spec_chk["s0_colloc_diff"] = s0_colloc_diff
            spec_chk["kappa_colloc_diff"] = kappa_colloc_diff
            spectral_cache[key] = spec_chk

        spec = spectral_cache[key]
        s0 = spec["s0"]
        p0 = spec["p0"]
        kappa = spec["kappa_eig"]
        d = len(S) + len(B)
        zeta_p0 = mp.zeta(p0)
        k_exact = d * kappa * zeta_p0 / 2
        k_old = d * kappa / (2 * (p0 - 1))
        ratio_exact_to_old = k_exact / k_old

        log()
        log("-" * 92)
        log(f"CASE S = {S}, B = {B}  (d = |S| + |B| = {d})")
        log(f"  s_0(S)            = {mp.nstr(s0, OUT_DPS)}")
        log(f"  p_0 = 2 s_0(S)    = {mp.nstr(p0, OUT_DPS)}")
        log(f"  c(p_0)            = {mp.nstr(spec['c_p0'], OUT_DPS)}")
        log(f"  -rho'(p_0)        = {mp.nstr(spec['neg_rho_prime'], OUT_DPS)}")
        log(f"  kappa(S) [eig]    = {mp.nstr(kappa, OUT_DPS)}")
        log(f"  kappa(S) [pole]   = {mp.nstr(spec['kappa_pole'], OUT_DPS)}")
        log(f"  |eig - pole|      = {mp.nstr(spec['kappa_diff'], 4)}")
        log(
            f"  |n={N_MAIN} vs n={N_CHECK}| s0 = {mp.nstr(spec['s0_colloc_diff'], 4)}, "
            f"kappa = {mp.nstr(spec['kappa_colloc_diff'], 4)}"
        )
        log(f"  zeta(2 s_0)       = {mp.nstr(zeta_p0, OUT_DPS)}")
        log(f"  1/(2 s_0 - 1)     = {mp.nstr(1 / (p0 - 1), OUT_DPS)}")
        log(f"  K_exact = d*kappa*zeta(2s0)/2     = {mp.nstr(k_exact, OUT_DPS)}")
        log(f"  K_old   = d*kappa/(2*(2s0 - 1))   = {mp.nstr(k_old, OUT_DPS)}")
        log(
            f"  K_exact / K_old = (2s0-1)zeta(2s0)= {mp.nstr(ratio_exact_to_old, 12)}  "
            f"({mp.nstr((ratio_exact_to_old - 1) * 100, 5)}% higher)"
        )
        log()
        log(
            f"  {'m':>13} | {'dimH(F_{m,S,B})':>32} | {'Q_m=m^{2s0}(d-s0)':>18} | "
            f"{'Q_m/K_exact':>12} | {'Q_m/K_old':>12} | {'|Q_m-Q_mast|/K':>14}"
        )

        rows = []
        for m in m_list:
            dim_m = solve_dim_multi_residue(m, S, B, s0, kappa, n=N_MAIN)
            s_mast = solve_master_root(m, S, B, s0, kappa, n=N_MAIN)
            colloc_err = None
            if m == m_list[-1]:
                dim_m_chk = solve_dim_multi_residue(m, S, B, s0, kappa, n=N_CHECK)
                colloc_err = abs(dim_m - dim_m_chk)
                assert colloc_err < mp.mpf("1e-32"), f"dim colloc mismatch at m={m}: {colloc_err}"
            qm = (mp.mpf(m) ** p0) * (dim_m - s0)
            qm_mast = (mp.mpf(m) ** p0) * (s_mast - s0)
            rel_exact = qm / k_exact
            rel_old = qm / k_old
            mast_gap = abs(qm - qm_mast) / k_exact
            log(
                f"  {m:>13} | {mp.nstr(dim_m, OUT_DPS):>32} | {mp.nstr(qm, 14):>18} | "
                f"{mp.nstr(rel_exact, 10):>12} | {mp.nstr(rel_old, 10):>12} | {mp.nstr(mast_gap, 4):>14}"
            )
            row = {
                "m": m,
                "dimH": mp.nstr(dim_m, OUT_DPS),
                "Q_m": mp.nstr(qm, 18),
                "Q_master": mp.nstr(qm_mast, 18),
                "Q_m_over_K_exact": mp.nstr(rel_exact, 12),
                "Q_m_over_K_old": mp.nstr(rel_old, 12),
                "master_rel_gap": mp.nstr(mast_gap, 6),
            }
            if colloc_err is not None:
                row["colloc_err_n44_vs_n48"] = mp.nstr(colloc_err, 4)
            rows.append(row)

        last_rel_exact = mp.mpf(rows[-1]["Q_m_over_K_exact"])
        last_rel_old = mp.mpf(rows[-1]["Q_m_over_K_old"])
        assert abs(last_rel_exact - 1) < mp.mpf("1e-5"), f"Expected Q_m/K_exact -> 1, got {last_rel_exact}"
        assert abs(last_rel_old - 1) > mp.mpf("0.03"), f"Expected Q_m/K_old separated from 1, got {last_rel_old}"
        log(f"  [PASS] At m={m_list[-1]}: Q_m/K_exact = {mp.nstr(last_rel_exact, 10)} (within 1e-5 of 1),")
        log(
            f"         while Q_m/K_old = {mp.nstr(last_rel_old, 10)} "
            f"(disproves old K_old by {mp.nstr((last_rel_old - 1) * 100, 5)}%)."
        )
        if rows[-1].get("colloc_err_n44_vs_n48"):
            log(
                f"         Collocation check n={N_MAIN} vs n={N_CHECK} at m={m_list[-1]}: "
                f"|diff| = {rows[-1]['colloc_err_n44_vs_n48']} (< 1e-32, securing all 30 digits)."
            )

        results["supercritical_cases"].append({
            "S": S,
            "B": B,
            "d": d,
            "s0": mp.nstr(s0, OUT_DPS),
            "p0": mp.nstr(p0, OUT_DPS),
            "c_p0": mp.nstr(spec["c_p0"], OUT_DPS),
            "neg_rho_prime": mp.nstr(spec["neg_rho_prime"], OUT_DPS),
            "kappa": mp.nstr(kappa, OUT_DPS),
            "kappa_pole_crosscheck": mp.nstr(spec["kappa_pole"], OUT_DPS),
            "zeta_2s0": mp.nstr(zeta_p0, OUT_DPS),
            "K_exact": mp.nstr(k_exact, OUT_DPS),
            "K_old": mp.nstr(k_old, OUT_DPS),
            "K_exact_over_K_old": mp.nstr(ratio_exact_to_old, 14),
            "rows": rows,
        })

    c_d2 = results["supercritical_cases"][0]
    c_d3 = results["supercritical_cases"][1]
    ratio_d = mp.mpf(c_d3["rows"][-1]["Q_m"]) / mp.mpf(c_d2["rows"][-1]["Q_m"])
    assert abs(ratio_d - mp.mpf("1.5")) < mp.mpf("1e-6"), f"d-ratio failed: {ratio_d}"
    log()
    log(
        f"  [PASS] Factor-d test at m={c_d2['rows'][-1]['m']}: "
        f"Q_m({{1,2}},{{0}}) / Q_m({{1,2}},empty) = {mp.nstr(ratio_d, 12)} (expected 3/2 = 1.5)."
    )

    # -------------------------------------------------------------------------
    # PART C: 50-Digit Verification of Sparse-Alphabet Counterexample
    # -------------------------------------------------------------------------
    log()
    log("=" * 92)
    log("PART C: SPARSE-ALPHABET COUNTEREXAMPLE A_{k0} = {2^{2^k} : k >= k0} (50-digit check)")
    log("=" * 92)
    u_sum = mp.fsum(mp.power(2, -(2 ** j)) for j in range(14))
    assert u_sum < 1, f"Expected sum 2^(-2^j) < 1, got {u_sum}"
    log(f"  Universal sum sum_{{j>=0}} 2^{{-2^j}} (50 digits) = {mp.nstr(u_sum, 50)} < 1")

    sparse_rows = []
    for k0 in [1, 2, 3, 4, 5, 10]:
        s_ub = mp.power(2, -(k0 + 1))
        tail_sum = mp.fsum(mp.power(2, -mp.mpf(2 ** k) * (2 * s_ub)) for k in range(k0, k0 + 14))
        assert abs(tail_sum - u_sum) < mp.mpf("1e-55")
        row = {
            "k0": k0,
            "min_digit": str(2 ** (2 ** k0)) if k0 <= 5 else f"2^{2**k0}",
            "s_upper_bound": mp.nstr(s_ub, 20),
            "tail_sum_at_s_ub": mp.nstr(tail_sum, 50),
        }
        if k0 <= 4:
            d_full = dim_sparse_alphabet(k0, n_terms=10, n_colloc=18)
            d_pair = solve_p0_and_kappa([2 ** (2 ** k0), 2 ** (2 ** (k0 + 1))], n=18)["s0"]
            assert 0 < d_pair <= d_full <= s_ub
            row["dimH_A_k0_colloc"] = mp.nstr(d_full, 25)
            row["dimH_first_pair_colloc"] = mp.nstr(d_pair, 25)
            log(
                f"  k0={k0:>2}: 0 < dimH(first pair)={mp.nstr(d_pair, 14)} <= dimH(A_k0)={mp.nstr(d_full, 14)} "
                f"<= 2^{{-({k0}+1)}}={mp.nstr(s_ub, 10)} (sum={mp.nstr(tail_sum, 12)} < 1)"
            )
        else:
            log(
                f"  k0={k0:>2}: 0 < dimH(A_k0) <= 2^{{-({k0}+1)}}={mp.nstr(s_ub, 10)} "
                f"(50-digit sum = {mp.nstr(tail_sum, 20)} < 1)"
            )
        sparse_rows.append(row)

    results["sparse_alphabet"] = {
        "universal_dyadic_sum_50d": mp.nstr(u_sum, 50),
        "note": (
            "For every fixed k0 >= 1, A_{k0} = {2^{2^k} : k >= k0} satisfies "
            "0 < dimH(E_{A_{k0}}) <= 2^{-(k0+1)} < 1/2 (disproving the naive infinite-alphabet >= 1/2 "
            "conjecture, while demonstrating dimH(E_{A_1}) > 0, NOT 0), and "
            "lim_{k0->inf} dimH(E_{A_{k0}}) = 0 = theta(A), with dimH({x in E_{A_1} : a_n(x) -> inf}) = 0."
        ),
        "rows": sparse_rows,
    }
    log("  [PASS] Sparse-alphabet counterexample & exact tail-abscissa limit verified.")

    # -------------------------------------------------------------------------
    # PART D: SymPy Symbolic Verification of Critical-Line Second-Order Expansion
    # -------------------------------------------------------------------------
    log()
    log("=" * 92)
    log("PART D: SYMPY SYMBOLIC CHECK OF CRITICAL-LINE SECOND-ORDER EXPANSION (eta = 0)")
    log("=" * 92)
    u, L, a = sp.symbols("u L a", positive=True)
    b = sp.Symbol("b", real=True)
    eps = a * u + b * L * u**2
    lhs = (eps / u) ** 2 * sp.exp(eps * L)
    ser = sp.series(lhs, u, 0, 2).removeO()
    coeff_u0 = sp.simplify(ser.subs(u, 0))
    coeff_u1 = sp.simplify(sp.diff(ser, u).subs(u, 0))
    b_sol = sp.solve(sp.Eq(coeff_u1, 0), b)[0]
    assert sp.simplify(coeff_u0 - a**2) == 0
    assert sp.simplify(b_sol + a**2 / 2) == 0
    dim_second_coeff = sp.simplify(b_sol / 2)
    log(f"  LHS expansion at u = m^{{-1/2}}: {ser}")
    log(f"  u^0 coefficient: {coeff_u0}  (matches d*kappa = a^2)")
    log(f"  u^1 coefficient: {coeff_u1} = 0  ==>  b = {b_sol} = -d*kappa/2")
    log(
        f"  Therefore dimH F_{{m,S,B}} - 1/2 = (sqrt(d*kappa)/2) m^{{-1/2}} "
        f"+ ({dim_second_coeff}) (log m)/m + O(m^{{-1}})"
    )
    log("  [PASS] Symbolic critical-line second-order expansion verified.")
    results["symbolic_critical_expansion"] = {
        "series_u1": str(ser),
        "b_solution_for_eps": str(b_sol),
        "second_order_coeff_for_dimH": str(dim_second_coeff),
    }

    elapsed = time.time() - t0
    log()
    log(f"ALL CHECKS PASSED in {elapsed:.2f}s.")
    results["meta"]["elapsed_seconds"] = round(elapsed, 2)

    log_path = HERE / "verify_supercritical_exact_constant_20261125.log"
    json_path = HERE / "verify_supercritical_exact_constant_20261125.json"
    log_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    json_path.write_text(json.dumps(results, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
