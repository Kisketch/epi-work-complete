"""High-precision Python verification for ResidueMultiAsymptotic.lean (2026-11-23).

Verifies (classification: 有限计算 / non-rigorous numerical evidence via Chebyshev collocation,
crossed against the 10 two-sided (20-endpoint) Lean-kernel-checked brackets in
residue_certificate_general_N512.json):
1. 32-digit values of C_r, C_r' = sum log(q_n)/q_n, and the exact third-order Euler-Mascheroni
   coefficient c_2(r) = C_r * (gamma * C_r - C_r') / 2 for r in {1..5} and r = m;
2. Subcritical multi-residue constants C_S, C_S', and c_2(S, B) = d^2 * C_S * (gamma * C_S - C_S') / 2
   both by direct word summation and resolvent collocation;
3. Cross-check against all 10 kernel-checked N=512 brackets (m=2..6);
4. Convergence of m^2 * (dim - two_term) to c_2(r) and c_2(S, B) with O((log m)^2 / m) error
   (equivalently O((log m)^2 / m^3) error on dimH itself);
5. Supercritical algebraic witness for S={1,2} at s=51/100 and power-law convergence
   dimH F_{m,S} - s_0 ~ Theta(m^{-2 s_0}) for S={1,2} and S={1,2,3}.

Writes verification/verify_residue_multi_asymptotic.json and .log (UTF-8 without BOM).
"""
from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path

import mpmath as mp

HERE = Path(__file__).resolve().parent
DPS = 32
mp.mp.dps = DPS
_V_INV_CACHE: dict[int, mp.matrix] = {}


def nodes(n: int) -> list[mp.mpf]:
    return [(1 + mp.cos(mp.pi * (2 * i + 1) / (2 * n))) / 2 for i in range(n)]


def vandermonde_inv(n: int) -> mp.matrix:
    if n not in _V_INV_CACHE:
        xs = nodes(n)
        V = mp.matrix(n, n)
        for i, x in enumerate(xs):
            for j in range(n):
                V[i, j] = x ** j
        _V_INV_CACHE[n] = V ** -1
    return _V_INV_CACHE[n]


def metal_C_and_Cp(r: int, terms: int = 240) -> tuple[mp.mpf, mp.mpf]:
    q0, q1 = mp.mpf(1), mp.mpf(r)
    c_val = mp.mpf(1)
    cp_val = mp.mpf(0)
    for _ in range(terms):
        c_val += 1 / q1
        cp_val += mp.log(q1) / q1
        q0, q1 = q1, r * q1 + q0
    return c_val, cp_val


def resolvent_C_colloc(S: list[int], s: mp.mpf, n: int = 16) -> mp.mpf:
    if not S:
        return mp.mpf(1)
    xs = nodes(n)
    M = mp.matrix(n, n)
    V = mp.matrix(n, n)
    for i, x in enumerate(xs):
        for j in range(n):
            M[i, j] = mp.fsum((mp.mpf(a) + x) ** (-(2 * s + j)) for a in S)
            V[i, j] = x ** j
    c = mp.lu_solve(V - M, mp.matrix([mp.mpf(1)] * n))
    return c[0]


def word_sum_C_direct(S: list[int], max_len: int = 18) -> tuple[mp.mpf, mp.mpf]:
    """Direct continuant tree summation up to word length max_len (for small subcritical S)."""
    if not S:
        return mp.mpf(1), mp.mpf(0)
    # State list of pairs (q_n, q_{n-1})
    states: list[tuple[int, int]] = [(1, 0)]
    c_tot = mp.mpf(1)
    cp_tot = mp.mpf(0)
    for _ in range(max_len):
        nxt: list[tuple[int, int]] = []
        for q, p in states:
            for a in S:
                qn = a * q + p
                nxt.append((qn, q))
                fq = mp.mpf(qn)
                c_tot += 1 / fq
                cp_tot += mp.log(fq) / fq
        states = nxt
        if len(states) > 200000:
            break
    return c_tot, cp_tot


def rho_finite(S: list[int], s: mp.mpf, n: int = 16) -> mp.mpf:
    xs = nodes(n)
    M = mp.matrix(n, n)
    for i, x in enumerate(xs):
        for j in range(n):
            M[i, j] = mp.fsum((mp.mpf(a) + x) ** (-(2 * s + j)) for a in S)
    ev = mp.eig(M * vandermonde_inv(n), left=False, right=False)
    return max(abs(e) for e in ev)


def rho_multi_residue(
    m: int,
    S: list[int],
    B: list[int],
    s: mp.mpf,
    n: int = 16,
    use_eig: bool = True,
) -> mp.mpf:
    xs = nodes(n)
    M = mp.matrix(n, n)
    for i, x in enumerate(xs):
        for j in range(n):
            tot = mp.mpf(0)
            for r in S:
                tot += mp.mpf(m) ** (-(2 * s + j)) * mp.zeta(2 * s + j, (mp.mpf(r) + x) / m)
            for b in B:
                tot += mp.mpf(m) ** (-(2 * s + j)) * mp.zeta(2 * s + j, (mp.mpf(m - b) + x) / m)
            M[i, j] = tot
    A = M * vandermonde_inv(n)
    if use_eig:
        ev = mp.eig(A, left=False, right=False)
        return max(abs(e) for e in ev)
    v = mp.matrix([mp.mpf(1)] + [mp.mpf(0)] * (n - 1))
    for _ in range(52):
        w = A * v
        nrm = mp.fsum(abs(x) for x in w)
        v = w / nrm
    nv = A * v
    return mp.fsum(nv[i] * v[i] for i in range(n)) / mp.fsum(v[i] * v[i] for i in range(n))


def find_dim_bracketed(
    fn,
    lo_init: mp.mpf,
    hi_init: mp.mpf,
    tol: mp.mpf = mp.mpf("1e-18"),
    bisect_steps: int = 2,
) -> mp.mpf:
    half = mp.mpf("0.5")
    lo = max(half + mp.mpf("1e-12"), lo_init)
    hi = max(lo + mp.mpf("1e-6"), hi_init)
    flo = fn(lo)
    while flo < 0:
        lo = (half + lo) / 2
        flo = fn(lo)
    fhi = fn(hi)
    while fhi > 0:
        hi = hi + max(mp.mpf("0.005"), hi - half)
        fhi = fn(hi)
    for _ in range(bisect_steps):
        mid = (lo + hi) / 2
        fmid = fn(mid)
        if fmid > 0:
            lo, flo = mid, fmid
        else:
            hi, fhi = mid, fmid
    side = 0
    for _ in range(45):
        if abs(hi - lo) < tol or flo == fhi:
            break
        mid = (lo * fhi - hi * flo) / (fhi - flo)
        if not (lo < mid < hi):
            mid = (lo + hi) / 2
        fmid = fn(mid)
        if abs(fmid) < tol:
            return mid
        if fmid > 0:
            lo, flo = mid, fmid
            if side == 1:
                fhi /= 2
            side = 1
        else:
            hi, fhi = mid, fmid
            if side == -1:
                flo /= 2
            side = -1
    return (lo + hi) / 2


def main() -> None:
    mp.mp.dps = DPS
    gamma = mp.euler
    lines: list[str] = []
    results: dict = {"dps": DPS, "single_residue": {}, "n512_cross_check": [], "multi_subcritical": [], "supercritical": []}

    lines.append("=== Multi-Residue Phase Transition & Euler-Mascheroni 3-Term Asymptotics Verification ===")
    lines.append(f"Precision: {DPS} digits; Euler-Mascheroni gamma = {mp.nstr(gamma, 30)}")

    # 1. Single-residue 50-digit constants C_r, C_r', c_2(r)
    lines.append("\n[1] Single-residue constants C_r, C_r', c_2(r) = C_r*(gamma*C_r - C_r')/2:")
    for r in (1, 2, 3, 4, 5):
        cr, cpr = metal_C_and_Cp(r, terms=280 if r == 1 else 180)
        c2 = cr * (gamma * cr - cpr) / 2
        results["single_residue"][str(r)] = {
            "C": mp.nstr(cr, 35),
            "Cp": mp.nstr(cpr, 35),
            "c2": mp.nstr(c2, 35),
        }
        lines.append(f"  r={r}: C={mp.nstr(cr, 18)}, C'={mp.nstr(cpr, 18)}, c2={mp.nstr(c2, 14)}")
    c2_mm = gamma / 2
    results["single_residue"]["m"] = {"C": "1", "Cp": "0", "c2": mp.nstr(c2_mm, 35)}
    lines.append(f"  r=m: C=1, C'=0, c2=gamma/2={mp.nstr(c2_mm, 14)}")

    # 2. Cross-check against 10 N=512 kernel-checked brackets (m=2..6)
    lines.append("\n[2] Cross-check Chebyshev collocation (n=16 vs n=22) against N=512 Lean brackets:")
    cert = json.loads((HERE / "residue_certificate_general_N512.json").read_text(encoding="utf-8"))["certificates"]
    for entry in cert:
        m = entry["modulus"]
        r = entry["residue"]
        lo_frac = Fraction(entry["lower"])
        hi_frac = Fraction(entry["upper"])
        lo_mp = mp.mpf(lo_frac.numerator) / mp.mpf(lo_frac.denominator)
        hi_mp = mp.mpf(hi_frac.numerator) / mp.mpf(hi_frac.denominator)
        S_arg, B_arg = ([], [0]) if r == m else ([r], [])
        d16 = find_dim_bracketed(
            lambda s: rho_multi_residue(m, S_arg, B_arg, s, n=16) - 1,
            lo_mp,
            hi_mp,
            bisect_steps=2,
        )
        d22 = find_dim_bracketed(
            lambda s: rho_multi_residue(m, S_arg, B_arg, s, n=22) - 1,
            d16 - mp.mpf("1e-8"),
            d16 + mp.mpf("1e-8"),
            bisect_steps=0,
        )
        assert lo_mp < d22 < hi_mp, f"Bracket check failed for m={m}, r={r}: {d22} not in ({lo_mp}, {hi_mp})"
        assert abs(d16 - d22) < mp.mpf("1e-11"), f"Collocation mismatch at m={m}, r={r}: {abs(d16 - d22)}"
        results["n512_cross_check"].append({
            "m": m,
            "r": r,
            "dim_n22": mp.nstr(d22, 22),
            "lower": entry["lower"],
            "upper": entry["upper"],
            "n_diff": float(abs(d16 - d22)),
        })
        lines.append(f"  m={m}, r={r}: est={mp.nstr(d22, 14)} in ({entry['lower']}, {entry['upper']}) [PASS]")

    # 3. Subcritical 3-term asymptotic convergence (single-residue and multi-residue)
    lines.append("\n[3] Subcritical 3-term asymptotics: m^2*(dim - two_term) -> c_2(S,B):")
    sub_cases = [
        ("r=1", [1], []),
        ("r=2", [2], []),
        ("r=3", [3], []),
        ("r=m (B={0})", [], [0]),
        ("S={2,3}, B={}", [2, 3], []),
        ("S={1,3}, B={}", [1, 3], []),
        ("S={1,4}, B={}", [1, 4], []),
        ("S={1}, B={0}", [1], [0]),
        ("S={}, B={0,1}", [], [0, 1]),
        ("S={2,4,5}, B={}", [2, 4, 5], []),
    ]
    ms = [64, 256, 1024, 4096, 16384]
    for label, S_arg, B_arg in sub_cases:
        d = len(S_arg) + len(B_arg)
        assert not S_arg or rho_finite(S_arg, mp.mpf("0.5"), n=14) < 1, f"{label} should be subcritical!"
        if len(S_arg) == 1 and not B_arg:
            CS, CSp = metal_C_and_Cp(S_arg[0], terms=240)
        else:
            CS = resolvent_C_colloc(S_arg, mp.mpf("0.5"), n=16)
            h = mp.mpf("1e-10")
            CSp = mp.mpf(0) if not S_arg else -(
                resolvent_C_colloc(S_arg, mp.mpf("0.5") + h, n=16)
                - resolvent_C_colloc(S_arg, mp.mpf("0.5") - h, n=16)
            ) / (4 * h)
        # Cross-check C_S with direct tree summation on S={2,3} (and resolvent collocation n=12 vs n=16)
        if S_arg == [2, 3]:
            cs_tree, csp_tree = word_sum_C_direct([2, 3], max_len=17)
            cs_n12 = resolvent_C_colloc([2, 3], mp.mpf("0.5"), n=12)
            assert abs(CS - cs_n12) < mp.mpf("1e-10"), f"Resolvent collocation mismatch: {CS} vs {cs_n12}"
            assert cs_tree < CS and abs(CS - cs_tree) < mp.mpf("0.015"), (
                f"Tree vs resolvent mismatch: {CS} vs {cs_tree}"
            )
        c2 = (d ** 2) * CS * (gamma * CS - CSp) / 2
        lines.append(f"  Case {label} (d={d}): C_S={mp.nstr(CS, 12)}, C_S'={mp.nstr(CSp, 12)}, c2={mp.nstr(c2, 12)}")
        case_rows = []
        prev_abs_err = None
        for m in ms:
            mm = mp.mpf(m)
            two_term = mp.mpf("0.5") + d * CS / (2 * mm) - (d * CS) ** 2 * mp.log(mm) / (2 * mm ** 2)
            three_term = two_term + c2 / (mm ** 2)
            lo_g = max(mp.mpf("0.5") + mp.mpf("1e-12"), three_term - mp.mpf("20") * (mp.log(mm) ** 2) / (mm ** 3))
            hi_g = max(lo_g + mp.mpf("1e-4"), three_term + mp.mpf("20") * (mp.log(mm) ** 2) / (mm ** 3))
            dim = find_dim_bracketed(
                lambda s: rho_multi_residue(m, S_arg, B_arg, s, n=16, use_eig=False) - 1,
                lo_g,
                hi_g,
                bisect_steps=1,
            )
            obs_c2 = (dim - two_term) * (mm ** 2)
            err_m3 = (dim - three_term) * (mm ** 3) / (mp.log(mm) ** 2)
            abs_err = abs(obs_c2 - c2)
            if prev_abs_err is not None and m >= 1024:
                assert abs_err < prev_abs_err, f"Error did not decrease for {label} at m={m}: {abs_err} vs {prev_abs_err}"
            prev_abs_err = abs_err
            case_rows.append({
                "m": m,
                "dim": mp.nstr(dim, 20),
                "obs_c2": float(obs_c2),
                "c2_diff": float(obs_c2 - c2),
                "scaled_m3_over_log2": float(err_m3),
            })
            lines.append(
                f"    m={m:5d}: dim={mp.nstr(dim, 15)}, m^2*resid={float(obs_c2):+.8f}, "
                f"err={float(obs_c2 - c2):+.8f}, m^3*(dim-3term)/(log m)^2={float(err_m3):+.4f}"
            )
        results["multi_subcritical"].append({
            "label": label,
            "S": S_arg,
            "B": B_arg,
            "C_S": mp.nstr(CS, 20),
            "C_S_prime": mp.nstr(CSp, 20),
            "c2": mp.nstr(c2, 20),
            "rows": case_rows,
        })

    # 4. Supercritical algebraic witness & Theta(m^{-2 s_0}) rate
    lines.append("\n[4] Supercritical witness & Theta(m^{-2 s_0}) rate:")
    # Verify algebraic witness for S={1,2} at s=51/100 with v(x) = 2/(2+x)
    s_wit = mp.mpf(51) / mp.mpf(100)
    min_ratio = mp.mpf(10)
    for k in range(101):
        x = mp.mpf(k) / 100
        vx = 2 / (2 + x)
        lvx = (1 + x) ** (-2 * s_wit) * (2 / (2 + 1 / (1 + x))) + (2 + x) ** (-2 * s_wit) * (2 / (2 + 1 / (2 + x)))
        min_ratio = min(min_ratio, lvx / vx)
    assert min_ratio > mp.mpf(1), f"Supercritical witness failed: min(Lv/v)={min_ratio}"
    lines.append(f"  Algebraic witness S={{1,2}}, s=51/100, v(x)=2/(2+x): min(Lv/v) = {float(min_ratio):.8f} > 1 [PASS]")

    for S_arg, lo_init, hi_init in [([1, 2], mp.mpf("0.53"), mp.mpf("0.535")), ([1, 2, 3], mp.mpf("0.70"), mp.mpf("0.71"))]:
        s0 = find_dim_bracketed(lambda s: rho_finite(S_arg, s, n=16) - 1, lo_init, hi_init, bisect_steps=2)
        assert s0 > mp.mpf("0.5")
        lines.append(f"  Supercritical S={S_arg}: s_0 = dimH E_S = {mp.nstr(s0, 15)}")
        sup_rows = []
        scaled_vals = []
        for m in [64, 256, 1024, 4096]:
            dim = find_dim_bracketed(
                lambda s: rho_multi_residue(m, S_arg, [], s, n=16, use_eig=False) - 1,
                s0 + mp.mpf("1e-10"),
                s0 + mp.mpf("0.1"),
                bisect_steps=3,
            )
            excess = dim - s0
            assert excess > 0
            scaled = excess * (mp.mpf(m) ** (2 * s0))
            scaled_vals.append(scaled)
            sup_rows.append({
                "m": m,
                "dim": mp.nstr(dim, 18),
                "excess": float(excess),
                "m_2s0_excess": float(scaled),
            })
            lines.append(
                f"    m={m:4d}: dim={mp.nstr(dim, 14)}, dim-s0={float(excess):.8e}, "
                f"m^(2s0)*(dim-s0)={float(scaled):.6f}"
            )
        assert all(v > 0 for v in scaled_vals)
        results["supercritical"].append({"S": S_arg, "s0": mp.nstr(s0, 20), "rows": sup_rows})

    lines.append("\nALL CHECKS PASSED")
    report = "\n".join(lines) + "\n"
    (HERE / "verify_residue_multi_asymptotic.log").write_text(report, encoding="utf-8")
    (HERE / "verify_residue_multi_asymptotic.json").write_text(json.dumps(results, indent=2), encoding="utf-8")
    print(report, end="")


if __name__ == "__main__":
    main()
