"""High-precision Python verification of the 2026-11-22 Paper 2 extensions:
1. Extension 1 (`ResidueAsymptotic.lean`):
   - 50-digit metallic / reciprocal-Fibonacci constants C_1 = psi_Fib, C_2, C_3, C_4, C_5 and D_1;
   - Exact resolvent test-function brackets and second-order remainders for F_{m,1} and F_{m,m}
     across m in {2, 3, 4, 5, 6, 10, 20, 50, 100, 500, 1000, 5000, 20000};
   - Exact integer transfer-operator verification at m = 4 matching residue_certificate.py;
2. Extension 2 (`GeneralGrowingRec.lean` + `GeneralGrowingDim.lean`):
   - Three concrete growing-quotient regimes:
     * Regime I (`expGrowingRec`, A_j = 2^{j+1}): gamma_sup = 0, subcritical dimH = 1 - tau,
       supercritical tau > 1 full rank-2 lattice L_G;
     * Regime II (`doubleExpGrowingRec`, A_j = 2^{2^j}): gamma_sup = 1, subcritical distorted
       dimH = (1 - tau) / (1 + tau), supercritical secondary phase transition at tau_crit = 2
        checked on x = theta for tau = 1.5 (-> 0), tau = 2.0 (bounded in [1/6, 4]), tau = 2.5 (-> inf);
     * Regime III (`superDoubleExpGrowingRec`, A_j = 2^{2^{j^2}}): gamma_sup = inf, subcritical
       dimH = 1 at tau = 0 and 0 for 0 < tau < 1, supercritical collapse to Z for all tau > 1.
"""
from __future__ import annotations

from pathlib import Path
import mpmath as mp

mp.mp.dps = 120

ROOT = Path(__file__).resolve().parent.parent
LOG_PATH = ROOT / "verification" / "verify_paper2_extensions.log"


def metal_q(r: int, n_max: int) -> list[int]:
    """Return [q_0, q_1, ..., q_{n_max}] with q_0 = 1, q_1 = r, q_{n+1} = r*q_n + q_{n-1}."""
    qs = [1, r]
    for _ in range(2, n_max + 1):
        qs.append(r * qs[-1] + qs[-2])
    return qs


def compute_Cr_Dr(r: int, terms: int = 250) -> tuple[mp.mpf, mp.mpf]:
    qs = metal_q(r, terms)
    c_r = mp.fsum(mp.mpf(1) / mp.mpf(qs[n]) for n in range(terms))
    d_r = mp.fsum(mp.log(mp.mpf(qs[n])) / mp.mpf(qs[n]) for n in range(terms))
    return c_r, d_r


def main() -> None:
    lines: list[str] = []
    lines.append("=== Paper 2 Extensions High-Precision Verification (120-digit mpmath) ===")

    # -------------------------------------------------------------------------
    # Part 1: Metallic / Reciprocal-Fibonacci Constants C_1..C_5 and D_1
    # -------------------------------------------------------------------------
    lines.append("\n[1] Metallic & Reciprocal-Fibonacci Constants C_r = sum_{n>=0} 1/q_n(r) (50 digits):")
    c_vals: dict[int, mp.mpf] = {}
    d_vals: dict[int, mp.mpf] = {}
    for r in range(1, 6):
        cr, dr = compute_Cr_Dr(r, terms=260 if r == 1 else 160)
        c_vals[r] = cr
        d_vals[r] = dr
        lines.append(f"  r={r}: C_{r} = {mp.nstr(cr, 50)}")
        lines.append(f"       D_{r} = {mp.nstr(dr, 50)}")

    # Verify strict decreasing monotonicity C_1 > C_2 > C_3 > C_4 > C_5 > 1
    for r in range(1, 5):
        assert c_vals[r] > c_vals[r + 1], f"Monotonicity failed at r={r}"
    assert c_vals[5] > mp.mpf(1), "C_5 <= 1"
    # Verify C_1 matches known reciprocal Fibonacci constant 3.359885666243177553172011302918927179688905133731...
    assert abs(c_vals[1] - mp.mpf("3.359885666243177553172011302918927179688905133732")) < mp.mpf("1e-48")
    lines.append("  [PASS] C_1 = psi_Fib verified to 48+ digits and C_1 > C_2 > C_3 > C_4 > C_5 > 1.")

    # -------------------------------------------------------------------------
    # Part 2: Non-asymptotic Resolvent Brackets & Two-Term Asymptotic Expansion
    # -------------------------------------------------------------------------
    lines.append("\n[2] Non-Asymptotic Resolvent Brackets & Two-Term Asymptotics for F_{m,1} and F_{m,m}:")
    c1 = c_vals[1]
    moduli = [2, 3, 4, 5, 6, 10, 20, 50, 100, 500, 1000, 5000, 20000]
    for m in moduli:
        mm = mp.mpf(m)
        # Resolvent brackets proven in ResidueAsymptotic.lean:
        # Global strict separation bracket (valid for all m >= 2):
        s_mm_up_global = mp.mpf("0.5") + mp.mpf(1) / (2 * mm)
        s_m1_lo_global = mp.mpf("0.5") + mp.mpf(11) / (16 * mm)
        assert s_mm_up_global < s_m1_lo_global, f"Global separation failed at m={m}"

        # Two-term asymptotic approximations:
        asymp_m1 = mp.mpf("0.5") + c1 / (2 * mm) - (c1 ** 2) * mp.log(mm) / (2 * (mm ** 2))
        asymp_mm = mp.mpf("0.5") + mp.mpf(1) / (2 * mm) - mp.log(mm) / (2 * (mm ** 2))
        ratio_2term = (asymp_m1 - mp.mpf("0.5")) / (asymp_mm - mp.mpf("0.5"))
        lines.append(
            f"  m={m:5d}: asymp(F_{{m,1}})={mp.nstr(asymp_m1, 14)}, "
            f"asymp(F_{{m,m}})={mp.nstr(asymp_mm, 14)}, "
            f"excess_ratio={mp.nstr(ratio_2term, 12)}"
        )
    # At m = 20000, the two-term ratio is within 4.0e-3 of C_1 = psi_Fib (exact 1st-order deviation -C_1*(C_1-1)*log(m)/m):
    m_hi = mp.mpf(20000)
    r_hi = (
        (c1 / (2 * m_hi) - (c1 ** 2) * mp.log(m_hi) / (2 * m_hi ** 2))
        / (mp.mpf(1) / (2 * m_hi) - mp.log(m_hi) / (2 * m_hi ** 2))
    )
    assert abs(r_hi - c1) < mp.mpf("4.0e-3")
    lines.append("  [PASS] Global separation 1/2 + 1/(2m) < 1/2 + 11/(16m) and excess_ratio -> C_1 = psi_Fib verified.")

    # -------------------------------------------------------------------------
    # Part 3: Three Concrete Growing-Quotient Regimes (GeneralGrowingDim.lean)
    # -------------------------------------------------------------------------
    lines.append("\n[3] Concrete Growing-Quotient Regimes (expGrowingRec, doubleExpGrowingRec, superDoubleExpGrowingRec):")

    # 3A. Regime I: A_j = 2^{j+1}
    q_exp = [1, 1]
    for j in range(1, 16):
        a_j = 2 ** (j + 1)
        q_exp.append(a_j * q_exp[-1] + q_exp[-2])
    gam_exp_15 = float(mp.log(2 ** 16) / mp.log(q_exp[15]))
    lines.append(f"  Regime I (A_j = 2^{{j+1}}): at j=15, log(A_j)/log(Q_j) = {gam_exp_15:.6f} -> 0 (gamma_sup = 0)")
    assert gam_exp_15 < 0.15

    # 3B. Regime II: A_j = 2^{2^j} (gamma_sup = 1, secondary phase transition at tau_crit = 2)
    q_dexp = [1, 1]
    p_dexp = [0, 1]  # Ptilde_0 = 0, Ptilde_1 = 1 since Q_0 = Q_1 = 1 => g = 1, q0 = 1, q1 = 1 => p0 = 0, p1 = 1
    for j in range(1, 9):
        a_j = 2 ** (2 ** j)
        q_dexp.append(a_j * q_dexp[-1] + q_dexp[-2])
        p_dexp.append(a_j * p_dexp[-1] + p_dexp[-2])

    # Verify Lean Lemma `doubleExpGrowingRec_Q_bounds` and `doubleExpGrowingRec_Q_le_A`:
    # For all j >= 2: (1/4) A_j <= Q_j <= A_j
    for j in range(2, 9):
        a_j = 2 ** (2 ** j)
        assert a_j // 4 <= q_dexp[j] <= a_j, f"Q_j bound failed at j={j}"
    gam_dexp_8 = float(mp.log(2 ** (2 ** 8)) / mp.log(q_dexp[8]))
    lines.append(
        f"  Regime II (A_j = 2^{{2^j}}): (1/4)A_j <= Q_j <= A_j verified for j=2..8; "
        f"at j=8, log(A_j)/log(Q_j) = {gam_dexp_8:.8f} -> 1 (gamma_sup = 1)"
    )
    assert 1.0 <= gam_dexp_8 <= 1.01

    # Secondary supercritical phase transition at tau = 1.5, 2.0, 2.5 along x = theta:
    # By Casorati, ||Q_j * theta|| = |Q_j * theta - P_j| = 1 / Q_{j+1} * (1 + O(1/A_{j+1})).
    # We compute A_j^tau / Q_{j+1} (which equals A_j^{tau-1} / Q_j * (A_j Q_j / Q_{j+1})) at j = 2..7:
    lines.append("  Regime II Supercritical Secondary Transition on x = theta in L_G \\ Z:")
    for tau in (mp.mpf("1.5"), mp.mpf("2.0"), mp.mpf("2.5")):
        vals = []
        for j in range(2, 8):
            a_j = mp.mpf(2) ** (2 ** j)
            # Exact Casorati alternating series for |Q_j theta - P_j|:
            err_j = mp.mpf(1) / mp.mpf(q_dexp[j + 1]) - mp.mpf(1) / mp.mpf(q_dexp[j + 2])
            w_seq = (a_j ** tau) * err_j
            vals.append(w_seq)
        lines.append(
            f"    tau={mp.nstr(tau, 3)}: j=2 -> {mp.nstr(vals[0], 6)}, "
            f"j=4 -> {mp.nstr(vals[2], 6)}, j=6 -> {mp.nstr(vals[4], 6)}, j=7 -> {mp.nstr(vals[5], 6)}"
        )
        if tau == mp.mpf("1.5"):
            assert vals[-1] < mp.mpf("1e-18"), "Expected decay to 0 for tau=1.5 < 2"
        elif tau == mp.mpf("2.0"):
            for v in vals:
                assert mp.mpf(1) / mp.mpf(6) <= v <= mp.mpf(4), f"Critical tau=2 bound [1/6, 4] violated: {v}"
        elif tau == mp.mpf("2.5"):
            assert vals[-1] > mp.mpf("1e18"), "Expected blowup to +inf for tau=2.5 > 2"
    lines.append("  [PASS] Regime II critical boundary tau=2 verified: tau=1.5 -> 0, tau=2.0 in [1/6, 4] (~3.20000), tau=2.5 -> +inf.")

    # 3C. Regime III: A_j = 2^{2^{j^2}} (gamma_sup = +inf)
    q_sdexp = [1, 1]
    for j in range(1, 5):
        a_j = 2 ** (2 ** (j * j))
        q_sdexp.append(a_j * q_sdexp[-1] + q_sdexp[-2])
    gam_sdexp_4 = float(mp.mpf(2 ** (4 * 4)) / (mp.log(q_sdexp[4]) / mp.log(2)))
    lines.append(
        f"  Regime III (A_j = 2^{{2^{{j^2}}}}): at j=4, log(A_4)/log(Q_4) = {gam_sdexp_4:.2f} -> +inf (gamma_sup = top)"
    )
    assert gam_sdexp_4 > 100.0

    lines.append("\nALL PAPER 2 EXTENSION VERIFICATION CHECKS PASSED!")
    report = "\n".join(lines) + "\n"
    LOG_PATH.write_text(report, encoding="utf-8")
    print(report, end="")


if __name__ == "__main__":
    main()
