"""
High-precision numerical verification for:
1. Theorem B1: Exact value c_phi(x) = 1 - 2/sqrt(5) and exact second limit point
   4/sqrt(5) - 1 for irrationals with eventually (A_k, 1, 1), A_k -> inf.
2. Corollary B2: c_phi(6 - e) = c_phi(e) = c_phi(M(e^{1/m})) = 1 - 2/sqrt(5),
   plus continued fraction verification of e, 6 - e, and e^{1/m} (m = 1..5).
3. Norm parity rigidity check over all coprime (a, b, c, d) with |ad - bc| = 1
   in a finite search box.
4. B = 2 control model 11/2 - e: periodic Hurwitz blocks and upper bound
   c_phi(11/2 - e) <= 9/(4*sqrt(5)) - 1 = sqrt(5)/4 - 1 + 1/sqrt(5) ~ 0.00623059.

All computations use mpmath with 400 decimal digits of working precision.
"""

from __future__ import annotations
import math
import mpmath as mp

mp.mp.dps = 400


def cf_expansion(x: mp.mpf, n_terms: int) -> list[int]:
    """Compute the first n_terms regular continued fraction partial quotients of x."""
    res: list[int] = []
    val = mp.mpf(x)
    for _ in range(n_terms):
        a = int(mp.floor(val))
        res.append(a)
        frac = val - a
        if frac == 0:
            break
        val = mp.mpf(1) / frac
    return res


def convergents(a: list[int]) -> tuple[list[int], list[int]]:
    """Compute convergent numerators p_n and denominators q_n for partial quotients a[0..N]."""
    p = [0] * len(a)
    q = [0] * len(a)
    for i, ai in enumerate(a):
        if i == 0:
            p[i], q[i] = ai, 1
        elif i == 1:
            p[i], q[i] = ai * a[0] + 1, ai
        else:
            p[i] = ai * p[i - 1] + p[i - 2]
            q[i] = ai * q[i - 1] + q[i - 2]
    return p, q


def eval_orbit_error(x: mp.mpf, prefix: list[int], tail_pre: list[int]) -> tuple[mp.mpf, mp.mpf]:
    """
    For beta = [prefix[0]; prefix[1], ..., prefix[-1], tail_pre..., 1, 1, 1, ...],
    compute exact h(beta) and h(beta)*|x - beta| using the matrix of prefix + tail_pre.
    """
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_conj = (mp.mpf(1) - mp.sqrt(5)) / 2
    full = prefix + tail_pre
    p, q = convergents(full)
    m = len(full)
    if m == 1:
        p1, q1, p0, q0 = p[0], q[0], 1, 0
    else:
        p1, q1, p0, q0 = p[m - 1], q[m - 1], p[m - 2], q[m - 2]

    beta = (p1 * phi + p0) / (q1 * phi + q0)
    beta_conj = (p1 * phi_conj + p0) / (q1 * phi_conj + q0)
    h_beta = mp.mpf(2) / abs(beta - beta_conj)
    err = h_beta * abs(x - beta)
    return h_beta, err


def section_constants() -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    c1 = mp.mpf(1) - mp.mpf(2) / mp.sqrt(5)
    c2 = mp.mpf(4) / mp.sqrt(5) - mp.mpf(1)
    c_half = mp.sqrt(5) / 4 - mp.mpf(1) + mp.mpf(1) / mp.sqrt(5)
    assert abs(c_half - (mp.mpf(9) / (4 * mp.sqrt(5)) - 1)) < mp.mpf("1e-70")
    print("=== 1. Exact Constants (50 digits) ===")
    print(f"c1 = 1 - 2/sqrt(5)               = {mp.nstr(c1, 50)}")
    print(f"c2 = 4/sqrt(5) - 1               = {mp.nstr(c2, 50)}")
    print(f"c_half = 9/(4*sqrt(5)) - 1       = {mp.nstr(c_half, 50)}")
    print()
    return c1, c2, c_half


def section_cf_hurwitz() -> None:
    print("=== 2. Hurwitz Continued Fractions of e, 6 - e, and e^(1/m) ===")
    e_val = mp.e
    cf_e = cf_expansion(e_val, 33)
    print(f"e (first 33 terms):     {cf_e}")
    # e = [2; 1, 2, 1, 1, 4, 1, 1, 6, ...] -> indices 2 + 3k are 2(k+1), followed by 1, 1
    for k in range(10):
        idx = 2 + 3 * k
        assert cf_e[idx] == 2 * (k + 1) and cf_e[idx + 1] == 1 and cf_e[idx + 2] == 1

    cf_6me = cf_expansion(mp.mpf(6) - e_val, 33)
    print(f"6 - e (first 33 terms): {cf_6me}")
    # 6 - e = [3; 3, 1, 1, 4, 1, 1, 6, 1, 1, 8, ...] -> after [3; 3, 1, 1], (2k+4, 1, 1)
    for k in range(9):
        idx = 4 + 3 * k
        assert cf_6me[idx] == 2 * (k + 2) and cf_6me[idx + 1] == 1 and cf_6me[idx + 2] == 1

    for m in range(2, 6):
        cf_em = cf_expansion(mp.exp(mp.mpf(1) / m), 31)
        print(f"e^(1/{m}) (first 31 terms): {cf_em}")
        assert cf_em[0] == 1
        for k in range(10):
            idx = 1 + 3 * k
            assert cf_em[idx] == (2 * k + 1) * m - 1
            assert cf_em[idx + 1] == 1 and cf_em[idx + 2] == 1
    print("All Hurwitz patterns for e, 6 - e, and e^(1/m) (m = 2..5) VERIFIED.\n")


def section_norm_parity_check(c1: mp.mpf, c2: mp.mpf) -> None:
    print("=== 3. Exhaustive Finite Check of Norm Parity Rigidity Lemma ===")
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_conj = (mp.mpf(1) - mp.sqrt(5)) / 2
    vals_below_c2: set[tuple[int, int, int, int]] = set()
    min_above_c1 = mp.mpf("inf")
    count = 0
    for a in range(-6, 7):
        for b in range(-6, 7):
            for c in range(-6, 7):
                for d in range(-6, 7):
                    det = a * d - b * c
                    if abs(det) != 1:
                        continue
                    count += 1
                    eta = (a * phi + b) / (c * phi + d)
                    eta_c = (a * phi_conj + b) / (c * phi_conj + d)
                    h_eta = mp.mpf(2) / abs(eta - eta_c)
                    val = h_eta * abs(2 - eta) * abs(eta_c) / 2
                    # Algebraic formula check: val == |2*k0 - det*sqrt(5)| / sqrt(5)
                    m0 = -2 * a * c + a * a + 2 * b * d - b * b + b * c + a * d - a * b
                    assert m0 % 2 == 0, f"Odd m0={m0} for {(a,b,c,d)}"
                    alg_val = abs(mp.mpf(m0) - det * mp.sqrt(5)) / mp.sqrt(5)
                    assert abs(val - alg_val) < mp.mpf("1e-65")
                    if val < c2 - mp.mpf("1e-30"):
                        assert abs(val - c1) < mp.mpf("1e-65")
                        # Confirm eta is either phi or phi + 1
                        assert abs(eta - phi) < mp.mpf("1e-65") or abs(eta - (phi + 1)) < mp.mpf("1e-65")
                        vals_below_c2.add((a, b, c, d))
                    else:
                        if val < min_above_c1:
                            min_above_c1 = val
    assert abs(min_above_c1 - c2) < mp.mpf("1e-65")
    print(f"Checked {count} GL_2(Z) matrices in [-6, 6]^4.")
    print(f"All m0 even: PASS. Matrices with value < c2: {len(vals_below_c2)} (all yield eta in {{phi, phi+1}} and value = c1).")
    print(f"Minimum value >= c2: {mp.nstr(min_above_c1, 25)} (exact match to 4/sqrt(5) - 1).\n")


def section_theorem_b1_families(c1: mp.mpf, c2: mp.mpf) -> None:
    print("=== 4. Convergence of Extremal and Second-Limit-Point Families (x = e and x = 6 - e) ===")
    for name, x_val, s0 in [("e", mp.e, 2), ("6 - e", mp.mpf(6) - mp.e, 4)]:
        cf = cf_expansion(x_val, 200)
        print(f"--- Target x = {name} ---")
        for k in [10, 20, 40, 60]:
            s_k = s0 + 3 * k
            A_k = cf[s_k]
            pref_s = cf[: s_k + 1]       # [a_0; ..., a_{s_k}]
            pref_sm1 = cf[:s_k]          # [a_0; ..., a_{s_k - 1}]

            _, e_f1 = eval_orbit_error(x_val, pref_s, [])                # [..., A_k, \bar{1}]
            _, e_f2 = eval_orbit_error(x_val, pref_s, [2])               # [..., A_k, 2, \bar{1}]
            _, e_s1 = eval_orbit_error(x_val, pref_s, [2, 2])            # [..., A_k, 2, 2, \bar{1}]
            _, e_s2 = eval_orbit_error(x_val, pref_sm1, [A_k - 1])       # [..., A_k - 1, \bar{1}]
            _, e_s3 = eval_orbit_error(x_val, pref_sm1, [A_k + 1, 2])    # [..., A_k + 1, 2, \bar{1}]
            _, e_s4 = eval_orbit_error(x_val, pref_sm1, [2])             # [..., 2, \bar{1}]
            print(
                f"k={k:2d} (A_k={A_k:3d}): "
                f"F1={mp.nstr(e_f1, 10)} F2={mp.nstr(e_f2, 10)} | "
                f"S1={mp.nstr(e_s1, 10)} S2={mp.nstr(e_s2, 10)} "
                f"S3={mp.nstr(e_s3, 10)} S4={mp.nstr(e_s4, 10)}"
            )
            if k == 60:
                assert abs(e_f1 - c1) < mp.mpf("0.005")
                assert abs(e_f2 - c1) < mp.mpf("0.005")
                assert abs(e_s1 - c2) < mp.mpf("0.025")
                assert abs(e_s2 - c2) < mp.mpf("0.025")
                assert abs(e_s3 - c2) < mp.mpf("0.025")
                assert abs(e_s4 - c2) < mp.mpf("0.025")
    print()


def section_gl2z_invariance(c1: mp.mpf) -> None:
    print("=== 5. GL_2(Z)-Invariance Verification on M(e^(1/m)) ===")
    # Test M(x) = (2x + 3)/(x + 2) (det = 1) on e^(1/3)
    x = mp.exp(mp.mpf(1) / 3)
    y = (2 * x + 3) / (x + 2)
    cf_x = cf_expansion(x, 70)
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_c = (mp.mpf(1) - mp.sqrt(5)) / 2
    for k in [5, 10, 15, 20]:
        s_k = 1 + 3 * k
        pref = cf_x[: s_k + 1]
        p, q = convergents(pref)
        p1, q1, p0, q0 = p[-1], q[-1], p[-2], q[-2]
        beta = (p1 * phi + p0) / (q1 * phi + q0)
        beta_c = (p1 * phi_c + p0) / (q1 * phi_c + q0)
        h_beta = mp.mpf(2) / abs(beta - beta_c)
        err_x = h_beta * abs(x - beta)

        gamma = (2 * beta + 3) / (beta + 2)
        gamma_c = (2 * beta_c + 3) / (beta_c + 2)
        h_gamma = mp.mpf(2) / abs(gamma - gamma_c)
        err_y = h_gamma * abs(y - gamma)
        ratio = err_y / err_x
        expected_ratio = abs(beta_c + 2) / abs(x + 2)
        assert abs(ratio - expected_ratio) < mp.mpf("1e-65")
        print(
            f"k={k:2d}: err_x={mp.nstr(err_x, 12)}, err_y={mp.nstr(err_y, 12)}, "
            f"ratio={mp.nstr(ratio, 15)}"
        )
        if k == 20:
            assert abs(err_x - c1) < mp.mpf("0.01")
            assert abs(err_y - c1) < mp.mpf("0.01")
    print()


def section_b2_model(c_half: mp.mpf) -> None:
    print("=== 6. B = 2 Control Model: x = 11/2 - e ===")
    x = mp.mpf(11) / 2 - mp.e
    cf = cf_expansion(x, 120)
    print(f"11/2 - e (first 55 terms): {cf[:55]}")

    # Rigorous base-period check via Theorem thm:affine-window (A=11, B=2, C=-2):
    # L = max(B, |C|)^2 = 4, T = 2*B*|C| = 8, G_j = gcd(11*Q_j - 2*P_j, 2*Q_j) = 1.
    # For all j >= 6 (j - 1 > L), W_{j+8} = (b_j + 4, S_j), so verifying W_6..W_13
    # unconditionally establishes the period-10 Hurwitz block for all k >= 1.
    P_h, Q_h = [1, 3], [1, 1]
    for j in range(1, 16):
        P_h.append((4 * j + 2) * P_h[-1] + P_h[-2])
        Q_h.append((4 * j + 2) * Q_h[-1] + Q_h[-2])
    px, qx = convergents(cf)
    cutoffs: dict[int, int] = {}
    for j in range(5, 16):
        num = 11 * Q_h[j] - 2 * P_h[j]
        den = 2 * Q_h[j]
        assert math.gcd(num, den) == 1, f"Expected G_{j}=1"
        idx = qx.index(den)
        assert px[idx] == num
        cutoffs[j] = idx
    # Check base period W_6..W_13 (indices 24..63):
    for m in range(1, 5):
        j_even = 2 * m + 4  # 6, 8, 10, 12
        j_odd = 2 * m + 5   # 7, 9, 11, 13
        w_even = cf[cutoffs[j_even] + 1 : cutoffs[j_even + 1] + 1]
        w_odd = cf[cutoffs[j_odd] + 1 : cutoffs[j_odd + 1] + 1]
        assert w_even == [m + 1, 1, 1, 1, 2], f"Mismatch at W_{j_even}: {w_even}"
        assert w_odd == [m + 2, 2, 1, 1, 1], f"Mismatch at W_{j_odd}: {w_odd}"
    print(
        "Theorem thm:affine-window base period W_6..W_13 (A=11, B=2, C=-2, L=4, T=8, G_j=1) "
        "VERIFIED via exact Hermite convergents."
    )

    # Also verify 10 consecutive period-10 blocks starting at index 8:
    start = 8
    k0 = cf[start + 1]
    assert k0 == 1
    print(f"Period-10 Hurwitz block starts at index {start} with initial k = {k0}:")
    for j in range(10):
        idx = start + 10 * j
        blk = cf[idx : idx + 10]
        k = k0 + j
        expected = [2, k, 2, 1, 1, 1, k, 1, 1, 1]
        assert blk == expected, f"Mismatch at block j={j}: got {blk}, expected {expected}"
    print("Verified 10 consecutive blocks of [2, k, 2, 1, 1, 1, k, 1, 1, 1] (100 partial quotients).")

    # Evaluate orbit family beta_j = [a_0; ..., a_{idx+6} (= k), \bar{1}]
    # After a_{idx+6} = k, the next partial quotients are 1, 1, 1, 2, k+1, 2, ...
    # So T_m -> [1; 1, 1, 2, inf] = 1 + 1/(1 + 1/(1 + 1/2)) = 1 + 1/(5/3) = 8/5 = 1.6
    # Wait: let's check both [..., a_{idx+6}, \bar{1}] and [..., a_{idx+1}, ...]
    # For a_{idx+6} = k: suffix is (1, 1, 1, 2, k+1, ...), so T_m -> [1; 1, 1, 2, inf] = 8/5 = 1.6!
    # Check: (2/sqrt(5)) * |8/5 - phi| * |phi'| / (8/5) = (2/sqrt(5)) * (phi - 8/5) * (phi - 1) / (8/5)
    # Wait: (phi - 8/5)*(phi - 1) = (phi^2 - 13/5 phi + 8/5) = (1 + phi - 13/5 phi + 8/5) = 13/5 - 8/5 phi
    # Divide by 8/5: 13/8 - phi = 9/8 - sqrt(5)/2.
    # Multiply by 2/sqrt(5): 9/(4*sqrt(5)) - 1 = sqrt(5)/4 - 1 + 1/sqrt(5)!
    print("Evaluating beta_j = [a_0; ..., a_{idx+6} (= k), 1, 1, 1, ...] (tail after second k in block):")
    cf_long = cf_expansion(x, 350)
    for j in [5, 10, 15, 25]:
        idx = start + 10 * j
        pos = idx + 6
        k = cf_long[pos]
        _, err = eval_orbit_error(x, cf_long[: pos + 1], [])
        print(f"  j={j:2d} (k={k:2d}, pos={pos:3d}): h(beta)*|x - beta| = {mp.nstr(err, 15)}")
        if j == 25:
            assert abs(err - c_half) < mp.mpf("1e-3")
    print(f"Theoretical limit 9/(4*sqrt(5)) - 1            = {mp.nstr(c_half, 15)}")
    print("B = 2 upper bound VERIFIED.\n")


if __name__ == "__main__":
    c1, c2, c_half = section_constants()
    section_cf_hurwitz()
    section_norm_parity_check(c1, c2)
    section_theorem_b1_families(c1, c2)
    section_gl2z_invariance(c1)
    section_b2_model(c_half)
    print("ALL VERIFICATIONS PASSED.")
