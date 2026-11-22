"""
High-precision (400-digit mpmath) verification for Parallel Track 2 / Deep-Dive #2:
1. General rational-endpoint norm-congruence rigidity identity:
   Phi_{u,v}(eta) = h(eta) * |u - eta| * |eta' + v| / (u + v) = |(ad-bc)*M_{u,v} / (D*sqrt(5)) - 1|
   and M_{u,v}^2 - 5*D^2 = 4 * N(xi_1) * N(xi_2) across all 744 GL_2(Z) matrices in [-6, 6]^4.
2. Z[phi] norm mod 5 ramification identity:
   N(p*phi + q) = -p^2 + p*q + q^2 = -(p + 2*q)^2 + 5*(p + q)*q.
3. Exact Pell-norm parity rigidity (Lemma lem:pell-b2-rigidity) at D = 8 endpoints
   (u, v) = (8/5, 0), (8/3, 0), and all period-10 intermediate shifts (3/2, 1/2), (2, 2/3),
   (1, 3/5), (5/3, 1), plus comparison with (u, v) = (2, 1/2) (D = 5):
   - Minimum 9/(4*sqrt(5)) - 1 (m = 9, from Pell equation 9^2 - 5*4^2 = 1),
     uniquely attained at eta = phi for (8/5, 0) and eta = phi + 1 for (8/3, 0);
   - Second minimum 1 - 7/(4*sqrt(5)) (m = 7) across all odd m != 9.
4. Theorem thm:golden-b2-exact for x = 11/2 - e:
   - Exact c_phi(11/2 - e) = 9/(4*sqrt(5)) - 1 attained along both extremal families
     beta_k^(1) = [a_0; ..., a_{s_k}, 2, \\bar{1}] and beta_k^(2) = [a_0; ..., a_{t_k}, \\bar{1}];
   - Exact second smallest limit point 1 - 7/(4*sqrt(5)) attained along the four families
     gamma_k^(1) = [a_0; ..., a_{s_k}, \\bar{1}],
     gamma_k^(2) = [a_0; ..., a_{t_k}, 2, \\bar{1}],
     gamma_k^(3) = [a_0; ..., a_{s_k}, 2, 1, 2, \\bar{1}],
     gamma_k^(4) = [a_0; ..., a_{t_k}, 1, 1, 1, 2, \\bar{1}].
"""

from __future__ import annotations
import math
import mpmath as mp

mp.mp.dps = 400


def zphi_norm(p: int, q: int) -> int:
    return -p * p + p * q + q * q


def M_uv_int(p1: int, q1: int, p2: int, q2: int, a: int, b: int, c: int, d: int) -> int:
    return (
        2 * a * a * q1 * q2
        - 2 * a * b * q1 * q2
        - 2 * a * c * p1 * q2
        + 2 * a * c * p2 * q1
        + a * d * p1 * q2
        - a * d * p2 * q1
        - 2 * b * b * q1 * q2
        + b * c * p1 * q2
        - b * c * p2 * q1
        + 2 * b * d * p1 * q2
        - 2 * b * d * p2 * q1
        - 2 * c * c * p1 * p2
        + 2 * c * d * p1 * p2
        + 2 * d * d * p1 * p2
    )


def cf_expansion(x: mp.mpf, n_terms: int) -> list[int]:
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


def section_1_constants() -> tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    c_min = mp.mpf(9) / (4 * mp.sqrt(5)) - 1
    c_b1 = 1 - mp.mpf(2) / mp.sqrt(5)
    c_sec = 1 - mp.mpf(7) / (4 * mp.sqrt(5))
    c_11 = mp.mpf(11) / (4 * mp.sqrt(5)) - 1
    assert 0 < c_min < c_b1 < c_sec < c_11
    print("=== 1. Exact Spectral Constants for B = 2 Model (50 digits) ===")
    print(f"c_min = 9/(4*sqrt(5)) - 1  (m=9)  = {mp.nstr(c_min, 50)}")
    print(f"c_b1  = 1 - 2/sqrt(5)      (m=8)  = {mp.nstr(c_b1, 50)}")
    print(f"c_sec = 1 - 7/(4*sqrt(5))  (m=7)  = {mp.nstr(c_sec, 50)}")
    print(f"c_11  = 11/(4*sqrt(5)) - 1 (m=11) = {mp.nstr(c_11, 50)}")
    print("Pell fundamental identity: 9^2 - 5 * 4^2 =", 9**2 - 5 * 4**2)
    print()
    return c_min, c_b1, c_sec, c_11


def section_2_mod5_ramification() -> None:
    print("=== 2. Z[phi] Norm Mod 5 Ramification Identity Check ===")
    count = 0
    for p in range(-50, 51):
        for q in range(-50, 51):
            n_val = zphi_norm(p, q)
            rhs = -((p + 2 * q) ** 2) + 5 * (p + q) * q
            assert n_val == rhs
            assert (n_val % 5 == 0) == ((p + 2 * q) % 5 == 0)
            assert (n_val % 5) in {0, 1, 4}
            count += 1
    print(f"Verified N(p*phi+q) = -(p+2q)^2 + 5(p+q)q and 5|N <=> 5|(p+2q) across {count} pairs.\n")


def section_3_exhaustive_rational_endpoints(c_min: mp.mpf, c_sec: mp.mpf) -> None:
    print("=== 3. Exhaustive 744-Matrix Check of Rational-Endpoint Rigidity ===")
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_conj = (mp.mpf(1) - mp.sqrt(5)) / 2

    # All 6 distinct rational endpoint pairs (u, v) = (p1/q1, p2/q2) occurring across the 8 bounded
    # steps in the period-10 block (k, 2, 1, 1, 1, k, 1, 1, 1, 2) of 11/2 - e:
    phase_endpoints = [
        ("m = t_k + 1: (8/5, 0)", 8, 5, 0, 1),
        ("m = s_k + 1: (8/3, 0)", 8, 3, 0, 1),
        ("m = s_k + 2 & t_k + 3: (3/2, 1/2)", 3, 2, 1, 2),
        ("m = s_k + 3 & t_k + 4: (2/1, 2/3)", 2, 1, 2, 3),
        ("m = s_k + 4: (1/1, 3/5)", 1, 1, 3, 5),
        ("m = t_k + 2: (5/3, 1/1)", 5, 3, 1, 1),
    ]

    for label, p1, q1, p2, q2 in phase_endpoints:
        D = p1 * q2 + p2 * q1
        assert D == 8
        u = mp.mpf(p1) / q1
        v = mp.mpf(p2) / q2
        min_val = mp.mpf("inf")
        sec_val = mp.mpf("inf")
        min_etas: set[str] = set()
        sec_etas: set[str] = set()
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
                        val = h_eta * abs(u - eta) * abs(eta_c + v) / (u + v)

                        M_val = M_uv_int(p1, q1, p2, q2, a, b, c, d)
                        N1 = zphi_norm(p1 * c - q1 * a, p1 * d - q1 * b)
                        N2 = zphi_norm(q2 * a + p2 * c, q2 * b + p2 * d)
                        assert M_val * M_val - 5 * (det * D) ** 2 == 4 * N1 * N2
                        assert M_val % 2 == 0
                        m_half = det * (M_val // 2)
                        assert m_half % 2 == 1, f"Expected odd m_half, got {m_half}"

                        alg_val = abs(mp.mpf(m_half) / (4 * mp.sqrt(5)) - 1)
                        assert abs(val - alg_val) < mp.mpf("1e-350")

                        if abs(val - c_min) < mp.mpf("1e-100"):
                            assert m_half == 9
                            min_etas.add(mp.nstr(eta, 20))
                            if val < min_val:
                                min_val = val
                        else:
                            assert val >= c_sec - mp.mpf("1e-100")
                            if abs(val - c_sec) < mp.mpf("1e-100"):
                                assert m_half == 7
                                sec_etas.add(mp.nstr(eta, 20))
                            if val < sec_val:
                                sec_val = val

        assert count == 744
        assert abs(min_val - c_min) < mp.mpf("1e-350")
        assert abs(sec_val - c_sec) < mp.mpf("1e-350")
        if (p1, q1, p2, q2) == (8, 5, 0, 1):
            assert min_etas == {mp.nstr(phi, 20)}
        elif (p1, q1, p2, q2) == (8, 3, 0, 1):
            assert min_etas == {mp.nstr(phi + 1, 20)}
        print(
            f"  {label:35s} (744 matrices): "
            f"min = {mp.nstr(min_val, 16)} (unique eta={sorted(min_etas)}), "
            f"2nd = {mp.nstr(sec_val, 16)} ({len(sec_etas)} etas)"
        )

    # Also check (u, v) = (2, 1/2) (D = 5) for completeness:
    p1, q1, p2, q2 = 2, 1, 1, 2
    D = p1 * q2 + p2 * q1
    assert D == 5
    u, v = mp.mpf(2), mp.mpf(1) / 2
    min_d5 = mp.mpf("inf")
    for a in range(-6, 7):
        for b in range(-6, 7):
            for c in range(-6, 7):
                for d in range(-6, 7):
                    det = a * d - b * c
                    if abs(det) != 1:
                        continue
                    eta = (a * phi + b) / (c * phi + d)
                    eta_c = (a * phi_conj + b) / (c * phi_conj + d)
                    h_eta = mp.mpf(2) / abs(eta - eta_c)
                    val = h_eta * abs(u - eta) * abs(eta_c + v) / (u + v)
                    M_val = M_uv_int(p1, q1, p2, q2, a, b, c, d)
                    N1 = zphi_norm(p1 * c - q1 * a, p1 * d - q1 * b)
                    N2 = zphi_norm(q2 * a + p2 * c, q2 * b + p2 * d)
                    assert M_val * M_val - 5 * (det * D) ** 2 == 4 * N1 * N2
                    alg_val = abs(mp.mpf(det * M_val) / (5 * mp.sqrt(5)) - 1)
                    assert abs(val - alg_val) < mp.mpf("1e-350")
                    if val < min_d5:
                        min_d5 = val
    expected_d5 = 1 - mp.mpf(11) / (5 * mp.sqrt(5))
    assert abs(min_d5 - expected_d5) < mp.mpf("1e-350")
    print(
        f"  Comparison (u,v)=(2, 1/2) (D=5, 744 matrices): "
        f"min = 1 - 11/(5*sqrt(5)) = {mp.nstr(min_d5, 16)}"
    )
    print()


def section_4_b2_exact_theorem(c_min: mp.mpf, c_sec: mp.mpf) -> None:
    print("=== 4. Theorem thm:golden-b2-exact Verification on x = 11/2 - e (400 digits) ===")
    x = mp.mpf(11) / 2 - mp.e
    cf = cf_expansion(x, 450)

    # Check 35 consecutive period-10 Hurwitz blocks starting at index 8:
    start = 8
    for j in range(35):
        idx = start + 10 * j
        blk = cf[idx : idx + 10]
        k = j + 1
        assert blk == [2, k, 2, 1, 1, 1, k, 1, 1, 1], f"Mismatch at block j={j}: {blk}"
    print("Verified 35 consecutive period-10 Hurwitz blocks [2, k, 2, 1, 1, 1, k, 1, 1, 1] (350 terms).")

    print("\n--- Convergence of Extremal Families (B1, B2 -> 9/(4*sqrt(5)) - 1) ---")
    print("    and Second-Limit-Point Families (G1, G2, G3, G4 -> 1 - 7/(4*sqrt(5))) ---")
    for j in [5, 10, 20, 30, 34]:
        idx = start + 10 * j
        s_k = idx + 1  # first k in block
        t_k = idx + 6  # second k in block
        k = cf[s_k]
        assert cf[t_k] == k

        _, e_b1 = eval_orbit_error(x, cf[: s_k + 1], [2])             # [..., a_{s_k}, 2, \bar{1}]
        _, e_b2 = eval_orbit_error(x, cf[: t_k + 1], [])              # [..., a_{t_k}, \bar{1}]
        _, e_g1 = eval_orbit_error(x, cf[: s_k + 1], [])              # [..., a_{s_k}, \bar{1}]
        _, e_g2 = eval_orbit_error(x, cf[: t_k + 1], [2])             # [..., a_{t_k}, 2, \bar{1}]
        _, e_g3 = eval_orbit_error(x, cf[: s_k + 1], [2, 1, 2])       # [..., a_{s_k}, 2, 1, 2, \bar{1}]
        _, e_g4 = eval_orbit_error(x, cf[: t_k + 1], [1, 1, 1, 2])    # [..., a_{t_k}, 1, 1, 1, 2, \bar{1}]

        print(
            f"k={k:2d}: B1={mp.nstr(e_b1, 12)} B2={mp.nstr(e_b2, 12)} | "
            f"G1={mp.nstr(e_g1, 10)} G2={mp.nstr(e_g2, 10)} "
            f"G3={mp.nstr(e_g3, 10)} G4={mp.nstr(e_g4, 10)}"
        )
        if j == 34:
            assert abs(e_b1 - c_min) < mp.mpf("3e-4")
            assert abs(e_b2 - c_min) < mp.mpf("3e-4")
            assert abs(e_g1 - c_sec) < mp.mpf("1.5e-2")
            assert abs(e_g2 - c_sec) < mp.mpf("1.5e-2")
            assert abs(e_g3 - c_sec) < mp.mpf("1.5e-2")
            assert abs(e_g4 - c_sec) < mp.mpf("1.5e-2")

    # Comprehensive non-extremal sweep across all 10 positions in block j = 30 (k = 31):
    j = 30
    idx = start + 10 * j
    s_k = idx + 1
    t_k = idx + 6
    k = cf[s_k]
    min_non_extremal = mp.mpf("inf")
    tested_candidates = 0
    candidate_tails = [[], [2], [3], [2, 2], [1, 2], [2, 1, 2], [1, 1, 2], [1, 1, 1, 2]]
    for pos in range(idx, idx + 10):
        a_pos = cf[pos]
        for q_alt in [1, 2, 3, max(1, a_pos - 1), a_pos + 1]:
            if q_alt == a_pos:
                continue
            for tail in candidate_tails:
                pref = cf[:pos] + [q_alt]
                # Check if this candidate coincides with an extremal point beta_k^(1) or beta_k^(2):
                # beta_k^(1) replaces a_{t_k} = k (offset 6) by 1 followed by \bar{1}
                # beta_{k-1}^(2) replaces a_{t_{k-1}+4} = a_{idx} = 2 (offset 0) by 1 followed by \bar{1}
                is_b1 = (pos == t_k and q_alt == 1 and set(tail) <= {1})
                is_b2 = (pos == idx and q_alt == 1 and set(tail) <= {1})
                if is_b1 or is_b2:
                    continue
                _, err = eval_orbit_error(x, pref, tail)
                tested_candidates += 1
                if err < min_non_extremal:
                    min_non_extremal = err

    print(
        f"\nNon-extremal sweep across block j={j} (k={k}, {tested_candidates} distinct orbit points):"
    )
    print(f"  Minimum non-extremal h(beta)*|x - beta| = {mp.nstr(min_non_extremal, 15)}")
    print(f"  Theoretical 2nd limit point c_sec       = {mp.nstr(c_sec, 15)}")
    assert min_non_extremal > mp.mpf("0.20")
    print("ALL B = 2 EXACT VALUE & SECOND LIMIT POINT CHECKS PASSED.")


if __name__ == "__main__":
    c_min, c_b1, c_sec, c_11 = section_1_constants()
    section_2_mod5_ramification()
    section_3_exhaustive_rational_endpoints(c_min, c_sec)
    section_4_b2_exact_theorem(c_min, c_sec)
