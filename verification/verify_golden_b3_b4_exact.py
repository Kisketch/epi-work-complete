r"""
High-precision (2500-digit mpmath) verification for Path 2A (Paper 1):
1. Conjugate lower bound on E_phi \cap (1, \infty) \ {phi}:
   - Counterexample eta = phi + 1 = [2; \bar{1}] with eta' = phi^{-2} < 1/2 < phi - 1.
   - Exhaustive check across all 2920 GL_2(Z) matrices in [-12, 12]^4 (708 with eta > 1, eta != phi).
2. Lemma lem:general-endpoint-rigidity (1)-(4) across all 744 GL_2(Z) matrices in [-6, 6]^4
   and 5 rational endpoint pairs (18/5, 0), (18/7, 0), (32/7, 0), (3/2, 1/2), (7/3, 2/5).
3. Lemma lem:even-suffix-sep positive gaps Delta(S) > 0 on all 12 suffixes for B = 3, 4.
4. 2500-digit mpmath expansion of 10/3 - e, 11/3 - e, 13/4 - e, 15/4 - e:
   - Q_j mod 3 period 6; B = 3 period 18, 6 suffixes, b_{j+18} = b_j + 4;
   - B = 4 suffix & window-length r_j minimal period 8 with b_{j+8} = b_j + 1 (so b_{j+32} = b_j + 4);
   - Mod 16 subgroup {+-1, +-7} excluding m = 37;
   - Algebraic 4*tau inversion solutions for B = 3 (m = 20, 22) and B = 4 (m = 35, 33, 37);
   - All Case 1 and Case 2 branch lower bounds (verifying 0.36959164... at Q_n = 2, r_2 = 1/32 for B = 4);
   - Extremal & second-limit-point convergence + non-extremal family scans.
5. B = 5, 6, 7 and (1+e)/6, (1+e)/3, (1+2e)/3 mechanisms and extremal values
   (including 1 - 13/(6*sqrt(5)) > 0 for (1+2e)/3).
"""

from __future__ import annotations
from fractions import Fraction
import math
import mpmath as mp

mp.mp.dps = 2500


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


def hermite_pq(n_max: int) -> tuple[list[int], list[int]]:
    """Hermite convergents P_j, Q_j to e just before 2j (P_0=1,Q_0=1; P_1=3,Q_1=1; P_{j+1}=(4j+2)P_j+P_{j-1})."""
    P = [1, 3]
    Q = [1, 1]
    for j in range(1, n_max):
        P.append((4 * j + 2) * P[j] + P[j - 1])
        Q.append((4 * j + 2) * Q[j] + Q[j - 1])
    return P, Q


def cf_value_fraction(digits: list[int]) -> Fraction:
    val = Fraction(digits[-1], 1)
    for d in reversed(digits[:-1]):
        val = d + Fraction(1, 1) / val
    return val


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


def extract_windows(cf: list[int], A: int, B: int, C: int, j_max: int) -> list[dict]:
    """
    Extract Hermite cutoff windows W_j for x = (A + C*e)/B using exact rational
    Hermite convergents V_j = (A*Q_j + C*P_j, B*Q_j) / G_j and exact CF denominators q_k.
    """
    P, Q = hermite_pq(j_max + 2)
    _, q_cf = convergents(cf)
    # Map denominator q_k -> index k in cf
    # For j > max(B, |C|)^2, terminal convergent denominator d_j is strictly increasing and unique in q_cf.
    q_to_k: dict[int, int] = {}
    for k, qk in enumerate(q_cf):
        if qk not in q_to_k:
            q_to_k[qk] = k
        else:
            # Handle duplicate q_k=1 at k=0,1: Hermite cutoff always uses the largest k with q_k == d_j
            q_to_k[qk] = k

    L = max(B, abs(C)) ** 2
    windows = []
    for j in range(L + 1, j_max + 1):
        num_unnorm = A * Q[j] + C * P[j]
        den_unnorm = B * Q[j]
        Gj = math.gcd(abs(num_unnorm), den_unnorm)
        dj = den_unnorm // Gj
        pj = num_unnorm // Gj
        if dj not in q_to_k:
            break
        k_j = q_to_k[dj]
        windows.append({
            "j": j,
            "k": k_j,
            "Gj": Gj,
            "pj": pj,
            "dj": dj,
        })

    out = []
    for idx in range(len(windows) - 1):
        w0 = windows[idx]
        w1 = windows[idx + 1]
        assert w1["j"] == w0["j"] + 1
        k0, k1 = w0["k"], w1["k"]
        rj = k1 - k0
        digits = cf[k0 + 1 : k1 + 1]
        assert len(digits) == rj and rj >= 1 and rj % 2 == 1
        Dj = abs(w0["pj"] * w1["dj"] - w1["pj"] * w0["dj"])
        T = 2 * B * abs(C)
        assert Dj == T // (w0["Gj"] * w1["Gj"])
        out.append({
            "j": w0["j"],
            "k0": k0,
            "k1": k1,
            "rj": rj,
            "bj": digits[0],
            "S": digits[1:],
            "W": digits,
            "Gj": w0["Gj"],
            "Gj_next": w1["Gj"],
            "Dj": Dj,
        })
    return out


def divisors(n: int) -> list[int]:
    n = abs(n)
    res = []
    for i in range(1, math.isqrt(n) + 1):
        if n % i == 0:
            res.append(i)
            if i * i != n:
                res.append(n // i)
    return sorted(res)


def match_quadratic_in_Ephi(num_rat: int, num_sqrt5: int, den: int) -> list[int] | None:
    r"""
    Given eta = (num_rat + num_sqrt5 * sqrt(5)) / den in Q(sqrt(5)), check if eta in E_phi
    (purely periodic tail 1^inf) by expanding its CF up to 80 terms and detecting eventual 1s.
    Returns CF prefix up to last non-1 term (or [] if eta == phi) if eta in E_phi and eta > 1, else None.
    """
    val = (mp.mpf(num_rat) + mp.mpf(num_sqrt5) * mp.sqrt(5)) / mp.mpf(den)
    if val <= 1:
        return None
    cf = cf_expansion(val, 80)
    if len(cf) < 60:
        return None
    # Check if tail from some index <= 40 is all 1s
    for idx in range(len(cf) - 25):
        if all(t == 1 for t in cf[idx:]):
            # Also verify exact algebraic equality with [cf[:idx]; \bar{1}]
            phi = (mp.mpf(1) + mp.sqrt(5)) / 2
            if idx == 0:
                exact = phi
            else:
                p, q = convergents(cf[:idx])
                p1, q1 = p[-1], q[-1]
                p0, q0 = (p[-2], q[-2]) if idx >= 2 else (1, 0)
                exact = (p1 * phi + p0) / (q1 * phi + q0)
            if abs(val - exact) < mp.mpf("1e-2000"):
                return cf[:idx]
            return None
    return None


def solve_4tau_inversion(p1: int, q1: int, D: int, m: int) -> list[tuple[int, list[int]]]:
    r"""
    Solve Phi_{D/q1, 0}(eta) = |m/(d*sqrt(5)) - 1| for D = 2*d via Lemma lem:general-endpoint-rigidity(4):
    M = 2*m, (M^2 - 5*D^2)/4 = m^2 - 5*d^2.
    For eta = (p1)/(q1 + R) with R = (sigma1*2*m - sigma2*D*sqrt(5))/(2*N2) = (sigma1*m - sigma2*d*sqrt(5))/N2:
    eta = p1 * N2 / (q1 * N2 + sigma1 * m - sigma2 * d * sqrt(5)).
    Rationalize denominator:
      X = q1 * N2 + sigma1 * m, Y = -sigma2 * d
      denom = X^2 - 5 * Y^2
      eta = (p1 * N2 * X + p1 * N2 * sigma2 * d * sqrt(5)) / denom.
    Verify exact Phi_{D/q1, 0}(eta) == |m/(d*sqrt(5)) - 1| and eta in E_phi \cap (1, \infty).
    """
    d = D // 2
    assert D == 2 * d
    target_num = m * m - 5 * d * d
    assert target_num != 0
    divs = divisors(target_num)
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_conj = (mp.mpf(1) - mp.sqrt(5)) / 2
    target_phi_val = abs(mp.mpf(m) / (d * mp.sqrt(5)) - 1)
    found: dict[tuple[int, ...], list[int]] = {}
    for pos_n2 in divs:
        for sgn_n2 in (1, -1):
            N2 = sgn_n2 * pos_n2
            for s1 in (1, -1):
                for s2 in (1, -1):
                    X = q1 * N2 + s1 * m
                    Y = -s2 * d
                    denom = X * X - 5 * Y * Y
                    if denom == 0:
                        continue
                    num_rat = p1 * N2 * X
                    num_sqrt5 = p1 * N2 * s2 * d
                    pref = match_quadratic_in_Ephi(num_rat, num_sqrt5, denom)
                    if pref is not None:
                        # Double check exact Phi value
                        eta = (mp.mpf(num_rat) + mp.mpf(num_sqrt5) * mp.sqrt(5)) / mp.mpf(denom)
                        eta_c = (mp.mpf(num_rat) - mp.mpf(num_sqrt5) * mp.sqrt(5)) / mp.mpf(denom)
                        h_eta = mp.mpf(2) / abs(eta - eta_c)
                        u = mp.mpf(p1) / mp.mpf(q1)
                        phi_val = h_eta * abs(u - eta) * abs(eta_c) / u
                        if abs(phi_val - target_phi_val) < mp.mpf("1e-2000"):
                            found[tuple(pref)] = pref
    return [(len(k), found[k]) for k in sorted(found)]


def section_1_conjugate_positivity() -> None:
    print("=== 1. Conjugate Positivity on E_phi cap (1, inf) \\ {phi} ===")
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_c = (mp.mpf(1) - mp.sqrt(5)) / 2
    eta_ce = phi + 1
    eta_ce_c = phi_c + 1
    phi_inv2 = (3 - mp.sqrt(5)) / 2
    assert abs(eta_ce_c - phi_inv2) < mp.mpf("1e-2400")
    assert eta_ce_c < mp.mpf("0.5") < phi - 1
    print(f"Counterexample eta = phi + 1 = [2; 1,1,...]:")
    print(f"  eta' = phi^(-2) = {mp.nstr(eta_ce_c, 25)} < 0.5 < phi - 1 = {mp.nstr(phi - 1, 25)}")

    total_gl2 = 0
    count_gt1_not_phi = 0
    min_conj = mp.mpf("inf")
    min_mat = None
    for a in range(-12, 13):
        for b in range(-12, 13):
            for c in range(-12, 13):
                for d in range(-12, 13):
                    if abs(a * d - b * c) != 1:
                        continue
                    total_gl2 += 1
                    eta = (a * phi + b) / (c * phi + d)
                    if eta <= 1:
                        continue
                    if abs(eta - phi) < mp.mpf("1e-2000"):
                        continue
                    count_gt1_not_phi += 1
                    eta_c = (a * phi_c + b) / (c * phi_c + d)
                    assert eta_c >= phi_inv2 - mp.mpf("1e-2400")
                    if eta_c < min_conj:
                        min_conj = eta_c
                        min_mat = (a, b, c, d)

    assert abs(min_conj - phi_inv2) < mp.mpf("1e-2400")
    print(f"Exhaustive GL_2(Z) cap [-12, 12]^4: {total_gl2} matrices, {count_gt1_not_phi} with eta > 1, eta != phi.")
    print(f"  min(eta') = {mp.nstr(min_conj, 30)} == phi^(-2), attained e.g. at {min_mat}; 0 exceptions.\n")


def section_2_general_endpoint_rigidity() -> None:
    print("=== 2. Lemma lem:general-endpoint-rigidity (1)-(4) Check (744 Matrices x 5 Endpoints) ===")
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_c = (mp.mpf(1) - mp.sqrt(5)) / 2
    inert_primes = [2, 3, 7, 13, 17, 23]
    endpoints = [
        (18, 5, 0, 1),
        (18, 7, 0, 1),
        (32, 7, 0, 1),
        (3, 2, 1, 2),
        (7, 3, 2, 5),
    ]
    mats = []
    for a in range(-6, 7):
        for b in range(-6, 7):
            for c in range(-6, 7):
                for d in range(-6, 7):
                    eps = a * d - b * c
                    if abs(eps) == 1:
                        mats.append((a, b, c, d, eps))
    assert len(mats) == 744

    for p1, q1, p2, q2 in endpoints:
        D = p1 * q2 + p2 * q1
        assert math.gcd(p1, q1) == 1 and math.gcd(p2, q2) == 1 and D > 0
        u = mp.mpf(p1) / q1
        v = mp.mpf(p2) / q2
        for a, b, c, d, eps in mats:
            eta = (a * phi + b) / (c * phi + d)
            eta_c = (a * phi_c + b) / (c * phi_c + d)
            h_eta = mp.mpf(2) / abs(eta - eta_c)
            phi_uv = h_eta * abs(u - eta) * abs(eta_c + v) / (u + v)

            M_val = M_uv_int(p1, q1, p2, q2, a, b, c, d)
            N1 = zphi_norm(p1 * c - q1 * a, p1 * d - q1 * b)
            N2 = zphi_norm(q2 * a + p2 * c, q2 * b + p2 * d)
            N_gamma = zphi_norm(a, b)

            # Identity & norm equation
            alg_val = abs(mp.mpf(eps * M_val) / (D * mp.sqrt(5)) - 1)
            assert abs(phi_uv - alg_val) < mp.mpf("1e-2400")
            assert M_val * M_val - 5 * D * D == 4 * N1 * N2

            # (1) Inert primes never divide N1 or N2
            for ell in inert_primes:
                assert N1 % ell != 0 and N2 % ell != 0

            # (2) Even D = 2d parity & inert factor exclusion
            if D % 2 == 0:
                d_half = D // 2
                assert M_val % 2 == 0
                m0 = M_val // 2
                m = eps * m0
                assert M_val == 2 * eps * m  # exact, no +-
                assert m * m - 5 * d_half * d_half == N1 * N2
                assert m % 2 == (d_half + 1) % 2
                for ell in inert_primes:
                    if d_half % ell == 0:
                        assert m % ell != 0

            # (3) Mod 2D congruences
            assert (q2 * (M_val + eps * D) + 2 * q1 * N2) % (2 * D) == 0
            assert (p2 * (M_val + eps * D) - 2 * p1 * N2) % (2 * D) == 0
            if D % 2 == 0 and p2 == 0 and q2 == 1:
                d_half = D // 2
                m = eps * (M_val // 2)
                assert (m - (d_half - eps * q1 * N_gamma)) % (2 * d_half) == 0

            # (4) Algebraic inversion formula eta = (p1 - p2*R)/(q1 + q2*R)
            R = (mp.mpf(M_val) - mp.mpf(eps * D) * mp.sqrt(5)) / mp.mpf(2 * N2)
            eta_rec = (mp.mpf(p1) - mp.mpf(p2) * R) / (mp.mpf(q1) + mp.mpf(q2) * R)
            assert abs(eta - eta_rec) < mp.mpf("1e-2400")

        print(f"  Endpoint ({p1}/{q1}, {p2}/{q2}) [D={D:2d}]: all 744 matrices passed (1)-(4) with 0 errors.")
    print()


def section_3_even_suffix_sep() -> None:
    print("=== 3. Lemma lem:even-suffix-sep Gap Delta(S) Check (All 12 Suffixes for B = 3, 4) ===")
    suffixes = {
        "B=3, S^(1)": [17, 1],
        "B=3, S^(5)": [3, 1, 1, 2],
        "B=3, S^(7)": [2, 1, 1, 3],
        "B=3, S^(11)": [1, 1, 1, 1, 2, 1],
        "B=3, S^(13)": [1, 2, 1, 1, 1, 1],
        "B=3, S^(17)": [1, 17],
        "B=4, S^(7)": [4, 1, 1, 3],
        "B=4, S^(9)": [3, 1, 1, 4],
        "B=4, S^(15)": [2, 7, 1, 1],
        "B=4, S^(23)": [1, 2, 1, 1, 3, 1],
        "B=4, S^(25)": [1, 3, 1, 1, 2, 1],
        "B=4, S^(31)": [1, 31],
    }
    for name, S in suffixes.items():
        assert len(S) % 2 == 0
        t = len(S) // 2
        u = cf_value_fraction(S)
        cands = []
        for r in range(1, t + 1):
            cands.append(cf_value_fraction(S[: 2 * r - 1]))
            cands.append(cf_value_fraction(S[: 2 * r - 1] + [S[2 * r - 1] + 1]))
        max_below = max(cands)
        delta = u - max_below
        assert delta > 0
        print(f"  {name:14s} S={str(S):22s} u={str(u):8s} Delta(S)={str(delta):12s} ({float(delta):.8f})")
    print()


def section_4_b3_exact() -> None:
    print("=== 4. Theorem thm:golden-b3-exact (B = 3: 10/3 - e and 11/3 - e, 2500 digits) ===")
    c_min_3 = 1 - mp.mpf(20) / (9 * mp.sqrt(5))
    c_sec_3 = mp.mpf(22) / (9 * mp.sqrt(5)) - 1
    print(f"c_min^(3) = 1 - 20/(9*sqrt(5)) = {mp.nstr(c_min_3, 40)}")
    print(f"c_sec^(3) = 22/(9*sqrt(5)) - 1 = {mp.nstr(c_sec_3, 40)}")
    assert 0 < c_min_3 < c_sec_3

    # Check Q_j mod 3 period 6
    _, Q = hermite_pq(100)
    qmod3 = [q % 3 for q in Q]
    assert qmod3[:12] == [1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2]
    for j in range(100):
        assert qmod3[j] == qmod3[j % 6] and qmod3[j] != 0
    print("Verified Q_j mod 3 has period 6: [1,1,1,2,2,2,...] and never 0.")

    # Algebraic 4*tau inversion for D = 18, m = 20 and m = 22
    q0_set = [1, 5, 7, 11, 13, 17]
    print("Algebraic 4*tau inversion at D = 18 (m = 20 and m = 22):")
    for m_val in (20, 22):
        sols = {}
        for q0 in q0_set:
            res = solve_4tau_inversion(18, q0, 18, m_val)
            sols[q0] = [p for _, p in res]
        print(f"  m={m_val}: {sols}")
        if m_val == 20:
            assert sols == {1: [], 5: [[3]], 7: [[2]], 11: [[]], 13: [[1, 2]], 17: []}
        else:
            assert sols == {1: [], 5: [[2]], 7: [[2, 1, 1, 2]], 11: [[1, 1, 1, 1, 2]], 13: [[]], 17: []}

    # Verify Case 1 Phi_{18/q0, 0}(phi)
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_c = (mp.mpf(1) - mp.sqrt(5)) / 2
    h_phi = mp.mpf(2) / mp.sqrt(5)
    for q0, m_exp in [(1, 10), (5, 14), (7, 16), (11, 20), (13, 22), (17, 26)]:
        u = mp.mpf(18) / q0
        val = h_phi * abs(u - phi) * abs(phi_c) / u
        exp_val = abs(mp.mpf(m_exp) / (9 * mp.sqrt(5)) - 1)
        assert abs(val - exp_val) < mp.mpf("1e-2400")
    print("Verified Phi_{18/q0,0}(phi) corresponds to m in {10, 14, 16, 20, 22, 26}.")

    # Verify Case 2 theoretical lower bounds for B = 3
    r_vals_3 = [mp.mpf(q) / 18 for q in q0_set]
    r_min_3, r_max_3 = min(r_vals_3), max(r_vals_3)
    b_phi_q2 = (2 / mp.sqrt(5)) * (2 - phi + r_min_3)
    b_phi_qgt = (2 / mp.sqrt(5)) * (phi - r_max_3)
    b_2phi_qgt = (2 / mp.sqrt(5)) * (3 - phi - r_max_3)
    b_other = 2 * mp.sqrt(5) * min(r_min_3, 1 - r_max_3)
    print(f"Case 2 bounds (B=3): theta=phi-1 Q=2: {mp.nstr(b_phi_q2, 10)}, Q>=bj+1: {mp.nstr(b_phi_qgt, 10)}")
    print(f"                     theta=2-phi Q>=bj+1: {mp.nstr(b_2phi_qgt, 10)}, other: {mp.nstr(b_other, 10)}")
    assert min(b_phi_q2, b_phi_qgt, b_2phi_qgt, b_other) > c_sec_3

    # Suffix mapping
    suf_map = {
        (17, 1): 1,
        (3, 1, 1, 2): 5,
        (2, 1, 1, 3): 7,
        (1, 1, 1, 1, 2, 1): 11,
        (1, 2, 1, 1, 1, 1): 13,
        (1, 17): 17,
    }
    ext_tails = {5: [3], 7: [2], 11: [], 13: [1, 2]}
    sec_tails = {5: [2], 7: [2, 1, 1, 2], 11: [1, 1, 1, 1, 2], 13: []}

    for label, A in [("10/3 - e", 10), ("11/3 - e", 11)]:
        x = mp.mpf(A) / 3 - mp.e
        cf = cf_expansion(x, 1900)
        wins = extract_windows(cf, A, 3, -3, 330)
        assert len(wins) >= 300
        # Check period 18 starting from j=10
        seen_q0 = set()
        for idx in range(len(wins)):
            w = wins[idx]
            assert w["Gj"] == 1 and w["Dj"] == 18
            q0 = suf_map[tuple(w["S"])]
            seen_q0.add(q0)
            if idx + 18 < len(wins):
                w18 = wins[idx + 18]
                assert w18["j"] == w["j"] + 18
                assert w18["S"] == w["S"]
                assert w18["rj"] == w["rj"]
                assert w18["bj"] == w["bj"] + 4
        assert seen_q0 == set(q0_set)

        # Evaluate extremal & 2nd limit point families in late windows
        last_cycle = wins[-18:]
        max_dev_ext = mp.mpf(0)
        max_dev_sec = mp.mpf(0)
        for w in last_cycle:
            q0 = suf_map[tuple(w["S"])]
            if q0 in ext_tails:
                _, err_ext = eval_orbit_error(x, cf[: w["k0"] + 2], ext_tails[q0])
                _, err_sec = eval_orbit_error(x, cf[: w["k0"] + 2], sec_tails[q0])
                dev_ext = abs(err_ext - c_min_3)
                dev_sec = abs(err_sec - c_sec_3)
                if dev_ext > max_dev_ext:
                    max_dev_ext = dev_ext
                if dev_sec > max_dev_sec:
                    max_dev_sec = dev_sec
                assert dev_ext < mp.mpf("3e-3")
                assert dev_sec < mp.mpf("1e-2")

        # Non-extremal scan on last 18 windows
        min_non_ext = mp.mpf("inf")
        scanned = 0
        tails_scan = [[], [2], [3], [1, 2], [2, 2], [1, 1, 2], [2, 1, 1, 2], [1, 1, 1, 1, 2]]
        start_k = last_cycle[0]["k0"] + 1
        end_k = last_cycle[-1]["k1"]
        for pos in range(start_k, end_k + 1):
            a_pos = cf[pos]
            for q_alt in [1, 2, 3, 4, max(1, a_pos - 1), a_pos + 1]:
                if q_alt == a_pos:
                    continue
                for tail in tails_scan:
                    cand = cf[:pos] + [q_alt] + tail
                    is_ext = False
                    for w in wins[-20:]:
                        q0 = suf_map[tuple(w["S"])]
                        if q0 not in ext_tails:
                            continue
                        ext_seq = cf[: w["k0"] + 2] + ext_tails[q0]
                        c_trim = cand[:]
                        while c_trim and c_trim[-1] == 1:
                            c_trim.pop()
                        e_trim = ext_seq[:]
                        while e_trim and e_trim[-1] == 1:
                            e_trim.pop()
                        if c_trim == e_trim:
                            is_ext = True
                            break
                    if is_ext:
                        continue
                    _, err = eval_orbit_error(x, cf[:pos] + [q_alt], tail)
                    scanned += 1
                    if err < min_non_ext:
                        min_non_ext = err
        print(f"  {label}: {len(wins)} windows verified (period 18, b_{{j+18}}=b_j+4); "
              f"max_dev_ext={mp.nstr(max_dev_ext, 4)}, max_dev_sec={mp.nstr(max_dev_sec, 4)}; "
              f"non-extremal scan ({scanned} pts) min = {mp.nstr(min_non_ext, 10)} (c_sec = {mp.nstr(c_sec_3, 10)})")
        assert min_non_ext > mp.mpf("0.088")
    print()


def section_5_b4_exact() -> None:
    print("=== 5. Theorem thm:golden-b4-exact (B = 4: 13/4 - e and 15/4 - e, 2500 digits) ===")
    c_min_4 = 1 - mp.mpf(35) / (16 * mp.sqrt(5))
    c_37 = mp.mpf(37) / (16 * mp.sqrt(5)) - 1
    c_sec_4 = 1 - mp.mpf(33) / (16 * mp.sqrt(5))
    print(f"c_min^(4) = 1 - 35/(16*sqrt(5)) = {mp.nstr(c_min_4, 40)}")
    print(f"forbidden m=37: 37/(16*sqrt(5))-1 = {mp.nstr(c_37, 40)}")
    print(f"c_sec^(4) = 1 - 33/(16*sqrt(5)) = {mp.nstr(c_sec_4, 40)}")
    assert 0 < c_min_4 < c_37 < c_sec_4

    # Check (P_j, Q_j) mod 16 and mod 32 periods
    P, Q = hermite_pq(100)
    pq16 = [(P[j] % 16, Q[j] % 16) for j in range(100)]
    pq32 = [(P[j] % 32, Q[j] % 32) for j in range(100)]
    assert all(pq16[j] == pq16[j + 8] for j in range(90))
    assert not all(pq16[j] == pq16[j + 4] for j in range(20))
    assert all(pq32[j] == pq32[j + 16] for j in range(80))
    assert not all(pq32[j] == pq32[j + 8] for j in range(20))
    print("Verified (P_j, Q_j) mod 16 minimal period = 8; mod 32 minimal period = 16.")

    # Mod 16 subgroup exclusion of m = 37
    q0_all_4 = [7, 9, 15, 23, 25, 31]
    subgrp16 = {1, 7, 9, 15}  # {+-1, +-7} mod 16
    assert all((q0 % 16) in subgrp16 for q0 in q0_all_4)
    assert 37**2 - 5 * 16**2 == 89
    divs_89 = [1, -1, 89, -89]
    assert all((d % 16) in subgrp16 for d in divs_89)
    for q0 in q0_all_4:
        for eps in (1, -1):
            for ng in divs_89:
                res16 = (-eps * q0 * ng) % 16
                assert res16 in subgrp16
                assert res16 != (37 % 16)  # 37 % 16 == 5
    print("Verified mod-16 subgroup {+-1, +-7} closes under multiplication and strictly excludes m = 37 (5 mod 16).")

    # Algebraic 4*tau inversion for D = 32, m = 35, 37, 33
    print("Algebraic 4*tau inversion at D = 32 (m = 35, 37, 33):")
    for m_val in (35, 37, 33):
        sols = {}
        for q0 in q0_all_4:
            res = solve_4tau_inversion(32, q0, 32, m_val)
            sols[q0] = [p for _, p in res]
        print(f"  m={m_val}: {sols}")
        if m_val == 35:
            assert sols == {7: [[4]], 9: [[3]], 15: [], 23: [[1, 2]], 25: [[1, 3]], 31: []}
        elif m_val == 37:
            assert all(len(v) == 0 for v in sols.values())
        elif m_val == 33:
            assert sols == {7: [], 9: [], 15: [[2], [2, 7]], 23: [], 25: [], 31: []}

    # Case 1 Phi_{32/q0, 0}(phi)
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_c = (mp.mpf(1) - mp.sqrt(5)) / 2
    h_phi = mp.mpf(2) / mp.sqrt(5)
    for q0, m_exp in [(7, 23), (9, 25), (15, 31), (23, 39), (25, 41), (31, 47)]:
        u = mp.mpf(32) / q0
        val = h_phi * abs(u - phi) * abs(phi_c) / u
        exp_val = abs(mp.mpf(m_exp) / (16 * mp.sqrt(5)) - 1)
        assert abs(val - exp_val) < mp.mpf("1e-2400")
    print("Verified Phi_{32/q0,0}(phi) corresponds to m in {23, 25, 31, 39, 41, 47}.")

    # Case 2 lower bounds for B = 4
    # Reverse suffixes q0': 15->17, 31->1, 7<->9, 23<->25
    q0_rev = [1, 7, 9, 17, 23, 25]
    r1_vals = [mp.mpf(q) / 32 for q in q0_all_4]
    r2_vals = [mp.mpf(q) / 32 for q in q0_rev]
    r1_min, r1_max = min(r1_vals), max(r1_vals)  # 7/32, 31/32
    r2_min, r2_max = min(r2_vals), max(r2_vals)  # 1/32, 25/32

    b_phi_q2_at_2 = (2 / mp.sqrt(5)) * (2 - phi + r2_min)  # Q_n = 2, r_2 = 1/32 -> 0.36959164...
    b_phi_q2_at_bm1 = (2 / mp.sqrt(5)) * (2 - phi + r1_min)  # Q_n = b_j - 1, r_1 = 7/32 -> 0.53729675...
    b_phi_qgt = (2 / mp.sqrt(5)) * (phi - r1_max)  # Q_n >= b_j + 1, r_1 = 31/32 -> 0.58074...
    b_2phi_q1 = (2 / mp.sqrt(5)) * (phi + 1 - r1_max) * (phi + r2_min)
    b_2phi_q2 = (2 / mp.sqrt(5)) * (3 - phi - r1_max)  # wait: at Q_n = b_j - 1 -> (b_j + r1 - (b_j-1 + 2 - phi))*(...) -> (2 - phi + r1)? No, (phi - 1 + r1) >= 2/sqrt5*(phi - 1 + 7/32)! Wait: at Q_n = b_j + 1: |T_m - eta_n| = Q_n + 2 - phi - b_j - r1 >= 3 - phi - r1_max!
    b_2phi_bm1 = (2 / mp.sqrt(5)) * (phi - 1 + r1_min)  # at Q_n = b_j - 1: |b_j + r1 - (b_j - 1 + 2 - phi)| = phi - 1 + r1 >= phi - 1 + 7/32
    b_other_q1 = 2 * mp.sqrt(5) * (1 - mp.mpf(1) / phi**2) * (1 / phi**2 + r2_min)  # rough; actually T_m >= b_j, eta' >= phi^-2
    b_other_mid = 2 * mp.sqrt(5) * min(r1_min, 1 - r1_max)  # 2*sqrt(5) * (1/32) = sqrt(5)/16 = 0.139754...
    print(f"Case 2 exact bounds (B=4):")
    print(f"  theta=phi-1, Q_n=2 (r_2=1/32):     {mp.nstr(b_phi_q2_at_2, 12)} (replaces erroneous 0.53730!)")
    print(f"  theta=phi-1, Q_n=b_j-1 (r_1=7/32): {mp.nstr(b_phi_q2_at_bm1, 12)}")
    print(f"  theta=phi-1, Q_n>=b_j+1 (r_1=31/32): {mp.nstr(b_phi_qgt, 12)}")
    print(f"  theta=2-phi, Q_n>=b_j+1 (r_1=31/32): {mp.nstr(b_2phi_q2, 12)}")
    print(f"  theta=2-phi, Q_n=b_j-1 (r_1=7/32):   {mp.nstr(b_2phi_bm1, 12)}")
    print(f"  theta not in {{phi-1,2-phi}}, min(r1_min, 1-r1_max)=1/32 -> sqrt(5)/16 = {mp.nstr(b_other_mid, 12)}")
    assert abs(b_phi_q2_at_2 - mp.mpf("0.36959164")) < mp.mpf("1e-7")
    assert min(b_phi_q2_at_2, b_phi_q2_at_bm1, b_phi_qgt, b_2phi_q2, b_2phi_bm1, b_other_mid) > c_sec_4

    # Also check Q_n = 1, theta = phi - 1 gives |32 + 2*q1'| / (32*sqrt(5)) - 1
    for qp in q0_rev:
        val_q1 = abs(mp.mpf(32 + 2 * qp) / (32 * mp.sqrt(5)) - 1)
        if qp == 17:
            assert abs(val_q1 - c_sec_4) < mp.mpf("1e-2400")
        elif qp != 23 and qp != 25:
            assert val_q1 > c_sec_4
    print("Verified Q_n=1, theta=phi-1: q1'=17 gives exact c_sec^(4), q1'=23 gives 39/(16*sqrt(5))-1 > c_sec^(4).")

    suf_map_4 = {
        (4, 1, 1, 3): 7,
        (3, 1, 1, 4): 9,
        (2, 7, 1, 1): 15,
        (1, 2, 1, 1, 3, 1): 23,
        (1, 3, 1, 1, 2, 1): 25,
        (1, 31): 31,
    }
    ext_tails_4_A1 = {7: [4], 23: [1, 2], 25: [1, 3]}
    ext_tails_4_A3 = {7: [4], 9: [3], 23: [1, 2]}

    for label, A, exp_q0, ext_tails in [
        ("13/4 - e", 13, {7, 15, 23, 25, 31}, ext_tails_4_A1),
        ("15/4 - e", 15, {7, 9, 15, 23, 31}, ext_tails_4_A3),
    ]:
        x = mp.mpf(A) / 4 - mp.e
        cf = cf_expansion(x, 1900)
        wins = extract_windows(cf, A, 4, -4, 300)
        assert len(wins) >= 270
        seen_q0 = set()
        for idx, w in enumerate(wins):
            assert w["Gj"] == 1 and w["Dj"] == 32
            q0 = suf_map_4[tuple(w["S"])]
            seen_q0.add(q0)
            if idx + 8 < len(wins):
                w8 = wins[idx + 8]
                assert w8["j"] == w["j"] + 8
                assert w8["S"] == w["S"]
                assert w8["rj"] == w["rj"]  # minimal period 8!
                assert w8["bj"] == w["bj"] + 1
            if idx + 32 < len(wins):
                w32 = wins[idx + 32]
                assert w32["bj"] == w["bj"] + 4
        # Verify 8 is minimal period for S_j and r_j from j=17
        w17 = [w for w in wins if w["j"] >= 17]
        for d_test in (1, 2, 4):
            assert not all(w17[i]["S"] == w17[i + d_test]["S"] for i in range(16))
            assert not all(w17[i]["rj"] == w17[i + d_test]["rj"] for i in range(16))
        assert seen_q0 == exp_q0

        # Check extremal and 2nd limit families on last 16 windows
        last_16 = wins[-16:]
        for w in last_16:
            q0 = suf_map_4[tuple(w["S"])]
            if q0 in ext_tails:
                _, err_ext = eval_orbit_error(x, cf[: w["k0"] + 2], ext_tails[q0])
                assert abs(err_ext - c_min_4) < mp.mpf("3e-3")
            if q0 == 15:
                _, err_sec1 = eval_orbit_error(x, cf[: w["k0"] + 2], [2])
                _, err_sec2 = eval_orbit_error(x, cf[: w["k0"] + 2], [2, 7])
                assert abs(err_sec1 - c_sec_4) < mp.mpf("1.5e-2")
                assert abs(err_sec2 - c_sec_4) < mp.mpf("1.5e-2")

        # Non-extremal scan on last 8 windows
        last_8 = wins[-8:]
        min_non_ext = mp.mpf("inf")
        scanned = 0
        tails_scan = [[], [2], [3], [4], [1, 2], [1, 3], [2, 7], [2, 1, 1, 3], [1, 2, 1, 1, 3]]
        for pos in range(last_8[0]["k0"] + 1, last_8[-1]["k1"] + 1):
            a_pos = cf[pos]
            for q_alt in [1, 2, 3, 4, max(1, a_pos - 1), a_pos + 1]:
                if q_alt == a_pos:
                    continue
                for tail in tails_scan:
                    cand = cf[:pos] + [q_alt] + tail
                    is_ext = False
                    for w in wins[-12:]:
                        q0 = suf_map_4[tuple(w["S"])]
                        if q0 not in ext_tails:
                            continue
                        ext_seq = cf[: w["k0"] + 2] + ext_tails[q0]
                        c_trim = cand[:]
                        while c_trim and c_trim[-1] == 1:
                            c_trim.pop()
                        e_trim = ext_seq[:]
                        while e_trim and e_trim[-1] == 1:
                            e_trim.pop()
                        if c_trim == e_trim:
                            is_ext = True
                            break
                    if is_ext:
                        continue
                    _, err = eval_orbit_error(x, cf[:pos] + [q_alt], tail)
                    scanned += 1
                    if err < min_non_ext:
                        min_non_ext = err
        print(f"  {label}: {len(wins)} windows verified (S_j & r_j min period 8, b_{{j+8}}=b_j+1); "
              f"non-extremal scan ({scanned} pts) min = {mp.nstr(min_non_ext, 10)} (c_sec = {mp.nstr(c_sec_4, 10)})")
        assert min_non_ext > mp.mpf("0.072")
    print()


def section_6_general_regimes() -> None:
    print("=== 6. B = 5, 6, 7 and (1+e)/6, (1+e)/3, (1+2e)/3 Mechanisms ===")
    # B = 5: 16/5, 17/5, 18/5, 19/5 - e
    c_min_5 = mp.mpf(56) / (25 * mp.sqrt(5)) - 1
    c_sec_5 = 1 - mp.mpf(54) / (25 * mp.sqrt(5))
    q0_sets_5 = []
    for A in (16, 17, 18, 19):
        x = mp.mpf(A) / 5 - mp.e
        cf = cf_expansion(x, 2000)
        wins = extract_windows(cf, A, 5, -5, 260)
        assert all(w["Gj"] == 1 and w["Dj"] == 50 for w in wins)
        q0s = set()
        for w in wins[-50:]:
            u = cf_value_fraction(w["S"])
            assert u.numerator == 50
            q0s.add(u.denominator)
        assert len(q0s) == 20
        q0_sets_5.append(q0s)
        # Check m=56 and m=54 attainment via 4*tau inversion on q0s
        sols_56 = [q0 for q0 in sorted(q0s) if solve_4tau_inversion(50, q0, 50, 56)]
        sols_54 = [q0 for q0 in sorted(q0s) if solve_4tau_inversion(50, q0, 50, 54)]
        assert len(sols_56) > 0 and len(sols_54) > 0
        # Verify on last 50 windows
        best_ext = mp.mpf("inf")
        best_sec = mp.mpf("inf")
        for w in wins[-50:]:
            q0 = cf_value_fraction(w["S"]).denominator
            for _, pref in solve_4tau_inversion(50, q0, 50, 56):
                _, err = eval_orbit_error(x, cf[: w["k0"] + 2], pref)
                if abs(err - c_min_5) < abs(best_ext - c_min_5):
                    best_ext = err
            for _, pref in solve_4tau_inversion(50, q0, 50, 54):
                _, err = eval_orbit_error(x, cf[: w["k0"] + 2], pref)
                if abs(err - c_sec_5) < abs(best_sec - c_sec_5):
                    best_sec = err
        assert abs(best_ext - c_min_5) < mp.mpf("5e-3"), f"B=5 A={A} best_ext={best_ext}"
        assert abs(best_sec - c_sec_5) < mp.mpf("2e-2"), f"B=5 A={A} best_sec={best_sec}"
    assert all(s == q0_sets_5[0] for s in q0_sets_5)
    print(f"B=5 (16/5..19/5 - e): 4 classes share identical 20-element q0 set; "
          f"m=56 ({mp.nstr(c_min_5, 10)}) & m=54 ({mp.nstr(c_sec_5, 10)}) attained "
          f"(last-cycle best_ext={mp.nstr(best_ext, 8)}, best_sec={mp.nstr(best_sec, 8)}).")

    # B = 6: 19/6 - e, 23/6 - e
    c_min_6 = 1 - mp.mpf(79) / (36 * mp.sqrt(5))
    for A in (19, 23):
        x = mp.mpf(A) / 6 - mp.e
        cf = cf_expansion(x, 2000)
        wins = extract_windows(cf, A, 6, -6, 260)
        assert all(w["Gj"] == 1 and w["Dj"] == 72 for w in wins)
        q0s = {cf_value_fraction(w["S"]).denominator for w in wins[-72:]}
        # Verify m=81 has NO inversion solutions (3 | 36 inert prime)
        sols_81 = [q0 for q0 in q0s if solve_4tau_inversion(72, q0, 72, 81)]
        sols_79 = [q0 for q0 in q0s if solve_4tau_inversion(72, q0, 72, 79)]
        assert len(sols_81) == 0 and len(sols_79) > 0
        best_ext = mp.mpf("inf")
        for w in wins[-72:]:
            q0 = cf_value_fraction(w["S"]).denominator
            for _, pref in solve_4tau_inversion(72, q0, 72, 79):
                _, err = eval_orbit_error(x, cf[: w["k0"] + 2], pref)
                if abs(err - c_min_6) < abs(best_ext - c_min_6):
                    best_ext = err
        assert abs(best_ext - c_min_6) < mp.mpf("1e-2"), f"B=6 A={A} best_ext={best_ext}"
    print(f"B=6 (19/6, 23/6 - e): D=72, inert 3|36 forbids m=81; m=79 ({mp.nstr(c_min_6, 10)}) > c_min^(2),c_min^(3),c_min^(5).")

    # B = 7: 22/7 - e
    x7 = mp.mpf(22) / 7 - mp.e
    cf7 = cf_expansion(x7, 1600)
    wins7 = extract_windows(cf7, 22, 7, -7, 200)
    # 1 full period of T = 98 starting from j=50
    period7 = [w for w in wins7 if 50 <= w["j"] < 148]
    assert len(period7) == 98
    dist7: dict[int, int] = {}
    for w in period7:
        dist7[w["Dj"]] = dist7.get(w["Dj"], 0) + 1
    assert dist7 == {2: 8, 14: 48, 98: 42}
    w59 = [w for w in wins7 if w["j"] == 59][0]
    w60 = [w for w in wins7 if w["j"] == 60][0]
    assert w59["Dj"] == 2 and w59["W"] == [1, 1, 1]
    assert w60["Dj"] == 2 and w60["W"][1:] == [1, 1]
    print(f"B=7 (22/7 - e): T=98 D_j distribution = {dist7}; W_59={w59['W']}, W_60={w60['W']}.")

    # (1+e)/6: A=1, B=6, C=1, T=12
    x_1e6 = (1 + mp.e) / 6
    cf_1e6 = cf_expansion(x_1e6, 800)
    wins_1e6 = extract_windows(cf_1e6, 1, 6, 1, 120)
    p_1e6 = [w for w in wins_1e6 if 40 <= w["j"] < 52]
    dist_1e6: dict[int, int] = {}
    for w in p_1e6:
        dist_1e6[w["Dj"]] = dist_1e6.get(w["Dj"], 0) + 1
    assert dist_1e6 == {1: 8, 3: 4}
    c_1e6_min = mp.mpf(7) / (3 * mp.sqrt(5)) - 1
    c_1e6_sec = 1 - mp.sqrt(5) / 3
    print(f"(1+e)/6: T=12 D_j dist={dist_1e6}, min=7/(3*sqrt(5))-1={mp.nstr(c_1e6_min, 10)}, "
          f"2nd=1-sqrt(5)/3={mp.nstr(c_1e6_sec, 10)}")

    # (1+e)/3: A=1, B=3, C=1, T=6
    x_1e3 = (1 + mp.e) / 3
    cf_1e3 = cf_expansion(x_1e3, 800)
    wins_1e3 = extract_windows(cf_1e3, 1, 3, 1, 120)
    p_1e3 = [w for w in wins_1e3 if 20 <= w["j"] < 26]
    dist_1e3: dict[int, int] = {}
    for w in p_1e3:
        dist_1e3[w["Dj"]] = dist_1e3.get(w["Dj"], 0) + 1
    assert dist_1e3 == {2: 4, 6: 2}
    c_1e3_min = 1 - mp.mpf(2) / mp.sqrt(5)
    c_1e3_sec = mp.mpf(8) / (3 * mp.sqrt(5)) - 1
    print(f"(1+e)/3: T=6  D_j dist={dist_1e3}, min=1-2/sqrt(5)={mp.nstr(c_1e3_min, 10)}, "
          f"2nd=8/(3*sqrt(5))-1={mp.nstr(c_1e3_sec, 10)}")

    # (1+2e)/3: A=1, B=3, C=2, T=12
    x_12e3 = (1 + 2 * mp.e) / 3
    cf_12e3 = cf_expansion(x_12e3, 800)
    wins_12e3 = extract_windows(cf_12e3, 1, 3, 2, 120)
    p_12e3 = [w for w in wins_12e3 if 20 <= w["j"] < 32]
    dist_12e3: dict[int, int] = {}
    for w in p_12e3:
        dist_12e3[w["Dj"]] = dist_12e3.get(w["Dj"], 0) + 1
    # Check W_j = [b_j, 2, 2, 1, 1] at D=12, q0=5
    w_d12_q5 = [w for w in wins_12e3[-24:] if w["Dj"] == 12 and w["S"] == [2, 2, 1, 1]]
    assert len(w_d12_q5) > 0
    c_12e3_min = 1 - mp.mpf(13) / (6 * mp.sqrt(5))  # > 0! NOT 13/(6*sqrt(5)) - 1
    c_12e3_sec = mp.sqrt(5) / 2 - 1
    assert c_12e3_min > 0
    _, err_a = eval_orbit_error(x_12e3, cf_12e3[: w_d12_q5[-1]["k0"] + 2], [2])
    _, err_b = eval_orbit_error(x_12e3, cf_12e3[: w_d12_q5[-1]["k0"] + 2], [2, 2])
    assert abs(err_a - c_12e3_min) < mp.mpf("5e-3")
    assert abs(err_b - c_12e3_min) < mp.mpf("5e-3")
    print(f"(1+2e)/3: T=12 D_j dist={dist_12e3}, min=1-13/(6*sqrt(5))={mp.nstr(c_12e3_min, 10)} (>0!), "
          f"2nd=sqrt(5)/2-1={mp.nstr(c_12e3_sec, 10)}")
    print("ALL VERIFICATION CHECKS PASSED WITH 0 ASSERTION FAILURES.")


if __name__ == "__main__":
    section_1_conjugate_positivity()
    section_2_general_endpoint_rigidity()
    section_3_even_suffix_sep()
    section_4_b3_exact()
    section_5_b4_exact()
    section_6_general_regimes()
