r"""
High-precision (2500-digit mpmath) verification for Path 2A (Paper 1, Section 8):
Complete Case 1 + Case 2 closure for B=5, B=6, and small-period multi-scale targets.

Sections:
1. Lemma lem:general-case2-criterion:
   - Auxiliary single-digit Case 2 lower bound h(theta)*(1-theta) >= sqrt(5) - 1
     for all theta in E_phi cap (0, 1) \ {phi - 1, 2 - phi} (exhaustive GL_2(Z) cap [-12,12]^4).
   - Exact branch lower-bound formulas validated numerically at large b_j.
2. Theorem thm:golden-b5-exact (B = 5: 16/5 - e, 17/5 - e, 18/5 - e, 19/5 - e):
   - Q_j mod 5 period 10 (5 nmid Q_j), G_j = 1, D_j = 50 for j > 25;
   - Period 50, b_{j+50} = b_j + 4, shared 20-element suffix set (Z/50Z)^x, Delta(S) > 0;
   - Algebraic 4*tau inversion for m = 56, 54, 58, 52;
   - Case 1 + Case 2 closure, convergence checks, and non-extremal scans.
3. Theorem thm:golden-b6-exact (B = 6: 19/6 - e, 23/6 - e):
   - Q_j mod 3 period 6 (3 nmid Q_j), G_j = 1, D_j = 72 for j > 36;
   - Minimal period 18 for (S_j, r_j) with b_{j+18} = b_j + 1 (b_{j+72} = b_j + 4);
   - Shared 12-element suffix set (q_0 mod 24 in {5, 11, 13, 19}, q_0 === +-3 mod 8);
   - Inert 3|36 exclusion of m = 81 and mod-8 congruence exclusion of m = 83;
   - Algebraic 4*tau inversion for m = 81, 79, 83, 77, 85;
   - Case 1 + Case 2 closure, convergence checks, and non-extremal scans.
4. Theorem thm:golden-multiscale-exact:
   - (i) (1+e)/6 (T=12, min period 6, mixed D_j in {1, 3}, single-digit r_j=1 windows);
   - (ii) (1+e)/3 (T=6, mixed D_j in {2, 6}, inert 3|3 exclusion of m=6);
   - (iii) (1+2e)/3 (T=12, min period 6, mixed D_j in {4, 12}, inert 3|6 exclusion of m=15);
   - (iv) 22/7 - e (T=98, three-scale D_j in {2, 14, 98}, all 8 D_j=2 windows,
         m=1..5 check at D=2, inert 7|7 and 7|49 exclusions, Case 1 + Case 2 closure,
         extremal/second-limit convergence, and full-period non-extremal scan).
"""

from __future__ import annotations
from fractions import Fraction
import math
import mpmath as mp

mp.mp.dps = 2500


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
    P = [1, 3]
    Q = [1, 1]
    for j in range(1, n_max):
        P.append((4 * j + 2) * P[j] + P[j - 1])
        Q.append((4 * j + 2) * Q[j] + Q[j - 1])
    return P, Q


def cf_value_fraction(digits: list[int]) -> Fraction:
    if not digits:
        return Fraction(0, 1)
    val = Fraction(digits[-1], 1)
    for d in reversed(digits[:-1]):
        val = d + Fraction(1, 1) / val
    return val


def suffix_gap_delta(S: list[int]) -> Fraction:
    assert len(S) % 2 == 0 and len(S) >= 2
    t = len(S) // 2
    u = cf_value_fraction(S)
    cands = []
    for r in range(1, t + 1):
        cands.append(cf_value_fraction(S[: 2 * r - 1]))
        cands.append(cf_value_fraction(S[: 2 * r - 1] + [S[2 * r - 1] + 1]))
    return u - max(cands)


def eval_orbit_error(x: mp.mpf, prefix: list[int], tail_pre: list[int]) -> tuple[mp.mpf, mp.mpf]:
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_c = (mp.mpf(1) - mp.sqrt(5)) / 2
    full = prefix + tail_pre
    p, q = convergents(full)
    m = len(full)
    if m == 1:
        p1, q1, p0, q0 = p[0], q[0], 1, 0
    else:
        p1, q1, p0, q0 = p[m - 1], q[m - 1], p[m - 2], q[m - 2]
    beta = (p1 * phi + p0) / (q1 * phi + q0)
    beta_c = (p1 * phi_c + p0) / (q1 * phi_c + q0)
    h_beta = mp.mpf(2) / abs(beta - beta_c)
    return h_beta, h_beta * abs(x - beta)


def extract_windows(cf: list[int], A: int, B: int, C: int, j_max: int) -> list[dict]:
    P, Q = hermite_pq(j_max + 2)
    _, q_cf = convergents(cf)
    q_to_k = {qk: k for k, qk in enumerate(q_cf)}
    L = max(B, abs(C)) ** 2
    T = 2 * B * abs(C)
    windows = []
    for j in range(L + 1, j_max + 1):
        num = A * Q[j] + C * P[j]
        den = B * Q[j]
        Gj = math.gcd(abs(num), den)
        dj = den // Gj
        pj = num // Gj
        if dj not in q_to_k:
            break
        windows.append({"j": j, "k": q_to_k[dj], "Gj": Gj, "pj": pj, "dj": dj})
    out = []
    for idx in range(len(windows) - 1):
        w0, w1 = windows[idx], windows[idx + 1]
        assert w1["j"] == w0["j"] + 1
        k0, k1 = w0["k"], w1["k"]
        digits = cf[k0 + 1 : k1 + 1]
        rj = k1 - k0
        assert len(digits) == rj and rj >= 1 and rj % 2 == 1
        Dj = abs(w0["pj"] * w1["dj"] - w1["pj"] * w0["dj"])
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
    val = (mp.mpf(num_rat) + mp.mpf(num_sqrt5) * mp.sqrt(5)) / mp.mpf(den)
    if val <= 1:
        return None
    cf = cf_expansion(val, 80)
    if len(cf) < 60:
        return None
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    for idx in range(len(cf) - 25):
        if all(t == 1 for t in cf[idx:]):
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


def solve_4tau_inversion(p1: int, q1: int, M: int) -> list[list[int]]:
    """Solve Phi_{p1/q1, 0}(eta) = |M/(p1*sqrt(5)) - 1| for eta in E_phi cap (1, inf)."""
    D = p1
    num = M * M - 5 * D * D
    if num == 0 or num % 4 != 0:
        return []
    K = num // 4
    divs = divisors(K)
    u = mp.mpf(p1) / q1
    target = abs(mp.mpf(M) / (D * mp.sqrt(5)) - 1)
    found: dict[tuple[int, ...], list[int]] = {}
    for pos_n2 in divs:
        for sgn in (1, -1):
            N2 = sgn * pos_n2
            for sM in (1, -1):
                for sD in (1, -1):
                    Br = 2 * q1 * N2 + sM * M
                    Bs = -sD * D
                    denom = Br * Br - 5 * Bs * Bs
                    if denom == 0:
                        continue
                    Ar = 2 * p1 * N2
                    num_rat = Ar * Br
                    num_sqrt5 = -Ar * Bs
                    pref = match_quadratic_in_Ephi(num_rat, num_sqrt5, denom)
                    if pref is not None:
                        eta = (mp.mpf(num_rat) + mp.mpf(num_sqrt5) * mp.sqrt(5)) / mp.mpf(denom)
                        eta_c = (mp.mpf(num_rat) - mp.mpf(num_sqrt5) * mp.sqrt(5)) / mp.mpf(denom)
                        h_eta = mp.mpf(2) / abs(eta - eta_c)
                        val = h_eta * abs(u - eta) * abs(eta_c) / u
                        if abs(val - target) < mp.mpf("1e-2000"):
                            found[tuple(pref)] = pref
    return [found[k] for k in sorted(found)]


def trim_ones(seq: list[int]) -> list[int]:
    out = seq[:]
    while out and out[-1] == 1:
        out.pop()
    return out


def verify_case2_bounds(
    name: str,
    win_types: dict[tuple[int, tuple[int, ...]], tuple[Fraction, Fraction]],
    r2_types: set[tuple[int, Fraction]],
    c_sec: mp.mpf,
    excluded_r2_pairs: set[tuple[int, Fraction]],
) -> None:
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    r1_all = [mp.mpf(r1.numerator) / r1.denominator for _, (_, r1) in win_types.items()]
    r1_pos = [mp.mpf(r1.numerator) / r1.denominator for (D, _), (_, r1) in win_types.items() if D > 1]
    r2_all = [mp.mpf(r2.numerator) / r2.denominator for _, r2 in r2_types]
    r1_min, r1_max = min(r1_all), max(r1_all)
    r1_pos_min = min(r1_pos)
    r2_min = min(r2_all)
    has_d1 = any(D == 1 for D, _ in win_types)

    # (a) theta = phi - 1
    q1_min_non_excl = mp.mpf("inf")
    for Dprev, r2 in sorted(r2_types):
        val = abs((mp.mpf(Dprev) + 2 * mp.mpf(r2.numerator)) / (Dprev * mp.sqrt(5)) - 1)
        if (Dprev, r2) not in excluded_r2_pairs:
            if val < q1_min_non_excl:
                q1_min_non_excl = val
    assert q1_min_non_excl >= c_sec - mp.mpf("1e-2400")

    b_a_mid = (2 / mp.sqrt(5)) * (2 - phi + min(r1_min, r2_min))
    b_a_gt = (2 / mp.sqrt(5)) * (phi - r1_max)
    # (b) theta = 2 - phi
    b_b_1 = (2 / mp.sqrt(5)) * (2 + phi + r2_min)
    b_b_mid = (2 / mp.sqrt(5)) * (phi - 1 + r1_min)
    b_b_gt = (2 / mp.sqrt(5)) * (3 - phi - r1_max)
    # (c) theta not in {phi-1, 2-phi}
    b_c_1 = 2 * mp.sqrt(5) * (1 / (phi ** 2) + r2_min)
    b_c_mid = 2 * mp.sqrt(5) * min(r1_pos_min, 1 - r1_max)
    if has_d1:
        b_c_mid = min(b_c_mid, mp.sqrt(5) - 1)

    min_other = min(b_a_mid, b_a_gt, b_b_1, b_b_mid, b_b_gt, b_c_1, b_c_mid)
    assert min_other > c_sec
    print(
        f"  [{name}] Case 2 closure: Q1(non-excl)>={mp.nstr(q1_min_non_excl, 10)}, "
        f"(a)mid={mp.nstr(b_a_mid, 8)}, (a)gt={mp.nstr(b_a_gt, 8)}, "
        f"(b)mid={mp.nstr(b_b_mid, 8)}, (b)gt={mp.nstr(b_b_gt, 8)}, "
        f"(c)1={mp.nstr(b_c_1, 8)}, (c)>=2={mp.nstr(b_c_mid, 8)} > c_sec={mp.nstr(c_sec, 10)}"
    )


def scan_non_extremal(
    cf: list[int],
    x: mp.mpf,
    wins_slice: list[dict],
    ext_seqs_trimmed: list[list[int]],
    tails_scan: list[list[int]],
    threshold: mp.mpf,
    label: str,
) -> None:
    ext_set = {tuple(s) for s in ext_seqs_trimmed}
    min_err = mp.mpf("inf")
    scanned = 0
    start_k = wins_slice[0]["k0"] + 1
    end_k = wins_slice[-1]["k1"]
    for pos in range(start_k, end_k + 1):
        a_pos = cf[pos]
        cands_q = sorted({1, 2, 3, 4, 5, 6, 14, max(1, a_pos - 1), a_pos + 1})
        for q_alt in cands_q:
            if q_alt == a_pos:
                continue
            for tail in tails_scan:
                cand = trim_ones(cf[:pos] + [q_alt] + tail)
                if tuple(cand) in ext_set:
                    continue
                _, err = eval_orbit_error(x, cf[:pos] + [q_alt], tail)
                scanned += 1
                if err < min_err:
                    min_err = err
    assert min_err > threshold, f"{label}: min_err={min_err} <= {threshold}"
    print(f"    non-extremal scan ({scanned} pts): min = {mp.nstr(min_err, 10)} (threshold {mp.nstr(threshold, 8)})")


def section_1_general_case2_criterion() -> None:
    print("=== 1. Lemma lem:general-case2-criterion Auxiliary Bound Check ===")
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_c = (mp.mpf(1) - mp.sqrt(5)) / 2
    target_lb = mp.sqrt(5) - 1
    min_val = mp.mpf("inf")
    checked = 0
    for a in range(-12, 13):
        for b in range(-12, 13):
            for c in range(-12, 13):
                for d in range(-12, 13):
                    if abs(a * d - b * c) != 1:
                        continue
                    den = c * phi + d
                    if den == 0:
                        continue
                    th = (a * phi + b) / den
                    if not (0 < th < 1):
                        continue
                    if abs(th - (phi - 1)) < mp.mpf("1e-2000") or abs(th - (2 - phi)) < mp.mpf("1e-2000"):
                        continue
                    checked += 1
                    th_c = (a * phi_c + b) / (c * phi_c + d)
                    h_th = mp.mpf(2) / abs(th - th_c)
                    val = h_th * (1 - th)
                    assert val >= target_lb - mp.mpf("1e-2400")
                    if val < min_val:
                        min_val = val
    assert abs(min_val - target_lb) < mp.mpf("1e-2400")
    print(f"Checked {checked} elements of E_phi cap (0,1) \\ {{phi-1, 2-phi}} in [-12,12]^4:")
    print(f"  min h(theta)*(1-theta) = {mp.nstr(min_val, 30)} == sqrt(5)-1 (at [0;1,2,\\bar{{1}}]); 0 exceptions.\n")


def section_2_b5_exact() -> None:
    print("=== 2. Theorem thm:golden-b5-exact (B = 5: 16/5..19/5 - e, 2500 digits) ===")
    c_min_5 = mp.mpf(56) / (25 * mp.sqrt(5)) - 1
    c_sec_5 = 1 - mp.mpf(54) / (25 * mp.sqrt(5))
    c_58 = mp.mpf(58) / (25 * mp.sqrt(5)) - 1
    print(f"c_min^(5) = 56/(25*sqrt(5)) - 1 = {mp.nstr(c_min_5, 40)}")
    print(f"c_sec^(5) = 1 - 54/(25*sqrt(5)) = {mp.nstr(c_sec_5, 40)}")
    assert 0 < c_min_5 < c_sec_5 < c_58

    _, Q = hermite_pq(120)
    qmod5 = [q % 5 for q in Q]
    assert qmod5[:10] == [1, 1, 2, 1, 1, 4, 4, 3, 4, 4]
    for j in range(110):
        assert qmod5[j + 5] == (-qmod5[j]) % 5
        assert qmod5[j + 10] == qmod5[j]
        assert qmod5[j] != 0 and Q[j] % 2 == 1
    print("Verified Q_j mod 5 has minimal period 10 with Q_{j+5} === -Q_j (mod 5) and 5 nmid Q_j.")

    q0_all_5 = [q for q in range(1, 50) if math.gcd(q, 50) == 1]
    assert len(q0_all_5) == 20

    # 4*tau inversion for m = 56, 54, 58, 52
    sols_56 = {q0: solve_4tau_inversion(50, q0, 112) for q0 in q0_all_5}
    sols_54 = {q0: solve_4tau_inversion(50, q0, 108) for q0 in q0_all_5}
    assert {q0: v for q0, v in sols_56.items() if v} == {
        19: [[2]],
        21: [[2, 2]],
        29: [[1, 1, 2]],
        31: [[]],
    }
    assert {q0: v for q0, v in sols_54.items() if v} == {
        9: [[5]],
        11: [[4]],
        19: [[2, 1, 1, 1, 2]],
        21: [[2]],
        29: [[]],
        31: [[1, 1, 1, 1, 1, 2]],
        39: [[1, 3]],
        41: [[1, 4]],
    }
    print("Verified 4*tau inversion at D=50: 4 families at m=56, 8 families at m=54.")

    # Check Phi_{50/q0, 0}(phi)
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_c = (mp.mpf(1) - mp.sqrt(5)) / 2
    for q0 in q0_all_5:
        u = mp.mpf(50) / q0
        val = (2 / mp.sqrt(5)) * abs(u - phi) * abs(phi_c) / u
        exp_val = abs(mp.mpf(25 + q0) / (25 * mp.sqrt(5)) - 1)
        assert abs(val - exp_val) < mp.mpf("1e-2400")
        if q0 == 31:
            assert abs(val - c_min_5) < mp.mpf("1e-2400")
        elif q0 == 29:
            assert abs(val - c_sec_5) < mp.mpf("1e-2400")
        else:
            assert val > c_sec_5

    ext_tails_5 = {31: [], 29: [1, 1, 2], 19: [2], 21: [2, 2]}
    sec_tails_5 = {
        31: [1, 1, 1, 1, 1, 2],
        29: [],
        39: [1, 3],
        41: [1, 4],
        19: [2, 1, 1, 1, 2],
        21: [2],
        11: [4],
        9: [5],
    }
    tails_scan_5 = [[], [2], [3], [4], [5], [1, 3], [1, 4], [2, 2], [1, 1, 2], [2, 1, 1, 1, 2], [1, 1, 1, 1, 1, 2]]

    shared_suffixes = None
    for A in (16, 17, 18, 19):
        x = mp.mpf(A) / 5 - mp.e
        cf = cf_expansion(x, 2200)
        wins = extract_windows(cf, A, 5, -5, 220)
        assert len(wins) >= 190
        assert all(w["Gj"] == 1 and w["Dj"] == 50 for w in wins)
        # Minimal period 50 & b_{j+50} = b_j + 4
        for i in range(len(wins) - 50):
            assert wins[i + 50]["S"] == wins[i]["S"]
            assert wins[i + 50]["rj"] == wins[i]["rj"]
            assert wins[i + 50]["bj"] == wins[i]["bj"] + 4
        for d_test in (1, 2, 5, 10, 25):
            assert not all(wins[i + d_test]["S"] == wins[i]["S"] for i in range(60))

        win_types = {}
        r2_types = set()
        for i, w in enumerate(wins):
            S = tuple(w["S"])
            assert len(S) % 2 == 0 and len(S) >= 2
            u = cf_value_fraction(w["S"])
            assert u.numerator == 50
            r1 = Fraction(1, 1) / u
            if (50, S) not in win_types:
                win_types[(50, S)] = (u, r1)
                assert suffix_gap_delta(w["S"]) > 0
            if i > 0:
                r2 = cf_value_fraction([0] + list(reversed(wins[i - 1]["S"])))
                r2_types.add((50, r2))
        cur_suf = {u.denominator: list(S) for (_, S), (u, _) in win_types.items()}
        assert set(cur_suf.keys()) == set(q0_all_5)
        if shared_suffixes is None:
            shared_suffixes = cur_suf
        else:
            assert cur_suf == shared_suffixes

        if A == 16:
            verify_case2_bounds("B=5", win_types, r2_types, c_sec_5, {(50, Fraction(31, 50))})

        # Convergence on last 50 windows
        last_50 = wins[-50:]
        max_dev_ext = mp.mpf(0)
        max_dev_sec = mp.mpf(0)
        ext_seqs_trimmed = []
        for w in wins[-55:]:
            q0 = cf_value_fraction(w["S"]).denominator
            if q0 in ext_tails_5:
                ext_seqs_trimmed.append(trim_ones(cf[: w["k0"] + 2] + ext_tails_5[q0]))
        for w in last_50:
            q0 = cf_value_fraction(w["S"]).denominator
            if q0 in ext_tails_5:
                _, err = eval_orbit_error(x, cf[: w["k0"] + 2], ext_tails_5[q0])
                max_dev_ext = max(max_dev_ext, abs(err - c_min_5))
            if q0 in sec_tails_5:
                _, err = eval_orbit_error(x, cf[: w["k0"] + 2], sec_tails_5[q0])
                max_dev_sec = max(max_dev_sec, abs(err - c_sec_5))
        assert max_dev_ext < mp.mpf("2e-3") and max_dev_sec < mp.mpf("1.5e-2")
        print(f"  {A}/5 - e: {len(wins)} windows (min period 50, b_{{j+50}}=b_j+4); "
              f"max_dev_ext={mp.nstr(max_dev_ext, 4)}, max_dev_sec={mp.nstr(max_dev_sec, 4)}")
        scan_non_extremal(cf, x, last_50, ext_seqs_trimmed, tails_scan_5, mp.mpf("0.028"), f"{A}/5-e")
    print("  Shared 20 suffixes for B=5:", {k: shared_suffixes[k] for k in sorted(shared_suffixes)})
    print()


def section_3_b6_exact() -> None:
    print("=== 3. Theorem thm:golden-b6-exact (B = 6: 19/6 - e and 23/6 - e, 2500 digits) ===")
    c_min_6 = 1 - mp.mpf(79) / (36 * mp.sqrt(5))
    c_83 = mp.mpf(83) / (36 * mp.sqrt(5)) - 1
    c_sec_6 = 1 - mp.mpf(77) / (36 * mp.sqrt(5))
    print(f"c_min^(6) = 1 - 79/(36*sqrt(5)) = {mp.nstr(c_min_6, 40)}")
    print(f"excluded m=83: 83/(36*sqrt(5))-1 = {mp.nstr(c_83, 40)}")
    print(f"c_sec^(6) = 1 - 77/(36*sqrt(5)) = {mp.nstr(c_sec_6, 40)}")
    assert 0 < c_min_6 < c_83 < c_sec_6

    q0_all_6 = [5, 11, 13, 19, 29, 35, 37, 43, 53, 59, 61, 67]
    assert all((q % 24) in {5, 11, 13, 19} for q in q0_all_6)
    assert all((q % 8) in {3, 5} for q in q0_all_6)

    # Check mod-8 exclusion of m = 83
    assert 83 * 83 - 5 * 36 * 36 == 409
    assert 409 % 8 == 1
    for q0 in q0_all_6:
        for eps in (1, -1):
            for ng in (1, -1, 409, -409):
                m_res8 = (36 - eps * q0 * ng) % 8
                assert m_res8 in {1, 7}
                assert m_res8 != (83 % 8)  # 83 % 8 == 3
    print("Verified inert 3|36 forbids m=81 and mod-8 congruence (m === +-1 mod 8) forbids m=83 (=== 3 mod 8).")

    # 4*tau inversion for m = 81, 79, 83, 77
    assert all(not solve_4tau_inversion(72, q0, 162) for q0 in q0_all_6)
    assert all(not solve_4tau_inversion(72, q0, 166) for q0 in q0_all_6)
    sols_79 = {q0: solve_4tau_inversion(72, q0, 158) for q0 in q0_all_6}
    sols_77 = {q0: solve_4tau_inversion(72, q0, 154) for q0 in q0_all_6}
    assert {q0: v for q0, v in sols_79.items() if v} == {
        5: [[14, 2]],
        29: [[2]],
        43: [[]],
        67: [[1, 13, 2]],
    }
    assert {q0: v for q0, v in sols_77.items() if v} == {
        11: [[6]],
        13: [[5]],
        59: [[1, 4]],
        61: [[1, 5]],
    }
    print("Verified 4*tau inversion at D=72: m=81,83 empty; 4 families at m=79, 4 families at m=77.")

    # Check Phi_{72/q0, 0}(phi)
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_c = (mp.mpf(1) - mp.sqrt(5)) / 2
    for q0 in q0_all_6:
        u = mp.mpf(72) / q0
        val = (2 / mp.sqrt(5)) * abs(u - phi) * abs(phi_c) / u
        exp_val = abs(mp.mpf(36 + q0) / (36 * mp.sqrt(5)) - 1)
        assert abs(val - exp_val) < mp.mpf("1e-2400")
        if q0 == 43:
            assert abs(val - c_min_6) < mp.mpf("1e-2400")
        else:
            assert val > c_sec_6

    ext_tails_6 = {43: [], 67: [1, 13, 2], 29: [2], 5: [14, 2]}
    sec_tails_6 = {59: [1, 4], 61: [1, 5], 13: [5], 11: [6]}
    tails_scan_6 = [[], [2], [3], [5], [6], [1, 2], [1, 4], [1, 5], [14, 2], [1, 13, 2], [1, 2, 1, 3]]

    shared_6 = None
    for A in (19, 23):
        x = mp.mpf(A) / 6 - mp.e
        cf = cf_expansion(x, 2200)
        wins = extract_windows(cf, A, 6, -6, 230)
        assert len(wins) >= 185
        assert all(w["Gj"] == 1 and w["Dj"] == 72 for w in wins)
        # Minimal period 18 & b_{j+18} = b_j + 1, b_{j+72} = b_j + 4
        for i in range(len(wins) - 18):
            assert wins[i + 18]["S"] == wins[i]["S"]
            assert wins[i + 18]["rj"] == wins[i]["rj"]
            assert wins[i + 18]["bj"] == wins[i]["bj"] + 1
        for i in range(len(wins) - 72):
            assert wins[i + 72]["bj"] == wins[i]["bj"] + 4
        for d_test in (1, 2, 3, 6, 9):
            assert not all(wins[i + d_test]["S"] == wins[i]["S"] for i in range(40))

        win_types = {}
        r2_types = set()
        for i, w in enumerate(wins):
            S = tuple(w["S"])
            assert len(S) % 2 == 0 and len(S) >= 2
            u = cf_value_fraction(w["S"])
            assert u.numerator == 72
            r1 = Fraction(1, 1) / u
            if (72, S) not in win_types:
                win_types[(72, S)] = (u, r1)
                assert suffix_gap_delta(w["S"]) > 0
            if i > 0:
                r2 = cf_value_fraction([0] + list(reversed(wins[i - 1]["S"])))
                r2_types.add((72, r2))
        cur_suf = {u.denominator: list(S) for (_, S), (u, _) in win_types.items()}
        assert set(cur_suf.keys()) == set(q0_all_6)
        if shared_6 is None:
            shared_6 = cur_suf
        else:
            assert cur_suf == shared_6

        if A == 19:
            verify_case2_bounds("B=6", win_types, r2_types, c_sec_6, {(72, Fraction(43, 72))})

        last_36 = wins[-36:]
        max_dev_ext = mp.mpf(0)
        max_dev_sec = mp.mpf(0)
        ext_seqs_trimmed = []
        for w in wins[-40:]:
            q0 = cf_value_fraction(w["S"]).denominator
            if q0 in ext_tails_6:
                ext_seqs_trimmed.append(trim_ones(cf[: w["k0"] + 2] + ext_tails_6[q0]))
        for w in last_36:
            q0 = cf_value_fraction(w["S"]).denominator
            if q0 in ext_tails_6:
                _, err = eval_orbit_error(x, cf[: w["k0"] + 2], ext_tails_6[q0])
                max_dev_ext = max(max_dev_ext, abs(err - c_min_6))
            if q0 in sec_tails_6:
                _, err = eval_orbit_error(x, cf[: w["k0"] + 2], sec_tails_6[q0])
                max_dev_sec = max(max_dev_sec, abs(err - c_sec_6))
        assert max_dev_ext < mp.mpf("5e-3") and max_dev_sec < mp.mpf("5e-3")
        print(f"  {A}/6 - e: {len(wins)} windows (min period 18, b_{{j+18}}=b_j+1); "
              f"max_dev_ext={mp.nstr(max_dev_ext, 4)}, max_dev_sec={mp.nstr(max_dev_sec, 4)}")
        scan_non_extremal(cf, x, last_36, ext_seqs_trimmed, tails_scan_6, mp.mpf("0.036"), f"{A}/6-e")
    print("  Shared 12 suffixes for B=6:", {k: shared_6[k] for k in sorted(shared_6)})
    print()


def section_4_multiscale_exact() -> None:
    print("=== 4. Theorem thm:golden-multiscale-exact (Multi-scale & 22/7 - e, 2500 digits) ===")
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    phi_c = (mp.mpf(1) - mp.sqrt(5)) / 2

    # --- (i) (1+e)/6 ---
    print("-- Target (i): (1+e)/6 --")
    x1 = (1 + mp.e) / 6
    cf1 = cf_expansion(x1, 1400)
    wins1 = extract_windows(cf1, 1, 6, 1, 180)
    assert len(wins1) >= 135
    for i in range(len(wins1) - 6):
        assert wins1[i + 6]["S"] == wins1[i]["S"]
        assert wins1[i + 6]["rj"] == wins1[i]["rj"]
        assert wins1[i + 6]["Dj"] == wins1[i]["Dj"]
        assert wins1[i + 6]["Gj"] == wins1[i]["Gj"]
        assert wins1[i + 6]["bj"] == wins1[i]["bj"] + 2 * (wins1[i]["Gj"] ** 2)
    for i in range(len(wins1) - 12):
        assert wins1[i + 12]["bj"] == wins1[i]["bj"] + 4 * (wins1[i]["Gj"] ** 2)
    win_types_1 = {}
    r2_types_1 = set()
    for i, w in enumerate(wins1):
        assert w["Gj"] in {2, 6} and w["Dj"] in {1, 3}
        if w["Dj"] == 1:
            assert w["rj"] == 1 and w["S"] == [] and w["j"] % 6 in {2, 3, 4, 5}
        else:
            assert w["rj"] == 3 and w["S"] == [1, 2] and w["j"] % 6 in {0, 1}
        S = tuple(w["S"])
        assert len(S) % 2 == 0
        u = cf_value_fraction(w["S"]) if S else Fraction(0, 1)
        r1 = Fraction(1, 1) / u if S else Fraction(0, 1)
        if (w["Dj"], S) not in win_types_1:
            win_types_1[(w["Dj"], S)] = (u, r1)
            if S:
                assert suffix_gap_delta(w["S"]) > 0
        if i > 0:
            Sp = wins1[i - 1]["S"]
            r2 = cf_value_fraction([0] + list(reversed(Sp))) if Sp else Fraction(0, 1)
            r2_types_1.add((wins1[i - 1]["Dj"], r2))
    assert solve_4tau_inversion(3, 2, 7) == [[]]
    assert solve_4tau_inversion(3, 2, 5) == [[1, 2], [2]]
    c1_min = mp.mpf(7) / (3 * mp.sqrt(5)) - 1
    c1_sec = 1 - mp.sqrt(5) / 3
    verify_case2_bounds("(1+e)/6", win_types_1, r2_types_1, c1_sec, set())
    ext_1 = [trim_ones(cf1[: w["k0"] + 2]) for w in wins1[-24:] if w["Dj"] == 3]
    for w in wins1[-12:]:
        if w["Dj"] == 3:
            _, e_min = eval_orbit_error(x1, cf1[: w["k0"] + 2], [])
            _, e_s1 = eval_orbit_error(x1, cf1[: w["k0"] + 2], [2])
            _, e_s2 = eval_orbit_error(x1, cf1[: w["k0"] + 2], [1, 2])
            assert abs(e_min - c1_min) < mp.mpf("5e-3")
            assert abs(e_s1 - c1_sec) < mp.mpf("5e-3")
            assert abs(e_s2 - c1_sec) < mp.mpf("5e-3")
    scan_non_extremal(cf1, x1, wins1[-12:], ext_1, [[], [2], [1, 2], [2, 2], [3]], mp.mpf("0.248"), "(1+e)/6")

    # --- (ii) (1+e)/3 ---
    print("-- Target (ii): (1+e)/3 --")
    x2 = (1 + mp.e) / 3
    cf2 = cf_expansion(x2, 1400)
    wins2 = extract_windows(cf2, 1, 3, 1, 180)
    assert len(wins2) >= 160
    for i in range(len(wins2) - 6):
        assert wins2[i + 6]["S"] == wins2[i]["S"]
        assert wins2[i + 6]["Dj"] == wins2[i]["Dj"]
        assert wins2[i + 6]["bj"] == wins2[i]["bj"] + 4 * (wins2[i]["Gj"] ** 2)
    win_types_2 = {}
    r2_types_2 = set()
    for i, w in enumerate(wins2):
        assert w["Gj"] in {1, 3} and w["Dj"] in {2, 6}
        if w["Dj"] == 2:
            assert w["S"] == [1, 1] and w["j"] % 6 in {2, 3, 4, 5}
        else:
            assert w["S"] == [1, 5] and w["j"] % 6 in {0, 1}
        S = tuple(w["S"])
        u = cf_value_fraction(w["S"])
        r1 = Fraction(1, 1) / u
        if (w["Dj"], S) not in win_types_2:
            win_types_2[(w["Dj"], S)] = (u, r1)
            assert suffix_gap_delta(w["S"]) > 0
        if i > 0:
            r2 = cf_value_fraction([0] + list(reversed(wins2[i - 1]["S"])))
            r2_types_2.add((wins2[i - 1]["Dj"], r2))
    assert solve_4tau_inversion(2, 1, 4) == [[], [2]]
    assert solve_4tau_inversion(6, 5, 12) == []  # 3 | 3 inert forbids m=6 (M=12)
    assert solve_4tau_inversion(6, 5, 16) == [[], [1, 4]]
    c2_min = 1 - mp.mpf(2) / mp.sqrt(5)
    c2_sec = mp.mpf(8) / (3 * mp.sqrt(5)) - 1
    verify_case2_bounds("(1+e)/3", win_types_2, r2_types_2, c2_sec, {(2, Fraction(1, 2))})
    ext_2 = []
    for w in wins2[-18:]:
        if w["Dj"] == 2:
            ext_2.append(trim_ones(cf2[: w["k0"] + 2]))
            ext_2.append(trim_ones(cf2[: w["k0"] + 2] + [2]))
    for w in wins2[-12:]:
        if w["Dj"] == 2:
            _, e1 = eval_orbit_error(x2, cf2[: w["k0"] + 2], [])
            _, e2 = eval_orbit_error(x2, cf2[: w["k0"] + 2], [2])
            assert abs(e1 - c2_min) < mp.mpf("5e-3") and abs(e2 - c2_min) < mp.mpf("5e-3")
        else:
            _, e3 = eval_orbit_error(x2, cf2[: w["k0"] + 2], [])
            _, e4 = eval_orbit_error(x2, cf2[: w["k0"] + 2], [1, 4])
            assert abs(e3 - c2_sec) < mp.mpf("5e-3") and abs(e4 - c2_sec) < mp.mpf("5e-3")
    scan_non_extremal(cf2, x2, wins2[-12:], ext_2, [[], [2], [1, 4], [1, 2], [3]], mp.mpf("0.185"), "(1+e)/3")

    # --- (iii) (1+2e)/3 ---
    print("-- Target (iii): (1+2e)/3 --")
    x3 = (1 + 2 * mp.e) / 3
    cf3 = cf_expansion(x3, 1400)
    wins3 = extract_windows(cf3, 1, 3, 2, 180)
    assert len(wins3) >= 160
    for i in range(len(wins3) - 6):
        assert wins3[i + 6]["S"] == wins3[i]["S"]
        assert wins3[i + 6]["Dj"] == wins3[i]["Dj"]
        assert wins3[i + 6]["Gj"] == wins3[i]["Gj"]
        assert wins3[i + 6]["bj"] == wins3[i]["bj"] + 2 * (wins3[i]["Gj"] ** 2)
    for i in range(len(wins3) - 12):
        assert wins3[i + 12]["bj"] == wins3[i]["bj"] + 4 * (wins3[i]["Gj"] ** 2)
    win_types_3 = {}
    r2_types_3 = set()
    for i, w in enumerate(wins3):
        assert w["Gj"] in {1, 3} and w["Dj"] in {4, 12}
        jm = w["j"] % 6
        if jm == 4:
            assert w["Dj"] == 12 and w["S"] == [2, 2, 1, 1]
        elif jm == 3:
            assert w["Dj"] == 12 and w["S"] == [1, 11]
        elif jm in {1, 5}:
            assert w["Dj"] == 4 and w["S"] == [3, 1]
        else:
            assert w["Dj"] == 4 and w["S"] == [1, 3]
        S = tuple(w["S"])
        u = cf_value_fraction(w["S"])
        r1 = Fraction(1, 1) / u
        if (w["Dj"], S) not in win_types_3:
            win_types_3[(w["Dj"], S)] = (u, r1)
            assert suffix_gap_delta(w["S"]) > 0
        if i > 0:
            r2 = cf_value_fraction([0] + list(reversed(wins3[i - 1]["S"])))
            r2_types_3.add((wins3[i - 1]["Dj"], r2))
    assert solve_4tau_inversion(12, 5, 26) == [[2], [2, 2]]
    assert solve_4tau_inversion(12, 5, 30) == [] and solve_4tau_inversion(12, 11, 30) == []  # 3|6 inert forbids m=15
    assert solve_4tau_inversion(4, 3, 10) == [[], [1, 2]]
    assert solve_4tau_inversion(4, 1, 10) == [[2], [3]]
    c3_min = 1 - mp.mpf(13) / (6 * mp.sqrt(5))
    c3_sec = mp.sqrt(5) / 2 - 1
    verify_case2_bounds("(1+2e)/3", win_types_3, r2_types_3, c3_sec, {(12, Fraction(7, 12))})
    ext_3 = []
    for w in wins3[-18:]:
        if w["S"] == [2, 2, 1, 1]:
            ext_3.append(trim_ones(cf3[: w["k0"] + 2] + [2]))
            ext_3.append(trim_ones(cf3[: w["k0"] + 2] + [2, 2]))
    for w in wins3[-12:]:
        if w["S"] == [2, 2, 1, 1]:
            _, e1 = eval_orbit_error(x3, cf3[: w["k0"] + 2], [2])
            _, e2 = eval_orbit_error(x3, cf3[: w["k0"] + 2], [2, 2])
            assert abs(e1 - c3_min) < mp.mpf("5e-3") and abs(e2 - c3_min) < mp.mpf("5e-3")
        elif w["S"] == [1, 3]:
            _, e3 = eval_orbit_error(x3, cf3[: w["k0"] + 2], [])
            _, e4 = eval_orbit_error(x3, cf3[: w["k0"] + 2], [1, 2])
            assert abs(e3 - c3_sec) < mp.mpf("5e-3") and abs(e4 - c3_sec) < mp.mpf("5e-3")
        elif w["S"] == [3, 1]:
            _, e5 = eval_orbit_error(x3, cf3[: w["k0"] + 2], [2])
            _, e6 = eval_orbit_error(x3, cf3[: w["k0"] + 2], [3])
            assert abs(e5 - c3_sec) < mp.mpf("5e-3") and abs(e6 - c3_sec) < mp.mpf("5e-3")
    scan_non_extremal(cf3, x3, wins3[-12:], ext_3, [[], [2], [3], [1, 2], [2, 2], [2, 2, 2]], mp.mpf("0.110"), "(1+2e)/3")

    # --- (iv) 22/7 - e ---
    print("-- Target (iv): 22/7 - e --")
    P, Q = hermite_pq(220)
    assert [Q[j] % 7 for j in range(14)] == [1, 1, 0, 1, 0, 1, 1, 6, 6, 0, 6, 0, 6, 6]
    for j in range(100):
        assert Q[j + 7] % 7 == (-Q[j]) % 7
        assert Q[j + 49] % 49 == (-Q[j]) % 49
        assert Q[j + 98] % 49 == Q[j] % 49

    x4 = mp.mpf(22) / 7 - mp.e
    cf4 = cf_expansion(x4, 2400)
    wins4 = extract_windows(cf4, 22, 7, -7, 260)
    assert len(wins4) >= 200
    for i in range(len(wins4) - 98):
        assert wins4[i + 98]["S"] == wins4[i]["S"]
        assert wins4[i + 98]["rj"] == wins4[i]["rj"]
        assert wins4[i + 98]["Dj"] == wins4[i]["Dj"]
        assert wins4[i + 98]["Gj"] == wins4[i]["Gj"]
        assert wins4[i + 98]["bj"] == wins4[i]["bj"] + 4 * (wins4[i]["Gj"] ** 2)

    p98 = [w for w in wins4 if 50 <= w["j"] < 148]
    assert len(p98) == 98
    dist_4: dict[int, int] = {}
    d2_list = []
    for w in p98:
        dist_4[w["Dj"]] = dist_4.get(w["Dj"], 0) + 1
        if w["Dj"] == 2:
            d2_list.append((w["j"], w["Gj"], w["Gj_next"], w["W"]))
    assert dist_4 == {2: 8, 14: 48, 98: 42}
    assert len(d2_list) == 8
    print("  All 8 D_j=2 windows in j=50..147:", d2_list)
    for j_w, g0, g1, W in d2_list:
        assert {g0, g1} == {1, 49} and W[1:] == [1, 1]

    win_types_4 = {}
    r2_types_4 = set()
    for i, w in enumerate(wins4):
        S = tuple(w["S"])
        assert len(S) % 2 == 0 and len(S) >= 2
        u = cf_value_fraction(w["S"])
        assert u.numerator == w["Dj"]
        r1 = Fraction(1, 1) / u
        if (w["Dj"], S) not in win_types_4:
            win_types_4[(w["Dj"], S)] = (u, r1)
            assert suffix_gap_delta(w["S"]) > 0
        if i > 0:
            r2 = cf_value_fraction([0] + list(reversed(wins4[i - 1]["S"])))
            r2_types_4.add((wins4[i - 1]["Dj"], r2))
    assert len(win_types_4) == 21  # 1 (D=2) + 6 (D=14) + 14 (D=98)

    # Check D=2 for m=1..5 (M=2,4,6,8,10 -> parity excludes m=1,3,5; m=2 -> 1-2/sqrt5; m=4 -> 4/sqrt5-1)
    assert solve_4tau_inversion(2, 1, 2) == []  # m=1 odd forbidden
    assert solve_4tau_inversion(2, 1, 4) == [[], [2]]  # m=2
    assert solve_4tau_inversion(2, 1, 6) == []  # m=3 odd forbidden
    assert solve_4tau_inversion(2, 1, 8) == [[1, 1, 2], [2, 2]]  # m=4
    assert solve_4tau_inversion(2, 1, 10) == []  # m=5 odd forbidden
    # Check D=14 (inert 7|7 forbids m=14 -> M=28; m=16 -> M=32 attained)
    q0_14 = sorted(u.denominator for (D, _), (u, _) in win_types_4.items() if D == 14)
    assert q0_14 == [1, 3, 5, 9, 11, 13]
    assert all(not solve_4tau_inversion(14, q0, 28) for q0 in q0_14)
    assert {q0: solve_4tau_inversion(14, q0, 32) for q0 in q0_14 if solve_4tau_inversion(14, q0, 32)} == {
        3: [[4]], 5: [[2]], 9: [[]], 11: [[1, 3]]
    }
    # Check D=98 (m=110 extremal, inert 7|49 forbids m=112, m=108 second limit point)
    q0_98 = sorted(u.denominator for (D, _), (u, _) in win_types_4.items() if D == 98)
    assert q0_98 == [1, 13, 15, 27, 29, 41, 43, 55, 57, 69, 71, 83, 85, 97]
    assert all(not solve_4tau_inversion(98, q0, 224) for q0 in q0_98)
    sols_110 = {q0: solve_4tau_inversion(98, q0, 220) for q0 in q0_98}
    sols_108 = {q0: solve_4tau_inversion(98, q0, 216) for q0 in q0_98}
    assert {q0: v for q0, v in sols_110.items() if v} == {
        27: [[3]], 29: [[3, 2]], 69: [[1, 2, 2]], 71: [[1, 2]]
    }
    assert {q0: v for q0, v in sols_108.items() if v} == {
        41: [[2, 2]], 43: [[2, 3]], 55: [[1, 1, 3]], 57: [[1, 1, 2]]
    }
    # Case 1 Phi_{D/q0, 0}(phi)
    for (D, _), (u, _) in win_types_4.items():
        val = (2 / mp.sqrt(5)) * abs(mp.mpf(u.numerator) / u.denominator - phi) * abs(phi_c) / (mp.mpf(u.numerator) / u.denominator)
        if D == 2:
            assert abs(val - (1 - 2 / mp.sqrt(5))) < mp.mpf("1e-2400")
        elif D == 14:
            assert val >= mp.mpf(16) / (7 * mp.sqrt(5)) - 1 - mp.mpf("1e-2400")
        else:
            assert val >= 1 - mp.mpf(106) / (49 * mp.sqrt(5)) - mp.mpf("1e-2400")

    c4_min = mp.mpf(110) / (49 * mp.sqrt(5)) - 1
    c4_sec = 1 - mp.mpf(108) / (49 * mp.sqrt(5))
    verify_case2_bounds("22/7-e", win_types_4, r2_types_4, c4_sec, set())

    ext_tails_4 = {27: [3], 29: [3, 2], 69: [1, 2, 2], 71: [1, 2]}
    sec_tails_4 = {41: [2, 2], 43: [2, 3], 55: [1, 1, 3], 57: [1, 1, 2]}
    last_98 = wins4[-98:]
    ext_seqs_4 = []
    for w in wins4[-105:]:
        if w["Dj"] == 98:
            q0 = cf_value_fraction(w["S"]).denominator
            if q0 in ext_tails_4:
                ext_seqs_4.append(trim_ones(cf4[: w["k0"] + 2] + ext_tails_4[q0]))
    max_dev_ext = mp.mpf(0)
    max_dev_sec = mp.mpf(0)
    for w in last_98:
        if w["Dj"] == 98:
            q0 = cf_value_fraction(w["S"]).denominator
            if q0 in ext_tails_4:
                _, err = eval_orbit_error(x4, cf4[: w["k0"] + 2], ext_tails_4[q0])
                max_dev_ext = max(max_dev_ext, abs(err - c4_min))
            if q0 in sec_tails_4:
                _, err = eval_orbit_error(x4, cf4[: w["k0"] + 2], sec_tails_4[q0])
                max_dev_sec = max(max_dev_sec, abs(err - c4_sec))
    assert max_dev_ext < mp.mpf("5e-3") and max_dev_sec < mp.mpf("5e-3")
    print(f"  22/7 - e: {len(wins4)} windows, max_dev_ext={mp.nstr(max_dev_ext, 4)}, max_dev_sec={mp.nstr(max_dev_sec, 4)}")
    tails_scan_4 = [[], [2], [3], [4], [1, 2], [2, 2], [2, 3], [3, 2], [1, 1, 2], [1, 1, 3], [1, 2, 2]]
    scan_non_extremal(cf4, x4, last_98, ext_seqs_4, tails_scan_4, mp.mpf("0.008"), "22/7-e")
    print("\nALL PATH 2A B=5, B=6, AND MULTISCALE CHECKS PASSED WITH 0 ASSERTION FAILURES.")


if __name__ == "__main__":
    section_1_general_case2_criterion()
    section_2_b5_exact()
    section_3_b6_exact()
    section_4_multiscale_exact()
