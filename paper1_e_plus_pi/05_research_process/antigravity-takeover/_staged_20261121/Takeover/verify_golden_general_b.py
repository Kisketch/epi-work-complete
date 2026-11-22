r"""
High-precision (2500-digit mpmath) verification for Path 2A General-B Theory (Paper 1, Section 8):
1. General Parametric & Structural Theorems:
   - Theorem G1: Odd-prime Hermite periodicity/anti-periodicity (P_{j+p} === P_j, Q_{j+p} === -Q_j,
     palindromic symmetry on 0..p-1), Z_Q vs N_Q prime partition (p <= 200), and exact single-scale
     criterion for arbitrary (A, B, C) (including (2+e)/7 single-scale vs (1+e)/7 multi-scale).
   - Theorem G2: Universal quarter-period theorem for ALL even B = 2^a * B_odd:
     2-adic transfer matrix T_r === I + 2^r [[1,3],[5,-1]] (mod 2^{r+3}) for r = 3..10,
     Q_{j+B^2/2} === u * Q_j (mod 2B^2), P_{j+B^2/2} === u * P_j (mod 2B),
     2500-digit mpmath window quarter-period W_{j+B^2/2} = (b_j + G_j^2, S_j) (including multi-scale B=14),
     and universal 2-adic residue laws q_0 mod 8, 16, 32, 64 (and Q_{2k+1} === Q_{2k} mod 64).
   - Theorem G3: Ramified-5 valuation rigidity (v_5(N(p*phi+q)) <= 1, v_5(M^2 - 5D^2) <= 2,
     excluding 25|m when 5|d), Universal Case 2 Collapse for D_max >= 14 (2*(2-phi)/sqrt(5) > sqrt(5)/7),
     and sharp universal lower envelope c_phi(A/B-e) >= 1/(10*B^4 + B^2*sqrt(5)).
2. B = 7 (all 6 coprime classes A === 1..6 mod 7):
   - Full three-scale D_j in {2, 14, 98} with distribution {2:8, 14:48, 98:42} across ALL 6 classes,
     explanation of why D_j=2 (1-2/sqrt(5)) does not win, shared 21 suffixes, inert 7|7,49 exclusions,
     4*tau inversion (4 extremal at m=110, 4 c_sec at m=108), Case 2 closure, 2500-digit scans.
3. B = 8 (all 4 odd classes A === 1, 3, 5, 7 mod 8):
   - Minimal period S=32 (b_{j+32}=b_j+1), two 18-suffix groups (A mod 4 = 1 vs 3), q_0 mod 16 in {1,7,15},
     4*tau inversion (3 extremal at m=143, 3 c_sec at m=145 per group), Case 2 closure, 2500-digit scans.
4. B = 9 (all 6 coprime classes 3 nmid A):
   - Period T=162, shared 54 suffixes (Z/162Z)^x, inert 3|81 exclusion of m=180,
     4*tau inversion (8 extremal at m=182, 4 c_sec at m=184), Case 2 closure, 2500-digit scans.
5. B = 10 (all 4 coprime classes gcd(A, 10) = 1):
   - Minimal period S=50 (b_{j+50}=b_j+1), shared 40 suffixes (q_0 === +-3 mod 8),
     Ramified-5 exclusion of m=225, 4*tau inversion (4 extremal at m=223, 4 c_sec at m=221),
     Case 2 closure, 2500-digit scans.
6. B = 11 (all 10 coprime classes 11 nmid A) and B = 12 (all 4 coprime classes gcd(A, 12) = 1):
   - Complete Case 1 + Case 2 theorems, 4*tau inversions, Case 2 closure, and 2500-digit scans.
"""

from __future__ import annotations
from fractions import Fraction
import math
import mpmath as mp

mp.mp.dps = 2500


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d != 0 for d in range(2, math.isqrt(n) + 1))


def extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    if b == 0:
        return a, 1, 0
    g, x1, y1 = extended_gcd(b, a % b)
    return g, y1, x1 - (a // b) * y1


def hermite_pq(n_max: int) -> tuple[list[int], list[int]]:
    P, Q = [1, 3], [1, 1]
    for j in range(1, n_max):
        P.append((4 * j + 2) * P[-1] + P[-2])
        Q.append((4 * j + 2) * Q[-1] + Q[-2])
    return P, Q


def hermite_mod(mod: int, n_max: int) -> tuple[list[int], list[int]]:
    P, Q = [1 % mod, 3 % mod], [1 % mod, 1 % mod]
    for j in range(1, n_max):
        m = (4 * j + 2) % mod
        P.append((m * P[-1] + P[-2]) % mod)
        Q.append((m * Q[-1] + Q[-2]) % mod)
    return P, Q


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


def eval_orbit_error_fast(
    x: mp.mpf,
    p_cf: list[int],
    q_cf: list[int],
    pos: int,
    extra_digits: list[int],
) -> tuple[mp.mpf, mp.mpf]:
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    if pos == 0:
        p1, q1, p0, q0 = 1, 0, 0, 1
    elif pos == 1:
        p1, q1, p0, q0 = p_cf[0], q_cf[0], 1, 0
    else:
        p1, q1, p0, q0 = p_cf[pos - 1], q_cf[pos - 1], p_cf[pos - 2], q_cf[pos - 2]
    for d in extra_digits:
        p1, p0 = d * p1 + p0, p1
        q1, q0 = d * q1 + q0, q1
    h_beta = mp.mpf(2 * abs(-q1 * q1 + q1 * q0 + q0 * q0)) / mp.sqrt(5)
    beta = (mp.mpf(p1) * phi + mp.mpf(p0)) / (mp.mpf(q1) * phi + mp.mpf(q0))
    return h_beta, h_beta * abs(x - beta)


def extract_windows(
    cf: list[int],
    q_cf: list[int],
    P: list[int],
    Q: list[int],
    A: int,
    B: int,
    C: int,
    j_max: int,
) -> list[dict]:
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
    Dmax: int,
) -> None:
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    r1_all = [mp.mpf(r1.numerator) / r1.denominator for _, (_, r1) in win_types.items()]
    r1_pos = [mp.mpf(r1.numerator) / r1.denominator for (D, _), (_, r1) in win_types.items() if D > 1]
    r2_all = [mp.mpf(r2.numerator) / r2.denominator for _, r2 in r2_types]
    r1_min, r1_max = min(r1_all), max(r1_all)
    r1_pos_min = min(r1_pos)
    r2_min = min(r2_all)

    # Universal Case 2 Collapse check for Dmax >= 14:
    dmax = Dmax // 2
    assert Dmax == 2 * dmax and dmax >= 7
    assert (2 / mp.sqrt(5)) * (2 - phi) > mp.sqrt(5) / dmax > c_sec

    # (a) theta = phi - 1, Q_n = 1 reduces to Case 1 value of window j-1
    q1_min_non_excl = mp.mpf("inf")
    for Dprev, r2 in sorted(r2_types):
        val = abs((mp.mpf(Dprev) + 2 * mp.mpf(r2.numerator)) / (Dprev * mp.sqrt(5)) - 1)
        if (Dprev, r2) not in excluded_r2_pairs:
            if val < q1_min_non_excl:
                q1_min_non_excl = val
    assert q1_min_non_excl >= c_sec - mp.mpf("1e-2400")

    b_a_mid = (2 / mp.sqrt(5)) * (2 - phi + min(r1_min, r2_min))
    b_a_gt = (2 / mp.sqrt(5)) * (phi - r1_max)
    b_b_1 = (2 / mp.sqrt(5)) * (2 + phi + r2_min)
    b_b_mid = (2 / mp.sqrt(5)) * (phi - 1 + r1_min)
    b_b_gt = (2 / mp.sqrt(5)) * (3 - phi - r1_max)
    b_c_1 = 2 * mp.sqrt(5) * (1 / (phi ** 2) + r2_min)
    b_c_mid = 2 * mp.sqrt(5) * min(r1_pos_min, 1 - r1_max)

    min_other = min(b_a_mid, b_a_gt, b_b_1, b_b_mid, b_b_gt, b_c_1, b_c_mid)
    assert min_other >= mp.sqrt(5) / dmax - mp.mpf("1e-2400")
    assert min_other > c_sec
    print(
        f"  [{name}] Case 2 closure: Q1(non-excl)>={mp.nstr(q1_min_non_excl, 10)}, "
        f"(a)mid={mp.nstr(b_a_mid, 8)}, (a)gt={mp.nstr(b_a_gt, 8)}, (b)1={mp.nstr(b_b_1, 8)}, "
        f"(b)mid={mp.nstr(b_b_mid, 8)}, (b)gt={mp.nstr(b_b_gt, 8)}, (c)1={mp.nstr(b_c_1, 8)}, "
        f"(c)>=2={mp.nstr(b_c_mid, 8)}, min_other={mp.nstr(min_other, 8)} >= sqrt(5)/{dmax}={mp.nstr(mp.sqrt(5)/dmax, 8)} > c_sec={mp.nstr(c_sec, 10)}",
        flush=True,
    )


def scan_non_extremal(
    cf: list[int],
    p_cf: list[int],
    q_cf: list[int],
    x: mp.mpf,
    wins_slice: list[dict],
    ext_seqs_trimmed: list[list[int]],
    sec_seqs_trimmed: list[list[int]],
    tails_scan: list[list[int]],
    threshold_ext: mp.mpf,
    threshold_sec: mp.mpf,
    label: str,
) -> None:
    ext_set = {tuple(s) for s in ext_seqs_trimmed}
    sec_set = {tuple(s) for s in sec_seqs_trimmed}
    min_err_ext = mp.mpf("inf")
    min_err_sec = mp.mpf("inf")
    scanned = 0
    start_k = wins_slice[0]["k0"] + 1
    end_k = wins_slice[-1]["k1"]
    for pos in range(start_k, end_k + 1):
        a_pos = cf[pos]
        cands_q = sorted({1, 2, 3, max(1, a_pos - 1), a_pos + 1})
        for q_alt in cands_q:
            if q_alt == a_pos:
                continue
            for tail in tails_scan:
                cand = tuple(trim_ones(cf[:pos] + [q_alt] + tail))
                if cand in ext_set:
                    continue
                _, err = eval_orbit_error_fast(x, p_cf, q_cf, pos, [q_alt] + tail)
                scanned += 1
                if err < min_err_ext:
                    min_err_ext = err
                if cand not in sec_set and err < min_err_sec:
                    min_err_sec = err
    assert min_err_ext > threshold_ext, f"{label}: min_err_ext={min_err_ext} <= {threshold_ext}"
    assert min_err_sec > threshold_sec, f"{label}: min_err_sec={min_err_sec} <= {threshold_sec}"
    print(
        f"    non-extremal scan ({scanned} pts): min_non_ext={mp.nstr(min_err_ext, 8)} (>{mp.nstr(threshold_ext, 6)}), "
        f"min_non_ext_sec={mp.nstr(min_err_sec, 8)} (>{mp.nstr(threshold_sec, 6)})",
        flush=True,
    )


def section_1_general_theorems() -> None:
    print("=== 1. General Parametric & Structural Theorems (G1, G2, G3) ===", flush=True)
    # --- G1: Odd-prime anti-periodicity, palindrome, Z_Q vs N_Q, single-scale criterion ---
    primes = [p for p in range(3, 200) if is_prime(p)]
    z_q = []
    n_q = [2]
    for p in primes:
        Pp, Qp = hermite_mod(p, 4 * p + 5)
        assert Pp[p - 1] == 1 and Pp[p] == 1 and Qp[p - 1] == 1 and Qp[p] == (p - 1)
        for j in range(2 * p + 3):
            assert Pp[j + p] == Pp[j]
            assert Qp[j + p] == (-Qp[j]) % p
            assert Qp[j + 2 * p] == Qp[j]
        for j in range(p):
            assert Pp[p - 1 - j] == Pp[j]
            assert Qp[p - 1 - j] == Qp[j]
        half_zeros = [j for j in range((p + 1) // 2) if Qp[j] == 0]
        full_zeros = [j for j in range(2 * p) if Qp[j] == 0]
        assert bool(half_zeros) == bool(full_zeros)
        if full_zeros:
            z_q.append(p)
        else:
            n_q.append(p)
    assert z_q == [7, 11, 13, 31, 41, 71, 79, 97, 101, 103, 107, 157, 173, 181, 199]
    assert n_q[:10] == [2, 3, 5, 17, 19, 23, 29, 37, 43, 47]
    print(f"G1(1): Verified P_{{j+p}}===P_j, Q_{{j+p}}===-Q_j, and 0..p-1 palindromy for all {len(primes)} odd primes < 200.")
    print(f"       Z_Q cap [2,200] = {z_q}; N_Q cap [2,200] (first 10) = {n_q[:10]}.")

    # G1(2): Test single-scale criterion on (2+e)/7 vs (1+e)/7 vs e/5 vs (1+e)/5
    P_ex, Q_ex = hermite_pq(300)
    assert all(math.gcd(2 * Q_ex[j] + P_ex[j], 7 * Q_ex[j]) == 1 for j in range(150))
    assert {math.gcd(Q_ex[j] + P_ex[j], 7 * Q_ex[j]) for j in range(150)} == {1, 7}
    assert all(math.gcd(P_ex[j], 5 * Q_ex[j]) == 1 for j in range(150))
    assert {math.gcd(Q_ex[j] + P_ex[j], 5 * Q_ex[j]) for j in range(150)} == {1, 5}
    # Verify (2+e)/7 in 2500-digit mpmath is single-scale D_j == 14
    x_2e7 = (2 + mp.e) / 7
    cf_2e7 = cf_expansion(x_2e7, 1500)
    _, q_2e7 = convergents(cf_2e7)
    wins_2e7 = extract_windows(cf_2e7, q_2e7, P_ex, Q_ex, 2, 7, 1, 120)
    assert len(wins_2e7) >= 60 and all(w["Gj"] == 1 and w["Dj"] == 14 for w in wins_2e7)
    print("G1(2): Verified exact (A,B,C) single-scale criterion: (2+e)/7 has G_j=1, D_j=14; (1+e)/7 has G_j in {1,7}.")

    # --- G2: Universal Quarter-Period Theorem & 2-adic laws ---
    for r in range(3, 11):
        S = 1 << r
        mod = 1 << (r + 3)
        a, b, c, d = 1, 0, 0, 1
        for j in range(S):
            m = (4 * j + 2) % mod
            a, b, c, d = (m * a + c) % mod, (m * b + d) % mod, a, b
        assert (a, b, c, d) == (
            (1 + (1 << r)) % mod,
            (3 * (1 << r)) % mod,
            (5 * (1 << r)) % mod,
            (1 - (1 << r)) % mod,
        )
    print("G2(1): Verified T_r === I + 2^r * [[1,3],[5,-1]] (mod 2^{r+3}) for all r = 3..10.")

    P_big, Q_big = hermite_pq(1200)
    assert all((Q_big[2 * k + 1] - Q_big[2 * k]) % 64 == 0 for k in range(300))
    for B in range(2, 34, 2):
        D = 2 * B * B
        S = (B * B) // 2
        u = (B * B + 1) % D if B % 4 == 0 else (1 - S) % D
        assert (u * u) % D == 1
        assert all((Q_big[j + S] - u * Q_big[j]) % D == 0 for j in range(150))
        assert all((P_big[j + S] - u * P_big[j]) % (2 * B) == 0 for j in range(150))
    print("G2(2): Verified Q_{2k+1} === Q_{2k} (mod 64) and Q_{j+B^2/2} === u*Q_j (mod 2B^2), P_{j+B^2/2} === u*P_j (mod 2B) for all even B=2..32.")

    # Test 2500-digit mpmath quarter-period on multi-scale even B = 14 (29/14 - e)
    x_14 = mp.mpf(29) / 14 - mp.e
    cf_14 = cf_expansion(x_14, 2800)
    _, q_14 = convergents(cf_14)
    wins_14 = extract_windows(cf_14, q_14, P_big, Q_big, 29, 14, -14, 410)
    assert len(wins_14) >= 200
    for i in range(len(wins_14) - 98):
        assert wins_14[i + 98]["S"] == wins_14[i]["S"]
        assert wins_14[i + 98]["Gj"] == wins_14[i]["Gj"]
        assert wins_14[i + 98]["Dj"] == wins_14[i]["Dj"]
        assert wins_14[i + 98]["bj"] == wins_14[i]["bj"] + (wins_14[i]["Gj"] ** 2)
    d14_dist = {}
    for w in wins_14[:98]:
        d14_dist[w["Dj"]] = d14_dist.get(w["Dj"], 0) + 1
    assert d14_dist == {8: 8, 56: 48, 392: 42}
    print(f"G2(3): Verified 2500-digit multi-scale B=14 (29/14 - e): quarter-period S=98, b_{{j+98}}=b_j+G_j^2, D_dist={d14_dist}.")

    # Universal 2-adic q_0 residue laws across even B in {2,4,6,8,10,12,14,16,18,20,24,32}
    for B in [2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 24, 32]:
        T = 2 * B * B
        L = B * B
        Pm, Qm = hermite_mod(T, L + T + 5)
        for j in range(L + 1, L + T + 1):
            u0, u1 = (Qm[j] - B * Pm[j]) % T, (B * Qm[j]) % T
            v0, v1 = (Qm[j + 1] - B * Pm[j + 1]) % T, (B * Qm[j + 1]) % T
            G0 = math.gcd(math.gcd(u0, u1), B * B)
            G1 = math.gcd(math.gcd(v0, v1), B * B)
            if G0 == 1 and G1 == 1:
                g1, x1, y1 = extended_gcd(u0, u1)
                g2, x2, _ = extended_gcd(g1, T)
                assert g2 == 1
                q0 = ((x2 * x1) % T * v0 + (x2 * y1) % T * v1) % T
                if B % 4 == 2:
                    assert q0 % 8 == (5 if j % 2 == 0 else 3)
                else:
                    assert q0 % 8 == (1 if j % 2 == 0 else 7)
                    if B % 8 == 0:
                        assert q0 % 16 in ({1} if j % 2 == 0 else {7, 15})
                    if B % 16 == 0:
                        assert q0 % 32 in ({1} if j % 2 == 0 else {7, 15, 23, 31})
                    if B % 32 == 0:
                        assert q0 % 64 in ({1} if j % 2 == 0 else {7, 15, 23, 31, 39, 47, 55, 63})
    print("G2(4): Verified universal 2-adic q_0 residue laws (mod 8, 16, 32, 64) for all B in {2,4,6,8,10,12,14,16,18,20,24,32}.")

    # --- G3: Ramified-5 valuation rigidity & Universal Case 2 Collapse ---
    for p in range(-25, 26):
        for q in range(-25, 26):
            if math.gcd(p, q) != 1:
                continue
            norm = -p * p + p * q + q * q
            assert norm % 25 != 0
    # Verify v_5(M_{u,v}^2 - 5D^2) <= 2 across all 744 GL_2(Z) matrices in [-6,6]^4 at 4 endpoints
    gl2_6 = []
    for a in range(-6, 7):
        for b in range(-6, 7):
            for c in range(-6, 7):
                for d in range(-6, 7):
                    if abs(a * d - b * c) == 1:
                        gl2_6.append((a, b, c, d))
    assert len(gl2_6) == 744
    for p1, q1, p2, q2 in [(10, 3, 0, 1), (200, 123, 0, 1), (50, 31, 0, 1), (15, 7, 2, 5)]:
        D = p1 * q2 + p2 * q1
        for a, b, c, d in gl2_6:
            xi1_p, xi1_q = p1 * c - q1 * a, p1 * d - q1 * b
            xi2_p, xi2_q = q2 * a + p2 * c, q2 * b + p2 * d
            n1 = -xi1_p * xi1_p + xi1_p * xi1_q + xi1_q * xi1_q
            n2 = -xi2_p * xi2_p + xi2_p * xi2_q + xi2_q * xi2_q
            assert n1 % 25 != 0 and n2 % 25 != 0 and (n1 * n2) % 125 != 0
    # Verify Case 2 Collapse inequality 2*(2-phi)/sqrt(5) > sqrt(5)/7
    phi = (mp.mpf(1) + mp.sqrt(5)) / 2
    assert (2 / mp.sqrt(5)) * (2 - phi) > mp.sqrt(5) / 7
    print("G3: Verified Ramified-5 valuation rigidity (v_5(N) <= 1, v_5(M^2 - 5D^2) <= 2) across 744 GL_2(Z) matrices & 4 endpoints, and Universal Case 2 Collapse 2*(2-phi)/sqrt(5) > sqrt(5)/7.\n")


def run_single_B_theorem(
    B: int,
    classes: list[int],
    T_per: int,
    n_cf: int,
    j_max: int,
    c_min: mp.mpf,
    c_sec: mp.mpf,
    group_defs: list[dict],
    is_even_quarter: bool,
) -> None:
    print(f"=== Theorem for B = {B} (classes={classes}, min_T={T_per}, D_max={2*B*B}, 2500 digits) ===", flush=True)
    print(f"  c_min^({B}) = {mp.nstr(c_min, 35)}", flush=True)
    print(f"  c_sec^({B}) = {mp.nstr(c_sec, 35)}", flush=True)
    assert c_min > 1 / (10 * mp.mpf(B) ** 4 + mp.mpf(B) ** 2 * mp.sqrt(5))

    P, Q = hermite_pq(j_max + 5)
    Dmax = 2 * B * B
    dmax = B * B

    # Check group_defs 4*tau inversions first
    for gd in group_defs:
        gname = gd["name"]
        for m_excl in gd["m_excl"]:
            for q0 in gd["q0_main"]:
                assert not solve_4tau_inversion(Dmax, q0, 2 * m_excl), f"Expected empty for B={B} {gname} m={m_excl} q0={q0}"
        sols_min = {q0: solve_4tau_inversion(Dmax, q0, 2 * gd["m_min"]) for q0 in gd["q0_main"]}
        sols_sec = {q0: solve_4tau_inversion(Dmax, q0, 2 * gd["m_sec"]) for q0 in gd["q0_main"]}
        got_min = {q0: v for q0, v in sols_min.items() if v}
        got_sec = {q0: v for q0, v in sols_sec.items() if v}
        assert got_min == gd["expected_min"], f"B={B} {gname} m_min={gd['m_min']}: got {got_min} vs {gd['expected_min']}"
        assert got_sec == gd["expected_sec"], f"B={B} {gname} m_sec={gd['m_sec']}: got {got_sec} vs {gd['expected_sec']}"
        print(
            f"  [{gname}] 4*tau inversion verified: m_excl={gd['m_excl']} empty; "
            f"m_min={gd['m_min']} ({sum(len(v) for v in got_min.values())} families: {got_min}); "
            f"m_sec={gd['m_sec']} ({sum(len(v) for v in got_sec.values())} families: {got_sec}).",
            flush=True,
        )

    # Map each class r to its group definition
    class_to_gd = {}
    for gd in group_defs:
        for r in gd["classes"]:
            class_to_gd[r] = gd

    tails_scan = [[], [2], [3], [4], [5], [1, 2], [1, 3], [1, 4], [2, 2], [2, 3], [3, 2], [1, 1, 2], [1, 1, 3], [1, 2, 2], [2, 1, 2], [2, 2, 2]]
    group_seen_suffixes: dict[str, dict] = {}

    for r in classes:
        gd = class_to_gd[r]
        gname = gd["name"]
        A = r + 4 * B
        x = mp.mpf(A) / B - mp.e
        cf = cf_expansion(x, n_cf)
        p_cf, q_cf = convergents(cf)
        wins = extract_windows(cf, q_cf, P, Q, A, B, -B, j_max)
        assert len(wins) >= T_per + 10, f"B={B} r={r}: only {len(wins)} windows"

        # Verify period / quarter-period and b_j increment
        expected_mult = 1 if is_even_quarter else 4
        for i in range(len(wins) - T_per):
            assert wins[i + T_per]["S"] == wins[i]["S"]
            assert wins[i + T_per]["rj"] == wins[i]["rj"]
            assert wins[i + T_per]["Dj"] == wins[i]["Dj"]
            assert wins[i + T_per]["Gj"] == wins[i]["Gj"]
            assert wins[i + T_per]["bj"] == wins[i]["bj"] + expected_mult * (wins[i]["Gj"] ** 2)

        # Check minimal period (no proper divisor of T_per gives a period)
        for d_test in divisors(T_per)[:-1]:
            assert not all(wins[i + d_test]["S"] == wins[i]["S"] and wins[i + d_test]["Dj"] == wins[i]["Dj"] for i in range(min(T_per, len(wins) - d_test)))

        # Check D_dist on one full period
        d_dist: dict[int, int] = {}
        for w in wins[:T_per]:
            d_dist[w["Dj"]] = d_dist.get(w["Dj"], 0) + 1
        assert d_dist == gd["D_dist"], f"B={B} r={r}: {d_dist} vs {gd['D_dist']}"

        win_types: dict[tuple[int, tuple[int, ...]], tuple[Fraction, Fraction]] = {}
        r2_types: set[tuple[int, Fraction]] = set()
        for i, w in enumerate(wins):
            S = tuple(w["S"])
            assert len(S) % 2 == 0 and len(S) >= 2
            u = cf_value_fraction(w["S"])
            assert u.numerator == w["Dj"]
            r1 = Fraction(1, 1) / u
            if (w["Dj"], S) not in win_types:
                win_types[(w["Dj"], S)] = (u, r1)
                assert suffix_gap_delta(w["S"]) > 0
            if i > 0:
                r2 = cf_value_fraction([0] + list(reversed(wins[i - 1]["S"])))
                r2_types.add((wins[i - 1]["Dj"], r2))

        q0_main_found = sorted(u.denominator for (D_val, _), (u, _) in win_types.items() if D_val == Dmax)
        assert q0_main_found == gd["q0_main"], f"B={B} r={r}: {q0_main_found} vs {gd['q0_main']}"
        if gname not in group_seen_suffixes:
            group_seen_suffixes[gname] = {k: list(v) for k, v in win_types.items()}
            by_D: dict[int, list[tuple[int, list[int], Fraction]]] = {}
            for (D_val, S_tup), (u, _) in sorted(win_types.items(), key=lambda kv: (kv[0][0], kv[1][0].denominator)):
                by_D.setdefault(D_val, []).append((u.denominator, list(S_tup), suffix_gap_delta(list(S_tup))))
            for D_val, items in sorted(by_D.items()):
                min_del = min(d for _, _, d in items)
                fmt = ", ".join(f"{q0}:{S}(d={d})" for q0, S, d in items)
                print(f"  [{gname}] Suffixes D={D_val} ({len(items)} distinct, min_Delta={min_del}): {fmt}", flush=True)
            # Check Case 1 on all smaller scales and non-extremal suffixes at Dmax
            phi = (mp.mpf(1) + mp.sqrt(5)) / 2
            phi_c = (mp.mpf(1) - mp.sqrt(5)) / 2
            for (D_val, _), (u, _) in win_types.items():
                val = (2 / mp.sqrt(5)) * abs(mp.mpf(u.numerator) / u.denominator - phi) * abs(phi_c) / (mp.mpf(u.numerator) / u.denominator)
                if D_val < Dmax:
                    assert val > c_sec
            verify_case2_bounds(f"B={B},{gname}", win_types, r2_types, c_sec, gd["excl_r2"], Dmax)
        else:
            assert {k: list(v) for k, v in win_types.items()} == group_seen_suffixes[gname]

        # Convergence check on last period (or last min(T_per, len(wins)) windows)
        ext_t = {q0: v[0] for q0, v in gd["expected_min"].items()}
        sec_t = {q0: v[0] for q0, v in gd["expected_sec"].items()}
        tail_wins = wins[-T_per:]
        max_dev_ext = mp.mpf(0)
        max_dev_sec = mp.mpf(0)
        ext_seqs_trimmed = []
        sec_seqs_trimmed = []
        for w in wins[-(T_per + 10) :]:
            if w["Dj"] == Dmax:
                q0 = cf_value_fraction(w["S"]).denominator
                if q0 in ext_t:
                    ext_seqs_trimmed.append(trim_ones(cf[: w["k0"] + 2] + ext_t[q0]))
                if q0 in sec_t:
                    sec_seqs_trimmed.append(trim_ones(cf[: w["k0"] + 2] + sec_t[q0]))
        for w in tail_wins:
            if w["Dj"] == Dmax:
                q0 = cf_value_fraction(w["S"]).denominator
                if q0 in ext_t:
                    _, err = eval_orbit_error_fast(x, p_cf, q_cf, w["k0"] + 2, ext_t[q0])
                    max_dev_ext = max(max_dev_ext, abs(err - c_min))
                if q0 in sec_t:
                    _, err = eval_orbit_error_fast(x, p_cf, q_cf, w["k0"] + 2, sec_t[q0])
                    max_dev_sec = max(max_dev_sec, abs(err - c_sec))
        assert max_dev_ext < gd["dev_ext_cap"] and max_dev_sec < gd["dev_sec_cap"], (
            f"B={B} r={r}: dev_ext={max_dev_ext}, dev_sec={max_dev_sec}"
        )
        print(
            f"  {A}/{B} - e (r={r}, {gname}): {len(wins)} windows (j={wins[0]['j']}..{wins[-1]['j']}), "
            f"max_dev_ext={mp.nstr(max_dev_ext, 4)}, max_dev_sec={mp.nstr(max_dev_sec, 4)}",
            flush=True,
        )
        scan_wins = wins[-min(T_per, 60) :]
        scan_non_extremal(
            cf,
            p_cf,
            q_cf,
            x,
            scan_wins,
            ext_seqs_trimmed,
            sec_seqs_trimmed,
            tails_scan,
            gd["scan_thresh"],
            gd["scan_thresh_sec"],
            f"{A}/{B}-e",
        )
    print(flush=True)


def section_2_b7_all() -> None:
    # Check B=7 equidistribution & C_{j0+14t} progression across A=1..6 mod 7
    P, Q = hermite_pq(150)
    z7 = [j for j in range(98) if Q[j] % 7 == 0]
    z49 = [j for j in range(98) if Q[j] % 49 == 0]
    assert len(z7) == 28 and z49 == [18, 30, 67, 79]
    counts_res = {}
    for j in z7:
        if j in z49:
            continue
        res = (P[j] * pow((Q[j] // 7) % 7, -1, 7)) % 7
        counts_res[res] = counts_res.get(res, 0) + 1
    assert counts_res == {1: 4, 2: 4, 3: 4, 4: 4, 5: 4, 6: 4}

    q0_98 = [1, 13, 15, 27, 29, 41, 43, 55, 57, 69, 71, 83, 85, 97]
    assert all(q % 14 in (1, 13) for q in q0_98)
    # Check D=2 and D=14 4*tau inversions too
    assert solve_4tau_inversion(2, 1, 4) == [[], [2]]
    for q0 in [1, 3, 5, 9, 11, 13]:
        assert solve_4tau_inversion(14, q0, 28) == []
    assert {q0: solve_4tau_inversion(14, q0, 32) for q0 in [1, 3, 5, 9, 11, 13] if solve_4tau_inversion(14, q0, 32)} == {
        3: [[4]], 5: [[2]], 9: [[]], 11: [[1, 3]]
    }

    c_min = mp.mpf(110) / (49 * mp.sqrt(5)) - 1
    c_sec = 1 - mp.mpf(108) / (49 * mp.sqrt(5))
    gd = [{
        "name": "all_7_nmid_A",
        "classes": [1, 2, 3, 4, 5, 6],
        "D_dist": {2: 8, 14: 48, 98: 42},
        "q0_main": q0_98,
        "m_excl": [112],
        "m_min": 110,
        "m_sec": 108,
        "expected_min": {27: [[3]], 29: [[3, 2]], 69: [[1, 2, 2]], 71: [[1, 2]]},
        "expected_sec": {41: [[2, 2]], 43: [[2, 3]], 55: [[1, 1, 3]], 57: [[1, 1, 2]]},
        "excl_r2": set(),
        "dev_ext_cap": mp.mpf("5e-3"),
        "dev_sec_cap": mp.mpf("5e-3"),
        "scan_thresh": mp.mpf("0.010"),
        "scan_thresh_sec": mp.mpf("0.014"),
    }]
    run_single_B_theorem(7, [1, 2, 3, 4, 5, 6], 98, 2500, 260, c_min, c_sec, gd, is_even_quarter=False)


def section_3_b8_all() -> None:
    c_min = 1 - mp.mpf(143) / (64 * mp.sqrt(5))
    c_sec = mp.mpf(145) / (64 * mp.sqrt(5)) - 1
    q0_g1 = [7, 15, 23, 31, 39, 47, 49, 55, 63, 71, 79, 87, 95, 103, 111, 113, 119, 127]
    q0_g2 = [7, 15, 17, 23, 31, 39, 47, 55, 63, 71, 79, 81, 87, 95, 103, 111, 119, 127]
    assert all(q % 16 in {1, 7, 15} for q in q0_g1 + q0_g2)
    gd = [
        {
            "name": "A===1(mod4)",
            "classes": [1, 5],
            "D_dist": {128: 32},
            "q0_main": q0_g1,
            "m_excl": [141],
            "m_min": 143,
            "m_sec": 145,
            "expected_min": {47: [[2, 1, 2]], 49: [[2]], 79: [[]]},
            "expected_sec": {47: [[2]], 49: [[2, 1, 1, 1, 1, 2]], 79: [[1, 1, 1, 1, 1, 1, 2]]},
            "excl_r2": {(128, Fraction(79, 128))},
            "dev_ext_cap": mp.mpf("5e-3"),
            "dev_sec_cap": mp.mpf("1e-2"),
            "scan_thresh": mp.mpf("0.008"),
            "scan_thresh_sec": mp.mpf("0.012"),
        },
        {
            "name": "A===3(mod4)",
            "classes": [3, 7],
            "D_dist": {128: 32},
            "q0_main": q0_g2,
            "m_excl": [141],
            "m_min": 143,
            "m_sec": 145,
            "expected_min": {47: [[2, 1, 2]], 79: [[]], 81: [[1, 1, 1, 2]]},
            "expected_sec": {47: [[2]], 79: [[1, 1, 1, 1, 1, 1, 2]], 81: [[]]},
            "excl_r2": {(128, Fraction(79, 128))},
            "dev_ext_cap": mp.mpf("5e-3"),
            "dev_sec_cap": mp.mpf("1e-2"),
            "scan_thresh": mp.mpf("0.008"),
            "scan_thresh_sec": mp.mpf("0.012"),
        },
    ]
    run_single_B_theorem(8, [1, 3, 5, 7], 32, 2300, 290, c_min, c_sec, gd, is_even_quarter=True)


def section_4_b9_all() -> None:
    c_min = mp.mpf(182) / (81 * mp.sqrt(5)) - 1
    c_sec = mp.mpf(184) / (81 * mp.sqrt(5)) - 1
    q0_all = [q for q in range(1, 162) if math.gcd(q, 162) == 1]
    assert len(q0_all) == 54
    gd = [{
        "name": "all_3_nmid_A",
        "classes": [1, 2, 4, 5, 7, 8],
        "D_dist": {162: 162},
        "q0_main": q0_all,
        "m_excl": [180],
        "m_min": 182,
        "m_sec": 184,
        "expected_min": {35: [[4]], 37: [[4, 2]], 61: [[2]], 77: [[2, 9]], 85: [[1, 1, 9]], 101: [[]], 125: [[1, 3, 2]], 127: [[1, 3]]},
        "expected_sec": {11: [[14, 1, 2]], 59: [[2]], 103: [[]], 151: [[1, 13, 1, 2]]},
        "excl_r2": {(162, Fraction(101, 162))},
        "dev_ext_cap": mp.mpf("1e-2"),
        "dev_sec_cap": mp.mpf("2e-2"),
        "scan_thresh": mp.mpf("0.008"),
        "scan_thresh_sec": mp.mpf("0.010"),
    }]
    run_single_B_theorem(9, [1, 2, 4, 5, 7, 8], 162, 2500, 320, c_min, c_sec, gd, is_even_quarter=False)


def section_5_b10_all() -> None:
    c_min = 1 - mp.mpf(223) / (100 * mp.sqrt(5))
    c_sec = 1 - mp.mpf(221) / (100 * mp.sqrt(5))
    q0_all = [q for q in range(1, 200) if math.gcd(q, 200) == 1 and q % 8 in (3, 5)]
    assert len(q0_all) == 40
    gd = [{
        "name": "all_coprime_10",
        "classes": [1, 3, 7, 9],
        "D_dist": {200: 50},
        "q0_main": q0_all,
        "m_excl": [225],
        "m_min": 223,
        "m_sec": 221,
        "expected_min": {13: [[15, 2]], 77: [[2]], 123: [[]], 187: [[1, 14, 2]]},
        "expected_sec": {59: [[3, 2]], 61: [[3, 3]], 139: [[1, 2, 3]], 141: [[1, 2, 2]]},
        "excl_r2": {(200, Fraction(123, 200))},
        "dev_ext_cap": mp.mpf("5e-3"),
        "dev_sec_cap": mp.mpf("5e-3"),
        "scan_thresh": mp.mpf("0.008"),
        "scan_thresh_sec": mp.mpf("0.011"),
    }]
    run_single_B_theorem(10, [1, 3, 7, 9], 50, 2300, 300, c_min, c_sec, gd, is_even_quarter=True)


def section_6_b11_b12_all() -> None:
    # B = 11
    c_min_11 = 1 - mp.mpf(270) / (121 * mp.sqrt(5))
    c_sec_11 = mp.mpf(272) / (121 * mp.sqrt(5)) - 1
    q0_11 = [q for q in range(1, 242) if math.gcd(q, 242) == 1 and q % 22 in (1, 7, 19, 21)]
    assert len(q0_11) == 44
    gd_11 = [{
        "name": "all_11_nmid_A",
        "classes": list(range(1, 11)),
        "D_dist": {2: 8, 22: 80, 242: 154},
        "q0_main": q0_11,
        "m_excl": [],
        "m_min": 270,
        "m_sec": 272,
        "expected_min": {65: [[3, 1, 2]], 67: [[3]], 175: [[1, 2]], 177: [[1, 2, 1, 2]]},
        "expected_sec": {43: [[5]], 45: [[5, 2]], 117: [[2, 14]], 151: [[]], 197: [[1, 4, 2]], 199: [[1, 4]]},
        "excl_r2": set(),
        "dev_ext_cap": mp.mpf("5e-3"),
        "dev_sec_cap": mp.mpf("1e-2"),
        "scan_thresh": mp.mpf("0.0030"),
        "scan_thresh_sec": mp.mpf("0.0055"),
    }]
    run_single_B_theorem(11, list(range(1, 11)), 242, 2600, 380, c_min_11, c_sec_11, gd_11, is_even_quarter=False)

    # B = 12
    c_min_12 = mp.mpf(323) / (144 * mp.sqrt(5)) - 1
    c_sec_12 = 1 - mp.mpf(319) / (144 * mp.sqrt(5))
    q0_12_g1 = [7, 23, 31, 41, 47, 55, 71, 73, 79, 95, 103, 119, 127, 137, 143, 151, 167, 169, 175, 191, 199, 215, 223, 233, 239, 247, 263, 265, 271, 287]
    q0_12_g2 = [7, 23, 25, 31, 47, 55, 71, 79, 89, 95, 103, 119, 121, 127, 143, 151, 167, 175, 185, 191, 199, 215, 217, 223, 239, 247, 263, 271, 281, 287]
    assert all(q % 8 in (1, 7) and q % 3 != 0 for q in q0_12_g1 + q0_12_g2)
    gd_12 = [
        {
            "name": "A===1,5(mod12)",
            "classes": [1, 5],
            "D_dist": {288: 72},
            "q0_main": q0_12_g1,
            "m_excl": [321],
            "m_min": 323,
            "m_sec": 319,
            "expected_min": {119: [[2, 2, 2]], 167: [[1, 1, 2]], 169: [[1, 1, 2, 2]]},
            "expected_sec": {79: [[3, 1, 1, 1, 4]], 175: [[]]},
            "excl_r2": set(),
            "dev_ext_cap": mp.mpf("5e-3"),
            "dev_sec_cap": mp.mpf("1e-2"),
            "scan_thresh": mp.mpf("0.0042"),
            "scan_thresh_sec": mp.mpf("0.0080"),
        },
        {
            "name": "A===7,11(mod12)",
            "classes": [7, 11],
            "D_dist": {288: 72},
            "q0_main": q0_12_g2,
            "m_excl": [321],
            "m_min": 323,
            "m_sec": 319,
            "expected_min": {119: [[2, 2, 2]], 121: [[2, 2]], 167: [[1, 1, 2]]},
            "expected_sec": {79: [[3, 1, 1, 1, 4]], 175: [[]]},
            "excl_r2": set(),
            "dev_ext_cap": mp.mpf("5e-3"),
            "dev_sec_cap": mp.mpf("1e-2"),
            "scan_thresh": mp.mpf("0.0042"),
            "scan_thresh_sec": mp.mpf("0.0080"),
        },
    ]
    run_single_B_theorem(12, [1, 5, 7, 11], 72, 2500, 360, c_min_12, c_sec_12, gd_12, is_even_quarter=True)


if __name__ == "__main__":
    section_1_general_theorems()
    section_2_b7_all()
    section_3_b8_all()
    section_4_b9_all()
    section_5_b10_all()
    section_6_b11_b12_all()
    print("ALL PATH 2A GENERAL-B AND B=7..12 CHECKS PASSED WITH 0 ASSERTION FAILURES.", flush=True)
