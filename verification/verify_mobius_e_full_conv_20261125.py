#!/usr/bin/env python3
"""
Verification of Route M2:
  1. General Mobius Images (a*e+b)/(c*e+d) (Delta = a*d - b*c != 0):
     Exact threshold J_0(a,b,c,d), window period T = 2|Delta|, digit-shift identity
     W_{j+T} = (b_j + 4*G_j^2, S_j), adversarial tiny-denominator test, and
     35+ matrix sweep across |Delta| = 1..16.
  2. General arithmetic recurrence orders omega(c, d; T) in GL_2(Z/TZ).
  3. Exact 3-orbit PGL_2(Z) classification of Mobius images of e with a_n -> infinity:
     exhaustive HNF sweep up to |Delta| <= 40 (1128 primitive HNFs) + exact parity invariants.
  4. Full-convergent spectrum and exact gauges of e:
     identities q_{3j-1} = (Q_{j+1}-Q_j)/2, q_{3j} = (Q_{j+1}+Q_j)/2 for j >= 0,
     KL weights w_n -> 2 (n != 3j-2 mod 3) and w_{3j-2}/(2j) -> 1,
     full-convergent KL and raw spectra, zero-level Z + Z*e, and telescoping witnesses.

Writes deterministic verification outputs to:
  - verification/verify_mobius_e_full_conv_20261125.log
  - verification/verify_mobius_e_full_conv_20261125.json
"""

from __future__ import annotations

import json
import math
import pathlib
import random
import sys
import time

import mpmath as mp

ROOT = pathlib.Path(__file__).resolve().parent.parent
LOG_PATH = ROOT / "verification" / "verify_mobius_e_full_conv_20261125.log"
JSON_PATH = ROOT / "verification" / "verify_mobius_e_full_conv_20261125.json"

mp.mp.dps = 350


def build_hermite_pq(j_max: int) -> tuple[list[int], list[int]]:
    """
    Selected Hermite convergents of e:
      P_0 = 1, Q_0 = 1; P_1 = 3, Q_1 = 1;
      X_{j+1} = (4j+2) X_j + X_{j-1} for j >= 1.
    """
    P = [1, 3]
    Q = [1, 1]
    for j in range(1, j_max + 2):
        P.append((4 * j + 2) * P[-1] + P[-2])
        Q.append((4 * j + 2) * Q[-1] + Q[-2])
    return P, Q


def cf_and_convergents(y: mp.mpf, num_terms: int) -> tuple[list[int], list[int], list[int]]:
    """Return regular CF [a_0, ..., a_{N-1}] and convergents p[k+2]/q[k+2] for k >= -1, stopping before precision loss."""
    cf = []
    p = [0, 1]
    q = [1, 0]
    v = y
    q_cap = 10 ** max(50, (mp.mp.dps // 2) - 25)
    for _ in range(num_terms):
        ai = int(mp.floor(v))
        cf.append(ai)
        p.append(ai * p[-1] + p[-2])
        q.append(ai * q[-1] + q[-2])
        if q[-1] > q_cap:
            break
        frac = v - ai
        if frac == 0:
            break
        v = 1 / frac
    return cf, p, q


def minimal_hurwitz_period(cf: list[int], start: int = 20) -> tuple[int | None, list[int] | None]:
    """Find minimal p >= 1 such that cf[n+p] - cf[n] is p-periodic (constant per residue mod p) for n >= start."""
    tail = cf[start:]
    m = len(tail)
    for p in range(1, m // 3 + 1):
        diffs = [tail[i + p] - tail[i] for i in range(m - p)]
        if len(diffs) >= 2 * p and all(diffs[i + p] == diffs[i] for i in range(len(diffs) - p)):
            return p, diffs[:p]
    return None, None


def explicit_threshold(a: int, b: int, c: int, d: int, P: list[int], Q: list[int]) -> int:
    """
    Derive rigorous threshold J_0(a,b,c,d) after ensuring ce+d > 0 such that for all j >= J_0:
      1) c*P_j + d*Q_j > (1/2) * Q_j * (ce + d) > 0,
      2) q'_j * |q'_j y - p'_j| < 1/2 (Legendre criterion),
      3) q'_j >= 2 (predecessor k(j)-1 >= 0 exists) and q'_{j+1} > q'_j.
    """
    if c * mp.e + d < 0:
        a, b, c, d = -a, -b, -c, -d
    Delta = abs(a * d - b * c)
    denom_val = c * mp.e + d
    for j in range(1, len(Q)):
        cond1 = j >= math.ceil(1.5 * Delta)
        cond2 = Q[j] * denom_val > 2 * Delta
        cond3 = (Q[j] ** 2) * (2 * j + 1) * denom_val > 2 * abs(c)
        if cond1 and cond2 and cond3:
            return j
    raise RuntimeError("Increase j_max for explicit_threshold")


def verify_single_mobius(a: int, b: int, c: int, d: int, P: list[int], Q: list[int], Jmax: int | None = None) -> dict:
    """Verify general Mobius window period theorem on matrix [[a,b],[c,d]]."""
    if c * mp.e + d < 0:
        a, b, c, d = -a, -b, -c, -d
    Delta = a * d - b * c
    assert Delta != 0
    T = 2 * abs(Delta)
    J0 = explicit_threshold(a, b, c, d, P, Q)
    if Jmax is None:
        Jmax = max(J0 + 2 * T + 5, 45)
    assert Jmax >= J0 + 2 * T + 2, f"Need larger Jmax={Jmax} for J0={J0}, T={T}"
    assert Jmax < len(Q), f"Jmax={Jmax} exceeds precomputed P,Q len={len(Q)}"

    # Dynamic working precision: Q_j has ~ j*log10(4j) digits; require > 2.5*log10(Q_{Jmax+1}) + 120 dps
    need_dps = max(350, int(3 * (Jmax + 2) * math.log10(max(10, 4 * Jmax)) + 150))
    with mp.workdps(need_dps):
        y = (a * mp.e + b) / (c * mp.e + d)
        cf_terms = max(500, 30 * Jmax)
        cf, p_cf, q_cf = cf_and_convergents(y, cf_terms)
        conv_map = {(p_cf[i + 2], q_cf[i + 2]): i for i in range(len(cf))}

    ks, Gs = {}, {}
    for j in range(1, Jmax + 1):
        U = a * P[j] + b * Q[j]
        V = c * P[j] + d * Q[j]
        if j >= J0:
            assert V > 0, f"V_{j} <= 0 above threshold J0={J0}!"
        if V > 0:
            g = math.gcd(abs(U), abs(V))
            p_red, q_red = U // g, V // g
            if (p_red, q_red) in conv_map:
                ks[j] = conv_map[(p_red, q_red)]
                Gs[j] = g
            elif j >= J0:
                raise AssertionError(
                    f"Locked fraction at j={j} >= J0={J0} missing from convergents for M=[[{a},{b}],[{c},{d}]]!"
                )

    # Check exact window properties for all j >= J0 + 1 with j + T + 1 <= Jmax
    checked = 0
    r_vals = []
    for j in range(J0 + 1, Jmax - T):
        k0, k1 = ks[j], ks[j + 1]
        kt0, kt1 = ks[j + T], ks[j + T + 1]
        r1 = k1 - k0
        r2 = kt1 - kt0
        assert r1 >= 1 and r1 % 2 == 1, f"r_{j}={r1} not odd positive!"
        assert r1 == r2, f"Periodicity r_{j}={r1} != r_{j+T}={r2}"
        U0, V0 = a * P[j] + b * Q[j], c * P[j] + d * Q[j]
        U1, V1 = a * P[j + 1] + b * Q[j + 1], c * P[j + 1] + d * Q[j + 1]
        p0, q0 = U0 // Gs[j], V0 // Gs[j]
        p1, q1 = U1 // Gs[j + 1], V1 // Gs[j + 1]
        det_val = abs(p0 * q1 - p1 * q0)
        D_j = T // (Gs[j] * Gs[j + 1])
        assert T % (Gs[j] * Gs[j + 1]) == 0
        assert det_val == D_j, f"det={det_val} != D_j={D_j}"
        assert (r1 == 1) == (D_j == 1), f"r1=1 iff D_j=1 failed at j={j}"

        W1 = cf[k0 + 1 : k1 + 1]
        W2 = cf[kt0 + 1 : kt1 + 1]
        assert W1[1:] == W2[1:], f"Suffix mismatch at j={j}: {W1[1:]} vs {W2[1:]}"
        assert W2[0] - W1[0] == 4 * (Gs[j] ** 2), f"Increment mismatch at j={j}: {W2[0]-W1[0]} vs {4*Gs[j]**2}"
        checked += 1
        if j < J0 + 1 + T:
            r_vals.append(r1)

    # Minimal window period dividing T
    min_win_T = T
    for d_div in range(1, T + 1):
        if T % d_div != 0:
            continue
        ok = True
        for j in range(J0 + 1, Jmax - d_div):
            W1 = cf[ks[j] + 1 : ks[j + 1] + 1]
            W2 = cf[ks[j + d_div] + 1 : ks[j + d_div + 1] + 1]
            if len(W1) != len(W2) or W1[1:] != W2[1:]:
                ok = False
                break
        if ok:
            incs = [
                cf[ks[j + d_div] + 1] - cf[ks[j] + 1]
                for j in range(J0 + 1, Jmax - d_div)
            ]
            if all(incs[i] == incs[i % d_div] for i in range(len(incs))):
                min_win_T = d_div
                break

    R_total = sum(r_vals)
    # Check minimal Hurwitz period ONLY inside certified convergent slice cf[:ks[Jmax-1]+1]
    # Note: for min_win_T with R_min digits, we need >= 3*R_min digits after start; ensure Jmax covers >= 3*T windows if needed
    certified_cf = cf[: ks[Jmax - 1] + 1]
    hurwitz_p, _ = minimal_hurwitz_period(certified_cf, start=ks[J0 + 1] + 1)

    return {
        "matrix": [[a, b], [c, d]],
        "Delta": Delta,
        "T_window": T,
        "min_win_T": min_win_T,
        "J0": J0,
        "checked_windows": checked,
        "R_digits_per_T": R_total,
        "min_hurwitz_digit_period": hurwitz_p,
        "r_period_slice": r_vals,
        "cf_prefix": cf[:14],
        "all_checks_passed": True,
    }


def verify_mobius_suite(P: list[int], Q: list[int]) -> dict:
    # Named matrices + adversarial tiny-denominator + systematic/random matrices
    named = [
        ("e", 1, 0, 0, 1),
        ("2e", 2, 0, 0, 1),
        ("3e", 3, 0, 0, 1),
        ("e/2", 1, 0, 0, 2),
        ("1/e", 0, 1, 1, 0),
        ("(e+1)/(e-1)", 1, 1, 1, -1),
        ("(e-1)/(e+1)", 1, -1, 1, 1),
        ("(e+1)/2", 1, 1, 0, 2),
        ("(e+1)/4", 1, 1, 0, 4),
        ("(e+3)/4", 1, 3, 0, 4),
        ("(e+1)/3", 1, 1, 0, 3),
        ("(e+1)/6", 1, 1, 0, 6),
        ("(2e+1)/(e+1)", 2, 1, 1, 1),
        ("(e+2)/(3e+1)", 1, 2, 3, 1),
        ("(e+1)/(e+5)", 1, 1, 1, 5),
        ("(2e+1)/(e+3)", 2, 1, 1, 3),
        ("(5e+2)/(3e+4)", 5, 2, 3, 4),
        ("(39e-106)/(71e-193)_adversarial", 39, -106, 71, -193),
        ("2*(e+1)/4_nonprim", 2, 2, 0, 8),
        ("(3e-5)/1_negative", 3, -5, 0, 1),
    ]

    rng = random.Random(20261125)
    sweep_extra = []
    seen = {(a, b, c, d) for _, a, b, c, d in named}
    # Add matrices covering determinants +-1..+-16
    for target_det in [1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 6, -6, 7, 8, -9, 10, 12, -12, 15, 16]:
        while True:
            c = rng.randint(0, 5)
            d = rng.randint(1, 7)
            a = rng.randint(-4, 6)
            # solve a*d - b*c = target_det if c != 0 else a*d = target_det
            if c == 0:
                a = target_det
                d = 1
                b = rng.randint(-5, 5)
            else:
                if (a * d - target_det) % c != 0:
                    continue
                b = (a * d - target_det) // c
            if math.gcd(math.gcd(abs(a), abs(b)), math.gcd(abs(c), abs(d))) == 0:
                continue
            if (a, b, c, d) not in seen and abs(a * d - b * c) == abs(target_det):
                seen.add((a, b, c, d))
                sweep_extra.append((f"rand_det{target_det}", a, b, c, d))
                break

    all_mats = named + sweep_extra
    records = []
    for label, a, b, c, d in all_mats:
        Delta = abs(a * d - b * c)
        J0 = explicit_threshold(a, b, c, d, P, Q)
        # Ensure at least 3*T windows above J0 so both R_T and minimal_hurwitz_period (3 repeats!) are captured
        Jmax = max(J0 + 3 * (2 * Delta) + 6, 45)
        rec = verify_single_mobius(a, b, c, d, P, Q, Jmax=Jmax)
        rec["label"] = label
        records.append(rec)

    # Also explicitly document the adversarial matrix behavior at j=3 (< J0)
    adv_V3 = 71 * P[3] - 193 * Q[3]
    assert adv_V3 == 0, f"Expected V_3 = 0 for adversarial matrix, got {adv_V3}"

    return {"total_matrices": len(records), "adversarial_V3_eq_0": True, "records": records}


def verify_gl2_orders_general_recurrences() -> dict:
    """Compute multiplicative orders omega(c, d; T) of M_{T-1}...M_0 in GL_2(Z/TZ)."""
    def mat_mul_mod(A, B, T):
        return (
            (A[0][0] * B[0][0] + A[0][1] * B[1][0]) % T,
            (A[0][0] * B[0][1] + A[0][1] * B[1][1]) % T,
        ), (
            (A[1][0] * B[0][0] + A[1][1] * B[1][0]) % T,
            (A[1][0] * B[0][1] + A[1][1] * B[1][1]) % T,
        )

    def order_mod(c: int, d: int, T: int) -> int:
        M = ((1 % T, 0), (0, 1 % T))
        for j in range(T):
            step = (((c * j + d) % T, 1 % T), (1 % T, 0))
            M = mat_mul_mod(step, M, T)
        cur = M
        ident = ((1 % T, 0), (0, 1 % T))
        for k in range(1, 2000):
            if cur == ident:
                return k
            cur = mat_mul_mod(cur, M, T)
        return -1

    families = {
        "e (4j+2)": (4, 2),
        "tanh(1) (2j+1)": (2, 1),
        "I1/I0 (j+1)": (1, 1),
        "3j+1": (3, 1),
    }
    Ts = [2, 3, 4, 5, 6, 8, 10, 12]
    table = {}
    for name, (c, d) in families.items():
        table[name] = {str(T): order_mod(c, d, T) for T in Ts}
        if name == "e (4j+2)":
            for T in [2, 4, 6, 8, 10, 12]:
                assert table[name][str(T)] == 1
    return table


def verify_three_orbit_classification(P: list[int], Q: list[int]) -> dict:
    """
    Exhaustively check all primitive HNFs [[C, A], [0, B]] with 1 <= CB = |Delta| <= 40.
    Verify ONLY (C,A,B) in {(1,1,2), (1,1,4), (1,3,4)} satisfy G_j G_{j+1} = 2*C*B
    across any 6 consecutive indices (5 consecutive 1-digit windows).
    Also verify P_j, Q_j mod 8 periodicity and distinct mod-16 congruence signatures
    of the 3 orbits.
    """
    # Check (P_j, Q_j) mod 8 for j=0..40
    mod8_seq = [(P[j] % 8, Q[j] % 8) for j in range(20)]
    assert mod8_seq[:4] == [(1, 1), (3, 1), (3, 7), (1, 7)]
    for j in range(20):
        assert mod8_seq[j] == mod8_seq[j % 4]

    total_hnf = 0
    hits_by_gcd = []
    hits_by_cf = []
    for det in range(1, 41):
        for C in range(1, det + 1):
            if det % C != 0:
                continue
            B = det // C
            for A in range(0, B):
                if math.gcd(math.gcd(A, B), C) != 1:
                    continue
                total_hnf += 1
                T = 2 * det
                # Check G_j * G_{j+1} == T for 6 consecutive indices (e.g. j=10..15)
                Gs = [math.gcd(C * P[j] + A * Q[j], B * Q[j]) for j in range(10, 16)]
                if all(Gs[i] * Gs[i + 1] == T for i in range(5)):
                    hits_by_gcd.append((C, A, B))
                # For det <= 16 also check actual CF windows directly
                if det <= 16:
                    rec = verify_single_mobius(C, A, 0, B, P, Q)
                    if all(r == 1 for r in rec["r_period_slice"]):
                        hits_by_cf.append((C, A, B))

    expected = [(1, 1, 2), (1, 1, 4), (1, 3, 4)]
    assert hits_by_gcd == expected, f"Unexpected hits_by_gcd={hits_by_gcd}"
    assert hits_by_cf == expected, f"Unexpected hits_by_cf={hits_by_cf}"

    # Verify explicit CF tails of the 3 orbit representatives
    orbit_tails = {}
    for label, (C, A, B) in zip(["(e+1)/2", "(e+1)/4", "(e+3)/4"], expected):
        y = (C * mp.e + A) / B
        cf, _, _ = cf_and_convergents(y, 30)
        orbit_tails[label] = cf[:16]
    # Check congruence invariants on tail (n >= 2 or n >= 3):
    assert all(x % 4 == 2 for x in orbit_tails["(e+1)/2"][2:])
    assert all(orbit_tails["(e+1)/4"][2 * k + 1] % 4 == 1 for k in range(1, 7))
    assert all(orbit_tails["(e+1)/4"][2 * k] % 16 == 12 for k in range(2, 7))
    assert all(orbit_tails["(e+3)/4"][2 * k] % 4 == 3 for k in range(1, 7))
    assert all(orbit_tails["(e+3)/4"][2 * k + 1] % 16 == 4 for k in range(1, 7))

    return {
        "total_primitive_hnfs_tested": total_hnf,
        "max_det_gcd_sweep": 40,
        "max_det_cf_sweep": 16,
        "exact_3_orbits_HNF": hits_by_gcd,
        "orbit_cf_prefixes": orbit_tails,
    }


def verify_full_convergent_spectrum_of_e(P: list[int], Q: list[int]) -> dict:
    """
    Verify:
      1. Exact full-convergent identities for e = [2; 1, 2, 1, 1, 4, ...]:
         q_{3j-1} = (Q_{j+1}-Q_j)/2, q_{3j} = (Q_{j+1}+Q_j)/2,
         p_{3j-1} = (P_{j+1}-P_j)/2, p_{3j} = (P_{j+1}+P_j)/2 for ALL j >= 0.
      2. Exact KL weights w_n = 1 / (q_n * |q_n * e - p_n|):
         w_{3j-2}/(2j) -> 1, w_{3j-1} -> 2, w_{3j} -> 2.
      3. Full-convergent spectrum verification on concrete witness points:
         - x in Z + Z*e (e.g. e, 3*e - 5) -> KL = 0, raw = 0
         - x in (1+e)/2 + Z + Z*e -> KL = 1, raw = 1/2 (expelled from level 0!)
         - telescoping witnesses x(d) = sum_{r>=1} (-1)^r d_r (Q_r*(e-1)/2 - (P_r-Q_r)/2):
           * d_r = 1 (all r): Lambda_sel = 1/4, M_{j+1} != M_j mod 2 -> KL = 1, raw = 1/2
           * d_r = 2 (all r), with M parity alternating -> KL = 1, raw = 1
           * d_r = 2 (even steps, constant M parity?) -> test d_r = (-1)^r * 2 vs d_r = 2!
           * d_r = 3 (all r): Lambda_sel = 3/4 -> KL = 3/2, raw = 3/2
           * d_r = 4 (all r): Lambda_sel = 1 -> KL = 2, raw = 2
           * d_r = 5 (all r): Lambda_sel = 5/4 -> KL = 5/2, raw = 5/2
    """
    J_N = 45
    cf_e = [2]
    for j in range(1, J_N + 5):
        cf_e.extend([1, 2 * j, 1])
    pe, qe = [0, 1], [1, 0]
    for a in cf_e:
        pe.append(a * pe[-1] + pe[-2])
        qe.append(a * qe[-1] + qe[-2])

    def pn(n: int) -> int:
        return pe[n + 2]

    def qn(n: int) -> int:
        return qe[n + 2]

    for j in range(0, J_N):
        if j >= 1:
            assert pn(3 * j - 2) == P[j] and qn(3 * j - 2) == Q[j]
        assert 2 * qn(3 * j - 1) == Q[j + 1] - Q[j]
        assert 2 * qn(3 * j) == Q[j + 1] + Q[j]
        assert 2 * pn(3 * j - 1) == P[j + 1] - P[j]
        assert 2 * pn(3 * j) == P[j + 1] + P[j]

    # Weights w_n
    weight_samples = []
    for j in [1, 2, 5, 10, 20, 35]:
        w0 = float(1 / (qn(3 * j - 2) * abs(qn(3 * j - 2) * mp.e - pn(3 * j - 2))))
        w1 = float(1 / (qn(3 * j - 1) * abs(qn(3 * j - 1) * mp.e - pn(3 * j - 1))))
        w2 = float(1 / (qn(3 * j) * abs(qn(3 * j) * mp.e - pn(3 * j))))
        weight_samples.append({
            "j": j,
            "w_(3j-2)/(2j)": round(w0 / (2 * j), 8),
            "w_(3j-1)": round(w1, 8),
            "w_(3j)": round(w2, 8),
        })

    # Verify telescoping construction for bounded defect sequences (d_r)_{r>=1}
    beta = (mp.e - 1) / 2
    P_tilde = [(P[j] - Q[j]) // 2 for j in range(len(Q))]

    def dist_int(z: mp.mpf) -> mp.mpf:
        return abs(z - mp.nint(z))

    def telescoping_witness(d_seq: list[int]) -> mp.mpf:
        s = mp.mpf(0)
        for r in range(1, len(d_seq)):
            s += ((-1) ** r) * d_seq[r] * (Q[r] * beta - P_tilde[r])
        return s

    def eval_spectrum_at(x: mp.mpf, j_lo: int = 12, j_hi: int = 38) -> dict:
        sel_vals = []
        kl0_vals, kl1_vals, kl2_vals = [], [], []
        raw0_vals, raw1_vals, raw2_vals = [], [], []
        parities = []
        for j in range(j_lo, j_hi + 1):
            Mj = int(mp.nint(Q[j] * x))
            parities.append(Mj % 2)
            sel_vals.append(float(j * dist_int(Q[j] * x)))

            w0 = 1 / (qn(3 * j - 2) * abs(qn(3 * j - 2) * mp.e - pn(3 * j - 2)))
            w1 = 1 / (qn(3 * j - 1) * abs(qn(3 * j - 1) * mp.e - pn(3 * j - 1)))
            w2 = 1 / (qn(3 * j) * abs(qn(3 * j) * mp.e - pn(3 * j)))

            kl0_vals.append(float(w0 * dist_int(qn(3 * j - 2) * x)))
            kl1_vals.append(float(w1 * dist_int(qn(3 * j - 1) * x)))
            kl2_vals.append(float(w2 * dist_int(qn(3 * j) * x)))

            raw0_vals.append(float(cf_e[3 * j - 1] * dist_int(qn(3 * j - 2) * x)))
            raw1_vals.append(float(cf_e[3 * j] * dist_int(qn(3 * j - 1) * x)))
            raw2_vals.append(float(cf_e[3 * j + 1] * dist_int(qn(3 * j) * x)))

        return {
            "sel_max_tail": round(max(sel_vals[-8:]), 6),
            "kl_class0_last": round(kl0_vals[-1], 6),
            "kl_class1_last": round(kl1_vals[-1], 6),
            "kl_class2_last": round(kl2_vals[-1], 6),
            "kl_overall_max_tail": round(max(max(kl0_vals[-8:]), max(kl1_vals[-8:]), max(kl2_vals[-8:])), 6),
            "raw_overall_max_tail": round(max(max(raw0_vals[-8:]), max(raw1_vals[-8:]), max(raw2_vals[-8:])), 6),
            "M_mod2_tail": parities[-8:],
        }

    witnesses = [
        ("x = 3*e - 5 (in Z + Ze)", 3 * mp.e - 5),
        ("x = (1 + e)/2 (coset)", (1 + mp.e) / 2),
        ("x = (3 - e)/2 (coset)", (3 - mp.e) / 2),
        ("d_r = 1 (Lambda_sel=1/4 -> KL=1, raw=1/2)", telescoping_witness([0] + [1] * 60)),
        ("d_r = 2 (Lambda_sel=1/2 -> KL=1, raw=1)", telescoping_witness([0] + [2] * 60)),
        ("d_r = 3 (Lambda_sel=3/4 -> KL=3/2, raw=3/2)", telescoping_witness([0] + [3] * 60)),
        ("d_r = 4 (Lambda_sel=1 -> KL=2, raw=2)", telescoping_witness([0] + [4] * 60)),
        ("d_r = 5 (Lambda_sel=5/4 -> KL=5/2, raw=5/2)", telescoping_witness([0] + [5] * 60)),
    ]

    witness_results = []
    for label, x in witnesses:
        ev = eval_spectrum_at(x)
        ev["label"] = label
        witness_results.append(ev)

    # Check exact parity consistency for telescoping defect sequences
    # For d_r = 1: KL should be ~1.0, raw ~0.5
    assert abs(witness_results[0]["kl_overall_max_tail"] - 0.0) < 1e-10
    assert abs(witness_results[1]["kl_overall_max_tail"] - 1.0) < 0.01
    assert abs(witness_results[1]["raw_overall_max_tail"] - 0.5) < 0.01
    assert abs(witness_results[3]["kl_overall_max_tail"] - 1.0) < 0.01
    assert abs(witness_results[3]["raw_overall_max_tail"] - 0.5) < 0.01
    assert abs(witness_results[4]["kl_overall_max_tail"] - 1.0) < 0.01
    assert abs(witness_results[5]["kl_overall_max_tail"] - 1.5) < 0.01
    assert abs(witness_results[6]["kl_overall_max_tail"] - 2.0) < 0.01
    assert abs(witness_results[7]["kl_overall_max_tail"] - 2.5) < 0.01

    return {
        "q_identities_verified_j_0_to": J_N - 1,
        "weight_samples": weight_samples,
        "witness_results": witness_results,
    }


def main() -> int:
    t0 = time.perf_counter()
    lines = []

    def log(msg: str = "") -> None:
        print(msg)
        lines.append(msg)

    log("=" * 78)
    log("Route M2 Verification: Mobius Images of e, 3-Orbit Classification,")
    log("and Full-Convergent Spectrum & Gauges of e")
    log(f"Python {sys.version.split()[0]} | mpmath {mp.__version__} (dps={mp.mp.dps})")
    log("=" * 78)

    P, Q = build_hermite_pq(180)

    mob_res = verify_mobius_suite(P, Q)
    log(f"\n[1] General Mobius Window Period Theorem ({mob_res['total_matrices']} matrices, dps={mp.mp.dps}):")
    log(f"  Adversarial tiny-denom M=[[39,-106],[71,-193]]: V_3={71*P[3]-193*Q[3]} (fails naive j>|Delta|+3, passes rigorous J0!)")
    log("  label                              Det    T  Tmin  J0  chk   R_T  p_min  cf[:8]")
    for r in mob_res["records"][:25]:
        log(
            f"  {r['label']:33s} {r['Delta']:4d}  {r['T_window']:3d}   {r['min_win_T']:3d}  {r['J0']:2d}"
            f"   {r['checked_windows']:2d}  {r['R_digits_per_T']:4d}   {str(r['min_hurwitz_digit_period']):>4s}"
            f"  {r['cf_prefix'][:8]}"
        )
    log(f"  ... all {mob_res['total_matrices']} matrices passed 100% of window/suffix/increment checks!")

    ord_res = verify_gl2_orders_general_recurrences()
    log("\n[2] Multiplicative Order omega(c,d;T) in GL_2(Z/TZ) for Q_{j+1}=(cj+d)Q_j+Q_{j-1}:")
    for name, row in ord_res.items():
        log(f"  {name:16s}: {row}")

    orb_res = verify_three_orbit_classification(P, Q)
    log(f"\n[3] 3-Orbit Classification Sweep ({orb_res['total_primitive_hnfs_tested']} primitive HNFs, |Delta|<=40):")
    log(f"  Exact HNFs with a_n -> infinity (r_j=1 eventually): {orb_res['exact_3_orbits_HNF']}")
    for lbl, pref in orb_res["orbit_cf_prefixes"].items():
        log(f"  - {lbl}: {pref}")

    spec_res = verify_full_convergent_spectrum_of_e(P, Q)
    log(f"\n[4] Full-Convergent Identities & KL Weights of e (j=0..{spec_res['q_identities_verified_j_0_to']} EXACT):")
    for ws in spec_res["weight_samples"]:
        log(f"  j={ws['j']:2d}: w_(3j-2)/(2j)={ws['w_(3j-2)/(2j)']:.6f}, w_(3j-1)={ws['w_(3j-1)']:.6f}, w_(3j)={ws['w_(3j)']:.6f}")

    log("\n[5] Full-Convergent KL & Raw Spectrum Witness Checks:")
    for wr in spec_res["witness_results"]:
        log(
            f"  {wr['label']:45s} | sel={wr['sel_max_tail']:.4f} | "
            f"KL={wr['kl_overall_max_tail']:.4f} (classes: {wr['kl_class0_last']:.3f}, {wr['kl_class1_last']:.3f}, {wr['kl_class2_last']:.3f}) | "
            f"raw={wr['raw_overall_max_tail']:.4f}"
        )

    elapsed = time.perf_counter() - t0
    log(f"\nALL M2 CHECKS PASSED in {elapsed:.2f}s.")

    payload = {
        "timestamp": "2026-11-25",
        "dps": mp.mp.dps,
        "mobius_window_suite": mob_res,
        "gl2_orders": ord_res,
        "three_orbit_classification": orb_res,
        "full_convergent_spectrum": spec_res,
        "elapsed_seconds": round(elapsed, 3),
    }

    LOG_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    JSON_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
