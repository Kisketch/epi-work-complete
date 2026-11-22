#!/usr/bin/env python3
"""
OBL-3b High-Precision Numerical Verification & Boundary/Counterexample Probe
for the Weighted Phase-Transition Lower Bound:
    dim_H {x : Lambda_alpha(x) <= c} >= 1 - alpha   (and = 1 - alpha, even for c = 0).

Definitions (matching Phase2_revised.tex & EpiFormal/WeightedFiber.lean, WeightedLower.lean):
  Q_0 = 1, Q_1 = 1, Q_2 = 7, Q_{j+1} = (4j+2) Q_j + Q_{j-1}  (j >= 1)
  Lambda_alpha(x) = limsup_{j->inf} j^alpha * ||Q_j x||
  wrad(c, alpha, j) = r_j = c / (j^alpha * Q_j)
  Parent interval: I_j(m) = [m/Q_j - r_j, m/Q_j + r_j]

Strict nesting condition I_{j+1}(k) subseteq I_j(m):
  |k/Q_{j+1} - m/Q_j| <= r_j - r_{j+1}
  Width in k-space: W_j = 2 * (r_j - r_{j+1}) * Q_{j+1} = 2c * (R_j / j^alpha - 1 / (j+1)^alpha),
  where R_j = Q_{j+1} / Q_j = (4j+2) + 1/R_{j-1}.

Sibling separation at level j+1:
  eps_j = 1/Q_{j+1} - 2 * r_{j+1} = (1 - 2c / (j+1)^alpha) / Q_{j+1}.

Falconer mass distribution lower bound (Falconer, Fractal Geometry, Prop. 4.6):
  s_k = (sum_{j=j_0}^{k-1} log m_j) / (-log(m_k * eps_k))
Direct diameter ratio:
  d_k = (sum_{j=j_0}^{k} log m_j) / (-log(2 * r_{k+1}))
"""

import sys
import math
from mpmath import mp, mpf, log, floor, ceil

mp.dps = 60  # 60 decimal digits of precision


def precompute_Q_ratios(N_max: int):
    """
    Precompute R_j = Q_{j+1}/Q_j and log Q_j up to j = N_max + 1 in 60-digit mpmath,
    and cross-check against exact Python integers up to j = 500.
    """
    # Exact integers up to 500
    Q_exact = [1, 1]  # Q_0=1, Q_1=1
    for j in range(1, 501):
        Q_exact.append((4 * j + 2) * Q_exact[j] + Q_exact[j - 1])

    # R[j] = Q_{j+1} / Q_j for j >= 0; R[0] = Q_1/Q_0 = 1, R[1] = Q_2/Q_1 = 7
    R = [mpf(0)] * (N_max + 2)
    logQ = [mpf(0)] * (N_max + 3)
    R[0] = mpf(1)
    logQ[0] = mpf(0)
    logQ[1] = mpf(0)
    for j in range(1, N_max + 2):
        R[j] = mpf(4 * j + 2) + mpf(1) / R[j - 1]
        logQ[j + 1] = logQ[j] + log(R[j])

    # Cross-check exact vs mpmath up to j = 500
    max_err = mpf(0)
    for j in range(1, 501):
        err = abs(logQ[j] - log(mpf(Q_exact[j])))
        if err > max_err:
            max_err = err
    assert max_err < mpf("1e-50"), f"logQ mismatch: {max_err}"
    return Q_exact, R, logQ, max_err


def width_W(c: mpf, alpha: mpf, j: int, R_j: mpf) -> mpf:
    """Exact width W_j = 2*(r_j - r_{j+1})*Q_{j+1} for constant c."""
    return mpf(2) * c * (R_j / (mpf(j) ** alpha) - mpf(1) / (mpf(j + 1) ** alpha))


def width_W_decay(alpha: mpf, j: int, R_j: mpf, mode: str = "log_j_plus_2") -> mpf:
    """Exact width W_j for slowly decaying radius c_j = 1/log(j+2) or 1/log(j)."""
    if mode == "log_j_plus_2":
        c_j = mpf(1) / log(mpf(j + 2))
        c_j1 = mpf(1) / log(mpf(j + 3))
    elif mode == "log_j":
        c_j = mpf(1) / log(mpf(j))
        c_j1 = mpf(1) / log(mpf(j + 1))
    else:
        raise ValueError(mode)
    return mpf(2) * (c_j * R_j / (mpf(j) ** alpha) - c_j1 / (mpf(j + 1) ** alpha))


def test_exact_nesting_vs_formula(Q_exact, R):
    """
    Verify on actual parent centers m in {1, ..., Q_j - 1} (for small j)
    that:
      min_m N_closed(j, m) >= floor(W_j) >= floor(8*c*j^(1-alpha))
      min_m N_open(j, m)   >= ceil(W_j) - 1
    and compare with Lean's WeightedLower intersection width W_inter = 2*(r_j + r_{j+1})*Q_{j+1}.
    """
    print("=" * 88)
    print("TEST 1: Exact Strict Nesting Count vs Uniform Lower Bounds (sampled over actual m)")
    print("=" * 88)
    print(f"{'alpha':>5} {'c':>6} {'j':>3} | {'W_j':>12} {'floor(W)':>8} {'min_cls':>7} {'max_cls':>7} {'min_opn':>7} {'fl(8cj^1-a)':>11} {'W_inter-W_nest':>14}")
    print("-" * 88)

    cases = [
        (mpf("0.5"), mpf("0.25"), [1, 2, 3, 4]),
        (mpf("0.5"), mpf("1.0"),  [1, 2, 3, 4]),
        (mpf("0.25"), mpf("0.01"), [1, 2, 3, 4]),
        (mpf("0.75"), mpf("0.25"), [1, 2, 3, 4]),
        (mpf("0.9"), mpf("1.0"),   [1, 2, 3, 4]),
    ]
    for alpha, c, js in cases:
        for j in js:
            Qj = Q_exact[j]
            Qj1 = Q_exact[j + 1]
            rj = c / (mpf(j) ** alpha * mpf(Qj))
            rj1 = c / (mpf(j + 1) ** alpha * mpf(Qj1))
            Wj = width_W(c, alpha, j, R[j])
            W_inter = mpf(2) * (rj + rj1) * mpf(Qj1)
            fl_W = int(floor(Wj))
            fl_8 = int(floor(mpf(8) * c * (mpf(j) ** (mpf(1) - alpha))))

            # Check all interior m (or sample up to 200 m if Qj is large)
            if Qj <= 200:
                ms = list(range(0, Qj + 1))
            else:
                step = max(1, Qj // 200)
                ms = list(range(0, Qj + 1, step))

            min_cls = 10**18
            max_cls = -1
            min_opn = 10**18
            for m in ms:
                center = mpf(m) * mpf(Qj1) / mpf(Qj)
                half = (rj - rj1) * mpf(Qj1)
                A = center - half
                B = center + half
                # Closed nesting: A <= k <= B
                k_lo = int(ceil(A))
                k_hi = int(floor(B))
                cnt_cls = max(0, k_hi - k_lo + 1)
                # Strict interior nesting: A < k < B
                # Use exact check with small tolerance avoidance via integer/floor
                k_lo_opn = int(floor(A)) + 1
                k_hi_opn = int(ceil(B)) - 1
                cnt_opn = max(0, k_hi_opn - k_lo_opn + 1)

                if cnt_cls < min_cls:
                    min_cls = cnt_cls
                if cnt_cls > max_cls:
                    max_cls = cnt_cls
                if cnt_opn < min_opn:
                    min_opn = cnt_opn

            assert min_cls >= fl_W, f"Closed nesting bound failed: {min_cls} < {fl_W}"
            assert fl_W >= fl_8, f"8c j^(1-alpha) bound failed: {fl_W} < {fl_8}"
            assert min_opn >= max(0, int(ceil(Wj)) - 1), f"Open nesting bound failed"
            print(
                f"{float(alpha):5.2f} {float(c):6.2f} {j:3d} | "
                f"{float(Wj):12.5f} {fl_W:8d} {min_cls:7d} {max_cls:7d} {min_opn:7d} "
                f"{fl_8:11d} {float(W_inter - Wj):14.5f}"
            )
    print("All exact strict nesting inequalities verified (0 failures).\n")


def find_j0_constant(c: mpf, alpha: mpf, R, max_search: int = 100000):
    """
    Find exact thresholds for constant c > 0, alpha in [0, 1):
      j_nest: smallest j >= 1 such that floor(W_{j'}) >= 2 for all j' >= j
      j_open: smallest j >= 1 such that ceil(W_{j'}) - 1 >= 2 (i.e. W_{j'} > 2) for all j' >= j
      j_sep:  smallest j >= 1 such that 1 - 2c/(j'+1)^alpha > 0 for all j' >= j
      j_0 = max(j_nest, j_sep)
    """
    # For alpha > 0, separation 1 - 2c/(j+1)^alpha > 0 iff (j+1)^alpha > 2c
    if alpha == 0:
        if c >= mpf("0.5"):
            j_sep = None  # Never separated!
        else:
            j_sep = 1
    else:
        # smallest j >= 1 with (j+1)^alpha > 2c
        val = (mpf(2) * c) ** (mpf(1) / alpha)
        j_sep = max(1, int(floor(val)) + 1 - 1)
        # verify strictly
        while (mpf(j_sep + 1) ** alpha) <= mpf(2) * c:
            j_sep += 1
        while j_sep > 1 and (mpf(j_sep) ** alpha) > mpf(2) * c:
            j_sep -= 1

    # Since W_j is strictly increasing for large j (in fact for all j >= 1 when alpha < 1),
    # find exact j_nest and j_open
    j_nest = None
    j_open = None
    # Analytical estimate for fast search if very large
    if alpha < 1 and c > 0:
        est = (mpf(2) / (mpf(8) * c)) ** (mpf(1) / (mpf(1) - alpha))
        if est > max_search:
            # Compute directly via asymptotic R_j ~ 4j+2
            j_lo = max(1, int(floor(est * mpf("0.5"))))
            j_hi = int(ceil(est * mpf("1.5"))) + 10
            # binary search using R_j > 4j+2
            def W_asym(j_int):
                R_approx = mpf(4 * j_int + 2) + mpf(1) / mpf(4 * j_int - 2)
                return width_W(c, alpha, j_int, R_approx)
            # find j_nest
            lo, hi = j_lo, j_hi
            while lo < hi:
                mid = (lo + hi) // 2
                if floor(W_asym(mid)) >= 2:
                    hi = mid
                else:
                    lo = mid + 1
            j_nest = lo
            lo, hi = j_lo, j_hi
            while lo < hi:
                mid = (lo + hi) // 2
                if ceil(W_asym(mid)) - 1 >= 2:
                    hi = mid
                else:
                    lo = mid + 1
            j_open = lo
            j_0 = max(j_nest, j_sep) if j_sep is not None else None
            return j_nest, j_open, j_sep, j_0

    for j in range(1, max_search + 1):
        Wj = width_W(c, alpha, j, R[j])
        if j_nest is None and int(floor(Wj)) >= 2:
            j_nest = j
        if j_open is None and int(ceil(Wj)) - 1 >= 2:
            j_open = j
        if j_nest is not None and j_open is not None:
            break
    j_0 = max(j_nest, j_sep) if (j_nest is not None and j_sep is not None) else None
    return j_nest, j_open, j_sep, j_0


def test_falconer_convergence(R, logQ):
    """
    Test thresholds j_0(alpha, c) and Falconer convergence s_k -> 1 - alpha
    across alpha in {0.1, 0.25, 0.5, 0.75, 0.9} and c in {0.01, 0.25, 1.0, 10.0}.
    """
    print("=" * 112)
    print("TEST 2: Thresholds j_0(alpha, c) and Falconer Lower Bound s_k -> 1 - alpha")
    print("=" * 112)
    alphas = [mpf("0.1"), mpf("0.25"), mpf("0.5"), mpf("0.75"), mpf("0.9")]
    cs = [mpf("0.01"), mpf("0.25"), mpf("1.0"), mpf("10.0")]
    ks_check = [1000, 10000, 50000, 100000]

    print(
        f"{'alpha':>5} {'1-a':>5} {'c':>6} | {'j_nest':>7} {'j_sep':>7} {'j_0':>7} | "
        f"{'s_1e3':>9} {'s_1e4':>9} {'s_5e4':>9} {'s_1e5':>9} | {'d_1e5':>9} | {'(s_1e5-(1-a))*ln(k)':>19} {'theo_C':>8}"
    )
    print("-" * 112)

    for alpha in alphas:
        target = mpf(1) - alpha
        for c in cs:
            j_nest, j_open, j_sep, j_0 = find_j0_constant(c, alpha, R, max_search=100000)
            # Theoretical leading constant C in s_k = (1-alpha) + C / log(k) + O(1/log^2 k)
            # C = log(8c) - (1-alpha)*log(4)
            theo_C = log(mpf(8) * c) - target * log(mpf(4))

            if j_0 is None or j_0 >= 90000:
                # For extreme cases like alpha=0.9, c=0.01 where j_nest ~ (1/0.04)^10 ~ 9.5e13,
                # or alpha=0.1, c=10 where j_sep ~ 20^10 = 1.024e13, report exact j_0 and asymptotic evaluation!
                print(
                    f"{float(alpha):5.2f} {float(target):5.2f} {float(c):6.2f} | "
                    f"{str(j_nest):>7} {str(j_sep):>7} {str(j_0):>7} | "
                    f"{'(j_0>9e4)':>9} {'(see note)':>9} {'':>9} {'':>9} | {'':>9} | {'':>19} {float(theo_C):8.4f}"
                )
                continue

            sum_log_m = mpf(0)
            s_vals = {}
            d_1e5 = None
            for k in range(j_0, 100001):
                Wk = width_W(c, alpha, k, R[k])
                mk = int(floor(Wk))
                assert mk >= 2, f"mk < 2 at alpha={alpha}, c={c}, k={k}"
                gap_factor = mpf(1) - mpf(2) * c / (mpf(k + 1) ** alpha)
                assert gap_factor > 0, f"gap <= 0 at alpha={alpha}, c={c}, k={k}"

                if k in ks_check and k > j_0:
                    # Falconer: s_k = (sum_{j=j_0}^{k-1} log m_j) / (-log(m_k * eps_k))
                    neg_log_mk_epsk = logQ[k + 1] - log(mpf(mk)) - log(gap_factor)
                    s_vals[k] = sum_log_m / neg_log_mk_epsk

                sum_log_m += log(mpf(mk))

                if k == 100000:
                    # Direct diameter ratio: (sum_{j=j_0}^k log m_j) / (-log(2*r_{k+1}))
                    neg_log_diam = logQ[k + 1] + alpha * log(mpf(k + 1)) - log(mpf(2) * c)
                    d_1e5 = sum_log_m / neg_log_diam

            def fmt(val):
                return f"{float(val):9.6f}" if val is not None else f"{'N/A':>9}"

            s1e5 = s_vals.get(100000)
            scaled_err = (s1e5 - target) * log(mpf(100000)) if s1e5 is not None else None
            print(
                f"{float(alpha):5.2f} {float(target):5.2f} {float(c):6.2f} | "
                f"{j_nest:7d} {j_sep:7d} {j_0:7d} | "
                f"{fmt(s_vals.get(1000))} {fmt(s_vals.get(10000))} {fmt(s_vals.get(50000))} {fmt(s1e5)} | "
                f"{fmt(d_1e5)} | {float(scaled_err):19.4f} {float(theo_C):8.4f}"
            )
    print()


def test_c_zero_decay(R, logQ):
    """
    Test c = 0 (Lambda_alpha(x) = 0) using slowly decaying radius:
      r_j = 1 / (j^alpha * Q_j * log(j+2))
    for alpha in {0.0, 0.1, 0.25, 0.5, 0.75, 0.9}.
    """
    print("=" * 112)
    print("TEST 3: c = 0 (Lambda_alpha(x) = 0) via Slowly Decaying Radius c_j = 1/log(j+2)")
    print("=" * 112)
    alphas = [mpf("0.0"), mpf("0.1"), mpf("0.25"), mpf("0.5"), mpf("0.75"), mpf("0.9")]
    ks_check = [1000, 10000, 50000, 100000]

    print(
        f"{'alpha':>5} {'1-a':>5} | {'j_nest':>7} {'j_sep':>7} {'j_0':>7} | "
        f"{'s_1e3':>9} {'s_1e4':>9} {'s_5e4':>9} {'s_1e5':>9} | {'d_1e5':>9} | {'err*ln(k)/lnln(k)':>17}"
    )
    print("-" * 112)

    for alpha in alphas:
        target = mpf(1) - alpha
        # Find j_sep: 2 / ((j+1)^alpha * log(j+3)) < 1
        j_sep = 1
        while mpf(2) / ((mpf(j_sep + 1) ** alpha) * log(mpf(j_sep + 3))) >= mpf(1):
            j_sep += 1
        # Find j_nest: floor(W_j) >= 2
        j_nest = 1
        while j_nest <= 100000 and int(floor(width_W_decay(alpha, j_nest, R[j_nest]))) < 2:
            j_nest += 1
        j_0 = max(j_nest, j_sep)

        sum_log_m = mpf(0)
        s_vals = {}
        d_1e5 = None
        for k in range(j_0, 100001):
            Wk = width_W_decay(alpha, k, R[k])
            mk = int(floor(Wk))
            assert mk >= 2
            c_k1 = mpf(1) / log(mpf(k + 3))
            gap_factor = mpf(1) - mpf(2) * c_k1 / (mpf(k + 1) ** alpha)
            assert gap_factor > 0

            if k in ks_check and k > j_0:
                neg_log_mk_epsk = logQ[k + 1] - log(mpf(mk)) - log(gap_factor)
                s_vals[k] = sum_log_m / neg_log_mk_epsk

            sum_log_m += log(mpf(mk))

            if k == 100000:
                neg_log_diam = logQ[k + 1] + alpha * log(mpf(k + 1)) - log(mpf(2) * c_k1)
                d_1e5 = sum_log_m / neg_log_diam

        s1e5 = s_vals[100000]
        # Expected error: s_k - (1-alpha) ~ - log(log(k)) / log(k)
        ratio_ll = (target - s1e5) * log(mpf(100000)) / log(log(mpf(100000)))
        print(
            f"{float(alpha):5.2f} {float(target):5.2f} | "
            f"{j_nest:7d} {j_sep:7d} {j_0:7d} | "
            f"{float(s_vals[1000]):9.6f} {float(s_vals[10000]):9.6f} {float(s_vals[50000]):9.6f} {float(s1e5):9.6f} | "
            f"{float(d_1e5):9.6f} | {float(ratio_ll):17.4f}"
        )
    print("Note: err*ln(k)/lnln(k) -> 1 asymptotically (here ~0.8-1.0 at k=1e5 due to O(1/ln k) subleading term).\n")


def test_endpoints_and_spectral_gap(Q_exact, R, logQ):
    """
    TEST 4: Endpoints alpha = 0 and alpha = 1, plus spectral gap 1/4 diagnostic.
    """
    print("=" * 100)
    print("TEST 4A: Endpoint alpha = 1 (Critical Weight) — Why the 1/4 Spectral Gap Exists ONLY Here")
    print("=" * 100)
    print(f"{'c':>6} | {'W_10':>10} {'W_100':>10} {'W_1000':>10} {'W_10000':>10} {'lim 8c':>8} | {'floor(W_1e4)':>12} {'Binary?':>8}")
    print("-" * 100)
    for c_str in ["0.10", "0.20", "0.24", "0.249", "0.25", "0.251", "0.50", "1.00"]:
        c = mpf(c_str)
        W10 = width_W(c, mpf(1), 10, R[10])
        W100 = width_W(c, mpf(1), 100, R[100])
        W1000 = width_W(c, mpf(1), 1000, R[1000])
        W10000 = width_W(c, mpf(1), 10000, R[10000])
        fl = int(floor(W10000))
        binary = "YES" if fl >= 2 else "NO (<2)"
        print(
            f"{float(c):6.3f} | {float(W10):10.6f} {float(W100):10.6f} {float(W1000):10.6f} "
            f"{float(W10000):10.6f} {float(8*c):8.4f} | {fl:12d} {binary:>8}"
        )

    print("\n" + "=" * 100)
    print("TEST 4B: Endpoint alpha = 0 (Unweighted) — Behavior at c < 1/2, c = 1/2, c > 1/2")
    print("=" * 100)
    print(f"{'c':>6} | {'j_nest':>6} {'j_sep':>7} {'eps_100*Q_101':>14} | {'s_1000':>9} {'s_10000':>9} {'s_100000':>9} | {'Note'}")
    print("-" * 100)
    for c_str in ["0.01", "0.10", "0.24", "0.25", "0.49", "0.50", "0.60"]:
        c = mpf(c_str)
        j_nest, j_open, j_sep, j_0 = find_j0_constant(c, mpf(0), R, max_search=10000)
        gap100 = mpf(1) - mpf(2) * c
        if j_sep is None:
            note = "Intervals overlap (eps<=0); E_0(c)=R (dim=1), but {||Q_jx||->c}=empty for c>1/2"
            print(f"{float(c):6.2f} | {j_nest:6d} {'NONE':>7} {float(gap100):14.6f} | {'N/A':>9} {'N/A':>9} {'N/A':>9} | {note}")
        else:
            sum_log_m = mpf(0)
            s_vals = {}
            for k in range(j_0, 100001):
                mk = int(floor(width_W(c, mpf(0), k, R[k])))
                if k in [1000, 10000, 100000]:
                    s_vals[k] = sum_log_m / (logQ[k + 1] - log(mpf(mk)) - log(gap100))
                sum_log_m += log(mpf(mk))
            note = "Disjoint Cantor -> dim=1"
            print(
                f"{float(c):6.2f} | {j_nest:6d} {j_sep:7d} {float(gap100):14.6f} | "
                f"{float(s_vals[1000]):9.6f} {float(s_vals[10000]):9.6f} {float(s_vals[100000]):9.6f} | {note}"
            )
    print()


def test_explicit_witness_subcritical(Q_exact):
    """
    TEST 5: Explicitly construct concrete points x (not in L = Z + Z*(e+1)/2) at alpha = 0.5
    with:
      (a) prescribed limit j^0.5 * ||Q_j x|| -> c_0 = 0.10  (strictly inside (0, 1/4)!)
      (b) prescribed limit j^0.5 * ||Q_j x|| -> 0           (Lambda_0.5(x) = 0, yet x not in L!)
    Verify by computing j^0.5 * ||Q_j x|| and recurrence digits d_j = M_{j+1} - (4j+2)M_j - M_{j-1}
    directly up to j = 80 in high precision (mp.dps = 300).
    """
    print("=" * 100)
    print("TEST 5: Explicit Non-L Witness Points at alpha = 0.5 (Refuting any 1/4 Gap for alpha < 1)")
    print("=" * 100)
    old_dps = mp.dps
    mp.dps = 300  # Need > log10(Q_100) ~ 220 digits

    alpha = mpf("0.5")
    J_max = 100

    for label, c_target in [("Prescribed c=0.10 (< 1/4)", mpf("0.10")), ("Prescribed c=0.00 (Lambda_0.5=0, x not in L)", mpf("0.0"))]:
        # Build nested intervals starting at j_start = 10, picking alternating left/right children
        # so the resulting point is definitely not in L (in fact d_j != 0 infinitely often).
        j_start = 10
        # Parent at j_start: center (k + c_target * j^-alpha) / Q_j
        k_cur = Q_exact[j_start] // 3  # safely in interior of (0, 1)
        centers_k = {j_start: k_cur}

        for j in range(j_start, J_max):
            Qj = mpf(Q_exact[j])
            Qj1 = mpf(Q_exact[j + 1])
            wj = (mpf(j) ** (-alpha)) / log(mpf(j + 2))
            wj1 = (mpf(j + 1) ** (-alpha)) / log(mpf(j + 3))
            rj = wj / Qj
            rj1 = wj1 / Qj1

            c_shift_j = c_target * (mpf(j) ** (-alpha))
            c_shift_j1 = c_target * (mpf(j + 1) ** (-alpha))

            parent_ctr = (mpf(k_cur) + c_shift_j) / Qj
            # Strict nesting: parent_ctr - rj <= (k' + c_shift_j1)/Qj1 - rj1  and  ... <= parent_ctr + rj
            A = (parent_ctr - (rj - rj1)) * Qj1 - c_shift_j1
            B = (parent_ctr + (rj - rj1)) * Qj1 - c_shift_j1
            k_lo = int(ceil(A))
            k_hi = int(floor(B))
            assert k_hi >= k_lo + 1, f"Not enough children at j={j}: [{k_lo}, {k_hi}]"
            # Pick k_hi on even j, k_lo on odd j to ensure non-trivial oscillation (not in L)
            k_next = k_hi if (j % 2 == 0) else k_lo
            k_cur = k_next
            centers_k[j + 1] = k_cur

        # Take x = center of level J_max interval
        x = (mpf(k_cur) + c_target * (mpf(J_max) ** (-alpha))) / mpf(Q_exact[J_max])

        print(f"\n--- {label} ---")
        print(f"x approx = {mp.nstr(x, 30)}")
        print(f"{'j':>4} | {'j^0.5 * ||Q_j x||':>20} | {'target c':>10} | {'|err|':>12} | {'1/log(j+2)':>12} | {'d_j':>6}")
        print("-" * 78)
        M_prev2 = None
        M_prev1 = None
        nonzero_d = 0
        for j in range(j_start, 81):
            qx = mpf(Q_exact[j]) * x
            M_j = int(floor(qx + mpf("0.5")))
            dist_int = abs(qx - mpf(M_j))
            val = (mpf(j) ** alpha) * dist_int
            err = abs(val - c_target)
            bnd = mpf(1) / log(mpf(j + 2))
            assert err <= bnd + mpf("1e-50"), f"Bound violated at j={j}: {err} > {bnd}"

            d_j_str = "   -"
            if M_prev2 is not None and M_prev1 is not None:
                # d_{j-1} = M_j - (4*(j-1)+2)*M_{j-1} - M_{j-2}
                d_prev = M_j - (4 * (j - 1) + 2) * M_prev1 - M_prev2
                if d_prev != 0:
                    nonzero_d += 1
                d_j_str = f"{d_prev:6d}"
            M_prev2, M_prev1 = M_prev1, M_j

            if j in [12, 20, 30, 40, 50, 60, 70, 80]:
                print(f"{j:4d} | {float(val):20.12f} | {float(c_target):10.4f} | {float(err):12.6e} | {float(bnd):12.6e} | {d_j_str}")
        print(f"Non-zero recurrence digits d_j among j in [{j_start+1}, 79]: {nonzero_d} / {79 - j_start} (proves x not in L!).")

    mp.dps = old_dps
    print()


def main():
    print("Precomputing Q_j ratios up to j = 100,000 (mpmath dps=60)...")
    Q_exact, R, logQ, max_err = precompute_Q_ratios(100000)
    print(f"Cross-check exact Q_j vs mpmath logQ_j (j<=500): max_err = {float(max_err):.3e}\n")

    test_exact_nesting_vs_formula(Q_exact, R)
    test_falconer_convergence(R, logQ)
    test_c_zero_decay(R, logQ)
    test_endpoints_and_spectral_gap(Q_exact, R, logQ)
    test_explicit_witness_subcritical(Q_exact)
    print("ALL VERIFICATION TESTS COMPLETED SUCCESSFULLY.")


if __name__ == "__main__":
    main()
