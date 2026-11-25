"""Numerical exploration (non-rigorous): local dimension of G = {x near v : ||x^n - y_n|| <= delta, all n >= n0}.

Research question (candidate A, nonlinear case; see verification/candidateA_precedent_search_20261125.md sec. 3).

Heuristic: a level-n interval (all constraints up to n satisfied) has length ~ 2 delta / (n v^(n-1)).
Under x -> x^(n+1) its image has length ~ 2 delta v, so it contains about 2 delta v (+-1) admissible
integers k for the next constraint, and each child is ~1/v times shorter. This suggests
    dim_loc(v) = log(2 delta v) / log v       (conjecture C1, for 2 delta v > 1),
with rigorous elementary bounds  log floor(2 delta (v-1)) / log v <= dim <= log(2 delta v + 2 delta + 1)/log v
(research note, sec. 2).

The script enumerates every level-n interval exactly (mpmath, precision grown with n) for
x in [v - eps, v + eps] and reports the growth rate of the count N_n against the shrinkage of the
interval lengths:
    s_n := log(N_n / N_m) / log(Lbar_m / Lbar_n),
where Lbar_n is the geometric mean length at level n and m is a reference level. s_n is a
box-counting-type estimate. It is evidence only, not a proof (class 4 in AGENTS.md).

Usage: python verification/powers_mod1_dimension_numerics_20261125.py
"""
import json
import math
import random
import sys
import time

import mpmath as mp

CASES = [
    # (v, delta, y-sequence label, eps, n_start, n_max, cap on #intervals)
    (3.0, 0.30, "zero", 0.002, 4, 40, 400000),
    (3.0, 0.30, "random", 0.002, 4, 40, 400000),
    (3.0, 0.30, "half", 0.002, 4, 40, 400000),
    (5.0, 0.15, "zero", 0.002, 3, 40, 400000),
    (5.0, 0.15, "random", 0.02, 3, 40, 400000),
    (2.5, 0.40, "random", 0.002, 5, 40, 400000),
    (4.0, 0.20, "random", 0.002, 4, 40, 400000),
    (3.0, 0.45, "random", 0.002, 4, 40, 400000),
]


def yseq(label, n, rng_cache):
    if label == "zero":
        return mp.mpf(0)
    if label == "half":
        return mp.mpf(1) / 2
    if n not in rng_cache:
        rng_cache[n] = mp.mpf(random.Random(1000 + n).random())
    return rng_cache[n]


def run_case(v, delta, ylab, eps, n_start, n_max, cap):
    rng_cache = {}
    delta = mp.mpf(delta)
    a, b = mp.mpf(v) - eps, mp.mpf(v) + eps
    # level n_start: all x in [a,b] with ||x^n - y_n|| <= delta
    intervals = [(a, b)]
    rows = []
    for n in range(n_start, n_max + 1):
        mp.mp.dps = int(n * math.log10(v + 1)) + 40
        y = yseq(ylab, n, rng_cache)
        new = []
        inv = mp.mpf(1) / n
        for (c, d) in intervals:
            lo, hi = c ** n, d ** n
            kmin = int(mp.ceil(lo - y - delta))
            kmax = int(mp.floor(hi - y + delta))
            for k in range(kmin, kmax + 1):
                l = max(c, mp.root(k + y - delta, n)) if k + y - delta > 0 else c
                r = min(d, mp.root(k + y + delta, n))
                if r > l:
                    new.append((l, r))
        intervals = new
        N = len(intervals)
        if N == 0:
            rows.append({"n": n, "N": 0})
            break
        mean_log_len = float(sum(mp.log(r - l) for (l, r) in intervals) / N)
        rows.append({"n": n, "N": N, "mean_log_len": mean_log_len})
        if N > cap:
            break
    return rows


def summarize(v, delta, rows):
    pred = math.log(2 * delta * v) / math.log(v)
    # rigorous elementary bounds (research note sec. 2): floor(2 delta (v-1)) full children per full
    # parent below; at most 2 delta v + 2 delta + 1 children per parent above
    m = math.floor(2 * delta * (v - 1))
    lo = math.log(m) / math.log(v) if m >= 2 else 0.0
    hi = math.log(2 * delta * v + 2 * delta + 1) / math.log(v)
    good = [r for r in rows if r.get("N", 0) > 0]
    est = []
    if len(good) >= 6:
        m = good[len(good) // 3]                      # reference level, past the transient
        for r in good[len(good) // 3 + 3:]:
            s = math.log(r["N"] / m["N"]) / (m["mean_log_len"] - r["mean_log_len"])
            est.append((r["n"], s))
    # correction-free statistic: g_n = (N_{n+1}/N_n) * n/(n+1) should tend to 2 delta v
    g = [(a["n"], (b["N"] / a["N"]) * a["n"] / (a["n"] + 1)) for a, b in zip(good, good[1:])]
    return pred, lo, hi, est, g


def main():
    out = []
    for (v, delta, ylab, eps, n0, n1, cap) in CASES:
        t0 = time.time()
        rows = run_case(v, delta, ylab, eps, n0, n1, cap)
        pred, lo, hi, est, g = summarize(v, delta, rows)
        last = est[-1] if est else (None, None)
        print(f"v={v} delta={delta} y={ylab}: levels {rows[0]['n']}..{rows[-1]['n']}, "
              f"N_last={rows[-1].get('N')}, 2*delta*v={2*delta*v:.3f}")
        print(f"   C1 prediction log(2dv)/log v = {pred:.4f}   rigorous bounds [{lo:.4f}, {hi:.4f}]")
        print("   estimates s_n:", ", ".join(f"n={n}:{s:.4f}" for n, s in est[-6:]))
        tail = g[len(g) // 2:]
        gbar = math.exp(sum(math.log(x) for _, x in tail) / len(tail)) if tail else float("nan")
        print(f"   normalized growth g_n (last 4):", ", ".join(f"n={n}:{x:.4f}" for n, x in g[-4:]),
              f"| geometric mean over second half = {gbar:.4f}  vs 2*delta*v = {2*delta*v:.4f}")
        print(f"   time {time.time()-t0:.1f}s")
        sys.stdout.flush()
        out.append({"v": v, "delta": delta, "y": ylab, "eps": eps, "rows": rows,
                    "pred": pred, "bounds": [lo, hi], "estimates": est, "g": g})
    with open("verification/powers_mod1_dimension_numerics_20261125.json", "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
