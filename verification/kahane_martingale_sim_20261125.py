"""Monte Carlo test (non-rigorous) of the second-moment route to the a.e. lower bound in Kahane's Q6.

For i.i.d. uniform targets b_n and a window I = [v - eta, v + eta], let
    mu_n = Lebesgue measure of {x in I : ||x^j - b_j|| <= eps for n0 <= j <= n},
    W_n  = mu_n / (|I| (2 eps)^(n - n0 + 1)).
For each fixed x the constraints are independent events of probability 2 eps, so E[W_n] = 1 exactly
and (W_n) is a nonnegative martingale. The proof route of research/kahane_q6_note_20261125.md sec. 3
needs sup_n E[W_n^2] < infinity in the supercritical case 2 eps v > 1, which forces W_n -> W with
P(W > 0) > 0. In the subcritical case 2 eps v < 1, Kahane's P6 suggests extinction: W_n -> 0.

The script samples many target sequences, computes mu_n exactly by interval enumeration (double
precision is adequate at these depths; see the depth guard), and reports the sample mean and
second moment of W_n per level, and the fraction of samples with W_n = 0. This is evidence only
(class 4 in AGENTS.md).

Usage: python verification/kahane_martingale_sim_20261125.py
"""
import json
import math
import random
import sys
import time
from multiprocessing import Pool

CASES = [
    # (label, v, eps, eta, n0, n_max, samples)
    ("supercritical 2ev=1.8", 3.0, 0.30, 0.002, 4, 25, 2000),
    ("supercritical 2ev=1.5", 5.0, 0.15, 0.02, 3, 17, 2000),
    ("near-critical 2ev=1.05", 3.0, 0.175, 0.002, 4, 25, 2000),
    ("subcritical 2ev=0.9", 3.0, 0.15, 0.002, 4, 25, 2000),
]


def mu_path(args):
    v, eps, eta, n0, n_max, seed = args
    rng = random.Random(seed)
    a, c = v - eta, v + eta
    assert n_max * math.log10(c) < 12, "depth guard: x^n must stay well inside double precision"
    ivs = [(a, c)]
    out = []
    for n in range(n0, n_max + 1):
        y = rng.random()
        new = []
        inv = 1.0 / n
        for (l0, r0) in ivs:
            lo, hi = l0 ** n, r0 ** n
            for k in range(math.ceil(lo - y - eps), math.floor(hi - y + eps) + 1):
                l = max(l0, (k + y - eps) ** inv) if k + y - eps > 0 else l0
                r = min(r0, (k + y + eps) ** inv)
                if r > l:
                    new.append((l, r))
        ivs = new
        mu = sum(r - l for l, r in ivs)
        out.append(mu / ((c - a) * (2 * eps) ** (n - n0 + 1)))
        if not ivs:
            out.extend([0.0] * (n_max - n))
            break
        if len(ivs) > 300000:            # cost guard; mark the rest as missing
            out.extend([float("nan")] * (n_max - n))
            break
    return out


def main():
    results = {}
    with Pool(10) as pool:
        for (label, v, eps, eta, n0, n_max, S) in CASES:
            t0 = time.time()
            paths = pool.map(mu_path, [(v, eps, eta, n0, n_max, 10_000 + s) for s in range(S)])
            print(f"== {label}: v={v} eps={eps} window +-{eta} levels {n0}..{n_max} samples={S} "
                  f"({time.time()-t0:.0f}s)")
            rows = []
            for i, n in enumerate(range(n0, n_max + 1)):
                col = [p[i] for p in paths if not math.isnan(p[i])]
                m1 = sum(col) / len(col)
                m2 = sum(w * w for w in col) / len(col)
                z = sum(1 for w in col if w == 0.0) / len(col)
                se = math.sqrt(max(m2 - m1 * m1, 0.0) / len(col))
                rows.append({"n": n, "samples": len(col), "mean_W": m1, "se_mean": se,
                             "mean_W2": m2, "frac_zero": z})
                print(f"   n={n:2d}  E[W]={m1:7.4f} (+-{se:.4f})  E[W^2]={m2:8.4f}  P(W=0)={z:.3f}"
                      f"  [{len(col)} samples]")
            sys.stdout.flush()
            results[label] = {"v": v, "eps": eps, "eta": eta, "rows": rows,
                              "final_W": [p[-1] for p in paths]}
    with open("verification/kahane_martingale_sim_20261125.json", "w") as f:
        json.dump(results, f, indent=1)


if __name__ == "__main__":
    main()
