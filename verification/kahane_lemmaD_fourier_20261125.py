"""Numerical probe (non-rigorous) of Lemma D in research/kahane_q6_note_20261125.md, sec. 3b.

Exact identity (sec. 3b): with W_n = mu_n / (|I| (2 eps)^(n - n0 + 1)),
    E[W_{n+1}^2] - E[W_n^2] = sum_{h != 0} ghat(h) E|S_n(h)|^2 / (|I|^2 (2 eps)^(2(n - n0 + 2))),
    S_n(h) = int_{G_n} e(h x^(n+1)) dx,   ghat(h) = sin^2(2 pi h eps) / (pi h)^2.
Lemma D says the right-hand side is summable in n when 2 eps v > 1.

For many i.i.d. uniform target sequences this script computes G_n exactly (numpy interval
enumeration), the integrals S_n(h) for |h| <= H by Gauss-Legendre quadrature on each interval, and
reports per level:
  * D_n(h)  = E|S_n(h)|^2 / (|I|^2 (2 eps)^(2(n - n0 + 1)))   (normalized Fourier energy, h = 1, 2, 3)
  * pred_n  = predicted increment of E[W^2] from the identity (|h| <= H)
  * emp_n   = empirical increment E[W_{n+1}^2] - E[W_n^2] (same samples)
pred_n vs emp_n is a consistency check of the identity (up to Monte Carlo error and truncation at H).
The decay rate of D_n in n indicates whether the series in Lemma D converges. Evidence only (class 4).

Usage: python verification/kahane_lemmaD_fourier_20261125.py
"""
import json
import math
import sys
import time
from multiprocessing import Pool

import numpy as np

H = 12
GL_X, GL_W = np.polynomial.legendre.leggauss(24)
CASES = [
    # (label, v, eps, eta, n0, n_max, samples)
    ("supercritical 2ev=1.8", 3.0, 0.30, 0.002, 4, 19, 600),
    ("supercritical 2ev=2.7", 3.0, 0.45, 0.002, 4, 14, 400),
    ("near-critical 2ev=1.05", 3.0, 0.175, 0.002, 4, 22, 600),
    ("subcritical 2ev=0.9", 3.0, 0.15, 0.002, 4, 22, 600),
]


def refine(L, R, n, y, eps):
    """Intersect intervals [L,R] with {x : ||x^n - y|| <= eps}; vectorized."""
    lo, hi = L ** n, R ** n
    kmin = np.ceil(lo - y - eps).astype(np.int64)
    kmax = np.floor(hi - y + eps).astype(np.int64)
    cnt = np.maximum(kmax - kmin + 1, 0)
    idx = np.repeat(np.arange(len(L)), cnt)
    if idx.size == 0:
        return np.empty(0), np.empty(0)
    start = np.repeat(np.cumsum(cnt) - cnt, cnt)
    k = np.repeat(kmin, cnt) + (np.arange(idx.size) - start)
    inv = 1.0 / n
    l = np.maximum(L[idx], np.where(k + y - eps > 0, np.maximum(k + y - eps, 0.0) ** inv, L[idx]))
    r = np.minimum(R[idx], (k + y + eps) ** inv)
    keep = r > l
    return l[keep], r[keep]


def fourier(L, R, n, hs):
    """S(h) = sum over intervals of int e(h x^(n+1)) dx, Gauss-Legendre per interval."""
    mid, half = (L + R) / 2, (R - L) / 2
    X = mid[:, None] + half[:, None] * GL_X[None, :]
    P = X ** (n + 1)
    P = P - np.floor(P)                       # reduce mod 1 before multiplying by h
    out = []
    for h in hs:
        ph = np.exp(2j * np.pi * ((h * P) % 1.0))
        out.append(np.sum(half[:, None] * GL_W[None, :] * ph))
    return np.array(out)


def path(args):
    v, eps, eta, n0, n_max, seed = args
    rng = np.random.default_rng(seed)
    a, c = v - eta, v + eta
    assert (n_max + 1) * math.log10(c) < 11.5, "depth guard for double precision"
    L, R = np.array([a]), np.array([c])
    hs = list(range(1, H + 1))
    rows = []
    for n in range(n0, n_max + 1):
        L, R = refine(L, R, n, rng.random(), eps)
        mu = float(np.sum(R - L))
        S = fourier(L, R, n, hs) if L.size else np.zeros(len(hs))
        rows.append((mu, np.abs(S) ** 2))
        if L.size > 2_000_000:
            raise RuntimeError("too many intervals; lower n_max")
    return rows


def main():
    results = {}
    with Pool(10) as pool:
        for (label, v, eps, eta, n0, n_max, S) in CASES:
            t0 = time.time()
            paths = pool.map(path, [(v, eps, eta, n0, n_max, 77_000 + s) for s in range(S)])
            Ilen = 2 * eta
            g = np.array([math.sin(2 * math.pi * h * eps) ** 2 / (math.pi * h) ** 2 for h in range(1, H + 1)])
            print(f"== {label}: v={v} eps={eps} levels {n0}..{n_max} samples={S} ({time.time()-t0:.0f}s)")
            print("    n   E[W^2]   emp_incr  pred_incr   D_n(1)     D_n(2)     D_n(3)")
            out = []
            for i, n in enumerate(range(n0, n_max + 1)):
                norm = Ilen * (2 * eps) ** (n - n0 + 1)
                W2 = np.mean([p[i][0] ** 2 for p in paths]) / norm ** 2
                E_S2 = np.mean([p[i][1] for p in paths], axis=0)          # E|S_n(h)|^2, h=1..H
                D = E_S2 / norm ** 2
                pred = 2 * np.sum(g * E_S2) / (norm * 2 * eps) ** 2        # factor 2: h and -h
                emp = (np.mean([p[i + 1][0] ** 2 for p in paths]) / (norm * 2 * eps) ** 2 - W2
                       if i + 1 < len(paths[0]) else float("nan"))
                out.append({"n": n, "EW2": W2, "emp_incr": emp, "pred_incr": pred, "D": D[:3].tolist()})
                print(f"   {n:2d}  {W2:7.4f}  {emp:9.5f}  {pred:9.5f}  {D[0]:9.3e}  {D[1]:9.3e}  {D[2]:9.3e}")
            sys.stdout.flush()
            results[label] = {"v": v, "eps": eps, "rows": out}
    with open("verification/kahane_lemmaD_fourier_20261125.json", "w") as f:
        json.dump(results, f, indent=1)


if __name__ == "__main__":
    main()
