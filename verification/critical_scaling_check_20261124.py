# -*- coding: utf-8 -*-
"""
Critical scaling check for the multi-residue family  (类别 4：有限计算 / 数值佐证，非证明).

Heuristic model (NOT a theorem; derived from the tail equation of paper 2, Step S15, with the
structural series C_S(p) = sum_n W_S(p,n) replaced near its pole p = 2 s0(S) by kappa(S) / (p - 2 s0(S))):
        eps * (eps + eta) * m^(1+eps) = d * kappa(S),      eps = 2*dim - 1 >= 0,  eta = 1 - 2 s0(S),  d = |S| + |B|.
Off critical (eps << |eta|) it reproduces the proved asymptotics:
        subcritical  (eta > 0):  eps ~ (d kappa / eta) / m            ->  dim - 1/2 ~ C_S / (2 m),  C_S = kappa / eta
        supercritical(eta < 0):  eps - |eta| ~ (d kappa / |eta|) m^(-1-|eta|) ->  dim - s0 ~ (d kappa/|eta|) m^(-2 s0)
Critical window (|eta| <~ m^(-1/2)):   eps ~ sqrt(d kappa) m^(-1/2)   ->  dim - 1/2 ~ m^(-1/2), crossover m* ~ d kappa / eta^2.

Independent prediction of kappa(S) = residue of C_S(p) at p = 2 s0(S):
        kappa = c / (-rho'(2 s0)),   c = lim_n W_S(2 s0, n) = lim_j (L^j 1)(0)  (PF eigenfunction normalisation),
        rho(p) = spectral radius of the finite-alphabet operator L f(x) = sum_{a in S} (a+x)^{-p} f(1/(a+x)).
rho' by central differences (h = 1e-4), c by iterating the n = 24 collocation of L at p = 2 s0.
Observed values come from critical_point_scan_20261124.jsonl (n = 16 records).
Usage: .venv\\Scripts\\python.exe verification\\critical_scaling_check_20261124.py  > output
"""
import json
import math
from collections import defaultdict
from pathlib import Path

from mpmath import mp, mpf, matrix, eig

DPS = 30
mp.dps = DPS
HERE = Path(__file__).resolve().parent
JSONL = HERE / "critical_point_scan_20261124.jsonl"
N = 24


def nodes(n):
    return [(1 + mp.cos(mp.pi * (2 * i + 1) / (2 * n))) / 2 for i in range(n)]


def op_matrix(S, p, n):
    """Collocation matrix A of L f(x) = sum_{a in S} (a+x)^{-p} f(1/(a+x)) on degree<n polys (value basis)."""
    xs = nodes(n)
    M = matrix(n, n)
    V = matrix(n, n)
    for i, x in enumerate(xs):
        for j in range(n):
            M[i, j] = sum((mpf(a) + x) ** (-(p + j)) for a in S)
            V[i, j] = x ** j
    return M * V ** -1


def rho_finite(S, p, n=N):
    A = op_matrix(S, p, n)
    return max(abs(e) for e in eig(A, left=False, right=False))


def c_limit(S, p, n=N, iters=3000, tol=mpf("1e-22")):
    """c = lim_j (L^j 1)(0) at exponent p = 2 s0 (spectral radius 1): equals lim_n W_S(2 s0, n)."""
    A = op_matrix(S, p, n)
    f = matrix([mpf(1)] * n)
    xs = nodes(n)
    V = matrix(n, n)
    for i, x in enumerate(xs):
        for j in range(n):
            V[i, j] = x ** j
    Vinv = V ** -1
    prev = None
    for _ in range(iters):
        f = A * f
        val = (Vinv * f)[0]
        if prev is not None and abs(val - prev) < tol:
            return val
        prev = val
    return prev


def kappa_pred(S, s0):
    h = mpf("1e-4")
    p0 = 2 * mpf(s0)
    drho = (rho_finite(S, p0 + h) - rho_finite(S, p0 - h)) / (2 * h)
    c = c_limit(S, p0)
    return c / (-drho), c, drho


def eps_model(m, eta, dk):
    """Solve eps*(eps+eta)*m^(1+eps) = dk for eps > max(0, -eta)."""
    lo = max(mpf(0), -eta) + mpf("1e-18")
    hi = mpf("1.5")

    def g(e):
        return mp.log(e) + mp.log(e + eta) + (1 + e) * mp.log(m) - mp.log(dk)

    # g increasing on (max(0,-eta), inf): check bracket
    if g(lo) > 0 or g(hi) < 0:
        return None
    for _ in range(200):
        mid = (lo + hi) / 2
        if g(mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def main():
    s0 = {}
    scan = defaultdict(dict)
    with open(JSONL, encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            if r.get("stage") == "s0" and r.get("n") == 24:
                s0[tuple(r["S"])] = mpf(r["s0"])
            elif r.get("stage") == "scan" and r.get("n") == 16:
                scan[(tuple(r["S"]), tuple(r["B"]))][r["m"]] = mpf(r["dim"])
    print("# Critical scaling check (类别 4): model eps(eps+eta) m^(1+eps) = d*kappa(S)\n")
    print("kappa(S) predicted = c / (-rho'(2 s0)),  c = lim_n W_S(2 s0, n)  (n=24 collocation, dps=30)\n")
    print("| S | s0 | eta=1-2s0 | c | -rho'(2s0) | kappa_pred |")
    print("|---|---:|---:|---:|---:|---:|")
    kmap = {}
    for S, sv in s0.items():
        k, c, dr = kappa_pred(S, sv)
        kmap[S] = k
        print(f"| {list(S)} | {mp.nstr(sv, 9)} | {mp.nstr(1 - 2 * sv, 7)} | {mp.nstr(c, 8)} | {mp.nstr(-dr, 8)} | {mp.nstr(k, 8)} |")
    print("\n## Model vs observation: eps_obs = 2(dim - 1/2), eps_model from the equation with kappa_pred and d = |S|+|B|\n")
    for (S, B), pts in sorted(scan.items(), key=lambda kv: (kv[0][0], kv[0][1])):
        if S not in kmap:
            continue
        d = len(S) + len(B)
        eta = 1 - 2 * s0[S]
        dk = d * kmap[S]
        mstar = dk / eta ** 2 if eta != 0 else mpf("inf")
        print(f"\n### S={list(S)} B={list(B)}  d={d}  eta={mp.nstr(eta, 7)}  d*kappa={mp.nstr(dk, 8)}  crossover m*~{mp.nstr(mstar, 5)}\n")
        print("| m | eps_obs | eps_model | ratio obs/model | window? (m << m*) |")
        print("|---:|---:|---:|---:|:---:|")
        for m in sorted(pts):
            e_obs = 2 * (pts[m] - mpf("0.5"))
            e_mod = eps_model(mpf(m), eta, dk)
            ratio = e_obs / e_mod if e_mod else mpf("nan")
            win = "yes" if m < mstar / 10 else ("edge" if m < 10 * mstar else "no")
            print(f"| {m} | {mp.nstr(e_obs, 8)} | {mp.nstr(e_mod, 8)} | {mp.nstr(ratio, 6)} | {win} |")
    print("\nAll values are numerical (类别 4). The model is a heuristic two-term truncation; deviations of a few percent at "
          "large eps (small m) are expected from the O(eps) terms dropped (zeta(1+eps) vs 1/eps, V ~ C_S(2s)).")


if __name__ == "__main__":
    main()
