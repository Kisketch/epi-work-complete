# -*- coding: utf-8 -*-
"""
Critical-point numerical scan for multi-residue alphabets F_{m,S,B}  (v1, 2026-11-24).

Classification (AGENTS.md): 类别 4 — 有限计算 / 数值佐证，非证明.  Nothing here is a proof.

Definitions (paper2_spectral_gap_dimension.tex, lines 3799-3826; Lean ResidueMultiAsymptotic.lean):
    A_{m,S,B} := { a in Z>=1 : (exists r in S, a >= r and a = r mod m)
                            or (exists b in B, exists k >= 1, a + b = k*m) },
    F_{m,S,B}  = CF Cantor set of numbers whose partial quotients all lie in A_{m,S,B},
    s_0(S)     := inf { s > 0 : sum_{n>=0} W_S(2s,n) < infty },   W_S(p,n) = sum_{w in S^n} q(w)^{-p}.
Numerically s_0(S) is the s at which the finite-alphabet transfer operator
    L^S_s f(x) = sum_{a in S} (a+x)^{-2s} f(1/(a+x))
has spectral radius 1 (the Poincare-abscissa identification dimH E_S = s_0(S); numerically the
same root as the pressure identification).

Method: Chebyshev collocation on polynomials, as in R7 (asymptotic_residues_check_20261123.py):
    L_s(y^j)(x) = sum_{r in S} m^{-(2s+j)} zeta(2s+j, (r+x)/m)                 # a = k m + r, k >= 0
                + sum_{b in B} m^{-(2s+j)} zeta(2s+j, k0 + (x-b)/m),  k0 = ceil((b+1)/m)   # a = k m - b, k >= k0
(no alphabet truncation), dimension estimate = s with spectral radius 1 (bisection, dps=30,
n=16; n=24 cross-check).  Self-check: S={r}, B={} must land inside the 10 kernel-checked open
brackets of tab:residues-general (m=2..6, r in {1,m}).

Stages
    selfcheck                         reproduce tab brackets
    s0                                s_0(S) table over the families below (n=24)
    xcheck S                           series-vs-operator consistency for one S (brute-force words)
    scan config.json                  dimension grid; resume by key
Run with .venv\\Scripts\\python.exe.  Outputs (all new files, never touching existing ones):
    critical_point_scan_20261124.jsonl / .log  (next to this script)
"""
import json
import sys
import time
from fractions import Fraction
from multiprocessing import Pool, cpu_count
from pathlib import Path

from mpmath import mp, mpf, zeta, matrix, eig  # noqa: F401

DPS = 30
HERE = Path(__file__).resolve().parent
JSONL = HERE / "critical_point_scan_20261124.jsonl"
LOG = HERE / "critical_point_scan_20261124.log"

# tab:residues-general (N=512 certificates): open brackets lower < dimH F_{m,r} < upper
BRACKETS = {
    (2, 1): (Fraction(105, 128), Fraction(421, 512)),
    (2, 2): (Fraction(23, 32), Fraction(369, 512)),
    (3, 1): (Fraction(95, 128), Fraction(381, 512)),
    (3, 3): (Fraction(41, 64), Fraction(329, 512)),
    (4, 1): (Fraction(357, 512), Fraction(179, 256)),
    (4, 4): (Fraction(309, 512), Fraction(155, 256)),
    (5, 1): (Fraction(171, 256), Fraction(343, 512)),
    (5, 5): (Fraction(149, 256), Fraction(299, 512)),
    (6, 1): (Fraction(331, 512), Fraction(83, 128)),
    (6, 6): (Fraction(291, 512), Fraction(73, 128)),
}

S0_FAMILIES = (
    [[1, j] for j in range(2, 13)]
    + [[2, j] for j in range(3, 13)]
    + [[1, 2, j] for j in range(3, 9)]
    + [[2, 3, j] for j in range(4, 9)]
    + [list(range(2, K + 1)) for K in range(3, 13)]
    + [list(range(3, K + 1)) for K in range(4, 13)]
    + [[2, 3, 4, j] for j in range(6, 15)]
    + [[3, 4, 5, 6, j] for j in range(8, 17)]
)


def log(msg):
    line = f"[{time.strftime('%H:%M:%S')}] {msg}"
    print(line, flush=True)
    with open(LOG, "a", encoding="utf-8") as f:
        f.write(line + "\n")


def done_keys():
    keys = set()
    if JSONL.exists():
        with open(JSONL, encoding="utf-8") as f:
            for line in f:
                try:
                    keys.add(json.loads(line)["key"])
                except Exception:
                    pass
    return keys


def append(rec):
    with open(JSONL, "a", encoding="utf-8") as f:
        f.write(json.dumps(rec) + "\n")


def nodes(n):
    return [(1 + mp.cos(mp.pi * (2 * i + 1) / (2 * n))) / 2 for i in range(n)]


def rho(S, B, m, s, n):
    """Spectral radius of the n-point collocation of L_s for the alphabet A_{m,S,B}."""
    xs = nodes(n)
    M = matrix(n, n)
    V = matrix(n, n)
    k0s = [-(-(b + 1) // m) for b in B]  # ceil((b+1)/m)
    for i, x in enumerate(xs):
        for j in range(n):
            p = 2 * s + j
            tot = mpf(0)
            for r in S:
                tot += mpf(m) ** (-p) * zeta(p, (mpf(r) + x) / m)
            for b, k0 in zip(B, k0s):
                tot += mpf(m) ** (-p) * zeta(p, mpf(k0) + (x - b) / m)
            M[i, j] = tot
            V[i, j] = x ** j
    A = M * V ** -1
    return max(abs(e) for e in eig(A, left=False, right=False))


def rho_finite(S, s, n):
    """Spectral radius of the collocation of the finite-alphabet operator L^S_s (for s_0(S))."""
    xs = nodes(n)
    M = matrix(n, n)
    V = matrix(n, n)
    for i, x in enumerate(xs):
        for j in range(n):
            p = 2 * s + j
            M[i, j] = sum((mpf(a) + x) ** (-p) for a in S)
            V[i, j] = x ** j
    A = M * V ** -1
    return max(abs(e) for e in eig(A, left=False, right=False))


def bisect(f, lo, hi, iters):
    assert f(lo) > 0 > f(hi), ("no sign change", lo, hi)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def dim_est(S, B, m, n, center):
    """Root of rho(s)=1; rho is decreasing in s with a pole at s=1/2+ (zeta pole)."""
    f = lambda s: rho(S, B, m, s, n) - 1
    lo = max(mpf("0.5") + mpf("1e-9"), mpf(center) - mpf("0.03"))
    hi = mpf(center) + mpf("0.12")
    if not (f(lo) > 0 > f(hi)):
        lo, hi = mpf("0.5") + mpf("1e-9"), mpf("1.5")
    return bisect(f, lo, hi, 56)


def s0_est(S, n):
    f = lambda s: rho_finite(S, s, n) - 1
    return bisect(f, mpf("1e-6"), mpf("1.5"), 60)


# ---------------- workers ----------------
def job_self(args):
    m, r, n = args
    mp.dps = DPS
    t = time.time()
    d = dim_est([r], [], m, n, "0.5")
    lo, hi = BRACKETS[(m, r)]
    inside = mpf(lo.numerator) / lo.denominator < d < mpf(hi.numerator) / hi.denominator
    rec = {"stage": "selfcheck", "key": f"self|m={m}|r={r}|n={n}", "m": m, "r": r, "n": n,
           "dim": str(d), "lower": str(float(lo)), "upper": str(float(hi)),
           "inside_open_bracket": bool(inside), "secs": round(time.time() - t, 1)}
    append(rec)
    return rec


def job_s0(args):
    S, n = args
    mp.dps = DPS
    t = time.time()
    s0 = s0_est(S, n)
    rec = {"stage": "s0", "key": f"s0|S={S}|n={n}", "S": S, "n": n, "s0": str(s0),
           "s0_minus_half": str(s0 - mpf("0.5")), "secs": round(time.time() - t, 1)}
    append(rec)
    return rec


def job_dim(args):
    S, B, m, n, center = args
    mp.dps = DPS
    t = time.time()
    d = dim_est(S, B, m, n, center)
    rec = {"stage": "scan", "key": f"scan|S={S}|B={B}|m={m}|n={n}", "S": S, "B": B, "m": m, "n": n,
           "center": center, "dim": str(d), "delta": str(d - mpf(center)), "secs": round(time.time() - t, 1)}
    append(rec)
    return rec


def pool_map(fn, jobs, tag):
    workers = max(1, min(cpu_count() - 1, 8))
    log(f"{tag}: {len(jobs)} jobs on {workers} workers")
    results = []
    with Pool(workers) as pool:
        for rec in pool.imap_unordered(fn, jobs):
            results.append(rec)
            log(f"  done {rec['key']} -> {rec.get('dim', rec.get('s0'))} ({rec['secs']}s)")
    return results


def words_series(S, s, nmax):
    """Brute-force W_S(2s,n) = sum_{w in S^n} q(w)^{-2s} for n <= nmax via the continuant recurrence
    q_k = a_k q_{k-1} + q_{k-2} (q_0 = 1 for the empty word, q_1 = a_1).  State after k letters:
    (q_{k-1}, q_k) -> number of words."""
    p = 2 * s
    cur = {}
    for a in S:
        cur[(1, a)] = cur.get((1, a), 0) + 1
    out = [(1, sum(mpf(c) * mpf(qc) ** (-p) for (_, qc), c in cur.items()))]
    for n in range(2, nmax + 1):
        nxt = {}
        for (qm, qc), c in cur.items():
            for a in S:
                qn = a * qc + qm
                nxt[(qc, qn)] = nxt.get((qc, qn), 0) + c
        cur = nxt
        out.append((n, sum(mpf(c) * mpf(qc) ** (-p) for (_, qc), c in cur.items())))
    return out


def stage_xcheck(S, s_list, nmax):
    mp.dps = DPS
    for s in s_list:
        ser = words_series(S, s, nmax)
        ratios = [str(ser[i + 1][1] / ser[i][1])[:12] for i in range(len(ser) - 4, len(ser) - 1)]
        rec = {"stage": "xcheck", "key": f"xcheck|S={S}|s={s}|nmax={nmax}", "S": S, "s": s,
               "tail_ratios_W(n+1)/W(n)": ratios, "W_last": str(ser[-1][1])[:16]}
        append(rec)
        log(f"  xcheck S={S} s={s}: tail ratios {ratios}")
    return True


def main():
    stage = sys.argv[1] if len(sys.argv) > 1 else "selfcheck"
    skip = done_keys()
    log(f"=== stage {stage} (resume: {len(skip)} keys already done) ===")
    if stage == "selfcheck":
        n = 16
        jobs = [(m, r, n) for (m, r) in BRACKETS if f"self|m={m}|r={r}|n={n}" not in skip]
        res = pool_map(job_self, jobs, "selfcheck")
        bad = [r for r in res if not r["inside_open_bracket"]]
        log(f"selfcheck: {len(res)} done, {len(bad)} OUTSIDE bracket" + (f" -> {bad}" if bad else ""))
    elif stage == "s0":
        n = 24
        jobs = [(S, n) for S in S0_FAMILIES if f"s0|S={S}|n={n}" not in skip]
        pool_map(job_s0, jobs, "s0")
        rows = []
        with open(JSONL, encoding="utf-8") as f:
            for line in f:
                rec = json.loads(line)
                if rec.get("stage") == "s0" and rec.get("n") == n:
                    rows.append(rec)
        rows = sorted(rows, key=lambda r: abs(float(r["s0_minus_half"])))
        log(f"s0 table ({len(rows)} sets, n={n}) sorted by |s0-1/2|:")
        for r in rows:
            log(f"  S={str(r['S']):<24} s0={r['s0'][:12]}  s0-1/2={r['s0_minus_half'][:12]}")
    elif stage == "xcheck":
        S = [int(t) for t in sys.argv[2].split(",")]
        s_list = [sys.argv[3], sys.argv[4], sys.argv[5]]
        stage_xcheck(S, s_list, int(sys.argv[6]) if len(sys.argv) > 6 else 12)
    elif stage == "scan":
        cfg = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
        jobs = []
        for fam in cfg["sets"]:
            S, B = fam["S"], fam.get("B", [])
            center = mpf(fam["center"])
            for m in cfg["m_list"]:
                key = f"scan|S={S}|B={B}|m={m}|n={cfg['n']}"
                if key not in skip:
                    jobs.append((S, B, m, cfg["n"], str(center)))
            for m in cfg.get("n_check_m", []):
                n2 = cfg.get("n_check", 24)
                key = f"scan|S={S}|B={B}|m={m}|n={n2}"
                if key not in skip:
                    jobs.append((S, B, m, n2, str(center)))
        res = pool_map(job_dim, jobs, "scan")
        log(f"scan: {len(res)} new points")
    else:
        raise SystemExit("unknown stage")


if __name__ == "__main__":
    main()
