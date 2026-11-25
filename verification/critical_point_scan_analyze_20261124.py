# -*- coding: utf-8 -*-
"""
Diagnostics for critical_point_scan_20261124.jsonl  (类别 4：有限计算，数值佐证，非证明).

Reads the JSONL written by critical_point_scan_20261124.py and prints, per (S, B):
  m, dim, delta = dim - max(1/2, s0(S)), local doubling exponent alpha_loc = log2(delta(m)/delta(2m)),
  m*delta, m^2*delta, m^2*delta/log m  (subcritical diagnostics), and  m^{2 s0} * delta
  (supercritical: should tend to a constant if the Theta(m^{-2 s0}) sandwich is tight),
  plus |dim(n=16) - dim(n=24)| where both exist.  Pure arithmetic on recorded values; nothing is fitted
  beyond the local ratios.  Usage:  .venv\\Scripts\\python.exe verification\\critical_point_scan_analyze_20261124.py
"""
import json
import math
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
JSONL = HERE / "critical_point_scan_20261124.jsonl"


def load():
    s0 = {}
    scan = defaultdict(dict)  # (S,B) -> {(m,n): dim}
    with open(JSONL, encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            if r.get("stage") == "s0" and r.get("n") == 24:
                s0[tuple(r["S"])] = float(r["s0"])
            elif r.get("stage") == "scan":
                scan[(tuple(r["S"]), tuple(r["B"]))][(r["m"], r["n"])] = float(r["dim"])
    return s0, scan


def fmt(x, nd=6):
    return f"{x:.{nd}f}"


def main():
    s0, scan = load()
    print("# Critical-point scan v1 — diagnostics (类别 4, numerical evidence only)\n")
    print("s0(S) used (n=24, finite-alphabet operator root): " + ", ".join(f"{list(S)}→{s0[S]:.6f}" for S in sorted(s0, key=lambda t: (len(t), t)) if list(S) in ([2,3],[1,2],[2,3,4],[3,4,5,6,7],[3,4,5,6,8],[3,4,5,6,9],[3,4,5,6,10],[3,4,5,6,11],[3,4,5,6,12])) + "\n")
    for (S, B), pts in sorted(scan.items(), key=lambda kv: (kv[0][0], kv[0][1])):
        if S not in s0:
            continue
        s = s0[S]
        center = max(0.5, s)
        regime = "SUB" if s < 0.5 else "SUPER"
        rows = sorted((m, n, d) for (m, n), d in pts.items())
        by_m16 = {m: d for (m, n, d) in rows if n == 16}
        ms = sorted(by_m16)
        print(f"\n## S={list(S)}  B={list(B)}  s0={s:.6f}  regime={regime}  center={center:.6f}  (s0-1/2={s-0.5:+.6f})\n")
        print("| m | dim(n=16) | delta=dim-center | alpha_loc (doubling) | m*delta | m^2*delta | m^2*delta/log m | m^{2s0}*delta | n=24 dim | abs(n16-n24) |")
        print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
        for i, m in enumerate(ms):
            d = by_m16[m]
            delta = d - center
            alpha = ""
            if i + 1 < len(ms) and delta > 0 and (by_m16[ms[i + 1]] - center) > 0 and ms[i + 1] == 2 * m:
                alpha = f"{math.log2(delta / (by_m16[ms[i + 1]] - center)):.3f}"
            md = m * delta
            m2d = m * m * delta
            m2dl = m2d / math.log(m) if m > 1 else float("nan")
            m2s0d = (m ** (2 * s)) * delta
            d24 = pts.get((m, 24))
            s24 = f"{d24:.9f}" if d24 is not None else "—"
            diff = f"{abs(d - d24):.1e}" if d24 is not None else "—"
            print(f"| {m} | {d:.9f} | {delta:+.3e} | {alpha} | {md:.4f} | {m2d:.3f} | {m2dl:.3f} | {m2s0d:.4f} | {s24} | {diff} |")
        print()
    print("\nNotes: alpha_loc is the local doubling exponent of delta; a pure K*m^{-a} law gives alpha_loc = a. "
          "For SUB sets the theorem predicts delta = C/(2m) - ..., i.e. alpha_loc -> 1 with m*delta -> C/2. "
          "For SUPER sets the theorem's sandwich is K1*m^{-2 s0} <= delta <= K2*m^{-2 s0}; a tight law would make "
          "m^{2 s0}*delta settle to a constant. All values are from the recorded JSONL; nothing is proved here.")


if __name__ == "__main__":
    main()
