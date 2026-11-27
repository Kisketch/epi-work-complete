"""Audit R6-S2 (Step 4, skeptic): check that proofs/R6-S2.md §0 is a verbatim copy of PLAN_GRAPH.md.

Compares, line by line (exact string equality after stripping trailing whitespace):
  * every bullet of PLAN_GRAPH §S.1  vs  proof §0.1
  * R6-S1 bullet + sub-bullets (a)-(d)  vs  proof §0.2
  * R6-S2 bullet (+ calibration sub-bullet)  vs  proof §0.3
Reports: lines present in PLAN_GRAPH but absent from the proof copy, and vice versa.
"""
import os, re, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
pg = open(os.path.join(ROOT, "PLAN_GRAPH.md"), encoding="utf-8").read().splitlines()
pf = open(os.path.join(ROOT, "proofs", "R6-S2.md"), encoding="utf-8").read().splitlines()


def section(lines, start_pat, end_pat):
    s = next(i for i, x in enumerate(lines) if re.match(start_pat, x))
    e = next(i for i in range(s + 1, len(lines)) if re.match(end_pat, lines[i]))
    return [x.rstrip() for x in lines[s + 1:e] if x.strip()]


pg_S1 = section(pg, r"^### S\.1 ", r"^### S\.2 ")
pg_S2 = section(pg, r"^### S\.2 ", r"^### S\.3 ")
pf_01 = section(pf, r"^### 0\.1 ", r"^### 0\.2 ")
pf_02 = section(pf, r"^### 0\.2 ", r"^### 0\.3 ")
pf_03 = section(pf, r"^### 0\.3 ", r"^### 0\.4 ")


def node_block(lines, tag):
    s = next(i for i, x in enumerate(lines) if x.startswith(f"- **{tag}"))
    out = [lines[s]]
    for x in lines[s + 1:]:
        if x.startswith("- **"):
            break
        out.append(x)
    return out


pg_R1 = node_block(pg_S2, "R6-S1")
pg_R2 = node_block(pg_S2, "R6-S2")

print("=== audit_S2_1: verbatim check of proof §0 against PLAN_GRAPH ===")
for name, a, b in [("S.1 notation vs §0.1", pg_S1, pf_01),
                   ("R6-S1 vs §0.2", pg_R1, pf_02),
                   ("R6-S2 vs §0.3", pg_R2, pf_03)]:
    sa, sb = set(a), set(b)
    miss = [x for x in a if x not in sb]
    extra = [x for x in b if x not in sa]
    print(f"\n--- {name}: PLAN_GRAPH lines={len(a)}, proof lines={len(b)}")
    print(f"identical lines: {len([x for x in a if x in sb])}")
    for x in miss:
        print(f"  [in PLAN_GRAPH, NOT in proof] {x[:160]}{'...' if len(x) > 160 else ''}")
    for x in extra:
        print(f"  [in proof, NOT in PLAN_GRAPH] {x[:160]}{'...' if len(x) > 160 else ''}")
    # for near-misses, show common prefix length
    for x in miss:
        best = max(b, key=lambda y: len(os.path.commonprefix([x, y])))
        cp = len(os.path.commonprefix([x, best]))
        if cp > 20:
            print(f"     nearest proof line shares prefix of {cp}/{len(x)} chars; divergence at: "
                  f"PG='{x[cp:cp+60]}' | proof='{best[cp:cp+60]}'")
