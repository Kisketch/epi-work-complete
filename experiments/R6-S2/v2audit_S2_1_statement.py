"""v2audit_S2_1: verbatim comparison of proofs/R6-S2.md §0 against PLAN_GRAPH.md §S.1/§S.2.
Self-written by the v2 skeptic; reads only PLAN_GRAPH.md S.1/S.2 and proofs/R6-S2.md."""
import os, re, difflib
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
pg = open(os.path.join(ROOT, "PLAN_GRAPH.md"), encoding="utf-8").read().splitlines()
pf = open(os.path.join(ROOT, "proofs", "R6-S2.md"), encoding="utf-8").read().splitlines()

def section(lines, start_pat, end_pat):
    i = next(k for k, l in enumerate(lines) if l.startswith(start_pat))
    j = next(k for k in range(i + 1, len(lines)) if lines[k].startswith(end_pat))
    return lines[i + 1:j]

S1 = [l for l in section(pg, "### S.1", "### S.2") if l.strip()]
S2 = [l for l in section(pg, "### S.2", "### S.3") if l.strip()]
P01 = [l for l in section(pf, "### 0.1", "### 0.2") if l.strip()]
P02 = [l for l in section(pf, "### 0.2", "### 0.3") if l.strip()]
P03 = [l for l in section(pf, "### 0.3", "### 0.4") if l.strip()]

def report(name, a, b):
    print(f"== {name}: PLAN_GRAPH {len(a)} lines vs proof {len(b)} lines")
    same = True
    for l in difflib.unified_diff(a, b, "PLAN_GRAPH", "proof", lineterm="", n=0):
        same = False
        print("   ", l[:260])
    print("   IDENTICAL" if same else "   DIFFERENCES ABOVE")

# S.1: 7 bullets
print("S.1 bullet count in PLAN_GRAPH:", sum(1 for l in S1 if l.startswith("- ")))
report("S.1 vs proof 0.1 (raw)", S1, P01)
P01_stripped = [l for l in P01 if not l.lstrip().startswith("- （prover 注")]
report("S.1 vs proof 0.1 (prover note removed)", S1, P01_stripped)

# S1 bullet + (a)-(d), excluding 推导要点
i = next(k for k, l in enumerate(S2) if l.startswith("- **R6-S1"))
j = next(k for k, l in enumerate(S2) if l.startswith("- **R6-S2"))
S1stmt = [l for l in S2[i:j] if "推导要点" not in l]
P02stmt = [l for l in P02 if l.startswith("- **R6-S1") or l.startswith("  - (")]
report("R6-S1 (minus 推导要点) vs proof 0.2", S1stmt, P02stmt)
S1_extra = [l for l in S2[i:j] if "推导要点" in l]
print("   omitted PLAN_GRAPH lines:", [l[:60] for l in S1_extra])

k2 = next(k for k, l in enumerate(S2) if l.startswith("- **R6-S3"))
S2stmt = S2[j:k2]
report("R6-S2 main sentence", S2stmt[:1], P03[:1])
print("== R6-S2 calibration sub-bullet")
print("   PLAN_GRAPH:", S2stmt[1])
print("   proof     :", P03[1])
pref = P03[1].split("……")[0]
print("   proof prefix (before ……) is a prefix of PLAN_GRAPH line:", S2stmt[1].startswith(pref))
print("   PLAN_GRAPH remainder dropped by proof:", S2stmt[1][len(pref):])
