"""reaudit_S2_1: verbatim comparison of proofs/R6-S2.md section 0 against PLAN_GRAPH.md (current).

Checks:
  (a) each of the S.1 bullet items (top-level '- ' lines inside '### S.1') appears verbatim in proof section 0.1;
  (b) R6-S1 header line and its (a)-(d) sub-bullets appear verbatim in proof section 0.2;
  (c) R6-S2 header line appears verbatim in 0.3; the calibration sub-bullet is compared up to the
      prover's explicit '……' truncation (reported, not silently accepted).
  (d) order of the S.1 items is preserved.
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
pg = (ROOT / "PLAN_GRAPH.md").read_text(encoding="utf-8").splitlines()
pr = (ROOT / "proofs" / "R6-S2.md").read_text(encoding="utf-8").splitlines()

def section(lines, start_pat, stop_pat):
    out, on = [], False
    for ln in lines:
        if re.match(start_pat, ln):
            on = True; continue
        if on and re.match(stop_pat, ln):
            break
        if on:
            out.append(ln)
    return out

s1 = section(pg, r"^### S\.1", r"^### ")
s1_items = [ln for ln in s1 if ln.startswith("- ")]
s2sec = section(pg, r"^### S\.2", r"^### ")

# proof section 0 (until first '---' after '## 0.')
p0 = section(pr, r"^## 0\. ", r"^---\s*$")
p01 = section(pr, r"^### 0\.1", r"^### ")
p02 = section(pr, r"^### 0\.2", r"^### ")
p03 = section(pr, r"^### 0\.3", r"^### ")

ok = True
print("S.1 items in PLAN_GRAPH:", len(s1_items))
p01_items = [ln for ln in p01 if ln.startswith("- ")]
print("top-level items in proof 0.1:", len(p01_items))
for i, it in enumerate(s1_items):
    hit = it in p01
    print(f"  S.1 item {i+1}: verbatim_in_0.1={hit}  pos_in_0.1={p01_items.index(it)+1 if it in p01_items else None}")
    ok &= hit
order = [p01_items.index(it) for it in s1_items if it in p01_items]
print("  order preserved:", order == sorted(order))
ok &= order == sorted(order)
extra = [ln for ln in p01_items if ln not in s1_items]
print("  extra top-level items in 0.1 not in S.1:", len(extra))

# R6-S1
i1 = next(i for i, ln in enumerate(s2sec) if ln.startswith("- **R6-S1"))
s1_block = [s2sec[i1]]
for ln in s2sec[i1 + 1:]:
    if ln.startswith("  - ") and not ln.startswith("  - 推导要点"):
        s1_block.append(ln)
    elif ln.startswith("  - 推导要点"):
        continue
    else:
        break
print("\nR6-S1 lines in PLAN_GRAPH (excluding strategist note):", len(s1_block))
for ln in s1_block:
    hit = ln in p02
    print(f"  verbatim_in_0.2={hit} :: {ln[:60]}...")
    ok &= hit

# R6-S2
i2 = next(i for i, ln in enumerate(s2sec) if ln.startswith("- **R6-S2"))
hdr = s2sec[i2]
print("\nR6-S2 header verbatim in 0.3:", hdr in p03)
ok &= hdr in p03
cal = s2sec[i2 + 1]
pcal = next(ln for ln in p03 if ln.startswith("  - 校准"))
prefix = pcal.split("……")[0]
print("R6-S2 calibration sub-bullet: proof truncates with '……':", "……" in pcal)
print("  proof prefix is a verbatim prefix of PLAN_GRAPH sub-bullet:", cal.startswith(prefix))
print("  PLAN_GRAPH sub-bullet length:", len(cal), " proof prefix length:", len(prefix))
print("  omitted tail:", repr(cal[len(prefix):][:200]))

# Proof's assumed label definition and statement's definition agree
lab_pg = re.search(r"r_k=r_k\(\\beta\):=\\operatorname\{round\}\(K\\,y_\{n_k\+1\}\)\\bmod K", "\n".join(s1_block))
lab_pr = re.search(r"r_k=r_k\(\\beta\):=\\operatorname\{round\}\(K\\,y_\{n_k\+1\}\)\\bmod K", "\n".join(pr))
print("\ncanonical label formula present in PLAN_GRAPH S1:", bool(lab_pg), " in proof:", bool(lab_pr))
print("\nOVERALL verbatim (S.1 items, S1 statement, S2 header):", ok)
