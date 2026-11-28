# reaudit3 (R6-S2, Step 4, round-3 re-audit), script 1: verbatim statement comparison.
# Compares proofs/R6-S2.md Sec.0 with PLAN_GRAPH.md (S.1 definitions, R6-S1, R6-S2) line by line.
import os, re, sys
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
pg = open(os.path.join(ROOT, 'PLAN_GRAPH.md'), encoding='utf-8').read().splitlines()
pf = open(os.path.join(ROOT, 'proofs', 'R6-S2.md'), encoding='utf-8').read().splitlines()

def section(lines, start_pat, end_pat):
    s = next(i for i, l in enumerate(lines) if l.startswith(start_pat))
    e = next(i for i in range(s + 1, len(lines)) if lines[i].startswith(end_pat))
    return s, e

# PLAN_GRAPH S.1 bullets
s, e = section(pg, '### S.1', '### S.2')
pg_s1 = [l for l in pg[s+1:e] if l.startswith('- ')]
# proof 0.1 bullets (top-level only)
s2, e2 = section(pf, '### 0.1', '### 0.2')
pf_s1 = [l for l in pf[s2+1:e2] if l.startswith('- ')]
print('S.1 bullets: PLAN_GRAPH', len(pg_s1), ' proof', len(pf_s1))
ok = True
for i, (a, b) in enumerate(zip(pg_s1, pf_s1)):
    same = (a == b)
    ok &= same
    print(f'  S.1 item {i+1}: {"IDENTICAL" if same else "DIFFERENT"}')
    if not same:
        for j, (x, y) in enumerate(zip(a, b)):
            if x != y:
                print('    first diff at char', j, repr(a[j-20:j+40]), '|', repr(b[j-20:j+40])); break
ok &= len(pg_s1) == len(pf_s1)

# R6-S1 statement: header + (a)-(d)
def block(lines, head):
    i = next(k for k, l in enumerate(lines) if l.startswith(head))
    out = [lines[i]]
    j = i + 1
    while j < len(lines) and lines[j].startswith('  - '):
        out.append(lines[j]); j += 1
    return out
pg_S1 = block(pg, '- **R6-S1')
pf_S1 = block(pf, '- **R6-S1')
# PLAN_GRAPH S1 has an extra sub-bullet "推导要点" which the proof explicitly omits
pg_S1_core = [l for l in pg_S1 if '推导要点' not in l]
print('R6-S1 lines: PLAN_GRAPH(core)', len(pg_S1_core), ' proof', len(pf_S1))
for i, (a, b) in enumerate(zip(pg_S1_core, pf_S1)):
    same = a == b; ok &= same
    print(f'  S1 line {i}: {"IDENTICAL" if same else "DIFFERENT"}')
ok &= len(pg_S1_core) == len(pf_S1)

pg_S2 = block(pg, '- **R6-S2')
pf_S2 = block(pf, '- **R6-S2')
same = pg_S2[0] == pf_S2[0]; ok &= same
print('R6-S2 main sentence:', 'IDENTICAL' if same else 'DIFFERENT')
# calibration sub-bullet: proof abbreviates with '……'; check its prefix is a verbatim prefix
cal_pg = pg_S2[1]; cal_pf = pf_S2[1]
prefix = cal_pf.split('……')[0]
pre_ok = cal_pg.startswith(prefix)
print('R6-S2 calibration: proof prefix is verbatim prefix of PLAN_GRAPH line:', pre_ok)
ok &= pre_ok
print('ALL STATEMENT CHECKS', 'PASSED' if ok else 'FAILED')
