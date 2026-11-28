"""reaudit2 (R6-S2, repair round 2): verbatim comparison of proofs/R6-S2.md sec 0 vs PLAN_GRAPH.md.
Self-written by isolated skeptic. Exact string comparison, line by line."""
import re, sys, difflib
ROOT = sys.argv[1] if len(sys.argv) > 1 else '.'
pg = open(f'{ROOT}/PLAN_GRAPH.md', encoding='utf-8').read().splitlines()
pf = open(f'{ROOT}/proofs/R6-S2.md', encoding='utf-8').read().splitlines()

def section(lines, start_pat, end_pat):
    i = next(k for k, s in enumerate(lines) if re.match(start_pat, s))
    j = next(k for k in range(i + 1, len(lines)) if re.match(end_pat, lines[k]))
    return lines[i + 1:j]

def bullets(block):
    """group into top-level bullets ('- ' at col 0) with their sub-lines."""
    out, cur = [], None
    for s in block:
        if s.startswith('- '):
            if cur is not None: out.append(cur)
            cur = [s]
        elif cur is not None and s.strip():
            cur.append(s)
    if cur is not None: out.append(cur)
    return out

ok = True
# S.1 notation
pg_s1 = bullets(section(pg, r'^### S\.1 ', r'^### S\.2 '))
pf_s1 = bullets(section(pf, r'^### 0\.1 ', r'^### 0\.2 '))
# strip the prover note sub-bullet (declared non-verbatim)
pf_s1 = [[s for s in b if not s.strip().startswith('- （prover 注')] for b in pf_s1]
print('S.1 bullets: PLAN_GRAPH', len(pg_s1), ' proof', len(pf_s1))
if len(pg_s1) != len(pf_s1): ok = False
for a, b in zip(pg_s1, pf_s1):
    eq = a == b
    print('  S.1 bullet', a[0][:30].encode('unicode_escape')[:40], 'EQUAL' if eq else 'DIFF')
    if not eq:
        ok = False
        for d in difflib.unified_diff(a, b, lineterm=''): print('    ', d)

pg_s2 = section(pg, r'^### S\.2 ', r'^### S\.3 ')
def get_bullet(lines, prefix):
    i = next(k for k, s in enumerate(lines) if s.startswith(prefix))
    blk = [lines[i]]
    for s in lines[i + 1:]:
        if s.startswith('  - '): blk.append(s)
        else: break
    return blk
S1pg = get_bullet(pg_s2, '- **R6-S1')
S2pg = get_bullet(pg_s2, '- **R6-S2')
sec02 = section(pf, r'^### 0\.2 ', r'^### 0\.3 ')
sec03 = section(pf, r'^### 0\.3 ', r'^### 0\.4 ')
S1pf = get_bullet(sec02, '- **R6-S1')
S2pf = get_bullet(sec03, '- **R6-S2')
# S1: PLAN_GRAPH has trailing '推导要点' sub-bullet, declared omitted in proof
S1pg_stmt = [s for s in S1pg if not s.startswith('  - 推导要点')]
print('S1 main+(a)-(d): lines PLAN_GRAPH', len(S1pg_stmt), 'proof', len(S1pf), 'EQUAL' if S1pg_stmt == S1pf else 'DIFF')
if S1pg_stmt != S1pf:
    ok = False
    for d in difflib.unified_diff(S1pg_stmt, S1pf, lineterm=''): print('    ', d)
print('S1 omitted sub-bullets in proof:', [s[:12] for s in S1pg if s not in S1pf])
# S2: main bullet must be identical; calibration sub-bullet abridged with '……'
print('S2 main bullet', 'EQUAL' if S2pg[0] == S2pf[0] else 'DIFF')
if S2pg[0] != S2pf[0]: ok = False
cal_pg, cal_pf = S2pg[1], S2pf[1]
prefix = cal_pf.split('……')[0]
print('S2 calibration: proof prefix is verbatim prefix of PLAN_GRAPH line:', cal_pg.startswith(prefix), '| prefix len', len(prefix))
if not cal_pg.startswith(prefix): ok = False
print('ALL VERBATIM CHECKS', 'PASSED' if ok else 'FAILED')
