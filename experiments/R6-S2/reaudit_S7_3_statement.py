#!/usr/bin/env python3
"""Re-audit S7: compare the proof's verbatim-quoted source statement with PLAN_GRAPH.md."""
import difflib, os
root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
pg = open(os.path.join(root, 'PLAN_GRAPH.md'), encoding='utf8').read().splitlines()
pr = open(os.path.join(root, 'proofs', 'R6-S7-mstar.md'), encoding='utf8').read()
q = [l for l in pr.splitlines() if l.startswith('> 结构性发现')][0][2:]
p = [l for l in pg if '结构性发现' in l][0]
diffs = [(op, p[a:b], q[c:d]) for op, a, b, c, d in difflib.SequenceMatcher(None, p, q).get_opcodes() if op != 'equal']
print('non-equal segments:', diffs)
print('only markdown markers differ:', all(set(x + y) <= set('-* ') for _, x, y in diffs))
