"""R6-S2 T1b (skeptic addition, exploratory, category 4): structure of nu on the T1 table and outside it.

(a) From the T1 table: how often is the witness a self-loop; how often nu > m* (edges binding); nu == min(1, m*)?
(b) Families beyond R1 (for S4 orientation only; finite data cannot decide inf_W nu):
    (w,1,1,1,w), (w,1^(2j+1),w), (w,w), (w,1,w) for w up to 40; plus random words l<=8, letters <=12.
"""
import ast, random, time
from fractions import Fraction
from common import nu, nu0, cont

t0 = time.time()
out = []
P = lambda s="": (out.append(s), print(s, flush=True))

rows = []
with open("R6_R6-S2_T1_nu_table.tsv") as fh:
    next(fh)
    for line in fh:
        W, l, K, s, n, nf, n0, ms, wit, mo = line.rstrip("\n").split("\t")
        rows.append((ast.literal_eval(W), Fraction(n), None if ms == "None" else Fraction(ms), wit))
self_loop = sum(1 for r in rows if r[3].startswith("[") and len(ast.literal_eval(r[3])) == 2)
nonself = [r for r in rows if r[3].startswith("[") and len(ast.literal_eval(r[3])) > 2]
eq_m = sum(1 for r in rows if r[2] is not None and r[1] == min(Fraction(1), r[2]))
P(f"(a) T1 table: #W={len(rows)}; witness self-loop: {self_loop}; witness longer cycle: {len(nonself)}; "
  f"loop0(+-1): {sum(1 for r in rows if r[3].startswith('loop0'))}")
P(f"    #W with nu == min(1, m*) (vertex cost alone decides): {eq_m};  #W with nu > m*: "
  f"{sum(1 for r in rows if r[2] is not None and r[1] > min(Fraction(1), r[2]))}")
for r in nonself[:10]:
    P(f"    longer-cycle witness: W={r[0]} nu={r[1]} m*={r[2]} walk={r[3]}")

P("(b) families (nu exact):")
fams = {
    "(w,1,1,1,w)": lambda w: (w, 1, 1, 1, w),
    "(w,1,w)": lambda w: (w, 1, w),
    "(w,w)": lambda w: (w, w),
    "(w,1,1,1,1,1,w)": lambda w: (w, 1, 1, 1, 1, 1, w),
}
for name, fn in fams.items():
    vals = []
    for w in list(range(1, 13)) + [16, 20, 25, 30, 40]:
        W = fn(w)
        n, wit, ms = nu(W)
        vals.append(f"w={w}:{n}({float(n):.4f})")
    P(f"  {name}: " + "  ".join(vals))
random.seed(20261127)
best = (Fraction(2), None)
cnt = 0
for _ in range(3000):
    l = random.randint(1, 8)
    W = tuple(random.randint(1, 12) for _ in range(l))
    if cont(W) > 60000:
        continue
    n, wit, ms = nu(W)
    cnt += 1
    if n < best[0]:
        best = (n, W, wit)
P(f"  random words (l<=8, letters<=12, K<=60000): {cnt} words; min nu = {best[0]} ({float(best[0]):.6f}) at W={best[1]} witness={best[2]}")
P(f"elapsed {time.time()-t0:.1f}s")
with open("R6_R6-S2_T1b_structure.out", "w") as fh:
    fh.write("\n".join(out) + "\n")
