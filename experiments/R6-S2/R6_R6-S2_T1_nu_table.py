"""R6-S2 T1: exact nu(W), nu_0(W) on R1 u R2 u E; gates g1, g2; witnesses.

R1: 0 <= l <= 5, letters in {1..5}.  R2: l <= 10, letters in {1,2}.
E = {(), (1), (1,1), (2), (1,1,1), (2,3), (5,1,5)}.
Exact arithmetic only for every reported/decisive value (Fractions, integer cross-multiplication).
Independent cross-check: O(K^3) bottleneck closure (nu_bruteforce) on every W with K <= 60.
Outputs: R6_R6-S2_T1_nu_table.out (summary), R6_R6-S2_T1_nu_table.tsv (full table).
"""
import itertools, sys, time
from fractions import Fraction
from common import nu, nu0, nu_bruteforce, cont, block_data, walk_cost

t0 = time.time()
E = [(), (1,), (1, 1), (2,), (1, 1, 1), (2, 3), (5, 1, 5)]
R1 = [w for l in range(0, 6) for w in itertools.product(range(1, 6), repeat=l)]
R2 = [w for l in range(0, 11) for w in itertools.product(range(1, 3), repeat=l)]
allW = list(dict.fromkeys(E + R1 + R2))
inR1 = set(R1); inR2 = set(R2)

rows = {}
bf_checked = 0
bf_mismatch = []
for W in allW:
    n, wit, mstar = nu(W)
    n0, orb0, maxorb = nu0(W)
    if wit != "loop0_t=+-1":
        assert walk_cost(W, wit) == n
    K = cont(W)
    if K <= 60:
        b = nu_bruteforce(W)
        bf_checked += 1
        if b != n:
            bf_mismatch.append((W, n, b))
    rows[W] = (K, block_data(W)[3], n, n0, wit, orb0, maxorb, mstar)

out = []
P = out.append
P("R6-S2 T1 exact nu(W) table   (category 4: finite exact computation)")
P(f"#W total = {len(allW)}  (|R1|={len(R1)}, |R2|={len(R2)}, |E|={len(E)}, union deduplicated)")
P(f"independent brute-force cross-check (K<=60): {bf_checked} words, mismatches = {len(bf_mismatch)}")
for m in bf_mismatch[:20]:
    P(f"   MISMATCH {m}")
P("")
P("--- list E ---")
for W in E:
    K, s, n, n0, wit, orb0, maxorb, mstar = rows[W]
    P(f"W={W!s:12} K={K:4d} sigma={s:3d} nu={n!s:6} nu0={n0!s:6} m*={mstar!s:6} witness={wit} nu0-orbit={orb0}")
P("")
g1 = all(rows[W][2] == 1 for W in [(), (1,), (1, 1)])
P(f"gate g1: nu(())={rows[()][2]}, nu((1,))={rows[(1,)][2]}, nu((1,1))={rows[(1,1)][2]}  -> {'PASS' if g1 else 'FAIL'}")
below = [W for W in allW if rows[W][2] < Fraction(1, 4)]
P(f"gate g2: #W with nu(W) < 1/4 : {len(below)}  -> {'PASS' if not below else 'FAIL'}")
P("")
lt1 = [W for W in allW if rows[W][2] < 1]
P(f"#W with nu(W) < 1 : {len(lt1)}  (R1: {sum(1 for W in lt1 if W in inR1)}, R2: {sum(1 for W in lt1 if W in inR2)})")
mn = min(rows[W][2] for W in allW)
am = [W for W in allW if rows[W][2] == mn]
P(f"min nu over range = {mn} = {float(mn):.12f};  #argmin = {len(am)}")
for W in am[:30]:
    K, s, n, n0, wit, orb0, maxorb, mstar = rows[W]
    P(f"   argmin W={W} K={K} sigma={s} nu0={n0} witness={wit}")
for name, S in (("R1", R1), ("R2", R2)):
    mS = min(rows[W][2] for W in S)
    aS = [W for W in S if rows[W][2] == mS]
    P(f"min over {name} = {mS} ({float(mS):.10f}); argmin ({len(aS)}): {aS[:10]}")
# distribution of values
from collections import Counter
cnt = Counter(rows[W][2] for W in allW)
P("value distribution (smallest 25 distinct values: value, count, example W):")
for val in sorted(cnt)[:25]:
    ex = next(W for W in allW if rows[W][2] == val)
    P(f"   {val!s:10} {float(val):.8f}  count={cnt[val]:5d}  e.g. {ex}")
# nu vs nu0 relation
strict = [W for W in allW if rows[W][3] is not None and rows[W][2] < min(rows[W][3], 1)]
P(f"#W with nu(W) < min(1, nu0(W)) (jump walks strictly beat zero-jump walks): {len(strict)}")
for W in strict[:15]:
    P(f"   W={W} nu={rows[W][2]} nu0={rows[W][3]} witness={rows[W][4]}")
mx = max(rows[W][6] or 0 for W in allW)
P(f"max sigma-orbit length over all W = {mx}")
P(f"elapsed {time.time()-t0:.1f}s")

with open("R6_R6-S2_T1_nu_table.tsv", "w") as f:
    f.write("W\tl\tK\tsigma\tnu\tnu_float\tnu0\tmstar\twitness\tmax_sigma_orbit\n")
    for W in allW:
        K, s, n, n0, wit, orb0, maxorb, mstar = rows[W]
        f.write(f"{W}\t{len(W)}\t{K}\t{s}\t{n}\t{float(n):.12f}\t{n0}\t{mstar}\t{wit}\t{maxorb}\n")
with open("R6_R6-S2_T1_nu_table.out", "w") as f:
    f.write("\n".join(out) + "\n")
print("\n".join(out))
