"""R6-S2 T1c (skeptic addition, exploratory, category 4): search for small m*(W) := min_{r!=0} v(r).
Fact used (elementary, from the definition): every edge has minimal |t| <= 1/2, so if m* >= 1/2 then
nu(W) = min(1, m*) exactly (self-loop at an argmin r).  Hence nu < 1/2 requires m* < 1/2.
Random words + word-level local search; exact value of the best re-derived with Fractions via nu()."""
import random, time
import numpy as np
from fractions import Fraction
from common import vertex_costs, nu, cont
random.seed(7); t0 = time.time()
def mstar(W):
    K, s, num, den = vertex_costs(W)
    if K == 1: return 2.0
    return float((num[1:] / den[1:]).min())
best = (9, None); seen = 0
for _ in range(20000):
    l = random.randint(1, 14); W = tuple(random.choice([1,1,1,2,2,3,4,5,6,8,10]) for _ in range(l))
    if cont(W) > 3_000_000: continue
    m = mstar(W); seen += 1
    if m < best[0]: best = (m, W)
# local search on words
cur = best
for it in range(3000):
    W = list(cur[1]); op = random.random()
    if op < 0.4 and W: W[random.randrange(len(W))] = random.randint(1, 12)
    elif op < 0.7: W.insert(random.randrange(len(W)+1), random.randint(1, 6))
    elif len(W) > 1: W.pop(random.randrange(len(W)))
    W = tuple(W)
    if cont(W) > 3_000_000: continue
    m = mstar(W)
    if m <= cur[0]: cur = (m, W)
n, wit, ms = nu(cur[1])
lines = [f"random words: {seen}; best m* (float) {best[0]:.6f} at {best[1]}",
         f"after local search: m* = {cur[0]:.8f} at W={cur[1]} K={cont(cur[1])}; exact nu = {n} ({float(n):.8f}), witness {wit}",
         f"elapsed {time.time()-t0:.1f}s"]
print("\n".join(lines)); open("R6_R6-S2_T1c_mstar_search.out","w").write("\n".join(lines)+"\n")
