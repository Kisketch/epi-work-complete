"""R6-S7 (prover sanity check, category 4; NOT part of the proof): exact finite check of the steps of the
paper proof of m*(W) >= 1/2 in proofs/R6-S7-mstar.md, and of the consequence nu(W) = min(1, m*(W)).

For every word W in the T1 table (experiments/R6-S2/R6_R6-S2_T1_nu_table.tsv, 5890 words) with K(W) >= 2:
  (L1) gcd(p, K) = 1, p := c'_1 = K(w_2..w_l);
  (L2) c_j == (-1)^(j-1) * lam * c'_j (mod K) for 0 <= j <= l+1, lam := p^{-1} mod K  (c_0 = 0, c'_0 = K,
       c_{l+1} = K, c'_{l+1} = 0);
  (L3) for every r in 1..K-1: with u := centred(lam*r), the index j chosen in the proof
       (j = J-1, J = min{j : c_j > 2|u|}; j = l if no such J) satisfies 2*d_K(c_j r) >= c_j c'_j  (exact ints);
  (L4) m* = min_{r != 0} v(r) >= 1/2 and the tabulated nu equals min(1, m*) (exact Fractions).
All arithmetic is exact integer / Fraction.
"""
from fractions import Fraction
from math import gcd
import ast, csv, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))


def cont(ws):
    a, b = 0, 1
    for w in ws:
        a, b = b, w * b + a
    return b


def dK(x, K):
    x %= K
    return min(x, K - x)


def check(W, nu_tab):
    l = len(W)
    K = cont(W)
    if K < 2:
        return None
    c = [0] + [cont(W[:j - 1]) for j in range(1, l + 1)] + [K]          # c_0..c_{l+1}
    cp = [K] + [cont(W[j:]) for j in range(1, l + 1)] + [0]             # c'_0..c'_{l+1}
    p = cp[1]
    assert gcd(p, K) == 1, ("L1", W)
    lam = pow(p, -1, K)
    for j in range(0, l + 2):
        assert (c[j] - (-1) ** (j - 1) * lam * cp[j]) % K == 0, ("L2", W, j)
    mstar = None
    for r in range(1, K):
        u = (lam * r) % K
        if u > K // 2:
            u -= K
        au = abs(u)
        J = next((j for j in range(1, l + 2) if c[j] > 2 * au), None)
        j = l if J is None else J - 1
        assert 1 <= j <= l, ("L3 index", W, r)
        assert 2 * dK(c[j] * r, K) >= c[j] * cp[j], ("L3", W, r, j)
        v = max(Fraction(dK(c[i] * r, K), c[i] * cp[i]) for i in range(1, l + 1))
        mstar = v if mstar is None else min(mstar, v)
    assert mstar >= Fraction(1, 2), ("L4 mstar", W)
    assert nu_tab == min(Fraction(1), mstar), ("L4 nu", W, nu_tab, mstar)
    return mstar


t0 = time.time()
n_ok = n_skip = 0
glob_min = None
with open(os.path.join(HERE, "R6_R6-S2_T1_nu_table.tsv")) as fh:
    for row in csv.DictReader(fh, delimiter="\t"):
        W = tuple(ast.literal_eval(row["W"]))
        if cont(W) > 20000:          # keep runtime small; O(K*l) per word
            n_skip += 1
            continue
        m = check(W, Fraction(row["nu"]))
        if m is None:
            n_skip += 1
            continue
        n_ok += 1
        if glob_min is None or m < glob_min[0]:
            glob_min = (m, W)
lines = [f"words checked (K>=2, K<=20000): {n_ok}; skipped (K=1 or K>20000): {n_skip}",
         f"L1-L4 all passed; min m* over checked words = {glob_min[0]} = {float(glob_min[0]):.10f} at W={glob_min[1]}",
         f"elapsed {time.time()-t0:.1f}s"]
print("\n".join(lines))
open(os.path.join(HERE, "R6_R6-S7_mstar_lemma_check.out"), "w").write("\n".join(lines) + "\n")
