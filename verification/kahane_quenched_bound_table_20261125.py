"""Compare, at sample (v, eps), three local-dimension values for Kahane's Q6 (research/kahane_q6_note_20261125.md):
  kahane   = log(2 eps (v-2)) / log v          (Kahane 2014, eq. (3), every target sequence; 0 if <= 0)
  quenched = E log f_L(U) / log v, L = 2 eps (v-1), f_L(U) = #(Z cap [U, U+L)), U uniform
           = ((1-{L}) log floor(L) + {L} log ceil(L)) / log v   (Theorem 3, a.e. target sequence)
  conj     = log(2 eps v) / log v                (Kahane's candidate; upper bound for a.e. targets, Thm 2)
"""
import math
print(f"{'v':>6} {'eps':>5} {'kahane':>8} {'quenched':>9} {'conj':>7}")
for v, eps in [(3, .3), (3, .45), (4, .2), (5, .15), (5, .3), (10, .3), (10, .1), (30, .1), (100, .1), (1000, .1)]:
    L = 2 * eps * (v - 1)
    k = math.log(2 * eps * (v - 2)) / math.log(v) if 2 * eps * (v - 2) > 1 else 0.0
    if L >= 1:
        fl, th = math.floor(L), L - math.floor(L)
        q = ((1 - th) * math.log(fl) + th * math.log(fl + 1)) / math.log(v)
    else:
        q = float("nan")
    c = math.log(2 * eps * v) / math.log(v)
    print(f"{v:>6} {eps:>5} {k:8.4f} {q:9.4f} {c:7.4f}")
