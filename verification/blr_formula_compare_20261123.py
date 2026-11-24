"""Compare BLR (arXiv:1710.03596) Theorem 7 delta-form dimension formula, evaluated for
f_n(x)=Q_n x and delta_n = c * w_n, with paper 2's subcritical dimension formulas.
BLR ratio_n = (log Q_n + sum_{j<n} log delta_j) / (log Q_n - log delta_n); dim = liminf ratio_n.
Exact recurrences in integers; logs in mpmath (60 digits). Finite n only: indicates the limit,
proves nothing."""
from mpmath import mp, mpf, log
mp.dps = 60

def ratios(A, w, c, n_max):
    Q_prev, Q = 1, 1
    S, out = mpf(0), []
    for n in range(1, n_max + 1):
        Q_prev, Q = Q, A(n) * Q + Q_prev          # Q_{n+1} = A_n Q_n + Q_{n-1}
        lq = log(mpf(Q))
        dn = c * w(n + 1)
        out.append((n + 1, (lq + S) / (lq - log(dn))))
        S += log(c * w(n + 1))
    return out

cases = [
  ("e-type A_j=4j+2, alpha=0.5 (expect 1-alpha=0.5)", lambda j: 4*j+2, lambda j: mpf(j)**-0.5, 3999),
  ("poly r=2: A_j=j^2+1, alpha=0.5 (expect 1-alpha/r=0.75)", lambda j: j*j+1, lambda j: mpf(j)**-0.5, 3999),
  ("double-exp A_j=2^(2^j), tau=0.5 (expect (1-tau)/(1+tau*gamma)=1/3, gamma=1)", lambda j: 2**(2**j), None, 17),
]
for name, A, w, nmax in cases:
    if w is None:  # delta_j = c * A_j^{-tau}
        tau = mpf("0.5")
        r = ratios(A, lambda j: mpf(A(j)) ** -tau, mpf("0.25"), nmax)   # delta_m = c * A_m^{-tau}
    else:
        r = ratios(A, w, mpf("0.25"), nmax)
    marks = [n for n in (5, 10, 15, 18, 100, 1000, 4000) if n <= nmax + 1]
    d = dict(r)
    print(name, "|", ", ".join(f"n={n}: {float(d[n]):.6f}" for n in marks if n in d))
