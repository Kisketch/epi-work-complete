import numpy as np
from math import lgamma, log
# log Q_{n+1} <= sum_{j=1}^n log(4j+3) = n log4 + lgamma(n+1+3/4) - lgamma(7/4)   (rigorous upper bound, Q_2/Q_1=7=4+3)
def logQ_up(n):
    return n*log(4) + lgamma(n+1+0.75) - lgamma(1.75)
def run(t, s, c=0.5, nmax=3*10**7):
    N = int((2/c)**(1/(1-t)))+1
    j = np.arange(N, nmax, dtype=np.float64)
    b = np.floor(c*j**(1-t))
    assert b.min() >= 2
    logM = np.concatenate(([0.0], np.cumsum(np.log(b))))  # logM[k] = log M_{N+k}
    n = np.arange(N, N+len(logM), dtype=np.float64)
    lq = n*log(4) + np.vectorize(lgamma)(n+1.75) - lgamma(1.75)
    ok = (log(3) - logM) <= -s*lq
    bad = np.where(~ok)[0]
    return N, int(n[bad[-1]]) if len(bad) else None, bool(ok[-1]), float(n[-1])
for t, s in [(0.5, 0.2), (0.5, 0.3), (0.5, 0.4), (0.3, 0.5)]:
    print("tau", t, "s", s, "(N, last failing n, holds at last n tested, n_max):", run(t, s, nmax=6*10**6))
