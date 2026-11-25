from mpmath import mp, mpf, log
import math
import numpy as np
mp.dps = 30
Q = [1, 1]
for j in range(1, 60):
    Q.append((4*j+2)*Q[j]+Q[j-1])
print(Q[:5])
for n in range(2, 60):
    lq = math.log(Q[n])
    assert lq >= n*math.log(n)+(math.log(4)-1)*n-math.log(4*n)
    assert all(4*j+2 <= Q[j+1]/Q[j] <= 4*j+3 for j in range(1, n))
    assert Q[n] <= 7**n*math.factorial(n)
print("sec0 ok")
for tau in [0.1, 0.3, 0.5, 0.7, 0.9]:
    for j in range(1, 40):
        rj = mpf(j)**-tau/(8*Q[j]); rj1 = mpf(j+1)**-tau/(8*Q[j+1])
        l = 2*(rj-rj1)*Q[j+1]
        assert rj > rj1 and l > mpf(j)**(1-tau)
print("lower ok")
# n0 for tau=.5, s=.4, N=16 (= 4^{1/(1-tau)})
M = 3_000_000
N = 16
lq = np.zeros(M+2)
ratio = 1.0
for j in range(1, M+1):
    rho = 4*j+2+ratio
    lq[j+1] = lq[j]+math.log(rho)
    ratio = 1.0/rho
b = np.floor(np.arange(M+1, dtype=float)**0.5/2)
assert b[N] >= 2
logb = np.log(b[1:]) if False else np.log(np.maximum(b, 1))
cs = np.cumsum(logb)
# logM[n] = sum_{j=N}^{n-1} logb[j]
ns = np.arange(N, M)
logM = cs[ns-1]-cs[N-1]
f = math.log(2)-logM+0.4*lq[ns+1]
idx = np.where(f > 0)[0]
print("last n with f>0:", ns[idx.max()] if len(idx) else None)
