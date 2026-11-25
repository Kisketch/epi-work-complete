from mpmath import mp, mpf, log, floor, ceil
import random
mp.dps = 80
Q = [1, 1]
for j in range(1, 400):
    Q.append((4*j+2)*Q[j]+Q[j-1])
print("Q:", Q[:6])
print("ratio in [4j+2,4j+3] all 1<=j<=398:", all(4*j+2 <= mpf(Q[j+1])/Q[j] <= 4*j+3 for j in range(1, 399)))
C = mpf(1)/8
def ell(j, t):
    return 2*C*(mpf(Q[j+1])/Q[j]*mpf(j)**(-t)-mpf(j+1)**(-t))
print("(ii) j^{-(1-t)} * ell_j, C=1/8")
for t in [mpf('0.1'), mpf('0.5'), mpf('0.9'), mpf('0.99')]:
    print(t, [mp.nstr(ell(j, t)/mpf(j)**(1-t), 10) for j in (1, 2, 5, 10, 100, 300, 398)])
print("min over j in 1..390, tau in {0,.03,..,.99} of ell_j/j^(1-tau):",
      mp.nstr(min(ell(j, mpf(t)/100)/mpf(j)**(1-mpf(t)/100) for j in range(1, 391) for t in range(0, 100, 3)), 12))
print("ell_j>=(j+1/4)j^-tau all tested:",
      all(ell(j, mpf(t)/100) >= (j+mpf(1)/4)*mpf(j)**(-mpf(t)/100) for j in range(1, 391) for t in range(0, 100, 3)))
print("r_{j+1}/r_j <= 1/(4j+2) all tested:",
      all((mpf(j)/(j+1))**(mpf(t)/100)*mpf(Q[j])/Q[j+1] <= mpf(1)/(4*j+2) for j in range(1, 391) for t in range(0, 100, 3)))
def count(a, L):
    return int(floor(a+L)-ceil(a)+1)
bad = 0
for _ in range(20000):
    a = mpf(random.random())*1000
    L = mpf(random.random())*30
    c = count(a, L)
    if not (c in (int(floor(L)), int(floor(L))+1) and c >= L-1):
        bad += 1
print("(i) count in {floor L, floor L+1} and >= L-1: violations", bad)
t = mpf('0.5')
for j in (3, 5, 8, 12, 20, 40):
    mn = 10**9
    mx = 0
    for k in [1, 2, Q[j]//3, Q[j]//2, Q[j]-1]:
        cen = mpf(k)/Q[j]
        r = C*mpf(j)**(-t)/Q[j]
        r1 = C*mpf(j+1)**(-t)/Q[j+1]
        lo = (cen-r+r1)*Q[j+1]
        hi = (cen+r-r1)*Q[j+1]
        c = count(lo, hi-lo)
        mn = min(mn, c)
        mx = max(mx, c)
    print("j", j, "ell", mp.nstr(ell(j, t), 8), "child count range", mn, mx, "ell-1", mp.nstr(ell(j, t)-1, 8))
print("(iii) max_n 2 r_n Q_n (tau=.5, n 1..49) =", max(2*C*mpf(n)**(-t) for n in range(1, 50)))
print("(v) (logQ_j - j log j)/j:", [mp.nstr((log(Q[j])-j*log(j))/j, 8) for j in (10, 50, 100, 300, 398)], "log4-1 =", mp.nstr(log(4)-1, 8))
# (vi) exact: min length of interval meeting 3 level-n intervals vs 1/Q_n
for n in (2, 3, 5, 10):
    for tt in (mpf(0), mpf('0.5')):
        r = C*mpf(n)**(-tt)/Q[n]
        minlen3 = (2/mpf(Q[n]) - 2*r)*Q[n]
        print("(vi) n", n, "tau", tt, "min length (x Q_n) of closed interval meeting 3 grid intervals =", mp.nstr(minlen3, 8), " > 1 ?", minlen3 > 1)
def thr(t, s, c=mpf(1)/2):
    N = int((2/c)**(1/(1-t)))+1
    logM = mpf(0)
    res = []
    for n in range(N, 398):
        if n > N:
            logM += log(floor(c*mpf(n-1)**(1-t)))
        res.append((n, log(3)-logM <= -s*log(Q[n+1])))
    bad = [n for n, o in res if not o]
    return N, (max(bad) if bad else None)
for t, s in [(mpf('0.5'), mpf('0.4')), (mpf('0.5'), mpf('0.49')), (mpf('0.3'), mpf('0.6'))]:
    print("(vii) tau,s", t, s, "N, last failing n (<398):", thr(t, s))
