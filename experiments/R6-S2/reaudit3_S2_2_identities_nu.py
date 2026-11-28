# reaudit3 script 2: exact checks of (A1),(A2),(A2a),(A2b), D3, D4, gcd(sigma,K)=1, Lemma B limits,
# nu(W) two independent ways (bottleneck vs brute force closed walks), C1 finiteness, R1 calibration,
# and the remark value nu(5,1,5)=5/6.
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(__file__))
from fractions import Fraction as Fr
from math import gcd
from reaudit3_S2_common import Kc, Kseg, params, dK, vcost, nu, nu_bruteforce

random.seed(20261127)
fails = 0
def chk(cond, msg):
    global fails
    if not cond:
        fails += 1; print('FAIL', msg)

# ---- (A2) split identity for all words len<=6 entries<=4, all split positions
cnt = 0
for m in range(1, 7):
    for x in itertools.product(range(1, 5), repeat=m):
        x = list(x)
        for i in range(1, m + 1):
            lhs = Kc(x)
            left1 = Kc(x[:i-1]); right1 = Kc(x[i-1:])
            left2 = 0 if i - 2 < 0 else Kc(x[:i-2]); right2 = Kc(x[i:])
            chk(lhs == left1 * right1 + left2 * right2, f'A2 {x} i={i}'); cnt += 1
print('(A2) split identity checked:', cnt, 'cases')

# ---- (A2a),(A2b), gcd(sigma,K)=1, c_i,c_i'>=1, sigma>=1
cnt = 0
for l in range(0, 7):
    for W in itertools.product(range(1, 5), repeat=l):
        W = list(W); K, c, cp, s = params(W)
        chk(gcd(s, K) == 1, f'gcd {W}')
        chk(s >= 1 and all(ci >= 1 for ci in c) and all(x >= 1 for x in cp), f'pos {W}')
        for i in range(1, l + 1):
            chk(K == c[i-1] * Kseg(W, i, l) + Kseg(W, 1, i-2) * cp[i-1], f'A2a {W} {i}')
            chk(Kseg(W, i, l) == W[i-1] * Kseg(W, i+1, l) + Kseg(W, i+2, l), f'A2b {W} {i}')
        cnt += 1
print('(A2a),(A2b),gcd checked for', cnt, 'words')

# ---- build a block Hurwitz CF and check (A1), D3, D4 exactly on integers
def cf_seq(a0, head, W, A):
    seq = [a0] + list(head)
    for Ak in A:
        seq += [Ak] + list(W)
    return seq

def convergents(seq):
    p = [1, seq[0]]; q = [0, 1]   # index shift: p[j+1]=p_j ; p[0]=p_{-1}
    for a in seq[1:]:
        p.append(a * p[-1] + p[-2]); q.append(a * q[-1] + q[-2])
    return p, q   # p[n+1] = p_n

for trial in range(60):
    l = random.randint(0, 4); W = [random.randint(1, 6) for _ in range(l)]
    N = random.randint(0, 3); head = [random.randint(1, 5) for _ in range(N)]
    A = [random.choice([1, 2, 3, random.randint(1, 50)]) for _ in range(12)]
    seq = cf_seq(random.randint(-3, 3), head, W, A)
    p, q = convergents(seq)
    P = lambda n: p[n+1]; Q = lambda n: q[n+1]
    nk = lambda k: N + (k-1)*(l+1)
    # positional large indices
    for k in range(1, 12):
        chk(seq[nk(k)+1] == A[k-1], 'position of A_k')
    # (A1) for X=q and X=D(m,.)
    for k in range(1, 11):
        for j in range(0, l+1):
            chk(Q(nk(k)+1+j) == Kseg(W, 1, j)*Q(nk(k)+1) + Kseg(W, 2, j)*Q(nk(k)), 'A1 q')
            m = random.randint(0, nk(k))
            D = lambda n: Q(m)*P(n) - P(m)*Q(n)
            chk(D(nk(k)+1+j) == Kseg(W, 1, j)*D(nk(k)+1) + Kseg(W, 2, j)*D(nk(k)), 'A1 D')
    # D3: D(m,m)=0, D(m,m+1)=(-1)^m
    for m in range(0, len(seq) - 2):
        chk(Q(m)*P(m) - P(m)*Q(m) == 0 and Q(m)*P(m+1) - P(m)*Q(m+1) == (-1)**m, 'D3')
    # D4 (i),(ii)
    K12 = 11
    for k in range(1, K12):
        chk(sum(Q(nk(j)) for j in range(1, k+1)) <= 4*Q(nk(k)), 'D4i')
        tail = sum(Fr(1, Q(nk(j)+1)) for j in range(k+1, K12+1))
        chk(tail <= Fr(4, Q(nk(k+1)+1)), 'D4ii')
print('(A1),D3,D4 checked on 60 random block-Hurwitz prefixes')

# ---- D4 adversarial: all-ones (slowest growth) partial quotients
seq = [0] + [1]*80
p, q = convergents(seq)
Q = lambda n: q[n+1]
worst = max(Fr(sum(Q(j) for j in range(0, k+1)), Q(k)) for k in range(0, 70))
print('D4(i) with l=0 and all a=1 (Fibonacci): max sum/q =', float(worst), '(<=4 required)')
chk(worst <= 4, 'D4 fib')

# ---- Lemma B limits with mpmath: 1/theta_{n_k+i} -> K/(c_i c_i')
import mpmath
mpmath.mp.dps = 1500
for W in [[5, 1, 5], [1, 9, 9], [2], [1, 1], [3, 1], [2, 2, 2, 2]]:
    l = len(W); K, c, cp, s = params(W)
    A = [10**6 + k for k in range(1, 40)]
    seq = cf_seq(0, [], W, A)
    p, q = convergents(seq)
    x = mpmath.mpf(0)
    for a in reversed(seq[1:]):
        x = 1/(a + x)
    alpha = x
    k = 30; nk0 = (k-1)*(l+1)
    th = lambda n: q[n+1]*abs(q[n+1]*alpha - p[n+1])
    errs = [abs(1/th(nk0+i) - mpmath.mpf(K)/(c[i-1]*cp[i-1])) for i in range(1, l+1)]
    Bk = 1/th(nk0)
    chk(A[k-1] < Bk < A[k-1] + 2, 'B1 interval')
    print('  W=%s: max|1/theta_{n_k+i}-K/(c c\')| at k=30, A~1e6: %s ; 1/theta_{n_k}-A_k = %s'
          % (W, mpmath.nstr(max(errs) if errs else 0, 5), mpmath.nstr(Bk - A[k-1], 8)))
    chk(all(e < 1e-4 for e in errs), 'B limit')

# ---- nu two independent ways
tested = 0
for l in range(0, 5):
    for W in itertools.product(range(1, 6), repeat=l):
        W = list(W); K = Kc(W)
        if K > 9:
            continue
        a, wit = nu(W)
        b = nu_bruteforce(W, maxlen=min(K, 6))
        chk(a == b, f'nu mismatch {W}: {a} vs {b}')
        chk(Fr(1, 4) <= a <= 1, f'nu range {W}')
        tested += 1
print('nu(W): bottleneck == brute-force closed-walk enumeration on', tested, 'words with K<=9')
for W in [[], [1], [1, 1], [5, 1, 5], [2], [1, 9, 9]]:
    print('  nu(%s) = %s   (K=%d, sigma=%d)' % (W, nu(W)[0], Kc(W), params(W)[3]))
chk(nu([])[0] == 1 and nu([1])[0] == 1 and nu([1, 1])[0] == 1, 'R1 calibration')
chk(nu([5, 1, 5])[0] == Fr(5, 6), 'remark nu(5,1,5)=5/6')
print('FAILS:', fails)
print('ALL CHECKS PASSED' if fails == 0 else 'SOME CHECKS FAILED')
