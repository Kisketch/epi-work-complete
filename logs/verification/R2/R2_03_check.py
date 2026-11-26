from mpmath import mp, mpf, e, nint, sqrt
from fractions import Fraction
mp.dps = 600

def seq(a, Q0, Q1, P0, P1, N):
    Q = [Q0, Q1]; P = [P0, P1]
    for j in range(1, N):
        Q.append(a(j)*Q[j] + Q[j-1]); P.append(a(j)*P[j] + P[j-1])
    return Q, P

def dist(x): return abs(x - nint(x))

# ---- e-case (THM-0003)
N = 60
Q, P = seq(lambda j: 4*j+2, 1, 1, 1, 3, N)
D = P[0]*Q[1] - P[1]*Q[0]
print("e-case D =", D, " Casoratian P_jQ_{j+1}-P_{j+1}Q_j == (-1)^j D for all j:",
      all(P[j]*Q[j+1]-P[j+1]*Q[j] == (-1)**j*D for j in range(N-1)))
d = [Q[j]*e - P[j] for j in range(N)]
print("max_{1<=j<N-1} |delta_j| Q_{j+1}/|D| =",
      mp.nstr(max(abs(d[j])*Q[j+1]/abs(D) for j in range(1, N-1)), 8), "(must be <=1)")
print("Q_{j+1}>=a_j Q_j:", all(Q[j+1] >= (4*j+2)*Q[j] for j in range(1, N-1)))
d0, d1 = d[0], d[1]
print("(d0-d1)/D =", mp.nstr((d0-d1)/D, 8), "(should be -1, so 1 in L);  d0/D =",
      mp.nstr(d0/D, 12), " (1-e)/2 =", mp.nstr((1-e)/2, 12))
for (u, v) in [(1, 0), (0, 1), (3, -5)]:
    z = (u*d1 - v*d0)/D; eps = Fraction(Q[1]*u - Q[0]*v, D)
    js = (5, 10, 20, 40)
    print("z in L, (u,v)=", (u, v), "a_j||Q_j z||:", [mp.nstr((4*j+2)*dist(Q[j]*z), 5) for j in js],
          "bound |eps D|/Q_j:", ["%.2e" % (abs(float(eps*D))/Q[j]) for j in js])
for name, z in [("e/2", e/2), ("e/3", e/3), ("sqrt2", sqrt(2)), ("1/2", mpf(1)/2), ("(e-1)/2 [in L]", (e-1)/2)]:
    print(name, "a_j||Q_j z||, j=20,22,..,30:", [mp.nstr((4*j+2)*dist(Q[j]*z), 3) for j in range(20, 31, 2)])

# single-index vs two-index integrality in e-case, (g,eps) in (1/2)Z^2 / Z^2
Qe, Pe = seq(lambda j: 4*j+2, 1, 1, 1, 3, 10)
def ok(x, y, js, Qs, Ps, den):
    return all((Fraction(x, den)*Qs[j] + Fraction(y, den)*Ps[j]).denominator == 1 for j in js)
print("e-case, (g,eps) in (1/2)Z^2 mod Z^2 passing at j=5 only:",
      [(x, y) for x in range(2) for y in range(2) if ok(x, y, (5,), Qe, Pe, 2)],
      " at j=5,6:", [(x, y) for x in range(2) for y in range(2) if ok(x, y, (5, 6), Qe, Pe, 2)])

# ---- general example: a_j=j^2+1, Q_0=2,Q_1=1,P_0=1,P_1=4
a = lambda j: j*j + 1
Q, P = seq(a, 2, 1, 1, 4, N)
D = P[0]*Q[1] - P[1]*Q[0]
print("\ngeneral example D =", D)
theta = P[N-1]/mpf(Q[N-1])
d = [Q[j]*theta - P[j] for j in range(N)]
print("Casoratian ok:", all(P[j]*Q[j+1]-P[j+1]*Q[j] == (-1)**j*D for j in range(N-1)))
print("max |delta_j|Q_{j+1}/|D| (j=1..40) =", mp.nstr(max(abs(d[j])*Q[j+1]/abs(D) for j in range(1, 40)), 8))
good = True
for (u, v) in [(1, 0), (0, 1), (2, 3), (-4, 7)]:
    g = Fraction(P[0]*v - P[1]*u, D); ep = Fraction(Q[1]*u - Q[0]*v, D)
    z = (u*d[1] - v*d[0])/D
    good &= abs(z - (mpf(g.numerator)/g.denominator + mpf(ep.numerator)/ep.denominator*theta)) < mpf(10)**-400
    good &= all((g*Q[j] + ep*P[j]).denominator == 1 for j in range(N))
print("parametrisation z=(u d1 - v d0)/D equals g+eps*theta, and g Q_j+eps P_j integer for all j<60:", good)
A = abs(D)
c01 = sum(1 for x in range(A) for y in range(A) if ok(x, y, (0, 1), Q, P, A))
c56 = sum(1 for x in range(A) for y in range(A) if ok(x, y, (5, 6), Q, P, A))
c5 = sum(1 for x in range(A) for y in range(A) if ok(x, y, (5,), Q, P, A))
print("index [Lambda:Z^2] via indices 0,1 =", c01, "; via 5,6 =", c56, "; |D| =", A, "; single index 5 passes:", c5)
for name, z in [("theta/2", theta/2), ("sqrt2", sqrt(2)), ("theta/3", theta/3)]:
    print(name, "a_j||Q_j z||, j=25,27,..,35:", [mp.nstr(a(j)*dist(Q[j]*z), 3) for j in range(25, 36, 2)])
