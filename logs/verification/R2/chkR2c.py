from mpmath import mp, mpf, e, nint
mp.dps=300
def run(a,Q0,Q1,P0,P1,N=60):
    Q=[Q0,Q1];P=[P0,P1]
    for j in range(1,N):
        Q.append(a(j)*Q[-1]+Q[-2]);P.append(a(j)*P[-1]+P[-2])
    return P,Q
def fr(x): return abs(x-nint(x))
P,Q=run(lambda j:4*j+2,1,1,1,3)
th=mpf(P[-1])/Q[-1]; print("theta-e",abs(th-e)<mpf(10)**-100, P[:5],Q[:5])
D=P[0]*Q[1]-P[1]*Q[0]; print("D",D)
print("casoratian",[P[j]*Q[j+1]-P[j+1]*Q[j] for j in range(5)])
d=[Q[j]*e-P[j] for j in range(30)]
print("bound",all(abs(d[j])<=abs(D)/Q[j+1] for j in range(30)))
for name,z in [("(e+1)/2",(e+1)/2),("(e-1)/2",(e-1)/2),("e/2",e/2),("1/2",mpf(1)/2),("e",e),("(e+1)/3",(e+1)/3)]:
    print(name,[float((4*j+2)*fr(Q[j]*z)) for j in (20,21,22,23)])
a=lambda j:j*j+1
P,Q=run(a,2,1,1,4,40)
D=P[0]*Q[1]-P[1]*Q[0];th=mpf(P[-1])/Q[-1];print("D",D)
d=[Q[j]*th-P[j] for j in range(25)]
print("bound",all(abs(d[j])<=abs(D)/Q[j+1] for j in range(25)))
for k in range(0,7):
  for m in range(0,7):
    z=(k*d[0]+m*d[1])/D
    v=max((a(j)*fr(Q[j]*z)) for j in range(15,20))
    if v>mpf('0.01'): print("L elem not small",k,m,v)
print("outside L:",[float(a(j)*fr(Q[j]*(d[0]/(2*D)))) for j in (15,16,17,18)],[float(a(j)*fr(Q[j]*th/7)) for j in (15,16,17,18)])
