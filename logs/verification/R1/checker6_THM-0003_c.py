from mpmath import mp, mpf, e, nint, sqrt, pi
from fractions import Fraction as F
import random
mp.dps=400
P=[1,3];Q=[1,1]
for j in range(1,40):
    P.append((4*j+2)*P[j]+P[j-1]);Q.append((4*j+2)*Q[j]+Q[j-1])
print("Q0..4",Q[:5],"P0..4",P[:5])
ok=True
for j in range(0,38):
    d=P[j]*Q[j+1]-P[j+1]*Q[j]
    dl=(Q[j]*e-P[j]); dl1=(Q[j+1]*e-P[j+1])
    dd=dl*Q[j+1]-dl1*Q[j]
    ok&= d==2*(-1)**(j+1) and abs(dd-2*(-1)**j)<mpf(10)**-300
    ok&= P[j]%2==1 and Q[j]%2==1
    if j>=1: ok&= Q[j+1]>=(4*j+2)*Q[j] and Q[j+1]>=6*Q[j]
    ok&= abs(dl)<=mpf(2)/Q[j+1]
print("F1-F4 checks (j<38):",ok)
print("|delta_j|*Q_{j+1} j=1..5:",[float(abs(Q[j]*e-P[j])*Q[j+1]) for j in range(1,6)])
def nd(x): return abs(x-nint(x))
for (a,b) in [(0,1),(3,-5),(1,7)]:
    z=a+b*(e+1)/2
    print("L",(a,b),[float(j*nd(Q[j]*z)) for j in (5,10,20,30)])
for name,z in [("e/2",e/2),("1/2",mpf(1)/2),("1/3",mpf(1)/3),("sqrt2",sqrt(2)),("e",e),("pi",pi),("(e+1)/4",(e+1)/4)]:
    print(name,[round(float(j*nd(Q[j]*z)),4) for j in (5,10,20,30,35)])
for j in (2,3,5,10,100):
    print("coef j",j,float(4+2/j+1/(j+1)+1/(j-1)))
def Eset(N,psi):
    iv=[]
    for k in range(N):
        lo=F(k,N)-psi/N; hi=F(k,N)+psi/N
        if lo<0: iv.append((F(0),hi)); iv.append((lo+1,F(1)))
        elif hi>1: iv.append((lo,F(1))); iv.append((F(0),hi-1))
        else: iv.append((lo,hi))
    return sorted(iv)
def meas(iv): return sum(b-a for a,b in iv)
def inter(A,B):
    t=F(0);i=j=0
    while i<len(A) and j<len(B):
        lo=max(A[i][0],B[j][0]);hi=min(A[i][1],B[j][1])
        if hi>lo:t+=hi-lo
        if A[i][1]<B[j][1]:i+=1
        else:j+=1
    return t
random.seed(1);worst=0
for B in (1,2,3):
  for (i,j) in ((1,2),(2,3),(1,3),(2,4),(3,4)):
    for _ in range(6):
        pi_=F(random.randint(0,500),1000);pj=F(random.randint(0,500),1000)
        Ni,Nj=B*Q[i],B*Q[j]
        Ei=Eset(Ni,pi_);Ej=Eset(Nj,pj)
        err=abs(inter(Ei,Ej)-meas(Ei)*meas(Ej))
        bound=2*(2*pj)*F(Ni,Nj)
        assert meas(Ei)==2*pi_ and meas(Ej)==2*pj
        if bound>0: worst=max(worst,float(err/bound))
        assert err<=bound,(B,i,j,pi_,pj,err,bound)
print("Lemma holds on all tests; max err/bound =",worst)
print("sum_{k>=1} 6^-k =",float(sum(F(1,6**k) for k in range(1,60))))
for S in (10,100,1e4): print("PZ ratio",S,S*S/(S*S+1.8*S))
