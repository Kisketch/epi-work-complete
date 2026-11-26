import random
from mpmath import mp, mpf, e, floor, nint, fabs, log10
mp.dps = 900
def dist(x): return fabs(x - nint(x))
N = 260
Q=[1,1]; P=[1,3]
for j in range(1,N): Q.append((4*j+2)*Q[j]+Q[j-1]); P.append((4*j+2)*P[j]+P[j-1])
E = +e
print("P_j/Q_j - e (j=1,5,20,100):", [mp.nstr(P[j]/mpf(Q[j])-E,3) for j in (1,5,20,100)])
print("|delta_j|*Q_{j+1} (should be <=|D|=2):", [mp.nstr(fabs(Q[j]*E-P[j])*Q[j+1],8) for j in (0,1,2,5,20,60)])
# 1. CF identification of alpha=(e-1)/2
al=(E-1)/2; x=al; a=[]
for _ in range(14):
    ip=int(floor(x)); a.append(ip); x=1/(x-ip)
print("CF of (e-1)/2:", a)
q=[1,0]; # q_{-1}=0,q_0=1
qs=[1]; qm=0; qc=1
for ai in a[1:]:
    qm,qc=qc,ai*qc+qm; qs.append(qc)
print("CF denominators:", qs[:12]); print("Q_j j=0..11     :", Q[:12], qs[:12]==Q[:12])
# 2. KL comparison: theta_j = Q_j ||Q_j alpha||, j*theta_j/4
print("j  theta_j  theta_j*(4j+2)  j*theta_j/4")
for j in (1,2,3,5,10,20,40,80,160,250):
    th=Q[j]*dist(Q[j]*al)
    print(j, mp.nstr(th,8), mp.nstr(th*(4*j+2),8), mp.nstr(j*th/4,8))
print("limit 1/16 =", 1/mpf(16))
# 3. sharpness sequence
def build(m):
    n=[0,0]
    for j in range(1,N): n.append((4*j+2)*n[j]+n[j-1]+m(j))
    return n
n=build(lambda j: 1 if (j>=2 and j%2==0) else 0)
z=mpf(n[N])/Q[N]
print("z* =", mp.nstr(z,30), " claimed 0.014041639566949028405640892454")
for J in (20,60,61,100,101):
    print("J",J,"J*||Q_J z*|| =",mp.nstr(J*dist(Q[J]*z),10), " J/(4J+2)=",mp.nstr(mpf(J)/(4*J+2),10))
# bounds G1,G2,G3, S_j/Q_j' <= 36/35, eta bound
ok=all((4*j+2)*Q[j]<=Q[j+1]<=(4*j+3)*Q[j] for j in range(1,N))
g2=all(Q[j+1]>=(4*j+2)*(4*j-2)*Q[j-1] for j in range(2,N))
S=0; okS=True; okE=True
for j in range(0,N):
    if j>=2 and j%2==0: S+=Q[j]
    jp=j if j%2==0 else j-1
    if j>=2: okS &= (Q[jp]<=S<=mpf(36)/35*Q[jp])
    okE &= (n[j+1]*Q[j]-n[j]*Q[j+1]==(-1)**j*S)
print("G1",ok,"G2",g2,"Step2",okS,"Step1 E_j=(-1)^j S_j",okE)
G3=all(sum(mpf(1)/Q[i+1] for i in range(i0,i0+60))<=mpf(6)/5/Q[i0+1] for i0 in range(1,40))
print("G3",G3)
# Step5 eta bound and Step6 odd bound
bad=0
for J in range(4,100,2):
    y=Q[J]*z-n[J]; eta=y*Q[J+1]/Q[J]-1
    b=mpf('1.03')/((4*J-2)*(4*J-6))+mpf('1.24')/(4*J+2)
    if not (fabs(eta)<=b and 0<y<mpf(1)/2): bad+=1
print("Step5 violations (even J=4..98):",bad)
bad=0
for j in range(3,100,2):
    y=fabs(Q[j]*z-n[j]); b=mpf('1.03')*Q[j-1]/Q[j+1]+mpf('1.24')*Q[j]/Q[j+2]
    if not y<=b: bad+=1
print("Step6 violations (odd j=3..99):",bad, " max j^2*|y_j| over odd 3..99:", mp.nstr(max(j*j*fabs(Q[j]*z-n[j]) for j in range(3,100,2)),6))
# 4. (A): z=k*alpha + l
for zz in (al, 3*al+5, (E+1)/2*7):
    print("(A) j*||Q_j z|| j=20,100,200:", [mp.nstr(j*dist(Q[j]*zz),5) for j in (20,100,200)])
# 5. (B) adversarial: random defect patterns -> limsup j||Q_j z|| over window should be >=~1/4
random.seed(1)
for p in (0.1,0.5,1.0):
    ms=[0]*(N+2)
    for j in range(2,N): ms[j]=1 if random.random()<p else 0
    nn=build(lambda j: ms[j]); zz=mpf(nn[N])/Q[N]
    vals=[(j*dist(Q[j]*zz)) for j in range(40,120) ]
    last_def=[j for j in range(40,120) if ms[j]]
    print("p",p,"max_{40<=j<120} j||Q_j z||=",mp.nstr(max(vals),6),
          " min over defect indices:",mp.nstr(min(j*dist(Q[j]*zz) for j in last_def),6) if last_def else None)
