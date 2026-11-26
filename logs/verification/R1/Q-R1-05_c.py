from mpmath import mp, mpf, e, pi, nint, fabs
mp.dps=400
Q=[1,1];P=[1,3]
for j in range(1,40):
    Q.append((4*j+2)*Q[j]+Q[j-1]);P.append((4*j+2)*P[j]+P[j-1])
print(Q[:6],P[:5])
print("all odd",all(q%2==1 for q in Q),all(p%2==1 for p in P))
print("det ok",all(P[j]*Q[j+1]-P[j+1]*Q[j]==2*(-1)**(j+1) for j in range(39)))
d=lambda j:Q[j]*e-P[j]
for j in [0,1,2,3,5,10,20,30]:
    print(j, mp.nstr(d(j),6), mp.nstr(fabs(d(j))*Q[j+1],8), abs(d(j))*Q[j+1]<=2)
print("cf check", mp.nstr(e-mpf(P[30])/Q[30],10), mp.nstr(2*(-1)**30/(Q[30]*Q[31]),10))
nn=lambda y:fabs(y-nint(y))
for name,z in [("(e+1)/2",(e+1)/2),("3+5(e+1)/2",3+5*(e+1)/2),("pi",pi),("e",e),("1/3",mpf(1)/3)]:
    print(name,[mp.nstr(j*nn(Q[j]*z),4) for j in range(1,31,3)])
