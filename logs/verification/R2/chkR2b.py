from mpmath import mp, mpf, floor, e as E, pslq
mp.dps = 1500
N = 160
Q=[1,1]; n=[0,0]
for j in range(1,N):
    Q.append((4*j+2)*Q[j]+Q[j-1])
    m = 1 if (j%2==0 and j>=2) else 0
    n.append((4*j+2)*n[j]+n[j-1]+m)
for j in range(N-1):
    Ej = n[j+1]*Q[j]-n[j]*Q[j+1]
    Sj = sum(Q[i] for i in range(2,j+1,2))
    assert Ej == (-1)**j*Sj, j
print("E_j=(-1)^j S_j OK")
for j in range(1,N-1):
    assert (4*j+2)*Q[j] <= Q[j+1] <= (4*j+3)*Q[j]
for j in range(2,N-1):
    assert Q[j+1] >= (4*j+2)*(4*j-2)*Q[j-1]
for j in range(2,N-1):
    Sj=sum(Q[i] for i in range(2,j+1,2)); jp=j if j%2==0 else j-1
    assert Q[jp]<=Sj<=mpf(36)/35*Q[jp]
print("G1,G2,step2 OK; min Q_i/Q_{i-2}, even i>=4:", min(Q[i]//Q[i-2] for i in range(4,N,2)), "; Q2/Q0 =",Q[2])
z = sum(mpf(n[j+1])/Q[j+1]-mpf(n[j])/Q[j] for j in range(N-1))
print("z* =", mp.nstr(z,30))
t=[None]+[mpf(sum(Q[i] for i in range(2,j+1,2)))/(Q[j]*Q[j+1]) for j in range(1,N-1)]
worst_tail=0
for j in range(1,60):
    y = Q[j]*z-n[j]
    tail=sum(t[i] for i in range(j+1,N-1))*Q[j+2]
    worst_tail=max(worst_tail,tail)
    if j%2==0 and j>=4:
        eta=(y*Q[j+1]/Q[j]-1)
        bound=mpf('1.03')/((4*j-2)*(4*j-6))+mpf('1.24')/(4*j+2)
        assert abs(eta)<=bound,(j,eta,bound)
        assert 0<y<mpf(1)/2
    if j>=3 and j%2==1:
        b=mpf('1.03')*Q[j-1]/Q[j+1]+mpf('1.24')*Q[j]/Q[j+2]
        assert abs(y)<=b,(j,y,b)
    if j in (2,4,6,10,11,20,21,40,41,59):
        print(j,"sign y_j:",'+' if y>0 else '-',"y_j=",mp.nstr(y,8)," j*y_j=",mp.nstr(j*y,8)," j*||Q_j z||=",mp.nstr(j*min(abs(y),1-abs(y)),8))
print("max tail*Q_{j+2} (j<60) =",mp.nstr(worst_tail,6),"(claim <=1.24)")
J=40
y=Q[J]*z-n[J]; print("J=40 y_J=",mp.nstr(y,8)," 1-y_J=",mp.nstr(1-y,8))
for J in (60,100,140,158):
    y=Q[J]*z-n[J]; print(J,"J*y_J=",mp.nstr(J*y,10), " 1/4-J*y_J=",mp.nstr(mpf(1)/4-J*y,6))
print("pslq [z,1,e]:", pslq([z,1,E],maxcoeff=10**6,maxsteps=10**6))
