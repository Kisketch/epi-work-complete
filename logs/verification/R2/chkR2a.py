from mpmath import mp, mpf
mp.dps = 400
N = 90
Q = [1, 1]; n = [0, 0]
for j in range(1, N):
    Q.append((4*j+2)*Q[j]+Q[j-1])
    m = 1 if (j % 2 == 0 and j >= 2) else 0
    n.append((4*j+2)*n[j]+n[j-1]+m)
S = 0; ok = True
for j in range(0, N-1):
    E = n[j+1]*Q[j]-n[j]*Q[j+1]
    if j >= 2 and j % 2 == 0:
        S += Q[j]
    ok &= (E == (-1)**j*S)
print("E_j=(-1)^j S_j for all j<89:", ok)
print("G1:", all((4*j+2)*Q[j] <= Q[j+1] <= (4*j+3)*Q[j] for j in range(1, N)))
print("G2:", all(Q[j+1] >= (4*j+2)*(4*j-2)*Q[j-1] for j in range(2, N)))
print("Q_i/Q_{i-2}>=36 for even i>=4:", all(Q[i] >= 36*Q[i-2] for i in range(4, N, 2)), "(i=2 ratio", Q[2]/Q[0], ")")
print("min Q_{i+1}/Q_i, i>=1:", min(mpf(Q[i+1])/Q[i] for i in range(1, N-1)))
mx = 0; S = 0
for j in range(2, N):
    if j % 2 == 0:
        S += Q[j]; jp = j
    mx = max(mx, mpf(S)/Q[jp])
print("max S_j/Q_j' =", mx, "<=", mpf(36)/35)
zs = mpf(n[N-1])/Q[N-1]
print("z*=", mp.nstr(zs, 30))
Ss = [0]*N; s = 0
for j in range(2, N):
    if j % 2 == 0:
        s += Q[j]
    Ss[j] = s
w = 0
for j in range(2, 60):
    tail = sum(mpf(Ss[i])/(Q[i]*Q[i+1]) for i in range(j+1, N-1))
    w = max(w, tail*Q[j+2])
print("max tail*Q_{j+2} =", mp.nstr(w, 8), "<=1.24")
for j in [4, 10, 20, 40, 60, 80]:
    y = Q[j]*zs-n[j]
    bd = mpf('1.03')/((4*j-2)*(4*j-6))+mpf('1.24')/(4*j+2)
    eta = y*Q[j+1]/Q[j]-1
    print(j, "j*y=", mp.nstr(j*abs(y), 10), "eta=", mp.nstr(eta, 5), "bound", mp.nstr(bd, 5), abs(eta) <= bd)
for j in [5, 11, 21, 41, 61, 81]:
    y = abs(Q[j]*zs-n[j]); b = mpf('1.03')*Q[j-1]/Q[j+1]+mpf('1.24')*Q[j]/Q[j+2]
    print(j, "|y|=", mp.nstr(y, 6), "bound", mp.nstr(b, 6), "y*j^2=", mp.nstr(y*j*j, 6), y <= b)
