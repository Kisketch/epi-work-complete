from mpmath import mp, mpf, nint
mp.dps = 700
N = 150
Q = [1, 1]
n = [0, 0]
for j in range(1, N):
    m = 1 if (j % 2 == 0 and j >= 2) else 0
    Q.append((4*j+2)*Q[j] + Q[j-1])
    n.append((4*j+2)*n[j] + n[j-1] + m)
z = mpf(n[N]) / mpf(Q[N])   # z = lim n_j/Q_j, error ~ 1/Q_{N+1}
print("z =", mp.nstr(z, 40))
for j in range(2, 61):
    x = Q[j] * z
    d = abs(x - nint(x))
    extra = mp.nstr(mpf(j*Q[j])/Q[j+1], 10) if j % 2 == 0 else ""
    print(j, "even" if j % 2 == 0 else "odd ", mp.nstr(j*d, 10), extra)
