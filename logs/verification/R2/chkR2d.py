from mpmath import mp, mpf, nint
mp.dps = 400


def seq(a, Q0, Q1, P0, P1, N):
    Q = [Q0, Q1]
    P = [P0, P1]
    for j in range(1, N):
        Q.append(a(j) * Q[-1] + Q[-2])
        P.append(a(j) * P[-1] + P[-2])
    return P, Q


def nd(x):
    return abs(x - nint(x))


def run(name, a, Q0, Q1, P0, P1, N=60):
    P, Q = seq(a, Q0, Q1, P0, P1, N + 3)
    D = P0 * Q1 - P1 * Q0
    theta = mpf(P[N + 2]) / Q[N + 2]
    d = [Q[j] * theta - P[j] for j in range(N)]
    ok_cas = all(P[j] * Q[j + 1] - P[j + 1] * Q[j] == (-1) ** j * D for j in range(N))
    tol = 1 + mpf(10) ** -100
    ok_bd = all(abs(d[j]) <= abs(D) / mpf(Q[j + 1]) * tol for j in range(N))
    ok_inc = all(Q[k] * Q[k + 1] < Q[k + 1] * Q[k + 2] for k in range(0, N))
    print(name, "D=", D, "| Casoratian=(-1)^j D:", ok_cas,
          "| |d_j|<=|D|/Q_{j+1}, all j>=0:", ok_bd, "| Q_kQ_{k+1} incr from k=0:", ok_inc)
    for (n0, n1) in [(1, 0), (0, 1), (3, -5), (7, 2)]:
        z = (n0 * d[1] - n1 * d[0]) / D
        vals = [a(j) * nd(Q[j] * z) for j in range(N - 12, N - 2)]
        print("  A: z=(%d d1-%d d0)/D  max a_j||Q_j z|| (window):" % (n0, n1), mp.nstr(max(vals), 5))
    bad = []
    for g in range(0, abs(D)):
        for ep in range(0, abs(D)):
            gam = mpf(g) / abs(D)
            eps = mpf(ep) / abs(D)
            inL = all(((g * Q[j] + ep * P[j]) % abs(D) == 0) for j in (0, 1))
            z = gam + eps * theta
            vals = [a(j) * nd(Q[j] * z) for j in range(N - 12, N - 2)]
            m = max(vals)
            if not inL:
                bad.append(m)
            if inL and m > mpf('0.01'):
                print("  !!in L but large", g, ep, m)
    print("  B: min over z not in L (denominator |D|) of window-max a_j||Q_j z|| =",
          mp.nstr(min(bad), 6) if bad else None)


run("e-case", lambda j: 4 * j + 2, 1, 1, 1, 3)
run("a=j^2+1 (2,1,1,4)", lambda j: j * j + 1, 2, 1, 1, 4)
run("Q0=0, D>0", lambda j: j + 1, 0, 1, 2, 1)
run("Q0=0, D<0", lambda j: 2 * j + 1, 0, 1, -3, 5)
run("a_1=a_2=1 then j^2", lambda j: 1 if j < 3 else j * j, 3, 2, 5, 1)

z = mpf(2).sqrt()
P, Q = seq(lambda j: 4 * j + 2, 1, 1, 1, 3, 80)
print("C: random z, w_j=j: max_j w_j||Q_j z|| (j=60..77):",
      mp.nstr(max(j * nd(Q[j] * z) for j in range(60, 78)), 5))
