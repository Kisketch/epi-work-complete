"""v2audit_S2_6: exact test of S1(c) on finitely supported constructions.
If T'_k = 0 for k > k*, then beta = (1/K) sum_{k<=k*} x_k eps_{n_k} = (U alpha - V)/K with
U = sum x_k q_{n_k}, V = sum x_k p_{n_k}. Since alpha is irrational, beta in Z alpha + Z iff K|U and K|V.
The construction makes the canonical labels eventually sigma^j r_{k*} and t_k -> 0, so S1(c) predicts:
K|U and K|V  <=>  r_{k*} = 0.  Exact integer arithmetic; independent of the proof's argument."""
import random
random.seed(31)
def Kc(w):
    a, b = 0, 1
    for x in w: a, b = b, x * b + a
    return b
fails = 0; tests = 0; pos = 0
for W in [(1,), (2,), (1, 1), (3,), (2, 2), (5, 1, 5), (1, 2, 3), (3, 1, 3), (4, 1), (2, 1, 1, 2)]:
    l = len(W); K = Kc(W); s = Kc(W[:l - 1]) if l else 1
    for trial in range(300):
        N = random.choice([0, 2]); a0 = random.choice([0, 4])
        kstar = random.randint(1, 8); M = kstar + 2
        A = [random.randint(1, 30) for _ in range(M)]
        a = [a0] + [random.randint(1, 5) for _ in range(N)]; nk = []
        for Ak in A: nk.append(len(a) - 1); a.append(Ak); a.extend(W)
        p = [1, a[0]]; q = [0, 1]
        for n in range(1, len(a)):
            p.append(a[n] * p[-1] + p[-2]); q.append(a[n] * q[-1] + q[-2])
        r = [random.randrange(K) for _ in range(kstar + 1)]
        if random.random() < 0.4: r[kstar] = 0
        T = [None] + [(r[k] - s * r[k - 1]) % K + K * random.randint(-2, 2) for k in range(1, kstar + 1)]
        Tp = T[:]; Tp[1] += s * r[0]
        U = sum((-1) ** nk[k - 1] * Tp[k] * q[nk[k - 1] + 1] for k in range(1, kstar + 1))
        V = sum((-1) ** nk[k - 1] * Tp[k] * p[nk[k - 1] + 1] for k in range(1, kstar + 1))
        inlat = (U % K == 0 and V % K == 0)
        pred = (r[kstar] == 0)
        tests += 1; pos += inlat
        if inlat != pred:
            fails += 1
            if fails < 10: print("FAIL", W, r, T, inlat, pred)
print("tests:", tests, " in-lattice cases:", pos, " FAILS:", fails)
