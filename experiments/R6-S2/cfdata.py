"""Continued-fraction data for alpha_W = [0; A_1, W, A_2, W, ...], A_k = scale*k.

Indexing: a_0 = 0, a_{n_k+1} = A_k, n_k = (k-1)(l+1); block k = indices n_k..n_k+l.
p_{-1}=1, q_{-1}=0, p_0=a_0, q_0=1.  eps_n := q_n alpha - p_n = (-1)^n / (q_n alpha_{n+1} + q_{n-1}),
alpha_{n+1} = [a_{n+1}; a_{n+2}, ..., a_M] (tail truncated at block KTAIL; error far below dps).
theta_n := q_n |eps_n|.
"""
import math
import mpmath as mp


class CF:
    def __init__(self, W, kmax=45, ktail=60, scale=10):
        self.W = tuple(W)
        self.l = len(W)
        self.scale = scale
        a = [0]
        for k in range(1, ktail + 1):
            a.append(scale * k)
            a.extend(W)
        self.a = a
        self.M = len(a) - 1
        q = [1]; p = [a[0]]
        qm, pm = 0, 1  # q_{-1}, p_{-1}
        for n in range(1, self.M + 1):
            qn = a[n] * q[-1] + (q[-2] if n >= 2 else qm)
            pn = a[n] * p[-1] + (p[-2] if n >= 2 else pm)
            q.append(qn); p.append(pn)
        self.q, self.p = q, p
        self.kmax = kmax
        self.N = self.nk(kmax) + self.l          # last index of block kmax
        self.dps = int(2 * math.log10(q[self.N + 1]) + 100)

    def nk(self, k):
        return (k - 1) * (self.l + 1)

    def block(self, k):
        return list(range(self.nk(k), self.nk(k) + self.l + 1))

    def qm1(self, n):
        return self.q[n - 1] if n >= 1 else 0

    def eps_theta(self, dps, nmax):
        """eps_n, theta_n (mpf) for 0 <= n <= nmax at given dps."""
        with mp.workdps(dps):
            # complete quotients alpha_{n+1} for n = nmax..0, backward from M
            x = mp.mpf(self.a[self.M])
            cq = {}
            for m in range(self.M - 1, 0, -1):
                x = self.a[m] + 1 / x           # x = alpha_m
                if m - 1 <= nmax:
                    cq[m - 1] = x               # alpha_{(m-1)+1}
            eps, th = {}, {}
            for n in range(0, nmax + 1):
                e = mp.mpf((-1) ** n) / (self.q[n] * cq[n] + self.qm1(n))
                eps[n] = +e
                th[n] = self.q[n] * abs(e)
            return eps, th
