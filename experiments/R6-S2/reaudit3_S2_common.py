# reaudit3 common helpers (self-written; does not import other auditors' code)
from fractions import Fraction as Fr
import itertools

def Kc(word):
    """continuant K(w_1..w_m); K()=1; length -1 convention handled by Kseg."""
    a, b = 0, 1   # K(len -1)=0, K()=1
    for w in word:
        a, b = b, w * b + a
    return b

def Kseg(W, a, b):
    """K_{[a,b]} = K(w_a..w_b) (1-based); b=a-1 ->1, b=a-2 ->0"""
    if b == a - 2:
        return 0
    if b == a - 1:
        return 1
    assert b >= a
    return Kc(W[a-1:b])

def params(W):
    l = len(W)
    K = Kc(W)
    c = [Kseg(W, 1, i-1) for i in range(1, l+1)]
    cp = [Kseg(W, i+1, l) for i in range(1, l+1)]
    sigma = c[-1] if l >= 1 else 1
    return K, c, cp, sigma

def dK(x, K):
    x %= K
    return min(x, K - x)

def vcost(W):
    K, c, cp, sigma = params(W)
    return [max([Fr(dK(c[i]*r, K), c[i]*cp[i]) for i in range(len(W))], default=Fr(0)) for r in range(K)]

def nu(W):
    """exact nu(W) via bottleneck reachability (independent re-implementation)."""
    K, c, cp, sigma = params(W)
    v = vcost(W)
    # minimal nontrivial edge cost from a to b
    def ecost(a, b):
        m = (b - sigma * a) % K
        if a == 0 and b == 0:
            return Fr(1)       # t=0 is the trivial loop; next is |t|=1
        return Fr(min(m, K - m), K)
    cands = sorted(set(v) | {ecost(a, b) for a in range(K) for b in range(K)} | {Fr(1)})
    for cval in cands:
        if cval > 1:
            break
        ok_v = [v[r] <= cval for r in range(K)]
        adj = {a: [b for b in range(K) if ok_v[a] and ok_v[b] and
                   (ecost(a, b) <= cval or ((b - sigma*a) % K == 0 and not (a == 0 and b == 0)))]
               for a in range(K)}
        # note ecost already handles m=0 for (a,b)!=(0,0) as 0
        # reachability incl. trivial loop irrelevant
        def reach(src):
            seen = {src}; st = [src]
            while st:
                x = st.pop()
                for y in adj[x]:
                    if y not in seen:
                        seen.add(y); st.append(y)
            return seen
        R = {a: reach(a) for a in range(K)}
        for a in range(K):
            if not ok_v[a]:
                continue
            for b in range(K):
                if not ok_v[b]:
                    continue
                if ecost(a, b) <= cval and a in R[b]:
                    return cval, (a, b, ecost(a, b))
    raise RuntimeError('nu > 1 ?')

def nu_bruteforce(W, maxlen=None):
    """brute force over closed walks (vertex sequences) up to length maxlen with best edge per pair."""
    K, c, cp, sigma = params(W)
    v = vcost(W)
    if maxlen is None:
        maxlen = K
    best = Fr(1)  # trivial bound from t=1 loop at 0
    def ecost(a, b):
        m = (b - sigma * a) % K
        if a == 0 and b == 0:
            return Fr(1)
        return Fr(min(m, K - m), K)
    for L in range(1, maxlen + 1):
        for seq in itertools.product(range(K), repeat=L):
            if seq[0] != min(seq):
                continue
            cost = max(v[r] for r in seq)
            # all edges: use cheapest edge for each consecutive pair; if all pairs are (0,0) then need |t|>=1
            ecs = []
            for m in range(L):
                a, b = seq[m], seq[(m + 1) % L]
                mm = (b - sigma * a) % K
                ecs.append(Fr(min(mm, K - mm), K))
            if all(x == 0 for x in seq):
                continue  # covered by bound 1
            cost = max(cost, max(ecs))
            best = min(best, cost)
    return best
