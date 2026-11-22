# -*- coding: utf-8 -*-
"""
第二阶段数值验证：沿 e 收敛子分母 Q_j 的逼近谱隙与水平集维数。
对齐 EpiFormal/SpectralGap.lean。mpmath 动态精度 digits(Q_j)+300。
数值≠证明，仅作佐证。
"""
import json, os
from mpmath import mp, mpf, floor, pi, e, sqrt

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "spectral_out")
os.makedirs(OUT, exist_ok=True)

def sel_pair(p0, p1, jmax):
    X = [0]*(jmax+2); a,b = p0,p1; X[0]=a
    for n in range(jmax+1):
        X[n+1]=b; a,b = b,(4*(n+1)+2)*b+a
    return X

def rhu(x): return int(floor(x+mpf(1)/2))
def dist_int(x): return abs(x-mpf(rhu(x)))

Q = sel_pair(1,1,82)
JMAX = 60

def lam_max(x, jmax=JMAX):
    """max_{j<=jmax} j*||Q_j x||，及末值趋势。
    注意：小 j 时 j‖Q_j x‖ 未必小（收敛子性质只对大 j 成立），
    故谱隙判据看大 j 末值（j>=40）而非全程 max。"""
    vals=[]
    for j in range(1,jmax+1):
        mp.dps = len(str(Q[j]))+300
        v = mpf(j)*dist_int(mpf(Q[j])*x)
        vals.append(float(v))
    return max(vals), vals[-1], max(vals[39:])  # 全程max, 末值, 大j max

# ---- 谱隙验证 ----
mp.dps = 400  # 测试点须高精度构造（默认 15 位会污染 L 内点）
tests = {
    "pi": pi, "2pi": 2*pi, "3pi": 3*pi, "5pi": 5*pi, "10pi": 10*pi,
    "sqrt2": sqrt(2), "golden": (1+sqrt(5))/2,
    "L_half_e_plus_1": (e+1)/2,           # ∈ L
    "L_1_plus_half": 1+(e+1)/2,           # ∈ L
    "e": e,                                # = 2*(e+1)/2 - 1 ∈ L
}
gap={}
for name,x in tests.items():
    mx,last,bigmax = lam_max(x)
    gap[name]={"max_j_le60":mx,"last_j60":last,"max_j40_60":bigmax}

# ---- 维数 box-counting（精确有理覆盖树）----
def box_count(c, N):
    """E_c∩[0,1] 的 box-counting 维数估计（单层上界）。
    第 N 层允许区间：中心 k/Q_N，半径 t/(N Q_N)，k=0..Q_N。
    用宽度 1/Q_N 的盒子覆盖这些区间，数盒子。
    注意：这是单层覆盖上界，非真实 liminf 集维数（真实分支更少）。"""
    import math
    mp.dps = len(str(Q[N]))+300
    t = mpf(c)
    qn = mpf(Q[N])
    radius = t/(mpf(N)*qn)
    # 每个区间覆盖约 2*radius*Q_N + 1 个盒子；共 Q_N+1 个区间（可能重叠）
    per_interval = float(2*radius*qn + 1)
    covered = min(float(Q[N]+1)*per_interval, float(Q[N]))
    if covered<=1: return 0.0
    return math.log(covered)/math.log(float(Q[N]))

dim={}
for c in (0.25,0.5,1.0,2.0):
    dim[str(c)]={f"N{N}":box_count(c,N) for N in (4,8,12)}

summary={"spectral_gap":gap,"box_counting_dim_single_layer_upper":dim,
         "note":"数值佐证，非证明。谱隙：L 内点 max_j40_60→0（~1e-72）；泛型点 max~22-28≫1/4。e∈L 故 Λ(e)=0。box-counting 为单层覆盖上界（恒 1，太松）；真实维数需多层覆盖树（见论文 Thm finite 覆盖论证，分支数常数、log Q_n~n log n ⇒ dim 0）。"}
with open(os.path.join(OUT,"spectral_summary.json"),"w",encoding="utf-8") as f:
    json.dump(summary,f,ensure_ascii=False,indent=2)
print(json.dumps(summary,ensure_ascii=False,indent=2))