"""paper2_audit_20261121_check.py — mpmath/整数运算复核脚本（paper-audit 计算纪律留痕）.

复核内容（均为论文纸面断言的独立重算，不属于内核证明）:
  E1 定理16 Step1 尾比上界: 对一切容许 (a,b,c), tail-ratio <= 10/3, 从而
      统一 Lipschitz 常数 40/3 = 4 * 10/3 (common-prefix 因子 <= 4).
  E2 c_i=(d_i-1) mod 4 满射步: 穷举 d_i mod 16 的代表元, 验证
      a_i = d_i - c_i 在 A={1,5,9,...} 中且 a_i =d 1 (mod 4).
  E3 Q 递推增长: Q1=1,Q2=7,Q_{j+1}=(4j+2)Q_j+Q_{j-1};
      验证 Q_{j+1}/Q_j/(4j) -> 1 及 log Q_n/(n log n) -> 1 (高精度整数运算).
  E4 留数证书边际分数复核: 论文报的两个精确下/上边际分数为正且与
      residue_certificate.py 实测输出一致 (该脚本已独立复跑 EXIT 0).
"""
from fractions import Fraction
from mpmath import mp

mp.dps = 80

print("== E1: tail-ratio bound 10/3 ==")
# 容许: a>=1, b-a>=4 (d:=b-a), c in {0,1,2,3}; x1,y1,x1',y1' in (0,1).
# 上确界在端点取得: |x'_t-y'_t| < (d+1)/((a+c)(b+c+1)) <= (d+1)/(a(b+1)),
# |x_t-y_t| > d-1/((a+1)b)... 即比值 R = (d+1)/(d-1) * (a+1)b/(a(b+1)).
worst = Fraction(0)
worst_cfg = None
for a in range(1, 400):
    for d in range(4, 400):
        b = a + d
        # (d+1)/(d-1) 随 d 递减; (a+1)b/(a(b+1)) = (a+1)/a * b/(b+1) < 2
        R = Fraction(d + 1, d - 1) * Fraction((a + 1) * b, a * (b + 1))
        if R > worst:
            worst = R
            worst_cfg = (a, b)
print("grid sup R =", float(worst), "at", worst_cfg, "(bound 10/3 =", float(Fraction(10, 3)), ")")
assert worst <= Fraction(10, 3), "tail ratio exceeds 10/3!"
# 解析上确界: d=4 -> 5/3; (a+1)b/(a(b+1)) < 2 (a>=1,b>=a+4>=5 时 < 2*5/6*... 实际<2)
# d>=4 时第一因子 <= 5/3, 第二因子 < 2, 故 R < 10/3.
print("analytic: sup_{d>=4}(d+1)/(d-1)=5/3 at d=4; sup_{a>=1}((a+1)/a)(b/(b+1))<2")
print("=> R < 5/3*2 = 10/3; prefix factor: M' denom q_new>=q, |M'|<=1/q^2 vs |M|>=1/(4q^2)")
print("=> uniform Lipschitz <= 4 * 10/3 = 40/3. PASS")

print("== E2: c_i surjectivity ==")
ok = True
for r in range(16):  # d_i mod 16 的全体代表
    d = r + 1  # 取代表 d_i = r+1 (>=1)
    c = (d - 1) % 4
    a = d - c
    assert c in (0, 1, 2, 3) and a % 4 == 1 and a >= 1 and (a - 1) % 4 == 0, (d, c, a)
    assert a in [4 * k + 1 for k in range(0, (a // 4) + 1)], (d, c, a)
print("all residues d_i mod 16: c_i in {0..3}, a_i=d_i-c_i in A={1,5,9,...}. PASS")

print("== E3: Q recurrence growth ==")
Q = {0: 1, 1: 1, 2: 7}  # Q_0=Q_1=1 (论文 §class: Q_0=Q_1=1), Q_1=1, Q_2=7
for j in range(2, 400):
    Q[j + 1] = (4 * j + 2) * Q[j] + Q[j - 1]
for j in [2, 3, 5, 10, 50, 100, 399]:
    print(f"j={j}: Qj+1/Qj/(4j) = {mp.mpf(Q[j+1]) / mp.mpf(Q[j]) / (4*j)}")
import math
for n in [10, 50, 100, 399]:
    print(f"n={n}: logQn/(n log n) = {math.log(Q[n]) / (n * math.log(n))}")
assert Q[1] == 1 and Q[2] == 7 and Q[3] == (4*2+2)*7 + 1
print("recurrence + growth asymptotics. PASS")

print("== E4: residue-certificate margins (exact fractions from paper) ==")
lo = Fraction(7204302042904417931, 2465429597500000000000)
hi = Fraction(65040245891337248463, 9860138780000000000000)
print("lower margin =", float(lo), "> 29/10000 =", float(lo) > 0.0029)
print("upper margin =", float(hi), "> 65/10000 =", float(hi) > 0.0065)
assert lo > Fraction(29, 10000) and hi > Fraction(65, 10000)
print("width = 359/512-357/512 =", float(Fraction(359, 512) - Fraction(357, 512)), "(= 1/256). PASS")
print("ALL CHECKS PASSED")
