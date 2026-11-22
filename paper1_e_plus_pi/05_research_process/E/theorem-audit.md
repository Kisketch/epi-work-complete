# E 组定理匹配与原文核验

对照稿为《第二阶段修订/Phase2_revised.tex》第 71–83、256–301、303–364 行，以及第一阶段命题 8.1。下文“未找到”仅指所核文献。编号采用所链接的版本，页码注明期刊页或作者稿页。

## 定理—假设—本项目用途

| 原定理 | 必须满足的假设 | 项目中的代入与判定 |
|---|---|---|
| BLR 推论 8，作者稿 p. 5 [1] | 正实数乘子相邻之比趋于无穷，任意实数中心序列 | 取乘子 Q_j 和常数中心 c。无权重 c=0 直接特例，全部 c∈[0,1/2] 为短推论。 |
| BLR 定理 7，作者稿 pp. 2、5，式 (1.1)、(1.5)–(1.7) [1] | 全层移动管道、导数畸变、下一层增长、相邻导数对数之比趋于无穷 | 线性导数通过畸变检验，管道宽度通过分枝检验，对数比趋于 1。正权重情形无法直接引用该式取得任何一侧界。 |
| Feng–Wen–Wu，定义 1.1、定理 2.1，pp. 475–478 [2] | 每层固定子数、固定收缩比、同父区间内部不交，嵌套 | 本文选枝后满足。给出指定极限集合的下界；配合正文覆盖上界即得等式。 |
| Cabrelli 等，§5，期刊定理 3，p. 57 [3] | 非增正间隙序列，总和为 1，按文中次序构造的 C_a，采用 p. 54 的专用 gauge | 给这个 C_a 正有限测度。未识别本项目的 gauge、严格次水平集、精确谱层或整层的 σ 有限性。 |
| Adiceam 定理 1，式 (5)、§2.1 [4] | 任意固定无理数，规定两条剩余类，至少一个剩余非零，无穷多个分数 | 可同时选 π 与给定模数，但没有命题 8.1 的窗口和误差常数。 |
| Borda 定理 1 与其分母推论，作者稿 pp. 3–4 [5] | 固定模数，对随机输入或几乎处处的输入给出分布律 | 可检测分母剩余类。未给固定 π 在随 j 变化的窗口上的估计。 |
| Zeilberger–Zudilin，命题 7、8 及末节 “World record” [6] | 固定 π，特定积分生成的整数系数 | 给 A 一个分母大小下界，给 C 真实的 π 线性形式；与 Q_j 的公因子需要另证。 |
| Mance，定义 1.9、1.10、注 1.11、定理 1.15 [7] | 任意基本序列的度量结论；基数趋于无穷时有逐点的数字判别 | 阶乘序列可直接代入；固定 −π 是否满足该数字判别仍待证明。 |
| Rivoal，§2 定理 1，式 (2.3)–(2.5)，及校正的定理 3 [8] | 同一自变量，指数与指定对数，共用同一显式多项式 | C 可调用多项式与余项表达式。特化点、清分母及合并余项非零仍是独立问题。 |

## 定理 11 的边界与归属

Q_1=1，Q_2=7，Q_{j+1}=(4j+2)Q_j+Q_{j-1}，故 Q_{j+1}/Q_j=4j+O(1)，log Q_j=j log j+O(j)。BLR 两处增长假设不能互换。

1. 对 f_j(x)=Q_j x，导数就是 Q_j；在 (1,2) 取足够晚的尾列，f_j 和导数均大于 1，整数平移还原至 (0,1)。式 (1.1) 中任意两点的对数导数之比恒为 1。
2. 取 y_j=c j^{-α}、δ_j=j^{-α}/log(j+2)。对 α>0 且 c≥0，或 α=0 且 0≤c≤1/2，最终 y_j∈[0,1/2]，0<δ_j<1/4。式 (1.5) 的左侧约为 4j^{1−α}/log j，因 α<1 最终大于 2。式 (1.6) 的左侧为 1+log(Q_{j+1}/Q_j)/log Q_j→1；任意固定截尾仍然如此。直接把数据填进 (1.7) 虽算出 1−α，却缺少定理的假设。取稀疏子列可能改变增长率，也会丢掉两项之间的所有约束。
3. 令 G_N={x: 对每个 j≥N 都有 ‖Q_j x−y_j‖≤δ_j}。重编号仅把 G_N 写成“所有指标”；最终满足这一固定管道的集合是可数并 ∪_N G_N。由距离函数的 1-Lipschitz 性，在 G_N 上有 |j^α‖Q_jx‖−c|≤1/log(j+2)。包含方向是 G_N ⊂ 指定极限集，原极限没有给出此收敛速度，也未指定从圆周的哪一侧靠近。故管道维数只能直接传递下界。局部维数指小邻域交集维数的极限；若在一个位于 (0,1) 的邻域取得下界，即可给 [0,1] 的下界。相反，全局上界要用覆盖；单个局部值不足以推出。固定起点的初层管道可能有开间隙，不能把包含一个晚层母区间偷换成穿过任意给定点。
4. α=0 时 BLR 推论 8 直接给 {x:‖Q_jx−c‖→0} 在实线上的满维。其整数平移不变，实线是可数个单位区间的并，所以在 [0,1] 满维。由 Lipschitz 性，该集包含于 ‖Q_jx‖→c 的集合；上界为 1。c=0 两集相等。此论证包括 c=1/2。任意 c≥0 的无权次水平集都包含零极限集。
5. 0<α<1 时，在一个完全落于 (0,1) 的晚层母区间起步。记 r_j=δ_j/Q_j。完整子区间数至少 2(r_j−r_{j+1})Q_{j+1}−1，故可统一选 m_j=⌊j^{1−α}/log(j+2)⌋≥2 个。将起始区间仿射归一化。每代收缩比 r_{j+1}/r_j，同层各区间内部不交，满足 [2] 定义 1.1。写 M_n=∏_{j=N}^{n−1}m_j、ℓ_n=r_n/r_N。定理 2.1 的两端分别为 liminf log M_n / [−log(m_n ℓ_{n+1})] 和 liminf log M_n / [−log ℓ_n]。分子为 (1−α)n log n+o(n log n)；两个分母均为 n log n+O(n)，故选枝集维数为 1−α。对整个极限集，上界来自正文定理 10：任取 t>c，最终 ‖Q_jx‖≤t j^{-α}；先按起点分成可数并，再在固定单位区间逐层覆盖。子水平集的下界取零极限子集。这样得到的是“经典 Moran 维数定理＋本文格点计数及覆盖的短推论”。

**可直接替换的英文归属段落**

> The unweighted assertion for every prescribed limit in [0,1/2] follows from Corollary 8 of Bugeaud, Liao and Rams, by taking a constant target and using integer periodicity and the Lipschitz continuity of distance to the integers. For positive subcritical weights, the logarithmic derivative ratio in hypothesis (1.6) of their Theorem 7 tends to one in our setting. Our lower bound follows from the grid count below and the homogeneous Moran dimension bounds of Feng, Wen and Wu (Theorem 2.1). The covering estimate of Theorem 10 supplies the matching upper bound.

## 定理 12 的三层检验

| 层次 | 原文覆盖 | 本文须保留的识别或证明 |
|---|---|---|
| 有限字母表与指定尺度 | [3] §5 以尾间隙和除以指标确定结点，给相应的 C_a 构造 gauge。 | 此处由整数缺陷 d_j 和递推得到 b=2k+1，定义 h_k(1/Q_n)=b^{-n}，结点间线性插值。若想直接套 [3]，尚须证明间隙排列适配且两个 gauge 在零附近可比较。正文的直接计数已绕过此步骤。 |
| 精确谱层正测度 | [3] 定理 3 的对象是其构造的紧集。 | 正文 317–351 行：固定初值实现全部 b 进缺陷尾，等权分布与短区间至多三个前缀给 μ(I)≤3b^{N+1}h_k(长度)。严格次水平集最终只有 2k−1 个字母，单类第 n 层覆盖成本至多常数乘 ((2k−1)/b)^n。先得次水平集正、严格次水平集零，差集才是正测度的精确层。 |
| 整层无穷且 σ 有限 | [3] 给的是单个紧集的正有限测度，没有给出这两个结论。 | 正文 320–327、352–364 行：按起点和两个初始舍入整数分可数类，每类有统一有限覆盖成本。整层是 Lebesgue 零 Borel 集并在稠密子群 L 下平移不变。若其 h_k 测度正有限，归一化限制后，对连续函数用一致连续性把不变性延至整个圆周；等长圆弧等质量遂推出它是 Lebesgue 概率，矛盾。该唯一性论证需要有限测度，σ 有限性来自前面的覆盖。 |

结论限于已核查文献：计数尺度与质量分布方法有先例；未找到直接识别本递推的精确层并给出该指定测度全部结论的已发表定理。定理 12 的归属可以写为 “The gauge is adapted to the defect alphabet and the scales of this recurrence. Classical exact-gauge results for gap-generated Cantor sets include Cabrelli et al., §5, Theorem 3. The passage to the exact level and the size of the entire level are proved below.” 不宜据此作首创性断言。

## 主线候选四行核验

**A1 · 固定 π 与指定剩余类 [4]**

- 原定理：定理 1，式 (5)，无穷多 p=am+r、d=bn+s 满足 |dξ−p|≤ab/(4|d|)（d≠0）。
- 量词：任意固定无理 ξ，固定 a,b≥1 及合法剩余 r,s，(r,s)≠(0,0)；m,n 为整数。
- 代入：ξ=π，a=1，取 b=Q_j>1、s=1。得到 |d| 与 Q_j 互素的无穷多个分母；若 d<0，同时变号亦保持互素。
- 缺口：对该固定 j，不保证 1≤|d|≤H_j，且上界为 Q_j/(4|d|)。在窗口内它远大于所需 1/(H_j+1)。让 j 变化也无法同步两个量词。

**A2 · 连分数分母模分布 [5]**

- 原定理：定理 1 及其后对 f(q_n mod m) 的推论，给相邻收敛矩阵在固定模数下的统计规律。
- 量词：固定 m，随机无理数输入；几乎必然结论允许零测例外集。
- 代入：固定 m 时可选 f 为“分母与 m 互素”的指示函数，或定一个剩余类。
- 缺口：需要指定 ξ=π、由 H_j 选择的收敛指标、随 j 变化的模数 Q_j。即便对某固定数知道全序列频率，仍不能直接限制到这些指标。

**A3 / C2 · 固定 π 的整数形式 [6]**

- 原定理：命题 7、8 及文末给整数形式 I'_n=a'_n+b'_nπ，limsup n⁻¹log|I'_n|≈−1.902916，lim n⁻¹log b'_n≈11.613890，推出 μ(π)≤μ₀=7.1032053341370017…。
- 量词：固定 π；对任意 ν>μ₀，所有充分大分母 d 有 |dπ−p|>d^{1−ν}。
- 代入：命题 8.1 中可推出 d>(H_j+1)^{1/(ν−1)}（大 j 的合格分母自动趋于无穷）。C 可直接用已经清分母的 I'_n，与另一条整数形式 Ae−P 对齐。
- 缺口：大小下界允许 d 是 Q_j 的倍数。对 C，令 g=gcd(|A|,|b'_n|)，合成误差是 (b'_n/g)(Ae−P)+(A/g)I'_n；两放大因子及和的非零性须单独控制。文献给 π 行的速率，未给两行的共同因子。

**B · 阶乘基数字与分布 [7]**

- 原定理：注 1.11 给任意基本序列的分布正规数满 Lebesgue 测度；定理 1.15（归于 Korobov）给 q_n→∞ 时等价的数字均匀分布判别。
- 量词：满测度结论涉及几乎处处 x。数字等价本身逐点成立，但其右侧同样需要验证。该文定义 1.5 采用不最终全取最大位的规范展开。
- 代入：q_i=i+1，乘积为 (i+1)!。取 x={−π}，则分布序列正是负号阶乘轨道（指标平移一位）。若有分布正规性，[1/4,3/4] 将被访问无穷次，立即排除 n{−n!π}→1。
- 缺口：没有查到针对该固定数的所需回访或数字结论。更弱的准确目标可直接写成数字：令 t_n={−n!π}，a_{n+1}=⌊(n+1)t_n⌋，则 a_{n+1}=(n+1)t_n−t_{n+1}。若 nt_n→1，则 t_{n+1}→0，整数 a_{n+1}→1，故最终全为 1。反之，若最终全为 1，则 t_n=Σ_{k≥1} n!/(n+k)!，因首项为 1/(n+1)、余尾为 O(n⁻²)，有 nt_n→1。因此 B 只需证无穷多 a_{n+1}≠1。此等价是初等推导；固定 −π 的数字输入仍缺失。有限位计算不能排除最终全为 1。

**C1 · 同一系数的指数—对数逼近 [8]**

- 原定理：§2.1 定理 1，式 (2.3)–(2.5)，同一 P(z) 乘 exp(z) 和 log(1−1/z)，给显式余项。校正版定理 3，式 (2.13)–(2.15)，改为 exp(1/z) 和同一对数，均在无穷远展开。
- 量词：定理 1 参数 a,b,c,d,f 非负且 a+b+d≥c；定理 3 参数 c,d,f 非负，d≥2c，f≥c。消失阶指变量趋近展开点，未给定点处随次数增长的整数线性形式结论。
- 代入：式 (2.3) 的每项系数为整数除以 j!，j≤d，故 d!P∈ℤ[z]；若 z=u/v 为有理数，d! v^{deg P} 可清 P(u/v) 的分母。定理 1 用 z=1 获取 e 会遇到对数奇点；例如取 z=(1+i)/2，则 1−1/z=i，主值对数为 iπ/2，但同时得到的是 exp((1+i)/2)。作者式 (2.1)、(2.2) 及 §7.1 可供改构造时核验余项。
- 缺口：两个评价点的 P 值一般不同，且复系数需转换为整数；仅清 P 的分母不保证其余多项式的评价值均为整数。即使成功对齐，仍需清分母后的余项在次数趋于无穷时趋零，并证无穷多次非零。引用定理 3 时须采用作者 2021 年勘误版。

## 可引用书目与原文入口

1. Yann Bugeaud, Lingmin Liao and Michał Rams, “Metrical results on the distribution of fractional parts of powers of real numbers,” *Proceedings of the Edinburgh Mathematical Society* (2) **62** (2019), no. 2, 505–521. [DOI](https://doi.org/10.1017/S0013091518000585) · [作者修订稿](https://irma.math.unistra.fr/~bugeaud/travaux/power-diop-revised.pdf) · [arXiv:1710.03596](https://arxiv.org/pdf/1710.03596).
2. De-Jun Feng, Zhi-Ying Wen and Jun Wu, “Some dimensional results for homogeneous Moran sets,” *Science in China Series A* **40** (1997), no. 5, 475–482. [DOI](https://doi.org/10.1007/BF02896955) · [作者提供的期刊扫描件](https://www.math.cuhk.edu.hk/~djfeng/fengpapers/old-papers/FWW_SC.pdf).
3. Carlos Cabrelli, Franklin Mendivil, Ursula M. Molter and Ronald Shonkwiler, “On the Hausdorff h-measure of Cantor sets,” *Pacific Journal of Mathematics* **217** (2004), no. 1, 45–59. 出版版定理 3，p. 57；早期作者稿编号为定理 5。[期刊全文](https://msp.org/pjm/2004/217-1/pjm-v217-n1-p04-s.pdf).
4. Faustin Adiceam, “Rational approximation and arithmetic progressions,” *International Journal of Number Theory* **11** (2015), no. 2. [DOI](https://doi.org/10.1142/S1793042115500232) · [作者稿](https://arxiv.org/pdf/1408.6151).
5. Bence Borda, “Equidistribution of continued fraction convergents in SL(2,ℤ_m) with an application to local discrepancy,” *Journal of Modern Dynamics* **21** (2025), 327–359. [DOI](https://doi.org/10.3934/jmd.2025005) · [作者稿](https://arxiv.org/pdf/2303.08504).
6. Doron Zeilberger and Wadim Zudilin, “The irrationality measure of π is at most 7.103205334137…,” *Moscow Journal of Combinatorics and Number Theory* **9** (2020), no. 4, 407–419. [期刊全文](https://msp.org/cnt/2020/9-4/moscow-v9-n4-p06-s.pdf) · [DOI](https://doi.org/10.2140/moscow.2020.9.407).
7. Bill Mance, “Cantor series constructions of sets of normal numbers,” *Acta Arithmetica* **156** (2012), no. 3, 223–245. [DOI](https://doi.org/10.4064/aa156-3-2) · [期刊全文](https://www.impan.pl/shop/en/publication/transaction/download/product/83485).
8. Tanguy Rivoal, “Simultaneous Padé approximants to the Euler, exponential and logarithmic functions,” *Journal de Théorie des Nombres de Bordeaux* **27** (2015), no. 2, 565–589. [出版版](https://doi.org/10.5802/jtnb.914) · [作者校正版](https://rivoal.perso.math.cnrs.fr/articles/explog.pdf).
