# 加权逼近谱的相变：上界定理 dimH ≤ 1−α（严格数学证明）

**对象** 沿用 $e$ 的选定收敛子分母 $Q_j$（$Q_{j+1}=(4j+2)Q_j+Q_{j-1}$，$Q_j\ge j!$，$Q_{j+1}\le(4j+3)Q_j$）。
对 $\alpha\in[0,1]$ 与 $x\in\mathbb R$ 定义加权逼近指数
$$\Lambda_\alpha(x):=\limsup_{j\to\infty} j^{\alpha}\,\|Q_j x\|\in[0,\infty],$$
水平集 $E_c^{(\alpha)}:=\{x:\Lambda_\alpha(x)\le c\}$。$\alpha=1$ 即第一/二阶段的 $\Lambda$。

**主定理（上界）** 对一切 $\alpha\in[0,1]$ 与有限 $c\ge0$，
$$\dim_H E_c^{(\alpha)}\ \le\ 1-\alpha .$$
特别地 $\alpha=1$ 给出 $\dim_H E_c^{(1)}=0$（即已机器验证的 T-finite）；$\alpha=0$ 给出平凡上界 $1$。

**对原猜想的修正** 第二阶段论文原猜想"$\alpha<1$ 时 $\dim_H=1$"是**错误的**。
正确临界指数是 $1-\alpha$（随 $\alpha$ 线性下降），而非在 $\alpha=1$ 处从 $1$ 跳变到 $0$。
上界 $\le1-\alpha$ 由本文证明；下界 $\ge1-\alpha$ 仍需质量分布原理，列为猜想（见 §5）。

> 可信度：本文上界为**严格纸面数学证明**；其 $\alpha=1$ 特例已 Lean 内核验证
> （`DimHFinite.dimH_levelSet_finite`，仅基础公理）。一般 $\alpha$ 的完整形式化列为工程义务（§6）。
> 数值仅佐证标度，不参与证明。

---

## 1. 覆盖的构造

固定有限 $c$ 与 $t>c$，$\alpha\in[0,1]$。由 $\Lambda_\alpha(x)\le c<t$ 知
$j^\alpha\|Q_jx\|\le t$ 对充分大 $j$ 成立，故存在 $J\ge1$ 使
$$E_c^{(\alpha)}\subseteq\bigcup_{J\ge1}\bigcap_{j\ge J}A_j^{(\alpha)}(t),\qquad
A_j^{(\alpha)}(t):=\{x:\|Q_jx\|\le t/j^\alpha\}.$$
$A_j^{(\alpha)}(t)$ 是 $Q_j$ 个区间之并：中心 $k/Q_j$（$k=0,\dots,Q_j$），半径
$$r_j:=\frac{t}{j^\alpha Q_j}.$$
记 $C_J:=\bigcap_{j\ge J}A_j^{(\alpha)}(t)$（嵌套 Cantor 型集）。只须证 $\dim_H C_J\le1-\alpha$，
再对可数并取上确界。

## 2. 分支数引理（关键标度）

**引理 2.1** 存在常数 $K=K(t,\alpha)$（与 $j$、父中心无关）使：对 $j\ge1$，任一第 $j$ 层存活区间
（中心 $k/Q_j$）在第 $j+1$ 层的存活子区间个数 $B_j$ 满足
$$B_j\ \le\ K\,j^{\,1-\alpha}.$$

**证明** 子区间中心 $k'/Q_{j+1}$ 存活当且仅当它与某父中心距离 $\le r_j+r_{j+1}$，即
$$\Big|\frac{k}{Q_j}-\frac{k'}{Q_{j+1}}\Big|\le r_j+r_{j+1}
\iff |k'Q_j-kQ_{j+1}|\le (r_j+r_{j+1})Q_jQ_{j+1}.$$
对固定 $k$，满足条件的整数 $k'$ 落在一个长度
$$L_j:=2(r_j+r_{j+1})Q_{j+1}
=2t\Big(\frac{Q_{j+1}}{j^\alpha Q_j}+\frac{1}{(j+1)^\alpha}\Big)$$
的实区间内，故 $B_j\le L_j+1$。用 $Q_{j+1}\le(4j+3)Q_j\le 7j\,Q_j$（$j\ge1$）：
$$\frac{Q_{j+1}}{j^\alpha Q_j}\le 7\,j^{1-\alpha},\qquad
\frac{1}{(j+1)^\alpha}\le 1\le j^{1-\alpha}\ (\alpha\le1,\ j\ge1).$$
故 $L_j\le 2t(7+1)j^{1-\alpha}=16t\,j^{1-\alpha}$，从而
$$B_j\le 16t\,j^{1-\alpha}+1\le (16t+1)\,j^{1-\alpha}=:K j^{1-\alpha}$$
（因 $j^{1-\alpha}\ge1$）。$\blacksquare$

**注** $\alpha=1$ 时 $B_j\le K$ 一致有界——这正是 T-finite 的一致分支界
（`DimHCore.fiber_card_le`，$K=\lfloor16t\rfloor+1$）。$\alpha<1$ 时分支随 $j^{1-\alpha}$ 增长，
这是相变的来源。

## 3. 内容标度与上界

第 $n$ 层（$n\ge J$）存活区间数 $N_n$ 满足
$$N_n\le (Q_J+1)\prod_{j=J}^{n-1}B_j
\le (Q_J+1)K^{n}\prod_{j=J}^{n-1}j^{1-\alpha}
\le (Q_J+1)K^{n}(n!)^{1-\alpha}.$$
每个第 $n$ 层区间直径 $\le 2r_n=2t/(n^\alpha Q_n)\le 2t/(n^\alpha n!)$（用 $Q_n\ge n!$）。
对 $s>0$，$s$-内容
$$\mathcal C_n(s):=N_n(2r_n)^s
\le (Q_J+1)K^n(n!)^{1-\alpha}\Big(\frac{2t}{n^\alpha n!}\Big)^s
=(Q_J+1)(2t)^s K^n\,n^{-\alpha s}(n!)^{1-\alpha-s}.$$

**引理 3.1** 若 $s>1-\alpha$，则 $\mathcal C_n(s)\to0$。

**证明** 取对数，用 $\log n!=n\log n-n+O(\log n)$（Stirling，或显式界 $n!\ge(n/e)^n$）：
$$\log\mathcal C_n(s)\le C_0+n\log K-\alpha s\log n+(1-\alpha-s)\log n!
=(1-\alpha-s)\,n\log n+O(n).$$
因 $1-\alpha-s<0$，主项 $(1-\alpha-s)n\log n\to-\infty$ 且压过 $O(n)$，故
$\log\mathcal C_n(s)\to-\infty$，即 $\mathcal C_n(s)\to0$。$\blacksquare$

（严格化不用渐近记号：对 $s>1-\alpha$ 取 $\varepsilon=(s-(1-\alpha))/2>0$，
用 $n!\ge(n/e)^n$ 得 $(n!)^{1-\alpha-s}\le (n/e)^{-2\varepsilon n}$，
而 $K^n n^{-\alpha s}(n/e)^{-2\varepsilon n}\to0$ 因指数底 $K e^{2\varepsilon}/n^{2\varepsilon}\to0$。
这与 T-finite 用 `tendsto_pow_div_factorial_atTop` 的显式手法同型。）

**定理 3.2（上界）** $\dim_H C_J\le1-\alpha$，从而 $\dim_H E_c^{(\alpha)}\le1-\alpha$。

**证明** 对任意 $s>1-\alpha$，第 $n$ 层区间族覆盖 $C_J$，直径 $\to0$，且
$\sum(\text{diam})^s\le\mathcal C_n(s)\to0$。由 Hausdorff 测度的覆盖判据
（`hausdorffMeasure_le_liminf_sum`）得 $\mathcal H^s(C_J)=0$，故 $\dim_H C_J\le s$。
令 $s\downarrow1-\alpha$ 得 $\dim_H C_J\le1-\alpha$。
$E_c^{(\alpha)}\subseteq\bigcup_J C_J$ 为可数并，$\dim_H$ 可数稳定，故
$\dim_H E_c^{(\alpha)}\le1-\alpha$。$\blacksquare$

**推论 3.3** $\alpha=1$：$\dim_H E_c^{(1)}\le0$，即 $=0$（T-finite，已机器验证）。
$\alpha=0$：$\le1$（平凡）。

## 4. 为什么原猜想错误：标度的直接反驳

原猜想断言 $\alpha<1$ 时 $\dim_H=1$。但引理 2.1 给出 $B_j\asymp j^{1-\alpha}$，
代入内容得临界 $s=1-\alpha<1$（当 $\alpha>0$）。例如 $\alpha=\tfrac12$ 时上界为 $\tfrac12$，
**严格小于 1**，直接否定"$\alpha<1$ 维数 1"。
数值（mpmath）核验 $\log\mathcal C_n(s)$ 的主项系数为 $(1-\alpha-s)$：
$s>1-\alpha$ 时随 $n$ 递减（渐近），$s<1-\alpha$ 时递增，与理论一致。
（小 $n$ 时因 $O(n)$ 项尚未被 $n\log n$ 压过而看似递增，交叉点 $n\sim e^{\log K/(s-(1-\alpha))}$
极大，不影响渐近结论。）

## 5. 下界（猜想，开放）

**猜想 5.1** 对 $\alpha\in[0,1)$ 与 $c>0$，$\dim_H E_c^{(\alpha)}\ge1-\alpha$，
从而 $\dim_H E_c^{(\alpha)}=1-\alpha$。

**思路与障碍** 上界用覆盖；下界需质量分布原理（Frostman）：在 $C_J$ 上构造概率测度 $\mu$
使 $\mu(I)\le C|I|^{1-\alpha}$ 对所有区间 $I$。自然候选是把质量均匀分配到存活子区间
（每父 $B_j\asymp j^{1-\alpha}$ 个子区间均分）。但需控制"区间 $I$ 跨多层时的质量"，
即证明存活树足够"满"（分支不仅上界而且下界 $\asymp j^{1-\alpha}$，且分布均匀）。
分支下界需要 $Q_{j+1}/Q_j\ge c j$（成立，$\ge4j$）与区间重叠的精细计数，
目前未完成；故下界列为开放。$\alpha=0$ 的下界 $1$ 是经典（坏逼近/满维数集），可作 sanity check。

**诚实定位** 本文只证上界。相变"恰好等于 $1-\alpha$"是猜想，上界半已证、下界半开放。
不得声称相变定理完全解决。

## 6. 形式化状态与工程义务

- $\alpha=1$ 上界（$=0$）：已 Lean 内核验证（`DimHFinite.dimH_levelSet_finite`），仅基础公理。
- 一般 $\alpha$ 上界：本文纸面严格证明；完整 Lean 形式化需把 `DimHFinite` 的覆盖论证
  推广到实数权重 $j^\alpha$（rpow），分支界引理 2.1 与内容引理 3.1 的一般 $\alpha$ 版。
  列为工程义务 OBL-3a（上界形式化）。
- 下界：开放数学问题 OBL-3b。

## 7. 与已有结果的一致性

- $\alpha=1$：与 T-finite 一致（$\le0$）。
- $\alpha=0$：$\Lambda_0(x)=\limsup\|Q_jx\|$。$\{ \Lambda_0=0\}$ 可数（$\subseteq L$，维数 0），
  但正水平集 $\{\Lambda_0\le c\}$ 上界 1、猜想下界 1（满维数），与经典坏逼近型集维数 1 相容。
  注意零集与正水平集维数不同，相变陈述针对正水平集。
- 方法论：覆盖+分支标度是 Eggleston/BLR 型经典方法；新颖在给出**随 $\alpha$ 线性变化的
  临界指数 $1-\alpha$** 这一精确标度，并纠正原跳变猜想的错误。

---

**公理/验证审计** 本文上界为纸面证明；其 $\alpha=1$ 特例机器验证
（`[propext, Classical.choice, Quot.sound]`，零 sorryAx）。一般 $\alpha$ 与下界未机器验证，
明确标注。$e+\pi$ 无理性仍开放，本文不涉及。
