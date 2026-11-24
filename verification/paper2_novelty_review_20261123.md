# 论文二新颖性与引用核查（2026-11-23）

**一句总判断**：对论文二 7 组主结果做了多路检索，并逐字打开 6 份原文 / 元数据核对。没有找到与 R1–R3（$e$ 收敛子分母上的全谱离散、临界精确规范、正能级三向分裂）或 R7（残差维数大模数二阶渐近）相同的先例，**但这只是负搜索**。同时发现一个**必须在论文中处理的重叠风险**：Bugeaud–Liao–Rams（BLR）定理 7 的 δ 型维数公式代入 $f_n(x)=Q_nx$ 后，与论文二 R4 的 $1-\alpha/r$、R5 的 $\frac{1-\tau}{1+\tau\gamma_{\sup}}$ 给出相同的值。BLR 的假设 (1.6) 对阶乘型 $Q_j$ 不成立，所以论文二的结论一般不是 BLR 的直接特例。论文对 $e$ 情形已经做了这一比较（第 355–362、1167–1170 行），但多项式递推和增长商递推两节没有；而且在增长商递推中，当 $\log A_j/\log Q_j\to\infty$ 时 (1.6) 反而成立，BLR 定理 7 可能直接覆盖该子情形。抽查的 3 条书目全部无误。本核查不涉及 $e+\pi$，对原问题无推进。

检索范围：2026-11-23 的 WebSearch（标准模式 6 次、扩展模式 2 次，关键词见 §4），web-fetch 逐字阅读 arXiv 摘要页与 HTML 全文（PDF 无法解码时以 HTML 为准），Crossref API 元数据查询。**未检索** zbMATH / MathSciNet、Google Scholar 引用链、中文数据库，也未读专著（Galambos 1976、Iosifescu–Kraaikamp 2002 等）。

## 1. 逐项对照表

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| R1 全谱 $\Lambda(\mathbb R)=\frac14\mathbb Z_{\ge0}\cup\{\infty\}$，$\{\Lambda=0\}=\mathbb Z+\mathbb Z\frac{e+1}2$ | 无条件新结果（作者自报 Lean 已闭合） | **负搜索未找到先例** | 零水平集刻画建立在 Kraaikamp–Liardet（PAMS 112, 1991）与 BDS（Studia 38, 2001）的"好逼近"子群刻画之上（论文已引用）；Dirichlet / Lagrange 型谱文献研究的是对全体无理数的 $\limsup q_{k+m}\|q_k\alpha\|$，对象不同 | §2.1 |
| R2 临界精确规范 $h_k$、$\sigma$-有限、每开弧测度无穷、三种 $\liminf$ 情形 | 无条件新结果（作者自报） | **负搜索未找到先例** | 方法上与齐次 Moran 集精确测度相关：CMMS（论文已引用）；Devos–Loosveldt–Nicolay 对 Cantor 展开的广义 Cantor 集证明 $\mathcal H^h(C_{q,n})=1$（定理 4.2，$h$ 取魔鬼阶梯函数）。后者是单个齐次集的精确测度，论文二是水平集的规范三分法，结论不重叠 | §2.2 |
| R3 正能级三向分裂（limsup 层基数 $2k+1$ / 无符号精确极限集普适基数 2 / 有符号集坍缩为陪集） | 无条件新结果（作者自报） | **负搜索未找到先例** | 未见同类陈述 | — |
| R4 多项式递推 $Q_{j+1}=(cj^r+d)Q_j+Q_{j-1}$：谱 $\frac1c\mathbb Z_{\ge0}\cup\{\infty\}$、规范、次临界维数 $1-\alpha/r$ | 谱与规范部分：无条件新结果（作者自报）；**维数公式部分：与 BLR 定理 7 公式重合，需在文中比较** | 谱与规范：负搜索未找到先例。维数：**已核实存在形式重合** | BLR 定理 7（arXiv:1710.03596v1）在 (1.1)(1.5)(1.6) 下给出 $\dim=\liminf_n\frac{\log f_n'+\sum_{j<n}\log\delta_j}{\log f_n'-\log\delta_n}$；取 $f_n=Q_nx$、$\delta_j=cj^{-\alpha}$ 得 $1-\alpha/r$。但 (1.6) 要求 $\log f'_{n+1}/\log f'_n\to\infty$，对 $Q_j$ 不成立；BLR 只在证明草图中提到用 Baker 插补去掉 (1.6)，没有写成定理 | §2.3、`blr_formula_compare_20261123.py` |
| R5 增长商递推：$\Lambda_G$ 与 KL 误差比恒等、谱 $\mathbb Z_{\ge0}\cup\{\infty\}$、维数 $\frac{1-\tau}{1+\tau\gamma_{\sup}}$、超临界相变 $\tau_{\rm crit}=1+1/\gamma_{\sup}$ | 同 R4：谱、恒等式、超临界相变为无条件新结果（作者自报）；**次临界维数公式与 BLR 定理 7 重合** | 同 R4；**另有一个子情形可能是已知结果** | 当 $\gamma_{\sup}<\infty$（如 $A_j=2^{2^j}$，$\gamma_{\sup}=1$）时 $\log Q_{n+1}/\log Q_n$ 有界，(1.6) 不成立。但若 $\lim_j\log A_j/\log Q_j=\infty$（极限而非上极限），则 $\log Q_{j+1}/\log Q_j\to\infty$，(1.6) 成立，BLR 定理 7 在 (1.1)(1.5) 也满足时可直接给出维数，论文二该子情形的结论（维数为 0）可能是其推论，**待逐条核对 (1.1)(1.5)**。BLR 定理 3（线性情形）给出 $\{\|a_nx-y_n\|<a_n^{-\tau}\ \text{i.o.}\}$ 的维数 $1/(1+\tau)$，是另一类集合 | §2.3 |
| R6 有限水平集维数 0；$0\le\alpha<1$ 时次临界维数 $1-\alpha$ | $\alpha=0$：已有结果的推论（论文已致谢 BLR）；$0<\alpha<1$：同 R4 | 已核实（BLR 推论 8 原文） | BLR 推论 8：$a_{n+1}/a_n\to\infty$ ⇒ $\dim_H\{x:\|a_nx-y_n\|\to0\}=1$，与论文用法一致 | §2.3 |
| R7 $\dim_H E_m=\dim_H F_{m,1}$；全模严格分离；$\dim_H F_{m,r}=\frac12+\frac{C_r}{2m}-\frac{C_r^2\log m}{2m^2}+O(m^{-2})$，$C_1=\psi_{\rm Fib}$ | 无条件新结果（作者自报 Lean 已闭合） | **负搜索未找到先例** | CLU（Trans. AMS 373, 2020）证明等差数字集维数谱满，并给出若干数值；Hensley 给出 $\{a_i\le N\}$ 的 $1-c/N$ 型渐近，Good 给出 $\{a_i\ge N\}$ 趋于 1/2；Fang–Moreira–Zhang（arXiv:2409.00521）已逐字读到的部分没有等差数字集的大模数展开。未见 $\frac{C_r}{2m}$ 型展开或与倒数 Fibonacci 常数的联系 | §2.4 |

## 2. 原文核对记录

### 2.1 Kraaikamp–Liardet、BDS（书目）
- Kraaikamp, Liardet, *Good approximations and continued fractions*, Proc. Amer. Math. Soc. 112 (1991), 303–309，DOI 10.1090/s0002-9939-1991-1062392-7（Crossref）。与论文二条目一致；论文条目缺 DOI，建议补上。
- Bíró, Deshouillers, Sós, *Good approximation and characterization of subgroups of $\mathbb R/\mathbb Z$*, Studia Sci. Math. Hungar. 38 (2001), 97–113，DOI 10.1556/sscmath.38.2001.1-4.7（Crossref）。与论文二条目一致；同样建议补 DOI。
- 本次未打开两文全文，论文所引"[BDS] Lemma 4.1"的定理号**未核到**。

### 2.2 Cantor 级数方向
- Cheng, Zhang, *Exact approximation order of real numbers in Cantor series expansions*, arXiv:2606.30435（v1 2026-06-29，v2 2026-09-19），无期刊信息。定理 1.1：在 $\log q_n/\log(q_1\cdots q_n)\to0$ 下 $\dim_H E_c(\psi)=1/(1+\alpha)$。只研究维数，没有谱和 $h$-测度，也不涉及 $Q_{n+1}=A_nQ_n+Q_{n-1}$。可在引言作为"沿序列逼近"的相关工作引用。
- Devos, Loosveldt, Nicolay, *On the fractal properties of generalized Cantor sets and devil's staircase functions*（ORBi 预印本 PDF，11 页，本地抽取文本阅读）。定理 4.2：$\mathcal H^{D_{q,n}}(C_{q,n})=1$。发表信息、年份**未核到**（PDF 致谢提到审稿人，说明已投稿或已发表）。

### 2.3 BLR（arXiv:1710.03596v1，HTML 逐字）
- 书目：Bugeaud, Liao, Rams, *Metrical results on the distribution of fractional parts of powers of real numbers*, Proc. Edinb. Math. Soc. (2) 62 (2019), no. 2, 505–521（Crossref：在线 2018-11-29）。与论文二条目一致。
- 推论 8 原文：$(a_n)$ 正实数列、$a_{n+1}/a_n\to+\infty$ ⇒ 对任意 $(y_n)$，$\dim_H\{x:\lim\|a_nx-y_n\|=0\}=1$。论文二的引用（"Cor. 8, the hypothesis is $Q_{j+1}/Q_j\to\infty$"）准确。注意：v1 中推论 8 没有给出证明；出版版的编号**未核到**。
- 定理 7 原文：在 (1.1)、(1.5)、(1.6) 下，$G(f,y,\delta)=\{x:\|f_n(x)-y_n\|\le\delta_n\ \forall n\}$ 的局部维数等于上式 liminf。(1.6)：$\lim\log f'_{n+1}(x)/\log f'_n(x)=\infty$。
- 数值比较（`blr_formula_compare_20261123.py` / `.log`，mpmath 60 位，整数递推）：$A_j=4j+2,\alpha=\frac12$ 时比值在 $n=100,1000,4000$ 处为 0.365、0.405、0.420，单调上升趋向 0.5；$A_j=j^2+1,\alpha=\frac12$ 时为 0.559、0.633、0.655，趋向 0.75；$A_j=2^{2^j},\tau=\frac12$ 时 $n=18$ 为 0.333253，趋向 1/3。前两例的剩余偏差约为 $\log(1/c)/\log n$ 量级。这是有限计算，只作佐证。

### 2.4 残差渐近方向
- CLU 已在既有记录 `residues_literature_20261121.md` 中逐条核对，本次未重复。
- Fang, Moreira, Zhang, arXiv:2409.00521v1（2024-08-31，56 页，无期刊信息）：逐字读到的部分（约 0–40k 与 140k–170k 字符）没有等差数字集或大参数展开；中间部分只读到模型摘要，**未逐字核对**。

## 3. 建议的论文修改（未执行，待作者确认）

1. **必做**：论文已对 $e$ 情形与 BLR 定理 7 做了比较（第 355–362、1167–1170 行），但没有写明两者的公式值重合。建议在 `thm:poly-phase-transition` 与 `thm:growing-rec-dim-phase` 后加一段同样的比较，并单独说明 $\lim\log A_j/\log Q_j=\infty$ 子情形与 BLR 定理 7 的关系，大意如下：
   > Formally, the value $1-\alpha/r$ (resp. $(1-\tau)/(1+\tau\gamma_{\sup})$) coincides with the dimension formula of Bugeaud–Liao–Rams [BLR, Theorem 7] for sets $\{x:\|f_n(x)-y_n\|\le\delta_n\ \forall n\}$, evaluated at $f_n(x)=Q_nx$. Their theorem assumes $\log f'_{n+1}/\log f'_n\to\infty$ (condition (1.6)), which fails for the present sequences since $\log Q_{j+1}/\log Q_j\to1$ (resp. stays bounded when $\gamma_{\sup}<\infty$); our proofs do not use that condition.
   
   写进去之前需要作者确认两点：论文二的证明确实不依赖 (1.6)；两者的集合在"对所有 $n$"与"最终成立"之间的差别（可数并）不影响维数。
2. 引言补引 Cheng–Zhang（arXiv:2606.30435）作为 Cantor 级数下逼近阶维数的相关工作，补引 Devos 等人作为 Cantor 展开下精确 $h$-测度的相关工作（后者书目待核）。
3. KL、BDS 两条补 DOI。
4. 新颖性表述统一改成"to our knowledge"口径，不写"first"。

## 4. 检索式（2026-11-23）
1. formally verified Hausdorff dimension bounds continued fraction Cantor set Lean Coq Isabelle certificate
2. rigorous computation Hausdorff dimension continued fractions restricted digits transfer operator computer-assisted proof Mathlib
3. Erdős Taylor lacunary sequence set of x with ||q_n x|| tends to 0 countable q_{n+1}/q_n tends to infinity Hausdorff dimension
4. Hausdorff dimension continued fraction digits in arithmetic progression asymptotic as modulus tends to infinity 1/2 + c/m
5. Diophantine approximation along convergent denominators of e limsup n ||q_n x|| spectrum
6. Cantor series expansion digits restricted exact Hausdorff measure gauge function growing bases q_n
7. （扩展）Hausdorff dimension continued fractions partial quotients congruent modulo m residue class asymptotic dimension tends to 1/2
8. （扩展）"arithmetic progression" continued fraction Cantor set Hausdorff dimension asymptotic expansion large common difference Hensley
9. reciprocal Fibonacci constant Hausdorff dimension continued fractions partial quotients asymptotic
