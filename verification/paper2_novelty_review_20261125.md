# 论文二投稿前新颖性核查：残差 / 多残差维数结果（2026-11-25）

**一句总判断**：论文二的残差与多残差维数结果都**有实质性的方法先例**。Das–Fishman–Simmons–Urbański（下称 DFSU，Selecta Math. 29 (2023)）的定理 4.1 是一般扰动定理，处理"有限系统再添上导数很小的生成元"后维数的渐近展开，$F_{m,S,B}$ 这一族落在它的假设范围内。在 DFSU 的记号下，论文的主常数 $C_S$ 正是 $1/\bar c$。此外：
- 定理 `thm:multi-residue-asymptotic` 的 (i) 就是经典 Bowen 公式，(iii) 就是 $\zeta$ 在 1 处的经典 Laurent 展开。
- (v) 的上界与 (ii) 的超临界部分，是 Heinemann–Urbański (2002) 估计的直接推论。
- 剩下没有找到先例的只有一类：等差数字集这一具体族的**显式**系数，即 $C_r$、$\psi_{\rm Fib}$、$\frac12d^2C_S(\gamma C_S-C_S')$，以及全模 $m\ge2$ 的严格分离。这只是**负搜索**的结论。
- `rem:fourth-term` 的猜想系数 $\frac34\Gamma^3$ 与 DFSU 对 $\{a_i\le N\}$ **已证明**的 Lambert-W（树函数）系数公式 (1.4) 结构一致，是有力的结构旁证，但不构成证明。

据此，README 中"负搜索，未见先例"的表述、"无条件新结果"的分类，以及论文的 prior-work 段落，**都必须改写**（建议措辞见 §5）。本核查不涉及 $e+\pi$，对原问题无推进。

上一轮（`paper2_novelty_review_20261123.md`）已核对的内容本次不重复：CLU 表 1、BLR、Kraaikamp–Liardet / BDS 书目、Fang–Moreira–Zhang 等。

---

## 0. 检索范围（覆盖声明）

检索于 2026-11-24 执行（系统日期；文件名按任务要求取 20261125）。

| 渠道 | 次数 / 内容 | 备注 |
| :--- | :--- | :--- |
| arXiv API（export.arxiv.org） | 14 个检索式（§6），另有 2 个因 HTTP 429 限流失败，未重试 | 只检索摘要字段（`abs:`） |
| arXiv 全文（e-print TeX 源 / PDF） | 2007.10554v2（DFSU，**全文**）、1805.11904v1（CLU，TeX 源 + PDF 抽取文本，用于定理编号）、2111.02694v1（Takahasi，引言与书目）、1611.09276（Jenkinson–Pollicott 2018 预印本，关键词 grep）、1612.00870（Falk–Nussbaum 预印本，关键词 grep）、2504.20878v2（Chitanga–Lemmens–Nussbaum，摘要 + grep） | 源文件下载到 scratchpad 的隔离目录，只做阅读与 grep |
| arXiv 摘要页 | 2601.12737、2510.24064、2604.00587 | 均与等差/剩余类数字集无关 |
| Crossref API | 11 个书目查询（§2 各条） | 只采信 Crossref 元数据 |
| WebSearch | 3 次（1 次扩展、2 次标准），检索式见 §6 | — |
| 出版商页面 | Cambridge Core（Good 1941，只取得摘要首段）；DLMF §25.2（全文） | — |
| **被拒或拦截** | ScienceDirect 403（Hensley 1989 / 1992，curl 与内置浏览器均如此）；AMS "Verifying your connection" 机器人验证（MU 1999、CLU 出版版，**未绕过**）；IOP 500（Heinemann–Urbański 2002） | 这些文献的原文内容一律标「未核到」或「转引」 |

**未检索**：zbMATH / MathSciNet、Google Scholar 引用链、中文数据库、专著（Mauldin–Urbański 2003 GDMS 专著、Iosifescu–Kraaikamp 2002）。
**未全文核对**：Good 1941、Hensley 1989 / 1992、Mauldin–Urbański 1996 / 1999、Heinemann–Urbański 2002、Jaerisch–Kesseböhmer 2010 的原文。

---

## 1. 逐项对照表

图例（重叠程度）：**精确先例** / **特例已知** / **方法已知** / **负搜索未见先例**。

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| `thm:residues-asymptotic`(i) 预解式恒等式 $(r+x)^{-2s}V_{r,s}(\frac1{r+x})=V_{r,s}(x)-1$ | 5 文献核查与复现（初等恒等式） | 已核实（代数推导与论文证明一致） | **方法已知**。它等价于 $V_{r,s}=\sum_{n\ge0}\mathcal L_{\{r\}}^n\mathbf 1$（单字母系统的 Neumann 级数，即预解式 $(I-\mathcal L)^{-1}\mathbf 1$）。DFSU 的常数 $\bar c=1/\sum_m\nu L_1^m h$ 正是同一个 Neumann 级数在 $x=0$ 的值 | DFSU v2 §4 记号段（TeX 源第 700–720 行附近）与几何 PF 算子定义 (3.?)（TeX 第 532–536 行）；§2.1 |
| 同 (ii)：全模 $m\ge2$ 严格分离 $\dim F_{m,m}<\dim F_{m,1}=\dim E_m$ | 1 无条件新结果（窄） | **负搜索未见先例** | CLU 只对个别等差集给出数值界（上一轮已核）。DFSU 的渐近结果只对充分大的 $m$ 有效，不能给出"对一切 $m\ge2$" | §2.1、§2.2；上一轮 R7 |
| 同 (iii)：二项渐近 $\frac12+\frac{C_r}{2m}-\frac{C_r^2\log m}{2m^2}+O(m^{-2})$ | 1 无条件结果，但属于**已知一般方法的显式实例**（增量） | 显式公式：**负搜索未见先例**；方法：**已核实存在先例** | **方法已知**：DFSU 定理 4.1 的假设逐条对得上（$S=\{r\}$ 有限，$\Theta_S=-\infty$；$\delta=\frac12>\delta_S$；对称差中的数字 $\ge m$，故 $\sup\lvert b\rvert\to0$；$S'$ 强正则），由此得到隐式方程 $\Xi=0$。按 DFSU 记号自行推导：$h\equiv1$，$\nu f=f(0)$，$\delta=\frac12$，因此 $1/\bar c=\sum_n\sum_{w\in S^n}q(w)^{-1}=C_S$，首项 $\frac{dC_S}{2m}$ 与论文一致。DFSU **没有**处理等差数字集族（全文 grep "arithmetic / progression / congruen" 无命中），也没有给出 $C_r$、$\psi_{\rm Fib}$。$\log m/m^2$ 系数 $-2\cdot(\frac{C_r}2)^2$ 与 Hensley 的 $72/\pi^4=2(6/\pi^2)^2$ 同构（脚本 (B) 已验证） | §2.1、§3 |
| 同 (iv)：比值极限 $\to C_r$、$\psi_{\rm Fib}$；关于 $r$ 的最终单调性 | 1（(iii) 的直接推论） | 负搜索未见先例 | 同 (iii) | — |
| `thm:multi-residue-asymptotic`(i)：无 Bowen 公式 $\dim_H E_S=s_0(S)$ | **5 文献核查与复现**（经典结果的自含新证明与形式化）；**不是新结果** | **已核实存在精确先例**（经 CLU v1 原文） | **精确先例**：CLU v1 定理 2.3（引 Mauldin–Urbański 1996）给出 $h_{\mathcal S}=\dim_H J$，其中 $h$ 是压力 $P(t)=\lim\frac1n\log Z_n(t)$ 的零点；CLU v1 命题 2.6 的证明中有 $\lVert\phi'_\omega\rVert_\infty=q_n(\omega)^{-2}$，于是 $Z_n(t)=W_S(2t,n)$，$s_0(S)$ 就是压力零点。论文的贡献只是绕开压力形式化的证明路线，外加 Lean 形式化 | §2.2 |
| 同 (ii)：$\lim_m\dim F_{m,S,B}=\max(\frac12,s_0(S))$ | 部分为 5（已知结果的推论），部分为 1（窄） | 超临界与 $S=\emptyset$：已核实为推论（经 CLU 原文与 DFSU 转引）；$S\neq\emptyset$ 次临界：负搜索未见同形陈述 | **特例已知**：① $s_0(S)>\frac12$：由 Heinemann–Urbański 估计（CLU v1 定理 2.4 所述形式）加 CLU v1 命题 2.6 的 Lyapunov 下界即得 $\dim\to s_0$（见 (v) 行）。② $S=\emptyset$：$\mathcal A_{m,\emptyset,B}\subset\{a\ge m-\max B\}$，由单调性和 Good 定理（$\dim F_{\ge N}\to\frac12$，经 DFSU 引言转引）立得。③ $S\ne\emptyset$ 次临界：DFSU 命题 9.3 对"$F\cup$ 多项式序列尾部"写出了同型的极限 $\max(\delta_E,1/2d)$（$d=1$ 时就是 $F\cup\{N,N+1,\dots\}$），等差尾部的步长随 $m$ 增长，不在 DFSU 命题 9.3 的范围内，但论证同型：**方法已知** | §2.1、§2.2 |
| 同 (iii)：$\lvert\sum_k k^{-1-\varepsilon}-\varepsilon^{-1}-\gamma\rvert\le4\zeta(\frac32)\varepsilon$ | **5**（经典结果的定量形式） | **已核实精确先例**（DLMF 原页） | **精确先例**：DLMF (25.2.4) $\zeta(s)=\frac1{s-1}+\sum_n\frac{(-1)^n}{n!}\gamma_n(s-1)^n$；(25.2.5) 中取 $n=0$ 即 $\gamma_0=\lim(\sum_{k\le m}\frac1k-\ln m)=\gamma$。显式常数 $4\zeta(3/2)$ 是论文自己的初等界 | §2.4 |
| 同 (iv)：三项渐近，$m^{-2}$ 系数 $\frac12d^2C_S(\gamma C_S-C_S')$ | 1 无条件结果，但属于**已知一般方法的显式实例**（增量） | 显式系数：**负搜索未见先例**；方法：已核实存在先例 | **方法已知**：同 `thm:residues-asymptotic`(iii) 行。DFSU 定理 4.1 原则上给出可计算的全部系数，但没有对等差族写出；$\gamma$ 来自 Hurwitz/Riemann $\zeta$ 在 1 处的常数项，$C_S'$ 来自 $C_S(1+\varepsilon)$ 的导数，都是该框架中的标准来源 | §2.1、§3(C) |
| 同 (v)：超临界 $\Theta(m^{-2s_0})$ | 上界：**5**（已知定理的直接推论）；下界：1（窄），方法已知 | 上界：已核实为推论（定理陈述经 CLU 原文；HU 2002 原文未核到）；下界：负搜索未见先例 | **特例已知（上界）**：CLU v1 定理 2.4（引 [15] Heinemann–Urbański 与 [5] CLU 2018）：强正则系统 $\mathcal S$、有限 $F\subset E$、$h_F\ge\theta_{\mathcal S}$ ⇒ $\dim J_{\mathcal S}-\dim J_F\le\frac{K^{h_F}}{\chi_{\mathcal S}}\sum_{E\setminus F}\lVert\phi_e'\rVert_\infty^{h_F}$。取 $E=\mathcal A_{m,S,B}$、$F=S$，尾和 $\asymp m^{-2s_0}$，再用 CLU v1 命题 2.6 的 $\chi\ge2\ln\frac{1+\sqrt5}2$，立得 $\dim F_{m,S,B}-s_0\le K_2m^{-2s_0}$。对 $S=\{1,2\}$ 算出常数 71.90，大于论文数值 28.78，相容（§3(D)）。**下界**：DFSU 定理 4.1 在 $\bar c=0$ 情形的一阶项 $-\tilde\chi\theta+\eta_0$ 提示有渐近等价 $\theta\sim\eta_0/\tilde\chi$，比 $\Theta$ 更强；但该推导 DFSU 未写出，本核查也**未严格完成** | §2.1、§2.2、§3(D) |
| `rem:fourth-term`：$\frac{3\Gamma^3(\log m)^2}{4m^3}$ 第四项 | 猜想（不是结果；数值部分属 4 有限计算） | 系数代数：已核实（sympy）；猜想本身未证 | **结构先例**：标量模型 $\varepsilon m=\Gamma m^{-\varepsilon}$ 的主对数塔恰为 $\varepsilon=W(\Gamma L/m)/L$，系数 $(-n)^{n-1}\Gamma^n/(2\,n!)$，$n=3$ 时为 $\frac34\Gamma^3$。DFSU 式 (1.4) 对 $F_{\le N}$ **证明了** $c_{i,i-1}=-\frac{2^{i-1}i^{i-2}}{(i-1)!}(\frac6{\pi^2})^i$，与 $-\frac12\frac{i^{i-1}}{i!}(2c)^i$ 恒等（$i=1..7$ 已验证），即同一树函数系数，仅把 $2c$ 换成 $-\Gamma$。这有力支持该猜想的系数，也指出了一条可能的证明路线（DFSU 定理 4.1）；**但对等差族尚未证明** | §3(A)(B)(C) |

**类别注**：AGENTS.md 的五分类没有"已知结果的新证明 / 推论"这一类。本表把这类条目归入 5（文献核查与复现），并在"与已有文献关系"列写明其性质。所有 Lean 状态均沿用 README 记载（本次**未复跑** Lean）。

---

## 2. 原文核对记录

### 2.1 DFSU（关键先例，全文已读）
- **书目**：T. Das, L. Fishman, D. Simmons, M. Urbański, *Hausdorff dimensions of perturbations of a conformal iterated function system via thermodynamic formalism*, Selecta Math. (N.S.) **29** (2023), no. 2, Paper No. 19；DOI 10.1007/s00029-022-00820-z。Crossref 记录：卷 29、期 2、article-number 19、2023-01-23；arXiv:2007.10554v2 的 journal_ref 为 "Sel. Math. New Ser. 29, 19 (2023)"。页码范围**未核到**。
- **核对内容**（arXiv v2 TeX 源 `Dimension_asymptotics_2023_01_04.tex` + PDF 抽取文本；编号按 v2，**出版版编号未核到**）：
  - 摘要与引言：在原系统上添加或移除导数很小的生成元，用转移算子得到扰动后维数的级数或渐近展开；应用是加强 Hensley 1992 的 $\dim F_{\le N}$ 公式，以及 Good 1941 关于 $F_{\ge N}$ 的估计。
  - 式 (1.2) 转述 Hensley：$\dim F_{\le N}=1-\frac6{\pi^2}\frac1N-\frac{72}{\pi^4}\frac{\log N}{N^2}+O(N^{-2})$。
  - 定理 1.1 给出 $F_{\le N}$ 的任意阶展开；式 (1.4) 给出 $c_{i,i-1}$ 的封闭公式。
  - 定理 1.2 给出 $F_{\ge N}$ 的展开，含 $\log\log N/\log N$。
  - 定理 4.1（主定理）：固定 $S$，$\delta\ge\delta_S$ 且 $\delta>\Theta_S$，则存在 $\epsilon>0$，使得对一切正则的 $S'$，只要 $\sup_{b\in S\triangle S'}\lvert b\rvert\le\epsilon$ 且 $\lvert\theta\rvert\le\epsilon$，就有 $\Xi=\sum c_{I,j,k}\eta_I\theta^j\xi^k=0$，其中 $\eta_i=\sum_{S'}\lvert b\rvert^{q(\delta+\theta)}b^i-\sum_S(\cdots)$，$\xi=\eta_0-\bar c$，$\bar c=1/\sum_m\nu L_1^m h$。
  - 推论 4.2（解析参数化）；命题 9.3（多项式序列尾部，含 $\delta=\max(\delta_E,1/2d)$ 的说明）；命题 9.4（拟几何序列，含 Fibonacci）；例 9.5（$\{N,N+1\}$）；例 9.6（$\{1,N\}$）。
  - Gauss 情形：$u(b,x)=\frac b{1+bx}$，$v=-2\log(1+bx)$，$q=2$，$S(E)=\{1/n:n\in E\}$，几何 PF 算子 $Lf(x)=\sum_b\lvert b\rvert^{qs}e^{sv(b,x)}f(u_b(x))$。§9 开头的注记写明 $h\equiv1$。
- **与论文二的对应**（本核查自行推导，DFSU 未写出）：
  - 取 $S$ 为有限集、$S'=\mathcal A_{m,S,B}$。当 $s_0(S)<\frac12$ 时 $\delta=\frac12$，$\nu L_1^n\mathbf1=\sum_{w\in S^n}q(w)^{-1}$，所以 $1/\bar c=C_S$；$S=\emptyset$ 时 $\bar c=1$（DFSU 命题 9.4 的证明中写有 "If $E=\emptyset$ then $\bar c=1$"），对应 $C_\emptyset=1$。
  - 主阶 $\eta_0\approx d\,m^{-1-2\theta}\zeta(1+2\theta)\approx\frac d{2\theta m}=\bar c$，于是 $2\theta\approx dC_S/m$，与论文首项一致。
- **负核对**：DFSU 全文 grep `arithmetic|progression|congruen|residue|multiples|Poincar|Hurwitz` 只有一处无关命中（"residue $-r$" 指留数）。DFSU 没有处理等差数字集，也没有出现 $C_r$、$\psi_{\rm Fib}$ 或含 $\gamma$ 的系数。DFSU §10 开放问题列出的三例（co-Cantor、$x\mapsto(1+x^n)2^{-n}$、素数字母表）也不含等差族。

### 2.2 CLU（arXiv:1805.11904v1，TeX 源 + PDF 抽取文本；编号按 v1）
- 定理 2.3（引 [24] = Mauldin–Urbański 1996）：$h_{\mathcal S}=\dim_HJ_{\mathcal S}=\sup\{\dim J_F:F\text{ 有限}\}$；压力为 $P(t)=\lim\frac1n\ln Z_n(t)$，$Z_n$ 次可乘。
- 定理 2.4（引 [15] Heinemann–Urbański 与 [5] CLU 2018）：上表 (v) 行所述不等式，前提是"强正则"且 $h_F\ge\theta_{\mathcal S}$。
- 命题 2.6：$E\subset\{k,k+1,\dots\}$ ⇒ $\chi_E\ge2\ln\frac{k+\sqrt{k^2+4}}2$；其证明中有 $\lVert\phi'_\omega\rVert_\infty=\lvert\phi'_\omega(0)\rvert=q_n(\omega)^{-2}$。
- 正文写明：$1\in E$ 时失真常数 $K=4$。
- 文中多处 "$\theta_{CF_{E_{s,q}}}=1/2$, hence [25, Theorem 6.3] implies $[0,1/2)\subset DS$"，其中 [25] = MU 1999。这是 MU 1999 定理 6.3 的**转引**，MU 1999 原文**未核到**。
- 书目（Crossref）：CLU，Trans. Amer. Math. Soc. 373 (2020), no. 2, 1009–1042，DOI 10.1090/tran/7984（Crossref issued 2019-11-05，即在线日期）。与论文二条目一致，上一轮已核。
- 出版版定理编号**未核到**（AMS 页面有机器人验证，未绕过）。

### 2.3 Heinemann–Urbański 2002
- Crossref：S. Heinemann, M. Urbański, *Hausdorff dimension estimates for infinite conformal IFSs*, Nonlinearity **15** (2002), no. 3, 727–734，DOI 10.1088/0951-7715/15/3/312。与 CLU v1 书目一致。
- **原文未核到**（IOP 返回 500）。定理内容只采信 CLU v1 定理 2.4 的陈述，属**转引**。论文若引用，需对照原文确认定理号与常数形式。

### 2.4 经典来源
- **Good 1941**：Crossref 记录为 I. J. Good, *The fractional dimensional theory of continued fractions*, Mathematical Proceedings of the Cambridge Philosophical Society（当时刊名为 Proc. Cambridge Philos. Soc.）**37** (1941), no. 3, 199–228，DOI 10.1017/S030500410002171X。Cambridge Core 只取得摘要首段（研究部分商受简单限制的连分数集的维数）。原文内容**未核到**。DFSU 引言转述 Good 证明了 $N\ge20$ 时 $\frac12+\frac1{2\log(N+2)}\le\dim F_{\ge N}\le\frac12+\frac{\log\log(N-1)}{2\log(N-1)}$；Takahasi (arXiv:2111.02694) 引言转述 [Goo41, Theorem 1]：$\dim\{a_n\to\infty\}=\frac12$。两者均为**转引**。Crossref 另有 Good 1989 的补遗：J. Stat. Comput. Simul. 32 (1989) 64–68，DOI 10.1080/00949658908811155，未打开。
- **Hensley**：Crossref 记录有两条。*Continued fraction Cantor sets, Hausdorff dimension, and functional analysis*, J. Number Theory **40** (1992), no. 3, 336–358，DOI 10.1016/0022-314X(92)90006-B；*The Hausdorff dimensions of some continued fraction Cantor sets*, J. Number Theory **33** (1989), no. 2, 182–198，DOI 10.1016/0022-314X(89)90005-X。原文**未核到**（ScienceDirect 403）；公式只采信 DFSU 式 (1.2) 的转述。
- **Mauldin–Urbański**：1996 年文为 Proc. LMS (3) 73 (1996), no. 1, 105–154，DOI 10.1112/plms/s3-73.1.105；1999 年文为 Trans. AMS 351 (1999), no. 12, 4995–5025，DOI 10.1090/S0002-9947-99-02268-0。以上仅为 Crossref 元数据，原文**未核到**。CLU v1 书目把 MU 1999 的题名写成 "...applications to the geometry of conformal iterated function systems"，与 Crossref 题名 "...geometry of continued fractions" 不符，是 CLU 预印本书目的笔误，与论文二无关。
- **Jaerisch–Kesseböhmer**：Crossref 记录为 *The arithmetic-geometric scaling spectrum for continued fractions*, Ark. Mat. 48 (2010), no. 2, 335–360，DOI 10.1007/s11512-009-0102-8。DFSU 转述其结果为 $\dim F_{\ge N}-\frac12\sim\frac{\log\log N}{2\log N}$；Takahasi 转述为 [JaeKes10]。原文**未核到**。
- **Jenkinson–Pollicott 与 Falk–Nussbaum**（只做 Crossref 与 arXiv 源关键词 grep）：
  - JP：ETDS 21 (2001), no. 5, 1429–1445，DOI 10.1017/S0143385701001687；Adv. Math. 325 (2018), 87–115，DOI 10.1016/j.aim.2017.11.028（预印本 arXiv:1611.09276）。
  - FN：J. Fractal Geom. 5 (2018), no. 3, 279–337，DOI 10.4171/JFG/62（预印本 arXiv:1612.00870）。
  - JP 2018 与 FN 的预印本 TeX 中 grep 不到 arithmetic progression、congruence、asymptotic 等命中。二者是有限字母表的严格数值方法，与本文渐近结果**无重叠**，只是论文证书方法的同类先例。
- **DLMF §25.2**（https://dlmf.nist.gov/25.2，原页已读）：(25.2.4) 为 Laurent 展开，(25.2.5) 定义 Stieltjes 常数 $\gamma_n$，$n=0$ 时即为 Euler 常数。

### 2.5 其他命中（均已排除重叠）
- Chitanga–Lemmens–Nussbaum（arXiv:2504.20878v2；jref Indagationes Math. 2026，DOI 10.1016/j.indag.2026.03.008，据 arXiv 元数据，未经 Crossref 核对）：研究 $\{q^n\}$、$\{n^q\}$ 的维数谱，不涉及剩余类渐近。
- Takahasi 2111.02694：研究 $a_n\in B$、$a_n\le f(n)$ 且 $a_n\to\infty$ 时维数为 $\tau(B)/2$，对象不同。
- Nakajima–Takahasi–Wang 2601.12737：部分商序列中含长等差数列，对象不同。
- Tang 2510.24064：沿子序列 $a_{k_n}\to\infty$，对象不同。
- Rusu–Sebe 2604.00587：$\theta$-展开，对象不同。
- Hussain–Shulga 2309.00826 与 Nakajima–Takahasi 2502.10902：只看了标题，对象分别是部分商乘积和密度组合，不是剩余类数字集维数。
- Dawar–Priyadarshi 2606.26747（Fibonacci 数字的维数谱）与 Tryniecki–Urbański–Zdunik 2504.02135（Hausdorff **测度**渐近）：只看了标题与元数据。

---

## 3. 计算核查（`paper2_novelty_crosscheck_20261125.py` / `.log`，sympy 1.14.0、mpmath 1.3.0）

- **(A) Lambert-W 塔**：$\varepsilon=W(\Gamma L/m)/L$ 代回模型方程，到 $x^6$ 的残差为 0。$\dim-\frac12$ 中 $L^{n-1}/m^n$ 的系数依次为 $\frac\Gamma2,\ -\frac{\Gamma^2}2,\ \frac{3\Gamma^3}4,\ -\frac{4\Gamma^4}3,\ \frac{125\Gamma^5}{48}$。
- **(B) 与 DFSU (1.4) 对照**：DFSU 的 $c_{i,i-1}$ 与 $-\frac12\frac{i^{i-1}}{i!}(2c)^i$ 在 $i=1..7$ 全部相等；$72/\pi^4-2(6/\pi^2)^2=0$。剩余类族的塔等于把 $2c$ 换成 $-\Gamma$ 后的同一公式（$n=1..5$ 已断言）。
- **(C) `rem:fourth-term` 完整标量模型**：$\frac1m$、$\frac{\log m}{m^2}$、$\frac1{m^2}$ 三项系数复现论文；$(\log m)^2/m^3$ 项为 $\frac34\Gamma^3$；$\log m/m^3$ 项为 $-\frac32\Gamma^2(\gamma\Gamma-\Gamma')$（论文没有声称此项）。
- **(D) Heinemann–Urbański 上界**（$S=\{1,2\}$，$B=\emptyset$）：$K^{s_0}\cdot2\zeta(2s_0)/(2\ln\varphi)=71.9031618657$。论文报告的数值 $m^{2s_0}(\dim-s_0)\approx28.78$（$m=4096$）不超过该界，相容。这里的 $s_0$ 取论文的非严格数值 0.531280506，所以只是一致性检查，不是证明。

---

## 4. 【引用问题】

1. **【引用问题·归属】** 论文第 349–351 行写道 "infinite-alphabet thermodynamic-formalism dimension theory goes back to Hensley, Jenkinson--Pollicott, and Chousionis--Leykekhman--Urba\'nski \cite{CLU}"。按本次核对：
   - Hensley 1992（经 DFSU 转述）与 Jenkinson–Pollicott 2018（预印本 grep）处理的都是**有限**字母表；
   - 无穷字母表的维数理论，CLU v1 定理 2.3 归于 Mauldin–Urbański 1996；
   - Hensley 与 Jenkinson–Pollicott 两处只写了人名，**没有 `\cite`，书目中也没有条目**。
2. **【引用缺失】** 书目中没有 DFSU、Heinemann–Urbański 2002、Mauldin–Urbański 1996、Good 1941、Hensley 1992。前两者是 §1 中重叠程度最高的先例。
3. **【表述问题】** 摘要第 110 行与第 258 行把 "Bowen-free Poincaré-abscissa dimension $\dim_H E_S=s_0(S)$" 写成本文"确立"的结果，第 384 行也把整组 residue 定理列为 "main new contributions"。按 §1，(i) 是经典结果的新证明，(v) 上界与 (ii) 的超临界部分是已知定理的推论，需要降级表述。
4. 第 3466 行引 "\cite[\S2, Theorem~2.3]{CLU}" 作为 Bowen 公式的出处，与 CLU v1 的编号一致（上一轮也已指出 CLU 定理 2.3 需结合命题 2.2 读）。
5. **未发现**作者、卷、页、年份、DOI 的笔误：本次只核了 CLU 一条既有书目，与 Crossref 一致。

---

## 5. 建议措辞

> **已执行（2026-11-24，系统日期）**：
> - **补丁脚本**：`paper2_spectral_gap_dimension/patch_novelty_wording_20261125.py` 把 §5.4 段落、摘要 / 引言 / Lean 状态段 / 诚实声明中的措辞，以及 6 条书目写入主 tex、13 个核心切片和 `frontmatter.tex`、`intro-shared.tex`、`refs.tex`。2C 引言（`intro-2C.tex`）作同样改写。脚本断言修改前后切片拼接与主 tex 逐字节一致。
> - **README**：第 14、16 行按 §5.1 / §5.2 改写，并登记本记录。
> - **校验**：`verify_paper2_merge.py` 全部通过（书目 21/21 全引用）。tectonic 0.15.0 重编主文 64 页，0 未定义引用与文献；日志为 `paper2_build_tectonic_20261125.log`。2A / 2B / 2C 分别为 24 / 16 / 26 页，`undef_ref_audit.py` 三轨全零。S 补充轨的未定义标签全部是主文标签（设计如此），本次修改没有新增。
> - **构建注意**：本次构建在沙箱中运行，xdvipdfmx 打开字体 CMap 辅助文件（`*-GID`、`*-UCS32-Add`）时出现 "Operation not permitted" 警告。PDF 文本抽取正常，但建议作者在本机重编一次再投稿。另有 5 处 Overfull，都在未改动的 Lean 标识符段落，属 tectonic 与 pdflatex 的排版差异。
> - **不要重跑 `split/intro_trim_*.py`**：这些脚本按行号从 `intro-shared.tex` 生成各轨引言，本次修改改变了该文件的行数。
> - **§5.3**：README 中没有 `rem:fourth-term` 的专门条目，未执行。

### 5.1 README 第 14 行（`thm:residues-asymptotic`）
- **"类别"列**：由 "无条件新结果 + Lean 4 Layer A 机器验证" 改为
  > 无条件结果（已知一般扰动方法的显式实例：Das–Fishman–Simmons–Urbański, Selecta Math. 29 (2023) 定理 4.1）+ Lean 4 Layer A 机器验证（作者自报两机复建，本核查未复跑）
- **"与已有文献关系"列**：由 "…（经 arXiv 与既有连分数维数文献**负搜索**，未见…先例）" 改为
  > 大 $m$ 渐近属于 DFSU 定理 4.1（在有限系统上添加导数很小的生成元）的适用范围；该文没有处理等差数字集，也没有给出 $C_r$。首项常数 $C_r$ 即该框架中 $1/\bar c$ 在 $S=\{r\}$ 的取值；$\log m/m^2$ 系数与 Hensley 的 $72/\pi^4=2(6/\pi^2)^2$ 同构。**负搜索**（范围见 `verification/paper2_novelty_review_20261125.md` §0）未见以 $C_r$ 或 $\psi_{\rm Fib}$ 作为剩余类数字集维数渐近常数的先例，也未见全模 $m\ge2$ 严格分离的先例；负搜索不等于不存在。
- **它没做到什么**：没有给出不依赖大 $m$ 的显式误差常数之外的新方法；没有推进 $e+\pi$。

### 5.2 README 第 16 行（`thm:multi-residue-asymptotic`）
- **"类别"列**改为
  > 分项：(i)(iii) 经典结果（Bowen 公式的 Poincaré 级数形式、$\zeta$ 的 Laurent 展开）的自含证明与形式化；(ii) 超临界情形与 (v) 上界是 Heinemann–Urbański (2002) 估计的推论，$S=\emptyset$ 情形是 Good (1941) 的推论；(ii) 次临界 $S\ne\emptyset$、(iv) 三阶系数、(v) 下界是已知方法（DFSU 定理 4.1）的显式实例，属无条件结果 + Lean 4 Layer A 机器验证（作者自报，README 记载两机复建）
- **"与已有文献关系"列**中，把 "直接从…绕过 Bowen 压力公式导出…（经 arXiv/已有文献与 Mathlib v4.35 **负搜索**，未见先例）" 改为
  > (i) 有精确先例（Mauldin–Urbański 1996；见 CLU 定理 2.3）。(v) 上界有先例（Heinemann–Urbański 2002；见 CLU 定理 2.4，结合 CLU 命题 2.6）。整体渐近属于 DFSU 定理 4.1 的适用范围（DFSU 未处理等差族）。三阶系数 $\frac12d^2C_S(\gamma C_S-C_S')$：**负搜索**未见先例（范围见 20261125 记录）。

### 5.3 README 中 `rem:fourth-term` 的相关表述（若有）
建议补一句：
> 猜想系数 $\frac34\Gamma^3$ 是 Lambert-W 主对数塔的 $n=3$ 项；DFSU 式 (1.4) 对 $\{a_i\le N\}$ 证明了同一树函数系数族。这是结构旁证，不是证明。

### 5.4 论文 prior-work 段落（替换第 349–361 行，从 "For the modular continued-fraction alphabets" 到 "rate of Theorem~\ref{thm:multi-residue-asymptotic})."）

```latex
For the modular continued-fraction alphabets $F_{m,r}=\{[0;a_1,a_2,\dots]:a_n\equiv r\pmod m\}$,
the underlying infinite-alphabet dimension theory is that of Mauldin and
Urba\'nski \cite{MU96} (see \cite[Theorem~2.3]{CLU}), and Chousionis, Leykekhman
and Urba\'nski \cite{CLU} proved that every arithmetic-progression alphabet has
full dimension spectrum. Asymptotic expansions of the Hausdorff dimension when
generators with small derivative are added to or removed from a conformal IFS
were developed by Das, Fishman, Simmons and Urba\'nski \cite{DFSU}, who
strengthened Hensley's expansion \cite{Hensley92} for partial quotients $\le N$
and Good's estimates \cite{Good41} for partial quotients $\ge N$. The families
$F_{m,S,B}$ fall within the scope of their perturbation theorem
\cite[Theorem~4.1]{DFSU} (fixed finite $S$, added generators $\ge m-\max B$);
in their notation the leading constant is $1/\bar c=\sum_{n\ge0}\sum_{w\in S^n}q(w)^{-1}=C_S$
when $s_0(S)<1/2$. Arithmetic-progression alphabets are not treated in
\cite{DFSU}, and Theorems~\ref{thm:residues-asymptotic}
and~\ref{thm:multi-residue-asymptotic} make the first terms explicit for them;
the $\log m/m^2$ coefficient has the same structure as Hensley's
$72/\pi^4=2(6/\pi^2)^2$ (cf.\ \cite[(1.4)]{DFSU}). Part~(i) of
Theorem~\ref{thm:multi-residue-asymptotic} is the classical Bowen formula
written as the abscissa of a Poincar\'e series; our contribution there is a
proof that avoids the pressure formalism, together with its formalization.
The upper bound in part~(v), and hence the supercritical case of part~(ii),
follow from the Heinemann--Urba\'nski estimate \cite{HU02} (in the form of
\cite[Theorem~2.4]{CLU}) combined with the Lyapunov bound
\cite[Proposition~2.6]{CLU}, and the case $S=\emptyset$ of part~(ii) follows
from Good's theorem by monotonicity. Part~(iii) is a quantitative form of the
Laurent expansion of $\zeta$ at $1$ \cite[(25.2.4)]{DLMF}. A targeted negative
search (arXiv, Crossref and web search; coverage recorded in the verification
archive) found no prior appearance of $C_r$, of $\psi_{\mathrm{Fib}}$, or of the
coefficient $\frac12 d^2C_S(\gamma C_S-C_S')$ as asymptotic dimension constants
of residue-class digit sets; this does not exclude such an appearance.
```

同时建议做以下改动：
- 第 384 行 "main new contributions" 中把 `thm:multi-residue-asymptotic` 改为 "explicit residue-class instances of known asymptotic methods (Theorems~\ref{thm:residues-asymptotic}--\ref{thm:multi-residue-asymptotic})"。
- 摘要第 110 行 "establishes the Bowen-free Poincaré-abscissa dimension $\dimH E_S=s_0(S)$" 改为 "gives a self-contained, Bowen-free proof of the classical identity $\dimH E_S=s_0(S)$"。
- 第 4330 行附近的表述作同样调整。

**待补书目**（字段均来自 Crossref；**页码 / 定理号以出版版为准，投稿前需对照**）：
- `DFSU`：T. Das, L. Fishman, D. Simmons, M. Urbański, Selecta Math. (N.S.) 29 (2023), no. 2, Paper No. 19, doi:10.1007/s00029-022-00820-z（arXiv:2007.10554）。**引用的定理 4.1、式 (1.4) 为 arXiv v2 编号，出版版编号未核到。**
- `HU02`：S. Heinemann, M. Urbański, Nonlinearity 15 (2002), no. 3, 727–734, doi:10.1088/0951-7715/15/3/312。**原文未核到。**
- `MU96`：R. D. Mauldin, M. Urbański, Proc. London Math. Soc. (3) 73 (1996), no. 1, 105–154, doi:10.1112/plms/s3-73.1.105。
- `Good41`：I. J. Good, Proc. Cambridge Philos. Soc. 37 (1941), no. 3, 199–228, doi:10.1017/S030500410002171X。
- `Hensley92`：D. Hensley, J. Number Theory 40 (1992), no. 3, 336–358, doi:10.1016/0022-314X(92)90006-B。
- `DLMF`：NIST Digital Library of Mathematical Functions, §25.2。版本号与访问日期**未记录**，投稿前补。

**需要作者确认**：
1. 在 DFSU 定理 4.1 下，"$\lvert\theta\rvert\le\epsilon$" 需要事先知道 $\delta_{S'}\to\delta$。论文的 (ii) 恰好提供这一点，不构成循环，但改写时应写清楚。
2. 若要声称 (v) 可加强为渐近等价，需要另作严格推导；本核查只提示了这一可能。

---

## 6. 检索式（2026-11-24）

**arXiv API**（`abs:` 字段）：
1. "continued fraction" AND "arithmetic progression" AND dimension
2. "continued fraction" AND "residue class" AND dimension（0 命中）
3. "partial quotients" AND congruen* AND "Hausdorff dimension"（0 命中）
4. "continued fraction" AND "dimension spectrum"
5. "continued fraction" AND Hausdorff AND asymptotic AND "tends to 1/2"（0 命中）
6. Hensley AND "continued fraction" AND dimension
7. "continued fraction" AND "Hausdorff dimension" AND "large partial quotients"
8. "continued fraction" AND "Hausdorff dimension" AND "asymptotic expansion"（唯一命中：DFSU）
9. "conformal iterated function system" AND perturbation AND "Hausdorff dimension" AND asymptotic（唯一命中：DFSU）
10. "continued fraction" AND "Hausdorff dimension" AND Euler AND constant（0 命中）
11. "continued fraction" AND "even partial quotients" AND dimension（0 命中）
12. Good AND "partial quotients" AND "tend to infinity" AND dimension
13. "finiteness parameter" AND "continued fraction"（无相关命中）
14. "continued fraction" AND "Hausdorff dimension" AND multiples

另有 "...subsystem AND asymptotic" 与 "...divisible" 两式因 HTTP 429 限流**未执行**。

**WebSearch**：
- （扩展）Hausdorff dimension continued fractions partial quotients in arithmetic progression asymptotic as common difference tends to infinity
- continued fraction Cantor set digits divisible by m Hausdorff dimension 1/2 + 1/(2m) Euler constant
- Hausdorff dimension continued fractions with partial quotients congruent to r modulo m

三次均未找到等差 / 剩余类数字集维数随模数渐近的文献。

**Crossref**：§2 所列 11 条书目查询。

---

## 7. 本核查没做到什么
- 没有打开 Good 1941、Hensley 1989 / 1992、MU 1996 / 1999、HU 2002、Jaerisch–Kesseböhmer 2010 的原文，相关内容均为转引。
- 没有查 zbMATH / MathSciNet 的引用链，尤其是"引用 DFSU 的后续文献"。这是最可能藏有等差族显式结果的地方，**投稿前强烈建议补查**。
- 没有严格推导"DFSU 定理 4.1 ⇒ 论文 (iii)(iv) 的显式系数"，只核对了首项常数的对应。
- 没有复跑 Lean。
- 负搜索不等于不存在先例。
