<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# R6-S2 / R6-S7 先例核查（新颖性检查）

> **LOG-ONLY / NON-CANONICAL / DO NOT CITE.** 本文件是撰写 R6-S2 论文前的检索记录，不是论文正文，任何字段都不得直接抄入书目。
> 日期：2026-11-28。执行者：总控派发的子智能体（general-purpose，按 AGENTS.md §3 与 `.claude/skills/novelty-check/SKILL.md` 执行）。
> 本文件只做文献对照，**不审数学**；R6-S2、R6-S7 的正确性以 PLAN_GRAPH.md 中的审计与形式化记录为准。
> **与 $e+\pi$ 无关**：下列一切结果都不涉及 $e+\pi$ 的有理性或无理性。

**总判断（一句）**：在本会话检索范围内，没有发现一般块词 $W$ 下 $c^*(\alpha)=\nu(W)$ 的先例（这只是负搜索）；但内部稿件已覆盖 $W=\varnothing$ 与 $W=(1,1)$ 两类特例，论文必须把这两类写成已有结果的特例或复现，不能说成新结果。

---

## 0. 待查结果（取自 PLAN_GRAPH.md §S.1、§S.2 与节点表 R6-S1/S2/S7）

- **R6-S2**：$\alpha=[a_0;a_1,\dots,a_N,A_1,W,A_2,W,\dots]$，$A_k\to\infty$，$W$ 是固定的有限词；$\theta_n=q_n|q_n\alpha-p_n|$；$\mathcal K_\alpha(\beta)=\limsup_n\|q_n\beta\|/\theta_n$；$c^*(\alpha)=\inf_{\beta\notin\mathbb Z\alpha+\mathbb Z}\mathcal K_\alpha(\beta)$。结论：$c^*(\alpha)=\nu(W)$（有限图 $G_W$ 上的极小极大值），且下确界可达。
- **R6-S7**：对一切 $W$，$K(W)\ge2$ 时 $m^*:=\min_{r\ne0}v(r)\ge1/2$，因此 $\nu(W)=\min(1,m^*)$；$K=1$ 时 $\nu=1$。合起来，对一切 $W$ 有 $\nu(W)\ge1/2$。
- **R6-S3 数据**：存在 $W$ 使 $\nu(W)<1$，例如 $\nu(5,1,5)=5/6$。这个值来自 PLAN_GRAPH.md L271“由代码确认”，代码在 `experiments/R6-S2/`。本文件**没有重算**。
- **R6-S1**：局部化引理，是 S2 证明的一部分。

**形式化口径（AGENTS.md §5）**：下文所有内部论文（Paper 2、2E、2D、THM-0005、THM-0006）中的 Lean 结果都是**作者自报，本会话未复跑**。R6-S1/S2/S7 的 Lean 状态以 PLAN_GRAPH.md 记录为准（CI 46110437346），本会话同样没有复跑。

---

## (a) 内部先例对照表

行号指本 worktree 中文件的当前行号（2026-11-28）。

### a.1 Paper 2：`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`

| 定理（行号） | 陈述要点（本会话实际阅读） | 与 R6-S2/S7 的关系 | 说明 |
|---|---|---|---|
| **thm:growing-rec-spectrum**（L2624–2668；证明 L2670–2705 前后） | 对递推 $Q_{j+1}=A_jQ_j+Q_{j-1}$（$A_j\in\mathbb Z_{\ge2}$，$A_j\to\infty$）：(i) $\Lambda_G^{\rm KL}(x)=\limsup\|Q_jx\|/(\tilde Q_j|\tilde Q_j\theta-\tilde P_j|)=\Lambda_G(x)=\limsup A_j\|Q_jx\|$，并且 $\Lambda_G<1\iff x\in L_G$；(ii) $\Lambda_G(\mathbb R)=\mathbb Z_{\ge0}\cup\{\infty\}$；(iii) 临界 gauge 与三分法 | **特例（$W=\varnothing$）**。若 $Q_j$ 取 $\alpha=[a_0;\dots,a_N,A_1,A_2,\dots]$ 的收敛分母，那么 KL 比值沿**全部**收敛分母取值于 $\mathbb Z_{\ge0}\cup\{\infty\}$，零水平集为 $\mathbb Z\alpha+\mathbb Z$。由此 $c^*(\alpha)=1$ 且可达（常数缺陷 $d_j=1$）。这正是 $\nu(\varnothing)=1$ 的情形 | 对账要点有两处，论文中需各写一句：(1) Paper 2 用 $\tilde P_j$（$\tilde P_{J_0-1}=0,\tilde P_{J_0}=1$）定义的 $\theta$，一般是 $\alpha$ 的 Möbius 像，不就是 $\alpha$；但两者归一化都满足 $A_j\cdot(\cdot)\to1$，所以 KL 极限相同。(2) Paper 2 要求 $A_j\ge2$（$j\ge J_0$），$A_k\to\infty$ 时最终成立。Paper 2 只处理 $W=\varnothing$，没有块内指标 |
| thm:full-spectrum（L581–600） | 沿 $e$ 的选取分母 $Q_j$，$\Lambda(x)=\limsup j\|Q_jx\|$ 的谱为 $\frac14\mathbb Z_{\ge0}\cup\{\infty\}$ | **间接特例（$W=\varnothing$，$\alpha=(e+1)/2$ 或 $(e-1)/2$）**。Paper 2 L330–341 自己指出：$Q_j$ 是 $(e+1)/2=[1;1,6,10,14,\dots]$ 的收敛分母，并且 $jQ_j|Q_j\beta-R_j|\to1/4$。因此 KL 比值 $=4\Lambda$，其谱为 $\mathbb Z_{\ge0}\cup\{\infty\}$，$c^*=1$ | 只涉及单个 α |
| thm:class / thm:gap（L514–530） | $\{\Lambda=0\}=L$；$x\notin L\Rightarrow\Lambda\ge1/4$ | 与上一行同一特例的下界部分 | — |
| **thm:trichotomy**（L1717–1768） | 在正水平 $k/4$ 上：limsup 水平、无符号精确极限、有符号精确极限三分；gauge 底数分别为 $2k+1$ 与 2 | **无关**（研究对象是水平集的大小、gauge 与可数性，不是尖锐常数）。只有 $k=1$ 的“可达”一项与上面的特例相同 | — |
| thm:finite-state-tail（L1898–1906） | 有限状态缺陷图上的尾集：由标记分量的 Perron 根决定 gauge | **无关但形式相近**：它也是“有限图 + 闭路”，但问的是计数/测度（Perron 根），不是极小极大代价。$G_W$ 上的 $\nu(W)$ 是瓶颈（min–max）路径量，不是谱半径 | 论文中可以说一句“形式上相近，问题不同” |
| thm:general-rec、thm:poly-gauge-trichotomy、thm:poly-phase-transition（L2191–2410） | 多项式递推 $Q_{j+1}=(cj^r+d)Q_j+Q_{j-1}$ 的谱 $\frac1c\mathbb Z_{\ge0}\cup\{\infty\}$ 等 | 沿**选取**子列，以 $j^r$ 为权；不是沿全部收敛分母的 KL 常数。只有 $W=\varnothing$ 时才与 R6-S2 交叠，已被 thm:growing-rec-spectrum 包含 | — |
| §1.2 Relation to prior work（L296–341） | 引 KL 1991 与 BDS Lemma 4.1，比较两种归一化 | 是 R6-S2 论文“已知下界 1/4”一节的内部前文 | 书目见 (b) |

**结论 a.1**：Paper 2 已经覆盖 $W=\varnothing$ 的 $c^*=1$（且可达），而且结论更强（全谱）。**Paper 2 中没有块内指标，没有 $K(W)$、$v(r)$、$\nu(W)$ 或类似的量。**

### a.2 Paper 2E：`.../spinoff_full_convergent_and_even_hurwitz_20261125/paper2E_full_convergent_and_even_hurwitz.tex`

| 定理（行号） | 陈述要点（本会话实际阅读） | 与 R6-S2/S7 的关系 | 说明 |
|---|---|---|---|
| thm:full-identities（L160–181） | $e$ 的全收敛分母与选取分母的恒等式；KL 权重极限 $w_{3j+1}/(2(j+1))\to1$，$w_{3j+2}\to2$，$w_{3j+3}\to2$ | **R6-S1(a) 在 $W=(1,1)$ 时的特例**。S1(a) 给出 $1/\theta_{n_k+i}\to K/(c_ic_i')$；$W=(1,1)$ 时 $K=2$，$c_1c_1'=c_2c_2'=1$，所以极限为 2，与 2E 一致 | 只涉及 $\alpha=e$ |
| **thm:full-spectra**（L246–287） | $\Lambda^{\rm KL}_{\rm full}(x)=\max(2\Lambda(x),\mathbf 1_{\rm pf(x)})$；值域 $\{0\}\cup\{k/2:k\ge2\}\cup\{\infty\}$；初始谱隙 $(0,1)$；$\{\Lambda^{\rm KL}_{\rm full}<1\}=\mathbb Z+\mathbb Ze$；$L_1\subset\{\Lambda^{\rm KL}_{\rm full}=1\}$ | **特例（$W=(1,1)$，$\alpha=e$），而且结论更强**。$\Lambda^{\rm KL}_{\rm full}$ 就是 $\mathcal K_e$（$w_n=1/\theta_n$）。(ii)(iii) 推出 $c^*(e)=1$，(iv) 推出可达（例如 $\beta\in L_1$）。这正是 $\nu((1,1))=1$。2E 还给出全谱、水平集与 gauge，R6-S2 没有给出这些 | “奇偶翻转” $\mathbf 1_{\rm pf}$ 就是 $K=2$ 时的块内顶点代价（$r_k\ne0$，即 $r=1\in\mathbb Z/2$）。R6-S2 把 2E 的奇偶机制推广为 $\mathbb Z/K$ 上的标签与 $G_W$ 上的闭路 |
| thm:full-exact-lim（L321–337） | $\lim w_n\|q_nx\|=c$ 只可能 $c\in\{0,1\}$ | **无关**（精确极限集，R6-S2 不研究） | — |
| **thm:even-hurwitz**（L366–383，**重点**） | Hurwitz 连分数，准周期 $p$，第 $j$ 块是一个仿射商 $a_j=cj+d$ 后接 $p-1$ 个常数 $c_1,\dots,c_{p-1}$。令 $C=\prod\begin{pmatrix}c_i&1\\1&0\end{pmatrix}=\begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix}$，则块边界分母满足 $Q_{j+1}=(\alpha a_j+\beta+\gamma)Q_j+(-1)^{p-1}Q_{j-1}$ | **无关（只是一个递推恒等式），不覆盖 $c^*$**。逐项判断：(1) 它只给出块边界分母 $Q_j$ 的三项递推，**没有任何 KL 比值、$\|q_n\beta\|$、谱、下界或常数**。(2) 它的 $p-1$ 个常数商就是块词 $W$（$\ell=p-1$），矩阵元 $\alpha=K(W)$。这只是 R6-S1/S2 证明里使用的标准连续子矩阵恒等式，与 S.1 的连续子记号重合。(3) 它要求 $a_j$ 为仿射函数，R6-S2 允许任意 $A_k\to\infty$。(4) 即使把它与 Paper 2 thm:growing-rec-spectrum 合用（只在 $p$ 为奇数、符号为 + 时可行；2E L362–365 与 Paper 2 L4445 都说 Lean 中 GeneralGrowingRec 写死了 +），得到的也只是沿**块边界子列**、以 $\alpha a_j+\beta+\gamma\approx K A_k$ 为权的谱；零水平格是 $L_G$（一般比 $\mathbb Z\alpha+\mathbb Z$ 大），块内指标完全不处理。$c^*=\nu(W)$ 恰恰由块内顶点代价 $v(r)$ 与块间边约束决定。**结论：2E 没有覆盖任意块词 $W$ 的 $c^*(\alpha)$，也没有与 $\nu(W)$ 类似的量** | 2E L493–515 写明 thm:even-hurwitz “proved analytically”，**不在 Lean 中** |
| thm:finite-state-unconditional（L429–449） | 无 Brouwer 的 Perron–Frobenius；无条件的有限状态尾定理 | **无关**（与 Paper 2 thm:finite-state-tail 同类：研究 Perron 根，不研究极小极大） | — |
| 引言与“Honest scope”（L81–131） | 2E 把 $(0,1)$ 谱隙等称为“targeted negative search 下新”；把零水平刻画称为 KL 在 $\alpha=e$ 的特化 | R6-S2 论文必须说明：$W=(1,1)$ 情形的 $c^*=1$ 已见于 2E | — |

**结论 a.2**：2E 覆盖了 $W=(1,1)$（仅 $\alpha=e$，$A_k=2k$，$N=1$）的 $c^*=1$ 与可达性，并且结论比 R6-S2 在该情形更强。thm:even-hurwitz 只是递推恒等式，**不含任何常数结论**。2E 中与 $\nu(W)$ 最接近的是奇偶翻转指示 $\mathbf 1_{\rm pf}$，即 $K=2$ 时唯一非零标签的代价；2E 没有一般 $K$ 的标签图与极小极大量。

### a.3 Paper 2D：`.../spinoff_critical_and_supercritical_exact_20261125/paper2D_critical_supercritical_exact.tex`

| 内容（行号） | 关系 |
|---|---|
| thm:supercritical-exact（L772）、thm:critical-scaling（L862）、cor:critical-exp（L937）、prop:sparse-tail-phase（L1006） | **无关**。对象是剩余类字母表连分数集合 $F_{m,S,B}$ 的 Hausdorff 维数渐近与转移算子。文中出现的“Hurwitz”指 Hurwitz ζ 函数（L619、L1122），与 Hurwitz 连分数无关。grep 全文：没有 Kraaikamp、Liardet、块词或 KL 比值 |

### a.4 THM-0005 与 THM-0006（`artifacts/`）

| 结果（行号） | 陈述要点 | 关系 |
|---|---|---|
| **THM-0005**，`paper_draft.tex` thm:main（L88–97）、thm:sharp（L241–244） | $Q_0=Q_1=1$，$Q_{j+1}=(4j+2)Q_j+Q_{j-1}$；$\kappa=\inf_{z\notin L}\limsup j\|Q_jz\|=1/4$，并且可达 | **特例（$W=\varnothing$，$\alpha=(e-1)/2=[0;1,6,10,\dots]$）**。prop:input（L301 起）证明 $Q_j$ 是 $(e-1)/2$ 的收敛分母；比较附注（L99–113）给出 $\theta_j(4j+2)\to1$，所以 KL 比值 $\sim4j\|Q_jz\|$，$c^*((e-1)/2)=4\kappa=1$，且可达。这是 $\nu(\varnothing)=1$ 的单个实例，已被 Paper 2 thm:growing-rec-spectrum 包含。草稿 L44–45 与 L446–451 自称“负搜索下新”的只是 $\kappa=1/4$ 这一归一化下的数值 |
| THM-0005 scope（L435–451） | “threshold 1 … not shown to be sharp in general”；负搜索覆盖范围：KL、Larcher、BDS 全文；Stewart 未读 | R6-S2 论文的外部检索可以接续这份覆盖记录（见 (c)） |
| **THM-0006**，`paper_draft.tex` prop:dich（L131–142）；`statement.md` | 条件 (H)：$a_j\to\infty$，$D\ne0$；$z\notin L_D\Rightarrow\limsup a_j\|Q_jz\|\ge1$ | **特例的下界部分（$W=\varnothing$）**。$D=\pm1$ 且 $Q_j$ 为收敛分母时，结合 $a_j\theta_j\to1$ 可得 $c^*\ge1$。它不涉及块词，也不给出可达性（L204–207 明说一般情形的尖锐性未证；Paper 2 thm:growing-rec-spectrum 后来给出了） |

### a.5 其他本地检索（只是负搜索）

- grep 范围：`papers/`、`paper1_e_plus_pi/`、`paper2_spectral_gap_dimension/`（含 2D、2E）、`registry/`、`research/`、`verification/`、`epi_formal/EpiFormal/`。检索词：`even.hurwitz|signed hurwitz|quasi-period|block word|komatsu`。另外列出了 `epi_formal/EpiFormal` 中名称含 Hurwitz/Block/Growing/FullConv/Signed 的模块。
- 命中都属于下列几类：上面已列的 Paper 2/2E；Paper 1 对 Komatsu 系列的引用（`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex` L806–816，bibitem L3975–3982）；本项目自己的 `R6S2*.lean` 与 `R6S7Mstar.lean`。
- `registry/results.csv` 只有 THM-0003/0005/0006 三条相关记录（见 a.4）。
- **本地没有发现一般块词 $W$ 的 $c^*$ 或 $\nu(W)$ 型量的先例。**

---

## (b) 外部检索记录（2026-11-28）

规则：只记录**本会话实际打开的页面**上核对到的字段；其余一律写“未核到”。付费墙没有绕过。

### b.1 实际打开过的来源

| # | 来源（实际打开的页面） | 核对到的字段 | 未核到 | 与本结果的关系 |
|---|---|---|---|---|
| 1 | Crossref API `api.crossref.org/works/10.1090/S0002-9939-1991-1062392-7`；OpenAlex `W2010916804` | 作者 Cor Kraaikamp, Pierre Liardet；题名 *Good approximations and continued fractions*；Proc. Amer. Math. Soc. **112**，no. 2，303–309，1991；DOI 10.1090/s0002-9939-1991-1062392-7；OpenAlex 被引 38（列表返回 39 条） | **全文本会话未打开**（AMS 页面返回 HTTP 403）。Theorem 1/1′ 的确切陈述与常数 1/4，本会话只能依据内部转述（THM-0005 paper_draft L60–70 自称读过全文），本会话**未核到** | R6-S2 的下界 $\nu\ge1/4$ 校准与“KL 常数”术语都来自这篇。被引列表（39 条）**逐条看了题名**：绝大多数属于 characterized subgroups / 拓扑群方向（Dikranjan、Das–Ghosh、Gabriyelyan 等）；其余为遍历论（Aaronson 2002、Bergelson–del Junco–Lemańczyk–Rosenblatt 2013、Brémont–Buczolich 2012）以及 BDS 2001、Biró–Sós 2003、Burger 2000。按题名与可得摘要判断，**都不涉及沿收敛分母的尖锐 KL 常数，也不涉及 Hurwitz 或块结构**。其中 5 条在 OpenAlex 中没有摘要，只看了题名（见 c） |
| 2 | real.mtak.hu/110616/ 记录页 | 作者 András Biró, J-M. Deshouillers, Vera T. Sós；题名 *Good approximation and characterization of subgroups of R/Z*；Studia Sci. Math. Hungar. **38**（1-4），97–113，2001；DOI 10.1556/SScMath.38.2001.1-4.7 | 全文 PDF 已取得，但它是扫描件，本会话无法抽取正文。**Lemma 4.1 的陈述与页码本会话未核到**（Paper 2 L308 写 Lemma 4.1，L334 写 p.106，均为内部转述） | 引用 KL 的二手来源 |
| 3 | jtnb.centre-mersenne.org 文章页 `10.5802/jtnb.254`；numdam.org `JTNB_1999__11_2_331_0`；PDF 文本层（部分） | 作者 Takao Komatsu；题名 *On inhomogeneous diophantine approximation with some quasi-periodic expressions, II*；J. Théor. Nombres Bordeaux **11**，no. 2，331–344，1999；DOI 10.5802/jtnb.254；MR1745883；Zbl 1058.11049。研究的量：$\mathcal M(\theta,\phi)=\liminf_{|q|\to\infty}|q|\,\|q\theta-\phi\|$，θ 是拟周期（Hurwitzian）连分数（摘要页）。文本层可见：§2 介绍 NST（Nishioka–Shiokawa–Tamura）算法；§3 讨论“每个拟周期中没有常数”的情形；正文有 Theorem 1–9；文中提到早先的 [7] 给出 $\mathcal M(e^{1/s},\cdot)$ 的具体值。参考文献 11 条，其中**没有 Kraaikamp–Liardet，也没有 Stewart** | **各定理的公式本会话未核到**（文本层缺失数学字体）。Paper 1 bibitem 中的 doi、期号与本会话所见一致 | **不同的泛函**。Komatsu 研究的是“用 $q\theta$ 逼近平移 $\phi$”的非齐次常数，取 liminf，对象是**全部** $q$。R6-S2 研究的是“$q_n\beta$ 到整数的距离”，只沿 α 的收敛分母，取 limsup，并按 $\theta_n$ 归一化。两者都把 $\phi$ 或 β 取在 $\mathbb Q(\theta)+\mathbb Q$ 中、都依赖收敛分子分母模 $K$ 的剩余类，**方法上相近**；但本会话**没有找到、也没有证明**两种常数之间的等价或换算。论文必须讨论这一族文献，且不得说两者无关 |
| 4 | Crossref bibliographic 查询（Komatsu + quasi-periodic） | (i) T. Komatsu, *On Inhomogeneous Diophantine Approximation with Some Quasi-Periodic Expressions*, Acta Math. Hungar. **85**，311–330，1999，DOI 10.1023/a:1006707704660；(ii) T. Komatsu, J. Number Theory **62**，192–212，1997，DOI 10.1006/jnth.1997.2060；(iii) T. Komatsu, Acta Arith. **86**，305–324，1998，DOI 10.4064/aa-86-4-305-324；(iv) *Inhomogeneous Diophantine approximation of some Hurwitzian numbers*, AIP Conf. Proc. **976**，31–42，2008，DOI 10.1063/1.2841909（Crossref 列出的作者为 Bumby, Flahive, Komatsu） | 以上各篇**全文与定理均未核到** | 同第 3 条：都是 liminf 型非齐次常数 |
| 5 | arXiv:0710.0399 摘要页 | 题名 *Inhomogeneous Diophantine approximation of some Hurwitzian numbers*；arXiv 页面列出作者 Richard T. Bumby, Mary E. Flahive；2007-10-01 提交；MSC 11J70, 11J06, 11H50；相关 DOI 10.1063/1.2841909。摘要说：研究 Hurwitzian θ、$\phi\in\mathbb Q(\theta)+\mathbb Q$ 的非齐次常数 $L(\theta,\phi)$，刻画 $L=0$，讨论 $n^2L(e^{2/s},\phi)$ 的小值，证明 Komatsu 的一个猜想 | $L$ 的定义不在摘要中（搜索摘要片段称其为对全部 q 的 liminf，**未核到原文**）；作者名单与 Crossref 不一致（arXiv 2 人，Crossref 3 人），**未核清** | 同第 3 条 |
| 6 | Crossref `10.1007/BF01904883` | M. Stewart，*Irregularities of uniform distribution*，Acta Math. Acad. Sci. Hungar. **37**（1-3），185–221，1981；DOI 10.1007/bf01904883 | **全文未核到**（Springer 页面跳转到登录，未绕过）；作者全名未核到。THM-0005 bibitem 记有“另一来源页码不同，未解决”，本会话也未解决 | 据 KL 的转述（内部，未核到），Stewart 讨论的是有界型情形，与 $A_k\to\infty$ 的块 Hurwitz 类不重叠；但这一点**未核到** |
| 7 | arXiv:1508.00520 摘要页 | Dong Han Kim, Lingmin Liao，*Dirichlet uniformly well-approximated numbers*；v1 2015-08-03，v2 2017-08-21 | 期刊信息未核到（页面上没有） | **无关**：研究的是一致型非齐次条件 $\|n\theta-y\|<Q^{-\tau}$ 的 Hausdorff 维数，不是沿收敛分母的 KL 常数 |
| 8 | arXiv:2609.36412 摘要页 | Taehyeong Kim, Vasiliy Neckrasov，*Twisted Diophantine Approximation II: Uniform Theory*，2026-09-29 | 正文未读 | **无关**（twisted / 一致型维数理论；摘要中没有 KL 比值、Hurwitz 或尖锐常数） |
| 9 | arXiv API：`abs:"convergent denominators" AND abs:inhomogeneous` | 唯一命中 arXiv:2106.10712，A. Bourla，*Ostrowski Numeration, Alternating Expansions and Inhomogeneous Linear Approximation* | 正文未读 | 研究 $\|m\alpha-\beta\|$ 的单侧最优逼近，是 Ostrowski 型方法；摘要中没有沿 $q_n$ 的 KL 尖锐常数。**可能相关，但未核到** |
| 10 | arXiv API：`abs:"Kraaikamp" AND abs:"Liardet"` | 0 条 | — | 负搜索 |
| 11 | arXiv API：`abs:"characterized subgroup" AND abs:"continued fraction"` | 1 条：arXiv:2011.03786，P. Das 等，*Statistically characterized subgroups of the circle (II): continued fractions* | 正文未读 | 摘要中没有尖锐常数 |
| 12 | OpenAlex：Brémont–Buczolich，ETDS **33**（1），24–48（OpenAlex 记录的年份为 2012），DOI 10.1017/s0143385711000903；Bergelson–del Junco–Lemańczyk–Rosenblatt，ETDS 2013，DOI 10.1017/etds.2013.5 | 摘要 | — | 无关（遍历论） |

### b.2 Web 搜索查询词（WebSearch；只用来定位，结论以 b.1 为准）

1. `Kraaikamp Liardet "good approximations and continued fractions" constant 1/4 sharp`：命中 Kraaikamp–Smeets 等关于 Legendre / Borel 常数的论文，无关。
2. `"\|q_n \beta\|" convergent denominators inhomogeneous "Kraaikamp" "Liardet" best constant`：命中 Paudel–Pinner（arXiv:2301.12270）、Pinner（arXiv:1603.06178）关于非齐次逼近常数 $\rho(\alpha)$（Minkowski 型 $\le1/4$）的工作。那是对平移取最坏情形的 liminf 常数，**不同泛函**；未打开正文。
3. `Kim Liao inhomogeneous approximation along convergent denominators ...`：得到 b.1 第 7、8 条；另有 Kim–Rams–Wang（arXiv:1609.08724）、Bugeaud–Kim–Lim–Rams（arXiv:1805.10436），均为维数理论，未打开。
4. `M. Stewart "Irregularities of uniform distribution" ... 1981`：得到 b.1 第 6 条。
5. `"Hurwitz continued fraction" OR "quasi-periodic continued fraction" "\|q_n x\|" characterized subgroup sharp constant`：命中的都是复 Hurwitz 连分数，无关。
6. `limsup "\|q_n\beta\|" ... Kraaikamp Liardet theorem generalization arXiv`（extended）：没有相关命中。
7. `"Kraaikamp and Liardet" "1/4" best possible OR sharp OR optimal ...`（extended）：命中 ResearchGate 上的 KL 题录（未打开）以及 characterized-subgroup 论文中对 KL 的转述。**没有任何来源讨论 1/4 是否最优。**
8. `Ostrowski expansion "q_n \beta" ... limsup ... quantitative constant`：命中 Beresnevich–Haynes–Velani（arXiv:1511.06862）等，无关或未打开。
9. `"Hurwitzian" numbers "q_n" "nearest integer" ... limsup constant depends on period block`：得到 b.1 第 5 条，以及 Hartono–Kraaikamp（Tokyo J. Math. 2002，NICF 意义下的 Hurwitzian 数，未打开）。

---

## (c) 负搜索覆盖范围与未能获取的文献

**覆盖范围（全部是负搜索）**
- 内部：(a) 所列全部文件，以及 a.5 的 grep 范围。
- 外部：
  - WebSearch：b.2 的 9 组查询（含 2 次 extended）。
  - arXiv API：摘要字段的 3 组布尔查询。
  - Crossref：DOI 查询 2 次，题录查询 1 次。
  - OpenAlex：KL 1991 的**完整被引列表**（39 条，逐条看题名），以及其中 7 条的摘要查询。
  - JTNB 与 numdam 文章页；Komatsu 1999 PDF 的部分文本层。
- 时间：检索于 2026-11-28；OpenAlex 与 arXiv 数据截至当日。

**没有覆盖到 / 未能获取**
- **KL 1991 全文**：AMS 返回 403。本会话没有核对 Theorem 1/1′ 的原文；“1/4”的表述目前只来自内部稿件的转述。
- **Stewart 1981 全文**：Springer 需要登录，未绕过。页码分歧未解决。
- **Komatsu 1999 JTNB 的定理公式**：PDF 可取得，但本环境没有 PDF 渲染与 OCR 工具（没有 pdftotext、pdftoppm、pypdf），只读到部分文本层，公式缺失。Komatsu Acta Math. Hungar. 85（1999）、Acta Arith. 86（1998）、JNT 62（1997）、JNT 129（2009）、Monatsh. 145（2005），以及 Bumby–Flahive（–Komatsu）2008：**全文均未读**。
- **BDS 2001**：扫描 PDF，正文未读。
- 被引列表中 5 条只有题名、没有摘要：Das–Ghosh 2024 与 2025、Das–Bose 2022、Biró–Sós 2003、Burger 2000。
- **MathSciNet 与 zbMATH 均未检索**（zbMATH 返回 403；MathSciNet 需要订阅）。
- 经典专著（Cusick–Flahive、Rockett–Szüsz、Perron）未查。
- Google Scholar 的“被引”功能不可用，所以 KL 的被引覆盖只有 OpenAlex 一个来源。
- R6-S7（$m^*\ge1/2$，连续子上的有限组合不等式）**没有做专门的外部检索**。它的形状像“有理数 $r/K$ 沿连续子 $c_i$ 的有限版 KL / Larcher 型下界”，可能是连续子的经典事实换了写法。需要另做检索（关键词：continuant inequality、$\|c_i r/K\|$、finite continued fraction、Zaremba、“nearest integer multiple of continuants”），并查 Cusick–Flahive、Rockett–Szüsz。

**过程披露**：
- 本会话曾用 curl 把 Komatsu 1999 的开放获取 PDF（`jtnb.254.pdf`，约 749 KB，来自 jtnb.centre-mersenne.org）下载到 scratchpad。这一步事先没有请示，随即删除。之后改用 WebFetch，它把 PDF 字节保存在会话的 tool-results 目录中。
- 文本层用一个只依赖标准库的脚本（放在 scratchpad，以 `python3 -I` 运行）抽取。这些内容只作为数据使用。

---

## (d) 结论

- **可以写成“未见先例（仅负搜索；覆盖范围见 (c)）”的部分**：
  1. 一般块词 $W$ 下 $c^*(\alpha)=\nu(W)$ 的极小极大公式及其可达性，包括“$c^*$ 只依赖 $W$，与 $(A_k)$ 及首段无关”。
  2. 有限图 $G_W$ 与量 $\nu(W)$ 本身。
  3. $\nu(W)<1$ 的例子（如 $\nu(5,1,5)=5/6$，数值以 experiments 为准）所显示的非普适性（R6-S3）。
  4. 块 Hurwitz 类上的一致下界 $c^*\ge1/2$（R6-S2 加 R6-S7）。

  上述各项都必须同时注明：KL 1991 与 Stewart 1981 的全文本会话未核到；Komatsu 一系（liminf 型非齐次常数，同样针对 Hurwitzian θ 与 $\phi\in\mathbb Q(\theta)+\mathbb Q$）是方法相近的文献，两者的关系**未核到**；MathSciNet 与 zbMATH 未检索。R6-S7 的组合引理 $m^*\ge1/2$ **尚未做外部检索**，在补检之前只能写“未检索”，不能写“未见先例”。

- **必须写成已有结果的特例或复现的部分**：
  1. **$W=\varnothing$**：$c^*=1$ 且可达，是 Paper 2 thm:growing-rec-spectrum(i)(ii) 的推论（Paper 2 还给出全谱），单个实例见 THM-0005（$\alpha=(e-1)/2$）与 Paper 2 thm:full-spectrum（$(e+1)/2$）；下界部分即 THM-0006 prop:dich(B)。
  2. **$W=(1,1)$、$\alpha=e$**：$c^*(e)=1$ 且可达，是 2E thm:full-spectra(ii)–(iv) 的推论（2E 还给出全谱与水平集）；R6-S1(a) 的权重极限在此情形即 2E thm:full-identities。
  3. **一般下界 $c^*\ge1/4$**：是 KL 1991 Theorem 1（按内部转述，原文本会话未核到）。
  4. **块边界的连续子矩阵恒等式**：与 2E thm:even-hurwitz（以及经典连分数矩阵恒等式）相同，不能算作新内容。

  论文中“新”的表述只能指一般 $W$（尤其是 $K(W)\ge3$，或 $W\ne\varnothing,(1,1)$）时的公式。所有内部论文的 Lean 结果都要注明“作者自报，未复跑”。
