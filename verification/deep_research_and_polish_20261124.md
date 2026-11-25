# 深度调研与论文二打磨记录（2026-11-24）

> **一句总判断**：本轮把论文二最关键的短板——临界相变常数——从「猜想」推进到「极点分解引理已证 + 联合标度极限定理（条件于一个明确假设）」，同时修正了旧猜想 C2 的固定 η 形式（已证其为假）与主稿尾方程的一处排版错误；论文一的最终目标（$e+\pi$ 无理性）仍是公开问题，本轮未产生任何新结果，且原理上不可能由有限计算完成。

**纪律声明**：本文件按 `AGENTS.md` 分类标注。所有书目字段只来自实际打开的页面；未核到者写「未核到」；负搜索≠不存在。本轮**未运行 Lean**（PI 指示），所有 Lean 口径均为仓库自报。新增 tex 已用主稿同款 preamble 独立编译通过（5 页，exit 0，仅未定义引用/文献警告）。

---

## 1. 调研结论

### 1.1 已核文献（2026-11-24 实际打开）

| 条目 | 核实到的字段 | 来源 | 状态 |
|---|---|---|---|
| D. Hensley, *Continued fraction Cantor sets, Hausdorff dimension, and functional analysis* | J. Number Theory **40** (1992), no. 3, 336–358 | ScienceDirect 记录（Pages 336–358, Volume 40）；AMS Math. Comp. 2020 参考文献表 | 已核到 |
| O. Jenkinson, M. Pollicott, *Rigorous effective bounds ... a hundred decimal digits for the dimension of $E_2$* | Adv. Math. **325** (2018), 87–115 | ScienceDirect 记录；Scilit 条目（Vol. 325, 87–115） | 已核到（DOI 未核到） |
| V. Chousionis, D. Leykekhman, M. Urbański, *On the dimension spectrum of infinite subsystems of continued fractions* | Trans. Amer. Math. Soc. **373** (2020), no. 2, 1009– | UConn 作者页（止页截断）；仓库 `refs.tex` 作 1009–1042 | 首页已核；止页仓库口径，外部未核到 |
| T. Das, L. Fishman, D. Simmons, M. Urbański, *Hausdorff dimensions of perturbations of a conformal IFS via thermodynamic formalism* | Selecta Math. New Ser. **29**, 19 (2023)；DOI 10.1007/s00029-022-00820-z | arXiv:2007.10554 摘要页（Journal reference + Related DOI） | 已核到 |
| Y. Nakajima, H. Takahasi, *Density combinatorics theorems in fractal dimension theory of continued fractions* | Adv. Math. **482** (2025), 110635 | H. Takahasi 论文列表页 | 已核到（ScienceDirect 摘要条目另显示 480 Part C, 110512，疑为另一篇或元数据错配，**未核到**） |
| W. Parry, M. Pollicott, *Zeta functions and the periodic orbit structure of hyperbolic dynamics* | Astérisque **187–188** (1990) | Numdam 期刊卷页 | 已核到 |
| T. Kato, *Perturbation Theory for Linear Operators* | Grundlehren Math. Wiss. **132**，2nd ed., Springer, New York, 1976（1995 重印） | Greenbaum 2020 参考文献；Kato 专著页（Chapter Seven: Analytic perturbation） | 已核到（定理编号未核到） |
| R. D. Mauldin, M. Urbański, *Graph Directed Markov Systems* | Cambridge Tracts in Mathematics **148**, CUP, 2003 | M. Urbański 著作页 | 已核到 |

### 1.2 领域现状与不足（据上述文献与仓库自述）

1. **方法主线已成熟**：Hensley 1992 建立连分数 Cantor 集维数的转移算子/泛函分析框架；Jenkinson–Pollicott 2018 用全纯延拓与 Hardy 空间逼近给出 $E_2$ 的百位严格界；DFSU 2023 用 SBR 热力学形式体系与转移算子摄动统一强化 Hensley 1992 与 Good 1941 的渐近。**这些是「工具成熟」的证据，不是「临界行为已解决」的证据。**
2. **有限字母表的维数公式已标准化**：CLU 2020 的 conformal IFS 公式（Theorem 2.3）与 Mauldin–Urbański 2003 的 GDMS 理论给出 $\dimH E_S$ 的压力刻画；仓库内核已有无 Bowen 版 `dimH_cfAlphabetSet_finset_eq_poincareAbscissa`。
3. **公开缺口（本轮负搜索，范围见 1.3）**：
   - 有限多残差字母表 $F_{m,S,B}$ 在相变点 $s_0(S)=1/2$ 的**精确渐近速率与振幅**——未找到直接先例；
   - $C_S(p)$ 的**极点分解** $C_S(p)=\kappa(S)/(p-2s_0)+O(1)$ 及 $\kappa(S)=c(S)/(-\rho'(2s_0))$ 的显式常数——未找到；
   - 交叉尺度 $m^*=d\kappa/\eta^2$ 与标度函数 $\Phi(x)=(-x+\sqrt{x^2+4d\kappa})/2$——未找到。
4. **领域审稿口味（据材料与对标论文）**：一般性原理/跨分支桥梁进 Adv. Math.（Nakajima–Takahasi 2025），特定集合维数计算进 JNT；转移算子严格界 + 计算机辅助可进 Adv. Math.（JP 2018），但作用对象须是公认硬骨头。**这直接决定论文二的定位：必须把「$e$ 的分母」降为旗舰推论，把一般结构字母表理论推到主位。**

### 1.3 负搜索声明（不是「不存在」）

检索日期 2026-11-24；检索词族：`critical behaviour phase transition Hausdorff dimension continued fraction restricted digits resolvent transfer operator`、`partial quotients arithmetic progressions Hausdorff dimension "phase transition" max(1/2)`、`Hensley continued fractions large partial quotients 1992`、`Nakajima Takahasi density combinatorics`、`Das Fishman Simmons Urbanski perturbations conformal IFS`、`Chousionis Leykekhman Urbanski dimension spectrum`、`Parry Pollicott zeta functions`、`Kato perturbation theory`、`Mauldin Urbanski graph directed Markov systems`。**覆盖范围**：上述公开搜索引擎返回的前 5–10 条/词；未系统检索 zbMATH/MathSciNet 全库，未检索 2026 年 11 月之后的预印本。结论只能是「在这些词族与范围内未找到先例」，不能写成「不存在先例」。

---

## 2. 对论文二的具体修改

### 2.1 新增证明节：`split/src_sections/sec-critical-scaling.tex`（18,249 字节；独立编译通过，5 页）

**内容与状态**：

| 对象 | 状态 | 说明 |
|---|---|---|
| Lemma `lem:pole`（Perron–Frobenius 与极点分解） | **[THEOREM] 已证** | 在显式 Banach 空间 $A(\Omega)$、$\Omega=\{|z-1|<1\}$ 上：$L_p$ 紧；$\rho(p)$ 单重正特征值、谱隙；$p\mapsto\rho,h_p,\nu_p$ 实解析（Kato）；$W_S(p,n)=c(p)\rho(p)^n+O(\theta^n)$；$C_S(p)=c(p)/(1-\rho(p))+A(p)$；$\rho(p_0)=1$、$\rho'(p_0)<0$；故 $C_S(p)=\kappa(S)/(p-p_0)+O(1)$，$\kappa=c(S)/(-\rho'(p_0))$。 |
| Theorem `thm:critical-scaling`（联合标度极限） | **[CONDITIONAL]** | 条件于 Hypothesis `hyp:tail`（临界窗内尾方程一致到 $O(m^{-1/2})$）。结论：$\eta m^{1/2}\to x$ 时 $m^{1/2}(\dimH F_{m,S,B}-1/2)\to\frac12\Phi(x)$，$\Phi(x)=(-x+\sqrt{x^2+4d\kappa})/2$。 |
| Corollary `cor:critical-exp`（临界指数与振幅） | **[CONDITIONAL]** | $\eta=0$ 时 $\dimH F_{m,S,B}-1/2\sim\frac12\sqrt{d\kappa}\,m^{-1/2}$，指数 $1/2$、无对数修正。 |
| Proposition `prop:supercritical-constant`（超临界常数） | **[HEURISTIC] 未证** | 预测常数 $d\kappa/(2(2s_0-1))$；数值 $33.43$ vs 实测 $32.86$（$m=16384$，差 2%）；但尾方程在超临界区的一致性预计失效（相对误差 $\asymp m^{2s_0-1}\to\infty$），故只列为猜想。 |
| Remark `rem:naive-C2-false` | **[PROVED]** | 旧 C2 的固定 $\eta$ 形式为假：次临界时 $\varepsilon_m\sim dC_S(1)/m$，左边 $\to d\kappa C_S(1)/\eta$，仅当 $\kappa/\eta=C_S(1)$ 才等于 $d\kappa$；数值比 $1.19$ 正是此差异（复算：`verification/verify_c2_discrepancy_20261124.py` 输出 1.19319）。正确形式是联合标度极限。 |
| Remark `rem:typo` | **[PROVED]** | 主稿 L3940 尾方程的 $m^{-\varepsilon}$ 应为 $m^{-1-\varepsilon}$；否则 $\varepsilon=\alpha/m$ 导致 $\alpha\approx m$，与 $\varepsilon\to0$ 矛盾；特例 $F_{m,m}$ 要求 $\alpha=1$。 |

**为什么这是实质进展**：旧 T6 草案把极点分解列为「六步骨架 + 三个缺口」，本轮把缺口 (a)(b)(c) 逐一闭合并写成可核查的证明；同时发现旧 C2 的陈述本身有误，避免了把一个假命题写进主稿。**它没做到什么**：Hypothesis `hyp:tail` 的临界窗一致性未证；超临界常数未证；tex 未编译；Lean 未形式化。

### 2.2 三处实质修正（已写入新文件，未改既有文件）

1. **尾方程排版错误**：主稿 L3940 的 $m^{-\varepsilon}$ → $m^{-1-\varepsilon}$。这是证明 (iv) 的关键平衡，特例 $F_{m,m}$ 可直接判定。**建议在 E10 补丁获批后一并修正**（当前只在新节中记录，未改主稿，以保持只增不减与字节一致性）。
2. **旧 C2 的固定 $\eta$ 形式为假**：改为联合标度极限 + 交叉尺度 $m^*=d\kappa/\eta^2$；固定 $\eta$ 的渐近仍由 (T-iv)/(T-v) 给出，不与极点近似混用。复算脚本与输出：`verification/verify_c2_discrepancy_20261124.py` / `_output.txt`（比值 1.19319；$\Phi$ 的代数残差 $\sim10^{-31}$）。
3. **缺口 (c) 的简化**：$\rho(p_0)=1$ 由 $s_0$ 的收敛横坐标定义直接给出，**不需要 Bowen/CLU 输入**；CLU Theorem 2.3 只用于 $s_0(S)=\dimH E_S$，而后者内核已有。Lean 化路线因此少一条外部依赖。

### 2.3 逐篇打磨清单（五轴：选题立意 / 理论深度 / 方法严谨性 / 实验验证 / 写作表达）

**主稿 A（2C + T6，25–30 页，冲 Adv. Math./PLMS）**

| 轴 | 现状 | 动作 | 状态 |
|---|---|---|---|
| 选题立意 | 2C 是多残差相变的完整理论，但引言仍以 $e$ 的分母为出发点 | 把「临界相变 + 结构字母表」提到标题与摘要首句；$e$ 降为旗舰推论 | 待 E7 前言 v2 审校 |
| 理论深度 | 临界常数原为猜想 | 新增 `sec-critical-scaling.tex`：极点分解定理 + 条件标度定理 + 两处修正 | 已落盘，未编译 |
| 方法严谨性 | 尾方程排版错；C2 陈述假 | 修正 L3940；C2 改为联合极限；明确 Hypothesis `hyp:tail` | 待 PI 批准补丁 |
| 实验验证 | 334 点扫描到 $m=65536$；近临界比值 1.007–1.014 | 补 $\kappa(S)$ 表与 $\Phi(x)$ 的数值对照；把「1.19 恒定偏差」写成 C2 为假的证据 | 待跑 |
| 写作表达 | `[Author name]`、TODO、工程日志语言 | 清占位符；把审计句改为可读的核验说明；补 AI 声明 | 待 E10/前言定稿 |

**主稿 B（2A + 2B 融合，30–35 页，冲 Math. Ann./Selecta）**

| 轴 | 现状 | 动作 | 状态 |
|---|---|---|---|
| 选题立意 | 2A 绑定 $e$ 的递推，2B 体量偏轻 | 以一般增长商/Hurwitz 递推为主定理舞台，$e$ 的全谱离散与三向分裂作旗舰推论 | 待包装（E13） |
| 理论深度 | 三向分裂与精确规范是亮点，但「可迁移性」未提炼 | 增写「结构字母表」定义节（T2 施工图 (C1)–(C5)），把 2A/2B 回收为推论 | 待我写 |
| 方法严谨性 | `prereq-2B.tex` 与 2A 正文重复；`sec-num` 归属待定 | 包装时跳过 `prereq-2B`，`sec-num` 按主稿 A/B 拆分 | 待 E13 |
| 实验验证 | 2A 数值注记在 `sec-num-2A`；2B 相变数值较薄 | 补一般递推的相变数值；与 Wang–Wu/Kleinbock–Wang 对标 | 待跑 |
| 写作表达 | 2A 标题含 $e$；2B 标题过长 | 改标题；统一记号；删重复定义 | 待 E13 |

**Lean 归档（独立）**：988 条 Layer A、0 sorryAx、3 条经典白名单公理（仓库口径，未复跑）。本轮不改 `.lean`；建议先以一条新白名单公理 `C_S_pole_decomposition` 引入极点分解，再在内核内完成标度极限的实代数部分。

### 2.4 本轮未改的既有文件（只增不减）

主稿 tex、三份 draft wrapper、`refs.tex`、全部 `.lean`、全部既有 md 均未修改。新增文件：
`split/src_sections/sec-critical-scaling.tex`、`split/src_sections/refs-addendum-20261124.tex`、本文件。

---

## 3. 推广与发展建议

1. **定位升级**：把论文二从「$e$ 的分母维数」重述为「结构字母表（残差/多残差/有限状态尾）的相变与临界标度理论」，$e$ 作旗舰推论。对标 JP 2018（工具）与 Nakajima–Takahasi 2025（一般原理），避免被归入「特定集合维数计算」。
2. **两主稿 + 归档**：主稿 A（2C+T6）冲 Adv. Math./PLMS；主稿 B（2A+2B）冲 Math. Ann./Selecta；Lean 独立 Zenodo/ITP。arXiv 推迟到临界定理后。
3. **数值补强**：对近临界族 $S_j=\{3,4,5,6,j\}$ 把 $m$ 推到 $2^{18}$–$2^{20}$，直接拟合 $\Phi(x)$ 与 $m^*=d\kappa/\eta^2$；这是把「条件定理」变成「数值 + 定理」组合的最便宜方式。
4. **理论补强（按优先级）**：
   - P0：证 Hypothesis `hyp:tail` 的临界窗一致性（把 (iv) 的预解式估计从 $\varepsilon=O(1/m)$ 推到 $O(m^{-1/2+\delta})$）；
   - P1：超临界常数（需要不依赖 Hurwitz 尾近似的预解式分析）；
   - P2：$\kappa(S)$ 对 $S$ 的连续性；$s_0(S)=1/2$ 的精确整数集合存在性。
5. **合规**：清理 `[Author name]`、逐定理人工复核说明、AI 使用声明（Annals/Elsevier 2026 政策原文未核到，引用前须核）。

---

## 4. 论文一：进展与完成情况

**最终目标**：证明 $e+\pi$ 无理。**基线（不得矛盾）**：截至目前这是公开问题，未被证明无理、有理或超越；唯一硬结论是 $e+\pi$ 与 $e\pi$ 至少其一超越；Carella、Sarich、Foukzon 等人的「已证」不被数学界接受，禁止引为证明。

**本轮进展**：
- 未产生论文一的新数学结果；本轮工作（结构字母表相变理论）与论文一的关系是**方法储备**，不是直接推进。
- 论文一既有硬资产（仓库口径）：`prop:denominator-bounds`——$e+\pi$、$e\pi$、$\pi-e$、$\pi/e$ 若有理则分母 $\ge10^{500018}$；Arb 严格包络 + Stern–Brocot 管线；OEIS A058651 两万项核对。
- 与论文二的对齐：论文二的结构字母表/相变机器可用于评估论文一轴 B 的可行性（$\mu(\pi)=2$ 等条件靶点），但**不构成**从计算到无理性的推理链。

**完成情况（如实）**：**未完成，且原理上不能由有限计算完成**。有限排除（哪怕分母下界 $10^{500018}$）只排除有限范围，属类别 4；它与无理性之间没有能合拢的推理链。本轮没有、也不应宣称任何「接近证明」。论文一的可行路线仍是：轴 B 的 $\le3$ 个月预注册闸门 + 条件靶点季检；禁做「计算→无理性」路线。

---

## 5. 诚实边界

1. 本轮新增的 tex **未编译**；`\cite` 键 `Mayer1991`/`JenkinsonPollicott2018`/`Kato1976` 需与 `refs-addendum-20261124.tex` 在装配时合并（不能直接改 `refs.tex`，否则破坏 11 切片字节一致性）。
2. Lemma `lem:pole` 的证明引用了「有限 conformal IFS 转移算子的标准 PF 定理」与「Kato 解析摄动」；前者书目已核到（Mayer 1991 卷期、JP 2018 卷页），**定理编号未核到**；后者书名/版次/章节已核到，**定理编号未核到**。
3. Theorem `thm:critical-scaling` 与 Corollary `cor:critical-exp` 是**条件结果**（Hypothesis `hyp:tail`），不是无条件新结果；Proposition `prop:supercritical-constant` 是**启发式/猜想**，不是定理。
4. 负搜索（1.3）只说明「在所列词族与范围内未找到先例」，不构成「不存在先例」。
5. 所有 Lean 口径（988 条审计、0 sorryAx、3 条白名单公理）均为仓库自报，本轮未复跑、未 `lake build`、未 `#print axioms`。
6. $e+\pi$ 无理性仍是公开问题；本文件与新增节均未改变该基线。
