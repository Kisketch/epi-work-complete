# Bowen 压力公式 / 热力学形式体系 / Mauldin–Urbanski 依赖清点（2026-11-24）

**口径**：本文件属 AGENTS.md 第 2 节「类别 4：有限计算 / 文献核查」与「类别 5：文献核查与复现」口径，只做清点，不作证明引用。
**只读**：本文件为唯一新建文件；未修改任何 .tex / .lean / .py / .md / 日志；未运行 `lake`；未联网。
**基线**：`git rev-parse --short HEAD` = `f345d60`，与 `origin/main` 同步；`git status --porcelain` 在本任务开始时显示 3 个未跟踪文件（`development_plan_20261124.md`、`paper2_numeric_check_20261124.py`、`paper2_numeric_check_20261124_output.txt`），均非本次产物；任务执行期间并行任务又新增若干未跟踪文件（如 `PI_*.md`、`verification/critical_point_scan_*`），亦非本次产物。**全程无任何已跟踪文件被修改**（`git status --porcelain` 无 ` M` 行）。

## 0. 检索方式与分类图例

检索命令（全部实测，行号即 rg 输出行号）：

```
rg -n -i "bowen|pressure|thermodynamic|mauldin|poincar" paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex   # 28 行命中 / 4463 行
rg -n -i "bowen|pressure|thermodynamic|mauldin|poincar" paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex               # 0 行命中 / 4759 行
rg -n -i "bowen|pressure|thermodynamic|mauldin|poincar" epi_formal -g '*.lean'                                              # 133 行命中 / 4 个文件
```

辅助检索（paper1 反向核查）：`Bowen / pressure / thermodynamic / Mauldin / Poincar / Hensley / Jenkinson / Gibbs / transfer operator` 逐词计数均为 0；`Urba` 命中 1 行，经核对为 `\bibitem{Lang1966}` 中的 “Bourbaki”（子串误命中），**非 Urbański 引用**。

分类图例（每处命中必居其一）：

| 标记 | 含义 |
|---|---|
| **a** | 已被无 Bowen 的 Poincaré 横坐标 / 传递算子判据在 Lean 内核替代（给出 Lean 文件:行 与定理名） |
| **b** | 可替代：内核已有机器但未接线（写明缺的接线） |
| **c** | 暂不可替代：剩余依赖，列出精确缺口 |
| **n** | 无数学依赖：历史叙述、替代声明、期刊名、书目条目，不计入剩余依赖 |

**证据等级声明（重要）**：Lean 侧的“已 kernel-checked”状态在本任务中**未复跑**（PI 硬规则禁止 `lake`），一律按 AGENTS.md 第 5 节标为「**作者自报，未复跑**」。本文件对 Lean 的核实只到“**声明存在且语句与论文所述相符**”（已逐个打开源文件读语句），不等于 kernel 检查。

---

## 1. 一句总判断

主稿 28 处命中中，**16 处是无 Bowen 替代机器的引用（a）、8 处是同一剩余依赖（开区间严格性）的不同表述（c）、4 处无依赖（n）、0 处属 b**；论文与 Lean 内核对 Bowen 的**唯一实质剩余依赖是“开区间严格性 + 谱半径=1 数值判据”**，前者摘要已自报且核实一致，**后者摘要未自报（遗漏）**。

---

## 2. 主稿 `paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`（28 行命中）

| 编号 | 文件:行 | 原文摘录（≤2 行） | 用途 | 分类 | 依据 / 缺口 | 备注 |
|---|---|---|---|---|---|---|
| M01 | paper2:110 | `establishes the Bowen-free Poincar\'e-abscissa dimension $\dimH E_S=s_0(S)$, the` | 摘要·叙述（自述替代） | **a** | `epi_formal/EpiFormal/ResidueMultiAsymptotic.lean:910` `theorem dimH_cfAlphabetSet_finset_eq_poincareAbscissa` | 作者自报，未复跑 |
| M02 | paper2:143 | `(bypassing Bowen-pressure axioms), strict lower bound $\dimH F_{m,r}>1/2$, upper` | 摘要·替代声明 | **a** | `TransferOperatorDim.lean:420` `dimH_le_of_transferOp_le`、`:1491` `le_dimH_of_transferOp_ge`、`:1806` `dimH_residueMod4_le_four_fifths` | 同上 |
| M03 | paper2:160 | `via the pressure formalism remain outside the Lean kernel` | 摘要·自报剩余 | **c** | 内核只有单侧闭界，见 R1 | 与 paper2:3653、4398 同一依赖 |
| M04 | paper2:258 | `Bowen-free Poincar\'e-abscissa dimension formula for finite alphabets $E_S$,` | 导言·叙述 | **a** | 同 M01（`ResidueMultiAsymptotic.lean:910`） | — |
| M05 | paper2:350 | `infinite-alphabet thermodynamic-formalism dimension theory goes back to Hensley,` | 历史叙述 | **n** | 仅指向 `\cite{CLU}`（条目在 paper2:4422） | 书目字段未核到原文 |
| M06 | paper2:1974 | `For comparison, the graph-directed similarity results of Mauldin` | 对照叙述 | **n** | `\cite[Theorems~3 and~4]{MW}`（条目 paper2:4453）；同段自陈 “Here the scales are supplied by $Q_n$” | 未用作证明步骤 |
| M07 | paper2:3451 | `\emph{Step 2: Transfer operator, Bowen's formula, and integral tail bounds.}` | 证明步骤（thm:residues） | **c** | 该步用 Bowen 公式把压力符号转成维数不等式，支撑开区间；内核无对应严格式 | 依赖簇 C1 的标题行 |
| M08 | paper2:3460 | `The topological pressure $P(s,\mathcal D)$ is the limit of` | 证明步骤·定义 | **c** | 同 C1 | — |
| M09 | paper2:3465 | `pressure $s\mapsto P(s,\mathcal D)$ is continuous and strictly decreasing on` | 证明步骤 | **c** | 同 C1 | — |
| M10 | paper2:3466 | `$(1/2,\infty)$, and Bowen's formula identifies its unique zero with the` | 证明步骤·核心引用 | **c** | `\cite[\S2, Theorem~2.3]{CLU}`（paper2:3468）；**定理编号未核到**（禁联网，未开原文） | 依赖簇 C1 的实质引用点 |
| M11 | paper2:3473 | `$\mathcal L_{s,\mathcal D}^2$ (so its pressure is $2P(s,\mathcal D)$, with the` | 证明步骤 | **c** | 同 C1 | — |
| M12 | paper2:3578 | `Without appealing to Bowen's pressure formula or external \cite{CLU} citations,` | thm:residues-general(ii) 陈述 | **a** | `TransferOperatorDim.lean:2131` `step_cert_upper_sound`、`:2242` `step_cert_lower_sound`、`:420`、`:1491` | 这是替代 Bowen 的**无 Bowen 判据**本体 |
| M13 | paper2:3634 | `Independently of Bowen's formula, every closed bracket` | Remark rem:residue-kernel | **a** | `ResidueCertTable.lean:35/45/55/65/75/85/95/105/115/125/135/145/155/165/175/185/195/205/215/225`（20 条单侧闭界） | 作者自报，未复跑 |
| M14 | paper2:3653 | `(open intervals) uses the positive margins and the pressure argument of` | Remark·自报剩余 | **c** | 同段下句 “which is not formalised” | **论文自认开区间严格性未形式化** |
| M15 | paper2:3817 | `the Poincar\'e abscissa (\texttt{poincareAbscissa S}), and, whenever convergent,` | 定义 | **a** | `ResidueMultiAsymptotic.lean:520-523` `def poincareAbscissa` | — |
| M16 | paper2:3825 | `\item \textbf{Bowen-free Poincar\'e-abscissa dimension for finite alphabets:}` | 定理陈述 | **a** | 同 M01 | — |
| M17 | paper2:3835 | `without invoking Bowen's pressure formula.` | 定理陈述 | **a** | 同 M01 + M12 | — |
| M18 | paper2:3894 | `$1\le W_S(2s_0(S),n)\le 2^{2s_0(S)}$ (\texttt{one\_le\_wordSum\_poincareAbscissa},` | 证明步骤·Lean 引用 | **a** | `ResidueMultiAsymptotic.lean:548` `one_le_wordSum_poincareAbscissa` | — |
| M19 | paper2:3895 | `\texttt{wordSum\_poincareAbscissa\_le}), absolute` | 证明步骤·Lean 引用 | **a** | `:575` `wordSum_poincareAbscissa_le` | — |
| M20 | paper2:3897 | `(\texttt{summable\_wordSum\_of\_poincareAbscissa\_lt}),` | 证明步骤·Lean 引用 | **a** | `:534` `summable_wordSum_of_poincareAbscissa_lt` | — |
| M21 | paper2:3899 | `(\texttt{not\_summable\_wordSum\_of\_lt\_poincareAbscissa}).` | 证明步骤·Lean 引用 | **a** | `:543` `not_summable_wordSum_of_lt_poincareAbscissa` | — |
| M22 | paper2:3906 | `Theorem~\ref{thm:residues-general}(ii) without Bowen's formula` | 证明步骤 | **a** | 同 M12 | — |
| M23 | paper2:3907 | `(\texttt{dimH\_cfAlphabetSet\_finset\_eq\_poincareAbscissa}).` | 证明步骤·Lean 引用 | **a** | `ResidueMultiAsymptotic.lean:910` | — |
| M24 | paper2:4051 | `(Bowen-free Poincar\'e-abscissa dimension, multi-residue phase transition` | 核查状态段·报告 | **a** | 报告 `ResidueMultiAsymptotic.lean` 24 条 + `AuditResidueMultiAsymptotic.lean` | 作者自报，未复跑 |
| M25 | paper2:4330 | `(Bowen-free Poincar\'e-abscissa dimension for finite alphabets, universal` | 核查状态段·报告 | **a** | 同上 | 作者自报，未复跑 |
| M26 | paper2:4398 | `cited pressure formalism (the closed brackets themselves are kernel-checked,` | 核查状态段·自报剩余 | **c** | 同 M03/M14 | 与 M03、M14 同一依赖 |
| M27 | paper2:4440 | `the Markov and Lagrange dynamical spectra}, Ann. Inst. H. Poincar\'e` | 书目·期刊名 | **n** | 非 Poincaré 横坐标，非依赖 | `\bibitem{LimaMoreira}` |
| M28 | paper2:4453 | `\bibitem{MW} R.~D.~Mauldin and S.~C.~Williams,` | 书目·条目 | **n** | 仅被 paper2:1974 对照引用 | 卷页按 tex 原文，未核 |

**主稿计数**：a = 16（M01,M02,M04,M12,M13,M15,M16,M17,M18,M19,M20,M21,M22,M23,M24,M25）；b = 0；c = 8（M03,M07,M08,M09,M10,M11,M14,M26）；n = 4（M05,M06,M27,M28）。
**去重后的依赖簇**：c 的 8 行实为 **2 个**依赖——C1 = 证明步骤用 Bowen 公式（M07–M11，同一段 Step 2）；C2 = 自报剩余（M03/M14/M26，同义三处）。

---

## 3. `split/src_sections/*.tex` 核对

**同源性核实（实测）**：按 `slice_index.csv` 顺序拼接 11 个基础切片（sec-preface, sec-class, sec-spectrum, sec-finite, sec-weights, sec-gauge, sec-growing, sec-windows, sec-resasymp, sec-num, sec-verification），共 **4463 行**，与主稿 4463 行**逐行比较 0 差异**。故主稿与基础切片内容同源，**以主稿为准**成立。

**但 `slice_index.csv` 的行区间已陈旧**：索引记 `sec-preface` 为 1–389 行，实际该文件 416 行；`sec-windows` 记 748 行，实际 776 行（例：`sec-windows.tex:570` ↔ 主稿 `:3451`）。索引需重新生成（本任务不改既有文件，仅记录）。

**主稿没有的额外引用（3 处，全部在 `*-2C` 变体文件中）**：

| 编号 | 文件:行 | 原文摘录 | 用途 | 分类 | 依据 / 缺口 |
|---|---|---|---|---|---|
| S01 | split/src_sections/frontmatter-2C.tex:25 | `combines exact Python integer certificates with the cited pressure formalism.` | 变体摘要·自报剩余 | **c** | 与主稿 M03/M26 同义但措辞不同；主稿无此句 |
| S02 | split/src_sections/intro-2C.tex:33 | `multi-residue alphabets $F_{m,S,B}$---giving a Bowen-free Poincar\'e-abscissa` | 变体导言·叙述 | **a** | 同 M01 |
| S03 | split/src_sections/intro-2C.tex:73 | `Bowen-free Poincar\'e-abscissa formula $\dimH E_S=s_0(S)$, the phase transition` | 变体导言·叙述 | **a** | 同 M01 |

其余命中（`frontmatter.tex`、`sec-preface.tex`、`intro-shared.tex`、`sec-windows.tex`、`sec-resasymp.tex`、`sec-verification.tex`、`refs.tex`、`sec-finstate.tex`、`sec-gauge.tex` 等）均可按文本前缀在主稿中找到，属同源副本，不重复计数。

---

## 4. `paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex`

**0 命中**（4759 行）。逐词反向核查亦为 0：`Bowen`、`pressure`、`thermodynamic`、`Mauldin`、`Poincar`、`Hensley`、`Jenkinson`、`Gibbs`、`transfer operator`；`Urba` 的 1 处命中经核对为 `Bourbaki` 子串误命中（paper1:3988 `\bibitem{Lang1966}`）。

**结论**：paper1 对 Bowen 压力公式 / 热力学形式体系 / Mauldin–Urbanski **无任何依赖**（含注释、书目、附录）。
**这是负搜索结论**：覆盖范围为该单一文件全文（4759 行）+ 上述 10 个关键词（含大小写不敏感），**不等于“已证明不存在”**其他表述方式（如中文“热力学”“压力”“鲍恩”“庞加莱”亦已检索，0 命中）。

---

## 5. Lean 工程 `epi_formal/`（133 行命中 / 4 个文件）

| 文件 | 命中行数 | 内容性质 | 分类 | 依据 |
|---|---|---|---|---|
| `EpiFormal/ResidueMultiAsymptotic.lean` | 117（其中 `poincar` 117、`bowen` 4） | `poincareAbscissa` 的定义、引理、定理名与文档串 | **a** | `:520-523` 定义；`:534/:543/:548/:575` 引理；`:910-912` `dimH_cfAlphabetSet_finset_eq_poincareAbscissa`；`:1374-1379`、`:4192-4212`、`:4470-4477`、`:4648-4682`、`:5010-5034` 均为以 `poincareAbscissa` 表述的定理 |
| `AuditResidueMultiAsymptotic.lean` | 9 | 文档串（`:6-7`）+ `#print axioms` 行（`:14,:15,:16,:17,:21`） | **a** | 审计清单，非依赖 |
| `EpiFormal/TransferOperatorDim.lean` | 6（`bowen` 6，其中 1 行同时含 `pressure`） | 文档串/章节标题（`:5,:7,:213,:303,:437,:925`） | **a** | `:2131 step_cert_upper_sound`、`:2242 step_cert_lower_sound`、`:420 dimH_le_of_transferOp_le`、`:1491 le_dimH_of_transferOp_ge`、`:1806 dimH_residueMod4_le_four_fifths` |
| `EpiFormal/ResidueAsymptotic.lean` | 1 | `:16` 文档串 `requiring no Bowen pressure formula.` | **a** | 同上 |

**关键否定核查（实测）**：
- `epi_formal` 内**无任何** `def pressure` / `noncomputable def pressure`（关键词 `pressure` 的 6 处命中全在 `TransferOperatorDim.lean` 的注释与标题，非定义）。
- 全仓库 `axiom` 声明共 **3 条**：`Axioms.lean:13` `e_transcendental`、`Axioms.lean:16` `pi_transcendental`、`Measure.lean:27` `mu_e_eq_two`，**均与 Bowen/压力/热力学无关**。故不存在“以公理形式引入 Bowen 公式”的情况。
- 依赖：`lakefile.toml` 要求 `mathlib` rev `v4.35.0`（本任务未构建）。

按关键词拆分（实测）：`bowen` 13 行、`pressure` 2 行、`thermodynamic` 0 行、`mauldin` 0 行、`poincar` 125 行；同一行命中多词时合并计数，故去重后 133 行。全部 `bowen`/`pressure` 命中均位于**文档串、章节标题或 `#print axioms` 审计行**，无一是定义或证明步骤。

另：`epi_formal/README.md:2`（非 `.lean`）含 1 处 `无 Bowen 庞加莱横坐标`，为状态说明文字，分类 **n**。

**Lean 侧结论**：133 处命中**全部**是“替代机器”的命名、注释或审计行，**无一处是把 Bowen 公式作为输入**；Lean 侧对 Bowen 的剩余依赖为 **0**。

---

## 6. 数值管线（3 个脚本）

| 编号 | 文件:行 | 原文摘录（≤2 行） | 用途 | 分类 | 依据 / 缺口 |
|---|---|---|---|---|---|
| N01 | verification/asymptotic_residues_check_20261123.py:13 | `so there is no alphabet truncation.  dimH = the s with spectral radius 1 (Bowen / Mauldin-Urbanski).` | 数值方法依据 | **c** | 谱半径=1 ⟺ dimH 正是 Bowen/Mauldin–Urbanski；内核无对应物。见 R2 |
| N02 | 同文件:36-49（`rho()`）、:51-60（`dim_estimate` 对 `rho(s)-1` 二分） | `"""Spectral radius of the n-point collocation of L_s ..."""` | 数值方法实现 | **c** | 与 N01 同一依赖（实现层） |
| N03 | verification/verify_residue_multi_asymptotic.py:95-125、:220、:226 | `ev = mp.eig(M * vandermonde_inv(n), left=False, right=False)` | 数值方法依据（隐式） | **c** | 未点名 Bowen，但同用“谱半径=1”判据；无内核对应物 |
| N04 | verification/residue_certificate_general_N512.py | `"""Exact integer transfer-operator certificates, N=512 variant."""` | 数值方法（证书） | **a** | 关键词 0 命中；方法即 thm:residues-general(ii) 的无 Bowen 阶梯函数判据，对应 `TransferOperatorDim.lean:2131/:2242` 与 `ResidueCertTable.lean` |

**判断**：`residue_certificate_general_N512.py` 的“维数=压力零点”**不**依赖 Bowen——它算的是阶梯函数不等式的精确整数余量，对应论文 thm:residues-general(ii) 的无 Bowen 判据，并在 Lean 中由 `step_cert_upper_sound` / `step_cert_lower_sound` 复检（作者自报，未复跑）。
反之，两个 **Chebyshev 配点脚本**（N01–N03）的“谱半径=1 即维数”判据**依赖 Bowen / Mauldin–Urbanski**，且**无内核替代**。论文对它们一律标注 non-rigorous（paper2:3986 表题、:4023、:4044、:4137-4145 “independently corroborates”），**不支撑任何定理**。

---

## 7. 摘要自报两处的核实

摘要原文（paper2:157-160）：
> `Only the finite-dimensional linear-algebraic Perron--Frobenius eigenvector existence input in Theorem~\ref{thm:finite-state-tail} and the Python-executed open-interval strictness verification of the narrow $m\in\{2,3,4,5,6\}$ brackets via the pressure formalism remain outside the Lean kernel`

| 自报项 | 核实结果 | 依据 |
|---|---|---|
| (1) PF 特征向量存在性输入在内核之外 | **一致** | `epi_formal/EpiFormal/FiniteStateComplete.lean:1805` `theorem thm_finite_state_tail_complete` 的第 (2) 支以 `∃ (w : Component edges v → ℝ) (lo : ℝ), 0 < lo ∧ (∀ u, (∑ z, adjacency ... * w z) = w u) ∧ ∀ u, lo ≤ w u` 作为**显式假设**（`:1813-1817`），即正右特征向量是输入而非结论；论文 `:1994` 的 “Lean status” 段亦自陈 “taken as an explicit hypothesis rather than derived via Lean matrix-eigenvalue machinery” |
| (2) 开区间严格性的 Python 压力形式验证在内核之外 | **一致** | `ResidueCertTable.lean` 只有 **20 条单侧闭界**（`:35`–`:225`，形如 `l ≤ dimH` / `dimH ≤ u`）与 **5 条跨集合严格分离**（`:236`–`:257`，`F_{m,m} < F_{m,1}`），**没有** `dimH F_{m,r} < upper` 或 `lower < dimH F_{m,r}`；论文 `:3653-3655` 自陈 “Strictness of the brackets (open intervals) uses the positive margins and the pressure argument of Theorem~\ref{thm:residues}, which is not formalised” |

**是否有遗漏：有 1 处（Bowen 相关）+ 1 处（非 Bowen，但摘要口径窄于正文）**

- **遗漏 R2（Bowen 相关）**：摘要只提“开区间严格性”，**未提**两个配点脚本的“谱半径=1 ⟺ dimH”判据（N01 明写 `Bowen / Mauldin-Urbanski`，N03 隐式）。该判据是独立的 Bowen 依赖，不落在摘要两项之内。
- **口径差异（非 Bowen）**：正文 §verification（paper2:4393-4401）自列 **4 项**未解/内核外内容——(i) PF 特征向量、(ii) 开区间严格性、(iii) **临界边界 $s_0(S)=1/2$ 的渐近率与超临界首项常数**、(iv) $e+\pi$ 无理性——摘要只列前两项。第 (iii) 项与 Bowen 无关，但说明摘要的自报**不完整**。

---

## 8. 汇总与「确切的剩余依赖清单」

**计数**

| 范围 | a | b | c | n | 合计 |
|---|---|---|---|---|---|
| paper2 主稿（28 行） | 16 | 0 | 8 | 4 | 28 |
| split 额外引用（3 行） | 2 | 0 | 1 | 0 | 3 |
| paper1 | 0 | 0 | 0 | 0 | 0 |
| Lean（133 行，按文件归并） | 133 | 0 | 0 | 0 | 133 |
| 数值管线（按依赖项） | 1 | 0 | 3 | 0 | 4 |

**剩余依赖确切清单（Bowen 家族）**

- **R1｜开区间严格性（论文证明层，未进内核）**
  位置：paper2:3451–3473（Step 2，簇 C1）、:160、:3653、:4398；split `frontmatter-2C.tex:25`。
  内容：`thm:residues` 断言 `357/512 < dimH F < 179/256`，Table 1 十个区间均为**开**区间；证明用 Bowen 公式（`\cite[\S2, Theorem~2.3]{CLU}`，paper2:3468）把 $P(s)<0$ / $P(s)>0$ 转成**严格**维数不等式。
  精确缺口：`ResidueCertTable.lean` 只有 `l ≤ dimH` 与 `dimH ≤ u`（闭），无严格式；`step_cert_upper_sound`（`:2131`）给的是 `≤`。
  性质：**c**；可行的 b 路线见 §9（未验证）。

- **R2｜配点脚本的“谱半径=1 ⟺ dimH”判据（数值层，无内核对应）**
  位置：`verification/asymptotic_residues_check_20261123.py:13`（明写 `Bowen / Mauldin-Urbanski`）、同文件 `rho()`/`dim_estimate`；`verification/verify_residue_multi_asymptotic.py:95-125`（`rho_finite`/`rho_multi_residue` 用 `mp.eig`，对 `rho−1` 求根）。
  精确缺口：内核只有 `poincareAbscissa`（分区和 $\sum_n W_S(2s,n)$ 的收敛横坐标），**不等同于**有限矩阵谱半径；二者之间的桥恰是 Bowen/Mauldin–Urbanski。
  影响面：仅 non-rigorous 数值佐证（paper2:3986、:4023、:4044、:4137-4145），不支撑任何已证定理。性质：**c**（但**不影响**任何定理的真值）。

- **R3｜（非 Bowen，属摘要自报项）PF 正右特征向量存在性**
  位置：`FiniteStateComplete.lean:1813-1817`（显式假设）；论文 `:1994` 自陈。
  精确缺口：非负不可约矩阵正右特征向量存在性的有限维证明；Mathlib v4.35.0 是否已有可用引理——**未核到**（禁 `lake`、禁联网）。

**不构成剩余依赖（n）**：paper2:350（CLU 历史叙述）、:1974（Mauldin–Williams 对照）、:4440（期刊名 *Ann. Inst. H. Poincaré*）、:4453（`\bibitem{MW}`，仅被 :1974 引用）。

**一句话**：除 R1、R2 外，两篇论文与 Lean 工程对 Bowen / 热力学形式体系 / Mauldin–Urbanski **无其他依赖**；paper1 **零依赖**；Lean 内核**零依赖**（且无相关公理）。

---

## 9. 待证项（未核实，不得当结论）

1. **R1 的 b 路线可行性（推测）**：若在 $s' = 179/256 - 1/2^{k}$ 处重跑同一整数证书仍得正余量，则由 `step_cert_upper_sound` 得 $\dimH F \le s' < 179/256$，可用**闭界包含**给出严格开区间而完全绕开 Bowen。**本任务未运行该验证**（禁改文件、禁 `lake`），$k$ 的取值与余量是否为正**未核到**。论文给的余量为 `1350497164217210109/4931093915000000000000 > 27/100000`（paper2:3546，**tex 原文数值，未复算**）。
2. **Mathlib v4.35.0 是否含 PF 存在性引理**：未核到。查法：在 Mathlib 源树检索 `Perron`/`IsPositive...`/`Matrix...eigenvalue`，或待允许 `lake` 后用 `exact?`。
3. **CLU §2 Theorem 2.3 的确切陈述**：未核到（禁联网）。查法：取 arXiv:1805.11904 原文核对定理编号与假设（强斥性、两字母分支处理）。
4. **`slice_index.csv` 重新生成**：行区间已陈旧（见 §3），非本任务范围，仅记录。

## 10. 建议的下一步（按性价比）

1. 先做 §9-1 的数值试验（最便宜，且能直接消掉 R1 的 Bowen 依赖）：对 $m\in\{2,3,4,5,6\}$、$r\in\{1,m\}$ 在上端点左移 $1/2^{15}$、$1/2^{16}$ 处重跑 `residue_certificate_general_N512.py` 的整数证书，若余量为正即可把“开区间”降为“闭界 + 严格包含”，R1 变为 a。
2. 再做 §9-2：核对 Mathlib 是否已有 PF 存在性，把 R3 从 c 降到 b/a。
3. 最后处理 R2：给配点脚本补一条 Bowen-free 的数值判据（直接对 $\sum_n W_S(2s,n)$ 的收敛/发散做二分，而非对谱半径二分），使数值佐证与内核口径一致；此项不影响任何定理，优先级最低。

---

*本文件所有行号均为 2026-11-24 在 HEAD `f345d60` 上 `rg -n` 实测；所有 Lean 定理名均来自已打开的源文件；未核对到的书目字段（CLU 定理编号、MW 卷页原文、Mathlib PF 引理）已标「未核到」。*
