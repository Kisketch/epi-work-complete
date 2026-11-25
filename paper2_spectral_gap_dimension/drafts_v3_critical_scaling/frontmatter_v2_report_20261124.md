# E7 对照报告：三篇 frontmatter v2 草案（2026-11-24）

**总判断**：三篇英文 frontmatter 草案（标题 + 摘要 ≤200 词 + 诚实声明段）已按任务书 E7 完成并通过全部可执行验收检查；本产出属**起草/整理（AGENTS.md 类别 5：文献核查与复现范畴）**，不含任何新数学结果；文中全部 Lean 口径照录主稿，状态为「**作者自报，未复跑**」（本任务禁 lake，未复跑；编译检查因禁 pdflatex 未执行）。

## 0. 路径约定说明

任务书写产出路径为 `split/…`；本工作区中同批 E6 的产出实际落在 `paper2_spectral_gap_dimension/split/`（`git status` 基线中的 `?? paper2_spectral_gap_dimension/split/slice_index_20261124.csv`、`?? …/slice_concat_check_20261124.md`），且既有 `frontmatter-2X.tex` 家族在该目录的 `src_sections/` 子目录下。故 E7 产出按同一约定写入 **`paper2_spectral_gap_dimension/split/`**：

| 产出 | 路径 | 状态 |
|---|---|---|
| P2A frontmatter | `paper2_spectral_gap_dimension/split/frontmatter-2A-v2.tex` | 新建 |
| P2B frontmatter | `paper2_spectral_gap_dimension/split/frontmatter-2B-v2.tex` | 新建 |
| P2C frontmatter | `paper2_spectral_gap_dimension/split/frontmatter-2C-v2.tex` | 新建 |
| 对照报告 | `paper2_spectral_gap_dimension/split/frontmatter_v2_report_20261124.md` | 新建（本文件） |
| 检查脚本（附属，可复查） | `verification/e7_frontmatter_checks_20261124.py` | 新建 |

既有 `frontmatter-2A/2B/2C.tex`、`frontmatter.tex` 与其余全部既有文件**未改动**（见 §5 git 核对）。

## 1. 逐项对照表

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
|---|---|---|---|---|
| P2A 草案（标题 15 词、摘要 186 词） | 5 起草/整理 | 本地检查全过；Lean 口径=作者自报未复跑 | 主稿 L417–1843 各定理的改写，无新结果 | 本报告 §2、§4 |
| P2B 草案（标题 15 词、摘要 186 词，含占位句） | 5 起草/整理 | 同上；占位句定理**未证**，已明示 | 主稿 L1844–2881 各定理的改写；统一结构字母表理论未成文（拆分方案 §4） | 本报告 §3、§4 |
| P2C 草案（标题 13 词、摘要 200 词，含占位句） | 5 起草/整理 | 同上；占位句定理（T6 临界标度）**未证**，已明示 | 主稿 L2884–4052 各定理的改写；T6 仍为猜想（verification/T6_critical_scaling_conjecture_20261124.md 在库） | 本报告 §3、§4 |

## 2. P2A（谱离散化与精确规范；主稿区块 L417–1843）

- **标题**（15 词）：On the complete spectrum discretization and exact Hausdorff gauges for the convergent denominators of $e$
- **摘要**：186 词（raw token 计数，含宏与模块名；上限 200）
- **摘要声称的定理清单 → 主稿行号**（label 均为本次实际读取行号）：
  - $\{\Lam=0\}=L=\Z+\Z\frac{e+1}{2}$ → thm:class L470；初始谱隙 → thm:gap L483（Layer A 版 thm:spectral L507）
  - 全谱离散化 $\Lam(\R)=\frac14\Z_{\ge0}\cup\{\infty\}$、空隙 $(k/4,(k+1)/4)$ → thm:full-spectrum L537；隙上子集恒定 → thm:sub L578
  - 有限能级集 Hausdorff 维数 0 → thm:finite L679（lem:factorial L634、lem:branch L648）；$\Lam=\infty$ a.e. 且维数 1 → cor:infinite-level L774
  - 次临界维数恰 $1-\alpha$（上下界）→ thm:upper L872 + conj:weight（Prescribed limits, Layer A in Lean）L980；rem:unweighted L856
  - 精确临界规范 $h_k(1/Q_n)=(2k+1)^{-n}$、$\sigma$-有限无穷 $\mathcal H^{h_k}$ 测度、严格子集零测 → thm:gauge L1215 + cor:exact-gauge L1529
  - 任意规范按 liminf 分类 → cor:liminf-gauges L1574；rem:gauge-scale L1637
  - 正能级三分法（二进制字母表、符号余弦坍缩）→ thm:trichotomy L1673（Lean status 段 L1821–1842）
- **审计子集声明（模块名照抄该区块引用，含引用行号）**：`DeltaSign.lean` L436；`EpiFormal/Classification.lean` L500；`SpectralGap.lean` L514 / `EpiFormal/SpectralGap.lean` L601；`EpiFormal/FullSpectrumDiscrete.lean` L608、L1823（15 declarations）；`EpiFormal/DimHCore.lean`+`EpiFormal/DimHFinite.lean` L630；`EpiFormal/GaugeExact.lean` L783、L1457；`QuarterPointFinal.lean` L860；`EpiFormal/UnweightedCorrection.lean` L864；`WeightedFiber.lean`/`WeightedDimHCore.lean`/`WeightedUpper.lean`/`WeightedFinal.lean` L976–977；`EpiFormal/WeightedExactDim.lean` L1185；`EpiFormal/GaugeNull.lean` L1451、L1831；`EpiFormal/GaugeCircle.lean` L1474（53 declarations L1520）、L1718、L1830；`GaugeLiminfComplete.lean` L1628（另 L610）；`EpiFormal/TrichotomyAndPolyExtension.lean` L1834（本篇只取其 8 条 part-(iii) 声明）。联合审计 `Audit.lean` L619（872 declarations across 131 files——已在草案中明示为**全项目口径、非本篇口径**）。
- **内核外声明**：本篇无（草案明写 "No input used by this paper lies outside the Lean kernel"；与主稿四项内核外清单 L4393–4401 不相交）。
- **e+π 免责句**：摘要末句，原文精确串 `does not resolve the open problem of the irrationality of $e+\pi$`（raw 匹配通过）；spin-off 出处补在诚实声明段。
- **companion 句**：文件末行（原文精确串匹配通过）。

## 3. P2B（一般递推与结构字母表理论；主稿区块 L1844–2881）与 P2C（窗口、残差与临界相变；主稿区块 L2884–4052）

### P2B
- **标题**（15 词）：On the general recurrence theory of weighted Diophantine approximation: spectra, gauges, and dimension phase transitions
- **摘要**：186 词。
- **定理清单 → 行号**：有限状态缺陷尾 → thm:finite-state-tail L1854（Lean status L1982–1995；PF 特征向量取为显式假设 L1994–1995）；多项式增长 → lem:poly-growth L2022、lem:poly-lattice L2068、thm:general-rec L2148（Lean 注 L2169–2178）、thm:poly-gauge-trichotomy L2206、cor:poly-exact-gauge L2309、rem:poly-gauge-scale L2327、thm:poly-phase-transition L2344（Lean status L2474–2479）；增长商递推 → thm:growing-rec-spectrum L2581、thm:growing-rec-dim-phase L2670、cor:growing-rec-three-regimes L2780（τ=2 临界边界）、Lean status L2825 起（L2827、L2849）。
- **审计子集声明（含引用行号）**：`EpiFormal/FiniteStateComplete.lean` L1983（12 audited declarations；依赖 `FiniteStateGauge.lean` L1986、`FiniteStateTail.lean` L1987、`FiniteStatePositive.lean` L1988）；`EpiFormal/TrichotomyAndPolyExtension.lean` L2170、L2476（37 declarations）；`EpiFormal/FullSpectrumDiscrete.lean` L2178（r=1 特化）；`EpiFormal/PolyGaugeAndPhaseTransition.lean` L2477（22）；`EpiFormal/PolyWeightedUpper.lean` L2478（1）；`EpiFormal/PolyWeightedLower.lean` L2479（8）；`EpiFormal/GeneralGrowingRec.lean` L2827（21）；`EpiFormal/GeneralGrowingDim.lean` L2849（29）。
- **内核外声明**（照录主稿摘要 L157–163 与 §verification L4393–4397 口径、限本篇）：Perron–Frobenius 特征向量存在性输入（passed explicitly as a hypothesis）。
- **占位句**：`[Unified structural-alphabet theorem: to be inserted]` 位于摘要「统一理论位置」——两条族（多项式/增长商）与有限状态结果陈述之后、Lean 验证句之前，前导语 "Beyond these two families:"；raw 精确匹配通过。该定理**未证**（拆分方案 §4 增量①，T2 施工图），草案与诚实声明段均明示其仅为占位。

### P2C
- **标题**（13 词）：On window constraints, digit residues, and critical phase transitions for modular continued fractions
- **摘要**：200 词（恰好达标）。
- **定理清单 → 行号**：Hermite 窗约束维数 → thm:windows L2890（prescribed parity 恰 1、bounded/prescribed increments 恰 1/2）；短窗 a.e. 显式常数 $(1-e^{-1})/160$ → thm:short-ae L3096；发散窗计数 → 维数 1 + Lebesgue 零测 → thm:no-short-dim L3219（rem:windows-lean L3324，Lean 明细 L3329–3333）；digit residues mod 4 → thm:residues L3351；一般模数三明治/传递算子/证书化 bracket → thm:residues-general L3556（rem:residue-kernel L3633：closed brackets 内核化 L3636–3652，**开区间严格性未形式化 L3653–3655**）；预解恒等 + 全局严格分离 + 两项渐近 → thm:residues-asymptotic L3687；多残差相变/三项 Euler–Mascheroni/超临界率 → thm:multi-residue-asymptotic L3823；第四项启发式**未证** → rem:fourth-term L3989；区块收尾 Lean status L4049–4051。
- **审计子集声明（含引用行号）**：13 个 window 模块 `WindowMobiusCount.lean`、`NoShortDimCount.lean`、`WindowTreePrune.lean`、`WindowAsympThresh.lean`、`WindowFrostmanDischarge.lean`、`WindowPaperScale.lean`、`WindowCFRealize.lean`、`WindowCFBridge.lean`、`WindowNoShortCFRealize.lean`、`WindowPrescribedCFRealize.lean`、`WindowBoundedUpper.lean`、`WindowShortAe.lean`、`WindowShortAeRealize.lean`（L4050；明细行 L3329/3331/3332）；残差模块 `EpiFormal/ResidueModGeneral.lean`、`EpiFormal/TransferOperatorDim.lean`、`EpiFormal/ResidueAsymptotic.lean`、`WindowAndResidueCore.lean`（L4051）；证书模块 `EpiFormal/ResidueCertGenSound.lean` L3639、`EpiFormal/ResidueCertGenBase.lean` L3640、`EpiFormal/ResidueCertTable.lean` L3652、L4051；`EpiFormal/ResidueMultiAsymptotic.lean` L4051（24 public theorems，独立审计于 `AuditResidueMultiAsymptotic.lean` L4051）。`Audit.lean` L3333（872 declarations，同样明示全项目口径）。Python 证书脚本 `residue_certificate_general_N512.py`（L4051）为非 Lean 证书，草案如实标注。**注**：`AuditResidueCert.lean`（27 declarations）在主稿摘要 L153–154 被引，但在 P2C 区块 L2884–4052 内未被引用，故按「照抄该区块」规则未列入子集——主会话审校时可自行决断是否补入。
- **内核外声明**：①开区间严格性（Python 整数证书 + 压力形式体系；closed brackets 内核化）——区块内依据 rem:residue-kernel L3653–3655，全稿口径见 L4397–4399；②临界边界 $s_0(S)=1/2$ 渐近率与超临界首项精确常数——依据 §verification L4399–4400（该项在 P2C 区块内无行级声明，系全稿四项清单口径，报告如实注明出处层级）；③第四项 collocation 值为启发式未证（rem:fourth-term L3989）。
- **占位句**：`[Critical scaling theorem: to be inserted]` 位于摘要临界情形位置（"…supercritical rate $\Theta(m^{-2s_0(S)})$; at the critical boundary $s_0(S)=1/2$," 之后）；raw 精确匹配通过。该定理**未证**（T6，主会话保留项）。

## 4. 设计决策（供主会话审校）

1. **审计子集句的位置**：按任务书③写于每篇 `\section*{Honesty statement and formal verification}` 首句；摘要的验证句照录主稿 L154–156 句式（"machine-checked in Lean~4 using only the base axioms propext, Classical.choice and Quot.sound"），但**只作本篇口径的定性声明并指向诚实声明段**——因 P2C 审计子集 20+ 个模块若全列摘要必超 200 词；三篇设计一致，主会话若要求把模块列表搬进摘要需重排词数。
2. **全项目计数隔离**：三篇草案均明写 `Audit.lean` 的 872/131、937/134、344 等 counts 是 project-wide、非本篇口径（拆分方案 §4「每篇 Lean 声明只写本篇覆盖的审计子集」）。草案未引 937/134/344。
3. **共享模块的归属**：`FullSpectrumDiscrete.lean`、`GaugeExact.lean`、`TrichotomyAndPolyExtension.lean`、`ResidueModGeneral.lean`、`TransferOperatorDim.lean` 等在多个区块被引，故按区块引用如实跨篇出现（P2A 只取 TrichotomyAndPolyExtension 的 8 条 part-(iii) 声明并已注明）。
4. **占位句语义**：两处占位句按任务书原文逐字写入，且诚实声明段明示「未证、仅为占位」，防止把条件/未成文结果读成已有结论（AGENTS.md 红线）。
5. **入轨方式**：三文件沿用既有家族约定（自带 `\title` + `\begin{document}\maketitle`，无 `\end{document}`，供 wrapper `\input`）；宏 `\R,\Z,\ee,\Lam,\dimH` 依赖共享 `preamble.tex`（与既有 frontmatter-2X.tex 同约定）。**编译验证未执行**（pdflatex 禁令）——验收要求的仅是花括号配对检查，已过。

## 5. 验收检查记录（全部实际运行）

- **命令**：`python verification\e7_frontmatter_checks_20261124.py`（脚本内容见该文件；检查：标题词数、摘要词数、忽略 `\{ \}` 后的花括号配对、两处占位句 raw 精确匹配、e+π 句与 companion 句 raw+空白归一化匹配）。最终输出：
  - 2A：title_words=15；abstract_raw_token_count=186；braces final_balance=0 min_balance=0；placeholder_2B/2C=False/False（本篇不应含，正确）；epi raw=True；companion raw=True
  - 2B：title_words=15；abstract_raw_token_count=186；braces 0/0；placeholder_2B_exact=True；epi raw=True；companion raw=True
  - 2C：title_words=13；abstract_raw_token_count=200；braces 0/0；placeholder_2C_exact=True；epi raw=True；companion raw=True
- **git 核对**：写作前基线 `git status --porcelain=v1` 共 36 行全部 `??`；终检 `total_lines=40`、`modified_or_deleted_lines=0`（新增 4 行 = 三个 v2 tex + 检查脚本），即**无既有文件被修改或删除**。
- **素材读取**：主稿摘要 L107–166、四项内核外清单 L4393–4401、三区块内全部定理 label 行号与 `.lean` 引用行号均来自本次对 `paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex` 的实际读取（read/grep 输出），非记忆转述。

## 6. 未核到 / 未完成

- **Lean 复跑未做**：`lake build` 与 `#print axioms` 均被禁令排除；草案中所有 "machine-checked / Layer A / base axioms only / zero sorryAx" 字样一律为**主稿自报口径的照录**，主会话引用时应保持「作者自报，未复跑」标记（AGENTS.md §5）。
- **编译未做**：pdflatex/tectonic 禁令；三文件只做了花括号配对与结构检查，未验证 LaTeX 实际可编译（宏依赖 preamble.tex 的可用性按既有家族约定假定）。
- **`AuditResidueCert.lean` 归属**：见 §3 P2C 注——区块内未引，未列入子集，留主会话决断。
- **E10 相关**：主稿摘要自身口径（2 处→4 处）的补丁属 E10 任务，本任务未触碰主稿。
