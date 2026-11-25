# 论文二拆分总览（原版冻结 + 2A/2B/2C/S 四轨）

> 日期：2026-11-23｜基线：`1e91028`｜原则：原版零丢失、拆分版全引用回原版、每处留痕。
> 一句总判断：原版 50+ 页 33 标签已冻结两份（`ed61a92` 213564B、`1e91028` 253919B+PDF 841123B），拆分只做新增目录 `split/`，不动原版正文。

## 一、原版冻结（已落盘）

| 冻结件 | 路径 | 规格 |
|---|---|---|
| 原版 ed61a92 | `paper2_spectral_gap_dimension/historical_versions/paper2_integrated_v20261122_ed61a92.tex` | 213564B，33 标签之前版 |
| 原版 1e91028 | `paper2_spectral_gap_dimension/historical_versions/paper2_integrated_v20261123_1e91028.tex` + 同名 `.pdf` | 253919B / 841123B，含新增两节 |

## 二、四轨划分（本次只建骨架，不复制正文）

| 轨道 | 目录 | 纳入节与标签 | 目标期刊相 |
|---|---|---|---|
| 2A 主文顶刊 shot | `split/2A_core_gauge_trichotomy/` | `sec:class/spectrum/finite-levels/weights/gauge` 前半：`thm:class/gap/spectral/full-spectrum/sub/finite/upper/conj:weight/gauge/trichotomy` + `cor:exact-gauge/liminf-gauges/infinite-level` + `lem:factorial/branch` | Annals/Inventiones/JAMS 级主定理：精确规范 + 三分法二值普适基 2 |
| 2B 一般理论 | `split/2B_general_theory/` | `sec:poly-rec` + `sec:growing-rec`：`lem:poly-growth/lattice`、`thm:general-rec/poly-gauge-trichotomy/poly-phase-transition/growing-rec-spectrum/growing-rec-dim-phase` + `cor:poly-exact-gauge/growing-rec-three-regimes` | Duke/Adv Math 级一般递推理论：`1/c` 谱 + `1-α/r` + `growing` 三 regime |
| 2C 窗口残差与有限状态 | `split/2C_windows_residues_finstate/` | `sec:finite-state-tail` + `sec:windows-residues` 全：`thm:finite-state-tail/windows/short-ae/no-short-dim/residues/residues-general/residues-asymptotic` + `tab:residues-general/residues-asymptotic` | 专业期刊副文：转移算子 + 整数证书 + 预解恒等式 |
| S 补充 | `split/S_supplement/` | `sec:num/sec:verification` + 全部审计日志 + 证书 `.json/.log` + Lean 双轨对照 | 投稿 supplement，不占主文篇幅 |

## 三、详细分类（33 标签按节归类，来自只读盘点）

* class (390–477)：`thm:class`、`thm:gap`（2）
* spectrum (478–594)：`thm:spectral`（cor 环境）、`thm:full-spectrum`、`thm:sub`（cor 环境）（3）
* finite-levels (595–826)：`lem:factorial`、`lem:branch`、`thm:finite`、`cor:infinite-level`（4）
* weights (827–1176)：`thm:upper`、`conj:weight`（theorem 环境，conj 前缀）（2）
* gauge (1177–1968)：`thm:gauge`、`cor:exact-gauge`、`cor:liminf-gauges`、`thm:trichotomy`、`thm:finite-state-tail`（5）
* poly (1969–2500)：`lem:poly-growth`、`lem:poly-lattice`、`thm:general-rec`、`thm:poly-gauge-trichotomy`、`cor:poly-exact-gauge`、`thm:poly-phase-transition`（6）
* growing (2501–2813，新增）：`thm:growing-rec-spectrum`、`thm:growing-rec-dim-phase`、`cor:growing-rec-three-regimes`（3）
* windows-residues (2814–3702，末子节新增）：`thm:windows`、`thm:short-ae`、`thm:no-short-dim`、`thm:residues`、`thm:residues-general`、`tab:residues-general`、`thm:residues-asymptotic`、`tab:residues-asymptotic`（8）

命名注意：`thm:spectral`、`thm:sub` 实为 corollary 环境；`conj:weight` 实为 theorem 环境；`thm:general-rec`/`thm:poly-phase-transition` 标签跨行定义。

## 四、Lean 精准映射（2026-11-23 声明级已补）

* 总数：134 文件 = 132 子模块 + `EpiFormal.lean` + `Audit.lean`；`Audit.lean` 937 行 `#print axioms`（932 依赖 + 5 零公理）；`EpiFormal.lean` 132 import（L1–132，连续无重，`Basic` 为占位 stub，数学模块实 131）。
* 新增 65 条连续位于 `Audit.lean` L1105–1169：`ResidueAsymptotic` 15 条（L1105–1119）+ `GeneralGrowingRec` 21 条（L1120–1140）+ `GeneralGrowingDim` 29 条（L1141–1169）；64 条基础三公理 + 1 条 `metalQ_one_eq_fib` 仅 `[propext, Quot.sound]`；零白名单；本轮未复跑，按纪律记作者自报 + 日志在列。
* 新三文件位置：`EpiFormal.lean` L88–90（`ResidueAsymptotic/GeneralGrowingRec/GeneralGrowingDim`，夹于 `FiniteStateComplete` L87 与 `AdjacentWitness` L91 之间）。
* 四轨文件级分组（132 已程序化校验无重无漏）：2A 21（Gauge×4 + Classification + SpectralGap + FullSpectrumDiscrete + DimHCore/Finite + Weighted×8 + QuarterPoint×3 + UnweightedCorrection）；2B 6（Poly×3 + TrichotomyAndPolyExtension + GeneralGrowingRec/Dim）；2C 61（Window×44 + Cylinder×7 + NoShortDim×2 + FiniteState×4 + HermiteResiduePeriod + ResidueModGeneral/Asymptotic + TransferOperatorDim）；共用基座 5（Basic stub + Axioms + Measure + EulerConvergents + ThresholdAttained）；论文一专属 39 不进拆分。21+6+61+5+39=132。
* 必须按声明切的 3 处：`FullSpectrumDiscrete`（2A 主 + 一般 `(cj+d)` 归 2B）、`TrichotomyAndPolyExtension`（前半 L48–638 系 2A `thm:trichotomy(iii)` 8 条，后半归 2B）、`WindowAndResidueCore`（2C 主，被论文一 §3 复用，2C 以外部基座引用不复制）。
* 依赖链：`ResidueAsymptotic → TransferOperatorDim`；`GeneralGrowingDim → GeneralGrowingRec → TrichotomyAndPolyExtension/PolyGaugeAndPhaseTransition/GaugeCircle`；`GeneralGrowingDim → WeightedExactDim`（2B 对 2A 真实依赖，拆分后 2B 需声明引用 2A 基座）。
* 口径问题 4 处（只记录不改文件，以免污染审计）：Basic 占位应改述 131+1；`DirichletDivisor` 头注释过期（实已 import L22 + 审计 13 条）；`FiniteStateTail` 命名空间实为 `FiniteStateGauge`；新增 65 条缺合并留痕注释块。

* 总数：134 文件 = 132 子模块 + `EpiFormal.lean` + `Audit.lean`；`Audit.lean` 937 行 `#print axioms`；`EpiFormal.lean` 132 import（100% 覆盖）。
* 新增三文件已确认存在：`GeneralGrowingDim.lean` 177149B、`GeneralGrowingRec.lean` 327791B、`ResidueAsymptotic.lean` 115873B。
* 分组初判：Window 44 → 2C；`Poly*/GeneralGrowing*/Gauge*/Trichotomy/FullSpectrum/Weighted/FiniteState` → 2A/2B 按上表切分；`Golden*/Residue*/Transfer*` → 2C；其余 57 Other 待声明级归属。声明级 `定理—Lean文件—审计行号` 对照表见 `verification/论文二拆分分类与Lean精准映射_20261123.md`（待补）。
* 双轨原则：正文数学自足，Lean 对应只在附录/S 补充中并列，不进主文篇幅。

## 五、新增两节一句话（只读盘点原文）

* `sec:growing-rec`：任意增长商 `A_j→∞` 三项递推的谱 `Z_{\ge0}∪{∞}`、零层 TFAE、三路分裂与 `γ_sup` 维数相变 + 三 regime 实例（含 `A_j=2^{2^j}` 临界 `τ=2`）。
* `sec:residues-asymptotic`：金属均值预解恒等式 → 全 `m≥2` 严格分离 + 倒 Fibonacci 二项渐近（`C_1=ψ_Fib`）；`verify_paper2_extensions.py` 120 位 mpmath 全 PASS（`m≤6` 超额比为负系小区间渐近代数失效，正文只报 `m=5000`，另日志 `~3.20000` 系笔误）。

## 六、接线进展（2026-11-23 wiring v2→v4，原版一字未动）

* 共享切片新增：`preamble.tex`（原 L1–35）、`frontmatter.tex`（L36–389）、`refs.tex`（verif 切片 bibliography 块）、`intro-shared.tex`（frontmatter 中 abstract 之后 237 行）。
* 三轨独立摘要：`frontmatter-2A/2B/2C.tex`（忠实原稿压缩，均声明 `e+π` 开放；作者占位未动）。
* 2A 定稿打磨：`frontmatter-2A.tex` 摘要重写为投稿标准（动机句 + 谱/规范/三分法 + Lean 一句 + `e+π` 开放声明）；D6 将 CMMS/MEA 对比压缩为指针句（详版留 S32），已折叠进 `intro_trim_2A.py` 行号操作，再生字节一致。
* 2C 引言改写：`intro_trim_2C.py` 按行号生成 `intro-2C.tex`（237→73 行）：新开篇 + S7/S8/S9（含记号段）+ S17 + 内联 Setup 子集 + S29 + 2C-only 贡献；其余整块删。
* 形式化推进（截至本提交）：`ResidueRpowBridge_Draft.lean`（包络引理两条，DRAFT 未编译）+ `emit_cert_data_41179.py`（确定性生成器）+ `ResidueCertData41179_Draft.lean`（1.8MB 数据 + h_hi/hcert 单 decide 义务，DRAFT 未编译）。注意目标已随 N512 前移：形式化上界为 179/256 = 358/512（严于正文 359/512）；2C 定稿表同步更新 N512 四处收紧值。编译验证待串行构建完成后执行。
* 背景复述保真度：`patch_prereq_fidelity.py` 已执行（`thm:gauge` 补 $g_\beta$ 两向结论，`cor:liminf-gauges` 展开三态），2B/2C 重编译 0 error、引用归零。
* N512 证书：10/10 区间收至 1/512 地板（4 处收紧：m=2,3,4,6 的 r=1 侧各丢一格已回收）；`tab:residues-general` 原表未动，2C 定稿时更新。
* 编译：2A 24 页 / 2B 15 页 / 2C 20 页，`pdflatex`（track 目录为 CWD）均 0 error。
* 引用审计（`undef_ref_audit.py`，两遍编译后）：三轨全部归零。2A 的 `sec:poly-rec` 已用方案A彻底消解（`derive_spectrum_2A.py` 生成 `sec-spectrum-2A.tex` 派生切片：仅改写审计归属段，删 `and Section` 跨轨引用；原切片冻结，diff 仅该段）。
* r=1 分析留痕：gauge-core 内 `(iii)` 陈述+证明已完整自足；`sec-poly` 无独立 $r=1$ 专段（`general-rec(i)` 与 `poly-gauge-trichotomy(iii)` 互引且为 2B 标题定理，整段搬会断 2B 主干），故不动数学、只改归属句。另正文审计口径双重记账（`TrichotomyAndPolyExtension` 在 gauge-core 记 8 条、在 sec-poly 记 37 条）实为同一文件前后两部分分属两轨，定稿时各自准确表述。
* 中间修正：gauge 子片初版 `Out-File utf8` 带 BOM 致 +9 字节，已二进制重切，13 片拼接 253919B SHA 与原版一致。

## 七、它没做到（截至 v6）

* 三 draft 为 `\input` 组装草案（引言/背景/归属已闭合，引用全零）；2B/2C 新写句与背景复述待人审措辞。
* Lean 主库已串行构建 132/132；Python 证书已全部独立复跑；`Audit.lean` 审计日志复跑待执行。
* `e+π` 无理性仍开放，拆分不构成原问题进展。

## 八、下一步（全自动继续）

1. ~~三轨未定义引用清单~~、`~~2B/2C 引言改写~~`、`~~2A 归属句~~`已完成（引用全零）；S 补充轨已组装。
2. 等待：证书数据单 decide 核查（后台运行中）→ 全量 `lake build` → Audit 审计复跑（届时 937 由作者自报转已复跑）。
3. Draft 入口存在性已验证（21/6/61）；审计口径双重记账定稿时各自表述；组装 358/512 定理待数据核查通过后开工。

## 九、2026-11-23 同步进展（`7ece3b9` → 最新版，只增不减）

* **7ece3b9 冻结快照**：主稿 [`paper2_integrated_v20261123_7ece3b9.tex`](../historical_versions/paper2_integrated_v20261123_7ece3b9.tex)（256,402 字节 LF，对应工作区 CRLF 260,549 字节）已冻结归档至 `historical_versions/`，与 `ed61a92`、`1e91028` 同目录留存。
* **$N=512$ 证书、BLR 对比与 Colab 复现**：`ResidueCertGen/` 与 [`ResidueCertTable.lean`](../../epi_formal/EpiFormal/ResidueCertTable.lean) / [`AuditResidueCert.lean`](../../epi_formal/AuditResidueCert.lean)（27 条，仅基础公理）已在 Lean 内核闭环 `tab:residues-general` 的全部 20 条闭界与 5 条严格分离（开区间严格性仍由 `residue_certificate_general_N512.py` 与 Bowen 压力公式共同支撑）；`rem:poly-BLR` / `rem:growing-BLR` 与 Colab 独立全量复现说明（937/937 + 27/27）已并入主切片。
* **多残差推广（`thm:multi-residue-asymptotic`）合入 2C 与主文**：`src_sections/sec-resasymp.tex` 新增 §7.5 `sec:multi-residue`（[定理 `thm:multi-residue-asymptotic`](src_sections/sec-resasymp.tex) 与 [数值佐证表 `tab:multi-residue-asymptotic`](src_sections/sec-resasymp.tex)），对应 `ResidueMultiAsymptotic.lean`（5,039 行，Part 1–6）与 `AuditResidueMultiAsymptotic.lean`（24/24 条仅基础公理）；同步更新 `sec-preface.tex`、`frontmatter.tex`、`intro-shared.tex`、`frontmatter-2C.tex`、`intro-2C.tex`、`preamble.tex`、`sec-num.tex`、`sec-verification.tex`。
* **切片逐字节一致性与三轨编译结果**：11 片拼接与 [`paper2_spectral_gap_dimension.tex`](../paper2_spectral_gap_dimension.tex) 逐字节一致（`279,145` 字节）；`pdflatex` 洁净重编主论文 **63 页**、2A **24 页**、2B **15 页**、2C **24 页**，0 错误 / 0 `Overfull \hbox`；[`undef_ref_audit.py`](undef_ref_audit.py) 与 [`undef_ref_audit.log`](undef_ref_audit.log) 确认 2A / 2B / 2C 三轨 **0 未定义引用、0 未定义文献**（S 补充轨单独编译时的主文标签引用按定位保留于 `S_supplement/build/paperS_draft.log`）。
* **诚实边界**：$e+\pi$ 无理性仍开放；临界线 $s_0(S)=1/2$ 速率与超临界阶段精确主导常数尚未解决。

## 十、2026-11-24 / 2026-11-25 同步进展（`rem:fourth-term` 与文献基准补全）

* **启发式四阶项与二次复建（2026-11-24）**：[`sec-resasymp.tex`](src_sections/sec-resasymp.tex) 与 [`sec-verification.tex`](src_sections/sec-verification.tex) 同步加入 Remark `rem:fourth-term`（非严格数值佐证，明确标明非定理）及第二次独立克隆审计说明。
* **外部基准引文与 DOI 规范化（2026-11-25）**：经 [`patch_evidence_citations_20261125.py`](../patch_evidence_citations_20261125.py) 同步更新 `sec-preface.tex`、`sec-resasymp.tex`、`sec-num.tex`、`sec-verification.tex` 与派生切片 `intro-2A.tex`、`intro-2B.tex`、`intro-2C.tex`、`refs.tex`，增补 `Hensley1996`（含勘误 `10.1006/jnth.1996.0107`）、`JP2018`、`CLN2026`、`CLUW2024`、`Brown2026`、`TTWW2026`、`BW2025`。
* **PR #2 合流、2A 投稿版与文献全并集（2026-11-25 续）**：合并 PR #2 的 `patch_novelty_wording_20261125.py`（增补 `DFSU`/`MU96`/`Good41`/`HU02`/`Hensley92`/`DLMF` 并严谨改写先例定位）、`patch_blr_baker_fix_20261125.py` 与 `derive_2A_pub.py`（为 2A 派生去除 Lean 审计文字的 `*-2Apub.tex` 与 `refs-2Apub.tex`）；经 [`patch_unify_20261125.py`](../patch_unify_20261125.py) 完成 `sec-preface.tex` / `intro-2C.tex` 并集整合、清洗全部新入 DOI `\allowbreak`、修正 `sec-resasymp.tex` 显示公式 `m^{-1-\varepsilon}` 笔误并同步 [`slice_index.csv`](src_sections/slice_index.csv)（11 切片合计 `289,499` 字节、`4,574` 行、`28/28` 全引用）。
* **重编实测**：主稿 **66 页**、2A（`*-2Apub`）**21 页**、2B **16 页**、2C **26 页**（0 错误 / 0 `Overfull \hbox` / `undef_ref_audit.py` 0/0）、S **8 页**（0 未定义文献引文）。
* **实验线与投稿信草稿**：`T6` 临界标度 `v3` 与两主稿装配试验另行隔离归档于 [`../drafts_v3_critical_scaling/README.md`](../drafts_v3_critical_scaling/README.md)（不改动标准 11 切片真源）；`2A+2B` / `2C` 诚实边界英文 Cover Letter 草稿见 [`cover_letters_2AB_and_2C_draft_20261125.md`](cover_letters_2AB_and_2C_draft_20261125.md)。
