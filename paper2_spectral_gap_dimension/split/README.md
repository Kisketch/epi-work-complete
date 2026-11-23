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
* 2A 引言裁剪：`intro_trim_2A.py` 从 `intro-shared` 确定性生成 `intro-2A.tex`（237→169 行）：删 finite-state-tail 两句、poly+growing 整块、窗口/残差整块、P11 混装块，贡献清单改写为 2A-only；S5/S16 改写暂缓留原样。
* 编译：2A 24 页 / 2B 15 页 / 2C 22 页，`pdflatex`（track 目录为 CWD）均 0 error。
* 引用审计（`undef_ref_audit.py`，两遍编译后）：2A 仅剩 1 个（`sec:poly-rec`，方案A：定稿改写归属句）；2B 归零——`intro-2B.tex`（66 行，`intro_trim_2B.py` 确定性生成，新写句标 `[2B-NEW]`）+ `prereq-2B.tex`（6 个 2A 背景事实复述备查，证明归姊妹篇）；2C 维持 20 个待处理。
* r=1 分析留痕：gauge-core 内 `(iii)` 陈述+证明已完整自足；`sec-poly` 无独立 $r=1$ 专段（`general-rec(i)` 与 `poly-gauge-trichotomy(iii)` 互引且为 2B 标题定理，整段搬会断 2B 主干），故不动数学、只改归属句。另正文审计口径双重记账（`TrichotomyAndPolyExtension` 在 gauge-core 记 8 条、在 sec-poly 记 37 条）实为同一文件前后两部分分属两轨，定稿时各自准确表述。
* 中间修正：gauge 子片初版 `Out-File utf8` 带 BOM 致 +9 字节，已二进制重切，13 片拼接 253919B SHA 与原版一致。

## 七、它没做到（截至 v4）

* 三 draft 仍为 `\input` 组装草案；2A 引言已裁剪至 2 个已知体内非自足点，2B/2C 引言改写未动；交叉引用跨轨未定义（编译 0 error，警告预期内）。

* 三 draft 仍为 `\input` 组装草案，非独立撰写；2B/2C 标题摘要为新写占位，交叉引用跨轨未定义。
* 未复跑 `lake build` 与 Python 证书；Lean 937 与扩展验证记作者自报 + 日志在列。
* `e+π` 无理性仍开放，拆分不构成原问题进展。

## 八、下一步（全自动继续）

1. ~~三轨未定义引用清单~~已完成；2A 剩余 `sec:poly-rec` 1 个已有方案A决议（定稿改写归属句），草案阶段保留。
2. 2B/2C 引言改写：2B 按裁剪表改写（主语换 $A_j$ + 自版三分法 + 跨篇引用 2A 基座策略先定）；2C 需先补 $S_k/d_j$ 记号段。
3. 审计口径：`TrichotomyAndPolyExtension` 双重记账在 2A/2B 定稿时各自准确表述 8 条 vs 37 条。
3. 台账与映射文档口径同步后提交推送。
