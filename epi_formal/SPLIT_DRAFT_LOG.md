# Lean 三轨入口草案日志（SPLIT_DRAFT_LOG）

**日期**：2026-11-23｜**状态**：草案，未进 `Audit.lean`、未参与 `lake build EpiFormal`、未经公理审计
**一句总判断**：三入口按名单机械抽取完成（21/6/61，合计 88 个模块 = 主入口 132 条 import 中的 88 条），
import 计数与主入口行号逐条可查；但**转正条件未满足**——3 处声明级边界待处理（2 处跨轨强制切分、1 处同轨备案），
88 个模块中仅 26 个在模块头出现 `§` 节号，另 1 个（`WindowShortAe`）只有 tex 行锚（L2610–2726），
合计 **27/88 有锚**，其余 61 个标「未核到」。

---

## 1. 三入口

| 入口 | 路径 | import 数 | 覆盖范围 |
|---|---|---|---|
| 2A | `epi_formal/EpiFormal2A_Draft.lean` | **21** | 谱 / 维数 / 规范测度核心层 |
| 2B | `epi_formal/EpiFormal2B_Draft.lean` | **6** | §6.3 多项式与一般增长递推扩展轨 |
| 2C | `epi_formal/EpiFormal2C_Draft.lean` | **61** | §7 窗口 / Cylinder / 有限状态 / 剩余类 |
| 合计 | — | **88** | 主入口 L1–132 的 132 条 import 中 88 条 |

**抽取规则**（可复现）：以 `epi_formal/EpiFormal.lean` L1–132 为唯一来源，按任务给定名单逐名匹配，
import 别名与主入口一致（`EpiFormal.<Module>`），顺序按主入口行号递增。
核验结果：88 个目标模块在 `epi_formal/EpiFormal/` 下**全部存在**（`Get-ChildItem` 全量比对，无缺名、无多余）；
三入口 import 去重后计数仍为 21/6/61（无重复行）。

未进三入口的 44 条主入口 import 包含：`Basic`（stub）、`DirichletDivisor`（注释过期）、
论文一黄金比 / Padé / Alekseyev / 逃逸与谱基础等模块——本次任务范围外，未处理。

---

## 2. 三处声明级切分点

| # | 文件（主入口行） | 分区（文件内 `/-! ##` 行） | 内容 | 归口 | 现状 / 切分动作 |
|---|---|---|---|---|---|
| 1 | `FullSpectrumDiscrete`（L7） | 第一部分 L42 / 第二部分 L124 | 第一部分：一般 `(cj+d)` 递推差商逼近；第二部分：整数离散刚性、等距谱隙排除、Euler 特化与 `k/4` 三分法 | 第一部分 → **2B**；第二部分 → **2A** | **跨轨强制**。草案 2A **整文件引用**；2B 当前未 import 本文件（无回边），切分后第一部分下沉独立模块（建议 `GeneralLinearRec`），2B 引之 |
| 2 | `TrichotomyAndPolyExtension`（L15） | 第一部分 L51 / 第二–七部分 L640、L986、L1912、L2287、L2877、L3085 | 第一部分：Theorem 16(iii)（Euler 收敛子有符号陪集坍缩）；第二–七部分：§6.3 多项式增长、`lem:poly-lattice`、`thm:general-rec`、相变三分 | 第一部分 → **2A**；第二–七部分 → **2B** | **跨轨强制**。草案 2B **整文件引用**并在头部注明「前半归 2A」；2A 当前未 import 本文件（无回边）。切分后第一部分（L51–639）下沉（建议 `EulerSignedTrichotomy`）归 2A |
| 3 | `GaugeExact`（L11） | 第一部分 L42（§4）/ 第二部分 L276（§6 Theorem 13） | §4 补集 Lebesgue 满测度与维数 1；§6 临界规范测度、σ-有限分解、`L`-平移不变 | **均为 2A** | **同轨节级备案**，草案整文件引用、**不切分**；仅登记为后续节级边界，若 §4 单独成轨再切 |

判定依据：三处均由文件内显式 `/-! ## 第…部分` 标记支撑（行号见上表），非按内容推测。
其余 85 个模块未见「一份文件内混两轨」的证据，按整文件切分。

---

## 3. 三口径备注

### 口径 1：`Basic` 是空 stub

`epi_formal/EpiFormal/Basic.lean` 全文 1 行：`def hello := "world"`。
主入口 L4 `import EpiFormal.Basic` 属**空 import**，无任何声明可用。
后果：三入口**均不 import `Basic`**（避免虚依赖被误当“基础层”）；分轨评估时不得把 `Basic` 计入任何轨的依赖图。

### 口径 2：`DirichletDivisor` 的注释已过期

`epi_formal/EpiFormal/DirichletDivisor.lean` 文件头写「隔离工作，**不合入** `EpiFormal.lean`/`Audit.lean`」，
但主入口 **L22 已 `import EpiFormal.DirichletDivisor`**：注释与事实冲突，属**过期注释**。
后果：该文件现为论文一 triage #1（`prop:dirichlet-divisor` 隔离核验），本次三轨**均不含它**；
转正时若要引用其结论，须先修正头注释，避免下游误判其「不在主工程」。

### 口径 3：`FiniteStateTail` 的命名空间与文件名不一致（三口径）

| 口径 | 值 |
|---|---|
| 文件名 | `FiniteStateTail.lean` |
| 命名空间 | `FiniteStateGauge`（`EpiFormal/FiniteStateTail.lean` L7） |
| 文档 / 任务命名 | 「FiniteStateTail」 |

后果：按**文件**切分时，声明归属落在 `FiniteStateGauge` 命名空间；引用必须写 `FiniteStateGauge.*`，
不可按文件名写 `FiniteStateTail.*`。且 `FiniteStateGauge.lean` 与 `FiniteStateTail.lean` 共用同一命名空间，
两文件同属 2C 故本次不产生跨轨歧义；但若未来把二者拆到不同轨，必须做**声明级**归属表，不能按文件切。

---

## 4. 依赖核验（脚本抽取，非人工推断）

抽取方法：逐文件解析 `^import EpiFormal\.(\w+)$`，全仓 214 条 in-repo 边；按三轨归属分组统计跨组边。

| 方向 | 边数 | 明细 |
|---|---|---|
| 2B → 2A | 7 | `PolyWeightedUpper→WeightedPhase`、`PolyGaugeAndPhaseTransition→{GaugeCircle, GaugeLiminfComplete, WeightedExactDim}`、`TrichotomyAndPolyExtension→GaugeExact`、`GeneralGrowingRec→GaugeCircle`、`GeneralGrowingDim→WeightedExactDim` |
| 2C → 2A | 5 | `FiniteStateTail→GaugeLiminfComplete`、`FiniteStateComplete→GaugeLiminfComplete`、`FiniteStateGauge→GaugeCircle`、`HermiteResiduePeriod→Classification`、`NoShortDimRatio→Classification` |
| 2A → 2B/2C | **0** | 2A 为闭合底层 |
| 2C → 2B | **0** | 2C 不触 2B |
| 2B → 2C | **0** | 2B 不触 2C |

**2A 的对外依赖**：2A 不是只依赖 Mathlib，它透传依赖主入口 5 个**非三轨**模块：
`Alekseyev`(L92)、`EulerConvergents`(L105)、`Measure`(L108)、`MeiburgConvergence`(L110)、`ThresholdAttained`(L125)。
这 5 个模块的归属未决，是 2A 冻结的阻塞项（记录在 2A 草案 §2.1）。

**2C 内部耦合**：残差链（`ResidueModGeneral` + `WindowThickening → TransferOperatorDim → ResidueAsymptotic`）
与窗口链在 `WindowThickening` 交汇，故 2C **不可**再拆成窗口/残差两个入口。

---

## 5. 验证状态（诚实记录）

| 检查 | 结果 |
|---|---|
| 88 个模块存在性 | **通过**（全量目录比对） |
| 三入口 import 计数 21/6/61（去重后） | **通过**（脚本计数） |
| `lean --version`（PATH 上裸 lean） | **通过**：Lean 4.36.0, commit 611c117 |
| 项目 toolchain | `epi_formal/lean-toolchain` / mathlib rev `v4.35.0` —— 与 PATH 上 4.36.0 **不一致**，故任何真实构建须走 `lake env lean`，不得用裸 `lean` |
| `lake env lean --version` | **未完成**：触发 `mathlib: materializing new dependency`（拉取 `56a0058…`），按任务要求「不跑重耗时」**已中止**；未产生版本输出 |
| `lake build` | **未运行**（按要求跳过） |
| 三入口语法编译验证 | **未做**：无 toolchain 环境即无法验证；草案文件仅保证 import 行与注释块结构，**不声称可编译** |
| 公理审计 | **未做**（草案未进 `Audit.lean`） |

未改动面（`git status --porcelain` 实证）：仅新增 3 个 untracked 文件；
`epi_formal/EpiFormal.lean`、`epi_formal/Audit.lean`、`epi_formal/EpiFormal/*.lean`（132 个子模块）
**零改动**；`paper2_spectral_gap_dimension/`、`verification/` **未触碰**。

---

## 6. 转正清单（按依赖顺序）

1. 决定 2A 透传依赖的 5 个模块（§4）归属；
2. 切分点 1（`FullSpectrumDiscrete` 第一部分 → 2B）；
3. 切分点 2（`TrichotomyAndPolyExtension` 第一部分 → 2A）；
4. 回填 61 个「未核到」节锚（需打开 tex 核对，本次按纪律未开）；
5. 逐库 `lake env lean` + `#print axioms` 记录；
6. 转正后同步 `Audit.lean` 与 `lakefile.toml`（当前 glob `EpiFormal.+` 不覆盖 `epi_formal/` 根层文件，
   转正需决定：下沉到 `EpiFormal/` 子目录，或改 glob）。
