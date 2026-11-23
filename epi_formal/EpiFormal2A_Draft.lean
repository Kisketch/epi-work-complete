/-
# EpiFormal2A_Draft —— 轨道 2A 草案入口（Draft / 未转正）

**性质**：草案入口，仅供分轨评审；**未进 `epi_formal/Audit.lean`、未参与 `lake build EpiFormal`**
（`lakefile.toml` 的 `[[lean_lib]] EpiFormal` 只 glob `EpiFormal.+`，本文件位于 `epi_formal/` 根层，不在该 glob 内）；
**按声明切分前不得转正**。

**来源**：`epi_formal/EpiFormal.lean` L1–132（132 条 import）。本入口取其 21 个模块，
行号逐条对应下列表格；import 顺序与主入口行号顺序一致，便于对照抽取。

**轨道定位**：论文二（*沿 e 收敛子分母的逼近谱隙与水平集维数*）的**谱 / 维数 / 规范测度核心层**。
2A 是三轨的**最底层**：全仓 import 图核验显示 2B→2A、2C→2A 有跨轨依赖，但 **2A 不 import 任何 2B/2C 模块**
（脚本核验：全仓 214 条 in-repo import 边中，2A 的 21 文件子图**零出边**指向 2B/2C）。

## 1. 声明级切分点（强制登记）

`FullSpectrumDiscrete`（`EpiFormal.lean` L7）**必须按声明切分，本草案暂时整文件引用**：

| 文件内分区 | 内容 | 归口 |
|---|---|---|
| `/-! ## 第一部分`（L42 起） | 一般线性增长递推 `Q_{j+1} = (c j + d) Q_j + Q_{j-1}` 的差商逼近引理（`general_defect_sub_main`、`general_signed_defect_approx` 等） | **2B**（一般递推轨的公共引理层） |
| `/-! ## 第二部分`（L124 起） | 整数序列离散刚性、无穷等距开谱隙排除、Euler 特化（`c = 4, d = 2`）的全谱离散化与正能级 `k/4` 三分法 | **2A**（谱结构核心） |

切分前：2B 不得直接 import 本文件（当前 2B 六个模块确实均未 import 它，故暂整文件挂 2A 不产生跨轨回边）；
切分后：第一部分应下沉为独立模块（建议名 `GeneralLinearRec`），2B 引之，2A 只保留第二部分。

## 2. 依赖声明

### 2.1 轨道内 5 个外部（非 2A/2B/2C）模块

2A **不是**只依赖 Mathlib：`Classification` / `SpectralGap` / `FullSpectrumDiscrete` / `QuarterPoint*` 链
透传依赖主入口的 5 个模块。转正时必须一并决定它们的归属，否则 2A 会拖着 5 个孤儿模块：

| 模块 | `EpiFormal.lean` 行 |
|---|---|
| `Alekseyev` | L92 |
| `EulerConvergents` | L105 |
| `Measure` | L108 |
| `MeiburgConvergence` | L110 |
| `ThresholdAttained` | L125 |

另：`EpiFormal.Basic`（L4）仅 1 行 `def hello := "world"`，**无实际声明**；本草案不 import 它，避免虚依赖。

### 2.2 轨道内 DAG 摘要（实际 import 边，脚本抽取）

```
Classification -> {EulerConvergents, Measure, MeiburgConvergence, Alekseyev}
SpectralGap    -> {EulerConvergents, Classification}
DimHCore       -> {SpectralGap}
DimHFinite     -> {DimHCore, SpectralGap}
QuarterPointCore  -> {ThresholdAttained}
QuarterPointTail  -> {QuarterPointCore}
QuarterPointFinal -> {QuarterPointTail, ThresholdAttained}
FullSpectrumDiscrete -> {Classification, SpectralGap, ThresholdAttained, QuarterPointFinal}
GaugeNull      -> {Classification, SpectralGap, DimHCore, FullSpectrumDiscrete}
GaugeExact     -> {DimHFinite, GaugeNull, FullSpectrumDiscrete, WeightedExactDim}
GaugeCircle    -> {GaugeNull, GaugeExact}
GaugeLiminfComplete -> {GaugeCircle}
WeightedPhase  -> {DimHFinite}
WeightedFiber  -> {DimHCore, WeightedPhase}
WeightedDimHCore -> {WeightedFiber}
WeightedLower  -> {WeightedFiber}
WeightedUpper  -> {WeightedDimHCore, SpectralGap, DimHFinite}
WeightedFinal  -> {WeightedUpper, DimHFinite}
WeightedExactDim -> {WeightedFinal, WeightedPhase, DimHCore}
WeightedCantor -> {WeightedDimHCore, WeightedLower}
UnweightedCorrection -> {QuarterPointFinal}
```

### 2.3 向下游（2B/2C）被依赖的接口

2B 显式依赖：`TrichotomyAndPolyExtension -> GaugeExact`、`PolyWeightedUpper -> WeightedPhase`、
`PolyGaugeAndPhaseTransition -> {GaugeCircle, GaugeLiminfComplete, WeightedExactDim}`、
`GeneralGrowingRec -> GaugeCircle`、`GeneralGrowingDim -> WeightedExactDim`。
2C 显式依赖：`FiniteStateTail -> GaugeLiminfComplete`、`FiniteStateComplete -> GaugeLiminfComplete`、
`FiniteStateGauge -> GaugeCircle`、`HermiteResiduePeriod -> Classification`、`NoShortDimRatio -> Classification`。
**冻结 2A 前必须先把上述 12 条跨轨边（2B 7 条 + 2C 5 条）的目标声明钉死**（本草案不改任何被依赖模块）。

## 3. 论文节锚（只登记模块头显式证据）

规则：仅当模块头出现 `§n` 时登记；否则写「未核到」——**不按内容猜节号**。
`§` 锚逐字取自模块头：`GaugeExact` → §4、§6；`GaugeCircle` → §6。

| # | 模块 | `EpiFormal.lean` 行 | 论文节锚 | 备注 |
|---|---|---|---|---|
| 1 | `GaugeNull` | L9 | 未核到（头指 Theorem 13 的零测度定理） | 临界能级子水平集 + 次临界规范规范零测度 |
| 2 | `GaugeExact` | L11 | **§4 / §6** | 内部两节级分区（见 LOG 切分点 3） |
| 3 | `GaugeCircle` | L13 | **§6** | 显式分片线性规范函数 + 柱集分裂 |
| 4 | `GaugeLiminfComplete` | L17 | 未核到 | 振荡规范推论 |
| 5 | `Classification` | L95 | 未核到（头提 Theorem 2） | `Qsel` 根序列地基，全仓共用 |
| 6 | `SpectralGap` | L123 | 未核到 | 谱隙基础 |
| 7 | `FullSpectrumDiscrete` | L7 | 未核到（头指「论文二三个核心升级结果」） | **需声明级切分，暂整文件引用** |
| 8 | `DimHCore` | L99 | 未核到 | 维数上/下界核心 |
| 9 | `DimHFinite` | L100 | 未核到 | 有限层维数 |
| 10 | `WeightedDimHCore` | L127 | 未核到 | 加权维数核心 |
| 11 | `WeightedFiber` | L128 | 未核到 | 纤维 |
| 12 | `WeightedUpper` | L132 | 未核到 | 加权上界 |
| 13 | `WeightedLower` | L130 | 未核到 | 加权下界 |
| 14 | `WeightedPhase` | L131 | 未核到 | 相变 |
| 15 | `WeightedCantor` | L126 | 未核到 | 加权 Cantor 构造 |
| 16 | `WeightedFinal` | L129 | 未核到 | 加权收尾 |
| 17 | `WeightedExactDim` | L6 | 未核到（头指「论文二」） | 精确极限集，2B 依赖入口 |
| 18 | `QuarterPointCore` | L117 | 未核到 | 四分之一极限点核心 |
| 19 | `QuarterPointTail` | L119 | 未核到 | 尾部 |
| 20 | `QuarterPointFinal` | L118 | 未核到 | 收尾，`FullSpectrumDiscrete` 依赖 |
| 21 | `UnweightedCorrection` | L10 | 未核到 | 无权情形修正 |

**节的补齐方式**（转正前置）：按 `paper2_spectral_gap_dimension/` 的 tex 逐模块核节号后回填；
本次按纪律**未打开**该目录，故一律标「未核到」，不得据内容推断。

## 4. 转正前置条件

1. `FullSpectrumDiscrete` 第一部分下沉为 `GeneralLinearRec` 一类独立模块，2B 引之（见 §1）；
2. §2.1 的 5 个外部模块归属决定完毕；
3. §2.3 的 12 条跨轨边目标声明冻结；
4. 论文节号按 tex 回填（§3 的「未核到」清零）；
5. 转正时逐库 `lake env lean` 验证并记录公理依赖，本草案**不预称已验证**。
-/

import EpiFormal.GaugeNull
import EpiFormal.GaugeExact
import EpiFormal.GaugeCircle
import EpiFormal.GaugeLiminfComplete
import EpiFormal.Classification
import EpiFormal.SpectralGap
import EpiFormal.FullSpectrumDiscrete
import EpiFormal.DimHCore
import EpiFormal.DimHFinite
import EpiFormal.WeightedDimHCore
import EpiFormal.WeightedFiber
import EpiFormal.WeightedUpper
import EpiFormal.WeightedLower
import EpiFormal.WeightedPhase
import EpiFormal.WeightedCantor
import EpiFormal.WeightedFinal
import EpiFormal.WeightedExactDim
import EpiFormal.QuarterPointCore
import EpiFormal.QuarterPointTail
import EpiFormal.QuarterPointFinal
import EpiFormal.UnweightedCorrection
