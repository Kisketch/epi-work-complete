/-
# EpiFormal2C_Draft —— 轨道 2C 草案入口（Draft / 未转正）

**性质**：草案入口，仅供分轨评审；**未进 `epi_formal/Audit.lean`、未参与 `lake build EpiFormal`**
（`lakefile.toml` 的 `[[lean_lib]] EpiFormal` 只 glob `EpiFormal.+`，本文件位于 `epi_formal/` 根层）；
**按声明切分前不得转正**。

**来源**：`epi_formal/EpiFormal.lean` L1–132；本入口取其中 61 个模块
（Window 族 44 + Cylinder 族 7 + 其余 10），行号逐条见下表，import 顺序按主入口行号。

**轨道定位**：论文二 §7 的**窗口计数 / 柱集（cylinder）/ 有限状态 / 剩余类**分析与组装轨。
2C 只向 2A 单向依赖（5 条 import 边、4 个目标模块），无 2B 依赖；2A/2B 均未 import 2C 任何模块
（脚本核验 214 条 in-repo 边）。

## 1. 声明级切分点

**2C 内部无跨轨声明级切分点**：61 个模块全部单轨，可整文件切分。
唯一需要登记的是 `FiniteStateTail` 的**命名空间口径**（文件 `FiniteStateTail.lean` 内为
`namespace FiniteStateGauge`，见 `EpiFormal/FiniteStateTail.lean` L7）：
按文件切分时声明归属会落在 `FiniteStateGauge` 命名空间下，引用需写 `FiniteStateGauge.*`，
不得据文件名推断命名空间。详见 `SPLIT_DRAFT_LOG.md` 口径 3。

## 2. 依赖声明

### 2.1 对 2A 的 5 条跨轨入边（2C 的全部跨轨依赖）

| 2C 模块 | -> 2A 模块 |
|---|---|
| `FiniteStateTail` | `GaugeLiminfComplete` |
| `FiniteStateComplete` | `GaugeLiminfComplete` |
| `FiniteStateGauge` | `GaugeCircle` |
| `HermiteResiduePeriod` | `Classification` |
| `NoShortDimRatio` | `Classification` |

### 2.2 三条内部主干链（实际 import 边）

```
[窗口链] WindowAndResidueCore (仅 Mathlib)
        -> WindowMobiusCount / WindowMobiusPartial / WindowWindowBounds -> WindowMainBound
        -> NoShortDimCount（反向吃窗口计数）
        -> WindowShortAe -> WindowShortAeRealize
[残差链] WindowAndResidueCore -> ResidueModGeneral
        + WindowThickening -> TransferOperatorDim -> ResidueAsymptotic
[有限状态链] GaugeCircle(2A) -> FiniteStateGauge -> FiniteStateTail -> FiniteStatePositive
        -> FiniteStateComplete（另加 GaugeLiminfComplete(2A)）
```

`ResidueAsymptotic -> TransferOperatorDim` 是**轨内**依赖（两者同在 2C），不是跨轨边；
`TransferOperatorDim` 另吃 `WindowThickening`，故残差链与窗口链在 2C 内部交汇，切轨时不可拆成两个入口。

### 2.3 孤立入口

`WindowAndResidueCore`（L12）只 import Mathlib，是 2C 的零依赖根；`Cylinder`（L32）只 import Mathlib，
是 Cylinder 族零依赖根；这两处适合作为 2C 转正时的编译起点（增量编译的最短验证路径）。

## 3. 论文节锚

规则：只登记模块头**前 40 行内**的显式 `§` 标记；无标记记「未核到」，不按内容猜节号。
**陷阱**：`WindowShortAe` 头部的 `§1`–`§6` 是**该文件内部小节编号**，不是论文节；
其论文锚是 tex L2610–2726（Theorem `thm:short-ae`）。同理 `WindowLogThresh` 头部的「blueprint §4」
是 blueprint 的 §4，不是论文 §4——两处都**不得**当作论文节号引用。

### 3.1 Window 族（44）

| 模块 | 行 | 节锚 |
|---|---|---|
| `WindowAndResidueCore` | L12 | §7（论文二 §7，Theorems 18–21） |
| `WindowShortAe` | L21 | tex L2610–2726（内部 §1–§6 非论文节） |
| `WindowMobiusCount` | L27 | §7 |
| `WindowMobiusPartial` | L28 | §7 |
| `WindowWindowBounds` | L29 | §7 |
| `WindowMainBound` | L30 | §7 |
| `WindowMuLevel` | L38 | 未核到 |
| `WindowThickBound` | L40 | 未核到 |
| `WindowLevelCount` | L41 | §7 |
| `WindowLogFact` | L42 | 未核到 |
| `WindowMassDist` | L43 | 未核到 |
| `WindowCoverCount` | L44 | §7 |
| `WindowHinter` | L45 | 未核到 |
| `WindowOverlap` | L46 | §7 |
| `WindowMuImplication` | L47 | §7 |
| `WindowMuBound` | L48 | §7 |
| `WindowMuScale` | L49 | 未核到 |
| `WindowSplitMass` | L50 | §7 |
| `WindowMuThresh` | L51 | 未核到 |
| `WindowStoppedTree` | L52 | §7 |
| `WindowFrostmanDirect` | L53 | 未核到 |
| `WindowRealize` | L54 | 未核到 |
| `WindowConcreteThresh` | L55 | 未核到 |
| `WindowLargeWindow` | L56 | 未核到 |
| `WindowLargeThresh` | L57 | §7 |
| `WindowSandwich` | L58 | §7 |
| `WindowWordTree` | L59 | 未核到 |
| `WindowMassProd` | L60 | §7 |
| `WindowLogThresh` | L61 | 未核到（头注「blueprint §4」非论文节） |
| `WindowMassFull` | L62 | 未核到 |
| `WindowDescFiber` | L63 | 未核到 |
| `WindowStoppedUniform` | L64 | §7 |
| `WindowThickening` | L65 | §7 |
| `WindowPointMass` | L66 | §7 |
| `WindowTreePrune` | L67 | 未核到 |
| `WindowAsympThresh` | L68 | 未核到 |
| `WindowFrostmanDischarge` | L69 | 未核到 |
| `WindowPaperScale` | L70 | 未核到 |
| `WindowCFRealize` | L71 | 未核到 |
| `WindowCFBridge` | L72 | 未核到 |
| `WindowNoShortCFRealize` | L73 | 未核到 |
| `WindowPrescribedCFRealize` | L74 | 未核到 |
| `WindowBoundedUpper` | L75 | 未核到 |
| `WindowShortAeRealize` | L84 | 未核到 |

### 3.2 Cylinder 族（7）

| 模块 | 行 | 节锚 |
|---|---|---|
| `Cylinder` | L32 | §7（头注 paper2 §7，均摊矩阵） |
| `CylinderMediant` | L33 | 未核到 |
| `CylinderOrder` | L34 | 未核到 |
| `CylinderDiameter` | L35 | 未核到 |
| `CylinderFiber` | L36 | §7 |
| `CylinderPhaseE` | L37 | 未核到 |
| `CylinderFrostman` | L39 | 未核到 |

### 3.3 其余（10）

| 模块 | 行 | 节锚 | 备注 |
|---|---|---|---|
| `FiniteStateTail` | L1 | 未核到 | 文件内 `namespace FiniteStateGauge`（L7） |
| `NoShortDimCount` | L3 | §7 | 吃窗口计数链 |
| `FiniteStateGauge` | L18 | 未核到 | 有限状态路径计数 |
| `HermiteResiduePeriod` | L20 | 未核到 | 相邻 Hermite 对剩余周期，内核基例 |
| `FiniteStatePositive` | L26 | 未核到 | |
| `NoShortDimRatio` | L31 | §7 | |
| `ResidueModGeneral` | L85 | 未核到 | |
| `TransferOperatorDim` | L86 | 未核到 | 残差链枢纽 |
| `FiniteStateComplete` | L87 | 未核到 | |
| `ResidueAsymptotic` | L88 | 未核到 | 轨内末端，依赖 `TransferOperatorDim` |

## 4. 转正前置条件

1. 2A 的 3 个被依赖模块（`GaugeLiminfComplete`、`GaugeCircle`、`Classification`）冻结——其中 `Classification`
   被 `HermiteResiduePeriod` 与 `NoShortDimRatio` 两处引用，`GaugeLiminfComplete` 被 `FiniteStateTail` 与
   `FiniteStateComplete` 两处引用；
2. `FiniteStateTail` 命名空间口径在引用处统一（见 §1）；
3. 节号回填（§3.1/3.2/3.3 的「未核到」按 tex 补齐）；
4. 残差链与窗口链必须同入口（§2.2），不得拆成 2C1/2C2 两个入口；
5. 转正时逐库验证并记录公理依赖，本草案不预称已验证。
-/

import EpiFormal.FiniteStateTail
import EpiFormal.NoShortDimCount
import EpiFormal.WindowAndResidueCore
import EpiFormal.WindowShortAe
import EpiFormal.WindowMobiusCount
import EpiFormal.WindowMobiusPartial
import EpiFormal.WindowWindowBounds
import EpiFormal.WindowMainBound
import EpiFormal.NoShortDimRatio
import EpiFormal.Cylinder
import EpiFormal.CylinderMediant
import EpiFormal.CylinderOrder
import EpiFormal.CylinderDiameter
import EpiFormal.CylinderFiber
import EpiFormal.CylinderPhaseE
import EpiFormal.WindowMuLevel
import EpiFormal.CylinderFrostman
import EpiFormal.WindowThickBound
import EpiFormal.WindowLevelCount
import EpiFormal.WindowLogFact
import EpiFormal.WindowMassDist
import EpiFormal.WindowCoverCount
import EpiFormal.WindowHinter
import EpiFormal.WindowOverlap
import EpiFormal.WindowMuImplication
import EpiFormal.WindowMuBound
import EpiFormal.WindowMuScale
import EpiFormal.WindowSplitMass
import EpiFormal.WindowMuThresh
import EpiFormal.WindowStoppedTree
import EpiFormal.WindowFrostmanDirect
import EpiFormal.WindowRealize
import EpiFormal.WindowConcreteThresh
import EpiFormal.WindowLargeWindow
import EpiFormal.WindowLargeThresh
import EpiFormal.WindowSandwich
import EpiFormal.WindowWordTree
import EpiFormal.WindowMassProd
import EpiFormal.WindowLogThresh
import EpiFormal.WindowMassFull
import EpiFormal.WindowDescFiber
import EpiFormal.WindowStoppedUniform
import EpiFormal.WindowThickening
import EpiFormal.WindowPointMass
import EpiFormal.WindowTreePrune
import EpiFormal.WindowAsympThresh
import EpiFormal.WindowFrostmanDischarge
import EpiFormal.WindowPaperScale
import EpiFormal.WindowCFRealize
import EpiFormal.WindowCFBridge
import EpiFormal.WindowNoShortCFRealize
import EpiFormal.WindowPrescribedCFRealize
import EpiFormal.WindowBoundedUpper
import EpiFormal.WindowShortAeRealize
import EpiFormal.ResidueModGeneral
import EpiFormal.TransferOperatorDim
import EpiFormal.FiniteStateComplete
import EpiFormal.ResidueAsymptotic
import EpiFormal.FiniteStateGauge
import EpiFormal.FiniteStatePositive
import EpiFormal.HermiteResiduePeriod
