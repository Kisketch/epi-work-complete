/-
# EpiFormal2B_Draft —— 轨道 2B 草案入口（Draft / 未转正）

**性质**：草案入口，仅供分轨评审；**未进 `epi_formal/Audit.lean`、未参与 `lake build EpiFormal`**
（`lakefile.toml` 的 `[[lean_lib]] EpiFormal` 只 glob `EpiFormal.+`，本文件位于 `epi_formal/` 根层）；
**按声明切分前不得转正**。

**来源**：`epi_formal/EpiFormal.lean` L1–132；本入口取其中 6 个模块，行号见下表。

**轨道定位**：论文二 §6.3 的**多项式 / 一般增长递推扩展轨**
（`PolyRecData` → `GrowingRecData` → 任意 `A_j ≥ 2, A_j → ∞` 的三项整递推）。
2B 是**上层轨**：只向 2A 单向依赖，无 2C 依赖，2A/2C 也无任何模块 import 本轨
（脚本核验：全仓 214 条 in-repo import 边中，2B 的跨轨出边全部指向 2A）。

## 1. 声明级切分点（强制登记）

`TrichotomyAndPolyExtension`（`EpiFormal.lean` L15）**前半归 2A，本草案暂时整文件引用**：

| 文件内分区 | 行 | 内容 | 归口 |
|---|---|---|---|
| `## 第一部分` | L51 | **Theorem 16(iii)** 完整补全（Euler 收敛子情形，`signedExactLimitSet` 陪集坍缩、`xPlus k`） | **2A**（Euler 谱结构，与 `GaugeExact` 的 Theorem 16(ii) 同族） |
| `## 第二部分` | L640 | §6.3 一般 `r ≥ 1` 多项式增长递推与 `lem:poly-growth` | 2B |
| `## 第三部分` | L986 | `lem:poly-lattice`（基本解、Casorati、交错收敛、内蕴晶格） | 2B |
| `## 第四部分` | L1912 | 一般递推逼近函数、缺陷、`lem:poly-lattice`(iv)、`thm:general-rec` | 2B |
| `## 第五部分` | L2287 | `xPlusPoly` 常值缺陷见证与全谱离散化 | 2B |
| `## 第六部分` | L2877 | `thm:poly-gauge-trichotomy(iii)`（一般多项式陪集坍缩） | 2B |
| `## 第七部分` | L3085 | `thm:poly-phase-transition`(i)(iii)（临界维数零、超临界坍缩） | 2B |

切分前：2A **不得** import 本文件（当前 2A 确实未 import，故无跨轨回边）；2B 整文件引用是安全的，
但会把 2A 的第一部分一并拉进 2B 的编译单元，转正时必须拆走。
切分后第一部分（L51–639）下沉为独立模块（建议名 `EulerSignedTrichotomy`），归 2A；2B 引之。

## 2. 依赖声明（实际 import 边，脚本抽取）

| # | 模块 | `EpiFormal.lean` 行 | 直接依赖 | 论文节锚 |
|---|---|---|---|---|
| 1 | `PolyWeightedLower` | L2 | `PolyWeightedUpper`（2B） | 未核到（头注：次临界维数下界，复用 WeightedExactDim 构造） |
| 2 | `PolyWeightedUpper` | L19 | `PolyGaugeAndPhaseTransition`（2B）、**`WeightedPhase`（2A）** | 未核到 |
| 3 | `PolyGaugeAndPhaseTransition` | L16 | `TrichotomyAndPolyExtension`（2B）、**`GaugeCircle`（2A）**、**`GaugeLiminfComplete`（2A）**、**`WeightedExactDim`（2A）** | **§6.3** |
| 4 | `TrichotomyAndPolyExtension` | L15 | **`GaugeExact`（2A）** | **§6.3**（另含 Theorem 16(iii)，见 §1） |
| 5 | `GeneralGrowingRec` | L89 | `TrichotomyAndPolyExtension`、`PolyGaugeAndPhaseTransition`（2B）、**`GaugeCircle`（2A）** | 未核到（头称 Paper 2 扩展，未标 §） |
| 6 | `GeneralGrowingDim` | L90 | `GeneralGrowingRec`（2B）、**`WeightedExactDim`（2A）** | 未核到 |

### 2.1 对 2A 的跨轨出边（2B 的全部跨轨依赖）

1. `PolyWeightedUpper -> WeightedPhase`
2. `PolyGaugeAndPhaseTransition -> GaugeCircle`
3. `PolyGaugeAndPhaseTransition -> GaugeLiminfComplete`
4. `PolyGaugeAndPhaseTransition -> WeightedExactDim`
5. `TrichotomyAndPolyExtension -> GaugeExact`
6. `GeneralGrowingRec -> GaugeCircle`
7. `GeneralGrowingDim -> WeightedExactDim`

（共 7 条 import 边、**5 个** 2A 目标模块：`WeightedPhase`、`GaugeCircle`、`GaugeLiminfComplete`、
`WeightedExactDim`、`GaugeExact`。）
**2A 冻结清单必须含这 5 个模块**，否则 2B 编译断裂。

### 2.2 轨道内 DAG

```
PolyWeightedUpper -> PolyGaugeAndPhaseTransition -> TrichotomyAndPolyExtension -> GaugeExact(2A)
PolyWeightedLower -> PolyWeightedUpper
GeneralGrowingRec -> {TrichotomyAndPolyExtension, PolyGaugeAndPhaseTransition, GaugeCircle(2A)}
GeneralGrowingDim -> {GeneralGrowingRec, WeightedExactDim(2A)}
```

## 3. 论文节锚说明

仅 `PolyGaugeAndPhaseTransition`（§6.3）与 `TrichotomyAndPolyExtension`（§6.3）在模块头出现显式 `§` 标记；
其余 4 个模块头写的是「Paper 2 / 论文二 扩展」，**未给节号** → 一律记「未核到」，不按内容猜。
转正前置：按 tex 回填 §6.3 的细分（`lem:poly-growth`、`lem:poly-lattice`、`thm:general-rec` 等标签
已在模块头出现，可直接对 tex 标签核位）。

## 4. 转正前置条件

1. `TrichotomyAndPolyExtension` 第一部分（L51–639）拆出归 2A（见 §1）；
2. 2A 的 5 个被依赖模块（§2.1）冻结；
3. `FullSpectrumDiscrete` 第一部分（一般 `(cj+d)` 递推）若下沉为 `GeneralLinearRec`，
   2B 应考虑引用它而非重复实现一般递推引理——本草案**未**做此引用，保持零跨轨新增边；
4. 节号回填完毕；
5. 转正时逐库验证并记录公理依赖，本草案不预称已验证。
-/

import EpiFormal.PolyWeightedLower
import EpiFormal.PolyWeightedUpper
import EpiFormal.PolyGaugeAndPhaseTransition
import EpiFormal.TrichotomyAndPolyExtension
import EpiFormal.GeneralGrowingRec
import EpiFormal.GeneralGrowingDim
