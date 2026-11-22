# P1：独立洁净环境 Lean 4 复现与三层公理审计记录

> **一句总判断**：在独立洁净目录 `%TEMP%\ef3` 中已核实 `epi_formal` 源码与配置文件（全部 **67 个**非 `.lake`/`.git` 文件，含 **56 个** `.lean` 文件）与工作区逐字节一致（`DIFFS=0`），删除 `.lake\build` 后从零顺序预热高并发根模块并执行完整 `lake build`（终版 **9101 jobs**，退出码 `0`）与 `lake env lean Audit.lean` 审计（**349 条**声明：**327** 条仅依赖 Lean 基础公理 + **22** 条依赖经典白名单公理 `e_transcendental` / `pi_transcendental` / `mu_e_eq_two` + **0** 条项目自加公理 + **0** 条 `sorryAx`），洁净环境原始 UTF-8/LF 输出 `SHA256` 与工作区主审计日志 `verification/final_audit_20261120.log` **逐字节完全一致**，核查状态记为 **已核实（类别 5：文献核查与复现）**。

---

## 一、复现环境与核查摘要

| 核查项 | 洁净目录复现结果 | 工作区主干基准 | 一致性 / 状态 |
|---|---|---|---|
| 洁净目录路径 | `%TEMP%\ef3`（短路径规避 Windows `MAX_PATH` 限制） | `epi_formal/` | 独立目录隔离 `.lake/build` |
| 非 `.lake`/`.git` 文件比对 | `67/67` 文件逐字节一致（含 `56` 个 `.lean` 文件，`DIFFS=0`） | `67` 个源码/配置文件 | 已核实（`SHA256` 零差异） |
| 工具链与依赖包 | `leanprover/lean4:v4.35.0`（Lake 5.0.0），`Copy-Item -Recurse` 镜像 `.lake/packages` | 同左（`146421` 个包文件无缺失） | 已核实 |
| 构建完成状态 | 删除 `ef3\.lake\build` 后分模块预热再运行 `lake build`：成功（`9101 jobs`，exit `0`） | 成功（`9101 jobs`，exit `0`） | 已核实（`0 sorry` 编译） |
| `Audit.lean` 声明总数 | `349` 条（含 `GeneralEndpointRigidity.lean` 30 条、`TrichotomyAndPolyExtension.lean` 45 条、`GaugeCircle.lean` 53 条） | `349` 条 | 一致 |
| 公理依赖三层分类 | `327` 基础 + `22` 白名单 + `0` 项目自加（`sorryAx = 0`） | `327` 基础 + `22` 白名单 + `0` 项目自加 | 逐字节相同 |
| 审计日志 `SHA256`（LF 规范化） | `CF55D97B01F56ECE9700DB7D807C594E84A8C1192C354C85144252F32AA7FE4C` | `CF55D97B01F56ECE9700DB7D807C594E84A8C1192C354C85144252F32AA7FE4C` | `BYTE_EQUAL=True` |

> **Windows 复现环境说明**：  
> 1. 洁净目录须置于短路径（如 `%TEMP%\ef3`），避免深层 `Mathlib\CategoryTheory\...olean.private` 触及 Windows 260 字符 `MAX_PATH` 限制。  
> 2. 复制预编译 `.lake\packages` 须使用 PowerShell `Copy-Item -Recurse -Force`（而非 `robocopy`），以确保全部 `146421` 个包文件完整镜像。  
> 3. 全量并发 `lake build` 在 Windows 上同时由 8+ 个 `lean.exe` 映射完整 Mathlib `.olean` 内存视图时，会触发虚拟内存提交上限导致 `failed to read file '...olean'`；先单模块顺序构建 `EpiFormal.Axioms`、`EpiFormal.Measure`、`EpiFormal.AlgebraicIndependence`、`EpiFormal.Elementary`、`EpiFormal.Series`、`EpiFormal.GoldenOrbitRigidity`、`EpiFormal.Spectrum`、`EpiFormal.WindowAndResidueCore`、`EpiFormal.PadeODE` 后，再运行全量 `lake build` 即可稳定通过全部 `9101 jobs`。

---

## 二、核心模块与公理层级结构

1. **Lean 基础公理（327 条）**：仅依赖 `[propext, Quot.sound]` 或 `[propext, Classical.choice, Quot.sound]`，覆盖：
   - 论文一基础代数、连分数近似率与轨道理论核心（`Basic`, `Elementary`, `Series`, `SpectralGap`, `Spectrum`, `DefectFibres`, `FullSpectrumDiscrete`, `SignedClusters`, `SignedCriterion`, `GoldenOrbitRigidity`, `GoldenOrbitB2Rigidity`, **`GeneralEndpointRigidity` [30 条]**），
   - 论文二三分法与一般多项式递推扩展（`QuarterPointCore/Tail/Final`, `WeightedPhase/Fiber/DimHCore/Upper/Final/ExactDim/Lower/Cantor`, `GaugeNull`, `GaugeExact`, `GaugeCircle` [53 条], **`TrichotomyAndPolyExtension` [45 条]**：`thm:trichotomy(iii)` 陪集塌缩全闭合与 §6.3 `PolyRecData` 任意阶 `r≥1` 递推核心），
   - 论文二 §7 有限局部窗与模 4 残差核心离散引理（`WindowAndResidueCore` 14 条）及 Padé / Meiburg / Alekseyev / Flint–Hills 相关纯代数与解析引理。
2. **经典白名单公理（22 条）**：仅在 `EpiFormal.Axioms` 引入 `e_transcendental`、`pi_transcendental`、`mu_e_eq_two`（Mahler $\mu(e)=2$）；其中 `AlgebraicIndependence`（6 条）、`Escape`（2 条）、`EscapeBoundary`（1 条）、`EscapeReduction`（1 条）、`ThresholdAttained`（4 条）、`Classification`（8 条）共 22 条声明合理依赖该白名单。
3. **项目自加公理 / `sorryAx`（0 条）**：`Audit.lean` 全部 `349` 条输出经逐块解析确认，`Axioms` 白名单外自定义公理为 `0`，`sorryAx` 为 `0`。
4. **独立未入主树补丁核验**：`论文一_e_plus_pi/第二阶段修订/formalization/FiniteStateGauge.lean` 在同一 Lake 环境下通过 `lake env lean` 检查（退出码 `0`），其 `walkMass_of_eigenvector` 与 `walkCount_bounds` 严格仅依赖 `[propext, Classical.choice, Quot.sound]`。

---

## 三、诚实边界（它没做到什么）

1. **论文一（$e+\pi$ 与连分数谱）未形式化部分**：$B=3,4,5,6$ 与 4 个多尺度特例（`thm:golden-b3-exact`、`thm:golden-b4-exact`、`thm:golden-b5-exact`、`thm:golden-b6-exact`、`thm:golden-multiscale-exact`）的连分数周期表生成、有限移位窗口最小间隔与动态 $\liminf$ 转移仍由纸面证明 + `2500` 位高精度 `mpmath` 脚本验证支撑（`GeneralEndpointRigidity.lean` 已形式化共轭下界 `prop:conjugate-positivity`、一般有理端点刚性 `lem:general-endpoint-rigidity` 与模筛/谱隙不等式）；$B \ge 7$ 尚未给出任意 $B$ 的闭式第二极限点；$e+\pi$ 无理性（`prob:main`）与 $c_\varphi(\pi)=0$ **完全未解决**。
2. **论文二（谱隙、Hausdorff 规范与窗口/残差）未形式化部分**：§6.3 一般多项式递推的规范零/正/精确分支（`thm:poly-gauge-trichotomy(i),(ii)`、`cor:poly-exact-gauge`）及一般次临界精确维数公式 $1-\alpha/r$（`thm:poly-phase-transition(ii)`）目前仍为纸面证明（`TrichotomyAndPolyExtension.lean` 已形式化增长、格点、全谱、三分法 (iii)、临界/超临界塌缩）；§6.2b `thm:finite-state-tail` 仅形式化了有限步游走质量与计数局部引理；§7 高斯测度遍历性、Bowen 拓扑压与转移算子微扰（`thm:windows`–`thm:residues`）的主体解析论证仍为纸面证明（辅以 `residue_certificate.py` 精确分数证书），`WindowAndResidueCore.lean` 仅形式化其局部组合核心；全区间非零残差窗口数值区间 `(0.371, 0.446)` 系有限深度实验观察，不作为一般性证明。
3. **本复现不构成新数学证明**：干净环境 `lake build` 与 `Audit.lean` 字节比对仅验证“既有 Lean 4 形式化代码在独立环境中无隐匿缓存地通过类型检查与三层公理审计”（类别 5）。
