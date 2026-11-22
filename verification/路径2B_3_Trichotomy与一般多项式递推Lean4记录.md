# 路径 2B-3：Theorem 16(iii) 与一般 $r \ge 1$ 多项式增长递推（§6.3）Lean 4 形式化核查记录

> **一句总判断**：在 `epi_formal/EpiFormal/TrichotomyAndPolyExtension.lean`（4,022 行）中已完成 `Theorem 16(iii)`（$E_{\mathrm{lim}}^\pm(k/4) = x_k^\pm + L$ 完整陪集坍缩与零规范测度/零维数）及论文二 §6.3 一般 $r \ge 1$ 多项式增长递推核心定理族（`lem:poly-growth`、`lem:poly-lattice`、`thm:general-rec`、`thm:poly-gauge-trichotomy(iii)`、`thm:poly-phase-transition(i),(iii)`）的 Lean 4.35.0 机器形式化；全部 45 条导出定理的 `#print axioms` 审计均为「**已核实**」，零 `sorry`、零警告、零自定义公理（仅依赖 `[propext, Classical.choice, Quot.sound]`，其中 2 条纯整数递推引理仅用 `[propext, Quot.sound]`）；**本组形式化均属度量丢番图逼近与一般三项递推谱理论的文献定理复现/机器化，不推进也不解决 $e+\pi$ 无理性公开问题。**

---

## 一、诚实分类逐项对照表（按 `AGENTS.md` §2 五分类法）

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
|---|---|---|---|---|
| `Theorem 16(iii)` 完整陪集坍缩：`xPlus k ∈ E_lim^+(k/4)`、`-xPlus k ∈ E_lim^-(k/4)`、`L`-平移不变性与全集等式 `E_lim^±(k/4) = (±xPlus k) + L`、可数性、`dimH = 0`、任意 $m(r)\to 0^+$ Hausdorff 规范测度为 $0$（`trichotomy_part_iii_complete` 等 8 条定理） | **5. 文献核查与复现** | **已核实**（`lake env lean` 退出码 0；`[propext, Classical.choice, Quot.sound]`） | 补全 `FullSpectrumDiscrete.lean` 既有 `Theorem 16(i)(ii)` 之后的第 (iii) 部分，对应论文二 `thm:trichotomy(iii)`（在 `FullSpectrumDiscrete.lean` 已证同限差入格 `sub_mem_latticeL_of_same_signed_limit` 与精确极限缺陷刻画基础上完成显式构造与反向平移闭性） | `TrichotomyAndPolyExtension.lean` L48–L638，`#print axioms` L3978–L3985（8 条） |
| `lem:poly-growth` 一般 $r \ge 1$ 增长与非渐近阶乘下界：`Q_m ≥ C_{J_1} (c / 2^(r+1))^m (m!)^r` 与 `m^α / Q_m → 0`（`poly_Q_ge_factorial`、`poly_pow_div_Q_tendsto_zero`） | **5. 文献核查与复现** | **已核实**（`lake env lean` 退出码 0；`[propext, Classical.choice, Quot.sound]`） | 形式化论文二 §6.3 `lem:poly-growth`（在一般 `PolyRecData` 公理化记录结构上对任意 $r \ge 1, c \ge 1, d \in \mathbb{Z}$ 无条件成立） | `TrichotomyAndPolyExtension.lean` L643–L974，`#print axioms` L3986–L3987（2 条） |
| `lem:poly-lattice` 基底解、Casorati 行列式与极限格刻画：`poly_Q_eq_lincomb`、`poly_casorati`、`alphaU/V_error_bound`、`poly_alpha_linear_relation`、`theta_irrational`、`poly_dist_le_of_mem_latticePoly`、`polyWeightedExponent_eq_zero_of_mem_latticePoly`、`polyApprExponent_eq_zero_tfae` 等 | **5. 文献核查与复现** | **已核实**（前 2 条纯 `ℤ` 递推仅 `[propext, Quot.sound]`；其余 `[propext, Classical.choice, Quot.sound]`） | 形式化论文二 §6.3 `lem:poly-lattice`：交错收敛级数 $\alpha_U, \alpha_V$、$Q_{J_0-1}\alpha_U + Q_{J_0}\alpha_V = 1$、$\theta \notin \mathbb{Q}$ 及其导出的全权重指数 $\Lambda_\alpha^{(r,c,d)}(x) = 0$（对一切 $x \in L^{(r,c,d)}$ 及任意 $\alpha \in \mathbb{R}$） | `TrichotomyAndPolyExtension.lean` L980–L2285，`#print axioms` L3988–L3998（11 条） |
| `thm:general-rec` 一般多项式递推全谱离散化：`poly_signed_defect_approx`、`poly_abs_defect_approx`、`polyApprExponent_xPlusPoly`、`poly_spectral_gap_open_interval`、`poly_levelSet_eq_on_gap`、`poly_levelSet_below_eq_lattice`、`poly_range_apprExponent` 等 | **5. 文献核查与复现** | **已核实**（`lake env lean` 退出码 0；`[propext, Classical.choice, Quot.sound]`） | 形式化论文二 §6.3 `thm:general-rec(i)(ii)`：全谱精确等于 $\frac{1}{c}\mathbb{Z}_{\ge 0} \cup \{\infty\}$、一切开区间 $(k/c, (k+1)/c)$ 空谱隙与水平集台阶坍缩 | `TrichotomyAndPolyExtension.lean` L2103–L2875, L3920–L3976，`#print axioms` L3999–L4005, L4022（8 条） |
| `thm:poly-gauge-trichotomy(iii)` 一般递推有符号精确极限陪集坍缩：`poly_signed_exact_limit_iff_defect_const`、`xPlusPoly_mem_signedExactLimitSet`、`neg_xPlusPoly_mem_signedExactLimitSet`、`poly_sub_mem_latticePoly_of_same_signed_limit`、`poly_add_latticePoly_mem_signedExactLimitSet`、`poly_trichotomy_part_iii_complete` | **5. 文献核查与复现** | **已核实**（`lake env lean` 退出码 0；`[propext, Classical.choice, Quot.sound]`） | 形式化论文二 §6.3 `thm:poly-gauge-trichotomy(iii)`：对 $k \ge 1$，有符号极限集 $E_{\mathrm{lim}}^{(r,c,d),\pm}(k/c) = (\pm x_k^+) + L^{(r,c,d)}$ 为单可数陪集、`dimH = 0` 且任意零极限规范测度为 $0$ | `TrichotomyAndPolyExtension.lean` L2880–L3084，`#print axioms` L4006–L4011（6 条） |
| `thm:poly-phase-transition(iii)` 超临界（$\alpha > r$）坍缩：`poly_supercritical_levelSet_eq_lattice`、`poly_supercritical_dimH_zero`、`poly_supercritical_empty_neg` | **5. 文献核查与复现** | **已核实**（`lake env lean` 退出码 0；`[propext, Classical.choice, Quot.sound]`） | 形式化论文二 §6.3 `thm:poly-phase-transition(iii)`：$\alpha > r$ 时有限水平集均坍缩为 $L^{(r,c,d)}$（可数、维数 $0$），负水平集为空 | `TrichotomyAndPolyExtension.lean` L3090–L3146，`#print axioms` L4012–L4014（3 条） |
| `thm:poly-phase-transition(i)` 临界（$\alpha = r$）维数零与几乎处处 $\infty$ 谱：`poly_dimH_levelSet_finite`、`poly_dimH_finiteLevel_zero`、`poly_volume_finiteLevel_zero`、`poly_ae_apprExponent_eq_top`、`poly_volume_infiniteLevel_Icc`、`poly_dimH_infiniteLevel_inter_Icc_eq_one`、`poly_dimH_infiniteLevel_eq_one` | **5. 文献核查与复现** | **已核实**（`lake env lean` 退出码 0；`[propext, Classical.choice, Quot.sound]`） | 形式化论文二 §6.3 `thm:poly-phase-transition(i)`：借助非渐近 $(m!)^r$ 阶乘下界与显式分支计数覆盖，证明临界有限水平集 $\dim_H = 0$、Lebesgue 零测、a.e. $\Lambda = \infty$ 及 $[a,b]$ 上 $\Lambda=\infty$ 维数为 $1$ | `TrichotomyAndPolyExtension.lean` L3150–L3917，`#print axioms` L4015–L4021（7 条） |

---

## 二、Lean 4.35.0 构建与公理依赖核查详情

### 1. 执行命令与实测结果
在工作区 `epi_formal/` 目录下执行：
```powershell
Set-Location epi_formal
& "$env:USERPROFILE\.elan\bin\lake.exe" env lean EpiFormal/TrichotomyAndPolyExtension.lean
```
- **退出码**：`0`
- **错误 / 警告数**：`0` 错误、`0` 警告
- **静态扫描（`sorry` / `admit` / `axiom `）**：
  - 唯一匹配行：第 7 行中文文档注释（说明零 `sorry` 与仅依赖标准基础公理），代码与证明体内 **0 处 `sorry`**、**0 处 `admit`**、**0 条自定义 `axiom`**。

### 2. 三层公理分类清单（`#print axioms` 实测汇总，共 45 条）

- **第 1 层（Lean 基础公理，45 / 45 条）**：
  - 仅 `[propext, Quot.sound]`（2 条，无 `Classical.choice`）：
    `TrichotomyAndPolyExtension.PolyRecData.poly_Q_eq_lincomb`、`TrichotomyAndPolyExtension.PolyRecData.poly_casorati`
  - `[propext, Classical.choice, Quot.sound]`（43 条）：
    - Part 1 (`Theorem 16(iii)`，8 条)：
      `xPlus_mem_signedExactLimitSet`、`neg_xPlus_mem_signedExactLimitSet`、`add_latticeL_mem_signedExactLimitSet`、`signedExactLimitSet_pos_eq_coset`、`signedExactLimitSet_neg_eq_coset`、`signedExactLimitSet_zero_eq_latticeL`、`signedExactLimitSet_empty_of_not_quarter_int`、`trichotomy_part_iii_complete`
    - Part 2 (`lem:poly-growth`，2 条)：
      `PolyRecData.poly_Q_ge_factorial`、`PolyRecData.poly_pow_div_Q_tendsto_zero`
    - Part 2 (`lem:poly-lattice`，9 条)：
      `PolyRecData.alphaU_error_bound`、`PolyRecData.alphaV_error_bound`、`PolyRecData.poly_alpha_linear_relation`、`PolyRecData.theta_irrational`、`PolyRecData.poly_dist_le_of_mem_latticePoly`、`PolyRecData.polyWeightedExponent_eq_zero_of_mem_latticePoly`、`PolyRecData.polyApprExponent_eq_zero_tfae`、`PolyRecData.polyApprExponent_eq_zero_iff_mem_latticePoly`、`PolyRecData.polyApprExponent_eq_zero_iff_defect_zero`
    - Part 2 (`thm:general-rec`，8 条)：
      `PolyRecData.poly_signed_defect_approx`、`PolyRecData.poly_abs_defect_approx`、`PolyRecData.poly_jr_mul_eps_tendsto_of_defect_const`、`PolyRecData.polyApprExponent_xPlusPoly`、`PolyRecData.poly_spectral_gap_open_interval`、`PolyRecData.poly_levelSet_eq_on_gap`、`PolyRecData.poly_levelSet_below_eq_lattice`、`PolyRecData.poly_range_apprExponent`
    - Part 2 (`thm:poly-gauge-trichotomy(iii)`，6 条)：
      `PolyRecData.poly_signed_exact_limit_iff_defect_const`、`PolyRecData.xPlusPoly_mem_signedExactLimitSet`、`PolyRecData.neg_xPlusPoly_mem_signedExactLimitSet`、`PolyRecData.poly_sub_mem_latticePoly_of_same_signed_limit`、`PolyRecData.poly_add_latticePoly_mem_signedExactLimitSet`、`PolyRecData.poly_trichotomy_part_iii_complete`
    - Part 2 (`thm:poly-phase-transition(iii)`，3 条)：
      `PolyRecData.poly_supercritical_levelSet_eq_lattice`、`PolyRecData.poly_supercritical_dimH_zero`、`PolyRecData.poly_supercritical_empty_neg`
    - Part 2 (`thm:poly-phase-transition(i)`，7 条)：
      `PolyRecData.poly_dimH_levelSet_finite`、`PolyRecData.poly_dimH_finiteLevel_zero`、`PolyRecData.poly_volume_finiteLevel_zero`、`PolyRecData.poly_ae_apprExponent_eq_top`、`PolyRecData.poly_volume_infiniteLevel_Icc`、`PolyRecData.poly_dimH_infiniteLevel_inter_Icc_eq_one`、`PolyRecData.poly_dimH_infiniteLevel_eq_one`
- **第 2 层（经典白名单公理 `e_transcendental` / `pi_transcendental` / `mu_e_eq_two`）**：**0 条**。
- **第 3 层（项目自加公理 / `sorryAx`）**：**0 条**（无任何 `sorryAx` 或自定义 `axiom`；本模块已正式并入 `EpiFormal.lean` 与 `Audit.lean`，参与全工程 `9101 jobs / 349` 条审计）。

---

## 三、边界声明：它没做到什么

1. **与 $e+\pi$ 无理性问题的关系**：本文件形式化的全部结论均属于连分数/三项递推 $Q_{j+1} = (cj^r + d)Q_j + Q_{j-1}$ 所诱导的度量丢番图逼近谱与豪斯多夫维数刻画，**不涉及也不推进 $e+\pi$ 的无理性证明**（$e+\pi$ 无理性仍为公开问题）。
2. **一般多项式递推 §6.3 尚未在本文件中形式化的分支**：
   - `thm:poly-phase-transition(ii)`（亚临界权 $0 < \alpha < r$ 的满谱与 $\dim_H \{\Lambda_\alpha^{(r,c,d)} \le t\} = 1 - \alpha/r$ 维数精确公式 / 质量分布原理下界）尚未形式化；
   - `thm:poly-gauge-trichotomy(i), (ii)`（一般多项式递推的临界规范 $h_c(u)$ 精确零测、严格低阶规范 $g(u)/h_c(u) \to 0$ 的无穷测度构造，以及严格高阶规范 $h_c(u)/g(u) \to 0$ 的满区间二分现象）尚未形式化（针对 Euler $r=1, c=4$ 情形已在其他模块完成相应部分）。
3. **工程集成隔离**：按多模块并行分工约定，本次未修改 `epi_formal/EpiFormal.lean`、`epi_formal/EpiFormal/Audit.lean`、`.lake/build` 缓存或任何 `.tex` 论文源码；需由协调者后续将 `import EpiFormal.TrichotomyAndPolyExtension` 合入总索引与全量 `lake build`。
