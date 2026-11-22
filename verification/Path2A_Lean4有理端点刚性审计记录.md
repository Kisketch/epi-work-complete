# Path 2A：共轭正性、一般有理端点四重算术刚性与 $B = 3, 4, 5, 6$ 谱隙核 Lean 4 形式化审计记录

> **一句总判断**：已在独立模块 [GeneralEndpointRigidity.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GeneralEndpointRigidity.lean) 中无条件形式化证明了论文一 §8 Path 2A 的 `prop:conjugate-positivity`、一般有理端点四重算术刚性与代数反演引理 `lem:general-endpoint-rigidity`（含二次互反律惰性素数判别与模 $2D$/$2d_0$ 同余筛），以及 $B = 3, 4, 5, 6$ 的算术筛与谱隙分离核心定理（含 $B=4$ 模 $16$ 乘法子群 $\{1, 7, 9, 15\}$ 禁除 $m = \pm 37$）；经本机实测 `lake env lean EpiFormal/GeneralEndpointRigidity.lean` 退出码 `0`、零警告、零错误、**30 条**导出 `theorem` 全部通过 `#print axioms` 核查（**28 条**仅依赖 `[propext, Classical.choice, Quot.sound]`，**2 条**仅依赖 `[propext, Quot.sound]`，**`sorryAx = 0`**，项目自加公理 `0` 条）。**以上工作仅形式化 $e$-侧仿射控制模型的局部代数与算术刚性核心，不对 $e+\pi$ 无理性这一公开中心问题构成任何推进。**

---

## 0. 诚实五分类逐项对照表

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| **`prop:conjugate-positivity`**（`cfMatrix_det`、`cfMatrix_eval_eq`、`eta_conj_ge_inv_sq_of_gt_one`、`eta_conj_add_pos_gt_abs`、`eta_conj_eq_inv_sq_at_two`）：对 $[a_0; \text{tail}, \overline{1}] > 1$ 且 $\ne \varphi$ 证明 $\eta' \ge \frac{3-\sqrt{5}}{2} = \varphi^{-2} > 0$（于 $[2;\overline{1}] = \varphi+1$ 取等）及 $z > 0 \implies |\eta'+z| = \eta'+z > |\eta'|$ | **1. 无条件新结果**（内部证明补洞，已形式化） | **已核实**（Lean 4.35.0 实测退出码 `0`，`sorryAx = 0`，仅基础公理） | 修复原 `thm:golden-b2-exact` Case 1 中 $|\eta'|\ge\varphi-1$ 伪不等式；并检验 $2\times 2$ 矩阵表示 `cfMatrix` 与连分数求值等价 | [GeneralEndpointRigidity.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GeneralEndpointRigidity.lean#L152-L350) |
| **`lem:general-endpoint-rigidity` 代数恒等式与 Part (4)**（`xi1_xi2Conj_identity`、`Muv_norm_identity`、`mobius_ratio_identity`、`ratio_eq_Muv_sub_div`、`Muv_norm_ne_zero`、`zphiNorm_xi2_dvd_norm_quot`） | **1. 无条件新结果**（已形式化） | **已核实**（Lean 4.35.0 实测退出码 `0`，`sorryAx = 0`，仅基础公理） | 复用 `GoldenOrbitB2Rigidity.M_uv` / `xi1_mul_xi2Conj` / `M_uv_norm_identity`，建立一般有理端点代数反演 $\eta = (p_1 - p_2 R)/(q_1 + q_2 R)$ 与非零范数整除性 | [GeneralEndpointRigidity.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GeneralEndpointRigidity.lean#L367-L445) / [#L819-L862](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GeneralEndpointRigidity.lean#L819-L862) |
| **`lem:general-endpoint-rigidity` Part (1)**（`inert_legendreSym_five_eq_neg_one`、`inert_prime_dvd_zphiNorm_iff`、`inert_prime_not_dvd_zphiNorm_of_cond`、`inert_prime_not_dvd_zphiNorm`、`inert_prime_not_dvd_zphiNorm_xi2`，含 $p=3,7$ `ZMod` 显式引理及对任意奇素数 $p \equiv 2,3 \pmod{5}$ 的二次互反律证明） | **1. 无条件新结果**（已形式化） | **已核实**（Lean 4.35.0 实测退出码 `0`，`sorryAx = 0`，仅基础公理） | 利用 Mathlib `legendreSym.quadratic_reciprocity_one_mod_four` 与 `eq_one_of_sq_sub_mul_sq_eq_zero`，覆盖全部惰性素数 $p=2$ 及 $p \equiv 2,3 \pmod{5}$ | [GeneralEndpointRigidity.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GeneralEndpointRigidity.lean#L450-L635) |
| **`lem:general-endpoint-rigidity` Part (2)–(3)**（`even_D_Muv_even`、`even_D_rigidity`、`even_D_rigidity_functional`、`mod_2D_sieve_q`、`mod_2D_sieve_p`、`mod_2d_sieve_special`） | **1. 无条件新结果**（已形式化） | **已核实**（Lean 4.35.0 实测退出码 `0`，`sorryAx = 0`，仅基础公理） | 推广 `GoldenOrbitRigidity.m0_even` 与 `GoldenOrbitB2Rigidity.m8q_mod4_identity` 至任意偶 $D = 2d_0$ 及一般端点 $(p_1/q_1, p_2/q_2)$ | [GeneralEndpointRigidity.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GeneralEndpointRigidity.lean#L637-L817) |
| **$B=3,4,5,6$ 算术筛与谱隙分离核心**（`b3_inert_three_not_dvd_m`、`b3_spectral_gap`、`b4_mod16_excludes_37`、`b4_spectral_gap`、`b5_even_m`、`b5_spectral_gap`、`b6_inert_three_not_dvd_m`、`b6_spectral_gap`） | **1. 无条件新结果**（核心算术/谱隙层，已形式化） | **已核实**（Lean 4.35.0 实测退出码 `0`，`sorryAx = 0`，仅基础公理） | 形式化 $B=3$（$3 \mid 9$ 惰性排除）、$B=4$（模 $16$ 子群 $\{1,7,9,15\}$ 封闭性并禁除 $m = \pm 37$）、$B=5$（偶 $m$ 与 $56,54$ 谱隙）与 $B=6$（$3 \mid 36$ 禁除 $m=81$ 达 $1 - 79/(36\sqrt{5})$）；完整 $\liminf$ 拓扑组装见纸面证明与 2500 位 `mpmath` 验证 | [GeneralEndpointRigidity.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GeneralEndpointRigidity.lean#L870-L1357) |

### 它没做到什么（边界声明）
1. **未形式化连分数极限拓扑组装与 Case 2 全分支**：本模块形式化了 `prop:conjugate-positivity`、`lem:general-endpoint-rigidity` 全文及 $B=3,4,5,6$ 的算术筛与谱隙核心不等式；`thm:golden-b3-exact`、`thm:golden-b4-exact`、`thm:golden-b5-exact`、`thm:golden-b6-exact` 与 `thm:golden-multiscale-exact` 中涉及 Hermite 收敛子周期 $W_j$ 枚举、`lem:even-suffix-sep`、`lem:general-case2-criterion` 及完整 Case 1/Case 2 $\liminf$ 拓扑组装保持为纸面证明与 2500 位 `mpmath` 核验（见 [Path2A_一般B3_B4仿射轨道谱理论记录.md](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/Path2A_一般B3_B4仿射轨道谱理论记录.md)、[Path2A_B5_B6与多尺度完全闭合记录.md](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/Path2A_B5_B6与多尺度完全闭合记录.md)、[verify_golden_b3_b4_exact.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_b3_b4_exact.log) 与 [verify_golden_b5_b6_multiscale.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_b5_b6_multiscale.log)）。
2. **总入口合入状态**：本模块已于后续收口阶段正式并入 `EpiFormal.lean` 与 `Audit.lean` 并通过全量 `lake build`（`9101 jobs`）与 `349` 条全量审计（见 [final_audit_20261120.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/final_audit_20261120.log)）。
3. **主问题边界**：所有结果均不推进 $e+\pi$ 无理性公开问题。

---

## 1. 本机实测命令与结果

- **工具链**：`epi_formal/lean-toolchain`（`leanprover/lean4:v4.35.0`）
- **实测命令**：
  ```powershell
  Set-Location epi_formal
  & "$env:USERPROFILE\.elan\bin\lake.exe" env lean EpiFormal/GeneralEndpointRigidity.lean
  ```
- **实测退出码**：`0`
- **编译输出检查**：`0` 错误、`0` 警告、**`sorryAx = 0`**，全 30 条导出定理均通过模块末尾 `#print axioms` 内核审计。
- **复用上游模块**：直接导入并复用 [GoldenOrbitRigidity.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GoldenOrbitRigidity.lean)（`φ`、`φ'`、`zphiNorm`、`mobius`、`orbitPt`、`orbitPtConj`、`orbitHeight`、`sqrt5_pos`、`sqrt5_sq`、`sqrt5_bounds`、`zphi_mul_conj`、`linear_phi_ne_zero`、`cd_ne_zero_of_det`、`zphiNorm_even_iff`）与 [GoldenOrbitB2Rigidity.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GoldenOrbitB2Rigidity.lean)（`M_uv`、`xi1_mul_xi2Conj`、`M_uv_norm_identity`、`rational_endpoint_rigidity_identity`）。

---

## 2. 三层公理清单与 30 条导出定理明细

### 2.1 三层公理统计

| 公理层级 | 包含公理 | 覆盖声明数 | 明细说明 |
| :--- | :--- | :---: | :--- |
| **第 1 层：Lean 基础公理** | `propext`、`Classical.choice`、`Quot.sound` | **30 条（100%）** | **28 条**依赖 `[propext, Classical.choice, Quot.sound]`；**2 条**纯整数环恒等式（`mod_2D_sieve_q`、`mod_2D_sieve_p`）仅依赖 `[propext, Quot.sound]`。 |
| **第 2 层：经典白名单公理** | `e_transcendental`、`pi_transcendental`、`mu_e_eq_two` | **0 条** | 本模块不涉及 $e, \pi$ 超越性或无理测度公理。 |
| **第 3 层：项目自加公理 / `sorryAx`** | 无 | **0 条** | 零自加公理、零 `sorryAx`。 |

### 2.2 全部 30 条导出定理逐项核查表

| 序号 | Lean 声明名（前缀 `GeneralEndpointRigidity.`） | 对应数学内容 | `#print axioms` 实测依赖 |
| :---: | :--- | :--- | :--- |
| 1 | `cfMatrix_det` | 连分数 $2\times 2$ 整数矩阵 `cfMatrix ns` 行列式恒为 $\pm 1$ | `[propext, Classical.choice, Quot.sound]` |
| 2 | `cfMatrix_eval_eq` | `cfMatrix (a0 :: tail)` 对 $\varphi, \varphi'$ 的 Möbius 作用与 `cfTailOne` / `cfConjTailOne` 一致 | `[propext, Classical.choice, Quot.sound]` |
| 3 | `eta_conj_ge_inv_sq_of_gt_one` | `prop:conjugate-positivity`：$\eta' \ge \frac{3-\sqrt{5}}{2} = \text{goldenRatio}^{-2} > 0$ 且 $\eta > 1$ | `[propext, Classical.choice, Quot.sound]` |
| 4 | `eta_conj_add_pos_gt_abs` | `prop:conjugate-positivity` 推论：$z > 0 \implies |\eta'+z| = \eta'+z > |\eta'|$ | `[propext, Classical.choice, Quot.sound]` |
| 5 | `eta_conj_eq_inv_sq_at_two` | 极值等号情况 $[2; \overline{1}] = \varphi + 1$，共轭恰取 $\frac{3-\sqrt{5}}{2}$ | `[propext, Classical.choice, Quot.sound]` |
| 6 | `xi1_xi2Conj_identity` | $2\xi_1 \xi_2' = M_{u,v} - (ad-bc)(p_1 q_2 + p_2 q_1)\sqrt{5}$ | `[propext, Classical.choice, Quot.sound]` |
| 7 | `Muv_norm_identity` | $|ad-bc|=1 \implies M_{u,v}^2 - 5D^2 = 4N(\xi_1)N(\xi_2)$ | `[propext, Classical.choice, Quot.sound]` |
| 8 | `mobius_ratio_identity` | $\xi_2 \ne 0, D \ne 0 \implies \eta = \frac{p_1 - p_2 R}{q_1 + q_2 R}$（$R = \xi_1/\xi_2$） | `[propext, Classical.choice, Quot.sound]` |
| 9 | `ratio_eq_Muv_sub_div` | $R = \xi_1/\xi_2 = \frac{M_{u,v} - \varepsilon D\sqrt{5}}{2N(\xi_2)}$ | `[propext, Classical.choice, Quot.sound]` |
| 10 | `inert_legendreSym_five_eq_neg_one` | 奇素数 $p \equiv 2, 3 \pmod{5} \implies \left(\frac{5}{p}\right) = -1$（二次互反律） | `[propext, Classical.choice, Quot.sound]` |
| 11 | `inert_prime_dvd_zphiNorm_iff` | 惰性素数 $p$（含 $p=2$ 与 $p \equiv 2,3 \pmod{5}$）：$p \mid N(x\varphi+y) \iff p \mid x \land p \mid y$ | `[propext, Classical.choice, Quot.sound]` |
| 12 | `inert_prime_not_dvd_zphiNorm_of_cond` | 由一般 `ZMod p` 二次型消去条件（含 $p=2,3,7$ 实例）推得 $p \nmid N(\xi_1)$ | `[propext, Classical.choice, Quot.sound]` |
| 13 | `inert_prime_not_dvd_zphiNorm` | `lem:general-endpoint-rigidity`(1)：惰性素数 $p \nmid N(\xi_1)$ | `[propext, Classical.choice, Quot.sound]` |
| 14 | `inert_prime_not_dvd_zphiNorm_xi2` | `lem:general-endpoint-rigidity`(1)：惰性素数 $p \nmid N(\xi_2)$ | `[propext, Classical.choice, Quot.sound]` |
| 15 | `even_D_Muv_even` | `lem:general-endpoint-rigidity`(2)：$D = 2d_0 \implies 2 \mid M_{u,v}$ | `[propext, Classical.choice, Quot.sound]` |
| 16 | `even_D_rigidity` | `lem:general-endpoint-rigidity`(2)：$m^2 - 5d_0^2 = N(\xi_1)N(\xi_2)$、$m \equiv d_0 + 1 \pmod{2}$、惰性 $p \mid d_0 \implies p \nmid m$ | `[propext, Classical.choice, Quot.sound]` |
| 17 | `even_D_rigidity_functional` | 偶 $D = 2d_0$ 情形误差泛函 $\Phi_{u,v}(\eta) = \left\|\frac{m}{d_0\sqrt{5}} - 1\right\|$ | `[propext, Classical.choice, Quot.sound]` |
| 18 | `mod_2D_sieve_q` | `lem:general-endpoint-rigidity`(3)：$2D \mid q_2(M_{u,v} + \varepsilon D) + 2q_1 N(\xi_2)$ | `[propext, Quot.sound]` |
| 19 | `mod_2D_sieve_p` | `lem:general-endpoint-rigidity`(3)：$2D \mid p_2(M_{u,v} + \varepsilon D) - 2p_1 N(\xi_2)$ | `[propext, Quot.sound]` |
| 20 | `mod_2d_sieve_special` | `lem:general-endpoint-rigidity`(3) 特化：$(2d_0/q_1, 0)$ 处 $m \equiv d_0 - \varepsilon q_1 N(\gamma) \pmod{2d_0}$ | `[propext, Classical.choice, Quot.sound]` |
| 21 | `Muv_norm_ne_zero` | `lem:general-endpoint-rigidity`(4)：$D \ne 0 \implies 4 \mid (M_{u,v}^2 - 5D^2)$ 且 $(M_{u,v}^2 - 5D^2)/4 \ne 0$ | `[propext, Classical.choice, Quot.sound]` |
| 22 | `zphiNorm_xi2_dvd_norm_quot` | `lem:general-endpoint-rigidity`(4)：$N(\xi_2) \mid (M_{u,v}^2 - 5D^2)/4$ | `[propext, Classical.choice, Quot.sound]` |
| 23 | `b3_inert_three_not_dvd_m` | $B=3$（$D=18, d=9$）：$m$ 为偶数且 $3 \nmid m$ | `[propext, Classical.choice, Quot.sound]` |
| 24 | `b3_spectral_gap` | $B=3$ 谱隙：$1 - \frac{20}{9\sqrt{5}} < \frac{22}{9\sqrt{5}} - 1 < 1 - \frac{16}{9\sqrt{5}}$ 及一般下界 | `[propext, Classical.choice, Quot.sound]` |
| 25 | `b4_mod16_excludes_37` | $B=4$（$D=32, d=16$）：$q_1 \in \{1,7,9,15\} \pmod{16}$ 迫使 $m$ 为奇数且 $m \ne \pm 37$ | `[propext, Classical.choice, Quot.sound]` |
| 26 | `b4_spectral_gap` | $B=4$ 谱隙：$1 - \frac{35}{16\sqrt{5}} < \frac{37}{16\sqrt{5}}-1 < 1 - \frac{33}{16\sqrt{5}} < \frac{39}{16\sqrt{5}}-1$ 及子群/奇数下界 | `[propext, Classical.choice, Quot.sound]` |
| 27 | `b5_even_m` | $B=5$（$D=50, d=25$）：$m$ 必为偶数 | `[propext, Classical.choice, Quot.sound]` |
| 28 | `b5_spectral_gap` | $B=5$ 谱隙：$\frac{56}{25\sqrt{5}}-1 < 1 - \frac{54}{25\sqrt{5}} < \frac{58}{25\sqrt{5}}-1$ 及偶整数下界 | `[propext, Classical.choice, Quot.sound]` |
| 29 | `b6_inert_three_not_dvd_m` | $B=6$（$D=72, d=36$）：$m$ 为奇数且 $3 \nmid m$（特别地 $m \ne 81$） | `[propext, Classical.choice, Quot.sound]` |
| 30 | `b6_spectral_gap` | $B=6$ 谱隙：$\frac{81}{36\sqrt{5}}-1 < 1 - \frac{79}{36\sqrt{5}} < \frac{83}{36\sqrt{5}}-1$ 及排除 $3 \mid m$ 后下界 | `[propext, Classical.choice, Quot.sound]` |

> 注：除上述 30 条 `theorem` 外，模块还导出辅助定义 `cfTail`、`cfTailOne`、`cfConjTailOne`、`cfMatrix`、`xi1`、`xi2`、`xi2Conj`、`InMod16Subgroup` 及辅助引理 `zmod3_norm_eq_zero`、`zmod7_norm_eq_zero`、`mod16_subgroup_neg`、`mod16_subgroup_mul`、`mod16_subgroup_dvd_89` 等。
