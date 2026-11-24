# OBL-3b 加权相变下界与精确维数等式 Lean 4 形式化审计记录（2026-11-20）

## 一句总判断
论文二（《谱隙与维数》）Theorem `\ref{conj:weight}` 对应的次临界加权相变下界与精确 Hausdorff 维数等式（OBL-3b）已在 Lean 4（`v4.35.0`）中无条件形式化闭合并通过全量 `lake build` 与 `Audit.lean` 核实（零 `sorryAx`、仅依赖 Lean 基础公理 `[propext, Classical.choice, Quot.sound]`）；该结果属于度量丢番图逼近中特定子列加权维数等式的形式化严格化，**不推进 $e+\pi$ 无理性这一公开中心问题**。

## 逐项对照表（诚实五分类法）

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
|---|---|---|---|---|
| `WeightedExactDim.one_le_hausdorffMeasure_cantorSet`：对 $0 < s < 1 - \beta$，均匀嵌套 Cantor 集满足 $\mu_H^s(K) \ge 1$ | 文献核查与复现（经典 Moran / 质量分布下界的紧致有限覆盖形式化） | **已核实**（`lake build` + `#print axioms`，仅基础公理） | 同类 Moran 维数下界见 Feng–Wen–Wu（论文二 `\cite{FWW}`）；本形式化绕过 Borel 测度构造，直接用紧致性与有限树计数作用于 Mathlib `hausdorffMeasure_apply` | [WeightedExactDim.lean](../epi_formal/EpiFormal/WeightedExactDim.lean) |
| `WeightedExactDim.dimH_exactLimitSetα_ge` 与 `dimH_exactLimitSetα_eq`：对 $0 < \alpha < 1, c \ge 0$ 及 $\alpha = 0, 0 \le c \le 1/2$，$\dim_H\{x \in [0,1] : j^\alpha\|Q_j x\| \to c\} = 1 - \alpha$ | 无条件新结果（对特定选定子列 $Q_j$ 的加权指定极限集精确维数；$\alpha = 0$ 情形对应 `\cite{BLR}` Corollary 8） | **已核实**（`lake build` + `#print axioms`，仅基础公理） | $\alpha = 0$ 可由 `\cite{BLR}` Corollary 8 得出；$0 < \alpha < 1$ 时其 Theorem 7 条件 (1.6) 不满足（$\log Q_{j+1}/\log Q_j \to 1$），此处与 `WeightedFinal.dimH_levelSetα_le` 拼接得精确等式 | [WeightedExactDim.lean](../epi_formal/EpiFormal/WeightedExactDim.lean)、[Phase2_revised.tex](../paper1_e_plus_pi/02_companion_paper/Phase2_revised.tex) |
| `WeightedExactDim.dimH_levelSetα_eq` 与 `dimH_apprExponentα_eq_zero`：对一切 $0 \le \alpha < 1, c \ge 0$，$\dim_H\{\Lambda_\alpha \le c\} = \dim_H\{\Lambda_\alpha = 0\} = 1 - \alpha$ | 无条件新结果（纠正早期“$\alpha<1$ 维数为 1”的错误猜想并完成双边机器闭合） | **已核实**（`lake build` + `#print axioms`，仅基础公理） | 结合 `WeightedFinal.dimH_levelSetα_le`（OBL-3a 上界）与 $c = 0$ 精确极限集包含关系闭合 OBL-3b | [WeightedExactDim.lean](../epi_formal/EpiFormal/WeightedExactDim.lean) |
| $e+\pi$ 无理性（OBL-4） | 开放未证 | 未证 | 公开问题；唯一硬结论仍为 $e+\pi$ 与 $e\pi$ 至少其一超越 | 见 [AGENTS.md](../AGENTS.md) 基线 |

## 形式化证明要点（`WeightedExactDim.lean`）
1. **多项式宽度与钳位偏移**：固定 $s \in (0, 1-\alpha)$，取 $\varepsilon = (1-\alpha-s)/2 > 0$，$\beta = \alpha + \varepsilon$，$w_j = j^{-\beta}$，钳位偏移 $\theta_j = \max(w_j, \min(c j^{-\alpha}, 1/2 - w_j)) \in [w_j, 1/2 - w_j]$。该设计统一处理 $0 < \alpha < 1, c \ge 0$ 与 $\alpha = 0, 0 \le c \le 1/2$（含 $c = 0$ 与 $c = 1/2$ 端点），保证对 $x \in I_j(k)$ 精确有 $k \le Q_j x \le k + 1/2$，从而 $\|Q_j x\| = Q_j x - k$ 且 $|j^\alpha \|Q_j x\| - c| \le 2 j^{-\varepsilon} \to 0$。
2. **严格嵌套均匀 Cantor 树**：用严格嵌套条件 $|c_{j+1}(k') - c_j(k)| \le r_j - r_{j+1}$ 及 $Q_{j+1} \ge 4j Q_j$ 给出每父节点至少 $b_j = \lfloor 6 j^{1-\beta} \rfloor \ge 5 j^{1-\beta}$ 个严格嵌套子节点；用抽象纤维计数引理证明每层祖先扩展数精确满足 $\mathrm{card}(\mathrm{fiber}) \cdot M_n = M_N$。
3. **紧致性 + 有限树计数证 $\mu_H^s(K) \ge 1$**：对任意小直径可数覆盖 $\{t_i\}$ 施加自适应开膨胀 $V_i = \mathrm{thickening}(\rho_i, t_i)$，利用 `IsCompact.elim_finite_subcover` 抽取有限子覆盖，结合同级至多交 2 块区间（$|k_1 - k_2| \le 1$）与 `DimHFinite.tendsto_powB_div_factorial_rpow` 导出矛盾，从而直接由 `le_dimH_of_hausdorffMeasure_ne_zero` 得 $s \le \dim_H(K)$，再令 $s \uparrow 1-\alpha$。

## 全量构建与三层公理审计结果
- **工具链**：`leanprover/lean4:v4.35.0`
- **`lake build`**：`Build completed successfully (9092 jobs)`，退出码 `0`。
- **`lake env lean Audit.lean`**：退出码 `0`，共 **144 条** `#print axioms` 声明，**`sorryAx = 0`**。
- **三层公理清单**：
  1. **Lean 基础公理**（`[propext, Classical.choice, Quot.sound]` 或其子集）：**122 条**（含本次新增 5 条 `WeightedExactDim.*` 声明）。
  2. **经典白名单公理**（`Axioms.e_transcendental`、`Axioms.pi_transcendental`、`Measure.mu_e_eq_two`）：**22 条**。
  3. **项目自加公理**：**0 条**。
- **审计日志文件**：[obl3b_audit_20261120.log](obl3b_audit_20261120.log)。

## 论文二同步与三处 SHA256 校验
- `pdflatex` 3 遍编译 [Phase2_revised.tex](../paper1_e_plus_pi/02_companion_paper/Phase2_revised.tex)：退出码 `0, 0, 0`，`0` 错误、`0` 未定义引用、`0` Overfull `\hbox`。
- 三处 `.tex`（`论文一_e_plus_pi/第二阶段修订/Phase2_revised.tex`、`papers/第二阶段_谱隙与维数.tex`、`论文二_谱隙与维数/第二阶段_谱隙与维数.tex`）SHA256 完全一致：
  `16B199F70E592560FFEB2607AA4B37C4FDE95876ADFD33B5C6D455A54F61BF9B`
- 三处 `.pdf`（`论文一_e_plus_pi/第二阶段修订/Phase2_revised.pdf`、`papers/第二阶段_谱隙与维数.pdf`、`论文二_谱隙与维数/第二阶段_谱隙与维数.pdf`）SHA256 完全一致：
  `F3F4A4D98A0605D4AD43FCBA1A1C1F91E735E85A3EC36ECA17BD2499DE44BFB3`

## 明确写明它没做到什么
1. **没有推进 $e+\pi$ 无理性**（$e+\pi$ 无理性仍为公开问题）。
2. **没有形式化论文二的其余纸面定理**：临界规范测度（Theorem `\ref{thm:gauge}`）、无穷水平集满测度、窗口结果（Theorems `\ref{thm:windows}`–`\ref{thm:no-short-dim}`）与模 4 剩余比较（Theorem `\ref{thm:residues}`）仍为纸面证明。
3. **没有覆盖临界情形 $\alpha = 1$ 的下界**：$\alpha = 1$ 时 $1 - \alpha = 0$，由 `DimHFinite.dimH_levelSet_finite` 已给出全有限子水平集维数为 $0$，无需正维数下界。
