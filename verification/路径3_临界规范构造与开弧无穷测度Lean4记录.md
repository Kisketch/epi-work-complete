# 路径 3：显式临界规范构造、任意非空开弧无穷测度（含 $\mathbb{R}$ 与 $\mathbb{R}/\mathbb{Z}$）及二进规范下界 Lean 4 形式化记录

> **一句总判断**：已在独立模块 [GaugeCircle.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GaugeCircle.lean) 中无条件形式化构造了论文二 §6 的显式分片线性规范函数 `interpGauge`（实例化 `critGauge k` 与 `binaryGauge`），消除了 `GaugeExact` 中外部 `hm_cont` 假设并完整实例化 Theorem 13（含幂规范族 $g_\beta$ 阈值相变、Corollary 14(iii) 与 Remark 15 相邻能级分离），证明了 Corollary 14(i) 在 $\mathbb{R}$ 上任意非空开区间 $(a, b)$ 内的 $\mathcal{H}^{h_k}$ 无穷测度定理、补全了 Theorem 16(ii) 无符号精确极限集 $E_{\mathrm{lim}}(k/4)$ 在普适规范 `binaryGauge` 下的 $2$-叉 Cantor 树正测度与开区间无穷测度，并将上述全部结论通过自然投影 $1$-Lipschitz 上界与宽度 $\le 1/2$ 局部等距嵌入直接迁移到商群度量空间 `UnitAddCircle`（$\mathbb{R}/\mathbb{Z}$）；经单文件命令 `& "$env:USERPROFILE\.elan\bin\lake.exe" env lean EpiFormal/GaugeCircle.lean` 实测通过（退出码 `0`，零警告、零 `sorry`，53 条导出声明全部仅依赖 Lean 基础公理 `[propext, Classical.choice, Quot.sound]`）。本工作**属于沿 $e$ 选定收敛子分母的度量丢番图逼近谱与形式化核查，不推进也不解决 $e+\pi$ 无理性公开问题**。

---

## 0. 诚实分类与核查总表（遵守 `AGENTS.md`）

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| `interpGauge` / `critGauge` / `binaryGauge`（分片线性插值规范构造、单调性、连续性含 $0^+$ 与 $\top$、端点值 $h_k(1/Q_n)=(2k+1)^{-n}$、$g_2(1/Q_n)=2^{-n}$ 及分段仿射公式） | 5. 文献核查与复现（论文二 §6 定义的 Lean 4 显式形式化构造与验证） | 已核实（`lake env lean EpiFormal/GaugeCircle.lean` 退出码 `0`，仅基础公理） | 对应论文二 §6 临界规范 $h_k$ 与普适二进规范 $g_2$ 的显式定义 | [GaugeCircle.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GaugeCircle.lean) |
| Theorem 13、Corollary 14(ii)(iii)、Remark 15 无外部连续性假设完整版（含 $\mathbb{R}$ 与 `UnitAddCircle` 上 $g_\beta$ 相变与相邻能级分离） | 5. 文献核查与复现（既有论文二定理的 Lean 4 无条件形式化核查） | 已核实（退出码 `0`，`sorryAx = 0`，仅基础公理） | 将 `GaugeNull` 与 `GaugeExact` 的抽象假设定理完全实例化到显式规范 $h_k$ 与 `UnitAddCircle`，与 CMMS `[4]` / MEA `[11]` 形成结构对比 | [GaugeCircle.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GaugeCircle.lean) |
| Corollary 14(i) 构造性证明（$\mathbb{R}$ 上任意非空开区间 $(a,b)$ 与 `UnitAddCircle` 任意非空开集/开弧上的 $\mathcal{H}^{h_k}$ 无穷测度） | 1. 无条件新结果（新的纯构造性无 Haar 唯一性证明方法，不推进 $e+\pi$）；同时完成既有 Corollary 14(i) 的 Lean 4 核查 | 已核实（退出码 `0`，`sorryAx = 0`，仅基础公理） | 不依赖 Kronecker 定理与 Haar 测度唯一性，以柱集分裂 + $\delta_j/2 \in L$ 小平移 + 局部等距嵌入直接机器核验 | [GaugeCircle.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GaugeCircle.lean) |
| Theorem 16(ii) 二进规范下界（$\mathbb{R}$ 与 `UnitAddCircle` 上 $E_{\mathrm{lim}}(k/4)$ 的 $g_2$-正测度、开弧无穷测度、$\sigma$-有限性及 $g_\beta$ 相变） | 5. 文献核查与复现（既有论文二定理的 Lean 4 无条件形式化核查） | 已核实（退出码 `0`，`sorryAx = 0`，仅基础公理） | 补齐论文二 Theorem 16(ii) 在普适规范 $g_2$ 下全部正测度、无穷测度、开弧无穷测度及圆周版本 | [GaugeCircle.lean](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/EpiFormal/GaugeCircle.lean) |

**明确边界声明（它没做到什么）**：
1. 本模块**不解决** $e+\pi$ 无理性公开问题，也不涉及 $\pi$ 侧的任何无理数性质。
2. 依主控并行分工要求，本轨道未修改 `Phase2_revised.tex`、`第一阶段_e_plus_pi.tex`、`epi_formal/EpiFormal.lean` 与 `epi_formal/Audit.lean`；因此 `GaugeCircle.lean` 目前通过单文件 `lake env lean EpiFormal/GaugeCircle.lean` 独立核验，尚未合入 `EpiFormal.lean` / `Audit.lean` 执行全项目 `lake build` 与集中 `Audit.lean` 审计（留待主控统一合入）。

---

## 1. 数学证明核心路线（Lean 4 实现要点）

### 1.1 显式分片线性规范函数 `interpGauge b`
- 令 $q_n = 1/Q_n$（`invQ n`），由 `EulerConvergents.Qsel_lt_succ` 与 `Qsel_strictMono` 得 $q_1 = 1$、$0 < q_{n+1} < q_n$ 且 $q_n \to 0$。
- 在每个区间 $[q_{n+1}, q_n]$（$n \ge 1$）定义仿射插值 `segVal b n t`，并用 `Nat.find` 定义指标函数 `interpIdx t`（对 $0 < t < 1$ 找出唯一满足 $q_{n+1} \le t < q_n$ 的 $n \ge 1$），从而定义实轴插值函数 `interpGaugeReal b`（$t \le 0$ 取 $0$，$t \ge 1$ 取 $b^{-1}$）。
- 在 $\mathbb{R}_{\ge 0\infty}$ 上定义：
  $$\mathrm{interpGauge}\ b\ x := \begin{cases} \mathrm{ENNReal.ofReal}(b^{-1}), & x \ge 1,\\ \mathrm{ENNReal.ofReal}(\mathrm{interpGaugeReal}\ b\ x.\mathrm{toReal}), & x < 1. \end{cases}$$
  - 在 $x > 1$ 的开邻域上为常值，故于 $\top$ 处自动连续；在 $x \le 1 < \top$ 处由 `ENNReal.continuousAt_toReal`、分段左/右连续并集及 $0^+$ 处的单调夹逼 $0 \le \mathrm{interpGaugeReal}\ b\ y \le b^{-n}$（$y < q_n$）直接证得全域连续性（`interpGauge_continuous`）。
- 实例化 `critGauge k := interpGauge (2 * (k : ℝ) + 1)` 与 `binaryGauge := interpGauge 2`，消除 `GaugeExact` 中外部 `hm_cont` 与上下界假设。

### 1.2 不依赖 Kronecker 与 Haar 唯一性的开区间无穷测度证明
论文二纸面证明通过 $\mathbb{R}/\mathbb{Z}$ 上 Haar 概率测度唯一性先证明 $\mathcal{H}^{h_k}(S_k) = \infty$ 再用有限 $L$-平移覆盖；在 Lean 4 中，我们采用了一套更初等且同时覆盖 `critGauge k` 与 `binaryGauge` 的统一几何论证（`mkMetric_inter_Ioo_eq_top_of_compact_tree`）：
1. **格 $L$ 的任意小正元素（`exists_mem_latticeL_pos_lt`）**：由 `Classification.Psel_odd` 与 `Qsel_odd` 知 $P_j + Q_j$ 为偶，从而
   $$\frac{\delta_j}{2} = Q_j \frac{e+1}{2} - \frac{P_j + Q_j}{2} \in L,$$
   再由 `Hermite.sign_alternation`（$0 < |\delta_j|$）与 `deltaSel_tendsto_zero`（$|\delta_j| \to 0$），直接给出任意 $\varepsilon > 0$ 下满足 $0 < y < \varepsilon$ 的 $y = |\delta_j|/2 \in L$。
2. **任意非空开区间 $(a, b)$ 内的 $L$-平移摆放（`exists_disjoint_latticeL_translates_in_Ioo`）**：对任意中心 $c$ 与半径 $r > 0$，利用 $0 < y < r$ 取步长 $s = (\lfloor 2r/y \rfloor + 1)y \in (2r, 3r) \cap L$ 与起点 $t_0 \in L$，在 $(a, b)$ 内放置至少 $N = \lfloor (b-a)/(3r) \rfloor$ 个互不相交的闭区间拷贝 $[c+t_i-r, c+t_i+r] \subseteq (a, b)$。
3. **紧致树柱集分裂与超指数爆炸**：对紧致 $b$-叉树 $K$（`cantorTreeC k` 时 $b=2k+1$；`binCantorTree k` 时 $b=2$），在第 $M$ 层将 $K$ 覆盖为 $b^M$ 个半径 $r_M = \mathrm{radC}\ k\ M \le \frac{1}{4 Q_{J+M+1}}$ 的闭区间，鸽巢原理保证至少存在一个柱集 $K' = K \cap I_M(w)$ 满足 $\mu(K') \ge c_0 / b^M$（其中 $0 < c_0 \le \mu(K)$）。将该柱集在 $(a, b_{\mathrm{end}})$ 内摆放 $N_M \ge (b_{\mathrm{end}}-a) Q_{J+M+1} - 1$ 个互不相交 $L$-平移拷贝，利用 `E` 的 $L$-不变性与 $\mu(K \setminus E) = 0$ 得
   $$\mu(E \cap (a, b_{\mathrm{end}})) \ge \frac{(b_{\mathrm{end}}-a) Q_{J+M+1} - 1}{b^M}\, c_0 \ge (b_{\mathrm{end}}-a) c_0 \frac{(J+M+1)!}{b^M} - c_0 \xrightarrow{M\to\infty} +\infty.$$

### 1.3 商群度量空间 `UnitAddCircle`（$\mathbb{R}/\mathbb{Z}$）的原生迁移
1. **$\mathbb{Z}$-不变下降**：利用 `DimHFinite.apprExponent_add_intCast` 与 `unsignedExactLimit_add_latticeL` 将 $\Lambda$、$S_k$、$\{\Lambda < k/4\}$、$\{\Lambda \le k/4\}$ 与 $E_{\mathrm{lim}}(k/4)$ 良定义地下降到 `UnitAddCircle := AddCircle (1 : ℝ)`（`circleApprExponent`、`circleExactLevel`、`circleStrictLevel`、`circleLevelSet`、`circleUnsignedExactLimitSet`）。
2. **$1$-Lipschitz 上界与 $\sigma$-有限性**：由 `UnitAddCircle.norm_eq` 与 `round_le (x - y) 0` 得 `circleProj : ℝ → UnitAddCircle` 全局 $1$-Lipschitz，故对任意单调规范 $m$ 与 $A \subseteq \mathbb{R}$ 有 `Measure.mkMetric m (circleProj '' A) ≤ Measure.mkMetric m A`（`mkMetric_circleProj_image_le`），直接将零测度（Theorem 13 严格子水平集、Corollary 14(ii)、$g_\beta$ 当 $\beta > 2k+1$ 或 $\beta > 2$）与可数有限覆盖（$\sigma$-有限性）迁移至 `UnitAddCircle`。
3. **局部等距下界与任意非空开集无穷测度**：在任何宽度 $b - a \le 1/2$ 的开区间 $(a, b)$ 上，`AddCircle.norm_coe_eq_abs_iff` 给出 `circleProj` 为等距映射；对 `UnitAddCircle` 上任一覆盖 `{t_n}`，取 `s_n := (circleProj ⁻¹' t_n) ∩ (a, b)` 可直接证明 `Measure.mkMetric m A ≤ Measure.mkMetric m (circleProj '' A)`（`mkMetric_le_circleProj_image_of_subset_Ioo`）。对 `UnitAddCircle` 上任意非空开集 $U$（包含任意非空开弧），由连续原像取宽度 $\le 1/2$ 的开区间 $(a, b) \subseteq \mathrm{circleProj}^{-1}(U)$，即刻在 `UnitAddCircle` 上原生证得 Corollary 14(i) 与 Theorem 16(ii) 的全部分支定理。

---

## 2. 实测验证与三层公理清单（53 条导出声明）

- **工具链**：`epi_formal/lean-toolchain`（`leanprover/lean4:v4.35.0`）
- **单文件核验命令**：
  ```powershell
  Set-Location epi_formal; & "$env:USERPROFILE\.elan\bin\lake.exe" env lean EpiFormal/GaugeCircle.lean
  ```
- **实测退出码**：`0`（零警告、零错误、`sorry`/`axiom` 静态检索 0 命中、`sorryAx` 计数 = `0`）

| 公理层级 | 包含公理 | 覆盖声明数 | 明细说明 |
| :--- | :--- | :---: | :--- |
| **第 1 层：Lean 基础公理** | `propext`、`Classical.choice`、`Quot.sound` | **53 / 53** | 全部 53 条 `#print axioms` 核查声明均仅依赖 `[propext, Classical.choice, Quot.sound]` |
| **第 2 层：经典白名单公理** | 无 | **0** | 不依赖 `e_transcendental`、`pi_transcendental`、`mu_e_eq_two` |
| **第 3 层：项目自加公理** | 无 | **0** | 零自加公理、零 `sorryAx` |

### 导出声明逐项清单（53 条）

**第一组：显式分片线性规范函数性质（12 条）**
1. `GaugeCircle.critGauge_zero` — $h_k(0) = 0$
2. `GaugeCircle.critGauge_mono` — `Monotone (critGauge k)`（$k \ge 1$）
3. `GaugeCircle.critGauge_continuous` — `Continuous (critGauge k)`（$k \ge 1$，含 $0^+$ 与 $\top$）
4. `GaugeCircle.critGauge_at_inv_Qsel` — $h_k(1/Q_n) = (2k+1)^{-n}$（$n \ge 1$）
5. `GaugeCircle.critGauge_ge_one` — $t \ge 1 \implies h_k(t) = (2k+1)^{-1}$
6. `GaugeCircle.critGauge_eq_segVal` — $[1/Q_{n+1}, 1/Q_n]$ 上的线性插值恒等式
7. `GaugeCircle.binaryGauge_zero` — $g_2(0) = 0$
8. `GaugeCircle.binaryGauge_mono` — `Monotone binaryGauge`
9. `GaugeCircle.binaryGauge_continuous` — `Continuous binaryGauge`
10. `GaugeCircle.binaryGauge_at_inv_Qsel` — $g_2(1/Q_n) = 2^{-n}$（$n \ge 1$）
11. `GaugeCircle.binaryGauge_ge_one` — $t \ge 1 \implies g_2(t) = 2^{-1}$
12. `GaugeCircle.binaryGauge_eq_segVal` — $g_2$ 在 $[1/Q_{n+1}, 1/Q_n]$ 上的线性插值恒等式

**第二组：$\mathbb{R}$ 上 Theorem 13、Corollary 14(i)(iii)、Remark 15 与幂规范相变（14 条）**
13. `GaugeCircle.mkMetric_critGauge_strictLevel_null` — $\mathcal{H}^{h_k}(\{\Lambda < k/4\}) = 0$
14. `GaugeCircle.mkMetric_critGauge_exactLevel_pos` — $\mathcal{H}^{h_k}(\{\Lambda = k/4\}) > 0$
15. `GaugeCircle.mkMetric_critGauge_exactLevel_eq_top` — $\mathcal{H}^{h_k}(\{\Lambda = k/4\}) = \top$
16. `GaugeCircle.critGauge_exactLevel_sigma_finite_cover` — $\{\Lambda = k/4\} \subseteq \{\Lambda \le k/4\}$ 的 $\mathcal{H}^{h_k}$-有限测度可数覆盖
17. `GaugeCircle.mkMetric_inter_Ioo_eq_top_of_compact_tree` — 紧致树柱集分裂 + $L$-平移开区间无穷测度通用引理
18. `GaugeCircle.mkMetric_critGauge_exactLevel_inter_Ioo_eq_top` — Corollary 14(i)：$\forall a < b,\ \mathcal{H}^{h_k}(\{\Lambda = k/4\} \cap (a, b)) = \top$
19. `GaugeCircle.mkMetric_critGauge_exactLevel_inter_Icc_zero_one_eq_top` — $\mathcal{H}^{h_k}(\{\Lambda = k/4\} \cap [0, 1]) = \top$
20. `GaugeCircle.mkMetric_critGauge_exactLevel_inter_eq_top_of_Ioo_subset` — 任意包含非空开区间的集合上的 $\mathcal{H}^{h_k}$ 无穷测度
21. `GaugeCircle.mkMetric_powerGauge_exactLevel_null_of_gt` — $\beta > 2k+1 \implies \mathcal{H}^{g_\beta}(\{\Lambda \le k/4\}) = \mathcal{H}^{g_\beta}(\{\Lambda = k/4\}) = 0$
22. `GaugeCircle.mkMetric_powerGauge_exactLevel_not_sigma_finite_of_lt` — $1 < \beta < 2k+1 \implies \{\Lambda = k/4\}$ 对 $\mathcal{H}^{g_\beta}$ 为 $\top$ 且非 $\sigma$-有限
23. `GaugeCircle.mkMetric_critGauge_exactLevel_not_sigma_finite_of_ratio` — Corollary 14(iii) 显式临界规范版（$h_k/g \to 0$）
24. `GaugeCircle.critGauge_adjacent_ratio_tendsto_zero` — Remark 15：$k \ge 2$ 时 $h_k(r)/h_{k-1}(r) \to 0$
25. `GaugeCircle.critGauge_adjacent_level_separation` — Remark 15：相邻能级 $S_{k-1}$ 与 $S_k$ 的规范分离

**第三组：$\mathbb{R}$ 上 Theorem 16(ii) 二进规范下界与 $g_\beta$ 相变（10 条）**
26. `GaugeCircle.mkMetric_binCantorTree_pos` — 均匀 $2$-叉 Cantor 树在连续规范下正测度
27. `GaugeCircle.unsignedExactLimit_add_latticeL` — $E_{\mathrm{lim}}(k/4)$ 的 $L$-平移不变性
28. `GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_pos` — $\mathcal{H}^{g_2}(E_{\mathrm{lim}}(k/4)) > 0$
29. `GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_inter_Ioo_eq_top` — $\forall a < b,\ \mathcal{H}^{g_2}(E_{\mathrm{lim}}(k/4) \cap (a, b)) = \top$
30. `GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_inter_Icc_zero_one_eq_top` — $\mathcal{H}^{g_2}(E_{\mathrm{lim}}(k/4) \cap [0, 1]) = \top$
31. `GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_eq_top` — $\mathcal{H}^{g_2}(E_{\mathrm{lim}}(k/4)) = \top$
32. `GaugeCircle.binaryGauge_unsignedExactLimit_sigma_finite_cover` — $E_{\mathrm{lim}}(k/4)$ 的 $\mathcal{H}^{g_2}$-有限测度可数覆盖
33. `GaugeCircle.critGauge_unsignedExactLimit_null` — $\mathcal{H}^{h_k}(E_{\mathrm{lim}}(k/4)) = 0$
34. `GaugeCircle.mkMetric_powerGauge_unsignedExactLimit_null_of_gt` — $\beta > 2 \implies \mathcal{H}^{g_\beta}(E_{\mathrm{lim}}(k/4)) = 0$
35. `GaugeCircle.mkMetric_powerGauge_unsignedExactLimit_not_sigma_finite_of_lt` — $1 < \beta < 2 \implies E_{\mathrm{lim}}(k/4)$ 对 $\mathcal{H}^{g_\beta}$ 为 $\top$ 且非 $\sigma$-有限

**第四组：圆周群 `UnitAddCircle`（$\mathbb{R}/\mathbb{Z}$）原生形式化（18 条）**
36. `GaugeCircle.mkMetric_le_mul_of_eventually_le_circle` — `UnitAddCircle` 上的规范比较引理
37. `GaugeCircle.not_countable_union_finite_of_ratio_tendsto_zero_circle` — `UnitAddCircle` 上比值趋零时的非 $\sigma$-有限性判定
38. `GaugeCircle.mkMetric_critGauge_circleStrictLevel_null` — 圆周上 $\mathcal{H}^{h_k}(\{\Lambda < k/4\}) = 0$
39. `GaugeCircle.mkMetric_circleLevelSet_null_of_subgauge` — Corollary 14(ii) 圆周原生版（$(2k+1)^n g(1/Q_n) \to 0 \implies \mathcal{H}^g(\{\Lambda \le k/4\}) = 0$）
40. `GaugeCircle.mkMetric_critGauge_circleExactLevel_inter_open_eq_top` — **Corollary 14(i) 圆周原生版**：任意非空开集/开弧 $U \subseteq \mathbb{R}/\mathbb{Z}$ 上 $\mathcal{H}^{h_k}(S_k \cap U) = \top$
41. `GaugeCircle.mkMetric_critGauge_circleExactLevel_eq_top` — **Theorem 13 圆周原生版**：$\mathcal{H}^{h_k}(S_k) = \top$
42. `GaugeCircle.mkMetric_critGauge_circleExactLevel_pos` — 圆周上 $\mathcal{H}^{h_k}(S_k) > 0$
43. `GaugeCircle.critGauge_circleExactLevel_sigma_finite_cover` — **Theorem 13 圆周原生版**：$\mathcal{H}^{h_k}$-$\sigma$-有限可数覆盖
44. `GaugeCircle.mkMetric_critGauge_circleExactLevel_not_sigma_finite_of_ratio` — **Corollary 14(iii) 圆周原生版**
45. `GaugeCircle.mkMetric_powerGauge_circleExactLevel_null_of_gt` — 圆周上 $\beta > 2k+1 \implies \mathcal{H}^{g_\beta}(S_k) = 0$
46. `GaugeCircle.mkMetric_powerGauge_circleExactLevel_not_sigma_finite_of_lt` — 圆周上 $1 < \beta < 2k+1 \implies S_k$ 对 $\mathcal{H}^{g_\beta}$ 为 $\top$ 且非 $\sigma$-有限
47. `GaugeCircle.critGauge_circleUnsignedExactLimit_null` — 圆周上 $\mathcal{H}^{h_k}(E_{\mathrm{lim}}(k/4)) = 0$
48. `GaugeCircle.binaryGauge_circleUnsignedExactLimit_sigma_finite_cover` — 圆周上 $E_{\mathrm{lim}}(k/4)$ 的 $\mathcal{H}^{g_2}$-$\sigma$-有限覆盖
49. `GaugeCircle.mkMetric_binaryGauge_circleUnsignedExactLimit_inter_open_eq_top` — **Theorem 16(ii) 圆周原生版**：任意非空开集/开弧上 $\mathcal{H}^{g_2}(E_{\mathrm{lim}}(k/4) \cap U) = \top$
50. `GaugeCircle.mkMetric_binaryGauge_circleUnsignedExactLimit_eq_top` — 圆周上 $\mathcal{H}^{g_2}(E_{\mathrm{lim}}(k/4)) = \top$
51. `GaugeCircle.mkMetric_binaryGauge_circleUnsignedExactLimit_pos` — 圆周上 $\mathcal{H}^{g_2}(E_{\mathrm{lim}}(k/4)) > 0$
52. `GaugeCircle.mkMetric_powerGauge_circleUnsignedExactLimit_null_of_gt` — 圆周上 $\beta > 2 \implies \mathcal{H}^{g_\beta}(E_{\mathrm{lim}}(k/4)) = 0$
53. `GaugeCircle.mkMetric_powerGauge_circleUnsignedExactLimit_not_sigma_finite_of_lt` — 圆周上 $1 < \beta < 2 \implies E_{\mathrm{lim}}(k/4)$ 对 $\mathcal{H}^{g_\beta}$ 为 $\top$ 且非 $\sigma$-有限

---

## 3. 可无缝合入 `Phase2_revised.tex`（§6 与 §9）的精确 LaTeX 段落草稿

> 注：合入时须同步将 `EpiFormal/GaugeCircle.lean` 加入 `EpiFormal.lean` 与 `Audit.lean` 并运行全项目 `lake build` 与 `lake env lean Audit.lean` 审计。

### 3.1 建议合入 §6.1（替换原第 1300–1326 行 `\paragraph{Lean status.}`）

```latex
\paragraph{Lean status.}
The null part \eqref{eq:strict-null} is kernel-checked at Layer~A in
\texttt{EpiFormal/\allowbreak GaugeNull.lean} as
\texttt{GaugeNull.\allowbreak mkMetric\_\allowbreak strictLevel\_\allowbreak null}
for any nondecreasing function $m:\R_{\ge0\infty}\to\R_{\ge0\infty}$ satisfying
$m(1/Q_n)\le C(2k+1)^{-n}$ ($n\ge1$), without requiring continuity of $m$; the
same module kernel-checks Corollary~\ref{cor:exact-gauge}(ii) on $\R$ as
\texttt{GaugeNull.\allowbreak mkMetric\_\allowbreak levelSet\_\allowbreak null\_\allowbreak of\_\allowbreak subgauge}.
In \texttt{EpiFormal/\allowbreak GaugeExact.lean}, $L$-translation invariance
(\texttt{exactLevel\_\allowbreak add\_\allowbreak latticeL}), the countable
finite-measure covering
(\texttt{exactLevel\_\allowbreak countable\_\allowbreak cover\_\allowbreak finite\_\allowbreak mkMetric}),
and---for arbitrary monotone continuous $m$ satisfying matching two-sided
bounds---the Cantor-tree lower bound
(\texttt{mkMetric\_\allowbreak cantorTree\_\allowbreak pos}), exact-level
positivity (\texttt{mkMetric\_\allowbreak exactLevel\_\allowbreak pos}),
exact-level infinitude on $\R$
(\texttt{mkMetric\_\allowbreak exactLevel\_\allowbreak eq\_\allowbreak top}),
and the non-$\sigma$-finiteness criterion
(\texttt{not\_\allowbreak countable\_\allowbreak union\_\allowbreak finite\_\allowbreak of\_\allowbreak ratio\_\allowbreak tendsto\_\allowbreak zero})
are likewise kernel-checked.

The external continuity hypothesis, the explicit piecewise-linear gauge
construction, and the native quotient-metric circle statements on
\texttt{UnitAddCircle} ($\R/\Z$) are completely discharged in
\texttt{EpiFormal/\allowbreak GaugeCircle.lean}:
the gauges $h_k$ (\texttt{critGauge k}), $g_2$ (\texttt{binaryGauge}), and
$g_\beta$ (\texttt{interpGauge \ensuremath{\beta}}) are constructed explicitly
with kernel-checked monotonicity (\texttt{critGauge\_\allowbreak mono}),
continuity on $\R_{\ge0\infty}$ including $0^+$ and $\infty$
(\texttt{critGauge\_\allowbreak continuous}), and exact endpoint and segment
values (\texttt{critGauge\_\allowbreak at\_\allowbreak inv\_\allowbreak Qsel},
\texttt{critGauge\_\allowbreak eq\_\allowbreak segVal}).
This yields the assumption-free instantiations of Theorem~\ref{thm:gauge},
Corollary~\ref{cor:exact-gauge}(i)--(iii), and Remark~\ref{rem:gauge-scale} both
on $\R$
(\texttt{mkMetric\_\allowbreak critGauge\_\allowbreak strictLevel\_\allowbreak null},
\texttt{mkMetric\_\allowbreak critGauge\_\allowbreak exactLevel\_\allowbreak pos},
\texttt{mkMetric\_\allowbreak critGauge\_\allowbreak exactLevel\_\allowbreak eq\_\allowbreak top},
\texttt{critGauge\_\allowbreak exactLevel\_\allowbreak sigma\_\allowbreak finite\_\allowbreak cover},
\texttt{mkMetric\_\allowbreak critGauge\_\allowbreak exactLevel\_\allowbreak inter\_\allowbreak Ioo\_\allowbreak eq\_\allowbreak top},
\texttt{mkMetric\_\allowbreak powerGauge\_\allowbreak exactLevel\_\allowbreak null\_\allowbreak of\_\allowbreak gt},
\texttt{mkMetric\_\allowbreak powerGauge\_\allowbreak exactLevel\_\allowbreak not\_\allowbreak sigma\_\allowbreak finite\_\allowbreak of\_\allowbreak lt},
and \texttt{critGauge\_\allowbreak adjacent\_\allowbreak level\_\allowbreak separation})
and natively on \texttt{UnitAddCircle} ($\R/\Z$)
(\texttt{mkMetric\_\allowbreak critGauge\_\allowbreak circleStrictLevel\_\allowbreak null},
\texttt{mkMetric\_\allowbreak circleLevelSet\_\allowbreak null\_\allowbreak of\_\allowbreak subgauge},
\texttt{mkMetric\_\allowbreak critGauge\_\allowbreak circleExactLevel\_\allowbreak inter\_\allowbreak open\_\allowbreak eq\_\allowbreak top},
\texttt{mkMetric\_\allowbreak critGauge\_\allowbreak circleExactLevel\_\allowbreak eq\_\allowbreak top},
\texttt{critGauge\_\allowbreak circleExactLevel\_\allowbreak sigma\_\allowbreak finite\_\allowbreak cover},
\texttt{mkMetric\_\allowbreak critGauge\_\allowbreak circleExactLevel\_\allowbreak not\_\allowbreak sigma\_\allowbreak finite\_\allowbreak of\_\allowbreak ratio},
\texttt{mkMetric\_\allowbreak powerGauge\_\allowbreak circleExactLevel\_\allowbreak null\_\allowbreak of\_\allowbreak gt},
and
\texttt{mkMetric\_\allowbreak powerGauge\_\allowbreak circleExactLevel\_\allowbreak not\_\allowbreak sigma\_\allowbreak finite\_\allowbreak of\_\allowbreak lt}),
proved constructively by splitting the Cantor tree into depth-$M$ cylinders,
packing $\Omega\bigl((b-a)Q_{J+M+1}\bigr)$ disjoint $L$-translates using
$\delta_j/2\in L$, and transferring across the local isometry
$\R\to\R/\Z$ on intervals of length $\le1/2$. For the binary exact-limit
regime of Theorem~\ref{thm:trichotomy}(ii), the binary Cantor-tree lower bound,
global and open-set $\mathcal H^{g_2}$-infinitude, $\sigma$-finite covering,
$\mathcal H^{h_k}$-nullity, and the $g_\beta$ threshold dichotomy ($\beta>2$ vs.\
$1<\beta<2$) are likewise kernel-checked on both $\R$ and \texttt{UnitAddCircle}
(\texttt{mkMetric\_\allowbreak binaryGauge\_\allowbreak unsignedExactLimit\_\allowbreak pos},
\texttt{mkMetric\_\allowbreak binaryGauge\_\allowbreak unsignedExactLimit\_\allowbreak inter\_\allowbreak Ioo\_\allowbreak eq\_\allowbreak top},
\texttt{mkMetric\_\allowbreak binaryGauge\_\allowbreak circleUnsignedExactLimit\_\allowbreak inter\_\allowbreak open\_\allowbreak eq\_\allowbreak top},
\texttt{mkMetric\_\allowbreak binaryGauge\_\allowbreak circleUnsignedExactLimit\_\allowbreak eq\_\allowbreak top},
\texttt{binaryGauge\_\allowbreak circleUnsignedExactLimit\_\allowbreak sigma\_\allowbreak finite\_\allowbreak cover},
\texttt{critGauge\_\allowbreak circleUnsignedExactLimit\_\allowbreak null},
\texttt{mkMetric\_\allowbreak powerGauge\_\allowbreak circleUnsignedExactLimit\_\allowbreak null\_\allowbreak of\_\allowbreak gt},
and
\texttt{mkMetric\_\allowbreak powerGauge\_\allowbreak circleUnsignedExactLimit\_\allowbreak not\_\allowbreak sigma\_\allowbreak finite\_\allowbreak of\_\allowbreak lt}).
All 53 audited declarations in \texttt{GaugeCircle.lean} report only
\texttt{propext}, \texttt{Classical.choice}, and \texttt{Quot.sound}, with zero
\texttt{sorryAx}.
```

### 3.2 建议合入 §9（替换原第 2382–2403 行 `Honesty statement` 第 5 项及第 2439–2443 行 `Use of AI` 对应句）

```latex
\item Theorem~\ref{thm:gauge}, Corollary~\ref{cor:exact-gauge},
Remark~\ref{rem:gauge-scale}, and Theorem~\ref{thm:trichotomy}(ii) are now
\emph{fully machine-checked at Layer~A} both on $\R$ and natively on the
quotient metric space $\R/\Z$ (\texttt{UnitAddCircle}) across
\texttt{EpiFormal/\allowbreak GaugeNull.lean} (3 declarations),
\texttt{EpiFormal/\allowbreak GaugeExact.lean} (22 declarations), and
\texttt{EpiFormal/\allowbreak GaugeCircle.lean} (53 declarations), using only
the three Lean base axioms \texttt{propext}, \texttt{Classical.choice}, and
\texttt{Quot.sound}, with zero \texttt{sorryAx}. In particular,
\texttt{GaugeCircle.lean} explicitly constructs the piecewise-linear gauges
$h_k$ (\texttt{critGauge}), $g_2$ (\texttt{binaryGauge}), and $g_\beta$
(\texttt{interpGauge}), discharges all external continuity hypotheses for
Theorem~\ref{thm:gauge} and Remark~\ref{rem:gauge-scale}, constructively proves
open-interval and open-arc $\mathcal H^{h_k}$-infinitude
(Corollary~\ref{cor:exact-gauge}(i) on $\R$ and \texttt{UnitAddCircle}), and
verifies the binary Cantor-tree positivity, $\mathcal H^{g_2}$-infinitude on
every nonempty open subset of $\R/\Z$, $\sigma$-finiteness,
$\mathcal H^{h_k}$-nullity, and $g_\beta$ threshold dichotomy for
$E_{\mathrm{lim}}(k/4)$ in Theorem~\ref{thm:trichotomy}(ii).
```

*(并在 `Use of AI and formal verification` 末尾相应收窄未形式化范围为：)*
```latex
The paper proofs (the full continued-fraction measure ergodicity and
Hausdorff-dimension pressure arguments in
Theorems~\ref{thm:windows}--\ref{thm:residues} beyond the 14 core lemmas in
\texttt{WindowAndResidueCore.lean}) are not machine-checked in Lean.
```
