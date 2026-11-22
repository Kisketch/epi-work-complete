# thm:no-short-dim 形式化设计文档（paper2 triage 第 4 项）

> 生成日期：2026-11-21 ｜ 性质：纯分析（未运行任何 Lean/lake，未修改任何 `.lean`）
> 唯一写出的文件：本文件。
> 采信范围：仅本工作区实际打开的文件与行号；未能打开核实的条目一律写「未核到」。
> 基线不变：$e+\pi$ 的无理性仍是公开问题；本文档与该问题无关，不构成任何关于 $e+\pi$ 的结论。

## 0. 一句总判断

**thm:no-short-dim 的数值骨架（终端分母包络、跨阈值、$m/n\in(2,3)$）已有 3 条仅依赖基础三公理的已核实引理（另有 `WindowMobiusCount` 的 5 条通用计数件，未接入审计），但证明主体的四块（连分数圆柱基础设施、Fibonacci 前缀块、Möbius 计数渐近、质量分布原理）在 `epi_formal` 中全部不存在，其中「连分数圆柱基础设施」是整个工作区级的单点阻塞；与 thm:finite 的同构度偏低（约 30%，方向相反），真正可复用的模板是 `WeightedExactDim` 的 Cantor/Frostman 构造。**

类别定位：本任务属第 5 类「文献核查与复现（核查既有结果的可形式化性）」，不产生新的数学结论。

---

## 1. 纸面锚点（逐条行号，均为实读）

文件：`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`（全文 3346 行）。

### 1.1 记号与阈值

| 行号 | 逐字内容（摘） | 作用 |
|---|---|---|
| L200–203 | `\label{eq:rec}`；`Q_{j+1}=(4j+2)Q_j+Q_{j-1}\quad(j\ge2),\qquad Q_1=1,\ Q_2=7` | 唯一递推来源，后续一切比值估计的根 |
| L2400–2402 | `Put $H_j=\lfloor Q_j\sqrt j\rfloor$. For irrational $x\in(0,1)$ let $k(j)$ be its last convergent index with denominator at most $H_j$ (the integer part has index zero) and $r_j=k(j+1)-k(j)$.` | 三个待定义量 $H_j,k(j),r_j$ |
| L2734–2735 | `Let $\varphi=(1+\sqrt5)/2$` | 黄金比，仅在指数 $1-\eta\log\varphi$ 出现 |

### 1.2 被改造的原构造（thm:windows）

| 行号 | 逐字内容（摘） | 作用 |
|---|---|---|
| L2404–2411 | thm:windows 陈述 | 提供「停止柱 + 不变式」范式 |
| L2414–2416 | `$Q_{j+1}/Q_j=4j+O(1)$`、`$H_{j+1}/H_j=4j+O(1)\asymp j$`、`$\log H_j=j\log j+O(j)$` | 三条比值估计（**全部为 $O$ 记号，无显式常数**） |
| L2421–2425 | `$I(a_1,\dots,a_r)$` 是闭区间，端点 `$\frac{p_r}{u}$` 与 `$\frac{p_r+p_{r-1}}{u+v}$`，长度 `$=\frac{1}{u(u+v)}\in[\frac{1}{2u^2},\frac{1}{u^2}]$` | 圆柱几何 |
| L2426–2431 | 停在首个跨越 $H_j$ 的 $\tau_j=k(j)+1$，维持 `$\frac43 H_j\le u\le \frac52 H_j$` | 核心不变式 |
| L2432–2434 | 末位部分商 $a_{\tau_j}=4$ ⇒ `$u=4v+q_{\tau_j-2}>4v$`，即 `$v<u/4$` | 第二不变式 |
| L2447–2465 | Möbius 反演计数：`$\frac{0.0004}{\zeta(2)}R^2+O(R\log R)$`，矩形 `$[0.34R,0.36R]\times[0.20R,0.22R]$` | ζ(2) 密度的出处 |
| L2477–2485 | `$t=mu+nv$` 与 $m/n$ 两种终端表示无关；`$1\le t'<t$` | continuant 恒等式（**纸面**） |
| L2494–2504 | 追加 $4$：`$u_{\mathrm{new}}=4t+t'$`，`$\frac43T<u_{\mathrm{new}}<\frac52T$` | 跨阈值 |
| L2536–2559 | 等分质量、`$\mu(I_j)\le\exp(-bj\log j+O(j))$`、`$\le 15$`（+2 端点）→ `$\le 17$`、`$O(h^s)$`、mass distribution ⇒ `$\dimH\ge b/2$` | 下界模板 |
| L2561–2595 | `$\sum_{a_1..a_n}d_n^{-2t}\le\zeta(2t)^n<\infty$`，取 $M>\frac{\log\zeta(2t)}{2(s-t)}$ ⇒ $\dimH\le1/2$ | **ζ(2t) 上界只在这里**，属 thm:windows 的「有界 $r_j$」支 |

### 1.3 目标定理本体

| 行号 | 逐字内容（摘） | 作用 |
|---|---|---|
| L2733–2741 | 陈述：`For any $0<\eta<1/\log\varphi$`, `$r_j(x)\ge\eta\log j$` 且 `$k(j)\equiv\epsilon_j\pmod2$` eventually ⇒ `$\dimH\ge1-\eta\log\varphi$`；`$r_j(x)\to\infty$` + 既定偶奇 ⇒ `dimension one and Lebesgue measure zero` | 三个断言：(a) 给定 $\eta$ 的下界 (b) $\dimH=1$ (c) Lebesgue 零 |
| L2743–2751 | 从 `Theorem~\ref{thm:windows}` 的停止柱改造，`$a_{\tau_j}=4$`，`$\frac43H_j\le u\le\frac52H_j$`，`$0<v\le u/4$` | 初始化 |
| L2752–2757 | `$\ell_j:=\lceil\eta\log j\rceil$` 个 $1$；`$\begin{pmatrix}1&1\\1&0\end{pmatrix}^{\ell_j}=\begin{pmatrix}F_{\ell_j+1}&F_{\ell_j}\\F_{\ell_j}&F_{\ell_j-1}\end{pmatrix}$` | Fibonacci 块 |
| L2758–2767 | `$u'=F_{\ell_j+1}u+F_{\ell_j}v$`，`$0<v'\le u'$`，`$u\le u'\le F_{\ell_j+2}u\le\varphi^{\ell_j+1}u\le\varphi^2j^{\eta\log\varphi}u$` | 放大界 |
| L2768–2777 | `$R:=T/u'$`，`$R\ge c_1 j^{1-\eta\log\varphi}$`；`$\gamma:=1-\eta\log\varphi>0$` | 尺度比 |
| L2779–2785 | 矩形 `$\mathcal R'_R:=[0.34R,0.35R]\times[0.12R,0.13R]$`，互素对数 `$=\frac{0.01\times0.01}{\zeta(2)}R^2+O(R\log R)\gg R^2\ge c_2 j^{2\gamma}$` | 分支数（*新矩形*，与 thm:windows 的 0.34–0.36×0.20–0.22 不同） |
| L2786–2794 | `$2<\frac{34}{13}\le\frac mn\le\frac{35}{12}<3$`，$\lfloor m/n\rfloor=2$，两种表示长度奇偶相反、均 $\ge2$ | 组合事实 |
| L2796–2804 | `$t=mu'+nv'$`；`$\frac13T<0.34T<\dots<t\le0.48T<\frac12T$` | 终端分母 |
| L2805–2813 | 追加 $4$：`$\frac43T<4t<u_{\mathrm{new}}<5t<\frac52T$`，`$v_{\mathrm{new}}=t<u_{\mathrm{new}}/4$`，首次跨越在末位 $4$ | 闭合不变式 |
| L2814–2816 | `$r_j=\tau_{j+1}-\tau_j=\ell_j+\operatorname{len}(m/n)+1\ge\ell_j+3>\eta\log j$` | 窗口下界 |
| L2817–2820 | 不同 $(m,n)$ ⇒ 子柱内部不交（首次跨越 ⇒ 无前缀关系） | 不交性 |
| L2822–2828 | 每层 `$\ge c_2 j^{2\gamma}$` 子；`$\mu\le\prod_{i=j_0}^{j-1}(c_2^{-1}i^{-2\gamma})=\exp(-2\gamma j\log j+O(j))$`；长 `$\asymp H_j^{-2}$`；任意区间至多 $17$ 个柱；`$O(h^s)$` | 质量分布四步 |
| L2828–2829 | `The mass distribution principle yields Hausdorff dimension at least $\gamma=1-\eta\log\varphi$` | 关键黑箱名 |
| L2829–2835 | `letting $\eta\downarrow0$ shows ... dimension 1`；`Theorem~\ref{thm:short-ae} implies ... Lebesgue measure zero` | 两条收尾 |
| L2838–2841 | 推论：最终 $r_j\ge3$ ⇒ 零测 + 满维 | 陈述的通俗版 |

### 1.4 依赖的姊妹定理

| 行号 | 内容 | 状态 |
|---|---|---|
| L2610–2616 | thm:short-ae：`$\#\{1\le j\le J:r_j(x)\le1\}\ge c\log J$` a.e. | 形式化仅完成抽象骨架（见 §5 R1） |
| L2618–2726 | 其证明（停时柱 σ-域、条件密度、指数矩、Markov、Borel–Cantelli、dyadic 延拓） | 对应 `WindowShortAe.short_ae_main` |

---

## 2. 陈述拆解与形式化目标

纸面陈述含三个可分离断言（L2733–2741）：

- **(a) 参数化下界**：$\forall\eta\in(0,1/\log\varphi)$，$\forall(\epsilon_j)\in\{0,1\}^{\mathbb N}$，
  $\dimH\{x: \exists j_0\,\forall j\ge j_0,\ r_j(x)\ge\eta\log j\ \wedge\ k(j)\equiv\epsilon_j\ (2)\}\ \ge\ 1-\eta\log\varphi$。
- **(b) 满维**：$\dimH\{x: \exists j_0\forall j\ge j_0,\,k(j)\equiv\epsilon_j(2);\ r_j(x)\to\infty\}=1$。
- **(c) 零测**：同 (b) 之集合 Lebesgue 测度为 $0$。

Lean 侧建议骨架（伪代码，非可编译代码）：

```
theorem no_short_dim_partial (ε : ℕ → ZMod 2) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1 / Real.log Real.goldenRatio) :
    ENNReal.ofReal (1 - η * Real.log Real.goldenRatio) ≤
      dimH {x : ℝ | 0 < x ∧ x < 1 ∧ ∃ j0, ∀ j, j0 ≤ j →
        η * Real.log (j:ℝ) ≤ (r j x : ℝ) ∧ (k j x : ℤ) ≡ ε j [ZMOD 2]}

theorem no_short_dim_full (ε : ℕ → ZMod 2) :
    dimH {x : ℝ | 0 < x ∧ x < 1 ∧ (∀ᶠ j in atTop, (k j x : ℤ) ≡ ε j [ZMOD 2]) ∧
          Tendsto (fun j => r j x) atTop atTop} = 1
    ∧ volume {x : ℝ | ...同上...} = 0
```

三处必须显式化的定义（工作区当前**均无**，见 §5 R2）：`H : ℕ → ℕ`（$=\lfloor Q_j\sqrt j\rfloor$）、`k : ℕ → ℝ → ℤ`、`r : ℕ → ℝ → ℤ`。

---

## 3. 引理清单（可独立形式化单元）

类别口径：**已有**＝`epi_formal` 中已核实（有 `#print axioms` 日志行号）；**需新建**＝工作区无，须自建；**mathlib**＝可直接引用（签名见 §4）。「工作量」列是**经验估算（未实测）**，仅供排期参考。

| ID | 目标（形式化要点） | 类别 | 依据 | 工作量 |
|---|---|---|---|---|
| **M1 阈值与数值骨架** | | | | |
| L01 | $4j+2\le Q_{j+1}/Q_j\le 4j+3$（$j\ge1$），进而 $H_{j+1}/H_j\in[3j,5j]$ 型双侧界 | 需新建（拼装已有） | 递推：`DimHCore.Qsel_rec1`(L48) + `Qsel_succ_le`(L56)；均见 `audit_after_track3.log:93` | 0.5 天，`linarith` 级 |
| L02 | 停止柱不变式 $(4/3)H\le u\le(5/2)H,\ 0<v\le u/4$ 在「先 $\ell$ 个 $1$、再 $m/n$、再 $4$」后仍成立 | 需新建 | 纸面 L2750, L2805–2810 | 1 天（无实质数学，靠 L03/L08 传递） |
| L03 | Fibonacci 块：$u'=F_{\ell+1}u+F_\ell v$，且 $u\le u'\le\varphi^{\ell+1}u$ | 需新建 | 纸面 L2754–2766 | 2 天（矩阵幂 + Binet 界） |
| L04 | $R=T/u'\ge c_1 j^{1-\eta\log\varphi}$（$c_1$ 显式） | 需新建 | 纸面 L2768–2773 | 1 天（接 L01/L03） |
| L05 | $0<\eta<1/\log\varphi\Rightarrow\gamma:=1-\eta\log\varphi>0$，且 $\log\varphi>0$ | 需新建（初等） | 纸面 L2774–2775 | 0.5 天 |
| L06 | 新矩形 $[0.34R,0.35R]\times[0.12R,0.13R]$ 内互素对数 $\ge c_2R^2$ 或 $\ge c_2'j^{2\gamma}$ | **部分已有 / 渐近部分需新建** | 已有通用件：`WindowMobiusCount.countMultiples`(L138)、`intervalCount`(L178)、`moebius_indicator`(L221)、`prod_filter_eq`(L253)、`coprime_count_eq`(L267)；**缺**：新常数矩形的代入 + 渐近下界（`coprime_count_ge` 不存在，见 §5 R6） | 2–3 天 |
| **M2 组合/连分数事实** | | | | |
| L07 | $m/n\in(2,3)$ | **已有** | `WindowAndResidueCore.thm20_rational_between_two_and_three`(L136)；`audit_after_track3.log:226` | 0 |
| L08 | $t=mu'+nv'\in(T/3,T/2)$ 且追加 $4$ 后 $u_{\text{new}}\in(4T/3,5T/2)$ | **已有** | `WindowAndResidueCore.thm20_terminal_denom_bounds`(L154)；`audit_after_track3.log:227` | 0 |
| L09 | 有理数 $m/n>1$ 的两个正则展开长度分别为 $s,s+1$，$s\ge2$，末位商 $\ge2$ | 需新建 | 纸面 L2790–2794, L2471 | 2–3 天（需连分数/continuant 基础） |
| L10 | 追加任一表示后终端分母同为 $t=mu'+nv'$（continuant 恒等式） | 需新建 | 纸面 L2472–2485（thm:windows 内已有，但无 Lean） | 3 天（矩阵恒等式，需 L09 的基础） |
| L11 | $r_j=\ell_j+\operatorname{len}(m/n)+1\ge\ell_j+3>\eta\log j$ | 需新建 | 纸面 L2814–2816 | 1 天（依赖 L09 + 奇偶记账） |
| L12 | 不同 $(m,n)$ 的子柱内部不交 | 需新建 | 纸面 L2817–2820 | 2 天（停止词前缀无关性） |
| **M3 几何与质量** | | | | |
| L13 | 第 $j$ 层柱长 $\asymp H_j^{-2}$；任意区间至多 $17$ 个第 $j$ 层柱 | 需新建 | 纸面 L2545–2551（被 L2826 引用） | 2 天 |
| L14 | 等分质量：$\mu(I_j)\le\exp(-2\gamma j\log j+O(j))$（显式常数版） | 需新建 | 纸面 L2822–2824 | 2 天（乘积 telescopes） |
| L15 | 质量分布原理：$\forall s<\gamma$，$\muH[s](\text{构造集})>0$ ⇒ $\dimH\ge\gamma$ | 需新建（mathlib 无） | 纸面 L2828–2829 | 5–8 天（最大单件；可仿 `WeightedExactDim.one_le_hausdorffMeasure_cantorSet`，见 §5.2） |
| L16 | 由 $\forall s<\gamma$ 得 $\mathrm{ofReal}\,\gamma\le\dimH$ | 需新建（小技巧） | 模板：`WeightedExactDim.lean:1276–1296`（`by_contra` + `max` 取中点） | 0.5 天 |
| **M4 组装与测度零** | | | | |
| L17 | $\eta\downarrow0$ ⇒ $\dimH=1$（建议改用可数序列 $\eta_n=1/(n\log\varphi)$） | 需新建 | 纸面 L2831–2833；`dimH_iUnion`（mathlib） | 1 天 |
| L18 | $\dimH\le1$ 封顶 | **源码已有 / 公理状态未核到** | `GaugeExact.lean:239` `lemma dimH_real_subset_le_one (S : Set ℝ) : dimH S ≤ 1`；但该条**未单列** `#print axioms`（`Audit.lean:284–295` 列的是 GaugeExact 的另外 12 条），**须先接入审计** | 0（+接入 0.5 天） |
| L19 | $\{r_j\to\infty\}$ 的 Lebesgue 测度为 $0$ | 需新建（组装） | 纸面 L2833–2835 引 thm:short-ae | 1–2 天（但继承 R1） |
| L20 | 0 号基础设施：$\mathbb Q$ 之外 $x$ 的收敛子/分母/圆柱/`k`/`r` 定义与基本性质 | 需新建（**阻塞级**） | 工作区无（`EulerConvergents.lean:25` 明文）；mathlib 亦无（同处原文） | 2–4 周（见 R2） |

覆盖度估计：L07/L08 两条零成本（L18 需补审计接入）；加上 `WindowMobiusCount` 的 5 条通用件（未审计）后，纸面证明工作量约 **12–15%** 已在手；L20 一项即占 **50% 以上**。

---

## 4. mathlib 现货（仅列已核实签名原文）

以下每条均实读自 `epi_formal/.lake/packages/mathlib/Mathlib/…`，路径与行号可复查。**未核实者不入表。**

### 4.1 Hausdorff 维数 API
文件 `Topology/MetricSpace/HausdorffDimension.lean`：

| 行 | 签名原文 |
|---|---|
| 98–99 | `@[irreducible] noncomputable def dimH (s : Set X) : ℝ≥0∞ := by borelize X; exact ⨆ (d : ℝ≥0) (_ : @hausdorffMeasure X _ _ ⟨rfl⟩ d s = ∞), d` |
| 115 | `theorem hausdorffMeasure_of_lt_dimH {s : Set X} {d : ℝ≥0} (h : ↑d < dimH s) : μH[d] s = ∞` |
| 124 | `theorem dimH_le_of_hausdorffMeasure_ne_top {s : Set X} {d : ℝ≥0} (h : μH[d] s ≠ ∞) : dimH s ≤ d` |
| 131 | `theorem hausdorffMeasure_of_dimH_lt {s : Set X} {d : ℝ≥0} (h : dimH s < d) : μH[d] s = 0` |
| 143 | `theorem le_dimH_of_hausdorffMeasure_ne_zero {s : Set X} {d : ℝ≥0} (h : μH[d] s ≠ 0) : ↑d ≤ dimH s` |
| 168 | `theorem dimH_mono {s t : Set X} (h : s ⊆ t) : dimH s ≤ dimH t` |
| 189–190 | `theorem dimH_iUnion {ι : Sort*} [Countable ι] (s : ι → Set X) : dimH (⋃ i, s i) = ⨆ i, dimH (s i)` |
| 200–201 | `theorem dimH_bUnion {s : Set ι} (hs : s.Countable) (t : ι → Set X) : dimH (⋃ i ∈ s, t i) = ⨆ i ∈ s, dimH (t i)` |
| 206 | `theorem dimH_sUnion {S : Set (Set X)} (hS : S.Countable) : dimH (⋃₀ S) = ⨆ s ∈ S, dimH s` |
| 210 | `theorem dimH_union (s t : Set X) : dimH (s ∪ t) = max (dimH s) (dimH t)` |

→ 直接支撑 L15 的最后一步、L16、L17、L18。**注意 `dimH_iUnion` 要求 `[Countable ι]`**：这正是 §5 R5 建议把 $\eta\downarrow0$ 改成可数序列的理由。

### 4.2 测度零
`MeasureTheory/OuterMeasure/Basic.lean`：

| 行 | 签名原文 |
|---|---|
| 52 | `theorem measure_mono_null (h : s ⊆ t) (ht : μ t = 0) : μ s = 0` |
| 116–117 | `theorem measure_iUnion_null_iff {ι : Sort*} [Countable ι] {s : ι → Set α} : μ (⋃ i, s i) = 0 ↔ ∀ i, μ (s i) = 0` |
| 120 | `alias ⟨_, measure_iUnion_null⟩ := measure_iUnion_null_iff` |
| 123 | `theorem measure_union_null_iff : μ (s ∪ t) = 0 ↔ μ s = 0 ∧ μ t = 0` |

`MeasureTheory/OuterMeasure/AE.lean`：

| 行 | 签名原文 |
|---|---|
| 330 | `theorem measure_mono_null_ae (H : s ≤ᵐ[μ] t) (ht : μ t = 0) : μ s = 0` |

→ 支撑 L19（把 thm:short-ae 的 a.e. 结论翻成测度零）。

### 4.3 黄金比与 Fibonacci
`NumberTheory/Real/GoldenRatio.lean`：

| 行 | 签名原文 |
|---|---|
| 35 | `abbrev goldenRatio : ℝ := (1 + √5) / 2` |
| 40 | `@[inherit_doc] scoped[goldenRatio] notation "φ" => Real.goldenRatio` |
| 81 | `theorem goldenRatio_sq : φ ^ 2 = φ + 1` |
| 88 | `theorem goldenRatio_pos : 0 < φ` |
| 94 | `theorem one_lt_goldenRatio : 1 < φ` |
| 196 | `theorem coe_fib_eq : ∀ n, (Nat.fib n : ℝ) = (φ ^ n - ψ ^ n) / √5` |
| 209 | `theorem fib_succ_sub_goldenRatio_mul_fib (n : ℕ) : Nat.fib (n + 1) - φ * Nat.fib n = ψ ^ n` |

`Data/Nat/Fib/Basic.lean`：

| 行 | 签名原文 |
|---|---|
| 72 | `theorem fib_add_two {n : ℕ} : fib (n + 2) = fib n + fib (n + 1)` |
| 78 | `theorem fib_le_fib_succ {n : ℕ} : fib n ≤ fib (n + 1)` |
| 81 | `theorem fib_mono : Monotone fib` |
| 89 | `@[simp] lemma fib_pos {n : ℕ} : 0 < fib n ↔ 0 < n` |

→ L03 的 $F_{\ell+2}\le\varphi^{\ell+1}$ 需自证（mathlib **无** `fib_le_goldenRatio_pow` 之类；已 rg 核实：`Analysis/SpecificLimits/Fibonacci.lean` 只有 `tendsto_fib_succ_div_fib_atTop`(L24) 与 `tendsto_fib_div_fib_succ_atTop`(L37) 两条极限）。建议路线：`fib_succ_sub_goldenRatio_mul_fib` + $|\psi|<1$ 直接给出线性型误差，或对 $F_{n+2}\le\varphi^{n+1}$ 用 `fib_add_two` 归纳。**该子引理未核到现成件，属需新建。**

### 4.4 分析基础
| 文件:行 | 签名原文 |
|---|---|
| `Analysis/SpecialFunctions/Log/Basic.lean:188` | `theorem log_pos (hx : 1 < x) : 0 < log x` |
| `Analysis/SpecialFunctions/Log/Basic.lean:155` | `theorem log_lt_log (hx : 0 < x) (h : x < y) : log x < log y` |
| `Analysis/SpecialFunctions/Pow/Real.lean:116` | `theorem rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y` |
| `Analysis/SpecialFunctions/Pow/Real.lean:550` | `theorem rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z` |
| `Analysis/PSeries.lean:317–318` | `theorem summable_one_div_nat_rpow {p : ℝ} : Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p` |
| `Analysis/PSeries.lean:330` | `theorem summable_one_div_nat_pow {p : ℕ} : Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p` |

→ $\log\varphi>0$（L05）用 `log_pos one_lt_goldenRatio`；$j^{1-\eta\log\varphi}$ 的单调性用 `rpow_le_rpow`；$\zeta(2)$ 的收敛性（thm:windows 支，非本定理必需）用 `summable_one_div_nat_rpow`。

### 4.5 Möbius
`NumberTheory/ArithmeticFunction/Moebius.lean`：

| 行 | 签名原文 |
|---|---|
| 52–53 | `def moebius : ArithmeticFunction ℤ := ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩` |
| 56 | `scoped[ArithmeticFunction.Moebius] notation "μ" => ArithmeticFunction.moebius` |
| 68 | `theorem moebius_apply_one : μ 1 = 1` |

→ L06 可直接用（`WindowMobiusCount.moebius_indicator` 已经用了它）。

### 4.6 明确**不存在**的 mathlib 件（同为已核实结论）

| 缺件 | 核实方式（实读/实搜） |
|---|---|
| 质量分布原理 / Moran 结构 | `rg "Moran"` 于整个 `Mathlib/` **0 命中**；`rg "mass distribution|massDistribution"` 仅 `Geometry/Convex/ConvexSpace/Defs.lean:129` 的无关注释 |
| 连分数（`sfrac`/`SimpleContinuedFraction`） | 本项目 `EpiFormal/EulerConvergents.lean:25–26` 原文：`mathlib v4.35.0 无 e 的连分数展开定理（全库无 sfrac/SimpleContinuedFraction，Mathlib/Algebra/ContinuedFractions/Euler.lean 是广义连分数的 Euler *变换*，非 e 展开）` |
| `fib ≤ φ^n` 型显式界 | 见 §4.3 末 |

---

## 5. 与 thm:finite 的同构评估

### 5.1 逐项对照

| 维度 | thm:finite（L569–574，`DimHFinite.dimH_levelSet_finite`） | thm:no-short-dim | 同构？ |
|---|---|---|---|
| 方向 | **上界** $\dimH E_c=0$ | **下界** $\dimH\ge\gamma$ | ✗ 相反 |
| 核心工具 | 覆盖：存活中心 `Finset` 递归 + 单步分支数一致界 | 构造：子柱树 + Frostman 质量 | ✗ |
| 增长机制 | 分支数 $B=\lfloor16t\rfloor+1$ 固定，被 $ (\text{factorial})^s$ 压过（`tendsto_powB_div_factorial_rpow`，L216） | 分支数 $\gg j^{2\gamma}$ **随层增长**，恰好吃掉 $H_j^{-2}$ 的几何衰减 | ✗（关键差别） |
| 递归对象 | `survSet t J n`（中心集，`DimHFinite:34`） | 停止柱（集合树，带前缀） | △ 形状相似 |
| 维数收尾 | `dimH_le_of_hausdorffMeasure_ne_top` 类（覆盖 ⇒ $\mathcal H^s=0$） | `le_dimH_of_hausdorffMeasure_ne_zero`（$\mathcal H^s>0$） | ✗ 对偶 |
| 可数并处理 | `dimH_iUnion` + Lipschitz 平移 | `dimH_iUnion`（$\eta$ 序列）/ 有限并 | ✓ |

**判定：同构度约 30%**，仅共享「逐层计数 + 乘积/指数估计 + `dimH` 可数并」这三件通用外壳。

### 5.2 triage 说法的更正（重要）

`verification/triage_map_paper2_20261121.md:98` 写：
> 4. **`thm:no-short-dim` 收尾**（上界 $\zeta(2t)$ 求和得 $\dimH\le1/2$＋下界 $\gamma=1-\eta\log\varphi$ 组装）：… 可行性高（初等覆盖，与 `thm:finite` 的 `tendsto_pow_div_factorial` 路数同构）。

**该表述不成立，须更正为三条**：
1. $\zeta(2t)$ 上界（L2572–2593）证明的是 **thm:windows** 中「$r_j$ 最终有界 ⇒ $\dimH\le1/2$」，与 thm:no-short-dim 的证明（L2743–2836）**无交集**；后者全程不出现 $\zeta(2t)$。
2. thm:no-short-dim 里出现的 ζ 只有 $\zeta(2)$（L2785 的互素对密度），且是**下界构造的输入**，不是求和上界。
3. 与 thm:finite 的 `tendsto_pow_div_factorial` 路数**不同构**（上界 vs 下界，见 5.1）；真正同构对象是 `WeightedExactDim` 的 Cantor 构造（5.3）。

### 5.3 真正可复用的证明模式（P1–P6，均给出实读行号）

| 模式 | 位置 | 用途 |
|---|---|---|
| **P1** 逐层分支数乘积 | `WeightedExactDim.wordCount`(L436)、`wordCount_succ`(L446)、`card_CWord`(L438) | L14 的 $\prod_i(\cdot)$ |
| **P2** 层间包含 + 紧致性有限子覆盖 | `WeightedExactDim:981`（`elim_finite_subcover`） | L15 的覆盖→测度比较 |
| **P3** 由 $\mathcal H^s>0$ 反推覆盖代价矛盾 | `WeightedExactDim.one_le_hausdorffMeasure_cantorSet`(L928–1218)，核心在 L938–949（`hausdorffMeasure_apply` + `by_contra`） | L15 整体骨架（203 行可直接仿写） |
| **P4** $\mathcal H^s\neq0\Rightarrow\dimH\ge s$ | `WeightedExactDim:1264–1268`（`ne_of_gt` + `le_dimH_of_hausdorffMeasure_ne_zero`） | L15 末步 |
| **P5** $\forall s<\gamma\Rightarrow\mathrm{ofReal}\,\gamma\le\dimH$ | `WeightedExactDim:1276–1296`（`by_contra` + 中点 `max`） | L16 |
| **P6** 抽象 a.e. 骨架（tower/Markov/BC/dyadic 延拓） | `WindowShortAe.short_ae_main`(L428–536)，已核实（`audit_shortae_wired_20261121.log:621`） | L19 |

结论：**不必从 `DimHFinite` 出发，应从 `WeightedExactDim` 出发**；`DimHFinite` 只提供「`dimH` 可数并 + 平移 Lipschitz」的用法示例（L553–579）。

---

## 6. 风险清单

**R1（黑箱依赖，中高）** thm:short-ae 的形式化只是抽象骨架：`short_ae_main` 的条件 `hStep`（tower 恒等式后件）、`hBchar`（停时柱示性）、`hfloor`（$H_{j+1}/H_j=O(j)$ 接口）在 `shortae_merge_20261121.md` 中被明确记为「纸面假设」。L19 若引用它，即继承该缺口；且其**实例化**仍需 R2 的连分数基础设施。

**R2（纸面接口／单点阻塞，最高）** 全工作区**没有**任意 $x$ 的连分数收敛子、部分商、分母 $q_n$、圆柱 $I(a_1,\dots,a_r)$、以及 $H_j,k(j),r_j$ 的定义；mathlib 亦无（`EulerConvergents.lean:25` 原文）。仅有 $e$ 的 `Psel/Qsel`（`EulerConvergents.lean:60` 等）。L09–L14 全部悬空于此。**建议先立抽象 `structure` 接口（圆柱树 + 长度 + 停止规则公理），把 L01–L05 数值件与 L15 质量分布并行推进。**

**R3（mathlib 缺口，中）** 无量分布原理、无 Moran（§4.6）。L15 必须自建，工作量 5–8 天，且需处理 `hausdorffMeasure_apply` 的 `iInf` 展开（模板已存在，但属重技术）。

**R4（数值部分，中）** 需显式化的常数：$0.34/0.35/0.12/0.13$、$0.01\times0.01=10^{-4}$、$1/\zeta(2)$、$17$、$\varphi^2$、$c_1,c_2$。其中 $1/\zeta(2)$ 需有理界（`WindowMobiusCount` 用 $359/900$：docstring L22 声称 $\sum_{d\le D}\mu(d)/d^2\ge359/900$，但**对应定理不存在**，见 R6）。$\gg$ 与 $O(\cdot)$ 必须全部常数化，否则 `linarith`/`nlinarith` 不可用。

**R5（陈述技术细节，低中）** 纸面 L2831–2833 用「letting $\eta\downarrow0$」取**不可数**并；`dimH_iUnion` 要求 `[Countable ι]`（§4.1）。建议形式化改用 $\eta_n=1/(n\log\varphi)$ 可数序列，结论不变（$\sup_n(1-\eta_n\log\varphi)=1$），但需在论文侧加一句说明，否则形式化与纸面陈述有肉眼可见的偏差。

**R6（陈旧 docstring，低但危险）** `WindowMobiusCount.lean` 文件头 L21–23 声称存在 `coprime_count_ge`（$R\ge10^6$ 时计数 $\ge R^2/10000$）；`rg "coprime_count_ge"` 于该文件**只命中 docstring 一处**，**定理不存在**。任何引用该名字的设计/审计都属误引。

**R7（审计缺口，中）** `WindowMobiusCount` 未被 `EpiFormal.lean` 或 `Audit.lean` import（两者 `rg` 均 0 命中），故**没有** `#print axioms` 记录；其 5 条通用引理目前只有「编译通过」（`window_fix3_20261121.log` 仅一条 deprecation warning）。若 L06 复用它们，须先接入审计并补公理清单。

**R8（表述混淆，低）** 「ζ(2t) 上界＋γ 下界组装」是**两条不同定理**的内容拼接（§5.2）。文档与后续工单不应沿用该措辞，以免把 thm:windows 的上界误记为 thm:no-short-dim 的组成部分。

---

## 7. 建议实施顺序（依赖 DAG）

1. **D0（阻塞）**：连分数圆柱抽象接口（L20 的 `structure` 版）+ `H,k,r` 定义。可先以公理/结构占位交付，但必须在文件中显式标注「接口未实例化」。
2. **D1（可独立交付）**：L01、L03、L04、L05、L07、L08、L18 → 纯数值/算术层，约 5–6 天，全部 `linarith`/`nlinarith`/`gcongr` 级，不依赖 D0。
3. **D2**：L06（新矩形计数，先补 `coprime_count_ge`）+ L09–L12（组合与不交性）。
4. **D3**：L13–L16（几何 + 质量分布），直接仿 `WeightedExactDim:928–1218` 与 `1276–1296`。
5. **D4**：L17、L19 组装 + 论文侧 R5 措辞修订。

---

## 8. 未核到清单（明确不编造）

| 条目 | 状态 |
|---|---|
| thm:no-short-dim 在 `.lean` 中的任何直接陈述 | **未核到**（`rg "no_short|noShort|noshort|divergent window"` 于 `epi_formal/EpiFormal` 0 命中） |
| `WindowMobiusCount.coprime_count_ge` | **未核到**（仅 docstring 命中） |
| `WindowMobiusCount` 任何声明的公理清单 | **未核到**（未接入 `Audit.lean`） |
| 论文 Theorem 编号（是否 18/19/20/21） | **未核到**：`.tex` 用无编号 `theorem` 环境，编号仅见于 `WindowAndResidueCore.lean` 文件头 L12 的自述，不据此断言 |
| `MeasureTheory.condExp` 签名 | **未核实**（本设计不需要；`short_ae_main` 已把条件期望抽象掉） |
| `dimH_of_hausdorffMeasure_ne_zero_ne_top` 完整签名 | **未核到**（`HausdorffDimension.lean:146` 只读到首行，正文被截断） |
| $F_{n+2}\le\varphi^{n+1}$ 的 mathlib 现成引理 | **未核到**（已搜 `Fibonacci.lean`/`Data/Nat/Fib`，无匹配；按需新建） |
| paper L2743–2836 之外的 thm:no-short-dim 证明变体（附录/补充材料） | **未核查**（未打开 `papers/` 与 `reference_pdfs/`） |
