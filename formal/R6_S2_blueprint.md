# R6-S2 形式化蓝图（第 1 阶段产出，2026-11-27，formalizer）

> 对象：`proofs/R6-S2.md` v2（PASSED_L2）及其中的引理 S1（= R6-S1）。
> Lean 模块：`epi_formal/EpiFormal/R6S2Kl.lean`（与 `formal/R6_S2.lean` 逐字节相同），命名空间 `R6S2`。
> 构建与公理记录：`formal/R6_S2.log`。
> 本文件只是计划。凡标“计划”的条目在仓库中**没有**任何 Lean 代码；它们的类型检查过的占位陈述只放在
> 本机草稿 `~/epi_native/epi_formal/scratch/R6S2_draft.lean`，不入库。
> 状态：**未达 L3**。主陈述 `StatementR6S2` 已写成 Lean `Prop`，尚未证明。
>
> **进度栏（第 2 阶段，2026-11-27，formalizer）**：新增模块 `epi_formal/EpiFormal/R6S2Blocks.lean`
> （= `formal/R6_S2_blocks.lean`）与 `epi_formal/EpiFormal/R6S2Realize.lean`（= `formal/R6_S2_realize.lean`），
> 零占位，`#print axioms` 只含基础与白名单公理（见 `formal/R6_S2.log` Build 3–5）。已证：D4(i)(ii)、
> B1 推论、B2、B3、B4、`KL_lt_top_of_bdd`、`KL_lt_top_bound`、**S1(a)**、**S1(d)**（`StatementS1d`，对一切
> 块 Hurwitz 数；语句对齐表见 §5）。本机草稿剩 6 个占位：`lemma0`、`cor0'`、`S1b`、`S1c`、`lower`、`upper`。

---

## 0. 设计决定

### 0.1 连分数：整数递推，不用 Mathlib `GenContFract`

- 仓库已有模块的情况：
  - `KappaSharp`、`Classification`、`EulerConvergents`、`FullConvergentSpectrum` 都是针对 e 的专用序列（`Qsel`、`qFull`），不能复用。
  - `GeneralDichotomy.Data` 要求**全部**部分商 $a_j\to\infty$。块 Hurwitz 数的块内部分商有界，不满足这一条件，所以也不能复用。
- Mathlib `Mathlib/Algebra/ContinuedFractions/` 以 `Stream'.Seq` 与 `Option` 为基础。要从给定的整数序列出发，必须先构造 `GenContFract` 并证明它等于 `GenContFract.of α`，代价高，而且仓库没有先例。
- 采用的方案：定义通用的移位递推 `crec a x y`（下标 $m$ 对应连分数下标 $m-1$），令 `qq = crec a 0 1`、`pp = crec a 1 (a 0)`，并取 `q n = qq (n+1)`、`p n = pp (n+1)`。于是 $q_{-1}$=`qq a 0`=0。正则性假设记为 `IsCF a`（$n\ge1\Rightarrow a_n\ge1$）。
- α 的定义是 `alpha a := a 0 + Σ' (-1)^j/(q_j q_{j+1})`。
  - `tendsto_conv` 证明 $p_n/q_n\to\alpha$。
  - `cf_algorithm` 证明正则连分数算法作用于 α 恰好给出 $(a_n)$：$\alpha_0=\alpha$，$\lfloor\alpha_m\rfloor=a_m$，$\alpha_{m+1}=1/(\alpha_m-a_m)$。
  - 由此，“$p_n/q_n$ 是 α 的正则连分数收敛分数”（F3、F4）在 Lean 中**已证明**，不是作为约定写入的。

### 0.2 $\mathcal K_\alpha(\beta)$ 取值于 `ℝ≥0∞`

- 定义：`KL a β := limsup (fun n => ENNReal.ofReal (dist0 (q_n β) / θ_n)) atTop`。
- 选择 `ℝ≥0∞` 的理由：
  - 原陈述的值域是 $[0,\infty]$，`ℝ≥0∞` 与它序同构。被取 limsup 的量非负，所以 `ofReal` 在这些值上是精确的。完备格中的 limsup 就是 $\inf_N\sup_{n\ge N}$，序列无界时值为 ∞。
  - 不用 ℝ 上的 `Filter.limsup`：序列无界时它返回垃圾值（`sInf ∅ = 0`），会把 $\mathcal K=\infty$ 误读成 0。
  - 不用 `EReal`：也可以用，但它多出负半轴，还要另证非负。
- 同理，`cstar a := ⨅ β ∈ (lattice (alpha a))ᶜ, KL a β`（`ℝ≥0∞` 中的下确界）。
- 结论写成 `cstar = ENNReal.ofReal (R6S7.nu W)`。由 `R6S7.nu_ge_half`，ν>0，`ofReal` 在 $[0,\infty)$ 上单射，所以与“$c^*=\nu$”等价。

### 0.3 复用 R6-S7（不重新定义 ν）

`R6S7.contK`、`cc`、`cc'`、`sigma`、`dK`、`vcost`、`ClosedWalk`、`costSet`、`nu`、`nuSimple`、`cseq`、`dseq`、`wseq`、`link`、`core_split`、`cor2_K_ge_two`、`cor2_K_eq_one`、`nu_ge_half`、`contK_pos` 全部直接引用。

### 0.4 S1 中的平局约定（为后续阶段定下）

Lean 的 `round` 平局取法是固定的，只用它会把“对任何平局取法”弱化成“对某一种取法”。因此 S1 的 Lean 陈述（计划）对**一切**最近整数选择做全称量化：

- `IsNearSel f ρ := ∀ n, |f n − ρ n| ≤ 1/2`，用于选择 $y_n$ 的取整；
- `IsLabelSel`，用于选择标签 $\operatorname{round}(Ky_{n_k+1})$；
- 规范标签 `lab lam k := (lam k : ZMod K)`。

这与原陈述“平局任取、结论对任何取法都成立”等价。R6-S2 本身只含 ‖·‖，与平局无关；`dist0_isLeast` 证明了 `dist0 = min_n |x−n|`。

---

## 1. R6-S2 语句对齐表

| # | 原陈述（PLAN_GRAPH §S.1/§S.2） | Lean | 判定 |
|---|---|---|---|
| 1 | “对一切块 Hurwitz 数 α” | `∀ X : BH`（`StatementR6S2`） | 等价 |
| 2 | $N\ge0$，$a_0\in\mathbb Z$，$a_1..a_N\in\mathbb Z_{\ge1}$ | `a0 : ℤ`；`pre : List ℕ` 且 `hpre : ∀ x ∈ pre, 1 ≤ x`；`N := pre.length` | 等价 |
| 3 | $A_k\in\mathbb Z_{\ge1}$（$k\ge1$），$A_k\to\infty$ | `A : ℕ → ℕ`，`hA : ∀ k, 1 ≤ k → 1 ≤ A k`，`hAt : Tendsto A atTop atTop` | 等价（`A 0` 从不被 `BH.a` 读取，因为块号 `…/(ℓ+1)+1 ≥ 1`；单个值也不影响 `Tendsto`） |
| 4 | $W\in\mathbb Z_{\ge1}^\ell$ 固定，$\ell\ge0$ | `W : List ℕ`，`hW : ∀ x ∈ W, 1 ≤ x`（含 `W = []`） | 等价 |
| 5 | 分商序列 $[a_0;a_1..a_N,A_1,W,A_2,W,\dots]$；$n_k:=N+(k-1)(\ell+1)$ | `BH.a`（按位置定义），`BH.nk`；已证 `a_zero`、`a_pre`、`a_big`（$a_{n_k+1}=A_k$）、`a_word`（$a_{n_k+1+i}=w_i$）、`nk_succ`、`nk_one`、`isCF` | 等价 |
| 6 | $p_n/q_n$ 为 α 的正则连分数收敛分数 | `p`、`q` 由 F1 递推定义；`alpha`；已证 `tendsto_conv`、`cf_algorithm` | 等价（展开的唯一性已在 Lean 中证明，见 §0.1） |
| 7 | $\theta_n:=q_n\lvert q_n\alpha-p_n\rvert$ | `theta a n := q_n * |q_n * alpha a − p_n|`；已证 `theta_pos` | 等价（逐字） |
| 8 | $\lVert x\rVert$ | `dist0 x := |x − round x|`；已证 `dist0_isLeast` | 等价 |
| 9 | $\mathcal K_\alpha(\beta):=\limsup_n\lVert q_n\beta\rVert/\theta_n\in[0,\infty]$ | `KL`（`ℝ≥0∞` 中的 `Filter.limsup`，见 §0.2） | 等价 |
| 10 | $c^*(\alpha):=\inf_{\beta\notin\mathbb Z\alpha+\mathbb Z}\mathcal K_\alpha(\beta)$ | `cstar`；`lattice α := {β | ∃ u v : ℤ, β = u*α + v}` | 等价 |
| 11 | $\nu(W)$：在不全由平凡环组成的有向闭路上取 min | `R6S7.nu W`（已在 R6-S7 的 L3 审计中对齐；两种闭路读法相等，见 `cor2_*`） | 等价 |
| 12 | 结论 $c^*(\alpha)=\nu(W)$ | `cstar X.a = ENNReal.ofReal (R6S7.nu X.W)` | 等价（ν>0，`ofReal` 单射） |
| 13 | 下确界可达：$\exists\beta\notin\mathbb Z\alpha+\mathbb Z$，$\mathcal K_\alpha(\beta)=\nu(W)$ | `∃ β, β ∉ lattice (alpha X.a) ∧ KL X.a β = ENNReal.ofReal (nu X.W)` | 等价 |
| 14 | 特别地，$c^*$ 只依赖 $W$ | `cstar_only_W`（以 `StatementR6S2` 为假设，**已证**） | 等价 |
| 15 | $1/4\le\nu(W)\le1$ | `nu_bounds`（对一切正词 W，**已证**） | 等价 |

**没有任何一项“更弱”。** 已证明的只有第 14、15 项（第 14 项以主陈述为条件）。第 12、13 项即 `StatementR6S2` 本身，尚未证明。

非空性：`BH.example11`（$W=(1,1)$，$A_k=k$，$N=0$）满足全部假设，并用 `decide` 核对了前几个分商。

---

## 2. 证明稿 → Lean 引理映射

难度：E = 易（≤50 行），M = 中（50–200 行），H = 难（>200 行或有结构性风险）。“已证”指已在 `R6S2Kl.lean` 中证明，且 `#print axioms` 只含基础与白名单公理（见 log）。

### 2.1 §2 记号、标准事实、初等推论

| 证明稿 | Lean 名 | 状态 | 难度 | 依赖 |
|---|---|---|---|---|
| §2.1 记号 $n_k$、块 | `BH.nk`、`BH.nk_succ`、`BH.nk_one`、`BH.a_big`、`BH.a_word`、`BH.a_pre` | 已证 | E | — |
| F1 递推 | `crec`、`q_succ`、`p_succ`、`q_zero`、`q_one`、`p_zero`、`p_one` | 已证 | E | — |
| F2 行列式 | `det`、`det'`、`det_shift` | 已证 | E | F1 |
| F3 收敛 | `alpha`、`conv_eq`、`tendsto_conv`、`term_summable` | 已证 | M | F2、D1 |
| F3 完全商 | `tail`、`cq`、`crec_concat`、`p_concat`、`q_concat`、`alpha_ge`、`alpha_eq`、`cq_rec`、`cq_gt`、`cq_lt`、`cf_algorithm` | 已证 | M | F1–F3 |
| F4 | `BH.isCF` | 已证 | E | — |
| D1 | `q_pos`、`qq_le_q`、`q_mono_succ`、`q_monotone`、`q_step`、`q_two`、`q_ge_self`、`q_tendsto`、`q_mul_ge` | 已证 | E | F1 |
| D2 | `eps`、`eps_eq`、`eps_sign`、`abs_eps_eq`、`theta_eq`、`theta_pos`、`theta_lt`、`theta_lt_one`、`abs_eps_lt`、`qq_div_q_mem` | 已证 | M | F2、F3 |
| D3 | `Dm`、`D3_eq`、`Dm_self`、`Dm_succ`、`Dm_rec` | 已证 | E | F1、F2 |
| D4 (i)(ii) | `D4i`、`D4ii`（对一切 $k$，比原文 $k\ge1$ 更强）；内部版 `D4i_mm`、`D4ii_mm`；核心 `geo_sum`、`geo_recip` | **已证（第 2 阶段）** | M | D1（$q_{m+2}\ge2q_m$）、`nk_succ` |
| (A1) | `A1`（任意交换环 R） | 已证 | M | `R6S7.link` |
| (A2a) | `A2a` | 已证 | E | `R6S7.core_split`、`link` |
| (A2b) | `R6S7.link` 的第 7 个分量（`dseq` 左递推），后续写包装引理 `A2b` | 实质已证（R6-S7），包装待写 | E | — |

### 2.2 §3 引理 B

| 证明稿 | Lean 名 | 状态 | 难度 | 依赖 |
|---|---|---|---|---|
| B1：$1/\theta_{n_k}\in(A_k,A_k+2)$ | `inv_theta_mem`（一般形式）、`BH.inv_theta_nk` | 已证 | E | D2、F3 |
| B1 推论：$A_k\theta_{n_k}\to1$ | `BH.A_theta_tendsto`；另 `BH.A_theta_lt_one`（$A_k\theta_{n_k}<1$） | **已证（第 2 阶段）** | E | B1、`hAt` |
| B2：$\alpha_{n_k+i+1}\to K_{[i,\ell]}/K_{[i+1,\ell]}$ | `B2` | **已证（第 2 阶段）** | M | `cq_rec`、`a_word`、`cq_gt`、`contK_cons_cons`（即 (A2b)），对 $i$ 倒序归纳 |
| B3：$q_{n_k+i-1}/q_{n_k+i}\to K_{[1,i-2]}/c_i$ | `B3` | **已证（第 2 阶段）** | M | (A1)（取 $X=q$）、`q_step` |
| B4：$1/\theta_{n_k+i}\to K/(c_ic_i')$ | `B4` | **已证（第 2 阶段）** | E | `theta_eq`、B2、B3、(A2a) |

### 2.3 §4 引理 0

| 证明稿 | Lean 名 | 状态 | 难度 | 依赖 |
|---|---|---|---|---|
| 0.1–0.2：$m_n=0$ 最终成立 | `lemma0_defect_zero` | 计划 | M | D2（`theta_lt`、`theta_lt_one`） |
| 0.3：$\rho_n=up_n+vq_n$（Bezout 来自 F2） | `lemma0_bezout` | 计划 | M | `det`、`crec_linear` |
| 0.4：$\beta=u\alpha+v$ | `lemma0` | 计划 | M | `q_tendsto` |
| 推论 0′：$\beta\notin L\Rightarrow\mathcal K\ge1/4$ | `cor0'` | 计划 | E–M | `lemma0`，`ℝ≥0∞` 的 limsup（`frequently_lt_of_lt_limsup`） |

### 2.4 §5 引理 S1（= R6-S1）

| 证明稿 | Lean 名 | 状态 | 难度 | 依赖 |
|---|---|---|---|---|
| 公共引理：`KL < ⊤` ⇒ 最终 $R_n\le C$ | `KL_lt_top_bound` | **已证（第 2 阶段，提前）** | E | `ℝ≥0∞` 的 limsup |
| 公共引理：$R_n$ 有界 ⇒ `KL < ⊤` | `KL_lt_top_of_bdd` | **已证（第 2 阶段）** | E | 同上 |
| 5.1 S1(a) | `S1a`（对一切舍入选择 ρ）；辅助 `near_abs_eq_dist0`、`BH.nk_tendsto` | **已证（第 2 阶段，提前）** | E | B1、B4、上面的公共引理 |
| 5.2 规范标签：$k\ge k_1$ 时唯一的 $s_k$，$g_k\to0$；平局一致性 | `S1_label_unique` | 计划 | M | (A1)、S1(a)、`IsNearSel`/`IsLabelSel` |
| 5.3 S1(b) 第一条 | `S1b_vertex` | 计划 | M | 5.2、(A1)、`R6S7.dK`、`dK_congr` |
| 5.4 S1(b) 第二、三条（有界与耦合；含 $\ell=0$） | `S1b_coupling` | 计划 | M | 5.2、5.3、F1 |
| 5.5 S1(c) | `S1c` | 计划 | M | 引理 0、5.3、B、D2 |
| 5.6 S1(d)：构造 $\beta=\frac1K\sum T'_k\lvert\varepsilon_{n_k}\rvert$，(d1) 精确分解，(d2) 余数归纳（模 $K$，对 $P^{(k)}$ 用 (A1)），(d3) 误差估计，(d4) 结论与 `KL < ⊤` | `StatementS1d`、`S1d`；实际拆分：`betaU`、`summ`、`decomp`（d1）、`PP_rec`、`residue`（d2）、`fut_bound`、`past_bound`、`big_decomp`、`pre_succ_bound`、`futBig_bound`、`E_bound`、`lab_err`（d3）、`BH.pos_cases`、`KL_lt_top_of_bdd`（d4 的 `KL < ⊤`）；对齐辅助 `near_iff_nearest`、`coset_indep` | **已证（第 2 阶段）** | **H（最难）** | D2、D3、D4、(A1)、B1、`hAt` |

### 2.5 §6 引理 C

| 证明稿 | Lean 名 | 状态 | 难度 | 依赖 |
|---|---|---|---|---|
| (C0) $v(0)=0$；$C_1$ 的代价为 1 | `R6S7.vcost_zero`、`R6S7.loopZero_cost`、`R6S7.loopZero_nontrivial` | 已证（R6-S7） | — | — |
| (C1)(C2) 有限化，最小值可达，$\nu\le1$ | `R6S7.cor2_K_ge_two`/`cor2_K_eq_one`（给出 `IsLeast (costSet W) (nu W)`）；`nu_bounds` | 已证（R6-S7 + 本模块） | — | — |
| (C3) 闭途径读法与简单圈读法相同 | `R6S7.cor2_*` 中的 `nuSimple W = nu W` | 已证（R6-S7） | — | — |
| 包装：`IsLeast (costSet W) (nu W)` | `nu_isLeast` | 计划 | E | `cor2_*` |

### 2.6 §7.1 下界（步 1–7）

| 证明稿 | Lean 名 | 状态 | 难度 | 依赖 |
|---|---|---|---|---|
| 步 1：$\mathcal K=\infty$ 的情形 | `lower`（第一个分支） | 计划 | E | `nu_bounds` |
| 步 2：limsup 按块取 | `limsup_blocks` | 计划 | M | `nk_succ`；`ℝ≥0∞` 的 limsup 与 `iSup` 的交换 |
| 步 3：$M_k-\max(\lvert t_k\rvert,v(r_k))\to0$ | `block_max_tendsto` | 计划 | M | S1(a)(b)、B |
| 步 4：取边 $\tau_k$，边集有限，$\mathcal K=\Lambda$ | `edge_choice`、`K_eq_Lambda` | 计划 | M | S1(b)、步 2–3 |
| 步 5：最终只出现无穷次的边；端点代价 $\le\Lambda$ | `eventually_infinitely_often` | 计划 | M | 有限集上的鸽巢（`Set.Finite`、`Filter.Frequently`） |
| 步 6：存在非平凡的无穷次边 | `exists_nontrivial_edge` | 计划 | E–M | S1(c)(⇐) |
| 步 7：从 $e_k=e_{k'}$ 截出闭途径，造 `R6S7.ClosedWalk`（`Fin L`、`finRotate`），代价 $\le\Lambda$ | `closedWalk_of_segment`、`lower` | 计划 | M–H | 步 5–6、`R6S7.ClosedWalk` |

### 2.7 §7.2 上界与可达（步 8–10）

| 证明稿 | Lean 名 | 状态 | 难度 | 依赖 |
|---|---|---|---|---|
| 步 8：由最小闭途径 $C^*$ 造周期数据 $(r_k,\tau_k)$，用 S1(d) 得 β | `periodic_data`、`upper`（构造部分） | 计划 | M | `nu_isLeast`、S1(d) |
| 步 9：最终周期序列的 limsup 等于一个周期内的最大值，即 cost | `limsup_eventually_periodic`、`KL_eq_cost` | 计划 | M | 步 2–3（对构造的 β） |
| 步 10：$\beta\notin\mathbb Z\alpha+\mathbb Z$ | `upper`（非格点部分） | 计划 | E–M | S1(c)(⇒) 的逆否 |
| 组装 | `main : StatementR6S2` | 计划 | E | `lower`、`upper`（草稿中已由占位推出，类型检查通过） |
| §7.3 只依赖 W；$1/4\le\nu\le1$ | `cstar_only_W`、`nu_bounds` | 已证 | E | — |

---

## 3. 最难项判断

**最难项：S1(d)（§5.6，实现引理）。** 理由如下。

1. 它是唯一一处要处理**无穷级数构造**的地方：$\beta=\frac1K\sum_k T'_k\lvert\varepsilon_{n_k}\rvert$。需要证明绝对收敛（D4(ii)），并对每个 $n$ 把 $q_n\beta$ 拆成有限和与级数尾部（(d1)，在 `tsum` 中拆分并交换）。
2. (d2) 是模 $K$ 的同余归纳。对每个 $k$，要把 (A1) 用到整数序列 $P^{(k)}=\sum_{j\le k}x_jD(n_j,\cdot)$ 上，并处理 $T'_1$ 只改首项的细节和 $\ell=0$ 的分支。
3. (d3) 有 4 组显式误差上界。每组都用到 D4、$q_{n_k+1}\ge A_kq_{n_k}$ 等链式不等式，并且依赖 $A_k\to\infty$。$T_{\max}=0$ 等退化情形需要从严格不等式退到非严格不等式（审计记录中的 m1/n1 类附注正出在这里）。
4. 末尾还要把“最近整数唯一”与 S1 陈述中的规范标签（对一切平局选择）接起来，并证明 `KL < ⊤`。

估计 400–600 行，约为其余各项之和的三分之一。次难项是下界步 2–7：在 `ℝ≥0∞` 中按块取 limsup，再从序列截出 `ClosedWalk`（`Fin L` 与 `finRotate` 的下标），风险在工程层面而不在数学层面。

按 Hardest-Case First，第 2 阶段应先做 S1(d)。

---

## 4. 分阶段计划

- **第 1 阶段（本次，已完成）**：定义、陈述 `StatementR6S2`；基础层 F1–F4、D1–D3、(A1)、(A2a)、B1；`nu_bounds`、`cstar_only_W`；全部零占位，`#print axioms` 只含基础与白名单公理。
- **第 2 阶段（最难项优先，已完成）**：D4(i)(ii)；B1 推论、B2、B3、B4；`KL_lt_top_of_bdd`；**S1(d) 全部**（含 `KL < ⊤`）。
  另提前完成 `KL_lt_top_bound` 与 S1(a)。
- **第 3 阶段**：引理 0 与推论 0′；5.2 标签唯一性、S1(b)、S1(c)（按 §0.4 对一切选择量化，复用 `IsNearSel`、`BH.yv`、`BH.tv`、`BH.IsLabelSel`、`BH.lab`）。
- **第 4 阶段**：下界步 1–7、上界步 8–10、组装 `main : StatementR6S2`；新增审计入口 `AuditR6S2.lean`，接入 CI siege 门禁（由总控决定）；语句对齐终审。

每个阶段结束时，只把零占位的模块入库；未完成的陈述只留在本机草稿中。

---

## 5. S1(d) 语句对齐表（第 2 阶段）

原陈述：PLAN_GRAPH.md 现行 R6-S1 陈述的前言（$y_n$、$t_k$、规范标签及平局约定）与 (d)。Lean：
`R6S2.StatementS1d X`（`R6S2Realize.lean`），`R6S2.S1d : ∀ X, StatementS1d X`。

| # | 原陈述 | Lean | 判定 |
|---|---|---|---|
| 1 | α 是块 Hurwitz 数（块词 $W$） | `X : BH`（`S1d` 对一切 `X`） | 等价 |
| 2 | 对任意序列 $(r_k)_{k\ge0}$，$r_k\in\mathbb Z/K$；$r_0$ 属于给定数据 | `r : ℕ → ZMod (R6S7.contK X.W)`（`r 0` 是给定数据，只出现在 $k=1$ 的条件里） | 等价 |
| 3 | 任意有界实数序列 $(\tau_k)_{k\ge1}$ | `τ : ℕ → ℝ`，`∃ B, ∀ k, 1 ≤ k → |τ k| ≤ B`（`τ 0` 不受约束，也不出现在结论中） | 等价 |
| 4 | $\tau_k\in(r_k-\sigma r_{k-1})/K+\mathbb Z$（$k\ge1$） | `∀ k, 1 ≤ k → ∃ z : ℤ, τ k = ((r k).val − σ·(r (k-1)).val)/K + z`，$\sigma$=`R6S7.sigma X.W`（含 $\ell=0$ 时 $\sigma=1$） | 等价：`coset_indep` 证明该条件与整数代表元的选取无关 |
| 5 | $y_n:=q_n\beta-\operatorname{round}(q_n\beta)$，平局任取 | `BH.yv X β ρ n = q_n β − ρ n`，`ρ` 取遍一切 `IsNearSel`（$\lvert q_n\beta-\rho_n\rvert\le1/2$）；`near_iff_nearest` 证明这恰好是“ρ_n 是最近整数” | 等价 |
| 6 | $t_k:=A_ky_{n_k}$ | `BH.tv X β ρ k = A_k * yv (n_k)` | 等价（逐字） |
| 7 | 规范标签 $r_k(\beta):=\operatorname{round}(Ky_{n_k+1})\bmod K$，平局任取 | `BH.lab X lam k = (lam k : ℤ/K)`，`lam` 取遍一切 `BH.IsLabelSel X β ρ lam`（`lam k` 是 $K y_{n_k+1}$ 的最近整数，$y$ 用同一个 ρ） | 等价 |
| 8 | “下列结论对任何平局取法都成立” | 结论在 `∀ ρ lam, IsNearSel … ρ → IsLabelSel … lam → …` 之下 | 等价 |
| 9 | 存在 β | `∃ β : ℝ` | 等价 |
| 10 | 规范标签最终等于 $r_k$ | `∀ᶠ k in atTop, X.lab lam k = r k` | 等价 |
| 11 | $t_k-\tau_k\to0$ | `Tendsto (fun k => X.tv β ρ k − τ k) atTop (𝓝 0)` | 等价 |
| 12 | （S1 前言的前提 $\mathcal K_\alpha(\beta)<\infty$，§5.6 (d4) 证明） | 附加结论 `KL X.a β < ⊤` | 更强（多给一个结论） |

**没有任何一项“更弱”。** 与第 1 阶段草稿陈述相比，第 3 项把 `∀ k, |τ k| ≤ B` 放宽为只要求 $k\ge1$（假设更弱，定理更强，且更贴近原文）。

S1(a)（`R6S2.S1a`）对齐：前提 `KL X.a β < ⊤` 与任意 `IsNearSel` 选择 ρ；三条结论 $y_{n_k}\to0$、$A_k\theta_{n_k}\to1$、
$1/\theta_{n_k+i}\to K/(c_ic_i')$（$1\le i\le\ell$，`cc W (i-1)`、`cc' W (i-1)` 即 $c_i$、$c_i'$）逐条对应，全部等价。

D4、B2–B4 的陈述与 §2.1–2.2 表中的数学命题逐字对应；D4 去掉了不需要的 $k\ge1$（更强）。
