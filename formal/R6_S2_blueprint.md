# R6-S2 形式化蓝图（第 1 阶段产出，2026-11-27，formalizer）

> 对象：`proofs/R6-S2.md` v2（PASSED_L2）及其中的引理 S1（= R6-S1）。
> Lean 模块：`epi_formal/EpiFormal/R6S2Kl.lean`（与 `formal/R6_S2.lean` 逐字节相同），命名空间 `R6S2`。
> 构建与公理记录：`formal/R6_S2.log`。
> 本文件只是计划。凡标“计划”的条目在仓库中**没有**任何 Lean 代码；它们的类型检查过的占位陈述只放在
> 本机草稿 `~/epi_native/epi_formal/scratch/R6S2_draft.lean`，不入库。
> 状态：**未达 L3**。主陈述 `StatementR6S2` 已写成 Lean `Prop`，尚未证明。
> （第 4 阶段更新：`StatementR6S2` 已由 `R6S2.main` 证明，本机构建通过、零占位、只含基础与白名单公理；
> 尚无 GitHub CI 运行号，L3 升级由总控在 CI 通过后决定。）
>
> **进度栏（第 2 阶段，2026-11-27，formalizer）**：新增模块 `epi_formal/EpiFormal/R6S2Blocks.lean`
> （= `formal/R6_S2_blocks.lean`）与 `epi_formal/EpiFormal/R6S2Realize.lean`（= `formal/R6_S2_realize.lean`），
> 零占位，`#print axioms` 只含基础与白名单公理（见 `formal/R6_S2.log` Build 3–5）。已证：D4(i)(ii)、
> B1 推论、B2、B3、B4、`KL_lt_top_of_bdd`、`KL_lt_top_bound`、**S1(a)**、**S1(d)**（`StatementS1d`，对一切
> 块 Hurwitz 数；语句对齐表见 §5）。本机草稿剩 6 个占位：`lemma0`、`cor0'`、`S1b`、`S1c`、`lower`、`upper`。
>
> **进度栏（第 3 阶段，2026-11-27，formalizer）**：新增模块 `epi_formal/EpiFormal/R6S2Localize.lean`
> （= `formal/R6_S2_localize.lean`），零占位，`#print axioms` 只含基础与白名单公理（见 `formal/R6_S2.log`
> Build 6–8）。已证：**引理 0**（`lemma0`）、**推论 0′**（`cor0'`、`cstar_ge_quarter`；对齐辅助
> `exists_isCF_alpha`：每个无理数都是某个 `alpha a`）、**§5.2 规范标签**（`S1_label`、`S1_label_tendsto`）、
> **S1(b)**（`S1b`）、**S1(c)**（`S1c`），以及为第 4 阶段准备的 `BH.blk_near`、`R_big_tendsto`、
> `R_word_tendsto`（步 3 的块极限）、`nu_isLeast`（§6 包装）、`BH.block_of`（块分解）。语句对齐表见 §6，
> **没有任何一项“更弱”**。本机草稿剩 2 个占位：`lower`、`upper`。
>
> **进度栏（第 4 阶段，2026-11-27，formalizer）**：新增模块 `epi_formal/EpiFormal/R6S2Main.lean`
> （= `formal/R6_S2_main.lean`）与审计入口 `epi_formal/AuditR6S2.lean`（= `formal/R6_S2_audit.lean`），
> 零占位，`#print axioms` 只含基础与白名单公理（见 `formal/R6_S2.log` Build 9–11）。已证：**`lower`**（§7.1）、
> **`upper`**（§7.2）、**`main : StatementR6S2`**（第 1 阶段对齐的原定义，未改写）、`cstar_only_W'`（无条件版）；
> **`StatementS1`/`S1_all`**（R6-S1 (a)–(d) 合成一句）；非空性 `main_example11`、校准值 `nu_one_one`（ν((1,1))=1）、
> `cstar_example11`。语句对齐终审见 §7。**R6-S2 形式化已无任何占位**；本机草稿的两个占位已被取代。
> 下界没有走步 2–5 的 limsup 等式与 $E_\infty$，改为反证加余量（§7.3）；上界只证 $\mathcal K\le\nu$，等号由下界给出。

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

**没有任何一项“更弱”。** 第 1–3 阶段时已证明的只有第 14、15 项（第 14 项以主陈述为条件）。**第 4 阶段**：第 12、13 项即
`StatementR6S2` 本身，已由 `R6S2.main` 证明（`R6S2Main.lean`）；第 14 项的无条件版为 `cstar_only_W'`。

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
| 0.1–0.2：$m_n=0$ 最终成立 | `lemma0` 内部 `hrec` | **已证（第 3 阶段）** | M | D2（`theta_lt`、`theta_lt_one`） |
| 0.3：$\rho_n=up_n+vq_n$（Bezout 来自 F2） | `lemma0` 内部 `hb`（显式 $u,v$ 由 `det` 给出，再对 F1 归纳；未用 `crec_linear`） | **已证（第 3 阶段）** | M | `det`、`p_succ`、`q_succ` |
| 0.4：$\beta=u\alpha+v$ | `lemma0` | **已证（第 3 阶段）** | M | `q_tendsto`、`abs_eps_lt` |
| 推论 0′：$\beta\notin L\Rightarrow\mathcal K\ge1/4$；$c^*\ge1/4$ | `cor0'`、`cstar_ge_quarter`、`cstar_ge_quarter_irrational`；对齐 `exists_isCF_alpha` | **已证（第 3 阶段）** | E–M | `lemma0`，`eventually_lt_of_limsup_lt` |

### 2.4 §5 引理 S1（= R6-S1）

| 证明稿 | Lean 名 | 状态 | 难度 | 依赖 |
|---|---|---|---|---|
| 公共引理：`KL < ⊤` ⇒ 最终 $R_n\le C$ | `KL_lt_top_bound` | **已证（第 2 阶段，提前）** | E | `ℝ≥0∞` 的 limsup |
| 公共引理：$R_n$ 有界 ⇒ `KL < ⊤` | `KL_lt_top_of_bdd` | **已证（第 2 阶段）** | E | 同上 |
| 5.1 S1(a) | `S1a`（对一切舍入选择 ρ）；辅助 `near_abs_eq_dist0`、`BH.nk_tendsto` | **已证（第 2 阶段，提前）** | E | B1、B4、上面的公共引理 |
| 5.2 规范标签：$k\ge k_1$ 时唯一的 $s_k$，$g_k\to0$；平局一致性 | `S1_label`、`S1_label_tendsto`；辅助 `BH.q_block`、`BH.yv_block`、`BH.Zl`、`BH.Ky_eq`、`BH.lab_core`、`BH.lab_eventually` | **已证（第 3 阶段）** | M | (A1)、S1(a)、`IsNearSel`/`IsLabelSel` |
| 5.3 S1(b) 第一条 | `S1b`（第 1 分量）；辅助 `BH.blk_near`、`dist0_div_eq_dK`、`dist0_sub_dist0_le`、`BH.lab_val` | **已证（第 3 阶段）** | M | 5.2、(A1)、`R6S7.dK_isLeast` |
| 5.4 S1(b) 第二、三条（有界与耦合；含 $\ell=0$） | `S1b`（第 2、3 分量）；辅助 `BH.yv_big`；对齐 `dist0_label_rep` | **已证（第 3 阶段）** | M | 5.2、5.3、F1 |
| 5.5 S1(c) | `S1c`；辅助 `BH.yv_lattice`、`abs_eps_tendsto`、`BH.block_of` | **已证（第 3 阶段）** | M | 引理 0、5.3、B1、D2 |
| 5.6 S1(d)：构造 $\beta=\frac1K\sum T'_k\lvert\varepsilon_{n_k}\rvert$，(d1) 精确分解，(d2) 余数归纳（模 $K$，对 $P^{(k)}$ 用 (A1)），(d3) 误差估计，(d4) 结论与 `KL < ⊤` | `StatementS1d`、`S1d`；实际拆分：`betaU`、`summ`、`decomp`（d1）、`PP_rec`、`residue`（d2）、`fut_bound`、`past_bound`、`big_decomp`、`pre_succ_bound`、`futBig_bound`、`E_bound`、`lab_err`（d3）、`BH.pos_cases`、`KL_lt_top_of_bdd`（d4 的 `KL < ⊤`）；对齐辅助 `near_iff_nearest`、`coset_indep` | **已证（第 2 阶段）** | **H（最难）** | D2、D3、D4、(A1)、B1、`hAt` |

### 2.5 §6 引理 C

| 证明稿 | Lean 名 | 状态 | 难度 | 依赖 |
|---|---|---|---|---|
| (C0) $v(0)=0$；$C_1$ 的代价为 1 | `R6S7.vcost_zero`、`R6S7.loopZero_cost`、`R6S7.loopZero_nontrivial` | 已证（R6-S7） | — | — |
| (C1)(C2) 有限化，最小值可达，$\nu\le1$ | `R6S7.cor2_K_ge_two`/`cor2_K_eq_one`（给出 `IsLeast (costSet W) (nu W)`）；`nu_bounds` | 已证（R6-S7 + 本模块） | — | — |
| (C3) 闭途径读法与简单圈读法相同 | `R6S7.cor2_*` 中的 `nuSimple W = nu W` | 已证（R6-S7） | — | — |
| 包装：`IsLeast (costSet W) (nu W)` | `nu_isLeast` | **已证（第 3 阶段）** | E | `cor2_*` |

### 2.6 §7.1 下界（步 1–7）

| 证明稿 | Lean 名 | 状态 | 难度 | 依赖 |
|---|---|---|---|---|
| 步 1：$\mathcal K=\infty$ 的情形 | `lower`（反证假设 $\mathcal K<\nu$ 已蕴含 $\mathcal K<\infty$，无需单列） | **已证（第 4 阶段）** | E | — |
| 步 2–4：按块取 limsup、块内极限、取边 | `lower` 内部 `hR`、`hτ`、`hE1`–`hE3`（只用不等式：$R_n<\Lambda$ 最终成立 ⇒ $\lvert t_k\rvert$、$v(r_k)$、$\lvert\tau_k\rvert$ 最终 $\le\mu<\nu$）；`R_big_tendsto`、`R_word_tendsto`、`vcost_le_of`、`BH.round_label_sel` | **已证（第 4 阶段）** | M | S1(a)(b)、B4 |
| 步 5：无穷次出现（改为：某顶点值无穷次出现） | `lower` 内部 `hv`（`Filter.eventually_all`，`ZMod K` 有限） | **已证（第 4 阶段）** | E | — |
| 步 6：非平凡边无穷次出现 | `lower` 内部 `hfreq` | **已证（第 4 阶段）** | E–M | S1(c)(⇐) |
| 步 7：截出闭途径 $r_a\to\cdots\to r_{b}=r_a$（含一条非平凡边），造 `R6S7.ClosedWalk`，代价 $\le\mu<\nu$，与 `nu_isLeast` 矛盾 | `lower` 内部 `hvert`、`C`、`hC`、`hcost`；`finRotate_val` | **已证（第 4 阶段）** | M | 步 5–6、`R6S7.ClosedWalk` |

### 2.7 §7.2 上界与可达（步 8–10）

| 证明稿 | Lean 名 | 状态 | 难度 | 依赖 |
|---|---|---|---|---|
| 步 8：由最小闭途径 $C^*$ 造周期数据 $r_k=C^*.\mathrm{vert}(k\bmod L)$、$\tau_k=C^*.t((k-1)\bmod L)$，用 S1(d) 得 β | `upper` 内部 `hτB`、`hτc`；`finRotate_val`、`ClosedWalk.t_le` | **已证（第 4 阶段）** | M | `nu_isLeast`、S1(d) |
| 步 9：只证 $\mathcal K\le\nu$（逐块：$R_{n_k}<\lvert\tau_k\rvert+\varepsilon$，$R_{n_k+i}<v(r_k)+\varepsilon$）；等号由 `lower` 给出 | `upper` 内部 `hup`；`KL_le_ofReal`、`vterm_le_vcost`、`ClosedWalk.vcost_le`、`BH.block_of` | **已证（第 4 阶段）** | M | `R_big_tendsto`、`R_word_tendsto` |
| 步 10：$\beta\notin\mathbb Z\alpha+\mathbb Z$（若在格中，则所有顶点为 0、所有 $t$ 为 0，与 $C^*$ 非平凡矛盾） | `upper` 内部 `hnot` | **已证（第 4 阶段）** | E–M | S1(c)(⇒) |
| 组装 | `main : StatementR6S2` | **已证（第 4 阶段）** | E | `lower`、`upper` |
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
- **第 3 阶段（已完成）**：引理 0 与推论 0′；5.2 标签唯一性、S1(b)、S1(c)（按 §0.4 对一切选择量化，复用 `IsNearSel`、`BH.yv`、`BH.tv`、`BH.IsLabelSel`、`BH.lab`）。另提前完成 `nu_isLeast`、`R_big_tendsto`、`R_word_tendsto`、`BH.block_of`。
- **第 4 阶段（已完成）**：下界步 1–7、上界步 8–10、组装 `main : StatementR6S2`；新增审计入口 `AuditR6S2.lean`（接入 CI siege 门禁由总控决定，未改 workflow）；语句对齐终审（§7）。

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

---

## 6. 第 3 阶段语句对齐表

模块 `R6S2Localize.lean`。原文：proofs/R6-S2.md v2 §4（引理 0、推论 0′）、§5.2；PLAN_GRAPH.md 现行 R6-S1 的前言与 (b)(c)。
平局约定与 S1(d)（§5）相同：$y_n$ 的取整对一切 `IsNearSel` 选择 ρ 全称量化；规范标签 `BH.lab X lam k = (lam k : ℤ/K)`
对一切 `BH.IsLabelSel X β ρ lam` 选择全称量化（lam 用同一个 ρ）。

### 6.1 引理 0（`lemma0`）

| # | 原文 | Lean | 判定 |
|---|---|---|---|
| 1 | α 为任意无理数（正则连分数满足 F1–F3） | 对一切 `a` 满足 `IsCF a`，α = `alpha a`（`cf_algorithm`：`a` 就是正则连分数算法作用于 α 的输出）；`exists_isCF_alpha`：每个无理数都是某个 `alpha a` | 等价 |
| 2 | $\beta\in\mathbb R$ | `β : ℝ` | 等价 |
| 3 | 存在 $n^*\ge1$，对一切 $n\ge n^*-1$，$\lVert q_n\beta\rVert<\theta_n/4$ | `n0 : ℕ`（$=n^*-1$；$n^*$ 取遍 $\mathbb Z_{\ge1}$ 恰对应 `n0` 取遍 ℕ），`∀ n, n0 ≤ n → dist0 (q_n β) < θ_n / 4` | 等价 |
| 4 | $\beta\in\mathbb Z\alpha+\mathbb Z$ | `β ∈ lattice (alpha a)` | 等价 |

### 6.2 推论 0′（`cor0'`、`cstar_ge_quarter`、`cstar_ge_quarter_irrational`）

| # | 原文 | Lean | 判定 |
|---|---|---|---|
| 1 | $\beta\notin\mathbb Z\alpha+\mathbb Z\Rightarrow\mathcal K_\alpha(\beta)\ge1/4$ | `cor0' : β ∉ lattice (alpha a) → ENNReal.ofReal (1/4) ≤ KL a β`（对一切 `IsCF a`） | 等价 |
| 2 | 对一切无理 α，$c^*(\alpha)\ge1/4$ | `cstar_ge_quarter`（对一切 `IsCF a`）；`cstar_ge_quarter_irrational`（对一切无理 x，存在 `IsCF a` 且 `alpha a = x`、`c* ≥ 1/4`） | 等价 |

### 6.3 §5.2 规范标签（`S1_label`、`S1_label_tendsto`）

| # | 原文 | Lean | 判定 |
|---|---|---|---|
| 1 | 前提：块 Hurwitz 数，$\mathcal K_\alpha(\beta)<\infty$ | `X : BH`，`hK : KL X.a β < ⊤` | 等价 |
| 2 | 存在 $k_1$（依赖 β），$k\ge k_1$ 时 $\operatorname{dist}(Ky_{n_k+1},\mathbb Z)<1/2$，最近整数唯一（记 $s_k$），不涉及平局 | `∃ k1, 1 ≤ k1 ∧ ∀ ρ lam ρ' lam' …, ∀ k ≥ k1, |K y_{n_k+1} − lam k| < 1/2 ∧ (∀ m : ℤ, |K y_{n_k+1} − m| ≤ 1/2 → m = lam k)`；`k1` 对一切选择一致 | 等价（`k1` 与选择无关，比逐个选择取 `k1` 更强） |
| 3 | $k\ge k_1$ 时 $r_k$ 与平局取法无关（两处平局来源都覆盖） | 同一 `k1` 下 `X.lab lam k = X.lab lam' k`，对任意两组选择 (ρ, lam)、(ρ', lam') | 等价 |
| 4 | $g_k:=y_{n_k+1}-s_k/K\to0$ | `S1_label_tendsto`：对一切选择，`y_{n_k+1} − lam k / K → 0` | 等价 |
| 5 | $\ell=0$：$r_k\equiv0$，$s_k:=0$ | 不单列：ℤ/1 平凡，$r_k=0$ 自动成立；第 2、4 项对 $\ell=0$ 同样成立（取 $s_k$ = `lam k`） | 等价（ℓ=0 时多给出 $g_k\to0$） |

### 6.4 S1(b)（`S1b`）

| # | 原文（PLAN_GRAPH 现行 R6-S1） | Lean | 判定 |
|---|---|---|---|
| 1 | α 是块 Hurwitz 数（块词 W） | `X : BH` | 等价 |
| 2 | $\beta\in\mathbb R$，$\mathcal K_\alpha(\beta)<\infty$ | `β : ℝ`，`hK : KL X.a β < ⊤` | 等价 |
| 3 | $y_n:=q_n\beta-\operatorname{round}(q_n\beta)$，平局任取 | 对一切 `ρ` 满足 `IsNearSel`，`BH.yv X β ρ n`（`near_iff_nearest`） | 等价 |
| 4 | $t_k:=A_ky_{n_k}$ | `BH.tv X β ρ k` | 等价（逐字） |
| 5 | 规范标签 $r_k=\operatorname{round}(Ky_{n_k+1})\bmod K$，平局任取，结论对任何取法成立 | 对一切 `lam` 满足 `BH.IsLabelSel X β ρ lam`，`BH.lab X lam k` | 等价 |
| 6 | 对 $1\le i\le\ell$，$\lvert y_{n_k+i}\rvert-d_K(c_ir_k)/K\to0$ | `∀ i, 1 ≤ i → i ≤ X.ell → Tendsto (fun k => |yv (n_k+i)| − dK K (cc W (i−1) · (lab lam k).val) / K) atTop (𝓝 0)`；$c_i$ = `cc W (i−1)`；$d_K(c_ir)$ 取代表元 `val`，与 `R6S7.vterm` 同形，`R6S7.dK_congr` 说明与代表元无关 | 等价 |
| 7 | $(t_k)$ 有界（$k\ge1$） | `∃ B, ∀ k, |tv k| ≤ B`（含 k = 0） | 更强 |
| 8 | $\operatorname{dist}(t_{k+1}-(r_{k+1}-\sigma r_k)/K,\mathbb Z)\to0$ | `Tendsto (fun k => dist0 (tv (k+1) − ((lab (k+1)).val − σ·(lab k).val)/K)) atTop (𝓝 0)`；σ = `R6S7.sigma W`（ℓ=0 时为 1）；`dist0_isLeast` 给出 dist0 = dist(·,ℤ)；`dist0_label_rep` 证明与代表元选取无关 | 等价 |

与第 2 阶段草稿陈述的差别：草稿第 1 分量写 `dK K (cc · lam k)`，入库版写 `dK K (cc · (lab lam k).val)`，二者由 `dK_congr` 相等；入库版直接引用规范标签，更贴近原文，也与 `vterm` 对齐。

### 6.5 S1(c)（`S1c`）

| # | 原文 | Lean | 判定 |
|---|---|---|---|
| 1–5 | 同 §6.4 第 1–5 项 | 同上 | 等价 |
| 6 | $\beta\in\mathbb Z\alpha+\mathbb Z\iff$ 最终规范标签 $r_k=0$ 且 $t_k\to0$ | `β ∈ lattice (alpha X.a) ↔ ((∀ᶠ k in atTop, X.lab lam k = 0) ∧ Tendsto (X.tv β ρ) atTop (𝓝 0))` | 等价 |

**§6 中没有任何一项“更弱”。** 第 4 阶段准备引理（不对应原文的单独陈述）：`R_big_tendsto`（$R_{n_k}-\lvert t_k\rvert\to0$）、
`R_word_tendsto`（$R_{n_k+i}-$`vterm W r_k (i−1)`$\to0$，即 §7.1 步 3 的逐点部分）、`nu_isLeast`、`BH.block_of`。

---

## 7. 第 4 阶段：主定理语句对齐终审

模块 `R6S2Main.lean`。`main : StatementR6S2`，`StatementR6S2` 是 `R6S2Kl.lean` 第 1 阶段的原定义（未改写、未放宽）；
`AuditR6S2.lean` 末尾的 `example` 把它逐字展开后再用 `main` 证明，类型检查通过（防止定义被悄悄替换）。

### 7.1 R6-S2（主定理）逐项终审

| # | 原陈述（PLAN_GRAPH §S.1/§S.2，proofs/R6-S2.md §0.3） | Lean（`StatementR6S2`） | 判定 |
|---|---|---|---|
| 1 | 对一切块 Hurwitz 数 α（单个块词 W，$A_k\to\infty$） | `∀ X : BH`；`BH` 的字段见 §1 第 2–5 项 | 等价 |
| 2 | $p_n/q_n$ 为 α 的正则连分数收敛分数，$\theta_n$、$\lVert\cdot\rVert$ | `q`、`p`、`alpha`、`theta`、`dist0`（§1 第 6–8 项；`cf_algorithm`、`dist0_isLeast`） | 等价 |
| 3 | $\mathcal K_\alpha(\beta)=\limsup_n\lVert q_n\beta\rVert/\theta_n\in[0,\infty]$ | `KL`（`ℝ≥0∞` 中的 limsup，§0.2） | 等价 |
| 4 | $c^*(\alpha)=\inf_{\beta\notin\mathbb Z\alpha+\mathbb Z}\mathcal K_\alpha(\beta)$ | `cstar`、`lattice` | 等价 |
| 5 | $\nu(W)$：不全由平凡环组成的有向闭路上代价的最小值 | `R6S7.nu`（闭途径读法；与简单圈读法相等，`cor2_*`；最小值可达，`nu_isLeast`） | 等价 |
| 6 | $c^*(\alpha)=\nu(W)$ | `cstar X.a = ENNReal.ofReal (R6S7.nu X.W)` | 等价（ν ≥ 1/2 > 0，`ofReal` 在 $[0,\infty)$ 上单射） |
| 7 | 下确界可达：$\exists\beta\notin\mathbb Z\alpha+\mathbb Z$，$\mathcal K_\alpha(\beta)=\nu(W)$ | `∃ β, β ∉ lattice (alpha X.a) ∧ KL X.a β = ENNReal.ofReal (R6S7.nu X.W)` | 等价 |
| 8 | 特别地，$c^*$ 只依赖 W | `cstar_only_W'`（无条件）：`X.W = Y.W → cstar X.a = cstar Y.a` | 等价 |
| 9 | $1/4\le\nu(W)\le1$ | `nu_bounds` | 等价 |
| 10 | 校准：$\nu((1,1))=1$ | `nu_one_one`；`cstar_example11`：$c^*([0;1,1,1,2,1,1,3,\dots])=1$ | 等价（只核了 (1,1) 这一个校准值；$\nu(\varnothing)$、$\nu((1))$ 未单独写定理，但由 `cor2_K_eq_one`（K=1）直接给出） |

**没有任何一项“更弱”。** 证明没有引入任何额外假设：`lower`、`upper`、`main` 的假设只有 `X : BH`（以及 `lower` 的 `β ∉ lattice`）。

非空性（不是空真）：`main_example11` 把 `main` 用在具体数据 `BH.example11`（W=(1,1)，$A_k=k$，N=0）上；`BH` 有居民，且
`main` 本身给出 `β ∉ lattice`，即 $(\mathbb Z\alpha+\mathbb Z)^c$ 中的元素，非空。

### 7.2 R6-S1（a)–(d) 合成陈述（`StatementS1`、`S1_all`）

`StatementS1 : Prop := ∀ X : BH, (∀ β, KL X.a β < ⊤ → ∀ ρ, IsNearSel … ρ → (a) ∧ ∀ lam, X.IsLabelSel β ρ lam → (b) ∧ (c)) ∧ StatementS1d X`。
(a)(b)(c) 的结论逐字取自 `S1a`、`S1b`、`S1c` 的类型，(d) 是 `StatementS1d`；对齐见 §5、§6。量词结构：(a) 只对 ρ 全称（不额外要求 lam），
(b)(c) 对 ρ 与 lam 全称，与原文“对任何平局取法都成立”一致。判定：**等价**（(b) 的有界性一项与 (d) 的 `KL < ⊤` 一项“更强”，见 §5、§6）。

### 7.3 证明路线与证明稿的差别（不影响陈述）

- 下界：证明稿步 2–4 先证 $\mathcal K=\Lambda$（limsup 等式），步 5 用无穷次出现的边集 $E_\infty$。Lean 版改为反证加余量：若
  $\mathcal K<\Lambda<\nu$，则最终 $R_n<\Lambda$，于是最终 $\lvert t_k\rvert<\Lambda+\delta$、$v(r_k)\le\Lambda+\delta$、$\lvert\tau_k\rvert<\Lambda+2\delta=\nu-\delta$；
  取一个无穷次出现的顶点值 $v$，在 $a<j_0<b$（$r_a=r_b=v$，第 $j_0$ 条边非平凡）处截出闭途径，代价 $\le\nu-\delta$，与 ν 的最小性矛盾。
  这里 τ 取 $(r_{k+1}-\sigma r_k)/K+\mathbb Z$ 中的 `round` 代表，不需要“平局只在有限个 k 上出现”的论证。
- 上界：只证 $\mathcal K\le\nu$（对每个 ε，最终 $R_n\le\nu+\varepsilon$），等号由下界给出，不需要“最终周期序列的 limsup 等于周期内最大值”。
- 步 10：若 β 在格中，由 S1(c)(⇒) 得最终标签为 0、$t_k\to0$，于是 $C^*$ 的所有顶点为 0、所有 $\tau$ 趋于 0；边条件使 $t$ 为整数，故全为 0，$C^*$ 全平凡，矛盾。
