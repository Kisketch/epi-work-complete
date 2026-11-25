# 施工图：相变公式 dimH F_{m,S,B} → max(1/2, s₀(S)) 的一般化障碍清单

日期：2026-11-24　产出类型：**类别 4（文献核查 / 复现）**。本文件只对既有证明做结构拆解与依赖分类，不产生新数学结论，不作证明引用。对应 PI 规划第一段第 2 项「max(1/2, s₀) 适用范围判定」。

## 0. 口径与核查状态

- 对象仓库 HEAD：f345d60（任务书给定；本次未执行任何 git 命令核验）。全部操作只读，本文件为唯一新建文件。
- Lean 侧（`epi_formal/EpiFormal/ResidueMultiAsymptotic.lean`、`epi_formal/EpiFormal/TransferOperatorDim.lean`）：只读源码，**未运行 lake**；所有 Lean 结果一律标「**作者自报，未复跑**」。
- 定理编号：论文未编译，`thm:multi-residue-asymptotic` 与 `thm:residues-general` 的印刷编号 **未核到**，本文一律用 label 指代。
- 未联网：未做任何文献检索，**不作任何「无先例」判断**；凡涉及文献状态处写「未核到」。
- 行文区分：已核对事实直接陈述；本文件的推断一律加【推断】标记；未查到的事实写「未核到」。

## 1. 照录：对象定义

### 1.1 TeX 原文（paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex）

L3797–3810（字母表与集合）：

```tex
More generally, fix two finite digit sets $S\subset\Z_{\ge1}$ and
$B\subset\Z_{\ge0}$ with $d:=|S|+|B|\ge1$. For every integer modulus $m\ge1$,
define the \emph{multi-residue digit alphabet}
(\texttt{multiResidueAlphabet m S B}) and its continued-fraction Cantor set
(\texttt{multiResidueSet m S B}) by
\[
\mathcal A_{m,S,B}:=\bigl\{a\in\Z_{\ge1} : (\exists r\in S,\ a\ge r\wedge a\equiv r\!\!\pmod m)\ \text{or}\ (\exists b\in B,\ \exists k\ge1,\ a+b=km)\bigr\},
\]
\[
F_{m,S,B}:=\bigl\{[0;a_1,a_2,\dots]\in(0,1)\setminus\Q : a_n\in\mathcal A_{m,S,B}\ \forall n\ge1\bigr\}.
\]
In particular, $F_{m,\{r\},\emptyset}=F_{m,r}$ for $r\ge1$ and
$F_{m,\emptyset,\{0\}}=F_{m,m}$.
```

（$\mathcal A_{m,S,B}$ 在 L3804，$F_{m,S,B}$ 在 L3807。）

L3811–3821（$W_S$、$s_0(S)$、$C_S$、$C_S'$、$V_{S,s}$）：

```tex
For finite $S\subset\Z_{\ge1}$, denote by $W_S(p,n):=\sum_{w\in S^n}q(w)^{-p}$
the $n$-th continuant word sum (\texttt{wordSum S p n}, with $W_S(p,0)=1$, where
$q(w)$ is the continuant denominator of the finite word $w$), by
\[
s_0(S):=\inf\Bigl\{s>0:\sum_{n=0}^{\infty} W_S(2s,n)<\infty\Bigr\}
\]
the Poincar\'e abscissa (\texttt{poincareAbscissa S}), and, whenever convergent,
by $C_S(p):=\sum_{n=0}^{\infty} W_S(p,n)$ (\texttt{multiC S p}, with $C_S:=C_S(1)$),
$C_S':=\sum_{n=0}^{\infty}\sum_{w\in S^n}\frac{\log q(w)}{q(w)}$ (\texttt{multiCLog S}),
and $V_{S,s}(x):=\sum_{n=0}^{\infty}\sum_{w\in S^n}(q(w)+p(w)x)^{-2s}$
(\texttt{multiResolventV S s x}, where $p(w)/q(w)=[0;w]$).
```

（$s_0(S)$ 在 L3815。）

### 1.2 Lean 原文（epi_formal/EpiFormal/ResidueMultiAsymptotic.lean）

```lean
/-- Critical Poincaré abscissa `s₀(S) = inf {s > 0 : ∑_n ∑_{w ∈ S^n} q(w)^{-2s} < ∞}`. -/
def poincareAbscissa (S : Finset ℕ) : ℝ :=
  sInf {s : ℝ | 0 < s ∧ Summable (wordSum S (2 * s))}
```
（L520–522）

```lean
/-- Combined multi-residue digit alphabet: `a ≡ r [MOD m]` with `a ≥ r` for `r ∈ S`,
    or `a ≡ -b [MOD m]` with `a ≥ 1` for `b ∈ B`. -/
def multiResidueAlphabet (m : ℕ) (S B : Finset ℕ) : Set ℕ :=
  {a : ℕ | (∃ r ∈ S, r ≤ a ∧ a % m = r % m) ∨
    (∃ b ∈ B, ∃ k : ℕ, 1 ≤ k ∧ a + b = k * m ∧ 1 ≤ a)}

/-- Multi-residue continued-fraction Cantor set `F_{m, S, B} = cfAlphabetSet (multiResidueAlphabet m S B)`. -/
def multiResidueSet (m : ℕ) (S B : Finset ℕ) : Set ℝ :=
  cfAlphabetSet (multiResidueAlphabet m S B)
```
（L1105–1113）

```lean
/-- Total `p`-weighted continuant partition sum over length-`n` words in `S`. -/
def wordSum (S : Finset ℕ) (p : ℝ) (n : ℕ) : ℝ :=
```
（L169–170，函数体未展开摘录）

```lean
/-- Total `p`-weighted continuant series `C_S(p) = ∑' n, ∑_{w ∈ S^n} q(w)^{-p}`. -/
def multiC (S : Finset ℕ) (p : ℝ) : ℝ :=
  ∑' n : ℕ, wordSum S p n

/-- Multi-branch resolvent test function `V_{S,s}(x) = ∑' n, ∑_{w ∈ S^n} (q(w) + p(w) x)^{-2s}`. -/
def multiResolventV (S : Finset ℕ) (s x : ℝ) : ℝ :=
  ∑' n : ℕ, ∑ w : Fin n → {a : ℕ // a ∈ S},
    (denQ (subWord n w) + denP (subWord n w) * x) ^ (-(2 * s))
```
（L657–664）

```lean
/-- Real-valued total tail sum over shifted branches `(k + 1) m + r` and `(k + 1) m - b`. -/
def multiResidueTailReal (m : ℕ) (S B : Finset ℕ) (s x : ℝ) : ℝ :=
  (∑ r ∈ S, ∑' k : ℕ,
    multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
      ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) +
  (∑ b ∈ B, ∑' k : ℕ,
    multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
      ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))

/-- Finite `K`-branch truncation of `multiResidueAlphabet m S B` for dimension lower bounds. -/
def truncMultiAlphabet (m K : ℕ) (S B : Finset ℕ) : Finset ℕ :=
  S ∪ (S ×ˢ Finset.range K).image (fun p => (p.2 + 1) * m + p.1) ∪
    (B ×ˢ Finset.range K).image (fun p => (p.2 + 1) * m - p.1)
```
（L2665–2677）

### 1.3 TeX ↔ Lean 对照

- $\mathcal A_{m,S,B}$ 的 S 分支 $a\ge r\wedge a\equiv r\pmod m$ ↔ `r ≤ a ∧ a % m = r % m`；B 分支 $\exists k\ge1,\ a+b=km$ ↔ `∃ k, 1 ≤ k ∧ a + b = k * m ∧ 1 ≤ a`（Lean 额外写明 `1 ≤ a`，与 $a\in\Z_{\ge1}$ 一致）。
- $F_{m,S,B}$ ↔ `cfAlphabetSet (multiResidueAlphabet m S B)`；$E_S$ ↔ `cfAlphabetSet (S : Set ℕ)`。
- $s_0(S)$ ↔ `sInf {s | 0 < s ∧ Summable (wordSum S (2 * s))}`，一致。
- 结构要点（已核对）：**有限核 $S$ 与尾部剩余类集合在定义中是同一个集合**（尾类 = $S$ 与 $-B\bmod m$，共 $d=|S|+|B|$ 类，步长恰为 $m$，尾部最小数字 $\ge m-\max B$）。

## 2. 依赖类型约定（本文件约定）

| 标签 | 含义 | 判据 |
| :--- | :--- | :--- |
| [AP] | 用到尾部数字**恰为**等差数列 $\{km+r\}$、$\{(k+1)m-b\}$（精确重排求和、Hurwitz 尾、MVT 伸缩、嵌入单剩余类集合）或核 = 残差集 | 把尾部换成别的无限集后该步论证是否失效 |
| [MUL] | 只用到连分母递推/可乘性 $q(uv)\in[q(u)q(v),2q(u)q(v)]$ 与词和单调性 | 对任意正数字母表逐字成立 |
| [FS] | 只用到「最终周期/有限状态」的簿记：尾由 $d$ 个剩余类索引、核为有限状态集、PF | 对任意最终周期集逐字成立 |
| [FS]* | 现证明中**没有**严格意义的 [FS] 步骤；[FS] 是推广目标。标注 [FS]* 处表示「推广时该步需以 PF/状态版引理替换」 | — |
| [GEN] | 普适工具：维数单调、转移算子判据、$\zeta$ 展开、Taylor、纯实代数 | 与字母表无关 |

难度：routine（改参数/换一般界即可）/ hard（需新引理或新 Lean 基础设施，数学已知）/ research-level（需新数学）。

## 3. 证明结构总览

| tex 部分 | tex 行 | 内容 | Lean Part（行范围） | Lean 主定理 |
| :--- | :--- | :--- | :--- | :--- |
| (i) | 3825–3835 / 证明 3889–3907 | $\dimH E_S=s_0(S)$，Bowen-free | Part 1（33–642）+ Part 2（643–1102） | `dimH_cfAlphabetSet_finset_eq_poincareAbscissa`（910） |
| (ii) | 3836–3844 / 证明 3909–3925 | 相变极限 + 见证 $\{2,3\},\{1,2\}$ | Part 3（1103–1789） | `tendsto_dimH_multiResidueSet`（1375）、`subcritical_pair_two_three`（1667）、`supercritical_pair_one_two`（1703） |
| (iii) | 3845–3851 / 证明 3927–3932 | $\zeta(1+\varepsilon)$ 的 Euler 展开 | Part 4（1790–2370） | `abs_tsum_rpow_sub_inv_sub_eulerMascheroni_le`（1910） |
| (iv) | 3852–3876 / 证明 3934–3950 | 次临界三阶渐近 | Part 4 后半 + Part 5（2371–4178） | `dimH_multiResidueSet_asymp_three_term`（3834）及 5 条推论（3943, 4023, 4121, 4139, 4158） |
| (v) | 3877–3884 / 证明 3952–3970 | 超临界速率 $\Theta(m^{-2s_0})$ | Part 6（4179–5039） | `dimH_multiResidueSet_supercritical_rate`（5012）、`..._one_two_supercritical_rate`（5027） |

外部输入：`thm:residues-general`(ii)（tex 3573–3579，无条件转移算子判据）在 Lean 中为 `TransferOperatorDim.lean` 的 `dimH_le_of_transferOp_le`（420，任意 `A : Set ℕ`）与 `le_dimH_of_transferOp_ge`（1491，仅有限 `A : Finset ℕ`）。

## 4. 步骤表

| 步骤 | 陈述摘要 | 位置（tex / Lean） | 依赖类型 | 一般化所需替换或障碍 | 难度 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| S1 | 连分母拼接界 $q(uv)\in[q(u)q(v),2q(u)q(v)]$，得词和次/超可乘 $2^{-p}W(p,k)W(p,n)\le W(p,k+n)\le W(p,k)W(p,n)$ | tex 3889–3893 / `denQ_append_eq` 45、`denQ_append_ge` 53、`denQ_append_le` 60、`wordSum_add_le` 241、`wordSum_add_ge` 260 | [MUL] | 任意正数字母表逐字可用。有限状态（sofic）约束下词和须按「被接受的路径」求和，拼接需经过连接状态：$W(k+n)\ge c\,W(k)W(n)$，常数 $c$ 依赖于状态数，不再是 2 | 普通字母表 routine；sofic hard |
| S2 | Poincaré 横坐标 $s_0(S)$ 的性质：$0\le s_0\le1$、$1\le W_S(2s_0,n)\le2^{2s_0}$、$s>s_0$ 可和、$s<s_0$ 发散 | tex 3815 / `poincareAbscissa` 521、`_nonneg` 524、`_le_one` 528、`summable_wordSum_of_poincareAbscissa_lt` 534、`not_summable_wordSum_of_lt_poincareAbscissa` 543、`one_le_wordSum_poincareAbscissa` 548、`wordSum_poincareAbscissa_le` 575 | [MUL]（经 S1）；定义用 `Finset` | 定义对任意（无限）字母表照写。下界 $1\le W(2s_0,n)$ 靠超可乘；sofic 情形改用 PF：$W(p,n)^{1/n}\to\rho(p)$，$s_0$ 为 $\rho(2s)=1$ 的根，常数 $2^{2s_0}$ 变为状态相关 | 普通字母表 routine；sofic hard |
| S3 | 多分支预解恒等式 $\sum_{a\in S}(a+x)^{-2s}V_{S,s}(1/(a+x))=V_{S,s}(x)-1$（移位 $w\mapsto aw$） | tex 3830–3833（eq:multi-resolvent-branch）、3900–3901 / `multiResolventV` 662、`multiResolventV_branch_eq` 739 | [MUL]（只用 $q(aw)=a\,q(w)+q(w')$） | 任意字母表逐字；sofic 情形成为按状态的向量恒等式 $V_i=\sum_{a:i\to j}(a+x)^{-2s}V_j(1/(a+x))+$ 常数项 | 普通 routine；sofic routine–hard（需新定义） |
| S4 | 上界 $\dimH E_S\le s_0(S)$：$\mathcal L_{s,S}V_{S,s}=V_{S,s}-1\le V_{S,s}$，$1\le V_{S,s}\le C_S(2s)$，套用无条件上判据 | tex 3902–3903 / `dimH_cfAlphabetSet_finset_eq_poincareAbscissa` 910（上界部分 913–946，941 行调用 `dimH_le_of_transferOp_le`）；界：`one_le_multiResolventV` 697、`multiResolventV_le_multiC` 715；判据 `TransferOperatorDim.lean` 304、420 | [GEN] + [MUL] | 判据对任意 `A : Set ℕ` 成立，无需改动；$V_{A,s}$ 的上下界对任意字母表成立 | routine |
| S5 | 下界 $\dimH E_S\ge s_0(S)$：$s<s_0$ 时截断部分和 $v_N=\sum_{j<N}\mathcal L_{s,S}^j1$ 超过自身像，用有限子字母表下判据 | tex 3903–3907 / Lean 954–1099（1095 行调用 `le_dimH_of_transferOp_ge`）；迭代公式 `transferOp_iterate_one_eq` 826、`transferOp_iterate_one_le` 886；判据 `TransferOperatorDim.lean` 926、1491 | [GEN]（有限子字母表判据）+ [MUL] | 推广到「核 $F$ + 逃逸尾」时直接对有限核 $F$ 用 S4–S5 即可。sofic 核：迭代公式按状态分量化，「超过自身像」需每个状态一致的 PF 下界 | 有限核 routine；sofic hard |
| S6 | 核/尾分离：$m>\max S+\max B$ 时 $\mathcal A_{m,S,B}=S\sqcup\bigsqcup_{r\in S}\{(k{+}1)m{+}r\}_{k\ge0}\sqcup\bigsqcup_{b\in B}\{(k{+}1)m{-}b\}_{k\ge0}$，尾数字 $\ge m-\max B$，转移算子精确分解 | tex 3909–3910 / `transferOp_multiResidueAlphabet_eq` 1153（假设 `S.sup id + B.sup id + 1 ≤ m`）、`multiResidueAlphabet_ge_one` 1115、`multiResidueTailReal` 2666 | [AP] | 最终周期字母表 $A_m=F\sqcup\bigsqcup_{\rho\in R}\{\rho+kM_m,\ k\ge k_0\}$ 用同一分解，参数 $(S,B)\mapsto(F,R)$、$d=\lvert R\rvert$。**障碍**：现 Lean 引理把「核」与「尾剩余类」绑在同一个 `Finset S` 上（见 `multiResidueTailReal` 中 `multiResolventV S s` 与外层 `∑ r ∈ S` 同用 S），须重构成两个独立参数 | routine（重构） |
| S7 | 尾界：$\sum_{k\ge1}(km{+}a_0{+}x)^{-2s}V(1/(km{+}a_0{+}x))\le C\,(m{-}M_B)^{-2s}\bigl(1+\tfrac1{2s-1}\bigr)$，MVT 伸缩 | tex 3911–3913 / `hshift_tail` 1443–1490（约 1487 行调用 `tsum_arith_tail_le`）；`TransferOperatorDim.lean` 1682 | [AP]（按步长 $m$ 的等差尾实现） | **只为极限 (ii)**：可换成一般计数界 $\sum_{a\ge N}(a+x)^{-2s}\le N^{1-2s}/(2s-1)$（任意字母表，$s>1/2$），只需尾最小数字 $N_m\to\infty$。**为 (iv)(v) 的定量结果**：必须保留等差尾的更尖界 $O(m^{-2s})$ | 极限 routine；定量 hard |
| S8 | 极限上界：$s>\max(1/2,s_0(S))$ 时大 $m$ 有 $\mathcal L_{s,\mathcal A_{m,S,B}}V_{S,s}\le V_{S,s}$，故 $\limsup_m\dimH F_{m,S,B}\le\max(1/2,s_0(S))$ | tex 3911–3913 / `hup_ev` 1382–1589（1588 行 `dimH_le_of_transferOp_le`） | [GEN]（判据 + 极限簿记），输入 S3、S7 | 用 $(F,V_{F,s})$ 替换 $(S,V_{S,s})$，只需尾和 $\to0$（$s>1/2$ 且 $N_m\to\infty$ 时自动） | routine |
| S9 | 极限下界（核）：$F_{m,S,B}\supseteq E_S$（$r<m$ 时 $r\equiv r\bmod m$），故 $\dimH\ge s_0(S)$ | tex 3914 / `hsub_S` 1644–1650（`cfAlphabetSet (S : Set ℕ) ⊆ multiResidueSet`，`dimH_mono`） | [GEN]（维数单调；只用核 $\subset\mathcal A$） | $F(A_m)\supseteq E_F$，$\dimH\ge s_0(F)$。此处决定了「替代 $s_0(S)$ 的量 = 核的 Poincaré 横坐标」 | routine |
| S10 | 极限下界（地板）：$\dimH F_{m,S,B}>1/2$，通过嵌入单剩余类集合 $\mathrm{residueConstSet}\ m\ r_0\subseteq F_{m,S,B}$（$r_0\in S$）或 $\mathrm{residueConstSet}\ m\,(m{-}b_0)$（$S=\emptyset$） | tex 3914–3915 / `hlo_ev` 1590–1660（B 分支 1607–1619，S 分支 1620–1624）；`TransferOperatorDim.lean` `half_lt_dimH_residueConstSet` 1507 | [AP]（归约到一条无限等差子字母表 $\{km+r_0\}$） | 尾含无限等差数列的最终周期字母表：同一归约逐字可用。**稀疏尾（无等差子列）不被工作区覆盖**：需新的 Frostman/Bernoulli 测度论证；「任意无限字母表 $\dimH E_A\ge1/2$」为【推断】，工作区与文献均未核到 | 等差尾 routine；一般尾 hard–research-level |
| S11 | 见证：$S=\{2,3\}$ 次临界（$W(1,1)=5/6<1$）、$S=\{1,2\}$ 超临界（$v(x)=2/(2+x)$，$s=51/100$） | tex 3842–3844、3918–3925 / `subcritical_pair_two_three` 1667、`supercritical_pair_one_two` 1703 | [GEN]（具体有限字母表，无残差结构） | 仅示例；对每个新字母表类需另给见证 | routine |
| S12 | $\lvert\sum_k k^{-(1+\varepsilon)}-\varepsilon^{-1}-\gamma\rvert\le4\zeta(3/2)\varepsilon$，$\varepsilon\in(0,1]$ | tex 3845–3851、3927–3932 / `abs_tsum_rpow_sub_inv_sub_eulerMascheroni_le` 1910 | [GEN] | 无需改动，原样复用 | routine |
| S13 | Taylor 包络 $C_S(1+\varepsilon)=C_S-C_S'\varepsilon+O(\varepsilon^2)$（含 $C_S''$） | tex 3934–3936 / `multiC_one_add_bounds` 2270；矩量 `wordLogSum` 2133、`wordLogSqSum` 2137、`multiCLog` 2141、`multiCLogSq` 2145；可和性 2185、2225 | [MUL]（$q(w)^{-p}$ 对 $p$ 单调） | 任意有限核 $F$ 逐字 | routine |
| S14 | 分支尾 vs. $\zeta$：$\lvert\sum_k V_{S,s}(\tfrac1{(k{+}1)m+\delta})((k{+}1)m{+}\delta)^{-(1+\varepsilon)}-C_S(1{+}\varepsilon)m^{-(1+\varepsilon)}\zeta(1{+}\varepsilon)\rvert\le8C_S(M_0{+}1)\zeta(2)/m^2$，对 $\lvert\delta\rvert\le M_0$ 一致 | tex 3937–3938 / `abs_branch_tsum_sub_le` 2494；`multiResolventV_sub_multiC_le` 2373 | [AP]（分支必须是步长 $m$、位移 $\delta$ 与 $m$ 无关的等差列） | **已对位移 $\delta$ 通用**：$\delta=r$ 与 $\delta=-b$ 同一定理覆盖，最终周期尾直接可用。非等差尾：需新的「尾和 ≈ 密度 × $\zeta$」引理，前提是计数函数 $N(t)=(d/M)t+O(1)$（剩余类均匀分布） | 等差尾 routine；非等差尾 hard |
| S15 | 主尾展开：$\lvert\text{tail}-\bigl(\tfrac{dC}{\alpha}-\tfrac{dC\log m}{m}+\tfrac{d(\gamma C-C')}{m}\bigr)\rvert\le E_0(\log m)^2/m^2$，$\alpha\in[dC/2,2dC]$，$s=\tfrac{1+\alpha/m}2$ | tex 3938–3941 / `subcritical_tail_expansion` 3008（调用 `m_rpow_zeta_approx` 2825、`multiC_zeta_prod_approx` 2915） | [AP]（对 $d$ 条分支求和，用 S14；$d\,C\,m^{-\varepsilon}(\varepsilon^{-1}+\gamma)$ 的线性结构） | 同一展开以 $d\mapsto\lvert R\rvert$、$C\mapsto C_F$ 成立。若尾各类「权重」不同（有限状态尾每类重数不同），$dC$ 变为 $\sum_\rho w_\rho C$，线性结构仍存 | routine |
| S16 | 带尾判据：$\text{tail}(x)\le1\ \forall x\Rightarrow\dimH\le s$；$\text{tail}(x)\ge1+\text{gap}\ \forall x\Rightarrow\dimH\ge s$（$V\in[1,C]$） | tex 3938 / `dimH_multiResidue_upper_of_tail_le` 3241、`dimH_multiResidue_lower_of_tail_ge` 3430（用 `truncMultiAlphabet` 2675 作有限子字母表） | [GEN]（判据）+ [MUL]（$\mathcal L_{s,S}V=V-1$） | 逐字，$(S,\text{tail})\mapsto(F,\text{tail}_F)$ | routine |
| S17 | 三阶代数：由 $dC(1{+}\varepsilon)(\varepsilon^{-1}{+}\gamma{+}O(\varepsilon){+}O(m^{-1}))m^{-\varepsilon}=1{+}O(m^{-1})$，$\varepsilon=\alpha/m$，解出 $\alpha$ 至 $O((\log m)^2/m^2)$ | tex 3942–3950 / `three_term_alpha_prep` 3661、`three_term_tail_upper` 3712、`three_term_tail_lower` 3769、`three_term_s_bounds` 3812；主定理 3834 | [GEN]（纯实代数，参数 $d,C,C',\gamma$） | 参数替换即得 | routine |
| S18 | 极点定量界 $C_S(2(s_0{+}\delta))\le32/\delta$，$0<\delta\le1$ | tex 3952–3954 / `multiC_supercritical_le` 4207 | [MUL]（次可乘 + $W(2s_0,n)\le2^{2s_0}\le4$） | 有限核逐字；sofic 核常数 32 变为状态相关 | 普通 routine；sofic hard |
| S19 | 上速率：$\delta=K_2m^{-2s_0}$ 使 $C_S(2s)\cdot O(m^{-2s_0})\le1$，得 $\dimH-s_0\le K_2m^{-2s_0}$ | tex 3955–3958 / `dimH_multiResidue_upper_of_tail_le_s` 4295、`dimH_multiResidueSet_supercritical_upper_ennreal` 4469、`dimH_multiResidueSet_supercritical_upper` 4650 | [AP]（尾 $\asymp d\,C_S(2s)\,\zeta(2s)\,m^{-2s}$，指数 $2s_0$ 来自步长 $m$）+ [GEN] | 最终周期尾逐字（尾 $=d\,C_F(2s)M^{-2s}\zeta(2s)(1{+}O(M^{-1}))$）。一般尾：速率指数由尾计数函数决定（$\sum_{a\ge N}a^{-2s}\asymp N^{1-2s}$，指数变为 $2s_0-1$ 型）【推断】 | 等差尾 routine；一般尾 research-level |
| S20 | 下速率：子字母表 $A_1=S\cup\{m{+}r_0\}$，$v=\sum_{j<n}\mathcal L_{s,S}^j1$，$n=\lfloor1/(2\delta\log(\max S{+}1))\rfloor$，$1/48\le(\mathcal L^j1)(y)\le4$，额外分支 $\ge(2m)^{-2s}n/48\ge1$，得 $\dimH\ge s_0{+}K_1m^{-2s_0}$ | tex 3959–3970 / `dimH_multiResidueSet_supercritical_lower` 4673（$A_1$、$n$、$K_1=1/(2048L)$、$L=2\log(M{+}1)$ 在 4683–4697；4993–5000 收尾）、`dimH_multiResidueSet_supercritical_rate` 5012、`..._one_two_supercritical_rate` 5027 | [AP]（额外数字恰为 $m{+}r_0$，尺寸 $\asymp m$）+ [MUL]（$1/48\le\mathcal L^j1\le4$ 来自 S2） | 需要尾中存在 $a_1\in[N_m,cN_m]$（等差尾取 $\rho+M$ 即可）。sofic 核：$\mathcal L^j1$ 的下界须对状态一致（PF） | 等差尾 routine；sofic hard |

## 5. ① 依赖 [AP] 的关键步骤清单（统一理论必须重做之处）

按对结论的支撑强度排序：

1. **S6 核/尾分离**（`transferOp_multiResidueAlphabet_eq` 1153）：整个 Part 3–6 的入口，要求尾**精确**是 $d$ 条步长 $m$ 的等差列，且核与尾剩余类重合。这是所有下游 [AP] 步骤的根。推广时须解耦为 $(F,R)$ 两参数。
2. **S14 分支尾 vs. $\zeta$**（2494）+ **S15 主尾展开**（3008）：(iv) 的核心；依赖 Hurwitz/黎曼 $\zeta$ 因子分解 $m^{-(1+\varepsilon)}\zeta(1+\varepsilon)$，仅对等差分支成立。已对位移通用，未对步长/非等差通用。
3. **S19/S20 速率指数 $2s_0$**：上界的 $O(m^{-2s_0})$ 与下界的 $(2m)^{-2s_0}n/48\ge1$ 都依赖「尾数字尺寸 $\asymp m$」。
4. **S7 尾界**（`tsum_arith_tail_le` 1682）：按等差列实现；但对**极限** (ii) 可被一般计数界替代（见 ②）。
5. **S10 1/2 地板**：工作区只证明了「含无限等差子列 ⇒ $>1/2$」（`half_lt_dimH_residueConstSet` 1507）。一般无限字母表的地板未被覆盖。
6. **定义层**：$\mathcal A_{m,S,B}$ 本身把「核」与「剩余类」绑定为同一 $S$，且 $s_0(S)$ 的 $S$ 既是核又是尾类索引；这是推广时第一个要动的地方。

## 6. ② 可直接推广的 [MUL]/[FS]/[GEN] 部分

- **[MUL] 全部**（S1、S2、S3、S13、S18 及 S4/S5/S16/S20 中的界）：对任意正数字母表逐字成立；连分母可乘性与词和单调性与字母表的算术结构无关。
- **[GEN] 全部**（S4、S5、S8、S9、S12、S16、S17；判据 `TransferOperatorDim.lean` 304/420/926/1491）：字母表无关。
- **[FS]**：现证明中没有严格意义的有限状态步骤（无状态转移、无 PF）。「最终周期」只以「$d$ 个剩余类索引尾和」的形式出现（S6、S15），其 [FS] 替代物就是 ③ 中的条件 (C4)。因此对**最终周期**字母表，所有 [AP] 步骤都能以重参数化 $(S,B)\mapsto(F,R)$ 逐字保留，难度 routine；真正需要新 [FS] 数学（PF、状态向量预解式）的只有 S2/S5/S18/S20 的下界部分。
- **【推断】极限 (ii) 对 [AP] 的依赖是便利性的**：上界 S8 只需尾和 $\to0$（S7 可换一般界），下界 S9 只是单调性；唯一只有 [AP] 路线被形式化的是地板 S10。故极限公式很可能对「固定有限核 + 一致逃逸的无穷尾」这一更宽的类成立，但 S10 的一般化未核。

## 7. ③ 「结构字母表」定义应满足的最低条件（建议，非结论）

设字母表族 $\{A_m\}_{m\ge1}\subset\Z_{\ge1}$，记 $F(A_m)=\{[0;a_1,\dots]:a_n\in A_m\ \forall n\}$。建议以下条件作为定义候选，并按强度分层：

- **(C1) 有限核**：存在非空有限 $F\subset\Z_{\ge1}$，对一切大 $m$ 有 $F\subset A_m$。以词和横坐标 $s_0(F)$（S2 定义）作为替代 $s_0(S)$ 的量。
- **(C2) 一致逃逸**：存在 $N_m\to\infty$ 使 $A_m\setminus F\subset[N_m,\infty)$。
- **(C3) 无穷尾**：对一切大 $m$，$A_m$ 无限。【推断】(C1)+(C2)+(C3) 足以给出 $\lim_m\dimH F(A_m)=\max(1/2,s_0(F))$；若尾有限，极限应为 $s_0(F)$（无地板）。(C3) 之所以需要，是因为地板 $1/2$ 目前只对「含无限等差子列」的尾被证明（S10）；若「任意无限字母表 $\dimH E_A\ge1/2$」不能以独立论证补上，则 (C3) 应加强为「尾含无限等差数列」。
- **(C4) 最终周期尾（定量结果所需）**：$A_m\setminus F=\bigcup_{\rho\in R}\{a\equiv\rho\pmod{M_m},\ a\ge N_m\}$，$R$ 有限，$M_m\to\infty$。此时 (iv) 的三阶渐近以 $d=\lvert R\rvert$、$C=C_F$、$C'=C'_F$ 成立，(v) 的速率为 $\Theta(M_m^{-2s_0})$。$\mathcal A_{m,S,B}$ 是 (C4) 在 $F=S$、$R=S\cup(-B)$、$M_m=m$、$N_m=m-\max B$ 的特例。
- **(C5) 有限状态核（sofic，可选）**：把 $F$ 换成带数字标号的有限图 $G$，$s_0(F)$ 换成路径词和的横坐标（$\rho(2s)=1$ 的根，$\rho$ 为 $M(p)_{ij}=\sum_{i\to j}a^{-p}$ 的谱半径），$V$ 换成按状态的向量。此层需要新 Lean 基础设施（sofic 连分数集、矩阵转移算子、PF），Mathlib 现成工具**未核到**。

对每个条件被违反时的后果【推断】：缺 (C1) 则 $s_0(F)$ 无定义，公式无右端；缺 (C2) 则尾和不趋于 0，S8 失效；缺 (C3) 则地板不成立（或未知）；缺 (C4) 则 (iv)(v) 的常数与指数改变（S14/S15/S19/S20 失效），但极限 (ii) 不受影响。

## 8. 待证项

| 编号 | 事项 | 现状 | 建议查法 |
| :--- | :--- | :--- | :--- |
| T1 | 任意无限字母表 $A$ 是否有 $\dimH E_A\ge1/2$ | 工作区仅对剩余类字母表形式化（1507）；文献未核到（未联网）；Bernoulli 测度 Frostman 路线为【推断】 | 先在纸面写出 Bernoulli 测度论证（权重 $\propto a^{-1}$ 的子字母表），再决定是否形式化 |
| T2 | 尾有限但元素 $\to\infty$ 时极限是否为 $s_0(F)$ | 【推断】，未核 | 用 S4/S5 对 $F\cup\{N_m\}$ 直接估计 |
| T3 | Mathlib 是否有可用的 PF / 谱半径工具 | 未核到 | 在本地 Mathlib 源码 grep `PerronFrobenius`、`spectralRadius`（本次未做） |
| T4 | sofic 连分数集的无 Bowen 维数公式 $\dimH E_G=s_0(G)$ | 工作区无；文献未核到，不引用 | 先做单状态版（即本文件 S2–S5）到多状态版的最小推广 |
| T5 | `thm:multi-residue-asymptotic`、`thm:residues-general` 的印刷编号 | 未核到（未编译） | 编译后回填 |

## 9. 检索记录

| 轮次 | 工具 / 模式 | 范围 | 命中 |
| :--- | :--- | :--- | :--- |
| 1 | grep `multi-residue-asymptotic\|multiResidueSet\|F_\{m,S,B\}` | tex | 定位 108–114、256–260、373、3799–3884、3910–3970 |
| 2 | grep `^theorem\|^lemma\|^/--\|Part [0-9]\|multiResidueSet\|poincareAbscissa`（截断 100 条） | lean | 补抽 `^theorem`（22 条）、`^lemma`（约 60 条）、`^/--`（40 条）、`^private (lemma\|theorem)`（30 条）、`^(def\|noncomputable def)`、`^/-! ###`（Part 位置 33/643/1103/1790/2371/4179） |
| 3 | grep `label\{thm:residues-general\}` + 读 3556–3615 | tex | 判据陈述 3573–3579 |
| 4 | grep `half_lt_dimH_residueConstSet\|cfAlphabetSet \(S : Set ℕ\)\|dimH_cfAlphabetSet_finset_eq_poincareAbscissa\|dimH_le_of_transferOp_le\|le_dimH_of_transferOp_ge` | lean | 用法位置 941、1095、1588、1619、1624、1644–1650、1783、3418、3654、4466、4995 |
| 5 | grep `^(private )?theorem\|^/--` | TransferOperatorDim.lean | 通用判据清单（304、420、926、1491、1507、1682、1765、2131、2242） |
| 6 | 读 1103–1118、1153–1174、1373–1495、1590–1625、2494–2511、2665–2680、3008–3037、3241–3265、3430–3459、3829–3885、4205–4216、4648–4710、5009–5030 | lean | 各步骤陈述与关键 `have` 结构 |
| 7 | 读 `verification/推广1_多残差相变与欧拉常数三阶渐近Lean4记录_20261123.md` 全文 | 作者侧记录 | 24 条审计定理清单、§四「它没做到什么」 |
| 8 | 读 AGENTS.md（workspace 根） | 规则 | 五类分类、引用纪律、形式化纪律 |
