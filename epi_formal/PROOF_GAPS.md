# 证明缺口（e+π 形式化 · 如实登记）

日期：2026-11-14（第二轮更新）。状态：**全项目零 sorry，核心命题、Meiburg 判据与 T3 Alekseyev 方向完整机器验证**。
T3（Alekseyev 方向，收敛⇒μ(π)≤5/2）已由最近整数论证完整形式化（alekseyev_bound，无 sorryAx）；
原"密度论证开放缺口"表述作废，历史障碍记录保留备查。
严禁将排版完成或骨架存在误认为定理已证。

## 最终公理审计（lake build 9056 jobs 零错误 + lake env lean Audit.lean，2026-11-14 第二轮复核）

**全部 31 个登记声明均无 sorryAx，全项目零 sorry**，仅依赖白名单公理
（e_transcendental / pi_transcendental / mu_e_eq_two + propext / Classical.choice / Quot.sound；
meiburg_criterion 已由 F2 证明为定理，不再是公理）：

| 定理 | 公理依赖 | sorryAx |
|---|---|---|
| vieta_identity | Lean 基础 | 无 |
| quadratic_roots_algebraic | Lean 基础 | 无 |
| at_least_one_transcendental | e_transcendental | 无 |
| four_numbers_at_most_one_rational | e_transcendental, pi_transcendental | 无 |
| mu0_identity | Lean 基础 | 无 |
| tail_summable / tail_recurrence | Lean 基础 | 无 |
| irrMeasure_neg / add_rat / mul_rat / inv | Lean 基础 | 无 |
| theoremA_sum / diff / quot | mu_e_eq_two | 无 |
| theoremA_prod | e_transcendental, mu_e_eq_two | 无 |
| **proposition_H'（Flint Hills 桥）** | **mu_e_eq_two, pi_transcendental**（meiburg_criterion 已是定理） | **无** |
| **alekseyev_bound（T3 主定理：收敛⇒μ(π)≤5/2）** | **pi_transcendental** | **无** |
| nearest_int_le_four_mul / nearest_int_tendsto_atTop | Lean 基础 | 无 |
| term_tendsto_eventually_gt / alekseyev_eventual_lower / apprPairs_finite_of_flintHills | pi_transcendental | 无 |

注：irrMeasure_inv 与 theoremA_prod 已于上一轮证完（早期摘要曾误记为未证，现已核实修正）。

## 重大定义修正（已固化，勿回退）
1. 分子取 **ℤ**（原骨架取 ℚ 导致逼近集恒全集、sSup 恒 0 的退化）。
2. 值域取 **ENNReal**（ℝ 的 sSup 无法表示 Liouville 数的 +∞）。
3. ε-吸收比较引理 irrMeasure_le_of_eps 用 ENNReal.le_of_forall_pos_le_add，无需有上界。

## 已就绪的分析工具（已证，可复用）
- irrMeasure_le_of_eps：ε-吸收 ⇒ sSup 比较。
- apprSet_downward / irrMeasure_mono / irrMeasure_congr / irrMeasure_neg。
- const_absorption(_nn)：常数 C·Q^(−ν) 吸收（分母无界限制 Q>T）。
- apprPairs_denom_unbounded / apprPairs_num_unbounded：固定分母/分子 ⟹ 另一坐标有限。
- mul_nat_le(_rev) / mul_nat_eq / add_rat_le。

## T3 现状（2026-11-14 第二轮更新：已完整机器验证，缺口闭合）

**alekseyev_bound（Flint Hills 收敛 ⇒ μ(π)≤5/2）已完整形式化，无 sorryAx**，
仅依赖 pi_transcendental + 基础公理。路线为修订包更正 1 的最近整数论证：
1. p=round(qπ)：|p−qπ|≤1/2（abs_sub_round）、p≤4q（π<4+整数性）、p→∞（qπ−1/2→∞）。
2. |sin p|≤|p−qπ|（abs_sin_int_le，周期+Lipschitz）。
3. 收敛⇒项→0⇒对任意 B 最终 n³sin²n>B（term_tendsto_eventually_gt）；
   取 B=64=(4^(3/2))²，开方得 p^(3/2)|sin p|>4^(3/2)。
4. 对所有整数 a 一致：q^(5/2)|π−a/q| = q^(3/2)|qπ−a| ≥ q^(3/2)|qπ−p|
   ≥ 4^(−3/2)·p^(3/2)|sin p| > 1（p≤4q ⇒ q^(3/2)≥4^(−3/2)p^(3/2)）。
5. 吸收 ε（q≥1 ⇒ q^(−ε)≤1）得最终一致下界 |π−a/q|≥q^(−(5/2+ε))。
6. ν>5/2 取 ε=ν−5/2，好逼近对集有限（apprPairs_denom_unbounded 反证）；
   apprSet⊆[0,5/2] ⇒ sSup≤5/2。
**关键**：只对 p=round(qπ)（自动 p≍q）用 sin 下界，绕开分子分母障碍，无需密度论证。

原 FlintHills.lean 的 2 处 sorry（alekseyev_diophantine / alekseyev_bound 旧陈述）已弃用删除（历史）。
以下为朴素逐项法障碍的历史记录，保留备查。

### 1. alekseyev_diophantine（原陈述方向错误，已弃用；历史障碍记录）
陈述：通项趋于 0 ⇒ ∀ε>0，最终 |π−m/n| ≥ n^(−(5/2+ε))（n 作分母）。

**本轮发现的数学障碍（非 tactic 问题，已回退错误证明）**：
- sin 下界 abs_sin_int_le 给出 |sin n| ≤ |n−mπ|。
- 代数恒等式 |n−mπ| = **|m|·|π−n/m|**：这里 **n 是分子、m 是分母**
  （sin n≈0 ⟺ n≈mπ ⟺ π≈n/m）。
- 但 irrMeasure 定义与引理陈述用 **n 作分母** 的 |π−m/n|。
- 错误写法 |n−mπ| = n|π−m/n| 不成立（n−mπ ≠ −n(π−m/n)）；
  field_simp;ring 残骸 `↑n−↑m·π = −(↑n·π)+↑m` 即此代数错误的证据。

**正确路线（待形式化）**：
1. 先证分子版引理：通项→0 ⇒ 最终 |π−n/m| ≥ |m|^(−(5/2+ε))（n 分子、m 分母）。
   由 |sin n|≤|m||π−n/m|，项 ≥ 1/(n³·m²·|π−n/m|²)；项→0 给 |π−n/m|²≥1/(n³m²·项)。
   需处理 n≍mπ（n 与 m 同阶）以把 n³ 换成 m³，得 m^(−5/2)。
2. 再经分母无界性 + 双射换算到分母版（与 mul_rat/inv 的互换技术同源）。
3. 由 ε 任意取 sSup 得 μ(π)≤5/2。

### 2. alekseyev_bound（收敛 ⇒ μ(π)≤5/2，原 sorry 已弃用）
原依赖 alekseyev_diophantine + irrMeasure_le_of_eps。属已发表（Alekseyev 2011,
arXiv:1104.5100）但非平凡的分析形式化；其完整密度论证仍是开放缺口（非 sorry）。

## 已证的 T3 周边（无 sorry）
- flint_hills_term_tendsto_zero：Summable.tendsto_atTop_zero。
- flint_hills_diverges_bound：Meiburg 判据逆否（发散 ⇒ μ(π)≥5/2）。
- meiburg_criterion：**已是定理**（F2 完整机器证明，MeiburgConvergence.lean；
  预印本 arXiv:2208.13356 仅作历史来源，不再作为公理依赖）。

## F2 进展（2026-11-13，第二环：Meiburg 公理→定理；已完成，以下为历史记录）

**新建 EpiFormal/Meiburg.lean，已证 7 引理（无 sorry，lake build 9054 jobs 零错误）**：
1. apprPairs_finite_of_mu_lt：μ(x)≤M ⇒ ν>M 的好逼近对集有限（μ 定义直接推论）。
2. eventual_approx_lower_bound：μ(x)≤M ⇒ ∀ε>0 最终 |x−m/n|≥n^(−(M+ε))（n 分母，
   有限例外集取分母 max；**走 μ 上界方向，避开 T3 分子分母障碍**）。
3. diff_quotient_error_bound：差商 (p₂−p₁)/(q₂−q₁) 误差 ≤(q₁A+q₂B)/(q₂−q₁)（纯代数+三角）。
4. good_approx_diff_quotient_bound：ν-好逼近差商误差 <(q₁^(1−ν)+q₂^(1−ν))/(q₂−q₁)（严格）。
5. sparsity_exponent_estimate：实数指数估计，条件 2q₁^(1−ν)<Q^(1−ν−δ) ⇒ 分式<Q^(−ν−δ)。
6. sparsity_diff_quotient_good：δ-邻近好逼近差商是 (ν+δ)-好逼近（组合 4+5，稀疏性核心）。
7. fixed_denom_fiber_finite：固定分母 d 的 ν-好逼近分子 p 有限（p∈Icc⌊L⌋⌈U⌉，重数界定基础）。

**剩余结构（研究级分析，数百行，待形式化）**：
- (a) 重数界定：同一差商 (p₂−p₁,q₂−q₁) 可能由多对产生，需界 Q_max（Meiburg 第8页压缩步）。
- (b) 二进块计数：由 (a)+μ 定义 ⇒ 好逼近分母在 [2^k,2^{k+1}) 内 O(2^{kε})（稀疏性引理计数形式）。
- (c) 项上界：sin 下界 → 1/(n³sin²n) 按逼近指数分类（好项大但稀疏，坏项一致小）。
- (d) 精细划分求和：Meiburg 线性函数 f(μ)=1+u/v−μ，μ<5/2 时 f>0，有限区间各贡献收敛子和。
- (e) 接线：把 FlintHills.lean 的 axiom meiburg_criterion 改为 theorem，重跑公理审计。

**关键简化**：H′ 只需 μ(π)=2 特例（非任意 μ<5/2），可用二进块计数直接论证，比完整精细划分更可行。
**诚实定位**：F2 是纯形式化工程（无新数学风险），但工作量大；当前完成代数核心，分析计数层待续。

## F2 收敛层进展（2026-11-13，新建 EpiFormal/MeiburgConvergence.lean，9 引理无 sorry）

依据参考证明 Epi_F1_F4.pdf §9.5（Lemma 9.11–9.14）。已证：
1. distToNearestInt 定义 + 最小性/≤1/2/非负/周期性/取负不变性（5 引理）。
2. uniform_approx_bound：μ(π)≤M<s ⇒ ∃C>0 统一常数，所有 a,b>0 有 |π−a/b|≥C·b^(−s)
   （有限例外集 bˢ|π−a/b| 正最小值与 1 取 min；π 无理保证正性）。
3. circle_spacing（Lemma 9.11）：∃c>0，‖h/π‖≥c·h^(1−s)。j=round(h/π)；
   j≥1 用 |π−h/j|≥C·j^(−s) 与 j≤h；j=0 单独处理 ‖h/π‖=h/π。c=min(C,1)/π。
4. block_point_lower：N≤n<2N ⇒ ‖n/π‖≥c·(2N)^(1−s)（n<2N,1−s<0 反序单调）。
5. block_pair_spacing：N≤n,m<2N,n≠m ⇒ ‖(n−m)/π‖≥c·(2N)^(1−s)
   （d=max−min∈[1,2N)，符号不变性化归 block_point_lower）。
6. abs_sin_add_int_mul_pi：|sin(x+mπ)|=|sin x|（周期平移）。
7. sin_ge_two_distToNearestInt（Jordan，Lemma 9.13 核心）：|sin n|≥2‖n/π‖。
   n=πy+jπ，|y|=‖n/π‖≤1/2，Real.mul_abs_le_abs_sin 给 |sin(πy)|≥(2/π)|πy|=2|y|。

8. packing_count（floor 单射法）：S 元素≥δ、两两距≥δ ⇒ #{≤t}≤⌊t/δ⌋+1。
   x↦⌊x/δ⌋₊ 单射（同值则距<δ 矛盾），像含于 Icc 0 ⌊t/δ⌋。
9. rep_injective：y(n)=n/π−round(n/π) 单射（π 无理；y(n)=y(m)⇒n−m=kπ⇒k=0）。
10. dyadic_block_count（Lemma 9.12，完整证完）：块 {N≤n<2N} 中 ‖n/π‖≤t 的点数
   ≤2(⌊t/δ⌋+1)。正负侧代表元各用 packing_count；filter 谓词需显式 (n:ℕ) 标注。

11. block_term_bound：N≤n<2N ⇒ 1/(n³sin²n)≤1/(4N³‖n/π‖²)（n³≥N³ + Jordan）。
12. sum_inv_sq_le_card（宽松版，已证）：∑_S 1/x²≤card(S)/δ²（每项≤1/δ²）。

## F2 完成（2026-11-13，三步全部机器验证，meiburg_criterion 公理已消除）

**MeiburgConvergence.lean 20 个声明全部无 sorry**，完整证明链：
- 圆周间距 circle_spacing（μ(π)<s ⇒ ‖h/π‖≥c·h^(1−s)，统一常数+ j=0 单独处理）。
- 二进块计数 dyadic_block_count（packing_count floor 单射法 + rep_injective）。
- Jordan sin_ge_two_distToNearestInt（|sin n|≥2‖n/π‖）。
- 精确常数界 sum_inv_sq_const（∑_S 1/x²≤(2/δ²)∑'1/(i+1)²，单射 g=⌊x/δ⌋−1 重索引）。
- 块和 block_sum_bound（≤C_s·N^(2s−5)）。
- 几何求和 flint_hills_converges_of_mu_lt（部分和单调有界 + tendsto_atTop_ciSup +
  hasSum_iff_tendsto_nat_of_nonneg；二进块分解 Ico_union_Ico_eq_Ico）。

**接线**：FlintHills.lean 的 `axiom meiburg_criterion` 已改为 `theorem`，
直接 exact flint_hills_converges_of_mu_lt。

**公理审计（lake env lean Audit.lean，全部无 sorryAx）**：
- meiburg_criterion：[pi_transcendental, propext, Classical.choice, Quot.sound]（不再是公理）。
- flint_hills_converges_of_mu_lt / circle_spacing / dyadic_block_count / block_sum_bound：同上。
- **proposition_H'：[mu_e_eq_two, pi_transcendental, propext, Classical.choice, Quot.sound]
  —— meiburg_criterion 公理彻底消失**，仅余 μ(e)=2 与 π 超越性两个经典结果公理。

**整体构建 9056 jobs 零错误。全项目零 sorry（T3 两处 sorry 陈述已弃用删除，2026-11-14）。**

**诚实边界**：F2 消除的是预印本公理依赖，提升论文可信度；e+π 无理性本身仍开放，
proposition_H' 仍是条件命题（e+π 有理 ⇒ Flint Hills 收敛），收敛本身不构成矛盾。

## 诚实边界
- **e+π 无理性本身仍是开放问题**，本项目未证明、也不声称证明。
- proposition_H' 是**条件性**结果：e+π 有理 ⇒ Flint Hills 收敛，
  条件于 mu_e_eq_two（μ(e)=2）与 pi_transcendental（π 超越）；
  **meiburg_criterion 已由 F2 证明，不再是公理**。
- T3 的 Alekseyev 方向（收敛⇒μ(π)≤5/2）**已完整机器验证**（alekseyev_bound，2026-11-14）；
  其前提 Flint Hills 收敛本身仍是开放问题，故该定理是条件性结果。

## T3 进展（2026-11-14，Alekseyev.lean，3+6 声明无 sorryAx）
- sin_nat_ne_zero：n≥1 ⇒ sin n≠0（π 无理）。
- sin_eventual_lower：项→0 ⇒ 最终 |sin n|≥n^(−3/2−ε)（aₙ<1 ⇒ n³sin²n>1）。
- abs_sub_mul_pi_factor：|n−mπ|=|m|·|π−n/m|（m≠0）。
- **历史障碍（保留）**：sin 下界给 |π−n/m|≥n^(−3/2−ε)/|m|；要得 μ(π)≤5/2 需 n≤C'|m|，
  但下界对所有大 n 成立（含 n>π|m|，方向反转）。故朴素逐项论证无效。
- **本轮闭合（第二轮）**：最近整数论证（修订包更正 1）绕开该障碍——
  新增 nearest_int_le_four_mul / nearest_int_tendsto_atTop / term_tendsto_eventually_gt /
  alekseyev_eventual_lower / apprPairs_finite_of_flintHills / **alekseyev_bound**，
  全部无 sorryAx。alekseyev_bound 仅依赖 pi_transcendental + 基础公理。
- 全项目零 sorry；登记声明 25+6=31。
- 踩坑记录：阈值须取 B=(4^(3/2))²=64 而非 4^(3/2)=8（开方后才得 p^(3/2)|sin p|>4^(3/2)）；
  p≤4q 用整数性（round<4q+1⇒≤4q），勿试图证 qπ+1/2≤4q（π 可任意接近 4 时不成立）；
  abs_sin_int_le 的 π 系数参数是 q（分母）不是 p；rpow 自然数幂转换需 rpow_natCast 显式桥接。

## 下一步（可恢复执行）
- （可选）形式化修订包补充页 2 Prop4 阶乘判据、S1–S7 辅助引理；需先取得或重建那 4 个新 .lean。
- 或继续开放问题的创造性探索（新加法恒等式 / Schanuel 实例）。
- 每步 lake build + #print axioms 复核，更新 LEMMA_AUDIT。

## M6 完整联合编译后的缺口状态（2026-11-14）

**已闭合（机器验证，无 sorryAx）**：修订包 S1–S7 + Prop3/Prop4 全部形式化并入主项目。
lake build 9064 jobs 零错误；Audit.lean sorryAx 计数 = 0；登记声明 31 + 179 = 210。
- S1 Theorem2 分类格 + S2 Cor3 间隙 1/4（B）
- S3 Lemma5 + S4 Theorem6 有限谱 {k/4}（C，无公理）
- S5 Theorem7 符号聚类 + Theorem8 实现（D，不依赖 deltaSel）
- S6 Theorem9 缺陷尾⇔格 + Cor10 单射 + 精细尺度 + 控制反例（E）
- S7 Theorem11 双指标三等价 + 定量推论（F）
- Prop3 符号判据双向等价（H）
- Prop4 阶乘判据（G，无公理）

**仍开放（研究级缺口，非 sorry，严禁声称解决）**：
1. **e+π 无理性本身**——本轮全部成果不判定它。
2. **Prop3 符号估计**：对每个 B>0 无穷多正乘积（H 文件末节记录坐标，未建立）。
3. **S7「对每个 B 匹配集有限」**：F theorem11 只是等价判据，该目标未证。
4. **Prop4 右侧极限 n·{-n!π}→1**：G 不作断言，开放命题。
5. **E Cor10 满射**：依赖 D theorem8_realization（已具备），尚未接线；本轮只证单射。

**公理化（未机器验证，显式登记）**：A 组两条 deltaSel（deltaSel_tendsto_zero / abs_deltaSel_lt），
经典 e 连分数误差估计，mathlib v4.35 无 e 展开定理。论文必须显式标注非机器验证。

**数值辅助（非内核）**：I 组 4 脚本，sympy/mpmath，只排除整数情形、乘积趋于1非1/2，不证明开放问题。

**待办收口**：论文 paper.tex M6 章节写入 + MiKTeX 重编译；归档同步重打包。

## M8 代数无关条件归约后的缺口状态（2026-11-14）

**新增机器验证（条件性，无 sorryAx）**：AlgebraicIndependence.lean 四定理
transcendental_add/sub/mul/div_of_algebraicIndependent：
前提 AlgebraicIndependent ℚ ![e,π] ⇒ e+π、e−π、e·π、e/π 全超越。
仅基础公理，不依赖 e_transcendental/pi_transcendental。lake build 9066 jobs 零错误。
论文 §9.8（thm:ai-reduction）已写入，重编译 26 页零错误。

**新增显式开放缺口（研究级，严禁声称解决）**：
6. **e 与 π 在 ℚ 上代数无关**——M8 四定理的前提，未证。本质上等价于
   Schanuel 对 {1,iπ} 的实例（e¹=e、e^{iπ}=−1）。这是把破局缺口 isolated
   成的最干净单一假设；现有方法（行列式/插值/周期）无条件供不出。

**与既有缺口的关系**：M8 不闭合缺口 1（e+π 无理性）——它把「四组合超越」
归约到缺口 6（代数无关），是更强的条件性结果，但缺口 6 本身比缺口 1 更深。
缺口 2–5 状态不变。乘法孪生引理（at_least_one_transcendental）项目早已具备，本轮未重复证明。

**诚实边界**：M8 是条件性归约，非破局证明。e+π 无理性、e/π 代数无关均仍开放。

## M9 E Cor10 满射接线后的缺口状态（2026-11-14）

**缺口 5（E Cor10 满射）已闭合**：DefectFibres.corollary10_surjective 机器验证，
仅基础公理、无 sorryAx、不依赖 deltaSel。缺陷尾映射 F/L → 有界整数序列尾空间 升级为**双射**
（单射 corollary10_injective 依赖 deltaSel_tendsto_zero；满射仅基础公理）。
调用 D theorem8_realization 的 xOfSeq 构造，桥接 Mseq=Msel 同源缺陷，证构造实数 ∈F。
lake build 9066 jobs 零错误；论文 §9.6 S6 更新为双射，26 页零错误。

**仍开放缺口**：1（e+π 无理性）、2（Prop3 符号估计）、3（S7 对每个 B 匹配集有限）、
4（Prop4 右侧极限）、6（e、π 代数无关）。缺口 5 移除。

## M10 审阅后：确立"逃离"主线与精确边界（2026-11-14）

**主线（缺口 3 的精确化，优先）**：∀B≥1,∀N,∃j≥N, D_j(B)=T_j+B·C_j≠0。
Escape.lean 已形式化精确恒等式 D_j(B)=ε_j·Q_{j+1}−ε_{j+1}·Q_j 与目标重述
（irrational_iff_inf_mismatch，复用 F 三等价）。**右侧非零性未证**。

**核心边界（必须守住）**：仅靠 Q_j 递推 + |ε|≤1/2 **不可能**完成最后一步——
把 π 换成 A/B−e，这些通用条件确实允许最终匹配。新增论证必须用到 π 本身的特殊性质。
每个新引理须回答"新增了哪条关于 π 的信息"；若仍只用通用递推+取整，则未跨过缺口。

**辅助/备选**：符号逃离（∃ε_B>0, ‖BQ_jπ‖≥ε_B 无穷多次）作辅助；
阶乘逃离（{n!π}≤½ 无穷多次）作备选。注意阶乘判据方向：证极限=1 推出有理性，须排除它。

**验证状态（M11 更新）**：Windows 缓存已修复，Escape.lean `lake env lean` **EXIT 0**，
公理审计无 sorryAx（恒等式仅基础公理；目标重述含 deltaSel_tendsto_zero，合规）。
**恒等式+目标重述已机器验证；右侧 D_j(B) 非零性仍开放。**
**仍开放**：缺口 1–4、6 不变；主线非零性是当前精确攻击目标。
三路调研确认：缺"关于 π 的子列下界/分布"新信息；μ(π) 上界方向不符，通用条件不足。

**诚实边界**：Cor10 双射是结构定理，不判定 e+π 无理性；D theorem8 存在性构造不判定 x=Bπ 缺陷。

## M16 归约终点 P1（2026-11-15，Dj 归约链）

**缺口 7（P1，归约终点，开放）**：∀B≥1, Bπ∉L，其中 L=ℤ+ℤ(e+1)/2。
EscapeReduction.lean 已机器验证归约链：D_j(B)=0 eventually ⇒ Bπ∈L
（reduction_to_lattice），故 P1 ⇒ e+π 无理（P1_imp_irrational，条件定理）。

**难度声明（D2-9，防自欺）**：Bπ∈L ⇔ ∃m,n∈ℤ, 2Bπ-ne∈ℤ。
n=0 ⇒ π∈ℚ（已关闭）；n≠0 是 {1,e,π} 的整线性关系（π 系数 2B≠0）。
原问题 e+π∈ℚ 等价于该族子族 n=-2B 的成员资格。**无已知定理排除一般整线性关系**。
故 P1 与原问题同族难度，归约是「换靶」不是「降难」。

**边界测试（D1-5）**：归约链每一步对 π'=A/B-e 同样成立，故归约本身不产生矛盾；
矛盾只能来自 P1，而 P1 对 π' 失败（π' 使 Bπ'∈L）。缺口精确隔离到 P1，未跨过。

**P1 的三条子路线（清单阶段 2，均开放，设 kill 条件）**：
- 2A 线性形式/Baker：π=log(-1)/i 可入框，但 e 无已知「代数数的对数」表示
  （断言 e 不是任何代数数的对数本身等价于 e^e 超越性一类开问题，非定理）；
  四指数/六指数对 2Bπ-ne=k 无法凑齐全代数矩阵（与 Prop 4.13 同型 blocked）。
- 2B 连分数/传递：需 π 连分数的任意结构性定理（如分部商无界）配合 Thm 4.6 传递像；
  π 分部商无界本身开放。
- 2C 定量间隙：把 S2 定量化求 φ(dist(x,L))，回灌为线性形式下界 |2Bπ-ne-k|≫B^{-t}；
  所需 t 与现有超越性度量文献最好 t 的差距待算。

**回灌接口（D2-10）**：一旦有任何 |2Bπ-ne-k| 下界（哪怕只对这族系数），
可经归约链直接回灌。价值在接上 Baker/Lindemann-Weierstrass 文献接口。

**诚实边界**：P1 未证；e+π 无理性仍开放。归约链已机器验证但只是换靶。

## M17 四路可行性判定（2026-11-15，并行推理）

**精确充分解析靶（2C 推导已核）**：∀B≥1, limsup_j j‖BQ_jπ‖>1/8
（等价稀疏子列 ‖BQ_jπ‖>1/(8j)）⇒ e+π∉ℚ。这是缺口 7/P1 的丢番图下界形式。
**关键修正**：S2 间隙本就一致（limsup≥1/4 与 dist(x,L) 无关），定量引理不用 x∉L；
清单 D2-10 设想的连续 φ(dist) 不必要，φ(d)=1/4(d>0) 在 0 间断。
**差距**：μ(π)≤7.1032 给的下界沿超指数 Q_j 衰减到 0，j=80 差 ~10^1010（即便 μ=2 差 10^164）；
|2Bπ-ne-k| 无任何已知无条件下界。靶对 π'=A/B-e 失败（limsup=0），须 π 专属下界。

**四路判定**：
- 2C 定量间隙：**等未来工具**（靶明确，所需下界远超已知）。
- 2A Baker：**no-go 封存**（e 无对数表示，与 Prop 4.13 同型；活口仅条件式）。
- 2B 连分数：**no-go**（无已知 π 连分数性质可用；匹配长度恒 1-2 无数值抓手）。
- 阶段3 π表示：**四者全出局**（Machin/BBP/Chudnovsky 产不出估计；AGM/Legendre 仅接口图）。

**封存方向（不再重复投入）**：2A、2B、D3-1 Machin、D3-2 BBP、D3-3 Chudnovsky。
**唯一真过边界杠杆**：「π是周期」（AGM/Legendre），但依赖预期假的 π∈S + 未审核 Bertolin，短期无结论。

**诚实边界**：四路均无突破，e+π 无理性仍开放。缺口需全新数学输入（π 稀疏丢番图下界 /
{1,e,π} 线性形式下界 / π 非 Hurwitz），非延长工作时间可产出。

## M18 新切入点破解判定（2026-11-15，第二轮）

**新封存方向**：
- 积分/正性法（A）：方向障碍——只给无理性或幂型逼近上界，给不出子列下界（Beukers I_j→0 反向）。
- Nesterenko+G-S 矛盾挖掘（B）：7 路径全不成立；已证定理无一控制 e 与 π 间代数关系。

**新条件定理（C，条件性非突破，前提均未证）**：
- C1：π∉E ⇒ e±π/eπ/e/π 皆超越（特别 e+π 无理）。证：e+π=a∈Q̄⊂E ⇒ π=a−e∈E 矛盾。
- C2：E∩G=Q̄ ⇒ π∉E（由 π∈G + Lindemann）⇒ C1。
- 最弱前提序：Schanuel(1,iπ)⇔e,π 代数独立 > X₂(E∩G=Q̄) > X₁(π∉E) > X₀(1,e,π 线性无关=P1)。
- 单位猜想（2610.16603）单独无推进（π∉E× 析取不闭合）。
- **未获得低于 P1 的真实弱化**；C1/C2 可作论文条件框架收录。

**文献核查（D）**：2024-2026 无 supplying 缺口的新输入；OpenAI μ=2 即便成立类型不符
（非有效、不含子列下界，沿超指数 Q_j 仅给 ‖qπ‖≥q^(−1−ε)）。Carella 1706.08394 疑似符号错误。

**诚实边界**：两轮（M17+M18）共封存 7+ 方向，无突破；e+π 无理性仍开放。
缺口本质：π 沿 e 收敛子分母的稀疏丢番图下界，当前数论界无此工具。

## M33 OBL-3b 几何零件：同级分离已验证 + 抓出假嵌套命题（2026-11-18）

**已验证（Lean 内核，仅基础公理，零 sorryAx）**：
```
'WeightedCantor.winterv_disjoint'  [propext, Classical.choice, Quot.sound]
```
数学：同级 j 不同中心 k₁≠k₂ 的加权区间不交，条件 2·wrad_j<1/Q_j
（中心距≥1/Q_j>2wrad_j=直径和）。lake build 9067；Audit 退出码 0；sorryAx=0。

**敌意审查抓出的真实数学错误（第①类：步骤不推出）**：
曾试图证"孩子区间⊆父区间"（winterv_nest）。**这是假命题**：分支条件
|c_j−c_{j+1}|≤r_j+r_{j+1} 是区间**相交**条件，不是**嵌套**条件
（嵌套需 |c_j−c_{j+1}|≤r_j−r_{j+1}）。linarith/nlinarith 反复失败正因在证伪命题，
内核正确拒绝。已删除该假引理，未入库。原 T-finite（DimHFinite）同样用相交条件，
上界覆盖论证只需"覆盖+基数界"，**不需嵌套**，故已验证的上界不受影响。

**对 OBL-3b 的影响**：Frostman 下界需 Cantor 极限集（嵌套紧集交）。
现有分支是相交型，不直接给嵌套 Cantor 结构。两条路：
(a) 改用嵌套子分支（中心差≤r_j−r_{j+1}），需重新估分支数下界；
(b) 用相交型覆盖直接构造 Frostman 测度（不依赖嵌套）。
二者皆未形式化。**下界 dimH≥1−α 仍开放**，不声称已解决。

**已备 Frostman 零件**：分支下界（M32）+ 同级分离（本条）+ 分支上界（M30）+
mathlib le_dimH_of_hausdorffMeasure_ne_zero（μH[d]≠0⇒d≤dimH）。
缺：Cantor 测度构造 + 质量分布原理（mathlib 无现成 Frostman 定理）。

## M32 OBL-3b 关键零件：分支下界已机器验证（2026-11-18）

**已验证（Lean 内核，仅基础公理，零 sorryAx）**：
```
'WeightedLower.width_ge'                  [propext, Classical.choice, Quot.sound]
'WeightedLower.fiber_card_weighted_ge'    [propext, Classical.choice, Quot.sound]
'WeightedLower.fiber_card_weighted_ge_scale' [propext, Classical.choice, Quot.sound]
```
数学：分支区间宽度 B−A=2(wrad_j+wrad_{j+1})Q_{j+1}≥8t·j^{1−α}（用 Q_{j+1}≥4jQ_j）。
内部父中心（0≤A 且 B≤Q_{j+1}）的孩子数 ≥⌊B−A⌋≥⌊8t·j^{1−α}⌋。
单射 m↦ceil(A)+m（m<⌊B−A⌋）进入分支集。lake build 9065；Audit 退出码 0；sorryAx=0。

**过程中修正的真实数学错误**：初版由 a0+m<B+1 推 a0+m≤B（实数下不成立！）。
正确论证用 m+1≤L（Nat，因 m<L）+ a0<A+1 + L≤B−A ⇒ a0+m+1<B+1 ⇒ a0+m≤B。已修正验证。

**OBL-3b 整体仍开放**：下界 dimH≥1−α 需 Frostman 质量分布原理——
在 Cantor 极限集上构造概率测度 μ 使 μ(B(x,r))≤C r^{1−α}。
必需零件已备：分支下界（本条）+ 区间分离（中心距 1/Q_n≫半径 r_n）+ 分支上界（M30）。
但 Frostman 测度构造与质量分布原理本身**尚未形式化**（mathlib 无现成 Frostman 定理）。
故"相变恰好=1−α"仍只证上界半；下界半是真实开放工程/数学，不声称已解决。

## M31 OBL-3a 完全闭合：加权相变上界完整机器验证（2026-11-18）

**主定理（Lean 内核验证，仅基础公理，零 sorryAx）**：
```
'WeightedFinal.dimH_levelSetα_le'  [propext, Classical.choice, Quot.sound]
```
即对 0≤α≤1、一切实数 c，$\dim_H\{x:\Lambda_\alpha(x)\le c\}\le1-\alpha$，
其中 $\Lambda_\alpha(x)=\limsup_j j^\alpha\|Q_jx\|$。
lake build 9067 jobs 零错误；Audit.lean 退出码 0；全项目 sorryAx=0。

**完整证明链（全部已验证，新增 4 模块）**：
- WeightedFiber：加权分支上界 ≤⌊16t(j+1)^{1−α}⌋+1（单调放大复用 fiber_card_le）。
- WeightedDimHCore：加权存活中心递归基数界 ≤C0·K^n·((J+n)!)^{1−α}；ediam(winterv)≤2wrad。
- WeightedUpper：centerOf 成员/分支/递归（加权版）；wtailSet 覆盖；
  wrad≤t/(J+n)!；内容界→0（s>1−α，用 content_core_tendsto）；
  hausdorffMeasure_wtailSet_zero；dimH_wtailSet_le（≤1−α，反证取 r∈(1−α,iInf)）。
- WeightedFinal：周期性 apprSeqα_add_intCast；levelSetα⊆wtailSet 可数并；
  Lipschitz 平移+dimH_iUnion+iSup_le 装配得 dimH_levelSetα_le。

**过程中修正的真实数学错误**：初版误把加权上界写成 dimH=0（应为 ≤1−α）；
反证法选 s=(1−α)+r/2 不能保证 s<r，改为取 r∈(1−α,iInf)、s=(1−α+r)/2。已修正并验证。

**推论**：α=1 退回 T-finite（dimH=0）；α=0 给平凡上界 1。临界指数 1−α 随 α 线性。

**诚实边界**：上界半完全机器验证。**下界 dimH≥1−α（OBL-3b）仍开放**（需 Frostman 质量分布）。
故"相变恰好=1−α"只证了一半。e+π 无理性仍开放（OBL-4）。

## M30 OBL-3a 关键零件：加权分支上界已机器验证（2026-11-18）

**新增 `EpiFormal/WeightedFiber.lean`（仅基础公理，零 sorryAx，9064 jobs）**：
```
'WeightedFiber.fiber_card_weighted_le'  [propext, Classical.choice, Quot.sound]
```
**内容**：对 0≤α≤1、t≥0、j≥1、父中心 c，加权子中心数
（条件 |c/Q_j − k'/Q_{j+1}| ≤ wrad t α j + wrad t α (j+1)，wrad=t/(j^αQ_j)）
≤ branchB(t·(j+1)^{1−α}) = ⌊16t(j+1)^{1−α}⌋+1，即 **j^{1−α} 标度**。

**省力路线（不重证单射计数）**：
- 关键幂不等式 `pow_cross`：j ≤ j^α·(j+1)^{1−α}（rpow 单调 + j=j^α·j^{1−α}）。
- `wrad_le_rad`：wrad t α j + wrad t α (j+1) ≤ rad t' j + rad t' (j+1)，t'=t(j+1)^{1−α}。
- filter 单调（card_le_card）+ 已验证 `DimHCore.fiber_card_le t'` 直接得结论。

**OBL-3a 剩余（装配，非新数学）**：把 DimHFinite 的覆盖论证推广到 wrad：
存活中心递归用加权分支界 ⇒ N_n ≲ (8t)^n(n!)^{1−α}；直径 ≤ 2t/(n^α n!)；
s-内容 ≲ K^n(n!)^{1−α−s} → 0（s>1−α，即已验证 `WeightedPhase.content_core_tendsto`）；
Hausdorff 判据 + 可数并 ⇒ dimH{Λ_α≤c} ≤ 1−α。零件齐备，属 DimHFinite 型装配工程。

**诚实边界**：上界 dimH≤1−α 目前为纸面严格证明（加权相变上界定理.md）+ 两个核心零件
（分支上界、内容核心）机器验证；完整装配未做。下界（OBL-3b）仍开放。e+π 仍开放。

## M29 OBL-2 完全解决：阈值 1/4 可达，显式构造点已机器验证（2026-11-18）

**主定理（Lean 内核验证，仅基础公理，零 sorryAx）**：
```
'QuarterPointFinal.lambda_x0_eq_quarter'  [propext, Classical.choice, Quot.sound]
```
即存在显式实数 x0 使 $\lim_{j\to\infty} j\|Q_j x_0\| = 1/4$（极限，故 Λ(x0)=1/4）。
**阈值 1/4 可达**，间隙 (0,1/4) 的端点属于谱。OBL-2 关闭。
lake build 9063 jobs 零错误；Audit.lean 退出码 0；全项目 sorryAx=0。

**构造**：M_0=M_1=0，M_{j+1}=(4j+2)M_j+M_{j−1}+1（defect≡1）；
x0 := ∑'_{j}(r_{j+1}−r_j)，r_j=M_j/Q_j（telescoping 级数，可和因 |r_{j+1}−r_j|≤1/Q_{j+1} 且 ∑1/Q 可和）。

**证明链（全部已验证）**：
- QuarterPointCore：W_j=M_{j+1}Q_j−M_jQ_{j+1} 满足 W_j=Q_j−W_{j−1}，0≤W_j≤Q_j，W_j>0；
  Q_{j+1}≥4jQ_j；r_{j+1}−r_j=W_j/(Q_jQ_{j+1})。
- QuarterPointTail：Q_{j+1}≥2Q_j（j≥1）；|r_{j+1}−r_j|≤1/Q_{j+1}；∑1/Q_j 可和。
- QuarterPointLimit（并入 Final）：summable_d；r_n=∑_{j<n}d_j；x0−r_n=∑'d(·+n)；
  Q_{j+m}≥2^mQ_j；尾和不变式 r_{j+m}≤r_j+(2/Q_{j+1})(1−2^{−m})；取极限得 x0−r_j≤2/Q_{j+1}。
- QuarterPointFinal：ε_j=Q_jx0−M_j=Q_j(x0−r_j)∈[0,2Q_j/Q_{j+1}]⊆[0,1/(2j)]；
  j≥2 时 |ε_j|<1/2 ⇒ round(Q_jx0)=M_j（GAP2）⇒ defect x0 j=1（j≥3，最终）；
  ε→0（夹逼 1/(2j)→0）；套用 ThresholdAttained.apprSeq_tendsto_quarter 得 Λ(x0)=1/4。

**推论**：x0∉L（因 j‖Q_jx0‖→1/4≠0，theorem2_classification 逆否）。
故 {Λ≤1/4} ⊋ L，不可数？（维数仍 0，由 T-finite；不可数性未证，不声称）。

**诚实边界**：这是**真实数学成果**——一个 previously open 问题（阈值端点可达性）
被显式构造+机器验证解决。但它是谱结构的精细性质，**不是 e+π 无理性突破**（OBL-4 仍开放）。
方法（defect 整数递推+Hermite 型尾和）是经典连分数技巧的实例化。

## M28 OBL-2 构造推进：GAP1 的代数与解析零件已机器验证（2026-11-18）

**新增两模块（均仅基础公理，零 sorryAx，已构建 9062 jobs）**：

`EpiFormal/QuarterPointCore.lean`（代数核心）：
- `Mseq`：M_0=M_1=0，M_{j+2}=(4(j+1)+2)M_{j+1}+M_j+1（defect≡1 的整数递推）
- `Wseq j := M_{j+1}Q_j − M_j Q_{j+1}`
- **`Wseq_rec`：W_j = Q_j − W_{j−1}（j≥1）**，W_0=0（代入两递推直接得，纯环运算）
- **`Wseq_bounds`：0 ≤ W_j ≤ Q_j 对一切 j**（归纳：W_{n+1}=Q_{n+1}−W_n，配 Q 单调）
- `Wseq_pos`：j≥1 时 W_j>0（j=1 直接算 W_1=1；j≥2 用 Q_{j−1}<Q_j）
- `Qsel_succ_ge_four`：Q_{j+1} ≥ 4j·Q_j
- `ratio_diff`：M_{j+1}/Q_{j+1} − M_j/Q_j = W_j/(Q_j Q_{j+1})

`EpiFormal/QuarterPointTail.lean`（解析零件）：
- `Qsel_ge_two_mul (j) (hj:1≤j)`：Q_{j+1} ≥ 2Q_j
  **注意 j=0 例外**：Q_1=1 < 2=2Q_0，故必须限定 j≥1（初版写"对一切 j"是假命题，已修正）
- **`ratio_diff_le`：|M_{j+1}/Q_{j+1} − M_j/Q_j| ≤ 1/Q_{j+1}**（由 0≤W_j≤Q_j）
- **`summable_inv_Qsel`：∑_j 1/Q_j 可和**（由 2^j ≤ 2Q_j 比较几何级数 ∑(1/2)^j）

**数学论证（已完成推导，形式化剩最后装配）**：
由 ratio_diff_le 与 summable_inv_Qsel，比值序列 M_j/Q_j 的部分和绝对可和 ⇒ Cauchy ⇒
x := lim M_j/Q_j 存在。尾和给出
ε_j = Q_j x − M_j = ∑_{k≥j} Q_j W_k/(Q_k Q_{k+1}) ≤ ∑_{k≥j} Q_j/Q_{k+1}
≤ Q_j/Q_{j+1}·∑_{m≥0}2^{−m} = 2Q_j/Q_{j+1} ≤ 2Q_j/(4jQ_j) = 1/(2j)。
故 j≥2 时 |ε_j| ≤ 1/4 < 1/2 ⇒ round(Q_j x)=M_j（**GAP2 同时闭合**）⇒ defect≡1 自洽。
再由已验证 `ThresholdAttained.apprSeq_tendsto_quarter` 得 Λ(x)=1/4。

**精确剩余（OPEN，OBL-2 最后一段）**：
- GAP1-final：把「绝对可和 ⇒ Cauchy ⇒ 极限存在」装配成 Lean（用
  `Summable.cauchySeq` / `cauchySeq_tendsto_of_complete` 或 `Summable.hasSum` 配尾和），
  并形式化上述尾和不等式链得 ε_j ≤ 1/(2j)。零件均已就绪，属装配工程。
- GAP2：由 ε_j ≤ 1/4 与 `abs_sub_round`/`round_eq_iff` 推 round(Q_j x)=M_j（小步）。
- 之后 x∉L 由 theorem2_classification 逆否（因 j‖Q_j x‖→1/4≠0）。

**诚实边界**：目前**仍未证出存在** Λ=1/4 的点；已证的是机制（M27）+ 构造所需的全部
代数与可和性零件（M28）。不得声称 OBL-2 已解决。数值（900 位）佐证 x≈0.1558983204，
j‖Q_j x‖↗1/4，舍入一致，但数值非证明。e+π 无理性仍开放。

## M27 OBL-2 机制突破：阈值 1/4 的可达性机制已机器验证（2026-11-18）

**背景**：OBL-2 问「Λ(x)=1/4 是否可达」（间隙 (0,1/4) 开，端点属谱否）。原为开放。

**已机器验证（`EpiFormal/ThresholdAttained.lean`，仅基础公理，零 sorryAx）**：
```
'ThresholdAttained.eps_mul_eq'                        [propext, Classical.choice, Quot.sound]
'ThresholdAttained.eps_mul_tendsto_of_defect_const'   [propext, Classical.choice, Quot.sound]
'ThresholdAttained.j_mul_eps_tendsto'                 [propext, Classical.choice, Quot.sound]
'ThresholdAttained.apprSeq_tendsto_of_defect_const'   [propext, Classical.choice, Quot.sound]
'ThresholdAttained.apprSeq_tendsto_quarter'           [propext, Classical.choice, Quot.sound]
```
**定理内容**：若 `defect x j` 最终恒为整数 d 且 `eps x → 0`，则
$(4j+2)\varepsilon_j\to d$，进而 $j\|Q_jx\|\to |d|/4$。
**d=1 时极限恰为 1/4**（是极限，强于 limsup）。
证法：由已验证 `defect_identity` 解出 $(4j+2)\varepsilon_j=D_j+\varepsilon_{j+1}-\varepsilon_{j-1}$，
三项分别取极限（$\varepsilon_{j\pm1}\to0$ 用 atTop 复合），再除 4 并吸收 $2\varepsilon_j\to0$，取绝对值。

**为何这解释了 c<1/4 的严格性（代码事实，子代理定位）**：
`Classification.lean` L599 `have h4c : 4*c < 1`，L601–603 得「最终 c·g(j) < 1」，
其中 g(j)=1/(j+1)+(4j+2)/j+1/(j−1) → 4。链：|D_j| ≤ c·g(j) < 1 ⇒ 整数 D_j=0。
**c=1/4 时 c·g(j) = 1 + 1/(2j) + j/(2(j²−1)) > 1 恒成立**（非等号），
只得 |D_j| ≤ 1，挤不出 0。故 **defect≡±1 与 c=1/4 完全相容**——
这是「边界等号失效」而非结构性障碍，正是 1/4 可达的机制。

**数值佐证（900 位 mpmath，非证明）**：
构造 M_0=0,M_1=0, M_{j+1}=(4j+2)M_j+M_{j−1}+1（defect≡1），x=M_70/Q_70≈0.1558983204098298700894012。
j‖Q_j x‖：j=2→0.18258, j=8→0.23368, j=20→0.24361, j=50→0.247476，
单调升向 1/4，差 ≈ −1/(8j)；且 `round(Q_j x)=M_j` 对所有测试 j 成立。

**精确剩余缺口（OPEN，不得声称已证可达）**：
- **GAP1（尾和估计）**：证由上述整数递推定义的 M_j 使 x:=lim M_j/Q_j 存在，
  且 ε_j=Q_j x−M_j=O(1/j)→0。思路：用行列式 ±2 的 Green 函数把 ε_j 表为
  $\sum_{k\ge j}$ 型尾和，配合已验证 |δ_k| ≤ 1/(2k Q_k) 与 Q 超指数增长。
- **GAP2（舍入一致性）**：证大 j 时 |ε_j|<1/2 ⇒ round(Q_j x)=M_j，从而 defect≡1 自洽。
  （数值已确认，但需解析证明；|ε_j|=O(1/j) 一旦成立即得。）
- GAP1+GAP2 闭合后，由已验证的 `apprSeq_tendsto_quarter` 立即得 Λ(x)=1/4，
  且 x∉L（因 j‖Q_j x‖↛0，用 theorem2_classification 逆否），**OBL-2 完全解决（可达）**。

**诚实边界**：目前**只证了机制**（条件定理：defect≡1 ⇒ 极限 1/4），
**尚未证明存在**这样的 x。不得声称「1/4 可达已证」。
子代理给出的 85% 置信度是其主观判断，非证明；构造的两个 GAP 显式未闭合。
e+π 无理性仍开放，本成果不涉及。

## M26 OBL-3 上界半：加权相变 dimH ≤ 1−α，并纠正原猜想错误（2026-11-18）

**发现原猜想错误**：第二阶段论文原猜想"α<1 时 dimH{Λ_α≤c}=1"是**错的**。
分支标度 B_j ≍ j^{1−α}（用 Q_{j+1}≤(4j+3)Q_j）使 s-内容 ≍ (n!)^{1−α−s}，
临界指数为 **1−α**（随 α 线性），而非在 α=1 处从 1 跳变到 0。
例 α=1/2 上界=1/2<1，直接否定原猜想。

**已证上界（纸面严格证明 + 解析核心机器验证）**：
定理：0≤α≤1、有限 c ⇒ dimH{Λ_α≤c} ≤ 1−α。
- 分支引理 B_j ≤ K j^{1−α}（纸面，一般 α；α=1 即已验证 fiber_card_le）。
- 内容核心 `WeightedPhase.content_core_tendsto`：s>1−α ⇒ K^n(n!)^{1−α−s}→0，
  **已 Lean 内核验证，仅基础公理**（归约到 DimHFinite.tendsto_powB_div_factorial_rpow，β=s−(1−α)）。
- 覆盖判据 + 可数并 ⇒ 上界（纸面；α=1 特例即已验证 T-finite）。
文档：outputs/加权相变上界定理.md。论文已加 Theorem thm:upper 并重编译（6 页）。

**下界开放（OBL-3b）**：dimH ≥ 1−α 需 Frostman 质量分布（存活树均匀分支 ≍ j^{1−α}），
未完成，列为猜想 conj:weight（已改写为匹配下界）。

**诚实边界**：相变"恰好=1−α"只证了上界半；下界半开放。不得声称相变完全解决。
一般 α 上界的完整 Lean 形式化（分支引理+覆盖装配带 rpow）列为 OBL-3a 工程义务；
解析核心已机器验证。e+π 无理性仍开放，本文不涉及。

## M25 OBL-5 彻底完成：两条 δ 公理已从项目物理删除（2026-11-18）

**完成状态**：`EulerConvergents.lean` 中两行 `axiom` 已替换为完整内联证明的 `theorem`，
下游全链无条件化。`lake build` 9079 jobs 零错误；`Audit.lean` 退出码 0；全项目 sorryAx = 0。

**下游公理审计（逐字，全部仅基础公理）**：
```
'Classification.theorem2_classification'  [propext, Classical.choice, Quot.sound]
'Classification.corollary3_gap'           [propext, Classical.choice, Quot.sound]
'SpectralGap.spectral_gap'                [propext, Classical.choice, Quot.sound]
'SpectralGap.levelSet_below_eq_lattice'   [propext, Classical.choice, Quot.sound]
'SpectralGap.dimH_levelSet_below'         [propext, Classical.choice, Quot.sound]
'EscapeReduction.P1_imp_irrational'       [propext, Classical.choice, Quot.sound]
```
即 C6/C7/C8/C9、S2/S3/S5 **不再依赖任何 δ 公理**。

**项目剩余公理（仅 3 条经典事实，均在白名单）**：
- `Axioms.lean`: `e_transcendental`（Hermite 1873）、`pi_transcendental`（Lindemann 1882）
- `Measure.lean`: `mu_e_eq_two`（μ(e)=2，经典）
两条 δ 公理已不在其中。

**重构方式（打破循环依赖）**：
1. 删除 `PadeIntegral.lean` 中未被使用的 `import EpiFormal.EulerConvergents`
   （该文件只用 padéR/padéP，不需要 δ）——这一步打破了
   DeltaSign→DeltaReduction→DimHCore→SpectralGap→EulerConvergents 的环。
2. 把 `Qsel_double_all`/`Qsel_ge_index`/`Qsel_tendsto_atTop` 三段（纯整数递推，
   经核实不依赖公理）前移到 δ 理论之前。
3. 在 `EulerConvergents.lean` 内新增 `Qsel_rec1`、`deltaSel_rec`、`cross_identity`、
   `namespace Hermite`（I/E 定义、初值、双递推、E_eq_I、I_pos、sign_alternation）、
   `sign_eq_abs`、`abs_sum_eq_two`、`abs_deltaSel_le_two_div`，
   并以 `theorem abs_deltaSel_lt` / `theorem deltaSel_tendsto_zero` 取代原 axiom。
   证明自包含（只用本文件的 sel_determinant/selPair_rec/Qsel_pos + Padé 模块）。

**数学论证文档**：outputs/δ符号交替定理的严格数学证明.md
（人类可读的完整分析证明：分部积分合法性、边界零点重数、(1−2t)²=1−4t(1−t) 的关键代数、
正性的 η-邻域论证、递推匹配归纳、符号⇒正项和⇒上界；含"哪些是数学、哪些是机械"对照表）。

**诚实边界**：e+π 无理性仍开放（OBL-4），本成果不涉及 π 的丢番图性质。
剩余 3 条经典公理是 MAY-ASSUME 白名单内的公认定理，非本项目缺口。

## M24 OBL-5 数学内容完成：δ 两条公理已证为定理（2026-11-18，DeltaSign.lean）

**决定性成果（机器验证，仅基础公理，零 sorryAx）**：

```
'DeltaSign.E_eq_I'                        [propext, Classical.choice, Quot.sound]
'DeltaSign.I_pos'                         [propext, Classical.choice, Quot.sound]
'DeltaSign.deltaSignAlternation_proved'   [propext, Classical.choice, Quot.sound]
'DeltaSign.deltaSel_tendsto_zero_proved'  [propext, Classical.choice, Quot.sound]
'DeltaSign.abs_deltaSel_lt_proved'        [propext, Classical.choice, Quot.sound]
```
lake build 9065 jobs 零错误；Audit.lean 退出码 0，全项目 sorryAx 计数 = 0。

**证明路线（绕开了原计划的端点组合恒等式，更干净）**：
不再直接计算 R_n(0)/R_n(1)（那需要 Σ C(n,j)(n+j)! = n!P_n 这类研究级组合恒等式），
改为证 E_n := (−1)^n n! δ_n 与 I_n := ∫₀¹ e^t t^n(1−t)^n dt **满足同一递推与同一初值**：
1. `padéP_first_deriv`、`padéP_second_deriv`：p_n'' = n(n−1)p_{n−2} − 2n(2n−1)p_{n−1}
   （PadeDeriv.lean；逐点求值 Polynomial.funext 降到 ℝ 后 ring 闭合）。
2. `padéP_eval_zero/one`、`padéP_deriv_eval_zero/one`：四个边界值皆零（PadeBoundary.lean）。
3. `ibp_zero`、`padeI_eq_second`、`padeI_recurrence`：两次分部积分（边界项零）
   ⇒ I_n = n(n−1)I_{n−2} − 2n(2n−1)I_{n−1}（PadeRecurrence.lean）。
4. `E_recurrence`：由 deltaSel_rec 纯代数推出 E 满足同递推（阶乘+符号关系）。
5. `E_zero/I_zero`（=e−1）、`E_one/I_one`（=3−e）：初值一致。
6. `E_eq_I`：强归纳 ⇒ E_n = I_n 对一切 n。
7. `I_pos`：被积函数在 (0,1) 恒正（e^t>0, t^n>0, (1−t)^n>0），
   integral_pos_iff_support_of_nonneg_ae' + support ⊇ Ioo 0 1 测度 1 ⇒ I_n > 0。
8. ⇒ (−1)^n δ_n > 0，即 deltaSignAlternation（M22 隔离的单一解析义务）。
9. ⇒ 由 M22 归约定理，两条原公理 deltaSel_tendsto_zero、abs_deltaSel_lt **均为定理**。

数值核验（mpmath 50 位）：E_n = I_n 对 n=0..6 全部成立；两条递推 n=2..6 全部 MATCH。

**剩余的纯工程步骤（不含数学内容）**：
EulerConvergents.lean 中两行 `axiom` 声明尚未物理删除，下游模块仍引用旧公理名。
原因：DeltaSign 经 DimHCore→SpectralGap 传递依赖 EulerConvergents，
若后者反向引用 DeltaSign 会形成循环 import。
消除方式：把 deltaSel 定义与两条新定理抽到独立的底层模块（如 EpiFormal/DeltaBase.lean，
只依赖 Qsel/Psel 的整数递推部分），EulerConvergents 改为 import 它并用 theorem 别名替换 axiom，
下游即可无条件化。此为文件依赖重构，非数学缺口。

**诚实边界**：δ 两条公理的**数学内容已完全机器验证**（这是实质突破，OBL-5 的数学部分完成）；
但项目里的 axiom 声明尚未物理移除，故 C6–C9/S2/S3/S5 的 #print axioms 目前仍列出旧公理名。
不得声称"下游已无条件化"直到重构完成。e+π 无理性仍开放（OBL-4），本成果不涉及该问题。

## M23 OBL-5 第二步：Padé 原函数 ODE 与积分表示（2026-11-18，PadeODE + PadeIntegral）

**成果（机器验证，仅基础公理，零 sorryAx）**：
- `padéP n = X^n(1−X)^n`；`padéR n = Σ_{k≤2n}(−1)^k D^k(padéP n)`（Hermite 原函数）。
- `padéR_ode : padéR n + derivative(padéR n) = padéP n`（反望远镜和，sum_telescope）。
- `natDegree_padéP ≤ 2n`，`iter_deriv_padéP : D^{2n+1}(padéP n)=0`。
- `PadeIntegral.pade_integral_repr : ∫₀¹ e^t·p_n(t) dt = e·R_n(1) − R_n(0)`
  （F(t)=e^t R_n(t)，F'=e^t p_n 用 ODE，FTC integral_eq_sub_of_hasDerivAt + 连续可积）。

审计：lake build 9055 jobs 零错误，Audit.lean 退出码 0，全部 [propext, Classical.choice, Quot.sound]。

**数值核验（mpmath 50 位）**：δ_n = (−1)^n/n!·∫₀¹ t^n(1−t)^n e^t dt 对 n=1..4 全 MATCH；
端点 R_n(0)=(−1)^n n! P_n、R_n(1)=(−1)^n n! Q_n 对 n=1..4 全 MATCH。

**剩余义务（精确隔离，OPEN）**：端点组合恒等式
- `padéR_eval_zero_sum : R_n(0) = Σ_{j≤n} C(n,j)(n+j)!`，需证 = (−1)^n n! P_n。
- `padéR_eval_one_sum : R_n(1) = (−1)^n Σ_{j≤n} C(n,j)(−1)^j(n+j)!`，需证 = (−1)^n n! Q_n。
- 子引理：iter_deriv_padéP_eval_zero（p_n^{(k)}(0)=C(n,k−n)(−1)^{k−n}k!，n≤k≤2n）、
  padéP_symm（p_n(1−t)=p_n(t)）、iter_deriv_padéP_eval_one（对称性给 (−1)^k 因子）。
这些是研究级组合恒等式（需 Psel/Qsel 递推 selPair_rec 归纳），尚未形式化。
一旦端点闭合，积分表示给 δ_n=(−1)^n/n!·(正积分)，被积函数 t^n(1−t)^n e^t 在 (0,1) 恒正
⇒ δ 符号交替 ⇒（由 M22 归约）两条 δ 公理消除 ⇒ C6–C9/S2/S3/S5 全链无条件机器验证。

**诚实边界**：ODE 与积分表示是真实机器验证进展，但 δ 公理本身尚未消除（端点组合恒等式 OPEN）。
不声称 OBL-5 完成。e+π 无理性仍开放。

## M22 OBL-5 第一步：δ 两公理的代数归约（2026-11-18，DeltaReduction.lean）

**成果（机器验证，仅基础公理）**：两条 δ 公理可由单一解析命题纯代数推出。
- `deltaSel_rec`：δ_{j+1} = (4j+2)δ_j + δ_{j-1}（无条件）。
- `cross_identity`：Q_j·δ_{j+1} − Q_{j+1}·δ_j = 2(−1)^{j+1}（无条件，行列式）。
- `deltaSignAlternation`（**OPEN 义务，Prop 定义，非公理非定理**）：∀j≥1, 0 < (−1)^j·δ_j。
- `abs_sum_eq_two`：符号交替 ⇒ Q_j|δ_{j+1}| + Q_{j+1}|δ_j| = 2（关键恒等式）。
- `abs_deltaSel_lt_of_sign`：符号交替 ⇒ 公理2（|δ_j| ≤ 2/Q_{j+1} < 1/(2jQ_j)，用 Q_{j+1}>4jQ_j）。
- `deltaSel_tendsto_zero_of_sign`：符号交替 ⇒ 公理1（双侧夹逼 2/Q_{j+1}→0）。

审计：lake build 9059 jobs 零错误，Audit.lean 退出码 0，五条引理均
[propext, Classical.choice, Quot.sound]，零 sorryAx。

**非循环性核验（第4类攻击）**：符号交替只断言符号，不含定量上界；量级信息来自
cross_identity（纯代数、独立已证）+ Q 增长（纯代数）。故归约非目标改头换面。
小情形核验：j=1 时 |δ_2|+7|δ_1| = (7e−19)+7(3−e) = 21−19 = 2 ✓（精确整数）。

**诚实边界**：EulerConvergents.lean 的两条 axiom 仍在，下游仍引用它们；本模块
证明的是归约定理，不是公理消除。OBL-5 剩余内容 = deltaSignAlternation 一条。

**已识别路线（计划，未形式化）**：Psel/Qsel = 3/1, 19/7, 193/71 恰为 e^x 的
对角 Padé 逼近 [n/n] 在 x=1 的值。经典积分表示
q_n(1)·e − p_n(1) = (−1)^n ∫₀¹ t^n(1−t)^n e^t dt / n!（正被积函数）
直接给符号交替与量级。需形式化 Padé 积分恒等式（分部积分 n 次或 Hermite 恒等式），
mathlib 有 intervalIntegral 基础设施。此为下一步候选。

## M21 T-finite 闭合（2026-11-18，DimHFinite.lean，OBL-1 完成）

**定理（机器验证，仅基础公理）**：
`DimHFinite.dimH_levelSet_finite (c : ℝ) : dimH (levelSet (ENNReal.ofReal c)) = 0`
即对一切实数 c，{x : Λ(x) ≤ c} 的 Hausdorff 维数为 0。Λ(x) = limsup_j j·‖Qsel_j·x‖。

**公理审计（lake env lean Audit.lean，AUDIT_EXIT=0，逐字）**：
```
'DimHFinite.dimH_levelSet_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
```
零 sorryAx；**不依赖 deltaSel 两公理、不依赖分类定理**（比原计划更强：
原 c<1/4 分支经由 SpectralGap.dimH_levelSet_below 会继承 δ 公理，
现改为单调归约 c'=max c 0 + 纯覆盖论证，对一切 c 统一处理）。

**四个 GAP 的闭合方式**：
- GAP-1（路径编码）：弃用 ℕ→ℕ 常函数 goodPath（设计缺陷，zero 分支必假），
  改存活中心 Finset 递归 survSet：S_0=range(Q_J.toNat+1)，
  S_{n+1}=⋃_{k∈S_n} branchSet(k)；基数界 card_survSet_le 由
  Finset.card_biUnion_le_card_mul + DimHCore.fiber_card_le 归纳，
  覆盖性 centerOf_mem_survSet 由三角不等式 centerOf_branchCond 归纳。
- GAP-2（[0,1] 限定）：tailSet 定义含 0≤x≤1；一般 x 经 x=⌊x⌋+y 分解，
  apprSeq_add_intCast（周期性，round_add_intCast）把条件搬到 y∈[0,1]，
  整数平移 LipschitzWith 1 保维数，dimH_iUnion 可数并保持 0。
- GAP-3（Hausdorff 对接）：MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum
  逐条件核验（Fintype ι、r→0、ediam≤r、覆盖），∑ediam^s 经实数域内容界
  hcontent + ENNReal.ofReal 单调性搬入，liminf=0 由 limsup_le_limsup + Tendsto.limsup_eq。
  dimH=0 收尾用 dimH_eq_iInf + ENNReal.lt_iff_exists_nnreal_btwn 反证。
- GAP-4（增长估计）：不用渐近记号；B^n/(n!)^s→0 由
  FloorSemiring.tendsto_pow_div_factorial_atTop（c=B^(1/s)）+ rpow 连续性 +
  显式恒等式 (B^(1/s))^n = B^(n/s)（Real.rpow_mul）；
  rad t j ≤ t/(j·j!) 由已验证 Qsel_ge_factorial。

**过程中发现并修正的真实错误（敌意审查记录）**：
1. 假设错配：centerOf_mem_interv 初版假设 ‖Q_j x‖≤rad t j（比水平集条件强 Q_j 倍），
   接不上 {Λ≤c}；改为 j·‖Q_j x‖≤t 后除以 j·Q_j 得 |x−k/Q_j|≤rad，链条闭合。
2. 假命题分支：tailSet t 0 = ∅ 是假的（j=0 时 apprSeq=0≤t 恒成立）；
   改为并集限制 J≥1（levelSet_subset_iUnion_tailSet 产出的 J=max 1 J0 恒≥1）。
3. 助理曾误判"rad 与 apprSeq 差 Q_j 倍、T-finite 是假命题"——算错（漏乘 Q_j），
   已撤回；x∈interv ⇔ j·‖Q_j x‖≤t 正是 apprSeq≤t。

**第 5 类攻击（证明过多）检验**：套**去权重**情形（weight=1，即 {‖Q_j x‖→0}）：
分支宽 2(t/Q_j+t/Q_{j+1})·Q_{j+1} ≈ 2t·Q_{j+1}/Q_j ≈ 8tj → ∞，B_j 不一致有界，
|S_n| ~ ∏j ~ n!，content ~ n!·(2t/Q_n)^s ≈ (2t)^s·(n!)^{1-s} → ∞（s<1），骨架失效。
失效点正是权重 j 把分支宽压成 2t·Q_{j+1}/(j·Q_j) ≈ 8t（一致有界）。
这与 Eggleston/BLR 无权重零集维数 1 一致，骨架未推出假命题。通过。
（注：曾误用 q_n=n 检验，算错 B_n——对 q_n=n 有 B_n≈4t/n→1 而非 2，
且 {limsup n‖nx‖<∞} 不是坏逼近集 {liminf n‖nx‖>0}；已撤回，改用去权重检验。）

**诚实定位**：这是经典覆盖论证（Eggleston/Bugeaud–Liao–Rams 型）在
e 收敛子分母子列 + 权重 j 这一具体实例上的机器验证；形式化≠新数学定理，
但 T-finite 从 AUDIT-GAP（assembly pending）升级为 AUDIT-PASS（内核零 sorryAx）。
e+π 无理性仍开放（OBL-4），δ 两公理仍在（OBL-5，但 T-finite 已不依赖它们）。

**第三阶段对抗审查另发现并修正的论文叙事错误（第 6 类·错误解释）**：
phase2_paper.tex 原称"无权重零集 {‖Q_j x‖→0} 维数 1（Eggleston），权重 j 把维数从 1 压到 0"。
**这与本项目机器验证的 theorem2_classification 直接矛盾**：该定理给 {j‖Q_j x‖→0}=L（可数），
而 j≥1 时 ‖Q_j x‖≤j‖Q_j x‖，故无权重零集 ⊆ L，可数、维数 0，不是 1。
Eggleston/BLR Cor.8 的维数 1 结论针对**一般无理数的全体收敛子分母**，不适用于本稀疏超指数子列。
已修正论文摘要、引言、相变备注、猜想四处：权重的作用不是"降零集维数"，而是使分支数一致有界
（B=⌊16t⌋+1），从而覆盖论证对**一切有限水平集**给维数 0；相变猜想改述为有限水平集层面
（α<1 维数 1 开放，α≥1 维数 0 由 T-finite+单调性），零集对一切 α≥0 恒可数。
PDF 已重编译（5 页，无 undefined reference）。此错误不影响 T-finite 定理本身（内核验证独立于叙事），
但说明"机器验证定理"与"论文解释性文字"须分别审查——内核不检查叙事是否与定理一致。