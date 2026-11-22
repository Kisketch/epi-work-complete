# 引理与调用条件审计（e+π 形式化）

日期：2026-11-14（复核更新）。方法：lake build 内核检查 + `#print axioms`（Audit.lean）。
白名单公理：e_transcendental, pi_transcendental, mu_e_eq_two
+ Lean 基础公理 propext, Classical.choice, Quot.sound。
（meiburg_criterion 已由 F2 证明为定理，不再是公理。全项目零 sorry。）

## 已证引理/定理（无 sorry，公理审计通过）
| 名称 | 文件 | 依赖 | 调用条件核查 |
|---|---|---|---|
| vieta_identity | Elementary | 基础公理 | 纯环恒等式，ring |
| quadratic_roots_algebraic | Elementary | 基础公理 | S,P 代数 + x²−Sx+P=0；实根⇒D=(S−2x)²≥0 已证 |
| at_least_one_transcendental | Elementary | e_transcendental | 反设两者代数⇒e 代数，矛盾 |
| pair_sum_diff…pair_prod_quot | Elementary | 基础公理 | 六组各自独立，条件（正性/e≠π/π≠0）已逐项供给 |
| four_numbers_at_most_one_rational | Elementary | e_transcendental, pi_transcendental | 调用六引理；e≠π 由 exp_one_lt_three<pi_gt_three |
| mu0_identity | Measure | 基础公理 | 1<D,0<ρ<1 保证 log 定义域与非零 |
| summable_tail_const | Series | 基础公理 | ∑1/k! 可和(Real.summable_pow_div_factorial 1)·常数倍·余有限同余 |
| tail_summable | Series | 基础公理 | summable_tail_const 特例 |
| tail_recurrence | Series | 基础公理 | (n+1)·n!=(n+1)!；拆 k=n+1 项=1；tsum_add 需两可和（已供） |
| apprSet_downward | Measure | 基础公理 | q'≥1 ⇒ rpow 单调（Real.rpow_le_rpow_of_exponent_le） |
| irrMeasure_neg | Measure | 基础公理 | 双射 (p,q)↦(−p,q)，infinite_image_iff 单射已证 |
| irrMeasure_add_rat | Measure | 基础公理 | 双射 (p,q')↦(p+q·q',q')；分母非零由 0<q' |
| irrMeasure_mul_rat | Measure | 基础公理 | 整数缩放+符号(natAbs)；常数吸收 |
| irrMeasure_inv | Measure | 基础公理 | 互换双射 (p,q)↦(q·sign p,|p|)；sign_coherent+abs_inv_sub_eq+常数吸收 |
| const_absorption(_nn) | Measure | 基础公理 | 分母无界限制 Q>T 吸收 C·Q^(−ν) |
| apprPairs_denom_unbounded | Measure | 基础公理 | 固定 q ⟹ p∈有限 Icc（floor/ceil 单调） |
| apprPairs_num_unbounded | Measure | 基础公理 | 固定 p ⟹ q 有界（ν>0, y 无理≠0） |
| theoremA_sum | Measure | mu_e_eq_two | π=(−e)+q；add_rat+neg |
| theoremA_diff | Measure | mu_e_eq_two | π=e+(−q)；add_rat |
| theoremA_quot | Measure | mu_e_eq_two | π=e/q；mul_rat |
| theoremA_prod | Measure | e_transcendental, mu_e_eq_two | π=q/e；mul_rat+inv |
| flint_hills_term_tendsto_zero | FlintHills | 基础公理 | Summable.tendsto_atTop_zero |
| flint_hills_diverges_bound | FlintHills | pi_transcendental | Meiburg 判据逆否（meiburg_criterion 已是定理） |
| proposition_H' | FlintHills | mu_e_eq_two, pi_transcendental | theoremA_sum 给 μ(π)=2<5/2，避开 Meiburg 边界 |
| meiburg_criterion | FlintHills（定理） | pi_transcendental | F2：exact flint_hills_converges_of_mu_lt |
| flint_hills_converges_of_mu_lt | MeiburgConvergence | pi_transcendental | 圆周间距+二进块计数+Jordan+几何求和，20 声明无 sorry |
| circle_spacing / dyadic_block_count / block_sum_bound | MeiburgConvergence | pi_transcendental | F2 计数与求和层核心引理 |
| sin_nat_ne_zero | Alekseyev | pi_transcendental | sin n=0 ⇒ n=mπ ⇒ π 有理，矛盾 |
| sin_eventual_lower | Alekseyev | pi_transcendental | 项→0 ⇒ 最终 aₙ<1 ⇒ \|sin n\|≥n^(−3/2−ε) |
| abs_sub_mul_pi_factor | Alekseyev | 基础公理 | \|n−mπ\|=\|m\|·\|π−n/m\|（m≠0），纯代数 |
| nearest_int_le_four_mul | Alekseyev | 基础公理 | p=round(qπ)≤4q：p≤qπ+1/2<4q+1，整数性（π<4） |
| nearest_int_tendsto_atTop | Alekseyev | 基础公理 | p>qπ−1/2→∞（tendsto_atTop_atTop 显式 N） |
| term_tendsto_eventually_gt | Alekseyev | pi_transcendental | 项→0 ⇒ 最终 n³sin²n>B（任意 B>0；sin_nat_ne_zero 保分母正） |
| alekseyev_eventual_lower | Alekseyev | pi_transcendental | 核心一致下界：取 B=64=(4^(3/2))²，p=round(qπ)，q^(5/2)\|π−a/q\|≥4^(−3/2)p^(3/2)\|sin p\|>1，对所有 a∈ℤ 一致 |
| apprPairs_finite_of_flintHills | Alekseyev | pi_transcendental | ν>5/2：一致下界（ε=ν−5/2）+ 分母无界 ⇒ 好逼近对集有限 |
| alekseyev_bound | Alekseyev | pi_transcendental | **T3 主定理**：收敛⇒μ(π)≤5/2；apprSet⊆[0,5/2]⇒sSup≤5/2 |

## 调用链复核
- proposition_H' → theoremA_sum（已证）→ irrMeasure_add_rat/neg（已证）+ mu_e_eq_two（公理）；
  → meiburg_criterion（**定理**，F2）→ flint_hills_converges_of_mu_lt（已证）。
- four_numbers_at_most_one_rational → 六配对 → quadratic_roots_algebraic（已证）。
- 无循环依赖；无清单外公理；全项目零 sorry。

## T3 已闭合（2026-11-14，最近整数论证机器验证）
原 alekseyev_diophantine / alekseyev_bound 两处 sorry 陈述方向错误，已弃用删除（历史）。
**本轮新增 alekseyev_bound（收敛⇒μ(π)≤5/2）已完整机器验证，无 sorryAx**，
仅依赖 pi_transcendental + 基础公理。路线：修订包更正 1 的最近整数论证——
p=round(qπ) 自动满足 p≍q（p≤4q），只对 p 用 sin 下界，q^(3/2) 换 p^(3/2)
仅损失常数 4^(−3/2)，无需密度论证。
历史障碍（保留备查）：逐项 sin 下界给 |π−n/m|≥n^(−3/2−ε)/|m|，需 n≤C'|m|
但下界对所有大 n 成立（含 n>π|m|，方向反转）——该朴素路线不成立，已被绕开。
注：irrMeasure_mul_rat/inv、theoremA_prod/quot、flint_hills_diverges_bound 均已证（无 sorryAx）。
登记声明总数（M5 止）：25 + 6 = 31，全部无 sorryAx（lake build 9056 jobs 零错误）。

## M6 新增声明审计（2026-11-14 完整联合编译，A–H 八模块）

白名单扩充：+ deltaSel_tendsto_zero, abs_deltaSel_lt（A 组两条经典 e 连分数误差公理）。
全项目 lake build **9064 jobs 零错误**；Audit.lean 全文 **sorryAx 计数 = 0**。

| 名称 | 文件 | 依赖 | 调用条件核查 |
|---|---|---|---|
| Qsel_pos/Psel_rec/Qsel_rec/sel_determinant/Psel_odd/Qsel_odd/Qsel_strictMono/Qsel_double/Qsel_succ_coprime | EulerConvergents(A) | 基础公理 | 选定收敛子整数地基；行列式±2，互素走 Q 递推归纳 gcd(1,7)=1；下标0占位1 |
| Psel_div_Qsel_tendsto_exp | EulerConvergents(A) | deltaSel_tendsto_zero | δ→0 与 Q→∞ ⇒ P/Q→e |
| Qsel_tendsto_atTop | EulerConvergents(A) | 基础公理 | Q≥j 线性下界 + natCast→∞ |
| theorem2_classification | Classification(B) | abs_deltaSel_lt, deltaSel_tendsto_zero | j‖Q_j x‖→0 ⇔ x∈L=ℤ+ℤ(e+1)/2；Cramér ±2 构造整数 a,b |
| corollary3_gap | Classification(B) | deltaSel_tendsto_zero | x∉L ⇒ limsup j‖Q_j x‖≥1/4；g(j)→4 极限保号 |
| propagate / sel_determinant | Classification(B) | 基础公理 | 纯整数代数 |
| theorem6_a / theorem6_b / lemma5_four_S_integer | Spectrum(C) | 基础公理 | 有限谱 {k/4}；**无 deltaSel 依赖**；C 无公理 |
| theorem7_cluster_set / theorem7_finite / theorem7_nonempty | SignedClusters(D) | 基础公理 | S(x)有限⇒聚类集={k/4:k 无穷多次取到}；不依赖 deltaSel |
| theorem8_realization | SignedClusters(D) | 基础公理 | 任意有界整数序列可实现；存在性构造，不判定 Bπ 缺陷 |
| theorem9_tail_iff / corollary10_injective / corollary10_ker | DefectFibres(E) | deltaSel_tendsto_zero | x,y∈F：缺陷尾相同⇔x−y∈L；只证单射 |
| finer_scale_ratio | DefectFibres(E) | deltaSel_tendsto_zero, e_transcendental | ε_j(x+re)/δ−ε_j(x)/δ=r |
| control_example | DefectFibres(E) | abs_deltaSel_lt, deltaSel_tendsto_zero, e_transcendental | x=6±e 缺陷尾恒0、符号比±1 |
| deltaSel_ne_zero | DefectFibres(E) | e_transcendental | δ_j≠0（e 无理） |
| theorem11_three_equiv / pair_iff / limit_integer / quantitative_bound(_succ) | AdjacentWitness(F) | deltaSel_tendsto_zero（部分仅基础） | S7 双指标三等价；「对每个 B 匹配集有限」仍开放 |
| factorial_criterion / tFrac_bounds / recurrence_u | FactorialCriterion(G) | 基础公理 | Prop4 阶乘判据；**无任何公理**；右侧极限开放 |
| proposition3_signed_criterion / forward / converse | SignedCriterion(H) | deltaSel_tendsto_zero（converse 仅基础） | Prop3 双向符号判据；符号估计仍开放 |

**M6 后登记声明总数：31 + 179（A13+B20+C30+D16+E30+F32+G21+H17）= 210，全部无 sorryAx。**
公理唯一来源：A 的两条 deltaSel + 既有白名单（e_transcendental/pi_transcendental/mu_e_eq_two）；C/G 无公理；无新增公理。

## M8 新增声明审计（2026-11-14 代数无关条件归约，AlgebraicIndependence.lean）

**无新增公理**。四公开定理均仅依赖基础公理 [propext, Classical.choice, Quot.sound]，
**无 sorryAx，且不依赖 e_transcendental/pi_transcendental**（代数无关假设更强）。
全项目 lake build **9066 jobs 零错误**。

| 名称 | 文件 | 依赖 | 调用条件核查 |
|---|---|---|---|
| transcendental_add_of_algebraicIndependent | AlgebraicIndependence | 基础公理 | 前提 AlgebraicIndependent ℚ ![e,π]；代入 X₀+X₁，左逆 (X,0) 证单射 |
| transcendental_sub_of_algebraicIndependent | AlgebraicIndependence | 基础公理 | 同上；代入 X₀−X₁，左逆 (X,0) |
| transcendental_mul_of_algebraicIndependent | AlgebraicIndependence | 基础公理 | 同上；代入 X₀·X₁，左逆 (X,1) |
| transcendental_div_of_algebraicIndependent | AlgebraicIndependence | 基础公理 | 同上；齐次化 homogenize m n，πⁿ·m(e/π)=0，homogenize_eq_zero_iff |
| aeval_aeval_comp（私有） | AlgebraicIndependence | 基础公理 | 求值复合，Polynomial.algHom_ext |
| aeval_X0_add/sub/mul_X1_injective（私有） | AlgebraicIndependence | 基础公理 | 代入映射单射，左逆归约单变量恒等 |
| transcendental_aeval_of_injective（私有） | AlgebraicIndependence | 基础公理 | 统一引理：单射代入 + 代数无关 ⇒ 取值超越 |

**M8 后公开登记定理：210 + 4 = 214，全部无 sorryAx。**（私有引理 7 条不计入公开注册数。）
**诚实边界**：四定理均为条件性，前提 e、π 代数无关未证；不证明 e+π 无理性。

## M9 新增声明审计（2026-11-14 E Cor10 满射接线，DefectFibres.lean）

**无新增公理**。满射定理仅依赖基础公理，**无 sorryAx，且不依赖 deltaSel**
（比单射部分更干净；单射 corollary10_injective 依赖 deltaSel_tendsto_zero）。
全项目 lake build **9066 jobs 零错误**。

| 名称 | 文件 | 依赖 | 调用条件核查 |
|---|---|---|---|
| corollary10_surjective | DefectFibres(E) | 基础公理 | 调用 D theorem8_realization 的 xOfSeq；inF 用 residual_bound_d+eventually_nearest_d；sameTail 用 defect_eq_d+defect_bridge |
| defect_bridge | DefectFibres(E) | 基础公理 | SignedClusters.defect = DefectFibres.defect（Mseq=Msel=round 同源） |

**M9 后公开登记定理：214 + 1 = 215**（corollary10_surjective；defect_bridge 为桥接引理）。
**诚实边界**：Cor10 双射是结构定理，不判定 e+π 无理性；D theorem8 存在性构造不判定 x=Bπ 缺陷。
缺口 5（E Cor10 满射）已闭合。

## M16 新增声明审计（2026-11-15 Dj 归约链，EscapeReduction.lean）

**无新增公理**。归约链 7 个公开声明全部内核验证，**无 sorryAx**。
依赖：前 5 个仅 Lean 基础公理（propext, Classical.choice, Quot.sound）；
后 2 个（reduction_to_lattice, P1_imp_irrational）另依赖 `deltaSel_tendsto_zero`
（经 Classification.corollary3_gap，白名单内经典 δ 公理）。
全项目 lake build **9069 jobs 零错误**；Audit.lean EXIT 0，sorryAx=0。

| 名称 | 文件 | 依赖 | 调用条件核查 |
|---|---|---|---|
| eps_cl_eq_neg_eps_esc | EscapeReduction | 基础公理 | Classification.eps(Bπ)=-Escape.eps B（符号相反，绝对值相等）；nearestInt=Msel=round 同源 |
| dist_eq_abs_eps_esc | EscapeReduction | 基础公理 | distToNearestInt(Qsel j·Bπ)=\|Escape.eps B j\| |
| match_eps_bound（D2-1） | EscapeReduction | 基础公理 | D_j=0 ⇒ \|ε_j\|≤(Q_j/2+2B)/Q_{j+1}；恒等式+\|ε\|≤1/2+\|C_j\|=2 |
| Qsel_pred_div_tendsto_zero | EscapeReduction | 基础公理 | Q_{j-1}/Q_j≤1/(4j-2)→0，夹逼 |
| jQsel_div_Qsel_succ_tendsto | EscapeReduction | 基础公理 | jQ_j/Q_{j+1}=1/(4+2/j+Q_{j-1}/(jQ_j))→1/4 |
| j_div_Qsel_succ_tendsto_zero | EscapeReduction | 基础公理 | j/Q_{j+1}≤1/(4j+2)→0 |
| sharp_bound_tendsto（D2-3） | EscapeReduction | 基础公理 | j(Q_j/2+2B)/Q_{j+1}→1/8 |
| sharp_bound_eventually | EscapeReduction | 基础公理 | 最终≤1/5（1/8<1/5） |
| match_eventually_eps_le_fifth（D2-4） | EscapeReduction | 基础公理 | D_j=0 eventually ⇒ j‖BQ_jπ‖≤1/5 eventually |
| reduction_to_lattice（D2-6） | EscapeReduction | deltaSel_tendsto_zero | 与 corollary3_gap(c=1/5<1/4) 对撞 ⇒ Bπ∈L |
| P1_imp_irrational（D2-6 等价） | EscapeReduction | deltaSel_tendsto_zero | P1 ⇒ e+π 无理（条件定理，前提 P1 开放） |

**M16 后公开登记定理：232 + 7 = 239**（EscapeReduction 7 个公开定理；衔接引理与私有辅助不计）。
**诚实边界（D1-5 边界测试）**：归约链每一步对 π'=A/B-e 同样成立（通用递推+取整），
故归约本身不产生矛盾；矛盾只能来自 P1（Bπ∉L），而 P1 对 π' 失败。
**P1 与原问题同族难度**（D2-9）：Bπ∈L ⇔ 2Bπ-ne∈ℤ，n≠0 情形是 {1,e,π} 整线性关系，
原问题 e+π∈ℚ 是其子族 n=-2B；无已知定理排除一般整线性关系。
归约是「换靶」不是「降难」，不证明 e+π 无理性。
**数值基线**（compute_dj.py，mpmath 动态精度 digits(Q_j)+500）：B≤20,j≤80 共 1600 对，
真 π 无匹配 0 次，恒等式相对误差<1e-100，反例侧 π'=6-e/π'=11/2-e 最终匹配，符号比例 0.42-0.48 无偏倚。
