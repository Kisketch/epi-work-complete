import EpiFormal.NoShortDimRatio
import EpiFormal.NoShortDimCount
import EpiFormal.Cylinder
import EpiFormal.CylinderMediant
import EpiFormal.CylinderOrder
import EpiFormal.CylinderDiameter
import EpiFormal.CylinderFiber
import EpiFormal.CylinderPhaseE
import EpiFormal.WindowMuLevel
import EpiFormal.CylinderFrostman
import EpiFormal.WindowThickBound
import EpiFormal.WindowLevelCount
import EpiFormal.WindowLogFact
import EpiFormal.WindowMassDist
import EpiFormal.WindowCoverCount
import EpiFormal.WindowHinter
import EpiFormal.WindowOverlap
import EpiFormal.WindowMuImplication
import EpiFormal.WindowMuBound
import EpiFormal.WindowMuScale
import EpiFormal.WindowSplitMass
import EpiFormal.WindowMuThresh
import EpiFormal.WindowStoppedTree
import EpiFormal.WindowFrostmanDirect
import EpiFormal.WindowRealize
import EpiFormal.WindowConcreteThresh
import EpiFormal.WindowLargeWindow
import EpiFormal.WindowLargeThresh
import EpiFormal.WindowSandwich
import EpiFormal.WindowWordTree
import EpiFormal.WindowMassProd
import EpiFormal.WindowLogThresh
import EpiFormal.WindowMassFull
import EpiFormal.WindowDescFiber
import EpiFormal.WindowStoppedUniform
import EpiFormal.WindowTreePrune
import EpiFormal.WindowAsympThresh
import EpiFormal.WindowFrostmanDischarge
import EpiFormal.WindowPaperScale
import EpiFormal.WindowCFRealize
import EpiFormal.WindowCFBridge
import EpiFormal.WindowNoShortCFRealize
import EpiFormal.WindowPrescribedCFRealize
import EpiFormal.WindowBoundedUpper
import EpiFormal.GoldenHeadCutoff
import EpiFormal.GoldenAffineEndpoint
import EpiFormal.AffineWindowAudit
import EpiFormal.DigitTailBound
import EpiFormal.DensityCube
import EpiFormal.OrbitAndFlow
import EpiFormal.ResearchAdvance
import EpiFormal.TraceMarkov
import EpiFormal.WindowMainBound
import EpiFormal.WindowWindowBounds
import EpiFormal.WindowMobiusPartial
import EpiFormal.WindowMobiusCount
import EpiFormal.OpenAI_mu_pi_bridge
import EpiFormal.FiniteStatePositive
import EpiFormal.AlgebraicIndependence
import EpiFormal.WindowShortAe
import EpiFormal.DirichletDivisor
import EpiFormal.GoldenFiniteShift
import EpiFormal.AffineWindowAssembly
import EpiFormal.DenominatorCertificate
import EpiFormal.FiniteStateTail
import EpiFormal.PolyWeightedLower
import EpiFormal.PolyWeightedUpper
import EpiFormal.HermiteResiduePeriod
import EpiFormal.PolyGaugeAndPhaseTransition
import EpiFormal.GaugeLiminfComplete
import EpiFormal.FiniteStateGauge
import EpiFormal.Elementary
import EpiFormal.Measure
import EpiFormal.Series
import EpiFormal.FlintHills
import EpiFormal.MeiburgConvergence
import EpiFormal.Alekseyev
import EpiFormal.EulerConvergents
import EpiFormal.AdjacentWitness
import EpiFormal.SignedCriterion
import EpiFormal.Classification
import EpiFormal.Spectrum
import EpiFormal.SignedClusters
import EpiFormal.DefectFibres
import EpiFormal.FactorialCriterion
import EpiFormal.Escape
import EpiFormal.EscapeBoundary
import EpiFormal.EscapeReduction
import EpiFormal.SpectralGap
import EpiFormal.DimHCore
import EpiFormal.DimHFinite
import EpiFormal.DeltaReduction
import EpiFormal.PadeODE
import EpiFormal.PadeIntegral
import EpiFormal.PadeDeriv
import EpiFormal.PadeBoundary
import EpiFormal.PadeRecurrence
import EpiFormal.DeltaSign
import EpiFormal.ThresholdAttained
import EpiFormal.QuarterPointCore
import EpiFormal.QuarterPointTail
import EpiFormal.QuarterPointFinal
import EpiFormal.WeightedFiber
import EpiFormal.WeightedDimHCore
import EpiFormal.WeightedUpper
import EpiFormal.WeightedFinal
import EpiFormal.WeightedLower
import EpiFormal.WeightedCantor
import EpiFormal.WeightedExactDim
import EpiFormal.GoldenOrbitRigidity
import EpiFormal.FullSpectrumDiscrete
import EpiFormal.GoldenOrbitB2Rigidity
import EpiFormal.GaugeNull
import EpiFormal.UnweightedCorrection
import EpiFormal.GaugeExact
import EpiFormal.WindowAndResidueCore
import EpiFormal.GaugeCircle
import EpiFormal.GeneralEndpointRigidity
import EpiFormal.TrichotomyAndPolyExtension
import EpiFormal.WindowThickening
import EpiFormal.WindowPointMass
import EpiFormal.WindowShortAeRealize
import EpiFormal.ResidueModGeneral
import EpiFormal.TransferOperatorDim
import EpiFormal.FiniteStateComplete
import EpiFormal.ResidueAsymptotic
import EpiFormal.GeneralGrowingRec
import EpiFormal.GeneralGrowingDim
import EpiFormal.Axioms
import EpiFormal.Basic
import EpiFormal.Meiburg
import EpiFormal.WeightedPhase

-- 公理审计：仅允许 Axioms/Measure 清单公理 + Lean 基础公理。
-- meiburg_criterion 已由 F2 证明为定理（不再是公理）；全项目零 sorry。
#print axioms vieta_identity
#print axioms quadratic_roots_algebraic
#print axioms at_least_one_transcendental
#print axioms four_numbers_at_most_one_rational
#print axioms mu0_identity
#print axioms tail_summable
#print axioms tail_recurrence
#print axioms irrMeasure_neg
#print axioms irrMeasure_add_rat
#print axioms irrMeasure_mul_rat
#print axioms irrMeasure_inv
#print axioms theoremA_sum
#print axioms theoremA_diff
#print axioms theoremA_prod
#print axioms theoremA_quot
#print axioms proposition_H'
#print axioms meiburg_criterion
#print axioms flint_hills_diverges_bound
#print axioms flint_hills_converges_of_mu_lt
#print axioms circle_spacing
#print axioms dyadic_block_count
#print axioms block_sum_bound
#print axioms sin_nat_ne_zero
#print axioms sin_eventual_lower
#print axioms abs_sub_mul_pi_factor
-- T3 最近整数论证（2026-11-14 修订包更正 1 的形式化）
#print axioms nearest_int_le_four_mul
#print axioms nearest_int_tendsto_atTop
#print axioms term_tendsto_eventually_gt
#print axioms alekseyev_eventual_lower
#print axioms apprPairs_finite_of_flintHills
#print axioms alekseyev_bound
-- 部分联合编译（2026-11-14，A 地基 + F 双指标 + H 符号判据；用户授权）
-- A 地基（EulerConvergents）
#print axioms Qsel_pos
#print axioms Psel_rec
#print axioms Qsel_rec
#print axioms sel_determinant
#print axioms Psel_odd
#print axioms Qsel_odd
#print axioms Qsel_strictMono
#print axioms Qsel_double
#print axioms Qsel_succ_coprime
#print axioms Psel_div_Qsel_tendsto_exp
#print axioms Qsel_tendsto_atTop
-- F 双指标三等价（AdjacentWitness）
#print axioms AdjacentWitness.theorem11_three_equiv
#print axioms AdjacentWitness.pair_iff
#print axioms AdjacentWitness.limit_integer
#print axioms AdjacentWitness.quantitative_bound
#print axioms AdjacentWitness.quantitative_bound_succ
#print axioms AdjacentWitness.hpos_eventually_mismatch
-- H 符号判据（SignedCriterion）
#print axioms EpiFormalH.proposition3_signed_criterion
#print axioms EpiFormalH.proposition3_forward
#print axioms EpiFormalH.proposition3_converse
-- 完整联合编译（2026-11-14，B/C/D/E/G 归一并入；用户授权「全部进行完毕」）
-- B 分类格 + Cor3 间隙（Classification）
#print axioms Classification.theorem2_classification
#print axioms Classification.corollary3_gap
#print axioms Classification.propagate
#print axioms Classification.sel_determinant
-- C 有限谱（Spectrum，无公理）
#print axioms CSpectrum.theorem6_a
#print axioms CSpectrum.theorem6_b
#print axioms CSpectrum.lemma5_four_S_integer
#print axioms CSpectrum.Qsel_pos
-- D 符号聚类（SignedClusters，定理7/8不依赖deltaSel）
#print axioms SignedClusters.theorem7_cluster_set
#print axioms SignedClusters.theorem7_finite
#print axioms SignedClusters.theorem8_realization
-- E 缺陷尾 + 双射（DefectFibres，deltaSel_ne_zero用白名单e_transcendental）
#print axioms DefectFibres.theorem9_tail_iff
#print axioms DefectFibres.corollary10_injective
#print axioms DefectFibres.finer_scale_ratio
#print axioms DefectFibres.control_example
#print axioms DefectFibres.deltaSel_ne_zero
-- G 阶乘判据（FactorialCriterion，无公理）
#print axioms FactorialCriterion.factorial_criterion
#print axioms FactorialCriterion.tFrac_bounds
#print axioms FactorialCriterion.recurrence_u

#print axioms Escape.irrational_iff_inf_mismatch
#print axioms Escape.D_eq_eps
#print axioms EscapeBoundary.boundary_eventual_match
#print axioms Escape.inf_mismatch_iff_eventually
-- Dj 归约链（EscapeReduction，2026-11-15；D2-1~D2-6，仅 deltaSel_tendsto_zero + 基础公理）
#print axioms EscapeReduction.match_eps_bound
#print axioms EscapeReduction.Qsel_pred_div_tendsto_zero
#print axioms EscapeReduction.jQsel_div_Qsel_succ_tendsto
#print axioms EscapeReduction.sharp_bound_tendsto
#print axioms EscapeReduction.match_eventually_eps_le_fifth
#print axioms EscapeReduction.reduction_to_lattice
#print axioms EscapeReduction.P1_imp_irrational
-- 第二阶段：谱隙与水平集维数（SpectralGap，2026-11-15）
#print axioms SpectralGap.apprExponent_eq_zero_iff
#print axioms SpectralGap.spectral_gap
#print axioms SpectralGap.levelSet_below_eq_lattice
#print axioms SpectralGap.latticeL_countable
#print axioms SpectralGap.dimH_levelSet_below
-- 第二阶段维数零覆盖论证核心引理（DimHCore，2026-11-16，仅基础公理）
#print axioms DimHCore.Qsel_ge_factorial
#print axioms DimHCore.Qsel_succ_le
#print axioms DimHCore.fiber_card_le
-- 第二阶段 T-finite 组装（DimHFinite，2026-11-18）
-- 覆盖论证核心：仅基础公理
#print axioms DimHFinite.card_survSet_le
#print axioms DimHFinite.centerOf_mem_survSet
#print axioms DimHFinite.tailSet_cover
#print axioms DimHFinite.tendsto_contentBound
#print axioms DimHFinite.hausdorffMeasure_tailSet_zero
#print axioms DimHFinite.dimH_tailSet_zero
-- 周期性与最终定理：dimH_levelSet_finite 额外依赖两条 deltaSel 公理（OBL-5，经由 c<1/4 分支）
#print axioms DimHFinite.apprExponent_add_intCast
#print axioms DimHFinite.levelSet_subset_iUnion_tailSet
#print axioms DimHFinite.dimH_levelSet_finite
-- OBL-5 第一步：δ 两公理 → 单一符号交替命题的代数归约（DeltaReduction，2026-11-18，仅基础公理）
#print axioms DeltaReduction.deltaSel_rec
#print axioms DeltaReduction.cross_identity
#print axioms DeltaReduction.abs_sum_eq_two
#print axioms DeltaReduction.abs_deltaSel_lt_of_sign
#print axioms DeltaReduction.deltaSel_tendsto_zero_of_sign
-- OBL-5 第二步：Padé 原函数 ODE 与积分表示（PadeODE + PadeIntegral，2026-11-18，仅基础公理）
#print axioms padéR_ode
#print axioms PadeIntegral.pade_integral_repr
-- OBL-5 完成：δ 两条原公理已证为定理（DeltaSign，2026-11-18，仅基础公理）
#print axioms padéP_second_deriv
#print axioms padeI_recurrence
#print axioms DeltaSign.E_eq_I
#print axioms DeltaSign.I_pos
#print axioms DeltaSign.deltaSignAlternation_proved
#print axioms DeltaSign.deltaSel_tendsto_zero_proved
#print axioms DeltaSign.abs_deltaSel_lt_proved
-- OBL-2 解决：阈值 1/4 可达（显式构造点 x0，2026-11-18，仅基础公理）
#print axioms ThresholdAttained.apprSeq_tendsto_quarter
#print axioms QuarterPointFinal.eps_bound
#print axioms QuarterPointFinal.round_eq_M
#print axioms QuarterPointFinal.defect_eventually_one
#print axioms QuarterPointFinal.lambda_x0_eq_quarter
-- OBL-3a 关键零件：加权分支上界（j^{1−α} 标度，2026-11-18，仅基础公理）
#print axioms WeightedFiber.fiber_card_weighted_le
-- OBL-3a 完全闭合：加权相变上界 dimH{Λ_α≤c}≤1−α（2026-11-18，仅基础公理）
#print axioms WeightedDimH.card_wsurvSet_le
#print axioms WeightedUpper.dimH_wtailSet_le
#print axioms WeightedFinal.dimH_levelSetα_le
-- OBL-3b 关键零件：分支下界（Frostman 必需，2026-11-18，仅基础公理）
#print axioms WeightedLower.width_ge
#print axioms WeightedLower.fiber_card_weighted_ge_scale
-- OBL-3b 几何零件：同级区间分离（2026-11-18，仅基础公理）
#print axioms WeightedCantor.winterv_disjoint
-- 方向 1：黄金比轨道范数奇偶刚性与定理 B1 核心代数界（2026-11-20，仅基础公理）
#print axioms GoldenOrbitRigidity.mobius_error_identity
#print axioms GoldenOrbitRigidity.zphiNorm_even_iff
#print axioms GoldenOrbitRigidity.m0_even
#print axioms GoldenOrbitRigidity.norm_parity_rigidity_identity
#print axioms GoldenOrbitRigidity.spectral_gap_constants
#print axioms GoldenOrbitRigidity.norm_parity_rigidity_eq_iff
#print axioms GoldenOrbitRigidity.norm_parity_rigidity_ge_second
#print axioms GoldenOrbitRigidity.zphiNorm_not_two_three_four
#print axioms GoldenOrbitRigidity.height_dichotomy
#print axioms GoldenOrbitRigidity.case1_lower_bound
#print axioms GoldenOrbitRigidity.case2_sub1_quadratic_ge
#print axioms GoldenOrbitRigidity.case2_sub2_quadratic_ge
#print axioms GoldenOrbitRigidity.case2_sub3_quadratic_ge
#print axioms GoldenOrbitRigidity.second_limit_point_attained_value
#print axioms GoldenOrbitRigidity.b2_control_model_constant
-- OBL-3b 完全闭合：精确极限集与加权子水平集精确 Hausdorff 维数等式（2026-11-20，仅基础公理）
#print axioms WeightedExactDim.one_le_hausdorffMeasure_cantorSet
#print axioms WeightedExactDim.dimH_exactLimitSetα_ge
#print axioms WeightedExactDim.dimH_exactLimitSetα_eq
#print axioms WeightedExactDim.dimH_levelSetα_eq
#print axioms WeightedExactDim.dimH_apprExponentα_eq_zero
-- 深挖 1：论文二全谱完全离散化、正能级 k/4 精确三分法与一般 (cj+d) 递推（2026-11-20，仅基础公理）
#print axioms FullSpectrumDiscrete.general_signed_defect_approx
#print axioms FullSpectrumDiscrete.general_abs_defect_approx
#print axioms FullSpectrumDiscrete.not_tendsto_open_interval_of_int_approx
#print axioms FullSpectrumDiscrete.eventually_le_of_int_approx_in_gap
#print axioms FullSpectrumDiscrete.eventually_eq_int_of_tendsto
#print axioms FullSpectrumDiscrete.euler_signed_defect_approx
#print axioms FullSpectrumDiscrete.euler_abs_defect_approx
#print axioms FullSpectrumDiscrete.spectral_gap_open_interval
#print axioms FullSpectrumDiscrete.eventually_abs_defect_le_of_apprExponent_le
#print axioms FullSpectrumDiscrete.levelSet_eq_on_gap
#print axioms FullSpectrumDiscrete.unsigned_exact_limit_iff_defect_binary
#print axioms FullSpectrumDiscrete.signed_exact_limit_iff_defect_const
#print axioms FullSpectrumDiscrete.sub_mem_latticeL_of_same_signed_limit
#print axioms FullSpectrumDiscrete.signed_exact_limit_set_countable
#print axioms FullSpectrumDiscrete.dimH_signed_exact_limit_set_zero
-- 深挖 2：论文一有理端点 p/q 范数同余刚性与 B=2 对照模型精确值及第二极限点（2026-11-20，仅基础公理）
#print axioms GoldenOrbitB2Rigidity.xi1_mul_xi2Conj
#print axioms GoldenOrbitB2Rigidity.M_uv_norm_identity
#print axioms GoldenOrbitB2Rigidity.rational_endpoint_rigidity_identity
#print axioms GoldenOrbitB2Rigidity.zphiNorm_mod5_identity
#print axioms GoldenOrbitB2Rigidity.five_dvd_zphiNorm_iff
#print axioms GoldenOrbitB2Rigidity.m8q_mod4_identity
#print axioms GoldenOrbitB2Rigidity.alpha8q_mul_gammaConj
#print axioms GoldenOrbitB2Rigidity.m8q_norm_identity
#print axioms GoldenOrbitB2Rigidity.m8q_odd
#print axioms GoldenOrbitB2Rigidity.phi8q_odd_rigidity_identity
#print axioms GoldenOrbitB2Rigidity.pell_b2_spectral_gap
#print axioms GoldenOrbitB2Rigidity.phi85_eq_min_iff
#print axioms GoldenOrbitB2Rigidity.phi83_eq_min_iff
#print axioms GoldenOrbitB2Rigidity.phi85_ge_second
#print axioms GoldenOrbitB2Rigidity.phi83_ge_second
#print axioms GoldenOrbitB2Rigidity.phi85_second_attained
#print axioms GoldenOrbitB2Rigidity.phi83_second_attained
#print axioms GoldenOrbitB2Rigidity.b2_case1_85_lower_bound
#print axioms GoldenOrbitB2Rigidity.b2_case1_83_lower_bound
#print axioms GoldenOrbitB2Rigidity.b2_case2_sk_Q1_limit
#print axioms GoldenOrbitB2Rigidity.b2_case2_sub1_quadratic_ge
#print axioms GoldenOrbitB2Rigidity.b2_case2_sub3_quadratic_ge
-- 临界能级严格子水平集与次临界规范 Hausdorff 测度零定理（GaugeNull + UnweightedCorrection，2026-11-20，仅基础公理）
#print axioms GaugeNull.mkMetric_digitClass_null
#print axioms GaugeNull.mkMetric_strictLevel_null
#print axioms GaugeNull.mkMetric_levelSet_null_of_subgauge
#print axioms UnweightedCorrection.witness
-- §4 补集满测度/维数 1、§6 Theorem 13 σ-有限性 & L-不变性、Corollary 14(iii) 非 σ-有限性与 Theorem 16(ii) 二值规范（GaugeExact，2026-11-20，仅基础公理）
#print axioms GaugeExact.dimH_finiteLevel_zero
#print axioms GaugeExact.volume_finiteLevel_zero
#print axioms GaugeExact.ae_apprExponent_eq_top
#print axioms GaugeExact.volume_infiniteLevel_Icc
#print axioms GaugeExact.volume_infiniteLevel_Icc_zero_one
#print axioms GaugeExact.dimH_infiniteLevel_inter_Icc_zero_one
#print axioms GaugeExact.dimH_infiniteLevel_eq_one
#print axioms GaugeExact.apprExponent_add_latticeL
#print axioms GaugeExact.exactLevel_add_latticeL
#print axioms GaugeExact.mkMetric_digitClass_le
#print axioms GaugeExact.mkMetric_digitClass_lt_top
#print axioms GaugeExact.exactLevel_countable_cover_finite_mkMetric
#print axioms GaugeExact.mkMetric_le_mul_of_eventually_le
#print axioms GaugeExact.mkMetric_eq_zero_of_ratio_tendsto_zero_of_lt_top
#print axioms GaugeExact.not_countable_union_finite_of_ratio_tendsto_zero
#print axioms GaugeExact.gauge_ratio_adjacent_levels_tendsto_zero
#print axioms GaugeExact.mkMetric_unsignedExactLimit_null_of_hk
#print axioms GaugeExact.mkMetric_unsignedExactLimit_null_of_subgauge_base2
#print axioms GaugeExact.unsignedExactLimit_countable_cover_finite_mkMetric_base2
#print axioms GaugeExact.mkMetric_cantorTree_pos
#print axioms GaugeExact.mkMetric_exactLevel_pos
#print axioms GaugeExact.mkMetric_exactLevel_eq_top
-- §7 连分数窗口与模 4 部分商残差核心引理（WindowAndResidueCore，2026-11-20，仅基础公理）
#print axioms WindowAndResidueCore.thm18_terminal_denom_bounds
#print axioms WindowAndResidueCore.thm18_append_four_crosses
#print axioms WindowAndResidueCore.thm18_prescribed_count_crossing
#print axioms WindowAndResidueCore.thm19_cond_prob_integral_identity
#print axioms WindowAndResidueCore.thm19_cond_prob_lower_bound
#print axioms WindowAndResidueCore.thm19_exp_moment_step_le
#print axioms WindowAndResidueCore.thm20_rational_between_two_and_three
#print axioms WindowAndResidueCore.thm20_terminal_denom_bounds
#print axioms WindowAndResidueCore.thm21_shift_mod4_mem_alphabet
#print axioms WindowAndResidueCore.thm21_tail_distance_ratio_identity
#print axioms WindowAndResidueCore.thm21_tail_distance_ratio_le
#print axioms WindowAndResidueCore.thm21_prefix_factor_bounds
#print axioms WindowAndResidueCore.thm21_integer_certificate_power_enclosure
#print axioms WindowAndResidueCore.thm21_transfer_operator_sub_super_iteration
-- §6 临界规范显式构造（GaugeCircle）：R 与圆周 R/Z (UnitAddCircle) 原生测度、开弧无穷性与 Theorem 16(ii) 二值规范（2026-11-20，仅基础公理）
#print axioms GaugeCircle.critGauge_zero
#print axioms GaugeCircle.critGauge_mono
#print axioms GaugeCircle.critGauge_continuous
#print axioms GaugeCircle.critGauge_at_inv_Qsel
#print axioms GaugeCircle.binaryGauge_zero
#print axioms GaugeCircle.binaryGauge_mono
#print axioms GaugeCircle.binaryGauge_continuous
#print axioms GaugeCircle.binaryGauge_at_inv_Qsel
#print axioms GaugeCircle.mkMetric_critGauge_strictLevel_null
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_pos
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_eq_top
#print axioms GaugeCircle.critGauge_exactLevel_sigma_finite_cover
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_inter_Ioo_eq_top
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_inter_Icc_zero_one_eq_top
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_inter_eq_top_of_Ioo_subset
#print axioms GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_pos
#print axioms GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_inter_Ioo_eq_top
#print axioms GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_eq_top
#print axioms GaugeCircle.binaryGauge_unsignedExactLimit_sigma_finite_cover
#print axioms GaugeCircle.critGauge_unsignedExactLimit_null
#print axioms GaugeCircle.mkMetric_powerGauge_exactLevel_null_of_gt
#print axioms GaugeCircle.mkMetric_powerGauge_exactLevel_not_sigma_finite_of_lt
#print axioms GaugeCircle.mkMetric_powerGauge_unsignedExactLimit_null_of_gt
#print axioms GaugeCircle.mkMetric_powerGauge_unsignedExactLimit_not_sigma_finite_of_lt
#print axioms GaugeCircle.critGauge_ge_one
#print axioms GaugeCircle.critGauge_eq_segVal
#print axioms GaugeCircle.binaryGauge_ge_one
#print axioms GaugeCircle.binaryGauge_eq_segVal
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_not_sigma_finite_of_ratio
#print axioms GaugeCircle.critGauge_adjacent_ratio_tendsto_zero
#print axioms GaugeCircle.critGauge_adjacent_level_separation
#print axioms GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_inter_Icc_zero_one_eq_top
#print axioms GaugeCircle.mkMetric_critGauge_circleStrictLevel_null
#print axioms GaugeCircle.mkMetric_critGauge_circleExactLevel_inter_open_eq_top
#print axioms GaugeCircle.mkMetric_critGauge_circleExactLevel_eq_top
#print axioms GaugeCircle.mkMetric_critGauge_circleExactLevel_pos
#print axioms GaugeCircle.critGauge_circleExactLevel_sigma_finite_cover
#print axioms GaugeCircle.mkMetric_critGauge_circleExactLevel_not_sigma_finite_of_ratio
#print axioms GaugeCircle.mkMetric_powerGauge_circleExactLevel_null_of_gt
#print axioms GaugeCircle.mkMetric_powerGauge_circleExactLevel_not_sigma_finite_of_lt
#print axioms GaugeCircle.critGauge_circleUnsignedExactLimit_null
#print axioms GaugeCircle.binaryGauge_circleUnsignedExactLimit_sigma_finite_cover
#print axioms GaugeCircle.mkMetric_binaryGauge_circleUnsignedExactLimit_inter_open_eq_top
#print axioms GaugeCircle.mkMetric_binaryGauge_circleUnsignedExactLimit_eq_top
#print axioms GaugeCircle.mkMetric_binaryGauge_circleUnsignedExactLimit_pos
#print axioms GaugeCircle.mkMetric_powerGauge_circleUnsignedExactLimit_null_of_gt
#print axioms GaugeCircle.mkMetric_powerGauge_circleUnsignedExactLimit_not_sigma_finite_of_lt
#print axioms GaugeCircle.mkMetric_inter_Ioo_eq_top_of_compact_tree
#print axioms GaugeCircle.mkMetric_binCantorTree_pos
#print axioms GaugeCircle.unsignedExactLimit_add_latticeL
#print axioms GaugeCircle.mkMetric_le_mul_of_eventually_le_circle
#print axioms GaugeCircle.not_countable_union_finite_of_ratio_tendsto_zero_circle
#print axioms GaugeCircle.mkMetric_circleLevelSet_null_of_subgauge
-- Path 2A：共轭正性、一般有理端点四重算术刚性与 B = 3, 4, 5, 6 谱隙核心（GeneralEndpointRigidity，30 条，仅基础公理）
#print axioms GeneralEndpointRigidity.cfMatrix_det
#print axioms GeneralEndpointRigidity.cfMatrix_eval_eq
#print axioms GeneralEndpointRigidity.eta_conj_ge_inv_sq_of_gt_one
#print axioms GeneralEndpointRigidity.eta_conj_add_pos_gt_abs
#print axioms GeneralEndpointRigidity.eta_conj_eq_inv_sq_at_two
#print axioms GeneralEndpointRigidity.xi1_xi2Conj_identity
#print axioms GeneralEndpointRigidity.Muv_norm_identity
#print axioms GeneralEndpointRigidity.mobius_ratio_identity
#print axioms GeneralEndpointRigidity.ratio_eq_Muv_sub_div
#print axioms GeneralEndpointRigidity.inert_legendreSym_five_eq_neg_one
#print axioms GeneralEndpointRigidity.inert_prime_dvd_zphiNorm_iff
#print axioms GeneralEndpointRigidity.inert_prime_not_dvd_zphiNorm_of_cond
#print axioms GeneralEndpointRigidity.inert_prime_not_dvd_zphiNorm
#print axioms GeneralEndpointRigidity.inert_prime_not_dvd_zphiNorm_xi2
#print axioms GeneralEndpointRigidity.even_D_Muv_even
#print axioms GeneralEndpointRigidity.even_D_rigidity
#print axioms GeneralEndpointRigidity.even_D_rigidity_functional
#print axioms GeneralEndpointRigidity.mod_2D_sieve_q
#print axioms GeneralEndpointRigidity.mod_2D_sieve_p
#print axioms GeneralEndpointRigidity.mod_2d_sieve_special
#print axioms GeneralEndpointRigidity.Muv_norm_ne_zero
#print axioms GeneralEndpointRigidity.zphiNorm_xi2_dvd_norm_quot
#print axioms GeneralEndpointRigidity.b3_inert_three_not_dvd_m
#print axioms GeneralEndpointRigidity.b3_spectral_gap
#print axioms GeneralEndpointRigidity.b4_mod16_excludes_37
#print axioms GeneralEndpointRigidity.b4_spectral_gap
#print axioms GeneralEndpointRigidity.b5_even_m
#print axioms GeneralEndpointRigidity.b5_spectral_gap
#print axioms GeneralEndpointRigidity.b6_inert_three_not_dvd_m
#print axioms GeneralEndpointRigidity.b6_spectral_gap
-- §6.2 Theorem 16(iii) 完整补全（8 条）与 §6.3 一般多项式增长递推理论（37 条）（TrichotomyAndPolyExtension，45 条，仅基础公理）
#print axioms TrichotomyAndPolyExtension.xPlus_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.neg_xPlus_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.add_latticeL_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.signedExactLimitSet_pos_eq_coset
#print axioms TrichotomyAndPolyExtension.signedExactLimitSet_neg_eq_coset
#print axioms TrichotomyAndPolyExtension.signedExactLimitSet_zero_eq_latticeL
#print axioms TrichotomyAndPolyExtension.signedExactLimitSet_empty_of_not_quarter_int
#print axioms TrichotomyAndPolyExtension.trichotomy_part_iii_complete
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_Q_ge_factorial
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_pow_div_Q_tendsto_zero
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_Q_eq_lincomb
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_casorati
#print axioms TrichotomyAndPolyExtension.PolyRecData.alphaU_error_bound
#print axioms TrichotomyAndPolyExtension.PolyRecData.alphaV_error_bound
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_alpha_linear_relation
#print axioms TrichotomyAndPolyExtension.PolyRecData.theta_irrational
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_dist_le_of_mem_latticePoly
#print axioms TrichotomyAndPolyExtension.PolyRecData.polyWeightedExponent_eq_zero_of_mem_latticePoly
#print axioms TrichotomyAndPolyExtension.PolyRecData.polyApprExponent_eq_zero_tfae
#print axioms TrichotomyAndPolyExtension.PolyRecData.polyApprExponent_eq_zero_iff_mem_latticePoly
#print axioms TrichotomyAndPolyExtension.PolyRecData.polyApprExponent_eq_zero_iff_defect_zero
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_signed_defect_approx
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_abs_defect_approx
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_jr_mul_eps_tendsto_of_defect_const
#print axioms TrichotomyAndPolyExtension.PolyRecData.polyApprExponent_xPlusPoly
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_spectral_gap_open_interval
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_levelSet_eq_on_gap
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_levelSet_below_eq_lattice
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_signed_exact_limit_iff_defect_const
#print axioms TrichotomyAndPolyExtension.PolyRecData.xPlusPoly_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.PolyRecData.neg_xPlusPoly_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_sub_mem_latticePoly_of_same_signed_limit
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_add_latticePoly_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_trichotomy_part_iii_complete
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_supercritical_levelSet_eq_lattice
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_supercritical_dimH_zero
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_supercritical_empty_neg
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_dimH_levelSet_finite
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_dimH_finiteLevel_zero
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_volume_finiteLevel_zero
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_ae_apprExponent_eq_top
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_volume_infiniteLevel_Icc
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_dimH_infiniteLevel_inter_Icc_eq_one
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_dimH_infiniteLevel_eq_one
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_range_apprExponent

-- 2026-11-21 Takeover 合并：71 条新增声明（FiniteStateTail / PolyWeightedLower /
-- PolyWeightedUpper / HermiteResiduePeriod / GaugeLiminf / FiniteStateGauge 增补）。
-- 来源 Takeover/Overlay/TakeoverAudit.lean；暂存包见
-- paper1_e_plus_pi/05_research_process/antigravity-takeover/_staged_20261121/。
#print axioms PolyGaugeAndPhaseTransition.poly_log_Q_asymptotic
#print axioms PolyGaugeAndPhaseTransition.polyInterpGauge_log_scale_tendsto
#print axioms PolyGaugeAndPhaseTransition.poly_unsigned_exact_limit_iff_defect_binary
#print axioms PolyGaugeAndPhaseTransition.poly_unsigned_exact_limit_empty_of_not_div_c
#print axioms PolyGaugeAndPhaseTransition.mkMetric_polyCritGauge_polyStrictLevel_null
#print axioms PolyGaugeAndPhaseTransition.polyExactLevel_critGauge_sigma_finite
#print axioms PolyGaugeAndPhaseTransition.mkMetric_polyUnsignedExactLimit_null_of_critGauge
#print axioms PolyGaugeAndPhaseTransition.polyUnsignedExactLimit_binaryGauge_sigma_finite
#print axioms PolyGaugeAndPhaseTransition.mkMetric_polyCritGauge_polyExactLevel_inter_open_eq_top
#print axioms PolyGaugeAndPhaseTransition.mkMetric_polyBinaryGauge_unsignedExactLimit_inter_open_eq_top
#print axioms PolyGaugeAndPhaseTransition.mkMetric_polyCritGauge_polyCircleStrictLevel_null
#print axioms PolyGaugeAndPhaseTransition.mkMetric_polyCritGauge_polyCircleExactLevel_inter_open_eq_top
#print axioms PolyGaugeAndPhaseTransition.polyCircleExactLevel_critGauge_sigma_finite
#print axioms PolyGaugeAndPhaseTransition.mkMetric_polyCircleUnsignedExactLimit_null_of_critGauge
#print axioms PolyGaugeAndPhaseTransition.mkMetric_polyBinaryGauge_polyCircleUnsignedExactLimit_inter_open_eq_top
#print axioms PolyGaugeAndPhaseTransition.polyCircleUnsignedExactLimit_binaryGauge_sigma_finite
#print axioms PolyGaugeAndPhaseTransition.polyExactLevel_power_gauge_dichotomy
#print axioms PolyGaugeAndPhaseTransition.polyExactLevel_liminf_four_way
#print axioms PolyGaugeAndPhaseTransition.polyUnsignedExactLimit_liminf_four_way
#print axioms GaugeLiminf.mkMetric_digitClass_le_liminf
#print axioms GaugeLiminf.mkMetric_binaryDigitClass_le_liminf
#print axioms GaugeLiminf.mkMetric_levelSet_null_of_liminf_zero
#print axioms GaugeLiminf.mkMetric_unsignedExactLimit_null_of_liminf_zero
#print axioms GaugeLiminf.levelSet_countable_cover_of_liminf_lt_top
#print axioms GaugeLiminf.unsignedExactLimit_countable_cover_of_liminf_lt_top
#print axioms GaugeScaleComparison.small_radius_le_of_adjacent_scale_le
#print axioms GaugeScaleComparison.not_countable_union_finite_of_adjacent_scale_ratio
#print axioms GaugeScaleComparison.exists_small_radius_comparison_of_lt_liminf
#print axioms GaugeScaleComparison.not_countable_union_finite_of_liminf_top
#print axioms GaugeScaleComparison.mkMetric_eq_top_of_liminf_pos
#print axioms GaugeLiminf.calibrated_exactLevel_eq_top
#print axioms GaugeLiminf.exactLevel_eq_top_of_liminf_pos
#print axioms GaugeLiminf.exactLevel_not_countable_union_finite_of_liminf_top
#print axioms GaugeLiminf.circleExactLevel_liminf_trichotomy
#print axioms GaugeLiminf.circleUnsignedExactLimit_liminf_trichotomy
#print axioms GaugeLiminf.liminf_normalizedGaugeCost_zero_of_smaller_base
#print axioms GaugeLiminf.mkMetric_circleStrictLevel_null_of_liminf_lt_top
#print axioms FiniteStateGauge.walkMass_of_eigenvector
#print axioms FiniteStateGauge.walkCount_bounds
#print axioms PolyGaugeAndPhaseTransition.mkMetric_polyLevelSet_null_of_liminf_zero
#print axioms PolyGaugeAndPhaseTransition.polyExactLevel_fast_gauge_null
#print axioms PolyGaugeAndPhaseTransition.polyExactLevel_slow_gauge_non_sigma_finite
#print axioms PolyWeightedUpper.dimH_polyWeightedExponent_le
#print axioms HermiteResiduePeriod.state_eq_selected
#print axioms HermiteResiduePeriod.selected_period
#print axioms HermiteResiduePeriod.state_period_3
#print axioms HermiteResiduePeriod.state_period_4
#print axioms HermiteResiduePeriod.state_period_5
#print axioms HermiteResiduePeriod.state_period_6
#print axioms PolyWeightedLower.exists_lower_growth
#print axioms PolyWeightedLower.exists_level_threshold
#print axioms PolyWeightedLower.one_le_hausdorffMeasure_cantorSet
#print axioms PolyWeightedLower.dimH_polyExactLimit_ge
#print axioms PolyWeightedLower.dimH_polyExactLimit_eq
#print axioms PolyWeightedLower.dimH_polyWeightedSublevel_eq
#print axioms PolyWeightedLower.polyZeroWeightSublevel_eq_univ
#print axioms PolyWeightedLower.polyExactLimit_zero_eq_empty
#print axioms FiniteStateGauge.card_path_eq_walkMass
#print axioms FiniteStateGauge.mkMetric_fixedTail_le
#print axioms FiniteStateGauge.mkMetric_eventualTail_null
#print axioms FiniteStateGauge.eventualTail_countable_cover_finite
#print axioms FiniteStateGauge.fixedTail_finite_of_root_one
#print axioms FiniteStateGauge.eventualTail_countable_of_root_one
#print axioms FiniteStateGauge.mkMetric_circle_fixedTail_le
#print axioms FiniteStateGauge.exists_marked_edge_with_return
#print axioms FiniteStateGauge.frequently_defectShift_eq_level
#print axioms FiniteStateGauge.exactTail_empty_of_no_marked_return
#print axioms FiniteStateGauge.exists_component_suffix
#print axioms FiniteStateGauge.exactTail_eq_iUnion_marked_components
#print axioms FiniteStateGauge.exactTail_countable_of_marked_roots_one
#print axioms FiniteStateGauge.mkMetric_exactTail_null_of_dominant_liminf_zero

-- 2026-11-21 桥接/约化补审计：thm:conditional-bridge 与 thm:ai-reduction 的声明在树内已编过，
-- 此前 Audit.lean import 闭包未引入其模块故无条目；在模块文件上下文中 lean_verify 已实测通过
-- （reconciliation 纯基础；bridge 仅 +pi_transcendental；四个约化全纯基础），现接入审计入口。
#print axioms OpenAIBridge.irrMeasure_le_two_of_PiEventualLowerBound
#print axioms OpenAIBridge.flint_hills_of_PiEventualLowerBound
#print axioms EpiFormal.transcendental_add_of_algebraicIndependent
#print axioms EpiFormal.transcendental_sub_of_algebraicIndependent
#print axioms EpiFormal.transcendental_mul_of_algebraicIndependent
#print axioms EpiFormal.transcendental_div_of_algebraicIndependent

-- 2026-11-21 short-ae 组装合入：WindowShortAe.lean（14 定理，lake env lean EXIT 0、零 sorry，
-- lean_verify 14/14 纯基础三公理）。主会话亲手复验后合入；声明全名为 WindowShortAe.*。
-- 接口假设（滤波/停时柱/Möbius 未形式化）见 triage 记录与攻击报告，triage 表中 short-ae 记为
-- "组装已核实/实例化接口纸面"，非端到端。
#print axioms WindowShortAe.short_ae_one_step_factor
#print axioms WindowShortAe.short_ae_step_factor_from_cylinders
#print axioms WindowShortAe.short_ae_telescope
#print axioms WindowShortAe.short_ae_harmonic_ge_log
#print axioms WindowShortAe.short_ae_exp_to_poly
#print axioms WindowShortAe.short_ae_tower_closed_form
#print axioms WindowShortAe.short_ae_markov_meas_bound
#print axioms WindowShortAe.short_ae_dyadic_rpow_eq
#print axioms WindowShortAe.short_ae_dyadic_ratio_bound
#print axioms WindowShortAe.short_ae_dyadic_summable
#print axioms WindowShortAe.short_ae_BC_ae
#print axioms WindowShortAe.short_ae_step_algebra
#print axioms WindowShortAe.short_ae_dyadic_to_full
#print axioms WindowShortAe.short_ae_main

-- 2026-11-21 dirichlet-divisor 合入：DirichletDivisor.lean（13 声明，lake env lean EXIT 0、
-- 文件内 sorry 零命中〈第 32 行系中文注释〉，lean_verify 抽查纯基础；namespace DVerify）。
-- 主会话亲手复验后合入；tex 第 324 行"十条已审计声明"至此在本工作区转正。
#print axioms DVerify.Qsel_pos_all
#print axioms DVerify.H_le
#print axioms DVerify.H_lt
#print axioms DVerify.H_pos
#print axioms DVerify.dirichlet_witness
#print axioms DVerify.linForm_identity
#print axioms DVerify.linForm_abs_lt_one
#print axioms DVerify.linForm_eq_zero
#print axioms DVerify.Psel_Qsel_coprime
#print axioms DVerify.gcd_dvd_Qsel
#print axioms DVerify.divisor_restriction
#print axioms DVerify.prop_8_1_div
#print axioms DVerify.prop_8_1

-- 2026-11-21 golden-finite-shift 合入：GoldenFiniteShift.lean（29 声明，lake env lean EXIT 0、
-- 文件内 sorry 零命中〈第 57 行系中文注释〉，29/29 纯基础三公理；namespace GoldenFiniteShift）。
-- 主会话亲手复验后合入；覆盖假设 hcover 与窗口相位提取仍为显式纸面接口（见攻击报告），
-- triage 状态记为"骨架已核实/覆盖假设纸面"。
#print axioms GoldenFiniteShift.search_bound_fixed_q
#print axioms GoldenFiniteShift.search_bound_strong_a
#print axioms GoldenFiniteShift.search_bound_moving_dist
#print axioms GoldenFiniteShift.search_bound_moving_offset
#print axioms GoldenFiniteShift.search_bound_gen_height
#print axioms GoldenFiniteShift.search_bound_norm_cutoff
#print axioms GoldenFiniteShift.search_bound_suffix_m
#print axioms GoldenFiniteShift.orbit_height_lower_bound
#print axioms GoldenFiniteShift.quadratic_tail_value_mem_lattice
#print axioms GoldenFiniteShift.suffix_value_mem_lattice
#print axioms GoldenFiniteShift.Dsqrt5_pos
#print axioms GoldenFiniteShift.Dsqrt5_irrational
#print axioms GoldenFiniteShift.dist_int_pos
#print axioms GoldenFiniteShift.lattice_spectrum_pos_min
#print axioms GoldenFiniteShift.lattice_values_separated
#print axioms GoldenFiniteShift.first_two_below_three
#print axioms GoldenFiniteShift.latticeSlab_finite
#print axioms GoldenFiniteShift.mem_latticeSlab_of_abs_le
#print axioms GoldenFiniteShift.suffixCand_finite
#print axioms GoldenFiniteShift.fixedCand_finite
#print axioms GoldenFiniteShift.movingCand_finite
#print axioms GoldenFiniteShift.latticeVal_comm
#print axioms GoldenFiniteShift.suffixCand_mem_lattice
#print axioms GoldenFiniteShift.fixedCand_mem_lattice
#print axioms GoldenFiniteShift.movingCand_mem_lattice
#print axioms GoldenFiniteShift.norm_divisor_finite
#print axioms GoldenFiniteShift.suffix_divisor_candidates_finite
#print axioms GoldenFiniteShift.finite_shift_of_covers
#print axioms GoldenFiniteShift.finite_shift_separated

-- 2026-11-21 affine-window phase-1 合入：AffineWindowAssembly.lean（7 声明，主会话亲手写+复验，
-- lake env lean EXIT 0；基础三公理及更弱：D_period 仅 propext，r_period 零公理；namespace AffineWindow）。
-- 接口假设显式（locked denominators / Hermite recurrence / mod-T congruence / digit rule），
-- triage 状态记为"组装已核实/实例化接口纸面"。
#print axioms AffineWindow.T_pos
#print axioms AffineWindow.D_pos
#print axioms AffineWindow.D_even
#print axioms AffineWindow.r_ge_three
#print axioms AffineWindow.D_period
#print axioms AffineWindow.r_period
#print axioms AffineWindow.first_digit_shift

-- 2026-11-21 farey-gap 集成：DenominatorCertificate.lean（4 声明，namespace EpiCertificate，
-- 原 04_formalization_audits 工作拷贝，原样入库；lake env lean EXIT 0，全基础三公理）。
-- prop:farey-gap 的"四声明已审计"声称转正。
#print axioms EpiCertificate.farey_bounds
#print axioms EpiCertificate.denominator_bound
#print axioms EpiCertificate.uniform_gap
#print axioms EpiCertificate.no_adjacent_match

-- 2026-11-21 finite-state-tail 正测度下界：6 条新增声明（Perron 有限词一致性
-- + 覆盖代价 + Frostman 比较 + 缩放 gauge 正测度）。μ 构造/a.e.穿越/Haar
-- 局部无穷为显式纸面接口（见文件头）；详见 verification/finite_positive_merge_20261121.md。
#print axioms FiniteStateGauge.perron_word_mass_sum
#print axioms FiniteStateGauge.perron_word_mass_bound
#print axioms FiniteStateGauge.muRestricted_elem_le
#print axioms FiniteStateGauge.muRestrict_le_mkMetric_hlam
#print axioms FiniteStateGauge.one_le_mkMetric_scaled
#print axioms FiniteStateGauge.pos_mkMetric_scaled

-- 2026-11-21 windows 下界组装（一）：WindowMobiusCount 计数核心（13 条）。
#print axioms WindowMobiusCount.nat_div_mono
#print axioms WindowMobiusCount.countMultiples
#print axioms WindowMobiusCount.intervalCount
#print axioms WindowMobiusCount.moebius_indicator
#print axioms WindowMobiusCount.key_mem_iff
#print axioms WindowMobiusCount.prod_filter_eq
#print axioms WindowMobiusCount.coprime_count_eq
#print axioms WindowMobiusCount.nat_div_cast_lower
#print axioms WindowMobiusCount.nat_div_cast_upper
#print axioms WindowMobiusCount.one_div_le_log_pred
#print axioms WindowMobiusCount.harmonic_tail_aux
#print axioms WindowMobiusCount.harmonic_le
#print axioms WindowMobiusCount.moebius_tail_sq

-- 2026-11-21 windows 下界组装（二）：WindowMobiusPartial 部分和下界（3 条）。
#print axioms WindowMobiusCount.moebius_first_five
#print axioms WindowMobiusCount.moebius_tail_le
#print axioms WindowMobiusCount.moebius_partial

-- 2026-11-21 windows 下界组装（三）：WindowWindowBounds 窗口界（8 条＋2 辅助等式）。
#print axioms WindowMobiusCount.W1_lo
#print axioms WindowMobiusCount.W1_hi
#print axioms WindowMobiusCount.W2_lo
#print axioms WindowMobiusCount.W2_hi
#print axioms WindowMobiusCount.W1_eq_cast
#print axioms WindowMobiusCount.Acount_lo
#print axioms WindowMobiusCount.Acount_hi
#print axioms WindowMobiusCount.W2_eq_cast
#print axioms WindowMobiusCount.Bcount_lo
#print axioms WindowMobiusCount.Bcount_hi

-- 2026-11-21 windows 下界组装（四）：WindowMainBound 主定理与对数链（6 条）。
#print axioms WindowMobiusCount.exp_three_gt_ten
#print axioms WindowMobiusCount.log_ten_lt_three
#print axioms WindowMobiusCount.log106_lt
#print axioms WindowMobiusCount.logMhi_le
#print axioms WindowMobiusCount.err_bound
#print axioms WindowMobiusCount.coprime_count_ge

-- 2026-11-21 no-short-dim phase 1: Q/H ratio bounds + gamma_pos (L01/L05).
#print axioms NoShortDim.Q_ratio_lo
#print axioms NoShortDim.Q_ratio_hi
#print axioms NoShortDim.Qsqrt_ge_one
#print axioms NoShortDim.H_ge_one
#print axioms NoShortDim.H_ratio_lo
#print axioms NoShortDim.Qsqrt_ge_two
#print axioms NoShortDim.H_ratio_hi
#print axioms NoShortDim.gamma_pos

-- 2026-11-21 no-short-dim L06: short-rectangle Möbius coprime count (21 decls).
#print axioms NoShortDim.boxS_mem_iff
#print axioms NoShortDim.MloS_ge_one
#print axioms NoShortDim.NloS_ge_one
#print axioms NoShortDim.boxS_mem_pos
#print axioms NoShortDim.boxS_nonempty
#print axioms NoShortDim.W1S_lo
#print axioms NoShortDim.W1S_hi
#print axioms NoShortDim.W2S_lo
#print axioms NoShortDim.W2S_hi
#print axioms NoShortDim.W1S_eq_cast
#print axioms NoShortDim.AcountS_lo
#print axioms NoShortDim.AcountS_hi
#print axioms NoShortDim.W2S_eq_cast
#print axioms NoShortDim.BcountS_lo
#print axioms NoShortDim.BcountS_hi
#print axioms NoShortDim.keyS_mem_iff
#print axioms NoShortDim.prodS_filter_eq
#print axioms NoShortDim.coprimeS_count_eq
#print axioms NoShortDim.logMhiS_le
#print axioms NoShortDim.errS_bound
#print axioms NoShortDim.coprimeS_count_ge

-- 2026-11-21 cylinder phase A: continuant matrices (8 decls).
#print axioms Cylinder.cfMat_det
#print axioms Cylinder.cfProd_det
#print axioms Cylinder.convPair_cons
#print axioms Cylinder.convPair_nonneg
#print axioms Cylinder.convDen_nonneg
#print axioms Cylinder.convNum_nonneg
#print axioms Cylinder.convDen_cons
#print axioms Cylinder.convNum_cons
#print axioms Cylinder.cfProd_append_single
#print axioms Cylinder.col1_convPair
#print axioms Cylinder.sibling_cross
#print axioms Cylinder.cfProd_nonneg
#print axioms Cylinder.cfProd_det_ne_zero
#print axioms Cylinder.childDen_pos
#print axioms Cylinder.sibling_strict
#print axioms Cylinder.consec_cross
#print axioms Cylinder.consec_cross_abs
#print axioms Cylinder.childDen_ge_one
#print axioms Cylinder.children
#print axioms Cylinder.mem_children_iff
#print axioms Cylinder.card_children
#print axioms Cylinder.fiber_card_eq
#print axioms Cylinder.child_prefix_self
#print axioms Cylinder.frac_abs_sub_of_unit_cross
#print axioms Cylinder.diam_Icc_min_max
#print axioms Cylinder.child_cyl_diam
#print axioms Cylinder.rpow_add_le_add_rpow
#print axioms Cylinder.ediam_thickening_le
#print axioms Cylinder.frostman_of_count_thresh
#print axioms Cylinder.frostman_dimH_le
#print axioms WindowMuLevel.filter_meet_card
#print axioms WindowMuLevel.mu_le_at_level
#print axioms WindowMuLevel.mu_le_of_sandwich
#print axioms WindowMass.ofReal_diam_le_mul_ediam_rpow
#print axioms WindowMass.mass_distrib_of_diam_bound
#print axioms CoverCount.left_separated
#print axioms CoverCount.floor_lt_of_separated
#print axioms CoverCount.meet_card_le
#print axioms CoverCount.meet_card_of_diam_le
#print axioms HinterBridge.thresh_bridge
#print axioms HinterBridge.fiber_count_ge
#print axioms CoverCount.child_len_bounds
#print axioms CoverCount.stopped_cyl_len_bounds
#print axioms CoverCount.window_overlap_le
#print axioms WindowMu.mu_biUnion_le
#print axioms WindowMu.mu_window_le
#print axioms WindowMu.exp_ratio_bound
#print axioms WindowMuBound.mu_le_of_overlap_thresh
#print axioms WindowMuScale.stopped_thresh_of_scale
#print axioms WindowMuScale.stopped_window_bound
#print axioms WindowSplitMass.uniform_split_mass_bound
#print axioms WindowMuThreshLevel.mu_window_thresh_num
#print axioms StoppedTree.Ioo_subset_of_Icc_subset
#print axioms StoppedTree.nodup_of_children_disjoint
#print axioms StoppedTree.mass_le_of_split
#print axioms WindowFrostDirect.direct_rpow_add_le_add_rpow
#print axioms WindowFrostDirect.direct_ediam_thickening_le
#print axioms WindowFrostDirect.frostman_of_window_layer
#print axioms WindowRealize.stopped_window_realize
#print axioms WindowConcrete.stopped_window_unit
#print axioms WindowLargeWindow.mu_large_window
#print axioms WindowLargeThresh.large_window_thresh
#print axioms WindowSandwich.sandwich_of_tendsto
#print axioms WindowThickBound.mu_thickened_le
#print axioms WindowLevelCount.level_count_ge
#print axioms WindowLogFact.log_factorial_ge
#print axioms WindowLogFact.log_factorial_le
#print axioms WindowWordTree.append_single_injective
#print axioms WindowWordTree.children_disjoint
#print axioms WindowWordTree.children_mem_next
#print axioms WindowWordTree.childrenOf_card
#print axioms WindowWordTree.mem_childrenOf
#print axioms WindowWordTree.nil_mem_levelWords_zero
#print axioms WindowWordTree.uniform_level_count
#print axioms WindowMassProd.mass_le_prod
#print axioms WindowMassProd.prod_Ico_self_eq_fact_div
#print axioms WindowMassProd.mass_le_fact_bound
#print axioms WindowLogThresh.log_inv_le_two_log
#print axioms WindowLogThresh.frostman_ratio_bound
#print axioms WindowMassFull.mu_window_le_full
#print axioms WindowDescFiber.desc_mem
#print axioms WindowDescFiber.desc_card_le
#print axioms WindowStoppedUniform.stopped_uniform_bound
#print axioms WindowThickening.isBounded_thickening_of_ediam
#print axioms WindowThickening.diam_thickening_pos
#print axioms WindowPointMass.mu_singleton_zero

-- 2026-11-22 L05 Frostman discharge + hCbig/小窗级联 + 论文真实尺度 H_j + 非空真见证（47 条，全基础三公理）。
#print axioms WindowTreePrune.isClosed_levelUnion
#print axioms WindowTreePrune.isCompact_cantorSet
#print axioms WindowTreePrune.desc_mem_from
#print axioms WindowTreePrune.desc_card_le_from
#print axioms WindowTreePrune.exists_ancestor_desc
#print axioms WindowTreePrune.exists_mem_cantorSet_of_mem_atoms
#print axioms WindowTreePrune.cantorSet_nonempty
#print axioms WindowTreePrune.atoms_card_le_sum_meet_desc
#print axioms WindowTreePrune.pruneChild_subset
#print axioms WindowTreePrune.pruneChild_card
#print axioms WindowTreePrune.pruneTree_atoms_base
#print axioms WindowTreePrune.pruneTree_atoms_succ
#print axioms WindowTreePrune.pruneTree_atoms_subset
#print axioms WindowTreePrune.pruneTree_child_mem
#print axioms WindowTreePrune.pruneTree_mem_parent
#print axioms WindowTreePrune.pruneTree_child_card
#print axioms WindowTreePrune.pruneTree_atoms_card
#print axioms WindowTreePrune.cantorSet_pruneTree_subset
#print axioms WindowAsympThresh.general_overlap_const
#print axioms WindowAsympThresh.stopped_overlap_const
#print axioms WindowAsympThresh.log_pred_fact_ge
#print axioms WindowAsympThresh.asymp_thresh_exists_rpow
#print axioms WindowAsympThresh.asymp_thresh_exists
#print axioms WindowAsympThresh.coprime_branching_quad
#print axioms WindowAsympThresh.coprimeS_branching_rpow
#print axioms WindowAsympThresh.hCbig_of_ge_scale
#print axioms WindowFrostmanDischarge.frostman_of_uniform_tree
#print axioms WindowFrostmanDischarge.frostman_of_stopped_tree_rpow
#print axioms WindowFrostmanDischarge.dimH_ge_of_stopped_tree_rpow
#print axioms WindowFrostmanDischarge.dimH_ge_one_of_coprime_tree
#print axioms WindowFrostmanDischarge.dimH_ge_gamma_of_coprimeS_tree
#print axioms WindowFrostmanDischarge.mass_distrib_of_local_diam_bound
#print axioms WindowFrostmanDischarge.dimH_ge_of_local_diam_bound
#print axioms WindowFrostmanDischarge.mu_singleton_zero_of_support
#print axioms WindowFrostmanDischarge.mu_window_cascade_full
#print axioms WindowFrostmanDischarge.dimH_ge_of_mu_window_cascade
#print axioms WindowPaperScale.Hpaper_pos
#print axioms WindowPaperScale.Hpaper_eq
#print axioms WindowPaperScale.Rpaper_ge_three_mul
#print axioms WindowPaperScale.Rpaper_ge_ten_pow_six
#print axioms WindowPaperScale.Hpaper_ge_three_pow
#print axioms WindowPaperScale.Hpaper_inv_sq_tendsto
#print axioms WindowPaperScale.Hpaper_le_fact
#print axioms WindowPaperScale.Hpaper_log_le
#print axioms WindowPaperScale.dimH_ge_one_windows_paper_scale
#print axioms WindowPaperScale.dimH_ge_half_prescribed_paper_scale
#print axioms WindowPaperScale.exists_j0_no_short
#print axioms WindowPaperScale.dimH_ge_gamma_no_short_paper_scale
#print axioms WindowPaperScale.dimH_ge_one_of_gamma_family
#print axioms WindowPaperScale.cantorSet_factTree_eq_Icc
#print axioms WindowPaperScale.nonvacuous_factorial_tree_dimH
#print axioms WindowPaperScale.nonvacuous_factorial_measure_dimH

-- 2026-11-22 CF stopping-rule realization for thm:windows (26 条，全基础三公理，零树前提).
#print axioms WindowCFRealize.cfProd_append
#print axioms WindowCFRealize.cfProd_col0_pos
#print axioms WindowCFRealize.cfProd_row1_le_row0
#print axioms WindowCFRealize.cfProd_col1_le_col0
#print axioms WindowCFRealize.den_mono_prefix
#print axioms WindowCFRealize.append_penult_bounds
#print axioms WindowCFRealize.euclidCF_pos_digits
#print axioms WindowCFRealize.euclidCF_col0
#print axioms WindowCFRealize.euclidCF_last_ge_two
#print axioms WindowCFRealize.flipLast_col0
#print axioms WindowCFRealize.chooseParityCF_props
#print axioms WindowCFRealize.mobius_sub
#print axioms WindowCFRealize.mobius_mul
#print axioms WindowCFRealize.cylPair_len
#print axioms WindowCFRealize.cylPair_len_bounds
#print axioms WindowCFRealize.mobius_mem_cylPair
#print axioms WindowCFRealize.cylPair_nest
#print axioms WindowCFRealize.cylPair_disj_sibling
#print axioms WindowCFRealize.cylPair_disj_of_incomparable
#print axioms WindowCFRealize.initWord_inv
#print axioms WindowCFRealize.parentScale_ge
#print axioms WindowCFRealize.childWord_transition
#print axioms WindowCFRealize.childWord_incomparable
#print axioms WindowCFRealize.cfWordAtoms_inv_and_incomp
#print axioms WindowCFRealize.cylPair_injOn_atoms
#print axioms WindowCFRealize.dimH_ge_one_cfWindowsTree

-- 2026-11-22 Pointwise regular CF bridge + thm:no-short-dim & b=1 prescribed-count CF realizations
-- (54 条，全基础三公理，端到端闭环 mathlib GenContFract.of / cfStopIdx).
#print axioms WindowCFBridge.mobius_mem_Ioo_cylPair
#print axioms WindowCFBridge.Ioo_cylPair_subset_Ioo_unit
#print axioms WindowCFBridge.cylPair_nest_strict
#print axioms WindowCFBridge.exists_mobius_of_mem_Ioo_cylPair
#print axioms WindowCFBridge.mobius_cfProd_zero_mem_Ioo
#print axioms WindowCFBridge.mobius_cfProd_zero_cons
#print axioms WindowCFBridge.intFractPair_stream_one_div_add
#print axioms WindowCFBridge.stream_mobius_spec
#print axioms WindowCFBridge.not_terminatedAt_mobius
#print axioms WindowCFBridge.contsAux_mobius_eq
#print axioms WindowCFBridge.dens_mobius_eq
#print axioms WindowCFBridge.dens_mobius_top_and_penult
#print axioms WindowCFBridge.dens_of_mono
#print axioms WindowCFBridge.cfStopIdx_eq_of_bracket
#print axioms WindowCFBridge.stopped_word_tree_cf_bridge
#print axioms WindowCFBridge.dimH_le_one_of_subset_Ioo_unit
#print axioms WindowCFBridge.mem_cantorSet_cfWindowsTree_cf
#print axioms WindowCFBridge.cantorSet_cfWindowsTree_subset_prescribedParitySet
#print axioms WindowCFBridge.dimH_ge_one_prescribedParitySet
#print axioms WindowCFBridge.dimH_prescribedParitySet_eq_one
#print axioms WindowNoShortCFRealize.cfProd_replicate_one
#print axioms WindowNoShortCFRealize.fib_le_goldenRatio_pow
#print axioms WindowNoShortCFRealize.prelude_den_bounds
#print axioms WindowNoShortCFRealize.initWordAt_inv
#print axioms WindowNoShortCFRealize.j0NoShort_scale
#print axioms WindowNoShortCFRealize.noShortScale_ge
#print axioms WindowNoShortCFRealize.noShortScale_ge_ten_pow_six
#print axioms WindowNoShortCFRealize.noShortChild_transition
#print axioms WindowNoShortCFRealize.noShortChild_incomparable
#print axioms WindowNoShortCFRealize.noShortWordAtoms_inv_and_incomp
#print axioms WindowNoShortCFRealize.cylPair_injOn_noShortAtoms
#print axioms WindowNoShortCFRealize.dimH_ge_gamma_cfNoShortTree
#print axioms WindowNoShortCFRealize.mem_cantorSet_cfNoShortTree_cf
#print axioms WindowNoShortCFRealize.cantorSet_cfNoShortTree_subset_noShortSet
#print axioms WindowNoShortCFRealize.dimH_ge_gamma_noShortSet
#print axioms WindowNoShortCFRealize.noShortSet_subset_divWindowSet
#print axioms WindowNoShortCFRealize.dimH_ge_one_divWindowSet
#print axioms WindowNoShortCFRealize.dimH_divWindowSet_eq_one
#print axioms WindowPrescribedCFRealize.initWordAt_prescribedInv
#print axioms WindowPrescribedCFRealize.prescPrelude_bounds
#print axioms WindowPrescribedCFRealize.prescRatio_ge
#print axioms WindowPrescribedCFRealize.prescDigits_card_ge
#print axioms WindowPrescribedCFRealize.prescChild_transition
#print axioms WindowPrescribedCFRealize.prescChild_incomparable
#print axioms WindowPrescribedCFRealize.prescWordAtoms_inv_and_incomp
#print axioms WindowPrescribedCFRealize.cylPair_injOn_prescAtoms
#print axioms WindowPrescribedCFRealize.dimH_ge_half_cfPrescribedTree
#print axioms WindowPrescribedCFRealize.prescribedIncSetAt_disjoint
#print axioms WindowPrescribedCFRealize.mem_cantorSet_cfPrescribedTree_cf
#print axioms WindowPrescribedCFRealize.cantorSet_cfPrescribedTree_subset_prescribedIncSetAt
#print axioms WindowPrescribedCFRealize.dimH_ge_half_prescribedIncSetAt
#print axioms WindowPrescribedCFRealize.exists_start_dimH_ge_half_prescribedIncSetAt
#print axioms WindowPrescribedCFRealize.dimH_ge_half_prescribedIncSet
#print axioms WindowPrescribedCFRealize.dimH_ge_half_boundedIncSet

-- 2026-11-22 Upper dimension 1/2 for boundedIncSet (closes all of thm:windows, 21 decls)
-- + all 8 Paper-1 standalone modules integrated (29 decls). Total +50 decls, base axioms only.
#print axioms WindowBoundedUpper.cfProd_den_ge_length_aux
#print axioms WindowBoundedUpper.cfProd_den_ge_length
#print axioms WindowBoundedUpper.list_prod_le_cfProd_den
#print axioms WindowBoundedUpper.cfProd_den_ge_prod
#print axioms WindowBoundedUpper.Hpaper_ge_fact
#print axioms WindowBoundedUpper.nat_pow_le_factorial
#print axioms WindowBoundedUpper.exists_word_of_irrational
#print axioms WindowBoundedUpper.exists_word_cover_of_irrational
#print axioms WindowBoundedUpper.nat_le_dens_of_irrational
#print axioms WindowBoundedUpper.H_lt_dens_of_cfStopIdx_lt
#print axioms WindowBoundedUpper.boundedIncSet_dens_exp_growth
#print axioms WindowBoundedUpper.ediam_cylPair_le
#print axioms WindowBoundedUpper.zetaTerm_ne_top
#print axioms WindowBoundedUpper.tsum_prod_rpow_eq
#print axioms WindowBoundedUpper.tsum_cfProd_den_rpow_le
#print axioms WindowBoundedUpper.hausdorffMeasure_tailSet_zero
#print axioms WindowBoundedUpper.hausdorffMeasure_boundedIncSet_zero
#print axioms WindowBoundedUpper.dimH_boundedIncSet_le_half
#print axioms WindowBoundedUpper.dimH_boundedIncSet_eq_half
#print axioms WindowBoundedUpper.dimH_prescribedIncSet_eq_half
#print axioms WindowBoundedUpper.dimH_prescribedIncSetAt_eq_half

#print axioms GoldenHeadCutoff.fixed_side_ratio
#print axioms GoldenHeadCutoff.moving_side_ratio
#print axioms GoldenHeadCutoff.mismatch_gap
#print axioms rational_endpoint_cutoff
#print axioms AffineWindowAudit.no_five_alternations
#print axioms AffineWindowAudit.no_modEight_middle
#print axioms AffineWindowAudit.prime_no_five_divisibility
#print axioms AffineWindowAudit.eight_not_dvd_middle
#print axioms AffineWindowAudit.selectedNumerator_step
#print axioms AffineWindowAudit.selectedNumerator_no_five
#print axioms AffineWindowAudit.selectedNumerator_no_eight_middle
#print axioms AffineWindowAudit.sixthModel_four_products
#print axioms DigitTailBound.fib_length_le_continuant
#print axioms DigitTailBound.digit_le_continuant
#print axioms DensityCube.squareResidueWitness
#print axioms DensityCube.oddMultiplier
#print axioms DensityCube.cubicExponent
#print axioms DensityCube.amplitudeBalance
#print axioms OrbitAndFlow.primeNorm_unitFactor
#print axioms OrbitAndFlow.pathSlack_telescopes
#print axioms ResearchAdvance.integerBudget_zero
#print axioms ResearchAdvance.stripBudget
#print axioms ResearchAdvance.digitGap
#print axioms ResearchAdvance.stripWeight_eq
#print axioms ResearchAdvance.normSevenExcluded
#print axioms TraceMarkov.primitiveFactor
#print axioms TraceMarkov.discriminantSixtyProgression
#print axioms TraceMarkov.potentialSum_eq
#print axioms TraceMarkov.twoReturnVariance
#print axioms WindowShortAeRealize.cfStopIdx_spec_of_irrational
#print axioms WindowShortAeRealize.stoppedWords_incomparable
#print axioms WindowShortAeRealize.stoppedWords_disjoint
#print axioms WindowShortAeRealize.stoppedWords_cover_irrationals
#print axioms WindowShortAeRealize.stoppedWords_cyl_ae_mem
#print axioms WindowShortAeRealize.cfStopIdx_const_on_stoppedCyl
#print axioms WindowShortAeRealize.measurableSet_shortWinEvent
#print axioms WindowShortAeRealize.atom_shortWin_volume_ge
#print axioms WindowShortAeRealize.atom_exp_neg_shortWinCount_step
#print axioms WindowShortAeRealize.integral_exp_neg_shortWinCount_step
#print axioms WindowShortAeRealize.thm_short_ae_explicit
#print axioms WindowShortAeRealize.thm_short_ae
#print axioms WindowShortAeRealize.volume_divWindowSet_eq_zero
#print axioms WindowShortAeRealize.thm_no_short_dim_complete
#print axioms ResidueModGeneral.cfVal_cfDigit
#print axioms ResidueModGeneral.lipschitzOnWith_cfShift
#print axioms ResidueModGeneral.dimH_residueSeqSet_add_le
#print axioms ResidueModGeneral.dimH_residueSeqSet_sandwich
#print axioms ResidueModGeneral.dimH_mobius_prefix_eq
#print axioms ResidueModGeneral.dimH_eventualResidueSeqSet_le
#print axioms ResidueModGeneral.dimH_eventuallyPeriodicResidueSet_eq
#print axioms TransferOperatorDim.hausdorffMeasure_le_of_transferOp_le
#print axioms TransferOperatorDim.dimH_le_of_transferOp_le
#print axioms TransferOperatorDim.isCompact_cfAlphabetSet
#print axioms TransferOperatorDim.hausdorffMeasure_pos_of_transferOp_ge
#print axioms TransferOperatorDim.le_dimH_of_transferOp_ge
#print axioms TransferOperatorDim.half_lt_dimH_residueConstSet
#print axioms TransferOperatorDim.tsum_arith_tail_le
#print axioms TransferOperatorDim.sum_arith_lower_ge
#print axioms TransferOperatorDim.dimH_residueMod4_le_four_fifths
#print axioms TransferOperatorDim.step_cert_upper_sound
#print axioms TransferOperatorDim.step_cert_lower_sound
#print axioms FiniteStateComplete.one_le_k_of_one_lt_growth
#print axioms FiniteStateComplete.wordOfPath_injective
#print axioms FiniteStateComplete.isCompact_graphTree
#print axioms FiniteStateComplete.graphTree_subset_fixedTail
#print axioms FiniteStateComplete.mkMetric_graphTree_pos
#print axioms FiniteStateComplete.mkMetric_unmarkedTail_null
#print axioms FiniteStateComplete.defect_zero_of_mem_latticeL
#print axioms FiniteStateComplete.exactTail_add_latticeL
#print axioms FiniteStateComplete.mkMetric_exactTail_inter_Ioo_eq_top
#print axioms FiniteStateComplete.mkMetric_circleExactTail_inter_open_eq_top
#print axioms FiniteStateComplete.thm_finite_state_tail_complete
#print axioms FiniteStateComplete.thm_finite_state_tail_circle_complete
#print axioms ResidueAsymptotic.metalQ_one_eq_fib
#print axioms ResidueAsymptotic.metalC_one_eq_psiFib
#print axioms ResidueAsymptotic.resolventV_branch_eq
#print axioms ResidueAsymptotic.dimH_residueConstSet_le_of_resolvent
#print axioms ResidueAsymptotic.le_dimH_residueConstSet_of_resolvent
#print axioms ResidueAsymptotic.dimH_residueConstSet_mm_le
#print axioms ResidueAsymptotic.le_dimH_residueConstSet_mm
#print axioms ResidueAsymptotic.dimH_residueConstSet_mm_lt_m1
#print axioms ResidueAsymptotic.dimH_residueConstSet_mm_lt_eventuallyPeriodic
#print axioms ResidueAsymptotic.dimH_residueConstSet_asymp_two_term
#print axioms ResidueAsymptotic.dimH_residueConstSet_mm_asymp_two_term
#print axioms ResidueAsymptotic.tendsto_mul_dimH_residueConstSet_sub_half
#print axioms ResidueAsymptotic.tendsto_dimH_residue_ratio_eq_metalC
#print axioms ResidueAsymptotic.tendsto_dimH_eventuallyPeriodic_ratio_eq_psiFib
#print axioms ResidueAsymptotic.eventually_dimH_residueConstSet_strictAnti
#print axioms GeneralGrowingRec.PolyRecData.toGrowingRecData
#print axioms GeneralGrowingRec.GrowingRecData.grow_pow_div_Q_tendsto_zero
#print axioms GeneralGrowingRec.GrowingRecData.grow_nat_div_log_Q_tendsto_zero
#print axioms GeneralGrowingRec.GrowingRecData.grow_alpha_linear_relation
#print axioms GeneralGrowingRec.GrowingRecData.growKLRatio_eq_growLambda
#print axioms GeneralGrowingRec.GrowingRecData.growLambda_eq_zero_tfae
#print axioms GeneralGrowingRec.GrowingRecData.growLevelSet_zero_eq_lattice
#print axioms GeneralGrowingRec.GrowingRecData.grow_telescoping_digit_realize
#print axioms GeneralGrowingRec.GrowingRecData.grow_spectral_gap_open_interval
#print axioms GeneralGrowingRec.GrowingRecData.dimH_growLevelSet_nat_eq_zero
#print axioms GeneralGrowingRec.GrowingRecData.dimH_growFiniteSet_eq_zero
#print axioms GeneralGrowingRec.GrowingRecData.volume_growFiniteSet_eq_zero
#print axioms GeneralGrowingRec.GrowingRecData.ae_growLambda_eq_top
#print axioms GeneralGrowingRec.GrowingRecData.dimH_growInfiniteSet_eq_one
#print axioms GeneralGrowingRec.GrowingRecData.grow_range_lambda
#print axioms GeneralGrowingRec.GrowingRecData.growSignedExactLimitSet_coset_collapse
#print axioms GeneralGrowingRec.GrowingRecData.grow_three_way_gauge_splitting
#print axioms GeneralGrowingRec.GrowingRecData.grow_power_gauge_dichotomy
#print axioms GeneralGrowingRec.GrowingRecData.growExactLevel_power_gauge_dichotomy
#print axioms GeneralGrowingRec.GrowingRecData.growExactLevel_liminf_four_way
#print axioms GeneralGrowingRec.GrowingRecData.growUnsignedExactLimit_liminf_four_way
#print axioms GeneralGrowingDim.grow_Q_le_two_pow_mul_prod_A
#print axioms GeneralGrowingDim.grow_prod_A_le_Q_simple
#print axioms GeneralGrowingDim.dimH_growWeightedLevelSet_le
#print axioms GeneralGrowingDim.le_dimH_growWeightedExactLimitSet_zero
#print axioms GeneralGrowingDim.dimH_growWeightedLevelSet_eq
#print axioms GeneralGrowingDim.dimH_growWeightedExactLimitSet_zero_eq
#print axioms GeneralGrowingDim.growWeightedLevelSet_subset_lattice
#print axioms GeneralGrowingDim.dimH_growWeightedLevelSet_of_one_lt
#print axioms GeneralGrowingDim.growRatLattice_subset_weightedLevelSet
#print axioms GeneralGrowingDim.growRatLattice_ssubset_growLatticeL
#print axioms GeneralGrowingDim.growWeightedSeq_bounds_of_lattice_irrational
#print axioms GeneralGrowingDim.growWeightedLevelSet_eq_lattice_of_tendsto_zero
#print axioms GeneralGrowingDim.growWeightedLevelSet_eq_lattice_of_mul_gamma_lt_one
#print axioms GeneralGrowingDim.growWeightedLevelSet_eq_lattice_of_gamma_zero
#print axioms GeneralGrowingDim.growWeightedLevelSet_eq_ratLattice_of_limsup_top
#print axioms GeneralGrowingDim.growWeightedLevelSet_eq_ratLattice_of_one_lt_mul_gamma
#print axioms GeneralGrowingDim.growWeightedLevelSet_eq_ratLattice_of_gamma_top
#print axioms GeneralGrowingDim.growGammaSup_expGrowingRec
#print axioms GeneralGrowingDim.dimH_expGrowingRec_subcritical
#print axioms GeneralGrowingDim.expGrowingRec_supercritical
#print axioms GeneralGrowingDim.growGammaSup_doubleExpGrowingRec
#print axioms GeneralGrowingDim.dimH_doubleExpGrowingRec_subcritical
#print axioms GeneralGrowingDim.doubleExpGrowingRec_supercritical_lt_two
#print axioms GeneralGrowingDim.doubleExpGrowingRec_supercritical_gt_two
#print axioms GeneralGrowingDim.doubleExpGrowingRec_critical_two
#print axioms GeneralGrowingDim.growGammaSup_superDoubleExpGrowingRec
#print axioms GeneralGrowingDim.dimH_superDoubleExpGrowingRec_zero
#print axioms GeneralGrowingDim.dimH_superDoubleExpGrowingRec_pos_subcritical
#print axioms GeneralGrowingDim.superDoubleExpGrowingRec_supercritical

