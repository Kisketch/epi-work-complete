# 论文二现行版：纸面定理 ↔ Lean 声明 ↔ 审计证据 对位图（2026-11-21）

> 方法与交付格式同论文一：表列 `PaperLabel | 章节 | LeanDeclaration | 审计证据 | 状态 | 备注`。
> 只读分析，未改动任何其他文件。
> - 论文主（A稿现行版）：`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`（3346 行；定理类标签 26 个，编号环境 30 个含 4 条备注）
> - 伴随稿（B稿）：`paper1_e_plus_pi/02_companion_paper/Phase2_revised.tex`（仅记录差异项，不全量重做，见附录 B）
> - 审计证据：`verification/audit_takeover_merge_20261121.log`（420 条 = 349 旧 + 71 新；全文检索 `sorry` 零命中，即 `sorryAx = 0`）
> - 参考：`verification/paper2_audit_20261121.md`（旧 349 条审计，判定基线）、`verification/Takeover_合并与复核记录_20261121.md`
> - 规则：`AGENTS.md`（形式化纪律：自报 vs 已核实；引用纪律；事实基线）
> - 命名注意：文件 `EpiFormal/FiniteStateTail.lean` 使用命名空间 `FiniteStateGauge`（与文件名不一致），对位以声明全名为准；
>   另有小文件 `EpiFormal/FiniteStateGauge.lean`（同名命名空间，仅含游走恒等式与 Perron 尺度界），两者在表中明确区分。

## 审计日志统计（新 420 条，本次实测）

- `sorry` 全文检索：0 命中（`sorryAx = 0`）。
- paper2 相关条目公理签名：全部仅为 Lean 基础公理 `[propext, Classical.choice, Quot.sound]`，
  其中 `PolyRecData.poly_Q_eq_lincomb / poly_casorati` 与 `HermiteResiduePeriod.*` 6 条为更弱的 `[propext, Quot.sound]`；
  零白名单公理、零项目自加公理（白名单 22 条均属 paper1 Phase-1 遗留声明，与论文二无关）。
- 日志中 `GoldenOrbitRigidity / GoldenOrbitB2Rigidity / GeneralEndpointRigidity / CSpectrum / SignedClusters / DefectFibres / FactorialCriterion / Escape* / AdjacentWitness / ThresholdAttained / QuarterPoint*` 等条目属 paper1 黄金轨道与端点刚性理论，**不计入**论文二对位（避免误归属）。
  仅有的两条 `mobius_*` 命中（L129、L336）亦属 paper1 黄金轨道模，与论文二窗口 Möbius 计数无关——后者在日志中**零命中**。

## 主表：A稿全量对位（30 行 = 26 定理类标签 + 4 备注）

| PaperLabel | 章节 | LeanDeclaration | 审计证据 | 状态 | 备注 |
|---|---|---|---|---|---|
| `thm:class` 分类（$\{j‖Q_jx‖→0\}=L$） | §sec:class（tex L365） | `Classification.theorem2_classification` | 新日志 L56，基础三公理，无 sorry | 已核实 | KL 准则子列变体，论文自定位为文献复核型结果 |
| `thm:gap` 初始隙 1/4 | §sec:class（tex L378） | `Classification.corollary3_gap` | 新日志 L57，基础三公理 | 已核实 | 黑箱用 KL 只能得 1/16，1/4 为直接递推分析所得 |
| `thm:spectral` 初始隙二分 | §sec:spectrum（tex L402） | `SpectralGap.*` 5 条（`apprExponent_eq_zero_iff`、`spectral_gap`、`levelSet_below_eq_lattice`、`latticeL_countable`、`dimH_levelSet_below`） | 新日志 L86–90，基础三公理 | 已核实 | 与旧审计一致 |
| `rem:linear-indep`（$\Lam(B\pi)>0$ ⟺ $1,e,\pi$ 线性无关，开放） | §sec:spectrum（tex L417） | —（范围限定声明，无需形式化） | — | N/A（诚实声明） | 两稿均明示不解决 $e+\pi$ 无理性，符合事实基线 |
| `thm:full-spectrum` 全谱离散化 $=\frac14\Z_{\ge0}\cup\{\infty\}$ | §sec:spectrum（tex L432） | `FullSpectrumDiscrete.*`（`general_signed/abs_defect_approx`、`not_tendsto_open_interval_of_int_approx`、`eventually_le_of_int_approx_in_gap`、`eventually_eq_int_of_tendsto`、`euler_signed/abs_defect_approx`、`spectral_gap_open_interval`） | 新日志 L149–158，基础三公理 | 已核实 | 负搜索范围内无先例（检索覆盖见旧审计§二说明）≠已证无先例 |
| `thm:sub` 隙上水平集恒定 $E_c=E_{k/4}$ | §sec:spectrum（tex L473） | `FullSpectrumDiscrete.eventually_abs_defect_le_of_apprExponent_le`、`levelSet_eq_on_gap`（$c<1/4$ 另有 `SpectralGap.levelSet_below_eq_lattice`、`dimH_levelSet_below`） | 新日志 L159–162 + L88–90 | 已核实 | 与旧审计一致 |
| `lem:factorial` $Q_j\ge j!$ | §sec:finite-levels（tex L524） | `DimHCore.Qsel_ge_factorial` | 新日志 L91 | 已核实 | 初等 |
| `lem:branch` 一致分支界 $\lfloor16t\rfloor+1$ | §sec:finite-levels（tex L538） | `DimHCore.fiber_card_le`（另 `Qsel_succ_le`） | 新日志 L92–93 | 已核实 | 初等；加权版另有 `WeightedFiber.fiber_card_weighted_le`（L122） |
| `thm:finite` 有限水平集 $\dimH=0$ | §sec:finite-levels（tex L569） | `DimHFinite.dimH_levelSet_finite`（支撑链：`card_survSet_le`、`centerOf_mem_survSet`、`tailSet_cover`、`tendsto_contentBound`、`hausdorffMeasure_tailSet_zero`、`dimH_tailSet_zero`、`apprExponent_add_intCast`、`levelSet_subset_iUnion_tailSet`） | 新日志 L94–102 | 已核实 | 无需连续分数公理；区别于经典无加权零集（满维数） |
| `cor:infinite-level` $\{\Lam=\infty\}$ 满测度、局部维数 1 | §sec:finite-levels（tex L664） | `GaugeExact.*`（`dimH_finiteLevel_zero`、`volume_finiteLevel_zero`、`ae_apprExponent_eq_top`、`volume_infiniteLevel_Icc[_zero_one]`、`dimH_infiniteLevel_inter_Icc_zero_one`、`dimH_infiniteLevel_eq_one`） | 新日志 L194–200 | 已核实 | 初等测度论证 |
| `rem:unweighted`（$x_0$ 见证，$\Lam(x_0)=1/4$ 且 $x_0\notin L$） | §sec:weights（tex L746） | `QuarterPointFinal.lambda_x0_eq_quarter`（+`eps_bound`、`round_eq_M`、`defect_eventually_one`）与 `UnweightedCorrection.witness` | 新日志 L118–121 + L193 | 已核实 | 备注体裁但有核验声明，计入已核实 |
| `thm:upper` 加权上界 $\dimH\le1-\alpha$ | §sec:weights（tex L762） | `WeightedFinal.dimH_levelSetα_le`（经 `WeightedFiber`、`WeightedDimHCore`、`WeightedUpper` 组装） | 新日志 L122–125 | 已核实 | $0<\alpha<1$ 时 BLR Thm 7 条件 (1.6) 失效，经典质量传输不适用，独立覆盖证明 |
| `conj:weight` 次临界精确维数 $1-\alpha$（含处方极限） | §sec:weights（tex L870） | `WeightedExactDim.*` 5 条（`one_le_hausdorffMeasure_cantorSet`、`dimH_exactLimitSetα_ge/eq`、`dimH_levelSetα_eq`、`dimH_apprExponentα_eq_zero`） | 新日志 L144–148 | 已核实 | $α=0$ 另有 BLR Cor 8 旁证（本地已开核）；FWW 仅旁证 |
| `thm:gauge` 临界规范 $h_k$（正水平无限 σ-有限、严格子水平零） | §sec:gauge（tex L1105） | `GaugeNull.*` 3 条 + `GaugeExact.*`（$L$-平移不变、可数有限覆盖、Cantor 树下界、正性、无穷、非 σ-有限判据等）+ `GaugeCircle.*` 53 条（`critGauge`/`binaryGauge`/`interpGauge` 构造、`mono`、`continuous`、`at_inv_Qsel`、`eq_segVal`、R 与 `UnitAddCircle` 两套实例化） | 新日志 L190–192（GaugeNull）、L194–217（GaugeExact）、L238–328（GaugeCircle 53 条） | 已核实 | 区别于 CMMS（有限正测度）与 MEA（$k^{-1}(3)$ 恒零或非 σ-有限）；CMMS §5 Thm 3 未能开核，只采信论文转述为作者声称 |
| `cor:exact-gauge` $h_k$ 恰为临界规范（三条） | §sec:gauge（tex L1419） | (i) `GaugeCircle.mkMetric_critGauge_exactLevel_inter_Ioo_eq_top`（+ circle/arc 变体）；(ii) `GaugeNull.mkMetric_levelSet_null_of_subgauge` + `GaugeCircle.mkMetric_circleLevelSet_null_of_subgauge`；(iii) `GaugeCircle.mkMetric_critGauge_exactLevel_not_sigma_finite_of_ratio`（+ circle 变体）+ `GaugeExact.not_countable_union_finite_of_ratio_tendsto_zero` | 新日志 L190–192、L208、L251–301、L315–328 | 已核实 | 与旧审计一致 |
| `cor:liminf-gauges` 任意规范 $\rho_b(g)$ 三分法（含振荡规范） | §sec:gauge（tex L1464） | `GaugeLiminf.*` + `GaugeScaleComparison.*` 共 18 条（文件 `GaugeLiminfComplete.lean`）：`mkMetric_digitClass_le_liminf`、`mkMetric_binaryDigitClass_le_liminf`、`mkMetric_levelSet/unsignedExactLimit_null_of_liminf_zero`、两套 `countable_cover_of_liminf_lt_top`、`small_radius_le_of_adjacent_scale_le`、`not_countable_union_finite_of_adjacent_scale_ratio`、`exists_small_radius_comparison_of_lt_liminf`、`not_countable_union_finite_of_liminf_top`、`mkMetric_eq_top_of_liminf_pos`、`calibrated_exactLevel_eq_top`、`exactLevel_eq_top_of_liminf_pos`、`exactLevel_not_countable_union_finite_of_liminf_top`、`circleExactLevel/circleUnsignedExactLimit_liminf_trichotomy`、`liminf_normalizedGaugeCost_zero_of_smaller_base`、`mkMetric_circleStrictLevel_null_of_liminf_lt_top` | 新日志 L529–558，全部基础三公理 | **转正→已核实** | 旧审计为“作者自报，未复跑”（18 条不在旧日志中）；本次合并后实测在列。文件内另有未审计引理（如 `exists_small_radius_comparison_of_liminf_pos`），不计入审计证据 |
| `rem:gauge-scale` 水平分离与无插值对数尺度 | §sec:gauge（tex L1527） | `GaugeCircle.critGauge_ge_one`、`critGauge_eq_segVal`、`critGauge_adjacent_ratio_tendsto_zero`、`critGauge_adjacent_level_separation` | 新日志 L276–284 | 已核实 | 备注体裁但有核验声明 |
| `thm:trichotomy` 正水平三分裂（(i) limsup 基 $2k+1$；(ii) 无符号精确极限普适基 2；(iii) 有符号精确极限单 $L$-陪集） | §sec:gauge（tex L1563） | (i) `FullSpectrumDiscrete` 数字刻画 + `GaugeCircle` limsup 规范群；(ii) `FullSpectrumDiscrete.unsigned_exact_limit_iff_defect_binary` + `GaugeCircle` binary-gauge 群（`…_unsignedExactLimit_pos/inter_Ioo_eq_top/eq_top/sigma_finite_cover`、`critGauge_circleUnsignedExactLimit_null`、$g_\beta$ 阈值二分 4 条）；(iii) `TrichotomyAndPolyExtension` 8 条（`xPlus_mem_signedExactLimitSet`、`neg_xPlus_mem_signedExactLimitSet`、`add_latticeL_mem_signedExactLimitSet`、`signedExactLimitSet_pos/neg_eq_coset`、`signedExactLimitSet_zero_eq_latticeL`、`signedExactLimitSet_empty_of_not_quarter_int`、`trichotomy_part_iii_complete`） | 新日志 L161–167（数字刻画）、L257–328（二元规范群）、L361–376（8 条 coset 坍缩） | 已核实 | 基 2 不依赖 $k$ 为本文核心观察之一；旧审计已为已核实，本次保持 |
| `thm:finite-state-tail` 有限状态缺陷尾（Perron 根规范分类） | §sec:finite-state-tail（tex L1744） | 已审计骨架：文件 `FiniteStateGauge.lean` 的 `FiniteStateGauge.walkMass_of_eigenvector`、`walkCount_bounds` ＋文件 `FiniteStateTail.lean`（命名空间 `FiniteStateGauge`）的 `card_path_eq_walkMass`、`mkMetric_fixedTail_le`、`mkMetric_eventualTail_null`、`eventualTail_countable_cover_finite`、`fixedTail_finite_of_root_one`、`eventualTail_countable_of_root_one`、`mkMetric_circle_fixedTail_le`、`exists_marked_edge_with_return`、`frequently_defectShift_eq_level`、`exactTail_empty_of_no_marked_return`、`exists_component_suffix`、`exactTail_eq_iUnion_marked_components`、`exactTail_countable_of_marked_roots_one`、`mkMetric_exactTail_null_of_dominant_liminf_zero`；**缺**：$\lambda_*>1$ 时正临界测度下界（`exactTail_pos / eq_top / sigma_finite_cover` 类声明在日志中零命中， ઉપરોक्त否定检索已确认）与局部无穷/非 σ-有限组装 | 新日志 L559–560 + L583–598；正测度下界否定检索（`exactTail_pos|…eq_top|…sigma…`）零命中 | **仍纸面**（骨架部分已核实，下界缺失） | 以 $S_k(G)$ 代全字母的推广；MW 图定向结果作对比引用（MW 未开核）。`FiniteStateGauge.lean` 另有 `walkMass_mono`、`walkMass_smul` 未进审计，不计入证据 |
| `lem:poly-growth` 一般 $(cj^r+d)$ 增长与非渐近阶乘界 | §sec:poly-rec（tex L1903） | `TrichotomyAndPolyExtension.PolyRecData.poly_Q_ge_factorial`、`poly_pow_div_Q_tendsto_zero` | 新日志 L377–380 | 已核实 | 新的一般框架 |
| `lem:poly-lattice` 内蕴秩 2 格与 Casorati 刚性 | §sec:poly-rec（tex L1949） | `PolyRecData.poly_Q_eq_lincomb`、`poly_casorati`（此二条为 `[propext, Quot.sound]`）、`alphaU/alphaV_error_bound`、`poly_alpha_linear_relation`、`theta_irrational`、`poly_dist_le_of_mem_latticePoly`、`polyWeightedExponent_eq_zero_of_mem_latticePoly`、`polyApprExponent_eq_zero_tfae/iff_mem_latticePoly/iff_defect_zero` | 新日志 L381–403 | 已核实 | 同上 |
| `thm:general-rec` 全谱 $\frac1c\Z_{\ge0}\cup\{\infty\}$ | §sec:poly-rec（tex L2028） | `PolyRecData.poly_signed/abs_defect_approx`、`poly_jr_mul_eps_tendsto_of_defect_const`、`polyApprExponent_xPlusPoly`、`poly_spectral_gap_open_interval`、`poly_levelSet_eq_on_gap`、`poly_levelSet_below_eq_lattice`、`poly_range_apprExponent` | 新日志 L404–422 + L473–475 | 已核实 | $r=1$ 特化另见 `FullSpectrumDiscrete` |
| `thm:poly-gauge-trichotomy` 一般递推临界规范与三分裂 | §sec:poly-rec（tex L2087） | (i) `PolyGaugeAndPhaseTransition.mkMetric_polyCritGauge_polyStrictLevel_null`、`polyExactLevel_critGauge_sigma_finite`、`mkMetric_polyCritGauge_polyExactLevel_inter_open_eq_top`、circle 三件套（`…_polyCircleStrictLevel_null`、`…_polyCircleExactLevel_inter_open_eq_top`、`polyCircleExactLevel_critGauge_sigma_finite`）；(ii) `poly_unsigned_exact_limit_iff_defect_binary`、`poly_unsigned_exact_limit_empty_of_not_div_c`、`mkMetric_polyUnsignedExactLimit_null_of_critGauge`、`polyUnsignedExactLimit_binaryGauge_sigma_finite`、`mkMetric_polyBinaryGauge_unsignedExactLimit_inter_open_eq_top`、circle 三件套；(iii) `PolyRecData.poly_signed_exact_limit_iff_defect_const`、`xPlusPoly/neg_xPlusPoly_mem_signedExactLimitSet`、`poly_sub_mem_latticePoly_of_same_signed_limit`、`poly_add_latticePoly_mem_signedExactLimitSet`、`poly_trichotomy_part_iii_complete` | 新日志 (i)(ii)+circle：L480–521；(iii)：L425–442 | **(i)(ii)转正→已核实**；(iii)保持已核实 | 旧审计中 (i)(ii) 为纸面（A稿诚实标注）；本次 71 条新增覆盖其全部三结论（零性/σ-有限/开集无穷）及 circle 版本 |
| `cor:poly-exact-gauge` 一般递推精确临界规范 | §sec:poly-rec（tex L2190） | `PolyGaugeAndPhaseTransition.polyExactLevel_power_gauge_dichotomy`、`polyExactLevel_liminf_four_way`、`polyUnsignedExactLimit_liminf_four_way`、`mkMetric_polyLevelSet_null_of_liminf_zero`、`polyExactLevel_fast_gauge_null`、`polyExactLevel_slow_gauge_non_sigma_finite` | 新日志 L522–528 + L561–567 | **转正→已核实** | 含 $1/r$ 对数尺度（下条备注） |
| `rem:poly-gauge-scale` 内插无关对数尺度与 $1/r$ 因子 | §sec:poly-rec（tex L2208） | `PolyGaugeAndPhaseTransition.poly_log_Q_asymptotic`、`polyInterpGauge_log_scale_tendsto` | 新日志 L476–479 | **转正→已核实** | 备注体裁但本次有核验声明 |
| `thm:poly-phase-transition` 临界维数 0 / 次临界 $1-\alpha/r$ / 超临界坍缩 | §sec:poly-rec（tex L2224） | (i) `PolyRecData.poly_dimH_levelSet_finite`、`poly_dimH_finiteLevel_zero`、`poly_volume_finiteLevel_zero`、`poly_ae_apprExponent_eq_top`、`poly_volume_infiniteLevel_Icc`、`poly_dimH_infiniteLevel_inter_Icc_eq_one`、`poly_dimH_infiniteLevel_eq_one`；(ii) `PolyWeightedUpper.dimH_polyWeightedExponent_le`（上界）＋`PolyWeightedLower.exists_lower_growth`、`exists_level_threshold`、`one_le_hausdorffMeasure_cantorSet`、`dimH_polyExactLimit_ge/eq`、`dimH_polyWeightedSublevel_eq`（下界与等式；另 `polyZeroWeightSublevel_eq_univ`、`polyExactLimit_zero_eq_empty` 处理 $\alpha=0$ 端点）；(iii) `PolyRecData.poly_supercritical_levelSet_eq_lattice`、`poly_supercritical_dimH_zero`、`poly_supercritical_empty_neg` | 新日志 (i)：L452–472；(iii)：L443–451；**(ii)：L568（上界）+ L575–582（下界 8 条）** | **(ii)转正→已核实**；（i)(iii)保持已核实 | 旧审计中 (ii) 为纸面 + mpmath 旁证（400/50 位）；本次上下界均有审计声明，mpmath 降为旁证。`PolyWeightedLower.lean` 内大量构造引理（`wWidth/cRad/branchNum/card_CWord/…`）未进审计，不计入证据 |
| `thm:windows` Hermite 窗口（宇称维数 1、有界增量维数 1/2） | §sec:windows-residues（tex L2404） | — 无直接维数结论声明；邻近支撑仅 `WindowAndResidueCore` 跨越界（`thm18_*`、`thm20_*`，名义上归属后两定理证明） | 新日志中 `window/pressure/ergodic/frequency/parity_full/Möbius计数/zeta` 等检索零命中（仅 paper1 黄金轨道 `mobius_*` 两条误检，已排除，L129/L336） | **仍纸面** | 与 FLLW 相关谱并列（FLLW 未开核）；完整遍历性与压力论证为纸面证明 |
| `thm:short-ae` 短窗口对数频率 | §sec:windows-residues（tex L2610） | 头部已核实：`WindowAndResidueCore.thm19_cond_prob_integral_identity`、`thm19_cond_prob_lower_bound`、`thm19_exp_moment_step_le`；**尾部无**：tower 迭代 + Markov + 并列 dyadic + Borel–Cantelli 组装在日志中零命中（`tower/Tower/Borel/cantelli` 检索零命中） | 新日志 L223–225；尾部否定检索零命中 | **仍纸面**（头部三步已核实，尾部组装纸面） | 新的停时柱鞅论证 |
| `thm:no-short-dim` 发散窗口满维数 $1-\eta\log\varphi$ | §sec:windows-residues（tex L2733） | 头部已核实：`WindowAndResidueCore.thm18_terminal_denom_bounds`、`thm18_append_four_crosses`、`thm18_prescribed_count_crossing`、`thm20_rational_between_two_and_three`、`thm20_terminal_denom_bounds`；**缺**：Möbius 计数完整组装、质量分布下界、$\zeta(2t)$ 上界求和 | 新日志 L220–222 + L226–227；`zeta/Zeta/mobius/Mobius`（除 paper1 误检外）零命中 | **仍纸面** | 同上 |
| `thm:residues` 模 4 最终周期维数 $=\dimH F$，$357/512<\dimH F<359/512$ | §sec:windows-residues（tex L2853） | 核心 6 条：`WindowAndResidueCore.thm21_shift_mod4_mem_alphabet`、`thm21_tail_distance_ratio_identity/le`、`thm21_prefix_factor_bounds`、`thm21_integer_certificate_power_enclosure`、`thm21_transfer_operator_sub_super_iteration` ＋周期 6 条：`HermiteResiduePeriod.state_eq_selected`、`selected_period`、`state_period_3/4/5/6`（`[propext, Quot.sound]`；`period_of_return` 未进审计）＋**严格整数证书已复跑**：`residue_certificate.py`（本轮独立复跑 EXIT 0，下边际 +0.002922128、上边际 +0.006596281，区间宽 $1/256$） | 新日志 L228–237 + L569–574；证书脚本留痕见旧审计§八 | **仍纸面**（核心引理＋证书已核实，Bowen 压力公式组装为纸面） | CLU transfer（Prop 2.7 方向正确，Table 1 上界 0.743586 已开核）＋ Bowen 压力公式（CLU §2 Thm 2.3 已开核，细微差别见旧审计§三：严格引文应为“Thm 2.3 经由 Prop 2.2 的零点读法”，轻微注记非错误） |

## 计数结论

- 编号环境 30 个，其中备注 4 条（`rem:linear-indep` 为范围限定 N/A；`rem:unweighted`、`rem:gauge-scale`、`rem:poly-gauge-scale` 均有核验声明，计入已核实）。
- 定理类标签 26 个，按 (i)(ii)(iii) 拆分子项计 32 项：
  **已核实 27 子项（21 个整标签）**；**仍纸面 5 子项（5 个整标签）**：
  `thm:finite-state-tail`（整体；骨架部分已核实）、`thm:windows`、`thm:short-ae`、`thm:no-short-dim`、`thm:residues`
  （后四者均为“部分核心引理已核实＋主体论证纸面”；`thm:residues` 另有严格整数证书已复跑）。
- 类别（AGENTS.md §2）：上表已核实条目均为**无条件新结果（1）或文献核查与复现（5）**；
  仍纸面 5 项同属类别 1，但其 Lean 覆盖缺失，投稿口径须维持“纸面证明（＋证书/旁证）”，禁称机器验证。
- 它没做到（重申，与旧审计§六一致）：$e+\pi$（及 $e\pi$、$e-\pi$ 等）无理性/超越性**毫无推进**，两稿书面承认；
  B 稿频率 machinery 独立复核缺失；CMMS/FLLW/KL 原文等未开核引文只作“作者声称”。

## 附录 A：本次 5 个曾纸面条目逐项复核结论（核心价值）

| 条目（旧审计结论） | 新 420 条日志复核 | 结论 |
|---|---|---|
| `poly-gauge-trichotomy` (i)(ii)（旧：纸面＋mpmath 旁证） | `PolyGaugeAndPhaseTransition` 新增约 20 条在列：(ii) 数字刻画 L480–485；(i) 零性 L486–488、σ-有限 L489–491、开集无穷 L498–500、circle 版 L504–512；(ii) 对应二元规范四件套 L492–521；另 `liminf_four_way` L525–528 | **转正→已核实** |
| `cor:poly-exact-gauge`＋`rem:poly-gauge-scale`（旧：纸面） | `polyExactLevel_power_gauge_dichotomy` L522–524、`mkMetric_polyLevelSet_null_of_liminf_zero` L561–563、`polyExactLevel_fast/slow_gauge_*` L564–567、`poly_log_Q_asymptotic` L476、`polyInterpGauge_log_scale_tendsto` L477–479 | **转正→已核实** |
| `finite-state-tail` 下界（旧：仅加权游走恒等式与 Perron 尺度界在 `FiniteStateGauge.lean`，整体纸面） | 新增 `FiniteStateTail.lean`（命名空间 `FiniteStateGauge`）16 条在列 L583–598：覆盖/可数/分支分解/零性；但**正测度下界**（`exactTail` 的 `pos / eq_top / sigma_finite_cover`、局部无穷）否定检索零命中 | **仍纸面**（骨架转正、下界缺失） |
| `windows` 全链（旧：14 核心引理已核实＋遍历性/压力纸面） | 新日志无新增窗口维数声明；`SharpWindow / pressure / ergodic / frequency / zeta / Möbius计数` 全文检索零命中（仅 paper1 黄金轨道误检 2 条） | **仍纸面** |
| `short-ae` 尾部（旧：条件概率一步不等式与指数矩步已核实） | 头部 `thm19_*` 3 条仍在 L223–225；`tower / Borel / cantelli / dyadic` 组装检索零命中 | **仍纸面**（头部保持已核实，尾部缺失） |

附加转正（不在上述 5 项内但同等重要）：
`cor:liminf-gauges`（18 条 L529–558）与 `poly-phase-transition` (ii)（上界 L568＋下界 L575–582）亦由“作者自报/纸面＋旁证”转为**已核实**。
论文 tex `sec:verification`（L3279–3288）仍把 poly (i)(ii)/cor/scale/(ii)、finite-state-tail、windows 全链写作“未机器验证”——
以**本次 420 条实测为准**，其中 poly 部分已过时（转正），finite-state-tail 下界与 windows 全链表述仍然准确；
投稿前建议按此对位图更新该段措辞（本任务只读，不改动）。

## 附录 B：伴随稿（B稿 `Phase2_revised.tex`）差异项（仅记录，不重做全量对位）

| B稿独有项 | 章节 | Lean 状态（新日志实测） | 备注 |
|---|---|---|---|
| `thm:finite-state-quant` 定量规范界；`cor:finite-state-nondet` 非确定图算法 | B§sec:finite-state（tex L1924、L1967） | 纸面（B稿自述 “have paper proofs”） | A稿现行版已删除 |
| 频率/压力/循环/立方根 machinery 约 20 个环境：`thm:pressure-frequency`（L2027）、`cor:full-alphabet-frequency`（L2163）、`thm:edge-frequency-circulation`（L2217）、`thm:frequency-endpoints`（L2300）、`cor:variational-frequency-rate`（L2396）、`cor:reducible-frequency-rates`（L2414）、`thm:frequency-strip`（L2469）、`cor:half-strip`（L2533）、`cor:sublinear-speed`（L2557）、`thm:frequency-upper-class`（L2600）、`prop:markov-discrepancy-variance`（L2680）、`thm:markov-upper-class`（L2742）、`lem:tilted-clt`（L2877）、`thm:cubic-root-threshold`（L2914）、`cor:off-perron-one-sided`（L3052）、`lem:sharp-moving-strip`（L3098）、`thm:sharp-cubic-amplitude`（L3227） | B§各频率子节 | 纸面（B稿自述 “These frequency results have paper proofs” / “are paper proofs”）；`SharpWindow.lean` 仅 3 条代数引理且**不在** 420 条日志中（`SharpWindow` 检索零命中） | A稿现行版已删除；B稿须清理新旧两种口径并存问题（旧审计§五.2） |
| B稿摘要“一般多项式递推临界规范结论＋次临界维数上下界均已机器验证” | B§摘要 L99–106 | 该措辞所涉模块当时不在旧日志中；**本次合并后**对应声明（`PolyGaugeAndPhaseTransition`、`PolyWeightedUpper/Lower`）已在新日志实测在列——但此为 A 稿合并后状态，B 稿摘要仍须按 A 稿口径（tex L104–111 诚实标注纸面＋旁证）同步修正，见旧审计§五.1 | 摘要措辞问题，与合并无关；投稿以 A 稿口径为准 |

## 附录 C：下轮最值得补进 Lean 的前 5 条（价值×可行性排序）

1. **`thm:short-ae` 尾部组装**（tower 迭代 → Markov → 并列 dyadic → Borel–Cantelli，得 $c\log J$）：价值高（唯一的 a.e. 频率定理，补上即整定理转正）×可行性最高（标准概率组装，短，与现有 `thm19_*` 三步直接衔接）。
2. **`thm:finite-state-tail` 正测度下界**（$\lambda_*>1$ 时 $\mathcal H^{h_\lambda}(S_k(G))>0$＋局部无穷＋非 σ-有限）：价值最高（补全规范三分法全家最后缺口）×可行性中高（`GaugeCircle` 质量分布＋Haar 唯一性模板可直接移植，Perron 向量与柱估计已有 `walkMass/walkCount/card_path` 支撑）。
3. **`thm:windows` 下界组装**（Möbius 互素计数 $\gg R^2$＋质量分布得 $\dimH\ge1$ / $\ge1/2$）：价值高（窗口定理是全文最长证明之一）×可行性中（计数＋Frostman 模板在 `WeightedExactDim` 下界已有先例）。
4. **`thm:no-short-dim` 收尾**（上界 $\zeta(2t)$ 求和得 $\dimH\le1/2$＋下界 $\gamma=1-\eta\log\varphi$ 组装）：价值中高×可行性高（初等覆盖，与 `thm:finite` 的 `tendsto_pow_div_factorial` 路数同构）。
5. **`thm:residues` Bowen/压力组装**（转移算子次/超迭代 → 压力零点 $=$ 维数 → $\dimH E=\dimH F$＋区间）：价值高（旗舰数值结果）×可行性中低（需压力单调性＋CLU 接口形式化，证书已复跑可先行）；排第 5 仅因工程量最大。

## 留痕

- 否定检索均在 `audit_takeover_merge_20261121.log` 全文执行并记录范围：`SharpWindow|TraceMarkov|…|zeta|tilted` 仅命中 paper1 误检 2 条；`exactTail_pos|…eq_top|…sigma…` 零命中；`sorry` 零命中。
- Lean 文件只读 grep 确认命名空间：`FiniteStateTail.lean:9 namespace FiniteStateGauge`；`GaugeLiminfComplete.lean` 内 `GaugeLiminf`（L8）与 `GaugeScaleComparison`（L142/L207）双命名空间；
  `FiniteStateGauge.lean:10 namespace FiniteStateGauge`（小文件，审计仅收录其中 2/4 条）；
  `PolyGaugeAndPhaseTransition.lean:43 namespace PolyGaugeAndPhaseTransition`；
  `HermiteResiduePeriod.lean:7 namespace HermiteResiduePeriod`（`period_of_return` 未进审计）。
- 未运行任何 `lake build`（遵守约束）；所有“已核实”结论以既有 420 条 `#print axioms` 日志＋`Takeover_合并与复核记录`的“串行构建全绿（9108 jobs，EXIT 0）”为据，属复用既有实测证据，非新跑构建。
