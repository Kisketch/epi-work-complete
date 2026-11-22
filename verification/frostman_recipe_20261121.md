# Frostman 建造手册：照抄 one_le_hausdorffMeasure_cantorSet（L928-1218）
日期 2026-11-21，只读实读 L928-1218（含 L1-120、L118-197、L430、L600-679、L795-929 辅助定位），未跑 lake build，未改动既有文件。
配套：verification/frostman_template_20261121.md 表1 T12 骨架；柱集仿写接口见该文表3（M1-M5）。
## 一句总判断（已验证）
L928-1218 是六段式：反设覆盖和小于1 → thickening 开膨胀 → 紧致有限子覆盖 → 按 diam 定层 lvl → 词数覆盖得 1 ≤ 求和(2/M) → 逐项 2/M ≤ diam的s次方 → 求和diam的s次方小于1矛盾。
有限子覆盖、thickening 直径、次可加 rpow、几何级数、ENNReal tsum 与有限和记账全部通用可抄；阈值数字、阶乘界、w≤1/8 专用，须按柱集重写。
## 1. 主定理完整假设清单（已验证，实读行号）
| # | 假设 | 类型 | 来源 |
|---|---|---|---|
| P0 | variable (α c β : ℝ)（L120）；variable (J : ℕ)（L430） | 构造参数（section 变量，本引理内不重复 binder） | 构造参数 |
| H1 | hβ : 0 < β（L928） | 显式假设 | 向 wWidth_antitone（L147）、childRight_sub（L195）、cInterv_prefix_subset、centerInt 单射、cInterv_inter 非空传递 |
| H2 | hβ1 : β < 1（L928） | 显式假设 | 向 wordCount_pos（L442）、branchNum_pos、exists_level_threshold（L795）、extendZero 传递 |
| H3 | hJ : 2 ≤ J（L928） | 显式假设 | 凡 by omega 的 1 ≤ J+n 正性都靠它 |
| H4 | hwJ : wWidth β J ≤ 1/8（L929） | 显式假设，窗口专用 | 唯一几何小宽度假设，经 wWidth_antitone 单调到 J+lvl i，向交叠上界传递（L1075-1076） |
| H5 | 隐式 s:ℝ + hs0 : 0 < s（L929） | 显式假设 | rpow 单调与分裂全用它作 0<s |
| H6 | hs : s < 1-β（L929） | 显式假设，窗口专用阈值 | 只用两处：exists_level_threshold（L795）阈值桥；h28s 中 s≤1 反证（L856-862） |
| D1 | hs1 : s ≤ 1（L931，by linarith） | 派生 | 由 H2+H6；喂给 rpow_add_le_add_rpow（L1167）的 s≤1 |
| E1 | N0,hN0_ge:1≤N0,hN0 := exists_level_threshold（L932） | 已证引理实例 | L795 引理；结论 ∀n≥N0, 2/Mn ≤ (1/Q(J+n+1))的s次方，计数↔几何阈值桥 |
| E2 | Qsel_pos、DimHCore.Qsel_ge_factorial（用 L1023-1025） | 外部已证引理 | lvl 存在性中 1/d<Q 下界链用 |
| E3 | wordCount_pos（L1051/1089） card_CWord（L1120） card_prefix_fiber_mul（L1107） | 外部或同文件已证（T4-T5） | 分支乘积记账；T5 对任意分支函数 b 抽象，通用可抄 |
| E4 | card_le_two_of_abs_sub_le_one（L382，用L1069-1071） centerInt_injective（L486） intersect_cInterv_abs_sub_le_one（L355，用L1077） | 同文件已证（T2+T3+T6） | 交叠上界核；T2 通用，T3 与单射证明窗口专用（w≤1/8+区间几何） |
| E5 | cInterv_prefix_subset（L469，用L1085） cInterv_inter_cantorSet_nonempty（L630，用L1057） isCompact_cantorSet（L618，用L981） | 同文件已证（T6+T7+紧性） | 跨层嵌套、每词区间交 K（覆盖存在性）、紧集 |
| E6 | ediam_thickening_le（L894，用L987/1150） diam_thickening_pos（L910，用L1004） | 同文件已证（T10-T11）纯度量通用 | 开膨胀直径控制 + 膨胀后直径大于0（lvl 良定） |
| E7 | rpow_add_le_add_rpow（L86，用L1167） | 同文件已证（T1）通用 | (a+b)的s次方 ≤ a的s次方+b的s次方，直径分裂用 |
| E8 | wWidth_antitone（L147，用L1076） Qsel_le_seven_pow_mul_fact（L30，用L817） DimHFinite.tendsto_powB_div_factorial_rpow（L802用） | 同文件或外部已证，窗口专用 | 阈值引理 L795 内部件（28的m次方放缩链）；仿写整块替换为柱集分支下界 |
## 2. 证明骨架分步（行号逐条，通=通用可抄，专=窗口专用须重写）
| 步 | 行 | 动作（Lean 写法照抄点） | 全名引理 | 通专 |
|---|---|---|---|---|
| S0 阈值 | L928-935 | hs1；obtain N0,hN0_ge,hN0 := exists_level_threshold；Qsel_pos 取 hQN0_pos；set r0R := 1/(2*Qsel(J+N0))；set r0 := ofReal r0R | exists_level_threshold（L795）；Qsel_pos；ENNReal.ofReal_pos | 专阈值形状（N0 定义、r0 取 1/2Q）按柱集直径重写；通：取阈值+定正半径动作 |
| S1 展开+反设 | L938-951 | rw hausdorffMeasure_apply；le_trans + le_iSup₂取r0；三层 le_iInf；by_contra hlt，push_neg；set S；hS_ne_top；hSR_lt 经 toReal_lt_toReal；set δ0 := (1-S.toReal)/2 | MeasureTheory.Measure.hausdorffMeasure_apply；le_iSup₂；le_iInf；ENNReal.toReal_lt_toReal（皆 Mathlib，共识未复跑） | 通：整段照抄，反设→S≠⊤→δ0 留空位 |
| S2 开膨胀 | L953-979 | ρ i := min (r0R/2) ((δ0/2的(i+1)次方)的(1/s)次方/2)；hρ_pos；h2ρ_le_r0（min_le_left）；h2ρ_rpow（min_le_right + rpow_le_rpow + rpow_mul + one_div_mul_cancel + rpow_one）；V i := thickening；hV_open；hV_cov 经 self_subset_thickening，族下标用 i:{i // (t i).Nonempty} | Real.rpow_pos_of_pos；Real.rpow_le_rpow；Real.rpow_mul；Real.rpow_one；Metric.isOpen_thickening；Metric.self_subset_thickening | 通：整段照抄；1/s 需 ne_of_gt hs0；ρ取min保证直径与级数两用 |
| S3 有限子覆盖 | L981-982 | obtain F,hFcov := (isCompact_cantorSet).elim_finite_subcover 开族 开性 hV_cov | IsCompact.elim_finite_subcover（Mathlib，共识签名见§4，未复跑）；isCompact_cantorSet（L618） | 通：三参形状照抄；柱集只换紧集K与开族V |
| S4 直径控制 | L984-1004 | hV_ediam_le：ediam_thickening_le + hdiam i + ofReal_mul改写 + gcongr + h2ρ_le_r0 + ofReal_add + ring；hV_bd 经 isBounded_iff_ediam_ne_top；hV_diam_le 经 toReal_mono + toReal_ofReal；hV_diam_pos 经 diam_thickening_pos | ediam_thickening_le（L894）；Metric.isBounded_iff_ediam_ne_top；ENNReal.toReal_mono；ENNReal.toReal_ofReal；diam_thickening_pos（L910） | 通推导链照抄；专：目标上界 1/Q 换柱集直径 |
| S5 定层lvl | L1006-1044 | hex_lvl：∃n, N0≤n ∧ 1/Q(J+n+1)<diam ∧ diam≤1/Q(J+n)；存在hex_m：factorial_tendsto_atTop + tendsto_natCast + eventually_gt_atTop 取M（L1014-1021）+ Qsel_ge_factorial（L1024-1026）+ div_lt_iff₀两次；m0 := Nat.find hex_m，hm0_gt（等N0则与hd_le矛盾 L1033-1037），取 m0-1（Nat.find_min）；choose lvl | factorial_tendsto_atTop；tendsto_natCast_atTop_atTop；eventually_gt_atTop；Nat.find_spec；Nat.find_min；div_lt_iff₀；DimHCore.Qsel_ge_factorial | 专：存在性链（Q≤7的j次方·j阶乘、Q≥阶乘）换柱集分母增速；通：Nat.find首穿层+回退一格模式 |
| S6a 词覆盖 | L1046-1059 | N := F.sup lvl；hN_ge 经 Finset.le_sup；hcover_words：每词 cInterv_inter_cantorSet_nonempty 取 x∈K（L1057），Set.mem_iUnion₂.mp (hFcov hxK) 落到某 i | Finset.le_sup；Finset.mem_biUnion；Set.mem_iUnion₂；cInterv_inter_cantorSet_nonempty（L630） | 通框架照抄；专：词↔区间交K换柱集版（extendZero补零法，柱集需停止柱不变式，见模板M5） |
| S6b 单i计数 | L1061-1114 | A_i := lvl层命中词filter；hAi_le ≤2 经 card_le_two + centerInt_injective + intersect_abs_sub_le_one（w单调L1075-1076 + hV_bd + hlvl_le）；hsub_fib 经 cInterv_prefix_subset 挂前缀（L1079-1088）；hcard_mul calc：card*h ≤ biUnion（card_le_card） ≤ Σcard*h（card_biUnion_le） = Σ（sum_mul） = Σ M_N（card_prefix_fiber_mul L1107） = A_i.card*M_N（sum_const） ≤ 2*M_N；cast + le_div_iff₀ 得 card ≤ 2*M_N/M | Finset.card_le_card；Finset.card_biUnion_le；Finset.sum_mul；Finset.sum_const；le_div_iff₀；card_le_two_of_abs_sub_le_one（L382）；centerInt_injective；intersect_cInterv_abs_sub_le_one（L355）；cInterv_prefix_subset；card_prefix_fiber_mul | 通：calc五段记账照抄（T5已对抽象分支函数通用）；专：常数2与几何输入T3（w≤1/8+区间形）按柱集交叠数改（2或17，在此一处同步改分子） |
| S6c 加总 | L1115-1132 | htotal：card_CWord + card_univ 写M_N为基数（L1120），card_le_card hcover_words + card_biUnion_le 得 M_N ≤ Σcard（L1121），cast + sum_le_sum hcard_i；hfactor 经 mul_sum 提M_N；le_of_mul_le_mul_left 消去得 1 ≤ Σ 2/M | card_CWord（L438）；Finset.card_univ；Finset.card_biUnion_le；Finset.sum_le_sum；Finset.mul_sum；le_of_mul_le_mul_left；wordCount_pos | 通：全抄；柱集分子分母同步换，Σ(k/M)形不变 |
| S7 逐项桥 | L1134-1142 | hsum_le_diam 经 sum_le_sum：h1 := hN0 (lvl i) (hlvl_ge i)；h2 经 Real.rpow_le_rpow + hlvl_gt + hs0 | exists_level_threshold实例hN0；Real.rpow_le_rpow | 专：左端形状由阈值引理定（柱集重写T9时同步换）；通：sum_le_sum逐项动作 |
| S8a 分裂 | L1143-1171 | hdiam_bound：ht_ne_top（hdiam + ofReal_lt_top）；hdiam_le_add（diam展开 + ediam_thickening_le + add_ne_top + toReal_mono + toReal_add/ofReal）；hpow_le 经 rpow_le_rpow + rpow_add_le_add_rpow（L1161-1167）；htoR_rpow 经 toReal_rpow；linarith [h2ρ_rpow] | ENNReal.add_ne_top；ENNReal.toReal_add；ENNReal.toReal_ofReal；ENNReal.toReal_mono；ENNReal.toReal_rpow；Real.rpow_le_rpow；rpow_add_le_add_rpow（L86）；Metric.diam_nonneg | 通：全抄（ht_ne_top先行、toReal_add改写、rpow分裂、toReal_rpow回合四件套） |
| S8b 有限vs级数 | L1172-1188 | hsum_t：G := F.image Subtype.val；hG_eq 经 sum_image（Subtype.ext单射）+ sum_congr + simp [i.2]消⨆守卫（L1179）；hleE 经 ENNReal.sum_le_tsum；每项≠⊤经 single_le_sum + hlt；toReal_sum + toReal_mono hS_ne_top hleE | Finset.sum_image；Finset.sum_congr；ENNReal.sum_le_tsum；Finset.single_le_sum；ENNReal.toReal_sum；ENNReal.toReal_mono | 通：全抄（image取下标集 + sum_image单射 + ⨆守卫simp + sum_le_tsum + toReal_sum四件套） |
| S8c 几何级数 | L1189-1209 | hsum_geom：同G + sum_image 改写 δ0/2的(n+1)次方 = δ0*((1/2)的(n+1)次方)（one_div/inv_pow/div_eq_mul_inv）；← mul_sum 提δ0；hgeom：Summable（summable_geometric_two改写pow_succ' + mul_left L1198-1202）+ sum_le_tsum + tsum=1（tsum_mul_left + tsum_geometric_two + norm_num L1204-1207）；nlinarith | summable_geometric_two；tsum_geometric_two；Summable.sum_le_tsum；tsum_mul_left；Finset.mul_sum；pow_succ'改写；one_div；inv_pow | 通：全抄；δ0系数与1/2公比是S2ρ设计的对偶，抄时两处同步 |
| S9 矛盾 | L1210-1218 | htotal_lt：sum_le_sum hdiam_bound → sum_add_distrib → add_le_add hsum_t hsum_geom → linarith（S.toReal+δ0<1）；末 linarith 与 hsum_ge_one + hsum_le_diam 矛盾 | Finset.sum_le_sum；Finset.sum_add_distrib；add_le_add | 通：全抄 |
## 3. 窗口专用 vs 通用对照（仿写 checklist）
通用照抄（语句证明不提 Qsel/wWidth/cTheta）：S1 反设四件套；S2 ρ/V 设计（含 Subtype 守卫）；S3 有限子覆盖三参；S4→S8a thickening直径链 + rpow 分裂；S8b tsum/有限和四件套；S8c 几何级数；S5 的 Nat.find 回退模式；S6b-c 的 calc 记账（含 T5 抽象分支函数）；T13 提升段（L1263-1292，见模板）。
窗口专用（柱集须重写，对应模板 M1-M5）：H4 w≤1/8 与 L1075-1076 单调传递；S0/S5 的 1/Q 直径标尺与 r0 取值。
窗口专用（续）：S5 存在性链（Q上界7的j次方乘j阶乘、Q下界阶乘、28的m次方、C0、tendsto_powB）；分支数 6j的(1-β)次方与 T8 阶乘下界。
窗口专用（续2）：交叠常数 2（纸面 17，Lean 取 2，改则 S6b 分子与 S6c/S7 同步改）；目标归属引理（柱集 M5 在 D0 落地前只能对抽象 K 陈述）。
数字改动唯一传导点（已验证）：交叠上界 hAi_le 的 2 → S6b 的 2*M_N → S6c 的 Σ2*M/M → hsum_ge_one 的 Σ2/M → S7 左端。
阈值引理结论形状 → S7 h1 左端。两处改动必同步，否则 S9 链断裂。
## 4. mathlib 全名索引（出现已验证实读，签名为共识未复跑）
紧性：IsCompact.elim_finite_subcover（S3）。共识签名：IsCompact s → (∀i, IsOpen (U i)) → (s ⊆ ⋃i, U i) → ∃F:Finset ι, s ⊆ ⋃i∈F, U i。
Hausdorff：MeasureTheory.Measure.hausdorffMeasure_apply（S1，iInf/iSup₂展开）。
比较：Finset.card_le_card；Finset.card_biUnion_le；Finset.sum_le_sum；Finset.single_le_sum。
求和记账：Finset.sum_image；Finset.mul_sum；Finset.sum_add_distrib；Finset.sum_congr；le_of_mul_le_mul_left。
级数：ENNReal.sum_le_tsum；ENNReal.toReal_sum；Summable.sum_le_tsum；tsum_mul_left；tsum_geometric_two；summable_geometric_two。
度量：Metric.isOpen_thickening；Metric.self_subset_thickening；Metric.isBounded_iff_ediam_ne_top；Metric.diam。
rpow：Real.rpow_pos_of_pos；Real.rpow_le_rpow；Real.rpow_mul；Real.rpow_one；ENNReal.toReal_rpow；ENNReal.toReal_add。
极小元与序：Nat.find_spec；Nat.find_min；div_lt_iff₀；ENNReal.toReal_mono；ENNReal.toReal_ofReal。
注：Frostman/质量分布/Moran 在 Mathlib 本次实搜零命中（见模板），须自建，无官方可抄引理。
## 5. 无法核实项
Mathlib 签名为标准库共识写法，本次只读未跑构建复核，仿写前以实测为准。
Cylinder 侧 M1-M5 改写方案为推测（模板表3），待 D0 接口落地证实。
Qsel_pos、Qsel_ge_factorial、wordCount_pos、tendsto_powB 的准确签名未逐条打开 DimHCore/DimHFinite，只核到用例行（L1023-1025、L802），列为未核到。
