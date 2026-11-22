# Frostman质量分布可复用模板挖掘记录
日期2026-11-21，只读核查，未运行Lean/lake构建，未改动既有文件。
来源：实读WeightedExactDim.lean全文1340行；Cylinder系4文件全文；design文档4-5节；mathlib grep实搜。
## 一句总判断（已验证）
WeightedExactDim.one_le_hausdorffMeasure_cantorSet（L928-1218）的覆盖反设加有限子覆盖加逐层计数加级数矛盾骨架，是窗口下界唯一可仿写的已验证Frostman模板。
其中thickening加纤维计数加Hs大于0提升三件与窗口无关可整体复用，而柱径、分支数、阈值三处须按柱集语言重写。mathlib无Frostman/质量分布/Moran引理（本次实搜零命中），该原理必须自建。
注：任务单写design文档5.1节P6，实读P1-P6表在5.3节（L257-266），5.1节是同构对照表无P编号，按实读为准。任务单称审计log有71条以上，本次未打开任何审计log，列为未核到。
## 表1引理链（全名加行号加前提结论一句话，本次实读，已验证）
T1 rpow_add_le_add_rpow（L86）：0≤a,b且0小于s≤1，则(a+b)的s次方≤a的s次方加b的s次方，直径分裂用。
T2 card_le_two_of_abs_sub_le_one（L382）：单射像中两两差绝对值≤1，则基数≤2，交叠上界的抽象组合核。
T3 intersect_cInterv_abs_sub_le_one（L355）：diamV≤1/Qj且w≤1/8、V交两同层区间，则中心指标差≤1，是T2的几何输入。
T4 card_CWord（L438）/wordCount_pos（L442）/wordCount_succ（L446）：词类型基数等于Mn、正性、递推M(n+1)=Mn乘b(J+n)，分支乘积记账。
T5 card_prefix_fiber_mul_aux（L540，private）到card_prefix_fiber_mul（L600）：前缀纤维基数乘Mn等于MN，跨层计数telescoping用。
T6 cInterv_prefix_subset（L469）/centerInt_injective（L486）：跨层区间嵌套、同层中心单射，均需w≤1/8加同级不交。
T7 cInterv_inter_cantorSet_nonempty（L630）：每词区间都交K，用extendZero补零延拓加紧区间套取交点，是覆盖计数的存在性来源。
T8 fact_mul_prod_add（L757）到wordCount_ge_fact_rpow（L772）：阶乘恒等式推出Mn≥((J+n-1)阶乘/(J-1)阶乘)的(1-β)次方，把分支乘积换成阶乘。
T9 exists_level_threshold（L795）：0小于s小于1-β，则存在N0使2/Mn≤(1/Q(J+n+1))的s次方，用Q≤7的j次方乘j阶乘加DimHFinite的tendsto_powB_div_factorial_rpow加28的m次方放缩，是计数与几何的阈值桥。
T10 ediam_thickening_le（L894）：ediam(thickening ρ A)≤ediam A加2倍ofReal ρ，开覆盖转直径控制。
T11 diam_thickening_pos（L910）：非空集ρ大于0膨胀后直径大于0，保证lvl分层良定。
T12 one_le_hausdorffMeasure_cantorSet（L928-1218）：0小于β小于1且0小于s小于1-β，则μH[s](K)≥1。
T12证明步骤：hausdorffMeasure_apply展开加反设级数和小于1（L938-949），thickening开膨胀，紧致有限子覆盖L981，按diam定层lvl（L1006-1044），字数覆盖得1≤求和2/M（L1049-1132），逐项2/M≤(diam)的s次方经T9（L1134-1142），求和小于1经T1加T10加几何级数（L1210-1217），矛盾。
T13 dimH_exactLimitSetα_ge（L1227，关键L1263-1292）：μH[s](K)非零经le_dimH_of_hausdorffMeasure_ne_zero得ofReal s≤dimH（L1264-1268），再by_contra加max中点技巧把任意s小于1-α提升为ofReal(1-α)≤dimH（L1276-1292）。
T14 dimH_exactLimitSetα_eq（L1297）/dimH_levelSetα_eq（L1309）/dimH_apprExponentα_eq_zero（L1325）：上界来自WeightedFinal.dimH_levelSetα_le加dimH_mono夹出等式，收尾件。
背景依赖（同文件实读）：exactLimitSetα（L16）；wWidth/cRad/cTheta/cCenter/cInterv/branchNum（L123-139）；childLeft/childRight/childInt（L188-226）；CWord/wordCount/centerInt/prefixWord（L433-458）；cantorLevel/cantorSet（L608-612）；extendZero（L624）；cantorSet_subset_exactLimitSetα（L675）。
## 表2通用件与专用件（已验证分类，通用指语句证明不提Qsel/wWidth/cTheta）
通用可整体复用：T1次可加；T2 card≤2抽象引理；T4-T5分支乘积纤维计数（branchNum只是参数b，aux已抽象为任意b）；T10-T11 thickening直径二条纯度量；T12骨架L938-949展开加反设、L981有限子覆盖、L1172-1217 tsum与有限和加几何级数；T13提升段L1263-1292。T5可原样复用，把窗口分支数代入参数b。
专用须重写：Qsel_le_seven_pow_mul_fact（L30）、four_mul_Qsel_le_succ（L55）；wWidth/cRad/cTheta定义与cRad_succ_le_quarter（L154）、childRight_sub_childLeft_ge（L195，用4jQ放缩得6j的1-β次方宽度）；cInterv_disjoint（L279）、distToNearestInt_cInterv_bound（L304）、abs_cTheta_sub_le（L330）、T3（均用区间几何1/Q加w≤1/8）；T8-T9（Q≤7的j次方乘j阶乘、28的m次方常数、tendsto_powB_div_factorial_rpow）；cantorSet_subset_exactLimitSetα（目标是apprSeq趋向c）。注意Lean模板交叠上界是2不是纸面17。
## 表3移植接口改写点（Cylinder侧现状本次实读，已验证；改写方案为推测）
M1测度定义：Weighted侧无显式测度对象，等分质量隐含在计数比card/MN与求和2/M中（L1049-1132）。Cylinder侧无测度无区间无质量，仅cfMat/cfProd/convPair代数件。方案推测：新建windowMass按互素对等分（纸面μ≤乘积c2逆乘i的负2γ次方），或沿用计数比写法避开测度论构造。
M2柱集直径：Weighted侧cRad等于w/Q加显式区间。Cylinder侧有代数芯无几何：sibling_cross（Mediant L39-42）、sibling_strict（Order L68-79）、consec_cross_abs等于1（Diameter L20-24）、childDen_ge_one（Diameter L27-30），但无柱区间定义、无长度公式。方案推测：新建cylInterv，用cfProd第一列作端点、col1_convPair作桥梁，直径引理用sibling_cross加det等于负1的len次方推出交叉差再除以分母乘积，替换cRad_succ_le_quarter与全部1/Q。
M3质量分配分支数：Weighted侧branchNum等于6j的1-β次方取整（L172下界5倍）。Cylinder侧convPair_cons等给出分母递推u_new等于m乘u加n乘v的代数件，但无分支计数，coprime_count_ge不存在（design R6已核实仅docstring命中）。方案推测：新建分支下界c2乘j的2γ次方≤新矩形互素对数（纸面新矩形与旧矩形不同），代入T5抽象参数b；T9改写为μ显式常数版对Hj负2s次方的比较。
M4交叠上界：Weighted侧T2加T3给出diamV≤1/Q则指标差≤1则基数≤2。Cylinder侧sibling_strict已给不同子柱交叉相乘不等（不交代数核），但无首次跨越则无前缀关系（纸面L2817-2820）与任意区间至多17柱。方案推测：用sibling_cross加childDen正性重证小直径则至多k柱；常数取2还是17取决于柱宽间距比，T12中2/M分子须同步改，这是T12骨架唯一须改数字处。
M5目标集归属：Weighted侧cantorSet_subset_exactLimitSetα（L675）逐点2j的负(β-α)次方估计。窗口侧无H/k/r定义（design R2单点阻塞最高风险）。方案推测：新建K包含于r_j≥ηlogj且k奇偶集合的归属引理，输入停止柱不变式；在D0接口落地前T12-T13只能对抽象K陈述。
## mathlib核查（已验证，2026-11-21实搜全Mathlib）Frostman零命中；Moran零命中；massDistribution仅1处无关注释ConvexSpace Defs L129点质量；Hausdorff维数API存在（HausdorffDimension.lean文件本次ls验证，dimH定义与引理签名沿design4.1节共识转引）。
## 无法核实项：审计log条数未打开未核到；WindowMobiusCount等条数与公理清单本次未逐条核不背书；表3方案为推测待D0接口落地证实。
