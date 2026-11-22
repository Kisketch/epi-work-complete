# 论文一主稿：纸面定理 ↔ Lean 声明 ↔ 审计证据 全量对位图（2026-11-21）

> **一句总判断**：96 个有标签的定理型断言中，8 条已核实（仅 Lean 基础公理）、12 条相对项目自加公理成立、55 条为纯纸面证明、17 条依赖外部黑箱（经典定理或未证预印本/猜想）、4 条为作者自报但本日志无对应（待补）；无 sorry；$e+\pi$ 无理性仍开放（稿件自承，事实基线不变）。

## 方法与证据基线

- 纸面来源：`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex`（定理号取自同目录 `.aux` 的 `\newlabel`，权威；附录 A/B 即第 8/9 章）。
- 审计证据：`verification/audit_takeover_merge_20261121.log`（`Audit.lean` 共 420 条 `#print axioms`，`sorryAx` = 0；本表“行 N”指该日志文件行号）。
- 解析说明：正文审计 `paper1_audit_20261121.md`（旧 349 条）+ `Takeover_合并与复核记录_20261121.md`（新增 71 条，全基础公理）为交叉依据；正则解析命中 419 条，差 1 条为 `proposition_H'`（日志行 20，名字含单引号致正则漏配，非缺失）。
- 公理层级：Lean 基础公理 = `propext, Classical.choice, Quot.sound`；项目自加公理 = `e_transcendental, pi_transcendental`（`EpiFormal/Axioms.lean`）+ `mu_e_eq_two`（`EpiFormal/Measure.lean`，即 $\irr(e)=2$）。
- 状态定义：**已核实** = 日志有同义对应且仅基础公理；**依赖项目自加公理** = 有对应但依赖上述 3 公理之一（结论为相对的）；**纸面证明** = tex 证明完整、无完整 Lean 对应、不依赖未证猜想；**依赖黑箱** = 依赖外部经典定理/预印本/猜想（未核到原文）；**自报待补** = tex 声称 machine-verified/kernel-checked 但本日志无对应。备注内 `[1]–[5]` 为 `AGENTS.md` 诚实分类号。
- 命名惯例差异经人工确认：纸面 `lem:f2-spacing/count/blocksum` ↔ Lean `circle_spacing/dyadic_block_count/block_sum_bound`（源码注释 Lemma 9.11–9.13 对应）；`prop:rational-span`（P1 格点约化）↔ `EscapeReduction.reduction_to_lattice/P1_imp_irrational`（名-内容一致）；其余名称 suggestive 但未经逐式确认的一律填 `—`、不作对应（见备注）。

## 计数

- 有标签定理/命题/推论/引理：**96**（另有 3 个无标签定理型环境，见表后附注；problem/def/remark 不计入）。
- 已核实 **8**｜依赖项目自加公理 **12**｜纸面证明 **55**｜依赖黑箱 **17**｜自报待补 **4**。

## 对位表

| PaperLabel | 章节 | LeanDeclaration | 审计证据 | 状态 | 备注 |
|---|---|---|---|---|---|
| `thm:HL` | §2 Thm 2.4 | — | 不在日志 | 依赖黑箱 | [5] 经典黑箱；Lean 侧对应公理 `e/pi_transcendental`（项目自加，非证明） |
| `thm:LW` | §2 Thm 2.5 | — | 不在日志 | 依赖黑箱 | [5] 经典黑箱，仅陈述 |
| `thm:GS` | §2 Thm 2.6 | — | 不在日志 | 依赖黑箱 | [5] 用于 `thm:epi` |
| `thm:schneider` | §2 Thm 2.7 | — | 不在日志 | 依赖黑箱 | [5] 经 Duke 讲稿转引，仅注记背景 |
| `thm:vieta` | §2 Thm 2.9 | `at_least_one_transcendental`（+`vieta_identity`、`quadratic_roots_algebraic`） | 行1–3 | 依赖项目自加公理 | [5] 初等复述；base 步骤已核实，顶层相对 `e_transcendental` |
| `thm:four` | §2 Thm 2.11 | `four_numbers_at_most_one_rational` | 行4–7 | 依赖项目自加公理 | [5] 六对排除；相对 `e/pi_transcendental` |
| `thm:epi` | §2 Thm 2.12 | — | 不在日志 | 依赖黑箱 | [5] GS 标准应用，纸面有效 |
| `thm:fourier` | §2 Thm 2.14 | — | 不在日志 | 依赖黑箱 | [5] 技术基线陈述，引 Conrad |
| `thm:niven` | §2 Thm 2.15 | — | 不在日志 | 依赖黑箱 | [5] 同上 |
| `prop:dirichlet-divisor` | §3 Thm 3.1 | — | 不在日志 | 自报待补 | [1] 纸面证明已通读；tex 注称 `DVerify.prop_8_1`/`dirichlet_witness` kernel-checked，但本日志无 `DVerify` 条目 |
| `prop:two-window` | §3 Thm 3.2 | — | 不在日志 | 纸面证明 | [1] 行列式估计；17 双窗口枚举为计算佐证（作者自报） |
| `prop:signed-round` | §3 Thm 3.3 | — | 不在日志 | 纸面证明 | [1] π 侧无穷奇偶一致开放（稿件自承） |
| `thm:explicit-period` | §3 Thm 3.5 | `HermiteResiduePeriod.selected_period`、`state_period_3/4/5/6` 等（部分：$P_j,Q_j\bmod T$ 周期片段） | 行570–575 | 纸面证明 | [1] 完整窗口周期组装为纸面；`RoundTwoD.irrational_of_parity_agreements` 本日志无对应（自报） |
| `thm:digit-shift` | §3 Thm 3.6 | — | 不在日志 | 纸面证明 | [1] 上定理的幺模基变换细化 |
| `cor:digit-statistics` | §3 Thm 3.7 | — | 不在日志 | 纸面证明 | [1] 主定理推论 |
| `thm:gcd-converse` | §3 Thm 3.8 | — | 不在日志 | 纸面证明 | [1] 核心分类，三条件等价；$1/3$ 非最优（稿件自承） |
| `cor:recover-slope` | §3 Thm 3.9 | — | 不在日志 | 纸面证明 | [1] 上定理推论；用于 π 需未获输入（稿件自承） |
| `thm:affine-window` | §3 Thm 3.10 | `HermiteResiduePeriod.*`（部分：偶模数 $T$ 移位同余片段） | 行570–575 | 纸面证明 | [1] 完整分类纸面；Lean 仅同余片段 |
| `cor:affine-single` | §3 Thm 3.11 | — | 不在日志 | 纸面证明 | [1] 五窗 sharp 刻画，有反例构造 |
| `prop:rational-gcd-valuations` | §3 Thm 3.12 | — | 不在日志 | 纸面证明 | [1] 赋值计算引理 |
| `cor:bounded-digit-block` | §4 Thm 4.1 | — | 不在日志 | 纸面证明 | [1] Fibonacci 生长 + 窗口界 |
| `cor:golden-bound` | §4 Thm 4.2 | —（支撑件见 `lem:norm-parity-rigidity` 行） | 不在日志 | 纸面证明 | [1] 后续精确值的粗界；完整推论纸面组装 |
| `lem:norm-parity-rigidity` | §4 Thm 4.3 | `GoldenOrbitRigidity.norm_parity_rigidity_identity/eq_iff/ge_second` 等 | 行130–135 | 已核实 | [1] 全部仅基础公理；后续分类的算术基础 |
| `thm:golden-exact-second` | §4 Thm 4.4 | `GoldenOrbitRigidity.mobius_error_identity` + `case1/case2_*_quadratic_ge` + `second_limit_point_attained_value`（核心代数/分离/下界件） | 行129，138–142 | 纸面证明 | [1] 核心件已核实（base）；Case 组装 + 完整 $\liminf$ 为纸面；Bugeaud (3.4) 为公式来源 |
| `cor:golden-exact-e` | §4 Thm 4.5 | —（支撑见上行） | 不在日志 | 纸面证明 | [1] 已知连分数直接应用 |
| `lem:pell-b2-rigidity` | §4 Thm 4.6 | `GoldenOrbitB2Rigidity.*`（`rational_endpoint_rigidity_identity`、mod5/m8q 系列、`pell_b2_spectral_gap` 等 22 条） | 行161–182 | 已核实 | [1] 全 base；$B=2$ 分类的算术核心 |
| `prop:conjugate-positivity` | §4 Thm 4.7 | `GeneralEndpointRigidity.eta_conj_ge_inv_sq_of_gt_one/add_pos_gt_abs/eq_inv_sq_at_two` | 行331–333 | 已核实 | [1] 全 base；初等共轭估计 |
| `thm:golden-b2-exact` | §4 Thm 4.8 | `GoldenOrbitB2Rigidity.b2_case1_*/b2_case2_*` + `phi85/phi83_*`（误差/下界/第二极限点件） | 行173–182 | 纸面证明 | [1] 核心件已核实；完整 $\liminf$ 组装纸面 + 数值；常数已独立复算一致 |
| `lem:general-endpoint-rigidity` | §4 Thm 4.9 | `GeneralEndpointRigidity.*`（xi1/Muv/inert/even_D/mod_2D 等约 30 条） | 行325–352 | 已核实 | [1] 全 base；$B\ge3$ 分类的统一算术引擎 |
| `lem:even-suffix-sep` | §4 Thm 4.10 | — | 不在日志 | 纸面证明 | [1] 纯连分数估计，Case 2 排除引理 |
| `thm:golden-b3-exact` | §4 Thm 4.11 | `GeneralEndpointRigidity.b3_inert_three_not_dvd_m` + `b3_spectral_gap`（关键排除/谱隙件） | 行353–354 | 纸面证明 | [1] 核心件已核实；Case1/2 $\liminf$ 组装纸面 + 2500 位数值（作者自报） |
| `thm:golden-b4-exact` | §4 Thm 4.13 | `GeneralEndpointRigidity.b4_mod16_excludes_37` + `b4_spectral_gap` | 行355–356 | 纸面证明 | [1] 核心件已核实；mod-16 排除纸面完整 |
| `thm:golden-finite-shift` | §4 Thm 4.14 | —（支撑：窗口周期 + `mobius_error_identity` 行129 + 三族枚举程序作者自报） | 不在日志 | 纸面证明 | [1] 主算法定理；13 基准复算作者自报（本工作区未见脚本） |
| `cor:golden-pure-heads` | §4 Thm 4.15 | — | 不在日志 | 纸面证明 | [1] 主定理 + 发散头推论 |
| `cor:golden-mixed` | §4 Thm 4.16 | — | 不在日志 | 纸面证明 | [1] 多尺度特例 + 数值 |
| `cor:golden-finite-shift-examples` | §4 Thm 4.17 | `GeneralEndpointRigidity.b5/b6_spectral_gap` 等（部分支撑） | 行358，360 | 纸面证明 | [1] 完整证明归入 B5/B6/多尺度定理；数值已复算一致 |
| `thm:general-quadratic-phase` | §5 Thm 5.1 | — | 不在日志 | 纸面证明 | [1] Bugeaud 公式 + 相位有限性；对 $e$ 仿射像有效性以窗口周期为前提 |
| `cor:metallic-spectrum` | §5 Thm 5.2 | — | 不在日志 | 纸面证明 | [1] 上定理特例 |
| `thm:pure-trace-test` | §5 Thm 5.4 | — | 不在日志 | 纸面证明 | [1] 通向理想类筛法的桥梁 |
| `cor:principal-orbit-spectrum` | §5 Thm 5.5 | — | 不在日志 | 纸面证明 | [1] 上定理推论 |
| `cor:prime-norm-orbit` | §5 Thm 5.6 | — | 不在日志 | 纸面证明 | [1] 上定理推论（$\Delta=60$ 例） |
| `prop:orbit-mobius` | §5 Thm 5.7 | — | 不在日志 | 纸面证明 | [1] 初等输运 |
| `thm:phase-convergence-rate` | §5 Thm 5.8 | — | 不在日志 | 纸面证明 | [1] 误差恒等式推论 |
| `lem:general-case2-criterion` | §5 Thm 5.9 | — | 不在日志 | 纸面证明 | [1] B5/B6/多尺度统一 Case 2 引擎 |
| `thm:golden-b5-exact` | §5 Thm 5.10 | `GeneralEndpointRigidity.b5_even_m` + `b5_spectral_gap`（部分） | 行357–358 | 纸面证明 | [1] $T=50$ 最小周期/20 后缀集为剩余计算；常数已复算一致 |
| `thm:golden-b6-exact` | §5 Thm 5.11 | `GeneralEndpointRigidity.b6_inert_three_not_dvd_m` + `b6_spectral_gap`（部分） | 行359–360 | 纸面证明 | [1] $m=83$ 排除用素性 + 同余筛；常数已复算一致 |
| `thm:golden-multiscale-exact` | §5 Thm 5.12 | —（支撑见 B3/B4/B5/B6 件） | 不在日志 | 纸面证明 | [1] 四项 (i)–(iv) 混合相位；前二值已复算一致 |
| `thm:trace-class-sieve` | §5 Thm 5.15 | — | 不在日志 | 依赖黑箱 | [1] 依赖类群对应（纸面自证）；新筛法陈述，首创性未核查 |
| `thm:trace-all-norms` | §5 Thm 5.16 | — | 不在日志 | 依赖黑箱 | [1] 上定理推广（含导子素数） |
| `cor:common-prime-power` | §5 Thm 5.17 | — | 不在日志 | 纸面证明 | [1] 上定理推论 |
| `thm:trace-common-progression` | §5 Thm 5.18 | — | 不在日志 | 纸面证明 | [1] 类群 + 中国剩余构造 |
| `thm:trace-density-one` | §5 Thm 5.19 | — | 不在日志 | 依赖黑箱 | [1] 依赖 Neukirch 射线类素理想密度 + Conrad 导子对应（均未核到原文）；且要求 $x$ 部分商发散（π 是否满足未知，稿件自承） |
| `cor:trace-common-density` | §5 Thm 5.20 | — | 不在日志 | 纸面证明 | [1] 上定理推论 |
| `lem:invariance` | §6 Thm 6.1 | `irrMeasure_neg/add_rat/mul_rat/inv` | 行12–15 | 已核实 | [5] 初等复述；全 base |
| `lem:mue` | §6 Thm 6.2 | `mu_e_eq_two`（公理声明，非审计条目；`Measure.lean`） | 不在日志 | 依赖黑箱 | [5] Bundschuh 结果经 CNU2024 转引；Lean 侧为项目自加公理，未证明 |
| `thm:measure-reduction` | §6 Thm 6.3 | `theoremA_sum/diff/prod/quot` | 行16–19 | 依赖项目自加公理 | [5]/[1] 初等组合；相对 `mu_e_eq_two`（prod 项另相对 `e_transcendental`） |
| `cor:four-irrational` | §6 Thm 6.4 | —（逆否；支撑见上行） | 不在日志 | 纸面证明 | [1] 有效推论；前提期望假（稿件自承） |
| `thm:cf` | §6 Thm 6.6 | — | 不在日志 | 依赖黑箱 | [1] 依赖 Serret + Raney（未核到原文）；观察向障碍 |
| `prop:not-integer` | §6 Thm 6.7 | — | 不在日志 | 纸面证明 | [4] 初等十进制包络 |
| `prop:window` | §6 Thm 6.10 | —（候选 `AdjacentWitness`/`EpiFormalH.proposition3_*` 未经逐式确认为同义，不作对应） | 不在日志 | 纸面证明 | [1] Route A 严格终点 |
| `prop:recurrence` | §6 Thm 6.11 | —（同上） | 不在日志 | 纸面证明 | [1] 尾刚性 |
| `prop:four-exp` | §6 Thm 6.14 | — | 不在日志 | 纸面证明 | [1] 消极结果，范围限定（不排除未知恒等式，稿件自承） |
| `thm:translation` | §6 Thm 6.16 | — | 不在日志 | 纸面证明 | [1] 消极结果（Bai 数值仅注记）；$\irr_0\le2$ 恒成立 |
| `prop:scaling` | §6 Thm 6.18 | — | 不在日志 | 纸面证明 | [1] 初等 CM 格验证 |
| `cor:bertolin` | §6 Thm 6.19 | — | 不在日志 | 依赖黑箱 | [2] 条件：未评审预印本 Bertolin2026（成员资格亦开放，稿件自承） |
| `thm:alekseyev` | §6 Thm 6.21 | — | 不在日志 | 依赖黑箱 | [5] 已发表 arXiv:1104.5100（作者自报已读；本审计未核到原文） |
| `thm:meiburg` | §6 Thm 6.23 | `meiburg_criterion` + `flint_hills_converges_of_mu_lt` | 行21，23 | 依赖项目自加公理 | [2]+[1] FH 情形相对 `pi_transcendental` 已核实；一般 $u,v$ 仍为预印本条件 |
| `thm:flint` | §6 Thm 6.25 | `flint_hills_diverges_bound`（发散方向；收敛件见上行） | 行22 | 依赖项目自加公理 | [1] 有效条件链；发散前提期望假（稿件自承） |
| `thm:schanuel` | §6 Thm 6.28 | — | 不在日志 | 依赖黑箱 | [2] 猜想陈述 |
| `thm:schanuel-consequence` | §6 Thm 6.29 | — | 不在日志 | 依赖黑箱 | [2] 标准推导，条件结果 |
| `thm:adaptive-strip` | §6 Thm 6.31 | —（候选 `Escape*` 系列未经逐式确认为同义，不作对应） | 不在日志 | 纸面证明 | [1] 必要条件；用于 π 需未获的收敛子输入 |
| `cor:strip-escape` | §6 Thm 6.32 | — | 不在日志 | 纸面证明 | [1] 上定理推论 |
| `thm:factorial-quantization` | §6 Thm 6.33 | `FactorialCriterion.factorial_criterion/tFrac_bounds/recurrence_u` | 行72–74 | 已核实 | [1] 全 base；初等判据 |
| `prop:farey-gap` | App A Thm A.1 | — | 不在日志 | 自报待补 | [4] 作者自报 kernel-checked + 450 位证书 + `residue_certificate.py` 留存；有限分母排除，不构成一般证明（稿件自承） |
| `prop:nest-transfer` | App A Thm A.2 | — | 不在日志 | 依赖黑箱 | [1] 纸面推导有效；依赖 Nesterenko 定理黑箱（未核到原文） |
| `lem:eps-abs` | App B Thm B.2 | — | 不在日志 | 纸面证明 | [1] 证明内比较引理；顶层 `meiburg_criterion`（行21）覆盖 |
| `lem:f2-finite` | App B Thm B.3 | — | 不在日志 | 纸面证明 | [1] 辅助引理未单独审计；顶层见 `thm:f2-conv` 行 |
| `lem:f2-eventual` | App B Thm B.4 | — | 不在日志 | 纸面证明 | [1] 同上 |
| `lem:f2-dq` | App B Thm B.6 | — | 不在日志 | 纸面证明 | [1] 同上 |
| `lem:f2-good-dq` | App B Thm B.7 | — | 不在日志 | 纸面证明 | [1] 同上 |
| `lem:f2-exp` | App B Thm B.8 | — | 不在日志 | 纸面证明 | [1] 同上 |
| `lem:f2-core` | App B Thm B.9 | — | 不在日志 | 纸面证明 | [1] 同上 |
| `lem:f2-fiber` | App B Thm B.10 | — | 不在日志 | 纸面证明 | [1] 同上（`DimHCore.fiber_card_le` 等为异语境 fiber，不作对应） |
| `lem:f2-spacing` | App B Thm B.11 | `circle_spacing` | 行24 | 依赖项目自加公理 | [1] 相对 `pi_transcendental`；源码注释 Lemma 9.11 对应 |
| `lem:f2-count` | App B Thm B.12 | `dyadic_block_count` | 行25 | 依赖项目自加公理 | [1] 相对 `pi_transcendental`；源码注释 Lemma 9.12 对应 |
| `lem:f2-blocksum` | App B Thm B.13 | `block_sum_bound` | 行26 | 依赖项目自加公理 | [1] 相对 `pi_transcendental`；源码注释 Lemma 9.13/Jordan 对应 |
| `thm:f2-conv` | App B Thm B.14 | `flint_hills_converges_of_mu_lt` | 行23 | 依赖项目自加公理 | [1] 相对 `pi_transcendental`；收敛阈值定理 |
| `lem:sin-lower` | App B Thm B.16 | `sin_nat_ne_zero` + `sin_eventual_lower` | 行27–28 | 依赖项目自加公理 | [1] 相对 `pi_transcendental` |
| `lem:nearest` | App B Thm B.18 | `nearest_int_le_four_mul` + `nearest_int_tendsto_atTop`（+`abs_sub_mul_pi_factor`） | 行29–31 | 已核实 | [1] 全 base；初等取整事实 |
| `lem:uniform` | App B Thm B.19 | `term_tendsto_eventually_gt` + `alekseyev_eventual_lower` + `apprPairs_finite_of_flintHills` | 行32–34 | 依赖项目自加公理 | [1] 一致发散链，相对 `pi_transcendental` |
| `thm:alekseyev-bound` | App B Thm B.20 | `alekseyev_bound` | 行35 | 依赖项目自加公理 | [1] 相对 `pi_transcendental`；失败的逐项路线保留为历史记录（稿件自承） |
| `thm:conditional-bridge` | App B Thm B.21 | — | 不在日志 | 自报待补 | [2] tex 标 machine-verified；本日志无 `conditional_bridge`（或同义）条目；外部 OpenAI 工程作者自报未独立编译 |
| `thm:ai-reduction` | App B Thm B.22 | — | 不在日志 | 自报待补 | [2] 同上；`ai_reduction`（或同义）无对应条目 |
| `prop:finite-match` | App B Thm B.23 | —（候选 `EscapeReduction` 系列未经逐式确认为同义，不作对应） | 不在日志 | 纸面证明 | [1] $D_j(B)$ 约化；$D_j(B)=0$ 判据 |
| `prop:rational-span` | App B Thm B.24 | `EscapeReduction.reduction_to_lattice` + `EscapeReduction.P1_imp_irrational` | 行84–85 | 已核实 | [3] 全 base；但为等价改写/换靶（与原问题同族难度，稿件 L108 自承），不降低难度 |
| `thm:eventual-dimension` | App B Thm B.25 | —（相关 `SpectralGap`/`DimHFinite`/`GaugeExact` 件已核实，逐式同义待确认，不作对应） | 不在日志 | 纸面证明 | [1] 初等覆盖论证；$\{\pi\}$ 成员资格未定（稿件自承） |

## 无标签定理型环境（附注，不计入 96）

- §3 Thm 3.4 Machin 同步截断障碍命题：无 `\label`；—；不在日志；纸面证明（消极结果，Bertrand 假设 + 同余计算）。
- App B Thm B.15 `sin n ≠ 0` 引理（无标签）：`sin_nat_ne_zero`，行27；依赖项目自加公理（相对 `pi_transcendental`）。
- App B Thm B.17 因式分解引理 `|n-mπ|=|m|·|π-n/m|`（无标签）：`abs_sub_mul_pi_factor`，行29；已核实（base）。

## 最值得下轮补进 Lean 的前 5 条（数学价值 × 可行性）

1. **`prop:dirichlet-divisor`**：全篇筛法的地基，tex 已声称 `DVerify` 核验但本日志无条目——补进即把“自报”转为“已核实”，价值/可行性双高（初等整性论证）。
2. **`thm:explicit-period` + `thm:affine-window` 的完整组装**：`HermiteResiduePeriod` 已有同余周期片段（行570–575），缺窗口长度奇性/`r_j=1` 判据/首位增量的组装；补齐即覆盖论文主窗口理论，可行性中等。
3. **`thm:golden-finite-shift` 的三族完备性组装**：刚性件（`mobius_error_identity`、`GeneralEndpointRigidity` 全系）均已核实，只差有限枚举完备性的形式化——主算术结果的最后一块拼图。
4. **`prop:farey-gap`**：`residue_certificate.py` 与日志已留存，有限分母证书的形式化（区间包络 + 剩余筛）属计算型任务，可行性高，可消掉一处“自报”。
5. **`thm:golden-b3/b4-exact` 的 Case1/Case2 `liminf` 组装**：`b3/b4_spectral_gap` 与排除引理已核实（行353–356），补第二极限点与 extremal 族完备性即可关闭 $B=3,4$ 分类。

> 注：`thm:conditional-bridge` / `thm:ai-reduction` 未进前 5——其证据在外部 OpenAI 仓库，本工作区不可独立复跑（作者自承未编译），可行性为零；应先降标为「作者自报，未复跑」，而非补形式化。
