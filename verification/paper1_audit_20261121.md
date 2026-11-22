# 论文一主稿现行版逐项审计报告（paper1_audit_20261121）

- 审计对象：`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex`（4623 行，约 72 页；2026-11-21 综合修订版）
- 审计人：数学研究助理（子代理）；方法：通读全文 + 100 个定理型环境逐项摘录 + Lean 实测日志复核 + 常数实测
- 背景文件：`paper1_e_plus_pi/00_merge_review.md`（已知核查结论）、`verification/audit_recheck_20261121.log`（Lean 审计实测）
- 纪律：`AGENTS.md` 五分类法 / 引用纪律 / 事实基线 / 形式化纪律 / 计算纪律；`paper-audit` skill 流程

## 一句话总判断

**本稿未证明 $e+\pi$ 的无理性（仍为公开问题，稿件自身亦明确声明），其实质贡献是一套关于 $e$ 的有理仿射像的连分数窗口周期理论、有界金轨极限谱的有限枚举与 $B\le 6$ 精确分类、以及二次轨道迹理想类筛法与密度一结果——其中核心代数恒等式与 Flint Hills 情形的 Meiburg 准则确有 Lean 核验支撑（349 条、sorryAx=0，但 22 条相对项目自加公理），而首创性未经系统文献对照、两处“machine-verified”标签在本工作区证据中无对应条目、全部 $\pi$ 侧无穷尺度输入依然开放。**

## 证据基线（先行说明）

1. **Lean 实测复核**（`verification/audit_recheck_20261121.log`，本审计实际打开核对）：
   - 共 349 条 `depends on axioms` 条目（与稿件自报 349 一致），`sorryAx` 出现 0 次（已核实）。
   - 其中 327 条仅依赖 Lean 基础公理 + 经典白名单（`propext, Classical.choice, Quot.sound`）。
   - **22 条依赖项目自加公理**（`e_transcendental` / `pi_transcendental` / `mu_e_eq_two`），即把 $e$ 超越、$\pi$ 超越、$\irr(e)=2$ 作为未证假设引入。
     名单：`at_least_one_transcendental`、`four_numbers_at_most_one_rational`、`theoremA_sum/diff/prod/quot`、`proposition_H'`、
     `meiburg_criterion`、`flint_hills_diverges_bound`、`flint_hills_converges_of_mu_lt`、`circle_spacing`、`dyadic_block_count`、
     `block_sum_bound`、`sin_nat_ne_zero`、`sin_eventual_lower`、`term_tendsto_eventually_gt`、`alekseyev_eventual_lower`、
     `apprPairs_finite_of_flintHills`、`alekseyev_bound`、`DefectFibres.finer_scale_ratio/control_example/deltaSel_ne_zero`。
     纸面上这些对应 Hermite–Lindemann（$e,\pi$ 超越）与 Bundschuh（$\irr(e^r)=2$）黑箱；形式化意义上凡依赖它们的结论都是**相对**这些假设的。
   - 日志中**无** `conditional_bridge` / `ai_reduction`（或同义）声明条目（已用 `bridge|eduction|converges|ranscend|ndepend|onditional` 全文检索），
     故文内 Theorem `thm:conditional-bridge` 与 `thm:ai-reduction` 的“machine-verified”标签**在本工作区证据中无对应**（见【引用错误/标签问题】第 1 条）。
2. **常数实测**：16 个精确值（$1-2/\sqrt5$、$9/(4\sqrt5)-1$、$1-20/(9\sqrt5)$、$22/(9\sqrt5)-1$、$1-35/(16\sqrt5)$、
   $56/(25\sqrt5)-1$、$1-54/(25\sqrt5)$、$1-79/(36\sqrt5)$、$110/(49\sqrt5)-1$、$1-108/(49\sqrt5)$、
   $7/(3\sqrt5)-1$、$1-\sqrt5/3$、$8/(3\sqrt5)-1$ 等）用 Python 复算，与稿值在 $10^{-9}$ 内一致。
   脚本：`verification/_audit_constcheck.py`，输出：`verification/_audit_constcheck.log`。全部通过。
3. **引用核查权限声明**：本子代理仅有本地工具（无外部文献浏览器），**未独立打开任何外部原始文献/网页**。
   因此一切外部书目字段（作者、卷、页、年、DOI、定理编号）对本审计均为「**未核到**」；下文“作者自报已读级别”转述稿件自己的说法，不视为本审计的核实。
4. 定理计数：全文定理型环境 100 个（problem 1 + theorem/proposition/corollary/lemma 99），下表覆盖全部有编号数学断言。

## 逐项对照表（结果 | 类别 | 核查状态 | 与已有文献关系 | 依据）

类别编号：[1]无条件（新）结果 [2]条件结果 [3]等价改写或换靶 [4]有限计算或有限排除 [5]文献核查与复现。
“首创性未核查”指本审计未做系统文献检索，只能作负搜索缺席声明，不能断言无先例。

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
|---|---|---|---|---|
| Prob `prob:main`（$e+\pi$ 无理/超越/代数无关？） | —（问题陈述） | 已通读 | 公开问题（事实基线） | 稿件诚实声明未解决 |
| Thm `thm:HL`（Hermite–Lindemann） | [5] | 未核到原文；黑箱引用 | 经典（Hermite 1873 / Lindemann 1882） | 纸面引用；Lean 中对应 `e_transcendental/pi_transcendental` 为项目公理 |
| Thm `thm:LW`（Lindemann–Weierstrass） | [5] | 未核到原文；黑箱引用 | 经典 | 同上 |
| Thm `thm:GS`（Gelfond–Schneider） | [5] | 未核到原文；黑箱引用 | 经典 | 用于 `thm:epi` |
| Thm `thm:schneider`（Schneider 椭圆情形，经 Duke 讲稿） | [5] | 未核到原文；转引讲稿 | 经典结果，引用的是预印本讲稿 URL | 仅用于注记与 `prop:scaling` 背景 |
| Thm `thm:vieta`（$e+\pi,e\pi$ 至少其一超越） | [5] | 纸面证明已通读，有效 | 初等经典论证复述 | Vieta 公式 + 代数数域封闭性 |
| Thm `thm:four`（四组合至多其一有理） | [5] | 纸面证明已通读，六对排除有效 | 初等组合复述；稿件未宣称新 | 逐对有理封闭性论证 |
| Thm `thm:epi`（$e^\pi$ 超越） | [5] | 纸面证明已通读，有效 | Gelfond–Schneider 标准应用 | Euler 恒等式 + GS |
| Thm `thm:fourier` / `thm:niven`（$e,\pi$ 无理） | [5] | 仅陈述，未重证 | 经典；弱于 HL，作技术基线 | 引 Conrad 讲稿 |
| Prop Dirichlet 除数限制（无编号，`prop:dirichlet-divisor`） | [1]（纸面；首创性未核查；作者不宣称优先权） | 纸面证明已通读 | 初等 Dirichlet + 整性论证；作者明示不争优先权 | 稿件注记另有 Lean 核验（`DVerify.prop_8_1`，作者自报） |
| Prop `prop:two-window`（双本原见证） | [1]（纸面；首创性未核查） | 纸面证明已通读 | 行列式初等估计 | 17 个双窗口枚举为计算佐证（作者自报） |
| Prop `prop:signed-round`（符号型与奇偶判别） | [1]（纸面；首创性未核查） | 纸面证明已通读；$\pi$ 侧无穷奇偶一致仍开放（稿件自承） | Hermite 恒等式 + 收敛子排序 | 推论“无穷同奇偶 $\Rightarrow$ 无理”本身有效但条件未获 |
| Prop Machin 截断障碍（无编号） | [1] 消极结果（纸面） | 已通读；Bertrand 假设 + 同余计算 | 排除“同步 Machin 截断”这一特定构造，不排除他法（稿件自承） | 余项积分估计 |
| Thm `thm:explicit-period`（有理蕴含窗口周期 $2B^2$，$r_j$ 奇 $\ge3$） | [1]（纸面；首创性未核查） | 纸面证明已通读；$P_j,Q_j\bmod T$ 周期论证完整 | 以 Hermite 行列式 + $M_j\mid B^2$ 为核心的新组装 | $B=1$ 时 $r_j\equiv3` 为特例 |
| Thm `thm:digit-shift`（窗口首位平移 $+4M_j^2$） | [1]（纸面；首创性未核查） | 纸面证明已通读 | 上定理的细化 | 幺模基变换 |
| Cor `cor:digit-statistics`（无候选周期检验） | [1]（纸面；首创性未核查） | 已通读；$\alpha=T/K$ 界依赖主定理 | 主定理的推论 | 对数密度估计 |
| Thm `thm:gcd-converse`（任一分母商有界 $\iff x\in\mathbb Q+\mathbb Qe$） | [1]（纸面；首创性未核查） | 纸面证明已通读（三条件等价） | 核心分类；$1/3$ 非最优（稿件自承） | 双向整性论证 |
| Cor `cor:recover-slope`（斜率隔离） | [1]（纸面） | 已通读；应用于 $\pi$ 需未获输入（稿件自承） | 上定理推论 | $s_j$ 有理量极限 |
| Thm `thm:affine-window`（仿射周期 $2B\|C\|$ 与首位增量） | [1]（纸面；首创性未核查） | 纸面证明已通读 | 主窗口理论的仿射推广 | $T=2B\|C\|$，$r_j=1\iff G_jG_{j+1}=T$ |
| Cor `cor:affine-single`（五连单窗口刻画 $\|C\|=1,B\in\{2,4\},A$ 奇；四窗不够） | [1]（纸面；首创性未核查） | 已通读；sharp 性有反例构造 | 上定理推论 | 五窗 $\Rightarrow$ 分类的组合论证 |
| Prop `prop:rational-gcd-valuations`（素数幂约化） | [1]（纸面） | 已通读 | 赋值计算引理 | $v_p(G_j)$ 分段公式 |
| Cor `cor:bounded-digit-block`（双数字检验） | [1]（纸面） | 已通读 | Fibonacci 生长 + 窗口界 | $F_{\ell+1}\le2B^2$ |
| Cor `cor:golden-bound`（金轨下界 $1/10368T^2$） | [1]（纸面） | 已通读 | 后续精确值的粗界 | 高度估计 |
| Lem `lem:norm-parity-rigidity`（$\mathbb Z[\varphi]$ 范数奇偶刚性） | [1]（Lean 已核验，base axioms） | 日志有对应条目（`GoldenOrbitRigidity.norm_parity_rigidity_*`，仅 base axioms） | 后续全部精确分类的算术基础 | $m$ 奇偶筛 |
| Thm `thm:golden-exact-second`（一般发散头 $c_\varphi=1-2/\sqrt5$ + 第二极限点） | [1]（纸面 + 核心 Lean 已核验；首创性未核查） | 核心代数/一致分离/凹二次下界 Lean 已核验（`rem:golden-b2-model` + 日志）；Case 组装为纸面 | 以 Bugeaud (3.4) 为局部误差源；框架为稿件自有 | 第二极限点 $4/\sqrt5-1$ sharp |
| Cor `cor:golden-exact-e`（$6-e,e,M(e^{1/m})$ 精确值） | [1]（纸面） | 已通读；由上定理 + $e$ 连分数直接得 | 已知连分数的应用 | — |
| Lem `lem:pell-b2-rigidity`（有理端点/Pell 模 5 刚性） | [1]（Lean 已核验，base axioms） | 日志 `GoldenOrbitB2Rigidity.*` 22 条对应 | $B=2$ 分类的算术核心 | $m$ 奇性 + $m\ne9$ 界 |
| Prop `prop:conjugate-positivity`（共轭正性） | [1]（Lean 已核验，base axioms，作者自报；日志 `GeneralEndpointRigidity` 系列佐证） | 已通读 | 初等共轭估计 | $\eta'\ge\varphi^{-2}$ |
| Thm `thm:golden-b2-exact`（$11/2-e$ 精确值 + 第二极限点） | [1]（纸面 + 核心 Lean；首创性未核查） | 误差恒等式/下界 Lean 已核验；完整 $\liminf$ 组装纸面 + 数值 | 模 $5$ 分歧排除 $m=9$ | $c=9/(4\sqrt5)-1$（已实测复算 OK） |
| Lem `lem:general-endpoint-rigidity`（一般有理端点四部分刚性） | [1]（Lean 已核验，base axioms，作者自报 30 条） | 已通读；inert 素数互反 + mod-$2D$ 同余筛 | $B\ge3$ 分类的统一算术引擎 | $M_{u,v}^2-5D^2=4N(\xi_1)N(\xi_2)$ |
| Lem `lem:even-suffix-sep`（偶长后缀一致分离） | [1]（纸面） | 已通读；纯连分数估计 | Case 2 排除引理 | $\Delta(S)>0$ 一致界 |
| Thm `thm:golden-b3-exact`（$B=3$ 精确值 + 四 extremal 族 + 第二极限点） | [1]（纸面 + 2500 位数值；首创性未核查） | 已通读；Case1/Case2 $\liminf$ 组装为纸面（稿件自承 §6 归纳），数值验证作者自报 | $D=18$，六后缀；$c=1-20/(9\sqrt5)$（实测 OK） | 周期 $T=18$ 最小性由剩余计算得 |
| Thm `thm:golden-b4-exact`（$B=4$ + mod-16 排除 $m=37$） | [1]（纸面 + 数值；首创性未核查） | 已通读；mod-16 排除论证完整 | $D=32$，$q_0\equiv\pm1\pmod8$；$c=1-35/(16\sqrt5)$（实测 OK） | 两剩余类 $A\equiv1,3\pmod4$ |
| Thm `thm:golden-finite-shift`（主算法定理：有界谱有限可枚举，首二值 $H=3$ 可算） | [1]（纸面；首创性未核查；稿件自承为主要算术结果） | 证明依赖窗口周期 + Bugeaud 公式 + 三族枚举；13 基准复算作者自报通过（本工作区未见该脚本，为作者自报） | 配套 `golden_finite_spectrum.py`（归档路径，作者自报） | 三族完备性为纸面论证 |
| Cor `cor:golden-pure-heads`（发散头全谱） | [1]（纸面） | 已通读 | 主定理 + 发散头的直接推论 | 谱 $=\{\|1-(2j+1)/\sqrt5\|\}$ |
| Cor `cor:golden-mixed`（$(1+e)/6$ 切片） | [1]（纸面 + 数值） | 已通读；七值表 | 多尺度定理特例 | 前二值已实测 OK |
| Cor `cor:golden-finite-shift-examples`（$B=5,6$、$22/7-e$ 表值） | [1]（纸面 + 数值；首创性未核查） | 已通读；完整证明归入 B5/B6/多尺度定理 | 数值已实测复算 OK | — |
| Thm `thm:general-quadratic-phase`（任意二次轨道有限相谱 + 计数界） | [1]（纸面；首创性未核查） | 已通读；“对非常值 $e$ 仿射像有效”以窗口周期为前提 | Bugeaud 公式 + 相位有限性 | $N_\tau$ 上下界 |
| Cor `cor:metallic-spectrum`（金属比常周期闭谱） | [1]（纸面） | 已通读 | 上定理特例 | $N=\sqrt{a^2+4}H+O(1)$ |
| Thm `thm:pure-trace-test`（纯头迹检验：除数判别） | [1]（纸面；首创性未核查） | 已通读 | 通向理想类筛法的桥梁 | $T_\tau$ 除数测试 |
| Cor `cor:principal-orbit-spectrum`（monoid 轨道全谱） | [1]（纸面） | 已通读 | 上定理推论 | 首项计数 |
| Cor `cor:prime-norm-orbit`（素范数障碍；$\sqrt{15}$ 例） | [1]（纸面） | 已通读 | 上定理推论 | $\Delta=60$ 例 |
| Prop `prop:orbit-mobius`（幺模输运不变性） | [1]（纸面） | 已通读 | 初等输运 | $\mathcal L_\tau(gx)=\mathcal L_\tau(x)$ |
| Thm `thm:phase-convergence-rate`（趋近速率 $O(b^{-1})$，$e$ 仿射像 $O(j^{-1})$） | [1]（纸面） | 已通读 | 误差恒等式推论 | 见证尾族同速率 |
| Lem `lem:general-case2-criterion`（一般 Case 2 排除准则） | [1]（纸面） | 已通读；分支 (a)(b) 界完整 | B5/B6/多尺度证明的统一 Case 2 引擎 | $r_1,r_2$ 极值量 |
| Thm `thm:golden-b5-exact`（$B=5$ 精确值 + inert 排除 + 第二极限点） | [1]（纸面 + 数值；首创性未核查） | 已通读；$T=50$ 最小周期、20 后缀集为剩余计算 | $c=56/(25\sqrt5)-1$（实测 OK） | 四类 $16$–$19/5-e$ |
| Thm `thm:golden-b6-exact`（$B=6$ + inert-3 与 mod-8 排除 $m=81,83$） | [1]（纸面 + 数值；首创性未核查） | 已通读；$m=83$ 排除用 $83^2-5\cdot36^2=409\equiv1\pmod8$ 素性 + 同余筛 | $c=1-79/(36\sqrt5)$（实测 OK） | $q_0\equiv\pm3\pmod8$ |
| Thm `thm:golden-multiscale-exact`（$(1+e)/6,(1+e)/3,(1+2e)/3,22/7-e$ 完整分类） | [1]（纸面 + 数值；首创性未核查） | 已通读四项 (i)–(iv)；混合 $D_j$ 相位 | 前二值已实测 OK | inert-3 排除 $m=6$（$(1+e)/3$） |
| Thm `thm:trace-class-sieve`（互素迹范数的理想类筛） | [1]（纸面 + 外部黑箱；首创性未核查） | 已通读；依赖类群对应（纸面自证） | 新筛法陈述 | $\mathfrak c_\tau^{\pm1}\in\prod[\mathfrak p_p]^{i_p}$ |
| Thm `thm:trace-all-norms`（任意非零范数迹类） | [1]（纸面 + 外部黑箱；首创性未核查） | 已通读；$p\mid m$ 情形由 $(p^{k_p},\omega)$ 处理 | 上定理推广（含导子素数） | $\mathcal F_p(m)$ 分段定义 |
| Cor `cor:common-prime-power`（公共素数幂迹；$\Delta=20,m=6$ 例） | [1]（纸面） | 已通读 | 上定理推论；非本原形 $(2,6,2)$ 说明 | — |
| Thm `thm:trace-common-progression`（公共谱含无穷等差数列；异域至多交于 $1$） | [1]（纸面；首创性未核查） | 已通读三项 | 类群 + 中国剩余的构造 | 正线性下界计数率 |
| Thm `thm:trace-density-one`（迹格中密度一；$\delta_\tau=1/4h_f$） | [1]（纸面 + 外部解析黑箱；首创性未核查） | 已通读；依赖 Neukirch VII§13 射线类素理想密度 + Conrad 导子对应（黑箱，未核到原文） | Chebotarev 型密度 + Bonferroni 筛法的组装 | 误差 $O((2k+1)X^{-1/2})$ 项完整 |
| Cor `cor:trace-common-density`（公共谱首项计数 $g\sqrt d\,H$） | [1]（纸面） | 已通读 | 上定理推论 | 连跑 $\gg(\log H)^\delta$ |
| Lem `lem:invariance`（无理数度量在有理变换下不变） | [5] | 初等，有效 | 经典复述 | — |
| Lem `lem:mue`（$\irr(e^r)=2$；Bundschuh，经 CNU2024 转引） | [5] | 未核到原始文献；转引 | 经典结果，转引 2024 综述 | 标题已诚实标注转引 |
| Thm `thm:measure-reduction`（四组合之一有理 $\Rightarrow\irr(\pi)=2$） | [5]/[1]（初等组合；作者不争优先权） | 纸面证明有效（不变性 + $\irr(e)=2$） | 结构性归约，非新定理宣称 | 全部后续条件链的前提 |
| Cor `cor:four-irrational`（$\irr(\pi)>2\Rightarrow$ 四组合无理） | [1]（纸面；逆否，条件未获） | 有效推论；前提期望假（稿件自承） | 上定理逆否 | — |
| Thm `thm:cf`（有理蕴含 $\pi$ 连分数为 $e$ 的有限状态传导像） | [1]（纸面必要条件；应用于 $\pi$ 无输入） | 有效（Serret + Raney 黑箱，未核到原文） | 观察向障碍（$\pi$ 连分数无界性亦开放，稿件自承） | 数值比对仅附录佐证 |
| Prop `prop:not-integer`（$e+\pi\notin\mathbb Z$） | [4]（初等数值排除） | 有效（十进制包络） | 平凡 | $5.85987<e+\pi<5.85989$ |
| Prop `prop:window` + Prop `prop:recurrence`（阶乘窗条件 + 尾刚性） | [1]（纸面必要条件；证伪即证主问题，但远未证伪） | 已通读；稿件明示“非等价难度断言” | Route A 的严格终点 | $B_n-1/n<n!\pi<B_n$ |
| Prop `prop:four-exp`（四指数路线的已知值构造被堵） | [1] 消极结果（纸面） | 已通读；“no $2\times2$ matrix … from known values”范围限定明确 | 不排除未知恒等式（稿件自承） | — |
| Thm `thm:translation`（$\irr(\pi)$ 上界程序的平移恒等式 + 空无性） | [1] 消极结果（纸面；Bai 数值仅注记） | 已通读；$\irr_0=1+1/(M-1)\le2$ 恒成立 | 终结“上界改进 $\Rightarrow$ 矛盾”幻想 | $M=7.10320534\Rightarrow\irr_0\approx1.16385$（注记） |
| Prop `prop:scaling`（$\wp$ 值集 $S$ 的代数数乘法封闭） | [1]（纸面初等） | 已通读；$\lambda=a^{-1/2}$ 缩放有效 | CM 格保持的直接验证 | — |
| Cor `cor:bertolin`（Bertolin 定理 $\Rightarrow e,\pi$ 代数无关） | [2]（依赖未评审预印本 arXiv:2609.15294） | 条件链本身有效；前提与成员资格皆开放（稿件自承条件） | 预印本仅“摘要+引言+证明开头已读”（作者自报） | $\pi\in S$ 子问题开放 |
| Thm `thm:alekseyev`（Alekseyev 已发表准则三项 + vacuous 充分条件说明） | [5] | 作者自报全文已读（Thms 2,5, Cors 3,4,6 已核）；本审计未核到原文 | 已发表 arXiv:1104.5100（2011） | 含对二级文献误传的纠正记录 |
| Thm `thm:meiburg`（Meiburg 预印本准则；FH 情形已 Lean 化） | [2] 一般情形（预印本）+ [1] FH 情形（Lean，相对 `pi_transcendental`） | FH 情形日志有 `meiburg_criterion` + `flint_hills_converges_of_mu_lt`；一般 $u,v$ 仍为预印本条件 | 作者自报原预印本证明结构已验；Round 6→7  attribution 更正留档 | 边缘 $\irr=5/2$ 不可判（构造反例） |
| Thm `thm:flint`（$e+\pi\in\mathbb Q\Rightarrow$ FH 收敛；发散 $\Rightarrow$ 四组合无理） | [1]（有效条件链；逆否前提期望假，稿件自承） | 证明 = measure-reduction + meiburg(FH)，有效 | 发散方向“probably false”，不构成进展承诺 | — |
| Thm `thm:schanuel`（Schanuel 猜想陈述） | [2]（猜想陈述；$n=1$ 已证等价 HL） | 状态说明已通读 | Ax 1971 函数域类比（未核到原文） | — |
| Thm `thm:schanuel-consequence`（Schanuel $\Rightarrow$ 代数无关 $\Rightarrow e+\pi$ 超越） | [2]（依赖未证猜想） | 标准推导，有效 | 条件结果 | — |
| Thm `thm:adaptive-strip`（自适应排除带 + 禁区 $[2Bq,jq/B]$） | [1]（纸面必要条件） | 已通读；预算不等式 $\Rightarrow d\mid Bq$ | 应用到 $\pi$ 需未获的收敛子输入 | — |
| Cor `cor:strip-escape`（分母逃逸检验） | [1]（纸面） | 已通读；固定 $B$ 单对排除有效 | 上定理推论 | $d/Q_j\to\infty,\ d/jQ_j\to0$ 条件未获 |
| Thm `thm:factorial-quantization`（$u_n$ 有界 $\Rightarrow$ 子列极限为整数；$\limsup\|u_n-k\|<1\iff x-ke\in\mathbb Q$） | [1]（纸面；首创性未核查） | 已通读 | 一般实数 $x$ 的初等判据 | $a_{n+1}=k$ 最终恒定 |
| Prop `prop:farey-gap`（$b<3635695100$ 认证分离 $\|bs-a\|>1/5\times10^9$） | [4]（有限排除；作者自报 kernel-checked） | 未复跑；脚本 `verification/residue_certificate.py` + `residue-certificate.log` 留存 | 有限分母范围，不构成一般证明（稿件自承） | 450 位区间证书（作者自报） |
| Prop `prop:nest-transfer`（$\pi=r+se\Rightarrow e,e^e,\Gamma(1/4)$ 代数无关） | [1]（纸面条件命题；依赖 Nesterenko 黑箱，未核到原文） | 已通读；“包含 $e+\pi\in\mathbb Q$”成立 | 应用 Nesterenko 定理的纸面推导 | $\varpi$ 恒等式 + 归纳 |
| Lean 引理群 `lem:eps-abs/f2-finite/f2-eventual/f2-dq/f2-good-dq/f2-exp/f2-core/f2-fiber/f2-spacing/f2-count/f2-blocksum` + Thm `thm:f2-conv` | [1]（Lean 已核验；多条相对 `pi_transcendental`） | 日志对应条目均为 base 或 +项目公理 | 稀疏代数 = Meiburg 论证的形式化 | 分母型下界方向（稿件注记方向选择） |
| Lemmas $\sin n\ne0$ / `lem:sin-lower` / 因式分解 / `lem:nearest` / `lem:uniform` + Thm `thm:alekseyev-bound`（收敛 $\Rightarrow\irr(\pi)\le5/2$） | [1]（Lean 已核验，相对 `pi_transcendental`） | 日志有 `alekseyev_bound` 等对应条目；Round 9 前失败的逐项路线保留为历史记录（稿件自承） | nearest-integer 论证替代密度路线 | — |
| Thm `thm:conditional-bridge`（OpenAI $\irr(\pi)=2$ 形式 $\Rightarrow$ FH 收敛） | [2]（依赖外部未独立编译的 Lean 工程） | **作者自报 machine-verified；本工作区日志无对应条目（未核到）** | 外部仓库 `openai/math` 未独立构建（稿件自承） | 见标签问题第 1 条 |
| Thm `thm:ai-reduction`（代数无关假设 $\Rightarrow$ 四组合超越） | [2]（假设前提；Hunter 式初等推导） | **作者自报 machine-verified；本工作区日志无对应条目（未核到）** | 条件命题本身初等 | 见标签问题第 1 条 |
| Prop `prop:finite-match`（固定斜率有限指数检验） | [1]（纸面） | 已通读；双向界完整 | $D_j(B)=0$ 判据 | — |
| Prop `prop:rational-span`（$\bigcup B^{-1}L=\mathbb Q+\mathbb Qe$；P1 $\iff 1,e,\pi$ 线性无关） | [3]（等价改写；稿件自承 P1 与原问题同族难度） | 已通读，有效 | 换靶的诚实标注在 L108 与附录 | 不降低难度 |
| Thm `thm:eventual-dimension`（$\dim_H F_\tau=\max(1-\tau,0)$） | [1]（纸面；首创性未核查） | 已通读；质量分布 + 覆盖论证完整 | 初等覆盖论证（作者自报 Lean 历史记录指旧声明） | $\{\pi\}$ 成员资格未定（稿件自承） |

## 作者声称 vs 实际成立（差异清单）

1. **摘要/引言强表述均配有守门句，总体诚实。** Title thanks、摘要末段、L123 Honesty statement 三处明示“未证明 $e+\pi$ 无理性”；L378（Hurwitzian 条件）、L108（P1 换靶）、L3585（FH 发散期望假）、L3378（“reformulation, not a reduction”）均主动限缩。未发现把等价改写说成“更接近证明”的表述。
2. **“machine-verified”标签覆盖过度。** `thm:conditional-bridge` 与 `thm:ai-reduction` 在本工作区 349 条 Lean 日志中无对应声明；按形式化纪律应降标为「作者自报，未复跑」（证据或存于归档而不在本工作区，见下条）。其余 Lean 标签（Meiburg FH 情形、Alekseyev 方向、P1 归约、金轨恒等式）均有日志对应。
3. **附录复现路径指向归档目录。** `app:repro` 所列 `03_Numerical_Verification/`、`epi_formal/`、`golden_finite_spectrum.py` 等不在本工作区；本工作区仅见 `verification/verify_golden_*.py`、`residue_certificate.py` 及其日志（未复跑）。“13 基准组通过 / 12 项 sympy 12/12 PASS / 450 位证书”均为作者自报，本审计既未证实也未证伪。
4. **精确分类的范围边界论文自承但易被误读。** 摘要“for all coprime denominator classes $B=1,\dots,6$”成立（$B=1$ 由 `thm:golden-exact-second` 家族 + `cor:golden-exact-e` 覆盖，$B=2$–$6$ 各有专定理）；但 $B\ge7$ 仅有参数前沿注记（`rem:golden-general-regimes` 自承开放），“exact constants beyond denominator four”推论只给 $B=5,6,22/7-e$ 表值——一般 $B\ge7$ 无表、无定理。
5. **Trace 密度定理的“密度一”以前提为代价。** `thm:trace-density-one` 要求“$x$ 部分商发散”——$\pi$ 是否满足未知（连分数无界性开放，稿件 L3378 自承）；且证明依赖射线类群素理想密度（Neukirch 黑箱）与导子对应（Conrad 黑箱），原文均未核到。它不给出关于 $\pi$ 的任何无条件信息。
6. **引言 L81 把 `thm:trace-density-one` 列为“principal”之一。** 该定理本身有效，但其首创性本审计未做文献对照（需与 Parkkonen–Paulin、Pejković、Lin 等二次 Lagrange 谱文献系统比对，稿件亦只在 `00_merge_review` 留“待系统对照”）。不得称为突破性进展。

## 真正新增了什么（剔除复述/改写/有限计算后）

1. **$H_j=\lfloor Q_j\sqrt j\rfloor$ 窗口周期理论**：有理仿射输入下窗口计数/数字后缀的显式周期（$2B^2$、$2B|C|$）、首位增量公式、任一分母商有界性的完整分类（`thm:gcd-converse`）与五连单窗口 sharp 刻画。纸面证明完整；首创性待文献对照。
2. **有界金轨极限谱的有限枚举算法**（`thm:golden-finite-shift`）与 $B\le6$ 及四个多尺度目标的**精确值 + extremal 族 + 第二极限点**完整分类，含 inert 素数 / mod-$16$ / mod-$8$ 排除法。核心恒等式有 Lean 支撑，常数值本审计独立复算一致。
3. **二次轨道迹理想类筛法**（`thm:trace-class-sieve`、`thm:trace-all-norms`）、公共谱等差数列存在性与**密度一 + 首项计数**。纸面证明完整（依赖经典解析/代数数论黑箱）；首创性待对照。
4. **四路线 + 四桥恒等式的系统障碍分析与期望假重组**（Hurwitzian / $E$-值环单条件化）。组织性贡献；消极结果范围均有明确限定。
5. **Flint Hills 情形 Meiburg 准则与 Alekseyev 方向的形式化**（相对项目公理），及 P1 格点归约的 Lean 化。工程性贡献；见证据基线第 1 条的公理层级披露。

## 没做到什么（必须明示）

1. 未证明 $e+\pi$（及 $e-\pi,e\pi,\pi/e,\pi^e$ 单个）的无理/超越/代数无关；事实基线维持“全部开放”，唯一硬结论仍是“$e+\pi$ 与 $e\pi$ 至少其一超越”。
2. 未提供任何关于 $\pi$ 的无穷尺度新输入：$c_\varphi(\pi)=0$、$\irr(\pi)>2$、FH 发散、$\pi$ 非 Hurwitzian、$\pi\notin\mathbf E$、$1/\pi\in\mathbf E$ 成员资格，全部开放（稿件自承）。
3. 金轨精确理论止于 $B\le6$ 与四个多尺度目标；一般 $B\ge7$ 无定理。
4. 首创性无系统文献对照；无独立人工审稿；外部 OpenAI Lean 工程未独立编译；两处 machine-verified 标签无工作区内证据。
5. 有限计算（Farey 证书 $b<3635695100$、双窗口枚举、2500 位数值验证）只排除有限范围，不构成一般证明（稿件自承）。

## 引用抽查与【引用错误/标签问题】

抽查钥：HuberWustholz2022、Baker、Ax1971、Hermite1873、Bertolin2026、Bai2026、Meiburg2022、Alekseyev2011、BugeaudQuad、CNU2024、Duke、CompanionGauge。
本审计未独立打开任何外部文献，所有卷页年 DOI 字段均为「未核到」；以下为可由工作区内证据判定的事项：

- 【标签问题-1】`thm:conditional-bridge`、`thm:ai-reduction` 的“machine-verified”在本工作区 `audit_recheck_20261121.log`（349 条）中无对应声明条目。按形式化纪律应改标「作者自报，未复跑」，或补入对应声明的审计行。严重程度：中（不影响纸面条件链的有效性，只影响标签可信度）。
- 【提醒-2】`lem:mue` 经 `CNU2024`（Liang–Wang 2024 综述）转引 Bundschuh 结果。转引本身已在引理标题诚实标注（“Classical; Bundschuh, see [CNU2024]”），合规；若投稿建议补引 Bundschuh 原始文献。严重程度：低。
- 【提醒-3】`BugeaudQuad` 的 `eq.(3.4)`、`Lemmas 2.1–2.2`、`Cor.2.3`、`Lemma 4.1`、`Thm 4.2` 编号本审计未核到原文；但误差恒等式内容本身已被 Lean 核验（`mobius_error_identity` 系列），公式实质有独立佐证，风险低。`Duke`（Schneider 椭圆情形）为讲稿预印本 URL，仅用于注记，不进入主证明链。`HuberWustholz2022` 正文在 L3548 remark 引用，书目著录未核到；其引用方式诚实（明确区分线性关系已解决 vs 代数关系仍猜想）。
- 【合规-4】以下高风险引用稿件均已正确标记，无需纠正：Bertolin2026 / FischlerRivoal2026 / Bai2026 / Dan2026 / Yu2026 / Powers2025 / KalininKomatsu2026 / OpenAI2026 均为预印本且标条件或仅作注记；
  Carella 系列列为负面线索且明示不用；Tijdeman1971 自承“精确推论未从原文核实、不依赖”；Meiburg 一般情形保持预印本条件、仅 FH 情形升格（有日志对应）。
- 未发现已证实的卷号页码编造（因未独立核对原文，不作反向保证；建议投稿前由有网络核查能力的流程逐条核对 DOI 与定理编号）。

## 方法与留痕

- 逐项摘录脚本（中间产物，已清理）：`_audit_extract.py`、`_audit_extract2.py`；陈述摘录表（中间产物，已清理）：`_audit_envlist.txt`、`_audit_stmts.txt`。
- 常数复算脚本与输出（保留）：`verification/_audit_constcheck.py`、`verification/_audit_constcheck.log`（16 项全 OK）。
- 本报告外未改动任何文件。
