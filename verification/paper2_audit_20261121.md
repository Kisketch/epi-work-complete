# 论文二现行版 + 伴随稿逐项审计报告（2026-11-21）

> 审计对象：
> - A稿（现行版）：`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`（3346行，约64页）
> - B稿（伴随稿）：`paper1_e_plus_pi/02_companion_paper/Phase2_revised.tex`（4905行，65页）
> - 背景：`paper1_e_plus_pi/03_submission_prep/checklist_next_steps.md`、
>   `verification/audit_recheck_20261121.log`（349条`#print axioms`，`sorryAx=0`）
> - 本审计新增复算脚本：`verification/paper2_audit_20261121_check.py`（已运行 PASS）、
>   `verification/residue_certificate.py`（本轮独立复跑 EXIT 0）
> - 引用核查实际打开的页面：本地 `verification/reference_pdfs/` 中
>   `CLU_1805_11904.pdf`、`MEA_2511_10328v3.pdf`、`BLR_1710_03596.pdf`（经 `pdftotext` 提取正文），
>   外加本次实际打开的 Springer 出版页 `https://link.springer.com/article/10.1007/BF02896955`（FWW）。
>   `h-sets.pdf`（疑为 CMMS）提取为乱码，未能核验其定理内容。

## 一、总判断

**两稿的核心数学结果（谱完全离散化、临界规范、三分法、维数相变、窗口/留数定理）均为无条件新结果，与 $e+\pi$ 无理性公开问题无矛盾且两稿均明确声明未解决该问题；其中 A 稿声称的全部 Lean 形式化部分（349条审计声明、零 sorry、仅三条基础公理，另22条 Phase-1 遗留声明用经典白名单公理）与本次实测的 `audit_recheck_20261121.log` 一致，而 B 稿摘要对一般多项式递推临界规范与次临界维数界的“已机器验证”声称超出了该日志的覆盖范围，A 稿已将其纠正为纸面证明——这是两稿之间最重要的实质差异。**

## 二、逐项对照表（结果 | 类别 | 核查状态 | 与已有文献关系 | 依据）

说明：类别编号 = 1无条件新结果 / 2条件结果 / 3等价改写或换靶 / 4有限计算 / 5文献核查与复现。
“已核实”指该声明出现在 `audit_recheck_20261121.log` 且仅依赖
`[propext, Classical.choice, Quot.sound]`（或注明白名单公理）；“作者自报”指论文声称但不在该日志中。

### A稿 = B稿共有核心部分

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
|---|---|---|---|---|
| Thm class（$\{\Lam=0\}=L$ 分类） | 5 | 已核实（`Classification.theorem2_classification`，基础公理） | KL准则的子列变体，论文自身亦如此定位（A§prior）；负搜索未发现先例不等于已证无先例 | A§sec:class 纸面证明 + 日志第56行 |
| Thm gap（初始谱隙 $1/4$） | 5 | 已核实（`Classification.corollary3_gap`，基础公理） | 同上；黑箱用KL只能得 $1/16$，$1/4$ 为直接递推分析所得 | A§sec:class 纸面证明 + 日志第57行 |
| Cor spectral（初始隙二分） | 5 | 已核实（`SpectralGap.*` 5条，基础公理） | 同上 | 日志第86–90行 |
| Thm full-spectrum（全谱 $=\frac14\Z_{\ge0}\cup\{\infty\}$） | 1 | 已核实（`FullSpectrumDiscrete.*` 15条，基础公理） | 负搜索范围内未见 $e$-选子列加权谱的完全离散化先例（检索覆盖：已开核的BLR/CLU/MEA/KL-BDS引文链；其余未核到） | A§sec:spectrum + 日志第149–167行 |
| Cor sub（隙上水平集恒定 $E_c=E_{k/4}$） | 1 | 已核实（同上模块） | 同上 | 日志第159–162行 |
| Lem factorial / Lem branch（$Q_j\ge j!$，一致分支界） | 1（辅助引理） | 已核实（`DimHCore.*`，基础公理） | 初等 | 日志第91–93行 |
| Thm finite（一切有限水平集 $\dimH=0$） | 1 | 已核实（`DimHFinite.dimH_levelSet_finite`，基础公理） | 区别于经典无加权零集（满维数）；覆盖论证不依赖连续分数公理 | A§sec:finite-levels + 日志第102行 |
| Cor infinite-level（$\{\Lam=\infty\}$ 满测度、局部维数1） | 1 | 已核实（`GaugeExact.*`，基础公理） | 初等测度论证 | 日志第194–200行 |
| Thm upper（加权上界 $\dimH\le1-\alpha$） | 1 | 已核实（`WeightedFinal.dimH_levelSetα_le`，基础公理） | $0<\alpha<1$ 时 BLR Thm 7 条件(1.6)失效（$\log Q_{j+1}/\log Q_j\to1$），经典质量传输不适用，故为独立覆盖证明 | A§sec:weights + 日志第125行；BLR本地PDF第262–331行已开核 |
| Thm conj:weight（次临界精确维数 $1-\alpha$，含处方极限） | 1 | 已核实（`WeightedExactDim.*`，基础公理；$\alpha=0$ 另有BLR Cor 8旁证） | 同上；FWW齐次Moran界仅作旁证（下界独立Moran构造） | 日志第144–148行；BLR Cor 8本地已开核（$a_{n+1}/a_n\to\infty\Rightarrow\dimH=1$，取中心 $c$ 经 $\lvert\lVert y\rVert-c\rvert\le\lVert y-c\rVert$ 转移） |
| Thm gauge（临界规范 $h_k$：正水平无限$\sigma$-有限、严格子水平零） | 1 | 已核实（`GaugeNull` 3条 + `GaugeExact` 22条 + `GaugeCircle` 53条，基础公理；含 $h_k,g_2,g_\beta$ 显式构造与连续性） | 区别于 CMMS（有限正测度）与 MEA（$k^{-1}(3)$ 恒零或非$\sigma$-有限）；CMMS §5 Thm 3 未能开核（本地PDF乱码），只采信论文转述为“作者声称” | 日志第190–192、201–275、238–328行 |
| Cor exact-gauge（$h_k$ 恰为临界规范，三条） | 1 | 已核实（同上模块） | 同上 | 同上 |
| Cor liminf-gauges（任意规范 $\rho_b(g)$ 三分法，含振荡规范） | 1 | 作者自报，未复跑（`GaugeLiminfComplete.lean` 18条声明**不在**本轮日志中；论文称“直接核查”） | 新颖表述；负搜索未见先例（须明示仅为负搜索） | A§“Lean verification”段自报 |
| Thm trichotomy (i) limsup 水平（字母 $2k+1$，基 $2k+1$） | 1 | 已核实（`FullSpectrumDiscrete` + `GaugeCircle` 二元+Cantor树部分） | 新 | 日志第162–167、251–261行 |
| Thm trichotomy (ii) 无符号精确极限集（普适二元字母 $\{\pm k\}$，基2） | 1 | 已核实（`GaugeCircle` 二元规范族声明群，基础公理） | 新；基2**不依赖** $k$ 为本文核心观察之一 | 日志第251–261行 |
| Thm trichotomy (iii) 有符号精确极限集坍缩为单 $L$-陪集 | 1 | 已核实（`TrichotomyAndPolyExtension` 8条，`…_eq_coset`、`trichotomy_part_iii_complete`，基础公理） | 新 | 日志第361–376行 |
| Thm finite-state-tail（有限状态缺陷尾的 Perron 根规范分类） | 1 | 部分作者自报：仅加权游走恒等式与Perron尺度界在 `FiniteStateGauge.lean`（**不在**本轮日志中）；整体为纸面证明 | 以 $S_k(G)$ 代全字母的推广；MW图定向结果作对比引用（MW未开核） | A§sec:finite-state-tail 末段自报 |
| Lem poly-growth / Lem poly-lattice（一般 $(cj^r+d)$ 增长与内蕴秩2格） | 1（辅助） | 已核实（`PolyRecData.poly_Q_ge_factorial` 等37条中对应部分，基础公理） | 新的一般框架 | 日志第377–392、393–452行 |
| Thm general-rec（全谱 $\frac1c\Z_{\ge0}\cup\{\infty\}$） | 1 | 已核实（`PolyRecData.poly_*defect_approx`、`poly_range_apprExponent` 等，基础公理） | 新 | 日志第404–421行 |
| Thm poly-gauge-trichotomy (iii)（一般递推有符号陪集坍缩） | 1 | 已核实（`…xPlusPoly…`、`poly_trichotomy_part_iii_complete`，基础公理） | 新 | 日志第428–441行 |
| Thm poly-gauge-trichotomy (i)(ii) + Cor poly-exact-gauge + Rem poly-gauge-scale | 1 | 纸面证明（A稿诚实标注；B稿见下表差异项） | 新（含 $1/r$ 对数尺度） | A§“Lean status for §poly-rec” + `verify_poly_recurrence_2b.py`（400/50位 mpmath 旁证，非证明） |
| Thm poly-phase-transition (i)临界维数0/(iii)超临界坍缩 | 1 | 已核实（`poly_dimH_levelSet_finite`、`poly_supercritical_*` 等，基础公理） | 新 | 日志第452–458行 |
| Thm poly-phase-transition (ii)次临界 $1-\alpha/r$ | 1 | 纸面证明 + mpmath 旁证（A稿诚实标注） | 新 | 同上 |
| Thm windows（Hermite窗口：宇称约束维数1、有界增量维数1/2） | 1 | 纸面证明（14条核心代数/条件概率引理已核实：`WindowAndResidueCore.*`，基础公理；完整遍历性与压力论证为纸面证明） | 与 FLLW 相关谱并列（FLLW未开核，只采信论文“相关”定位） | 日志第220–227行 |
| Thm short-ae（短窗口对数频率） | 1 | 纸面证明（条件概率一步不等式与指数矩步已核实：`thm19_*`，基础公理） | 新的停时柱鞅论证 | 日志第223–225行 |
| Thm no-short-dim（发散窗口满维数 $1-\eta\log\varphi$） | 1 | 纸面证明（终端分母界与跨越计数已核实：`thm18_*`、`thm20_*`；Möbius 计数与质量分布为纸面证明） | 新 | 日志第220–222、226–227行 |
| Thm residues（模4最终周期维数 $=\dimH F$，$357/512<\dimH F<359/512$） | 1 | 纸面证明 + **严格整数证书已复跑**（`residue_certificate.py` EXIT 0，下边际 +0.002922128、上边际 +0.006596281，精确分数见§四） | CLU transfer（Prop 2.7方向正确，Table 1上界0.743586已开核）+ Bowen压力公式（CLU §2 Thm 2.3已开核，细微差别见§四） | 日志第228–235行（`thm21_*` 8条：移位、尾距比、 Lipschitz 界、证书可靠性） |

### B稿（伴随稿）独有部分（A稿现行版已删除）

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
|---|---|---|---|---|
| Thm finite-state-quant / Cor finite-state-nondet（定量规范与非确定图算法） | 1 | 纸面证明（B稿自述 “have paper proofs”，B§2005行） | 新；A稿删除 | B§sec:finite-state |
| Thm pressure-frequency / Cor极端频率 / Thm edge-frequency-circulation / 标量端点熵 / Cor变分率 / Cor标量频率 / Thm frequency-strip / Cor half-strip / Cor速度限制 / Thm二阶边界 / Prop方差 / Thm Perron频率高阶界 / Lem tilted涨落 / Thm立方根阈值 / Cor单侧零性 / Lem widening区间 / Thm立方根振幅 | 1 | 纸面证明（B稿自述 “These frequency results have paper proofs”“are paper proofs”，B§2212、2452、2594、2871、3085、3346行） | 新；A稿删除；`SharpWindow.lean` 仅3条代数引理（B§4770–4773行自报，不在审计日志中） | B§sec:finite-state 各子节 |
| B稿摘要对一般多项式递推“临界规范结论 + 次临界维数上下界均已机器验证”的声称 | —（声称层面） | **作者自报，未复跑**：所引 `PolyGaugeAndPhaseTransition.lean`、`PolyWeightedUpper.lean`、`PolyWeightedLower.lean` **无一条声明出现在** `audit_recheck_20261121.log` 中（全文检索仅1条含“PolyWeighted”字样的 `polyWeightedExponent…`，属 `TrichotomyAndPolyExtension`） | A稿已纠正为纸面证明（A§abstract第104–108行、A§poly-rec Lean status段） | B§摘要第99–106行 vs A§对应段 vs 日志检索 |

## 三、定理16（模4最终周期维数，A§`thm:residues`）专项核对

1. **$c_i=(d_i-1)\bmod 4$ 满射步**：论文 A§第2941–2950行。复核：对任意 $x=[0;d_1,d_2,\dots]\in E$，
   取 $c_i=(d_i-1)\bmod4\in\{0,1,2,3\}$，则 $d_i-c_i=4\lfloor(d_i-1)/4\rfloor+1\in\mathcal A=\{1,5,9,\dots\}$，
   且 $(c_i)$ 随 $(d_i\bmod4)$ 最终周期。本审计脚本 E2 对 $d_i\bmod16$ 全体代表元穷举验证通过。**准确。**
2. **统一 Lipschitz 常数 $40/3$**：论文 A§第2865–2937行。复核链条：
   尾距比 $\le\frac{b-a+1}{\,b-a-1\,}\frac{(a+1)b}{a(b+1)}$，$d=b-a\ge4$ 时第一因子 $\le5/3$（$d=4$ 取等、单调递减），
   第二因子 $=\frac{a+1}{a}\frac{b}{b+1}<2$，故尾比 $<10/3$（论文第2906–2910行注记与端点 $a=1,b=5$ 的 $50/18<10/3$ 一致）；
   公共前缀 M\"obius 映射导数满足 $1/(4q^2)\le|M'|\le1/q^2$，移位后 $q_{\rm new}\ge q$（continuant 逐元递增），
   故前缀因子 $\le4$，得 $40/3=4\times10/3$，且**不依赖**位移序列 $\mathbf c$。脚本 E1 网格验算上确界 $=50/18\approx2.778<10/3$。**准确。**
   Lean 侧 `thm21_tail_distance_ratio_le`、`thm21_prefix_factor_bounds` 在日志中（基础公理）。**准确。**
3. **CLU §2 Theorem 2.3 压缩条件引用**：本地 `CLU_1805_11904.pdf` 第309行
   “Theorem 2.3 ([24]). If $S=\{\varphi_e\}_{e\in E}$ is a conformal IFS, then $h_S=\dim_H(J_S)=\sup\{\dim_H(J_F)\}$”，
   及第298–302行 Prop 2.2（压力严格递减、连续、$P(t)\to-\infty$）。论文用“$P(s,\mathcal D)$ 连续严格递减、唯一零点 = 维数”是对 Thm 2.3 + Prop 2.2 的联合应用，
   表述实质正确，唯严格引文应为“Thm 2.3（经由 Prop 2.2 的零点读法）”——**轻微注记，非错误**。
   两字母分支导数 $|(f_a\circ f_b)'|=(ab+ax+1)^{-2}\le1/4$（因 $f_1'(0)=-1$ 单字母系非一致压缩，转两字母的动机正确）。**准确。**
4. **Table 1 / Prop 2.7 引用**：本地PDF第149–150行 `E1mod3={1,4,7,...}` 配 `[0.743520, 0.743586]`，
   论文“Table 1界0.743586”**准确**；Prop 2.7（第622行起：递增双射 $s:E\to F\Rightarrow\dimH(J_F)\le\dimH(J_E)$），
   论文用 $1+3k\mapsto1+4k$ 把 $\{1,4,7,\dots\}$ 上界转给 $\{1,5,9,\dots\}$，**方向正确**。

## 四、FWW 与其他引用抽查（只采信实际打开的页面）

| 引文 | 核查状态 | 实际打开看到的内容 |
|---|---|---|
| FWW（Feng/Wen/Wu, Sci. China Ser. A 40 (1997), 475–482） | **已核对一致** | 本次实际打开 Springer 出版页：作者 Dejun Feng, Zhiying Wen & Jun Wu；刊名 Science in China Series A: Mathematics；Volume 40, pages 475–482 (1997)；DOI 10.1007/BF02896955。与论文 `\bibitem{FWW}` 三作者、卷期页、DOI 逐字一致。**但**论文正文对FWW的引用是宽松的（“下界亦可从FWW齐次Moran界读出”，A§1088–1092行），FWW只作旁证，不影响主证明的自足性 |
| BLR（Bugeaud/Liao/Rams, Proc. Edinb. Math. Soc. 62 (2019), 505–521） | **已核对一致（本地PDF）** | 本地PDF第331行起 Cor 8：$a_{n+1}/a_n\to\infty$ 则 $\dimH\{x:\lim\|a_nx-y_n\|=0\}=1$。论文取 $a_n=Q_n$（$Q_{n+1}/Q_n\to\infty`成立，脚本E3复核比值$\to4j$）、中心 $y_n\equiv c$ 的用法正确；作者/卷期页/DOI（S0013091518000585）/arXiv号与论文条目一致 |
| MEA（Moreira/Erazo/Angelini, arXiv:2511.10328v3） | **已核对一致（本地PDF）** | 本地PDF标题页：作者 CARLOS GUSTAVO MOREIRA, HAROLD ERAZO, NICOLAS ANGELINI；arXiv:2511.10328v3；摘要“对 $k^{-1}(3)$ 的广义Hausdorff测度恒为零或非$\sigma$-有限”。论文“either zero or non-$\sigma$-finite for every dimension function”转述准确；B稿历史错题（dimension→measure）按checklist已修正 |
| CLU（Chousionis/Leykekhman/Urbański, Trans. AMS 373 (2020), 1009–1042） | **已核对一致（本地PDF arXiv:1805.11904v1）** | 作者三人、Thm 2.3、Prop 2.2/2.7、Table界值均见上文§三；论文条目卷页年份 arXiv号未在本审计打开的v1首页之外的页面核验，标**未核到**（条目本身沿用B稿已刊信息） |
| FLLW / KL / LimaMoreira / Moreira / MW / Falconer / BV / CMMS / BDS | **未核到**（本次未打开；BDS为引KL转引，KL原文未开） | 论文中的相关数学转述（如KL常数、BLR条件失效分析）按“作者声称”处理，不采信为已核实 |
| Phase1（自引形式化项目） | 日志旁证 | `Classification`/`SpectralGap` 等声明在日志中确为基础公理、零sorry；`deltaSel` 白名单公理已转为定理（`DeltaSign.*` 在日志第112–116行，基础公理） |

## 五、作者声称 vs 实际成立（差异清单）

1. **B稿摘要夸大一般多项式递推的Lean覆盖**（B§99–106行：“临界规范结论、次临界维数上下界均机器验证”）：
   实际 `audit_recheck_20261121.log`（349条）中**不存在** `PolyGaugeAndPhaseTransition`、`PolyWeightedUpper`、`PolyWeightedLower`、`GaugeLiminfComplete`、`FiniteStateGauge`、`SharpWindow` 任一模块的声明。
   **A稿已纠正**（A§102–111行明确列出 (i)(ii)/推论/注记/(ii) 为纸面证明 + mpmath旁证）。投稿必须以A稿口径为准，B稿摘要须同步修改。
2. **B稿验证节同时存在新旧两种口径**（B§4666–4669行称三模块“verified”，B§4796–4801行又把有限状态正测度下界等列为未机器验证），自洽性差；A稿已统一。**B稿须清理。**
3. **Cor liminf-gauges 与 Thm finite-state-tail 的Lean部分**：两稿均有“已验证/直接核查”表述，但均不在本轮日志中 → 按形式化纪律降为**作者自报，未复跑**，不得在投稿信中称为已审计。
4. **CLU Thm 2.3 引文**：实质正确但应补注经由 Prop 2.2 的零点读法（轻微注记，非实质错误）。
5. **FWW引用**：书目信息本次开页核对无误；但正文“可从FWW读出下界”属宽松旁证，主证明自足，不构成依赖风险。
6. **e+π相关表述**：两稿摘要/验证节均明确“does not prove / does not resolve the irrationality of $e+\pi$”（A§114–115、A§3245–3248行；B§115–116、4738–4741行），
   Rem `linear-indep` 把 “$\Lam(B\pi)>0$” 严格等价于 $1,e,\pi$ 线性无关（开放问题）并声明“Nothing in this article decides it”——**完全符合事实基线，无换靶夸大**。

## 六、真正新增了什么 / 没做到什么

**真正新增（无条件，均经纸面证明；Lean部分见上表“已核实”者）：**
- (a) $e$-选子列加权谱的完全离散化 $\Lam(\R)=\frac14\Z_{\ge0}\cup\{\infty\}$ 与无限等距空隙 ladder；
- (b) 临界规范 $h_k(1/Q_n)=(2k+1)^{-n}$：正水平无限$\sigma$-有限、严格子水平零、开弧局部无限、任意规范 $\liminf$ 三分法（含振荡规范）；
- (c) 正水平的三分裂：limsup（基 $2k+1$）/ 无符号精确极限（普适基2，不依赖 $k$）/ 有符号精确极限（单 $L$-陪集、可数）；
- (d) 一般 $(cj^r+d)$ 递推的完整平行理论：谱 $\frac1c\Z_{\ge0}$、内蕴秩2格、$1/r$ 对数尺度、相变 $1-\alpha/r$、超临界坍缩；
- (e) 全部有限水平集维数0 + 次临界精确维数 $1-\alpha$（Lean上下界）；
- (f) Hermite窗口定理（宇称维数1/有界增量维数1/2/短窗口对数频率/发散窗口满维数）；
- (g) 模4最终周期维数 $=\dimH\{1\bmod4\}$ + 严格区间证书 $(357/512,359/512)$（已复跑）；
- (h) 有限状态/频率 machinery（**仅B稿**，纸面证明）。

**没做到（两稿均未做，A稿已诚实声明；B稿摘要除外，见差异1）：**
- (1) $e+\pi$（及 $e\pi$、$e-\pi$ 等）的无理性/超越性——**毫无推进**，两稿均书面承认；
- (2) 一般 $(cj^r+d)$ 的临界规范测度结论与次临界 $1-\alpha/r$ 维数等式——仅纸面证明 + mpmath旁证，未机器验证；
- (3) 窗口/留数定理的完整遍历性与压力论证、有限状态尾的正测度下界、B稿全部频率/压力/循环/立方根 machinery——纸面证明，无独立裁判复核（B§4802–4805行自认“未被独立人类裁判检查”）；
- (4) CMMS §5 Thm 3、FLLW、KL原文、LimaMoreira、MW、Falconer、BDS——本次审计未打开，不采信其转述精度；
- (5) “负搜索未发现先例”≠“已证明无先例”：(a)–(h) 的新颖性表述须保留此限定。

## 七、两稿关系与差异

- **高度重合**：B稿伴随稿与A稿现行版共享全部核心定理陈述、证明与Lean状态（分类/隙/离散化/规范/三分法/多项式递推/窗口/留数），文字几乎逐段一致。
- **A稿 = 精简现行版**：删除B稿整个频率 machinery（finite-state-quant、pressure-frequency、edge-frequency、frequency-strip、Perron高阶界、立方根阈值/振幅等约20个定理/命题环境），并把一般多项式递推的Lean声称纠正为纸面证明。
- **B稿 = 伴随稿**：多出频率/压力/循环 machinery（均为纸面证明），但摘要的Lean覆盖声称超出审计日志，投稿前必须按A稿口径修正。
- **数值证书**：两稿共用 `residue_certificate.py`，本轮复跑 EXIT 0，边际与论文印刷值逐字一致。

## 八、复算留痕

- `verification/paper2_audit_20261121_check.py`：E1（尾比 $<10/3$，网格上确界 $50/18$，$40/3$ 成立）、
  E2（$c_i$ 满射穷举）、E3（$Q_{j+1}/Q_j/(4j)\to1$，$j=399$ 时 $1.00125$；$\log Q_n/(n\log n)$ 从 $1.16$ 降至 $1.064$，与 $n\log n+O(n)$ 相容）、
  E4（下边际 $7204302042904417931/2465429597500000000000\approx0.00292213>0.0029$；
  上边际 $65040245891337248463/9860138780000000000000\approx0.00659628>0.0065$；宽度 $1/256$）——**全部 PASS**。
- `verification/residue_certificate.py` 本轮复跑：`lower … +0.002922128 … upper … +0.006596281 … Certified: 357/512 < dimension < 359/512`，EXIT 0。
- 日志统计（`Select-String` 实测）：以 `'` 起始的审计声明行 **349条**，含 `sorry` 的行 **0条**；
  含白名单公理（`e_transcendental`/`pi_transcendental`/`mu_e_eq_two`）的行 23行（含续行），对应论文自报的22条 Phase-1 遗留声明；
  `GaugeLiminfComplete|FiniteState|PolyGauge|PolyWeighted|SharpWindow` 检索命中仅1条（误含 `polyWeightedExponent`，属 `TrichotomyAndPolyExtension`）——即这些模块**不在**本轮日志中。
