# $e+\pi$ 无理性研究与连分数谱/维数理论完整私有归档（2026-11-23 最新版）

> **一句总判断**：本仓库完整归档截至 **2026-11-23** 的最新研究全貌，涵盖两篇修订重编主论文（**Paper 1** 72 页 + **Paper 2** 63 页，洁净 `pdflatex` 0 错误 / 0 未定义引用 / 0 Overfull `\hbox`，且主稿与 `split/` 三轨拆分源码保持逐字节/0 未定义引用同步）、全量 Lean 4 `v4.35.0` 形式化工程（`lake build EpiFormal` **9179 jobs** EXIT 0，全库 **344** 个 `.lean` 文件，0 逃逸关键字、`sorryAx = 0`；核心 `Audit.lean` **937/937** 条 `#print axioms` 严格双射 [= **914** 基础公理（含 **5** 条零公理）+ **23** 论文一经典白名单 + **0** 项目自加公理]，独立残差证书审计 `AuditResidueCert.lean` **27/27** 条仅用基础公理，独立多残差推广审计 `AuditResidueMultiAsymptotic.lean` **24/24** 条仅用基础公理，合计 **988** 条 Layer A 审计声明）、全部符号/高精度区间/精确整数转移算子与 32 位 Chebyshev 配置核验脚本与日志、CMMS 一次文献核查，以及全部研究过程记录与历史版本快照（全局架构导航见 [`REPOSITORY_STRUCTURE.md`](REPOSITORY_STRUCTURE.md)）；同时严格遵循 [`AGENTS.md`](AGENTS.md) 诚实基线——**$e+\pi$ 的无理性（及 $e\pi, e-\pi, \pi/e, \pi^e$ 单个的无理性）仍是公开问题，本仓库未证明 $e+\pi$ 无理、有理或超越。**

---

## 一、成果诚实分类与逐项对照表（遵循 `AGENTS.md` 五分法）

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| 论文二：全谱离散化 $\frac14\mathbb{Z}_{\ge0}\cup\{\infty\}$、正能级三分法（含 $L$-陪集坍缩）、临界/二值精确 Hausdorff 规范（$\mathbb{R}$ 与 $\mathbb{R}/\mathbb{Z}$）、一般 $(cj^r+d)$ 递推与次临界维数相变 $1-\alpha/r$、以及 `thm:finite-state-tail` 带标记分量临界规范全结论（$\mathbb{R}$ 与 $\mathbb{T}$） | 无条件新结果 + Lean 4 Layer A 机器验证 | **已核实**（仅依赖 Lean 基础三公理 `propext`, `Classical.choice`, `Quot.sound`；0 `sorryAx`；0 项目自加公理；新增 [`FiniteStateComplete.lean`](epi_formal/EpiFormal/FiniteStateComplete.lean) 12 条声明完整闭环 `thm:finite-state-tail`） | 在 Kraaikamp–Liardet 零能级准则（[BDS] Lemma 4.1）基础上的独立谱离散化、正能级三分法、临界规范与一般递推维数理论 | [`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex)、[`GaugeCircle.lean`](epi_formal/EpiFormal/GaugeCircle.lean)、[`TrichotomyAndPolyExtension.lean`](epi_formal/EpiFormal/TrichotomyAndPolyExtension.lean)、[`FiniteStateComplete.lean`](epi_formal/EpiFormal/FiniteStateComplete.lean) |
| 论文二新拓展（一）：**任意增长商三项递推** $Q_{j+1}=A_jQ_j+Q_{j-1}$ ($A_j\in\mathbb{Z}_{\ge2}, A_j\to\infty$) 的普适离散谱 $\mathbb{Z}_{\ge0}\cup\{\infty\}$、Kraaikamp–Liardet 误差比恒等 $\Lambda_G^{\mathrm{KL}}=\Lambda_G$、临界/二进量规与三重分裂（`thm:growing-rec-spectrum`）、亚临界维数畸变公式 $\dim_{\mathrm{H}} E_{G,\tau}(t)=\frac{1-\tau}{1+\tau\gamma_{\sup}}$ ($0\le\tau<1, \gamma_{\sup}=\limsup\frac{\log A_j}{\log Q_j}\in[0,\infty]$) 及超临界（$\tau>1$）在 $\tau_{\mathrm{crit}}=1+1/\gamma_{\sup}$ 处从秩-2 格 $L_G$ 到秩-1 有理子格 $\frac{1}{g}\mathbb{Z}$ 的二次坍缩相变与三类典型增长相图（`thm:growing-rec-dim-phase`, `cor:growing-rec-three-regimes`） | 无条件新结果 + Lean 4 Layer A 机器验证 | **已核实**（新增 [`GeneralGrowingRec.lean`](epi_formal/EpiFormal/GeneralGrowingRec.lean) 21 条 + [`GeneralGrowingDim.lean`](epi_formal/EpiFormal/GeneralGrowingDim.lean) 29 条声明，仅基础公理，0 `sorryAx` + [`verify_paper2_extensions.py`](verification/verify_paper2_extensions.py) 50 位验证） | 完全去除 $A_j$ 的多项式函数形式假设，首次揭示当 $\gamma_{\sup}>0$（如双指数 $A_j=2^{2^j}, \gamma_{\sup}=1, \tau_{\mathrm{crit}}=2$）时亚临界 Hausdorff 维数畸变因子 $(1+\tau\gamma_{\sup})^{-1}$ 与超临界秩-2 格内部二次相变 | [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex) §6.4、[`GeneralGrowingRec.lean`](epi_formal/EpiFormal/GeneralGrowingRec.lean)、[`GeneralGrowingDim.lean`](epi_formal/EpiFormal/GeneralGrowingDim.lean) |
| 论文二窗口与一般模残差体系：`thm:windows` 全四条、`thm:short-ae` 显式常数 $c=(1-e^{-1})/160$ 零尾率、`thm:no-short-dim` 完整合取（$\dim_{\mathrm{H}}=1\wedge\operatorname{Leb}=0$），以及 `thm:residues`/`thm:residues-general`（一般模 $m\ge2$ Lipschitz 移位与最终周期不变性、转移算子 Hausdorff 维数桥接、$\dim_{\mathrm{H}} F_{m,r}>1/2$、$\dim_{\mathrm{H}} F_{4,1}\le 4/5$ 与有限步矩阵证书可靠性） | 无条件新结果 + Lean 4 Layer A 机器验证（结构与解析主干全闭环） | **已核实**（仅 Lean 基础三公理；新增 [`WindowShortAeRealize.lean`](epi_formal/EpiFormal/WindowShortAeRealize.lean) 14 条、[`ResidueModGeneral.lean`](epi_formal/EpiFormal/ResidueModGeneral.lean) 7 条、[`TransferOperatorDim.lean`](epi_formal/EpiFormal/TransferOperatorDim.lean) 11 条全通 `Audit.lean`） | 对 $e$ 收敛子尺度窗口连分数商约束集与一般模残差集 $F_{m,r}$ 建立端到端（`GenContFract.of` + `hausdorffMeasure`）机器证明框架 | [`WindowShortAeRealize.lean`](epi_formal/EpiFormal/WindowShortAeRealize.lean)、[`ResidueModGeneral.lean`](epi_formal/EpiFormal/ResidueModGeneral.lean)、[`TransferOperatorDim.lean`](epi_formal/EpiFormal/TransferOperatorDim.lean)、[`WindowBoundedUpper.lean`](epi_formal/EpiFormal/WindowBoundedUpper.lean) |
| 论文二新拓展（二）：**金属连分数预解式恒等式、全模 $m\ge2$ 全局严格维数分离与倒数 Fibonacci 常数二阶渐近展开**（`thm:residues-asymptotic`）：精确预解式分支恒等式 $(r+x)^{-2s}V_{r,s}(1/(r+x))=V_{r,s}(x)-1$、对**一切**整数模 $m\ge2$ 无条件成立的全局严格分离 $\dim_{\mathrm{H}} F_{m,m}<\dim_{\mathrm{H}} F_{m,1}=\dim_{\mathrm{H}} E_m$、二阶渐近展开 $\dim_{\mathrm{H}} F_{m,r}=\frac12+\frac{C_r}{2m}-\frac{C_r^2\log m}{2m^2}+O(m^{-2})$（其中 $C_r=\sum_{n=0}^\infty 1/q_n(r)$，$C_1=\psi_{\mathrm{Fib}}=\sum_{k=1}^\infty 1/F_k\approx3.3598856662$ 为倒数 Fibonacci 常数，$\dim_{\mathrm{H}} F_{m,m}=\frac12+\frac{1}{2m}-\frac{\log m}{2m^2}+O(m^{-2})$）、维数超出比 $\frac{\dim_{\mathrm{H}} E_m-1/2}{\dim_{\mathrm{H}} F_{m,m}-1/2}\to\psi_{\mathrm{Fib}}$ 及关于余数 $r$ 的最终严格单调递减性 | 无条件结果（已知一般扰动方法的显式实例：Das–Fishman–Simmons–Urbański, Selecta Math. 29 (2023) 定理 4.1；全模严格分离为窄的新结论）+ Lean 4 Layer A 机器验证 | **已核实**（新增 [`ResidueAsymptotic.lean`](epi_formal/EpiFormal/ResidueAsymptotic.lean) 15 条声明，仅基础公理，0 `sorryAx` + [`verify_paper2_extensions.py`](verification/verify_paper2_extensions.py) 50 位验证） | 将有限模 $m\le6$ 的数值严格分离提升为对所有 $m\ge2$ 的无条件定理。大 $m$ 渐近落在 DFSU 定理 4.1（在有限系统上添加导数很小的生成元）的适用范围内；该文没有处理等差数字集，也没有给出 $C_r$。首项常数 $C_r$ 即该框架中 $1/\bar c$ 在 $S=\{r\}$ 的取值；$\log m/m^2$ 系数与 Hensley 的 $72/\pi^4=2(6/\pi^2)^2$ 同构。**负搜索**（范围见 [`paper2_novelty_review_20261125.md`](verification/paper2_novelty_review_20261125.md) §0）未见以 $C_r$ 或 $\psi_{\mathrm{Fib}}$ 作为剩余类数字集维数渐近常数的先例，也未见全模 $m\ge2$ 严格分离的先例；负搜索不等于不存在。它没做到：没有给出新方法，没有推进 $e+\pi$ | [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex) §7.4、[`ResidueAsymptotic.lean`](epi_formal/EpiFormal/ResidueAsymptotic.lean)、[`paper2_novelty_review_20261125.md`](verification/paper2_novelty_review_20261125.md) |
| 论文二残差表全表 Lean 化（2026-11-23）：`tab:residues-general` 换为 N=512 证书（10 个区间宽度均 1/512，$F_{4,1}$ 上界 359/512→**179/256**），20 个单侧闭界 $\mathrm{lower}\le\dim_{\mathrm H}F_{m,r}\le\mathrm{upper}$ 与 5 条严格分离 $\dim_{\mathrm H}F_{m,m}<\dim_{\mathrm H}F_{m,1}$（$2\le m\le6$）均为 Lean 定理；通用可靠性定理 `dimH_le_of_certU`/`le_dimH_of_certL` 对任意参数成立 | 有限计算（10 个具体集合）+ 无条件形式化可靠性定理 | **已核实**（本机 Lean 4.35.0 + Mathlib 实跑：201 个 core 证书模块 `decide +kernel` 全通过、`ResidueCertTable` `lake build` EXIT 0；27 条声明仅基础三公理；未用 `native_decide`）。开区间严格性仍依赖引用的 Bowen 公式，未形式化 | 负搜索未找到证明助手内核检查的连分数康托集维数数值界先例（仅网页检索，范围见记录）；数值方法与论文原证书相同 | [`residue_certgen_lean_20261123.md`](verification/residue_certgen_lean_20261123.md)、[`ResidueCertTable.lean`](epi_formal/EpiFormal/ResidueCertTable.lean)、[`AuditResidueCert.lean`](epi_formal/AuditResidueCert.lean) |
| 论文二新拓展（三，2026-11-23）：**多残差连分数相变、无 Bowen 庞加莱横坐标、欧拉常数 $\gamma$ 三阶渐近与超临界 $\Theta(m^{-2s_0})$ 速率**（`thm:multi-residue-asymptotic`）：有限字母表无 Bowen 维数公式 $\dim_{\mathrm H} E_S=s_0(S)$；一般多残差族 `multiResidueSet m S B`（$F_{m,S,B}$）的全局相变 $\lim_{m\to\infty}\dim_{\mathrm H} F_{m,S,B}=\max(1/2, s_0(S))$ 及二元素见证 $S=\{2,3\}$（次临界 $<1/2$）与 $S=\{1,2\}$（超临界 $\ge 51/100$）；初等 $\zeta(1+\varepsilon)=\frac{1}{\varepsilon}+\gamma+O(\varepsilon)$ 展开；次临界主三阶渐近至 $O((\log m)^2/m^3)$（含 $m^{-2}$ 精确系数 $\frac12 d^2 C_S(\gamma C_S-C_S')$ 及 $r\ge1$、$r=m$、$\{2,3\}$ 推论与比值收敛）；超临界 $s_0(S)>1/2$ 双向幂律速率 $K_1 m^{-2s_0}\le \dim_{\mathrm H} F_{m,S,B}-s_0\le K_2 m^{-2s_0}$ | 分项：(i)(iii) 为经典结果（Bowen 公式的 Poincaré 级数形式、$\zeta$ 的 Laurent 展开）的自含证明与形式化；(ii) 的超临界情形与 (v) 的上界是 Heinemann–Urbański (2002) 估计的推论，$S=\emptyset$ 情形是 Good (1941) 的推论；(ii) 次临界 $S\ne\emptyset$、(iv) 三阶系数、(v) 下界是已知方法（DFSU 定理 4.1）的显式实例，属无条件结果 + Lean 4 Layer A 机器验证 | **已核实**（本机 Lean `v4.35.0`：`lake build EpiFormal.ResidueMultiAsymptotic` **9098 jobs** EXIT 0，`AuditResidueMultiAsymptotic.lean` **24/24** 条公开定理仅基础三公理，0 `sorryAx` + [`verify_residue_multi_asymptotic.py`](verification/verify_residue_multi_asymptotic.py) 32 位验证 `ALL CHECKS PASSED`；**2026-11-24 第二台机器（Google Colab）从公开仓库全新克隆复建，24 条输出与日志逐条一致**，见 [`colab_rebuild_audit_20261124.md`](verification/colab_rebuild_audit_20261124.md)） | (i) 有精确先例（Mauldin–Urbański 1996；见 CLU 定理 2.3）；(v) 上界有先例（Heinemann–Urbański 2002，见 CLU 定理 2.4，结合 CLU 命题 2.6）；整体渐近落在 DFSU 定理 4.1 的适用范围内（DFSU 未处理等差族）。三阶系数 $\frac12d^2C_S(\gamma C_S-C_S')$：**负搜索**未见先例（范围见 [`paper2_novelty_review_20261125.md`](verification/paper2_novelty_review_20261125.md) §0；负搜索不等于不存在）。定理号按 arXiv 版本，出版版编号未核到 | [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex) §7.5、[`ResidueMultiAsymptotic.lean`](epi_formal/EpiFormal/ResidueMultiAsymptotic.lean)、[`AuditResidueMultiAsymptotic.lean`](epi_formal/AuditResidueMultiAsymptotic.lean)、[`推广1_多残差相变与欧拉常数三阶渐近Lean4记录_20261123.md`](verification/推广1_多残差相变与欧拉常数三阶渐近Lean4记录_20261123.md)、[`paper2_novelty_review_20261125.md`](verification/paper2_novelty_review_20261125.md) |
| 论文二 Remark `rem:fourth-term`（2026-11-24）：标量模型 $\varepsilon m=(\Gamma-\varepsilon\Gamma')(1+\gamma\varepsilon)m^{-\varepsilon}$（$\Gamma=dC_S$）的符号展开与已证三阶渐近逐项一致，并给出**猜想**第四项 $+\frac34\Gamma^3(\log m)^2/m^3$；数值上 $m^3(\dim_{\mathrm H}-\text{模型})/(\log m)^2$ 在 10 例中 9 例随 $m$ 递减（$S=\{1,3\}$ 在 $m\le16384$ 仍处前渐近区） | 条件结果（启发式猜想）+ 有限计算（非严格数值佐证） | 数值已复现（两套独立配置法脚本在 $m=4096,16384$ 一致到 $<10^{-15}$；Colab 70 项结果 SHA-256 与本地转录一致）；**猜想本身未证明** | 未做文献检索，不声称首创；它没做到：未证明第四项，也未证明余项阶 | [`fourth_term_fit_20261124.py`](verification/fourth_term_fit_20261124.py) / [`.log`](verification/fourth_term_fit_20261124.log)、[`asymptotic_residues_check_20261123.log`](verification/asymptotic_residues_check_20261123.log)、[`asymptotic_largem_crosscheck_20261124.jsonl`](verification/asymptotic_largem_crosscheck_20261124.jsonl)、[`patch_fourth_term_remark_20261124.py`](paper2_spectral_gap_dimension/patch_fourth_term_remark_20261124.py) |
| 论文一：仿射窗口显式周期 $2B|C|$、黄金比轨道有限谱与 $B=1\text{--}6$ / 四类多尺度有理端点刚性；全部 8 个原独立 Lean 辅助模块（共 29 条声明）并入主工程与统一审计 | 无条件模型/归约结果 + 已有辅理统一机器复核 | **已核实**（72 页重编 0 错误/0 警告；原独立 8 模块——`GoldenHeadCutoff`, `GoldenAffineEndpoint`, `AffineWindowAudit`, `DigitTailBound`, `DensityCube`, `OrbitAndFlow`, `ResearchAdvance`, `TraceMarkov`——全部并入 `EpiFormal.lean` 与 `Audit.lean`，共 29 条声明仅用基础公理） | 用 Bugeaud 二次 Mobius 恒等式研究 $A/B-e$ 与 $(A+Ce)/B$ 模型；模型与窗口研究**不解决 $e+\pi$ 无理性** | [`paper1_e_plus_pi.pdf`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf)、[`GoldenHeadCutoff.lean`](epi_formal/EpiFormal/GoldenHeadCutoff.lean)、[`GeneralEndpointRigidity.lean`](epi_formal/EpiFormal/GeneralEndpointRigidity.lean)、[`EpiFormal.lean`](epi_formal/EpiFormal.lean) |
| 论文一 `prop:denominator-bounds`（2026-11-24）：Arb 球算术严格包络 + 区间内最简有理数，得**若 $x\in\{e+\pi,e\pi,\pi-e,\pi/e\}$ 且 $x=p/q$，则 $q\ge10^{500018}$**（$D=10^6$，本机与 Colab 两台机器输出逐项一致）；并以严格包络复核 OEIS A058651 全部 20000 个部分商（$q_{19998}$ 有 10149 位） | 有限计算或有限排除（只排除有限范围） | **已核实**（两机复现；自检 12/12 PASS） | 负搜索未见以“若 $e+\pi=p/q$ 则 $q>N$”形式发表的界（检索范围：OEIS、MathWorld、Wikipedia、三次网络检索；**负搜索≠不存在**）；Bailey 1988 摘要排除了 $e+\pi$ 满足次数 $\le8$、系数欧氏范数 $\le10^9$ 的代数方程（只核了摘要）。它没做到：**不涉及无理性**，更大分母的有理数未被排除，$e+\pi$ 仍开放 | [`rational_exclusion_bound_20261124.py`](verification/rational_exclusion_bound_20261124.py)、[`exclusion_runs_20261124/`](verification/exclusion_runs_20261124/)、[`oeis_a058651_crosscheck_20261124.py`](verification/oeis_a058651_crosscheck_20261124.py) / [`.log`](verification/oeis_a058651_crosscheck_20261124.log)、[`patch_denominator_bounds_20261124.py`](paper1_e_plus_pi/01_main_paper/patch_denominator_bounds_20261124.py) |
| 论文一：$e+\pi$ 无理性归约、Flint Hills 条件桥接、Alekseyev 方向（$\text{收敛}\Rightarrow\mu(\pi)\le 5/2$）、逃逸约化（P1）与四路障碍分析 | 等价改写/换靶 + 条件结果 + 障碍分析 + Lean 4 机器验证 | **已核实**（23 条经典定理推导显式依赖 3 条经典白名单公理；Meiburg Flint Hills 情况与 Alekseyev 方向已机器形式化，无项目自加公理） | 仅做条件桥接、等价换靶（如 P1 晶格逃逸）或排除特定构造；明确不宣称解决原问题或“更接近证明” | [`FlintHills.lean`](epi_formal/EpiFormal/FlintHills.lean)、[`MeiburgConvergence.lean`](epi_formal/EpiFormal/MeiburgConvergence.lean)、[`Alekseyev.lean`](epi_formal/EpiFormal/Alekseyev.lean)、[`Escape.lean`](epi_formal/EpiFormal/Escape.lean) |
| 符号、区间与精确整数/Chebyshev 数值核验脚本（`verify_round3.py`、`verify_round4.py`、`residue_certificate_general_N512.py`、`verify_residue_multi_asymptotic.py` 等） | 有限计算或有限排除（Python 数值核验） | **已核实**（SymPy `12/12` PASS；450 位 `mpmath.iv`；`residue_certificate_general_N512.py` 以 $N=512$, $S=10^{13}$, $K\in\{120,\dots,258\}$ 精确整数算术认证 10 组 $N=512$ 区间与严格隙 [其闭区间已在 `ResidueCertTable.lean` 复跑]，`verify_residue_multi_asymptotic.py` 32 位 Chebyshev 配置法全面复核 10 组次临界三阶渐近与 `{1,2}`/`{1,2,3}` 超临界速率并 `ALL CHECKS PASSED`） | 对有限分母、有限窗口与有限格点算子给数值佐证或有限精确整数计算；多残差 32 位 Chebyshev 数值结果明确标为佐证而非证明 | [`verify_round3.py`](verification/verify_round3.py)、[`verify_round4.py`](verification/verify_round4.py)、[`residue_certificate_general_N512.py`](verification/residue_certificate_general_N512.py)、[`verify_residue_multi_asymptotic.py`](verification/verify_residue_multi_asymptotic.py) |
| CMMS 一次文献核查与论文二全篇纠偏 | 文献核查与复现 | **已核实**（下载并逐页核对 *Pacific J. Math.* 217(1) (2004), pp. 45–59 官方刊出全文，确认 §5 主定理为 **Theorem 3** 而非误写的 Theorem 5；论文二三处引文已全部更正重编） | Cabrelli–Mendivil–Molter–Shonkwiler, *Pacific J. Math.* 217(1) (2004), 45–59, `doi:10.2140/pjm.2004.217.45`（pp. 57–58, §5 Theorem 3） | [`cmms_citation_check_20261122.md`](verification/cmms_citation_check_20261122.md)、[`CMMS_PJM_2004_217_45.pdf`](verification/reference_pdfs/CMMS_PJM_2004_217_45.pdf) |

---

## 二、三层公理依赖实测清单（`verification/audit_final_20261122.log`）

> **2026-11-23 独立机器复现（已核实）**：在 Google Colab（8 vCPU / 50 GB）上从公开仓库全新克隆（提交 `3563f85`），全量 `lake build` 退出码 0（21 分 14 秒），`Audit.lean` 的 937 条 `#print axioms` 输出与下述日志**逐条一致（0 条差异）**，`check_audit_reconcile.py` 全部通过；残差证书层 `AuditResidueCert.lean` 27 条仅基础三公理。详见 [`verification/colab_rebuild_audit_20261123.md`](verification/colab_rebuild_audit_20261123.md)。按 `AGENTS.md` §5，下列 Lean 结论据此由“作者自报”改为**已核实**。

> **2026-11-24 第二次独立机器复现（已核实）**：对含 `ResidueMultiAsymptotic.lean` 的提交 `d920a81` 在 Colab High-RAM CPU（8 vCPU / 50 GB）全新克隆，`lake build` 退出码 0（16 分 41 秒）；`Audit.lean` 937 条、`AuditResidueCert.lean` 27 条、`AuditResidueMultiAsymptotic.lean` 24 条输出均与仓库日志逐条一致，后两者仅基础三公理；`check_audit_reconcile.py` 全部通过。详见 [`verification/colab_rebuild_audit_20261124.md`](verification/colab_rebuild_audit_20261124.md)。

经 [`epi_formal/`](epi_formal/)（Lean `v4.35.0` + Mathlib `v4.35.0`）执行 `lake build EpiFormal`（**9179 jobs**，EXIT 0）与 `lake env lean Audit.lean`（EXIT 0），并由 [`verification/check_audit_reconcile.py`](verification/check_audit_reconcile.py) 自动对账核实：

- **审计声明总计**：**937 条**（`Audit.lean` 与原始日志 **937/937** 严格双射，重复 0）
- **`sorryAx` 计数**：**0**
- **逃逸关键字全库扫描**（扫描全库 **344** 个 `.lean` 文件中的 `sorry` / `admit` / `native_decide` / `implemented_by` / `extern` / `unsafe` / `partial` / `opaque`）：**0 命中**
- **两项独立 Layer A 扩展审计入口（不修改 `Audit.lean` 937 条双射）**：
  - `AuditResidueCert.lean`（[`verification/residue_certgen_lean_20261123.md`](verification/residue_certgen_lean_20261123.md)）：**27 条**（$m\in\{2,\dots,6\}$ 共 20 条闭界 + 5 条严格分离 + 2 条通用可靠性），**27/27** 仅用 Lean 基础三公理，0 `sorryAx`；
  - `AuditResidueMultiAsymptotic.lean`（[`verification/audit_residue_multi_asymptotic_20261123.log`](verification/audit_residue_multi_asymptotic_20261123.log)）：**24 条**（覆盖 Part 1–6 全核心定理，`lake build EpiFormal.ResidueMultiAsymptotic` **9098 jobs** EXIT 0），**24/24** 仅用 Lean 基础三公理，0 `sorryAx`。
- **第 1 层（仅 Lean 基础公理：`propext`, `Classical.choice`, `Quot.sound`）**：**914 条**
  - 含 5 条零公理（空公理列表 `[]`）声明；
  - 含 2026-11-22 新增/并入全部 **291 条** 审计声明（含新闭合与拓展 7 模块 `WindowShortAeRealize` [14]、`ResidueModGeneral` [7]、`TransferOperatorDim` [11]、`FiniteStateComplete` [12]、`ResidueAsymptotic` [15]、`GeneralGrowingRec` [21]、`GeneralGrowingDim` [29]，`WindowBoundedUpper` [21] 与并入的 8 个论文一辅助模块 [29] 等），非基础公理数为 **0**。
- **第 2 层（经典白名单公理，全库仅此 3 条源码 `axiom` 声明）**：**23 条**（仅用于论文一经典超越数/无理性测度推论）：
  1. `e_transcendental : Transcendental ℚ (Real.exp 1)`（[`epi_formal/EpiFormal/Axioms.lean`](epi_formal/EpiFormal/Axioms.lean)）
  2. `pi_transcendental : Transcendental ℚ Real.pi`（[`epi_formal/EpiFormal/Axioms.lean`](epi_formal/EpiFormal/Axioms.lean)）
  3. `mu_e_eq_two : irrMeasure (exp 1) = 2`（[`epi_formal/EpiFormal/Measure.lean`](epi_formal/EpiFormal/Measure.lean)）
- **第 3 层（项目自加公理）**：**0 条**

---

## 三、完整仓库目录与快速导航

### 1. 最新主论文、历史 B 稿与编译日志
- **全局目录索引与文档入口**：[`REPOSITORY_STRUCTURE.md`](REPOSITORY_STRUCTURE.md)（全仓结构总览）、[`paper1_e_plus_pi/00_PROJECT_INDEX.md`](paper1_e_plus_pi/00_PROJECT_INDEX.md)（论文一索引）、[`paper2_spectral_gap_dimension/README.md`](paper2_spectral_gap_dimension/README.md)（论文二索引）、[`verification/README.md`](verification/README.md)（核验脚本与记录总索引）
- **论文一（72 页，0 错误 / 0 警告 / 0 Overfull `\hbox`）**：
  - 源码：[`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex)
  - 成稿 PDF 与日志：[`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf)、[`paper1_e_plus_pi.log`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.log)
- **论文二（63 页，0 错误 / 0 未定义引用 / 0 Overfull `\hbox`；含 §7.5 `thm:multi-residue-asymptotic`）**：
  - 源码：[`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex)
  - 成稿 PDF 与日志：[`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.pdf`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.pdf)、[`paper2_spectral_gap_dimension.log`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.log)
  - 拆分三轨及补充工程（总览 [`split/README.md`](paper2_spectral_gap_dimension/split/README.md)；与主稿 11 个切片拼接 **279,145 字节逐字节一致**；2A 24 页 / 2B 15 页 / 2C 24 页均 0 未定义引用）：[`paper2_spectral_gap_dimension/split/`](paper2_spectral_gap_dimension/split/)
- **历史 B 稿完整备份（65 页，已明确标为历史归档）**：
  - [`paper1_e_plus_pi/02_companion_paper/Phase2_revised.tex`](paper1_e_plus_pi/02_companion_paper/Phase2_revised.tex) / [`.pdf`](paper1_e_plus_pi/02_companion_paper/Phase2_revised.pdf) / [`.log`](paper1_e_plus_pi/02_companion_paper/Phase2_revised.log)
- **论文一投稿准备与论文二历史稿**：
  - [`paper1_e_plus_pi/03_submission_prep/`](paper1_e_plus_pi/03_submission_prep/)（cover letter、AI 贡献草稿、核对清单等）
  - [`paper1_e_plus_pi/04_formalization_audits/`](paper1_e_plus_pi/04_formalization_audits/)（早期单文件审计记录与旧日志）
  - [`paper2_spectral_gap_dimension/historical_versions/`](paper2_spectral_gap_dimension/historical_versions/)（`paper2_old.tex/.pdf`、`paper2_20261118.tex/.pdf`、`paper2_integrated_v20261122_ed61a92.tex`、`paper2_integrated_v20261123_1e91028.tex/.pdf`、`paper2_integrated_v20261123_7ece3b9.tex` 等）

### 2. Lean 4 完整形式化工程（[`epi_formal/`](epi_formal/)）
- 工具链与清单：[`lean-toolchain`](epi_formal/lean-toolchain)（`leanprover/lean4:v4.35.0`）、[`lakefile.toml`](epi_formal/lakefile.toml)、[`lake-manifest.json`](epi_formal/lake-manifest.json)
- 总入口与独立审计脚本：[`EpiFormal.lean`](epi_formal/EpiFormal.lean)、[`Audit.lean`](epi_formal/Audit.lean)（937 条核心双射）、[`AuditResidueCert.lean`](epi_formal/AuditResidueCert.lean)（27 条残差证书表审计）、[`AuditResidueMultiAsymptotic.lean`](epi_formal/AuditResidueMultiAsymptotic.lean)（24 条多残差推广审计）
- 分轨评审草案入口（独立于 `Audit.lean` 与 `lake build EpiFormal`，仅作拆轨核对）：[`EpiFormal2A_Draft.lean`](epi_formal/EpiFormal2A_Draft.lean)、[`EpiFormal2B_Draft.lean`](epi_formal/EpiFormal2B_Draft.lean)、[`EpiFormal2C_Draft.lean`](epi_formal/EpiFormal2C_Draft.lean)
- 全量 337 个 `EpiFormal/` 子模块源码：[`epi_formal/EpiFormal/`](epi_formal/EpiFormal/)（含 2026-11-22 新增的 [`WindowShortAeRealize.lean`](epi_formal/EpiFormal/WindowShortAeRealize.lean)、[`ResidueModGeneral.lean`](epi_formal/EpiFormal/ResidueModGeneral.lean)、[`TransferOperatorDim.lean`](epi_formal/EpiFormal/TransferOperatorDim.lean)、[`FiniteStateComplete.lean`](epi_formal/EpiFormal/FiniteStateComplete.lean)、[`ResidueAsymptotic.lean`](epi_formal/EpiFormal/ResidueAsymptotic.lean)、[`GeneralGrowingRec.lean`](epi_formal/EpiFormal/GeneralGrowingRec.lean)、[`GeneralGrowingDim.lean`](epi_formal/EpiFormal/GeneralGrowingDim.lean)、[`WindowBoundedUpper.lean`](epi_formal/EpiFormal/WindowBoundedUpper.lean) 与并入的 8 个论文一模块，以及 2026-11-23 新增的 [`ResidueCertTable.lean`](epi_formal/EpiFormal/ResidueCertTable.lean) / `ResidueCertGen/` 与 [`ResidueMultiAsymptotic.lean`](epi_formal/EpiFormal/ResidueMultiAsymptotic.lean)）
- 阶段性基线与历史文档（含 2026-11-23 更新头注）：[`epi_formal/README.md`](epi_formal/README.md)、[`LEMMA_AUDIT.md`](epi_formal/LEMMA_AUDIT.md)、[`PROOF_GAPS.md`](epi_formal/PROOF_GAPS.md)、[`FINAL_REVIEW.md`](epi_formal/FINAL_REVIEW.md)

### 3. 核验脚本、审计日志、数学记录与一次文献（[`verification/`](verification/)）
- **分类总导航与一体体检**：[`verification/README.md`](verification/README.md)、[`verify_repo_integrity.py`](verification/verify_repo_integrity.py) / [`.log`](verification/verify_repo_integrity.log)（全库零遗漏/审计/论文/链接一站式核查）
- **核心审计与对账**：[`audit_final_20261122.log`](verification/audit_final_20261122.log)、[`audit_residue_multi_asymptotic_20261123.log`](verification/audit_residue_multi_asymptotic_20261123.log)、[`check_audit_reconcile.py`](verification/check_audit_reconcile.py)
- **符号 / 区间 / 转移算子 / 论文完整性验证**：
  - [`verify_round3.py`](verification/verify_round3.py) / [`.log`](verification/verify_round3.log)（12/12 SymPy 1.14.0 符号验证）
  - [`verify_round4.py`](verification/verify_round4.py) / [`.log`](verification/verify_round4.log) / [`certificate_round4.json`](verification/certificate_round4.json)（余弦积分 + 450 位 `mpmath.iv` 区间证书）
  - [`residue_certificate.py`](verification/residue_certificate.py) / [`residue-certificate.log`](verification/residue-certificate.log)（论文二 `thm:residues` 早期 $N=256$ 精确有理转移算子认证）
  - [`residue_certificate_general.py`](verification/residue_certificate_general.py) / [`.json`](verification/residue_certificate_general.json) / [`.log`](verification/residue_certificate_general.log)（论文二 `thm:residues-general` 一般模 $m\in\{2,3,4,5,6\}, r\in\{1,m\}$ 早期 $N=256$ 精确整数证书）
  - [`residue_certificate_general_N512.py`](verification/residue_certificate_general_N512.py)（论文二 `thm:residues-general` / `tab:residues-general` 最新 $N=512$ 精确整数证书并生成 `ResidueCertGen/` 核验表格）
  - [`verify_paper2_extensions.py`](verification/verify_paper2_extensions.py) / [`.log`](verification/verify_paper2_extensions.log)（论文二 `thm:residues-asymptotic` 倒数 Fibonacci 常数 $\psi_{\mathrm{Fib}}$ 与金属常数 $C_r$ 50 位计算及 `cor:growing-rec-three-regimes` 任意增长商三类递推相图验证）
  - [`verify_residue_multi_asymptotic.py`](verification/verify_residue_multi_asymptotic.py) / [`.log`](verification/verify_residue_multi_asymptotic.log) / [`.json`](verification/verify_residue_multi_asymptotic.json)（论文二 `thm:multi-residue-asymptotic` 32 位 Chebyshev 配置法全面核验：单残差常数 $c_2(r)$、10 组 $N=512$ 核区间、10 组次临界三阶渐近与 `{1,2}`/`{1,2,3}` 超临界 $\Theta(m^{-2s_0})$ 速率）
  - [`verify_paper2_merge.py`](verification/verify_paper2_merge.py) / [`.log`](verification/verify_paper2_merge.log)（论文二结构、标签、引文、切片逐字节一致性与完整内容校验）
  - [`asymptotic_residues_check_20261123.py`](verification/asymptotic_residues_check_20261123.py)、[`blr_formula_compare_20261123.py`](verification/blr_formula_compare_20261123.py)（2026-11-23 Hurwitz-zeta 与 BLR 公式对比辅助脚本）
  - 其余黄金比轨道与谱理论数值验证脚本：[`verify_golden_orbit_model.py`](verification/verify_golden_orbit_model.py)、[`verify_golden_b2_exact.py`](verification/verify_golden_b2_exact.py)、[`verify_golden_b3_b4_exact.py`](verification/verify_golden_b3_b4_exact.py)、[`verify_golden_b5_b6_multiscale.py`](verification/verify_golden_b5_b6_multiscale.py)、[`verify_golden_general_b.py`](verification/verify_golden_general_b.py)、[`verify_full_spectrum_discrete.py`](verification/verify_full_spectrum_discrete.py)、[`verify_poly_recurrence_2b.py`](verification/verify_poly_recurrence_2b.py)、[`verify_weighted_lower.py`](verification/verify_weighted_lower.py)
- **全工作区台账、数学论证留痕与一次文献 PDF**：
  - [`全工作区总索引与留痕台账.md`](verification/全工作区总索引与留痕台账.md)、[`成果清单与边界.md`](verification/成果清单与边界.md)、[`复现指南.md`](verification/复现指南.md)、[`cmms_citation_check_20261122.md`](verification/cmms_citation_check_20261122.md)
  - 2026-11-23 新增记录：[`colab_rebuild_audit_20261123.md`](verification/colab_rebuild_audit_20261123.md)、[`residue_certgen_lean_20261123.md`](verification/residue_certgen_lean_20261123.md)、[`cert_v3_redesign_20261123.md`](verification/cert_v3_redesign_20261123.md)、[`paper2_novelty_review_20261123.md`](verification/paper2_novelty_review_20261123.md)、[`论文二拆分分类与Lean精准映射_20261123.md`](verification/论文二拆分分类与Lean精准映射_20261123.md)、[`推广1_多残差相变与欧拉常数三阶渐近Lean4记录_20261123.md`](verification/推广1_多残差相变与欧拉常数三阶渐近Lean4记录_20261123.md)
  - 2026-11-25 新增记录：[`paper2_novelty_review_20261125.md`](verification/paper2_novelty_review_20261125.md)（论文二残差 / 多残差维数结果的投稿前新颖性核查：DFSU、Heinemann–Urbański、Bowen 公式等先例）、[`paper2_novelty_crosscheck_20261125.py`](verification/paper2_novelty_crosscheck_20261125.py) / [`.log`](verification/paper2_novelty_crosscheck_20261125.log)、[`patch_novelty_wording_20261125.py`](paper2_spectral_gap_dimension/patch_novelty_wording_20261125.py)（按核查 §5 改写论文 prior-work 段与新颖性措辞）
  - [`verification/reference_pdfs/`](verification/reference_pdfs/)（含官方 [`CMMS_PJM_2004_217_45.pdf`](verification/reference_pdfs/CMMS_PJM_2004_217_45.pdf)、`h-sets.pdf`、`BLR_1710_03596.pdf`、`CLU_1805_11904.pdf`、`MEA_2511_10328v3.pdf`）
  - [`build_desktop_package_20261122.py`](verification/build_desktop_package_20261122.py)（桌面完整交付包组装与端到端复验脚本）

### 4. 研究过程与历史全量归档
- [`paper1_e_plus_pi/05_research_process/`](paper1_e_plus_pi/05_research_process/)（分轮研究目录 `A`–`E`、`golden_finite_spectrum/` 及 `golden_finite_spectrum.py` 等 9 个论文一伴随证书脚本与实验日志）
- [`paper1_e_plus_pi/06_historical_versions/`](paper1_e_plus_pi/06_historical_versions/)（1–8 轮演化备份及 `archive_snapshots/` 快照包）
- [`downloads/`](downloads/)（文献下载缓存 PDF：`1211.2494.pdf`、`1805.11904v1.pdf`）、[`papers/README.md`](papers/README.md)（arxiv MCP 落盘说明）、[`scripts/`](scripts/)、[`progress_and_path_analysis.md`](progress_and_path_analysis.md)、[`AGENTS.md`](AGENTS.md)、[`REPOSITORY_STRUCTURE.md`](REPOSITORY_STRUCTURE.md)、[`.agents/skills/`](.agents/skills/)、[`.claude/skills/README.md`](.claude/skills/README.md)
- 工作区根目录下配合重组的 PowerShell 脚本：[`rename_english_20261121.ps1`](rename_english_20261121.ps1)、[`reorganize_step1_20261121.ps1`](reorganize_step1_20261121.ps1)、[`reorganize_step2_20261121.ps1`](reorganize_step2_20261121.ps1)

> **关于未上传的大体积缓存与本地工具文件**（已在 [`.gitignore`](.gitignore) 中排除）：
> - `epi_formal/.lake/`（约 **8.49 GB** 本地 Mathlib `.olean`/编译产物缓存，可通过下方 `lake exe cache get && lake build EpiFormal` 全量复现）
> - `.venv/`（本地 Python 虚拟环境）
> - `.opencode/`、`opencode.json`、`opencode.json.bak-*`（本地编辑器/Agent 运行时配置）
> - `**/__pycache__/`、`*.pyc` 及 LaTeX 中间产物 `*.aux`、`*.out`、`*.toc`、`*.fls`、`*.fdb_latexmk`、`*.synctex.gz`

---

## 四、完整复现指南

### 4.1 离线核对审计日志与核心 Python 证书（无需联网）

需安装 Python `sympy >= 1.14` 与 `mpmath >= 1.3`：

```powershell
# 0. 一键全仓库零遗漏/审计/论文/链接统一体检
python verification\verify_repo_integrity.py

# 1. 核对主审计 937/937 双射、0 sorryAx、23 白名单、0 项目自加公理、0 逃逸关键字（扫描全库 344 个 Lean 文件）
python verification\check_audit_reconcile.py verification\audit_final_20261122.log

# 2. 复跑核心符号、450 位区间、N=256 与 N=512 整数转移算子、新拓展 50/32 位验证及论文完整性（含切片逐字节）与拆分引用检查
python verification\verify_round3.py
python verification\verify_round4.py
python verification\residue_certificate.py
python verification\residue_certificate_general.py
python verification\residue_certificate_general_N512.py
python verification\verify_paper2_extensions.py
python verification\verify_residue_multi_asymptotic.py
python verification\verify_paper2_merge.py
python paper2_spectral_gap_dimension\split\undef_ref_audit.py
```

论文一涉及的多尺度黄金比伴随脚本也可直接从原路径运行（例如）：

```powershell
python paper1_e_plus_pi\05_research_process\golden_finite_spectrum\golden_finite_spectrum.py
```

### 4.2 洁净环境从源码重编译 Lean 4 与重跑三大内核审计（需联网下载 Mathlib 预编译 cache）

```powershell
cd epi_formal
lake exe cache get
lake build EpiFormal
lake build EpiFormal.ResidueCertTable
lake build EpiFormal.ResidueMultiAsymptotic
lake env lean Audit.lean | Out-File -Encoding utf8 ..\verification\audit_rerun.log
lake env lean AuditResidueCert.lean
lake env lean AuditResidueMultiAsymptotic.lean
cd ..
python verification\check_audit_reconcile.py verification\audit_rerun.log
```

> 注：`check_audit_reconcile.py` 自动兼容 UTF-8、UTF-8-SIG 以及 Windows PowerShell 默认 `>` 重定向产生的 UTF-16LE 日志；若 Windows 下并发 `lake build` 遭遇安全软件 `.olean` 文件锁抖动，可对报错模块串行执行 `lake build EpiFormal.<ModuleName>` 后再跑 `lake build EpiFormal`。

### 4.3 从零洁净目录重编译两篇主论文 PDF（需 TeX Live 或 MiKTeX `pdflatex`）

```powershell
# 论文一（含 hyperref 书签与复杂交叉引用，无 .aux 洁净目录需三遍稳定全部引用）
cd paper1_e_plus_pi\01_main_paper
pdflatex -interaction=nonstopmode paper1_e_plus_pi.tex
pdflatex -interaction=nonstopmode paper1_e_plus_pi.tex
pdflatex -interaction=nonstopmode paper1_e_plus_pi.tex

# 论文二（洁净目录三遍稳定全部引用与书签）
cd ..\..\paper2_spectral_gap_dimension
pdflatex -interaction=nonstopmode paper2_spectral_gap_dimension.tex
pdflatex -interaction=nonstopmode paper2_spectral_gap_dimension.tex
pdflatex -interaction=nonstopmode paper2_spectral_gap_dimension.tex
```

---

## 五、它没做到什么（诚实边界与留存待办）

1. **核心数学问题未解决**：本仓库中的所有工作**没有证明** $e+\pi$（以及单个 $e\pi, e-\pi, \pi/e, \pi^e$）的无理性或超越性；逃逸约化（P1）属于同难度族等价换靶，障碍分析不构成一般方法的不可能性证明。
2. **数值认证、Lean 内核分工与尚未覆盖的数学边界**：`thm:windows`、`thm:short-ae`、`thm:no-short-dim`（含 $\dim_{\mathrm{H}}=1$ 与 $\operatorname{Leb}=0$）、`thm:finite-state-tail`（$\mathbb{R}$ 与 $\mathbb{T}$）、`thm:residues`/`thm:residues-general`/`thm:residues-asymptotic` 以及 `thm:multi-residue-asymptotic` 均已入 Lean 4 内核闭环；`tab:residues-general` 的 20 个 $N=512$ 单侧**闭区间**与 5 条严格分离亦已在 `ResidueCertTable.lean`（`AuditResidueCert.lean` 27 条）由 Lean 内核直接复跑通过（未用 `native_decide`）。仍留存在 Lean 内核或当前理论之外的部分包括：（a）`thm:residues` 与 `tab:residues-general` **开区间严格性**仍依赖引用的 Bowen 压力公式与精确整数脚本 [`residue_certificate_general_N512.py`](verification/residue_certificate_general_N512.py)；（b）`thm:finite-state-tail` 中的有限维 Perron–Frobenius 右特征向量需显式传入；（c）`thm:multi-residue-asymptotic` 中临界线 $s_0(S)=1/2$ 处的收敛速率与超临界阶段精确主导前因子常数尚未解决；（d）`verify_residue_multi_asymptotic.py` 为 32 位 Chebyshev 配置法数值佐证，不作严格证明引用。
3. **重耗时高精度脚本与独立重构边界**：
   - 4 个 2500 位高精度长耗时脚本（[`verify_golden_b3_b4_exact.py`](verification/verify_golden_b3_b4_exact.py)、[`verify_golden_b5_b6_multiscale.py`](verification/verify_golden_b5_b6_multiscale.py)、[`verify_golden_general_b.py`](verification/verify_golden_general_b.py)、[`verify_weighted_lower.py`](verification/verify_weighted_lower.py)）保留源码与历史 `.log` 供按需完整重跑；
   - `Audit.lean`（937 条）与 `AuditResidueCert.lean`（27 条）已于 2026-11-23 在 Google Colab 洁净克隆环境中完成独立全量复现（[`colab_rebuild_audit_20261123.md`](verification/colab_rebuild_audit_20261123.md)）；`ResidueMultiAsymptotic.lean` 与 `AuditResidueMultiAsymptotic.lean`（24 条）已在本地 Lean `v4.35.0` / Mathlib `v4.35.0` 完成全量构建与独立 `#print axioms` 审计（[`audit_residue_multi_asymptotic_20261123.log`](verification/audit_residue_multi_asymptotic_20261123.log)）；2026-11-24 已在 Colab 全新克隆环境完成第二次独立复建，24 条逐条一致（[`colab_rebuild_audit_20261124.md`](verification/colab_rebuild_audit_20261124.md)）。
4. **投稿前人工完善项**：
   - [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex) 仍保留作者/单位占位符（`[Author name]`, `[Affiliation]`）与 `% TODO before submission:` 注释待正式投稿前由作者补充；
   - [`epi_formal/README.md`](epi_formal/README.md)、[`LEMMA_AUDIT.md`](epi_formal/LEMMA_AUDIT.md)、[`PROOF_GAPS.md`](epi_formal/PROOF_GAPS.md)、[`FINAL_REVIEW.md`](epi_formal/FINAL_REVIEW.md) 保留了 2026-11-14 初版 31 条基线记录作为历史档案，当前最新全量审计口径以本 `README.md`、[`Audit.lean`](epi_formal/Audit.lean) 及 [`verification/audit_final_20261122.log`](verification/audit_final_20261122.log) 为准。
