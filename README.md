# $e+\pi$ 无理性研究与连分数谱/维数理论完整私有归档（2026-11-22 最新版）

> **一句总判断**：本仓库完整归档截至 **2026-11-22** 的最新研究全貌，涵盖两篇修订重编主论文（**Paper 1** 72 页 + **Paper 2** 58 页，洁净 `pdflatex` 0 错误 / 0 警告 / 0 Overfull `\hbox`）、全量一体化的 Lean 4 `v4.35.0` 形式化工程（`lake build EpiFormal` **9179 jobs** EXIT 0，**134** 个 `.lean` 文件 [含 132 个 `EpiFormal/` 子模块 + `EpiFormal.lean` + `Audit.lean`]，`Audit.lean` **937/937** 条 `#print axioms` 严格双射 = **914** 条仅用 Lean 基础公理 [含 5 条零公理] + **23** 条论文一经典白名单公理 + **0** 条项目自加公理，`sorryAx = 0`，0 逃逸关键字）、全部符号/高精度区间/精确整数转移算子认证脚本（含一般模 $m\in\{2,3,4,5,6\}$ 的 `residue_certificate_general.py` 与论文二两项新拓展的 `verify_paper2_extensions.py`）与日志、CMMS 官方刊出全文一次文献核查，以及全部研究过程记录与历史版本快照；同时严格遵循 [`AGENTS.md`](AGENTS.md) 诚实基线——**$e+\pi$ 的无理性（及 $e\pi, e-\pi, \pi/e, \pi^e$ 单个的无理性）仍是公开问题，本仓库未证明 $e+\pi$ 无理、有理或超越。**

---

## 一、成果诚实分类与逐项对照表（遵循 `AGENTS.md` 五分法）

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| 论文二：全谱离散化 $\frac14\mathbb{Z}_{\ge0}\cup\{\infty\}$、正能级三分法（含 $L$-陪集坍缩）、临界/二值精确 Hausdorff 规范（$\mathbb{R}$ 与 $\mathbb{R}/\mathbb{Z}$）、一般 $(cj^r+d)$ 递推与次临界维数相变 $1-\alpha/r$、以及 `thm:finite-state-tail` 带标记分量临界规范全结论（$\mathbb{R}$ 与 $\mathbb{T}$） | 无条件新结果 + Lean 4 Layer A 机器验证 | **已核实**（仅依赖 Lean 基础三公理 `propext`, `Classical.choice`, `Quot.sound`；0 `sorryAx`；0 项目自加公理；新增 [`FiniteStateComplete.lean`](epi_formal/EpiFormal/FiniteStateComplete.lean) 12 条声明完整闭环 `thm:finite-state-tail`） | 在 Kraaikamp–Liardet 零能级准则（[BDS] Lemma 4.1）基础上的独立谱离散化、正能级三分法、临界规范与一般递推维数理论 | [`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex)、[`GaugeCircle.lean`](epi_formal/EpiFormal/GaugeCircle.lean)、[`TrichotomyAndPolyExtension.lean`](epi_formal/EpiFormal/TrichotomyAndPolyExtension.lean)、[`FiniteStateComplete.lean`](epi_formal/EpiFormal/FiniteStateComplete.lean) |
| 论文二新拓展（一）：**任意增长商三项递推** $Q_{j+1}=A_jQ_j+Q_{j-1}$ ($A_j\in\mathbb{Z}_{\ge2}, A_j\to\infty$) 的普适离散谱 $\mathbb{Z}_{\ge0}\cup\{\infty\}$、Kraaikamp–Liardet 误差比恒等 $\Lambda_G^{\mathrm{KL}}=\Lambda_G$、临界/二进量规与三重分裂（`thm:growing-rec-spectrum`）、亚临界维数畸变公式 $\dim_{\mathrm{H}} E_{G,\tau}(t)=\frac{1-\tau}{1+\tau\gamma_{\sup}}$ ($0\le\tau<1, \gamma_{\sup}=\limsup\frac{\log A_j}{\log Q_j}\in[0,\infty]$) 及超临界（$\tau>1$）在 $\tau_{\mathrm{crit}}=1+1/\gamma_{\sup}$ 处从秩-2 格 $L_G$ 到秩-1 有理子格 $\frac{1}{g}\mathbb{Z}$ 的二次坍缩相变与三类典型增长相图（`thm:growing-rec-dim-phase`, `cor:growing-rec-three-regimes`） | 无条件新结果 + Lean 4 Layer A 机器验证 | **已核实**（新增 [`GeneralGrowingRec.lean`](epi_formal/EpiFormal/GeneralGrowingRec.lean) 21 条 + [`GeneralGrowingDim.lean`](epi_formal/EpiFormal/GeneralGrowingDim.lean) 29 条声明，仅基础公理，0 `sorryAx` + [`verify_paper2_extensions.py`](verification/verify_paper2_extensions.py) 50 位验证） | 完全去除 $A_j$ 的多项式函数形式假设，首次揭示当 $\gamma_{\sup}>0$（如双指数 $A_j=2^{2^j}, \gamma_{\sup}=1, \tau_{\mathrm{crit}}=2$）时亚临界 Hausdorff 维数畸变因子 $(1+\tau\gamma_{\sup})^{-1}$ 与超临界秩-2 格内部二次相变 | [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex) §6.4、[`GeneralGrowingRec.lean`](epi_formal/EpiFormal/GeneralGrowingRec.lean)、[`GeneralGrowingDim.lean`](epi_formal/EpiFormal/GeneralGrowingDim.lean) |
| 论文二窗口与一般模残差体系：`thm:windows` 全四条、`thm:short-ae` 显式常数 $c=(1-e^{-1})/160$ 零尾率、`thm:no-short-dim` 完整合取（$\dim_{\mathrm{H}}=1\wedge\operatorname{Leb}=0$），以及 `thm:residues`/`thm:residues-general`（一般模 $m\ge2$ Lipschitz 移位与最终周期不变性、转移算子 Hausdorff 维数桥接、$\dim_{\mathrm{H}} F_{m,r}>1/2$、$\dim_{\mathrm{H}} F_{4,1}\le 4/5$ 与有限步矩阵证书可靠性） | 无条件新结果 + Lean 4 Layer A 机器验证（结构与解析主干全闭环） | **已核实**（仅 Lean 基础三公理；新增 [`WindowShortAeRealize.lean`](epi_formal/EpiFormal/WindowShortAeRealize.lean) 14 条、[`ResidueModGeneral.lean`](epi_formal/EpiFormal/ResidueModGeneral.lean) 7 条、[`TransferOperatorDim.lean`](epi_formal/EpiFormal/TransferOperatorDim.lean) 11 条全通 `Audit.lean`） | 对 $e$ 收敛子尺度窗口连分数商约束集与一般模残差集 $F_{m,r}$ 建立端到端（`GenContFract.of` + `hausdorffMeasure`）机器证明框架 | [`WindowShortAeRealize.lean`](epi_formal/EpiFormal/WindowShortAeRealize.lean)、[`ResidueModGeneral.lean`](epi_formal/EpiFormal/ResidueModGeneral.lean)、[`TransferOperatorDim.lean`](epi_formal/EpiFormal/TransferOperatorDim.lean)、[`WindowBoundedUpper.lean`](epi_formal/EpiFormal/WindowBoundedUpper.lean) |
| 论文二新拓展（二）：**金属连分数预解式恒等式、全模 $m\ge2$ 全局严格维数分离与倒数 Fibonacci 常数二阶渐近展开**（`thm:residues-asymptotic`）：精确预解式分支恒等式 $(r+x)^{-2s}V_{r,s}(1/(r+x))=V_{r,s}(x)-1$、对**一切**整数模 $m\ge2$ 无条件成立的全局严格分离 $\dim_{\mathrm{H}} F_{m,m}<\dim_{\mathrm{H}} F_{m,1}=\dim_{\mathrm{H}} E_m$、二阶渐近展开 $\dim_{\mathrm{H}} F_{m,r}=\frac12+\frac{C_r}{2m}-\frac{C_r^2\log m}{2m^2}+O(m^{-2})$（其中 $C_r=\sum_{n=0}^\infty 1/q_n(r)$，$C_1=\psi_{\mathrm{Fib}}=\sum_{k=1}^\infty 1/F_k\approx3.3598856662$ 为倒数 Fibonacci 常数，$\dim_{\mathrm{H}} F_{m,m}=\frac12+\frac{1}{2m}-\frac{\log m}{2m^2}+O(m^{-2})$）、维数超出比 $\frac{\dim_{\mathrm{H}} E_m-1/2}{\dim_{\mathrm{H}} F_{m,m}-1/2}\to\psi_{\mathrm{Fib}}$ 及关于余数 $r$ 的最终严格单调递减性 | 无条件新结果 + Lean 4 Layer A 机器验证 | **已核实**（新增 [`ResidueAsymptotic.lean`](epi_formal/EpiFormal/ResidueAsymptotic.lean) 15 条声明，仅基础公理，0 `sorryAx` + [`verify_paper2_extensions.py`](verification/verify_paper2_extensions.py) 50 位验证） | 将有限模 $m\le6$ 的数值严格分离提升为对所有 $m\ge2$ 的无条件定理，并导出由倒数 Fibonacci 常数 $\psi_{\mathrm{Fib}}$ 与金属连分数级数 $C_r$ 支配的二阶渐近公式（经 arXiv 与既有连分数维数文献**负搜索**，未见将 $\psi_{\mathrm{Fib}}$ 或 $C_r$ 作为模余数连分数集 Hausdorff 维数渐近常数的先例） | [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex) §7.4、[`ResidueAsymptotic.lean`](epi_formal/EpiFormal/ResidueAsymptotic.lean) |
| 论文二残差表全表 Lean 化（2026-11-23）：`tab:residues-general` 换为 N=512 证书（10 个区间宽度均 1/512，$F_{4,1}$ 上界 359/512→**179/256**），20 个单侧闭界 $\mathrm{lower}\le\dim_{\mathrm H}F_{m,r}\le\mathrm{upper}$ 与 5 条严格分离 $\dim_{\mathrm H}F_{m,m}<\dim_{\mathrm H}F_{m,1}$（$2\le m\le6$）均为 Lean 定理；通用可靠性定理 `dimH_le_of_certU`/`le_dimH_of_certL` 对任意参数成立 | 有限计算（10 个具体集合）+ 无条件形式化可靠性定理 | **已核实**（本机 Lean 4.35.0 + Mathlib 实跑：201 个 core 证书模块 `decide +kernel` 全通过、`ResidueCertTable` `lake build` EXIT 0；27 条声明仅基础三公理；未用 `native_decide`）。开区间严格性仍依赖引用的 Bowen 公式，未形式化 | 负搜索未找到证明助手内核检查的连分数康托集维数数值界先例（仅网页检索，范围见记录）；数值方法与论文原证书相同 | [`residue_certgen_lean_20261123.md`](verification/residue_certgen_lean_20261123.md)、[`ResidueCertTable.lean`](epi_formal/EpiFormal/ResidueCertTable.lean)、[`AuditResidueCert.lean`](epi_formal/AuditResidueCert.lean) |
| 论文一：仿射窗口显式周期 $2B|C|$、黄金比轨道有限谱与 $B=1\text{--}6$ / 四类多尺度有理端点刚性；全部 8 个原独立 Lean 辅助模块（共 29 条声明）并入主工程与统一审计 | 无条件模型/归约结果 + 已有辅理统一机器复核 | **已核实**（72 页重编 0 错误/0 警告；原独立 8 模块——`GoldenHeadCutoff`, `GoldenAffineEndpoint`, `AffineWindowAudit`, `DigitTailBound`, `DensityCube`, `OrbitAndFlow`, `ResearchAdvance`, `TraceMarkov`——全部并入 `EpiFormal.lean` 与 `Audit.lean`，共 29 条声明仅用基础公理） | 用 Bugeaud 二次 Mobius 恒等式研究 $A/B-e$ 与 $(A+Ce)/B$ 模型；模型与窗口研究**不解决 $e+\pi$ 无理性** | [`paper1_e_plus_pi.pdf`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf)、[`GoldenHeadCutoff.lean`](epi_formal/EpiFormal/GoldenHeadCutoff.lean)、[`GeneralEndpointRigidity.lean`](epi_formal/EpiFormal/GeneralEndpointRigidity.lean)、[`EpiFormal.lean`](epi_formal/EpiFormal.lean) |
| 论文一：$e+\pi$ 无理性归约、Flint Hills 条件桥接、Alekseyev 方向（$\text{收敛}\Rightarrow\mu(\pi)\le 5/2$）、逃逸约化（P1）与四路障碍分析 | 等价改写/换靶 + 条件结果 + 障碍分析 + Lean 4 机器验证 | **已核实**（23 条经典定理推导显式依赖 3 条经典白名单公理；Meiburg Flint Hills 情况与 Alekseyev 方向已机器形式化，无项目自加公理） | 仅做条件桥接、等价换靶（如 P1 晶格逃逸）或排除特定构造；明确不宣称解决原问题或“更接近证明” | [`FlintHills.lean`](epi_formal/EpiFormal/FlintHills.lean)、[`MeiburgConvergence.lean`](epi_formal/EpiFormal/MeiburgConvergence.lean)、[`Alekseyev.lean`](epi_formal/EpiFormal/Alekseyev.lean)、[`Escape.lean`](epi_formal/EpiFormal/Escape.lean) |
| 符号、区间与精确整数转移算子证书（`verify_round3.py`、`verify_round4.py`、`residue_certificate.py`、`residue_certificate_general.py` 等） | 有限计算或有限排除（非 Lean 内核求值） | **已核实**（SymPy `12/12` PASS；450 位 `mpmath.iv`；`residue_certificate.py` 认证 $357/512 < \dim_{\mathrm{H}} F_{4,1} < 359/512$；`residue_certificate_general.py` 以 $N=256$, $S=10^{13}$, $K\in\{120,130\}$ 精确整数算术认证 $m\in\{2,3,4,5,6\}, r\in\{1,m\}$ 全部 10 组精细二进区间及每一 $m$ 的严格谱隙 $[ \mathrm{PASS} ]$，可靠桥已由 `TransferOperatorDim.lean` 形式化） | 对有限分母、有限窗口与有限格点转移矩阵给精确有理计算验证；精确 256 格点数值运算由 Python 证书执行、结构可靠性由 Lean 证明 | [`verify_round3.py`](verification/verify_round3.py)、[`verify_round4.py`](verification/verify_round4.py)、[`residue_certificate.py`](verification/residue_certificate.py)、[`residue_certificate_general.py`](verification/residue_certificate_general.py)、[`residue_certificate_general.json`](verification/residue_certificate_general.json) |
| CMMS 一次文献核查与论文二全篇纠偏 | 文献核查与复现 | **已核实**（下载并逐页核对 *Pacific J. Math.* 217(1) (2004), pp. 45–59 官方刊出全文，确认 §5 主定理为 **Theorem 3** 而非误写的 Theorem 5；论文二三处引文已全部更正重编） | Cabrelli–Mendivil–Molter–Shonkwiler, *Pacific J. Math.* 217(1) (2004), 45–59, `doi:10.2140/pjm.2004.217.45`（pp. 57–58, §5 Theorem 3） | [`cmms_citation_check_20261122.md`](verification/cmms_citation_check_20261122.md)、[`CMMS_PJM_2004_217_45.pdf`](verification/reference_pdfs/CMMS_PJM_2004_217_45.pdf) |

---

## 二、三层公理依赖实测清单（`verification/audit_final_20261122.log`）

经 [`epi_formal/`](epi_formal/)（Lean `v4.35.0` + Mathlib `v4.35.0`）执行 `lake build EpiFormal`（**9179 jobs**，EXIT 0）与 `lake env lean Audit.lean`（EXIT 0），并由 [`verification/check_audit_reconcile.py`](verification/check_audit_reconcile.py) 自动对账核实：

- **审计声明总计**：**937 条**（`Audit.lean` 与原始日志 **937/937** 严格双射，重复 0）
- **`sorryAx` 计数**：**0**
- **逃逸关键字全库扫描**（扫描全部 134 个 `.lean` 文件中的 `sorry` / `admit` / `native_decide` / `implemented_by` / `extern` / `unsafe` / `partial` / `opaque`）：**0 命中**
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
- **论文一（72 页，0 错误 / 0 警告 / 0 Overfull `\hbox`）**：
  - 源码：[`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex)
  - 成稿 PDF 与日志：[`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf)、[`paper1_e_plus_pi.log`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.log)
- **论文二（50 页，0 错误 / 0 警告 / 0 Overfull `\hbox`）**：
  - 源码：[`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex)
  - 成稿 PDF 与日志：[`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.pdf`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.pdf)、[`paper2_spectral_gap_dimension.log`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.log)
- **历史 B 稿完整备份（65 页，已明确标为历史归档）**：
  - [`paper1_e_plus_pi/02_companion_paper/Phase2_revised.tex`](paper1_e_plus_pi/02_companion_paper/Phase2_revised.tex) / [`.pdf`](paper1_e_plus_pi/02_companion_paper/Phase2_revised.pdf) / [`.log`](paper1_e_plus_pi/02_companion_paper/Phase2_revised.log)
- **论文一投稿准备与论文二历史稿**：
  - [`paper1_e_plus_pi/03_submission_prep/`](paper1_e_plus_pi/03_submission_prep/)（cover letter、AI 贡献草稿、核对清单等）
  - [`paper1_e_plus_pi/04_formalization_audits/`](paper1_e_plus_pi/04_formalization_audits/)（早期单文件审计记录与旧日志）
  - [`paper2_spectral_gap_dimension/historical_versions/`](paper2_spectral_gap_dimension/historical_versions/)（`paper2_old.tex/.pdf`、`paper2_20261118.tex/.pdf` 等）

### 2. Lean 4 完整形式化工程（[`epi_formal/`](epi_formal/)）
- 工具链与清单：[`lean-toolchain`](epi_formal/lean-toolchain)（`leanprover/lean4:v4.35.0`）、[`lakefile.toml`](epi_formal/lakefile.toml)、[`lake-manifest.json`](epi_formal/lake-manifest.json)
- 总入口与全量审计脚本：[`EpiFormal.lean`](epi_formal/EpiFormal.lean)、[`Audit.lean`](epi_formal/Audit.lean)
- 全量 132 个子模块源码：[`epi_formal/EpiFormal/`](epi_formal/EpiFormal/)（含 2026-11-22 新增的 [`WindowShortAeRealize.lean`](epi_formal/EpiFormal/WindowShortAeRealize.lean)、[`ResidueModGeneral.lean`](epi_formal/EpiFormal/ResidueModGeneral.lean)、[`TransferOperatorDim.lean`](epi_formal/EpiFormal/TransferOperatorDim.lean)、[`FiniteStateComplete.lean`](epi_formal/EpiFormal/FiniteStateComplete.lean)、[`ResidueAsymptotic.lean`](epi_formal/EpiFormal/ResidueAsymptotic.lean)、[`GeneralGrowingRec.lean`](epi_formal/EpiFormal/GeneralGrowingRec.lean)、[`GeneralGrowingDim.lean`](epi_formal/EpiFormal/GeneralGrowingDim.lean)、[`WindowBoundedUpper.lean`](epi_formal/EpiFormal/WindowBoundedUpper.lean) 与并入的 8 个论文一模块）
- 历史阶段性基线文档：[`epi_formal/README.md`](epi_formal/README.md)、[`LEMMA_AUDIT.md`](epi_formal/LEMMA_AUDIT.md)、[`PROOF_GAPS.md`](epi_formal/PROOF_GAPS.md)、[`FINAL_REVIEW.md`](epi_formal/FINAL_REVIEW.md)（标注了 2026-11-14 初版 31 条基线快照；最新 937 条权威数据以本说明和 `Audit.lean` 为准）

### 3. 核验脚本、审计日志、数学记录与一次文献（[`verification/`](verification/)）
- **核心审计与对账**：[`audit_final_20261122.log`](verification/audit_final_20261122.log)、[`check_audit_reconcile.py`](verification/check_audit_reconcile.py)
- **符号 / 区间 / 转移算子 / 论文完整性验证**：
  - [`verify_round3.py`](verification/verify_round3.py) / [`.log`](verification/verify_round3.log)（12/12 SymPy 1.14.0 符号验证）
  - [`verify_round4.py`](verification/verify_round4.py) / [`.log`](verification/verify_round4.log) / [`certificate_round4.json`](verification/certificate_round4.json)（余弦积分 + 450 位 `mpmath.iv` 区间证书）
  - [`residue_certificate.py`](verification/residue_certificate.py) / [`residue-certificate.log`](verification/residue-certificate.log)（论文二 `thm:residues` 精确有理转移算子认证）
  - [`residue_certificate_general.py`](verification/residue_certificate_general.py) / [`.json`](verification/residue_certificate_general.json) / [`.log`](verification/residue_certificate_general.log)（论文二 `thm:residues-general` 一般模 $m\in\{2,3,4,5,6\}, r\in\{1,m\}$ 精确整数证书）
  - [`verify_paper2_extensions.py`](verification/verify_paper2_extensions.py) / [`.log`](verification/verify_paper2_extensions.log)（论文二 `thm:residues-asymptotic` 倒数 Fibonacci 常数 $\psi_{\mathrm{Fib}}$ 与金属常数 $C_r$ 50 位计算及 `cor:growing-rec-three-regimes` 任意增长商三类递推相图验证）
  - [`verify_paper2_merge.py`](verification/verify_paper2_merge.py) / [`.log`](verification/verify_paper2_merge.log)（论文二结构、标签、引文与双稿融合完整性校验）
  - 其余黄金比轨道与谱理论数值验证脚本：[`verify_golden_orbit_model.py`](verification/verify_golden_orbit_model.py)、[`verify_golden_b2_exact.py`](verification/verify_golden_b2_exact.py)、[`verify_golden_b3_b4_exact.py`](verification/verify_golden_b3_b4_exact.py)、[`verify_golden_b5_b6_multiscale.py`](verification/verify_golden_b5_b6_multiscale.py)、[`verify_golden_general_b.py`](verification/verify_golden_general_b.py)、[`verify_full_spectrum_discrete.py`](verification/verify_full_spectrum_discrete.py)、[`verify_poly_recurrence_2b.py`](verification/verify_poly_recurrence_2b.py)、[`verify_weighted_lower.py`](verification/verify_weighted_lower.py)
- **全工作区台账、数学论证留痕与一次文献 PDF**：
  - [`全工作区总索引与留痕台账.md`](verification/全工作区总索引与留痕台账.md)、[`成果清单与边界.md`](verification/成果清单与边界.md)、[`复现指南.md`](verification/复现指南.md)、[`cmms_citation_check_20261122.md`](verification/cmms_citation_check_20261122.md)
  - [`verification/reference_pdfs/`](verification/reference_pdfs/)（含官方 [`CMMS_PJM_2004_217_45.pdf`](verification/reference_pdfs/CMMS_PJM_2004_217_45.pdf)、`h-sets.pdf`、`BLR_1710_03596.pdf`、`CLU_1805_11904.pdf`、`MEA_2511_10328v3.pdf`）
  - [`build_desktop_package_20261122.py`](verification/build_desktop_package_20261122.py)（桌面完整交付包组装与端到端复验脚本）

### 4. 研究过程与历史全量归档
- [`paper1_e_plus_pi/05_research_process/`](paper1_e_plus_pi/05_research_process/)（分轮研究目录 `A`–`E`、`golden_finite_spectrum/` 及 `golden_finite_spectrum.py` 等 9 个论文一伴随证书脚本与实验日志）
- [`paper1_e_plus_pi/06_historical_versions/`](paper1_e_plus_pi/06_historical_versions/)（1–8 轮演化备份及 `archive_snapshots/` 快照包）
- [`downloads/`](downloads/)（文献下载缓存 PDF：`1211.2494.pdf`、`1805.11904v1.pdf`）、[`papers/README.md`](papers/README.md)（arxiv MCP 落盘说明）、[`scripts/`](scripts/)、[`progress_and_path_analysis.md`](progress_and_path_analysis.md)、[`AGENTS.md`](AGENTS.md)、[`.agents/skills/`](.agents/skills/)
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
# 1. 核对 Lean 公理审计 937/937 双射、0 sorryAx、23 白名单、0 项目自加公理、0 逃逸关键字
python verification\check_audit_reconcile.py verification\audit_final_20261122.log

# 2. 复跑核心符号、450 位区间、整数转移算子（m=4 与一般 m=2..6）、论文二两项新拓展 50 位验证及完整性检查
python verification\verify_round3.py
python verification\verify_round4.py
python verification\residue_certificate.py
python verification\residue_certificate_general.py
python verification\verify_paper2_extensions.py
python verification\verify_paper2_merge.py
```

论文一涉及的多尺度黄金比伴随脚本也可直接从原路径运行（例如）：

```powershell
python paper1_e_plus_pi\05_research_process\golden_finite_spectrum\golden_finite_spectrum.py
```

### 4.2 洁净环境从源码重编译 Lean 4 与重跑内核审计（需联网下载 Mathlib 预编译 cache）

```powershell
cd epi_formal
lake exe cache get
lake build EpiFormal
lake env lean Audit.lean | Out-File -Encoding utf8 ..\verification\audit_rerun.log
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
2. **数值认证与 Lean 内核分工边界**：`thm:windows`、`thm:short-ae`、`thm:no-short-dim`（含 $\dim_{\mathrm{H}}=1$ 与 $\operatorname{Leb}=0$）、`thm:finite-state-tail`（$\mathbb{R}$ 与 $\mathbb{T}$）以及 `thm:residues`/`thm:residues-general` 的一般模 Lipschitz/移位/最终周期不变性与转移算子可靠性桥接均已入 Lean 4 内核闭环；但 `thm:residues` 与 Table `tab:residues-general` 中 $N=256$、$K\in\{120,130\}$、$2^{80}$ 精度的具体有理矩阵谱隙数值求值仍由可复现精确整数脚本 [`residue_certificate.py`](verification/residue_certificate.py) 与 [`residue_certificate_general.py`](verification/residue_certificate_general.py) 执行，未在 Lean 内核中直接展开大矩阵算术计算。
3. **重耗时高精度脚本与联网洁净重构边界**：
   - 本轮批量复验中，4 个 2500 位高精度长耗时脚本（[`verify_golden_b3_b4_exact.py`](verification/verify_golden_b3_b4_exact.py)、[`verify_golden_b5_b6_multiscale.py`](verification/verify_golden_b5_b6_multiscale.py)、[`verify_golden_general_b.py`](verification/verify_golden_general_b.py)、[`verify_weighted_lower.py`](verification/verify_weighted_lower.py)）未等待其全程结束，仓内保留源码与历史 `.log` 供按需完整重跑；
   - 未在完全无缓存的联网环境中重新执行 `lake exe cache get && lake build EpiFormal`（已在本地完成 `9179 jobs` 全量构建、937/937 审计对账及全源码归档完整性校验）。
4. **投稿前人工完善项**：
   - [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex) 仍保留作者/单位占位符（`[Author name]`, `[Affiliation]`）与 `% TODO before submission:` 注释待正式投稿前由作者补充；
   - [`epi_formal/README.md`](epi_formal/README.md)、[`LEMMA_AUDIT.md`](epi_formal/LEMMA_AUDIT.md)、[`PROOF_GAPS.md`](epi_formal/PROOF_GAPS.md)、[`FINAL_REVIEW.md`](epi_formal/FINAL_REVIEW.md) 保留了 2026-11-14 初版 31 条基线记录作为历史档案，当前最新全量审计口径以本 `README.md`、[`Audit.lean`](epi_formal/Audit.lean) 及 [`verification/audit_final_20261122.log`](verification/audit_final_20261122.log) 为准。
