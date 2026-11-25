# $e+\pi$ 无理性研究与连分数谱/维数理论完整私有归档（2026-11-25 最新版）

> **一句总判断**：本仓库完成截至 **2026-11-25** 的全面整合与本地/GitHub 统一归档，涵盖两篇修订重编主论文（**Paper 1** 75 页 + **Paper 2** 66 页，洁净 `pdflatex` 0 错误 / 0 未定义引用 / 0 Overfull `\hbox`，且主稿与 `split/` 三轨拆分源码保持 `289,499` 字节逐字节同步、**28/28** 文献全引用、2A/2B/2C `0/0` 未定义引用）、全量 Lean 4 `v4.35.0` 形式化工程（全库 **344** 个 `.lean` 文件，0 逃逸关键字、`sorryAx = 0`；核心 `Audit.lean` **937/937** + `AuditResidueCert.lean` **27/27** + `AuditResidueMultiAsymptotic.lean` **24/24** 合计 **988** 条 Layer A 审计声明，及在 `main@833845f` 跑通的 GitHub Actions 双 CI 绿灯）、新课题 [`research/`](research/README.md)（Kahane 问题 Q6 与阶段规划）、T6 临界标度实验归档 [`drafts_v3_critical_scaling/`](paper2_spectral_gap_dimension/drafts_v3_critical_scaling/README.md) 以及全套符号/`python-flint==0.9.0` Arb 球算术/配置/证据核查脚本（全局导航见 [`REPOSITORY_STRUCTURE.md`](REPOSITORY_STRUCTURE.md)）；同时严格遵循 [`AGENTS.md`](AGENTS.md) 诚实基线——**$e+\pi$ 的无理性（及 $e\pi, e-\pi, \pi/e, \pi^e$ 单个的无理性）仍是公开问题，本仓库未证明 $e+\pi$ 无理、有理或超越。**

---

## 0. 最新更改情况（2026-11-24 / 2026-11-25）

1. **论文一与论文二文献核查补全与重编**：
   - **Paper 1**（`75` 页，0 错误 / 0 Overfull）：将 `Dan2026`（`arXiv:2609.12338v1`）、`Yu2026`（`arXiv:2606.17303v1`，145 候选/133 本原 Apéry 审计）更新为全文已核口径；区分 `openai/math` 中含 `sorry` 的挑战题面 `ComparatorChallenges/PiExponent.lean` 与主证明 `OAI/NumberTheory/PiExponent/Main.lean`；补充 `CDT2026`（Calegari–Dimitrov–Tang ICM 2026 `doi:10.1137/25m1806776`）、`Chudnovsky2026`（`arXiv:2610.31112v1`、`2610.26539v1`）、`Fauzan2026`（`10.5281/zenodo.22826419`）与 `Zapata2026`（`arXiv:2603.09719v5`）边界定位。
   - **Paper 2**（`66` 页，`289,499` 字节 / `4,574` 行，0 错误 / 0 Overfull）：通过 [`patch_evidence_citations_20261125.py`](paper2_spectral_gap_dimension/patch_evidence_citations_20261125.py) 与 [`patch_unify_20261125.py`](paper2_spectral_gap_dimension/patch_unify_20261125.py) 同步主稿、[`slice_index.csv`](paper2_spectral_gap_dimension/split/src_sections/slice_index.csv) 与 `split/` 四轨切片，补引 `Hensley1996`（附 *J. Number Theory* 59 勘误 `doi:10.1006/jnth.1996.0107`）、`JP2018`（`doi:10.1016/j.aim.2017.11.028`）、`CLN2026`（`doi:10.1016/j.indag.2026.03.008` / `arXiv:2504.20878v2`）、`CLUW2024`（`arXiv:2408.06330v2`）、`Brown2026`（`arXiv:2604.20812v2`，$E_{\{1,2\}}$ 9 位吻合外部对照）、`TTWW2026`（`arXiv:2511.02492v2`，实核第二作者 `Chen Tian`）与 `BW2025`（`arXiv:2510.18451v1`），并并入 `DFSU`（2023 定理 4.1）、`MU96`、`Good41`、`HU02`、`Hensley92`、`DLMF` 先例定位于 `sec:prior`；补齐全部 DOI 并去除 DOI 内 `\allowbreak`，使 **28/28** 文献 100% 被引用且分轨 `2A`（`*-2Apub` 21 页）/ `2B`（16 页）/ `2C`（26 页）保持 `0/0` 未定义引用。
2. **双通道证据深调与前沿调研档案**：
   - 新增 [`方法论证据支撑深调报告_20261125.md`](verification/方法论证据支撑深调报告_20261125.md)（覆盖 100 个去重 arXiv 基础号、89 篇 OpenAlex 文献、52 个 Crossref DOI 与 11 篇抽提 PDF，记录 8 项跨通道冲突与 6 项 Load-Bearing 勘误/撤稿审计）、[`工具库整理与六方向前沿调研记忆_20261125.md`](verification/工具库整理与六方向前沿调研记忆_20261125.md) 与 50 位高精度验证脚本 [`verify_evidence_numbers_20261125.py`](verification/verify_evidence_numbers_20261125.py) / [`.log`](verification/verify_evidence_numbers_20261125.log)。
3. **缺失工具补装、技能镜像与后续阶段规则硬化**：
   - 本地 Python `3.14.7` 已补装 `python-flint==0.9.0`，实测通过 [`rational_exclusion_bound_20261124.py`](verification/rational_exclusion_bound_20261124.py) `--selftest`（12/12 PASS）；本工作树补建 `.lake` 并实测 `lake build`（9384 jobs, EXIT 0）及三份 `Audit*.lean` 脚本全通过。
   - `.agents/skills/` 与 `.claude/skills/` 完成双根镜像同步，新增 `mathodology-evidence-search`（MIT）、`verified-research`（MIT）及 4 项 `leanprover/skills`（Apache-2.0），并附 API 授权声明 [`.licenses/`](.licenses/)；`verify_refs.py` 自检 `40/40` 单元测试通过且对 Paper 1（52 项）与 Paper 2（31 条识别项 / 28 bibitem，0 fail）均 `0 fail`。
   - 新增后续工作流与质量门禁规则 [`.agents/rules/next-step-workflow.md`](.agents/rules/next-step-workflow.md) 并在 [`AGENTS.md`](AGENTS.md) §8 建立索引。
4. **CI 工作流整合、跨平台依赖清单与投稿 Cover Letter 草稿（2026-11-25 续）**：
   - 合入仓库根目录 [`.github/workflows/lean-audit.yml`](.github/workflows/lean-audit.yml)、[`compare_audit_logs.py`](verification/compare_audit_logs.py) 与 [`verify_repo_integrity.py`](verification/verify_repo_integrity.py) 跨平台路径/Linux 兼容补丁（亦同步更新台账与 `OBL3b` 记录中相对链接），并在本机以实跑输出验证 `compare_audit_logs.py` 对 `937` / `27` / `24` 三份审计日志均 0 差异匹配；另增轻量快速门禁 [`.github/workflows/python-checks.yml`](.github/workflows/python-checks.yml)，且于 `main@833845f` 在 GitHub Actions 云端实测双 workflow 均跑出绿灯。
   - 新增跨平台 Python 依赖文件 [`requirements.txt`](requirements.txt) 与 [`pyproject.toml`](pyproject.toml)，以及诚实边界对齐的英文投稿信草稿 [`cover_letters_2AB_and_2C_draft_20261125.md`](paper2_spectral_gap_dimension/split/cover_letters_2AB_and_2C_draft_20261125.md)。
5. **三方结构统一（PR #1/#2 合流 + 本地 `epi_work` 资产整编 + 统一展望定稿）**：
   - 合并 PR #1 (`b6e7e48`) 与 PR #2 (`edc7673`，含 `paper2_novelty_review_20261125.md`、`patch_blr_baker_fix_20261125.py`、[`derive_2A_pub.py`](paper2_spectral_gap_dimension/split/derive_2A_pub.py) 2A 投稿呈现版 `*-2Apub.tex`、[`kahane_q6_note_20261125.md`](research/kahane_q6_note_20261125.md) 与 5 组数值探针、`value_rating_and_top_journal_gap_20261125.md`），并修正 `sec-resasymp.tex` 显示公式 `m^{-1-\varepsilon}` 笔误。
   - 零损失归档本地主检出 `epi_work` 的 `75` 份独特研究/规划/扫描/草案产物至 [`research/`](research/README.md)（含 `planning_20261124/`）、[`drafts_v3_critical_scaling/`](paper2_spectral_gap_dimension/drafts_v3_critical_scaling/README.md)（T6 临界标度实验线）、[`verification/`](verification/README.md)（35 项扫描/期刊/KMS/验收文件）与 [`verification/lean_drafts/paper_interfaces_20261124/`](verification/lean_drafts/README.md)（分篇接口隔离归档，保护 `epi_formal/` 3 条源公理净度），更新 [`.gitignore`](.gitignore)，并将本地与 GitHub 分支统一收敛到单一 `main`。

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
| 论文二扩展实验线 `T6` 临界标度（[`drafts_v3_critical_scaling/`](paper2_spectral_gap_dimension/drafts_v3_critical_scaling/README.md)）：`lem:pole`（Banach 空间 $A(\{|z-1|<1\})$）、`lem:resolvent-uniform`、`lem:master`、`thm:critical-scaling`（联合极限 $m^{1/2}(\dim_{\mathrm{H}}F_{m,S,B}-1/2)\to\Phi(x)/2$，指数 $1/2$、振幅 $\sqrt{d\kappa}/2$）、`rem:naive-C2-false`（证伪固定 $\eta$ 旧猜想 C2）与超临界常数猜想 | 无条件分析结果（论文正文证明，依赖仓库转移算子准则）+ 启发式猜想（超临界常数）+ 有限计算（334 点扫描） | 实验稿 v3 70 页 / 主稿 A 31 页编译 0 未定义引用；T6 分析层**未 Lean 形式化**，隔离接口 [`Paper2C.lean`](verification/lean_drafts/paper_interfaces_20261124/Paper2C.lean) 对 `lem:pole` 引入 1 条项目公理 `C_S_pole_decomposition`（仅内核证 `scaling_function_identity`）；未经同行审阅 | 基于 Perron–Frobenius + Kato 解析摄动与 Hurwitz 位移估计；负搜索未见显式临界窗联合标度极限定理先例；它没做到：**超临界常数 $\frac{d\kappa}{2(2s_0-1)}$ 未证**，未并入主稿 11 切片 | [`sec-critical-scaling.tex`](paper2_spectral_gap_dimension/drafts_v3_critical_scaling/sec-critical-scaling.tex)、[`verify_c2_discrepancy_20261124.py`](verification/verify_c2_discrepancy_20261124.py)、[`critical_point_scan_20261124.py`](verification/critical_point_scan_20261124.py)、[`Paper2C.lean`](verification/lean_drafts/paper_interfaces_20261124/Paper2C.lean) |
| 论文一：仿射窗口显式周期 $2B|C|$、黄金比轨道有限谱与 $B=1\text{--}6$ / 四类多尺度有理端点刚性；全部 8 个原独立 Lean 辅助模块（共 29 条声明）并入主工程与统一审计 | 无条件模型/归约结果 + 已有辅理统一机器复核 | **已核实**（72 页重编 0 错误/0 警告；原独立 8 模块——`GoldenHeadCutoff`, `GoldenAffineEndpoint`, `AffineWindowAudit`, `DigitTailBound`, `DensityCube`, `OrbitAndFlow`, `ResearchAdvance`, `TraceMarkov`——全部并入 `EpiFormal.lean` 与 `Audit.lean`，共 29 条声明仅用基础公理） | 用 Bugeaud 二次 Mobius 恒等式研究 $A/B-e$ 与 $(A+Ce)/B$ 模型；模型与窗口研究**不解决 $e+\pi$ 无理性** | [`paper1_e_plus_pi.pdf`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf)、[`GoldenHeadCutoff.lean`](epi_formal/EpiFormal/GoldenHeadCutoff.lean)、[`GeneralEndpointRigidity.lean`](epi_formal/EpiFormal/GeneralEndpointRigidity.lean)、[`EpiFormal.lean`](epi_formal/EpiFormal.lean) |
| 论文一 `prop:denominator-bounds`（2026-11-24）：Arb 球算术严格包络 + 区间内最简有理数，得**若 $x\in\{e+\pi,e\pi,\pi-e,\pi/e\}$ 且 $x=p/q$，则 $q\ge10^{500018}$**（$D=10^6$，本机与 Colab 两台机器输出逐项一致）；并以严格包络复核 OEIS A058651 全部 20000 个部分商（$q_{19998}$ 有 10149 位） | 有限计算或有限排除（只排除有限范围） | **已核实**（两机复现；自检 12/12 PASS） | 负搜索未见以“若 $e+\pi=p/q$ 则 $q>N$”形式发表的界（检索范围：OEIS、MathWorld、Wikipedia、三次网络检索；**负搜索≠不存在**）；Bailey 1988 摘要排除了 $e+\pi$ 满足次数 $\le8$、系数欧氏范数 $\le10^9$ 的代数方程（只核了摘要）。它没做到：**不涉及无理性**，更大分母的有理数未被排除，$e+\pi$ 仍开放 | [`rational_exclusion_bound_20261124.py`](verification/rational_exclusion_bound_20261124.py)、[`exclusion_runs_20261124/`](verification/exclusion_runs_20261124/)、[`oeis_a058651_crosscheck_20261124.py`](verification/oeis_a058651_crosscheck_20261124.py) / [`.log`](verification/oeis_a058651_crosscheck_20261124.log)、[`patch_denominator_bounds_20261124.py`](paper1_e_plus_pi/01_main_paper/patch_denominator_bounds_20261124.py) |
| 论文一：$e+\pi$ 无理性归约、Flint Hills 条件桥接、Alekseyev 方向（$\text{收敛}\Rightarrow\mu(\pi)\le 5/2$）、逃逸约化（P1）与四路障碍分析 | 等价改写/换靶 + 条件结果 + 障碍分析 + Lean 4 机器验证 | **已核实**（23 条经典定理推导显式依赖 3 条经典白名单公理；Meiburg Flint Hills 情况与 Alekseyev 方向已机器形式化，无项目自加公理） | 仅做条件桥接、等价换靶（如 P1 晶格逃逸）或排除特定构造；明确不宣称解决原问题或“更接近证明” | [`FlintHills.lean`](epi_formal/EpiFormal/FlintHills.lean)、[`MeiburgConvergence.lean`](epi_formal/EpiFormal/MeiburgConvergence.lean)、[`Alekseyev.lean`](epi_formal/EpiFormal/Alekseyev.lean)、[`Escape.lean`](epi_formal/EpiFormal/Escape.lean) |
| 符号、区间与精确整数/Chebyshev 数值核验脚本（`verify_round3.py`、`verify_round4.py`、`residue_certificate_general_N512.py`、`verify_residue_multi_asymptotic.py` 等） | 有限计算或有限排除（Python 数值核验） | **已核实**（SymPy `12/12` PASS；450 位 `mpmath.iv`；`residue_certificate_general_N512.py` 以 $N=512$, $S=10^{13}$, $K\in\{120,\dots,258\}$ 精确整数算术认证 10 组 $N=512$ 区间与严格隙 [其闭区间已在 `ResidueCertTable.lean` 复跑]，`verify_residue_multi_asymptotic.py` 32 位 Chebyshev 配置法全面复核 10 组次临界三阶渐近与 `{1,2}`/`{1,2,3}` 超临界速率并 `ALL CHECKS PASSED`） | 对有限分母、有限窗口与有限格点算子给数值佐证或有限精确整数计算；多残差 32 位 Chebyshev 数值结果明确标为佐证而非证明 | [`verify_round3.py`](verification/verify_round3.py)、[`verify_round4.py`](verification/verify_round4.py)、[`residue_certificate_general_N512.py`](verification/residue_certificate_general_N512.py)、[`verify_residue_multi_asymptotic.py`](verification/verify_residue_multi_asymptotic.py) |
| CMMS 一次文献核查与论文二全篇纠偏 | 文献核查与复现 | **已核实**（下载并逐页核对 *Pacific J. Math.* 217(1) (2004), pp. 45–59 官方刊出全文，确认 §5 主定理为 **Theorem 3** 而非误写的 Theorem 5；论文二三处引文已全部更正重编） | Cabrelli–Mendivil–Molter–Shonkwiler, *Pacific J. Math.* 217(1) (2004), 45–59, `doi:10.2140/pjm.2004.217.45`（pp. 57–58, §5 Theorem 3） | [`cmms_citation_check_20261122.md`](verification/cmms_citation_check_20261122.md)、[`CMMS_PJM_2004_217_45.pdf`](verification/reference_pdfs/CMMS_PJM_2004_217_45.pdf) |
| 新课题（2026-11-25，与论文一、论文二无关）：**Kahane 问题 Q6**（C. R. Acad. Sci. Paris 352 (2014)，原文逐字核对）。定理 2：对几乎每个目标序列 $(b_n)$，$\dim_H(E(\varepsilon)\cap[1,X])\le\log(2\varepsilon X)/\log X$，与 Kahane 的下界合起来两侧相差约 $2/(X\log X)$；定理 3：几乎处处的淬火下界，在 7 组样本中优于 Kahane 的界，但非处处更优 | 无条件新结果（窄；标准第一矩方法与沿路径大数定律） | 本人推导，定理 2、定理 3 各经一次子代理独立对抗审阅并按意见修改；**未经同行审阅** | 负搜索未见先例（arXiv、Crossref、网页，引用 Kahane 2014 的 4 篇；**未**查 MathSciNet、zbMATH） | [`kahane_q6_note_20261125.md`](research/kahane_q6_note_20261125.md) §2、§3d |
| Kahane Q6 精确下界（几乎处处）：二阶矩恒等式与正表示（命题 P1）、两种导数检验的部分证明（命题 P2），归约为"引理 R ⇒ D′ ⇒ 引理 D" | 等价改写与部分结果；**精确下界未证** | P1、P2 经一次独立对抗审阅；引理 R 开放 | 负搜索未见可直接套用的工具（Shmerkin–Suomala 的空间独立性不满足；Aistleitner–Baker 的方法需推广） | [`kahane_q6_note_20261125.md`](research/kahane_q6_note_20261125.md) §3b、§3c‴ |
| Kahane Q6 数值证据：确定目标（$b_n\equiv0$、$\frac12$）下增长率与 $2\varepsilon v$ 吻合到 0.8% 内；超临界时鞅二阶矩有界、次临界时趋于灭绝；Fourier 能量按约 $1/(2\varepsilon v)$ 衰减 | 有限计算（佐证，非证明） | 脚本、日志与 JSON 可复查 | — | [`powers_mod1_dimension_numerics_20261125.py`](verification/powers_mod1_dimension_numerics_20261125.py)、[`kahane_martingale_sim_20261125.py`](verification/kahane_martingale_sim_20261125.py)、[`kahane_lemmaD_fourier_20261125.py`](verification/kahane_lemmaD_fourier_20261125.py)、[`kahane_lemmaD_rate_fit_20261125.py`](verification/kahane_lemmaD_rate_fit_20261125.py)、[`kahane_quenched_bound_table_20261125.py`](verification/kahane_quenched_bound_table_20261125.py) |

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
- **论文一（75 页，0 错误 / 0 未定义引用 / 0 Overfull `\hbox`）**：
  - 源码：[`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex)
  - 成稿 PDF 与日志：[`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf)、[`paper1_e_plus_pi.log`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.log)
- **论文二（66 页，0 错误 / 0 未定义引用 / 0 Overfull `\hbox`；含 §7.5 `thm:multi-residue-asymptotic`、`rem:fourth-term`、28/28 全文献与新颖性修正）**：
  - 源码与补丁脚本：[`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex)、[`patch_evidence_citations_20261125.py`](paper2_spectral_gap_dimension/patch_evidence_citations_20261125.py)、[`patch_novelty_wording_20261125.py`](paper2_spectral_gap_dimension/patch_novelty_wording_20261125.py)、[`patch_unify_20261125.py`](paper2_spectral_gap_dimension/patch_unify_20261125.py)
  - 成稿 PDF 与日志：[`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.pdf`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.pdf)、[`paper2_spectral_gap_dimension.log`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.log)
  - 拆分三轨及补充工程（总览 [`split/README.md`](paper2_spectral_gap_dimension/split/README.md)；与主稿 11 个切片拼接 **289,499 字节逐字节一致**；2A `*-2Apub` 21 页 / 2B 16 页 / 2C 26 页均 0 未定义引用、0 Overfull；S 8 页）：[`paper2_spectral_gap_dimension/split/`](paper2_spectral_gap_dimension/split/)
  - `T6` 临界标度 `v3` 与两主稿实验存档：[`paper2_spectral_gap_dimension/drafts_v3_critical_scaling/`](paper2_spectral_gap_dimension/drafts_v3_critical_scaling/README.md)（独立归档 `sec-critical-scaling.tex`、`v3` 70 页、主稿 A 31 页、主稿 B 35 页）
- **新课题与阶段规划档案（[`research/`](research/README.md)）**：[`kahane_q6_note_20261125.md`](research/kahane_q6_note_20261125.md)（Kahane 问题 Q6）与 2026-11-24 阶段规划 [`planning_20261124/`](research/planning_20261124/master_overview_20261124.md)
- **历史 B 稿完整备份（65 页，已明确标为历史归档）**：
  - [`paper1_e_plus_pi/02_companion_paper/Phase2_revised.tex`](paper1_e_plus_pi/02_companion_paper/Phase2_revised.tex) / [`.pdf`](paper1_e_plus_pi/02_companion_paper/Phase2_revised.pdf) / [`.log`](paper1_e_plus_pi/02_companion_paper/Phase2_revised.log)
- **论文一投稿准备与论文二历史稿**：
  - [`paper1_e_plus_pi/03_submission_prep/`](paper1_e_plus_pi/03_submission_prep/)（cover letter、AI 贡献草稿、核对清单等）
  - [`paper1_e_plus_pi/04_formalization_audits/`](paper1_e_plus_pi/04_formalization_audits/)（早期单文件审计记录与旧日志）
  - [`paper2_spectral_gap_dimension/historical_versions/`](paper2_spectral_gap_dimension/historical_versions/)（`paper2_old.tex/.pdf`、`paper2_20261118.tex/.pdf`、`paper2_integrated_v20261122_ed61a92.tex`、`paper2_integrated_v20261123_1e91028.tex/.pdf`、`paper2_integrated_v20261123_7ece3b9.tex` 等）

### 2. Lean 4 完整形式化工程（[`epi_formal/`](epi_formal/)）
- 工具链与清单：[`lean-toolchain`](epi_formal/lean-toolchain)（`leanprover/lean4:v4.35.0`）、[`lakefile.toml`](epi_formal/lakefile.toml)、[`lake-manifest.json`](epi_formal/lake-manifest.json)
- 总入口与独立审计脚本：[`EpiFormal.lean`](epi_formal/EpiFormal.lean)、[`Audit.lean`](epi_formal/Audit.lean)（937 条核心双射）、[`AuditResidueCert.lean`](epi_formal/AuditResidueCert.lean)（27 条残差证书表审计）、[`AuditResidueMultiAsymptotic.lean`](epi_formal/AuditResidueMultiAsymptotic.lean)（24 条多残差推广审计）
- 分轨评审与分篇接口隔离草案：[`EpiFormal2A_Draft.lean`](epi_formal/EpiFormal2A_Draft.lean)、[`EpiFormal2B_Draft.lean`](epi_formal/EpiFormal2B_Draft.lean)、[`EpiFormal2C_Draft.lean`](epi_formal/EpiFormal2C_Draft.lean)；分篇接口 [`Paper2{A,B,C}.lean`](verification/lean_drafts/README.md) 隔离存于 `verification/lean_drafts/paper_interfaces_20261124/`（其中 `Paper2C.lean` 含 `axiom C_S_pole_decomposition`）。
- 全量 337 个 `EpiFormal/` 子模块源码：[`epi_formal/EpiFormal/`](epi_formal/EpiFormal/)（含 2026-11-22 新增的 [`WindowShortAeRealize.lean`](epi_formal/EpiFormal/WindowShortAeRealize.lean)、[`ResidueModGeneral.lean`](epi_formal/EpiFormal/ResidueModGeneral.lean)、[`TransferOperatorDim.lean`](epi_formal/EpiFormal/TransferOperatorDim.lean)、[`FiniteStateComplete.lean`](epi_formal/EpiFormal/FiniteStateComplete.lean)、[`ResidueAsymptotic.lean`](epi_formal/EpiFormal/ResidueAsymptotic.lean)、[`GeneralGrowingRec.lean`](epi_formal/EpiFormal/GeneralGrowingRec.lean)、[`GeneralGrowingDim.lean`](epi_formal/EpiFormal/GeneralGrowingDim.lean)、[`WindowBoundedUpper.lean`](epi_formal/EpiFormal/WindowBoundedUpper.lean) 与并入的 8 个论文一模块，以及 2026-11-23 新增的 [`ResidueCertTable.lean`](epi_formal/EpiFormal/ResidueCertTable.lean) / `ResidueCertGen/` 与 [`ResidueMultiAsymptotic.lean`](epi_formal/EpiFormal/ResidueMultiAsymptotic.lean)）
- 阶段性基线与历史文档（含 2026-11-23 更新头注）：[`epi_formal/README.md`](epi_formal/README.md)、[`LEMMA_AUDIT.md`](epi_formal/LEMMA_AUDIT.md)、[`PROOF_GAPS.md`](epi_formal/PROOF_GAPS.md)、[`FINAL_REVIEW.md`](epi_formal/FINAL_REVIEW.md)

### 3. 核验脚本、审计日志、数学记录与一次文献（[`verification/`](verification/)）
- **分类总导航与一体体检**：[`verification/README.md`](verification/README.md)、[`verify_repo_integrity.py`](verification/verify_repo_integrity.py) / [`.log`](verification/verify_repo_integrity.log)（全库零遗漏/审计/论文/链接一站式核查）、[`compare_audit_logs.py`](verification/compare_audit_logs.py)（937/27/24 公理审计逐条比对器）
- **核心审计与对账**：[`audit_final_20261122.log`](verification/audit_final_20261122.log)、[`audit_residue_cert_20261123.log`](verification/audit_residue_cert_20261123.log)、[`audit_residue_multi_asymptotic_20261123.log`](verification/audit_residue_multi_asymptotic_20261123.log)、[`check_audit_reconcile.py`](verification/check_audit_reconcile.py)
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
  - 2026-11-23 / 24 核心复现与扫点档案：[`colab_rebuild_audit_20261123.md`](verification/colab_rebuild_audit_20261123.md)、[`colab_rebuild_audit_20261124.md`](verification/colab_rebuild_audit_20261124.md)、[`residue_certgen_lean_20261123.md`](verification/residue_certgen_lean_20261123.md)、[`cert_v3_redesign_20261123.md`](verification/cert_v3_redesign_20261123.md)、[`paper2_novelty_review_20261123.md`](verification/paper2_novelty_review_20261123.md)、[`论文二拆分分类与Lean精准映射_20261123.md`](verification/论文二拆分分类与Lean精准映射_20261123.md)、[`推广1_多残差相变与欧拉常数三阶渐近Lean4记录_20261123.md`](verification/推广1_多残差相变与欧拉常数三阶渐近Lean4记录_20261123.md)、[`critical_point_scan_record_20261124.md`](verification/critical_point_scan_record_20261124.md)、[`verify_c2_discrepancy_20261124.py`](verification/verify_c2_discrepancy_20261124.py)、[`journal_landscape_20261124.md`](verification/journal_landscape_20261124.md)、[`kms_comparison_materials_20261124.md`](verification/kms_comparison_materials_20261124.md)
  - 2026-11-25 证据深调、新颖性重审、顶刊差距与价值评级：[`方法论证据支撑深调报告_20261125.md`](verification/方法论证据支撑深调报告_20261125.md)、[`工具库整理与六方向前沿调研记忆_20261125.md`](verification/工具库整理与六方向前沿调研记忆_20261125.md)、[`verify_evidence_numbers_20261125.py`](verification/verify_evidence_numbers_20261125.py) / [`.log`](verification/verify_evidence_numbers_20261125.log)、[`paper2_novelty_review_20261125.md`](verification/paper2_novelty_review_20261125.md)、[`paper2_novelty_crosscheck_20261125.py`](verification/paper2_novelty_crosscheck_20261125.py) / [`.log`](verification/paper2_novelty_crosscheck_20261125.log)、[`candidateA_precedent_search_20261125.md`](verification/candidateA_precedent_search_20261125.md)、[`paper2_venue_gap_assessment_20261125.md`](verification/paper2_venue_gap_assessment_20261125.md)、[`value_rating_and_top_journal_gap_20261125.md`](verification/value_rating_and_top_journal_gap_20261125.md)
  - 2026-11-25 新课题与规划归档（[`research/README.md`](research/README.md)）：[`kahane_q6_note_20261125.md`](research/kahane_q6_note_20261125.md)（含上表 5 组 Kahane 数值脚本与日志/JSON）及 2026-11-24 阶段规划 [`planning_20261124/`](research/planning_20261124/master_overview_20261124.md)
  - [`verification/reference_pdfs/`](verification/reference_pdfs/)（含官方 [`CMMS_PJM_2004_217_45.pdf`](verification/reference_pdfs/CMMS_PJM_2004_217_45.pdf)、`h-sets.pdf`、`BLR_1710_03596.pdf`、`CLU_1805_11904.pdf`、`MEA_2511_10328v3.pdf`）
  - [`build_desktop_package_20261122.py`](verification/build_desktop_package_20261122.py)（桌面完整交付包组装与端到端复验脚本）

### 4. 研究过程与历史全量归档
- [`paper1_e_plus_pi/05_research_process/`](paper1_e_plus_pi/05_research_process/)（分轮研究目录 `A`–`E`、`golden_finite_spectrum/` 及 `golden_finite_spectrum.py` 等 9 个论文一伴随证书脚本与实验日志）
- [`paper1_e_plus_pi/06_historical_versions/`](paper1_e_plus_pi/06_historical_versions/)（1–8 轮演化备份及 `archive_snapshots/` 快照包）
- [`downloads/`](downloads/)（文献下载缓存 PDF：`1211.2494.pdf`、`1805.11904v1.pdf`）、[`papers/README.md`](papers/README.md)（arxiv MCP 落盘说明）、[`scripts/`](scripts/)、[`progress_and_path_analysis.md`](progress_and_path_analysis.md)、[`AGENTS.md`](AGENTS.md)、[`.agents/rules/next-step-workflow.md`](.agents/rules/next-step-workflow.md)、[`REPOSITORY_STRUCTURE.md`](REPOSITORY_STRUCTURE.md)、[`.agents/skills/`](.agents/skills/)、[`.claude/skills/README.md`](.claude/skills/README.md)、[`.licenses/`](.licenses/)
- 工作区根目录下配合重组的 PowerShell 脚本：[`rename_english_20261121.ps1`](rename_english_20261121.ps1)、[`reorganize_step1_20261121.ps1`](reorganize_step1_20261121.ps1)、[`reorganize_step2_20261121.ps1`](reorganize_step2_20261121.ps1)

> **关于未上传的大体积缓存与本地工具文件**（已在 [`.gitignore`](.gitignore) 中排除）：
> - `epi_formal/.lake/`（约 **8.49 GB** 本地 Mathlib `.olean`/编译产物缓存，可通过下方 `lake exe cache get && lake build EpiFormal` 全量复现）
> - `.venv/`、`Python/`（本地 Python 环境）
> - `.opencode/`、`.zcode/`、`.zwork/`、`opencode.json`、`opencode.json.bak-*`（本地编辑器/Agent 运行时配置与目录）
> - `**/__pycache__/`、`*.pyc`、LaTeX 中间产物 `*.aux`/`*.out`/`*.toc`/`*.fls`/`*.fdb_latexmk`/`*.synctex.gz`，以及分轨可再生 PDF 与工作区根目录外溢副本 `split/2*/paper2*_draft.{pdf,log}`

---

## 四、完整复现指南

### 4.1 离线核对审计日志与核心 Python 证书（无需联网）

需安装 Python 依赖（Linux / macOS / Windows 通用：`pip install -r requirements.txt`，含 `sympy >= 1.14`、`mpmath >= 1.3`、`python-flint >= 0.9` 等，详见 [`requirements.txt`](requirements.txt) 与 [`pyproject.toml`](pyproject.toml)）：

```bash
# Linux / macOS / Windows（PowerShell 或 bash 均可，Windows 可用 python 或 py）
python3 verification/verify_repo_integrity.py
python3 verification/check_audit_reconcile.py verification/audit_final_20261122.log
python3 verification/rational_exclusion_bound_20261124.py --selftest
python3 verification/verify_evidence_numbers_20261125.py
```

```powershell
# 0. 一键全仓库零遗漏/审计/论文/链接统一体检
python verification\verify_repo_integrity.py

# 1. 核对主审计 937/937 双射、0 sorryAx、23 白名单、0 项目自加公理、0 逃逸关键字（扫描全库 344 个 Lean 文件）
python verification\check_audit_reconcile.py verification\audit_final_20261122.log

# 2. 复跑核心符号、450 位区间、Arb 有限排除、N=256/512 整数转移算子、50/32 位渐近及文献核验与论文切片检查
python verification\verify_round3.py
python verification\verify_round4.py
python verification\rational_exclusion_bound_20261124.py --selftest
python verification\verify_evidence_numbers_20261125.py
python verification\residue_certificate.py
python verification\residue_certificate_general.py
python verification\residue_certificate_general_N512.py
python verification\verify_paper2_extensions.py
python verification\verify_residue_multi_asymptotic.py
python verification\verify_paper2_merge.py
python paper2_spectral_gap_dimension\split\undef_ref_audit.py
python .agents\skills\mathodology-evidence-search\scripts\verify_refs.py paper1_e_plus_pi\01_main_paper\paper1_e_plus_pi.tex
python .agents\skills\mathodology-evidence-search\scripts\verify_refs.py paper2_spectral_gap_dimension\paper2_spectral_gap_dimension.tex
python -m unittest discover -s .agents\skills\mathodology-evidence-search\scripts -v
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

### 4.4 CI：Lean 重建、Python 验证与公理审计（GitHub Actions）

- [`.github/workflows/lean-audit.yml`](.github/workflows/lean-audit.yml)：在每次 push / pull request 到 `main` 以及手动触发（`workflow_dispatch`）时，于 `ubuntu-latest` 上安装 `elan`、执行 `lake exe cache get` → `lake build`（并显式检查 `EpiFormal.ResidueCertTable` 与 `EpiFormal.ResidueMultiAsymptotic`），再用 [`verification/compare_audit_logs.py`](verification/compare_audit_logs.py) 将 `Audit.lean`（937 条）、`AuditResidueCert.lean`（27 条）及 `AuditResidueMultiAsymptotic.lean`（24 条）输出与仓库参考日志逐条比对并运行 `check_audit_reconcile.py`；另一并行 job 执行 `verify_repo_integrity.py`。
- [`.github/workflows/python-checks.yml`](.github/workflows/python-checks.yml)：通过 [`requirements.txt`](requirements.txt) 在 `ubuntu-latest`（Python 3.12）快速运行 `verify_repo_integrity.py`、`rational_exclusion_bound_20261124.py --selftest`、`verify_evidence_numbers_20261125.py`、`verify_round3.py`、`verify_round4.py` 与 40 项 `verify_refs` 离线单元测试。
- 按 `AGENTS.md` §5：workflow 定义本身不构成核实，仅在 GitHub Actions 云端实际跑出绿灯后方计作云端独立复现。截至目前，`main@833845f` 已于 GitHub Actions `ubuntu-latest` 实测完成两项 workflow 并均获 `success`（`Python verification & repository checks` #1 与 `Lean build and axiom audit` #2，及 `b6e7e48` 上的运行 #1）；此后新提交的云端状态仍待相应 Actions 运行完毕后确认。

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

---

## 六、未来展望与路径预测（2026-11-25 统一版）

> **一句总判断**：
> - **$e+\pi$**：本项目在可预见的将来**不会**证明 $e+\pi$ 的无理性。计算只能扩大有限排除范围（类别 4），不能给出证明。
> - **论文二**：`2A+2B` 合并稿与 `2C`（包括归档于实验线的 `T6` 临界标度节）投度量数论 / 动力系统专业期刊是现实的（价值评估详见 [`value_rating_and_top_journal_gap_20261125.md`](verification/value_rating_and_top_journal_gap_20261125.md)）；在现有数学深度下直接冲顶刊（T1）不现实。
> - **Kahane 问题 Q6**：最有潜力产生独立新数学的方向——几乎处处上界（定理 2）与淬火弱下界（定理 3）已推进并经内部对抗审阅，能否达到完整期刊论文水准取决于开放的**引理 R**；所有新方向目前均未经外部同行评审。
>
> 下表中的“可能性”与期刊档位判断是作者与助手基于仓内既有核查的**主观定性判断**，不是计算出的概率，也不代表任何期刊的审稿意见。

### 6.1 各方向的路径与预测

| 方向 | 下一步 | 预期产出 | 可能性（主观） | 不会做到什么 |
| :--- | :--- | :--- | :--- | :--- |
| **Kahane Q6（几乎处处版本）** | 优先把定理 2 与定理 3 整理成短文，补查 MathSciNet/zbMATH 引用链后送同行审阅 | *C. R. Math.* 类短文（T4，内部评价接近 B−） | **中**（需同行确认，目前仅经过子代理对抗审阅） | 只覆盖几乎每个目标序列，不覆盖 Kahane 确定性原问题 |
| **Kahane Q6（精确下界与推广）** | 攻关证明**引理 R**（双重共振项 / 共振级联估计），补能量形式与 0–1 律；在 Colab 上将 $D'$ 数值推向更深层数；视进展推广至一般 $f_n, \delta_n\to0$ | 对几乎每个目标序列完整回答 Q6 的期刊论文（T3），及后续一般化 | **中低**（需要新的共振级联估计；数值支持 $D'$，但数值不是证明） | 即使解决几乎处处 Q6，仍不解决对**每一个**目标序列的原问题（原问题解决可能性低） |
| **Lean 4 形式化工程** | 将 988 条 Layer A 证明中可复用的 Hausdorff 测度/规范工具提炼并尝试上游化至 Mathlib，独立撰写形式化论文并附完整可复现制品（CI 已就绪） | ITP / CPP 等形式化会议或期刊论文 | **中**（本领域内最接近顶会水准的一条线） | 形式化规模不提升数学结果本身的数学新颖性或期刊档位 |
| **论文二 `2A+2B` 合并稿** | 用公开同伴/仓库引用替换内部 `Phase1` 归档，以“任意增长商递推”为主定理、$e$ 收敛分母作旗舰推论，基于 `*-2Apub` 风格消去工程叙事并补齐作者占位 | *J. Number Theory* / *Acta Arith.* / *ETDS* 等专业刊主论文（T4，偶有 T3 可能） | 专业刊：**中**；顶刊：**低** | 线性情形去掉 BLR 条件 (1.6) 属已知方法（[`candidateA_precedent_search_20261125.md`](verification/candidateA_precedent_search_20261125.md)）；写作包装不会改变核心数学深度 |
| **论文二 `2C` 与 `T6` 临界标度** | 主线 `2C` 按新颖性核查措辞投专业短文；实验线 `T6`（[`sec-critical-scaling.tex`](paper2_spectral_gap_dimension/drafts_v3_critical_scaling/sec-critical-scaling.tex)）优先将 $D_K$ 机制形式化、推进超临界常数 $\frac{d\kappa}{2(2s_0-1)}$ 解析突破并将近临界验证推至 $m=2^{18}\text{--}2^{20}$；待独立核验后再决定是否并入标准 11 切片 | `2C` 专业期刊论文（T4）；若超临界常数与 `T6` 彻底闭合且经外部审验，可提升 `2C+T6` 统一稿档位 | `2C` 单独：**中**；超临界常数完全解析突破：**低至中低** | 大 $m$ 渐近是 DFSU 框架的显式实例；`T6` 超临界主导常数仍是启发式猜想，$s_0(S)=1/2$ 精确构造性与 $\kappa(S)$ 连续性未解 |
| **论文一：$e+\pi$ 无理性** | 维持归档守势（条件靶点季检、Arb 有限排除按需扩展），按 `AGENTS.md` 纪律**禁止**把有限排除与等价换靶宣称为逼近证明 | 只扩大有限分母/代数范数排除范围（类别 4）或作形式化案例 | 证明无理性：**极低**；扩大有限排除：高 | 不证明无理性或超越性；不主张“更接近证明” |

### 6.2 预计推进顺序

1. **近期（整理、核对、CI 与同行预审，投入低）**：
   - 完成 Kahane Q6 定理 2、定理 3 短文初稿，并补查 MathSciNet / zbMATH 引用链后送熟悉幂次模 $1$ 的同行；
   - 核对新推提交在 GitHub Actions（`lean-audit.yml` 与 `python-checks.yml`）的云端跑测结果；
   - 为论文二完成投稿前 3 项人工放行门禁（替换 `Phase1`、补填作者/单位、`Use of AI` 与人工逐行审阅声明），整合 `2A+2B` 投递稿源与配套 Cover Letter。
2. **中期（新数学攻关与上游化，需要实质创新或工程投入）**：
   - 攻关 Kahane **引理 R** 与 $0\text{--}1$ 律，在大尺度下交叉检验猜想 $D'$；
   - 提炼 Paper 2 Lean 4 的 `hausdorffMeasure` / 规范与金属连分数证明工具，整理可独立发表的形式化成果；
   - 在 `T6` 临界标度线上推进 $D_K$ 有限子字母表机制的 Lean 内核替代（以消除 `Paper2C.lean` 中的 `C_S_pole_decomposition` 公理）并探索超临界前因子的无 Hurwitz 近似分析。
3. **长期 / 开放基线**：
   - Kahane Q6 对**每一个**具体目标序列的精确局部维数；
   - $e+\pi$、$e\pi$、$e-\pi$、$\pi/e$、$\pi^e$ 的无理性或超越性仍是世界公开问题，本项目不对此作进展预测。

### 6.3 会改变上述判断的信号

- **引理 R 被证明（且能量/0–1 律闭合）**：Kahane 方向评价上调为“可期待一篇扎实的独立期刊论文”。
- **外部同行审阅发现新定理存在缺口（Kahane 定理 2/3 或 T6 `lem:master` 等）**：相应结论立即降级或撤回重证，并在本表中如实修订。
- **MathSciNet / zbMATH 引用链检索发现先例**：本仓库迄今未系统检索该二库；一旦检出先例，“负搜索未见先例”一栏须全部改写，对应结果降为“文献核查与复现”。
- **外部数学界对 $e+\pi$ 取得公认突破**：及时文献跟进，不改变本仓库现有工作“未证明 $e+\pi$”的历史事实。
