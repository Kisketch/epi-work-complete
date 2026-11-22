# $e+\pi$ 无理性研究与连分数谱/维数理论完整私有归档（2026-11-22 最新版）

> **一句总判断**：本仓库完整归档截至 **2026-11-22** 的最新研究全貌，涵盖两篇修订重编主论文（**Paper 1** 72 页 + **Paper 2** 48 页，洁净 `pdflatex` 0 错误 / 0 警告 / 0 Overfull `\hbox`）、全量一体化的 Lean 4 `v4.35.0` 形式化工程（`lake build EpiFormal` **9172 jobs** EXIT 0，`127` 个 `.lean` 文件，`Audit.lean` **828/828** 条 `#print axioms` 严格双射 = **805** 条仅用 Lean 基础公理 [含 5 条零公理] + **23** 条论文一经典白名单公理 + **0** 条项目自加公理，`sorryAx = 0`，0 逃逸关键字）、全部符号/高精度区间/精确整数认证脚本与日志、CMMS 官方刊出全文一次文献核查，以及全部研究过程记录与历史版本快照；同时严格遵循 [`AGENTS.md`](AGENTS.md) 诚实基线——**$e+\pi$ 的无理性（及 $e\pi, e-\pi, \pi/e, \pi^e$ 单个的无理性）仍是公开问题，本仓库未证明 $e+\pi$ 无理、有理或超越。**

---

## 一、成果诚实分类与逐项对照表（遵循 `AGENTS.md` 五分法）

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| 论文二：沿 $e$ 收敛子分母 $Q_j$ 的全谱离散化 $\Lambda(\mathbb{R})=\frac14\mathbb{Z}_{\ge0}\cup\{\infty\}$、正能级三分法（含 $L$-陪集坍缩）、临界/二值精确 Hausdorff 规范（$\mathbb{R}$ 与 $\mathbb{R}/\mathbb{Z}$ 原生商圆环）、一般 $(cj^r+d)$ 多项式递推与次临界维数相变 $1-\alpha/r$ | 无条件新结果 + Lean 4 Layer A 机器验证 | **已核实**（仅依赖 Lean 基础三公理 `propext`, `Classical.choice`, `Quot.sound`；0 `sorryAx`；0 项目自加公理） | 在 Kraaikamp–Liardet 零能级准则（[BDS] Lemma 4.1）基础上的独立谱离散化、正能级精细三分法、临界规范与一般递推维数理论 | [`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex)、[`GaugeCircle.lean`](epi_formal/EpiFormal/GaugeCircle.lean)、[`TrichotomyAndPolyExtension.lean`](epi_formal/EpiFormal/TrichotomyAndPolyExtension.lean)、[`PolyGaugeAndPhaseTransition.lean`](epi_formal/EpiFormal/PolyGaugeAndPhaseTransition.lean) |
| 论文二 `thm:windows` 全四条（奇偶分支 $\dim_{\mathrm{H}}=1$ 与有界/指定窗口增量 $\dim_{\mathrm{H}}=1/2$ 上下界）与 `thm:no-short-dim` 维数部分（$\dim_{\mathrm{H}}=1$） | 无条件新结果 + Lean 4 Layer A 端到端机器验证 | **已核实**（21 条 `WindowBoundedUpper` + 此前 `WindowPrescribedCFRealize` / `WindowNoShortCFRealize` 等全链通过 mathlib `GenContFract.of` 与 `hausdorffMeasure_apply` 闭环，仅基础三公理） | 对 $e$ 收敛子尺度窗口连分数商增长/奇偶限制集的精确 Hausdorff 维数结果 | [`WindowBoundedUpper.lean`](epi_formal/EpiFormal/WindowBoundedUpper.lean)、[`WindowPrescribedCFRealize.lean`](epi_formal/EpiFormal/WindowPrescribedCFRealize.lean)、[`WindowNoShortCFRealize.lean`](epi_formal/EpiFormal/WindowNoShortCFRealize.lean)、[`WindowCFBridge.lean`](epi_formal/EpiFormal/WindowCFBridge.lean) |
| 论文一：仿射窗口显式周期 $2B|C|$、黄金比轨道有限谱与 $B=1\text{--}6$ / 四类多尺度有理端点刚性；全部 8 个原独立 Lean 辅助模块（共 29 条声明）并入主工程与统一审计 | 无条件模型/归约结果 + 已有辅理统一机器复核 | **已核实**（72 页重编 0 错误/0 警告；原独立 8 模块——`GoldenHeadCutoff`, `GoldenAffineEndpoint`, `AffineWindowAudit`, `DigitTailBound`, `DensityCube`, `OrbitAndFlow`, `ResearchAdvance`, `TraceMarkov`——全部并入 `EpiFormal.lean` 与 `Audit.lean`，共 29 条声明仅用基础公理） | 用 Bugeaud 二次 Mobius 恒等式研究 $A/B-e$ 与 $(A+Ce)/B$ 模型；模型与窗口研究**不解决 $e+\pi$ 无理性** | [`paper1_e_plus_pi.pdf`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf)、[`GoldenHeadCutoff.lean`](epi_formal/EpiFormal/GoldenHeadCutoff.lean)、[`GeneralEndpointRigidity.lean`](epi_formal/EpiFormal/GeneralEndpointRigidity.lean)、[`EpiFormal.lean`](epi_formal/EpiFormal.lean) |
| 论文一：$e+\pi$ 无理性归约、Flint Hills 条件桥接、Alekseyev 方向（$\text{收敛}\Rightarrow\mu(\pi)\le 5/2$）、逃逸约化（P1）与四路障碍分析 | 等价改写/换靶 + 条件结果 + 障碍分析 + Lean 4 机器验证 | **已核实**（23 条经典定理推导显式依赖 3 条经典白名单公理；Meiburg Flint Hills 情况与 Alekseyev 方向已机器形式化，无项目自加公理） | 仅做条件桥接、等价换靶（如 P1 晶格逃逸）或排除特定构造；明确不宣称解决原问题或“更接近证明” | [`FlintHills.lean`](epi_formal/EpiFormal/FlintHills.lean)、[`MeiburgConvergence.lean`](epi_formal/EpiFormal/MeiburgConvergence.lean)、[`Alekseyev.lean`](epi_formal/EpiFormal/Alekseyev.lean)、[`Escape.lean`](epi_formal/EpiFormal/Escape.lean) |
| 符号、区间与转移算子整数证书（`verify_round3.py`、`verify_round4.py`、`residue_certificate.py` 等） | 有限计算或有限排除（非 Lean 内核证明） | **已核实**（SymPy 1.14.0 `12/12` PASS；余弦积分 $\pi e^{-1}/2$ 与 80 位振荡积分误差 `0.0`；450 位 `mpmath.iv` 宽度 $\le 2.12421\times 10^{-460} < 9.13\times 10^{-451}$；$1\le q\le 1000$ 无整数、$1\le n\le 60$ 仅 $[1,3,5,6,34]$ 通过且 $q=34\to n=35$；精确有理转移算子认证 $357/512 < \dim_{\mathrm{H}} F < 359/512$） | 对有限分母、有限窗口与有限尺度维数界作机器高精度/精确有理计算验证，不构成一般性无理性证明 | [`verify_round3.py`](verification/verify_round3.py)、[`verify_round4.py`](verification/verify_round4.py)、[`certificate_round4.json`](verification/certificate_round4.json)、[`residue_certificate.py`](verification/residue_certificate.py) |
| CMMS 一次文献核查与论文二全篇纠偏 | 文献核查与复现 | **已核实**（下载并逐页核对 *Pacific J. Math.* 217(1) (2004), pp. 45–59 官方刊出全文，确认 §5 主定理为 **Theorem 3** 而非误写的 Theorem 5；论文二三处引文已全部更正重编） | Cabrelli–Mendivil–Molter–Shonkwiler, *Pacific J. Math.* 217(1) (2004), 45–59, `doi:10.2140/pjm.2004.217.45`（pp. 57–58, §5 Theorem 3） | [`cmms_citation_check_20261122.md`](verification/cmms_citation_check_20261122.md)、[`CMMS_PJM_2004_217_45.pdf`](verification/reference_pdfs/CMMS_PJM_2004_217_45.pdf) |

---

## 二、三层公理依赖实测清单（`verification/audit_final_20261122.log`）

经 [`epi_formal/`](epi_formal/)（Lean `v4.35.0` + Mathlib `v4.35.0`）执行 `lake build EpiFormal`（**9172 jobs**，EXIT 0）与 `lake env lean Audit.lean`（EXIT 0），并由 [`verification/check_audit_reconcile.py`](verification/check_audit_reconcile.py) 自动对账核实：

- **审计声明总计**：**828 条**（`Audit.lean` 与原始日志 **828/828** 严格双射，重复 0）
- **`sorryAx` 计数**：**0**
- **逃逸关键字全库扫描**（扫描全部 127 个 `.lean` 文件中的 `sorry` / `admit` / `native_decide` / `implemented_by` / `extern` / `unsafe` / `partial` / `opaque`）：**0 命中**
- **第 1 层（仅 Lean 基础公理：`propext`, `Classical.choice`, `Quot.sound`）**：**805 条**
  - 含 5 条零公理（空公理列表 `[]`）声明；
  - 论文二全部形式化模块、新建 [`WindowBoundedUpper.lean`](epi_formal/EpiFormal/WindowBoundedUpper.lean)（21 条声明）以及新并入的 8 个论文一辅助模块（29 条声明）全部落在此层。
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
- **论文二（48 页，0 错误 / 0 警告 / 0 Overfull `\hbox`）**：
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
- 全量 125 个子模块源码：[`epi_formal/EpiFormal/`](epi_formal/EpiFormal/)（含 2026-11-22 新增的 [`WindowBoundedUpper.lean`](epi_formal/EpiFormal/WindowBoundedUpper.lean) 与并入的 8 个论文一模块）
- 历史阶段性基线文档：[`epi_formal/README.md`](epi_formal/README.md)、[`LEMMA_AUDIT.md`](epi_formal/LEMMA_AUDIT.md)、[`PROOF_GAPS.md`](epi_formal/PROOF_GAPS.md)、[`FINAL_REVIEW.md`](epi_formal/FINAL_REVIEW.md)（标注了 2026-11-14 初版 31 条基线快照；最新 828 条权威数据以本说明和 `Audit.lean` 为准）

### 3. 核验脚本、审计日志、数学记录与一次文献（[`verification/`](verification/)）
- **核心审计与对账**：[`audit_final_20261122.log`](verification/audit_final_20261122.log)、[`check_audit_reconcile.py`](verification/check_audit_reconcile.py)
- **符号 / 区间 / 转移算子 / 论文完整性验证**：
  - [`verify_round3.py`](verification/verify_round3.py) / [`.log`](verification/verify_round3.log)（12/12 SymPy 1.14.0 符号验证）
  - [`verify_round4.py`](verification/verify_round4.py) / [`.log`](verification/verify_round4.log) / [`certificate_round4.json`](verification/certificate_round4.json)（余弦积分 + 450 位 `mpmath.iv` 区间证书）
  - [`residue_certificate.py`](verification/residue_certificate.py) / [`residue-certificate.log`](verification/residue-certificate.log)（论文二 `thm:residues` 精确有理转移算子认证）
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
# 1. 核对 Lean 公理审计 828/828 双射、0 sorryAx、23 白名单、0 项目自加公理、0 逃逸关键字
python verification\check_audit_reconcile.py verification\audit_final_20261122.log

# 2. 复跑核心符号、450 位区间、整数转移算子及论文二完整性检查
python verification\verify_round3.py
python verification\verify_round4.py
python verification\residue_certificate.py
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

# 论文二（洁净目录两遍即可 0 警告稳定全部引用）
cd ..\..\paper2_spectral_gap_dimension
pdflatex -interaction=nonstopmode paper2_spectral_gap_dimension.tex
pdflatex -interaction=nonstopmode paper2_spectral_gap_dimension.tex
```

---

## 五、它没做到什么（诚实边界与留存待办）

1. **核心数学问题未解决**：本仓库中的所有工作**没有证明** $e+\pi$（以及单个 $e\pi, e-\pi, \pi/e, \pi^e$）的无理性或超越性；逃逸约化（P1）属于同难度族等价换靶，障碍分析不构成一般方法的不可能性证明。
2. **论文二仍为纸面证明的四个局部**：
   - `thm:no-short-dim` 的 Lebesgue 零测度推论（依赖 `thm:short-ae`）；
   - `thm:short-ae` 的塔–Markov–Borel–Cantelli 测度论实例化（Lean 仅验证条件组装 [`WindowShortAe.lean`](epi_formal/EpiFormal/WindowShortAe.lean) 与核心引理 [`WindowAndResidueCore.lean`](epi_formal/EpiFormal/WindowAndResidueCore.lean)）；
   - `thm:finite-state-tail` 的正测度下界（Lean 已验证骨架与带标记分支引理）；
   - `thm:residues` 的 Bowen/压力 Hausdorff 维数组装（区间 $(357/512, 359/512)$ 由精确有理脚本 [`residue_certificate.py`](verification/residue_certificate.py) 认证，非 Lean 内核证明）。
3. **重耗时高精度脚本与联网洁净重构边界**：
   - 本轮批量 45 秒超时复验中，4 个 2500 位高精度长耗时脚本（[`verify_golden_b3_b4_exact.py`](verification/verify_golden_b3_b4_exact.py)、[`verify_golden_b5_b6_multiscale.py`](verification/verify_golden_b5_b6_multiscale.py)、[`verify_golden_general_b.py`](verification/verify_golden_general_b.py)、[`verify_weighted_lower.py`](verification/verify_weighted_lower.py)）未等待其全程结束，仓内保留源码与历史 `.log` 供按需完整重跑；
   - 未在完全无缓存的联网环境中重新执行 `lake exe cache get && lake build EpiFormal`（已在本地完成 `9172 jobs` 全量构建、828/828 审计对账及全源码归档完整性校验）。
4. **投稿前人工完善项**：
   - [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex) 仍保留作者/单位占位符（`[Author name]`, `[Affiliation]`）与 3 处 `% TODO before submission:` 注释待正式投稿前由作者补充；
   - [`epi_formal/README.md`](epi_formal/README.md)、[`LEMMA_AUDIT.md`](epi_formal/LEMMA_AUDIT.md)、[`PROOF_GAPS.md`](epi_formal/PROOF_GAPS.md)、[`FINAL_REVIEW.md`](epi_formal/FINAL_REVIEW.md) 保留了 2026-11-14 初版 31 条基线记录作为历史档案，当前最新全量审计口径以本 `README.md`、[`Audit.lean`](epi_formal/Audit.lean) 及 [`verification/audit_final_20261122.log`](verification/audit_final_20261122.log) 为准。
