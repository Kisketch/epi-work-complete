# epi_work 发展规划（2026-11-24）

> 编制：AutoClaw（数学研究助理）。遵循 [`AGENTS.md`](AGENTS.md) 诚实分类法与引用纪律；本文件为新增规划文件（只增不减，不改动任何既有文件）。
> 基线：本地已按「以 GitHub 为准」快进同步至 `f345d60`（2026-11-24，合并 5 个提交，26 文件 +2464/−15）；`epi_formal/.lake`（Mathlib 缓存）在位；数值环境 venv 就绪。
> 边界声明：$e+\pi$（及 $e\pi, e-\pi, \pi/e, \pi^e$ 单个）的无理性仍是公开问题，本规划不含任何「证明 $e+\pi$ 无理性」的承诺；文中所有「已核实」均为仓库文档口径（作者自报 + 2026-11-23 / 2026-11-24 两次 Colab 独立复现），助理未复跑（PI 于 2026-11-24 明示无需复跑）。

---

## 0. 一句总判断

形式化侧与论文工程已达到「可投稿、可展示」的完备度（988 条 Layer A 审计声明、0 `sorryAx`、仅 3 条经典白名单公理、两次独立机器复现），且原 F1/F2 缺口已闭合；剩余工作重心应从「证明搬运」转向：**投稿收尾 → 论文二体系的数学延展（临界速率 / 超临界前因子 / 第四项猜想）→ 仅存的三个条件靶点的文献跟踪**，不再在已探明障碍的经典路线上重复投入。

---

## 1. 环境配置现状（2026-11-24 实测）

| 工具 | 版本 | 用途 | 状态 |
| :--- | :--- | :--- | :--- |
| `.venv\Scripts\python.exe` | Python 3.12.14 + mpmath 1.3.0 + sympy 1.14.0 | 全部数值/符号验证脚本 | ✅ 满足 README §4.1 要求（sympy ≥ 1.14、mpmath ≥ 1.3）；**数值工作一律用它** |
| 系统 `python` | 3.13.15（无 mpmath） | — | ⚠️ 勿用于 verify 脚本 |
| elan / lean / lake | elan 4.2.4；已装 leanprover/lean4 v4.35.0 与 v4.36.0 | Lean 形式化 | ✅ [`epi_formal/lean-toolchain`](epi_formal/lean-toolchain) 锁 `v4.35.0`，进入目录自动解析正确工具链；本机 `.lake/` 缓存（约 8.49 GB）在位，无需重新下载 Mathlib |
| pdflatex | MiKTeX-pdfTeX 4.27（MiKTeX 26.5） | 论文重编译 | ✅ 按 README §4.3 洁净目录三遍编译 |
| git | 2.55.0.windows.3 | 版本守恒 | ✅ 与 `origin/main` 同步于 `f345d60`；`.venv/`、`.lake/` 等已被 `.gitignore` 排除 |

**今日新增计算留痕（类别 4：有限计算）**：用 venv mpmath（dps=60，另以 dps=120 复核一致）实算 $e+\pi$ = `5.85987448204883847382293085463216538195441649307507`（50 位）、$e\pi$ = `8.53973422267356706546355086954657449503488853576511`（50 位）、连分数前 25 个部分商 `5,1,6,7,3,21,2,1,2,2,1,1,2,3,3,2,5,2,1,1,1,1,3,1,8`、分母 $\le 10^6$ 收敛项 13 个。脚本与输出在 `%TEMP%\epi_envcheck\`（不在仓库内）。此仅为环境自检，不构成任何数学进展。

---

## 2. 成果对照表（README 权威口径 + 助理核查状态）

助理核查状态统一为：**仓库文档与审计日志已实际读取；未复跑任何验证（PI 指示）**。类别按 AGENTS.md 五分法，沿用 README 自评。

| 结果 | 类别 | 与已有文献关系（README 口径） | 依据 |
| :--- | :--- | :--- | :--- |
| 论文二主体：全谱离散化 $\frac14\mathbb{Z}_{\ge0}\cup\{\infty\}$、正能级三分法、临界/二值精确 Hausdorff 规范、一般 $(cj^r+d)$ 递推与次临界相变 $1-\alpha/r$、`thm:finite-state-tail` | 无条件新结果 + Lean 4 Layer A 验证 | Kraaikamp–Liardet 零能级准则（[BDS] Lemma 4.1）之上的独立推进 | [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex)、`GaugeCircle/TrichotomyAndPolyExtension/FiniteStateComplete.lean` |
| 论文二拓展一：任意增长商三项递推的普适离散谱、$\gamma_{\sup}$ 维数畸变与超临界二次坍缩（`thm:growing-rec-*`） | 无条件新结果 + Lean 验证 | 完全去除 $A_j$ 多项式形式假设；$\gamma_{\sup}>0$ 时新相变 | paper2 §6.4、`GeneralGrowingRec/GeneralGrowingDim.lean` |
| 论文二拓展二：残差维数二阶渐近与倒数 Fibonacci 常数 $\psi_{\mathrm{Fib}}$（`thm:residues-asymptotic`） | 无条件新结果 + Lean 验证 | arXiv 与连分数维数文献**负搜索**未见先例（负搜索 ≠ 不存在） | paper2 §7.4、`ResidueAsymptotic.lean` |
| 论文二拓展三：多残差相变、无 Bowen 庞加莱横坐标、$\gamma$ 三阶渐近、超临界 $\Theta(m^{-2s_0})$ 速率（`thm:multi-residue-asymptotic`） | 无条件新结果 + Lean 验证 | 负搜索未见先例；Colab 全新克隆复建逐条一致 | paper2 §7.5、`ResidueMultiAsymptotic.lean`、[`colab_rebuild_audit_20261124.md`](verification/colab_rebuild_audit_20261124.md) |
| 论文二 `rem:fourth-term`（2026-11-24）：第四项猜想 $+\frac34\Gamma^3(\log m)^2/m^3$ | **条件结果（启发式猜想）+ 有限计算** | 数值已双配置法复现；**猜想未证明**；未做文献检索 | [`fourth_term_fit_20261124.py`](verification/fourth_term_fit_20261124.py) 等 |
| 论文一：仿射窗口显式周期 $2B|C|$、黄金比轨道有限谱、$B=1$–$6$/四类多尺度端点刚性 | 无条件模型/归约结果 + 已有辅理统一机器复核 | Bugeaud 二次 Möbius 恒等式路径；**不解决 $e+\pi$ 无理性** | [`paper1_e_plus_pi.pdf`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf)、`GoldenHeadCutoff` 等 |
| 论文一 `prop:denominator-bounds`（2026-11-24）：若 $x\in\{e+\pi,e\pi,\pi-e,\pi/e\}$ 有理则 $q\ge 10^{500018}$；OEIS A058651 全部 20000 部分商严格复核 | **有限计算或有限排除** | 负搜索未见同形发表界；Bailey 1988 仅核摘要；**不涉及无理性，更大分母未排除** | [`rational_exclusion_bound_20261124.py`](verification/rational_exclusion_bound_20261124.py)、[`exclusion_runs_20261124/`](verification/exclusion_runs_20261124/) |
| 论文一归约/障碍体系（定理 A/B/C/E、H′、四路线障碍） | 等价改写/换靶 + 条件结果 + 障碍分析 | 条件桥接与换靶；**不宣称更接近证明** | `FlintHills/MeiburgConvergence/Alekseyev/Escape.lean` |
| 数值脚本族（verify_round3/4、$N{=}512$ 精确整数证书、32 位 Chebyshev 配置法等） | 有限计算或有限排除 | 数值佐证，不作严格证明引用 | [`verification/`](verification/README.md) |
| CMMS 一次文献核查 | 文献核查与复现 | 官方刊出全文逐页核对（§5 主定理为 Theorem 3），三处引文已更正 | [`cmms_citation_check_20261122.md`](verification/cmms_citation_check_20261122.md) |

**形式化侧现状更正（相对 [`progress_and_path_analysis.md`](progress_and_path_analysis.md) 2026-11-13 的更新）**：
- **F1（T3 Alekseyev 方向）已闭合**：原 `alekseyev_diophantine / alekseyev_bound` 的 sorry 陈述已弃用（方向错误），改由 `sin_eventual_lower`、`abs_sub_mul_pi_factor` 等真证引理承接（[`FlintHills.lean`](epi_formal/EpiFormal/FlintHills.lean) 头注）。
- **F2（Meiburg 公理 → 定理）已完成**：`meiburg_criterion` 现为定理（FlintHills.lean:49；`Audit.lean:135` 注记「已由 F2 证明为定理（不再是公理）；全项目零 sorry」）。命题 H′ 的公理依赖随之降为 1 条（`mu_e_eq_two`）。
- 源码 `axiom` 声明仅剩 3 条经典白名单：`e_transcendental`、`pi_transcendental`（`Axioms.lean`）、`mu_e_eq_two`（`Measure.lean`）；本次 rg 复核确认 16 个文件中出现的 "sorry" 字样全部位于注释，与 README「0 逃逸关键字」口径一致。
- 唯一剩余的经典形式化项为 **F3**（见 §5.2）；`progress_and_path_analysis.md` 的 F1/F2 建议已过时，以本文件与 README 为准。

---

## 3. 发展规划

### 3.1 近期（0–2 周：工程与投稿收尾，零数学风险）

1. **论文二投稿收尾**：清除 [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex) 的 `[Author name]` / `[Affiliation]` 占位符与 `% TODO before submission:` 清单；论文一 [`03_submission_prep/`](paper1_e_plus_pi/03_submission_prep/)（cover letter、AI 贡献草稿、核对清单）定稿；目标期刊由 PI 圈定（数论 / 动力系统 / 分形几何方向）。
2. **提交前一键体检入常轨**：`.\.venv\Scripts\python.exe verification\verify_repo_integrity.py`；注意它会刷新被跟踪的 `verify_repo_integrity.log`，应随提交一并入库（符合本项目「日志留痕入库」文化）。
3. **e+π 计算留痕入档（可选）**：把 `%TEMP%\epi_envcheck\` 的 sanity 脚本与输出复制进 `verification/`，并在 [`全工作区总索引与留痕台账.md`](verification/全工作区总索引与留痕台账.md) 补一行（类别 4）。
4. **防误读头注（可选）**：为 [`epi_formal/README.md`](epi_formal/README.md)、`LEMMA_AUDIT.md`、`PROOF_GAPS.md`、`FINAL_REVIEW.md` 四份 2026-11-14 历史治理文档加「历史档案」头注（README §五.4 已声明以新口径为准，补头注可彻底防误读）。

### 3.2 中期 A（形式化收尾：唯一剩余经典项）

- **F3：`mu_e_eq_two` 公理 → 定理**（Bundschuh 经典结果 $\mu(e)=2$，需连分数 machinery）。完成后白名单降至 2 条（仅 $e$、$\pi$ 超越性），命题 H′ 与定理 A 全部只依赖经典超越公理。这是形式化侧最后一件「把已确立数学搬进 Lean」的事。
- **F4（长期、低优先）**：$e/\pi$ 超越性的 Lindemann–Weierstrass 完整形式化——Mathlib 尚无，投入产出比低，维持 repo 原判断暂缓。

### 3.3 中期 B（论文二数学延展：README 明示的未解决边界，均为无条件方向）

1. 临界线 $s_0(S)=1/2$ 处的收敛速率（`thm:multi-residue-asymptotic` 遗留）。
2. 超临界阶段的精确主导前因子常数（当前只有 $K_1 m^{-2s_0}$ 双侧幂律）。
3. `rem:fourth-term` 第四项猜想 $+\frac34\Gamma^3(\log m)^2/m^3$ 的证明或否证（当前为启发式 + 双配置法数值佐证，未证明）。
4. $F_{m,r}$ **开区间**严格性摆脱 Bowen 压力公式依赖（闭区间已 Lean 化；开区间仍引用 Bowen）。
5. `thm:finite-state-tail` 的有限维 Perron–Frobenius 右特征向量显式化（当前显式传入）。

### 3.4 中期 C（论文一有限排除的稳妥外推——类别 4，明示不逼近证明）

- 分母下界外推（$D=10^7$ 或按算力定）；OEIS A058651 部分商核对窗口扩展；多残差 Chebyshev 数值佐证扩展。
- **红线**：此类结果只排除有限范围，不得表述为「更接近证明」；论文中沿用「界只反映计算长度」的措辞（f345d60 已加）。

### 3.5 长期（原问题条件靶点跟踪，不承诺）

- 仅存三个条件靶点：① $\mu(\pi)>2 \Rightarrow$ 四数无理；② Flint Hills 发散 $\Rightarrow$ 四数无理（现两端均已机器化：`meiburg_criterion` 为定理、「发散 ⇒ $\mu(\pi)\ge 5/2$」亦已证）；③ $\pi\in S$ + Bertolin $\Rightarrow$ $e+\pi$ 超越。另有「全新精确加法恒等式」靶（当前无候选）。
- **行动 = 文献监控**：arXiv 关键词（Flint Hills series、irrationality exponent of π、e+π irrational、Bertolin motivic / $\wp$ values）。出现新文献时机再评估；不在已断裂路线（级数 / Niven 积分 / 超越框架 / 丢番图三角界）重复投入。
- （可选，需 PI 同意后建立）每周 arXiv 关键词巡检的定时任务。

---

## 4. 本规划的诚实边界

1. 未复跑任何 Lean 构建或数值验证（PI 指示）；所有验证状态引自仓库文档及其记录的两次 Colab 独立复现。
2. §3.2、§3.3、§3.4 全部不改变「$e+\pi$ 无理性开放」这一基线；§3.4 属类别 4（有限计算/有限排除）。
3. 本文件由助理依据实际读取的仓库文档编制；书目与计数信息未凭记忆补全，未核到的字段均未写入。
