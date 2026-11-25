---
name: epi-research-commander
description: Master research commander skill and comprehensive operational guide for the e+pi irrationality, continued-fraction spectral/dimension theory (Paper 1 & Paper 2 series), Lean 4 Layer A formalization, and parallel hydrogen subagent orchestration. Trigger whenever planning, executing, reviewing, dispatching parallel research streams, spinning off standalone theorems into the Paper 2 series, or onboarding onto this repository.
---

# EPI Research Commander — 总研究指南与并行指挥手册 (`epi-research-commander`)

> **定位声明**：本技能是 `epi_work` 仓库的总研究指南与并行研究指挥手册，双根镜像维护于 `.agents/skills/epi-research-commander/SKILL.md` 与 `.claude/skills/epi-research-commander/SKILL.md`，并在两篇主论文目录的独立日志文件夹 `paper1_e_plus_pi/07_research_log_and_guide/MASTER_GUIDE_SKILL.md` 与 `paper2_spectral_gap_dimension/00_research_log_and_guide/MASTER_GUIDE_SKILL.md` 中保留同内容副本，以便同行学者与后续代理快速复用全部研究方法、工具链、检验门禁与交接规范。

---

## 1. 不可逾越的学术红线与诚实基线（`AGENTS.md` + `.agents/rules/next-step-workflow.md`）

任何研究、写作、审稿、形式化、数值计算或 `hydrogen` 子代理任务均须严格遵守以下六条铁律：

1. **公开问题基线（`AGENTS.md` §4）**：
   - 截至目前，**$e+\pi$ 的无理性仍是公开问题**，未被证明无理、有理或超越；$e\pi$、$e-\pi$、$\pi/e$、$\pi^e$ 单个亦然。
   - 当前唯一无条件硬结论是：**$e+\pi$ 与 $e\pi$ 至少其一超越**（Vieta 恒等式 + Hermite/Lindemann）。
   - Carella、Sarich、Foukzon 等人声称的“$e+\pi$ 已证”不被数学界接受，**禁止引为证明**；`openai/math` 家族 017（`PiExponent`）未经独立同行评审，且须区分含 `sorry` 的挑战题面 `ComparatorChallenges/PiExponent.lean` 与主证明文件 `OAI/NumberTheory/PiExponent/Main.lean`。
2. **五分法诚实分类（`AGENTS.md` §2）**：评估任何数学结果时必须且仅能标注以下五类之一：
   - **1. 无条件新结果**：不依赖未证猜想或外加公理，且确实在现有文献之外推进明确数学结论（若是已知一般方法的显式实例，须标明“窄 / 已知方法的显式实例”）。
   - **2. 条件结果**：显式依赖未证猜想、未独立核验预印本或外加公理。
   - **3. 等价改写或换靶**：与原问题难度等价，**禁止说成“更接近证明”**。
   - **4. 有限计算或有限排除**：数值验证、有限分母/尺度排除、Chebyshev 配点佐证等，**严禁冒充一般性证明**。
   - **5. 文献核查与复现**：核查他人结果、经典结论的新证明或既有证明的形式化复现。
3. **引用与双通道防伪纪律（`AGENTS.md` §3 + `next-step-workflow.md` §1）**：
   - 书目字段（作者、期刊、卷、页、年份、DOI、定理编号、常数）**只能来自实际打开核对的一手页面或全文**；未核到一律写「**未核到**」。
   - 严格区分「**负搜索未找到先例**」（必须交代检索式、渠道与未覆盖库如 MathSciNet/zbMATH）与「已证明不存在先例」。
   - 前沿/承重文献必须执行**双通道检索**（`free-search-mcp` + `literature-search-arxiv` / `literature-search-openalex` / Crossref / DataCite）及**四重勘误与撤稿核查**（Crossref `update-to`/`updated-by` + DataCite、OpenAlex `is_retracted`、arXiv `/abs/` 评论与 `WITHDRAWN` 字段、经典刊物专项 Erratum 检索）。
   - LaTeX `\bibitem` 中**禁止对 DOI 使用 `\allowbreak`**，改用 `{\sloppy ...}` 与 `\emergencystretch` 处理折行，以免破坏 `verify_refs.py` 与超链接提取。
4. **Lean 4 形式化口径（`AGENTS.md` §5 + `next-step-workflow.md` §4）**：
   - 任何未经本机或独立环境实际跑过 `lake build` 与 `#print axioms` 的形式化结果一律标为「**作者自报，未复跑**」。
   - 核实后必须按三层披露公理依赖：**Layer 1（Lean 基础三公理 `propext`, `Classical.choice`, `Quot.sound`） / Layer 2（经典白名单公理，本库仅 `e_transcendental`, `pi_transcendental`, `mu_e_eq_two` 三条） / Layer 3（项目自加公理，目标恒为 0）**，同时扫描全库 `sorry`/`admit`/`native_decide`/`implemented_by`/`extern`/`unsafe`/`partial`/`opaque`（须 0 命中）。
5. **计算纪律（`AGENTS.md` §6）**：
   - **严禁心算给数**。一切常数、界、计数与展开系数须用 Python（`mpmath` / `sympy` / `python-flint` Arb）实际计算，脚本与输出 `.log`/`.json` 留在 `verification/` 可复查。
   - 严格区分 **Arb/精确整数认证界**（可作有限排除证明）与 **Chebyshev 配点/启发式拟合**（正文与图注必须显式标注 *non-rigorous numerical corroboration / not proved*）。
6. **学术正文与研究过程日志物理分离**：
   - 论文正文目录（`paper1_e_plus_pi/01_main_paper/`、`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`、`paper2_spectral_gap_dimension/split/`）与权威形式化工程（`epi_formal/`）保持纯净学术呈报，**不混入过程流水账**。
   - 详尽思路历程、试错记录、失败障碍坐标、总清单台账与本总指南独立存放在：
     - `paper1_e_plus_pi/07_research_log_and_guide/`
     - `paper2_spectral_gap_dimension/00_research_log_and_guide/`

---

## 2. 先前研究全景总结（截至 2026-11-25）

### 2.1 Paper 1 主线：$e+\pi$ 无理性归约、仿射窗口、二次轨道谱与障碍分析
- **文件位置**：`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex` / `.pdf`（75 页，0 错误 / 0 Overfull）。
- **精确章节结构**：
  - `§1` Introduction (L71)、`§2` Preliminaries & unconditional baseline (L127)
  - `§3` Window periods and converse to denominator locking (L270)：仿射窗口显式周期 $2B|C|$、5-窗锐性、任意分母逐素数约分公式 $G_j=g\gcd(A(Q_j/g)-(B/g)P_j,g)$
  - `§4` Bounded golden-orbit limit spectrum (L941)：黄金比轨道有限谱、共轭正性 `prop:conjugate-positivity`、$B=1\text{--}6$ 全互素类精确最小值与第二极限点、4 类多尺度仿射轨道
  - `§5` General quadratic orbits, ideal classes, and uniform interval counting (L2064–3284)
  - `§6` Reductions, obstructions, and conditional frameworks (L3285–3855)：度量归约（定理 A）、连分数转换器必要条件（定理 B）、级数刚性（命题 C）、四指数阻断（命题 D）、$\mu_0=1+1/(M-1)$（定理 E）、$\wp$ 缩放闭包（命题 G）、Flint Hills 桥接（命题 H'，经 Meiburg 2022 机器验证 + Alekseyev 方向）、晶格逃逸约化（P1）、四路经典障碍分析与 2026 前沿定位（Bai, Dan, Yu, CDT, Chudnovsky, Fauzan, Zapata）
  - `§7` Conclusion & open problems (L3856–3905)、`Use of AI` (L3906)、`App. A` Numerics & Arb exclusion $q\ge 10^{500018}$ (L4021)、`App. B` Lean (L4152)、`App. C` Audit trail (L4667)、`App. D` Reproducibility (L4701)。
- **诚实评估**：对 $e+\pi$ 开放问题本身**无突破**；四条经典路线（级数/整数序列、Niven 积分、超越数论、丢番图逼近）及桥梁恒等式、Chowla–Selberg、Mahler 分类均探明共同结构障碍——$e$ 与 $\pi$ 缺乏已知加法算术联系。数学价值定位为归档、模型副产物（C−）与条件链形式化基准。

### 2.2 Paper 2 主线：谱离散化、精确 Hausdorff 规范、一般递推与多残差连分数维数
- **文件位置**：`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`（66 页，293,395 字节，4,568 行，28/28 文献全引用），由 `split/src_sections/` 下 11 个标准切片（`slice_index.csv`）逐字节拼接生成。
- **四轨拆分与核心定理**：
  - **2A（核心规范与三分法，`split/2A_core_gauge_trichotomy/`，`*-2Apub` 21 页）**：$e$ 选定收敛分母 $Q_{j+1}=(4j+2)Q_j+Q_{j-1}$ 上全谱 $\Lambda(\R)=\frac14\Z_{\ge0}\cup\{\infty\}$、零能级 $L=\Z+\Z\frac{e+1}{2}$、有限水平维数 0、次临界精确维数 $1-\alpha$、正能级 $k/4$ 精确规范 $h_k(1/Q_n)=(2k+1)^{-n}$ 与三分法（含二值通用基 2 与有符号 $L$-陪集坍缩，覆盖 $\R$ 与 $\R/\Z$）。注：主稿尚存 6 处 `Phase1`（未公开归档）引用（L266, L455, L505, L518, L4390, L4566），投稿前须替换为公开伴随引用。
  - **2B（一般递推理论，`split/2B_general_theory/`，16 页）**：多项式递推 $Q_{j+1}=(cj^r+d)Q_j+Q_{j-1}$ 全谱 $\frac1c\Z_{\ge0}\cup\{\infty\}$ 与 $1-\alpha/r$ 维数相变；任意增长商递推 $Q_{j+1}=A_jQ_j+Q_{j-1}$ ($A_j\to\infty$) 普适离散谱、KL 恒等、亚临界维数畸变 $\frac{1-\tau}{1+\tau\gamma_{\sup}}$ 及超临界 $\tau_{\mathrm{crit}}=1+1/\gamma_{\sup}$ 处从秩-2 格到秩-1 子格 $\frac1g\Z$ 的二次相变。推荐与 **2A 合并为单一主稿**（30–35 页，一般增长商为主定理，$e$ 作为旗舰推论）。
  - **2C（窗口、有限状态、单/多残差连分数与证书，`split/2C_windows_residues_finstate/`，26 页）**：`thm:finite-state-tail` 带标记分量 Perron 规范；Hermite 窗口维数与显式常数 $(1-e^{-1})/160$ 几乎处处短窗率；模 $m$ 最终周期 24-Lipschitz 夹逼与无 Bowen 转移算子框架；$N=512$ 精确整数证书表（20 闭界 + 5 严格分离）；金属连分数预解恒等式与全模 $m\ge2$ 全局严格分离 $\dimH F_{m,m}<\dimH F_{m,1}=\dimH E_m$、倒数 Fibonacci 常数 $\psi_{\mathrm{Fib}}$ 渐近；`thm:multi-residue-asymptotic` 多残差相变 $\max(1/2, s_0(S))$、含 Euler 常数 $\gamma$ 的三阶渐近至 $O((\log m)^2/m^3)$ 及超临界 $\Theta(m^{-2s_0})$ 速率；`rem:fourth-term` 启发式四阶猜想。
  - **S（补充材料，`split/S_supplement/`，8 页）**：数值佐证与 Lean 审计映射。
- **新颖性诚实校准（2026-11-25 核查结论）**：
  - 2B 线性情形与 BLR (2019) 公式重合、方法已知（Fan–Fan–Ye 引理 6.3 同型），贡献在于去除 BLR 条件 (1.6) 并推广至任意增长商的 $\gamma_{\sup}$ 畸变与二次相变；
  - 2C 大 $m$ 渐近落在 DFSU (*Selecta Math.* 2023, Thm 4.1) 扰动框架内（$C_S = 1/\bar c$），`(i)(iii)` 为经典结果（Bowen/MU96, DLMF），`(v)` 上界为 Heinemann–Urbański (2002) 推论；负搜索未见先例之处聚焦于等差族显式常数 $C_r, \psi_{\mathrm{Fib}}, \frac12 d^2 C_S(\gamma C_S-C_S')$ 与全模 $m\ge2$ 严格分离。

### 2.3 Paper 2D 新独立定理论文（2026-11-25）：临界标度修复、超临界精确主导常数与稀疏字母表相变
- **文件位置**：`paper2_spectral_gap_dimension/spinoff_critical_and_supercritical_exact_20261125/paper2D_critical_supercritical_exact.tex` / `.pdf`（隔离于标准 11 切片之外，保留旧实验稿 `drafts_v3_critical_scaling/sec-critical-scaling.tex` 作历史对照）。
- **核心数学推进（完全修复旧稿 7 处缺陷并新证两项无条件定理）**：
  1. **修复 `lem:pole`（彻底消除复全纯盘 $A(\Omega)$ 上的实非负锥谬误）**：在 $\Omega=\{|z-1|<5/4\}$（使 $[0,1]\Subset\Omega$ 且 $\varphi_a(\overline\Omega)\subset\{|z-1|\le1\}\Subset\Omega$）上，结合连分母次/超可乘性给出幂有界性 $\sup_n\|\rho(p)^{-n}L_p^n\|\le(8/3)^p$，以 Cesàro 紧性构造 $[0,1]$ 上严格正特征函数 $h_p\in A(\Omega)$，经马尔可夫极大模 + 全纯唯一性定理证得单纯外围谱 $\{\rho(p)\}$ 与对偶正性，零黑箱完成极点分解 $C_S(p)=\frac{c(p)}{1-\rho(p)}+A(p)$（同步修复 $n=0$ 重复计数、$O((\theta\rho)^n)$ 余项与 $A(p)$ 跨过 $p_0$ 的解析域）。
  2. **修复 `lem:resolvent-uniform` 与 `lem:master`**：显式选取截断项数 $N(m,s)$、以绝对下界 $\varepsilon_-\ge\frac{1}{2em}$ 取代错误假设 $\varepsilon_0\log m\to0$、以初等伸缩界 $C_S(2)\le 2(\max S+1)$（及 $32/(1-s_0)$）修复 $h(1)$ 上界，使统一主方程 $\bigl|d\,C_S(2s^*)m^{-2s^*}\zeta(2s^*)-1\bigr|\le C_1\Sigma/m$ 在**次临界、临界、超临界三区一致成立**（仅需 $m\ge 340\Sigma$）。
  3. **新无条件定理（超临界精确主导常数）**：对一切有限 $S\subset\Z_{\ge1}$ 满足 $s_0(S)>1/2$ 与有限 $B\subset\Z_{\ge0}$，证明
     $$\dimH F_{m,S,B}-s_0(S)=\frac{d\,\kappa(S)\,\zeta(2s_0(S))}{2}\,m^{-2s_0(S)}\bigl(1+O_{S,B}(m^{-1})\bigr),$$
     同时彻底推翻旧启发式常数 $\frac{d\kappa}{2(2s_0-1)}$（旧稿误把固定 $2s_0>1$ 处的 $\zeta(2s_0)$ 截断为 $1/(2s_0-1)$，且误判 `lem:master` 在超临界区失效），并由 `verification/verify_supercritical_exact_constant_20261125.py` 30 位配置法数值佐证（$n=44$ vs $n=48$ 误差 $<10^{-32}$）。
  4. **修复 `thm:critical-scaling` 与加强 `cor:critical-exp`**：对变序列 $(m_k,S_k,B_k)$ 显式列出一致尺度分离 $\Sigma_k/m_k\to0$、$\gamma_k\log m_k\to0$、无量纲归一化 $\gamma_k=\sqrt{d_k\kappa(S_k)/m_k}$ 与极点余项一致占优条件；在固定临界集合 $s_0(S)=1/2$ 下进一步导出二阶对数修正 $-\frac{d\kappa(S)\log m}{4m}+O_{S,B}(m^{-1})$。
  5. **新无条件命题（稀疏字母表反例与尾收敛横坐标相变）**：精确澄清 $A_{k_0}=\{2^{2^k}:k\ge k_0\}$ 满足 $0<\dimH E_{A_{k_0}}\le 2^{-(k_0+1)}<1/2$（注意固定 $k_0$ 时因包含二元集 $\{2^{2^{k_0}},2^{2^{k_0+1}}\}$ 故维数严格正、**并非 0**，从而证伪朴素无限字母表 $\ge1/2$ 猜想，且 $\lim_{k_0\to\infty}\dimH E_{A_{k_0}}=0=\theta(A)$、逃逸集 $\dimH\{x\in E_{A_1}:a_n(x)\to\infty\}=0$），并无 Bowen 地在 6 行内证明一般扰动尾相变 $\lim_{M\to\infty}\dimH E_{S\cup(T\cap[M,\infty))}=\max(\theta(T),s_0(S))$。

### 2.4 Paper 2E 新独立定理论文（2026-11-25）：$e$ 全收敛谱、偶数拟周期递推与无 Brouwer Perron–Frobenius 消去
- **文件位置**：`paper2_spectral_gap_dimension/spinoff_full_convergent_and_even_hurwitz_20261125/paper2E_full_convergent_and_even_hurwitz.tex` / `.pdf`（8 页，0 错误 / 0 Overfull / 0 Undefined，`verify_refs.py` 0 fail）。
- **核心成果**：
  1. **$e$ 全正则收敛序列完整谱论（已入 Lean 4，40 条声明）**：建立 $q_{3j}=(Q_{j+1}+Q_j)/2$、$q_{3j+2}=(Q_{j+2}-Q_{j+1})/2$、重量极限与主公式 $\Lam_{\mathrm{full}}^{\mathrm{KL}}(x)=\max(2\Lam(x),\mathbf{1}_{\mathrm{pf}(x)})$、巨型初始谱隙 $(0,1)$、奇伴随余集 $\frac{e+1}{2}+\Z+\Z e$ 逐出后零水平坍缩回 $\Z+\Z e$、基-$5$/基-$(2k+1)$ 临界规范与 $k\ge 3$ 无符号精确极限空集定理。
  2. **任意 Hurwitz 拟周期 $p\ge1$ 有符号三项递推**：$Q_{j+1}=(\alpha a_j+\beta+\gamma)Q_j+(-1)^{p-1}Q_{j-1}$，修复原 `GeneralGrowingRec` 仅涵奇数周期 $+Q_{j-1}$ 之局限。
  3. **Brouwer-free Collatz–Wielandt 有限维 Perron–Frobenius（已入 Lean 4，13 条声明）**：彻底消除 Paper 2 `thm:finite-state-tail` 外部特征向量输入（R3），并严格界定非线性 BLR (1.6) 在单步有界失真下成立与超缺项 $19.94\times$ 反例边界。

### 2.5 Lean 4 `v4.35.0` 形式化架构与已核实成果（全库 356 个 `.lean` 文件）
- **核心与八路独立 Layer A 审计合计 `1,093` 条声明（`sorryAx = 0`，0 逃逸关键字）**：
  - `Audit.lean`（**937 条** = 914 基础 + 23 经典白名单，维持不可变双射）
  - `AuditResidueCert.lean`（**27 条**，基础三公理，`tab:residues-general` $N=512$ 闭界）
  - `AuditResidueMultiAsymptotic.lean`（**24 条**，基础三公理，`thm:multi-residue-asymptotic`）
  - `AuditResidueCertStrictOpen.lean`（**22 条**，基础三公理，零重算升级全部 20 条严格开界，**彻底消除 R1**）
  - `AuditMuEEqTwo.lean`（**9 条**，基础三公理，无条件证明 Bundschuh $\mu(e)=2$，**完成 L1**）
  - `AuditGeneralAlphabetFloor.lean`（**15 条**，基础三公理，稀疏字母表下界与倍双指数极限，**L4a**）
  - `AuditSupercriticalConstant.lean`（**6 条**，基础三公理，显式极点残差 `hPole` 条件下超临界精确常数归约，**L4a**）
  - `AuditPerronFrobenius.lean`（**13 条**，基础三公理，Collatz–Wielandt 无 Brouwer 证明与无条件 `thm:finite-state-tail`，**彻底消除 R3**）
  - `AuditFullConvergentSpectrum.lean`（**40 条**，基础三公理，$e$ 全收敛子谱理论，**L5**）
- **待续队列（L4b）**：仅余 Paper 2D 全纯盘 `lem:pole` 与 $\kappa(S)$ 一致极点分解尚待入 Lean 内核。

### 2.6 Kahane 问题 Q6（增补纠正与确定性下界突破）与 Paper 1 M1/M2 试错
- **Kahane Q6 重大修正（`research/kahane_q6_addendum_20261125.md`）**：多重点多项式 $P_{n,m}(x)$ 反例**彻底否证**原笔记猜想 D′ 与引理 R（对一切 $2\varepsilon a>1, h\ne0$，含 $2\varepsilon\in\Q$），而最优阶 $m\asymp n^{1/3}$ 包络 $\exp(-cn^{2/3})$ 仍可和，**引理 D 仍开放**；另一方面无条件证明**确定性局部维数定理 K-1 / K-2**（$\underline{\dim}_{\mathrm{loc}}(E(\varepsilon),M)\ge\frac{\log(\lceil 2\varepsilon M\rceil-1)}{\log M}$，$2\varepsilon M>K\ge 3$），已通过真 $x^n$ 映射 `dps=32000, n=45000` 核验。
- **Paper 1 M1/M2（`paper1_e_plus_pi/07_research_log_and_guide/trial_notes_M1_M2_20261125.md`）**：证得混合 $(1,e^z,G(z))$ 阶乘整除爆炸与 CDT 超度量排斥（并标明不阻断变尺度/Borel 绕行）；纠正一般 Möbius 窗口阈值并给出 $T=2|\Delta|$ 与 3 条 $\mathrm{PGL}_2(\Z)$-轨道刻画（记录 Elsner–Havens 2025 付费墙专著未核到）。与 $e+\pi$ 本题皆无突破，原问题仍完全开放。

---

## 3. 本地工具链、脚本与 MCP 能力全清单

| 类别 | 工具 / 命令 | 版本与实测口径 | 用途与注意事项 |
| :--- | :--- | :--- | :--- |
| **Python 主入口** | `py`（Windows Launcher） | Python 3.14.7 | 含 `sympy`, `mpmath`, `numpy`, `scipy`, `python-flint==0.9.0`, `pymupdf`, `pdfplumber`, `requests`, `uv`；**避免裸 `python`**（可能命中 WindowsApps 占位符） |
| **Arb 严格区间** | `py verification/rational_exclusion_bound_20261124.py --selftest` | `python-flint==0.9.0` | 12/12 PASS；用于大整数分母严格排除（Category 4） |
| **Lean 4 / Lake** | `elan`, `lean`, `lake`（工作目录 `epi_formal/`） | `v4.35.0` + Mathlib `v4.35.0` | `lake build` + `lake env lean Audit*.lean`；Windows 并行 `.olean` 锁可用 `epi_formal/serial_build_all.py` |
| **LaTeX 编译** | `pdflatex -interaction=nonstopmode <file>.tex` | MiKTeX 26.5 (`pdfTeX 4.27`) | 须跑 **3 遍**，检查 0 Error、0 `Undefined`、0 `Overfull \hbox` |
| **文献核查脚本** | `py .agents/skills/mathodology-evidence-search/scripts/verify_refs.py <file>` | 离线 40/40 单测 PASS | 自动校验 DOI / arXiv / Retraction；DOI 禁用 `\allowbreak` |
| **全仓体检脚本** | `py verification/verify_repo_integrity.py` | 零丢失 + 审计 + 切片 + 断链 | 每次改核心文档/切片/Lean 后必跑，落盘 `verification/verify_repo_integrity.log` |
| **审计对账/比对** | `py verification/check_audit_reconcile.py` & `compare_audit_logs.py` | 937 / 27 / 24 逐条双射 | 扫描全库 0 逃逸关键字 + CI 三日志比对 |
| **Paper 2 校验** | `py verification/verify_paper2_merge.py` & `paper2_spectral_gap_dimension/split/undef_ref_audit.py` | 11 切片逐字节 + 86 标签 + 46 锚点 | 确保主稿与 `split/src_sections/` 零漂移、2A/2B/2C `undef-refs: 0` |
| **MCP 检索服务** | `free-search-mcp==0.18.2` & `papergraph-mcp==1.2.3` | 仅在用户级 `~/.gemini/config/mcp_config.json` 配置 | 严禁运行 `search-mcp-login antigravity` 或静默装插件 |
| **学术 API 技能** | `literature-search-arxiv`, `literature-search-openalex` | 全局插件（arXiv 限流 3s/次） | 与 `free-search-mcp` 构成强制双通道一手核验 |

---

## 4. 全库双根技能矩阵（`.agents/skills/` 与 `.claude/skills/` 逐字节同步）

| # | 技能名 | 来源 | 触发时机与职责 |
| :-: | :--- | :--- | :--- |
| 1 | `epi-research-commander` | 本项目自研（2026-11-25） | **总研究指南**：全局进展、工具链、SSOT/CI 规范与 `hydrogen` 并行派活模板 |
| 2 | `paper-audit` | 本项目自研 | 数学论文逐项五分法审计、作者声称 vs 实际成立对比 |
| 3 | `lean-audit` | 本项目自研 | `lake build` + `#print axioms` 三层公理审计，区分作者自报与已核实 |
| 4 | `novelty-check` | 本项目自研 | 先行文献与引用核查、严格负搜索口径与【引用错误】标红 |
| 5 | `proof-reasoning` | 本项目自研 | 证明草稿对抗性逐行审查、退化反例构造与可证伪计算 |
| 6 | `lean-proof` | `leanprover/skills @ 7d3da02` (Apache-2.0) | Lean 4 逐步证明、错误优先级、依赖类型重写技巧 |
| 7 | `lean-mwe` | 同上 | 最小复现例构造（定位大证书 elaboration/kernel 超时问题） |
| 8 | `mathlib-build` | 同上 | Mathlib 缓存拉取、`lake` 构建故障排查 |
| 9 | `lean-setup` | 同上 | `elan` 工具链与 Lean 4 项目初始化 |
| 10 | `mathodology-evidence-search` | `sweetcornna/mathodology @ 49c639648c61` (MIT) | 双通道文献检索与 `scripts/verify_refs.py` DOI/arXiv/撤稿校验 |
| 11 | `verified-research` | `sweetcornna/free-search-mcp @ 9a59cfc3df5b` (MIT) | 配合 `free-search-mcp` 核实一手网页、发布日期与时效性 |

> **同步规则**：修改任一自研技能时，必须同步更新 `.agents/skills/<name>/SKILL.md`、`.claude/skills/<name>/SKILL.md` 及 `.claude/skills/README.md`；上游 6 项原样快照不做本地修改。

---

## 5. Paper 2 11-切片真源（SSOT）、分拆定理论文与投稿/CI 规范

### 5.1 Paper 2 单一真源（SSOT）规则
- 严禁只手改 `paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`！
- 凡改动 Paper 2 主体正文，必须用确定性 Python 补丁脚本同步修改 `paper2_spectral_gap_dimension/split/src_sections/` 中对应切片（及 `intro-2A/2B/2C.tex`、`refs.tex`），按 `slice_index.csv` 11 切片拼接重建主稿，随后执行 `verify_paper2_merge.py`、`undef_ref_audit.py`、`verify_repo_integrity.py` 及三遍 `pdflatex`。
- 独立展开的新定理论文（如 `spinoff_critical_and_supercritical_exact_20261125/`）可先以**独立子目录成稿 + 完整编译 + `verify_refs.py` + 高精数值脚本 + 独立 Lean 模块**闭环验收；确认无误后再决定是作为 Paper 2 系列独立分篇投稿，还是经确定性脚本并入标准 11 切片。

### 5.2 投稿前三大人类独占放行门禁（**AI 严禁代填或删除**）
1. 作者姓名与单位占位符（`[Author name]` / `[Affiliation]` / `% TODO before submission`）；
2. 正文 `Use of AI and formal verification` 节按目标期刊政策填写的合规声明；
3. `sec:verification` 末尾人类作者逐行核对证明方法与审阅人声明。

### 5.3 Git、文件卫生与 CI 双门禁
- **只增不减守恒**：绝不删除既有跟踪文件（`verify_repo_integrity.py` 强制核对基线提交 `1e91028` 与 `7ece3b9` 100% 留存）。
- **编码与可移植性红线**：所有新建文本/代码/TeX/Markdown 必须 **UTF-8 无 BOM**；**严禁硬编码个人绝对路径**（一律使用相对路径或 `Path(__file__).resolve()`）；新建 Markdown 须自动校验全部本地相对链接 0 断链。
- **GitHub Actions 双工作流**：
  - `.github/workflows/python-checks.yml`（快速门禁，~5 min）：`verify_repo_integrity.py` + Arb `--selftest` + 50 位证据脚本 + `verify_round3/4.py` + `verify_refs.py` 40 单测。
  - `.github/workflows/lean-audit.yml`（完整形式化门禁，~40 min）：`lake exe cache get` + `lake build` + 三入口 `#print axioms` + `compare_audit_logs.py`（937/27/24 零差异）+ `check_audit_reconcile.py`。

---

## 6. 总指挥并行研究循环与 `hydrogen` 派活提示词模板

### 6.1 并行研究工作流（Plan → Dispatch → Adversarial Audit → Formalize → Spin-off → Log）
1. **文件独占分区**：并行派发多个 `hydrogen` 子代理前，总指挥必须先为每个代理划定**互斥的文件写入边界**（例如：Lean 代理只动 `epi_formal/`；理论/写作代理只动新建 `spinoff_*/` 与 `verification/`；日志与治理代理只动 `07_research_log_and_guide/`、`00_research_log_and_guide/` 与 `.agents/.claude/skills/`），禁止多代理同时改写同一 `.tex` 或 `README.md`，也禁止子代理私自 `git commit`。
2. **有价值即拎出展开**：一旦某路线产出经对抗性审查确认的无条件新结论（即便未能攻克 $e+\pi$），立即为其开辟独立子目录定理论文（Paper 2 系列分篇）、补全推广与反例检验、编写高精度核验脚本、推进 Lean 4 Layer A 形式化，并同步登记至总清单 `MASTER_INVENTORY_LIST.md`。
3. **成败必留痕**：每一轮无论成功、部分推进、失败或阻断，必须写入 `PAPER1_ATTACK_AND_TRIAL_LOG.md` 或 `SPINOFF_AND_TRIAL_LOG.md`，明确记录：**目标、尝试路径、精确数学障碍坐标 / 反例、核查状态、未完成清单、下一轮可证伪切入点**。

---

### 6.2 可复用 `hydrogen` 派活模板（直接填空复用）

#### 模板 A：Paper 1（$e+\pi$ 主攻 / 新障碍或新归约探索）
```text
[Role] 你是 hydrogen 数学研究执行代理。严格遵守仓库根目录 AGENTS.md（五分法、禁心算、禁把换靶说成接近证明）与 .agents/rules/next-step-workflow.md。
[Target] 围绕 Paper 1 最终目标（e+pi 无理性），探索路线：<具体路线名与核心数学猜想/构造>。
[Exclusive File Ownership] 仅可写入：<新建草稿/脚本路径，如 verification/<name>_<date>.py 与 paper1_e_plus_pi/07_research_log_and_guide/trials/<name>.md>；严禁修改 01_main_paper/、epi_formal/、README.md，严禁 git commit。
[Method]
1. 先用 proof-reasoning 技能复述精确量词与假设，对构造执行“替代点压力测试”（代入已知有理和对照点 x = A/B - e，检查该论证是否同样适用；若适用则立即判为无法区分真实 pi 并记录障碍坐标）。
2. 若涉及常数/渐近/整除/窗长，编写 Python (mpmath/sympy/python-flint Arb) 脚本实测并落盘 .log/.json。
3. 若发现无条件新副产物（不依赖未证猜想），评估是否可独立拎出进入 Paper 2 系列。
[Failure Deliverable] 若路线失败或等价换靶，必须交付：(a) 精确失效步骤与数学障碍坐标；(b) 对照点测试反例；(c) 明确标注「难度未降」并建议暂停或转向。
[Acceptance] 输出遵循 AGENTS.md：一句总判断 + 五分法对照表 + 完整推导/反例 + 下一步可证伪检验。
```

#### 模板 B：Paper 2 系列独立定理论文展开与对抗性审稿
```text
[Role] 你是 hydrogen 理论数学与 LaTeX 成稿代理。先调用 proof-reasoning 与 novelty-check 技能，严格遵守 AGENTS.md 与 next-step-workflow.md。
[Target] 将新发现的数学结果 <定理名称> 充分推广、消除所有证明跳步，并撰写为独立定理论文 <spinoff_dir/paper2X_*.tex>。
[Exclusive File Ownership] 仅可写入：<paper2_spectral_gap_dimension/spinoff_<name>/ 与 verification/verify_<name>.py/.log/.json>；严禁触碰 split/src_sections/ 与主稿 paper2_spectral_gap_dimension.tex。
[Method]
1. 逐行对抗审查每一引理：Banach 空间与实/复锥合法性、边界点与紧包含、n=0 项核对、变序列一致假设显式化、边界反例自检。
2. 编写 >=30 位 mpmath 高精度数值脚本（交叉校验配点阶数 n1 vs n2）与 SymPy 符号校验脚本，显式标注 Category 4（非证明佐证）。
3. 参考文献执行双通道核查，DOI 严禁 \allowbreak；正文保留 [Author name] 与 % TODO before submission 人类门禁占位符。
[Verification Gates]
1. py verification/verify_<name>.py 退出码 0 且断言全 PASS；
2. 3 遍 pdflatex -interaction=nonstopmode 编译：0 error、0 Undefined、0 Overfull \hbox；
3. py .agents/skills/mathodology-evidence-search/scripts/verify_refs.py <tex_file> 输出 0 fail。
```

#### 模板 C：Lean 4 Layer A 形式化与三层公理审计
```text
[Role] 你是 hydrogen Lean 4 形式化工程师。先调用 lean-proof 与 lean-audit 技能，严格遵守 AGENTS.md §5（零自加公理、零 sorryAx、零 native_decide）。
[Target] 在 epi_formal/EpiFormal/ 中新增独立模块 <ModuleName>.lean，形式化 <定理列表>，并配套独立审计入口 epi_formal/Audit<Name>.lean。
[Exclusive File Ownership] 仅可写入：epi_formal/EpiFormal/<ModuleName>.lean、epi_formal/Audit<Name>.lean 与 verification/audit_<name>_<date>.log；除非主指挥明确授权，不修改现有 Audit.lean（保持 937 条双射稳定）。
[Method]
1. 尽量复用 TransferOperatorDim / ResidueMultiAsymptotic / ResidueCertGenBase / EulerConvergents 既有定理。
2. 在 epi_formal/ 下实跑：lake build EpiFormal.<ModuleName> 与 lake env lean Audit<Name>.lean。
3. 保存完整 #print axioms 原始输出至 verification/audit_<name>_<date>.log，并逐条核对仅含 [propext, Classical.choice, Quot.sound]（或明确披露是否依赖 3 条既有经典白名单公理之一）；全库扫描逃逸关键字确认 0 命中。
[Failure Deliverable] 若卡在某 Mathlib 缺失引理，用 lean-mwe 给出最小缺口声明，不得悄悄引入新 axiom 或 sorry 蒙混过关。
```

#### 模板 D：双通道先例核查与四重勘误/撤稿审计
```text
[Role] 你是 hydrogen 文献与新颖性审计代理。先调用 novelty-check、mathodology-evidence-search 与 verified-research 技能。
[Target] 对候选定理 <陈述> 开展投稿前先例核查，并对承重引文 <列表> 执行四重勘误/撤稿核查。
[Exclusive File Ownership] 仅可写入：verification/<topic>_novelty_<date>.md（UTF-8 无 BOM，全相对链接）。
[Method]
1. 强制双通道：同时使用 free-search-mcp 与 literature-search-arxiv / literature-search-openalex / Crossref / DataCite，只采信实际打开核对的一手页面字段；未核到一律标「未核到」。
2. 对每条承重文献执行四重检查：Crossref update-to/relation + DataCite、OpenAlex is_retracted、arXiv /abs/ 版本与 WITHDRAWN comment、经典刊物 Erratum/Corrigendum 检索。
3. 明确区分「精确先例 / 特例已知 / 方法已知 / 负搜索未见先例」，并交代检索覆盖与未覆盖库（如 MathSciNet/zbMATH）。
[Verification Gates] 运行 py .agents/skills/mathodology-evidence-search/scripts/verify_refs.py verification/<topic>_novelty_<date>.md 确认 0 fail。
```

#### 模板 E：高精度数值 / Arb 区间认证与可证伪实验
```text
[Role] 你是 hydrogen 数值与认证计算代理。严格遵守 AGENTS.md §6（严禁心算）与 next-step-workflow.md §4。
[Target] 对命题/猜想 <描述> 编写可复现验证脚本 verification/<name>_<date>.py 并输出 .log 与 .json。
[Exclusive File Ownership] 仅可写入：verification/<name>_<date>.{py,log,json}。
[Method]
1. 若为严格有限排除/区间界：使用 python-flint (Arb) 或纯精确整数/Fraction 算术，内嵌 --selftest 单元测试。
2. 若为渐近/谱半径/维数佐证：使用 mpmath >=30 位（工作精度 >=60 位）并做两套阶数（如 n=44 vs n=48）与两种独立算法交叉检验，断言误差阈值。
3. 脚本头注与输出日志必须显式标注 AGENTS.md Category 4 及「non-rigorous numerical corroboration / not proved」（若非严格认证）。
[Verification Gates] py verification/<name>_<date>.py 退出码 0、所有 assert 通过、输出文件 UTF-8 无 BOM、零硬编码绝对路径。
```
