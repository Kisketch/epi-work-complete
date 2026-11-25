# 论文一（$e+\pi$ 无理性主问题）全周期攻关、试错与障碍日志

> **一句话总判断**：经过云端 1–9 轮、本机第 10 轮、A–E 并行五支线、十轮轨道深化及 2026-11-24/25 Arb 排除与六方向前沿核查，**$e+\pi$ 的无理性仍完全开放，未取得任何降低原问题核心难度的突破**；但全过程以可审计方式精确标定了十余条经典与当代路线的结构性障碍坐标，完成了全部可形式化归约链的 Lean 4 Layer A 验证（0 `sorryAx`，仅依赖 3 条经典白名单公理），并在寻找反例与对照模型时衍生出了整个 **Paper 2 连分数谱与维数理论系列**。

本日志与 Paper 1 正文 [`../01_main_paper/paper1_e_plus_pi.tex`](../01_main_paper/paper1_e_plus_pi.tex) 物理分离，供同行学者透明复查每一条尝试路径为何失败、卡在哪一精确不等式、哪些已成独立无条件结果、哪些仍待攻关。

---

## 一、Paper 1 主稿精确章节地图（75 页，2026-11-25 核实）

| 节号 | 标题（行号） | 类别（`AGENTS.md`） | 核查与形式化状态 |
| :--- | :--- | :--- | :--- |
| §1 | Introduction (`L71`) | 综述与边界声明 | 编译 0 错 / 0 Overfull |
| §2 | Preliminaries, classical theorems, and unconditional baseline (`L127`) | 5 文献复现（Vieta 至少一超越、四数至多一有理） | Lean `Elementary.lean` 已核实 |
| §3 | Window periods and the converse to denominator locking (`L270`) | 1 无条件模型结果（仿射窗长 $2B\|C\|$、5-窗锐性、逐素数约分 $G_j$） | Lean `AffineWindowAssembly/Audit.lean` + 2500 位数值 |
| §4 | The bounded golden-orbit limit spectrum (`L941`) | 1 无条件模型结果（`prop:conjugate-positivity`、$B=1\text{--}6$ 全互素类精确最小值与第二极限点、4 类多尺度） | Lean `GoldenOrbit*`, `GeneralEndpointRigidity.lean` + 2500 位数值 |
| §5 | General quadratic orbits, ideal classes, and uniform interval counting (`L2064–3284`) | 1 无条件模型结果（一般二次判别式、素范数障碍、导子素数迹测试、理想类密度） | 部分核心引理入 Lean（`OrbitAndFlow`, `DensityCube`, `TraceMarkov`）+ 精确证书 |
| §6 | Reductions, obstructions, and conditional frameworks (`L3285–3855`) | 3 等价改写/换靶 + 2 条件结果 + 5 障碍分析 | Lean `Measure`, `Series`, `FlintHills`, `MeiburgConvergence`, `Alekseyev`, `Escape` 均无 `sorryAx` |
| §7 | Conclusion and open problems (`L3856–3905`) + Use of AI (`L3906`) | 诚实边界与开放靶点 | 明确声明 $e+\pi$ 开放 |
| App. A | Computational verification and certificates (`L4021`) | 4 有限计算 / 有限排除（Arb $q\ge 10^{500018}$、OEIS A058651 前 20000 商、SymPy 12/12、450 位区间） | 两台机器（本机 + Colab）逐项一致复现 |
| App. B–D | Machine-Verified Lean (`L4152`) / Audit trail (`L4667`) / Reproducibility (`L4701`) | 5 形式化与审计留痕 | 经 `check_audit_reconcile.py` 对账 |

---

## 二、编年全周期攻关与试错流水（Rounds 1–10 + A–E 支线 + 2026-11-24/25 前沿轮）

### 阶段一：云端自主攻关第 1–9 轮（障碍地图奠基与自我纠偏）

*原始全量归档见 [`../../progress_and_path_analysis.md`](../../progress_and_path_analysis.md) 与 [`../06_historical_versions/`](../06_historical_versions/)。*

| 轮次 | 尝试方向与产出 | 结果判定 | 精确失败 / 阻断坐标与教训 |
| :--- | :--- | :--- | :--- |
| **Round 1** | 度量归约（定理 A：$e+\pi,e-\pi,e\pi,e/\pi$ 任一有理 $\Rightarrow\mu(\pi)=2$）；连分数有限状态转换器必要条件（定理 B，Raney）；级数尾项刚性 $t_{n+1}=(n+1)t_n-1$（命题 C）；乘法重构 $e^e\cdot e^\pi=e^r$；混合积分 $\int_0^\pi e^x\sin x\,dx=(e^\pi+1)/2$ | **成功建立归约骨架，但原问题 0 突破**（类别 3 + 5） | 障碍定位：① $\mu(\pi)>2$ 预期为假（通有数 $\mu=2$）且未证；② $\pi$ 连分数无结构定理；③ 混合积分仅产出乘法型 $e^\pi$ 而非加法型 $e+\pi$。 |
| **Round 2** | 尝试四指数/六指数定理构造全代数 $2\times 2$ 矩阵；定理 E（$\mu(\pi)\le M\Rightarrow \mu_0=1+1/(M-1)$）；Mahler 分类分离；最小未证假设层级 | **四指数/六指数/Mahler 全部阻断**（命题 D；类别 3） | ① 命题 D 证实在 $e+\pi=r$ 下无法凑出全代数 $2\times2$ 指数矩阵；② $M\ge 2\Rightarrow \mu_0\le 2$ 与 $\mu(e)=2$ 完全自洽，无矛盾；③ $e,\pi$ 同属非 $U$-数，有理 Möbius 变换保 Mahler 类；④ 最小条件站即 $\mathrm{Schanuel}(1,i\pi)$，无更便宜中间站。 |
| **Round 3** | 精读 Bertolin (`arXiv:2609.15294`) 1-动机/Tannakian 归约；测试 Gauss 积分、Stirling、混合积分三候选桥梁；跟踪 Bai 2026 ($\mu(\pi)\le 7.101863$)；SymPy 12/12 符号验证 | **三桥梁全排除；Bertolin 归约为等价/更强开放子问题**（类别 2 + 3 + 4） | ① Gauss 积分给出 $\pi=4I^2$（二次化摧毁线性形式）；Stirling 仅为渐近非精确恒等式；② Bai 2026 代入定理 E 得 $\mu_0\approx 1.1639\le 2$，无矛盾；③ 子问题“$\pi=\wp_\Omega(\text{代数点})$?”不弱于原问题。 |
| **Round 4** | 命题 G（$\wp$ 缩放闭包）；测试第 4 桥梁 $\int_0^\infty\frac{\cos x}{1+x^2}dx=\frac{\pi}{2e}$；首次生成 450 位 `mpmath.iv` 证书排除 $q\le 1000$ | **第 4 桥梁排除；发现统一机制障碍**（类别 3 + 4） | **核心机理诊断**：一切已知 $e$–$\pi$ 精确恒等式（欧拉、$e^\pi$、$\coth$、模形式、Gauss、余弦积分）皆为“在周期处求指数值”，产出全属 $e^\pi$ 或 $\pi/e$ 乘法族，而 $e=e^1$ 是代数点指数值，无已知加法桥梁。 |
| **Round 5–6** | 合并前四轮档案；建立 Flint Hills 桥（原称命题 H：$e+\pi\in\Q\Rightarrow$ Flint Hills 收敛）；检验 Chowla–Selberg 公式 $\varpi=\Gamma(1/4)^2/(2\sqrt{2\pi})$ | **Chowla–Selberg 循环关闭；Flint Hills 桥初建**（类别 2 + 3） | ① Chowla–Selberg 代入 $\pi=\Gamma(1/4)^4/(8\varpi^2)$ 构成恒等循环，不提供新代数约束（120 位核验误差 $7.7\times10^{-121}$）；② 发现第 6 轮误将 Meiburg 预印本归功于 Alekseyev（受 Wikipedia 混述误导）。 |
| **Round 7** | **关键自我纠偏**：逐字精读 Alekseyev 原文，确认其仅证“收敛 $\Rightarrow\mu(\pi)\le 5/2$”而无反向；将命题 H 降级更正为条件命题 H'（显式依赖 Meiburg `arXiv:2208.13356`）；警示 2026 批量未核声称 | **纠错成功（学术纪律里程碑）**（类别 5） | 确立硬规则：严禁采信 Wikipedia 二手转述；一切预印本必须全文核对结构并显式标条件。 |
| **Round 8–9** | 全文逐段核验 Meiburg 证明（稀疏性引理 + $S_1/S_2/S_3$ 三分划 + 线性函数 $f(\mu)=1+u/v-\mu$）；评估 Dan 2026 (`arXiv:2609.12338`)；建立 50 项六组审计台账 | **Meiburg 结构核验通过**（后于本机补完 Lean 无公理定理化！） | Dan 2026 明确重申经典 Flint Hills 收敛性未解；四存活靶点（$\mu(\pi)>2$、Flint Hills 发散、$\pi\in S$、新加法恒等式）均“预期为假或无候选”。 |

---

### 阶段二：本机第 10 轮与并行五支线 A–E（2026-11-13 至 2026-11-21）

*执行任务书见 [`../05_research_process/Parallel_Research_Plan.md`](../05_research_process/Parallel_Research_Plan.md)；关键支线记录见 `05_research_process/{A,B,C,D,E}/`。*

| 支线 / 轮次 | 攻击目标 | 实际产出与状态 | 精确障碍坐标与对照点检验（$x=6-e$） |
| :--- | :--- | :--- | :--- |
| **本机 Round 10 (T3 & 靶点 4)** | 形式化 Alekseyev 方向；探索新加法积分 $e+\pi=1+\int_0^1 e^x dx+\int_0^1 \frac{4}{1+x^2}dx$ | **T3 发现分子分母障碍并最终在 `Alekseyev.lean` & `MeiburgConvergence.lean` 完全闭合**（Meiburg 公理已证为定理！）；靶点 4 阻断 | ① 曾误写 $\|n-m\pi\|=n\|\pi-m/n\|$（实为 $\|m\|\cdot\|\pi-n/m\|$），发现并修复；② $1+\int_0^1(e^x+\frac{4}{1+x^2})dx$ 无清分母与小余项兼得机制。 |
| **支线 A（Dirichlet 窗口与双既约见证）** | 对 $q=Q_j, H=\lfloor q\sqrt{j}\rfloor$ 与见证 $\|d\pi-p\|\le 1/(H+1)$，证 $Q_j/\gcd(Q_j,d)$ 无界（[`../05_research_process/A/handoff.md`](../05_research_process/A/handoff.md)） | **无条件分类定理 + 双既约见证引理**：同一窗口至多 2 个既约见证，若共存则 $\operatorname{lcm}(R(b),R(f))=Q_j\Rightarrow\max\ge\sqrt{Q_j}$；$1\le j\le 60$ 认证找到 17 个 $\pi$ 的双既约窗口（类别 1 + 4） | **障碍坐标**：对照点 $6-e$ 全 $j$ 恰有 1 个既约见证且商恒为 1；对真实 $\pi$，**证明双既约窗口无穷多次出现**等价于排除某种极稀连分数相位锁定，仍完全开放。 |
| **支线 B（阶乘尾项与 Machin 截断）** | 排除 `FactorialCriterion.lean` 充要条件 $n\{-n!\pi\}\to 1$（[`../05_research_process/B/handoff.md`](../05_research_process/B/handoff.md)） | **命题 B1（分母障碍）+ 命题 B2（阈值放大至 $\varepsilon=1/2$）+ 等价算术靶 (★)**（类别 1 + 3） | **障碍坐标**：Machin 截断至 $O(1/n)$ 误差后，既约分母 $Q_n$ 必含素因子 $>n$（B1），阻断“部分和为整数”的企图；剩余靶 (★) $\min_j\|nP_n+Q_n-jnQ_n\|\ge Q_n/2$ 需控制分子 $P_n\bmod Q_n$ 位置，取模后丢失所有实解析信息。 |
| **支线 C（同号收敛分数 + Hermite 积分）** | 复用 `PadeIntegral.lean` 构造同号线性形式 $L_n=u_n(e+\pi)-v_n$（[`../05_research_process/C/signed-pade-forms.md`](../05_research_process/C/signed-pade-forms.md)） | **严格非零构造 + 精确充要判据** $(-1)^n L_n>0$ 且 $L_{n_j}\to 0 \iff \frac{gh\,q_{k+1}}{Q_n}\to\infty$（类别 1 + 3） | **障碍坐标**：同时确保了整性与严格非零性，但趋零条件 $\frac{gh\,q_{k+1}}{Q_n}\to\infty$ 要求 $\pi$ 在特定窗口处有极大下一个收敛分母 $q_{k+1}$（即部分商 $a_{k+1}$ 超常放大），与已知 $\pi$ 信息脱节。 |
| **支线 D（形式化审核与测度反例）** | 独立核验 A 命题、攻关 Paper 2 定理 12 测度步、排查假嵌套与实数不等式漏洞 | **抓出 5 个真实数学/证明错误并全部修复**（见 [`../../verification/成果清单与边界.md`](../../verification/成果清单与边界.md)），推动 Lean 内核全量闭合 | 修复了“$\alpha<1$ 维数$=1$”错猜想、假嵌套引理、`thm:golden-b2-exact` 伪不等式 $\|\eta'\|\ge\varphi-1$（改证 `prop:conjugate-positivity`）等真实缺陷。 |
| **支线 E（文献与可用性审核）** | 逐项核对 BLR (2019)、Komatsu (2003/2005/2009)、Davis (1945)、Perron (1954)、CMMS (2004) | **核正 CMMS Theorem 5→3**，厘清 BLR 定理 7 / 推论 8 适用边界（类别 5） | 确认无任何已发表定理可同时控制固定常数 $\pi$、指定 $e$-分母窗口与公因子 $\gcd(Q_j,d)$。 |

---

### 阶段三：仿射窗口、黄金比与一般二次轨道深化（2026-11-18 至 2026-11-22）

*原始归档见 [`../05_research_process/golden_finite_spectrum/`](../05_research_process/golden_finite_spectrum/README.md)、[`../05_research_process/round10_advance/`](../05_research_process/round10_advance/00_十轮推进记录.md) 与 Paper 1 §3–§5。*

- **战略思路（为何做对照组模型？）**：在发现“凡仅用 $Q_j$ 递推与有界缺陷的论证必然被 $x=A/B-e$ 阻断”后，团队转而彻底剖析所有有理仿射对照模型 $x=(A+Ce)/B$ 的连分数窗口与二次轨道谱（尤其是黄金比 $\varphi$ 轨道 $c_\varphi(x)$），以建立“若能证明 $c_\varphi(\pi)=0$ 即可把 $\pi$ 与全体有理仿射模型分离”的固定目标测试。
- **取得成果（类别 1 无条件模型结果 + Lean 4 核验）**：
  - 仿射窗口显式周期 $2B|C|$ 与 5-窗锐性；任意分母 $B$ 的逐素数约分公式 $G_j=g\gcd(A(Q_j/g)-(B/g)P_j,g)$；
  - 黄金比轨道有限判定算法、`prop:conjugate-positivity`（$\eta'\ge\varphi^{-2}>0$）、$B=1\text{--}6$ 全互素类精确最小值与第二极限点、4 类多尺度轨道、一般二次判别式素范数障碍与导子素数迹测试；
  - **直接孕育了 Paper 2**：研究 $\{x:\limsup j\|Q_j x\|\le c\}$ 的度量大小时发现了完全离散谱 $\frac14\Z_{\ge0}\cup\{\infty\}$、精确 Hausdorff 规范与三分法，从而独立裂变为 Paper 2 系列！
- **遗留局限**：模型侧全量闭合，但**仍缺关于真实 $\pi$ 连分数数字的任意无穷子列输入**；对任意通式分母 $B\ge 7$ 的封闭第二极限点通式亦未得到。

---

### 阶段四：2026-11-24/25 Arb 百万位排除、双通道前沿核查与战略评估

- **严格有限分母排除（`prop:denominator-bounds`，类别 4）**：
  - 脚本：[`../../verification/rational_exclusion_bound_20261124.py`](../../verification/rational_exclusion_bound_20261124.py)（`python-flint==0.9.0` Arb 球算术，12/12 `--selftest` PASS）及 [`../../verification/oeis_a058651_crosscheck_20261124.py`](../../verification/oeis_a058651_crosscheck_20261124.py)。
  - 结论：**若 $x\in\{e+\pi, e\pi, \pi-e, \pi/e\}$ 且 $x=p/q$，则 $q\ge 10^{500018}$**（$D=10^6$，本机与 Colab 双机输出逐项一致）；严格复核 OEIS A058651 前 20,000 个部分商。
  - **诚实边界**：有限排除规模再大也不触及无理性证明；**禁止再投入资源做“扩大有限排除 $\to$ 幻想证明无理性”路线**。
- **2024–2026 外部尖端前沿双通道核查（[`../../verification/方法论证据支撑深调报告_20261125.md`](../../verification/方法论证据支撑深调报告_20261125.md)、[`../../verification/工具库整理与六方向前沿调研记忆_20261125.md`](../../verification/工具库整理与六方向前沿调研记忆_20261125.md)）**：
  - 逐一排查 Calegari–Dimitrov–Tang 算术全纯界（`2408.15403`, `2510.04156`, `doi:10.1137/25m1806776`）、Fauzan + Fischler–Lai–Sprang–Zudilin 2026 $\zeta(5)$ 与奇 $\zeta$ 行列式簇、Chudnovsky (`2610.26539`) 双纽线周期 $\mu(\Omega)=2$、Bai (`2609.11276`) $\mu(\pi)\le 7.101863$、Yu (`2606.17303`) 145 候选 Apéry 尾项 no-go 审计、Dan (`2609.12338`)、Zapata (`2603.09719`)、撤稿预印本 `2502.03474v2`、以及 `openai/math` `PiExponent`。
  - **统一诊断**：2024–2026 的全部突破（算术全纯界、Hankel 行列式、双纽线周期）均作用于**单源积分 / 微分方程 / 周期家族**，均未产生连接代数点指数值 $e=e^1$ 与椭圆/圆周期 $\pi$ 的新加法算术机制。

---

## 三、全路线障碍矩阵（哪些已死、哪些悬而未决、哪些仍有探索空间）

| 路线编号与名称 | 状态 | 精确障碍坐标 | 建议动作 |
| :--- | :--- | :--- | :--- |
| R-A 级数/阶乘尾项 (`FactorialCriterion`, 支线 B) | **阻断** | $\{n!\pi\}$ 分布未知；Machin 截断取模后丢失分子位置信息 (★) | 暂停常规尝试，除非出现控制 $n!\pi\bmod 1$ 的新分析工具 |
| R-B Niven 积分与 4 候选桥梁 | **阻断** | $\sin(e+\pi)=-\sin e\neq 0$；一切已知 $e$–$\pi$ 积分桥均产出 $e^\pi$ 或 $\pi/e$ | **永久关闭**已有 4 候选，仅当发现全新加法型精确恒等式时重启 |
| R-C 经典超越数论 / 四指数 / 六指数 / Mahler | **阻断** | $e^{i(e+\pi)}=-e^{ie}$ 落在所有已知超越定理外；命题 D 阻断 $2\times2$ 矩阵 | 关闭经典应用路径 |
| R-D 丢番图逼近三角界 / $\mu(\pi)$ 平移 (定理 A/E) | **阻断（需 $\mu(\pi)>2$）** | 组合三角界 $\ge 2$；$\mu_0=1+1/(M-1)\le 2$；$\mu(\pi)>2$ 预期为假 | 仅季检外部 $\mu(\pi)$ 新文献 |
| R-E Flint Hills 桥 (命题 H') | **条件存活（预期为假）** | Meiburg 已 Lean 定理化；但经典 Flint Hills 预期收敛（即发散靶预期为假） | 季检 Flint Hills 进展 |
| R-F Dirichlet 双既约窗口 (支线 A) & 同号线性形式 (支线 C) | **阻断（需 $\pi$ 连分数输入）** | 需证 $\pi$ 有无穷多双既约窗口或 $\frac{gh\,q_{k+1}}{Q_n}\to\infty$，均缺 $\pi$ 部分商定理 | 暂停纯递推尝试；仅当获得 $\pi$ 部分商新工具时重启 |
| R-G 黄金比轨道测试 $c_\varphi(\pi)=0$ | **归约存活（缺 $\pi$ 输入）** | 模型侧 $B=1\text{--}6$ 全闭合；$\pi$ 侧仍需连分数相位信息 | 模型理论已归档；可拓展任意 $B$ 通式作为独立副产品 |
| R-H 算术全纯界 (CDT 2024–2026) / 混合 $E$-函数与 $G$-函数 | **高风险前沿探针（未证可行）** | CDT 作用于单源全纯函数族；如何对 $e$（整函数 / $E$-函数）与 $\pi$（$G$-函数 / 周期）构造共同算术全纯函数族尚未建立 | **唯一值得做限时预注册探索的新方向**（须先做文献核查与可证伪测试，严禁夸大） |
| R-I 有限排除（Arb $q\ge 10^{500018}$） | **已饱和** | 有限排除绝不能证无理性 | 冻结，不再加码算力 |

---

## 四、2026-11-25 Round 2 增补记录与未完成项台账

### 4.1 2026-11-25 Round 2 实测闭环记录（详见 [trial_notes_M1_M2_20261125.md](trial_notes_M1_M2_20261125.md)）
1. **Paper 1 侧 Lean 经典公理消减（L1 已完成）**：新增 [`MuEEqTwo.lean`](../../epi_formal/EpiFormal/MuEEqTwo.lean) 与 [`AuditMuEEqTwo.lean`](../../epi_formal/AuditMuEEqTwo.lean)（**9/9** 声明仅依赖 `[propext, Classical.choice, Quot.sound]`，0 `sorryAx`，完整内置并证明 `mu_e_eq_two_proved`），保持 `Audit.lean`（937 条双射）与 `Axioms.lean` 受保护口径稳定。
2. **Route M1（混合 $(1,e^z,G(z))$ Hermite–Padé 与 CDT 算术全纯界障碍）— 已完成诊断**：
   - 无条件证明混合形式精确整除律 $(M-1-d)!\mid D_{M-1}(G)\,d!\,Q_d$（去掉草稿中无必要的多项式次数预设）及混合级数 $F(z)=\alpha e^{\beta z}+G(z)$ 在 CDT 框架下的分母率 $\tau(F)=\infty$ vs 共形半径上界 $\rho\le 4R_G$ 冲突（[`verify_mixed_eg_hermite_pade_obstruction_20261125.py`](../../verification/verify_mixed_eg_hermite_pade_obstruction_20261125.py)，SymPy 符号整性与 104 例/LLL/CDT 逐素数核验全 PASS）。
   - **对抗性自省边界**：严格指出整除下界自身并不直接排除固定点余项趋零（实际指数爆炸源自 $(S)$-消元方程组），且 M1 明确不覆盖 $M\le 2n+O(1)$、变尺度 $z_n\to 0$ 或 Borel 变换绕行；对 $e+\pi$ 无理性不降难，归类为 Paper 1 §6 窄诊断障碍（类别 1 + 5）。
3. **Route M2（一般整数 Möbius 窗口周期 $T=2|\Delta|$、3-轨道与 $e$ 全收敛子谱）— 已完成核实**：
   - 构造对抗反例 $M=\begin{pmatrix}39&-106\\71&-193\end{pmatrix}$（$\Delta=-1$ 但 $V_3=0$）抓获并修正草稿阈值 $j>|\Delta|+3$ 的漏洞，确立严格阈值 $J_0(a,b,c,d)$、窗口移位定理（$W_{j+T}=(b_j+4G_j^2, S_j)$）与仅有的 **3 条 $\mathrm{PGL}_2(\mathbb{Z})$ 发散轨道** $(e+1)/2,(e+1)/4,(e+3)/4$（[`verify_mobius_e_full_conv_20261125.py`](../../verification/verify_mobius_e_full_conv_20261125.py) 40 矩阵 + 1240 本原 HNF 穷举全通过；明确注明 Elsner–Havens 2025 付费墙专著全文**未核到**）。
   - 将其中的 **$e$ 全正则收敛子谱理论（M2c）** 正式剥离并入 **Paper 2E**（[`../../paper2_spectral_gap_dimension/spinoff_full_convergent_and_even_hurwitz_20261125/`](../../paper2_spectral_gap_dimension/spinoff_full_convergent_and_even_hurwitz_20261125/README.md)）及 Lean 4 模块 `FullConvergentSpectrum.lean`（**40/40** 基础三公理）。

### 4.2 明确挂起的后续可探索项
1. **Elsner–Havens (2025) 专著先例全文对照**：需通过图书馆馆际渠道获取该专著后核实其 *"Characteristic gcd sequences $G(e)$"* 与 M2a/M2b 的重叠细节，此前禁止对 M2a/M2b 作对外优先权宣称。
2. **任意分母 $B\ge 7$ 黄金比轨道封闭通解**：目前闭合 $B=1\text{--}6$ 与 $22/7-e$，任意惰性素数幂 $B=p^k$ 的第二极限点闭式公式尚未探索。
3. **与原问题相关的新范式跟踪**：持续按季度检索 Bai/Fauzan/Fischler–Rivoal/CDT/$e+\pi$ 与 $\mu(\pi)$ 外部进展；严禁将有限排除（$q\ge 10^{500018}$）与模型结果表述为“更接近证明 $e+\pi$”。
