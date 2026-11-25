# 论文二系列（Paper 2A / 2B / 2C / 2D / 2E / S）衍生演化、试错与评审纠偏日志

> **一句话总判断**：Paper 2 系列从 Paper 1 寻找“$e+\pi$ 归约障碍的对照模型与度量刻画”中自然裂变而出，现已演化为四轨主干（`2A`/`2B`/`2C`/`S`）与两篇独立衍生定理论文——**`Paper 2D`**（临界标度修复 + 无条件超临界精确常数 + 稀疏字母表尾相变）与 **`Paper 2E`**（[`../spinoff_full_convergent_and_even_hurwitz_20261125/README.md`](../spinoff_full_convergent_and_even_hurwitz_20261125/README.md)：$e$ 全正则收敛谱 + 偶数拟周期 $(-1)^{p-1}$ 符号律 + Brouwer-free Perron–Frobenius），并**已全面完成 L1 / L2 / L3 / L4a / L5 六路 Lean 4 Layer A 核实（累计 `1,093` 条声明、0 `sorryAx`，彻底消除 Paper 2 正文全部外置假设 R1 与 R3）**。

---

## 一、从 Paper 1 到 Paper 2 系列的裂变脉络

1. **起源（2026-11-15 至 11-18）**：在研究 $e+\pi$ 时，Paper 1 构造了沿 $e$ 选定收敛分母 $Q_{j+1}=(4j+2)Q_j+Q_{j-1}$ 的加权逼近泛函 $\Lambda(x)=\limsup_{j\to\infty} j\|Q_j x\|$。初期仅作为 Paper 1 的伴随度量注记（历史 B 稿 [`../../paper1_e_plus_pi/02_companion_paper/Phase2_revised.pdf`](../../paper1_e_plus_pi/02_companion_paper/Phase2_revised.pdf)）。
2. **首次裂变（2026-11-19 至 11-22）**：发现 $\Lambda(\R)=\frac14\Z_{\ge0}\cup\{\infty\}$ 完全离散化、正能级 $k/4$ 的三路精确 Hausdorff 规范分裂（$\R$ 与 $\R/\Z$）、多项式递推 $1-\alpha/r$ 及任意增长商 $Q_{j+1}=A_j Q_j+Q_{j-1}$ 的 $\gamma_{\sup}$ 维数畸变与二次相变；同步建立无 Bowen 转移算子框架、全模 $m\ge2$ 严格分离与倒数 Fibonacci 常数 $\psi_{\mathrm{Fib}}$ 渐近。至此正式独立成篇并完成 `Audit.lean` 937 条 Layer A 形式化。
3. **二次裂变与四轨拆分（2026-11-23 至 11-24）**：新增 `ResidueCertTable.lean`（200 模块 $N=512$ 证书，`AuditResidueCert.lean` 27/27）与 5,039 行 `ResidueMultiAsymptotic.lean`（`thm:multi-residue-asymptotic`，`AuditResidueMultiAsymptotic.lean` 24/24），完成两次 Google Colab 独立复建与 11 切片逐字节同步工程（`split/`），并产出 `T6` 临界标度实验线（`drafts_v3_critical_scaling/`）。
4. **深度新颖性重审与 Paper 2D 突破（2026-11-25 Round 1）**：抓出旧实验稿 `sec-critical-scaling.tex` 的 **7 处数学/书目缺陷**，无条件证出**超临界精确主导常数定理** $\dim_{\mathrm H}F_{m,S,B}-s_0(S)=\frac{d\kappa(S)\zeta(2s_0(S))}{2}m^{-2s_0(S)}(1+O_{S,B}(m^{-1}))$，独立成篇为 **Paper 2D**（[`../spinoff_critical_and_supercritical_exact_20261125/README.md`](../spinoff_critical_and_supercritical_exact_20261125/README.md)）。
5. **Round 2 收口与 Paper 2E 裂变（2026-11-25 下半轮）**：新增 **6 项独立 Lean 4 Layer A 模块（105 条新声明）**——全面消去 Paper 2 **R1**（`ResidueCertStrictOpen` 22）与 **R3**（`PerronFrobenius` 13），证明 Bundschuh $\mu(e)=2$（`MuEEqTwo` 9），形式化 Paper 2D 稀疏字母表与条件超临界常数（`GeneralAlphabetFloor` 15 + `SupercriticalConstant` 6），形式化 $e$ 全正则收敛谱论（`FullConvergentSpectrum` 40），纠正偶数拟周期 Hurwitz $(-1)^{p-1}$ 符号律并审计非线性 BLR (1.6) 边界，独立成篇为 **Paper 2E**（8 页，0 Overfull / 0 Undef）并通过 [`../patch_round2_20261125.py`](../patch_round2_20261125.py) 同步至 Paper 2 SSOT（`293,395` 字节，66 页，4 轨 0/0 未定义引用）。

---

## 二、历次对抗性审稿与新颖性核查纠偏总表（零掩饰记录）

| 日期 | 审稿抓出的真实问题 / 文献先例冲突 | 修复与纠偏动作 | 留痕依据 |
| :--- | :--- | :--- | :--- |
| 2026-11-20 | 原相变猜想“$\alpha<1$ 时 $\dim_{\mathrm H}=1$”错误；假嵌套区间条件；实数不等式 $a_0+m<B+1\Rightarrow\le B$ 错误 | 纠正为 $1-\alpha$（一般 $1-\alpha/r$）并在 `WeightedExactDim.lean` / `PolyGaugeAndPhaseTransition.lean` 机器证明；改严格嵌套与 `Nat` 不等式 | [`../../verification/成果清单与边界.md`](../../verification/成果清单与边界.md) |
| 2026-11-22 | CMMS (*Pacific J. Math.* 217, 2004) 主定理在原稿中被误引为 Theorem 5 | 下载官方 PJM 全文 PDF 逐页核对（pp. 57–58），确认实为 **Theorem 3**，全稿三处更正 | [`../../verification/cmms_citation_check_20261122.md`](../../verification/cmms_citation_check_20261122.md) |
| 2026-11-23 | 旧猜想 C2（固定 $\eta\neq0$ 下 $\varepsilon(\varepsilon+\eta)m^{1+\varepsilon}\to d\kappa$）数值出现 1.19 恒定偏差 | 严格证伪固定 $\eta$ 形式（`rem:naive-C2-false`），仅联合标度极限存活 | [`../../verification/verify_c2_discrepancy_20261124.py`](../../verification/verify_c2_discrepancy_20261124.py) |
| 2026-11-25 (上午) | **投稿前新颖性重审**：`2C` 渐近落在 DFSU (*Selecta Math.* 2023, Thm 4.1) 框内（$C_S=1/\bar c$）；`(i)(iii)` 为经典结果（MU96/Bowen, DLMF）；`(v)` 上界为 HU02 推论；`2B` 线性情形与 BLR (2019) 重合且原稿 `rem:poly-BLR` 误述 Baker 插补用途；`sec-resasymp.tex` L283 漏写 $m^{-1}$ 因子 | 经 `patch_novelty_wording_20261125.py`、`patch_blr_baker_fix_20261125.py`、`patch_unify_20261125.py` 全量下调夸大措辞、补齐 28/28 文献（含 CLN 2026, Brown 2026, TTWW 2026, Hensley 1996 勘误）并修正 L283 笔误 | [`../../verification/paper2_novelty_review_20261125.md`](../../verification/paper2_novelty_review_20261125.md)、[`../../verification/paper2_venue_gap_assessment_20261125.md`](../../verification/paper2_venue_gap_assessment_20261125.md) |
| **2026-11-25 (本轮 Round 1–2)** | **抓出 `drafts_v3_critical_scaling/sec-critical-scaling.tex` 共 7 处数学缺陷 + 1 处书目幻觉**：<br>① `lem:pole` 在复全纯盘 $A(\Omega)$ 上定义实非负锥 $K=\{f\in A(\Omega): f(z)\ge0\ \forall z\in\overline\Omega\}$（由开映射定理，该集合仅含非负常数，非全锥、无内点、不被 $L_p$ 保持！且 $z=0\in\partial\Omega$）；<br>② `lem:pole`(c) 写 $O(\theta(p)^n)$ 而漏乘 $\rho(p)^n$；<br>③ `lem:pole`(d) 写 $A(p)=\sum_{n\ge0}(R(p)^n 1)(0)$ 在 $n=0$ 处重复计入 $c(p)$ 且未证明 $A(p)$ 跨 $p_0$ 解析；<br>④ `lem:master` 下界侧构造 $v_N$ 从未选取足够大的 $N(m,s)$；<br>⑤ `lem:master` 写 $h(1)\le 64d\zeta(2)/m^2$ 在超临界 $s_0>1/2$ 失效，且证明 $\varepsilon_0\ge c_0/m$ 时错误假设 $\varepsilon_0\log m\to0$ 并混用 $h(s)$ 与 $h(\varepsilon)$；<br>⑥ `prop:supercritical-constant` 误将固定 $2s_0>1$ 处的 $\zeta(2s_0)$ 替换为极点主部 $1/(2s_0-1)$，导致错常数 $\frac{d\kappa}{2(2s_0-1)}$，且 `rem:supercritical-status` 误判 `lem:master` 相对误差为 $C_S/m\to\infty$（实为 $C_S$ 提公因式后相对误差 $O(\Sigma/m)$！）；<br>⑦ `thm:critical-scaling` 漏写变序列 $(S_k,B_k)$ 的 $\Sigma_k/m_k\to0$、$\gamma_k\log m_k\to0$、$\sqrt{d_k\kappa_k}$ 归一化与一致极点占优假设；<br>⑧ 旧 `refs-addendum-20261124.tex` 把 `Mayer1991` 错记为 *ETDS* 11 (1991)（Crossref 实核为 *CMP* **130** (1990), 311–333, `doi:10.1007/BF02473355`） | **全部彻底修复并升级为独立论文 Paper 2D**（[`../spinoff_critical_and_supercritical_exact_20261125/paper2D_critical_supercritical_exact.tex`](../spinoff_critical_and_supercritical_exact_20261125/paper2D_critical_supercritical_exact.tex)）：<br>- 改用 $\Omega=\{\|z-1\|<5/4\}$ + Fekete 幂有界 + Cesàro 紧性 + 马尔可夫极大模 + 全纯唯一性自含证明 `lem:pole`（零复锥、零黑箱）；<br>- 以 $C_S(2)\le 2(\max S+1)$、显式 $N(m,s)$ 与绝对下界 $\varepsilon_-\ge\frac{1}{2em}$ 证得三区统一主方程（$m\ge340\Sigma$）；<br>- **无条件证出新定理 `thm:supercritical-exact`**：$\dim_{\mathrm H}F_{m,S,B}-s_0=\frac{d\kappa\zeta(2s_0)}{2}m^{-2s_0}(1+O(m^{-1}))$，并以 30 位配置法佐证（$n=44$ vs $48$ 差 $<10^{-37}$）证实旧常数在 $S=\{1,2\},\{1,2,3\},\{1,2,3,4\}$ 分别偏低 $3.64\%/24.94\%/35.69\%$；<br>- 补齐 `thm:critical-scaling` 一致假设并强化 `cor:critical-exp` 至二阶对数项 $-\frac{d\kappa\log m}{4m}$ | [`../spinoff_critical_and_supercritical_exact_20261125/README.md`](../spinoff_critical_and_supercritical_exact_20261125/README.md)、[`../../verification/verify_supercritical_exact_constant_20261125.log`](../../verification/verify_supercritical_exact_constant_20261125.log) |
| **2026-11-25 (本轮临界纠偏)** | **拦截协调层对稀疏字母表的不准确转述**：任务简介曾简写为“$\dim_{\mathrm H}E_{\{2^{2^k}\}}=0$”与“一般上界 $\dim_{\mathrm H}E_A\le\theta(A)$”——**二者按字面均不成立**！（因 $E_{\{2^{2^k}:k\ge1\}}\supset E_{\{4,16\}}$ 故 $\dim_{\mathrm H}\approx 0.20311\ge 0.17091>0$；且对有限集 $A=\{1,2\}$ 有 $\theta(A)=0<0.53128=\dim_{\mathrm H}E_A$！） | 在 Paper 2D `prop:sparse-tail-phase` 中严格表述并证明**真实无条件定理**：① $\dim_{\mathrm H}E_A\ge\theta(A)$（真实地板下界）；② $\lim_{M\to\infty}\dim_{\mathrm H}E_{A\cap[M,\infty)}=\theta(A)$ 且 $\dim_{\mathrm H}\{x\in E_A: a_n(x)\to\infty\}\le\theta(A)$；③ 对 $A_{k_0}=\{2^{2^k}:k\ge k_0\}$ 有 $0<\dim_{\mathrm H}E_{A_{k_0}}\le 2^{-(k_0+1)}<1/2$（证伪朴素 $\ge1/2$ 猜想，且 $\lim_{k_0\to\infty}\dim_{\mathrm H}E_{A_{k_0}}=0$、逃逸集维数为 $0$）；④ 一般扰动尾相变 $\lim_{M\to\infty}\dim_{\mathrm H}E_{S\cup(T\cap[M,\infty))}=\max(\theta(T),s_0(S))$ | Paper 2D §7 + [`../../verification/verify_supercritical_exact_constant_20261125.log`](../../verification/verify_supercritical_exact_constant_20261125.log) Part C |

| **2026-11-25 (本轮 Round 2 对抗审核)** | **拦截“一般性去掉非线性 BLR 条件 (1.6) 且免 Baker 插补”过度声称并捕获 3 处漏洞**：① “$\forall n\ge 1$”集可在固定 $v$ 下为空集；② 超缺项（例 $v=1.5,\delta_n=1/8,r_n=24,r_{n+1}=2^{32}$）右端点集中 $99.873\%$ 子区间致等质量 Frostman 违例 $19.94\times$；③ 一般 $C^2$ Adler 失真无法控跨步累积因子 $\sum\log f'_j$。同步检出 `GeneralGrowingRec.lean` 仅覆盖奇数 Hurwitz 拟周期（漏掉偶数周期 `-1` 符号）。 | 仅在「尾集 + 右侧 $[v,v+\eta]$ + 单步有界失真 $\sup_n\delta_n r_{n+1}/(r_n v^{r_n})<\infty$」下有条件成立并收入 **Paper 2E** `rem:blr-audit`；正式证明任意 Hurwitz 拟周期 $p\ge1$ 统一公式 $Q_{j+1}=(\alpha a_j+\beta+\gamma)Q_j+(-1)^{p-1}Q_{j-1}$ 并入 Paper 2E §4 | [`../../verification/kahane_and_blr_audit_20261125.md`](../../verification/kahane_and_blr_audit_20261125.md)、[`../../verification/verify_nonlinear_blr_20261125.py`](../../verification/verify_nonlinear_blr_20261125.py) |

---

## 三、Lean 4 强化线已核实成果与留存待办追踪（2026-11-25）

| 编号 | 课题 / 强化线 | 当前状态（严格区分已核实与未完成） | 预期价值与下一步 |
| :-: | :--- | :--- | :--- |
| **L3** | **零重算消除 R1（`tab:residues-general` 全 20 条严格开界）** | **已核实（Lean 内核 `lake build` + `#print axioms` PASS）**：[`ResidueCertStrictOpen.lean`](../../epi_formal/EpiFormal/ResidueCertStrictOpen.lean) / [`AuditResidueCertStrictOpen.lean`](../../epi_formal/AuditResidueCertStrictOpen.lean) **22/22** 声明仅基础三公理，0 `sorryAx` | **已彻底消除 Paper 2 R1 Bowen 依赖**并写入 SSOT |
| **L1** | **`MuEEqTwo`（无条件证明 $\mu(e)=2$）** | **已核实**：[`MuEEqTwo.lean`](../../epi_formal/EpiFormal/MuEEqTwo.lean) / [`AuditMuEEqTwo.lean`](../../epi_formal/AuditMuEEqTwo.lean) **9/9** 仅基础三公理 | 无条件消解三经典白名单公理之一，同时保 `Audit.lean` (937) 稳定 |
| **L2** | **无 Brouwer Perron–Frobenius（消除 R3 外置特征向量假设）** | **已核实**：[`PerronFrobenius.lean`](../../epi_formal/EpiFormal/PerronFrobenius.lean) / [`AuditPerronFrobenius.lean`](../../epi_formal/AuditPerronFrobenius.lean) **13/13** 仅基础三公理，交付无条件 `thm_finite_state_tail_unconditional`（$\R$ 与 $\mathbb T$） | **已彻底消除 Paper 2 R3 外置假设**并写入 SSOT |
| **L4a** | **Paper 2D 稀疏字母表与条件超临界常数 Lean 4 形式化** | **已核实**：[`GeneralAlphabetFloor.lean`](../../epi_formal/EpiFormal/GeneralAlphabetFloor.lean) (**15/15**) + [`SupercriticalConstant.lean`](../../epi_formal/EpiFormal/SupercriticalConstant.lean) (**6/6**，条件于显式 `hPole`)，仅基础三公理 | 将稀疏字母表地板与超临界恒等归约正式纳入 Layer A |
| **L5** | **Paper 2E $e$ 全正则收敛序列完整谱论** | **已核实**：[`FullConvergentSpectrum.lean`](../../epi_formal/EpiFormal/FullConvergentSpectrum.lean) (**40/40** 仅基础三公理，`fullConv_det` 仅二公理)，0 `sorryAx` | 为 Paper 2A/2E 提供 $e$ 全收敛子对比完整形式化基石 |
| **L4b** | **Paper 2D 解析 `lem:pole` 与一致性形式化** | **待续队列（未开工）**：需形式化全纯盘 $A(\Omega)$ 上 Cesàro 紧性与单纯外围谱以消解 `SupercriticalConstant.lean` 中的 `hPole` 输入 | 实现 Paper 2D 100% 无条件 Layer A 闭环 |
| **P2-Open-1** | **替换 Paper 2 主稿 6 处未公开 `Phase1` 引用**（L266, L455, L505, L518, L4390, L4566） | **未完成（投稿前必做）**；须与作者确认公开伴随版本号后统一替换 | 消除审稿人无法访问 `Phase1` 的硬伤 |
| **P2-Open-2** | **是否存在有限整数集 $S\subset\Z_{\ge1}$ 精确满足 $s_0(S)=1/2$？** | **公开数学问题（未解决）** | 深化 `cor:critical-exp` |
| **P2-Open-3** | **严格证明 `rem:fourth-term` 第四项 $+\frac34\Gamma^3(\log m)^2/m^3$** | **启发式猜想（未证）** | 待用 `lem:master` 高阶展开与 Hurwitz 移位精细估计 |
| **P2-Open-4** | **主稿（含 2D/2E）投稿前 3 项人类独占放行门禁** | **等待人类作者亲签**（`[Author name]`、AI 政策声明、人工逐行核对） | AI 严禁代签 |

---

## 四、每项 Paper 2 子成果的诚实价值与投稿组合评估

| 子成果 | AGENTS 类别 | 数学/形式化评级 | 推荐投稿载体与组合策略 |
| :--- | :--- | :--- | :--- |
| **2A + 2B（+ 2E 扩充）主稿** | 1（2A/2E 零能级复现 KL 属 5） | 数学 **B− / C+** | 以“任意增长商递推（含全周期符号）”为主定理，$e$ 选定与全收敛谱作双旗舰推论，投 **T4** 或评估 **T3**（*ETDS*） |
| **2C + 2D 合并稿（或 2D 独立）** | 1（无 Bowen 证书 + 超临界精确常数 + 临界二阶 + 尾相变）+ 5 | 数学 **B−** | R1/R3 现已完全 Lean 闭合，2C+2D 合并可冲 **T3** 或各自独立投 **T4**；需补 MathSciNet/zbMATH 核查 |
| **Lean 4 形式化总成（356 文件 / 1,093 条 Layer A 声明）** | 形式化工程 | 形式化 **B+ / A−** | 覆盖 Brouwer-free Perron–Frobenius、无 Bowen 转移算子、$N=512$ 严格开界整数证书与全收敛谱，投 **ITP / CPP / JAR** |
| **S 补充材料** | 5 | 内部支撑 **高** | 作为上述各稿的在线 Supplement / Zenodo 伴随制品 |
