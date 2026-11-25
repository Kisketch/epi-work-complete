# T6：临界标度猜想——陈述草案与可证性评估（2026-11-24）

> **状态**：本文全部内容为 **[CONJECTURE] / [HEURISTIC] / [CHECKED-by-computation]**，**不是定理**。标签按研究协作者模板：`[THEOREM-known + reference]` `[CONJECTURE]` `[HEURISTIC]` `[CHECKED-by-computation]` `[SPECULATION]`。凡引用仓库已证结果标 `[THEOREM-repo]`（Lean 内核口径，作者自报 + 两次 Colab 复现，助理未复跑）。数值依据见 [`critical_point_scan_record_20261124.md`](critical_point_scan_record_20261124.md)（类别 4）。
> **用途**：对应 PI《新努力方向与路径》第二段第 5 项「临界情形定理」的候选精确陈述；以及 README §五.2(c)「临界边界 $s_0(S)=1/2$ 处收敛速率与超临界精确主导前因子常数」的直接目标。

---

## 1. 记号（照录 tex 3797–3821）

$S\subset\Z_{\ge1}$、$B\subset\Z_{\ge0}$ 有限，$d:=|S|+|B|\ge1$；$\mathcal A_{m,S,B}$、$F_{m,S,B}$ 如论文二定义；$W_S(p,n)=\sum_{w\in S^n}q(w)^{-p}$，$C_S(p)=\sum_{n\ge0}W_S(p,n)$，$s_0(S)=\inf\{s:\sum_n W_S(2s,n)<\infty\}$。记
$$\varepsilon_m:=2\dimH F_{m,S,B}-1\ (\ge0),\qquad \eta:=1-2s_0(S)\in(-1,1).$$
**结构级数留数**：
$$\kappa(S):=\lim_{p\downarrow 2s_0(S)}(p-2s_0(S))\,C_S(p).$$
对有限字母表，转移算子 $L^S_sf(x)=\sum_{a\in S}(a+x)^{-2s}f(1/(a+x))$ 的谱半径 $\rho_S(p)$（指数 $p=2s$）在 $p=2s_0$ 处为 1，若 $\rho_S$ 可微且 $c(S):=\lim_n W_S(2s_0,n)$ 存在（PF），则 $\kappa(S)=c(S)/(-\rho_S'(2s_0))$ —— 这是数值计算用的等价式（已对 69 个 $S$ 算出，见记录 §5）。

## 2. 已证锚点（`[THEOREM-repo]`，`thm:multi-residue-asymptotic`）

- (T-ii) $\dimH F_{m,S,B}\to\max(1/2,s_0(S))$。
- (T-iv) 次临界（$\eta>0$）：$\dimH F_{m,S,B}=\tfrac12+\tfrac{dC_S(1)}{2m}-\tfrac{(dC_S(1))^2\log m}{2m^2}+\tfrac{d^2C_S(1)(\gamma C_S(1)-C_S')}{2m^2}\cdot\!(\text{论文系数})\!+O((\log m)^2/m^3)$（系数以论文原文为准，此处只取首项用于对照）。
- (T-v) 超临界（$\eta<0$）：$\dimH F_{m,S,B}-s_0(S)=\Theta(m^{-2s_0(S)})$，常数未定。

## 3. 猜想（三条，由强到弱）

**猜想 C2（统一标度律）** `[CONJECTURE]`
对任意有限 $S,B$（$d\ge1$），
$$\varepsilon_m\,(\varepsilon_m+\eta)\,m^{1+\varepsilon_m}\ \longrightarrow\ d\,\kappa(S)\qquad(m\to\infty).$$

**猜想 C1（临界指数与振幅）** `[CONJECTURE]`
若 $s_0(S)=1/2$（即 $\eta=0$），则
$$\lim_{m\to\infty} m^{1/2}\Bigl(\dimH F_{m,S,B}-\tfrac12\Bigr)=\frac{\sqrt{d\,\kappa(S)}}{2},$$
特别地维数在相变点连续、临界指数为 $1/2$、无对数修正。

**猜想 C3（交叉尺度）** `[HEURISTIC]`
远离临界时渐近区的起始尺度为 $m^*\asymp d\kappa(S)/\eta^2$；$m\ll m^*$ 时 $\varepsilon_m\approx\sqrt{d\kappa}\,m^{-1/2}$，$m\gg m^*$ 时回到 (T-iv)/(T-v)。

**推论（由 C2 形式推出）**
- (a) $\eta>0$：$\varepsilon_m\sim \dfrac{d\kappa}{\eta}\,m^{-1}$，即 $\dimH-\tfrac12\sim\dfrac{d\,C_S(1)}{2m}$，与 (T-iv) 首项一致**当且仅当** $C_S(1)=\kappa/\eta$——这恰是极点分解 $C_S(p)=\frac{\kappa}{p-2s_0}+O(1)$ 在 $p=1$ 处的一阶近似，故 (a) 与已证结果相容但**不等价**（C2 是更强的统一陈述）。
- (b) $\eta<0$：$\dimH F_{m,S,B}-s_0\sim\dfrac{d\kappa}{2(2s_0-1)}\,m^{-2s_0}$，给出 (T-v) 的**精确前因子**——README §五.2(c) 列为未解决的常数。数值：$S=\{1,2\}$ 预测 $K=33.43$，$m=16384$ 测得 $m^{2s_0}\Delta=32.86$（差 2%）。
- (c) $\eta\to0$ 两侧极限连续：$\lim_{\eta\to0^\pm}\lim_m m^{1/2}\varepsilon_m$ 存在且等于 $\sqrt{d\kappa}$（在 $\kappa(S)$ 随 $S$ 连续的范围内）。

## 4. 数值证据摘要 `[CHECKED-by-computation]`（细节见记录 §4–§5）

| 项目 | 结果 |
|---|---|
| 自检 | 单残差在 10 条内核核验开括号内 10/10；$n=16$ vs $n=24$ 差 $\le7.1\times10^{-15}$ |
| 临界窗口 | 族 $S_j=\{3,4,5,6,j\}$：$j=9$ 超临界（$s_0=0.502406$）、$j=10$ 次临界（$0.498980$） |
| 临界慢化 | $\|s_0-1/2\|\lesssim0.003$ 时 $\alpha_{\rm loc}\approx0.46$–$0.55$（名义渐近为 1 或 $\approx1.005$） |
| 零参数验证 | 近临界两侧 $\varepsilon_{\rm obs}/\varepsilon_{\rm model}$：$m=16384$ 处 1.007 / 1.010（$B=\emptyset$），1.011 / 1.014（$B=\{1\}$，$m=8192$）；随 $m$ 单调趋 1 |
| 远离临界 | $S=\{1,2\}$：比值 →1.001；$S=\{2,3\}$：恒 1.19 = $C_S(1)_{\rm真}/(\kappa/\eta)$（极点近似远离极点的已知误差） |
| $d$ 线性 | $B=\{1\}$ 组用 $d+1$ 同样成立 |

## 5. 可证性评估 `[HEURISTIC]`/`[SPECULATION]`

- **路线**：C2 的证明 = 论文二 S15 尾展开 + 极点分解引理 + S17 型隐式方程渐近。关键新引理只有一条：$C_S(p)=\dfrac{\kappa(S)}{p-2s_0(S)}+O(1)$（$p\downarrow2s_0$）。它由有限字母表转移算子的 PF 理论与 $\rho_S(p)$ 的解析性给出——这类事实在连分数维数文献中是标准工具 `[THEOREM-known, reference unverified]`（未在本轮核对书目，按纪律标注）。尾方程 $d\,C_S(1+\varepsilon)\,m^{-1-\varepsilon}\,\zeta(1+\varepsilon)=1$ 在 $\varepsilon=\varepsilon_m\to0$ 下展开，$O(\varepsilon)$ 项与 $O(1/m)$ 项相对主项 $m^{-1}\kappa/(\varepsilon+\eta)$ 均可忽略（$\varepsilon\gtrsim m^{-1/2}$），S17 的代数需改为对 $\varepsilon$ 的隐式求解——**难度 hard，但不需要新范式**。
- **Lean 侧**：需在 `poincareAbscissa` 机器上加（i）极点分解引理的 Lean 版本（涉及 $\rho_S$ 可微性——当前内核是否已有谱半径可微性：**未核到**）；（ii）隐式方程渐近（S17 推广）。按 Layer A 标准。
- **风险**：若 $\rho_S$ 在 $2s_0$ 处不可微（有限字母表下通常可微，但未核），C2 退化为双侧界；若 $\kappa$ 随 $S$ 在临界集处不连续，C1 的振幅常数需对每个临界 $S$ 单独陈述。
- **精确临界集的存在性**：有限整数集合中 $s_0(S)=1/2$ 恰好成立者未必存在（族 $\{3,4,5,6,j\}$ 在 $j=9$ 与 $10$ 之间跨越）；C1 的实际可证形式可能是「对任意 $\eta$ 的统一渐近 C2」而临界集本身以极限方式处理。

## 6. 对 T2 施工图的修正建议 `[SPECULATION]`

T2 §7 的条件 (C3)「尾无限」不足以给出 $1/2$ 地板：稀疏无限尾（如 $A=\{2^{2^k}\}$）的 $\sum_{a\in A}a^{-1}<\infty$，其横坐标可远低于 $1/2$。建议把 (C3) 改为「尾的调和和发散 $\sum_{a\in A_m\setminus F}a^{-1}=\infty$（等价地尾有正下密度）」，并把「任意调和和发散的无限字母表 $\dimH E_A\ge1/2$」列为待证（Frostman/Bernoulli 路线）。此条**未验证**，仅为建议。

## 7. 它没做到什么

- 未证明任何一条猜想；数值已到 $m=65536$（增补完成），近临界组的渐近区（$m^*\sim10^5$–$10^6$）仍未触及；故「$m^{-1/2}$」是临界窗内的有效指数，名义渐近未被直接观测到（深次临界/远离临界组已观测到）。
- 数值判据属 R2 类（谱半径=1，Bowen/Mauldin–Urbanski 口径），非内核口径。
- 书目未核：第 5 节 `[THEOREM-known, reference unverified]`。
- 不改变「$e+\pi$ 无理性开放」基线；本文件与论文一无关。

## 8. 关键引理：$C_S(p)$ 的极点分解——证明骨架与 Lean 化路径（主会话撰写，状态：骨架，非证明）

**引理（极点分解）**：设 $S\subset\Z_{\ge1}$ 有限、$|S|\ge2$，$L^S_{p/2}f(x)=\sum_{a\in S}(a+x)^{-p}f(1/(a+x))$，$\rho_S(p)$ 为其谱半径，$s_0=s_0(S)$（即 $\rho_S(2s_0)=1$）。则存在 $\kappa(S)\in(0,\infty)$ 使
$$C_S(p)=\sum_{n\ge0}W_S(p,n)=\frac{\kappa(S)}{p-2s_0}+O(1)\qquad(p\downarrow 2s_0),$$
其中 $\kappa(S)=c(S)/(-\rho_S'(2s_0))$，$c(S)=\lim_n W_S(2s_0,n)\in(0,\infty)$。

**证明骨架（六步）**：
1. **算子框架**：$\varphi_a(x)=1/(a+x)$ 是 $[0,1]$ 上的 $C^\omega$ 压缩（$\varphi_a([0,1])=[1/(a{+}1),1/a]$，压缩比 $\le 1/\min S<1$）；$L^S_{p/2}$ 是该有限 IFS 的 Ruelle 转移算子，权重 $(a+x)^{-p}$ 对 $p$ 解析。
2. **谱隙**：在 $[0,1]$ 的复邻域上的全纯函数空间（sup 范数）中，$L^S_{p/2}$ 紧（实为 nuclear），谱 = 单重正主特征值 $\rho_S(p)$ + 模 $\le\lambda_2(p)<\rho_S(p)$ 的尾部；由解析摄动（Kato），$\rho_S(p)$ 在任意 $p_0>0$ 邻域实解析、严格递减。〔[THEOREM-known, reference unverified]：有限字母表连分数转移算子的核性与谱隙是 Hensley / Mauldin–Urbanski 一系的标准工具；本轮未核书目，按纪律标注〕
3. **Perron–Frobenius**：$p\approx2s_0$ 时 $L^S_{p/2}$ 正且强连通（全移位语义，$|S|\ge2$），Krein–Rutman 给唯一正右特征函数 $h_p$、正左泛函 $\nu_p$，且 $W_S(p,n)=(L^n 1)(0)=c(p)\,\rho_S(p)^n+O(\lambda_2(p)^n)$，$c(p)=h_p(0)\nu_p(1)/\langle h_p,\nu_p\rangle$；$p=2s_0$ 处 $\rho=1$ 故 $W_S(2s_0,n)=c(S)+O(\lambda_2^n)$。
4. **求和**：$C_S(p)=\sum_n W_S(p,n)=\dfrac{c(p)}{1-\rho_S(p)}+A(p)$，$A$ 在 $p=2s_0$ 邻域解析（紧区间上一致的几何控制由 2–3 的连续性给出）。
5. **取极点**：$1-\rho_S(p)=-\rho_S'(2s_0)(p-2s_0)+O((p-2s_0)^2)$，代入即得引理，$\kappa=c(S)/(-\rho_S'(2s_0))$。这正是扫描所用 $\kappa_{\rm pred}$ 的解析出处（数值实现：$c$ 用 $p=2s_0$ 处配点迭代——收敛率 $\lambda_2<1$；$\rho'$ 用中心差分）。
6. **接入尾方程**：$V_{S,s}(x)=\sum_n\sum_w(q(w)+p(w)x)^{-2s}$ 对 $x$ 一致地 $=C_S(2s)+O(1)$（S14/S15 的一致 $x$ 控制已在仓库证明），故尾方程 $d\,C_S(1+\varepsilon)m^{-1-\varepsilon}\zeta(1+\varepsilon)\approx1$ 中的 $C_S$ 代入极点分解即得 C2 的隐式方程；$\varepsilon_m\gtrsim m^{-1/2}\gg m^{-1}$ 使 $O(\varepsilon)$ 与 $O(1/m)$ 修正项可忽略，S17 代数改为对 $\varepsilon$ 的隐式求解（唯一结构变化）。

**待闭合的三个缺口（诚实清单）**：(a) 步骤 2 的谱隙需按选定函数空间正式陈述并在紧 $p$ 区间上一致化（引文待核：Hensley 1992；Mauldin–Urbanski 2003；Pollicott–Vytopil? 均未核）；(b) $h_p,\nu_p$ 对 $p$ 的解析性（Kato 摄动，标准但需引文）；(c) $\rho_S(2s_0)=1$ 与 $s_0(S)$ 的同一性依赖经典 Bowen 公式（CLU Thm 2.3，仓库已引；内核已有无 Bowen 版 `dimH_cfAlphabetSet_finset_eq_poincareAbscissa`，两条路径的相容性需一桥接引理）。$|S|=1$ 时 $\kappa$ 的退化情形（单字母表 $s_0=0$）不在本引理范围。

**Lean 化路径（Layer A）**：路径一（彻底）：在 mathlib 上形式化有限 CF 算子的谱隙与解析摄动——mathlib 是否已有 Perron–Frobenius / 谱半径解析性工具：**未核到**；路径二（务实）：把极点分解引理作为一条新公理 `C_S_pole_decomposition` 引入（入经典白名单层，同 `mu_e_eq_two` 的处理先例），在内核内完成 C2 的隐式方程渐近（纯实代数，S17 推广）——定理陈述 Layer A、关键输入显式公理，诚实标注。建议先走路径二出定理，路径一长期补。
