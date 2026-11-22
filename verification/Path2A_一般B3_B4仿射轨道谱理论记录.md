# Path 2A：一般 $B=3,4$ 仿射轨道谱理论与 $B\ge 5$ 谱机制记录

> **一句总判断**：我们在无外加公理与未证假设前提下，修补了原论文一 `thm:golden-b2-exact` 第 1822 行 $|\eta'|\ge\varphi-1$ 的伪不等式（替换为更强的 `prop:conjugate-positivity`：$\eta'\ge\varphi^{-2}>0$），建立了一般有理端点四重算术刚性（`lem:general-endpoint-rigidity`）与偶长后缀分离引理（`lem:even-suffix-sep`），从而**无条件确定**了 $B=3$（对一切 $3\nmid A$）与 $B=4$（对一切奇数 $A$）仿射控制模型 $c_\varphi(A/B-e)$ 的精确值、全部极值轨道族与精确第二极限点（含模 $16$ 乘法子群 $\{\pm 1,\pm 7\}$ 禁除 $m=37$），并经 2500 位 `mpmath` 零失败验证（属**第 1 类：无条件新结果**与**第 4 类：有限计算验证**）；**以上工作仅刻画 $e$-侧仿射对照模型的离散谱机制，不对 $e+\pi$ 无理性公开问题构成任何推进。**

---

## 0. 诚实五分类逐项对照表

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| `prop:conjugate-positivity`：$\eta\in E_\varphi\cap(1,\infty)\setminus\{\varphi\}\Rightarrow \eta'\ge\varphi^{-2}>0$（修复原 `thm:golden-b2-exact` Case 1 伪不等式） | **1. 无条件新结果**（内部证明补洞） | **已核实**（纸面证明 + `[-12,12]^4` 全部 2920 个 $\mathrm{GL}_2(\Z)$ 矩阵中 708 个满足条件元素实测 $\min\eta'=\varphi^{-2}$，0 反例） | 显式反例 $\eta=\varphi+1=[2;\overline1]$（$\eta'=\varphi^{-2}<1/2<\varphi-1$）；完全闭合 `thm:golden-b2-exact`、`thm:golden-b3-exact`、`thm:golden-b4-exact` Case 1 与 Case 2 | 论文一 `prop:conjugate-positivity`；`verify_golden_b3_b4_exact.py` §1 |
| `lem:general-endpoint-rigidity`（惰性素数非整除、偶 $D=2d$ 奇偶律 $m\equiv d+1\pmod 2$、模 $2D$/$2d$ 同余筛、$4\tau$ 代数反演公式）与 `lem:even-suffix-sep` | **1. 无条件新结果** | **已核实**（完整纸面证明 + `[-6,6]^4` 744 矩阵 $\times$ 5 有理端点 0 误差 + $B=3,4$ 全部 12 后缀 $\Delta(S)>0$ 验证） | 推广论文一 `lem:norm-parity-rigidity` 与 `lem:pell-b2-rigidity` 至任意有理端点 $(p_1/q_1,p_2/q_2)$；无冗余 $\pm$ 符号（$M_{u,v}=2m_0=2\varepsilon m$） | 论文一 `lem:general-endpoint-rigidity`、`lem:even-suffix-sep`；`verify_golden_b3_b4_exact.log` §2–§3 |
| `thm:golden-b3-exact`：对一切 $3\nmid A$，$c_\varphi(A/3-e)=1-\frac{20}{9\sqrt5}$，4 族极值轨道，第二极限点 $\frac{22}{9\sqrt5}-1$ | **1. 无条件新结果** | **已核实**（完整纸面证明 + 2500 位 `mpmath` 320 窗 + $4\tau$ 反演穷举 + $3392\times 2$ 非极值扫描） | 2018–2026 二次 Lagrange 谱公开检索负搜索未见先例（与 Lin 2018 Lemma 4.2 之 $\liminf a_r=\infty$ 无重叠） | 论文一 `thm:golden-b3-exact`；`verify_golden_b3_b4_exact.log` §4 |
| `thm:golden-b4-exact`：对一切奇数 $A$，$c_\varphi(A/4-e)=1-\frac{35}{16\sqrt5}$，3 族极值轨道，模 $16$ 子群 $\{\pm1,\pm7\}$ 禁除 $m=37$，第二极限点 $1-\frac{33}{16\sqrt5}$ | **1. 无条件新结果** | **已核实**（完整纸面证明 + 2500 位 `mpmath` 283 窗；确认 $j\ge 17$ 起后缀与窗长 $r_j$ 最小周期均为 $8$ 且 $b_{j+8}=b_j+1$；Case 2 $\theta_n=\varphi-1, Q_n=2, r_2=1/32$ 精确下界 `0.36959`） | 同上，且首次刻画模 $16$ 乘法子群禁除最近相邻奇数 $m=37$ 的新现象 | 论文一 `thm:golden-b4-exact`；`verify_golden_b3_b4_exact.log` §5 |
| `rem:golden-general-regimes`：$B=5,6,7$ 与 $(1+e)/6,(1+e)/3,(1+2e)/3$ 谱机制数值对照 | **1. 局部机制** + **4. 有限计算**（未证一般 Case 2） | **已核实**（2500 位 `mpmath` 计算；修正 $(1+2e)/3$ 极小值为 $1-\frac{13}{6\sqrt5}\approx 0.03103721>0$） | 在 `thm:affine-window` / `cor:affine-single` 与 Lin (2018) 交界处分类 4 类机制（纯无界退化、恒定 $D_j=2B^2$、多尺度分裂、一致离散性） | 论文一 `rem:golden-general-regimes`；`verify_golden_b3_b4_exact.log` §6 |

---

## 1. 关键数学结果与核实数值摘要

### 1.1 共轭正性补洞（`prop:conjugate-positivity`）
- **原漏洞**：旧版 `thm:golden-b2-exact` Case 1 误称对一切 $\eta\in E_\varphi\cap(1,\infty)$ 有 $|\eta'|\ge|\varphi'|=\varphi-1>1/2$。反例 $\eta=\varphi+1=[2;\overline1]>1$ 给出 $\eta'=1+\varphi'=\varphi^{-2}\approx 0.38196601125<0.5<\varphi-1$。
- **修正与实测**：`prop:conjugate-positivity` 证明对一切 $\eta\in E_\varphi\cap(1,\infty)\setminus\{\varphi\}$ 恒有 $\eta'\ge\varphi^{-2}>0$，从而对任意 $z>0$ 恒有 $|\eta'+z|=\eta'+z>|\eta'|$。在 $[-12,12]^4$ 全部 $2920$ 个 $\mathrm{GL}_2(\Z)$ 矩阵中满足条件的 $708$ 个元素上，实测 $\min \eta'=\varphi^{-2}$，0 例例外。

### 1.2 $B=3$ 定理（`thm:golden-b3-exact`）
- 对一切 $3\nmid A$，$Q_j\bmod 3$ 以 $6$ 为周期循环 $(1,1,1,2,2,2)$，故 $G_j=1$、$D_j=18$（$j>9$），归约至 $10/3-e$ 与 $11/3-e$。两者在周期 $T=18$（$b_{j+18}=b_j+4$）内出现完全相同的 $6$ 个偶长后缀 $q_0\in\{1,5,7,11,13,17\}$（$\Delta(S)>0$ 实测为 $1/2, 1/35, 1/63, 1/209, 1/273, 1/306$）。
- 在 $D=18\ (d=9)$ 下，$m$ 为偶数且惰性素数 $3\nmid m$；最接近 $9\sqrt5$ 的偶数为 $m=20$（$c_\varphi(A/3-e)=1-\frac{20}{9\sqrt5}\approx 0.00619201$），次近为 $m=22$（$c_{\mathrm{sec}}^{(3)}=\frac{22}{9\sqrt5}-1\approx 0.09318879$）。
- 2500 位 `mpmath` 对 $10/3-e$ 与 $11/3-e$ 各验证 320 个连续窗口（$4\tau$ 反演精确锁定 4 族极值轨道与 4 族第二极限点轨道；3392 个非极值点扫描最小值分别为 `0.090116` 与 `0.090096`，随 $b_j\to\infty$ 趋近 `0.093189`）。

### 1.3 $B=4$ 定理（`thm:golden-b4-exact`）
- 对一切奇数 $A$，$G_j=1$、$D_j=32$（$j>16$），归约至 $13/4-e$ 与 $15/4-e$。从 $j=17$ 起，**后缀 $S_j$ 与窗口长度 $r_j=1+|S_j|$ 均以 $8$ 为最小周期重复**，且每 $8$ 步首数字增 $1$（$b_{j+8}=b_j+1$，从而在 `thm:affine-window` 的周期 $T=32$ 下满足 $b_{j+32}=b_j+4$）；$(P_j,Q_j)\bmod 16$ 最小周期为 $8$、$\bmod 32$ 为 $16$。
- 全部出现后缀 $q_0\in\{7,9,15,23,25,31\}$ 满足 $q_0\bmod 16\in\{\pm 1,\pm 7\}$。因 $37^2-5\cdot 16^2=89$ 的所有因子 $N(\gamma)\in\{\pm 1,\pm 89\}$ 均落入 $\{\pm 1,\pm 7\}\pmod{16}$，同余律 $m\equiv -\varepsilon q_0 N(\gamma)\pmod{16}$ **将 $m=37\equiv 5\pmod{16}$ 彻底排除**。故 $c_\varphi(A/4-e)=1-\frac{35}{16\sqrt5}\approx 0.02172026$（每类各有 3 族极值轨道），第二极限点为 $c_{\mathrm{sec}}^{(4)}=1-\frac{33}{16\sqrt5}\approx 0.07762196$（于 $S^{(15)}=[2,7,1,1]$ 处由 $[a_0;\dots,b_j,2,\overline1]$ 与 $[a_0;\dots,b_j,2,7,\overline1]$ 达到）。
- Case 2 全分支严格验证：于 $\theta_n=\varphi-1,\ 2\le Q_n\le b_j-1$，因 $S^{(31)}=[1,31]$ 给出逆后缀 $r_2=1/32$，区间端点 $Q_n=2$ 处给出下界 $\frac{2}{\sqrt5}(2-\varphi+\frac{1}{32})\approx 0.36959164$（大于 $c_{\mathrm{sec}}^{(4)}$）；$\theta_n\notin\{\varphi-1,2-\varphi\}$ 最小分支为 $\frac{\sqrt5}{16}\approx 0.13975425 > c_{\mathrm{sec}}^{(4)}$。2500 位 `mpmath` 对 $13/4-e$ 与 $15/4-e$ 各验证 283 个连续窗口，非极值扫描（2015 / 1731 点）最小值分别为 `0.073129` 与 `0.073068`。

### 1.4 $B\ge 5$ 与一般 $(A,B,C)$ 谱机制（`rem:golden-general-regimes`）
- $B=5$（$16/5,\dots,19/5-e$）：$D=50$，4 个剩余类共享同一 20 元后缀集，均达到 $m=56$（$\approx 0.00175845$）与 $m=54$（$\approx 0.03401863$）。
- $B=6$（$19/6,23/6-e$）：$D=72$（$d=36$），惰性素数 $3\mid 36$ 刚性禁除 $m=81$，两者均达到 $m=79$（$1-\frac{79}{36\sqrt5}\approx 0.01861461$），展示 $c_\varphi(A/B-e)$ 对 $B$ 的非单调性。
- $B=7$（$22/7-e$，$T=98$）：$G_j\in\{1,7,49\}$ 引起 $D_j\in\{2,14,98\}$ 分裂，单周期分布 `{14: 48, 98: 42, 2: 8}`（其中 $W_{59}=[1,1,1],\ W_{60}=[5928,1,1]$ 具有 $D=2$）。
- $(1+e)/6$：$D_j\in\{1,3\}$ 分布 `{1: 8, 3: 4}`，局部极小 $\frac{7}{3\sqrt5}-1\approx 0.04349839$，次小 $1-\frac{\sqrt5}{3}\approx 0.25464401$。
- $(1+e)/3$：$D_j\in\{2,6\}$ 分布 `{2: 4, 6: 2}`，局部极小 $1-\frac{2}{\sqrt5}\approx 0.10557281$，次小 $\frac{8}{3\sqrt5}-1\approx 0.19256959$。
- $(1+2e)/3$：$D_j\in\{4,12\}$ 分布 `{4: 8, 12: 4}`，局部极小为 $1-\frac{13}{6\sqrt5}\approx 0.03103721>0$（于 $W_j=[b_j,2,2,1,1],\ D_j=12,\ q_0=5$ 处达到），次小 $\frac{\sqrt5}{2}-1\approx 0.11803399$。

---

## 2. 它没做到什么（边界与未完成事项）
1. **Case 2 理论边界**：$B=5,6,7$ 与 $(1+e)/6,(1+e)/3,(1+2e)/3$ 仅完成了后缀分类、算术刚性机制与有限窗口数值实测（第 4 类），**尚未**逐一证明与 `thm:golden-b3-exact` / `thm:golden-b4-exact` 同等完备的 Case 2 排除定理。
2. **Lean 4 形式化范围**：`epi_formal/` 当前仅覆盖 $B=1,2$（`GoldenOrbitRigidity.lean`、`GoldenOrbitB2Rigidity.lean`）；`prop:conjugate-positivity`、`lem:general-endpoint-rigidity`、`lem:even-suffix-sep` 及 `thm:golden-b3-exact`、`thm:golden-b4-exact` 为纸面完整证明与 2500 位 `mpmath` 检验，尚未纳入 Lean 4 形式化库。
3. **中心公开问题**：$c_\varphi(\pi)=0$ 与 $e+\pi\notin\Q$ 仍完全公开；本记录所有结果均不声称推进或解决 $e+\pi$ 的无理性。
