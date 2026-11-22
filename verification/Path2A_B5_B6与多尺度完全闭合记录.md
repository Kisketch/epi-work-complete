# Path 2A：$B=5,6$ 与多尺度仿射轨道完全闭合记录（Case 1 + Case 2）

> **一句总判断**：我们在无外加公理与未证假设前提下，建立了一般周期仿射窗 Case 2 排除准则（`lem:general-case2-criterion`，含单数字窗 $D_j=1$ 的精确下界 $h(\theta)(1-\theta)\ge\sqrt5-1$），并**无条件完成**了 $B=5$（一切 $5\nmid A$）、$B=6$（一切 $\gcd(A,6)=1$，含惰性素数 $3\mid 36$ 禁除 $m=81$ 与模 $8$ 同余禁除 $m=83$）以及多尺度目标 $(1+e)/6,(1+e)/3,(1+2e)/3,22/7-e$ 的 Case 1 + Case 2 完整分类定理（`thm:golden-b5-exact`、`thm:golden-b6-exact`、`thm:golden-multiscale-exact`），经 2500 位 `mpmath` 零失败验证（属**第 1 类：无条件新结果**与**第 4 类：有限计算验证**）；**任意参数分母 $B\ge 7$ 的闭式谱公式仍公开，且全部结果仅刻画 $e$-侧仿射对照模型，不对 $e+\pi$ 无理性公开问题构成任何推进。**

---

## 0. 诚实五分类逐项对照表

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| `lem:general-case2-criterion`（一般周期仿射窗 Case 2 排除准则，含 $D_j=1$ 单数字窗辅助界 $h(\theta)(1-\theta)\ge\sqrt5-1$） | **1. 无条件新结果** | **已核实**（纸面完整证明 + `[-12,12]^4` 中全部 $688$ 个满足条件元素实测 $\min h(\theta)(1-\theta)=\sqrt5-1$，0 例例外） | 统一 `thm:golden-b3-exact`/`thm:golden-b4-exact` 的 Case 2 分支下界并首次覆盖含 $r_j=1$ 相位的混合尺度模型 | 论文一 `lem:general-case2-criterion`；`verify_golden_b5_b6_multiscale.log` §1 |
| `thm:golden-b5-exact`：对一切 $5\nmid A$，$c_\varphi(A/5-e)=\frac{56}{25\sqrt5}-1$，4 族极值轨道，第二极限点 $1-\frac{54}{25\sqrt5}$（8 族） | **1. 无条件新结果** | **已核实**（完整纸面 Case 1+Case 2 证明 + 2500 位 `mpmath` 四类各 194 窗 + $4\tau$ 反演 + 约 $2.09\times 10^4\times 4$ 非极值扫描） | 补齐 `cor:golden-finite-shift-examples` 未给出的极值族完整分类、20 元共享后缀 $(\Z/50\Z)^\times$ 与直接 Case 1+Case 2 排除；与 Lin (2018) 无重叠 | 论文一 `thm:golden-b5-exact`；`verify_golden_b5_b6_multiscale.log` §2 |
| `thm:golden-b6-exact`：对一切 $\gcd(A,6)=1$，最小周期 $18$（$b_{j+18}=b_j+1$），惰性 $3\mid 36$ 禁除 $m=81$ 且模 $8$ 同余禁除 $m=83$，$c_\varphi(A/6-e)=1-\frac{79}{36\sqrt5}$（4 族），第二极限点 $1-\frac{77}{36\sqrt5}$（4 族） | **1. 无条件新结果** | **已核实**（完整纸面证明 + 2500 位 `mpmath` 193 窗 $\times 2$ + 模 $8$ 禁除验证 + $15168\times 2$ 非极值扫描） | 揭示 $q_0\bmod 24\in\{5,11,13,19\}$（$q_0\equiv\pm 3\pmod 8$）对 $m=83\equiv 3\pmod 8$ 的刚性禁除；超出 `cor:golden-finite-shift-examples` 数值列举 | 论文一 `thm:golden-b6-exact`；`verify_golden_b5_b6_multiscale.log` §3 |
| `thm:golden-multiscale-exact`：$(1+e)/6$、$(1+e)/3$、$(1+2e)/3$、$22/7-e$ 完整 Case 1+Case 2 精确常数、极值族与第二极限点 | **1. 无条件新结果** | **已核实**（完整纸面证明 + 2500 位 `mpmath` 135–210 窗 + $4\tau$ 反演 + 37377 点全周期扫描） | $(1+e)/6,(1+e)/3,(1+2e)/3$ 属 $C\ne -B$ 一般仿射模型，不在 `thm:golden-finite-shift` 覆盖范围内；$22/7-e$ 完整给出 8 个 $D_j=2$ 窗、$m=1..5$ 校验与 $7\mid 7,49$ 禁除 | 论文一 `thm:golden-multiscale-exact`；`verify_golden_b5_b6_multiscale.log` §4 |
| 任意参数 $B\ge 7$ 与一般 $(A,B,C)$ 闭式极限公式（`rem:golden-general-regimes`） | **公开边界**（固定 $A/B-e$ 可由 `thm:golden-finite-shift` 有限计算，但一般参数闭式未证） | **诚实标注公开** | — | 论文一 `rem:golden-general-regimes` |

---

## 1. 关键数学机制与 2500 位实测汇总

1. **单数字窗 Case 2 辅助界（`lem:general-case2-criterion`(c)）**：
   当 $D_j=1$（$r_j=1, S_j=\emptyset, r_1(j)=0$）且 $Q_n=b_j-1$ 时，$\theta_n\in E_\varphi\cap(0,1)\setminus\{\varphi-1,2-\varphi\}$ 满足：若 $\theta_n\le 1/2$ 则 $h(\theta_n)(1-\theta_n)\ge\sqrt5$；若 $\theta_n>1/2$，写 $\theta_n=1/(1+\psi)$ 后有 $h(\theta_n)(1-\theta_n)=|m/\sqrt5-1|$（$m\in2\Z+1$，$|m|\in\{1,3\}$ 对应被排除的 $\{2-\varphi,\varphi-1\}$），故必有 $|m|\ge 5$，即 $h(\theta_n)(1-\theta_n)\ge\sqrt5-1\approx 1.23606798$（于 $[0;1,2,\overline1]$ 取等）。在 `[-12,12]^4` 全部 $688$ 个元素上实测 `min = 1.2360679775 == sqrt(5)-1`，0 例例外。

2. **$B=5$（`thm:golden-b5-exact`）**：
   - $(Q_j\bmod 5)$ 以 $10$ 为最小周期且 $Q_{j+5}\equiv -Q_j\pmod 5$（$5\nmid Q_j$），故 $G_j=1,D_j=50$（$j>25$）。
   - $16/5-e, 17/5-e, 18/5-e, 19/5-e$ 共享全部 $20$ 个 $(\Z/50\Z)^\times$ 偶长后缀（最小周期 $T=50$，$b_{j+50}=b_j+4$）。
   - $m=56$ 锁定 $4$ 族极值轨道（$c_\varphi=\frac{56}{25\sqrt5}-1\approx 0.00175845$）；$m=54$ 锁定 $8$ 族第二极限点轨道（$c_{\mathrm{sec}}^{(5)}=1-\frac{54}{25\sqrt5}\approx 0.03401863$）。Case 2 最紧分支为 $\theta_n\notin\{\varphi-1,2-\varphi\}, Q_n\ge 2$，下界 $\frac{\sqrt5}{25}\approx 0.08944272 > c_{\mathrm{sec}}^{(5)}$。

3. **$B=6$（`thm:golden-b6-exact`）**：
   - $\gcd(Q_j,6)=1$，故 $G_j=1,D_j=72$（$j>36$）；$19/6-e$ 与 $23/6-e$ 均从 $j=37$ 起具有最小周期 $18$ 与 $b_{j+18}=b_j+1$（因 $4\cdot 18=72$ 且 $S_{54}=S_{36}$），共享 $12$ 个后缀 $q_0\in\{5,11,13,19,29,35,37,43,53,59,61,67\}$，全部满足 $q_0\bmod 24\in\{5,11,13,19\}$（即 $q_0\equiv\pm 3\pmod 8$）。
   - 惰性素数 $3\mid 36$ 禁除 $m=81$；因 $83^2-5\cdot 36^2=409\equiv 1\pmod 8$，所有因子 $N(\gamma)\equiv\pm 1\pmod 8$，同余律 $m\equiv 36-\varepsilon q_0 N(\gamma)\equiv\pm 1\pmod 8$ 彻底禁除 $m=83\equiv 3\pmod 8$。
   - 故 $c_\varphi(A/6-e)=1-\frac{79}{36\sqrt5}\approx 0.01861461$（4 族），第二极限点 $c_{\mathrm{sec}}^{(6)}=1-\frac{77}{36\sqrt5}\approx 0.04345981$（4 族），Case 2 全分支下界 $\ge \frac{5\sqrt5}{36}\approx 0.310565 > c_{\mathrm{sec}}^{(6)}$。

4. **多尺度与一般仿射目标（`thm:golden-multiscale-exact`）**：
   - **$(1+e)/6$**（$T=12$，最小周期 $6$，$D_j\in\{1,3\}$）：$c_\varphi=\frac{7}{3\sqrt5}-1\approx 0.04349839$（$j\equiv 0,1\pmod 6$，$[a_0;\dots,b_j,\overline1]$）；$c_{\mathrm{sec}}=1-\frac{\sqrt5}{3}\approx 0.25464401$（$[a_0;\dots,b_j,2,\overline1]$ 与 $[a_0;\dots,b_j,1,2,\overline1]$）；含 $r_j=1$（$D_j=1$）窗口由 $h(\theta)(1-\theta)\ge\sqrt5-1\approx 1.236068$ 闭合。
   - **$(1+e)/3$**（$T=6$，$D_j\in\{2,6\}$）：$c_\varphi=1-\frac{2}{\sqrt5}\approx 0.10557281$（$D_j=2$）；惰性 $3\mid 3$ 禁除 $D=6$ 处 $m=6$，得 $c_{\mathrm{sec}}=\frac{8}{3\sqrt5}-1\approx 0.19256959$（$D_j=6$）；Case 2 下界 $\ge 0.490712$。
   - **$(1+2e)/3$**（$T=12$，最小周期 $6$，$D_j\in\{4,12\}$）：惰性 $3\mid 6$ 禁除 $D=12$ 处 $m=15$，得 $c_\varphi=1-\frac{13}{6\sqrt5}\approx 0.03103721>0$（$S_j=[2,2,1,1]$）；$c_{\mathrm{sec}}=\frac{\sqrt5}{2}-1\approx 0.11803399$（$D_j=4$ 处 4 族）；Case 2 下界 $\ge\frac{\sqrt5}{6}\approx 0.372678$。
   - **$22/7-e$**（$T=98$，$D_j\in\{2,14,98\}$）：单周期分布 $\{2:8,14:48,98:42\}$，$8$ 个 $D_j=2$ 窗均为 $(G_j,G_{j+1})\in\{(1,49),(49,1)\}$ 且 $S_j=[1,1]$（$m=1..5$ 奇偶禁除 $m=1,3,5$，$m=2,4$ 分别给出 $1-2/\sqrt5$ 与 $4/\sqrt5-1$）；惰性 $7\mid 7,49$ 禁除 $D=14$ 的 $m=14$ 与 $D=98$ 的 $m=112$；得 $c_\varphi=\frac{110}{49\sqrt5}-1\approx 0.00394889$（4 族）与 $c_{\mathrm{sec}}=1-\frac{108}{49\sqrt5}\approx 0.01430473$（4 族）；Case 2 最紧分支为 $\frac{\sqrt5}{49}\approx 0.04563404 > c_{\mathrm{sec}}$。

---

## 2. 边界与未完成事项（诚实声明）
1. **任意参数 $B\ge 7$**：`thm:golden-finite-shift` 已证明对每个固定 $A/B-e$ 存在有限算法，但对任意参数分母 $B\ge 7$ 的闭式谱公式与一般 $(A,B,C)$ 含单数字窗的完全分类仍公开。
2. **Lean 4 形式化边界**：`epi_formal/` 仅形式化 $B=1,2$ 与截断头界（`GoldenOrbitRigidity.lean`, `GoldenOrbitB2Rigidity.lean`, `GoldenHeadCutoff.lean`），`lem:general-case2-criterion` 及 `thm:golden-b5-exact`--`thm:golden-multiscale-exact` 为纸面证明与 2500 位 `mpmath` 零失败校验，不声称已经 Lean 4 核验。
3. **核心公开问题**：$c_\varphi(\pi)=0$ 与 $e+\pi\notin\Q$ 仍完全公开，本记录不对其构成任何推进。
