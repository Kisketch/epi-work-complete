# Path 2A：任意分母 $B \ge 7$ 与一般 $(A + Ce)/B$ 黄金比轨道谱一般理论记录

> **一句总判断**：我们在无外加公理与未证假设前提下，建立了黄金比仿射轨道的三条一般结构定理（**定理 G1** 奇素数 Hermite 反周期/回文与任意 $(A,B,C)$ 精确单尺度充要判据；**定理 G2** 任意偶分母 $B=2^a B_{\mathrm{odd}}$ 的普适四分之一周期定理与 $q_0\bmod 8,16,32,64$ 同余律；**定理 G3** 分歧素数 $5$ 赋值刚性 $v_5(M^2-5D^2)\le 2$、$D_{\max}\ge 14$ 普适 Case 2 坍缩定理与 $c_\varphi(A/B-e)>\frac{1}{10B^4+B^2\sqrt5}$ 精确下包络），并**无条件完全闭合**了 **$B=7$（全部 $7\nmid A$）、$B=8$（全部奇数 $A$）、$B=9$（全部 $3\nmid A$）、$B=10$（全部 $\gcd(A,10)=1$）、$B=11$（全部 $11\nmid A$）、$B=12$（全部 $\gcd(A,12)=1$）** 全部 $34$ 个互素剩余类的精确 $c_\varphi$、第二极限点 $c_{\mathrm{sec}}^{(B)}$、极值轨道族与 Case 1+Case 2 排除（经 `2500` 位 `mpmath` 零失败验证，属**第 1 类：无条件新结果**与**第 4 类：有限计算验证**）；**任意参数 $B\ge 13$ 的闭式谱公式仍依赖有限模 $2B^2$ 窗枚举与后缀饱和判定，且全部结果仅刻画 $e$-侧仿射对照模型，不对 $c_\varphi(\pi)=0$ 或 $e+\pi\notin\mathbb{Q}$ 构成任何推进。**

---

## 0. 诚实五分类逐项对照表（遵守 `AGENTS.md`）

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| **定理 G1**（奇素数 Hermite 反周期与回文对称；$\mathcal{Z}_Q\sqcup\mathcal{N}_Q$ 划分；任意 $(A,B,C)$ 单尺度充要判据） | **1. 无条件新结果** | **已核实**（完整纸面代数证明 + `200` 以内全部 $45$ 个奇素数及 $(2+e)/7,(1+e)/7$ 实测零例外） | 推广论文一 `cor:affine-single` 至全部 $(A,B,C)$ 与一般奇素数幂；解释为何 $B=2^a 3^b 5^c$ 对全部 $\gcd(A,B)=1$ 保持单尺度 $G_j\equiv 1$ | [verify_golden_general_b.py](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.py)、[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L2-L4) |
| **定理 G2**（一切偶分母 $B=2^a B_{\mathrm{odd}}$ 的普适四分之一周期 $S=B^2/2$ 与 $2$-进 $q_0$ 同余律） | **1. 无条件新结果** | **已核实**（完整诱导与 $Q_{2k+1}\equiv Q_{2k}\pmod{64}$ 证明 + $r=3..10$ 转移矩阵、$B=2..32$ 及 $29/14-e$ 2500 位全检） | 将 `thm:golden-b4-exact`/`thm:golden-b6-exact` 观察到的周期 $1/4$ 折半现象证明为全体偶 $B$ 普适规律（含多尺度 $B=14$） | [verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L5-L8) |
| **定理 G3**（分歧 $5$ 赋值刚性 $v_5(M^2-5D^2)\le 2$、$D_{\max}\ge 14$ 普适 Case 2 坍缩与 $c_\varphi(A/B-e)>\frac{1}{10B^4+B^2\sqrt5}$ 下包络） | **1. 无条件新结果** | **已核实**（完整纸面证明 + $744$ 个 $[-6,6]^4$ 幺模矩阵 $\times 4$ 端点与 $B=7..12$ 实测零例外） | 补充 `lem:general-endpoint-rigidity`（此前仅处理 $p\equiv 2,3\pmod 5$ 奇惰性素数）至分歧素数 $5$；当 $D_{\max}\ge 14$（含全部 $B\ge 3$）自动关闭全部非-$Q_1$ Case 2 分支 | [verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L9) |
| **$B=7$ 全剩余类完全定理**（全部 $7\nmid A$ 均落入三尺度 $\{2:8, 14:48, 98:42\}$，共享 $21$ 后缀，精确 $c_\varphi=\frac{110}{49\sqrt5}-1$、$c_{\mathrm{sec}}^{(7)}=1-\frac{108}{49\sqrt5}$） | **1. 无条件新结果** | **已核实**（完整纸面 Case 1+Case 2 证明 + `2500` 位 $29/7..34/7-e$ 各 $210$ 窗、$4\tau$ 反演与 $\sim 1.5\times 10^4\times 6$ 非极值扫描） | 将论文一 `thm:golden-multiscale-exact`(iv)（仅处理 $22/7-e$ 即 $A\equiv 1\pmod 7$）完整推广至全部 $6$ 个非零剩余类，并解释为何 $D_j=2$ 不取得 $c_\varphi$ | [verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L11-L30) |
| **$B=8$ 全奇数类完全定理**（$S=32$、$A\bmod 4$ 分两组各 $18$ 后缀、$c_\varphi=1-\frac{143}{64\sqrt5}$、$c_{\mathrm{sec}}^{(8)}=\frac{145}{64\sqrt5}-1$） | **1. 无条件新结果** | **已核实**（完整纸面证明 + `2500` 位 $33/8..39/8-e$ 各 $225$ 窗、$4\tau$ 反演与 $10518\times 4$ 非极值扫描） | 新增完整分类定理；揭示 $q_0\bmod 16\in\{1,7,15\}$ 及 $A\mapsto A+2$ 诱导 $\{49,113\}\leftrightarrow\{17,81\}$ 对换 | [verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L32-L48) |
| **$B=9$ 全 $3\nmid A$ 类完全定理**（$T=162$、共享 $54$ 后缀、惰性 $3\mid 81$ 禁除 $m=180$、$c_\varphi=\frac{182}{81\sqrt5}-1$、$c_{\mathrm{sec}}^{(9)}=\frac{184}{81\sqrt5}-1$） | **1. 无条件新结果** | **已核实**（完整纸面证明 + `2500` 位 $37/9..44/9-e$ 各 $238$ 窗、$4\tau$ 反演与 $\sim 1.86\times 10^4\times 6$ 非极值扫描） | 新增完整分类定理；$8$ 族极值 + $4$ 族第二极限点全闭合 | [verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L50-L67) |
| **$B=10$ 全互素类完全定理**（$S=50$、共享 $40$ 后缀、分歧 $5\mid 100$ 禁除 $m=225$、$c_\varphi=1-\frac{223}{100\sqrt5}$、$c_{\mathrm{sec}}^{(10)}=1-\frac{221}{100\sqrt5}$） | **1. 无条件新结果** | **已核实**（完整纸面证明 + `2500` 位 $41/10..49/10-e$ 各 $199$ 窗、$4\tau$ 反演与 $15868\times 4$ 非极值扫描） | 新增完整分类定理；首例直接由定理 G3 禁除最近奇数候选 $m=225$ 的偶分母模型 | [verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L69-L82) |
| **$B=11$ 全 $11\nmid A$ 类完全定理**（三尺度 $\{2:8, 22:80, 242:154\}$、共享 $55$ 后缀、$c_\varphi=1-\frac{270}{121\sqrt5}$、$c_{\mathrm{sec}}^{(11)}=\frac{272}{121\sqrt5}-1$） | **1. 无条件新结果** | **已核实**（完整纸面证明 + `2500` 位 $45/11..54/11-e$ 各 $258$ 窗、$4\tau$ 反演与 $\sim 1.76\times 10^4\times 10$ 非极值扫描） | 新增完整分类定理；首次实现 $T=242$ 高周期多尺度全 $10$ 类闭合 | [verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L84-L111) |
| **$B=12$ 全互素类完全定理**（$S=72$、$A\bmod 4$ 分两组各 $30$ 后缀、惰性 $3\mid 144$ 禁除 $m=321$、$c_\varphi=\frac{323}{144\sqrt5}-1$、$c_{\mathrm{sec}}^{(12)}=1-\frac{319}{144\sqrt5}$） | **1. 无条件新结果** | **已核实**（完整纸面证明 + `2500` 位 $49/12..59/12-e$ 各 $215$ 窗、$4\tau$ 反演与 $\sim 1.88\times 10^4\times 4$ 非极值扫描） | 新增完整分类定理；结合 G2 模 $32$ 分组规律与惰性 $3\mid 144$ 排除 | [verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L113-L130) |
| 任意高分母 $B\ge 13$ 显式后缀表与一般 $B$ 闭式谱公式 | **公开边界 / 算法性归约**（个案可通过模 $2B^2$ 有限窗枚举求解，参数化闭式未证） | **诚实标注公开** | — | 本记录 §4 边界声明 |

---

## 1. 基础记号与 Hermite–仿射窗口框架

记 Hermite 收敛序列 $(P_j, Q_j)_{j\ge 0}$ 由初值
$$(P_{-1}, Q_{-1}) = (1, -1), \qquad (P_0, Q_0) = (1, 1), \qquad (P_1, Q_1) = (3, 1)$$
及递推（对全部 $j \ge 0$）生成：
$$P_{j+1} = (4j+2)P_j + P_{j-1}, \qquad Q_{j+1} = (4j+2)Q_j + Q_{j-1}.$$
记基本矩阵 $H_j := \begin{pmatrix} P_j & Q_j \\ P_{j-1} & Q_{j-1} \end{pmatrix}$ 与单步转移矩阵 $M(c) := \begin{pmatrix} c & 1 \\ 1 & 0 \end{pmatrix}$。由 $H_{j+1} = M(4j+2) H_j$ 及 $\det H_0 = -2$，立得对一切 $j \ge 0$：
$$\det H_j = P_j Q_{j-1} - P_{j-1} Q_j = 2(-1)^{j+1}, \qquad \gcd(P_j, Q_j) \mid 2.$$
又因 $Q_0=Q_1=1$、$P_0=1, P_1=3$ 且 $4j+2\equiv 0\pmod 2$，归纳即知**对一切 $j \ge 0$，$P_j$ 与 $Q_j$ 恒为奇数**，故 $\gcd(P_j, Q_j) = 1$。

对给定 $(A, B, C) \in \mathbb{Z}^3$（$B \ge 1, C \ne 0, \gcd(A,B,C)=1$）与目标 $x = (A + Ce)/B$（当研究 $A/B - e$ 时取 $C = -B$ 且 $\gcd(A,B)=1$），依论文一 `thm:affine-window` / `thm:explicit-period` 定义窗口缩放因子与尺度：
$$G_j := \gcd(|A Q_j + C P_j|,\ B Q_j), \qquad p_{k(j)} = \frac{A Q_j + C P_j}{G_j}, \qquad q_{k(j)} = \frac{B Q_j}{G_j}, \qquad D_j := \frac{2B|C|}{G_j G_{j+1}}.$$
对充分大 $j$（如 $j - 1 > \max(B, |C|)^2$），$(p_{k(j)}, q_{k(j)})$ 为 $x$ 的真连分数渐近分数列，相邻两窗之间的转移矩阵分解为
$$M_{k(j+1)} = M_{k(j)} \begin{pmatrix} b_j & 1 \\ 1 & 0 \end{pmatrix} M(S_j), \qquad M(S_j) := \prod_{s \in S_j} \begin{pmatrix} s & 1 \\ 1 & 0 \end{pmatrix} = \begin{pmatrix} D_j & U_0 \\ q_0(j) & V_0 \end{pmatrix},$$
其中 $r_j := k(j+1)-k(j)$ 为奇数，$S_j$ 为偶数长非负整系数序列，且当 $D_j \ge 2$ 时 $1 \le q_0(j) < D_j$、$\gcd(q_0(j), D_j) = 1$ 且 $[S_j] = D_j / q_0(j)$。此时由 $\mathbf{v}_j := (p_{k(j)}, q_{k(j)})^T$ 满足
$$\mathbf{v}_{j+1} = \bigl(b_j D_j + q_0(j)\bigr)\mathbf{v}_j + D_j \mathbf{v}'_j, \qquad \mathbf{v}'_j := (p_{k(j)-1}, q_{k(j)-1})^T.$$

---

## 2. 一般参数化谱定理与完整证明（G1, G2, G3）

### 定理 G1（奇素数幂 Hermite 反周期、回文对称与任意 $(A,B,C)$ 精确单尺度判据）

**(1) 奇素数幂 Hermite 同余定理**：对任意奇素数幂 $M = p^k$（$p \ge 3$ 素数，$k \ge 1$），有
$$P_M \equiv 1, \quad Q_M \equiv -1, \quad P_{M-1} \equiv 1, \quad Q_{M-1} \equiv 1 \pmod{M},$$
进而对一切 $j \ge 0$ 成立反周期性、回文对称性与全周期性：
$$P_{j+M} \equiv P_j \pmod{M}, \qquad Q_{j+M} \equiv -Q_j \pmod{M}, \qquad Q_{j+2M} \equiv Q_j \pmod{M},$$
且当 $M = p$ 时，对全部 $0 \le j \le p-1$ 成立回文对称 $P_{p-1-j} \equiv P_j,\ Q_{p-1-j} \equiv Q_j \pmod{p}$。特别地，若 $M = \prod_i p_i^{k_i}$ 为任意奇数，由中国剩余定理上式与反周期性对一切奇数 $M \ge 1$ 皆成立：
$$P_{j+M} \equiv P_j \pmod{M}, \qquad Q_{j+M} \equiv -Q_j \pmod{M}.$$

**(2) $\mathcal{Z}_Q \sqcup \mathcal{N}_Q$ 素数划分**：记
$$\mathcal{Z}_Q := \{p \in \mathbb{P} : \exists j \ge 0,\ p \mid Q_j\}, \qquad \mathcal{N}_Q := \mathbb{P} \setminus \mathcal{Z}_Q.$$
则 $p = 2 \in \mathcal{N}_Q$，且对奇素数 $p$，$p \in \mathcal{Z}_Q \iff \exists j \in \{0, 1, \dots, (p-1)/2\}$ 使 $p \mid Q_j$。在 $[2, 200]$ 内全检得：
$$\mathcal{Z}_Q \cap [2, 200] = \{7, 11, 13, 31, 41, 71, 79, 97, 101, 103, 107, 157, 173, 181, 199\},$$
$$\mathcal{N}_Q \cap [2, 200] \text{ 前十项} = \{2, 3, 5, 17, 19, 23, 29, 37, 43, 47\}.$$

**(3) 任意 $(A, B, C)$ 精确单尺度充要判据**：设 $B \ge 1, C \ne 0, \gcd(A,B,C)=1$。对每个奇素数 $p$，定义可实现比值集
$$\mathcal{R}_p := \{P_j Q_j^{-1} \bmod p : 0 \le j \le (p-1)/2,\ p \nmid Q_j\} \subseteq \mathbb{F}_p.$$
则素数 $p$ 整除某个 $G_j$ 当且仅当满足以下三类之一：
1. **$p = 2$**：$2 \mid B$、$2 \nmid C$ 且 $A \equiv C \pmod 2$（此时对一切 $j$ 均有 $2 \mid G_j$）；
2. **$p \ge 3$ 且 $p \mid C$**：$p \in \mathcal{Z}_Q$；
3. **$p \ge 3$ 且 $p \mid B,\ p \nmid C$**：$-A C^{-1} \bmod p \in \mathcal{R}_p \cup (-\mathcal{R}_p)$。

**推论**：对 $x = A/B - e$（$C = -B, \gcd(A,B)=1$），恒有 $G_j \equiv 1$（全轨道单尺度 $D_j \equiv 2B^2$）当且仅当 **$B$ 不含 $\mathcal{Z}_Q$ 中的素因子**（例如全部 $B = 2^a 3^b 5^c$ 族）。对 $x = (2+e)/7$，$7 \nmid C=1$ 且 $-2 \equiv 5 \notin \pm\mathcal{R}_7 = \{1,3,4,6\} \pmod 7$，故全轨道严格单尺度 $G_j \equiv 1,\ D_j \equiv 14$；而 $(1+e)/7$ 命中 $-1 \equiv 6 \in \pm\mathcal{R}_7$，故 $G_j \in \{1,7\}$。

#### 定理 G1 证明

1. **多项式母函数与闭式公式**：置 $g_n(t) := t^n(1-t)^n = (t-t^2)^n$（$n \ge 0$）。对 $n \ge 1$ 直接求二阶导并利用 $(1-2t)^2 = 1 - 4(t-t^2)$ 得恒等式：
   $$g_{n+1}''(t) = (n+1)n\, g_{n-1}(t)\bigl(1 - 4(t-t^2)\bigr) - 2(n+1)g_n(t) = n(n+1)g_{n-1}(t) - (4n+2)(n+1)g_n(t).$$
   在多项式环 $\mathbb{Q}[t]$ 上定义线性泛函 $L_a(g) := \sum_{k \ge 0} (-1)^k g^{(k)}(a)$（$a \in \{0, 1\}$）。当 $n \ge 1$ 时，$g_{n+1}(a) = g_{n+1}'(a) = 0$，故 $L_a(g_{n+1}'') = \sum_{k \ge 0}(-1)^k g_{n+1}^{(k+2)}(a) = L_a(g_{n+1})$。从而 $\widetilde{P}_n := \frac{(-1)^n}{n!} L_0(g_n)$ 与 $\widetilde{Q}_n := \frac{(-1)^n}{n!} L_1(g_n)$ 对全部 $n \ge 1$ 满足同一递推 $\widetilde{X}_{n+1} = (4n+2)\widetilde{X}_n + \widetilde{X}_{n-1}$。直接算初值：$g_0=1 \implies \widetilde{P}_0=1, \widetilde{Q}_0=1$；$g_1 = t-t^2 \implies L_0(g_1)=0-1-2=-3, L_1(g_1)=0-(-1)-2=1$? 精细核符号：$g_1'(0)=1, g_1''(0)=-2 \implies L_0(g_1) = 0 - 1 + (-2) = -3 \implies \widetilde{P}_1 = 3$；$g_1'(1)=-1, g_1''(1)=-2 \implies L_1(g_1) = 0 - (-1) + (-2) = -1 \implies \widetilde{Q}_1 = +1$。初值与递推完全吻合，故对一切 $n \ge 0$ 有 $P_n = \widetilde{P}_n,\ Q_n = \widetilde{Q}_n$。展开 $g_n(t) = \sum_{r=0}^n \binom{n}{r}(-1)^r t^{n+r}$ 并由 $g_n(1-s) = g_n(s)$ 得 $g_n^{(k)}(1) = (-1)^k g_n^{(k)}(0)$，直接计算即得精确整数闭式：
   $$P_n = \sum_{r=0}^n \frac{(n+r)!}{r!(n-r)!} = \sum_{r=0}^n \binom{n}{r}\prod_{i=1}^r (n+i), \qquad Q_n = \sum_{r=0}^n (-1)^{n-r} \frac{(n+r)!}{r!(n-r)!}.$$

2. **模 $p^k$ 估值**：令 $n = p^k$。对于 $1 \le r \le p^k - 1$，因 $\binom{p^k}{r} = \frac{p^k}{r}\binom{p^k-1}{r-1}$ 且对 $1 \le t < p^k$ 恒有 $v_p(p^k-t)=v_p(t)$ 故 $p \nmid \binom{p^k-1}{r-1}$，有 $v_p\binom{p^k}{r} = k - v_p(r)$。同时 $\prod_{i=1}^r(p^k+i)$ 中每项满足 $v_p(p^k+i)=v_p(i)$，故其 $p$-进赋值为 $v_p(r!) \ge v_p(r)$（当 $p^s \mid r$ 时 $\lfloor r/p\rfloor + \dots \ge s$）。于是每一项 $1 \le r \le p^k-1$ 的估值至少为 $(k - v_p(r)) + v_p(r) = k$；对 $r = p^k$，项值为 $\prod_{i=1}^{p^k}(p^k+i)$ 含因子 $2p^k$ 与 $(p^k-1)!$，估值亦 $\ge k$。故仅剩 $r=0$ 项为 $1$：
   $$P_{p^k} \equiv 1 \pmod{p^k}, \qquad Q_{p^k} \equiv (-1)^{p^k} = -1 \pmod{p^k}.$$
   同理，令 $n = p^k - 1$。对 $1 \le r \le p^k - 1$，项值为 $\binom{p^k-1}{r}\cdot p^k(p^k+1)\cdots(p^k-1+r)$，显然被 $p^k$ 整除，仅剩 $r=0$ 项为 $1$，故 $P_{p^k-1} \equiv 1,\ Q_{p^k-1} \equiv (-1)^{p^k-1} = 1 \pmod{p^k}$。

3. **反周期与回文对称**：记 $J = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$。上式即 $H_{p^k} \equiv \begin{pmatrix} 1 & -1 \\ 1 & 1 \end{pmatrix} = H_0 J \pmod{p^k}$。因 $4(j+p^k)+2 \equiv 4j+2 \pmod{p^k}$，对 $j \ge 0$ 归纳得 $H_{j+p^k} \equiv H_j J \pmod{p^k}$，即 $P_{j+p^k}\equiv P_j,\ Q_{j+p^k}\equiv -Q_j \pmod{p^k}$。若 $M = \prod_i p_i^{k_i}$ 为任意奇数，对每个 $p_i^{k_i}$ 写 $M = p_i^{k_i} m_i$（$m_i$ 奇数），迭代 $m_i$ 次得 $H_{j+M} \equiv H_j J^{m_i} = H_j J \pmod{p_i^{k_i}}$，由 CRT 即得对全部奇数 $M$ 成立。再证回文：置 $\widehat{P}_j := P_{p-1-j}$、$\widehat{Q}_j := Q_{p-1-j}$（$0 \le j \le p-1$）。利用 $c_j := 4j+2$ 满足 $c_{p-1-j} \equiv -c_j \pmod p$ 及 $c_{p-1} \equiv -2 \pmod p$，有
   $$\widehat{P}_0 = P_{p-1} \equiv 1 = P_0, \quad \widehat{P}_1 = P_{p-2} = P_p - c_{p-1} P_{p-1} \equiv 1 - (-2)\cdot 1 = 3 = P_1 \pmod p,$$
   $$\widehat{Q}_0 = Q_{p-1} \equiv 1 = Q_0, \quad \widehat{Q}_1 = Q_{p-2} = Q_p - c_{p-1} Q_{p-1} \equiv -1 - (-2)\cdot 1 = 1 = Q_1 \pmod p,$$
   且反向递推 $\widehat{X}_{j+1} = X_{p-2-j} = X_{p-j} - c_{p-1-j}X_{p-1-j} \equiv c_j \widehat{X}_j + \widehat{X}_{j-1} \pmod p$，故 $(\widehat{P}_j,\widehat{Q}_j) \equiv (P_j, Q_j) \pmod p$ 对全部 $0 \le j \le p-1$ 成立。由 $Q_{j+p} \equiv -Q_j$ 与 $Q_{p-1-j} \equiv Q_j \pmod p$ 即得 $p \in \mathcal{Z}_Q \iff \exists j \in [0, (p-1)/2]$ 使 $p \mid Q_j$。

4. **单尺度判据**：对素数 $p$，$p \mid G_j \iff p \mid B Q_j$ 且 $p \mid A Q_j + C P_j$。
   - 若 $p = 2$：因 $P_j, Q_j$ 恒为奇数，若 $2 \nmid B$ 则 $2 \nmid B Q_j$；若 $2 \mid B$ 且 $2 \mid C$，由 $\gcd(A,B,C)=1$ 知 $2 \nmid A$，故 $A Q_j + C P_j$ 恒为奇数；若 $2 \mid B,\ 2 \nmid C$，则 $A Q_j + C P_j \equiv A + C \equiv A - C \pmod 2$，故 $2 \mid G_j \iff A \equiv C \pmod 2$。
   - 若 $p \ge 3$ 且 $p \mid C$：由 $\gcd(P_j, Q_j) = 1$ 及 $\gcd(A, B, C) = 1$：若 $p \mid B$ 则 $p \nmid A$，故 $p \mid A Q_j + C P_j \iff p \mid Q_j$；若 $p \nmid B$ 则 $p \mid B Q_j \iff p \mid Q_j$，此时 $p \nmid P_j$ 且 $p \mid C \implies p \mid A Q_j + C P_j$ 自动成立。两种情形均等价于 $p \in \mathcal{Z}_Q$。
   - 若 $p \ge 3$ 且 $p \nmid C$：要使 $p \mid B Q_j$，必要么 $p \mid B$ 要么 $p \mid Q_j$。但若 $p \nmid B$ 则须 $p \mid Q_j$，此时 $p \mid A Q_j + C P_j \implies p \mid C P_j \implies p \mid P_j$，与 $\gcd(P_j,Q_j)=1$ 矛盾！故必 $p \mid B$。此时对任意 $j$ 若 $p \mid Q_j$ 则 $p \nmid C P_j$ 不可能使 $p \mid A Q_j + C P_j$，故必 $p \nmid Q_j$ 且 $-A C^{-1} \equiv P_j Q_j^{-1} \pmod p$。由回文对称 $P_{p-1-j} Q_{p-1-j}^{-1} \equiv P_j Q_j^{-1}$ 及反周期 $P_{j+p} Q_{j+p}^{-1} \equiv -P_j Q_j^{-1} \pmod p$，全部比值落在 $\mathcal{R}_p \cup (-\mathcal{R}_p)$ 中。$\square$

---

### 定理 G2（全部偶分母 $B = 2^a B_{\mathrm{odd}}$ 的普适四分之一周期定理与 $2$-进同余律）

设 $B = 2^a B_{\mathrm{odd}}$（$a \ge 1,\ 2 \nmid B_{\mathrm{odd}}$），置 $S := B^2/2 = 2^{2a-1} B_{\mathrm{odd}}^2$，$D := 2B^2$，并定义对合乘子
$$u := \begin{cases} B^2 + 1, & 4 \mid B \ (a \ge 2), \\ 1 - B^2/2, & B \equiv 2 \pmod 4 \ (a = 1), \end{cases} \qquad u^2 \equiv 1 \pmod{2B^2}.$$
则：
1. **普适 $2$-进提升与邻项不变式**：对全部 $k \ge 0$ 成立 $Q_{2k+1} \equiv Q_{2k} \pmod{64}$ 与 $Q_{2k+1} - Q_{2k} \equiv 64 k^2 \pmod{128}$；且对一切 $r \ge 3$ 与 $k \ge 0$，模 $2^{r+3}$ 的 $2^r$-步转移矩阵满足
   $$U^{(2k, 2^r)} := \prod_{j=2k}^{2k+2^r-1} M(4j+2) \equiv I + 2^r \begin{pmatrix} 1 & 3 - 4k \\ 5 - 4k & -1 \end{pmatrix} \pmod{2^{r+3}}$$
   （特别地，$k=0$ 即 $T_r = U^{(0, 2^r)} \equiv I + 2^r \begin{pmatrix} 1 & 3 \\ 5 & -1 \end{pmatrix} \pmod{2^{r+3}}$）。
2. **全局 Hermite 四分之一周期同余**：对一切 $j \ge 0$，
   $$Q_{j+S} \equiv u\, Q_j \pmod{2B^2}, \qquad P_{j+S} \equiv u\, P_j \pmod{2B},$$
   且对 $B_{\mathrm{odd}}^2$ 成立 $Q_{j+S} \equiv Q_j,\ P_{j+S} \equiv P_j \pmod{B_{\mathrm{odd}}^2}$。
3. **普适窗口四分之一周期**：对目标 $x = A/B - e$（$\gcd(A,B)=1$）及全部满足 $j - 1 > B^2$ 的窗口，均成立 $2 \nmid G_j,\ G_j \mid B_{\mathrm{odd}}^2$，且
   $$G_{j+S} = G_j, \qquad D_{j+S} = D_j, \qquad S_{j+S} = S_j, \qquad b_{j+S} = b_j + G_j^2.$$
   从而其最小窗口周期恒整除 $S = B^2/2$（比模 $2B^2$ 周期缩短至 $1/4$；对多尺度偶分母例如 $B=14$ 仍成立，$S=98,\ b_{j+98}=b_j+G_j^2$）。
4. **普适 $2$-进后缀 $q_0$ 同余律**：记 $M_2 := \min(2^{a+1}, 64)$。对任意 $A/B - e$ 的任意窗口 $j - 1 > B^2$（若 $B_{\mathrm{odd}} \in \langle \mathcal{N}_Q \rangle$ 则自动满足 $G_j = G_{j+1} = 1$；一般情形在 $G_j \equiv G_{j+1} \pmod{M_2}$ 窗口上成立）：
   - 当 $a = 1$（$B \equiv 2 \pmod 4$）：若 $j$ 为偶数则 $q_0(j) \equiv 5 \pmod 8$；若 $j$ 为奇数则 $q_0(j) \equiv 3 \pmod 8$（恒有 $q_0(j) \equiv \pm 3 \pmod 8$）。
   - 当 $a \ge 2$（$4 \mid B$）：若 $j$ 为偶数则 $q_0(j) \equiv 1 \pmod{M_2}$；若 $j$ 为奇数则 $q_0(j) \equiv 7 \pmod 8$（逐一命中模 $M_2$ 下满足 $\equiv 7 \pmod 8$ 的剩余类）。

#### 定理 G2 证明

1. **证明 $Q_{2k+1} \equiv Q_{2k} \pmod{64}$ 与 $Q_{2k+1} - Q_{2k} \equiv 64 k^2 \pmod{128}$**：对 $k$ 归纳。基例 $k=0$: $Q_1 - Q_0 = 0$。设 $Q_{2k-1} \equiv Q_{2k-2} \pmod{64}$（$k \ge 1$），因 $Q_{2k} = (8k-2)Q_{2k-1} + Q_{2k-2} \equiv (8k-1)Q_{2k-1} \pmod{64}$，代入 $Q_{2k+1} - Q_{2k} = (8k+1)Q_{2k} + Q_{2k-1}$ 得
   $$Q_{2k+1} - Q_{2k} \equiv \bigl((8k+1)(8k-1)+1\bigr)Q_{2k-1} = 64k^2 Q_{2k-1} \equiv 0 \pmod{64},$$
   且因 $Q_{2k-1}$ 恒奇，模 $128$ 给出 $Q_{2k+1} - Q_{2k} \equiv 64 k^2 \pmod{128}$。顺带一提，对 $P_n \pmod 4$，由于 $P_n$ 恒奇且 $P_{n+2} = (4n+6)P_{n+1} + P_n$ 中 $2 \mid (4n+6) \implies (4n+6)P_{n+1} \equiv 2 \equiv -2P_n \pmod 4$，故 $P_{n+2} \equiv -P_n \pmod 4$。由 $P_0=1, P_1=3$ 归纳知**对一切 $k \ge 0$，$P_{2k+1} - P_{2k} \equiv 2 \pmod 4$ 且 $P_{2k+2} \equiv P_{2k+1} \pmod 4$**。

2. **证明 $U^{(2k, 2^r)} \pmod{2^{r+3}}$**：先计算 $2$-步块 $A_k := M(8k+6)M(8k+2) = \begin{pmatrix} 13 + 64k(k+1) & 8k+6 \\ 8k+2 & 1 \end{pmatrix}$。因 $k(k+1)$ 恒偶， $A_k \equiv \begin{pmatrix} 13 & 8k+6 \\ 8k+2 & 1 \end{pmatrix} \pmod{128}$。乘出 $U^{(2k, 4)} = A_{k+1} A_k \equiv I + 4\begin{pmatrix} 1 & 7-4k \\ 1-4k & 7 \end{pmatrix} \pmod{64}$（仅 $(0,0),(1,1)$ 含 $+64k^2$）。注意到 $B_k^{(2)} := \begin{pmatrix} 1 & 7-4k \\ 1-4k & 7 \end{pmatrix}$ 满足 $(B_k^{(2)})^2 \equiv 0 \pmod 4$，且 $B_{k+2}^{(2)} - B_k^{(2)} \equiv 8E \pmod{16}$（$E=\begin{pmatrix}0&1\\1&0\end{pmatrix}$），故
   $$U^{(2k, 8)} = U^{(2k+4, 4)} U^{(2k, 4)} \equiv \bigl(I + 4(B_k^{(2)} + 8E)\bigr)(I + 4 B_k^{(2)}) \equiv I + 8\begin{pmatrix} 1 & 3-4k \\ 5-4k & -1 \end{pmatrix} \pmod{64},$$
   此即 $r=3$ 情形。设 $r \ge 3$ 时命题成立，置 $B_k^{(r)} \equiv \begin{pmatrix} 1 & 3-4k \\ 5-4k & -1 \end{pmatrix} \pmod 8$。注意当 $j \mapsto j + 2^r$ 时，每步矩阵 $M(4j+2)$ 改变 $\Delta M = 2^{r+2} E_{11}$（$E_{11}=\begin{pmatrix}1&0\\0&0\end{pmatrix}$），在模 $2^{r+4}$ 下因 $(2^{r+2})^2 = 2^{2r+4} \ge 2^{r+7}$ 仅一阶线性项有贡献：
   $$U^{(j_0+2^r, 2^r)} - U^{(j_0, 2^r)} \equiv 2^{r+2} \sum_{t=0}^{2^r-1} U^{(j_0+t+1, 2^r-t-1)} E_{11} U^{(j_0, t)} \pmod{2^{r+4}}.$$
   模 $4$ 下 $M(4j+2) \equiv M_0 := \begin{pmatrix} 2 & 1 \\ 1 & 0 \end{pmatrix} \pmod 4$，而 $M_0^4 \equiv I \pmod 4$，直接算 $4$ 项和 $\sum_{t=0}^3 M_0^{3-t} E_{11} M_0^t \equiv \begin{pmatrix} 0 & 2 \\ 2 & 0 \end{pmatrix} \pmod 4$。因 $r \ge 3 \implies 2^r = 4 \cdot 2^{r-2}$ 含偶数个（$2^{r-2} \ge 2$）长度 $4$ 块，总和 $\equiv \mathbf{0} \pmod 4$，故 $U^{(2k+2^r, 2^r)} \equiv U^{(2k, 2^r)} \pmod{2^{r+4}}$。最后直算 $(B_k^{(r)})^2 \equiv 0 \pmod 8$，且 $2r \ge r+3$（对 $r \ge 3$）使 $2^{2r}(B_k^{(r)})^2 \equiv 0 \pmod{2^{r+4}}$（对 $r=3$：$2^6\cdot 8 = 2^9 \ge 2^7$；对 $r \ge 4$：$2r+3 \ge r+7$）。故平方得
   $$U^{(2k, 2^{r+1})} \equiv \bigl(I + 2^r B_k^{(r)}\bigr)^2 \equiv I + 2^{r+1} B_k^{(r)} \pmod{2^{r+4}},$$
   完成所有 $r \ge 3$ 归纳（注意到将 $k$ 换为 $k+2^{r-1}$ 不改 $3-4k \pmod 8$）。

3. **证明全局四分之一周期同余**：将模 $2B^2$ 拆成奇部 $B_{\mathrm{odd}}^2$ 与 $2$-部 $2^{2a+1}$。
   - **奇部**：$S = 2^{2a-1} B_{\mathrm{odd}}^2$ 为 $2 B_{\mathrm{odd}}^2$ 的整数倍，由定理 G1(1)（取奇数 $M = B_{\mathrm{odd}}^2$）立得 $Q_{j+S} \equiv Q_j,\ P_{j+S} \equiv P_j \pmod{B_{\mathrm{odd}}^2}$，且显然 $u \equiv 1 \pmod{B_{\mathrm{odd}}^2}$。
   - **$2$-部（$a=1$）**：此时 $2^{2a+1}=8,\ 2^{a+1}=4$，$S = 2 B_{\mathrm{odd}}^2$ 为 $2$ 的奇数倍。对 $j=2k$，由 $A_k \equiv \begin{pmatrix}5&6\\2&1\end{pmatrix} \pmod 8$ 与 $Q_{2k-1} \equiv -Q_{2k} \pmod 8$（因 $Q_{2k} \equiv (8k-1)Q_{2k-1}$），得 $Q_{2k+2} \equiv (5-6)Q_{2k} = -Q_{2k} \pmod 8$；对 $j=2k+1$，由 $U^{(2k+1,2)} \equiv \begin{pmatrix}5&2\\6&1\end{pmatrix} \pmod 8$ 与 $Q_{2k+1} \equiv Q_{2k} \pmod 8$，得 $Q_{2k+3} \equiv (5+2)Q_{2k+1} \equiv -Q_{2k+1} \pmod 8$。连乘 $B_{\mathrm{odd}}^2$（奇数）次即得 $Q_{j+S} \equiv -Q_j \equiv u\, Q_j \pmod 8$。对 $P_j$，已证 $P_{j+2} \equiv -P_j \pmod 4$，连乘 $B_{\mathrm{odd}}^2$ 次即得 $P_{j+S} \equiv -P_j \equiv u\, P_j \pmod 4$。
   - **$2$-部（$a \ge 2$）**：此时 $r := 2a-1 \ge 3$ 且 $r \ge a+1$，而 $S = 2^r B_{\mathrm{odd}}^2$。对偶 $j=2k$，利用 $Q_{2k} - Q_{2k-1} \equiv 2 Q_{2k} \pmod 4$（因 $Q_{2k-1} \equiv -Q_{2k} \pmod 8$）及 $(U^{(2k,2^r)}-I)/2^r \equiv \begin{pmatrix}1&3\\1&3\end{pmatrix} \pmod 4$，第一行给出 $Q_{2k+2^r} - Q_{2k} \equiv 2^r(Q_{2k} - Q_{2k-1}) \equiv 2^{r+1} \equiv 2^{2a} Q_{2k} \pmod{2^{2a+1}}$；对奇 $j=2k+1$，用 $M_0^{-1} \begin{pmatrix}1&3\\1&3\end{pmatrix} M_0 \equiv \begin{pmatrix}1&1\\3&3\end{pmatrix} \pmod 4$ 与 $Q_{2k+1} + Q_{2k} \equiv 2 \pmod 4$，同样给出 $Q_{j+2^r} - Q_j \equiv 2^{2a} Q_j \pmod{2^{2a+1}}$。因 $(1+2^{2a})^{B_{\mathrm{odd}}^2} \equiv 1 + 2^{2a} \equiv u \pmod{2^{2a+1}}$（$B_{\mathrm{odd}}^2$ 为奇），即得 $Q_{j+S} \equiv u\, Q_j \pmod{2^{2a+1}}$。又因 $U^{(j, 2^r)} \equiv I \pmod{2^r}$ 且 $r \ge a+1$，立得 $P_{j+S} \equiv P_j \equiv u\, P_j \pmod{2^{a+1}}$。由 CRT 合并奇部与 $2$-部即完成证明。

4. **证明窗口四分之一周期与 $b_{j+S} = b_j + G_j^2$**：首先对任意 $j$，若奇素数幂 $p^e \mid G_j$，分 $p^v \parallel B$ 情形（$e \ge 2v+1 \implies p^{v+1} \mid Q_j$ 且 $p^{v+1} \mid A Q_j - B P_j$，结合 $\gcd(A,B)=1$ 与 $\gcd(P_j,Q_j)=1$ 必导矛盾）可证 $G_j \mid B^2$；而 $A Q_j - B P_j$ 恒奇，故 $2 \nmid G_j$ 且 $G_j \mid B_{\mathrm{odd}}^2$。由于 $(P_{j+S}, Q_{j+S}) \equiv (P_j, Q_j) \pmod{B_{\mathrm{odd}}^2}$，立得 $G_{j+S} = G_j$ 与 $D_{j+S} = D_j$。再由 $P_{j+S} \equiv u P_j \pmod{2B}$ 乘以 $B$ 得 $B P_{j+S} \equiv u B P_j \pmod{2B^2}$，结合 $Q_{j+S} \equiv u Q_j \pmod{2B^2}$ 得
   $$G_j \mathbf{v}_{j+S} \equiv u\, G_j \mathbf{v}_j \pmod{2B^2} \implies \mathbf{v}_{j+S} \equiv u\,\mathbf{v}_j \pmod{\frac{2B^2}{G_j}}.$$
   因 $D_j = \frac{2B^2}{G_j G_{j+1}}$ 同除 $\frac{2B^2}{G_j}$ 与 $\frac{2B^2}{G_{j+1}}$，将 $\mathbf{v}_{j+1} \equiv q_0(j)\mathbf{v}_j \pmod{D_j}$ 与其对比得 $q_0(j+S)\mathbf{v}_{j+S} \equiv q_0(j)\mathbf{v}_{j+S} \pmod{D_j}$。因 $\gcd(p_{k(j+S)}, q_{k(j+S)}) = 1$ 可消去 $\mathbf{v}_{j+S}$，故 $q_0(j+S) = q_0(j)$。由于偶数长连分数展开 $[S_j] = D_j / q_0(j) > 1$（$8 \mid D_j$）唯一，从而 $S_{j+S} = S_j$。最后，将递推第二分量 $q_{k(j+1)}/q_{k(j)} = b_j D_j + q_0(j) + D_j \frac{q_{k(j)-1}}{q_{k(j)}}$ 与 $\frac{G_j}{G_{j+1}}\bigl(4j+2+\frac{Q_{j-1}}{Q_j}\bigr)$ 联立同除 $D_j$，得
   $$b_j + \frac{q_0(j)}{D_j} + \frac{q_{k(j)-1}}{q_{k(j)}} = \frac{G_j^2}{2B^2}\left(4j + 2 + \frac{Q_{j-1}}{Q_j}\right).$$
   将 $j+S$ 式减 $j$ 式（注意 $\frac{G_j^2}{2B^2}(4S) = \frac{G_j^2}{2B^2}(2B^2) = G_j^2$ 且 $q_0(j+S)/D_{j+S} = q_0(j)/D_j$ 完全相消），得
   $$(b_{j+S} - b_j - G_j^2) + \left(\frac{q_{k(j+S)-1}}{q_{k(j+S)}} - \frac{q_{k(j)-1}}{q_{k(j)}}\right) = \frac{G_j^2}{2B^2}\left(\frac{Q_{j+S-1}}{Q_{j+S}} - \frac{Q_{j-1}}{Q_j}\right).$$
   对 $j - 1 > B^2$：右侧满足 $0 < \frac{Q_{j-1}}{Q_j} < \frac{1}{4j-2} < \frac{1}{4B^2+2}$ 且 $\frac{G_j^2}{2B^2} \le \frac{B^2}{2}$，故右侧绝对值 $< \frac{1}{8}$；左侧利用 $S_{j+S-1} = S_{j-1}$ 与反转连分数 $\frac{q_{k(j)-1}}{q_{k(j)}} = \frac{U_0(j-1) Y + V_0(j-1)}{D_{j-1} Y + q_0(j-1)}$（$Y \ge 1,\ D_{j-1} \ge 8$），二者均落在长度为 $\frac{1}{D_{j-1}(D_{j-1}+q_0)} \le \frac{1}{72}$ 的同一区间内！于是整数 $b_{j+S} - b_j - G_j^2$ 的绝对值严格 $< \frac{1}{72} + \frac{1}{8} = \frac{5}{36} < 1$，故必 $b_{j+S} = b_j + G_j^2$。

5. **证明 $2$-进后缀 $q_0$ 同余律**：在 $G_j \equiv G_{j+1} \pmod{M_2}$ 下，由 $\mathbf{v}_{j+1} \equiv q_0(j)\mathbf{v}_j \pmod{2^{2a+1}}$ 的第二分量同除 $B = 2^a B_{\mathrm{odd}}$ 得 $q_0(j) \equiv Q_{j+1} Q_j^{-1} \pmod{M_2}$。若 $a \ge 2$：$j=2k$ 时 $Q_{2k+1} \equiv Q_{2k} \pmod{64} \implies q_0(2k) \equiv 1 \pmod{M_2}$；$j=2k+1$ 时 $Q_{2k+2} \equiv (8k+7)Q_{2k+1} \pmod{64} \implies q_0(2k+1) \equiv 7 \pmod 8$。若 $a = 1$（$2 \parallel B$）：对偶 $j=2k$，由上得 $q_0 = 1+4\varepsilon \pmod 8$，代入第一分量 $\pmod 8$ 并用 $Q_{2k+1}\equiv Q_{2k} \pmod{64}$ 与 $2 \parallel (P_{2k+1}-P_{2k})$ 得 $-B(P_{2k+1}-P_{2k}) \equiv 4\varepsilon \pmod 8 \implies \varepsilon = 1 \implies q_0(2k) \equiv 5 \pmod 8$；对奇 $j=2k+1$，写 $q_0 = 3+4\varepsilon \pmod 8$，利用 $Q_{2k+2}\equiv -Q_{2k+1} \equiv 3Q_{2k+1}+4 \pmod 8$、$P_{2k+2}\equiv P_{2k+1}\pmod 4$ 与 $2\parallel B \implies 2B P_{2k+1} \equiv 4 \pmod 8$ 得 $4\varepsilon \equiv 0 \pmod 8 \implies q_0(2k+1) \equiv 3 \pmod 8$。$\square$

---

### 定理 G3（分歧素数 $5$ 赋值刚性、普适 Case 2 坍缩与 $O(B^{-4})$ 精确下包络）

1. **分歧 $5$ 赋值刚性**：对任意本原元 $\xi = p\varphi + q \in \mathbb{Z}[\varphi]$（$\gcd(p,q)=1$），$4 N(\xi) = (2q+p)^2 - 5p^2$ 满足 $v_5(N(\xi)) \le 1$。因而在任意既约端点 $u = p_1/q_1,\ v = -p_2/q_2$（$D = p_1 q_2 + p_2 q_1 \ge 1$）与 $GL_2(\mathbb{Z})$-伴随 $\eta = (a\varphi+b)/(c\varphi+d)$ 下，Case 1/2 极限值 $\frac{2|\xi_1\sigma(\xi_2)|}{D\sqrt5} = \bigl|\frac{M_{u,v}}{D\sqrt5}\pm 1\bigr|$ 满足的范数等式
   $$M_{u,v}^2 - 5 D^2 = 4 N(\xi_1) N(\xi_2)$$
   必服从 $v_5(M_{u,v}^2 - 5 D^2) \le 2$。特别地，**只要 $5 \mid D$（等价于在 $D=2d$ 中 $5 \mid d$），必有 $25 \nmid M_{u,v}$（且对 $M_{u,0}=2m$，$25 \nmid m$）**；例如 $B = 5, 10, 15, \dots$ 中所有形如 $25k$ 的中心整数候选项皆被绝对禁除。
2. **普适 Case 2 坍缩（$D_{\max} \ge 14$）**：对任意无 $D_j=1$ 窗的周期仿射窗口模型（包含全体 $x = A/B - e,\ B \ge 3,\ \gcd(A,B)=1$），记最大尺度 $D_{\max} = 2 d_{\max}$（对 $A/B-e$ 有 $d_{\max} = B^2$）。若 $D_{\max} \ge 14$（即 $d_{\max} \ge 7$），则在 `lem:general-case2-criterion` 的全部分支中：
   - 分支 (a) $Q_n=1,\ \theta_n=\varphi-1$ 折算为前窗 $j-1$ 的 Case 1 值；
   - 其余全部 $7$ 条非-$Q_1$ Case 2 分支满足
     $$\min\bigl\{(a)_{\mathrm{mid}}, (a)_{>}, (b)_1, (b)_{\mathrm{mid}}, (b)_{>}, (c)_1, (c)_{\ge 2}\bigr\} \ge \min\!\left(\frac{2}{\sqrt5}(2-\varphi),\ \frac{\sqrt5}{d_{\max}}\right) = \frac{\sqrt5}{d_{\max}},$$
     因 $\frac{2}{\sqrt5}(2-\varphi) > \frac{\sqrt5}{7} \iff 256 > 245$！故只要在 Case 1 中存在（极值及第二）极限点 $< \sqrt{5}/d_{\max}$，全轨道 Case 2 除前窗降维外被**自动关闭**。
3. **普适 $O(T^{-2}) / O(B^{-4})$ 精确下包络**：对任意周期有限尺度窗模型（$D_j \le T$ 且无 $D_j=1$ 窗；或任意 $B \ge 3$ 的 $x = A/B - e$ 取 $T = 2B^2$），恒成立
   $$c_\varphi(x) > \frac{2}{5 T^2 + T \sqrt{5}}, \qquad c_\varphi(A/B - e) > \frac{1}{10 B^4 + B^2 \sqrt{5}} \quad (\forall B \ge 3,\ \gcd(A,B)=1).$$

#### 定理 G3 证明

1. 若 $5 \mid N(\xi)$，由 $4N(\xi) = (2q+p)^2 - 5p^2$ 知 $5 \mid 2q+p$；而 $\gcd(p,q)=1$ 排除 $5 \mid p$（否则 $5 \mid q$），故 $25 \mid (2q+p)^2$ 且 $25 \nmid 5p^2$，即 $v_5(N(\xi)) = 1$。由端点参数化公式（与 `lem:general-endpoint-rigidity` 及 `verify_golden_general_b.py` L479–483 一致）：$\xi_1 = (p_1 c - q_1 a)\varphi + (p_1 d - q_1 b)$ 与 $\xi_2 = (q_2 a + p_2 c)\varphi + (q_2 b + p_2 d)$ 均由本原向量经 $GL_2(\mathbb{Z})$ 变换得到，故均本原，于是 $v_5(4 N(\xi_1) N(\xi_2)) = v_5(N(\xi_1)) + v_5(N(\xi_2)) \le 2$。由 $(2\xi_1)(2\sigma(\xi_2))$ 中 $\sqrt{5}$ 的系数为 $2\det\begin{pmatrix}x_1&y_1\\x_2&y_2\end{pmatrix} = \pm 2 D$ 知 $2\xi_1\sigma(\xi_2) = M_{u,v} \pm D\sqrt{5}$，取范数得 $M_{u,v}^2 - 5D^2 = 4N(\xi_1)N(\xi_2)$。当 $5 \mid D$ 时 $v_5(5D^2) \ge 3$，若 $25 \mid M_{u,v}$ 则 $v_5(M_{u,v}^2 - 5D^2) \ge 3$ 矛盾，故 $25 \nmid M_{u,v}$。
2. 对 `lem:general-case2-criterion`（论文一）中全部 $7$ 条非-$Q_1$ 下界：当 $D_j \ge 2$ 时 $r_1, r_2 \in (0, 1)$ 且 $r_1 \in [1/D_j, 1 - 1/D_j] \subseteq [1/D_{\max}, 1 - 1/D_{\max}]$，故
   - $(a)_{\mathrm{mid}} > \frac{2}{\sqrt5}(2-\varphi)$，$(a)_{>} > \frac{2}{\sqrt5}(\varphi-1) > \frac{2}{\sqrt5}(2-\varphi)$，$(b)_1 > \frac{2}{\sqrt5}(2+\varphi)$，$(b)_{\mathrm{mid}} > \frac{2}{\sqrt5}(\varphi-1)$，$(b)_{>} > \frac{2}{\sqrt5}(2-\varphi)$，$(c)_1 > 2\sqrt{5}(2-\varphi)$，而 $(c)_{\ge 2} = 2\sqrt{5}\min(r_{1,\min}, 1-r_{1,\max}) \ge \frac{2\sqrt{5}}{D_{\max}} = \frac{\sqrt5}{d_{\max}}$。
   由 $21 - 7\sqrt{5} > 5 \iff 16 > 7\sqrt{5} \iff 256 > 245$，对一切 $d_{\max} \ge 7$ 均有 $\frac{2}{\sqrt5}(2-\varphi) > \frac{\sqrt5}{7} \ge \frac{\sqrt5}{d_{\max}}$。对 $A/B-e$，因 $G_j$ 恒奇且 $G_j \mid B^2$，$D_j = \frac{2B^2}{G_j G_{j+1}}$ 恒为偶数，故绝无 $D_j=1$ 窗；且 $B \ge 3 \implies d_{\max} = B^2 \ge 9 \ge 7$。
3. 任意 Case 1 候选极限点具有形式 $\lambda = \frac{|M - D\sqrt{5}|}{D\sqrt{5}}$（$1 \le D \le T$），其中 $M^2 - 5 D^2 = 4 N(\xi_1) N(\xi_2)$ 为非零整数且被 $4$ 整除，故 $k := |M^2 - 5D^2| \ge 4$。利用恒等式与对称性（$M^2 = 5D^2 - k$ 时分子相同而分母更小）：
   $$\lambda \ge \frac{\sqrt{5D^2 + 4} - D\sqrt{5}}{D\sqrt{5}} = \frac{4}{D\sqrt{5}\bigl(\sqrt{5D^2 + 4} + D\sqrt{5}\bigr)}.$$
   对一切 $D \ge 1$，平方可证 $\sqrt{5D^2 + 4} < D\sqrt{5} + 2$（等价于 $0 < 4D\sqrt{5}$），故
   $$\lambda > \frac{4}{D\sqrt{5}(2D\sqrt{5} + 2)} = \frac{2}{5D^2 + D\sqrt{5}} \ge \frac{2}{5T^2 + T\sqrt{5}}.$$
   当 $D_{\max} \ge 14$ 时，Case 2 全分支下界 $\frac{\sqrt5}{d_{\max}} = \frac{2\sqrt5}{D_{\max}} \ge \frac{2\sqrt5}{T} > \frac{2}{5T^2+T\sqrt5}$。取 $T = 2B^2$ 即得 $c_\varphi(A/B - e) > \frac{1}{10B^4 + B^2\sqrt5}$。$\square$

---

## 3. $B = 7, 8, 9, 10, 11, 12$ 全剩余类完整谱定理与 2500 位实证核对

下面统一记号：对给定分母 $B$ 与允许分子类 $A$（$\gcd(A,B)=1$），以 $c_\varphi^{(B)}$ 与 $c_{\mathrm{sec}}^{(B)}$ 表示定理给出的精确最小与第二极限点；记 $4\tau$-反演对每个 $q_0$ 给出的前缀表为 $\mathrm{ext}[q_0]$（其对应的轨道族为 $[a_0;\dots,b_j, \mathrm{pref}, \overline{1}]$）。全部 $34$ 个剩余类均经 `.venv\Scripts\python.exe` 下 `2500` 位 `mpmath` 验证通过（[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L11-L131)）。

---

### 3.1 $B = 7$ 全剩余类定理（$A \equiv 1, 2, 3, 4, 5, 6 \pmod 7$）

**定理（$B=7$ 全类精确谱）**：对**一切** $7 \nmid A$，记 $x = A/7 - e$：
1. **统一三尺度窗口与 $D_j=2$ 非优机理**：自 $j \ge 50$ 起，$(b_j, S_j, G_j, D_j)$ 具有最小周期 $T = 98$ 且 $b_{j+98} = b_j + 4 G_j^2$。在每一个 $98$-周期内，**全部 $6$ 个剩余类一致满足**：
   - 存在 **4** 个隔离指标满足 $49 \mid Q_j$（$j \equiv 18, 30, 67, 79 \pmod{98}$），此处恒有 $G_j = 7$；
   - 在 $24$ 个满足 $7 \parallel Q_j$ 的指标上，残差 $P_j (Q_j/7)^{-1} \bmod 7$ 对每个非零剩余类 $1,2,3,4,5,6 \pmod 7$ **精确等频命中 $4$ 次**，从而不论 $A \bmod 7$ 取何值，恰有 $4$ 个隔离指标取 $G_j = 49$、$24$ 个指标取 $G_j = 7$、$70$ 个指标取 $G_j = 1$；
   - 因而窗口尺度分布对**全部 $6$ 类**恒为 $\{2: 8,\ 14: 48,\ 98: 42\}$！且在全部 $8$ 个 $D_j = 2$ 窗口处均有 $S_j = [1, 1]$，故 $D_j = 2$ 确实产生极限点 $1 - \frac{2}{\sqrt5} \approx 0.10557281$（$m=2$）与 $\frac{4}{\sqrt5} - 1 \approx 0.78885438$（$m=4$），但两者均远大于 $D_j=98$ 与 $D_j=14$ 处的更小极限点，故 **$D_j = 2$ 从不决定 $c_\varphi(A/7-e)$**。
2. **共享 $21$ 个有限后缀（与 $A \bmod 7$ 无关）**：全部 $6$ 类共享完全相同的 $21$ 个偶长后缀（按 $D_j$ 分列，`[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L15-L17)` 逐一核实 $\Delta(S)>0$）：
   - $D=2$（$1$ 个，$\min\Delta = 1/2$）：`1:[1, 1]`；
   - $D=14$（$6$ 个，$\min\Delta = 1/182$）：`1:[13,1], 3:[4,1,1,1], 5:[2,1,3,1], 9:[1,1,1,4], 11:[1,3,1,2], 13:[1,13]`；
   - $D=98$（$14$ 个，恰好取遍 $\{q_0 \in (\mathbb{Z}/98\mathbb{Z})^\times : q_0 \equiv \pm 1 \pmod{14}\}$ 且 $\min\Delta = 1/13345$）：`1, 13, 15, 27, 29, 41, 43, 55, 57, 69, 71, 83, 85, 97`。
3. **Case 1 + Case 2 精确谱常值**：
   $$c_\varphi(A/7 - e) = \frac{110}{49\sqrt5} - 1 \approx 0.0039488878570484351224861369813893302,$$
   $$c_{\mathrm{sec}}^{(7)} = 1 - \frac{108}{49\sqrt5} \approx 0.014304728285806990970649974600090476.$$
   - 极值轨道族（$m = 110$，$4$ 族）：$q_0=27: [[3]],\ q_0=29: [[3,2]],\ q_0=69: [[1,2,2]],\ q_0=71: [[1,2]]$。
   - 第二极限点（$m = 108$，$4$ 族）：$q_0=41: [[2,2]],\ q_0=43: [[2,3]],\ q_0=55: [[1,1,3]],\ q_0=57: [[1,1,2]]$。
   - $D=98$ 处最近偶数 $m = 112$ 被惰性素数 $7 \mid 49$ 禁除（`lem:general-endpoint-rigidity`）；$D=14$ 处最小 Case 1 值为 $\frac{16}{7\sqrt5}-1 \approx 0.022202504 > c_{\mathrm{sec}}^{(7)}$；Case 2 全部非-$Q_1$ 分支均 $\ge \frac{\sqrt5}{49} \approx 0.04563404 > c_{\mathrm{sec}}^{(7)}$（实测 $Q_1 \ge 0.022202504$）。

**证明要点**：除上述 $7 \parallel Q_j$ 等频分配之外，需证为何 $D=98$（即 $j \bmod 7 \in \{5,6,0\}$）上 $q_0(j) \bmod 98$ 对全部 $7 \nmid A$ 均取遍 $\{q_0 \equiv \pm 1 \pmod{14}\}$。固定 $j_0 \bmod 14$ 满足 $j_0 \bmod 7 \in \{5,6,0\}$，沿步长 $14$ 考察 $Q_{j+14} = Q_j + 7\alpha_j \pmod{49}$ 与 $P_{j+14} = P_j + 7\beta_j \pmod{49}$（由 $U^{(0,14)} \equiv I \pmod 7$）。对比率 $q_0(j) \equiv \frac{A Q_{j+1} - 7 P_{j+1}}{A Q_j - 7 P_j} \pmod{49}$，其步长 $14$ 乘法偏移为
$$\frac{q_0(j+14)}{q_0(j)} \equiv 1 + 7\bigl(\alpha_{j+1} Q_{j+1}^{-1} - \alpha_j Q_j^{-1}\bigr) \pmod{49},$$
其中 **$A$ 在 $O(7)$ 项上彻底消去**（因分子分母 $7 P$ 项对 $O(7)$ 比率贡献为 $O(49)\equiv 0$）！又 $q_0(j) \bmod 7 \equiv Q_{j+1} Q_j^{-1} \bmod 7 \in \{\pm 1\}$ 且 $q_0(j)$ 恒奇，故对全部 $7 \nmid A$ 均生成同一模 $98$ 陪集 $\{q_0 \equiv \pm 1 \pmod{14}\}$。Case 1（$4\tau$-反演对 $m=112$ 为空、对 $m=110$ 得 $4$ 族、对 $m=108$ 得 $4$ 族）及 Case 2（由定理 G3(2) $d_{\max}=49 \ge 7$）全线闭合。$\square$

- **2500 位 `mpmath` 实测**（`29/7..34/7 - e` 各 $210$ 窗，$j=50..259$，见 [verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L19-L30)）：
  `max_dev_ext <= 0.0001968`，`max_dev_sec <= 0.0005791`；每类扫描 `14856..15239` 个非极值点均满足 `min_non_ext >= 0.013835 > 0.01`，排除 $c_{\mathrm{sec}}$ 族后 `min_non_ext_sec >= 0.016107 > 0.014`。

---

### 3.2 $B = 8$ 全奇数类定理（$A \equiv 1, 3, 5, 7 \pmod 8$）

**定理（$B=8$ 全奇数类精确谱）**：对**一切奇数 $A$**，记 $x = A/8 - e$：
1. **单尺度与四分之一周期**：由定理 G1(2)（$2 \in \mathcal{N}_Q$）与定理 G2（$a=3,\ S=32$），对一切 $j \ge 65$ 成立 $G_j \equiv 1,\ D_j \equiv 128$（$d=64$），最小周期 $S = 32$ 且 $b_{j+32} = b_j + 1$。全周期共有 $18$ 个不同后缀，按 $A \bmod 4$ 分为两组（各自共享完全相同的 $18$ 个后缀且 $\min\Delta > 0$，[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L37-L41)）：
   - 两组共享全部 $16$ 个满足 $q_0 \equiv 7 \pmod 8$ 的奇数位置后缀（$\{7,15,23,31,39,47,55,63,71,79,87,95,103,111,119,127\}$）；
   - 偶数位置（必有 $q_0 \equiv 1 \pmod{16}$）：当 **$A \equiv 1 \pmod 4$**（$A \equiv 1, 5 \pmod 8$）时为 **$\{49, 113\}$**；当 **$A \equiv 3 \pmod 4$**（$A \equiv 3, 7 \pmod 8$）时为 **$\{17, 81\}$**。
2. **Case 1 + Case 2 精确谱常值**：两组具有完全相同的精确最小与第二极限点：
   $$c_\varphi(A/8 - e) = 1 - \frac{143}{64\sqrt5} \approx 0.00075712255478147941715051678571093229,$$
   $$c_{\mathrm{sec}}^{(8)} = \frac{145}{64\sqrt5} - 1 \approx 0.013218302304592206185406818643859544.$$
   - 极值轨道族（$m = 143$，每组各 $3$ 族）：
     - $A \equiv 1 \pmod 4$：$q_0=47: [[2,1,2]],\ q_0=49: [[2]],\ q_0=79: [[]]$；
     - $A \equiv 3 \pmod 4$：$q_0=47: [[2,1,2]],\ q_0=79: [[]],\ q_0=81: [[1,1,1,2]]$。
   - 第二极限点（$m = 145$，每组各 $3$ 族）：
     - $A \equiv 1 \pmod 4$：$q_0=47: [[2]],\ q_0=49: [[2,1,1,1,1,2]],\ q_0=79: [[1,1,1,1,1,1,2]]$；
     - $A \equiv 3 \pmod 4$：$q_0=47: [[2]],\ q_0=79: [[1,1,1,1,1,1,2]],\ q_0=81: [[]]$。
   - Case 1 最近其余奇数 $m = 141$（$1 - \frac{141}{64\sqrt5} \approx 0.01472 > c_{\mathrm{sec}}^{(8)}$）在全部 $18$ 后缀上 $4\tau$-反演为空；Case 2 中除自反边界 $(128, 79/128)$ 落回 $c_{\mathrm{sec}}^{(8)}$ 外，所有非排除 $Q_1 \ge c_{\mathrm{sec}}^{(8)}$，全部 $7$ 条非-$Q_1$ 分支 $\ge \frac{\sqrt5}{64} \approx 0.034938562 > c_{\mathrm{sec}}^{(8)}$。

**证明要点（$A \bmod 4$ 分组机理）**：在偶数下标 $j=2k$，由定理 G2 中 $Q_{2k+1} = Q_{2k} + 64 k^2 \pmod{128}$ 得
$$q_0(2k) \equiv \frac{A(Q_{2k}+64 k^2) - 8 P_{2k+1}}{A Q_{2k} - 8 P_{2k}} = 1 + \frac{64 A k^2 - 8(P_{2k+1} - P_{2k})}{A Q_{2k} - 8 P_{2k}} \pmod{128}.$$
因 $2 \parallel (P_{2k+1}-P_{2k})$ 故 $16 \parallel 8(P_{2k+1}-P_{2k})$：将 $A \mapsto A+4$ 仅把分母改 $+4 Q_{2k}$，乘以 $16$ 后恰好产生 $+64 \pmod{128}$，而 $64 A k^2 \pmod{128}$ 不变，故 $A \mapsto A+4$ 仅在 $\{49, 113\}$（或 $\{17, 81\}$）内部对换；而 $A \mapsto A+2$ 在分母上引起 $+32 \pmod{128}$ 平移，将 $\{49,113\} \leftrightarrow \{17,81\}$ 互相映照！其余由 $4\tau$-反演与定理 G3(2)（$d=64$）完全闭合。$\square$

- **2500 位 `mpmath` 实测**（`33/8, 35/8, 37/8, 39/8 - e` 各 $225$ 窗，$j=65..289$，[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L39-L48)）：
  `max_dev_ext <= 0.0002181`，`max_dev_sec <= 0.003678`；每类 `10518` 点扫描 `min_non_ext >= 0.009540 > 0.008`，`min_non_ext_sec >= 0.028176 > 0.012`。

---

### 3.3 $B = 9$ 全 $3 \nmid A$ 类定理（$A \equiv 1, 2, 4, 5, 7, 8 \pmod 9$）

**定理（$B=9$ 全互素类精确谱）**：对**一切 $3 \nmid A$**，记 $x = A/9 - e$：
1. 由定理 G1(2)（$3 \in \mathcal{N}_Q$）与奇整数周期（$M = 81$），自 $j \ge 82$ 起恒有 $G_j \equiv 1,\ D_j \equiv 162$（$d=81$），最小周期 $T = 162$ 且 $b_{j+162} = b_j + 4$。全部 $6$ 个剩余类一致饱和 $(\mathbb{Z}/162\mathbb{Z})^\times$ 全部 $\varphi(162) = 54$ 个偶长后缀（$\min\Delta = 1/44640$，[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L54)）。
2. 因 $d = 81$ 为奇，$m$ 必为偶数（`lem:norm-parity-rigidity`）。最接近 $81\sqrt{5} \approx 181.12151$ 的偶数 $m = 180$ 被惰性素数 $3 \mid 81$ 绝对禁除（`lem:general-endpoint-rigidity`）。取次近偶数 $m = 182$ 与 $m = 184$ 得：
   $$c_\varphi(A/9 - e) = \frac{182}{81\sqrt5} - 1 \approx 0.0048503009999054932011595252076352465,$$
   $$c_{\mathrm{sec}}^{(9)} = \frac{184}{81\sqrt5} - 1 \approx 0.015892611999904454664908530979147722.$$
   - 极值轨道族（$m = 182$，$8$ 族）：$35:[[4]],\ 37:[[4,2]],\ 61:[[2]],\ 77:[[2,9]],\ 85:[[1,1,9]],\ 101:[[]],\ 125:[[1,3,2]],\ 127:[[1,3]]$。
   - 第二极限点（$m = 184$，$4$ 族）：$11:[[14,1,2]],\ 59:[[2]],\ 103:[[]],\ 151:[[1,13,1,2]]$。
   - Case 1 其余候选 $m = 178$ 给 $1 - \frac{178}{81\sqrt5} \approx 0.017234 > c_{\mathrm{sec}}^{(9)}$；Case 2 中 $Q_1(162, 101/162) = c_\varphi$ 对应极值本身，其余全非排除 $Q_1 \ge c_{\mathrm{sec}}^{(9)}$，全非-$Q_1$ 分支 $\ge \frac{\sqrt5}{81} \approx 0.027605777 > c_{\mathrm{sec}}^{(9)}$（定理 G3(2)）。$\square$

- **2500 位 `mpmath` 实测**（`37/9..44/9 - e` 各 $238$ 窗，$j=82..319$，[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L56-L67)）：
  `max_dev_ext <= 0.002774`，`max_dev_sec <= 0.009092`；各 `18346..19090` 点扫描 `min_non_ext >= 0.010472 > 0.008`，`min_non_ext_sec >= 0.011380 > 0.01`。

---

### 3.4 $B = 10$ 全互素类定理（$A \equiv 1, 3, 7, 9 \pmod{10}$）

**定理（$B=10$ 全互素类精确谱）**：对**一切 $\gcd(A,10)=1$**，记 $x = A/10 - e$：
1. 由定理 G1(2)（$2,5 \in \mathcal{N}_Q$）与定理 G2（$a=1,\ S=50$），自 $j \ge 101$ 起恒有 $G_j \equiv 1,\ D_j \equiv 200$（$d=100$），最小周期 $S = 50$ 且 $b_{j+50} = b_j + 1$。全部 $4$ 个互素剩余类一致饱和 $\{q_0 \in (\mathbb{Z}/200\mathbb{Z})^\times : q_0 \equiv \pm 3 \pmod 8\}$ 全 $40$ 个偶长后缀（$\min\Delta = 1/62083$，[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L73)）。
2. 因 $d = 100$ 为偶，$m$ 必为奇数。最接近 $100\sqrt{5} \approx 223.60680$ 的奇数 **$m = 225$ 被定理 G3(1)（分歧 $5$ 赋值刚性）绝对禁除**（因 $5 \mid 100$ 且 $25 \mid 225$）。依次取次近奇数 $m = 223$ 与 $m = 221$ 得：
   $$c_\varphi(A/10 - e) = 1 - \frac{223}{100\sqrt5} \approx 0.002713682035093795401508543745850799,$$
   $$c_{\mathrm{sec}}^{(10)} = 1 - \frac{221}{100\sqrt5} \approx 0.011657953945092954187145238420775904.$$
   - 极值轨道族（$m = 223$，$4$ 族）：$13:[[15,2]],\ 77:[[2]],\ 123:[[]],\ 187:[[1,14,2]]$。
   - 第二极限点（$m = 221$，$4$ 族）：$59:[[3,2]],\ 61:[[3,3]],\ 139:[[1,2,3]],\ 141:[[1,2,2]]$。
   - Case 1 其余奇数 $m = 227$ 给 $\frac{227}{100\sqrt5} - 1 \approx 0.015175 > c_{\mathrm{sec}}^{(10)}$；Case 2 排除对应极值的 $(200, 123/200)$ 后，其余 $Q_1 \ge 0.02954649777$，全部非-$Q_1$ 分支 $\ge \frac{\sqrt5}{100} \approx 0.02236068 > c_{\mathrm{sec}}^{(10)}$。$\square$

- **2500 位 `mpmath` 实测**（`41/10, 43/10, 47/10, 49/10 - e` 各 $199$ 窗，$j=101..299$，[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L75-L82)）：
  `max_dev_ext <= 0.001206`，`max_dev_sec <= 0.0003587`；每类 `15868` 点扫描 `min_non_ext >= 0.011304 > 0.008`，`min_non_ext_sec >= 0.014614 > 0.011`。

---

### 3.5 $B = 11$ 全 $11 \nmid A$ 类定理（$A \equiv 1, \dots, 10 \pmod{11}$）

**定理（$B=11$ 全类精确多尺度谱）**：对**一切** $11 \nmid A$，记 $x = A/11 - e$：
1. 因 $11 \in \mathcal{Z}_Q$ 且由定理 G1(1)（取 $M = 121$），自 $j \ge 122$ 起最小周期为 $T = 242$（$b_{j+242} = b_j + 4 G_j^2$）。全部 $10$ 个剩余类具有完全相同的三尺度分布 $\{2: 8,\ 22: 80,\ 242: 154\}$ 及相同的 $55$ 个偶长后缀（$D=2$ $1$ 个；$D=22$ $10$ 个 $\min\Delta=1/608$；$D=242$ $44$ 个即 $\{q_0 \in (\mathbb{Z}/242\mathbb{Z})^\times : q_0 \bmod 22 \in \{1,7,19,21\}\}$，$\min\Delta=1/93041$，[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L88-L90)）。
2. 在小尺度上，$D=2$ 给出 $1 - 2/\sqrt{5} \approx 0.10557$，$D=22$（$d=11$）最小 Case 1 值为 $1 - \frac{24}{11\sqrt5} \approx 0.024261$，均远大于主尺度 $D=242$（$d=121$）。在 $D=242$ 处（$m$ 必为偶）：
   $$c_\varphi(A/11 - e) = 1 - \frac{270}{121\sqrt5} \approx 0.0020853654133169949909472883348023412,$$
   $$c_{\mathrm{sec}}^{(11)} = \frac{272}{121\sqrt5} - 1 \approx 0.0053065948428806568980086576775324563.$$
   - 极值轨道族（$m = 270$，$4$ 族）：$65:[[3,1,2]],\ 67:[[3]],\ 175:[[1,2]],\ 177:[[1,2,1,2]]$。
   - 第二极限点（$m = 272$，$6$ 族）：$43:[[5]],\ 45:[[5,2]],\ 117:[[2,14]],\ 151:[[]],\ 197:[[1,4,2]],\ 199:[[1,4]]$。
   - Case 2 无需排除任何 $r_2$：全 $Q_1 \ge 0.00947732567 > c_{\mathrm{sec}}^{(11)}$，全非-$Q_1$ 分支 $\ge \frac{\sqrt5}{121} \approx 0.018479901 > c_{\mathrm{sec}}^{(11)}$（[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L91)）。$\square$

- **2500 位 `mpmath` 实测**（`45/11..54/11 - e` 各 $258$ 窗，$j=122..379$，[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L92-L111)）：
  `max_dev_ext <= 0.0004369`，`max_dev_sec <= 0.00516`（注：$T=242$ 时 $j \le 379$ 仅约 $1.57$ 个周期，$b_j$ 仍较小；例如 `47/11 - e` 在 $j=359$ 处 $b_{359}=5$ 时 $q_0=151$ 的 $c_{\mathrm{sec}}$ 族 `[]` 有限项误差为 `0.0033059868`，随 $b_{359+242t}=5+4t \to \infty$ 渐近收敛至 `0.00530659`）；跨全 $10$ 类 `17118..18124` 点扫描均满足 `min_non_ext >= 0.003103 > 0.003 > c_min^(11)`，且同时排除 $c_{\min}, c_{\mathrm{sec}}$ 族后 **`min_non_ext_sec >= 0.005579 > 0.0055 > c_sec^(11)`**。

---

### 3.6 $B = 12$ 全互素类定理（$A \equiv 1, 5, 7, 11 \pmod{12}$）

**定理（$B=12$ 全互素类精确谱）**：对**一切 $\gcd(A,12)=1$**，记 $x = A/12 - e$：
1. 由定理 G1(2)（$2,3 \in \mathcal{N}_Q$）与定理 G2（$a=2,\ S=72$），自 $j \ge 145$ 起恒有 $G_j \equiv 1,\ D_j \equiv 288$（$d=144$），最小周期 $S = 72$ 且 $b_{j+72} = b_j + 1$。全部 $4$ 类按 $A \bmod 4$ 分为两组，每组各含 $30$ 个偶长后缀（共享全部 $24$ 个 $q_0 \equiv 7 \pmod 8$ 后缀；而在 $6$ 个 $q_0 \equiv 1 \pmod 8$ 偶数位置上，$A \equiv 1,5 \pmod{12}$ 取 $\{41,73,137,169,233,265\} \equiv 9 \pmod{32}$，$A \equiv 7,11 \pmod{12}$ 取 $\{25,89,121,185,217,281\} \equiv 25 \pmod{32}$，[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L118,L124)）。
2. 因 $d = 144$ 为偶，$m$ 必为奇。最接近 $144\sqrt{5} \approx 321.99379$ 的奇数 $m = 321$ 被惰性素数 $3 \mid 144$ 绝对禁除（`lem:general-endpoint-rigidity`）。取 $m = 323$ 与 $m = 319$ 得：
   $$c_\varphi(A/12 - e) = \frac{323}{144\sqrt5} - 1 \approx 0.0031249399061556554724487430558364223,$$
   $$c_{\mathrm{sec}}^{(12)} = 1 - \frac{319}{144\sqrt5} \approx 0.0092976599688431761742688884371151124.$$
   - 极值轨道族（$m = 323$，每组各 $3$ 族）：
     - $A \equiv 1,5 \pmod{12}$：$119:[[2,2,2]],\ 167:[[1,1,2]],\ 169:[[1,1,2,2]]$；
     - $A \equiv 7,11 \pmod{12}$：$119:[[2,2,2]],\ 121:[[2,2]],\ 167:[[1,1,2]]$。
   - 第二极限点（$m = 319$，两组均为 $2$ 族）：$79:[[3,1,1,1,4]],\ 175:[[]]$。
   - Case 2 无需排除任何 $r_2$：全 $Q_1 \ge 0.02175883972 > c_{\mathrm{sec}}^{(12)}$，全非-$Q_1$ 分支 $\ge \frac{\sqrt5}{144} \approx 0.01552825 > c_{\mathrm{sec}}^{(12)}$。$\square$

- **2500 位 `mpmath` 实测**（`49, 53, 55, 59 / 12 - e` 各 $215$ 窗，$j=145..359$，[verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log#L119-L129)）：
  `max_dev_ext <= 0.0001308`，`max_dev_sec <= 0.005148`（有限 $b_j$ 移位均来自 $q_0=175$ 的 `[]` 族）；每类 `18711..19047` 点扫描 `min_non_ext >= 0.004482 > 0.0042 > c_min^(12)`，`min_non_ext_sec >= 0.008374 > 0.008`。

---

## 4. 通用算法归约、无穷族规律与诚实边界声明

### 4.1 任意 $(A, B, C)$ 的完全一般证明部分 vs 有限枚举部分

1. **已获完全一般证明（对无穷族成立）的定律**：
   - **单尺度全覆盖族（定理 G1(2)-(3)）**：对任意 $B = 2^a 3^b 5^c \prod_{p\in\mathcal{N}_Q} p^{e_p}$ 及任意 $\gcd(A, B) = 1$，$x = A/B - e$ 绝对不出现任何 $G_j > 1$ 的缩并，全轨道严格单尺度 $D_j \equiv 2B^2$。对更一般 $(A,B,C)$，单尺度是否成立仅取决于有限集合 $\{p \mid BC\}$ 的模 $p$ 判定（定理 G1(3)）。
   - **偶 $B$ 四分之一周期折半与 $2$-进屏蔽（定理 G2）**：对**全体偶 $B = 2^a B_{\mathrm{odd}}$**，最小窗口周期必整除 $S = B^2/2$（缩减模算枚举规模至 $1/4$），且在 $G_j \equiv G_{j+1} \pmod{M_2}$ 窗口上严格服从 $q_0 \bmod 8 \in \{3,5\}$（$a=1$）或 $q_0 \bmod 8 \in \{1,7\}$ 且偶窗 $q_0 \equiv 1 \pmod{\min(2^{a+1},64)}$（$a \ge 2$）。
   - **三重算术筛法与普适 Case 2 坍缩（定理 G3 + 论文一既有引理）**：对**全体** $D = 2d$ 模型，候选项 $m$ 必须同时通过：(i) 奇偶性 $m \equiv d + 1 \pmod 2$；(ii) 全部奇惰性素数 $p \equiv 2,3 \pmod 5 \implies (p\mid d \Rightarrow p\nmid m)$；(iii) 分歧 $5$ 刚性 $5\mid d \Rightarrow 25\nmid m$；(iv) 模 $2^k$ 因子范数同余。且只要 $D_{\max} \ge 14$（**一切 $B \ge 3$ 的 $A/B-e$ 均自动满足**），除有限个前窗 $Q_1$ 外，全部分支均由 $\sqrt5/d_{\max}$ 一致封闭。
   - **普适下包络（定理 G3(3)）**：对全部 $B \ge 3,\ \gcd(A,B)=1$ 成立 $c_\varphi(A/B-e) > \frac{1}{10B^4+B^2\sqrt5}$。

2. **仍依赖有限周期窗枚举的部分（以及未证公开点）**：
   - **高分母 $B \ge 13$ 的实际实现后缀集 $\mathcal{Q}_0(A, B)$**：尽管已知 $\mathcal{Q}_0(A, B)$ 必然落入上述理论筛出的 $2$-进/$p$-进子群中，但目前尚未证明哪些 $A/B-e$ 恰好饱和整个同余陪集（如 $B=7,9,10,11$），哪些按 $A \bmod 4$（或更高模）分裂为多组（如 $B=4,8,12$），以及在 $p \in \mathcal{Z}_Q$ 时何时会饱和 $p^2 \mid Q_j$（而非不整除 $p^2$ 或稀疏命中）；因此对特定高分母 $B \ge 13$，确定最紧合法整数 $m$ 是否确由 $\mathcal{Q}_0(A,B)$ 的 $4\tau$-约数实现，仍依赖模 $2B^2$ 有限周期窗枚举（论文一 `thm:golden-finite-shift` 算法保证在有限步内停机）。
   - **Lean 4 形式化与核心公开问题边界**：
     - [epi_formal/](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/epi_formal/) 当前仅形式化 $B=1,2$、截断头界及 `GeneralEndpointRigidity.lean`（$B=3..6$ 核心不等式与奇惰性素数引理）；本记录中的定理 G1–G3 及 $B=7..12$ 全定理目前为**纸面完整证明 + `2500` 位 `mpmath` 零失败验证**，未声称已经 Lean 4 核验。
     - **与 $e+\pi$ 无理性的关系**：本文全部结果**严格属于 $e$-侧仿射模型 $A/B-e$ 与 $(A+Ce)/B$ 的谱与轨道刻画**，没有任何结果对 $c_\varphi(\pi)=0$ 或 $e+\pi\notin\mathbb{Q}$ 构成证明推进或近似推进。

---

## 5. 留痕文件核对索引

- **2500 位高精度验证脚本**：[verification/verify_golden_general_b.py](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.py)
- **完整验证日志（0 失败）**：[verification/verify_golden_general_b.log](file:///c:/Users/Lgnatius/Documents/qwen-agent/QOTCWZPRRA/default/epi_work/verification/verify_golden_general_b.log)
- **未改动文件确认**：未修改任何 `.tex` 主论文或 Lean 4 源码。
