# 对抗性逐行审阅报告：Kahane Q6、非线性 BLR (1.6) 去除与偶数拟周期 Hurwitz 符号（2026-11-25）

**一句总判断**：四项待审命题的最终裁决为：**两项成立（其中 K-2 需补严量词与缩放阈值）、一项被彻底否证（猜想 D′ 与引理 R，但引理 D 仍开放）、一项在原文声称的完全一般性上不成立且证明存在实质漏洞（非线性 BLR 去除 (1.6) 在超缺项幂次与一般 $C^2$ 情形需要补加单步失真与尾集/右侧局部化条件）**；偶数拟周期 Hurwitz 三项递推负号与 $e$ 全收敛子结论完全成立。

| 审阅对象 | 类别（[`AGENTS.md`](../AGENTS.md)） | 审阅裁决 | 核心漏洞 / 关键修正 | 复核脚本 |
| :--- | :--- | :--- | :--- | :--- |
| **1. 猜想 D′ & 引理 R 否证，与引理 D 现状** | 无条件新结果（反例否证） | **否证 D′ 与 R 成立；引理 D 仍开放** | 补全了 $2\varepsilon\in\mathbb Q$ / $v\mid h$ 零权重规避及无整数区间情形；证明最优阶 $m\asymp n^{1/3}$ 包络为 $\exp(-c n^{2/3})$（可和），故不推翻引理 D | [`verify_kahane_q6_refutation_and_det_20261125.py`](verify_kahane_q6_refutation_and_det_20261125.py) [1A–1C] |
| **2. 确定性定理 K-1（线性）与 K-2（非线性 $x^n$）** | 无条件新结果 | **基本成立（补全量词条件后完全严格）** | (a) K-1 依靠 $M^m p_+\equiv M^m p_-\pmod 1$ 的 $\theta+(1-\theta)=1$ 精确配对，实测锐度 $171=171$；(b) K-2 必须要求**严格** $2\varepsilon M > K\ge 3$，且在 $M$ 处须满足 $N(m)\gg m M^m/(\varepsilon-\varepsilon_0)$（对 $M=4,\varepsilon=0.376$ 即使 $m=2$ 亦需 $N\approx 4.5\times 10^4$） | [`verify_kahane_q6_refutation_and_det_20261125.py`](verify_kahane_q6_refutation_and_det_20261125.py) [2A–2C] |
| **3. 非线性 BLR (1.6) 去除与放弃 Baker 插补** | 条件修复后部分成立（原文草稿有 3 处实质缺口） | **一般性声称不成立；需加限修复** | (a) 原 BLR “$\forall n\ge 1$” 集合在固定 $v$ 下可为空集；(b) 超缺项 $r_{n+1}\gg r_n v^{r_n}$ 时，放弃 Baker 插补会导致等质量 Frostman 测度在 $r=10/r_{n+1}$ 处球测度爆表（脚本 [1A] 实测违例 $19.94\times$）；(c) 一般 $C^2$ 仅靠 BLR (1.1) + Adler 失真无法吸收 $\sum_{j<n}\log f'_j$ | [`verify_nonlinear_blr_20261125.py`](verify_nonlinear_blr_20261125.py) [1A–1B] |
| **4. 偶数拟周期 Hurwitz 负号 & $e$ 全收敛子** | 无条件新结果 | **完全成立** | $2\times 2$ 常数块行列式 $\det C=(-1)^{p-1}$ 严格给出 $Q_{j+1}=(\alpha a_j+\beta+\gamma)Q_j+(-1)^{p-1}Q_{j-1}$；`GrowingRecData` 仅覆盖奇数 $p$ | [`verify_nonlinear_blr_20261125.py`](verify_nonlinear_blr_20261125.py) [2] |

---

## 一、猜想 D′、引理 R 与引理 D 对抗审阅

1. **原草稿缺口排查**：
   - 原草稿仅写 $(qx-p)^m x^{n+1-m}$：当 $q>1$ 时首项为 $q^m\ne 1$，只反驳 $U_n(q^m)$ 而不直接反驳 $U_n(1)$；当 $2\varepsilon=u/v\in\mathbb Q$（如 $\varepsilon=1/3$、$I=[2.9,3.1]$ 时 $3\mid (-3)^r\binom{m}{r}$）时权重可全零。
   - **修复后无条件构造**：见 [`kahane_q6_addendum_20261125.md`](../research/kahane_q6_addendum_20261125.md) §1.2，采用 $(x^d-M)^{p^t-1}$ 或 $(x^d-M)^{p^t}(h x^{dm}+\sum_{r=0}^{p^t-1}x^{dr})$，使**所有**非首项非零系数不被 $p\mid v$ 整除，且积分基数 $x_0^{-2/m}>(2\varepsilon a)^{-1}$。
2. **数值核验摘要**（`mpmath` `dps=120`）：
   - 在 $I=[2.998,3.002],\varepsilon=0.30,h=1$ 上，$(2\varepsilon a)^{-1}=0.555926173004$；$m=1,2,3$ 衰减率均低于该值，而 $m=4$ 的 $3^{-1/2}=0.5773502692 > 0.555926173004$。
   - 对 $m=4$，高精度振荡求积核实 $|I_n|^2 / (C_4\cdot 3^{-(n-3)/2})$ 在 $n=60\dots 200$ 上等于 `1.0`，精确交叉层 $n_{\mathrm{cross}}=968$（单一项超过 $(2\varepsilon a)^{-n}$，比值 `1.02413`）。
   - 最优 $m$ 包络在 $n=50\dots 5000$ 处呈现 $m_{\mathrm{opt}}/n^{1/3}\in[0.684,1.134]$、$-\log(\text{contrib})/n^{2/3}\approx 4.09\text{–}4.69$，确认该族无法推翻引理 D。

---

## 二、确定性定理 K-1 与 K-2 逐行审阅

1. **K-1 线性模型（完全通过）**：
   - **关键不变量**：用半开区 $[- \varepsilon, \varepsilon)$ 维持诱导测度与重数，每层 $u\mapsto M^{r+1}u\bmod 1$ 是精确 $K^{r+1}$-对-$1$（不是 $K^r$！），故第 $r$ 层边界点在 $\operatorname{int}(\Omega_{r-1})$ 中各有至多 $K^r$ 个 $p_+$ 与 $p_-$。
   - **精妙抵消**：因为 $M^m(p_+-p_-)$ 的同层窗口宽对模 $1$ 放大 $M^m$ 倍后为整数 $M^{m-r-1}K$，所有 $p_+$ 与 $p_-$ 落在完全相同的相对相位 $\theta\in(0,1)$ 上，切出的总残片测度至多 $K^r(\theta+(1-\theta))\frac{2\varepsilon}{M^m}=K^r\frac{2\varepsilon}{M^m}$。
   - 有理数 `Fraction` 精确核验全部 7 组 $(M,K,m)$（含贪心对抗与随机搜索）均满足 $|\Omega_m|=(2\varepsilon)^{m+1}$ 且 $Z_m^*\ge\frac{(K-2)K^m+1}{K-1}$（$M=5,K=4,m=4$ 与 $M=7,K=4,m=4$ 取等 `171=171`；$K=2$ 退化为 `1=1`）。
2. **K-2 非线性迁移（补正后通过）**：
   - **捕获的关键边界错误**：原草稿曾混用 $\lfloor 2\varepsilon M\rfloor$（当 $2\varepsilon M=K$ 为精确整数时，若取 $\varepsilon_0=\frac{K}{2M}=\varepsilon$ 则无缓冲区 $\delta=\varepsilon-\varepsilon_0>0$ 吸收非线性 Taylor 误差！），必须修正为 $K=\lceil 2\varepsilon M\rceil-1$（要求严格 $2\varepsilon M>K\ge 3$）。
   - **量词依赖核查**：线性化误差 $|x(u)^{n+r}-x_0^{n+r}-M^r u|$ 含有 $\frac{r M^r}{n}\varepsilon_0$ 项，要求先固定 $m$，再取 $\eta\ll \frac{\delta}{m M^{m-1}}$ 与 $N\gg \frac{m M^m}{\delta}$。脚本在 $M=4,\varepsilon=0.376$（$m=2,\delta=0.001$）上验证：当 $n=24$ 时线性化误差高达 `0.50`（远超 $\delta/3$），而当 $n=45000$（`dps=32000`）时，实测误差 `2.65e-04 < delta/3=3.33e-04` 且真实非线性子窗口数 `6 >= 3`（全通过）。

---

## 三、非线性 BLR (1.6) 去除与 Baker 插补审阅（发现实质漏洞）

逐字核对 BLR 原文（正式发表版 *Proc. Edinb. Math. Soc.*, 2018, doi:10.1017/s0013091518000585；本审阅逐字阅读的公开全文为预印本 arXiv:1710.03596v1 定理 7，p.5、pp.13–15）及 Baker (预印本 arXiv:1411.4817v1；BLR 中引为 *Uniform Distribution Theory* 10(2), 2015) 后，发现 `08ff5eb8` 草稿声称“对一切 $r_{n+1}-r_n\to\infty$ 的幂映射 $x^{r_n}$ 及一般 $C^2$ 映射均可去掉 BLR (1.6) 并放弃 Baker 插补”存在**三项实质漏洞**：

1. **漏洞 1（原 BLR 集合“$\forall n\ge 1$”在局部维数下的空集退化）**：若按原文定义 $G(f,y,\delta)=\{x:\|x^{r_n}-y_n\|\le\delta_n,\ \forall n\ge 1\}$，取 $r_1=1,y_1=1/2,\delta_1=0.1,v=3$，则对 $\eta<0.4$ 恒有 $[v-\eta,v+\eta]\cap G=\emptyset$（即使所有高阶条件皆满足），局部维数为 $0$。必须改为**尾集** $\{x:\|x^{r_n}-y_n\|\le\delta_n\text{ 对充分大的 }n\text{ 成立}\}$。
2. **漏洞 2（放弃 Baker 插补在超缺项 $r_{n+1}\gg r_n v^{r_n}$ 下导致等质量 Frostman 测度失效）**：
   - `08ff5eb8` 断言在 $\mathrm{gap}_{n+1}\le r\le\mathrm{diam}_n$ 尺度下可免去 Baker 插补并使用每个子区间等质量 $\mu(J_{n+1})=\mu(J_n)/N_{n+1}(J_n)$。
   - **反例（脚本 [1A] 精确验证）**：取 $v=1.5,\delta_n=1/8,r_n=24,r_{n+1}=2^{32}$。满足 $r_{n+1}-r_n\to\infty$ 且 $2\delta_n v^{r_{n+1}-r_n}\to\infty$。在窗口 $J_n=[c_n,d_n]$（$c_n=1.5$）上，$\log_{10}(f'_{n+1}(d_n)/f'_{n+1}(c_n))\approx 1154.2$。几乎全部子窗口都紧贴右端点 $d_n$ 分布：取测试球 $B(d_n,r_{\mathrm{test}})$（$r_{\mathrm{test}}=10/r_{n+1}\approx 2.33\times 10^{-9} < \mathrm{diam}_n\approx 9.28\times 10^{-7}$，$r_{\mathrm{test}}/\mathrm{diam}_n\approx 0.00251$），球内竟然集中了 $\mathbf{99.873\%}$ 的子区间质量！按等质量分配，$\mu(B(d_n,r_{\mathrm{test}}))/\mu(J_n)$ 违背 $s=0.5$ 霜满球界达 $19.94\times$（随 $r_n$ 增大将超指数发散），证实此情形下**必须保留 Baker 插补或改用非均匀测度**（正如 Baker 2015 原文在 $q_{n+1}/q_n\not\to 1$ 时强制启用 $\tilde q_n$ 插补）。
3. **漏洞 3（一般 $C^2$ 映射的 Adler 失真误用）**：对一般 $C^2$ 映射，Adler 条件 $|f''_n|/(f'_n)^2\le C$ 只保证 $f'_n$ 在 $J_n$ 自身上有界失真，不保证 $f'_{n+1}$ 在 $J_n$ 上有界失真；而仅有 BLR (1.1) 时，跨步失真因子 $(f'_j)^{\gamma(\eta)}$ 在非 (1.6) 情形会累积成 $\gamma(\eta)\sum_{j\le n}\log f'_j$（如 $r_j=j^2$ 时 $\sum j^2\gg n^2$），无法被 $\log f'_n$ 吸收。
4. **可执行修复版结论**：在 (i) 改为尾集、(ii) 下界限制在右侧半区间 $[v,v+\eta]$（因 $x<v$ 时 $(x/v)^{r_{n+1}-r_n}\to 0$ 可破坏 $\liminf 2\delta_n x^{r_{n+1}-r_n}>2$）、以及 (iii) 补充**单步有界失真条件** $\sup_n \frac{\delta_n r_{n+1}}{r_n v^{r_n}}<\infty$（或对超缺项段保留 Baker 插补）后，定理对诸如 $r_n=n^2$、$r_n=2^n$ 等不满足 BLR (1.6) 的幂映射完全成立（脚本 [1B] 验证单步对数失真一致有界）。

---

## 四、偶数拟周期 Hurwitz 递推负号与 $e$ 全收敛子审阅

1. **通用三项递推公式（完全严格）**：对拟周期为 $p$、每周期含 1 个线性增长部分商 $a_j=cj+d$ 与 $p-1$ 个常数部分商 $[c_1,\dots,c_{p-1}]$ 的 Hurwitz 连分数，记常数传输矩阵 $C=\prod_{i=1}^{p-1}\begin{pmatrix}c_i&1\\1&0\end{pmatrix}=\begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix}$。由 $\det C=(-1)^{p-1}$ 消元直接得到
   $$Q_{j+1}=(\alpha a_j+\beta+\gamma)Q_j+(-1)^{p-1}Q_{j-1}.$$
   当 $p$ 为**奇数**时取 $+$（如 $e$，$p=3$），当 $p$ 为**偶数**时严格取 $-$（如 $\tan(1),\tan(1/2),\tan(1/3),J_1(2)/J_0(2)$ 均 $p=2$，以及任意 $p=4$ 示例）。仓库 [`GeneralGrowingRec.lean`](../epi_formal/EpiFormal/GeneralGrowingRec.lean) 第 47 行硬编码了 $+Q_{j-1}$，确实未覆盖偶数拟周期。
2. **$e$ 全收敛子关系（完全严格）**：由 $a_{3j}=a_{3j+1}=1$ 立得 $q_{3j-1}=(Q_{j+1}-Q_j)/2$、$q_{3j}=(Q_{j+1}+Q_j)/2$（$j\ge 1$），且对 $x=(1+e)/2$（其奇数位伴随序列在 $\bmod 2$ 下交替），脚本 [2] 确认其在 $n=3j-2$ 处逼近零而在 $n=3j-1,3j$ 处 $w_n\|q_n x\|\to 1$，将零水平从扩大的陪集重新压回经典格 $\mathbb Z+\mathbb Z e$。
