# Kahane 问题 Q6 增补与修正（2026-11-25 Addendum）

**一句总判断**：本增补文档在不修改原笔记 [`kahane_q6_note_20261125.md`](kahane_q6_note_20261125.md) 的前提下，给出两项经独立逐行审查与高精度计算核验的新定论：（一）**否证**原笔记 §3c′–§3c‴ 的**猜想 D′** 与**引理 R**（但**引理 D** 本身因最优阶 $m \asymp n^{1/3}$ 仅给出 $\exp(-c n^{2/3})$ 次指数下界而**仍然开放**）；（二）对**任意**确定目标序列 $(b_n)$，在整数 $M \ge 4$ 与严格条件 $2\varepsilon M > 3$ 下证明了全新的**确定性局部维数下界定理 K-2**（$\underline{\dim}_{\mathrm{loc}}(E(\varepsilon), M) \ge \frac{\log(\lceil 2\varepsilon M\rceil - 1)}{\log M}$），在如 $M=4,\varepsilon=0.376$ 等区间不仅大幅超越 Kahane 2014 式 (3)（$0.7925$ vs $0.2944$），甚至超过原笔记面向几乎所有 $(b_n)$ 的淬火定理 3（$0.5749$）。

> **范围声明**：本增补仍不解决 Kahane 原问题 Q6 的等式（$\dim_H(E(\varepsilon)\cap[1,X]) \stackrel{?}{=} \log(2\varepsilon X)/\log X$），亦与 $e+\pi$ 无理性无关。

| 结果 | 类别（[`AGENTS.md`](../AGENTS.md)） | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| 否证猜想 D′ 与引理 R：对每个满足 $2\varepsilon a>1$ 的紧区间 $I=[a,c]\subset(1,\infty)$、每个 $\varepsilon\in(0,1/2)$ 及每个 $h\in\mathbb Z\setminus\{0\}$，均存在固定阶多重点多项式使 $U_n(h)$ 按次指数衰减并指数级超越 $(2\varepsilon a)^{-n}$ | **无条件新结果（反例否证）** | 完整分析证明；`mpmath`（`dps=120`）数值核验精确交叉点 $n_{\mathrm{cross}}=968$ 与零权重规避构造 | 推翻 [`kahane_q6_note_20261125.md`](kahane_q6_note_20261125.md) §3c′–§3c‴ 的充分链条，说明原路径需从“逐项指数上界”改道 | §1、[`verify_kahane_q6_refutation_and_det_20261125.py`](../verification/verify_kahane_q6_refutation_and_det_20261125.py) |
| 引理 D 现状：多重点单多项式族的最优下界包络为 $\exp(-c n^{2/3})$（仍可和） | **文献与结构澄清** | 分析推导 + $n\le 5000$ 数值包络核验 | 引理 D 本身尚未被否证，仍为开放问题 | §1.3 |
| 线性模型精确下界（定理 K-1）：当 $2\varepsilon M = K \in \mathbb Z_{\ge 2}$ 时，对**一切** $(\tilde b_1,\dots,\tilde b_m)\in[0,1)^m$，测度恒为 $(2\varepsilon)^{m+1}$ 且完整窗口数 $Z_m^* \ge \frac{(K-2)K^m+1}{K-1}$ | **无条件新结果** | 完整归纳与端点配对证明；有理数精确算术 `Fraction` 核验含最坏情况（如 $M=5,K=4,m=4$ 取等 $171=171$） | 负搜索未见于现有关于 $x^n\bmod 1$ 的文献（检索范围见 §4） | §2.1 |
| 确定性局部维数下界（定理 K-2）：对**一切**确定序列 $(b_n)\subset[0,1)$、一切整数 $M\ge 4$ 与 $2\varepsilon M > K\ge 3$（即 $K=\lceil 2\varepsilon M\rceil-1\ge 3$），$\underline{\dim}_{\mathrm{loc}}(E(\varepsilon),M)\ge\frac{\log K}{\log M}$ | **无条件新结果** | 逐行对抗审查修复边界截断与 Taylor 误差量词顺序后闭合；`mpmath` 高精度（最高 `dps=32000`, $n=45000$）真实非线性 $x^n$ 分支校验全过 | 严格改进 Kahane 2014 式 (3)（当 $\frac{\lceil 2\varepsilon M\rceil-1}{M}$ 大于 $2\varepsilon(1-2/M)$ 时）；与定理 3 互补（对确定序列成立） | §2.2、§2.3 |
| 原笔记定理 1–3 与 §4 复核 | **文献核查与复现** | 50 位精度复核定理 3 全表与反例 $(26,0.03)$；补注边界条件与“$\le\varepsilon$ vs $<\varepsilon$”细节 | 与原笔记一致，无实质错误 | §3 |

---

## 1. 猜想 D′ 与引理 R 的完全否证（§3c′–§3c‴ 勘误）

回顾 [`kahane_q6_note_20261125.md`](kahane_q6_note_20261125.md) §3c‴（命题 P1）：对 $I=[a,c]\subset(1,\infty)$（$a<c$）与 $h\in\mathbb Z\setminus\{0\}$，
$$U_n(h)=\sum_{k\in\mathbb Z^{n-N+1}}\left(\prod_{j=N}^n w(k_j)\right)\left|\int_I e\big(P_k(x)\big)\,dx\right|^2,\qquad P_k(x)=hx^{n+1}+\sum_{j=N}^n k_j x^j,$$
其中 $w(0)=1$，对 $k\ne 0$ 有 $w(k)=\big(\frac{\sin(2\pi k\varepsilon)}{2\pi k\varepsilon}\big)^2\ge 0$。猜想 D′ 断言 $U_n(h)\le C_h n^{O(1)}(2\varepsilon a)^{-n}$；引理 R 断言在 $L=\lceil n^2|I|\rceil$ 等分小段 $I_\ell$ 上，同时存在 $x,y\in I_\ell$ 使 $|P_k'(x)|<\lambda_1$ 且 $|P_k''(y)|<\lambda_2$ 的二重共振项对 $U_n(h)$ 贡献也至多 $C_h n^{O(1)}(2\varepsilon a)^{-n}$。

### 1.1 典型反例与精确数学证明（$x_0=3\in I$，$h=1$）

取 $I=[2.998,3.002]$、$\varepsilon=0.30$（故 $2\varepsilon a=1.7988>1$）与 $h=1$。对固定整数 $m\ge 4$ 及充分大的 $n\ge N+m-1$，考虑单一项多项式
$$P_{n,m}(x)=x^{n+1-m}(x-3)^m=x^{n+1}+\sum_{r=1}^m (-1)^r\binom{m}{r}3^r\,x^{n+1-r}.$$
1. **权重与 $n$ 无关**：非零且非首项的系数只有 $k_{n+1-r}=(-1)^r\binom{m}{r}3^r$（$1\le r\le m$），全部独立于 $n$；其余系数为 $0$（权重 $w(0)=1$）。对 $\varepsilon=0.30$，有 $2\varepsilon k\in\mathbb Z\iff 5\mid k$；当 $m=4$ 时，系数为 $(-12,54,-108,81)$，均不被 $5$ 整除，故
   $$c_4(0.30):=w(-12)w(54)w(-108)w(81)\approx 1.90688059\times 10^{-17}>0.$$
2. **振荡积分的次指数衰减**：令 $x=3+u\cdot 3^{-(n+1-m)/m}$。当 $n\to\infty$ 时，积分区间化为 $[-0.002\cdot 3^{(n+1-m)/m},\ 0.002\cdot 3^{(n+1-m)/m}]\to\mathbb R$，相位一致收敛于 $u^m$，从而
   $$\left|\int_{2.998}^{3.002} e\big(P_{n,m}(x)\big)\,dx\right|^2=\big(C_m+o(1)\big)\,3^{-\frac{2(n+1-m)}{m}},\qquad C_m:=\left|\int_{-\infty}^{\infty} e(u^m)\,du\right|^2>0$$
   （$m=4$ 时 $C_4=\big(2\Gamma(5/4)(2\pi)^{-1/4}\big)^2\approx 1.31102878$）。
3. **否证猜想 D′ 与引理 R**：当 $m=4$ 时，单一项底数为 $3^{-1/2}\approx 0.57735027 > (2\varepsilon a)^{-1}\approx 0.55592617$。因此 $U_n(1)\ge c_4(0.30)\big(C_4+o(1)\big)3^{-(n-3)/2}$ **指数级超过** $(2\varepsilon a)^{-n}$。脚本 [`verify_kahane_q6_refutation_and_det_20261125.py`](../verification/verify_kahane_q6_refutation_and_det_20261125.py) 通过核心分段高精度求积加二阶分部积分，在 $n=30\dots 200$ 范围内核实 $|I_n|^2/C_4 3^{-(n-3)/2}\to 1.00000000$，且严格给出该单一项超越 $(2\varepsilon a)^{-n}$ 的精确交叉点为 $n_{\mathrm{cross}}=968$（这也解释了为何 §3c′ 仅在 $n\le 22$ 的模拟中完全观察不到该反例）。
   同时，由于 $m\ge 3$ 时在 $x=y=3\in I_\ell$ 处有 $P_{n,m}'(3)=P_{n,m}''(3)=0$，该多项式精确落入引理 R 的剩余集 $\{(k,\ell)\}$ 中，故**引理 R 亦同步被否证**。

### 1.2 一般性补全：任意区间 $I$、任意 $\varepsilon$（含 $2\varepsilon\in\mathbb Q$）与任意 $h\ne 0$

原初探中仅构造了 $(qx-p)^m x^{n+1-m}$；若不加以修补，该式有两点不足：（i）当 $q>1$ 时首项系数为 $q^m\ne 1$，不直接落在 $U_n(1)$ 的求和中；（ii）当 $2\varepsilon=u/v\in\mathbb Q$ 时，对某些 $m$（例如 $\varepsilon=1/4, m=4$ 时 $k_n=-12$ 满足 $2\varepsilon k_n\in\mathbb Z$），会触发权重 $w(k_j)=0$ 使该项退化。以下构造完全消除了这两点瑕疵：

- **情形 A（$2\varepsilon\notin\mathbb Q$，或 $2\varepsilon=u/v\in\mathbb Q$ 且存在素数 $p\mid v$ 使 $p\nmid h$）**：对任意非空闭区间 $I=[a,c]\subset(1,\infty)$，取足够大的 $d\ge 1$ 使 $c^d-a^d>p+1$（若 $2\varepsilon\notin\mathbb Q$ 可任意取 $p=2$），选整数 $M\in(a^d,c^d)$ 使 $p\nmid M$，令 $x_0=M^{1/d}\in(a,c)$。再选 $m=p^t-1$ 充分大使得 $x_0^{-2/m}>(2\varepsilon a)^{-1}$。取
  $$P_{n,m}(x)=h\,x^{n+1-dm}(x^d-M)^m.$$
  由 Lucas 定理，$p\nmid\binom{p^t-1}{r}$ 对所有 $0\le r\le m$ 成立；又 $p\nmid hM^r$，故所有非零非首项系数均不被 $p$（从而不被 $v$）整除，保证权重 $\prod w(k_j)>0$ 与 $n$ 无关，且积分平方按 $x_0^{-2n/m}$ 衰减，严格超越 $(2\varepsilon a)^{-n}$。
- **情形 B（$2\varepsilon=u/v\in\mathbb Q$ 且对所有 $p\mid v$ 均有 $p\mid h$）**：取 $v$ 的任一素因子 $p$，选 $d,M$ 如上使 $p\nmid M$，取 $m=p^t$ 充分大，令
  $$P_{n,m}(x)=x^{n+1-2dm}(x^d-M)^{p^t}\left(h\,x^{dm}+\sum_{r=0}^{p^t-1}x^{dr}\right).$$
  由于 $(x^d-M)^{p^t}\equiv x^{dp^t}-M^{p^t}\pmod p$，其与 $\sum_{r=0}^{p^t-1}x^{dr}$ 的乘积在所有 $x^{ds}$（$0\le s\le 2p^t-1$）上的系数模 $p$ 均非零（分别为 $-M^{p^t}$ 或 $1$）；再加首部 $h x^{dm}(x^d-M)^{p^t}$ 仅贡献首项 $h x^{n+1}$ 与可被 $p$ 整除的项，故**所有**非首项非零系数均不被 $p$ 整除，权重严格为正。脚本 [1B] 已验证 Case 1（$I=[2.9,3.1],\varepsilon=1/3,h=1$）、Case 2（$I=[1.9,2.1],\varepsilon=1/3,h=3$）与 Case 3（$I=[2.4,2.6],\varepsilon=0.30,h=1$）全部成功。

### 1.3 为何引理 D 仍保持开放（最优阶 $m\asymp n^{1/3}$ 包络）

固定 $x_0=M\in I$ 时，随 $m$ 增大，权重衰减量为
$$\prod_{r=1}^m w\!\left((-1)^r\binom{m}{r}M^r\right)\approx\prod_{r=1}^m\binom{m}{r}^{-2}M^{-2r}=\exp\big(-(1+\log M)m^2+O(m\log m)\big).$$
将其与积分平方 $M^{-2n/m}$ 相乘并对 $m$ 求极值：极小化 $(1+\log M)m^2 + \frac{2\log M}{m}n$ 得最优阶
$$m_{\mathrm{opt}}(n)\sim \left(\frac{\log M}{1+\log M}\,n\right)^{1/3},\qquad \max_m\Big(W_m\cdot M^{-2n/m}\Big)\approx \exp\big(-c\,n^{2/3}\big).$$
由于 $\sum_{n\ge 1}\exp(-c\,n^{2/3})<\infty$，这一多重点多项式反例族**无法否证引理 D**（脚本 [1C] 对 $n\le 5000$ 实测 $- \log(\text{贡献})/n^{2/3}\approx 4.09\text{–}4.69$）。换言之：猜想 D′ 要求的“逐项指数上界 $n^{O(1)}(2\varepsilon a)^{-n}$”过强而为假；引理 D 若为真，其上界必须是次指数型（如 $\exp(-c n^{2/3})$ 或整体求和抵消）。

---

## 2. 确定性局部维数下界：线性模型定理 K-1 与非线性定理 K-2

本节给出对**每一个**确定序列 $(b_n)\subset[0,1)$ 成立的新下界，彻底摆脱“几乎处处”假设。

### 2.1 线性模型精确定理（定理 K-1）

**定理 K-1**：设 $M\in\mathbb Z_{\ge 2}$、$\varepsilon\in(0,1/2)$ 满足**整除条件** $2\varepsilon M = K\in\mathbb Z_{\ge 2}$。令 $\Omega_0=[-\varepsilon,\varepsilon)$，对任意确定序列 $(\tilde b_1,\dots,\tilde b_m)\in[0,1)^m$ 递推定义
$$\Omega_r=\big\{u\in\Omega_{r-1}:\ \|M^r u-\tilde b_r\|\in[0,\varepsilon)\big\}\quad(\text{模 }1\text{ 半开弧 }[\tilde b_r-\varepsilon,\tilde b_r+\varepsilon)\bmod 1).$$
则对所有 $m\ge 1$ 及**一切** $(\tilde b_1,\dots,\tilde b_m)\in[0,1)^m$：
1. **确定性测度守恒**：$|\Omega_m|=(2\varepsilon)^{m+1}$；且 $u\mapsto M^{m+1}u\bmod 1$ 将 $\Omega_m$ **恰好 $K^{m+1}$-对-$1$ 地**满射到 $\mathbb R/\mathbb Z$。
2. **完整窗口精确下界**：记 $Z_m^*$ 为 $\Omega_m$ 内部所含长度恰为 $2\varepsilon/M^m$ 的完整第 $m$ 层窗口 $[(k+\tilde b_m-\varepsilon)/M^m,\,(k+\tilde b_m+\varepsilon)/M^m]$ 的个数，则
   $$Z_m^*\ge K^m-\sum_{r=0}^{m-1}K^r=\frac{(K-2)K^m+1}{K-1}.$$

**证明**：
1. 对 $r$ 归纳。$r=0$ 时，$M\Omega_0=[-K/2,K/2)$ 长度为整数 $K$，故 $u\mapsto Mu\bmod 1$ 恰好 $K$-对-$1$。由 $r-1$ 推 $r$：圆周上满足 $Mz\equiv y\pmod 1$ 的 $M$ 个点 $z_j=(y+j)/M$ 间距为 $1/M$，而半开弧 $A_r=[\tilde b_r-\varepsilon,\tilde b_r+\varepsilon)\bmod 1$ 长度为 $2\varepsilon=K/M$，因此恰有 $K$ 个 $z_j$ 落入 $A_r$，每个 $z_j$ 在 $\Omega_{r-1}$ 中有 $K^r$ 个原像，总原像数为 $K^{r+1}$。测度为 $\frac{1}{M}\cdot K^r\cdot(2\varepsilon)=(2\varepsilon)^{r+1}$。
2. 对任意第 $r$ 层（$0\le r\le m-1$）在 $\operatorname{int}(\Omega_{r-1})$ 中的边界点 $p_+$（右端点，$M^r p_+\equiv\tilde b_r+\varepsilon\pmod 1$）与 $p_-$（左端点，$M^r p_-\equiv\tilde b_r-\varepsilon\pmod 1$）：因 $M^m(2\varepsilon/M^r)=M^{m-r-1}K\in\mathbb Z$，必有
   $$M^m p_+\equiv M^m p_-\equiv M^{m-r}(\tilde b_r+\varepsilon)\pmod 1.$$
   若该相位落在第 $m$ 层窗口弧 $(\tilde b_m-\varepsilon,\tilde b_m+\varepsilon)\bmod 1$ 内部，相对比例为 $\theta\in(0,1)$，则每个 $p_+$ 至多切出左侧残片测度 $\theta\cdot\frac{2\varepsilon}{M^m}$，每个 $p_-$ 至多切出右侧残片测度 $(1-\theta)\cdot\frac{2\varepsilon}{M^m}$。由第 (1) 步，$p_+$ 与 $p_-$ 在 $\operatorname{int}(\Omega_{r-1})$ 中的个数均至多 $K^r$。因此第 $r$ 层边界产生的全部残片测度之和至多为 $K^r(\theta+(1-\theta))\frac{2\varepsilon}{M^m}=K^r\frac{2\varepsilon}{M^m}$！用总测度 $|\Omega_m|=K^m\frac{2\varepsilon}{M^m}$ 减去各层 $0\le r\le m-1$ 残片测度即得 $Z_m^*\ge K^m-\sum_{r=0}^{m-1}K^r$。∎

### 2.2 非线性映射向确定性下界的迁移（定理 K-2）

**定理 K-2（对任意确定目标序列成立）**：设 $M\in\mathbb Z_{\ge 4}$、$\varepsilon\in(0,1/2)$ 满足**严格**不等式 $2\varepsilon M > K$，其中 $K:=\lceil 2\varepsilon M\rceil - 1\in\mathbb Z_{\ge 3}$。则对**每一个**确定序列 $(b_n)_{n\ge 1}\subset[0,1)$，
$$\underline{\dim}_{\mathrm{loc}}\big(E(\varepsilon,(b_n)),\,M\big):=\lim_{\eta\to 0^+}\dim_H\big(E(\varepsilon,(b_n))\cap[M-\eta,M+\eta]\big)\ge \frac{\log K}{\log M}.$$
推论：对任意 $X\ge 4$，取遍 $[4,X]$ 内所有整数 $M$ 即得无条件全局下界 $\dim_H(E(\varepsilon,(b_n))\cap[1,X])\ge \max_{4\le M\le X,\ 2\varepsilon M>3}\frac{\log(\lceil 2\varepsilon M\rceil-1)}{\log M}$。

**完整证明（经对抗审查与高精度数值验证）**：
1. **收缩半径以制造缓冲区**：令 $\varepsilon_0:=\frac{K}{2M}<\varepsilon$，于是 $2\varepsilon_0 M=K\in\mathbb Z_{\ge 3}$ 精确成立，且缓冲区 $\delta:=\min(\varepsilon-\varepsilon_0,\varepsilon_0,1/4)>0$。
2. **固定分块长度 $m\ge 2$ 并控制 Taylor 线性化误差**：给定任意 $\eta_0>0$ 与分块步长 $m\ge 2$，选取 $\eta\in(0,\eta_0)$ 足够小及起始层 $N=N(m,M,\delta)$ 足够大，使得对所有 $n\ge N$、所有 $x_0\in[M-\eta,M]$、所有 $u\in[-\varepsilon_0,\varepsilon_0]$ 及所有 $1\le r\le m$，令 $x(u)=(x_0^n+u)^{1/n}$，有
   $$x(u)^{n+r}-x_0^{n+r}=M^r u+E_r(u),\qquad |E_r(u)|\le |x_0^r-M^r|\varepsilon_0 + \frac{r x_0^r}{n}\varepsilon_0 + O\!\left(\frac{r^2 M^r}{n^2}\right) < \frac{\delta}{3}.$$
   （注意此处必须要求 $N\gg \frac{m M^m}{\delta}$ 与 $\eta\ll \frac{\delta}{m M^{m-1}}$。）
3. **构造嵌套的 $\varepsilon_0$-完整窗口树**：在 $[M-\eta,M-\eta/2]$ 内选取一个第 $N$ 层半径为 $\varepsilon_0$ 的完整窗口 $J_0$（存在性由 $(M-\eta/2)^N-(M-\eta)^N>2$ 保证）。归纳地，设 $J$ 为任意第 $n_t=N+tm$ 层半径 $\varepsilon_0$ 的完整窗口（以 $u=x^{n_t}-(k_{n_t}+b_{n_t})\in[-\varepsilon_0,\varepsilon_0]$ 参数化，中心 $x_0\in[M-\eta,M]$）。在 $[-\varepsilon_0,\varepsilon_0]$ 上对有效偏移 $\tilde b_r:=b_{n_t+r}-x_0^{n_t+r}\bmod 1$ 应用定理 K-1，得至少 $Z_m^*\ge \frac{(K-2)K^m+1}{K-1}$ 个完整线性窗口 $I_{m,\ell}=[L_\ell/M^m, R_\ell/M^m]$。
4. **丢弃至多 2 个边界窗口以确保严格嵌套与中间层约束**：
   - 因不同完整线性窗口左端点间距至少为 $1/M^m$，且 $\delta/(2M^m)<1/(4M^m)$，至多有最左与最右共 $2$ 个完整线性窗口不落在 $[-\varepsilon_0+\frac{\delta}{2M^m},\,\varepsilon_0-\frac{\delta}{2M^m}]$ 内。
   - 对其余至少 $Z_m^*-2\ge \frac{(K-2)K^m+1}{K-1}-2\ge 3$ 个内部线性窗口 $I_{m,\ell}$，相应的非线性子窗口 $J'_\ell=\{u:\|x(u)^{n_t+m}-b_{n_t+m}\|\le\varepsilon_0\}$ 满足 $M^m u\in[L_\ell-\delta/3, R_\ell+\delta/3]$，故严格包含于 $(-\varepsilon_0,\varepsilon_0)$（即 $J'_\ell\subset\operatorname{int}(J)$），且对所有 $1\le r\le m-1$ 均有 $\operatorname{dist}(u,I_{m,\ell})\le \frac{\delta}{3M^m}$，从而
     $$\|x(u)^{n_t+r}-b_{n_t+r}\|\le \varepsilon_0+M^r\frac{\delta}{3M^m}+|E_r(u)|\le \varepsilon_0+\frac{\delta}{6}+\frac{\delta}{3}<\varepsilon.$$
   （注：为避免紧贴 $2\varepsilon M=K$ 整数点时退化，不能省略步骤 1 中的严格收缩 $\varepsilon_0<\varepsilon$；这也是当 $2\varepsilon M=K$ 恰好为整数时，定理 K-2 在 $M$ 处给出 $\log(K-1)/\log M$ 而非 $\log K/\log M$ 的根本原因。）
5. **质量分布收尾**：沿分块树均匀分配质量 $\mu(J_t)\le (Z_m^*-2)^{-t}$。不同同层子块间隙至少为 $\mathrm{gap}_t=\frac{1-2\varepsilon_0}{n_t M^{n_t-1}}$（事实上因 $x\le M$ 导数至多 $n_t M^{n_t-1}$！）。对任意满足 $\frac{1}{2}\mathrm{gap}_{t+1}\le r<\frac{1}{2}\mathrm{gap}_t$ 的球 $B(x,r)$，因 $2r<\mathrm{gap}_t$，它至多与一个深度 $t$ 块相交，故 $\mu(B(x,r))\le (Z_m^*-2)^{-t}$。令 $t\to\infty$ 得 $\dim_H(F_m)\ge \frac{\log(Z_m^*-2)}{m\log M}$，再令 $m\to\infty$ 且 $\eta_0\to 0$ 即证 $\underline{\dim}_{\mathrm{loc}}(E(\varepsilon),M)\ge \frac{\log K}{\log M}$。∎

### 2.3 定量对比（30 位高精度核验）

| $M$ | $\varepsilon$ | $2\varepsilon M$ | Kahane (3)（任意 $b_n$） | 定理 3（几乎每个 $b_n$） | 新定理 K-2（任意 $b_n$，在 $M$ 处） | $[1,M]$ 上最佳整数 $M'$ 的 K-2 | 候选值 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 0.45 | 3.6 | 0.42400 | 0.70474 | **0.79248** | 0.79248 ($M'=4$) | 0.92400 |
| 4 | 0.376 | 3.008 | 0.29440 | 0.57488 | **0.79248** | 0.79248 ($M'=4$) | 0.79440 |
| 5 | 0.31 | 3.1 | 0.38559 | 0.55160 | **0.68261** | 0.68261 ($M'=5$) | 0.70298 |
| 5 | 0.45 | 4.5 | 0.61714 | 0.78985 | **0.86135** | 0.86135 ($M'=5$) | 0.93454 |
| 6 | 0.35 | 4.2 | 0.57464 | 0.69343 | **0.77371** | 0.77371 ($M'=6$) | 0.80094 |
| 10 | 0.201 | 4.02 | 0.50732 | 0.55433 | **0.60206** | 0.60206 ($M'=10$) | 0.60423 |
| 10 | 0.30 | 6.0 | 0.68124 | 0.73064 | 0.69897（$K=5$） | **0.73249**（$M'=9$） | 0.77815 |
| 100 | 0.10 | 20.0 | 0.64613 | 0.64829 | 0.63938 | 0.64510 ($M'=96$) | 0.65051 |

**诚实评注**：当 $\varepsilon$ 较小时，或当 $M$ 处 $2\varepsilon M$ 恰好为整数时（如 $M=10,\varepsilon=0.30$），K-2 在 $M$ 处因取 $K=\lceil 2\varepsilon M\rceil-1$ 退步一档，但通过在 $[1,M]$ 中选较小整数（如 $M'=9$）可部分挽回；且当 $X\to\infty$ 且 $\varepsilon$ 固定时，K-2 与 Kahane (3) 同为 $1-O(1/\log X)$。它未能证明非整数处的等价维数，也未给出任意 $X$ 处的上界。

---

## 3. 原笔记定理 1–3 的边界与细节核查

对 [`kahane_q6_note_20261125.md`](kahane_q6_note_20261125.md) 的主结果进行 50 位精度复算与逐行条件检验后，确认：
- **定理 1、2、3 数学主体均成立**：50 位精度复算验证原笔记定理 3 表中全部数值及 $(v=26,\varepsilon=0.03)$ 反例（Kahane $=0.11191906$ vs 定理 3 $=0.10637303$）。
- **需注意的小边界**：
  1. 定理 2 中对小区间 $I=[a,c]$ 给出上界 $\max(0,\log(2\varepsilon c)/\log a)$，故对单点 $v$ 处仅能推出 $\le\max(0,\log(2\varepsilon v)/\log v)$，无非局部的直接误差项依赖；
  2. 定理 3 证明中严格使用 $L_\eta=2\varepsilon(v-\eta-1)>1$ 以保证 $\mathbb P(f_{L_\eta}\ge 2)>0$ 从而 $\nu$ 无原子（用于排除可数个 $\|x^n-b_n\|=\varepsilon$ 边界点），在 $L=1$ 临界处退化为 $0$，与表中陈述一致。

---

## 4. 先例检索覆盖与局限

- **覆盖范围**：经本地 `search` MCP（含 arXiv、OpenAlex）及已有 [`candidateA_precedent_search_20261125.md`](../verification/candidateA_precedent_search_20261125.md) 核查 Kahane (2014, doi:10.1016/j.crma.2013.12.014)、Baker (预印本 arXiv:1411.4817，BLR 中引为 *Uniform Distribution Theory* 10(2), 2015)、Bugeaud–Liao–Rams (*Proc. Edinb. Math. Soc.*, 2018, doi:10.1017/s0013091518000585；逐字核对之 v1 文本为预印本 arXiv:1710.03596)。**负搜索**未发现针对确定 $(b_n)$ 的整数位点下界 $\log(\lceil 2\varepsilon M\rceil-1)/\log M$。
- **未做到与覆盖局限**：
  - 未检索 MathSciNet / zbMATH 全文引用链，因此不能宣称“已证明文献中绝对不存在先例”，仅报告在上述检索覆盖内未见先例；
  - 确定性下界 K-2 仍依赖整数 $M$（尚不能直接对非整数有理数 $p/q$ 复制，因 $q^r$ 在分母会破坏 $1$-周期网格恒定重数）；
  - 几乎处处下界的引理 D 仍完全开放，推翻猜想 D′ 与引理 R 后需要新的次指数级或宏观消去路线。
