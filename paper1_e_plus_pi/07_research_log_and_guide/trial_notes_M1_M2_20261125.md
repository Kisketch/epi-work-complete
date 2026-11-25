# 试错详记：Route M1（混合 $E/G$ Hermite–Padé 与 CDT 障碍）与 Route M2（一般 Möbius 窗口、3-轨道分类与 $e$ 全收敛谱）

> **一句总判断**：经过独立符号/高精度程序验证与对抗性边界审查，**Route M1 与 Route M2 均未降低原问题（$e+\pi$ 无理性）的核心难度，$e+\pi$ 仍完全公开**；但在副产物与障碍坐标上产出两项明确核实结论：**（1）Route M1** 精确证否了直接混合系列 $\alpha e^{\beta z}+G(z)$ 在 Calegari–Dimitrov–Tang 算术全纯界中的可行性（$\tau=\infty$ vs 有界共形半径 $\rho\le 4R_G$），并无条件证明混合 $(1,e^z,G(z))$ Type-I 线性形式的整除爆炸定律 $(M-1-d)!\mid D_{M-1}(G)\,d!\,Q_d$（同时严格标出该整除本身不直接推出固定点余项爆炸及若干绕行边界）；**（2）Route M2** 修正了草稿中关于一般 Möbius 变换 $M(e)$ 窗口阈值与周期的偏差，完成 $T=2|\Delta|$ 窗口移位定理、3 条 $\mathrm{PGL}_2(\mathbb{Z})$-发散轨道分类及 **$e$ 全收敛序列（$(q_n)_{n\ge -1}$）Kraaikamp–Liardet 完整离散谱 $\{0\}\cup\{k/2:k\ge 2\}\cup\{\infty\}$ 与精细规范**的独立复核（其中 $e$ 全收敛谱非常适合作为 Paper 2 独立增补章节并做 Lean 4 形式化）。

---

## §0 诚实分类总表（`AGENTS.md` 五分法）与未做到之事

| 结果 | 类别（`AGENTS.md` §2） | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| **M1a**：混合 $(1,e^z,G(z))$ 形式精确整除律 $(M-1-d)!\mid D_{M-1}(G)\,d!\,Q_d$ 及 $M\ge (2+\delta)n$ 下 $\log\|Q\|_\infty \ge \delta n\log n-O(n)$ | **1. 无条件新结果（窄诊断型）** + **4. 有限计算佐证** | **已核实**：SymPy $d=1..5, M=d+1..12$ 符号多项式整性全通过；104 组非对称次数边界 + 4 类 $G$-函数（含 $D_m=1$ 之 $(1-4z)^{-1/2}$）+ LLL 松弛对比全通过 | 在实际读取的 CDT (预印本 `arXiv:2408.15403` v2；ICM 2026 `10.1137/25m1806776` 对应预印本 `arXiv:2510.04156` v1) 与 Fischler–Rivoal (预印本 `arXiv:2610.16603` v1) 中**负搜索未见此精确阶乘整除表述**（覆盖局限见 §3） | [`verify_mixed_eg_hermite_pade_obstruction_20261125.py`](../../verification/verify_mixed_eg_hermite_pade_obstruction_20261125.py), [`.log`](../../verification/verify_mixed_eg_hermite_pade_obstruction_20261125.log) |
| **M1b**：混合级数 $F(z)=\alpha e^{\beta z}+G(z)$ 对 CDT 算术全纯界之超指数分母与有限半径冲突（$\log D_N(F)\ge N\log N-O(N)$ vs $\log\rho\le\log(4R_G)$） | **1. 无条件障碍诊断** + **5. 文献核查** | **已核实**：逐素数超度量下界在 $N=20..200$、4 类 $G$-函数上 100% 实测成立 | 对照 CDT (`arXiv:2408.15403v2` §2.2 & Thm 2.7.1) 分母型 $[1,\dots,bn]^\sigma$ 的直接排斥诊断 | 同上脚本 §5 |
| **M2a**：一般整数 Möbius 变换 $y=(ae+b)/(ce+d)$（$\Delta=ad-bc\neq 0$）之精确阈值 $J_0(a,b,c,d)$、窗口周期 $T=2|\Delta|$ 与首数字增幅 $W_{j+T}=(b_j+4G_j^2, S_j)$ | **1. 无条件模型结果（Paper 1 §3 直接推广）** + **5. 与 Elsner–Havens 部分重叠** | **已核实**：`mpmath`（动态 $350+$ 至 $700+$ 位）全量通过 40 组矩阵（含 $|\Delta|=1..16$ 与极端小分母反例 $M=\begin{pmatrix}39&-106\\71&-193\end{pmatrix}$） | 直接推广 Paper 1 `thm:affine-window`；与 **Elsner–Havens (2023)** Thm 1 / Ex 1（已定义 $G_n$ 并证收敛分数转移）及 Matthews–Walters (1970) / HBCM (2020) 部分重叠；Elsner–Havens (2025 Springer 专著) 受付费墙限制**未核到全文** | [`verify_mobius_e_full_conv_20261125.py`](../../verification/verify_mobius_e_full_conv_20261125.py), [`.log`](../../verification/verify_mobius_e_full_conv_20261125.log) |
| **M2b**：$a_n(M(e))\to\infty \iff r_j=1$ 最终成立 $\iff M(e)$ 属 $\{(e+1)/2,\,(e+1)/4,\,(e+3)/4\}$ 之 3 条 $\mathrm{PGL}_2(\mathbb{Z})$-轨道 | **1. 无条件模型分类（Paper 1 `cor:affine-single` 推广）** | **已核实**：基于左 $\mathrm{GL}_2(\mathbb{Z})$ Hermite 标准型证明 + 全覆盖穷举 $|\Delta|\le 40$ 共 `1240` 个本原 HNF（及 $|\Delta|\le 16$ 全连分数实测）精确仅命中此 3 类 | 推广 Paper 1 [`cor:affine-single`](../01_main_paper/paper1_e_plus_pi.tex#L828-L882)；在 `x82.pdf` 与 `2002.12644v1` 中负搜索未见此 3-轨道刻画（2025 专著未核到） | 同上脚本 §3 |
| **M2c**：$e$ 全收敛序列 $(p_n/q_n)_{n\ge -1}$ 之恒等式 $q_{3j\mp 1}=(Q_{j+1}\mp Q_j)/2$（$j\ge 0$）、KL 完整离散谱 $\{0\}\cup\{k/2:k\ge 2\}\cup\{\infty\}$、零能级缩回 $\mathbb{Z}+\mathbb{Z}e$、原始谱 $\frac12\mathbb{Z}_{\ge 0}\cup\{\infty\}$ 及精确规范基 | **1. 无条件新结果（Paper 2 衍生候选）** + **5. 零能级复现 KL 1991** | **已核实**：$j=0..44$ 恒等式、三类模 3 权重收敛及 8 个构造见证点在 350 位下全量核验；实测发现原始极限 $w_n\|q_n x\|\to k/2$ 在 $k\ge 3$ 为空集（修正草稿细节） | 零能级复现 Kraaikamp–Liardet (`1991`, `10.1090/s0002-9939-1991-1062392-7`)；正能级离散谱（含 $(0,1)$ 首隙与 $k=2$ 基 5 / $k\ge 3$ 基 $2k+1$ 规范）为 Paper 2 选定子列理论向 $e$ 全收敛列之精确推广 | 同上脚本 §4–§5 |

> **它们没做到什么（红线声明）**：
> 1. **未证明 $e+\pi$、$e\pi$、$e-\pi$、$\pi/e$ 中任何一数的无理性或超越性**，亦未降低原问题的核心难度。
> 2. **M1 未给出“所有可能分析/Padé 构造皆不可能”的元定理**：如 §1.3 详述，整除下界本身不能单独封死固定点余项趋零，且变换评估点 $z_n\to 0$、Borel 变换或子松弛度 $M\le 2n+O(1)$ 均不在 M1 阻断范围内。
> 3. **M2 仅刻画 $\mathbb{Q}(e)$ 中的 Möbius 轨道与 $e$ 自身的全收敛逼近谱**：对于具体常数 $\pi$ 是否落在任何 Hurwitz 轨道或 $e$ 轨道零水平集中，依然没有任何无穷子列输入。

---

## §1 Route M1：混合 $(1, e^z, G(z))$ Hermite–Padé 整除爆炸与 CDT 算术全纯障碍

### 1.1 精确命题与逐行证明核查

**命题 M1a（混合 $(1, e^z, G(z))$ 线性形式阶乘整除定理）**  
设 $G(z)=\sum_{k=0}^\infty b_k z^k\in\mathbb{Q}[[z]]$，对每个 $m\ge 0$ 记 $D_m(G)\in\mathbb{Z}_{\ge 1}$ 为满足 $D_m(G)b_k\in\mathbb{Z}$（$\forall\,0\le k\le m$）的公倍数分母。设 $P,Q,S\in\mathbb{Z}[z]$ 为任意整系数多项式，满足 $Q\not\equiv 0$、$d:=\deg Q\ge 0$（首项系数 $Q_d\neq 0$），且 Taylor 余项满足
\[
R(z):=P(z)+Q(z)e^z+S(z)G(z)=\sum_{k=M}^\infty r_k z^k=O(z^M),\qquad M\ge d+1.
\]
则**不依赖 $\deg P$ 与 $\deg S$ 的任何上界**，恒有整除关系
\[
(M-1-d)!\;\Big|\; D_{M-1}(G)\cdot d!\cdot Q_d,
\qquad\text{从而}\qquad
\|Q\|_\infty \ge |Q_d| \ge \frac{(M-1-d)!}{d!\,D_{M-1}(G)}.
\]

**逐行推导核查（修复/强化的边界假设）**：
1. 记 $\Phi_Q(X):=\sum_{j=0}^d Q_j\,X(X-1)\cdots(X-j+1)\in\mathbb{Z}[X]$。其次数恰为 $d$ 且首项系数为 $Q_d$。
2. 对**所有**整数 $k\ge 0$（包括 $0\le k<d$ 的边界情形！因为在 $j>k$ 时下降幂 $k(k-1)\cdots(k-j+1)$ 中必含因子 $(k-k)=0$），$[z^k]\bigl(Q(z)e^z\bigr)=\sum_{j=0}^{\min(k,d)}\frac{Q_j}{(k-j)!}=\frac{\Phi_Q(k)}{k!}$。
3. 当 $0\le k\le M-1$ 时，$0=r_k=P_k+\frac{\Phi_Q(k)}{k!}+\sum_{\ell=0}^{\min(k,\deg S)} S_\ell b_{k-\ell}$（若 $k>\deg P$ 则 $P_k=0$）。两边同乘 $k!\,D_{M-1}(G)$：注意**即使 $k\le\deg P$**，项 $k!\,D_{M-1}(G)P_k$ 仍自动被 $k!$ 整除！故对一切 $0\le k\le M-1$ 均有
   \[
   k!\;\Big|\; D_{M-1}(G)\,\Phi_Q(k).
   \]
   （注：由此可见草稿无需额外限定 $k>\deg P$ 或 $\deg P\le n$。）
4. 取起点 $m:=M-1-d\ge 0$，作 $d$ 阶前向差分 $\Delta^d\Phi_Q(m)=\sum_{r=0}^d (-1)^{d-r}\binom{d}{r}\Phi_Q(m+r)=d!\,Q_d$。因 $0\le m\le m+r\le M-1$，故 $m!\mid (m+r)!\mid D_{M-1}(G)\Phi_Q(m+r)$ 对每项成立，求和即得 $(M-1-d)!\mid D_{M-1}(G)\,d!\,Q_d$。$\square$

**命题 M1b（CDT 算术全纯界在混合函数 $F(z)=\alpha e^{\beta z}+G(z)$ 上的无条件失效）**  
设 $\alpha,\beta\in\mathbb{Q}^\times$，$G(z)=\sum_{k\ge 0} b_k z^k\in\mathbb{Q}[[z]]$ 具有有限收敛半径 $R_G\in(0,\infty)$ 及亚阶乘分母增长 $\log D_N(G)=o(N\log N)$（例如一切 $G$-函数满足 $\log D_N(G)=O(N)$）。置 $F(z)=\alpha e^{\beta z}+G(z)=\sum_{k\ge 0} c_k z^k$，记 $D_N(F)=\operatorname{lcm}_{0\le k\le N}\operatorname{denom}(c_k)$。
1. **分母速率 $\tau(F)=\infty$**：对任意素数 $p$，若 $v_p(\alpha\beta^N/N!)<-v_p(D_N(G))$，则超度量三角不等式强制 $v_p(c_N)=v_p(\alpha\beta^N/N!)$，故对一切素数 $p$ 恒有
   \[
   v_p(D_N(F))\ge \max\!\big(0,\; v_p(N!)-v_p(D_N(G))-v_p^+(\operatorname{num}(\alpha))-N\,v_p^+(\operatorname{num}(\beta))\big).
   \]
   对全部素数 $p$ 乘 $\log p$ 求和（利用 $\max(0,A-B)\ge A-B$，无需额外对 $p>\sqrt{N}$ 或 $b_p$ 单独分类），得
   \[
   \log D_N(F)\ge \log(N!)-\log D_N(G)-O_{\alpha,\beta}(N)=N\log N-O(N).
   \]
   从而 Calegari–Dimitrov–Tang（[`arXiv:2408.15403v2`](https://arxiv.org/abs/2408.15403) §2.2 Eq. (2.2.2) 与 Thm 2.7.1）所要求的全纯模空间分母指标 $\tau(F)=\limsup_{N\to\infty}\frac{\log D_N(F)}{N}=+\infty$。
2. **共形半径有界**：因 $G$ 在圆盘边界 $|z|=R_G$ 必有奇点而 $e^{\beta z}$ 整函数不消去该奇点，任何使 $F\circ\varphi$ 单叶/亚纯延拓的指点可缩区域 $(\Omega,0)$ 必绕开该奇点，由 Koebe $1/4$ 定理有 $\rho(\Omega,0)\le 4R_G<\infty$，即 $\log\rho(\Omega,0)<\infty$。因此 CDT 核心条件 $\log\rho(\Omega,0)>\tau$ 无条件溃败（$\log\rho<\infty=\tau$）。

### 1.2 对抗性边界检验与精确适用局限（M1 关闭了什么、没关闭什么）

按 `proof-reasoning` 纪律，严查以下边界：
1. **整除下界自身并不直接阻断 $|R(z_0)|\|Q\|_\infty\to 0$**：当 $M=(2+\delta)n$（$\delta\in(0,1)$）且 $d=n$ 时，命题 M1a 仅给出 $|Q_d|\ge \frac{((1+\delta)n-1)!}{n! D_M(G)}=\exp(\delta n\log n-O(n))$。而另一方面，$M!\approx \exp((2+\delta)n\log n)$，因此若仅凭该整除下界，$1/M!$ 的衰减理论上仍可压过 $\exp(\delta n\log n)$。**真正导致 Padé 彻底爆炸的机理**在于：消去 $P,Q$ 后，关于 $(S_0,\dots,S_n)$ 的 $(M-2n-1)$ 条线性方程（由 $\Delta^{n+1}\Phi_Q(k)=0$ 导出）系数矩阵元素含 $(k+n+1)!\,D_{M-1}(G)\sim\exp(n\log n)$，使得 LLL 极小整数解（及对角 Padé 唯一解）实测呈现 $\log\|Q\|_\infty,\log\|S\|_\infty\asymp \Theta(n^2\log n)$，一举压垮 $M!=\exp(\Theta(n\log n))$，迫使余项 $|R(z_0)|$ 反向指数爆炸！
2. **M1 不适用（绕行）的精确边界条件**：
   - **情况 A（零松弛/亚临界阶 $M\le 2n+O(1)$）**：当 $M\le 2n+1$ 时存在 $Q\equiv 0$ 的纯 $(1,G)$ 线性形式（如 $n=8, M=16$ LLL 给出 $\log_{10}|R(1/5)|=-8.83$，或 $\delta=0$ 高阶时直接落入 $Q\equiv 0$ 子空间）；当 $M=2n+2$ 时 $(M-1-d)!/d!=n+1$ 仅多项式增长（$n=10, M=22$ 下 LLL 给出 $\log_{10}\|Q\|_\infty=10.61, \log_{10}|R(1/5)|=-10.18$）。
   - **情况 B（变尺度求值点 $z_n\to 0$，如 $z_n=z_0/n$）或积分核重整化**：固定 $z_0$ 的多项式 Padé 假定 $z_0\neq 0$ 固定；若改为 $e^{z/n}$ 或指数型变尺度积分（但此时不再直接给出 $e^{z_0}$ 与 $G(z_0)$ 同一固定点值）。
   - **情况 C（Borel / 逆 Borel 变换）**：Borel 变换把 $e^z$ 映为有理 $G$-函数 $\frac{1}{1-z}$，却把 $\arctan z$ 映为收敛半径 $0$ 的 Gevrey-1 级数（$\rho=0$ 仍失败）；逆 Borel 变换把 $\arctan z$ 映为 $E$-函数 $\operatorname{Si}(z)$，同入 Siegel–Shidlovskii 范畴但无法在代数点取值同时恢复 $\pi$ 与 $e$。

### 1.3 可复查数值与符号验证结果（`verify_mixed_eg_hermite_pade_obstruction_20261125.py`）

运行命令：`py -3 verification/verify_mixed_eg_hermite_pade_obstruction_20261125.py`（退出码 **`0`**，耗时 **`0.59s`**）：
- **SymPy 精确符号核查**：$d=1..5$、$M=d+1..12$（取超越 $d$ 的 $\deg P=d+3,\deg S=d+2$）全部确认 $(M-1-d)!$ 商为 $\mathbb{Z}[P,Q,S,B,D_G]$ 精确整系数多项式。
- **104 组非对称次数边界算例**：覆盖 $4\arctan z$、$\log(1+z)$、$(1-4z)^{-1/2}$（注意此处 $D_m=1$ 为整系数 $G$-函数！）与 $\operatorname{Li}_2(z)$，100% 满足整除。
- **对角 Hermite–Padé ($M=3n+2, n=1..7$)**：全部呈 $\Theta(n^2\log n)$ 系数与余项爆炸（例如 $4\arctan z, z_0=1/5$ 在 $n=7, M=23$ 时 $\log_{10}\|Q\|_\infty=72.558,\log_{10}\|S\|_\infty=61.152,\log_{10}|R(1/5)|=+39.87$；$(1-4z)^{-1/2}, z_0=1/8$ 在 $n=7$ 时 $\log_{10}\|Q\|_\infty=97.154,\log_{10}|R(1/8)|=+65.45$）。
- **LLL 松弛对比（$4\arctan z, z_0=1/5, n=4,6,8,10$）**：在 $\delta=0.5$（$M=2.5n$）下，LLL 极小解仍于 $n=8,10$ 爆发为 $\log_{10}\|Q\|_\infty=30.635, 53.678$ 且余项反转增长至 $\log_{10}|R(1/5)|=+10.240, +27.369$；仅当 $M=2n$ 或 $2n+2$ 时余项保持负指数，且 $n=8, M=16$ 最短向量直接退化为 $Q\equiv 0$（`Q=0_short?=True`）。
- **CDT 超度量核验（$N=20..200$）**：在 $N=200$ 时，4 类 $G$-函数均满足 $\tau_N=\frac{\log D_N(F)}{N}\in[4.3141, 4.8383]\gg \log(4R_G)\in\{0.0000, 1.3863\}$，且 $\log D_N(F)\ge \log(N!)-\log D_N(G)-O(N)$ 逐素数成立。

---

## §2 Route M2：一般 Möbius 窗口、3-轨道分类与 $e$ 全收敛谱

### 2.1 一般 Möbius 窗口期定理（M2a）与对 `08ff5eb8` 的两处关键修正

设 $M=\begin{pmatrix} a&b\\ c&d\end{pmatrix}\in M_2(\mathbb{Z})$ 满足 $\Delta:=ad-bc\neq 0$，规范化符号使 $ce+d>0$，置 $y=M(e)=\frac{ae+b}{ce+d}$。记 $(P_j,Q_j)$ 为 $e$ 的选定 Hermite 收敛子（$P_0=Q_0=1$，$P_1=3, Q_1=1$，$X_{j+1}=(4j+2)X_j+X_{j-1}$），定义
\[
U_j=aP_j+bQ_j,\quad V_j=cP_j+dQ_j,\quad G_j=\gcd(U_j,V_j)>0,\quad p_j'=\frac{U_j}{G_j},\quad q_j'=\frac{V_j}{G_j}.
\]
**定理 M2a（一般 Möbius 窗口期与首数字增量）**  
置 $T:=2|\Delta|$。定义显式阈值 $J_0(a,b,c,d)$ 为满足以下三条的最小整数 $j\ge 1$：
\[
j\ge\lceil 3|\Delta|/2\rceil,\qquad Q_j(ce+d)>2|\Delta|,\qquad Q_j^2(2j+1)(ce+d)>2|c|.
\]
则对一切 $j\ge J_0$：
1. $V_j>0$，$q_j'\ge 2$ 且严格递增，$p_j'/q_j'=p_{k(j)}(y)/q_{k(j)}(y)$ 为 $y$ 的正则收敛分数，其中 $k(j)$ 与 $j$ 有固定奇偶偏移（$\Delta>0$ 时同奇偶，$\Delta<0$ 时异奇偶）；
2. 窗口长度 $r_j:=k(j+1)-k(j)\ge 1$ 恒为奇数，且连续锁定行列式恒等于 $D_j:=|p_j'q_{j+1}'-p_{j+1}'q_j'|=\frac{T}{G_j G_{j+1}}\in\mathbb{Z}_{\ge 1}$，进而 $r_j=1\iff D_j=1\iff G_j G_{j+1}=T$；
3. 对一切 $j\ge J_0+1$，窗口具有周期 $T$：$r_{j+T}=r_j$，后缀全等，且首数字精确移位 $W_{j+T}=(b_j+4G_j^2, S_j)$。

**针对 `08ff5eb8` 草稿的两处关键纠偏**：
- **纠偏 1（阈值 `j > |Delta| + 3` 对 $c\neq 0$ 不足）**：若 $c=Q_k, d=-P_k$，即使 $|\Delta|=1$ 也可使 $ce+d$ 极小。例如脚本构造的对抗矩阵 $M=\begin{pmatrix}39&-106\\71&-193\end{pmatrix}$ 具有 $\Delta=-1$（草稿阈值 $|\Delta|+3=4$），但实测在 $j=3$ 处 **$V_3=71\cdot 193 - 193\cdot 71=0$**（$j=1,2$ 时 $V_1=-20, V_2=2$），说明必须引入依赖 $(ce+d)^{-1}$ 与 $|c|$ 的上述三条阈值（该矩阵在我们的 $J_0=5$ 下全量通过）。
- **纠偏 2（窗口周期 $T=2|\Delta|$ vs 普通连分数最小 Hurwitz 周期 $p_{\min}$）**：$T=2|\Delta|$ 是**窗口编号 $j\mapsto j+T$** 的周期（其背后是 $e$ 的递增商矩阵 $\pmod{2|\Delta|}$ 阶数 $\omega(4,2;T)=1$，而一般递增递推 $(cj+d)$ 如 $\tanh 1$ 须乘以 $\omega(c,d;T)$），**并非**普通部分商下标 $n$ 的最小 Hurwitz 周期 $p_{\min}$。一个 $T$-周期窗口共包含 $R_T=\sum_{i=j}^{j+T-1}r_i$ 个普通部分商，而 $p_{\min}$ 等于最小窗口周期 $T_{\min}\mid T$ 所含部分商之和 $R_{T_{\min}}$（例如 $e$ 本身 $T=2, T_{\min}=1, p_{\min}=3$；$(e+1)/(e-1)$ 有 $T=4, T_{\min}=1, p_{\min}=1$；$(5e+2)/(3e+4)$ 有 $\Delta=14, T=28, T_{\min}=14, R_T=112, p_{\min}=56$）。

### 2.2 精确 3 条 $\mathrm{PGL}_2(\mathbb{Z})$-轨道分类（M2b）

**定理 M2b（发散部分商 Möbius 轨道完备分类）**  
设 $M\in M_2(\mathbb{Z})$ 本原且 $\det M=\pm\Delta\neq 0$，$y=M(e)$。以下四条件等价：
1. $\lim_{n\to\infty} a_n(y)=+\infty$；
2. 最终所有窗口长度 $r_j=1$（等价地，在 $j>J_0$ 后连续 5 个窗口均有 $r_j=1$）；
3. 连续 6 个指标满足 $G_j G_{j+1}=2|\Delta|$；
4. $y$ 落在且仅落在以下 **3 条互不相交的 $\mathrm{PGL}_2(\mathbb{Z})$-轨道** 之一：
   \[
   \frac{e+1}{2}=[1;1,6,10,14,18,\dots],\qquad
   \frac{e+1}{4}=[0;1,13,5,28,9,44,\dots],\qquad
   \frac{e+3}{4}=[1;2,3,20,7,36,11,\dots].
   \]

**证明骨架核查**：
- 由 $\det\begin{pmatrix}P_j&P_{j+1}\\Q_j&Q_{j+1}\end{pmatrix}=2(-1)^{j+1}$ 知对奇素数 $\ell$，$(P_j,Q_j)^T$ 与 $(P_{j+1},Q_{j+1})^T$ 在 $\mathbb{F}_\ell^2$ 线性无关。若 $\ell\mid\Delta$，则因 $M$ 本原，$\ker(M\bmod\ell)$ 一维且不能同时含连续两项，故 $\ell\nmid\gcd(G_j,G_{j+1})$；若出现连续 5 窗 $G_iG_{i+1}=2|\Delta|$，则在 $\ell\mid\Delta$ 下必连续 6 步交替出现 $v_\ell(G_i)>0$ 与 $0$，代入 $(4i+2)$ 递推得 $\ell\mid 8$，矛盾！故 $|\Delta|=2^b$。
- 利用 $\mathrm{PGL}_2(\mathbb{Z})$-等价对应于左乘 $\mathrm{GL}_2(\mathbb{Z})$ 不变性（$e$ 无理且非二次，故 $U M_1(e)=M_2(e)\iff U M_1=\pm M_2$），每个本原矩阵有唯一左 $\mathrm{GL}_2(\mathbb{Z})$ Hermite 标准型 $\begin{pmatrix}C&A\\0&B\end{pmatrix}$（$CB=2^b, 0\le A<B, \gcd(A,B,C)=1$）。若 $C=2^\gamma\ge 2$，则 $B=1$ 时 $V_j=Q_j$ 为奇，$B=2^\beta\ge 2$ 时 $A$ 必为奇故 $U_j=2^\gamma P_j+AQ_j$ 为奇，均有 $G_j=1$；仅当 $C=1, B=2^b$（即 Paper 1 `cor:affine-single` 仿射情形）可取偶 $G_j$，由 `cor:affine-single` 知连续 5 窗 $r_j=1$ 充要条件为 $b\in\{1,2\}$、$A$ 奇，即唯一三组 HNF $(1,1,2), (1,1,4), (1,3,4)$。
- 反方向若某 $j>J_0$ 有 $r_j>1$，则固定非空后缀 $S_j$ 随 $j+tT$ 无穷次重复，故 $\liminf a_n(y)<\infty$。此 3 条轨道由各自标准型唯一性及连分数尾部同余类（$2\bmod 4$ vs $(1\bmod 4, 12\bmod 16)$ vs $(3\bmod 4, 4\bmod 16)$）双重隔离。

### 2.3 $e$ 的全收敛序列 $(p_n/q_n)_{n\ge -1}$ 完整谱与规范理论（M2c）

记 $e=[2;1,2,1,1,4,1,1,6,\dots]$ 的全部正则收敛分数为 $(p_n/q_n)_{n\ge -1}$（约定 $p_{-1}/q_{-1}=1/0, p_0/q_0=2/1$）。对所有 $j\ge 0$ 成立精确恒等式：
\[
q_{3j-2}=Q_j\ (j\ge 1),\qquad q_{3j-1}=\frac{Q_{j+1}-Q_j}{2},\qquad q_{3j}=\frac{Q_{j+1}+Q_j}{2},
\]
以及分子同步恒等式 $p_{3j-1}=(P_{j+1}-P_j)/2$、$p_{3j}=(P_{j+1}+P_j)/2$（由 $a_{3j}=a_{3j+1}=1$ 直接消元即得，且 $j=0$ 亦成立！）。

定义全收敛 Kraaikamp–Liardet 权重 $w_n:=\frac{1}{q_n|q_n e-p_n|}=a_{n+1}+[0;a_{n+2},\dots]+[0;a_n,\dots,a_1]$。则三类模 3 权重满足：
\[
\frac{w_{3j-2}}{2j}\longrightarrow 1,\qquad w_{3j-1}\longrightarrow 2,\qquad w_{3j}\longrightarrow 2\qquad (j\to\infty).
\]
对任意 $x\in\mathbb{R}$，置 $M_j=\operatorname{round}(Q_j x)$、$u_j=Q_j x-M_j$、缺陷 $d_j(x)=M_{j+1}-(4j+2)M_j-M_{j-1}$。当 $\Lambda_{\text{sel}}(x)=\limsup j\|Q_j x\|<\infty$ 时，由 $q_{3j\mp 1}x=\frac{M_{j+1}\mp M_j}{2}+\frac{u_{j+1}\mp u_j}{2}$ 与 $u_j\to 0$ 立得：
1. **KL 标准化全谱与零能级坍缩**：
   \[
   \Lambda_{\text{full}}^{\text{KL}}(x):=\limsup_{n\to\infty}\frac{\|q_n x\|}{q_n|q_n e-p_n|}=\max\!\Big(2\Lambda_{\text{sel}}(x),\;\mathbf{1}_{\{M_{j+1}\not\equiv M_j\!\!\pmod 2\text{ i.o.}\}}\Big).
   \]
   由于当 $M_{j+1}\equiv M_j\pmod 2$ 最终成立时有 $d_j(x)\equiv M_{j+1}-M_{j-1}\equiv 0\pmod 2$，故 $2\Lambda_{\text{sel}}(x)=\frac{1}{2}\limsup|d_j(x)|\in\mathbb{Z}_{\ge 0}$ **永不取 $1/2$**；而当 $M_{j+1}\not\equiv M_j\pmod 2$ 无穷次发生时指标函数压住下界 $1$。从而：
   - **完整离散谱**：$\Lambda_{\text{full}}^{\text{KL}}(\mathbb{R})=\{0\}\cup\{k/2:k\in\mathbb{Z}_{\ge 2}\}\cup\{\infty\}=\{0,1,3/2,2,5/2,3,\dots\}\cup\{\infty\}$，首隙为巨型区间 $(0,1)$！
   - **零能级坍缩**：$\{\Lambda_{\text{full}}^{\text{KL}}=0\}=\{\Lambda_{\text{full}}^{\text{KL}}<1\}=\mathbb{Z}+\mathbb{Z}e$（将在 Paper 2 中进入零能级的半陪集 $\frac{1+e}{2}+\mathbb{Z}+\mathbb{Z}e$ 精确驱逐至能级 $1$，完整复现 Kraaikamp–Liardet 1991 定理）。
   - **精细规范与无符号极限修正**：能级 $\{\Lambda_{\text{full}}^{\text{KL}}=1\}=\{\Lambda_{\text{sel}}\le 1/2\}\setminus(\mathbb{Z}+\mathbb{Z}e)$ 临界规范基为 **$5$**（$d_j\in\{0,\pm 1,\pm 2\}$）；对一切 $k\ge 3$，$\{\Lambda_{\text{full}}^{\text{KL}}=k/2\}=\{\Lambda_{\text{sel}}=k/4\}$ 临界规范基为 **$2k+1$**。另一方面，对**无符号极限集合** $\{x:\lim_{n\to\infty} w_n\|q_n x\|=c\}$：能级 $c=0$ 为 $\mathbb{Z}+\mathbb{Z}e$；能级 $c=1$ 要求 $d_j\in\{\pm 2\}$ 且 $M_{j+1}\not\equiv M_j$ 最终恒成立（二元基 $2$）；而对一切 $k\ge 3$，因 $w_{3j-1}\|q_{3j-1}x\|$ 仅能趋于 $0$ 或 $1$，**该极限集为空集**（此为与选定子列三分法的关键细化）。
2. **原始商标准化全谱**：$\Lambda_{\text{full}}^{\text{raw}}(x):=\limsup_{n\to\infty} a_{n+1}\|q_n x\|=\max\big(2\Lambda_{\text{sel}}(x),\,\frac12\mathbf{1}_{\{M_{j+1}\not\equiv M_j\!\!\pmod 2\text{ i.o.}\}}\big)$，全谱为 $\frac{1}{2}\mathbb{Z}_{\ge 0}\cup\{\infty\}$，零能级仍为 $\mathbb{Z}+\mathbb{Z}e$，且对一切 $k\ge 1$ 能级 $k/2$ 的临界规范基均为 $2k+1$。

### 2.4 可复查数值验证结果（`verify_mobius_e_full_conv_20261125.py`）

运行命令：`py -3 verification/verify_mobius_e_full_conv_20261125.py`（退出码 **`0`**，耗时 **`1.17s`**，动态 `mpmath` 精度 `350`–`700+` 位）：
- **40 组 Möbius 矩阵验证**：覆盖 $\Delta\in\{\pm 1,\dots,\pm 16\}$、非本原矩阵（如 $2(e+1)/4$）、负输出矩阵（如 $(3e-5)/1$）及对抗矩阵 $M=\begin{pmatrix}39&-106\\71&-193\end{pmatrix}$，在各自严格阈值 $J_0$ 之上 100% 满足 $V_j>0$、收敛子锁定、$D_j=T/(G_j G_{j+1})$、$r_{j+T}=r_j$ 与 $W_{j+T}=(b_j+4G_j^2, S_j)$。
- **$\mathrm{GL}_2(\mathbb{Z}/T\mathbb{Z})$ 矩阵阶数 $\omega(c,d;T)$**：实测 $e$（$4j+2$）对所有偶数 $T\in\{2,4,6,8,10,12\}$ 均满足 $\omega=1$（奇数 $T=3,5$ 时 $\omega=2$），而 $\tanh(1)$（$2j+1$）在 $T=2,4,8,10$ 取 $\omega=3$。
- **3-轨道全覆盖穷举**：$|\Delta|\le 40$ 共 `1240` 个本原 HNF（及 $|\Delta|\le 16$ 全连分数检查）精确且仅命中 `(1,1,2)`, `(1,1,4)`, `(1,3,4)`。
- **全收敛恒等式与谱见证**：$j=0..44$ 全部恒等式精确成立；$j=35$ 时 $w_{3j-2}/(2j)=1.014386$, $w_{3j-1}=2.000579$, $w_{3j}=1.999807$；$d_r=1,2,3,4,5$ 叠缩见证及陪集 $(1+e)/2$ 均精确命中预测能级（如 $(1+e)/2$ 得 $\text{KL}=1.0004, \text{raw}=0.5000$；$d_r=1$ 得 $\text{KL}=1.0001, \text{raw}=0.4999$）。

---

## §3 文献检索与先例边界表（双通道证据与覆盖局限）

> **检索范围与显式覆盖局限（遵循 `AGENTS.md` §3）**：本次通过本地 `search` MCP（Multi-engine Web + arXiv + Crossref/OpenAlex `paper_graph`）实际读取了多篇一手 PDF/摘要页面；**未直连** MathSciNet、zbMATH（`zbmath` 引擎 404 静默）及 Springer 2025 专著（ISBN `9783031995460`）付费墙后全文。故表中「未见」均指**在已读一手材料与上述可用检索引擎范围内的负搜索**，不代表已证明文献中绝对不存在先例。

| 文献与标识 | 实际读取范围（先读后写） | 核心内容与精确边界对照 |
| :--- | :--- | :--- |
| **Calegari–Dimitrov–Tang (2024 预印本)** [`arXiv:2408.15403`](https://arxiv.org/abs/2408.15403) (v2) | 读取 PDF 首页–p.21（§1–§2.7）及 p.163–190（§11–§15.1） | Eq. (2.2.2) 与 Thm 2.7.1 要求级数分母不快于 $A^{n+1}[1,\dots,bn]^\sigma$ 且 $\log\rho(\Omega,0)>b\sigma$。本文 **M1b** 据此给出混合系列 $\alpha e^{\beta z}+G(z)$ 的无条件超度量冲突证明。 |
| **Calegari–Dimitrov–Tang (2026 ICM)** `10.1137/25m1806776`（所读文本为预印本 [`arXiv:2510.04156`](https://arxiv.org/abs/2510.04156) v1，与已刊同题条目一致；刊本正文未另核） | 读取预印本 PDF p.1–11（含 §3.3） | §3.3 以 $A(z)=(1-4z^2)^{-1/2},\,B(z)=-2A(z)\arcsin(2z)$（$[1,\dots,n]$ 分母）新证 $\pi$ 超越性，仍属纯 $G$-函数/对数二面体构造，不涉 $e^z$ 混合。 |
| **Fischler–Rivoal (2026 预印本)** [`arXiv:2610.16603`](https://arxiv.org/abs/2610.16603) (v1) | 读取 PDF p.1–4（Thm 1.1–1.3） | 证 $E$-函数值环 $\mathbf{E}$ 非域，给出 $e+1\notin\mathbf{E}^\times$；仍未涉及 $\mathbf{E}\cap\mathbf{G}=\overline{\mathbb{Q}}$ 与混合 $(1,e^z,G)$ Padé 阶乘整除障碍。 |
| **Matthews–Walters (1970)** `10.1017/S0305004100057108` | 通过 `paper_graph` 与 Paper 1 既有核对记录 | 仅处理齐次情形 $(m/n)e^{1/q}$（$b=c=0$）；M2a/M2b 覆盖任意 $c\neq 0$ 与 $a,b\neq 0$。 |
| **Havens–Barbero–Cerruti–Murru (2020)** `10.1007/s40993-020-0187-5`（所读文本为 [`arXiv:2002.12644`](https://arxiv.org/abs/2002.12644) v1，同篇 *Res. Number Theory* 2020 已刊论文） | 读取预印本 PDF 全文（18 页） | 以 Raney 矩阵完整解出 $|\det\sigma|=2$ 情形，并在 p.2 明确指出 $|\det\sigma|>2$ 需不同方法。M2a/M2b 用选定收敛子窗口矩阵解决任意 $\Delta\neq 0$。 |
| **Elsner–Havens (2023)** *INTEGERS* 23, #A82 (`10.5281/zenodo.10075884`, `x82.pdf`) | 读取 PDF p.1–19（Thms 1–6 & Ex. 1–2） | **关键已有先例**：已引入 $G_n=\gcd(ap_n+bq_n, cp_n+dq_n)$ 与 $u_n/v_n$，并在 Thm 1(3)–(4) 与 Ex. 1 中证对 $e$ 足够大时 $u_{3k+1}/v_{3k+1}$ 为 $\sigma(e)$ 的收敛分数！与 M2a 重合于 $G_n$ 定义及收敛子转移，但未给出 $r_{j+T}=r_j$、$W_{j+T}=(b_j+4G_j^2, S_j)$ 或 3-轨道完备分类。 |
| **Elsner–Havens (2025 专著)** Springer (`978-3-031-99546-0`) & `continuedfractions.net` | 读取官网主页与勘误表（**专著正文付费墙未核到**） | 官网目录显示包含 *"Linear fractional transforms; Characteristic gcd sequences $G(e)$"*；因未读全书，M2a/M2b 与该书可能存在额外重合，须保持诚实未核标注。 |
| **Kalinin–Komatsu (2026 预印本)** [`arXiv:2604.09726`](https://arxiv.org/abs/2604.09726) (v1) | 读取 arXiv 摘要页 | 研究 $e^{1/s}$ 与 $\tanh$ 连分数加权误差和恒等式，不涉及 Möbius 3-轨道或 $e$ 全收敛离散谱。 |
| **Kraaikamp–Liardet (1991)** `10.1090/s0002-9939-1991-1062392-7` | 通过 Paper 2 `sec:prior` 核对 | 仅刻画全收敛零水平集 $\mathbb{Z}+\mathbb{Z}\alpha$ 及一般下界 $1/4$；M2c 给出 $e$ 专属的 $(0,1)$ 首隙、全部半整数能级及精细规范。 |

---

## §4 后续整合与 Paper 2 裂变建议

1. **Route M1 $\to$ 纳入 Paper 1 §6（`sec:obstructions` / `sec:feasibility` 新障碍子节，不另拆独立论文）**：
   - M1 数学内容精炼（6 行整除定理 + 3 行超度量不等式），对 $e+\pi$ 属明确的障碍坐标，不宜充当独立期刊论文，极适合作为 Paper 1 第 6 章继 Niven、四指数、$\mu(\pi)$ 平移之后的第 5 条严格障碍（"Mixed $E/G$ Hermite–Padé and CDT Holonomy Obstruction"）。
2. **Route M2c（$e$ 全收敛谱与精确规范）$\to$ 强烈建议并入 Paper 2A+2B（或作为独立短附注 + Lean 4 模块）**：
   - Paper 2 当前主要建立在“每 3 个选定收敛子 $Q_j=q_{3j-2}$”之上，审稿人极易提问“为何只取子列而不取 $e$ 的**全部**收敛分母 $q_n$？”；M2c 用 2 页即可彻底解答该问题，展示零水平从 $L$ 坍缩回 $\mathbb{Z}+\mathbb{Z}e$、KL 首隙从 $1/4$ 跳变为 $(0,1)$、正能级谱为 $\{k/2:k\ge 2\}$、以及 $k\ge 3$ 时全收敛无符号精确极限集为空集等锐利差异，且可直接在 `EulerConvergents.lean` 之上零新增公理形式化。
3. **Route M2a + M2b（一般 Möbius 窗口与 3-轨道分类）$\to$ 暂入 Paper 1 §3 扩充备选，待核对 Elsner–Havens (2025) 专著后再定外部投稿**：
   - 在获得并核对 Elsner–Havens (2025) 第 II/III 部分关于 `Characteristic gcd sequences G(e)` 的准确命题前，禁止在对外投稿中宣称 M2a 拥有全量优先权；当前可作为 Paper 1 §3 `thm:affine-window` 与 `cor:affine-single` 的完整内部推广留档。
