# Kahane 问题 Q6：幂次模 1 落在区间内的集合的维数（研究笔记，2026-11-25）

**一句总判断**：这是一个**有名有姓的公开问题**：Kahane（C. R. Acad. Sci. Paris 352 (2014)，问题 Q6）提出，候选值为 $\log(2\varepsilon X)/\log X$。本笔记对**几乎每一个**目标序列 $(b_n)$ 证明了这一候选值是上界（定理 2），并证明了一个更弱的下界（定理 3）。精确下界已归约到一个尚未证明的引理（引理 R）。对每一个确定的 $(b_n)$，Kahane 的原问题仍完全开放。

本笔记与 $e+\pi$ 无关，对 $e+\pi$ 无推进。

| 结果 | 类别（AGENTS.md） | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| 定理 2：对几乎每个 $(b_n)$，$\dim_H(E(\varepsilon)\cap[1,X])\le\log(2\varepsilon X)/\log X$；与 Kahane 的下界 (3) 合起来，两侧相差约 $2/(X\log X)$ | 无条件新结果（窄；标准第一矩方法） | 本人推导，经一次独立对抗审阅，按意见修改 | 负搜索未见先例（范围见 §0） | §2 |
| 定理 3：对几乎每个 $(b_n)$，局部维数 $\ge\mathbb E\log f_L(U)/\log v$，$L=2\varepsilon(v-1)>1$ | 无条件新结果（窄） | 同上 | 负搜索未见；在 7 组样本中优于 Kahane 的 (3)，但并非处处更优（有反例） | §3d |
| 命题 P1、P2：二阶矩问题的正表示，以及"引理 R ⇒ D′ ⇒ 引理 D"的部分证明 | 等价改写与部分结果 | 同上 | — | §3b、§3c‴ |
| 精确下界（几乎处处） | 未证（依赖引理 R，并需能量形式与 0-1 律） | 开放 | — | §3、§3c‴ |
| 候选值对确定的 $(b_n)$（含 $b_n\equiv0$、$\frac12$）也成立 | 有限计算（佐证） | 脚本与日志可复查 | — | §4a |
| 鞅二阶矩有界；Fourier 能量按约 $1/(2\varepsilon v)$ 衰减 | 有限计算（佐证） | 同上 | — | §4b、§3c′ |

---

## 0. 问题与已知结果

记号：$\varepsilon\in(0,1/2)$，$(b_n)\subset[0,1)$，
$$E(\varepsilon)=E(\varepsilon,(b_n))=\{x>1:\ \lVert x^n-b_n\rVert<\varepsilon\ \text{对充分大的 } n\}.$$

| 来源 | 内容 | 核查状态 |
| :--- | :--- | :--- |
| J.-P. Kahane, *Sur la répartition des puissances modulo 1*, C. R. Acad. Sci. Paris Sér. I **352** (2014), 383–385, doi:10.1016/j.crma.2013.12.014 | **P3**：$\dim E(\varepsilon)=1$。证明中的式 (3)：$\dim E'\ge\log2\varepsilon(X-2)/\log X$（$E'\subset E(\varepsilon)\cap[1,X]$，$X$ 充分大）。**P6**：若 $X\le1/(2\varepsilon)$，$E(\varepsilon)\cap[1,X]$ "一般为空"；若 $X>1/(2\varepsilon)$，维数为正，原文 "je n'ai pas su la calculer"。**Q6**："Calculer la dimension de $E(\varepsilon)\cap[1,X]$ quand $X>\frac1{2\varepsilon}$. Un candidat possible est $\frac{\log2\varepsilon X}{\log X}$." | 本人从 PDF 抽取文本，逐字核对 P3、P6、Q6 与式 (3) |
| M. A. Lerma, *Distribution of powers modulo 1 and related topics*, arXiv:1312.5996（1995 年文本，Kahane 文中提及） | 全文 PDF 抽取后检索 "Hausdorff"、"dimension"，均 0 次出现；没有维数结果 | 已核（全文检索） |
| Bugeaud–Liao–Rams, arXiv:1710.03596，定理 7 | 精确局部维数，但要求 $\log f'_{n+1}/\log f'_n\to\infty$，对 $x^n$ 不成立 | 已核（见 `verification/candidateA_precedent_search_20261125.md`） |
| Bugeaud–Moshchevitin arXiv:1009.4528；Schleischitz arXiv:1501.07176；Dobbs, *Enseign. Math.* 62 (2016)；Fan–Fan–Ye arXiv:2512.05690 | 全维数或可数 / 不可数阈值；没有给出 Q6 所求的精确值 | 由检索子代理读取原文（TeX 或 PDF），本人未逐字复核 |
| Pollington 1980；Bugeaud《Distribution modulo one and Diophantine approximation》(2012) 第 2 章 | — | **未核到**（付费墙） |

**先例检索结论**：没有找到解决 Q6 的文献，也没有找到"几乎每个 $(b_n)$ 下的上界"。这是**负搜索**，覆盖范围是：
- arXiv API、网页检索；
- 引用 Kahane 2014 的文献中已核的 4 篇；
- **未**查 MathSciNet、zbMATH、Google Scholar 的引用链。

---

## 1. 启发式

在 $x\approx v$ 附近，第 $n$ 层区间（前 $n$ 个约束都满足）长度约为 $2\varepsilon/(nv^{n-1})$。在 $x\mapsto x^{n+1}$ 下，它的像长约 $2\varepsilon v$，所以含约 $2\varepsilon v$ 个下一层区间，每个短约 $v$ 倍。等价说法：第 $n$ 层集合的 Lebesgue 测度每步乘以 $2\varepsilon$（即"$x^{n+1}\bmod1$ 在分形上等分布"）。由此得到局部维数的猜想值
$$d(v)=\frac{\log(2\varepsilon v)}{\log v},$$
它关于 $v$ 递增，在 $[1,X]$ 上的上确界正是 Kahane 的候选值。

---

## 2. 定理与证明

**定理 1（初等，对每个 $(b_n)$）**：对每个 $v>1$，$E(\varepsilon)$ 在 $v$ 处的局部维数不超过 $\log(2\varepsilon v+2\varepsilon+1)/\log v$。

*证明*：一个第 $n$ 层区间在 $x^{n+1}$ 下的像长 $\le2\varepsilon v(1+o(1))$，与它相交的目标窗 $[k+b-\varepsilon,k+b+\varepsilon]$ 至多 $2\varepsilon v+2\varepsilon+1+o(1)$ 个。用第 $n$ 层区间覆盖即得。∎

定理 1 仅当 $v>(1+2\varepsilon)/(1-2\varepsilon)$ 时非平凡（右端小于 1），只作参照。

**定理 2（本笔记的结果）**：设 $(b_n)$ 独立同分布、在 $[0,1)$ 上均匀。则几乎必然，对所有 $v>1$，
$$\lim_{\eta\to0}\dim_H\big(E(\varepsilon)\cap[v-\eta,v+\eta]\big)\le\max\Big(0,\frac{\log2\varepsilon v}{\log v}\Big),$$
从而对所有 $X>1$ 同时有 $\dim_H\big(E(\varepsilon)\cap[1,X]\big)\le\max\big(0,\log(2\varepsilon X)/\log X\big)$。结合 Kahane 的式 (3)：对几乎每个 $(b_n)$，当 $X$ 充分大时
$$\frac{\log2\varepsilon(X-2)}{\log X}\le\dim_H\big(E(\varepsilon)\cap[1,X]\big)\le\frac{\log2\varepsilon X}{\log X}.$$

*证明*：
- **记号**：固定紧区间 $I=[a,c]\subset(1,\infty)$ 与 $N\ge1$。对 $n\ge N$，令
  $$G_{N,n}=\{x\in I:\lVert x^j-b_j\rVert\le\varepsilon,\ N\le j\le n\},\qquad G_N=\bigcap_n G_{N,n},$$
  于是 $E(\varepsilon)\cap I\subset\bigcup_NG_N$。窗口 $W_{n,k}=\{x\in I:x^n\in[k+b_n-\varepsilon,k+b_n+\varepsilon]\}$ 是区间。设 $K_n$ 为与 $G_{N,n-1}$ 相交的窗口个数，则 $G_N$ 被 $K_n$ 个长度 $\le r_n:=2\varepsilon/(na^{n-1})$ 的区间覆盖。
- **局部松弛**：若 $x\in W_{n,k}\cap G_{N,n-1}$，$x'\in W_{n,k}$，则 $|x'-x|\le|W_{n,k}|\le2\varepsilon(1+o(1))/(nx^{n-1})$。对 $N\le j<n$，
  $$|x'^j-x^j|\le jx^{j-1}|x'-x|(1+o(1))\le2\varepsilon\,x^{j-n}(1+o(1))=:\varepsilon\eta_j .$$
  这里关键是在估计 $|x'-x|$ 时用 $x$ 处的**局部**尺度，而不是 $I$ 两端的 $a$、$c$；否则会出现 $(c/a)^n$ 的指数损失。上述 $o(1)$ 在 $I$ 上一致：$(\max(x,x')/x)^n\le\exp(nr_n/a)\to1$。由于 $x^{j-n}\le a^{j-n}$，可取与 $x$ 无关的确定阈值 $\eta_j:=3a^{j-n}$（$n\ge n_0(I)$）。这样 $G'_{n-1}:=\{x\in I:\lVert x^j-b_j\rVert\le\varepsilon(1+\eta_j),\ N\le j<n\}$ 在抽取 $b_n$ 之前就已确定，$W_{n,k}\subset G'_{n-1}$ 仍成立，且 $\sum_j\eta_j\le3/(a-1)$ 有界。
- **计数**：除去被 $I$ 端点截断的至多 2 个窗口，每个窗口长 $\ge\rho_n:=2\varepsilon/(nc^{n-1})$，所以
  $$K_n\le2+\rho_n^{-1}\int_I\mathbf 1_{G'_{n-1}}(x)\,\mathbf 1[\lVert x^n-b_n\rVert\le\varepsilon]\,dx .$$
- **取期望**：各 $b_j$ 独立且均匀，对每个固定的 $x$，$\mathbb P(\lVert x^j-b_j\rVert\le\varepsilon')=\min(1,2\varepsilon')$。于是
  $$\mathbb E K_n\le2+\frac{nc^{n-1}}{2\varepsilon}\,|I|\,2\varepsilon\prod_{j=N}^{n-1}2\varepsilon(1+\eta_j)\le2+C\,n\,c^{n}(2\varepsilon)^{n},$$
  其中常数 $C=C(N,I,\varepsilon)$（含因子 $(2\varepsilon)^{-N}$ 与 $e^{3/(a-1)}$）。不等式 $K_n\le2+\rho_n^{-1}\int\cdots$ 对每个实现都成立：所有窗口恰好划分 $\{x\in I:\lVert x^n-b_n\rVert\le\varepsilon\}$，因此窗口依赖于 $b_n$ 不影响论证；随后再用 Fubini 取期望。
- **Borel–Cantelli**：由 Markov 不等式，$\mathbb P(K_n>n^2\mathbb EK_n)\le n^{-2}$，故几乎必然对充分大的 $n$，$K_n\le C'n^3\max(1,2\varepsilon c)^n$。于是对 $s>\max\big(0,\log(2\varepsilon c)/\log a\big)$，有 $\mathcal H^s_{r_n}(G_N)\le K_nr_n^s\to0$。
- **收尾**：
  - 对 $N$ 与有理端点区间 $I$ 取可数交，得到一个几乎必然事件；在该事件上令 $I$ 缩向 $v$，即得对所有 $v$ 同时成立的局部陈述。
  - 写 $(1,X]=\bigcup_m[1+1/m,X]$。每一段是紧集，可用有限个有理区间覆盖，使每个区间上的界都小于 $d(v)+\eta$；再用可数稳定性。
  - $d(v)=\log(2\varepsilon v)/\log v$ 的导数为 $-\log(2\varepsilon)/(v\log^2v)>0$，所以 $d$ 递增，上确界为 $d(X)$。
  - 非严格不等式 $\le\varepsilon$ 给出 $E(\varepsilon)$ 的超集，方向正确。∎

**独立审阅记录（2026-11-25）**：另一子代理作对抗性审阅，结论为"正确，需小修，无实质缺口"。本节已按其意见修改：确定阈值 $\eta_j=3a^{j-n}$、注明常数依赖、写出紧集穷竭、改正定理 1 的说明。

Kahane 下界 (3) 的适用范围已从原文核对：P3 以 "Soit $(b_n)$ une suite arbitraire" 开头，(3) 出自 P3 的证明，所以对任意 $(b_n)$ 成立。

审阅者同时指出，这是标准的第一矩论证，"新结果"必须带"窄"的限定。

**说明**：
- 证明只用到"每个固定的 $x$ 在独立随机目标下的命中概率恰为 $2\varepsilon$"，属于第一矩方法，对确定的 $(b_n)$ 不适用。
- 本证明为本人推导，**尚未经他人审阅**；投稿前应由作者逐行复核。

---

## 3. 几乎处处的下界：证明路线（**未完成**）

目标：几乎必然地，局部维数 $\ge\log(2\varepsilon v)/\log v$。

- **思路**：取 $\nu_n=(2\varepsilon)^{-n}\mathbf 1_{G_{N,n}}dx$，计算期望能量 $\mathbb E I_s(\nu_n)=\iint|x-x'|^{-s}\prod_j\frac{g(x^j-x'^j)}{(2\varepsilon)^2}\,dx\,dx'$，其中 $g(t)=|A\cap(A+t)|$，$A=[-\varepsilon,\varepsilon]+\mathbb Z$。
- **尺度分解**：当 $|x-x'|\approx v^{-m}$ 时，
  - $j<m$ 的因子 $\approx1/(2\varepsilon)$，贡献 $(2\varepsilon)^{-m}\approx|x-x'|^{\log(2\varepsilon)/\log v}$；
  - $j>m$ 的因子在对 $x$ 平均后应约为 $1$。
- **结论**：若上述平均成立，则对 $s<\log(2\varepsilon v)/\log v$，能量一致有界。再配合二阶矩与鞅收敛，即得结论（与 fractal percolation 的标准论证同型）。
- **缺的关键引理（去相关引理）**：对 $|t|\approx v^{-m}$，在 $x$ 的小窗口上，$\phi_j(x)=x^j-(x+t)^j\bmod1$（$j>m$）的联合分布与独立均匀分布的偏差，按 $\prod_jg(\phi_j)/(2\varepsilon)^2$ 计算可以控制。
- **困难所在**：
  - 这是 Koksma 型的度量独立性问题；
  - $g$ 的 Fourier 系数非负、和为 $2\varepsilon$，每一层的绝对值和 $1/(2\varepsilon)>1$，不能逐项估计；
  - 需要利用 $\phi_j'$ 随 $j$ 几何增长，用 van der Corput 型估计并分块处理。

### 3a. 更具体的路线（2026-11-25 推导，**仍未证明**）

- **递推形式**：写 $g=(2\varepsilon)^2+\tilde g$，$\int\tilde g=0$。对 $b_{n+1}$ 取条件期望，
  $$\mathbb E[\mu_{n+1}^2\mid\mathcal F_n]=(2\varepsilon)^2\mu_n^2+R_n,\qquad R_n=\iint_{G_n^2}\tilde g(x^{n+1}-x'^{n+1})\,dx\,dx'.$$
  于是 $\sup_n\mathbb EW_n^2<\infty$ 等价于 $\sum_n\mathbb ER_n/(2\varepsilon)^{2n+2}<\infty$。
- **近对角项**：当 $|x-x'|\lesssim v^{-n}$ 时 $\tilde g\approx2\varepsilon(1-2\varepsilon)>0$。这部分贡献约为 $\mu_nv^{-n}$，规范化后是 $(2\varepsilon v)^{-n}$，**恰在 $2\varepsilon v>1$ 时可和**，与 Kahane 的临界值吻合。
- **离对角项**：
  - 设 $x$、$x'$ 在第 $n$ 层的窗口编号相差 $d$。由 $x^n\approx k+b_n$ 得 $\phi_{n+1}=x'^{n+1}-x^{n+1}\approx d\,x\,\frac{n+1}{n}\pmod 1$；一般地，$r$ 层之后相位约为 $d\,x^r\frac{n+r}{n}\pmod1$。
  - 在半径 $\eta$ 的窗口内，$x^r$ 的变化量约为 $r v^{r-1}\eta$。当 $r\gtrsim\log(1/\eta)/\log v$ 时，相位在窗口内等分布，相关性消失。
  - 所以每一对的"未去相关"层数有界，乘性相关因子 $\le(2\varepsilon)^{-O(\log(1/\eta))}$ 是常数。这与 §4b 数值中二阶矩有界一致。
- **需要严格化的地方**：
  - 把"相位等分布"写成对分形集 $G_n$ 上的平均，而不是对整个窗口的平均。困难在于 $G_n$ 本身由更早的相位决定。
  - 朴素的一次分部积分只能得到常数倍的增益 $1/v$，不足以求和；必须用上面的"$d$ 分组 + 有界持续层数"的结构。
  - 整数 $v$（如 $v=3$）时 $dv^r\bmod1=0$，相关性完全依赖 $x$ 在窗口内的变化来打破，需要单独处理（数值中 $v=3$ 同样有界）。

### 3b. 精确约化（已证）

$g=\mathbf 1_A*\mathbf 1_{-A}$，所以 $\hat g(h)=|\hat{\mathbf 1}_A(h)|^2=\sin^2(2\pi h\varepsilon)/(\pi h)^2\ge0$，Fourier 级数绝对收敛。对 $b_{n+1}$ 取条件期望得到**恒等式**
$$\mathbb E[\mu_{n+1}^2\mid\mathcal F_n]=(2\varepsilon)^2\mu_n^2+\sum_{h\ne0}\hat g(h)\,\big|\hat S_n(h)\big|^2,\qquad \hat S_n(h):=\int_{G_n}e(hx^{n+1})\,dx .$$
因此 §3 所需的二阶矩有界**等价于**：

> **引理 D（开放）**：当 $2\varepsilon v>1$ 时，$\displaystyle\sum_n(2\varepsilon)^{-2n}\sum_{h\ne0}\hat g(h)\,\mathbb E|\hat S_n(h)|^2<\infty$。

这是关于分形集 $G_n$ 上指数和的精确陈述。§4b 的数值（$\mathbb EW_n^2$ 稳定）就是这一级数收敛的数值证据。

### 3c. 为什么引理 D 不是"技术细节"：退火与淬火

- **新鲜性**：沿树中任何适应地选出的路径，节点的偏移 $U_{j+1}=(\text{像的起点}+\varepsilon)-b_{j+1}\bmod1$ 都是**新鲜的均匀变量**，因为 $b_{j+1}$ 与已选的一切独立。
- **相关性**：同层兄弟节点共用 $b_{j+1}$，彼此只差各自的相位。
- **两个极端**：
  - 若兄弟相位在 $\mathbb T$ 上等分布，维数应为**退火值**，即 Kahane 的候选 $\log(2\varepsilon v)/\log v$，由 $\log\mathbb E\sum_cr_c^s=0$ 决定。
  - 若兄弟相位全部相同，维数会降到**淬火值**，由 $\mathbb E\log\sum_cr_c^s=0$ 决定。
- **推论（只对非预见性构造成立）**：
  - 若每一层的质量分配只用到 $b_{\le j+1}$（不看更深层），每个子节点的偏移都是新鲜的，由 Jensen 不等式，这样的 Frostman 测度最多只能达到淬火值。
  - 这**不**适用于预见性的分配规则，例如按孙节点个数或子树极限 $W$ 加权。Galton–Watson 树就是例子：均匀"可见度"测度的维数是 $\mathbb E\log Z$，而分支测度可达到 $\log m$。
  - 所以引理 D 是"不能用非预见性的路径构造绕开"的障碍，而不是一般意义上没有捷径。数值（§4a、§4b）显示真实行为是退火的。

### 3c′. 引理 D 的进一步化简与数值（2026-11-25，**仍未证明**）

**化简（分析）**：
- **窗口对**：把 $\hat S_n(h)$ 拆到第 $n$ 层窗口上。窗口 $k$ 的相位为 $\Phi_k=(k+b_n)^{1+1/n}$；编号相差 $d$ 的一对窗口，相位差约为 $h\,d\,x(1+\tfrac1n)$，$x$ 是这对窗口的位置。
  - **近对**（$|d|\lesssim1/(h\eta)$）：属于对角型区域，额外相关只持续约 $\log(1/\eta)/\log v$ 层。
  - **远对**：只有当 $G_{n-1}$ 的质量在线性频率约 $hd$ 上分散时才会相消。所以引理 D 递归地化为随机分形测度自身的 Fourier 衰减。
- **障碍**：在 Koksma 型展开中，活跃频率向量的个数约为 $(1/2\varepsilon)^J$，一阶导数检验给出约 $v^{-J}$ 的增益，二者恰在 $2\varepsilon v>1$ 处平衡。困难集中在共振向量：低层频率与最高层频率相抵。
- **补充难点**：在固定窗口上，$x^{j}$ 的导数随 $j$ 呈指数变化，一阶导数检验需要分段处理。

**数值**：
- **脚本**：`verification/kahane_lemmaD_fourier_20261125.py`（输出 `.log`、`.json`）与 `verification/kahane_lemmaD_rate_fit_20261125.py`（输出 `.log`）。
- **方法**：对 400–600 个随机目标序列精确计算 $\hat S_n(h)$（每个区间用 24 点 Gauss–Legendre 求积），统计 $D_n(h)=\mathbb E|\hat S_n(h)|^2/(|I|^2(2\varepsilon)^{2(n-n_0+1)})$。
- **恒等式检验**：§3b 恒等式预言的 $\mathbb EW_n^2$ 增量与实测增量在 Monte Carlo 误差内一致。例如次临界情形，预言每层约 0.12–0.19，实测平均约 0.15。
- **衰减率**（后半段层数的对数线性拟合，$h=1,2,3$）：

| 情形 | $2\varepsilon v$ | 拟合的 $D_{n+1}/D_n$ | 对角率 $1/(2\varepsilon v)$ | 读法 |
| :--- | :--- | :--- | :--- | :--- |
| $v=3$，$\varepsilon=0.3$ | 1.8 | 0.48 / 0.62 / 0.53 | 0.556 | 几何衰减，级数收敛 |
| $v=3$，$\varepsilon=0.45$ | 2.7 | 0.29 / 0.32 / 0.28 | 0.370 | 几何衰减，级数收敛 |
| $v=3$，$\varepsilon=0.175$ | 1.05 | 0.90 / 0.90 / 0.86 | 0.952 | 缓慢衰减，级数收敛 |
| $v=3$，$\varepsilon=0.15$ | 0.9 | 1.06 / 1.03 / 1.08 | 1.111 | 不衰减，级数发散（灭绝） |

**由此提出的更尖锐的子猜想**：

> **猜想 D′（对角主导，按窗口左端点陈述）**：对窗口 $I=[a,c]$，$U_n(h)\le C_h\,n^{O(1)}(2\varepsilon a)^{-n}$（$U_n$ 见 §3c‴），即非对角部分的 Fourier 能量不超过对角部分（同一窗口内的配对）的量级。

**说明（2026-11-25 审阅后修正）**：
- 原稿用 $(2\varepsilon v)^{-n}$。但对固定半径 $\eta$ 的窗口，$a=v-\eta<v$，$(2\varepsilon a)^{-n}$ 与 $(2\varepsilon v)^{-n}$ 相差指数因子 $(v/a)^n$，所以必须按 $a$ 陈述。
- D′ 在 $2\varepsilon a>1$ 时推出引理 D。取 $\eta$ 足够小即可满足，这对 $v$ 处的局部维数已经足够。四种情形下拟合的比值都接近且多数略低于对角率，与 D′ 一致。这是有限计算，不是证明；拟合只用了 $n\le22$（$\varepsilon=0.45$ 一组只到 $n\le14$）。

### 3c″. 可用工具的文献检索（2026-11-25，子代理检索，负搜索）

| 来源 | 与引理 D 的关系 | 结论 |
| :--- | :--- | :--- |
| Shmerkin–Suomala，*Spatially independent martingales…*，arXiv:1409.6707v4（子代理读了 TeX 源；Mem. AMS 251 (2018) no. 1195 仅见于网页检索，**官方页面未核到**） | 定义中的 (SI4) 要求相隔足够远的二进方块上的限制在条件下独立。我们每层只有一个 $b_j$，各方块完全相关，(SI4) 不成立。文中提到更弱独立性的版本"在准备中"，相关预印本 arXiv:1703.09553 只处理分形渗流的乘积 | 不适用 |
| Aistleitner–Baker，*On the pair correlations of powers of real numbers*，arXiv:1910.01437（子代理读了 TeX 源；期刊卷页**未核到**） | 用与 $x^n$ 尺度相适应的二进 σ-代数和 van der Corput 估计证明几乎处处的 Poisson 对相关 | 方法上最接近 $\hat S_n(h)$ 的估计，**需修改**：它只处理成对的乘积，不处理多因子乘积；我们还要对约 $(2\varepsilon v)^n$ 个窗口求和 |
| Troscheit，arXiv:1511.03461（只看了摘要） | 单变量（1-variable）随机图有向自相似集：每层一个随机选择，几乎必然 Hausdorff 维数等于上盒维数 | 结构上类比我们"每层一个随机平移"的模型。这类模型的维数通常由**淬火**公式给出；而我们的数值显示**退火**行为，原因在于兄弟节点的相位差提供了伪独立性。这正是引理 D 的实质，也说明它不能从现成的单变量理论推出 |
| Bugeaud–Liao–Rams 的定理 7；Baker arXiv:1411.4817 | 已在前文讨论 | 不适用 |

**负搜索**：没有找到"i.i.d. 随机中心下 $x^n$ 的维数"，也没有找到"随机平移周期图案"的 Fourier 衰减或维数结果。覆盖范围是 arXiv 标题和摘要（约 16 个检索式）与网页检索，**未**查 MathSciNet、zbMATH。

**下一步的技术路线**（据此选定）：
- 以 Aistleitner–Baker 的"尺度适应 σ-代数 + van der Corput"为模板，证明 D′ 在单一频率 $h$ 下的形式；
- 关键是把"对 $(2\varepsilon v)^n$ 个窗口求和"化成对上一层结构的递归控制，即 §3c′ 中的近对与远对分解。

### 3c‴. 对 D′ 的部分证明（2026-11-25，本笔记推导；已经一次独立对抗审阅，结论为"正确，需小修"，修改见本节末）

**命题 P1（正表示，已证）**：把每个因子 $g$ 展开为 Fourier 级数，系数 $\hat g\ge0$。记 $w=\hat g/(2\varepsilon)^2$，则 $w\ge0$、$w(0)=1$、$\sum_kw(k)=g(0)/(2\varepsilon)^2=1/(2\varepsilon)$，并且
$$U_n(h):=\frac{\mathbb E|\hat S_n(h)|^2}{(2\varepsilon)^{2(n-N+1)}}=\sum_{k\in\mathbb Z^{n-N+1}}\prod_{j=N}^nw(k_j)\,\Big|\int_Ie\big(P_k(x)\big)dx\Big|^2,\qquad P_k(x)=hx^{n+1}+\sum_{j=N}^nk_jx^j .$$
推导：$\mathbb E\big[\prod_jg(x^j-y^j)\big]$ 展开后，$e\big(\sum_jk_j(x^j-y^j)\big)=e(P_k(x))\overline{e(P_k(y))}$，对 $x$、$y$ 积分即得平方模。各项非负，问题化为整系数多项式相位的加权计数。

**命题 P2（两种导数检验，已证）**：
- **局部化**：设 $I=[a,c]$，把它切成 $L=\lceil n^2|I|\rceil$ 段等长的 $I_\ell$。由 Cauchy–Schwarz，$|\int_I|^2\le L\sum_\ell|\int_{I_\ell}|^2$。在每段上，对 $j\le n+1$ 有 $x^j\in[x_\ell^j,2x_\ell^j]$（$n\ge n_0$）。
- **一阶导数检验**：若在 $I_\ell$ 上 $|P_k'|\ge\lambda_1:=|h|a^n/2$，则 $P_k'$ 不变号；$P_k''$ 至多 $n-1$ 个零点，所以 $P_k'$ 至多分 $n$ 段单调。由 Kusmin–Landau 型估计，$|\int_{I_\ell}e(P_k)|\le n/\lambda_1$。
- **二阶导数检验**：若在 $I_\ell$ 上 $|P_k''|\ge\lambda_2:=(n+1)|h|a^{n-1}/2$，由 van der Corput 二阶导数检验，$|\int_{I_\ell}e(P_k)|\le8\lambda_2^{-1/2}$。
- **求和**：对在某段上满足其一的 $(k,\ell)$ 求和，并用总权重 $\sum_k\prod w=(2\varepsilon)^{-(n-N+1)}$，这部分贡献至多
  $$L^2(2\varepsilon)^{-(n-N+1)}\Big(\frac{64}{\lambda_2}+\frac{n^2}{\lambda_1^2}\Big)\le C\,n^3(2\varepsilon a)^{-n}+C\,n^6(2\varepsilon a^2)^{-n},$$
  其中 $C=C(N,I,\varepsilon,h)$。这正是按 $a$ 陈述的 D′ 所要求的速率（见 §3c′ 的修正说明）；第二项衰减更快。

**机制说明（启发式，与数值一致）**：
- 主导共振是 $k_n\approx-(n+1)hx/n$：次高系数在 $P'$ 中抵消最高项。
- 只有 $k_n$ 时，代数上 $P''(x_0)=(n+1)hx_0^{n-1}$ 精确成立（审阅者对 $n=10,20,40$ 核算）。在长度 $\le1/n^2$ 的小段上 $P''$ 保持 $\ge\lambda_2$，所以这一类落在二阶导数检验之内。若还有 $k_{n-1}$ 等低层系数参与，就只在约化二次式的单根附近被覆盖，这正是引理 R 要处理的情形。
- 这一类给出的**上界**与对角率同阶，与 §3c′ 中实测衰减率约为 $1/(2\varepsilon v)$ 一致。这只是启发式的同阶对照，不等于证明它就是主项。

**剩余部分（引理 R，开放）**：
- **对象**：P2 的两种检验在 $I_\ell$ 上都不适用的 $(k,\ell)$，即
  $$\big(\exists x\in I_\ell:\ |P_k'(x)|<\lambda_1\big)\ \text{且}\ \big(\exists y\in I_\ell:\ |P_k''(y)|<\lambda_2\big),$$
  $x$ 与 $y$ 可以不同。
- **逻辑关系**：若这些 $(k,\ell)$ 的贡献 $\lesssim n^{O(1)}(2\varepsilon a)^{-n}$（**引理 R**），则 D′ 成立。这只是**充分条件**，不是等价：Cauchy–Schwarz 有损失，且小段随 $n$ 缩小，所以 D′ 推不出引理 R。
- **结构**：对两条共振条件作消元可知，双重共振至少需要两个较大的低层系数。在最小的双重共振中，$k_n\approx-2(n+1)hx_0/n$，$k_{n-1}\approx(n+1)hx_0^2/(n-1)$，即 $|k_{n-1}|\gtrsim|h|v^2$。由于 $w(k)\asymp k^{-2}$，这只带来常数倍的权重减小（约 $1/(h^2v^4)$），**没有指数增益**。
- **困难**：
  - 在最小双重共振处，$P'=x^{n-2}(n+1)h(x-x_0)^2$，所以 $|P'''(x_0)|=2(n+1)|h|x_0^{n-2}$，是 $n$ 的一次量级。三阶导数检验给出 $|\int|\lesssim\lambda_3^{-1/3}$，即 $|\int|^2\lesssim\lambda_3^{-2/3}$，按 $v^{-2n/3}$ 衰减。由此可和需要 $2\varepsilon v^{2/3}>1$，比所需的 $2\varepsilon v>1$ 弱。
  - 一旦 $k_{n-2}$ 也参与（三重共振），$P'''$ 就没有一致的下界，连这一估计也不可用。
  - 所以需要更精细的"共振级联"递归分析，不能逐层套用 van der Corput。
- **另一条可能的路线**：把积分换元到 $u=x^n$，用周期化与 Parseval 改写为整数滞后的自相关和。但低层系数可以近似抵消 $F''$，所以一致于低层系数的估计不成立，只能对权重取平均。

**结论**：引理 R 是 D′ 的充分条件。数值（§3c′）支持 D′，但引理 R 尚无证明。

**审阅记录（2026-11-25）**：独立对抗审阅的结论为"正确，需小修"。P1 与 P2 已覆盖的部分成立，审阅者用精确有理算术核对了常数。
- 审阅者对常数的说明：
  - Kusmin–Landau 每段 $\le1/(\pi\lambda_1)$（Titchmarsh 的形式为 $2/(\pi\lambda_1)$），所以 $n/\lambda_1$ 成立；
  - 二阶导数检验的精确常数约为 $4/\sqrt{\pi\lambda}$，所以 $8\lambda^{-1/2}$ 成立；
  - $(1+1/(n^2a))^{n+1}=1+O(1/n)$，局部化中的倍数 2 绰绰有余。
- 已作的修改：
  - "等价"改为"充分条件"；
  - 剩余集合写成 $\exists x$、$\exists y$ 的明确定义；
  - D′ 与速率改按窗口左端点 $a$ 陈述，并要求 $2\varepsilon a>1$；
  - "恰好重现对角率"降级为同阶的启发式对照；
  - "权重较小"注明只有常数倍；
  - 三阶导数检验的指数与量级已改正为 $\lambda_3\approx2(n+1)|h|v^{n-2}$、$|\int|^2\lesssim\lambda_3^{-2/3}$。

### 3d. 定理 3：几乎处处的淬火下界（本笔记推导；已经一次独立对抗审阅，结论为"正确，需小修"，修改见本节）

**定理 3**：设 $(b_n)$ 独立同分布、在 $[0,1)$ 上均匀，$v>1$，$L:=2\varepsilon(v-1)>1$。则几乎必然，$E(\varepsilon)$ 在 $v$ 处的局部维数满足
$$\ge\frac{(1-\{L\})\log\lfloor L\rfloor+\{L\}\log\lceil L\rceil}{\log v}=\frac{\mathbb E\log f_L(U)}{\log v},\qquad f_L(U):=\#\big(\mathbb Z\cap[U,U+L)\big).$$
由于 $L$ 关于 $v$ 连续，对所有 $v$ 同时成立（取可数个有理窗口）。

*证明梗概*：
- **构造**：取半径 $\eta$ 的窗口 $I\ni v$。$\eta$ 足够小，使 $L_\eta:=2\varepsilon(v-\eta-1)>1$（**严格**大于 1，保证 $\mathbb P(f\ge2)>0$，从而 $\nu$ 无原子）。取 $N$ 充分大，使 $I$ 内确定地含有一个完整的第 $N$ 层窗口。只保留**完整**的子窗口，并在它们之间均匀分配质量，得到测度 $\nu$。
- **子窗口个数**：
  - 完整窗口 $J=[(k+b_j-\varepsilon)^{1/j},(k+b_j+\varepsilon)^{1/j}]$ 在 $x^{j+1}$ 下的像长为 $2\varepsilon(1+1/j)\xi^{1/j}\ge2\varepsilon(v-\eta)$（中值定理）。
  - 完整子窗口要求 $k'+b_{j+1}\in[\alpha+\varepsilon,\beta-\varepsilon]$，其中 $[\alpha,\beta]$ 是像。这个区间长 $\ge L_\eta$，所以个数为 $\lceil U+L_\eta\rceil-1\ge f_{L_\eta}(U_{j+1})$，其中 $U_{j+1}=\{\alpha+\varepsilon-b_{j+1}\}$ 是新鲜的均匀变量，计数关于长度单调。
  - 子窗口是 $J$ 的像的子集在单射下的原像，所以落在 $J\subset I$ 内。
  - 由于 $L_\eta>1$，每个节点至少有一个子窗口，不会出现死路。
- **沿路径的大数定律**：$J_j$ 关于 $\sigma(b_{\le j},\xi_{\le j})$ 可测（$\xi$ 是路径选择的辅助随机性），所以 $U_{j+1}$ 与它独立且均匀，$U_j$ **恰好**独立同分布，用普通强大数定律即可。第 $j+1$ 层的选择用到 $b_{j+1}$，但从不用 $b_{j+2}$。给定 $b$，路径的条件分布就是 $\nu_b$。于是 $\nu$-几乎处处有 $\liminf\frac1n\sum\log N_j\ge\mathbb E\log f_{L_\eta}(U)$。再由 Fubini（联合概率为 1，故对 $\mathbb P$-几乎每个 $b$ 有 $\nu_b(A_b)=1$），对几乎每个 $b$，这对 $\nu_b$-几乎每条路径成立。
- **从柱集到球（按间隙尺度，已修正）**：
  - 第 $m$ 层不同窗口之间的间隙至少为 $\delta_m\approx(1-2\varepsilon)/(m(v+\eta)^{m-1})$。若 $r<\delta_m$，则 $B(x,r)\cap\operatorname{supp}\nu\subset J_m(x)$。
  - 取固定的 $K$，使 $v^{K-1}(1-2\varepsilon)>2\varepsilon$。当 $\rho_{n+1}\le r<\rho_n$（$\rho_n$ 为完整窗口长度）时有 $r<\delta_{n-K}$，从而 $\nu(B(x,r))\le\nu(J_{n-K}(x))=\prod_{j=N}^{n-K-1}N_j^{-1}$。
  - 原稿用 $J_{n-1}$，需要 $v(1-2\varepsilon)>2\varepsilon$。这一条件在表中 $v=3$、$\varepsilon=0.45$ 一行不成立，因此改为 $J_{n-K}$。$K$ 固定，极限比值不变。
- **结论**：$\log r\approx-n\log v$，由局部质量分布原理（Billingsley 形式，$x$ 取 $\nu$-典型点），下局部维数 $\ge\mathbb E\log f_{L_\eta}(U)/\log(v+\eta)$。
  - **边界点**：$\operatorname{supp}\nu$ 用的是闭约束 $\le\varepsilon$，而 $E(\varepsilon)$ 用严格的 $<\varepsilon$。两者只差可数个边界点；$\nu$ 无原子，所以这些点是 $\nu$-零集。
  - **收尾**：令 $\eta\to0$。界 $(1-\theta)\log m+\theta\log(m+1)$ 是 $\log$ 的分段线性插值，在整数处连续，所以取可数个有理窗口即对所有 $v$ 同时成立。∎
- **与定理 2 一致**：$\mathbb Ef_L(U)=L$，由 Jensen 不等式，$\mathbb E\log f_L\le\log L=\log2\varepsilon(v-1)<\log2\varepsilon v$。

**与已知界的比较**：脚本 `verification/kahane_quenched_bound_table_20261125.py`，输出在同名 `.log`。

| $v$ | $\varepsilon$ | Kahane (3)：对每个 $(b_n)$ | 定理 3：几乎每个 $(b_n)$ | 候选值（定理 2 的上界） |
| :--- | :--- | :--- | :--- | :--- |
| 3 | 0.3 | 0（平凡） | 0.1262 | 0.5350 |
| 3 | 0.45 | 0（平凡） | 0.5047 | 0.9041 |
| 5 | 0.3 | 0.3652 | 0.5314 | 0.6826 |
| 10 | 0.3 | 0.6812 | 0.7306 | 0.7782 |
| 10 | 0.1 | 0.2041 | 0.2408 | 0.3010 |
| 100 | 0.1 | 0.6461 | 0.6483 | 0.6505 |
| 1000 | 0.1 | 0.7667 | 0.7669 | 0.7670 |

**注意**：
- 定理 3 只对几乎每个 $(b_n)$ 成立，Kahane 的界对每个 $(b_n)$ 成立。
- 定理 3 并非处处更好：当 $\lfloor L\rfloor=1$ 且 $\varepsilon$ 很小时可能更差（例：$\varepsilon=0.03$、$v=26$ 时，定理 3 约 0.106，Kahane 约 0.112）。正确的陈述是"两者取大"。
- 所以，对几乎每个 $(b_n)$，局部维数被夹在 $\max(\text{Kahane},\text{定理 3})$ 与候选值之间。
- 要闭合，单是引理 D（总质量的二阶矩有界）还**不够**：
  - 它只给出 $\mathbb P(W_\infty>0)>0$（数值中 $\mathbb P(W=0)\approx0.04$）。升级为"几乎必然"还需要 Kolmogorov 0-1 律：$\dim(E\cap I)$ 是尾可测的，因为 $E(\varepsilon)$ 不依赖于有限多个 $b_n$。
  - 维数下界需要引理 D 的能量形式，或者对所有子窗口、所有起始层一致成立的版本。

**审阅记录（2026-11-25）**：独立对抗审阅的结论为"定理 3 正确，需小修，无实质缺口"。已修改：
- 从柱集到球的论证，原稿在 $v(1-2\varepsilon)\le2\varepsilon$ 时不成立，已改为按间隙尺度；
- 条件 $L_\eta\ge1$ 改为 $>1$，并补上边界点可数的说明；
- §3c 的推论限于非预见性构造；
- 闭合条件改为"引理 D 的一致或能量形式加上 0-1 律"；
- 偏移的定义补上 $+\varepsilon$。

审阅者独立复算了表中 7 行和反例（$\varepsilon=0.03$、$v=26$），全部一致；本表数值由上述脚本生成。

---

## 4. 数值证据（有限计算，非证明）

- **脚本**：`verification/powers_mod1_dimension_numerics_20261125.py`，输出在同名 `.log` 与 `.json`。
- **方法**：在 $[v-\eta,v+\eta]$ 内精确枚举所有第 $n$ 层区间（mpmath，精度随 $n$ 增长）。
- **统计量**：无偏的 $g_n=(N_{n+1}/N_n)\cdot\frac{n}{n+1}$，猜想预言 $g_n\to2\varepsilon v$。
- **结果**：见 §4a。

### 4a. 结果（2026-11-24 运行，窗口半径 0.002；$v=5$ 的随机目标一组为 0.02）

| $v$ | $\varepsilon$ | 目标 $b_n$ | 层数 | 末层区间数 | $g_n$ 后半几何平均 | $2\varepsilon v$ | 猜想维数 $\log2\varepsilon v/\log v$ |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 3 | 0.30 | $\equiv0$ | 4–24 | 673824 | 1.8094 | 1.8 | 0.5350 |
| 3 | 0.30 | 伪随机 | 4–25 | 427232 | 1.8010 | 1.8 | 0.5350 |
| 3 | 0.30 | $\equiv\frac12$ | 4–26 | 532516 | 1.7997 | 1.8 | 0.5350 |
| 5 | 0.15 | $\equiv0$ | 3–30 | 517128 | 1.5005 | 1.5 | 0.2519 |
| 5 | 0.15 | 伪随机 | 3–26 | 400045 | 1.5021 | 1.5 | 0.2519 |
| 2.5 | 0.40 | 伪随机 | 5–22 | 806223 | 2.0057 | 2.0 | 0.7565 |
| 4 | 0.20 | 伪随机 | 4–27 | 530450 | 1.5990 | 1.6 | 0.3390 |
| 3 | 0.45 | 伪随机 | 4–17 | 965523 | 2.7212 | 2.7 | 0.9041 |

**读法**：
- 8 组的 $g_n$ 都在 $2\varepsilon v$ 的 0.8% 以内；最后 4 层的单层值都在 0.5% 以内。
- **确定的目标**（$b_n\equiv0$、$b_n\equiv\frac12$）与伪随机目标同样吻合。这支持猜想对确定的 $(b_n)$ 也成立，也就是 Kahane 的原问题，而不仅是几乎处处的版本。
- 未修正的 $s_n$ 估计（日志中另列）收敛较慢，例如 $v=3$、$n=24$ 时为 $0.559$，偏差来自 $(n+1)/n$ 修正，与启发式算出的有限 $n$ 预言 $\approx0.558$ 一致。
- 局限：
  - 这些都是有限 $n$、有限窗口的计数，不是证明；
  - 也不能区分 Hausdorff 维数与盒维数。

### 4b. 鞅的二阶矩（检验 §3 的证明路线；有限计算，非证明）

- **脚本**：`verification/kahane_martingale_sim_20261125.py`，输出在同名 `.log` 与 `.json`。
- **方法**：每种参数抽 2000 个独立均匀目标序列，精确计算 $\mu_n$，统计 $W_n=\mu_n/(|I|(2\varepsilon)^{n-n_0+1})$。由于对每个固定的 $x$ 各约束独立，$\mathbb EW_n=1$ 精确成立，$(W_n)$ 是非负鞅。

| 情形 | $2\varepsilon v$ | $\mathbb E W_n$ | $\mathbb E W_n^2$ | $\mathbb P(W_n=0)$ | 读法 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| $v=3$，$\varepsilon=0.3$ | 1.8 | $0.996\pm0.013$ | $n=8$：1.306；$n=12$–$22$：1.311 | 0.043（自 $n\approx8$ 起不变） | 二阶矩有界，$W>0$ 的概率约 0.96 |
| $v=5$，$\varepsilon=0.15$ | 1.5 | $0.999\pm0.002$ | 1.0058 → 1.0074（$n=8$–$17$） | 0 | 二阶矩有界 |
| $v=3$，$\varepsilon=0.175$ | 1.05 | $0.99\pm0.03$ | 2.05 → 2.49（$n=8$–$25$），缓增 | 0.43 → 0.446 | 近临界，收敛慢 |
| $v=3$，$\varepsilon=0.15$ | 0.9 | $0.99\pm0.05$ | 2.32 → 5.18，持续增长 | 0.52 → 0.75，持续增长 | 次临界：趋于灭绝，与 Kahane P6 一致 |

**读法与局限**：
- 超临界两组的二阶矩在可测深度内已稳定。这正是 §3 路线所需的 $L^2$ 有界性，属于有力的数值支持，但**不是证明**。
- 第一组 $n\ge23$ 的样本被计算量保护截断（只保留区间数较少的路径），统计有偏，已从表中排除；$n\le22$ 时全部 2000 个样本完整。
- 去相关引理仍需严格证明。

---

## 5. 它没做到什么

- **原问题未解决**：对**确定的** $(b_n)$（Kahane 原问题），上界与精确值都没有证明；数值只是佐证。
- **精确下界缺一环**：几乎处处的精确下界缺引理 R（双重共振项）。即使引理 R 成立，还需要引理 D 的能量形式，或对所有子窗口一致的版本，加上 0-1 律。
- **审阅范围**：定理 2、定理 3 与命题 P1、P2 各只经过一次子代理的独立对抗审阅，**未经同行审阅**。
- **检索范围**：先例检索未覆盖 MathSciNet、zbMATH 的引用链。Pollington 1980 与 Bugeaud 2012 的专著未核到。
- **与论文二的关系**：这是独立的新课题，不是论文二的内容。
- **档次判断**：定理 2 加定理 3 单独成文，大约是 C. R. Math. 短文的分量。补上引理 R，可得到几乎处处的完整答案，成为一篇扎实的期刊论文。只有对每一个 $(b_n)$ 解决 Q6，才可能有更高的显示度。
