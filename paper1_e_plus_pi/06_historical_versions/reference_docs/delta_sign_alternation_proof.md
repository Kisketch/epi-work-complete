# δ 符号交替定理的严格数学分析证明

**定理（主结果）** 设 $P_j/Q_j$ 为 $e$ 的正则连分数 $[2;1,2,1,1,4,1,1,6,\dots]$ 中位于部分商 $2j$ 之前的收敛子（$j\ge1$，前三项 $3/1,\,19/7,\,193/71$），置
$$\delta_j := Q_j e - P_j .$$
则对一切 $j\ge1$，
$$(-1)^j\,\delta_j>0 .$$
即误差严格交错，收敛子从两侧交替夹逼 $e$。由此可推出两条原先被公理化的估计：
$$\delta_j\to0,\qquad |\delta_j|<\frac{1}{2jQ_j}\quad(j\ge1).$$

**方法说明** 这是 Hermite 型积分表示方法。核心不是计算，而是一个结构性观察：
把代数量 $E_n:=(-1)^n n!\,\delta_n$ 与解析量 $I_n:=\int_0^1 e^t t^n(1-t)^n\,dt$ 放在同一递推下比较。
二者满足**同一个二阶线性递推**且有**同一组初值**，故由归纳法恒等；而 $I_n$ 的正性由被积函数的
逐点正性直接给出。这就把"符号"这一离散信息转化为"正被积函数的积分"这一解析事实。

> 本文所有结论均已在 Lean 4.35 + mathlib v4.35 中内核验证，公理依赖仅
> `propext, Classical.choice, Quot.sound`（Lean 基础公理），零 `sorryAx`。
> 下文给出的是人类可读的数学论证，与形式化证明一一对应；数值计算仅作独立佐证，不参与证明。

---

## 0. 记号与已知代数事实

对 $n\ge0$ 置
$$p_n(t):=t^n(1-t)^n,\qquad t\in[0,1].$$
$p_n$ 是次数 $2n$ 的实系数多项式，在 $[0,1]$ 上非负，在 $(0,1)$ 内严格正。

选定收敛子的分子分母满足三项递推（$j\ge1$，约定 $Q_0=P_0=1$ 使 $j=1$ 处闭合）：
$$Q_{j+1}=(4j+2)Q_j+Q_{j-1},\qquad P_{j+1}=(4j+2)P_j+P_{j-1}. \tag{0.1}$$
初值 $Q_1=1,\ Q_2=7,\ P_1=3,\ P_2=19$。行列式恒等式
$$P_jQ_{j+1}-P_{j+1}Q_j=2(-1)^{j+1}\qquad(j\ge1). \tag{0.2}$$
以及 $Q_j>0$、$Q_j\ge j!$、$Q_j\to\infty$。这些都是纯整数代数，已独立验证。

由 $(0.1)$ 两式立即得 $\delta$ 的递推：把 $Q_{j+1}e-P_{j+1}=(4j+2)(Q_je-P_j)+(Q_{j-1}e-P_{j-1})$ 展开即
$$\delta_{j+1}=(4j+2)\delta_j+\delta_{j-1}\qquad(j\ge1). \tag{0.3}$$

**注** $(0.3)$ 中 $e$ 的一次项系数恰好相消，这是"同一递推"现象的代数根源：$P,Q$ 满足同一线性递推，
故其任意线性组合（特别是 $Q_je-P_j$）也满足它。

---

## 1. 解析部分：$I_n$ 的正性、微分恒等式与递推

定义
$$I_n:=\int_0^1 e^t\,p_n(t)\,dt=\int_0^1 e^t\,t^n(1-t)^n\,dt .$$
被积函数 $f_n(t):=e^tp_n(t)$ 在 $[0,1]$ 上连续（初等函数之积），故 Riemann 可积，$I_n$ 有定义。

### 命题 1.1（严格正性） 对一切 $n\ge0$，$I_n>0$。

**证明** 在开区间 $(0,1)$ 内，$e^t>0$、$t^n>0$、$(1-t)^n>0$，故 $f_n(t)>0$。
$f_n$ 在 $[0,1]$ 连续且非负。取内点 $t_0=\tfrac12$，则 $c:=f_n(t_0)>0$。
由连续性，存在 $\eta>0$ 使 $[t_0-\eta,t_0+\eta]\subset(0,1)$ 且在其上 $f_n\ge c/2$。于是
$$I_n\ \ge\ \int_{t_0-\eta}^{t_0+\eta}f_n(t)\,dt\ \ge\ \frac{c}{2}\cdot2\eta\ =\ c\eta\ >\ 0,$$
其中第一个不等号用到 $f_n\ge0$ 于整个 $[0,1]$（区间外部分贡献非负）。$\blacksquare$

> **形式化对应**：`DeltaSign.I_pos`。Lean 中用
> `integral_pos_iff_support_of_nonneg_ae'`，把"连续 + 内点正"转成
> "$\operatorname{supp}f_n\cap(0,1]$ 的 Lebesgue 测度为正"，
> 并以 $(0,1)\subseteq\operatorname{supp}f_n$、$\operatorname{vol}(0,1)=1$ 完成。
> 这与上面的 $\eta$-邻域论证等价，只是用测度语言表述。

### 命题 1.2（一阶导数） 对 $n\ge1$，
$$p_n'(t)=n\,t^{n-1}(1-t)^{n-1}(1-2t).$$

**证明** 乘积法则与链式法则：
$$p_n'=n t^{n-1}(1-t)^n+t^n\cdot n(1-t)^{n-1}(-1)
=n t^{n-1}(1-t)^{n-1}\big[(1-t)-t\big],$$
方括号即 $1-2t$。$\blacksquare$

### 命题 1.3（二阶微分恒等式） 对 $n\ge2$，
$$\boxed{\,p_n''=n(n-1)\,p_{n-2}-2n(2n-1)\,p_{n-1}\,}\tag{1.1}$$
作为多项式恒等式成立。

**证明** 对命题 1.2 的表达式再求导。记 $u=t^{n-1}(1-t)^{n-1}$，则由同一计算（把 $n$ 换成 $n-1$）
$$u'=(n-1)t^{n-2}(1-t)^{n-2}(1-2t).$$
于是
$$p_n''=n\big[u'(1-2t)+u\cdot(-2)\big]
=n(n-1)t^{n-2}(1-t)^{n-2}(1-2t)^2-2n\,t^{n-1}(1-t)^{n-1}.$$
关键代数步骤：
$$(1-2t)^2=1-4t+4t^2=1-4t(1-t).$$
代入第一项：
$$n(n-1)t^{n-2}(1-t)^{n-2}\big[1-4t(1-t)\big]
=n(n-1)p_{n-2}-4n(n-1)\,t^{n-1}(1-t)^{n-1}
=n(n-1)p_{n-2}-4n(n-1)p_{n-1}.$$
故
$$p_n''=n(n-1)p_{n-2}-\big[4n(n-1)+2n\big]p_{n-1}
=n(n-1)p_{n-2}-2n(2n-1)p_{n-1},$$
因 $4n(n-1)+2n=4n^2-4n+2n=4n^2-2n=2n(2n-1)$。$\blacksquare$

> **这是整个证明的解析心脏**：$(1-2t)^2=1-4t(1-t)$ 这一步把二阶导数重新表达为
> *同族*多项式 $p_{n-2},p_{n-1}$ 的线性组合，从而使积分族 $\{I_n\}$ 封闭于一个二阶递推。
> 若无此恒等式，$\{I_n\}$ 不满足有限阶递推，方法失效。

### 命题 1.4（边界消失） 对 $n\ge1$：$p_n(0)=p_n(1)=0$；对 $n\ge2$：$p_n'(0)=p_n'(1)=0$。

**证明** $p_n(t)=t^n(1-t)^n$ 含因子 $t^n$ 与 $(1-t)^n$，$n\ge1$ 时分别在 $t=0$、$t=1$ 处为零。
由命题 1.2，$p_n'$ 含因子 $t^{n-1}(1-t)^{n-1}$，$n\ge2$ 时指数 $\ge1$，故同样在两端点为零。$\blacksquare$

### 命题 1.5（积分递推） 对 $n\ge2$，
$$\boxed{\,I_n=n(n-1)I_{n-2}-2n(2n-1)I_{n-1}\,}\tag{1.2}$$

**证明** 两次分部积分。分部积分公式
$$\int_a^b u v'=\big[uv\big]_a^b-\int_a^b u'v$$
在此合法：取 $u(t)=e^t$、$v(t)=p_n(t)$，二者在 $[0,1]$ 上连续可微（$C^1$），
导数连续故可积，满足公式的全部假设。

第一次，取 $u=e^t,\ v=p_n$（注意 $(e^t)'=e^t$）：
$$I_n=\int_0^1 e^t p_n=\big[e^tp_n\big]_0^1-\int_0^1 e^tp_n'
=-\int_0^1 e^tp_n',$$
边界项由命题 1.4（$n\ge1$）为零。

第二次，取 $u=e^t,\ v=p_n'$（$p_n'$ 也是多项式，$C^1$）：
$$\int_0^1 e^tp_n'=\big[e^tp_n'\big]_0^1-\int_0^1 e^tp_n''=-\int_0^1 e^tp_n'',$$
边界项由命题 1.4（$n\ge2$）为零。合并得
$$I_n=\int_0^1 e^t\,p_n''(t)\,dt .$$
最后代入 $\S$命题 1.3 的恒等式 $(1.1)$，并用积分的线性性（三项皆连续故可积）：
$$I_n=n(n-1)\int_0^1e^tp_{n-2}-2n(2n-1)\int_0^1e^tp_{n-1}
=n(n-1)I_{n-2}-2n(2n-1)I_{n-1}. \qquad\blacksquare$$

### 命题 1.6（初值） $I_0=e-1$，$I_1=3-e$。

**证明** $p_0\equiv1$，故 $I_0=\int_0^1e^t\,dt=e-1$。

$p_1(t)=t-t^2$。用两个标准原函数（可直接微分验证）
$$\int e^t t\,dt=e^t(t-1),\qquad \int e^t t^2\,dt=e^t(t^2-2t+2),$$
得
$$\int_0^1 e^tt\,dt=\big[e^t(t-1)\big]_0^1=0-(-1)=1,$$
$$\int_0^1 e^tt^2\,dt=\big[e^t(t^2-2t+2)\big]_0^1=e\cdot1-1\cdot2=e-2 .$$
故 $I_1=1-(e-2)=3-e$。$\blacksquare$

（注意 $I_1=3-e>0$ 与 $2<e<3$ 一致，与命题 1.1 相符。）

---

## 2. 代数部分：$E_n$ 满足同一递推与同一初值

定义
$$E_n:=(-1)^n\,n!\,\delta_n\qquad(n\ge0).$$

### 命题 2.1（$E$ 的递推） 对 $n\ge2$，
$$E_n=n(n-1)E_{n-2}-2n(2n-1)E_{n-1}.$$
即与 $(1.2)$ **逐字相同**。

**证明** 在 $(0.3)$ 中把 $j$ 换成 $n-1$（$n\ge2$ 保证 $n-1\ge1$）：
$$\delta_n=(4n-2)\delta_{n-1}+\delta_{n-2}.$$
两边乘 $(-1)^nn!$：
$$E_n=(-1)^nn!(4n-2)\delta_{n-1}+(-1)^nn!\,\delta_{n-2}.$$
分别处理两项，用 $n!=n\,(n-1)!$ 与 $n!=n(n-1)(n-2)!$，以及符号关系
$(-1)^n=-(-1)^{n-1}$、$(-1)^n=(-1)^{n-2}$：

第一项
$$(-1)^nn!\,\delta_{n-1}=n\cdot(-1)^n(n-1)!\,\delta_{n-1}
=-n\cdot\underbrace{(-1)^{n-1}(n-1)!\,\delta_{n-1}}_{=E_{n-1}}=-n\,E_{n-1}.$$
第二项
$$(-1)^nn!\,\delta_{n-2}=n(n-1)\cdot(-1)^n(n-2)!\,\delta_{n-2}
=n(n-1)\underbrace{(-1)^{n-2}(n-2)!\,\delta_{n-2}}_{=E_{n-2}}=n(n-1)E_{n-2}.$$
故
$$E_n=-(4n-2)\,n\,E_{n-1}+n(n-1)E_{n-2}
=n(n-1)E_{n-2}-2n(2n-1)E_{n-1},$$
其中 $(4n-2)n=2n(2n-1)$。$\blacksquare$

### 命题 2.2（初值） $E_0=e-1$，$E_1=3-e$。即与命题 1.6 **相同**。

**证明** $n=0$：$E_0=(-1)^0\,0!\,\delta_0=\delta_0=Q_0e-P_0=1\cdot e-1=e-1$。

$n=1$：$E_1=(-1)^1\,1!\,\delta_1=-(Q_1e-P_1)=-(1\cdot e-3)=3-e$。$\blacksquare$

---

## 3. 归纳：$E_n=I_n$，及主定理

### 定理 3.1（Hermite 积分表示） 对一切 $n\ge0$，
$$\boxed{\,(-1)^n\,n!\,\delta_n=\int_0^1 e^t\,t^n(1-t)^n\,dt\,}$$

**证明** 对 $n$ 作强归纳。

*基础* $n=0$：由命题 2.2 与 1.6，$E_0=e-1=I_0$。
$n=1$：$E_1=3-e=I_1$。

*归纳步* 设 $n\ge2$ 且对一切 $k<n$ 有 $E_k=I_k$。特别地 $E_{n-1}=I_{n-1}$、$E_{n-2}=I_{n-2}$
（$n-1<n$、$n-2<n$）。由命题 2.1 与 1.5，两序列满足同一递推，故
$$E_n=n(n-1)E_{n-2}-2n(2n-1)E_{n-1}
=n(n-1)I_{n-2}-2n(2n-1)I_{n-1}=I_n .$$
$\blacksquare$

> **逻辑要点**：这里用的是"二阶线性递推 + 两个初值唯一确定序列"这一原理，
> 以强归纳形式实现。不需要求出递推的闭式解，也不需要计算 $R_n(0),R_n(1)$ 之类的端点组合和。
> 这正是本证明相对于"直接算 Hermite 原函数端点值"路线的结构性优势：
> 后者需要恒等式 $\sum_{j=0}^n\binom nj(n+j)!=n!\,P_n$（研究级组合难题），前者完全绕开它。

### 定理 3.2（主定理：$\delta$ 符号严格交错） 对一切 $n\ge1$，$(-1)^n\delta_n>0$。

**证明** 由定理 3.1，$(-1)^nn!\,\delta_n=I_n$。由命题 1.1，$I_n>0$。
因 $n!>0$，两边除以 $n!$ 得 $(-1)^n\delta_n=I_n/n!>0$。$\blacksquare$

**几何含义** $\delta_n=Q_ne-P_n$ 的符号即 $e-P_n/Q_n$ 的符号。定理说
$$n\ \text{偶}\Rightarrow P_n/Q_n<e,\qquad n\ \text{奇}\Rightarrow P_n/Q_n>e,$$
即选定收敛子严格交替地从下方与上方逼近 $e$——这正是连分数收敛子的经典交错性质，
此处对**选定子列**给出了独立的解析证明（不依赖连分数一般理论）。

---

## 4. 由主定理推出两条原公理

### 引理 4.1（组合恒等式） 对 $j\ge1$，
$$Q_j\delta_{j+1}-Q_{j+1}\delta_j=2(-1)^{j+1}.$$

**证明** 直接展开 $\delta$ 的定义，$e$ 的一次项相消：
$$Q_j(Q_{j+1}e-P_{j+1})-Q_{j+1}(Q_je-P_j)
=-Q_jP_{j+1}+Q_{j+1}P_j=P_jQ_{j+1}-P_{j+1}Q_j,$$
由行列式恒等式 $(0.2)$ 等于 $2(-1)^{j+1}$。$\blacksquare$

### 引理 4.2（关键正项恒等式） 对 $j\ge1$，
$$\boxed{\,Q_j\,|\delta_{j+1}|+Q_{j+1}\,|\delta_j|=2\,}\tag{4.1}$$

**证明** 把引理 4.1 两边乘 $(-1)^{j+1}$。由定理 3.2，
$$(-1)^{j+1}\delta_{j+1}=|\delta_{j+1}|,\qquad
(-1)^{j+1}\delta_j=-(-1)^j\delta_j=-|\delta_j| .$$
左边变为
$$Q_j|\delta_{j+1}|-Q_{j+1}\big(-|\delta_j|\big)=Q_j|\delta_{j+1}|+Q_{j+1}|\delta_j| ;$$
右边变为 $2(-1)^{j+1}(-1)^{j+1}=2$。$\blacksquare$

> **这是符号信息的兑现之处**：交错符号把原本"两项相减"的行列式恒等式
> 变成"两项相加且皆为正"的恒等式，从而立即给出**上界**。
> 若无符号信息，$(0.2)$ 只给出差的信息，无法控制单项大小。

### 定理 4.3（原公理 2） 对 $j\ge1$，$\displaystyle|\delta_j|<\frac1{2jQ_j}$。

**证明** 由 $(4.1)$ 与 $Q_j|\delta_{j+1}|\ge0$（$Q_j>0$）得
$$Q_{j+1}|\delta_j|\le2,\qquad\text{即}\qquad|\delta_j|\le\frac2{Q_{j+1}} .$$
另一方面由递推 $(0.1)$ 与 $Q_{j-1}\ge0$、$Q_j>0$：
$$Q_{j+1}=(4j+2)Q_j+Q_{j-1}\ \ge\ (4j+2)Q_j\ >\ 4j\,Q_j .$$
（$j\ge1$ 时 $4j+2>4j$。）故
$$|\delta_j|\le\frac2{Q_{j+1}}<\frac2{4jQ_j}=\frac1{2jQ_j}. \qquad\blacksquare$$

### 定理 4.4（原公理 1） $\delta_j\to0$。

**证明** 由定理 4.3 的证明中间步骤，$|\delta_j|\le2/Q_{j+1}$ 对 $j\ge1$ 成立。
因 $Q_{j+1}\ge(j+1)!\to\infty$，有 $2/Q_{j+1}\to0$。由双侧夹逼
$$-\frac2{Q_{j+1}}\ \le\ \delta_j\ \le\ \frac2{Q_{j+1}}$$
（对充分大的 $j$）得 $\delta_j\to0$。$\blacksquare$

---

## 5. 方法论评注：哪些是数学，哪些是机械

| 步骤 | 性质 | 说明 |
|---|---|---|
| 选择 $E_n=(-1)^nn!\delta_n$ 与 $I_n$ 比较 | **数学洞察** | 认识到"符号 × 阶乘"能把代数递推与解析递推对齐；这是 Hermite 方法的核心思想 |
| 放弃直接算端点组合和 | **数学判断** | 识别出 $\sum\binom nj(n+j)!=n!P_n$ 是研究级难题，改走递推匹配路线绕开 |
| $(1-2t)^2=1-4t(1-t)$ | **关键代数洞察** | 使 $\{p_n\}$ 的二阶导数封闭于同族，是递推存在的根本原因 |
| 分部积分边界项消失 | **解析论证** | 需核验 $p_n,p_n'$ 在端点的零点重数，及 $C^1$ 可积性 |
| $I_n>0$ | **解析论证** | 连续 + 内点正 $\Rightarrow$ 积分正（$\eta$-邻域或测度语言） |
| 递推 + 初值 $\Rightarrow$ 恒等 | **逻辑原理** | 二阶线性递推的解由两初值唯一确定 |
| 符号 $\Rightarrow$ 正项和 $\Rightarrow$ 上界 | **数学兑现** | 引理 4.2 把符号信息转化为定量控制 |
| `ring` / `push_cast` / `simp` 展开 | 机械核验 | 仅验证已写出的代数等式，不产生数学内容 |
| mpmath 50 位数值核对 | **仅佐证** | 用于在形式化前发现公式错误；**不构成证明**，不参与任何结论 |

**诚实定位** 本定理是经典 Hermite 方法在 $e$ 的**选定收敛子子列**上的实例化。
方法本身经典（Hermite 1873 证 $e$ 超越即用此类积分），新颖性在于：
(i) 对选定子列（每三个收敛子取一）给出符号交错的独立解析证明；
(ii) 由此把原先公理化的两条误差估计降为定理，使下游分类/谱隙链的数学内容不再依赖未验证假设。
**这不是 $e+\pi$ 无理性问题的进展**——该问题仍开放，本证明不涉及 $\pi$。

---

## 6. 与形式化的对应表

| 本文 | Lean 声明 | 文件 |
|---|---|---|
| $(0.3)$ $\delta$ 递推 | `DeltaReduction.deltaSel_rec` | `DeltaReduction.lean` |
| 引理 4.1 | `DeltaReduction.cross_identity` | 同上 |
| 命题 1.2 | `padéP_first_deriv` | `PadeDeriv.lean` |
| 命题 1.3 | `padéP_second_deriv` | 同上 |
| 命题 1.4 | `padéP_eval_zero/one`, `padéP_deriv_eval_zero/one` | `PadeBoundary.lean` |
| 命题 1.5 | `ibp_zero`, `padeI_eq_second`, `padeI_recurrence` | `PadeRecurrence.lean` |
| 命题 1.1 | `DeltaSign.I_pos` | `DeltaSign.lean` |
| 命题 1.6 / 2.2 | `I_zero/I_one`, `E_zero/E_one` | 同上 |
| 命题 2.1 | `DeltaSign.E_recurrence` | 同上 |
| 定理 3.1 | `DeltaSign.E_eq_I` | 同上 |
| 定理 3.2 | `DeltaSign.deltaSignAlternation_proved` | 同上 |
| 引理 4.2 | `DeltaReduction.abs_sum_eq_two` | `DeltaReduction.lean` |
| 定理 4.3 | `DeltaSign.abs_deltaSel_lt_proved` | `DeltaSign.lean` |
| 定理 4.4 | `DeltaSign.deltaSel_tendsto_zero_proved` | 同上 |

另有一条独立路线（Hermite 原函数 $R_n=\sum_{k\le2n}(-1)^kp_n^{(k)}$ 满足 $R_n+R_n'=p_n$，
经 FTC 得 $\int_0^1e^tp_n=eR_n(1)-R_n(0)$）也已内核验证
（`padéR_ode`、`PadeIntegral.pade_integral_repr`），但因端点值需研究级组合恒等式而未采用；
本文的递推匹配路线是实际完成的证明。

**公理审计（逐字）**
```
'DeltaSign.E_eq_I'                        [propext, Classical.choice, Quot.sound]
'DeltaSign.I_pos'                         [propext, Classical.choice, Quot.sound]
'DeltaSign.deltaSignAlternation_proved'   [propext, Classical.choice, Quot.sound]
'DeltaSign.deltaSel_tendsto_zero_proved'  [propext, Classical.choice, Quot.sound]
'DeltaSign.abs_deltaSel_lt_proved'        [propext, Classical.choice, Quot.sound]
```
`lake build` 9065 jobs 零错误；`Audit.lean` 退出码 0；全项目 `sorryAx` 计数 0。
