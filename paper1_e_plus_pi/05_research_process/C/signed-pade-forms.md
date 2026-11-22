# C 组研究札记：同号收敛分数与 Hermite 积分

选取同侧逼近后，清分母的整数线性形式对每个允许指标都严格非零。下文给出趋零的充要尺度判据，以及有理性迫使 π 的部分商在指定位置增长的定量结论。尚未证明实际的 π 满足所需的无穷子列条件。

## 1. 可复用的证明与候选选择

第一阶段正文的 Route B 将 Niven 积分的端点移到 α=e+π。假设 α 有理可以保证多项式的端点导数整性，但 sin α=−sin e 不为零；改用 sin(πx/α) 会在微分方程中引入 (π/α)²。正文的混合积分给出 (exp(π)+1)/2，余弦积分给出 π/(2e)，均未提供和的整数线性形式。以下保留 [0,1] 上的指数核。

记 $f_n(t)=t^n(1-t)^n$，$I_n=\int_0^1e^tf_n(t)\,dt$。下表对应相邻目录 `../epi_formal/EpiFormal` 的源文件；本次核对了证明源码，没有重新编译 Lean。

| 文件与声明 | 可复用的结论 |
|---|---|
| PadeODE，`padéR_ode`；PadeIntegral，`pade_integral_repr` | $R_n=\sum_{s=0}^{2n}(-1)^sf_n^{(s)}$，$R_n+R_n'=f_n$，所以 $I_n=eR_n(1)-R_n(0)$。 |
| PadeBoundary，`padéP_eval_zero/one` 及两个导数端点引理 | $n\ge1$ 时两端的函数值为零，$n\ge2$ 时两端的一阶导数也为零。 |
| PadeDeriv，`padéP_second_deriv`；PadeRecurrence，`ibp_zero`、`padeI_eq_second`、`padeI_recurrence` | $n\ge2$ 时 $f_n''=n(n-1)f_{n-2}-2n(2n-1)f_{n-1}$，两次分部积分给出 $I_n=n(n-1)I_{n-2}-2n(2n-1)I_{n-1}$。 |
| EulerConvergents，`Hermite.E_eq_I`、`Hermite.I_pos`、`sign_eq_abs` | 令 $P_0=1,P_1=3,Q_0=Q_1=1$，两序列均满足 $X_{n+1}=(4n+2)X_n+X_{n-1}$（$n\ge1$）。则 $\delta_n=Q_ne-P_n=(-1)^nI_n/n!$，且 $I_n>0$。初值 $I_0=e-1,I_1=3-e$。 |
| 同文件，`sel_determinant`、`abs_sum_eq_two`、`abs_deltaSel_lt` | $P_nQ_{n+1}-P_{n+1}Q_n=2(-1)^{n+1}$，$Q_n|\delta_{n+1}|+Q_{n+1}|\delta_n|=2$，$|\delta_n|<1/(2nQ_n)$（$n\ge1$）。 |

**源码勘误。** PadeDeriv 中二阶导数引理上方的注释称 $n<2$ 时两边均为零。取 $n=1$ 得 $f_1=t-t^2$、$f_1''=-2$，右边也是 $-2f_0=-2$。Lean 声明带有 $n\ge2$ 的前提，证明及后续调用均不受这句注释影响。

下表令 $Q=Q_n,P=P_n,H=\lfloor Q\sqrt n\rfloor$，$g=\gcd(Q,d)$。

| 候选 | 两行系数与清分母 | 消元后误差 | 非零性 |
|---|---|---|---|
| 正文命题 8.1 的双侧 Dirichlet 见证 | $(Q,0),(0,d)$，$d\le H$，公共系数 $Qd/g\le QH/g$ | 取 $|d\pi-p|\le1/(H+1)$，原稿上界除以 $g$ 后为 $3/(2g\sqrt n)$ | 异号误差可能精确相消 |
| **所选：π 的同号收敛分数** | 同样两行，$d=q_k\le H$，只选 $k\equiv n\pmod 2$。公共系数同上，可进一步约分 | 两个正项之和，大小相当于 $d/(gnQ)+Q/(gq_{k+1})$，进一步约分时两项同除以 $h$ | 符号严格为 $(-1)^n$ |

## 2. 构造、整性与精确清分母

取 π 的正规连分数 $[a_0;a_1,\ldots]$，$p_k/q_k=[a_0;\ldots,a_k]$，从 $k=0$ 起算。对 $n\ge2$，取满足 $k\equiv n\pmod 2$ 且 $q_k\le H$ 的最大 $k$。偶侧从 $q_0=1$ 起，奇侧从 $q_1=7$ 起；$Q_3=71$，故选择总存在。以下记 $p=p_k,d=q_k,s=q_{k+1}$。同样公式允许换用其他同奇偶指标。

令 $\eta=d\pi-p$。直接相加得到 $Qe+d\pi-(P+p)$，只在 $Q=d$ 时系数相等。整数倍 $x,y>0$ 满足 $xQ=yd$ 当且仅当 $(x,y)=m(d/g,Q/g)$，$m\in\mathbb N_{>0}$。用最小正倍数得到

$$
F=\frac d g\delta_n+\frac Q g\eta
  =U(e+\pi)-V,\qquad U=\frac{Qd}{g},\quad V=\frac{dP+Qp}{g}.
$$

$g$ 同时整除 $d,Q$，故 $U,V$ 为整数。第一行误差放大 $d/g$ 倍，第二行放大 $Q/g$ 倍。若从有理逼近的和出发，裸误差为 $T=e+\pi-P/Q-p/d$，分别清分母用 $U=\mathrm{lcm}(Q,d)$ 就够了。两个分数相加后还可能约掉 $h=\gcd(U,V)$；**实际最小正清分母倍数** 为 $D_n=U/h$，因为 $P/Q+p/d=(V/h)/(U/h)$ 已既约。最终选取

$$
L_n=D_nT=u_n(e+\pi)-v_n,\qquad
(u_n,v_n)=(U/h,V/h),\qquad L_n=F/h .
$$

这里对 $T$ 清分母恰好一次，下面所有估计都针对清分母后的 $L_n$。

## 3. 单独验证非零性

写 $z=[a_{k+1};a_{k+2},\ldots]$。连分数递推的二乘二行列式给出 $q_kp_{k-1}-p_kq_{k-1}=(-1)^k$（初始 $p_{-1}=1,q_{-1}=0$）。将 $\pi=(p_kz+p_{k-1})/(q_kz+q_{k-1})$ 代入得

$$
\eta=\frac{(-1)^k}{q_kz+q_{k-1}},\qquad
\frac1{s+d}<|\eta|<\frac1s.
$$

严格界来自 $a_{k+1}<z<a_{k+1}+1$。由正积分，$(-1)^n\delta_n>0$。所选 $k$ 与 $n$ 同奇偶，两个消元系数及 $h$ 均为正。因此

$$
(-1)^n L_n=\frac{d|\delta_n|+Q|\eta|}{gh}>0 .
$$

这对每个 $n\ge2$ 成立，无须对 π 的部分商作统计假设。

## 4. 最终误差的双侧界

由 $Q|\delta_{n+1}|<1$ 及正项和恒等式，得 $|\delta_n|>1/Q_{n+1}\ge1/((4n+3)Q)$。结合上界及 $d\le s$ 得

$$
\frac1{gh}\left(\frac d{(4n+3)Q}+\frac Q{2s}\right)
 < |L_n| <
\frac1{gh}\left(\frac d{2nQ}+\frac Qs\right).
$$

因 $d\le Q\sqrt n$，上界的第一项至多 $1/(2gh\sqrt n)$。于是对任意递增子列 $n_j$ 有精确判据

$$
L_{n_j}\longrightarrow0
\quad\Longleftrightarrow\quad
\frac{g h\,q_{k+1}}{Q_n}\longrightarrow\infty .
$$

若使用未进一步约分的 $F$，判据中须去掉 $h$。单凭 $q_k\le H<q_{k+2}$ 无法将 $q_{k+1}$ 替换为 $H$。本次没有证明上述比值对 π 无界。双侧界说明若该比值有界，该选法确实无法趋零；目前也未证明有界。

## 5. 有理性将迫使指定位置出现线性增长的部分商

同一构造允许改变截断尺度。假设 $e+\pi=A/B$，$B\ge1$。对充分大的 $n$ 取 $H_B=\lfloor nQ/B\rfloor$，仍选 $q_k\le H_B$ 的最大同奇偶指标，重新据此计算 $g,h,s$。上面的整性、符号及一般双侧界仍成立。$BL_n$ 是非零整数，故

$$
1\le B|L_n|<
\frac1{gh}\left(\frac12+\frac{BQ}{s}\right),
\qquad
s<\frac{BQ}{gh-1/2}\le 2BQ.
$$

最大性的意义在于 $q_{k+2}>nQ/B$（分母为整数）。由 $q_{k+2}=a_{k+2}s+d$ 及 $d\le s$ 得

$$
a_{k+2}>\frac{n(gh-1/2)}{B^2}-1\ \ge\ \frac n{2B^2}-1 .
$$

故若和有理，则对每个充分大的 Hermite 指标 $n$，上述规则选中的 π 的部分商都必须通过这个门槛。检验给定 $B$ 时，单次违反即可排除该分母，所需条件只是该指标的同侧选择已存在。要排除所有 $B$ 仍需无穷尺度的信息。此推论未声称 π 的部分商实际具有或违反这种增长规律。

**方向检验。** 取 $n=2$，$P_2/Q_2=19/7$，$H=9$，π 的相邻相关分母是 $q_0=1,q_1=7,q_2=106$，所以 $k=0$。两行是 $7e-19>0$ 和 $\pi-3>0$，所得 $L_2=7(e+\pi)-40>0$。取 $n=3$，$P_3/Q_3=193/71$，$H=122$，$k=3$（$355/113$，下一个奇指标分母已超过 122）。此时 $71e-193<0$ 且 $113\pi-355<0$，故清分母后符号反转，和推导一致。
