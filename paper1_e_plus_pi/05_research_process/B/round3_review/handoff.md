# 配套稿临界标度定理 12 独立复核

以当前 Phase2_revised.tex 的标签 thm:gauge 为准。复核结果为四个结论均由现有论证推出。圆周度量、覆盖起始指标和差分符号值得明确写出。此项为纸面审读。

## 1. 整个严格子水平集为零，整个精确水平集 σ 有限

固定 k≥1，b=2k+1，Aⱼ=4j+2，并固定最近整数舍入规则。设 Mⱼ 为 Qⱼx 的最近整数，uⱼ=Qⱼx−Mⱼ，dⱼ=Mⱼ₊₁−AⱼMⱼ−Mⱼ₋₁。递推给出 dⱼ=Aⱼuⱼ+uⱼ₋₁−uⱼ₊₁。若 Λ(x)<∞，则 uⱼ→0，故 dⱼ−4juⱼ→0。因而 Λ≤k/4 时，整数 dⱼ 最终属于 [−k,k]。严格 Λ<k/4 时，整数 dⱼ 最终属于 [−k+1,k−1]。这些是针对每个 x 的最终断言，起始指标可依赖 x。

按满足所有尾部条件的起始指标 N 与种子 (Mₙ₋₁,Mₙ) 分成可数个覆盖类。每类在级 n 的可用 Mₙ 至多有 b^(n−N) 种，此处种子指标为 N−1、N。因尾部 |uₙ|≤(k+1)/n，每种 Mₙ 的区间直径至多 2(k+1)/(nQₙ)；n≥2(k+1) 时，该直径至多 1/Qₙ，覆盖成本至多 b^(−N)。将 b 换成 2k−1 作为严格子水平的分支数，则总成本趋于 0。边界 k=1 时严格子水平的分支数等于 1，论证照常成立。有限测度类与精确水平相交即为 σ 有限分解。

## 2. 精确水平集有正测度

固定种子 Mₙ₋₁=Mₙ=0，给 [-k,k] 中的 dⱼ (j≥N) 任意赋值，从递推求 Mⱼ。令 Wⱼ=Mⱼ₊₁Qⱼ−MⱼQⱼ₊₁，有 Wⱼ=dⱼQⱼ−Wⱼ₋₁。由 Q 的相邻增长因子 ≥2，归纳得 |Wⱼ|≤2kQⱼ，并由伸缩和得 x=lim Mⱼ/Qⱼ 及 |x−Mⱼ/Qⱼ|≤4k/Qⱼ₊₁。选 N 充分大后，|uⱼ|<1/8 对所有 j≥N 一致成立。这证明刚构造的整数确为最近整数。上面的误差恒等式给出 Λ(x)≤k/4。

设 h 是实轴区间长度，1/Qₙ₊₁≤h<1/Qₙ。区间内两点在 N≤j<n 对应的 Mⱼ 之差小于 Qⱼ/Qₙ+1/4≤3/4，故相同。在 j=n 处，该差严格小于 5/4，至多两种整数值。初始种子固定，M_N 至 M_n 决定 d_N 至 d_{n−1}。独立均匀字母测度给该区间的质量至多 2b^(−(n−N))≤2b^(N+1)hₖ(h)。有限前段不影响小直径界。质量分布原理推出该构造集标度测度为正。严格子水平集已证测度零，减去它即得精确水平的正测度。

圆周度量可直接处理。阈值 N 再选大，使 8k/Q_{N+1}<1/2，所有构造点位于 [−4k/Q_{N+1},4k/Q_{N+1}]。此区间投影到圆周是等距嵌入，故质量估计直接传到圆周。总水平集的覆盖亦可从实轴投影，投影是 1-Lipschitz。

## 3. 精确水平集的测度无限

精确水平 E 为 Borel，因为各 x↦j||Qⱼx|| 连续，limsup 为 Borel。分类定理给 y∈L 时 j||Qⱼy||→0。逆三角不等式给 |j||Qⱼ(x+y)||−j||Qⱼx|||≤j||Qⱼy||。故 E 在 L/Z 的平移下不变。L/Z 稠密，由 (e+1)/2 无理得出。若 0<ℋ^{hₖ}(E)<∞，将标度 Hausdorff 测度限制在 E 并归一化，得到 Borel 概率 ν。平移为等距变换，故 ν 在 L/Z 下不变。对连续函数，平移参数的收敛给一致收敛，故 ν 在全圆平移下不变。利用 Haar 概率唯一性，ν 等于归一化 Lebesgue 测度。有限水平集的维数零推出 E 的 Lebesgue 测度为零，然而定义给 ν(E)=1，矛盾。

## 可插入英文补强

“Choose the starting index (N) also so that (8k/Q_{N+1}<1/2). The constructed points lie in ([-4k/Q_{N+1},4k/Q_{N+1}]), which projects isometrically to the circle for its usual geodesic metric. Thus the mass-distribution estimate holds on the circle.”

“For every (yin L), the reverse triangle inequality gives
[
 igl|j|Q_j(x+y)|-j|Q_jx|igr|le j|Q_jy|longrightarrow 0 .
]
Consequently every exact level is invariant under (L/mathbb Z).”

“Put (E_k={x:Lambda(x)=k/4}). If (0<mathcal H^{h_k}(E_k)<infty), the Borel probability (
u(A)=mathcal H^{h_k}(Acap E_k)/mathcal H^{h_k}(E_k)) is invariant under translations by (L/mathbb Z). By uniform continuity of continuous functions on the circle and density of (L/mathbb Z), it is translation invariant. Uniqueness of normalized Haar measure identifies (
u) with normalized Lebesgue measure, contradicting (
u(E_k)=1) and the Lebesgue nullity of (E_k).”

## 另查数值表述

谱隙定理后的 Remark 有一处将有限窗口数值结果写成若干常数的 Λ=∞。该断言超出已有数值证据。建议用 “Section~\ref{sec:num} reports finite-window maxima for the test inputs.” 替换；数值节已明确自身范围。
