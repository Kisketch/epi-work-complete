# DEAD_ENDS：已证伪或卡死的路线

> 只追加，不删除。每条记录写明：路线、精确失效步骤、最小反例或阻断事实、可复用的教训。strategist 提出新路线前**必须**逐条比对本文件（CLAUDE.md 硬门禁 2）。
> 初版条目 D1–D13 来自 R1–R5 战役与 Paper 1。来源文件已在表中注明，均为过程记录（LOG-ONLY），不得作为文献引用。

| 编号 | 路线 | 精确失效步骤 | 最小反例 / 阻断事实 | 教训 | 对应障碍 | 来源 |
|---|---|---|---|---|---|---|
| D1 | Lindemann–Weierstrass / Hermite–Lindemann | 由 $S=e+\pi$ 代数推出 $e^{iS}=-e^{ie}$，然后无法继续 | 右边指数 $ie$ 是超越数，定理无输出；该恒等式不需要任何假设就成立 | 必须先检查恒等式是否只是重言式 | B2 | Paper 1 Route C；Q-R1-04 #1 |
| D2 | Baker 线性型 | 把 $e$ 写成 $\log\alpha$ | 无已知表示；“$e$ 不是代数数的对数”本身未证（等价于 $e^e$ 超越） | 不要引用流行说法当定理 | B3 | Paper 1 Route C；Q-R1-04 #2 |
| D3 | Siegel–Shidlovskii | 找一个在代数点取值 $\pi$ 的 E-函数 | 未知；$\pi\notin\mathbf E$ 是猜想 | — | B4 | Q-R1-04 #3 |
| D4 | Nesterenko（$\pi,e^\pi,\Gamma(1/4)$） | 从 $e+\pi\in\mathbb Q$ 推出与 Nesterenko 定理矛盾 | 7 条推导路径全部断在“定理不涉及 $e$” | 模形式三元组不含 $e$ | B1 | Paper 1 §feasibility；Q-R1-04 #4 |
| D5 | $e^z$ 与 $\pi$ 族的联合 Padé | 构造耦合系统 | 没有耦合系统，没有非零性 / 分母估计 | 需要的是能同时逼近 $e$ 与 $\pi$ 的**同一**有理系统 | B7 | Q-R1-04 #5 |
| D6 | Schanuel 在 $(1,i\pi)$ | 直接得到 P1 | 依赖猜想（类别 2） | 条件结果不得说成无条件 | B11 | Q-R1-04 #6 |
| D7 | $Q_j$ 稀疏 limsup 路线 | 需要 $\limsup_j j\lVert BQ_j\pi\rVert>1/8$ 对所有 $B$ | $\pi$ 的连分数无可用结构；1/4 是这一递推的天花板（THM-0005） | 只用 $Q_j$ 递推的论证在常数上已到极限 | B8 | THM-0005；Q-R1-04 #7 |
| D8 | 格 / Minkowski | 重述线性无关 | 循环论证，没有新信息 | 换坐标不降难度 | B10 | Q-R1-04 #8 |
| D9 | 级数与整数序列（阶乘窗口） | 需要 $\{n!\pi\}\le\frac12$ 无穷多次 | $\{n!\pi\}$ 的分布完全未知，连稠密性都未知 | 与 $\{(3/2)^n\}$ 同难度 | B8 | Paper 1 Route A |
| D10 | Niven 型积分移植到 $e+\pi$ | 端点核 | $\sin(e+\pi)=-\sin e\ne0$；改用 $\sin(\pi x/\alpha)$ 会带入 $(1+e/\pi)^2$ 的幂，整性崩溃 | 端点整性不是瓶颈，**核**才是 | B5 | Paper 1 Route B |
| D11 | 收敛分数乘积分母（Route D） | 证明 $\lvert b_nd_n(e+\pi)-(\cdot)\rvert\to0$ | 三角不等式只能给出 $\ge2$ 的上界；有效界缺失 | 需要相消或公分母节省，不能逐项估计 | B7 | Paper 1 Route D |
| D12 | $\operatorname{irr}(\pi)>2$ / Flint Hills 发散 / $\pi\in S$ 当作攻击路线 | 这些条件预期为假 | — | 必要条件必须在“导出矛盾”的方向上预期为假才有用 | B12 | Paper 1 §conclusion |
| D13 | 由测度上界（含 $\sin$ 下界）逐项推出 $\operatorname{irr}(\pi)\le5/2$ | 当 $n>\pi\lvert m\rvert$ 时不等式反向 | 逐项论证在 $n>\pi\lvert m\rvert$ 时失效（Paper 1 中保留了历史记录） | 检查不等式在**所有**参数范围上的方向 | B9 | Paper 1 §Alekseyev |

## R6 自主循环新增

> D14–D16 是 R6 Step 1 strategist 的纸面分析，**未经 skeptic 复核**，不得当作定理引用；skeptic 若推翻其中任何一条，请在本表追加更正行。D17 不是失败路线，而是“已饱和、低信息”的不重复标记。

| 编号 | 路线 | 精确失效步骤 | 最小反例 / 阻断事实 | 教训 | 对应障碍 | 来源 |
|---|---|---|---|---|---|---|
| D14 | Nesterenko 一般 $q$ 版本取 $q=e^{-1}$，配合 $E_2$ 拟模变换（D4 的推广） | 在 $e+\pi=r$ 的假设下，把 $q=e^{-1}$ 与 $q'=e^{-4\pi^2}=e^{-4(r-e)^2}$ 两点的 $P,Q,R$ 值放进同一个域 | 假设至多让联合超越次数降 1，而单点下界只有 $\ge3$，两者不冲突；两点联合下界未知，所需强度接近 Schanuel 型 | 只能拿到单点超越次数下界的定理，不可能被一个“降 1”的假设驳倒 | B18、B1 | R6 strategist 分析 |
| D15 | 留数型指数周期恒等式（把 bridge 4 推广到一般有理函数 $R$） | 由 $\int_{\mathbb R}R(x)e^{iax}dx$ 求 $e,\pi$ 的加法关系 | 由留数定理，值属于 $2\pi i\cdot\overline{\mathbb Q}[e^{ia\beta_k}]$，π 只作为整体因子出现 | 先检查恒等式里 π 是加法出现还是乘法出现 | B19 | R6 strategist 分析；Paper 1 §sub:bridges |
| D16 | 用 π 的 Padé 型（非收敛分数）逼近填 adaptive strip（Paper 1 thm:adaptive-strip） | 需要 $q\asymp Q_j\cdot(\le j)$ 的分母，并且 $\lvert q\pi-p\rvert<c/(BQ_j)$ | 这是收敛分数级的质量；Padé 构造的质量 $q^{-\tau}$（$\tau<1$）在该尺度上远远不够 | strip 判据要求 π 在**指定尺度**上有**最佳逼近**，而测度型信息给不了这一点 | B14、B13 | R6 strategist 分析 |
| D17 | 继续扩大方向 R 的有限排除，或在小 $B$ 上做 π 的 $e$ 尺度数值（**低信息，已饱和**） | 不是失败，而是信息量趋近于零 | Paper 1 prop:denominator-bounds 已给出 $q\ge10^{500018}$（两台机器复现，Paper 1 自报）；prop:farey-gap 已给出 $b<3635695100$ 时对所有 $j\ge8$ 有 $D_j(b)\ne0$（Lean 证书，Paper 1 自报，未复跑）；§lean-reduction 已算 $B\le20$、$j\le80$。按 Paper 1 自己的说明，界 $\approx10^{D/2}$ 只反映计算长度 | 有限排除只是证伪门槛，不是进展；除非有新的对照设计，否则不要重复 | B11、B16 | Paper 1 §sub:denominator-bounds、§lean-reduction |
| D18 | 把 THM-0006 阈值 1 的尖锐性（一般 $a_j\to\infty$）与 THM-0005 的极值集合当作**新**旁支目标重做（R6 旁支 Step 1 strategist，2026-11-27 去重） | 不是失败，是**重复**：Paper 2 thm:growing-rec-spectrum 已给出任意增长商递推的全谱 $\mathbb Z_{\ge0}\cup\{\infty\}$（含阈值 1 尖锐且可达）；thm:trichotomy 与 `FullSpectrumDiscrete.lean`、`GaugeLiminfComplete.lean`、`QuarterPoint*.lean` 已刻画 $\{\Lambda=1/4\}$ 等水平集（缺陷字母表、陪集坍缩、临界 gauge、维数 0） | 均为作者自报 Lean，本轮未复跑；`logs/CAMPAIGN_SUMMARY.md`“展望”第 2、3 条与 Paper 2 现状不同步 | 提新目标前先 grep Paper 2 / 2D / 2E 的摘要与 `EpiFormal/` 声明；剩余的设定差异（$a_j\ge1$、任意初值、$L_D$ 对 $L_G$）只作对账（R6-S6，类别 5） | — | PLAN_GRAPH §R6 旁支轨 S.0 |

## R6 旁支流程记录（strategist，2026-11-27）

> D19 是**流程记录**，不是数学失败：R6-S2 的陈述没有被证伪，证明链 §0–§7 在 4 次隔离审计中没有被报出缺口。记录它是为了满足“失败记录保留”与 CLAUDE.md 硬门禁 2（不重复失败做法）。

| 编号 | 路线 | 精确失效步骤 | 最小反例 / 阻断事实 | 教训 | 对应障碍 | 来源 |
|---|---|---|---|---|---|---|
| D19 | 对 R6-S2 第 1 版证明稿（proofs/R6-S2.md，含 §8 附注、§9 备注与修补记录）做原地修补（流程层面） | 首审与 3 次复审都是 MINOR_FIX，3 轮修补预算用尽。证明链内的真实问题（规范标签定义；§5.4、§5.5 退化情形的严格不等号）都已修正；剩余发现集中在不承重的 §8 附注：第 2 轮复审 m1（第 1 轮修补新增的 $8K\tau_{\max}$ 界为假，反例 $W=(1,9,9)$）、第 3 轮复审 n1（§8 把只在模 1 下成立的关系写成实数等式，反例 $W=(1,1)$、$\beta=\alpha/2$）、n2（§8 中“$y_{n_k}$ 远离 $\pm1/2$”无依据） | 每轮修补都在审计范围内的附注中新增解释性文字，新增文字成为下一轮的主要发现来源，修补不收敛 | 待审文件只放承重证明链；解释、一致性讨论与修补记录放进不入审计的单独文件；修补只改被点名的位置，禁止在待审文件新增附注（PLAN_GRAPH §“R6-S2 路线重构”D-1、D-5） | —（非数学障碍，不追加 BARRIERS） | 账本 `logs/ledger/ledger-R6.jsonl` R6-S2 各行；`experiments/R6-S2/audit_S2_*`、`reaudit_S2_*`、`reaudit2_S2_*`、`reaudit3_S2_*` |
