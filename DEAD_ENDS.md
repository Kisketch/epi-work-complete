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
（尚无）
