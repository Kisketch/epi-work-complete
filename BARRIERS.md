# BARRIERS：$e+\pi$ 有理性问题的根本障碍

> 由 strategist 维护，总控每轮落盘。**每条新策略都必须写明它绕过了哪一条 Bk、怎样绕过**（CLAUDE.md 硬门禁 2）。只能追加；作废的条目标 `[SUPERSEDED by Bk]`，不删除。
> 初版（2026-11-27）从仓库既有记录整理而来：logs/evidence/Q-R1-04.md（9 条路线）、Paper 1 §obstructions / §feasibility、logs/CAMPAIGN_SUMMARY.md。

| 编号 | 障碍 | 精确内容 | 被它挡住的路线 | 来源 |
|---|---|---|---|---|
| B1 | **e–π 关系空白** | 现有已证定理（Lindemann–Weierstrass、Baker、Nesterenko、Siegel–Shidlovskii）都不控制 $e$ 与 $\pi$ 之间的代数关系，“$e+\pi\in\mathbb Q$”恰好落在这块空白里 | 几乎全部；Nesterenko 矛盾挖掘的 7 条路径 | Paper 1 §feasibility；Q-R1-04 #4 |
| B2 | **指数位置错配** | Hermite–Lindemann 需要“代数点处的指数”。从 $e^{iS}=-e^{ie}$ 出发，右边指数 $ie$ 是超越数，定理不提供任何信息 | LW / Hermite–Lindemann | Paper 1 Route C；Q-R1-04 #1 |
| B3 | **$e$ 不是已知的代数对数** | Baker 理论处理 $\beta_0+\sum\beta_j\log\alpha_j$（$\alpha_j,\beta_j$ 代数）；$e=\log\alpha$ 等价于 $e^e$ 代数，而这本身是公开问题 | Baker 线性型 | Paper 1 Route C；Q-R1-04 #2 |
| B4 | **E-函数值缺口** | 没有已知的 E-函数在代数点取值 $\pi$；$\pi\notin\mathbf E$ 是猜想 | Siegel–Shidlovskii；E/G 条件链 | Q-R1-04 #3；Paper 1 §expected-false |
| B5 | **核函数缺口（Niven 型）** | 端点整性对任意有理端点 $a/b$ 都成立，但没有在 $e+\pi$ 处为零、且导数算术可控的核：$\sin(e+\pi)=-\sin e\ne0$；改用 $\sin(\pi x/\alpha)$ 会引入 $(1+e/\pi)^2$ 的幂，整性崩溃 | Niven / Beukers 积分 | Paper 1 Route B |
| B6 | **方向错误（上界 vs 下界）** | Niven/Beukers 型积分给出无理性证明或逼近**上**界（积分趋于 0）；P1 路线需要的是沿稀疏子列的**下**界 | 积分正性 | Paper 1 §feasibility “Integral positivity” |
| B7 | **联合逼近缺口** | 直接组合 $e$ 与 $\pi$ 的收敛分数，三角不等式误差上界 $\ge2$；没有耦合的 Padé 系统，也没有非零性和分母估计 | 联合 Padé；Route D | Paper 1 Route D；Q-R1-04 #5 |
| B8 | **$Q_j$ 递推的常数天花板** | 沿 $e$ 的 $Q_j$ 递推，对 $z\notin\mathcal L$ 只能保证 $\limsup j\lVert Q_jz\rVert\ge1/4$，而且 1/4 尖锐可达（THM-0005）；只用该递推的论证无法给出更多。要排除 $\pi\in\mathcal L$ 型关系，需要一个关于 $\pi$ 的子列分布事实（例如 $\{n!\pi\}$ 或 $\lVert BQ_j\pi\rVert$ 的下界），而这类事实与 $\{(3/2)^n\}$ 同难度 | Q_j 稀疏 limsup 路线；阶乘窗口路线 | THM-0005；Paper 1 Route A；Q-R1-04 #7 |
| B9 | **无理性测度类型不对** | $\mu(\pi)$ 的上界（以及未核实的 $\mu(\pi)=2$）控制的是**所有**分母上的最坏情况，非有效，给不出 B8 所需的子列下界 | 测度路线；$\operatorname{irr}(\pi)>2$；Flint Hills | Paper 1 §feasibility、§conclusion |
| B10 | **等价改写不降难度** | P1 $\iff$ $\{1,e,\pi\}$ 线性无关（THM-0001）、阶乘–Cantor 判据、格 / Minkowski 重述，都只是换坐标 | 格方法；判据形式化 | Q-R1-04 #8；THM-0001 |
| B11 | **方向 R 与猜想冲突** | Schanuel 猜想 ⇒ $e,\pi$ 代数无关 ⇒ $e+\pi$ 超越。方向 R 的证明必须否证 Schanuel 猜想；任何“构造 $a/b$”的尝试都必须先过有限排除（类别 4）的数值门槛 | 方向 R 的一切构造 | PROBLEM.md §0（类别 2 推理） |
| B12 | **预期为假的必要条件不能当攻击路线** | $\operatorname{irr}(\pi)>2$、Flint Hills 级数发散、$\pi\in S$ 都预期为**假**，沿它们推进不会产生矛盾 | 这三条“充分条件”路线 | Paper 1 §conclusion |

## 变更记录
- 2026-11-27：初版 B1–B12（R6 bootstrap，由总控从仓库记录整理；尚未经 strategist 复核）。
