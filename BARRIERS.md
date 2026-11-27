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
| B8 | [SUPERSEDED by B13] **$Q_j$ 递推的常数天花板** | 沿 $e$ 的 $Q_j$ 递推，对 $z\notin\mathcal L$ 只能保证 $\limsup j\lVert Q_jz\rVert\ge1/4$，而且 1/4 尖锐可达（THM-0005）；只用该递推的论证无法给出更多。要排除 $\pi\in\mathcal L$ 型关系，需要一个关于 $\pi$ 的子列分布事实（例如 $\{n!\pi\}$ 或 $\lVert BQ_j\pi\rVert$ 的下界），而这类事实与 $\{(3/2)^n\}$ 同难度 | Q_j 稀疏 limsup 路线；阶乘窗口路线 | THM-0005；Paper 1 Route A；Q-R1-04 #7 |
| B9 | [SUPERSEDED by B14] **无理性测度类型不对** | $\mu(\pi)$ 的上界（以及未核实的 $\mu(\pi)=2$）控制的是**所有**分母上的最坏情况，非有效，给不出 B8 所需的子列下界 | 测度路线；$\operatorname{irr}(\pi)>2$；Flint Hills | Paper 1 §feasibility、§conclusion |
| B10 | **等价改写不降难度** | P1 $\iff$ $\{1,e,\pi\}$ 线性无关（THM-0001）、阶乘–Cantor 判据、格 / Minkowski 重述，都只是换坐标 | 格方法；判据形式化 | Q-R1-04 #8；THM-0001 |
| B11 | **方向 R 与猜想冲突** | Schanuel 猜想 ⇒ $e,\pi$ 代数无关 ⇒ $e+\pi$ 超越。方向 R 的证明必须否证 Schanuel 猜想；任何“构造 $a/b$”的尝试都必须先过有限排除（类别 4）的数值门槛 | 方向 R 的一切构造 | PROBLEM.md §0（类别 2 推理） |
| B12 | [SUPERSEDED by B15] **预期为假的必要条件不能当攻击路线** | $\operatorname{irr}(\pi)>2$、Flint Hills 级数发散、$\pi\in S$ 都预期为**假**，沿它们推进不会产生矛盾 | 这三条“充分条件”路线 | Paper 1 §conclusion |

## R6 Step 1 strategist 复核追加（2026-11-27）

**复核结论**：B1–B7、B10、B11 无实质错误，保留原文。B4 可再补一句对偶形式（$e\notin\mathbf G$ 同样足以推出结论，同样未证），已并入 B16 的迁移表，不单独作废 B4。B8、B9、B12 各有一处错误或歧义，已标 `[SUPERSEDED]`，修正版为 B13–B15。B16–B19 是新增的遗漏障碍。

凡标“strategist 推导”的内容，都是纸面分析，**未经 skeptic 审核**；凡标“Paper 1 自报”的 Lean 结论，本轮**未复跑**（AGENTS.md §5）。

| 编号 | 障碍 | 精确内容 | 被它挡住的路线 | 来源 |
|---|---|---|---|---|
| B13 | **$Q_j$ 尺度的 π 专属下界缺失**（修正 B8） | 由 THM-0003（K2），对任意 $z$：$z\notin\mathcal L\iff j\lVert Q_jz\rVert\not\to0\iff\limsup_j j\lVert Q_jz\rVert\ge1/4$；THM-0005 说明 1/4 尖锐可达。配合 prop:rational-span，P1 $\iff\forall B\ge1\ \exists c_B>0$：$\lVert BQ_j\pi\rVert\ge c_B/j$ 对无穷多 $j$ 成立。这是**等价改写（类别 3）**，不是降难度。要证它，必须提供一个关于 π 在稀疏尺度 $BQ_j$ 上的下界事实，而这类事实对 π 全部未知。**B8 的两处修正**：(a) 阶乘窗口 $\{n!\pi\}$ 只针对斜率 $-1$（即 $e+\pi\notin\mathbb Q$，Paper 1 thm:factorial-quantization 取 $k=1$），不针对整个 $\mathcal L$ 或 P1；(b) “与 $\{(3/2)^n\}$ 同难度”只是启发式类比（Paper 1 也只这样表述），**并无已证的难度等价**，不得当定理引用 | D7、D9；一切“先证 π 的稀疏下界”路线 | THM-0003/0005；Paper 1 §lean-escape、thm:factorial-quantization；strategist 复核 |
| B14 | **测度信息的尺度错配**（修正 B9） | 任何形如 $\operatorname{irr}(\pi)\le\mu_0$ 的结论（Paper 1 引 ZZ2020 的 $\mu_0\approx7.1032$；即便是未核实的 $\mu_0=2$）只能给出 $\lVert q\pi\rVert\ge q^{1-\mu_0-\varepsilon}$（$q$ 充分大）。这是 $q$ 的**多项式**衰减；而 B13 要求在 $q=BQ_j$ 处有 $\gg1/j$。由递推 $Q_{j+1}<(4j+3)Q_j$ 且 $Q_j$ 至少指数增长（Paper 1 §lean-escape），$j$ 相对 $\log Q_j$ 只是次线性增长，所以无论 $\mu_0$ 取何值、有效与否，测度型下界都远小于所需量。**B9 的错误**：原文“非有效”被当成障碍的原因。已发表上界是否有效，本条**未核到**，而且与障碍无关；真正的原因是尺度与类型不对。另外，测度结论对 $r-e$ 同样成立（见 B16），本来就无法把 π 与 $\mathbb Q-e$ 分开。对 adaptive strip（Paper 1 thm:adaptive-strip）同理：它需要在指定尺度上有**收敛分数级**质量的 π 逼近，Padé 型 $q^{-\tau}$（$\tau<1$）不够（D16） | 测度路线；$\operatorname{irr}(\pi)$ 上界程序；用 Padé 逼近填 strip（D16） | Paper 1 §feasibility、§lean-escape “three-route survey”、thm:measure-reduction；strategist 推导 |
| B15 | **逻辑方向：预期为真的必要条件驳不倒**（修正 B12） | B12 把 $\operatorname{irr}(\pi)>2$、Flint Hills 级数发散、$\pi\in S$ 称作“预期为假的**必要**条件”，这是**标签方向错误**。正确表述有两种，彼此等价：(i) 它们是方向 I 的**充分**条件，且预期为**假**，所以无法证明；(ii) 等价地，它们的否定（$\operatorname{irr}(\pi)=2$、级数收敛、$\pi\notin S$）是“$e+\pi\in\mathbb Q$”的**必要**条件，且预期为**真**，所以无法被驳倒、导不出矛盾。可用的必要条件必须在导出矛盾的方向上预期为假，例如“π 是 Hurwitz 数”“$\pi\in\mathbf E$”“$e\in\mathbf G$”，但它们都被 B4/B13/B16 挡住。另外，$\pi\in S$ 一支依赖未审预印本 Bertolin2026，属**类别 2** | D12 | Paper 1 §expected-false、§“Surviving targets”；strategist 复核 |
| B16 | **可数集分离 / 迁移障碍** | 方向 I $\iff\pi\notin\mathbb Q-e$；P1 $\iff\pi\notin\mathbb Q+\mathbb Qe$。两者都是可数集。证明必须用到某个性质 $\mathsf P$，满足 $\mathsf P(\pi)$ 为真，且对**每个** $x=r-e$（或 $r+se$）$\mathsf P(x)$ 为假。**迁移检验**：把 π 的每个已证性质搬到 $r-e$ 上看——① $\operatorname{irr}(\pi)\le7.1032$ 对应 $\operatorname{irr}(r-e)=2$，已知为真，无用；② π 超越对应 $r-e$ 超越，已知为真，无用；③ Nesterenko（π、$e^\pi$、$\Gamma(1/4)$ 代数无关）对应“$e,e^e,\Gamma(1/4)$ 代数无关”（Paper 1 prop:nest-transfer），公开且**预期为真**，导不出矛盾；④ $\pi\in\mathbf G$（Paper 1 引 FR2014）对应 $e\in\mathbf G$，公开且**预期为假**（由 $\mathbf E\cap\mathbf G=\overline{\mathbb Q}$ 猜想推出）。④ 是一根“好杠杆”，但被 B4 的对偶挡住：没有任何已知技术能证明某个具体数 $\notin\mathbf G$。另有 EscapeBoundary.lean（Paper 1 自报，未复跑）：把 π 换成 $A/B-e$ 后，递推、取整等通用条件仍然成立，因而这类条件不能单独推出结论 | 一切只输入“通用性”或“测度型”信息的路线；D7、D9、D13 族 | Paper 1 lem:invariance、lem:mue、prop:nest-transfer、§expected-false、§lean-escape；strategist 推导 |
| B17 | **校准障碍：稀疏 / CF 尺度事实只作为“输出”出现** | Toy T1（见 PLAN_GRAPH）：对 $x\in\{e^{\sqrt2},\cos1\}$，Lindemann–Weierstrass 给出 $1,e,x$ 线性无关，再经 THM-0003 推出 $\forall B:\limsup_j j\lVert BQ_jx\rVert\ge1/4$（R6-N2）。可见这类稀疏事实可以作为线性无关定理的**推论**得到。但在项目记录中，我们没有见到哪个非 Hurwitz 型经典常数，其 $Q_j$ 尺度或 CF 尺度事实是**直接**从它自身的解析定义证出来的（**文献负搜索未做**，检索范围仅限本仓库 Paper 1/2 与 logs/evidence）。推论：B8/B13 族路线要成功，就得成为稀疏事实的**新来源**；它们在信息上被 B1 型工具支配。B8 不是本质障碍，只是 B1 的症状 | D7、D9、cor:strip-escape 一族作为“主攻”的资格 | strategist 推导（Toy T1）；THM-0003；LW（经典，本条未核原文页码） |
| B18 | **CM 点障碍（Nesterenko 机制）** | Nesterenko 方法通过 Ramanujan 函数 $P,Q,R$ 在 $q=e^{2\pi i\tau}$ 处的值工作；只有在 CM 点（如 $\tau=i$）这些值才能用 π、$\Gamma(1/4)$ 表示。若要让 $e$ 出现，须取 $q=e^{-1}$，即 $\tau=i/(2\pi)$，这不是 CM 点，此时 $P,Q,R$ 的值是新的未知常数。$E_2$ 的拟模变换把 $q=e^{-1}$ 与 $q'=e^{-4\pi^2}$ 用含 π 的系数联系起来，但假设 $e+\pi\in\mathbb Q$ 只能让这两点联合生成域的超越次数至多降 1；单点下界（每点 $\ge3$，一般 $q$ 形式据通行表述，**原文未核到**）推不出矛盾。要产生矛盾，需要两点联合的下界，其强度接近 Schanuel 型 | D4 的一般 $q$ 推广（D14） | strategist 推导；Paper 1 引 Nesterenko1996（原文未核到） |
| B19 | **乘性分离（留数型指数周期）** | 形如 $\int_{\mathbb R}R(x)e^{iax}\,dx$ 的恒等式（$R\in\overline{\mathbb Q}(x)$，$a\in\overline{\mathbb Q}$；含实轴极点的主值情形同理）由留数定理等于 $2\pi i\sum\operatorname{Res}$，而每个留数都落在 $\overline{\mathbb Q}[e^{ia\beta}]$ 中（$\beta$ 为极点）。所以 π 只作为**整体乘因子**出现，这类恒等式只能约束 $\pi\cdot(\text{指数值})$ 型乘积，不能约束 $e+\pi$ 型加法关系。Paper 1 的 bridge 4（$\int_0^\infty\cos x/(1+x^2)dx=\pi/(2e)$）正是这一类 | D15；bridge-identity 路线的整个留数类 | strategist 推导（留数定理；未审）；Paper 1 §sub:bridges |

## 变更记录
- 2026-11-27：初版 B1–B12（R6 bootstrap，由总控从仓库记录整理；尚未经 strategist 复核）。
- 2026-11-27（R6 Step 1 strategist）：复核 B1–B12。B8、B9、B12 标 `[SUPERSEDED]`，修正版为 B13（阶乘判据只针对斜率 −1；“同难度”降为启发式）、B14（“非有效”不是障碍原因，改为尺度与类型错配）、B15（必要/充分条件的标签方向更正，并标出 $\pi\in S$ 一支属类别 2）。新增 B16（可数集分离/迁移）、B17（校准，来自 Toy T1）、B18（CM 点）、B19（乘性分离）。B16–B19 中的推导均为纸面分析，待 skeptic 复核。
