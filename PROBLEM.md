# PROBLEM：$e+\pi$ 的有理性问题（自主研究循环的目标陈述）

> 本文件是自主研究循环（见 [CLAUDE.md](CLAUDE.md)）的**唯一目标陈述**。研究纪律以 [AGENTS.md](AGENTS.md) 为准；凡与 AGENTS.md 冲突之处，以 AGENTS.md 为准。
> 创建：2026-11-27（R6 自主循环 bootstrap）。修改本文件需在文末“变更记录”中留痕，不得静默改动命题、量词或记号。

## 0. 用户给定的目标与诚实定位

- **用户原文目标**：“证明 $e+\pi$ 的有理性的问题”。
- **精确的数学问题（判定问题）**：判定 $e+\pi\in\mathbb Q$ 是否成立。
  - **方向 R（有理）**：存在 $a\in\mathbb Z$、$b\in\mathbb Z_{\ge1}$，使 $b(e+\pi)=a$。
  - **方向 I（无理）**：对一切 $a\in\mathbb Z$、$b\in\mathbb Z_{\ge1}$，都有 $b(e+\pi)\ne a$。
- **现状（AGENTS.md §4 基线，不得矛盾）**：两个方向都**未被证明**，这是公开问题。当前唯一的硬结论是：$e+\pi$ 与 $e\pi$ 至少有一个超越（见 §3 E3）。Carella、Sarich、Foukzon 等人的“已证”声明**不被接受，禁止引用为证明**。
- **方向 R 在猜想层面为假**：Schanuel 猜想取 $z_1=1$、$z_2=i\pi$（两者在 $\mathbb Q$ 上线性无关），可推出 $\operatorname{trdeg}_{\mathbb Q}\mathbb Q(1,i\pi,e,-1)\ge2$，即 $e$ 与 $\pi$ 代数无关，从而 $e+\pi$ 超越、无理。因此：
  - 任何“$e+\pi$ 有理”的证明都将**否证 Schanuel 猜想**（这一推出关系属类别 2，依赖猜想）。
  - 本循环**不预设方向**。方向 R 只能靠给出显式的 $a/b$ 并证明恒等式来完成；方向 I 是主流预期的方向。两个方向的进展都按 AGENTS.md §2 分类，**禁止把等价改写说成“更接近证明”**。
  - 若循环的结论是“方向 R 在给定分母范围内被有限排除”，这属于**类别 4（有限排除）**，不是证明。

## 1. 记号约定

| 记号 | 含义 |
|---|---|
| $\lVert x\rVert$ | $x$ 到最近整数的距离 |
| $\mathcal L$ | $\mathbb Z+\mathbb Z\frac{e+1}2=\mathbb Z+\mathbb Z\frac{e-1}2$ |
| $Q_j,P_j$ | $Q_0=Q_1=1$，$P_0=1$，$P_1=3$；$X_{j+1}=(4j+2)X_j+X_{j-1}$（$j\ge1$）。由 R5 命题 9（纸面证明，已双检）：$P_j/Q_j\to e$，且 $Q_j$ 是 $(e-1)/2=[0;1,6,10,\dots]$ 的连分数分母 |
| $\delta_j$ | $Q_je-P_j=(-1)^jJ_j$，$J_j=\frac1{j!}\int_0^1x^j(1-x)^je^x\,dx$ |
| P1 | $\pi\notin\mathbb Q+\mathbb Qe$（Paper 1 的最终目标） |
| $\mathbf E,\mathbf G$ | Siegel E-函数值环与 G-函数值环（Fischler–Rivoal 记号，见 Paper 1 §expected-false） |

## 2. 等价形式（均为类别 3：等价改写，不降低难度）

| 编号 | 形式 | 状态 | 依据 |
|---|---|---|---|
| EQ1 | $e+\pi\in\mathbb Q \iff \pi\in\mathbb Q+(-1)\cdot e$，即 $\pi\in -e+\mathbb Q$ | 平凡 | — |
| EQ2 | P1 $\iff$ $\{1,e,\pi\}$ 在 $\mathbb Q$ 上线性无关 $\iff$ $\pi\notin\mathbb Q+\mathbb Qe$。P1 蕴含 $e+\pi\notin\mathbb Q$，但 P1 **严格强于**方向 I | **已核实**（Lean：`RationalSpan.lean`，`P1_iff_linearIndependent_of_irrational`；CI 公理门禁） | [artifacts/THM-0001](artifacts/THM-0001/) |
| EQ3 | 若 $e+\pi=a/b$，则 $b\pi=a-be\in\mathcal L$（因为 $be=2b\cdot\frac{e-1}2+b$），由 THM-0003 得 $j\lVert bQ_j\pi\rVert\to0$。反过来，“存在 $B\ge1$ 使 $j\lVert BQ_j\pi\rVert\to0$”等价于 $B\pi\in\mathcal L$，即 $\pi\in\mathbb Q+\mathbb Qe$（**¬P1**），比 $e+\pi\in\mathbb Q$ **弱**。所以这个判据刻画的是 ¬P1，不是方向 R | 已核实（THM-0003 二分；Lean）。蕴含方向的书写为 R6 总控推导，待 skeptic 复核 | [artifacts/THM-0003](artifacts/THM-0003/)、Paper 1 |
| EQ4 | 阶乘–Cantor 数字判据（Paper 1 Prop. window）：$e+\pi\in\mathbb Q$ 等价于 $\{n!\pi\}$ 的某种最终窗口条件 | Paper 1 纸面 | [Paper 1](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex) §obstructions |

## 3. 已知边界条件与可用事实

| 编号 | 事实 | 类别 / 状态 | 依据 |
|---|---|---|---|
| E1 | $e$、$\pi$ 各自超越（Hermite 1873、Lindemann 1882） | 经典定理；本表未核原文页码 | AGENTS.md 基线 |
| E2 | 单个超越性推不出和的无理性（例：$\pi$ 与 $1-\pi$ 都超越，和为 1） | 平凡 | Paper 1 Route C |
| E3 | $e+\pi$ 与 $e\pi$ 至少有一个超越：二者是 $(x-e)(x-\pi)$ 的系数；若都代数，则 $e$ 代数，矛盾 | 无条件、初等 | AGENTS.md §4 |
| E4 | 对 $z\notin\mathcal L$：$\limsup_j j\lVert Q_jz\rVert\ge1/4$，常数尖锐且可达 | **已核实**（Lean `kappa_eq_quarter`） | [artifacts/THM-0005](artifacts/THM-0005/) |
| E5 | 已知的 $\pi$ 无理性测度上界（Paper 1 记作 $\mu(\pi)\le7.1032$）沿超指数增长的 $Q_j$ 衰减到 0，**不能**提供 E4 所需的子列下界 | Paper 1 纸面；文献数值以 Paper 1 引文为准，本文件**未核到原文** | Paper 1 §feasibility |
| E6 | OpenAI 关于 $\mu(\pi)=2$ 的预印本：**未经独立专家验证**；即便成立也是非有效的，类型不对 | 未核实的外部声明 | Paper 1 §OpenAI |
| E7 | 若方向 R 成立，其分母 $b$ 的数值下界只能通过 `experiments/` 中实际运行的代码得到（类别 4）；本文件**不引用**任何未复算的文献分母界 | 待 skeptic 计算 | — |

## 4. 成功标准（什么才算“解决”）

- **方向 R**：给出显式的 $a,b$ 与 $b(e+\pi)=a$ 的完整证明。该证明须经 skeptic 隔离审计（`PASSED_L2`），并由 formalizer 用 Lean 4 形式化（`L3_FORMALIZED`，含 `#print axioms` 公理层级）。
- **方向 I**：同上，证明 $\forall a,b:\ b(e+\pi)\ne a$。
- **部分结果**：任何引理都按 AGENTS.md §2 标注类别，必须写明“它没做到什么”。**禁止**说“突破性进展”，除非满足 AGENTS.md §7 的全部条件。

## 4b. 收窄后的工作目标（用户决定，2026-11-27，人工检查点 2 之后）

- **背景**：R6 Step 1–2 的结论是，所有通向 ROOT 的路线都被 B1 挡住，满足人工检查点 2。用户选择“收窄到可证明的旁支目标”。
- **新的工作目标（旁支轨，side track）**：在 $e$ 的连分数分母、Hurwitz 型连分数与项目已有结果（K1–K4、THM-0006）周边，产出**可严格证明、可审计、可形式化**的定理。候选方向包括：
  - R6-N1：度量 strip 律；
  - R6-N2：Lindemann–Weierstrass 校准推论；
  - 一般 Hurwitz 型连分数下阈值或常数的尖锐性（推广 THM-0005/0006）；
  - strategist 提出的其他节点。
- **诚实约束**：
  - 旁支结果**不推进** ROOT、N6 或 P1。
  - 对外表述一律写明“与 $e+\pi$ 的无理性无关”。
  - 类别按 AGENTS.md §2 标注；新颖性只做负搜索，必须写明检索范围。
- **原目标保持不变**：§0–§4 不改。ROOT 仍是公开问题，循环可以随时回到主轨。

## 5. 变更记录

- 2026-11-27：初版（R6 bootstrap）。依据：AGENTS.md §4，Paper 1 §§obstructions/feasibility，logs/CAMPAIGN_SUMMARY.md，artifacts/THM-0001/0003/0005。
- 2026-11-27：新增 §4b，收窄到旁支轨（用户在人工检查点 2 的决定）。§0–§4 的命题不变。
