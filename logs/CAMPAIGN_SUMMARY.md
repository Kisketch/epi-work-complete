<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# 围攻战役总结（Rounds 1–4，2026-11-25 至 2026-11-26）

**一句总判断：**四轮里有 6 个定理单元经双检通过，其中 4 个已通过 Lean 门禁：THM-0001、0003、0005、0006，均由 CI 全量构建并做公理审计。THM-0002、THM-0004 只有纸面证明。THM-0005 是唯一一个机器核实过的「无条件新结果候选」：常数 1/4 尖锐且可达。**最终目标 P1 等价于 1、e、π 在 ℚ 上线性无关，仍是公开问题；e+π 的无理性也仍是公开问题。本战役没有声称、也没有做到任何关于 π 或 e+π 的推进。**

## 1. 结果总表

| 结果 | 类别（AGENTS.md §2） | 核查状态 | 与已有文献关系 | 依据 |
|---|---|---|---|---|
| THM-0001：P1 ⇔ π ∉ ℚ+ℚe ⇔ {1,e,π} ℚ-线性无关 | 3 等价改写 | **已核实**（`RationalSpan.lean`；CI 门禁；关键定理只依赖 propext / Classical.choice / Quot.sound） | 改写 Paper 1 的 prop:rational-span | `logs/verification/LEAN-THM-0001.log` |
| THM-0002：dim_H F_τ = max(1−τ, 0) | 5 复现与修补 | 纸面证明双检 PASS；Lean 未做 | 修补 Paper 1 的 thm:eventual-dimension（"三个"改为"两个"，常数 c 显式化）；负搜索 | `artifacts/THM-0002` |
| THM-0003：L 上的二分（j‖Q_jz‖→0 ⇔ z∈L；否则 limsup ≥ 1/4） | 5 | **已核实**（`theorem2_classification` + `corollary3_gap`，本机复跑并经 CI 门禁） | 定性部分即 Kraaikamp–Liardet 1991 Thm 1′（Q_j 是 (e−1)/2 的渐近分母，数值验证 14 项）；我们的常数比它强 4 倍 | `LEAN-THM-0003.log`；`logs/evidence/Q-R2-05_*.md` |
| THM-0004：BQ_j 的度量 Khintchine 律（不要求单调） | 5 | 纸面证明双检 PASS；Lean 未做 | Philipp 1967 不覆盖 BQ_j；先例未核到 | `artifacts/THM-0003`（同文件） |
| **THM-0005：κ = inf_{z∉L} limsup j‖Q_jz‖ = 1/4，且可达** | **1 的候选**（仅负搜索） | **已核实**（`KappaSharp.lean`：`kappa_eq_quarter`；CI 运行 45759959535；陈述一致性 PASS）；偶数/奇数子列极限只有纸面证明 | KL、Larcher、Philipp、Bíró–Deshouillers–Sós 四篇全文均无精确常数；Stewart 1981 全文未取得 | `LEAN-THM-0005.log`；`artifacts/THM-0005/paper_draft.tex` |
| THM-0006：一般递推（a_j→∞，任意 D≠0）的二分 | 5（阈值 1 为候选加强） | **已核实** (A)+(B)（`GeneralDichotomy.lean`；CI 运行 45763704930）；(C) 与 L 的结构未形式化 | KL 1991 同族 | `LEAN-THM-0006.log` |
| P1 核心（π ∉ ℚ+ℚe） | — | **OPEN** | 盲攻 9 条路线全部失败，与 Paper 1 的 8 路线审计一致 | `logs/evidence/Q-R1-04.md` |

**没做到的：**以上都不涉及 π 本身、P1 或 e+π。THM-0005 是一个障碍结果：只用 Q_j 递推的论证无法突破 1/4，这实际上排除了一条通往 P1 的杠杆。

## 2. 基础设施与门禁

- **协议：**指挥官（Opus）负责调度、账本与门禁；所有数学工作由 Sonnet 子代理完成，包括 judge、worker、每个证明 2 名 checker、fresh-evaluator 和 lean-formalizer。
- **账本：**`logs/ledger/ledger-R1..R4.jsonl`，只追加。
- **交接：**`logs/handoffs/ROUND-1..4.md`。
- **注册表：**`registry/results.csv`。
- **跨轮记忆：**`logs/MEMORY.md`。
- **Lean 环境：**Windows 挂载卷上无法打开 olean，改用本机原生副本加 `lake exe cache get`。本机内存紧张，所以以 **GitHub CI（16 GB）全量 `lake build` 为正式构建**。
- **CI 公理门禁：**`.github/workflows/lean-audit.yml` 新增 siege 步骤，要求 15 个关键定理的公理清单逐字等于 `[propext, Classical.choice, Quot.sound]`，并扫描 sorry/admit。每个 PR 自动执行。
- **文献：**KL 1991、Larcher 1988、Philipp 1967 由用户提供全文后核对；BDS 2001 为开放获取；Stewart 1981 只核了元数据（付费墙，未绕过）。
- **GitHub：**PR #3、#4 已合并入 `main`；PR #5（Round 4）在 CI 通过后合并。

## 3. 失败与纠错记录（不删除）

| 类别 | 次数 | 说明 |
|---|---|---|
| route error | 4 | P1 盲攻：Lindemann–Weierstrass、Baker、Nesterenko、格方法 |
| missing literature | 6+ | AMS 403、Stewart 付费墙、zbMATH Cloudflare |
| missing certificate | 3 | 一份 worker 脚本未保留；note 未编译；其余已归档 |
| Lean unreachable | 3 | Windows 挂载卷；本机内存不足；均已绕开 |
| formalization-interface | 3 | 均在 THM-0006 形式化中解决 |
| context drift | 1 | 第 2 轮评审漏看了已有的 `theorem2_classification` |
| 指挥官失误 | 2 | `sed` 误改只追加账本，当轮还原；LaTeX 替换写乱，提交前更正 |
| premature convergence | 0 | P1 未加派深度攻关，是有意的决定 |

## 4. 展望

**近期（可执行，属类别 1/5）**
1. **THM-0006 (C) 与 Lean 内推导：**形式化权重形式 (C)，再在 Lean 中从 `GeneralDichotomy` 推出 `Classification.theorem2_classification`，让两套定义对上。
2. **THM-0005 细化：**形式化偶数/奇数子列极限；刻画所有达到 1/4 的 z（极值集合）。这是自然的新问题，可能产出新的类别 1 结果。
3. **一般常数：**对一般的 a_j→∞，阈值 1 是否尖锐？THM-0005 的构造能否推广到一切 Hurwitz 型连分数，比如 e^{2/n}、tanh(1/n)？
4. **Paper 2 短文：**编译 `paper_draft.tex`，需要 TeX 环境或在 CI 中加 LaTeX 任务。

**需要人工**
- 取得 Stewart 1981（Acta Math. Hungar. 37, 185–221）全文，它决定 THM-0005、THM-0006 能否称首创。
- 投稿前的作者信息、单位、AI 使用声明，以及人工逐行核对（next-step-workflow §5 规定 AI 不得代签）。

**关于 P1 / e+π（诚实评估）**
- P1 与 1、e、π 的 ℚ-线性无关等价。这是数论中公认的难题，现有工具（Lindemann–Weierstrass、Baker、Nesterenko、Siegel–Shidlovskii、Padé）都不控制 e 与 π 之间的线性关系。
- 本战役证明的 THM-0005 还说明：沿 e 的 Q_j 递推这条路线，在常数上已到极限。
- 继续投入应面向**有明确缺失引理的新路线**，而不是对 N6 盲攻。在找到这样的引理之前，指挥官的决定是维持 OPEN，不升级。
