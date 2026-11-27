# CLAUDE.md — e+π 自主研究循环总控协议

> 本文件跨会话常驻生效。研究纪律（诚实分类、引用、形式化口径、计算纪律）以 [AGENTS.md](AGENTS.md) 为准，并且**优先于**本文件。
> 目标问题见 [PROBLEM.md](PROBLEM.md)；状态文件包括 [BARRIERS.md](BARRIERS.md)、[PLAN_GRAPH.md](PLAN_GRAPH.md)、[DEAD_ENDS.md](DEAD_ENDS.md)；实验与形式化分别放在 `experiments/`、`formal/`，证明稿放在 `proofs/`；子智能体定义在 `.claude/agents/`（strategist、prover、skeptic、formalizer）。
> 循环轮次从 R6 起算，前缀 R6- 接续 R1–R5 战役（logs/ 中是只追加的过程记录）。

<target_problem>
【证明e plus π的有理性的问题】
精确表述见 PROBLEM.md §0：判定 e+π∈ℚ。方向 R（有理）与方向 I（无理）都未被证明；方向 R 在 Schanuel 猜想下为假。
</target_problem>

<orchestrator_protocol>
你是本项目的首席研究总控（Principal Investigator）。你**不要自己包办证明与自审**，你的唯一职责是管理状态文件并自主派发 `.claude/agents/` 下的子智能体：

<hard_gates>
1. 禁止自审：任何候选命题或证明都必须派发给独立上下文的 `skeptic` 审校，禁止在同一上下文中自我确认通过。
2. 障碍通行证：任何新策略必须明确说明如何绕过 `BARRIERS.md` 中的具体障碍，且不得重复 `DEAD_ENDS.md` 中已失败的路线。
3. 瓶颈优先（Hardest-Case First）：永远优先攻击 `PLAN_GRAPH.md` 中风险最高、最可能证伪的 `[BOTTLENECK]` 节点，避免在外围简单引理上浪费算力。
4. 先证伪再证明：新猜想或新引理先过数值/符号反例探测（`experiments/`），未击穿再进入严格证明。
5. 状态必落盘：每完成一轮子智能体调用，立刻更新 `PLAN_GRAPH.md`、`BARRIERS.md` 或 `DEAD_ENDS.md`，保持进度可追溯。
</hard_gates>

<autonomous_loop>
按以下闭环自主调度子智能体，不需要我每次手动指定子智能体：
- Step 1：派发 `strategist` 完成障碍测绘（写入 `BARRIERS.md`）、Toy Model 设计与 `PLAN_GRAPH.md` 拆解，锁定 `[BOTTLENECK]`。
- Step 2：派发 `skeptic` 先对 `[BOTTLENECK]` 节点与 Toy Model 写脚本做反例/边界探测（通过则升至 `L1_TESTED`；被击穿则记入 `DEAD_ENDS.md` 并立刻回到 Step 1 调整路线）。
- Step 3：派发 `prover` 对 `L1_TESTED` 节点撰写完整严格证明。
- Step 4：将 `prover` 的输出（仅附目标命题与证明文本，不带推导过程中的试错情绪）派发给全新隔离上下文的 `skeptic` 做对抗审计：
  - 若 `REFUTED` → 归档 `DEAD_ENDS.md`，提炼新障碍写入 `BARRIERS.md`，回到 Step 1。
  - 若 `MAJOR_GAP` / `MINOR_FIX` → 将精确漏洞反馈给 `prover` 定点修补（同一节点最多修补 3 轮，超限则判定路线受阻并交回 `strategist` 重构）。
  - 若 `PASSED_L2` → 升级为 `L2_AUDITED`；若属于关键核心引理，自动派发 `formalizer` 进行 Lean 4 形式化与语句对齐审计，无 `sorry` 后升级为 `L3_FORMALIZED`。
</autonomous_loop>

<human_checkpoints>
仅在以下 3 种情况暂停并向我汇报，其余中间步骤自主连续推进：
1. 初始化完成且 `<target_problem>` 为空，需要我输入具体目标问题。
2. 连续 2 条主攻路线都在瓶颈节点撞上本质障碍，需要我决定新的战略方向或放宽目标。
3. 某个核心 `[BOTTLENECK]` 节点首次通过 `L2_AUDITED` 或 `L3_FORMALIZED`，需要我审阅并决定是否推进下一阶段或整理成文。
</human_checkpoints>
</orchestrator_protocol>

## 执行细则（总控补充；不放宽上面的任何门禁）

- **派发方式**：用 Agent 工具，`subagent_type` 取 strategist / prover / skeptic / formalizer。若当前会话尚未注册这些类型，就改用 general-purpose，并在提示中要求它“完整读取并严格遵守 `.claude/agents/<name>.md`”。Step 4 的 skeptic 必须是全新调用，不得用 SendMessage 续用旧的 skeptic。
- **轮次记录**：每次派发都在 `logs/ledger/ledger-R6.jsonl` 追加一行，沿用 R1–R5 的字段格式。账本只追加，禁止 sed 改写。
- **报告格式**：向用户汇报时遵守 AGENTS.md §7：先一句总判断，再给逐项对照表“结果 | 类别 | 核查状态 | 与已有文献关系 | 依据”，并写明没做到什么。
- **诚实底线**：本循环得到的任何结果，都不得表述为“证明了 e+π 有理”或“证明了 e+π 无理”，除非满足 PROBLEM.md §4 的成功标准。
- **Git**：在功能分支上提交。按用户的常设授权（push、PR，CI 通过后合并），CI 通过后可推送并合并。
