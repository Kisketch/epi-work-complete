# registry/ — 结果注册表

- **`results.csv`**：每个定理或重要尝试一行，是查状态的首选入口。主要列：
  - `ID`：如 THM-0005
  - `status`：IDEA / IN-SIEGE / NEEDS-LEAN / LEAN_VERIFIED / PAPER_DRAFT / BLOCKED 等
  - `verification_status`：核查到什么程度、依据什么证据
  - `value_assessment`：含 AGENTS.md §2 类别
  - `lean_module`、`file_location`、`ledger_link`、`handoff_link`、`next_step`
- **`shards/`**：每轮结束时的注册表快照（R1-seed、R1..R4-final），只作历史留存。

当前结论：THM-0001、0003、0005、0006 为 LEAN_VERIFIED；THM-0005 为类别 1 的候选；P1-CORE 为 OPEN。逐项说明见 [../artifacts/README.md](../artifacts/README.md)。返回 [../FOLDER_GUIDE.md](../FOLDER_GUIDE.md)。
