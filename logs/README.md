<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# logs/ — 围攻战役过程记录（只供复查，不得引用）

| 路径 | 内容 |
|---|---|
| [CAMPAIGN_SUMMARY.md](CAMPAIGN_SUMMARY.md) | 第 1–4 轮总结与展望 |
| [PREVIOUS_RESEARCH_SUMMARY.md](PREVIOUS_RESEARCH_SUMMARY.md) | Phase 0 盘点 |
| [SKILL.md](SKILL.md) | 围攻协议、角色、门禁、账本格式 |
| [MEMORY.md](MEMORY.md) | 跨轮失败模式 |
| `blueprint/` | 蓝图与各轮查询。Q-R1-*、Q-R2-01..03 由 judge 写出；Q-R2-04（T5/T6 新颖性）、Q-R2-05（全文核对）、Q-R3-01（Stewart）由指挥官直接下达，任务文本记录在对应 evidence 与账本中 |
| `ledger/` | `ledger-R1..R4.jsonl`，**只追加**；状态变化追加新行并写明 prev_status 与 reason |
| `handoffs/` | `ROUND-1..4.md` |
| `evaluations/` | fresh-evaluator 与 Lean 门禁裁决 |
| `evidence/` | 文献与盲攻证据（全文 PDF 不入库，只存已核书目与转述） |
| `verification/` | `LEAN-THM-*.log`（门禁证据）；`R1/`、`R2/`、`R4/` 数值复核脚本（类别 4，只作佐证）。`LEAN-THM-0003B.log` 是指向 `LEAN-THM-0003.log` 的占位文件，保留它是为了让只追加账本里的旧引用仍然有效 |
