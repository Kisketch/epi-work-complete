# .github/workflows/ — 持续集成

| 工作流 | 做什么 |
|---|---|
| `lean-audit.yml` | 拉 Mathlib 缓存，对 `epi_formal` 全量 `lake build`；运行 `Audit.lean`（937 条）和 8 个 Layer A 审计入口并与基准日志比对；**siege 公理门禁**要求 15 个围攻战役关键定理的公理清单逐字等于 `[propext, Classical.choice, Quot.sound]`，并检查 sorry/admit |
| `python-checks.yml` | 安装 `requirements.txt`；运行 `verify_repo_integrity.py`（只增不减、链接、审计对账）、Arb 有理排除自检、证据数字核验和技能脚本单测 |

每个 PR 都会跑这两个工作流，全部通过才合并。返回 [../../FOLDER_GUIDE.md](../../FOLDER_GUIDE.md)。
