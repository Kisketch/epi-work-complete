# Lean 草案隔离区（不进构建、不进审计）

> 本目录文件**不在** `epi_formal/` 内，故 `lake build` 与
> `verification/check_audit_reconcile.py`（全库 escape 关键字扫描）均不受影响。
> 转正前不得移回；移回条件见各文件头。

| 文件 | 状态 | 转正条件 |
|---|---|---|
| `ResidueUpper358_Draft.lean` | 骨架 + 2 处 `sorry`（binOf-cell 对应引理、主定理组装） | `lake env lean` 逐项消 sorry；`EpiFormal.lean`/`Audit.lean` 仍不动，待独立入口与审计行号分配后再合入 |

检查方法（串行构建完成后）：
`lake env lean verification/lean_drafts/ResidueUpper358_Draft.lean`
（import 经 LEAN_PATH 解析；不写 `.lake` 主构建产物）。
