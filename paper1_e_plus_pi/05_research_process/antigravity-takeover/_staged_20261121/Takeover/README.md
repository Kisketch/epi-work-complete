# Antigravity 接续验收

`Overlay/` 的相对路径与既有 Lean 工程对应。`EpiFormal.lean` 和 `Audit.lean`
是核验时使用的完整入口。若已有更新的同名入口，将新增 import 和审计指令合并进去。
使用原项目的 Lean 4.35.0 和 Mathlib 版本构建，并运行：

```text
lake build EpiFormal
lake env lean Audit.lean
lake env lean TakeoverAudit.lean
```

`final-exits.txt` 记录本轮用现有依赖在隔离副本运行三个入口的退出码。
`final-TakeoverAudit.log` 给出本批声明的公理依赖。
`check_golden_valuations.py` 只需 Python 标准库。
`verify_golden_general_b.py` 使用 mpmath。第 7–10 和第 11–12 分母的
本轮运行日志按区间保存。B=13 及以上的谱闭式仍待完成。

PolyWeightedLower.lean verifies both general subcritical dimension equalities.

FiniteStateTail.lean verifies the labelled path covers and upper gauge bounds, marked component reduction, and the countability result at Perron root one.
