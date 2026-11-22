# F3a 合入记录：WindowSandwich（2026-11-21）

## 一句总判断

`WindowSandwich.lean`（1 定理：`sandwich_of_tendsto`）已合入主树，全量审计 **606 条（605+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`sandwich_of_tendsto`：正尺度列 `H`（`1/H² → 0`）下，每个 `0 < h ≤ 1/H(j0)²` 被夹在连续两逆平方尺度之间（`∃ j ≥ j0`）。
证明：`eventually_atTop` 取一致 N → `Nat.find` 取最小超标层 m → 回退 m-1（`Nat.find_min` + `Nat.find_spec`；j=j0 用假设，j>j0 用极小性）。

## 设计注记

- 镜像模板 S5（`hex_lvl`）但**无需单调性**：least-element 论证自足；`hpos`（H>0）证明中根本用不到，已删（接口更干净）。
- e-specific 尺度事实（`H→∞`、log 比较）全部留用方接口。

## 调试留痕（5 处）

1. `Set.Iio_mem_nhds` 不存在 → `mem_nhds_iff + isOpen_Iio` 组合。
2. `HasSubset.Subset.rfl` 非法 → 显式 `fun x hx => hx`。
3. `hev.exists` 给单点非单调 → `Filter.eventually_atTop.mp` 取一致 N。
4. `push Not` 把 `¬(a<b)` 归一为 `b≤a` → 结论侧直接 `exact`（删 `le_of_not_gt`）。
5. `Iio_mem_nhds` WithZero 专用版（`LinearOrderedCommGroupWithZero`）不适用于 ℝ → 弃用。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print；单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_sandwich_wired_20261121.log` EXIT 0，606 条。
- 单文件 5 轮验证日志：`window_sandwich_verify[_2|_3|_4|_5].log`（终轮零 issue）。

## 下一步

F3b（组合）：三明治 + 交数（meet_card）+ 质量组合（mu_biUnion_le）+ 阈值接口 ⇒ 逐窗上界（F1 逐集上界形状），e-specific 几何/计数留接口。
