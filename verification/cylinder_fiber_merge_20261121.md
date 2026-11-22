# E4b 合入记录：CylinderFiber（2026-11-21）

## 一句总判断

`CylinderFiber.lean`（5 定理：`children`、`mem_children_iff`、`card_children`、`fiber_card_eq`、`child_prefix_self`）已合入主树，全量审计 **594 条（589+5），`sorryAx = 0`**，5 条全仅依赖 Lean 基础三公理。

## 设计

子柱纤维集（Hinter discharge 的"同层细化数一致"组合输入）：
- `children w K = (Icc 1 K).image (fun k => w ++ [k])`。
- `card_children`：基数恒 `K`（与父词无关）。
- `fiber_card_eq`：同层两父柱子柱数相等。
- `child_prefix_self`：子柱以前缀词为前缀（嵌套性）。

## 调试留痕（4 处）

1. `Finset.card_Icc` 不存在 → `Nat.card_Icc`（`b+1-a`），再 `Nat.add_sub_cancel`。
2. `child_prefix_self` 中 `j` 先用后绑定 → iff 参数改隐式占位 `_`。
3. `rw [Finset.mem_image]` 后两边仅差 beta，被 rw 自带 rfl 直接闭合 → 改 `exact Finset.mem_image`（"No goals" 反向信号：tactic 太多而非太少）。
4. `end Cylinder` 补在文件尾（本轮 `end` hygiene 延续）。

## 接线（三处）

- `EpiFormal.lean` / `Audit.lean` 各 +1 import；Audit +5 prints。
- 单目标构建 EXIT 0（9052 jobs）；全量审计 `audit_cylinder_fiber_wired_20261121.log` EXIT 0，594 条。

## 审计口径核对（本轮发现）

- 本次 594 = 前序 overlapdiam 审计 589 + 5（前序日志复查：589 条、零 `: error:`），与 `Audit.lean` 内 594 行 `#print` 逐一对上（按模块前缀普查：Cylinder 30 = base 8 + mediant 3 + order 4 + diameter 3 + phaseE 7 + fiber 5；WindowMobiusCount 32、CoverCount 4 等均吻合）。
- **检查方法修正**：此前审计用的 `^error` 锚定漏检 Lean 的 `path:line:col: error:` 格式，今后审计 error 统计一律用 `: error` 模式（本次及前序日志已用正确模式复查，均为 0）。

## 下一步

Hinter 实例化：`meet_card_of_diam_le`（计数侧）＋柱径上界（几何侧）＋纤维计数（本文件）→ discharge `frostman_of_count_thresh`，得 windows 质量分布下界（L02/L05 收尾）。
