# Cylinder Phase D 合入记录（2026-11-21）

## 一句总判断

`CylinderDiameter.lean`（3 定理：`consec_cross`、`consec_cross_abs`、`childDen_ge_one`）已合入主树，全量审计 **578 条（575+3），`sorryAx = 0`**，3 条全仅依赖 Lean 基础三公理。

## 新定理清单

| 定理 | 内容 | 公理 |
|---|---|---|
| `Cylinder.consec_cross` | 连项交叉数恒等式（行列式 ±1 的直接实例化） | 基础三公理 |
| `Cylinder.consec_cross_abs` | 其绝对值形式（`m+1 ≡ 1`） | 基础三公理 |
| `Cylinder.childDen_ge_one` | 子柱分母 ≥ 1（`one_pow` 桥） | 基础三公理 |

## 接线（三处）

- `EpiFormal.lean`：+1 import（`CylinderDiameter`，紧随 `CylinderOrder`）。
- `Audit.lean`：+1 import + 3 `#print axioms`。
- 单目标 `lake build EpiFormal.CylinderDiameter` EXIT 0（9050 jobs）。
- 全量审计 `verification/audit_cylinder_diameter_wired_20261121.log` EXIT 0，578 条，error 行 0。

## 备注

- 文件尾补显式 `end Cylinder`（原靠 EOF 自动闭合，仅风格告警）；补后单文件重验 EXIT 0。
- Cylinder 系列累计：Base + Mediant(3) + Order(4) + Diameter(3)；下一步 Phase E（柱集直径上界 `1/(q*q')`，接 Frostman 模板）。
