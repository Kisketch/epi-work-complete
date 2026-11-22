# Cylinder Phase C 合入记录（2026-11-21）

## 总判断

`CylinderOrder.lean`（4 定理：矩阵元非负 `cfProd_nonneg`、行列式非零 `cfProd_det_ne_zero`、子分母正性 `childDen_pos`、兄弟端点相异 `sibling_strict`）已合入主树，全量审计 **575 条（571+4），`sorryAx = 0`**，4 条全部仅依赖 Lean 基础三公理。不交性的最后整数输入就位。

## 逐项对照表

| 结果 | 类别 | 核查状态 | 依据 |
|---|---|---|---|
| `Cylinder.cfProd_nonneg` | 无条件新引理 | 已核实 | `cylinder_order_20261121.log`，基础三公理（Fin-2 归纳+逐元非负） |
| `Cylinder.cfProd_det_ne_zero` | 无条件新引理 | 已核实 | 同上（`cfProd_det` + `pow_ne_zero`） |
| `Cylinder.childDen_pos` | 无条件新引理 | 已核实 | 同上（`k*A10+A11>0`，det≠0 反证消零情形） |
| `Cylinder.sibling_strict` | 无条件新引理 | 已核实 | 同上（`sibling_cross` + `mul_ne_zero`，交叉相乘形式，无除法） |
| 全量审计 | 文献核查与复现 | 575 条，sorryAx=0，error=0 | `audit_cylinder_order_wired_20261121.log` |

## 修复记录（5 处）

1. `rw [one_apply_ne]` 后 `norm_num` 冗余（rw 自带 rfl  closed `0 ≤ 0`）→ 删。
2. `fin_cases` 后 `simp [cfMat, Int.natCast_nonneg]` 参数多余（simp 集自带）→ 删参数。
3. `simp only [cfMat]` 未化简 `!![...]` 字面索引 → 改全集 `simp [cfMat]`。
4. `push_neg` 弃用 → `push Not at h`。
5. 非线性原子 `↑k * x` 在 `x=0` 下 linarith 不认 → 先 `rw [hx_eq, mul_zero]` 得显式零等式再 linarith。
6. `sibling_strict` 中 `rw [hcross] at hne` 方向反（hne 右端是 RHS）→ `rw [← hcross]`。

## 接线

- `EpiFormal.lean` +1 import（`CylinderOrder`）；`Audit.lean` +1 import + 4 `#print`。
- 单目标构建 EXIT 0（9049 jobs）。

## 仍纸面（Phase D 预告）

连续子端点交叉差绝对值（`=1`）＋分母 `≥1` → 直径上界的整数核心；Frostman 质量分布组装待 Phase E（`WeightedExactDim` 模板移植）。
