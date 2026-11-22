# Cylinder Phase E1 合入记录（2026-11-21）

## 一句总判断

`CylinderPhaseE.lean`（3 定理：`frac_abs_sub_of_unit_cross`、`diam_Icc_min_max`、`child_cyl_diam`）已合入主树，全量审计 **581 条（578+3），`sorryAx = 0`**，3 条全仅依赖 Lean 基础三公理。

## 新定理清单

| 定理 | 内容 | 公理 |
|---|---|---|
| `Cylinder.frac_abs_sub_of_unit_cross` | 单位交叉行列式分数差绝对值 = 1/(q·q')（纯分数引理，假设用 `a*d - c*b` 序以逐字匹配 `consec_cross`） | 基础三公理 |
| `Cylinder.diam_Icc_min_max` | 无序两点闭区间直径 = \|x - y\|（min/max 两 case） | 基础三公理 |
| `Cylinder.child_cyl_diam` | 词级柱集直径：连续子柱区间直径 = 1/(q·q')（经 `consec_cross` + `cfProd_det` + `childDen_pos` discharging，`neg_one_pow_eq_or` 分支） | 基础三公理 |

## 辅助定义

- `cylFrac M = (M 0 0 : ℝ) / (M 1 0 : ℝ)`、`cylDen M = (M 1 0 : ℝ)`（`noncomputable`，证毕后补 `end Cylinder` + 文件末换行，单文件重验零告警）。

## 接线（三处）

- `EpiFormal.lean`：+1 import（`CylinderPhaseE`）。
- `Audit.lean`：+1 import + 3 `#print axioms`。
- 单目标 `lake build EpiFormal.CylinderPhaseE` EXIT 0（9051 jobs）。
- 全量审计 `verification/audit_cylinder_phaseE_wired_20261121.log` EXIT 0，581 条，error 行 0。

## 关键坑（已解决，留痕）

1. `div_sub_div` 分子是 `a*d - c*b` 序——初版引理假设写成 `a*d - b*c` 致全链失配；改用 `field_simp`（单步闭环，删多余 `ring`）+ 假设改 `a*d - c*b` 序，与 `consec_cross` 逐字同序。
2. `max_sub_min_eq_abs` 在 mathlib 不存在——改 min/max 两 case + `← abs_sub_comm` 转向。
3. `neg_one_pow_eq_or` 显式传 `ℤ`（`neg_one_pow_eq_or ℤ w.length`），非 `(R := ℤ)`。
4. 陈述括号灾难——改 `cylFrac/cylDen` 缩写，`simp only` 展开后 `exact` 直连。
5. `exact_mod_cast` 在跨 `ℤ`/`ℝ` 分支证明中不可靠——改 `e : ↑(a*d-c*b) = ↑a*↑d-↑c*↑b`（`norm_cast`）+ `rw [← e, h, ...]` 确定性桥。

## 下一步

Phase E2：Frostman 质量分布骨架（按 `verification/frostman_recipe_20261121.md` S0–S9，交叠常数 2→17 五处同步）。
