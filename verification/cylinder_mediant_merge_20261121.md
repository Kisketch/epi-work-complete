# Cylinder Phase B 合入记录（2026-11-21）

## 总判断

`CylinderMediant.lean`（3 定理：拼接桥 `cfProd_append_single`、列-收敛子桥 `col1_convPair`、兄弟交叉差 `sibling_cross`）已合入主树，全量审计 **571 条（568+3），`sorryAx = 0`**，3 条全部仅依赖 Lean 基础三公理。mediant 分离核心就位。

## 逐项对照表

| 结果 | 类别 | 核查状态 | 依据 |
|---|---|---|---|
| `Cylinder.cfProd_append_single` | 无条件新引理 | 已核实 | `cylinder_mediant_20261121.log` L1，基础三公理 |
| `Cylinder.col1_convPair` | 无条件新引理 | 已核实 | 同上 L2（第二列 = convPair，归纳+显式 Fin-2 矩阵 simp） |
| `Cylinder.sibling_cross` | 无条件新引理 | 已核实 | 同上 L3（`(P₁Q₂−P₂Q₁) = (k₁−k₂)·det`，entries 展开 + ring） |
| 全量审计 | 文献核查与复现 | 571 条，sorryAx=0，error=0 | `audit_cylinder_mediant_wired_20261121.log` |

## 修复记录

- 初版 3 处 `No goals to be solved`（`simp [cfMat]` 已闭环，属 `ring` 冗余）+ nil 分支 simp 参数多余警告；删冗余后复验 3 行干净输出（零 warning）。
- 关键洞察：`convPair w` = `cfProd w` 的**第二列**（`[]` 时 `(0,1)` 对上；`[a]` 时 `(1,0)` 为 `cfMat a` 第二列），非第一列——归纳方向据此确定。

## 接线

- `EpiFormal.lean` +1 import（`CylinderMediant`，接 `Cylinder` 后）；`Audit.lean` +1 import + 3 `#print`。
- 单目标 `lake build EpiFormal.CylinderMediant` EXIT 0（9048 jobs）。

## 仍纸面（Phase C 预告）

端点正性（`Q k > 0`，需 det≠0 反证）＋兄弟端点相异（`sibling_strict`，交叉差≠0）→ 不交性；单调方向与父区间包含待 Phase C/D。
