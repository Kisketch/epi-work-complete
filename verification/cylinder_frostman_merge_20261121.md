# Cylinder Phase E2 合入记录（2026-11-21）

## 一句总判断

`CylinderFrostman.lean`（4 定理：`rpow_add_le_add_rpow`、`ediam_thickening_le`、`frostman_of_count_thresh`、`frostman_dimH_le`）已合入主树，全量审计 **585 条（581+4），`sorryAx = 0`**，4 条全仅依赖 Lean 基础三公理。

## 设计

- 通用 Frostman 核心（S1–S3、S8–S9 照抄模板骨架）＋存在式计数/阈值接口 `Hinter`（S6/S7 由应用方 discharge）。
- `Hinter`：`∀ (ι : Type) (V : ι → Set ℝ) (F : Finset ι)`，开覆盖＋有限子覆盖 → `∃ Kc M`，`0 < M ∧ 1 ≤ Σ Kc/M ∧ Kc/M ≤ (diam V)^s`。
- 推论 `frostman_dimH_le`：`ofReal s ≤ dimH K`（T13 模式：`set d`＋`le_dimH_of_hausdorffMeasure_ne_zero`＋`ofReal_coe_nnreal` 桥）。

## 调试留痕（7 处）

1. `set_option ... in` 必须在 doc 之前；裸 `set_option` 不是命令（最小复现 ScratchOpt.lean 已删）。
2. 主定理超时 → `set_option maxHeartbeats 800000 in` 前置。
3. `universe u` 致 `⋃` 宇宙 `u+1` 失配 → 单态化 `Type`。
4. `end Cylinder` 在匿名 section 下报错 → 裸 `end` + `end Cylinder`。
5. `le_dimH_*`/`dimH`/`μH` 为 root 名（新 module 系统），照抄模板 bare 用法；`open scoped` 加 `MeasureTheory` 取 `μH` 记号。
6. `hbridge` 的 `rw [← ofReal_coe_nnreal]` 后需 `congr 1`（rw 的 auto-rfl 只用 reducible transparency）。
7. `Real.rpow_le_rpow_of_exponent_ge` 等签名以模板用例为准，不另查文档。

## 接线（三处）

- `EpiFormal.lean`：+1 import（`CylinderFrostman`）。
- `Audit.lean`：+1 import + 4 `#print axioms`。
- 单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_cylinder_frostman_wired_20261121.log` EXIT 0，585 条。

## 下一步

windows 实例化：用 `coprime_count_ge`（R²/10000）＋重叠界 discharge `Hinter`，得 windows 质量分布下界（L02/L05 收尾）。
