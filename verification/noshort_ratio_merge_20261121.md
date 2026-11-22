# no-short-dim phase 1 合并记录（2026-11-21）：Q/H 比值界 + γ>0

> 一句总判断：`NoShortDimRatio.lean`（8 定理：Q_ratio_lo/hi、Qsqrt_ge_one/two、H_ge_one、H_ratio_lo/hi、gamma_pos）单文件 EXIT 0、零 sorry，
> 接线后单目标构建 EXIT 0，全量审计 539 条（531+8，sorryAx=0），8 条全部仅依赖 Lean 基础三公理。

## 内容

- L01：`Q_{j+1}/Q_j ∈ [4j+2, 4j+3]`（j≥1），基于 `Classification.Qsel_rec'/Qsel_pos/Qsel_double` + 初值 `Qsel_zero/one/two`。
- H 比值：`3j ≤ H_{j+1}/H_j`（j≥1），`H_{j+1}/H_j ≤ 20j`（j≥3），其中 `H_j = ⌊Q_j√j⌋`；常数不求最优（与纸面 O(j) 同阶）。
- L05：`gamma_pos`（`η < 1/log φ → 0 < 1 - η·log φ`），`Real.log_pos Real.one_lt_goldenRatio`。

## 接线（三处清单）

- `EpiFormal.lean`：+1 import（NoShortDimRatio，30 模块）。
- `Audit.lean`：+1 import + 8 `#print axioms`。
- 单目标 `lake build EpiFormal.NoShortDimRatio` EXIT 0（9060 jobs）。
- 全量 `audit_noshort_ratio_wired_20261121.log` EXIT 0：539 条，sorryAx = 0。

## 过程坑（已解决）

- 三重括号强转 `(((Qsel j : ℤ)) : ℝ)` 大面积解析失败 → 统一双括号惯用法重写全文件。
- `Nat.lt_floor_add_one` 必须传完整乘积（曾误传单个因子）。
- `Nat.floor_le` 的非负前提必须显式给（positivity 看不穿 Int.cast）。
- `Nat.le_floor` 可替代错误的 `one_le_floor_iff` 用法。

## 下一步

- L06 新矩形计数（0.34–0.35 × 0.12–0.13）：复用 `intervalCount/countMultiples/moebius_indicator/moebius_partial/harmonic_le`，
  新 defs + 新组装 `NoShortDimCount.lean`（目标 `R²/100000`，余量推算约 3× @R=10⁶）。
- 阻塞仍在：L09/L10/L12 圆柱基础设施（continuant 恒等式、前缀无关性）。
