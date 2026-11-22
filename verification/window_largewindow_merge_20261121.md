# L02b 合入记录：WindowLargeWindow（2026-11-21）

## 一句总判断

`WindowLargeWindow.lean`（1 定理：`mu_large_window`）已合入主树，全量审计 **617 条（616+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`WindowLargeWindow.mu_large_window`：`dmin ≤ diam U ≤ 1` 的窗，以 L02a 显式常数 discharge F3e 数值阈值，得 F1 逐集上界形状（F3e `mu_window_thresh_num` + L02a `large_window_thresh` 组装）。

## 调试留痕（3 处）

1. 传参顺序照抄 F3e 签名（`K hK hsplit U hbddU hcov hbound hnum`）——首轮即对。
2. F3e 的 `hnum` 要的是分裂质量界代入后的版本（`(Mpar*10000/R²)` 而非 `m0`）→ 传 L02a 的 m0 版结论直接报 type mismatch。
3. 方向教训：m0 版推不出 split 版（split 更大，单调性方向反了）→ 改以 `m0 := Mpar*10000/R²` 直接实例化 L02a（m0 全称量词），`hsplit_nn` 经 `div_nonneg (mul_nonneg hMpar norm_num) positivity` 自给；F3d import 随之删掉（不再需要）。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print；单文件 4 轮验证（verify2 方向错 → verify4 EXIT 0 零 issue）；单目标构建 EXIT 0（9058 jobs）；全量审计 `audit_largewindow_wired_20261121.log` EXIT 0，617 条。
- `#print axioms WindowLargeWindow.mu_large_window` → `[propext, Classical.choice, Quot.sound]`。

## 状态

- L02 收尾：大窗区（`diam ≥ dmin`）逐窗上界已形式化；小窗区（`diam < dmin`）级联细分仍为接口。
- 当前基线 617 条；队列：no-short-dim 组装（L02 已齐 → L05 `1 ≤ μH[s]`）→ residues。
