# L02a 合入记录：WindowLargeThresh（2026-11-21）

## 一句总判断

`WindowLargeThresh.lean`（1 定理：`large_window_thresh`）已合入主树，全量审计 **616 条（615+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`WindowLargeThresh.large_window_thresh`：`dmin ≤ D ≤ 1` 的窗，以显式常数 `C = ((2+3L)/d0+2)*m0/dmin^s` discharge F3e 数值阈值 `((2D+3L)/d0+2)*m0 ≤ C*D^s`。
- `diam < dmin` 的小窗区阈值对固定 C 不成立（D→0 时 LHS→正数、RHS→0），需原子内质量级联细分——接口留用方，已在 doc 注明。
- 新增接口假设 `0 ≤ L`（长度非负；调试发现 linarith 需它，调用方 discharge）。

## 调试留痕（5 处）

1. doc 块压住 import（"invalid 'import' command"）→ import 置顶。
2. `add_le_add_right` apply 统一失败（F3c 同款怪癖）→ 显式 `add_le_add_left hdiv 2`（2 在右）。
3. `positivity` 证不出 `0 < dmin^s` / `0 ≤ C`（C 是自由变量）→ `Real.rpow_pos_of_pos hdmin s` + 显式 `hCnn` 链。
4. `mul_le_mul_of_nonneg_left` 显式调用须先给 le 后给非负（apply 无所谓、exact 有所谓）。
5. `linarith [hhi, hDnn]` 证不出 `(2+3L)/d0+2 ≥ 0`（L 自由）→ 补 `hL` 接口假设。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print；单文件 5 轮验证（终轮 EXIT 0 零 issue）；单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_largethresh_wired_20261121.log` EXIT 0，616 条。

## 下一步

L02b：用 F3e（`mu_window_thresh_num`）+ 大窗阈值组装 stopped 层逐窗上界（`dmin ≤ diam ≤ 1` 区）；小窗区级联细分留接口。
