# Overlap 合入记录：WindowOverlap（2026-11-21）

## 一句总判断

`WindowOverlap.lean`（3 定理：`child_len_bounds`、`stopped_cyl_len_bounds`、`window_overlap_le`）已合入主树，全量审计 **599 条（596+3），`sorryAx = 0`**，3 条全仅依赖 Lean 基础三公理。

## 定理

- `child_len_bounds`：分母∈[4H/3,5H/2] ⇒ `4/(25H²) ≤ 1/(q₀q₁) ≤ 9/(16H²)`（纯代数；对应论文 L2545–2547 的柱长界下半部分，`4/25` 强于论文的 `2/25` 常数，因对象为连子柱直径而非 `u(u+v)` 形式——已在 doc 注明）。
- `stopped_cyl_len_bounds`：实例化到 `child_cyl_diam`。
- `window_overlap_le`：宽 `h ≤ 1/H²` 的窗至多交 `753/64 < 12` 个柱（论文：`≤15+2=17`；常数不影响 `O(h^s)`）。

## 调试留痕（3 处）

1. calc 方向证反：`one_div_le_one_div_of_le` 的 `1/b ≤ 1/a` 要求 `a ≤ b`，上下界两处 calc 起点须与统一后的 `?a/?b` 一致（报错即指引）。
2. `exact child_len_bounds ...` 传参顺序：目标先出现 `[k+1]` 分母，故 `[k+1]` 假设在前（`hlo' hhi' hlo hhi`）。
3. `have h` 遮蔽实数 `h`（Prop vs ℝ，同名导致 `x-h` 处类型错配）→ 改名 `hcard`；教训：短名 `h` 禁止复用。

## 接线（三处）

- `EpiFormal.lean` / `Audit.lean` 各 +1 import；Audit +3 prints。
- 单目标构建 EXIT 0（9053 jobs）；全量审计 `audit_overlap_wired_20261121.log` EXIT 0，599 条。
- 单文件三轮验证日志：`window_overlap_verify[_2|_3].log`（终轮零 issue）。

## 下一步

μ 接口 + `O(h^s)` implication（Frostman 实例化最后一块）：以 `window_overlap_le`（交数）+ `child_len_bounds`（柱径）discharge `frostman_of_count_thresh` 的 `Hinter`，得 windows 质量分布下界。
