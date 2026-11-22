# LogThresh 合入记录：WindowLogThresh（2026-11-21）

## 一句总判断

`WindowLogThresh.lean`（2 定理：`log_inv_le_two_log`、`frostman_ratio_bound`）已合入主树，全量审计 **636 条（634+2），`sorryAx = 0`**，2 条全仅依赖 Lean 基础三公理。

## 定理

- `log_inv_le_two_log`（蓝图 S3）：`H^{-2} ≤ h` ⇒ `log h⁻¹ ≤ 2 log H`（`one_div_le_one_div_of_le` + `log_le_log` + `log_pow`）。
- `frostman_ratio_bound`（蓝图 S5 核心）：重叠质量 + exp 形质量 + 对数比较 ⇒ `μU ≤ K0·M0·exp(-(b-2s)·jlogj + E1 + E2)·h^s`；`s < b/2` 的作用显式化为残余指数系数（`E2 ≥ 0` 为用方接口）。

## 调试留痕（4 处）

1. `mul_le_mul_of_nonneg_left` 产物结合律与目标不一致（`K0*M0*(E*h^s)` vs `(K0*M0*E)*h^s`）→ e1 用 `← mul_assoc` 预归一，e3 用显式 `mul_assoc (K0*M0)` 定点重写。
2. `hs`/`hE2` 未被证明引用（E2 在 linarith 中消去，hs 只作接口语义）→ 改 `_hs`/`_hE2` 下划线保留签名（零 warning 纪律）。
3. `Real.rpow_def_of_pos` + `← Real.exp_add` + `Real.exp_le_exp.mpr` 桥接 `h^s` 与 exp 形式。
4. `one_div_le_one_div_of_le`（E3 已验证）复用。

## 接线 / 验证

- 两入口各 +1 import；Audit +2 prints；单文件 3 轮验证（终轮 EXIT 0 零 issue）；单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_logthresh_wired_20261121.log` EXIT 0，636 条（文件 prints = 日志条目，airtight）。

## 状态

- 当前基线 636 条；下一步：用方实例化（`H_j` 增长接口 discharge + 阈值链闭合 → L02/L05）。
