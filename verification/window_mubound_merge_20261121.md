# F2 合入记录：WindowMuBound（2026-11-21）

## 一句总判断

`WindowMuBound.lean`（1 定理：`mu_le_of_overlap_thresh`）已合入主树，全量审计 **605 条（604+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`WindowMuBound.mu_le_of_overlap_thresh`：交窗原子数 ≤ N、每原子质量 ≤ m0、数值阈值 `N*m0 ≤ C·diam^s` ⇒ `μ U ≤ ofReal (C * diam U ^ s)`（F1 主定理所需的逐集上界形状）。
证明：`mu_window_le`（μU ≤ N·m0）+ `ofReal_natCast/ofReal_mul` 桥（`(N:ℝ≥0∞)*ofReal m0 = ofReal (N*m0)`）+ `ofReal_le_ofReal`。

## 调试留痕（2 处）

1. `μ` 是 section 变量（`variable {μ}`），调用 `mu_window_le` 时不传（传了会把 μ 错位成 A）。
2. `ℝ≥0∞` 记号需 `open scoped ENNReal`（缺则 "expected token" 级联）。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print；单目标构建 EXIT 0（9048 jobs）；全量审计 `audit_mubound_wired_20261121.log` EXIT 0。
- 单文件三轮验证日志：`window_mubound_verify[_2|_3].log`（终轮零 issue）。

## 对账注记

- 链条：602（E5）→ 604（F1，+2）→ 605（F2，+1），逐轮吻合。
- `proposition_H'` 在日志行首引号致朴素 split 解析错位（误读为 proposition_H），非真实缺失；今后条目统计用 `: error`/`sorryAx` 锚定 + 全名 grep，不用 split。
