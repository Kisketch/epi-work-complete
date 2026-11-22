# F3f 合入记录：WindowRealize（2026-11-21）

## 一句总判断

`WindowRealize.lean`（1 定理：`stopped_window_realize`）已合入主树，全量审计 **614 条（613+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`WindowRealize.stopped_window_realize`：stopped 层用方实例化——把 F3e 的 `hlen_lo/hi` 归约为停止规则接口 `hden`（每原子分母对在 `[4H/3,5H/2]` 且长度 `= 1/(q₀*q₁)`），经 `CoverCount.child_len_bounds` 真实 discharge；`K := P.card`，其余接口（realize 单射 `hK`、均分 `hsplit`、覆盖 `hcov`、逐原子质量 `hbound`、数值阈值 `hnum`）原样传递给 F3e。

## 调试留痕（2 处）

1. 新文件漏写 import 头（`MeasureTheory.Measure` 未知 + `OfNat ℝ` 合成失败共 68 issue）→ 照抄 F3e 的三行 import（WindowMuThresh/WindowOverlap/WindowMobiusCount）。
2. `/-` 锚定不唯一（文件内两处）→ 用首行 doc 标题扩展 oldString。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print；单文件两轮验证（首轮 import 缺失失败留痕 → 终轮 EXIT 0 零 issue）；单目标构建 EXIT 0（9063 jobs）；全量审计 `audit_realize_wired_20261121.log` EXIT 0，614 条。
- 被调用全名：`CoverCount.child_len_bounds`（WindowOverlap.lean，命名空间 CoverCount）、`WindowMuThreshLevel.mu_window_thresh_num`。

## 下一步

F3g（最终实例化）：以 stopped 柱族 + realize 单射 + 均匀分裂 + 具体 R/H/s/C 数值 discharge 剩余接口，得 windows 逐窗质量上界（L02 收尾）；再调 F1 主定理得 `1 ≤ μH[s]` → L05。
