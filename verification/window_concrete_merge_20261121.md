# F3g 合入记录：WindowConcreteThresh（2026-11-21）

## 一句总判断

`WindowConcreteThresh.lean`（1 定理：`stopped_window_unit`）已合入主树，全量审计 **615 条（614+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`WindowConcrete.stopped_window_unit`：具体数值（R=10⁶、H=100、s=1、Mpar=1、C=1/500、d0=4/(25·100²)、L=9/(16·100²)、diam U=1）下，数值阈值 `hnum` 由 `norm_num` 实算 discharge（LHS≈0.00125 ≤ RHS=0.002），其余用方几何接口（realize 单射 hK、均分 hsplit、覆盖 hcov、逐原子质量 hbound）原样传递。

## 调试留痕（2 处）

1. 全名 grep 确认 F3f 接口后照抄隐式参数顺序（hd0/hL/hm0/hMpar/hd0eq/hLeq 全显式传，`rfl` 定 d0/L）。
2. 未用变量告警（d0/L 只在 rfl 中出现）→ 改 `_d0`/`_L` 下划线前缀（位置传参不受影响）。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print；单文件两轮验证（首轮 2 warning → 终轮零 issue）；单目标构建 EXIT 0（9064 jobs）；全量审计 `audit_concrete_wired_20261121.log` EXIT 0，615 条。

## 全链对账

E4c 596 → overlap 599 → E5 mu 602 → F1 604 → F2 605 → F3a 606 → F3b 609 → F3c 611 → F3d 612 → F3e 613 → F3f 614 → F3g 615。

## 下一步

L05 收尾：以 F3g 实例 + F1 主定理（`mass_distrib_of_diam_bound`）组装 `1 ≤ μH[s]`；L02（逐窗上界 general-s）需把 s=1 推广——阈值对 s 的单调性/显式 C(s) 是用方数值工作。
