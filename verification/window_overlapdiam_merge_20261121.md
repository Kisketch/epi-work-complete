# E4a 合入记录：meet_card_of_diam_le（2026-11-21）

## 一句总判断

`CoverCount.meet_card_of_diam_le`（直径版交数界，Hinter discharge 的计数 heart）已合入主树，全量审计 **589 条（588+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`meet_card_of_diam_le`：`(d0,L)`-分离不交原子族中，与有界集 `V`（`diam V ≤ D`，`0 ≤ D`，`IsBounded V`）相交的原子数 ≤ `(2D+3L)/d0 + 2`。
证明：空族直接非负；否则取见证点 `x0 ∈ V`，`dist_le_diam_of_mem` 把相交原子锁进窗口 `[x0-D-L, x0+D+L]`，调用 `meet_card_le`，窗口宽 `2D+2L` 经 `ring` 化为 `(2D+3L)/d0+2`。

## 设计注记

- `diam` 为 `toReal ∘ ediam`，有限直径不蕴含无界集的反例（无界集直径为 0），故 `IsBounded V` 必须显式假设；调用方（Hinter 实例化）从覆盖集的 ediam 有界性 discharge，不循环。
- `Real.dist_eq` + `abs_le.mp` 做距离↔序桥；`Finset.eq_empty_or_nonempty` 分空非空。

## 接线

- 源文件内 +1 定理 +1 print；`EpiFormal.lean` import 已有；`Audit.lean` +1 print。
- 单文件验证 EXIT 0（零 error/warning/sorry）；单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_covercount_diam_wired_20261121.log` EXIT 0，589 条。

## 下一步

E4b：柱词一致纤维计数（`card_prefix_fiber` 的柱集版：同前缀词的细化数相等/有界，为 `Hcount` 的 `Σ Kc ≥ M` 提供组合输入）。
