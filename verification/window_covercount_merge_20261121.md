# E3 合入记录：WindowCoverCount（2026-11-21）

## 一句总判断

`WindowCoverCount.lean`（3 定理：`left_separated`、`floor_lt_of_separated`、`meet_card_le`）已合入主树，全量审计 **588 条（585+3），`sorryAx = 0`**，3 条全仅依赖 Lean 基础三公理。

## 设计

不交区间族覆盖计数引理（Frostman `Hinter` discharge 的组合 heart）：
- `left_separated`：不交内部 + 非平凡 ⇒ 区间分居两侧。
- `floor_lt_of_separated`：`d0`-分离实数的缩放 floor 严格有序。
- `meet_card_le`：长 ≥`d0`、长 ≤`L`、交窗口 `[Vl,Vr]`（需 `Vl ≤ Vr`、`0 ≤ L`，否则空窗大间隔下命题为假——已证伪并加假设）的有限族，基数 ≤ `(Vr-Vl+L)/d0 + 2`。证明：左端点 `⌊·/d0⌋` 单射 + 整数区间基数。

## 调试留痕

1. `InjOn` 只有 5 个前件（`I ≠ J` 须 `by_contra` 自证）。
2. 左右分支曾写反（`left_separated` 的 `I.2 ≤ J.1` 给左界）。
3. omega 原子对齐：`heq` 须先转 floor 形式（`set` 的 defeq 用 `have heq' := heq` 桥）。
4. `gcongr` 已闭合处删多余 `linarith`（"No goals" 反向信号）。
5. `Finset.card_image_of_injOn`（Card.lean:239）+ `Int.card_Icc`（Data/Int/Interval.lean:96）实名确认；`Int.floor_le_floor` 不存在，改用 `Int.le_floor`/`Int.floor_le`/`Int.lt_floor_add_one`（Defs.lean:300/307、Ring.lean:127）。
6. 结尾 calc 桥（`Int.cast_natCast` + `toNat_of_nonneg`）；文件末换行符补上（空白 lint）。

## 接线（三处）

- `EpiFormal.lean` / `Audit.lean` 各 +1 import；Audit +3 prints。
- 单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_covercount_wired_20261121.log` EXIT 0，588 条。
- 单文件三轮验证日志：`window_covercount_verify[_2|_3]_20261121.log`（终轮零 error 零 warning）。

## 下一步

Hinter 实例化：`meet_card_le`（计数侧）+ 柱径上界（几何侧）→ discharge `frostman_of_count_thresh`，得 windows 质量分布下界（L02/L05 收尾）。
