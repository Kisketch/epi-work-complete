# E4c 合入记录：WindowHinter（2026-11-21）

## 一句总判断

`WindowHinter.lean`（2 定理：`thresh_bridge`、`fiber_count_ge`）已合入主树，全量审计 **596 条（594+2），`sorryAx = 0`**，2 条全仅依赖 Lean 基础三公理。

## 定理

- `HinterBridge.thresh_bridge`（S7 阈值桥）：一致交数界 + `C/M ≤ t^s` + 直径下界 ⇒ 逐点 `Kc/M ≤ diam^s`（`gcongr` + `Real.rpow_le_rpow`）。
- `HinterBridge.fiber_count_ge`（S6 双计数）：`choose` 取交集选择函数 + 前缀纤维划分 + `card_biUnion` + 单调性 + `sum_le_sum_of_subset_of_nonneg`，得 `card A ≤ Σ Kc`。

## 调试留痕（7 处）

1. `F.image f` 实为对 F 取像 → 改 `A.image f`（6 处）。
2. `choose` 产生依赖型函数 → 空/非空分情况 + `i0` 兜底 + 非依赖 `hex`。
3. `div_le_div_right` 不存在 → `gcongr`。
4. `Finset.sum_natCast` 不存在 → `Nat.cast_sum`。
5. `rw [ha.2]` 目标无 `f a` → `ha.2 ▸ hfmeet`。
6. `Finset.sum_le_sum_of_subset` 已改名 → `sum_le_sum_of_subset_of_nonneg`（实名经 mathlib 源码确认）。
7. hai/haj 同向（均为 `f a = _`）→ `e1.symm.trans e2`；`disjoint_filter` 后加 `have e1/e2` 定向桥。
8. PowerShell `Out-File` 拼接写回带 BOM（EF BB BF）→ `1:0 expected token` 级联 → 字节级去 BOM（`imp` 开头）；教训：**凡用脚本改 .lean，必须无 BOM 写回**。
9. `Finset.disjoint_filter` 后 simp 集去冗余（coe_sort_coe 未用）；hcard 长行拆分（longLine lint）。

## 接线（三处）

- `EpiFormal.lean` / `Audit.lean` 各 +1 import；Audit +2 prints。
- 单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_hinter_wired_20261121.log` EXIT 0，596 条。
- 单文件验证日志：verify5/6/7（失败留痕）→ verify8（EXIT 0 零 issue）。

## 对账

594（E4b 收官）+ 2 = 596；新命名空间小计：WindowMobiusCount 32 + Cylinder 30 + CoverCount 4 + HinterBridge 2 = 68。
