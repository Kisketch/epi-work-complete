# P2b 合入记录：WindowMassProd（2026-11-21）

## 一句总判断

`WindowMassProd.lean`（3 定理：`mass_le_prod`、`prod_Ico_self_eq_fact_div`、`mass_le_fact_bound`）已合入主树，全量审计 **634 条（631+3），`sorryAx = 0`**，3 条全仅依赖 Lean 基础三公理。

## 定理

- `mass_le_prod`：分裂递推 `m(j+1) = m j / B j` 展开为乘积上界 `m j ≤ m j0 / ∏_{Ico j0 j} B`（`Nat.le_induction` + `div_le_div_of_nonneg_right` + `div_div` + `prod_Ico_succ_top`）。
- `prod_Ico_self_eq_fact_div`：`∏_{Ico j0 j} i = (j-1)!/(j0-1)!`（`1 ≤ j0`；`Nat.le_induction` + `field_simp` + `push_cast` + `ring`）。
- `mass_le_fact_bound`：分支下界 `B_i ≥ c·i^b` ⇒ `m j ≤ m j0 / (c^{j-j0} · R^b)`，`R = (j-1)!/(j0-1)!`（`prod_le_prod₀` + `prod_mul_distrib` + `prod_const` + `Nat.card_Ico` + `prod_pow` + 阶乘比）。

## 调试留痕（7 处）

1. `div_le_div_right` 已改名 → `div_le_div_of_nonneg_right (hab) (hc)`（GroupWithZero/Basic.lean:1193）。
2. calc 中括号把 `∏` body 吞错（`∏ i ∈ s, B i * B j` 被解析为逐项积）→ 显式括号 `(∏ …) * B j`。
3. `m.succ` 与 `m+1` 字面不统一致 rw 失配 → 全改 `∃ m, j = m + 1` 匿名构造（`⟨j-1, by omega⟩`）。
4. `congr 1` 已闭合后多余 `omega`（"No goals"）→ 删。
5. `Finset.card_Ico` 不存在 → `Nat.card_Ico`（`b - a` 形式正好）。
6. `Finset.prod_le_prod` 需 `MulLeftMono` → 改 `prod_le_prod₀`（GroupWithZero 版，`0 ≤` 前件）。
7. `← prod_pow` 方向反（目标已是分布形）→ 正向 `Finset.prod_pow`（Defs.lean:635）。
8. `field_simp` 后 cast 被推反（`↑(m*m!+m!)` 成原子）→ 加 `push_cast` 再 `ring`。

## 接线 / 验证

- 两入口各 +1 import；Audit +3 prints；单文件多轮迭代后 EXIT 0 零 issue；单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_massprod_wired_20261121.log` EXIT 0，634 条（文件 prints = 日志条目，airtight 双向对账）。
- 接线复核：WordTree 实为 1 import + 7 prints（尾部只见 4 行系正常截断，`grep` 全文件确认 8 命中含 import）。

## 状态

- 当前基线 634 条；下一步：对数比较文件（`Σ log` 积分比较 + `log H_j` 渐近 + 阈值 discharge，蓝图 S3–S5）。
