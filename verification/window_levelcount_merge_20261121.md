# LevelCount 合入记录：WindowLevelCount（2026-11-21）

## 一句总判断

`WindowLevelCount.lean`（1 定理：`level_count_ge`）已合入主树，全量审计 **618 条（617+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`WindowLevelCount.level_count_ge`：多层分支计数——每父至少 `B i` 个互不交子 ⇒ 第 J 层保留总数 `≥ ∏_{i∈Ico j0 J} B i`。
证明：`Nat.le_induction`；归纳步经 `biUnion_subset`（子并 ⊆ 下层）+ `card_biUnion`（不交并基数）+ `sum_le_sum`（逐父分支下界）+ `prod_Ico_succ_top` 闭合。

## 调试留痕（5 处）

1. `Finset.mul_sum` 方向反了（目标不是 `*∑` 形）→ 改 `sum_const + nsmul_eq_mul` 证 `card*B = ∑B` 再 `sum_le_sum`。
2. `prod_Ico_succ_top` 需显式传 `f`（`(hab)(f)` 双参）→ `Finset.prod_Ico_succ_top (by omega : j0 ≤ J) B`。
3. `nsmul_eq_mul` 引入 `↑card` 强转残留 → 补 `Nat.cast_id`。
4. 初版误写裸 `end`（无 section）→ 删；保留 `end WindowLevelCount`。
5. `rwa ... at *` 弃用告警 → 改显式 `hexpand` 等式 + `rw` + `exact`。

## 接线事故（重要教训）

- 追加 print 用 PowerShell `Set-Content -Encoding utf8` 重写全文件**带入 BOM**（`EF BB BF`），致审计 `1:0 expected token` + EXIT=1。
- 修复：`[IO.File]::WriteAllText(path, text, UTF8NoBOM)`；字节级确认 `imp` 开头后重跑 EXIT 0。
- **教训升级**：凡用脚本改 .lean（含 Audit.lean），一律无 BOM 写回 + 字节级验头。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print（文件 618 prints = 日志 618 条目，双向 diff 为空，无重复）。
- 单文件验证 EXIT 0（终轮零 error/warning/sorry）；单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_levelcount_wired_20261121.log` EXIT 0，618 条。

## 下一步

对数渐近比较：`Σ log i` 积分比较 + `H_j` 增长（`log H_j = j log j + O(j)` e-侧接口）+ Stirling/阶乘界，为阈值 discharge 准备显式常数。
