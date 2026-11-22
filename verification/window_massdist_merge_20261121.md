# F1 合入记录：WindowMassDist（2026-11-21）

## 一句总判断

`WindowMassDist.lean`（2 定理：`ofReal_diam_le_mul_ediam_rpow`、`mass_distrib_of_diam_bound`）已合入主树，全量审计 **604 条（602+2），`sorryAx = 0`**，2 条全仅依赖 Lean 基础三公理。

## 设计（直接质量分布引擎）

- 不经过 Hinter/公共 M：假设逐集上界 `μ V ≤ C·diam V^s`，结论 `1 ≤ μH[s] K`（另需 `ofReal C ≤ μ K`）。
- 证明链：subadditivity（OuterMeasure.measure_iUnion_le + toOuterMeasure_apply 桥）→ termwise（ofReal 桥 + tsum_mono + tsum_mul）→ 逐覆盖 `1 ≤ Σ'ediam^s`（inv_mul_cancel 消 C）→ guarded sup 逐点等式（`iSup_pos`-style：非空 `simp [h]+iSup_const`，空集 le_antisymm+iSup_le+ediam_empty+zero_rpow 链）→ le_iInf×3 + le_iSup₂ 收官。

## 调试留痕（10 处）

1. `ENNReal.ofReal_rpow` 不存在 → 实名 `ofReal_rpow_of_nonneg`（正向）。
2. `.le` 点记法非法（`hC.le`/`hs.le`）→ 一律 `le_of_lt`。
3. `Measure.iUnion_le` 不存在 → `MeasureTheory.measure_iUnion_le μ.toOuterMeasure` + `toOuterMeasure_apply` 桥。
4. C 进/出下确界无引理（反例：C=⊤ 时不成立）→ 改逐覆盖消 C 策略。
5. `ENNReal.tsum_le_tsum`、`ENNReal.tsum_mul_left`、`ENNReal.mul_inv_cancel`、`ENNReal.ofReal_pos/ne_top`、`iSup_const/of_empty`、`ediam_empty`、`bot_eq_zero`、`zero_rpow`（Real 版）实名确认。
6. `← mul_assoc` 疑似失效 → 改显式 `h3` 等式桥（`rw [mul_assoc]` 正向在 have 中正常）。
7. `iSup_const` 不取显式参数；`have` 不注册 TC 实例（`haveI` 带标注才行，但 linter 会报——最终两边都绕开）。
8. 空集分支：`subst` 要求局部变量（`t n` 非变量）→ `rw`。
9. `Set.not_mem_empty` 不存在 → `iSup_le + le_rfl`（目标本就是自反式）。
10. `ENNReal.zero_rpow` 不存在 → `ofReal_zero/rpow_of_nonneg/Real.zero_rpow` 组合桥。

## 接线 / 验证

- `EpiFormal.lean` / `Audit.lean` 各 +1 import；Audit +2 prints。
- 单文件 10+ 轮迭代后 EXIT 0 零 issue；单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_massdist_wired_20261121.log` EXIT 0，604 条。
- 验证日志：`window_massdist_verify*.log`（桥 + 主定理分文件留痕）。

## 下一步

F2 逐集上界实例化：`μ V ≤ C·diam V^s` 的 discharge（阶段选择 + 交数 + 质量 + 阈值组装，接口：hStage/hOverlapJ/hMassAtom/hThreshJ + staged atoms 数据）。
