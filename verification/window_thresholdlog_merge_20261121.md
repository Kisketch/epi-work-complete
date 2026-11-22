# L05b 合入记录：WindowThresholdLog（2026-11-21）

## 一句总判断

`WindowThresholdLog.lean`（1 定理：`threshold_of_log_growth`）已合入主树，全量审计 **621 条（620+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`threshold_of_log_growth`：`log A ≥ Ls - t` ⇒ `A * C0 ≥ K0 + C`（线性化阈值引理）。
- 输入 `hb : B * tB ≥ m * R + (Ls + C1)`（对数下界编过码）与 `hbl : (R:B) * (B tB : ℝ) ≤ Real.log (A:B)`（桥下界）。
- 结论 `A.real * C0 ≥ K0 + (C:B)`，其中 `hA1 : 1 ≤ (A:B)`、`hC0 : 0 < C0`。
- 证明：`tsub` 双边展开 + `NormedField` 桥 + nlinarith 五链。

## 调试留痕（4 处）

1. 重叠导出引理签名须变实例形：通用 `(B:R) * (B tB:R) ≤ Real.log (A:B)`，真实实例 `M*N ≥ ΠB`+`ΠB = exp(Σlog)` 待用方；e-side 接口注记在案。
2. `Nat.exists_eq_add_of_le` 不存在（says unknown package）→ 显式 `have ⟨k, hk⟩ := Nat.le.dest`。
3. `Real.exp_lt_exp.mpr` 方向 + `Real.log_exp` 回跳 orelse 闭环。
4. `Real.add_rpow_le_rpow` 不存在 → 拆 `ge_of_eq`/`mul_le_mul_of_nonneg_left`（或用已验证 T1 `rpow_add_le_add_rpow`）。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print；单文件三轮验证（终轮 EXIT 0 零 issue）；单目标构建 EXIT 0（9049 jobs）；全量审计 `audit_thresholdlog_wired_20261121.log` EXIT 0，621 条。

## 下一步

L05c（最终组装）：用 `threshold_of_log_growth` + `coprime_count_ge` + 对数比较 discharge F3e `hnum` ⇒ 逐窗上界；再调 F1 主定理得 `1 ≤ μH[s]`（L05 收官）。
