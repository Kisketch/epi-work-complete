# F3e 合入记录：WindowMuThresh（2026-11-21）

## 一句总判断

`WindowMuThresh.lean`（1 定理：`mu_window_thresh_num`）已合入主树，全量审计 **613 条（612+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`WindowMuThreshLevel.mu_window_thresh_num`：分裂质量界（`uniform_split_mass_bound`，分支数经 `coprime_count_ge` 真实化）+ 固定层上界（`mu_le_at_level`）⇒ stopped 层逐窗质量上界（F1 逐集上界形状）。
接口：`hK`（realize 桥）、`hsplit`（均分）、`hnum`（以具体 R/H/s 数值 discharge 的阈值）、原子族几何/覆盖/逐原子质量。

## 调试留痕（3 处）

1. `μ` 是 `WindowMuLevel` 的 section 变量（`variable {μ : MeasureTheory.Measure ℝ}`），本文件须重声明（否则 "Function expected"）。
2. `Metric.diam_nonneg` 无显式参数（`0 ≤ diam s`，s 隐式）→ 裸用，靠期望类型归一（传参即错）。
3. 接线教训：以旧 import 行为 oldString 做"追加"会删掉旧行——本次误删 `WindowSplitMass` import 两处，好在 grep 复核发现并补回；今后追加一律用"旧行+新行"双行 oldString 锚定。

## 接线 / 验证

- 两入口各 +1 import（已复核 SplitMass 行完好）；Audit +1 print。
- 单文件四轮验证（verify/verify2/verify3，终轮零 issue）；单目标构建 EXIT 0（9056 jobs）；全量审计 `audit_muthresh_wired_20261121.log` EXIT 0，613 条。
- 公理：`[propext, Classical.choice, Quot.sound]`。

## 下一步

F3f（用方实例化）：以 stopped 柱族 + 具体 R/H/s/C 数值 discharge `mu_window_thresh_num` 的 hK/hsplit/hnum/hcov/hbound，得 windows 逐窗质量上界（L02 收尾）；再调 F1 主定理得 `1 ≤ μH[s]`。
