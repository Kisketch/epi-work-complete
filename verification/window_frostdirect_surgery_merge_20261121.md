# E2 手术合入记录：WindowFrostmanDirect Hinter 正性前提（2026-11-21）

## 一句总判断

E2 主定理 `frostman_of_window_layer` 的 Hinter 接口增加正性前提并在 S3 处供给证明，单文件验证 EXIT 0（终轮零 issue）、单目标构建 EXIT 0、全量审计 **646 条（文件 prints = 日志条目，双向全唯一），`sorryAx = 0`**。审计条目数不变（E2 本体无 `#print` 行，未增删）。

## 改动（4 处，均在 `epi_formal/EpiFormal/WindowFrostmanDirect.lean`）

1. `import EpiFormal.WindowThickening`（新增第 2 行）。
2. Hinter 签名 += `(hpos : ∀ i, (V i).Nonempty → 0 < Metric.diam (V i))`（discharge 方原本无法处理空集/零直径集）。
3. S3 后新增 `hV_bd`（加厚集有界，经 `isBounded_thickening_of_ediam` + S1 的 `hdiam ≤ r0`）与 `hV_pos`（直径为正，经 `diam_thickening_pos` + 子类型非空性）。
4. Hinter 调用处传入 `(fun i _ => hV_pos i)`。

## 动因（R3 补记，见 frostman_redesign_20261121.md）

- discharge 方（我方）只能处理"空集（Kc=0）/正直径（选层+阈值）"两类；原 Hinter 对任意族（包括无界集、diam-junk-0 集）要求阈值，不可满足（`V = univ` 反例）。
- S3 族（开加厚 + 非空下标）天然满足正性前提，故收紧 Hinter 不损失 E2 证明的适用性。

## 顺手清理（2 处预存风格告警）

- `direct_ediam_thickening_le` 未用假设 `hρ` → `_hρ`。
- `push_neg at hlt` → `push Not at hlt`（弃用）。

## 验证

- 单文件验证两轮（终轮 EXIT 0 零 issue）；单目标构建 EXIT 0；全量审计 `audit_frostdirect_surgery_wired_20261121.log` EXIT 0，646 条。
- 空集/零直径覆盖的 discharge 由 L05 承担（`Kc = 0` + `0 ≤ 0^s`）；正直径集由 F3a 选层 + 交数 + 阈值承担（下一步）。

## 计数器说明

- 本轮"645→646"之谜已解：差集唯一项为 `WindowPointMass.mu_singleton_zero`（前序接线后审计日志被覆盖，链条数字漂移）。当前以 airtight 双向对账为准，不再沿用历史基线数。
