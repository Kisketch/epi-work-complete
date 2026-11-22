# F3c 合入记录：WindowMuScale（2026-11-21）

## 一句总判断

`WindowMuScale.lean`（2 定理：`stopped_thresh_of_scale`、`stopped_window_bound`）已合入主树，全量审计 **611 条（609+2），`sorryAx = 0`**，2 条全仅依赖 Lean 基础三公理。

## 定理

- `stopped_thresh_of_scale`：diam 双侧夹（`dmin ≤ diam U ≤ dmax`）⇒ 逐窗阈值归约为纯数值条件 `((2*dmax+3L)/d0+2)*m0 ≤ C*dmin^s`（用方以具体 R/H/s 数值 discharge）。
- `stopped_window_bound`：归约 + `mu_le_at_level` 组装，得 F1 逐集上界形状的 stopped 层逐窗上界。

## 调试留痕（3 处）

1. `apply add_le_add_right` 统一失败（OfNat/HAdd 怪癖）→ 改 linarith 原子化（除法项当原子）+ `mul_le_mul_of_nonneg_right` 显式项模式。
2. `add_le_add_right`/`div_le_div_of_nonneg_right` 实名确认（后者在 GroupWithZero/Basic.lean:1193，签名 `(hab)(hc)` 正常——问题仅在 apply 链）。
3. 未用假设 `hL` → 改名 `_hL`（调用方位置传参不受影响；`stopped_window_bound` 自身 `hL` 仍传给 `mu_le_at_level`）。

## 接线 / 验证

- 两入口各 +1 import；Audit +2 prints；单文件三轮验证（verify/verify2/verify3，终轮零 issue）；单目标构建 EXIT 0（9051 jobs）；全量审计 `audit_muscale_wired_20261121.log` EXIT 0。
- `Metric.diam_nonneg` 可裸用（F3b 已验证）。

## 全链对账（ canonical 计数器：`^'.*(depends|does not depend)` 行数）

E4c 596 → overlap 599 → E5 mu 602 → F1 massdist 604 → F2 mubound 605 → F3a sandwich 606 → F3b mulevel 609 → F3c muscale 611。Audit.lean 现有 611 条 `#print` = 日志 611 唯一条目，`sorryAx = 0`，error 0。

## 下一步

F3d（用方实例化）：以 stopped 柱族 + coprime 计数（N）+ 具体 R/H/s 数值 discharge `stopped_window_bound` 的 hcov/hbound/hnum，得 windows 质量分布下界（L02/L05 收尾）；再调 F1 主定理得 `1 ≤ μH[s]`。
