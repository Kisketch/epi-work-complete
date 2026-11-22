# F3d 合入记录：WindowSplitMass（2026-11-21）

## 一句总判断

`WindowSplitMass.lean`（1 定理：`uniform_split_mass_bound`）已合入主树，全量审计 **612 条（611+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`WindowSplitMass.uniform_split_mass_bound`：均匀分裂下，每原子质量 `m0 ≤ Mpar * 10000 / R^2`。
- 分支数输入真实化为已验证的 `WindowMobiusCount.coprime_count_ge`（`R ≥ 10^6 ⇒ R²/10000 ≤ copCount R`），不再是假设。
- 显式纸面接口（用方 discharge）：`hK`（互素对→互异子柱 realize 桥）、`hsplit`（等条件概率均分）。

## 调试留痕（3 处）

1. `div_le_div_iff` 已改名（未知标识符）→ `one_div_le_one_div_of_le` + `one_div_div` 重写（`1/K ≤ 10000/R²` 经 `1/(R²/10000)` 桥）。
2. `one_div_le_one_div_of_le` 参数顺序：先正性 `hpos` 后不等式 `hbase`（传反即 type mismatch）。
3. 清掉重写后失活的 `hKlt`/`hKpos`（`one_div_le_one_div_of_le` 不需 `0 < K`）。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print；单文件三轮验证（verify/verify2/verify3，终轮零 issue）；单目标构建 EXIT 0（9051 jobs）；全量审计 `audit_splitmass_wired_20261121.log` EXIT 0，612 条（规范计数器）。

## 下一步

F3e（阈值数值化）：以 stopped 层尺度 + 具体 R/H/s/C discharge `stopped_window_bound` 的 `hthresh`，得 windows 逐窗质量上界（L02 收尾）；再调 F1 主定理得 `1 ≤ μH[s]`。
