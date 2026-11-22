# P2c 合入记录：WindowDescFiber（2026-11-21）

## 一句总判断

`WindowDescFiber.lean`（2 定理：`desc_mem`、`desc_card_le`）已合入主树，全量审计 **639 条（637+2），`sorryAx = 0`**，2 条全仅依赖 Lean 基础三公理。

## 定理

- `WindowDescFiber.desc_mem`：凡 level-j 原子皆有祖先链（归属存在性）。
- `WindowDescFiber.desc_card_le`：该 level-j 原子的后代总数 ≤ `∏_{Ico j N} B i`（乘积分支界，`level_count_ge` 实例化）。

## 验证历程（9 轮，教训已记）

- PowerShell 写 .lean 带 BOM 致 `1:0`——shell 永不直接写 .lean（write 工具 + IO 去 BOM + 字节验头）。
- `intro u hu t ht` 顺序即 revert 顺序；term-mode `exact` 打 `prod_Ico_succ_top` 显式 f。
- `mul_le_mul_of_nonneg_right` 替代已改名引理；终态 2/2 基础公理。

## 接线 / 验证

- 两入口各 +1 import；Audit +2 prints；单文件 EXIT 0 零 issue；单目标构建 EXIT 0（9048 jobs）；全量审计 `audit_descfiber_wired_20261121.log` EXIT 0，639 条（文件 prints = 日志条目，双向对账）。

## 状态

- 当前基线 639 条；P2 剩余：stopped 规则实例化（hchild/hmem/hbranch 的用方 discharge，论文 L2444–2465 矩形计数 + L2514–2528 有界增量）。
