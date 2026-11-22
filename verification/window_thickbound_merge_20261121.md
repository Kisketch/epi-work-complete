# L05c 合入记录：WindowThickBound（2026-11-21）

## 一句总判断

`WindowThickBound.mu_thickened_le`（逐窗选层上界）已合入主树，全量审计 **624 条，`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`mu_thickened_le`：三明治选层（F3a）+ 固定层交数/质量/阈值（F3b `mu_le_at_level`）⇒ `μ U ≤ C·diam^s`（要求 `0 < diam U`；diam=0 情形留终文件）。
接口：per-level 几何（d0/L/triv/len/disj）+ 阈值 hthresh（sandwich 区间参数化）+ 覆盖 hcov + 质量 hbound；mass 由调用方经 `mass_le_of_split` 提供（本文件不重复取 splitting 假设）。

## 调试留痕（2 处）

1. 无用假设清理：初版带 `hB1/hm0/hmrec/hsplit/hmem`（`hbound` 已是直接接口）→ 整文件重写删 5 行（edit 锚定遇不可见字符差异，改走全量重写）。
2. `open Classical in` 未用则不必加（本文件无 classical 需求，终版未加，零告警证实）。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print；单文件 EXIT 0 零 issue；单目标构建 EXIT 0（9052 jobs）；全量审计 `audit_thickbound_wired_20261121.log` EXIT 0。

## 对账（airtight 方法）

- 文件 `#print axioms` 行数 = 624；日志 `^'...'` 条目 = 624 且全唯一；双向名字匹配唯一差异为 `proposition_H'` 引号正则伪影（同一条目），实质零差异。
- 历史链条修正：618 基线过期——其后 StoppedTree（+3）与 LogFact（+2）各有独立合入审计；624 = 618+3+2+1 吻合。今后以 airtight 双向匹配为准，不再沿用携带基线。

## 状态

- L05c 完成；L05d（终文件：点质量 + per-set wrapper + S1–S4+S8–S9 + dimH 推论）为最后一步，设计已定稿（见 frostman_redesign + L05c 讨论）。
