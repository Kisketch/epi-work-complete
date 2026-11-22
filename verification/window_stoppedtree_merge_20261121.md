# StoppedTree 合入记录：WindowStoppedTree（2026-11-21）

## 一句总判断

`WindowStoppedTree.lean`（3 定理：`Ioo_subset_of_Icc_subset`、`nodup_of_children_disjoint`、`mass_le_of_split`）已合入主树，全量审计 **623 条，`sorryAx = 0`**，3 条全仅依赖 Lean 基础三公理（`mass_le_of_split` 含 `Classical.choice`，来自 `Nat.le_induction` 无需 classical 段？实测输出为基础三公理，照录）。

## 定理

- `Ioo_subset_of_Icc_subset`：闭区间包含 ⇒ 开区间包含（端点序传递）。
- `nodup_of_children_disjoint`：不交性沿树向下传播（同父用子不交、异父经父不交 + `Disjoint.mono` 传递；归纳用 `Nat.le_induction`）。
- `mass_le_of_split`：均分分裂下逐层一致质量上界 `μ(atom_j) ≤ m_j`（`m_{j+1} = m_j/B_j` 递归；无需跨父一致性）。

## 调试留痕（6 处）

1. `Set.Pairwise` 匿名 binder 无类型 → 逐个显式标注 `(I J : ℝ × ℝ)`（元组 binder 须拆写，不可 `(A B : T)` 合写）。
2. `ENNReal.div_le_div_right` 实签名为 `(h : a ≤ b) (c)`（假设在前）→ `ENNReal.div_le_div_right hPle _`。
3. `ENNReal.ofReal_div_of_pos {x y} (hy : 0 < y)` → 目标侧用 `.symm`。
4. 结尾多余 `rfl`（calc 已闭环）→ 删。
5. `Set.Pairwise` 用严格隐式 ⦃⦄ → `ih` 按证明项传参，不可按位传。
6. 双 binder `(A B : T)` 非法语法 → 拆写。

## 计数器正本清源（重要）

- 规范计数 = `^'.*(depends on axioms|does not depend on any axioms)` 行数；零公理条目必须计入。
- 旧 split/`^error` 锚定系统性漏计：零公理条目（本次 4 条：`AffineWindow.r_period`、`Cylinder.convPair_cons/convDen_cons/convNum_cons`）+ `proposition_H'` 行首双引号。
- 本次 airtight 对账：文件 623 `#print` = 日志 623 条目（含 4 零公理），双向 diff 为空（前次 diff 的 8 行差异经逐项复核全部为正则伪影）。
- 历史链条绝对数（613/616/617…）因旧计数器漏计而系统性偏小，以本次 623 为准重新锚定；各步 +N 增量当时均经构建 EXIT + 抽查验证有效。

## 接线 / 验证

- 两入口各 +1 import；Audit +3 prints；单文件 5 轮验证（终轮 EXIT 0 零 issue）；单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_stoppedtree_wired_20261121.log` EXIT 0。
- 验证日志：`window_tree_verify[1-5]_20261121.log`（逐轮留痕）。
