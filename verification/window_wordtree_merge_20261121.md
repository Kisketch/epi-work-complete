# P2a 合入记录：WindowWordTree（2026-11-21）

## 一句总判断

`WindowWordTree.lean`（7 定理：`mem_childrenOf`、`append_single_injective`、`childrenOf_card`、`children_mem_next`、`children_disjoint`、`nil_mem_levelWords_zero`、`uniform_level_count`）已合入主树，全量审计 **631 条（624+7），`sorryAx = 0`**，6 条基础三公理 + `append_single_injective` 仅 `[propext]`。

## 设计

纯词树组合子（无停止规则、无 `H_j`，为 P2 柱树备料）：
- `childrenOf D w`（单字母延长）+ `levelWords D j`（长 j 词全体，递归构造）。
- `uniform_level_count`：`D.card ^ J ≤ #(levelWords D J)`，为 `WindowLevelCount.level_count_ge` 的均匀分支实例化。

## 调试留痕（5 处）

1. `{[[]]}` 单例歧义（`Singleton (List (List ?))`）→ `{([] : List ℕ)}` 显式标注。
2. `simp [childrenOf]` 后等式方向反 → 加 `eq_comm`。
3. `congrArg` 产物带 beta-redex，`rw`/`simpa using` 钥匙匹配失败 → 改 `List.append_inj hab (rfl : length = length)` 正向路线（`h.right : [a] = [b]` 经 `simpa` 得 `a = b`）。
4. `rw [levelWords]` 非法（def 无 eq 引理名）→ 删 rw，`exact` 靠 defeq 展开。
5. `rw` 已自动闭环后多余 `exact`（"No goals" 反向信号）→ 删。

## 接线 / 验证

- 两入口各 +1 import；Audit +7 prints；单文件三轮验证（终轮 EXIT 0 零 issue）；单目标构建 EXIT 0（9048 jobs）；全量审计 `audit_wordtree_wired_20261121.log` EXIT 0，631 条（文件 prints = 日志条目，双向对账）。
- 残留 `exact h.2` 行清理（接线前已删）。

## 状态

- 当前基线 631 条；P2b（stopped 前缀嵌套 + 每层分支下界，论文 L2621–2633）待启动；阈值蓝图子代理进行中。
