# F3b 合入记录：WindowMuLevel（2026-11-21）

## 一句总判断

`WindowMuLevel.lean`（3 定理：`filter_meet_card`、`mu_le_at_level`、`mu_le_of_sandwich`）已合入主树，全量审计 **609 条（606+3），`sorryAx = 0`**，3 条全仅依赖 Lean 基础三公理。

## 定理

- `filter_meet_card`：交窗过滤子族的交数上界（E4a 引理的过滤实例化）。
- `mu_le_at_level`：固定层数据（原子对族 + 分离/长度/不交 + 全覆盖 + 逐原子质量 + 以 diam U 为参数的数值阈值）⇒ `μ U ≤ ofReal (C * diam U ^ s)`（F1 逐集上界形状）。
- `mu_le_of_sandwich`：三明治选层定 j，再调固定层上界（阈值以区间成员为接口，由具体数值在用方 discharge）。

## 设计注记

- 阈值方向：D 直接取 `diam U`（D ≤ h 会把上界放大，错误方向）；数值阈值 `((2*diam+3L)/d0+2)*m0 ≤ C*diam^s` 为显式接口。
- `hs`/`hC` 被阈值接口完全吸收，从签名删除（零 warning 纪律）。
- `mu_window_le` 的 `G.card ≤ N` 取 `N := card`（`le_rfl`），免去 ceil 取整。

## 调试留痕（8 处）

1. `P.filter (fun I => ...)` 的 binder 类型推不出（filter 先 elaborates 谓词）→ 显式 `(I : ℝ × ℝ)`。
2. `Finset.mem_biUnion hIG hxI` 非法（mem_biUnion 是 Iff）→ `Set.mem_biUnion` 构造子式 + `Finset.mem_coe` 桥（`⋃ i ∈ G` 是 Set 层 biUnion）。
3. sandwich 签名实为 `(H)(hlim)(j0)` → 传参顺序 `H hH j0`（`{h}` 隐参靠 `hdpos` 归一）。
4. `Metric.diam_nonneg` 的 `s` 不可见 → 裸用靠期望类型归一。
5. `Finset.filter_subset _ _ hiI` 非法（filter_subset 只取两参）→ `Finset.mem_of_subset` 桥。
6. e1 的 `← ofReal_mul + congr 1` 走偏 → `ofReal_mul + ofNat_natCast` 正向。
7. `open Classical in` 必须在 docstring 之前（否则 "expected lemma"）。
8. `Set.mem_biUnion` 实名确认（构造子式，非 Iff）。

## 接线 / 验证

- 两入口各 +1 import；Audit +3 prints；单文件 7 轮迭代后 EXIT 0 零 issue；单目标构建 EXIT 0（9050 jobs）；全量审计 `audit_mulevel_wired_20261121.log` EXIT 0。
- 验证日志：`window_mulevel_verify[_2.._7].log`（终轮零 issue；中间 `sorryAx` 均为错误级联产物，随错误消除）。

## 计数器规范（本次教训）

- 规范计数 = `^'.*(depends on axioms|does not depend on any axioms)` 行数。
- `proposition_H'` 行首双引号致严格正则漏计；4 条 `does not depend` 零公理定理须计入。
- 复核链：mu 602 → massdist 604 → mubound 605 → sandwich 606 → mulevel 609，逐轮吻合。

## 下一步

F3c（用方实例化）：以 stopped 柱族 + coprime 计数 + 具体 R/H/s 数值 discharge `mu_le_of_sandwich` 的 hcov/hbound/hthresh，得 windows 质量分布下界（L02/L05 收尾）。
