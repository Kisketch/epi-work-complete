# PointMass 合入记录：WindowPointMass（2026-11-21/22）

## 一句总判断

`WindowPointMass.mu_singleton_zero`（嵌套原子覆盖下单点集测度为零）已合入主树，全量审计 **646 条（645+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

在分裂树（`StoppedTree`）+ 质量递推（`mass_le_prod`）上：若每层原子覆盖点 `x` 且分支 `B ≥ 2`、质量非负，则 `μ {x} = 0`。
证明链：`measure_mono`（单点集⊆原子）→ `mass_le_of_split`（逐层质量界）→ `mass_le_prod`（乘积展开）→ `∏ ≥ 2^{j-j0}`（`prod_le_prod₀`）→ `ge_of_tendsto` squeeze。

## 调试留痕（7 处）

1. `prod_le_prod` 新版只要一个显参 → 改 `Finset.prod_le_prod₀`（P2b 已验证用法）。
2. `rw [div_eq_mul_inv]` 会同时改写等式两侧不同实例 → 改用 `div_eq_mul_one_div _` 精确项。
3. `← inv_pow` 模式失配（`1/2` 是 HDiv 不是 `⁻¹`）→ `div_pow + one_pow + one_div + ← div_eq_mul_inv`。
4. `Filter.Eventually.of_forall`（首字母大写 E）。
5. `simpa` 需同时处理 `Function.comp_def` + `ENevntual_of_forall`。
6. `ge_of_tendsto` 取 eventually 假设（`Filter.Eventually.of_forall` 包裹）。
7. `zero_le` 无显式参数（`le_antisymm hle0 zero_le`）。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print；单文件 6 轮验证（终轮 EXIT 0 零 issue，mu_singleton_zero 仅基础三公理）；单目标构建 EXIT 0（9051 jobs）；全量审计 `audit_pointmass_wired_20261121.log` EXIT 0。
- Airtight 对账：文件 prints 646 = 日志条目 646（双向唯一）；基线链 645（FrostDirect）+1 = 646。

## 状态

- 当前基线 **646 条**；L05 三件套最后一块（FrostDirect 骨架已有 + L02 逐窗上界 + hpt 已备）就绪。
