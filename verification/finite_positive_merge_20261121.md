# finite-state-tail 正测度下界合并记录（2026-11-21）

> 一句总判断：`FiniteStatePositive.lean`（6 定理）单文件 EXIT 0、接线、单目标构建 EXIT 0、全量审计复跑 **499 条（493+6，`sorryAx = 0`）**，新增 6 条全部仅依赖 Lean 基础三公理；`lean_verify` 抽查 2/2 standard、无源码扫描警告。论文二 triage 的 finite-state-tail 下界项从"仍纸面"转为"组装已核实/实例化接口纸面"。

## 一、新文件与设计

- `epi_formal/EpiFormal/FiniteStatePositive.lean`（namespace `FiniteStateGauge`，~400 行）。
- 复用已核实件：`walkMass_of_eigenvector`、`walkCount_bounds`（Perron 有限词恒等式）、`card_path_eq_walkMass`（计数桥）、`Measure.le_mkMetric` + `mkMetric_apply`（mathlib Frostman 比较 + 通用 gauge 测度定义；mathlib 的 Hausdorff API 只有幂 gauge，故结论取缩放 gauge 的正性，header 已诚实注记）。
- 验证（无条件）：`perron_word_mass_sum`（柱质量望远镜求和）、`perron_word_mass_bound`（C0 接口常数一致性）、`muRestricted_elem_le`（覆盖代价上界）、`muRestrict_le_mkMetric_hlam`（Frostman 比较）、`one_le_mkMetric_scaled`（`1 ≤` 缩放 gauge 测度）、`pos_mkMetric_scaled`（正性）。
- 显式纸面接口（定理前提，非公理）：`Hcyl`（柱质量界，paper L1767/1790-1792）、`Hmeet`（小集至多交 3 柱 + 尺度比较，paper L1786-1793）、`hμfull : μ S = 1`（pushforward 满质量，paper L1783-1784）、`hSmeas`（Borel，paper L1800）、`(1-p)^m` 块避让/a.e.穿越（paper L1769-1774）、Haar 局部无穷矛盾（paper L1809-1820）、多分支组装（paper L1822-1847）。

## 二、复验波折（留痕）

1. `endVertex` 未引用绑定 `u`（linter 警告）→ 改匿名。
2. 零情况 `Fintype.card (Path edges 0 v)` 不自动归一 → `Equiv.refl _` + `Fintype.card_congr` + `Fintype.card_unique`。
3. 柱求和的 `Finset.univ.card` 需 `Finset.card_univ` + `Fintype.card_coe` 两步桥接（`rfl` 直断失败）。
4. `h2` 引理名试错 3 轮（`div_mul_cancel₀` 行为不符预期 → `one_div_mul_cancel` 未命中 → 落定 `one_div` + `inv_pow` + `inv_mul_cancel₀`，全部为确定性引理）。
5. `field_simp` 把 `heq` 化简过头（剩逆元恒等式 ring 证不出）→ 改用 h2 显式改写 + ring。
6. `Measure.restrict_apply_self` 需显式传 μ（`Measure.restrict_apply_self μ S`）。
7. 接线遗漏：Audit.lean 缺 `import EpiFormal.FiniteStatePositive`（6 条 Unknown constant，EXIT=1）→ 补 import 重跑 EXIT=0。教训：每次合并的接线清单 = EpiFormal.lean import + Audit.lean import + Audit.lean prints，三项缺一即审计失败。

## 三、审计与核验证据

- 单文件：`verification/finite_positive_verify4_20261121.log`（EXIT 0，6/6 三公理，零警告；中间迭代日志 verify1–3 留存）。
- 单目标构建：`lake build EpiFormal.FiniteStatePositive` EXIT 0（9080 jobs）。
- 全量审计：`verification/audit_finite_positive_wired_20261121.log` EXIT 0，**499 条 = 493 + 6**，`sorryAx = 0`，error 行 0；新增 6 条在审计上下文中同为三公理。
- `lean_verify`：`perron_word_mass_sum` + `pos_mkMetric_scaled`，trust 均为 standard，warnings 均为空（rg 注入持续有效）。

## 四、诚实口径更新

- finite-state-tail 下界：组装已核实；μ 构造/a.e./Haar/分支组装仍为纸面接口（与 short-ae 的 hStep/hBchar 同类）；不声称"定理已完全形式化"。
- 白名单总数：审计显示白名单相关 23 条（间距排版变体计入），项目自加仍 0。
- 队列推进：finite-state-tail（论文二 triage #2）→ windows 下界（#3，有 WeightedExactDim 下界先例）→ no-short-dim → residues Bowen 组装。
