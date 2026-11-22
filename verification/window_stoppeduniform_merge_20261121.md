# StoppedUniform 合入记录：WindowStoppedUniform（2026-11-21）

## 一句总判断

`WindowStoppedUniform.stopped_uniform_bound`（分裂均分 + 乘积展开合成）已合入主树，全量审计 **640 条（639+1），`sorryAx = 0`**，仅依赖 Lean 基础三公理。

## 定理

`stopped_uniform_bound`：`StoppedTree.mass_le_of_split`（`μ ≤ m j`）+ `WindowMassProd.mass_le_prod`（`m j ≤ m j0/∏B`）经 `ENNReal.ofReal_le_ofReal` 桥接 ⇒ `μ I ≤ ofReal (m j0 / ∏_{i∈Ico j0 j} B i)`。

## 调试留痕（3 处）

1. **模块名≠命名空间**：`import EpiFormal.StoppedTree` 报 file not found——模块名由文件名决定，实为 `EpiFormal.WindowStoppedTree`（命名空间才叫 `StoppedTree`）。教训：新文件 import 先 grep 接线实例。
2. `ENNReal.ofReal_le_ofReal.mpr` 不存在（它本身就是蕴含式）→ 去掉 `.mpr`。
3. olean 缺失恐慌是误报：`StoppedTree.olean` 从不存在，存在的是 `WindowStoppedTree.olean`（104 个 olean 完好）。

## 接线 / 验证

- 两入口各 +1 import；Audit +1 print；单文件 3 轮验证（终轮 EXIT 0 零 issue）；单目标构建 EXIT 0（9049 jobs）；全量审计 `audit_stoppeduniform_wired_20261121.log` EXIT 0，640 条。

## 状态

- 当前基线 640 条；L05 直接组装的前置件已齐（选层 F3a + 交数 meet_card + 质量 stopped_uniform_bound + 阈值 logthresh）。
