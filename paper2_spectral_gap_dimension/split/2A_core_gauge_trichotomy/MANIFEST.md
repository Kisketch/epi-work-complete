# 2A 抽取草案（未抽正文，只定范围）

* 范围：`sec:class/spectrum/finite-levels/weights/gauge` 前半，见 `split/README.md` 三、#1–15。
* 标签 15 个：`thm:class/gap/spectral/full-spectrum/sub/finite/upper/trichotomy/gauge` + `cor:exact-gauge/liminf-gauges/infinite-level` + `lem:factorial/branch`（`conj:weight` 计入 weights）。
* Lean 21 文件：GaugeNull/GaugeExact/GaugeCircle/GaugeLiminfComplete/Classification/SpectralGap/FullSpectrumDiscrete（声明级切：仅 2A 部分）/DimHCore/DimHFinite/WeightedDimHCore/WeightedFiber/WeightedUpper/WeightedLower/WeightedPhase/WeightedCantor/WeightedFinal/WeightedExactDim/QuarterPointCore/QuarterPointTail/QuarterPointFinal/UnweightedCorrection。
* 基座引用：Basic(stub)/Axioms/Measure/EulerConvergents/ThresholdAttained（不复制，双篇引用）。
* 下一步：按声明切出 `FullSpectrumDiscrete` 2A 部分与 `TrichotomyAndPolyExtension` L48–638。

## 投稿呈现版（2026-11-25）
* 入口 `paper2A_draft.tex` 改为接线 `*-2Apub.tex`，共 21 页（原 24 页）；tectonic 构建 0 未定义引用、0 未定义文献、0 Overfull。
* 正文切片 `sec-*-2Apub.tex` 由 `../derive_2A_pub.py` 从共享切片派生：
  - 只删 Lean 审计文字，包括定理标题里的 "Layer~A in Lean"、"(Lean: …)" 括注和 "Lean status" 段落，数学内容不变；
  - 脚本断言输出中不残留任何形式化词汇；
  - 共享切片与主稿不受影响。
* 摘要 `frontmatter-2Apub.tex` 与引言 `intro-2Apub.tex` 为重写版：
  - 引言结构为 Setup / 主要结果 / 方法 / 与已有工作关系 / 形式化验证（一段）/ 结构；
  - 写明 Moran 型覆盖技巧的来源（FWW、CMMS）；
  - 删去 $e+\pi$ 来历句。
* `refs-2Apub.tex` 只保留 2A 实际引用的 12 条。
* 数值注记一节（`sec-num-2A`）不进投稿版。旧切片原样保留，可回退。
* 待作者处理：`Phase1` 条目（"Lean 4 modules …"）是 Thm 1–2 的唯一出处，投稿前需换成可公开访问的引用（预印本或 DOI）；作者与单位仍为占位。
