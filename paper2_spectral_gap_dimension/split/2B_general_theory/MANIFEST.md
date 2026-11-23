# 2B 抽取草案（未抽正文，只定范围）

* 范围：`sec:poly-rec` + `sec:growing-rec`（1969–2813），见 `split/README.md` 三、#17–25。
* 标签 9 个：`lem:poly-growth/poly-lattice` + `thm:general-rec/poly-gauge-trichotomy/poly-phase-transition/growing-rec-spectrum/growing-rec-dim-phase` + `cor:poly-exact-gauge/growing-rec-three-regimes`。
* Lean 6 文件：PolyWeightedLower/PolyWeightedUpper/PolyGaugeAndPhaseTransition/TrichotomyAndPolyExtension（声明级切：后半归 2B）/GeneralGrowingRec/GeneralGrowingDim。
* 对 2A 依赖：`GeneralGrowingDim → WeightedExactDim`，`GeneralGrowingRec → GaugeCircle`，拆后 2B 前言声明引用 2A 基座，不复制。
* 下一步：`TrichotomyAndPolyExtension` 按 L48–638 / 之后切分；`FullSpectrumDiscrete` 中一般 `(cj+d)` 推广段归 2B 附录引用。
