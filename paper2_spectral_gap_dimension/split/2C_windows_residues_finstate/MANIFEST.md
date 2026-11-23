# 2C 抽取草案（未抽正文，只定范围）

* 范围：`sec:finite-state-tail` + `sec:windows-residues` 全（2814–3702），见 `split/README.md` 三、#16/26–33。
* 标签 9 个：`thm:finite-state-tail/windows/short-ae/no-short-dim/residues/residues-general/residues-asymptotic` + `tab:residues-general/residues-asymptotic`。
* Lean 61 文件：Window×44（含 WindowAndResidueCore，外部基座引用）+ Cylinder×7 + NoShortDimRatio/NoShortDimCount + FiniteStateTail/FiniteStateGauge/FiniteStatePositive/FiniteStateComplete + HermiteResiduePeriod + ResidueModGeneral + ResidueAsymptotic + TransferOperatorDim。
* 外部基座引用不复制：`DirichletDivisor/DenominatorCertificate`（论文一 §3 接口，2C 依赖）。
* 证书：`residue_certificate.py`、`residue_certificate_general.py`、50 位 `C_r` 表与 `verify_paper2_extensions.py`（120 位 mpmath 全 PASS，`m≤6` 负超额比与 `~3.20000` 笔误已留痕）。
* 下一步：`WindowAndResidueCore` 保持单份，2C 以 import 引用；`FiniteStateTail` 以全名 `FiniteStateGauge.*` 引用。
