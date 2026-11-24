# S 补充轨（wiring v1；依附主文，单独编译引用指向主文属预期）

* 内容：`sec:num.tex` 全节 + `sec:verification.tex` 全节（含 bibliography 与 `\end{document}`）；自写短摘要说明依附关系。
* 编译：0 error；未定义 39 个（全部为主文定理/节标签，`tab:`/`thm:`/`cor:`/`sec:` 全集，主文齐套即消解；引用零缺失）。

* 内容：`sec:num/sec:verification` + `audit_final_20261122.log`（937 行对账）+ `check_audit_reconcile.py` + 全部证书 `.py/.json/.log` + CMMS 一次文献 PDF。
* 双轨原则：正文数学自足，Lean 872→937 对应只在 S 并列。
* 本次新增留痕：原版双冻结 + 33 标签分类 + Lean 132 分组 + 65 条位置（Audit L1105–1169）+ 4 口径问题。
* **2026-11-23 同步更新**：随 `sec-num.tex`（新增 32 位 `verify_residue_multi_asymptotic.py` 数值佐证段）与 `sec-verification.tex`（新增 `AuditResidueCert.lean` 27 条、`AuditResidueMultiAsymptotic.lean` 24 条及 2026-11-23 Colab 独立复现记录）更新，已重新编译 `paperS_draft.tex` 刷新 `build/paperS_draft.log`（0 LaTeX 错误；主文定理/表格引用在独立编译 Supplement 时仍按预期指向主轨）。
