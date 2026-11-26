# 01_main_paper/ — 论文一正式稿

- **`paper1_e_plus_pi.tex` / `.pdf`**：论文一正文（75 页）。唯一权威源是 `.tex`，PDF 由它两遍 `pdflatex` 生成。
- **`paper1_e_plus_pi.log`、`paper1_build_tectonic_*.log`**：编译日志。
- **`patch_*.py`**：对正文做确定性修补的脚本（文献完整性、一致性、分母界），留作可复现记录。
- **`assemble_restructure.ps1`**：重组正文结构的脚本。

论文最后的目标 P1 在 §`sec:lean-reduction`，等价于 1、e、π 在 ℚ 上线性无关，**仍是公开问题**。上级索引见 [../00_PROJECT_INDEX.md](../00_PROJECT_INDEX.md)。
