# AI 贡献记录（草稿，待作者确认）

> **状态**：草稿，2026-11-21 由研究助理按工作区实际记录整理。**署名、贡献比例、最终表述须由人类作者逐项确认**后方可用于投稿；各期刊披露口径见 `journal_policy_notes.md`。本文件不代替作者的人工核验责任。

## 1. 参与的 AI 系统与时间范围

| 系统 | 时间 | 承担工作 | 留痕 |
|---|---|---|---|
| 云端研究模型（九轮自主研究） | 2026-11 上旬 | 定理 A–E、命题 G/H′、障碍地图、四条桥梁排除、Meiburg 精读与补完、审计台账 | `progress_and_path_analysis.md` 第二部分 |
| 本机 Lean 形式化代理 | 2026-11 中旬 | M0–M5 里程碑、Flint Hills 桥、Audit.lean 审计链、`lake build` 9053/9090 jobs | `epi_formal/`、`verification/*.log` |
| 本机核查与整理代理 | 2026-11-20/21 | 450 位区间证书复跑、整数证书、目录英文化重组（守恒校验）、Takeover 合并、`lean_verify` 抽查 | `verification/` 各记录、本文件 |
| arxiv / paper-search / lean-lsp MCP 工具 | 2026-11-21 | 文献检索与书目核对、Lean 诊断与公理导出 | `scripts/probe_paper_search_output.json` |

## 2. AI 具体贡献（按论文部分）

1. **数学探索**：九轮云端研究提出归约链（定理 A/B/C/D/E、命题 G/H′）与障碍分析；全部以"候选命题"产出，正确性由纸面证明与 Lean 内核分别确立。
2. **形式化**：Lean 4 证明脚本由代理编写，经 `lake build` + `#print axioms` 全量审计（349 条，`sorryAx = 0`，见 `verification/audit_recheck_20261121.log`）；11-21 合并 Takeover 5 个新模块与 71 条审计（`takeover_merge_build_20261121.log` 待构建完成后归档）。
3. **计算证书**：`residue_certificate.py`（357/512–359/512）、450 位区间证书、`verify_*` 系列脚本复跑；数值仅佐证，不参与证明（见各 `.log`）。
4. **写作与整理**：论文 TeX 起草与修订、投稿信/复核信草稿、目录重组脚本；**所有数学断言的最终责任在人类作者**。

## 3. 人类作者保留事项（AI 未做）

- 全部纸面证明的逐行人工核验；定理陈述的最终拍板。
- 署名排序、通讯作者、单位、基金标注。
- 私人复核信的发出与反馈处置（见 `review_cover_letter_draft.md` 反馈处置记录表）。
- 选刊决策与各期刊 AI 政策的最终合规判断。
- arXiv 提交（含许可权）与版本管理。

## 4. 各渠道披露映射（定稿前复核原文）

- **Acta Arith.**：实质性 AI 使用须完整披露；本稿含实质性 AI 研究参与——投稿前须按"人和结果"核定贡献（见 `journal_policy_notes.md`）。
- **J. Number Theory（Elsevier）**：生成式 AI 的工具/用途/监督单独声明 + 方法中描述研究过程 AI 使用。
- **Combinatorics and Number Theory**：论证与引文中的 AI 辅助应声明；禁投"主要由 AI 创建"的论文——需真实贡献记录支撑资格判断。
- **arXiv**：提交人须有提交与许可权利；AI 参与本身不禁，但须与期刊政策一致。

## 5. 待作者确认清单

- [ ] 署名与排序、通讯作者、单位
- [ ] 上述 §2 四条贡献描述是否准确、有无遗漏/夸大
- [ ] 选刊（JNT / Acta Arith. / Exp. Math. / Proc. Edinburgh / 其他）
- [ ] 按所选期刊政策定稿披露声明的具体措辞
- [ ] 私人复核信收件人与发出时间
