# 核验脚本、审计日志、证明记录与一次文献总索引（`verification/`）

> 本目录归档全项目的机器审计对账、高精度数值证书/佐证、数学证明与新颖性核查记录以及一次文献 PDF（总计 500+ 顶层文件 + 子目录 `reference_pdfs/`、`lean_drafts/`）。所有历史日志按原名冻结保留以保证内部互引完整；权威结论口径严格遵循 [`../AGENTS.md`](../AGENTS.md) 与 [`../README.md`](../README.md)。

## 一、全库治理总表与核心复核（先看这里）

| 文件 | 用途与最新状态 |
| :--- | :--- |
| [`全工作区总索引与留痕台账.md`](全工作区总索引与留痕台账.md) | 从阶段一到 2026-11-23 第十四节的全程时间线台账 |
| [`成果清单与边界.md`](成果清单与边界.md) | T1–T4 分层成果清单与敌意审查纠错汇总（含 2026-11-23 增量头注） |
| [`复现指南.md`](复现指南.md) | 独立环境 Lean 4 / Python 复现步骤与 Windows 并发提示 |
| [`verify_repo_integrity.py`](verify_repo_integrity.py) / [`.log`](verify_repo_integrity.log) | **一键全库体检脚本**：检查 `1e91028`/`7ece3b9` 零文件丢失、Lean 9 入口审计（1,093 条声明）、论文二与 2D/2E 编译与切片一致性、拆分引用及文档本地链接/技能同步（含 Linux/Windows 路径兼容） |
| [`compare_audit_logs.py`](compare_audit_logs.py) | `#print axioms` 输出逐条比对器（支持 `--count` 与 `--only-axioms` 校验核心 937 + 8 路独立审计合计 156 条，供根 CI 调用） |
| [`check_audit_reconcile.py`](check_audit_reconcile.py) | 核对 [`audit_final_20261122.log`](audit_final_20261122.log)（937/937 严格双射、0 `sorryAx`、23 白名单、全库 356 个 `.lean` 文件 0 逃逸关键字） |
| [`verify_paper2_merge.py`](verify_paper2_merge.py) / [`.log`](verify_paper2_merge.log) | 检查论文二 `86` 唯一标签、`28/28` 全引用、`46` 项内容锚点及 `split/src_sections/` 11 片逐字节一致（`289,499` 字节） |
| [`value_rating_and_top_journal_gap_20261125.md`](value_rating_and_top_journal_gap_20261125.md) | 2026-11-25 全内容价值评级（A–D）、期刊档位（T1–T4）差距分析与优化优先级 |

## 二、2026-11-22 至 2026-11-25 核心审计日志与专题核查记录

* **Lean 4 审计日志与独立复现**：
  * [`audit_final_20261122.log`](audit_final_20261122.log)（`Audit.lean` 937 条核心声明）
  * [`colab_rebuild_audit_20261123.md`](colab_rebuild_audit_20261123.md) 与 [`colab_rebuild_audit_20261124.md`](colab_rebuild_audit_20261124.md)（两次 Google Colab 洁净克隆全量复现审计，937/937 + 27/27 + 24/24 逐条一致）
  * [`residue_certgen_lean_20261123.md`](residue_certgen_lean_20261123.md)（$N=512$ 残差证书 Lean 内核化 `ResidueCertTable.lean` 全流程与 `cert_v3_redesign_20261123.md`）
  * [`audit_residue_multi_asymptotic_20261123.log`](audit_residue_multi_asymptotic_20261123.log) 与 [`推广1_多残差相变与欧拉常数三阶渐近Lean4记录_20261123.md`](推广1_多残差相变与欧拉常数三阶渐近Lean4记录_20261123.md)（`ResidueMultiAsymptotic.lean` Part 1–6 及 `AuditResidueMultiAsymptotic.lean` 24/24 纯基础公理证明记录）
  * **Round 2 新增 6 路独立 Layer A 审计日志（105 条新声明，0 `sorryAx`）**：[`audit_residue_cert_strict_open_20261125.log`](audit_residue_cert_strict_open_20261125.log)（`22`，消除 R1）、[`audit_mu_e_eq_two_20261125.log`](audit_mu_e_eq_two_20261125.log)（`9`，证明 $\mu(e)=2$）、[`audit_general_alphabet_floor_20261125.log`](audit_general_alphabet_floor_20261125.log)（`15`，稀疏字母表下界与零极限）、[`audit_supercritical_constant_20261125.log`](audit_supercritical_constant_20261125.log)（`6`，条件于 `hPole` 超临界常数归约）、[`audit_perron_frobenius_20261125.log`](audit_perron_frobenius_20261125.log)（`13`，Brouwer-free Perron–Frobenius 消除 R3）与 [`audit_full_convergent_spectrum_20261125.log`](audit_full_convergent_spectrum_20261125.log)（`40`，$e$ 全正则收敛列谱论）
  * **Round 2 衍生对抗审查档案**：[`kahane_and_blr_audit_20261125.md`](kahane_and_blr_audit_20261125.md)（猜想 D′/引理 R 否证、确定性定理 K-1/K-2 与非线性 BLR (1.6) 三漏洞核审报告）
* **文献一次核查、双通道证据深调、新颖性重审与前沿记忆（2026-11-22 至 2026-11-25）**：
  * [`cmms_citation_check_20261122.md`](cmms_citation_check_20261122.md)（CMMS 官方 PJM 原文逐页核对 Theorem 5 → Theorem 3）
  * [`paper2_novelty_review_20261123.md`](paper2_novelty_review_20261123.md) 与 [`paper2_novelty_review_20261125.md`](paper2_novelty_review_20261125.md)（R1–R7 负搜索 + 投稿前 DFSU/HU02/Bowen/Good 先例重审）
  * [`candidateA_precedent_search_20261125.md`](candidateA_precedent_search_20261125.md)、[`paper2_venue_gap_assessment_20261125.md`](paper2_venue_gap_assessment_20261125.md)、[`deep_research_and_polish_20261124.md`](deep_research_and_polish_20261124.md)
  * [`journal_landscape_20261124.md`](journal_landscape_20261124.md)、[`journal_landscape_evidence_20261124.md`](journal_landscape_evidence_20261124.md)、[`kms_comparison_materials_20261124.md`](kms_comparison_materials_20261124.md)
  * [`T6_critical_scaling_conjecture_20261124.md`](T6_critical_scaling_conjecture_20261124.md)、[`bowen_dependency_inventory_20261124.md`](bowen_dependency_inventory_20261124.md)、[`generalization_obstacle_list_20261124.md`](generalization_obstacle_list_20261124.md)、[`critical_point_scan_record_20261124.md`](critical_point_scan_record_20261124.md) / [`critical_point_scan_addendum_20261124.md`](critical_point_scan_addendum_20261124.md)
  * [`方法论证据支撑深调报告_20261125.md`](方法论证据支撑深调报告_20261125.md)（六方向双通道深调、8 项冲突对照、6 项 Load-Bearing 勘误/撤稿审计）
  * [`工具库整理与六方向前沿调研记忆_20261125.md`](工具库整理与六方向前沿调研记忆_20261125.md)（本地工具库与 2024–2026 六方向文献记忆）
  * [`论文二拆分分类与Lean精准映射_20261123.md`](论文二拆分分类与Lean精准映射_20261123.md)、[`cert_v3_redesign_20261123.md`](cert_v3_redesign_20261123.md)、`flash_task_briefs*_2026112*.md`、`flash_batch_v2_acceptance_20261124.md`、`paper2_section_map_20261124.csv`、`patch_abstract_scope_preview_20261124.md`
* **论文一 / 论文二专项证明与审计记录（2026-11-15 至 2026-11-22）**：
  * 论文一与黄金比轨道：`P1_洁净环境Lean复现记录.md`、`P3_黄金比轨道精确值与第二极限点证明记录.md`、`P4_与二次Lagrange谱先例全文核查记录.md`、`Path2A_一般B3_B4仿射轨道谱理论记录.md`、`Path2A_B5_B6与多尺度完全闭合记录.md`、`Path2A_Lean4有理端点刚性审计记录.md`、`Path2A_任意分母B一般谱理论记录.md`、`Path2C_Davis_Komatsu_Perron文献边界核查记录.md`、`方向1_黄金比轨道Lean4形式化审计记录.md`、`深挖2_黄金比轨道B2精确值与有理端点刚性证明记录.md`、`paper1_audit_20261121.md`。
  * 论文二谱/规范/窗口体系：`OBL3b_加权相变下界与精确维数形式化记录.md`、`深挖1_论文二全谱离散化与三分法证明记录.md`、`路径2B_一般多项式递推临界规范与三分法证明记录.md`、`路径2B_3_Trichotomy与一般多项式递推Lean4记录.md`、`路径3_临界规范构造与开弧无穷测度Lean4记录.md`、`论文二两稿融合与证明完整性逐项核查表.md`、`paper2_audit_20261121.md`、`路线A_投稿体检与深挖方向评估.md`。

## 三、数值计算与证书生成脚本（明确区分有限计算与 Lean 定理）

* **最新活跃证书、新颖性互证与高精佐证脚本**：
  * [`rational_exclusion_bound_20261124.py`](rational_exclusion_bound_20261124.py) / [`oeis_a058651_crosscheck_20261124.py`](oeis_a058651_crosscheck_20261124.py)（Arb 球算术 `python-flint` 大分母有限排除与 OEIS A058651 复核）
  * [`fourth_term_fit_20261124.py`](fourth_term_fit_20261124.py) / [`.log`](fourth_term_fit_20261124.log)（`rem:fourth-term` 标量模型非严格数值检验）
  * [`verify_c2_discrepancy_20261124.py`](verify_c2_discrepancy_20261124.py) / [`_output.txt`](verify_c2_discrepancy_20261124_output.txt)（旧猜想 C2 固定 $\eta$ 形式 1.19 偏差与 $\Phi(x)$ 代数残差复核）
  * [`critical_point_scan_20261124.py`](critical_point_scan_20261124.py)、[`critical_scaling_check_20261124.py`](critical_scaling_check_20261124.py)、[`paper2_numeric_check_20261124.py`](paper2_numeric_check_20261124.py)（334 点临界扫描、临界标度检查与常量交叉核对）
  * [`paper2_novelty_crosscheck_20261125.py`](paper2_novelty_crosscheck_20261125.py) / [`.log`](paper2_novelty_crosscheck_20261125.log)（Lambert-W 塔与 DFSU (1.4)、HU 上界常数核查）
  * [`verify_evidence_numbers_20261125.py`](verify_evidence_numbers_20261125.py) / [`.log`](verify_evidence_numbers_20261125.log)（2026-11-25 证据深调 50 位 `mpmath` 与精确分式核验）
  * **Kahane Q6 数值探针与 Round 2 对抗验证（有限计算，非证明）**：[`powers_mod1_dimension_numerics_20261125.py`](powers_mod1_dimension_numerics_20261125.py)、[`kahane_martingale_sim_20261125.py`](kahane_martingale_sim_20261125.py)、[`kahane_quenched_bound_table_20261125.py`](kahane_quenched_bound_table_20261125.py)、[`kahane_lemmaD_fourier_20261125.py`](kahane_lemmaD_fourier_20261125.py)、[`kahane_lemmaD_rate_fit_20261125.py`](kahane_lemmaD_rate_fit_20261125.py)，以及 Round 2 新增 [`verify_kahane_q6_refutation_and_det_20261125.py`](verify_kahane_q6_refutation_and_det_20261125.py)（D′/R 反例 + 32000 位真实 $x^n$ 定理 K-2 核验）与 [`verify_nonlinear_blr_20261125.py`](verify_nonlinear_blr_20261125.py)（BLR 超缺项 $19.94\times$ 反例 + 偶数 Hurwitz 120 位检验）
  * **Paper 2D / Paper 1 M1–M2 精密核验脚本**：[`verify_supercritical_exact_constant_20261125.py`](verify_supercritical_exact_constant_20261125.py)（至 $m=10^{12}$ 验证 $K_{\mathrm{exact}}$ 与 50 位稀疏字母表）、[`verify_mixed_eg_hermite_pade_obstruction_20261125.py`](verify_mixed_eg_hermite_pade_obstruction_20261125.py)（SymPy 整性 + LLL + CDT 超度量检验）与 [`verify_mobius_e_full_conv_20261125.py`](verify_mobius_e_full_conv_20261125.py)（40 组 Möbius 矩阵、1240 本原 HNF 与全收敛谱核验）
  * [`residue_certificate_general_N512.py`](residue_certificate_general_N512.py)（最新 $N=512$ 精确整数转移算子证书，对应 Lean 内核闭区间 `ResidueCertGen/`）
  * [`verify_residue_multi_asymptotic.py`](verify_residue_multi_asymptotic.py) / [`.log`](verify_residue_multi_asymptotic.log) / [`.json`](verify_residue_multi_asymptotic.json)（32 位 Chebyshev 配置法全面核验 `thm:multi-residue-asymptotic`）
  * [`verify_paper2_extensions.py`](verify_paper2_extensions.py) / [`.log`](verify_paper2_extensions.log)（50 位验证 $C_r$ / $\psi_{\mathrm{Fib}}$ 与任意增长商三类递推）
  * [`verify_round3.py`](verify_round3.py)（SymPy 12/12）、[`verify_round4.py`](verify_round4.py) / [`certificate_round4.json`](certificate_round4.json)（450 位 `mpmath.iv`）
* **前序 / 历史对比证书与研究过程数值脚本**：
  * [`residue_certificate.py`](residue_certificate.py)（m=4 早期 $N=256$）、[`residue_certificate_general.py`](residue_certificate_general.py) / [`.json`](residue_certificate_general.json)（m=2..6 早期 $N=256$）
  * [`verify_golden_orbit_model.py`](verify_golden_orbit_model.py)、[`verify_golden_b2_exact.py`](verify_golden_b2_exact.py)、[`verify_golden_b3_b4_exact.py`](verify_golden_b3_b4_exact.py)、[`verify_golden_b5_b6_multiscale.py`](verify_golden_b5_b6_multiscale.py)、[`verify_golden_general_b.py`](verify_golden_general_b.py)、[`verify_full_spectrum_discrete.py`](verify_full_spectrum_discrete.py)、[`verify_poly_recurrence_2b.py`](verify_poly_recurrence_2b.py)、[`verify_weighted_lower.py`](verify_weighted_lower.py)
  * 辅助开发/比对脚本：`asymptotic_residues_check_20261123.py`（注：历史 Colab 异步实验因未完成故未采信引用，现已由完备且全 PASS 的 `verify_residue_multi_asymptotic.py` 替代）、`blr_formula_compare_20261123.py`、`build_desktop_package_20261122.py`、`patch_independent_rebuild_20261123.py`、`emit_cert_*.py`、`derive_spectrum_2A.py`。

## 四、一次文献与阶段历史留痕子目录

* [`reference_pdfs/`](reference_pdfs/)：直接下载核对的 5 份一次文献全文 PDF（含官方 `CMMS_PJM_2004_217_45.pdf`、`h-sets.pdf`、`BLR_1710_03596.pdf`、`CLU_1805_11904.pdf`、`MEA_2511_10328v3.pdf`）。
* [`lean_drafts/`](lean_drafts/)：早期证书草稿归档（见 [`lean_drafts/README.md`](lean_drafts/README.md)），不参与 `epi_formal/` 构建。
* 2026-11-21 合并过程按文件冻结的 `audit_*_20261121.log`、`*_merge_20261121.md` 与构建日志：全量保留在 `verification/` 顶层，仅供追溯各模块合并时的历史凭证。
