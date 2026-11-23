> [!NOTE]
> **2026-11-22 最新状态提示**：下方原文保留为 **2026-11-14 Phase-1 初版基线快照**（31 条声明 / 9056 jobs）。当前完整工程的 2026-11-22 实测验证状态为：**`lake build EpiFormal` 9179 jobs EXIT 0，共 134 个 `.lean` 文件（132 个 `EpiFormal/` 子模块 + `EpiFormal.lean` + `Audit.lean`），937/937 条 `#print axioms` 严格双射（914 条 Lean 基础公理 [含 5 条零公理] + 23 条论文一经典白名单公理 + 0 条项目自加公理，`sorryAx = 0`，0 逃逸关键字）**。完整最新总览与复现指南请见 [../README.md](../README.md)、[Audit.lean](Audit.lean) 及 [../verification/audit_final_20261122.log](../verification/audit_final_20261122.log)。

# epi_formal — e+π 研究的 Lean 4 形式化

环境：Windows，Lean 4.35.0 + mathlib v4.35.0（lake 项目）。

## 当前状态（2026-11-14 第二轮更新）
- **全项目零 sorry**；`lake build` 9056 jobs 零错误。
- 31 个登记声明经 `#print axioms` 审计，全部无 sorryAx，仅依赖白名单公理：
  e_transcendental、pi_transcendental、mu_e_eq_two + Lean 基础公理。
- **meiburg_criterion 已是定理**（F2 完整机器证明），不再是公理。
- 核心命题 proposition_H'（e+π 有理 ⇒ Flint Hills 收敛）机器验证，
  依赖仅 mu_e_eq_two + pi_transcendental。
- **T3 主定理 alekseyev_bound（Flint Hills 收敛 ⇒ μ(π)≤5/2）机器验证**
  （最近整数论证，2026-11-14），依赖仅 pi_transcendental + 基础公理。

## 模块
- Axioms.lean：e、π 超越性公理；e、π 无理性（已证）。
- Elementary.lean：韦达恒等式、二次根代数性、定理 2.1/2.2。
- Measure.lean：非退化 irrMeasure（ℤ 分子 + ENNReal）、不变性、定理 A（零 sorry）。
- Series.lean：级数可和性与精确递推。
- FlintHills.lean：Flint Hills 猜想陈述、meiburg_criterion（定理）、proposition_H'、逆否。
- Meiburg.lean：稀疏性代数 7 引理。
- MeiburgConvergence.lean：F2 收敛层 20 声明（圆周间距、二进块计数、Jordan、几何求和）。
- Alekseyev.lean：T3 三引理（sin_nat_ne_zero、sin_eventual_lower、abs_sub_mul_pi_factor）
  + 最近整数论证六声明（主定理 alekseyev_bound：收敛⇒μ(π)≤5/2，无 sorryAx）
  + 朴素逐项法障碍的历史记录。
- Audit.lean：公理审计脚本（`lake env lean Audit.lean`）。

## 治理文档
RESEARCH_LOG.md（路线与失败留痕）、PROOF_PLAN.md（里程碑）、LEMMA_AUDIT.md（引理审计）、
PROOF_GAPS.md（缺口登记）、FINAL_REVIEW.md（独立审查）。

## 诚实边界
形式化验证的是论文推导的逻辑正确性，**不证明 e+π 无理性**（开放问题）。
alekseyev_bound（收敛⇒μ(π)≤5/2）已机器验证，但其前提 Flint Hills 收敛本身是开放问题，
故为条件性结果。修订包补充页与 S1–S7 扩展仍为纸面证明，未形式化。