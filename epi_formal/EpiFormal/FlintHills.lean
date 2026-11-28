import Mathlib
import EpiFormal.Measure
import EpiFormal.MeiburgConvergence

/-!
# Flint Hills 猜想与命题 H′（T3 目标）

猜想陈述已在 DeepMind formal-conjectures 仓库形式化（issue #3484，2026-03-17 关闭，
形式化可行性评级 1/5）。此处给出等价陈述与论文的条件性命题 H′。

依据文献：
- Alekseyev 2011 (arXiv:1104.5100v1, eprint，未发表，无期刊记录)：收敛 ⇒ μ(π) ≤ 5/2。
- Meiburg 2022 (arXiv:2208.13356，预印本；第八轮已核验其证明结构)：μ(π) < 5/2 ⇒ 收敛。
-/

open Real

/-- Flint Hills 级数收敛性猜想（开放问题）。指标平移 n+1 以避开 n=0。 -/
def FlintHillsConjecture : Prop :=
  Summable (fun n : ℕ => 1 / (((n + 1) : ℝ)^3 * (sin (n + 1))^2))

/-- 收敛的必要条件：Flint Hills 收敛 ⇒ 通项趋于 0（标准分析，已证）。 -/
theorem flint_hills_term_tendsto_zero (h : FlintHillsConjecture) :
    Filter.Tendsto (fun n : ℕ => 1 / (((n + 1) : ℝ)^3 * (sin (n + 1))^2))
      Filter.atTop (nhds 0) :=
  h.tendsto_atTop_zero

/-- sin 整数下界：|sin n| ≤ |n − mπ|（周期平移 + |sin x|≤|x|）。 -/
lemma abs_sin_int_le (n : ℕ) (m : ℤ) :
    |sin (n : ℝ)| ≤ |(n : ℝ) - (m : ℝ) * π| := by
  have h1 : sin ((n : ℝ) - (m : ℝ) * π) = (-1 : ℝ) ^ m * sin (n : ℝ) := by
    have := Real.sin_sub_int_mul_pi (n : ℝ) m
    simpa using this
  have h2 : |sin ((n : ℝ) - (m : ℝ) * π)| = |sin (n : ℝ)| := by
    rw [h1]
    simp [abs_mul, abs_zpow]
  have h3 : |sin ((n : ℝ) - (m : ℝ) * π)| ≤ |(n : ℝ) - (m : ℝ) * π| :=
    Real.abs_sin_le_abs
  linarith

/- T3（Alekseyev 方向）见 EpiFormal/Alekseyev.lean：已证 sin_nat_ne_zero、
   sin_eventual_lower、abs_sub_mul_pi_factor 三引理（无 sorryAx）；
   完整密度论证为研究级开放缺口，精确障碍在该文件末节如实记录。
   原 alekseyev_diophantine / alekseyev_bound 的 sorry 陈述已弃用（方向错误）。 -/

/-- Meiburg 判据（μ(π) < 5/2 ⇒ Flint Hills 收敛）。【已完整机器验证，无 sorryAx】
    原为预印本公理（arXiv:2208.13356）；F2 已用圆周间距+二进块计数+几何求和直接证明，
    见 EpiFormal/MeiburgConvergence.lean 的 flint_hills_converges_of_mu_lt。 -/
theorem meiburg_criterion : irrMeasure π < 5/2 → FlintHillsConjecture := by
  intro h
  exact flint_hills_converges_of_mu_lt h

/-- 命题 H′：e+π 有理 ⇒ Flint Hills 收敛。【已完整机器验证，无 sorryAx】
    证明接线：theoremA_sum（已证，平移+有理缩放不变性）给出 μ(π)=2，2 < 5/2 严格成立，
    避开 Meiburg 的边界情形 μ=5/2。meiburg_criterion 已是定理（F2），
    公理依赖仅 mu_e_eq_two + pi_transcendental + Lean 基础。 -/
theorem proposition_H' (h : ∃ q : ℚ, exp 1 + π = q) : FlintHillsConjecture := by
  have hμ : irrMeasure π = 2 := theoremA_sum h
  apply meiburg_criterion
  rw [hμ]
  have hnum : (2 : ENNReal) < 5 / 2 := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  exact hnum

/-- 命题 H′ 逆否：Flint Hills 发散 ⇒ μ(π) ≥ 5/2。（已证，meiburg_criterion 为定理） -/
theorem flint_hills_diverges_bound (h : ¬ FlintHillsConjecture) : irrMeasure π ≥ 5/2 := by
  by_contra hlt
  push Not at hlt
  have hconv : FlintHillsConjecture := meiburg_criterion hlt
  exact h hconv
