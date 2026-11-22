import EpiFormal.WindowAndResidueCore

open scoped BigOperators ENNReal

namespace WindowShortAe

/-!
# `thm:short-ae`：tower / Markov / Borel–Cantelli 组装链

纸面位置：`paper2_spectral_gap_dimension.tex` 第 2610–2726 行
（Theorem `thm:short-ae` 及其证明）。

本文件形式化该证明中“停柱集 / Möbius 参数化之后”的组装链：

* §1 单步指数矩因子：复用已核实引理
  `WindowAndResidueCore.thm19_exp_moment_step_le`（一步收缩）
  与 `WindowAndResidueCore.thm19_cond_prob_lower_bound`（柱集一致下界），
  得到 `E[exp(-1_{E_j}) | F_j] ≤ exp(-b / j)` 的纯实数形式。
* §2 tower 迭代的确定性推论：抽象期望序列的单步界经归纳得到
  `E_J ≤ j₀^b · J^{-b}`（含调和和下界 `∑ 1/j ≥ log(J+1) - log j₀` 的完整证明）。
* §3 Markov 不等式的 mathlib 应用（`mul_meas_ge_le_lintegral₀`）。
* §4 dyadic 子列的几何可和性与首 Borel–Cantelli
  （`measure_limsup_atTop_eq_zero`、`ae_eventually_notMem` 均直接调用）。
* §5 dyadic 下界到全体 `J` 的单调性延拓（`c = b / 4`）。
* §6 主组装定理 `short_ae_main`。

显式假设接口（纸面接口，未在本文件中证明）：
(i) tower 单步条件期望不等式（需要滤波与条件期望机制）；
(ii) 坏事件集的示性描述（停时柱集的划分结构）；
(iii) 可积性、初值界与平凡单步界（标准分析侧条件）。
Möbius 密度积分的代数部分已由 `thm19_cond_prob_integral_identity` 覆盖。
-/

/-! ## §1 单步指数矩因子（复用已核实引理） -/

/-- **单步指数矩因子**：条件概率 `p ≥ c₀ / j` 蕴含
`e⁻¹ p + (1 - p) ≤ exp(-((1 - e⁻¹) c₀) / j)`。
即纸面 `E[exp(-1_{E_j}) | F_j] ≤ exp(-b / j)`（`b = (1 - e⁻¹) c₀`）的纯实数形式，
直接复用 `thm19_exp_moment_step_le`。 -/
theorem short_ae_one_step_factor
    (c0 p : ℝ) (j : ℕ)
    (hc0 : 0 < c0) (hj : 1 ≤ j)
    (hp : c0 / (j : ℝ) ≤ p) :
    Real.exp (-1) * p + (1 - p)
      ≤ Real.exp (-((1 - Real.exp (-1)) * c0) / (j : ℝ)) := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by
    have h : 0 < j := by omega
    exact_mod_cast h
  have hp0 : 0 ≤ c0 / (j : ℝ) := div_nonneg hc0.le hjpos.le
  have h := WindowAndResidueCore.thm19_exp_moment_step_le p (c0 / (j : ℝ)) hp0 hp
  have heq : (1 - Real.exp (-1)) * (c0 / (j : ℝ))
      = ((1 - Real.exp (-1)) * c0) / (j : ℝ) := by ring
  have heq2 : -(1 - Real.exp (-1)) * (c0 / (j : ℝ))
      = -((1 - Real.exp (-1)) * c0) / (j : ℝ) := by ring
  rw [heq, heq2] at h
  exact le_trans h.1 h.2

/-- **柱集参数到单步因子的实例化**：把 `thm19_cond_prob_lower_bound`
（一切停柱集上 `P(E_j | I) ≥ (q + q') / (A q + q') ≥ 1 / A ≥ H_j / (2 H_{j+1})`）
与单步因子链起来；`c₀ / j ≤ H_j / (2 H_{j+1})`
是纸面 `H_{j+1} / H_j = 4j + O(1)` 的比值接口。 -/
theorem short_ae_step_factor_from_cylinders
    (Hj Hj1 q q' A c0 : ℝ) (j : ℕ)
    (hc0 : 0 < c0) (hj : 1 ≤ j)
    (hHj : 0 < Hj) (hq : Hj < q)
    (hq'0 : 0 ≤ q') (hq'q : q' ≤ q)
    (hA1 : 1 ≤ A) (hA2 : A ≤ 2 * Hj1 / Hj)
    (hfloor : c0 / (j : ℝ) ≤ Hj / (2 * Hj1))
    (p : ℝ) (hp : (q + q') / (A * q + q') ≤ p) :
    Real.exp (-1) * p + (1 - p)
      ≤ Real.exp (-((1 - Real.exp (-1)) * c0) / (j : ℝ)) := by
  have h := WindowAndResidueCore.thm19_cond_prob_lower_bound
    Hj Hj1 q q' A hHj hq hq'0 hq'q hA1 hA2
  exact short_ae_one_step_factor c0 p j hc0 hj
    (le_trans hfloor (le_trans h.1 (le_trans h.2 hp)))

/-! ## §2 tower 迭代：调和和下界与多项式界 -/

/-- **望远镜求和**：`∑_{j ∈ Icc j₀ J} (F (j+1) - F j) = F (J+1) - F j₀`。 -/
theorem short_ae_telescope (F : ℕ → ℝ) (j0 J : ℕ) (hJ : j0 ≤ J) :
    ∑ j ∈ Finset.Icc j0 J, (F (j + 1) - F j) = F (J + 1) - F j0 := by
  induction J, hJ using Nat.le_induction with
  | base => simp
  | succ n hnm ih =>
    have htop : ∑ j ∈ Finset.Icc j0 (n + 1), (F (j + 1) - F j)
        = (∑ j ∈ Finset.Icc j0 n, (F (j + 1) - F j))
          + (F (n + 1 + 1) - F (n + 1)) :=
      Finset.sum_Icc_succ_top (by omega) _
    rw [htop, ih]
    ring

/-- **调和和对数下界**：`∑_{j ∈ Icc j₀ J} 1 / j ≥ log(J + 1) - log j₀`。
每项用 `log(1 + 1/j) ≤ 1/j`（即 `Real.log_le_sub_one_of_pos`），再望远镜求和。 -/
theorem short_ae_harmonic_ge_log (j0 J : ℕ) (hj0 : 1 ≤ j0) (hJ : j0 ≤ J) :
    Real.log ((J : ℝ) + 1) - Real.log (j0 : ℝ)
      ≤ ∑ j ∈ Finset.Icc j0 J, (1 : ℝ) / (j : ℝ) := by
  have htele := short_ae_telescope (fun n => Real.log ((n : ℕ) : ℝ)) j0 J hJ
  have hterm : ∀ j : ℕ, j ∈ Finset.Icc j0 J →
      Real.log ((((j + 1 : ℕ))) : ℝ) - Real.log (j : ℝ)
        ≤ (1 : ℝ) / (j : ℝ) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : 1 ≤ j := le_trans hj0 hj.1
    have hjR : (0 : ℝ) < (j : ℝ) := by
      have h : 0 < j := by omega
      exact_mod_cast h
    have hjne : (j : ℝ) ≠ 0 := ne_of_gt hjR
    have hcast : ((((j + 1 : ℕ))) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    have hqpos : (0 : ℝ) < ((j : ℝ) + 1) / (j : ℝ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hqpos
    have hdiv : ((j : ℝ) + 1) / (j : ℝ) - 1 = 1 / (j : ℝ) := by
      field_simp
      ring
    have hlogdiv : Real.log (((j : ℝ) + 1) / (j : ℝ))
        = Real.log ((((j + 1 : ℕ))) : ℝ) - Real.log (j : ℝ) := by
      rw [hcast]
      exact Real.log_div (by positivity) hjne
    linarith
  calc Real.log ((J : ℝ) + 1) - Real.log (j0 : ℝ)
      = ∑ j ∈ Finset.Icc j0 J,
          (Real.log ((((j + 1 : ℕ))) : ℝ) - Real.log (j : ℝ)) := by
        have hJcast : ((((J + 1 : ℕ))) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
        rw [← hJcast]
        exact htele.symm
    _ ≤ ∑ j ∈ Finset.Icc j0 J, (1 : ℝ) / (j : ℝ) :=
        Finset.sum_le_sum hterm

/-- **指数界转多项式界**：
`exp(-b (log(J+1) - log j₀)) ≤ j₀^b · J^{-b}`（即纸面 `C = e^{b log j₀}`）。 -/
theorem short_ae_exp_to_poly (b : ℝ) (j0 J : ℕ)
    (hb : 0 < b) (hj0 : 1 ≤ j0) (hJ : 1 ≤ J) :
    Real.exp (-b * (Real.log ((J : ℝ) + 1) - Real.log (j0 : ℝ)))
      ≤ (j0 : ℝ) ^ b * (J : ℝ) ^ (-b) := by
  have hj0R : (0 : ℝ) < (j0 : ℝ) := by
    have h : 0 < j0 := by omega
    exact_mod_cast h
  have hJR : (0 : ℝ) < (J : ℝ) := by
    have h : 0 < J := by omega
    exact_mod_cast h
  have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by linarith
  have hle1 : (J : ℝ) / (j0 : ℝ) ≤ ((J : ℝ) + 1) / (j0 : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (inv_nonneg.mpr hj0R.le)
  have hkey : -b * (Real.log ((J : ℝ) + 1) - Real.log (j0 : ℝ))
      = Real.log ((((J : ℝ) + 1) / (j0 : ℝ)) ^ (-b)) := by
    rw [Real.rpow_def_of_pos (div_pos hJ1 hj0R), Real.log_exp,
      Real.log_div (ne_of_gt hJ1) (ne_of_gt hj0R)]
    ring
  rw [hkey, Real.exp_log
    (Real.rpow_pos_of_pos (div_pos hJ1 hj0R) _)]
  refine le_trans
    (Real.rpow_le_rpow_of_nonpos (div_pos hJR hj0R) hle1 (by linarith)) ?_
  rw [Real.div_rpow hJR.le hj0R.le, Real.rpow_neg hj0R.le, Real.rpow_neg hJR.le,
    div_eq_mul_inv, inv_inv]
  apply le_of_eq
  ring

/-- **tower 迭代的闭式多项式界**：抽象期望序列满足初值界、平凡单步界（`j < j₀`）
与指数单步界（`j ≥ j₀`）时，对一切 `J ≥ 1` 有 `E_J ≤ j₀^b · J^{-b}`。
这是纸面 tower 迭代 `E[e^{-Z_J}] ≤ C J^{-b}`（`C = e^{b log j₀} = j₀^b`）
的确定性后件；条件期望的 tower 恒等式本身留作主定理的假设接口。 -/
theorem short_ae_tower_closed_form (E : ℕ → ℝ) (b : ℝ) (j0 : ℕ)
    (hb : 0 < b) (hj0 : 1 ≤ j0)
    (hE0 : E 0 ≤ 1)
    (htriv : ∀ j : ℕ, 1 ≤ j → j < j0 → E j ≤ E (j - 1))
    (hstep : ∀ j : ℕ, j0 ≤ j → E j ≤ E (j - 1) * Real.exp (-b / (j : ℝ))) :
    ∀ J : ℕ, 1 ≤ J → E J ≤ (j0 : ℝ) ^ b * (J : ℝ) ^ (-b) := by
  have hj0R : (0 : ℝ) < (j0 : ℝ) := by
    have h : 0 < j0 := by omega
    exact_mod_cast h
  have hEle1 : ∀ n : ℕ, n < j0 → E n ≤ 1 := by
    intro n hn
    induction n with
    | zero => exact hE0
    | succ k ih =>
      exact le_trans (htriv (k + 1) (by omega) hn) (ih (by omega))
  have hexp : ∀ n : ℕ,
      E n ≤ Real.exp (-b * ∑ j ∈ Finset.Icc j0 n, (1 : ℝ) / (j : ℝ)) := by
    intro n
    induction n with
    | zero =>
      have hempty : Finset.Icc j0 0 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [Finset.mem_Icc] at hx
        omega
      rw [hempty, Finset.sum_empty, mul_zero, Real.exp_zero]
      exact hE0
    | succ k ih =>
      by_cases hk : j0 ≤ k + 1
      · have hkc : ((((k + 1 : ℕ))) : ℝ) ≠ 0 := by
          have h : k + 1 ≠ 0 := by omega
          exact_mod_cast h
        have hsum : ∑ j ∈ Finset.Icc j0 (k + 1), (1 : ℝ) / (j : ℝ)
            = (∑ j ∈ Finset.Icc j0 k, (1 : ℝ) / (j : ℝ))
              + 1 / ((((k + 1 : ℕ))) : ℝ) :=
          Finset.sum_Icc_succ_top hk _
        have hpos : (0 : ℝ) ≤ Real.exp (-b / ((((k + 1 : ℕ))) : ℝ)) :=
          (Real.exp_pos _).le
        have hexparg : -b * ((∑ j ∈ Finset.Icc j0 k, (1 : ℝ) / (j : ℝ))
            + 1 / ((((k + 1 : ℕ))) : ℝ))
            = -b * (∑ j ∈ Finset.Icc j0 k, (1 : ℝ) / (j : ℝ))
              + -b / ((((k + 1 : ℕ))) : ℝ) := by
          field_simp
          ring
        calc E (k + 1)
            ≤ E ((k + 1) - 1) * Real.exp (-b / ((((k + 1 : ℕ))) : ℝ)) :=
              hstep (k + 1) hk
          _ = E k * Real.exp (-b / ((((k + 1 : ℕ))) : ℝ)) := by
              rw [Nat.add_sub_cancel]
          _ ≤ Real.exp (-b * ∑ j ∈ Finset.Icc j0 k, (1 : ℝ) / (j : ℝ))
              * Real.exp (-b / ((((k + 1 : ℕ))) : ℝ)) :=
              mul_le_mul_of_nonneg_right ih hpos
          _ = Real.exp (-b * ∑ j ∈ Finset.Icc j0 (k + 1), (1 : ℝ) / (j : ℝ)) := by
              rw [hsum, hexparg, Real.exp_add]
      · have hkle : k + 1 < j0 := by omega
        have hempty : Finset.Icc j0 (k + 1) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro x hx
          rw [Finset.mem_Icc] at hx
          omega
        rw [hempty, Finset.sum_empty, mul_zero, Real.exp_zero]
        exact hEle1 (k + 1) hkle
  intro J hJ
  by_cases hJj : J < j0
  · have hJpos : (0 : ℝ) < (J : ℝ) := by
      have h : 0 < J := by omega
      exact_mod_cast h
    have hj0J : (1 : ℝ) ≤ (j0 : ℝ) / (J : ℝ) := by
      rw [le_div_iff₀ hJpos]
      have hJj0 : (J : ℝ) ≤ (j0 : ℝ) := by
        have h : J ≤ j0 := le_of_lt hJj
        exact_mod_cast h
      linarith
    have h2 : (1 : ℝ) ≤ ((j0 : ℝ) / (J : ℝ)) ^ b := Real.one_le_rpow hj0J hb.le
    have h3 : ((j0 : ℝ) / (J : ℝ)) ^ b = (j0 : ℝ) ^ b * (J : ℝ) ^ (-b) := by
      rw [Real.div_rpow hj0R.le hJpos.le, Real.rpow_neg hJpos.le, div_eq_mul_inv]
    exact le_trans (le_trans (hEle1 J hJj) h2) (le_of_eq h3)
  · have hJJ : j0 ≤ J := le_of_not_gt hJj
    have hS := short_ae_harmonic_ge_log j0 J hj0 hJJ
    have harg : -b * ∑ j ∈ Finset.Icc j0 J, (1 : ℝ) / (j : ℝ)
        ≤ -b * (Real.log ((J : ℝ) + 1) - Real.log (j0 : ℝ)) :=
      mul_le_mul_of_nonpos_left hS (by linarith)
    refine le_trans (hexp J) (le_trans (Real.exp_le_exp.mpr harg) ?_)
    exact short_ae_exp_to_poly b j0 J hb hj0 hJ

/-! ## §3 Markov 不等式的 mathlib 应用 -/

/-- **Markov 界包装**：由 mathlib 的 `mul_meas_ge_le_lintegral₀` 直接得到
`μ {ε ≤ Y} ≤ Ebar / ε`。这是纸面
`P(Z_J < (b/2) log J) = P(e^{-Z_J} > J^{-b/2}) ≤ J^{b/2} E[e^{-Z_J}]` 的测度论形式。 -/
theorem short_ae_markov_meas_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (Y : Ω → ℝ≥0∞) (hY : AEMeasurable Y μ)
    (Ebar ε : ℝ≥0∞)
    (hint : ∫⁻ ω, Y ω ∂μ ≤ Ebar) (hε0 : ε ≠ 0) (hεtop : ε ≠ ⊤) :
    μ {ω | ε ≤ Y ω} ≤ Ebar / ε := by
  have h := MeasureTheory.mul_meas_ge_le_lintegral₀ hY ε
  have h' : μ {ω | ε ≤ Y ω} * ε ≤ Ebar := by
    rw [mul_comm]
    exact le_trans h hint
  exact (ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl hεtop)).mpr h'

/-! ## §4 dyadic 子列：几何可和性与首 Borel–Cantelli -/

/-- **dyadic 幂恒等式**：`((2^m : ℕ) : ℝ)^{-b/2} = (2^{-b/2})^m`。 -/
theorem short_ae_dyadic_rpow_eq (b : ℝ) (m : ℕ) :
    ((((2 ^ m : ℕ))) : ℝ) ^ (-(b / 2)) = ((2 : ℝ) ^ (-(b / 2))) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hcast : ((((2 ^ (k + 1) : ℕ))) : ℝ) = ((((2 ^ k : ℕ))) : ℝ) * 2 := by
      rw [pow_succ, Nat.cast_mul, Nat.cast_two]
    rw [hcast, Real.mul_rpow (by positivity) (by norm_num), ih, pow_succ]

/-- **Markov 比值化为几何项**：
`ofReal (C₀ · J_m^{-b} / J_m^{-b/2}) = ofReal C₀ · ρ^m`
（`J_m = 2^m`，`ρ = ofReal (2^{-b/2})`），即纸面
`C J^{-b} / J^{-b/2} = C J^{-b/2}` 沿 dyadic 子列的 `ℝ≥0∞` 形式。 -/
theorem short_ae_dyadic_ratio_bound (C0 b : ℝ) (m : ℕ)
    (hC0 : 0 ≤ C0) :
    ENNReal.ofReal (C0 * ((((2 ^ m : ℕ))) : ℝ) ^ (-b)
        / ((((2 ^ m : ℕ))) : ℝ) ^ (-(b / 2)))
      = ENNReal.ofReal C0 * (ENNReal.ofReal ((2 : ℝ) ^ (-(b / 2)))) ^ m := by
  have hJm : (0 : ℝ) < ((((2 ^ m : ℕ))) : ℝ) := by positivity
  have hsplit : ((((2 ^ m : ℕ))) : ℝ) ^ (-b)
      = ((((2 ^ m : ℕ))) : ℝ) ^ (-(b / 2))
        * ((((2 ^ m : ℕ))) : ℝ) ^ (-(b / 2)) := by
    rw [← Real.rpow_add hJm]
    congr 1
    ring
  have hfield : C0 * ((((2 ^ m : ℕ))) : ℝ) ^ (-b)
        / ((((2 ^ m : ℕ))) : ℝ) ^ (-(b / 2))
      = C0 * ((((2 ^ m : ℕ))) : ℝ) ^ (-(b / 2)) := by
    have hyne : ((((2 ^ m : ℕ))) : ℝ) ^ (-(b / 2)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hJm _)
    rw [hsplit]
    field_simp
  rw [hfield, ENNReal.ofReal_mul hC0,
    short_ae_dyadic_rpow_eq b m,
    ENNReal.ofReal_pow (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))]

/-- **dyadic 坏事件的测度可和**：几何级数控制给出 `∑' μ(B m) ≠ ⊤`。 -/
theorem short_ae_dyadic_summable (B : ℕ → ℝ≥0∞) (Cbar ρ : ℝ≥0∞)
    (hC : Cbar ≠ ⊤) (hρ1 : ρ < 1) (hB : ∀ m, B m ≤ Cbar * ρ ^ m) :
    ∑' m, B m ≠ ⊤ := by
  have hρle : ρ ≤ 1 := le_of_lt hρ1
  have h1ρ : (1 : ℝ≥0∞) - ρ ≠ 0 := by
    intro h0
    have hle1 : (1 : ℝ≥0∞) ≤ ρ := tsub_eq_zero_iff_le.mp h0
    exact absurd hle1 (not_le_of_gt hρ1)
  have hfin : Cbar * (1 - ρ)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top hC (ENNReal.inv_ne_top.mpr h1ρ)
  have hle : ∑' m, B m ≤ Cbar * (1 - ρ)⁻¹ := by
    calc ∑' m, B m ≤ ∑' m, Cbar * ρ ^ m := ENNReal.tsum_le_tsum hB
      _ = Cbar * ∑' m, ρ ^ m := ENNReal.tsum_mul_left
      _ = Cbar * (1 - ρ)⁻¹ := by rw [ENNReal.tsum_geometric]
  exact ne_top_of_le_ne_top hfin hle

/-- **首 Borel–Cantelli 组装**：直接调用 mathlib 的
`measure_limsup_atTop_eq_zero` 与 `ae_eventually_notMem`。 -/
theorem short_ae_BC_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (Bset : ℕ → Set Ω) (Cbar ρ : ℝ≥0∞)
    (hC : Cbar ≠ ⊤) (hρ1 : ρ < 1) (hB : ∀ m, μ (Bset m) ≤ Cbar * ρ ^ m) :
    (∀ᵐ ω ∂μ, ∀ᶠ m in Filter.atTop, ω ∉ Bset m)
      ∧ μ (Filter.limsup Bset Filter.atTop) = 0 := by
  have hsum : ∑' m, μ (Bset m) ≠ ⊤ := short_ae_dyadic_summable _ _ _ hC hρ1 hB
  exact ⟨MeasureTheory.ae_eventually_notMem hsum,
    MeasureTheory.measure_limsup_atTop_eq_zero hsum⟩

/-- **单步代数不等式**：`m ≥ 1` 且 `b * L ≥ 0` 时
`(b/4) * ((m+1) * L) ≤ (b/2) * (m * L)`。这是 dyadic 延拓中
`(b/2)·log(2^m) ≥ (b/4)·log J` 的纯代数核心。 -/
theorem short_ae_step_algebra (b L m : ℝ) (hm : 1 ≤ m) (hpos : 0 ≤ b * L) :
    (b / 4) * ((m + 1) * L) ≤ (b / 2) * (m * L) := by
  have hm1 : (0 : ℝ) ≤ m - 1 := by linarith
  have h : (0 : ℝ) ≤ (b * L) * (m - 1) := mul_nonneg hpos hm1
  nlinarith [h]

/-! ## §5 dyadic 下界到全体 `J` 的单调性延拓 -/

/-- **dyadic 到全体的延拓**：沿 `2^m ≤ J < 2^{m+1}` 用单调性把
`(b/2) log(2^m)` 下界传到 `(b/4) log J`。`m = 0` 时 `log J = 0` 由非负性处理。 -/
theorem short_ae_dyadic_to_full (Z : ℕ → ℝ) (b : ℝ) (m0 J : ℕ)
    (hb : 0 < b)
    (hZnn : ∀ n, 0 ≤ Z n)
    (hmono : Monotone Z)
    (hJ : 2 ^ m0 ≤ J)
    (hdy : ∀ m : ℕ, m0 ≤ m → (b / 2) * Real.log ((((2 ^ m : ℕ))) : ℝ) ≤ Z (2 ^ m)) :
    (b / 4) * Real.log (J : ℝ) ≤ Z J := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJ1 : 1 ≤ J := le_trans (one_le_pow₀ (by norm_num)) hJ
  have hJne : J ≠ 0 := by omega
  have h2mJ : 2 ^ Nat.log 2 J ≤ J := Nat.pow_log_le_self 2 hJne
  have hJ2m : J < 2 ^ (Nat.log 2 J + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) J
    rwa [Nat.succ_eq_add_one] at h
  have hm0m : m0 ≤ Nat.log 2 J := by
    by_contra hlt
    have hle : 2 ^ (Nat.log 2 J + 1) ≤ 2 ^ m0 :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  have hle : Z (2 ^ Nat.log 2 J) ≤ Z J := hmono h2mJ
  have hcast1 : ((((2 ^ Nat.log 2 J : ℕ))) : ℝ) = (2 : ℝ) ^ Nat.log 2 J := by
    norm_cast
  have hlog2m : Real.log ((((2 ^ Nat.log 2 J : ℕ))) : ℝ)
      = ((((Nat.log 2 J : ℕ))) : ℝ) * Real.log 2 := by
    rw [hcast1, Real.log_pow]
  have hcastm : ((((Nat.log 2 J + 1 : ℕ))) : ℝ)
      = ((((Nat.log 2 J : ℕ))) : ℝ) + 1 := by push_cast; ring
  have hlogJ : Real.log (J : ℝ)
      ≤ (((((Nat.log 2 J : ℕ))) : ℝ) + 1) * Real.log 2 := by
    have hleJ : J ≤ 2 ^ (Nat.log 2 J + 1) := le_of_lt hJ2m
    have hJJ : (J : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 J + 1) := by
      have hcast : ((((2 ^ (Nat.log 2 J + 1) : ℕ))) : ℝ)
          = (2 : ℝ) ^ (Nat.log 2 J + 1) := by norm_cast
      calc (J : ℝ) ≤ ((((2 ^ (Nat.log 2 J + 1) : ℕ))) : ℝ) := by
            exact_mod_cast hleJ
        _ = (2 : ℝ) ^ (Nat.log 2 J + 1) := hcast
    have hJpos : (0 : ℝ) < (J : ℝ) := by
      have h : 0 < J := by omega
      exact_mod_cast h
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 J + 1) := by positivity
    have h := (Real.log_le_log_iff hJpos h2pos).mpr hJJ
    rw [Real.log_pow, hcastm] at h
    exact h
  by_cases hm : Nat.log 2 J = 0
  · have h2m : (2 : ℕ) ^ Nat.log 2 J ≤ J := h2mJ
    rw [hm, pow_zero] at h2m
    have hJ2 : J < 2 ^ (Nat.log 2 J + 1) := hJ2m
    rw [hm] at hJ2
    simp at hJ2
    have hJeq : J = 1 := by omega
    rw [hJeq, Nat.cast_one, Real.log_one, mul_zero]
    exact hZnn 1
  · have hmpos : 0 < Nat.log 2 J := Nat.pos_of_ne_zero hm
    have hm1 : (1 : ℝ) ≤ ((((Nat.log 2 J : ℕ))) : ℝ) := by exact_mod_cast hmpos
    have hdy0 := hdy (Nat.log 2 J) hm0m
    have hpos : (0 : ℝ) ≤ b * Real.log 2 := mul_nonneg hb.le hlog2.le
    have step1 :=
      mul_le_mul_of_nonneg_left hlogJ
        (div_nonneg hb.le (show (0 : ℝ) ≤ 4 by norm_num))
    have step2 := short_ae_step_algebra b (Real.log 2)
      ((((Nat.log 2 J : ℕ))) : ℝ) hm1 hpos
    have step3 : (b / 2) * (((((Nat.log 2 J : ℕ))) : ℝ) * Real.log 2)
        ≤ Z (2 ^ Nat.log 2 J) := by
      rw [← hlog2m]
      exact hdy0
    exact le_trans step1 (le_trans step2 (le_trans step3 hle))

/-! ## §6 主组装定理 -/

/-- **主组装定理（`thm:short-ae` 的组装链）**：
在 tower 单步界（`hStep`，`b` 经 `hbdef` 与柱集常数 `c₀` 相连）、
平凡单步界（`hTriv`）、初值界（`hInit`）、可积性（`hInt`）、
计数非负单调（`hZnn`、`hmono`）与坏事件示性描述（`hBchar`）之下，
dyadic 坏事件的测度呈几何衰减，从而 a.e. 点最终脱离全部 dyadic 坏事件、
`limsup` 测度为零，且 a.e. 点有 `Z_J ≥ (b/4) log J` 对一切充分大的 `J` 成立。

纸面接口说明：
`hStep` 是 tower 恒等式 `E[e^{-Z_j}] = E[e^{-Z_{j-1}} E[e^{-1_{E_j}} | F_j]]`
的单步后件（条件期望机制未在本文件形式化）；
`hBchar` 把停时柱集的示性结构抽象为集合等式；
`hfloor`（§1 引理的输入）是 `H_{j+1} / H_j = O(j)` 比值估计的接口。
本定理内部的全部推理（tower 迭代 → Markov → BC → 单调延拓）均已证毕，无任何未证断言。 -/
theorem short_ae_main {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (Z : ℕ → Ω → ℝ) (Bset : ℕ → Set Ω)
    (b c0 : ℝ) (j0 : ℕ)
    (hb : 0 < b) (_hc0 : 0 < c0) (hj0 : 1 ≤ j0)
    (hbdef : b = (1 - Real.exp (-1)) * c0)
    (hZnn : ∀ n ω, 0 ≤ Z n ω)
    (hmono : ∀ ω, Monotone (fun J => Z J ω))
    (hBchar : ∀ m ω,
      ω ∈ Bset m ↔ Z (2 ^ m) ω < (b / 2) * Real.log ((((2 ^ m : ℕ))) : ℝ))
    (hInt : ∀ J, MeasureTheory.Integrable (fun ω => Real.exp (-Z J ω)) μ)
    (hInit : ∫ ω, Real.exp (-Z 0 ω) ∂μ ≤ 1)
    (htriv : ∀ j : ℕ, 1 ≤ j → j < j0 →
      (∫ ω, Real.exp (-Z j ω) ∂μ) ≤ ∫ ω, Real.exp (-Z (j - 1) ω) ∂μ)
    (hStep : ∀ j : ℕ, j0 ≤ j →
      (∫ ω, Real.exp (-Z j ω) ∂μ) ≤ (∫ ω, Real.exp (-Z (j - 1) ω) ∂μ)
        * Real.exp (-((1 - Real.exp (-1)) * c0) / (j : ℝ))) :
    (∀ᵐ ω ∂μ, ∀ᶠ m in Filter.atTop, ω ∉ Bset m)
      ∧ μ (Filter.limsup Bset Filter.atTop) = 0
      ∧ ∀ᵐ ω ∂μ, ∃ M : ℕ, ∀ J : ℕ, M ≤ J →
        (b / 4) * Real.log (J : ℝ) ≤ Z J ω := by
  have hStep' : ∀ j : ℕ, j0 ≤ j →
      (∫ ω, Real.exp (-Z j ω) ∂μ) ≤ (∫ ω, Real.exp (-Z (j - 1) ω) ∂μ)
        * Real.exp (-b / (j : ℝ)) := by
    intro j hj
    rw [hbdef]
    exact hStep j hj
  have hEbound : ∀ J : ℕ, 1 ≤ J →
      (∫ ω, Real.exp (-Z J ω) ∂μ) ≤ (j0 : ℝ) ^ b * (J : ℝ) ^ (-b) :=
    fun J hJ => short_ae_tower_closed_form
      (fun J => ∫ ω, Real.exp (-Z J ω) ∂μ) b j0 hb hj0 hInit htriv hStep' J hJ
  have hρ1 : ENNReal.ofReal ((2 : ℝ) ^ (-(b / 2))) < 1 := by
    have hr : (2 : ℝ) ^ (-(b / 2)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(b / 2)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn).mpr hr
    rwa [ENNReal.ofReal_one] at h
  have hBbound : ∀ m : ℕ, μ (Bset m)
      ≤ ENNReal.ofReal ((j0 : ℝ) ^ b)
        * (ENNReal.ofReal ((2 : ℝ) ^ (-(b / 2)))) ^ m := by
    intro m
    have hJm1 : 1 ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have hE := hEbound (2 ^ m) hJm1
    have hJmpos : (0 : ℝ) < ((((2 ^ m : ℕ))) : ℝ) := by
      have h : (0 : ℕ) < 2 ^ m := pow_pos (by norm_num) m
      exact_mod_cast h
    have hbase : AEMeasurable
        (fun ω => Real.exp (-Z (2 ^ m) ω)) μ :=
      (hInt (2 ^ m)).aemeasurable
    have hYm : AEMeasurable
        (fun ω => ENNReal.ofReal (Real.exp (-Z (2 ^ m) ω))) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable' hbase
    have hYint : ∫⁻ ω, ENNReal.ofReal (Real.exp (-Z (2 ^ m) ω)) ∂μ
        ≤ ENNReal.ofReal ((j0 : ℝ) ^ b * ((((2 ^ m : ℕ))) : ℝ) ^ (-b)) := by
      have hnn : ∀ᵐ ω ∂μ, 0 ≤ Real.exp (-Z (2 ^ m) ω) :=
        MeasureTheory.ae_of_all μ fun ω => (Real.exp_pos _).le
      have hbridge :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hInt (2 ^ m)) hnn
      rw [← hbridge]
      exact ENNReal.ofReal_le_ofReal hE
    have hthr : (0 : ℝ≥0∞)
        < ENNReal.ofReal (((2 ^ m : ℕ) : ℝ) ^ (-(b / 2))) := by
      rw [ENNReal.ofReal_pos]
      exact Real.rpow_pos_of_pos hJmpos _
    have hMarkov := short_ae_markov_meas_bound μ
      (fun ω => ENNReal.ofReal (Real.exp (-Z (2 ^ m) ω))) hYm
      (ENNReal.ofReal ((j0 : ℝ) ^ b * ((((2 ^ m : ℕ))) : ℝ) ^ (-b)))
      (ENNReal.ofReal (((2 ^ m : ℕ) : ℝ) ^ (-(b / 2))))
      hYint (ne_of_gt hthr) ENNReal.ofReal_lt_top.ne
    have hsub : Bset m ⊆ {ω |
        ENNReal.ofReal (((2 ^ m : ℕ) : ℝ) ^ (-(b / 2)))
          ≤ ENNReal.ofReal (Real.exp (-Z (2 ^ m) ω))} := by
      intro ω hω
      have hlt := (hBchar m ω).mp hω
      show ENNReal.ofReal (((2 ^ m : ℕ) : ℝ) ^ (-(b / 2)))
        ≤ ENNReal.ofReal (Real.exp (-Z (2 ^ m) ω))
      apply ENNReal.ofReal_le_ofReal
      have hexp : Real.exp (-((b / 2) * Real.log ((((2 ^ m : ℕ))) : ℝ)))
          = ((((2 ^ m : ℕ))) : ℝ) ^ (-(b / 2)) := by
        rw [Real.rpow_def_of_pos hJmpos]
        congr 1
        ring
      rw [← hexp]
      exact Real.exp_le_exp.mpr (by linarith)
    calc μ (Bset m)
        ≤ ENNReal.ofReal ((j0 : ℝ) ^ b * ((((2 ^ m : ℕ))) : ℝ) ^ (-b))
            / ENNReal.ofReal (((2 ^ m : ℕ) : ℝ) ^ (-(b / 2))) :=
          le_trans (MeasureTheory.measure_mono hsub) hMarkov
      _ = ENNReal.ofReal ((j0 : ℝ) ^ b)
            * (ENNReal.ofReal ((2 : ℝ) ^ (-(b / 2)))) ^ m := by
          rw [← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hJmpos _),
            short_ae_dyadic_ratio_bound _ _ m
              (Real.rpow_nonneg (by positivity) _)]
  have hC : ENNReal.ofReal ((j0 : ℝ) ^ b) ≠ ⊤ := ENNReal.ofReal_lt_top.ne
  have hBC := short_ae_BC_ae μ Bset (ENNReal.ofReal ((j0 : ℝ) ^ b))
    (ENNReal.ofReal ((2 : ℝ) ^ (-(b / 2)))) hC hρ1 hBbound
  refine ⟨hBC.1, hBC.2, ?_⟩
  filter_upwards [hBC.1] with ω hω
  rw [Filter.eventually_atTop] at hω
  obtain ⟨m0, hm0⟩ := hω
  exact ⟨2 ^ m0, fun J hJ => short_ae_dyadic_to_full (fun n => Z n ω) b m0 J hb
    (fun n => hZnn n ω) (hmono ω) hJ (fun m hm => by
      have hnot : ω ∉ Bset m := hm0 m hm
      rw [hBchar m ω] at hnot
      show (b / 2) * Real.log ((((2 ^ m : ℕ))) : ℝ) ≤ (fun n => Z n ω) (2 ^ m)
      exact not_lt.mp hnot)⟩

end WindowShortAe
