import Mathlib
import EpiFormal.Axioms

/-!
# T1 纯代数层：韦达恒等式与定理 2.2 的六组配对（M1/M2，全部已证）

公理审计：本文件定理仅依赖 Axioms.lean 的 e_transcendental / pi_transcendental
与 Lean 基础公理。抽象引理以变量 e p 陈述；具体定理使用常数 exp 1 与 π。
-/

open Real

/-- 韦达恒等式（M1）。 -/
theorem vieta_identity (e p : ℝ) : e^2 - (e + p) * e + e * p = 0 := by
  ring

/-- 二次根代数性：S、P 代数且 x²−Sx+P=0 ⇒ x 代数。
    路线（纯 ℝ 环运算 + 有理数乘，不引入子代数）：
    判别式 D=S²−4P 整；r=√D 整（r²=max D 0，of_pow）；S±r 整；
    由因式分解 (x−(S+r)/2)(x−(S−r)/2)=0 得 x=(S±r)/2=(½:ℚ)•(S±r)，
    用 IsIntegral.smul 得 x 整 ⇒ 代数。 -/
theorem quadratic_roots_algebraic (S P x : ℝ)
    (hS : IsAlgebraic ℚ S) (hP : IsAlgebraic ℚ P)
    (hx : x^2 - S * x + P = 0) : IsAlgebraic ℚ x := by
  have hSi : IsIntegral ℚ S := hS.isIntegral
  have hPi : IsIntegral ℚ P := hP.isIntegral
  have h4 : IsIntegral ℚ (4 : ℝ) := isIntegral_algebraMap
  have hDi : IsIntegral ℚ (S^2 - 4 * P) := by
    have := (hSi.mul hSi).sub (h4.mul hPi)
    simpa [pow_two] using this
  set D := S^2 - 4 * P with hDdef
  -- 实根 ⇒ 判别式非负：D = (S−2x)²（由 hx 线性组合）
  have hDsq : D = (S - 2 * x)^2 := by
    dsimp only [D]
    linear_combination -4 * hx
  have hDnonneg : 0 ≤ D := by rw [hDsq]; positivity
  set r := Real.sqrt D
  have hrD : r^2 = D := Real.sq_sqrt hDnonneg
  have hri : IsIntegral ℚ r := by
    have hi_r2 : IsIntegral ℚ (r^2) := by rw [hrD]; exact hDi
    exact IsIntegral.of_pow (by norm_num) hi_r2
  have hpr : IsIntegral ℚ (S + r) := hSi.add hri
  have hmr : IsIntegral ℚ (S - r) := hSi.sub hri
  -- 因式分解：(x−(S+r)/2)(x−(S−r)/2) = x²−Sx+P = 0
  have hfac : (x - (S + r) / 2) * (x - (S - r) / 2) = 0 := by
    have hprod : ((S + r) / 2) * ((S - r) / 2) = P := by
      have h1 : (S + r) * (S - r) = S^2 - r^2 := by ring
      have h2 : S^2 - r^2 = 4 * P := by rw [hrD, hDdef]; ring
      have h3 : ((S + r) / 2) * ((S - r) / 2) = ((S + r) * (S - r)) / 4 := by ring
      rw [h3, h1, h2]; ring
    have hsum : (S + r) / 2 + (S - r) / 2 = S := by ring
    nlinarith [hprod, hsum, hx]
  rcases mul_eq_zero.mp hfac with h | h
  · have hxr : x = (S + r) / 2 := by linarith [sub_eq_zero.mp h]
    have hsm : IsIntegral ℚ ((1 / 2 : ℚ) • (S + r)) := IsIntegral.smul (1 / 2 : ℚ) hpr
    have heq : (1 / 2 : ℚ) • (S + r) = (S + r) / 2 := by
      rw [Algebra.smul_def]
      have hc : algebraMap ℚ ℝ (1 / 2) = (1 : ℝ) / 2 := by
        rw [map_div₀, map_one]; norm_num
      rw [hc]; ring
    rw [hxr, ← heq]; exact hsm.isAlgebraic
  · have hxr : x = (S - r) / 2 := by linarith [sub_eq_zero.mp h]
    have hsm : IsIntegral ℚ ((1 / 2 : ℚ) • (S - r)) := IsIntegral.smul (1 / 2 : ℚ) hmr
    have heq : (1 / 2 : ℚ) • (S - r) = (S - r) / 2 := by
      rw [Algebra.smul_def]
      have hc : algebraMap ℚ ℝ (1 / 2) = (1 : ℝ) / 2 := by
        rw [map_div₀, map_one]; norm_num
      rw [hc]; ring
    rw [hxr, ← heq]; exact hsm.isAlgebraic

/-- 定理 2.1：e+π 与 eπ 至少一个超越。 -/
theorem at_least_one_transcendental :
    Transcendental ℚ (exp 1 + π) ∨ Transcendental ℚ (exp 1 * π) := by
  by_contra h
  push Not at h
  obtain ⟨hS, hP⟩ := h
  have hS' : IsAlgebraic ℚ (exp 1 + π) := by simpa [Transcendental] using hS
  have hP' : IsAlgebraic ℚ (exp 1 * π) := by simpa [Transcendental] using hP
  have he : IsAlgebraic ℚ (exp 1) :=
    quadratic_roots_algebraic (exp 1 + π) (exp 1 * π) (exp 1) hS' hP' (by ring)
  exact e_transcendental he

/-- 配对一：和与差不能同时有理。 -/
theorem pair_sum_diff (e p : ℝ) (he : Irrational e) :
    ¬ ∃ q r : ℚ, e + p = q ∧ e - p = r := by
  rintro ⟨q, r, hq, hr⟩
  have heq : e = ((q + r) / 2 : ℚ) := by
    have h1 : (q : ℝ) + (r : ℝ) = 2 * e := by
      rw [← hq, ← hr]; ring
    have h2 : (2 : ℝ) * e = ((q + r : ℚ) : ℝ) := by rw [← h1]; push_cast; ring
    have h3 : e = ((q + r : ℚ) : ℝ) / 2 := by
      apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
      rw [h2]; ring
    rw [h3]; push_cast; ring
  exact he ⟨(q + r) / 2, heq.symm⟩

/-- 配对二：和与积不能同时有理。 -/
theorem pair_sum_prod (e p : ℝ) (he : Transcendental ℚ e) :
    ¬ ∃ q r : ℚ, e + p = q ∧ e * p = r := by
  rintro ⟨q, r, hq, hr⟩
  have hroot : e^2 - (q : ℝ) * e + (r : ℝ) = 0 := by
    have : e^2 - (e + p) * e + e * p = 0 := by ring
    rw [hq, hr] at this; exact this
  exact he (quadratic_roots_algebraic (q : ℝ) (r : ℝ) e
    (isAlgebraic_algebraMap q) (isAlgebraic_algebraMap r) hroot)

/-- 配对三：差与积不能同时有理。 -/
theorem pair_diff_prod (e p : ℝ) (he : Transcendental ℚ e) :
    ¬ ∃ q r : ℚ, e - p = q ∧ e * p = r := by
  rintro ⟨q, r, hq, hr⟩
  have hroot : e^2 - (q : ℝ) * e + (-(r : ℝ)) = 0 := by
    have : e^2 - (e - p) * e - e * p = 0 := by ring
    rw [hq, hr] at this; ring_nf at this ⊢; exact this
  have halg : IsAlgebraic ℚ (-(r : ℝ)) := by
    have : IsAlgebraic ℚ ((-r : ℚ) : ℝ) := isAlgebraic_algebraMap (-r)
    simpa using this
  exact he (quadratic_roots_algebraic (q : ℝ) (-(r : ℝ)) e
    (isAlgebraic_algebraMap q) halg hroot)

/-- 配对四：和与商不能同时有理（正数情形）。 -/
theorem pair_sum_quot (e p : ℝ) (hp : Irrational p) (he0 : 0 < e) (hp0 : 0 < p) :
    ¬ ∃ q r : ℚ, e + p = q ∧ e / p = r := by
  rintro ⟨q, r, hq, hr⟩
  have hrpos : 0 < (r : ℝ) := by rw [← hr]; exact div_pos he0 hp0
  have heq : e = (r : ℝ) * p := by
    have h := hr
    field_simp at h
    linarith
  have hden : (r : ℝ) + 1 ≠ 0 := by linarith
  have hpi : p = (q : ℝ) / ((r : ℝ) + 1) := by
    rw [eq_div_iff_mul_eq hden]
    linarith [heq, hq]
  exact hp ⟨q / (r + 1), by rw [hpi]; push_cast; ring⟩

/-- 配对五：差与商不能同时有理（需 e≠p）。 -/
theorem pair_diff_quot (e p : ℝ) (hp : Irrational p) (hne : e ≠ p) (hp0 : p ≠ 0) :
    ¬ ∃ q r : ℚ, e - p = q ∧ e / p = r := by
  rintro ⟨q, r, hq, hr⟩
  have heq : e = (r : ℝ) * p := by
    have h := hr
    field_simp at h
    linarith
  have hrne : (r : ℝ) ≠ 1 := by
    intro h1
    exact hne (by rw [heq, h1, one_mul])
  have hden : (r : ℝ) - 1 ≠ 0 := by
    intro h; apply hrne; linarith
  have hpi : p = (q : ℝ) / ((r : ℝ) - 1) := by
    rw [eq_div_iff_mul_eq hden]
    linarith [heq, hq]
  exact hp ⟨q / (r - 1), by rw [hpi]; push_cast; ring⟩

/-- 配对六：积与商不能同时有理。 -/
theorem pair_prod_quot (e p : ℝ) (he : Transcendental ℚ e) (hp0 : p ≠ 0) :
    ¬ ∃ q r : ℚ, e * p = q ∧ e / p = r := by
  rintro ⟨q, r, hq, hr⟩
  have he2 : e^2 = (q : ℝ) * (r : ℝ) := by
    have h1 : (e * p) * (e / p) = (q : ℝ) * (r : ℝ) := by rw [hq, hr]
    have h2 : (e * p) * (e / p) = e^2 := by field_simp
    rw [h2] at h1; exact h1
  have hroot : e^2 - (q * r : ℚ) = 0 := by
    rw [he2]; push_cast; ring
  have halg2 : IsAlgebraic ℚ (e^2) := by
    have hcast : (q : ℝ) * (r : ℝ) = ((q * r : ℚ) : ℝ) := by push_cast; ring
    rw [he2, hcast]
    exact isAlgebraic_algebraMap (q * r)
  exact he (IsAlgebraic.of_pow (by norm_num : 0 < 2) halg2)

/-- 定理 2.2：四个组合数至多一个有理。 -/
theorem four_numbers_at_most_one_rational :
    ¬ ∃ a b : ℚ, (exp 1 + π = a ∧ exp 1 - π = b) ∨
               (exp 1 + π = a ∧ exp 1 * π = b) ∨
               (exp 1 - π = a ∧ exp 1 * π = b) ∨
               (exp 1 + π = a ∧ exp 1 / π = b) ∨
               (exp 1 - π = a ∧ exp 1 / π = b) ∨
               (exp 1 * π = a ∧ exp 1 / π = b) := by
  have heI : Irrational (exp 1) := e_irrational
  have hπI : Irrational π := pi_irrational
  have hpos_e : 0 < exp 1 := exp_pos 1
  have hpos_π : 0 < π := pi_pos
  have hne : exp 1 ≠ π := ne_of_lt (lt_trans exp_one_lt_three pi_gt_three)
  rintro ⟨a, b, h | h | h | h | h | h⟩
  · exact pair_sum_diff (exp 1) π heI ⟨a, b, h.1, h.2⟩
  · exact pair_sum_prod (exp 1) π e_transcendental ⟨a, b, h.1, h.2⟩
  · exact pair_diff_prod (exp 1) π e_transcendental ⟨a, b, h.1, h.2⟩
  · exact pair_sum_quot (exp 1) π hπI hpos_e hpos_π ⟨a, b, h.1, h.2⟩
  · exact pair_diff_quot (exp 1) π hπI hne hpos_π.ne' ⟨a, b, h.1, h.2⟩
  · exact pair_prod_quot (exp 1) π e_transcendental hpos_π.ne' ⟨a, b, h.1, h.2⟩
