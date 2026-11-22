import Mathlib
import EpiFormal.Axioms

/-!
# 代数无关条件桥：e 与 π 代数无关 ⇒ e±π、e·π、e/π 全超越

把"破局缺的那一块"isolated 成一句最干净的假设：**e 与 π 在 ℚ 上代数无关**
（这正是 Schanuel 猜想对 {1, iπ} 所给出的结论）。在此假设下，
四个初等组合 e+π、e−π、e·π、e/π 全部超越。

比库里 `Elementary.at_least_one_transcendental`（仅"至少一个超越"）强得多：
和/差/积/商一次性全部拿下，代价是假设升级为代数无关
（本质上等价于 Schanuel 单实例的未证命题）。

## 诚实边界
* 不证明 e 与 π 代数无关——那是未解决的。
* 全部定理是条件性的，前提 `AlgebraicIndependent ℚ ![exp 1, π]`。
* 不引入新公理；审计应仅含 propext / Classical.choice / Quot.sound，无 sorryAx。

## 证明思路
若组合 c 代数，取零化多项式 m（m≠0, m(c)=0）。
和/差/积：代入 T↦(X₀±X₁ / X₀·X₁) 得二元 P，P(e,π)=0；
P≠0 因代入映射有左逆（在 (X,0) 或 (X,1) 处求值归约为单变量恒等）。
商：齐次化 homogenize m n 在 (e,π) 处 = πⁿ·m(e/π)=0 且非零。
均由代数无关（aeval 单射）矛盾。
-/

open Real MvPolynomial Polynomial

namespace EpiFormal

/-- 求值复合：`aeval x (aeval q m) = aeval (aeval x q) m`（任意 ℚ-代数目标）。
    两边均为 ℚ[X]→ₐ[ℚ] A 同态，在 X 上取值相同，由 algHom_ext 相等。 -/
private lemma aeval_aeval_comp {A : Type*} [CommRing A] [Algebra ℚ A]
    (x : Fin 2 → A) (q : MvPolynomial (Fin 2) ℚ) (m : ℚ[X]) :
    MvPolynomial.aeval x (Polynomial.aeval q m)
      = Polynomial.aeval (MvPolynomial.aeval x q) m := by
  have hext : (MvPolynomial.aeval x).comp (Polynomial.aeval q)
      = Polynomial.aeval (MvPolynomial.aeval x q) := by
    apply Polynomial.algHom_ext
    simp
  exact congrArg (fun f : ℚ[X] →ₐ[ℚ] A => f m) hext

/-- 单变量代入 `T ↦ X₀+X₁` 的单射性：左逆为映到 ℚ[X]，X₀↦X, X₁↦0。 -/
private lemma aeval_X0_add_X1_injective :
    Function.Injective (Polynomial.aeval (R := ℚ)
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ)) := by
  intro m₁ m₂ h
  have := congrArg (MvPolynomial.aeval
    (![Polynomial.X, 0] : Fin 2 → ℚ[X])) h
  simp only [aeval_aeval_comp, MvPolynomial.aeval_X, map_add,
    Matrix.cons_val_zero, Matrix.cons_val_one, add_zero,
    Polynomial.aeval_X_left_apply] at this
  exact this

/-- 单变量代入 `T ↦ X₀−X₁` 的单射性：左逆为映到 ℚ[X]，X₀↦X, X₁↦0。 -/
private lemma aeval_X0_sub_X1_injective :
    Function.Injective (Polynomial.aeval (R := ℚ)
      (MvPolynomial.X 0 - MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ)) := by
  intro m₁ m₂ h
  have := congrArg (MvPolynomial.aeval
    (![Polynomial.X, 0] : Fin 2 → ℚ[X])) h
  simp only [aeval_aeval_comp, MvPolynomial.aeval_X, map_sub,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero,
    Polynomial.aeval_X_left_apply] at this
  exact this

/-- 单变量代入 `T ↦ X₀·X₁` 的单射性：左逆为映到 ℚ[X]，X₀↦X, X₁↦1。 -/
private lemma aeval_X0_mul_X1_injective :
    Function.Injective (Polynomial.aeval (R := ℚ)
      (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ)) := by
  intro m₁ m₂ h
  have := congrArg (MvPolynomial.aeval
    (![Polynomial.X, 1] : Fin 2 → ℚ[X])) h
  simp only [aeval_aeval_comp, MvPolynomial.aeval_X, map_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
    Polynomial.aeval_X_left_apply] at this
  exact this

/-- 统一引理：若单变量代入 q 的映射单射，则 aeval ![e,π] q 超越。 -/
private lemma transcendental_aeval_of_injective
    (h : AlgebraicIndependent ℚ ![exp 1, π])
    (q : MvPolynomial (Fin 2) ℚ)
    (hq : Function.Injective (Polynomial.aeval q :
      ℚ[X] →ₐ[ℚ] MvPolynomial (Fin 2) ℚ)) :
    Transcendental ℚ (MvPolynomial.aeval ![exp 1, π] q) := by
  rw [transcendental_iff]
  intro m hm
  have hP : MvPolynomial.aeval ![exp 1, π] (Polynomial.aeval q m) = 0 := by
    rw [aeval_aeval_comp]; exact hm
  have hP0 : Polynomial.aeval q m = 0 := h.eq_zero_of_aeval_eq_zero _ hP
  exact hq (by simpa using hP0)

/-- 条件定理：e 与 π 代数无关 ⇒ e+π 超越。 -/
theorem transcendental_add_of_algebraicIndependent
    (h : AlgebraicIndependent ℚ ![exp 1, π]) :
    Transcendental ℚ (exp 1 + π) := by
  have := transcendental_aeval_of_injective h
    (MvPolynomial.X 0 + MvPolynomial.X 1) aeval_X0_add_X1_injective
  simpa [map_add, MvPolynomial.aeval_X] using this

/-- 条件定理：e 与 π 代数无关 ⇒ e−π 超越。 -/
theorem transcendental_sub_of_algebraicIndependent
    (h : AlgebraicIndependent ℚ ![exp 1, π]) :
    Transcendental ℚ (exp 1 - π) := by
  have := transcendental_aeval_of_injective h
    (MvPolynomial.X 0 - MvPolynomial.X 1) aeval_X0_sub_X1_injective
  simpa [map_sub, MvPolynomial.aeval_X] using this

/-- 条件定理：e 与 π 代数无关 ⇒ e·π 超越。 -/
theorem transcendental_mul_of_algebraicIndependent
    (h : AlgebraicIndependent ℚ ![exp 1, π]) :
    Transcendental ℚ (exp 1 * π) := by
  have := transcendental_aeval_of_injective h
    (MvPolynomial.X 0 * MvPolynomial.X 1) aeval_X0_mul_X1_injective
  simpa [map_mul, MvPolynomial.aeval_X] using this

/-- 条件定理：e 与 π 代数无关 ⇒ e/π 超越（齐次化路线）。 -/
theorem transcendental_div_of_algebraicIndependent
    (h : AlgebraicIndependent ℚ ![exp 1, π]) :
    Transcendental ℚ (exp 1 / π) := by
  rw [transcendental_iff]
  intro m hm
  set n := m.natDegree
  -- 把 m 映到 ℝ[X]，其齐次化在 (e,π) 处 = πⁿ · m(e/π) = 0
  set p := m.map (algebraMap ℚ ℝ) with hpdef
  have hpeval : p.eval (exp 1 / π) = 0 := by
    have := hm
    rw [Polynomial.aeval_def] at this
    rw [hpdef, Polynomial.eval_map]
    exact this
  have hmap : MvPolynomial.eval ![exp 1, π] (p.homogenize n)
      = p.eval (exp 1 / π) * π ^ n :=
    Polynomial.eval_homogenize (by rw [hpdef]; exact natDegree_map_le) _ pi_ne_zero
  have hzero : MvPolynomial.eval ![exp 1, π] (p.homogenize n) = 0 := by
    rw [hmap, hpeval, zero_mul]
  -- p.homogenize n = map (algebraMap) (m.homogenize n)
  have hhom : p.homogenize n = MvPolynomial.map (algebraMap ℚ ℝ) (m.homogenize n) := by
    rw [hpdef, Polynomial.homogenize_map]
  -- eval (map f P) = eval₂ f · P；故 eval₂ (algebraMap) ![e,π] (m.homogenize n) = 0
  have hP : MvPolynomial.aeval ![exp 1, π] (m.homogenize n) = 0 := by
    rw [MvPolynomial.aeval_eq_eval₂Hom]
    have := hzero
    rw [hhom, MvPolynomial.eval_map] at this
    exact this
  have hP0 : m.homogenize n = 0 := h.eq_zero_of_aeval_eq_zero _ hP
  exact (Polynomial.homogenize_eq_zero_iff (le_rfl)).mp hP0

end EpiFormal