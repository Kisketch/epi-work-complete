import Mathlib

/-!
# 黄金比轨道范数奇偶刚性与定理 B1 核心代数界

本模块形式化论文一 §8 的以下结果（全部无条件，仅依赖 Lean 基础公理，零 `sorry`）：
1. **引理 1**（Möbius 误差恒等式，Bugeaud 2014 式 (3.4)）：`mobius_error_identity`。
2. **引理 2**（$\mathbb{Z}[\varphi]$ 范数奇偶刚性，`lem:norm-parity-rigidity`）：
   - `zphiNorm_even_iff`：$-p^2 + pq + q^2$ 为偶当且仅当 $2\mid p \land 2\mid q$；
   - `m0_even`：对 $|ad-bc|=1$，有理部分 $m_0$ 必为偶数；
   - `norm_parity_rigidity_identity`：$h(\eta)\frac{|2-\eta|\,|\eta'|}{2} = \left|\frac{2m}{\sqrt{5}}-1\right|$；
   - `spectral_gap_constants`：$0 < 1 - \frac{2}{\sqrt{5}} < \frac{4}{\sqrt{5}} - 1$，且 $m \ne 1 \implies \left|\frac{2m}{\sqrt{5}}-1\right| \ge \frac{4}{\sqrt{5}} - 1$；
   - `norm_parity_rigidity_eq_iff` 与 `norm_parity_rigidity_ge_second`：取到 $1 - \frac{2}{\sqrt{5}}$ 当且仅当
     $\eta \in \{\varphi, \varphi+1\}$，其余一律 $\ge \frac{4}{\sqrt{5}} - 1$。
3. **定理 B1**（`thm:golden-exact-second`）的核心代数界：
   - `zphiNorm_not_two_three_four` 与 `height_dichotomy`：$|N(c\varphi+d)| \notin \{2,3,4\}$，故
     $h(\eta) = \frac{2}{\sqrt{5}}$ 或 $h(\eta) \ge 2\sqrt{5}$；
   - `case1_lower_bound`：情形 1 的一致下界；
   - `case2_sub1_quadratic_ge`、`case2_sub2_quadratic_ge`、`case2_sub3_quadratic_ge`：
     情形 2 三个子情形的凹二次函数精确下界；
   - `second_limit_point_attained_value` 与 `b2_control_model_constant`：
     第二极限点 $\frac{4}{\sqrt{5}}-1$ 与 $11/2-e$ 上界常数 $\frac{9}{4\sqrt{5}}-1$ 的精确代数恒等式。

公理审计：本模块仅依赖 Lean 基础公理 `[propext, Classical.choice, Quot.sound]`，不依赖任何额外公理。
-/

namespace GoldenOrbitRigidity

open Real

/-- 黄金比 $\varphi = \frac{1+\sqrt{5}}{2}$。 -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- 共轭 $\varphi' = \frac{1-\sqrt{5}}{2}$。 -/
noncomputable def φ' : ℝ := (1 - Real.sqrt 5) / 2

/-- $\mathbb{Z}[\varphi]$ 上元素 $p\varphi + q$ 的域范数 $N(p\varphi+q) = -p^2 + pq + q^2$。 -/
def zphiNorm (p q : ℤ) : ℤ := -p ^ 2 + p * q + q ^ 2

/-- 整数矩阵 $(a,b;c,d)$ 诱导的 Möbius 变换。 -/
noncomputable def mobius (a b c d : ℤ) (x : ℝ) : ℝ :=
  ((a : ℝ) * x + (b : ℝ)) / ((c : ℝ) * x + (d : ℝ))

/-- 轨道点 $\eta = \frac{a\varphi+b}{c\varphi+d}$。 -/
noncomputable def orbitPt (a b c d : ℤ) : ℝ := mobius a b c d φ

/-- 轨道点共轭 $\eta' = \frac{a\varphi'+b}{c\varphi'+d}$。 -/
noncomputable def orbitPtConj (a b c d : ℤ) : ℝ := mobius a b c d φ'

/-- 二次轨道点的高度 $h(\beta) = \frac{2}{|\beta - \beta'|}$。 -/
noncomputable def orbitHeight (x x' : ℝ) : ℝ := 2 / |x - x'|

/-- 引理 2 中的有理部分 $m_0$。 -/
def m0 (a b c d : ℤ) : ℤ :=
  -2 * a * c + a ^ 2 + 2 * b * d - b ^ 2 + b * c + a * d - a * b

/-! ### 基本代数恒等式 -/

lemma sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
  Real.sqrt_pos.mpr (by norm_num)

lemma sqrt5_sq : (Real.sqrt 5) ^ 2 = 5 :=
  Real.sq_sqrt (by norm_num)

lemma sqrt5_bounds : (2 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < (5 : ℝ) / 2 := by
  constructor
  · rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [show (5 : ℝ) / 2 = Real.sqrt (25 / 4) by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma phi_add_phi' : φ + φ' = 1 := by
  unfold φ φ'; ring

lemma phi_sub_phi' : φ - φ' = Real.sqrt 5 := by
  unfold φ φ'; ring

lemma phi_mul_phi' : φ * φ' = -1 := by
  unfold φ φ'
  linear_combination -(1 / 4 : ℝ) * sqrt5_sq

lemma phi_sq : φ ^ 2 = φ + 1 := by
  unfold φ
  linear_combination (1 / 4 : ℝ) * sqrt5_sq

lemma phi'_sq : φ' ^ 2 = φ' + 1 := by
  unfold φ'
  linear_combination (1 / 4 : ℝ) * sqrt5_sq

lemma zphi_mul_conj (p q : ℤ) :
    ((p : ℝ) * φ + (q : ℝ)) * ((p : ℝ) * φ' + (q : ℝ)) = (zphiNorm p q : ℝ) := by
  unfold zphiNorm
  push_cast
  have h1 := phi_add_phi'
  have h2 := phi_mul_phi'
  calc ((p : ℝ) * φ + (q : ℝ)) * ((p : ℝ) * φ' + (q : ℝ))
      = (p : ℝ) ^ 2 * (φ * φ') + (p : ℝ) * (q : ℝ) * (φ + φ') + (q : ℝ) ^ 2 := by ring
    _ = -((p : ℝ) ^ 2) + (p : ℝ) * (q : ℝ) + (q : ℝ) ^ 2 := by rw [h1, h2]; ring

/-- $\sqrt{5}$ 无理，故 $(p,q)\ne(0,0)$ 时 $N(p\varphi+q)\ne 0$。 -/
lemma zphiNorm_ne_zero {p q : ℤ} (h : p ≠ 0 ∨ q ≠ 0) : zphiNorm p q ≠ 0 := by
  intro h0
  have hsq : (2 * q + p) ^ 2 = 5 * p ^ 2 := by
    unfold zphiNorm at h0
    linarith
  have hp : p ≠ 0 := by
    intro hp0
    subst hp0
    have : q = 0 := by nlinarith
    exact h.elim (fun h1 => h1 rfl) (fun h2 => h2 this)
  have hirr : Irrational (Real.sqrt 5) := Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 5)
  have hreal : ((2 * q + p : ℤ) : ℝ) ^ 2 = 5 * ((p : ℤ) : ℝ) ^ 2 := by
    exact_mod_cast hsq
  have hpR : (p : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hp
  have hdiv : ((2 * q + p : ℤ) : ℝ) / (p : ℝ) = Real.sqrt 5 ∨
      ((2 * q + p : ℤ) : ℝ) / (p : ℝ) = -Real.sqrt 5 := by
    have hdiff : (((2 * q + p : ℤ) : ℝ) / (p : ℝ) - Real.sqrt 5) *
        (((2 * q + p : ℤ) : ℝ) / (p : ℝ) + Real.sqrt 5) = 0 := by
      have h5 := sqrt5_sq
      field_simp [hpR]
      linear_combination hreal - (p : ℝ) ^ 2 * h5
    rcases mul_eq_zero.mp hdiff with h1 | h2
    · left; linarith
    · right; linarith
  rcases hdiv with hpos | hneg
  · exact hirr ⟨((2 * q + p : ℤ) : ℚ) / (p : ℚ), by push_cast at hpos ⊢; exact hpos⟩
  · exact hirr ⟨-(((2 * q + p : ℤ) : ℚ) / (p : ℚ)), by push_cast at hneg ⊢; linarith⟩

lemma linear_phi_ne_zero {p q : ℤ} (h : p ≠ 0 ∨ q ≠ 0) :
    (p : ℝ) * φ + (q : ℝ) ≠ 0 ∧ (p : ℝ) * φ' + (q : ℝ) ≠ 0 := by
  have hN : (zphiNorm p q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (zphiNorm_ne_zero h)
  rw [← zphi_mul_conj p q] at hN
  exact mul_ne_zero_iff.mp hN

lemma cd_ne_zero_of_det {a b c d : ℤ} (hdet : |a * d - b * c| = 1) : c ≠ 0 ∨ d ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨hc, hd⟩
  subst hc; subst hd
  simp at hdet

lemma ab_ne_zero_of_det {a b c d : ℤ} (hdet : |a * d - b * c| = 1) : a ≠ 0 ∨ b ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨ha, hb⟩
  subst ha; subst hb
  simp at hdet

/-! ### 引理 1：Möbius 误差恒等式（Bugeaud 2014, (3.4)） -/

/-- Möbius 变换差值恒等式。 -/
lemma mobius_sub (a b c d : ℤ) {x y : ℝ}
    (hx : (c : ℝ) * x + (d : ℝ) ≠ 0) (hy : (c : ℝ) * y + (d : ℝ) ≠ 0) :
    mobius a b c d x - mobius a b c d y =
      ((a * d - b * c : ℤ) : ℝ) * (x - y) /
        (((c : ℝ) * x + (d : ℝ)) * ((c : ℝ) * y + (d : ℝ))) := by
  unfold mobius
  rw [div_sub_div _ _ hx hy]
  push_cast
  congr 1
  ring

/-- 引理 1（Bugeaud 2014 式 (3.4)）：Möbius 误差精确恒等式。 -/
theorem mobius_error_identity (p1 p0 q1 q0 : ℤ) {T η η' : ℝ}
    (hdet : |p1 * q0 - p0 * q1| = 1)
    (hq1 : (0 : ℝ) < (q1 : ℝ))
    (hTz : (0 : ℝ) < T + (q0 : ℝ) / (q1 : ℝ))
    (hη : (q1 : ℝ) * η + (q0 : ℝ) ≠ 0)
    (hη' : (q1 : ℝ) * η' + (q0 : ℝ) ≠ 0)
    (hdiff : η ≠ η') :
    orbitHeight (mobius p1 p0 q1 q0 η) (mobius p1 p0 q1 q0 η') *
      |mobius p1 p0 q1 q0 T - mobius p1 p0 q1 q0 η| =
    orbitHeight η η' *
      (|T - η| * |η' + (q0 : ℝ) / (q1 : ℝ)| / (T + (q0 : ℝ) / (q1 : ℝ))) := by
  have hq1_ne : (q1 : ℝ) ≠ 0 := ne_of_gt hq1
  have hT_pos : (0 : ℝ) < (q1 : ℝ) * T + (q0 : ℝ) := by
    have : (q1 : ℝ) * T + (q0 : ℝ) = (q1 : ℝ) * (T + (q0 : ℝ) / (q1 : ℝ)) := by
      field_simp [hq1_ne]
    rw [this]
    exact mul_pos hq1 hTz
  have hT_ne : (q1 : ℝ) * T + (q0 : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hdetR : |((p1 * q0 - p0 * q1 : ℤ) : ℝ)| = 1 := by exact_mod_cast hdet
  have hsub1 := mobius_sub p1 p0 q1 q0 hT_ne hη
  have hsub2 := mobius_sub p1 p0 q1 q0 hη hη'
  have habs1 : |mobius p1 p0 q1 q0 T - mobius p1 p0 q1 q0 η| =
      |T - η| / (|(q1 : ℝ) * T + (q0 : ℝ)| * |(q1 : ℝ) * η + (q0 : ℝ)|) := by
    rw [hsub1, abs_div, abs_mul, abs_mul, hdetR, one_mul]
  have habs2 : |mobius p1 p0 q1 q0 η - mobius p1 p0 q1 q0 η'| =
      |η - η'| / (|(q1 : ℝ) * η + (q0 : ℝ)| * |(q1 : ℝ) * η' + (q0 : ℝ)|) := by
    rw [hsub2, abs_div, abs_mul, abs_mul, hdetR, one_mul]
  unfold orbitHeight
  rw [habs1, habs2]
  have hη_abs_ne : |(q1 : ℝ) * η + (q0 : ℝ)| ≠ 0 := abs_ne_zero.mpr hη
  have hη'_abs_ne : |(q1 : ℝ) * η' + (q0 : ℝ)| ≠ 0 := abs_ne_zero.mpr hη'
  have hdiff_ne : |η - η'| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hdiff)
  have hT_abs : |(q1 : ℝ) * T + (q0 : ℝ)| = (q1 : ℝ) * (T + (q0 : ℝ) / (q1 : ℝ)) := by
    rw [abs_of_pos hT_pos]
    field_simp [hq1_ne]
  have hη'_abs : |(q1 : ℝ) * η' + (q0 : ℝ)| = (q1 : ℝ) * |η' + (q0 : ℝ) / (q1 : ℝ)| := by
    have : (q1 : ℝ) * η' + (q0 : ℝ) = (q1 : ℝ) * (η' + (q0 : ℝ) / (q1 : ℝ)) := by
      field_simp [hq1_ne]
    rw [this, abs_mul, abs_of_pos hq1]
  rw [hT_abs, hη'_abs]
  have hTz_ne : T + (q0 : ℝ) / (q1 : ℝ) ≠ 0 := ne_of_gt hTz
  set A := |(q1 : ℝ) * η + (q0 : ℝ)|
  set B := |η' + (q0 : ℝ) / (q1 : ℝ)|
  set C := T + (q0 : ℝ) / (q1 : ℝ)
  set D := |η - η'|
  set E := |T - η|
  have hA : A ≠ 0 := hη_abs_ne
  have hC : C ≠ 0 := hTz_ne
  have hD : D ≠ 0 := hdiff_ne
  have hB : B ≠ 0 := by
    intro h0
    have : |(q1 : ℝ) * η' + (q0 : ℝ)| = 0 := by rw [hη'_abs, h0, mul_zero]
    exact hη'_abs_ne this
  field_simp [hq1_ne, hA, hB, hC, hD]

/-! ### 轨道点高度公式 -/

lemma orbitHeight_eq {a b c d : ℤ} (hdet : |a * d - b * c| = 1) :
    orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) =
      2 * |(zphiNorm c d : ℝ)| / Real.sqrt 5 := by
  have hcd := linear_phi_ne_zero (cd_ne_zero_of_det hdet)
  have hsub := mobius_sub a b c d hcd.1 hcd.2
  have hdetR : |((a * d - b * c : ℤ) : ℝ)| = 1 := by exact_mod_cast hdet
  unfold orbitHeight orbitPt orbitPtConj
  rw [hsub, phi_sub_phi', abs_div, abs_mul, hdetR, one_mul, abs_of_pos sqrt5_pos,
    zphi_mul_conj c d]
  have hN_ne : |(zphiNorm c d : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Int.cast_ne_zero.mpr (zphiNorm_ne_zero (cd_ne_zero_of_det hdet)))
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt sqrt5_pos
  field_simp [hN_ne, h5_ne]

/-! ### 引理 2：$\mathbb{Z}[\varphi]$ 范数奇偶刚性 -/

/-- $\mathbb{Z}[\varphi]$ 范数奇偶判据：$-p^2 + pq + q^2$ 为偶当且仅当 $p, q$ 同为偶。 -/
theorem zphiNorm_even_iff (p q : ℤ) : Even (zphiNorm p q) ↔ Even p ∧ Even q := by
  unfold zphiNorm
  constructor
  · rintro ⟨k, hk⟩
    have hp_decomp : p = 2 * (p / 2) + p % 2 := by omega
    have hq_decomp : q = 2 * (q / 2) + q % 2 := by omega
    set rp := p % 2
    set rq := q % 2
    set kp := p / 2
    set kq := q / 2
    have hrp : rp = 0 ∨ rp = 1 := by omega
    have hrq : rq = 0 ∨ rq = 1 := by omega
    have hexp : -p ^ 2 + p * q + q ^ 2 =
        2 * (-2 * kp ^ 2 - 2 * kp * rp + 2 * kp * kq + kp * rq + rp * kq + 2 * kq ^ 2 + 2 * kq * rq) +
          (-rp ^ 2 + rp * rq + rq ^ 2) := by
      rw [hp_decomp, hq_decomp]; ring
    rcases hrp with hp0 | hp1 <;> rcases hrq with hq0 | hq1
    · exact ⟨⟨kp, by omega⟩, ⟨kq, by omega⟩⟩
    · rw [hp0, hq1] at hexp; omega
    · rw [hp1, hq0] at hexp; omega
    · rw [hp1, hq1] at hexp; omega
  · rintro ⟨⟨p', rfl⟩, ⟨q', rfl⟩⟩
    exact ⟨-2 * p' ^ 2 + 2 * p' * q' + 2 * q' ^ 2, by ring⟩

/-- $\alpha \gamma' = m_0 - (ad - bc)\sqrt{5}$ 的精确展开。 -/
lemma alpha_mul_gammaConj (a b c d : ℤ) :
    (((2 * c - a : ℤ) : ℝ) * φ + ((2 * d - b : ℤ) : ℝ)) *
      ((a : ℝ) * φ' + (b : ℝ)) =
    (m0 a b c d : ℝ) - ((a * d - b * c : ℤ) : ℝ) * Real.sqrt 5 := by
  unfold m0 φ φ'
  push_cast
  linear_combination (-((2 * (c : ℝ) - (a : ℝ)) * (a : ℝ)) / 4) * sqrt5_sq

/-- 范数恒等式：$m_0^2 - 5(ad-bc)^2 = N((2c-a)\varphi+(2d-b)) \cdot N(a\varphi+b)$。 -/
lemma m0_norm_identity (a b c d : ℤ) :
    (m0 a b c d) ^ 2 - 5 * (a * d - b * c) ^ 2 =
      zphiNorm (2 * c - a) (2 * d - b) * zphiNorm a b := by
  unfold m0 zphiNorm
  ring

/-- 行列式为 $\pm 1$ 时，$m_0$ 必为偶数。 -/
theorem m0_even {a b c d : ℤ} (hdet : |a * d - b * c| = 1) : Even (m0 a b c d) := by
  have hdet_sq : (a * d - b * c) ^ 2 = 1 := by
    have : |a * d - b * c| ^ 2 = 1 ^ 2 := by rw [hdet]
    simpa [sq_abs] using this
  have hnot_ab : ¬ (Even a ∧ Even b) := by
    rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩
    have hmul : (a' + a') * d - (b' + b') * c = 2 * (a' * d - b' * c) := by ring
    rw [hmul] at hdet
    have : (2 * (a' * d - b' * c)) = 1 ∨ (2 * (a' * d - b' * c)) = -1 :=
      (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
    omega
  have hnot_alpha : ¬ (Even (2 * c - a) ∧ Even (2 * d - b)) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    apply hnot_ab
    exact ⟨⟨c - x, by omega⟩, ⟨d - y, by omega⟩⟩
  have hN1 : ¬ Even (zphiNorm a b) := by rwa [zphiNorm_even_iff]
  have hN2 : ¬ Even (zphiNorm (2 * c - a) (2 * d - b)) := by rwa [zphiNorm_even_iff]
  have hN1_odd : Odd (zphiNorm a b) := Int.not_even_iff_odd.mp hN1
  have hN2_odd : Odd (zphiNorm (2 * c - a) (2 * d - b)) := Int.not_even_iff_odd.mp hN2
  have hprod_odd : Odd (zphiNorm (2 * c - a) (2 * d - b) * zphiNorm a b) := hN2_odd.mul hN1_odd
  have hnorm := m0_norm_identity a b c d
  rw [hdet_sq, mul_one] at hnorm
  rw [← hnorm] at hprod_odd
  rcases hprod_odd with ⟨t, ht⟩
  set M := m0 a b c d
  have hM_decomp : M = 2 * (M / 2) + M % 2 := by omega
  set r := M % 2
  set q := M / 2
  have hr : r = 0 ∨ r = 1 := by omega
  have hsq : M ^ 2 = 2 * (2 * q ^ 2 + 2 * q * r) + r ^ 2 := by rw [hM_decomp]; ring
  rcases hr with hr0 | hr1
  · exact ⟨q, by omega⟩
  · rw [hr1] at hsq; omega

/-- 核心乘积公式：$h(\eta)\frac{|2-\eta|\,|\eta'|}{2} = \frac{|\alpha\gamma'|}{\sqrt{5}}$。 -/
lemma rigidity_lhs_eq {a b c d : ℤ} (hdet : |a * d - b * c| = 1) :
    orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
      (|2 - orbitPt a b c d| * |orbitPtConj a b c d| / 2) =
    |(m0 a b c d : ℝ) - ((a * d - b * c : ℤ) : ℝ) * Real.sqrt 5| / Real.sqrt 5 := by
  have hcd := linear_phi_ne_zero (cd_ne_zero_of_det hdet)
  have h2sub : 2 - orbitPt a b c d =
      (((2 * c - a : ℤ) : ℝ) * φ + ((2 * d - b : ℤ) : ℝ)) / ((c : ℝ) * φ + (d : ℝ)) := by
    unfold orbitPt mobius
    rw [sub_div' hcd.1]
    push_cast
    congr 1; ring
  rw [orbitHeight_eq hdet, h2sub]
  unfold orbitPtConj mobius
  rw [abs_div, abs_div, ← zphi_mul_conj c d, abs_mul]
  have h1_ne : |(c : ℝ) * φ + (d : ℝ)| ≠ 0 := abs_ne_zero.mpr hcd.1
  have h2_ne : |(c : ℝ) * φ' + (d : ℝ)| ≠ 0 := abs_ne_zero.mpr hcd.2
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt sqrt5_pos
  have hprod := alpha_mul_gammaConj a b c d
  calc 2 * (|(c : ℝ) * φ + (d : ℝ)| * |(c : ℝ) * φ' + (d : ℝ)|) / Real.sqrt 5 *
        (|((2 * c - a : ℤ) : ℝ) * φ + ((2 * d - b : ℤ) : ℝ)| / |(c : ℝ) * φ + (d : ℝ)| *
          (|(a : ℝ) * φ' + (b : ℝ)| / |(c : ℝ) * φ' + (d : ℝ)|) / 2)
      = |((2 * c - a : ℤ) : ℝ) * φ + ((2 * d - b : ℤ) : ℝ)| * |(a : ℝ) * φ' + (b : ℝ)| /
          Real.sqrt 5 := by field_simp [h1_ne, h2_ne, h5_ne]
    _ = |(((2 * c - a : ℤ) : ℝ) * φ + ((2 * d - b : ℤ) : ℝ)) * ((a : ℝ) * φ' + (b : ℝ))| /
          Real.sqrt 5 := by rw [abs_mul]
    _ = |(m0 a b c d : ℝ) - ((a * d - b * c : ℤ) : ℝ) * Real.sqrt 5| / Real.sqrt 5 := by
          rw [hprod]

/-- 引理 2 第一部分：存在整数 $m$ 使 $h(\eta)\frac{|2-\eta|\,|\eta'|}{2} = \left|\frac{2m}{\sqrt{5}}-1\right|$。 -/
theorem norm_parity_rigidity_identity {a b c d : ℤ} (hdet : |a * d - b * c| = 1) :
    ∃ m : ℤ, orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
      (|2 - orbitPt a b c d| * |orbitPtConj a b c d| / 2) =
      |2 * (m : ℝ) / Real.sqrt 5 - 1| := by
  rcases m0_even hdet with ⟨k0, hk0⟩
  have hε : a * d - b * c = 1 ∨ a * d - b * c = -1 :=
    (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
  refine ⟨(a * d - b * c) * k0, ?_⟩
  rw [rigidity_lhs_eq hdet]
  have hm0R : (m0 a b c d : ℝ) = 2 * (k0 : ℝ) := by
    exact_mod_cast (show m0 a b c d = 2 * k0 by omega)
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  rw [hm0R]
  rcases hε with h1 | hm1
  · rw [h1]
    push_cast
    rw [one_mul, one_mul, show |2 * (k0 : ℝ) - Real.sqrt 5| / Real.sqrt 5 =
        |(2 * (k0 : ℝ) - Real.sqrt 5) / Real.sqrt 5| by rw [abs_div, abs_of_pos h5_pos]]
    congr 1; field_simp [h5_ne]
  · rw [hm1]
    push_cast
    rw [show |2 * (k0 : ℝ) - (-1 : ℝ) * Real.sqrt 5| / Real.sqrt 5 =
        |(2 * (k0 : ℝ) - (-1 : ℝ) * Real.sqrt 5) / Real.sqrt 5| by rw [abs_div, abs_of_pos h5_pos]]
    rw [← abs_neg (2 * (-1 * (k0 : ℝ)) / Real.sqrt 5 - 1)]
    congr 1; field_simp [h5_ne]; ring

/-- 谱隙常数分离：$0 < 1 - \frac{2}{\sqrt{5}} < \frac{4}{\sqrt{5}} - 1$，且对任意 $m \ne 1$ 有
    $\left|\frac{2m}{\sqrt{5}}-1\right| \ge \frac{4}{\sqrt{5}} - 1$。 -/
theorem spectral_gap_constants :
    (0 : ℝ) < 1 - 2 / Real.sqrt 5 ∧
    1 - 2 / Real.sqrt 5 < 4 / Real.sqrt 5 - 1 ∧
    ∀ m : ℤ, m ≠ 1 → 4 / Real.sqrt 5 - 1 ≤ |2 * (m : ℝ) / Real.sqrt 5 - 1| := by
  have h5_pos := sqrt5_pos
  have h5_gt2 : (2 : ℝ) < Real.sqrt 5 := sqrt5_bounds.1
  have h5_lt3 : Real.sqrt 5 < 3 := lt_trans sqrt5_bounds.2 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_pos, div_lt_one h5_pos]; exact h5_gt2
  · have h6 : (2 : ℝ) < 6 / Real.sqrt 5 := by
      rw [lt_div_iff₀ h5_pos]; linarith
    have hsplit : (6 : ℝ) / Real.sqrt 5 = 4 / Real.sqrt 5 + 2 / Real.sqrt 5 := by ring
    linarith
  · intro m hm
    have hcases : m ≤ 0 ∨ 2 ≤ m := by omega
    rcases hcases with hle0 | hge2
    · have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hle0
      have hnonpos : 2 * (m : ℝ) / Real.sqrt 5 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt h5_pos)
      have habs : |2 * (m : ℝ) / Real.sqrt 5 - 1| = 1 - 2 * (m : ℝ) / Real.sqrt 5 := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [habs]
      have h4 : 4 / Real.sqrt 5 < 2 := by rw [div_lt_iff₀ h5_pos]; linarith
      linarith
    · have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hge2
      have hle : 4 / Real.sqrt 5 ≤ 2 * (m : ℝ) / Real.sqrt 5 :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt h5_pos)
      have h4 : 1 < 4 / Real.sqrt 5 := by rw [one_lt_div h5_pos]; linarith
      rw [abs_of_nonneg (by linarith)]
      linarith

/-- 引理 2 第二部分（取等条件）：值等于 $1 - \frac{2}{\sqrt{5}}$ 当且仅当 $\eta \in \{\varphi, \varphi+1\}$。 -/
theorem norm_parity_rigidity_eq_iff {a b c d : ℤ} (hdet : |a * d - b * c| = 1) :
    orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
      (|2 - orbitPt a b c d| * |orbitPtConj a b c d| / 2) = 1 - 2 / Real.sqrt 5 ↔
    orbitPt a b c d = φ ∨ orbitPt a b c d = φ + 1 := by
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  have h5_sq := sqrt5_sq
  have hcd := linear_phi_ne_zero (cd_ne_zero_of_det hdet)
  have hab := linear_phi_ne_zero (ab_ne_zero_of_det hdet)
  constructor
  · intro heq
    rcases m0_even hdet with ⟨k0, hk0⟩
    set ε : ℤ := a * d - b * c with hε_def
    have hε : ε = 1 ∨ ε = -1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
    have hε_sq : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
    set m : ℤ := ε * k0
    have hm0R : (m0 a b c d : ℝ) = 2 * (k0 : ℝ) := by
      exact_mod_cast (show m0 a b c d = 2 * k0 by omega)
    have hval : |2 * (m : ℝ) / Real.sqrt 5 - 1| = 1 - 2 / Real.sqrt 5 := by
      rw [rigidity_lhs_eq hdet] at heq
      rw [← heq, hm0R, ← hε_def]
      dsimp only [m]
      rcases hε with h1 | hm1
      · rw [h1]; push_cast; rw [one_mul, one_mul]
        rw [show |2 * (k0 : ℝ) - Real.sqrt 5| / Real.sqrt 5 =
            |(2 * (k0 : ℝ) - Real.sqrt 5) / Real.sqrt 5| by rw [abs_div, abs_of_pos h5_pos]]
        congr 1; field_simp [h5_ne]
      · rw [hm1]; push_cast
        rw [show |2 * (k0 : ℝ) - (-1 : ℝ) * Real.sqrt 5| / Real.sqrt 5 =
            |(2 * (k0 : ℝ) - (-1 : ℝ) * Real.sqrt 5) / Real.sqrt 5| by
          rw [abs_div, abs_of_pos h5_pos]]
        rw [← abs_neg (2 * (-1 * (k0 : ℝ)) / Real.sqrt 5 - 1)]
        congr 1; field_simp [h5_ne]; ring
    have hm1 : m = 1 := by
      by_contra hne
      have hge := spectral_gap_constants.2.2 m hne
      have hlt := spectral_gap_constants.2.1
      linarith
    have hk0_eq : k0 = ε := by
      have : ε * (ε * k0) = ε * 1 := congrArg (ε * ·) hm1
      have : ε ^ 2 * k0 = ε := by linarith
      rw [hε_sq, one_mul] at this
      exact this
    have hm0_eq : m0 a b c d = 2 * ε := by omega
    have hnorm := m0_norm_identity a b c d
    rw [hm0_eq, ← hε_def, hε_sq, mul_one] at hnorm
    have hNprod : zphiNorm (2 * c - a) (2 * d - b) * zphiNorm a b = -1 := by
      have : (2 * ε) ^ 2 - 5 = -1 := by nlinarith [hε_sq]
      linarith
    have hNγ : zphiNorm a b = 1 ∨ zphiNorm a b = -1 := by
      have hdvd : zphiNorm a b ∣ -1 := ⟨zphiNorm (2 * c - a) (2 * d - b), by linarith⟩
      rcases Int.isUnit_iff.mp (isUnit_of_dvd_one (by simpa using dvd_neg.mp hdvd)) with h | h
      · left; exact h
      · right; exact h
    set αR : ℝ := ((2 * c - a : ℤ) : ℝ) * φ + ((2 * d - b : ℤ) : ℝ)
    set γR : ℝ := (a : ℝ) * φ + (b : ℝ)
    set γ'R : ℝ := (a : ℝ) * φ' + (b : ℝ)
    have hαγ' : αR * γ'R = (ε : ℝ) * (2 - Real.sqrt 5) := by
      have h1 := alpha_mul_gammaConj a b c d
      change αR * γ'R = _ at h1
      rw [h1, hm0_eq, ← hε_def]
      push_cast; ring
    have hγγ' : γR * γ'R = (zphiNorm a b : ℝ) := zphi_mul_conj a b
    have hsum : αR + γR = 2 * ((c : ℝ) * φ + (d : ℝ)) := by
      dsimp only [αR, γR]; push_cast; ring
    have hσ : (ε : ℝ) * (zphiNorm a b : ℝ) = 1 ∨ (ε : ℝ) * (zphiNorm a b : ℝ) = -1 := by
      rcases hε with h1 | hm1
      · rcases hNγ with h2 | hm2
        · left; rw [h1, h2]; norm_num
        · right; rw [h1, hm2]; norm_num
      · rcases hNγ with h2 | hm2
        · right; rw [hm1, h2]; norm_num
        · left; rw [hm1, hm2]; norm_num
    have hα_eq : αR = ((ε : ℝ) * (zphiNorm a b : ℝ)) * (2 - Real.sqrt 5) * γR := by
      have hγ'_ne : γ'R ≠ 0 := hab.2
      have hNγ_sq : (zphiNorm a b : ℝ) ^ 2 = 1 := by
        rcases hNγ with h | h <;> rw [h] <;> norm_num
      have hmul : αR * γ'R = ((ε : ℝ) * (zphiNorm a b : ℝ)) * (2 - Real.sqrt 5) * (γR * γ'R) := by
        rw [hγγ', hαγ']
        linear_combination -(ε : ℝ) * (2 - Real.sqrt 5) * hNγ_sq
      exact mul_right_cancel₀ hγ'_ne (by linarith)
    rcases hσ with hσ1 | hσm1
    · right
      rw [hσ1, one_mul] at hα_eq
      unfold orbitPt mobius
      change γR / ((c : ℝ) * φ + (d : ℝ)) = φ + 1
      have h2denom : 2 * ((c : ℝ) * φ + (d : ℝ)) = (3 - Real.sqrt 5) * γR := by
        linarith [hsum, hα_eq]
      have hdenom_eq : (c : ℝ) * φ + (d : ℝ) = ((3 - Real.sqrt 5) / 2) * γR := by linarith
      rw [hdenom_eq]
      have h3m5 : (3 - Real.sqrt 5) / 2 ≠ 0 := by
        have := sqrt5_bounds.2; linarith
      have hγ_ne : γR ≠ 0 := hab.1
      rw [div_eq_iff (mul_ne_zero h3m5 hγ_ne)]
      unfold φ
      ring_nf; rw [h5_sq]; ring
    · left
      rw [hσm1] at hα_eq
      unfold orbitPt mobius
      change γR / ((c : ℝ) * φ + (d : ℝ)) = φ
      have h2denom : 2 * ((c : ℝ) * φ + (d : ℝ)) = (Real.sqrt 5 - 1) * γR := by
        linarith [hsum, hα_eq]
      have hdenom_eq : (c : ℝ) * φ + (d : ℝ) = ((Real.sqrt 5 - 1) / 2) * γR := by linarith
      rw [hdenom_eq]
      have h5m1 : (Real.sqrt 5 - 1) / 2 ≠ 0 := by
        have := sqrt5_bounds.1; linarith
      have hγ_ne : γR ≠ 0 := hab.1
      rw [div_eq_iff (mul_ne_zero h5m1 hγ_ne)]
      unfold φ
      ring_nf; rw [h5_sq]; ring
  · intro hor
    have hconj_eq : (orbitPt a b c d = φ → orbitPtConj a b c d = φ') ∧
        (orbitPt a b c d = φ + 1 → orbitPtConj a b c d = φ' + 1) := by
      have hlin : ∀ (u v : ℤ), (u : ℝ) * φ + (v : ℝ) = 0 → u = 0 ∧ v = 0 := by
        intro u v huv
        by_contra h
        have hne : u ≠ 0 ∨ v ≠ 0 := by tauto
        exact (linear_phi_ne_zero hne).1 huv
      constructor
      · intro hη
        unfold orbitPt mobius at hη
        have h0 : (a : ℝ) * φ + (b : ℝ) = φ * ((c : ℝ) * φ + (d : ℝ)) :=
          (div_eq_iff hcd.1).mp hη
        have h1 : ((a - c - d : ℤ) : ℝ) * φ + ((b - c : ℤ) : ℝ) = 0 := by
          push_cast
          linear_combination h0 + (c : ℝ) * phi_sq
        rcases hlin _ _ h1 with ⟨hu, hv⟩
        unfold orbitPtConj mobius
        rw [div_eq_iff hcd.2]
        have ha : (a : ℝ) = (c : ℝ) + (d : ℝ) := by exact_mod_cast (show a = c + d by omega)
        have hb : (b : ℝ) = (c : ℝ) := by exact_mod_cast (show b = c by omega)
        rw [ha, hb]; linear_combination -(c : ℝ) * phi'_sq
      · intro hη
        unfold orbitPt mobius at hη
        have h0 : (a : ℝ) * φ + (b : ℝ) = (φ + 1) * ((c : ℝ) * φ + (d : ℝ)) :=
          (div_eq_iff hcd.1).mp hη
        have h1 : ((a - 2 * c - d : ℤ) : ℝ) * φ + ((b - c - d : ℤ) : ℝ) = 0 := by
          push_cast
          linear_combination h0 + (c : ℝ) * phi_sq
        rcases hlin _ _ h1 with ⟨hu, hv⟩
        unfold orbitPtConj mobius
        rw [div_eq_iff hcd.2]
        have ha : (a : ℝ) = 2 * (c : ℝ) + (d : ℝ) := by
          exact_mod_cast (show a = 2 * c + d by omega)
        have hb : (b : ℝ) = (c : ℝ) + (d : ℝ) := by exact_mod_cast (show b = c + d by omega)
        rw [ha, hb]; linear_combination -(c : ℝ) * phi'_sq
    rcases hor with hφ | hφ1
    · have hφ' := hconj_eq.1 hφ
      rw [hφ, hφ']
      unfold orbitHeight
      rw [phi_sub_phi', abs_of_pos h5_pos]
      have h2mφ : 0 < 2 - φ := by unfold φ; linarith [sqrt5_bounds.2]
      have hφ'_neg : φ' < 0 := by unfold φ'; linarith [sqrt5_bounds.1]
      rw [abs_of_pos h2mφ, abs_of_neg hφ'_neg]
      unfold φ φ'
      field_simp [h5_ne]
      ring_nf; rw [h5_sq]; ring
    · have hφ1' := hconj_eq.2 hφ1
      rw [hφ1, hφ1']
      unfold orbitHeight
      rw [show (φ + 1) - (φ' + 1) = φ - φ' by ring, phi_sub_phi', abs_of_pos h5_pos]
      have h2mφ1 : 2 - (φ + 1) < 0 := by unfold φ; linarith [sqrt5_bounds.1]
      have hφ'1_pos : 0 < φ' + 1 := by unfold φ'; linarith [sqrt5_bounds.2]
      rw [abs_of_neg h2mφ1, abs_of_pos hφ'1_pos]
      unfold φ φ'
      field_simp [h5_ne]
      ring_nf; rw [h5_sq]; ring

/-- 引理 2 第三部分（谱隙下界）：对一切 $\eta \notin \{\varphi, \varphi+1\}$，恒有
    $h(\eta)\frac{|2-\eta|\,|\eta'|}{2} \ge \frac{4}{\sqrt{5}} - 1$。 -/
theorem norm_parity_rigidity_ge_second {a b c d : ℤ} (hdet : |a * d - b * c| = 1)
    (hne1 : orbitPt a b c d ≠ φ) (hne2 : orbitPt a b c d ≠ φ + 1) :
    4 / Real.sqrt 5 - 1 ≤
      orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
        (|2 - orbitPt a b c d| * |orbitPtConj a b c d| / 2) := by
  rcases norm_parity_rigidity_identity hdet with ⟨m, hm⟩
  rw [hm]
  have hm_ne : m ≠ 1 := by
    intro h1
    subst h1
    have hval : |2 * ((1 : ℤ) : ℝ) / Real.sqrt 5 - 1| = 1 - 2 / Real.sqrt 5 := by
      push_cast
      have hneg : 2 * 1 / Real.sqrt 5 - 1 < 0 := by
        have := spectral_gap_constants.1; linarith
      rw [abs_of_neg hneg]; ring
    rw [hval] at hm
    have := (norm_parity_rigidity_eq_iff hdet).mp hm
    rcases this with h | h
    · exact hne1 h
    · exact hne2 h
  exact spectral_gap_constants.2.2 m hm_ne

/-! ### 定理 B1 核心代数界 -/

/-- 素数 $2, 3$ 在 $\mathbb{Z}[\varphi]$ 中惰性：$|ad-bc|=1$ 时 $|N(c\varphi+d)| \notin \{2,3,4\}$，
    故要么 $|N(c\varphi+d)| = 1$，要么 $|N(c\varphi+d)| \ge 5$。 -/
theorem zphiNorm_not_two_three_four {a b c d : ℤ} (hdet : |a * d - b * c| = 1) :
    |zphiNorm c d| = 1 ∨ 5 ≤ |zphiNorm c d| := by
  have hne0 : zphiNorm c d ≠ 0 := zphiNorm_ne_zero (cd_ne_zero_of_det hdet)
  have hdet_cases : a * d - b * c = 1 ∨ a * d - b * c = -1 :=
    (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
  have hnot_even : ¬ Even (zphiNorm c d) := by
    rw [zphiNorm_even_iff]
    rintro ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩
    have hmul : a * (d' + d') - b * (c' + c') = 2 * (a * d' - b * c') := by ring
    omega
  have hnot_mod3 : zphiNorm c d % 3 ≠ 0 := by
    intro h3
    unfold zphiNorm at h3
    have hc_decomp : c = 3 * (c / 3) + c % 3 := by omega
    have hd_decomp : d = 3 * (d / 3) + d % 3 := by omega
    set rc := c % 3
    set rd := d % 3
    set kc := c / 3
    set kd := d / 3
    have hrc : rc = 0 ∨ rc = 1 ∨ rc = 2 := by omega
    have hrd : rd = 0 ∨ rd = 1 ∨ rd = 2 := by omega
    have hexp : -c ^ 2 + c * d + d ^ 2 =
        3 * (-3 * kc ^ 2 - 2 * kc * rc + 3 * kc * kd + kc * rd + rc * kd + 3 * kd ^ 2 + 2 * kd * rd) +
          (-rc ^ 2 + rc * rd + rd ^ 2) := by
      rw [hc_decomp, hd_decomp]; ring
    have hboth0 : rc = 0 ∧ rd = 0 := by
      rcases hrc with hc0 | hc1 | hc2 <;> rcases hrd with hd0 | hd1 | hd2
      · exact ⟨hc0, hd0⟩
      · rw [hc0, hd1] at hexp; omega
      · rw [hc0, hd2] at hexp; omega
      · rw [hc1, hd0] at hexp; omega
      · rw [hc1, hd1] at hexp; omega
      · rw [hc1, hd2] at hexp; omega
      · rw [hc2, hd0] at hexp; omega
      · rw [hc2, hd1] at hexp; omega
      · rw [hc2, hd2] at hexp; omega
    have hmul : a * d - b * c = 3 * (a * kd - b * kc) := by
      have hc0 : c = 3 * kc := by omega
      have hd0 : d = 3 * kd := by omega
      rw [hc0, hd0]; ring
    omega
  have hodd : zphiNorm c d % 2 ≠ 0 := by
    intro h2
    exact hnot_even ⟨zphiNorm c d / 2, by omega⟩
  set N := zphiNorm c d
  rcases le_or_gt 0 N with hpos | hneg
  · rw [abs_of_nonneg hpos]; omega
  · rw [abs_of_neg hneg]; omega

/-- 高度二分律：对任意轨道点，要么 $h(\eta) = \frac{2}{\sqrt{5}}$，要么 $h(\eta) \ge 2\sqrt{5}$。 -/
theorem height_dichotomy {a b c d : ℤ} (hdet : |a * d - b * c| = 1) :
    orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) = 2 / Real.sqrt 5 ∨
    2 * Real.sqrt 5 ≤ orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) := by
  rw [orbitHeight_eq hdet]
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  have h5_sq := sqrt5_sq
  rcases zphiNorm_not_two_three_four hdet with h1 | h5
  · left
    have h1R : |(zphiNorm c d : ℝ)| = 1 := by exact_mod_cast h1
    rw [h1R, mul_one]
  · right
    have h5R : (5 : ℝ) ≤ |(zphiNorm c d : ℝ)| := by exact_mod_cast h5
    have hle : 2 * (5 : ℝ) / Real.sqrt 5 ≤ 2 * |(zphiNorm c d : ℝ)| / Real.sqrt 5 :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt h5_pos)
    have heq : 2 * (5 : ℝ) / Real.sqrt 5 = 2 * Real.sqrt 5 := by
      field_simp [h5_ne]; ring_nf; rw [h5_sq]
    linarith

/-- 定理 B1 情形 1 的一致下界：将引理 2 与 $|T-\eta|$、$|\eta'+z|$ 的一致比较合并。 -/
theorem case1_lower_bound {a b c d : ℤ} (hdet : |a * d - b * c| = 1)
    (hne1 : orbitPt a b c d ≠ φ) (hne2 : orbitPt a b c d ≠ φ + 1)
    {δ z : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hconj : 0 < orbitPtConj a b c d ∨ orbitPtConj a b c d < -1)
    (hsep : 2 < orbitPt a b c d ∨ orbitPt a b c d < 3 / 2) :
    ((1 - 2 * δ) * (1 - z) / (1 + z / 2)) * (4 / Real.sqrt 5 - 1) ≤
      orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
        (|(2 - δ) - orbitPt a b c d| * |orbitPtConj a b c d + z| / ((2 - δ) + z)) := by
  set η := orbitPt a b c d
  set η' := orbitPtConj a b c d
  set H := orbitHeight η η'
  have hH_nonneg : 0 ≤ H := by
    unfold H orbitHeight; positivity
  have hη'_bound : (1 - z) * |η'| ≤ |η' + z| := by
    rcases hconj with hpos | hlt
    · rw [abs_of_pos hpos, abs_of_pos (by linarith)]
      nlinarith
    · have hneg1 : η' < 0 := by linarith
      have hneg2 : η' + z < 0 := by linarith
      rw [abs_of_neg hneg1, abs_of_neg hneg2]
      nlinarith
  have hT_bound : (1 - 2 * δ) * |2 - η| ≤ |(2 - δ) - η| := by
    rcases hsep with hgt2 | hlt32
    · rw [abs_of_neg (by linarith : 2 - η < 0), abs_of_neg (by linarith : (2 - δ) - η < 0)]
      nlinarith
    · rw [abs_of_pos (by linarith : 0 < 2 - η), abs_of_pos (by linarith : 0 < (2 - δ) - η)]
      nlinarith
  have hdenom_pos : 0 < (2 - δ) + z := by linarith
  have hdenom_le : (2 - δ) + z ≤ 2 * (1 + z / 2) := by linarith
  have h1 : (1 - 2 * δ) * (1 - z) * (|2 - η| * |η'|) ≤ |(2 - δ) - η| * |η' + z| := by
    have hmul := mul_le_mul hT_bound hη'_bound (by positivity) (by positivity)
    linarith
  have h2 : ((1 - 2 * δ) * (1 - z) / (1 + z / 2)) * (|2 - η| * |η'| / 2) ≤
      |(2 - δ) - η| * |η' + z| / ((2 - δ) + z) := by
    have hdiv1 : ((1 - 2 * δ) * (1 - z) * (|2 - η| * |η'|)) / (2 * (1 + z / 2)) ≤
        (|(2 - δ) - η| * |η' + z|) / (2 * (1 + z / 2)) :=
      div_le_div_of_nonneg_right h1 (by linarith)
    have hdiv2 : (|(2 - δ) - η| * |η' + z|) / (2 * (1 + z / 2)) ≤
        (|(2 - δ) - η| * |η' + z|) / ((2 - δ) + z) :=
      div_le_div_of_nonneg_left (by positivity) hdenom_pos hdenom_le
    have h1z_ne : 1 + z / 2 ≠ 0 := by linarith
    have hrew : ((1 - 2 * δ) * (1 - z) / (1 + z / 2)) * (|2 - η| * |η'| / 2) =
        ((1 - 2 * δ) * (1 - z) * (|2 - η| * |η'|)) / (2 * (1 + z / 2)) := by
      field_simp [h1z_ne]
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hH_nonneg
  have hrig := norm_parity_rigidity_ge_second hdet hne1 hne2
  have hfac_nonneg : 0 ≤ (1 - 2 * δ) * (1 - z) / (1 + z / 2) := by
    apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h4 := mul_le_mul_of_nonneg_left hrig hfac_nonneg
  linarith

/-- 定理 B1 情形 2.1 凹二次下界：对 $2 \le Q \le A - 1$，
    $(A - Q + 1 - \frac{\sqrt{5}}{2})(Q - \frac{\sqrt{5}}{2}) \ge (A - 1 - \frac{\sqrt{5}}{2})(2 - \frac{\sqrt{5}}{2})$。 -/
theorem case2_sub1_quadratic_ge {A Q : ℝ} (hQ1 : 2 ≤ Q) (hQ2 : Q ≤ A - 1) :
    (A - 1 - Real.sqrt 5 / 2) * (2 - Real.sqrt 5 / 2) ≤
      (A - Q + 1 - Real.sqrt 5 / 2) * (Q - Real.sqrt 5 / 2) := by
  have hdiff : (A - Q + 1 - Real.sqrt 5 / 2) * (Q - Real.sqrt 5 / 2) -
      (A - 1 - Real.sqrt 5 / 2) * (2 - Real.sqrt 5 / 2) = (Q - 2) * (A - 1 - Q) := by ring
  nlinarith

/-- 定理 B1 情形 2.2 凹二次下界：对 $A \ge 3$ 与 $2 \le Q \le A - 1$，
    $\frac{2}{\sqrt{5}} \frac{(A - Q + \frac{\sqrt{5}}{2} - 1)(Q + 2 + \frac{\sqrt{5}}{2})}{A + 1} \ge 1$。 -/
theorem case2_sub2_quadratic_ge {A Q : ℝ} (hA : 3 ≤ A) (hQ1 : 2 ≤ Q) (hQ2 : Q ≤ A - 1) :
    (1 : ℝ) ≤ (2 / Real.sqrt 5) *
      (((A - Q + Real.sqrt 5 / 2 - 1) * (Q + 2 + Real.sqrt 5 / 2)) / (A + 1)) := by
  have h5_pos := sqrt5_pos
  have h5_sq := sqrt5_sq
  have h5_gt2 := sqrt5_bounds.1
  have h5_lt25 := sqrt5_bounds.2
  have hA1 : 0 < A + 1 := by linarith
  have hquad : (Real.sqrt 5 / 2) * (A + 1) ≤
      (A - Q + Real.sqrt 5 / 2 - 1) * (Q + 2 + Real.sqrt 5 / 2) := by
    by_cases hA3 : A = 3
    · subst hA3
      have hQ2_eq : Q = 2 := by linarith
      subst hQ2_eq
      nlinarith [h5_gt2, h5_sq]
    · have hA3pos : 0 < A - 3 := lt_of_le_of_ne (by linarith) (Ne.symm (sub_ne_zero.mpr hA3))
      have hne : A - 3 ≠ 0 := ne_of_gt hA3pos
      have heq : (A - Q + Real.sqrt 5 / 2 - 1) * (Q + 2 + Real.sqrt 5 / 2) =
          (Q - 2) * (A - 1 - Q) +
            ((A - 1 - Q) / (A - 3)) * ((A - 3 + Real.sqrt 5 / 2) * (4 + Real.sqrt 5 / 2)) +
            ((Q - 2) / (A - 3)) * ((Real.sqrt 5 / 2) * (A + 1 + Real.sqrt 5 / 2)) := by
        field_simp [hne]; ring
      have hL : (Real.sqrt 5 / 2) * (A + 1) ≤ (A - 3 + Real.sqrt 5 / 2) * (4 + Real.sqrt 5 / 2) := by
        nlinarith [h5_gt2, h5_lt25, h5_sq]
      have hR : (Real.sqrt 5 / 2) * (A + 1) ≤ (Real.sqrt 5 / 2) * (A + 1 + Real.sqrt 5 / 2) := by
        nlinarith [h5_pos]
      have hα : 0 ≤ (A - 1 - Q) / (A - 3) := div_nonneg (by linarith) (le_of_lt hA3pos)
      have hβ : 0 ≤ (Q - 2) / (A - 3) := div_nonneg (by linarith) (le_of_lt hA3pos)
      have hsum : (A - 1 - Q) / (A - 3) + (Q - 2) / (A - 3) = 1 := by
        field_simp [hne]; ring
      have hprod_nonneg : 0 ≤ (Q - 2) * (A - 1 - Q) := mul_nonneg (by linarith) (by linarith)
      nlinarith
  have hdiv : Real.sqrt 5 / 2 ≤
      ((A - Q + Real.sqrt 5 / 2 - 1) * (Q + 2 + Real.sqrt 5 / 2)) / (A + 1) := by
    rw [le_div_iff₀ hA1]; linarith
  have hmul := mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 / Real.sqrt 5)
  have hcancel : (2 / Real.sqrt 5) * (Real.sqrt 5 / 2) = 1 := by
    field_simp [ne_of_gt h5_pos]
  linarith

/-- 定理 B1 情形 2.3 凹二次下界：对 $2 \le Q \le A - 1$，
    $(A - Q - \frac{1}{2})(Q - \frac{1}{2}) \ge \frac{1}{2}(A - \frac{3}{2})$。 -/
theorem case2_sub3_quadratic_ge {A Q : ℝ} (hQ1 : 2 ≤ Q) (hQ2 : Q ≤ A - 1) :
    (1 / 2 : ℝ) * (A - 3 / 2) ≤ (A - Q - 1 / 2) * (Q - 1 / 2) := by
  have hdiff : (A - Q - 1 / 2) * (Q - 1 / 2) - (1 / 2) * (A - 3 / 2) =
      (A - 1 - Q) * (Q - 1) := by ring
  nlinarith

/-- 第二极限点 $\frac{4}{\sqrt{5}} - 1$ 由 $\eta = 4 - \varphi$ 精确取到。 -/
theorem second_limit_point_attained_value :
    orbitHeight (4 - φ) (4 - φ') * (|2 - (4 - φ)| * |4 - φ'| / 2) = 4 / Real.sqrt 5 - 1 := by
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  have h5_sq := sqrt5_sq
  unfold orbitHeight
  rw [show (4 - φ) - (4 - φ') = -(φ - φ') by ring, abs_neg, phi_sub_phi', abs_of_pos h5_pos]
  have h1 : 2 - (4 - φ) < 0 := by unfold φ; linarith [sqrt5_bounds.2]
  have h2 : 0 < 4 - φ' := by unfold φ'; linarith [sqrt5_bounds.1]
  rw [abs_of_neg h1, abs_of_pos h2]
  unfold φ φ'
  field_simp [h5_ne]
  ring_nf; rw [h5_sq]; ring

/-- $B=2$ 对照模型 $11/2 - e$ 上界常数恒等式：
    $\frac{2}{\sqrt{5}} \cdot \frac{|\varphi - 8/5|\,|\varphi'|}{8/5} = \frac{9}{4\sqrt{5}} - 1$。 -/
theorem b2_control_model_constant :
    (2 / Real.sqrt 5) * (|φ - 8 / 5| * |φ'| / (8 / 5)) = 9 / (4 * Real.sqrt 5) - 1 := by
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  have h5_sq := sqrt5_sq
  have h1 : 0 < φ - 8 / 5 := by
    unfold φ
    have : (11 : ℝ) / 5 < Real.sqrt 5 := by
      rw [show (11 : ℝ) / 5 = Real.sqrt (121 / 25) by norm_num]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have h2 : φ' < 0 := by unfold φ'; linarith [sqrt5_bounds.1]
  rw [abs_of_pos h1, abs_of_neg h2]
  unfold φ φ'
  field_simp [h5_ne]
  ring_nf; rw [h5_sq]; ring

end GoldenOrbitRigidity
