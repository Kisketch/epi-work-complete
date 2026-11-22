import Mathlib
import EpiFormal.EulerConvergents
import EpiFormal.Axioms
import EpiFormal.SignedClusters

/-!
# S6 缺陷尾等价（Theorem 9）与双射（Corollary 10）—— 联合编译归一版

本文件为「总」联合编译归一版：地基统一取用 A 组 `EpiFormal.EulerConvergents`
（顶层 Psel/Qsel/deltaSel 与两条 deltaSel 公理），删除 E 原自建地基；
E 下游所需桥接引理从 A 接口重证，Theorem 9 / Corollary 10 / 精细尺度 / 控制反例主体证明原样保留。
`deltaSel_ne_zero` 用白名单公理 `e_transcendental`（经 `e_irrational`）。

**e+π 无理性仍是开放问题；本文件只做结构定理的机器验证，不声称解决该问题。**
Corollary 10 单射 + 满射均已机器验证：满射调用 D 组 SignedClusters.theorem8_realization
（任意有界整数序列可实现），桥接 Mseq=Msel 同源缺陷定义，并证构造实数属于 F。
-/

open Real Set Filter Int

namespace DefectFibres

noncomputable section

/-! ## 地基桥接：从 A 组重证 E 下游所需引理（同名同陈述） -/

@[simp] lemma Psel_zero : Psel 0 = 1 := _root_.Psel_zero
@[simp] lemma Qsel_zero : Qsel 0 = 1 := _root_.Qsel_zero
@[simp] lemma Psel_one : Psel 1 = 3 := _root_.Psel_one
@[simp] lemma Qsel_one : Qsel 1 = 1 := _root_.Qsel_one
lemma Psel_two : Psel 2 = 19 := _root_.Psel_two
lemma Qsel_two : Qsel 2 = 7 := _root_.Qsel_two

/-- 系数 4k+6 形式 P 递推（全 k）。 -/
lemma Psel_rec_aux (k : ℕ) :
    Psel (k + 2) = (4 * (k : ℤ) + 6) * Psel (k + 1) + Psel k := by
  have h := selPair_rec 1 3 k
  simp only [Psel] at h ⊢
  convert h using 1 <;> push_cast <;> ring

/-- 系数 4k+6 形式 Q 递推（全 k）。 -/
lemma Qsel_rec_aux (k : ℕ) :
    Qsel (k + 2) = (4 * (k : ℤ) + 6) * Qsel (k + 1) + Qsel k := by
  have h := selPair_rec 1 1 k
  simp only [Qsel] at h ⊢
  convert h using 1 <;> push_cast <;> ring

/-- 分母正性（j≥1）。 -/
lemma Qsel_pos (j : ℕ) (hj : 1 ≤ j) : 0 < Qsel j := _root_.Qsel_pos j hj

/-- 分子递推（j≥2）。 -/
lemma Psel_rec (j : ℕ) (hj : 2 ≤ j) : Psel (j + 1) = (4 * (j : ℤ) + 2) * Psel j + Psel (j - 1) :=
  _root_.Psel_rec j hj

/-- 分母递推（j≥2）。 -/
lemma Qsel_rec (j : ℕ) (hj : 2 ≤ j) : Qsel (j + 1) = (4 * (j : ℤ) + 2) * Qsel j + Qsel (j - 1) :=
  _root_.Qsel_rec j hj

/-- 相邻行列式（j≥1）。 -/
lemma sel_determinant (j : ℕ) (hj : 1 ≤ j) :
    Psel j * Qsel (j + 1) - Psel (j + 1) * Qsel j = 2 * (-1 : ℤ) ^ (j + 1) :=
  _root_.sel_determinant j hj

/-- 分子恒奇（j≥1）。 -/
lemma Psel_odd (j : ℕ) (hj : 1 ≤ j) : Odd (Psel j) := _root_.Psel_odd j hj

/-- 分母恒奇（j≥1）。 -/
lemma Qsel_odd (j : ℕ) (hj : 1 ≤ j) : Odd (Qsel j) := _root_.Qsel_odd j hj

/-- 分母倍增（j≥2）。 -/
lemma Qsel_double (j : ℕ) (hj : 2 ≤ j) : 2 * Qsel j ≤ Qsel (j + 1) := _root_.Qsel_double j hj

/-- 相邻分母互素（j≥1）。 -/
lemma Qsel_succ_coprime (j : ℕ) (hj : 1 ≤ j) : Int.gcd (Qsel j) (Qsel (j + 1)) = 1 :=
  _root_.Qsel_succ_coprime j hj

/-- Q_j → ∞。 -/
lemma Qsel_tendsto_atTop : Tendsto (fun j : ℕ => (Qsel j : ℝ)) atTop atTop :=
  _root_.Qsel_tendsto_atTop

/-- P_j/Q_j → e。 -/
lemma Psel_div_Qsel_tendsto_exp :
    Tendsto (fun j : ℕ => (Psel j : ℝ) / (Qsel j : ℝ)) atTop (nhds (exp 1)) :=
  _root_.Psel_div_Qsel_tendsto_exp

/-- δ_j ≠ 0（e 无理）。 -/
lemma deltaSel_ne_zero (j : ℕ) (hj : 1 ≤ j) : deltaSel j ≠ 0 := by
  intro h
  have hQ : (Qsel j : ℝ) ≠ 0 := by exact_mod_cast (Qsel_pos j hj).ne'
  have he : exp 1 = (Psel j : ℝ) / (Qsel j : ℝ) := by
    simp only [deltaSel] at h
    field_simp at h ⊢
    linarith
  exact e_irrational ⟨(Psel j : ℚ) / (Qsel j : ℚ), by push_cast; exact he.symm⟩

/-- j·δ_j → 0（平移保 F 用）。 -/
lemma jdeltaSel_tendsto_zero : Tendsto (fun j : ℕ => (j : ℝ) * deltaSel j) atTop (nhds 0) := by
  have hbound : ∀ᶠ j : ℕ in atTop, |(j : ℝ) * deltaSel j| ≤ 1 / (2 * (Qsel j : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hj1 : 1 ≤ j := hj
    have hδ := abs_deltaSel_lt j hj1
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    calc |(j : ℝ) * deltaSel j| = (j : ℝ) * |deltaSel j| := by rw [abs_mul, abs_of_pos hjR]
      _ ≤ (j : ℝ) * (1 / (2 * (j : ℝ) * (Qsel j : ℝ))) := by gcongr
      _ = 1 / (2 * (Qsel j : ℝ)) := by
        have hQ : (Qsel j : ℝ) ≠ 0 := by exact_mod_cast (Qsel_pos j hj1).ne'
        field_simp
  have htend : Tendsto (fun j : ℕ => 1 / (2 * (Qsel j : ℝ))) atTop (nhds 0) := by
    have hden : Tendsto (fun j : ℕ => 2 * (Qsel j : ℝ)) atTop atTop :=
      Qsel_tendsto_atTop.const_mul_atTop (by norm_num)
    have h1 : Tendsto (fun j : ℕ => (1 : ℝ) / (2 * (Qsel j : ℝ))) atTop (nhds 0) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hden
    exact h1
  have habs : Tendsto (fun j : ℕ => |(j : ℝ) * deltaSel j|) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound htend
  exact (tendsto_zero_iff_abs_tendsto_zero (f := fun j : ℕ => (j : ℝ) * deltaSel j)).mpr habs

/-! ## 第二部分：记号（S1/S6） -/

/-- 最近整数 M_j(x) = round(Q_j x)。 -/
noncomputable def Msel (x : ℝ) (j : ℕ) : ℤ := round ((Qsel j : ℝ) * x)

/-- 带号残差 ε_j(x) = Q_j x − M_j(x)。 -/
noncomputable def epsSel (x : ℝ) (j : ℕ) : ℝ := (Qsel j : ℝ) * x - (Msel x j : ℝ)

/-- 整数缺陷 D_j(x) = M_{j+1} − (4j+2)M_j − M_{j−1}。 -/
def defect (x : ℝ) (j : ℕ) : ℤ :=
  Msel x (j + 1) - (4 * (j : ℤ) + 2) * Msel x j - Msel x (j - 1)

/-- 尾相同：最终逐指标相等。 -/
def sameTail (a b : ℕ → ℤ) : Prop := ∀ᶠ j in atTop, a j = b j

/-- 分类格 L = ℤ + ℤ(e+1)/2。 -/
def latticeL : Set ℝ := {t | ∃ m n : ℤ, t = (m : ℝ) + (n : ℝ) * (exp 1 + 1) / 2}

/-- F = {x : S(x) 有限}，用等价刻画 j·|ε_j(x)| 最终有界。 -/
def inF (x : ℝ) : Prop := ∃ C : ℝ, ∀ᶠ j : ℕ in atTop, (j : ℝ) * |epsSel x j| ≤ C

/-- 残差恒等式：Q_j x = M_j(x) + ε_j(x)。 -/
lemma Qsel_mul_eq_Msel_add_eps (x : ℝ) (j : ℕ) :
    (Qsel j : ℝ) * x = (Msel x j : ℝ) + epsSel x j := by
  simp [epsSel]

/-- 缺陷恒等式（S1，j≥1）。 -/
lemma defect_identity (x : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    (defect x j : ℝ) =
      -epsSel x (j + 1) + (4 * (j : ℝ) + 2) * epsSel x j + epsSel x (j - 1) := by
  by_cases hj2 : 2 ≤ j
  · have hQ : (Qsel (j + 1) : ℝ) = (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by
      have := Qsel_rec j hj2
      push_cast at this ⊢
      exact_mod_cast this
    simp only [defect, epsSel, Msel]
    push_cast
    rw [hQ]
    ring
  · have hj1 : j = 1 := by omega
    subst hj1
    simp only [defect, epsSel, Msel]
    norm_num [Qsel, Psel, selPair]
    ring

/-- 齐次递推谓词。 -/
def homogeneousRec (H : ℕ → ℤ) (j : ℕ) : Prop :=
  H (j + 1) = (4 * (j : ℤ) + 2) * H j + H (j - 1)

/-- 缺陷尾相同 ⇔ 差 H=M(x)−M(y) 最终满足齐次递推。 -/
lemma homogeneous_recurrence_iff (x y : ℝ) :
    sameTail (defect x) (defect y) ↔
      ∀ᶠ j : ℕ in atTop, homogeneousRec (fun k => Msel x k - Msel y k) j := by
  constructor
  · intro h
    filter_upwards [h] with j hj
    simp only [defect, homogeneousRec] at hj ⊢
    linarith
  · intro h
    filter_upwards [h] with j hj
    simp only [defect, homogeneousRec] at hj ⊢
    linarith

/-- F 中残差→0。 -/
lemma epsSel_tendsto_zero_of_inF {x : ℝ} (hx : inF x) :
    Tendsto (epsSel x) atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := hx
  have hbound : ∀ᶠ j : ℕ in atTop, |epsSel x j| ≤ C / (j : ℝ) := by
    filter_upwards [hC, eventually_ge_atTop 1] with j hj hj1
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    rw [le_div_iff₀ hjR]
    nlinarith [abs_nonneg (epsSel x j)]
  have htend : Tendsto (fun j : ℕ => C / (j : ℝ)) atTop (nhds 0) :=
    (tendsto_const_nhds (x := C)).div_atTop tendsto_natCast_atTop_atTop
  have habs : Tendsto (fun j : ℕ => |epsSel x j|) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound htend
  exact (tendsto_zero_iff_abs_tendsto_zero (f := epsSel x)).mpr habs

/-- 由 j|ε_j|≤C 推出 |ε_j|≤C/j。 -/
lemma eps_bound_of_weighted {x : ℝ} {C : ℝ} {N : ℕ}
    (hC : ∀ j : ℕ, N ≤ j → (j : ℝ) * |epsSel x j| ≤ C) :
    ∀ j : ℕ, max N 1 ≤ j → |epsSel x j| ≤ C / (j : ℝ) := by
  intro j hj
  have hjN : N ≤ j := le_trans (le_max_left N 1) hj
  have hj1 : 1 ≤ j := le_trans (le_max_right N 1) hj
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have := hC j hjN
  rw [le_div_iff₀ hjR]
  nlinarith [abs_nonneg (epsSel x j)]

/-- F 中缺陷最终有界。 -/
lemma defect_bounded_of_inF {x : ℝ} (hx : inF x) :
    ∃ K : ℤ, ∀ᶠ j : ℕ in atTop, |defect x j| ≤ K := by
  obtain ⟨C, hC⟩ := hx
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.mp hC)
  have hεb := eps_bound_of_weighted (C := C) (N := N) hN
  have hCnn : 0 ≤ C := by
    have := hN (max N 1) (le_max_left N 1)
    nlinarith [abs_nonneg (epsSel x (max N 1))]
  use ⌈(7 : ℝ) * C⌉₊
  refine (eventually_ge_atTop (max N 2 + 1)).mono ?_
  intro j hj
  have hj2 : 2 ≤ j := by omega
  have hjN1 : max N 1 ≤ j := by omega
  have hjN1p : max N 1 ≤ j + 1 := by omega
  have hjN1m : max N 1 ≤ j - 1 := by omega
  have hb_j := hεb j hjN1
  have hb_jp := hεb (j + 1) hjN1p
  have hb_jm := hεb (j - 1) hjN1m
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hjpR : (0 : ℝ) < (j + 1 : ℝ) := by positivity
  have hjmR : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < j - 1)
  have hjp_cast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  have hjm_cast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ j)]; ring
  have hb_jp' : |epsSel x (j + 1)| ≤ C / ((j : ℝ) + 1) := by rw [← hjp_cast]; exact hb_jp
  have hb_jm' : |epsSel x (j - 1)| ≤ C / ((j : ℝ) - 1) := by rw [← hjm_cast]; exact hb_jm
  have hreal : |(defect x j : ℝ)| ≤ (7 : ℝ) * C := by
    rw [defect_identity x j (by omega)]
    have h1 : |-epsSel x (j + 1) + (4 * (j : ℝ) + 2) * epsSel x j + epsSel x (j - 1)| ≤
        |epsSel x (j + 1)| + (4 * (j : ℝ) + 2) * |epsSel x j| + |epsSel x (j - 1)| := by
      have t1 := abs_add_le (-epsSel x (j + 1) + (4 * (j : ℝ) + 2) * epsSel x j) (epsSel x (j - 1))
      have t2 := abs_add_le (-epsSel x (j + 1)) ((4 * (j : ℝ) + 2) * epsSel x j)
      have t3 : |(4 * (j : ℝ) + 2) * epsSel x j| = (4 * (j : ℝ) + 2) * |epsSel x j| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (j : ℝ) + 2)]
      linarith [abs_neg (epsSel x (j + 1))]
    have h2 : |epsSel x (j + 1)| + (4 * (j : ℝ) + 2) * |epsSel x j| + |epsSel x (j - 1)| ≤
        C / ((j : ℝ) + 1) + (4 * (j : ℝ) + 2) * (C / (j : ℝ)) + C / ((j : ℝ) - 1) := by
      have c4 : (0 : ℝ) ≤ 4 * (j : ℝ) + 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hb_j c4]
    have h3 : C / ((j : ℝ) + 1) + (4 * (j : ℝ) + 2) * (C / (j : ℝ)) + C / ((j : ℝ) - 1) ≤
        (7 : ℝ) * C := by
      have hj2R : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
      have hdiv1 : C / ((j : ℝ) + 1) ≤ C := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)]; nlinarith
      have hdiv2 : (4 * (j : ℝ) + 2) * (C / (j : ℝ)) ≤ (5 : ℝ) * C := by
        have heq : (4 * (j : ℝ) + 2) * (C / (j : ℝ)) = (4 : ℝ) * C + 2 * C / (j : ℝ) := by
          field_simp
        rw [heq]
        have h2C : 2 * C / (j : ℝ) ≤ C := by
          rw [div_le_iff₀ hjR]; nlinarith
        nlinarith
      have hdiv3 : C / ((j : ℝ) - 1) ≤ C := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < (j : ℝ) - 1)]; nlinarith
      calc C / ((j : ℝ) + 1) + (4 * (j : ℝ) + 2) * (C / (j : ℝ)) + C / ((j : ℝ) - 1)
          ≤ C + (5 : ℝ) * C + C := by
            nlinarith [hdiv1, hdiv2, hdiv3]
        _ = (7 : ℝ) * C := by ring
    linarith
  have hcast : |(defect x j : ℝ)| = (|defect x j| : ℝ) := by push_cast; rfl
  rw [hcast] at hreal
  have hceil : (7 : ℝ) * C ≤ (⌈(7 : ℝ) * C⌉₊ : ℝ) := Nat.le_ceil _
  exact_mod_cast (le_trans hreal hceil)

/-! ## 第三部分：Theorem 9 的代数核心 -/

/-- Cramér（行列式 ±2）。 -/
lemma cramer_two_int (j : ℕ) (hj : 1 ≤ j) (Hj Hj1 : ℤ) :
    ∃ a b : ℤ, 2 * Hj = a * Psel j + b * Qsel j ∧
      2 * Hj1 = a * Psel (j + 1) + b * Qsel (j + 1) := by
  set s := (-1 : ℤ) ^ (j + 1)
  have hdet : Psel j * Qsel (j + 1) - Psel (j + 1) * Qsel j = 2 * s := sel_determinant j hj
  have hs2 : s * s = 1 := by
    have hpm : s = 1 ∨ s = -1 := by
      simp only [s]
      rcases Nat.even_or_odd (j + 1) with h | h
      · left; exact h.neg_one_pow
      · right; exact h.neg_one_pow
    rcases hpm with h | h <;> rw [h] <;> norm_num
  use s * (Hj * Qsel (j + 1) - Hj1 * Qsel j)
  use s * (Psel j * Hj1 - Psel (j + 1) * Hj)
  constructor
  · have h1 : s * (Hj * Qsel (j + 1) - Hj1 * Qsel j) * Psel j +
        s * (Psel j * Hj1 - Psel (j + 1) * Hj) * Qsel j = s * Hj * (2 * s) := by
      linear_combination s * Hj * hdet
    have h2 : s * Hj * (2 * s) = 2 * Hj := by
      calc s * Hj * (2 * s) = 2 * Hj * (s * s) := by ring
        _ = 2 * Hj := by rw [hs2]; ring
    linarith
  · have h1 : s * (Hj * Qsel (j + 1) - Hj1 * Qsel j) * Psel (j + 1) +
        s * (Psel j * Hj1 - Psel (j + 1) * Hj) * Qsel (j + 1) = s * Hj1 * (2 * s) := by
      linear_combination s * Hj1 * hdet
    have h2 : s * Hj1 * (2 * s) = 2 * Hj1 := by
      calc s * Hj1 * (2 * s) = 2 * Hj1 * (s * s) := by ring
        _ = 2 * Hj1 := by rw [hs2]; ring
    linarith

/-- 齐次递推传播。 -/
lemma propagate_homogeneous (H : ℕ → ℤ) (a b : ℤ) (N : ℕ) (hN : 2 ≤ N)
    (hrec : ∀ j : ℕ, N ≤ j → homogeneousRec H j)
    (hbase0 : 2 * H N = a * Psel N + b * Qsel N)
    (hbase1 : 2 * H (N + 1) = a * Psel (N + 1) + b * Qsel (N + 1)) :
    ∀ j : ℕ, N ≤ j → 2 * H j = a * Psel j + b * Qsel j := by
  have hstrong : ∀ k : ℕ, 2 * H (N + k) = a * Psel (N + k) + b * Qsel (N + k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k with
      | 0 => simpa using hbase0
      | 1 => simpa using hbase1
      | k + 2 =>
        set m := N + k
        have hm2 : 2 ≤ m + 1 := by omega
        have hjrec : homogeneousRec H (m + 1) := hrec (m + 1) (by omega)
        simp only [homogeneousRec] at hjrec
        have hm1 : m + 1 - 1 = m := by omega
        have hm2' : m + 1 + 1 = m + 2 := by omega
        rw [hm1, hm2'] at hjrec
        have hjP : Psel (m + 2) = (4 * (m : ℤ) + 6) * Psel (m + 1) + Psel m := Psel_rec_aux m
        have hjQ : Qsel (m + 2) = (4 * (m : ℤ) + 6) * Qsel (m + 1) + Qsel m := Qsel_rec_aux m
        have ih1 : 2 * H (m + 1) = a * Psel (m + 1) + b * Qsel (m + 1) := by
          have := ih (k + 1) (by omega)
          convert this using 1 <;> simp [m] <;> omega
        have ih0 : 2 * H m = a * Psel m + b * Qsel m := by
          have := ih k (by omega)
          convert this using 1 <;> simp [m] <;> omega
        have hcast : (4 * ((m + 1 : ℕ) : ℤ) + 2) = 4 * (m : ℤ) + 6 := by push_cast; ring
        have hgoal : 2 * H (N + (k + 2)) = a * Psel (N + (k + 2)) + b * Qsel (N + (k + 2)) := by
          have hNk : N + (k + 2) = m + 2 := by simp [m]; omega
          rw [hNk, hjrec, hjP, hjQ, hcast]
          nlinarith [ih1, ih0]
        exact hgoal
  intro j hj
  have hk : ∃ k : ℕ, j = N + k := ⟨j - N, by omega⟩
  obtain ⟨k, rfl⟩ := hk
  exact hstrong k

/-- 极限引理：2(x−y) = a·e + b。 -/
lemma limit_two_diff (x y : ℝ) (hx : inF x) (hy : inF y) (a b : ℤ) (N : ℕ)
    (hprop : ∀ j : ℕ, N ≤ j → 2 * (Msel x j - Msel y j) = a * Psel j + b * Qsel j) :
    2 * (x - y) = (a : ℝ) * exp 1 + (b : ℝ) := by
  have heq : ∀ᶠ j : ℕ in atTop,
      2 * (x - y) = (a : ℝ) * ((Psel j : ℝ) / (Qsel j : ℝ)) + (b : ℝ) +
        2 * (epsSel x j - epsSel y j) / (Qsel j : ℝ) := by
    filter_upwards [eventually_ge_atTop (max N 1)] with j hj
    have hjN : N ≤ j := le_trans (le_max_left N 1) hj
    have hj1 : 1 ≤ j := le_trans (le_max_right N 1) hj
    have hQ : (Qsel j : ℝ) ≠ 0 := by exact_mod_cast (Qsel_pos j hj1).ne'
    have hp := hprop j hjN
    have hpx : (Qsel j : ℝ) * x = (Msel x j : ℝ) + epsSel x j := Qsel_mul_eq_Msel_add_eps x j
    have hpy : (Qsel j : ℝ) * y = (Msel y j : ℝ) + epsSel y j := Qsel_mul_eq_Msel_add_eps y j
    have hpR : (2 : ℝ) * ((Msel x j : ℝ) - (Msel y j : ℝ)) =
        (a : ℝ) * (Psel j : ℝ) + (b : ℝ) * (Qsel j : ℝ) := by exact_mod_cast hp
    have h2Q : (2 : ℝ) * (Qsel j : ℝ) * (x - y) =
        (a : ℝ) * (Psel j : ℝ) + (b : ℝ) * (Qsel j : ℝ) + 2 * (epsSel x j - epsSel y j) := by
      calc (2 : ℝ) * (Qsel j : ℝ) * (x - y)
          = 2 * ((Qsel j : ℝ) * x - (Qsel j : ℝ) * y) := by ring
        _ = 2 * ((Msel x j : ℝ) + epsSel x j - ((Msel y j : ℝ) + epsSel y j)) := by rw [hpx, hpy]
        _ = 2 * ((Msel x j : ℝ) - (Msel y j : ℝ)) + 2 * (epsSel x j - epsSel y j) := by ring
        _ = (a : ℝ) * (Psel j : ℝ) + (b : ℝ) * (Qsel j : ℝ) + 2 * (epsSel x j - epsSel y j) := by
            rw [hpR]
    field_simp at h2Q ⊢
    linarith
  have hPQ : Tendsto (fun j : ℕ => (a : ℝ) * ((Psel j : ℝ) / (Qsel j : ℝ)) + (b : ℝ))
      atTop (nhds ((a : ℝ) * exp 1 + (b : ℝ))) := by
    exact (Psel_div_Qsel_tendsto_exp.const_mul (a : ℝ)).add
      (tendsto_const_nhds (x := (b : ℝ)))
  have hnum : Tendsto (fun j : ℕ => 2 * (epsSel x j - epsSel y j)) atTop (nhds 0) := by
    have hεx := epsSel_tendsto_zero_of_inF hx
    have hεy := epsSel_tendsto_zero_of_inF hy
    have := (hεx.sub hεy).const_mul (2 : ℝ)
    convert this using 1; ext j; ring_nf
  have hres : Tendsto (fun j : ℕ => 2 * (epsSel x j - epsSel y j) / (Qsel j : ℝ))
      atTop (nhds 0) := hnum.div_atTop Qsel_tendsto_atTop
  have hRHS : Tendsto (fun j : ℕ => (a : ℝ) * ((Psel j : ℝ) / (Qsel j : ℝ)) + (b : ℝ) +
      2 * (epsSel x j - epsSel y j) / (Qsel j : ℝ)) atTop (nhds ((a : ℝ) * exp 1 + (b : ℝ))) := by
    have := hPQ.add hres
    convert this using 1; ext j; ring_nf
  have hLHS : Tendsto (fun j : ℕ => 2 * (x - y)) atTop (nhds (2 * (x - y))) := tendsto_const_nhds
  exact tendsto_nhds_unique_of_eventuallyEq hLHS hRHS heq

/-- 奇偶步骤：a+b 偶。 -/
lemma parity_even_sum (j : ℕ) (hj : 1 ≤ j) (a b Hj : ℤ)
    (h : 2 * Hj = a * Psel j + b * Qsel j) : Even (a + b) := by
  have hP1 : (Psel j : ZMod 2) = (1 : ℤ) := by
    rw [ZMod.intCast_eq_intCast_iff']
    exact Int.odd_iff.mp (Psel_odd j hj)
  have hQ1 : (Qsel j : ZMod 2) = (1 : ℤ) := by
    rw [ZMod.intCast_eq_intCast_iff']
    exact Int.odd_iff.mp (Qsel_odd j hj)
  have hz : ((a + b : ℤ) : ZMod 2) = (0 : ℤ) := by
    have := congrArg (fun t : ℤ => (t : ZMod 2)) h
    have h2 : ((2 * Hj : ℤ) : ZMod 2) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨Hj, by ring⟩
    have hR : ((a * Psel j + b * Qsel j : ℤ) : ZMod 2) = ((a + b : ℤ) : ZMod 2) := by
      push_cast
      rw [hP1, hQ1]
      ring
    rw [h2, hR] at this
    exact this.symm
  have hmod : (a + b) % 2 = 0 := by
    have := (ZMod.intCast_eq_intCast_iff' (a + b) 0 2).mp hz
    simpa using this
  exact Int.even_iff.mpr hmod

/-- 前向方向：x,y∈F 且缺陷尾相同 ⇒ x−y∈L。 -/
theorem theorem9_forward {x y : ℝ} (hx : inF x) (hy : inF y)
    (h : sameTail (defect x) (defect y)) : x - y ∈ latticeL := by
  have hrec := (homogeneous_recurrence_iff x y).mp h
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hrec
  let N := max N0 2
  have hrecN : ∀ j : ℕ, N ≤ j → homogeneousRec (fun k => Msel x k - Msel y k) j := by
    intro j hj
    exact hN0 j (le_trans (le_max_left N0 2) hj)
  have hN2 : 2 ≤ N := le_max_right N0 2
  obtain ⟨a, b, hab0, hab1⟩ := cramer_two_int N (by omega)
    (Msel x N - Msel y N) (Msel x (N + 1) - Msel y (N + 1))
  have hprop : ∀ j : ℕ, N ≤ j → 2 * (Msel x j - Msel y j) = a * Psel j + b * Qsel j :=
    propagate_homogeneous (fun k => Msel x k - Msel y k) a b N hN2 hrecN hab0 hab1
  have hlim := limit_two_diff x y hx hy a b N hprop
  have heven : Even (a + b) := parity_even_sum N (by omega) a b (Msel x N - Msel y N) hab0
  obtain ⟨t, ht⟩ := heven
  use (t - a), a
  have hb : b = 2 * t - a := by linarith
  have h2 : 2 * (x - y) = (a : ℝ) * exp 1 + (b : ℝ) := hlim
  rw [hb] at h2
  push_cast at h2 ⊢
  linarith

/-- K_j = mQ_j + n(P_j+Q_j)/2。 -/
def Kshift (m n : ℤ) (j : ℕ) : ℤ :=
  m * Qsel j + n * ((Psel j + Qsel j) / 2)

/-- P_j+Q_j 偶（j≥1）。 -/
lemma PQ_sum_even (j : ℕ) (hj : 1 ≤ j) : Even (Psel j + Qsel j) :=
  (Psel_odd j hj).add_odd (Qsel_odd j hj)

lemma two_mul_Kshift_half (j : ℕ) (hj : 1 ≤ j) :
    2 * ((Psel j + Qsel j) / 2) = Psel j + Qsel j := by
  have hdvd : (2 : ℤ) ∣ Psel j + Qsel j := (PQ_sum_even j hj).two_dvd
  have h := Int.ediv_mul_cancel hdvd
  linarith

/-- K_j 满足齐次递推（j≥2）。 -/
lemma Kshift_homogeneous (m n : ℤ) (j : ℕ) (hj : 2 ≤ j) :
    homogeneousRec (Kshift m n) j := by
  simp only [Kshift, homogeneousRec]
  have hP := Psel_rec j hj
  have hQ := Qsel_rec j hj
  have hhalf_j : 2 * ((Psel j + Qsel j) / 2) = Psel j + Qsel j := two_mul_Kshift_half j (by omega)
  have hhalf_jp : 2 * ((Psel (j + 1) + Qsel (j + 1)) / 2) = Psel (j + 1) + Qsel (j + 1) :=
    two_mul_Kshift_half (j + 1) (by omega)
  have hhalf_jm : 2 * ((Psel (j - 1) + Qsel (j - 1)) / 2) = Psel (j - 1) + Qsel (j - 1) :=
    two_mul_Kshift_half (j - 1) (by omega)
  have h2 : 2 * (m * Qsel (j + 1) + n * ((Psel (j + 1) + Qsel (j + 1)) / 2)) =
      2 * ((4 * (j : ℤ) + 2) * (m * Qsel j + n * ((Psel j + Qsel j) / 2)) +
        (m * Qsel (j - 1) + n * ((Psel (j - 1) + Qsel (j - 1)) / 2))) := by
    have hL : 2 * (m * Qsel (j + 1) + n * ((Psel (j + 1) + Qsel (j + 1)) / 2)) =
        2 * m * Qsel (j + 1) + n * (Psel (j + 1) + Qsel (j + 1)) := by
      linear_combination n * hhalf_jp
    have hR : 2 * ((4 * (j : ℤ) + 2) * (m * Qsel j + n * ((Psel j + Qsel j) / 2)) +
        (m * Qsel (j - 1) + n * ((Psel (j - 1) + Qsel (j - 1)) / 2))) =
        (4 * (j : ℤ) + 2) * (2 * m * Qsel j + n * (Psel j + Qsel j)) +
          (2 * m * Qsel (j - 1) + n * (Psel (j - 1) + Qsel (j - 1))) := by
      linear_combination (4 * (j : ℤ) + 2) * n * hhalf_j + n * hhalf_jm
    rw [hL, hR, hP, hQ]
    ring
  exact Int.eq_of_mul_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0) h2

/-- 反向方向：x,y∈F 且 x−y∈L ⇒ 缺陷尾相同。 -/
theorem theorem9_converse {x y : ℝ} (hx : inF x) (hy : inF y)
    (h : x - y ∈ latticeL) : sameTail (defect x) (defect y) := by
  obtain ⟨m, n, hmn⟩ := h
  have hKrec : ∀ j : ℕ, 2 ≤ j → homogeneousRec (Kshift m n) j := Kshift_homogeneous m n
  have hres : ∀ j : ℕ, 1 ≤ j →
      (Qsel j : ℝ) * x - ((Msel y j + Kshift m n j : ℤ) : ℝ) =
        epsSel y j + (n : ℝ) * deltaSel j / 2 := by
    intro j hj
    have hxy : x = y + (m : ℝ) + (n : ℝ) * (exp 1 + 1) / 2 := by linarith
    have hhalf : (2 : ℝ) * (((Psel j + Qsel j) / 2 : ℤ) : ℝ) =
        (Psel j : ℝ) + (Qsel j : ℝ) := by
      have := two_mul_Kshift_half j hj
      push_cast at this ⊢
      exact_mod_cast this
    have hK : (Kshift m n j : ℝ) = (m : ℝ) * (Qsel j : ℝ) +
        (n : ℝ) * ((Psel j : ℝ) + (Qsel j : ℝ)) / 2 := by
      simp only [Kshift]
      push_cast
      have hhalf' : (((Psel j + Qsel j) / 2 : ℤ) : ℝ) =
          ((Psel j : ℝ) + (Qsel j : ℝ)) / 2 := by
        have := hhalf
        linarith
      rw [hhalf']
      ring
    have hcast : ((Msel y j + Kshift m n j : ℤ) : ℝ) =
        (Msel y j : ℝ) + (Kshift m n j : ℝ) := by push_cast; ring
    rw [hxy, hcast, hK]
    simp only [epsSel, deltaSel, Msel]
    ring
  have hres0 : Tendsto (fun j : ℕ => epsSel y j + (n : ℝ) * deltaSel j / 2) atTop (nhds 0) := by
    have hεy := epsSel_tendsto_zero_of_inF hy
    have hδ : Tendsto (fun j : ℕ => (n : ℝ) * deltaSel j / 2) atTop (nhds 0) := by
      have := (deltaSel_tendsto_zero.const_mul (n : ℝ)).div_const 2
      convert this using 1; ext j; ring
    have := hεy.add hδ
    convert this using 1; ext j; ring
  have hnearest : ∀ᶠ j : ℕ in atTop, Msel x j = Msel y j + Kshift m n j := by
    have hsmall : ∀ᶠ j : ℕ in atTop,
        |(Qsel j : ℝ) * x - ((Msel y j + Kshift m n j : ℤ) : ℝ)| < 1 / 2 := by
      have := (Metric.tendsto_nhds.mp hres0) (1 / 2) (by norm_num)
      filter_upwards [this, eventually_ge_atTop 1] with j hj hj1
      have hr := hres j hj1
      rw [hr]
      simpa [Real.dist_eq, abs_sub_comm] using hj
    filter_upwards [hsmall, eventually_ge_atTop 1] with j hj hj1
    have hround : round ((Qsel j : ℝ) * x) = Msel y j + Kshift m n j := by
      rw [round_eq_iff]
      constructor <;> linarith [abs_lt.mp hj]
    exact hround
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnearest
  refine (eventually_ge_atTop (max N 2 + 1)).mono ?_
  intro j hj
  have hjN : N ≤ j := by omega
  have hjNp : N ≤ j + 1 := by omega
  have hjNm : N ≤ j - 1 := by omega
  have hj2 : 2 ≤ j := by omega
  have hj_eq := hN j hjN
  have hjp_eq := hN (j + 1) hjNp
  have hjm_eq := hN (j - 1) hjNm
  simp only [defect, hj_eq, hjp_eq, hjm_eq]
  have hK := Kshift_homogeneous m n j hj2
  simp only [homogeneousRec] at hK
  linarith

/-- **Theorem 9**：x,y∈F ⇒ 缺陷尾相同 ⇔ x−y∈L。 -/
theorem theorem9_tail_iff {x y : ℝ} (hx : inF x) (hy : inF y) :
    sameTail (defect x) (defect y) ↔ x - y ∈ latticeL :=
  ⟨theorem9_forward hx hy, theorem9_converse hx hy⟩

/-! ## 第四部分：Corollary 10、精细尺度与反例 -/

/-- 平移保 F。 -/
theorem translation_preserves_F {x : ℝ} (hx : inF x) {ℓ : ℝ} (hℓ : ℓ ∈ latticeL) :
    inF (x + ℓ) := by
  obtain ⟨m, n, hmn⟩ := hℓ
  obtain ⟨C, hC⟩ := hx
  have hjδ : Tendsto (fun j : ℕ => (j : ℝ) * deltaSel j) atTop (nhds 0) := jdeltaSel_tendsto_zero
  have hjδ_bdd : ∃ D : ℝ, ∀ᶠ j : ℕ in atTop, |(j : ℝ) * deltaSel j| ≤ D := by
    have := (Metric.tendsto_nhds.mp hjδ) 1 (by norm_num)
    refine ⟨1, ?_⟩
    filter_upwards [this] with j hj
    have : |(j : ℝ) * deltaSel j| < 1 := by simpa [Real.dist_eq] using hj
    linarith
  obtain ⟨D, hD⟩ := hjδ_bdd
  use C + |n| * D / 2 + 1
  filter_upwards [hC, hD, eventually_ge_atTop 1] with j hjC hjD hj1
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hdist : |epsSel (x + ℓ) j| ≤ |epsSel x j + (n : ℝ) * deltaSel j / 2| := by
    have hhalf : (2 : ℝ) * (((Psel j + Qsel j) / 2 : ℤ) : ℝ) =
        (Psel j : ℝ) + (Qsel j : ℝ) := by
      have := two_mul_Kshift_half j hj1
      push_cast at this ⊢
      exact_mod_cast this
    have hcand : (Qsel j : ℝ) * (x + ℓ) - ((Msel x j + Kshift m n j : ℤ) : ℝ) =
        epsSel x j + (n : ℝ) * deltaSel j / 2 := by
      simp only [epsSel, Kshift, deltaSel, Msel]
      rw [hmn]
      push_cast
      linear_combination (-(n : ℝ) / 2) * hhalf
    have hround : |epsSel (x + ℓ) j| ≤
        |(Qsel j : ℝ) * (x + ℓ) - ((Msel x j + Kshift m n j : ℤ) : ℝ)| := by
      simp only [epsSel, Msel]
      exact round_le _ _
    rw [hcand] at hround
    exact hround
  have habsplit : |(n : ℝ) * deltaSel j / 2| = |n| * |deltaSel j| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    <;> push_cast <;> ring
  have hjδ' : (j : ℝ) * |deltaSel j| ≤ D := by
    have : (j : ℝ) * |deltaSel j| = |(j : ℝ) * deltaSel j| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ))]
    rw [this]
    exact hjD
  calc (j : ℝ) * |epsSel (x + ℓ) j|
      ≤ (j : ℝ) * |epsSel x j + (n : ℝ) * deltaSel j / 2| := by gcongr
    _ ≤ (j : ℝ) * (|epsSel x j| + |(n : ℝ) * deltaSel j / 2|) := by
        gcongr; exact abs_add_le _ _
    _ = (j : ℝ) * |epsSel x j| + (j : ℝ) * |(n : ℝ) * deltaSel j / 2| := by ring
    _ = (j : ℝ) * |epsSel x j| + |n| * ((j : ℝ) * |deltaSel j|) / 2 := by
        rw [habsplit]; ring
    _ ≤ C + |n| * D / 2 := by
        have h1 : (j : ℝ) * |epsSel x j| ≤ C := hjC
        have h2 : |n| * ((j : ℝ) * |deltaSel j|) / 2 ≤ |n| * D / 2 := by
          gcongr
        linarith
    _ ≤ C + |n| * D / 2 + 1 := by linarith

/-- 有界整数序列（最终有界）。 -/
def boundedIntSeq (d : ℕ → ℤ) : Prop := ∃ K : ℤ, ∀ᶠ j : ℕ in atTop, |d j| ≤ K

/-- 缺陷尾映射良定义。 -/
theorem defect_bounded {x : ℝ} (hx : inF x) : boundedIntSeq (defect x) :=
  defect_bounded_of_inF hx

/-- **Corollary 10（单射部分）**。满射依赖 S5 Theorem 8，此处只证单射。 -/
theorem corollary10_injective {x y : ℝ} (hx : inF x) (hy : inF y) :
    sameTail (defect x) (defect y) → x - y ∈ latticeL :=
  theorem9_forward hx hy

/-- 商集核 = L 关系。 -/
theorem corollary10_ker {x y : ℝ} (hx : inF x) (hy : inF y) :
    sameTail (defect x) (defect y) ↔ x - y ∈ latticeL :=
  theorem9_tail_iff hx hy

/-- D 组缺陷与本文件缺陷同源（Mseq = Msel = round(Qsel·x)）。 -/
lemma defect_bridge (x : ℝ) (j : ℕ) :
    SignedClusters.defect x j = defect x j := by
  simp only [SignedClusters.defect, SignedClusters.Mseq, defect, Msel]

/-- **Corollary 10（满射部分）**：任意最终有界整数序列可实现为某 F 中实数的缺陷尾。
    调用 D 组 theorem8_realization 的构造 xOfSeq，证其属于 F 并桥接缺陷定义。 -/
theorem corollary10_surjective (d : ℕ → ℤ) (K : ℕ) (hK : ∀ j ≥ 2, |d j| ≤ K) :
    ∃ x : ℝ, inF x ∧ sameTail (defect x) d := by
  use SignedClusters.xOfSeq d
  constructor
  · -- inF：j·|epsSel| 最终有界（界 K）
    have hres := SignedClusters.residual_bound_d d K hK
    obtain ⟨N, hN⟩ := SignedClusters.eventually_nearest_d d K hK
    use (K : ℝ)
    filter_upwards [eventually_ge_atTop (max N 2)] with j hj
    have hjN : N ≤ j := by omega
    have hj2 : 2 ≤ j := by omega
    have hMj : Msel (SignedClusters.xOfSeq d) j = SignedClusters.Md d j := by
      simpa [Msel, SignedClusters.Mseq] using hN j hjN
    have heps : |epsSel (SignedClusters.xOfSeq d) j| =
        |(Qsel j : ℝ) * SignedClusters.xOfSeq d - (SignedClusters.Md d j : ℝ)| := by
      simp only [epsSel]
      rw [hMj]
    rw [heps]
    have hres' : |(Qsel j : ℝ) * SignedClusters.xOfSeq d - (SignedClusters.Md d j : ℝ)| ≤
        4 * (K : ℝ) / (4 * (j : ℝ) + 2) := hres j hj2
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    calc (j : ℝ) * |(Qsel j : ℝ) * SignedClusters.xOfSeq d - (SignedClusters.Md d j : ℝ)|
        ≤ (j : ℝ) * (4 * (K : ℝ) / (4 * (j : ℝ) + 2)) := by gcongr
      _ = 4 * (K : ℝ) * (j : ℝ) / (4 * (j : ℝ) + 2) := by ring
      _ ≤ (K : ℝ) := by
        have hden : (0 : ℝ) < 4 * (j : ℝ) + 2 := by positivity
        rw [div_le_iff₀ hden]
        nlinarith
  · -- sameTail：桥接 D 缺陷 = 本文件缺陷，用 defect_eq_d
    obtain ⟨N, hN⟩ := SignedClusters.defect_eq_d d K hK
    filter_upwards [eventually_ge_atTop N] with j hj
    rw [← defect_bridge]
    exact hN j hj

/-- 精细尺度。 -/
theorem finer_scale_ratio (r : ℤ) {x : ℝ} (hx : inF x) :
    ∀ᶠ j : ℕ in atTop, epsSel (x + (r : ℝ) * exp 1) j / deltaSel j -
      epsSel x j / deltaSel j = (r : ℝ) := by
  have hL : (r : ℝ) * exp 1 ∈ latticeL := by
    use -r, 2 * r
    push_cast
    ring
  have hK : ∀ j : ℕ, Kshift (-r) (2 * r) j = r * Psel j := by
    intro j
    simp only [Kshift]
    have hhalf : 2 * ((Psel j + Qsel j) / 2) = Psel j + Qsel j := by
      by_cases hj : 1 ≤ j
      · exact two_mul_Kshift_half j hj
      · have hj0 : j = 0 := by omega
        subst hj0
        norm_num [Psel, Qsel, selPair]
    have h2 : 2 * ((-r) * Qsel j + (2 * r) * ((Psel j + Qsel j) / 2)) =
        2 * (r * Psel j) := by
      have : 2 * ((-r) * Qsel j + (2 * r) * ((Psel j + Qsel j) / 2)) =
          -2 * r * Qsel j + 2 * r * (2 * ((Psel j + Qsel j) / 2)) := by ring
      rw [this, hhalf]
      ring
    exact Int.eq_of_mul_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0) h2
  have hres : ∀ᶠ j : ℕ in atTop, epsSel (x + (r : ℝ) * exp 1) j =
      epsSel x j + (r : ℝ) * deltaSel j := by
    have hres0 : Tendsto (fun j : ℕ => epsSel x j + (2 * r : ℝ) * deltaSel j / 2)
        atTop (nhds 0) := by
      have hεx := epsSel_tendsto_zero_of_inF hx
      have hδ : Tendsto (fun j : ℕ => (2 * r : ℝ) * deltaSel j / 2) atTop (nhds 0) := by
        have := (deltaSel_tendsto_zero.const_mul (2 * r : ℝ)).div_const 2
        convert this using 1; ext j; ring
      have := hεx.add hδ
      convert this using 1; ext j; ring
    have hsmall : ∀ᶠ j : ℕ in atTop,
        |(Qsel j : ℝ) * (x + (r : ℝ) * exp 1) -
          ((Msel x j + Kshift (-r) (2 * r) j : ℤ) : ℝ)| < 1 / 2 := by
      have := (Metric.tendsto_nhds.mp hres0) (1 / 2) (by norm_num)
      filter_upwards [this, eventually_ge_atTop 1] with j hj hj1
      have hhalf : (2 : ℝ) * (((Psel j + Qsel j) / 2 : ℤ) : ℝ) =
          (Psel j : ℝ) + (Qsel j : ℝ) := by
        have := two_mul_Kshift_half j hj1
        push_cast at this ⊢
        exact_mod_cast this
      have hcand : (Qsel j : ℝ) * (x + (r : ℝ) * exp 1) -
          ((Msel x j + Kshift (-r) (2 * r) j : ℤ) : ℝ) =
          epsSel x j + (2 * r : ℝ) * deltaSel j / 2 := by
        have hL' : (r : ℝ) * exp 1 = (-r : ℝ) + (2 * r : ℝ) * (exp 1 + 1) / 2 := by ring
        simp only [epsSel, Kshift, deltaSel, Msel]
        rw [hL']
        push_cast
        linear_combination (-(r : ℝ)) * hhalf
      rw [hcand]
      simpa [Real.dist_eq, abs_sub_comm] using hj
    have hnearest : ∀ᶠ j : ℕ in atTop,
        Msel (x + (r : ℝ) * exp 1) j = Msel x j + Kshift (-r) (2 * r) j := by
      filter_upwards [hsmall, eventually_ge_atTop 1] with j hj hj1
      simp only [Msel] at hj ⊢
      rw [round_eq_iff]
      push_cast at hj ⊢
      have habs := abs_lt.mp hj
      constructor <;> linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnearest
    refine (eventually_ge_atTop (max N 1)).mono ?_
    intro j hj
    have hjN : N ≤ j := le_trans (le_max_left N 1) hj
    have hj1 : 1 ≤ j := le_trans (le_max_right N 1) hj
    have hM := hN j hjN
    have hKj := hK j
    simp only [epsSel, deltaSel]
    rw [hM, hKj]
    push_cast
    ring
  filter_upwards [hres, eventually_ge_atTop 1] with j hj hj1
  have hδ : deltaSel j ≠ 0 := deltaSel_ne_zero j hj1
  rw [hj]
  field_simp
  ring

/-- 反例：x=6−e, y=6+e。 -/
theorem control_example :
    (∀ᶠ j : ℕ in atTop, defect (6 - exp 1) j = 0) ∧
    (∀ᶠ j : ℕ in atTop, defect (6 + exp 1) j = 0) ∧
    (∀ᶠ j : ℕ in atTop, epsSel (6 - exp 1) j / deltaSel j = (-1 : ℝ)) ∧
    (∀ᶠ j : ℕ in atTop, epsSel (6 + exp 1) j / deltaSel j = (1 : ℝ)) := by
  have hxL : (6 - exp 1 : ℝ) ∈ latticeL := by
    use 7, -2
    ring
  have hyL : (6 + exp 1 : ℝ) ∈ latticeL := by
    use 5, 2
    ring
  have h0F : inF (0 : ℝ) := by
    use 0
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hM : Msel 0 j = 0 := by simp [Msel]
    simp [epsSel, hM]
  have hxF : inF (6 - exp 1) := by
    have := translation_preserves_F h0F hxL
    simpa using this
  have hyF : inF (6 + exp 1) := by
    have := translation_preserves_F h0F hyL
    simpa using this
  have h0def : ∀ᶠ j : ℕ in atTop, defect (0 : ℝ) j = 0 := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hM : ∀ k : ℕ, Msel 0 k = 0 := by intro k; simp [Msel]
    simp [defect, hM]
  have hxL0 : (6 - exp 1 : ℝ) - 0 ∈ latticeL := by simpa using hxL
  have hyL0 : (6 + exp 1 : ℝ) - 0 ∈ latticeL := by simpa using hyL
  have hxdef : ∀ᶠ j : ℕ in atTop, defect (6 - exp 1) j = 0 := by
    have htail := theorem9_converse hxF h0F hxL0
    filter_upwards [htail, h0def] with j hj h0
    linarith
  have hydef : ∀ᶠ j : ℕ in atTop, defect (6 + exp 1) j = 0 := by
    have htail := theorem9_converse hyF h0F hyL0
    filter_upwards [htail, h0def] with j hj h0
    linarith
  have hxr : ∀ᶠ j : ℕ in atTop, epsSel (6 - exp 1) j / deltaSel j = (-1 : ℝ) := by
    have := finer_scale_ratio (-1) h0F
    filter_upwards [this] with j hj
    have h6 : (6 - exp 1 : ℝ) = (0 : ℝ) + (-1 : ℝ) * exp 1 + 6 := by ring
    have hε0 : epsSel (0 : ℝ) j = 0 := by
      have hM : Msel 0 j = 0 := by simp [Msel]
      simp [epsSel, hM]
    have hshift : epsSel (6 - exp 1) j = epsSel ((-1 : ℝ) * exp 1) j := by
      have hM : Msel (6 - exp 1) j = Msel ((-1 : ℝ) * exp 1) j + 6 * Qsel j := by
        simp only [Msel]
        have h6 : (6 - exp 1 : ℝ) = (-1 : ℝ) * exp 1 + 6 := by ring
        rw [h6]
        have hcast : (Qsel j : ℝ) * ((-1 : ℝ) * exp 1 + 6) =
            (Qsel j : ℝ) * ((-1 : ℝ) * exp 1) + (6 * Qsel j : ℤ) := by
          push_cast; ring
        rw [hcast, round_add_intCast]
        <;> push_cast <;> ring
      simp only [epsSel, hM]
      push_cast
      ring
    rw [hshift]
    have := hj
    simp only [hε0, sub_zero] at this
    have h0e : (0 : ℝ) + (-1 : ℝ) * exp 1 = (-1 : ℝ) * exp 1 := by ring
    simpa [h0e] using this
  have hyr : ∀ᶠ j : ℕ in atTop, epsSel (6 + exp 1) j / deltaSel j = (1 : ℝ) := by
    have := finer_scale_ratio 1 h0F
    filter_upwards [this] with j hj
    have hε0 : epsSel (0 : ℝ) j = 0 := by
      have hM : Msel 0 j = 0 := by simp [Msel]
      simp [epsSel, hM]
    have hshift : epsSel (6 + exp 1) j = epsSel ((1 : ℝ) * exp 1) j := by
      have hM : Msel (6 + exp 1) j = Msel ((1 : ℝ) * exp 1) j + 6 * Qsel j := by
        simp only [Msel]
        have h6 : (6 + exp 1 : ℝ) = (1 : ℝ) * exp 1 + 6 := by ring
        rw [h6]
        have hcast : (Qsel j : ℝ) * ((1 : ℝ) * exp 1 + 6) =
            (Qsel j : ℝ) * ((1 : ℝ) * exp 1) + (6 * Qsel j : ℤ) := by
          push_cast; ring
        rw [hcast, round_add_intCast]
        <;> push_cast <;> ring
      simp only [epsSel, hM]
      push_cast
      ring
    rw [hshift]
    have := hj
    simp only [hε0, sub_zero] at this
    have h0e : (0 : ℝ) + (1 : ℝ) * exp 1 = (1 : ℝ) * exp 1 := by ring
    simpa [h0e] using this
  exact ⟨hxdef, hydef, hxr, hyr⟩

end

/-! ## 公理审计 -/

#print axioms Qsel_pos
#print axioms Psel_rec
#print axioms Qsel_rec
#print axioms sel_determinant
#print axioms Psel_odd
#print axioms Qsel_odd
#print axioms Qsel_double
#print axioms Qsel_succ_coprime
#print axioms Qsel_tendsto_atTop
#print axioms Psel_div_Qsel_tendsto_exp
#print axioms deltaSel_ne_zero
#print axioms jdeltaSel_tendsto_zero
#print axioms defect_identity
#print axioms homogeneous_recurrence_iff
#print axioms epsSel_tendsto_zero_of_inF
#print axioms defect_bounded_of_inF
#print axioms cramer_two_int
#print axioms propagate_homogeneous
#print axioms limit_two_diff
#print axioms parity_even_sum
#print axioms theorem9_forward
#print axioms Kshift_homogeneous
#print axioms theorem9_converse
#print axioms theorem9_tail_iff
#print axioms translation_preserves_F
#print axioms defect_bounded
#print axioms corollary10_injective
#print axioms corollary10_ker
#print axioms finer_scale_ratio
#print axioms control_example

end DefectFibres