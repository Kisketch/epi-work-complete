import Mathlib
import EpiFormal.Measure
import EpiFormal.MeiburgConvergence
import EpiFormal.Alekseyev
import EpiFormal.PadeODE
import EpiFormal.PadeDeriv
import EpiFormal.PadeBoundary
import EpiFormal.PadeRecurrence
import EpiFormal.PadeIntegral

/-!
# 子任务 A：e 的选定收敛子地基（EulerConvergents）

本文件是「e+π 研究并发形式化」的子任务 A，形式化 e 的正则连分数
`[2;1,2,1,1,4,1,1,6,...]` 中、位于每个部分商 `2j` **之前**的那个收敛子
`P_j/Q_j`（j≥1），前三个为 `3/1, 19/7, 193/71`。

**范围声明**：e+π 无理性仍是开放问题。本文件只机器验证整数递推基础设施，
并把两条经典 e 连分数分析性质作为显式公理引入；不声称、也不暗示解决该开放问题。

## 可信度分层
- **机器验证**：Psel/Qsel 的递推、行列式、奇偶、严格单调、倍增、相邻互素，
  以及由公理推导的 `Psel_div_Qsel_tendsto_exp`、`Qsel_tendsto_atTop`。
- **公理化（未验证）**：`deltaSel_tendsto_zero`、`abs_deltaSel_lt`。
  mathlib v4.35.0 无 e 的连分数展开定理（全库无 `sfrac`/`SimpleContinuedFraction`，
  `Mathlib/Algebra/ContinuedFractions/Euler.lean` 是广义连分数的 Euler *变换*，非 e 展开）。
- 本文件无纸面/数值辅助结论；全部真证或显式公理，零 sorry。

## 下标约定
`Psel`/`Qsel` 用 ℕ 下标，j≥1 有效。下标 0 为任意占位（Psel 0 = 1, Qsel 0 = 1），
仅用于让配对原始递归在 j=1 处闭合（Q_2 = 6·Q_1 + Q_0 = 6·1 + 1 = 7），
不参与任何 j≥1 的结论。注意 Qsel 0 必须取 1 而非 0，否则 Q_2 会算成 6。

## 构造
用「双步配对」原始递归 `selPair j = (X_j, X_{j+1})`：
`selPair 0 = (X_0, X_1)`，`selPair (n+1) = (b, (4(n+1)+2)*b + a)`，其中 `selPair n = (a,b)`。
于是 `selPair j = (X_j, X_{j+1})`，递推方程对 j≥1 由 `rfl` 直接得到，避免 well-founded 展开。
-/

open Filter Topology Real Set

/-- 配对原始递归：`selPair p0 p1 j = (X_j, X_{j+1})`。 -/
def selPair (p0 p1 : ℤ) : ℕ → ℤ × ℤ
  | 0 => (p0, p1)
  | n + 1 =>
    let prev := selPair p0 p1 n
    (prev.2, (4 * ((n + 1 : ℕ) : ℤ) + 2) * prev.2 + prev.1)

@[simp] lemma selPair_zero (p0 p1 : ℤ) : selPair p0 p1 0 = (p0, p1) := rfl

lemma selPair_succ (p0 p1 : ℤ) (n : ℕ) :
    selPair p0 p1 (n + 1) =
      ((selPair p0 p1 n).2,
       (4 * ((n + 1 : ℕ) : ℤ) + 2) * (selPair p0 p1 n).2 + (selPair p0 p1 n).1) := rfl

/-- 选定收敛子分子：3, 19, 193, 2721, ...（j≥1）。下标 0 占位为 1。 -/
def Psel (j : ℕ) : ℤ := (selPair 1 3 j).1

/-- 选定收敛子分母：1, 7, 71, 1001, ...（j≥1）。下标 0 占位为 1。 -/
def Qsel (j : ℕ) : ℤ := (selPair 1 1 j).1

@[simp] lemma Psel_zero : Psel 0 = 1 := rfl
@[simp] lemma Qsel_zero : Qsel 0 = 1 := rfl
@[simp] lemma Psel_one : Psel 1 = 3 := rfl
@[simp] lemma Qsel_one : Qsel 1 = 1 := rfl
@[simp] lemma Psel_two : Psel 2 = 19 := rfl
@[simp] lemma Qsel_two : Qsel 2 = 7 := rfl

/-- 第二分量即下一项：`(selPair p0 p1 j).2 = X_{j+1}`。 -/
lemma selPair_snd (p0 p1 : ℤ) (j : ℕ) :
    (selPair p0 p1 j).2 = (selPair p0 p1 (j + 1)).1 := by
  cases j <;> rfl

lemma Psel_succ_eq (j : ℕ) : Psel (j + 1) = (selPair 1 3 j).2 := (selPair_snd 1 3 j).symm
lemma Qsel_succ_eq (j : ℕ) : Qsel (j + 1) = (selPair 1 1 j).2 := (selPair_snd 1 1 j).symm

/-- 核心递推（对一切 j 成立，含 j=0，因配对构造闭合）：
    `X_{j+2} = (4(j+1)+2) X_{j+1} + X_j`。 -/
lemma selPair_rec (p0 p1 : ℤ) (j : ℕ) :
    (selPair p0 p1 (j + 2)).1 =
      (4 * ((j + 1 : ℕ) : ℤ) + 2) * (selPair p0 p1 (j + 1)).1 + (selPair p0 p1 j).1 := by
  have h := congrArg Prod.fst (selPair_succ p0 p1 (j + 1))
  -- h : (selPair (j+2)).1 = (4*(j+2)+2)*(selPair (j+1)).2 + (selPair (j+1)).1
  rw [selPair_snd p0 p1 (j + 1)] at h
  exact h

/-- P 递推（契约形式，j≥2）。 -/
lemma Psel_rec (j : ℕ) (hj : 2 ≤ j) :
    Psel (j + 1) = (4 * (j : ℤ) + 2) * Psel j + Psel (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have h := selPair_rec 1 3 (k + 1)
  simp only [Psel] at h ⊢
  convert h using 1
  push_cast
  ring

/-- Q 递推（契约形式，j≥2）。 -/
lemma Qsel_rec (j : ℕ) (hj : 2 ≤ j) :
    Qsel (j + 1) = (4 * (j : ℤ) + 2) * Qsel j + Qsel (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have h := selPair_rec 1 1 (k + 1)
  simp only [Qsel] at h ⊢
  convert h using 1
  push_cast
  ring

/-! ## 配对归纳：一次性建立正性、奇性 -/

/-- 对 p0,p1>0 且奇，配对所有分量正且奇。 -/
lemma selPair_pos_odd (p0 p1 : ℤ) (hp0 : 0 < p0) (hp1 : 0 < p1)
    (ho0 : Odd p0) (ho1 : Odd p1) :
    ∀ j, 0 < (selPair p0 p1 j).1 ∧ 0 < (selPair p0 p1 j).2 ∧
      Odd (selPair p0 p1 j).1 ∧ Odd (selPair p0 p1 j).2 := by
  intro j
  induction j with
  | zero => simp [hp0, hp1, ho0, ho1]
  | succ n ih =>
    obtain ⟨ha1, ha2, ho1', ho2'⟩ := ih
    simp only [selPair_succ]
    refine ⟨ha2, ?_, ho2', ?_⟩
    · have hc : (0 : ℤ) < 4 * ((n + 1 : ℕ) : ℤ) + 2 := by positivity
      exact add_pos (mul_pos hc ha2) ha1
    · have he : Even (4 * ((n + 1 : ℕ) : ℤ) + 2) := by
        use 2 * ((n + 1 : ℕ) : ℤ) + 1; ring
      exact (he.mul_right _).add_odd ho1'

lemma Qsel_pos (j : ℕ) (_hj : 1 ≤ j) : 0 < Qsel j :=
  (selPair_pos_odd 1 1 (by norm_num) (by norm_num) odd_one odd_one j).1

lemma Qsel_odd (j : ℕ) (_hj : 1 ≤ j) : Odd (Qsel j) :=
  (selPair_pos_odd 1 1 (by norm_num) (by norm_num) odd_one odd_one j).2.2.1

lemma Psel_odd (j : ℕ) (_hj : 1 ≤ j) : Odd (Psel j) :=
  (selPair_pos_odd 1 3 (by norm_num) (by norm_num) odd_one (by decide : Odd (3 : ℤ)) j).2.2.1

/-! ## 行列式（先证无前提的偏移形式，再包装契约） -/

lemma sel_det_shift (k : ℕ) :
    Psel (k + 1) * Qsel (k + 2) - Psel (k + 2) * Qsel (k + 1) =
      2 * (-1 : ℤ) ^ (k + 2) := by
  induction k with
  | zero => norm_num [Psel, Qsel, selPair]
  | succ n ih =>
    have hP : Psel (n + 3) =
        (4 * ((n + 2 : ℕ) : ℤ) + 2) * Psel (n + 2) + Psel (n + 1) := by
      have := selPair_rec 1 3 (n + 1); simpa only [Psel] using this
    have hQ : Qsel (n + 3) =
        (4 * ((n + 2 : ℕ) : ℤ) + 2) * Qsel (n + 2) + Qsel (n + 1) := by
      have := selPair_rec 1 1 (n + 1); simpa only [Qsel] using this
    have hstep :
        Psel (n + 2) * Qsel (n + 3) - Psel (n + 3) * Qsel (n + 2) =
          -(Psel (n + 1) * Qsel (n + 2) - Psel (n + 2) * Qsel (n + 1)) := by
      rw [hP, hQ]; ring
    have hpow : (-1 : ℤ) ^ (n + 3) = -((-1 : ℤ) ^ (n + 2)) := by
      rw [show (n + 3 : ℕ) = (n + 2) + 1 by omega, pow_succ]; ring
    calc Psel (n + 2) * Qsel (n + 3) - Psel (n + 3) * Qsel (n + 2)
        = -(Psel (n + 1) * Qsel (n + 2) - Psel (n + 2) * Qsel (n + 1)) := hstep
      _ = -(2 * (-1 : ℤ) ^ (n + 2)) := by rw [ih]
      _ = 2 * (-1 : ℤ) ^ (n + 3) := by rw [hpow]; ring

/-- 相邻行列式：`P_j Q_{j+1} − P_{j+1} Q_j = 2·(−1)^{j+1}`（j≥1）。 -/
lemma sel_determinant (j : ℕ) (hj : 1 ≤ j) :
    Psel j * Qsel (j + 1) - Psel (j + 1) * Qsel j = 2 * (-1 : ℤ) ^ (j + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact sel_det_shift k

/-- Q 逐点严格增（j≥1）。 -/
lemma Qsel_lt_succ (j : ℕ) (hj : 1 ≤ j) : Qsel j < Qsel (j + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hrec : Qsel (k + 2) =
      (4 * ((k + 1 : ℕ) : ℤ) + 2) * Qsel (k + 1) + Qsel k := by
    have := selPair_rec 1 1 k; simpa only [Qsel] using this
  have hpos1 : 0 < Qsel (k + 1) := Qsel_pos (k + 1) (by omega)
  have hc : (1 : ℤ) < 4 * ((k + 1 : ℕ) : ℤ) + 2 := by
    have : (0 : ℤ) ≤ (k + 1 : ℕ) := by positivity
    linarith
  have hgt : Qsel (k + 1) < (4 * ((k + 1 : ℕ) : ℤ) + 2) * Qsel (k + 1) := by
    have := mul_lt_mul_of_pos_right hc hpos1
    simpa using this
  have hpos0 : 0 < Qsel k :=
    (selPair_pos_odd 1 1 (by norm_num) (by norm_num) odd_one odd_one k).1
  linarith

lemma Qsel_strictMono : StrictMonoOn Qsel (Set.Ici 1) := by
  apply strictMonoOn_of_lt_succ Set.ordConnected_Ici
  intro a _ ha _
  have ha1 : 1 ≤ a := ha
  simpa using Qsel_lt_succ a ha1

/-- Q 倍增（j≥2）：`2 Qsel j ≤ Qsel (j+1)`（实际 ≥10 Qsel j）。 -/
lemma Qsel_double (j : ℕ) (hj : 2 ≤ j) : 2 * Qsel j ≤ Qsel (j + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have hrec : Qsel (k + 3) =
      (4 * ((k + 2 : ℕ) : ℤ) + 2) * Qsel (k + 2) + Qsel (k + 1) := by
    have := selPair_rec 1 1 (k + 1); simpa only [Qsel] using this
  have hpos : 0 < Qsel (k + 2) := Qsel_pos (k + 2) (by omega)
  have hpos0 : 0 < Qsel (k + 1) := Qsel_pos (k + 1) (by omega)
  have hc : (2 : ℤ) ≤ 4 * ((k + 2 : ℕ) : ℤ) + 2 := by
    have : (0 : ℤ) ≤ (k + 2 : ℕ) := by positivity
    linarith
  have hge : 2 * Qsel (k + 2) ≤ (4 * ((k + 2 : ℕ) : ℤ) + 2) * Qsel (k + 2) :=
    mul_le_mul_of_nonneg_right hc (le_of_lt hpos)
  linarith

/-! ## 相邻互素（先证无前提偏移形式，再包装契约） -/

lemma Qsel_coprime_shift (k : ℕ) : Int.gcd (Qsel (k + 1)) (Qsel (k + 2)) = 1 := by
  induction k with
  | zero => norm_num [Qsel, selPair]
  | succ n ih =>
    have hrec : Qsel (n + 3) =
        (4 * ((n + 2 : ℕ) : ℤ) + 2) * Qsel (n + 2) + Qsel (n + 1) := by
      have := selPair_rec 1 1 (n + 1); simpa only [Qsel] using this
    show Int.gcd (Qsel (n + 2)) (Qsel (n + 3)) = 1
    rw [hrec, mul_comm ((4 * ((n + 2 : ℕ) : ℤ) + 2)) (Qsel (n + 2)),
      add_comm (Qsel (n + 2) * (4 * ((n + 2 : ℕ) : ℤ) + 2)) (Qsel (n + 1)),
      Int.gcd_add_mul_left_right, Int.gcd_comm]
    exact ih

/-- 相邻 Q 互素（j≥1）：`gcd(Qsel j, Qsel (j+1)) = 1`。
    **关键**：行列式是 ±2 而非 ±1，故不能从行列式直接得互素；
    走 Q 自身递推 `gcd(Q_{j+1},Q_j)=gcd(Q_{j-1},Q_j)`，归纳到 gcd(Q_1,Q_2)=gcd(1,7)=1。 -/
lemma Qsel_succ_coprime (j : ℕ) (hj : 1 ≤ j) : Int.gcd (Qsel j) (Qsel (j + 1)) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact Qsel_coprime_shift k

/-! ## δ 与分析性质（公理化部分） -/

/-- δ_j = Q_j·e − P_j。 -/
noncomputable def deltaSel (j : ℕ) : ℝ := (Qsel j : ℝ) * Real.exp 1 - (Psel j : ℝ)

/-- 全下标倍增：`2·Qsel(j+1) ≤ Qsel(j+2)` 对一切 j 成立（递推系数≥6，Qsel 恒正）。 -/
lemma Qsel_double_all (j : ℕ) : 2 * Qsel (j + 1) ≤ Qsel (j + 2) := by
  have hrec : Qsel (j + 2) =
      (4 * ((j + 1 : ℕ) : ℤ) + 2) * Qsel (j + 1) + Qsel j := by
    have := selPair_rec 1 1 j; simpa only [Qsel] using this
  have hpos : 0 < Qsel (j + 1) :=
    (selPair_pos_odd 1 1 (by norm_num) (by norm_num) odd_one odd_one (j + 1)).1
  have hpos0 : 0 ≤ Qsel j :=
    le_of_lt (selPair_pos_odd 1 1 (by norm_num) (by norm_num) odd_one odd_one j).1
  have hc : (2 : ℤ) ≤ 4 * ((j + 1 : ℕ) : ℤ) + 2 := by
    have : (0 : ℤ) ≤ (j + 1 : ℕ) := by positivity
    linarith
  have hge : 2 * Qsel (j + 1) ≤ (4 * ((j + 1 : ℕ) : ℤ) + 2) * Qsel (j + 1) :=
    mul_le_mul_of_nonneg_right hc (le_of_lt hpos)
  rw [hrec]
  linarith

/-- Q_j ≥ j（j≥1），几何增长的线性下界。 -/
lemma Qsel_ge_index (k : ℕ) : (k + 1 : ℤ) ≤ Qsel (k + 1) := by
  induction k with
  | zero => norm_num [Qsel, selPair]
  | succ n ih =>
    have hdbl : 2 * Qsel (n + 1) ≤ Qsel (n + 2) := Qsel_double_all n
    have h3 : 2 * (n + 1 : ℤ) ≤ 2 * Qsel (n + 1) :=
      mul_le_mul_of_nonneg_left ih (by norm_num)
    have h4 : (n + 2 : ℤ) ≤ 2 * (n + 1 : ℤ) := by linarith
    show (n + 2 : ℤ) ≤ Qsel (n + 2)
    exact le_trans h4 (le_trans h3 hdbl)

/-- Q_j → ∞（沿 atTop）。由 Qsel j ≥ j 与 natCast→∞ 比较推出。 -/
lemma Qsel_tendsto_atTop : Tendsto (fun j => (Qsel j : ℝ)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt b
  use max 1 N
  intro j hj
  have hjN : N ≤ j := le_trans (le_max_right _ _) hj
  have hb : (b : ℝ) < (N : ℝ) := hN
  have hNj : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjN
  have hgej : (j : ℝ) ≤ (Qsel j : ℝ) := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact_mod_cast Qsel_ge_index k
  linarith

/-- j≥1 的递推（含 j=1，用 Qsel 0 = 1 闭合）。 -/
lemma Qsel_rec1 (j : ℕ) (hj : 1 ≤ j) :
    Qsel (j + 1) = (4 * (j : ℤ) + 2) * Qsel j + Qsel (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have h := selPair_rec 1 1 k
  simp only [Qsel] at h ⊢
  convert h using 1 <;> push_cast <;> ring

/-! ## δ 的解析理论（Hermite 积分表示；原两条公理已在此证明为定理）

    数学论证见 outputs/δ符号交替定理的严格数学证明.md。要点：
    E_n := (−1)^n n! δ_n 与 I_n := ∫₀¹ e^t t^n(1−t)^n dt 满足同一二阶递推
    与同一初值（e−1, 3−e），故 E_n = I_n；被积函数在 (0,1) 恒正故 I_n>0，
    得 δ 符号严格交错。再由行列式恒等式得正项和 Q_j|δ_{j+1}|+Q_{j+1}|δ_j| = 2，
    结合 Q_{j+1} > 4j·Q_j 推出两条估计。 -/

/-- δ 递推：δ_{j+1} = (4j+2)δ_j + δ_{j−1}（j≥1）。纯代数。 -/
lemma deltaSel_rec (j : ℕ) (hj : 1 ≤ j) :
    deltaSel (j + 1) = (4 * (j : ℝ) + 2) * deltaSel j + deltaSel (j - 1) := by
  have hQ := Qsel_rec1 j hj
  have hP : Psel (j + 1) = (4 * (j : ℤ) + 2) * Psel j + Psel (j - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have h := selPair_rec 1 3 k
    simp only [Psel] at h ⊢
    convert h using 1 <;> push_cast <;> ring
  unfold deltaSel
  have hQr : (Qsel (j + 1) : ℝ) =
      (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by exact_mod_cast hQ
  have hPr : (Psel (j + 1) : ℝ) =
      (4 * (j : ℝ) + 2) * (Psel j : ℝ) + (Psel (j - 1) : ℝ) := by exact_mod_cast hP
  rw [hQr, hPr]; ring

/-- 组合恒等式：Q_j δ_{j+1} − Q_{j+1} δ_j = 2(−1)^{j+1}（e 项相消，余行列式）。 -/
lemma cross_identity (j : ℕ) (hj : 1 ≤ j) :
    (Qsel j : ℝ) * deltaSel (j + 1) - (Qsel (j + 1) : ℝ) * deltaSel j =
      (2 * (-1 : ℤ) ^ (j + 1) : ℝ) := by
  have hdet := sel_determinant j hj
  unfold deltaSel
  have hdetR : (Psel j : ℝ) * (Qsel (j + 1) : ℝ) - (Psel (j + 1) : ℝ) * (Qsel j : ℝ) =
      (2 * (-1 : ℤ) ^ (j + 1) : ℝ) := by exact_mod_cast hdet
  linarith [hdetR]

namespace Hermite

open Polynomial MeasureTheory intervalIntegral
open scoped Interval ENNReal

/-- I_n = ∫₀¹ e^t t^n(1−t)^n dt。 -/
noncomputable def I (n : ℕ) : ℝ := ∫ t in (0:ℝ)..1, Real.exp t * (padéP n).eval t

/-- E_n = (−1)^n n! δ_n。 -/
noncomputable def E (n : ℕ) : ℝ := (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) * deltaSel n

lemma I_zero : I 0 = Real.exp 1 - 1 := by
  unfold I padéP
  simp only [pow_zero, mul_one, eval_one]
  simp [intervalIntegral.integral_const_mul]

lemma E_zero : E 0 = Real.exp 1 - 1 := by
  unfold E deltaSel
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, Qsel_zero, Psel_zero]
  push_cast; ring

lemma I_one : I 1 = 3 - Real.exp 1 := by
  have h := PadeIntegral.pade_integral_repr 1
  unfold I
  rw [h]
  have hR0 : (padéR 1).eval 0 = -3 := by
    unfold padéR padéP
    norm_num [Finset.sum_range_succ, Function.iterate_succ_apply']
    <;> simp [derivative_mul, derivative_pow_succ, derivative_sub, derivative_X]
    <;> ring
  have hR1 : (padéR 1).eval 1 = -1 := by
    unfold padéR padéP
    norm_num [Finset.sum_range_succ, Function.iterate_succ_apply']
    <;> simp [derivative_mul, derivative_pow_succ, derivative_sub, derivative_X]
    <;> ring
  rw [hR0, hR1]; ring

lemma E_one : E 1 = 3 - Real.exp 1 := by
  unfold E deltaSel
  simp only [Nat.factorial_one, Nat.cast_one, pow_one, Qsel_one, Psel_one]
  push_cast; ring

lemma E_recurrence (n : ℕ) (hn : 2 ≤ n) :
    E n = (n : ℝ) * ((n - 1 : ℕ) * E (n - 2) - (4 * n - 2 : ℝ) * E (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : (m + 2 - 1 : ℕ) = m + 1 := by omega
  have h2 : (m + 2 - 2 : ℕ) = m := by omega
  have hd := deltaSel_rec (m + 1) (by omega)
  have h3 : (m + 1 - 1 : ℕ) = m := by omega
  have h4 : (m + 1 + 1 : ℕ) = m + 2 := by omega
  rw [h3, h4] at hd
  have hf1 : (Nat.factorial (m + 1) : ℝ) = (m + 1 : ℝ) * (Nat.factorial m : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf2 : (Nat.factorial (m + 2) : ℝ) =
      (m + 2 : ℝ) * (m + 1 : ℝ) * (Nat.factorial m : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have hs1 : (-1 : ℝ) ^ (m + 1) = -((-1 : ℝ) ^ m) := by rw [pow_succ]; ring
  have hs2 : (-1 : ℝ) ^ (m + 2) = (-1 : ℝ) ^ m := by rw [pow_succ, pow_succ]; ring
  unfold E
  simp only [h1, h2]
  rw [hf1, hf2, hs1, hs2, hd]
  push_cast; ring

lemma I_recurrence (n : ℕ) (hn : 2 ≤ n) :
    I n = (n : ℝ) * ((n - 1 : ℕ) * I (n - 2) - (4 * n - 2 : ℝ) * I (n - 1)) := by
  have h := padeI_recurrence n hn
  unfold I
  rw [h]
  have hc1 : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by push_cast; ring
  have hc2 : ((2 * n * (2 * n - 1) : ℕ) : ℝ) = (n : ℝ) * (4 * n - 2 : ℝ) := by
    cases n with
    | zero => omega
    | succ k =>
        simp only [Nat.mul_succ, Nat.add_sub_cancel]
        push_cast; ring
  rw [hc1, hc2]; ring

/-- **Hermite 积分表示**：(−1)^n n! δ_n = ∫₀¹ e^t t^n(1−t)^n dt。 -/
theorem E_eq_I (n : ℕ) : E n = I n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · rw [E_zero, I_zero]
    · rw [E_one, I_one]
    · have hn : 2 ≤ m + 2 := by omega
      have h1 : m + 2 - 2 = m := by omega
      have h2 : m + 2 - 1 = m + 1 := by omega
      rw [E_recurrence (m + 2) hn, I_recurrence (m + 2) hn, h1, h2]
      rw [ih m (by omega), ih (m + 1) (by omega)]

/-- I_n > 0：被积函数在 (0,1) 内严格正且连续。 -/
theorem I_pos (n : ℕ) : 0 < I n := by
  have hpos_on : ∀ t ∈ Set.Ioo (0:ℝ) 1, 0 < Real.exp t * (padéP n).eval t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h1t : 0 < 1 - t := by linarith [ht.2]
    apply mul_pos (Real.exp_pos t)
    unfold padéP
    simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one]
    exact mul_pos (pow_pos ht0 n) (pow_pos h1t n)
  have hcont : Continuous (fun t : ℝ => Real.exp t * (padéP n).eval t) :=
    cont_exp_mul_eval (padéP n)
  have hnn : ∀ t ∈ Set.Ioc (0:ℝ) 1, 0 ≤ Real.exp t * (padéP n).eval t := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht.1
    apply mul_nonneg (le_of_lt (Real.exp_pos t))
    unfold padéP
    simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one]
    exact mul_nonneg (pow_nonneg (le_of_lt ht0) n) (pow_nonneg (by linarith [ht.2]) n)
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp t * (padéP n).eval t)
      volume (0:ℝ) 1 := hcont.intervalIntegrable _ _
  unfold I
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae']
  · refine ⟨by norm_num, ?_⟩
    have hsub : Set.Ioo (0:ℝ) 1 ⊆ Function.support
        (fun t : ℝ => Real.exp t * (padéP n).eval t) ∩ Set.Ioc (0:ℝ) 1 := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht.1
      have ht1 : t < 1 := ht.2
      exact ⟨ne_of_gt (hpos_on t ⟨ht0, ht1⟩), ⟨ht0, le_of_lt ht1⟩⟩
    have hmeas : volume (Set.Ioo (0:ℝ) 1) = 1 := by simp
    have hle : volume (Set.Ioo (0:ℝ) 1) ≤ volume
        (Function.support (fun t : ℝ => Real.exp t * (padéP n).eval t) ∩ Set.Ioc (0:ℝ) 1) :=
      measure_mono hsub
    rw [hmeas] at hle
    exact lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞) < 1) hle
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact hnn t ht
  · exact hint

/-- **δ 符号严格交错**：(−1)^j δ_j > 0（j≥1）。 -/
theorem sign_alternation (j : ℕ) (hj : 1 ≤ j) : 0 < (-1 : ℝ) ^ j * deltaSel j := by
  have hEI := E_eq_I j
  have hpos := I_pos j
  unfold E at hEI
  rw [← hEI] at hpos
  have hfact : 0 < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hrearr : (-1 : ℝ) ^ j * (Nat.factorial j : ℝ) * deltaSel j =
      (Nat.factorial j : ℝ) * ((-1 : ℝ) ^ j * deltaSel j) := by ring
  rw [hrearr] at hpos
  have hdiv : 0 < (Nat.factorial j : ℝ) * ((-1 : ℝ) ^ j * deltaSel j) /
      (Nat.factorial j : ℝ) := div_pos hpos hfact
  rwa [mul_div_cancel_left₀ _ (ne_of_gt hfact)] at hdiv

end Hermite

/-- 标准化：(−1)^j δ_j = |δ_j|。 -/
lemma sign_eq_abs (j : ℕ) (hj : 1 ≤ j) :
    (-1 : ℝ) ^ j * deltaSel j = |deltaSel j| := by
  have hpos := Hermite.sign_alternation j hj
  have habs : |(-1 : ℝ) ^ j * deltaSel j| = (-1 : ℝ) ^ j * deltaSel j := abs_of_pos hpos
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at habs
  exact habs.symm

/-- **正项和恒等式**：Q_j|δ_{j+1}| + Q_{j+1}|δ_j| = 2（j≥1）。 -/
lemma abs_sum_eq_two (j : ℕ) (hj : 1 ≤ j) :
    (Qsel j : ℝ) * |deltaSel (j + 1)| + (Qsel (j + 1) : ℝ) * |deltaSel j| = 2 := by
  have hcross := cross_identity j hj
  have hs1 := sign_eq_abs j hj
  have hs2 := sign_eq_abs (j + 1) (by omega)
  have hcast : (2 * (-1 : ℤ) ^ (j + 1) : ℝ) = 2 * (-1 : ℝ) ^ (j + 1) := by push_cast; ring
  rw [hcast] at hcross
  have hB : (-1 : ℝ) ^ (j + 1) * deltaSel j = -|deltaSel j| := by
    have hpow : (-1 : ℝ) ^ (j + 1) = -((-1 : ℝ) ^ j) := by rw [pow_succ]; ring
    rw [hpow, neg_mul, hs1]
  have hmul := congrArg (fun t => (-1 : ℝ) ^ (j + 1) * t) hcross
  have hL : (-1 : ℝ) ^ (j + 1) *
      ((Qsel j : ℝ) * deltaSel (j + 1) - (Qsel (j + 1) : ℝ) * deltaSel j) =
      (Qsel j : ℝ) * |deltaSel (j + 1)| + (Qsel (j + 1) : ℝ) * |deltaSel j| := by
    rw [mul_sub]
    have e1 : (-1 : ℝ) ^ (j + 1) * ((Qsel j : ℝ) * deltaSel (j + 1)) =
        (Qsel j : ℝ) * |deltaSel (j + 1)| := by rw [mul_left_comm, hs2]
    have e2 : (-1 : ℝ) ^ (j + 1) * ((Qsel (j + 1) : ℝ) * deltaSel j) =
        -((Qsel (j + 1) : ℝ) * |deltaSel j|) := by rw [mul_left_comm, hB]; ring
    rw [e1, e2]; ring
  have hR : (-1 : ℝ) ^ (j + 1) * (2 * (-1 : ℝ) ^ (j + 1)) = 2 := by
    have hp : (-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (j + 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc (-1 : ℝ) ^ (j + 1) * (2 * (-1 : ℝ) ^ (j + 1))
        = 2 * ((-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (j + 1)) := by ring
      _ = 2 * 1 := by rw [hp]
      _ = 2 := by ring
  linarith [hmul, hL, hR]

/-- 中间界：|δ_j| ≤ 2/Q_{j+1}。 -/
lemma abs_deltaSel_le_two_div (j : ℕ) (hj : 1 ≤ j) :
    |deltaSel j| ≤ 2 / (Qsel (j + 1) : ℝ) := by
  have hsum := abs_sum_eq_two j hj
  have hQpos : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hQ1pos : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hnn : 0 ≤ (Qsel j : ℝ) * |deltaSel (j + 1)| :=
    mul_nonneg (le_of_lt hQpos) (abs_nonneg _)
  have hle : (Qsel (j + 1) : ℝ) * |deltaSel j| ≤ 2 := by linarith
  exact (le_div_iff₀ hQ1pos).mpr (by linarith)

/-- **原公理 2，现为定理**：|δ_j| < 1/(2j·Q_j)（j≥1）。
    证：|δ_j| ≤ 2/Q_{j+1}，而 Q_{j+1} = (4j+2)Q_j + Q_{j−1} > 4j·Q_j。 -/
theorem abs_deltaSel_lt (j : ℕ) (hj : 1 ≤ j) :
    |deltaSel j| < 1 / (2 * (j : ℝ) * (Qsel j : ℝ)) := by
  have habs := abs_deltaSel_le_two_div j hj
  have hQpos : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hQ1pos : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hrec := Qsel_rec1 j hj
  have hQprev : 0 ≤ (Qsel (j - 1) : ℝ) := by
    by_cases h1 : 1 ≤ j - 1
    · exact le_of_lt (by exact_mod_cast Qsel_pos (j - 1) h1)
    · have h0 : j - 1 = 0 := by omega
      rw [h0]; simp [Qsel_zero]
  have hrecR : (Qsel (j + 1) : ℝ) =
      (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by exact_mod_cast hrec
  have hgrow : (4 * (j : ℝ)) * (Qsel j : ℝ) < (Qsel (j + 1) : ℝ) := by
    rw [hrecR]; nlinarith
  have hden : 0 < (4 * (j : ℝ)) * (Qsel j : ℝ) := by positivity
  calc |deltaSel j| ≤ 2 / (Qsel (j + 1) : ℝ) := habs
    _ < 2 / ((4 * (j : ℝ)) * (Qsel j : ℝ)) := by
        apply (div_lt_div_iff₀ hQ1pos hden).mpr; nlinarith
    _ = 1 / (2 * (j : ℝ) * (Qsel j : ℝ)) := by field_simp; ring

/-- **原公理 1，现为定理**：δ_j → 0。
    证：|δ_j| ≤ 2/Q_{j+1} → 0（Q_j → ∞），双侧夹逼。 -/
theorem deltaSel_tendsto_zero : Tendsto deltaSel atTop (nhds 0) := by
  have hQ : Tendsto (fun j : ℕ => (Qsel (j + 1) : ℝ)) atTop atTop :=
    Qsel_tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hzero : Tendsto (fun j : ℕ => 2 / (Qsel (j + 1) : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hQ
  have hnegzero : Tendsto (fun j : ℕ => -(2 / (Qsel (j + 1) : ℝ))) atTop (nhds 0) := by
    have := hzero.neg; simpa using this
  have hlo : ∀ᶠ j in atTop, -(2 / (Qsel (j + 1) : ℝ)) ≤ deltaSel j := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (abs_le.mp (abs_deltaSel_le_two_div j hj)).1
  have hhi : ∀ᶠ j in atTop, deltaSel j ≤ 2 / (Qsel (j + 1) : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (abs_le.mp (abs_deltaSel_le_two_div j hj)).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hnegzero hzero hlo hhi

/-! ## 由 δ 定理推导 -/

/-- P_j/Q_j → e。由 δ_j→0 与 Q_j→∞：P_j/Q_j = e − δ_j/Q_j，δ_j/Q_j→0。 -/
lemma Psel_div_Qsel_tendsto_exp :
    Tendsto (fun j => (Psel j : ℝ) / (Qsel j : ℝ)) atTop (nhds (Real.exp 1)) := by
  have hevent : ∀ᶠ j : ℕ in atTop, (Psel j : ℝ) / (Qsel j : ℝ) =
      Real.exp 1 - deltaSel j / (Qsel j : ℝ) := by
    apply Filter.eventually_atTop.mpr
    use 1
    intro j hj
    have hQ : (Qsel j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Qsel_pos j hj)
    have hδ : deltaSel j = (Qsel j : ℝ) * Real.exp 1 - (Psel j : ℝ) := rfl
    field_simp [hQ]
    linarith
  have hdiv : Tendsto (fun j => deltaSel j / (Qsel j : ℝ)) atTop (nhds 0) := by
    have hinv : Tendsto (fun j => (Qsel j : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Qsel_tendsto_atTop
    have hmul := deltaSel_tendsto_zero.mul hinv
    have hmul' : Tendsto (fun j => deltaSel j * (Qsel j : ℝ)⁻¹) atTop (nhds 0) := by
      simpa using hmul
    convert hmul' using 1
    funext j
    ring
  have hsub : Tendsto (fun j => Real.exp 1 - deltaSel j / (Qsel j : ℝ)) atTop
      (nhds (Real.exp 1 - 0)) :=
    tendsto_const_nhds.sub hdiv
  have h0 : Real.exp 1 - 0 = Real.exp 1 := by ring
  rw [h0] at hsub
  exact hsub.congr' (by filter_upwards [hevent] with j hj; exact hj.symm)

/-! ## 公理审计 -/

#print axioms Qsel_pos
#print axioms Psel_rec
#print axioms Qsel_rec
#print axioms sel_determinant
#print axioms Psel_odd
#print axioms Qsel_odd
#print axioms Qsel_strictMono
#print axioms Qsel_double
#print axioms Qsel_succ_coprime
#print axioms deltaSel_tendsto_zero
#print axioms abs_deltaSel_lt
#print axioms Psel_div_Qsel_tendsto_exp
#print axioms Qsel_tendsto_atTop