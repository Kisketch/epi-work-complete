import Mathlib
import EpiFormal.EulerConvergents

/-!
# D 组：命题 8.1（Dirichlet 尺度下的分母整除限制）独立核验

本文件独立重建并机器核验第一阶段主稿 Proposition `prop:dirichlet-divisor`（命题 8.1）。
拆成四个声明，分别形式化：
  1. `dirichlet_witness`   —— Dirichlet 见证存在（对每个 j≥1）。
  2. `linForm_identity`    —— 假设有理时，构造整数线性形式并给出精确恒等式。
  3. `linForm_abs_lt_one` / `linForm_eq_zero` —— 阈值 j>(3B/2)^2 下绝对值严格小于 1，从而为 0。
  4. `Psel_Qsel_coprime` + `divisor_restriction` —— 用 gcd(P_j,Q_j)=1 推出 Q_j/gcd(Q_j,B) ∣ d。

## 诚实声明
e+π 无理性仍是开放问题。本文件只核验命题 8.1 这一**必要条件**（纸面命题）的逻辑正确性，
不声称、也不暗示解决该开放问题。整除结论以「B(e+π)=A 为整数」为前提，是条件性结论。

## 依赖与新增
- 取用共享地基 `EpiFormal.EulerConvergents` 的 `Psel`/`Qsel`/`deltaSel`、
  `abs_deltaSel_lt`（已是定理，Hermite 积分路线，非公理）、`sel_determinant`、`Qsel_odd`、`Qsel_pos`。
- **新增引理** `Psel_Qsel_coprime`：共享库只有相邻 Q-Q 互素（`Qsel_succ_coprime`），
  没有 P_j 与 Q_j 互素。此处用行列式 ±2 + P、Q 均为奇数补证。
- Dirichlet 见证存在性直接引用 mathlib `Real.exists_int_int_abs_mul_sub_le`，
  其上界恰为 `1/(n+1)`，与正文 `1/(H+1)` 完全一致，无需补证。

## 量词与除法口径
- 整除结论的量词是「**每个**合格见证 (p,d)」，不是「存在」。
- 正文 q/gcd(q,B) 是整数意义下的精确商（gcd∣q）。本文件在 ℤ 上用 `Int.ediv` 表达，
  并由 `Int.gcd_dvd_left` 保证整除精确；与正文 ℕ 除法在正性假设下等价。
- 阈值严格：`j > (3B/2)^2`，B 为正整数（这里用 `B : ℤ, 0 < B`）。
-/

open Real

namespace DVerify

set_option maxHeartbeats 800000

noncomputable section

/-- H_j = ⌊Q_j √j⌋（自然数向下取整）。 -/
def H (j : ℕ) : ℕ := ⌊(Qsel j : ℝ) * √(j : ℝ)⌋₊

lemma Qsel_pos_all (j : ℕ) : 0 < Qsel j :=
  (selPair_pos_odd 1 1 (by norm_num) (by norm_num) odd_one odd_one j).1

lemma H_le (j : ℕ) : (H j : ℝ) ≤ (Qsel j : ℝ) * √(j : ℝ) := by
  apply Nat.floor_le
  exact mul_nonneg (by exact_mod_cast le_of_lt (Qsel_pos_all j)) (Real.sqrt_nonneg _)

lemma H_lt (j : ℕ) : (Qsel j : ℝ) * √(j : ℝ) < (H j : ℝ) + 1 :=
  Nat.lt_floor_add_one _

lemma H_pos (j : ℕ) (hj : 1 ≤ j) : 1 ≤ H j := by
  rw [H, Nat.one_le_floor_iff]
  have hq1 : 1 ≤ Qsel j := by have := Qsel_pos j hj; omega
  have hq : (1 : ℝ) ≤ (Qsel j : ℝ) := by exact_mod_cast hq1
  have hs : (1 : ℝ) ≤ √(j : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hj)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (Qsel j : ℝ) * √(j : ℝ) := mul_le_mul hq hs (by norm_num) (by positivity)

/-! ## 声明 1：Dirichlet 见证存在 -/

/-- 对每个 j≥1，存在整数 p,d 满足 1≤d≤H_j 且 |dπ−p|≤1/(H_j+1)。
    直接引用 mathlib Dirichlet 定理（上界恰为 1/(n+1)）。 -/
theorem dirichlet_witness (j : ℕ) (hj : 1 ≤ j) :
    ∃ p d : ℤ, 1 ≤ d ∧ d ≤ (H j : ℤ) ∧ |(d : ℝ) * Real.pi - p| ≤ 1 / ((H j : ℝ) + 1) := by
  have hH : 0 < H j := Nat.lt_of_lt_of_le (by norm_num) (H_pos j hj)
  obtain ⟨p, d, hd0, hdH, herr⟩ := Real.exists_int_int_abs_mul_sub_le Real.pi hH
  refine ⟨p, d, Int.add_one_le_iff.mpr hd0, hdH, ?_⟩
  -- mathlib 给 |↑d * π - p| ≤ 1 / (↑(H j) + 1)，与目标一致
  simpa [mul_comm] using herr

/-! ## 声明 2：整数线性形式与精确恒等式 -/

/-- 整数线性形式 N = A·Q_j·d − B·(P_j·d + p·Q_j)。 -/
def linForm (A B : ℤ) (j : ℕ) (p d : ℤ) : ℤ :=
  A * Qsel j * d - B * (Psel j * d + p * Qsel j)

/-- 假设有理 B(e+π)=A 时，N = B·(d·δ_j + Q_j·(dπ−p))（精确实数恒等式）。 -/
theorem linForm_identity (A B : ℤ) (j : ℕ) (p d : ℤ)
    (hA : (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ)) :
    (linForm A B j p d : ℝ) =
      (B : ℝ) * ((d : ℝ) * deltaSel j + (Qsel j : ℝ) * ((d : ℝ) * Real.pi - p)) := by
  calc (linForm A B j p d : ℝ)
      = (A : ℝ) * (Qsel j : ℝ) * d - (B : ℝ) * (Psel j : ℝ) * d
          - (B : ℝ) * p * (Qsel j : ℝ) := by
        simp only [linForm]; push_cast; ring
    _ = (B : ℝ) * (Real.exp 1 + Real.pi) * (Qsel j : ℝ) * d
          - (B : ℝ) * (Psel j : ℝ) * d - (B : ℝ) * p * (Qsel j : ℝ) := by
        rw [← hA]
    _ = (B : ℝ) * ((d : ℝ) * deltaSel j + (Qsel j : ℝ) * ((d : ℝ) * Real.pi - p)) := by
        simp only [deltaSel]; ring

/-! ## 声明 3：阈值下绝对值严格小于 1 -/

/-- 关键估计：j>(3B/2)^2 且见证合格时，|N|<1。 -/
theorem linForm_abs_lt_one (B : ℤ) (A : ℤ) (j : ℕ) (p d : ℤ)
    (hB : 0 < B) (hj : (3 * (B : ℝ) / 2) ^ 2 < (j : ℝ))
    (hA : (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ))
    (hd1 : 1 ≤ d) (hdH : d ≤ (H j : ℤ))
    (herr : |(d : ℝ) * Real.pi - p| ≤ 1 / ((H j : ℝ) + 1)) :
    |(linForm A B j p d : ℝ)| < 1 := by
  -- 阈值蕴含 j≥1
  have hj1 : 1 ≤ j := by
    have hB1 : (1 : ℤ) ≤ B := Int.add_one_le_iff.mpr hB
    have hB1r : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
    have hsq : (1 : ℝ) ≤ (3 * (B : ℝ) / 2) ^ 2 := by nlinarith
    have hjr : (1 : ℝ) < (j : ℝ) := by linarith
    have hjz : (1 : ℤ) < (j : ℤ) := by exact_mod_cast hjr
    omega
  have hqpos : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj1
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hspos : 0 < √(j : ℝ) := Real.sqrt_pos.mpr hjpos
  have hHpos : 0 < (H j : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) (H_pos j hj1))
  have hδ := abs_deltaSel_lt j hj1
  -- 第一项：d·|δ_j| < H/(2jq)
  have ht1 : (d : ℝ) * |deltaSel j| < (H j : ℝ) / (2 * (j : ℝ) * (Qsel j : ℝ)) := by
    calc (d : ℝ) * |deltaSel j|
        ≤ (H j : ℝ) * |deltaSel j| :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hdH) (abs_nonneg _)
      _ < (H j : ℝ) * (1 / (2 * (j : ℝ) * (Qsel j : ℝ))) :=
          mul_lt_mul_of_pos_left hδ hHpos
      _ = (H j : ℝ) / (2 * (j : ℝ) * (Qsel j : ℝ)) := by ring
  -- 第二项：Q_j·|dπ−p| ≤ Q_j/(H+1)
  have ht2 : (Qsel j : ℝ) * |(d : ℝ) * Real.pi - p| ≤
      (Qsel j : ℝ) / ((H j : ℝ) + 1) := by
    calc (Qsel j : ℝ) * |(d : ℝ) * Real.pi - p|
        ≤ (Qsel j : ℝ) * (1 / ((H j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left herr (le_of_lt hqpos)
      _ = (Qsel j : ℝ) / ((H j : ℝ) + 1) := by ring
  -- H/(2jq) ≤ 1/(2√j)
  have hb1 : (H j : ℝ) / (2 * (j : ℝ) * (Qsel j : ℝ)) ≤ 1 / (2 * √(j : ℝ)) := by
    have hjq : (j : ℝ) = √(j : ℝ) * √(j : ℝ) := (Real.mul_self_sqrt (le_of_lt hjpos)).symm
    have hkey : (H j : ℝ) * √(j : ℝ) ≤ (Qsel j : ℝ) * √(j : ℝ) * √(j : ℝ) :=
      mul_le_mul_of_nonneg_right (H_le j) (le_of_lt hspos)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey, hjq]
  -- Q_j/(H+1) < 1/√j
  have hb2 : (Qsel j : ℝ) / ((H j : ℝ) + 1) < 1 / √(j : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hspos]
    linarith [H_lt j]
  -- 合并：d|δ|+Q|dπ−p| < 3/(2√j)
  have hsum : (d : ℝ) * |deltaSel j| + (Qsel j : ℝ) * |(d : ℝ) * Real.pi - p| <
      3 / (2 * √(j : ℝ)) := by
    have heq : 1 / (2 * √(j : ℝ)) + 1 / √(j : ℝ) = 3 / (2 * √(j : ℝ)) := by
      field_simp; ring
    linarith [ht1, ht2, hb1, hb2, heq]
  -- 阈值：3B/(2√j) < 1
  have hthr : 3 * (B : ℝ) / (2 * √(j : ℝ)) < 1 := by
    have hs : 3 * (B : ℝ) / 2 < √(j : ℝ) := (Real.lt_sqrt (by positivity)).mpr hj
    calc 3 * (B : ℝ) / (2 * √(j : ℝ)) = (3 * (B : ℝ) / 2) / √(j : ℝ) := by ring
      _ < 1 := (div_lt_one hspos).mpr hs
  -- 组装
  calc |(linForm A B j p d : ℝ)|
      = |(B : ℝ) * ((d : ℝ) * deltaSel j + (Qsel j : ℝ) * ((d : ℝ) * Real.pi - p))| := by
        rw [linForm_identity A B j p d hA]
    _ = (B : ℝ) * |(d : ℝ) * deltaSel j + (Qsel j : ℝ) * ((d : ℝ) * Real.pi - p)| := by
        rw [abs_mul, abs_of_nonneg (by exact_mod_cast (le_of_lt hB) : 0 ≤ (B : ℝ))]
    _ ≤ (B : ℝ) * ((d : ℝ) * |deltaSel j| + (Qsel j : ℝ) * |(d : ℝ) * Real.pi - p|) := by
        apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast (le_of_lt hB))
        calc |(d : ℝ) * deltaSel j + (Qsel j : ℝ) * ((d : ℝ) * Real.pi - p)|
            ≤ |(d : ℝ) * deltaSel j| + |(Qsel j : ℝ) * ((d : ℝ) * Real.pi - p)| :=
              abs_add_le _ _
          _ = (d : ℝ) * |deltaSel j| + (Qsel j : ℝ) * |(d : ℝ) * Real.pi - p| := by
              rw [abs_mul, abs_mul,
                abs_of_nonneg (by exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 1) hd1) :
                  0 ≤ (d : ℝ)),
                abs_of_nonneg (le_of_lt hqpos)]
    _ < (B : ℝ) * (3 / (2 * √(j : ℝ))) :=
        mul_lt_mul_of_pos_left hsum (by exact_mod_cast hB)
    _ = 3 * (B : ℝ) / (2 * √(j : ℝ)) := by ring
    _ < 1 := hthr

/-- 整数绝对值 <1 ⇒ 该整数为 0。 -/
theorem linForm_eq_zero (B : ℤ) (A : ℤ) (j : ℕ) (p d : ℤ)
    (hB : 0 < B) (hj : (3 * (B : ℝ) / 2) ^ 2 < (j : ℝ))
    (hA : (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ))
    (hd1 : 1 ≤ d) (hdH : d ≤ (H j : ℤ))
    (herr : |(d : ℝ) * Real.pi - p| ≤ 1 / ((H j : ℝ) + 1)) :
    linForm A B j p d = 0 := by
  have h := linForm_abs_lt_one B A j p d hB hj hA hd1 hdH herr
  have hz : |linForm A B j p d| < 1 := by exact_mod_cast h
  rcases abs_lt.mp hz with ⟨h1, h2⟩
  omega

/-! ## 声明 4：互素与整除 -/

/-- **新增引理**：gcd(P_j, Q_j) = 1（j≥1）。
    共享库只有 Q-Q 相邻互素；此处用行列式 ±2 与 P、Q 均为奇数补证。 -/
theorem Psel_Qsel_coprime (j : ℕ) (hj : 1 ≤ j) : Int.gcd (Psel j) (Qsel j) = 1 := by
  set g := Int.gcd (Psel j) (Qsel j) with hg_def
  have hgP : (g : ℤ) ∣ Psel j := Int.gcd_dvd_left _ _
  have hgQ : (g : ℤ) ∣ Qsel j := Int.gcd_dvd_right _ _
  have hg2 : (g : ℤ) ∣ 2 * (-1 : ℤ) ^ (j + 1) := by
    have hdvd : (g : ℤ) ∣ Psel j * Qsel (j + 1) - Psel (j + 1) * Qsel j :=
      dvd_sub (dvd_mul_of_dvd_left hgP _) (dvd_mul_of_dvd_right hgQ _)
    rwa [sel_determinant j hj] at hdvd
  have hg2' : g ∣ 2 := by
    have h' : (g : ℤ) ∣ 2 * (-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j + 1) :=
      dvd_mul_of_dvd_left hg2 _
    have hp : (2 : ℤ) * (-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j + 1) = 2 := by
      have hsq : (-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j + 1) = 1 := by
        rw [← pow_add, show (j + 1) + (j + 1) = 2 * (j + 1) by ring, pow_mul]
        norm_num
      calc (2 : ℤ) * (-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j + 1)
          = 2 * ((-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j + 1)) := by ring
        _ = 2 * 1 := by rw [hsq]
        _ = 2 := by ring
    have h'' : (g : ℤ) ∣ 2 := by rwa [hp] at h'
    exact_mod_cast h''
  have hcases : g = 1 ∨ g = 2 := (Nat.dvd_prime Nat.prime_two).mp hg2'
  rcases hcases with h1 | h2
  · exact h1
  · exfalso
    have hgQ2 : (2 : ℤ) ∣ Qsel j := by
      have hc : (g : ℤ) = 2 := by exact_mod_cast h2
      rwa [← hc]
    have heven : Even (Qsel j) := even_iff_two_dvd.mpr hgQ2
    exact (Int.not_even_iff_odd.mpr (Qsel_odd j hj)) heven

/-- gcd(Q_j, B) 整除 Q_j（保证 ℤ 除法精确）。 -/
lemma gcd_dvd_Qsel (j : ℕ) (B : ℤ) : (Int.gcd (Qsel j) B : ℤ) ∣ Qsel j :=
  Int.gcd_dvd_left _ _

/-- **整除限制**：给定合格见证且 N=0，则 Q_j/gcd(Q_j,B) ∣ d。
    这是「给定见证推出整除」的完整形式化，见证存在性单列（见 dirichlet_witness）。 -/
theorem divisor_restriction (B : ℤ) (A : ℤ) (j : ℕ) (p d : ℤ) (hj1 : 1 ≤ j)
    (h0 : linForm A B j p d = 0) :
    (Qsel j / (Int.gcd (Qsel j) B : ℤ)) ∣ d := by
  -- 第一步：Q_j ∣ B·P_j·d
  have hqBP : (Qsel j : ℤ) ∣ B * Psel j * d := by
    use A * d - B * p
    have h := h0
    simp only [linForm] at h
    linarith
  -- 第二步：gcd(P_j,Q_j)=1 ⇒ Q_j ∣ B·d
  have hcop := Psel_Qsel_coprime j hj1
  have hqB : (Qsel j : ℤ) ∣ B * d := by
    have h' : (Qsel j : ℤ) ∣ B * d * Psel j := by
      have h := hqBP
      rw [show B * Psel j * d = B * d * Psel j by ring] at h
      exact h
    have hcop' : Int.gcd (Qsel j) (Psel j) = 1 := by
      rw [Int.gcd_comm]; exact hcop
    exact Int.dvd_of_dvd_mul_left_of_gcd_one h' hcop'
  -- 第三步：消去 gcd(Q_j,B)
  set g := Int.gcd (Qsel j) B with hg_def
  have gpos : 0 < g := Int.gcd_pos_of_ne_zero_left B (ne_of_gt (Qsel_pos j hj1))
  have gposZ : (0 : ℤ) < (g : ℤ) := by exact_mod_cast gpos
  have hgq : (g : ℤ) ∣ Qsel j := Int.gcd_dvd_left _ _
  have hgB : (g : ℤ) ∣ B := Int.gcd_dvd_right _ _
  have hcop' : Int.gcd (Qsel j / (g : ℤ)) (B / (g : ℤ)) = 1 :=
    Int.gcd_div_gcd_div_gcd gpos
  have hstep : (Qsel j / (g : ℤ)) ∣ (B / (g : ℤ)) * d := by
    have h := hqB
    rw [← Int.ediv_mul_cancel hgq, ← Int.ediv_mul_cancel hgB] at h
    -- h : (Q_j/g)*g ∣ ((B/g)*g)*d
    have h' : (g : ℤ) * (Qsel j / (g : ℤ)) ∣ (g : ℤ) * ((B / (g : ℤ)) * d) := by
      rw [show (g : ℤ) * (Qsel j / (g : ℤ)) = (Qsel j / (g : ℤ)) * (g : ℤ) by ring,
        show (g : ℤ) * ((B / (g : ℤ)) * d) = (B / (g : ℤ)) * (g : ℤ) * d by ring]
      exact h
    exact (mul_dvd_mul_iff_left (ne_of_gt gposZ)).mp h'
  exact (Int.isCoprime_iff_gcd_eq_one.mpr hcop').dvd_of_dvd_mul_left hstep

/-! ## 组装：命题 8.1 -/

/-- 命题 8.1 主体（整除部分）：假设有理，则对每个 j>(3B/2)^2 与每个合格见证，
    Q_j/gcd(Q_j,B) ∣ d。 -/
theorem prop_8_1_div (B : ℤ) (hB : 0 < B) (A : ℤ)
    (hA : (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ)) :
    ∀ j : ℕ, (3 * (B : ℝ) / 2) ^ 2 < (j : ℝ) →
      ∀ p d : ℤ, 1 ≤ d → d ≤ (H j : ℤ) →
        |(d : ℝ) * Real.pi - p| ≤ 1 / ((H j : ℝ) + 1) →
        (Qsel j / (Int.gcd (Qsel j) B : ℤ)) ∣ d := by
  intro j hj p d hd1 hdH herr
  have hj1 : 1 ≤ j := by
    have hB1 : (1 : ℤ) ≤ B := Int.add_one_le_iff.mpr hB
    have hB1r : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
    have hsq : (1 : ℝ) ≤ (3 * (B : ℝ) / 2) ^ 2 := by nlinarith
    have hjr : (1 : ℝ) < (j : ℝ) := by linarith
    have hjz : (1 : ℤ) < (j : ℤ) := by exact_mod_cast hjr
    omega
  exact divisor_restriction B A j p d hj1
    (linForm_eq_zero B A j p d hB hj hA hd1 hdH herr)

/-- 命题 8.1 完整包装：对每个 j>(3B/2)^2，见证存在且每个合格见证满足整除限制。 -/
theorem prop_8_1 (B : ℤ) (hB : 0 < B) (A : ℤ)
    (hA : (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ)) :
    ∀ j : ℕ, (3 * (B : ℝ) / 2) ^ 2 < (j : ℝ) →
      (∃ p d : ℤ, 1 ≤ d ∧ d ≤ (H j : ℤ) ∧ |(d : ℝ) * Real.pi - p| ≤ 1 / ((H j : ℝ) + 1)) ∧
      (∀ p d : ℤ, 1 ≤ d → d ≤ (H j : ℤ) →
        |(d : ℝ) * Real.pi - p| ≤ 1 / ((H j : ℝ) + 1) →
        (Qsel j / (Int.gcd (Qsel j) B : ℤ)) ∣ d) := by
  intro j hj
  have hj1 : 1 ≤ j := by
    have hB1 : (1 : ℤ) ≤ B := Int.add_one_le_iff.mpr hB
    have hB1r : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
    have hsq : (1 : ℝ) ≤ (3 * (B : ℝ) / 2) ^ 2 := by nlinarith
    have hjr : (1 : ℝ) < (j : ℝ) := by linarith
    have hjz : (1 : ℤ) < (j : ℤ) := by exact_mod_cast hjr
    omega
  exact ⟨dirichlet_witness j hj1, prop_8_1_div B hB A hA j hj⟩

end

end DVerify

/-! ## 公理审计 -/

#print axioms DVerify.H_pos
#print axioms DVerify.dirichlet_witness
#print axioms DVerify.linForm_identity
#print axioms DVerify.linForm_abs_lt_one
#print axioms DVerify.linForm_eq_zero
#print axioms DVerify.Psel_Qsel_coprime
#print axioms DVerify.gcd_dvd_Qsel
#print axioms DVerify.divisor_restriction
#print axioms DVerify.prop_8_1_div
#print axioms DVerify.prop_8_1
