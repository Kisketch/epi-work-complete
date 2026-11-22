import Mathlib
import EpiFormal.EulerConvergents
import EpiFormal.DimHCore
import EpiFormal.DefectFibres

/-!
# OBL-5 第一步：δ 两公理的代数归约（DeltaReduction，2026-11-18）

**成果**：两条公理 `deltaSel_tendsto_zero`、`abs_deltaSel_lt` 被证明可由单一
解析命题「δ 符号交替」（收敛子交错夹逼 e）纯代数推出。全部归约引理仅依赖
Lean 基础公理，零 sorryAx。

**剩余义务（精确隔离）**：`deltaSignAlternation`（见下），即
∀ j ≥ 1, 0 < (−1)^j · δ_j。这是经典连分数的交错夹逼性质在本选定子列上的实例；
mathlib v4.35 无 e 的正则连分数展开定理。计划路线：Psel/Qsel 恰为 e^x 的对角
Padé 逼近在 x=1 的值（3/1, 19/7, 193/71 = [1/1],[2/2],[3/3] Padé），可用
经典积分表示 q_n(x)e^x − p_n(x) = (−1)^n·(正积分) 证符号与界。该路线尚未形式化。

**诚实边界**：本文件不消除公理本身（EulerConvergents.lean 的两条 axiom 仍在，
下游仍引用它们）；它证明的是「符号交替 ⇒ 两公理」的归约，把 OBL-5 的解析内容
压缩为单一命题。e+π 无理性仍开放。
-/

open Real Filter Topology Set

namespace DeltaReduction

noncomputable section

/-! ## 1. 剩余解析义务的精确陈述（OPEN，非公理、非定理） -/

/-- δ 符号交替：选定收敛子交错夹逼 e。**开放义务**，未证明。 -/
def deltaSignAlternation : Prop :=
  ∀ j : ℕ, 1 ≤ j → 0 < (-1 : ℝ) ^ j * deltaSel j

/-! ## 2. δ 递推与组合恒等式（纯代数，无条件） -/

/-- δ 递推：δ_{j+1} = (4j+2)δ_j + δ_{j-1}（j≥1）。 -/
lemma deltaSel_rec (j : ℕ) (hj : 1 ≤ j) :
    deltaSel (j + 1) = (4 * (j : ℝ) + 2) * deltaSel j + deltaSel (j - 1) := by
  have hQ := DimHCore.Qsel_rec1 j hj
  have hP : Psel (j + 1) = (4 * (j : ℤ) + 2) * Psel j + Psel (j - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have h := selPair_rec 1 3 k
    simp only [Psel] at h ⊢
    convert h using 1 <;> push_cast <;> ring
  unfold deltaSel
  have hQr : (Qsel (j + 1) : ℝ) =
      (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by
    exact_mod_cast hQ
  have hPr : (Psel (j + 1) : ℝ) =
      (4 * (j : ℝ) + 2) * (Psel j : ℝ) + (Psel (j - 1) : ℝ) := by
    exact_mod_cast hP
  rw [hQr, hPr]
  ring

/-- 组合恒等式：Q_j·δ_{j+1} − Q_{j+1}·δ_j = 2(−1)^{j+1}（j≥1）。
    展开 δ 定义后 e 项相消，余下行列式 sel_determinant。 -/
lemma cross_identity (j : ℕ) (hj : 1 ≤ j) :
    (Qsel j : ℝ) * deltaSel (j + 1) - (Qsel (j + 1) : ℝ) * deltaSel j =
      (2 * (-1 : ℤ) ^ (j + 1) : ℝ) := by
  have hdet := sel_determinant j hj
  unfold deltaSel
  have hdetR : (Psel j : ℝ) * (Qsel (j + 1) : ℝ) - (Psel (j + 1) : ℝ) * (Qsel j : ℝ) =
      (2 * (-1 : ℤ) ^ (j + 1) : ℝ) := by exact_mod_cast hdet
  linarith [hdetR]

/-! ## 3. 符号交替 ⇒ 关键恒等式与两条公理 -/

/-- 符号交替的标准化：(−1)^j · δ_j = |δ_j|。 -/
lemma sign_eq_abs (hsign : deltaSignAlternation)
    (j : ℕ) (hj : 1 ≤ j) : (-1 : ℝ) ^ j * deltaSel j = |deltaSel j| := by
  have hpos := hsign j hj
  have habs : |(-1 : ℝ) ^ j * deltaSel j| = (-1 : ℝ) ^ j * deltaSel j :=
    abs_of_pos hpos
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at habs
  exact habs.symm

/-- **关键恒等式**：Q_j·|δ_{j+1}| + Q_{j+1}·|δ_j| = 2（j≥1）。
    组合恒等式两边乘 (−1)^(j+1)，符号交替把两项都变成正的绝对值项。 -/
lemma abs_sum_eq_two (hsign : deltaSignAlternation)
    (j : ℕ) (hj : 1 ≤ j) :
    (Qsel j : ℝ) * |deltaSel (j + 1)| + (Qsel (j + 1) : ℝ) * |deltaSel j| = 2 := by
  have hcross := cross_identity j hj
  have hj1 : 1 ≤ j + 1 := by omega
  have hs1 := sign_eq_abs hsign j hj
  have hs2 := sign_eq_abs hsign (j + 1) hj1
  have hcast : (2 * (-1 : ℤ) ^ (j + 1) : ℝ) = 2 * (-1 : ℝ) ^ (j + 1) := by push_cast; ring
  rw [hcast] at hcross
  have hA : (-1 : ℝ) ^ (j + 1) * deltaSel (j + 1) = |deltaSel (j + 1)| := hs2
  have hB : (-1 : ℝ) ^ (j + 1) * deltaSel j = -|deltaSel j| := by
    have hpow : (-1 : ℝ) ^ (j + 1) = -((-1 : ℝ) ^ j) := by rw [pow_succ]; ring
    rw [hpow, neg_mul, hs1]
  have hmul := congrArg (fun t => (-1 : ℝ) ^ (j + 1) * t) hcross
  have hL : (-1 : ℝ) ^ (j + 1) *
      ((Qsel j : ℝ) * deltaSel (j + 1) - (Qsel (j + 1) : ℝ) * deltaSel j) =
      (Qsel j : ℝ) * |deltaSel (j + 1)| + (Qsel (j + 1) : ℝ) * |deltaSel j| := by
    rw [mul_sub]
    have e1 : (-1 : ℝ) ^ (j + 1) * ((Qsel j : ℝ) * deltaSel (j + 1)) =
        (Qsel j : ℝ) * |deltaSel (j + 1)| := by
      rw [mul_left_comm, hA]
    have e2 : (-1 : ℝ) ^ (j + 1) * ((Qsel (j + 1) : ℝ) * deltaSel j) =
        -((Qsel (j + 1) : ℝ) * |deltaSel j|) := by
      rw [mul_left_comm, hB]; ring
    rw [e1, e2]; ring
  have hR : (-1 : ℝ) ^ (j + 1) * (2 * (-1 : ℝ) ^ (j + 1)) = 2 := by
    have hp : (-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (j + 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc (-1 : ℝ) ^ (j + 1) * (2 * (-1 : ℝ) ^ (j + 1))
        = 2 * ((-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (j + 1)) := by ring
      _ = 2 * 1 := by rw [hp]
      _ = 2 := by ring
  linarith [hmul, hL, hR]

/-- **公理 2 的归约**：符号交替 ⇒ |δ_j| < 1/(2j·Q_j)。
    由关键恒等式得 |δ_j| ≤ 2/Q_{j+1}，再用 Q_{j+1} > 4j·Q_j。 -/
lemma abs_deltaSel_lt_of_sign (hsign : deltaSignAlternation)
    (j : ℕ) (hj : 1 ≤ j) : |deltaSel j| < 1 / (2 * (j : ℝ) * (Qsel j : ℝ)) := by
  have hsum := abs_sum_eq_two hsign j hj
  have hQpos : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hQ1pos : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hnn : 0 ≤ (Qsel j : ℝ) * |deltaSel (j + 1)| :=
    mul_nonneg (le_of_lt hQpos) (abs_nonneg _)
  have hle : (Qsel (j + 1) : ℝ) * |deltaSel j| ≤ 2 := by linarith
  have habs : |deltaSel j| ≤ 2 / (Qsel (j + 1) : ℝ) :=
    (le_div_iff₀ hQ1pos).mpr (by linarith)
  have hrec := DimHCore.Qsel_rec1 j hj
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
        apply (div_lt_div_iff₀ hQ1pos hden).mpr
        nlinarith
    _ = 1 / (2 * (j : ℝ) * (Qsel j : ℝ)) := by field_simp; ring

/-- **公理 1 的归约**：符号交替 ⇒ δ_j → 0。
    |δ_j| ≤ 2/Q_{j+1} → 0，双侧夹逼。 -/
lemma deltaSel_tendsto_zero_of_sign (hsign : deltaSignAlternation) :
    Tendsto deltaSel atTop (nhds 0) := by
  have hbound : ∀ j, 1 ≤ j → |deltaSel j| ≤ 2 / (Qsel (j + 1) : ℝ) := by
    intro j hj
    have hsum := abs_sum_eq_two hsign j hj
    have hQpos : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
    have hQ1pos : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
    have hnn : 0 ≤ (Qsel j : ℝ) * |deltaSel (j + 1)| :=
      mul_nonneg (le_of_lt hQpos) (abs_nonneg _)
    have hle : (Qsel (j + 1) : ℝ) * |deltaSel j| ≤ 2 := by linarith
    exact (le_div_iff₀ hQ1pos).mpr (by linarith)
  have hQ : Tendsto (fun j : ℕ => (Qsel (j + 1) : ℝ)) atTop atTop := by
    have := Qsel_tendsto_atTop
    exact this.comp (tendsto_add_atTop_nat 1)
  have hzero : Tendsto (fun j : ℕ => 2 / (Qsel (j + 1) : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hQ
  have hnegzero : Tendsto (fun j : ℕ => -(2 / (Qsel (j + 1) : ℝ))) atTop (nhds 0) := by
    have := hzero.neg
    simpa using this
  have hlo : ∀ᶠ j in atTop, -(2 / (Qsel (j + 1) : ℝ)) ≤ deltaSel j := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (abs_le.mp (hbound j hj)).1
  have hhi : ∀ᶠ j in atTop, deltaSel j ≤ 2 / (Qsel (j + 1) : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (abs_le.mp (hbound j hj)).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hnegzero hzero hlo hhi

end

end DeltaReduction

#print axioms DeltaReduction.deltaSel_rec
#print axioms DeltaReduction.cross_identity
#print axioms DeltaReduction.abs_sum_eq_two
#print axioms DeltaReduction.abs_deltaSel_lt_of_sign
#print axioms DeltaReduction.deltaSel_tendsto_zero_of_sign
