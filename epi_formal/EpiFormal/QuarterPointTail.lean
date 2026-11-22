import Mathlib
import EpiFormal.QuarterPointCore

open Real Filter Topology Set Classification QuarterPoint

namespace QuarterPointTail

/-! ## GAP1：尾和估计

    由 0 ≤ W_j ≤ Q_j 得 |M_{j+1}/Q_{j+1} − M_j/Q_j| ≤ 1/Q_{j+1}。
    Q 至少几何增长（Q_{k+1} ≥ 2Q_k），故 ∑ 1/Q_k 可和 ⇒ 比值序列 Cauchy ⇒ x 存在。
    尾和给出 ε_j = Q_j x − M_j ≤ 2Q_j/Q_{j+1} ≤ 1/(2j)。 -/

/-- Q_{j+1} ≥ 2 Q_j（j≥1）。注意 j=0 例外：Q_1 = 1 < 2 = 2Q_0。 -/
lemma Qsel_ge_two_mul (j : ℕ) (hj : 1 ≤ j) : 2 * Qsel j ≤ Qsel (j + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  · have hrec := Qsel_rec1 (k + 1) (by omega)
    have hs : k + 1 - 1 = k := by omega
    rw [hs] at hrec
    have hpos : 0 < Qsel (k + 1) := Qsel_pos (k + 1) (by omega)
    have hprev : 0 ≤ Qsel k := by
      rcases k with _ | m
      · simp [Qsel_zero]
      · exact le_of_lt (Qsel_pos (m + 1) (by omega))
    have hcoef : (2 : ℤ) ≤ 4 * ((k + 1 : ℕ) : ℤ) + 2 := by
      have : (0 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by positivity
      linarith
    nlinarith [hrec, hpos, hprev, hcoef]

/-- 比值差的绝对值 ≤ 1/Q_{j+1}（j≥1）。 -/
lemma ratio_diff_le (j : ℕ) (hj : 1 ≤ j) :
    |(Mseq (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) - (Mseq j : ℝ) / (Qsel j : ℝ)|
      ≤ 1 / (Qsel (j + 1) : ℝ) := by
  rw [ratio_diff j hj]
  have hQ1 : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hQ2 : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hW0 : (0 : ℝ) ≤ (Wseq j : ℝ) := by exact_mod_cast (Wseq_bounds j).1
  have hW1 : (Wseq j : ℝ) ≤ (Qsel j : ℝ) := by exact_mod_cast (Wseq_bounds j).2
  rw [abs_of_nonneg (div_nonneg hW0 (le_of_lt (mul_pos hQ1 hQ2)))]
  rw [div_le_div_iff₀ (mul_pos hQ1 hQ2) hQ2]
  nlinarith [hW1, hQ1, hQ2]

/-- 实数版几何增长：(Qsel (j+1) : ℝ) ≥ 2 * (Qsel j : ℝ)。 -/
lemma Qsel_real_ge_two (j : ℕ) (hj : 1 ≤ j) : 2 * (Qsel j : ℝ) ≤ (Qsel (j + 1) : ℝ) := by
  exact_mod_cast Qsel_ge_two_mul j hj

/-- 1/Qsel 可和（几何衰减，比较 ∑ (1/2)^j）。 -/
lemma summable_inv_Qsel : Summable (fun j : ℕ => 1 / (Qsel j : ℝ)) := by
  have hpos : ∀ j : ℕ, (0 : ℝ) < (Qsel j : ℝ) := by
    intro j
    rcases j with _ | k
    · simp [Qsel_zero]
    · exact_mod_cast Qsel_pos (k + 1) (by omega)
  -- (Qsel j : ℝ) ≥ (1/2)^{-j} 型下界：Qsel j ≥ 2^j / 2 不成立(j=0,1)，改用 Qsel j ≥ 2^{j-1}
  have hgrow : ∀ j : ℕ, (2 : ℝ) ^ j ≤ 2 * (Qsel j : ℝ) := by
    intro j
    induction j with
    | zero => simp [Qsel_zero]
    | succ n ih =>
        rcases Nat.eq_or_lt_of_le (Nat.succ_pos n) with h | h
        · -- n + 1 = 1：2^1 = 2 ≤ 2·Q_1 = 2
          have hn1 : n + 1 = 1 := h.symm
          rw [hn1, Qsel_one]
          norm_num
        · -- n + 1 ≥ 2，故 n ≥ 1，可用几何增长
          have hn : 1 ≤ n := by omega
          have h2 := Qsel_real_ge_two n hn
          calc (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by ring
            _ ≤ 2 * (2 * (Qsel n : ℝ)) := by gcongr
            _ ≤ 2 * (Qsel (n + 1) : ℝ) := by gcongr
  have hbound : ∀ j : ℕ, 1 / (Qsel j : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ j := by
    intro j
    have hg := hgrow j
    have hp := hpos j
    rw [div_le_iff₀ hp]
    have hhalf : (1 / 2 : ℝ) ^ j = ((2 : ℝ) ^ j)⁻¹ := by
      rw [div_pow, one_pow, one_div]
    have hkey : ((2 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ j = 1 := by field_simp
    calc (1 : ℝ) = ((2 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ j := hkey.symm
      _ ≤ ((2 : ℝ) ^ j)⁻¹ * (2 * (Qsel j : ℝ)) := by gcongr
      _ = (2 : ℝ) * (1 / 2 : ℝ) ^ j * (Qsel j : ℝ) := by
          rw [hhalf]; ring
  have hnn : ∀ j : ℕ, 0 ≤ 1 / (Qsel j : ℝ) := by
    intro j; exact div_nonneg zero_le_one (le_of_lt (hpos j))
  exact Summable.of_nonneg_of_le hnn hbound
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2)

end QuarterPointTail

#print axioms QuarterPointTail.Qsel_ge_two_mul
#print axioms QuarterPointTail.ratio_diff_le
#print axioms QuarterPointTail.summable_inv_Qsel
