import Mathlib
import EpiFormal.ThresholdAttained

open Real Filter Topology Set Classification

namespace QuarterPoint

/-! ## 构造 defect ≡ 1 的点：代数核心

    M_{j+1} = (4j+2)M_j + M_{j−1} + 1，M_0 = M_1 = 0。
    W_j := M_{j+1}Q_j − M_j Q_{j+1} 满足 W_j = Q_j − W_{j−1}，W_0 = 0，
    故 0 ≤ W_j ≤ Q_j。这是尾和估计与舍入一致性的基础。 -/

/-- 分子序列：defect 恒为 1 的整数递推。 -/
def Mseq : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | (j + 2) => (4 * ((j + 1 : ℕ) : ℤ) + 2) * Mseq (j + 1) + Mseq j + 1

@[simp] lemma Mseq_zero : Mseq 0 = 0 := rfl
@[simp] lemma Mseq_one : Mseq 1 = 0 := rfl

lemma Mseq_rec (j : ℕ) :
    Mseq (j + 2) = (4 * ((j + 1 : ℕ) : ℤ) + 2) * Mseq (j + 1) + Mseq j + 1 := rfl

/-- W_j = M_{j+1}Q_j − M_j Q_{j+1}。 -/
def Wseq (j : ℕ) : ℤ := Mseq (j + 1) * Qsel j - Mseq j * Qsel (j + 1)

@[simp] lemma Wseq_zero : Wseq 0 = 0 := by simp [Wseq]

/-- Q 单调不减（Q_0 = Q_1 = 1，之后严格增）。 -/
lemma Qsel_mono_le (j : ℕ) : Qsel j ≤ Qsel (j + 1) := by
  rcases j with _ | k
  · simp [Qsel_zero, Qsel_one]
  · exact le_of_lt (Qsel_lt_succ (k + 1) (by omega))

/-- **关键递推**：W_{j} = Q_j − W_{j−1}（j≥1）。 -/
lemma Wseq_rec (j : ℕ) (hj : 1 ≤ j) : Wseq j = Qsel j - Wseq (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k + 1 - 1 = k := by omega
  rw [hk]
  have hQ := Qsel_rec1 (k + 1) (by omega)
  rw [hk] at hQ
  simp only [Wseq, Mseq_rec]
  rw [hQ]
  ring

/-- **界**：0 ≤ W_j ≤ Q_j 对一切 j。 -/
lemma Wseq_bounds (j : ℕ) : 0 ≤ Wseq j ∧ Wseq j ≤ Qsel j := by
  induction j with
  | zero => simp [Qsel_zero]
  | succ n ih =>
      have hrec := Wseq_rec (n + 1) (by omega)
      have hs : n + 1 - 1 = n := by omega
      rw [hs] at hrec
      have hmono := Qsel_mono_le n
      have hpos : 0 < Qsel (n + 1) := Qsel_pos (n + 1) (by omega)
      constructor
      · linarith [ih.2, hmono, hrec]
      · linarith [ih.1, hrec]

/-- j≥1 时 W_j > 0。 -/
lemma Wseq_pos (j : ℕ) (hj : 1 ≤ j) : 0 < Wseq j := by
  rcases Nat.eq_or_lt_of_le hj with h | h
  · -- j = 1：W_1 = Q_1 − W_0 = 1 − 0 = 1
    subst h
    have hrec := Wseq_rec 1 (by norm_num)
    norm_num at hrec
    linarith [hrec]
  · -- j ≥ 2：Q_{j−1} < Q_j，故 W_j = Q_j − W_{j−1} ≥ Q_j − Q_{j−1} > 0
    have hj2 : 2 ≤ j := h
    have hrec := Wseq_rec j hj
    have hb := Wseq_bounds (j - 1)
    have hpred : 1 ≤ j - 1 := by omega
    have hlt : Qsel (j - 1) < Qsel j := by
      have := Qsel_lt_succ (j - 1) hpred
      have hs : j - 1 + 1 = j := by omega
      rwa [hs] at this
    linarith [hb.2, hrec, hlt]

/-- Q_{j+1} ≥ 4j·Q_j（j≥1）。 -/
lemma Qsel_succ_ge_four (j : ℕ) (hj : 1 ≤ j) : 4 * (j : ℤ) * Qsel j ≤ Qsel (j + 1) := by
  have hrec := Qsel_rec1 j hj
  have hQpos : 0 < Qsel j := Qsel_pos j hj
  have hprev : 0 ≤ Qsel (j - 1) := by
    rcases j with _ | k
    · omega
    · have h : k + 1 - 1 = k := by omega
      rw [h]
      rcases k with _ | m
      · simp [Qsel_zero]
      · exact le_of_lt (Qsel_pos (m + 1) (by omega))
  linarith [hrec, hQpos, hprev]

/-- 相邻比值的实数形式：M_{j+1}/Q_{j+1} − M_j/Q_j = W_j/(Q_j Q_{j+1})。 -/
lemma ratio_diff (j : ℕ) (hj : 1 ≤ j) :
    (Mseq (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) - (Mseq j : ℝ) / (Qsel j : ℝ) =
      (Wseq j : ℝ) / ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ)) := by
  have hQ1 : (Qsel j : ℝ) ≠ 0 := by
    have := Qsel_pos j hj; positivity
  have hQ2 : (Qsel (j + 1) : ℝ) ≠ 0 := by
    have := Qsel_pos (j + 1) (by omega); positivity
  simp only [Wseq]
  push_cast
  field_simp

end QuarterPoint

#print axioms QuarterPoint.Wseq_rec
#print axioms QuarterPoint.Wseq_bounds
#print axioms QuarterPoint.Wseq_pos
#print axioms QuarterPoint.Qsel_succ_ge_four
#print axioms QuarterPoint.ratio_diff
