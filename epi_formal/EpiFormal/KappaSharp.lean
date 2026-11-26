import Mathlib
import EpiFormal.Classification

/-!
# THM-0005 (sharpness of the quarter gap): `kappa_sharp`, `kappa_eq_quarter`

For the Euler convergent denominators `Qsel` of `e`, we construct an explicit `z ∉ L`
(`L = Classification.latticeL`) with `limsup j‖Q_j z‖ ≤ 1/4` while `j‖Q_j z‖ ≥ 1/5`
infinitely often.  Combined with `Classification.corollary3_gap` this gives
`inf_{z ∉ L} limsup j ‖Q_j z‖ = 1/4`, attained.  No project axioms are added.
-/

open Filter Topology

namespace KappaSharp

noncomputable section

/-! ### Abstract real inequalities -/

lemma real_upper (J a b c d S μ Y E : ℝ) (hJ : 1 ≤ J)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : 3 * J * a ≤ b) (h2 : 4 * J * b ≤ c) (h3 : 4 * J * c ≤ d)
    (hS0 : 0 ≤ S) (hS : S ≤ 2 * a + μ * b) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hY : |Y| ≤ S / c + E) (hE : E = 12 / 5 * b / d) :
    J ^ 2 * |Y| ≤ μ * J / 4 + 1 / 2 := by
  have hJ0 : 0 < J := by linarith
  have hx1 : 0 ≤ a / b := by positivity
  have hx2 : 0 ≤ b / c := by positivity
  have hx3 : 0 ≤ c / d := by positivity
  have k1 : 3 * J * (a / b) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hb]; exact h1
  have k2 : 4 * J * (b / c) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hc]; exact h2
  have k3 : 4 * J * (c / d) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hd]; exact h3
  have e1 : S / c ≤ 2 * (a / b) * (b / c) + μ * (b / c) := by
    calc S / c ≤ (2 * a + μ * b) / c := by gcongr
      _ = 2 * (a / b) * (b / c) + μ * (b / c) := by
        first | (field_simp; ring) | field_simp
  have e2 : E = 12 / 5 * ((b / c) * (c / d)) := by
    rw [hE]
    first | (field_simp; ring) | field_simp
  have P1 : (3 * J * (a / b)) * (4 * J * (b / c)) ≤ 1 * 1 :=
    mul_le_mul k1 k2 (by positivity) zero_le_one
  have P2 : (4 * J * (b / c)) * (4 * J * (c / d)) ≤ 1 * 1 :=
    mul_le_mul k2 k3 (by positivity) zero_le_one
  have P3 : J * (μ * (4 * J * (b / c))) ≤ J * (μ * 1) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left k2 hμ0) hJ0.le
  have hsum : |Y| ≤ 2 * (a / b) * (b / c) + μ * (b / c) + 12 / 5 * ((b / c) * (c / d)) := by
    rw [← e2]; linarith
  have hsq : J ^ 2 * |Y| ≤ J ^ 2 * (2 * (a / b) * (b / c) + μ * (b / c)
      + 12 / 5 * ((b / c) * (c / d))) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  nlinarith [P1, P2, P3, hsq]

lemma real_lower (J a b c d S Y E : ℝ) (hJ : 1 ≤ J)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h2 : 4 * J * b ≤ c) (h2' : c ≤ (4 * J + 3) * b) (h3 : 4 * J * c ≤ d)
    (hS : b ≤ S)
    (hY : S / c - E ≤ Y) (hE : E = 12 / 5 * b / d) :
    J / 4 - 1 / 2 ≤ J ^ 2 * Y := by
  have hJ0 : 0 < J := by linarith
  have hx2 : 0 ≤ b / c := by positivity
  have hx3 : 0 ≤ c / d := by positivity
  have k2 : 4 * J * (b / c) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hc]; exact h2
  have k3 : 4 * J * (c / d) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hd]; exact h3
  have k2' : 1 ≤ (4 * J + 3) * (b / c) := by
    rw [← mul_div_assoc, le_div_iff₀ hc]; linarith
  have e2 : E = 12 / 5 * ((b / c) * (c / d)) := by
    rw [hE]
    first | (field_simp; ring) | field_simp
  have e1 : b / c ≤ S / c := by gcongr
  have P2 : (4 * J * (b / c)) * (4 * J * (c / d)) ≤ 1 * 1 :=
    mul_le_mul k2 k3 (by positivity) zero_le_one
  have Q1 : J * 1 ≤ J * ((4 * J + 3) * (b / c)) := mul_le_mul_of_nonneg_left k2' hJ0.le
  have hY2 : b / c - 12 / 5 * ((b / c) * (c / d)) ≤ Y := by rw [← e2]; linarith
  have hsq : J ^ 2 * (b / c - 12 / 5 * ((b / c) * (c / d))) ≤ J ^ 2 * Y :=
    mul_le_mul_of_nonneg_left hY2 (by positivity)
  nlinarith [P2, Q1, k2, hsq]


/-! ### The perturbation sequence -/

/-- `m_j = 1` for even `j ≥ 2`, else `0`. -/
def mm (j : ℕ) : ℤ := if 2 ≤ j ∧ j % 2 = 0 then 1 else 0

lemma mm_cases (j : ℕ) : mm j = 0 ∨ (mm j = 1 ∧ 2 ≤ j ∧ j % 2 = 0) := by
  unfold mm
  split_ifs with h
  · exact Or.inr ⟨rfl, h.1, h.2⟩
  · exact Or.inl rfl

lemma mm_nonneg (j : ℕ) : 0 ≤ mm j := by
  rcases mm_cases j with h | ⟨h, -⟩ <;> simp [h]

lemma mm_le_one (j : ℕ) : mm j ≤ 1 := by
  rcases mm_cases j with h | ⟨h, -⟩ <;> simp [h]

lemma mm_real_cases (j : ℕ) :
    (mm j : ℝ) = 0 ∨ ((mm j : ℝ) = 1 ∧ 2 ≤ j ∧ j % 2 = 0) := by
  rcases mm_cases j with h | ⟨h, h2, h3⟩
  · left; simp [h]
  · right; exact ⟨by simp [h], h2, h3⟩

/-! ### Growth facts for `Qsel` -/

lemma q_pos (j : ℕ) : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Classification.Qsel_pos j

lemma q_rec2 (k : ℕ) :
    (Qsel (k + 2) : ℝ) = (4 * (k : ℝ) + 6) * (Qsel (k + 1) : ℝ) + (Qsel k : ℝ) := by
  have h := Classification.Qsel_rec k
  exact_mod_cast h

lemma q_ge (k : ℕ) (hk : 1 ≤ k) : (4 * (k : ℝ) + 2) * (Qsel k : ℝ) ≤ (Qsel (k + 1) : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h : (Qsel (m + 2) : ℝ) = (4 * (m : ℝ) + 6) * (Qsel (m + 1) : ℝ) + (Qsel m : ℝ) := q_rec2 m
  have h1 := q_pos m
  have e : (4 * ((m + 1 : ℕ) : ℝ) + 2) = 4 * (m : ℝ) + 6 := by push_cast; ring
  rw [e]
  show (4 * (m : ℝ) + 6) * (Qsel (m + 1) : ℝ) ≤ (Qsel (m + 2) : ℝ)
  rw [h]; linarith

lemma q_ge6 (k : ℕ) (hk : 1 ≤ k) : 6 * (Qsel k : ℝ) ≤ (Qsel (k + 1) : ℝ) := by
  have h := q_ge k hk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h0 := q_pos k
  nlinarith [mul_nonneg (sub_nonneg.2 hk') h0.le]

lemma q_mono (k : ℕ) : (Qsel k : ℝ) ≤ (Qsel (k + 1) : ℝ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have := q_ge6 k hk
    have := q_pos k
    linarith

lemma q_le (k : ℕ) (hk : 1 ≤ k) : (Qsel (k + 1) : ℝ) ≤ (4 * (k : ℝ) + 3) * (Qsel k : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h : (Qsel (m + 2) : ℝ) = (4 * (m : ℝ) + 6) * (Qsel (m + 1) : ℝ) + (Qsel m : ℝ) := q_rec2 m
  have h1 := q_mono m
  have e : (4 * ((m + 1 : ℕ) : ℝ) + 3) = 4 * (m : ℝ) + 7 := by push_cast; ring
  rw [e]
  show (Qsel (m + 2) : ℝ) ≤ (4 * (m : ℝ) + 7) * (Qsel (m + 1) : ℝ)
  rw [h]; linarith

lemma q_pow (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    (6 : ℝ) ^ k * (Qsel m : ℝ) ≤ (Qsel (m + k) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := q_ge6 (m + k) (by omega)
    have e : (Qsel (m + (k + 1)) : ℝ) = (Qsel (m + k + 1) : ℝ) := rfl
    rw [e, pow_succ]
    linarith

lemma q_six_pow (i : ℕ) : (6 : ℝ) ^ i ≤ (Qsel (i + 1) : ℝ) := by
  have h := q_pow 1 le_rfl i
  have e : (Qsel (1 + i) : ℝ) = (Qsel (i + 1) : ℝ) := by rw [Nat.add_comm]
  rw [e] at h
  simpa using h

/-! ### The partial sums `S_j` -/

/-- `S_j = ∑_{even i, 2 ≤ i ≤ j} Q_i`. -/
def SS : ℕ → ℤ
  | 0 => 0
  | j + 1 => SS j + mm (j + 1) * Qsel (j + 1)

lemma SS_succ (j : ℕ) :
    (SS (j + 1) : ℝ) = (SS j : ℝ) + (mm (j + 1) : ℝ) * (Qsel (j + 1) : ℝ) := by
  simp only [SS]; push_cast; ring

lemma SS_nonneg (j : ℕ) : (0 : ℝ) ≤ (SS j : ℝ) := by
  induction j with
  | zero => simp [SS]
  | succ j ih =>
    rw [SS_succ]
    have h1 : (0 : ℝ) ≤ (mm (j + 1) : ℝ) := by exact_mod_cast mm_nonneg (j + 1)
    have h2 := q_pos (j + 1)
    have := mul_nonneg h1 h2.le
    linarith

lemma SS_le (j : ℕ) : (SS j : ℝ) ≤ 2 * (Qsel j : ℝ) := by
  induction j with
  | zero => simp [SS]
  | succ j ih =>
    rw [SS_succ]
    have hp := q_pos (j + 1)
    rcases mm_real_cases (j + 1) with h | ⟨h, h2, h3⟩
    · rw [h]
      have := q_mono j
      linarith
    · rw [h]
      have hj : 1 ≤ j := by omega
      have := q_ge6 j hj
      linarith

/-! ### The integer sequence `n_j` -/

/-- `n_0 = n_1 = 0`, `n_{j+1} = (4j+2) n_j + n_{j-1} + m_j`. -/
def nn : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | j + 2 => (4 * ((j + 1 : ℕ) : ℤ) + 2) * nn (j + 1) + nn j + mm (j + 1)

lemma EE_eq (j : ℕ) :
    nn (j + 1) * Qsel j - nn j * Qsel (j + 1) = (-1) ^ j * SS j := by
  induction j with
  | zero => simp [nn, SS]
  | succ j ih =>
    have hQ : Qsel (j + 2) = (4 * (j : ℤ) + 6) * Qsel (j + 1) + Qsel j :=
      Classification.Qsel_rec j
    have hn : nn (j + 2) = (4 * ((j + 1 : ℕ) : ℤ) + 2) * nn (j + 1) + nn j + mm (j + 1) := rfl
    have key : nn (j + 1 + 1) * Qsel (j + 1) - nn (j + 1) * Qsel (j + 1 + 1)
        = -(nn (j + 1) * Qsel j - nn j * Qsel (j + 1)) + mm (j + 1) * Qsel (j + 1) := by
      show nn (j + 2) * Qsel (j + 1) - nn (j + 1) * Qsel (j + 2) = _
      rw [hQ, hn]; push_cast; ring
    have hs : SS (j + 1) = SS j + mm (j + 1) * Qsel (j + 1) := rfl
    rw [key, ih, hs]
    rcases mm_cases (j + 1) with h | ⟨h, h2, h3⟩
    · rw [h]; ring
    · have hodd : Odd j := by rw [Nat.odd_iff]; omega
      have hp : (-1 : ℤ) ^ j = -1 := hodd.neg_one_pow
      rw [h, pow_succ, hp]; ring

/-! ### The series defining `z*` -/

/-- `t_i = S_i / (Q_i Q_{i+1})`. -/
def tt (i : ℕ) : ℝ := (SS i : ℝ) / ((Qsel i : ℝ) * (Qsel (i + 1) : ℝ))

/-- `f_i = (-1)^i t_i`. -/
def ff (i : ℕ) : ℝ := (-1 : ℝ) ^ i * tt i

lemma tt_nonneg (i : ℕ) : 0 ≤ tt i :=
  div_nonneg (SS_nonneg i) (mul_pos (q_pos i) (q_pos (i + 1))).le

lemma tt_le (i : ℕ) : tt i ≤ 2 / (Qsel (i + 1) : ℝ) := by
  unfold tt
  have h0 := q_pos i
  have h1 := q_pos (i + 1)
  rw [div_le_div_iff₀ (mul_pos h0 h1) h1]
  nlinarith [mul_le_mul_of_nonneg_right (SS_le i) h1.le]

lemma ff_abs (i : ℕ) : |ff i| = tt i := by
  unfold ff
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (tt_nonneg i)]

lemma ff_summable : Summable ff := by
  have hg : Summable (fun i : ℕ => 2 * (1 / 6 : ℝ) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
  refine Summable.of_norm_bounded hg (fun i => ?_)
  rw [Real.norm_eq_abs, ff_abs]
  have h6 : (0 : ℝ) < 6 ^ i := by positivity
  calc tt i ≤ 2 / (Qsel (i + 1) : ℝ) := tt_le i
    _ ≤ 2 / 6 ^ i := div_le_div_of_nonneg_left (by norm_num) h6 (q_six_pow i)
    _ = 2 * (1 / 6 : ℝ) ^ i := by rw [one_div, inv_pow, div_eq_mul_inv]

/-- The limit point `z*`. -/
def zs : ℝ := ∑' i, ff i

lemma nn_div_succ (j : ℕ) :
    (nn (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) - (nn j : ℝ) / (Qsel j : ℝ) = ff j := by
  have h0 := (q_pos j).ne'
  have h1 := (q_pos (j + 1)).ne'
  have hE : (nn (j + 1) : ℝ) * Qsel j - nn j * Qsel (j + 1) = (-1) ^ j * SS j := by
    exact_mod_cast EE_eq j
  have e : ff j = ((nn (j + 1) : ℝ) * Qsel j - nn j * Qsel (j + 1))
      / ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ)) := by
    rw [hE]; unfold ff tt; ring
  rw [e]
  first | (field_simp; ring) | field_simp

lemma ff_partial (j : ℕ) : ∑ i ∈ Finset.range j, ff i = (nn j : ℝ) / (Qsel j : ℝ) := by
  induction j with
  | zero => simp [nn]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, ← nn_div_succ]; ring

/-- `y_j = Q_j z* - n_j`. -/
def yy (j : ℕ) : ℝ := (Qsel j : ℝ) * zs - (nn j : ℝ)

lemma yy_eq (j : ℕ) : yy j = (Qsel j : ℝ) * ∑' k, ff (k + j) := by
  have h := ff_summable.sum_add_tsum_nat_add j
  rw [ff_partial] at h
  have h0 := (q_pos j).ne'
  have e : (Qsel j : ℝ) * ((nn j : ℝ) / (Qsel j : ℝ)) = (nn j : ℝ) := by field_simp
  unfold yy zs
  rw [← h, mul_add, e]
  ring

lemma tail_bound (j : ℕ) : |∑' k, ff (k + 1 + j)| ≤ 12 / 5 / (Qsel (j + 2) : ℝ) := by
  have hq := q_pos (j + 2)
  have hq' := hq.ne'
  have hg : HasSum (fun k : ℕ => 2 / (Qsel (j + 2) : ℝ) * (1 / 6 : ℝ) ^ k)
      (2 / (Qsel (j + 2) : ℝ) * (1 - 1 / 6)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have key : ∀ k : ℕ, ‖ff (k + 1 + j)‖ ≤ 2 / (Qsel (j + 2) : ℝ) * (1 / 6 : ℝ) ^ k := by
    intro k
    rw [Real.norm_eq_abs, ff_abs]
    have h1 : tt (k + 1 + j) ≤ 2 / (Qsel (k + 1 + j + 1) : ℝ) := tt_le _
    have h2 := q_pow (j + 2) (by omega) k
    have e : k + 1 + j + 1 = j + 2 + k := by omega
    rw [e] at h1
    have h6 : (0 : ℝ) < 6 ^ k := by positivity
    have h3 : 2 / (Qsel (j + 2 + k) : ℝ) ≤ 2 / ((6 : ℝ) ^ k * (Qsel (j + 2) : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos h6 hq) h2
    calc tt (k + 1 + j) ≤ 2 / (Qsel (j + 2 + k) : ℝ) := h1
      _ ≤ 2 / ((6 : ℝ) ^ k * (Qsel (j + 2) : ℝ)) := h3
      _ = 2 / (Qsel (j + 2) : ℝ) * (1 / 6 : ℝ) ^ k := by
        rw [one_div, inv_pow]; field_simp
  have := tsum_of_norm_bounded hg (f := fun k => ff (k + 1 + j)) key
  rw [Real.norm_eq_abs] at this
  have e6 : (1 - 1 / 6 : ℝ)⁻¹ = 6 / 5 := by norm_num
  rw [e6] at this
  calc _ ≤ _ := this
    _ = 12 / 5 / (Qsel (j + 2) : ℝ) := by ring

lemma yy_decomp (j : ℕ) :
    |yy j - (-1) ^ j * ((SS j : ℝ) / (Qsel (j + 1) : ℝ))|
      ≤ 12 / 5 * (Qsel j : ℝ) / (Qsel (j + 2) : ℝ) := by
  have h0 := q_pos j
  have h0' := h0.ne'
  have hq1 := (q_pos (j + 1)).ne'
  have hs : Summable (fun k => ff (k + j)) := (summable_nat_add_iff j).2 ff_summable
  have hT : ∑' k, ff (k + j) = ff j + ∑' k, ff (k + 1 + j) := by
    rw [hs.tsum_eq_zero_add]
    simp only [zero_add]
  have e1 : (Qsel j : ℝ) * ff j = (-1) ^ j * ((SS j : ℝ) / (Qsel (j + 1) : ℝ)) := by
    unfold ff tt
    first | (field_simp; ring) | field_simp
  have e2 : yy j - (-1) ^ j * ((SS j : ℝ) / (Qsel (j + 1) : ℝ))
      = (Qsel j : ℝ) * ∑' k, ff (k + 1 + j) := by
    rw [yy_eq, hT, mul_add, e1]; ring
  rw [e2, abs_mul, abs_of_pos h0]
  calc (Qsel j : ℝ) * |∑' k, ff (k + 1 + j)|
      ≤ (Qsel j : ℝ) * (12 / 5 / (Qsel (j + 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left (tail_bound j) h0.le
    _ = 12 / 5 * (Qsel j : ℝ) / (Qsel (j + 2) : ℝ) := by ring

/-! ### Main estimates -/

lemma main_upper (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ 2 * |yy (m + 1)| ≤ (mm (m + 1) : ℝ) * ((m : ℝ) + 1) / 4 + 1 / 2 := by
  have hD := yy_decomp (m + 1)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ha := q_pos m
  have hb := q_pos (m + 1)
  have hc := q_pos (m + 1 + 1)
  have hd := q_pos (m + 1 + 2)
  have g1 := q_ge m hm
  have g2 := q_ge (m + 1) (by omega)
  have g3 := q_ge (m + 1 + 1) (by omega)
  have g3' : (4 * ((m + 1 + 1 : ℕ) : ℝ) + 2) * (Qsel (m + 1 + 1) : ℝ)
      ≤ (Qsel (m + 1 + 2) : ℝ) := g3
  push_cast at g2 g3'
  have h1 : 3 * ((m : ℝ) + 1) * (Qsel m : ℝ) ≤ (Qsel (m + 1) : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hm') ha.le]
  have h2 : 4 * ((m : ℝ) + 1) * (Qsel (m + 1) : ℝ) ≤ (Qsel (m + 1 + 1) : ℝ) := by
    nlinarith
  have h3 : 4 * ((m : ℝ) + 1) * (Qsel (m + 1 + 1) : ℝ) ≤ (Qsel (m + 1 + 2) : ℝ) := by
    nlinarith
  have hSS := SS_succ m
  have hSle := SS_le m
  have hS : (SS (m + 1) : ℝ) ≤ 2 * (Qsel m : ℝ) + (mm (m + 1) : ℝ) * (Qsel (m + 1) : ℝ) := by
    linarith
  have hμ0 : (0 : ℝ) ≤ (mm (m + 1) : ℝ) := by exact_mod_cast mm_nonneg (m + 1)
  have hμ1 : (mm (m + 1) : ℝ) ≤ 1 := by exact_mod_cast mm_le_one (m + 1)
  have hnorm : |(-1 : ℝ) ^ (m + 1) * ((SS (m + 1) : ℝ) / (Qsel (m + 1 + 1) : ℝ))|
      = (SS (m + 1) : ℝ) / (Qsel (m + 1 + 1) : ℝ) := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (div_nonneg (SS_nonneg _) hc.le)]
  have hY : |yy (m + 1)| ≤ (SS (m + 1) : ℝ) / (Qsel (m + 1 + 1) : ℝ)
      + 12 / 5 * (Qsel (m + 1) : ℝ) / (Qsel (m + 1 + 2) : ℝ) := by
    have := abs_sub_abs_le_abs_sub (yy (m + 1))
      ((-1 : ℝ) ^ (m + 1) * ((SS (m + 1) : ℝ) / (Qsel (m + 1 + 1) : ℝ)))
    rw [hnorm] at this
    linarith
  exact real_upper ((m : ℝ) + 1) _ _ _ _ _ _ _ _ (by linarith) ha hb hc hd h1 h2 h3
    (SS_nonneg _) hS hμ0 hμ1 hY rfl

lemma main_lower (m : ℕ) (hm : 1 ≤ m) (hmm : mm (m + 1) = 1) :
    ((m : ℝ) + 1) / 4 - 1 / 2 ≤ ((m : ℝ) + 1) ^ 2 * yy (m + 1) := by
  have hD := yy_decomp (m + 1)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ha := q_pos m
  have hb := q_pos (m + 1)
  have hc := q_pos (m + 1 + 1)
  have hd := q_pos (m + 1 + 2)
  have g2 := q_ge (m + 1) (by omega)
  have g3 := q_ge (m + 1 + 1) (by omega)
  have g3' : (4 * ((m + 1 + 1 : ℕ) : ℝ) + 2) * (Qsel (m + 1 + 1) : ℝ)
      ≤ (Qsel (m + 1 + 2) : ℝ) := g3
  have g4 := q_le (m + 1) (by omega)
  push_cast at g2 g3' g4
  have h2 : 4 * ((m : ℝ) + 1) * (Qsel (m + 1) : ℝ) ≤ (Qsel (m + 1 + 1) : ℝ) := by
    nlinarith
  have h2' : (Qsel (m + 1 + 1) : ℝ) ≤ (4 * ((m : ℝ) + 1) + 3) * (Qsel (m + 1) : ℝ) := by
    linarith
  have h3 : 4 * ((m : ℝ) + 1) * (Qsel (m + 1 + 1) : ℝ) ≤ (Qsel (m + 1 + 2) : ℝ) := by
    nlinarith
  have hmm' : mm (m + 1) = 1 := hmm
  have hpar : (m + 1) % 2 = 0 := ((mm_cases (m + 1)).resolve_left (by rw [hmm]; norm_num)).2.2
  have hev : Even (m + 1) := by rw [Nat.even_iff]; exact hpar
  have hsgn : (-1 : ℝ) ^ (m + 1) = 1 := hev.neg_one_pow
  have hSS := SS_succ m
  have hS0 := SS_nonneg m
  have hmmR : (mm (m + 1) : ℝ) = 1 := by exact_mod_cast hmm
  have hS : (Qsel (m + 1) : ℝ) ≤ (SS (m + 1) : ℝ) := by
    rw [hSS, hmmR]; linarith
  rw [hsgn, one_mul] at hD
  have hY := (abs_le.1 hD).1
  have hY' : (SS (m + 1) : ℝ) / (Qsel (m + 1 + 1) : ℝ)
      - 12 / 5 * (Qsel (m + 1) : ℝ) / (Qsel (m + 1 + 2) : ℝ) ≤ yy (m + 1) := by linarith
  exact real_lower ((m : ℝ) + 1) _ _ _ _ _ _ _ (by linarith) ha hb hc hd h2 h2' h3 hS hY' rfl

/-! ### Conclusion -/

lemma dist_le_abs (j : ℕ) : distToNearestInt ((Qsel j : ℝ) * zs) ≤ |yy j| := by
  have := distToNearestInt_le ((Qsel j : ℝ) * zs) (nn j)
  unfold yy
  exact this

lemma dist_eq_of (n : ℤ) (y : ℝ) (h0 : 0 ≤ y) (h1 : y < 1 / 2) :
    distToNearestInt ((n : ℝ) + y) = y := by
  have hr : round ((n : ℝ) + y) = n := by
    rw [round_eq, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  unfold distToNearestInt
  rw [hr]
  simp [abs_of_nonneg h0]

lemma upper_ev (c : ℝ) (hc : 1 / 4 < c) :
    ∀ᶠ j : ℕ in atTop, (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * zs) ≤ c := by
  have hε : 0 < c - 1 / 4 := by linarith
  rw [eventually_atTop]
  refine ⟨⌈1 / (2 * (c - 1 / 4))⌉₊ + 2, fun j hj => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hup := main_upper m hm
  have hμ : (mm (m + 1) : ℝ) ≤ 1 := by exact_mod_cast mm_le_one (m + 1)
  have hJ : 1 / (2 * (c - 1 / 4)) ≤ (m : ℝ) + 1 := by
    have h1 := Nat.le_ceil (1 / (2 * (c - 1 / 4)))
    have h2 : ((⌈1 / (2 * (c - 1 / 4))⌉₊ : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : ⌈1 / (2 * (c - 1 / 4))⌉₊ ≤ m + 1)
    push_cast at h2
    linarith
  have hJε : 1 / 2 ≤ ((m : ℝ) + 1) * (c - 1 / 4) := by
    have h := (div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (c - 1 / 4))).1 hJ
    nlinarith
  have hd := dist_le_abs (m + 1)
  have hJ0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  push_cast
  by_contra hcon
  push_neg at hcon
  have h3 : c < ((m : ℝ) + 1) * |yy (m + 1)| :=
    lt_of_lt_of_le hcon (mul_le_mul_of_nonneg_left hd hJ0.le)
  have h4 := mul_lt_mul_of_pos_left h3 hJ0
  have h5 := mul_le_mul_of_nonneg_right hμ hJ0.le
  nlinarith

lemma lower_key (m : ℕ) (h10 : 10 ≤ m + 1) (hpar : (m + 1) % 2 = 0) :
    (1 : ℝ) / 5 ≤ ((m + 1 : ℕ) : ℝ) * distToNearestInt ((Qsel (m + 1) : ℝ) * zs) := by
  have hm1 : 1 ≤ m := by omega
  have hmm : mm (m + 1) = 1 := by
    unfold mm
    rw [if_pos]
    constructor <;> omega
  have hlow := main_lower m hm1 hmm
  have hup := main_upper m hm1
  have hmmR : (mm (m + 1) : ℝ) = 1 := by exact_mod_cast hmm
  rw [hmmR] at hup
  have hJ10 : (10 : ℝ) ≤ (m : ℝ) + 1 := by
    have h : ((10 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_le.2 h10
    push_cast at h
    linarith
  have hJ0 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hy_pos : 0 < yy (m + 1) := by
    by_contra h
    push_neg at h
    have : ((m : ℝ) + 1) ^ 2 * yy (m + 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hy_lt : yy (m + 1) < 1 / 2 := by
    by_contra h
    push_neg at h
    have h1 : ((m : ℝ) + 1) ^ 2 * (1 / 2) ≤ ((m : ℝ) + 1) ^ 2 * yy (m + 1) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : ((m : ℝ) + 1) ^ 2 * yy (m + 1) ≤ ((m : ℝ) + 1) ^ 2 * |yy (m + 1)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.2 hJ10) hJ0.le]
  have e : (Qsel (m + 1) : ℝ) * zs = ((nn (m + 1) : ℤ) : ℝ) + yy (m + 1) := by
    unfold yy; ring
  rw [e, dist_eq_of _ _ hy_pos.le hy_lt]
  push_cast
  by_contra h
  push_neg at h
  have h' := mul_lt_mul_of_pos_left h hJ0
  nlinarith

lemma lower_freq :
    ∃ᶠ j : ℕ in atTop, (1 : ℝ) / 5 ≤ (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * zs) := by
  rw [frequently_atTop]
  intro a
  refine ⟨2 * (a + 5), by omega, ?_⟩
  have := lower_key (2 * (a + 5) - 1) (by omega) (by omega)
  rwa [show 2 * (a + 5) - 1 + 1 = 2 * (a + 5) by omega] at this

end

end KappaSharp

theorem kappa_sharp : ∃ z : ℝ, z ∉ Classification.latticeL ∧
    (∀ c : ℝ, 1/4 < c → ∀ᶠ j : ℕ in Filter.atTop, (j:ℝ) * distToNearestInt ((Qsel j : ℝ) * z) ≤ c) ∧
    (∃ᶠ j : ℕ in Filter.atTop, (1:ℝ)/5 ≤ (j:ℝ) * distToNearestInt ((Qsel j : ℝ) * z)) := by
  refine ⟨KappaSharp.zs, ?_, fun c hc => KappaSharp.upper_ev c hc, KappaSharp.lower_freq⟩
  intro hz
  have ht := (Classification.theorem2_classification KappaSharp.zs).2 hz
  have hev := (tendsto_order.1 ht).2 (1 / 5) (by norm_num)
  obtain ⟨j, hj1, hj2⟩ := (KappaSharp.lower_freq.and_eventually hev).exists
  linarith

theorem kappa_eq_quarter :
    (∀ z ∉ Classification.latticeL, ∀ c : ℝ, c < 1/4 →
      ¬ ∀ᶠ j : ℕ in Filter.atTop, (j:ℝ) * distToNearestInt ((Qsel j:ℝ) * z) ≤ c) ∧
    (∃ z ∉ Classification.latticeL, ∀ c : ℝ, c > 1/4 →
      ∀ᶠ j : ℕ in Filter.atTop, (j:ℝ) * distToNearestInt ((Qsel j:ℝ) * z) ≤ c) := by
  refine ⟨fun z hz c hc => Classification.corollary3_gap z hz c hc, ?_⟩
  obtain ⟨z, hz, h1, -⟩ := kappa_sharp
  exact ⟨z, hz, fun c hc => h1 c hc⟩
