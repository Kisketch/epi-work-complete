import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# THM-0006 (general dichotomy), standalone formalization

No project axioms, no `sorry`.  Indexing: `Q (j+2) = a (j+1) * Q (j+1) + Q j`, i.e.
`Q_{j+1} = a_j Q_j + Q_{j-1}` for `j ≥ 1`; the partial quotient `a j` is paired with `Q j`.
-/

open Filter Topology

namespace GeneralDichotomy

noncomputable section

/-- distance to the nearest integer -/
def dist0 (x : ℝ) : ℝ := |x - round x|

/-- the recurrence sequence with prescribed first two terms -/
def seq (a : ℕ → ℤ) (q0 q1 : ℤ) : ℕ → ℤ
  | 0 => q0
  | 1 => q1
  | (j+2) => a (j+1) * seq a q0 q1 (j+1) + seq a q0 q1 j

/-- the determinant `D = P0 Q1 - P1 Q0` -/
def D (P Q : ℕ → ℤ) : ℤ := P 0 * Q 1 - P 1 * Q 0

/-- hypotheses (H) -/
structure Data (a Q P : ℕ → ℤ) : Prop where
  ha1 : ∀ j, 1 ≤ j → 1 ≤ a j
  hat : Tendsto (fun j => (a j : ℝ)) atTop atTop
  hQ : ∀ j, Q (j+2) = a (j+1) * Q (j+1) + Q j
  hP : ∀ j, P (j+2) = a (j+1) * P (j+1) + P j
  hQ0 : 0 ≤ Q 0
  hQ1 : 1 ≤ Q 1
  hD : D P Q ≠ 0

variable {a Q P : ℕ → ℤ}

/-- T1: Casoratian -/
theorem casoratian (h : Data a Q P) (j : ℕ) :
    P j * Q (j+1) - P (j+1) * Q j = (-1) ^ j * D P Q := by
  induction j with
  | zero => simp [D]
  | succ n ih =>
    have e1 : Q (n+1+1) = a (n+1) * Q (n+1) + Q n := h.hQ n
    have e2 : P (n+1+1) = a (n+1) * P (n+1) + P n := h.hP n
    rw [e1, e2, pow_succ]
    linear_combination (-1 : ℤ) * ih

lemma cast_casoratian (h : Data a Q P) (j : ℕ) :
    (P j : ℝ) * Q (j+1) - P (j+1) * Q j = (-1) ^ j * ((D P Q : ℤ) : ℝ) := by
  exact_mod_cast casoratian h j

lemma Q_facts (h : Data a Q P) : ∀ n, 0 ≤ Q n ∧ 1 ≤ Q (n+1) := by
  intro n
  induction n with
  | zero => exact ⟨h.hQ0, h.hQ1⟩
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have ha := h.ha1 (n+1) (by omega)
    have e : Q (n+1+1) = a (n+1) * Q (n+1) + Q n := h.hQ n
    refine ⟨by linarith, ?_⟩
    have : 1 ≤ a (n+1) * Q (n+1) := by nlinarith
    show 1 ≤ Q (n+1+1)
    rw [e]; linarith

lemma Q_ge_one (h : Data a Q P) (j : ℕ) (hj : 1 ≤ j) : 1 ≤ Q j := by
  cases j with
  | zero => omega
  | succ k => exact (Q_facts h k).2

lemma Q_step (h : Data a Q P) (j : ℕ) (hj : 1 ≤ j) : a j * Q j ≤ Q (j+1) := by
  cases j with
  | zero => omega
  | succ k =>
    have e : Q (k+1+1) = a (k+1) * Q (k+1) + Q k := h.hQ k
    have := (Q_facts h k).1
    show a (k+1) * Q (k+1) ≤ Q (k+1+1)
    rw [e]; linarith

lemma Qr_ge_one (h : Data a Q P) (j : ℕ) (hj : 1 ≤ j) : (1 : ℝ) ≤ Q j := by
  exact_mod_cast Q_ge_one h j hj

lemma Qr_step (h : Data a Q P) (j : ℕ) (hj : 1 ≤ j) : (a j : ℝ) * Q j ≤ Q (j+1) := by
  exact_mod_cast Q_step h j hj

lemma ar_ge_one (h : Data a Q P) (j : ℕ) (hj : 1 ≤ j) : (1 : ℝ) ≤ a j := by
  exact_mod_cast h.ha1 j hj

lemma Q_tendsto (h : Data a Q P) : Tendsto (fun j => (Q j : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => (a (n+1) : ℝ)) atTop atTop :=
    (tendsto_add_atTop_iff_nat (f := fun j : ℕ => (a j : ℝ)) 1).2 h.hat
  have h2 : Tendsto (fun n : ℕ => (Q (n+1+1) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) h1
    have e1 := Qr_ge_one h (n+1) (by omega)
    have e2 := Qr_step h (n+1) (by omega)
    have e3 := ar_ge_one h (n+1) (by omega)
    show (a (n+1) : ℝ) ≤ Q (n+1+1)
    nlinarith
  exact (tendsto_add_atTop_iff_nat (f := fun j : ℕ => (Q j : ℝ)) 2).1 h2

/-! ### T2: convergents -/

/-- the convergent ratio -/
def xx (P Q : ℕ → ℤ) (j : ℕ) : ℝ := (P j : ℝ) / (Q j : ℝ)

lemma xx_step (h : Data a Q P) (j : ℕ) (hj : 1 ≤ j) :
    xx P Q (j+2) ∈ segment ℝ (xx P Q j) (xx P Q (j+1)) := by
  have hq1 : (1:ℝ) ≤ Q j := Qr_ge_one h j hj
  have hq2 : (1:ℝ) ≤ Q (j+1) := Qr_ge_one h (j+1) (by omega)
  have hA : (1:ℝ) ≤ a (j+1) := ar_ge_one h (j+1) (by omega)
  have hQr : (Q (j+2) : ℝ) = a (j+1) * Q (j+1) + Q j := by exact_mod_cast h.hQ j
  have hPr : (P (j+2) : ℝ) = a (j+1) * P (j+1) + P j := by exact_mod_cast h.hP j
  have hpos : (0:ℝ) < Q (j+2) := by rw [hQr]; nlinarith
  have hq1ne : (Q j : ℝ) ≠ 0 := by linarith
  have hq2ne : (Q (j+1) : ℝ) ≠ 0 := by linarith
  have hq3ne : (Q (j+2) : ℝ) ≠ 0 := hpos.ne'
  refine ⟨(Q j : ℝ) / Q (j+2), (a (j+1) : ℝ) * Q (j+1) / Q (j+2),
    div_nonneg (by linarith) hpos.le,
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hpos.le, ?_, ?_⟩
  · rw [← add_div, div_eq_one_iff_eq hq3ne]; linarith
  · simp only [smul_eq_mul, xx]
    have e1 : (Q j : ℝ) / Q (j+2) * (P j / Q j) = P j / Q (j+2) := by field_simp
    have e2 : (a (j+1) : ℝ) * Q (j+1) / Q (j+2) * (P (j+1) / Q (j+1))
        = a (j+1) * P (j+1) / Q (j+2) := by field_simp
    rw [e1, e2, ← add_div, hPr]; ring

lemma xx_nest (h : Data a Q P) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    xx P Q (n+m) ∈ segment ℝ (xx P Q n) (xx P Q (n+1)) ∧
    xx P Q (n+m+1) ∈ segment ℝ (xx P Q n) (xx P Q (n+1)) := by
  induction m with
  | zero => exact ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have hs := xx_step h (n+m) (by omega)
    exact (convex_segment (xx P Q n) (xx P Q (n+1))).segment_subset ih.1 ih.2 hs

lemma xx_mem (h : Data a Q P) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : n ≤ m) :
    xx P Q m ∈ segment ℝ (xx P Q n) (xx P Q (n+1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact (xx_nest h n hn d).1

lemma seg_abs {x y z : ℝ} (hz : z ∈ segment ℝ x y) : |z - x| ≤ |y - x| := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hz
  have e : p • x + q • y - x = q * (y - x) := by
    simp only [smul_eq_mul]
    rw [show p = 1 - q by linarith]; ring
  rw [e, abs_mul, abs_of_nonneg hq]
  have : q ≤ 1 := by linarith
  nlinarith [abs_nonneg (y - x)]

lemma xx_gap (h : Data a Q P) (n : ℕ) (hn : 1 ≤ n) :
    |xx P Q (n+1) - xx P Q n| = |((D P Q : ℤ) : ℝ)| / ((Q n : ℝ) * Q (n+1)) := by
  have c := cast_casoratian h n
  have hq0 : (0:ℝ) < Q n := by have := Qr_ge_one h n hn; linarith
  have hq1 : (0:ℝ) < Q (n+1) := by have := Qr_ge_one h (n+1) (by omega); linarith
  have hq0ne : (Q n : ℝ) ≠ 0 := hq0.ne'
  have hq1ne : (Q (n+1) : ℝ) ≠ 0 := hq1.ne'
  have e : xx P Q (n+1) - xx P Q n
      = -((-1 : ℝ) ^ n * ((D P Q : ℤ) : ℝ)) / ((Q n : ℝ) * Q (n+1)) := by
    unfold xx
    rw [eq_div_iff (mul_ne_zero hq0ne hq1ne), ← c]
    first | (field_simp; ring) | field_simp | ring
  rw [e, abs_div, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (mul_pos hq0 hq1)]

theorem T2 (h : Data a Q P) :
    ∃ θ : ℝ, Tendsto (fun j => (P j : ℝ) / Q j) atTop (𝓝 θ) ∧
      ∀ j, 1 ≤ j → |(Q j : ℝ) * θ - P j| ≤ |((D P Q : ℤ) : ℝ)| / Q (j+1) := by
  have hQ2 : Tendsto (fun N : ℕ => (Q (N+1+1) : ℝ)) atTop atTop :=
    (tendsto_add_atTop_iff_nat (f := fun j : ℕ => (Q j : ℝ)) 2).2 (Q_tendsto h)
  have hcauchy : CauchySeq (fun k => xx P Q (k+1)) := by
    refine cauchySeq_of_le_tendsto_0
      (fun N => 2 * (|((D P Q : ℤ) : ℝ)| / Q (N+1+1))) ?_ ?_
    · intro n m N hn hm
      have h1 := xx_mem h (N+1) (by omega) (n+1) (by omega)
      have h2 := xx_mem h (N+1) (by omega) (m+1) (by omega)
      have g1 := seg_abs h1
      have g2 := seg_abs h2
      have hg := xx_gap h (N+1) (by omega)
      have hq1 : (1:ℝ) ≤ Q (N+1) := Qr_ge_one h (N+1) (by omega)
      have hq2 : (1:ℝ) ≤ Q (N+1+1) := Qr_ge_one h (N+1+1) (by omega)
      have hgap : |xx P Q (N+1+1) - xx P Q (N+1)|
          ≤ |((D P Q : ℤ) : ℝ)| / Q (N+1+1) := by
        rw [hg, div_le_div_iff₀ (by positivity) (by linarith)]
        nlinarith [mul_nonneg (mul_nonneg (abs_nonneg ((D P Q : ℤ) : ℝ)) (by linarith : (0:ℝ) ≤ Q (N+1+1)))
          (sub_nonneg.2 hq1)]
      rw [Real.dist_eq]
      have := abs_sub_le (xx P Q (n+1)) (xx P Q (N+1)) (xx P Q (m+1))
      rw [abs_sub_comm (xx P Q (N+1)) (xx P Q (m+1))] at this
      linarith
    · have := ((tendsto_const_nhds (x := |((D P Q : ℤ) : ℝ)|)).div_atTop hQ2).const_mul 2
      simpa using this
  obtain ⟨θ, hθ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hx : Tendsto (xx P Q) atTop (𝓝 θ) :=
    (tendsto_add_atTop_iff_nat (f := xx P Q) 1).1 hθ
  refine ⟨θ, hx, ?_⟩
  intro j hj
  have hclosed : IsClosed (segment ℝ (xx P Q j) (xx P Q (j+1))) := by
    rw [segment_eq_uIcc]; exact isClosed_Icc
  have hmem : θ ∈ segment ℝ (xx P Q j) (xx P Q (j+1)) :=
    hclosed.mem_of_tendsto hx (eventually_atTop.2 ⟨j, fun m hm => xx_mem h j hj m hm⟩)
  have g := seg_abs hmem
  rw [xx_gap h j hj] at g
  have hq0 : (0:ℝ) < Q j := by have := Qr_ge_one h j hj; linarith
  have hq1 : (0:ℝ) < Q (j+1) := by have := Qr_ge_one h (j+1) (by omega); linarith
  have e : (Q j : ℝ) * θ - P j = Q j * (θ - xx P Q j) := by
    unfold xx; field_simp
  rw [e, abs_mul, abs_of_pos hq0]
  calc (Q j : ℝ) * |θ - xx P Q j|
      ≤ Q j * (|((D P Q : ℤ) : ℝ)| / (Q j * Q (j+1))) := by gcongr
    _ = |((D P Q : ℤ) : ℝ)| / Q (j+1) := by field_simp


/-! ### T3: the dichotomy -/

/-- `δ_j = Q_j θ - P_j` -/
def delta (P Q : ℕ → ℤ) (θ : ℝ) (j : ℕ) : ℝ := (Q j : ℝ) * θ - P j

/-- the group `L = {(u δ₁ - v δ₀)/D}` -/
def Lset (P Q : ℕ → ℤ) (θ : ℝ) : Set ℝ :=
  {z | ∃ u v : ℤ, z = ((u : ℝ) * delta P Q θ 1 - (v : ℝ) * delta P Q θ 0) / ((D P Q : ℤ) : ℝ)}

lemma Qr_rec (h : Data a Q P) (j : ℕ) : (Q (j+2) : ℝ) = a (j+1) * Q (j+1) + Q j := by
  exact_mod_cast h.hQ j

lemma Pr_rec (h : Data a Q P) (j : ℕ) : (P (j+2) : ℝ) = a (j+1) * P (j+1) + P j := by
  exact_mod_cast h.hP j

lemma delta_rec (h : Data a Q P) (θ : ℝ) (j : ℕ) :
    delta P Q θ (j+2) = a (j+1) * delta P Q θ (j+1) + delta P Q θ j := by
  unfold delta
  rw [Qr_rec h j, Pr_rec h j]; ring

lemma Dr_expand (P Q : ℕ → ℤ) : ((D P Q : ℤ) : ℝ) = (P 0 : ℝ) * Q 1 - P 1 * Q 0 := by
  simp [D]

lemma Dr_ne (h : Data a Q P) : ((D P Q : ℤ) : ℝ) ≠ 0 := by
  exact_mod_cast h.hD

/-- two sequences with the same recurrence agreeing at two consecutive indices agree after -/
lemma rec_eq (a : ℕ → ℤ) (f g : ℕ → ℝ) (J : ℕ)
    (hf : ∀ j, J ≤ j → f (j+2) = a (j+1) * f (j+1) + f j)
    (hg : ∀ j, J ≤ j → g (j+2) = a (j+1) * g (j+1) + g j)
    (h0 : f J = g J) (h1 : f (J+1) = g (J+1)) :
    ∀ k, f (J+k) = g (J+k) ∧ f (J+k+1) = g (J+k+1) := by
  intro k
  induction k with
  | zero => exact ⟨h0, h1⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have e1 : f (J+k+2) = a (J+k+1) * f (J+k+1) + f (J+k) := hf (J+k) (by omega)
    have e2 : g (J+k+2) = a (J+k+1) * g (J+k+1) + g (J+k) := hg (J+k) (by omega)
    show f (J+k+2) = g (J+k+2)
    rw [e1, e2, ih.1, ih.2]

lemma rec_eq' (a : ℕ → ℤ) (f g : ℕ → ℝ) (J : ℕ)
    (hf : ∀ j, J ≤ j → f (j+2) = a (j+1) * f (j+1) + f j)
    (hg : ∀ j, J ≤ j → g (j+2) = a (j+1) * g (j+1) + g j)
    (h0 : f J = g J) (h1 : f (J+1) = g (J+1)) :
    ∀ j, J ≤ j → f j = g j := by
  intro j hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact (rec_eq a f g J hf hg h0 h1 k).1

/-- backward integrality -/
lemma back_int (a : ℕ → ℤ) (f : ℕ → ℝ)
    (hf : ∀ j, f (j+2) = a (j+1) * f (j+1) + f j) :
    ∀ J : ℕ, ∀ k1 k2 : ℤ, f J = k1 → f (J+1) = k2 →
      ∃ m1 m2 : ℤ, f 0 = m1 ∧ f 1 = m2 := by
  intro J
  induction J with
  | zero => intro k1 k2 h1 h2; exact ⟨k1, k2, h1, h2⟩
  | succ J ih =>
    intro k1 k2 h1 h2
    have e : f (J+1+1) = a (J+1) * f (J+1) + f J := hf J
    refine ih (k2 - a (J+1) * k1) k1 ?_ h1
    push_cast
    rw [← h1, ← h2]
    have : f (J+1+1) = k2 := h2
    linarith

lemma ident0 (q0 q1 p0 p1 θ u v : ℝ) (hD : p0 * q1 - p1 * q0 ≠ 0) :
    q0 * ((u * (q1 * θ - p1) - v * (q0 * θ - p0)) / (p0 * q1 - p1 * q0)) - u
      = ((u * q1 - v * q0) / (p0 * q1 - p1 * q0)) * (q0 * θ - p0) := by
  generalize hΔ : p0 * q1 - p1 * q0 = Δ at hD ⊢
  field_simp
  subst hΔ
  ring

lemma ident1 (q0 q1 p0 p1 θ u v : ℝ) (hD : p0 * q1 - p1 * q0 ≠ 0) :
    q1 * ((u * (q1 * θ - p1) - v * (q0 * θ - p0)) / (p0 * q1 - p1 * q0)) - v
      = ((u * q1 - v * q0) / (p0 * q1 - p1 * q0)) * (q1 * θ - p1) := by
  generalize hΔ : p0 * q1 - p1 * q0 = Δ at hD ⊢
  field_simp
  subst hΔ
  ring

lemma solve2 (q0 q1 d0 d1 y0 y1 : ℝ) (hΔ : q0 * d1 - q1 * d0 ≠ 0) :
    ((y0 * d1 - y1 * d0) / (q0 * d1 - q1 * d0)) * q0
      + ((q0 * y1 - q1 * y0) / (q0 * d1 - q1 * d0)) * d0 = y0 ∧
    ((y0 * d1 - y1 * d0) / (q0 * d1 - q1 * d0)) * q1
      + ((q0 * y1 - q1 * y0) / (q0 * d1 - q1 * d0)) * d1 = y1 := by
  generalize hΔ' : q0 * d1 - q1 * d0 = Δ at hΔ ⊢
  constructor
  · field_simp; subst hΔ'; ring
  · field_simp; subst hΔ'; ring

lemma delta_tendsto (h : Data a Q P) (θ : ℝ)
    (hθ : ∀ j, 1 ≤ j → |(Q j : ℝ) * θ - P j| ≤ |((D P Q : ℤ) : ℝ)| / Q (j+1)) :
    Tendsto (fun j => delta P Q θ j) atTop (𝓝 0) := by
  have hQ1 : Tendsto (fun n : ℕ => (Q (n+1) : ℝ)) atTop atTop :=
    (tendsto_add_atTop_iff_nat (f := fun j : ℕ => (Q j : ℝ)) 1).2 (Q_tendsto h)
  have hb : Tendsto (fun n : ℕ => |((D P Q : ℤ) : ℝ)| / (Q (n+1) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hQ1
  refine (tendsto_zero_iff_abs_tendsto_zero _).2
      (squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hb)
  filter_upwards [eventually_ge_atTop 1] with j hj
  exact hθ j hj

theorem T3A (h : Data a Q P) (θ : ℝ)
    (hθ : ∀ j, 1 ≤ j → |(Q j : ℝ) * θ - P j| ≤ |((D P Q : ℤ) : ℝ)| / Q (j+1))
    (z : ℝ) (hz : z ∈ Lset P Q θ) :
    Tendsto (fun j => (a j : ℝ) * dist0 ((Q j : ℝ) * z)) atTop (𝓝 0) := by
  obtain ⟨u, v, hzdef⟩ := hz
  have hDr := Dr_expand P Q
  have hDne : (P 0 : ℝ) * Q 1 - P 1 * Q 0 ≠ 0 := by rw [← hDr]; exact Dr_ne h
  have hz' : z = ((u : ℝ) * ((Q 1 : ℝ) * θ - P 1) - (v : ℝ) * ((Q 0 : ℝ) * θ - P 0))
      / ((P 0 : ℝ) * Q 1 - P 1 * Q 0) := by
    rw [hzdef, hDr]; rfl
  set ε : ℝ := ((u : ℝ) * Q 1 - (v : ℝ) * Q 0) / ((P 0 : ℝ) * Q 1 - P 1 * Q 0) with hε
  obtain ⟨N, hN0, hN1, hNr⟩ : ∃ N : ℕ → ℤ, N 0 = u ∧ N 1 = v ∧
      ∀ j, N (j+2) = a (j+1) * N (j+1) + N j :=
    ⟨seq a u v, rfl, rfl, fun j => rfl⟩
  have hNr' : ∀ j, (N (j+2) : ℝ) = a (j+1) * N (j+1) + N j := fun j => by exact_mod_cast hNr j
  have key : ∀ j, (Q j : ℝ) * z - N j = ε * delta P Q θ j := by
    have := rec_eq' a (fun j => (Q j : ℝ) * z - N j) (fun j => ε * delta P Q θ j) 0
      (fun j _ => by
        show (Q (j+2) : ℝ) * z - N (j+2) = a (j+1) * ((Q (j+1) : ℝ) * z - N (j+1))
          + ((Q j : ℝ) * z - N j)
        rw [Qr_rec h j, hNr' j]; ring)
      (fun j _ => by
        show ε * delta P Q θ (j+2) = a (j+1) * (ε * delta P Q θ (j+1)) + ε * delta P Q θ j
        rw [delta_rec h θ j]; ring)
      (by
        show (Q 0 : ℝ) * z - N 0 = ε * delta P Q θ 0
        rw [hN0, hz']
        exact ident0 _ _ _ _ θ _ _ hDne)
      (by
        show (Q 1 : ℝ) * z - N 1 = ε * delta P Q θ 1
        rw [hN1, hz']
        exact ident1 _ _ _ _ θ _ _ hDne)
    intro j
    exact this j (Nat.zero_le j)
  have hbound : Tendsto (fun j : ℕ => |ε| * |((D P Q : ℤ) : ℝ)| / (Q j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Q_tendsto h)
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have := ar_ge_one h j hj
    unfold dist0
    exact mul_nonneg (by linarith) (abs_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have hq : (0:ℝ) < Q j := by have := Qr_ge_one h j hj; linarith
    have hq1 : (0:ℝ) < Q (j+1) := by have := Qr_ge_one h (j+1) (by omega); linarith
    have ha : (0:ℝ) < a j := by have := ar_ge_one h j hj; linarith
    have hst := Qr_step h j hj
    have hd := hθ j hj
    have hd' : |delta P Q θ j| * Q (j+1) ≤ |((D P Q : ℤ) : ℝ)| := by
      have : |delta P Q θ j| ≤ |((D P Q : ℤ) : ℝ)| / Q (j+1) := hd
      rwa [le_div_iff₀ hq1] at this
    have h1 : dist0 ((Q j : ℝ) * z) ≤ |ε| * |delta P Q θ j| := by
      have := round_le ((Q j : ℝ) * z) (N j)
      unfold dist0
      rw [key j, abs_mul] at this
      exact this
    have h2 : (a j : ℝ) * |delta P Q θ j| ≤ |((D P Q : ℤ) : ℝ)| / Q j := by
      rw [le_div_iff₀ hq]
      nlinarith [mul_nonneg (sub_nonneg.2 hst) (abs_nonneg (delta P Q θ j))]
    calc (a j : ℝ) * dist0 ((Q j : ℝ) * z) ≤ a j * (|ε| * |delta P Q θ j|) :=
          mul_le_mul_of_nonneg_left h1 ha.le
      _ = |ε| * ((a j : ℝ) * |delta P Q θ j|) := by ring
      _ ≤ |ε| * (|((D P Q : ℤ) : ℝ)| / Q j) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = |ε| * |((D P Q : ℤ) : ℝ)| / Q j := by ring

theorem T3B (h : Data a Q P) (θ : ℝ)
    (hθ : ∀ j, 1 ≤ j → |(Q j : ℝ) * θ - P j| ≤ |((D P Q : ℤ) : ℝ)| / Q (j+1))
    (z : ℝ) (hz : z ∉ Lset P Q θ) (c : ℝ) (hc : c < 1) :
    ¬ ∀ᶠ j in atTop, (a j : ℝ) * dist0 ((Q j : ℝ) * z) ≤ c := by
  intro hev
  apply hz
  have hc0 : max c 0 < 1 := max_lt hc one_pos
  have hc00 : 0 ≤ max c 0 := le_max_right _ _
  generalize hc0def : max c 0 = c0 at hc0 hc00
  have hev0 : ∀ᶠ j in atTop, (a j : ℝ) * dist0 ((Q j : ℝ) * z) ≤ c0 :=
    hev.mono (fun j hj => by rw [← hc0def]; exact hj.trans (le_max_left _ _))
  have hsmall : Tendsto (fun j => c0 / (a j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h.hat
  have hs1 : ∀ᶠ j in atTop, c0 / (a j : ℝ) < (1 - c0) / 2 :=
    hsmall.eventually (gt_mem_nhds (by linarith))
  obtain ⟨J1, hJ1⟩ := eventually_atTop.1 hs1
  obtain ⟨J2, hJ2⟩ := eventually_atTop.1 hev0
  obtain ⟨J, hJ1', hJ2', hJ0⟩ : ∃ J, J1 ≤ J ∧ J2 ≤ J ∧ 1 ≤ J :=
    ⟨max (max J1 J2) 1, by omega, by omega, by omega⟩
  -- the integers n_j and the errors y_j
  obtain ⟨n, hn⟩ : ∃ n : ℕ → ℤ, ∀ j, n j = round ((Q j : ℝ) * z) := ⟨_, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℝ, ∀ j, y j = (Q j : ℝ) * z - n j := ⟨_, fun _ => rfl⟩
  have hdist : ∀ j, dist0 ((Q j : ℝ) * z) = |y j| := by
    intro j; unfold dist0; rw [hy, hn]
  have hapos : ∀ j, J ≤ j → (0:ℝ) < a j := fun j hj => by
    have := ar_ge_one h j (by omega); linarith
  have hya : ∀ j, J ≤ j → (a j : ℝ) * |y j| ≤ c0 := fun j hj => by
    have := hJ2 j (by omega); rwa [hdist] at this
  have hy1 : ∀ j, J ≤ j → |y j| ≤ c0 / a j := fun j hj => by
    rw [le_div_iff₀ (hapos j hj)]
    have := hya j hj; linarith
  -- integrality of the recurrence defect
  have hm : ∀ j, J ≤ j → n (j+2) = a (j+1) * n (j+1) + n j := by
    intro j hj
    have hmr : ((n (j+2) - a (j+1) * n (j+1) - n j : ℤ) : ℝ)
        = -(y (j+2) - a (j+1) * y (j+1) - y j) := by
      push_cast
      rw [hy (j+2), hy (j+1), hy j, Qr_rec h j]; ring
    have b2 := hy1 (j+2) (by omega)
    have b0 := hy1 j hj
    have b1 : |(a (j+1) : ℝ) * y (j+1)| ≤ c0 := by
      rw [abs_mul, abs_of_pos (hapos (j+1) (by omega))]; exact hya (j+1) (by omega)
    have s2 := hJ1 (j+2) (by omega)
    have s0 := hJ1 j (by omega)
    obtain ⟨l2, u2⟩ := abs_le.1 b2
    obtain ⟨l0, u0⟩ := abs_le.1 b0
    obtain ⟨l1, u1⟩ := abs_le.1 b1
    have hlt : |((n (j+2) - a (j+1) * n (j+1) - n j : ℤ) : ℝ)| < 1 := by
      rw [hmr, abs_neg, abs_lt]
      constructor <;> linarith
    have hlt' : |(n (j+2) - a (j+1) * n (j+1) - n j : ℤ)| < 1 := by
      rw [← Int.cast_abs] at hlt
      exact_mod_cast hlt
    have := Int.abs_lt_one_iff.1 hlt'
    linarith
  have hmr : ∀ j, J ≤ j → (n (j+2) : ℝ) = a (j+1) * n (j+1) + n j := fun j hj => by
    exact_mod_cast hm j hj
  have hyrec : ∀ j, J ≤ j → y (j+2) = a (j+1) * y (j+1) + y j := by
    intro j hj
    rw [hy (j+2), hy (j+1), hy j, Qr_rec h j, hmr j hj]; ring
  -- the basis (Q, δ)
  have hΔ : (Q J : ℝ) * delta P Q θ (J+1) - (Q (J+1) : ℝ) * delta P Q θ J
      = (-1) ^ J * ((D P Q : ℤ) : ℝ) := by
    unfold delta
    linear_combination cast_casoratian h J
  have hΔne : (Q J : ℝ) * delta P Q θ (J+1) - (Q (J+1) : ℝ) * delta P Q θ J ≠ 0 := by
    rw [hΔ]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Dr_ne h)
  obtain ⟨hs0, hs1'⟩ := solve2 (Q J) (Q (J+1)) (delta P Q θ J) (delta P Q θ (J+1))
    (y J) (y (J+1)) hΔne
  set α : ℝ := (y J * delta P Q θ (J+1) - y (J+1) * delta P Q θ J) /
    ((Q J : ℝ) * delta P Q θ (J+1) - (Q (J+1) : ℝ) * delta P Q θ J) with hα
  set β : ℝ := ((Q J : ℝ) * y (J+1) - (Q (J+1) : ℝ) * y J) /
    ((Q J : ℝ) * delta P Q θ (J+1) - (Q (J+1) : ℝ) * delta P Q θ J) with hβ
  have hyg : ∀ j, J ≤ j → y j = α * Q j + β * delta P Q θ j := by
    have := rec_eq' a y (fun j => α * Q j + β * delta P Q θ j) J
      (fun j hj => hyrec j hj)
      (fun j _ => by
        show α * (Q (j+2) : ℝ) + β * delta P Q θ (j+2)
          = a (j+1) * (α * Q (j+1) + β * delta P Q θ (j+1)) + (α * Q j + β * delta P Q θ j)
        rw [Qr_rec h j, delta_rec h θ j]; ring)
      (by show y J = α * Q J + β * delta P Q θ J; exact hs0.symm)
      (by show y (J+1) = α * Q (J+1) + β * delta P Q θ (J+1); exact hs1'.symm)
    exact this
  -- α = 0
  have ty : Tendsto y atTop (𝓝 0) := by
    refine (tendsto_zero_iff_abs_tendsto_zero _).2
      (squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hsmall)
    filter_upwards [eventually_ge_atTop J] with j hj
    exact hy1 j hj
  have tδ := delta_tendsto h θ hθ
  have hαQ : Tendsto (fun j => α * (Q j : ℝ)) atTop (𝓝 0) := by
    have t : Tendsto (fun j => y j - β * delta P Q θ j) atTop (𝓝 (0 - β * 0)) :=
      ty.sub (tδ.const_mul β)
    have t' : Tendsto (fun j => y j - β * delta P Q θ j) atTop (𝓝 0) := by simpa using t
    refine Tendsto.congr' ?_ t'
    filter_upwards [eventually_ge_atTop J] with j hj
    rw [hyg j hj]; ring
  have hα0 : α = 0 := by
    by_contra hne
    have := (hαQ.div_const α).congr (fun j => mul_div_cancel_left₀ _ hne)
    rw [zero_div] at this
    exact not_tendsto_nhds_of_tendsto_atTop (Q_tendsto h) 0 this
  have hyβ : ∀ j, J ≤ j → y j = β * delta P Q θ j := fun j hj => by
    rw [hyg j hj, hα0]; ring
  -- f j = γ Q_j + β P_j is integral at J, J+1, hence at 0, 1
  have hfrec : ∀ j, ((z - β * θ) * (Q (j+2) : ℝ) + β * P (j+2))
      = a (j+1) * ((z - β * θ) * (Q (j+1) : ℝ) + β * P (j+1))
        + ((z - β * θ) * (Q j : ℝ) + β * P j) := fun j => by
    rw [Qr_rec h j, Pr_rec h j]; ring
  have hfn : ∀ j, J ≤ j → (z - β * θ) * (Q j : ℝ) + β * P j = n j := fun j hj => by
    have e1 := hyβ j hj
    rw [hy j] at e1
    unfold delta at e1
    linarith
  obtain ⟨m1, m2, hm1, hm2⟩ := back_int a (fun j => (z - β * θ) * (Q j : ℝ) + β * P j) hfrec J
    (n J) (n (J+1)) (hfn J le_rfl) (hfn (J+1) (by omega))
  refine ⟨m1, m2, ?_⟩
  have hDne : (P 0 : ℝ) * Q 1 - P 1 * Q 0 ≠ 0 := by rw [← Dr_expand]; exact Dr_ne h
  rw [Dr_expand, eq_div_iff hDne]
  have e1 : (m1 : ℝ) = (z - β * θ) * (Q 0 : ℝ) + β * P 0 := hm1.symm
  have e2 : (m2 : ℝ) = (z - β * θ) * (Q 1 : ℝ) + β * P 1 := hm2.symm
  rw [e1, e2]
  unfold delta
  ring

/-- Main theorem: existence of θ, the bound, and the dichotomy (A)/(B). -/
theorem general_dichotomy (h : Data a Q P) :
    ∃ θ : ℝ, Tendsto (fun j => (P j : ℝ) / Q j) atTop (𝓝 θ) ∧
      (∀ j, 1 ≤ j → |(Q j : ℝ) * θ - P j| ≤ |((D P Q : ℤ) : ℝ)| / Q (j+1)) ∧
      (∀ z ∈ Lset P Q θ,
        Tendsto (fun j => (a j : ℝ) * dist0 ((Q j : ℝ) * z)) atTop (𝓝 0)) ∧
      (∀ z, z ∉ Lset P Q θ → ∀ c : ℝ, c < 1 →
        ¬ ∀ᶠ j in atTop, (a j : ℝ) * dist0 ((Q j : ℝ) * z) ≤ c) := by
  obtain ⟨θ, hlim, hb⟩ := T2 h
  exact ⟨θ, hlim, hb, fun z hz => T3A h θ hb z hz, fun z hz c hc => T3B h θ hb z hz c hc⟩

/-! ### Sanity instance: `a j = 4j+2`, `(Q0,Q1,P0,P1) = (1,1,1,3)` -/

def aS : ℕ → ℤ := fun j => 4 * (j : ℤ) + 2

lemma sanity_D : D (seq aS 1 3) (seq aS 1 1) = -2 := by
  norm_num [D, seq]

lemma sanity_data : Data aS (seq aS 1 1) (seq aS 1 3) where
  ha1 := fun j _ => by unfold aS; omega
  hat := by
    unfold aS
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    push_cast
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  hQ := fun j => rfl
  hP := fun j => rfl
  hQ0 := by norm_num [seq]
  hQ1 := by norm_num [seq]
  hD := by rw [sanity_D]; norm_num

theorem sanity_dichotomy :
    ∃ θ : ℝ, Tendsto (fun j => ((seq aS 1 3 j : ℤ) : ℝ) / ((seq aS 1 1 j : ℤ) : ℝ)) atTop (𝓝 θ) ∧
      (∀ z ∈ Lset (seq aS 1 3) (seq aS 1 1) θ,
        Tendsto (fun j => (aS j : ℝ) * dist0 (((seq aS 1 1 j : ℤ) : ℝ) * z)) atTop (𝓝 0)) ∧
      (∀ z, z ∉ Lset (seq aS 1 3) (seq aS 1 1) θ → ∀ c : ℝ, c < 1 →
        ¬ ∀ᶠ j in atTop, (aS j : ℝ) * dist0 (((seq aS 1 1 j : ℤ) : ℝ) * z) ≤ c) := by
  obtain ⟨θ, h1, -, h3, h4⟩ := general_dichotomy sanity_data
  exact ⟨θ, h1, h3, h4⟩

end

end GeneralDichotomy

open GeneralDichotomy in
#print axioms casoratian
open GeneralDichotomy in
#print axioms T2
open GeneralDichotomy in
#print axioms T3A
open GeneralDichotomy in
#print axioms T3B
open GeneralDichotomy in
#print axioms general_dichotomy
open GeneralDichotomy in
#print axioms sanity_D
open GeneralDichotomy in
#print axioms sanity_dichotomy
