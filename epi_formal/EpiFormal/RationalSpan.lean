import EpiFormal.EscapeReduction

/-!
# THM-0001: rational span reformulation of P1 (equivalent rewriting, not progress on P1)

* `mem_latticeL_iff_rat`: `⋃_{B ≥ 1} B⁻¹ L = ℚ + ℚ e`.
* `P1_iff_not_mem_span`: `P1 ↔ π ∉ ℚ + ℚ e`.
* `P1_iff_linearIndependent`: with `e` irrational as hypothesis,
  `P1 ↔ 1, e, π` linearly independent over ℚ.
-/

open Classification

namespace RationalSpan

lemma rat_mul_den (r : ℚ) : (r.den : ℝ) * (r : ℝ) = (r.num : ℝ) := by
  have h : r * (r.den : ℚ) = (r.num : ℚ) := Rat.mul_den_eq_num r
  have h2 : ((r * (r.den : ℚ) : ℚ) : ℝ) = (((r.num : ℚ)) : ℝ) := by rw [h]
  push_cast at h2
  linarith

end RationalSpan

theorem mem_latticeL_iff_rat (z : ℝ) :
    (∃ B : ℕ, 1 ≤ B ∧ (B : ℝ) * z ∈ Classification.latticeL) ↔
      ∃ r s : ℚ, z = r + s * Real.exp 1 := by
  constructor
  · rintro ⟨B, hB, m, n, h⟩
    have hB' : (B : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ B := by exact_mod_cast hB
      linarith
    refine ⟨((m : ℚ) + (n : ℚ) / 2) / B, (n : ℚ) / (2 * B), ?_⟩
    push_cast
    field_simp
    linarith
  · rintro ⟨r, s, rfl⟩
    have hr := RationalSpan.rat_mul_den r
    have hs := RationalSpan.rat_mul_den s
    refine ⟨r.den * s.den, Nat.mul_pos r.den_pos s.den_pos, r.num * s.den - s.num * r.den,
      2 * (s.num * r.den), ?_⟩
    push_cast
    have e1 : ((r.den : ℝ) * (s.den : ℝ)) * (r : ℝ) = (r.num : ℝ) * (s.den : ℝ) := by
      rw [← hr]; ring
    have e2 : ((r.den : ℝ) * (s.den : ℝ)) * (s : ℝ) = (s.num : ℝ) * (r.den : ℝ) := by
      rw [← hs]; ring
    calc ((r.den : ℝ) * (s.den : ℝ)) * ((r : ℝ) + (s : ℝ) * Real.exp 1)
        = ((r.den : ℝ) * (s.den : ℝ)) * (r : ℝ)
          + ((r.den : ℝ) * (s.den : ℝ)) * (s : ℝ) * Real.exp 1 := by ring
      _ = _ := by rw [e1, e2]; ring

theorem P1_iff_not_mem_span :
    EscapeReduction.P1 ↔ ¬ ∃ r s : ℚ, Real.pi = r + s * Real.exp 1 := by
  rw [← mem_latticeL_iff_rat]
  unfold EscapeReduction.P1
  push_neg
  rfl

theorem P1_iff_linearIndependent_of_irrational (he : Irrational (Real.exp 1)) :
    EscapeReduction.P1 ↔ LinearIndependent ℚ ![(1 : ℝ), Real.exp 1, Real.pi] := by
  rw [P1_iff_not_mem_span, Fintype.linearIndependent_iff]
  constructor
  · intro hP g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Rat.smul_def] at hg
    by_cases h2 : g 2 = 0
    · by_cases h1 : g 1 = 0
      · have h0 : g 0 = 0 := by
          rw [h2, h1] at hg
          simpa using hg
        intro i; fin_cases i <;> simp [h0, h1, h2]
      · exfalso
        apply he
        refine ⟨-(g 0) / g 1, ?_⟩
        rw [h2] at hg
        simp only [Rat.cast_zero, zero_mul, add_zero, mul_one] at hg
        have h1' : (g 1 : ℝ) ≠ 0 := by exact_mod_cast h1
        push_cast
        field_simp
        linarith
    · exfalso
      apply hP
      have h2' : (g 2 : ℝ) ≠ 0 := by exact_mod_cast h2
      refine ⟨-(g 0) / g 2, -(g 1) / g 2, ?_⟩
      push_cast
      field_simp
      linarith
  · rintro hL ⟨r, s, h⟩
    have := hL ![-r, -s, 1] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Rat.smul_def]
      push_cast
      linarith) 2
    simp at this

/-- Part (b), stated with the project's `e_irrational` (which depends on the project axiom
`e_transcendental`); see audit. -/
theorem P1_iff_linearIndependent :
    EscapeReduction.P1 ↔ LinearIndependent ℚ ![(1 : ℝ), Real.exp 1, Real.pi] :=
  P1_iff_linearIndependent_of_irrational e_irrational
