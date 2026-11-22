import Mathlib
import EpiFormal.DirichletDivisor
import EpiFormal.HermiteResiduePeriod

/-!
# Affine window assembly, phase 1 (paper1 §3, thm:explicit-period + thm:affine-window).

Machine-checked assembly of the paper's algebra. Deep inputs enter as
explicit interface hypotheses: locked denominators, content divisibility,
the Hermite recurrence, the mod-`T` congruence, and the digit-determination
rule. House style in this project is fully explicit binders (no `variable`).

What IS verified here: content arithmetic, evenness of `D j`, `r` odd and
`r ≥ 3`, period transfer from `G`-periodicity, and the first-digit increment
algebra `4T·Gj/(Gj1·Dj) = 4Gj²`.
-/

namespace AffineWindow

/-- `T = 2Bc` is positive. -/
theorem T_pos (B c : ℕ) (hB : 0 < B) (hc : 0 < c) : 0 < 2 * B * c :=
  Nat.mul_pos (Nat.mul_pos (by norm_num) hB) hc

/-- `D j` is positive (exact division of a positive `T`). -/
theorem D_pos (B c : ℕ) (hB : 0 < B) (hc : 0 < c)
    (D G : ℕ → ℕ)
    (hDT : ∀ j, D j * (G j * G (j + 1)) = 2 * B * c) (j : ℕ) :
    0 < D j := by
  rcases Nat.eq_zero_or_pos (D j) with h | h
  · exfalso
    have h0 : 2 * B * c = 0 := by rw [← hDT j, h, zero_mul]
    have hT := T_pos B c hB hc
    omega
  · exact h

/-- `D j` is even: `T` is even, the content product is odd. -/
theorem D_even (B c : ℕ) (G D : ℕ → ℕ)
    (hGodd : ∀ j, Odd (G j))
    (hDT : ∀ j, D j * (G j * G (j + 1)) = 2 * B * c) (j : ℕ) :
    Even (D j) := by
  have hP : Odd (G j * G (j + 1)) := (hGodd j).mul (hGodd (j + 1))
  rcases Nat.even_or_odd (D j) with h | h
  · exact h
  · exfalso
    have hprod := h.mul hP
    rw [hDT j] at hprod
    have hT : Even (2 * B * c) := ⟨B * c, by ring⟩
    obtain ⟨a, ha⟩ := hT
    obtain ⟨b, hb⟩ := hprod
    omega

/-- An odd window length different from 1 is at least 3. -/
theorem r_ge_three (r : ℕ → ℕ) (j : ℕ) (hodd : Odd (r j))
    (hne : r j ≠ 1) : 3 ≤ r j := by
  obtain ⟨k, hk⟩ := hodd
  omega

/-- `D` repeats wherever `G` repeats (exact-division cancellation). -/
theorem D_period (B c : ℕ) (G D : ℕ → ℕ) (j T' : ℕ)
    (hP : G (j + T') * G ((j + T') + 1) = G j * G (j + 1))
    (hT1 : D (j + T') * (G j * G (j + 1)) = 2 * B * c)
    (hT2 : D j * (G j * G (j + 1)) = 2 * B * c)
    (hPpos : 0 < G j * G (j + 1)) :
    D (j + T') = D j := by
  apply mul_right_cancel₀ (ne_of_gt hPpos)
  rw [hT1, hT2]

/-- `r` repeats wherever `D` repeats and the recovered residues agree. -/
theorem r_period (r D : ℕ → ℕ) (F : ℕ → ℕ → ℕ) (C : ℕ → ℕ)
    (hDet : ∀ j, r j = F (D j) (C j % D j))
    (j T' : ℕ)
    (hD : D (j + T') = D j)
    (hCm : C (j + T') % D (j + T') = C j % D j) :
    r (j + T') = r j := by
  rw [hDet (j + T'), hDet j, hCm, hD]

/-- First-digit increment algebra: `4T·Gj/(Gj1·Dj) = 4Gj²` given `Dj·(Gj·Gj1) = T`. -/
theorem first_digit_shift (Tq Gj Gj1 Dj : ℚ)
    (hDTq : Dj * (Gj * Gj1) = Tq) (hGj1 : Gj1 ≠ 0) (hDj0 : Dj ≠ 0) :
    4 * Tq * Gj / (Gj1 * Dj) = 4 * Gj ^ 2 := by
  have hprod : Gj1 * Dj ≠ 0 := mul_ne_zero hGj1 hDj0
  have h1 : (4 : ℚ) * Tq * Gj / (Gj1 * Dj)
      = 4 * (Dj * (Gj * Gj1)) * Gj / (Gj1 * Dj) := by rw [hDTq]
  rw [h1]
  field_simp

end AffineWindow

#print axioms AffineWindow.T_pos
#print axioms AffineWindow.D_pos
#print axioms AffineWindow.D_even
#print axioms AffineWindow.r_ge_three
#print axioms AffineWindow.D_period
#print axioms AffineWindow.r_period
#print axioms AffineWindow.first_digit_shift
