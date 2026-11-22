import EpiFormal.EulerConvergents
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

namespace AffineWindowAudit

/-- Four Hermite recurrence steps cannot connect six residues with alternating zeros
in a field of characteristic other than two. -/
theorem no_five_alternations {K : Type*} [Field K] (h8 : (8 : K) ≠ 0)
    (x : ℕ → K) (a : K)
    (hrec : ∀ i : ℕ, i < 4 → x (i + 2) = (a + 4 * (i : K)) * x (i + 1) + x i)
    (hflip : ∀ i : ℕ, i < 5 → (x i = 0 ↔ x (i + 1) ≠ 0)) : False := by
  have coeff_zero (i : ℕ) (hi : i < 4) (hL : x i = 0)
      (hM : x (i + 1) ≠ 0) (hR : x (i + 2) = 0) :
      a + 4 * (i : K) = 0 := by
    have h := hrec i hi
    rw [hL, hR, add_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hM
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := (hflip 0 (by decide)).mp h0
    have h2 : x 2 = 0 := by
      by_contra hn
      exact h1 ((hflip 1 (by decide)).mpr hn)
    have h3 : x 3 ≠ 0 := (hflip 2 (by decide)).mp h2
    have h4 : x 4 = 0 := by
      by_contra hn
      exact h3 ((hflip 3 (by decide)).mpr hn)
    have hA := coeff_zero 0 (by decide) h0 h1 h2
    have hB := coeff_zero 2 (by decide) h2 h3 h4
    apply h8
    calc
      (8 : K) = (a + 4 * (2 : ℕ)) - (a + 4 * (0 : ℕ)) := by norm_num
      _ = 0 := by rw [hA, hB, sub_self]
  · have h1 : x 1 = 0 := by
      by_contra hn
      exact h0 ((hflip 0 (by decide)).mpr hn)
    have h2 : x 2 ≠ 0 := (hflip 1 (by decide)).mp h1
    have h3 : x 3 = 0 := by
      by_contra hn
      exact h2 ((hflip 2 (by decide)).mpr hn)
    have h4 : x 4 ≠ 0 := (hflip 3 (by decide)).mp h3
    have h5 : x 5 = 0 := by
      by_contra hn
      exact h4 ((hflip 4 (by decide)).mpr hn)
    have hA := coeff_zero 1 (by decide) h1 h2 h3
    have hB := coeff_zero 3 (by decide) h3 h4 h5
    apply h8
    calc
      (8 : K) = (a + 4 * (3 : ℕ)) - (a + 4 * (1 : ℕ)) := by norm_num
      _ = 0 := by rw [hA, hB, sub_self]

private theorem modEight_kernel : ∀ a b : ZMod 8,
    (4 * a + 2) * (4 * b + 2) = 4 := by decide

/-- In a Hermite recurrence step, two residues zero modulo eight
cannot enclose a middle term congruent to two modulo four. -/
theorem no_modEight_middle (j u v w : ZMod 8)
    (hrec : w = (4 * j + 2) * v + u)
    (hU : u = 0) (hW : w = 0) (hV : ∃ k : ZMod 8, v = 4 * k + 2) : False := by
  obtain ⟨k, hk⟩ := hV
  rw [hU, hW, hk, modEight_kernel, add_zero] at hrec
  exact (by decide : (0 : ZMod 8) ≠ 4) hrec

/-- Integer divisibility form of the odd-prime obstruction. -/
theorem prime_no_five_divisibility (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (u : ℕ → ℤ) (a : ℤ)
    (hrec : ∀ i : ℕ, i < 4 → u (i + 2) = (a + 4 * (i : ℤ)) * u (i + 1) + u i)
    (hflip : ∀ i : ℕ, i < 5 → ((p : ℤ) ∣ u i ↔ ¬ (p : ℤ) ∣ u (i + 1))) :
    False := by
  letI : Fact p.Prime := ⟨hp⟩
  have h8 : (8 : ZMod p) ≠ 0 := by
    intro h
    have hz : ((8 : ℤ) : ZMod p) = 0 := by simpa using h
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd 8 p).mp hz
    have hn : p ∣ 2 * (2 * 2) := by exact_mod_cast hd
    have htwo : p ∣ 2 := by
      rcases hp.dvd_mul.mp hn with h | h
      · exact h
      · rcases hp.dvd_mul.mp h with h | h <;> exact h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) htwo
    have hge := hp.two_le
    exact hodd (by omega)
  refine no_five_alternations h8 (fun i => (u i : ZMod p)) (a : ZMod p) ?_ ?_
  · intro i hi
    have h := congrArg (fun z : ℤ => (z : ZMod p)) (hrec i hi)
    push_cast at h
    exact h
  · intro i hi
    change (↑(u i) : ZMod p) = 0 ↔ (↑(u (i + 1)) : ZMod p) ≠ 0
    simp only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hflip i hi

/-- The integer form of the obstruction modulo eight. -/
theorem eight_not_dvd_middle (i u : ℤ) (hu : u % 4 = 2) :
    ¬ (8 : ℤ) ∣ (4 * i + 2) * u := by
  intro hd
  have hc : u = 4 * (u / 4) + 2 := by omega
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ((4 * i + 2) * u) 8).mpr hd
  rw [hc] at hz
  push_cast at hz
  rw [modEight_kernel] at hz
  exact (by decide : (4 : ZMod 8) ≠ 0) hz

def selectedNumerator (A C : ℤ) (j : ℕ) : ℤ :=
  A * Qsel j + C * Psel j

/-- The unnormalised numerator at a cutoff inherits the Hermite recurrence. -/
theorem selectedNumerator_step (A C : ℤ) (j : ℕ) (hj : 1 ≤ j) :
    selectedNumerator A C (j + 2) =
      (4 * (j : ℤ) + 6) * selectedNumerator A C (j + 1) + selectedNumerator A C j := by
  have hp := Psel_rec (j + 1) (by omega)
  have hq := Qsel_rec1 (j + 1) (by omega)
  rw [Nat.add_sub_cancel] at hp hq
  unfold selectedNumerator
  rw [hq, hp]
  push_cast
  ring

/-- An odd prime cannot alternate in and out of the selected affine
numerator at all five adjacent pairs. Taking A = 1 and C = 0 gives Qsel. -/
theorem selectedNumerator_no_five (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (A C : ℤ) (j : ℕ) (hj : 1 ≤ j)
    (hflip : ∀ i : ℕ, i < 5 →
      ((p : ℤ) ∣ selectedNumerator A C (j + i) ↔
       ¬ (p : ℤ) ∣ selectedNumerator A C (j + (i + 1)))) : False := by
  refine prime_no_five_divisibility p hp hodd
    (fun i => selectedNumerator A C (j + i)) (4 * (j : ℤ) + 6) ?_ hflip
  intro i _
  have step := selectedNumerator_step A C (j + i) (by omega)
  push_cast at step
  rw [← Nat.add_assoc j i 2, ← Nat.add_assoc j i 1, step]
  ring

/-- The selected affine numerator cannot have a residue two modulo four
between two multiples of eight. -/
theorem selectedNumerator_no_eight_middle (A C : ℤ) (j : ℕ) (hj : 1 ≤ j)
    (hleft : (8 : ℤ) ∣ selectedNumerator A C j)
    (hmid : selectedNumerator A C (j + 1) % 4 = 2)
    (hright : (8 : ℤ) ∣ selectedNumerator A C (j + 2)) : False := by
  have h := dvd_sub hright hleft
  rw [selectedNumerator_step A C j hj, add_sub_cancel_right] at h
  apply eight_not_dvd_middle ((j : ℤ) + 1) _ hmid
  convert h using 1 <;> ring

def sixthModelContent (j : ℕ) : ℕ :=
  Int.gcd (selectedNumerator 1 1 j) (6 * Qsel j)

/-- The example (1+e)/6 realises four adjacent content products equal to 12.
The index shift to the locked range uses the paper's period theorem. -/
theorem sixthModel_four_products :
    ∀ k : Fin 4, sixthModelContent (k.val + 2) * sixthModelContent (k.val + 3) = 12 := by
  decide

#print axioms no_five_alternations
#print axioms no_modEight_middle
#print axioms prime_no_five_divisibility
#print axioms eight_not_dvd_middle
#print axioms selectedNumerator_step
#print axioms selectedNumerator_no_five
#print axioms selectedNumerator_no_eight_middle
#print axioms sixthModel_four_products

end AffineWindowAudit