import Mathlib
import EpiFormal.Classification

/-! Residue periods for two consecutive Hermite pairs. The base cases are
finite calculations in the kernel. The periodicity step holds for every index. -/

namespace HermiteResiduePeriod

def step {m : ℕ} (j : ℕ) (s : (ZMod m × ZMod m) × (ZMod m × ZMod m)) :
    (ZMod m × ZMod m) × (ZMod m × ZMod m) :=
  (s.2, (s.1.1 + (4 * (j : ZMod m) + 6) * s.2.1,
         s.1.2 + (4 * (j : ZMod m) + 6) * s.2.2))

def state (m : ℕ) : ℕ → (ZMod m × ZMod m) × (ZMod m × ZMod m)
  | 0 => ((1, 1), (3, 1))
  | j + 1 => step j (state m j)

theorem state_eq_selected (m : ℕ) (j : ℕ) :
    state m j = (((Psel j : ZMod m), (Qsel j : ZMod m)),
      ((Psel (j+1) : ZMod m), (Qsel (j+1) : ZMod m))) := by
  induction j with
  | zero => simp [state]
  | succ j ih =>
    rw [state, ih]
    simp only [step, Classification.Psel_rec j, Classification.Qsel_rec j, Int.cast_add,
      Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> exact add_comm _ _

theorem period_of_return (m : ℕ) (h : state m m = state m 0) :
    ∀ j, state m (j + m) = state m j := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [show j + 1 + m = (j + m) + 1 by omega, state, state, ih]
    have hc : ((j + m : ℕ) : ZMod m) = j := by
      rw [Nat.cast_add, ZMod.natCast_self, add_zero]
    simp [step, hc]

theorem state_period_3 : ∀ j, state 18 (j + 18) = state 18 j :=
  period_of_return 18 (by decide)

theorem state_period_4 : ∀ j, state 32 (j + 32) = state 32 j :=
  period_of_return 32 (by decide)

theorem state_period_5 : ∀ j, state 50 (j + 50) = state 50 j :=
  period_of_return 50 (by decide)

theorem state_period_6 : ∀ j, state 72 (j + 72) = state 72 j :=
  period_of_return 72 (by decide)

/-- The residue periodicity of the actual selected numerators and denominators
follows from the checked recurrence and the two-vector return. -/
theorem selected_period (m : ℕ) (h : state m m = state m 0) (j : ℕ) :
    (Psel (j+m) : ZMod m) = (Psel j : ZMod m) ∧
      (Qsel (j+m) : ZMod m) = (Qsel j : ZMod m) := by
  have hs := period_of_return m h j
  rw [state_eq_selected, state_eq_selected] at hs
  exact ⟨congrArg (fun s => s.1.1) hs, congrArg (fun s => s.1.2) hs⟩

end HermiteResiduePeriod



