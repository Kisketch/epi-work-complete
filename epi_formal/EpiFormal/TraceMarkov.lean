import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace TraceMarkov

/-- When the middle coefficient is divisible by a prime, the two outside
coefficients cannot both contain that prime in a primitive triple. -/
theorem primitiveFactor {p a b c : ℕ} (hp : Nat.Prime p)
    (hprim : Nat.gcd (Nat.gcd a b) c = 1) (hb : p ∣ b) :
    ¬ (p ∣ a ∧ p ∣ c) := by
  rintro ⟨ha, hc⟩
  have h : p ∣ Nat.gcd (Nat.gcd a b) c := Nat.dvd_gcd (Nat.dvd_gcd ha hb) hc
  rw [hprim] at h
  exact hp.ne_one (Nat.dvd_one.mp h)

/-- Congruences and discriminant for the explicit shared progression. -/
theorem discriminantSixtyProgression (t : ℤ) :
    let m := 420 * t + 16
    let u := 210 * t + 8
    m % 14 = 2 ∧ m % 4 = 0 ∧ m % 3 = 1 ∧ m % 5 = 1 ∧
      u % 2 = 0 ∧ m ^ 2 - 4 * (u ^ 2 - 15) = 60 := by
  dsimp
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  ring

def potentialSum {V : Type} (F : V → ℝ) (v : V) : List V → ℝ
  | [] => 0
  | u :: tail => F u - F v + potentialSum F u tail

def finalVertex {V : Type} (v : V) : List V → V
  | [] => v
  | u :: tail => finalVertex u tail

/-- A potential contributes only its boundary values along a path. -/
theorem potentialSum_eq {V : Type} (F : V → ℝ) (v : V) (tail : List V) :
    potentialSum F v tail = F (finalVertex v tail) - F v := by
  induction tail generalizing v with
  | nil => simp [potentialSum, finalVertex]
  | cons u tail ih =>
    simp only [potentialSum, finalVertex, ih]
    ring

/-- Centered reward variance of return excursions of lengths one and two. -/
theorem twoReturnVariance (q p : ℝ) (h : p * (1 + q) = q) :
    ((1 - q) * p ^ 2 + q * (1 - 2 * p) ^ 2) * (1 + q) ^ 2 = q * (1 - q) := by
  have h0 : p * (1 + q) = q := h
  have h1 : (1 - 2 * p) * (1 + q) = 1 - q := by
    calc
      (1 - 2 * p) * (1 + q) = 1 + q - 2 * (p * (1 + q)) := by ring
      _ = 1 - q := by rw [h]; ring
  calc
    ((1 - q) * p ^ 2 + q * (1 - 2 * p) ^ 2) * (1 + q) ^ 2 =
        (1 - q) * (p * (1 + q)) ^ 2 + q * ((1 - 2 * p) * (1 + q)) ^ 2 := by ring
    _ = q * (1 - q) := by rw [h0, h1]; ring

end TraceMarkov

#print axioms TraceMarkov.primitiveFactor
#print axioms TraceMarkov.discriminantSixtyProgression
#print axioms TraceMarkov.potentialSum_eq
#print axioms TraceMarkov.twoReturnVariance
