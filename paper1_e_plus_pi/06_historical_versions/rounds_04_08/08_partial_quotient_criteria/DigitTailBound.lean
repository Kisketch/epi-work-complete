import Mathlib.Data.Nat.Fib.Basic

namespace DigitTailBound

/-- For a nonempty list the two coordinates are the continuants of the list
and of its tail. The empty list gives the initial column of the recurrence. -/
def continuantPair : List ℕ → ℕ × ℕ
  | [] => (1, 0)
  | a :: s =>
    let v := continuantPair s
    (a * v.1 + v.2, v.1)

def continuant (s : List ℕ) : ℕ := (continuantPair s).1

private theorem pair_fib_lower (s : List ℕ) (hs : ∀ a ∈ s, 0 < a) :
    Nat.fib (s.length + 1) ≤ (continuantPair s).1 ∧
    Nat.fib s.length ≤ (continuantPair s).2 := by
  induction s with
  | nil => decide
  | cons a s ih =>
    have ha : 1 ≤ a := hs a (by simp)
    obtain ⟨h₁, h₂⟩ := ih (fun d hd => hs d (List.mem_cons_of_mem a hd))
    have hm : (continuantPair s).1 ≤ a * (continuantPair s).1 := by
      simpa using Nat.mul_le_mul_right (continuantPair s).1 ha
    change Nat.fib (s.length + 2) ≤ a * (continuantPair s).1 + (continuantPair s).2 ∧
      Nat.fib (s.length + 1) ≤ (continuantPair s).1
    rw [Nat.fib_add_two]
    exact ⟨by omega, h₁⟩

/-- Among positive words of length m, every continuant is at least F_(m+1). -/
theorem fib_length_le_continuant (s : List ℕ) (hs : ∀ a ∈ s, 0 < a) :
    Nat.fib (s.length + 1) ≤ continuant s :=
  (pair_fib_lower s hs).1

/-- Every digit of a positive word is bounded by its continuant. -/
theorem digit_le_continuant (s : List ℕ) (hs : ∀ a ∈ s, 0 < a)
    (d : ℕ) (hd : d ∈ s) : d ≤ continuant s := by
  induction s with
  | nil => simp at hd
  | cons a s ih =>
    have ha : 1 ≤ a := hs a (by simp)
    have htail : ∀ b ∈ s, 0 < b := fun b hb => hs b (List.mem_cons_of_mem a hb)
    have hpos : 1 ≤ (continuantPair s).1 :=
      le_trans (Nat.fib_pos.mpr (Nat.zero_lt_succ _)) (pair_fib_lower s htail).1
    change d ≤ a * (continuantPair s).1 + (continuantPair s).2
    rcases List.mem_cons.mp hd with hhead | hd
    · have hle : a ≤ a * (continuantPair s).1 := by
        simpa using Nat.mul_le_mul_left a hpos
      omega
    · have hle : (continuantPair s).1 ≤ a * (continuantPair s).1 := by
        simpa using Nat.mul_le_mul_right (continuantPair s).1 ha
      have hds : d ≤ (continuantPair s).1 := ih htail hd
      omega

#print axioms fib_length_le_continuant
#print axioms digit_le_continuant

end DigitTailBound
