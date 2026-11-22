import Mathlib
import EpiFormal.WindowMobiusCount

/-!
# Window widths and interval divisor counts (paper2 §7, `thm:windows`)

Paper reference: `paper2_spectral_gap_dimension` §7, theorem `thm:windows`
(parity construction, paper L2444–L2465). The coprime count of the Hermite
window rectangle is assembled from the two interval widths and from the number
of multiples of `d` in each interval. This file supplies exactly those two
ingredients, with explicit decimal constants (no `O`-notation, no asymptotics)
and under the single naked hypothesis `(10^6 : ℝ) ≤ R`:

* `W1 R` and `W2 R` — the real widths of the `m`-range `[Mlo R, Mhi R]` and the
  `n`-range `[Nlo R, Nhi R]` — satisfy `0.019 R ≤ Wᵢ R ≤ 0.021 R`;
* for `d ≥ 1`, the number of multiples of `d` in each window differs from the
  continuous count `Wᵢ R / d` by at most `1`, on both sides
  (`Acount_lo`/`Acount_hi` for the `m`-window, `Bcount_lo`/`Bcount_hi` for the
  `n`-window).

All six floor-based definitions (`Mlo`, `Mhi`, `Nlo`, `Nhi`, `W1`, `W2`) and the
interval count `intervalCount` come from `EpiFormal.WindowMobiusCount`.
-/

open ArithmeticFunction Finset Real
open scoped BigOperators

namespace WindowMobiusCount

/-! ## 1. Width bounds for the `m`-window. -/

theorem W1_lo (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) : 0.019 * R ≤ W1 R := by
  have e1 : ((⌊0.36 * R⌋₊ : ℕ) : ℝ) ≤ 0.36 * R := Nat.floor_le (by nlinarith)
  have e2 : 0.36 * R < ((⌊0.36 * R⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have e3 : ((⌊0.34 * R⌋₊ : ℕ) : ℝ) ≤ 0.34 * R := Nat.floor_le (by nlinarith)
  unfold W1 Mhi Mlo
  push_cast
  nlinarith [e1, e2, e3, hR]

theorem W1_hi (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) : W1 R ≤ 0.021 * R := by
  have e1 : ((⌊0.36 * R⌋₊ : ℕ) : ℝ) ≤ 0.36 * R := Nat.floor_le (by nlinarith)
  have e3 : 0.34 * R < ((⌊0.34 * R⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  unfold W1 Mhi Mlo
  push_cast
  nlinarith [e1, e3, hR]

/-! ## 2. Width bounds for the `n`-window. -/

theorem W2_lo (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) : 0.019 * R ≤ W2 R := by
  have e1 : ((⌊0.22 * R⌋₊ : ℕ) : ℝ) ≤ 0.22 * R := Nat.floor_le (by nlinarith)
  have e2 : 0.22 * R < ((⌊0.22 * R⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have e3 : ((⌊0.20 * R⌋₊ : ℕ) : ℝ) ≤ 0.20 * R := Nat.floor_le (by nlinarith)
  unfold W2 Nhi Nlo
  push_cast
  nlinarith [e1, e2, e3, hR]

theorem W2_hi (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) : W2 R ≤ 0.021 * R := by
  have e1 : ((⌊0.22 * R⌋₊ : ℕ) : ℝ) ≤ 0.22 * R := Nat.floor_le (by nlinarith)
  have e3 : 0.20 * R < ((⌊0.20 * R⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  unfold W2 Nhi Nlo
  push_cast
  nlinarith [e1, e3, hR]

/-! ## 3. Multiples of `d` in the `m`-window. -/

/-- `W1 R = ↑(Mhi R) - ↑(Mlo R - 1)`, the natural-number form of the width. -/
theorem W1_eq_cast (R : ℝ) :
    W1 R = (Mhi R : ℝ) - ((Mlo R - 1 : ℕ) : ℝ) := by
  have h : ((Mlo R - 1 : ℕ) : ℝ) = (Mlo R : ℝ) - 1 := by
    simpa using Nat.cast_sub (Mlo_ge_one R) (m := 1)
  unfold W1
  rw [h]
  ring

/-- Lower bound: the `m`-window multiple count is at most `1` below `W1 R / d`. -/
theorem Acount_lo (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) (d : ℕ) (hd : 1 ≤ d) :
    W1 R / (d : ℝ) - 1 ≤ (Acount R d : ℝ) := by
  obtain ⟨hMle, -⟩ := box_nonempty R (by linarith : (100 : ℝ) ≤ R)
  have hd0 : 0 < d := by omega
  have hdle : (Mlo R - 1) / d ≤ Mhi R / d := nat_div_mono (by omega)
  have hAcard : Acount R d = Mhi R / d - (Mlo R - 1) / d := by
    unfold Acount
    exact intervalCount (Mlo R) (Mhi R) d hd (Mlo_ge_one R)
  have hAc : (Acount R d : ℝ) =
      ((Mhi R / d : ℕ) : ℝ) - (((Mlo R - 1) / d : ℕ) : ℝ) := by
    rw [hAcard]
    exact Nat.cast_sub hdle
  have low1 : (Mhi R : ℝ) / (d : ℝ) - 1 ≤ ((Mhi R / d : ℕ) : ℝ) :=
    nat_div_cast_lower _ _ hd0
  have up2 : (((Mlo R - 1) / d : ℕ) : ℝ) ≤ ((Mlo R - 1 : ℕ) : ℝ) / (d : ℝ) :=
    nat_div_cast_upper _ _ hd0
  have heq : W1 R / (d : ℝ) - 1 =
      (Mhi R : ℝ) / (d : ℝ) - ((Mlo R - 1 : ℕ) : ℝ) / (d : ℝ) - 1 := by
    rw [W1_eq_cast R, sub_div]
  rw [hAc, heq]
  linarith

/-- Upper bound: the `m`-window multiple count is at most `1` above `W1 R / d`. -/
theorem Acount_hi (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) (d : ℕ) (hd : 1 ≤ d) :
    (Acount R d : ℝ) ≤ W1 R / (d : ℝ) + 1 := by
  obtain ⟨hMle, -⟩ := box_nonempty R (by linarith : (100 : ℝ) ≤ R)
  have hd0 : 0 < d := by omega
  have hdle : (Mlo R - 1) / d ≤ Mhi R / d := nat_div_mono (by omega)
  have hAcard : Acount R d = Mhi R / d - (Mlo R - 1) / d := by
    unfold Acount
    exact intervalCount (Mlo R) (Mhi R) d hd (Mlo_ge_one R)
  have hAc : (Acount R d : ℝ) =
      ((Mhi R / d : ℕ) : ℝ) - (((Mlo R - 1) / d : ℕ) : ℝ) := by
    rw [hAcard]
    exact Nat.cast_sub hdle
  have up1 : ((Mhi R / d : ℕ) : ℝ) ≤ (Mhi R : ℝ) / (d : ℝ) :=
    nat_div_cast_upper _ _ hd0
  have low2 : ((Mlo R - 1 : ℕ) : ℝ) / (d : ℝ) - 1 ≤
      (((Mlo R - 1) / d : ℕ) : ℝ) := nat_div_cast_lower _ _ hd0
  have heq : W1 R / (d : ℝ) + 1 =
      (Mhi R : ℝ) / (d : ℝ) - ((Mlo R - 1 : ℕ) : ℝ) / (d : ℝ) + 1 := by
    rw [W1_eq_cast R, sub_div]
  rw [hAc, heq]
  linarith

/-! ## 4. Multiples of `d` in the `n`-window. -/

/-- `W2 R = ↑(Nhi R) - ↑(Nlo R - 1)`, the natural-number form of the width. -/
theorem W2_eq_cast (R : ℝ) :
    W2 R = (Nhi R : ℝ) - ((Nlo R - 1 : ℕ) : ℝ) := by
  have h : ((Nlo R - 1 : ℕ) : ℝ) = (Nlo R : ℝ) - 1 := by
    simpa using Nat.cast_sub (Nlo_ge_one R) (m := 1)
  unfold W2
  rw [h]
  ring

/-- Lower bound: the `n`-window multiple count is at most `1` below `W2 R / d`. -/
theorem Bcount_lo (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) (d : ℕ) (hd : 1 ≤ d) :
    W2 R / (d : ℝ) - 1 ≤ (Bcount R d : ℝ) := by
  obtain ⟨-, hNle⟩ := box_nonempty R (by linarith : (100 : ℝ) ≤ R)
  have hd0 : 0 < d := by omega
  have hdle : (Nlo R - 1) / d ≤ Nhi R / d := nat_div_mono (by omega)
  have hBcard : Bcount R d = Nhi R / d - (Nlo R - 1) / d := by
    unfold Bcount
    exact intervalCount (Nlo R) (Nhi R) d hd (Nlo_ge_one R)
  have hBc : (Bcount R d : ℝ) =
      ((Nhi R / d : ℕ) : ℝ) - (((Nlo R - 1) / d : ℕ) : ℝ) := by
    rw [hBcard]
    exact Nat.cast_sub hdle
  have low1 : (Nhi R : ℝ) / (d : ℝ) - 1 ≤ ((Nhi R / d : ℕ) : ℝ) :=
    nat_div_cast_lower _ _ hd0
  have up2 : (((Nlo R - 1) / d : ℕ) : ℝ) ≤ ((Nlo R - 1 : ℕ) : ℝ) / (d : ℝ) :=
    nat_div_cast_upper _ _ hd0
  have heq : W2 R / (d : ℝ) - 1 =
      (Nhi R : ℝ) / (d : ℝ) - ((Nlo R - 1 : ℕ) : ℝ) / (d : ℝ) - 1 := by
    rw [W2_eq_cast R, sub_div]
  rw [hBc, heq]
  linarith

/-- Upper bound: the `n`-window multiple count is at most `1` above `W2 R / d`. -/
theorem Bcount_hi (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) (d : ℕ) (hd : 1 ≤ d) :
    (Bcount R d : ℝ) ≤ W2 R / (d : ℝ) + 1 := by
  obtain ⟨-, hNle⟩ := box_nonempty R (by linarith : (100 : ℝ) ≤ R)
  have hd0 : 0 < d := by omega
  have hdle : (Nlo R - 1) / d ≤ Nhi R / d := nat_div_mono (by omega)
  have hBcard : Bcount R d = Nhi R / d - (Nlo R - 1) / d := by
    unfold Bcount
    exact intervalCount (Nlo R) (Nhi R) d hd (Nlo_ge_one R)
  have hBc : (Bcount R d : ℝ) =
      ((Nhi R / d : ℕ) : ℝ) - (((Nlo R - 1) / d : ℕ) : ℝ) := by
    rw [hBcard]
    exact Nat.cast_sub hdle
  have up1 : ((Nhi R / d : ℕ) : ℝ) ≤ (Nhi R : ℝ) / (d : ℝ) :=
    nat_div_cast_upper _ _ hd0
  have low2 : ((Nlo R - 1 : ℕ) : ℝ) / (d : ℝ) - 1 ≤
      (((Nlo R - 1) / d : ℕ) : ℝ) := nat_div_cast_lower _ _ hd0
  have heq : W2 R / (d : ℝ) + 1 =
      (Nhi R : ℝ) / (d : ℝ) - ((Nlo R - 1 : ℕ) : ℝ) / (d : ℝ) + 1 := by
    rw [W2_eq_cast R, sub_div]
  rw [hBc, heq]
  linarith

/-! ## 5. Axiom audit. -/

#print axioms W1_lo
#print axioms W1_hi
#print axioms W2_lo
#print axioms W2_hi
#print axioms Acount_lo
#print axioms Acount_hi
#print axioms Bcount_lo
#print axioms Bcount_hi

end WindowMobiusCount
