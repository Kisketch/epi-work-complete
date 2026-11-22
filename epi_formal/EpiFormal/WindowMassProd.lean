import Mathlib

/-!
# Mass product bounds (multi-level splitting, paper §7 L2536–2543 S1)

Pure arithmetic core of LEM-prod-mu-bound (threshold blueprint S1):
unrolling `m (j+1) = m j / B j` gives `m j ≤ m j0 / ∏ B`,
and with per-level branching `B i ≥ c * i ^ b` the product is bounded below
by `c ^ (j - j0) * R ^ b` with `R = (j-1)! / (j0-1)!`.

All bounds use `ℕ` exponents (`b ∈ {1, 2}` per blueprint); log/exp conversion
is left to the threshold file. No project axioms beyond Lean core are used.
-/

namespace WindowMassProd

open Finset

/-- Unrolling a splitting recurrence into a product lower bound. -/
theorem mass_le_prod (m B : ℕ → ℝ) (j0 : ℕ)
    (hB : ∀ i, 0 < B i)
    (hmrec : ∀ j ≥ j0, m (j + 1) = m j / B j) :
    ∀ j ≥ j0, m j ≤ m j0 / ∏ i ∈ Finset.Ico j0 j, B i := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    have hBj : 0 < B j := hB j
    calc m (j + 1) = m j / B j := hmrec j hj
      _ ≤ (m j0 / ∏ i ∈ Finset.Ico j0 j, B i) / B j :=
        div_le_div_of_nonneg_right ih (le_of_lt hBj)
      _ = m j0 / ((∏ i ∈ Finset.Ico j0 j, B i) * B j) := by rw [div_div]
      _ = m j0 / ∏ i ∈ Finset.Ico j0 (j + 1), B i := by
        rw [Finset.prod_Ico_succ_top (by omega : j0 ≤ j) B]

/-- Product of `Ico` naturals as a factorial ratio (needs `1 ≤ j0`). -/
theorem prod_Ico_self_eq_fact_div (j0 : ℕ) (hj0 : 1 ≤ j0) :
    ∀ j ≥ j0, ∏ i ∈ Finset.Ico j0 j, ((i : ℝ)) =
      ((Nat.factorial (j - 1) : ℕ) : ℝ) / ((Nat.factorial (j0 - 1) : ℕ) : ℝ) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    have hempty : Finset.Ico j0 j0 = ∅ := by simp
    rw [hempty, Finset.prod_empty]
    have hne : ((Nat.factorial (j0 - 1) : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    exact (div_self hne).symm
  | succ j hj ih =>
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hprod : ∏ i ∈ Finset.Ico j0 (m + 1 + 1), ((i : ℝ)) =
        (∏ i ∈ Finset.Ico j0 (m + 1), ((i : ℝ))) * ((m + 1 : ℕ) : ℝ) :=
      Finset.prod_Ico_succ_top (by omega : j0 ≤ m + 1) (fun i => ((i : ℝ)))
    have hne : ((Nat.factorial (j0 - 1) : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have e1 : m + 1 + 1 - 1 = m + 1 := by omega
    have e2 : m + 1 - 1 = m := by omega
    rw [hprod, ih, e1, e2, Nat.factorial_succ]
    field_simp
    push_cast
    ring

/-- Mass upper bound via per-level branching lower bounds. -/
theorem mass_le_fact_bound (m B : ℕ → ℝ) (c : ℝ) (b j0 : ℕ)
    (hc : 0 < c) (hB : ∀ i, 0 < B i)
    (hmrec : ∀ j ≥ j0, m (j + 1) = m j / B j)
    (hm0nn : 0 ≤ m j0) (hj0 : 1 ≤ j0)
    (hbranch : ∀ i ≥ j0, c * (i : ℝ) ^ b ≤ B i) :
    ∀ j ≥ j0, m j ≤ m j0 /
      (c ^ (j - j0) * ((((Nat.factorial (j - 1) : ℕ) : ℝ) /
        ((Nat.factorial (j0 - 1) : ℕ) : ℝ)) ^ b)) := by
  intro j hj
  have hprod := mass_le_prod m B j0 hB hmrec j hj
  have hRpos : 0 < (((Nat.factorial (j - 1) : ℕ) : ℝ) /
      ((Nat.factorial (j0 - 1) : ℕ) : ℝ)) := by
    apply div_pos <;> exact_mod_cast Nat.factorial_pos _
  have hDpos : 0 < c ^ (j - j0) *
      ((((Nat.factorial (j - 1) : ℕ) : ℝ) /
        ((Nat.factorial (j0 - 1) : ℕ) : ℝ)) ^ b) :=
    mul_pos (pow_pos hc _) (pow_pos hRpos _)
  have h1 : ∏ i ∈ Finset.Ico j0 j, (c * (i : ℝ) ^ b) ≤
      ∏ i ∈ Finset.Ico j0 j, B i := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact mul_nonneg hc.le (pow_nonneg (Nat.cast_nonneg i) b)
    · intro i hi
      exact hbranch i (Finset.mem_Ico.mp hi).1
  have h2 : ∏ i ∈ Finset.Ico j0 j, (c * (i : ℝ) ^ b) =
      c ^ (j - j0) * ((((Nat.factorial (j - 1) : ℕ) : ℝ) /
        ((Nat.factorial (j0 - 1) : ℕ) : ℝ)) ^ b) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico,
      Finset.prod_pow, prod_Ico_self_eq_fact_div j0 hj0 j hj]
  have hle : c ^ (j - j0) * ((((Nat.factorial (j - 1) : ℕ) : ℝ) /
      ((Nat.factorial (j0 - 1) : ℕ) : ℝ)) ^ b) ≤
      ∏ i ∈ Finset.Ico j0 j, B i := h2 ▸ h1
  exact le_trans hprod (div_le_div_of_nonneg_left hm0nn hDpos hle)

#print axioms WindowMassProd.mass_le_prod
#print axioms WindowMassProd.prod_Ico_self_eq_fact_div
#print axioms WindowMassProd.mass_le_fact_bound

end WindowMassProd
