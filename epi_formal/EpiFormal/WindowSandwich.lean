import Mathlib

/-!
# Sandwich lemma for the windows mass distribution (paper2 §7, L2548-2552)

For a positive scale sequence `H` with `1 / H j ^ 2 → 0`, every sufficiently
small `h > 0` is sandwiched between consecutive inverse-square scales:
`1 / H (j+1) ^ 2 ≤ h ∧ h ≤ 1 / H j ^ 2` for some `j ≥ j0`.

This mirrors the S5 level selection of the WeightedExactDim template
(`hex_lvl`, `Nat.find` + back-off-by-one), but needs no monotonicity:
the least-element argument alone suffices.
All e-specific scale facts (`H → ∞`, log comparisons) stay at the use site.
-/

namespace WindowSandwich

/-- Sandwich: every `0 < h ≤ 1 / H j0 ^ 2` lies between two consecutive
inverse-square scales at some level `j ≥ j0`. -/
theorem sandwich_of_tendsto (H : ℕ → ℝ)
    (hlim : Filter.Tendsto (fun j => 1 / (H j) ^ 2) Filter.atTop (nhds 0))
    (j0 : ℕ) {h : ℝ} (hhpos : 0 < h) (hhle : h ≤ 1 / (H j0) ^ 2) :
    ∃ j, j0 ≤ j ∧ 1 / (H (j + 1)) ^ 2 ≤ h ∧ h ≤ 1 / (H j) ^ 2 := by
  classical
  -- The set of levels strictly below scale, above j0, is nonempty.
  have hmem : Set.Iio h ∈ nhds (0 : ℝ) := by
    rw [mem_nhds_iff]
    exact ⟨Set.Iio h, fun x hx => hx, isOpen_Iio, hhpos⟩
  have hev : ∀ᶠ m in Filter.atTop, 1 / (H m) ^ 2 < h := by
    simpa only [Set.mem_Iio] using hlim.eventually hmem
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hSne : ∃ m, j0 < m ∧ 1 / (H m) ^ 2 < h :=
    ⟨max N (j0 + 1), by omega, hN _ (le_max_left _ _)⟩
  -- Least such level; back off by one.
  set m := Nat.find hSne with hmdef
  have hm := Nat.find_spec hSne
  have hm1 : 1 ≤ m := by omega
  refine ⟨m - 1, by omega, ?_, ?_⟩
  · -- Upper scale: H (j+1) = H m is below h.
    have : j0 < m - 1 + 1 := by omega
    have e1 : m - 1 + 1 = m := by omega
    rw [e1]; exact le_of_lt hm.2
  · -- Lower scale: minimality (or the j0 hypothesis) forces h ≤ scale.
    rcases eq_or_lt_of_le (by omega : j0 ≤ m - 1) with heq | hlt
    · have : m - 1 = j0 := by omega
      rw [this]; exact hhle
    · have hnot : ¬ (j0 < m - 1 ∧ 1 / (H (m - 1)) ^ 2 < h) :=
        Nat.find_min hSne (by omega : m - 1 < m)
      push Not at hnot
      exact hnot hlt

#print axioms WindowSandwich.sandwich_of_tendsto

end WindowSandwich
