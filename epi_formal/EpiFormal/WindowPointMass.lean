import EpiFormal.WindowStoppedTree
import EpiFormal.WindowMassProd

open scoped ENNReal

/-!
# Point mass vanishes (paper §7 interface: `μ(U) = 0` for singletons)

For a splitting tree with branching `B j ≥ 2` (from `j0` on) and global
positivity, per-atom mass decays like `m j0 / 2^{j-j0} → 0`. A point covered
by nested atoms at every level therefore has measure zero. This discharges
the singleton case that the per-window threshold (`mu_window_le_full`
needs `0 < diam`) excludes.
-/

namespace WindowPointMass

variable {μ : MeasureTheory.Measure ℝ}

/-- Point mass vanishes under nested atomic covers with doubling branching. -/
theorem mu_singleton_zero
    {T : StoppedTree.TreeData} {m B : ℕ → ℝ} {j0 : ℕ}
    (hB2 : ∀ j ≥ j0, 2 ≤ B j)
    (hBpos : ∀ i, (0 : ℝ) < B i)
    (hm0 : ∀ I ∈ T.atoms j0, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m j0))
    (hm0nn : 0 ≤ m j0)
    (hmrec : ∀ j ≥ j0, m (j + 1) = m j / B j)
    (hsplit : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ C ∈ T.child j I,
      μ (Set.Icc C.1 C.2) ≤ μ (Set.Icc I.1 I.2) / ENNReal.ofReal (B j))
    (hmem : ∀ j ≥ j0, ∀ I ∈ T.atoms (j + 1),
      ∃ P ∈ T.atoms j, I ∈ T.child j P)
    (hnest : ∀ x : ℝ, ∀ j ≥ j0, ∃ I ∈ T.atoms j, x ∈ Set.Icc I.1 I.2)
    (x : ℝ) :
    μ {x} = 0 := by
  have hB1 : ∀ j ≥ j0, 1 ≤ B j := fun j hj => by
    have h2 := hB2 j hj
    have h0 : (0 : ℝ) < 2 := by norm_num
    linarith
  -- Per-level bound via splitting + unrolling.
  have hle : ∀ j ≥ j0,
      μ {x} ≤ ENNReal.ofReal (m j0 / (2 : ℝ) ^ (j - j0)) := by
    intro j hj
    obtain ⟨I, hI, hxI⟩ := hnest x j hj
    have hsub : μ {x} ≤ μ (Set.Icc I.1 I.2) := by
      apply MeasureTheory.measure_mono
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact hxI
    have hmass : μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m j) :=
      StoppedTree.mass_le_of_split hB1 hm0 hmrec hsplit hmem j hj I hI
    have hunroll : m j ≤ m j0 / ∏ i ∈ Finset.Ico j0 j, B i :=
      WindowMassProd.mass_le_prod m B j0 hBpos hmrec j hj
    have hprod : (2 : ℝ) ^ (j - j0) ≤ ∏ i ∈ Finset.Ico j0 j, B i := by
      have hcard : (Finset.Ico j0 j).card = j - j0 := Nat.card_Ico j0 j
      have h2 : ∏ _i ∈ Finset.Ico j0 j, (2 : ℝ) = (2 : ℝ) ^ (j - j0) := by
        rw [Finset.prod_const, hcard]
      rw [← h2]
      exact Finset.prod_le_prod₀ (fun i _ => by norm_num) (fun i hi => by
        have hmem' : j0 ≤ i := (Finset.mem_Ico.mp hi).1
        exact hB2 i hmem')
    have hdiv : m j ≤ m j0 / (2 : ℝ) ^ (j - j0) := by
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ (j - j0) := by positivity
      have hrec : (1 : ℝ) / ∏ i ∈ Finset.Ico j0 j, B i ≤ 1 / (2 : ℝ) ^ (j - j0) :=
        one_div_le_one_div_of_le h2pos hprod
      have hmul : m j0 * (1 / ∏ i ∈ Finset.Ico j0 j, B i)
          ≤ m j0 * (1 / (2 : ℝ) ^ (j - j0)) :=
        mul_le_mul_of_nonneg_left hrec hm0nn
      calc m j ≤ m j0 / ∏ i ∈ Finset.Ico j0 j, B i := hunroll
        _ = m j0 * (1 / ∏ i ∈ Finset.Ico j0 j, B i) :=
          div_eq_mul_one_div _ _
        _ ≤ m j0 * (1 / (2 : ℝ) ^ (j - j0)) := hmul
        _ = m j0 / (2 : ℝ) ^ (j - j0) :=
          (div_eq_mul_one_div _ _).symm
    calc μ {x} ≤ μ (Set.Icc I.1 I.2) := hsub
      _ ≤ ENNReal.ofReal (m j) := hmass
      _ ≤ ENNReal.ofReal (m j0 / (2 : ℝ) ^ (j - j0)) := by
          apply ENNReal.ofReal_le_ofReal
          exact hdiv
  -- Squeeze along j = j0 + k.
  have htend : Filter.Tendsto (fun k => ENNReal.ofReal (m j0 / (2 : ℝ) ^ ((j0 + k) - j0)))
      Filter.atTop (nhds 0) := by
    have hlim : Filter.Tendsto (fun k : ℕ => m j0 / (2 : ℝ) ^ ((j0 + k) - j0))
        Filter.atTop (nhds 0) := by
      have heq : (fun k : ℕ => m j0 / (2 : ℝ) ^ ((j0 + k) - j0)) = fun k => m j0 * ((1 / 2 : ℝ) ^ k) := by
        funext k
        have hk : (j0 + k) - j0 = k := by omega
        rw [hk, div_pow, one_pow, one_div, ← div_eq_mul_inv]
      rw [heq]
      have hgeo : Filter.Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ k)) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hmul := hgeo.const_mul (m j0)
      simpa using hmul
    have hcomp := (ENNReal.continuous_ofReal.tendsto 0).comp hlim
    simpa [Function.comp_def, ENNReal.ofReal_zero] using hcomp
  have hbound : ∀ k, μ {x} ≤ ENNReal.ofReal (m j0 / (2 : ℝ) ^ ((j0 + k) - j0)) :=
    fun k => hle (j0 + k) (by omega)
  have hle0 : μ {x} ≤ 0 :=
    ge_of_tendsto htend (Filter.Eventually.of_forall (fun k => hbound k))
  exact le_antisymm hle0 zero_le

#print axioms WindowPointMass.mu_singleton_zero
