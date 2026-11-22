import EpiFormal.WindowStoppedTree
import EpiFormal.WindowMassProd

open scoped ENNReal

/-!
# Stopped-tree uniform mass bound (paper §7, windows Frostman input)

`mass_le_of_split`（StoppedTree：均分上界）与 `mass_le_prod`
（WindowMassProd：递推展开）的合成：stopped 树上第 j 层原子的
质量被首层质量除以分支下界连乘积所控制。

分支下界 `1 ≤ B j` 取全局形式（用方以 `max 1 ·` 垫小层即可满足）。
-/

namespace WindowStoppedUniform

variable {μ : MeasureTheory.Measure ℝ} {T : StoppedTree.TreeData}

/-- 均匀分裂质量界：`μ I ≤ m j0 / ∏_{i∈[j0,j)} B i`。 -/
theorem stopped_uniform_bound
    {j0 : ℕ} {m B : ℕ → ℝ}
    (hB : ∀ j, 1 ≤ B j)
    (hm0 : ∀ I ∈ T.atoms j0, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m j0))
    (hmrec : ∀ j ≥ j0, m (j + 1) = m j / B j)
    (hsplit : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ C ∈ T.child j I,
      μ (Set.Icc C.1 C.2) ≤ μ (Set.Icc I.1 I.2) / ENNReal.ofReal (B j))
    (hmem : ∀ j ≥ j0, ∀ I ∈ T.atoms (j + 1), ∃ P ∈ T.atoms j, I ∈ T.child j P) :
    ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m j0 / ∏ i ∈ Finset.Ico j0 j, B i) := by
  intro j hj I hI
  have hB1 : ∀ k ≥ j0, 1 ≤ B k := fun k _ => hB k
  have h1 := StoppedTree.mass_le_of_split (T := T) (μ := μ) hB1 hm0 hmrec hsplit hmem j hj I hI
  have hBpos : ∀ i, 0 < B i :=
    fun i => lt_of_lt_of_le one_pos (hB i)
  have h2 := WindowMassProd.mass_le_prod m B j0 hBpos hmrec j hj
  exact le_trans h1 (ENNReal.ofReal_le_ofReal h2)

#print axioms WindowStoppedUniform.stopped_uniform_bound

end WindowStoppedUniform
