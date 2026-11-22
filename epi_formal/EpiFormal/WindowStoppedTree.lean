import Mathlib

/-!
# Stopped-cylinder tree data (paper §7, L2621–2633, L2746–2750)

Abstract stopped tree: per-level finite atom families (endpoint pairs) with
children maps. Proves two generic facts used by the windows Frostman assembly:

* disjointness propagates down the tree (children of disjoint parents, pairwise
  disjoint children within each parent);
* uniform upper mass bounds propagate down via per-parent equal splitting and
  min-branching lower bounds (no cross-parent uniformity needed).

Paper-side interfaces (children sets, branching lower bounds, splitting rule)
are hypotheses; the tree SHAPE (nesting/disjointness/counting consequences) is
proved here. No project axioms beyond Lean core are used.
-/

namespace StoppedTree

/-- Finite atom families per level with children maps.
    Atoms are `(left, right)` endpoint pairs; interiors are the working sets. -/
structure TreeData where
  atoms : ℕ → Finset (ℝ × ℝ)
  child : (j : ℕ) → (ℝ × ℝ) → Finset (ℝ × ℝ)

variable {T : TreeData}

/-- Closed-interval nesting gives open-interval nesting. -/
theorem Ioo_subset_of_Icc_subset {A P : ℝ × ℝ}
    (hA : A.1 ≤ A.2)
    (hsub : Set.Icc A.1 A.2 ⊆ Set.Icc P.1 P.2) :
    Set.Ioo A.1 A.2 ⊆ Set.Ioo P.1 P.2 := by
  intro x hx
  have hxA := hx
  rw [Set.mem_Ioo] at hxA ⊢
  have h1 : A.1 ∈ Set.Icc A.1 A.2 := ⟨le_rfl, hA⟩
  have h2 : A.2 ∈ Set.Icc A.1 A.2 := ⟨hA, le_rfl⟩
  have hP1 := hsub h1
  have hP2 := hsub h2
  rw [Set.mem_Icc] at hP1 hP2
  exact ⟨lt_of_le_of_lt hP1.1 hxA.1, lt_of_lt_of_le hxA.2 hP2.2⟩

/-- Pairwise disjointness propagates one level down. -/
theorem nodup_of_children_disjoint {j0 : ℕ}
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 ≤ I.2)
    (hbase : Set.Pairwise (↑(T.atoms j0))
      (fun (I J : ℝ × ℝ) => Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2)))
    (hchild_disj : ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      Set.Pairwise (↑(T.child j I))
        (fun (A : ℝ × ℝ) (B : ℝ × ℝ) => Disjoint (Set.Ioo A.1 A.2) (Set.Ioo B.1 B.2)))
    (hnest : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ C ∈ T.child j I,
      Set.Icc C.1 C.2 ⊆ Set.Icc I.1 I.2)
    (hmem : ∀ j ≥ j0, ∀ I ∈ T.atoms (j + 1),
      ∃ P ∈ T.atoms j, I ∈ T.child j P)
    : ∀ j ≥ j0, Set.Pairwise (↑(T.atoms j))
      (fun (I J : ℝ × ℝ) => Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact hbase
  | succ j hj ih =>
    intro A hA B hB hne
    obtain ⟨PA, hPA, hmA⟩ := hmem j hj A hA
    obtain ⟨PB, hPB, hmB⟩ := hmem j hj B hB
    by_cases heq : PA = PB
    · subst heq
      exact hchild_disj j hj PA hPA
        (Finset.mem_coe.mpr hmA) (Finset.mem_coe.mpr hmB) hne
    · have hdisj := ih (Finset.mem_coe.mpr hPA) (Finset.mem_coe.mpr hPB) heq
      have hsubA : Set.Ioo A.1 A.2 ⊆ Set.Ioo PA.1 PA.2 :=
        Ioo_subset_of_Icc_subset (htriv (j + 1) (by omega) A hA) (hnest j hj PA hPA A hmA)
      have hsubB : Set.Ioo B.1 B.2 ⊆ Set.Ioo PB.1 PB.2 :=
        Ioo_subset_of_Icc_subset (htriv (j + 1) (by omega) B hB) (hnest j hj PB hPB B hmB)
      exact Disjoint.mono hsubA hsubB hdisj

variable {μ : MeasureTheory.Measure ℝ}

/-- Uniform upper mass bounds propagate down via per-parent splitting.
    Per-parent equal splitting (`hsplit`) needs only min-branching lower bounds
    (`hB1`); no cross-parent uniformity is assumed. -/
theorem mass_le_of_split {j0 : ℕ} {m B : ℕ → ℝ}
    (hB1 : ∀ j ≥ j0, 1 ≤ B j)
    (hm0 : ∀ I ∈ T.atoms j0, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m j0))
    (hmrec : ∀ j ≥ j0, m (j + 1) = m j / B j)
    (hsplit : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ C ∈ T.child j I,
      μ (Set.Icc C.1 C.2) ≤ μ (Set.Icc I.1 I.2) / ENNReal.ofReal (B j))
    (hmem : ∀ j ≥ j0, ∀ I ∈ T.atoms (j + 1),
      ∃ P ∈ T.atoms j, I ∈ T.child j P)
    : ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m j) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact hm0
  | succ j hj ih =>
    intro I hI
    obtain ⟨P, hP, hm⟩ := hmem j hj I hI
    have hPle : μ (Set.Icc P.1 P.2) ≤ ENNReal.ofReal (m j) := ih P hP
    have hBpos : (0 : ℝ) < B j := lt_of_lt_of_le one_pos (hB1 j hj)
    calc μ (Set.Icc I.1 I.2)
        ≤ μ (Set.Icc P.1 P.2) / ENNReal.ofReal (B j) :=
          hsplit j hj P hP I hm
      _ ≤ ENNReal.ofReal (m j) / ENNReal.ofReal (B j) :=
          ENNReal.div_le_div_right hPle _
      _ = ENNReal.ofReal (m (j + 1)) := by
          rw [hmrec j hj, ← ENNReal.ofReal_div_of_pos hBpos]

#print axioms StoppedTree.Ioo_subset_of_Icc_subset
#print axioms StoppedTree.nodup_of_children_disjoint
#print axioms StoppedTree.mass_le_of_split

end StoppedTree
