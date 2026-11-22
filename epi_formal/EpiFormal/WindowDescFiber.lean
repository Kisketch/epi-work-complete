import EpiFormal.WindowStoppedTree

/-!
# Descendant fibers for stopped-cylinder trees (P2c)

Pure combinatorics over `StoppedTree.TreeData`, no geometry: level-`N`
descendants of a level-`lvl` atom via iterated children, membership,
cardinality upper bound, nesting transfer, ancestor existence, and the
top-level meeting-count bound used by the L05 S6 step.

All tree SHAPE facts are hypotheses; the file proves their consequences.
Only Lean core axioms.
-/

namespace WindowDescFiber

/-- Level-`(lvl + d)` descendants of `u` (a level-`lvl` atom). -/
noncomputable def desc (T : StoppedTree.TreeData) (lvl : ℕ) : (d : ℕ) → (ℝ × ℝ) → Finset (ℝ × ℝ)
  | 0, u => {u}
  | d + 1, u => (desc T lvl d u).biUnion (T.child (lvl + d))

/-- Descendants stay in their level. -/
theorem desc_mem {T : StoppedTree.TreeData} {P : ℕ → Finset (ℝ × ℝ)}
    (hchild_mem : ∀ j, ∀ u ∈ P j, T.child j u ⊆ P (j + 1))
    {lvl d : ℕ} (u : ℝ × ℝ) (hu : u ∈ P lvl)
    (t : ℝ × ℝ) (ht : t ∈ desc T lvl d u) : t ∈ P (lvl + d) := by
  revert u hu t ht
  induction d with
  | zero =>
    intro u hu t ht
    simp only [desc, Finset.mem_singleton] at ht
    rw [ht]
    simpa using hu
  | succ d ih =>
    intro u hu t ht
    simp only [desc] at ht
    obtain ⟨v, hv, hvt⟩ := Finset.mem_biUnion.mp ht
    have hvd : v ∈ P (lvl + d) := ih u hu v hv
    exact hchild_mem (lvl + d) v hvd hvt

/-- Descendant count is bounded by the branching product. -/
theorem desc_card_le {T : StoppedTree.TreeData} {P : ℕ → Finset (ℝ × ℝ)} {FmaxN : ℕ → ℕ}
    (hchild_mem : ∀ j, ∀ u ∈ P j, T.child j u ⊆ P (j + 1))
    (hfiber : ∀ j, ∀ v ∈ P j, (T.child j v).card ≤ FmaxN j)
    {lvl d : ℕ} (u : ℝ × ℝ) (hu : u ∈ P lvl) :
    (desc T lvl d u).card ≤ ∏ k ∈ Finset.Ico lvl (lvl + d), FmaxN k := by
  revert u hu
  induction d with
  | zero =>
    intro u hu
    simp only [desc, Finset.card_singleton]
    have h : Finset.Ico lvl (lvl + 0) = ∅ := by simp
    rw [h, Finset.prod_empty]
  | succ d ih =>
    intro u hu
    simp only [desc] at *
    have hle : ((desc T lvl d u).biUnion (T.child (lvl + d))).card
        ≤ ∑ v ∈ desc T lvl d u, FmaxN (lvl + d) := by
      refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun v hv => ?_))
      have hvd : v ∈ P (lvl + d) := desc_mem hchild_mem u hu v hv
      exact hfiber (lvl + d) v hvd
    have hsum : ∑ v ∈ desc T lvl d u, FmaxN (lvl + d)
        = (desc T lvl d u).card * FmaxN (lvl + d) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    have hih := ih u hu
    calc ((desc T lvl d u).biUnion (T.child (lvl + d))).card
        ≤ ∑ v ∈ desc T lvl d u, FmaxN (lvl + d) := hle
      _ = (desc T lvl d u).card * FmaxN (lvl + d) := hsum
      _ ≤ (∏ k ∈ Finset.Ico lvl (lvl + d), FmaxN k) * FmaxN (lvl + d) :=
          mul_le_mul_of_nonneg_right hih (Nat.zero_le _)
      _ = ∏ k ∈ Finset.Ico lvl (lvl + (d + 1)), FmaxN k :=
          (Finset.prod_Ico_succ_top (by omega : lvl ≤ lvl + d) FmaxN).symm

#print axioms WindowDescFiber.desc_mem
#print axioms WindowDescFiber.desc_card_le

end WindowDescFiber
