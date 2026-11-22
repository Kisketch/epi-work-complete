import EpiFormal.WindowStoppedTree
import EpiFormal.WindowDescFiber

/-!
# Stopped-tree Cantor set, uniform pruning, and double counting (L05 support)

Provides the purely combinatorial & topological bridge from a stopped-cylinder
tree `T : StoppedTree.TreeData` to the L05 Frostman `Hwin` discharge:

1. `cantorSet T j0`: the limit set `⋂ j ≥ j0, ⋃ I ∈ T.atoms j, Icc I.1 I.2`.
2. `isCompact_cantorSet`: compactness of `cantorSet T j0`.
3. `exists_ancestor_desc`: every level-`(lvl + d)` atom descends from a
   level-`lvl` atom via `WindowDescFiber.desc`, with nested closed intervals.
4. `exists_mem_cantorSet_of_mem_atoms`: Cantor intersection theorem — every
   level-`N` atom (`N ≥ j0`) contains a point of `cantorSet T j0`.
5. `atoms_card_le_sum_meet_desc`: double-counting bound for `Hcount`,
   bounding `(T.atoms N).card` by `∑ i ∈ F, Kc i * ∏_{k ∈ [lvl i, N)} FmaxN k`.
6. `pruneTree`: given any non-uniform tree with lower branching `B j ≤ (T.child j u).card`,
   constructs a pruned subtree with exact branching `= B j`, exact level count
   `∏_{k ∈ [j0, j)} B k`, and `cantorSet (pruneTree ...) j0 ⊆ cantorSet T j0`.

No project axioms beyond Lean core (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace WindowTreePrune

open Set Finset

/-- The Cantor limit set of a stopped-cylinder tree starting at level `j0`. -/
def cantorSet (T : StoppedTree.TreeData) (j0 : ℕ) : Set ℝ :=
  ⋂ (j : ℕ) (_ : j0 ≤ j), ⋃ I ∈ T.atoms j, Set.Icc I.1 I.2

/-- Every level union of closed intervals is closed. -/
theorem isClosed_levelUnion (T : StoppedTree.TreeData) (j : ℕ) :
    IsClosed (⋃ I ∈ T.atoms j, Set.Icc I.1 I.2) :=
  (T.atoms j).finite_toSet.isClosed_biUnion fun _ _ => isClosed_Icc

/-- The Cantor limit set is compact (closed subset of the compact level-`j0` union). -/
theorem isCompact_cantorSet (T : StoppedTree.TreeData) (j0 : ℕ) :
    IsCompact (cantorSet T j0) := by
  have hcomp0 : IsCompact (⋃ I ∈ T.atoms j0, Set.Icc I.1 I.2) :=
    (T.atoms j0).isCompact_biUnion fun _ _ => isCompact_Icc
  have hclosed : IsClosed (cantorSet T j0) :=
    isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_levelUnion T j
  have hsub : cantorSet T j0 ⊆ ⋃ I ∈ T.atoms j0, Set.Icc I.1 I.2 := by
    intro x hx
    exact (Set.mem_iInter.mp (Set.mem_iInter.mp hx j0)) le_rfl
  exact hcomp0.of_isClosed_subset hclosed hsub

/-- Descendants stay in their level (starting from `j0`). -/
theorem desc_mem_from {T : StoppedTree.TreeData} {j0 : ℕ}
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    {lvl d : ℕ} (hlvl : j0 ≤ lvl) (u : ℝ × ℝ) (hu : u ∈ T.atoms lvl)
    (t : ℝ × ℝ) (ht : t ∈ WindowDescFiber.desc T lvl d u) :
    t ∈ T.atoms (lvl + d) := by
  revert u hu t ht
  induction d with
  | zero =>
    intro u hu t ht
    simp only [WindowDescFiber.desc, Finset.mem_singleton] at ht
    rw [ht]
    simpa using hu
  | succ d ih =>
    intro u hu t ht
    simp only [WindowDescFiber.desc] at ht
    obtain ⟨v, hv, hvt⟩ := Finset.mem_biUnion.mp ht
    have hvd : v ∈ T.atoms (lvl + d) := ih u hu v hv
    exact hchild_mem (lvl + d) (by omega) v hvd hvt

/-- Descendant count is bounded by the branching product (starting from `j0`). -/
theorem desc_card_le_from {T : StoppedTree.TreeData} {j0 : ℕ} {FmaxN : ℕ → ℕ}
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hfiber : ∀ j ≥ j0, ∀ v ∈ T.atoms j, (T.child j v).card ≤ FmaxN j)
    {lvl d : ℕ} (hlvl : j0 ≤ lvl) (u : ℝ × ℝ) (hu : u ∈ T.atoms lvl) :
    (WindowDescFiber.desc T lvl d u).card ≤ ∏ k ∈ Finset.Ico lvl (lvl + d), FmaxN k := by
  revert u hu
  induction d with
  | zero =>
    intro u hu
    simp only [WindowDescFiber.desc, Finset.card_singleton]
    have h : Finset.Ico lvl (lvl + 0) = ∅ := by simp
    rw [h, Finset.prod_empty]
  | succ d ih =>
    intro u hu
    simp only [WindowDescFiber.desc] at *
    have hle : ((WindowDescFiber.desc T lvl d u).biUnion (T.child (lvl + d))).card
        ≤ ∑ v ∈ WindowDescFiber.desc T lvl d u, FmaxN (lvl + d) := by
      refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun v hv => ?_)
      have hvd : v ∈ T.atoms (lvl + d) := desc_mem_from hchild_mem hlvl u hu v hv
      exact hfiber (lvl + d) (by omega) v hvd
    have hsum : ∑ _v ∈ WindowDescFiber.desc T lvl d u, FmaxN (lvl + d)
        = (WindowDescFiber.desc T lvl d u).card * FmaxN (lvl + d) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    have hih := ih u hu
    calc ((WindowDescFiber.desc T lvl d u).biUnion (T.child (lvl + d))).card
        ≤ ∑ _v ∈ WindowDescFiber.desc T lvl d u, FmaxN (lvl + d) := hle
      _ = (WindowDescFiber.desc T lvl d u).card * FmaxN (lvl + d) := hsum
      _ ≤ (∏ k ∈ Finset.Ico lvl (lvl + d), FmaxN k) * FmaxN (lvl + d) :=
          Nat.mul_le_mul_right _ hih
      _ = ∏ k ∈ Finset.Ico lvl (lvl + (d + 1)), FmaxN k :=
          (Finset.prod_Ico_succ_top (by omega : lvl ≤ lvl + d) FmaxN).symm

/-- Every level-`(lvl + d)` atom has a level-`lvl` ancestor whose closed interval
    contains it and whose `desc` family contains it. -/
theorem exists_ancestor_desc {T : StoppedTree.TreeData} {j0 : ℕ}
    (hmem : ∀ j ≥ j0, ∀ t ∈ T.atoms (j + 1), ∃ u ∈ T.atoms j, t ∈ T.child j u)
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2)
    {lvl d : ℕ} (hlvl : j0 ≤ lvl) (t : ℝ × ℝ) (ht : t ∈ T.atoms (lvl + d)) :
    ∃ u ∈ T.atoms lvl,
      t ∈ WindowDescFiber.desc T lvl d u ∧ Set.Icc t.1 t.2 ⊆ Set.Icc u.1 u.2 := by
  revert t ht
  induction d with
  | zero =>
    intro t ht
    refine ⟨t, by simpa using ht, ?_, Subset.rfl⟩
    simp [WindowDescFiber.desc]
  | succ d ih =>
    intro t ht
    obtain ⟨v, hv, htv⟩ := hmem (lvl + d) (by omega) t ht
    obtain ⟨u, hu, hvu, hsubv⟩ := ih v hv
    refine ⟨u, hu, ?_, Subset.trans (hnest (lvl + d) (by omega) v hv t htv) hsubv⟩
    simp only [WindowDescFiber.desc]
    exact Finset.mem_biUnion.mpr ⟨v, hvu, htv⟩

/-- Cantor intersection property: every atom at level `N ≥ j0` contains a point
    of `cantorSet T j0`. -/
theorem exists_mem_cantorSet_of_mem_atoms {T : StoppedTree.TreeData} {j0 : ℕ}
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 ≤ I.2)
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_ne : ∀ j ≥ j0, ∀ u ∈ T.atoms j, (T.child j u).Nonempty)
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2)
    (hmem : ∀ j ≥ j0, ∀ t ∈ T.atoms (j + 1), ∃ u ∈ T.atoms j, t ∈ T.child j u)
    {N : ℕ} (hN : j0 ≤ N) {I0 : ℝ × ℝ} (hI0 : I0 ∈ T.atoms N) :
    ∃ x ∈ cantorSet T j0, x ∈ Set.Icc I0.1 I0.2 := by
  classical
  let step : ∀ k : ℕ, {I : ℝ × ℝ // I ∈ T.atoms (N + k)} →
      {I : ℝ × ℝ // I ∈ T.atoms (N + (k + 1))} := fun k cur =>
    let hne := hchild_ne (N + k) (by omega) cur.1 cur.2
    let c := Classical.choose hne
    let hc : c ∈ T.child (N + k) cur.1 := Classical.choose_spec hne
    ⟨c, by
      have hm := hchild_mem (N + k) (by omega) cur.1 cur.2 hc
      simpa [Nat.add_assoc] using hm⟩
  let seq : ∀ k : ℕ, {I : ℝ × ℝ // I ∈ T.atoms (N + k)} :=
    Nat.rec ⟨I0, by simpa using hI0⟩ step
  let Kseq : ℕ → Set ℝ := fun k => Set.Icc (seq k).1.1 (seq k).1.2
  have hanti : ∀ k, Kseq (k + 1) ⊆ Kseq k := by
    intro k
    have hne := hchild_ne (N + k) (by omega) (seq k).1 (seq k).2
    have hc : (seq (k + 1)).1 ∈ T.child (N + k) (seq k).1 := Classical.choose_spec hne
    exact hnest (N + k) (by omega) (seq k).1 (seq k).2 (seq (k + 1)).1 hc
  have hne_seq : ∀ k, (Kseq k).Nonempty := fun k =>
    Set.nonempty_Icc.mpr (htriv (N + k) (by omega) (seq k).1 (seq k).2)
  have hcomp_seq : IsCompact (Kseq 0) := isCompact_Icc
  have hclosed_seq : ∀ k, IsClosed (Kseq k) := fun _ => isClosed_Icc
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    Kseq hanti hne_seq hcomp_seq hclosed_seq
  have hx_all : ∀ k, x ∈ Kseq k := Set.mem_iInter.mp hx
  have hx0 : x ∈ Set.Icc I0.1 I0.2 := by simpa [Kseq, seq] using hx_all 0
  refine ⟨x, ?_, hx0⟩
  rw [cantorSet, Set.mem_iInter]
  intro j
  rw [Set.mem_iInter]
  intro hj
  by_cases hNj : N ≤ j
  · have hk : N + (j - N) = j := by omega
    have hxk : x ∈ Set.Icc (seq (j - N)).1.1 (seq (j - N)).1.2 := hx_all (j - N)
    rcases hseq : seq (j - N) with ⟨I, hI⟩
    rw [hseq] at hxk
    have hIj : I ∈ T.atoms j := by rwa [hk] at hI
    exact Set.mem_biUnion hIj hxk
  · have hlt : j ≤ N := by omega
    have heq : j + (N - j) = N := by omega
    have hI0' : I0 ∈ T.atoms (j + (N - j)) := by rwa [heq]
    obtain ⟨u, hu, _, hsub⟩ := exists_ancestor_desc hmem hnest hj I0 hI0'
    exact Set.mem_biUnion hu (hsub hx0)

/-- If `T.atoms j0` is nonempty, `cantorSet T j0` is nonempty. -/
theorem cantorSet_nonempty {T : StoppedTree.TreeData} {j0 : ℕ}
    (hne0 : (T.atoms j0).Nonempty)
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 ≤ I.2)
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_ne : ∀ j ≥ j0, ∀ u ∈ T.atoms j, (T.child j u).Nonempty)
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2)
    (hmem : ∀ j ≥ j0, ∀ t ∈ T.atoms (j + 1), ∃ u ∈ T.atoms j, t ∈ T.child j u) :
    (cantorSet T j0).Nonempty := by
  obtain ⟨I0, hI0⟩ := hne0
  obtain ⟨x, hx, _⟩ :=
    exists_mem_cantorSet_of_mem_atoms htriv hchild_mem hchild_ne hnest hmem le_rfl hI0
  exact ⟨x, hx⟩

open Classical in
/-- Double-counting bound for `Hcount`: any finite cover of `cantorSet T j0`
    controls `(T.atoms N).card` via per-window meeting counts and descendant fibers. -/
theorem atoms_card_le_sum_meet_desc {ι : Type}
    {T : StoppedTree.TreeData} {j0 N : ℕ} {FmaxN : ℕ → ℕ}
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 ≤ I.2)
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_ne : ∀ j ≥ j0, ∀ u ∈ T.atoms j, (T.child j u).Nonempty)
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2)
    (hmem : ∀ j ≥ j0, ∀ t ∈ T.atoms (j + 1), ∃ u ∈ T.atoms j, t ∈ T.child j u)
    (hfiber : ∀ j ≥ j0, ∀ v ∈ T.atoms j, (T.child j v).card ≤ FmaxN j)
    (V : ι → Set ℝ) (F : Finset ι)
    (hcov : cantorSet T j0 ⊆ ⋃ i ∈ F, V i)
    (lvl : ι → ℕ) (hlvl_lo : ∀ i ∈ F, j0 ≤ lvl i)
    (hlvl_hi : ∀ i ∈ F, lvl i ≤ N) (hN : j0 ≤ N) :
    (T.atoms N).card ≤
      ∑ i ∈ F,
        ((T.atoms (lvl i)).filter (fun (u : ℝ × ℝ) => (Set.Icc u.1 u.2 ∩ V i).Nonempty)).card *
          ∏ k ∈ Finset.Ico (lvl i) N, FmaxN k := by
  let meet : ι → Finset (ℝ × ℝ) := fun i =>
    (T.atoms (lvl i)).filter (fun (u : ℝ × ℝ) => (Set.Icc u.1 u.2 ∩ V i).Nonempty)
  have hsub : T.atoms N ⊆
      F.biUnion (fun i => (meet i).biUnion (WindowDescFiber.desc T (lvl i) (N - lvl i))) := by
    intro t ht
    obtain ⟨x, hxK, hxt⟩ :=
      exists_mem_cantorSet_of_mem_atoms htriv hchild_mem hchild_ne hnest hmem hN ht
    obtain ⟨i, hiF, hxi⟩ := Set.mem_iUnion₂.mp (hcov hxK)
    have hli : j0 ≤ lvl i := hlvl_lo i hiF
    have hleN : lvl i ≤ N := hlvl_hi i hiF
    have hsum_eq : lvl i + (N - lvl i) = N := by omega
    have ht' : t ∈ T.atoms (lvl i + (N - lvl i)) := by rwa [hsum_eq]
    obtain ⟨u, hu, htu, hsub_tu⟩ := exists_ancestor_desc hmem hnest hli t ht'
    have hxu : x ∈ Set.Icc u.1 u.2 := hsub_tu hxt
    have humeet : u ∈ meet i := Finset.mem_filter.mpr ⟨hu, ⟨x, hxu, hxi⟩⟩
    exact Finset.mem_biUnion.mpr ⟨i, hiF, Finset.mem_biUnion.mpr ⟨u, humeet, htu⟩⟩
  calc (T.atoms N).card
      ≤ (F.biUnion (fun i =>
          (meet i).biUnion (WindowDescFiber.desc T (lvl i) (N - lvl i)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i ∈ F, ((meet i).biUnion (WindowDescFiber.desc T (lvl i) (N - lvl i))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ i ∈ F, ((meet i).card * ∏ k ∈ Finset.Ico (lvl i) N, FmaxN k) := by
        apply Finset.sum_le_sum
        intro i hiF
        have hli : j0 ≤ lvl i := hlvl_lo i hiF
        have hleN : lvl i ≤ N := hlvl_hi i hiF
        have hsum_eq : lvl i + (N - lvl i) = N := by omega
        calc ((meet i).biUnion (WindowDescFiber.desc T (lvl i) (N - lvl i))).card
            ≤ ∑ u ∈ meet i, (WindowDescFiber.desc T (lvl i) (N - lvl i) u).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _u ∈ meet i, ∏ k ∈ Finset.Ico (lvl i) N, FmaxN k := by
              apply Finset.sum_le_sum
              intro u hu
              have hu_atoms : u ∈ T.atoms (lvl i) := (Finset.mem_filter.mp hu).1
              have hcard := desc_card_le_from (d := N - lvl i) hchild_mem hfiber hli u hu_atoms
              rwa [hsum_eq] at hcard
          _ = (meet i).card * ∏ k ∈ Finset.Ico (lvl i) N, FmaxN k := by
              simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

/-! ### Uniform-branching tree pruning -/

section Prune

open Classical in
/-- Pruned children map: picks a subset of size `B j` whenever `(T.child j u).card ≥ B j`. -/
noncomputable def pruneChild (T : StoppedTree.TreeData) (B : ℕ → ℕ)
    (j : ℕ) (u : ℝ × ℝ) : Finset (ℝ × ℝ) :=
  if h : B j ≤ (T.child j u).card then
    Classical.choose (Finset.exists_subset_card_eq h)
  else ∅

theorem pruneChild_subset (T : StoppedTree.TreeData) (B : ℕ → ℕ) (j : ℕ) (u : ℝ × ℝ) :
    pruneChild T B j u ⊆ T.child j u := by
  unfold pruneChild
  split_ifs with h
  · exact (Classical.choose_spec (Finset.exists_subset_card_eq h)).1
  · exact Finset.empty_subset _

theorem pruneChild_card (T : StoppedTree.TreeData) (B : ℕ → ℕ) (j : ℕ) (u : ℝ × ℝ)
    (h : B j ≤ (T.child j u).card) :
    (pruneChild T B j u).card = B j := by
  unfold pruneChild
  simp only [h, ↓reduceDIte]
  exact (Classical.choose_spec (Finset.exists_subset_card_eq h)).2

open Classical in
/-- Iterated pruned level atoms starting from a single root `{I0}` at offset `0`. -/
noncomputable def pruneAtomsAux (T : StoppedTree.TreeData) (B : ℕ → ℕ)
    (j0 : ℕ) (I0 : ℝ × ℝ) : ℕ → Finset (ℝ × ℝ)
  | 0 => {I0}
  | d + 1 => (pruneAtomsAux T B j0 I0 d).biUnion (pruneChild T B (j0 + d))

/-- Pruned tree anchored at level `j0` with single root `I0`. -/
noncomputable def pruneTree (T : StoppedTree.TreeData) (B : ℕ → ℕ)
    (j0 : ℕ) (I0 : ℝ × ℝ) : StoppedTree.TreeData where
  atoms := fun j => if j0 ≤ j then pruneAtomsAux T B j0 I0 (j - j0) else ∅
  child := pruneChild T B

theorem pruneTree_atoms_base (T : StoppedTree.TreeData) (B : ℕ → ℕ)
    (j0 : ℕ) (I0 : ℝ × ℝ) :
    (pruneTree T B j0 I0).atoms j0 = {I0} := by
  simp [pruneTree, pruneAtomsAux]

open Classical in
theorem pruneTree_atoms_succ (T : StoppedTree.TreeData) (B : ℕ → ℕ)
    (j0 : ℕ) (I0 : ℝ × ℝ) {j : ℕ} (hj : j0 ≤ j) :
    (pruneTree T B j0 I0).atoms (j + 1) =
      ((pruneTree T B j0 I0).atoms j).biUnion (pruneChild T B j) := by
  have hj1 : j0 ≤ j + 1 := by omega
  have hsub : j + 1 - j0 = (j - j0) + 1 := by omega
  have hadd : j0 + (j - j0) = j := by omega
  simp only [pruneTree, hj, hj1, ↓reduceIte, hsub, pruneAtomsAux, hadd]

theorem pruneTree_atoms_subset {T : StoppedTree.TreeData} {B : ℕ → ℕ}
    {j0 : ℕ} {I0 : ℝ × ℝ} (hI0 : I0 ∈ T.atoms j0)
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1)) :
    ∀ j ≥ j0, (pruneTree T B j0 I0).atoms j ⊆ T.atoms j := by
  classical
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    rw [pruneTree_atoms_base]
    exact Finset.singleton_subset_iff.mpr hI0
  | succ j hj ih =>
    rw [pruneTree_atoms_succ T B j0 I0 hj]
    intro c hc
    obtain ⟨u, hu, hcu⟩ := Finset.mem_biUnion.mp hc
    exact hchild_mem j hj u (ih hu) (pruneChild_subset T B j u hcu)

theorem pruneTree_child_mem (T : StoppedTree.TreeData) (B : ℕ → ℕ)
    (j0 : ℕ) (I0 : ℝ × ℝ) :
    ∀ j ≥ j0, ∀ u ∈ (pruneTree T B j0 I0).atoms j,
      (pruneTree T B j0 I0).child j u ⊆ (pruneTree T B j0 I0).atoms (j + 1) := by
  classical
  intro j hj u hu c hc
  rw [pruneTree_atoms_succ T B j0 I0 hj]
  exact Finset.mem_biUnion.mpr ⟨u, hu, hc⟩

theorem pruneTree_mem_parent (T : StoppedTree.TreeData) (B : ℕ → ℕ)
    (j0 : ℕ) (I0 : ℝ × ℝ) :
    ∀ j ≥ j0, ∀ t ∈ (pruneTree T B j0 I0).atoms (j + 1),
      ∃ u ∈ (pruneTree T B j0 I0).atoms j, t ∈ (pruneTree T B j0 I0).child j u := by
  classical
  intro j hj t ht
  rw [pruneTree_atoms_succ T B j0 I0 hj] at ht
  exact Finset.mem_biUnion.mp ht

theorem pruneTree_child_card {T : StoppedTree.TreeData} {B : ℕ → ℕ}
    {j0 : ℕ} {I0 : ℝ × ℝ} (hI0 : I0 ∈ T.atoms j0)
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_card : ∀ j ≥ j0, ∀ u ∈ T.atoms j, B j ≤ (T.child j u).card) :
    ∀ j ≥ j0, ∀ u ∈ (pruneTree T B j0 I0).atoms j,
      ((pruneTree T B j0 I0).child j u).card = B j := by
  intro j hj u hu
  have huT : u ∈ T.atoms j := pruneTree_atoms_subset hI0 hchild_mem j hj hu
  exact pruneChild_card T B j u (hchild_card j hj u huT)

theorem pruneTree_atoms_card {T : StoppedTree.TreeData} {B : ℕ → ℕ}
    {j0 : ℕ} {I0 : ℝ × ℝ} (hI0 : I0 ∈ T.atoms j0)
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_card : ∀ j ≥ j0, ∀ u ∈ T.atoms j, B j ≤ (T.child j u).card)
    (hdisj_child : ∀ j ≥ j0, ∀ u₁ ∈ T.atoms j, ∀ u₂ ∈ T.atoms j, u₁ ≠ u₂ →
      Disjoint (T.child j u₁) (T.child j u₂)) :
    ∀ j ≥ j0, ((pruneTree T B j0 I0).atoms j).card = ∏ k ∈ Finset.Ico j0 j, B k := by
  classical
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    rw [pruneTree_atoms_base, Finset.card_singleton, Finset.Ico_self, Finset.prod_empty]
  | succ j hj ih =>
    rw [pruneTree_atoms_succ T B j0 I0 hj]
    have hdisj : Set.Pairwise (↑((pruneTree T B j0 I0).atoms j))
        (fun u₁ u₂ => Disjoint (pruneChild T B j u₁) (pruneChild T B j u₂)) := by
      intro u₁ hu₁ u₂ hu₂ hne
      have h1 := pruneTree_atoms_subset hI0 hchild_mem j hj (Finset.mem_coe.mp hu₁)
      have h2 := pruneTree_atoms_subset hI0 hchild_mem j hj (Finset.mem_coe.mp hu₂)
      exact Disjoint.mono (pruneChild_subset T B j u₁) (pruneChild_subset T B j u₂)
        (hdisj_child j hj u₁ h1 u₂ h2 hne)
    rw [Finset.card_biUnion hdisj]
    have hsum : ∑ u ∈ (pruneTree T B j0 I0).atoms j, (pruneChild T B j u).card =
        ∑ _u ∈ (pruneTree T B j0 I0).atoms j, B j := by
      apply Finset.sum_congr rfl
      intro u hu
      exact pruneTree_child_card hI0 hchild_mem hchild_card j hj u hu
    rw [hsum, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, ih,
      Finset.prod_Ico_succ_top hj B]

theorem cantorSet_pruneTree_subset {T : StoppedTree.TreeData} {B : ℕ → ℕ}
    {j0 : ℕ} {I0 : ℝ × ℝ} (hI0 : I0 ∈ T.atoms j0)
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1)) :
    cantorSet (pruneTree T B j0 I0) j0 ⊆ cantorSet T j0 := by
  intro x hx
  rw [cantorSet, Set.mem_iInter] at hx ⊢
  intro j
  rw [Set.mem_iInter]
  intro hj
  have hxj := Set.mem_iInter.mp (hx j) hj
  obtain ⟨I, hI, hxI⟩ := Set.mem_iUnion₂.mp hxj
  exact Set.mem_biUnion (pruneTree_atoms_subset hI0 hchild_mem j hj hI) hxI

end Prune

#print axioms WindowTreePrune.isClosed_levelUnion
#print axioms WindowTreePrune.isCompact_cantorSet
#print axioms WindowTreePrune.desc_mem_from
#print axioms WindowTreePrune.desc_card_le_from
#print axioms WindowTreePrune.exists_ancestor_desc
#print axioms WindowTreePrune.exists_mem_cantorSet_of_mem_atoms
#print axioms WindowTreePrune.cantorSet_nonempty
#print axioms WindowTreePrune.atoms_card_le_sum_meet_desc
#print axioms WindowTreePrune.pruneChild_subset
#print axioms WindowTreePrune.pruneChild_card
#print axioms WindowTreePrune.pruneTree_atoms_base
#print axioms WindowTreePrune.pruneTree_atoms_succ
#print axioms WindowTreePrune.pruneTree_atoms_subset
#print axioms WindowTreePrune.pruneTree_child_mem
#print axioms WindowTreePrune.pruneTree_mem_parent
#print axioms WindowTreePrune.pruneTree_child_card
#print axioms WindowTreePrune.pruneTree_atoms_card
#print axioms WindowTreePrune.cantorSet_pruneTree_subset

end WindowTreePrune
