import EpiFormal.WindowFrostmanDirect
import EpiFormal.WindowTreePrune
import EpiFormal.WindowAsympThresh
import EpiFormal.WindowMuLevel
import EpiFormal.WindowMassDist
import EpiFormal.WindowMassFull
import EpiFormal.WindowPointMass
import EpiFormal.WindowStoppedUniform

/-!
# L05 Frostman discharge & unified windows / no-short-dim dimension assembly

Closes the L05 gap from `WindowFrostmanDirect.frostman_of_window_layer` and the
`hCbig` / small-window cascade interfaces from `WindowMassFull.mu_window_le_full`,
for arbitrary scale-free length constants `[d0_c / H_j², L_c / H_j²]` and arbitrary
real branching exponent `b : ℝ` (covering `b = 2`, `b = 1` in `thm:windows`, and
`b = 2γ = 2(1 - η log φ)` in `thm:no-short-dim`):

1. `frostman_of_uniform_tree`: discharges `Hwin` in
   `WindowFrostDirect.frostman_of_window_layer` via `WindowSandwich` (level
   selection), `WindowMuLevel.filter_meet_card` (overlap), and
   `WindowTreePrune.atoms_card_le_sum_meet_desc` (`Hcount` double counting).
2. `frostman_of_stopped_tree_rpow` & `dimH_ge_of_stopped_tree_rpow`: handles
   arbitrary non-uniform stopped trees with real branching exponent `b : ℝ`
   via `WindowTreePrune.pruneTree` and `WindowAsympThresh.asymp_thresh_exists_rpow`,
   yielding `ENNReal.ofReal (min 1 (b / 2)) ≤ dimH (cantorSet T j0)`.
3. `dimH_ge_one_of_coprime_tree` (`thm:windows`, `WindowMobiusCount.coprime_count_ge`)
   and `dimH_ge_gamma_of_coprimeS_tree` (`thm:no-short-dim`,
   `NoShortDim.coprimeS_count_ge`).
4. `mass_distrib_of_local_diam_bound` (local-scale Frostman lemma, immune to
   the R1 `V = univ` defect), `mu_singleton_zero_of_support` (non-vacuous
   singleton vanishing for measures supported on `cantorSet T j0`), and
   `mu_window_cascade_full` (discharging `hCbig` + arbitrarily small-window
   cascades on all bounded `U : Set ℝ`).

Only Lean core axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace WindowFrostmanDischarge

open MeasureTheory Set Filter Finset ENNReal Metric Real
open scoped NNReal BigOperators Topology MeasureTheory

/-! ### Part 1: Direct `Hwin` discharge for uniform-branching stopped trees -/

set_option maxHeartbeats 800000 in
-- Required by the multi-step Frostman Hwin discharge (`sandwich` + `Hcount` + `Hthresh`).
/-- L05 core discharge: for a uniform-branching stopped tree satisfying an
    asymptotic per-level threshold from `J1 ≥ j0`, discharges `Hwin` in
    `WindowFrostDirect.frostman_of_window_layer` to yield `1 ≤ μH[s] (cantorSet T j0)`. -/
theorem frostman_of_uniform_tree
    {T : StoppedTree.TreeData} {j0 J1 : ℕ} (hJ1 : j0 ≤ J1)
    {B : ℕ → ℕ} (hB1 : ∀ j ≥ j0, 1 ≤ B j)
    {H d0 L : ℕ → ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hne0 : (T.atoms j0).Nonempty)
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 < I.2)
    (hlen_lo : ∀ j ≥ j0, ∀ I ∈ T.atoms j, d0 j ≤ I.2 - I.1)
    (hlen_hi : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.2 - I.1 ≤ L j)
    (hdisj : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ J ∈ T.atoms j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_card : ∀ j ≥ j0, ∀ u ∈ T.atoms j, (T.child j u).card = B j)
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2)
    (hmem : ∀ j ≥ j0, ∀ t ∈ T.atoms (j + 1), ∃ u ∈ T.atoms j, t ∈ T.child j u)
    (hatoms_card : ∀ j ≥ j0, (T.atoms j).card = ∏ k ∈ Finset.Ico j0 j, B k)
    (hd0j : ∀ j ≥ j0, 0 < d0 j) (hLj : ∀ j ≥ j0, 0 ≤ L j)
    (hHpos : ∀ j, 0 < H j)
    (hHlim : Filter.Tendsto (fun j => 1 / (H j) ^ 2) Filter.atTop (nhds 0))
    (hthresh : ∀ j ≥ J1, ∀ h' : ℝ,
      h' ∈ Set.Icc (1 / (H (j + 1)) ^ 2) (1 / (H j) ^ 2) →
      ((2 * h' + 3 * L j) / d0 j + 2) / (∏ k ∈ Finset.Ico j0 j, (B k : ℝ)) ≤ h' ^ s) :
    1 ≤ MeasureTheory.Measure.hausdorffMeasure s (WindowTreePrune.cantorSet T j0) := by
  classical
  have htriv_le : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 ≤ I.2 :=
    fun j hj I hI => le_of_lt (htriv j hj I hI)
  have hchild_ne : ∀ j ≥ j0, ∀ u ∈ T.atoms j, (T.child j u).Nonempty := by
    intro j hj u hu
    rw [← Finset.card_pos, hchild_card j hj u hu]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (hB1 j hj)
  have hK : IsCompact (WindowTreePrune.cantorSet T j0) :=
    WindowTreePrune.isCompact_cantorSet T j0
  have hKne : (WindowTreePrune.cantorSet T j0).Nonempty :=
    WindowTreePrune.cantorSet_nonempty hne0 htriv_le hchild_mem hchild_ne hnest hmem
  let r0R : ℝ := (1 / (H J1) ^ 2) / 2
  have hr0R : 0 < r0R := by
    have := hHpos J1
    positivity
  let Q : ℕ → ℝ := fun j => (H j) ^ 2
  let M : ℕ → ℝ := fun j => ∏ k ∈ Finset.Ico j0 j, (B k : ℝ)
  have hMpos : ∀ j ≥ j0, 0 < M j := by
    intro j _
    apply Finset.prod_pos
    intro k hk
    have hk1 : 1 ≤ B k := hB1 k (Finset.mem_Ico.mp hk).1
    have : (1 : ℝ) ≤ (B k : ℝ) := by exact_mod_cast hk1
    linarith
  refine WindowFrostDirect.frostman_of_window_layer hs0 hs1 hK hKne r0R hr0R Q M J1 ?_
  intro ι V F _hopen hcov hbdd hpos _hFne htop
  have hsand : ∀ i : ι, (V i).Nonempty →
      ∃ j, J1 ≤ j ∧ 1 / (H (j + 1)) ^ 2 ≤ Metric.diam (V i) ∧
        Metric.diam (V i) ≤ 1 / (H j) ^ 2 := by
    intro i hne
    have hdiam_le : Metric.diam (V i) ≤ 1 / (H J1) ^ 2 := by
      have h1 := htop i
      have h2 : 2 * r0R = 1 / (H J1) ^ 2 := by dsimp only [r0R]; ring
      linarith
    exact WindowSandwich.sandwich_of_tendsto H hHlim J1 (hpos i hne) hdiam_le
  let lvl : ι → ℕ := fun i =>
    if h : (V i).Nonempty then Classical.choose (hsand i h) else J1
  let Kc : ι → ℕ := fun i =>
    ((T.atoms (lvl i)).filter (fun (u : ℝ × ℝ) => (Set.Icc u.1 u.2 ∩ V i).Nonempty)).card
  have hlvl_ge_J1 : ∀ i, J1 ≤ lvl i := by
    intro i
    simp only [lvl]
    split_ifs with h
    · exact (Classical.choose_spec (hsand i h)).1
    · exact le_rfl
  refine ⟨lvl, Kc, ?_, ?_, ?_⟩
  · -- (1) Layer condition h_layer.
    intro i _ hne
    have hspec := Classical.choose_spec (hsand i hne)
    have hlvl_eq : lvl i = Classical.choose (hsand i hne) := by simp only [lvl, hne, ↓reduceDIte]
    rw [hlvl_eq]
    refine ⟨hspec.1, ?_⟩
    simpa [Q, one_div] using hspec.2.1
  · -- (2) Global double counting Hcount.
    let N : ℕ := max J1 (F.sup lvl)
    have hN_J1 : J1 ≤ N := le_max_left _ _
    have hN_j0 : j0 ≤ N := le_trans hJ1 hN_J1
    have hlvl_lo : ∀ i ∈ F, j0 ≤ lvl i := fun i _ => le_trans hJ1 (hlvl_ge_J1 i)
    have hlvl_hi : ∀ i ∈ F, lvl i ≤ N := fun i hi =>
      le_trans (Finset.le_sup hi) (le_max_right _ _)
    have hcard_nat := WindowTreePrune.atoms_card_le_sum_meet_desc
      htriv_le hchild_mem hchild_ne hnest hmem
      (fun j hj v hv => le_of_eq (hchild_card j hj v hv))
      V F hcov lvl hlvl_lo hlvl_hi hN_j0
    rw [hatoms_card N hN_j0] at hcard_nat
    have hcard_real : M N ≤ ∑ i ∈ F, (Kc i : ℝ) * ∏ k ∈ Finset.Ico (lvl i) N, (B k : ℝ) := by
      have hcast : ((∏ k ∈ Finset.Ico j0 N, B k : ℕ) : ℝ) ≤
          ((∑ i ∈ F, Kc i * ∏ k ∈ Finset.Ico (lvl i) N, B k : ℕ) : ℝ) := by
        exact_mod_cast hcard_nat
      simpa only [M, Nat.cast_prod, Nat.cast_sum, Nat.cast_mul] using hcast
    have hMNpos : 0 < M N := hMpos N hN_j0
    have hdiv := div_le_div_of_nonneg_right hcard_real (le_of_lt hMNpos)
    rw [div_self (ne_of_gt hMNpos), Finset.sum_div] at hdiv
    refine le_trans hdiv (le_of_eq (Finset.sum_congr rfl fun i hi => ?_))
    have hsplit : M (lvl i) * ∏ k ∈ Finset.Ico (lvl i) N, (B k : ℝ) = M N := by
      simp only [M]
      exact Finset.prod_Ico_consecutive (fun k => (B k : ℝ)) (hlvl_lo i hi) (hlvl_hi i hi)
    have htail_pos : 0 < ∏ k ∈ Finset.Ico (lvl i) N, (B k : ℝ) := by
      apply Finset.prod_pos
      intro k hk
      have hk1 : 1 ≤ B k := hB1 k (le_trans (hlvl_lo i hi) (Finset.mem_Ico.mp hk).1)
      have : (1 : ℝ) ≤ (B k : ℝ) := by exact_mod_cast hk1
      linarith
    have htail_ne : (∏ k ∈ Finset.Ico (lvl i) N, (B k : ℝ)) ≠ 0 := ne_of_gt htail_pos
    rw [← hsplit, mul_div_mul_right _ _ htail_ne]
  · -- (3) Per-window threshold Hthresh.
    intro i _
    by_cases hne : (V i).Nonempty
    · have hspec := Classical.choose_spec (hsand i hne)
      have hlvl_eq : lvl i = Classical.choose (hsand i hne) := by simp only [lvl, hne, ↓reduceDIte]
      have hjJ1 : J1 ≤ lvl i := by rw [hlvl_eq]; exact hspec.1
      have hjj0 : j0 ≤ lvl i := le_trans hJ1 hjJ1
      have hmem_Icc : Metric.diam (V i) ∈
          Set.Icc (1 / (H (lvl i + 1)) ^ 2) (1 / (H (lvl i)) ^ 2) := by
        rw [hlvl_eq]
        exact ⟨hspec.2.1, hspec.2.2⟩
      have hKc_le : (Kc i : ℝ) ≤
          (2 * Metric.diam (V i) + 3 * L (lvl i)) / d0 (lvl i) + 2 :=
        WindowMuLevel.filter_meet_card (hd0j (lvl i) hjj0) (hLj (lvl i) hjj0)
          Metric.diam_nonneg (T.atoms (lvl i))
          (htriv (lvl i) hjj0) (hlen_lo (lvl i) hjj0) (hlen_hi (lvl i) hjj0)
          (hdisj (lvl i) hjj0) (V i) (hbdd i) le_rfl
      have hMpos_i : 0 < M (lvl i) := hMpos (lvl i) hjj0
      calc ((Kc i : ℝ) / M (lvl i))
          ≤ ((2 * Metric.diam (V i) + 3 * L (lvl i)) / d0 (lvl i) + 2) / M (lvl i) :=
            div_le_div_of_nonneg_right hKc_le (le_of_lt hMpos_i)
        _ ≤ (Metric.diam (V i)) ^ s :=
            hthresh (lvl i) hjJ1 (Metric.diam (V i)) hmem_Icc
    · have hempty : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hKc0 : Kc i = 0 := by
        simp only [Kc, hempty, Set.inter_empty, Set.not_nonempty_empty, Finset.filter_false,
          Finset.card_empty]
      rw [hKc0, Nat.cast_zero, zero_div]
      exact Real.rpow_nonneg Metric.diam_nonneg s

/-! ### Part 2: Non-uniform stopped tree with real exponent `b : ℝ` & general length bounds -/

/-- General L05 Frostman measure lower bound for non-uniform stopped trees
    with real branching exponent `B i ≥ c * i^b` and length constants
    `[d0_c / H_j², L_c / H_j²]`. -/
theorem frostman_of_stopped_tree_rpow
    {T : StoppedTree.TreeData} {j0 : ℕ} (hj0 : 1 ≤ j0)
    {B : ℕ → ℕ} (hB1 : ∀ j ≥ j0, 1 ≤ B j)
    {b c d0_c L_c C_H s : ℝ}
    (hc : 0 < c) (hd0c : 0 < d0_c) (hLc : 0 ≤ L_c)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hsb : s < b / 2)
    (hbranch : ∀ i ≥ j0, c * (i : ℝ) ^ b ≤ (B i : ℝ))
    {H : ℕ → ℝ} (hHpos : ∀ j, 0 < H j)
    (hHlim : Filter.Tendsto (fun j => 1 / (H j) ^ 2) Filter.atTop (nhds 0))
    (hHlog : ∀ j ≥ j0,
      Real.log (H (j + 1)) ≤ (j : ℝ) * Real.log (j : ℝ) + C_H * (j : ℝ))
    (hne0 : (T.atoms j0).Nonempty)
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 < I.2)
    (hlen : ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      d0_c / (H j) ^ 2 ≤ I.2 - I.1 ∧ I.2 - I.1 ≤ L_c / (H j) ^ 2)
    (hdisj : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ J ∈ T.atoms j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_card : ∀ j ≥ j0, ∀ u ∈ T.atoms j, B j ≤ (T.child j u).card)
    (hdisj_child : ∀ j ≥ j0, ∀ u₁ ∈ T.atoms j, ∀ u₂ ∈ T.atoms j, u₁ ≠ u₂ →
      Disjoint (T.child j u₁) (T.child j u₂))
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2) :
    1 ≤ MeasureTheory.Measure.hausdorffMeasure s (WindowTreePrune.cantorSet T j0) := by
  obtain ⟨I0, hI0⟩ := hne0
  let T' := WindowTreePrune.pruneTree T B j0 I0
  let BR : ℕ → ℝ := fun i => if j0 ≤ i then (B i : ℝ) else 1
  have hBRpos : ∀ i, 0 < BR i := by
    intro i
    simp only [BR]
    split_ifs with hi
    · have : (1 : ℝ) ≤ (B i : ℝ) := by exact_mod_cast hB1 i hi
      linarith
    · norm_num
  have hBR_branch : ∀ i ≥ j0, c * (i : ℝ) ^ b ≤ BR i := by
    intro i hi
    simp only [BR, hi, ↓reduceIte]
    exact hbranch i hi
  let K0 : ℝ := (2 + 3 * L_c) / d0_c + 2
  have hK0pos : 0 < K0 := by
    dsimp only [K0]
    have hdiv : 0 ≤ (2 + 3 * L_c) / d0_c := div_nonneg (by linarith) (le_of_lt hd0c)
    linarith
  obtain ⟨J1, hJ1, hJ1_thresh⟩ := WindowAsympThresh.asymp_thresh_exists_rpow
    j0 hj0 b c s K0 C_H hc hs0 hsb hK0pos BR H hBRpos hBR_branch hHpos hHlog
  have hsub_atoms := WindowTreePrune.pruneTree_atoms_subset (B := B) hI0 hchild_mem
  have hmu_pruned :
      1 ≤ MeasureTheory.Measure.hausdorffMeasure s (WindowTreePrune.cantorSet T' j0) := by
    refine frostman_of_uniform_tree hJ1 hB1 hs0 hs1
      (by rw [WindowTreePrune.pruneTree_atoms_base]; exact Finset.singleton_nonempty I0)
      (fun j hj I hI => htriv j hj I (hsub_atoms j hj hI))
      (fun j hj I hI => (hlen j hj I (hsub_atoms j hj hI)).1)
      (fun j hj I hI => (hlen j hj I (hsub_atoms j hj hI)).2)
      (fun j hj I hI J hJ hne =>
        hdisj j hj I (hsub_atoms j hj hI) J (hsub_atoms j hj hJ) hne)
      (WindowTreePrune.pruneTree_child_mem T B j0 I0)
      (WindowTreePrune.pruneTree_child_card hI0 hchild_mem hchild_card)
      (fun j hj u hu c hc =>
        hnest j hj u (hsub_atoms j hj hu) c (WindowTreePrune.pruneChild_subset T B j u hc))
      (WindowTreePrune.pruneTree_mem_parent T B j0 I0)
      (WindowTreePrune.pruneTree_atoms_card hI0 hchild_mem hchild_card hdisj_child)
      (fun j _ => by have := hHpos j; positivity)
      (fun j _ => by have := hHpos j; positivity)
      hHpos hHlim ?_
    intro j hj h' hh'
    have hprod_eq : ∏ k ∈ Finset.Ico j0 j, BR k = ∏ k ∈ Finset.Ico j0 j, (B k : ℝ) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hk_ge : j0 ≤ k := (Finset.mem_Ico.mp hk).1
      simp only [BR, hk_ge, ↓reduceIte]
    have hprod_pos : 0 < ∏ k ∈ Finset.Ico j0 j, (B k : ℝ) := by
      apply Finset.prod_pos
      intro k hk
      have : (1 : ℝ) ≤ (B k : ℝ) := by exact_mod_cast hB1 k (Finset.mem_Ico.mp hk).1
      linarith
    have hov := WindowAsympThresh.general_overlap_const (L_c := L_c) (hHpos j) hd0c hh'.2
    have hth := hJ1_thresh j hj h' hh'.1
    rw [hprod_eq] at hth
    calc ((2 * h' + 3 * (L_c / (H j) ^ 2)) / (d0_c / (H j) ^ 2) + 2) /
          (∏ k ∈ Finset.Ico j0 j, (B k : ℝ))
        ≤ K0 / (∏ k ∈ Finset.Ico j0 j, (B k : ℝ)) :=
          div_le_div_of_nonneg_right hov (le_of_lt hprod_pos)
      _ ≤ h' ^ s := hth
  exact le_trans hmu_pruned
    (MeasureTheory.measure_mono (WindowTreePrune.cantorSet_pruneTree_subset hI0 hchild_mem))

/-- Hausdorff dimension lower bound for arbitrary real branching exponent `b : ℝ`
    and general stopped-cylinder length constants `[d0_c / H_j², L_c / H_j²]`:
    `min 1 (b / 2) ≤ dimH (cantorSet T j0)`. -/
theorem dimH_ge_of_stopped_tree_rpow
    {T : StoppedTree.TreeData} {j0 : ℕ} (hj0 : 1 ≤ j0)
    {B : ℕ → ℕ} (hB1 : ∀ j ≥ j0, 1 ≤ B j)
    {b c d0_c L_c C_H : ℝ} (hc : 0 < c) (hd0c : 0 < d0_c) (hLc : 0 ≤ L_c)
    (hbranch : ∀ i ≥ j0, c * (i : ℝ) ^ b ≤ (B i : ℝ))
    {H : ℕ → ℝ} (hHpos : ∀ j, 0 < H j)
    (hHlim : Filter.Tendsto (fun j => 1 / (H j) ^ 2) Filter.atTop (nhds 0))
    (hHlog : ∀ j ≥ j0,
      Real.log (H (j + 1)) ≤ (j : ℝ) * Real.log (j : ℝ) + C_H * (j : ℝ))
    (hne0 : (T.atoms j0).Nonempty)
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 < I.2)
    (hlen : ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      d0_c / (H j) ^ 2 ≤ I.2 - I.1 ∧ I.2 - I.1 ≤ L_c / (H j) ^ 2)
    (hdisj : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ J ∈ T.atoms j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_card : ∀ j ≥ j0, ∀ u ∈ T.atoms j, B j ≤ (T.child j u).card)
    (hdisj_child : ∀ j ≥ j0, ∀ u₁ ∈ T.atoms j, ∀ u₂ ∈ T.atoms j, u₁ ≠ u₂ →
      Disjoint (T.child j u₁) (T.child j u₂))
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2) :
    ENNReal.ofReal (min 1 (b / 2)) ≤ dimH (WindowTreePrune.cantorSet T j0) := by
  by_cases hb0 : b ≤ 0
  · have hmin : min (1 : ℝ) (b / 2) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
    rw [ENNReal.ofReal_eq_zero.mpr hmin]
    exact bot_le
  · push Not at hb0
    set t : ℝ := min 1 (b / 2)
    have ht_pos : 0 < t := lt_min zero_lt_one (by linarith)
    have hs_le : ∀ s : ℝ, 0 < s → s < t →
        ENNReal.ofReal s ≤ dimH (WindowTreePrune.cantorSet T j0) := by
      intro s hs0 hst
      have hs1 : s ≤ 1 := le_of_lt (lt_of_lt_of_le hst (min_le_left _ _))
      have hsb : s < b / 2 := lt_of_lt_of_le hst (min_le_right _ _)
      have hmu : 1 ≤ μH[s] (WindowTreePrune.cantorSet T j0) :=
        frostman_of_stopped_tree_rpow hj0 hB1 hc hd0c hLc hs0 hs1 hsb hbranch
          hHpos hHlim hHlog hne0 htriv hlen hdisj hchild_mem hchild_card hdisj_child hnest
      have hmu_ne : μH[s] (WindowTreePrune.cantorSet T j0) ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hmu)
      set d : ℝ≥0 := ⟨s, le_of_lt hs0⟩
      have hdim : (d : ℝ≥0∞) ≤ dimH (WindowTreePrune.cantorSet T j0) :=
        le_dimH_of_hausdorffMeasure_ne_zero hmu_ne
      have hd_eq : (d : ℝ≥0∞) = ENNReal.ofReal s := by
        simp only [d, ENNReal.ofReal]
        congr 1
        exact (Real.toNNReal_of_nonneg (le_of_lt hs0)).symm
      rwa [hd_eq] at hdim
    apply le_of_forall_lt
    intro r hr
    by_cases hr0 : r = 0
    · subst hr0
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (half_pos ht_pos))
        (hs_le (t / 2) (half_pos ht_pos) (half_lt_self ht_pos))
    · have hr_ne_top : r ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hr (le_of_lt ENNReal.ofReal_lt_top))
      have hr_lt_t : r.toReal < t := by
        have h1 := (ENNReal.toReal_lt_toReal hr_ne_top ENNReal.ofReal_ne_top).mpr hr
        rwa [ENNReal.toReal_ofReal (le_of_lt ht_pos)] at h1
      set s : ℝ := (r.toReal + t) / 2
      have hr_lt_s : r.toReal < s := by dsimp only [s]; linarith
      have hs_lt_t : s < t := by dsimp only [s]; linarith
      have hs0 : 0 < s := lt_of_le_of_lt ENNReal.toReal_nonneg hr_lt_s
      have hlt : r < ENNReal.ofReal s := by
        rw [← ENNReal.ofReal_toReal hr_ne_top]
        exact (ENNReal.ofReal_lt_ofReal_iff hs0).mpr hr_lt_s
      exact lt_of_lt_of_le hlt (hs_le s hs0 hs_lt_t)

/-- Flagship windows dimension assembly (`thm:windows`, `b = 2`): plugs the verified
    Möbius coprime count `WindowMobiusCount.coprime_count_ge` directly into
    `dimH_ge_of_stopped_tree_rpow` with parent-dependent scale `R j u` (matching
    Paper 2 L2446 `R = H_{j+1} / u`) and general length constants `[d0_c / H², L_c / H²]`. -/
theorem dimH_ge_one_of_coprime_tree
    {T : StoppedTree.TreeData} {j0 : ℕ} (hj0 : 1 ≤ j0)
    {R : ℕ → (ℝ × ℝ) → ℝ} {H : ℕ → ℝ} {c_R d0_c L_c C_H : ℝ}
    (hcR : 0 < c_R) (hd0c : 0 < d0_c) (hLc : 0 ≤ L_c)
    (hR106 : ∀ i ≥ j0, ∀ u ∈ T.atoms i, (10 ^ 6 : ℝ) ≤ R i u)
    (hRlin : ∀ i ≥ j0, ∀ u ∈ T.atoms i, c_R * (i : ℝ) ≤ R i u)
    (hHpos : ∀ j, 0 < H j)
    (hHlim : Filter.Tendsto (fun j => 1 / (H j) ^ 2) Filter.atTop (nhds 0))
    (hHlog : ∀ j ≥ j0,
      Real.log (H (j + 1)) ≤ (j : ℝ) * Real.log (j : ℝ) + C_H * (j : ℝ))
    (hne0 : (T.atoms j0).Nonempty)
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 < I.2)
    (hlen : ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      d0_c / (H j) ^ 2 ≤ I.2 - I.1 ∧ I.2 - I.1 ≤ L_c / (H j) ^ 2)
    (hdisj : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ J ∈ T.atoms j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_cop : ∀ j ≥ j0, ∀ u ∈ T.atoms j,
      WindowMobiusCount.copCount (R j u) ≤ (T.child j u).card)
    (hdisj_child : ∀ j ≥ j0, ∀ u₁ ∈ T.atoms j, ∀ u₂ ∈ T.atoms j, u₁ ≠ u₂ →
      Disjoint (T.child j u₁) (T.child j u₂))
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2) :
    (1 : ℝ≥0∞) ≤ dimH (WindowTreePrune.cantorSet T j0) := by
  let x : ℕ → ℝ := fun i => (max (10 ^ 6 : ℝ) (c_R * (i : ℝ))) ^ 2 / 10000
  let B : ℕ → ℕ := fun i => Nat.floor (x i)
  have hx_ge : ∀ i, (2 : ℝ) ≤ x i := by
    intro i
    dsimp only [x]
    have hmax : (10 ^ 6 : ℝ) ≤ max (10 ^ 6 : ℝ) (c_R * (i : ℝ)) := le_max_left _ _
    have hsq : ((10 ^ 6 : ℝ)) ^ 2 ≤ (max (10 ^ 6 : ℝ) (c_R * (i : ℝ))) ^ 2 := by nlinarith
    have hdiv : ((10 ^ 6 : ℝ)) ^ 2 / 10000 ≤ (max (10 ^ 6 : ℝ) (c_R * (i : ℝ))) ^ 2 / 10000 :=
      div_le_div_of_nonneg_right hsq (by norm_num)
    linarith
  have hB1 : ∀ j ≥ j0, 1 ≤ B j := by
    intro j _
    exact Nat.le_floor (by push_cast; linarith [hx_ge j])
  have hbranch : ∀ i ≥ j0, (c_R ^ 2 / 20000) * (i : ℝ) ^ (2 : ℝ) ≤ (B i : ℝ) := by
    intro i _
    have hfl : x i - 1 < (B i : ℝ) := by
      have := Nat.lt_floor_add_one (x i)
      linarith
    have hhalf : x i / 2 ≤ x i - 1 := by linarith [hx_ge i]
    have hci : c_R * (i : ℝ) ≤ max (10 ^ 6 : ℝ) (c_R * (i : ℝ)) := le_max_right _ _
    have hci_nn : 0 ≤ c_R * (i : ℝ) := mul_nonneg (le_of_lt hcR) (Nat.cast_nonneg i)
    have hsq : (c_R * (i : ℝ)) ^ 2 ≤ (max (10 ^ 6 : ℝ) (c_R * (i : ℝ))) ^ 2 := by nlinarith
    have hpow : (c_R ^ 2 / 20000) * (i : ℝ) ^ (2 : ℝ) = (c_R * (i : ℝ)) ^ 2 / 20000 := by
      rw [Real.rpow_two]; ring
    have hdiv : (c_R * (i : ℝ)) ^ 2 / 20000 ≤ x i / 2 := by
      have h1 : (c_R * (i : ℝ)) ^ 2 / 20000 ≤ (max (10 ^ 6 : ℝ) (c_R * (i : ℝ))) ^ 2 / 20000 :=
        div_le_div_of_nonneg_right hsq (by norm_num)
      have h2 : x i / 2 = (max (10 ^ 6 : ℝ) (c_R * (i : ℝ))) ^ 2 / 20000 := by
        dsimp only [x]; ring
      linarith
    rw [hpow]
    linarith
  have hchild_B : ∀ j ≥ j0, ∀ u ∈ T.atoms j, B j ≤ (T.child j u).card := by
    intro j hj u hu
    have hmax_le : max (10 ^ 6 : ℝ) (c_R * (j : ℝ)) ≤ R j u :=
      max_le (hR106 j hj u hu) (hRlin j hj u hu)
    have hmax_nn : 0 ≤ max (10 ^ 6 : ℝ) (c_R * (j : ℝ)) :=
      le_trans (by norm_num) (le_max_left _ _)
    have hsq : (max (10 ^ 6 : ℝ) (c_R * (j : ℝ))) ^ 2 ≤ (R j u) ^ 2 := by nlinarith
    have hx_le : x j ≤ ((WindowMobiusCount.copCount (R j u) : ℕ) : ℝ) := by
      have hge := WindowMobiusCount.coprime_count_ge (R j u) (hR106 j hj u hu)
      have hdiv : x j ≤ (R j u) ^ 2 / 10000 := div_le_div_of_nonneg_right hsq (by norm_num)
      exact le_trans hdiv hge
    exact le_trans (Nat.floor_le_of_le hx_le) (hchild_cop j hj u hu)
  have hc : 0 < c_R ^ 2 / 20000 := by positivity
  have hdim := dimH_ge_of_stopped_tree_rpow (b := (2 : ℝ)) (B := B)
    hj0 hB1 hc hd0c hLc hbranch
    hHpos hHlim hHlog hne0 htriv hlen hdisj hchild_mem hchild_B hdisj_child hnest
  have hmin : ENNReal.ofReal (min (1 : ℝ) ((2 : ℝ) / 2)) = 1 := by
    have : min (1 : ℝ) ((2 : ℝ) / 2) = 1 := by norm_num
    rw [this, ENNReal.ofReal_one]
  rwa [hmin] at hdim

/-- No-short-windows dimension assembly (`thm:no-short-dim`): plugs the verified
    short-rectangle Möbius count `NoShortDim.coprimeS_count_ge` directly into
    `dimH_ge_of_stopped_tree_rpow` with parent-dependent scale `R j u` (matching
    Paper 2 L2769 `R = H_{j+1} / u'`) and `b = 2γ`, yielding `min 1 γ ≤ dimH`. -/
theorem dimH_ge_gamma_of_coprimeS_tree
    {T : StoppedTree.TreeData} {j0 : ℕ} (hj0 : 1 ≤ j0)
    {R : ℕ → (ℝ × ℝ) → ℝ} {H : ℕ → ℝ} {c_R γ d0_c L_c C_H : ℝ}
    (hcR : 0 < c_R) (hd0c : 0 < d0_c) (hLc : 0 ≤ L_c)
    (hR106 : ∀ i ≥ j0, ∀ u ∈ T.atoms i, (10 ^ 6 : ℝ) ≤ R i u)
    (hRpow : ∀ i ≥ j0, ∀ u ∈ T.atoms i, c_R * (i : ℝ) ^ γ ≤ R i u)
    (hHpos : ∀ j, 0 < H j)
    (hHlim : Filter.Tendsto (fun j => 1 / (H j) ^ 2) Filter.atTop (nhds 0))
    (hHlog : ∀ j ≥ j0,
      Real.log (H (j + 1)) ≤ (j : ℝ) * Real.log (j : ℝ) + C_H * (j : ℝ))
    (hne0 : (T.atoms j0).Nonempty)
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 < I.2)
    (hlen : ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      d0_c / (H j) ^ 2 ≤ I.2 - I.1 ∧ I.2 - I.1 ≤ L_c / (H j) ^ 2)
    (hdisj : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ J ∈ T.atoms j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_cop : ∀ j ≥ j0, ∀ u ∈ T.atoms j,
      NoShortDim.copCountS (R j u) ≤ (T.child j u).card)
    (hdisj_child : ∀ j ≥ j0, ∀ u₁ ∈ T.atoms j, ∀ u₂ ∈ T.atoms j, u₁ ≠ u₂ →
      Disjoint (T.child j u₁) (T.child j u₂))
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2) :
    ENNReal.ofReal (min 1 γ) ≤ dimH (WindowTreePrune.cantorSet T j0) := by
  let x : ℕ → ℝ := fun i => (max (10 ^ 6 : ℝ) (c_R * (i : ℝ) ^ γ)) ^ 2 / 100000
  let B : ℕ → ℕ := fun i => Nat.floor (x i)
  have hx_ge : ∀ i, (2 : ℝ) ≤ x i := by
    intro i
    dsimp only [x]
    have hmax : (10 ^ 6 : ℝ) ≤ max (10 ^ 6 : ℝ) (c_R * (i : ℝ) ^ γ) := le_max_left _ _
    have hsq : ((10 ^ 6 : ℝ)) ^ 2 ≤ (max (10 ^ 6 : ℝ) (c_R * (i : ℝ) ^ γ)) ^ 2 := by nlinarith
    have hdiv : ((10 ^ 6 : ℝ)) ^ 2 / 100000 ≤
        (max (10 ^ 6 : ℝ) (c_R * (i : ℝ) ^ γ)) ^ 2 / 100000 :=
      div_le_div_of_nonneg_right hsq (by norm_num)
    linarith
  have hB1 : ∀ j ≥ j0, 1 ≤ B j := by
    intro j _
    exact Nat.le_floor (by push_cast; linarith [hx_ge j])
  have hbranch : ∀ i ≥ j0, (c_R ^ 2 / 200000) * (i : ℝ) ^ (2 * γ) ≤ (B i : ℝ) := by
    intro i _
    have hfl : x i - 1 < (B i : ℝ) := by
      have := Nat.lt_floor_add_one (x i)
      linarith
    have hhalf : x i / 2 ≤ x i - 1 := by linarith [hx_ge i]
    have hci : c_R * (i : ℝ) ^ γ ≤ max (10 ^ 6 : ℝ) (c_R * (i : ℝ) ^ γ) := le_max_right _ _
    have hci_nn : 0 ≤ c_R * (i : ℝ) ^ γ :=
      mul_nonneg (le_of_lt hcR) (Real.rpow_nonneg (Nat.cast_nonneg i) γ)
    have hsq : (c_R * (i : ℝ) ^ γ) ^ 2 ≤ (max (10 ^ 6 : ℝ) (c_R * (i : ℝ) ^ γ)) ^ 2 := by nlinarith
    have hpow2 : ((i : ℝ) ^ γ) ^ 2 = (i : ℝ) ^ (2 * γ) := by
      rw [← Real.rpow_natCast ((i : ℝ) ^ γ) 2, ← Real.rpow_mul (Nat.cast_nonneg i)]
      congr 1
      ring
    have hpow : (c_R ^ 2 / 200000) * (i : ℝ) ^ (2 * γ) = (c_R * (i : ℝ) ^ γ) ^ 2 / 200000 := by
      rw [mul_pow, hpow2]; ring
    have hdiv : (c_R * (i : ℝ) ^ γ) ^ 2 / 200000 ≤ x i / 2 := by
      have h1 : (c_R * (i : ℝ) ^ γ) ^ 2 / 200000 ≤
          (max (10 ^ 6 : ℝ) (c_R * (i : ℝ) ^ γ)) ^ 2 / 200000 :=
        div_le_div_of_nonneg_right hsq (by norm_num)
      have h2 : x i / 2 = (max (10 ^ 6 : ℝ) (c_R * (i : ℝ) ^ γ)) ^ 2 / 200000 := by
        dsimp only [x]; ring
      linarith
    linarith
  have hchild_B : ∀ j ≥ j0, ∀ u ∈ T.atoms j, B j ≤ (T.child j u).card := by
    intro j hj u hu
    have hmax_le : max (10 ^ 6 : ℝ) (c_R * (j : ℝ) ^ γ) ≤ R j u :=
      max_le (hR106 j hj u hu) (hRpow j hj u hu)
    have hmax_nn : 0 ≤ max (10 ^ 6 : ℝ) (c_R * (j : ℝ) ^ γ) :=
      le_trans (by norm_num) (le_max_left _ _)
    have hsq : (max (10 ^ 6 : ℝ) (c_R * (j : ℝ) ^ γ)) ^ 2 ≤ (R j u) ^ 2 := by nlinarith
    have hx_le : x j ≤ ((NoShortDim.copCountS (R j u) : ℕ) : ℝ) := by
      have hge := NoShortDim.coprimeS_count_ge (R j u) (hR106 j hj u hu)
      have hdiv : x j ≤ (R j u) ^ 2 / 100000 := div_le_div_of_nonneg_right hsq (by norm_num)
      exact le_trans hdiv hge
    exact le_trans (Nat.floor_le_of_le hx_le) (hchild_cop j hj u hu)
  have hc : 0 < c_R ^ 2 / 200000 := by positivity
  have hdim := dimH_ge_of_stopped_tree_rpow (b := 2 * γ) (B := B)
    hj0 hB1 hc hd0c hLc hbranch
    hHpos hHlim hHlog hne0 htriv hlen hdisj hchild_mem hchild_B hdisj_child hnest
  have h2g : (2 * γ) / 2 = γ := by ring
  rwa [h2g] at hdim

/-! ### Part 3: Local-scale mass distribution (R1 fix) + non-vacuous `hCbig` & cascade -/

/-- Local-scale mass distribution principle: restricts the Frostman hypothesis
    to sets with `ediam V ≤ ofReal r0R` (excluding `V = univ`, resolving R1) and
    yields the general Frostman inequality `μ K ≤ ofReal C * μH[s] K` (which
    composes directly with probability measures even when `C > 1`). -/
theorem mass_distrib_of_local_diam_bound {μ : Measure ℝ} {K : Set ℝ}
    {C s r0R : ℝ} (hC : 0 < C) (hs : 0 < s) (hr0R : 0 < r0R)
    (h : ∀ V : Set ℝ, Metric.ediam V ≤ ENNReal.ofReal r0R →
      μ V ≤ ENNReal.ofReal (C * (Metric.diam V) ^ s)) :
    μ K ≤ ENNReal.ofReal C * MeasureTheory.Measure.hausdorffMeasure s K := by
  set r0 : ℝ≥0∞ := ENNReal.ofReal r0R with hr0def
  have hr0 : 0 < r0 := by rw [hr0def]; exact ENNReal.ofReal_pos.mpr hr0R
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hCt : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv : (ENNReal.ofReal C)⁻¹ * μ K ≤ MeasureTheory.Measure.hausdorffMeasure s K := by
    rw [MeasureTheory.Measure.hausdorffMeasure_apply]
    refine le_trans ?_ (le_iSup₂ r0 hr0)
    apply le_iInf; intro t; apply le_iInf; intro hcov; apply le_iInf; intro hdiam
    have hsub : μ K ≤ ∑' n, μ (t n) := by
      have hle : μ.toOuterMeasure (⋃ n, t n) ≤ ∑' n, μ.toOuterMeasure (t n) :=
        MeasureTheory.measure_iUnion_le t
      have hle2 : μ (⋃ n, t n) ≤ ∑' n, μ (t n) := by
        simpa [MeasureTheory.Measure.toOuterMeasure_apply] using hle
      exact le_trans (measure_mono hcov) hle2
    have hterm : ∀ n, μ (t n) ≤ ENNReal.ofReal C * Metric.ediam (t n) ^ s := by
      intro n
      exact le_trans (h (t n) (hdiam n))
        (WindowMass.ofReal_diam_le_mul_ediam_rpow (le_of_lt hC) hs)
    have hCS : μ K ≤ ENNReal.ofReal C * ∑' n, Metric.ediam (t n) ^ s := by
      refine le_trans hsub ?_
      calc ∑' n, μ (t n)
          ≤ ∑' n, (ENNReal.ofReal C * Metric.ediam (t n) ^ s) := ENNReal.tsum_le_tsum hterm
        _ = ENNReal.ofReal C * ∑' n, Metric.ediam (t n) ^ s := ENNReal.tsum_mul_left
    have h2 : (ENNReal.ofReal C)⁻¹ * μ K ≤ ∑' n, Metric.ediam (t n) ^ s := by
      have h4 := mul_le_mul_of_nonneg_left hCS
        (show (0 : ℝ≥0∞) ≤ (ENNReal.ofReal C)⁻¹ by positivity)
      have h3 : ((ENNReal.ofReal C)⁻¹ * ENNReal.ofReal C) * ∑' n, Metric.ediam (t n) ^ s
          = (ENNReal.ofReal C)⁻¹ * (ENNReal.ofReal C * ∑' n, Metric.ediam (t n) ^ s) := by
        rw [mul_assoc]
      rw [← h3, ENNReal.inv_mul_cancel hC0 hCt, one_mul] at h4
      exact h4
    have hguard : ∀ n, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s)
        = Metric.ediam (t n) ^ s := by
      intro n
      by_cases hne : (t n).Nonempty
      · simp only [hne]; exact iSup_const
      · have hempty : t n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        rw [hempty, Metric.ediam_empty]
        have hz : ((0 : ℝ≥0∞) ^ s) = 0 := by
          rw [← ENNReal.ofReal_zero, ENNReal.ofReal_rpow_of_nonneg le_rfl hs.le,
            Real.zero_rpow (ne_of_gt hs), ENNReal.ofReal_zero]
        apply le_antisymm
        · apply iSup_le; intro _; exact le_rfl
        · rw [hz]; exact bot_le
    simpa only [hguard] using h2
  have hmul := mul_le_mul_of_nonneg_left hdiv (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal C by positivity)
  rwa [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCt, one_mul] at hmul

/-- Hausdorff dimension lower bound from a local-scale Frostman bound on a set of
    positive measure `0 < μ K`. -/
theorem dimH_ge_of_local_diam_bound {μ : Measure ℝ} {K : Set ℝ}
    {C s r0R : ℝ} (hC : 0 < C) (hs : 0 < s) (hr0R : 0 < r0R)
    (hKpos : 0 < μ K)
    (h : ∀ V : Set ℝ, Metric.ediam V ≤ ENNReal.ofReal r0R →
      μ V ≤ ENNReal.ofReal (C * (Metric.diam V) ^ s)) :
    ENNReal.ofReal s ≤ dimH K := by
  have hmu := mass_distrib_of_local_diam_bound (K := K) hC hs hr0R h
  have hmu_ne : μH[s] K ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmu
    exact not_lt_of_ge hmu hKpos
  set d : ℝ≥0 := ⟨s, le_of_lt hs⟩
  have hdim : (d : ℝ≥0∞) ≤ dimH K := le_dimH_of_hausdorffMeasure_ne_zero hmu_ne
  have hd_eq : (d : ℝ≥0∞) = ENNReal.ofReal s := by
    simp only [d, ENNReal.ofReal]
    congr 1
    exact (Real.toNNReal_of_nonneg (le_of_lt hs)).symm
  rwa [hd_eq] at hdim

/-- Non-vacuous singleton vanishing for a splitting measure supported on `cantorSet T j0`
    (`μ (cantorSet T j0)ᶜ = 0`; does NOT require finitely many atoms to cover all of `ℝ`). -/
theorem mu_singleton_zero_of_support
    {μ : Measure ℝ} {T : StoppedTree.TreeData} {m B : ℕ → ℝ} {j0 : ℕ}
    (hsupp : μ (WindowTreePrune.cantorSet T j0)ᶜ = 0)
    (hB2 : ∀ j ≥ j0, 2 ≤ B j) (hBpos : ∀ i, 0 < B i)
    (hm0 : ∀ I ∈ T.atoms j0, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m j0))
    (hm0nn : 0 ≤ m j0)
    (hmrec : ∀ j ≥ j0, m (j + 1) = m j / B j)
    (hsplit : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ C ∈ T.child j I,
      μ (Set.Icc C.1 C.2) ≤ μ (Set.Icc I.1 I.2) / ENNReal.ofReal (B j))
    (hmem : ∀ j ≥ j0, ∀ I ∈ T.atoms (j + 1), ∃ P ∈ T.atoms j, I ∈ T.child j P)
    (x : ℝ) :
    μ {x} = 0 := by
  by_cases hxK : x ∈ WindowTreePrune.cantorSet T j0
  · have hB1 : ∀ j ≥ j0, 1 ≤ B j := fun j hj => by linarith [hB2 j hj]
    have hle : ∀ j ≥ j0, μ {x} ≤ ENNReal.ofReal (m j0 / (2 : ℝ) ^ (j - j0)) := by
      intro j hj
      have hxj := Set.mem_iInter.mp (Set.mem_iInter.mp hxK j) hj
      obtain ⟨I, hI, hxI⟩ := Set.mem_iUnion₂.mp hxj
      have hsub : μ {x} ≤ μ (Set.Icc I.1 I.2) :=
        MeasureTheory.measure_mono (Set.singleton_subset_iff.mpr hxI)
      have hmass := StoppedTree.mass_le_of_split hB1 hm0 hmrec hsplit hmem j hj I hI
      have hunroll := WindowMassProd.mass_le_prod m B j0 hBpos hmrec j hj
      have hprod : (2 : ℝ) ^ (j - j0) ≤ ∏ i ∈ Finset.Ico j0 j, B i := by
        have h2 : ∏ _i ∈ Finset.Ico j0 j, (2 : ℝ) = (2 : ℝ) ^ (j - j0) := by
          rw [Finset.prod_const, Nat.card_Ico]
        rw [← h2]
        exact Finset.prod_le_prod₀ (fun _ _ => by norm_num)
          (fun i hi => hB2 i (Finset.mem_Ico.mp hi).1)
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ (j - j0) := by positivity
      have hdiv : m j ≤ m j0 / (2 : ℝ) ^ (j - j0) :=
        le_trans hunroll (div_le_div_of_nonneg_left hm0nn h2pos hprod)
      exact le_trans hsub (le_trans hmass (ENNReal.ofReal_le_ofReal hdiv))
    have htend : Filter.Tendsto
        (fun k : ℕ => ENNReal.ofReal (m j0 / (2 : ℝ) ^ ((j0 + k) - j0)))
        Filter.atTop (nhds 0) := by
      have hlim : Filter.Tendsto
          (fun k : ℕ => m j0 / (2 : ℝ) ^ ((j0 + k) - j0)) Filter.atTop (nhds 0) := by
        have heq : (fun k : ℕ => m j0 / (2 : ℝ) ^ ((j0 + k) - j0)) =
            fun k => m j0 * ((1 / 2 : ℝ) ^ k) := by
          funext k
          have hk : (j0 + k) - j0 = k := by omega
          rw [hk, div_pow, one_pow, one_div, ← div_eq_mul_inv]
        rw [heq]
        have hgeo : Filter.Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ k)) Filter.atTop (nhds 0) :=
          _root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        simpa using hgeo.const_mul (m j0)
      simpa [Function.comp_def, ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto 0).comp hlim
    have hle0 : μ {x} ≤ 0 :=
      ge_of_tendsto htend (Filter.Eventually.of_forall fun k => hle (j0 + k) (by omega))
    exact le_antisymm hle0 zero_le
  · have hsub : ({x} : Set ℝ) ⊆ (WindowTreePrune.cantorSet T j0)ᶜ :=
      Set.singleton_subset_iff.mpr hxK
    exact le_antisymm (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq hsupp)) zero_le

/-- Full three-branch window measure bound for a splitting probability measure `μ`
    supported on `cantorSet T j0` (`μ (cantorSet T j0)ᶜ = 0`):
    discharges `hCbig` (large windows), the small-window cascade (`0 < diam U ≤ 1/(H J1)²`,
    arbitrarily below any fixed level's `dmin`), and singletons (`diam U = 0`)
    on ALL bounded sets `U : Set ℝ` without vacuous full-`ℝ` covering hypotheses. -/
theorem mu_window_cascade_full
    {μ : Measure ℝ} {T : StoppedTree.TreeData} {j0 : ℕ} (hj0 : 1 ≤ j0)
    {m B H : ℕ → ℝ} {b c d0_c L_c C_H s : ℝ}
    (hc : 0 < c) (hd0c : 0 < d0_c) (hLc : 0 ≤ L_c)
    (hs0 : 0 < s) (hsb : s < b / 2)
    (hsupp : μ (WindowTreePrune.cantorSet T j0)ᶜ = 0)
    (hB2 : ∀ j ≥ j0, 2 ≤ B j) (hBpos : ∀ i, 0 < B i)
    (hbranch : ∀ i ≥ j0, c * (i : ℝ) ^ b ≤ B i)
    (hm0 : ∀ I ∈ T.atoms j0, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m j0))
    (hm0pos : 0 < m j0)
    (hmrec : ∀ j ≥ j0, m (j + 1) = m j / B j)
    (hsplit : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ C ∈ T.child j I,
      μ (Set.Icc C.1 C.2) ≤ μ (Set.Icc I.1 I.2) / ENNReal.ofReal (B j))
    (hmem : ∀ j ≥ j0, ∀ I ∈ T.atoms (j + 1), ∃ P ∈ T.atoms j, I ∈ T.child j P)
    (hHpos : ∀ j, 0 < H j)
    (hHlim : Filter.Tendsto (fun j => 1 / (H j) ^ 2) Filter.atTop (nhds 0))
    (hHlog : ∀ j ≥ j0,
      Real.log (H (j + 1)) ≤ (j : ℝ) * Real.log (j : ℝ) + C_H * (j : ℝ))
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 < I.2)
    (hlen : ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      d0_c / (H j) ^ 2 ≤ I.2 - I.1 ∧ I.2 - I.1 ≤ L_c / (H j) ^ 2)
    (hdisj : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ J ∈ T.atoms j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hprob : ∀ V : Set ℝ, μ V ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Set ℝ, Bornology.IsBounded U →
      μ U ≤ ENNReal.ofReal (C * Metric.diam U ^ s) := by
  let K0 : ℝ := ((2 + 3 * L_c) / d0_c + 2) * m j0
  have hK0pos : 0 < K0 := by
    have hdiv : 0 ≤ (2 + 3 * L_c) / d0_c := div_nonneg (by linarith) (le_of_lt hd0c)
    exact mul_pos (by linarith) hm0pos
  obtain ⟨J1, hJ1, hJ1_thresh⟩ := WindowAsympThresh.asymp_thresh_exists_rpow
    j0 hj0 b c s K0 C_H hc hs0 hsb hK0pos B H hBpos hbranch hHpos hHlog
  let C : ℝ := max 1 (((H J1) ^ 2) ^ s)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCbig : ∀ D : ℝ, 1 / (H J1) ^ 2 < D → (1 : ℝ) ≤ C * D ^ s :=
    WindowAsympThresh.hCbig_of_ge_scale (hHpos J1) (le_of_lt hs0) (le_max_right _ _)
  have hpt : ∀ x : ℝ, μ {x} = 0 :=
    mu_singleton_zero_of_support hsupp hB2 hBpos hm0 (le_of_lt hm0pos) hmrec hsplit hmem
  have hB1 : ∀ j ≥ j0, 1 ≤ B j := fun j hj => by linarith [hB2 j hj]
  -- Pad P below j0 with T.atoms j0 so WindowMassFull's ∀ j quantifiers hold uniformly.
  let P : ℕ → Finset (ℝ × ℝ) := fun j => if j0 ≤ j then T.atoms j else T.atoms j0
  let d0 : ℕ → ℝ := fun j => if j0 ≤ j then d0_c / (H j) ^ 2 else d0_c / (H j0) ^ 2
  let L : ℕ → ℝ := fun j => if j0 ≤ j then L_c / (H j) ^ 2 else L_c / (H j0) ^ 2
  let m0 : ℕ → ℝ := fun j => if j0 ≤ j then m j0 / ∏ i ∈ Finset.Ico j0 j, B i else m j0
  have hd0j : ∀ j, 0 < d0 j := by
    intro j; dsimp only [d0]; split_ifs
    · have := hHpos j; positivity
    · have := hHpos j0; positivity
  have hLj : ∀ j, 0 ≤ L j := by
    intro j; dsimp only [L]; split_ifs
    · have := hHpos j; positivity
    · have := hHpos j0; positivity
  have hm0nn : ∀ j, 0 ≤ m0 j := by
    intro j; dsimp only [m0]; split_ifs
    · exact div_nonneg (le_of_lt hm0pos) (le_of_lt (Finset.prod_pos fun i _ => hBpos i))
    · exact le_of_lt hm0pos
  refine ⟨C, hCpos, ?_⟩
  intro U hbddU
  let UK : Set ℝ := U ∩ WindowTreePrune.cantorSet T j0
  have hbddUK : Bornology.IsBounded UK := hbddU.subset Set.inter_subset_left
  have hmu_le_UK : μ U ≤ μ UK := by
    have hsub : U ⊆ UK ∪ (WindowTreePrune.cantorSet T j0)ᶜ := by
      intro x hx
      by_cases hxK : x ∈ WindowTreePrune.cantorSet T j0
      · exact Or.inl ⟨hx, hxK⟩
      · exact Or.inr hxK
    calc μ U ≤ μ (UK ∪ (WindowTreePrune.cantorSet T j0)ᶜ) := MeasureTheory.measure_mono hsub
      _ ≤ μ UK + μ (WindowTreePrune.cantorSet T j0)ᶜ := MeasureTheory.measure_union_le _ _
      _ = μ UK := by rw [hsupp, add_zero]
  have hUK_bound : μ UK ≤ ENNReal.ofReal (C * Metric.diam UK ^ s) := by
    refine WindowMassFull.mu_window_le_full (j0 := J1) hHlim d0 L m0 C s P
      hd0j hLj hm0nn
      (fun j I hI => by
        dsimp only [P] at hI; split_ifs at hI with hj
        · exact htriv j hj I hI
        · exact htriv j0 le_rfl I hI)
      (fun j I hI => by
        dsimp only [P, d0] at hI ⊢; split_ifs at hI ⊢ with hj
        · exact (hlen j hj I hI).1
        · exact (hlen j0 le_rfl I hI).1)
      (fun j I hI => by
        dsimp only [P, L] at hI ⊢; split_ifs at hI ⊢ with hj
        · exact (hlen j hj I hI).2
        · exact (hlen j0 le_rfl I hI).2)
      (fun j I hI J hJ hne => by
        dsimp only [P] at hI hJ; split_ifs at hI hJ with hj
        · exact hdisj j hj I hI J hJ hne
        · exact hdisj j0 le_rfl I hI J hJ hne)
      UK hbddUK
      (fun j x hx => by
        have hxK : x ∈ WindowTreePrune.cantorSet T j0 := hx.2
        dsimp only [P]; split_ifs with hj
        · have hxj := Set.mem_iInter.mp (Set.mem_iInter.mp hxK j) hj
          obtain ⟨I, hI, hxI⟩ := Set.mem_iUnion₂.mp hxj
          exact ⟨I, hI, hxI⟩
        · have hxj := Set.mem_iInter.mp (Set.mem_iInter.mp hxK j0) le_rfl
          obtain ⟨I, hI, hxI⟩ := Set.mem_iUnion₂.mp hxj
          exact ⟨I, hI, hxI⟩)
      (fun j I hI => by
        dsimp only [P, m0] at hI ⊢; split_ifs at hI ⊢ with hj
        · have h1 := StoppedTree.mass_le_of_split hB1 hm0 hmrec hsplit hmem j hj I hI
          have h2 := WindowMassProd.mass_le_prod m B j0 hBpos hmrec j hj
          exact le_trans h1 (ENNReal.ofReal_le_ofReal h2)
        · exact hm0 I hI)
      (fun j hj h' hh' => by
        have hjj0 : j0 ≤ j := le_trans hJ1 hj
        dsimp only [d0, L, m0]
        simp only [hjj0, ↓reduceIte]
        have hov := WindowAsympThresh.general_overlap_const (L_c := L_c) (hHpos j) hd0c hh'.2
        have hprod_pos : 0 < ∏ i ∈ Finset.Ico j0 j, B i :=
          Finset.prod_pos fun i _ => hBpos i
        have hm0_nn : 0 ≤ m j0 / ∏ i ∈ Finset.Ico j0 j, B i :=
          div_nonneg (le_of_lt hm0pos) (le_of_lt hprod_pos)
        have hth := hJ1_thresh j hj h' hh'.1
        have hh'pos : 0 < h' := lt_of_lt_of_le (by have := hHpos (j + 1); positivity) hh'.1
        calc ((2 * h' + 3 * (L_c / (H j) ^ 2)) / (d0_c / (H j) ^ 2) + 2) *
              (m j0 / ∏ i ∈ Finset.Ico j0 j, B i)
            ≤ ((2 + 3 * L_c) / d0_c + 2) * (m j0 / ∏ i ∈ Finset.Ico j0 j, B i) :=
              mul_le_mul_of_nonneg_right hov hm0_nn
          _ = K0 / ∏ i ∈ Finset.Ico j0 j, B i := by dsimp only [K0]; ring
          _ ≤ h' ^ s := hth
          _ = 1 * h' ^ s := (one_mul _).symm
          _ ≤ C * h' ^ s :=
              mul_le_mul_of_nonneg_right hC1 (le_of_lt (Real.rpow_pos_of_pos hh'pos s)))
      hpt hprob hCbig
  have hdiam_mono : Metric.diam UK ≤ Metric.diam U :=
    Metric.diam_mono Set.inter_subset_left hbddU
  have hrpow_mono : C * Metric.diam UK ^ s ≤ C * Metric.diam U ^ s :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow Metric.diam_nonneg hdiam_mono (le_of_lt hs0)) (le_of_lt hCpos)
  exact le_trans hmu_le_UK (le_trans hUK_bound (ENNReal.ofReal_le_ofReal hrpow_mono))

/-- Composes `mu_window_cascade_full` with `dimH_ge_of_local_diam_bound` to obtain
    `ENNReal.ofReal (b / 2) ≤ dimH (cantorSet T j0)` directly from a splitting
    probability measure `μ` supported on `cantorSet T j0` with `0 < μ (cantorSet T j0)`. -/
theorem dimH_ge_of_mu_window_cascade
    {μ : Measure ℝ} {T : StoppedTree.TreeData} {j0 : ℕ} (hj0 : 1 ≤ j0)
    {m B H : ℕ → ℝ} {b c d0_c L_c C_H : ℝ}
    (hc : 0 < c) (hd0c : 0 < d0_c) (hLc : 0 ≤ L_c)
    (hKpos : 0 < μ (WindowTreePrune.cantorSet T j0))
    (hsupp : μ (WindowTreePrune.cantorSet T j0)ᶜ = 0)
    (hB2 : ∀ j ≥ j0, 2 ≤ B j) (hBpos : ∀ i, 0 < B i)
    (hbranch : ∀ i ≥ j0, c * (i : ℝ) ^ b ≤ B i)
    (hm0 : ∀ I ∈ T.atoms j0, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m j0))
    (hm0pos : 0 < m j0)
    (hmrec : ∀ j ≥ j0, m (j + 1) = m j / B j)
    (hsplit : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ C ∈ T.child j I,
      μ (Set.Icc C.1 C.2) ≤ μ (Set.Icc I.1 I.2) / ENNReal.ofReal (B j))
    (hmem : ∀ j ≥ j0, ∀ I ∈ T.atoms (j + 1), ∃ P ∈ T.atoms j, I ∈ T.child j P)
    (hHpos : ∀ j, 0 < H j)
    (hHlim : Filter.Tendsto (fun j => 1 / (H j) ^ 2) Filter.atTop (nhds 0))
    (hHlog : ∀ j ≥ j0,
      Real.log (H (j + 1)) ≤ (j : ℝ) * Real.log (j : ℝ) + C_H * (j : ℝ))
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 < I.2)
    (hlen : ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      d0_c / (H j) ^ 2 ≤ I.2 - I.1 ∧ I.2 - I.1 ≤ L_c / (H j) ^ 2)
    (hdisj : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ J ∈ T.atoms j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hprob : ∀ V : Set ℝ, μ V ≤ 1) :
    ENNReal.ofReal (b / 2) ≤ dimH (WindowTreePrune.cantorSet T j0) := by
  by_cases hb0 : b ≤ 0
  · rw [ENNReal.ofReal_eq_zero.mpr (by linarith)]
    exact bot_le
  · push Not at hb0
    set t : ℝ := b / 2
    have ht_pos : 0 < t := by dsimp only [t]; linarith
    have hs_le : ∀ s : ℝ, 0 < s → s < t →
        ENNReal.ofReal s ≤ dimH (WindowTreePrune.cantorSet T j0) := by
      intro s hs0 hst
      obtain ⟨C, hCpos, hbound⟩ := mu_window_cascade_full hj0 hc hd0c hLc hs0 hst hsupp
        hB2 hBpos hbranch hm0 hm0pos hmrec hsplit hmem hHpos hHlim hHlog htriv hlen hdisj hprob
      refine dimH_ge_of_local_diam_bound hCpos hs0 zero_lt_one hKpos ?_
      intro V hVed
      have hbdd : Bornology.IsBounded V :=
        Metric.isBounded_iff_ediam_ne_top.mpr (ne_of_lt (lt_of_le_of_lt hVed ENNReal.ofReal_lt_top))
      exact hbound V hbdd
    apply le_of_forall_lt
    intro r hr
    by_cases hr0 : r = 0
    · subst hr0
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (half_pos ht_pos))
        (hs_le (t / 2) (half_pos ht_pos) (half_lt_self ht_pos))
    · have hr_ne_top : r ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hr (le_of_lt ENNReal.ofReal_lt_top))
      have hr_lt_t : r.toReal < t := by
        have h1 := (ENNReal.toReal_lt_toReal hr_ne_top ENNReal.ofReal_ne_top).mpr hr
        rwa [ENNReal.toReal_ofReal (le_of_lt ht_pos)] at h1
      set s : ℝ := (r.toReal + t) / 2
      have hr_lt_s : r.toReal < s := by dsimp only [s]; linarith
      have hs_lt_t : s < t := by dsimp only [s]; linarith
      have hs0 : 0 < s := lt_of_le_of_lt ENNReal.toReal_nonneg hr_lt_s
      have hlt : r < ENNReal.ofReal s := by
        rw [← ENNReal.ofReal_toReal hr_ne_top]
        exact (ENNReal.ofReal_lt_ofReal_iff hs0).mpr hr_lt_s
      exact lt_of_lt_of_le hlt (hs_le s hs0 hs_lt_t)

#print axioms WindowFrostmanDischarge.frostman_of_uniform_tree
#print axioms WindowFrostmanDischarge.frostman_of_stopped_tree_rpow
#print axioms WindowFrostmanDischarge.dimH_ge_of_stopped_tree_rpow
#print axioms WindowFrostmanDischarge.dimH_ge_one_of_coprime_tree
#print axioms WindowFrostmanDischarge.dimH_ge_gamma_of_coprimeS_tree
#print axioms WindowFrostmanDischarge.mass_distrib_of_local_diam_bound
#print axioms WindowFrostmanDischarge.dimH_ge_of_local_diam_bound
#print axioms WindowFrostmanDischarge.mu_singleton_zero_of_support
#print axioms WindowFrostmanDischarge.mu_window_cascade_full
#print axioms WindowFrostmanDischarge.dimH_ge_of_mu_window_cascade

end WindowFrostmanDischarge
