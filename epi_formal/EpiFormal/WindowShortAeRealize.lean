import EpiFormal.WindowShortAe
import EpiFormal.WindowBoundedUpper

/-!
# Full Measure-Theoretic Layer-A Proof of `thm:short-ae` and `thm:no-short-dim` Nullity

Proves Paper 2's `thm:short-ae` (`∀ᵐ x ∈ (0, 1), ∃ M, ∀ J ≥ M, c * log J ≤ Z_J(x)`)
and the Lebesgue-nullity half of `thm:no-short-dim` (`volume (divWindowSet ε) = 0`)
unconditionally in Lean 4 using ONLY Lean core axioms (`propext`, `Classical.choice`,
`Quot.sound`), with zero external hypotheses and zero `condExp` / Jacobian machinery:

1. Exact stopping-cylinder partition (`stoppedWordSet j`): pairwise disjoint open cylinders
   covering `(0, 1) \ ℚ`, with `cfStopIdx x i` constant on irrationals of each atom.
2. Elementary Möbius-endpoint sub-interval conditional bound (`atom_shortWin_volume_ge`):
   when `u = q_r > H_{j+1}`, `r_j = 0 ≤ 1` throughout the atom; when `H_j < u ≤ H_{j+1}`,
   setting `A = ⌊H_{j+1} / u⌋ + 1` gives an explicit Möbius open sub-interval `(0, 1/A)` of
   relative length `(u + v) / (A u + v) ≥ 1 / A ≥ H_j / (2 H_{j+1}) ≥ 1 / (40 j)` inside
   which every irrational satisfies `r_j = 1`.
3. Disjoint `lintegral_iUnion` one-step contraction & instantiation of `WindowShortAe.short_ae_main`
   yielding `thm_short_ae`, `volume_divWindowSet_eq_zero`, and `thm_no_short_dim_complete`.
-/

namespace WindowShortAeRealize

open Matrix Set Filter Finset ENNReal Metric Real MeasureTheory
open Cylinder WindowCFRealize WindowCFBridge WindowNoShortCFRealize WindowBoundedUpper

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Part 1: Stopping words, denominator identity, and `cfStopIdx` bracket -/

/-- Matrix convergent denominator `q_{|w|}` of a word `w : List ℕ`. -/
def cfDen (w : List ℕ) : ℤ := (cfProd (0 :: w)) 1 0

/-- Restricted Lebesgue measure on `(0, 1)`. -/
def unitVol : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

lemma unitVol_isFinite : IsFiniteMeasure unitVol := by
  refine ⟨?_⟩
  simp [unitVol, Real.volume_Ioo]

lemma dens_of_zero (x : ℝ) : (GenContFract.of x).dens 0 = 1 := by
  simp [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux,
    GenContFract.contsAux]

lemma cfDen_dropLast_eq {w : List ℕ} (hne : w ≠ []) :
    (cfProd (0 :: w)) 1 1 = cfDen w.dropLast := by
  have hspec : w.dropLast ++ [w.getLast hne] = w := List.dropLast_append_getLast hne
  have hcons : (0 :: w) = (0 :: w.dropLast) ++ [w.getLast hne] := by
    change 0 :: w = 0 :: (w.dropLast ++ [w.getLast hne])
    rw [hspec]
  rw [hcons, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
  simp [cfProd, cfMat, cfDen]

lemma cfDen_pos {w : List ℕ} (hw : PosDigits w) : 0 < cfDen w := by
  cases w with
  | nil => simp [cfDen, cfProd, cfMat]
  | cons a t =>
    unfold cfDen
    rw [(cfProd_zero_cons_row1 (a :: t)).1]
    exact (cfProd_col0_pos hw (List.cons_ne_nil a t)).1

lemma cfDen_mono_prefix {w₁ w₂ : List ℕ} (hw₂ : PosDigits w₂) (hpre : w₁ <+: w₂) :
    cfDen w₁ ≤ cfDen w₂ := by
  obtain ⟨u, rfl⟩ := hpre
  exact den_mono_prefix ((posDigits_append.mp hw₂).2)

lemma posDigits_dropLast {w : List ℕ} (hw : PosDigits w) : PosDigits w.dropLast := by
  intro a ha
  exact hw a (List.dropLast_subset w ha)

lemma H_mono {a b : ℕ} (hab : a ≤ b) : NoShortDim.H a ≤ NoShortDim.H b := by
  cases a with
  | zero =>
    have h0 : NoShortDim.H 0 = 0 := by
      unfold NoShortDim.H
      simp
    rw [h0]
    exact Nat.zero_le _
  | succ k =>
    have ha1 : 1 ≤ k + 1 := by omega
    have hb1 : 1 ≤ b := le_trans ha1 hab
    have hQ : Qsel (k + 1) ≤ Qsel b :=
      _root_.Qsel_strictMono.monotoneOn (Set.mem_Ici.mpr ha1) (Set.mem_Ici.mpr hb1) hab
    have hQR : ((Qsel (k + 1) : ℤ) : ℝ) ≤ ((Qsel b : ℤ) : ℝ) := by exact_mod_cast hQ
    have hsq : Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ Real.sqrt (b : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hab)
    have hQbnn : 0 ≤ ((Qsel b : ℤ) : ℝ) := by
      exact_mod_cast le_of_lt (Classification.Qsel_pos b)
    have hmul : ((Qsel (k + 1) : ℤ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤
        ((Qsel b : ℤ) : ℝ) * Real.sqrt (b : ℝ) :=
      mul_le_mul hQR hsq (Real.sqrt_nonneg _) hQbnn
    exact Nat.floor_mono hmul

/-- Bracket specification of `cfStopIdx x j` for any irrational `x ∈ (0, 1)` and `j ≥ 1`. -/
theorem cfStopIdx_spec_of_irrational {x : ℝ} (hirr : Irrational x) (hx0 : 0 < x) (hx1 : x < 1)
    {j : ℕ} (hj : 1 ≤ j) :
    (GenContFract.of x).dens (cfStopIdx x j) ≤ ((NoShortDim.H j : ℕ) : ℝ) ∧
      ((NoShortDim.H j : ℕ) : ℝ) < (GenContFract.of x).dens (cfStopIdx x j + 1) := by
  set S : Set ℕ := {k : ℕ | (GenContFract.of x).dens k ≤ ((NoShortDim.H j : ℕ) : ℝ)}
  have h0_mem : 0 ∈ S := by
    change (GenContFract.of x).dens 0 ≤ ((NoShortDim.H j : ℕ) : ℝ)
    rw [dens_of_zero]
    exact_mod_cast NoShortDim.H_ge_one j hj
  have hbdd : BddAbove S := by
    refine ⟨NoShortDim.H j, fun k hk => ?_⟩
    have hkd : (k : ℝ) ≤ (GenContFract.of x).dens k := nat_le_dens_of_irrational hirr hx0 hx1 k
    exact_mod_cast (le_trans hkd hk : (k : ℝ) ≤ ((NoShortDim.H j : ℕ) : ℝ))
  have hmem : cfStopIdx x j ∈ S := Nat.sSup_mem ⟨0, h0_mem⟩ hbdd
  have hlt : ((NoShortDim.H j : ℕ) : ℝ) < (GenContFract.of x).dens (cfStopIdx x j + 1) :=
    H_lt_dens_of_cfStopIdx_lt hirr hx0 hx1 (Nat.lt_succ_self _)
  exact ⟨hmem, hlt⟩

/-- Predicate defining minimal stopped continued-fraction words at stage `j`:
    `cfDen w > H_j` while `cfDen w.dropLast ≤ H_j`. -/
def isStoppedWord (j : ℕ) (w : List ℕ) : Prop :=
  PosDigits w ∧ w ≠ [] ∧ ((NoShortDim.H j : ℕ) : ℤ) < cfDen w ∧
    cfDen w.dropLast ≤ ((NoShortDim.H j : ℕ) : ℤ)

/-- Countable set of stopped words at stage `j`. -/
def stoppedWordSet (j : ℕ) : Set (List ℕ) :=
  {w : List ℕ | isStoppedWord j w}

theorem stoppedWordSet_countable (j : ℕ) : (stoppedWordSet j).Countable :=
  Set.to_countable _

theorem stoppedWords_incomparable {j : ℕ} {w₁ w₂ : List ℕ}
    (hw₁ : isStoppedWord j w₁) (hw₂ : isStoppedWord j w₂) (hne : w₁ ≠ w₂) :
    ¬ (w₁ <+: w₂) := by
  intro hpre
  obtain ⟨u, hu_eq⟩ := hpre
  have hune : u ≠ [] := by
    intro hu0
    subst hu0
    rw [List.append_nil] at hu_eq
    exact hne hu_eq
  have hdrop : w₁ <+: w₂.dropLast := by
    have hdl : w₂.dropLast = w₁ ++ u.dropLast := by
      rw [← hu_eq, List.dropLast_append_of_ne_nil hune]
    exact ⟨u.dropLast, hdl.symm⟩
  have hmono : cfDen w₁ ≤ cfDen w₂.dropLast :=
    cfDen_mono_prefix (posDigits_dropLast hw₂.1) hdrop
  have h1 : ((NoShortDim.H j : ℕ) : ℤ) < cfDen w₁ := hw₁.2.2.1
  have h2 : cfDen w₂.dropLast ≤ ((NoShortDim.H j : ℕ) : ℤ) := hw₂.2.2.2
  omega

theorem stoppedWords_disjoint {j : ℕ} {w₁ w₂ : List ℕ}
    (hw₁ : isStoppedWord j w₁) (hw₂ : isStoppedWord j w₂) (hne : w₁ ≠ w₂) :
    Disjoint (Set.Ioo (cylPair w₁).1 (cylPair w₁).2)
      (Set.Ioo (cylPair w₂).1 (cylPair w₂).2) :=
  cylPair_disj_of_incomparable hw₁.1 hw₂.1
    (stoppedWords_incomparable hw₁ hw₂ hne)
    (stoppedWords_incomparable hw₂ hw₁ hne.symm)

theorem cylPair_subset_Ioo_unit_of_stopped {j : ℕ} {w : List ℕ} (hw : isStoppedWord j w) :
    Set.Ioo (cylPair w).1 (cylPair w).2 ⊆ Set.Ioo (0 : ℝ) 1 :=
  Ioo_cylPair_subset_Ioo_unit hw.1 hw.2.1

theorem stoppedWords_cover_irrationals {j : ℕ} (hj : 1 ≤ j) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hirr : Irrational x) :
    ∃ w ∈ stoppedWordSet j, x ∈ Set.Ioo (cylPair w).1 (cylPair w).2 := by
  obtain ⟨_, hgt⟩ := cfStopIdx_spec_of_irrational hirr hx.1 hx.2 hj
  set r : ℕ := cfStopIdx x j + 1
  obtain ⟨w, t, _, ht0, ht1, hmob⟩ := exists_word_of_irrational r hirr hx.1 hx.2
  set wl : List ℕ := pnatWord w
  have hpd : PosDigits wl := posDigits_pnatWord w
  have hlen : wl.length = r := pnatWord_length w
  have hne : wl ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hx_mem : x ∈ Set.Ioo (cylPair wl).1 (cylPair wl).2 := by
    rw [hmob]
    exact mobius_mem_Ioo_cylPair hpd hne ht0 ht1
  have htop_pen := dens_mobius_top_and_penult hpd hne ht0 ht1
  rw [← hmob, hlen] at htop_pen
  have hden_top : ((NoShortDim.H j : ℕ) : ℤ) < cfDen wl := by
    have hR : ((NoShortDim.H j : ℕ) : ℝ) < (cfDen wl : ℝ) := by
      unfold cfDen
      rw [← htop_pen.1]
      exact hgt
    exact_mod_cast hR
  have hden_pen : cfDen wl.dropLast ≤ ((NoShortDim.H j : ℕ) : ℤ) := by
    have hR : (cfDen wl.dropLast : ℝ) ≤ ((NoShortDim.H j : ℕ) : ℝ) := by
      rw [← cfDen_dropLast_eq hne, ← htop_pen.2]
      have hsub : r - 1 = cfStopIdx x j := by omega
      rw [hsub]
      exact (cfStopIdx_spec_of_irrational hirr hx.1 hx.2 hj).1
    exact_mod_cast hR
  exact ⟨wl, ⟨hpd, hne, hden_top, hden_pen⟩, hx_mem⟩

theorem stoppedWords_cyl_ae_mem (j : ℕ) (hj : 1 ≤ j) :
    ∀ᵐ x ∂unitVol, x ∈ ⋃ w ∈ stoppedWordSet j, Set.Ioo (cylPair w).1 (cylPair w).2 := by
  have hdiff : Set.Ioo (0 : ℝ) 1 \
      (⋃ w ∈ stoppedWordSet j, Set.Ioo (cylPair w).1 (cylPair w).2) ⊆
      Set.range ((↑) : ℚ → ℝ) := by
    intro x ⟨hx_Ioo, hx_not⟩
    by_contra hq
    have hirr : Irrational x := fun ⟨q, hq'⟩ => hq ⟨q, hq'⟩
    obtain ⟨w, hw, hxw⟩ := stoppedWords_cover_irrationals hj hx_Ioo hirr
    exact hx_not (Set.mem_iUnion₂.mpr ⟨w, hw, hxw⟩)
  have hnull_q : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    (Set.countable_range ((↑) : ℚ → ℝ)).measure_zero volume
  rw [ae_iff]
  have hrest : unitVol {x : ℝ |
      ¬ x ∈ ⋃ w ∈ stoppedWordSet j, Set.Ioo (cylPair w).1 (cylPair w).2} =
      volume (Set.Ioo (0 : ℝ) 1 \
        (⋃ w ∈ stoppedWordSet j, Set.Ioo (cylPair w).1 (cylPair w).2)) := by
    rw [unitVol, Measure.restrict_apply' measurableSet_Ioo]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff, and_comm]
  rw [hrest]
  exact measure_mono_null hdiff hnull_q

/-! ### Part 2: Short-window event measurability & atomwise constancy -/

/-- Deterministic stopping index induced by a stopped word `w` at earlier index `i`. -/
noncomputable def wordStopIdx (i : ℕ) (w : List ℕ) : ℕ :=
  sSup {k : ℕ | k < w.length ∧ (cfProd (0 :: w.take k)) 1 0 ≤ ((NoShortDim.H i : ℕ) : ℤ)}

/-- Paper 2's short-window event `E_j = {x ∈ (0, 1) | Irrational x ∧ k_{j+1}(x) - k_j(x) ≤ 1}`. -/
def shortWinEvent (j : ℕ) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 | Irrational x ∧ cfStopIdx x (j + 1) - cfStopIdx x j ≤ 1}

/-- Cumulative short-window count `Z_J(x) = ∑_{1 ≤ j ≤ J} 1_{E_j}(x)`. -/
noncomputable def shortWinCount (J : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 J, if x ∈ shortWinEvent j then (1 : ℝ) else 0

theorem cfStopIdx_const_on_stoppedCyl {i j : ℕ} (_hi : 1 ≤ i) (hij : i ≤ j)
    {w : List ℕ} (hw : isStoppedWord j w) {x : ℝ} (_hirr : Irrational x)
    (hx : x ∈ Set.Ioo (cylPair w).1 (cylPair w).2) :
    cfStopIdx x i = wordStopIdx i w := by
  obtain ⟨t, ht, hmob⟩ := exists_mobius_of_mem_Ioo_cylPair hw.1 hw.2.1 hx
  have hdens_w : ((NoShortDim.H i : ℕ) : ℝ) < (GenContFract.of x).dens w.length := by
    rw [← hmob, (dens_mobius_top_and_penult hw.1 hw.2.1 ht.1 ht.2).1]
    have h1 : ((NoShortDim.H i : ℕ) : ℤ) ≤ ((NoShortDim.H j : ℕ) : ℤ) := by
      exact_mod_cast H_mono hij
    exact_mod_cast lt_of_le_of_lt h1 hw.2.2.1
  have hset_eq : {k : ℕ | (GenContFract.of x).dens k ≤ ((NoShortDim.H i : ℕ) : ℝ)} =
      {k : ℕ | k < w.length ∧ (cfProd (0 :: w.take k)) 1 0 ≤ ((NoShortDim.H i : ℕ) : ℤ)} := by
    ext k
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hk
      have hk_lt : k < w.length := by
        by_contra hge
        have hmono := dens_of_mono x (by omega : w.length ≤ k)
        linarith
      refine ⟨hk_lt, ?_⟩
      rw [← hmob, dens_mobius_eq hw.1 ht.1 ht.2 (le_of_lt hk_lt)] at hk
      exact_mod_cast hk
    · rintro ⟨hk_lt, hk_le⟩
      rw [← hmob, dens_mobius_eq hw.1 ht.1 ht.2 (le_of_lt hk_lt)]
      exact_mod_cast hk_le
  unfold cfStopIdx wordStopIdx
  rw [hset_eq]

theorem measurableSet_shortWinEvent (j : ℕ) (hj : 1 ≤ j) : MeasurableSet (shortWinEvent j) := by
  let W : Set (List ℕ) :=
    {w ∈ stoppedWordSet (j + 1) | wordStopIdx (j + 1) w - wordStopIdx j w ≤ 1}
  have hset : shortWinEvent j =
      (⋃ w ∈ W, Set.Ioo (cylPair w).1 (cylPair w).2) \ Set.range ((↑) : ℚ → ℝ) := by
    ext x
    constructor
    · rintro ⟨hx01, hirr, hdiff⟩
      obtain ⟨w, hw, hxw⟩ := stoppedWords_cover_irrationals (by omega : 1 ≤ j + 1) hx01 hirr
      have hw_diff : wordStopIdx (j + 1) w - wordStopIdx j w ≤ 1 := by
        rw [← cfStopIdx_const_on_stoppedCyl (by omega) le_rfl hw hirr hxw,
          ← cfStopIdx_const_on_stoppedCyl hj (by omega) hw hirr hxw]
        exact hdiff
      refine ⟨Set.mem_iUnion₂.mpr ⟨w, ⟨hw, hw_diff⟩, hxw⟩, ?_⟩
      rintro ⟨q, rfl⟩
      exact hirr ⟨q, rfl⟩
    · rintro ⟨hx_u, hx_nq⟩
      obtain ⟨w, ⟨hw, hw_diff⟩, hxw⟩ := Set.mem_iUnion₂.mp hx_u
      have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := cylPair_subset_Ioo_unit_of_stopped hw hxw
      have hirr : Irrational x := fun ⟨q, hq⟩ => hx_nq ⟨q, hq⟩
      refine ⟨hx01, hirr, ?_⟩
      rw [cfStopIdx_const_on_stoppedCyl (by omega) le_rfl hw hirr hxw,
        cfStopIdx_const_on_stoppedCyl hj (by omega) hw hirr hxw]
      exact hw_diff
  rw [hset]
  have hW_cnt : W.Countable := (stoppedWordSet_countable (j + 1)).mono (fun _ hw => hw.1)
  have hU_meas : MeasurableSet (⋃ w ∈ W, Set.Ioo (cylPair w).1 (cylPair w).2) :=
    MeasurableSet.biUnion hW_cnt (fun _ _ => measurableSet_Ioo)
  have hQ_meas : MeasurableSet (Set.range ((↑) : ℚ → ℝ)) :=
    (Set.countable_range ((↑) : ℚ → ℝ)).measurableSet
  exact hU_meas.diff hQ_meas

theorem measurable_shortWinCount (J : ℕ) : Measurable (shortWinCount J) := by
  unfold shortWinCount
  refine Finset.measurable_sum _ fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  exact Measurable.ite (measurableSet_shortWinEvent j hj1) measurable_const measurable_const

theorem integrable_exp_neg_shortWinCount (J : ℕ) :
    Integrable (fun x => Real.exp (-shortWinCount J x)) unitVol := by
  have : IsFiniteMeasure unitVol := unitVol_isFinite
  refine Integrable.of_bound
    ((measurable_exp.comp (measurable_shortWinCount J).neg).aestronglyMeasurable) 1 ?_
  refine Eventually.of_forall fun x => ?_
  have hnn : 0 ≤ shortWinCount J x := by
    unfold shortWinCount
    exact Finset.sum_nonneg fun j _ => by by_cases h : x ∈ shortWinEvent j <;> simp [h]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- Deterministic pre-count value `zPrev j w` shared by all irrationals in `Ioo (cylPair w)`. -/
noncomputable def zPrev (j : ℕ) (w : List ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (j - 1),
    if wordStopIdx (i + 1) w - wordStopIdx i w ≤ 1 then (1 : ℝ) else 0

theorem shortWinCount_pred_eq_on_atom {j : ℕ} (hj : 1 ≤ j) {w : List ℕ}
    (hw : isStoppedWord j w) {x : ℝ} (hirr : Irrational x)
    (hx : x ∈ Set.Ioo (cylPair w).1 (cylPair w).2) :
    shortWinCount (j - 1) x = zPrev j w := by
  unfold shortWinCount zPrev
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  have hi1 : 1 ≤ i := hi.1
  have hij1 : i + 1 ≤ j := by omega
  have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := cylPair_subset_Ioo_unit_of_stopped hw hx
  have h1 : cfStopIdx x (i + 1) = wordStopIdx (i + 1) w :=
    cfStopIdx_const_on_stoppedCyl (by omega) hij1 hw hirr hx
  have h2 : cfStopIdx x i = wordStopIdx i w :=
    cfStopIdx_const_on_stoppedCyl hi1 (by omega) hw hirr hx
  have hiff : x ∈ shortWinEvent i ↔ wordStopIdx (i + 1) w - wordStopIdx i w ≤ 1 := by
    simp only [shortWinEvent, Set.mem_ofPred_eq, h1, h2]
    exact ⟨fun h => h.2.2, fun h => ⟨hx01, hirr, h⟩⟩
  by_cases hL : x ∈ shortWinEvent i <;>
    by_cases hR : wordStopIdx (i + 1) w - wordStopIdx i w ≤ 1
  · simp only [hL, ↓reduceIte, hR]
  · exact absurd (hiff.mp hL) hR
  · exact absurd (hiff.mpr hR) hL
  · simp only [hL, ↓reduceIte, hR]

theorem shortWinCount_succ_eq_on_atom {j : ℕ} (hj : 1 ≤ j) {w : List ℕ}
    (hw : isStoppedWord j w) {x : ℝ} (hirr : Irrational x)
    (hx : x ∈ Set.Ioo (cylPair w).1 (cylPair w).2) :
    shortWinCount j x = zPrev j w + (if x ∈ shortWinEvent j then (1 : ℝ) else 0) := by
  have hsum : Finset.Icc 1 j = insert j (Finset.Icc 1 (j - 1)) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : j ∉ Finset.Icc 1 (j - 1) := by
    simp only [Finset.mem_Icc]
    omega
  unfold shortWinCount
  rw [hsum, Finset.sum_insert hnot, add_comm]
  congr 1
  exact shortWinCount_pred_eq_on_atom hj hw hirr hx

/-! ### Part 3: Elementary Möbius-endpoint conditional probability lower bound -/

private lemma mobius_interval_equiv {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M.det = 1 ∨ M.det = -1)
    (hu_pos : (0 : ℝ) < (M 1 0 : ℝ)) (hv_nn : (0 : ℝ) ≤ (M 1 1 : ℝ))
    {A : ℝ} (hA : 1 ≤ A) {x : ℝ} :
    x ∈ Set.Ioo (min (mobius M 0) (mobius M (1 / A))) (max (mobius M 0) (mobius M (1 / A))) ↔
      ∃ t ∈ Set.Ioo (0 : ℝ) (1 / A), mobius M t = x := by
  have hApos : 0 < A := by linarith
  have hinvA_le1 : 1 / A ≤ 1 := div_le_one_of_le₀ hA hApos.le
  have hden_s : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (0 : ℝ) < (M 1 0 : ℝ) + (M 1 1 : ℝ) * s := by
    intro s hs0 _; nlinarith
  have hmono_pt : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (M.det = 1 → mobius M s < mobius M 0 ∧ mobius M 1 ≤ mobius M s) ∧
      (M.det = -1 → mobius M 0 < mobius M s ∧ mobius M s ≤ mobius M 1) := by
    intro s hs0 hs1
    have hds := ne_of_gt (hden_s s hs0.le hs1)
    have hd0 := ne_of_gt (hden_s 0 le_rfl zero_le_one)
    have hd1 := ne_of_gt (hden_s 1 zero_le_one le_rfl)
    have hsub0 := mobius_sub M s 0 hds hd0
    have hsub1 := mobius_sub M 1 s hd1 hds
    constructor
    · intro hd
      have hlt0 : mobius M s - mobius M 0 < 0 := by
        rw [hsub0, hd, Int.cast_one]
        exact div_neg_of_neg_of_pos (by nlinarith)
          (mul_pos (hden_s s hs0.le hs1) (hden_s 0 le_rfl zero_le_one))
      have hle1 : mobius M 1 - mobius M s ≤ 0 := by
        rw [hsub1, hd, Int.cast_one]
        exact div_nonpos_of_nonpos_of_nonneg (by nlinarith)
          (mul_pos (hden_s 1 zero_le_one le_rfl) (hden_s s hs0.le hs1)).le
      exact ⟨by linarith, by linarith⟩
    · intro hd
      have hgt0 : 0 < mobius M s - mobius M 0 := by
        rw [hsub0, hd, Int.cast_neg, Int.cast_one]
        exact div_pos (by nlinarith)
          (mul_pos (hden_s s hs0.le hs1) (hden_s 0 le_rfl zero_le_one))
      have hge1 : 0 ≤ mobius M 1 - mobius M s := by
        rw [hsub1, hd, Int.cast_neg, Int.cast_one]
        exact div_nonneg (by nlinarith)
          (mul_pos (hden_s 1 zero_le_one le_rfl) (hden_s s hs0.le hs1)).le
      exact ⟨by linarith, by linarith⟩
  constructor
  · intro hx
    have hx_cyl : x ∈ Set.Ioo (min (mobius M 0) (mobius M 1))
        (max (mobius M 0) (mobius M 1)) := by
      rcases hdet with hd | hd
      · obtain ⟨hlt0, hle1⟩ := (hmono_pt (1 / A) (by positivity) hinvA_le1).1 hd
        rw [min_eq_right hlt0.le, max_eq_left hlt0.le] at hx
        have h10 : mobius M 1 ≤ mobius M 0 := le_trans hle1 hlt0.le
        rw [min_eq_right h10, max_eq_left h10]
        exact ⟨lt_of_le_of_lt hle1 hx.1, hx.2⟩
      · obtain ⟨hgt0, hle1⟩ := (hmono_pt (1 / A) (by positivity) hinvA_le1).2 hd
        rw [min_eq_left hgt0.le, max_eq_right hgt0.le] at hx
        have h01 : mobius M 0 ≤ mobius M 1 := le_trans hgt0.le hle1
        rw [min_eq_left h01, max_eq_right h01]
        exact ⟨hx.1, lt_of_lt_of_le hx.2 hle1⟩
    set X : ℝ := x * (M 1 0 : ℝ) - (M 0 0 : ℝ)
    set Y : ℝ := ((M 0 0 : ℝ) + (M 0 1 : ℝ)) - x * ((M 1 0 : ℝ) + (M 1 1 : ℝ))
    have hmob0 : mobius M 0 = (M 0 0 : ℝ) / (M 1 0 : ℝ) := by simp [mobius]
    have hmob1 : mobius M 1 = ((M 0 0 : ℝ) + (M 0 1 : ℝ)) / ((M 1 0 : ℝ) + (M 1 1 : ℝ)) := by
      simp [mobius]
    have hden0 : 0 < (M 1 0 : ℝ) := hu_pos
    have hden1 : 0 < (M 1 0 : ℝ) + (M 1 1 : ℝ) := by linarith
    have hXY : (0 < X ∧ 0 < Y) ∨ (X < 0 ∧ Y < 0) := by
      rcases le_total (mobius M 0) (mobius M 1) with hle | hle
      · rw [min_eq_left hle, max_eq_right hle] at hx_cyl
        left
        have hX : (M 0 0 : ℝ) < x * (M 1 0 : ℝ) := by
          have := hx_cyl.1; rw [hmob0, div_lt_iff₀ hden0] at this; exact this
        have hY : x * ((M 1 0 : ℝ) + (M 1 1 : ℝ)) < (M 0 0 : ℝ) + (M 0 1 : ℝ) := by
          have := hx_cyl.2; rw [hmob1, lt_div_iff₀ hden1] at this; exact this
        exact ⟨by linarith, by linarith⟩
      · rw [min_eq_right hle, max_eq_left hle] at hx_cyl
        right
        have hX : x * (M 1 0 : ℝ) < (M 0 0 : ℝ) := by
          have := hx_cyl.2; rw [hmob0, lt_div_iff₀ hden0] at this; exact this
        have hY : (M 0 0 : ℝ) + (M 0 1 : ℝ) < x * ((M 1 0 : ℝ) + (M 1 1 : ℝ)) := by
          have := hx_cyl.1; rw [hmob1, div_lt_iff₀ hden1] at this; exact this
        exact ⟨by linarith, by linarith⟩
    set t : ℝ := X / (X + Y)
    have hXY_ne : X + Y ≠ 0 := by rcases hXY with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
    have ht0 : 0 < t := by
      rcases hXY with ⟨hX, hY⟩ | ⟨hX, hY⟩
      · exact div_pos hX (by linarith)
      · exact div_pos_of_neg_of_neg hX (by linarith)
    have ht1 : t < 1 := by
      rcases hXY with ⟨hX, hY⟩ | ⟨hX, hY⟩
      · exact (div_lt_one (by linarith)).mpr (by linarith)
      · exact (div_lt_one_of_neg (by linarith)).mpr (by linarith)
    have hdt : 0 < (M 1 0 : ℝ) + (M 1 1 : ℝ) * t := by nlinarith
    have hx_eq : mobius M t = x := by
      unfold mobius
      rw [div_eq_iff (ne_of_gt hdt)]
      dsimp only [t]
      field_simp [hXY_ne]
      dsimp only [X, Y]
      ring
    have ht_lt_A : t < 1 / A := by
      have hsub := mobius_sub M t (1 / A) (ne_of_gt hdt)
        (ne_of_gt (hden_s _ (by positivity) hinvA_le1))
      have hpos_den : 0 < ((M 1 0 : ℝ) + (M 1 1 : ℝ) * t) *
          ((M 1 0 : ℝ) + (M 1 1 : ℝ) * (1 / A)) :=
        mul_pos hdt (hden_s _ (by positivity) hinvA_le1)
      rcases hdet with hd | hd
      · obtain ⟨h0A, _⟩ := (hmono_pt (1 / A) (by positivity) hinvA_le1).1 hd
        rw [min_eq_right h0A.le, max_eq_left h0A.le] at hx
        have hdiff : 0 < mobius M t - mobius M (1 / A) := by rw [hx_eq]; exact sub_pos.mpr hx.1
        rw [hsub, hd, Int.cast_one] at hdiff
        have hnum := (div_pos_iff_of_pos_right hpos_den).mp hdiff
        linarith
      · obtain ⟨h0A, _⟩ := (hmono_pt (1 / A) (by positivity) hinvA_le1).2 hd
        rw [min_eq_left h0A.le, max_eq_right h0A.le] at hx
        have hdiff : mobius M t - mobius M (1 / A) < 0 := by rw [hx_eq]; exact sub_neg.mpr hx.2
        rw [hsub, hd, Int.cast_neg, Int.cast_one, div_lt_iff₀ hpos_den, zero_mul] at hdiff
        linarith
    exact ⟨t, ⟨ht0, ht_lt_A⟩, hx_eq⟩
  · rintro ⟨t, ⟨ht0, htA⟩, rfl⟩
    have ht1 : t < 1 := lt_of_lt_of_le htA hinvA_le1
    have hdt := hden_s t ht0.le ht1.le
    have hd0 := hden_s 0 le_rfl zero_le_one
    have hdA := hden_s (1 / A) (by positivity) hinvA_le1
    have h0 := mobius_sub M t 0 (ne_of_gt hdt) (ne_of_gt hd0)
    have hA' := mobius_sub M (1 / A) t (ne_of_gt hdA) (ne_of_gt hdt)
    rcases hdet with hd | hd
    · have hmt0 : mobius M t < mobius M 0 := by
        have : mobius M t - mobius M 0 < 0 := by
          rw [h0, hd, Int.cast_one]; exact div_neg_of_neg_of_pos (by nlinarith) (mul_pos hdt hd0)
        linarith
      have hmAt : mobius M (1 / A) < mobius M t := by
        have : mobius M (1 / A) - mobius M t < 0 := by
          rw [hA', hd, Int.cast_one]; exact div_neg_of_neg_of_pos (by nlinarith) (mul_pos hdA hdt)
        linarith
      exact ⟨lt_of_le_of_lt (min_le_right _ _) hmAt, lt_of_lt_of_le hmt0 (le_max_left _ _)⟩
    · have hmt0 : mobius M 0 < mobius M t := by
        have : 0 < mobius M t - mobius M 0 := by
          rw [h0, hd, Int.cast_neg, Int.cast_one]
          exact div_pos (by nlinarith) (mul_pos hdt hd0)
        linarith
      have hmAt : mobius M t < mobius M (1 / A) := by
        have : 0 < mobius M (1 / A) - mobius M t := by
          rw [hA', hd, Int.cast_neg, Int.cast_one]
          exact div_pos (by nlinarith) (mul_pos hdA hdt)
        linarith
      exact ⟨lt_of_le_of_lt (min_le_left _ _) hmt0, lt_of_lt_of_le hmAt (le_max_right _ _)⟩

/-- Atom-wise short-window volume lower bound:
    `volume (Ioo (cylPair w) ∩ shortWinEvent j) ≥ ((1 / 40) / j) * volume (Ioo (cylPair w))`
    for all `j ≥ 3` and every stopped word `w ∈ stoppedWordSet j`. -/
theorem atom_shortWin_volume_ge {j : ℕ} (hj : 3 ≤ j) {w : List ℕ} (hw : isStoppedWord j w) :
    ENNReal.ofReal (((1 : ℝ) / 40) / (j : ℝ)) * volume (Set.Ioo (cylPair w).1 (cylPair w).2) ≤
      volume (Set.Ioo (cylPair w).1 (cylPair w).2 ∩ shortWinEvent j) := by
  have hj1 : 1 ≤ j := by omega
  have hjpos : (0 : ℝ) < (j : ℝ) := by positivity
  have hrat_pos : 0 < ((1 : ℝ) / 40) / (j : ℝ) := by positivity
  have hrat_le1 : ((1 : ℝ) / 40) / (j : ℝ) ≤ 1 := by
    have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    rw [div_le_one hjpos]
    linarith
  by_cases hcross : ((NoShortDim.H (j + 1) : ℕ) : ℤ) < cfDen w
  · have hsub : Set.Ioo (cylPair w).1 (cylPair w).2 \ Set.range ((↑) : ℚ → ℝ) ⊆
        Set.Ioo (cylPair w).1 (cylPair w).2 ∩ shortWinEvent j := by
      intro x ⟨hx_mem, hx_nq⟩
      have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := cylPair_subset_Ioo_unit_of_stopped hw hx_mem
      have hirr : Irrational x := fun ⟨q, hq⟩ => hx_nq ⟨q, hq⟩
      obtain ⟨t, ht, hmob⟩ := exists_mobius_of_mem_Ioo_cylPair hw.1 hw.2.1 hx_mem
      obtain ⟨htop, hpen⟩ := dens_mobius_top_and_penult hw.1 hw.2.1 ht.1 ht.2
      rw [hmob] at htop hpen
      have hstop_j : cfStopIdx x j = w.length - 1 := by
        have hlen1 : 1 ≤ w.length := List.length_pos_of_ne_nil hw.2.1
        have hsub1 : w.length - 1 + 1 = w.length := by omega
        refine (cfStopIdx_eq_of_bracket ?_ ?_).2
        · rw [hpen, cfDen_dropLast_eq hw.2.1]
          exact_mod_cast hw.2.2.2
        · rw [hsub1, htop]
          exact_mod_cast hw.2.2.1
      have hstop_j1 : cfStopIdx x (j + 1) = w.length - 1 := by
        have hlen1 : 1 ≤ w.length := List.length_pos_of_ne_nil hw.2.1
        have hsub1 : w.length - 1 + 1 = w.length := by omega
        refine (cfStopIdx_eq_of_bracket ?_ ?_).2
        · rw [hpen, cfDen_dropLast_eq hw.2.1]
          have hHm : NoShortDim.H j ≤ NoShortDim.H (j + 1) := H_mono (Nat.le_succ j)
          exact_mod_cast le_trans hw.2.2.2 (by exact_mod_cast hHm)
        · rw [hsub1, htop]
          exact_mod_cast hcross
      refine ⟨hx_mem, hx01, hirr, ?_⟩
      rw [hstop_j1, hstop_j, Nat.sub_self]
      omega
    have hnull_q : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
      (Set.countable_range ((↑) : ℚ → ℝ)).measure_zero volume
    have heq_vol : volume (Set.Ioo (cylPair w).1 (cylPair w).2) =
        volume (Set.Ioo (cylPair w).1 (cylPair w).2 \ Set.range ((↑) : ℚ → ℝ)) :=
      (measure_sdiff_null hnull_q).symm
    have hle1 : ENNReal.ofReal (((1 : ℝ) / 40) / (j : ℝ)) ≤ 1 := ENNReal.ofReal_le_one.mpr hrat_le1
    calc ENNReal.ofReal (((1 : ℝ) / 40) / (j : ℝ)) * volume (Set.Ioo (cylPair w).1 (cylPair w).2)
        ≤ 1 * volume (Set.Ioo (cylPair w).1 (cylPair w).2) := mul_le_mul_of_nonneg_right hle1 bot_le
      _ = volume (Set.Ioo (cylPair w).1 (cylPair w).2 \ Set.range ((↑) : ℚ → ℝ)) := by
          rw [one_mul, heq_vol]
      _ ≤ volume (Set.Ioo (cylPair w).1 (cylPair w).2 ∩ shortWinEvent j) := measure_mono hsub
  · have hle_cross : cfDen w ≤ ((NoShortDim.H (j + 1) : ℕ) : ℤ) := le_of_not_gt hcross
    set M := cfProd (0 :: w)
    set u : ℤ := (cfProd (0 :: w)) 1 0
    set v : ℤ := (cfProd (0 :: w)) 1 1
    have hu_posZ : 0 < u := cfDen_pos hw.1
    have hu_posR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu_posZ
    have hv_nnZ : 0 ≤ v := cfProd_nonneg (0 :: w) 1 1
    have hv_nnR : (0 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv_nnZ
    have hv_le_u : v ≤ u := by
      change (cfProd (0 :: w)) 1 1 ≤ (cfProd (0 :: w)) 1 0
      rw [(cfProd_zero_cons_row1 w).1, (cfProd_zero_cons_row1 w).2]
      exact (cfProd_col1_le_col0 hw.1 hw.2.1).1
    have hH_gtZ : ((NoShortDim.H j : ℕ) : ℤ) < u := hw.2.2.1
    set A : ℕ := NoShortDim.H (j + 1) / u.toNat + 1
    have hu_toNat : (u.toNat : ℤ) = u := Int.toNat_of_nonneg hu_posZ.le
    have hdiv_ge : 1 ≤ NoShortDim.H (j + 1) / u.toNat := by
      refine Nat.div_pos ?_ (by omega)
      exact_mod_cast (by rw [hu_toNat]; exact hle_cross : (u.toNat : ℤ) ≤ NoShortDim.H (j + 1))
    have hA2 : 2 ≤ A := by omega
    have hA1R : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast (by omega : 1 ≤ A)
    have hAu_gtN : NoShortDim.H (j + 1) < A * u.toNat := by
      have h1 : A = NoShortDim.H (j + 1) / u.toNat + 1 := rfl
      rw [h1, Nat.add_mul, one_mul]
      exact Nat.lt_div_mul_add (a := NoShortDim.H (j + 1)) (by omega : 0 < u.toNat)
    have hAu_gtZ : ((NoShortDim.H (j + 1) : ℕ) : ℤ) < (A : ℤ) * u := by
      have h1 : ((A * u.toNat : ℕ) : ℤ) = (A : ℤ) * u := by
        rw [Nat.cast_mul, hu_toNat]
      rw [← h1]
      exact_mod_cast hAu_gtN
    have hdet : M.det = 1 ∨ M.det = -1 := by
      have hd : M.det = (-1 : ℤ) ^ (0 :: w).length := cfProd_det (0 :: w)
      rw [hd]; exact neg_one_pow_eq_or ℤ (0 :: w).length
    set loA : ℝ := min (mobius M 0) (mobius M (1 / (A : ℝ)))
    set hiA : ℝ := max (mobius M 0) (mobius M (1 / (A : ℝ)))
    have hJA_sub_cyl : Set.Ioo loA hiA ⊆ Set.Ioo (cylPair w).1 (cylPair w).2 := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (mobius_interval_equiv hdet hu_posR hv_nnR hA1R).mp hx
      have ht1 : t < 1 := lt_of_lt_of_le ht.2 (div_le_one_of_le₀ hA1R (by positivity))
      exact mobius_mem_Ioo_cylPair hw.1 hw.2.1 ht.1 ht1
    have hJA_sub_ev : Set.Ioo loA hiA \ Set.range ((↑) : ℚ → ℝ) ⊆
        Set.Ioo (cylPair w).1 (cylPair w).2 ∩ shortWinEvent j := by
      intro x ⟨hx_JA, hx_nq⟩
      have hx_cyl := hJA_sub_cyl hx_JA
      have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := cylPair_subset_Ioo_unit_of_stopped hw hx_cyl
      have hirr : Irrational x := fun ⟨q, hq⟩ => hx_nq ⟨q, hq⟩
      obtain ⟨t, ht, hmob⟩ := (mobius_interval_equiv hdet hu_posR hv_nnR hA1R).mp hx_JA
      have ht1 : t < 1 := lt_of_lt_of_le ht.2 (div_le_one_of_le₀ hA1R (by positivity))
      have htinv_gt : (A : ℝ) < t⁻¹ := by
        rw [lt_inv_comm₀ (by positivity) ht.1]
        simpa [one_div] using ht.2
      set a : ℕ := ⌊t⁻¹⌋₊
      have ha_ge_A : A ≤ a := Nat.le_floor (by exact_mod_cast le_of_lt htinv_gt)
      have ha1 : 1 ≤ a := by omega
      have hflZ : ⌊t⁻¹⌋ = (a : ℤ) := by
        refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
        · exact_mod_cast Nat.floor_le (inv_nonneg.mpr ht.1.le)
        · exact_mod_cast Nat.lt_floor_add_one t⁻¹
      set t' : ℝ := Int.fract t⁻¹
      have ht'_eq : t' = t⁻¹ - (a : ℝ) := by
        dsimp only [t']
        rw [Int.fract, hflZ, Int.cast_natCast]
      have ht'_ge : 0 ≤ t' := Int.fract_nonneg t⁻¹
      have ht'_lt : t' < 1 := Int.fract_lt_one t⁻¹
      have ht'_ne : t' ≠ 0 := by
        intro h0
        have ha_eq : t⁻¹ = (a : ℝ) := by linarith [ht'_eq]
        have ht_rat : t = ((1 / a : ℚ) : ℝ) := by
          push_cast
          rw [← ha_eq, one_div, inv_inv]
        have hx_rat : ∃ q : ℚ, (q : ℝ) = x := by
          refine ⟨((M 0 0 : ℚ) + (M 0 1 : ℚ) * (1 / (a : ℚ))) /
            ((M 1 0 : ℚ) + (M 1 1 : ℚ) * (1 / (a : ℚ))), ?_⟩
          rw [← hmob, ht_rat]
          unfold mobius
          push_cast
          rfl
        exact hirr hx_rat
      have ht'_pos : 0 < t' := lt_of_le_of_ne ht'_ge (Ne.symm ht'_ne)
      have ht_step : t = 1 / ((a : ℝ) + t') := by
        have hay : (a : ℝ) + t' = t⁻¹ := by linarith [ht'_eq]
        rw [hay, one_div, inv_inv]
      have hcons : (0 :: (w ++ [a])) = (0 :: w) ++ [a] := rfl
      have hprod : cfProd (0 :: (w ++ [a])) = M * cfMat a := by
        rw [hcons, cfProd_append]
        simp [M, cfProd]
      have hmat_pos : (0 : ℝ) < ((cfMat a) 0 0 : ℝ) + ((cfMat a) 0 1 : ℝ) * t' := by
        simp only [cfMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_natCast, Int.cast_one, one_mul]
        linarith [show (1 : ℝ) ≤ (a : ℝ) from by exact_mod_cast ha1]
      have hmob_ext : mobius (cfProd (0 :: (w ++ [a]))) t' = x := by
        rw [← hmob, hprod, mobius_mul M (cfMat a) t' (ne_of_gt hmat_pos)]
        have harg : (((cfMat a) 1 0 : ℝ) + ((cfMat a) 1 1 : ℝ) * t') /
            (((cfMat a) 0 0 : ℝ) + ((cfMat a) 0 1 : ℝ) * t') = t := by
          simp only [cfMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_one, Int.cast_zero, zero_mul,
            add_zero, Int.cast_natCast, one_mul]
          exact ht_step.symm
        rw [harg]
      have hpd_ext : PosDigits (w ++ [a]) :=
        posDigits_append.mpr ⟨hw.1, posDigits_cons.mpr ⟨ha1, posDigits_nil⟩⟩
      have hne_ext : w ++ [a] ≠ [] := List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil a [])
      obtain ⟨htop_ext, hpen_ext⟩ := dens_mobius_top_and_penult hpd_ext hne_ext ht'_pos ht'_lt
      rw [hmob_ext, List.length_append, List.length_singleton] at htop_ext hpen_ext
      have hlen1 : 1 ≤ w.length := List.length_pos_of_ne_nil hw.2.1
      have hden_ext10 : (cfProd (0 :: (w ++ [a]))) 1 0 = (a : ℤ) * u + v := by
        rw [hprod, Matrix.mul_apply, Fin.sum_univ_two]
        simp [M, u, v, cfMat]; ring
      have hden_ext11 : (cfProd (0 :: (w ++ [a]))) 1 1 = u := by
        rw [hprod, Matrix.mul_apply, Fin.sum_univ_two]
        simp [M, u, cfMat]
      have hstop_j1 : cfStopIdx x (j + 1) = w.length := by
        refine (cfStopIdx_eq_of_bracket ?_ ?_).2
        · have hsub : w.length + 1 - 1 = w.length := by omega
          rw [← hsub, hpen_ext, hden_ext11]
          exact_mod_cast hle_cross
        · rw [htop_ext, hden_ext10]
          have hAu : (A : ℤ) * u ≤ (a : ℤ) * u :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast ha_ge_A) hu_posZ.le
          have : ((NoShortDim.H (j + 1) : ℕ) : ℤ) < (a : ℤ) * u + v := by linarith
          exact_mod_cast this
      have hstop_j : cfStopIdx x j = w.length - 1 := by
        obtain ⟨htop_w, hpen_w⟩ := dens_mobius_top_and_penult hw.1 hw.2.1 ht.1 ht1
        rw [hmob] at htop_w hpen_w
        have hsub : w.length - 1 + 1 = w.length := by omega
        refine (cfStopIdx_eq_of_bracket ?_ ?_).2
        · rw [hpen_w, cfDen_dropLast_eq hw.2.1]
          exact_mod_cast hw.2.2.2
        · rw [hsub, htop_w]
          exact_mod_cast hw.2.2.1
      refine ⟨hx_cyl, hx01, hirr, ?_⟩
      rw [hstop_j1, hstop_j]
      omega
    have hden0 : (M 1 0 : ℝ) + (M 1 1 : ℝ) * 0 ≠ 0 := by linarith
    have hdenA : (M 1 0 : ℝ) + (M 1 1 : ℝ) * (1 / (A : ℝ)) ≠ 0 := by positivity
    have hsubA := mobius_sub M 0 (1 / (A : ℝ)) hden0 hdenA
    have hdet_abs : |(-(M.det : ℝ) * (0 - 1 / (A : ℝ)))| = 1 / (A : ℝ) := by
      have hp : 0 < 1 / (A : ℝ) := by positivity
      rcases hdet with hd | hd <;> simp only [hd, Int.cast_one, Int.cast_neg, neg_neg, one_mul,
        neg_one_mul, zero_sub, abs_neg, abs_of_pos hp]
    have hdenA_eq : (u : ℝ) * ((u : ℝ) + (v : ℝ) * (1 / (A : ℝ))) =
        (u : ℝ) * ((A : ℝ) * (u : ℝ) + (v : ℝ)) / (A : ℝ) := by
      have hAne : (A : ℝ) ≠ 0 := by positivity
      field_simp
    have hJA_len : hiA - loA = 1 / ((u : ℝ) * ((A : ℝ) * (u : ℝ) + (v : ℝ))) := by
      have hmaxmin : hiA - loA = |mobius M 0 - mobius M (1 / (A : ℝ))| := by
        dsimp only [hiA, loA]
        rcases le_total (mobius M 0) (mobius M (1 / (A : ℝ))) with h | h
        · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
        · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      rw [hmaxmin, hsubA, abs_div, hdet_abs]
      change (1 / (A : ℝ)) / |((u : ℝ) + (v : ℝ) * 0) * ((u : ℝ) + (v : ℝ) * (1 / (A : ℝ)))| = _
      have hprod_pos : 0 < ((u : ℝ) + (v : ℝ) * 0) * ((u : ℝ) + (v : ℝ) * (1 / (A : ℝ))) := by
        positivity
      rw [abs_of_pos hprod_pos, mul_zero, add_zero, hdenA_eq]
      have hAne : (A : ℝ) ≠ 0 := by positivity
      have hune : (u : ℝ) ≠ 0 := ne_of_gt hu_posR
      field_simp
    have hHj_pos : 0 < ((NoShortDim.H j : ℕ) : ℝ) := by
      exact_mod_cast NoShortDim.H_ge_one j hj1
    have hH_rat : 1 ≤ ((NoShortDim.H (j + 1) : ℕ) : ℝ) / (u : ℝ) := by
      rw [one_le_div hu_posR]
      exact_mod_cast hle_cross
    have hA_le_2H :
        (A : ℝ) ≤ 2 * ((NoShortDim.H (j + 1) : ℕ) : ℝ) / ((NoShortDim.H j : ℕ) : ℝ) := by
      have hfl : ((NoShortDim.H (j + 1) / u.toNat : ℕ) : ℝ) ≤
          ((NoShortDim.H (j + 1) : ℕ) : ℝ) / (u : ℝ) := by
        rw [le_div_iff₀ hu_posR]
        have h1 : (NoShortDim.H (j + 1) / u.toNat) * u.toNat ≤ NoShortDim.H (j + 1) :=
          Nat.div_mul_le_self _ _
        have h2 : (((NoShortDim.H (j + 1) / u.toNat : ℕ) : ℝ)) * (u.toNat : ℝ) ≤
            ((NoShortDim.H (j + 1) : ℕ) : ℝ) := by exact_mod_cast h1
        have h3 : (u.toNat : ℝ) = (u : ℝ) := by exact_mod_cast hu_toNat
        rwa [h3] at h2
      have hA_eq : (A : ℝ) = ((NoShortDim.H (j + 1) / u.toNat : ℕ) : ℝ) + 1 := by
        push_cast [A]; rfl
      have h1_le : (A : ℝ) ≤ ((NoShortDim.H (j + 1) : ℕ) : ℝ) / (u : ℝ) + 1 := by linarith
      have h2_le : ((NoShortDim.H (j + 1) : ℕ) : ℝ) / (u : ℝ) + 1 ≤
          2 * ((NoShortDim.H (j + 1) : ℕ) : ℝ) / (u : ℝ) := by
        have hring : 2 * ((NoShortDim.H (j + 1) : ℕ) : ℝ) / (u : ℝ) =
            ((NoShortDim.H (j + 1) : ℕ) : ℝ) / (u : ℝ) +
              ((NoShortDim.H (j + 1) : ℕ) : ℝ) / (u : ℝ) := by ring
        linarith [hH_rat, hring]
      have h21 : 2 * ((NoShortDim.H (j + 1) : ℕ) : ℝ) / (u : ℝ) ≤
          2 * ((NoShortDim.H (j + 1) : ℕ) : ℝ) / ((NoShortDim.H j : ℕ) : ℝ) := by
        rw [div_le_div_iff₀ hu_posR hHj_pos]
        have hltR : ((NoShortDim.H j : ℕ) : ℝ) < (u : ℝ) := by exact_mod_cast hH_gtZ
        have hH1_nn : (0 : ℝ) ≤ ((NoShortDim.H (j + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith
      exact le_trans h1_le (le_trans h2_le h21)
    have hcore := WindowAndResidueCore.thm19_cond_prob_lower_bound
      ((NoShortDim.H j : ℕ) : ℝ) ((NoShortDim.H (j + 1) : ℕ) : ℝ)
      (u : ℝ) (v : ℝ) (A : ℝ)
      hHj_pos (by exact_mod_cast hH_gtZ) hv_nnR (by exact_mod_cast hv_le_u) hA1R hA_le_2H
    have hHj_rat : ((1 : ℝ) / 40) / (j : ℝ) ≤
        ((NoShortDim.H j : ℕ) : ℝ) / (2 * ((NoShortDim.H (j + 1) : ℕ) : ℝ)) := by
      have hhi := NoShortDim.H_ratio_hi j hj
      have hHj1_pos : (0 : ℝ) < ((NoShortDim.H (j + 1) : ℕ) : ℝ) := by
        exact_mod_cast NoShortDim.H_ge_one (j + 1) (by omega)
      have hmul : ((NoShortDim.H (j + 1) : ℕ) : ℝ) ≤
          20 * (j : ℝ) * ((NoShortDim.H j : ℕ) : ℝ) := (div_le_iff₀ hHj_pos).mp hhi
      rw [div_le_div_iff₀ hjpos (by positivity)]
      linarith
    have hprob_ge :
        ((1 : ℝ) / 40) / (j : ℝ) ≤ ((u : ℝ) + (v : ℝ)) / ((A : ℝ) * (u : ℝ) + (v : ℝ)) :=
      le_trans hHj_rat (le_trans hcore.1 hcore.2)
    have hvol_ratio : ((1 : ℝ) / 40) / (j : ℝ) * (1 / ((u : ℝ) * ((u : ℝ) + (v : ℝ)))) ≤
        1 / ((u : ℝ) * ((A : ℝ) * (u : ℝ) + (v : ℝ))) := by
      have h1 : (((1 : ℝ) / 40) / (j : ℝ)) / (u : ℝ) ≤
          ((u : ℝ) + (v : ℝ)) / ((u : ℝ) * ((A : ℝ) * (u : ℝ) + (v : ℝ))) := by
        have hdv := div_le_div_of_nonneg_right hprob_ge hu_posR.le
        calc (((1 : ℝ) / 40) / (j : ℝ)) / (u : ℝ)
            ≤ (((u : ℝ) + (v : ℝ)) / ((A : ℝ) * (u : ℝ) + (v : ℝ))) / (u : ℝ) := hdv
          _ = ((u : ℝ) + (v : ℝ)) / ((u : ℝ) * ((A : ℝ) * (u : ℝ) + (v : ℝ))) := by
              rw [div_div, mul_comm ((A : ℝ) * (u : ℝ) + (v : ℝ)) (u : ℝ)]
      have h2 := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (u : ℝ) + (v : ℝ))
      have hu_ne : (u : ℝ) ≠ 0 := ne_of_gt hu_posR
      have huv_ne : (u : ℝ) + (v : ℝ) ≠ 0 := by positivity
      have hAu_ne : (A : ℝ) * (u : ℝ) + (v : ℝ) ≠ 0 := by positivity
      calc ((1 : ℝ) / 40) / (j : ℝ) * (1 / ((u : ℝ) * ((u : ℝ) + (v : ℝ))))
          = (((1 : ℝ) / 40) / (j : ℝ) / (u : ℝ)) / ((u : ℝ) + (v : ℝ)) := by field_simp
        _ ≤ (((u : ℝ) + (v : ℝ)) / ((u : ℝ) * ((A : ℝ) * (u : ℝ) + (v : ℝ)))) /
              ((u : ℝ) + (v : ℝ)) := h2
        _ = 1 / ((u : ℝ) * ((A : ℝ) * (u : ℝ) + (v : ℝ))) := by field_simp
    have hcyl_len : (cylPair w).2 - (cylPair w).1 =
        1 / ((u : ℝ) * ((u : ℝ) + (v : ℝ))) := cylPair_len hw.1 hw.2.1
    have hnull_q : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
      (Set.countable_range ((↑) : ℚ → ℝ)).measure_zero volume
    have hvol_cyl : volume (Set.Ioo (cylPair w).1 (cylPair w).2) =
        ENNReal.ofReal (1 / ((u : ℝ) * ((u : ℝ) + (v : ℝ)))) := by
      rw [Real.volume_Ioo, hcyl_len]
    have hvol_JA : volume (Set.Ioo loA hiA) =
        ENNReal.ofReal (1 / ((u : ℝ) * ((A : ℝ) * (u : ℝ) + (v : ℝ)))) := by
      rw [Real.volume_Ioo, hJA_len]
    calc ENNReal.ofReal (((1 : ℝ) / 40) / (j : ℝ)) * volume (Set.Ioo (cylPair w).1 (cylPair w).2)
        = ENNReal.ofReal (((1 : ℝ) / 40) / (j : ℝ) * (1 / ((u : ℝ) * ((u : ℝ) + (v : ℝ))))) := by
          rw [hvol_cyl, ← ENNReal.ofReal_mul hrat_pos.le]
      _ ≤ volume (Set.Ioo loA hiA) := by
          rw [hvol_JA]
          exact ENNReal.ofReal_le_ofReal hvol_ratio
      _ = volume (Set.Ioo loA hiA \ Set.range ((↑) : ℚ → ℝ)) :=
          (measure_sdiff_null hnull_q).symm
      _ ≤ volume (Set.Ioo (cylPair w).1 (cylPair w).2 ∩ shortWinEvent j) :=
          measure_mono hJA_sub_ev

/-! ### Part 4: One-step tower contraction & unconditional `thm:short-ae` / `thm:no-short-dim` -/

theorem atom_exp_neg_shortWinCount_step {j : ℕ} (hj : 3 ≤ j) {w : List ℕ} (hw : isStoppedWord j w) :
    ∫⁻ x in Set.Ioo (cylPair w).1 (cylPair w).2,
        ENNReal.ofReal (Real.exp (-shortWinCount j x)) ≤
      ENNReal.ofReal (Real.exp (-((1 - Real.exp (-1)) * ((1 : ℝ) / 40)) / (j : ℝ))) *
        ∫⁻ x in Set.Ioo (cylPair w).1 (cylPair w).2,
          ENNReal.ofReal (Real.exp (-shortWinCount (j - 1) x)) := by
  let S : Set ℝ := Set.Ioo (cylPair w).1 (cylPair w).2
  let E : Set ℝ := shortWinEvent j
  have hQ_null : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    (Set.countable_range ((↑) : ℚ → ℝ)).measure_zero volume
  have hnotQ : ∀ᵐ x ∂(volume.restrict S), x ∉ Set.range ((↑) : ℚ → ℝ) := by
    rw [ae_iff]
    simp only [not_not]
    have h : volume.restrict S {a : ℝ | a ∈ Set.range ((↑) : ℚ → ℝ)} ≤
        volume (Set.range ((↑) : ℚ → ℝ)) := Measure.restrict_le_self _
    exact le_antisymm (h.trans (le_of_eq hQ_null)) bot_le
  have hL_ae : (fun x => ENNReal.ofReal (Real.exp (-shortWinCount j x))) =ᵐ[volume.restrict S]
      (fun x => ENNReal.ofReal (Real.exp (-zPrev j w)) *
        (E.indicator (fun _ => ENNReal.ofReal (Real.exp (-1))) x +
          Eᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hnotQ] with x hxS hxQ
    have hirr : Irrational x := fun ⟨q, hq⟩ => hxQ ⟨q, hq⟩
    rw [shortWinCount_succ_eq_on_atom (by omega : 1 ≤ j) hw hirr hxS]
    by_cases hxE : x ∈ E
    · have hne : -(zPrev j w + (if x ∈ E then (1 : ℝ) else 0)) = -zPrev j w + -1 := by
        simp [hxE]; ring
      rw [hne, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      rw [Set.indicator_of_mem hxE, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hxE),
        add_zero]
    · have hne : -(zPrev j w + (if x ∈ E then (1 : ℝ) else 0)) = -zPrev j w := by
        simp [hxE]
      rw [hne, Set.indicator_of_notMem hxE, Set.indicator_of_mem (Set.mem_compl hxE),
        zero_add, mul_one]
  have hR_ae : (fun x => ENNReal.ofReal (Real.exp (-shortWinCount (j - 1) x))) =ᵐ[volume.restrict S]
      fun _ => ENNReal.ofReal (Real.exp (-zPrev j w)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hnotQ] with x hxS hxQ
    have hirr : Irrational x := fun ⟨q, hq⟩ => hxQ ⟨q, hq⟩
    rw [shortWinCount_pred_eq_on_atom (by omega : 1 ≤ j) hw hirr hxS]
  have hE_meas : MeasurableSet E := measurableSet_shortWinEvent j (by omega : 1 ≤ j)
  have hL_eval : ∫⁻ x in S, ENNReal.ofReal (Real.exp (-shortWinCount j x)) =
      ENNReal.ofReal (Real.exp (-zPrev j w)) *
        (ENNReal.ofReal (Real.exp (-1)) * volume (S ∩ E) + volume (S \ E)) := by
    rw [lintegral_congr_ae hL_ae]
    let g1 : ℝ → ℝ≥0∞ := E.indicator (fun _ : ℝ => ENNReal.ofReal (Real.exp (-1)))
    let g2 : ℝ → ℝ≥0∞ := Eᶜ.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
    have hg1 : Measurable g1 := measurable_const.indicator hE_meas
    have hg2 : Measurable g2 := measurable_const.indicator hE_meas.compl
    have hmul := lintegral_const_mul (ENNReal.ofReal (Real.exp (-zPrev j w))) (hg1.add hg2)
      (μ := volume.restrict S)
    have hpi : (fun x => ENNReal.ofReal (Real.exp (-zPrev j w)) *
        (E.indicator (fun _ => ENNReal.ofReal (Real.exp (-1))) x +
          Eᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x)) =
        (fun x => ENNReal.ofReal (Real.exp (-zPrev j w)) * ((g1 + g2) x)) := rfl
    rw [hpi, hmul]
    congr 1
    rw [Pi.add_def, lintegral_add_left hg1]
    dsimp only [g1, g2]
    rw [lintegral_indicator hE_meas, lintegral_indicator hE_meas.compl]
    simp only [setLIntegral_const]
    have h1 : (volume.restrict S) E = volume (S ∩ E) := by
      rw [Measure.restrict_apply hE_meas, Set.inter_comm]
    have h2 : (volume.restrict S) Eᶜ = volume (S \ E) := by
      rw [Measure.restrict_apply hE_meas.compl, ← Set.sdiff_eq_compl_inter]
    rw [h1, h2]
    ring
  have hR_eval : ∫⁻ x in S, ENNReal.ofReal (Real.exp (-shortWinCount (j - 1) x)) =
      ENNReal.ofReal (Real.exp (-zPrev j w)) * volume S := by
    rw [lintegral_congr_ae hR_ae, setLIntegral_const]
  have hS_pos : 0 < volume S := by
    have hlen := cylPair_len hw.1 hw.2.1
    have hu_pos : (0 : ℝ) < ((cfProd (0 :: w)) 1 0 : ℝ) := by exact_mod_cast cfDen_pos hw.1
    have hv_nn : (0 : ℝ) ≤ ((cfProd (0 :: w)) 1 1 : ℝ) := by
      exact_mod_cast cfProd_nonneg (0 :: w) 1 1
    have hpos_len : 0 < (cylPair w).2 - (cylPair w).1 := by rw [hlen]; positivity
    dsimp only [S]
    rw [Real.volume_Ioo, ENNReal.ofReal_pos]
    exact hpos_len
  have hS_ne_top : volume S ≠ ⊤ := by
    dsimp only [S]
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  set pReal : ℝ := (volume (S ∩ E)).toReal / (volume S).toReal
  have hSE_le_S : volume (S ∩ E) ≤ volume S := measure_mono Set.inter_subset_left
  have hSE_ne_top : volume (S ∩ E) ≠ ⊤ := ne_top_of_le_ne_top hS_ne_top hSE_le_S
  have hS_toReal_pos : 0 < (volume S).toReal := ENNReal.toReal_pos hS_pos.ne' hS_ne_top
  have hp_ge : ((1 : ℝ) / 40) / (j : ℝ) ≤ pReal := by
    have hvol_ge := atom_shortWin_volume_ge hj hw
    have hrat_nn : 0 ≤ ((1 : ℝ) / 40) / (j : ℝ) := by positivity
    have h1 := ENNReal.toReal_mono hSE_ne_top hvol_ge
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hrat_nn] at h1
    calc ((1 : ℝ) / 40) / (j : ℝ)
        = ((((1 : ℝ) / 40) / (j : ℝ)) * (volume S).toReal) / (volume S).toReal :=
          (mul_div_cancel_right₀ _ hS_toReal_pos.ne').symm
      _ ≤ (volume (S ∩ E)).toReal / (volume S).toReal :=
          div_le_div_of_nonneg_right h1 hS_toReal_pos.le
  have hS_split : volume (S ∩ E) + volume (S \ E) = volume S := by
    have hdisj : Disjoint (S ∩ E) (S \ E) :=
      Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1.2
    rw [← measure_union hdisj (measurableSet_Ioo.diff hE_meas)]
    congr 1
    exact Set.inter_union_sdiff S E
  have hS_diff_eq : (volume (S \ E)).toReal = (volume S).toReal - (volume (S ∩ E)).toReal := by
    have hdiff_ne_top : volume (S \ E) ≠ ⊤ :=
      ne_top_of_le_ne_top hS_ne_top (measure_mono Set.sdiff_subset)
    have htr := congrArg ENNReal.toReal hS_split
    rw [ENNReal.toReal_add hSE_ne_top hdiff_ne_top] at htr
    linarith
  have hfactor := WindowShortAe.short_ae_one_step_factor ((1 : ℝ) / 40) pReal j
    (by norm_num) (by omega) hp_ge
  have hcomb_real : Real.exp (-1) * (volume (S ∩ E)).toReal + (volume (S \ E)).toReal =
      (volume S).toReal * (Real.exp (-1) * pReal + (1 - pReal)) := by
    have hp_mul : pReal * (volume S).toReal = (volume (S ∩ E)).toReal :=
      div_mul_cancel₀ _ hS_toReal_pos.ne'
    calc Real.exp (-1) * (volume (S ∩ E)).toReal + (volume (S \ E)).toReal
        = Real.exp (-1) * (pReal * (volume S).toReal) +
            ((volume S).toReal - pReal * (volume S).toReal) := by
          rw [hS_diff_eq, hp_mul]
      _ = (volume S).toReal * (Real.exp (-1) * pReal + (1 - pReal)) := by ring
  have hcomb_le : Real.exp (-1) * (volume (S ∩ E)).toReal + (volume (S \ E)).toReal ≤
      Real.exp (-((1 - Real.exp (-1)) * ((1 : ℝ) / 40)) / (j : ℝ)) * (volume S).toReal := by
    rw [hcomb_real, mul_comm (volume S).toReal _]
    exact mul_le_mul_of_nonneg_right hfactor hS_toReal_pos.le
  have hcomb_E : ENNReal.ofReal (Real.exp (-1)) * volume (S ∩ E) + volume (S \ E) ≤
      ENNReal.ofReal (Real.exp (-((1 - Real.exp (-1)) * ((1 : ℝ) / 40)) / (j : ℝ))) * volume S := by
    have hdiff_ne_top : volume (S \ E) ≠ ⊤ :=
      ne_top_of_le_ne_top hS_ne_top (measure_mono Set.sdiff_subset)
    rw [← ENNReal.ofReal_toReal hSE_ne_top, ← ENNReal.ofReal_toReal hdiff_ne_top,
      ← ENNReal.ofReal_toReal hS_ne_top,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
        ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal hcomb_le
  rw [hL_eval, hR_eval]
  calc ENNReal.ofReal (Real.exp (-zPrev j w)) *
        (ENNReal.ofReal (Real.exp (-1)) * volume (S ∩ E) + volume (S \ E))
      ≤ ENNReal.ofReal (Real.exp (-zPrev j w)) *
          (ENNReal.ofReal (Real.exp (-((1 - Real.exp (-1)) * ((1 : ℝ) / 40)) / (j : ℝ))) *
            volume S) := mul_le_mul_of_nonneg_left hcomb_E bot_le
    _ = ENNReal.ofReal (Real.exp (-((1 - Real.exp (-1)) * ((1 : ℝ) / 40)) / (j : ℝ))) *
          (ENNReal.ofReal (Real.exp (-zPrev j w)) * volume S) := by ring

theorem integral_exp_neg_shortWinCount_step {j : ℕ} (hj : 3 ≤ j) :
    (∫ x, Real.exp (-shortWinCount j x) ∂unitVol) ≤
      (∫ x, Real.exp (-shortWinCount (j - 1) x) ∂unitVol) *
        Real.exp (-((1 - Real.exp (-1)) * ((1 : ℝ) / 40)) / (j : ℝ)) := by
  let b : ℝ := (1 - Real.exp (-1)) * ((1 : ℝ) / 40)
  have hj1 : 1 ≤ j := by omega
  have hcnt := stoppedWordSet_countable j
  let : Countable (stoppedWordSet j) := hcnt.to_subtype
  have h_disj : Pairwise fun w₁ w₂ : stoppedWordSet j =>
      Disjoint (Set.Ioo (cylPair w₁.1).1 (cylPair w₁.1).2)
        (Set.Ioo (cylPair w₂.1).1 (cylPair w₂.1).2) := by
    intro w₁ w₂ hne
    exact stoppedWords_disjoint w₁.2 w₂.2 (fun h => hne (Subtype.ext h))
  have h_meas : ∀ w : stoppedWordSet j,
      MeasurableSet (Set.Ioo (cylPair w.1).1 (cylPair w.1).2) :=
    fun _ => measurableSet_Ioo
  have hU_eq : (⋃ w : stoppedWordSet j, Set.Ioo (cylPair w.1).1 (cylPair w.1).2) =
      ⋃ w ∈ stoppedWordSet j, Set.Ioo (cylPair w).1 (cylPair w).2 := by
    ext x; simp
  have h_rest_eq : ∀ w : stoppedWordSet j,
      unitVol.restrict (Set.Ioo (cylPair w.1).1 (cylPair w.1).2) =
        volume.restrict (Set.Ioo (cylPair w.1).1 (cylPair w.1).2) := by
    intro w
    rw [unitVol, Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.mpr (cylPair_subset_Ioo_unit_of_stopped w.2)]
  have h_eq_lint : ∀ n : ℕ,
      ∫⁻ x, ENNReal.ofReal (Real.exp (-shortWinCount n x)) ∂unitVol =
        ∑' w : stoppedWordSet j,
          ∫⁻ x in Set.Ioo (cylPair w.1).1 (cylPair w.1).2,
            ENNReal.ofReal (Real.exp (-shortWinCount n x)) := by
    intro n
    have hae := stoppedWords_cyl_ae_mem j hj1
    have hrest_unit : unitVol.restrict (⋃ w : stoppedWordSet j,
        Set.Ioo (cylPair w.1).1 (cylPair w.1).2) = unitVol := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      filter_upwards [hae] with x hx
      rw [hU_eq]
      exact hx
    calc ∫⁻ x, ENNReal.ofReal (Real.exp (-shortWinCount n x)) ∂unitVol
        = ∫⁻ x in ⋃ w : stoppedWordSet j, Set.Ioo (cylPair w.1).1 (cylPair w.1).2,
            ENNReal.ofReal (Real.exp (-shortWinCount n x)) ∂unitVol := by
          rw [hrest_unit]
      _ = ∑' w : stoppedWordSet j,
            ∫⁻ x in Set.Ioo (cylPair w.1).1 (cylPair w.1).2,
              ENNReal.ofReal (Real.exp (-shortWinCount n x)) ∂unitVol :=
          lintegral_iUnion h_meas h_disj _
      _ = ∑' w : stoppedWordSet j,
            ∫⁻ x in Set.Ioo (cylPair w.1).1 (cylPair w.1).2,
              ENNReal.ofReal (Real.exp (-shortWinCount n x)) := by
          congr 1; funext w; rw [h_rest_eq w]
  have h_lint_step :
      ∫⁻ x, ENNReal.ofReal (Real.exp (-shortWinCount j x)) ∂unitVol ≤
        ENNReal.ofReal (Real.exp (-b / (j : ℝ))) *
          ∫⁻ x, ENNReal.ofReal (Real.exp (-shortWinCount (j - 1) x)) ∂unitVol := by
    rw [h_eq_lint j, h_eq_lint (j - 1), ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun w => atom_exp_neg_shortWinCount_step hj w.2
  have h_bridge : ∀ n : ℕ,
      ENNReal.ofReal (∫ x, Real.exp (-shortWinCount n x) ∂unitVol) =
        ∫⁻ x, ENNReal.ofReal (Real.exp (-shortWinCount n x)) ∂unitVol := by
    intro n
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_neg_shortWinCount n) (Eventually.of_forall fun _ => (Real.exp_pos _).le)
  have h_int_nn : ∀ n : ℕ, 0 ≤ ∫ x, Real.exp (-shortWinCount n x) ∂unitVol :=
    fun n => integral_nonneg fun _ => (Real.exp_pos _).le
  rw [← h_bridge j, ← h_bridge (j - 1), ← ENNReal.ofReal_mul (Real.exp_pos _).le] at h_lint_step
  have hReal : (∫ x, Real.exp (-shortWinCount j x) ∂unitVol) ≤
      (∫ x, Real.exp (-shortWinCount (j - 1) x) ∂unitVol) *
        Real.exp (-((1 - Real.exp (-1)) * ((1 : ℝ) / 40)) / (j : ℝ)) := by
    have hmul_nn := mul_nonneg (Real.exp_pos (-b / (j : ℝ))).le (h_int_nn (j - 1))
    have hreal := (ENNReal.ofReal_le_ofReal_iff hmul_nn).mp h_lint_step
    linarith [hreal]
  exact hReal

/-- **Unconditional Layer-A `thm:short-ae`**: for Lebesgue-almost every `x ∈ (0, 1)`,
    the number of short Hermite windows up to `J` satisfies `c * log J ≤ Z_J(x)`
    for all sufficiently large `J`, with explicit `c = (1 - e⁻¹) / 160 > 0`. -/
theorem thm_short_ae_explicit :
    ∀ᵐ x ∂unitVol, ∃ M : ℕ, ∀ J : ℕ, M ≤ J →
      (((1 - Real.exp (-1)) * ((1 : ℝ) / 40)) / 4) * Real.log (J : ℝ) ≤ shortWinCount J x := by
  let c0 : ℝ := (1 : ℝ) / 40
  let b : ℝ := (1 - Real.exp (-1)) * c0
  have hc0 : 0 < c0 := by norm_num
  have hexp1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hb : 0 < b := mul_pos (by linarith) hc0
  let Bset : ℕ → Set ℝ := fun m =>
    {x : ℝ | shortWinCount (2 ^ m) x < (b / 2) * Real.log ((((2 ^ m : ℕ))) : ℝ)}
  have hInit : ∫ x, Real.exp (-shortWinCount 0 x) ∂unitVol ≤ 1 := by
    have hzero : (fun x => Real.exp (-shortWinCount 0 x)) = fun _ => (1 : ℝ) := by
      funext x
      simp [shortWinCount]
    rw [hzero, integral_const, smul_eq_mul, mul_one, Measure.real_def, unitVol,
      Measure.restrict_apply_univ, Real.volume_Ioo]
    norm_num
  have htriv : ∀ j : ℕ, 1 ≤ j → j < 3 →
      (∫ x, Real.exp (-shortWinCount j x) ∂unitVol) ≤
        ∫ x, Real.exp (-shortWinCount (j - 1) x) ∂unitVol := by
    intro j hj1 _
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => (Real.exp_pos _).le)
      (integrable_exp_neg_shortWinCount (j - 1)) (Eventually.of_forall fun x => ?_)
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    unfold shortWinCount
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (Nat.sub_le j 1))
      (fun i _ _ => by by_cases h : x ∈ shortWinEvent i <;> simp [h])
  have hmain := WindowShortAe.short_ae_main
    unitVol shortWinCount Bset b c0 3 hb hc0 (by norm_num) rfl
    (fun J x => by
      unfold shortWinCount
      exact Finset.sum_nonneg fun j _ => by by_cases h : x ∈ shortWinEvent j <;> simp [h])
    (fun x i k hik => by
      unfold shortWinCount
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hik)
        (fun j _ _ => by by_cases h : x ∈ shortWinEvent j <;> simp [h]))
    (fun _ _ => Iff.rfl)
    integrable_exp_neg_shortWinCount
    hInit
    htriv
    (fun j hj => integral_exp_neg_shortWinCount_step hj)
  exact hmain.2.2

/-- **Unconditional Layer-A `thm:short-ae` (existential statement matching Paper 2)**. -/
theorem thm_short_ae :
    ∃ c : ℝ, 0 < c ∧
      ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), ∃ M : ℕ, ∀ J : ℕ, M ≤ J →
        c * Real.log (J : ℝ) ≤
          ((Finset.filter (fun j => Irrational x ∧ cfStopIdx x (j + 1) - cfStopIdx x j ≤ 1)
            (Finset.Icc 1 J)).card : ℝ) := by
  let c : ℝ := ((1 - Real.exp (-1)) * ((1 : ℝ) / 40)) / 4
  have hc : 0 < c := by
    have hexp1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    dsimp only [c]
    positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [thm_short_ae_explicit, ae_restrict_mem measurableSet_Ioo] with x ⟨M, hM⟩ hx01
  refine ⟨M, fun J hJ => ?_⟩
  have hcnt_eq :
      shortWinCount J x =
        ((Finset.filter (fun j => Irrational x ∧ cfStopIdx x (j + 1) - cfStopIdx x j ≤ 1)
          (Finset.Icc 1 J)).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    unfold shortWinCount
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : Irrational x ∧ cfStopIdx x (j + 1) - cfStopIdx x j ≤ 1
    · have hE : x ∈ shortWinEvent j := ⟨hx01, h⟩
      simp [hE, h]
    · have hE : x ∉ shortWinEvent j := fun hE => h hE.2
      have hlhs : (if x ∈ shortWinEvent j then (1 : ℝ) else 0) = 0 := by
        simp only [hE, ↓reduceIte]
      have hrhs : (if Irrational x ∧ cfStopIdx x (j + 1) - cfStopIdx x j ≤ 1
          then 1 else 0) = 0 := by
        simp only [h, ↓reduceIte]
      rw [hlhs, hrhs]
      simp
  rw [← hcnt_eq]
  exact hM J hJ

/-- **Unconditional Layer-A Lebesgue-nullity half of `thm:no-short-dim`**:
    for any parity sequence `ε : ℕ → Bool`, `volume (divWindowSet ε) = 0`. -/
theorem volume_divWindowSet_eq_zero (ε : ℕ → Bool) : volume (divWindowSet ε) = 0 := by
  let c : ℝ := ((1 - Real.exp (-1)) * ((1 : ℝ) / 40)) / 4
  have hc : 0 < c := by
    have hexp1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    dsimp only [c]
    positivity
  have hnull_unit : unitVol (divWindowSet ε) = 0 := by
    refine measure_mono_null (s := divWindowSet ε)
      (t := {x : ℝ | ¬ ∃ M : ℕ, ∀ J : ℕ, M ≤ J → c * Real.log (J : ℝ) ≤ shortWinCount J x})
      ?_ (ae_iff.mp thm_short_ae_explicit)
    intro x ⟨_, _, _, htend⟩ ⟨M, hM⟩
    obtain ⟨J1, hJ1⟩ := Filter.eventually_atTop.mp (htend.eventually_ge_atTop 2)
    have hle_J1 : ∀ J : ℕ, shortWinCount J x ≤ (J1 : ℝ) := by
      intro J
      unfold shortWinCount
      have hsub : ∀ j ∈ Finset.Icc 1 J,
          (if x ∈ shortWinEvent j then (1 : ℝ) else 0) ≤
            if j ∈ Finset.Ico 0 J1 then (1 : ℝ) else 0 := by
        intro j _
        by_cases hjJ1 : j < J1
        · by_cases hxE : x ∈ shortWinEvent j <;>
            simp only [hxE, Finset.mem_Ico, Nat.zero_le, hjJ1, and_self, ↓reduceIte, le_refl,
              zero_le_one]
        · have hj_ge : J1 ≤ j := by omega
          have h2 : 2 ≤ cfStopIdx x (j + 1) - cfStopIdx x j := hJ1 j hj_ge
          have hnot : x ∉ shortWinEvent j := by
            intro h
            have := h.2.2
            omega
          simp only [hnot, ↓reduceIte, Finset.mem_Ico, Nat.zero_le, hjJ1, and_false, le_refl]
      have hnn_ico : ∀ j : ℕ, (0 : ℝ) ≤ if j ∈ Finset.Ico 0 J1 then (1 : ℝ) else 0 := by
        intro j
        by_cases hm : j < J1 <;>
          simp only [Finset.mem_Ico, Nat.zero_le, hm, and_self, and_false, ↓reduceIte, le_refl,
            zero_le_one]
      calc ∑ j ∈ Finset.Icc 1 J, (if x ∈ shortWinEvent j then (1 : ℝ) else 0)
          ≤ ∑ j ∈ Finset.Icc 1 J, (if j ∈ Finset.Ico 0 J1 then (1 : ℝ) else 0) :=
            Finset.sum_le_sum hsub
        _ ≤ ∑ j ∈ Finset.Icc 0 (J + J1), (if j ∈ Finset.Ico 0 J1 then (1 : ℝ) else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) (by omega))
              (fun j _ _ => hnn_ico j)
        _ = ((Finset.Icc 0 (J + J1) ∩ Finset.Ico 0 J1).card : ℝ) := by
            rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul,
              mul_one]
        _ ≤ ((Finset.Ico 0 J1).card : ℝ) := by
            exact_mod_cast Finset.card_le_card Finset.inter_subset_right
        _ = (J1 : ℝ) := by simp
    set J : ℕ := max M (Nat.ceil (Real.exp (((J1 : ℝ) + 1) / c)) + 1)
    have hMJ : M ≤ J := le_max_left _ _
    have hJ_gt : Real.exp (((J1 : ℝ) + 1) / c) < (J : ℝ) := by
      have h1 : Real.exp (((J1 : ℝ) + 1) / c) ≤
          (Nat.ceil (Real.exp (((J1 : ℝ) + 1) / c)) : ℝ) := Nat.le_ceil _
      have hle_nat : Nat.ceil (Real.exp (((J1 : ℝ) + 1) / c)) + 1 ≤ J := le_max_right _ _
      have h2 : (Nat.ceil (Real.exp (((J1 : ℝ) + 1) / c)) : ℝ) + 1 ≤ (J : ℝ) := by
        exact_mod_cast hle_nat
      linarith
    have hlog : ((J1 : ℝ) + 1) / c < Real.log (J : ℝ) := by
      have h1 := Real.log_lt_log (Real.exp_pos _) hJ_gt
      rwa [Real.log_exp] at h1
    have hclog : (J1 : ℝ) + 1 < c * Real.log (J : ℝ) := (div_lt_iff₀' hc).mp hlog
    linarith [hM J hMJ, hle_J1 J]
  have hsub_unit : divWindowSet ε ⊆ Set.Ioo (0 : ℝ) 1 := fun _ hx => hx.1
  rw [unitVol, Measure.restrict_apply' measurableSet_Ioo, Set.inter_eq_left.mpr hsub_unit]
    at hnull_unit
  exact hnull_unit

/-- **Complete Layer-A `thm:no-short-dim`**:
    `dimH (divWindowSet ε) = 1 ∧ volume (divWindowSet ε) = 0`. -/
theorem thm_no_short_dim_complete (ε : ℕ → Bool) :
    dimH (divWindowSet ε) = 1 ∧ volume (divWindowSet ε) = 0 :=
  ⟨dimH_divWindowSet_eq_one ε, volume_divWindowSet_eq_zero ε⟩

#print axioms WindowShortAeRealize.cfStopIdx_spec_of_irrational
#print axioms WindowShortAeRealize.stoppedWords_incomparable
#print axioms WindowShortAeRealize.stoppedWords_disjoint
#print axioms WindowShortAeRealize.stoppedWords_cover_irrationals
#print axioms WindowShortAeRealize.stoppedWords_cyl_ae_mem
#print axioms WindowShortAeRealize.cfStopIdx_const_on_stoppedCyl
#print axioms WindowShortAeRealize.measurableSet_shortWinEvent
#print axioms WindowShortAeRealize.atom_shortWin_volume_ge
#print axioms WindowShortAeRealize.atom_exp_neg_shortWinCount_step
#print axioms WindowShortAeRealize.integral_exp_neg_shortWinCount_step
#print axioms WindowShortAeRealize.thm_short_ae_explicit
#print axioms WindowShortAeRealize.thm_short_ae
#print axioms WindowShortAeRealize.volume_divWindowSet_eq_zero
#print axioms WindowShortAeRealize.thm_no_short_dim_complete

end
end WindowShortAeRealize
