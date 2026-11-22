import EpiFormal.FiniteStateTail
import EpiFormal.FiniteStatePositive
import EpiFormal.GaugeLiminfComplete

/-!
# Complete Unconditional Proof of `thm:finite-state-tail` (`ℝ` and `UnitAddCircle`)

Proves Paper 2's Theorem `thm:finite-state-tail` unconditionally in Lean 4 on core axioms
(`[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero external probabilistic/analytic
hypotheses):

1. Deterministic finite-state graphs (`Deterministic edges`: distinct outgoing edge labels at each
   vertex) embed faithfully into the Cantor coding tree `cantorTreeC k` via `wordOfPath` and
   `graphTree`, whose points lie in `fixedTail` / `eventualTail`.
2. Direct finite-sum Frostman positivity (`mkMetric_graphTree_pos`): Perron eigenvector weights
   telescope cleanly over `Path` prefixes (`sum_perron_weight_fiber`) and collide at most twice per
   small cover element, yielding `0 < Measure.mkMetric (interpGauge growth) (graphTree ...)`.
3. Unmarked tail nullity (`mkMetric_unmarkedTail_null`): deleting a marked edge forces a uniform
   spectral contraction at `L = Fintype.card V` via backward reachability stabilization, giving a
   strict factor `θ < 1` and `Measure.mkMetric (interpGauge growth) (graphTree \ exactTail) = 0`.
4. Lattice invariance (`eventually_defect_add_latticeL`, `exactTail_add_latticeL`) plugs directly
   into `GaugeCircle.mkMetric_inter_Ioo_eq_top_of_compact_tree` for local infinitude on every
   nonempty open interval `(a, b) ⊆ ℝ` and every nonempty open `U ⊆ UnitAddCircle`.
5. Arbitrary-gauge comparison & multi-component assembly (`thm_finite_state_tail_complete` on `ℝ`,
   `thm_finite_state_tail_circle_complete` on `UnitAddCircle`).
-/

open Filter Topology Set MeasureTheory Classification SpectralGap FullSpectrumDiscrete
open GaugeNull GaugeExact GaugeCircle GaugeLiminf GaugeScaleComparison FiniteStateGauge
open scoped ENNReal NNReal BigOperators

namespace FiniteStateComplete

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Part 1: Exact finite-state sets, deterministic paths, and `graphTree` -/

/-- Exact level-`k/4` slice of `eventualTail edges` on `ℝ`. -/
def exactTail {V : Type*} (edges : V → V → Finset ℤ) (k : ℕ) : Set ℝ :=
  eventualTail edges ∩ {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)}

/-- Exact level-`k/4` finite-state tail set projected to `UnitAddCircle`. -/
def circleExactTail {V : Type*} (edges : V → V → Finset ℤ) (k : ℕ) : Set UnitAddCircle :=
  circleProj '' exactTail edges k

/-- Outgoing edge labels at each vertex uniquely determine target vertices (Paper 2 §6). -/
def Deterministic {V : Type*} (edges : V → V → Finset ℤ) : Prop :=
  ∀ v u₁ u₂ : V, ∀ a : ℤ, a ∈ edges v u₁ → a ∈ edges v u₂ → u₁ = u₂

/-- Edge labels lie in `{-k, ..., k}`. -/
def edgeLabelsLe {V : Type*} (edges : V → V → Finset ℤ) (k : ℕ) : Prop :=
  ∀ v u : V, ∀ a ∈ edges v u, |a| ≤ (k : ℤ)

private def backReach {V : Type*} [Fintype V] (edges : V → V → Finset ℤ) (u₁ : V) :
    ℕ → Finset V
  | 0 => {u₁}
  | n + 1 => backReach edges u₁ n ∪
      Finset.univ.filter (fun v => ∃ u ∈ backReach edges u₁ n, (edges v u).Nonempty)

private lemma local_ediam_thickening_le {A : Set ℝ} {ρ : ℝ} (_hρ : 0 ≤ ρ) :
    Metric.ediam (Metric.thickening ρ A) ≤ Metric.ediam A + 2 * ENNReal.ofReal ρ := by
  rw [Metric.ediam_le_iff]
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := Metric.mem_thickening_iff.mp hx
  obtain ⟨b, hb, hyb⟩ := Metric.mem_thickening_iff.mp hy
  have h1 : edist x a ≤ ENNReal.ofReal ρ := by
    rw [edist_dist]; exact ENNReal.ofReal_le_ofReal hxa.le
  have h2 : edist b y ≤ ENNReal.ofReal ρ := by
    rw [edist_comm, edist_dist]; exact ENNReal.ofReal_le_ofReal hyb.le
  have h3 : edist a b ≤ Metric.ediam A := Metric.edist_le_ediam_of_mem ha hb
  calc edist x y ≤ edist x a + edist a b + edist b y := edist_triangle4 x a b y
    _ ≤ ENNReal.ofReal ρ + Metric.ediam A + ENNReal.ofReal ρ := by gcongr
    _ = Metric.ediam A + 2 * ENNReal.ofReal ρ := by ring

private lemma local_diam_thickening_pos {s : Set ℝ} {δ : ℝ} (hne : s.Nonempty) (hδ : 0 < δ)
    (hbdd : Bornology.IsBounded (Metric.thickening δ s)) :
    0 < Metric.diam (Metric.thickening δ s) := by
  obtain ⟨x, hx⟩ := hne
  have hball : Metric.ball x δ ⊆ Metric.thickening δ s :=
    Metric.ball_subset_thickening hx δ
  have hy1 : x - δ / 2 ∈ Metric.thickening δ s := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : |x - δ / 2 - x| = δ / 2 := by
      have e1 : x - δ / 2 - x = -(δ / 2) := by ring
      rw [e1, abs_neg, abs_of_pos (half_pos hδ)]
    rw [h1]; linarith
  have hy2 : x + δ / 2 ∈ Metric.thickening δ s := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have h2 : |x + δ / 2 - x| = δ / 2 := by
      have e2 : x + δ / 2 - x = δ / 2 := by ring
      rw [e2, abs_of_pos (half_pos hδ)]
    rw [h2]; linarith
  have hdist : (δ : ℝ) ≤ dist (x - δ / 2) (x + δ / 2) := by
    have e : (x - δ / 2) - (x + δ / 2) = -δ := by ring
    rw [Real.dist_eq, e, abs_neg, abs_of_pos hδ]
  have hle := Metric.dist_le_diam_of_mem hbdd hy1 hy2
  linarith [Metric.diam_nonneg (s := Metric.thickening δ s)]

private lemma local_card_le_two_of_abs_sub_le_one {ι : Type*} (f : ι → ℤ)
    (hinj : Function.Injective f) (S : Finset ι)
    (hclose : ∀ a ∈ S, ∀ b ∈ S, |f a - f b| ≤ 1) :
    S.card ≤ 2 := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨a₀, ha₀⟩ := hS
    rw [← Finset.card_image_of_injective S hinj]
    by_cases hm : f a₀ - 1 ∈ S.image f
    · obtain ⟨a₁, ha₁, hfa₁⟩ := Finset.mem_image.mp hm
      have hsub : S.image f ⊆ {f a₀ - 1, f a₀} := fun z hz => by
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        have h1 := abs_le.mp (hclose a ha a₀ ha₀)
        have h2 := abs_le.mp (hclose a ha a₁ ha₁)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    · have hsub : S.image f ⊆ {f a₀, f a₀ + 1} := fun z hz => by
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        have h1 := abs_le.mp (hclose a ha a₀ ha₀)
        have hne : f a ≠ f a₀ - 1 := fun h => hm (Finset.mem_image.mpr ⟨a, ha, h⟩)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]; simp

private lemma local_sum_biUnion_le {ι α : Type*} (s : Finset ι) (t : ι → Finset α)
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ a ∈ s.biUnion t, f a) ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have hunion : (∑ a ∈ t i ∪ s.biUnion t, f a) ≤
        (∑ a ∈ t i, f a) + ∑ a ∈ s.biUnion t, f a := by
      have hsub := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := f)
      have hnn : 0 ≤ ∑ a ∈ t i ∩ s.biUnion t, f a := Finset.sum_nonneg fun a _ => hf a
      linarith
    linarith

private def localEndPair {V : Type*} (edges : V → V → Finset ℤ) :
    ∀ {n : ℕ} {v : V}, Path edges n v → ℕ → ℤ × ℤ → ℤ × ℤ
  | 0, _, _, _, p => p
  | _n + 1, _, ⟨_, a, q⟩, N, p =>
    localEndPair edges q (N + 1) (p.2, (4 * (N : ℤ) + 6) * p.2 + p.1 + a.1)

private lemma localEndPair_realizes_prefix {V : Type*} (edges : V → V → Finset ℤ) (x : ℝ)
    (n N : ℕ) (vertices : ℕ → V)
    (hadm : ∀ i, defectShift x (N + i) ∈ edges (vertices i) (vertices (i + 1))) :
    ∃ q : Path edges n (vertices 0),
      localEndPair edges q N
          (nearestInt ((Qsel N : ℝ) * x), nearestInt ((Qsel (N + 1) : ℝ) * x)) =
        (nearestInt ((Qsel (N + n) : ℝ) * x), nearestInt ((Qsel (N + n + 1) : ℝ) * x)) := by
  induction n generalizing N vertices with
  | zero => exact ⟨PUnit.unit, rfl⟩
  | succ n ih =>
    let tail : ℕ → V := fun i => vertices (i + 1)
    have htail : ∀ i, defectShift x (N + 1 + i) ∈ edges (tail i) (tail (i + 1)) := fun i => by
      simpa [tail, Nat.add_assoc, Nat.add_comm i 1] using hadm (i + 1)
    obtain ⟨q, hq⟩ := ih (N + 1) tail htail
    have ha : defectShift x N ∈ edges (vertices 0) (vertices 1) := by simpa using hadm 0
    refine ⟨⟨vertices 1, ⟨defectShift x N, ha⟩, q⟩, ?_⟩
    change localEndPair edges q (N + 1)
      (nearestInt ((Qsel (N + 1) : ℝ) * x),
        (4 * (N : ℤ) + 6) * nearestInt ((Qsel (N + 1) : ℝ) * x) +
          nearestInt ((Qsel N : ℝ) * x) + defectShift x N) = _
    rw [← nearestInt_add_two_eq x N, hq, show N + 1 + n = N + (n + 1) by omega]

private def localPathInterv {V : Type*} (edges : V → V → Finset ℤ) (N : ℕ) (p : ℤ × ℤ)
    {n : ℕ} {v : V} (q : Path edges n v) : Set ℝ :=
  gaugeInterv (N + n) (localEndPair edges q N p).1

private lemma localFixedTail_cover {V : Type*} (edges : V → V → Finset ℤ) (N : ℕ) (p : ℤ × ℤ)
    (n : ℕ) (v : V) :
    fixedTail edges N p v ⊆ ⋃ q : Path edges n v, localPathInterv edges N p q := by
  intro x hx
  rcases hx with ⟨hp, vertices, rfl, hadm⟩
  obtain ⟨q, hq⟩ := localEndPair_realizes_prefix edges x n N vertices hadm
  refine Set.mem_iUnion.mpr ⟨q, ?_⟩
  unfold localPathInterv
  rw [← hp, hq]
  exact mem_gaugeInterv_nearestInt x (N + n)

lemma one_le_k_of_one_lt_growth {V : Type*} [Fintype V] [Nonempty V]
    {edges : V → V → Finset ℤ} {k : ℕ}
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges)
    (w : V → ℝ) {growth lo : ℝ} (hlo : 0 < lo) (hgrowth : 1 < growth)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    (hl : ∀ v, lo ≤ w v) : 1 ≤ k := by
  by_contra hk0
  have hk_eq : k = 0 := by omega
  subst hk_eq
  obtain ⟨v₀, _, hvmax⟩ := Finset.exists_max_image (Finset.univ : Finset V) w
    Finset.univ_nonempty
  have hw₀ : 0 < w v₀ := hlo.trans_le (hl v₀)
  have hadj_sum : (∑ u : V, adjacency edges v₀ u) ≤ 1 := by
    let S : Finset V := Finset.univ.filter (fun u => (edges v₀ u).Nonempty)
    have hcard_S : S.card ≤ 1 := by
      refine Finset.card_le_one.mpr fun u₁ hu₁ u₂ hu₂ => ?_
      obtain ⟨a₁, ha₁⟩ := (Finset.mem_filter.mp hu₁).2
      obtain ⟨a₂, ha₂⟩ := (Finset.mem_filter.mp hu₂).2
      have h10 : a₁ = 0 := by
        have hlab := abs_le.mp (hlabels v₀ u₁ a₁ ha₁)
        omega
      have h20 : a₂ = 0 := by
        have hlab := abs_le.mp (hlabels v₀ u₂ a₂ ha₂)
        omega
      exact hdet v₀ u₁ u₂ 0 (h10 ▸ ha₁) (h20 ▸ ha₂)
    have hsplit : (∑ u : V, adjacency edges v₀ u) = ∑ u ∈ S, adjacency edges v₀ u := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun u _ hu => ?_).symm
      have hne : ¬ (edges v₀ u).Nonempty := fun h =>
        hu (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
      simp [adjacency, Finset.not_nonempty_iff_eq_empty.mp hne]
    rw [hsplit]
    have hterm : ∀ u ∈ S, adjacency edges v₀ u ≤ 1 := by
      intro u _
      have hsub : edges v₀ u ⊆ ({0} : Finset ℤ) := fun a ha => by
        rw [Finset.mem_singleton]
        have hlab := abs_le.mp (hlabels v₀ u a ha)
        omega
      have hc : (edges v₀ u).card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
      unfold adjacency
      exact_mod_cast hc
    calc (∑ u ∈ S, adjacency edges v₀ u)
        ≤ ∑ _u ∈ S, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard_S
  have hle_sum : growth * w v₀ ≤ (∑ u : V, adjacency edges v₀ u) * w v₀ := by
    rw [← hw v₀, Finset.sum_mul]
    exact Finset.sum_le_sum fun u _ =>
      mul_le_mul_of_nonneg_left (hvmax u (Finset.mem_univ u)) (Nat.cast_nonneg _)
  have hle_w : growth * w v₀ ≤ 1 * w v₀ :=
    hle_sum.trans (mul_le_mul_of_nonneg_right hadj_sum hw₀.le)
  have hgle : growth ≤ 1 := le_of_mul_le_mul_right hle_w hw₀
  linarith

/-- Map `a ∈ {-k, ..., k}` into `Fin (2 * k + 1)` inverse to `GaugeExact.digitOf k`. -/
def finOfDigit (k : ℕ) (a : ℤ) (ha : |a| ≤ (k : ℤ)) : Fin (2 * k + 1) :=
  ⟨(a + (k : ℤ)).toNat, by rw [abs_le] at ha; omega⟩

lemma digitOf_finOfDigit (k : ℕ) (a : ℤ) (ha : |a| ≤ (k : ℤ)) :
    digitOf k (finOfDigit k a ha) = a := by
  unfold digitOf finOfDigit
  rw [abs_le] at ha
  have hnn : 0 ≤ a + (k : ℤ) := by omega
  rw [Int.toNat_of_nonneg hnn]
  ring

lemma finOfDigit_injective (k : ℕ) {a b : ℤ} (ha : |a| ≤ (k : ℤ)) (hb : |b| ≤ (k : ℤ))
    (heq : finOfDigit k a ha = finOfDigit k b hb) : a = b := by
  have h := congrArg (digitOf k) heq
  rwa [digitOf_finOfDigit, digitOf_finOfDigit] at h

/-- Map a finite graph path of length `n` from `v` to a Cantor word of length `n`. -/
def wordOfPath {V : Type*} [Fintype V] (edges : V → V → Finset ℤ) (k : ℕ)
    (hlabels : edgeLabelsLe edges k) :
    ∀ {n : ℕ} {v : V}, Path edges n v → Fin n → Fin (2 * k + 1)
  | 0, _, _ => fun i => i.elim0
  | _ + 1, _, ⟨_, a, r⟩ =>
      Fin.cons (finOfDigit k a.1 (hlabels _ _ a.1 a.2)) (wordOfPath edges k hlabels r)

theorem wordOfPath_injective {V : Type*} [Fintype V] {edges : V → V → Finset ℤ} {k : ℕ}
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges) :
    ∀ {n : ℕ} {v : V}, Function.Injective (wordOfPath edges k hlabels (n := n) (v := v))
  | 0, _, a, b, _ => by cases a; cases b; rfl
  | _ + 1, v, ⟨u₁, ⟨a₁, ha₁⟩, r₁⟩, ⟨u₂, ⟨a₂, ha₂⟩, r₂⟩, heq => by
    have h0 := congrFun heq 0
    simp only [wordOfPath, Fin.cons_zero] at h0
    have ha_eq : a₁ = a₂ :=
      finOfDigit_injective k (hlabels v u₁ a₁ ha₁) (hlabels v u₂ a₂ ha₂) h0
    subst ha_eq
    have hu_eq : u₁ = u₂ := hdet v u₁ u₂ a₁ ha₁ ha₂
    subst hu_eq
    have htail : wordOfPath edges k hlabels r₁ = wordOfPath edges k hlabels r₂ := by
      funext i
      have hi := congrFun heq i.succ
      simpa only [wordOfPath, Fin.cons_succ] using hi
    have hr_eq := wordOfPath_injective hlabels hdet htail
    subst hr_eq
    rfl

/-- Length-`m` prefix of a finite walk of length `n ≥ m`. -/
def pathTake {V : Type*} [Fintype V] {edges : V → V → Finset ℤ} :
    ∀ {n : ℕ} (m : ℕ) (_h : m ≤ n) {v : V}, Path edges n v → Path edges m v
  | _, 0, _, _, _ => PUnit.unit
  | _ + 1, m + 1, h, _, ⟨u, a, r⟩ => ⟨u, a, pathTake m (by omega) r⟩

lemma wordOfPath_pathTake {V : Type*} [Fintype V] {edges : V → V → Finset ℤ} {k : ℕ}
    (hlabels : edgeLabelsLe edges k) :
    ∀ {n : ℕ} (m : ℕ) (h : m ≤ n) {v : V} (q : Path edges n v),
      wordOfPath edges k hlabels (pathTake m h q) =
        prefixWordC h (wordOfPath edges k hlabels q)
  | _, 0, _, _, _ => by funext i; exact i.elim0
  | _ + 1, m + 1, h, _, ⟨u, a, r⟩ => by
    funext ⟨i, hi⟩
    cases i with
    | zero => rfl
    | succ j =>
      have hj : j < m := by omega
      have ih := congrFun (wordOfPath_pathTake hlabels m (by omega) r) ⟨j, hj⟩
      have h1 : wordOfPath edges k hlabels (pathTake (m + 1) h ⟨u, a, r⟩) ⟨j + 1, hi⟩ =
          wordOfPath edges k hlabels (pathTake m (by omega) r) ⟨j, hj⟩ := rfl
      have h2 : prefixWordC h (wordOfPath edges k hlabels ⟨u, a, r⟩) ⟨j + 1, hi⟩ =
          prefixWordC (by omega : m ≤ _) (wordOfPath edges k hlabels r) ⟨j, hj⟩ := rfl
      rw [h1, h2]
      exact ih

lemma sum_perron_weight_fiber {V : Type*} [Fintype V] (edges : V → V → Finset ℤ)
    (w : V → ℝ) (growth : ℝ)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v) :
    ∀ (m N : ℕ) (h : m ≤ N) (v : V) (q₀ : Path edges m v),
      (∑ q : Path edges N v, if pathTake m h q = q₀ then w (endVertex edges q) else 0) =
        growth ^ (N - m) * w (endVertex edges q₀)
  | 0, N, _, v, q₀ => by
    have hall : ∀ q : Path edges N v,
        (if pathTake 0 (Nat.zero_le N) q = q₀ then w (endVertex edges q) else 0) =
          w (endVertex edges q) := fun q => by
      simp only [PUnit.ext (pathTake 0 (Nat.zero_le N) q) q₀, ↓reduceIte]
    simp_rw [hall]
    simpa only [Nat.sub_zero, endVertex] using perron_word_mass_sum edges w growth hw N v
  | m + 1, 0, h, _, _ => by omega
  | m + 1, n' + 1, h, v, ⟨u₀, ⟨a₀, ha₀⟩, r₀⟩ => by
    have ih := sum_perron_weight_fiber edges w growth hw m n' (by omega) u₀ r₀
    have hsplit : (∑ q : Path edges (n' + 1) v,
        if pathTake (m + 1) h q = ⟨u₀, ⟨a₀, ha₀⟩, r₀⟩ then w (endVertex edges q) else 0) =
        ∑ u : V, ∑ a : {a // a ∈ edges v u}, ∑ r : Path edges n' u,
          if pathTake (m + 1) h ⟨u, a, r⟩ = ⟨u₀, ⟨a₀, ha₀⟩, r₀⟩ then
            w (endVertex edges r) else 0 := by
      change ∑ q : (Σ u : V, {a // a ∈ edges v u} × Path edges n' u), _ = _
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Fintype.sum_prod_type]
      rfl
    rw [hsplit]
    have hu_eq : ∀ u : V, (∑ a : {a // a ∈ edges v u}, ∑ r : Path edges n' u,
        if pathTake (m + 1) h ⟨u, a, r⟩ = ⟨u₀, ⟨a₀, ha₀⟩, r₀⟩ then
          w (endVertex edges r) else 0) =
        if u = u₀ then growth ^ (n' - m) * w (endVertex edges r₀) else 0 := by
      intro u
      by_cases hu : u = u₀
      · subst hu
        simp only [↓reduceIte]
        have ha_eq : ∀ a : {a // a ∈ edges v u}, (∑ r : Path edges n' u,
            if pathTake (m + 1) h ⟨u, a, r⟩ = ⟨u, ⟨a₀, ha₀⟩, r₀⟩ then
              w (endVertex edges r) else 0) =
            if a = ⟨a₀, ha₀⟩ then growth ^ (n' - m) * w (endVertex edges r₀) else 0 := by
          intro a
          by_cases ha : a = ⟨a₀, ha₀⟩
          · subst ha
            simp only [↓reduceIte]
            refine (Finset.sum_congr rfl fun r _ => ?_).trans ih
            have hiff : pathTake (m + 1) h ⟨u, ⟨a₀, ha₀⟩, r⟩ = ⟨u, ⟨a₀, ha₀⟩, r₀⟩ ↔
                pathTake m (by omega) r = r₀ := by
              constructor
              · intro heq
                obtain ⟨_, hpair⟩ := Sigma.mk.inj heq
                rw [heq_eq_eq] at hpair
                exact (Prod.mk.inj hpair).2
              · intro heq
                dsimp only [pathTake]
                rw [heq]
            simp only [hiff]
          · simp only [ha, ↓reduceIte]
            refine Finset.sum_eq_zero fun r _ => ?_
            have hne : pathTake (m + 1) h ⟨u, a, r⟩ ≠ ⟨u, ⟨a₀, ha₀⟩, r₀⟩ := by
              intro heq
              obtain ⟨_, hpair⟩ := Sigma.mk.inj heq
              rw [heq_eq_eq] at hpair
              exact ha (Prod.mk.inj hpair).1
            simp [hne]
        simp only [ha_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      · simp only [hu, ↓reduceIte]
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun r _ => ?_
        have hne : pathTake (m + 1) h ⟨u, a, r⟩ ≠ ⟨u₀, ⟨a₀, ha₀⟩, r₀⟩ := by
          intro heq; exact hu (Sigma.mk.inj heq).1
        simp [hne]
    simp only [hu_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hsub : n' + 1 - (m + 1) = n' - m := by omega
    rw [hsub]
    rfl

private lemma step_label_of_pathTake_succ {V : Type*} [Fintype V] {edges : V → V → Finset ℤ}
    {k : ℕ} (hlabels : edgeLabelsLe edges k) :
    ∀ {n : ℕ} {v : V} (q : Path edges n v) (q' : Path edges (n + 1) v),
      pathTake n (Nat.le_succ n) q' = q →
        digitOf k (wordOfPath edges k hlabels q' (Fin.last n)) ∈
          edges (endVertex edges q) (endVertex edges q')
  | 0, _, _, ⟨_, ⟨a, ha⟩, PUnit.unit⟩, _ => by
    have h0 : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [h0]
    simpa only [endVertex, wordOfPath, Fin.cons_zero, digitOf_finOfDigit] using ha
  | n + 1, _, ⟨u, p⟩, ⟨u', p'⟩, heq => by
    dsimp only [pathTake] at heq
    obtain ⟨rfl, hpair⟩ := Sigma.mk.inj heq
    rw [heq_eq_eq] at hpair
    obtain ⟨_, hp2⟩ := Prod.mk.inj hpair
    have hr := step_label_of_pathTake_succ hlabels p.2 p'.2 hp2
    have hlast : (Fin.last (n + 1) : Fin (n + 2)) = Fin.succ (Fin.last n) := rfl
    simpa only [endVertex, wordOfPath, hlast, Fin.cons_succ] using hr

/-- Compact subset of `ℝ` coded by infinite graph paths starting at `v₀` from level `J_cantor k`. -/
def graphTree {V : Type*} [Fintype V] (edges : V → V → Finset ℤ) (k : ℕ)
    (hlabels : edgeLabelsLe edges k) (v₀ : V) : Set ℝ :=
  ⋂ n : ℕ, ⋃ q : Path edges n v₀, cIntervC k n (wordOfPath edges k hlabels q)

lemma graphTree_subset_cantorTreeC {V : Type*} [Fintype V] (edges : V → V → Finset ℤ) (k : ℕ)
    (hlabels : edgeLabelsLe edges k) (v₀ : V) :
    graphTree edges k hlabels v₀ ⊆ cantorTreeC k := by
  intro x hx
  rw [cantorTreeC, Set.mem_iInter]
  intro n
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hx n)
  exact Set.mem_iUnion.mpr ⟨wordOfPath edges k hlabels q, hq⟩

theorem isCompact_graphTree {V : Type*} [Fintype V] (edges : V → V → Finset ℤ) (k : ℕ)
    (hlabels : edgeLabelsLe edges k) (v₀ : V) :
    IsCompact (graphTree edges k hlabels v₀) := by
  apply IsCompact.of_isClosed_subset (isCompact_cantorTreeC k)
  · exact isClosed_iInter fun n =>
      isClosed_iUnion_of_finite fun q => (isCompact_cIntervC k n _).isClosed
  · exact graphTree_subset_cantorTreeC edges k hlabels v₀

private def pathSnocStep {V : Type*} [Fintype V] {edges : V → V → Finset ℤ}
    (nextU : V → V) (nextA : V → ℤ) (hmem : ∀ v, nextA v ∈ edges v (nextU v)) :
    ∀ {n : ℕ} {v : V}, Path edges n v → Path edges (n + 1) v
  | 0, v, _ => ⟨nextU v, ⟨nextA v, hmem v⟩, PUnit.unit⟩
  | _ + 1, _, ⟨u, a, r⟩ => ⟨u, a, pathSnocStep nextU nextA hmem r⟩

private lemma pathTake_pathSnocStep {V : Type*} [Fintype V] {edges : V → V → Finset ℤ}
    (nextU : V → V) (nextA : V → ℤ) (hmem : ∀ v, nextA v ∈ edges v (nextU v)) :
    ∀ {n : ℕ} {v : V} (q : Path edges n v),
      pathTake n (Nat.le_succ n) (pathSnocStep nextU nextA hmem q) = q
  | 0, _, _ => rfl
  | _ + 1, _, ⟨_, _, r⟩ => by
    dsimp only [pathSnocStep, pathTake]
    rw [pathTake_pathSnocStep nextU nextA hmem r]

private def extendPathN {V : Type*} [Fintype V] {edges : V → V → Finset ℤ}
    (nextU : V → V) (nextA : V → ℤ) (hmem : ∀ v, nextA v ∈ edges v (nextU v)) :
    ∀ (m : ℕ) {n : ℕ} {v : V}, Path edges n v → Path edges (n + m) v
  | 0, _, _, q => q
  | m + 1, _, _, q => pathSnocStep nextU nextA hmem (extendPathN nextU nextA hmem m q)

lemma cIntervC_inter_graphTree_nonempty {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) {k : ℕ} (hk : 1 ≤ k)
    (hlabels : edgeLabelsLe edges k)
    (hout : ∀ v : V, ∃ u : V, ∃ a : ℤ, a ∈ edges v u)
    (n : ℕ) (v₀ : V) (q : Path edges n v₀) :
    (cIntervC k n (wordOfPath edges k hlabels q) ∩ graphTree edges k hlabels v₀).Nonempty := by
  choose nextU nextA hmem using hout
  let ext := fun m => extendPathN nextU nextA hmem m q
  let S : ℕ → Set ℝ := fun m => cIntervC k (n + m) (wordOfPath edges k hlabels (ext m))
  have hS_ne : ∀ m, (S m).Nonempty := fun m => cIntervC_nonempty k (n + m) _
  have hS_comp : ∀ m, IsCompact (S m) := fun m => isCompact_cIntervC k (n + m) _
  have hS_closed : ∀ m, IsClosed (S m) := fun m => (hS_comp m).isClosed
  have hpref_step : ∀ m : ℕ,
      prefixWordC (Nat.le_succ (n + m)) (wordOfPath edges k hlabels (ext (m + 1))) =
        wordOfPath edges k hlabels (ext m) := fun m => by
    have hext1 : ext (m + 1) = pathSnocStep nextU nextA hmem (ext m) := rfl
    rw [← wordOfPath_pathTake hlabels (n + m) (Nat.le_succ (n + m)) (ext (m + 1)),
      hext1, pathTake_pathSnocStep]
  have hS_anti : Antitone S := by
    refine antitone_nat_of_succ_le fun m x hx => ?_
    have hsub := cIntervC_succ_subset k hk (n + m) (wordOfPath edges k hlabels (ext (m + 1))) hx
    have hfin : Fin.init (wordOfPath edges k hlabels (ext (m + 1))) =
        prefixWordC (Nat.le_succ (n + m)) (wordOfPath edges k hlabels (ext (m + 1))) := by
      ext ⟨i, hi⟩; rfl
    rwa [hfin, hpref_step m] at hsub
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S (fun m => hS_anti (Nat.le_succ m)) hS_ne (hS_comp 0) hS_closed
  have hx0 : x ∈ cIntervC k n (wordOfPath edges k hlabels q) := Set.mem_iInter.mp hx 0
  refine ⟨x, hx0, ?_⟩
  rw [graphTree, Set.mem_iInter]
  intro j
  by_cases hj : j ≤ n
  · refine Set.mem_iUnion.mpr ⟨pathTake j hj q, ?_⟩
    rw [wordOfPath_pathTake]
    exact cIntervC_prefix_subset k hk hj (wordOfPath edges k hlabels q) hx0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = n + m := ⟨j - n, by omega⟩
    exact Set.mem_iUnion.mpr ⟨ext m, Set.mem_iInter.mp hx m⟩

theorem graphTree_subset_fixedTail {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) {k : ℕ} (hk : 1 ≤ k)
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges) (v₀ : V) :
    graphTree edges k hlabels v₀ ⊆ eventualTail edges := by
  intro x hx
  have hx_q : ∀ n : ℕ, ∃ q : Path edges n v₀, x ∈ cIntervC k n (wordOfPath edges k hlabels q) :=
    fun n => Set.mem_iUnion.mp (Set.mem_iInter.mp hx n)
  choose q hq using hx_q
  let w : ∀ n : ℕ, Fin n → Fin (2 * k + 1) := fun n => wordOfPath edges k hlabels (q n)
  have hnear : ∀ n : ℕ,
      nearestInt ((Qsel (J_cantor k + n + 1) : ℝ) * x) = centerIntC k n (w n) := by
    intro n
    have hQpos : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
      exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
    have hxn := hq n
    have hdiff : |(Qsel (J_cantor k + n + 1) : ℝ) * x - (centerIntC k n (w n) : ℝ)| ≤
        (Qsel (J_cantor k + n + 1) : ℝ) * radC k n := by
      have h1 : |x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
        abs_le.mpr ⟨by linarith [hxn.1], by linarith [hxn.2]⟩
      calc |(Qsel (J_cantor k + n + 1) : ℝ) * x - (centerIntC k n (w n) : ℝ)|
          = (Qsel (J_cantor k + n + 1) : ℝ) *
              |x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := by
            rw [← abs_of_pos hQpos, ← abs_mul]
            congr 1; rw [abs_of_pos hQpos]; field_simp
        _ ≤ (Qsel (J_cantor k + n + 1) : ℝ) * radC k n :=
            mul_le_mul_of_nonneg_left h1 hQpos.le
    have hlt_half : |(Qsel (J_cantor k + n + 1) : ℝ) * x - (centerIntC k n (w n) : ℝ)| < 1 / 2 :=
      calc _ ≤ (Qsel (J_cantor k + n + 1) : ℝ) * radC k n := hdiff
        _ ≤ (Qsel (J_cantor k + n + 1) : ℝ) * (1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ))) :=
            mul_le_mul_of_nonneg_left (radC_le_quarter_inv k n hk) hQpos.le
        _ = 1 / 4 := by field_simp
        _ < 1 / 2 := by norm_num
    rw [nearestInt, round_eq_iff]
    have habs := abs_lt.mp hlt_half
    exact ⟨by linarith, by linarith⟩
  have hinit_eq : ∀ n : ℕ, Fin.init (w (n + 1)) = w n := by
    intro n
    have h1 := cIntervC_succ_subset k hk n (w (n + 1)) (hq (n + 1))
    have h2 := hq n
    have hQpos : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
      exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
    have hcdiff : |(centerIntC k n (Fin.init (w (n + 1))) : ℝ) /
        (Qsel (J_cantor k + n + 1) : ℝ) -
        (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ 2 * radC k n := by
      have hd1 : |x - (centerIntC k n (Fin.init (w (n + 1))) : ℝ) /
          (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
        abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
      have hd2 : |x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
        abs_le.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩
      have hsub : (centerIntC k n (Fin.init (w (n + 1))) : ℝ) /
          (Qsel (J_cantor k + n + 1) : ℝ) -
          (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) =
          ((centerIntC k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x) +
            (x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)) := by ring
      rw [hsub]
      calc _ ≤ |(centerIntC k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x| +
              |x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := abs_add_le _ _
        _ ≤ radC k n + radC k n := by rw [abs_sub_comm]; exact add_le_add hd1 hd2
        _ = 2 * radC k n := by ring
    have hlt1 : |centerIntC k n (Fin.init (w (n + 1))) - centerIntC k n (w n)| < 1 := by
      have h2r : 2 * radC k n < 1 / (Qsel (J_cantor k + n + 1) : ℝ) := by
        calc 2 * radC k n ≤ 2 * (1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ))) := by
              linarith [radC_le_quarter_inv k n hk]
          _ = (1 / 2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) := by ring
          _ < 1 / (Qsel (J_cantor k + n + 1) : ℝ) := by
              rw [div_lt_div_iff_of_pos_right hQpos]; linarith
      have heq : |(centerIntC k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
          (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| =
          (|centerIntC k n (Fin.init (w (n + 1))) - centerIntC k n (w n)| : ℝ) /
            (Qsel (J_cantor k + n + 1) : ℝ) := by
        rw [← sub_div, abs_div, abs_of_pos hQpos, ← Int.cast_sub, ← Int.cast_abs]
      rw [heq] at hcdiff
      have hltR := (div_lt_div_iff_of_pos_right hQpos).mp (lt_of_le_of_lt hcdiff h2r)
      exact_mod_cast hltR
    rw [abs_lt] at hlt1
    exact centerIntC_injective k hk n (by omega)
  have htake_eq : ∀ n : ℕ, pathTake n (Nat.le_succ n) (q (n + 1)) = q n := fun n => by
    apply wordOfPath_injective hlabels hdet
    rw [wordOfPath_pathTake]
    calc prefixWordC (Nat.le_succ n) (w (n + 1))
        = Fin.init (w (n + 1)) := by ext ⟨i, hi⟩; rfl
      _ = w n := hinit_eq n
  let N₀ := J_cantor k + 1
  let vertices : ℕ → V := fun i => endVertex edges (q (i + 1))
  refine Set.mem_iUnion.mpr ⟨N₀, Set.mem_iUnion.mpr
    ⟨(nearestInt ((Qsel N₀ : ℝ) * x), nearestInt ((Qsel (N₀ + 1) : ℝ) * x)),
      Set.mem_iUnion.mpr ⟨vertices 0, rfl, vertices, rfl, fun i => ?_⟩⟩⟩
  have hdef_eq : defectShift x (N₀ + i) = digitOf k (w (i + 2) (Fin.last (i + 1))) := by
    rw [defectShift_eq_defect_succ]
    have hidx : N₀ + i + 1 = J_cantor k + i + 2 := by dsimp [N₀]; omega
    rw [hidx]
    unfold defect
    have hm0 : nearestInt ((Qsel (J_cantor k + i + 1) : ℝ) * x) = centerIntC k i (w i) :=
      hnear i
    have hm1 : nearestInt ((Qsel (J_cantor k + i + 2) : ℝ) * x) =
        centerIntC k (i + 1) (w (i + 1)) :=
      hnear (i + 1)
    have hm2 : nearestInt ((Qsel (J_cantor k + i + 3) : ℝ) * x) =
        centerIntC k (i + 2) (w (i + 2)) :=
      hnear (i + 2)
    have hsub1 : J_cantor k + i + 2 - 1 = J_cantor k + i + 1 := by omega
    have hsub2 : J_cantor k + i + 2 + 1 = J_cantor k + i + 3 := by omega
    rw [hsub1, hsub2, hm0, hm1, hm2]
    have hrec_w : centerIntC k (i + 2) (w (i + 2)) =
        (4 * ((J_cantor k + (i + 1) : ℕ) : ℤ) + 6) *
          (pairOfWord k (i + 1) (Fin.init (w (i + 2)))).2 +
          (pairOfWord k (i + 1) (Fin.init (w (i + 2)))).1 +
          digitOf k (w (i + 2) (Fin.last (i + 1))) := rfl
    rw [hrec_w, hinit_eq (i + 1)]
    have hp1 : (pairOfWord k (i + 1) (w (i + 1))).1 = centerIntC k i (w i) := by
      change (pairOfWord k i (Fin.init (w (i + 1)))).2 = centerIntC k i (w i)
      rw [hinit_eq i]; rfl
    rw [hp1]
    have hcast : 4 * ((J_cantor k + (i + 1) : ℕ) : ℤ) + 6 =
        4 * ((J_cantor k + i + 2 : ℕ) : ℤ) + 2 := by push_cast; ring
    rw [hcast]
    change _ = digitOf k (w (i + 2) (Fin.last (i + 1)))
    unfold centerIntC
    ring
  rw [hdef_eq]
  exact step_label_of_pathTake_succ hlabels (q (i + 1)) (q (i + 2)) (htake_eq (i + 1))

/-! ## Part 2: Direct finite-sum Frostman positivity for `graphTree` -/

theorem mkMetric_graphTree_pos {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) (k : ℕ)
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges)
    (w : V → ℝ) {growth lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 < hi) (hgrowth : 1 < growth)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    (hl : ∀ v, lo ≤ w v) (hu : ∀ v, w v ≤ hi) (v₀ : V) :
    0 < Measure.mkMetric (interpGauge growth) (graphTree edges k hlabels v₀) := by
  have : Nonempty V := ⟨v₀⟩
  have hk : 1 ≤ k := one_le_k_of_one_lt_growth hlabels hdet w hlo hgrowth hw hl
  have hgrowth_pos : 0 < growth := by linarith
  have hout : ∀ v : V, ∃ u : V, ∃ a : ℤ, a ∈ edges v u := fun v => by
    by_contra hnone
    push Not at hnone
    have hzero : (∑ u, adjacency edges v u * w u) = 0 :=
      Finset.sum_eq_zero fun u _ => by
        have hem : edges v u = ∅ := Finset.eq_empty_of_forall_notMem (hnone u)
        simp [adjacency, hem]
    rw [hw v] at hzero
    have hwv : 0 < w v := hlo.trans_le (hl v)
    linarith [mul_pos hgrowth_pos hwv]
  set J := J_cantor k
  set m_g := interpGauge growth
  set c₀R : ℝ := 1 / (2 * ((2 * (hi / lo) * growth ^ 2) * growth ^ J))
  have hc₀R_pos : 0 < c₀R := by positivity
  set c₀ : ℝ≥0∞ := ENNReal.ofReal c₀R
  have hc₀_pos : 0 < c₀ := ENNReal.ofReal_pos.mpr hc₀R_pos
  refine lt_of_lt_of_le hc₀_pos ?_
  have hQJ1_pos : 0 < (Qsel (J + 1) : ℝ) := by
    exact_mod_cast Qsel_pos (J + 1) (by dsimp [J]; unfold J_cantor; omega)
  set r0R : ℝ := 1 / (2 * (Qsel (J + 1) : ℝ))
  have hr0R_pos : 0 < r0R := by positivity
  set r0 : ℝ≥0∞ := ENNReal.ofReal r0R
  have hr0_pos : 0 < r0 := ENNReal.ofReal_pos.mpr hr0R_pos
  rw [Measure.mkMetric_apply]
  refine le_trans ?_ (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
    ⨅ (t : ℕ → Set ℝ) (_ : graphTree edges k hlabels v₀ ⊆ ⋃ n, t n)
      (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, m_g (Metric.ediam (t n))) r0 hr0_pos)
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
  by_contra hlt
  push Not at hlt
  set S : ℝ≥0∞ := ∑' n, ⨆ _ : (t n).Nonempty, m_g (Metric.ediam (t n))
  have hS_ne_top : S ≠ ⊤ := ne_of_lt (lt_trans hlt ENNReal.ofReal_lt_top)
  have hSR_lt : S.toReal < c₀R := by
    have h1 := (ENNReal.toReal_lt_toReal hS_ne_top ENNReal.ofReal_ne_top).mpr hlt
    rwa [ENNReal.toReal_ofReal hc₀R_pos.le] at h1
  set δ0 : ℝ := (c₀R - S.toReal) / 2
  have hδ0 : 0 < δ0 := by dsimp [δ0]; linarith
  have hex_rho : ∀ i : ℕ, (t i).Nonempty → ∃ ρi : ℝ, 0 < ρi ∧ 2 * ρi ≤ r0R ∧
      m_g (Metric.ediam (t i) + ENNReal.ofReal (2 * ρi)) ≤
        m_g (Metric.ediam (t i)) + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i + 1)) := by
    intro i hne
    have hm_lt : m_g (Metric.ediam (t i)) < ⊤ := by
      have hleS : m_g (Metric.ediam (t i)) ≤ S := by
        have h1 : (⨆ _ : (t i).Nonempty, m_g (Metric.ediam (t i))) ≤ S :=
          ENNReal.le_tsum (f := fun n => ⨆ _ : (t n).Nonempty, m_g (Metric.ediam (t n))) i
        simpa [hne] using h1
      exact lt_of_le_of_lt hleS (lt_trans hlt ENNReal.ofReal_lt_top)
    have hε_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i + 1)) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    have hlt_m : m_g (Metric.ediam (t i)) <
        m_g (Metric.ediam (t i)) + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i + 1)) :=
      ENNReal.lt_add_right hm_lt.ne hε_pos.ne'
    have hcont_add : Tendsto (fun x : ℝ≥0∞ => m_g (Metric.ediam (t i) + x)) (nhds 0)
        (nhds (m_g (Metric.ediam (t i)))) := by
      have h1 : Tendsto (fun x : ℝ≥0∞ => Metric.ediam (t i) + x) (nhds 0)
          (nhds (Metric.ediam (t i) + 0)) := tendsto_const_nhds.add tendsto_id
      rw [add_zero] at h1
      exact (interpGauge_continuous hgrowth).continuousAt.tendsto.comp h1
    have hev := hcont_add.eventually (Iio_mem_nhds hlt_m)
    rw [ENNReal.nhds_zero_basis.eventually_iff] at hev
    obtain ⟨η, hη_pos, hη⟩ := hev
    by_cases htop : η = ⊤
    · refine ⟨r0R / 2, by linarith, by linarith, ?_⟩
      exact (hη (by rw [htop]; exact ENNReal.ofReal_lt_top)).le
    · have hηpos : 0 < η.toReal := ENNReal.toReal_pos hη_pos.ne' htop
      set ρi : ℝ := min (r0R / 2) (η.toReal / 4)
      have hρi_pos : 0 < ρi := lt_min (by linarith) (by linarith)
      have hρ1 : ρi ≤ r0R / 2 := min_le_left _ _
      have hρ2 : ρi ≤ η.toReal / 4 := min_le_right _ _
      have h2ρ_lt_η : ENNReal.ofReal (2 * ρi) < η := by
        calc ENNReal.ofReal (2 * ρi)
            ≤ ENNReal.ofReal (η.toReal / 2) := ENNReal.ofReal_le_ofReal (by linarith)
          _ < ENNReal.ofReal η.toReal :=
              (ENNReal.ofReal_lt_ofReal_iff hηpos).mpr (by linarith)
          _ = η := ENNReal.ofReal_toReal htop
      exact ⟨ρi, hρi_pos, (mul_le_mul_of_nonneg_left hρ1 zero_le_two).trans_eq
        (mul_div_cancel₀ r0R two_ne_zero), (hη h2ρ_lt_η).le⟩
  choose ρ hρ_pos h2ρ_le hρ_m using fun i : {i : ℕ // (t i).Nonempty} => hex_rho i.1 i.2
  let V_th : {i : ℕ // (t i).Nonempty} → Set ℝ := fun i => Metric.thickening (ρ i) (t i.1)
  have hV_open : ∀ i, IsOpen (V_th i) := fun _ => Metric.isOpen_thickening
  have hV_cov : graphTree edges k hlabels v₀ ⊆ ⋃ i : {i : ℕ // (t i).Nonempty}, V_th i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, Metric.self_subset_thickening (hρ_pos _) (t i) hi⟩
  obtain ⟨F, hFcov⟩ := (isCompact_graphTree edges k hlabels v₀).elim_finite_subcover
    V_th hV_open hV_cov
  have hV_ediam_le : ∀ i : {i : ℕ // (t i).Nonempty},
      Metric.ediam (V_th i) ≤ ENNReal.ofReal (1 / (Qsel (J + 1) : ℝ)) := fun i => by
    calc Metric.ediam (V_th i)
        ≤ Metric.ediam (t i.1) + 2 * ENNReal.ofReal (ρ i) :=
          local_ediam_thickening_le (hρ_pos i).le
      _ ≤ r0 + ENNReal.ofReal (2 * ρ i) := by
          have h2 : 2 * ENNReal.ofReal (ρ i) = ENNReal.ofReal (2 * ρ i) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp
          rw [h2]; gcongr; exact hdiam i.1
      _ ≤ ENNReal.ofReal r0R + ENNReal.ofReal r0R := by gcongr; exact h2ρ_le i
      _ = ENNReal.ofReal (1 / (Qsel (J + 1) : ℝ)) := by
          rw [← ENNReal.ofReal_add hr0R_pos.le hr0R_pos.le]; congr 1; simp only [r0R]; ring
  have hV_bd : ∀ i, Bornology.IsBounded (V_th i) := fun i =>
    Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_of_lt (lt_of_le_of_lt (hV_ediam_le i) ENNReal.ofReal_lt_top))
  have hV_diam_le : ∀ i, Metric.diam (V_th i) ≤ 1 / (Qsel (J + 1) : ℝ) := fun i => by
    unfold Metric.diam
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hV_ediam_le i)
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hV_diam_pos : ∀ i, 0 < Metric.diam (V_th i) := fun i =>
    local_diam_thickening_pos i.2 (hρ_pos i) (hV_bd i)
  have hex_lvl : ∀ i : {i : ℕ // (t i).Nonempty},
      ∃ n : ℕ, 1 ≤ n ∧ 1 / (Qsel (J + n + 1) : ℝ) < Metric.diam (V_th i) ∧
        Metric.diam (V_th i) ≤ 1 / (Qsel (J + n) : ℝ) := by
    intro i
    set d := Metric.diam (V_th i)
    have hd_pos : 0 < d := hV_diam_pos i
    have hd_le : d ≤ 1 / (Qsel (J + 1) : ℝ) := hV_diam_le i
    have hex_m : ∃ m : ℕ, 1 ≤ m ∧ 1 / (Qsel (J + m) : ℝ) < d := by
      have hfact_top : Tendsto (fun m : ℕ => (Nat.factorial (J + m) : ℝ)) atTop atTop := by
        have h1 : Tendsto (fun m : ℕ => Nat.factorial (J + m)) atTop atTop := by
          rw [Filter.tendsto_atTop_atTop]
          intro B
          obtain ⟨K, hK⟩ := Filter.tendsto_atTop_atTop.mp factorial_tendsto_atTop B
          exact ⟨K, fun m hm => hK (J + m) (by omega)⟩
        exact tendsto_natCast_atTop_atTop.comp h1
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hfact_top.eventually_gt_atTop (1 / d))
      refine ⟨max 1 M, le_max_left _ _, ?_⟩
      have hQpos : 0 < (Qsel (J + max 1 M) : ℝ) := by
        exact_mod_cast Qsel_pos (J + max 1 M) (by dsimp [J]; unfold J_cantor; omega)
      have hQge : (Nat.factorial (J + max 1 M) : ℝ) ≤ (Qsel (J + max 1 M) : ℝ) := by
        exact_mod_cast DimHCore.Qsel_ge_factorial (J + max 1 M)
          (by dsimp [J]; unfold J_cantor; omega)
      have hgt := lt_of_lt_of_le (hM (max 1 M) (le_max_right _ _)) hQge
      rw [div_lt_iff₀ hQpos]
      have := (div_lt_iff₀ hd_pos).mp hgt
      linarith
    let m0 := Nat.find hex_m
    have hm0 : 1 ≤ m0 ∧ 1 / (Qsel (J + m0) : ℝ) < d := Nat.find_spec hex_m
    have hm0_gt : 1 < m0 := by
      by_contra hle
      have heq : m0 = 1 := by omega
      rw [heq] at hm0
      linarith [hm0.2, hd_le]
    refine ⟨m0 - 1, by omega, ?_, ?_⟩
    · have heq : J + (m0 - 1) + 1 = J + m0 := by omega
      rw [heq]; exact hm0.2
    · by_contra hgt
      push Not at hgt
      exact Nat.find_min hex_m (show m0 - 1 < m0 by omega) ⟨by omega, hgt⟩
  choose lvl hlvl_ge hlvl_gt hlvl_le using hex_lvl
  set N : ℕ := F.sup (fun i => lvl i)
  have hN_ge : ∀ i ∈ F, lvl i ≤ N := fun i hi => Finset.le_sup hi
  let wt : ∀ {n : ℕ}, Path edges n v₀ → ℝ := fun {n} q =>
    w (endVertex edges q) / (growth ^ n * w v₀)
  have hwt_nn : ∀ {n : ℕ} (q : Path edges n v₀), 0 ≤ wt q := fun {n} q => by
    dsimp [wt]
    exact div_nonneg (hlo.le.trans (hl _)) (mul_nonneg (pow_pos hgrowth_pos n).le
      (hlo.le.trans (hl v₀)))
  have hcover_paths : (Finset.univ : Finset (Path edges N v₀)) ⊆
      F.biUnion (fun i => Finset.univ.filter (fun q : Path edges N v₀ =>
        (V_th i ∩ cIntervC k N (wordOfPath edges k hlabels q)).Nonempty)) := by
    intro q _
    obtain ⟨x, hxI, hxK⟩ := cIntervC_inter_graphTree_nonempty edges hk hlabels hout N v₀ q
    obtain ⟨i, hiF, hxiV⟩ := Set.mem_iUnion₂.mp (hFcov hxK)
    exact Finset.mem_biUnion.mpr ⟨i, hiF, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxiV, hxI⟩⟩⟩
  have hsum_i : ∀ i ∈ F,
      (∑ q ∈ Finset.univ.filter (fun q : Path edges N v₀ =>
          (V_th i ∩ cIntervC k N (wordOfPath edges k hlabels q)).Nonempty), wt q) ≤
        2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ)) := by
    intro i hiF
    have hleN : lvl i ≤ N := hN_ge i hiF
    have hl1 : lvl i - 1 ≤ N := by omega
    set m := lvl i - 1
    have hm_eq : m + 1 = lvl i := by have := hlvl_ge i; omega
    set Hit := Finset.univ.filter (fun q : Path edges N v₀ =>
      (V_th i ∩ cIntervC k N (wordOfPath edges k hlabels q)).Nonempty)
    set A_i := Finset.univ.filter (fun q₀ : Path edges m v₀ =>
      (V_th i ∩ cIntervC k m (wordOfPath edges k hlabels q₀)).Nonempty)
    have hAi_le : A_i.card ≤ 2 := by
      apply local_card_le_two_of_abs_sub_le_one
        (fun q₀ => centerIntC k m (wordOfPath edges k hlabels q₀))
        ((centerIntC_injective k hk m).comp (wordOfPath_injective hlabels hdet)) A_i
      intro q₁ hq₁ q₂ hq₂
      have hdiam_m : Metric.diam (V_th i) ≤ 1 / (Qsel (J + m + 1) : ℝ) := by
        have : J + m + 1 = J + lvl i := by omega
        rw [this]
        exact hlvl_le i
      exact intersect_cIntervC_abs_sub_le_one k hk m (hV_bd i) hdiam_m
        (Finset.mem_filter.mp hq₁).2 (Finset.mem_filter.mp hq₂).2
    have hproj_mem : ∀ q ∈ Hit, pathTake m hl1 q ∈ A_i := by
      intro q hq
      obtain ⟨x, hxV, hxI⟩ := (Finset.mem_filter.mp hq).2
      have hxI' := cIntervC_prefix_subset k hk hl1 (wordOfPath edges k hlabels q) hxI
      rw [← wordOfPath_pathTake hlabels m hl1 q] at hxI'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxV, hxI'⟩⟩
    have hsub_fib : (∑ q ∈ Hit, wt q) ≤
        ∑ q₀ ∈ A_i, ∑ q : Path edges N v₀,
          if pathTake m hl1 q = q₀ then wt q else 0 := by
      have h1 : (∑ q ∈ Hit, wt q) ≤
          ∑ q : Path edges N v₀, if pathTake m hl1 q ∈ A_i then wt q else 0 := by
        calc (∑ q ∈ Hit, wt q)
            ≤ ∑ q ∈ Hit, if pathTake m hl1 q ∈ A_i then wt q else 0 :=
              Finset.sum_le_sum fun q hq => by simp [hproj_mem q hq]
          _ ≤ ∑ q ∈ Finset.univ, if pathTake m hl1 q ∈ A_i then wt q else 0 :=
              Finset.sum_le_univ_sum_of_nonneg fun q => by
                split_ifs <;> [exact hwt_nn q; exact le_rfl]
      refine h1.trans_eq ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hmem : pathTake m hl1 q ∈ A_i
      · simp [hmem]
      · simp [hmem]
    have hfib_sum : ∀ q₀ ∈ A_i,
        (∑ q : Path edges N v₀, if pathTake m hl1 q = q₀ then wt q else 0) = wt q₀ := by
      intro q₀ _
      dsimp [wt]
      have hwv0 : growth ^ N * w v₀ ≠ 0 := by
        have := hlo.trans_le (hl v₀); positivity
      have hdiv_sum : ∀ f : Path edges N v₀ → ℝ,
          (∑ q : Path edges N v₀, if pathTake m hl1 q = q₀ then f q / (growth ^ N * w v₀) else 0) =
            (∑ q : Path edges N v₀, if pathTake m hl1 q = q₀ then f q else 0) /
              (growth ^ N * w v₀) := fun f => by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun q _ => by split_ifs <;> simp
      rw [hdiv_sum, sum_perron_weight_fiber edges w growth hw m N hl1 v₀ q₀]
      have hN_split : N = m + (N - m) := by omega
      conv_lhs => rhs; rw [hN_split, pow_add]
      have hgm : growth ^ m ≠ 0 := (pow_pos hgrowth_pos m).ne'
      have hgnm : growth ^ (N - m) ≠ 0 := (pow_pos hgrowth_pos (N - m)).ne'
      field_simp
    have hwt_q₀ : ∀ q₀ : Path edges m v₀, wt q₀ ≤ (hi / lo) * growth ^ (-(m : ℤ)) := fun q₀ => by
      have h1 := perron_word_mass_bound edges w growth lo hi hlo hl hu hgrowth_pos m v₀ q₀
      refine h1.trans_eq ?_
      rw [one_div, zpow_neg, zpow_natCast, inv_pow]
    have hwt_lv : (hi / lo) * growth ^ (-(m : ℤ)) =
        (hi / lo) * growth * growth ^ (-(lvl i : ℤ)) := by
      rw [show -(m : ℤ) = 1 + -(lvl i : ℤ) by omega, zpow_add₀ hgrowth_pos.ne', zpow_one]
      ring
    calc (∑ q ∈ Hit, wt q)
        ≤ ∑ q₀ ∈ A_i, wt q₀ := hsub_fib.trans_eq (Finset.sum_congr rfl hfib_sum)
      _ ≤ ∑ _q₀ ∈ A_i, (hi / lo) * growth * growth ^ (-(lvl i : ℤ)) :=
          Finset.sum_le_sum fun q₀ _ => (hwt_q₀ q₀).trans_eq hwt_lv
      _ = (A_i.card : ℝ) * ((hi / lo) * growth * growth ^ (-(lvl i : ℤ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * ((hi / lo) * growth * growth ^ (-(lvl i : ℤ))) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hAi_le) (by positivity)
      _ = 2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ)) := by ring
  have hsum_total_one : (1 : ℝ) = ∑ q : Path edges N v₀, wt q := by
    dsimp [wt]
    have hwv0 : growth ^ N * w v₀ ≠ 0 := by
      have := hlo.trans_le (hl v₀); positivity
    rw [← Finset.sum_div, perron_word_mass_sum edges w growth hw N v₀, div_self hwv0]
  have hsum_ge_one : (1 : ℝ) ≤ ∑ i ∈ F, 2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ)) := by
    calc (1 : ℝ) = ∑ q : Path edges N v₀, wt q := hsum_total_one
      _ ≤ ∑ q ∈ F.biUnion (fun i => Finset.univ.filter (fun q : Path edges N v₀ =>
            (V_th i ∩ cIntervC k N (wordOfPath edges k hlabels q)).Nonempty)), wt q :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover_paths fun q _ _ => hwt_nn q
      _ ≤ ∑ i ∈ F, ∑ q ∈ Finset.univ.filter (fun q : Path edges N v₀ =>
            (V_th i ∩ cIntervC k N (wordOfPath edges k hlabels q)).Nonempty), wt q :=
          local_sum_biUnion_le F _ wt hwt_nn
      _ ≤ ∑ i ∈ F, 2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ)) :=
          Finset.sum_le_sum hsum_i
  have hmV_ge : ∀ i ∈ F,
      ENNReal.ofReal (c₀R * (2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ)))) ≤
        m_g (Metric.ediam (V_th i)) := by
    intro i _
    have hed_ge : ENNReal.ofReal (1 / (Qsel (J + lvl i + 1) : ℝ)) ≤ Metric.ediam (V_th i) := by
      have hne_top : Metric.ediam (V_th i) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (hV_ediam_le i) ENNReal.ofReal_lt_top)
      rw [← ENNReal.ofReal_toReal hne_top]
      exact ENNReal.ofReal_le_ofReal (hlvl_gt i).le
    have hsat := interpGauge_at_inv_Qsel hgrowth (show 1 ≤ J + lvl i + 1 by omega)
    have halg : c₀R * (2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ))) ≤
        growth ^ (-((J + lvl i + 1 : ℕ) : ℤ)) := by
      have heq2 : 2 * (c₀R * (2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ)))) =
          growth ^ (-((J + lvl i + 1 : ℕ) : ℤ)) := by
        calc 2 * (c₀R * (2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ))))
            = growth⁻¹ * (growth ^ J)⁻¹ * (growth ^ lvl i)⁻¹ := by
              dsimp [c₀R]
              have hhi0 : hi ≠ 0 := hhi.ne'
              have hlo0 : lo ≠ 0 := hlo.ne'
              have hg0 : growth ≠ 0 := hgrowth_pos.ne'
              have hgJ0 : growth ^ J ≠ 0 := (pow_pos hgrowth_pos J).ne'
              have hgL0 : growth ^ lvl i ≠ 0 := (pow_pos hgrowth_pos (lvl i)).ne'
              rw [zpow_neg, zpow_natCast]
              field_simp
          _ = growth ^ (-(1 : ℤ)) * growth ^ (-(J : ℤ)) * growth ^ (-(lvl i : ℤ)) := by
              rw [zpow_neg_one, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          _ = growth ^ (-((J + lvl i + 1 : ℕ) : ℤ)) := by
              rw [← zpow_add₀ hgrowth_pos.ne', ← zpow_add₀ hgrowth_pos.ne']
              congr 1
              push_cast
              ring
      have hnn : 0 ≤ c₀R * (2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ))) := by positivity
      linarith
    exact (ENNReal.ofReal_le_ofReal halg).trans (hsat ▸ (interpGauge_mono hgrowth) hed_ge)
  have hsum_lb : c₀ ≤ ∑ i ∈ F, m_g (Metric.ediam (V_th i)) :=
    calc c₀ = ENNReal.ofReal (c₀R * 1) := by simp [c₀]
      _ ≤ ENNReal.ofReal (c₀R * ∑ i ∈ F, 2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ))) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsum_ge_one hc₀R_pos.le)
      _ = ENNReal.ofReal (∑ i ∈ F, c₀R * (2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ)))) := by
          rw [Finset.mul_sum]
      _ = ∑ i ∈ F, ENNReal.ofReal (c₀R * (2 * (hi / lo) * growth * growth ^ (-(lvl i : ℤ)))) :=
          ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity
      _ ≤ ∑ i ∈ F, m_g (Metric.ediam (V_th i)) := Finset.sum_le_sum hmV_ge
  have hsum_ub : ∑ i ∈ F, m_g (Metric.ediam (V_th i)) ≤ S + ENNReal.ofReal δ0 := by
    have h1 : ∑ i ∈ F, m_g (Metric.ediam (V_th i)) ≤
        ∑ i ∈ F, (m_g (Metric.ediam (t i.1)) + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1))) :=
      Finset.sum_le_sum fun i _ => by
        calc m_g (Metric.ediam (V_th i))
            ≤ m_g (Metric.ediam (t i.1) + ENNReal.ofReal (2 * ρ i)) := by
              apply interpGauge_mono hgrowth
              calc Metric.ediam (V_th i) ≤ Metric.ediam (t i.1) + 2 * ENNReal.ofReal (ρ i) :=
                    local_ediam_thickening_le (hρ_pos i).le
                _ = Metric.ediam (t i.1) + ENNReal.ofReal (2 * ρ i) := by
                    rw [ENNReal.ofReal_mul (by norm_num)]; simp
          _ ≤ m_g (Metric.ediam (t i.1)) + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1)) := hρ_m i
    rw [Finset.sum_add_distrib] at h1
    have hS_ge : ∑ i ∈ F, m_g (Metric.ediam (t i.1)) ≤ S := by
      have h_img : ∑ i ∈ F, m_g (Metric.ediam (t i.1)) ≤
          ∑ i ∈ F, ⨆ _ : (t i.1).Nonempty, m_g (Metric.ediam (t i.1)) :=
        Finset.sum_le_sum fun i _ => by simp [i.2]
      have h_inj : Function.Injective (Subtype.val : {i : ℕ // (t i).Nonempty} → ℕ) :=
        Subtype.val_injective
      have h_sum_im : ∑ i ∈ F, ⨆ _ : (t i.1).Nonempty, m_g (Metric.ediam (t i.1)) =
          ∑ n ∈ F.image Subtype.val, ⨆ _ : (t n).Nonempty, m_g (Metric.ediam (t n)) :=
        (Finset.sum_image (f := fun n => ⨆ _ : (t n).Nonempty, m_g (Metric.ediam (t n)))
          fun a _ b _ hab => h_inj hab).symm
      exact h_img.trans (h_sum_im ▸ ENNReal.sum_le_tsum _)
    have hδ_ge : ∑ i ∈ F, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1)) ≤ ENNReal.ofReal δ0 := by
      have h_inj : Function.Injective (Subtype.val : {i : ℕ // (t i).Nonempty} → ℕ) :=
        Subtype.val_injective
      have h_sum_im : ∑ i ∈ F, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1)) =
          ∑ n ∈ F.image Subtype.val, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (n + 1)) :=
        (Finset.sum_image (f := fun n => ENNReal.ofReal (δ0 / (2 : ℝ) ^ (n + 1)))
          fun a _ b _ hab => h_inj hab).symm
      rw [h_sum_im, ← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (fun n : ℕ => δ0 / (2 : ℝ) ^ (n + 1)) =
          fun n => (δ0 * (1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ n := by
        ext n; rw [pow_succ, div_eq_mul_inv, mul_inv, ← inv_pow]; simp only [one_div]; ring
      have hsum_1 : Summable (fun n : ℕ => δ0 / (2 : ℝ) ^ (n + 1)) := by
        rw [h1]
        simpa only [one_div] using summable_geometric_two.mul_left (δ0 * (1 / 2 : ℝ))
      calc ∑ n ∈ F.image Subtype.val, δ0 / (2 : ℝ) ^ (n + 1)
          ≤ ∑' n : ℕ, δ0 / (2 : ℝ) ^ (n + 1) :=
            Summable.sum_le_tsum _ (fun _ _ => by positivity) hsum_1
        _ = δ0 := by rw [h1, tsum_mul_left, tsum_geometric_two]; ring
    exact h1.trans (add_le_add hS_ge hδ_ge)
  have hlt_c0 : S + ENNReal.ofReal δ0 < c₀ := by
    have h1 : S + ENNReal.ofReal δ0 = ENNReal.ofReal (S.toReal + δ0) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hδ0.le, ENNReal.ofReal_toReal hS_ne_top]
    rw [h1]
    exact (ENNReal.ofReal_lt_ofReal_iff hc₀R_pos).mpr (by dsimp [δ0]; linarith)
  exact not_lt_of_ge (hsum_lb.trans hsum_ub) hlt_c0

/-! ## Part 3: Unmarked tail nullity via spectral drop at `L = Fintype.card V` -/

/-- Subgraph retaining only unmarked edges `|a| < k`. -/
def unmarkedEdges {V : Type*} (edges : V → V → Finset ℤ) (k : ℕ) : V → V → Finset ℤ :=
  fun v u => (edges v u).filter (fun a => |a| < (k : ℤ))

lemma walkMass_add {V : Type*} [Fintype V] (A : V → V → ℝ) (w : V → ℝ) :
    ∀ (a b : ℕ) (v : V), walkMass A w (a + b) v = walkMass A (walkMass A w b) a v
  | 0, _, v => by simp [walkMass]
  | a + 1, b, v => by
    rw [Nat.add_right_comm a 1 b]
    simp only [walkMass]
    exact Finset.sum_congr rfl fun u _ => by rw [walkMass_add A w a b u]

private lemma walkMass_unmarked_nonneg {V : Type*} [Fintype V]
    (A : V → V → ℝ) (hA : ∀ v u, 0 ≤ A v u) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∀ n : ℕ, ∀ v : V, 0 ≤ walkMass A w n v
  | 0, v => hw v
  | n + 1, v =>
      Finset.sum_nonneg fun u _ => mul_nonneg (hA v u) (walkMass_unmarked_nonneg A hA w hw n u)

private lemma walkMass_le_of_eigenvector {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) {k : ℕ} (w : V → ℝ) {growth : ℝ}
    (hw_nn : ∀ v, 0 ≤ w v) (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v) :
    ∀ n : ℕ, ∀ v : V, walkMass (adjacency (unmarkedEdges edges k)) w n v ≤ growth ^ n * w v
  | 0, _ => by simp [walkMass]
  | n + 1, v => by
    calc walkMass (adjacency (unmarkedEdges edges k)) w (n + 1) v
        = ∑ u, adjacency (unmarkedEdges edges k) v u *
            walkMass (adjacency (unmarkedEdges edges k)) w n u := rfl
      _ ≤ ∑ u, adjacency edges v u * (growth ^ n * w u) := by
          refine Finset.sum_le_sum fun u _ => mul_le_mul ?_
            (walkMass_le_of_eigenvector edges w hw_nn hw n u)
            (walkMass_unmarked_nonneg _ (fun _ _ => Nat.cast_nonneg _) w hw_nn n u)
            (Nat.cast_nonneg _)
          unfold adjacency
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = growth ^ n * ∑ u, adjacency edges v u * w u := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => by ring
      _ = growth ^ (n + 1) * w v := by rw [hw v, pow_succ, mul_assoc]

private lemma walkMass_unmarked_lt_of_step {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) {k : ℕ} (w : V → ℝ) {growth lo : ℝ}
    (hlo : 0 < lo) (hgrowth : 0 < growth) (hl : ∀ v, lo ≤ w v)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    {y z : V} (hyz : (edges y z).Nonempty) {n : ℕ}
    (hz_lt : walkMass (adjacency (unmarkedEdges edges k)) w n z < growth ^ n * w z) :
    walkMass (adjacency (unmarkedEdges edges k)) w (n + 1) y < growth ^ (n + 1) * w y := by
  let B := adjacency (unmarkedEdges edges k)
  let A := adjacency edges
  have hw_nn : ∀ v, 0 ≤ w v := fun v => hlo.le.trans (hl v)
  have hB_le_A : ∀ u v, B u v ≤ A u v := fun u v => by
    dsimp only [A, B, adjacency]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hle_pt : ∀ u : V,
      B y u * walkMass B w n u ≤ A y u * (growth ^ n * w u) := fun u =>
    mul_le_mul (hB_le_A y u) (walkMass_le_of_eigenvector edges w hw_nn hw n u)
      (walkMass_unmarked_nonneg B (fun _ _ => Nat.cast_nonneg _) w hw_nn n u)
      (Nat.cast_nonneg _)
  have hlt_z : B y z * walkMass B w n z < A y z * (growth ^ n * w z) := by
    have hApos : (0 : ℝ) < A y z := by
      dsimp only [A, adjacency]
      exact_mod_cast Finset.card_pos.mpr hyz
    have hgn : 0 < growth ^ n * w z := mul_pos (pow_pos hgrowth n) (hlo.trans_le (hl z))
    by_cases hBz : B y z = 0
    · rw [hBz, zero_mul]
      exact mul_pos hApos hgn
    · have hBpos : 0 < B y z := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hBz)
      exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hz_lt hBpos)
        (mul_le_mul_of_nonneg_right (hB_le_A y z) hgn.le)
  have hsum_lt : (∑ u : V, B y u * walkMass B w n u) < ∑ u : V, A y u * (growth ^ n * w u) :=
    Finset.sum_lt_sum (fun u _ => hle_pt u) ⟨z, Finset.mem_univ z, hlt_z⟩
  refine hsum_lt.trans_eq ?_
  have hcomm : (∑ u : V, A y u * (growth ^ n * w u)) = growth ^ n * ∑ u : V, A y u * w u := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => by ring
  rw [hcomm, hw y, pow_succ, mul_assoc]

/-- Strongly connected graphs losing a marked edge have a uniform strict spectral contraction,
    making `eventualTail (unmarkedEdges edges k)` null under `interpGauge growth`. -/
theorem mkMetric_unmarkedTail_null {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) {k : ℕ}
    (w : V → ℝ) {growth lo : ℝ} (hlo : 0 < lo) (hgrowth : 1 < growth)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    (hl : ∀ v, lo ≤ w v)
    (hsc : ∀ u v : V, Relation.ReflTransGen (edgeRel edges) u v)
    (u₁ u₂ : V) (a_mark : ℤ) (ha_mem : a_mark ∈ edges u₁ u₂) (ha_mark_abs : |a_mark| = (k : ℤ)) :
    Measure.mkMetric (interpGauge growth)
      (eventualTail (unmarkedEdges edges k)) = 0 := by
  have : Nonempty V := ⟨u₁⟩
  let B := adjacency (unmarkedEdges edges k)
  let A := adjacency edges
  have hgrowth_pos : 0 < growth := by linarith
  have hw_nn : ∀ v, 0 ≤ w v := fun v => hlo.le.trans (hl v)
  have hu₁_lt : walkMass B w 1 u₁ < growth ^ 1 * w u₁ := by
    have hnot : a_mark ∉ unmarkedEdges edges k u₁ u₂ := by
      simp only [unmarkedEdges, Finset.mem_filter, not_and]; intro _; omega
    have hB_lt_A : B u₁ u₂ + 1 ≤ A u₁ u₂ := by
      have hsub : insert a_mark (unmarkedEdges edges k u₁ u₂) ⊆ edges u₁ u₂ :=
        Finset.insert_subset_iff.mpr ⟨ha_mem, Finset.filter_subset _ _⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at hcard
      dsimp only [A, B, adjacency]
      exact_mod_cast hcard
    have hpt : ∀ u : V, B u₁ u * w u ≤ A u₁ u * w u := fun u =>
      mul_le_mul_of_nonneg_right (by
        dsimp only [A, B, adjacency]
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)) (hw_nn u)
    have hstrict : B u₁ u₂ * w u₂ < A u₁ u₂ * w u₂ := by
      have hwu₂ : 0 < w u₂ := hlo.trans_le (hl u₂)
      linarith [mul_le_mul_of_nonneg_right hB_lt_A hwu₂.le]
    have hsum := Finset.sum_lt_sum (fun u _ => hpt u) ⟨u₂, Finset.mem_univ u₂, hstrict⟩
    simpa [walkMass, pow_one] using hsum.trans_eq (hw u₁)
  have hBack_mono : ∀ n, backReach edges u₁ n ⊆ backReach edges u₁ (n + 1) :=
    fun _ _ h => Finset.mem_union_left _ h
  have hBack_lt : ∀ n : ℕ, ∀ v ∈ backReach edges u₁ n,
      walkMass B w (n + 1) v < growth ^ (n + 1) * w v := by
    intro n
    induction n with
    | zero =>
      intro v hv
      simp only [backReach, Finset.mem_singleton] at hv
      subst hv
      exact hu₁_lt
    | succ n ih =>
      intro v hv
      rcases Finset.mem_union.mp hv with hpre | hnew
      · have hih := ih v hpre
        have hadd : walkMass B w (n + 2) v = walkMass B (walkMass B w 1) (n + 1) v := by
          simpa only [Nat.add_comm (n + 1) 1] using walkMass_add B w (n + 1) 1 v
        have h_next : walkMass B w (n + 2) v ≤ growth * walkMass B w (n + 1) v := by
          rw [hadd]
          calc walkMass B (walkMass B w 1) (n + 1) v
              ≤ walkMass B (fun z => growth * w z) (n + 1) v := by
                refine walkMass_mono B (fun _ _ => Nat.cast_nonneg _) (fun z => ?_) (n + 1) v
                simpa [pow_one] using walkMass_le_of_eigenvector edges w hw_nn hw 1 z
            _ = growth * walkMass B w (n + 1) v := walkMass_smul B w growth (n + 1) v
        calc walkMass B w (n + 2) v
            ≤ growth * walkMass B w (n + 1) v := h_next
          _ < growth * (growth ^ (n + 1) * w v) := mul_lt_mul_of_pos_left hih hgrowth_pos
          _ = growth ^ (n + 2) * w v := by ring
      · obtain ⟨u, huBack, hyz⟩ := (Finset.mem_filter.mp hnew).2
        exact walkMass_unmarked_lt_of_step edges w hlo hgrowth_pos hl hw hyz (ih u huBack)
  have hex_stab : ∃ m < Fintype.card V,
      backReach edges u₁ m = backReach edges u₁ (m + 1) := by
    by_contra hno
    push Not at hno
    have hcard_lt : ∀ m < Fintype.card V,
        (backReach edges u₁ m).card < (backReach edges u₁ (m + 1)).card := fun m hm =>
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hBack_mono m, hno m hm⟩)
    have hgrowth_card : ∀ m ≤ Fintype.card V, m + 1 ≤ (backReach edges u₁ m).card := by
      intro m hm
      induction m with
      | zero => simp [backReach]
      | succ m ih =>
        have hlt := hcard_lt m (by omega)
        have := ih (by omega)
        omega
    have hbot := hgrowth_card (Fintype.card V) le_rfl
    have htop := Finset.card_le_univ (backReach edges u₁ (Fintype.card V))
    omega
  obtain ⟨m, hm_lt, hm_eq⟩ := hex_stab
  have hbase_back : ∀ n : ℕ, u₁ ∈ backReach edges u₁ n := fun n => by
    induction n with
    | zero => simp [backReach]
    | succ n ih => exact Finset.mem_union_left _ ih
  have hall_back : ∀ v : V, v ∈ backReach edges u₁ m := by
    intro v
    have hreach : Relation.ReflTransGen (edgeRel edges) v u₁ := hsc v u₁
    refine Relation.ReflTransGen.head_induction_on hreach (hbase_back m)
      (fun {x y} hxy _ hy => ?_)
    have hmem_succ : x ∈ backReach edges u₁ (m + 1) :=
      Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, y, hy, hxy⟩)
    rwa [← hm_eq] at hmem_succ
  let L := Fintype.card V
  have hL_pos : 1 ≤ L := Fintype.card_pos
  have hmono_back_le : ∀ a b : ℕ, a ≤ b → backReach edges u₁ a ⊆ backReach edges u₁ b := by
    intro a b hab
    induction hab with
    | refl => exact Subset.rfl
    | step _ ih => exact ih.trans (hBack_mono _)
  have hall_L : ∀ v : V, walkMass B w L v < growth ^ L * w v := fun v => by
    have hv_in : v ∈ backReach edges u₁ (L - 1) :=
      hmono_back_le m (L - 1) (by omega) (hall_back v)
    have h := hBack_lt (L - 1) v hv_in
    rwa [show L - 1 + 1 = L by omega] at h
  let ratio : V → ℝ := fun v => walkMass B w L v / (growth ^ L * w v)
  let θ : ℝ := Finset.univ.sup' Finset.univ_nonempty ratio
  have hθ_nn : 0 ≤ θ := by
    have h1 : 0 ≤ ratio u₁ := div_nonneg
      (walkMass_unmarked_nonneg B (fun _ _ => Nat.cast_nonneg _) w hw_nn L u₁)
      (mul_pos (pow_pos hgrowth_pos L) (hlo.trans_le (hl u₁))).le
    exact h1.trans (Finset.le_sup' ratio (Finset.mem_univ u₁))
  have hθ_lt1 : θ < 1 := by
    rw [Finset.sup'_lt_iff]
    intro v _
    exact (div_lt_one (mul_pos (pow_pos hgrowth_pos L) (hlo.trans_le (hl v)))).mpr (hall_L v)
  have hstep_L : ∀ v : V, walkMass B w L v ≤ θ * growth ^ L * w v := fun v => by
    have h1 := Finset.le_sup' ratio (Finset.mem_univ v)
    have hden : 0 < growth ^ L * w v := mul_pos (pow_pos hgrowth_pos L) (hlo.trans_le (hl v))
    have := (div_le_iff₀ hden).mp h1
    linarith
  have hblocks : ∀ q : ℕ, ∀ v : V, walkMass B w (q * L) v ≤ θ ^ q * growth ^ (q * L) * w v := by
    intro q
    induction q with
    | zero => intro v; simp [walkMass]
    | succ q ih =>
      intro v
      have hsplit : (q + 1) * L = L + q * L := by ring
      rw [hsplit, walkMass_add]
      calc walkMass B (walkMass B w (q * L)) L v
          ≤ walkMass B (fun z => (θ ^ q * growth ^ (q * L)) * w z) L v :=
            walkMass_mono B (fun _ _ => Nat.cast_nonneg _) ih L v
        _ = (θ ^ q * growth ^ (q * L)) * walkMass B w L v := walkMass_smul B w _ L v
        _ ≤ (θ ^ q * growth ^ (q * L)) * (θ * growth ^ L * w v) :=
            mul_le_mul_of_nonneg_left (hstep_L v) (by positivity)
        _ = θ ^ (q + 1) * growth ^ (L + q * L) * w v := by
            rw [pow_succ, pow_add]; ring
  have hgeneral : ∀ n : ℕ, ∀ v : V,
      walkMass B (fun _ => 1) n v ≤ (θ ^ (n / L) * growth ^ n * w v) / lo := by
    intro n v
    have hleft := walkMass_mono B (fun _ _ => Nat.cast_nonneg _)
      (w₁ := fun _ => lo * 1) (w₂ := w) (fun u => by simpa using hl u) n v
    rw [walkMass_smul] at hleft
    have hdiv_mod : n = n % L + (n / L) * L := by
      calc n = L * (n / L) + n % L := (Nat.div_add_mod n L).symm
        _ = n % L + (n / L) * L := by ring
    have hright : walkMass B w n v ≤ θ ^ (n / L) * growth ^ n * w v := by
      conv_lhs => rw [hdiv_mod]
      rw [walkMass_add]
      calc walkMass B (walkMass B w ((n / L) * L)) (n % L) v
          ≤ walkMass B (fun z => (θ ^ (n / L) * growth ^ ((n / L) * L)) * w z) (n % L) v :=
            walkMass_mono B (fun _ _ => Nat.cast_nonneg _) (hblocks (n / L)) (n % L) v
        _ = (θ ^ (n / L) * growth ^ ((n / L) * L)) * walkMass B w (n % L) v :=
            walkMass_smul B w _ (n % L) v
        _ ≤ (θ ^ (n / L) * growth ^ ((n / L) * L)) * (growth ^ (n % L) * w v) :=
            mul_le_mul_of_nonneg_left (walkMass_le_of_eigenvector edges w hw_nn hw (n % L) v)
              (by positivity)
        _ = θ ^ (n / L) * growth ^ (n % L + (n / L) * L) * w v := by
            rw [pow_add]; ring
        _ = θ ^ (n / L) * growth ^ n * w v := by rw [← hdiv_mod]
    exact (le_div_iff₀ hlo).mpr (by simpa [mul_comm] using hleft.trans hright)
  apply measure_iUnion_null; intro N
  apply measure_iUnion_null; intro p
  apply measure_iUnion_null; intro v
  let ι : ℕ → Type _ := fun n => Path (unmarkedEdges edges k) n v
  let cov : ∀ n, ι n → Set ℝ := fun n q => localPathInterv (unmarkedEdges edges k) N p q
  let rad : ℕ → ℝ≥0∞ := fun n => gaugeScale (N + n)
  have hmain := Measure.mkMetric_le_liminf_sum (fixedTail (unmarkedEdges edges k) N p v)
    rad (tendsto_inv_Qsel_shift N) cov
    (Eventually.of_forall fun n q => ediam_gaugeInterv_le (N + n) (localEndPair _ q N p).1)
    (Eventually.of_forall fun n => localFixedTail_cover (unmarkedEdges edges k) N p n v)
    (interpGauge growth)
  have hterm_bd : ∀ᶠ n : ℕ in atTop,
      (∑ q : ι n, interpGauge growth (Metric.ediam (cov n q))) ≤
        ENNReal.ofReal ((w v / (lo * growth ^ N)) * θ ^ (n / L)) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hgauge_eq : interpGauge growth (rad n) =
        ENNReal.ofReal (growth ^ (-((N + n : ℕ) : ℤ))) :=
      interpGauge_at_inv_Qsel hgrowth (by omega)
    have hcard_le : (Fintype.card (ι n) : ℝ) ≤ (θ ^ (n / L) * growth ^ n * w v) / lo := by
      have hc := (card_path_eq_walkMass (unmarkedEdges edges k) n v).symm
      rw [← hc]
      exact hgeneral n v
    calc ∑ q : ι n, interpGauge growth (Metric.ediam (cov n q))
        ≤ ∑ _q : ι n, interpGauge growth (rad n) :=
          Finset.sum_le_sum fun q _ => (interpGauge_mono hgrowth)
            (ediam_gaugeInterv_le (N + n) (localEndPair _ q N p).1)
      _ = ((Fintype.card (ι n) : ℝ≥0∞)) * ENNReal.ofReal (growth ^ (-((N + n : ℕ) : ℤ))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hgauge_eq]
      _ = ENNReal.ofReal ((Fintype.card (ι n) : ℝ) * growth ^ (-((N + n : ℕ) : ℤ))) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal (((θ ^ (n / L) * growth ^ n * w v) / lo) *
            growth ^ (-((N + n : ℕ) : ℤ))) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ = ENNReal.ofReal ((w v / (lo * growth ^ N)) * θ ^ (n / L)) := by
          congr 1
          rw [Nat.cast_add, neg_add, zpow_add₀ hgrowth_pos.ne', zpow_neg, zpow_neg, zpow_natCast,
            zpow_natCast]
          have hgN : growth ^ N ≠ 0 := (pow_pos hgrowth_pos N).ne'
          have hgn : growth ^ n ≠ 0 := (pow_pos hgrowth_pos n).ne'
          have hlo0 : lo ≠ 0 := hlo.ne'
          field_simp
  have hlim_zero : Tendsto (fun n : ℕ => ENNReal.ofReal ((w v / (lo * growth ^ N)) * θ ^ (n / L)))
      atTop (nhds 0) := by
    have hdiv_top : Tendsto (fun n : ℕ => n / L) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro M
      exact ⟨M * L, fun n hn => (Nat.le_div_iff_mul_le hL_pos).mpr hn⟩
    have hpow0 : Tendsto (fun n : ℕ => θ ^ (n / L)) atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ_nn hθ_lt1).comp hdiv_top
    have hconst0 : Tendsto (fun n : ℕ => (w v / (lo * growth ^ N)) * θ ^ (n / L))
        atTop (nhds 0) := by
      simpa using hpow0.const_mul (w v / (lo * growth ^ N))
    simpa using ENNReal.tendsto_ofReal hconst0
  exact le_antisymm ((hmain.trans (liminf_le_liminf hterm_bd)).trans hlim_zero.liminf_eq.le) bot_le

lemma graphTree_sdiff_exactTail_null {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) {k : ℕ}
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges)
    (w : V → ℝ) {growth lo : ℝ} (hlo : 0 < lo) (hgrowth : 1 < growth)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    (hl : ∀ v, lo ≤ w v)
    (hsc : ∀ u v : V, Relation.ReflTransGen (edgeRel edges) u v)
    (u₁ u₂ : V) (a_mark : ℤ) (ha_mem : a_mark ∈ edges u₁ u₂) (ha_mark_abs : |a_mark| = (k : ℤ))
    (v₀ : V) :
    Measure.mkMetric (interpGauge growth)
      (graphTree edges k hlabels v₀ \ exactTail edges k) = 0 := by
  have : Nonempty V := ⟨v₀⟩
  have hk : 1 ≤ k := one_le_k_of_one_lt_growth hlabels hdet w hlo hgrowth hw hl
  have hsub : graphTree edges k hlabels v₀ \ exactTail edges k ⊆
      eventualTail (unmarkedEdges edges k) := by
    rintro x ⟨hxK, hx_not⟩
    have hx_ev := graphTree_subset_fixedTail edges hk hlabels hdet v₀ hxK
    have hx_le : apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4) :=
      cantorTreeC_subset_levelSet k hk (graphTree_subset_cantorTreeC edges k hlabels v₀ hxK)
    have hx_lt : apprExponent x < ENNReal.ofReal ((k : ℝ) / 4) :=
      lt_of_le_of_ne hx_le fun heq => hx_not ⟨hx_ev, heq⟩
    obtain ⟨L, hL_nn, hL_gt, hL_lt⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx_lt
    have hL_pos : 0 < L := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hL_gt)
    have hL_ltR : L < (k : ℝ) / 4 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hL_lt
    have hev_appr : ∀ᶠ j : ℕ in atTop, apprSeq x j < L := by
      have hevE : ∀ᶠ j : ℕ in atTop, apprSeqE x j < ENNReal.ofReal L :=
        eventually_lt_of_limsup_lt hL_gt
      exact hevE.mono fun j hj => by
        unfold apprSeqE at hj
        exact (ENNReal.ofReal_lt_ofReal_iff hL_pos).mp hj
    have heps0 : Tendsto (eps x) atTop (nhds 0) := by
      have hlt_half : ∀ᶠ j : ℕ in atTop, apprSeq x j ≤ L := hev_appr.mono fun _ h => h.le
      have hbound : ∀ᶠ j : ℕ in atTop, |eps x j| ≤ (L + 1) / (j : ℝ) := by
        filter_upwards [hlt_half, eventually_ge_atTop 1] with j hj hj1
        have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
        have heps : |eps x j| = distToNearestInt ((Qsel j : ℝ) * x) := rfl
        have hmul : (j : ℝ) * |eps x j| ≤ L := by simpa [apprSeq, heps] using hj
        exact (le_div_iff₀ hjpos).mpr (by linarith)
      exact tendsto_zero_of_eventually_abs_le_div hbound
    have heuler := euler_abs_defect_approx x heps0
    set δ : ℝ := (k : ℝ) - 4 * L
    have hδ : 0 < δ := by linarith
    have hev_diff := heuler.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < δ / 2))
    have hev_unmarked : ∀ᶠ j : ℕ in atTop, |defectShift x j| < (k : ℤ) := by
      have h_def : ∀ᶠ j : ℕ in atTop, |defect x j| < (k : ℤ) := by
        filter_upwards [hev_appr, hev_diff] with j hja hjd
        have hltR : |((defect x j : ℤ) : ℝ)| < (k : ℝ) := by linarith
        rw [← Int.cast_abs (R := ℝ)] at hltR
        exact_mod_cast hltR
      rw [eventually_atTop] at h_def ⊢
      obtain ⟨M, hM⟩ := h_def
      exact ⟨M, fun j hj => by rw [defectShift_eq_defect_succ]; exact hM (j + 1) (by omega)⟩
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hev_unmarked
    rcases Set.mem_iUnion.mp hx_ev with ⟨N, hx_ev1⟩
    rcases Set.mem_iUnion.mp hx_ev1 with ⟨p, hx_ev2⟩
    rcases Set.mem_iUnion.mp hx_ev2 with ⟨v, _, vertices, rfl, hwalk⟩
    let N' := N + J
    let vertices' : ℕ → V := fun i => vertices (J + i)
    refine Set.mem_iUnion.mpr ⟨N', Set.mem_iUnion.mpr
      ⟨(nearestInt ((Qsel N' : ℝ) * x), nearestInt ((Qsel (N' + 1) : ℝ) * x)),
        Set.mem_iUnion.mpr ⟨vertices' 0, rfl, vertices', rfl, fun i => ?_⟩⟩⟩
    dsimp only [unmarkedEdges]
    rw [Finset.mem_filter]
    refine ⟨?_, hJ (N' + i) (by dsimp [N']; omega)⟩
    simpa only [N', vertices', Nat.add_assoc] using hwalk (J + i)
  exact measure_mono_null hsub (mkMetric_unmarkedTail_null edges w hlo hgrowth hw hl hsc
    u₁ u₂ a_mark ha_mem ha_mark_abs)

/-! ## Part 4: Lattice invariance and local infinitude on `ℝ` and `UnitAddCircle` -/

/-- Every lattice element `z ∈ latticeL` has `defect z j = 0` eventually. -/
theorem defect_zero_of_mem_latticeL {z : ℝ} (hz : z ∈ Classification.latticeL) :
    ∀ᶠ j : ℕ in atTop, defect z j = 0 := by
  have hz_appr : Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * z))
      atTop (nhds 0) := (Classification.theorem2_classification z).mpr hz
  have hev1 : ∀ᶠ j : ℕ in atTop, (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * z) < 1 :=
    hz_appr.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hεz : Tendsto (eps z) atTop (nhds 0) := by
    have hbound : ∀ᶠ j : ℕ in atTop, |eps z j| ≤ 1 / (j : ℝ) := by
      filter_upwards [hev1, eventually_ge_atTop 1] with j hj hj1
      have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
      have heps : |eps z j| = distToNearestInt ((Qsel j : ℝ) * z) := rfl
      have hj' : distToNearestInt ((Qsel j : ℝ) * z) * (j : ℝ) ≤ 1 := by
        rw [mul_comm]; exact hj.le
      exact (le_div_iff₀ hjpos).mpr (by simpa [heps] using hj')
    exact tendsto_zero_of_eventually_abs_le_div hbound
  have heuler := euler_defect_eq_general z
  have h4j : Tendsto (fun j : ℕ => (4 * (j : ℝ) + 2) * eps z j) atTop (nhds 0) := by
    have h_abs : Tendsto (fun j : ℕ => |(4 * (j : ℝ) + 2) * eps z j|) atTop (nhds 0) := by
      have hub : Tendsto (fun j : ℕ =>
          4 * ((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * z)) + 2 * |eps z j|)
          atTop (nhds 0) := by
        simpa using (hz_appr.const_mul 4).add (hεz.abs.const_mul 2)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
        (Eventually.of_forall fun _ => abs_nonneg _) (eventually_atTop.mpr ⟨0, fun j _ => ?_⟩)
      have heps : |eps z j| = distToNearestInt ((Qsel j : ℝ) * z) := rfl
      have hpos : 0 ≤ 4 * (j : ℝ) + 2 := by positivity
      rw [abs_mul, abs_of_nonneg hpos, heps]
      ring_nf; exact le_rfl
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using h_abs)
  have h_def_0 : Tendsto (fun j : ℕ => ((defect z j : ℤ) : ℝ)) atTop (nhds 0) := by
    have hrhs : Tendsto (fun j : ℕ => (4 * (j : ℝ) + 2) * eps z j - eps z (j + 1) + eps z (j - 1))
        atTop (nhds 0) := by
      simpa using ((h4j.sub (hεz.comp (tendsto_add_atTop_nat 1))).add
        (hεz.comp tendsto_sub_one_atTop))
    exact hrhs.congr' (heuler.mono fun _ h => h.symm)
  have h_def_abs : Tendsto (fun j : ℕ => |((defect z j : ℤ) : ℝ)|) atTop (nhds 0) := by
    simpa only [abs_zero] using h_def_0.abs
  have hlt1 : ∀ᶠ j : ℕ in atTop, |((defect z j : ℤ) : ℝ)| < 1 :=
    h_def_abs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  exact int_eventually_zero_of_abs_lt_one hlt1

/-- Lattice shift invariance of `exactTail edges k`. -/
theorem exactTail_add_latticeL {V : Type*} (edges : V → V → Finset ℤ) {k : ℕ}
    (hlabels : edgeLabelsLe edges k) {y : ℝ} (hy : y ∈ Classification.latticeL) :
    (fun x : ℝ => x + y) ⁻¹' exactTail edges k = exactTail edges k := by
  have hfwd : ∀ (z : ℝ) {w : ℝ} (hw : w ∈ Classification.latticeL),
      z ∈ exactTail edges k → z + w ∈ exactTail edges k := by
    intro z w hw ⟨hz_tail, hz_app⟩
    have hdef_w := defect_zero_of_mem_latticeL hw
    have hw_appr : Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * w))
        atTop (nhds 0) := (Classification.theorem2_classification w).mpr hw
    have hεw : Tendsto (eps w) atTop (nhds 0) := by
      have hev1 : ∀ᶠ j : ℕ in atTop, (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * w) < 1 :=
        hw_appr.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
      have hbound : ∀ᶠ j : ℕ in atTop, |eps w j| ≤ 1 / (j : ℝ) := by
        filter_upwards [hev1, eventually_ge_atTop 1] with j hj hj1
        have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
        have heps : |eps w j| = distToNearestInt ((Qsel j : ℝ) * w) := rfl
        have hj' : distToNearestInt ((Qsel j : ℝ) * w) * (j : ℝ) ≤ 1 := by
          rw [mul_comm]; exact hj.le
        exact (le_div_iff₀ hjpos).mpr (by simpa [heps] using hj')
      exact tendsto_zero_of_eventually_abs_le_div hbound
    rcases Set.mem_iUnion.mp hz_tail with ⟨N, hz_tail1⟩
    rcases Set.mem_iUnion.mp hz_tail1 with ⟨p, hz_tail2⟩
    rcases Set.mem_iUnion.mp hz_tail2 with ⟨v, _, vertices, rfl, hwalk⟩
    have hbd_z : ∀ᶠ j : ℕ in atTop, |defect z j| ≤ (k : ℤ) := by
      rw [eventually_atTop]
      refine ⟨N + 1, fun j hj => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = N + m + 1 := ⟨j - (N + 1), by omega⟩
      have hds : defectShift z (N + m) = defect z (N + m + 1) :=
        defectShift_eq_defect_succ z (N + m)
      rw [← hds]
      exact hlabels _ _ _ (hwalk m)
    have hεz : Tendsto (eps z) atTop (nhds 0) := by
      have heuler := euler_defect_eq_general z
      have hbound : ∀ᶠ j : ℕ in atTop, |eps z j| ≤ ((k : ℝ) + 2) / (j : ℝ) := by
        filter_upwards [heuler, hbd_z, eventually_ge_atTop 1] with j hj_id hj_d hj1
        have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
        have he1 := Classification.abs_eps_le_half z (j + 1)
        have he2 := Classification.abs_eps_le_half z (j - 1)
        have h4j_pos : (0 : ℝ) < 4 * (j : ℝ) + 2 := by positivity
        have hmul : (4 * (j : ℝ) + 2) * |eps z j| ≤ (k : ℝ) + 1 := by
          have h1 : (4 * (j : ℝ) + 2) * eps z j =
              (defect z j : ℝ) + eps z (j + 1) - eps z (j - 1) := by linarith
          have h2 : |(4 * (j : ℝ) + 2) * eps z j| = (4 * (j : ℝ) + 2) * |eps z j| := by
            rw [abs_mul, abs_of_pos h4j_pos]
          rw [← h2, h1]
          have hdR : |(defect z j : ℝ)| ≤ (k : ℝ) := by
            rw [← Int.cast_abs]; exact_mod_cast hj_d
          have htri1 := abs_add_le ((defect z j : ℝ) + eps z (j + 1)) (-eps z (j - 1))
          have htri2 := abs_add_le (defect z j : ℝ) (eps z (j + 1))
          rw [abs_neg] at htri1
          rw [sub_eq_add_neg ((defect z j : ℝ) + eps z (j + 1)) (eps z (j - 1))]
          linarith
        have hjm : |eps z j| * (j : ℝ) ≤ ((k : ℝ) + 2) := by
          have : (j : ℝ) ≤ 4 * (j : ℝ) + 2 := by linarith
          have hnn := mul_le_mul_of_nonneg_right this (abs_nonneg (eps z j))
          linarith
        exact (le_div_iff₀ hjpos).mpr hjm
      exact tendsto_zero_of_eventually_abs_le_div hbound
    have hsum_eps : Tendsto (fun j : ℕ => eps z j + eps w j) atTop (nhds 0) := by
      simpa using hεz.add hεw
    have hsum_abs : Tendsto (fun j : ℕ => |eps z j + eps w j|) atTop (nhds 0) := by
      simpa only [abs_zero] using hsum_eps.abs
    have hlt_half : ∀ᶠ j : ℕ in atTop, |eps z j + eps w j| < 1 / 2 :=
      hsum_abs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    have hm_add : ∀ᶠ j : ℕ in atTop,
        nearestInt ((Qsel j : ℝ) * (z + w)) =
          nearestInt ((Qsel j : ℝ) * z) + nearestInt ((Qsel j : ℝ) * w) := by
      filter_upwards [hlt_half] with j hj
      unfold nearestInt at *
      rw [round_eq_iff]
      have hid : (Qsel j : ℝ) * (z + w) =
          ((round ((Qsel j : ℝ) * z) + round ((Qsel j : ℝ) * w) : ℤ) : ℝ) +
            (eps z j + eps w j) := by
        simp only [eps, nearestInt]; push_cast; ring
      have habs := abs_lt.mp hj
      rw [hid]
      exact ⟨by linarith, by linarith⟩
    have hdef_eq : ∀ᶠ j : ℕ in atTop, defectShift (z + w) j = defectShift z j := by
      rw [eventually_atTop] at hm_add hdef_w ⊢
      obtain ⟨M₁, hM₁⟩ := hm_add
      obtain ⟨M₂, hM₂⟩ := hdef_w
      refine ⟨max M₁ M₂ + 1, fun j hj => ?_⟩
      rw [defectShift_eq_defect_succ, defectShift_eq_defect_succ]
      unfold defect
      have hs0 := hM₁ j (by omega)
      have hs1 := hM₁ (j + 1) (by omega)
      have hs2 := hM₁ (j + 2) (by omega)
      have hsub1 : (j + 1 - 1 : ℕ) = j := by omega
      have hsub2 : (j + 1 + 1 : ℕ) = j + 2 := by omega
      rw [hsub1, hsub2, hs0, hs1, hs2]
      have hdw : defect w (j + 1) = 0 := hM₂ (j + 1) (by omega)
      unfold defect at hdw
      rw [hsub1, hsub2] at hdw
      linarith
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hdef_eq
    let N' := N + J
    let vertices' : ℕ → V := fun i => vertices (J + i)
    refine ⟨Set.mem_iUnion.mpr ⟨N', Set.mem_iUnion.mpr
      ⟨(nearestInt ((Qsel N' : ℝ) * (z + w)), nearestInt ((Qsel (N' + 1) : ℝ) * (z + w))),
        Set.mem_iUnion.mpr ⟨vertices' 0, rfl, vertices', rfl, fun i => ?_⟩⟩⟩, ?_⟩
    · rw [hJ (N' + i) (by dsimp [N']; omega)]
      simpa only [N', vertices', Nat.add_assoc] using hwalk (J + i)
    · change apprExponent (z + w) = ENNReal.ofReal ((k : ℝ) / 4)
      rw [apprExponent_add_latticeL z hw, hz_app]
  ext x
  simp only [Set.mem_preimage]
  constructor
  · intro hx
    have h := hfwd (x + y) (neg_mem_latticeL hy) hx
    have heq : x + y + -y = x := by ring
    rwa [heq] at h
  · intro hx
    exact hfwd x hy hx

/-- Local infinitude of `exactTail edges k` on every open interval `(a, b)` for a strongly
    connected marked deterministic graph with `growth > 1`. -/
theorem mkMetric_exactTail_inter_Ioo_eq_top {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) (k : ℕ)
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges)
    (w : V → ℝ) {growth lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 < hi) (hgrowth : 1 < growth)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    (hl : ∀ v, lo ≤ w v) (hu : ∀ v, w v ≤ hi)
    (hsc : ∀ u v : V, Relation.ReflTransGen (edgeRel edges) u v)
    (u₁ u₂ : V) (a_mark : ℤ) (ha_mem : a_mark ∈ edges u₁ u₂) (ha_mark_abs : |a_mark| = (k : ℤ))
    {a b_end : ℝ} (hab : a < b_end) :
    Measure.mkMetric (interpGauge growth) (exactTail edges k ∩ Set.Ioo a b_end) = ⊤ := by
  have : Nonempty V := ⟨u₁⟩
  have hk : 1 ≤ k := one_le_k_of_one_lt_growth hlabels hdet w hlo hgrowth hw hl
  refine GaugeCircle.mkMetric_inter_Ioo_eq_top_of_compact_tree (interpGauge growth)
    (graphTree edges k hlabels u₁) (exactTail edges k)
    (isCompact_graphTree edges k hlabels u₁)
    (mkMetric_graphTree_pos edges k hlabels hdet w hlo hhi hgrowth hw hl hu u₁)
    (graphTree_sdiff_exactTail_null edges hlabels hdet w hlo hgrowth hw hl hsc
      u₁ u₂ a_mark ha_mem ha_mark_abs u₁)
    (fun _ hy => exactTail_add_latticeL edges hlabels hy)
    (2 * k + 1) (J_cantor k) (by omega) (by unfold J_cantor; omega)
    (fun M w => (centerIntC k M w : ℝ) / (Qsel (J_cantor k + M + 1) : ℝ))
    (radC k) (fun M => radC_pos k M) (fun M => radC_le_quarter_inv k M hk)
    (fun M x hx => by
      have hc := Set.mem_iInter.mp (graphTree_subset_cantorTreeC edges k hlabels u₁ hx) M
      exact hc)
    hab

/-- Local infinitude of `circleExactTail edges k` on every nonempty open `U ⊆ UnitAddCircle`. -/
theorem mkMetric_circleExactTail_inter_open_eq_top {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) (k : ℕ)
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges)
    (w : V → ℝ) {growth lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 < hi) (hgrowth : 1 < growth)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    (hl : ∀ v, lo ≤ w v) (hu : ∀ v, w v ≤ hi)
    (hsc : ∀ u v : V, Relation.ReflTransGen (edgeRel edges) u v)
    (u₁ u₂ : V) (a_mark : ℤ) (ha_mem : a_mark ∈ edges u₁ u₂) (ha_mark_abs : |a_mark| = (k : ℤ))
    {U : Set UnitAddCircle} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    Measure.mkMetric (interpGauge growth) (circleExactTail edges k ∩ U) = ⊤ := by
  obtain ⟨a, b, hab, hwidth, hsub⟩ := exists_Ioo_subset_preimage_of_isOpen_circle hU_open hU_ne
  set A : Set ℝ := exactTail edges k ∩ Set.Ioo a b
  have hA_img : circleProj '' A ⊆ circleExactTail edges k ∩ U := by
    rintro _ ⟨x, ⟨hxE, hxI⟩, rfl⟩
    exact ⟨⟨x, hxE, rfl⟩, hsub hxI⟩
  have hle : Measure.mkMetric (interpGauge growth) A ≤
      Measure.mkMetric (interpGauge growth) (circleExactTail edges k ∩ U) :=
    le_trans
      (mkMetric_le_circleProj_image_of_subset_Ioo (interpGauge growth)
        (interpGauge_mono hgrowth) hwidth Set.inter_subset_right)
      (measure_mono hA_img)
  rw [mkMetric_exactTail_inter_Ioo_eq_top edges k hlabels hdet w hlo hhi hgrowth hw hl hu
    hsc u₁ u₂ a_mark ha_mem ha_mark_abs hab] at hle
  exact top_unique hle

/-! ## Part 5: Arbitrary-gauge comparison & multi-component complete theorems -/

private lemma interpGauge_at_gaugeScale {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 1 ≤ n) :
    interpGauge b (gaugeScale n) = (ENNReal.ofReal b ^ n)⁻¹ := by
  have hbpos : 0 < b := by linarith
  change interpGauge b (ENNReal.ofReal (1 / (Qsel n : ℝ))) = _
  rw [interpGauge_at_inv_Qsel hb hn, zpow_neg, zpow_natCast,
    ENNReal.ofReal_inv_of_pos (pow_pos hbpos n), ENNReal.ofReal_pow hbpos.le]

private lemma adjacent_bound_of_perron_lower {b : ℝ} (hb : 1 < b)
    (g : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hc : 0 < c) (n : ℕ) (hn : 1 ≤ n)
    (hlower : ENNReal.ofReal b / (c : ℝ≥0∞) ≤ perronCost b g (n + 1)) :
    interpGauge b (gaugeScale n) ≤ (c : ℝ≥0∞) * g (gaugeScale (n + 1)) := by
  have hbpos : 0 < b := by linarith
  let p : ℝ≥0∞ := ENNReal.ofReal b ^ n
  let q : ℝ≥0∞ := ENNReal.ofReal b ^ (n + 1)
  have hp0 : p ≠ 0 := pow_ne_zero n (ENNReal.ofReal_pos.mpr hbpos).ne'
  have hpT : p ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hq0 : q ≠ 0 := pow_ne_zero (n + 1) (ENNReal.ofReal_pos.mpr hbpos).ne'
  have hqT : q ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hq : q = ENNReal.ofReal b * p := by simp [p, q, pow_succ']
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hproduct : ENNReal.ofReal b ≤ (c : ℝ≥0∞) * (q * g (gaugeScale (n + 1))) :=
    (ENNReal.div_le_iff' hc0 (by simp)).mp hlower
  have hmul : q * p⁻¹ ≤ q * ((c : ℝ≥0∞) * g (gaugeScale (n + 1))) := by
    calc q * p⁻¹ = ENNReal.ofReal b := by
          rw [hq, mul_assoc, ENNReal.mul_inv_cancel hp0 hpT, mul_one]
      _ ≤ (c : ℝ≥0∞) * (q * g (gaugeScale (n + 1))) := hproduct
      _ = q * ((c : ℝ≥0∞) * g (gaugeScale (n + 1))) := by ring
  have hdiv := (ENNReal.mul_le_mul_iff_right hq0 hqT).mp hmul
  simpa only [interpGauge_at_gaugeScale hb hn] using hdiv

private lemma small_radius_le_of_adjacent_scale {b : ℝ} (hb : 1 < b)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (N : ℕ) (c : ℝ≥0∞)
    (hle : ∀ n ≥ N, interpGauge b (gaugeScale n) ≤ c * g (gaugeScale (n + 1))) :
    ∀ r ≤ gaugeScale N, interpGauge b r ≤ c * g r := by
  intro r hrN
  by_cases hr : r = 0
  · subst r; rw [interpGauge_zero]; exact bot_le
  have ht : Tendsto (fun m => gaugeScale (N + 1 + m)) atTop (nhds 0) :=
    tendsto_inv_Qsel_shift (N + 1)
  have hex : ∃ m, gaugeScale (N + 1 + m) < r :=
    ((tendsto_order.1 ht).2 r (pos_iff_ne_zero.mpr hr)).exists
  let m := Nat.find hex
  have hright : gaugeScale (N + m + 1) ≤ r := by
    have hspec := Nat.find_spec hex
    change gaugeScale (N + 1 + m) < r at hspec
    simpa only [Nat.add_right_comm N m 1] using hspec.le
  have hleft : r ≤ gaugeScale (N + m) := by
    cases hcase : m with
    | zero => simpa [hcase] using hrN
    | succ i =>
      have hi : i < Nat.find hex := by change i < m; omega
      have hmin := le_of_not_gt (Nat.find_min hex hi)
      have heq : N + (i + 1) = N + 1 + i := by omega
      simpa only [Nat.succ_eq_add_one, heq] using hmin
  exact ((interpGauge_mono hb) hleft).trans
    ((hle (N + m) (by omega)).trans (mul_le_mul_of_nonneg_left (hg hright) bot_le))

private lemma exists_small_radius_of_liminf_pos {b : ℝ} (hb : 1 < b)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hlim : 0 < liminf (perronCost b g) atTop) :
    ∃ (c : ℝ≥0) (δ : ℝ≥0∞), 0 < δ ∧
      ∀ r ≤ δ, interpGauge b r ≤ (c : ℝ≥0∞) * g r := by
  obtain ⟨l, hl0, hlt⟩ := exists_between hlim
  have hev : ∀ᶠ n in atTop, l < perronCost b g n := eventually_lt_of_lt_liminf hlt
  have hev' : ∀ᶠ n in atTop, 1 ≤ n ∧ l < perronCost b g n :=
    (eventually_ge_atTop 1).and hev
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev'
  let M : ℝ≥0 := (ENNReal.ofReal b / l).toNNReal + 1
  have hM_pos : 0 < M := add_pos_of_nonneg_of_pos bot_le zero_lt_one
  have hle_M : ENNReal.ofReal b / l ≤ (M : ℝ≥0∞) := by
    by_cases hlT : l = ⊤
    · simp [hlT]
    · have hl_ne : l ≠ 0 := hl0.ne'
      have hne_top : ENNReal.ofReal b / l ≠ ⊤ :=
        ENNReal.div_ne_top ENNReal.ofReal_ne_top hl_ne
      calc ENNReal.ofReal b / l
          = ((ENNReal.ofReal b / l).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hne_top).symm
        _ ≤ (M : ℝ≥0∞) := by
            exact_mod_cast (le_self_add : (ENNReal.ofReal b / l).toNNReal ≤ M)
  let c : ℝ≥0 := M
  have hc_pos : 0 < c := hM_pos
  have hratio : ∀ n ≥ N, ENNReal.ofReal b / (c : ℝ≥0∞) ≤ perronCost b g (n + 1) := by
    intro n hn
    have hn1 := hN (n + 1) (by omega)
    have hinv : ENNReal.ofReal b / (c : ℝ≥0∞) ≤ l := by
      by_cases hlT : l = ⊤
      · simp [hlT]
      · have h1 : (ENNReal.ofReal b / l) * l ≤ (c : ℝ≥0∞) * l :=
          mul_le_mul_of_nonneg_right hle_M bot_le
        rw [ENNReal.div_mul_cancel hl0.ne' hlT, mul_comm] at h1
        exact ENNReal.div_le_of_le_mul h1
    exact hinv.trans hn1.2.le
  refine ⟨c, gaugeScale N, ENNReal.ofReal_pos.mpr
      (one_div_pos.mpr (by exact_mod_cast Classification.Qsel_pos N)),
    small_radius_le_of_adjacent_scale hb g hg N (c : ℝ≥0∞) fun n hn => ?_⟩
  exact adjacent_bound_of_perron_lower hb g c hc_pos n (hN n hn).1 (hratio n hn)

private lemma exists_small_radius_of_liminf_top {b : ℝ} (hb : 1 < b)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hlim : liminf (perronCost b g) atTop = ⊤) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r ≤ δ, interpGauge b r ≤ (ε : ℝ≥0∞) * g r := by
  intro ε hε
  have hev : ∀ᶠ n in atTop, ENNReal.ofReal b / (ε : ℝ≥0∞) < perronCost b g n :=
    eventually_lt_of_lt_liminf (hlim ▸ ENNReal.div_lt_top ENNReal.ofReal_ne_top
      (by exact_mod_cast hε.ne'))
  have hev' : ∀ᶠ n in atTop, 1 ≤ n ∧ ENNReal.ofReal b / (ε : ℝ≥0∞) < perronCost b g n :=
    (eventually_ge_atTop 1).and hev
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev'
  refine ⟨gaugeScale N, ENNReal.ofReal_pos.mpr
      (one_div_pos.mpr (by exact_mod_cast Classification.Qsel_pos N)),
    small_radius_le_of_adjacent_scale hb g hg N (ε : ℝ≥0∞) fun n hn => ?_⟩
  exact adjacent_bound_of_perron_lower hb g ε hε n (hN n hn).1 (hN (n + 1) (by omega)).2.le

private lemma component_reachable {V : Type*} (edges : V → V → Finset ℤ) {v : V} :
    ∀ {a b : V} (hab : Relation.ReflTransGen (edgeRel edges) a b)
      (ha : Relation.ReflTransGen (edgeRel edges) v a)
      (hb : Relation.ReflTransGen (edgeRel edges) b v),
      Relation.ReflTransGen (edgeRel (componentEdges edges v))
        ⟨a, ha, hab.trans hb⟩ ⟨b, ha.trans hab, hb⟩ := by
  intro a b hab ha hb
  induction hab with
  | refl => exact .refl
  | tail had hdb ih =>
    have hdv : Relation.ReflTransGen (edgeRel edges) _ v := .head hdb hb
    exact (ih hdv).tail hdb

private lemma component_stronglyConnected {V : Type*} (edges : V → V → Finset ℤ) (v : V) :
    ∀ u₁ u₂ : Component edges v,
      Relation.ReflTransGen (edgeRel (componentEdges edges v)) u₁ u₂ := fun u₁ u₂ => by
  have h12 : Relation.ReflTransGen (edgeRel edges) u₁.1 u₂.1 := u₁.2.2.trans u₂.2.1
  exact component_reachable edges h12 u₁.2.1 u₂.2.2

private lemma component_edgeLabelsLe {V : Type*} {edges : V → V → Finset ℤ} {k : ℕ}
    (hlabels : edgeLabelsLe edges k) (v : V) :
    edgeLabelsLe (componentEdges edges v) k := fun u₁ u₂ a ha => hlabels u₁.1 u₂.1 a ha

private lemma component_deterministic {V : Type*} {edges : V → V → Finset ℤ}
    (hdet : Deterministic edges) (v : V) :
    Deterministic (componentEdges edges v) := fun u u₁ u₂ a ha₁ ha₂ =>
  Subtype.ext (hdet u.1 u₁.1 u₂.1 a ha₁ ha₂)

private lemma gauge_zero_eq_zero_of_liminf_lt_top {b : ℝ} (hb : 1 < b)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hfin : liminf (perronCost b g) atTop < ⊤) : g 0 = 0 := by
  by_contra h0
  obtain ⟨C, hC, hCT⟩ := exists_between hfin
  have hfreq : ∃ᶠ n : ℕ in atTop, perronCost b g n < C :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hC
  have hg_ev : ∀ᶠ n : ℕ in atTop, C ≤ perronCost b g n := by
    by_cases hgT : g 0 = ⊤
    · refine eventually_atTop.mpr ⟨0, fun n _ => ?_⟩
      have hgn : g 0 ≤ g (gaugeScale n) := hg bot_le
      have hb1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal b ^ n :=
        one_le_pow₀ (ENNReal.one_le_ofReal.mpr (by linarith))
      calc C ≤ ⊤ := le_top
        _ = 1 * ⊤ := (one_mul ⊤).symm
        _ ≤ ENNReal.ofReal b ^ n * g (gaugeScale n) :=
            mul_le_mul' hb1 (hgT ▸ hgn)
    · have hgR : 0 < (g 0).toReal := ENNReal.toReal_pos h0 hgT
      have hR : Tendsto (fun n : ℕ => b ^ n * (g 0).toReal) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt hb).atTop_mul_const hgR
      have hevR := (tendsto_atTop.mp hR) (C.toReal + 1)
      refine hevR.mono fun n hn => ?_
      have hc_le : C ≤ ENNReal.ofReal (C.toReal + 1) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hCT.ne]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      have hgn : g 0 ≤ g (gaugeScale n) := hg bot_le
      have hbg : ENNReal.ofReal (b ^ n * (g 0).toReal) ≤ perronCost b g n := by
        rw [ENNReal.ofReal_mul (pow_pos (by linarith) n).le, ENNReal.ofReal_pow (by linarith),
          ENNReal.ofReal_toReal hgT]
        exact mul_le_mul_of_nonneg_left hgn bot_le
      exact hc_le.trans ((ENNReal.ofReal_le_ofReal hn).trans hbg)
  obtain ⟨n, h1, h2⟩ := (hfreq.and_eventually hg_ev).exists
  exact (not_le_of_gt h1) h2

private lemma mkMetric_countable_eq_zero_of_gauge_zero {α : Type*}
    [EMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    {g : ℝ≥0∞ → ℝ≥0∞} (hg0 : g 0 = 0) {S : Set α} (hS : S.Countable) :
    Measure.mkMetric g S = 0 := by
  have hsingle : ∀ a : α, Measure.mkMetric g ({a} : Set α) = 0 := fun a => by
    apply le_antisymm _ bot_le
    rw [Measure.mkMetric_apply]
    refine iSup₂_le fun r _ => ?_
    let cov : ℕ → Set α := fun n => if n = 0 then {a} else ∅
    have hcov : ({a} : Set α) ⊆ ⋃ n, cov n := by
      intro x hx; exact Set.mem_iUnion.mpr ⟨0, by simpa [cov] using hx⟩
    have hdiam : ∀ n, Metric.ediam (cov n) ≤ r := fun n => by
      cases n <;> simp [cov]
    have hzero : ∀ n : ℕ, (⨆ _ : (cov n).Nonempty, g (Metric.ediam (cov n))) = 0 := fun n => by
      cases n
      · simp [cov, hg0]
      · simp [cov]
    calc (⨅ (t : ℕ → Set α) (_ : ({a} : Set α) ⊆ ⋃ n, t n)
          (_ : ∀ n, Metric.ediam (t n) ≤ r),
          ∑' n, ⨆ _ : (t n).Nonempty, g (Metric.ediam (t n)))
        ≤ ⨅ (_ : ({a} : Set α) ⊆ ⋃ n, cov n) (_ : ∀ n, Metric.ediam (cov n) ≤ r),
            ∑' n, ⨆ _ : (cov n).Nonempty, g (Metric.ediam (cov n)) := iInf_le _ cov
      _ ≤ ⨅ (_ : ∀ n, Metric.ediam (cov n) ≤ r),
            ∑' n, ⨆ _ : (cov n).Nonempty, g (Metric.ediam (cov n)) := iInf_le _ hcov
      _ ≤ ∑' n, ⨆ _ : (cov n).Nonempty, g (Metric.ediam (cov n)) := iInf_le _ hdiam
      _ = 0 := by simp [hzero]
  have hcov : S ⊆ ⋃ x : S, ({(x : α)} : Set α) := fun x hx =>
    Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Set.mem_singleton x⟩
  have : Countable S := hS.to_subtype
  exact measure_mono_null hcov (measure_iUnion_null fun x => hsingle x.1)

private lemma perronCost_liminf_zero_of_smaller {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (g : ℝ≥0∞ → ℝ≥0∞) (hfin : liminf (perronCost b g) atTop < ⊤) :
    liminf (perronCost a g) atTop = 0 := by
  obtain ⟨C, hC, hCT⟩ := exists_between hfin
  have hCfreq : ∃ᶠ n : ℕ in atTop, perronCost b g n < C :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hC
  have hb0 : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.mpr (ha.trans hab)).ne'
  have hbT : ENNReal.ofReal b ≠ ⊤ := ENNReal.ofReal_ne_top
  have hratio : ENNReal.ofReal a / ENNReal.ofReal b < 1 := by
    apply (ENNReal.div_lt_iff (Or.inl hb0) (Or.inl hbT)).mpr
    rw [one_mul, ENNReal.ofReal_lt_ofReal_iff (ha.trans hab)]
    exact hab
  have ht : Tendsto (fun n : ℕ => (ENNReal.ofReal a / ENNReal.ofReal b) ^ n * C)
      atTop (nhds 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio) (Or.inr hCT.ne)
  have hidentity : ∀ n : ℕ, perronCost a g n =
      (ENNReal.ofReal a / ENNReal.ofReal b) ^ n * perronCost b g n := fun n => by
    simp only [perronCost, div_eq_mul_inv, mul_pow, mul_assoc]
    rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel_left (pow_ne_zero n hb0)
      (ENNReal.pow_ne_top hbT)]
  apply le_antisymm _ bot_le
  by_contra hpos
  have hpos' : 0 < liminf (perronCost a g) atTop := lt_of_not_ge hpos
  obtain ⟨ε, hε, hεlim⟩ := exists_between hpos'
  have hev := (tendsto_order.1 ht).2 ε hε
  have hsmall : ∃ᶠ n : ℕ in atTop, perronCost a g n ≤ ε := by
    refine (hCfreq.and_eventually hev).mono fun n hn => ?_
    rw [hidentity n]
    exact (mul_le_mul_of_nonneg_left hn.1.le bot_le).trans hn.2.le
  exact hεlim.not_ge (liminf_le_of_frequently_le' hsmall)

private lemma exactTail_component_lift {V : Type*} (edges : V → V → Finset ℤ) (k : ℕ) (v : V) :
    exactTail (componentEdges edges v) k ⊆ exactTail edges k := by
  intro x ⟨hx_ev, hx_app⟩
  refine ⟨?_, hx_app⟩
  rcases Set.mem_iUnion.mp hx_ev with ⟨N, hx1⟩
  rcases Set.mem_iUnion.mp hx1 with ⟨p, hx2⟩
  rcases Set.mem_iUnion.mp hx2 with ⟨u, hu, vertices, rfl, hwalk⟩
  exact Set.mem_iUnion.mpr ⟨N, Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
    ⟨(vertices 0).1, hu, fun i => (vertices i).1, rfl, fun i => hwalk i⟩⟩⟩

/-- **Complete Finite-State Tail Theorem on `ℝ` (Paper 2 Theorem `thm:finite-state-tail`)**. -/
theorem thm_finite_state_tail_complete {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges) :
    -- (1) No marked cycle -> empty
    ((¬ ∃ u v : V, ∃ a, a ∈ edges u v ∧ |a| = (k : ℤ) ∧
        Relation.ReflTransGen (edgeRel edges) v u) →
      exactTail edges k = ∅) ∧
    -- (2) Dominant Perron root 1 -> countable
    ((∀ v : V,
        (∃ u₁ u₂ : Component edges v, ∃ a, a ∈ componentEdges edges v u₁ u₂ ∧ |a| = (k : ℤ)) →
        ∃ (w : Component edges v → ℝ) (lo : ℝ), 0 < lo ∧
          (∀ u, (∑ z, adjacency (componentEdges edges v) u z * w z) = w u) ∧
          ∀ u, lo ≤ w u) →
      (exactTail edges k).Countable) ∧
    -- (3) Supercritical dominant Perron root lamStar > 1 -> sharp arbitrary-gauge trichotomy
    (∀ (lamStar : ℝ), 1 < lamStar →
      (∀ v : V,
        (∃ u₁ u₂ : Component edges v, ∃ a, a ∈ componentEdges edges v u₁ u₂ ∧ |a| = (k : ℤ)) →
        ∃ (w : Component edges v → ℝ) (growth lo hi : ℝ),
          0 < lo ∧ 0 < hi ∧ 1 ≤ growth ∧ growth ≤ lamStar ∧
          (∀ u, (∑ z, adjacency (componentEdges edges v) u z * w z) = growth * w u) ∧
          (∀ u, lo ≤ w u) ∧ (∀ u, w u ≤ hi)) →
      (∃ (v₀ : V) (u₁ u₂ : Component edges v₀) (a_mark : ℤ),
        a_mark ∈ componentEdges edges v₀ u₁ u₂ ∧ |a_mark| = (k : ℤ) ∧
        ∃ (w : Component edges v₀ → ℝ) (lo hi : ℝ), 0 < lo ∧ 0 < hi ∧
          (∀ u, (∑ z, adjacency (componentEdges edges v₀) u z * w z) = lamStar * w u) ∧
          (∀ u, lo ≤ w u) ∧ (∀ u, w u ≤ hi)) →
      ∀ (g : ℝ≥0∞ → ℝ≥0∞), Monotone g →
        (liminf (perronCost lamStar g) atTop = 0 →
          Measure.mkMetric g (exactTail edges k) = 0) ∧
        (0 < liminf (perronCost lamStar g) atTop →
          (∀ a b : ℝ, a < b → Measure.mkMetric g (exactTail edges k ∩ Set.Ioo a b) = ⊤) ∧
          Measure.mkMetric g (exactTail edges k) = ⊤) ∧
        (liminf (perronCost lamStar g) atTop < ⊤ →
          ∃ E : ℕ → Set ℝ, exactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
        (liminf (perronCost lamStar g) atTop = ⊤ →
          ¬ ∃ E : ℕ → Set ℝ,
            exactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hno
    exact exactTail_empty_of_no_marked_return edges hk fun u v a hm ha hr =>
      hno ⟨u, v, a, hm, ha, hr⟩
  · intro hdata
    exact exactTail_countable_of_marked_roots_one edges hk hdata
  · intro lamStar hlam hcomp_bd ⟨v₀, u₁, u₂, a_mark, ha_mem, ha_abs, w₀, lo₀, hi₀, hlo₀, hhi₀,
        hw₀, hl₀, hu₀⟩ g hg
    have hsplit_comp := exactTail_eq_iUnion_marked_components edges hk
    have hcomp_Ioo : ∀ a b : ℝ, a < b →
        Measure.mkMetric (interpGauge lamStar) (exactTail edges k ∩ Set.Ioo a b) = ⊤ := by
      intro a b hab
      have hcomp_sub : exactTail (componentEdges edges v₀) k ⊆ exactTail edges k :=
        exactTail_component_lift edges k v₀
      have hdom := mkMetric_exactTail_inter_Ioo_eq_top (componentEdges edges v₀) k
        (component_edgeLabelsLe hlabels v₀) (component_deterministic hdet v₀) w₀ hlo₀ hhi₀
        hlam hw₀ hl₀ hu₀ (component_stronglyConnected edges v₀) u₁ u₂ a_mark ha_mem ha_abs hab
      exact top_unique (le_of_eq_of_le hdom.symm
        (measure_mono (Set.inter_subset_inter_left (Set.Ioo a b) hcomp_sub)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hzero
      refine mkMetric_exactTail_null_of_dominant_liminf_zero edges hk lamStar g hg hzero ?_
      intro v hv
      obtain ⟨w, growth, lo, hi, hlo, _, hge1, hle_lam, hw, hl, _⟩ := hcomp_bd v hv
      exact ⟨w, growth, lo, by linarith, hle_lam, hlo, hw, hl⟩
    · intro hpos
      obtain ⟨c, δ, hδ_pos, hcomp⟩ := exists_small_radius_of_liminf_pos hlam g hg hpos
      have hIoo : ∀ a b : ℝ, a < b → Measure.mkMetric g (exactTail edges k ∩ Set.Ioo a b) = ⊤ := by
        intro a b hab
        by_contra hne_top
        have hle := mkMetric_le_mul_of_eventually_le (interpGauge lamStar) g c hδ_pos hcomp
          (exactTail edges k ∩ Set.Ioo a b)
        rw [hcomp_Ioo a b hab] at hle
        exact (not_lt_of_ge hle) (ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr hne_top))
      refine ⟨hIoo, ?_⟩
      exact top_unique ((hIoo 0 1 zero_lt_one).symm.le.trans (measure_mono Set.inter_subset_left))
    · intro hfin
      have hg0 : g 0 = 0 := gauge_zero_eq_zero_of_liminf_lt_top hlam g hg hfin
      let I : Type _ :=
        Σ v : V, ℕ × (ℤ × ℤ) × Component edges v
      have : Countable V := inferInstance
      have hI_count : Countable I := inferInstance
      let E_idx : I → Set ℝ := fun ⟨v, N, p, u⟩ =>
        if _ : ∃ u₁ u₂ : Component edges v, ∃ a, a ∈ componentEdges edges v u₁ u₂ ∧ |a| = (k : ℤ)
        then fixedTail (componentEdges edges v) N p u ∩ exactTail edges k
        else ∅
      have hcov_idx : exactTail edges k ⊆ ⋃ i : I, E_idx i := by
        intro x hx
        have hx' : x ∈ eventualTail edges ∩
            {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} := hx
        rw [hsplit_comp] at hx'
        rcases Set.mem_iUnion.mp hx' with ⟨v, hx_v⟩
        rcases Set.mem_iUnion.mp hx_v with ⟨hv, hx_c⟩
        rcases Set.mem_iUnion.mp hx_c.1 with ⟨N, hx_N⟩
        rcases Set.mem_iUnion.mp hx_N with ⟨p, hx_p⟩
        rcases Set.mem_iUnion.mp hx_p with ⟨u, hu_pair, vertices, rfl, hwalk⟩
        refine Set.mem_iUnion.mpr ⟨⟨v, N, p, vertices 0⟩, ?_⟩
        dsimp [E_idx]
        simp only [hv, ↓reduceIte]
        exact ⟨⟨hu_pair, vertices, rfl, hwalk⟩, hx⟩
      have hfin_idx : ∀ i : I, Measure.mkMetric g (E_idx i) < ⊤ := by
        rintro ⟨v, N, p, u⟩
        dsimp [E_idx]
        by_cases hv :
            ∃ u₁ u₂ : Component edges v, ∃ a, a ∈ componentEdges edges v u₁ u₂ ∧ |a| = (k : ℤ)
        · simp only [hv, ↓reduceIte]
          obtain ⟨w, growth, lo, _, hlo, _, hge1, hle_lam, hw, hl, _⟩ := hcomp_bd v hv
          rcases eq_or_lt_of_le hge1 with heq1 | hgt1
          · have hsub_cnt :
                (fixedTail (componentEdges edges v) N p u ∩ exactTail edges k).Countable := by
              have hw1 : ∀ z, (∑ y, adjacency (componentEdges edges v) z y * w y) = w z := by
                intro z; simpa [← heq1] using hw z
              exact (fixedTail_finite_of_root_one (componentEdges edges v) w
                hlo hw1 hl N p u).countable.mono Set.inter_subset_left
            rw [mkMetric_countable_eq_zero_of_gauge_zero hg0 hsub_cnt]
            exact ENNReal.zero_lt_top
          · rcases eq_or_lt_of_le hle_lam with heq_lam | hlt_lam
            · have h_m := mkMetric_fixedTail_le (componentEdges edges v) w
                (by linarith) hlo (by simpa [heq_lam] using hw) hl g hg N p u
              have hfin_f : Measure.mkMetric g (fixedTail (componentEdges edges v) N p u) < ⊤ :=
                h_m.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (heq_lam ▸ hfin))
              exact (measure_mono Set.inter_subset_left).trans_lt hfin_f
            · have hz : liminf (perronCost growth g) atTop = 0 :=
                perronCost_liminf_zero_of_smaller (by linarith) hlt_lam g hfin
              have hnull := mkMetric_eventualTail_null (componentEdges edges v) w
                (by linarith) hlo hw hl g hg hz
              have hzero : Measure.mkMetric g
                  (fixedTail (componentEdges edges v) N p u ∩ exactTail edges k) = 0 :=
                measure_mono_null (Set.inter_subset_left.trans fun x hx =>
                  Set.mem_iUnion.mpr ⟨N, Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨u, hx⟩⟩⟩) hnull
              rw [hzero]
              exact ENNReal.zero_lt_top
        · simp only [hv, ↓reduceIte]
          simp
      let enc : Encodable I := Encodable.ofCountable I
      let E : ℕ → Set ℝ := fun n =>
        match @Encodable.decode I enc n with
        | some i => E_idx i
        | none => ∅
      refine ⟨E, ?_, fun n => ?_⟩
      · intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov_idx hx)
        exact Set.mem_iUnion.mpr ⟨@Encodable.encode I enc i, by
          simpa only [E, @Encodable.encodek _ enc] using hi⟩
      · cases hdec : @Encodable.decode I enc n with
        | none => simp [E, hdec]
        | some i => simpa only [E, hdec] using hfin_idx i
    · intro htop
      have hIoo := hcomp_Ioo 0 1 zero_lt_one
      have hpos : 0 < Measure.mkMetric (interpGauge lamStar) (exactTail edges k) :=
        lt_of_lt_of_le (hIoo ▸ ENNReal.zero_lt_top) (measure_mono Set.inter_subset_left)
      have hratio : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
          ∀ r ≤ δ, interpGauge lamStar r ≤ (ε : ℝ≥0∞) * g r :=
        exists_small_radius_of_liminf_top hlam g hg htop
      exact (not_countable_union_finite_of_ratio_tendsto_zero (interpGauge lamStar) g hratio hpos).2

/-- **Complete Finite-State Tail Theorem on `UnitAddCircle`**. -/
theorem thm_finite_state_tail_circle_complete {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges) :
    -- (1) No marked cycle -> empty
    ((¬ ∃ u v : V, ∃ a, a ∈ edges u v ∧ |a| = (k : ℤ) ∧
        Relation.ReflTransGen (edgeRel edges) v u) →
      circleExactTail edges k = ∅) ∧
    -- (2) Dominant Perron root 1 -> countable
    ((∀ v : V,
        (∃ u₁ u₂ : Component edges v, ∃ a, a ∈ componentEdges edges v u₁ u₂ ∧ |a| = (k : ℤ)) →
        ∃ (w : Component edges v → ℝ) (lo : ℝ), 0 < lo ∧
          (∀ u, (∑ z, adjacency (componentEdges edges v) u z * w z) = w u) ∧
          ∀ u, lo ≤ w u) →
      (circleExactTail edges k).Countable) ∧
    -- (3) Supercritical dominant Perron root lamStar > 1 -> sharp arbitrary-gauge trichotomy
    (∀ (lamStar : ℝ), 1 < lamStar →
      (∀ v : V,
        (∃ u₁ u₂ : Component edges v, ∃ a, a ∈ componentEdges edges v u₁ u₂ ∧ |a| = (k : ℤ)) →
        ∃ (w : Component edges v → ℝ) (growth lo hi : ℝ),
          0 < lo ∧ 0 < hi ∧ 1 ≤ growth ∧ growth ≤ lamStar ∧
          (∀ u, (∑ z, adjacency (componentEdges edges v) u z * w z) = growth * w u) ∧
          (∀ u, lo ≤ w u) ∧ (∀ u, w u ≤ hi)) →
      (∃ (v₀ : V) (u₁ u₂ : Component edges v₀) (a_mark : ℤ),
        a_mark ∈ componentEdges edges v₀ u₁ u₂ ∧ |a_mark| = (k : ℤ) ∧
        ∃ (w : Component edges v₀ → ℝ) (lo hi : ℝ), 0 < lo ∧ 0 < hi ∧
          (∀ u, (∑ z, adjacency (componentEdges edges v₀) u z * w z) = lamStar * w u) ∧
          (∀ u, lo ≤ w u) ∧ (∀ u, w u ≤ hi)) →
      ∀ (g : ℝ≥0∞ → ℝ≥0∞), Monotone g →
        (liminf (perronCost lamStar g) atTop = 0 →
          Measure.mkMetric g (circleExactTail edges k) = 0) ∧
        (0 < liminf (perronCost lamStar g) atTop →
          (∀ U : Set UnitAddCircle, IsOpen U → U.Nonempty →
            Measure.mkMetric g (circleExactTail edges k ∩ U) = ⊤) ∧
          Measure.mkMetric g (circleExactTail edges k) = ⊤) ∧
        (liminf (perronCost lamStar g) atTop < ⊤ →
          ∃ E : ℕ → Set UnitAddCircle,
            circleExactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
        (liminf (perronCost lamStar g) atTop = ⊤ →
          ¬ ∃ E : ℕ → Set UnitAddCircle,
            circleExactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤)) := by
  have hR := thm_finite_state_tail_complete edges k hk hlabels hdet
  refine ⟨?_, ?_, ?_⟩
  · intro hno
    rw [circleExactTail, hR.1 hno, Set.image_empty]
  · intro hdata
    exact (hR.2.1 hdata).image circleProj
  · intro lamStar hlam hcomp_bd hex_dom g hg
    have hR3 := hR.2.2 lamStar hlam hcomp_bd hex_dom g hg
    rcases hex_dom with ⟨v₀, u₁, u₂, a_mark, ha_mem, ha_abs, w₀, lo₀, hi₀, hlo₀, hhi₀,
      hw₀, hl₀, hu₀⟩
    have hcirc_open : ∀ U : Set UnitAddCircle, IsOpen U → U.Nonempty →
        Measure.mkMetric (interpGauge lamStar) (circleExactTail edges k ∩ U) = ⊤ := by
      intro U hU_open hU_ne
      have hcomp_sub :
          circleExactTail (componentEdges edges v₀) k ⊆ circleExactTail edges k := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, exactTail_component_lift edges k v₀ hx, rfl⟩
      have hdom := mkMetric_circleExactTail_inter_open_eq_top (componentEdges edges v₀) k
        (component_edgeLabelsLe hlabels v₀) (component_deterministic hdet v₀)
        w₀ hlo₀ hhi₀ hlam hw₀ hl₀ hu₀ (component_stronglyConnected edges v₀)
        u₁ u₂ a_mark ha_mem ha_abs hU_open hU_ne
      exact top_unique (le_of_eq_of_le hdom.symm
        (measure_mono (Set.inter_subset_inter_left U hcomp_sub)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hzero
      exact le_antisymm
        ((mkMetric_circleProj_image_le g hg _).trans_eq (hR3.1 hzero))
        bot_le
    · intro hpos
      obtain ⟨c, δ, hδ_pos, hcomp⟩ := exists_small_radius_of_liminf_pos hlam g hg hpos
      have hU_top : ∀ U : Set UnitAddCircle, IsOpen U → U.Nonempty →
          Measure.mkMetric g (circleExactTail edges k ∩ U) = ⊤ := by
        intro U hU_open hU_ne
        by_contra hne_top
        have hle := mkMetric_le_mul_of_eventually_le_circle (interpGauge lamStar) g c hδ_pos hcomp
          (circleExactTail edges k ∩ U)
        rw [hcirc_open U hU_open hU_ne] at hle
        exact (not_lt_of_ge hle) (ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr hne_top))
      refine ⟨hU_top, ?_⟩
      simpa using hU_top Set.univ isOpen_univ ⟨0, Set.mem_univ _⟩
    · intro hfin
      obtain ⟨Eℝ, hE_cov, hE_fin⟩ := hR3.2.2.1 hfin
      refine ⟨fun n => circleProj '' Eℝ n, ?_, fun n => ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hE_cov hx)
        exact Set.mem_iUnion.mpr ⟨n, x, hn, rfl⟩
      · exact (mkMetric_circleProj_image_le g hg _).trans_lt (hE_fin n)
    · intro htop
      have hpos : 0 < Measure.mkMetric (interpGauge lamStar) (circleExactTail edges k) := by
        have h := hcirc_open Set.univ isOpen_univ ⟨0, Set.mem_univ _⟩
        simp only [Set.inter_univ] at h
        rw [h]; exact ENNReal.zero_lt_top
      have hratio : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
          ∀ r ≤ δ, interpGauge lamStar r ≤ (ε : ℝ≥0∞) * g r :=
        exists_small_radius_of_liminf_top hlam g hg htop
      exact (not_countable_union_finite_of_ratio_tendsto_zero_circle
        (interpGauge lamStar) g hratio hpos).2

end

end FiniteStateComplete

/-! ## Axiom Dependencies (`#print axioms`) -/

#print axioms FiniteStateComplete.one_le_k_of_one_lt_growth
#print axioms FiniteStateComplete.wordOfPath_injective
#print axioms FiniteStateComplete.isCompact_graphTree
#print axioms FiniteStateComplete.graphTree_subset_fixedTail
#print axioms FiniteStateComplete.mkMetric_graphTree_pos
#print axioms FiniteStateComplete.mkMetric_unmarkedTail_null
#print axioms FiniteStateComplete.defect_zero_of_mem_latticeL
#print axioms FiniteStateComplete.exactTail_add_latticeL
#print axioms FiniteStateComplete.mkMetric_exactTail_inter_Ioo_eq_top
#print axioms FiniteStateComplete.mkMetric_circleExactTail_inter_open_eq_top
#print axioms FiniteStateComplete.thm_finite_state_tail_complete
#print axioms FiniteStateComplete.thm_finite_state_tail_circle_complete
