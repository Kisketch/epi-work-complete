import EpiFormal.FiniteStateGauge
import EpiFormal.GaugeLiminfComplete

/-! Finite labelled path covers along the selected denominators of e. -/

open Filter Topology Set MeasureTheory Classification GaugeNull GaugeCircle GaugeLiminf
open scoped ENNReal BigOperators

namespace FiniteStateGauge

noncomputable section

universe u

variable {V : Type u} [Fintype V]

/-- Parallel edges with different labels are counted separately. -/
def adjacency (edges : V → V → Finset ℤ) (v u : V) : ℝ :=
  (edges v u).card

/-- A finite walk beginning at v, with an edge label at each step. -/
def Path (edges : V → V → Finset ℤ) : ℕ → V → Type u
  | 0, _ => PUnit
  | n + 1, v => Σ u : V, {a // a ∈ edges v u} × Path edges n u

instance pathFintype (edges : V → V → Finset ℤ) : ∀ n v, Fintype (Path edges n v)
  | 0, _ => inferInstanceAs (Fintype PUnit)
  | n + 1, v => by
    letI (u : V) : Fintype (Path edges n u) := pathFintype edges n u
    change Fintype (Σ u : V, {a // a ∈ edges v u} × Path edges n u)
    infer_instance

lemma card_path_eq_walkMass (edges : V → V → Finset ℤ) (n : ℕ) (v : V) :
    (Fintype.card (Path edges n v) : ℝ) = walkMass (adjacency edges) (fun _ => 1) n v := by
  induction n generalizing v with
  | zero =>
    change (Fintype.card PUnit : ℝ) = 1
    rw [Fintype.card_unique, Nat.cast_one]
  | succ n ih =>
    change (Fintype.card (Σ u : V, {a // a ∈ edges v u} × Path edges n u) : ℝ) = _
    simp [Fintype.card_sigma, Fintype.card_prod, Fintype.card_coe, Nat.cast_sum, Nat.cast_mul,
      walkMass, adjacency, ih]

private def endPair (edges : V → V → Finset ℤ) :
    ∀ {n v}, Path edges n v → ℕ → ℤ × ℤ → ℤ × ℤ
  | 0, _, _, _, p => p
  | _n + 1, _, ⟨_, a, q⟩, N, p =>
    endPair edges q (N+1) (p.2, (4 * (N : ℤ) + 6) * p.2 + p.1 + a)

private abbrev mInt (x : ℝ) (j : ℕ) : ℤ := nearestInt ((Qsel j : ℝ) * x)

/-- A fixed starting position, nearest-integer pair, and initial vertex. -/
def fixedTail (edges : V → V → Finset ℤ) (N : ℕ) (p : ℤ × ℤ) (v : V) : Set ℝ :=
  {x | (mInt x N, mInt x (N+1)) = p ∧
    ∃ vertices : ℕ → V, vertices 0 = v ∧
      ∀ i, defectShift x (N+i) ∈ edges (vertices i) (vertices (i+1))}

/-- All points whose defect tail labels a walk somewhere in the graph. -/
def eventualTail (edges : V → V → Finset ℤ) : Set ℝ :=
  ⋃ N : ℕ, ⋃ p : ℤ × ℤ, ⋃ v : V, fixedTail edges N p v

omit [Fintype V] in
private lemma endPair_realizes_prefix (edges : V → V → Finset ℤ) (x : ℝ)
    (n N : ℕ) (vertices : ℕ → V)
    (hadm : ∀ i, defectShift x (N+i) ∈ edges (vertices i) (vertices (i+1))) :
    ∃ q : Path edges n (vertices 0),
      endPair edges q N (mInt x N, mInt x (N+1)) = (mInt x (N+n), mInt x (N+n+1)) := by
  induction n generalizing N vertices with
  | zero => exact ⟨PUnit.unit, rfl⟩
  | succ n ih =>
    let tail : ℕ → V := fun i => vertices (i+1)
    have htail : ∀ i, defectShift x (N+1+i) ∈ edges (tail i) (tail (i+1)) := by
      intro i
      simpa [tail, Nat.add_assoc, Nat.add_comm i 1] using hadm (i+1)
    obtain ⟨q,hq⟩ := ih (N+1) tail htail
    have ha : defectShift x N ∈ edges (vertices 0) (vertices 1) := by simpa using hadm 0
    refine ⟨⟨vertices 1, ⟨defectShift x N, ha⟩, q⟩, ?_⟩
    change endPair edges q (N+1)
      (mInt x (N+1), (4 * (N : ℤ)+6) * mInt x (N+1) + mInt x N + defectShift x N) = _
    rw [← nearestInt_add_two_eq x N, hq,
      show N+1+n = N+(n+1) by omega]

private def pathInterv (edges : V → V → Finset ℤ) (N : ℕ) (p : ℤ × ℤ)
    {n : ℕ} {v : V} (q : Path edges n v) : Set ℝ :=
  gaugeInterv (N+n) (endPair edges q N p).1

omit [Fintype V] in
private lemma fixedTail_cover (edges : V → V → Finset ℤ) (N : ℕ) (p : ℤ × ℤ)
    (n : ℕ) (v : V) :
    fixedTail edges N p v ⊆ ⋃ q : Path edges n v, pathInterv edges N p q := by
  intro x hx
  rcases hx with ⟨hp, vertices, rfl, hadm⟩
  obtain ⟨q,hq⟩ := endPair_realizes_prefix edges x n N vertices hadm
  refine Set.mem_iUnion.mpr ⟨q, ?_⟩
  unfold pathInterv
  rw [← hp, hq]
  exact mem_gaugeInterv_nearestInt x (N+n)

/-- Normalized covering cost at the real Perron base. -/
def perronCost (growth : ℝ) (g : ℝ≥0∞ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal growth ^ n * g (gaugeScale n)

/-- The fixed-tail upper bound with the initial-vertex factor of the Perron vector. -/
theorem mkMetric_fixedTail_le (edges : V → V → Finset ℤ)
    (w : V → ℝ) {growth lo : ℝ} (hgrowth : 0 < growth) (hlo : 0 < lo)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    (hl : ∀ u, lo ≤ w u) (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (N : ℕ) (p : ℤ × ℤ) (v : V) :
    Measure.mkMetric g (fixedTail edges N p v) ≤
      ENNReal.ofReal (w v / (lo * growth ^ N)) * liminf (perronCost growth g) atTop := by
  let C := ENNReal.ofReal (w v / (lo * growth ^ N))
  have hv : 0 < w v := hlo.trans_le (hl v)
  have hC : C ≠ 0 := (ENNReal.ofReal_pos.mpr (div_pos hv (by positivity))).ne'
  have hCT : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcov := Measure.mkMetric_le_liminf_sum (fixedTail edges N p v)
    (fun n => gaugeScale (N+n)) (tendsto_inv_Qsel_shift N) (fun n (q : Path edges n v) =>
      pathInterv edges N p q)
    (Eventually.of_forall (fun n q => ediam_gaugeInterv_le (N+n) (endPair edges q N p).1))
    (Eventually.of_forall (fun n => fixedTail_cover edges N p n v)) g
  have hsum : ∀ n, (∑ q : Path edges n v, g (Metric.ediam (pathInterv edges N p q))) ≤
      C * perronCost growth g (N+n) := by
    intro n
    have hc : (Fintype.card (Path edges n v) : ℝ) ≤ (growth ^ n * w v) / lo := by
      rw [card_path_eq_walkMass]
      have h := walkMass_mono (adjacency edges) (fun _ _ => Nat.cast_nonneg _)
        (w₁ := fun _ => lo * 1) (w₂ := w) (fun u => by simpa using hl u) n v
      rw [walkMass_smul, walkMass_of_eigenvector _ _ _ hw] at h
      exact (le_div_iff₀ hlo).mpr (by simpa [mul_comm] using h)
    have hc' : (Fintype.card (Path edges n v) : ℝ≥0∞) ≤ C * ENNReal.ofReal growth ^ (N+n) := by
      rw [← ENNReal.ofReal_natCast]
      dsimp only [C]
      rw [← ENNReal.ofReal_pow hgrowth.le, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      convert hc using 1
      rw [pow_add]
      field_simp
    calc
      _ ≤ ∑ _q : Path edges n v, g (gaugeScale (N+n)) :=
        Finset.sum_le_sum (fun q _ => hg (ediam_gaugeInterv_le (N+n) (endPair edges q N p).1))
      _ = (Fintype.card (Path edges n v) : ℝ≥0∞) * g (gaugeScale (N+n)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := by rw [perronCost, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hc' bot_le
  refine hcov.trans ((liminf_le_liminf (f := atTop) (Eventually.of_forall hsum)).trans ?_)
  have hmul := ENNReal.liminf_mul_le
    (u := fun _ : ℕ => C) (v := fun n => perronCost growth g (N+n)) (f := atTop)
    (Or.inl (by simpa using hC)) (Or.inl (by simpa using hCT))
  simpa only [Pi.mul_def, limsup_const, Nat.add_comm N, liminf_nat_add] using hmul

theorem mkMetric_eventualTail_null (edges : V → V → Finset ℤ)
    (w : V → ℝ) {growth lo : ℝ} (hgrowth : 0 < growth) (hlo : 0 < lo)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    (hl : ∀ u, lo ≤ w u) (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hzero : liminf (perronCost growth g) atTop = 0) :
    Measure.mkMetric g (eventualTail edges) = 0 := by
  apply measure_iUnion_null
  intro N
  apply measure_iUnion_null
  intro p
  apply measure_iUnion_null
  intro v
  have h := mkMetric_fixedTail_le edges w hgrowth hlo hw hl g hg N p v
  rw [hzero, mul_zero] at h
  exact le_antisymm h bot_le

theorem eventualTail_countable_cover_finite (edges : V → V → Finset ℤ)
    (w : V → ℝ) {growth lo : ℝ} (hgrowth : 0 < growth) (hlo : 0 < lo)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    (hl : ∀ u, lo ≤ w u) (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hfinite : liminf (perronCost growth g) atTop < ⊤) :
    ∃ E : (ℕ × (ℤ × ℤ) × V) → Set ℝ, eventualTail edges ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  refine ⟨fun i => fixedTail edges i.1 i.2.1 i.2.2, ?_, ?_⟩
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨N,hN⟩
    rcases Set.mem_iUnion.mp hN with ⟨p,hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨v,hv⟩
    exact Set.mem_iUnion.mpr ⟨⟨N,p,v⟩,hv⟩
  · intro ⟨N,p,v⟩
    exact (mkMetric_fixedTail_le edges w hgrowth hlo hw hl g hg N p v).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite)


/-- Uniformly bounded finite covers whose mesh tends to zero imply finiteness. -/
private lemma finite_of_bounded_mesh_covers (S : Set ℝ) (K : ℕ) (I : ℕ → Type u)
    [∀ n, Fintype (I n)] (U : ∀ n, I n → Set ℝ) (radius : ℕ → ℝ≥0∞)
    (hmesh : Tendsto radius atTop (nhds 0))
    (hcover : ∀ n, S ⊆ ⋃ q, U n q)
    (hdiam : ∀ n q, Metric.ediam (U n q) ≤ radius n)
    (hsize : ∀ n, Fintype.card (I n) ≤ K) :
    S.Finite := by
  classical
  by_contra hS
  have : Infinite S := infinite_coe_iff.mpr hS
  let f (i : Fin (K+1)) : S := Infinite.natEmbedding S i.val
  have hf : Function.Injective f := fun i j h =>
    Fin.ext ((Infinite.natEmbedding S).injective h)
  have hsep : ∀ᶠ n in atTop, ∀ i j : Fin (K+1), i ≠ j →
      radius n < edist ((f i : S) : ℝ) ((f j : S) : ℝ) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · have hdist : 0 < edist ((f i : S) : ℝ) ((f j : S) : ℝ) :=
        pos_iff_ne_zero.mpr (fun hd => hij (hf (Subtype.ext (edist_eq_zero.mp hd))))
      exact (hmesh.eventually (gt_mem_nhds hdist)).mono (fun _ h _ => h)
  obtain ⟨n, hn⟩ := hsep.exists
  have hmem : ∀ i : Fin (K+1), ∃ q : I n, (f i : ℝ) ∈ U n q :=
    fun i => Set.mem_iUnion.mp (hcover n (f i).property)
  choose q hq using hmem
  have hqinj : Function.Injective q := by
    intro i j heq
    by_contra hij
    have hj : (f j : ℝ) ∈ U n (q i) := heq ▸ hq j
    exact (hn i j hij).not_ge
      ((Metric.edist_le_ediam_of_mem (hq i) hj).trans (hdiam n (q i)))
  have h := (Fintype.card_le_of_injective q hqinj).trans (hsize n)
  simp at h

/-- At Perron base one, each class with fixed initial data is finite. -/
theorem fixedTail_finite_of_root_one (edges : V → V → Finset ℤ)
    (w : V → ℝ) {lo : ℝ} (hlo : 0 < lo)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = w v)
    (hl : ∀ u, lo ≤ w u) (N : ℕ) (p : ℤ × ℤ) (v : V) :
    (fixedTail edges N p v).Finite := by
  let K := ⌈w v / lo⌉₊
  refine finite_of_bounded_mesh_covers _ K (fun n => Path edges n v)
    (fun n q => pathInterv edges N p q) (fun n => gaugeScale (N+n))
    (tendsto_inv_Qsel_shift N) (fun n => fixedTail_cover edges N p n v)
    (fun n q => ediam_gaugeInterv_le (N+n) (endPair edges q N p).1) ?_
  intro n
  have hm := walkMass_mono (adjacency edges) (fun _ _ => Nat.cast_nonneg _)
    (w₁ := fun _ => lo * 1) (w₂ := w) (fun u => by simpa using hl u) n v
  have hw' : ∀ v, (∑ u, adjacency edges v u * w u) = 1 * w v :=
    fun u => by simpa using hw u
  rw [walkMass_smul, walkMass_of_eigenvector _ _ _ hw', one_pow, one_mul] at hm
  have hle := (le_div_iff₀ hlo).mpr (by simpa [mul_comm] using hm)
  rw [← card_path_eq_walkMass] at hle
  exact_mod_cast hle.trans (Nat.le_ceil _)

/-- The eventual-tail set at Perron base one is countable. -/
theorem eventualTail_countable_of_root_one (edges : V → V → Finset ℤ)
    (w : V → ℝ) {lo : ℝ} (hlo : 0 < lo)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = w v)
    (hl : ∀ u, lo ≤ w u) :
    (eventualTail edges).Countable :=
  countable_iUnion (fun N => countable_iUnion (fun p => countable_iUnion (fun v =>
    (fixedTail_finite_of_root_one edges w hlo hw hl N p v).countable)))

/-- The fixed-start upper bound also holds after projection to the circle. -/
theorem mkMetric_circle_fixedTail_le (edges : V → V → Finset ℤ)
    (w : V → ℝ) {growth lo : ℝ} (hgrowth : 0 < growth) (hlo : 0 < lo)
    (hw : ∀ v, (∑ u, adjacency edges v u * w u) = growth * w v)
    (hl : ∀ u, lo ≤ w u) (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (N : ℕ) (p : ℤ × ℤ) (v : V) :
    Measure.mkMetric g (circleProj '' fixedTail edges N p v) ≤
      ENNReal.ofReal (w v / (lo * growth ^ N)) * liminf (perronCost growth g) atTop :=
  (mkMetric_circleProj_image_le g hg _).trans (mkMetric_fixedTail_le edges w hgrowth hlo hw hl g hg N p v)



/-- The directed reachability relation forgets the labels but retains each edge. -/
def edgeRel (edges : V → V → Finset ℤ) (u v : V) : Prop :=
  (edges u v).Nonempty

omit [Fintype V] in
private lemma segment_reachable (edges : V → V → Finset ℤ)
    (vertices : ℕ → V) (labels : ℕ → ℤ)
    (hpath : ∀ i, labels i ∈ edges (vertices i) (vertices (i+1)))
    {i j : ℕ} (hij : i ≤ j) :
    Relation.ReflTransGen (edgeRel edges) (vertices i) (vertices j) := by
  induction j, hij using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ j _ ih => exact ih.tail ⟨labels j, hpath j⟩

/-- An infinitely recurring marked label lies on an edge with a return path. -/
theorem exists_marked_edge_with_return (edges : V → V → Finset ℤ)
    (vertices : ℕ → V) (labels : ℕ → ℤ)
    (hpath : ∀ i, labels i ∈ edges (vertices i) (vertices (i+1))) (k : ℕ)
    (hmark : ∃ᶠ i in atTop, |labels i| = (k : ℤ)) :
    ∃ u v a, a ∈ edges u v ∧ |a| = (k : ℤ) ∧ Relation.ReflTransGen (edgeRel edges) v u := by
  have hp : ∃ᶠ i in atTop, ∃ p : V × V,
      vertices i = p.1 ∧ vertices (i+1) = p.2 ∧ |labels i| = (k : ℤ) :=
    hmark.mono (fun i hi => ⟨(vertices i, vertices (i+1)), rfl, rfl, hi⟩)
  obtain ⟨⟨u,v⟩, huv⟩ := frequently_exists.mp hp
  obtain ⟨i, _, hiu, hiv, hi⟩ := frequently_atTop.mp huv 0
  obtain ⟨j, hij, hju, _, _⟩ := frequently_atTop.mp huv (i+1)
  have hmem := hpath i
  have hr := segment_reachable edges vertices labels hpath hij
  rw [hiu, hiv] at hmem
  rw [hiv, hju] at hr
  exact ⟨u,v,labels i,hmem,hi,hr⟩

/-- At a positive exact spectral level, extremal defects occur infinitely often. -/
theorem frequently_defectShift_eq_level {x : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hx : SpectralGap.apprExponent x = ENNReal.ofReal ((k : ℝ)/4)) (N : ℕ) :
    ∃ᶠ i in atTop, |defectShift x (N+i)| = (k : ℤ) := by
  have hfin : SpectralGap.apprExponent x ≠ ⊤ := hx ▸ ENNReal.ofReal_ne_top
  have hε := FullSpectrumDiscrete.eps_tendsto_zero_of_apprExponent_ne_top x hfin
  have happrox := FullSpectrumDiscrete.euler_abs_defect_approx x hε
  have hj1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : ENNReal.ofReal ((k : ℝ)/4 - 1/16) < SpectralGap.apprExponent x := by
    rw [hx]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hvisit : ∃ᶠ j in atTop, ENNReal.ofReal ((k : ℝ)/4 - 1/16) < SpectralGap.apprSeqE x j :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) ht
  have hbound := FullSpectrumDiscrete.eventually_abs_defect_le_of_apprExponent_le k
    (show (k : ℝ)/4 < ((k : ℝ)+1)/4 by linarith) x hx.le
  have hclose : ∀ᶠ j in atTop,
      -(1/4 : ℝ) < |(Classification.defect x j : ℝ)| - 4 * SpectralGap.apprSeq x j :=
    happrox.eventually (Ioi_mem_nhds (by norm_num))
  have hmarked : ∃ᶠ j in atTop, |Classification.defect x j| = (k : ℤ) := by
    refine ((hvisit.and_eventually hbound).and_eventually hclose).mono ?_
    rintro j ⟨⟨hup, hle⟩, hneg⟩
    have ht' : (k : ℝ)/4 - 1/16 < SpectralGap.apprSeq x j := by
      have hR := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr hup
      simpa only [SpectralGap.apprSeqE, ENNReal.toReal_ofReal (by linarith : 0 ≤ (k : ℝ)/4-1/16),
        ENNReal.toReal_ofReal (SpectralGap.apprSeq_nonneg x j)] using hR
    have hgt : (k : ℝ)-1/2 < |(Classification.defect x j : ℝ)| := by linarith
    apply le_antisymm hle
    by_contra! h
    have hz : |Classification.defect x j| ≤ (k : ℤ)-1 := by omega
    have hzR : |(Classification.defect x j : ℝ)| ≤ (k : ℝ)-1 := by exact_mod_cast hz
    linarith
  apply frequently_atTop.mpr
  intro i
  obtain ⟨j,hj,hd⟩ := frequently_atTop.mp hmarked (N+i+1)
  let m := j-(N+1)
  refine ⟨m, by dsimp [m]; omega, ?_⟩
  rwa [defectShift_eq_defect_succ, show N+m+1 = j by dsimp [m]; omega]

/-- The finite-state exact layer is empty when no marked edge has a return path. -/
theorem exactTail_empty_of_no_marked_return (edges : V → V → Finset ℤ) {k : ℕ} (hk : 1 ≤ k)
    (hNoMark : ∀ u v a, a ∈ edges u v → |a| = (k : ℤ) →
      ¬ Relation.ReflTransGen (edgeRel edges) v u) :
    eventualTail edges ∩ {x : ℝ | SpectralGap.apprExponent x = ENNReal.ofReal ((k : ℝ)/4)} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases Set.mem_iUnion.mp hx.1 with ⟨N,hN⟩
  rcases Set.mem_iUnion.mp hN with ⟨p,hp⟩
  rcases Set.mem_iUnion.mp hp with ⟨v,_,vertices,_,hpath⟩
  obtain ⟨u,v,a,hm,ha,hr⟩ := exists_marked_edge_with_return edges vertices
    (fun i => defectShift x (N+i)) hpath k (frequently_defectShift_eq_level hk hx.2 N)
  exact hNoMark u v a hm ha hr



/-- Every infinite walk in a finite graph ultimately remains in one component. -/
theorem exists_component_suffix (edges : V → V → Finset ℤ)
    (vertices : ℕ → V) (labels : ℕ → ℤ)
    (hpath : ∀ i, labels i ∈ edges (vertices i) (vertices (i+1))) :
    ∃ N, ∀ j ≥ N, Relation.ReflTransGen (edgeRel edges) (vertices N) (vertices j) ∧
      Relation.ReflTransGen (edgeRel edges) (vertices j) (vertices N) := by
  classical
  let recurrent (v : V) : Prop := ∃ᶠ i in atTop, vertices i = v
  have hfinite : ∀ᶠ i in atTop, ∀ v, ¬ recurrent v → vertices i ≠ v := by
    refine eventually_all.mpr (fun v => ?_)
    by_cases hv : recurrent v
    · exact Eventually.of_forall (fun _ hv' => (hv' hv).elim)
    · have h := not_frequently.mp hv
      exact h.mono (fun _ h' _ => h')
  obtain ⟨N,hN⟩ := eventually_atTop.mp hfinite
  have hv : recurrent (vertices N) := by
    by_contra h
    exact hN N le_rfl (vertices N) h rfl
  refine ⟨N, fun j hj => ⟨segment_reachable edges vertices labels hpath hj, ?_⟩⟩
  obtain ⟨i,hi,hv'⟩ := frequently_atTop.mp hv j
  simpa only [hv'] using segment_reachable edges vertices labels hpath hi

/-- The component represented by a vertex, including the representative. -/
def Component (edges : V → V → Finset ℤ) (v : V) :=
  {u : V // Relation.ReflTransGen (edgeRel edges) v u ∧ Relation.ReflTransGen (edgeRel edges) u v}

noncomputable instance componentFintype (edges : V → V → Finset ℤ) (v : V) :
    Fintype (Component edges v) := by
  classical
  unfold Component
  infer_instance

def componentEdges (edges : V → V → Finset ℤ) (v : V) :
    Component edges v → Component edges v → Finset ℤ :=
  fun u₁ u₂ => edges u₁.1 u₂.1

/-- An exact spectral layer splits into the finitely many marked component layers. -/
theorem exactTail_eq_iUnion_marked_components (edges : V → V → Finset ℤ) {k : ℕ} (hk : 1 ≤ k) :
    eventualTail edges ∩ {x : ℝ | SpectralGap.apprExponent x = ENNReal.ofReal ((k : ℝ)/4)} =
    ⋃ (v : V) (_ : ∃ u₁ u₂ : Component edges v, ∃ a, a ∈ componentEdges edges v u₁ u₂ ∧ |a| = (k : ℤ)),
      eventualTail (componentEdges edges v) ∩
        {x : ℝ | SpectralGap.apprExponent x = ENNReal.ofReal ((k : ℝ)/4)} := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx.1 with ⟨N,hN⟩
    rcases Set.mem_iUnion.mp hN with ⟨p,hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨v,_,vertices,_,hpath⟩
    obtain ⟨J,hJ⟩ := exists_component_suffix edges vertices (fun i => defectShift x (N+i)) hpath
    let tail (i : ℕ) : Component edges (vertices J) :=
      ⟨vertices (J+i), hJ _ (Nat.le_add_right J i)⟩
    have htail : ∀ i, defectShift x ((N+J)+i) ∈
        componentEdges edges (vertices J) (tail i) (tail (i+1)) := by
      intro i
      simpa only [tail, componentEdges, Nat.add_assoc] using hpath (J+i)
    obtain ⟨i,_,hmark⟩ := frequently_atTop.mp (frequently_defectShift_eq_level hk hx.2 (N+J)) 0
    refine Set.mem_iUnion.mpr ⟨vertices J, Set.mem_iUnion.mpr
      ⟨⟨tail i,tail (i+1),defectShift x ((N+J)+i),htail i,hmark⟩, ?_⟩⟩
    refine ⟨Set.mem_iUnion.mpr ⟨N+J,Set.mem_iUnion.mpr
      ⟨(mInt x (N+J),mInt x (N+J+1)), Set.mem_iUnion.mpr ⟨tail 0,rfl,tail,rfl,htail⟩⟩⟩,hx.2⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨v,hv⟩
    rcases Set.mem_iUnion.mp hv with ⟨_,hz⟩
    rcases Set.mem_iUnion.mp hz.1 with ⟨N,hN⟩
    rcases Set.mem_iUnion.mp hN with ⟨p,hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨u,hpair,vertices,hstart,hwalk⟩
    refine ⟨Set.mem_iUnion.mpr ⟨N,Set.mem_iUnion.mpr ⟨p,Set.mem_iUnion.mpr
      ⟨u.1,hpair,(fun i => (vertices i).1),congrArg Subtype.val hstart,hwalk⟩⟩⟩,hz.2⟩



/-- At the dominant root one, every marked component has a countable exact layer. -/
theorem exactTail_countable_of_marked_roots_one (edges : V → V → Finset ℤ) {k : ℕ} (hk : 1 ≤ k)
    (hdata : ∀ v : V,
      (∃ u₁ u₂ : Component edges v, ∃ a, a ∈ componentEdges edges v u₁ u₂ ∧ |a| = (k : ℤ)) →
      ∃ (w : Component edges v → ℝ) (lo : ℝ), 0 < lo ∧
        (∀ u, (∑ z, adjacency (componentEdges edges v) u z * w z) = w u) ∧
        ∀ u, lo ≤ w u) :
    (eventualTail edges ∩ {x : ℝ | SpectralGap.apprExponent x = ENNReal.ofReal ((k : ℝ)/4)}).Countable := by
  rw [exactTail_eq_iUnion_marked_components edges hk]
  refine countable_iUnion (fun v => countable_iUnion (fun hv => ?_))
  obtain ⟨w,lo,hlo,hw,hl⟩ := hdata v hv
  exact (eventualTail_countable_of_root_one _ w hlo hw hl).mono Set.inter_subset_left

/-- Zero normalized cost at a common upper Perron base implies global nullity. -/
theorem mkMetric_exactTail_null_of_dominant_liminf_zero (edges : V → V → Finset ℤ)
    {k : ℕ} (hk : 1 ≤ k) (b : ℝ) (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hcost : liminf (perronCost b g) atTop = 0)
    (hdata : ∀ v : V,
      (∃ u₁ u₂ : Component edges v, ∃ a, a ∈ componentEdges edges v u₁ u₂ ∧ |a| = (k : ℤ)) →
      ∃ (w : Component edges v → ℝ) (growth lo : ℝ), 0 < growth ∧ growth ≤ b ∧ 0 < lo ∧
        (∀ u, (∑ z, adjacency (componentEdges edges v) u z * w z) = growth * w u) ∧
        ∀ u, lo ≤ w u) :
    Measure.mkMetric g
      (eventualTail edges ∩ {x : ℝ | SpectralGap.apprExponent x = ENNReal.ofReal ((k : ℝ)/4)}) = 0 := by
  rw [exactTail_eq_iUnion_marked_components edges hk]
  refine measure_iUnion_null (fun v => measure_iUnion_null (fun hv => ?_))
  obtain ⟨w,growth,lo,hgrowth,hb,hlo,hw,hl⟩ := hdata v hv
  have hlim : liminf (perronCost growth g) atTop ≤ liminf (perronCost b g) atTop := by
    refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
    exact Eventually.of_forall (fun n => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal hb) n) bot_le)
  have hz : liminf (perronCost growth g) atTop = 0 := le_antisymm (hlim.trans hcost.le) bot_le
  exact measure_mono_null Set.inter_subset_left (mkMetric_eventualTail_null _ w hgrowth hlo hw hl g hg hz)


end
end FiniteStateGauge

#print axioms FiniteStateGauge.card_path_eq_walkMass
#print axioms FiniteStateGauge.mkMetric_fixedTail_le
#print axioms FiniteStateGauge.mkMetric_eventualTail_null
#print axioms FiniteStateGauge.eventualTail_countable_cover_finite


#print axioms FiniteStateGauge.fixedTail_finite_of_root_one
#print axioms FiniteStateGauge.eventualTail_countable_of_root_one
#print axioms FiniteStateGauge.mkMetric_circle_fixedTail_le

#print axioms FiniteStateGauge.exists_marked_edge_with_return
#print axioms FiniteStateGauge.frequently_defectShift_eq_level
#print axioms FiniteStateGauge.exactTail_empty_of_no_marked_return

#print axioms FiniteStateGauge.exists_component_suffix
#print axioms FiniteStateGauge.exactTail_eq_iUnion_marked_components


#print axioms FiniteStateGauge.exactTail_countable_of_marked_roots_one
#print axioms FiniteStateGauge.mkMetric_exactTail_null_of_dominant_liminf_zero

