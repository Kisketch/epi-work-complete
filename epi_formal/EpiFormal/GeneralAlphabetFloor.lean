import EpiFormal.ResidueMultiAsymptotic

/-!
# General Infinite-Alphabet Hausdorff Dimension Floor, Tail-Abscissa Limit, and Counterexample

Establishes the complete Bowen-free dimension theory for arbitrary continued-fraction alphabets
`A ⊆ ℕ_≥1` strictly on Lean's three base axioms (`propext`, `Classical.choice`, `Quot.sound`):

1. **Constant-Test-Function Upper Bound (`dimH_cfAlphabetSet_le_of_tsum_le_one`)**:
   If `∑'_{a ∈ A} a^(-2s) ≤ 1` (`s > 0`), then `dimH (cfAlphabetSet A) ≤ ENNReal.ofReal s`
   directly from `TransferOperatorDim.dimH_le_of_transferOp_le` with `v ≡ 1`.
2. **Strict Positivity for Every `|A| ≥ 2` (`pos_dimH_cfAlphabetSet_of_two_mem`,
   `pos_dimH_cfAlphabetSet_of_infinite`)**:
   Every alphabet containing at least two distinct digits (in particular every infinite alphabet)
   satisfies `0 < dimH (cfAlphabetSet A)`. Thus no single stationary infinite alphabet attains
   `dimH = 0`.
3. **Dirichlet Convergence Abscissa & General Tail-Abscissa Convergence Theorem
   (`alphabetAbscissa`, `lt_dimH_of_not_summable`, `alphabetAbscissa_le_dimH`,
   `tendsto_dimH_alphabet_tail`)**:
   For `alphabetAbscissa A := inf {s > 0 : ∑_{a ∈ A} a^(-2s) < ∞}`:
   - If `∑_{a ∈ A} a^(-2s)` diverges (`s > 0`), then `ENNReal.ofReal s < dimH (cfAlphabetSet A)`.
   - Unconditionally `ENNReal.ofReal (alphabetAbscissa A) ≤ dimH (cfAlphabetSet A)`.
   - The tail alphabets `A ∩ Set.Ici M` satisfy the exact limit
     `dimH (cfAlphabetSet (A ∩ Set.Ici M)) → ENNReal.ofReal (alphabetAbscissa A)` as `M → ∞`.
4. **Doubly-Exponential Sparse Counterexample (`doublyExpAlphabet`)**:
   For `A(k₀) = {2^(2^k) : k ≥ k₀}`:
   - `A(k₀)` is infinite with `alphabetAbscissa (A(k₀)) = 0`.
   - `0 < dimH (cfAlphabetSet (A(1))) ≤ ENNReal.ofReal (1 / 4) < ENNReal.ofReal (1 / 2)`,
     unconditionally disproving the naive infinite-alphabet `≥ 1/2` floor conjecture.
   - `Tendsto (fun k₀ => dimH (cfAlphabetSet (A(k₀)))) atTop (𝓝 0)`, proving that the universal
     infimum of `dimH (cfAlphabetSet A)` over infinite alphabets `A ⊆ ℕ_≥1` is strictly `0`
     (approached arbitrarily closely, never attained).
-/

namespace GeneralAlphabetFloor

open Set Filter Finset ENNReal Real MeasureTheory Topology
open TransferOperatorDim ResidueMultiAsymptotic

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Part 1: General `∑_{a ∈ A} a^(-2s) ≤ 1` Upper Bound via `v ≡ 1` -/

/-- **ENNReal Constant-Test-Function Upper Bound**:
    if `∑'_{a ∈ A} a^(-2s) ≤ 1` (`s > 0`), then `dimH (cfAlphabetSet A) ≤ ENNReal.ofReal s`. -/
theorem dimH_cfAlphabetSet_le_of_tsum_ennreal_le_one {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a)
    {s : ℝ} (hs : 0 < s)
    (hle : (∑' a : ℕ, if a ∈ A then ENNReal.ofReal ((a : ℝ) ^ (-(2 * s))) else 0) ≤ 1) :
    dimH (cfAlphabetSet A) ≤ ENNReal.ofReal s := by
  refine dimH_le_of_transferOp_le ha1 hs (v := fun _ => (1 : ℝ≥0∞)) (lo := 1) (hi := 1)
    zero_lt_one ENNReal.one_lt_top (fun _ _ => ⟨le_rfl, le_rfl⟩) ?_
  intro x hx
  unfold transferOp
  have hpt : ∀ a : ℕ,
      (if a ∈ A then (1 : ℝ≥0∞) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))) else 0) ≤
        if a ∈ A then ENNReal.ofReal ((a : ℝ) ^ (-(2 * s))) else 0 := by
    intro a
    split_ifs with ha
    · rw [one_mul]
      have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by have := ha1 a ha; omega : 0 < a)
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos ha_pos (by linarith [hx.1]) (by linarith))
    · exact le_rfl
  exact (ENNReal.tsum_le_tsum hpt).trans hle

/-- **Real Constant-Test-Function Upper Bound**:
    if `a ↦ a^(-2s)` is summable on `A` with sum `≤ 1` (`s > 0`), then
    `dimH (cfAlphabetSet A) ≤ ENNReal.ofReal s`. -/
theorem dimH_cfAlphabetSet_le_of_tsum_le_one {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a)
    {s : ℝ} (hs : 0 < s)
    (hsum : Summable (fun a : {a : ℕ // a ∈ A} => (a.1 : ℝ) ^ (-(2 * s))))
    (hle : (∑' a : {a : ℕ // a ∈ A}, (a.1 : ℝ) ^ (-(2 * s))) ≤ 1) :
    dimH (cfAlphabetSet A) ≤ ENNReal.ofReal s := by
  refine dimH_cfAlphabetSet_le_of_tsum_ennreal_le_one ha1 hs ?_
  have hsub : (∑' a : ℕ, if a ∈ A then ENNReal.ofReal ((a : ℝ) ^ (-(2 * s))) else 0) =
      ∑' a : {a : ℕ // a ∈ A}, ENNReal.ofReal ((a.1 : ℝ) ^ (-(2 * s))) := by
    have h1 := tsum_subtype A (fun a : ℕ => ENNReal.ofReal ((a : ℝ) ^ (-(2 * s))))
    rw [h1]
    refine tsum_congr fun a => ?_
    simp [Set.indicator_apply]
  rw [hsub, ← ENNReal.ofReal_tsum_of_nonneg (fun a => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum]
  exact (ENNReal.ofReal_le_ofReal hle).trans (by simp)

/-! ### Part 2: Strict Positivity of `dimH (cfAlphabetSet A)` for Every `|A| ≥ 2` -/

/-- Every alphabet `A ⊆ ℕ_≥1` with at least two distinct digits has strictly positive
    Hausdorff dimension `0 < dimH (cfAlphabetSet A)`. -/
theorem pos_dimH_cfAlphabetSet_of_two_mem {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hne : a ≠ b) :
    (0 : ℝ≥0∞) < dimH (cfAlphabetSet A) := by
  let S : Finset ℕ := {a, b}
  have hS1 : ∀ x ∈ S, 1 ≤ x := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx <;> rw [hx]
    · exact ha1 a ha
    · exact ha1 b hb
  have hSne : S.Nonempty := ⟨a, Finset.mem_insert_self a {b}⟩
  have hScard : S.card = 2 := Finset.card_pair hne
  let M : ℕ := S.sup id
  have hM1 : 1 ≤ M := le_trans (ha1 a ha) (Finset.le_sup (f := id) (Finset.mem_insert_self a {b}))
  have hM1_ge2 : (2 : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast (by omega : 2 ≤ M + 1)
  have hlogM_pos : 0 < Real.log ((M : ℝ) + 1) := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  let s₀ : ℝ := Real.log 2 / (4 * Real.log ((M : ℝ) + 1))
  have hs₀_pos : 0 < s₀ := by dsimp [s₀]; positivity
  have hnot_sum : ¬ Summable (wordSum S (2 * s₀)) := by
    intro hsum
    have hge1 : ∀ n : ℕ, (1 : ℝ) ≤ wordSum S (2 * s₀) n := by
      intro n
      have hterm : ∀ w : Fin n → {x : ℕ // x ∈ S},
          (((M : ℝ) + 1) ^ (-(2 * s₀))) ^ n ≤ (denQ (subWord n w)) ^ (-(2 * s₀)) := fun w => by
        have hpd := posDigits_subWord (fun x hx => hS1 x hx) n w
        have hmem : ∀ d ∈ subWord n w, d ≤ M := by
          intro d hd
          simp only [subWord, List.mem_ofFn] at hd
          obtain ⟨i, rfl⟩ := hd
          exact Finset.le_sup (f := id) (w i).2
        have hq_le : denQ (subWord n w) ≤ ((M : ℝ) + 1) ^ n := by
          simpa [subWord_length] using denQ_le_max_add_one_pow hpd hmem
        have h1 := Real.rpow_le_rpow_of_nonpos (denQ_pos hpd) hq_le (by linarith : -(2 * s₀) ≤ 0)
        have heq : (((M : ℝ) + 1) ^ n) ^ (-(2 * s₀)) = (((M : ℝ) + 1) ^ (-(2 * s₀))) ^ n := by
          rw [← Real.rpow_natCast ((M : ℝ) + 1) n, ← Real.rpow_mul (by positivity),
            ← Real.rpow_natCast (((M : ℝ) + 1) ^ (-(2 * s₀))) n,
            ← Real.rpow_mul (by positivity), mul_comm]
        rwa [heq] at h1
      have hsum_ge : (2 : ℝ) ^ n * (((M : ℝ) + 1) ^ (-(2 * s₀))) ^ n ≤ wordSum S (2 * s₀) n := by
        unfold wordSum
        have hcard : (Fintype.card (Fin n → {x : ℕ // x ∈ S}) : ℝ) = (2 : ℝ) ^ n := by
          rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, hScard]
          push_cast; rfl
        calc (2 : ℝ) ^ n * (((M : ℝ) + 1) ^ (-(2 * s₀))) ^ n
            = ∑ _w : Fin n → {x : ℕ // x ∈ S}, (((M : ℝ) + 1) ^ (-(2 * s₀))) ^ n := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
          _ ≤ ∑ w : Fin n → {x : ℕ // x ∈ S}, (denQ (subWord n w)) ^ (-(2 * s₀)) :=
              Finset.sum_le_sum fun w _ => hterm w
      have hbase_ge1 : (1 : ℝ) ≤ 2 * ((M : ℝ) + 1) ^ (-(2 * s₀)) := by
        have hMp : 0 < (M : ℝ) + 1 := by positivity
        have hpow_eq : ((M : ℝ) + 1) ^ (-(2 * s₀)) = Real.exp (-(Real.log 2 / 2)) := by
          rw [Real.rpow_def_of_pos hMp]
          congr 1
          dsimp only [s₀]
          field_simp [hlogM_pos.ne']
          ring
        calc (1 : ℝ) ≤ Real.exp (Real.log 2 + -(Real.log 2 / 2)) :=
              Real.one_le_exp (by linarith)
          _ = Real.exp (Real.log 2) * Real.exp (-(Real.log 2 / 2)) := Real.exp_add _ _
          _ = 2 * ((M : ℝ) + 1) ^ (-(2 * s₀)) := by rw [Real.exp_log two_pos, hpow_eq]
      have hpow1 : (1 : ℝ) ≤ (2 * ((M : ℝ) + 1) ^ (-(2 * s₀))) ^ n := one_le_pow₀ hbase_ge1
      rw [mul_pow] at hpow1
      exact hpow1.trans hsum_ge
    have ht0 := hsum.tendsto_atTop_zero
    obtain ⟨n, hn⟩ := (ht0.eventually (gt_mem_nhds one_pos)).exists
    linarith [hge1 n]
  have hs₀_le : s₀ ≤ poincareAbscissa S := by
    by_contra hlt
    exact hnot_sum (summable_wordSum_of_poincareAbscissa_lt hS1 (not_le.mp hlt))
  have hsub : cfAlphabetSet (S : Set ℕ) ⊆ cfAlphabetSet A := by
    rintro x ⟨hx01, hirr, hadm⟩
    refine ⟨hx01, hirr, fun i => ?_⟩
    have hi := hadm i
    simp only [Finset.mem_coe, S, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h <;> rw [h] <;> assumption
  have hdim_eq := dimH_cfAlphabetSet_finset_eq_poincareAbscissa hSne hS1
  have hpos_enn : (0 : ℝ≥0∞) < ENNReal.ofReal s₀ := ENNReal.ofReal_pos.mpr hs₀_pos
  calc (0 : ℝ≥0∞) < ENNReal.ofReal s₀ := hpos_enn
    _ ≤ ENNReal.ofReal (poincareAbscissa S) := ENNReal.ofReal_le_ofReal hs₀_le
    _ = dimH (cfAlphabetSet (S : Set ℕ)) := hdim_eq.symm
    _ ≤ dimH (cfAlphabetSet A) := dimH_mono hsub

/-- Every infinite alphabet `A ⊆ ℕ_≥1` has strictly positive Hausdorff dimension. -/
theorem pos_dimH_cfAlphabetSet_of_infinite {A : Set ℕ} (hinf : A.Infinite)
    (ha1 : ∀ a ∈ A, 1 ≤ a) :
    (0 : ℝ≥0∞) < dimH (cfAlphabetSet A) := by
  obtain ⟨a, ha, b, hb, hne⟩ := hinf.nontrivial
  exact pos_dimH_cfAlphabetSet_of_two_mem ha1 ha hb hne

/-! ### Part 3: Dirichlet Convergence Abscissa & General Tail-Abscissa Convergence Theorem -/

/-- Dirichlet convergence abscissa of an alphabet `A ⊆ ℕ_≥1`:
    `alphabetAbscissa A = inf {s > 0 : ∑_{a ∈ A} a^(-2s) < ∞}`. -/
def alphabetAbscissa (A : Set ℕ) : ℝ :=
  sInf {s : ℝ | 0 < s ∧ Summable (fun a : {a : ℕ // a ∈ A} => (a.1 : ℝ) ^ (-(2 * s)))}

lemma alphabetAbscissa_nonneg (A : Set ℕ) : 0 ≤ alphabetAbscissa A :=
  Real.sInf_nonneg fun _ hs => hs.1.le

lemma summable_nat_neg_two_mul_one :
    Summable (fun a : ℕ => (a : ℝ) ^ (-(2 * (1 : ℝ)))) := by
  have h : Summable (fun a : ℕ => ((a : ℝ) ^ (2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr one_lt_two
  refine h.congr fun a => ?_
  rw [mul_one, Real.rpow_neg (Nat.cast_nonneg a)]

lemma alphabetAbscissa_le_one (A : Set ℕ) : alphabetAbscissa A ≤ 1 := by
  refine csInf_le ⟨0, fun _ hs => hs.1.le⟩ ⟨one_pos, ?_⟩
  exact summable_nat_neg_two_mul_one.subtype A

lemma summable_of_alphabetAbscissa_lt {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a)
    {s : ℝ} (hs : alphabetAbscissa A < s) :
    Summable (fun a : {a : ℕ // a ∈ A} => (a.1 : ℝ) ^ (-(2 * s))) := by
  have hne : {t : ℝ | 0 < t ∧
      Summable (fun a : {a : ℕ // a ∈ A} => (a.1 : ℝ) ^ (-(2 * t)))}.Nonempty :=
    ⟨1, one_pos, summable_nat_neg_two_mul_one.subtype A⟩
  obtain ⟨s₁, ⟨_, hs₁_sum⟩, hs₁_lt⟩ := exists_lt_of_csInf_lt hne hs
  refine Summable.of_nonneg_of_le (fun a => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun a => ?_) hs₁_sum
  have ha_ge1 : (1 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast ha1 a.1 a.2
  exact Real.rpow_le_rpow_of_exponent_le ha_ge1 (by linarith)

lemma not_summable_of_lt_alphabetAbscissa {A : Set ℕ} {s : ℝ} (hs0 : 0 < s)
    (hs : s < alphabetAbscissa A) :
    ¬ Summable (fun a : {a : ℕ // a ∈ A} => (a.1 : ℝ) ^ (-(2 * s))) := fun hsum =>
  not_le_of_gt hs (csInf_le ⟨0, fun _ hx => hx.1.le⟩ ⟨hs0, hsum⟩)

/-- **Strict Divergence Lower Bound**: if `∑_{a ∈ A} a^(-2s)` diverges (`s > 0`),
    then strictly `ENNReal.ofReal s < dimH (cfAlphabetSet A)`. -/
theorem lt_dimH_of_not_summable {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a)
    {s : ℝ} (hs : 0 < s)
    (hdiv : ¬ Summable (fun a : {a : ℕ // a ∈ A} => (a.1 : ℝ) ^ (-(2 * s)))) :
    ENNReal.ofReal s < dimH (cfAlphabetSet A) := by
  have hex_fin : ∃ F : Finset {a : ℕ // a ∈ A},
      (2 : ℝ) ^ (2 * s) < ∑ a ∈ F, (a.1 : ℝ) ^ (-(2 * s)) := by
    by_contra hall
    push Not at hall
    exact hdiv (summable_of_sum_le (fun a => Real.rpow_nonneg (Nat.cast_nonneg _) _) hall)
  obtain ⟨F, hF⟩ := hex_fin
  let F' : Finset ℕ := F.map ⟨Subtype.val, Subtype.val_injective⟩
  have hF'_sub : (F' : Set ℕ) ⊆ A := by
    intro a ha
    simp only [F', Finset.mem_coe, Finset.mem_map, Function.Embedding.coeFn_mk] at ha
    obtain ⟨x, _, rfl⟩ := ha
    exact x.2
  have hF'_1 : ∀ a ∈ F', 1 ≤ a := fun a ha => ha1 a (hF'_sub ha)
  have hsum_gt1 : (1 : ℝ) < ∑ a ∈ F', ((a : ℝ) + 1) ^ (-(2 * s)) := by
    have hmap : ∑ a ∈ F', ((a : ℝ) + 1) ^ (-(2 * s)) =
        ∑ a ∈ F, ((a.1 : ℝ) + 1) ^ (-(2 * s)) := by
      simp [F']
    rw [hmap]
    have hpt : ∀ a ∈ F, (2 : ℝ) ^ (-(2 * s)) * (a.1 : ℝ) ^ (-(2 * s)) ≤
        ((a.1 : ℝ) + 1) ^ (-(2 * s)) := fun a _ => by
      have haR : (1 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast ha1 a.1 a.2
      have hle : (a.1 : ℝ) + 1 ≤ 2 * (a.1 : ℝ) := by linarith
      have h1 := Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < (a.1 : ℝ) + 1) hle
        (by linarith : -(2 * s) ≤ 0)
      rwa [Real.mul_rpow zero_le_two (by linarith)] at h1
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(2 * s)) := Real.rpow_pos_of_pos two_pos _
    have hmul : (1 : ℝ) < (2 : ℝ) ^ (-(2 * s)) * ∑ a ∈ F, (a.1 : ℝ) ^ (-(2 * s)) := by
      have hinv : (2 : ℝ) ^ (-(2 * s)) * (2 : ℝ) ^ (2 * s) = 1 := by
        rw [← Real.rpow_add two_pos]; simp
      calc (1 : ℝ) = (2 : ℝ) ^ (-(2 * s)) * (2 : ℝ) ^ (2 * s) := hinv.symm
        _ < (2 : ℝ) ^ (-(2 * s)) * ∑ a ∈ F, (a.1 : ℝ) ^ (-(2 * s)) :=
            mul_lt_mul_of_pos_left hF h2pos
    rw [Finset.mul_sum] at hmul
    exact lt_of_lt_of_le hmul (Finset.sum_le_sum hpt)
  have hF'_ne : F'.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hsum_gt1
    linarith
  have hcont : Continuous (fun t : ℝ => ∑ a ∈ F', ((a : ℝ) + 1) ^ (-(2 * t))) := by
    refine continuous_finsetSum _ fun a _ => ?_
    have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    exact Continuous.rpow continuous_const (continuous_const.mul continuous_id).neg
      (fun _ => Or.inl hpos.ne')
  have hev := (hcont.continuousAt (x := s)).eventually (Ioi_mem_nhds hsum_gt1)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ_pos, hδ_prop⟩ := hev
  set s' : ℝ := s + δ / 2 with hs'_def
  have hdist : dist s' s < δ := by
    rw [Real.dist_eq, hs'_def, show s + δ / 2 - s = δ / 2 by ring,
      abs_of_pos (half_pos hδ_pos)]
    linarith
  have hsum_s' : (1 : ℝ) < ∑ a ∈ F', ((a : ℝ) + 1) ^ (-(2 * s')) := hδ_prop hdist
  have hs_lt_s' : s < s' := by rw [hs'_def]; linarith
  have hs'_pos : 0 < s' := lt_trans hs hs_lt_s'
  have hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 : ℝ≥0∞) ≤ transferOp (F' : Set ℕ) s' (fun _ => 1) x := fun x hx => by
    rw [transferOp_finset_eq]
    have hnn : ∀ a ∈ F', (0 : ℝ) ≤ ((a : ℝ) + 1) ^ (-(2 * s')) :=
      fun a _ => Real.rpow_nonneg (by positivity) _
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (∑ a ∈ F', ((a : ℝ) + 1) ^ (-(2 * s'))) :=
          ENNReal.ofReal_le_ofReal hsum_s'.le
      _ = ∑ a ∈ F', ENNReal.ofReal (((a : ℝ) + 1) ^ (-(2 * s'))) :=
          ENNReal.ofReal_sum_of_nonneg hnn
      _ ≤ ∑ a ∈ F', (1 : ℝ≥0∞) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s'))) := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [one_mul]
          have hax : (0 : ℝ) < (a : ℝ) + x := by
            have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hF'_1 a ha
            linarith [hx.1]
          exact ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow_of_nonpos hax (by linarith [hx.2]) (by linarith))
  have hdim_F' : ENNReal.ofReal s' ≤ dimH (cfAlphabetSet (F' : Set ℕ)) :=
    le_dimH_of_transferOp_ge hF'_ne hF'_1 hs'_pos zero_lt_one ENNReal.one_lt_top
      (fun _ _ => ⟨le_rfl, le_rfl⟩) hsuper
  have hsub_cf : cfAlphabetSet (F' : Set ℕ) ⊆ cfAlphabetSet A := by
    rintro x ⟨hx01, hirr, hadm⟩
    exact ⟨hx01, hirr, fun i => hF'_sub (hadm i)⟩
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hs'_pos).mpr hs_lt_s')
    (hdim_F'.trans (dimH_mono hsub_cf))

/-- **Universal Abscissa Lower Bound**: for every `A ⊆ ℕ_≥1`,
    `ENNReal.ofReal (alphabetAbscissa A) ≤ dimH (cfAlphabetSet A)`. -/
theorem alphabetAbscissa_le_dimH {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a) :
    ENNReal.ofReal (alphabetAbscissa A) ≤ dimH (cfAlphabetSet A) := by
  by_cases h0 : alphabetAbscissa A = 0
  · rw [h0, ENNReal.ofReal_zero]; exact zero_le
  have habs_pos : 0 < alphabetAbscissa A :=
    lt_of_le_of_ne (alphabetAbscissa_nonneg A) (Ne.symm h0)
  by_contra hlt
  push Not at hlt
  have hfin : dimH (cfAlphabetSet A) ≠ ⊤ :=
    ne_top_of_lt (lt_of_lt_of_le hlt le_rfl)
  have hreal_lt : (dimH (cfAlphabetSet A)).toReal < alphabetAbscissa A := by
    have h1 := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hlt
    rwa [ENNReal.toReal_ofReal habs_pos.le] at h1
  let t : ℝ := max ((dimH (cfAlphabetSet A)).toReal) 0 +
    (alphabetAbscissa A - max ((dimH (cfAlphabetSet A)).toReal) 0) / 2
  have hmax_lt : max ((dimH (cfAlphabetSet A)).toReal) 0 < alphabetAbscissa A :=
    max_lt hreal_lt habs_pos
  have ht_pos : 0 < t := by dsimp [t]; linarith [le_max_right (dimH (cfAlphabetSet A)).toReal 0]
  have ht_lt : t < alphabetAbscissa A := by dsimp [t]; linarith
  have hdim_lt_t : dimH (cfAlphabetSet A) < ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff ht_pos).mpr (by
      dsimp [t]; linarith [le_max_left (dimH (cfAlphabetSet A)).toReal 0])
  have hdiv := not_summable_of_lt_alphabetAbscissa ht_pos ht_lt
  exact not_lt_of_gt hdim_lt_t (lt_dimH_of_not_summable ha1 ht_pos hdiv)

lemma alphabetAbscissa_tail_eq (A : Set ℕ) (M : ℕ) :
    alphabetAbscissa (A ∩ Set.Ici M) = alphabetAbscissa A := by
  unfold alphabetAbscissa
  congr 1
  ext s
  refine and_congr_right fun _ => ?_
  let f : ℕ → ℝ := fun a => (a : ℝ) ^ (-(2 * s))
  change Summable (f ∘ (Subtype.val : {a : ℕ // a ∈ A ∩ Set.Ici M} → ℕ)) ↔
    Summable (f ∘ (Subtype.val : {a : ℕ // a ∈ A} → ℕ))
  rw [summable_subtype_iff_indicator, summable_subtype_iff_indicator]
  have hdiff : ∀ᶠ a : ℕ in cofinite, (A ∩ Set.Ici M).indicator f a = A.indicator f a := by
    have hfin : {a : ℕ | a < M}.Finite := Set.finite_lt_nat M
    filter_upwards [hfin.compl_mem_cofinite] with a ha
    have hM : M ≤ a := not_lt.mp ha
    by_cases hA : a ∈ A
    · simp [hA, hM]
    · simp [hA]
  exact summable_congr_cofinite hdiff

/-- **General Tail Upper Bound**: if `∑_{a ∈ A} a^(-2s)` converges (`s > 0`),
    then eventually `dimH (cfAlphabetSet (A ∩ Set.Ici M)) ≤ ENNReal.ofReal s`. -/
theorem dimH_tail_le_of_summable {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a)
    {s : ℝ} (hs : 0 < s)
    (hsum : Summable (fun a : {a : ℕ // a ∈ A} => (a.1 : ℝ) ^ (-(2 * s)))) :
    ∀ᶠ M : ℕ in atTop, dimH (cfAlphabetSet (A ∩ Set.Ici M)) ≤ ENNReal.ofReal s := by
  let f : ℕ → ℝ := fun a => (a : ℝ) ^ (-(2 * s))
  let g : ℕ → ℝ := A.indicator f
  have hg_sum : Summable g := summable_subtype_iff_indicator.mp hsum
  have hg_nn : ∀ a : ℕ, 0 ≤ g a := fun a => by
    by_cases ha : a ∈ A
    · simp [g, f, ha, Real.rpow_nonneg (Nat.cast_nonneg _)]
    · simp [g, ha]
  have hlim : Tendsto (fun M : ℕ => (∑' a : ℕ, g a) - ∑ a ∈ Finset.range M, g a) atTop (𝓝 0) := by
    have ht := hg_sum.hasSum.tendsto_sum_nat
    simpa only [sub_self] using (tendsto_const_nhds (x := ∑' a : ℕ, g a)).sub ht
  filter_upwards [hlim.eventually (gt_mem_nhds one_pos)] with M hM_lt
  have hsub_sum : Summable (fun a : {a : ℕ // a ∈ A ∩ Set.Ici M} => (a.1 : ℝ) ^ (-(2 * s))) := by
    change Summable (f ∘ (Subtype.val : {a : ℕ // a ∈ A ∩ Set.Ici M} → ℕ))
    rw [summable_subtype_iff_indicator]
    refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_) hg_sum
    · by_cases h : a ∈ A ∩ Set.Ici M
      · simp [f, h, Real.rpow_nonneg (Nat.cast_nonneg _)]
      · simp [h]
    · by_cases h : a ∈ A ∩ Set.Ici M
      · simp [g, h, h.1]
      · simp [h, hg_nn a]
  have htsum_eq : (∑' a : {a : ℕ // a ∈ A ∩ Set.Ici M}, (a.1 : ℝ) ^ (-(2 * s))) =
      (∑' a : ℕ, g a) - ∑ a ∈ Finset.range M, g a := by
    rw [tsum_subtype (A ∩ Set.Ici M) (fun a : ℕ => (a : ℝ) ^ (-(2 * s)))]
    have hsplit : (∑' a : ℕ, g a) =
        (∑ a ∈ Finset.range M, g a) +
          ∑' a : ℕ, (A ∩ Set.Ici M).indicator (fun a : ℕ => (a : ℝ) ^ (-(2 * s))) a := by
      have h1 := (hg_sum.sum_add_tsum_nat_add M).symm
      rw [h1]
      congr 1
      have hshift : (∑' k : ℕ, g (k + M)) =
          ∑' a : ℕ, if M ≤ a then g a else 0 := by
        let e : ℕ ≃ Set.Ici M :=
          { toFun := fun k => ⟨k + M, Nat.le_add_left M k⟩
            invFun := fun a => a.1 - M
            left_inv := fun k => Nat.add_sub_cancel k M
            right_inv := fun a => Subtype.ext (Nat.sub_add_cancel a.2) }
        have hsub_e : (∑' k : ℕ, g (k + M)) = ∑' a : Set.Ici M, g a.1 :=
          Equiv.tsum_eq e (fun a : Set.Ici M => g a.1)
        rw [hsub_e, tsum_subtype (Set.Ici M) g]
        refine tsum_congr fun a => ?_
        simp [Set.indicator_apply]
      rw [hshift]
      refine tsum_congr fun a => ?_
      by_cases hM : M ≤ a <;> by_cases hA : a ∈ A <;> simp [g, f, hM, hA]
    linarith
  refine dimH_cfAlphabetSet_le_of_tsum_le_one (fun a ha => ha1 a ha.1) hs hsub_sum ?_
  rw [htsum_eq]
  exact hM_lt.le

/-- **General Tail-Abscissa Convergence Theorem**: for ANY alphabet `A ⊆ ℕ_≥1`,
    `dimH (cfAlphabetSet (A ∩ Set.Ici M)) → ENNReal.ofReal (alphabetAbscissa A)` as `M → ∞`. -/
theorem tendsto_dimH_alphabet_tail {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a) :
    Tendsto (fun M : ℕ => dimH (cfAlphabetSet (A ∩ Set.Ici M)))
      atTop (𝓝 (ENNReal.ofReal (alphabetAbscissa A))) := by
  refine tendsto_order.mpr ⟨fun a ha => ?_, fun b hb => ?_⟩
  · refine Filter.Eventually.of_forall fun M => ?_
    have hlo : ENNReal.ofReal (alphabetAbscissa A) ≤ dimH (cfAlphabetSet (A ∩ Set.Ici M)) := by
      rw [← alphabetAbscissa_tail_eq A M]
      exact alphabetAbscissa_le_dimH (fun x hx => ha1 x hx.1)
    exact lt_of_lt_of_le ha hlo
  · have h_lt_b : ENNReal.ofReal (alphabetAbscissa A) < b := hb
    by_cases hb_top : b = ⊤
    · subst hb_top
      have h1 : ∀ᶠ M : ℕ in atTop,
          dimH (cfAlphabetSet (A ∩ Set.Ici M)) ≤ ENNReal.ofReal (alphabetAbscissa A + 1) :=
        dimH_tail_le_of_summable ha1 (by linarith [alphabetAbscissa_nonneg A])
          (summable_of_alphabetAbscissa_lt ha1 (by linarith))
      filter_upwards [h1] with M hM
      exact lt_of_le_of_lt hM ENNReal.ofReal_lt_top
    · have habs_lt_b : alphabetAbscissa A < b.toReal := by
        have h1 := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hb_top).mpr h_lt_b
        rwa [ENNReal.toReal_ofReal (alphabetAbscissa_nonneg A)] at h1
      set s : ℝ := (alphabetAbscissa A + b.toReal) / 2 with hs_def
      have habs_lt_s : alphabetAbscissa A < s := by dsimp [s]; linarith
      have hs_pos : 0 < s := lt_of_le_of_lt (alphabetAbscissa_nonneg A) habs_lt_s
      have hs_lt_b : ENNReal.ofReal s < b := by
        rw [← ENNReal.ofReal_toReal hb_top]
        exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans hs_pos (by dsimp [s]; linarith))).mpr
          (by dsimp [s]; linarith)
      have hev :=
        dimH_tail_le_of_summable ha1 hs_pos (summable_of_alphabetAbscissa_lt ha1 habs_lt_s)
      filter_upwards [hev] with M hM
      exact lt_of_le_of_lt hM hs_lt_b

/-! ### Part 4: Doubly-Exponential Sparse Alphabet Counterexample -/

/-- Shifted doubly-exponential sparse alphabet `A(k₀) = {2^(2^k) : k ≥ k₀}`. -/
def doublyExpAlphabet (k₀ : ℕ) : Set ℕ :=
  {a : ℕ | ∃ k : ℕ, k₀ ≤ k ∧ a = 2 ^ (2 ^ k)}

lemma doublyExpAlphabet_ge_one (k₀ : ℕ) : ∀ a ∈ doublyExpAlphabet k₀, 1 ≤ a := by
  rintro a ⟨k, _, rfl⟩
  exact Nat.one_le_two_pow

lemma doublyExpAlphabet_infinite (k₀ : ℕ) : (doublyExpAlphabet k₀).Infinite := by
  let f : ℕ → ℕ := fun j => 2 ^ (2 ^ (k₀ + j))
  have hinj : Function.Injective f := by
    intro j₁ j₂ h
    have h1 : 2 ^ (k₀ + j₁) = 2 ^ (k₀ + j₂) :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
    have h2 : k₀ + j₁ = k₀ + j₂ :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2) h1
    omega
  have hsub : Set.range f ⊆ doublyExpAlphabet k₀ := by
    rintro _ ⟨j, rfl⟩
    exact ⟨k₀ + j, Nat.le_add_right k₀ j, rfl⟩
  exact Set.Infinite.mono hsub (Set.infinite_range_of_injective hinj)

lemma nat_add_one_le_two_pow (j : ℕ) : j + 1 ≤ 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ']
    omega

/-- Explicit geometric tail bound for `doublyExpAlphabet k₀`:
    whenever `1 / 2 ≤ s * 2^k₀`, we have `dimH (cfAlphabetSet (doublyExpAlphabet k₀)) ≤ s`. -/
theorem dimH_doublyExpAlphabet_le {k₀ : ℕ} {s : ℝ} (hs : 0 < s)
    (hcond : (1 / 2 : ℝ) ≤ s * (2 : ℝ) ^ k₀) :
    dimH (cfAlphabetSet (doublyExpAlphabet k₀)) ≤ ENNReal.ofReal s := by
  let φ : ℕ → {a : ℕ // a ∈ doublyExpAlphabet k₀} :=
    fun j => ⟨2 ^ (2 ^ (k₀ + j)), ⟨k₀ + j, Nat.le_add_right k₀ j, rfl⟩⟩
  have hbij : Function.Bijective φ := by
    refine ⟨fun j₁ j₂ h => ?_, fun ⟨a, ha⟩ => ?_⟩
    · have hv : 2 ^ (2 ^ (k₀ + j₁)) = 2 ^ (2 ^ (k₀ + j₂)) := congrArg Subtype.val h
      have h1 : 2 ^ (k₀ + j₁) = 2 ^ (k₀ + j₂) :=
        Nat.pow_right_injective (by norm_num : 2 ≤ 2) hv
      have h2 : k₀ + j₁ = k₀ + j₂ :=
        Nat.pow_right_injective (by norm_num : 2 ≤ 2) h1
      omega
    · obtain ⟨k, hk, rfl⟩ := ha
      refine ⟨k - k₀, Subtype.ext ?_⟩
      dsimp [φ]
      rw [Nat.add_sub_cancel' hk]
  let e : ℕ ≃ {a : ℕ // a ∈ doublyExpAlphabet k₀} := Equiv.ofBijective φ hbij
  have hpt : ∀ j : ℕ, ((e j).1 : ℝ) ^ (-(2 * s)) ≤ (1 / 2 : ℝ) ^ (j + 1) := by
    intro j
    have heval : ((e j).1 : ℝ) = (2 : ℝ) ^ (2 ^ (k₀ + j)) := by
      change ((2 ^ (2 ^ (k₀ + j)) : ℕ) : ℝ) = _
      push_cast; rfl
    rw [heval, ← Real.rpow_natCast (2 : ℝ) (2 ^ (k₀ + j)), ← Real.rpow_mul zero_le_two]
    have hpow_ge : ((j + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ k₀ * (2 : ℝ) ^ j * (2 * s) := by
      have h1 : ((j + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ j := by
        exact_mod_cast nat_add_one_le_two_pow j
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k₀ * (2 * s) := by linarith
      have h2j : (0 : ℝ) ≤ (2 : ℝ) ^ j := by positivity
      calc ((j + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ j := h1
        _ = 1 * (2 : ℝ) ^ j := (one_mul _).symm
        _ ≤ ((2 : ℝ) ^ k₀ * (2 * s)) * (2 : ℝ) ^ j := mul_le_mul_of_nonneg_right h2 h2j
        _ = (2 : ℝ) ^ k₀ * (2 : ℝ) ^ j * (2 * s) := by ring
    have hexp_eq : ((2 ^ (k₀ + j) : ℕ) : ℝ) * -(2 * s) =
        -((2 : ℝ) ^ k₀ * (2 : ℝ) ^ j * (2 * s)) := by
      rw [pow_add]; push_cast; ring
    rw [hexp_eq]
    have hhalf_eq : (1 / 2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg zero_le_two, Real.rpow_natCast, one_div, inv_pow]
    rw [hhalf_eq]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hgeom_sum : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) := by
    have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 2 : ℝ)
    refine h.congr fun j => ?_
    rw [pow_succ']
  have hgeom_val : (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1)) = 1 := by
    have hrew : (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) = fun j => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ j :=
      funext fun j => pow_succ' _ _
    rw [hrew, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have he_sum : Summable (fun j : ℕ => ((e j).1 : ℝ) ^ (-(2 * s))) :=
    Summable.of_nonneg_of_le (fun j => Real.rpow_nonneg (Nat.cast_nonneg _) _) hpt hgeom_sum
  have hA_sum : Summable (fun a : {a : ℕ // a ∈ doublyExpAlphabet k₀} => (a.1 : ℝ) ^ (-(2 * s))) :=
    (Equiv.summable_iff e).mp he_sum
  have hA_le : (∑' a : {a : ℕ // a ∈ doublyExpAlphabet k₀}, (a.1 : ℝ) ^ (-(2 * s))) ≤ 1 := by
    rw [← Equiv.tsum_eq e (fun a : {a : ℕ // a ∈ doublyExpAlphabet k₀} => (a.1 : ℝ) ^ (-(2 * s)))]
    exact (he_sum.tsum_le_tsum hpt hgeom_sum).trans_eq hgeom_val
  exact dimH_cfAlphabetSet_le_of_tsum_le_one (doublyExpAlphabet_ge_one k₀) hs hA_sum hA_le

/-- **Explicit Counterexample to the Naive Infinite-Alphabet `≥ 1/2` Conjecture**:
    for the infinite alphabet `A(1) = {2^(2^k) : k ≥ 1}`,
    `0 < dimH (cfAlphabetSet (A(1))) ≤ 1/4 < 1/2`. -/
theorem dimH_doublyExpAlphabet_one_le_quarter :
    dimH (cfAlphabetSet (doublyExpAlphabet 1)) ≤ ENNReal.ofReal (1 / 4) :=
  dimH_doublyExpAlphabet_le (by norm_num) (by norm_num)

theorem dimH_doublyExpAlphabet_one_lt_half :
    dimH (cfAlphabetSet (doublyExpAlphabet 1)) < ENNReal.ofReal (1 / 2) :=
  lt_of_le_of_lt dimH_doublyExpAlphabet_one_le_quarter
    ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num))

theorem zero_lt_dimH_doublyExpAlphabet (k₀ : ℕ) :
    (0 : ℝ≥0∞) < dimH (cfAlphabetSet (doublyExpAlphabet k₀)) :=
  pos_dimH_cfAlphabetSet_of_infinite (doublyExpAlphabet_infinite k₀) (doublyExpAlphabet_ge_one k₀)

/-- `alphabetAbscissa (doublyExpAlphabet k₀) = 0` for every shift `k₀`. -/
theorem alphabetAbscissa_doublyExpAlphabet (k₀ : ℕ) :
    alphabetAbscissa (doublyExpAlphabet k₀) = 0 := by
  refine le_antisymm ?_ (alphabetAbscissa_nonneg _)
  by_contra hpos
  have hgt : 0 < alphabetAbscissa (doublyExpAlphabet k₀) := not_le.mp hpos
  let s : ℝ := alphabetAbscissa (doublyExpAlphabet k₀) / 2
  have hs_pos : 0 < s := half_pos hgt
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, (1 / 2 : ℝ) ≤ s * (2 : ℝ) ^ k₁ := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 * s))
    refine ⟨n, ?_⟩
    have h1 : (n : ℝ) ≤ (2 : ℝ) ^ n := by
      have : n ≤ 2 ^ n := le_trans (Nat.le_succ n) (nat_add_one_le_two_pow n)
      exact_mod_cast this
    have h2 : 1 / (2 * s) < (2 : ℝ) ^ n := lt_of_lt_of_le hn h1
    rw [div_lt_iff₀ (by positivity)] at h2
    linarith
  let k₂ := max k₀ k₁
  have hcond : (1 / 2 : ℝ) ≤ s * (2 : ℝ) ^ k₂ := by
    have hpow : (2 : ℝ) ^ k₁ ≤ (2 : ℝ) ^ k₂ :=
      pow_le_pow_right₀ one_le_two (le_max_right k₀ k₁)
    have : s * (2 : ℝ) ^ k₁ ≤ s * (2 : ℝ) ^ k₂ := mul_le_mul_of_nonneg_left hpow hs_pos.le
    linarith
  have hdim_le : dimH (cfAlphabetSet (doublyExpAlphabet k₂)) ≤ ENNReal.ofReal s :=
    dimH_doublyExpAlphabet_le hs_pos hcond
  have hsub_eq : doublyExpAlphabet k₂ = doublyExpAlphabet k₀ ∩ Set.Ici (2 ^ (2 ^ k₂)) := by
    ext a
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨k, le_trans (le_max_left k₀ k₁) hk, rfl⟩, ?_⟩
      exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
    · rintro ⟨⟨k, _, rfl⟩, hge⟩
      have h1 : 2 ^ k₂ ≤ 2 ^ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hge
      have h2 : k₂ ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
      exact ⟨k, h2, rfl⟩
  have habs_eq : alphabetAbscissa (doublyExpAlphabet k₂) =
      alphabetAbscissa (doublyExpAlphabet k₀) := by
    rw [hsub_eq]
    exact alphabetAbscissa_tail_eq _ _
  have hlo := alphabetAbscissa_le_dimH (doublyExpAlphabet_ge_one k₂)
  rw [habs_eq] at hlo
  have hle_enn : ENNReal.ofReal (alphabetAbscissa (doublyExpAlphabet k₀)) ≤ ENNReal.ofReal s :=
    hlo.trans hdim_le
  have hle_real := (ENNReal.ofReal_le_ofReal_iff hs_pos.le).mp hle_enn
  dsimp only [s] at hle_real
  linarith

/-- As the shift `k₀ → ∞`, `dimH (cfAlphabetSet (doublyExpAlphabet k₀)) → 0`. -/
theorem tendsto_dimH_doublyExpAlphabet_zero :
    Tendsto (fun k₀ : ℕ => dimH (cfAlphabetSet (doublyExpAlphabet k₀))) atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨fun a ha => absurd ha (not_lt.mpr zero_le), fun b hb => ?_⟩
  by_cases hb_top : b = ⊤
  · subst hb_top
    filter_upwards [eventually_ge_atTop 1] with k₀ hk₀
    have hle : dimH (cfAlphabetSet (doublyExpAlphabet k₀)) ≤ ENNReal.ofReal (1 / 4) := by
      refine dimH_doublyExpAlphabet_le (by norm_num) ?_
      have h2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ k₀ := pow_le_pow_right₀ one_le_two hk₀
      linarith
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  · have hb_pos : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hb_top
    let s : ℝ := b.toReal / 2
    have hs_pos : 0 < s := half_pos hb_pos
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 * s))
    filter_upwards [eventually_ge_atTop n] with k₀ hk₀
    have hcond : (1 / 2 : ℝ) ≤ s * (2 : ℝ) ^ k₀ := by
      have h1 : (n : ℝ) ≤ (2 : ℝ) ^ k₀ := by
        have : n ≤ 2 ^ k₀ := le_trans (le_trans hk₀ (Nat.le_succ k₀)) (nat_add_one_le_two_pow k₀)
        exact_mod_cast this
      have h2 : 1 / (2 * s) < (2 : ℝ) ^ k₀ := lt_of_lt_of_le hn h1
      rw [div_lt_iff₀ (by positivity)] at h2
      linarith
    have hle := dimH_doublyExpAlphabet_le hs_pos hcond
    have hs_lt : ENNReal.ofReal s < b := by
      rw [← ENNReal.ofReal_toReal hb_top]
      exact (ENNReal.ofReal_lt_ofReal_iff hb_pos).mpr (by dsimp [s]; linarith)
    exact lt_of_le_of_lt hle hs_lt

/-- **Universal Zero Infimum over Infinite Alphabets (Never Attained)**:
    for every `ε > 0`, there is an infinite alphabet `A ⊆ ℕ_≥1` with
    `0 < dimH (cfAlphabetSet A) ≤ ENNReal.ofReal ε`. -/
theorem exists_infinite_alphabet_dimH_le {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set ℕ, A.Infinite ∧ (∀ a ∈ A, 1 ≤ a) ∧
      (0 : ℝ≥0∞) < dimH (cfAlphabetSet A) ∧ dimH (cfAlphabetSet A) ≤ ENNReal.ofReal ε := by
  obtain ⟨k₀, hk₀⟩ := (tendsto_dimH_doublyExpAlphabet_zero.eventually
    (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  exact ⟨doublyExpAlphabet k₀, doublyExpAlphabet_infinite k₀, doublyExpAlphabet_ge_one k₀,
    zero_lt_dimH_doublyExpAlphabet k₀, hk₀.le⟩

end

end GeneralAlphabetFloor
