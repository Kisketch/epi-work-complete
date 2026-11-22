import EpiFormal.ResidueModGeneral
import EpiFormal.WindowThickening

/-!
# Bowen-Free Transfer-Operator Hausdorff Dimension Theorems (`TransferOperatorDim`)

Proves elementary, completely Bowen-free (no topological pressure, no Gibbs/Kolmogorov measure)
Hausdorff dimension upper and lower theorems directly from Gauss-map transfer operators on
continued-fraction alphabet sets `cfAlphabetSet A`, plus concrete kernel-checked bounds and
soundness bridges for finite-grid exact-integer certificates:

1. **Transfer-Operator Upper Theorem (`hausdorffMeasure_le_of_transferOp_le`,
   `dimH_le_of_transferOp_le`)**: If bounded `v : ℝ → [lo, hi]` (`0 < lo ≤ hi < ∞`) satisfies
   `L_s v ≤ v` on `[0, 1]`, then `μH[s] (cfAlphabetSet A) ≤ hi / lo < ∞` and `dimH ≤ s`.
2. **Transfer-Operator Lower Theorem (`hausdorffMeasure_pos_of_transferOp_ge`,
   `le_dimH_of_transferOp_ge`)**: For nonempty finite `A : Finset ℕ` (`∀ a ∈ A, 1 ≤ a`),
   `cfAlphabetSet A` is compact (`isCompact_cfAlphabetSet`), and if `v ≤ L_s v` on `[0, 1]`, a
   finite prefix-free Moran cut + thickening argument proves `0 < μH[s] (cfAlphabetSet A)` and
   `s ≤ dimH (cfAlphabetSet A)`.
3. **Pure-Lean Unconditional Analytic Bounds**:
   - `half_lt_dimH_residueConstSet`: `(1 / 2 : ℝ≥0∞) < dimH F_{m,r}` for every `m ≥ 2, r ≥ 1`.
   - `dimH_residueMod4_le_four_fifths`: `dimH F_{4,1} ≤ 4 / 5` via `v(x) = 1 / (1 + x)` and
     MVT telescoping, combining with `ResidueModGeneral` to yield
     `1 / 2 < dimH F_{4,4} ≤ dimH F_4(r) ≤ dimH F_{4,1} = dimH E_per(4) ≤ 4 / 5`.
4. **Uniform-Grid Step-Vector + Integral-Tail Soundness (`step_cert_upper_sound`,
   `step_cert_lower_sound`)**: Rigorously validates the exact rational transfer-operator
   certificates in `verification/residue_certificate.py` and `residue_certificate_general.py`.
-/

namespace TransferOperatorDim

open Matrix Set Filter Finset ENNReal Metric Real MeasureTheory
open Cylinder WindowCFRealize WindowCFBridge WindowBoundedUpper ResidueModGeneral WindowThickening
open scoped NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Part 1: Alphabet sets, transfer operators, and continuant ratio identities -/

/-- Continued-fraction irrationals in `(0, 1)` whose partial quotients lie in `A`. -/
def cfAlphabetSet (A : Set ℕ) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 | Irrational x ∧ ∀ i, cfDigit x i ∈ A}

lemma cfAlphabetSet_eq_residueConstSet (m r : ℕ) :
    cfAlphabetSet {a : ℕ | r ≤ a ∧ a % m = r % m} = residueConstSet m r := by
  ext x
  simp [cfAlphabetSet, residueConstSet, residueSeqSet]

/-- Transfer operator `(L_s^A v)(x)` evaluated in `ℝ≥0∞`. -/
def transferOp (A : Set ℕ) (s : ℝ) (v : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∑' a : ℕ, if a ∈ A then
    v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))
  else 0

lemma transferOp_mono {A : Set ℕ} {s : ℝ} {v₁ v₂ : ℝ → ℝ≥0∞}
    (hv : ∀ y ∈ Set.Icc (0 : ℝ) 1, v₁ y ≤ v₂ y) (ha1 : ∀ a ∈ A, 1 ≤ a)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    transferOp A s v₁ x ≤ transferOp A s v₂ x := by
  unfold transferOp
  refine ENNReal.tsum_le_tsum fun a => ?_
  split_ifs with ha
  · have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1 a ha
    have hy : 1 / ((a : ℝ) + x) ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg zero_le_one (by linarith [hx.1]), ?_⟩
      exact (div_le_one (by linarith [hx.1])).mpr (by linarith [hx.1])
    exact mul_le_mul_of_nonneg_right (hv _ hy) bot_le
  · exact le_rfl

private lemma transferOp_eq_tsum_subtype (A : Set ℕ) (s : ℝ) (v : ℝ → ℝ≥0∞) (x : ℝ) :
    transferOp A s v x =
      ∑' a : {a : ℕ // a ∈ A},
        v (1 / ((a.1 : ℝ) + x)) * ENNReal.ofReal (((a.1 : ℝ) + x) ^ (-(2 * s))) := by
  unfold transferOp
  refine (tsum_congr fun a => ?_).trans
    (tsum_subtype A fun a : ℕ =>
      v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))).symm
  simp only [Set.indicator_apply]

/-- Real convergent denominator `q_{|w|}` of a CF prefix word `w`. -/
def denQ (w : List ℕ) : ℝ := ((cfProd (0 :: w)) 1 0 : ℝ)

/-- Real penultimate convergent denominator `q_{|w|-1}` of a CF prefix word `w`. -/
def denP (w : List ℕ) : ℝ := ((cfProd (0 :: w)) 1 1 : ℝ)

/-- Real tail ratio `q_{|w|-1} / q_{|w|} ∈ [0, 1]`. -/
def ratioT (w : List ℕ) : ℝ := denP w / denQ w

@[simp]
lemma denQ_nil : denQ [] = 1 := by simp [denQ, cfProd, cfMat]

@[simp]
lemma denP_nil : denP [] = 0 := by simp [denP, cfProd, cfMat]

@[simp]
lemma ratioT_nil : ratioT [] = 0 := by simp [ratioT]

lemma denQ_pos {w : List ℕ} (hw : PosDigits w) : 0 < denQ w := by
  unfold denQ
  cases w with
  | nil => simp [cfProd, cfMat]
  | cons b rest =>
    have hc := cfProd_col0_pos hw (List.cons_ne_nil b rest)
    have hr := cfProd_zero_cons_row1 (b :: rest)
    exact_mod_cast (by linarith [hc.1, hr.1] : (0 : ℤ) < (cfProd (0 :: b :: rest)) 1 0)

lemma denQ_ge_one {w : List ℕ} (hw : PosDigits w) : 1 ≤ denQ w := by
  unfold denQ
  cases w with
  | nil => simp [cfProd, cfMat]
  | cons b rest =>
    have hc := cfProd_col0_pos hw (List.cons_ne_nil b rest)
    have hr := cfProd_zero_cons_row1 (b :: rest)
    exact_mod_cast (by linarith [hc.1, hr.1] : (1 : ℤ) ≤ (cfProd (0 :: b :: rest)) 1 0)

lemma denP_nonneg (w : List ℕ) : 0 ≤ denP w := by
  unfold denP
  exact_mod_cast cfProd_nonneg (0 :: w) 1 1

lemma denP_le_denQ {w : List ℕ} (hw : PosDigits w) : denP w ≤ denQ w := by
  unfold denP denQ
  exact_mod_cast cfProd_zero_cons_col1_le_col0 hw

lemma ratioT_mem_Icc {w : List ℕ} (hw : PosDigits w) :
    ratioT w ∈ Set.Icc (0 : ℝ) 1 := by
  have hq := denQ_pos hw
  exact ⟨div_nonneg (denP_nonneg w) hq.le, (div_le_one hq).mpr (denP_le_denQ hw)⟩

lemma denQ_snoc (w : List ℕ) (a : ℕ) :
    denQ (w ++ [a]) = (a : ℝ) * denQ w + denP w := by
  unfold denQ denP
  have hcons : (0 :: (w ++ [a])) = (0 :: w) ++ [a] := rfl
  rw [hcons, cfProd_append_single, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [cfMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  ring

lemma denP_snoc (w : List ℕ) (a : ℕ) : denP (w ++ [a]) = denQ w := by
  unfold denP denQ
  have hcons : (0 :: (w ++ [a])) = (0 :: w) ++ [a] := rfl
  rw [hcons, cfProd_append_single, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [cfMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero]

lemma denQ_snoc_factor {w : List ℕ} (hw : PosDigits w) (a : ℕ) :
    denQ (w ++ [a]) = denQ w * ((a : ℝ) + ratioT w) := by
  have hq : denQ w ≠ 0 := (denQ_pos hw).ne'
  rw [denQ_snoc, ratioT]
  field_simp

lemma ratioT_snoc {w : List ℕ} (hw : PosDigits w) (a : ℕ) (_ha : 1 ≤ a) :
    ratioT (w ++ [a]) = 1 / ((a : ℝ) + ratioT w) := by
  have hq : denQ w ≠ 0 := (denQ_pos hw).ne'
  calc ratioT (w ++ [a]) = denP (w ++ [a]) / denQ (w ++ [a]) := rfl
    _ = denQ w / (denQ w * ((a : ℝ) + ratioT w)) := by
      rw [denP_snoc, denQ_snoc_factor hw a]
    _ = 1 / ((a : ℝ) + ratioT w) := by rw [div_mul_eq_div_div, div_self hq]

lemma denQ_snoc_le {w : List ℕ} (hw : PosDigits w) {a M : ℕ} (haM : a ≤ M) :
    denQ (w ++ [a]) ≤ ((M : ℝ) + 1) * denQ w := by
  rw [denQ_snoc]
  have hq := (denQ_pos hw).le
  have hp := denP_le_denQ hw
  have haR : (a : ℝ) ≤ (M : ℝ) := by exact_mod_cast haM
  nlinarith

lemma cylPair_len_bounds {w : List ℕ} (hw : PosDigits w) (hne : w ≠ []) :
    1 / (2 * (denQ w) ^ 2) ≤ (cylPair w).2 - (cylPair w).1 ∧
      (cylPair w).2 - (cylPair w).1 ≤ 1 / (denQ w) ^ 2 := by
  rw [cylPair_len hw hne]
  have hq := denQ_pos hw
  have hp0 := denP_nonneg w
  have hpq := denP_le_denQ hw
  change 1 / (2 * (denQ w) ^ 2) ≤ 1 / (denQ w * (denQ w + denP w)) ∧
    1 / (denQ w * (denQ w + denP w)) ≤ 1 / (denQ w) ^ 2
  constructor
  · exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  · exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

lemma cylPair_len_step_ge {w : List ℕ} (hw : PosDigits w) (hne : w ≠ [])
    {a M : ℕ} (ha : 1 ≤ a) (haM : a ≤ M) :
    ((cylPair w).2 - (cylPair w).1) / (2 * ((M : ℝ) + 1) * ((M : ℝ) + 2)) ≤
      (cylPair (w ++ [a])).2 - (cylPair (w ++ [a])).1 := by
  have hw' : PosDigits (w ++ [a]) := posDigits_append.mpr
    ⟨hw, fun d hd => by rw [List.mem_singleton] at hd; rw [hd]; exact ha⟩
  have hne' : w ++ [a] ≠ [] := by simp
  have hb1 := (cylPair_len_bounds hw hne).2
  have hb2 := (cylPair_len_bounds hw' hne').1
  have hq := denQ_pos hw
  have hq_snoc := denQ_snoc_le hw haM
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hq_sq : (denQ (w ++ [a])) ^ 2 ≤ ((M : ℝ) + 1) ^ 2 * (denQ w) ^ 2 := by
    have hq_nn : 0 ≤ denQ (w ++ [a]) := (denQ_pos hw').le
    nlinarith
  have hM_le : ((M : ℝ) + 1) ^ 2 ≤ ((M : ℝ) + 1) * ((M : ℝ) + 2) := by
    have : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    nlinarith
  have hcomb : 2 * (denQ (w ++ [a])) ^ 2 ≤
      (2 * ((M : ℝ) + 1) * ((M : ℝ) + 2)) * (denQ w) ^ 2 := by
    have hq2 : 0 ≤ (denQ w) ^ 2 := by positivity
    nlinarith
  calc ((cylPair w).2 - (cylPair w).1) / (2 * ((M : ℝ) + 1) * ((M : ℝ) + 2))
      ≤ (1 / (denQ w) ^ 2) / (2 * ((M : ℝ) + 1) * ((M : ℝ) + 2)) :=
        div_le_div_of_nonneg_right hb1 (by positivity)
    _ = 1 / ((2 * ((M : ℝ) + 1) * ((M : ℝ) + 2)) * (denQ w) ^ 2) := by
        rw [div_div, mul_comm (denQ w ^ 2)]
    _ ≤ 1 / (2 * (denQ (w ++ [a])) ^ 2) :=
        one_div_le_one_div_of_le (by have := denQ_pos hw'; positivity) hcomb
    _ ≤ (cylPair (w ++ [a])).2 - (cylPair (w ++ [a])).1 := hb2

/-! ### Part 2: Finite-word prefix trees & Bowen-free Upper Theorem -/

/-- Word in `List ℕ` encoded from `Fin n → {a // a ∈ A}`. -/
def subWord {A : Set ℕ} : ∀ n : ℕ, (Fin n → {a : ℕ // a ∈ A}) → List ℕ
  | n, w => List.ofFn (fun i : Fin n => (w i).1)

@[simp]
lemma subWord_length {A : Set ℕ} (n : ℕ) (w : Fin n → {a : ℕ // a ∈ A}) :
    (subWord n w).length = n := by
  simp [subWord]

lemma posDigits_subWord {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a)
    (n : ℕ) (w : Fin n → {a : ℕ // a ∈ A}) : PosDigits (subWord n w) := by
  intro d hd
  rw [subWord, List.mem_ofFn] at hd
  obtain ⟨i, rfl⟩ := hd
  exact ha1 (w i).1 (w i).2

lemma subWord_snoc {A : Set ℕ} {n : ℕ} (u : Fin n → {a : ℕ // a ∈ A})
    (a : {a : ℕ // a ∈ A}) :
    subWord (n + 1) (Fin.snoc u a) = subWord n u ++ [a.1] := by
  refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
  simp only [subWord, List.getElem_ofFn, List.getElem_append, List.length_ofFn]
  split_ifs with h
  · simp [Fin.snoc, h]
  · have hi_eq : i = n := by rw [subWord_length] at hi1; omega
    subst hi_eq
    simp [Fin.snoc]

private def finSnocEquiv {α : Type*} (n : ℕ) : (Fin (n + 1) → α) ≃ (Fin n → α) × α where
  toFun w := (Fin.init w, w (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv w := by
    ext ⟨i, hi⟩
    by_cases h : i < n
    · simp [Fin.snoc, Fin.init, h]
    · have hin : i = n := by omega
      subst hin
      simp [Fin.snoc, Fin.last]
  right_inv p := by
    ext i
    · simp [Fin.init, Fin.snoc]
    · simp [Fin.snoc]

/-- Node weight `v(ratioT w) * denQ(w)^{-2s}` along a CF word. -/
def nodeWeight (s : ℝ) (v : ℝ → ℝ≥0∞) (w : List ℕ) : ℝ≥0∞ :=
  v (ratioT w) * ENNReal.ofReal ((denQ w) ^ (-(2 * s)))

lemma nodeWeight_snoc {s : ℝ} {w : List ℕ} (hw : PosDigits w) {a : ℕ} (ha : 1 ≤ a)
    (v : ℝ → ℝ≥0∞) :
    nodeWeight s v (w ++ [a]) =
      (v (1 / ((a : ℝ) + ratioT w)) * ENNReal.ofReal (((a : ℝ) + ratioT w) ^ (-(2 * s)))) *
        ENNReal.ofReal ((denQ w) ^ (-(2 * s))) := by
  unfold nodeWeight
  have hq : 0 < denQ w := denQ_pos hw
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hax : 0 < (a : ℝ) + ratioT w := by linarith [(ratioT_mem_Icc hw).1]
  rw [ratioT_snoc hw a ha, denQ_snoc_factor hw a, Real.mul_rpow hq.le hax.le,
    ENNReal.ofReal_mul (Real.rpow_nonneg hq.le _)]
  ring

lemma tsum_nodeWeight_step {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a) {s : ℝ} (v : ℝ → ℝ≥0∞)
    (n : ℕ) :
    (∑' w : Fin (n + 1) → {a : ℕ // a ∈ A}, nodeWeight s v (subWord (n + 1) w)) =
      ∑' u : Fin n → {a : ℕ // a ∈ A},
        transferOp A s v (ratioT (subWord n u)) *
          ENNReal.ofReal ((denQ (subWord n u)) ^ (-(2 * s))) := by
  rw [← Equiv.tsum_eq (finSnocEquiv n).symm
    (fun w => nodeWeight s v (subWord (n + 1) w))]
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun u => ?_
  have hpd := posDigits_subWord ha1 n u
  have hstep : ∀ a : {a : ℕ // a ∈ A},
      nodeWeight s v (subWord (n + 1) ((finSnocEquiv n).symm (u, a))) =
        (v (1 / ((a.1 : ℝ) + ratioT (subWord n u))) *
          ENNReal.ofReal (((a.1 : ℝ) + ratioT (subWord n u)) ^ (-(2 * s)))) *
            ENNReal.ofReal ((denQ (subWord n u)) ^ (-(2 * s))) := fun a => by
    change nodeWeight s v (subWord (n + 1) (Fin.snoc u a)) = _
    rw [subWord_snoc, nodeWeight_snoc hpd (ha1 a.1 a.2)]
  simp only [hstep, ENNReal.tsum_mul_right]
  congr 1
  let f : ℕ → ℝ≥0∞ := fun a =>
    v (1 / ((a : ℝ) + ratioT (subWord n u))) *
      ENNReal.ofReal (((a : ℝ) + ratioT (subWord n u)) ^ (-(2 * s)))
  have hsub : (∑' a : {a : ℕ // a ∈ A}, f a.1) = ∑' a : ℕ, A.indicator f a :=
    tsum_subtype A f
  rw [hsub]
  refine tsum_congr fun a => ?_
  simp [Set.indicator_apply, f]

/-- **Bowen-Free Transfer-Operator Upper Theorem (`μH[s] ≤ hi / lo`)**. -/
theorem hausdorffMeasure_le_of_transferOp_le {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a)
    {s : ℝ} (hs : 0 < s) {v : ℝ → ℝ≥0∞} {lo hi : ℝ≥0∞}
    (hlo : 0 < lo) (hhi : hi < ⊤)
    (hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1, lo ≤ v x ∧ v x ≤ hi)
    (hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1, transferOp A s v x ≤ v x) :
    μH[s] (cfAlphabetSet A) ≤ hi / lo := by
  have hsum_step : ∀ n : ℕ,
      (∑' w : Fin n → {a : ℕ // a ∈ A}, nodeWeight s v (subWord n w)) ≤ v 0 := by
    intro n
    induction n with
    | zero =>
      have hsub0 : subWord (A := A) 0 (fun i : Fin 0 => i.elim0) = [] := rfl
      rw [tsum_eq_single (fun i : Fin 0 => (i.elim0 : {a : ℕ // a ∈ A}))
        (fun w hw => absurd (funext fun i => i.elim0) hw), hsub0]
      simp [nodeWeight]
    | succ n ih =>
      rw [tsum_nodeWeight_step ha1 v n]
      have hpt : ∀ u : Fin n → {a : ℕ // a ∈ A},
          transferOp A s v (ratioT (subWord n u)) *
            ENNReal.ofReal ((denQ (subWord n u)) ^ (-(2 * s))) ≤
          nodeWeight s v (subWord n u) := fun u => by
        exact mul_le_mul_of_nonneg_right
          (hsub _ (ratioT_mem_Icc (posDigits_subWord ha1 n u))) bot_le
      exact le_trans (ENNReal.tsum_le_tsum hpt) ih
  have hr_lim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) ^ (-(2 : ℝ))))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun x : ℝ => x ^ (-(2 : ℝ))) Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    simpa using ENNReal.tendsto_ofReal (h0.comp tendsto_natCast_atTop_atTop)
  let cov : ∀ n : ℕ, (Fin n → {a : ℕ // a ∈ A}) → Set ℝ := fun n w =>
    Set.Icc (cylPair (subWord n w)).1 (cylPair (subWord n w)).2
  have hcov : ∀ᶠ n : ℕ in Filter.atTop,
      cfAlphabetSet A ⊆ ⋃ w : Fin n → {a : ℕ // a ∈ A}, cov n w := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn x hx => ?_⟩
    rcases hx with ⟨⟨hx0, hx1⟩, hirr, hadm⟩
    let w : Fin n → {a : ℕ // a ∈ A} := fun i => ⟨cfDigit x i, hadm i⟩
    refine Set.mem_iUnion.mpr ⟨w, ?_⟩
    have hpref : subWord n w = cfPrefixList (cfDigit x) n := rfl
    have hne : subWord n w ≠ [] := by
      intro h; have := subWord_length n w; rw [h] at this
      simp only [List.length_nil] at this; omega
    have hmob := eq_mobius_cfPrefix_cfTail hx0 hx1 hirr n
    have ht := cfTail_mem_Ioo hx0 hx1 hirr n
    rw [← hpref] at hmob
    rw [hmob]
    exact mobius_mem_cylPair (posDigits_subWord ha1 n w) hne ht.1.le ht.2.le
  have hdiam : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ w : Fin n → {a : ℕ // a ∈ A},
        Metric.ediam (cov n w) ≤ ENNReal.ofReal ((n : ℝ) ^ (-(2 : ℝ))) := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn w => ?_⟩
    have hpd := posDigits_subWord ha1 n w
    have hne : subWord n w ≠ [] := by
      intro h; have := subWord_length n w; rw [h] at this
      simp only [List.length_nil] at this; omega
    have hd1 := ediam_cylPair_le hpd hne
    have hden := (cfProd_zero_cons_den_ge hpd).1
    have hq_ge : (n : ℝ) ≤ denQ (subWord n w) := by
      unfold denQ
      exact_mod_cast (subWord_length n w) ▸ hden
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hrpow : (denQ (subWord n w)) ^ (-(2 : ℝ)) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hn_pos hq_ge (by norm_num)
    exact le_trans hd1 (ENNReal.ofReal_le_ofReal hrpow)
  have hmain := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum s (cfAlphabetSet A)
    (fun n : ℕ => ENNReal.ofReal ((n : ℝ) ^ (-(2 : ℝ)))) hr_lim cov hdiam hcov
  have hcost : ∀ n : ℕ, 1 ≤ n →
      (∑' w : Fin n → {a : ℕ // a ∈ A}, Metric.ediam (cov n w) ^ s) ≤ hi / lo := by
    intro n hn
    have hper : ∀ w : Fin n → {a : ℕ // a ∈ A},
        Metric.ediam (cov n w) ^ s ≤ lo⁻¹ * nodeWeight s v (subWord n w) := by
      intro w
      have hpd := posDigits_subWord ha1 n w
      have hne : subWord n w ≠ [] := by
        intro h; have := subWord_length n w; rw [h] at this
        simp only [List.length_nil] at this; omega
      have hq_pos := denQ_pos hpd
      have h1 : Metric.ediam (cov n w) ^ s ≤
          (ENNReal.ofReal ((denQ (subWord n w)) ^ (-(2 : ℝ)))) ^ s :=
        ENNReal.rpow_le_rpow (ediam_cylPair_le hpd hne) hs.le
      have h2 : (ENNReal.ofReal ((denQ (subWord n w)) ^ (-(2 : ℝ)))) ^ s =
          ENNReal.ofReal ((denQ (subWord n w)) ^ (-(2 * s))) := by
        rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hq_pos _),
          ← Real.rpow_mul hq_pos.le]
        congr 1; ring
      have hv_lo : lo ≤ v (ratioT (subWord n w)) :=
        (hv_bd _ (ratioT_mem_Icc hpd)).1
      have hlo_ne_top : lo ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (hv_bd 0 (by simp)).1
        (lt_of_le_of_lt (hv_bd 0 (by simp)).2 hhi))
      have h3 : (1 : ℝ≥0∞) ≤ lo⁻¹ * v (ratioT (subWord n w)) := by
        rw [← ENNReal.mul_inv_cancel hlo.ne' hlo_ne_top, mul_comm lo lo⁻¹]
        exact mul_le_mul_of_nonneg_left hv_lo bot_le
      calc Metric.ediam (cov n w) ^ s
          ≤ ENNReal.ofReal ((denQ (subWord n w)) ^ (-(2 * s))) := h1.trans_eq h2
        _ = 1 * ENNReal.ofReal ((denQ (subWord n w)) ^ (-(2 * s))) := (one_mul _).symm
        _ ≤ (lo⁻¹ * v (ratioT (subWord n w))) *
              ENNReal.ofReal ((denQ (subWord n w)) ^ (-(2 * s))) :=
            mul_le_mul_of_nonneg_right h3 bot_le
        _ = lo⁻¹ * nodeWeight s v (subWord n w) := by
            unfold nodeWeight; ring
    have hhi_v0 : v 0 ≤ hi := (hv_bd 0 ⟨le_rfl, zero_le_one⟩).2
    calc (∑' w : Fin n → {a : ℕ // a ∈ A}, Metric.ediam (cov n w) ^ s)
        ≤ ∑' w : Fin n → {a : ℕ // a ∈ A}, lo⁻¹ * nodeWeight s v (subWord n w) :=
          ENNReal.tsum_le_tsum hper
      _ = lo⁻¹ * ∑' w : Fin n → {a : ℕ // a ∈ A}, nodeWeight s v (subWord n w) :=
          ENNReal.tsum_mul_left
      _ ≤ lo⁻¹ * v 0 := mul_le_mul_of_nonneg_left (hsum_step n) bot_le
      _ ≤ lo⁻¹ * hi := mul_le_mul_of_nonneg_left hhi_v0 bot_le
      _ = hi / lo := by rw [div_eq_mul_inv, mul_comm]
  have hlim_le : Filter.liminf
      (fun n : ℕ => ∑' w : Fin n → {a : ℕ // a ∈ A}, Metric.ediam (cov n w) ^ s)
      Filter.atTop ≤ hi / lo :=
    Filter.liminf_le_of_frequently_le
      ((Filter.eventually_atTop.mpr ⟨1, hcost⟩).frequently)
  exact hmain.trans hlim_le

/-- **Dimension Upper Bound Corollary (`dimH (cfAlphabetSet A) ≤ s`)**. -/
theorem dimH_le_of_transferOp_le {A : Set ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a)
    {s : ℝ} (hs : 0 < s) {v : ℝ → ℝ≥0∞} {lo hi : ℝ≥0∞}
    (hlo : 0 < lo) (hhi : hi < ⊤)
    (hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1, lo ≤ v x ∧ v x ≤ hi)
    (hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1, transferOp A s v x ≤ v x) :
    dimH (cfAlphabetSet A) ≤ ENNReal.ofReal s := by
  let d : ℝ≥0 := ⟨s, hs.le⟩
  have hmeas : μH[(d : ℝ)] (cfAlphabetSet A) ≠ ∞ := by
    have h1 := hausdorffMeasure_le_of_transferOp_le ha1 hs hlo hhi hv_bd hsub
    have hfin : hi / lo < ∞ := by
      rw [div_eq_mul_inv]
      exact ENNReal.mul_lt_top hhi (ENNReal.inv_lt_top.mpr hlo)
    exact ne_of_lt (lt_of_le_of_lt h1 hfin)
  have hdim := dimH_le_of_hausdorffMeasure_ne_top hmeas
  rw [← ENNReal.ofReal_coe_nnreal] at hdim
  exact hdim

/-! ### Part 3: Compact sub-cylinder geometry & Bowen-free Lower Theorem -/

/-- Closed sub-cylinder lying strictly inside `(cylPair w).1 < ... < (cylPair w).2`. -/
def subCyl (M : ℕ) (w : List ℕ) : Set ℝ :=
  mobius (cfProd (0 :: w)) ''
    Set.Icc (1 / ((M : ℝ) + 1)) (((M : ℝ) + 1) / ((M : ℝ) + 2))

lemma subCyl_compact (M : ℕ) {w : List ℕ} (hw : PosDigits w) : IsCompact (subCyl M w) := by
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hM2 : (0 : ℝ) < (M : ℝ) + 2 := by positivity
  have hq : (0 : ℝ) < denQ w := denQ_pos hw
  have hp : 0 ≤ denP w := denP_nonneg w
  have hcont : ContinuousOn (mobius (cfProd (0 :: w)))
      (Set.Icc (1 / ((M : ℝ) + 1)) (((M : ℝ) + 1) / ((M : ℝ) + 2))) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
    change denQ w + denP w * t ≠ 0
    linarith [mul_nonneg hp ht0.le]
  exact isCompact_Icc.image_of_continuousOn hcont

lemma subCyl_subset_Ioo_cylPair {M : ℕ} (hM : 1 ≤ M) {w : List ℕ}
    (hw : PosDigits w) (hne : w ≠ []) :
    subCyl M w ⊆ Set.Ioo (cylPair w).1 (cylPair w).2 := by
  rintro _ ⟨t, ht, rfl⟩
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  have ht1 : t < 1 := lt_of_le_of_lt ht.2 (by
    rw [div_lt_one (by positivity : (0 : ℝ) < (M : ℝ) + 2)]
    linarith)
  exact mobius_mem_Ioo_cylPair hw hne ht0 ht1

lemma cfAlphabetSet_eq_compact_iInter (A : Finset ℕ) (hAne : A.Nonempty)
    (ha1 : ∀ a ∈ A, 1 ≤ a) :
    let M := A.sup id
    cfAlphabetSet (A : Set ℕ) =
      ⋂ n : ℕ, ⋃ w : Fin (n + 1) → {a : ℕ // a ∈ A},
        subCyl M (subWord (n + 1) w) := by
  intro M
  have hM1 : 1 ≤ M := by
    obtain ⟨a₀, ha₀⟩ := hAne
    exact le_trans (ha1 a₀ ha₀) (Finset.le_sup (f := id) ha₀)
  ext x
  constructor
  · rintro ⟨⟨hx0, hx1⟩, hirr, hadm⟩
    rw [Set.mem_iInter]
    intro n
    let w : Fin (n + 1) → {a : ℕ // a ∈ A} := fun i => ⟨cfDigit x i, hadm i⟩
    refine Set.mem_iUnion.mpr ⟨w, cfTail x (n + 1), ?_, ?_⟩
    · have hrec1 := cfTail_recurrence hx0 hx1 hirr (n + 1)
      have hrec2 := cfTail_recurrence hx0 hx1 hirr (n + 2)
      have ht1 := cfTail_mem_Ioo hx0 hx1 hirr (n + 1)
      have ht2 := cfTail_mem_Ioo hx0 hx1 hirr (n + 2)
      have ht3 := cfTail_mem_Ioo hx0 hx1 hirr (n + 3)
      have ha_le1 : cfDigit x (n + 1) ≤ M := Finset.le_sup (f := id) (hadm (n + 1))
      have ha_le2 : cfDigit x (n + 2) ≤ M := Finset.le_sup (f := id) (hadm (n + 2))
      have ha_ge1 := cfDigit_ge_one hx0 hx1 hirr (n + 1)
      have ha_le1R : (cfDigit x (n + 1) : ℝ) ≤ (M : ℝ) := by exact_mod_cast ha_le1
      have ha_le2R : (cfDigit x (n + 2) : ℝ) ≤ (M : ℝ) := by exact_mod_cast ha_le2
      have ha_ge1R : (1 : ℝ) ≤ (cfDigit x (n + 1) : ℝ) := by exact_mod_cast ha_ge1
      have hlo2 : 1 / ((M : ℝ) + 1) ≤ cfTail x (n + 2) := by
        rw [hrec2]
        exact one_div_le_one_div_of_le (by linarith [ht3.1]) (by linarith [ht3.2])
      have hlo1 : 1 / ((M : ℝ) + 1) ≤ cfTail x (n + 1) := by
        rw [hrec1]
        exact one_div_le_one_div_of_le (by linarith [ht2.1]) (by linarith [ht2.2])
      have hhi1 : cfTail x (n + 1) ≤ ((M : ℝ) + 1) / ((M : ℝ) + 2) := by
        rw [hrec1]
        have hden : 1 + 1 / ((M : ℝ) + 1) ≤ (cfDigit x (n + 1) : ℝ) + cfTail x (n + 2) := by
          linarith
        have h1 : 1 / ((cfDigit x (n + 1) : ℝ) + cfTail x (n + 2)) ≤
            1 / (1 + 1 / ((M : ℝ) + 1)) :=
          one_div_le_one_div_of_le (by positivity) hden
        have h2 : 1 / (1 + 1 / ((M : ℝ) + 1)) = ((M : ℝ) + 1) / ((M : ℝ) + 2) := by
          have hM0 : (M : ℝ) + 1 ≠ 0 := by positivity
          field_simp; ring
        linarith
      exact ⟨hlo1, hhi1⟩
    · have hpw : subWord (n + 1) w = cfPrefixList (cfDigit x) (n + 1) := rfl
      rw [hpw]
      exact (eq_mobius_cfPrefix_cfTail hx0 hx1 hirr (n + 1)).symm
  · intro hx
    rw [Set.mem_iInter] at hx
    have huniq : ∀ n : ℕ, ∃ w : Fin (n + 1) → {a : ℕ // a ∈ A},
        x ∈ subCyl M (subWord (n + 1) w) := fun n => Set.mem_iUnion.mp (hx n)
    choose w hw using huniq
    have hw_Ioo : ∀ n : ℕ,
        x ∈ Set.Ioo (cylPair (subWord (n + 1) (w n))).1
          (cylPair (subWord (n + 1) (w n))).2 := fun n =>
      subCyl_subset_Ioo_cylPair hM1 (posDigits_subWord (fun a ha => ha1 a ha) (n + 1) (w n))
        (by intro h; have := subWord_length (n + 1) (w n); rw [h] at this; simp at this)
        (hw n)
    have hinit : ∀ n : ℕ, Fin.init (w (n + 1)) = w n := by
      intro n
      have hne_w : subWord (n + 1) (w n) ≠ [] := by
        intro h; have := subWord_length (n + 1) (w n); rw [h] at this; simp at this
      have hsub := hw_Ioo (n + 1)
      have hcons : subWord (n + 2) (w (n + 1)) =
          subWord (n + 1) (Fin.init (w (n + 1))) ++ [(w (n + 1) (Fin.last (n + 1))).1] := by
        have hid : w (n + 1) = Fin.snoc (Fin.init (w (n + 1))) (w (n + 1) (Fin.last (n + 1))) :=
          ((finSnocEquiv (n + 1)).left_inv (w (n + 1))).symm
        conv_lhs => rw [hid]
        exact subWord_snoc (Fin.init (w (n + 1))) _
      have hnest := cylPair_nest
        (posDigits_subWord (fun a ha => ha1 a ha) (n + 1) (Fin.init (w (n + 1))))
        (by
          intro h
          have := subWord_length (n + 1) (Fin.init (w (n + 1)))
          rw [h] at this; simp at this)
        (u := [(w (n + 1) (Fin.last (n + 1))).1])
        (fun d hd => by
          rw [List.mem_singleton] at hd; rw [hd]
          exact ha1 _ (w (n + 1) (Fin.last (n + 1))).2)
      rw [← hcons] at hnest
      have hx_init := hnest (Set.Ioo_subset_Icc_self hsub)
      have hx_wn := hw_Ioo n
      by_contra hne_init
      have hneq_list : subWord (n + 1) (Fin.init (w (n + 1))) ≠ subWord (n + 1) (w n) := by
        intro heq
        apply hne_init
        ext i
        have hi := congrArg (fun l : List ℕ => l[i.1]?) heq
        simp only [subWord, List.getElem?_ofFn, i.2, ↓reduceDIte, Option.some.injEq] at hi
        exact hi
      have hdisj := cylPair_disj_of_incomparable
        (posDigits_subWord (fun a ha => ha1 a ha) (n + 1) (Fin.init (w (n + 1))))
        (posDigits_subWord (fun a ha => ha1 a ha) (n + 1) (w n))
        (fun hpref => hneq_list (List.IsPrefix.eq_of_length hpref (by simp)))
        (fun hpref => hneq_list (List.IsPrefix.eq_of_length hpref (by simp)).symm)
      have hlt_len : (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).1 <
          (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).2 := by
        have hl := cylPair_len
          (posDigits_subWord (fun a ha => ha1 a ha) (n + 1) (Fin.init (w (n + 1))))
          (by
            intro h
            have := subWord_length (n + 1) (Fin.init (w (n + 1)))
            rw [h] at this
            simp at this)
        have hq := denQ_pos (posDigits_subWord (fun a ha => ha1 a ha) (n + 1)
          (Fin.init (w (n + 1))))
        have hp := denP_nonneg (subWord (n + 1) (Fin.init (w (n + 1))))
        have : 0 < (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).2 -
            (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).1 := by
          rw [hl]; change 0 < 1 / (denQ _ * (denQ _ + denP _)); positivity
        linarith
      by_cases hx_gt : (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).1 < x
      · by_cases hx_lt : x < (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).2
        · exact (Set.disjoint_left.mp hdisj ⟨hx_gt, hx_lt⟩) hx_wn
        · have hx_b2 : x = (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).2 :=
            le_antisymm hx_init.2 (not_lt.mp hx_lt)
          let y : ℝ := (max (cylPair (subWord (n + 1) (w n))).1
            (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).1 + x) / 2
          have hy_def : y = (max (cylPair (subWord (n + 1) (w n))).1
              (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).1 + x) / 2 := rfl
          have hma : max (cylPair (subWord (n + 1) (w n))).1
              (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).1 < x := max_lt hx_wn.1 hx_gt
          have hy_lt : y < x := by rw [hy_def]; linarith
          have hy_gt_m : max (cylPair (subWord (n + 1) (w n))).1
              (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).1 < y := by rw [hy_def]; linarith
          have hy_init : y ∈ Set.Ioo
              (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).1
              (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).2 :=
            ⟨lt_of_le_of_lt (le_max_right _ _) hy_gt_m, hx_b2 ▸ hy_lt⟩
          have hy_wn : y ∈ Set.Ioo
              (cylPair (subWord (n + 1) (w n))).1 (cylPair (subWord (n + 1) (w n))).2 :=
            ⟨lt_of_le_of_lt (le_max_left _ _) hy_gt_m, lt_trans hy_lt hx_wn.2⟩
          exact (Set.disjoint_left.mp hdisj hy_init) hy_wn
      · have hx_eq : x = (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).1 :=
          le_antisymm (not_lt.mp hx_gt) hx_init.1
        let y : ℝ := (x + min (cylPair (subWord (n + 1) (w n))).2
          (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).2) / 2
        have hy_def : y = (x + min (cylPair (subWord (n + 1) (w n))).2
            (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).2) / 2 := rfl
        have hxb : x < min (cylPair (subWord (n + 1) (w n))).2
            (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).2 :=
          lt_min hx_wn.2 (hx_eq ▸ hlt_len)
        have hy_gt : x < y := by rw [hy_def]; linarith
        have hy_lt_m : y < min (cylPair (subWord (n + 1) (w n))).2
            (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).2 := by rw [hy_def]; linarith
        have hy_init : y ∈ Set.Ioo
            (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).1
            (cylPair (subWord (n + 1) (Fin.init (w (n + 1))))).2 :=
          ⟨hx_eq ▸ hy_gt, lt_of_lt_of_le hy_lt_m (min_le_right _ _)⟩
        have hy_wn : y ∈ Set.Ioo
            (cylPair (subWord (n + 1) (w n))).1 (cylPair (subWord (n + 1) (w n))).2 :=
          ⟨lt_trans hx_wn.1 hy_gt, lt_of_lt_of_le hy_lt_m (min_le_left _ _)⟩
        exact (Set.disjoint_left.mp hdisj hy_init) hy_wn
    have hunit : x ∈ Set.Ioo (0 : ℝ) 1 :=
      Ioo_cylPair_subset_Ioo_unit (posDigits_subWord (fun a ha => ha1 a ha) 1 (w 0))
        (by intro h; have := subWord_length 1 (w 0); rw [h] at this; simp at this) (hw_Ioo 0)
    have hirr : Irrational x := by
      intro ⟨q, hq⟩
      obtain ⟨N, hN⟩ := (GenContFract.terminates_iff_rat x).mpr ⟨q, hq.symm⟩
      have hpd := posDigits_subWord (fun a ha => ha1 a ha) (N + 1) (w N)
      have hne : subWord (N + 1) (w N) ≠ [] := by
        intro h; have := subWord_length (N + 1) (w N); rw [h] at this; simp at this
      obtain ⟨t, ht, hmob⟩ := exists_mobius_of_mem_Ioo_cylPair hpd hne (hw_Ioo N)
      have hnot := not_terminatedAt_mobius hpd ht.1 ht.2 (k := N) (by rw [subWord_length]; omega)
      rw [hmob] at hnot
      exact hnot hN
    refine ⟨hunit, hirr, fun i => ?_⟩
    have hpd := posDigits_subWord (fun a ha => ha1 a ha) (i + 1) (w i)
    have hne : subWord (i + 1) (w i) ≠ [] := by
      intro h; have := subWord_length (i + 1) (w i); rw [h] at this; simp at this
    obtain ⟨t, ht, hmob⟩ := exists_mobius_of_mem_Ioo_cylPair hpd hne (hw_Ioo i)
    have hsm := stream_mobius_spec (subWord (i + 1) (w i)) hpd ht.1 ht.2
    rw [hmob] at hsm
    have hget := hsm.2.1 i (by rw [subWord_length]; omega)
    simp only [subWord, List.getElem_ofFn] at hget
    have hdig : cfDigit x i = (w i ⟨i, by omega⟩).1 := by simp [cfDigit, hget]
    rw [hdig]
    exact (w i ⟨i, by omega⟩).2

lemma isCompact_cfAlphabetSet (A : Finset ℕ) (hAne : A.Nonempty) (ha1 : ∀ a ∈ A, 1 ≤ a) :
    IsCompact (cfAlphabetSet (A : Set ℕ)) := by
  rw [cfAlphabetSet_eq_compact_iInter A hAne ha1]
  let L : ℕ → Set ℝ := fun n =>
    ⋃ w : Fin (n + 1) → {a : ℕ // a ∈ A}, subCyl (A.sup id) (subWord (n + 1) w)
  have hcomp0 : IsCompact (L 0) :=
    isCompact_iUnion fun w => subCyl_compact (A.sup id)
      (posDigits_subWord (fun a ha => ha1 a ha) 1 w)
  have hclosed : ∀ n, IsClosed (L n) := fun n =>
    (isCompact_iUnion fun w => subCyl_compact (A.sup id)
      (posDigits_subWord (fun a ha => ha1 a ha) (n + 1) w)).isClosed
  exact IsCompact.of_isClosed_subset hcomp0 (isClosed_iInter hclosed) (Set.iInter_subset L 0)

lemma cfAlphabetSet_nonempty_cyl (A : Finset ℕ) (hAne : A.Nonempty) (ha1 : ∀ a ∈ A, 1 ≤ a)
    {n : ℕ} (w : Fin n → {a : ℕ // a ∈ A}) :
    (cfAlphabetSet (A : Set ℕ) ∩
      Set.Icc (cylPair (subWord n w)).1 (cylPair (subWord n w)).2).Nonempty ∨ n = 0 := by
  by_cases hn : n = 0
  · exact Or.inr hn
  refine Or.inl ?_
  obtain ⟨a₀, ha₀⟩ := hAne
  let seq : ℕ → ℕ := fun i => if h : i < n then (w ⟨i, h⟩).1 else a₀
  have hseq1 : ∀ i, 1 ≤ seq i := fun i => by
    dsimp only [seq]
    split_ifs with h
    · exact ha1 _ (w ⟨i, h⟩).2
    · exact ha1 a₀ ha₀
  obtain ⟨hx01, hxirr, hxdig⟩ := cfVal_spec hseq1
  have hx_mem : cfVal seq ∈ cfAlphabetSet (A : Set ℕ) := by
    refine ⟨hx01, hxirr, fun i => ?_⟩
    rw [hxdig i]
    dsimp only [seq]
    split_ifs with h
    · exact (w ⟨i, h⟩).2
    · exact ha₀
  have hpref_eq : cfPrefixList seq n = subWord n w := by
    refine List.ext_getElem (by simp [cfPrefixList_length, subWord_length]) fun i hi _ => ?_
    rw [cfPrefixList_length] at hi
    simp [cfPrefixList, subWord, seq]
  have hx_cyl := cfVal_mem_cylPair_Ioo hseq1 (show 1 ≤ n by omega)
  rw [hpref_eq] at hx_cyl
  exact ⟨cfVal seq, hx_mem, Set.Ioo_subset_Icc_self hx_cyl⟩

private def prefixFin {α : Type*} {n m : ℕ} (h : m ≤ n) (w : Fin n → α) : Fin m → α :=
  fun i => w ⟨i.1, lt_of_lt_of_le i.2 h⟩

lemma subWord_isPrefix_iff_prefixFin {A : Set ℕ} {m₁ m₂ : ℕ}
    (w₁ : Fin m₁ → {a : ℕ // a ∈ A}) (w₂ : Fin m₂ → {a : ℕ // a ∈ A}) :
    (subWord m₁ w₁ <+: subWord m₂ w₂) ↔
      ∃ h : m₁ ≤ m₂, w₁ = prefixFin h w₂ := by
  constructor
  · rintro ⟨t, ht⟩
    have hlen : m₁ ≤ m₂ := by
      have h1 := congrArg List.length ht
      rw [List.length_append, subWord_length, subWord_length] at h1
      omega
    refine ⟨hlen, funext fun ⟨i, hi⟩ => ?_⟩
    have hget := congrArg (fun l : List ℕ => l[i]?) ht
    have hi1 : i < (subWord m₁ w₁).length := by rw [subWord_length]; exact hi
    have hi2 : i < (subWord m₂ w₂).length := by rw [subWord_length]; exact lt_of_lt_of_le hi hlen
    rw [List.getElem?_append_left hi1, List.getElem?_eq_getElem hi1,
      List.getElem?_eq_getElem hi2] at hget
    simp only [subWord, List.getElem_ofFn, Option.some.injEq] at hget
    exact Subtype.ext hget
  · rintro ⟨h, rfl⟩
    refine ⟨List.ofFn (fun i : Fin (m₂ - m₁) => (w₂ ⟨m₁ + i.1, by omega⟩).1), ?_⟩
    refine List.ext_getElem (by simp; omega) fun i hi1 hi2 => ?_
    simp only [subWord, List.getElem_append, List.length_ofFn] at hi2 ⊢
    split_ifs with hlt
    · simp [prefixFin]
    · simp only [List.getElem_ofFn, Nat.add_sub_cancel' (not_lt.mp hlt)]

private theorem tree_prefixCut_weight_le {A : Finset ℕ} (ha1 : ∀ a ∈ A, 1 ≤ a)
    {s : ℝ} {v : ℝ → ℝ≥0∞}
    (hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1, v x ≤ transferOp (A : Set ℕ) s v x)
    (N : ℕ) (Cut : Finset (Σ m : Fin (N + 1), Fin m.1 → {a : ℕ // a ∈ A}))
    (hmin : ∀ c ∈ Cut, 1 ≤ c.1.1 ∧
      ∀ c' ∈ Cut, (subWord c'.1.1 c'.2 <+: subWord c.1.1 c.2) → c' = c)
    (hcov : ∀ u : Fin N → {a : ℕ // a ∈ A}, ∃ c ∈ Cut, subWord c.1.1 c.2 <+: subWord N u) :
    v 0 ≤ ∑ c ∈ Cut, nodeWeight s v (subWord c.1.1 c.2) := by
  classical
  have step_node : ∀ (m : ℕ) (hm : m ≤ N) (w : Fin m → {a : ℕ // a ∈ A}),
      nodeWeight s v (subWord m w) ≤
        ∑ a : {a : ℕ // a ∈ A}, nodeWeight s v (subWord (m + 1) (Fin.snoc w a)) := by
    intro m _ w
    have hpd := posDigits_subWord (fun a ha => ha1 a ha) m w
    have hvt := hsuper (ratioT (subWord m w)) (ratioT_mem_Icc hpd)
    have hmul := mul_le_mul_of_nonneg_right hvt
      (bot_le : 0 ≤ ENNReal.ofReal ((denQ (subWord m w)) ^ (-(2 * s))))
    change nodeWeight s v (subWord m w) ≤
      transferOp (A : Set ℕ) s v (ratioT (subWord m w)) *
        ENNReal.ofReal ((denQ (subWord m w)) ^ (-(2 * s))) at hmul
    refine hmul.trans_eq ?_
    have hsub : (∑' a : {a : ℕ // a ∈ A}, nodeWeight s v (subWord (m + 1) (Fin.snoc w a))) =
        transferOp (A : Set ℕ) s v (ratioT (subWord m w)) *
          ENNReal.ofReal ((denQ (subWord m w)) ^ (-(2 * s))) := by
      have hstep : ∀ a : {a : ℕ // a ∈ A},
          nodeWeight s v (subWord (m + 1) (Fin.snoc w a)) =
            (v (1 / ((a.1 : ℝ) + ratioT (subWord m w))) *
              ENNReal.ofReal (((a.1 : ℝ) + ratioT (subWord m w)) ^ (-(2 * s)))) *
                ENNReal.ofReal ((denQ (subWord m w)) ^ (-(2 * s))) := fun a => by
        rw [subWord_snoc, nodeWeight_snoc hpd (ha1 a.1 a.2)]
      simp only [hstep, ENNReal.tsum_mul_right]
      congr 1
      exact (transferOp_eq_tsum_subtype (A : Set ℕ) s v (ratioT (subWord m w))).symm
    rw [← hsub, tsum_fintype]
  have aux : ∀ (d m : ℕ) (hmd : m + d = N) (hmN : m ≤ N) (w : Fin m → {a : ℕ // a ∈ A}),
      (¬ ∃ c ∈ Cut, c.1.1 < m ∧ subWord c.1.1 c.2 <+: subWord m w) →
      nodeWeight s v (subWord m w) ≤
        ∑ c ∈ Cut, if subWord m w <+: subWord c.1.1 c.2 then
          nodeWeight s v (subWord c.1.1 c.2) else 0 := by
    intro d
    induction d with
    | zero =>
      intro m hmd hmN w hno
      have hm_eq : m = N := by omega
      subst hm_eq
      obtain ⟨c, hcCut, hc_pref⟩ := hcov w
      have hc_le : c.1.1 ≤ m := by
        have := List.IsPrefix.length_le hc_pref
        simpa [subWord_length] using this
      have hc_eq_len : c.1.1 = m := by
        by_contra hne
        exact hno ⟨c, hcCut, by omega, hc_pref⟩
      have h1 : subWord c.1.1 c.2 = subWord m w :=
        List.IsPrefix.eq_of_length hc_pref (by simp [hc_eq_len])
      have hpref_self : subWord m w <+: subWord c.1.1 c.2 := by rw [h1]
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le) hcCut)
      simp only [hpref_self, ↓reduceIte]
      rw [h1]
    | succ d ih =>
      intro m hmd hmN w hno
      by_cases hmem : ∃ hm_lt : m < N + 1, ⟨⟨m, hm_lt⟩, w⟩ ∈ Cut
      · obtain ⟨hm_lt, hwCut⟩ := hmem
        refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le) hwCut)
        simp only [List.prefix_refl, ↓reduceIte, le_rfl]
      · have hm_snoc : m + 1 ≤ N := by omega
        have hno_child : ∀ a : {a : ℕ // a ∈ A},
            ¬ ∃ c ∈ Cut, c.1.1 < m + 1 ∧
              subWord c.1.1 c.2 <+: subWord (m + 1) (Fin.snoc w a) := by
          intro a ⟨c, hcCut, hc_lt, hc_pref⟩
          have hc_le_m : c.1.1 ≤ m := by omega
          have hc_pref_w : subWord c.1.1 c.2 <+: subWord m w := by
            rw [subWord_snoc] at hc_pref
            obtain ⟨t, ht⟩ := hc_pref
            have hle_m : c.1.1 ≤ (subWord m w).length := by rw [subWord_length]; exact hc_le_m
            have hleft := congrArg (List.take c.1.1) ht
            rw [List.take_left' (by simp [subWord_length]),
              List.take_append_of_le_length hle_m] at hleft
            exact ⟨(subWord m w).drop c.1.1, by rw [hleft]; exact List.take_append_drop _ _⟩
          by_cases hc_eq : c.1.1 = m
          · have hw_eq : c = ⟨⟨m, by omega⟩, w⟩ := by
              have hls : subWord c.1.1 c.2 = subWord m w :=
                List.IsPrefix.eq_of_length hc_pref_w (by simp [hc_eq])
              cases c with
              | mk len wf =>
                cases len with
                | mk lv hl =>
                  dsimp only at hc_eq
                  subst hc_eq
                  congr 1
                  funext ⟨i, hi⟩
                  have hget := congrArg (fun l : List ℕ => l[i]?) hls
                  simpa [subWord, hi] using hget
            exact hmem ⟨by omega, hw_eq ▸ hcCut⟩
          · exact hno ⟨c, hcCut, by omega, hc_pref_w⟩
        have hch := fun a : {a : ℕ // a ∈ A} =>
          ih (m + 1) (by omega) hm_snoc (Fin.snoc w a) (hno_child a)
        calc nodeWeight s v (subWord m w)
            ≤ ∑ a : {a : ℕ // a ∈ A}, nodeWeight s v (subWord (m + 1) (Fin.snoc w a)) :=
              step_node m hmN w
          _ ≤ ∑ a : {a : ℕ // a ∈ A}, ∑ c ∈ Cut,
                (if subWord (m + 1) (Fin.snoc w a) <+: subWord c.1.1 c.2 then
                  nodeWeight s v (subWord c.1.1 c.2) else 0) :=
              Finset.sum_le_sum fun a _ => hch a
          _ = ∑ c ∈ Cut, ∑ a : {a : ℕ // a ∈ A},
                (if subWord (m + 1) (Fin.snoc w a) <+: subWord c.1.1 c.2 then
                  nodeWeight s v (subWord c.1.1 c.2) else 0) := Finset.sum_comm
          _ ≤ ∑ c ∈ Cut, (if subWord m w <+: subWord c.1.1 c.2 then
                nodeWeight s v (subWord c.1.1 c.2) else 0) := by
              refine Finset.sum_le_sum fun c hcCut => ?_
              by_cases hpw : subWord m w <+: subWord c.1.1 c.2
              · simp only [hpw, ↓reduceIte]
                have hcle := List.IsPrefix.length_le hpw
                rw [subWord_length, subWord_length] at hcle
                have hc_gt : m < c.1.1 := by
                  rcases eq_or_lt_of_le hcle with heq | hlt
                  · exfalso
                    have hc_eq : c = ⟨⟨m, by omega⟩, w⟩ := by
                      have hls : subWord c.1.1 c.2 = subWord m w :=
                        (List.IsPrefix.eq_of_length hpw (by simp [heq])).symm
                      cases c with
                      | mk len wf =>
                        cases len with
                        | mk lv hl =>
                          dsimp only at heq
                          subst heq
                          congr 1
                          funext ⟨i, hi⟩
                          have hget := congrArg (fun l : List ℕ => l[i]?) hls
                          simpa [subWord, hi] using hget
                    exact hmem ⟨by omega, hc_eq ▸ hcCut⟩
                  · exact hlt
                let a₀ : {a : ℕ // a ∈ A} := c.2 ⟨m, hc_gt⟩
                have ha_uniq : ∀ a : {a : ℕ // a ∈ A},
                    subWord (m + 1) (Fin.snoc w a) <+: subWord c.1.1 c.2 → a = a₀ := by
                  intro a hap
                  rw [subWord_snoc] at hap
                  obtain ⟨t, ht⟩ := hap
                  have hget := congrArg (fun l : List ℕ => l[m]?) ht
                  have hm_lt1 : m < (subWord m w ++ [a.1]).length := by
                    simp [subWord_length]
                  have hm_lt2 : m < (subWord c.1.1 c.2).length := by
                    simpa [subWord_length] using hc_gt
                  have hwm : (subWord m w).length = m := subWord_length m w
                  rw [List.getElem?_append_left hm_lt1,
                    List.getElem?_append_right hwm.le, hwm, Nat.sub_self,
                    List.getElem?_eq_getElem hm_lt2] at hget
                  simp only [List.getElem?_cons_zero, subWord, List.getElem_ofFn,
                    Option.some.injEq] at hget
                  exact Subtype.ext hget
                calc ∑ a : {a : ℕ // a ∈ A},
                      (if subWord (m + 1) (Fin.snoc w a) <+: subWord c.1.1 c.2 then
                        nodeWeight s v (subWord c.1.1 c.2) else 0)
                    ≤ ∑ a : {a : ℕ // a ∈ A},
                        (if a = a₀ then nodeWeight s v (subWord c.1.1 c.2) else 0) := by
                      refine Finset.sum_le_sum fun a _ => ?_
                      split_ifs with h1 h2
                      · exact le_rfl
                      · exact absurd (ha_uniq a h1) h2
                      · exact bot_le
                      · exact le_rfl
                  _ = nodeWeight s v (subWord c.1.1 c.2) := by simp
              · have hno_child_p : ∀ a : {a : ℕ // a ∈ A},
                    ¬ (subWord (m + 1) (Fin.snoc w a) <+: subWord c.1.1 c.2) := by
                  intro a hap
                  apply hpw
                  rw [subWord_snoc] at hap
                  exact List.IsPrefix.trans ⟨[a.1], rfl⟩ hap
                simp [hpw, hno_child_p]
  have hroot := aux N 0 (Nat.zero_add N) (Nat.zero_le N) (fun i => i.elim0)
    (fun ⟨c, _, hc0, _⟩ => by omega)
  have hsub0 : subWord (A := (A : Set ℕ)) 0 (fun i : Fin 0 => i.elim0) = [] := rfl
  have h0_le : v 0 ≤ nodeWeight s v [] := by simp [nodeWeight]
  refine h0_le.trans (hroot.trans_eq ?_)
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hsub0, List.nil_prefix, ↓reduceIte]

private theorem cut_card_le_of_disjoint_Ioo {α : Type*}
    (C : Finset α) (I : α → ℝ × ℝ) {x0 d Lmin : ℝ} (hd : 0 < d) (_hLmin : 0 < Lmin)
    (hdisj : (C : Set α).Pairwise fun w₁ w₂ =>
      Disjoint (Set.Ioo (I w₁).1 (I w₁).2) (Set.Ioo (I w₂).1 (I w₂).2))
    (hsub : ∀ w ∈ C, Set.Ioo (I w).1 (I w).2 ⊆ Set.Icc (x0 - 2 * d) (x0 + 2 * d))
    (hlen : ∀ w ∈ C, Lmin ≤ (I w).2 - (I w).1) :
    (C.card : ℝ) * Lmin ≤ 4 * d := by
  classical
  have hmeas : ∀ w ∈ C, MeasurableSet (Set.Ioo (I w).1 (I w).2) := fun _ _ => measurableSet_Ioo
  have hU_sub : (⋃ w ∈ C, Set.Ioo (I w).1 (I w).2) ⊆ Set.Icc (x0 - 2 * d) (x0 + 2 * d) :=
    Set.iUnion₂_subset hsub
  have hvol := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hU_sub
  rw [MeasureTheory.measure_biUnion_finset hdisj hmeas, Real.volume_Icc] at hvol
  have hsum_le : (∑ w ∈ C, ENNReal.ofReal Lmin) ≤
      ∑ w ∈ C, MeasureTheory.volume (Set.Ioo (I w).1 (I w).2) := by
    refine Finset.sum_le_sum fun w hw => ?_
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_le_ofReal (hlen w hw)
  have hbound : (C.card : ℝ≥0∞) * ENNReal.ofReal Lmin ≤ ENNReal.ofReal (4 * d) := by
    calc (C.card : ℝ≥0∞) * ENNReal.ofReal Lmin
        = ∑ _w ∈ C, ENNReal.ofReal Lmin := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ C, MeasureTheory.volume (Set.Ioo (I w).1 (I w).2) := hsum_le
      _ ≤ ENNReal.ofReal ((x0 + 2 * d) - (x0 - 2 * d)) := hvol
      _ = ENNReal.ofReal (4 * d) := by congr 1; ring
  have hof : ENNReal.ofReal ((C.card : ℝ) * Lmin) ≤ ENNReal.ofReal (4 * d) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    exact hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hof

/-- **Bowen-Free Transfer-Operator Lower Theorem (`0 < μH[s] (cfAlphabetSet A)`)**. -/
theorem hausdorffMeasure_pos_of_transferOp_ge {A : Finset ℕ} (hAne : A.Nonempty)
    (ha1 : ∀ a ∈ A, 1 ≤ a) {s : ℝ} (hs : 0 < s)
    {v : ℝ → ℝ≥0∞} {lo hi : ℝ≥0∞} (hlo : 0 < lo) (hhi : hi < ⊤)
    (hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1, lo ≤ v x ∧ v x ≤ hi)
    (hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1, v x ≤ transferOp (A : Set ℕ) s v x) :
    0 < μH[s] (cfAlphabetSet (A : Set ℕ)) := by
  classical
  set K := cfAlphabetSet (A : Set ℕ)
  have hK_comp : IsCompact K := isCompact_cfAlphabetSet A hAne ha1
  set M := A.sup id
  have hM1 : 1 ≤ M := by
    obtain ⟨a₀, ha₀⟩ := hAne
    exact le_trans (ha1 a₀ ha₀) (Finset.le_sup (f := id) ha₀)
  have hloT : lo < ⊤ := lt_of_le_of_lt (hv_bd 0 ⟨le_rfl, zero_le_one⟩).1
    (lt_of_le_of_lt (hv_bd 0 ⟨le_rfl, zero_le_one⟩).2 hhi)
  have hv0_ne : lo ≤ v 0 := (hv_bd 0 ⟨le_rfl, zero_le_one⟩).1
  set loR : ℝ := lo.toReal
  set hiR : ℝ := hi.toReal
  have hloR : 0 < loR := ENNReal.toReal_pos hlo.ne' hloT.ne
  have hhiR : 0 < hiR := by
    have h1 : lo ≤ hi := le_trans (hv_bd 0 ⟨le_rfl, zero_le_one⟩).1
      (hv_bd 0 ⟨le_rfl, zero_le_one⟩).2
    exact ENNReal.toReal_pos (lt_of_lt_of_le hlo h1).ne' hhi.ne
  set C_moran : ℝ := 8 * ((M : ℝ) + 1) * ((M : ℝ) + 2) * (2 : ℝ) ^ s * hiR
  have hCm_pos : 0 < C_moran := by positivity
  set c₀R : ℝ := loR / (2 * C_moran)
  have hc₀R : 0 < c₀R := by positivity
  set c₀ : ℝ≥0∞ := ENNReal.ofReal c₀R
  have hc₀_pos : 0 < c₀ := ENNReal.ofReal_pos.mpr hc₀R
  refine lt_of_lt_of_le hc₀_pos ?_
  set r0R : ℝ := 1 / 2
  set r0 : ℝ≥0∞ := ENNReal.ofReal r0R
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine le_trans ?_ (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
    ⨅ (t : ℕ → Set ℝ) (_ : K ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s)
    r0 (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < r0R)))
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
  by_contra hlt
  push Not at hlt
  set S : ℝ≥0∞ := ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s
  have hS_ne_top : S ≠ ⊤ := ne_of_lt (lt_trans hlt ENNReal.ofReal_lt_top)
  have hSR : S.toReal < c₀R := by
    have h1 := (ENNReal.toReal_lt_toReal hS_ne_top ENNReal.ofReal_ne_top).mpr hlt
    rwa [ENNReal.toReal_ofReal hc₀R.le] at h1
  set δ0 : ℝ := (c₀R - S.toReal) / 2
  have hδ0 : 0 < δ0 := by dsimp [δ0]; linarith
  have hex_rho : ∀ i : ℕ, (t i).Nonempty → ∃ ρi : ℝ, 0 < ρi ∧ 2 * ρi ≤ r0R ∧
      (Metric.ediam (t i) + ENNReal.ofReal (2 * ρi)) ^ s ≤
        Metric.ediam (t i) ^ s + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i + 1)) := by
    intro i hne
    have hleS : Metric.ediam (t i) ^ s ≤ S := by
      have h1 : (⨆ _ : (t i).Nonempty, Metric.ediam (t i) ^ s) ≤ S :=
        ENNReal.le_tsum (f := fun n => ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s) i
      simpa [hne] using h1
    have hm_lt : Metric.ediam (t i) ^ s < ⊤ := by
      have hc₀T : c₀ < ⊤ := ENNReal.ofReal_lt_top
      exact lt_of_le_of_lt hleS (lt_trans hlt hc₀T)
    have hlt_m : Metric.ediam (t i) ^ s <
        Metric.ediam (t i) ^ s + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i + 1)) :=
      ENNReal.lt_add_right hm_lt.ne (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hcont : Filter.Tendsto (fun x : ℝ≥0∞ => (Metric.ediam (t i) + x) ^ s)
        (nhds 0) (nhds (Metric.ediam (t i) ^ s)) := by
      have h1 : Filter.Tendsto (fun x : ℝ≥0∞ => Metric.ediam (t i) + x)
          (nhds 0) (nhds (Metric.ediam (t i) + 0)) := tendsto_const_nhds.add tendsto_id
      rw [add_zero] at h1
      exact ((ENNReal.continuous_rpow_const (y := s)).continuousAt).tendsto.comp h1
    have hev := hcont.eventually (Iio_mem_nhds hlt_m)
    rw [ENNReal.nhds_zero_basis.eventually_iff] at hev
    obtain ⟨η, hη_pos, hη⟩ := hev
    by_cases htop : η = ⊤
    · refine ⟨r0R / 2, by norm_num [r0R], by norm_num [r0R], ?_⟩
      exact (hη (by rw [htop]; exact ENNReal.ofReal_lt_top)).le
    · have hηpos : 0 < η.toReal := ENNReal.toReal_pos hη_pos.ne' htop
      set ρi : ℝ := min (r0R / 2) (η.toReal / 4)
      have hρ_le1 : ρi ≤ r0R / 2 := min_le_left _ _
      have hρ_le2 : ρi ≤ η.toReal / 4 := min_le_right _ _
      have h2ρ_lt_η : ENNReal.ofReal (2 * ρi) < η := by
        have h1 : 2 * ρi ≤ η.toReal / 2 := by linarith
        calc ENNReal.ofReal (2 * ρi)
            ≤ ENNReal.ofReal (η.toReal / 2) := ENNReal.ofReal_le_ofReal h1
          _ < ENNReal.ofReal η.toReal :=
              (ENNReal.ofReal_lt_ofReal_iff hηpos).mpr (by linarith)
          _ = η := ENNReal.ofReal_toReal htop
      refine ⟨ρi, lt_min (by norm_num [r0R]) (by linarith),
        (mul_le_mul_of_nonneg_left hρ_le1 zero_le_two).trans_eq (mul_div_cancel₀ r0R two_ne_zero),
        (hη h2ρ_lt_η).le⟩
  choose ρ hρ_pos h2ρ_le hρ_m using fun i : {i : ℕ // (t i).Nonempty} => hex_rho i.1 i.2
  let V : {i : ℕ // (t i).Nonempty} → Set ℝ := fun i => Metric.thickening (ρ i) (t i.1)
  have hV_open : ∀ i, IsOpen (V i) := fun _ => Metric.isOpen_thickening
  have hV_cov : K ⊆ ⋃ i : {i : ℕ // (t i).Nonempty}, V i := fun x hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, Metric.self_subset_thickening (hρ_pos _) _ hi⟩
  obtain ⟨F, hFcov⟩ := hK_comp.elim_finite_subcover V hV_open hV_cov
  have hK_ne : K.Nonempty := by
    obtain ⟨a₀, ha₀⟩ := hAne
    obtain ⟨hx01, hxirr, hxdig⟩ := cfVal_spec (a := fun _ : ℕ => a₀) (fun _ => ha1 a₀ ha₀)
    exact ⟨cfVal (fun _ => a₀), hx01, hxirr, fun i => by rw [hxdig i]; exact ha₀⟩
  have hFne : F.Nonempty := by
    obtain ⟨x₀, hx₀⟩ := hK_ne
    obtain ⟨i, hiF, _⟩ := Set.mem_iUnion₂.mp (hFcov hx₀)
    exact ⟨i, hiF⟩
  have hV_bd : ∀ i, Bornology.IsBounded (V i) := fun i =>
    isBounded_thickening_of_ediam (hρ_pos i).le (hdiam i.1) ENNReal.ofReal_ne_top
  have hV_ediam_le : ∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal 1 := fun i => by
    calc Metric.ediam (V i)
        ≤ Metric.ediam (t i.1) + ENNReal.ofReal (2 * ρ i) := by
          have h2 : 2 * ENNReal.ofReal (ρ i) = ENNReal.ofReal (2 * ρ i) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp
          rw [← h2]
          exact ediam_thickening_le (hρ_pos i).le
      _ ≤ r0 + ENNReal.ofReal r0R := add_le_add (hdiam i.1) (ENNReal.ofReal_le_ofReal (h2ρ_le i))
      _ = ENNReal.ofReal 1 := by
          rw [← ENNReal.ofReal_add (by norm_num [r0R]) (by norm_num [r0R])]
          congr 1; norm_num [r0R]
  have hV_diam_le : ∀ i, Metric.diam (V i) ≤ 1 := fun i => by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hV_ediam_le i)
    rwa [ENNReal.toReal_ofReal zero_le_one] at h1
  have hV_diam_pos : ∀ i, 0 < Metric.diam (V i) := fun i =>
    diam_thickening_pos i.2 (hρ_pos i) (hV_bd i)
  have hV_ne : ∀ i, (V i).Nonempty := fun i =>
    let ⟨x, hx⟩ := i.2; ⟨x, Metric.self_subset_thickening (hρ_pos i) _ hx⟩
  set dmin : ℝ := (F.image (fun i => Metric.diam (V i))).min' (hFne.image _)
  have hdmin_pos : 0 < dmin := by
    obtain ⟨i, hiF, himin⟩ :=
      Finset.mem_image.mp (Finset.min'_mem (F.image fun i => Metric.diam (V i)) (hFne.image _))
    dsimp only [dmin]
    rw [← himin]
    exact hV_diam_pos i
  obtain ⟨N, hN_gt⟩ := exists_nat_gt (1 / dmin)
  let N₀ := max N 1
  have hN1 : 1 ≤ N₀ := le_max_right _ _
  have hN₀_len : ∀ u : Fin N₀ → {a : ℕ // a ∈ A}, ∀ i ∈ F,
      (cylPair (subWord N₀ u)).2 - (cylPair (subWord N₀ u)).1 < Metric.diam (V i) := by
    intro u i hiF
    have hd_min_le : dmin ≤ Metric.diam (V i) := Finset.min'_le _ _ (Finset.mem_image_of_mem _ hiF)
    have hN₀_gt : 1 / dmin < (N₀ : ℝ) := lt_of_lt_of_le hN_gt (by exact_mod_cast le_max_left N 1)
    have hlen_le : (cylPair (subWord N₀ u)).2 - (cylPair (subWord N₀ u)).1 ≤ 1 / (N₀ : ℝ) := by
      have hpd := posDigits_subWord (fun a ha => ha1 a ha) N₀ u
      have hne : subWord N₀ u ≠ [] := by
        intro h; have := subWord_length N₀ u
        rw [h] at this; simp only [List.length_nil] at this; omega
      have hbd := (cylPair_len_bounds hpd hne).2
      have hden := (cfProd_zero_cons_den_ge hpd).1
      have hq_ge : (N₀ : ℝ) ≤ denQ (subWord N₀ u) := by
        unfold denQ
        exact_mod_cast (subWord_length N₀ u) ▸ hden
      have hq2 : (N₀ : ℝ) ^ 2 ≤ (denQ (subWord N₀ u)) ^ 2 := by
        have : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg N₀
        nlinarith
      have hN₀_pos : (0 : ℝ) < (N₀ : ℝ) := by exact_mod_cast hN1
      have h1 : (N₀ : ℝ) ≤ (N₀ : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN1
        nlinarith
      exact hbd.trans (one_div_le_one_div_of_le hN₀_pos (h1.trans hq2))
    have hinv_lt : 1 / (N₀ : ℝ) < dmin := by
      have hN₀_pos : (0 : ℝ) < (N₀ : ℝ) := by exact_mod_cast hN1
      rw [div_lt_iff₀ hdmin_pos] at hN₀_gt
      rw [div_lt_iff₀ hN₀_pos]
      linarith
    linarith
  let Node := Σ m : Fin (N₀ + 1), Fin m.1 → {a : ℕ // a ∈ A}
  let condI (i : {i : ℕ // (t i).Nonempty}) (c : Node) : Prop :=
    1 ≤ c.1.1 ∧
    (V i ∩ Set.Icc (cylPair (subWord c.1.1 c.2)).1
      (cylPair (subWord c.1.1 c.2)).2).Nonempty ∧
    (cylPair (subWord c.1.1 c.2)).2 - (cylPair (subWord c.1.1 c.2)).1 ≤ Metric.diam (V i) ∧
    ∀ (m' : ℕ) (hm' : m' < c.1.1), 1 ≤ m' →
      Metric.diam (V i) <
        (cylPair (subWord m' (prefixFin (by omega : m' ≤ c.1.1) c.2))).2 -
          (cylPair (subWord m' (prefixFin (by omega : m' ≤ c.1.1) c.2))).1
  let CutI (i : {i : ℕ // (t i).Nonempty}) : Finset Node := Finset.univ.filter (condI i)
  let CutAll : Finset Node := F.biUnion CutI
  let CutMin : Finset Node := CutAll.filter fun c =>
    ∀ (m' : ℕ) (hm' : m' < c.1.1), 1 ≤ m' →
      (⟨⟨m', by omega⟩, prefixFin (by omega : m' ≤ c.1.1) c.2⟩ : Node) ∉ CutAll
  have hCut_min_spec : ∀ c ∈ CutMin, 1 ≤ c.1.1 ∧
      ∀ c' ∈ CutMin, (subWord c'.1.1 c'.2 <+: subWord c.1.1 c.2) → c' = c := by
    intro c hc
    obtain ⟨hcAll, hc_no⟩ := Finset.mem_filter.mp hc
    obtain ⟨i, _, hci⟩ := Finset.mem_biUnion.mp hcAll
    have hc1 : 1 ≤ c.1.1 := (Finset.mem_filter.mp hci).2.1
    refine ⟨hc1, fun c' hc' hpref => ?_⟩
    obtain ⟨hc'All, _⟩ := Finset.mem_filter.mp hc'
    obtain ⟨i', _, hc'i⟩ := Finset.mem_biUnion.mp hc'All
    have hc'1 : 1 ≤ c'.1.1 := (Finset.mem_filter.mp hc'i).2.1
    obtain ⟨hle, hw_eq⟩ := (subWord_isPrefix_iff_prefixFin c'.2 c.2).mp hpref
    rcases eq_or_lt_of_le hle with heq | hlt_len
    · cases c with | mk l w => cases c' with | mk l' w' =>
      have hl : l' = l := Fin.ext heq
      subst hl
      refine congrArg (Sigma.mk l') (funext fun j => ?_)
      have hji := congrFun hw_eq j
      simpa [prefixFin] using hji
    · exfalso
      apply hc_no c'.1.1 hlt_len hc'1
      have hc'eq : c' = ⟨⟨c'.1.1, by omega⟩, prefixFin (by omega : c'.1.1 ≤ c.1.1) c.2⟩ := by
        cases c' with | mk l' w' =>
        cases l' with | mk lv hlv =>
        refine congrArg (Sigma.mk (⟨lv, hlv⟩ : Fin (N₀ + 1))) (funext fun j => ?_)
        have hji := congrFun hw_eq j
        simpa [prefixFin] using hji
      rwa [← hc'eq]
  have hCut_cov : ∀ u : Fin N₀ → {a : ℕ // a ∈ A},
      ∃ c ∈ CutMin, subWord c.1.1 c.2 <+: subWord N₀ u := by
    intro u
    obtain ⟨x, hxK, hx_cyl⟩ :=
      (cfAlphabetSet_nonempty_cyl A hAne ha1 u).resolve_right (by omega)
    obtain ⟨i, hiF, hxV⟩ := Set.mem_iUnion₂.mp (hFcov hxK)
    have hex_hit : ∃ m : ℕ, 1 ≤ m ∧ m ≤ N₀ ∧ ∀ h : m ≤ N₀,
        (cylPair (subWord m (prefixFin h u))).2 -
          (cylPair (subWord m (prefixFin h u))).1 ≤ Metric.diam (V i) :=
      ⟨N₀, hN1, le_rfl, fun _ => (hN₀_len u i hiF).le⟩
    let m₁ := Nat.find hex_hit
    have hm₁ := Nat.find_spec hex_hit
    have hm₁_ge : 1 ≤ m₁ := hm₁.1
    have hm₁_le : m₁ ≤ N₀ := hm₁.2.1
    have hm₁_diam : (cylPair (subWord m₁ (prefixFin hm₁_le u))).2 -
        (cylPair (subWord m₁ (prefixFin hm₁_le u))).1 ≤ Metric.diam (V i) :=
      hm₁.2.2 hm₁_le
    let c₁ : Node := ⟨⟨m₁, Nat.lt_succ_of_le hm₁_le⟩, prefixFin hm₁_le u⟩
    have hc₁_in : c₁ ∈ CutI i := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm₁_ge, ?_, hm₁_diam, fun m' hm' hm'1 => ?_⟩
      · have hnest : Set.Icc (cylPair (subWord N₀ u)).1 (cylPair (subWord N₀ u)).2 ⊆
            Set.Icc (cylPair (subWord c₁.1.1 c₁.2)).1 (cylPair (subWord c₁.1.1 c₁.2)).2 := by
          have hsplit : subWord N₀ u =
              subWord c₁.1.1 c₁.2 ++
                List.ofFn (fun j : Fin (N₀ - m₁) => (u ⟨m₁ + j.1, by omega⟩).1) := by
            refine List.ext_getElem (by simp [c₁]; omega) fun t ht1 ht2 => ?_
            simp only [subWord, List.getElem_append, List.length_ofFn, c₁, prefixFin] at ht2 ⊢
            split_ifs with hlt
            · simp only [List.getElem_ofFn]
            · simp only [List.getElem_ofFn, Nat.add_sub_cancel' (not_lt.mp hlt)]
          rw [hsplit]
          exact cylPair_nest (posDigits_subWord (fun a ha => ha1 a ha) c₁.1.1 c₁.2)
            (by intro h; have := subWord_length c₁.1.1 c₁.2; rw [h] at this
                simp only [List.length_nil] at this; dsimp [c₁] at this; omega)
            (fun d hd => by
              rw [List.mem_ofFn] at hd
              obtain ⟨j, rfl⟩ := hd
              exact ha1 _ (u _).2)
        exact ⟨x, hxV, hnest hx_cyl⟩
      · have hnot := Nat.find_min hex_hit hm'
        push Not at hnot
        have hm'_le : m' ≤ N₀ := by dsimp [c₁] at hm'; omega
        exact (hnot hm'1 hm'_le).choose_spec
    have hc₁_all : c₁ ∈ CutAll := Finset.mem_biUnion.mpr ⟨i, hiF, hc₁_in⟩
    have hex_m : ∃ m : ℕ, 1 ≤ m ∧ m ≤ N₀ ∧
        ∀ hm : m ≤ N₀, (⟨⟨m, Nat.lt_succ_of_le hm⟩, prefixFin hm u⟩ : Node) ∈ CutAll :=
      ⟨m₁, hm₁_ge, hm₁_le, fun hm => by
        convert hc₁_all using 2⟩
    let m₀ := Nat.find hex_m
    have hm₀ := Nat.find_spec hex_m
    have hm₀_ge : 1 ≤ m₀ := hm₀.1
    have hm₀_le : m₀ ≤ N₀ := hm₀.2.1
    let c₀n : Node := ⟨⟨m₀, Nat.lt_succ_of_le hm₀_le⟩, prefixFin hm₀_le u⟩
    refine ⟨c₀n, Finset.mem_filter.mpr ⟨hm₀.2.2 hm₀_le, fun m' hm' hm'1 => ?_⟩, ?_⟩
    · have hnot := Nat.find_min hex_m hm'
      intro hmem'
      have hm'_le : m' ≤ N₀ := by dsimp [c₀n] at hm'; omega
      apply hnot ⟨hm'1, hm'_le, fun hm'' => ?_⟩
      convert hmem' using 2
      funext j; rfl
    · exact (subWord_isPrefix_iff_prefixFin c₀n.2 u).mpr ⟨hm₀_le, rfl⟩
  have htree := tree_prefixCut_weight_le ha1 hsuper N₀ CutMin hCut_min_spec hCut_cov
  have hCut_le_F : ∑ c ∈ CutMin, nodeWeight s v (subWord c.1.1 c.2) ≤
      ∑ i ∈ F, ∑ c ∈ CutI i, nodeWeight s v (subWord c.1.1 c.2) := by
    have h1 : ∑ c ∈ CutMin, nodeWeight s v (subWord c.1.1 c.2) ≤
        ∑ c ∈ CutAll, nodeWeight s v (subWord c.1.1 c.2) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hbi : ∀ G : Finset {i : ℕ // (t i).Nonempty},
        ∑ c ∈ G.biUnion CutI, nodeWeight s v (subWord c.1.1 c.2) ≤
          ∑ i ∈ G, ∑ c ∈ CutI i, nodeWeight s v (subWord c.1.1 c.2) := by
      intro G
      induction G using Finset.induction_on with
      | empty => simp
      | insert a G₀ ha ih =>
        rw [Finset.biUnion_insert, Finset.sum_insert ha]
        have hu : ∑ c ∈ CutI a ∪ G₀.biUnion CutI, nodeWeight s v (subWord c.1.1 c.2) ≤
            (∑ c ∈ CutI a, nodeWeight s v (subWord c.1.1 c.2)) +
              (∑ c ∈ G₀.biUnion CutI, nodeWeight s v (subWord c.1.1 c.2)) := by
          have hint := Finset.sum_union_inter
            (f := fun c : Node => nodeWeight s v (subWord c.1.1 c.2))
            (s₁ := CutI a) (s₂ := G₀.biUnion CutI)
          exact le_self_add.trans_eq hint
        exact hu.trans (add_le_add le_rfl ih)
    exact h1.trans (hbi F)
  have hCutI_bound : ∀ i ∈ F,
      (∑ c ∈ CutI i, nodeWeight s v (subWord c.1.1 c.2)) ≤
        ENNReal.ofReal (C_moran * (Metric.diam (V i)) ^ s) := by
    intro i _
    have hci_spec := fun c (hc : c ∈ CutI i) => (Finset.mem_filter.mp hc).2
    have hcard_le : ((CutI i).card : ℝ) ≤ 8 * ((M : ℝ) + 1) * ((M : ℝ) + 2) := by
      have hdisj : (CutI i : Set Node).Pairwise fun c₁ c₂ =>
          Disjoint (Set.Ioo (cylPair (subWord c₁.1.1 c₁.2)).1
              (cylPair (subWord c₁.1.1 c₁.2)).2)
            (Set.Ioo (cylPair (subWord c₂.1.1 c₂.2)).1
              (cylPair (subWord c₂.1.1 c₂.2)).2) := by
        intro c₁ hc₁ c₂ hc₂ hne
        have h1 := hci_spec c₁ hc₁
        have h2 := hci_spec c₂ hc₂
        refine cylPair_disj_of_incomparable
          (posDigits_subWord (fun a ha => ha1 a ha) c₁.1.1 c₁.2)
          (posDigits_subWord (fun a ha => ha1 a ha) c₂.1.1 c₂.2) ?_ ?_
        · intro hpref
          obtain ⟨hle, hw⟩ := (subWord_isPrefix_iff_prefixFin c₁.2 c₂.2).mp hpref
          rcases eq_or_lt_of_le hle with heq | hlt_len
          · apply hne
            cases c₁ with | mk l₁ w₁ => cases c₂ with | mk l₂ w₂ =>
            dsimp only at heq
            have hl : l₁ = l₂ := Fin.ext heq
            subst hl
            exact congrArg (Sigma.mk _) (funext fun j => by simpa [prefixFin] using congrFun hw j)
          · have hgt := h2.2.2.2 c₁.1.1 hlt_len h1.1
            have hle' := h1.2.2.1
            have heq_p : prefixFin (by omega : c₁.1.1 ≤ c₂.1.1) c₂.2 = c₁.2 := hw.symm
            rw [heq_p] at hgt
            linarith
        · intro hpref
          obtain ⟨hle, hw⟩ := (subWord_isPrefix_iff_prefixFin c₂.2 c₁.2).mp hpref
          rcases eq_or_lt_of_le hle with heq | hlt_len
          · apply hne.symm
            cases c₁ with | mk l₁ w₁ => cases c₂ with | mk l₂ w₂ =>
            dsimp only at heq
            have hl : l₂ = l₁ := Fin.ext heq
            subst hl
            exact congrArg (Sigma.mk _) (funext fun j => by simpa [prefixFin] using congrFun hw j)
          · have hgt := h1.2.2.2 c₂.1.1 hlt_len h2.1
            have hle' := h2.2.2.1
            have heq_p : prefixFin (by omega : c₂.1.1 ≤ c₁.1.1) c₁.2 = c₂.2 := hw.symm
            rw [heq_p] at hgt
            linarith
      obtain ⟨x0, hx0⟩ := hV_ne i
      have hsub_box : ∀ c ∈ CutI i,
          Set.Ioo (cylPair (subWord c.1.1 c.2)).1 (cylPair (subWord c.1.1 c.2)).2 ⊆
            Set.Icc (x0 - 2 * Metric.diam (V i)) (x0 + 2 * Metric.diam (V i)) := by
        intro c hc y hy
        obtain ⟨xc, hxcV, hxcI⟩ := (hci_spec c hc).2.1
        have hxc0 : dist xc x0 ≤ Metric.diam (V i) := Metric.dist_le_diam_of_mem (hV_bd i) hxcV hx0
        have hlen_bd := (hci_spec c hc).2.2.1
        rw [Real.dist_eq, abs_le] at hxc0
        constructor <;> linarith [hy.1, hy.2, hxcI.1, hxcI.2]
      have hLmin_eq : ∀ c ∈ CutI i,
          Metric.diam (V i) / (2 * ((M : ℝ) + 1) * ((M : ℝ) + 2)) ≤
            (cylPair (subWord c.1.1 c.2)).2 - (cylPair (subWord c.1.1 c.2)).1 := by
        intro c hc
        have h1 := (hci_spec c hc).1
        rcases eq_or_lt_of_le h1 with heq | hgt1
        · have hpd := posDigits_subWord (fun a ha => ha1 a ha) c.1.1 c.2
          have hne : subWord c.1.1 c.2 ≠ [] := by
            intro h; have := subWord_length c.1.1 c.2
            rw [h] at this; simp only [List.length_nil] at this; omega
          have hlen1 := (cylPair_len_bounds hpd hne).1
          have hlen_w : c.1.1 = 1 := heq.symm
          have hden_le : denQ (subWord c.1.1 c.2) ≤ (M : ℝ) + 1 := by
            have hd_eq : subWord c.1.1 c.2 = [(c.2 ⟨0, by omega⟩).1] := by
              refine List.ext_getElem (by simp [hlen_w]) fun j hj1 _ => ?_
              have hj0 : j = 0 := by rw [subWord_length, hlen_w] at hj1; omega
              subst hj0; simp [subWord]
            rw [hd_eq]
            have ha_leM : (c.2 ⟨0, by omega⟩).1 ≤ M :=
              Finset.le_sup (f := id) (c.2 ⟨0, by omega⟩).2
            have haR : ((c.2 ⟨0, by omega⟩).1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast ha_leM
            unfold denQ
            simp [cfProd, cfMat]
            linarith
          have hden_sq : 2 * (denQ (subWord c.1.1 c.2)) ^ 2 ≤
              2 * ((M : ℝ) + 1) * ((M : ℝ) + 2) := by
            have hq := (denQ_pos hpd).le
            have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
            nlinarith
          have h_inv : 1 / (2 * ((M : ℝ) + 1) * ((M : ℝ) + 2)) ≤
              1 / (2 * (denQ (subWord c.1.1 c.2)) ^ 2) :=
            one_div_le_one_div_of_le (by have := denQ_pos hpd; positivity) hden_sq
          have hd_le1 := hV_diam_le i
          have hdiv_le : Metric.diam (V i) / (2 * ((M : ℝ) + 1) * ((M : ℝ) + 2)) ≤
              1 / (2 * ((M : ℝ) + 1) * ((M : ℝ) + 2)) :=
            div_le_div_of_nonneg_right hd_le1 (by positivity)
          linarith
        · let m' := c.1.1 - 1
          have hm'1 : 1 ≤ m' := by omega
          have hm'_lt : m' < c.1.1 := by omega
          have hgt := (hci_spec c hc).2.2.2 m' hm'_lt hm'1
          let p := prefixFin (by omega : m' ≤ c.1.1) c.2
          have hcons : subWord c.1.1 c.2 =
              subWord m' p ++ [(c.2 ⟨m', by omega⟩).1] := by
            refine List.ext_getElem (by simp; omega) fun j hj1 hj2 => ?_
            simp only [subWord, List.getElem_append, List.length_ofFn, p, prefixFin] at hj2 ⊢
            split_ifs with hlt
            · simp only [List.getElem_ofFn]
            · have hj_eq : j = m' := by rw [subWord_length] at hj1; omega
              subst hj_eq
              simp
          rw [hcons]
          have hstep := cylPair_len_step_ge
            (posDigits_subWord (fun a ha => ha1 a ha) m' p)
            (by
              intro h; have := subWord_length m' p
              rw [h] at this; simp only [List.length_nil] at this; omega)
            (ha1 _ (c.2 ⟨m', by omega⟩).2)
            (Finset.le_sup (f := id) (c.2 ⟨m', by omega⟩).2)
          have hd_div := div_le_div_of_nonneg_right hgt.le
            (show 0 ≤ 2 * ((M : ℝ) + 1) * ((M : ℝ) + 2) by positivity)
          linarith
      have hc_bd := cut_card_le_of_disjoint_Ioo (CutI i) (fun c => cylPair (subWord c.1.1 c.2))
        (hV_diam_pos i)
        (div_pos (hV_diam_pos i) (by positivity))
        hdisj hsub_box hLmin_eq
      have hd_pos : 0 < Metric.diam (V i) := hV_diam_pos i
      have hdiv_rw :
          ((CutI i).card : ℝ) * (Metric.diam (V i) / (2 * ((M : ℝ) + 1) * ((M : ℝ) + 2))) ≤
          4 * Metric.diam (V i) := hc_bd
      rw [mul_div_assoc',
        div_le_iff₀ (by positivity : 0 < 2 * ((M : ℝ) + 1) * ((M : ℝ) + 2))] at hdiv_rw
      have hdiv_rw2 : ((CutI i).card : ℝ) * Metric.diam (V i) ≤
          (8 * ((M : ℝ) + 1) * ((M : ℝ) + 2)) * Metric.diam (V i) := by linarith
      have hcard_le8 : ((CutI i).card : ℝ) ≤ 8 * ((M : ℝ) + 1) * ((M : ℝ) + 2) :=
        le_of_mul_le_mul_right hdiv_rw2 hd_pos
      exact hcard_le8
    have hper_wt : ∀ c ∈ CutI i,
        nodeWeight s v (subWord c.1.1 c.2) ≤
          ENNReal.ofReal (hiR * (2 : ℝ) ^ s * (Metric.diam (V i)) ^ s) := by
      intro c hc
      have h1 := (hci_spec c hc).1
      have hpd := posDigits_subWord (fun a ha => ha1 a ha) c.1.1 c.2
      have hne : subWord c.1.1 c.2 ≠ [] := by
        intro h; have := subWord_length c.1.1 c.2
        rw [h] at this; simp only [List.length_nil] at this; omega
      have hq_pos := denQ_pos hpd
      have hv_hi : v (ratioT (subWord c.1.1 c.2)) ≤ ENNReal.ofReal hiR := by
        rw [ENNReal.ofReal_toReal hhi.ne]
        exact (hv_bd _ (ratioT_mem_Icc hpd)).2
      have hlen_lo := (cylPair_len_bounds hpd hne).1
      have hlen_hi := (hci_spec c hc).2.2.1
      have hq_inv_le : (denQ (subWord c.1.1 c.2)) ^ (-(2 : ℝ)) ≤ 2 * Metric.diam (V i) := by
        have hq2_pos : 0 < 2 * (denQ (subWord c.1.1 c.2)) ^ 2 := by positivity
        have h1d : 1 / (denQ (subWord c.1.1 c.2)) ^ 2 ≤ 2 * Metric.diam (V i) := by
          have h0 : 1 / (2 * (denQ (subWord c.1.1 c.2)) ^ 2) ≤ Metric.diam (V i) :=
            hlen_lo.trans hlen_hi
          rw [div_le_iff₀ hq2_pos] at h0
          rw [div_le_iff₀ (by positivity : 0 < (denQ (subWord c.1.1 c.2)) ^ 2)]
          linarith
        have hpow_eq : (denQ (subWord c.1.1 c.2)) ^ (-(2 : ℝ)) =
            1 / (denQ (subWord c.1.1 c.2)) ^ 2 := by
          rw [Real.rpow_neg hq_pos.le, one_div]; norm_cast
        linarith
      have hrpow_le : (denQ (subWord c.1.1 c.2)) ^ (-(2 * s)) ≤
          (2 : ℝ) ^ s * (Metric.diam (V i)) ^ s := by
        have hd_pos := hV_diam_pos i
        have hqpow : (denQ (subWord c.1.1 c.2)) ^ (-(2 * s)) =
            ((denQ (subWord c.1.1 c.2)) ^ (-(2 : ℝ))) ^ s := by
          rw [← Real.rpow_mul hq_pos.le]
          congr 1; ring
        rw [hqpow, ← Real.mul_rpow (by norm_num) hd_pos.le]
        exact Real.rpow_le_rpow (Real.rpow_nonneg hq_pos.le _) hq_inv_le hs.le
      unfold nodeWeight
      calc v (ratioT (subWord c.1.1 c.2)) *
              ENNReal.ofReal ((denQ (subWord c.1.1 c.2)) ^ (-(2 * s)))
          ≤ ENNReal.ofReal hiR * ENNReal.ofReal ((2 : ℝ) ^ s * (Metric.diam (V i)) ^ s) :=
            mul_le_mul' hv_hi (ENNReal.ofReal_le_ofReal hrpow_le)
        _ = ENNReal.ofReal (hiR * (2 : ℝ) ^ s * (Metric.diam (V i)) ^ s) := by
            rw [← ENNReal.ofReal_mul hhiR.le, mul_assoc]
    calc ∑ c ∈ CutI i, nodeWeight s v (subWord c.1.1 c.2)
        ≤ ∑ _c ∈ CutI i, ENNReal.ofReal (hiR * (2 : ℝ) ^ s * (Metric.diam (V i)) ^ s) :=
          Finset.sum_le_sum hper_wt
      _ = ((CutI i).card : ℝ≥0∞) *
            ENNReal.ofReal (hiR * (2 : ℝ) ^ s * (Metric.diam (V i)) ^ s) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (8 * ((M : ℝ) + 1) * ((M : ℝ) + 2)) *
            ENNReal.ofReal (hiR * (2 : ℝ) ^ s * (Metric.diam (V i)) ^ s) := by
          apply mul_le_mul_of_nonneg_right _ bot_le
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hcard_le
      _ = ENNReal.ofReal (C_moran * (Metric.diam (V i)) ^ s) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; dsimp only [C_moran]; ring
  have hsum_F_le : (∑ i ∈ F, ENNReal.ofReal (C_moran * (Metric.diam (V i)) ^ s)) ≤
      ENNReal.ofReal C_moran * (S + ENNReal.ofReal δ0) := by
    have hterm : ∀ i ∈ F,
        ENNReal.ofReal (C_moran * (Metric.diam (V i)) ^ s) ≤
          ENNReal.ofReal C_moran *
            (Metric.ediam (t i.1) ^ s + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1))) := by
      intro i _
      rw [ENNReal.ofReal_mul hCm_pos.le]
      refine mul_le_mul_of_nonneg_left ?_ bot_le
      have hdiam_eq : ENNReal.ofReal (Metric.diam (V i)) = Metric.ediam (V i) := by
        have hne_top := Metric.isBounded_iff_ediam_ne_top.mp (hV_bd i)
        exact ENNReal.ofReal_toReal hne_top
      have hrpow_eq : ENNReal.ofReal ((Metric.diam (V i)) ^ s) = Metric.ediam (V i) ^ s := by
        rw [← ENNReal.ofReal_rpow_of_pos (hV_diam_pos i), hdiam_eq]
      have hthick : Metric.ediam (V i) ^ s ≤
          (Metric.ediam (t i.1) + ENNReal.ofReal (2 * ρ i)) ^ s := by
        refine ENNReal.rpow_le_rpow ?_ hs.le
        have h2 : 2 * ENNReal.ofReal (ρ i) = ENNReal.ofReal (2 * ρ i) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
        rw [← h2]
        exact ediam_thickening_le (hρ_pos i).le
      exact hrpow_eq.symm ▸ hthick.trans (hρ_m i)
    have hsum1 : (∑ i ∈ F, Metric.ediam (t i.1) ^ s) ≤ S := by
      have hle_img : (∑ i ∈ F, Metric.ediam (t i.1) ^ s) ≤
          ∑ i ∈ F, ⨆ _ : (t i.1).Nonempty, Metric.ediam (t i.1) ^ s :=
        Finset.sum_le_sum fun i _ => by simp [i.2]
      have hfin_tsum : (∑ i ∈ F, ⨆ _ : (t i.1).Nonempty, Metric.ediam (t i.1) ^ s) ≤
          ∑' n : ℕ, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s := by
        have h_im :
            (F.image Subtype.val).sum (fun n => ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s) =
            F.sum (fun i => ⨆ _ : (t i.1).Nonempty, Metric.ediam (t i.1) ^ s) :=
          Finset.sum_image fun a _ b _ h => Subtype.ext h
        rw [← h_im]
        exact ENNReal.sum_le_tsum _
      exact hle_img.trans hfin_tsum
    have hsum2 : (∑ i ∈ F, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1))) ≤ ENNReal.ofReal δ0 := by
      have hfin_tsum : (∑ i ∈ F, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1))) ≤
          ∑' n : ℕ, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (n + 1)) := by
        have h_im : (F.image Subtype.val).sum (fun n => ENNReal.ofReal (δ0 / (2 : ℝ) ^ (n + 1))) =
            F.sum (fun i => ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1))) :=
          Finset.sum_image fun a _ b _ h => Subtype.ext h
        rw [← h_im]
        exact ENNReal.sum_le_tsum _
      have hgeom : (∑' n : ℕ, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (n + 1))) = ENNReal.ofReal δ0 := by
        have hsum_R : HasSum (fun n : ℕ => δ0 * ((1 / 2 : ℝ) ^ (n + 1))) δ0 := by
          have hs0 := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (δ0 * (1 / 2))
          have hs1 : (δ0 * (1 / 2)) * (1 - (1 / 2 : ℝ))⁻¹ = δ0 := by ring
          rw [hs1] at hs0
          refine hs0.congr_fun fun n => ?_
          rw [pow_succ']
          ring
        have heq_f : (fun n : ℕ => ENNReal.ofReal (δ0 / (2 : ℝ) ^ (n + 1))) =
            fun n : ℕ => ENNReal.ofReal (δ0 * ((1 / 2 : ℝ) ^ (n + 1))) := by
          funext n; congr 1; rw [one_div, inv_pow, div_eq_mul_inv]
        rw [heq_f, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum_R.summable,
          hsum_R.tsum_eq]
      exact hfin_tsum.trans_eq hgeom
    calc (∑ i ∈ F, ENNReal.ofReal (C_moran * (Metric.diam (V i)) ^ s))
        ≤ ∑ i ∈ F, ENNReal.ofReal C_moran *
            (Metric.ediam (t i.1) ^ s + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1))) :=
          Finset.sum_le_sum hterm
      _ = ENNReal.ofReal C_moran *
            ((∑ i ∈ F, Metric.ediam (t i.1) ^ s) +
              (∑ i ∈ F, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1)))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ ENNReal.ofReal C_moran * (S + ENNReal.ofReal δ0) :=
          mul_le_mul_of_nonneg_left (add_le_add hsum1 hsum2) bot_le
  have hlo_all : lo ≤ ENNReal.ofReal C_moran * (S + ENNReal.ofReal δ0) := by
    calc lo ≤ v 0 := hv0_ne
      _ ≤ ∑ c ∈ CutMin, nodeWeight s v (subWord c.1.1 c.2) := htree
      _ ≤ ∑ i ∈ F, ∑ c ∈ CutI i, nodeWeight s v (subWord c.1.1 c.2) := hCut_le_F
      _ ≤ ∑ i ∈ F, ENNReal.ofReal (C_moran * (Metric.diam (V i)) ^ s) :=
          Finset.sum_le_sum hCutI_bound
      _ ≤ ENNReal.ofReal C_moran * (S + ENNReal.ofReal δ0) := hsum_F_le
  have hS_eq : S = ENNReal.ofReal S.toReal := (ENNReal.ofReal_toReal hS_ne_top).symm
  have hlo_eq : lo = ENNReal.ofReal loR := (ENNReal.ofReal_toReal hloT.ne).symm
  rw [hS_eq, hlo_eq, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hδ0.le,
    ← ENNReal.ofReal_mul hCm_pos.le] at hlo_all
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlo_all
  have hS_lt : C_moran * (S.toReal + δ0) < loR := by
    calc C_moran * (S.toReal + δ0)
        = C_moran * ((S.toReal + c₀R) / 2) := by dsimp only [δ0]; ring
      _ < C_moran * c₀R := by nlinarith
      _ = loR / 2 := by dsimp only [c₀R]; field_simp
      _ < loR := by linarith
  linarith

/-- **Dimension Lower Bound Corollary (`s ≤ dimH (cfAlphabetSet A)`)**. -/
theorem le_dimH_of_transferOp_ge {A : Finset ℕ} (hAne : A.Nonempty)
    (ha1 : ∀ a ∈ A, 1 ≤ a) {s : ℝ} (hs : 0 < s)
    {v : ℝ → ℝ≥0∞} {lo hi : ℝ≥0∞} (hlo : 0 < lo) (hhi : hi < ⊤)
    (hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1, lo ≤ v x ∧ v x ≤ hi)
    (hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1, v x ≤ transferOp (A : Set ℕ) s v x) :
    ENNReal.ofReal s ≤ dimH (cfAlphabetSet (A : Set ℕ)) := by
  let d : ℝ≥0 := ⟨s, hs.le⟩
  have hmeas : μH[(d : ℝ)] (cfAlphabetSet (A : Set ℕ)) ≠ 0 :=
    (hausdorffMeasure_pos_of_transferOp_ge hAne ha1 hs hlo hhi hv_bd hsuper).ne'
  have hdim := le_dimH_of_hausdorffMeasure_ne_zero hmeas
  rw [← ENNReal.ofReal_coe_nnreal] at hdim
  exact hdim

/-! ### Part 4: Pure-Lean unconditional bounds (`1/2 < dimH F_{m,r}` and `dimH F_{4,1} ≤ 4/5`) -/

/-- For EVERY modulus `m ≥ 2` and residue `r ≥ 1`, `1 / 2 < dimH F_{m,r}` unconditionally. -/
theorem half_lt_dimH_residueConstSet {m r : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (1 / 2 : ℝ≥0∞) < dimH (residueConstSet m r) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  let C_hm : ℝ := (m : ℝ) + (r : ℝ) + 1
  have hC_pos : 0 < C_hm := by positivity
  have hdiv : Filter.Tendsto (fun K : ℕ =>
      ∑ k ∈ Finset.range K, 1 / ((m * k + r + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have hlow : ∀ K : ℕ,
        (1 / C_hm) * (∑ k ∈ Finset.range K, (1 : ℝ) / ((k : ℝ) + 1)) ≤
          ∑ k ∈ Finset.range K, 1 / ((m * k + r + 1 : ℕ) : ℝ) := by
      intro K
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hden_le : ((m * k + r + 1 : ℕ) : ℝ) ≤ C_hm * ((k : ℝ) + 1) := by
        push_cast; dsimp only [C_hm]; nlinarith
      have h1 : 1 / (C_hm * ((k : ℝ) + 1)) ≤ 1 / ((m * k + r + 1 : ℕ) : ℝ) :=
        one_div_le_one_div_of_le (by positivity) hden_le
      rwa [one_div_mul_one_div]
    exact Filter.tendsto_atTop_mono hlow
      (Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop (by positivity))
  obtain ⟨K, hK⟩ := (hdiv.eventually_ge_atTop (2 : ℝ)).exists
  let K₀ := max K 1
  have hK1 : 1 ≤ K₀ := le_max_right _ _
  have hsum_ge2 : (2 : ℝ) ≤ ∑ k ∈ Finset.range K₀, 1 / ((m * k + r + 1 : ℕ) : ℝ) := by
    by_cases hKz : K ≤ K₀
    · refine hK.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left K 1))
        fun k _ _ => by positivity)
    · exact False.elim (hKz (le_max_left K 1))
  let B : ℝ := ((m * K₀ + r + 1 : ℕ) : ℝ)
  have hB1 : 1 < B := by
    dsimp [B]; push_cast; nlinarith [show (1 : ℝ) ≤ (K₀ : ℝ) by exact_mod_cast hK1]
  have hcont : ContinuousAt (fun t : ℝ => B ^ (2 * t)) 0 :=
    (ContinuousAt.rpow continuousAt_const (continuous_const.mul continuous_id).continuousAt
      (Or.inl (by linarith))).comp continuousAt_id
  have h0_lt : B ^ ((2 : ℝ) * 0) < 2 := by norm_num
  have hev := hcont.eventually (Iio_mem_nhds h0_lt)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, hη_bd⟩ := hev
  let δ : ℝ := min (1 / 4) (η / 2)
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by linarith)
  have hB_le2 : B ^ (2 * δ) ≤ 2 := by
    refine le_of_lt (hη_bd ?_)
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let s : ℝ := 1 / 2 + δ
  have hs_pos : 0 < s := by dsimp [s]; positivity
  let A_fin : Finset ℕ := (Finset.range K₀).image (fun k => m * k + r)
  have hAne : A_fin.Nonempty := ⟨r, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hK1, by simp⟩⟩
  have ha1 : ∀ a ∈ A_fin, 1 ≤ a := by
    intro a ha
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
    omega
  have hinj : Function.Injective (fun k => m * k + r) := fun a b hab =>
    Nat.mul_left_cancel hm (Nat.add_right_cancel hab)
  have hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 : ℝ≥0∞) ≤ transferOp (A_fin : Set ℕ) s (fun _ => 1) x := by
    intro x hx
    unfold transferOp
    have hsum_fin : (∑ k ∈ Finset.range K₀,
        ENNReal.ofReal (((m * k + r : ℕ) + x) ^ (-(2 * s)))) ≤
        ∑' a : ℕ, if a ∈ (A_fin : Set ℕ) then
          1 * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))) else 0 := by
      have h_im : A_fin.sum (fun a : ℕ => ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))) =
          ∑ k ∈ Finset.range K₀, ENNReal.ofReal (((m * k + r : ℕ) + x) ^ (-(2 * s))) :=
        Finset.sum_image (fun a _ b _ hab => hinj hab)
      rw [← h_im]
      have hts := ENNReal.sum_le_tsum (A_fin)
        (f := fun a => if a ∈ (A_fin : Set ℕ) then
          1 * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))) else 0)
      refine le_trans ?_ hts
      refine Finset.sum_le_sum fun a ha => ?_
      simp [ha]
    have hterm_ge : ∀ k ∈ Finset.range K₀,
        1 / (2 * ((m * k + r + 1 : ℕ) : ℝ)) ≤ (((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := by
      intro k hk
      have hk_lt : k < K₀ := Finset.mem_range.mp hk
      have hbase_le : ((m * k + r : ℕ) : ℝ) + x ≤ ((m * k + r + 1 : ℕ) : ℝ) := by
        push_cast; linarith [hx.2]
      have hbase_pos : 0 < ((m * k + r : ℕ) : ℝ) + x := by
        have : (1 : ℝ) ≤ ((m * k + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m * k + r)
        linarith [hx.1]
      have hr1 : ((m * k + r + 1 : ℕ) : ℝ) ^ (-(2 * s)) ≤
          (((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
        Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (by dsimp [s]; linarith)
      have hr2 : ((m * k + r + 1 : ℕ) : ℝ) ^ (2 * s) =
          ((m * k + r + 1 : ℕ) : ℝ) * ((m * k + r + 1 : ℕ) : ℝ) ^ (2 * δ) := by
        have hpos1 : (0 : ℝ) < ((m * k + r + 1 : ℕ) : ℝ) := by positivity
        rw [show 2 * s = 1 + 2 * δ by dsimp [s]; ring, Real.rpow_add hpos1, Real.rpow_one]
      have hr3 : ((m * k + r + 1 : ℕ) : ℝ) ^ (2 * δ) ≤ B ^ (2 * δ) :=
        Real.rpow_le_rpow (by positivity)
          (by dsimp [B]; exact_mod_cast (by nlinarith : m * k + r + 1 ≤ m * K₀ + r + 1))
          (by positivity)
      have hr4 : ((m * k + r + 1 : ℕ) : ℝ) ^ (2 * s) ≤ 2 * ((m * k + r + 1 : ℕ) : ℝ) := by
        have : 0 ≤ ((m * k + r + 1 : ℕ) : ℝ) := by positivity
        nlinarith
      have hinv := one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _) hr4
      conv_rhs at hinv => rw [one_div, ← Real.rpow_neg (by positivity)]
      exact hinv.trans hr1
    have hsum_R : (1 : ℝ) ≤ ∑ k ∈ Finset.range K₀, (((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := by
      have h1 : (∑ k ∈ Finset.range K₀, 1 / (2 * ((m * k + r + 1 : ℕ) : ℝ))) =
          (1 / 2) * ∑ k ∈ Finset.range K₀, 1 / ((m * k + r + 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      have h2 := Finset.sum_le_sum hterm_ge
      linarith
    have hof : ENNReal.ofReal (1 : ℝ) ≤
        ∑ k ∈ Finset.range K₀, ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      have hnn : ∀ k ∈ Finset.range K₀, 0 ≤ (((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun k _ =>
        Real.rpow_nonneg (add_nonneg (Nat.cast_nonneg _) hx.1) _
      rw [← ENNReal.ofReal_sum_of_nonneg hnn]
      exact ENNReal.ofReal_le_ofReal hsum_R
    simpa using hof.trans hsum_fin
  have hdim_sub : ENNReal.ofReal s ≤ dimH (cfAlphabetSet (A_fin : Set ℕ)) :=
    le_dimH_of_transferOp_ge hAne ha1 hs_pos zero_lt_one ENNReal.one_lt_top
      (fun _ _ => ⟨le_rfl, le_rfl⟩) hsuper
  have hsub_F : cfAlphabetSet (A_fin : Set ℕ) ⊆ residueConstSet m r := by
    rintro x ⟨hx01, hirr, hadm⟩
    refine ⟨hx01, hirr, fun i => ?_⟩
    obtain ⟨k, _, hk_eq⟩ := Finset.mem_image.mp (Finset.mem_coe.mp (hadm i))
    rw [← hk_eq]
    refine ⟨Nat.le_add_left _ _, ?_⟩
    simp [Nat.add_mod, Nat.mul_mod_right]
  have hhalf_lt : (1 / 2 : ℝ≥0∞) < ENNReal.ofReal s := by
    have hhalf_eq : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
      rw [one_div, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [hhalf_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff hs_pos).mpr (by dsimp [s]; linarith)
  exact lt_of_lt_of_le hhalf_lt (hdim_sub.trans (dimH_mono hsub_F))

private lemma sum_Ico_sub_succ (F : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (F k - F (k + 1)) = F a - F b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

/-- Universal MVT telescoping bound for `t ↦ t ^ (-α)` (`α > 0`, `m > 0`) on `[t₀, t₀ + m]`. -/
lemma rpow_neg_step_bounds {t₀ m α : ℝ} (ht₀ : 0 < t₀) (hm : 0 < m) (hα : 0 < α) :
    (t₀ + m) ^ (-α - 1) ≤ (t₀ ^ (-α) - (t₀ + m) ^ (-α)) / (m * α) ∧
      (t₀ ^ (-α) - (t₀ + m) ^ (-α)) / (m * α) ≤ t₀ ^ (-α - 1) := by
  let f : ℝ → ℝ := fun t => - (t ^ (-α))
  let f' : ℝ → ℝ := fun t => α * t ^ (-α - 1)
  have hcont : ContinuousOn f (Set.Icc t₀ (t₀ + m)) := by
    refine ContinuousOn.neg ?_
    exact ContinuousOn.rpow continuousOn_id continuousOn_const
      fun t ht => Or.inl (by linarith [ht.1])
  have hderiv : ∀ t ∈ Set.Ioo t₀ (t₀ + m), HasDerivAt f (f' t) t := fun t ht => by
    have ht_pos : 0 < t := lt_of_lt_of_le ht₀ ht.1.le
    have hd := (Real.hasDerivAt_rpow_const (p := -α) (Or.inl ht_pos.ne')).neg
    convert hd using 1
    dsimp only [f']
    ring
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' (by linarith : t₀ < t₀ + m) hcont hderiv
  have hc_pos : 0 < c := lt_trans ht₀ hc.1
  have hf_sub : (f (t₀ + m) - f t₀) / ((t₀ + m) - t₀) =
      (t₀ ^ (-α) - (t₀ + m) ^ (-α)) / m := by
    dsimp only [f]
    ring
  rw [hf_sub] at hslope
  dsimp only [f'] at hslope
  have hdiv : (t₀ ^ (-α) - (t₀ + m) ^ (-α)) / (m * α) = c ^ (-α - 1) := by
    have hα0 : α ≠ 0 := hα.ne'
    rw [mul_comm m α, div_mul_eq_div_div_swap, div_eq_iff hα0]
    exact hslope.symm.trans (mul_comm _ _)
  rw [hdiv]
  constructor
  · exact Real.rpow_le_rpow_of_nonpos hc_pos hc.2.le (by linarith)
  · exact Real.rpow_le_rpow_of_nonpos ht₀ hc.1.le (by linarith)

/-- Exact infinite arithmetic tail upper bound via MVT telescoping. -/
theorem tsum_arith_tail_le {m r K : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r) (hK : 1 ≤ K)
    {s : ℝ} (hs : 1 / 2 < s) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑' k : ℕ, if K ≤ k then ENNReal.ofReal (((m * k + r : ℕ) + x) ^ (-(2 * s))) else 0) ≤
      ENNReal.ofReal ((((m * (K - 1) + r : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hα : 0 < 2 * s - 1 := by linarith
  have hterm : ∀ k ≥ K,
      ((m * k + r : ℕ) + x) ^ (-(2 * s)) ≤
        (((m * (k - 1) + r : ℕ) : ℝ) ^ (1 - 2 * s) -
          ((m * k + r : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)) := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans hK hk
    have ht₀ : 0 < ((m * (k - 1) + r : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < m * (k - 1) + r)
    have hadd : ((m * (k - 1) + r : ℕ) : ℝ) + (m : ℝ) = ((m * k + r : ℕ) : ℝ) := by
      have hn : m * (k - 1) + r + m = m * k + r := by
        calc m * (k - 1) + r + m = m * (k - 1 + 1) + r := by ring
          _ = m * k + r := by rw [Nat.sub_add_cancel hk1]
      exact_mod_cast hn
    have hb := (rpow_neg_step_bounds ht₀ hmR hα).1
    rw [hadd, show -(2 * s - 1) - 1 = -(2 * s) by ring,
      show -(2 * s - 1) = 1 - 2 * s by ring] at hb
    have hbase_ge : ((m * k + r : ℕ) : ℝ) ≤ (m * k + r : ℕ) + x := by linarith [hx.1]
    have hmono : ((m * k + r : ℕ) + x) ^ (-(2 * s)) ≤ ((m * k + r : ℕ) : ℝ) ^ (-(2 * s)) :=
      Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (by omega : 0 < m * k + r))
        hbase_ge (by linarith)
    exact hmono.trans hb
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  have hfin : (∑ i ∈ Finset.range N,
      if K ≤ i then ENNReal.ofReal (((m * i + r : ℕ) + x) ^ (-(2 * s))) else 0) ≤
      ENNReal.ofReal ((((m * (K - 1) + r : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) := by
    by_cases hNK : N ≤ K
    · have hz : ∀ i ∈ Finset.range N, ¬ K ≤ i := fun i hi => by
        have := Finset.mem_range.mp hi; omega
      have hzero : ∑ i ∈ Finset.range N,
          (if K ≤ i then ENNReal.ofReal (((m * i + r : ℕ) + x) ^ (-(2 * s))) else 0) = 0 :=
        Finset.sum_eq_zero fun i hi => by simp [hz i hi]
      rw [hzero]
      exact bot_le
    · have hKN : K ≤ N := by omega
      have hsplit : (∑ i ∈ Finset.range N,
          if K ≤ i then ENNReal.ofReal (((m * i + r : ℕ) + x) ^ (-(2 * s))) else 0) =
          ∑ i ∈ Finset.Ico K N, ENNReal.ofReal (((m * i + r : ℕ) + x) ^ (-(2 * s))) := by
        have hsub : (Finset.range N).filter (fun i => K ≤ i) = Finset.Ico K N := by
          ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
        rw [← Finset.sum_filter, hsub]
      rw [hsplit]
      have hnn : ∀ i : ℕ, 0 ≤ (((m * i + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun i =>
        Real.rpow_nonneg (add_nonneg (Nat.cast_nonneg _) hx.1) _
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hnn i]
      apply ENNReal.ofReal_le_ofReal
      let F : ℕ → ℝ := fun k => (((m * k + r : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))
      have hsum_tel : (∑ i ∈ Finset.Ico K N, (((m * i + r : ℕ) : ℝ) + x) ^ (-(2 * s))) ≤
          ∑ i ∈ Finset.Ico K N, (F (i - 1) - F i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have := hterm i (Finset.mem_Ico.mp hi).1
        dsimp only [F]
        rwa [← sub_div]
      have htel : (∑ i ∈ Finset.Ico K N, (F (i - 1) - F i)) = F (K - 1) - F (N - 1) := by
        have heq_range : ∑ i ∈ Finset.Ico K N, (F (i - 1) - F i) =
            ∑ j ∈ Finset.Ico (K - 1) (N - 1), (F j - F (j + 1)) := by
          refine Finset.sum_bij (fun i _ => i - 1) ?_ ?_ ?_ ?_
          · intro i hi
            have := Finset.mem_Ico.mp hi
            exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
          · intro a ha b hb hab
            have := Finset.mem_Ico.mp ha
            have := Finset.mem_Ico.mp hb
            omega
          · intro j hj
            have := Finset.mem_Ico.mp hj
            exact ⟨j + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro i hi
            have := Finset.mem_Ico.mp hi
            congr 2; omega
        rw [heq_range]
        exact sum_Ico_sub_succ F (by omega : K - 1 ≤ N - 1)
      have hFN_nn : 0 ≤ F (N - 1) := div_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
      linarith
  exact hfin

/-- Exact finite arithmetic tail lower bound via MVT telescoping. -/
theorem sum_arith_lower_ge {m r K Kmax : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r) (hKK : K ≤ Kmax)
    {s : ℝ} (hs : 1 / 2 < s) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (((((m * K + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) -
        (((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s))) / ((m : ℝ) * (2 * s - 1))) ≤
      ∑ k ∈ Finset.Ico K Kmax, ENNReal.ofReal (((m * k + r : ℕ) + x) ^ (-(2 * s))) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hα : 0 < 2 * s - 1 := by linarith
  have hnn : ∀ i : ℕ, 0 ≤ (((m * i + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun i =>
    Real.rpow_nonneg (add_nonneg (Nat.cast_nonneg _) hx.1) _
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hnn i]
  apply ENNReal.ofReal_le_ofReal
  let F : ℕ → ℝ := fun k => (((m * k + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))
  have hterm : ∀ k ∈ Finset.Ico K Kmax,
      F k - F (k + 1) ≤ (((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := by
    intro k _
    have ht₀ : 0 < ((m * k + r + 1 : ℕ) : ℝ) := by positivity
    have hadd : ((m * k + r + 1 : ℕ) : ℝ) + (m : ℝ) = ((m * (k + 1) + r + 1 : ℕ) : ℝ) := by
      push_cast; ring
    have hb := (rpow_neg_step_bounds ht₀ hmR hα).2
    rw [hadd, show -(2 * s - 1) - 1 = -(2 * s) by ring,
      show -(2 * s - 1) = 1 - 2 * s by ring] at hb
    have hbase_le : ((m * k + r : ℕ) : ℝ) + x ≤ ((m * k + r + 1 : ℕ) : ℝ) := by
      push_cast; linarith [hx.2]
    have hbase_pos : 0 < ((m * k + r : ℕ) : ℝ) + x := by
      have : (1 : ℝ) ≤ ((m * k + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m * k + r)
      linarith [hx.1]
    have hmono : ((m * k + r + 1 : ℕ) : ℝ) ^ (-(2 * s)) ≤
        (((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
      Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (by linarith)
    dsimp only [F]
    rw [← sub_div]
    exact hb.trans hmono
  have htel := sum_Ico_sub_succ F hKK
  calc ((((m * K + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) -
          (((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s))) / ((m : ℝ) * (2 * s - 1))
      = F K - F Kmax := by dsimp only [F]; ring
    _ = ∑ k ∈ Finset.Ico K Kmax, (F k - F (k + 1)) := htel.symm
    _ ≤ ∑ k ∈ Finset.Ico K Kmax, (((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
        Finset.sum_le_sum hterm

/-- **Pure-Lean Upper Dimension Certificate (`dimH F_{4,1} ≤ 4 / 5`)** via `v(x) = 1 / (1 + x)`. -/
theorem dimH_residueMod4_le_four_fifths :
    dimH (residueConstSet 4 1) ≤ ENNReal.ofReal (4 / 5) := by
  let v : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (1 / (1 + x))
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (1 / 2) ≤ v x ∧ v x ≤ ENNReal.ofReal 1 := by
    intro x hx
    exact ⟨ENNReal.ofReal_le_ofReal
        (one_div_le_one_div_of_le (by linarith [hx.1]) (by linarith [hx.2])),
      ENNReal.ofReal_le_ofReal ((div_le_one (by linarith [hx.1])).mpr (by linarith [hx.1]))⟩
  have hincr : ∀ (a : ℝ), 5 ≤ a → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 + x) * (a + x) ^ (-(8 / 5 : ℝ)) ≤ 2 * (a + 1) ^ (-(8 / 5 : ℝ)) := by
    intro a ha x hx
    let g : ℝ → ℝ := fun t => (1 + t) ^ 5 / (a + t) ^ 8
    have hcont : ContinuousOn g (Set.Icc 0 1) := by
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
      have : 0 < a + t := by linarith [ht.1]
      exact pow_ne_zero 8 this.ne'
    have hdiff : DifferentiableOn ℝ g (interior (Set.Icc 0 1)) := by
      intro t ht
      rw [interior_Icc] at ht
      have hpos : a + t ≠ 0 := by linarith [ht.1]
      exact ((((differentiableAt_const (1 : ℝ)).add differentiableAt_id).pow 5).div
        (((differentiableAt_const a).add differentiableAt_id).pow 8)
        (pow_ne_zero 8 hpos)).differentiableWithinAt
    have hmono : MonotoneOn g (Set.Icc 0 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcont hdiff fun t ht => ?_
      rw [interior_Icc] at ht
      have hden0 : a + t ≠ 0 := by linarith [ht.1]
      have hd1 : HasDerivAt (fun t : ℝ => (1 + t) ^ 5) (5 * (1 + t) ^ 4) t := by
        convert ((hasDerivAt_id' t).const_add (1 : ℝ)).pow 5 using 1
        ring
      have hd2 : HasDerivAt (fun t : ℝ => (a + t) ^ 8) (8 * (a + t) ^ 7) t := by
        convert ((hasDerivAt_id' t).const_add a).pow 8 using 1
        ring
      have hd_g : HasDerivAt g
          ((5 * (1 + t) ^ 4 * (a + t) ^ 8 - (1 + t) ^ 5 * (8 * (a + t) ^ 7)) / ((a + t) ^ 8) ^ 2)
          t :=
        hd1.div hd2 (pow_ne_zero 8 hden0)
      rw [hd_g.deriv]
      have hnum : 0 ≤ 5 * (1 + t) ^ 4 * (a + t) ^ 8 - (1 + t) ^ 5 * (8 * (a + t) ^ 7) := by
        have hfac : 5 * (1 + t) ^ 4 * (a + t) ^ 8 - (1 + t) ^ 5 * (8 * (a + t) ^ 7) =
            (1 + t) ^ 4 * (a + t) ^ 7 * (5 * a - 3 * t - 8) := by ring
        rw [hfac]
        have hat : 0 ≤ a + t := by linarith [ht.1]
        have hp1 : 0 ≤ (1 + t) ^ 4 := by positivity
        have hp2 : 0 ≤ (a + t) ^ 7 := by positivity
        have hp3 : 0 ≤ 5 * a - 3 * t - 8 := by linarith [ht.1, ht.2]
        positivity
      exact div_nonneg hnum (by positivity)
    have hgx := hmono hx (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) hx.2
    have hx_le : (1 + x) ^ 5 / (a + x) ^ 8 ≤ (2 : ℝ) ^ 5 / (a + 1) ^ 8 := by
      simpa [g, show (1 : ℝ) + 1 = 2 by norm_num] using hgx
    have hpow5 : ((1 + x) * (a + x) ^ (-(8 / 5 : ℝ))) ^ 5 ≤
        (2 * (a + 1) ^ (-(8 / 5 : ℝ))) ^ 5 := by
      have ha_x : 0 < a + x := by linarith [hx.1]
      have ha_1 : 0 < a + 1 := by linarith
      have hl : ((1 + x) * (a + x) ^ (-(8 / 5 : ℝ))) ^ 5 = (1 + x) ^ 5 / (a + x) ^ 8 := by
        rw [mul_pow, ← Real.rpow_natCast ((a + x) ^ (-(8 / 5 : ℝ))) 5,
          ← Real.rpow_mul ha_x.le]
        norm_num
        rw [div_eq_mul_inv]
      have hr : (2 * (a + 1) ^ (-(8 / 5 : ℝ))) ^ 5 = (2 : ℝ) ^ 5 / (a + 1) ^ 8 := by
        rw [mul_pow, ← Real.rpow_natCast ((a + 1) ^ (-(8 / 5 : ℝ))) 5,
          ← Real.rpow_mul ha_1.le]
        norm_num
        rw [div_eq_mul_inv]
      rw [hl, hr]
      exact hx_le
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow5
  have hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      transferOp {a : ℕ | 1 ≤ a ∧ a % 4 = 1 % 4} (4 / 5) v x ≤ v x := by
    intro x hx
    have hfactor : ∀ a : ℕ, 1 ≤ a →
        v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * (4 / 5 : ℝ)))) ≤
          v x * ENNReal.ofReal ((1 + x) * ((a : ℝ) + x) ^ (-(8 / 5 : ℝ))) := by
      intro a ha
      have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have h1x : 0 < 1 + x := by linarith [hx.1]
      have hax : 0 < (a : ℝ) + x := by linarith [hx.1]
      have hv_eq : v (1 / ((a : ℝ) + x)) =
          v x * ENNReal.ofReal ((1 + x) * ((a : ℝ) + x) / ((a : ℝ) + x + 1)) := by
        dsimp only [v]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      rw [hv_eq, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) bot_le
      have hratio : ((a : ℝ) + x) / ((a : ℝ) + x + 1) ≤ 1 :=
        (div_le_one (by linarith)).mpr (by linarith)
      have hmul1 : (1 + x) * ((a : ℝ) + x) / ((a : ℝ) + x + 1) ≤ 1 + x := by
        rw [mul_div_assoc]
        exact mul_le_of_le_one_right h1x.le hratio
      rw [show (2 * (4 / 5 : ℝ)) = 8 / 5 by norm_num]
      exact mul_le_mul_of_nonneg_right hmul1 (Real.rpow_nonneg hax.le _)
    have hsplit : transferOp {a : ℕ | 1 ≤ a ∧ a % 4 = 1 % 4} (4 / 5) v x =
        ∑' k : ℕ, v (1 / (((4 * k + 1 : ℕ) : ℝ) + x)) *
          ENNReal.ofReal ((((4 * k + 1 : ℕ) : ℝ) + x) ^ (-(2 * (4 / 5 : ℝ)))) := by
      let e : ℕ ≃ {a : ℕ // a ∈ {a : ℕ | 1 ≤ a ∧ a % 4 = 1 % 4}} :=
        { toFun := fun k => ⟨4 * k + 1, ⟨by omega, by simp [Nat.add_mod]⟩⟩
          invFun := fun a => a.1 / 4
          left_inv := fun k => by dsimp; rw [Nat.mul_add_div (by norm_num : 0 < 4)]; norm_num
          right_inv := fun a => Subtype.ext (by
            dsimp
            have hdiv := Nat.div_add_mod a.1 4
            have hm : a.1 % 4 = 1 := by simpa using a.2.2
            omega) }
      rw [transferOp_eq_tsum_subtype, ← Equiv.tsum_eq e
        (fun a => v (1 / ((a.1 : ℝ) + x)) *
          ENNReal.ofReal (((a.1 : ℝ) + x) ^ (-(2 * (4 / 5 : ℝ)))))]
      rfl
    let g : ℕ → ℝ≥0∞ := fun k =>
      v (1 / (((4 * k + 1 : ℕ) : ℝ) + x)) *
        ENNReal.ofReal ((((4 * k + 1 : ℕ) : ℝ) + x) ^ (-(2 * (4 / 5 : ℝ))))
    have hsep3 : (∑' k : ℕ, g k) = g 0 + (g 1 + ∑' k : ℕ, if 2 ≤ k then g k else 0) := by
      rw [ENNReal.tsum_eq_add_tsum_ite (0 : ℕ) (f := g)]
      congr 1
      let f1 : ℕ → ℝ≥0∞ := fun k => if k = 0 then 0 else g k
      have h1 := ENNReal.tsum_eq_add_tsum_ite (1 : ℕ) (f := f1)
      simp only [f1, show (1 : ℕ) ≠ 0 by omega, ↓reduceIte] at h1
      calc _ = ∑' k : ℕ, f1 k := tsum_congr fun k => by by_cases hk : k = 0 <;> simp [f1, hk]
        _ = g 1 + ∑' k : ℕ, if k = 1 then 0 else f1 k := h1
        _ = g 1 + ∑' k : ℕ, if 2 ≤ k then g k else 0 := by
            congr 1
            refine tsum_congr fun k => ?_
            by_cases h0k : k = 0 <;> by_cases h1k : k = 1
            · omega
            · simp [f1, h0k]
            · simp [f1, h1k]
            · have h2k : 2 ≤ k := by omega
              simp [f1, h0k, h1k, h2k]
    rw [hsplit]
    change (∑' k : ℕ, g k) ≤ v x
    rw [hsep3]
    dsimp only [g]
    have ht0 : v (1 / (((4 * 0 + 1 : ℕ) : ℝ) + x)) *
        ENNReal.ofReal ((((4 * 0 + 1 : ℕ) : ℝ) + x) ^ (-(2 * (4 / 5 : ℝ)))) ≤
        v x * ENNReal.ofReal (1 / 2) := by
      have h1x : 0 < 1 + x := by linarith [hx.1]
      have hax : ((4 * 0 + 1 : ℕ) : ℝ) + x = 1 + x := by norm_num
      rw [hax]
      have hv0 : v (1 / (1 + x)) * ENNReal.ofReal ((1 + x) ^ (-(2 * (4 / 5 : ℝ)))) =
          v x * ENNReal.ofReal ((1 + x) ^ (2 / 5 : ℝ) / (2 + x)) := by
        dsimp only [v]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have halg1 : (1 / (1 + (1 / (1 + x)))) * (1 + x) ^ (-(2 * (4 / 5 : ℝ))) =
            ((1 + x) / (2 + x)) * (1 + x) ^ (-(8 / 5 : ℝ)) := by
          have h1x0 : 1 + x ≠ 0 := h1x.ne'
          have h2x0 : 2 + x ≠ 0 := by linarith [hx.1]
          congr 1
          · field_simp [h1x0, h2x0]; ring
          · congr 1; ring
        have halg2 : (1 / (1 + x)) * ((1 + x) ^ (2 / 5 : ℝ) / (2 + x)) =
            ((1 + x) / (2 + x)) * (1 + x) ^ (-(8 / 5 : ℝ)) := by
          have hadd : (1 + x) ^ (2 / 5 : ℝ) * (1 + x) ^ (-1 : ℝ) = (1 + x) ^ (-(3 / 5 : ℝ)) := by
            rw [← Real.rpow_add h1x]; congr 1; norm_num
          have hadd2 : (1 + x) * (1 + x) ^ (-(8 / 5 : ℝ)) = (1 + x) ^ (-(3 / 5 : ℝ)) := by
            calc (1 + x) * (1 + x) ^ (-(8 / 5 : ℝ))
                = (1 + x) ^ (1 : ℝ) * (1 + x) ^ (-(8 / 5 : ℝ)) := by rw [Real.rpow_one]
              _ = (1 + x) ^ ((1 : ℝ) + -(8 / 5 : ℝ)) := (Real.rpow_add h1x _ _).symm
              _ = (1 + x) ^ (-(3 / 5 : ℝ)) := by congr 1; norm_num
          rw [Real.rpow_neg_one] at hadd
          calc (1 / (1 + x)) * ((1 + x) ^ (2 / 5 : ℝ) / (2 + x))
              = ((1 + x) ^ (2 / 5 : ℝ) * (1 + x)⁻¹) / (2 + x) := by ring
            _ = (1 + x) ^ (-(3 / 5 : ℝ)) / (2 + x) := by rw [hadd]
            _ = ((1 + x) * (1 + x) ^ (-(8 / 5 : ℝ))) / (2 + x) := by rw [hadd2]
            _ = ((1 + x) / (2 + x)) * (1 + x) ^ (-(8 / 5 : ℝ)) := by ring
        rw [halg1, halg2]
      rw [hv0]
      refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) bot_le
      have hpoly : (1 + x) ^ 2 * 32 ≤ (2 + x) ^ 5 := by
        have hx0 : 0 ≤ x := hx.1
        have hdiff : (2 + x) ^ 5 - (1 + x) ^ 2 * 32 =
            16 * x + 48 * x ^ 2 + 40 * x ^ 3 + 10 * x ^ 4 + x ^ 5 := by ring
        have hd_nn : 0 ≤ (2 + x) ^ 5 - (1 + x) ^ 2 * 32 := by rw [hdiff]; positivity
        linarith
      have hpow5 : ((1 + x) ^ (2 / 5 : ℝ) / (2 + x)) ^ 5 ≤ (1 / 2 : ℝ) ^ 5 := by
        rw [div_pow, ← Real.rpow_natCast ((1 + x) ^ (2 / 5 : ℝ)) 5, ← Real.rpow_mul h1x.le]
        norm_num
        rw [div_le_iff₀ (pow_pos (by linarith [hx.1]) 5)]
        linarith
      exact le_of_pow_le_pow_left₀ (n := 5) (by norm_num) (by positivity) hpow5
    have ht1 : v (1 / (((4 * 1 + 1 : ℕ) : ℝ) + x)) *
        ENNReal.ofReal ((((4 * 1 + 1 : ℕ) : ℝ) + x) ^ (-(2 * (4 / 5 : ℝ)))) ≤
        v x * ENNReal.ofReal (1 / 8) := by
      refine le_trans (hfactor 5 (by norm_num))
        (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) bot_le)
      have hi1 := hincr 5 le_rfl x hx
      have hnum : (2 : ℝ) * (5 + 1 : ℝ) ^ (-(8 / 5 : ℝ)) ≤ 1 / 8 := by
        have hpow5 : ((2 : ℝ) * (6 : ℝ) ^ (-(8 / 5 : ℝ))) ^ 5 ≤ (1 / 8 : ℝ) ^ 5 := by
          rw [mul_pow, ← Real.rpow_natCast ((6 : ℝ) ^ (-(8 / 5 : ℝ))) 5,
            ← Real.rpow_mul (by norm_num)]
          norm_num
        exact le_of_pow_le_pow_left₀ (n := 5) (by norm_num) (by positivity)
          (by simpa [show (5 + 1 : ℝ) = 6 by norm_num] using hpow5)
      exact hi1.trans (by simpa using hnum)
    have htail2 : (∑' k : ℕ, if 2 ≤ k then
        v (1 / (((4 * k + 1 : ℕ) : ℝ) + x)) *
          ENNReal.ofReal ((((4 * k + 1 : ℕ) : ℝ) + x) ^ (-(2 * (4 / 5 : ℝ)))) else 0) ≤
        v x * ENNReal.ofReal (3 / 10) := by
      have hbd_k : ∀ k : ℕ, (if 2 ≤ k then
          v (1 / (((4 * k + 1 : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((4 * k + 1 : ℕ) : ℝ) + x) ^ (-(2 * (4 / 5 : ℝ)))) else 0) ≤
          v x * (ENNReal.ofReal 2 * (if 2 ≤ k then
            ENNReal.ofReal ((((4 * k + 2 : ℕ) : ℝ) + 0) ^ (-(2 * (4 / 5 : ℝ)))) else 0)) := by
        intro k
        split_ifs with hk
        · have hf1 := hfactor (4 * k + 1) (by omega)
          have ha5 : (5 : ℝ) ≤ ((4 * k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 5 ≤ 4 * k + 1)
          have hin := hincr _ ha5 x hx
          have hl2 : v x * ENNReal.ofReal ((1 + x) * ((4 * k + 1 : ℕ) + x) ^ (-(8 / 5 : ℝ))) ≤
              v x * (ENNReal.ofReal 2 *
                ENNReal.ofReal ((((4 * k + 2 : ℕ) : ℝ) + 0) ^ (-(2 * (4 / 5 : ℝ))))) := by
            conv_rhs => rw [← ENNReal.ofReal_mul (by norm_num)]
            refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) bot_le
            rw [show (((4 * k + 2 : ℕ) : ℝ) + 0) = ((4 * k + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
              show -(2 * (4 / 5 : ℝ)) = -(8 / 5 : ℝ) by norm_num]
            exact hin
          exact hf1.trans hl2
        · simp
      have htsum_k := ENNReal.tsum_le_tsum hbd_k
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left] at htsum_k
      have htail := tsum_arith_tail_le (m := 4) (r := 2) (K := 2)
        (by omega) (by omega) (by omega) (s := 4 / 5) (by norm_num) (x := 0) ⟨le_rfl, zero_le_one⟩
      have hnum : (2 : ℝ) * ((((4 * (2 - 1) + 2 : ℕ) : ℝ) ^ (1 - 2 * (4 / 5 : ℝ))) /
          ((4 : ℝ) * (2 * (4 / 5 : ℝ) - 1))) ≤ 3 / 10 := by
        have hsimpl : (2 : ℝ) * ((((4 * (2 - 1) + 2 : ℕ) : ℝ) ^ (1 - 2 * (4 / 5 : ℝ))) /
            ((4 : ℝ) * (2 * (4 / 5 : ℝ) - 1))) = (5 / 6 : ℝ) * (6 : ℝ) ^ (-(3 / 5 : ℝ)) := by
          norm_num; ring
        rw [hsimpl]
        have hpow5 : ((5 / 6 : ℝ) * (6 : ℝ) ^ (-(3 / 5 : ℝ))) ^ 5 ≤ (3 / 10 : ℝ) ^ 5 := by
          rw [mul_pow, ← Real.rpow_natCast ((6 : ℝ) ^ (-(3 / 5 : ℝ))) 5,
            ← Real.rpow_mul (by norm_num)]
          norm_num
        exact le_of_pow_le_pow_left₀ (n := 5) (by norm_num) (by positivity) hpow5
      calc (∑' k : ℕ, if 2 ≤ k then _ else 0)
          ≤ v x * (ENNReal.ofReal 2 * ∑' k : ℕ, if 2 ≤ k then _ else 0) := htsum_k
        _ ≤ v x * (ENNReal.ofReal 2 * ENNReal.ofReal
              ((((4 * (2 - 1) + 2 : ℕ) : ℝ) ^ (1 - 2 * (4 / 5 : ℝ))) /
                ((4 : ℝ) * (2 * (4 / 5 : ℝ) - 1)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail bot_le) bot_le
        _ ≤ v x * ENNReal.ofReal (3 / 10) := by
            rw [← ENNReal.ofReal_mul (by norm_num)]
            exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hnum) bot_le
    calc _ ≤ v x * ENNReal.ofReal (1 / 2) +
            (v x * ENNReal.ofReal (1 / 8) + v x * ENNReal.ofReal (3 / 10)) :=
          add_le_add ht0 (add_le_add ht1 htail2)
      _ = v x * (ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 8) +
            ENNReal.ofReal (3 / 10)) := by ring
      _ = v x * ENNReal.ofReal (1 / 2 + 1 / 8 + 3 / 10) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      _ ≤ v x * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          norm_num
      _ = v x := mul_one _
  rw [← cfAlphabetSet_eq_residueConstSet]
  exact dimH_le_of_transferOp_le (fun _ ha => ha.1) (by norm_num : (0 : ℝ) < 4 / 5)
    (ENNReal.ofReal_pos.mpr (by norm_num)) ENNReal.ofReal_lt_top hv_bd hsub

/-! ### Part 5: Uniform-grid step-vector + integral-tail certificate soundness -/

/-- Bin index of `x ∈ [0, 1]` on a uniform `N`-partition (`1 ≤ N`). -/
def binOf (N : ℕ) (hN : 1 ≤ N) (x : ℝ) : Fin N :=
  ⟨min (N - 1) (Nat.floor ((N : ℝ) * x)), by omega⟩

/-- Left and right cell endpoints `binOf (1 / (a + (j+1)/N))` and `binOf (1 / (a + j/N))`. -/
def binLeft (N : ℕ) (hN : 1 ≤ N) (a : ℕ) (j : Fin N) : Fin N :=
  binOf N hN (1 / ((a : ℝ) + ((j.1 : ℝ) + 1) / (N : ℝ)))

def binRight (N : ℕ) (hN : 1 ≤ N) (a : ℕ) (j : Fin N) : Fin N :=
  binOf N hN (1 / ((a : ℝ) + (j.1 : ℝ) / (N : ℝ)))

lemma binOf_cell_bounds (N : ℕ) (hN : 1 ≤ N) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((binOf N hN x).1 : ℝ) / (N : ℝ) ≤ x ∧
      x ≤ (((binOf N hN x).1 : ℝ) + 1) / (N : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  dsimp only [binOf]
  by_cases hfl : Nat.floor ((N : ℝ) * x) ≤ N - 1
  · rw [min_eq_right hfl]
    have hlo : (Nat.floor ((N : ℝ) * x) : ℝ) ≤ x * (N : ℝ) := by
      rw [mul_comm x (N : ℝ)]; exact Nat.floor_le (mul_nonneg hNR.le hx.1)
    have hhi : x * (N : ℝ) < (Nat.floor ((N : ℝ) * x) : ℝ) + 1 := by
      rw [mul_comm x (N : ℝ)]; exact Nat.lt_floor_add_one _
    exact ⟨(div_le_iff₀ hNR).mpr hlo, (le_div_iff₀ hNR).mpr hhi.le⟩
  · have hge : N - 1 ≤ Nat.floor ((N : ℝ) * x) := by omega
    rw [min_eq_left hge]
    have hNx : (N : ℝ) - 1 ≤ x * (N : ℝ) := by
      have h1 : (N - 1 : ℕ) ≤ Nat.floor ((N : ℝ) * x) := hge
      have h2 := le_trans (by exact_mod_cast h1 : ((N - 1 : ℕ) : ℝ) ≤ (Nat.floor ((N : ℝ) * x) : ℝ))
        (Nat.floor_le (mul_nonneg hNR.le hx.1))
      rw [Nat.cast_sub hN, Nat.cast_one] at h2
      linarith
    have hsub1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub hN, Nat.cast_one]
    have htop : x * (N : ℝ) ≤ ((N : ℝ) - 1) + 1 := by nlinarith [hx.2, hNR]
    rw [hsub1]
    exact ⟨(div_le_iff₀ hNR).mpr hNx, (le_div_iff₀ hNR).mpr htop⟩

lemma binOf_mono (N : ℕ) (hN : 1 ≤ N) {x y : ℝ} (hxy : x ≤ y) :
    binOf N hN x ≤ binOf N hN y := by
  dsimp only [binOf]
  change min (N - 1) (Nat.floor ((N : ℝ) * x)) ≤ min (N - 1) (Nat.floor ((N : ℝ) * y))
  exact min_le_min le_rfl (Nat.floor_mono (mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg N)))

lemma binOf_tail_eq_zero {N a : ℕ} (hN : 1 ≤ N) (ha : N + 1 ≤ a) {x : ℝ} (hx : 0 ≤ x) :
    binOf N hN (1 / ((a : ℝ) + x)) = ⟨0, hN⟩ := by
  have haR : ((N : ℝ) + 1) ≤ (a : ℝ) := by exact_mod_cast ha
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hax : 0 < (a : ℝ) + x := by linarith
  have hlt1 : (N : ℝ) * (1 / ((a : ℝ) + x)) < 1 := by
    rw [mul_one_div, div_lt_one hax]
    linarith
  have hfl0 : Nat.floor ((N : ℝ) * (1 / ((a : ℝ) + x))) = 0 :=
    Nat.floor_eq_zero.mpr hlt1
  ext
  change min (N - 1) (Nat.floor ((N : ℝ) * (1 / ((a : ℝ) + x)))) = 0
  rw [hfl0]
  exact Nat.min_zero _

/-- Piecewise-constant grid function on `[0, 1]`. -/
def stepVec (N : ℕ) (hN : 1 ≤ N) (v : Fin N → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  v (binOf N hN x)

/-- **Upper Grid Certificate Soundness**: validates `certify_side(..., "upper")` in
    `verification/residue_certificate.py` and `residue_certificate_general.py`. -/
theorem step_cert_upper_sound {m r K N : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r) (hK : 1 ≤ K) (hN : 1 ≤ N)
    (hcut : N + 1 ≤ m * K + r) {s : ℝ} (hs : 1 / 2 < s)
    (v : Fin N → ℝ≥0∞) (hv_pos : ∀ j, 0 < v j) (hv_top : ∀ j, v j < ⊤)
    (v_hi : Fin N → ℕ → ℝ≥0∞)
    (h_hi : ∀ j : Fin N, ∀ k < K, ∀ i : Fin N,
      binLeft N hN (m * k + r) j ≤ i → i ≤ binRight N hN (m * k + r) j → v i ≤ v_hi j k)
    (hcert : ∀ j : Fin N,
      (∑ k ∈ Finset.range K,
          v_hi j k * ENNReal.ofReal (((m * k + r : ℕ) + (j.1 : ℝ) / (N : ℝ)) ^ (-(2 * s)))) +
        v ⟨0, hN⟩ *
          ENNReal.ofReal ((((m * (K - 1) + r : ℕ) : ℝ) ^ (1 - 2 * s)) /
            ((m : ℝ) * (2 * s - 1))) ≤ v j) :
    dimH (residueConstSet m r) ≤ ENNReal.ofReal s := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hlo : 0 < Finset.univ.inf' Finset.univ_nonempty v :=
    (Finset.lt_inf'_iff _).mpr fun j _ => hv_pos j
  have hhi : Finset.univ.sup' Finset.univ_nonempty v < ⊤ :=
    (Finset.sup'_lt_iff _).mpr fun j _ => hv_top j
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Finset.univ.inf' Finset.univ_nonempty v ≤ stepVec N hN v x ∧
        stepVec N hN v x ≤ Finset.univ.sup' Finset.univ_nonempty v := fun x _ =>
    ⟨Finset.inf'_le v (Finset.mem_univ _), Finset.le_sup' v (Finset.mem_univ _)⟩
  have hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      transferOp {a : ℕ | r ≤ a ∧ a % m = r % m} s (stepVec N hN v) x ≤ stepVec N hN v x := by
    intro x hx
    set j := binOf N hN x
    have hcell := binOf_cell_bounds N hN hx
    have hsplit : transferOp {a : ℕ | r ≤ a ∧ a % m = r % m} s (stepVec N hN v) x =
        (∑ k ∈ Finset.range K,
          stepVec N hN v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) +
        ∑' k : ℕ, if K ≤ k then
          stepVec N hN v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0 := by
      let e : ℕ ≃ {a : ℕ // a ∈ {a : ℕ | r ≤ a ∧ a % m = r % m}} :=
        { toFun := fun k =>
            ⟨m * k + r, ⟨Nat.le_add_left _ _, by simp [Nat.add_mod, Nat.mul_mod_right]⟩⟩
          invFun := fun a => (a.1 - r) / m
          left_inv := fun k => by dsimp; rw [Nat.add_sub_cancel]; exact Nat.mul_div_right k hm
          right_inv := fun a => Subtype.ext (by
            dsimp
            have h1 := a.2.1
            have h2 := a.2.2
            have hdiv1 := Nat.div_add_mod a.1 m
            have hdiv2 := Nat.div_add_mod r m
            have hmq : m * (r / m) ≤ m * (a.1 / m) := by omega
            have hle_q : r / m ≤ a.1 / m := Nat.le_of_mul_le_mul_left hmq hm
            have hsub_eq : a.1 - r = m * (a.1 / m - r / m) := by
              rw [Nat.mul_sub_left_distrib]; omega
            rw [hsub_eq, Nat.mul_div_right _ hm]; omega) }
      let f : ℕ → ℝ≥0∞ := fun a =>
        stepVec N hN v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))
      rw [transferOp_eq_tsum_subtype, ← Equiv.tsum_eq e (fun a => f a.1)]
      have hsep : ∀ K₀ : ℕ, ∀ g : ℕ → ℝ≥0∞, (∑' k : ℕ, g k) =
          (∑ k ∈ Finset.range K₀, g k) + ∑' k : ℕ, if K₀ ≤ k then g k else 0 := by
        intro K₀ g
        induction K₀ with
        | zero => simp
        | succ K₀ ih =>
          rw [Finset.sum_range_succ, add_assoc]
          refine ih.trans (congrArg _ ?_)
          have hstep := ENNReal.tsum_eq_add_tsum_ite K₀
            (f := fun k => if K₀ ≤ k then g k else 0)
          simp only [le_rfl, ↓reduceIte] at hstep
          refine hstep.trans (congrArg _ (tsum_congr fun k => ?_))
          split_ifs <;> first | exact False.elim (by omega) | rfl
      exact hsep K fun k => f (m * k + r)
    have hhead : (∑ k ∈ Finset.range K,
          stepVec N hN v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) ≤
        ∑ k ∈ Finset.range K,
          v_hi j k * ENNReal.ofReal (((m * k + r : ℕ) + (j.1 : ℝ) / (N : ℝ)) ^ (-(2 * s))) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk_lt : k < K := Finset.mem_range.mp hk
      have ha1 : 1 ≤ m * k + r := by omega
      have haR : (1 : ℝ) ≤ ((m * k + r : ℕ) : ℝ) := by exact_mod_cast ha1
      have hL : binLeft N hN (m * k + r) j ≤ binOf N hN (1 / (((m * k + r : ℕ) : ℝ) + x)) :=
        binOf_mono N hN (one_div_le_one_div_of_le (by linarith [hx.1]) (by linarith [hcell.2]))
      have hR : binOf N hN (1 / (((m * k + r : ℕ) : ℝ) + x)) ≤ binRight N hN (m * k + r) j :=
        binOf_mono N hN (one_div_le_one_div_of_le (by positivity) (by linarith [hcell.1]))
      have hv_le := h_hi j k hk_lt _ hL hR
      have hj_pos : 0 < ((m * k + r : ℕ) : ℝ) + (j.1 : ℝ) / (N : ℝ) := by positivity
      have hrpow : (((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)) ≤
          (((m * k + r : ℕ) : ℝ) + (j.1 : ℝ) / (N : ℝ)) ^ (-(2 * s)) :=
        Real.rpow_le_rpow_of_nonpos hj_pos (by linarith [hcell.1]) (by linarith : -(2 * s) ≤ 0)
      exact mul_le_mul' hv_le (ENNReal.ofReal_le_ofReal hrpow)
    have htail : (∑' k : ℕ, if K ≤ k then
          stepVec N hN v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0) ≤
        v ⟨0, hN⟩ * ENNReal.ofReal ((((m * (K - 1) + r : ℕ) : ℝ) ^ (1 - 2 * s)) /
          ((m : ℝ) * (2 * s - 1))) := by
      have hzero : ∀ k : ℕ, (if K ≤ k then
          stepVec N hN v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0) =
          v ⟨0, hN⟩ *
            (if K ≤ k then ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0) := by
        intro k
        split_ifs with hk
        · have hk_cut : N + 1 ≤ m * k + r := le_trans hcut (by nlinarith)
          simp only [stepVec, binOf_tail_eq_zero hN hk_cut hx.1]
        · simp
      simp_rw [hzero, ENNReal.tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (tsum_arith_tail_le hm hr hK hs hx) bot_le
    rw [hsplit]
    exact (add_le_add hhead htail).trans (hcert j)
  rw [← cfAlphabetSet_eq_residueConstSet]
  exact dimH_le_of_transferOp_le (fun _ ha => le_trans hr ha.1)
    (by linarith : 0 < s) hlo hhi hv_bd hsub

/-- **Lower Grid Certificate Soundness**: validates `certify_side(..., "lower")` in
    `verification/residue_certificate.py` and `residue_certificate_general.py`. -/
theorem step_cert_lower_sound {m r K Kmax N : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r) (hK : 1 ≤ K)
    (hKK : K ≤ Kmax) (hN : 1 ≤ N) (hcut : N + 1 ≤ m * K + r) {s : ℝ} (hs : 1 / 2 < s)
    (v : Fin N → ℝ≥0∞) (hv_pos : ∀ j, 0 < v j) (hv_top : ∀ j, v j < ⊤)
    (v_lo : Fin N → ℕ → ℝ≥0∞)
    (h_lo : ∀ j : Fin N, ∀ k < K, ∀ i : Fin N,
      binLeft N hN (m * k + r) j ≤ i → i ≤ binRight N hN (m * k + r) j → v_lo j k ≤ v i)
    (hcert : ∀ j : Fin N, v j ≤
      (∑ k ∈ Finset.range K,
          v_lo j k * ENNReal.ofReal (((m * k + r : ℕ) + ((j.1 : ℝ) + 1) / (N : ℝ)) ^ (-(2 * s)))) +
        v ⟨0, hN⟩ *
          ENNReal.ofReal (((((m * K + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) -
            (((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s))) / ((m : ℝ) * (2 * s - 1)))) :
    ENNReal.ofReal s ≤ dimH (residueConstSet m r) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let A_fin : Finset ℕ := (Finset.range Kmax).image (fun k => m * k + r)
  have hAne : A_fin.Nonempty :=
    ⟨r, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩⟩
  have ha1 : ∀ a ∈ A_fin, 1 ≤ a := by
    intro a ha
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
    omega
  have hinj : Function.Injective (fun k => m * k + r) := fun a b hab =>
    Nat.mul_left_cancel hm (Nat.add_right_cancel hab)
  have hlo : 0 < Finset.univ.inf' Finset.univ_nonempty v :=
    (Finset.lt_inf'_iff _).mpr fun j _ => hv_pos j
  have hhi : Finset.univ.sup' Finset.univ_nonempty v < ⊤ :=
    (Finset.sup'_lt_iff _).mpr fun j _ => hv_top j
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Finset.univ.inf' Finset.univ_nonempty v ≤ stepVec N hN v x ∧
        stepVec N hN v x ≤ Finset.univ.sup' Finset.univ_nonempty v := fun x _ =>
    ⟨Finset.inf'_le v (Finset.mem_univ _), Finset.le_sup' v (Finset.mem_univ _)⟩
  have hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      stepVec N hN v x ≤ transferOp (A_fin : Set ℕ) s (stepVec N hN v) x := by
    intro x hx
    set j := binOf N hN x
    have hcell := binOf_cell_bounds N hN hx
    have hsplit : (∑ k ∈ Finset.range K,
          stepVec N hN v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) +
        (∑ k ∈ Finset.Ico K Kmax,
          stepVec N hN v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) ≤
        transferOp (A_fin : Set ℕ) s (stepVec N hN v) x := by
      conv_lhs => rw [← Nat.Ico_zero_eq_range]
      rw [Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKK]
      have h_im : A_fin.sum (fun a : ℕ =>
          stepVec N hN v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))) =
          ∑ k ∈ Finset.range Kmax,
            stepVec N hN v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
              ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) :=
        Finset.sum_image (fun a _ b _ hab => hinj hab)
      rw [Nat.Ico_zero_eq_range, ← h_im]
      unfold transferOp
      refine le_trans ?_ (ENNReal.sum_le_tsum A_fin)
      refine Finset.sum_le_sum fun a ha => ?_
      simp [ha]
    have hhead : (∑ k ∈ Finset.range K,
          v_lo j k * ENNReal.ofReal (((m * k + r : ℕ) + ((j.1 : ℝ) + 1) / (N : ℝ)) ^ (-(2 * s)))) ≤
        ∑ k ∈ Finset.range K,
          stepVec N hN v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk_lt : k < K := Finset.mem_range.mp hk
      have ha1 : 1 ≤ m * k + r := by omega
      have haR : (1 : ℝ) ≤ ((m * k + r : ℕ) : ℝ) := by exact_mod_cast ha1
      have hL : binLeft N hN (m * k + r) j ≤ binOf N hN (1 / (((m * k + r : ℕ) : ℝ) + x)) :=
        binOf_mono N hN (one_div_le_one_div_of_le (by linarith [hx.1]) (by linarith [hcell.2]))
      have hR : binOf N hN (1 / (((m * k + r : ℕ) : ℝ) + x)) ≤ binRight N hN (m * k + r) j :=
        binOf_mono N hN (one_div_le_one_div_of_le (by positivity) (by linarith [hcell.1]))
      have hv_le := h_lo j k hk_lt _ hL hR
      have hax_pos : 0 < ((m * k + r : ℕ) : ℝ) + x := by linarith [hx.1]
      have hrpow : (((m * k + r : ℕ) : ℝ) + ((j.1 : ℝ) + 1) / (N : ℝ)) ^ (-(2 * s)) ≤
          (((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
        Real.rpow_le_rpow_of_nonpos hax_pos (by linarith [hcell.2]) (by linarith : -(2 * s) ≤ 0)
      exact mul_le_mul' hv_le (ENNReal.ofReal_le_ofReal hrpow)
    have htail : v ⟨0, hN⟩ *
          ENNReal.ofReal (((((m * K + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) -
            (((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s))) / ((m : ℝ) * (2 * s - 1))) ≤
        ∑ k ∈ Finset.Ico K Kmax,
          stepVec N hN v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      have heq_t : (∑ k ∈ Finset.Ico K Kmax,
          stepVec N hN v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
          v ⟨0, hN⟩ * ∑ k ∈ Finset.Ico K Kmax,
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk_cut : N + 1 ≤ m * k + r :=
          le_trans hcut (by have := (Finset.mem_Ico.mp hk).1; nlinarith)
        simp only [stepVec, binOf_tail_eq_zero hN hk_cut hx.1]
      rw [heq_t]
      exact mul_le_mul_of_nonneg_left (sum_arith_lower_ge hm hr hKK hs hx) bot_le
    exact (hcert j).trans ((add_le_add hhead htail).trans hsplit)
  have hdim_sub := le_dimH_of_transferOp_ge hAne ha1 (by linarith : 0 < s) hlo hhi hv_bd hsuper
  have hsub_F : cfAlphabetSet (A_fin : Set ℕ) ⊆ residueConstSet m r := by
    rintro x ⟨hx01, hirr, hadm⟩
    refine ⟨hx01, hirr, fun i => ?_⟩
    obtain ⟨k, _, hk_eq⟩ := Finset.mem_image.mp (Finset.mem_coe.mp (hadm i))
    rw [← hk_eq]
    exact ⟨Nat.le_add_left _ _, by simp [Nat.add_mod, Nat.mul_mod_right]⟩
  exact hdim_sub.trans (dimH_mono hsub_F)

end

end TransferOperatorDim

#print axioms TransferOperatorDim.hausdorffMeasure_le_of_transferOp_le
#print axioms TransferOperatorDim.dimH_le_of_transferOp_le
#print axioms TransferOperatorDim.isCompact_cfAlphabetSet
#print axioms TransferOperatorDim.hausdorffMeasure_pos_of_transferOp_ge
#print axioms TransferOperatorDim.le_dimH_of_transferOp_ge
#print axioms TransferOperatorDim.half_lt_dimH_residueConstSet
#print axioms TransferOperatorDim.tsum_arith_tail_le
#print axioms TransferOperatorDim.sum_arith_lower_ge
#print axioms TransferOperatorDim.dimH_residueMod4_le_four_fifths
#print axioms TransferOperatorDim.step_cert_upper_sound
#print axioms TransferOperatorDim.step_cert_lower_sound

