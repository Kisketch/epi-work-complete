import EpiFormal.ResidueAsymptotic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Multi-Residue Continued-Fraction Phase Transition, Bowen-Free Poincaré Abscissa,
# Euler–Mascheroni Three-Term Asymptotics, and Supercritical Power-Law Rate

Generalizes `ResidueAsymptotic.lean` (Paper 2 Track 2C) from single positive residue
alphabets `F_{m,r}` (`a_i ≡ r (mod m)`) to arbitrary finite-union multi-residue alphabets
`multiResidueSet m S B` (`a_i ≡ r (mod m)` for `r ∈ S`, or `a_i ≡ -b (mod m)` for `b ∈ B`)
and sharpens the asymptotic expansion from two terms (`O(1/m^2)`) to three exact terms
(`O((log m)^2 / m^3)`) involving the Euler–Mascheroni constant `Real.eulerMascheroniConstant`:

1. **Continuant Multiplicativity & Poincaré Abscissa (`Part 1`)**
2. **Multi-Branch Resolvent & Bowen-Free Poincaré-Abscissa Dimension (`Part 2`)**
3. **Multi-Residue Phase Transition at `1/2` & Concrete Witnesses (`Part 3`)**
4. **Euler–Mascheroni Zeta Expansion & Logarithmic Derivatives (`Part 4`)**
5. **Master Three-Term Subcritical Asymptotics (`Part 5`)**
6. **Supercritical Power-Law Rate `Θ(m^(-2 s₀))` (`Part 6`)**
-/

namespace ResidueMultiAsymptotic

open Matrix Set Filter Finset ENNReal Metric Real MeasureTheory
open Cylinder WindowCFRealize WindowCFBridge ResidueModGeneral TransferOperatorDim
  ResidueAsymptotic
open scoped NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Part 1: Continuant Multiplicativity, Partition Sums `wordSum`, & `poincareAbscissa` -/

lemma denQ_eq_cfProd_zero_zero (w : List ℕ) :
    denQ w = ((cfProd w) 0 0 : ℝ) := by
  unfold denQ
  rw [(cfProd_zero_cons_row1 w).1]

lemma denP_eq_cfProd_zero_one (w : List ℕ) :
    denP w = ((cfProd w) 0 1 : ℝ) := by
  unfold denP
  rw [(cfProd_zero_cons_row1 w).2]

lemma denQ_append_eq (u v : List ℕ) :
    denQ (u ++ v) = denQ u * denQ v + denP u * ((cfProd v) 1 0 : ℝ) := by
  conv_lhs => rw [denQ_eq_cfProd_zero_zero]
  rw [denQ_eq_cfProd_zero_zero u, denQ_eq_cfProd_zero_zero v, denP_eq_cfProd_zero_one u,
    cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

lemma denQ_append_ge {u v : List ℕ} (_hu : PosDigits u) (_hv : PosDigits v) :
    denQ u * denQ v ≤ denQ (u ++ v) := by
  rw [denQ_append_eq]
  have hp : 0 ≤ denP u := denP_nonneg u
  have hv10 : 0 ≤ ((cfProd v) 1 0 : ℝ) := by exact_mod_cast cfProd_nonneg v 1 0
  linarith [mul_nonneg hp hv10]

lemma denQ_append_le {u v : List ℕ} (hu : PosDigits u) (hv : PosDigits v) :
    denQ (u ++ v) ≤ 2 * denQ u * denQ v := by
  rw [denQ_append_eq]
  have hp_le : denP u ≤ denQ u := denP_le_denQ hu
  have hv10_le : ((cfProd v) 1 0 : ℝ) ≤ denQ v := by
    rw [denQ_eq_cfProd_zero_zero]
    cases v with
    | nil => simp [cfProd]
    | cons a t => exact_mod_cast (cfProd_row1_le_row0 hv (List.cons_ne_nil a t)).1
  have hmul : denP u * ((cfProd v) 1 0 : ℝ) ≤ denQ u * denQ v :=
    mul_le_mul hp_le hv10_le (by exact_mod_cast cfProd_nonneg v 1 0) (denQ_pos hu).le
  linarith

lemma denQ_two_letters_ge_two {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (2 : ℝ) ≤ denQ [a, b] := by
  rw [denQ_eq_cfProd_zero_zero]
  have hmat : ((cfProd [a, b]) 0 0 : ℤ) = (a : ℤ) * (b : ℤ) + 1 := by
    simp [cfProd, cfMat, Matrix.mul_apply, Fin.sum_univ_two]
  have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have hbZ : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
  have h2Z : (2 : ℤ) ≤ (cfProd [a, b]) 0 0 := by nlinarith
  exact_mod_cast h2Z

lemma denQ_pow_two_le {w : List ℕ} (hw : PosDigits w) :
    (2 : ℝ) ^ (w.length / 2) ≤ denQ w := by
  match w with
  | [] => simp
  | [a] =>
    simp only [List.length_singleton, Nat.reduceDiv, pow_zero]
    exact denQ_ge_one hw
  | a :: b :: t =>
    have ha : 1 ≤ a := hw a (by simp)
    have hb : 1 ≤ b := hw b (by simp)
    have ht : PosDigits t := fun d hd => hw d (by simp [hd])
    have hab : PosDigits [a, b] := fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> assumption
    have ih := denQ_pow_two_le ht
    have hsplit : a :: b :: t = [a, b] ++ t := rfl
    have hge := denQ_append_ge hab ht
    rw [← hsplit] at hge
    have h2 : (2 : ℝ) ≤ denQ [a, b] := denQ_two_letters_ge_two ha hb
    have hlen : (a :: b :: t).length / 2 = t.length / 2 + 1 := by
      simp only [List.length_cons]
      omega
    rw [hlen, pow_succ']
    have htnn : 0 ≤ (2 : ℝ) ^ (t.length / 2) := by positivity
    calc (2 : ℝ) * (2 : ℝ) ^ (t.length / 2)
        ≤ denQ [a, b] * (2 : ℝ) ^ (t.length / 2) := mul_le_mul_of_nonneg_right h2 htnn
      _ ≤ denQ [a, b] * denQ t := mul_le_mul_of_nonneg_left ih (denQ_pos hab).le
      _ ≤ denQ (a :: b :: t) := hge
termination_by w.length

lemma denQ_le_max_add_one_pow {w : List ℕ} (hw : PosDigits w) {M : ℕ}
    (hM : ∀ a ∈ w, a ≤ M) :
    denQ w ≤ ((M : ℝ) + 1) ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w a ih =>
    rw [posDigits_append] at hw
    have ih' := ih hw.1 fun b hb => hM b (by simp [hb])
    have haM : a ≤ M := hM a (by simp)
    have hstep := denQ_snoc_le hw.1 haM
    rw [List.length_append, List.length_singleton, pow_succ']
    exact hstep.trans (mul_le_mul_of_nonneg_left ih' (by positivity))

private def finAddEquiv (m n : ℕ) (α : Type*) :
    (Fin m → α) × (Fin n → α) ≃ (Fin (m + n) → α) where
  toFun p i := if h : i.1 < m then p.1 ⟨i.1, h⟩ else p.2 ⟨i.1 - m, by omega⟩
  invFun f := (fun i => f ⟨i.1, by omega⟩, fun j => f ⟨m + j.1, by omega⟩)
  left_inv p := by
    ext i
    · dsimp; simp [i.2]
    · dsimp
      have hnot : ¬ m + i.1 < m := by omega
      simp [hnot]
  right_inv f := by
    ext ⟨i, hi⟩
    dsimp
    split_ifs with h
    · rfl
    · have heq : m + (i - m) = i := by omega
      congr 1; exact Fin.ext heq

private lemma subWord_finAddEquiv {S : Finset ℕ} {m n : ℕ}
    (u : Fin m → {a : ℕ // a ∈ S}) (v : Fin n → {a : ℕ // a ∈ S}) :
    subWord (A := (S : Set ℕ)) (m + n) (finAddEquiv m n {a : ℕ // a ∈ S} (u, v)) =
      subWord (A := (S : Set ℕ)) m u ++ subWord (A := (S : Set ℕ)) n v := by
  refine List.ext_getElem (by simp [subWord]) fun i hi1 hi2 => ?_
  simp only [subWord, finAddEquiv, Equiv.coe_fn_mk, List.getElem_ofFn,
    List.getElem_append, List.length_ofFn] at hi1 hi2 ⊢
  split_ifs with h <;> rfl

private def finSnocEquivLocal {α : Type*} (n : ℕ) :
    (Fin (n + 1) → α) ≃ (Fin n → α) × α where
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

/-- Total `p`-weighted continuant partition sum over length-`n` words in `S`. -/
def wordSum (S : Finset ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → {a : ℕ // a ∈ S}, (denQ (subWord n w)) ^ (-p)

lemma wordSum_nonneg (S : Finset ℕ) (p : ℝ) (n : ℕ) : 0 ≤ wordSum S p n :=
  Finset.sum_nonneg fun w _ => Real.rpow_nonneg (by
    unfold denQ
    exact_mod_cast cfProd_nonneg (0 :: subWord n w) 1 0) _

@[simp]
lemma wordSum_zero (S : Finset ℕ) (p : ℝ) : wordSum S p 0 = 1 := by
  unfold wordSum
  letI : Unique (Fin 0 → {a : ℕ // a ∈ S}) :=
    { default := fun i => i.elim0
      uniq := fun f => funext fun i => i.elim0 }
  rw [Fintype.sum_unique]
  have hsub0 : subWord (A := (S : Set ℕ)) 0 default = [] := rfl
  rw [hsub0, denQ_nil, Real.one_rpow]

lemma wordSum_empty {p : ℝ} {n : ℕ} (hn : 1 ≤ n) : wordSum ∅ p n = 0 := by
  unfold wordSum
  have hmt : IsEmpty (Fin n → {a : ℕ // a ∈ (∅ : Finset ℕ)}) :=
    ⟨fun f => by
      have h0 : 0 < n := by omega
      exact Finset.notMem_empty _ (f ⟨0, h0⟩).2⟩
  letI := hmt
  simp

lemma wordSum_pos {S : Finset ℕ} (hSne : S.Nonempty) (hS1 : ∀ a ∈ S, 1 ≤ a) (p : ℝ) (n : ℕ) :
    0 < wordSum S p n := by
  obtain ⟨a₀, ha₀⟩ := hSne
  let w₀ : Fin n → {a : ℕ // a ∈ S} := fun _ => ⟨a₀, ha₀⟩
  have hterm : 0 < (denQ (subWord n w₀)) ^ (-p) :=
    Real.rpow_pos_of_pos (denQ_pos (posDigits_subWord (fun a ha => hS1 a ha) n w₀)) _
  have hle : (denQ (subWord n w₀)) ^ (-p) ≤ wordSum S p n :=
    Finset.single_le_sum (f := fun w : Fin n → {a : ℕ // a ∈ S} => (denQ (subWord n w)) ^ (-p))
      (fun w _ => Real.rpow_nonneg (denQ_pos (posDigits_subWord (fun a ha => hS1 a ha) n w)).le _)
      (Finset.mem_univ w₀)
  exact lt_of_lt_of_le hterm hle

lemma wordSum_one (S : Finset ℕ) (p : ℝ) :
    wordSum S p 1 = ∑ a ∈ S, (a : ℝ) ^ (-p) := by
  unfold wordSum
  let e : {a : ℕ // a ∈ S} ≃ (Fin 1 → {a : ℕ // a ∈ S}) :=
    { toFun := fun a _ => a
      invFun := fun w => w 0
      left_inv := fun _ => rfl
      right_inv := fun w => funext fun i => by fin_cases i; rfl }
  rw [← Equiv.sum_comp e (fun w => (denQ (subWord 1 w)) ^ (-p))]
  have hterm : ∀ a : {a : ℕ // a ∈ S},
      (denQ (subWord 1 (e a))) ^ (-p) = (a.1 : ℝ) ^ (-p) := fun a => by
    have hs1 : subWord 1 (e a) = [a.1] := by
      refine List.ext_getElem (by simp [subWord]) fun i hi _ => ?_
      rw [subWord_length] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp [subWord, e]
    have hq : denQ [a.1] = (a.1 : ℝ) := by
      rw [denQ_eq_cfProd_zero_zero]
      simp [cfProd, cfMat]
    rw [hs1, hq]
  simp_rw [hterm, Finset.univ_eq_attach]
  exact Finset.sum_attach S (fun a => (a : ℝ) ^ (-p))

lemma wordSum_antitone_p (S : Finset ℕ) (hS1 : ∀ a ∈ S, 1 ≤ a) {p₁ p₂ : ℝ}
    (hle : p₁ ≤ p₂) (n : ℕ) :
    wordSum S p₂ n ≤ wordSum S p₁ n := by
  refine Finset.sum_le_sum fun w _ => ?_
  have h1 : (1 : ℝ) ≤ denQ (subWord n w) :=
    denQ_ge_one (posDigits_subWord (fun a ha => hS1 a ha) n w)
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

lemma wordSum_add_le {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a) {p : ℝ} (hp : 0 ≤ p)
    (m n : ℕ) :
    wordSum S p (m + n) ≤ wordSum S p m * wordSum S p n := by
  unfold wordSum
  rw [← Equiv.sum_comp (finAddEquiv m n {a : ℕ // a ∈ S})]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [subWord_finAddEquiv]
  have hmu := posDigits_subWord (fun a ha => hS1 a ha) m u
  have hnv := posDigits_subWord (fun a ha => hS1 a ha) n v
  have hq_pos : 0 < denQ (subWord m u) * denQ (subWord n v) :=
    mul_pos (denQ_pos hmu) (denQ_pos hnv)
  have hge := denQ_append_ge hmu hnv
  have hr := Real.rpow_le_rpow_of_nonpos hq_pos hge (neg_nonpos.mpr hp)
  rw [Real.mul_rpow (denQ_pos hmu).le (denQ_pos hnv).le] at hr
  exact hr

lemma wordSum_add_ge {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a) {p : ℝ} (hp : 0 ≤ p)
    (m n : ℕ) :
    (2 : ℝ) ^ (-p) * wordSum S p m * wordSum S p n ≤ wordSum S p (m + n) := by
  unfold wordSum
  rw [← Equiv.sum_comp (finAddEquiv m n {a : ℕ // a ∈ S})]
  rw [Fintype.sum_prod_type, mul_assoc, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [subWord_finAddEquiv]
  have hmu := posDigits_subWord (fun a ha => hS1 a ha) m u
  have hnv := posDigits_subWord (fun a ha => hS1 a ha) n v
  have hle := denQ_append_le hmu hnv
  have hpos : 0 < denQ (subWord m u ++ subWord n v) :=
    denQ_pos (posDigits_append.mpr ⟨hmu, hnv⟩)
  have hr := Real.rpow_le_rpow_of_nonpos hpos hle (neg_nonpos.mpr hp)
  rw [mul_assoc (2 : ℝ), Real.mul_rpow (by norm_num) (mul_nonneg (denQ_pos hmu).le (denQ_pos hnv).le),
    Real.mul_rpow (denQ_pos hmu).le (denQ_pos hnv).le] at hr
  simpa [mul_assoc] using hr

private lemma gauss_density_step_bound {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑ a ∈ S, (((a : ℝ) + x) ^ (-2 : ℝ)) * (1 / (1 + 1 / ((a : ℝ) + x)))) ≤
      (1 - 1 / (((S.sup id : ℕ) : ℝ) + 2)) * (1 / (1 + x)) := by
  set M := S.sup id
  have hterm_eq : ∀ a : ℕ, 1 ≤ a →
      (((a : ℝ) + x) ^ (-2 : ℝ)) * (1 / (1 + 1 / ((a : ℝ) + x))) =
        1 / ((a : ℝ) + x) - 1 / (((a : ℝ) + 1) + x) := fun a ha => by
    have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hax : 0 < (a : ℝ) + x := by linarith [hx.1]
    have hax1 : 0 < ((a : ℝ) + 1) + x := by linarith [hx.1]
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hax.le, Real.rpow_natCast]
    field_simp [hax.ne', hax1.ne']
    ring
  have hsum_le_Icc :
      (∑ a ∈ S, (((a : ℝ) + x) ^ (-2 : ℝ)) * (1 / (1 + 1 / ((a : ℝ) + x)))) ≤
        ∑ a ∈ Finset.Icc 1 M, (1 / ((a : ℝ) + x) - 1 / (((a : ℝ) + 1) + x)) := by
    have hS_sub : S ⊆ Finset.Icc 1 M := fun a ha =>
      Finset.mem_Icc.mpr ⟨hS1 a ha, Finset.le_sup (f := id) ha⟩
    calc (∑ a ∈ S, (((a : ℝ) + x) ^ (-2 : ℝ)) * (1 / (1 + 1 / ((a : ℝ) + x))))
        = ∑ a ∈ S, (1 / ((a : ℝ) + x) - 1 / (((a : ℝ) + 1) + x)) :=
          Finset.sum_congr rfl fun a ha => hterm_eq a (hS1 a ha)
      _ ≤ ∑ a ∈ Finset.Icc 1 M, (1 / ((a : ℝ) + x) - 1 / (((a : ℝ) + 1) + x)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun a ha _ => ?_
          have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp ha).1
          have hax : 0 < (a : ℝ) + x := by linarith [hx.1]
          have hax1 : 0 < ((a : ℝ) + 1) + x := by linarith [hx.1]
          rw [sub_nonneg]
          exact one_div_le_one_div_of_le hax (by linarith)
  have htel : (∑ a ∈ Finset.Icc 1 M, (1 / ((a : ℝ) + x) - 1 / (((a : ℝ) + 1) + x))) =
      if M = 0 then 0 else 1 / (1 + x) - 1 / ((M : ℝ) + 1 + x) := by
    induction M with
    | zero => simp
    | succ M ih =>
      by_cases hM0 : M = 0
      · subst hM0
        simp [Finset.Icc_self]
      · rw [show Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) by
            ext y; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
          Finset.sum_insert (by simp)]
        rw [ih]
        simp only [hM0, ↓reduceIte, Nat.succ_ne_zero]
        push_cast
        ring
  rcases eq_or_ne M 0 with hM0 | hMne
  · simp only [htel, hM0, ↓reduceIte] at hsum_le_Icc
    have hM2_pos : (0 : ℝ) < (M : ℝ) + 2 := by positivity
    have h1 : 1 / ((M : ℝ) + 2) ≤ 1 := (div_le_one hM2_pos).mpr (by linarith [Nat.cast_nonneg (α := ℝ) M])
    have hfac : 0 ≤ (1 - 1 / ((M : ℝ) + 2)) * (1 / (1 + x)) :=
      mul_nonneg (sub_nonneg.mpr h1) (div_nonneg zero_le_one (by linarith [hx.1]))
    exact hsum_le_Icc.trans hfac
  · simp only [htel, hMne, ↓reduceIte] at hsum_le_Icc
    have h1x : 0 < 1 + x := by linarith [hx.1]
    have hM1x : 0 < (M : ℝ) + 1 + x := by linarith [hx.1, Nat.cast_nonneg (α := ℝ) M]
    have hM2 : (0 : ℝ) < (M : ℝ) + 2 := by positivity
    have hcmp : 1 / ((M : ℝ) + 2) ≤ (1 + x) / ((M : ℝ) + 1 + x) := by
      rw [div_le_div_iff₀ hM2 hM1x]
      have hM_nn : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
      nlinarith [hx.1]
    have hrew : 1 / (1 + x) - 1 / ((M : ℝ) + 1 + x) =
        (1 - (1 + x) / ((M : ℝ) + 1 + x)) * (1 / (1 + x)) := by
      field_simp [h1x.ne', hM1x.ne']
    refine hsum_le_Icc.trans ?_
    rw [hrew]
    exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg zero_le_one h1x.le)

lemma wordSum_two_le_geom (S : Finset ℕ) (hS1 : ∀ a ∈ S, 1 ≤ a) (n : ℕ) :
    wordSum S 2 n ≤ 2 * (1 - 1 / (((S.sup id : ℕ) : ℝ) + 2)) ^ n := by
  let ρ : ℝ := 1 - 1 / (((S.sup id : ℕ) : ℝ) + 2)
  have hρ_nn : 0 ≤ ρ := by
    have hpos : (0 : ℝ) < ((S.sup id : ℕ) : ℝ) + 2 := by positivity
    have : 1 / (((S.sup id : ℕ) : ℝ) + 2) ≤ 1 :=
      (div_le_one hpos).mpr (by linarith [Nat.cast_nonneg (α := ℝ) (S.sup id)])
    linarith
  let W : ℕ → ℝ := fun k =>
    ∑ w : Fin k → {a : ℕ // a ∈ S},
      (1 / (1 + ratioT (subWord k w))) * (denQ (subWord k w)) ^ (-2 : ℝ)
  have hW_step : ∀ k : ℕ, W (k + 1) ≤ ρ * W k := by
    intro k
    dsimp only [W]
    rw [← Equiv.sum_comp (finSnocEquivLocal (α := {a : ℕ // a ∈ S}) k).symm, Fintype.sum_prod_type]
    have hterm : ∀ u : Fin k → {a : ℕ // a ∈ S}, ∀ a : {a : ℕ // a ∈ S},
        (1 / (1 + ratioT (subWord (k + 1) ((finSnocEquivLocal k).symm (u, a))))) *
          (denQ (subWord (k + 1) ((finSnocEquivLocal k).symm (u, a)))) ^ (-2 : ℝ) =
          ((((a.1 : ℝ) + ratioT (subWord k u)) ^ (-2 : ℝ)) *
            (1 / (1 + 1 / ((a.1 : ℝ) + ratioT (subWord k u))))) *
              (denQ (subWord k u)) ^ (-2 : ℝ) := fun u a => by
      change (1 / (1 + ratioT (subWord (k + 1) (Fin.snoc u a)))) *
        (denQ (subWord (k + 1) (Fin.snoc u a))) ^ (-2 : ℝ) = _
      have hpd := posDigits_subWord (fun b hb => hS1 b hb) k u
      have ha1 : 1 ≤ a.1 := hS1 a.1 a.2
      have hq : 0 < denQ (subWord k u) := denQ_pos hpd
      have hax : 0 < (a.1 : ℝ) + ratioT (subWord k u) := by
        have : (1 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast ha1
        linarith [(ratioT_mem_Icc hpd).1]
      rw [subWord_snoc, ratioT_snoc hpd a.1 ha1, denQ_snoc_factor hpd a.1,
        Real.mul_rpow hq.le hax.le]
      ring
    simp_rw [hterm, ← Finset.sum_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    have hpd := posDigits_subWord (fun b hb => hS1 b hb) k u
    have hgb := gauss_density_step_bound hS1 (ratioT_mem_Icc hpd)
    rw [Finset.univ_eq_attach]
    have hsum_att :
        (∑ a ∈ S.attach, (((a.1 : ℝ) + ratioT (subWord k u)) ^ (-2 : ℝ)) *
          (1 / (1 + 1 / ((a.1 : ℝ) + ratioT (subWord k u))))) =
          ∑ a ∈ S, (((a : ℝ) + ratioT (subWord k u)) ^ (-2 : ℝ)) *
            (1 / (1 + 1 / ((a : ℝ) + ratioT (subWord k u)))) :=
      Finset.sum_attach S (fun a : ℕ =>
        (((a : ℝ) + ratioT (subWord k u)) ^ (-2 : ℝ)) *
          (1 / (1 + 1 / ((a : ℝ) + ratioT (subWord k u)))))
    rw [hsum_att, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hgb (Real.rpow_nonneg (denQ_pos hpd).le _)
  have hW_pow : ∀ k : ℕ, W k ≤ ρ ^ k := by
    intro k
    induction k with
    | zero =>
      dsimp only [W]
      letI : Unique (Fin 0 → {a : ℕ // a ∈ S}) :=
        { default := fun i => i.elim0
          uniq := fun f => funext fun i => i.elim0 }
      rw [Fintype.sum_unique]
      have hsub0 : subWord (A := (S : Set ℕ)) 0 default = [] := rfl
      rw [hsub0, ratioT_nil, denQ_nil]
      norm_num
    | succ k ih =>
      rw [pow_succ']
      exact (hW_step k).trans (mul_le_mul_of_nonneg_left ih hρ_nn)
  have hword_le : wordSum S 2 n ≤ 2 * W n := by
    unfold wordSum
    dsimp only [W]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    have hpd := posDigits_subWord (fun a ha => hS1 a ha) n w
    have hrt := ratioT_mem_Icc hpd
    have hhalf : (1 / 2 : ℝ) ≤ 1 / (1 + ratioT (subWord n w)) :=
      one_div_le_one_div_of_le (by linarith [hrt.1]) (by linarith [hrt.2])
    have hmul : (1 : ℝ) * (denQ (subWord n w)) ^ (-2 : ℝ) ≤
        (2 * (1 / (1 + ratioT (subWord n w)))) * (denQ (subWord n w)) ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (denQ_pos hpd).le _)
    linarith [hmul]
  exact hword_le.trans (mul_le_mul_of_nonneg_left (hW_pow n) zero_le_two)

theorem summable_wordSum_two {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a) :
    Summable (wordSum S 2) := by
  let ρ : ℝ := 1 - 1 / (((S.sup id : ℕ) : ℝ) + 2)
  have hpos : (0 : ℝ) < ((S.sup id : ℕ) : ℝ) + 2 := by positivity
  have hρ_nn : 0 ≤ ρ := by
    have : 1 / (((S.sup id : ℕ) : ℝ) + 2) ≤ 1 :=
      (div_le_one hpos).mpr (by linarith [Nat.cast_nonneg (α := ℝ) (S.sup id)])
    linarith
  have hρ_lt : ρ < 1 := by
    have : 0 < 1 / (((S.sup id : ℕ) : ℝ) + 2) := by positivity
    linarith
  exact Summable.of_nonneg_of_le (wordSum_nonneg S 2) (wordSum_two_le_geom S hS1)
    ((summable_geometric_of_lt_one hρ_nn hρ_lt).mul_left 2)

theorem exists_geom_bound_of_exists_wordSum_lt_one {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {p : ℝ} (hp : 0 ≤ p) (hex : ∃ n ≥ 1, wordSum S p n < 1) :
    ∃ C > 0, ∃ ρ ∈ Set.Ioo (0 : ℝ) 1, ∀ k : ℕ, wordSum S p k ≤ C * ρ ^ k := by
  by_cases hSne : S.Nonempty
  · obtain ⟨n, hn1, hlt⟩ := hex
    let ρ₀ : ℝ := wordSum S p n
    have hρ_pos : 0 < ρ₀ := wordSum_pos hSne hS1 p n
    have hρ_lt : ρ₀ < 1 := hlt
    have hblock : ∀ q : ℕ, wordSum S p (q * n) ≤ ρ₀ ^ q := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [Nat.succ_mul, pow_succ]
        exact (wordSum_add_le hS1 hp (q * n) n).trans (mul_le_mul_of_nonneg_right ih hρ_pos.le)
    let Cmax : ℝ := ∑ r ∈ Finset.range n, wordSum S p r + 1
    have hCmax_pos : 0 < Cmax := by
      have : 0 ≤ ∑ r ∈ Finset.range n, wordSum S p r :=
        Finset.sum_nonneg fun r _ => wordSum_nonneg S p r
      linarith
    have hCmax_ge : ∀ r < n, wordSum S p r ≤ Cmax := fun r hr => by
      have h1 := Finset.single_le_sum (fun j _ => wordSum_nonneg S p j) (Finset.mem_range.mpr hr)
      dsimp only [Cmax]; linarith
    let σ : ℝ := ρ₀ ^ ((1 : ℝ) / (n : ℝ))
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hσ_pos : 0 < σ := Real.rpow_pos_of_pos hρ_pos _
    have hσ_lt : σ < 1 := Real.rpow_lt_one hρ_pos.le hρ_lt (by positivity)
    refine ⟨Cmax / ρ₀, div_pos hCmax_pos hρ_pos, σ, ⟨hσ_pos, hσ_lt⟩, fun k => ?_⟩
    let q := k / n
    let r := k % n
    have hkr : k = q * n + r := by rw [mul_comm, Nat.div_add_mod]
    have hr_lt : r < n := Nat.mod_lt k hn1
    have h1 : wordSum S p k ≤ wordSum S p (q * n) * wordSum S p r := by
      conv_lhs => rw [hkr]
      exact wordSum_add_le hS1 hp (q * n) r
    have h2 : wordSum S p (q * n) ≤ ρ₀ ^ q := hblock q
    have h3 : wordSum S p r ≤ Cmax := hCmax_ge r hr_lt
    have hq_exp : (k : ℝ) / (n : ℝ) ≤ (q : ℝ) + 1 := by
      have hkR : (k : ℝ) = (q : ℝ) * (n : ℝ) + (r : ℝ) := by exact_mod_cast hkr
      have hrR : (r : ℝ) < (n : ℝ) := by exact_mod_cast hr_lt
      rw [div_le_iff₀ hn_pos]
      nlinarith
    have hρ_pow : ρ₀ ^ q ≤ (1 / ρ₀) * σ ^ k := by
      rw [← Real.rpow_natCast ρ₀ q, ← Real.rpow_natCast σ k]
      have hσk : σ ^ (k : ℝ) = ρ₀ ^ ((k : ℝ) / (n : ℝ)) := by
        dsimp [σ]
        rw [← Real.rpow_mul hρ_pos.le]
        congr 1; ring
      rw [hσk, one_div, ← Real.rpow_neg_one ρ₀, ← Real.rpow_add hρ_pos]
      refine Real.rpow_le_rpow_of_exponent_ge hρ_pos hρ_lt.le ?_
      linarith
    calc wordSum S p k ≤ wordSum S p (q * n) * wordSum S p r := h1
      _ ≤ ρ₀ ^ q * Cmax := mul_le_mul h2 h3 (wordSum_nonneg S p r) (pow_nonneg hρ_pos.le q)
      _ ≤ ((1 / ρ₀) * σ ^ k) * Cmax := mul_le_mul_of_nonneg_right hρ_pow hCmax_pos.le
      _ = (Cmax / ρ₀) * σ ^ k := by ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hSne
    subst hSne
    refine ⟨1, zero_lt_one, 1 / 2, ⟨by norm_num, by norm_num⟩, fun k => ?_⟩
    cases k with
    | zero => simp
    | succ k => rw [wordSum_empty (by omega)]; positivity

theorem summable_wordSum_iff_exists_lt_one {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {p : ℝ} (hp : 0 ≤ p) :
    Summable (wordSum S p) ↔ ∃ n ≥ 1, wordSum S p n < 1 := by
  constructor
  · intro hsum
    obtain ⟨n, hn⟩ := ((hsum.tendsto_atTop_zero.eventually (gt_mem_nhds zero_lt_one)).and
      (eventually_ge_atTop 1)).exists
    exact ⟨n, hn.2, hn.1⟩
  · intro hex
    obtain ⟨C, _, ρ, ⟨hρ0, hρ1⟩, hbd⟩ :=
      exists_geom_bound_of_exists_wordSum_lt_one hS1 hp hex
    exact Summable.of_nonneg_of_le (wordSum_nonneg S p) hbd
      ((summable_geometric_of_lt_one hρ0.le hρ1).mul_left C)

theorem exists_geom_bound_of_summable_wordSum {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {p : ℝ} (hp : 0 ≤ p) (hsum : Summable (wordSum S p)) :
    ∃ C > 0, ∃ ρ ∈ Set.Ioo (0 : ℝ) 1, ∀ k : ℕ, wordSum S p k ≤ C * ρ ^ k :=
  exists_geom_bound_of_exists_wordSum_lt_one hS1 hp
    ((summable_wordSum_iff_exists_lt_one hS1 hp).mp hsum)

/-- Critical Poincaré abscissa `s₀(S) = inf {s > 0 : ∑_n ∑_{w ∈ S^n} q(w)^{-2s} < ∞}`. -/
def poincareAbscissa (S : Finset ℕ) : ℝ :=
  sInf {s : ℝ | 0 < s ∧ Summable (wordSum S (2 * s))}

lemma poincareAbscissa_nonneg (S : Finset ℕ) : 0 ≤ poincareAbscissa S := by
  unfold poincareAbscissa
  refine Real.sInf_nonneg fun s hs => hs.1.le

lemma poincareAbscissa_le_one {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a) :
    poincareAbscissa S ≤ 1 := by
  refine csInf_le ⟨0, fun s hs => hs.1.le⟩ ?_
  refine ⟨zero_lt_one, ?_⟩
  simpa using summable_wordSum_two hS1

lemma summable_wordSum_of_poincareAbscissa_lt {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {s : ℝ} (hs : poincareAbscissa S < s) :
    Summable (wordSum S (2 * s)) := by
  obtain ⟨s₁, ⟨_, hs₁_sum⟩, hs₁_lt⟩ :=
    exists_lt_of_csInf_lt
      (by refine ⟨1, zero_lt_one, ?_⟩; simpa using summable_wordSum_two hS1) hs
  refine Summable.of_nonneg_of_le (wordSum_nonneg S (2 * s))
    (fun n => wordSum_antitone_p S hS1 (by linarith) n) hs₁_sum

lemma not_summable_wordSum_of_lt_poincareAbscissa {S : Finset ℕ}
    {s : ℝ} (hs0 : 0 < s) (hs : s < poincareAbscissa S) :
    ¬ Summable (wordSum S (2 * s)) := fun hsum =>
  not_le_of_gt hs (csInf_le ⟨0, fun x hx => hx.1.le⟩ ⟨hs0, hsum⟩)

lemma one_le_wordSum_poincareAbscissa {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    (hs₀ : 0 < poincareAbscissa S) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ wordSum S (2 * poincareAbscissa S) n := by
  by_contra hlt
  push Not at hlt
  have hcont : Continuous (fun s : ℝ => wordSum S (2 * s) n) := by
    unfold wordSum
    refine continuous_finsetSum _ fun w _ => ?_
    have hq : 0 < denQ (subWord n w) :=
      denQ_pos (posDigits_subWord (fun a ha => hS1 a ha) n w)
    exact Continuous.rpow continuous_const (continuous_const.mul continuous_id).neg
      (fun _ => Or.inl hq.ne')
  have hev := (hcont.continuousAt (x := poincareAbscissa S)).eventually (Iio_mem_nhds hlt)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, hη_bd⟩ := hev
  let s₂ : ℝ := max (poincareAbscissa S / 2) (poincareAbscissa S - η / 2)
  have hs₂_pos : 0 < s₂ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hs₂_lt : s₂ < poincareAbscissa S := max_lt (by linarith) (by linarith)
  have hdist : dist s₂ (poincareAbscissa S) < η := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs₂_lt)]
    have : poincareAbscissa S - η / 2 ≤ s₂ := le_max_right _ _
    linarith
  have hw_lt : wordSum S (2 * s₂) n < 1 := hη_bd hdist
  have hsum : Summable (wordSum S (2 * s₂)) :=
    (summable_wordSum_iff_exists_lt_one hS1 (by linarith)).mpr ⟨n, hn, hw_lt⟩
  exact not_summable_wordSum_of_lt_poincareAbscissa hs₂_pos hs₂_lt hsum

lemma wordSum_poincareAbscissa_le {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a) (n : ℕ) :
    wordSum S (2 * poincareAbscissa S) n ≤ (2 : ℝ) ^ (2 * poincareAbscissa S) := by
  by_contra hgt
  push Not at hgt
  have hn1 : 1 ≤ n := by
    by_contra hn0
    have hn_eq : n = 0 := by omega
    subst hn_eq
    rw [wordSum_zero] at hgt
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * poincareAbscissa S) :=
      Real.one_le_rpow one_le_two (by linarith [poincareAbscissa_nonneg S])
    linarith
  have hcont : Continuous (fun s : ℝ => (2 : ℝ) ^ (-(2 * s)) * wordSum S (2 * s) n) := by
    refine Continuous.mul
      (Continuous.rpow continuous_const (continuous_const.mul continuous_id).neg
        (fun _ => Or.inl (by norm_num))) ?_
    unfold wordSum
    refine continuous_finsetSum _ fun w _ => ?_
    have hq : 0 < denQ (subWord n w) :=
      denQ_pos (posDigits_subWord (fun a ha => hS1 a ha) n w)
    exact Continuous.rpow continuous_const (continuous_const.mul continuous_id).neg
      (fun _ => Or.inl hq.ne')
  have hgt1 : 1 < (2 : ℝ) ^ (-(2 * poincareAbscissa S)) *
      wordSum S (2 * poincareAbscissa S) n := by
    have hpos : 0 < (2 : ℝ) ^ (2 * poincareAbscissa S) := Real.rpow_pos_of_pos (by norm_num) _
    rw [Real.rpow_neg (by norm_num), inv_mul_eq_div, lt_div_iff₀ hpos, one_mul]
    exact hgt
  have hev := (hcont.continuousAt (x := poincareAbscissa S)).eventually (Ioi_mem_nhds hgt1)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, hη_bd⟩ := hev
  let s₁ : ℝ := poincareAbscissa S + η / 2
  have hs₁_gt : poincareAbscissa S < s₁ := by dsimp [s₁]; linarith
  have hs₁_pos : 0 < s₁ := lt_of_le_of_lt (poincareAbscissa_nonneg S) hs₁_gt
  have hdist : dist s₁ (poincareAbscissa S) < η := by
    rw [Real.dist_eq, abs_of_pos (by dsimp [s₁]; linarith)]
    dsimp [s₁]; linarith
  have hc1 : 1 < (2 : ℝ) ^ (-(2 * s₁)) * wordSum S (2 * s₁) n := hη_bd hdist
  have hlow : ∀ k : ℕ, 1 ≤ k → (1 : ℝ) ≤ (2 : ℝ) ^ (-(2 * s₁)) * wordSum S (2 * s₁) (k * n) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simpa using hc1.le
    | succ k hk ih =>
      rw [Nat.succ_mul]
      have hge := wordSum_add_ge hS1 (by linarith : 0 ≤ 2 * s₁) (k * n) n
      have hmul := mul_le_mul_of_nonneg_left hge
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(2 * s₁)))
      have hprod : (1 : ℝ) ≤
          ((2 : ℝ) ^ (-(2 * s₁)) * wordSum S (2 * s₁) (k * n)) *
            ((2 : ℝ) ^ (-(2 * s₁)) * wordSum S (2 * s₁) n) := by
        nlinarith [hc1, ih]
      linarith [hmul, hprod]
  have hsum : Summable (wordSum S (2 * s₁)) := summable_wordSum_of_poincareAbscissa_lt hS1 hs₁_gt
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds zero_lt_one))
  let m₀ := max N 1
  have hm₀1 : 1 ≤ m₀ := le_max_right _ _
  have hm₀_ge : N ≤ m₀ * n := by
    calc N ≤ m₀ := le_max_left _ _
      _ = m₀ * 1 := (mul_one _).symm
      _ ≤ m₀ * n := Nat.mul_le_mul_left m₀ hn1
  have hlt_one := hN (m₀ * n) hm₀_ge
  have hge_pow := hlow m₀ hm₀1
  have h2_le_one : (2 : ℝ) ^ (-(2 * s₁)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)
  have hge_one : (1 : ℝ) ≤ wordSum S (2 * s₁) (m₀ * n) := by
    have hnn := wordSum_nonneg S (2 * s₁) (m₀ * n)
    nlinarith [h2_le_one, hge_pow]
  linarith

/-! ### Part 2: Multi-Branch Resolvent & Bowen-Free Poincaré-Abscissa Dimension Formula -/

lemma transferOp_finset_eq (S : Finset ℕ) (s : ℝ) (v : ℝ → ℝ≥0∞) (x : ℝ) :
    transferOp (S : Set ℕ) s v x =
      ∑ a ∈ S, v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))) := by
  let F : ℕ → ℝ≥0∞ := fun a =>
    v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))
  unfold transferOp
  trans (∑' a : ℕ, Set.indicator (S : Set ℕ) F a)
  · refine tsum_congr fun a => ?_
    by_cases ha : a ∈ S <;> simp [Set.indicator_apply, ha, F]
  · rw [← tsum_subtype (S : Set ℕ) F, tsum_fintype, Finset.univ_eq_attach]
    exact Finset.sum_attach S F

/-- Total `p`-weighted continuant series `C_S(p) = ∑' n, ∑_{w ∈ S^n} q(w)^{-p}`. -/
def multiC (S : Finset ℕ) (p : ℝ) : ℝ :=
  ∑' n : ℕ, wordSum S p n

/-- Multi-branch resolvent test function `V_{S,s}(x) = ∑' n, ∑_{w ∈ S^n} (q(w) + p(w) x)^{-2s}`. -/
def multiResolventV (S : Finset ℕ) (s x : ℝ) : ℝ :=
  ∑' n : ℕ, ∑ w : Fin n → {a : ℕ // a ∈ S},
    (denQ (subWord n w) + denP (subWord n w) * x) ^ (-(2 * s))

lemma multiResolventV_term_le {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (n : ℕ) :
    (∑ w : Fin n → {a : ℕ // a ∈ S},
      (denQ (subWord n w) + denP (subWord n w) * x) ^ (-(2 * s))) ≤ wordSum S (2 * s) n := by
  refine Finset.sum_le_sum fun w _ => ?_
  have hq : 0 < denQ (subWord n w) := denQ_pos (posDigits_subWord (fun a ha => hS1 a ha) n w)
  have hp : 0 ≤ denP (subWord n w) * x := mul_nonneg (denP_nonneg _) hx
  exact Real.rpow_le_rpow_of_nonpos hq (by linarith) (by linarith)

lemma summable_multiResolventV {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (hsum : Summable (wordSum S (2 * s))) :
    Summable fun n : ℕ => ∑ w : Fin n → {a : ℕ // a ∈ S},
      (denQ (subWord n w) + denP (subWord n w) * x) ^ (-(2 * s)) :=
  Summable.of_nonneg_of_le
    (fun n => Finset.sum_nonneg fun w _ =>
      Real.rpow_nonneg
        (add_nonneg (denQ_pos (posDigits_subWord (fun a ha => hS1 a ha) n w)).le
          (mul_nonneg (denP_nonneg _) hx)) _)
    (multiResolventV_term_le hS1 hs hx) hsum

lemma multiResolventV_zero (S : Finset ℕ) (s : ℝ) :
    multiResolventV S s 0 = multiC S (2 * s) := by
  simp [multiResolventV, multiC, wordSum]

lemma one_le_multiC {S : Finset ℕ} {p : ℝ} (hsum : Summable (wordSum S p)) :
    1 ≤ multiC S p := by
  unfold multiC
  have h0 : wordSum S p 0 = 1 := wordSum_zero S p
  have hle := hsum.le_tsum 0 (fun n _ => wordSum_nonneg S p n)
  linarith

lemma one_le_multiResolventV {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (hsum : Summable (wordSum S (2 * s))) :
    1 ≤ multiResolventV S s x := by
  unfold multiResolventV
  have h0 : (∑ w : Fin 0 → {a : ℕ // a ∈ S},
      (denQ (subWord 0 w) + denP (subWord 0 w) * x) ^ (-(2 * s))) = 1 := by
    letI : Unique (Fin 0 → {a : ℕ // a ∈ S}) :=
      { default := fun i => i.elim0
        uniq := fun f => funext fun i => i.elim0 }
    rw [Fintype.sum_unique]
    have hsub0 : subWord (A := (S : Set ℕ)) 0 default = [] := rfl
    rw [hsub0, denQ_nil, denP_nil, zero_mul, add_zero, Real.one_rpow]
  have hle := (summable_multiResolventV hS1 hs hx hsum).le_tsum 0 (fun n _ =>
    Finset.sum_nonneg fun w _ => Real.rpow_nonneg
      (add_nonneg (denQ_pos (posDigits_subWord (fun a ha => hS1 a ha) n w)).le
        (mul_nonneg (denP_nonneg _) hx)) _)
  linarith

lemma multiResolventV_le_multiC {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (hsum : Summable (wordSum S (2 * s))) :
    multiResolventV S s x ≤ multiC S (2 * s) :=
  Summable.tsum_le_tsum (multiResolventV_term_le hS1 hs hx)
    (summable_multiResolventV hS1 hs hx hsum) hsum

lemma multiResolventV_antitone {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {s : ℝ} (hs : 0 < s) (hsum : Summable (wordSum S (2 * s)))
    {x₁ x₂ : ℝ} (hx₁ : 0 ≤ x₁) (hle : x₁ ≤ x₂) :
    multiResolventV S s x₂ ≤ multiResolventV S s x₁ := by
  unfold multiResolventV
  refine Summable.tsum_le_tsum (fun n => Finset.sum_le_sum fun w _ => ?_)
    (summable_multiResolventV hS1 hs (hx₁.trans hle) hsum)
    (summable_multiResolventV hS1 hs hx₁ hsum)
  have hq : 0 < denQ (subWord n w) + denP (subWord n w) * x₁ :=
    add_pos_of_pos_of_nonneg (denQ_pos (posDigits_subWord (fun a ha => hS1 a ha) n w))
      (mul_nonneg (denP_nonneg _) hx₁)
  have hbase : denQ (subWord n w) + denP (subWord n w) * x₁ ≤
      denQ (subWord n w) + denP (subWord n w) * x₂ :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hle (denP_nonneg _))
  exact Real.rpow_le_rpow_of_nonpos hq hbase (by linarith)

/-- **Exact Multi-Branch Resolvent Functional Identity**:
    `∑_{a ∈ S} (a + x)^{-2s} V_{S,s}(1/(a + x)) = V_{S,s}(x) - 1`. -/
theorem multiResolventV_branch_eq {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (hsum : Summable (wordSum S (2 * s))) :
    (∑ a ∈ S, ((a : ℝ) + x) ^ (-(2 * s)) * multiResolventV S s (1 / ((a : ℝ) + x))) =
      multiResolventV S s x - 1 := by
  have hsum_a : ∀ a ∈ S, Summable fun n : ℕ =>
      ((a : ℝ) + x) ^ (-(2 * s)) *
        ∑ w : Fin n → {b : ℕ // b ∈ S},
          (denQ (subWord n w) + denP (subWord n w) * (1 / ((a : ℝ) + x))) ^ (-(2 * s)) := by
    intro a ha
    have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hS1 a ha
    have hax : 0 ≤ 1 / ((a : ℝ) + x) := by positivity
    exact (summable_multiResolventV hS1 hs hax hsum).mul_left _
  have hmul : ∀ a ∈ S,
      ((a : ℝ) + x) ^ (-(2 * s)) * multiResolventV S s (1 / ((a : ℝ) + x)) =
        ∑' n : ℕ, ((a : ℝ) + x) ^ (-(2 * s)) *
          ∑ w : Fin n → {b : ℕ // b ∈ S},
            (denQ (subWord n w) + denP (subWord n w) * (1 / ((a : ℝ) + x))) ^ (-(2 * s)) := by
    intro a _
    unfold multiResolventV
    rw [← tsum_mul_left]
  rw [Finset.sum_congr rfl hmul, ← Summable.tsum_finsetSum (fun a ha => hsum_a a ha)]
  have hstep : ∀ n : ℕ,
      (∑ a ∈ S, ((a : ℝ) + x) ^ (-(2 * s)) *
        ∑ w : Fin n → {b : ℕ // b ∈ S},
          (denQ (subWord n w) + denP (subWord n w) * (1 / ((a : ℝ) + x))) ^ (-(2 * s))) =
        ∑ w : Fin (n + 1) → {b : ℕ // b ∈ S},
          (denQ (subWord (n + 1) w) + denP (subWord (n + 1) w) * x) ^ (-(2 * s)) := by
    intro n
    rw [← Equiv.sum_comp (finSnocEquivLocal (α := {b : ℕ // b ∈ S}) n).symm, Fintype.sum_prod_type,
      Finset.sum_comm]
    rw [Finset.univ_eq_attach]
    rw [← Finset.sum_attach S (fun a => ((a : ℝ) + x) ^ (-(2 * s)) *
      ∑ w : Fin n → {b : ℕ // b ∈ S},
        (denQ (subWord n w) + denP (subWord n w) * (1 / ((a : ℝ) + x))) ^ (-(2 * s)))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    change ((a.1 : ℝ) + x) ^ (-(2 * s)) *
        (denQ (subWord n u) + denP (subWord n u) * (1 / ((a.1 : ℝ) + x))) ^ (-(2 * s)) =
      (denQ (subWord (n + 1) (Fin.snoc u a)) +
        denP (subWord (n + 1) (Fin.snoc u a)) * x) ^ (-(2 * s))
    have haR : (1 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast hS1 a.1 a.2
    have hax_pos : 0 < (a.1 : ℝ) + x := by linarith
    have hpd := posDigits_subWord (fun b hb => hS1 b hb) n u
    have hq_nn : 0 ≤ denQ (subWord n u) + denP (subWord n u) * (1 / ((a.1 : ℝ) + x)) :=
      add_nonneg (denQ_pos hpd).le (mul_nonneg (denP_nonneg _) (by positivity))
    rw [← Real.mul_rpow hax_pos.le hq_nn, subWord_snoc, denQ_snoc, denP_snoc]
    congr 1
    field_simp [hax_pos.ne']
    ring
  simp_rw [hstep]
  have hsplit := (summable_multiResolventV hS1 hs hx hsum).tsum_eq_zero_add
  have h0 : (∑ w : Fin 0 → {b : ℕ // b ∈ S},
      (denQ (subWord 0 w) + denP (subWord 0 w) * x) ^ (-(2 * s))) = 1 := by
    letI : Unique (Fin 0 → {b : ℕ // b ∈ S}) :=
      { default := fun i => i.elim0
        uniq := fun f => funext fun i => i.elim0 }
    rw [Fintype.sum_unique]
    have hsub0 : subWord (A := (S : Set ℕ)) 0 default = [] := rfl
    rw [hsub0, denQ_nil, denP_nil, zero_mul, add_zero, Real.one_rpow]
  change (∑' n : ℕ, ∑ w : Fin (n + 1) → {b : ℕ // b ∈ S},
      (denQ (subWord (n + 1) w) + denP (subWord (n + 1) w) * x) ^ (-(2 * s))) =
    multiResolventV S s x - 1
  unfold multiResolventV at hsplit ⊢
  linarith [hsplit, h0]

lemma transferOp_add {A : Set ℕ} (s : ℝ) (v₁ v₂ : ℝ → ℝ≥0∞) (x : ℝ) :
    transferOp A s (fun y => v₁ y + v₂ y) x =
      transferOp A s v₁ x + transferOp A s v₂ x := by
  unfold transferOp
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun a => ?_
  split_ifs with ha
  · simp [add_mul]
  · simp

lemma transferOp_finset_sum {A : Set ℕ} (s : ℝ) {ι : Type*} (I : Finset ι)
    (v : ι → ℝ → ℝ≥0∞) (x : ℝ) :
    transferOp A s (fun y => ∑ i ∈ I, v i y) x =
      ∑ i ∈ I, transferOp A s (v i) x := by
  induction I using Finset.induction_on with
  | empty => simp [transferOp]
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    rw [transferOp_add, ih]

/-- Exact `n`-th iterate formula for `(L_s^S)^n 1`. -/
theorem transferOp_iterate_one_eq (S : Finset ℕ) (hS1 : ∀ a ∈ S, 1 ≤ a)
    {s : ℝ} (hs : 0 < s) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (transferOp (S : Set ℕ) s)^[n] (fun _ => 1) x =
      ENNReal.ofReal (∑ w : Fin n → {a : ℕ // a ∈ S},
        (denQ (subWord n w) + denP (subWord n w) * x) ^ (-(2 * s))) := by
  induction n generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    letI : Unique (Fin 0 → {a : ℕ // a ∈ S}) :=
      { default := fun i => i.elim0
        uniq := fun f => funext fun i => i.elim0 }
    rw [Fintype.sum_unique]
    have hsub0 : subWord (A := (S : Set ℕ)) 0 default = [] := rfl
    rw [hsub0, denQ_nil, denP_nil, zero_mul, add_zero, Real.one_rpow, ENNReal.ofReal_one]
  | succ n ih =>
    rw [Function.iterate_succ_apply', transferOp_finset_eq]
    rw [← Finset.sum_attach S (fun a =>
      ((transferOp (S : Set ℕ) s)^[n] (fun _ => 1)) (1 / ((a : ℝ) + x)) *
        ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))))]
    have hstep : ∀ a : {a : ℕ // a ∈ S},
        ((transferOp (S : Set ℕ) s)^[n] (fun _ => 1)) (1 / ((a.1 : ℝ) + x)) *
          ENNReal.ofReal (((a.1 : ℝ) + x) ^ (-(2 * s))) =
          ENNReal.ofReal (∑ u : Fin n → {b : ℕ // b ∈ S},
            (denQ (subWord (n + 1) (Fin.snoc u a)) +
              denP (subWord (n + 1) (Fin.snoc u a)) * x) ^ (-(2 * s))) := by
      intro a
      have haR : (1 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast hS1 a.1 a.2
      have hax : 0 < (a.1 : ℝ) + x := by linarith [hx.1]
      have hy : 1 / ((a.1 : ℝ) + x) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by positivity, (div_le_one hax).mpr (by linarith [hx.1])⟩
      rw [ih hy]
      have hnn : ∀ u : Fin n → {b : ℕ // b ∈ S},
          0 ≤ (denQ (subWord n u) + denP (subWord n u) * (1 / ((a.1 : ℝ) + x))) ^ (-(2 * s)) :=
        fun u => Real.rpow_nonneg (add_nonneg
          (denQ_pos (posDigits_subWord (fun b hb => hS1 b hb) n u)).le
          (mul_nonneg (denP_nonneg _) hy.1)) _
      rw [← ENNReal.ofReal_mul (Finset.sum_nonneg fun u _ => hnn u), Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun u _ => ?_
      have hpd := posDigits_subWord (fun b hb => hS1 b hb) n u
      have hq_nn : 0 ≤ denQ (subWord n u) + denP (subWord n u) * (1 / ((a.1 : ℝ) + x)) :=
        add_nonneg (denQ_pos hpd).le (mul_nonneg (denP_nonneg _) hy.1)
      rw [← Real.mul_rpow hq_nn hax.le, subWord_snoc, denQ_snoc, denP_snoc]
      congr 1
      field_simp [hax.ne']
      ring
    simp_rw [hstep]
    have hnn_all : ∀ a : {a : ℕ // a ∈ S}, 0 ≤ ∑ u : Fin n → {b : ℕ // b ∈ S},
        (denQ (subWord (n + 1) (Fin.snoc u a)) +
          denP (subWord (n + 1) (Fin.snoc u a)) * x) ^ (-(2 * s)) := fun a =>
      Finset.sum_nonneg fun u _ => Real.rpow_nonneg (add_nonneg
        (denQ_pos (posDigits_subWord (fun b hb => hS1 b hb) (n + 1) (Fin.snoc u a))).le
        (mul_nonneg (denP_nonneg _) hx.1)) _
    rw [← Finset.univ_eq_attach]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hnn_all a)]
    congr 1
    rw [← Equiv.sum_comp (finSnocEquivLocal (α := {b : ℕ // b ∈ S}) n).symm, Fintype.sum_prod_type,
      Finset.sum_comm]
    rfl

lemma transferOp_iterate_one_le {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {s : ℝ} (hs : 0 < s) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (transferOp (S : Set ℕ) s)^[n] (fun _ => 1) x ≤ (S.card : ℝ≥0∞) ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hmono : transferOp (S : Set ℕ) s ((transferOp (S : Set ℕ) s)^[n] (fun _ => 1)) x ≤
        transferOp (S : Set ℕ) s (fun _ => (S.card : ℝ≥0∞) ^ n) x :=
      transferOp_mono (fun y hy => ih hy) (fun a ha => hS1 a ha) hx
    refine hmono.trans ?_
    rw [transferOp_finset_eq]
    calc ∑ a ∈ S, (S.card : ℝ≥0∞) ^ n * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))
        ≤ ∑ _a ∈ S, (S.card : ℝ≥0∞) ^ n * 1 := by
          refine Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ bot_le
          have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hS1 a ha
          have hpow : ((a : ℝ) + x) ^ (-(2 * s)) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.1]) (by linarith)
          exact ENNReal.ofReal_le_one.mpr hpow
      _ = (S.card : ℝ≥0∞) ^ (n + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, pow_succ']

/-- **Bowen-Free Continuant Poincaré-Abscissa Dimension Formula**:
    for every nonempty finite positive-digit alphabet `S`, `dimH (cfAlphabetSet S) = poincareAbscissa S`. -/
theorem dimH_cfAlphabetSet_finset_eq_poincareAbscissa {S : Finset ℕ}
    (hSne : S.Nonempty) (hS1 : ∀ a ∈ S, 1 ≤ a) :
    dimH (cfAlphabetSet (S : Set ℕ)) = ENNReal.ofReal (poincareAbscissa S) := by
  have hupper_of_sum : ∀ {s : ℝ}, 0 < s → Summable (wordSum S (2 * s)) →
      dimH (cfAlphabetSet (S : Set ℕ)) ≤ ENNReal.ofReal s := by
    intro s hs_pos hsum
    let v : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (multiResolventV S s x)
    have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal 1 ≤ v x ∧ v x ≤ ENNReal.ofReal (multiC S (2 * s)) := fun x hx =>
      ⟨ENNReal.ofReal_le_ofReal (one_le_multiResolventV hS1 hs_pos hx.1 hsum),
        ENNReal.ofReal_le_ofReal (multiResolventV_le_multiC hS1 hs_pos hx.1 hsum)⟩
    have hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1, transferOp (S : Set ℕ) s v x ≤ v x := by
      intro x hx
      rw [transferOp_finset_eq]
      have hnn : ∀ a ∈ S, 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) *
          multiResolventV S s (1 / ((a : ℝ) + x)) := fun a ha => by
        have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hS1 a ha
        have hax : 0 < (a : ℝ) + x := by linarith [hx.1]
        have hy : 0 ≤ 1 / ((a : ℝ) + x) := div_nonneg zero_le_one hax.le
        exact mul_nonneg (Real.rpow_nonneg hax.le _)
          (le_trans zero_le_one (one_le_multiResolventV hS1 hs_pos hy hsum))
      have hrew : (∑ a ∈ S, v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))) =
          ENNReal.ofReal (∑ a ∈ S, ((a : ℝ) + x) ^ (-(2 * s)) *
            multiResolventV S s (1 / ((a : ℝ) + x))) := by
        rw [ENNReal.ofReal_sum_of_nonneg hnn]
        refine Finset.sum_congr rfl fun a ha => ?_
        have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hS1 a ha
        have hax : 0 < (a : ℝ) + x := by linarith [hx.1]
        rw [mul_comm (v _), ← ENNReal.ofReal_mul (Real.rpow_nonneg hax.le _)]
      rw [hrew, multiResolventV_branch_eq hS1 hs_pos hx.1 hsum]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    exact dimH_le_of_transferOp_le (fun a ha => hS1 a ha) hs_pos
      (by simp : (0 : ℝ≥0∞) < ENNReal.ofReal 1) ENNReal.ofReal_lt_top hv_bd hsub
  have hdim_le_one : dimH (cfAlphabetSet (S : Set ℕ)) ≤ ENNReal.ofReal 1 :=
    hupper_of_sum zero_lt_one (by simpa using summable_wordSum_two hS1)
  have hne_top : dimH (cfAlphabetSet (S : Set ℕ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdim_le_one
  have htoReal_le : (dimH (cfAlphabetSet (S : Set ℕ))).toReal ≤ poincareAbscissa S := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    let s : ℝ := poincareAbscissa S + ε
    have hs_gt : poincareAbscissa S < s := by dsimp [s]; linarith
    have hs_pos : 0 < s := lt_of_le_of_lt (poincareAbscissa_nonneg S) hs_gt
    have hle := hupper_of_sum hs_pos (summable_wordSum_of_poincareAbscissa_lt hS1 hs_gt)
    exact ENNReal.toReal_le_of_le_ofReal hs_pos.le hle
  have hle_toReal : poincareAbscissa S ≤ (dimH (cfAlphabetSet (S : Set ℕ))).toReal := by
    rcases eq_or_lt_of_le (poincareAbscissa_nonneg S) with h0 | hs₀_pos
    · rw [← h0]; exact ENNReal.toReal_nonneg
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hε_ge : poincareAbscissa S ≤ ε
    · linarith [ENNReal.toReal_nonneg (a := dimH (cfAlphabetSet (S : Set ℕ)))]
    push Not at hε_ge
    let s : ℝ := poincareAbscissa S - ε / 2
    have hs_pos : 0 < s := by dsimp [s]; linarith
    have hs_lt : s < poincareAbscissa S := by dsimp [s]; linarith
    let s' : ℝ := (s + poincareAbscissa S) / 2
    have hs'_pos : 0 < s' := by dsimp [s']; linarith
    have hs'_lt : s' < poincareAbscissa S := by dsimp [s']; linarith
    have hnot : ¬ Summable (wordSum S (2 * s')) :=
      not_summable_wordSum_of_lt_poincareAbscissa hs'_pos hs'_lt
    have hge1 : ∀ n ≥ 1, 1 ≤ wordSum S (2 * s') n := fun n hn => by
      by_contra hlt
      push Not at hlt
      exact hnot ((summable_wordSum_iff_exists_lt_one hS1 (by linarith)).mpr ⟨n, hn, hlt⟩)
    have hword_grow : ∀ n : ℕ, 1 ≤ n →
        (2 : ℝ) ^ ((s' - s) * ((n : ℝ) - 1)) ≤ wordSum S (2 * s) n := by
      intro n hn
      have hexp : (2 : ℝ) ^ ((s' - s) * ((n : ℝ) - 1)) * wordSum S (2 * s') n ≤
          wordSum S (2 * s) n := by
        unfold wordSum
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun w _ => ?_
        have hpd := posDigits_subWord (fun a ha => hS1 a ha) n w
        have hq_pos : 0 < denQ (subWord n w) := denQ_pos hpd
        have hpow_ge : (2 : ℝ) ^ ((n : ℝ) / 2 - 1 / 2) ≤ denQ (subWord n w) := by
          have hrem : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
          have hm : n % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt n (by norm_num))
          have hnat' : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) := by exact_mod_cast hrem
          have hm' : ((n % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hm
          have h1 : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by linarith
          have h2 : (2 : ℝ) ^ ((n : ℝ) / 2 - 1 / 2) ≤ (2 : ℝ) ^ ((n / 2 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
          have h3 : (2 : ℝ) ^ ((n / 2 : ℕ) : ℝ) = (2 : ℝ) ^ (n / 2) := by
            rw [Real.rpow_natCast]
          have h4 : (2 : ℝ) ^ (n / 2) ≤ denQ (subWord n w) := by
            simpa [subWord_length] using denQ_pow_two_le hpd
          exact h2.trans (h3 ▸ h4)
        have hpow_diff : (2 : ℝ) ^ ((s' - s) * ((n : ℝ) - 1)) ≤
            denQ (subWord n w) ^ (2 * (s' - s)) := by
          have h2s : (2 : ℝ) ^ ((s' - s) * ((n : ℝ) - 1)) =
              ((2 : ℝ) ^ ((n : ℝ) / 2 - 1 / 2)) ^ (2 * (s' - s)) := by
            rw [← Real.rpow_mul (by norm_num)]
            congr 1; ring
          rw [h2s]
          exact Real.rpow_le_rpow (by positivity) hpow_ge (by dsimp [s']; linarith)
        have hsplit : denQ (subWord n w) ^ (-(2 * s)) =
            denQ (subWord n w) ^ (2 * (s' - s)) * denQ (subWord n w) ^ (-(2 * s')) := by
          rw [← Real.rpow_add hq_pos]
          congr 1; ring
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right hpow_diff (Real.rpow_nonneg hq_pos.le _)
      exact (le_mul_of_one_le_right (by positivity) (hge1 n hn)).trans hexp
    have htend : Tendsto (fun n : ℕ => (2 : ℝ) ^ ((s' - s) * ((n : ℝ) - 1))) atTop atTop := by
      have hexp_eq : (fun n : ℕ => (2 : ℝ) ^ ((s' - s) * ((n : ℝ) - 1))) =
          fun n : ℕ => Real.exp (Real.log 2 * ((s' - s) * ((n : ℝ) - 1))) := by
        funext n; rw [Real.rpow_def_of_pos (by norm_num)]
      rw [hexp_eq]
      have hlin' : Tendsto (fun n : ℕ => Real.log 2 * ((s' - s) * ((n : ℝ) - 1))) atTop atTop := by
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hss : 0 < s' - s := by dsimp [s']; linarith
        refine tendsto_atTop_atTop.mpr fun B => ?_
        obtain ⟨N, hN⟩ := exists_nat_gt (B / (Real.log 2 * (s' - s)) + 1)
        refine ⟨N, fun n hn => ?_⟩
        have hNR : B / (Real.log 2 * (s' - s)) + 1 < (n : ℝ) :=
          lt_of_lt_of_le hN (by exact_mod_cast hn)
        have hlt_sub : B / (Real.log 2 * (s' - s)) < (n : ℝ) - 1 := by linarith
        have h1 : B < ((n : ℝ) - 1) * (Real.log 2 * (s' - s)) :=
          (div_lt_iff₀ (mul_pos hlog2 hss)).mp hlt_sub
        linarith
      exact Real.tendsto_exp_atTop.comp hlin'
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htend.eventually_ge_atTop ((2 : ℝ) ^ (2 * s)))
    let n₀ : ℕ := max N 1
    have hn₀1 : 1 ≤ n₀ := le_max_right _ _
    have hword_big : (2 : ℝ) ^ (2 * s) ≤ wordSum S (2 * s) n₀ :=
      (hN n₀ (le_max_left _ _)).trans (hword_grow n₀ hn₀1)
    have hiter_ge : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (1 : ℝ≥0∞) ≤ (transferOp (S : Set ℕ) s)^[n₀] (fun _ => 1) x := by
      intro x hx
      rw [transferOp_iterate_one_eq S hS1 hs_pos n₀ hx]
      have hreal_ge : (1 : ℝ) ≤ ∑ w : Fin n₀ → {a : ℕ // a ∈ S},
          (denQ (subWord n₀ w) + denP (subWord n₀ w) * x) ^ (-(2 * s)) := by
        have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 * s) := Real.rpow_pos_of_pos (by norm_num) _
        have hdiv : (2 : ℝ) ^ (-(2 * s)) * wordSum S (2 * s) n₀ ≤
            ∑ w : Fin n₀ → {a : ℕ // a ∈ S},
              (denQ (subWord n₀ w) + denP (subWord n₀ w) * x) ^ (-(2 * s)) := by
          unfold wordSum
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun w _ => ?_
          have hpd := posDigits_subWord (fun a ha => hS1 a ha) n₀ w
          have hq_pos : 0 < denQ (subWord n₀ w) := denQ_pos hpd
          have hp_nn : 0 ≤ denP (subWord n₀ w) := denP_nonneg _
          have hp_le : denP (subWord n₀ w) ≤ denQ (subWord n₀ w) := denP_le_denQ hpd
          have hle2 : denQ (subWord n₀ w) + denP (subWord n₀ w) * x ≤
              2 * denQ (subWord n₀ w) := by
            nlinarith [hx.1, hx.2]
          have hadd_pos : 0 < denQ (subWord n₀ w) + denP (subWord n₀ w) * x :=
            add_pos_of_pos_of_nonneg hq_pos (mul_nonneg hp_nn hx.1)
          have hpow := Real.rpow_le_rpow_of_nonpos hadd_pos hle2
            (neg_nonpos.mpr (mul_nonneg zero_le_two hs_pos.le))
          rw [Real.mul_rpow (by norm_num) hq_pos.le] at hpow
          exact hpow
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (-(2 * s)) * (2 : ℝ) ^ (2 * s) := by
          rw [Real.rpow_neg (by norm_num), inv_mul_cancel₀ h2pos.ne']
        exact h1.trans ((mul_le_mul_of_nonneg_left hword_big
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)).trans hdiv)
      simpa using ENNReal.ofReal_le_ofReal hreal_ge
    let v : ℝ → ℝ≥0∞ := fun x =>
      ∑ j ∈ Finset.range n₀, (transferOp (S : Set ℕ) s)^[j] (fun _ => 1) x
    have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (1 : ℝ≥0∞) ≤ v x ∧ v x ≤ ∑ j ∈ Finset.range n₀, (S.card : ℝ≥0∞) ^ j := by
      intro x hx
      constructor
      · refine Finset.single_le_sum (f := fun j => (transferOp (S : Set ℕ) s)^[j] (fun _ => 1) x)
          (fun _ _ => bot_le) (Finset.mem_range.mpr hn₀1) |>.trans_eq' ?_
        simp
      · exact Finset.sum_le_sum fun j _ => transferOp_iterate_one_le hS1 hs_pos j hx
    have hhi_lt : (∑ j ∈ Finset.range n₀, (S.card : ℝ≥0∞) ^ j) < ⊤ := by
      refine ENNReal.sum_lt_top.mpr fun j _ => ?_
      exact ENNReal.pow_lt_top (ENNReal.natCast_lt_top S.card)
    have hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1, v x ≤ transferOp (S : Set ℕ) s v x := by
      intro x hx
      have hadd1 : v x + 1 ≤ v x + (transferOp (S : Set ℕ) s)^[n₀] (fun _ => 1) x :=
        add_le_add le_rfl (hiter_ge x hx)
      have hlhs : v x + (transferOp (S : Set ℕ) s)^[n₀] (fun _ => 1) x =
          ∑ j ∈ Finset.range (n₀ + 1), (transferOp (S : Set ℕ) s)^[j] (fun _ => 1) x := by
        rw [Finset.sum_range_succ]
      have hrhs : ∑ j ∈ Finset.range (n₀ + 1), (transferOp (S : Set ℕ) s)^[j] (fun _ => 1) x =
          1 + transferOp (S : Set ℕ) s v x := by
        rw [Finset.sum_range_succ', Function.iterate_zero, id_eq, add_comm]
        congr 1
        dsimp only [v]
        rw [transferOp_finset_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Function.iterate_succ_apply' (transferOp (S : Set ℕ) s) j (fun _ => 1)]
      rw [hlhs, hrhs, add_comm (v x) 1] at hadd1
      exact (ENNReal.add_le_add_iff_left (by simp)).mp hadd1
    have hdim_ge := le_dimH_of_transferOp_ge hSne hS1 hs_pos zero_lt_one hhi_lt hv_bd hsuper
    have hs_toReal := (ENNReal.ofReal_le_iff_le_toReal hne_top).mp hdim_ge
    dsimp [s] at hs_toReal
    linarith
  have heq : (dimH (cfAlphabetSet (S : Set ℕ))).toReal = poincareAbscissa S :=
    le_antisymm htoReal_le hle_toReal
  rw [← ENNReal.ofReal_toReal hne_top, heq]

/-! ### Part 3: Multi-Residue Alphabets `multiResidueSet`, Universal Limit, & Phase Witnesses -/

/-- Combined multi-residue digit alphabet: `a ≡ r [MOD m]` with `a ≥ r` for `r ∈ S`,
    or `a ≡ -b [MOD m]` with `a ≥ 1` for `b ∈ B`. -/
def multiResidueAlphabet (m : ℕ) (S B : Finset ℕ) : Set ℕ :=
  {a : ℕ | (∃ r ∈ S, r ≤ a ∧ a % m = r % m) ∨
    (∃ b ∈ B, ∃ k : ℕ, 1 ≤ k ∧ a + b = k * m ∧ 1 ≤ a)}

/-- Multi-residue continued-fraction Cantor set `F_{m, S, B} = cfAlphabetSet (multiResidueAlphabet m S B)`. -/
def multiResidueSet (m : ℕ) (S B : Finset ℕ) : Set ℝ :=
  cfAlphabetSet (multiResidueAlphabet m S B)

lemma multiResidueAlphabet_ge_one {m : ℕ} {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) :
    ∀ a ∈ multiResidueAlphabet m S B, 1 ≤ a := by
  rintro a (⟨r, hr, hra, _⟩ | ⟨b, _, _, _, _, ha1⟩)
  · exact le_trans (hS1 r hr) hra
  · exact ha1

lemma multiResidueSet_singleton_eq (m r : ℕ) :
    multiResidueSet m {r} ∅ = residueConstSet m r := by
  ext x
  simp [multiResidueSet, multiResidueAlphabet, cfAlphabetSet, residueConstSet, residueSeqSet]

lemma multiResidueSet_empty_zero_eq {m : ℕ} (hm : 1 ≤ m) :
    multiResidueSet m ∅ {0} = residueConstSet m m := by
  ext x
  constructor
  · rintro ⟨hx01, hirr, hres⟩
    refine ⟨hx01, hirr, fun i => ?_⟩
    rcases hres i with ⟨r, hr, _⟩ | ⟨b, hb, k, hk1, hkm, _⟩
    · simp at hr
    · rw [Finset.mem_singleton] at hb
      subst hb
      rw [add_zero] at hkm
      refine ⟨by rw [hkm]; exact Nat.le_mul_of_pos_left m hk1, ?_⟩
      rw [hkm, Nat.mul_mod_left, Nat.mod_self]
  · rintro ⟨hx01, hirr, hres⟩
    refine ⟨hx01, hirr, fun i => Or.inr ⟨0, Finset.mem_singleton_self 0, ?_⟩⟩
    obtain ⟨hle, hmod⟩ := hres i
    dsimp only at hle hmod
    rw [Nat.mod_self] at hmod
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk_eq : k = 0 := by omega
      rw [hk_eq, mul_zero] at hk
      omega
    exact ⟨k, hk1, by rw [add_zero, hk, mul_comm], le_trans hm hle⟩

lemma transferOp_multiResidueAlphabet_eq {m : ℕ} {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hm : S.sup id + B.sup id + 1 ≤ m)
    (s : ℝ) (v : ℝ → ℝ≥0∞) (x : ℝ) :
    transferOp (multiResidueAlphabet m S B) s v x =
      transferOp (S : Set ℕ) s v x +
      (∑ r ∈ S, ∑' k : ℕ,
        v (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ENNReal.ofReal (((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) +
      (∑ b ∈ B, ∑' k : ℕ,
        v (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ENNReal.ofReal (((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))) := by
  let g : ℕ → ℝ≥0∞ := fun a =>
    v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))
  suffices hgoal :
      (∑' a : ℕ, if a ∈ multiResidueAlphabet m S B then g a else 0) =
        (∑' a : ℕ, if a ∈ S then g a else 0) +
          (∑ r ∈ S, ∑' k : ℕ, g ((k + 1) * m + r)) +
          (∑ b ∈ B, ∑' k : ℕ, g ((k + 1) * m - b)) by
    unfold transferOp
    trans ((∑' a : ℕ, if a ∈ S then g a else 0) +
      (∑ r ∈ S, ∑' k : ℕ, g ((k + 1) * m + r)) +
      (∑ b ∈ B, ∑' k : ℕ, g ((k + 1) * m - b)))
    · exact (tsum_congr fun a => by split_ifs <;> simp_all [g]).trans hgoal
    · congr 2
      refine tsum_congr fun a => ?_
      split_ifs <;> simp_all [g]
  have hr_lt_m : ∀ r ∈ S, r < m := fun r hr => by
    have hle : r ≤ S.sup id := Finset.le_sup (f := id) hr
    omega
  have hb_lt_m : ∀ b ∈ B, b < m := fun b hb => by
    have hle : b ≤ B.sup id := Finset.le_sup (f := id) hb
    omega
  have hrb_lt_m : ∀ r ∈ S, ∀ b ∈ B, r + b < m := fun r hr b hb => by
    have h1 : r ≤ S.sup id := Finset.le_sup (f := id) hr
    have h2 : b ≤ B.sup id := Finset.le_sup (f := id) hb
    omega
  have hm_pos : 0 < m := by omega
  have hsum_comm : ∀ (P : ℕ → ℕ → ℝ≥0∞) (T : Finset ℕ),
      (∑ x ∈ T, ∑' a : ℕ, P x a) = ∑' a : ℕ, ∑ x ∈ T, P x a := by
    intro P T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert t T' ht ih =>
      simp only [Finset.sum_insert ht, ih, ENNReal.tsum_add]
  have hsum_S : (∑ r ∈ S, ∑' a : ℕ, if (∃ k : ℕ, a = (k + 1) * m + r) then g a else 0) =
      ∑' a : ℕ, ∑ r ∈ S, if (∃ k : ℕ, a = (k + 1) * m + r) then g a else 0 :=
    hsum_comm _ S
  have hsum_B : (∑ b ∈ B, ∑' a : ℕ, if (∃ k : ℕ, a = (k + 1) * m - b) then g a else 0) =
      ∑' a : ℕ, ∑ b ∈ B, if (∃ k : ℕ, a = (k + 1) * m - b) then g a else 0 :=
    hsum_comm _ B
  have hbij_S : ∀ r ∈ S,
      (∑' a : ℕ, if (∃ k : ℕ, a = (k + 1) * m + r) then g a else 0) =
        ∑' k : ℕ, g ((k + 1) * m + r) := by
    intro r _
    let img : Set ℕ := Set.range (fun k : ℕ => (k + 1) * m + r)
    have hinj : Function.Injective (fun k : ℕ => (k + 1) * m + r) := fun k₁ k₂ h => by
      dsimp only at h
      have h' : (k₁ + 1) * m = (k₂ + 1) * m := Nat.add_right_cancel h
      have h'' := Nat.mul_right_cancel hm_pos h'
      omega
    trans (∑' a : ℕ, img.indicator g a)
    · refine tsum_congr fun a => ?_
      simp [Set.indicator_apply, img, eq_comm]
    · rw [← tsum_subtype img g]
      simpa using (Equiv.tsum_eq (Equiv.ofInjective (fun k : ℕ => (k + 1) * m + r) hinj)
        (fun a : img => g a.1)).symm
  have hbij_B : ∀ b ∈ B,
      (∑' a : ℕ, if (∃ k : ℕ, a = (k + 1) * m - b) then g a else 0) =
        ∑' k : ℕ, g ((k + 1) * m - b) := by
    intro b hb
    have hbm : b < m := hb_lt_m b hb
    let img : Set ℕ := Set.range (fun k : ℕ => (k + 1) * m - b)
    have hinj : Function.Injective (fun k : ℕ => (k + 1) * m - b) := fun k₁ k₂ h => by
      dsimp only at h
      have hm1 : m ≤ (k₁ + 1) * m := Nat.le_mul_of_pos_left m (by omega)
      have hm2 : m ≤ (k₂ + 1) * m := Nat.le_mul_of_pos_left m (by omega)
      have heq : (k₁ + 1) * m = (k₂ + 1) * m := by omega
      have h'' := Nat.mul_right_cancel hm_pos heq
      omega
    trans (∑' a : ℕ, img.indicator g a)
    · refine tsum_congr fun a => ?_
      simp [Set.indicator_apply, img, eq_comm]
    · rw [← tsum_subtype img g]
      simpa using (Equiv.tsum_eq (Equiv.ofInjective (fun k : ℕ => (k + 1) * m - b) hinj)
        (fun a : img => g a.1)).symm
  rw [← Finset.sum_congr rfl hbij_S, ← Finset.sum_congr rfl hbij_B, hsum_S, hsum_B,
    ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine tsum_congr fun a => ?_
  have hS_disj : ∀ r₁ ∈ S, ∀ r₂ ∈ S, (∃ k : ℕ, a = (k + 1) * m + r₁) →
      (∃ k : ℕ, a = (k + 1) * m + r₂) → r₁ = r₂ := by
    rintro r₁ hr₁ r₂ hr₂ ⟨k₁, rfl⟩ ⟨k₂, h2⟩
    have hm1 := hr_lt_m r₁ hr₁
    have hm2 := hr_lt_m r₂ hr₂
    have hmod := congrArg (· % m) h2
    simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod] at hmod
    rwa [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2] at hmod
  have hB_disj : ∀ b₁ ∈ B, ∀ b₂ ∈ B, (∃ k : ℕ, a = (k + 1) * m - b₁) →
      (∃ k : ℕ, a = (k + 1) * m - b₂) → b₁ = b₂ := by
    rintro b₁ hb₁ b₂ hb₂ ⟨k₁, h1⟩ ⟨k₂, h2⟩
    have hm1 := hb_lt_m b₁ hb₁
    have hm2 := hb_lt_m b₂ hb₂
    have hm_le1 : m ≤ (k₁ + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    have hm_le2 : m ≤ (k₂ + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    have h1_nat : a + b₁ = (k₁ + 1) * m := by omega
    have h2_nat : a + b₂ = (k₂ + 1) * m := by omega
    have hZ : (((k₁ + 1 : ℤ) - (k₂ + 1 : ℤ)) * (m : ℤ)) = (b₁ : ℤ) - (b₂ : ℤ) := by
      have h1Z : (a : ℤ) + (b₁ : ℤ) = ((k₁ + 1 : ℤ)) * (m : ℤ) := by exact_mod_cast h1_nat
      have h2Z : (a : ℤ) + (b₂ : ℤ) = ((k₂ + 1 : ℤ)) * (m : ℤ) := by exact_mod_cast h2_nat
      linarith
    have hdiff_lt : |((k₁ + 1 : ℤ) - (k₂ + 1 : ℤ)) * (m : ℤ)| < (m : ℤ) := by
      rw [hZ, abs_lt]
      constructor <;> omega
    have hdiff0 : (k₁ + 1 : ℤ) - (k₂ + 1 : ℤ) = 0 := by
      rw [abs_mul, abs_of_pos (by exact_mod_cast hm_pos : (0 : ℤ) < m)] at hdiff_lt
      nlinarith [abs_nonneg ((k₁ + 1 : ℤ) - (k₂ + 1 : ℤ))]
    rw [hdiff0, zero_mul] at hZ
    omega
  have hSB_disj : ∀ r ∈ S, ∀ b ∈ B, (∃ k : ℕ, a = (k + 1) * m + r) →
      ¬ (∃ k : ℕ, a = (k + 1) * m - b) := by
    rintro r hr b hb ⟨k₁, h1⟩ ⟨k₂, h2⟩
    have hbm := hb_lt_m b hb
    have hm_le2 : m ≤ (k₂ + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    have h2_nat : a + b = (k₂ + 1) * m := by omega
    have hZ : ((k₂ + 1 : ℤ) - (k₁ + 1 : ℤ)) * (m : ℤ) = (r : ℤ) + (b : ℤ) := by
      have h1Z : (a : ℤ) = ((k₁ + 1 : ℤ)) * (m : ℤ) + (r : ℤ) := by exact_mod_cast h1
      have h2Z : (a : ℤ) + (b : ℤ) = ((k₂ + 1 : ℤ)) * (m : ℤ) := by exact_mod_cast h2_nat
      linarith
    have hr1 : 1 ≤ r := hS1 r hr
    have hrb := hrb_lt_m r hr b hb
    have hpos : 0 < (k₂ + 1 : ℤ) - (k₁ + 1 : ℤ) := by
      by_contra hle0
      have h1' : ((k₂ + 1 : ℤ) - (k₁ + 1 : ℤ)) * (m : ℤ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hle0) (by positivity)
      omega
    have hge_m : (m : ℤ) ≤ ((k₂ + 1 : ℤ) - (k₁ + 1 : ℤ)) * (m : ℤ) :=
      le_mul_of_one_le_left (by positivity) (by omega)
    omega
  have ha_S_lt : a ∈ S → ∀ r ∈ S, ¬ (∃ k : ℕ, a = (k + 1) * m + r) := by
    rintro haS r _ ⟨k, hak⟩
    have hm1 := hr_lt_m a haS
    have hge : m ≤ (k + 1) * m + r := le_trans (Nat.le_mul_of_pos_left m (by omega)) (Nat.le_add_right _ _)
    omega
  have ha_B_lt : a ∈ S → ∀ b ∈ B, ¬ (∃ k : ℕ, a = (k + 1) * m - b) := by
    rintro haS b hb ⟨k, hak⟩
    have h1 : a ≤ S.sup id := Finset.le_sup (f := id) haS
    have h2 : b ≤ B.sup id := Finset.le_sup (f := id) hb
    have hge : m ≤ (k + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    omega
  have hmem_iff : a ∈ multiResidueAlphabet m S B ↔
      a ∈ S ∨ (∃ r ∈ S, ∃ k : ℕ, a = (k + 1) * m + r) ∨
        (∃ b ∈ B, ∃ k : ℕ, a = (k + 1) * m - b) := by
    constructor
    · rintro (⟨r, hr, hra, hmod⟩ | ⟨b, hb, k, hk1, hkm, _⟩)
      · have hdvd : m ∣ (a - r) :=
          (Nat.modEq_iff_dvd' hra).mp (by simpa [Nat.ModEq] using hmod.symm)
        obtain ⟨q, hq⟩ := hdvd
        have ha_eq : a = q * m + r := by rw [mul_comm]; omega
        cases q with
        | zero =>
          rw [Nat.zero_mul, Nat.zero_add] at ha_eq
          exact Or.inl (ha_eq ▸ hr)
        | succ k => exact Or.inr (Or.inl ⟨r, hr, k, ha_eq⟩)
      · obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        rw [hk', Nat.succ_eq_add_one] at hkm
        exact Or.inr (Or.inr ⟨b, hb, k', by omega⟩)
    · rintro (haS | ⟨r, hr, k, rfl⟩ | ⟨b, hb, k, rfl⟩)
      · exact Or.inl ⟨a, haS, le_rfl, rfl⟩
      · refine Or.inl ⟨r, hr, Nat.le_add_left _ _, ?_⟩
        simp [Nat.add_mod]
      · have hbm : b < m := hb_lt_m b hb
        have hm_le : m ≤ (k + 1) * m := Nat.le_mul_of_pos_left m (by omega)
        have hle : b ≤ (k + 1) * m := le_trans hbm.le hm_le
        refine Or.inr ⟨b, hb, k + 1, by omega, Nat.sub_add_cancel hle, by omega⟩
  by_cases haS : a ∈ S
  · have hmem : a ∈ multiResidueAlphabet m S B := hmem_iff.mpr (Or.inl haS)
    have hS0 : (∑ r ∈ S, if (∃ k : ℕ, a = (k + 1) * m + r) then g a else 0) = 0 :=
      Finset.sum_eq_zero fun r hr => ite_eq_right_iff.mpr fun h => absurd h (ha_S_lt haS r hr)
    have hB0 : (∑ b ∈ B, if (∃ k : ℕ, a = (k + 1) * m - b) then g a else 0) = 0 :=
      Finset.sum_eq_zero fun b hb => ite_eq_right_iff.mpr fun h => absurd h (ha_B_lt haS b hb)
    simp [hmem, haS, hS0, hB0]
  · by_cases hexS : ∃ r ∈ S, ∃ k : ℕ, a = (k + 1) * m + r
    · obtain ⟨r₀, hr₀, hk₀⟩ := hexS
      have hmem : a ∈ multiResidueAlphabet m S B := hmem_iff.mpr (Or.inr (Or.inl ⟨r₀, hr₀, hk₀⟩))
      have hS_eq : (∑ r ∈ S, if (∃ k : ℕ, a = (k + 1) * m + r) then g a else 0) = g a := by
        rw [Finset.sum_eq_single r₀]
        · simp [hk₀]
        · intro r hr hne
          rw [ite_eq_right_iff]
          intro hkr
          exact absurd (hS_disj r hr r₀ hr₀ hkr hk₀) hne
        · intro hno; exact absurd hr₀ hno
      have hB0 : (∑ b ∈ B, if (∃ k : ℕ, a = (k + 1) * m - b) then g a else 0) = 0 :=
        Finset.sum_eq_zero fun b hb => ite_eq_right_iff.mpr fun h => absurd h (hSB_disj r₀ hr₀ b hb hk₀)
      simp [hmem, haS, hS_eq, hB0]
    · by_cases hexB : ∃ b ∈ B, ∃ k : ℕ, a = (k + 1) * m - b
      · obtain ⟨b₀, hb₀, hk₀⟩ := hexB
        have hmem : a ∈ multiResidueAlphabet m S B := hmem_iff.mpr (Or.inr (Or.inr ⟨b₀, hb₀, hk₀⟩))
        have hS0 : (∑ r ∈ S, if (∃ k : ℕ, a = (k + 1) * m + r) then g a else 0) = 0 :=
          Finset.sum_eq_zero fun r hr => ite_eq_right_iff.mpr fun hk => absurd ⟨r, hr, hk⟩ hexS
        have hB_eq : (∑ b ∈ B, if (∃ k : ℕ, a = (k + 1) * m - b) then g a else 0) = g a := by
          rw [Finset.sum_eq_single b₀]
          · simp [hk₀]
          · intro b hb hne
            rw [ite_eq_right_iff]
            intro hkb
            exact absurd (hB_disj b hb b₀ hb₀ hkb hk₀) hne
          · intro hno; exact absurd hb₀ hno
        simp [hmem, haS, hS0, hB_eq]
      · have hnot : a ∉ multiResidueAlphabet m S B := by
          intro hm
          rcases hmem_iff.mp hm with h1 | h2 | h3
          · exact haS h1
          · exact hexS h2
          · exact hexB h3
        have hS0 : (∑ r ∈ S, if (∃ k : ℕ, a = (k + 1) * m + r) then g a else 0) = 0 :=
          Finset.sum_eq_zero fun r hr => ite_eq_right_iff.mpr fun hk => absurd ⟨r, hr, hk⟩ hexS
        have hB0 : (∑ b ∈ B, if (∃ k : ℕ, a = (k + 1) * m - b) then g a else 0) = 0 :=
          Finset.sum_eq_zero fun b hb => ite_eq_right_iff.mpr fun hk => absurd ⟨b, hb, hk⟩ hexB
        simp [hnot, haS, hS0, hB0]

/-- Universal limit & phase transition for multi-residue continued-fraction sets:
    `dimH (multiResidueSet m S B) → max (1 / 2) (poincareAbscissa S)` as `m → ∞`. -/
theorem tendsto_dimH_multiResidueSet {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hd : 1 ≤ S.card + B.card) :
    Tendsto (fun m : ℕ => (dimH (multiResidueSet m S B)).toReal)
      atTop (nhds (max (1 / 2 : ℝ) (poincareAbscissa S))) := by
  let L : ℝ := max (1 / 2 : ℝ) (poincareAbscissa S)
  have hL_ge : (1 / 2 : ℝ) ≤ L := le_max_left _ _
  have hL_poin : poincareAbscissa S ≤ L := le_max_right _ _
  have hup_ev : ∀ ε > 0, ∀ᶠ m : ℕ in atTop,
      dimH (multiResidueSet m S B) ≤ ENNReal.ofReal (L + ε) := by
    intro ε hε
    let s : ℝ := L + ε
    have hs_gt_half : 1 / 2 < s := by dsimp [s]; linarith
    have hs_gt_poin : poincareAbscissa S < s := by dsimp [s]; linarith
    have hs_pos : 0 < s := by linarith
    have hsum : Summable (wordSum S (2 * s)) := summable_wordSum_of_poincareAbscissa_lt hS1 hs_gt_poin
    let C : ℝ := multiC S (2 * s)
    have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one (one_le_multiC hsum)
    let M_S : ℕ := S.sup id
    let M_B : ℕ := B.sup id
    let d : ℝ := (S.card + B.card : ℝ)
    have h2s1 : 0 < 2 * s - 1 := by linarith
    let A_const : ℝ := C * d * (1 + 1 / (2 * s - 1))
    have htend0 : Tendsto (fun m : ℕ => A_const * (((m - M_B : ℕ) : ℝ) ^ (-(2 * s))))
        atTop (nhds 0) := by
      have hlin : Tendsto (fun m : ℕ => ((m - M_B : ℕ) : ℝ)) atTop atTop := by
        refine tendsto_atTop_atTop.mpr fun B₀ => ⟨Nat.ceil (max B₀ 0) + M_B, fun m hm => ?_⟩
        have : (Nat.ceil (max B₀ 0) : ℝ) ≤ ((m - M_B : ℕ) : ℝ) := by
          exact_mod_cast (by omega : Nat.ceil (max B₀ 0) ≤ m - M_B)
        exact (le_max_left B₀ 0).trans ((Nat.le_ceil _).trans this)
      simpa [Function.comp_def, mul_zero] using
        ((tendsto_rpow_neg_atTop (by positivity : 0 < 2 * s)).comp hlin).const_mul A_const
    filter_upwards [eventually_ge_atTop (max 2 (2 * (M_S + M_B + 2))),
      htend0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with m hm hm_tail
    have hm_sep : M_S + M_B + 1 ≤ m := by
      have := le_trans (le_max_right _ _) hm; omega
    have hmB_ge1 : 1 ≤ m - M_B := by
      have := le_trans (le_max_right _ _) hm; omega
    have hmB_pos : (0 : ℝ) < ((m - M_B : ℕ) : ℝ) := by exact_mod_cast hmB_ge1
    let v : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (multiResolventV S s x)
    have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal 1 ≤ v x ∧ v x ≤ ENNReal.ofReal C := fun x hx =>
      ⟨ENNReal.ofReal_le_ofReal (one_le_multiResolventV hS1 hs_pos hx.1 hsum),
        ENNReal.ofReal_le_ofReal (multiResolventV_le_multiC hS1 hs_pos hx.1 hsum)⟩
    have hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        transferOp (multiResidueAlphabet m S B) s v x ≤ v x := by
      intro x hx
      rw [transferOp_multiResidueAlphabet_eq hS1 hm_sep s v x]
      have hS_part : transferOp (S : Set ℕ) s v x = ENNReal.ofReal (multiResolventV S s x - 1) := by
        rw [transferOp_finset_eq]
        have hnn : ∀ a ∈ S, 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) *
            multiResolventV S s (1 / ((a : ℝ) + x)) := fun a ha => by
          have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hS1 a ha
          have hax : 0 < (a : ℝ) + x := by linarith [hx.1]
          exact mul_nonneg (Real.rpow_nonneg hax.le _)
            (le_trans zero_le_one (one_le_multiResolventV hS1 hs_pos (by positivity) hsum))
        have hrew : (∑ a ∈ S, v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))) =
            ENNReal.ofReal (∑ a ∈ S, ((a : ℝ) + x) ^ (-(2 * s)) *
              multiResolventV S s (1 / ((a : ℝ) + x))) := by
          rw [ENNReal.ofReal_sum_of_nonneg hnn]
          refine Finset.sum_congr rfl fun a ha => ?_
          have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hS1 a ha
          have hax : 0 < (a : ℝ) + x := by linarith [hx.1]
          rw [mul_comm (v _), ← ENNReal.ofReal_mul (Real.rpow_nonneg hax.le _)]
        rw [hrew, multiResolventV_branch_eq hS1 hs_pos hx.1 hsum]
      have hshift_tail : ∀ a0 : ℕ, 1 ≤ a0 → (m - M_B) ≤ a0 →
          (∑' k : ℕ, v (1 / (((k * m + a0 : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((k * m + a0 : ℕ) : ℝ) + x) ^ (-(2 * s)))) ≤
            ENNReal.ofReal (C * (((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) * (1 + 1 / (2 * s - 1)))) := by
        intro a0 ha0_pos ha0_ge
        have ha0R_pos : 0 < ((a0 : ℕ) : ℝ) + x := by
          have : (1 : ℝ) ≤ (a0 : ℝ) := by exact_mod_cast ha0_pos
          linarith [hx.1]
        have hsplit : (∑' k : ℕ, v (1 / (((k * m + a0 : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((k * m + a0 : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
            v (1 / (((a0 : ℕ) : ℝ) + x)) * ENNReal.ofReal ((((a0 : ℕ) : ℝ) + x) ^ (-(2 * s))) +
            ∑' k : ℕ, if 1 ≤ k then
              v (1 / (((k * m + a0 : ℕ) : ℝ) + x)) *
                ENNReal.ofReal ((((k * m + a0 : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0 := by
          rw [ENNReal.tsum_eq_add_tsum_ite (0 : ℕ)]
          congr 1
          · simp
          · refine tsum_congr fun k => ?_
            by_cases hk : k = 0 <;> simp [hk, show 1 ≤ k ↔ k ≠ 0 by omega]
        have hk0_le : v (1 / (((a0 : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((a0 : ℕ) : ℝ) + x) ^ (-(2 * s))) ≤
            ENNReal.ofReal C * ENNReal.ofReal (((m - M_B : ℕ) : ℝ) ^ (-(2 * s))) := by
          have ha0R : ((m - M_B : ℕ) : ℝ) ≤ ((a0 : ℕ) : ℝ) + x := by
            have : ((m - M_B : ℕ) : ℝ) ≤ (a0 : ℝ) := by exact_mod_cast ha0_ge
            linarith [hx.1]
          have hv0 : v (1 / (((a0 : ℕ) : ℝ) + x)) ≤ ENNReal.ofReal C :=
            ENNReal.ofReal_le_ofReal (multiResolventV_le_multiC hS1 hs_pos
              (div_nonneg zero_le_one ha0R_pos.le) hsum)
          have hp0 : (((a0 : ℕ) : ℝ) + x) ^ (-(2 * s)) ≤ ((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) :=
            Real.rpow_le_rpow_of_nonpos hmB_pos ha0R (by linarith)
          exact mul_le_mul' hv0 (ENNReal.ofReal_le_ofReal hp0)
        have hktail_le : (∑' k : ℕ, if 1 ≤ k then
            v (1 / (((k * m + a0 : ℕ) : ℝ) + x)) *
              ENNReal.ofReal ((((k * m + a0 : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0) ≤
            ENNReal.ofReal C *
              ENNReal.ofReal ((((m - M_B : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) := by
          have h1 : (∑' k : ℕ, if 1 ≤ k then
              v (1 / (((k * m + a0 : ℕ) : ℝ) + x)) *
                ENNReal.ofReal ((((k * m + a0 : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0) ≤
              ENNReal.ofReal C * ∑' k : ℕ, if 1 ≤ k then
                ENNReal.ofReal ((((m * k + a0 : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0 := by
            rw [← ENNReal.tsum_mul_left]
            refine ENNReal.tsum_le_tsum fun k => ?_
            split_ifs with hk
            · rw [mul_comm k m]
              have hk_pos : 0 < (((m * k + a0 : ℕ) : ℝ) + x) := by
                have : (1 : ℝ) ≤ ((m * k + a0 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m * k + a0)
                linarith [hx.1]
              exact mul_le_mul_of_nonneg_right
                (ENNReal.ofReal_le_ofReal (multiResolventV_le_multiC hS1 hs_pos
                  (div_nonneg zero_le_one hk_pos.le) hsum))
                bot_le
            · simp
          have ht := tsum_arith_tail_le (by omega : 1 ≤ m) ha0_pos (by decide : 1 ≤ 1) hs_gt_half hx
          simp only [Nat.sub_self, mul_zero, zero_add] at ht
          have ha0_pow : ((a0 : ℝ) ^ (1 - 2 * s)) ≤ ((m - M_B : ℕ) : ℝ) ^ (1 - 2 * s) :=
            Real.rpow_le_rpow_of_nonpos hmB_pos (by exact_mod_cast ha0_ge) (by linarith)
          have ht' : (∑' k : ℕ, if 1 ≤ k then
              ENNReal.ofReal ((((m * k + a0 : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0) ≤
              ENNReal.ofReal ((((m - M_B : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) :=
            ht.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ha0_pow (by positivity)))
          exact h1.trans (mul_le_mul_of_nonneg_left ht' bot_le)
        have hm_pow_le : (((m - M_B : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)) ≤
            ((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) / (2 * s - 1) := by
          have hmB_le_m : ((m - M_B : ℕ) : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast Nat.sub_le m M_B
          have hnum : ((m - M_B : ℕ) : ℝ) ^ (1 - 2 * s) =
              ((m - M_B : ℕ) : ℝ) * ((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) := by
            rw [show (1 - 2 * s : ℝ) = 1 + -(2 * s) by ring, Real.rpow_add hmB_pos, Real.rpow_one]
          have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
          rw [hnum, div_le_div_iff₀ (mul_pos hm_pos h2s1) h2s1]
          have hnn : 0 ≤ ((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) * (2 * s - 1) :=
            mul_nonneg (Real.rpow_nonneg hmB_pos.le _) h2s1.le
          nlinarith [hmB_le_m, hnn]
        rw [hsplit]
        refine (add_le_add hk0_le hktail_le).trans ?_
        calc ENNReal.ofReal C * ENNReal.ofReal (((m - M_B : ℕ) : ℝ) ^ (-(2 * s))) +
              ENNReal.ofReal C *
                ENNReal.ofReal ((((m - M_B : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)))
            ≤ ENNReal.ofReal C * ENNReal.ofReal (((m - M_B : ℕ) : ℝ) ^ (-(2 * s))) +
              ENNReal.ofReal C *
                ENNReal.ofReal (((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) / (2 * s - 1)) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hm_pow_le) bot_le)
          _ = ENNReal.ofReal (C * (((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) * (1 + 1 / (2 * s - 1)))) := by
              rw [← ENNReal.ofReal_mul hC_pos.le, ← ENNReal.ofReal_mul hC_pos.le,
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1; ring
      have hS_tail : (∑ r ∈ S, ∑' k : ℕ,
          v (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) ≤
          (S.card : ℝ≥0∞) *
            ENNReal.ofReal (C * (((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) * (1 + 1 / (2 * s - 1)))) := by
        calc (∑ r ∈ S, ∑' k : ℕ,
              v (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
                ENNReal.ofReal (((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))))
            ≤ ∑ _r ∈ S,
                ENNReal.ofReal (C * (((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) * (1 + 1 / (2 * s - 1)))) := by
              refine Finset.sum_le_sum fun r hr => ?_
              have heq_k : ∀ k : ℕ, (k + 1) * m + r = k * m + (m + r) := fun k => by ring
              simp_rw [heq_k]
              exact hshift_tail (m + r) (by omega) (by omega)
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      have hB_tail : (∑ b ∈ B, ∑' k : ℕ,
          v (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))) ≤
          (B.card : ℝ≥0∞) *
            ENNReal.ofReal (C * (((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) * (1 + 1 / (2 * s - 1)))) := by
        calc (∑ b ∈ B, ∑' k : ℕ,
              v (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
                ENNReal.ofReal (((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))))
            ≤ ∑ _b ∈ B,
                ENNReal.ofReal (C * (((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) * (1 + 1 / (2 * s - 1)))) := by
              refine Finset.sum_le_sum fun b hb => ?_
              have hb_le : b ≤ M_B := Finset.le_sup (f := id) hb
              have heq_k : ∀ k : ℕ, (k + 1) * m - b = k * m + (m - b) := fun k => by
                have hbm : b ≤ m := le_trans hb_le (by omega)
                rw [add_mul, one_mul]
                omega
              simp_rw [heq_k]
              exact hshift_tail (m - b) (by omega) (by omega)
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      have htail_sum :
          (∑ r ∈ S, ∑' k : ℕ, v (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
              ENNReal.ofReal (((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) +
            (∑ b ∈ B, ∑' k : ℕ, v (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
              ENNReal.ofReal (((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))) ≤
            ENNReal.ofReal 1 := by
        calc _ ≤ (S.card : ℝ≥0∞) *
                ENNReal.ofReal (C * (((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) * (1 + 1 / (2 * s - 1)))) +
              (B.card : ℝ≥0∞) *
                ENNReal.ofReal (C * (((m - M_B : ℕ) : ℝ) ^ (-(2 * s)) * (1 + 1 / (2 * s - 1)))) :=
              add_le_add hS_tail hB_tail
          _ = ENNReal.ofReal (A_const * (((m - M_B : ℕ) : ℝ) ^ (-(2 * s)))) := by
              rw [← add_mul, ← Nat.cast_add, ← ENNReal.ofReal_natCast,
                ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
              congr 1; dsimp only [A_const, d]; push_cast; ring
          _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hm_tail.le
      have hvx_ge1 : 1 ≤ multiResolventV S s x := one_le_multiResolventV hS1 hs_pos hx.1 hsum
      rw [hS_part, add_assoc]
      calc ENNReal.ofReal (multiResolventV S s x - 1) +
            ((∑ r ∈ S, ∑' k : ℕ, v (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
                ENNReal.ofReal (((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) +
              (∑ b ∈ B, ∑' k : ℕ, v (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
                ENNReal.ofReal (((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))))
          ≤ ENNReal.ofReal (multiResolventV S s x - 1) + ENNReal.ofReal 1 :=
            add_le_add le_rfl htail_sum
        _ = ENNReal.ofReal ((multiResolventV S s x - 1) + 1) :=
            (ENNReal.ofReal_add (sub_nonneg.mpr hvx_ge1) zero_le_one).symm
        _ = v x := by simp [v]
    exact dimH_le_of_transferOp_le (multiResidueAlphabet_ge_one hS1) hs_pos
      (by simp : (0 : ℝ≥0∞) < ENNReal.ofReal 1) ENNReal.ofReal_lt_top hv_bd hsub
  have hlo_ev : ∀ᶠ m : ℕ in atTop, (1 / 2 : ℝ) ≤ (dimH (multiResidueSet m S B)).toReal ∧
      poincareAbscissa S ≤ (dimH (multiResidueSet m S B)).toReal := by
    obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (hup_ev 1 zero_lt_one)
    let M₀ : ℕ := max m₀ (S.sup id + B.sup id + 2)
    refine eventually_atTop.mpr ⟨M₀, fun m hm => ?_⟩
    have hm_m0 : m₀ ≤ m := le_trans (le_max_left _ _) hm
    have hm_sep : S.sup id + B.sup id + 2 ≤ m := le_trans (le_max_right _ _) hm
    have hne_top : dimH (multiResidueSet m S B) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hm₀ m hm_m0)
    have hhalf_lt : (1 / 2 : ℝ≥0∞) < dimH (multiResidueSet m S B) := by
      rcases S.eq_empty_or_nonempty with rfl | hSne
      · have hBne : B.Nonempty := Finset.card_pos.mp (by simpa using hd)
        obtain ⟨b₀, hb₀⟩ := hBne
        have hb0_le : b₀ ≤ B.sup id := Finset.le_sup (f := id) hb₀
        have hS0 : (∅ : Finset ℕ).sup id = 0 := by simp
        have hm_b0 : b₀ + 2 ≤ m := by omega
        have hr0_pos : 1 ≤ m - b₀ := by omega
        have hsub : residueConstSet m (m - b₀) ⊆ multiResidueSet m ∅ B := by
          rintro x ⟨hx01, hirr, hres⟩
          refine ⟨hx01, hirr, fun i => Or.inr ⟨b₀, hb₀, ?_⟩⟩
          obtain ⟨hle, hmod⟩ := hres i
          dsimp only at hle hmod
          have hdvd : m ∣ (cfDigit x i - (m - b₀)) :=
            (Nat.modEq_iff_dvd' hle).mp (by simpa [Nat.ModEq] using hmod.symm)
          obtain ⟨k, hk⟩ := hdvd
          have h1 : cfDigit x i = k * m + (m - b₀) := by rw [mul_comm]; omega
          refine ⟨k + 1, by omega, ?_, le_trans hr0_pos hle⟩
          rw [h1, add_mul, one_mul]
          omega
        exact lt_of_lt_of_le (half_lt_dimH_residueConstSet (by omega) hr0_pos) (dimH_mono hsub)
      · obtain ⟨r₀, hr₀⟩ := hSne
        have hsub : residueConstSet m r₀ ⊆ multiResidueSet m S B := by
          rintro x ⟨hx01, hirr, hres⟩
          exact ⟨hx01, hirr, fun i => Or.inl ⟨r₀, hr₀, hres i⟩⟩
        exact lt_of_lt_of_le (half_lt_dimH_residueConstSet (by omega) (hS1 r₀ hr₀)) (dimH_mono hsub)
    have hhalf_toReal : (1 / 2 : ℝ) ≤ (dimH (multiResidueSet m S B)).toReal := by
      have h1 : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
        rw [one_div, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
      rw [h1] at hhalf_lt
      exact ((ENNReal.ofReal_le_iff_le_toReal hne_top).mp hhalf_lt.le)
    have hpoin_toReal : poincareAbscissa S ≤ (dimH (multiResidueSet m S B)).toReal := by
      rcases S.eq_empty_or_nonempty with rfl | hSne
      · have h0 : poincareAbscissa ∅ = 0 := by
          unfold poincareAbscissa
          have h1 : ∀ ε > 0, (0 : ℝ) ≤ sInf {s : ℝ | 0 < s ∧ Summable (wordSum ∅ (2 * s))} ∧
              sInf {s : ℝ | 0 < s ∧ Summable (wordSum ∅ (2 * s))} ≤ ε := fun ε hε => by
            refine ⟨Real.sInf_nonneg fun s hs => hs.1.le,
              csInf_le ⟨0, fun s hs => hs.1.le⟩ ⟨hε, ?_⟩⟩
            refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
            simp only [Finset.mem_singleton] at hn
            exact wordSum_empty (by omega)
          exact le_antisymm (le_of_forall_pos_le_add fun ε hε => by linarith [(h1 ε hε).2])
            (Real.sInf_nonneg fun s hs => hs.1.le)
        rw [h0]; exact ENNReal.toReal_nonneg
      · have hsub_S : cfAlphabetSet (S : Set ℕ) ⊆ multiResidueSet m S B := by
          rintro x ⟨hx01, hirr, hadm⟩
          exact ⟨hx01, hirr, fun i => Or.inl ⟨cfDigit x i, hadm i, le_rfl, rfl⟩⟩
        have hdim_S : ENNReal.ofReal (poincareAbscissa S) ≤ dimH (multiResidueSet m S B) := by
          rw [← dimH_cfAlphabetSet_finset_eq_poincareAbscissa hSne hS1]
          exact dimH_mono hsub_S
        exact (ENNReal.ofReal_le_iff_le_toReal hne_top).mp hdim_S
    exact ⟨hhalf_toReal, hpoin_toReal⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m₁, hm₁⟩ := eventually_atTop.mp (hup_ev (ε / 2) (half_pos hε))
  obtain ⟨m₂, hm₂⟩ := eventually_atTop.mp hlo_ev
  refine ⟨max m₁ m₂, fun m hm => ?_⟩
  have hup := hm₁ m (le_trans (le_max_left _ _) hm)
  have hlo := hm₂ m (le_trans (le_max_right _ _) hm)
  have hL_le : L ≤ (dimH (multiResidueSet m S B)).toReal := max_le hlo.1 hlo.2
  have h_le_L : (dimH (multiResidueSet m S B)).toReal ≤ L + ε / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by linarith) hup
  dsimp only [L] at hL_le h_le_L
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Subcritical multi-residue witness `S = {2, 3}`: `poincareAbscissa {2, 3} < 1 / 2`. -/
theorem subcritical_pair_two_three :
    Summable (wordSum ({2, 3} : Finset ℕ) 1) ∧ poincareAbscissa ({2, 3} : Finset ℕ) < 1 / 2 := by
  have hS1 : ∀ a ∈ ({2, 3} : Finset ℕ), 1 ≤ a := by decide
  have hw1 : wordSum ({2, 3} : Finset ℕ) (2 * (1 / 2 : ℝ)) 1 = 5 / 6 := by
    rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num, wordSum_one]
    simp [Finset.sum_pair (by decide : (2 : ℕ) ≠ 3)]
    norm_num
  have hsum1 : Summable (wordSum ({2, 3} : Finset ℕ) 1) := by
    refine (summable_wordSum_iff_exists_lt_one hS1 zero_le_one).mpr ⟨1, le_rfl, ?_⟩
    simpa using (by rw [hw1]; norm_num : wordSum ({2, 3} : Finset ℕ) (2 * (1 / 2 : ℝ)) 1 < 1)
  have hcont : Continuous (fun s : ℝ => wordSum ({2, 3} : Finset ℕ) (2 * s) 1) := by
    simp_rw [wordSum_one]
    refine continuous_finsetSum _ fun a ha => ?_
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by have := hS1 a ha; omega : a ≠ 0)
    exact Continuous.rpow continuous_const (continuous_const.mul continuous_id).neg
      (fun _ => Or.inl ha0)
  have hev := (hcont.continuousAt (x := (1 / 2 : ℝ))).eventually
    (Iio_mem_nhds (by rw [hw1]; norm_num : wordSum ({2, 3} : Finset ℕ) (2 * (1 / 2 : ℝ)) 1 < 1))
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, hη_bd⟩ := hev
  let s : ℝ := max (1 / 4) (1 / 2 - η / 2)
  have hs_pos : 0 < s := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hs_lt : s < 1 / 2 := max_lt (by norm_num) (by linarith)
  have hdist : dist s (1 / 2 : ℝ) < η := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs_lt)]
    have : 1 / 2 - η / 2 ≤ s := le_max_right _ _
    linarith
  have hw_lt : wordSum ({2, 3} : Finset ℕ) (2 * s) 1 < 1 := hη_bd hdist
  have hsum_s : Summable (wordSum ({2, 3} : Finset ℕ) (2 * s)) :=
    (summable_wordSum_iff_exists_lt_one hS1 (by linarith)).mpr ⟨1, le_rfl, hw_lt⟩
  have hpoin_le : poincareAbscissa ({2, 3} : Finset ℕ) ≤ s :=
    csInf_le ⟨0, fun x hx => hx.1.le⟩ ⟨hs_pos, hsum_s⟩
  exact ⟨hsum1, hpoin_le.trans_lt hs_lt⟩

/-- Supercritical multi-residue witness `S = {1, 2}`: `51 / 100 ≤ poincareAbscissa {1, 2}`
    via the exact algebraic rational test function `v(x) = 2 / (2 + x)`. -/
theorem supercritical_pair_one_two :
    (51 / 100 : ℝ) ≤ poincareAbscissa ({1, 2} : Finset ℕ) ∧
      (1 / 2 : ℝ) < poincareAbscissa ({1, 2} : Finset ℕ) := by
  have hSne : ({1, 2} : Finset ℕ).Nonempty := ⟨1, by simp⟩
  have hS1 : ∀ a ∈ ({1, 2} : Finset ℕ), 1 ≤ a := by decide
  let v : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (2 / (2 + x))
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (2 / 3) ≤ v x ∧ v x ≤ ENNReal.ofReal 1 := fun x hx =>
    ⟨ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by norm_num)
        (by linarith [hx.1]) (by linarith [hx.2])),
      ENNReal.ofReal_le_ofReal ((div_le_one (by linarith [hx.1])).mpr (by linarith [hx.1]))⟩
  have h3_pow : (35 / 36 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 50 : ℝ)) := by
    have hpow50 : ((35 / 36 : ℝ) ^ 50) ≤ ((3 : ℝ) ^ (-(1 / 50 : ℝ))) ^ 50 := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 50 : ℝ))) 50, ← Real.rpow_mul (by norm_num)]
      norm_num
    exact le_of_pow_le_pow_left₀ (by decide) (Real.rpow_nonneg (by norm_num) _) hpow50
  have hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      v x ≤ transferOp (({1, 2} : Finset ℕ) : Set ℕ) (51 / 100) v x := by
    intro x hx
    rw [transferOp_finset_eq, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
    norm_num
    have h1x : 0 < 1 + x := by linarith [hx.1]
    have h2x : 0 < 2 + x := by linarith [hx.1]
    have h2x3 : 0 < 2 * x + 3 := by linarith [hx.1]
    have h2x5 : 0 < 2 * x + 5 := by linarith [hx.1]
    have hv1 : v (1 / (1 + x)) * ENNReal.ofReal ((1 + x) ^ (-(51 / 50 : ℝ))) =
        ENNReal.ofReal ((2 / (2 * x + 3)) * (1 + x) ^ (-(1 / 50 : ℝ))) := by
      dsimp only [v]
      rw [← ENNReal.ofReal_mul (div_nonneg (by norm_num) (by positivity))]
      congr 1
      have hpow : (1 + x) ^ (-(51 / 50 : ℝ)) = (1 + x) ^ (-1 : ℝ) * (1 + x) ^ (-(1 / 50 : ℝ)) := by
        rw [← Real.rpow_add h1x]; congr 1; norm_num
      rw [hpow, Real.rpow_neg_one]
      field_simp [h1x.ne', h2x3.ne']
      ring
    have hv2 : v (1 / (2 + x)) * ENNReal.ofReal ((2 + x) ^ (-(51 / 50 : ℝ))) =
        ENNReal.ofReal ((2 / (2 * x + 5)) * (2 + x) ^ (-(1 / 50 : ℝ))) := by
      dsimp only [v]
      rw [← ENNReal.ofReal_mul (div_nonneg (by norm_num) (by positivity))]
      congr 1
      have hpow : (2 + x) ^ (-(51 / 50 : ℝ)) = (2 + x) ^ (-1 : ℝ) * (2 + x) ^ (-(1 / 50 : ℝ)) := by
        rw [← Real.rpow_add h2x]; congr 1; norm_num
      rw [hpow, Real.rpow_neg_one]
      field_simp [h2x.ne', h2x5.ne']
      ring
    have hpow1_ge : (35 / 36 : ℝ) ≤ (1 + x) ^ (-(1 / 50 : ℝ)) :=
      h3_pow.trans (Real.rpow_le_rpow_of_nonpos h1x (by linarith [hx.2]) (by norm_num))
    have hpow2_ge : (35 / 36 : ℝ) ≤ (2 + x) ^ (-(1 / 50 : ℝ)) :=
      h3_pow.trans (Real.rpow_le_rpow_of_nonpos h2x (by linarith [hx.2]) (by norm_num))
    have halg : (36 / 35 : ℝ) * (2 / (2 + x)) ≤ 2 / (2 * x + 3) + 2 / (2 * x + 5) := by
      have hdiff : 2 / (2 * x + 3) + 2 / (2 * x + 5) - 2 / (2 + x) =
          2 / ((2 * x + 3) * (2 * x + 5) * (2 + x)) := by
        field_simp [h2x3.ne', h2x5.ne', h2x.ne']
        ring
      have hden35 : (2 * x + 3) * (2 * x + 5) ≤ 35 := by nlinarith [hx.1, hx.2]
      have h35_le : 2 / (35 * (2 + x)) ≤ 2 / ((2 * x + 3) * (2 * x + 5) * (2 + x)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_right hden35 h2x.le)
      have h36 : (36 / 35 : ℝ) * (2 / (2 + x)) = 2 / (2 + x) + 2 / (35 * (2 + x)) := by
        field_simp [h2x.ne']; ring
      linarith
    have h23 : 0 ≤ 2 / (2 * x + 3) := by positivity
    have h25 : 0 ≤ 2 / (2 * x + 5) := by positivity
    have hreal_ge : 2 / (2 + x) ≤
        (2 / (2 * x + 3)) * (1 + x) ^ (-(1 / 50 : ℝ)) +
          (2 / (2 * x + 5)) * (2 + x) ^ (-(1 / 50 : ℝ)) := by
      calc 2 / (2 + x) = (35 / 36 : ℝ) * ((36 / 35 : ℝ) * (2 / (2 + x))) := by ring
        _ ≤ (35 / 36 : ℝ) * (2 / (2 * x + 3) + 2 / (2 * x + 5)) :=
            mul_le_mul_of_nonneg_left halg (by norm_num)
        _ = (2 / (2 * x + 3)) * (35 / 36) + (2 / (2 * x + 5)) * (35 / 36) := by ring
        _ ≤ (2 / (2 * x + 3)) * (1 + x) ^ (-(1 / 50 : ℝ)) +
              (2 / (2 * x + 5)) * (2 + x) ^ (-(1 / 50 : ℝ)) :=
            add_le_add (mul_le_mul_of_nonneg_left hpow1_ge h23)
              (mul_le_mul_of_nonneg_left hpow2_ge h25)
    rw [show (1 + x)⁻¹ = 1 / (1 + x) from (one_div _).symm,
      show (2 + x)⁻¹ = 1 / (2 + x) from (one_div _).symm,
      hv1, hv2, ← ENNReal.ofReal_add (mul_nonneg h23 (Real.rpow_nonneg h1x.le _))
      (mul_nonneg h25 (Real.rpow_nonneg h2x.le _))]
    exact ENNReal.ofReal_le_ofReal hreal_ge
  have hdim_ge : ENNReal.ofReal (51 / 100) ≤ dimH (cfAlphabetSet (({1, 2} : Finset ℕ) : Set ℕ)) :=
    le_dimH_of_transferOp_ge hSne hS1 (by norm_num)
      (by norm_num : (0 : ℝ≥0∞) < ENNReal.ofReal (2 / 3)) ENNReal.ofReal_lt_top hv_bd hsuper
  rw [dimH_cfAlphabetSet_finset_eq_poincareAbscissa hSne hS1] at hdim_ge
  have hle : (51 / 100 : ℝ) ≤ poincareAbscissa ({1, 2} : Finset ℕ) :=
    (ENNReal.ofReal_le_ofReal_iff (poincareAbscissa_nonneg _)).mp hdim_ge
  exact ⟨hle, lt_of_lt_of_le (by norm_num) hle⟩

/-! ### Part 4: Elementary Euler–Mascheroni Zeta Expansion & Logarithmic Derivatives -/

private lemma exp_neg_bounds {t : ℝ} (ht : 0 ≤ t) :
    1 - t ≤ Real.exp (-t) ∧ Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  have hlo : 1 - t ≤ Real.exp (-t) := by
    have := Real.add_one_le_exp (-t)
    linarith
  refine ⟨hlo, ?_⟩
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · norm_num
  · let g : ℝ → ℝ := fun u => 1 - u + u ^ 2 / 2 - Real.exp (-u)
    have hg0 : g 0 = 0 := by simp [g]
    have hg_cont : ContinuousOn g (Set.Icc 0 t) := by
      apply Continuous.continuousOn
      continuity
    have hg_deriv : ∀ u ∈ Set.Ioo 0 t,
        HasDerivAt g (u - 1 + Real.exp (-u)) u := by
      intro u _
      have h1 := (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)
      have h2 := ((hasDerivAt_id u).pow 2).div_const 2
      have h3 := (hasDerivAt_neg u).exp
      have h_raw := (h1.add h2).sub h3
      refine (h_raw.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)).congr_deriv ?_
      · simp [g, sub_eq_add_neg]
      · simp; ring
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g
      (f' := fun u => u - 1 + Real.exp (-u)) ht_pos hg_cont hg_deriv
    have hc_lo : 1 - c ≤ Real.exp (-c) := by
      have := Real.add_one_le_exp (-c)
      linarith
    have hderiv_nn : 0 ≤ (g t - g 0) / (t - 0) := by
      rw [← hslope]
      linarith
    have hgt_nn : 0 ≤ g t := by
      rw [hg0, sub_zero, sub_zero, div_nonneg_iff] at hderiv_nn
      rcases hderiv_nn with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · linarith
    dsimp only [g] at hgt_nn
    linarith

private lemma one_add_rpow_neg_two_ge_local {y p : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    1 - 2 * y ≤ (1 + y) ^ (-p) := by
  have h1y : 1 ≤ 1 + y := by linarith
  have hpos : 0 < 1 + y := by linarith
  have hmono : (1 + y) ^ (-2 : ℝ) ≤ (1 + y) ^ (-p) :=
    Real.rpow_le_rpow_of_exponent_le h1y (by linarith)
  have h2 : 1 - 2 * y ≤ (1 + y) ^ (-2 : ℝ) := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hpos.le,
      Real.rpow_natCast, inv_eq_one_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg y, hy0, hy1]
  exact h2.trans hmono

private lemma log_le_rpow_sub_one_div {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    Real.log x ≤ (x ^ α - 1) / α := by
  have h1 : Real.log (x ^ α) ≤ x ^ α - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx α)
  rw [Real.log_rpow hx α] at h1
  exact (le_div_iff₀' hα).mpr h1

private lemma tendsto_log_div_nat_local :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have hup : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) / (n : ℝ) ≤ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog := log_le_rpow_sub_one_div (by norm_num : (0 : ℝ) < 1 / 2) hn_pos
    have hlog2 : Real.log (n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by linarith
    calc Real.log (n : ℝ) / (n : ℝ)
        ≤ (2 * (n : ℝ) ^ (1 / 2 : ℝ)) / (n : ℝ) :=
          div_le_div_of_nonneg_right hlog2 hn_pos.le
      _ = 2 * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-1 : ℝ)) := by
          rw [Real.rpow_neg_one]; ring
      _ = 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hn_pos]; congr 2; norm_num
  have hlo : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ Real.log (n : ℝ) / (n : ℝ) :=
    eventually_atTop.mpr ⟨1, fun n hn =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (Nat.cast_nonneg n)⟩
  have htend : Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend hlo hup

private lemma tendsto_log_sq_div_nat_local :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 2 / (n : ℝ)) atTop (nhds 0) := by
  have hup : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ≤ 16 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog := log_le_rpow_sub_one_div (by norm_num : (0 : ℝ) < 1 / 4) hn_pos
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hlog4 : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by linarith
    have hsq : (Real.log (n : ℝ)) ^ 2 ≤ 16 * (n : ℝ) ^ (1 / 2 : ℝ) := by
      have h1 : (Real.log (n : ℝ)) ^ 2 ≤ (4 * (n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hlog_nn hlog4 2
      have h2 : (4 * (n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = 16 * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by ring
      have h3 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
      linarith
    calc (Real.log (n : ℝ)) ^ 2 / (n : ℝ)
        ≤ (16 * (n : ℝ) ^ (1 / 2 : ℝ)) / (n : ℝ) :=
          div_le_div_of_nonneg_right hsq hn_pos.le
      _ = 16 * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-1 : ℝ)) := by
          rw [Real.rpow_neg_one]; ring
      _ = 16 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hn_pos]; congr 2; norm_num
  have hlo : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 / (n : ℝ) :=
    eventually_atTop.mpr ⟨1, fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)⟩
  have htend : Tendsto (fun n : ℕ => 16 * (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend hlo hup

/-- Uniform elementary expansion of `∑' k, (k + 1)^{-(1 + ε)}` around `1 / ε + γ`
    for `0 < ε ≤ 1` (`O(ε)` error using `Real.eulerMascheroniConstant`). -/
lemma abs_tsum_rpow_sub_inv_sub_eulerMascheroni_le :
    ∃ Cζ > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |(∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε)))) - 1 / ε -
        Real.eulerMascheroniConstant| ≤ Cζ * ε := by
  have hsum_32 : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2))
    refine h.congr fun k => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
  let Cζ : ℝ := 4 * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
  have hCζ_pos : 0 < Cζ := by
    have h0 : (1 : ℝ) ≤ ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
      have hterm := hsum_32.le_tsum 0 (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      simpa using hterm
    dsimp only [Cζ]; linarith
  refine ⟨Cζ, hCζ_pos, fun ε hε hε1 => ?_⟩
  let a : ℕ → ℝ := fun k =>
    (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε))) -
      ((((k + 1 : ℕ) : ℝ) ^ (-ε)) - (((k + 2 : ℕ) : ℝ) ^ (-ε))) / ε
  let b : ℕ → ℝ := fun k =>
    (1 : ℝ) / ((k + 1 : ℕ) : ℝ) -
      (Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))
  have hb_sum : ∀ N : ℕ, ∑ k ∈ Finset.range N, b k = Real.eulerMascheroniSeq N := by
    intro N
    induction N with
    | zero => simp [Real.eulerMascheroniSeq_zero]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Real.eulerMascheroniSeq, Real.eulerMascheroniSeq,
        harmonic_succ]
      dsimp only [b]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      rw [show (((N + 1 : ℕ) : ℝ) + 1) = ((N + 2 : ℕ) : ℝ) by push_cast; ring]
      push_cast
      ring
  have ha_sum : ∀ N : ℕ, ∑ k ∈ Finset.range N, a k =
      (∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε)))) -
        (1 - (((N + 1 : ℕ) : ℝ) ^ (-ε))) / ε := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      dsimp only [a]
      ring
  have hsum_1e : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε)))) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + ε))
    refine h.congr fun k => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
  have ha_tend : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, a k) atTop
      (nhds ((∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε)))) - 1 / ε)) := by
    simp_rw [ha_sum]
    have h1 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε))))
        atTop (nhds (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε))))) :=
      hsum_1e.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ (-ε))) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hε).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have h3 : Tendsto (fun N : ℕ => (1 - (((N + 1 : ℕ) : ℝ) ^ (-ε))) / ε) atTop
        (nhds ((1 - 0) / ε)) :=
      ((tendsto_const_nhds.sub h2).div_const ε)
    simpa [sub_zero] using h1.sub h3
  have hb_tend : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, b k) atTop
      (nhds Real.eulerMascheroniConstant) := by
    simp_rw [hb_sum]
    exact Real.tendsto_eulerMascheroniSeq
  have hdiff_tend : Tendsto (fun N : ℕ => |∑ k ∈ Finset.range N, a k - ∑ k ∈ Finset.range N, b k|)
      atTop (nhds |(∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε)))) - 1 / ε -
        Real.eulerMascheroniConstant|) :=
    (ha_tend.sub hb_tend).abs
  have hpt : ∀ k : ℕ, |a k - b k| ≤ 4 * ε * (((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
    intro k
    let u : ℝ := ((k + 1 : ℕ) : ℝ)
    have hu1 : 1 ≤ u := by dsimp [u]; exact_mod_cast (by omega : 1 ≤ k + 1)
    have hu_pos : 0 < u := by linarith
    have hu1_lt : u < u + 1 := by linarith
    let H : ℝ → ℝ := fun t => (u ^ (-(1 + ε)) - u⁻¹) * t + t ^ (-ε) / ε + Real.log t
    have hH_cont : ContinuousOn H (Set.Icc u (u + 1)) := by
      refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
      · exact continuous_const.mul continuous_id |>.continuousOn
      · refine ContinuousOn.div_const ?_ ε
        exact ContinuousOn.rpow continuousOn_id continuousOn_const
          fun t ht => Or.inl (by linarith [ht.1, hu_pos])
      · exact Real.continuousOn_log.mono fun t ht => ne_of_gt (by linarith [ht.1, hu_pos])
    have hH_deriv : ∀ t ∈ Set.Ioo u (u + 1),
        HasDerivAt H ((u ^ (-(1 + ε)) - u⁻¹) - (t ^ (-(1 + ε)) - t⁻¹)) t := by
      intro t ht
      have ht_pos : 0 < t := by linarith [ht.1, hu_pos]
      have h1 : HasDerivAt (fun s : ℝ => (u ^ (-(1 + ε)) - u⁻¹) * s)
          (u ^ (-(1 + ε)) - u⁻¹) t := by
        simpa using (hasDerivAt_id t).const_mul (u ^ (-(1 + ε)) - u⁻¹)
      have h2 : HasDerivAt (fun s : ℝ => s ^ (-ε) / ε) (-t ^ (-(1 + ε))) t := by
        have hr : HasDerivAt (fun s : ℝ => s ^ (-ε)) (-ε * t ^ (-ε - 1)) t := by
          simpa using Real.hasDerivAt_rpow_const (Or.inl ht_pos.ne') (p := -ε)
        convert hr.div_const ε using 1
        have heq : -ε - 1 = -(1 + ε) := by ring
        rw [heq]
        field_simp [hε.ne']
      have h3 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht_pos.ne'
      convert (h1.add h2).add h3 using 1
      ring
    obtain ⟨c, hc, hHc⟩ := exists_hasDerivAt_eq_slope H
      (f' := fun t => (u ^ (-(1 + ε)) - u⁻¹) - (t ^ (-(1 + ε)) - t⁻¹))
      hu1_lt hH_cont hH_deriv
    have hH_diff_eq : H (u + 1) - H u = a k - b k := by
      dsimp only [H, a, b, u]
      have hu2 : ((k + 2 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hu2]
      ring
    have hab_eq : a k - b k =
        (u ^ (-(1 + ε)) - u⁻¹) - (c ^ (-(1 + ε)) - c⁻¹) := by
      rw [← hH_diff_eq, hHc, add_sub_cancel_left, div_one]
    let f : ℝ → ℝ := fun t => t ^ (-(1 + ε)) - t⁻¹
    have huc : u < c := hc.1
    have hf_cont : ContinuousOn f (Set.Icc u c) := by
      refine ContinuousOn.sub ?_ ?_
      · exact ContinuousOn.rpow continuousOn_id continuousOn_const
          fun t ht => Or.inl (by linarith [ht.1, hu_pos])
      · exact continuousOn_inv₀.mono fun t ht => ne_of_gt (by linarith [ht.1, hu_pos])
    have hf_deriv : ∀ t ∈ Set.Ioo u c,
        HasDerivAt f (t ^ (-2 : ℝ) * (1 - (1 + ε) * t ^ (-ε))) t := by
      intro t ht
      have ht_pos : 0 < t := by linarith [ht.1, hu_pos]
      have h1 : HasDerivAt (fun s : ℝ => s ^ (-(1 + ε)))
          (-(1 + ε) * t ^ (-(1 + ε) - 1)) t := by
        simpa using Real.hasDerivAt_rpow_const (Or.inl ht_pos.ne') (p := -(1 + ε))
      have h2 : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t :=
        hasDerivAt_inv ht_pos.ne'
      convert h1.sub h2 using 1
      have h_pow1 : t ^ (-(1 + ε) - 1) = t ^ (-2 : ℝ) * t ^ (-ε) := by
        rw [← Real.rpow_add ht_pos]; congr 1; ring
      have h_pow2 : (t ^ 2)⁻¹ = t ^ (-2 : ℝ) := by
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht_pos.le,
          Real.rpow_natCast]
      rw [h_pow1, h_pow2]
      ring
    obtain ⟨ξ, hξ, hfc⟩ := exists_hasDerivAt_eq_slope f
      (f' := fun t => t ^ (-2 : ℝ) * (1 - (1 + ε) * t ^ (-ε)))
      huc hf_cont hf_deriv
    have hcu_pos : 0 < c - u := sub_pos.mpr hc.1
    have hcu_le1 : c - u ≤ 1 := by linarith [hc.2]
    have hξ1 : 1 ≤ ξ := by linarith [hξ.1, hu1]
    have hξ_pos : 0 < ξ := by linarith
    have hξ_le : ξ ≤ u + 1 := by linarith [hξ.2, hc.2]
    have hξ_ge_u : u ≤ ξ := hξ.1.le
    have hab_slope : |a k - b k| =
        |ξ ^ (-2 : ℝ) * (1 - (1 + ε) * ξ ^ (-ε))| * (c - u) := by
      rw [hab_eq]
      have hf_eq : (u ^ (-(1 + ε)) - u⁻¹) - (c ^ (-(1 + ε)) - c⁻¹) = -(f c - f u) := by
        dsimp only [f]; ring
      rw [hf_eq, abs_neg]
      have hfc' : f c - f u = (ξ ^ (-2 : ℝ) * (1 - (1 + ε) * ξ ^ (-ε))) * (c - u) :=
        (div_eq_iff hcu_pos.ne').mp hfc.symm
      rw [hfc', abs_mul, abs_of_pos hcu_pos]
    have h_inner : |1 - (1 + ε) * ξ ^ (-ε)| ≤ ε * (Real.log (u + 1) + 1) := by
      rw [abs_le]
      have hξ_pow_le1 : ξ ^ (-ε) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hξ1 (by linarith)
      have hξ_pow_pos : 0 < ξ ^ (-ε) := Real.rpow_pos_of_pos hξ_pos _
      have h_lo_fac : 0 ≤ Real.log (u + 1) := Real.log_nonneg (by linarith)
      have hlo : -(ε * (Real.log (u + 1) + 1)) ≤ 1 - (1 + ε) * ξ ^ (-ε) := by
        have h1 : (1 + ε) * ξ ^ (-ε) ≤ 1 + ε := by nlinarith [hξ_pow_le1, hε]
        nlinarith [mul_nonneg hε.le h_lo_fac]
      have hhi : 1 - (1 + ε) * ξ ^ (-ε) ≤ ε * (Real.log (u + 1) + 1) := by
        have hexp : 1 - ε * Real.log ξ ≤ Real.exp (-(ε * Real.log ξ)) :=
          (exp_neg_bounds (mul_nonneg hε.le (Real.log_nonneg hξ1))).1
        have hrpow_eq : ξ ^ (-ε) = Real.exp (-(ε * Real.log ξ)) := by
          rw [Real.rpow_def_of_pos hξ_pos]; congr 1; ring
        have hlog_le : Real.log ξ ≤ Real.log (u + 1) :=
          Real.log_le_log hξ_pos hξ_le
        have h2 : 1 - ξ ^ (-ε) ≤ ε * Real.log (u + 1) := by
          rw [hrpow_eq]
          nlinarith [hexp, mul_le_mul_of_nonneg_left hlog_le hε.le]
        nlinarith [mul_pos hε hξ_pow_pos]
      exact ⟨hlo, hhi⟩
    have hlog_bd : Real.log (u + 1) + 1 ≤ 4 * u ^ (1 / 2 : ℝ) := by
      have hu1_pos : 0 < u + 1 := by linarith
      have hlog := log_le_rpow_sub_one_div (by norm_num : (0 : ℝ) < 1 / 2) hu1_pos
      have h1 : Real.log (u + 1) + 1 ≤ 2 * (u + 1) ^ (1 / 2 : ℝ) := by linarith
      have hu_4u : u + 1 ≤ 4 * u := by linarith
      have h4_pow : (4 * u) ^ (1 / 2 : ℝ) = 2 * u ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hu_pos.le]
        have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [h4]
      have hmono : (u + 1) ^ (1 / 2 : ℝ) ≤ (4 * u) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hu1_pos.le hu_4u (by norm_num)
      linarith
    have hξ2_le : ξ ^ (-2 : ℝ) ≤ u ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hu_pos hξ_ge_u (by norm_num)
    calc |a k - b k|
        = (ξ ^ (-2 : ℝ) * |1 - (1 + ε) * ξ ^ (-ε)|) * (c - u) := by
            rw [hab_slope, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hξ_pos _)]
      _ ≤ (ξ ^ (-2 : ℝ) * |1 - (1 + ε) * ξ ^ (-ε)|) * 1 := by
            exact mul_le_mul_of_nonneg_left hcu_le1
              (mul_nonneg (Real.rpow_nonneg hξ_pos.le _) (abs_nonneg _))
      _ ≤ u ^ (-2 : ℝ) * (ε * (4 * u ^ (1 / 2 : ℝ))) := by
            rw [mul_one]
            refine mul_le_mul hξ2_le ?_ (abs_nonneg _) (Real.rpow_nonneg hu_pos.le _)
            exact h_inner.trans (mul_le_mul_of_nonneg_left hlog_bd hε.le)
      _ = 4 * ε * (u ^ (-2 : ℝ) * u ^ (1 / 2 : ℝ)) := by ring
      _ = 4 * ε * u ^ (-(3 / 2 : ℝ)) := by
            rw [← Real.rpow_add hu_pos]; congr 2; norm_num
  have hpartial : ∀ N : ℕ,
      |∑ k ∈ Finset.range N, a k - ∑ k ∈ Finset.range N, b k| ≤ Cζ * ε := by
    intro N
    rw [← Finset.sum_sub_distrib]
    calc |∑ k ∈ Finset.range N, (a k - b k)|
        ≤ ∑ k ∈ Finset.range N, |a k - b k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range N, (4 * ε * (((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
          Finset.sum_le_sum fun k _ => hpt k
      _ = (4 * ε) * ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
          rw [← Finset.mul_sum]
      _ ≤ (4 * ε) * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hsum_32.sum_le_tsum (Finset.range N)
            (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = Cζ * ε := by dsimp only [Cζ]; ring
  exact le_of_tendsto hdiff_tend (Eventually.of_forall hpartial)

/-- First logarithmic moment at level `n`: `∑_{w ∈ S^n} (log q(w)) / q(w)`. -/
def wordLogSum (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → {a : ℕ // a ∈ S}, Real.log (denQ (subWord n w)) / denQ (subWord n w)

/-- Second logarithmic moment at level `n`: `∑_{w ∈ S^n} (log q(w))^2 / q(w)`. -/
def wordLogSqSum (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → {a : ℕ // a ∈ S}, (Real.log (denQ (subWord n w))) ^ 2 / denQ (subWord n w)

/-- First logarithmic continuant series `C_S' = ∑' n, ∑_{w ∈ S^n} (log q(w)) / q(w)`. -/
def multiCLog (S : Finset ℕ) : ℝ :=
  ∑' n : ℕ, wordLogSum S n

/-- Second logarithmic continuant series `C_S'' = ∑' n, ∑_{w ∈ S^n} (log q(w))^2 / q(w)`. -/
def multiCLogSq (S : Finset ℕ) : ℝ :=
  ∑' n : ℕ, wordLogSqSum S n

lemma wordLogSum_nonneg {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a) (n : ℕ) :
    0 ≤ wordLogSum S n := by
  refine Finset.sum_nonneg fun w _ => ?_
  have hpd := posDigits_subWord (fun a ha => hS1 a ha) n w
  exact div_nonneg (Real.log_nonneg (denQ_ge_one hpd)) (denQ_pos hpd).le

lemma wordLogSqSum_nonneg {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a) (n : ℕ) :
    0 ≤ wordLogSqSum S n := by
  refine Finset.sum_nonneg fun w _ => ?_
  have hpd := posDigits_subWord (fun a ha => hS1 a ha) n w
  exact div_nonneg (sq_nonneg _) (denQ_pos hpd).le

lemma wordLogSum_zero (S : Finset ℕ) : wordLogSum S 0 = 0 := by
  unfold wordLogSum
  letI : Unique (Fin 0 → {a : ℕ // a ∈ S}) :=
    { default := fun i => i.elim0
      uniq := fun f => funext fun i => i.elim0 }
  rw [Fintype.sum_unique]
  have hsub0 : subWord (A := (S : Set ℕ)) 0 default = [] := rfl
  rw [hsub0, denQ_nil, Real.log_one, zero_div]

lemma wordLogSqSum_zero (S : Finset ℕ) : wordLogSqSum S 0 = 0 := by
  unfold wordLogSqSum
  letI : Unique (Fin 0 → {a : ℕ // a ∈ S}) :=
    { default := fun i => i.elim0
      uniq := fun f => funext fun i => i.elim0 }
  rw [Fintype.sum_unique]
  have hsub0 : subWord (A := (S : Set ℕ)) 0 default = [] := rfl
  rw [hsub0, denQ_nil, Real.log_one]
  norm_num

lemma multiCLog_nonneg {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a) : 0 ≤ multiCLog S :=
  tsum_nonneg fun n => wordLogSum_nonneg hS1 n

lemma multiCLogSq_nonneg {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a) : 0 ≤ multiCLogSq S :=
  tsum_nonneg fun n => wordLogSqSum_nonneg hS1 n

lemma summable_wordLogSum {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    (hsum : Summable (wordSum S 1)) :
    Summable (wordLogSum S) := by
  obtain ⟨C, hC_pos, ρ, hρ_mem, hgeom⟩ :=
    exists_geom_bound_of_summable_wordSum hS1 zero_le_one hsum
  let M : ℕ := S.sup id
  let L : ℝ := Real.log ((M : ℝ) + 1)
  have hL_nn : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
  have hbound : ∀ n : ℕ, wordLogSum S n ≤ (C * L) * ((n : ℝ) ^ 1 * ρ ^ n) := fun n => by
    have hterm : ∀ w : Fin n → {a : ℕ // a ∈ S},
        Real.log (denQ (subWord n w)) / denQ (subWord n w) ≤
          ((n : ℝ) * L) * denQ (subWord n w) ^ (-1 : ℝ) := fun w => by
      have hpd := posDigits_subWord (fun a ha => hS1 a ha) n w
      have hq_pos : 0 < denQ (subWord n w) := denQ_pos hpd
      have hM : ∀ a ∈ subWord n w, a ≤ M := by
        intro a ha
        simp only [subWord, List.mem_ofFn] at ha
        rcases ha with ⟨i, rfl⟩
        exact Finset.le_sup (f := id) (w i).2
      have hq_le := denQ_le_max_add_one_pow hpd hM
      rw [subWord_length] at hq_le
      have hlog_le : Real.log (denQ (subWord n w)) ≤ (n : ℝ) * L := by
        calc Real.log (denQ (subWord n w))
            ≤ Real.log (((M : ℝ) + 1) ^ n) := Real.log_le_log hq_pos hq_le
          _ = (n : ℝ) * L := by rw [Real.log_pow]
      rw [Real.rpow_neg_one, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hlog_le (inv_nonneg.mpr hq_pos.le)
    calc wordLogSum S n
        ≤ ∑ w : Fin n → {a : ℕ // a ∈ S}, ((n : ℝ) * L) * denQ (subWord n w) ^ (-1 : ℝ) :=
          Finset.sum_le_sum fun w _ => hterm w
      _ = ((n : ℝ) * L) * wordSum S 1 n := by rw [← Finset.mul_sum]; rfl
      _ ≤ ((n : ℝ) * L) * (C * ρ ^ n) :=
          mul_le_mul_of_nonneg_left (hgeom n) (mul_nonneg (Nat.cast_nonneg n) hL_nn)
      _ = (C * L) * ((n : ℝ) ^ 1 * ρ ^ n) := by rw [pow_one]; ring
  have hnorm : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hρ_mem.1]
    exact hρ_mem.2
  exact Summable.of_nonneg_of_le (wordLogSum_nonneg hS1) hbound
    ((summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).mul_left (C * L))

lemma summable_wordLogSqSum {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    (hsum : Summable (wordSum S 1)) :
    Summable (wordLogSqSum S) := by
  obtain ⟨C, hC_pos, ρ, hρ_mem, hgeom⟩ :=
    exists_geom_bound_of_summable_wordSum hS1 zero_le_one hsum
  let M : ℕ := S.sup id
  let L : ℝ := Real.log ((M : ℝ) + 1)
  have hL_nn : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
  have hbound : ∀ n : ℕ, wordLogSqSum S n ≤ (C * L ^ 2) * ((n : ℝ) ^ 2 * ρ ^ n) := fun n => by
    have hterm : ∀ w : Fin n → {a : ℕ // a ∈ S},
        (Real.log (denQ (subWord n w))) ^ 2 / denQ (subWord n w) ≤
          ((n : ℝ) ^ 2 * L ^ 2) * denQ (subWord n w) ^ (-1 : ℝ) := fun w => by
      have hpd := posDigits_subWord (fun a ha => hS1 a ha) n w
      have hq_pos : 0 < denQ (subWord n w) := denQ_pos hpd
      have hq1 : 1 ≤ denQ (subWord n w) := denQ_ge_one hpd
      have hM : ∀ a ∈ subWord n w, a ≤ M := by
        intro a ha
        simp only [subWord, List.mem_ofFn] at ha
        rcases ha with ⟨i, rfl⟩
        exact Finset.le_sup (f := id) (w i).2
      have hq_le := denQ_le_max_add_one_pow hpd hM
      rw [subWord_length] at hq_le
      have hlog_le : Real.log (denQ (subWord n w)) ≤ (n : ℝ) * L := by
        calc Real.log (denQ (subWord n w))
            ≤ Real.log (((M : ℝ) + 1) ^ n) := Real.log_le_log hq_pos hq_le
          _ = (n : ℝ) * L := by rw [Real.log_pow]
      have hsq : (Real.log (denQ (subWord n w))) ^ 2 ≤ (n : ℝ) ^ 2 * L ^ 2 := by
        have := pow_le_pow_left₀ (Real.log_nonneg hq1) hlog_le 2
        linarith [show ((n : ℝ) * L) ^ 2 = (n : ℝ) ^ 2 * L ^ 2 by ring]
      rw [Real.rpow_neg_one, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr hq_pos.le)
    calc wordLogSqSum S n
        ≤ ∑ w : Fin n → {a : ℕ // a ∈ S}, ((n : ℝ) ^ 2 * L ^ 2) * denQ (subWord n w) ^ (-1 : ℝ) :=
          Finset.sum_le_sum fun w _ => hterm w
      _ = ((n : ℝ) ^ 2 * L ^ 2) * wordSum S 1 n := by rw [← Finset.mul_sum]; rfl
      _ ≤ ((n : ℝ) ^ 2 * L ^ 2) * (C * ρ ^ n) :=
          mul_le_mul_of_nonneg_left (hgeom n) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (C * L ^ 2) * ((n : ℝ) ^ 2 * ρ ^ n) := by ring
  have hnorm : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hρ_mem.1]
    exact hρ_mem.2
  exact Summable.of_nonneg_of_le (wordLogSqSum_nonneg hS1) hbound
    ((summable_pow_mul_geometric_of_norm_lt_one 2 hnorm).mul_left (C * L ^ 2))

/-- Exact second-order Taylor envelope for `multiC S (1 + ε)` at `ε ≥ 0`. -/
lemma multiC_one_add_bounds {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    (hsum : Summable (wordSum S 1)) {ε : ℝ} (hε : 0 ≤ ε) :
    multiC S 1 - ε * multiCLog S ≤ multiC S (1 + ε) ∧
      multiC S (1 + ε) ≤ multiC S 1 - ε * multiCLog S + ε ^ 2 / 2 * multiCLogSq S := by
  have hlog_sum := summable_wordLogSum hS1 hsum
  have hlogsq_sum := summable_wordLogSqSum hS1 hsum
  have h1e_sum : Summable (wordSum S (1 + ε)) :=
    Summable.of_nonneg_of_le (wordSum_nonneg S (1 + ε))
      (fun n => wordSum_antitone_p S hS1 (by linarith) n) hsum
  have h_level : ∀ n : ℕ,
      wordSum S 1 n - ε * wordLogSum S n ≤ wordSum S (1 + ε) n ∧
        wordSum S (1 + ε) n ≤
          wordSum S 1 n - ε * wordLogSum S n + ε ^ 2 / 2 * wordLogSqSum S n := by
    intro n
    have hpt_lo : ∀ w : Fin n → {a : ℕ // a ∈ S},
        denQ (subWord n w) ^ (-1 : ℝ) -
          ε * (Real.log (denQ (subWord n w)) / denQ (subWord n w)) ≤
          denQ (subWord n w) ^ (-(1 + ε)) := fun w => by
      have hpd := posDigits_subWord (fun a ha => hS1 a ha) n w
      have hq_pos : 0 < denQ (subWord n w) := denQ_pos hpd
      have hq1 : 1 ≤ denQ (subWord n w) := denQ_ge_one hpd
      have ht : 0 ≤ ε * Real.log (denQ (subWord n w)) :=
        mul_nonneg hε (Real.log_nonneg hq1)
      have hexp := (exp_neg_bounds ht).1
      have hr : denQ (subWord n w) ^ (-(1 + ε)) =
          (denQ (subWord n w))⁻¹ * Real.exp (-(ε * Real.log (denQ (subWord n w)))) := by
        rw [show -(1 + ε) = -1 + -ε by ring, Real.rpow_add hq_pos, Real.rpow_neg_one,
          Real.rpow_def_of_pos hq_pos]
        congr 2; ring
      rw [hr]
      have hmul := mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr hq_pos.le)
      have heq : (denQ (subWord n w))⁻¹ * (1 - ε * Real.log (denQ (subWord n w))) =
          denQ (subWord n w) ^ (-1 : ℝ) -
            ε * (Real.log (denQ (subWord n w)) / denQ (subWord n w)) := by
        rw [Real.rpow_neg_one]; ring
      linarith
    have hpt_hi : ∀ w : Fin n → {a : ℕ // a ∈ S},
        denQ (subWord n w) ^ (-(1 + ε)) ≤
          denQ (subWord n w) ^ (-1 : ℝ) -
            ε * (Real.log (denQ (subWord n w)) / denQ (subWord n w)) +
            ε ^ 2 / 2 * ((Real.log (denQ (subWord n w))) ^ 2 / denQ (subWord n w)) := fun w => by
      have hpd := posDigits_subWord (fun a ha => hS1 a ha) n w
      have hq_pos : 0 < denQ (subWord n w) := denQ_pos hpd
      have hq1 : 1 ≤ denQ (subWord n w) := denQ_ge_one hpd
      have ht : 0 ≤ ε * Real.log (denQ (subWord n w)) :=
        mul_nonneg hε (Real.log_nonneg hq1)
      have hexp := (exp_neg_bounds ht).2
      have hr : denQ (subWord n w) ^ (-(1 + ε)) =
          (denQ (subWord n w))⁻¹ * Real.exp (-(ε * Real.log (denQ (subWord n w)))) := by
        rw [show -(1 + ε) = -1 + -ε by ring, Real.rpow_add hq_pos, Real.rpow_neg_one,
          Real.rpow_def_of_pos hq_pos]
        congr 2; ring
      rw [hr]
      have hmul := mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr hq_pos.le)
      have heq : (denQ (subWord n w))⁻¹ *
          (1 - ε * Real.log (denQ (subWord n w)) + (ε * Real.log (denQ (subWord n w))) ^ 2 / 2) =
          denQ (subWord n w) ^ (-1 : ℝ) -
            ε * (Real.log (denQ (subWord n w)) / denQ (subWord n w)) +
            ε ^ 2 / 2 * ((Real.log (denQ (subWord n w))) ^ 2 / denQ (subWord n w)) := by
        rw [Real.rpow_neg_one]; ring
      linarith
    constructor
    · calc wordSum S 1 n - ε * wordLogSum S n
          = ∑ w : Fin n → {a : ℕ // a ∈ S},
              (denQ (subWord n w) ^ (-1 : ℝ) -
                ε * (Real.log (denQ (subWord n w)) / denQ (subWord n w))) := by
              unfold wordSum wordLogSum
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        _ ≤ wordSum S (1 + ε) n := Finset.sum_le_sum fun w _ => hpt_lo w
    · calc wordSum S (1 + ε) n
          ≤ ∑ w : Fin n → {a : ℕ // a ∈ S},
              (denQ (subWord n w) ^ (-1 : ℝ) -
                ε * (Real.log (denQ (subWord n w)) / denQ (subWord n w)) +
                ε ^ 2 / 2 * ((Real.log (denQ (subWord n w))) ^ 2 / denQ (subWord n w))) :=
              Finset.sum_le_sum fun w _ => hpt_hi w
        _ = wordSum S 1 n - ε * wordLogSum S n + ε ^ 2 / 2 * wordLogSqSum S n := by
            unfold wordSum wordLogSum wordLogSqSum
            simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  constructor
  · have hlo_s : Summable (fun n : ℕ => wordSum S 1 n - ε * wordLogSum S n) :=
      hsum.sub (hlog_sum.mul_left ε)
    have ht := hlo_s.tsum_le_tsum (fun n => (h_level n).1) h1e_sum
    have hts : (∑' n : ℕ, (wordSum S 1 n - ε * wordLogSum S n)) =
        multiC S 1 - ε * multiCLog S := by
      rw [hsum.tsum_sub (hlog_sum.mul_left ε), tsum_mul_left]
      rfl
    rw [hts] at ht
    exact ht
  · have hhi_s : Summable (fun n : ℕ =>
        wordSum S 1 n - ε * wordLogSum S n + ε ^ 2 / 2 * wordLogSqSum S n) :=
      (hsum.sub (hlog_sum.mul_left ε)).add (hlogsq_sum.mul_left (ε ^ 2 / 2))
    have ht := h1e_sum.tsum_le_tsum (fun n => (h_level n).2) hhi_s
    have hts : (∑' n : ℕ,
        (wordSum S 1 n - ε * wordLogSum S n + ε ^ 2 / 2 * wordLogSqSum S n)) =
        multiC S 1 - ε * multiCLog S + ε ^ 2 / 2 * multiCLogSq S := by
      rw [(hsum.sub (hlog_sum.mul_left ε)).tsum_add (hlogsq_sum.mul_left (ε ^ 2 / 2)),
        hsum.tsum_sub (hlog_sum.mul_left ε), tsum_mul_left, tsum_mul_left]
      rfl
    rw [hts] at ht
    exact ht

/-! ### Part 5: Master Three-Term Subcritical Asymptotics & Corollaries -/

lemma multiResolventV_sub_multiC_le {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    (hsum : Summable (wordSum S 1)) {s x : ℝ}
    (hs_lo : 1 / 2 ≤ s) (hs_hi : s ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ multiC S (2 * s) - multiResolventV S s x ∧
      multiC S (2 * s) - multiResolventV S s x ≤ 2 * multiC S 1 * x := by
  have hs_pos : 0 < s := by linarith
  have hsum2s : Summable (wordSum S (2 * s)) :=
    Summable.of_nonneg_of_le (wordSum_nonneg S (2 * s))
      (fun n => wordSum_antitone_p S hS1 (by linarith) n) hsum
  have hV_le : multiResolventV S s x ≤ multiC S (2 * s) :=
    multiResolventV_le_multiC hS1 hs_pos hx0 hsum2s
  refine ⟨sub_nonneg.mpr hV_le, ?_⟩
  have hV_sum := summable_multiResolventV hS1 hs_pos hx0 hsum2s
  have hterm : ∀ n : ℕ,
      wordSum S (2 * s) n -
          (∑ w : Fin n → {a : ℕ // a ∈ S},
            (denQ (subWord n w) + denP (subWord n w) * x) ^ (-(2 * s))) ≤
        (2 * x) * wordSum S 1 n := by
    intro n
    unfold wordSum
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    have hpd := posDigits_subWord (fun a ha => hS1 a ha) n w
    have hq_pos : 0 < denQ (subWord n w) := denQ_pos hpd
    have hq1 : 1 ≤ denQ (subWord n w) := denQ_ge_one hpd
    have hp_nn : 0 ≤ denP (subWord n w) := denP_nonneg _
    have hp_le : denP (subWord n w) ≤ denQ (subWord n w) := denP_le_denQ hpd
    let y : ℝ := (denP (subWord n w) * x) / denQ (subWord n w)
    have hy0 : 0 ≤ y := div_nonneg (mul_nonneg hp_nn hx0) hq_pos.le
    have hy_le_x : y ≤ x := by
      dsimp only [y]
      rw [div_le_iff₀ hq_pos]
      nlinarith [hx0, hp_le]
    have hy1 : y ≤ 1 := hy_le_x.trans hx1
    have h1y : 1 - 2 * y ≤ (1 + y) ^ (-(2 * s)) :=
      one_add_rpow_neg_two_ge_local hy0 hy1 (by linarith) (by linarith)
    have hsplit : (denQ (subWord n w) + denP (subWord n w) * x) ^ (-(2 * s)) =
        denQ (subWord n w) ^ (-(2 * s)) * (1 + y) ^ (-(2 * s)) := by
      have hfac : denQ (subWord n w) + denP (subWord n w) * x =
          denQ (subWord n w) * (1 + y) := by
        dsimp only [y]; field_simp [hq_pos.ne']
      rw [hfac, Real.mul_rpow hq_pos.le (by linarith)]
    have h2s_le1 : denQ (subWord n w) ^ (-(2 * s)) ≤ denQ (subWord n w) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have hq_2s_nn : 0 ≤ denQ (subWord n w) ^ (-(2 * s)) :=
      Real.rpow_nonneg hq_pos.le _
    calc denQ (subWord n w) ^ (-(2 * s)) -
          (denQ (subWord n w) + denP (subWord n w) * x) ^ (-(2 * s))
        = denQ (subWord n w) ^ (-(2 * s)) * (1 - (1 + y) ^ (-(2 * s))) := by
            rw [hsplit]; ring
      _ ≤ denQ (subWord n w) ^ (-(2 * s)) * (2 * y) := by
            refine mul_le_mul_of_nonneg_left (by linarith) hq_2s_nn
      _ ≤ denQ (subWord n w) ^ (-1 : ℝ) * (2 * x) := by
            refine mul_le_mul h2s_le1 (by linarith) (by linarith)
              (Real.rpow_nonneg hq_pos.le _)
      _ = 2 * x * denQ (subWord n w) ^ (-1 : ℝ) := by ring
  have hsub_sum := hsum2s.sub hV_sum
  have ht := hsub_sum.tsum_le_tsum hterm (hsum.mul_left (2 * x))
  have hL : (∑' n : ℕ,
      (wordSum S (2 * s) n -
        ∑ w : Fin n → {a : ℕ // a ∈ S},
          (denQ (subWord n w) + denP (subWord n w) * x) ^ (-(2 * s)))) =
      multiC S (2 * s) - multiResolventV S s x := by
    rw [hsum2s.tsum_sub hV_sum]
    rfl
  have hR : (∑' n : ℕ, 2 * x * wordSum S 1 n) = 2 * multiC S 1 * x := by
    rw [tsum_mul_left]
    change 2 * x * multiC S 1 = _
    ring
  rw [hL, hR] at ht
  exact ht

private lemma rpow_neg_diff_bound {a b p M : ℝ}
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hlow : M ≤ a) (hlow' : M ≤ b) (hM : 1 ≤ M) :
    |a ^ (-p) - b ^ (-p)| ≤ 2 * M ^ (-2 : ℝ) * |a - b| := by
  have hM_pos : 0 < M := by linarith
  have helper : ∀ u v : ℝ, u < v → M ≤ u →
      |u ^ (-p) - v ^ (-p)| ≤ 2 * M ^ (-2 : ℝ) * (v - u) := by
    intro u v huv hMu
    have hu_pos : 0 < u := lt_of_lt_of_le hM_pos hMu
    let f : ℝ → ℝ := fun t => t ^ (-p)
    have hf_cont : ContinuousOn f (Set.Icc u v) :=
      ContinuousOn.rpow continuousOn_id continuousOn_const
        fun t ht => Or.inl (by linarith [ht.1, hu_pos])
    have hf_deriv : ∀ t ∈ Set.Ioo u v, HasDerivAt f (-p * t ^ (-p - 1)) t := by
      intro t ht
      have ht_pos : 0 < t := by linarith [ht.1, hu_pos]
      simpa using Real.hasDerivAt_rpow_const (Or.inl ht_pos.ne') (p := -p)
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f
      (f' := fun t => -p * t ^ (-p - 1)) huv hf_cont hf_deriv
    have hvu_pos : 0 < v - u := sub_pos.mpr huv
    have hMξ : M ≤ ξ := by linarith [hξ.1, hMu]
    have hξ1 : 1 ≤ ξ := hM.trans hMξ
    have hξ_pos : 0 < ξ := by linarith
    have hξ2 : ξ ^ (-p - 1) ≤ M ^ (-2 : ℝ) := by
      have h1 : ξ ^ (-p - 1) ≤ ξ ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hξ1 (by linarith)
      have h2 : ξ ^ (-2 : ℝ) ≤ M ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hM_pos hMξ (by norm_num)
      exact h1.trans h2
    have hdiff : f v - f u = (-p * ξ ^ (-p - 1)) * (v - u) :=
      (div_eq_iff hvu_pos.ne').mp hslope.symm
    have h_abs : |u ^ (-p) - v ^ (-p)| = (p * ξ ^ (-p - 1)) * (v - u) := by
      rw [show |u ^ (-p) - v ^ (-p)| = |-(f v - f u)| by dsimp only [f]; ring_nf,
        abs_neg, hdiff, abs_mul, abs_of_pos hvu_pos]
      have hnn : 0 ≤ p * ξ ^ (-p - 1) := mul_nonneg (by linarith) (Real.rpow_nonneg hξ_pos.le _)
      rw [show |-p * ξ ^ (-p - 1)| = p * ξ ^ (-p - 1) by
        rw [neg_mul, abs_neg, abs_of_nonneg hnn]]
    rw [h_abs]
    have hle_coeff : p * ξ ^ (-p - 1) ≤ 2 * M ^ (-2 : ℝ) :=
      mul_le_mul hp2 hξ2 (Real.rpow_nonneg hξ_pos.le _) (by norm_num)
    exact mul_le_mul_of_nonneg_right hle_coeff hvu_pos.le
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [abs_of_neg (sub_neg.mpr hab), neg_sub]
    exact helper a b hab hlow
  · simp
  · rw [abs_sub_comm (a ^ (-p)), abs_of_pos (sub_pos.mpr hba)]
    exact helper b a hba hlow'

/-- Uniform `O(1 / m^2)` error comparing each shifted branch series with `C_S(1+ε) m^{-(1+ε)} ζ(1+ε)`. -/
lemma abs_branch_tsum_sub_le {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    (hsum : Summable (wordSum S 1)) {M₀ : ℝ} (hM₀ : 1 ≤ M₀)
    {m : ℕ} (hm : 2 * M₀ ≤ (m : ℝ)) {δ ε : ℝ}
    (hδ : |δ| ≤ M₀) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    |(∑' k : ℕ,
        multiResolventV S ((1 + ε) / 2) (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ)) *
          ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ) ^ (-(1 + ε)))) -
      multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) *
        (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε))))| ≤
      (8 * multiC S 1 * (M₀ + 1) * (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)))) / (m : ℝ) ^ 2 := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have h1m : 1 ≤ (m : ℝ) := by linarith
  have hs_lo : 1 / 2 ≤ (1 + ε) / 2 := by linarith
  have hs_hi : (1 + ε) / 2 ≤ 1 := by linarith
  have hs_pos : 0 < (1 + ε) / 2 := by linarith
  have h2s : 2 * ((1 + ε) / 2) = 1 + ε := by ring
  have hsum_1e : Summable (wordSum S (1 + ε)) :=
    Summable.of_nonneg_of_le (wordSum_nonneg S (1 + ε))
      (fun n => wordSum_antitone_p S hS1 (by linarith) n) hsum
  have hC1_nn : 0 ≤ multiC S 1 := le_trans zero_le_one (one_le_multiC hsum)
  have hC1e_nn : 0 ≤ multiC S (1 + ε) := le_trans zero_le_one (one_le_multiC hsum_1e)
  have hC1e_le : multiC S (1 + ε) ≤ multiC S 1 :=
    Summable.tsum_le_tsum (fun n => wordSum_antitone_p S hS1 (by linarith) n) hsum_1e hsum
  have hζ_1e : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε)))) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + ε))
    refine h.congr fun k => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
  have hζ_2 : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2))
    refine h.congr fun k => ?_
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (Nat.cast_nonneg _)]
  let f : ℕ → ℝ := fun k =>
    multiResolventV S ((1 + ε) / 2) (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ)) *
      ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ) ^ (-(1 + ε)))
  let g : ℕ → ℝ := fun k =>
    multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε)))
  have hlow_k : ∀ k : ℕ,
      (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 ≤ ((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ ∧
        1 ≤ (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 := fun k => by
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
    have hhalf : M₀ ≤ (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 := by
      have : 2 * M₀ ≤ ((k + 1 : ℕ) : ℝ) * (m : ℝ) := by nlinarith [hk1, hm, hM₀]
      linarith
    have hδ_le := abs_le.mp hδ
    exact ⟨by linarith, hM₀.trans hhalf⟩
  have hf_sum : Summable f := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      (hζ_1e.mul_left (multiC S 1 * ((m : ℝ) / 2) ^ (-(1 + ε))))
    · have hk_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ := by
        linarith [(hlow_k k).1, (hlow_k k).2]
      have hV_nn : 0 ≤ multiResolventV S ((1 + ε) / 2)
          (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ)) :=
        le_trans zero_le_one (one_le_multiResolventV hS1 hs_pos (by positivity) (by simpa [h2s] using hsum_1e))
      exact mul_nonneg hV_nn (Real.rpow_nonneg hk_pos.le _)
    · obtain ⟨h_ge, h_one⟩ := hlow_k k
      have hk_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ := by linarith
      have hV_le : multiResolventV S ((1 + ε) / 2)
          (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ)) ≤ multiC S 1 := by
        have h1 := multiResolventV_le_multiC hS1 hs_pos (by positivity : 0 ≤ 1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ))
          (by simpa [h2s] using hsum_1e)
        rw [h2s] at h1
        exact h1.trans hC1e_le
      have hpow_le : (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ) ^ (-(1 + ε)) ≤
          ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(1 + ε)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) h_ge (by linarith)
      have hsplit : ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(1 + ε)) =
          ((m : ℝ) / 2) ^ (-(1 + ε)) * (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε))) := by
        rw [show (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 = ((m : ℝ) / 2) * ((k + 1 : ℕ) : ℝ) by ring,
          Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
      calc f k
          ≤ multiC S 1 * ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(1 + ε)) :=
            mul_le_mul hV_le hpow_le (Real.rpow_nonneg hk_pos.le _) hC1_nn
        _ = (multiC S 1 * ((m : ℝ) / 2) ^ (-(1 + ε))) * (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε))) := by
            rw [hsplit]; ring
  have hg_sum : Summable g := hζ_1e.mul_left (multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)))
  have h_pt : ∀ k : ℕ, |f k - g k| ≤
      (8 * multiC S 1 * (M₀ + 1) / (m : ℝ) ^ 2) * (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    intro k
    obtain ⟨h_ge, h_one⟩ := hlow_k k
    let u : ℝ := ((k + 1 : ℕ) : ℝ)
    let M : ℝ := u * (m : ℝ) / 2
    let a : ℝ := u * (m : ℝ) + δ
    let b : ℝ := u * (m : ℝ)
    have hM1 : 1 ≤ M := h_one
    have hM_pos : 0 < M := by linarith
    have ha_pos : 0 < a := by linarith
    have ha1 : 1 ≤ a := hM1.trans h_ge
    have hb_ge : M ≤ b := by
      dsimp only [M, b]
      have : 0 ≤ u * (m : ℝ) := mul_nonneg (Nat.cast_nonneg _) hm_pos.le
      linarith
    have hb_pos : 0 < b := by linarith
    have hx_lo : 0 ≤ 1 / a := by positivity
    have hx_hi : 1 / a ≤ 1 := (div_le_one ha_pos).mpr ha1
    have hV_diff := multiResolventV_sub_multiC_le hS1 hsum hs_lo hs_hi hx_lo hx_hi
    rw [h2s] at hV_diff
    have ha_pow_le1 : a ^ (-(1 + ε)) ≤ a ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
    have hpart1 : |(multiResolventV S ((1 + ε) / 2) (1 / a) - multiC S (1 + ε)) * a ^ (-(1 + ε))| ≤
        2 * multiC S 1 * M ^ (-2 : ℝ) := by
      rw [abs_mul, abs_sub_comm,
        abs_of_nonneg hV_diff.1, abs_of_nonneg (Real.rpow_nonneg ha_pos.le _)]
      have ha2 : a ^ (-2 : ℝ) ≤ M ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hM_pos h_ge (by norm_num)
      have ha2_eq : (1 / a) * a ^ (-1 : ℝ) = a ^ (-2 : ℝ) := by
        rw [one_div, ← Real.rpow_neg_one a, ← Real.rpow_add ha_pos]; congr 1; norm_num
      calc (multiC S (1 + ε) - multiResolventV S ((1 + ε) / 2) (1 / a)) * a ^ (-(1 + ε))
          ≤ (2 * multiC S 1 * (1 / a)) * a ^ (-1 : ℝ) :=
            mul_le_mul hV_diff.2 ha_pow_le1 (Real.rpow_nonneg ha_pos.le _) (by positivity)
        _ = 2 * multiC S 1 * ((1 / a) * a ^ (-1 : ℝ)) := by ring
        _ = 2 * multiC S 1 * a ^ (-2 : ℝ) := by rw [ha2_eq]
        _ ≤ 2 * multiC S 1 * M ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left ha2 (by positivity)
    have hpart2 : |multiC S (1 + ε) * (a ^ (-(1 + ε)) - b ^ (-(1 + ε)))| ≤
        2 * multiC S 1 * M₀ * M ^ (-2 : ℝ) := by
      rw [abs_mul, abs_of_nonneg hC1e_nn]
      have hdiff_pow := rpow_neg_diff_bound (a := a) (b := b) (p := 1 + ε) (M := M)
        (by linarith) (by linarith) h_ge hb_ge hM1
      have hab_δ : |a - b| ≤ M₀ := by
        dsimp only [a, b]
        simpa [add_sub_cancel_left] using hδ
      calc multiC S (1 + ε) * |a ^ (-(1 + ε)) - b ^ (-(1 + ε))|
          ≤ multiC S 1 * (2 * M ^ (-2 : ℝ) * |a - b|) :=
            mul_le_mul hC1e_le hdiff_pow (abs_nonneg _) hC1_nn
        _ ≤ multiC S 1 * (2 * M ^ (-2 : ℝ) * M₀) := by
            refine mul_le_mul_of_nonneg_left ?_ hC1_nn
            exact mul_le_mul_of_nonneg_left hab_δ (by positivity)
        _ = 2 * multiC S 1 * M₀ * M ^ (-2 : ℝ) := by ring
    have hM2_eq : M ^ (-2 : ℝ) = (4 / (m : ℝ) ^ 2) * u ^ (-2 : ℝ) := by
      have hu_pos : 0 < u := by dsimp only [u]; positivity
      have hM_eq : M = (m : ℝ) / 2 * u := by dsimp only [M]; ring
      rw [hM_eq, Real.mul_rpow (by positivity) hu_pos.le,
        show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast]
      congr 1; field_simp; ring
    have hfg_eq : f k - g k =
        (multiResolventV S ((1 + ε) / 2) (1 / a) - multiC S (1 + ε)) * a ^ (-(1 + ε)) +
          multiC S (1 + ε) * (a ^ (-(1 + ε)) - b ^ (-(1 + ε))) := by
      dsimp only [f, g, a, b, u]
      rw [mul_comm (u) (m : ℝ), Real.mul_rpow hm_pos.le (Nat.cast_nonneg _)]
      ring
    calc |f k - g k|
        ≤ |(multiResolventV S ((1 + ε) / 2) (1 / a) - multiC S (1 + ε)) * a ^ (-(1 + ε))| +
            |multiC S (1 + ε) * (a ^ (-(1 + ε)) - b ^ (-(1 + ε)))| := by
            rw [hfg_eq]; exact abs_add_le _ _
      _ ≤ 2 * multiC S 1 * M ^ (-2 : ℝ) + 2 * multiC S 1 * M₀ * M ^ (-2 : ℝ) :=
            add_le_add hpart1 hpart2
      _ = 2 * multiC S 1 * (M₀ + 1) * M ^ (-2 : ℝ) := by ring
      _ = (8 * multiC S 1 * (M₀ + 1) / (m : ℝ) ^ 2) * u ^ (-2 : ℝ) := by
            rw [hM2_eq]; ring
  have hdiff_sum : Summable (fun k => |f k - g k|) :=
    (hf_sum.sub hg_sum).abs
  have hmaj_sum : Summable (fun k : ℕ =>
      (8 * multiC S 1 * (M₀ + 1) / (m : ℝ) ^ 2) * (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) :=
    hζ_2.mul_left _
  calc |∑' k : ℕ, f k - multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) *
          ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε)))|
      = |∑' k : ℕ, f k - ∑' k : ℕ, g k| := by
          dsimp only [g]; rw [tsum_mul_left]
    _ = |∑' k : ℕ, (f k - g k)| := by rw [hf_sum.tsum_sub hg_sum]
    _ ≤ ∑' k : ℕ, |f k - g k| := by
          simp only [← Real.norm_eq_abs]
          exact norm_tsum_le_tsum_norm (f := fun k => f k - g k)
            (by simpa only [Real.norm_eq_abs] using hdiff_sum)
    _ ≤ ∑' k : ℕ, (8 * multiC S 1 * (M₀ + 1) / (m : ℝ) ^ 2) * (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) :=
          hdiff_sum.tsum_le_tsum h_pt hmaj_sum
    _ = (8 * multiC S 1 * (M₀ + 1) * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) / (m : ℝ) ^ 2 := by
          rw [tsum_mul_left]; ring

/-- Real-valued total tail sum over shifted branches `(k + 1) m + r` and `(k + 1) m - b`. -/
def multiResidueTailReal (m : ℕ) (S B : Finset ℕ) (s x : ℝ) : ℝ :=
  (∑ r ∈ S, ∑' k : ℕ,
    multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
      ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) +
  (∑ b ∈ B, ∑' k : ℕ,
    multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
      ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))

/-- Finite `K`-branch truncation of `multiResidueAlphabet m S B` for dimension lower bounds. -/
def truncMultiAlphabet (m K : ℕ) (S B : Finset ℕ) : Finset ℕ :=
  S ∪ (S ×ˢ Finset.range K).image (fun p => (p.2 + 1) * m + p.1) ∪
    (B ×ˢ Finset.range K).image (fun p => (p.2 + 1) * m - p.1)

lemma truncMultiAlphabet_subset {m K : ℕ} {S B : Finset ℕ}
    (hm : S.sup id + B.sup id + 1 ≤ m) :
    (truncMultiAlphabet m K S B : Set ℕ) ⊆ multiResidueAlphabet m S B := by
  intro a ha
  simp only [Finset.mem_coe, truncMultiAlphabet, Finset.mem_union, Finset.mem_image,
    Finset.mem_product, Finset.mem_range] at ha
  rcases ha with (haS | ⟨⟨r, k⟩, ⟨hr, _⟩, rfl⟩) | ⟨⟨b, k⟩, ⟨hb, _⟩, rfl⟩
  · exact Or.inl ⟨a, haS, le_rfl, rfl⟩
  · refine Or.inl ⟨r, hr, Nat.le_add_left _ _, ?_⟩
    simp [Nat.add_mod]
  · dsimp only at *
    have hb_le : b ≤ B.sup id := Finset.le_sup (f := id) hb
    have hbm : b < m := by omega
    have hm_le : m ≤ (k + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    have hle : b ≤ (k + 1) * m := le_trans hbm.le hm_le
    refine Or.inr ⟨b, hb, k + 1, by omega, Nat.sub_add_cancel hle, by omega⟩

lemma truncMultiAlphabet_ge_one {m K : ℕ} {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hm : S.sup id + B.sup id + 1 ≤ m) :
    ∀ a ∈ truncMultiAlphabet m K S B, 1 ≤ a := fun a ha =>
  multiResidueAlphabet_ge_one hS1 a (truncMultiAlphabet_subset hm ha)

lemma truncMultiAlphabet_nonempty {m K : ℕ} {S B : Finset ℕ}
    (hm : S.sup id + B.sup id + 1 ≤ m) (hd : 1 ≤ S.card + B.card) (hK : 1 ≤ K) :
    (truncMultiAlphabet m K S B).Nonempty := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
  · have hBne : B.Nonempty := Finset.card_pos.mp (by simpa using hd)
    obtain ⟨b, hb⟩ := hBne
    refine ⟨(0 + 1) * m - b, ?_⟩
    simp only [truncMultiAlphabet, Finset.mem_union, Finset.mem_image,
      Finset.mem_product, Finset.mem_range]
    exact Or.inr ⟨(b, 0), ⟨hb, by omega⟩, rfl⟩
  · refine ⟨r, ?_⟩
    simp only [truncMultiAlphabet, Finset.mem_union]
    exact Or.inl (Or.inl hr)

lemma transferOp_truncMultiAlphabet_eq {m K : ℕ} {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hm : S.sup id + B.sup id + 1 ≤ m)
    (s : ℝ) (v : ℝ → ℝ≥0∞) (x : ℝ) :
    transferOp (truncMultiAlphabet m K S B : Set ℕ) s v x =
      transferOp (S : Set ℕ) s v x +
        (∑ r ∈ S, ∑ k ∈ Finset.range K,
          v (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) +
        (∑ b ∈ B, ∑ k ∈ Finset.range K,
          v (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))) := by
  let g : ℕ → ℝ≥0∞ := fun a =>
    v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))
  let A_S := (S ×ˢ Finset.range K).image (fun p : ℕ × ℕ => (p.2 + 1) * m + p.1)
  let A_B := (B ×ˢ Finset.range K).image (fun p : ℕ × ℕ => (p.2 + 1) * m - p.1)
  have hm_pos : 0 < m := by omega
  have hr_lt_m : ∀ r ∈ S, r < m := fun r hr => by
    have hle : r ≤ S.sup id := Finset.le_sup (f := id) hr; omega
  have hb_lt_m : ∀ b ∈ B, b < m := fun b hb => by
    have hle : b ≤ B.sup id := Finset.le_sup (f := id) hb; omega
  have hrb_lt_m : ∀ r ∈ S, ∀ b ∈ B, r + b < m := fun r hr b hb => by
    have h1 : r ≤ S.sup id := Finset.le_sup (f := id) hr
    have h2 : b ≤ B.sup id := Finset.le_sup (f := id) hb
    omega
  have hdisj_S : Disjoint S A_S := by
    rw [Finset.disjoint_left]
    intro a haS haAS
    simp only [A_S, Finset.mem_image, Finset.mem_product, Finset.mem_range] at haAS
    rcases haAS with ⟨⟨r, k⟩, ⟨_, _⟩, hak⟩
    dsimp only at hak
    have hm1 := hr_lt_m a haS
    have hm_le : m ≤ (k + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    omega
  have hdisj_SA_B : Disjoint (S ∪ A_S) A_B := by
    rw [Finset.disjoint_left]
    intro a ha haAB
    simp only [A_B, Finset.mem_image, Finset.mem_product, Finset.mem_range] at haAB
    rcases haAB with ⟨⟨b, k₂⟩, ⟨hb, _⟩, hakB⟩
    dsimp only at hakB
    have hbm := hb_lt_m b hb
    have hm_le2 : m ≤ (k₂ + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    simp only [Finset.mem_union, A_S, Finset.mem_image, Finset.mem_product, Finset.mem_range] at ha
    rcases ha with haS | ⟨⟨r, k₁⟩, ⟨hr, _⟩, hakS⟩
    · have h1 : a ≤ S.sup id := Finset.le_sup (f := id) haS
      have h2 : b ≤ B.sup id := Finset.le_sup (f := id) hb
      omega
    · dsimp only at hakS
      have hrb := hrb_lt_m r hr b hb
      have h1_nat : (k₁ + 1) * m + r + b = (k₂ + 1) * m := by omega
      have hZ : ((k₂ + 1 : ℤ) - (k₁ + 1 : ℤ)) * (m : ℤ) = (r : ℤ) + (b : ℤ) := by
        have hz : ((k₁ + 1 : ℤ)) * (m : ℤ) + (r : ℤ) + (b : ℤ) = ((k₂ + 1 : ℤ)) * (m : ℤ) := by
          exact_mod_cast h1_nat
        linarith
      have hr1 : 1 ≤ r := hS1 r hr
      have hpos : 0 < (k₂ + 1 : ℤ) - (k₁ + 1 : ℤ) := by
        by_contra hle0
        have : ((k₂ + 1 : ℤ) - (k₁ + 1 : ℤ)) * (m : ℤ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hle0) (by positivity)
        omega
      have hge_m : (m : ℤ) ≤ ((k₂ + 1 : ℤ) - (k₁ + 1 : ℤ)) * (m : ℤ) :=
        le_mul_of_one_le_left (by positivity) (by omega)
      omega
  have hinj_S : Set.InjOn (fun p : ℕ × ℕ => (p.2 + 1) * m + p.1) ↑(S ×ˢ Finset.range K) := by
    intro p₁ hp₁ p₂ hp₂ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp₁ hp₂
    dsimp only at h
    have hm1 := hr_lt_m p₁.1 hp₁.1
    have hm2 := hr_lt_m p₂.1 hp₂.1
    have hmod := congrArg (· % m) h
    simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod] at hmod
    rw [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2] at hmod
    have hk : (p₁.2 + 1) * m = (p₂.2 + 1) * m := by omega
    have hk' := Nat.mul_right_cancel hm_pos hk
    exact Prod.ext hmod (by omega)
  have hinj_B : Set.InjOn (fun p : ℕ × ℕ => (p.2 + 1) * m - p.1) ↑(B ×ˢ Finset.range K) := by
    intro p₁ hp₁ p₂ hp₂ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp₁ hp₂
    dsimp only at h
    have hm1 := hb_lt_m p₁.1 hp₁.1
    have hm2 := hb_lt_m p₂.1 hp₂.1
    have hle1 : m ≤ (p₁.2 + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    have hle2 : m ≤ (p₂.2 + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    have hZ : ((p₁.2 + 1 : ℤ) - (p₂.2 + 1 : ℤ)) * (m : ℤ) = (p₁.1 : ℤ) - (p₂.1 : ℤ) := by
      have h1Z : ((p₁.2 + 1 : ℤ)) * (m : ℤ) - (p₁.1 : ℤ) =
          ((p₂.2 + 1 : ℤ)) * (m : ℤ) - (p₂.1 : ℤ) := by
        have hnat : (p₁.2 + 1) * m - p₁.1 + p₁.1 + p₂.1 =
            (p₂.2 + 1) * m - p₂.1 + p₁.1 + p₂.1 := by omega
        have hnat' : (p₁.2 + 1) * m + p₂.1 = (p₂.2 + 1) * m + p₁.1 := by omega
        have hz : ((p₁.2 + 1 : ℤ)) * (m : ℤ) + (p₂.1 : ℤ) =
            ((p₂.2 + 1 : ℤ)) * (m : ℤ) + (p₁.1 : ℤ) := by exact_mod_cast hnat'
        linarith
      linarith
    have hdiff_lt : |((p₁.2 + 1 : ℤ) - (p₂.2 + 1 : ℤ)) * (m : ℤ)| < (m : ℤ) := by
      rw [hZ, abs_lt]; constructor <;> omega
    have hdiff0 : (p₁.2 + 1 : ℤ) - (p₂.2 + 1 : ℤ) = 0 := by
      rw [abs_mul, abs_of_pos (by exact_mod_cast hm_pos : (0 : ℤ) < m)] at hdiff_lt
      nlinarith [abs_nonneg ((p₁.2 + 1 : ℤ) - (p₂.2 + 1 : ℤ))]
    rw [hdiff0, zero_mul] at hZ
    exact Prod.ext (by omega) (by omega)
  have hsum_AS : ∑ a ∈ A_S, g a = ∑ r ∈ S, ∑ k ∈ Finset.range K, g ((k + 1) * m + r) := by
    dsimp only [A_S]
    rw [Finset.sum_image hinj_S, Finset.sum_product]
  have hsum_AB : ∑ a ∈ A_B, g a = ∑ b ∈ B, ∑ k ∈ Finset.range K, g ((k + 1) * m - b) := by
    dsimp only [A_B]
    rw [Finset.sum_image hinj_B, Finset.sum_product]
  rw [transferOp_finset_eq]
  change ∑ a ∈ S ∪ A_S ∪ A_B, g a = _
  rw [Finset.sum_union hdisj_SA_B, Finset.sum_union hdisj_S, hsum_AS, hsum_AB,
    transferOp_finset_eq]

private lemma m_rpow_zeta_approx {dC γ Cζ m α Z : ℝ}
    (hdC1 : 1 ≤ dC) (hγ_nn : 0 ≤ γ) (hCζ_pos : 0 < Cζ)
    (hm1 : 1 ≤ m) (hlog1 : 1 ≤ Real.log m)
    (hα_lo : dC / 2 ≤ α) (hα_hi : α ≤ 2 * dC)
    (ht_le1 : (2 * dC) * (Real.log m / m) ≤ 1)
    (hZ_err : |Z - (m / α + γ)| ≤ Cζ * (α / m)) :
    |m ^ (-(1 + α / m)) * Z - (1 / α - Real.log m / m + γ / m)| ≤
      (4 * dC ^ 2 + 2 * dC * γ + 2 * dC * Cζ) * ((Real.log m) ^ 2 / m ^ 2) := by
  have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have hm_nn : 0 ≤ m := hm_pos.le
  have hα_pos : 0 < α := by linarith
  have hlog_nn : 0 ≤ Real.log m := zero_le_one.trans hlog1
  have hlogsq1 : 1 ≤ (Real.log m) ^ 2 := by nlinarith [hlog1]
  let ε : ℝ := α / m
  have hε0 : 0 < ε := div_pos hα_pos hm_pos
  have ht_nn : 0 ≤ ε * Real.log m := mul_nonneg hε0.le hlog_nn
  have hexp_m := exp_neg_bounds ht_nn
  have hm_neg1e : m ^ (-(1 + ε)) = m⁻¹ * Real.exp (-(ε * Real.log m)) := by
    rw [show -(1 + ε) = -1 + -ε by ring, Real.rpow_add hm_pos, Real.rpow_neg_one,
      Real.rpow_def_of_pos hm_pos]
    congr 2; ring
  let R_exp : ℝ := Real.exp (-(ε * Real.log m)) - (1 - ε * Real.log m)
  have hR_exp_bd : |R_exp| ≤ 2 * dC ^ 2 * ((Real.log m) ^ 2 / m ^ 2) := by
    have h0 : 0 ≤ R_exp := by dsimp [R_exp]; linarith [hexp_m.1]
    have h_ub : R_exp ≤ (ε * Real.log m) ^ 2 / 2 := by dsimp [R_exp]; linarith [hexp_m.2]
    have hε_le : ε ≤ 2 * dC / m := div_le_div_of_nonneg_right hα_hi hm_nn
    have hε_sq : ε ^ 2 ≤ (2 * dC / m) ^ 2 := pow_le_pow_left₀ hε0.le hε_le 2
    have h_ub2 : (ε * Real.log m) ^ 2 / 2 ≤ 2 * dC ^ 2 * ((Real.log m) ^ 2 / m ^ 2) := by
      calc (ε * Real.log m) ^ 2 / 2
          = ε ^ 2 * (Real.log m) ^ 2 / 2 := by ring
        _ ≤ (2 * dC / m) ^ 2 * (Real.log m) ^ 2 / 2 := by gcongr
        _ = 2 * dC ^ 2 * ((Real.log m) ^ 2 / m ^ 2) := by ring
    rw [abs_of_nonneg h0]
    exact h_ub.trans h_ub2
  have hinv_α : 1 / α ≤ 2 := by rw [div_le_iff₀ hα_pos]; linarith
  have hR_exp_div : |R_exp / α| ≤ (4 * dC ^ 2) * ((Real.log m) ^ 2 / m ^ 2) := by
    rw [abs_div, abs_of_pos hα_pos]
    calc |R_exp| / α = (1 / α) * |R_exp| := by ring
      _ ≤ 2 * (2 * dC ^ 2 * ((Real.log m) ^ 2 / m ^ 2)) :=
          mul_le_mul hinv_α hR_exp_bd (abs_nonneg _) zero_le_two
      _ = 4 * dC ^ 2 * ((Real.log m) ^ 2 / m ^ 2) := by ring
  have hexp_sub_1 : |Real.exp (-(ε * Real.log m)) - 1| ≤ 2 * dC * (Real.log m / m) := by
    rw [abs_le]
    have hexp_le1 : Real.exp (-(ε * Real.log m)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hε_le : ε ≤ 2 * dC / m := div_le_div_of_nonneg_right hα_hi hm_nn
    have ht_bd : ε * Real.log m ≤ 2 * dC * (Real.log m / m) := by
      calc ε * Real.log m ≤ (2 * dC / m) * Real.log m := mul_le_mul_of_nonneg_right hε_le hlog_nn
        _ = 2 * dC * (Real.log m / m) := by ring
    constructor <;> linarith [hexp_m.1, hexp_le1, ht_bd]
  have h_gam_err : |(γ / m) * (Real.exp (-(ε * Real.log m)) - 1)| ≤
      (2 * dC * γ) * ((Real.log m) ^ 2 / m ^ 2) := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hγ_nn hm_nn)]
    calc (γ / m) * |Real.exp (-(ε * Real.log m)) - 1|
        ≤ (γ / m) * (2 * dC * (Real.log m / m)) :=
          mul_le_mul_of_nonneg_left hexp_sub_1 (div_nonneg hγ_nn hm_nn)
      _ = (2 * dC * γ) * (Real.log m / m ^ 2) := by ring
      _ ≤ (2 * dC * γ) * ((Real.log m) ^ 2 / m ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right (by nlinarith [hlog1]) (sq_nonneg _)
  have hm_pow_le1 : m ^ (-(1 + ε)) ≤ 1 / m := by
    rw [hm_neg1e, ← one_div]
    have hexp_le1 : Real.exp (-(ε * Real.log m)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    simpa using mul_le_mul_of_nonneg_left hexp_le1 (div_nonneg zero_le_one hm_nn)
  have h_zeta_tail : |m ^ (-(1 + ε)) * (Z - (m / α + γ))| ≤
      (2 * dC * Cζ) * ((Real.log m) ^ 2 / m ^ 2) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hm_nn _)]
    have hε_le : ε ≤ 2 * dC / m := div_le_div_of_nonneg_right hα_hi hm_nn
    calc m ^ (-(1 + ε)) * |Z - (m / α + γ)|
        ≤ (1 / m) * (Cζ * (2 * dC / m)) :=
          mul_le_mul hm_pow_le1 (hZ_err.trans (mul_le_mul_of_nonneg_left hε_le hCζ_pos.le))
            (abs_nonneg _) (div_nonneg zero_le_one hm_nn)
      _ = (2 * dC * Cζ) * (1 / m ^ 2) := by ring
      _ ≤ (2 * dC * Cζ) * ((Real.log m) ^ 2 / m ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right hlogsq1 (sq_nonneg _)
  have hZ_alg : m ^ (-(1 + ε)) * Z - (1 / α - Real.log m / m + γ / m) =
      m ^ (-(1 + ε)) * (Z - (m / α + γ)) + R_exp / α +
        (γ / m) * (Real.exp (-(ε * Real.log m)) - 1) := by
    have hm1e' : m ^ (-(1 + ε)) = (1 / m) * ((1 - ε * Real.log m) + R_exp) := by
      rw [hm_neg1e, one_div]; dsimp only [R_exp]; ring
    rw [show Z = (Z - (m / α + γ)) + (m / α + γ) by ring, mul_add, hm1e']
    dsimp only [R_exp, ε]
    field_simp [hm_pos.ne', hα_pos.ne']
    ring
  rw [hZ_alg]
  refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) h_gam_err).trans ?_)
  linarith [h_zeta_tail, hR_exp_div, h_gam_err]

private lemma multiC_zeta_prod_approx {dC C C' C'' γ EZ m α C_val P : ℝ}
    (hdC1 : 1 ≤ dC) (hC1 : 1 ≤ C) (hC'_nn : 0 ≤ C') (hC''_nn : 0 ≤ C'')
    (hγ_nn : 0 ≤ γ) (hEZ_nn : 0 ≤ EZ)
    (hm1 : 1 ≤ m) (hlog1 : 1 ≤ Real.log m)
    (hα_lo : dC / 2 ≤ α) (hα_hi : α ≤ 2 * dC)
    (hlog_div1 : Real.log m / m ≤ 1)
    (hP_err : |P - (1 / α - Real.log m / m + γ / m)| ≤ EZ * ((Real.log m) ^ 2 / m ^ 2))
    (hP_small : EZ * ((Real.log m) ^ 2 / m ^ 2) ≤ Real.log m / m)
    (hC_lo : C - (α / m) * C' ≤ C_val)
    (hC_hi : C_val ≤ C - (α / m) * C' + (α / m) ^ 2 / 2 * C'') :
    |C_val * P - (C / α - C * Real.log m / m + (γ * C - C') / m)| ≤
      (C * EZ + 2 * dC * C' * (γ + 2) + 2 * dC ^ 2 * C'' * (γ + 4)) *
        ((Real.log m) ^ 2 / m ^ 2) := by
  have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have hm_nn : 0 ≤ m := hm_pos.le
  have hα_pos : 0 < α := by linarith
  have hlog_nn : 0 ≤ Real.log m := zero_le_one.trans hlog1
  have hlogsq1 : 1 ≤ (Real.log m) ^ 2 := by nlinarith [hlog1]
  let ε : ℝ := α / m
  have hε0 : 0 < ε := div_pos hα_pos hm_pos
  let R_C : ℝ := C_val - (C - ε * C')
  have hR_C_bd : |R_C| ≤ 2 * dC ^ 2 * C'' * ((Real.log m) ^ 2 / m ^ 2) := by
    have h0 : 0 ≤ R_C := by dsimp [R_C, ε]; linarith
    have h_ub : R_C ≤ ε ^ 2 / 2 * C'' := by dsimp [R_C, ε]; linarith
    have hε_sq : ε ^ 2 ≤ (2 * dC / m) ^ 2 :=
      pow_le_pow_left₀ hε0.le (div_le_div_of_nonneg_right hα_hi hm_nn) 2
    have h_ub2 : ε ^ 2 / 2 * C'' ≤ (2 * dC ^ 2 * C'') * (1 / m ^ 2) := by
      calc ε ^ 2 / 2 * C'' ≤ (2 * dC / m) ^ 2 / 2 * C'' := by gcongr
        _ = (2 * dC ^ 2 * C'') * (1 / m ^ 2) := by ring
    have h_ub3 : (2 * dC ^ 2 * C'') * (1 / m ^ 2) ≤
        (2 * dC ^ 2 * C'') * ((Real.log m) ^ 2 / m ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact div_le_div_of_nonneg_right hlogsq1 (sq_nonneg _)
    rw [abs_of_nonneg h0]
    exact h_ub.trans (h_ub2.trans h_ub3)
  let R_P : ℝ := P - (1 / α - Real.log m / m + γ / m)
  have hR_P_bd : |R_P| ≤ Real.log m / m := hP_err.trans hP_small
  have hP_tail : |-Real.log m / m + γ / m + R_P| ≤ (γ + 2) * (Real.log m / m) := by
    have h_rw : -Real.log m / m + γ / m + R_P = (-(Real.log m / m) + γ / m) + R_P := by ring
    have h1 : |-(Real.log m / m) + γ / m| ≤ (γ + 1) * (Real.log m / m) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (div_nonneg hlog_nn hm_nn),
        abs_of_nonneg (div_nonneg hγ_nn hm_nn)]
      have hγ_le : γ / m ≤ γ * (Real.log m / m) := by
        rw [show γ * (Real.log m / m) = (γ / m) * Real.log m by ring]
        exact le_mul_of_one_le_right (div_nonneg hγ_nn hm_nn) hlog1
      linarith
    rw [h_rw]
    refine (abs_add_le _ _).trans ?_
    linarith [add_le_add h1 hR_P_bd]
  have hP_abs : |P| ≤ γ + 4 := by
    have hinv_bd : |1 / α| ≤ 2 := by
      rw [abs_of_nonneg (div_nonneg zero_le_one hα_pos.le), div_le_iff₀ hα_pos]
      linarith
    have htail_bd : |-Real.log m / m + γ / m + R_P| ≤ γ + 2 :=
      hP_tail.trans (mul_le_of_le_one_right (by linarith) hlog_div1)
    rw [show P = 1 / α + (-Real.log m / m + γ / m + R_P) by dsimp [R_P]; ring]
    exact (abs_add_le _ _).trans (by linarith)
  have h_alg : C_val * P - (C / α - C * Real.log m / m + (γ * C - C') / m) =
      C * R_P + (-ε * C') * (-Real.log m / m + γ / m + R_P) + R_C * P := by
    have hC_eq : C_val = (C - ε * C') + R_C := by dsimp [R_C]; ring
    have hP_eq : P = (1 / α - Real.log m / m + γ / m) + R_P := by dsimp [R_P]; ring
    rw [hC_eq, hP_eq]
    dsimp only [ε]
    field_simp [hm_pos.ne', hα_pos.ne']
    ring
  have h1 : |C * R_P| ≤ (C * EZ) * ((Real.log m) ^ 2 / m ^ 2) := by
    rw [abs_mul, abs_of_nonneg (zero_le_one.trans hC1)]
    exact (mul_le_mul_of_nonneg_left hP_err (zero_le_one.trans hC1)).trans_eq (by ring)
  have h2 : |(-ε * C') * (-Real.log m / m + γ / m + R_P)| ≤
      (2 * dC * C' * (γ + 2)) * ((Real.log m) ^ 2 / m ^ 2) := by
    rw [abs_mul]
    have h_left : |-ε * C'| ≤ 2 * dC * C' / m := by
      rw [neg_mul, abs_neg, abs_mul, abs_of_pos hε0, abs_of_nonneg hC'_nn]
      exact (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hα_hi hm_nn) hC'_nn).trans_eq
        (by ring)
    calc |-ε * C'| * |-Real.log m / m + γ / m + R_P|
        ≤ (2 * dC * C' / m) * ((γ + 2) * (Real.log m / m)) :=
          mul_le_mul h_left hP_tail (abs_nonneg _) (by positivity)
      _ = (2 * dC * C' * (γ + 2)) * (Real.log m / m ^ 2) := by ring
      _ ≤ (2 * dC * C' * (γ + 2)) * ((Real.log m) ^ 2 / m ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right (by nlinarith [hlog1]) (sq_nonneg _)
  have h3 : |R_C * P| ≤ (2 * dC ^ 2 * C'' * (γ + 4)) * ((Real.log m) ^ 2 / m ^ 2) := by
    rw [abs_mul]
    calc |R_C| * |P|
        ≤ (2 * dC ^ 2 * C'' * ((Real.log m) ^ 2 / m ^ 2)) * (γ + 4) :=
          mul_le_mul hR_C_bd hP_abs (abs_nonneg _) (by positivity)
      _ = (2 * dC ^ 2 * C'' * (γ + 4)) * ((Real.log m) ^ 2 / m ^ 2) := by ring
  rw [h_alg]
  refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) h3).trans ?_)
  linarith [h1, h2, h3]

private lemma subcritical_tail_expansion {S B : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    (hd : 1 ≤ S.card + B.card) (hsum : Summable (wordSum S 1)) :
    ∃ E₀ > 0, ∃ m₁ : ℕ, 2 ≤ m₁ ∧
      ∀ (m : ℕ), m₁ ≤ m → ∀ (α x : ℝ),
        ((S.card + B.card : ℝ) * multiC S 1) / 2 ≤ α →
        α ≤ 2 * ((S.card + B.card : ℝ) * multiC S 1) →
        x ∈ Set.Icc (0 : ℝ) 1 →
        |multiResidueTailReal m S B ((1 + α / (m : ℝ)) / 2) x -
          (((S.card + B.card : ℝ) * multiC S 1) / α -
            ((S.card + B.card : ℝ) * multiC S 1) * Real.log (m : ℝ) / (m : ℝ) +
            (S.card + B.card : ℝ) *
              (Real.eulerMascheroniConstant * multiC S 1 - multiCLog S) / (m : ℝ))| ≤
          E₀ * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) := by
  let d : ℝ := (S.card + B.card : ℝ)
  let C : ℝ := multiC S 1
  let C' : ℝ := multiCLog S
  let C'' : ℝ := multiCLogSq S
  let γ : ℝ := Real.eulerMascheroniConstant
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast hd
  have hC1 : 1 ≤ C := one_le_multiC hsum
  have hdC1 : 1 ≤ d * C := by nlinarith [hd1, hC1]
  have hC'_nn : 0 ≤ C' := multiCLog_nonneg hS1
  have hC''_nn : 0 ≤ C'' := multiCLogSq_nonneg hS1
  have hγ_nn : 0 ≤ γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  obtain ⟨Cζ, hCζ_pos, hZ_approx⟩ := abs_tsum_rpow_sub_inv_sub_eulerMascheroni_le
  let M₀ : ℝ := ((S.sup id + B.sup id + 1 : ℕ) : ℝ)
  have hM₀1 : 1 ≤ M₀ := by dsimp [M₀]; exact_mod_cast (by omega : 1 ≤ S.sup id + B.sup id + 1)
  have hζ2_sum : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2))
    refine h.congr fun k => ?_
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (Nat.cast_nonneg _)]
  let Cbr : ℝ := 8 * C * (M₀ + 1) * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ))
  have hCbr_nn : 0 ≤ Cbr := by
    have hζ2_nn : 0 ≤ ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) :=
      tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
    dsimp only [Cbr]; positivity
  let EZ : ℝ := 4 * (d * C) ^ 2 + 2 * d * C * γ + 2 * d * C * Cζ
  let E_prod : ℝ := C * EZ + 2 * d * C * C' * (γ + 2) + 2 * (d * C) ^ 2 * C'' * (γ + 4)
  let E₀ : ℝ := d * Cbr + d * E_prod + 1
  have hEZ_nn : 0 ≤ EZ := by dsimp [EZ]; positivity
  have hE0_pos : 0 < E₀ := by dsimp [E₀, E_prod]; positivity
  have ht1 : Tendsto (fun m : ℕ => (2 * d * C) * (Real.log (m : ℝ) / (m : ℝ))) atTop (nhds 0) := by
    simpa using tendsto_log_div_nat_local.const_mul (2 * d * C)
  have ht2 : Tendsto (fun m : ℕ => EZ * (Real.log (m : ℝ) / (m : ℝ))) atTop (nhds 0) := by
    simpa using tendsto_log_div_nat_local.const_mul EZ
  have h_log_div_ev : ∀ᶠ m : ℕ in atTop,
      (2 * d * C) * (Real.log (m : ℝ) / (m : ℝ)) ≤ 1 ∧
      EZ * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) ≤ Real.log (m : ℝ) / (m : ℝ) := by
    filter_upwards [ht1.eventually (gt_mem_nhds zero_lt_one),
      ht2.eventually (gt_mem_nhds zero_lt_one),
      eventually_ge_atTop 2] with m h1 h2 hm2
    refine ⟨h1.le, ?_⟩
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
    have hlog_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
    have hmul : (EZ * (Real.log (m : ℝ) / (m : ℝ))) * (Real.log (m : ℝ) / (m : ℝ)) ≤
        1 * (Real.log (m : ℝ) / (m : ℝ)) :=
      mul_le_mul h2.le le_rfl (div_nonneg hlog_nn (zero_le_one.trans hm1)) zero_le_one
    linarith [show (EZ * (Real.log (m : ℝ) / (m : ℝ))) * (Real.log (m : ℝ) / (m : ℝ)) =
      EZ * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) by ring]
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp h_log_div_ev
  let m₁ : ℕ := max M₁ (Nat.ceil (Real.exp 2) + 2 * (S.sup id + B.sup id + 1) +
    Nat.ceil (2 * d * C) + 4)
  refine ⟨E₀, hE0_pos, m₁, le_trans (by omega) (le_max_right _ _), fun m hm α x hα_lo hα_hi hx => ?_⟩
  have hm_M₁ : M₁ ≤ m := le_trans (le_max_left _ _) hm
  have hm_big : Nat.ceil (Real.exp 2) + 2 * (S.sup id + B.sup id + 1) +
      Nat.ceil (2 * d * C) + 4 ≤ m := le_trans (le_max_right _ _) hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hm_pos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hexp2_le : Real.exp 2 ≤ (m : ℝ) :=
    (Nat.le_ceil (Real.exp 2)).trans (by exact_mod_cast (by omega : Nat.ceil (Real.exp 2) ≤ m))
  have hlog_ge2 : 2 ≤ Real.log (m : ℝ) := by
    have := Real.log_le_log (Real.exp_pos 2) hexp2_le
    rwa [Real.log_exp] at this
  have hlog_ge1 : 1 ≤ Real.log (m : ℝ) := by linarith
  have hlogsq1 : 1 ≤ (Real.log (m : ℝ)) ^ 2 := by nlinarith [hlog_ge1]
  have hm_2M0 : 2 * M₀ ≤ (m : ℝ) := by
    dsimp [M₀]; exact_mod_cast (by omega : 2 * (S.sup id + B.sup id + 1) ≤ m)
  have hm_2dC : 2 * d * C ≤ (m : ℝ) :=
    (Nat.le_ceil (2 * d * C)).trans (by exact_mod_cast (by omega : Nat.ceil (2 * d * C) ≤ m))
  have hα_lo' : d * C / 2 ≤ α := hα_lo
  have hα_hi' : α ≤ 2 * (d * C) := hα_hi
  let ε : ℝ := α / (m : ℝ)
  have hα_pos : 0 < α := by linarith [hα_lo', hdC1]
  have hε0 : 0 < ε := div_pos hα_pos hm_pos
  have hε1 : ε ≤ 1 := (div_le_one hm_pos).mpr (by linarith)
  have h_ld := hM₁ m hm_M₁
  let s : ℝ := (1 + ε) / 2
  have h2s : 2 * s = 1 + ε := by dsimp [s]; ring
  let Z : ℝ := ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(1 + ε)))
  have h_br_S : ∀ r ∈ S,
      |(∑' k : ℕ, multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) -
        multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z| ≤ Cbr / (m : ℝ) ^ 2 := by
    intro r hr
    have hr_le : (r : ℝ) ≤ ((S.sup id : ℕ) : ℝ) := by exact_mod_cast Finset.le_sup (f := id) hr
    have hM0_eq : M₀ = ((S.sup id : ℕ) : ℝ) + ((B.sup id : ℕ) : ℝ) + 1 := by
      dsimp [M₀]; push_cast; ring
    have hδ : |(r : ℝ) + x| ≤ M₀ := by
      rw [abs_le]
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) r, hx.1, hx.2,
        Nat.cast_nonneg (α := ℝ) (B.sup id)]
    have hcongr : (∑' k : ℕ, multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
        ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) =
        (∑' k : ℕ, multiResolventV S ((1 + ε) / 2)
          (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((r : ℝ) + x))) *
          ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((r : ℝ) + x)) ^ (-(1 + ε)))) := by
      refine tsum_congr fun k => ?_
      have hcast : ((((k + 1) * m + r : ℕ) : ℝ) + x) =
          ((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((r : ℝ) + x) := by push_cast; ring
      rw [hcast, h2s]
    rw [hcongr]
    exact abs_branch_tsum_sub_le hS1 hsum hM₀1 hm_2M0 hδ hε0 hε1
  have h_br_B : ∀ b ∈ B,
      |(∑' k : ℕ, multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) -
        multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z| ≤ Cbr / (m : ℝ) ^ 2 := by
    intro b hb
    have hb_nat : b ≤ B.sup id := Finset.le_sup (f := id) hb
    have hb_le : (b : ℝ) ≤ ((B.sup id : ℕ) : ℝ) := by exact_mod_cast hb_nat
    have hbm : b ≤ m := le_trans hb_nat (by omega)
    have hM0_eq : M₀ = ((S.sup id : ℕ) : ℝ) + ((B.sup id : ℕ) : ℝ) + 1 := by
      dsimp [M₀]; push_cast; ring
    have hδ : |(-(b : ℝ) + x)| ≤ M₀ := by
      rw [abs_le]
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) b, hx.1, hx.2,
        Nat.cast_nonneg (α := ℝ) (S.sup id)]
    have hcongr : (∑' k : ℕ, multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
        ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) =
        (∑' k : ℕ, multiResolventV S ((1 + ε) / 2)
          (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x))) *
          ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x)) ^ (-(1 + ε)))) := by
      refine tsum_congr fun k => ?_
      have hk1m : b ≤ (k + 1) * m := le_trans hbm (Nat.le_mul_of_pos_left m (by omega))
      have hcast : ((((k + 1) * m - b : ℕ) : ℝ) + x) =
          ((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x) := by
        rw [Nat.cast_sub hk1m]; push_cast; ring
      rw [hcast, h2s]
    rw [hcongr]
    exact abs_branch_tsum_sub_le hS1 hsum hM₀1 hm_2M0 hδ hε0 hε1
  have h_br_tot :
      |multiResidueTailReal m S B s x - d * (multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z)| ≤
        (d * Cbr) * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) := by
    let T_0 : ℝ := multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z
    have hS_bd : |(∑ r ∈ S, ∑' k : ℕ, multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
        ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) - (S.card : ℝ) * T_0| ≤
        (S.card : ℝ) * (Cbr / (m : ℝ) ^ 2) := by
      rw [show (S.card : ℝ) * T_0 = ∑ _r ∈ S, T_0 by rw [Finset.sum_const, nsmul_eq_mul],
        ← Finset.sum_sub_distrib]
      calc |∑ r ∈ S, _| ≤ ∑ r ∈ S, |∑' k : ℕ, _ - T_0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _r ∈ S, (Cbr / (m : ℝ) ^ 2) := Finset.sum_le_sum fun r hr => h_br_S r hr
        _ = (S.card : ℝ) * (Cbr / (m : ℝ) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hB_bd : |(∑ b ∈ B, ∑' k : ℕ, multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
        ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) - (B.card : ℝ) * T_0| ≤
        (B.card : ℝ) * (Cbr / (m : ℝ) ^ 2) := by
      rw [show (B.card : ℝ) * T_0 = ∑ _b ∈ B, T_0 by rw [Finset.sum_const, nsmul_eq_mul],
        ← Finset.sum_sub_distrib]
      calc |∑ b ∈ B, _| ≤ ∑ b ∈ B, |∑' k : ℕ, _ - T_0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _b ∈ B, (Cbr / (m : ℝ) ^ 2) := Finset.sum_le_sum fun b hb => h_br_B b hb
        _ = (B.card : ℝ) * (Cbr / (m : ℝ) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hsplit : multiResidueTailReal m S B s x - d * T_0 =
        ((∑ r ∈ S, ∑' k : ℕ, multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) - (S.card : ℝ) * T_0) +
          ((∑ b ∈ B, ∑' k : ℕ, multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) - (B.card : ℝ) * T_0) := by
      dsimp only [multiResidueTailReal, d]; ring
    have h1 : |multiResidueTailReal m S B s x - d * T_0| ≤ (d * Cbr) / (m : ℝ) ^ 2 := by
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      have : (S.card : ℝ) * (Cbr / (m : ℝ) ^ 2) + (B.card : ℝ) * (Cbr / (m : ℝ) ^ 2) =
          (d * Cbr) / (m : ℝ) ^ 2 := by dsimp only [d]; ring
      linarith only [hS_bd, hB_bd, this]
    have h1_le : (d * Cbr) / (m : ℝ) ^ 2 ≤ (d * Cbr) * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) := by
      rw [show (d * Cbr) / (m : ℝ) ^ 2 = ((d * Cbr) / (m : ℝ) ^ 2) * 1 by ring,
        show (d * Cbr) * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) =
          ((d * Cbr) / (m : ℝ) ^ 2) * (Real.log (m : ℝ)) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left hlogsq1 (by positivity)
    exact h1.trans h1_le
  have hZ_err : |Z - ((m : ℝ) / α + γ)| ≤ Cζ * (α / (m : ℝ)) := by
    have h1 := hZ_approx ε hε0 hε1
    have heqv : 1 / ε = (m : ℝ) / α := by dsimp only [ε]; rw [one_div_div]
    simpa [Z, γ, sub_sub, heqv] using h1
  have hP_approx := m_rpow_zeta_approx hdC1 hγ_nn hCζ_pos hm1 hlog_ge1 hα_lo'
    (by linarith only [hα_hi'] : α ≤ 2 * (d * C))
    (by linarith only [h_ld.1] : 2 * (d * C) * (Real.log (m : ℝ) / (m : ℝ)) ≤ 1)
    hZ_err
  have hC_bds := multiC_one_add_bounds hS1 hsum hε0.le
  have hlog_div1 : Real.log (m : ℝ) / (m : ℝ) ≤ 1 := by
    have h_nn : 0 ≤ Real.log (m : ℝ) / (m : ℝ) :=
      div_nonneg (zero_le_one.trans hlog_ge1) hm_pos.le
    have h_mul := le_mul_of_one_le_left h_nn (by linarith only [hdC1] : (1 : ℝ) ≤ 2 * d * C)
    linarith only [h_mul, h_ld.1]
  have hprod := multiC_zeta_prod_approx hdC1 hC1 hC'_nn hC''_nn hγ_nn hEZ_nn hm1 hlog_ge1
    hα_lo' (by linarith only [hα_hi'] : α ≤ 2 * (d * C)) hlog_div1
    (by
      dsimp only [EZ, ε]
      refine hP_approx.trans_eq ?_
      ring)
    h_ld.2 hC_bds.1 hC_bds.2
  have h_final_alg : multiResidueTailReal m S B s x -
      (d * C / α - d * C * Real.log (m : ℝ) / (m : ℝ) + d * (γ * C - C') / (m : ℝ)) =
      (multiResidueTailReal m S B s x - d * (multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z)) +
        d * (multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z -
          (C / α - C * Real.log (m : ℝ) / (m : ℝ) + (γ * C - C') / (m : ℝ))) := by
    ring
  rw [h_final_alg]
  have hd_prod : |d * (multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z -
      (C / α - C * Real.log (m : ℝ) / (m : ℝ) + (γ * C - C') / (m : ℝ)))| ≤
      (d * E_prod) * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) := by
    rw [abs_mul, abs_of_nonneg (zero_le_one.trans hd1)]
    have hprod' : |multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z -
        (C / α - C * Real.log (m : ℝ) / (m : ℝ) + (γ * C - C') / (m : ℝ))| ≤
        E_prod * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) := by
      dsimp only [E_prod, EZ, ε] at hprod ⊢
      simpa only [mul_assoc] using hprod
    calc d * _ ≤ d * (E_prod * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hprod' (zero_le_one.trans hd1)
      _ = (d * E_prod) * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) := by ring
  have hnn : 0 ≤ (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by positivity
  have hcomb : d * Cbr + d * E_prod ≤ E₀ := by dsimp only [E₀]; linarith only []
  calc |multiResidueTailReal m S B s x - d * (multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z) +
        d * (multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z -
          (C / α - C * Real.log (m : ℝ) / (m : ℝ) + (γ * C - C') / (m : ℝ)))|
      ≤ |multiResidueTailReal m S B s x - d * (multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z)| +
          |d * (multiC S (1 + ε) * (m : ℝ) ^ (-(1 + ε)) * Z -
            (C / α - C * Real.log (m : ℝ) / (m : ℝ) + (γ * C - C') / (m : ℝ)))| :=
        abs_add_le _ _
    _ ≤ (d * Cbr) * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) +
          (d * E_prod) * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) :=
        add_le_add h_br_tot hd_prod
    _ = (d * Cbr + d * E_prod) * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) := by ring
    _ ≤ E₀ * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcomb hnn

private lemma dimH_multiResidue_upper_of_tail_le {m : ℕ} {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hm_sep : S.sup id + B.sup id + 1 ≤ m)
    (hm_2M0 : 2 * ((S.sup id + B.sup id + 1 : ℕ) : ℝ) ≤ (m : ℝ))
    {s : ℝ} (hs_lo : 1 / 2 < s) (hs_hi : s ≤ 1)
    (hsum : Summable (wordSum S 1))
    (htail : ∀ x ∈ Set.Icc (0 : ℝ) 1, multiResidueTailReal m S B s x ≤ 1) :
    dimH (multiResidueSet m S B) ≤ ENNReal.ofReal s := by
  let M₀ : ℝ := ((S.sup id + B.sup id + 1 : ℕ) : ℝ)
  have hM₀1 : 1 ≤ M₀ := by dsimp [M₀]; exact_mod_cast (by omega : 1 ≤ S.sup id + B.sup id + 1)
  have hs_pos : 0 < s := by linarith
  have hsum_s : Summable (wordSum S (2 * s)) :=
    Summable.of_nonneg_of_le (wordSum_nonneg S (2 * s))
      (fun n => wordSum_antitone_p S hS1 (by linarith) n) hsum
  let C : ℝ := multiC S 1
  have hC1 : 1 ≤ C := one_le_multiC hsum
  have hCs_le : multiC S (2 * s) ≤ C :=
    Summable.tsum_le_tsum (fun n => wordSum_antitone_p S hS1 (by linarith) n) hsum_s hsum
  have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by dsimp only [M₀] at hM₀1; linarith only [hm_2M0, hM₀1]
  have hV_ge1 : ∀ y : ℝ, 0 ≤ y → 1 ≤ multiResolventV S s y :=
    fun y hy => one_le_multiResolventV hS1 hs_pos hy hsum_s
  have hV_leC : ∀ y : ℝ, 0 ≤ y → multiResolventV S s y ≤ C :=
    fun y hy => (multiResolventV_le_multiC hS1 hs_pos hy hsum_s).trans hCs_le
  let v : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (multiResolventV S s x)
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal 1 ≤ v x ∧ v x ≤ ENNReal.ofReal C := fun x hx =>
    ⟨ENNReal.ofReal_le_ofReal (hV_ge1 x hx.1), ENNReal.ofReal_le_ofReal (hV_leC x hx.1)⟩
  have hterm_sum : ∀ δ : ℝ, |δ| ≤ M₀ →
      Summable fun k : ℕ =>
        multiResolventV S s (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ)) *
          ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ) ^ (-(2 * s))) := fun δ hδ => by
    have hζ : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-(2 * s)))) := by
      have h := (summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 2 * s))
      refine h.congr fun k => ?_
      rw [Real.rpow_neg (Nat.cast_nonneg _)]
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      (hζ.mul_left (C * ((m : ℝ) / 2) ^ (-(2 * s))))
    · have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      have h_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ := by
        have := (abs_le.mp hδ).1; nlinarith [hk1, hm_2M0, hM₀1]
      exact mul_nonneg (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one h_pos.le)))
        (Real.rpow_nonneg h_pos.le _)
    · have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      have hk_ge : (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 ≤ ((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ := by
        have := (abs_le.mp hδ).1; nlinarith [hk1, hm_2M0]
      have h_half_pos : 0 < (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 := by nlinarith [hk1, hm_ge2]
      have h_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ := by linarith only [h_half_pos, hk_ge]
      have hV_le := hV_leC (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ)) (div_nonneg zero_le_one h_pos.le)
      have hpow := Real.rpow_le_rpow_of_nonpos (z := -(2 * s)) h_half_pos hk_ge
        (by linarith only [hs_pos])
      have hsplit : ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(2 * s)) =
          ((m : ℝ) / 2) ^ (-(2 * s)) * (((k + 1 : ℕ) : ℝ) ^ (-(2 * s))) := by
        rw [show (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 = ((m : ℝ) / 2) * ((k + 1 : ℕ) : ℝ) by ring,
          Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
      calc _ ≤ C * ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(2 * s)) :=
            mul_le_mul hV_le hpow (Real.rpow_nonneg h_pos.le _) (zero_le_one.trans hC1)
        _ = _ := by rw [hsplit]; ring
  have hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      transferOp (multiResidueAlphabet m S B) s v x ≤ v x := by
    intro x hx
    rw [transferOp_multiResidueAlphabet_eq hS1 hm_sep s v x]
    have hS_part : transferOp (S : Set ℕ) s v x = ENNReal.ofReal (multiResolventV S s x - 1) := by
      rw [transferOp_finset_eq]
      have hbr := multiResolventV_branch_eq hS1 hs_pos hx.1 hsum_s
      have hnonneg : ∀ a ∈ S, 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) *
          multiResolventV S s (1 / ((a : ℝ) + x)) := fun a _ =>
        mul_nonneg (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]) _)
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]))))
      calc (∑ a ∈ S, v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))))
          = ∑ a ∈ S, ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)) *
              multiResolventV S s (1 / ((a : ℝ) + x))) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              have ha_nn : 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) :=
                Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]) _
              dsimp only [v]; rw [mul_comm, ← ENNReal.ofReal_mul ha_nn]
        _ = ENNReal.ofReal (∑ a ∈ S, ((a : ℝ) + x) ^ (-(2 * s)) *
              multiResolventV S s (1 / ((a : ℝ) + x))) :=
              (ENNReal.ofReal_sum_of_nonneg hnonneg).symm
        _ = ENNReal.ofReal (multiResolventV S s x - 1) := by rw [hbr]
    have hM0_eq : M₀ = ((S.sup id : ℕ) : ℝ) + ((B.sup id : ℕ) : ℝ) + 1 := by
      dsimp [M₀]; push_cast; ring
    have hS_tsum :
        (∑ r ∈ S, ∑' k : ℕ, v (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
          ENNReal.ofReal (∑ r ∈ S, ∑' k : ℕ,
            multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
              ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      have h_nn_r : ∀ r ∈ S, 0 ≤ ∑' k : ℕ,
          multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun r _ =>
        tsum_nonneg fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _)
      rw [ENNReal.ofReal_sum_of_nonneg h_nn_r]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_le : (r : ℝ) ≤ ((S.sup id : ℕ) : ℝ) := by exact_mod_cast Finset.le_sup (f := id) hr
      have hδ : |(r : ℝ) + x| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) r, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (B.sup id)]
      have hsum_r' : Summable fun k : ℕ =>
          multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := by
        refine (hterm_sum ((r : ℝ) + x) hδ).congr fun k => ?_
        congr 2 <;> push_cast <;> ring
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _))
        hsum_r']
      refine tsum_congr fun k => ?_
      dsimp only [v]
      rw [ENNReal.ofReal_mul (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
        (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))]
    have hB_tsum :
        (∑ b ∈ B, ∑' k : ℕ, v (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
          ENNReal.ofReal (∑ b ∈ B, ∑' k : ℕ,
            multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
              ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      have h_nn_b : ∀ b ∈ B, 0 ≤ ∑' k : ℕ,
          multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun b _ =>
        tsum_nonneg fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _)
      rw [ENNReal.ofReal_sum_of_nonneg h_nn_b]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb_nat : b ≤ B.sup id := Finset.le_sup (f := id) hb
      have hb_le : (b : ℝ) ≤ ((B.sup id : ℕ) : ℝ) := by exact_mod_cast hb_nat
      have hbm : b ≤ m := le_trans hb_nat (by omega)
      have hδ : |(-(b : ℝ) + x)| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) b, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (S.sup id)]
      have hsum_b' : Summable fun k : ℕ =>
          multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) := by
        refine (hterm_sum (-(b : ℝ) + x) hδ).congr fun k => ?_
        have hk1m : b ≤ (k + 1) * m := le_trans hbm (Nat.le_mul_of_pos_left m (by omega))
        have hcast : ((((k + 1) * m - b : ℕ) : ℝ) + x) =
            ((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x) := by
          rw [Nat.cast_sub hk1m]; push_cast; ring
        rw [hcast]
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _))
        hsum_b']
      refine tsum_congr fun k => ?_
      dsimp only [v]
      rw [ENNReal.ofReal_mul (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
        (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))]
    have hvx_ge1 : 1 ≤ multiResolventV S s x := hV_ge1 x hx.1
    have h_S_nn : 0 ≤ ∑ r ∈ S, ∑' k : ℕ,
        multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
      Finset.sum_nonneg fun r _ => tsum_nonneg fun k => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _)
    have h_B_nn : 0 ≤ ∑ b ∈ B, ∑' k : ℕ,
        multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
      Finset.sum_nonneg fun b _ => tsum_nonneg fun k => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _)
    have htail_nn : 0 ≤ multiResidueTailReal m S B s x := add_nonneg h_S_nn h_B_nn
    rw [hS_part, hS_tsum, hB_tsum, add_assoc, ← ENNReal.ofReal_add h_S_nn h_B_nn]
    change ENNReal.ofReal (multiResolventV S s x - 1) +
      ENNReal.ofReal (multiResidueTailReal m S B s x) ≤ v x
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hvx_ge1) htail_nn]
    exact ENNReal.ofReal_le_ofReal (by linarith [htail x hx])
  exact dimH_le_of_transferOp_le (multiResidueAlphabet_ge_one hS1) hs_pos
    (by simp : (0 : ℝ≥0∞) < ENNReal.ofReal 1) ENNReal.ofReal_lt_top hv_bd hsub

private lemma single_branch_rem_le {f maj : ℕ → ℝ} (K : ℕ)
    (hf_nn : ∀ k, 0 ≤ f k) (hmaj_sum : Summable maj)
    (hdom : ∀ k, f k ≤ maj k) :
    (∑' k : ℕ, f k) - ∑ k ∈ Finset.range K, f k ≤ ∑' k : ℕ, maj (k + K) := by
  have hf_sum : Summable f := Summable.of_nonneg_of_le hf_nn hdom hmaj_sum
  rw [sub_eq_iff_eq_add'.mpr (hf_sum.sum_add_tsum_nat_add K).symm]
  exact (hf_sum.comp_injective (add_left_injective K)).tsum_le_tsum
    (fun k => hdom (k + K)) ((summable_nat_add_iff K).mpr hmaj_sum)

private lemma dimH_multiResidue_lower_of_tail_ge {m : ℕ} {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hd : 1 ≤ S.card + B.card)
    (hm_sep : S.sup id + B.sup id + 1 ≤ m)
    (hm_2M0 : 2 * ((S.sup id + B.sup id + 1 : ℕ) : ℝ) ≤ (m : ℝ))
    {s gap : ℝ} (hs_lo : 1 / 2 < s) (hs_hi : s ≤ 1) (hgap_pos : 0 < gap)
    (hsum : Summable (wordSum S 1))
    (htail : ∀ x ∈ Set.Icc (0 : ℝ) 1, 1 + gap ≤ multiResidueTailReal m S B s x) :
    ENNReal.ofReal s ≤ dimH (multiResidueSet m S B) := by
  let M₀ : ℝ := ((S.sup id + B.sup id + 1 : ℕ) : ℝ)
  let d : ℝ := (S.card + B.card : ℝ)
  let C : ℝ := multiC S 1
  have hM₀1 : 1 ≤ M₀ := by dsimp [M₀]; exact_mod_cast (by omega : 1 ≤ S.sup id + B.sup id + 1)
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast hd
  have hC1 : 1 ≤ C := one_le_multiC hsum
  have hs_pos : 0 < s := by linarith
  have hsum_s : Summable (wordSum S (2 * s)) :=
    Summable.of_nonneg_of_le (wordSum_nonneg S (2 * s))
      (fun n => wordSum_antitone_p S hS1 (by linarith) n) hsum
  have hCs_le : multiC S (2 * s) ≤ C :=
    Summable.tsum_le_tsum (fun n => wordSum_antitone_p S hS1 (by linarith) n) hsum_s hsum
  have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by dsimp only [M₀] at hM₀1; linarith only [hm_2M0, hM₀1]
  have hV_ge1 : ∀ y : ℝ, 0 ≤ y → 1 ≤ multiResolventV S s y :=
    fun y hy => one_le_multiResolventV hS1 hs_pos hy hsum_s
  have hV_leC : ∀ y : ℝ, 0 ≤ y → multiResolventV S s y ≤ C :=
    fun y hy => (multiResolventV_le_multiC hS1 hs_pos hy hsum_s).trans hCs_le
  let maj : ℕ → ℝ := fun k => C * ((((k + 1 : ℕ) : ℝ) * (m : ℝ) / 2) ^ (-(2 * s)))
  have hmaj_sum : Summable maj := by
    have hζ : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-(2 * s)))) := by
      have h := (summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 2 * s))
      refine h.congr fun k => ?_
      rw [Real.rpow_neg (Nat.cast_nonneg _)]
    refine (hζ.mul_left (C * ((m : ℝ) / 2) ^ (-(2 * s)))).congr fun k => ?_
    dsimp only [maj]
    rw [show ((k + 1 : ℕ) : ℝ) * (m : ℝ) / 2 = ((m : ℝ) / 2) * ((k + 1 : ℕ) : ℝ) by ring,
      Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
    ring
  let U : ℕ → ℝ := fun k => d * maj k
  have hU_sum : Summable U := hmaj_sum.mul_left d
  have htend_diff : Tendsto (fun K : ℕ => (∑' k : ℕ, U k) - ∑ k ∈ Finset.range K, U k)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := ∑' k : ℕ, U k)).sub hU_sum.hasSum.tendsto_sum_nat
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (htend_diff.eventually (gt_mem_nhds (half_pos hgap_pos)))
  let Kmax : ℕ := max K₀ 1
  have hKmax_ge1 : 1 ≤ Kmax := le_max_right _ _
  have hU_tail_lt : (∑' k : ℕ, U k) - ∑ k ∈ Finset.range Kmax, U k < gap / 2 :=
    hK₀ Kmax (le_max_left _ _)
  let v : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (multiResolventV S s x)
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal 1 ≤ v x ∧ v x ≤ ENNReal.ofReal C := fun x hx =>
    ⟨ENNReal.ofReal_le_ofReal (hV_ge1 x hx.1), ENNReal.ofReal_le_ofReal (hV_leC x hx.1)⟩
  let A_fin := truncMultiAlphabet m Kmax S B
  have hAne := truncMultiAlphabet_nonempty hm_sep hd hKmax_ge1
  have ha1 := truncMultiAlphabet_ge_one (K := Kmax) hS1 hm_sep
  have hM0_eq : M₀ = ((S.sup id : ℕ) : ℝ) + ((B.sup id : ℕ) : ℝ) + 1 := by
    dsimp [M₀]; push_cast; ring
  have hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1, v x ≤ transferOp (A_fin : Set ℕ) s v x := by
    intro x hx
    let tailFin : ℝ :=
      (∑ r ∈ S, ∑ k ∈ Finset.range Kmax,
        multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) +
      (∑ b ∈ B, ∑ k ∈ Finset.range Kmax,
        multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))
    have hdom_shift : ∀ δ : ℝ, |δ| ≤ M₀ → ∀ k : ℕ,
        0 ≤ multiResolventV S s (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ)) *
            ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ) ^ (-(2 * s))) ∧
        multiResolventV S s (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ)) *
            ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ) ^ (-(2 * s))) ≤ maj k := fun δ hδ k => by
      have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      have hk_ge : (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 ≤ ((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ := by
        have := (abs_le.mp hδ).1; nlinarith [hk1, hm_2M0]
      have h_half_pos : 0 < (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 := by nlinarith [hk1, hm_ge2]
      have h_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ := by linarith only [h_half_pos, hk_ge]
      have hV_nn := zero_le_one.trans (hV_ge1 (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ))
        (div_nonneg zero_le_one h_pos.le))
      have hV_le := hV_leC (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ)) (div_nonneg zero_le_one h_pos.le)
      have hpow := Real.rpow_le_rpow_of_nonpos (z := -(2 * s)) h_half_pos hk_ge
        (by linarith only [hs_pos])
      exact ⟨mul_nonneg hV_nn (Real.rpow_nonneg h_pos.le _),
        mul_le_mul hV_le hpow (Real.rpow_nonneg h_pos.le _) (zero_le_one.trans hC1)⟩
    have hS_rem : (∑ r ∈ S, ∑' k : ℕ,
          multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) -
        (∑ r ∈ S, ∑ k ∈ Finset.range Kmax,
          multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) ≤
        (S.card : ℝ) * ∑' k : ℕ, maj (k + Kmax) := by
      rw [← Finset.sum_sub_distrib,
        show (S.card : ℝ) * ∑' k : ℕ, maj (k + Kmax) = ∑ _r ∈ S, ∑' k : ℕ, maj (k + Kmax) by
          rw [Finset.sum_const, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun r hr => ?_
      have hr_le : (r : ℝ) ≤ ((S.sup id : ℕ) : ℝ) := by exact_mod_cast Finset.le_sup (f := id) hr
      have hδ : |(r : ℝ) + x| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) r, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (B.sup id)]
      refine single_branch_rem_le Kmax (fun k => ?_) hmaj_sum (fun k => ?_)
      · have hk1m : ((((k + 1) * m + r : ℕ) : ℝ) + x) =
            ((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((r : ℝ) + x) := by push_cast; ring
        rw [hk1m]; exact (hdom_shift ((r : ℝ) + x) hδ k).1
      · have hk1m : ((((k + 1) * m + r : ℕ) : ℝ) + x) =
            ((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((r : ℝ) + x) := by push_cast; ring
        rw [hk1m]; exact (hdom_shift ((r : ℝ) + x) hδ k).2
    have hB_rem : (∑ b ∈ B, ∑' k : ℕ,
          multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) -
        (∑ b ∈ B, ∑ k ∈ Finset.range Kmax,
          multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) ≤
        (B.card : ℝ) * ∑' k : ℕ, maj (k + Kmax) := by
      rw [← Finset.sum_sub_distrib,
        show (B.card : ℝ) * ∑' k : ℕ, maj (k + Kmax) = ∑ _b ∈ B, ∑' k : ℕ, maj (k + Kmax) by
          rw [Finset.sum_const, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun b hb => ?_
      have hb_nat : b ≤ B.sup id := Finset.le_sup (f := id) hb
      have hb_le : (b : ℝ) ≤ ((B.sup id : ℕ) : ℝ) := by exact_mod_cast hb_nat
      have hbm : b ≤ m := le_trans hb_nat (by omega)
      have hδ : |(-(b : ℝ) + x)| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) b, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (S.sup id)]
      refine single_branch_rem_le Kmax (fun k => ?_) hmaj_sum (fun k => ?_)
      · have hk1m : b ≤ (k + 1) * m := le_trans hbm (Nat.le_mul_of_pos_left m (by omega))
        have hcast : ((((k + 1) * m - b : ℕ) : ℝ) + x) =
            ((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x) := by
          rw [Nat.cast_sub hk1m]; push_cast; ring
        rw [hcast]; exact (hdom_shift (-(b : ℝ) + x) hδ k).1
      · have hk1m : b ≤ (k + 1) * m := le_trans hbm (Nat.le_mul_of_pos_left m (by omega))
        have hcast : ((((k + 1) * m - b : ℕ) : ℝ) + x) =
            ((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x) := by
          rw [Nat.cast_sub hk1m]; push_cast; ring
        rw [hcast]; exact (hdom_shift (-(b : ℝ) + x) hδ k).2
    have hU_rem : d * ∑' k : ℕ, maj (k + Kmax) =
        (∑' k : ℕ, U k) - ∑ k ∈ Finset.range Kmax, U k := by
      rw [← tsum_mul_left, sub_eq_iff_eq_add'.mpr (hU_sum.sum_add_tsum_nat_add Kmax).symm]
    have htail_diff : multiResidueTailReal m S B s x - tailFin ≤
        (∑' k : ℕ, U k) - ∑ k ∈ Finset.range Kmax, U k := by
      dsimp only [multiResidueTailReal, tailFin]
      have hcomb := add_le_add hS_rem hB_rem
      have hSB : (S.card : ℝ) * ∑' k : ℕ, maj (k + Kmax) + (B.card : ℝ) * ∑' k : ℕ, maj (k + Kmax) =
          d * ∑' k : ℕ, maj (k + Kmax) := by dsimp only [d]; ring
      linarith
    have htailFin_ge1 : 1 ≤ tailFin := by linarith [htail x hx]
    rw [transferOp_truncMultiAlphabet_eq hS1 hm_sep s v x]
    have hS_part : transferOp (S : Set ℕ) s v x = ENNReal.ofReal (multiResolventV S s x - 1) := by
      rw [transferOp_finset_eq]
      have hbr := multiResolventV_branch_eq hS1 hs_pos hx.1 hsum_s
      have hnonneg : ∀ a ∈ S, 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) *
          multiResolventV S s (1 / ((a : ℝ) + x)) := fun a _ =>
        mul_nonneg (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]) _)
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]))))
      calc (∑ a ∈ S, v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))))
          = ∑ a ∈ S, ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)) *
              multiResolventV S s (1 / ((a : ℝ) + x))) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              have ha_nn : 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) :=
                Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]) _
              dsimp only [v]; rw [mul_comm, ← ENNReal.ofReal_mul ha_nn]
        _ = ENNReal.ofReal (∑ a ∈ S, ((a : ℝ) + x) ^ (-(2 * s)) *
              multiResolventV S s (1 / ((a : ℝ) + x))) :=
              (ENNReal.ofReal_sum_of_nonneg hnonneg).symm
        _ = ENNReal.ofReal (multiResolventV S s x - 1) := by rw [hbr]
    have hfinS_eq :
        (∑ r ∈ S, ∑ k ∈ Finset.range Kmax, v (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
          ENNReal.ofReal (∑ r ∈ S, ∑ k ∈ Finset.range Kmax,
            multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
              ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => Finset.sum_nonneg fun k _ => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _))]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _))]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [v]
      rw [ENNReal.ofReal_mul (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
        (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))]
    have hfinB_eq :
        (∑ b ∈ B, ∑ k ∈ Finset.range Kmax, v (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
          ENNReal.ofReal (∑ b ∈ B, ∑ k ∈ Finset.range Kmax,
            multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
              ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => Finset.sum_nonneg fun k _ => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _))]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _))]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [v]
      rw [ENNReal.ofReal_mul (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
        (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))]
    have hvx_ge1 : 1 ≤ multiResolventV S s x := hV_ge1 x hx.1
    have h_S_nn : 0 ≤ ∑ r ∈ S, ∑ k ∈ Finset.range Kmax,
        multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun k _ => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _)
    have h_B_nn : 0 ≤ ∑ b ∈ B, ∑ k ∈ Finset.range Kmax,
        multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
      Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun k _ => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _)
    have htailFin_nn : 0 ≤ tailFin := add_nonneg h_S_nn h_B_nn
    rw [hS_part, hfinS_eq, hfinB_eq, add_assoc, ← ENNReal.ofReal_add h_S_nn h_B_nn]
    change v x ≤ ENNReal.ofReal (multiResolventV S s x - 1) + ENNReal.ofReal tailFin
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hvx_ge1) htailFin_nn]
    exact ENNReal.ofReal_le_ofReal (by linarith [htailFin_ge1])
  have hsub_dim : ENNReal.ofReal s ≤ dimH (cfAlphabetSet (A_fin : Set ℕ)) :=
    le_dimH_of_transferOp_ge hAne ha1 hs_pos
      (by simp : (0 : ℝ≥0∞) < ENNReal.ofReal 1) ENNReal.ofReal_lt_top hv_bd hsuper
  have hset_mono : cfAlphabetSet (A_fin : Set ℕ) ⊆ multiResidueSet m S B := by
    rintro x ⟨hx01, hirr, hadm⟩
    exact ⟨hx01, hirr, fun i => truncMultiAlphabet_subset hm_sep (hadm i)⟩
  exact hsub_dim.trans (dimH_mono hset_mono)

private lemma three_term_alpha_prep {d C c₂ K_α m L : ℝ}
    (hdC1 : 1 ≤ d * C) (hm_pos : 0 < m) (hL2 : 2 ≤ L) (hKα : 0 < K_α)
    (hlk : K_α * (L / m) < 1)
    (hcomb : (d * C) ^ 2 * (L / m) + |c₂| / m + K_α * (L ^ 2 / m ^ 2) < d * C / 2) :
    2 * (d * C) ≤ m ∧
      ∀ α : ℝ, |α - (d * C - (d * C) ^ 2 * L / m + c₂ / m)| ≤ K_α * (L ^ 2 / m ^ 2) →
        d * C / 2 ≤ α ∧ α ≤ 2 * (d * C) ∧
          |d * C - α| ≤ ((d * C) ^ 2 + |c₂| + 1) * (L / m) := by
  have hdC_pos : 0 < d * C := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL_pos : 0 < L := by linarith
  have h2dC_le_m : 2 * (d * C) ≤ m := by
    have h1' : (d * C) ^ 2 * (L / m) < d * C / 2 := by
      have : 0 ≤ |c₂| / m + K_α * (L ^ 2 / m ^ 2) := by positivity
      linarith
    have h2dCm : (d * C) ^ 2 * (2 / m) ≤ (d * C) ^ 2 * (L / m) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hL2 hm_pos.le) (sq_nonneg _)
    have hlt : (d * C) ^ 2 * (2 / m) < d * C / 2 := h2dCm.trans_lt h1'
    have hlt_m : ((d * C) ^ 2 * (2 / m)) * m < (d * C / 2) * m :=
      mul_lt_mul_of_pos_right hlt hm_pos
    have h1'' : ((d * C) ^ 2 * (2 / m)) * m = 2 * (d * C) ^ 2 := by
      field_simp [hm_pos.ne']
    have hlt2 : 4 * (d * C) ^ 2 < (d * C) * m := by linarith
    nlinarith [hdC1]
  refine ⟨h2dC_le_m, fun α hα => ?_⟩
  let δ₂ : ℝ := K_α * (L ^ 2 / m ^ 2)
  let α₀ : ℝ := d * C - (d * C) ^ 2 * L / m + c₂ / m
  have hδ₂_le_log : δ₂ ≤ L / m := by
    have hmul : (K_α * (L / m)) * (L / m) ≤ 1 * (L / m) :=
      mul_le_mul hlk.le le_rfl (div_nonneg hL_pos.le hm_pos.le) zero_le_one
    linarith [show δ₂ = (K_α * (L / m)) * (L / m) by dsimp [δ₂]; ring]
  have hdiff_bd : |d * C - α₀| ≤ (d * C) ^ 2 * (L / m) + |c₂| / m := by
    rw [show d * C - α₀ = (d * C) ^ 2 * (L / m) - c₂ / m by dsimp [α₀]; ring]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (div_nonneg hL_pos.le hm_pos.le)),
      abs_div, abs_of_pos hm_pos]
  have hfull_bd : |d * C - α| ≤ (d * C) ^ 2 * (L / m) + |c₂| / m + δ₂ := by
    rw [show d * C - α = (d * C - α₀) + (α₀ - α) by ring]
    exact (abs_add_le _ _).trans (add_le_add hdiff_bd (by rwa [abs_sub_comm]))
  have hlt_half : |d * C - α| ≤ d * C / 2 := hfull_bd.trans (by dsimp [δ₂]; linarith)
  have h_abs := abs_le.mp hlt_half
  have hlog_inv : 1 / m ≤ L / m := div_le_div_of_nonneg_right hL1 hm_pos.le
  have h_quad_bd : |d * C - α| ≤ ((d * C) ^ 2 + |c₂| + 1) * (L / m) := by
    have hcm_le : |c₂| / m ≤ |c₂| * (L / m) := by
      rw [show |c₂| / m = |c₂| * (1 / m) by ring]
      exact mul_le_mul_of_nonneg_left hlog_inv (abs_nonneg _)
    calc |d * C - α|
        ≤ (d * C) ^ 2 * (L / m) + |c₂| * (L / m) + 1 * (L / m) := by linarith
      _ = ((d * C) ^ 2 + |c₂| + 1) * (L / m) := by ring
  exact ⟨by linarith, by linarith, h_quad_bd⟩

private lemma three_term_tail_upper {d C C' γ E₀ m L T_u : ℝ}
    (hdC_pos : 0 < d * C) (hE₀_pos : 0 < E₀) (hm_pos : 0 < m) (hL_pos : 0 < L)
    (hαu_lo : d * C / 2 ≤ (d * C - (d * C) ^ 2 * L / m + d ^ 2 * C * (γ * C - C') / m) +
      (2 * d * C * (E₀ + 2 * ((d * C) ^ 2 + |d ^ 2 * C * (γ * C - C')| + 1) ^ 2 / (d * C) ^ 2 + 2)) *
        (L ^ 2 / m ^ 2))
    (hαu_diff : |d * C - ((d * C - (d * C) ^ 2 * L / m + d ^ 2 * C * (γ * C - C') / m) +
      (2 * d * C * (E₀ + 2 * ((d * C) ^ 2 + |d ^ 2 * C * (γ * C - C')| + 1) ^ 2 / (d * C) ^ 2 + 2)) *
        (L ^ 2 / m ^ 2))| ≤
      ((d * C) ^ 2 + |d ^ 2 * C * (γ * C - C')| + 1) * (L / m))
    (hexp : |T_u - (d * C / ((d * C - (d * C) ^ 2 * L / m + d ^ 2 * C * (γ * C - C') / m) +
        (2 * d * C * (E₀ + 2 * ((d * C) ^ 2 + |d ^ 2 * C * (γ * C - C')| + 1) ^ 2 / (d * C) ^ 2 + 2)) *
          (L ^ 2 / m ^ 2)) -
        d * C * L / m + d * (γ * C - C') / m)| ≤ E₀ * (L ^ 2 / m ^ 2)) :
    T_u ≤ 1 := by
  let c₂ : ℝ := d ^ 2 * C * (γ * C - C')
  let E_quad : ℝ := 2 * ((d * C) ^ 2 + |c₂| + 1) ^ 2 / (d * C) ^ 2
  let K_α : ℝ := 2 * d * C * (E₀ + E_quad + 2)
  let δ₂ : ℝ := K_α * (L ^ 2 / m ^ 2)
  let α₀ : ℝ := d * C - (d * C) ^ 2 * L / m + c₂ / m
  let α_u : ℝ := α₀ + δ₂
  let gap : ℝ := L ^ 2 / m ^ 2
  have hd_ne : d ≠ 0 := left_ne_zero_of_mul hdC_pos.ne'
  have hC_ne : C ≠ 0 := right_ne_zero_of_mul hdC_pos.ne'
  have hE_quad_nn : 0 ≤ E_quad := by dsimp [E_quad]; positivity
  have hgap_pos : 0 < gap := by dsimp [gap]; positivity
  have hαu_pos : 0 < α_u := by
    change 0 < α₀ + δ₂; linarith [hαu_lo, hdC_pos]
  have h_ident : d * C / α_u - d * C * L / m + d * (γ * C - C') / m =
      1 - (α_u - α₀) / (d * C) + (d * C - α_u) ^ 2 / (α_u * (d * C)) := by
    dsimp only [α₀, c₂]
    field_simp [hαu_pos.ne', hd_ne, hC_ne, hm_pos.ne']
    ring
  have hsq : (d * C - α_u) ^ 2 ≤ ((d * C) ^ 2 + |c₂| + 1) ^ 2 * gap := by
    have h1' := pow_le_pow_left₀ (abs_nonneg _) hαu_diff 2
    rw [sq_abs] at h1'
    exact h1'.trans_eq (by dsimp only [gap]; ring)
  have hden_ge : (d * C) ^ 2 / 2 ≤ α_u * (d * C) := by
    convert mul_le_mul_of_nonneg_right hαu_lo hdC_pos.le using 1; ring
  have h_quad_u : (d * C - α_u) ^ 2 / (α_u * (d * C)) ≤ E_quad * gap :=
    calc (d * C - α_u) ^ 2 / (α_u * (d * C))
        ≤ (((d * C) ^ 2 + |c₂| + 1) ^ 2 * gap) / (α_u * (d * C)) :=
          div_le_div_of_nonneg_right hsq (mul_pos hαu_pos hdC_pos).le
      _ ≤ (((d * C) ^ 2 + |c₂| + 1) ^ 2 * gap) / ((d * C) ^ 2 / 2) :=
          div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) hgap_pos.le)
            (div_pos (sq_pos_of_pos hdC_pos) two_pos) hden_ge
      _ = E_quad * gap := by dsimp only [E_quad]; field_simp [hd_ne, hC_ne] <;> ring
  have h_ub := (abs_le.mp hexp).2
  have h_diff_u : (α_u - α₀) / (d * C) = δ₂ / (d * C) := by dsimp only [α_u]; ring
  have hδ_eq : δ₂ / (d * C) = (2 * (E₀ + E_quad + 2)) * gap := by
    dsimp only [δ₂, gap, K_α]; field_simp [hd_ne, hC_ne] <;> ring
  have h_K_crush : -(δ₂ / (d * C)) + (E_quad + E₀) * gap ≤ 0 := by
    rw [hδ_eq, show -(2 * (E₀ + E_quad + 2) * gap) + (E_quad + E₀) * gap =
        -((E₀ + E_quad + 4) * gap) by ring]
    exact neg_nonpos.mpr (mul_nonneg (by linarith) hgap_pos.le)
  change T_u - (d * C / α_u - d * C * L / m + d * (γ * C - C') / m) ≤ E₀ * gap at h_ub
  linarith

private lemma three_term_tail_lower {d C C' γ E₀ m L T_l : ℝ}
    (hdC_pos : 0 < d * C) (hE₀_pos : 0 < E₀) (hm_pos : 0 < m) (hL_pos : 0 < L)
    (hαl_lo : d * C / 2 ≤ (d * C - (d * C) ^ 2 * L / m + d ^ 2 * C * (γ * C - C') / m) -
      (2 * d * C * (E₀ + 2 * ((d * C) ^ 2 + |d ^ 2 * C * (γ * C - C')| + 1) ^ 2 / (d * C) ^ 2 + 2)) *
        (L ^ 2 / m ^ 2))
    (hexp : |T_l - (d * C / ((d * C - (d * C) ^ 2 * L / m + d ^ 2 * C * (γ * C - C') / m) -
        (2 * d * C * (E₀ + 2 * ((d * C) ^ 2 + |d ^ 2 * C * (γ * C - C')| + 1) ^ 2 / (d * C) ^ 2 + 2)) *
          (L ^ 2 / m ^ 2)) -
        d * C * L / m + d * (γ * C - C') / m)| ≤ E₀ * (L ^ 2 / m ^ 2)) :
    1 + L ^ 2 / m ^ 2 ≤ T_l := by
  let c₂ : ℝ := d ^ 2 * C * (γ * C - C')
  let E_quad : ℝ := 2 * ((d * C) ^ 2 + |c₂| + 1) ^ 2 / (d * C) ^ 2
  let K_α : ℝ := 2 * d * C * (E₀ + E_quad + 2)
  let δ₂ : ℝ := K_α * (L ^ 2 / m ^ 2)
  let α₀ : ℝ := d * C - (d * C) ^ 2 * L / m + c₂ / m
  let α_l : ℝ := α₀ - δ₂
  let gap : ℝ := L ^ 2 / m ^ 2
  have hd_ne : d ≠ 0 := left_ne_zero_of_mul hdC_pos.ne'
  have hC_ne : C ≠ 0 := right_ne_zero_of_mul hdC_pos.ne'
  have hE_quad_nn : 0 ≤ E_quad := by dsimp [E_quad]; positivity
  have hgap_pos : 0 < gap := by dsimp [gap]; positivity
  have hαl_pos : 0 < α_l := by
    change 0 < α₀ - δ₂; linarith [hαl_lo, hdC_pos]
  have h_ident : d * C / α_l - d * C * L / m + d * (γ * C - C') / m =
      1 - (α_l - α₀) / (d * C) + (d * C - α_l) ^ 2 / (α_l * (d * C)) := by
    dsimp only [α₀, c₂]
    field_simp [hαl_pos.ne', hd_ne, hC_ne, hm_pos.ne']
    ring
  have h_lb := (abs_le.mp hexp).1
  have h_diff_l : (α_l - α₀) / (d * C) = -(δ₂ / (d * C)) := by dsimp only [α_l]; ring
  have hquad_nn : 0 ≤ (d * C - α_l) ^ 2 / (α_l * (d * C)) := by positivity
  have hδ_eq : δ₂ / (d * C) = (2 * (E₀ + E_quad + 2)) * gap := by
    dsimp only [δ₂, gap, K_α]; field_simp [hd_ne, hC_ne] <;> ring
  have h_K_win : gap ≤ δ₂ / (d * C) - E₀ * gap := by
    rw [hδ_eq]
    have hdiff_nn : 0 ≤ (E₀ + 2 * E_quad + 3) * gap :=
      mul_nonneg (by linarith) hgap_pos.le
    linarith [hdiff_nn, show gap - (2 * (E₀ + E_quad + 2) * gap - E₀ * gap) =
      -((E₀ + 2 * E_quad + 3) * gap) by ring]
  change -(E₀ * gap) ≤ T_l - (d * C / α_l - d * C * L / m + d * (γ * C - C') / m) at h_lb
  change 1 + gap ≤ T_l
  linarith

private lemma three_term_s_bounds {d C c₂ m L K_α dimR : ℝ}
    (hm_pos : 0 < m)
    (h_hi : dimR ≤ (1 + ((d * C - (d * C) ^ 2 * L / m + c₂ / m) + K_α * (L ^ 2 / m ^ 2)) / m) / 2)
    (h_lo : (1 + ((d * C - (d * C) ^ 2 * L / m + c₂ / m) - K_α * (L ^ 2 / m ^ 2)) / m) / 2 ≤ dimR) :
    |dimR - (1 / 2 + d * C / (2 * m) - (d * C) ^ 2 * L / (2 * m ^ 2) + c₂ / (2 * m ^ 2))| ≤
      (K_α / 2) * (L ^ 2 / m ^ 3) := by
  have h1 : (1 + ((d * C - (d * C) ^ 2 * L / m + c₂ / m) + K_α * (L ^ 2 / m ^ 2)) / m) / 2 =
      (1 / 2 + d * C / (2 * m) - (d * C) ^ 2 * L / (2 * m ^ 2) + c₂ / (2 * m ^ 2)) +
        (K_α / 2) * (L ^ 2 / m ^ 3) := by
    field_simp [hm_pos.ne']; ring
  have h2 : (1 + ((d * C - (d * C) ^ 2 * L / m + c₂ / m) - K_α * (L ^ 2 / m ^ 2)) / m) / 2 =
      (1 / 2 + d * C / (2 * m) - (d * C) ^ 2 * L / (2 * m ^ 2) + c₂ / (2 * m ^ 2)) -
        (K_α / 2) * (L ^ 2 / m ^ 3) := by
    field_simp [hm_pos.ne']; ring
  rw [abs_le]
  constructor <;> linarith

/-- **Master Three-Term Subcritical Multi-Residue Asymptotic**:
    whenever `∑_{w} q(w)^{-1} < ∞` (i.e., `poincareAbscissa S < 1 / 2` or `S = ∅`),
    putting `d = #S + #B ≥ 1`, `C = multiC S 1`, `C' = multiCLog S`, and
    `γ = Real.eulerMascheroniConstant`:
    `dimH (multiResidueSet m S B) = 1/2 + d*C/(2m) - (d*C)^2*(log m)/(2m^2) + d^2*C*(γ*C - C')/(2m^2) + O((log m)^2/m^3)`. -/
theorem dimH_multiResidueSet_asymp_three_term {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hd : 1 ≤ S.card + B.card)
    (hsum : Summable (wordSum S 1)) :
    ∃ K > 0, ∀ᶠ m : ℕ in atTop,
      |(dimH (multiResidueSet m S B)).toReal -
        (1 / 2 +
          ((S.card + B.card : ℝ) * multiC S 1) / (2 * (m : ℝ)) -
          ((S.card + B.card : ℝ) * multiC S 1) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) +
          ((S.card + B.card : ℝ) ^ 2 * multiC S 1 *
            (Real.eulerMascheroniConstant * multiC S 1 - multiCLog S)) /
            (2 * (m : ℝ) ^ 2))| ≤
        K * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 3) := by
  let d : ℝ := (S.card + B.card : ℝ)
  let C : ℝ := multiC S 1
  let C' : ℝ := multiCLog S
  let γ : ℝ := Real.eulerMascheroniConstant
  let c₂ : ℝ := d ^ 2 * C * (γ * C - C')
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast hd
  have hC1 : 1 ≤ C := one_le_multiC hsum
  have hdC1 : 1 ≤ d * C := one_le_mul_of_one_le_of_one_le hd1 hC1
  have hdC_pos : 0 < d * C := by linarith only [hdC1]
  obtain ⟨E₀, hE₀_pos, m₁, hm₁_ge2, htail_exp⟩ := subcritical_tail_expansion hS1 hd hsum
  let E_quad : ℝ := 2 * ((d * C) ^ 2 + |c₂| + 1) ^ 2 / (d * C) ^ 2
  have hE_quad_nn : 0 ≤ E_quad := by dsimp [E_quad]; positivity
  let K_α : ℝ := 2 * d * C * (E₀ + E_quad + 2)
  have hKα_pos : 0 < K_α := by dsimp [K_α]; positivity
  let K : ℝ := K_α / 2
  have hK_pos : 0 < K := by dsimp [K]; linarith only [hKα_pos]
  refine ⟨K, hK_pos, ?_⟩
  let M₀ : ℝ := ((S.sup id + B.sup id + 1 : ℕ) : ℝ)
  have ht_log_div : Tendsto (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ)) atTop (nhds 0) :=
    tendsto_log_div_nat_local
  have ht_logK : Tendsto (fun m : ℕ => K_α * (Real.log (m : ℝ) / (m : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using ht_log_div.const_mul K_α
  have ht_comb : Tendsto (fun m : ℕ =>
      (d * C) ^ 2 * (Real.log (m : ℝ) / (m : ℝ)) + |c₂| / (m : ℝ) +
        K_α * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2)) atTop (nhds 0) := by
    have t1 := ht_log_div.const_mul ((d * C) ^ 2)
    have t2 := (tendsto_const_nhds (x := |c₂|)).div_atTop tendsto_natCast_atTop_atTop
    have t3 : Tendsto (fun m : ℕ => K_α * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2)) atTop (nhds 0) := by
      have ht_sq_div : Tendsto (fun m : ℕ => (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) atTop (nhds 0) := by
        have : (fun m : ℕ => (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) =
            (fun m : ℕ => ((Real.log (m : ℝ)) ^ 2 / (m : ℝ)) * (1 / (m : ℝ))) := by
          funext m; ring
        rw [this]
        simpa only [mul_zero] using tendsto_log_sq_div_nat_local.mul
          (tendsto_const_nhds (x := (1 : ℝ)).div_atTop tendsto_natCast_atTop_atTop)
      simpa only [mul_zero] using ht_sq_div.const_mul K_α
    simpa only [add_zero, mul_zero] using (t1.add t2).add t3
  filter_upwards [eventually_ge_atTop (max m₁ (Nat.ceil (Real.exp 2) + 2 * (S.sup id + B.sup id + 1) + 4)),
    ht_logK.eventually (gt_mem_nhds (one_pos : (0 : ℝ) < 1)),
    ht_comb.eventually (gt_mem_nhds (show (0 : ℝ) < d * C / 2 by linarith only [hdC_pos]))]
    with m hm hlk hcomb
  have hm_m1 : m₁ ≤ m := le_trans (le_max_left _ _) hm
  have hm_big : Nat.ceil (Real.exp 2) + 2 * (S.sup id + B.sup id + 1) + 4 ≤ m :=
    le_trans (le_max_right _ _) hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm_sep : S.sup id + B.sup id + 1 ≤ m := by omega
  have hm_2M0 : 2 * M₀ ≤ (m : ℝ) := by
    dsimp [M₀]; exact_mod_cast (by omega : 2 * (S.sup id + B.sup id + 1) ≤ m)
  have hexp2_le : Real.exp 2 ≤ (m : ℝ) :=
    (Nat.le_ceil (Real.exp 2)).trans (by exact_mod_cast (by omega : Nat.ceil (Real.exp 2) ≤ m))
  have hlog_ge2 : 2 ≤ Real.log (m : ℝ) := by
    have := Real.log_le_log (Real.exp_pos 2) hexp2_le
    rwa [Real.log_exp] at this
  have hlog_pos : 0 < Real.log (m : ℝ) := by linarith only [hlog_ge2]
  obtain ⟨h2dC_le_m, hα_range⟩ :=
    three_term_alpha_prep hdC1 hm_pos hlog_ge2 hKα_pos hlk hcomb
  let δ₂ : ℝ := K_α * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2)
  have hδ₂_pos : 0 < δ₂ := by dsimp [δ₂]; positivity
  let α₀ : ℝ := d * C - (d * C) ^ 2 * Real.log (m : ℝ) / (m : ℝ) + c₂ / (m : ℝ)
  let α_u : ℝ := α₀ + δ₂
  let α_l : ℝ := α₀ - δ₂
  have hαu_prop := hα_range α_u (by dsimp only [α_u]; rw [add_sub_cancel_left, abs_of_pos hδ₂_pos])
  have hαl_prop := hα_range α_l (by
    dsimp only [α_l]; rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ₂_pos])
  let s_u : ℝ := (1 + α_u / (m : ℝ)) / 2
  let s_l : ℝ := (1 + α_l / (m : ℝ)) / 2
  have hαu_pos : 0 < α_u := by linarith only [hαu_prop.1, hdC_pos]
  have hαl_pos : 0 < α_l := by linarith only [hαl_prop.1, hdC_pos]
  have hsu_lo : 1 / 2 < s_u := by dsimp only [s_u]; linarith only [div_pos hαu_pos hm_pos]
  have hsl_lo : 1 / 2 < s_l := by dsimp only [s_l]; linarith only [div_pos hαl_pos hm_pos]
  have hsu_hi : s_u ≤ 1 := by
    have h1m : α_u / (m : ℝ) ≤ 1 :=
      (div_le_one hm_pos).mpr (by linarith only [hαu_prop.2.1, h2dC_le_m])
    dsimp only [s_u]; linarith only [h1m]
  have hsl_hi : s_l ≤ 1 := by
    have h1m : α_l / (m : ℝ) ≤ 1 :=
      (div_le_one hm_pos).mpr (by linarith only [hαl_prop.2.1, h2dC_le_m])
    dsimp only [s_l]; linarith only [h1m]
  have htail_u : ∀ x ∈ Set.Icc (0 : ℝ) 1, multiResidueTailReal m S B s_u x ≤ 1 := fun x hx =>
    three_term_tail_upper hdC_pos hE₀_pos hm_pos hlog_pos hαu_prop.1 hαu_prop.2.2
      (htail_exp m hm_m1 α_u x hαu_prop.1 hαu_prop.2.1 hx)
  have htail_l : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      1 + (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 ≤ multiResidueTailReal m S B s_l x := fun x hx =>
    three_term_tail_lower hdC_pos hE₀_pos hm_pos hlog_pos hαl_prop.1
      (htail_exp m hm_m1 α_l x hαl_prop.1 hαl_prop.2.1 hx)
  have hgap_pos : 0 < (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by positivity
  have h_up := dimH_multiResidue_upper_of_tail_le hS1 hm_sep hm_2M0 hsu_lo hsu_hi hsum htail_u
  have h_lo := dimH_multiResidue_lower_of_tail_ge hS1 hd hm_sep hm_2M0 hsl_lo hsl_hi hgap_pos hsum htail_l
  have hne_top : dimH (multiResidueSet m S B) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_up
  have h_toReal_le : (dimH (multiResidueSet m S B)).toReal ≤ s_u :=
    ENNReal.toReal_le_of_le_ofReal (by linarith only [hsu_lo]) h_up
  have h_le_toReal : s_l ≤ (dimH (multiResidueSet m S B)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hne_top).mp h_lo
  exact three_term_s_bounds hm_pos h_toReal_le h_le_toReal

/-- Exact `m^2` Euler–Mascheroni third-order limit for subcritical multi-residue sets. -/
theorem tendsto_m2_residual_multiResidue {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hd : 1 ≤ S.card + B.card)
    (hsum : Summable (wordSum S 1)) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 *
        ((dimH (multiResidueSet m S B)).toReal -
          (1 / 2 + ((S.card + B.card : ℝ) * multiC S 1) / (2 * (m : ℝ)) -
            ((S.card + B.card : ℝ) * multiC S 1) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2))))
      atTop
      (nhds (((S.card + B.card : ℝ) ^ 2 * multiC S 1 *
        (Real.eulerMascheroniConstant * multiC S 1 - multiCLog S)) / 2)) := by
  let c₂ : ℝ := (S.card + B.card : ℝ) ^ 2 * multiC S 1 *
    (Real.eulerMascheroniConstant * multiC S 1 - multiCLog S)
  obtain ⟨K, _, h_ev⟩ := dimH_multiResidueSet_asymp_three_term hS1 hd hsum
  have h_err : Tendsto (fun m : ℕ => K * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ))) atTop (nhds 0) := by
    simpa using tendsto_log_sq_div_nat_local.const_mul K
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using (tendsto_const_nhds (x := c₂ / 2)).sub h_err)
    (by simpa using (tendsto_const_nhds (x := c₂ / 2)).add h_err) ?_ ?_
  · filter_upwards [h_ev, eventually_ge_atTop 1] with m hm hm1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have h_abs := abs_le.mp hm
    have hmul := mul_le_mul_of_nonneg_left h_abs.1 (sq_nonneg (m : ℝ))
    have heq : (m : ℝ) ^ 2 * (-(K * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 3)) +
        (1 / 2 + ((S.card + B.card : ℝ) * multiC S 1) / (2 * (m : ℝ)) -
          ((S.card + B.card : ℝ) * multiC S 1) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) +
          c₂ / (2 * (m : ℝ) ^ 2) -
          (1 / 2 + ((S.card + B.card : ℝ) * multiC S 1) / (2 * (m : ℝ)) -
            ((S.card + B.card : ℝ) * multiC S 1) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2)))) =
        c₂ / 2 - K * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ)) := by
      field_simp [hm_pos.ne']; ring
    linarith
  · filter_upwards [h_ev, eventually_ge_atTop 1] with m hm hm1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have h_abs := abs_le.mp hm
    have hmul := mul_le_mul_of_nonneg_left h_abs.2 (sq_nonneg (m : ℝ))
    have heq : (m : ℝ) ^ 2 * (K * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 3) +
        (1 / 2 + ((S.card + B.card : ℝ) * multiC S 1) / (2 * (m : ℝ)) -
          ((S.card + B.card : ℝ) * multiC S 1) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) +
          c₂ / (2 * (m : ℝ) ^ 2) -
          (1 / 2 + ((S.card + B.card : ℝ) * multiC S 1) / (2 * (m : ℝ)) -
            ((S.card + B.card : ℝ) * multiC S 1) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2)))) =
        c₂ / 2 + K * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ)) := by
      field_simp [hm_pos.ne']; ring
    linarith

lemma tendsto_mul_dimH_multiResidue_sub_half {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hd : 1 ≤ S.card + B.card)
    (hsum : Summable (wordSum S 1)) :
    Tendsto (fun m : ℕ => (m : ℝ) * ((dimH (multiResidueSet m S B)).toReal - 1 / 2))
      atTop (nhds (((S.card + B.card : ℝ) * multiC S 1) / 2)) := by
  let d : ℝ := (S.card + B.card : ℝ)
  let C : ℝ := multiC S 1
  let c₂ : ℝ := d ^ 2 * C * (Real.eulerMascheroniConstant * C - multiCLog S)
  have h2 := tendsto_m2_residual_multiResidue hS1 hd hsum
  have hinv : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun m : ℕ =>
      (m : ℝ) ^ 2 * ((dimH (multiResidueSet m S B)).toReal -
        (1 / 2 + d * C / (2 * (m : ℝ)) -
          (d * C) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2))) * (1 / (m : ℝ)))
      atTop (nhds ((c₂ / 2) * 0)) := h2.mul hinv
  have hlog : Tendsto (fun m : ℕ =>
      ((d * C) ^ 2 / 2) * (Real.log (m : ℝ) / (m : ℝ))) atTop (nhds 0) := by
    simpa using tendsto_log_div_nat_local.const_mul ((d * C) ^ 2 / 2)
  have htot : Tendsto (fun m : ℕ =>
      (m : ℝ) ^ 2 * ((dimH (multiResidueSet m S B)).toReal -
        (1 / 2 + d * C / (2 * (m : ℝ)) -
          (d * C) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2))) * (1 / (m : ℝ)) +
        (d * C / 2 - ((d * C) ^ 2 / 2) * (Real.log (m : ℝ) / (m : ℝ))))
      atTop (nhds ((c₂ / 2) * 0 + (d * C / 2 - 0))) :=
    h1.add (tendsto_const_nhds.sub hlog)
  simp only [mul_zero, sub_zero, zero_add] at htot
  refine htot.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm1
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  dsimp only [d, C]
  field_simp [hm_ne]
  ring

/-- Exact first-order dimension-excess ratio for subcritical multi-residue sets. -/
theorem tendsto_dimH_multiResidue_ratio {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hd : 1 ≤ S.card + B.card)
    (hsum : Summable (wordSum S 1)) :
    Tendsto (fun m : ℕ =>
        ((dimH (multiResidueSet m S B)).toReal - 1 / 2) /
          ((dimH (residueConstSet m m)).toReal - 1 / 2))
      atTop (nhds ((S.card + B.card : ℝ) * multiC S 1)) := by
  have hnum := tendsto_mul_dimH_multiResidue_sub_half hS1 hd hsum
  have hden := tendsto_mul_dimH_residueConstSet_mm_sub_half
  have hdiv : Tendsto (fun m : ℕ =>
      ((m : ℝ) * ((dimH (multiResidueSet m S B)).toReal - 1 / 2)) /
        ((m : ℝ) * ((dimH (residueConstSet m m)).toReal - 1 / 2)))
      atTop (nhds ((((S.card + B.card : ℝ) * multiC S 1) / 2) / (1 / 2))) :=
    hnum.div hden (by norm_num)
  rw [show (((S.card + B.card : ℝ) * multiC S 1) / 2) / (1 / 2) =
      (S.card + B.card : ℝ) * multiC S 1 by ring] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm1
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp [hm_ne]

lemma denQ_replicate_eq_metalQ (r n : ℕ) :
    denQ (List.replicate n r) = (metalQ r n : ℝ) ∧
      denP (List.replicate n r) = (metalQPrev r n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [denQ_nil, denP_nil]
    | 1 =>
      have hrp : List.replicate 1 r = ([] : List ℕ) ++ [r] := rfl
      rw [hrp, denQ_snoc, denP_snoc, denQ_nil, denP_nil]
      simp
    | k + 2 =>
      have hconcat : List.replicate (k + 2) r = List.replicate (k + 1) r ++ [r] := by
        rw [← List.replicate_succ']
      rw [hconcat, denQ_snoc, denP_snoc, (ih (k + 1) (by omega)).1, (ih (k + 1) (by omega)).2]
      rw [metalQPrev_succ, metalQ_succ_succ]
      push_cast
      exact ⟨rfl, rfl⟩

/-- First logarithmic moment of the metallic-mean continuant sequence `q_n(r)`. -/
def metalCLog (r : ℕ) : ℝ :=
  ∑' n : ℕ, Real.log (metalQ r n : ℝ) / (metalQ r n : ℝ)

private lemma subWord_singleton_eq_replicate {r n : ℕ} (w : Fin n → {a : ℕ // a ∈ ({r} : Finset ℕ)}) :
    subWord (A := (({r} : Finset ℕ) : Set ℕ)) n w = List.replicate n r := by
  refine List.ext_getElem (by simp [subWord]) fun i hi1 hi2 => ?_
  simp only [subWord, List.getElem_ofFn, List.getElem_replicate]
  exact Finset.mem_singleton.mp (w ⟨i, by simp [subWord] at hi1; exact hi1⟩).2

lemma wordSum_singleton_eq (r : ℕ) (p : ℝ) (n : ℕ) :
    wordSum ({r} : Finset ℕ) p n = (metalQ r n : ℝ) ^ (-p) := by
  unfold wordSum
  letI : Unique (Fin n → {a : ℕ // a ∈ ({r} : Finset ℕ)}) :=
    { default := fun _ => ⟨r, Finset.mem_singleton_self r⟩
      uniq := fun f => funext fun i => Subtype.ext (Finset.mem_singleton.mp (f i).2) }
  rw [Fintype.sum_unique, subWord_singleton_eq_replicate, (denQ_replicate_eq_metalQ r n).1]

lemma summable_wordSum_singleton {r : ℕ} (hr : 1 ≤ r) :
    Summable (wordSum ({r} : Finset ℕ) 1) :=
  (summable_metalQ_rpow hr zero_lt_one).congr fun n => (wordSum_singleton_eq r 1 n).symm

lemma multiC_singleton_eq_metalC (r : ℕ) (p : ℝ) :
    multiC ({r} : Finset ℕ) p = metalC r p := by
  unfold multiC metalC
  exact tsum_congr (wordSum_singleton_eq r p)

lemma multiCLog_singleton_eq (r : ℕ) :
    multiCLog ({r} : Finset ℕ) = metalCLog r := by
  unfold multiCLog wordLogSum metalCLog
  refine tsum_congr fun n => ?_
  letI : Unique (Fin n → {a : ℕ // a ∈ ({r} : Finset ℕ)}) :=
    { default := fun _ => ⟨r, Finset.mem_singleton_self r⟩
      uniq := fun f => funext fun i => Subtype.ext (Finset.mem_singleton.mp (f i).2) }
  rw [Fintype.sum_unique, subWord_singleton_eq_replicate, (denQ_replicate_eq_metalQ r n).1]

lemma multiC_empty (p : ℝ) : multiC (∅ : Finset ℕ) p = 1 := by
  unfold multiC
  have h : (∑' n : ℕ, wordSum (∅ : Finset ℕ) p n) = wordSum (∅ : Finset ℕ) p 0 := by
    refine tsum_eq_single 0 fun n hn => ?_
    exact wordSum_empty (by omega)
  rw [h, wordSum_zero]

lemma multiCLog_empty : multiCLog (∅ : Finset ℕ) = 0 := by
  have h0 : wordLogSum (∅ : Finset ℕ) = fun _ => 0 := by
    funext n
    cases n with
    | zero => exact wordLogSum_zero ∅
    | succ k =>
      unfold wordLogSum
      have hmt : IsEmpty (Fin (k + 1) → {a : ℕ // a ∈ (∅ : Finset ℕ)}) :=
        ⟨fun f => Finset.notMem_empty _ (f ⟨0, Nat.succ_pos k⟩).2⟩
      letI := hmt
      simp
  unfold multiCLog
  rw [h0, tsum_zero]

/-- Sharp three-term Euler–Mascheroni asymptotic for single positive residue `F_{m,r}` (`r ≥ 1`). -/
theorem dimH_residueConstSet_asymp_three_term (r : ℕ) (hr : 1 ≤ r) :
    ∃ K > 0, ∀ᶠ m : ℕ in atTop,
      |(dimH (residueConstSet m r)).toReal -
        (1 / 2 + metalC r 1 / (2 * (m : ℝ)) -
          (metalC r 1) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) +
          metalC r 1 * (Real.eulerMascheroniConstant * metalC r 1 - metalCLog r) /
            (2 * (m : ℝ) ^ 2))| ≤
        K * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 3) := by
  have hS1 : ∀ a ∈ ({r} : Finset ℕ), 1 ≤ a := by
    intro a ha; rw [Finset.mem_singleton] at ha; omega
  have hd : 1 ≤ ({r} : Finset ℕ).card + (∅ : Finset ℕ).card := by simp
  have hsum := summable_wordSum_singleton hr
  obtain ⟨K, hK, h_ev⟩ := dimH_multiResidueSet_asymp_three_term hS1 hd hsum
  refine ⟨K, hK, ?_⟩
  filter_upwards [h_ev] with m hm
  simpa [multiResidueSet_singleton_eq, multiC_singleton_eq_metalC, multiCLog_singleton_eq] using hm

/-- Sharp three-term Euler–Mascheroni asymptotic for `F_{m,m}` (`γ / (2 m^2)` third term). -/
theorem dimH_residueConstSet_mm_asymp_three_term :
    ∃ K > 0, ∀ᶠ m : ℕ in atTop,
      |(dimH (residueConstSet m m)).toReal -
        (1 / 2 + 1 / (2 * (m : ℝ)) - Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) +
          Real.eulerMascheroniConstant / (2 * (m : ℝ) ^ 2))| ≤
        K * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 3) := by
  have hS1 : ∀ a ∈ (∅ : Finset ℕ), 1 ≤ a := fun a ha => by simp at ha
  have hd : 1 ≤ (∅ : Finset ℕ).card + ({0} : Finset ℕ).card := by simp
  have hsum : Summable (wordSum (∅ : Finset ℕ) 1) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by
      simp only [Finset.mem_singleton] at hn
      exact wordSum_empty (by omega)
  obtain ⟨K, hK, h_ev⟩ := dimH_multiResidueSet_asymp_three_term hS1 hd hsum
  refine ⟨K, hK, ?_⟩
  filter_upwards [h_ev, eventually_ge_atTop 1] with m hm hm1
  rw [← multiResidueSet_empty_zero_eq hm1]
  simpa [multiC_empty, multiCLog_empty] using hm

/-- Concrete subcritical three-term asymptotic for the two-digit alphabet `S = {2, 3}, B = ∅`. -/
theorem dimH_multiResidueSet_two_three_asymp :
    ∃ K > 0, ∀ᶠ m : ℕ in atTop,
      |(dimH (multiResidueSet m ({2, 3} : Finset ℕ) ∅)).toReal -
        (1 / 2 +
          (2 * multiC ({2, 3} : Finset ℕ) 1) / (2 * (m : ℝ)) -
          (2 * multiC ({2, 3} : Finset ℕ) 1) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) +
          (4 * multiC ({2, 3} : Finset ℕ) 1 *
            (Real.eulerMascheroniConstant * multiC ({2, 3} : Finset ℕ) 1 -
              multiCLog ({2, 3} : Finset ℕ))) /
            (2 * (m : ℝ) ^ 2))| ≤
        K * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 3) := by
  have hS1 : ∀ a ∈ ({2, 3} : Finset ℕ), 1 ≤ a := by decide
  have hd : 1 ≤ ({2, 3} : Finset ℕ).card + (∅ : Finset ℕ).card := by decide
  obtain ⟨K, hK, h_ev⟩ :=
    dimH_multiResidueSet_asymp_three_term hS1 hd subcritical_pair_two_three.1
  refine ⟨K, hK, ?_⟩
  filter_upwards [h_ev] with m hm
  have hcard : (({2, 3} : Finset ℕ).card + (∅ : Finset ℕ).card : ℝ) = 2 := by norm_num
  have h22 : (2 : ℝ) ^ 2 = 4 := by norm_num
  simpa [hcard, h22] using hm

/-! ### Part 6: Supercritical Power-Law Convergence Rate `Θ(m ^ (-2 s₀))` -/

private lemma one_half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have hexp_sq : (Real.exp (1 / 2)) ^ 2 < (2 : ℝ) ^ 2 := by
    rw [sq, ← Real.exp_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp_pos : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have hexp_lt2 : Real.exp (1 / 2) < 2 := by nlinarith
  exact ((Real.lt_log_iff_exp_lt two_pos).mpr hexp_lt2).le

private lemma log_two_le_one : Real.log 2 ≤ 1 :=
  ((Real.log_lt_iff_lt_exp two_pos).mpr Real.exp_one_gt_two).le

private lemma poincareAbscissa_lt_half_imp_nonempty {S : Finset ℕ}
    (hsuper : (1 / 2 : ℝ) < poincareAbscissa S) : S.Nonempty := by
  by_contra hmt
  rw [Finset.not_nonempty_iff_eq_empty] at hmt
  subst hmt
  have hsum_mt : Summable (wordSum (∅ : Finset ℕ) (2 * (1 / 4 : ℝ))) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by
      simp only [Finset.mem_singleton] at hn
      exact wordSum_empty (by omega)
  have hle : poincareAbscissa (∅ : Finset ℕ) ≤ 1 / 4 :=
    csInf_le ⟨0, fun s hs => hs.1.le⟩ ⟨by norm_num, hsum_mt⟩
  linarith

/-- Quantitative supercritical partition-sum bound near the Poincaré abscissa:
    `multiC S (2 * (poincareAbscissa S + δ)) ≤ 32 / δ` for all `0 < δ ≤ 1`. -/
theorem multiC_supercritical_le {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    multiC S (2 * (poincareAbscissa S + δ)) ≤ 32 / δ := by
  let s₀ : ℝ := poincareAbscissa S
  have hs₀_nn : 0 ≤ s₀ := poincareAbscissa_nonneg S
  have hs₀_le1 : s₀ ≤ 1 := poincareAbscissa_le_one hS1
  let ρ : ℝ := (2 : ℝ) ^ (-δ)
  have hρ_nn : 0 ≤ ρ := Real.rpow_nonneg zero_le_two _
  have hρ_eq : ρ = Real.exp (-(δ * Real.log 2)) := by
    dsimp only [ρ]
    rw [Real.rpow_def_of_pos two_pos]
    congr 1
    ring
  let t : ℝ := δ * Real.log 2
  have hlog2_lo := one_half_le_log_two
  have hlog2_hi := log_two_le_one
  have ht_nn : 0 ≤ t := mul_nonneg hδ0.le (by linarith)
  have ht_lo : δ / 2 ≤ t := by dsimp [t]; nlinarith [hδ0, hlog2_lo]
  have ht_hi : t ≤ 1 := by dsimp [t]; nlinarith [hδ0, hδ1, hlog2_hi]
  have hρ_ub : ρ ≤ 1 - δ / 4 := by
    rw [hρ_eq]
    have hexp_bd : Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := (exp_neg_bounds ht_nn).2
    have ht_sq : t ^ 2 ≤ t := by nlinarith [ht_nn, ht_hi]
    change Real.exp (-t) ≤ 1 - δ / 4
    linarith
  have hρ_lt1 : ρ < 1 := by linarith
  have hpt : ∀ n : ℕ, wordSum S (2 * (s₀ + δ)) n ≤ 8 * ρ ^ n := fun n => by
    have hw_terms : wordSum S (2 * (s₀ + δ)) n ≤ wordSum S (2 * s₀) n * (2 * ρ ^ n) := by
      unfold wordSum
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun w _ => ?_
      have hpd := posDigits_subWord (fun a ha => hS1 a ha) n w
      have hq_pos : 0 < denQ (subWord n w) := denQ_pos hpd
      have hq_pow : (2 : ℝ) ^ (n / 2) ≤ denQ (subWord n w) := by
        simpa [subWord_length] using denQ_pow_two_le hpd
      have h_exp_le : ((n : ℝ) - 1) / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
        have hnat : n ≤ 2 * (n / 2) + 1 := by omega
        have hR : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
        linarith
      have hq_lo : (2 : ℝ) ^ (((n : ℝ) - 1) / 2) ≤ denQ (subWord n w) :=
        calc (2 : ℝ) ^ (((n : ℝ) - 1) / 2)
            ≤ (2 : ℝ) ^ ((n / 2 : ℕ) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h_exp_le
          _ = (2 : ℝ) ^ (n / 2) := Real.rpow_natCast 2 (n / 2)
          _ ≤ denQ (subWord n w) := hq_pow
      have hq_neg2δ : denQ (subWord n w) ^ (-(2 * δ)) ≤ 2 * ρ ^ n := by
        have h1 := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos two_pos _) hq_lo
          (by linarith : -(2 * δ) ≤ 0)
        have h_alg : ((2 : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ (-(2 * δ)) = (2 : ℝ) ^ δ * ρ ^ n := by
          rw [← Real.rpow_mul zero_le_two,
            show (((n : ℝ) - 1) / 2) * (-(2 * δ)) = δ + (-δ) * (n : ℝ) by ring,
            Real.rpow_add two_pos, Real.rpow_mul zero_le_two, Real.rpow_natCast]
        have h2δ : (2 : ℝ) ^ δ ≤ 2 := by
          calc (2 : ℝ) ^ δ ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hδ1
            _ = 2 := Real.rpow_one 2
        calc denQ (subWord n w) ^ (-(2 * δ))
            ≤ (2 : ℝ) ^ δ * ρ ^ n := h_alg ▸ h1
          _ ≤ 2 * ρ ^ n := mul_le_mul_of_nonneg_right h2δ (pow_nonneg hρ_nn n)
      have hsplit : denQ (subWord n w) ^ (-(2 * (s₀ + δ))) =
          denQ (subWord n w) ^ (-(2 * s₀)) * denQ (subWord n w) ^ (-(2 * δ)) := by
        rw [show -(2 * (s₀ + δ)) = -(2 * s₀) + -(2 * δ) by ring, Real.rpow_add hq_pos]
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hq_neg2δ
        (Real.rpow_nonneg hq_pos.le _)
    have hw_s0 : wordSum S (2 * s₀) n ≤ 4 := by
      have h1 := wordSum_poincareAbscissa_le hS1 n
      have h2 : (2 : ℝ) ^ (2 * s₀) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
      norm_num at h2
      exact h1.trans h2
    calc wordSum S (2 * (s₀ + δ)) n
        ≤ wordSum S (2 * s₀) n * (2 * ρ ^ n) := hw_terms
      _ ≤ 4 * (2 * ρ ^ n) := mul_le_mul_of_nonneg_right hw_s0 (by positivity)
      _ = 8 * ρ ^ n := by ring
  have hmaj_sum : Summable (fun n : ℕ => 8 * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ_nn hρ_lt1).mul_left 8
  have hsum_s : Summable (wordSum S (2 * (s₀ + δ))) :=
    Summable.of_nonneg_of_le (wordSum_nonneg S _) hpt hmaj_sum
  have h_inv_le : (1 - ρ)⁻¹ ≤ 4 / δ := by
    rw [← one_div, show (4 : ℝ) / δ = 1 / (δ / 4) by ring]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  calc multiC S (2 * (s₀ + δ))
      ≤ ∑' n : ℕ, 8 * ρ ^ n := hsum_s.tsum_le_tsum hpt hmaj_sum
    _ = 8 * (1 - ρ)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hρ_nn hρ_lt1]
    _ ≤ 8 * (4 / δ) := mul_le_mul_of_nonneg_left h_inv_le (by positivity)
    _ = 32 / δ := by ring

private lemma dimH_multiResidue_upper_of_tail_le_s {m : ℕ} {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hm_sep : S.sup id + B.sup id + 1 ≤ m)
    (hm_2M0 : 2 * ((S.sup id + B.sup id + 1 : ℕ) : ℝ) ≤ (m : ℝ))
    {s : ℝ} (hs_lo : 1 / 2 < s) (hsum_s : Summable (wordSum S (2 * s)))
    (htail : ∀ x ∈ Set.Icc (0 : ℝ) 1, multiResidueTailReal m S B s x ≤ 1) :
    dimH (multiResidueSet m S B) ≤ ENNReal.ofReal s := by
  let M₀ : ℝ := ((S.sup id + B.sup id + 1 : ℕ) : ℝ)
  have hM₀1 : 1 ≤ M₀ := by dsimp [M₀]; exact_mod_cast (by omega : 1 ≤ S.sup id + B.sup id + 1)
  have hs_pos : 0 < s := by linarith
  let C : ℝ := multiC S (2 * s)
  have hC1 : 1 ≤ C := one_le_multiC hsum_s
  have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by dsimp only [M₀] at hM₀1; linarith only [hm_2M0, hM₀1]
  have hV_ge1 : ∀ y : ℝ, 0 ≤ y → 1 ≤ multiResolventV S s y :=
    fun y hy => one_le_multiResolventV hS1 hs_pos hy hsum_s
  have hV_leC : ∀ y : ℝ, 0 ≤ y → multiResolventV S s y ≤ C :=
    fun y hy => multiResolventV_le_multiC hS1 hs_pos hy hsum_s
  let v : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (multiResolventV S s x)
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal 1 ≤ v x ∧ v x ≤ ENNReal.ofReal C := fun x hx =>
    ⟨ENNReal.ofReal_le_ofReal (hV_ge1 x hx.1), ENNReal.ofReal_le_ofReal (hV_leC x hx.1)⟩
  have hterm_sum : ∀ δ : ℝ, |δ| ≤ M₀ →
      Summable fun k : ℕ =>
        multiResolventV S s (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ)) *
          ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ) ^ (-(2 * s))) := fun δ hδ => by
    have hζ : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-(2 * s)))) := by
      have h := (summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 2 * s))
      refine h.congr fun k => ?_
      rw [Real.rpow_neg (Nat.cast_nonneg _)]
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      (hζ.mul_left (C * ((m : ℝ) / 2) ^ (-(2 * s))))
    · have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      have h_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ := by
        have := (abs_le.mp hδ).1; nlinarith [hk1, hm_2M0, hM₀1]
      exact mul_nonneg (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one h_pos.le)))
        (Real.rpow_nonneg h_pos.le _)
    · have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      have hk_ge : (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 ≤ ((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ := by
        have := (abs_le.mp hδ).1; nlinarith [hk1, hm_2M0]
      have h_half_pos : 0 < (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 := by nlinarith [hk1, hm_ge2]
      have h_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ := by linarith only [h_half_pos, hk_ge]
      have hV_le := hV_leC (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + δ)) (div_nonneg zero_le_one h_pos.le)
      have hpow := Real.rpow_le_rpow_of_nonpos (z := -(2 * s)) h_half_pos hk_ge
        (by linarith only [hs_pos])
      have hsplit : ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(2 * s)) =
          ((m : ℝ) / 2) ^ (-(2 * s)) * (((k + 1 : ℕ) : ℝ) ^ (-(2 * s))) := by
        rw [show (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 = ((m : ℝ) / 2) * ((k + 1 : ℕ) : ℝ) by ring,
          Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
      calc _ ≤ C * ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(2 * s)) :=
            mul_le_mul hV_le hpow (Real.rpow_nonneg h_pos.le _) (zero_le_one.trans hC1)
        _ = _ := by rw [hsplit]; ring
  have hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      transferOp (multiResidueAlphabet m S B) s v x ≤ v x := by
    intro x hx
    rw [transferOp_multiResidueAlphabet_eq hS1 hm_sep s v x]
    have hS_part : transferOp (S : Set ℕ) s v x = ENNReal.ofReal (multiResolventV S s x - 1) := by
      rw [transferOp_finset_eq]
      have hbr := multiResolventV_branch_eq hS1 hs_pos hx.1 hsum_s
      have hnonneg : ∀ a ∈ S, 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) *
          multiResolventV S s (1 / ((a : ℝ) + x)) := fun a _ =>
        mul_nonneg (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]) _)
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]))))
      calc (∑ a ∈ S, v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))))
          = ∑ a ∈ S, ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)) *
              multiResolventV S s (1 / ((a : ℝ) + x))) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              have ha_nn : 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) :=
                Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]) _
              dsimp only [v]; rw [mul_comm, ← ENNReal.ofReal_mul ha_nn]
        _ = ENNReal.ofReal (∑ a ∈ S, ((a : ℝ) + x) ^ (-(2 * s)) *
              multiResolventV S s (1 / ((a : ℝ) + x))) :=
              (ENNReal.ofReal_sum_of_nonneg hnonneg).symm
        _ = ENNReal.ofReal (multiResolventV S s x - 1) := by rw [hbr]
    have hM0_eq : M₀ = ((S.sup id : ℕ) : ℝ) + ((B.sup id : ℕ) : ℝ) + 1 := by
      dsimp [M₀]; push_cast; ring
    have hS_tsum :
        (∑ r ∈ S, ∑' k : ℕ, v (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
          ENNReal.ofReal (∑ r ∈ S, ∑' k : ℕ,
            multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
              ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      have h_nn_r : ∀ r ∈ S, 0 ≤ ∑' k : ℕ,
          multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun r _ =>
        tsum_nonneg fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _)
      rw [ENNReal.ofReal_sum_of_nonneg h_nn_r]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_le : (r : ℝ) ≤ ((S.sup id : ℕ) : ℝ) := by exact_mod_cast Finset.le_sup (f := id) hr
      have hδ : |(r : ℝ) + x| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) r, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (B.sup id)]
      have hsum_r' : Summable fun k : ℕ =>
          multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := by
        refine (hterm_sum ((r : ℝ) + x) hδ).congr fun k => ?_
        congr 2 <;> push_cast <;> ring
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _))
        hsum_r']
      refine tsum_congr fun k => ?_
      dsimp only [v]
      rw [ENNReal.ofReal_mul (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
        (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))]
    have hB_tsum :
        (∑ b ∈ B, ∑' k : ℕ, v (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
          ENNReal.ofReal (∑ b ∈ B, ∑' k : ℕ,
            multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
              ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      have h_nn_b : ∀ b ∈ B, 0 ≤ ∑' k : ℕ,
          multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun b _ =>
        tsum_nonneg fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _)
      rw [ENNReal.ofReal_sum_of_nonneg h_nn_b]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb_nat : b ≤ B.sup id := Finset.le_sup (f := id) hb
      have hb_le : (b : ℝ) ≤ ((B.sup id : ℕ) : ℝ) := by exact_mod_cast hb_nat
      have hbm : b ≤ m := le_trans hb_nat (by omega)
      have hδ : |(-(b : ℝ) + x)| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) b, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (S.sup id)]
      have hsum_b' : Summable fun k : ℕ =>
          multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) := by
        refine (hterm_sum (-(b : ℝ) + x) hδ).congr fun k => ?_
        have hk1m : b ≤ (k + 1) * m := le_trans hbm (Nat.le_mul_of_pos_left m (by omega))
        have hcast : ((((k + 1) * m - b : ℕ) : ℝ) + x) =
            ((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x) := by
          rw [Nat.cast_sub hk1m]; push_cast; ring
        rw [hcast]
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _))
        hsum_b']
      refine tsum_congr fun k => ?_
      dsimp only [v]
      rw [ENNReal.ofReal_mul (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
        (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))]
    have hvx_ge1 : 1 ≤ multiResolventV S s x := hV_ge1 x hx.1
    have h_S_nn : 0 ≤ ∑ r ∈ S, ∑' k : ℕ,
        multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
      Finset.sum_nonneg fun r _ => tsum_nonneg fun k => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _)
    have h_B_nn : 0 ≤ ∑ b ∈ B, ∑' k : ℕ,
        multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
      Finset.sum_nonneg fun b _ => tsum_nonneg fun k => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _)
    have htail_nn : 0 ≤ multiResidueTailReal m S B s x := add_nonneg h_S_nn h_B_nn
    rw [hS_part, hS_tsum, hB_tsum, add_assoc, ← ENNReal.ofReal_add h_S_nn h_B_nn]
    change ENNReal.ofReal (multiResolventV S s x - 1) +
      ENNReal.ofReal (multiResidueTailReal m S B s x) ≤ v x
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hvx_ge1) htail_nn]
    exact ENNReal.ofReal_le_ofReal (by linarith [htail x hx])
  exact dimH_le_of_transferOp_le (multiResidueAlphabet_ge_one hS1) hs_pos
    (by simp : (0 : ℝ≥0∞) < ENNReal.ofReal 1) ENNReal.ofReal_lt_top hv_bd hsub

private lemma dimH_multiResidueSet_supercritical_upper_ennreal {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hsuper : (1 / 2 : ℝ) < poincareAbscissa S) :
    ∃ K₂ > 0, ∀ᶠ m : ℕ in atTop,
      dimH (multiResidueSet m S B) ≤
        ENNReal.ofReal (poincareAbscissa S + K₂ * (m : ℝ) ^ (-(2 * poincareAbscissa S))) := by
  let s₀ : ℝ := poincareAbscissa S
  let d : ℝ := (S.card + B.card : ℝ)
  let Z_s : ℝ := ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀)))
  have hs₀_le1 : s₀ ≤ 1 := poincareAbscissa_le_one hS1
  have hd_nn : 0 ≤ d := by dsimp [d]; positivity
  have hZs_sum : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀)))) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 2 * s₀))
    refine h.congr fun k => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
  have hZs_nn : 0 ≤ Z_s := tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let K₂ : ℝ := 128 * (d + 1) * (Z_s + 1) + 1
  have hK₂_pos : 0 < K₂ := by dsimp [K₂]; positivity
  refine ⟨K₂, hK₂_pos, ?_⟩
  let M₀ : ℝ := ((S.sup id + B.sup id + 1 : ℕ) : ℝ)
  have hM₀1 : 1 ≤ M₀ := by dsimp [M₀]; exact_mod_cast (by omega : 1 ≤ S.sup id + B.sup id + 1)
  have ht_dec : Tendsto (fun m : ℕ => K₂ * (m : ℝ) ^ (-(2 * s₀))) atTop (nhds 0) := by
    have ht0 : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(2 * s₀))) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * s₀)).comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero] using ht0.const_mul K₂
  filter_upwards [eventually_ge_atTop (2 * (S.sup id + B.sup id + 1) + 4),
    ht_dec.eventually (gt_mem_nhds (one_pos : (0 : ℝ) < 1))] with m hm_big hδ_lt1
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm_sep : S.sup id + B.sup id + 1 ≤ m := by omega
  have hm_2M0 : 2 * M₀ ≤ (m : ℝ) := by
    dsimp [M₀]; exact_mod_cast (by omega : 2 * (S.sup id + B.sup id + 1) ≤ m)
  have hm_half_ge1 : (1 : ℝ) ≤ (m : ℝ) / 2 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
    linarith
  let δ : ℝ := K₂ * (m : ℝ) ^ (-(2 * s₀))
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hδ_le1 : δ ≤ 1 := hδ_lt1.le
  let s : ℝ := s₀ + δ
  have hs_lo : 1 / 2 < s := by dsimp [s]; linarith
  have hs_pos : 0 < s := by linarith
  have hsum_s : Summable (wordSum S (2 * s)) :=
    summable_wordSum_of_poincareAbscissa_lt hS1 (by dsimp [s, s₀]; linarith)
  have hC_ub : multiC S (2 * s) ≤ 32 / δ := multiC_supercritical_le hS1 hδ_pos hδ_le1
  have hC_nn : 0 ≤ multiC S (2 * s) :=
    le_trans zero_le_one (one_le_multiC hsum_s)
  have htail : ∀ x ∈ Set.Icc (0 : ℝ) 1, multiResidueTailReal m S B s x ≤ 1 := fun x hx => by
    have hM0_eq : M₀ = ((S.sup id : ℕ) : ℝ) + ((B.sup id : ℕ) : ℝ) + 1 := by
      dsimp [M₀]; push_cast; ring
    have hbr_bd : ∀ γ' : ℝ, |γ'| ≤ M₀ →
        (∑' k : ℕ, multiResolventV S s (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ')) *
            ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ') ^ (-(2 * s)))) ≤
          1 / (d + 1) := fun γ' hγ' => by
      let maj : ℕ → ℝ := fun k =>
        multiC S (2 * s) * (4 * (m : ℝ) ^ (-(2 * s₀))) * (((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀)))
      have hmaj_sum : Summable maj := hZs_sum.mul_left _
      have hpt : ∀ k : ℕ,
          multiResolventV S s (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ')) *
              ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ') ^ (-(2 * s))) ≤ maj k := fun k => by
        have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
        have hk_ge : (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 ≤ ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ' := by
          have := (abs_le.mp hγ').1; nlinarith [hk1, hm_2M0]
        have h_half_ge1 : 1 ≤ (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 := by
          have : 1 * 1 ≤ ((k + 1 : ℕ) : ℝ) * ((m : ℝ) / 2) :=
            mul_le_mul hk1 hm_half_ge1 zero_le_one (by positivity)
          linarith
        have h_half_pos : 0 < (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 := by linarith
        have h_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ' := by linarith
        have hV_le := multiResolventV_le_multiC hS1 hs_pos
          (div_nonneg zero_le_one h_pos.le) hsum_s
        have hpow1 := Real.rpow_le_rpow_of_nonpos (z := -(2 * s)) h_half_pos hk_ge
          (by linarith only [hs_pos])
        have hpow2 : ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(2 * s)) ≤
            ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(2 * s₀)) :=
          Real.rpow_le_rpow_of_exponent_le h_half_ge1 (by dsimp [s]; linarith)
        have hm2_eq : ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(2 * s₀)) =
            (2 : ℝ) ^ (2 * s₀) * (m : ℝ) ^ (-(2 * s₀)) * (((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀))) := by
          rw [show (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 =
              ((m : ℝ) * (1 / 2 : ℝ)) * ((k + 1 : ℕ) : ℝ) by ring,
            Real.mul_rpow (by positivity) (Nat.cast_nonneg _),
            Real.mul_rpow hm_pos.le (by norm_num),
            one_div, Real.inv_rpow zero_le_two, Real.rpow_neg zero_le_two, inv_inv]
          ring
        have h2s₀ : (2 : ℝ) ^ (2 * s₀) ≤ 4 := by
          calc (2 : ℝ) ^ (2 * s₀) ≤ (2 : ℝ) ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
            _ = 4 := by norm_num
        have hm2_le : ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(2 * s₀)) ≤
            4 * (m : ℝ) ^ (-(2 * s₀)) * (((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀))) := by
          rw [hm2_eq]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h2s₀ (Real.rpow_nonneg hm_pos.le _))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        calc _ ≤ multiC S (2 * s) * ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(2 * s)) :=
              mul_le_mul hV_le hpow1 (Real.rpow_nonneg h_pos.le _) hC_nn
          _ ≤ multiC S (2 * s) *
              (4 * (m : ℝ) ^ (-(2 * s₀)) * (((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀)))) :=
              mul_le_mul_of_nonneg_left (hpow2.trans hm2_le) hC_nn
          _ = maj k := by dsimp [maj]; ring
      have hterm_sum' : Summable fun k : ℕ =>
          multiResolventV S s (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ')) *
            ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ') ^ (-(2 * s))) := by
        refine Summable.of_nonneg_of_le (fun k => ?_) hpt hmaj_sum
        have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
        have h_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ' := by
          have := (abs_le.mp hγ').1; nlinarith [hk1, hm_2M0, hM₀1]
        exact mul_nonneg (zero_le_one.trans (one_le_multiResolventV hS1 hs_pos
          (div_nonneg zero_le_one h_pos.le) hsum_s)) (Real.rpow_nonneg h_pos.le _)
      have htsum_le := hterm_sum'.tsum_le_tsum hpt hmaj_sum
      have hmaj_eval : (∑' k : ℕ, maj k) =
          multiC S (2 * s) * (4 * (m : ℝ) ^ (-(2 * s₀))) * Z_s := by
        dsimp only [maj, Z_s]; rw [tsum_mul_left]
      have hconst_le : multiC S (2 * s) * (4 * (m : ℝ) ^ (-(2 * s₀))) * Z_s ≤ 1 / (d + 1) := by
        have h1 : multiC S (2 * s) * (4 * (m : ℝ) ^ (-(2 * s₀))) * Z_s ≤
            (32 / δ) * (4 * (m : ℝ) ^ (-(2 * s₀))) * (Z_s + 1) := by
          refine mul_le_mul ?_ (by linarith) hZs_nn (by positivity)
          exact mul_le_mul_of_nonneg_right hC_ub (by positivity)
        have hm_pow_ne : (m : ℝ) ^ (-(2 * s₀)) ≠ 0 :=
          (Real.rpow_pos_of_pos hm_pos _).ne'
        have h2 : (32 / δ) * (4 * (m : ℝ) ^ (-(2 * s₀))) * (Z_s + 1) =
            (128 * (Z_s + 1)) / K₂ := by
          dsimp only [δ]
          field_simp [hm_pow_ne, hK₂_pos.ne']
          ring
        have h3 : (128 * (Z_s + 1)) / K₂ ≤ 1 / (d + 1) := by
          rw [div_le_div_iff₀ hK₂_pos (by positivity)]
          dsimp only [K₂]
          nlinarith [hd_nn, hZs_nn]
        exact h1.trans (h2 ▸ h3)
      exact htsum_le.trans (hmaj_eval ▸ hconst_le)
    have hS_br : (∑ r ∈ S, ∑' k : ℕ,
        multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) ≤ (S.card : ℝ) * (1 / (d + 1)) := by
      rw [show (S.card : ℝ) * (1 / (d + 1)) = ∑ _r ∈ S, (1 / (d + 1) : ℝ) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun r hr => ?_
      have hr_le : (r : ℝ) ≤ ((S.sup id : ℕ) : ℝ) := by exact_mod_cast Finset.le_sup (f := id) hr
      have hγ' : |(r : ℝ) + x| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) r, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (B.sup id), hM0_eq]
      have hcongr : (∑' k : ℕ, multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) =
          ∑' k : ℕ, multiResolventV S s (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((r : ℝ) + x))) *
            ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((r : ℝ) + x)) ^ (-(2 * s))) := by
        refine tsum_congr fun k => ?_
        congr 2 <;> push_cast <;> ring
      rw [hcongr]
      exact hbr_bd ((r : ℝ) + x) hγ'
    have hB_br : (∑ b ∈ B, ∑' k : ℕ,
        multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) ≤ (B.card : ℝ) * (1 / (d + 1)) := by
      rw [show (B.card : ℝ) * (1 / (d + 1)) = ∑ _b ∈ B, (1 / (d + 1) : ℝ) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun b hb => ?_
      have hb_nat : b ≤ B.sup id := Finset.le_sup (f := id) hb
      have hb_le : (b : ℝ) ≤ ((B.sup id : ℕ) : ℝ) := by exact_mod_cast hb_nat
      have hbm : b ≤ m := le_trans hb_nat (by omega)
      have hγ' : |(-(b : ℝ) + x)| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) b, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (S.sup id), hM0_eq]
      have hcongr : (∑' k : ℕ, multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) =
          ∑' k : ℕ, multiResolventV S s (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x))) *
            ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x)) ^ (-(2 * s))) := by
        refine tsum_congr fun k => ?_
        have hk1m : b ≤ (k + 1) * m := le_trans hbm (Nat.le_mul_of_pos_left m (by omega))
        have hcast : ((((k + 1) * m - b : ℕ) : ℝ) + x) =
            ((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x) := by
          rw [Nat.cast_sub hk1m]; push_cast; ring
        rw [hcast]
      rw [hcongr]
      exact hbr_bd (-(b : ℝ) + x) hγ'
    calc multiResidueTailReal m S B s x
        ≤ (S.card : ℝ) * (1 / (d + 1)) + (B.card : ℝ) * (1 / (d + 1)) := add_le_add hS_br hB_br
      _ = d / (d + 1) := by dsimp only [d]; ring
      _ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  exact dimH_multiResidue_upper_of_tail_le_s hS1 hm_sep hm_2M0 hs_lo hsum_s htail

/-- **Supercritical upper power-law bound**: when `1/2 < poincareAbscissa S`,
    `dimH (multiResidueSet m S B) ≤ s₀ + K₂ * m ^ (-2 s₀)` for all large `m`. -/
theorem dimH_multiResidueSet_supercritical_upper {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hsuper : (1 / 2 : ℝ) < poincareAbscissa S) :
    ∃ K₂ > 0, ∀ᶠ m : ℕ in atTop,
      (dimH (multiResidueSet m S B)).toReal - poincareAbscissa S ≤
        K₂ * (m : ℝ) ^ (-(2 * poincareAbscissa S)) := by
  obtain ⟨K₂, hK₂, h_ev⟩ := dimH_multiResidueSet_supercritical_upper_ennreal hS1 hsuper
  refine ⟨K₂, hK₂, ?_⟩
  filter_upwards [h_ev] with m hm
  have hnn : 0 ≤ poincareAbscissa S + K₂ * (m : ℝ) ^ (-(2 * poincareAbscissa S)) := by
    have : 0 ≤ poincareAbscissa S := poincareAbscissa_nonneg S
    positivity
  have hle := ENNReal.toReal_le_of_le_ofReal hnn hm
  linarith

private lemma transferOp_finset_sum_fun (S : Finset ℕ) (s : ℝ) (n : ℕ)
    (f : ℕ → ℝ → ℝ≥0∞) (x : ℝ) :
    transferOp (S : Set ℕ) s (fun y => ∑ j ∈ Finset.range n, f j y) x =
      ∑ j ∈ Finset.range n, transferOp (S : Set ℕ) s (f j) x := by
  simp_rw [transferOp_finset_eq, Finset.sum_mul]
  exact Finset.sum_comm

/-- **Supercritical lower power-law bound**: when `1/2 < poincareAbscissa S`,
    `K₁ * m ^ (-2 s₀) ≤ dimH (multiResidueSet m S B) - s₀` for all large `m`. -/
theorem dimH_multiResidueSet_supercritical_lower {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hsuper : (1 / 2 : ℝ) < poincareAbscissa S) :
    ∃ K₁ > 0, ∀ᶠ m : ℕ in atTop,
      K₁ * (m : ℝ) ^ (-(2 * poincareAbscissa S)) ≤
        (dimH (multiResidueSet m S B)).toReal - poincareAbscissa S := by
  let s₀ : ℝ := poincareAbscissa S
  have hs₀_pos : 0 < s₀ := by dsimp [s₀]; linarith
  have hs₀_nn : 0 ≤ s₀ := hs₀_pos.le
  have hs₀_le1 : s₀ ≤ 1 := poincareAbscissa_le_one hS1
  have hSne : S.Nonempty := poincareAbscissa_lt_half_imp_nonempty hsuper
  obtain ⟨r₀, hr₀⟩ := hSne
  have hr₀_1 : 1 ≤ r₀ := hS1 r₀ hr₀
  have hr₀_leM : r₀ ≤ S.sup id := Finset.le_sup (f := id) hr₀
  let M : ℕ := S.sup id
  have hM1 : 1 ≤ M := hr₀_1.trans hr₀_leM
  let L : ℝ := 2 * Real.log ((M : ℝ) + 1)
  have hM2_ge2 : (2 : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast (by omega : 2 ≤ M + 1)
  have hlog2_le : Real.log 2 ≤ Real.log ((M : ℝ) + 1) := Real.log_le_log two_pos hM2_ge2
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [one_half_le_log_two, hlog2_le]
  have hL_pos : 0 < L := by linarith
  let K₁ : ℝ := 1 / (2048 * L)
  have hK₁_pos : 0 < K₁ := by dsimp [K₁]; positivity
  obtain ⟨K₂, _, h_up_enn⟩ := dimH_multiResidueSet_supercritical_upper_ennreal (B := B) hS1 hsuper
  have ht_rpow0 : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(2 * s₀))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * s₀)).comp tendsto_natCast_atTop_atTop
  have ht_δL : Tendsto (fun m : ℕ => (K₁ * (m : ℝ) ^ (-(2 * s₀))) * L) atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using (ht_rpow0.const_mul K₁).mul_const L
  have ht_2m : Tendsto (fun m : ℕ =>
      2 * (K₁ * (m : ℝ) ^ (-(2 * s₀))) * Real.log (2 * (m : ℝ))) atTop (nhds 0) := by
    have ht_rhs : Tendsto (fun m : ℕ =>
        (2 * K₁) * (Real.log 2 / (m : ℝ) + Real.log (m : ℝ) / (m : ℝ))) atTop (nhds 0) := by
      have t1 : Tendsto (fun m : ℕ => Real.log 2 / (m : ℝ)) atTop (nhds 0) :=
        (tendsto_const_nhds (x := Real.log 2)).div_atTop tendsto_natCast_atTop_atTop
      simpa only [add_zero, mul_zero] using (t1.add tendsto_log_div_nat_local).const_mul (2 * K₁)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht_rhs ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with m hm1
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hlog_nn : 0 ≤ Real.log (2 * (m : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * m))
      positivity
    · filter_upwards [eventually_ge_atTop 1] with m hm1
      have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
      have hpow_le : (m : ℝ) ^ (-(2 * s₀)) ≤ (m : ℝ)⁻¹ := by
        calc (m : ℝ) ^ (-(2 * s₀))
            ≤ (m : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm_ge1 (by linarith)
          _ = (m : ℝ)⁻¹ := Real.rpow_neg_one (m : ℝ)
      have hlog_eq : Real.log (2 * (m : ℝ)) = Real.log 2 + Real.log (m : ℝ) :=
        Real.log_mul two_ne_zero hm_pos.ne'
      have hlog_nn : 0 ≤ Real.log (2 * (m : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * m))
      rw [hlog_eq]
      calc 2 * (K₁ * (m : ℝ) ^ (-(2 * s₀))) * (Real.log 2 + Real.log (m : ℝ))
          ≤ 2 * (K₁ * (m : ℝ)⁻¹) * (Real.log 2 + Real.log (m : ℝ)) := by
            rw [← hlog_eq]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow_le hK₁_pos.le) zero_le_two)
              hlog_nn
        _ = (2 * K₁) * (Real.log 2 / (m : ℝ) + Real.log (m : ℝ) / (m : ℝ)) := by ring
  refine ⟨K₁, hK₁_pos, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * (S.sup id + B.sup id + 1) + 4),
    ht_δL.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    ht_2m.eventually (gt_mem_nhds (one_pos : (0 : ℝ) < 1)),
    h_up_enn]
    with m hm_big hδL_lt h2m_lt h_dim_enn
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm_sep : S.sup id + B.sup id + 1 ≤ m := by omega
  have hr₀_lt_m : r₀ < m := lt_of_le_of_lt hr₀_leM (by omega)
  let δ : ℝ := K₁ * (m : ℝ) ^ (-(2 * s₀))
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hδL_pos : 0 < δ * L := mul_pos hδ_pos hL_pos
  have hδL_le : δ * L ≤ 1 / 4 := hδL_lt.le
  have hδ_le : δ ≤ 1 / 4 := by nlinarith [hL1, hδ_pos]
  let s : ℝ := s₀ + δ
  have hs_lo : 1 / 2 < s := by dsimp [s]; linarith
  have hs_pos : 0 < s := by linarith
  have h2s_le3 : 2 * s ≤ 3 := by dsimp [s]; linarith
  let n : ℕ := Nat.floor (1 / (δ * L))
  have h_inv_ge4 : (4 : ℝ) ≤ 1 / (δ * L) := by
    rw [le_div_iff₀ hδL_pos]; linarith
  have hn_ge4 : 4 ≤ n := Nat.le_floor h_inv_ge4
  have hn_pos_nat : 0 < n := by omega
  have hn_le : (n : ℝ) ≤ 1 / (δ * L) := Nat.floor_le (div_nonneg zero_le_one hδL_pos.le)
  have hn_ge_half : 1 / (2 * δ * L) ≤ (n : ℝ) := by
    have hlt := Nat.lt_floor_add_one (1 / (δ * L))
    change 1 / (δ * L) < (n : ℝ) + 1 at hlt
    have hhalf_ge2 : (2 : ℝ) ≤ 1 / (2 * δ * L) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hsub_eq : 1 / (δ * L) - 1 = 2 * (1 / (2 * δ * L)) - 1 := by
      field_simp [hδ_pos.ne', hL_pos.ne']
    linarith
  let a₁ : ℕ := m + r₀
  have ha₁_notMem : a₁ ∉ S := by
    intro ha₁_mem
    have hsup : m + r₀ ≤ S.sup id := Finset.le_sup (f := id) ha₁_mem
    omega
  have ha₁_in : a₁ ∈ multiResidueAlphabet m S B := by
    refine Or.inl ⟨r₀, hr₀, by omega, ?_⟩
    show (m + r₀) % m = r₀ % m
    rw [Nat.add_mod_left]
  let A₁ : Finset ℕ := insert a₁ S
  have hA₁_ne : A₁.Nonempty := ⟨a₁, Finset.mem_insert_self _ _⟩
  have hA₁_sub : (A₁ : Set ℕ) ⊆ multiResidueAlphabet m S B := by
    intro a ha
    simp only [Finset.mem_coe, A₁, Finset.mem_insert] at ha
    rcases ha with rfl | haS
    · exact ha₁_in
    · exact Or.inl ⟨a, haS, le_rfl, rfl⟩
  have hA₁_1 : ∀ a ∈ A₁, 1 ≤ a := fun a ha => multiResidueAlphabet_ge_one hS1 a (hA₁_sub ha)
  have hexp_neg1_ge : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos 1) (Real.exp_one_lt_d9.le.trans (by norm_num))
  have hiter_bd : ∀ j : ℕ, j < n → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (1 / 48) ≤ (transferOp (S : Set ℕ) s)^[j] (fun _ => 1) y ∧
        (transferOp (S : Set ℕ) s)^[j] (fun _ => 1) y ≤ ENNReal.ofReal 4 := fun j hj y hy => by
    rw [transferOp_iterate_one_eq S (fun a ha => hS1 a ha) hs_pos j hy]
    have h_ub : (∑ w : Fin j → {a : ℕ // a ∈ S},
        (denQ (subWord j w) + denP (subWord j w) * y) ^ (-(2 * s))) ≤ 4 := by
      have hterm : ∀ w : Fin j → {a : ℕ // a ∈ S},
          (denQ (subWord j w) + denP (subWord j w) * y) ^ (-(2 * s)) ≤
            denQ (subWord j w) ^ (-(2 * s₀)) := fun w => by
        have hpd := posDigits_subWord (fun a ha => hS1 a ha) j w
        have hq1 : 1 ≤ denQ (subWord j w) := denQ_ge_one hpd
        have hqp_ge : denQ (subWord j w) ≤ denQ (subWord j w) + denP (subWord j w) * y := by
          linarith [mul_nonneg (denP_nonneg (subWord j w)) hy.1]
        have h1 := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < denQ (subWord j w)) hqp_ge
          (by linarith : -(2 * s) ≤ 0)
        have h2 := Real.rpow_le_rpow_of_exponent_le hq1 (by dsimp [s]; linarith : -(2 * s) ≤ -(2 * s₀))
        exact h1.trans h2
      have hsum_le : (∑ w : Fin j → {a : ℕ // a ∈ S},
          (denQ (subWord j w) + denP (subWord j w) * y) ^ (-(2 * s))) ≤
          wordSum S (2 * s₀) j := Finset.sum_le_sum fun w _ => hterm w
      have hw4 : wordSum S (2 * s₀) j ≤ 4 := by
        have h1 := wordSum_poincareAbscissa_le hS1 j
        have h2 : (2 : ℝ) ^ (2 * s₀) ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
        norm_num at h2
        exact h1.trans h2
      exact hsum_le.trans hw4
    have h_lb : (1 / 48 : ℝ) ≤ ∑ w : Fin j → {a : ℕ // a ∈ S},
        (denQ (subWord j w) + denP (subWord j w) * y) ^ (-(2 * s)) := by
      by_cases hj0 : j = 0
      · subst hj0
        letI : Unique (Fin 0 → {a : ℕ // a ∈ S}) :=
          { default := Fin.elim0, uniq := fun _ => funext fun i => i.elim0 }
        rw [Fintype.sum_unique]
        have hsw : subWord 0 (default : Fin 0 → {a : ℕ // a ∈ S}) = [] := by simp [subWord]
        rw [hsw, denQ_nil, denP_nil, zero_mul, add_zero, Real.one_rpow]
        norm_num
      · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
        have hterm : ∀ w : Fin j → {a : ℕ // a ∈ S},
            (1 / 24 : ℝ) * denQ (subWord j w) ^ (-(2 * s₀)) ≤
              (denQ (subWord j w) + denP (subWord j w) * y) ^ (-(2 * s)) := fun w => by
          have hpd := posDigits_subWord (fun a ha => hS1 a ha) j w
          have hq_pos : 0 < denQ (subWord j w) := denQ_pos hpd
          have hp_le : denP (subWord j w) ≤ denQ (subWord j w) := denP_le_denQ hpd
          have hqp_le : denQ (subWord j w) + denP (subWord j w) * y ≤ 2 * denQ (subWord j w) := by
            have : denP (subWord j w) * y ≤ denP (subWord j w) * 1 :=
              mul_le_mul_of_nonneg_left hy.2 (denP_nonneg _)
            linarith
          have h_pos_sum : 0 < denQ (subWord j w) + denP (subWord j w) * y := by
            linarith [mul_nonneg (denP_nonneg (subWord j w)) hy.1]
          have h1 := Real.rpow_le_rpow_of_nonpos h_pos_sum hqp_le (by linarith : -(2 * s) ≤ 0)
          have h_split : (2 * denQ (subWord j w)) ^ (-(2 * s)) =
              (2 : ℝ) ^ (-(2 * s)) * denQ (subWord j w) ^ (-(2 * s₀)) *
                denQ (subWord j w) ^ (-(2 * δ)) := by
            rw [Real.mul_rpow zero_le_two hq_pos.le,
              show -(2 * s) = -(2 * s₀) + -(2 * δ) by dsimp [s]; ring,
              Real.rpow_add hq_pos]
            ring
          have h2s_ge : (1 / 8 : ℝ) ≤ (2 : ℝ) ^ (-(2 * s)) := by
            calc (1 / 8 : ℝ) = (2 : ℝ) ^ (-3 : ℝ) := by norm_num
              _ ≤ (2 : ℝ) ^ (-(2 * s)) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
          have hqM : denQ (subWord j w) ≤ ((M : ℝ) + 1) ^ j := by
            have hmem : ∀ a ∈ subWord j w, a ≤ M := by
              intro a ha
              simp only [subWord, List.mem_ofFn] at ha
              obtain ⟨i, rfl⟩ := ha
              exact Finset.le_sup (f := id) (w i).2
            simpa [subWord_length] using denQ_le_max_add_one_pow hpd hmem
          have hqδ_ge : (1 / 3 : ℝ) ≤ denQ (subWord j w) ^ (-(2 * δ)) := by
            have h_pow_ge := Real.rpow_le_rpow_of_nonpos hq_pos hqM (by linarith : -(2 * δ) ≤ 0)
            have hMp_pos : 0 < (M : ℝ) + 1 := by positivity
            have h_exp_eq : (((M : ℝ) + 1) ^ j) ^ (-(2 * δ)) =
                Real.exp (-((j : ℝ) * δ * L)) := by
              rw [← Real.rpow_natCast ((M : ℝ) + 1) j, ← Real.rpow_mul hMp_pos.le,
                Real.rpow_def_of_pos hMp_pos]
              congr 1
              dsimp only [L]; ring
            have hj_le : (j : ℝ) ≤ 1 / (δ * L) :=
              le_trans (by exact_mod_cast hj.le) hn_le
            have h_exp_bd : -1 ≤ -((j : ℝ) * δ * L) := by
              have h_mul : (j : ℝ) * (δ * L) ≤ 1 := (le_div_iff₀ hδL_pos).mp hj_le
              linarith
            exact hexp_neg1_ge.trans ((Real.exp_le_exp.mpr h_exp_bd).trans (h_exp_eq ▸ h_pow_ge))
          have hq_nn : 0 ≤ denQ (subWord j w) ^ (-(2 * s₀)) := Real.rpow_nonneg hq_pos.le _
          calc (1 / 24 : ℝ) * denQ (subWord j w) ^ (-(2 * s₀))
              = ((1 / 8 : ℝ) * (1 / 3 : ℝ)) * denQ (subWord j w) ^ (-(2 * s₀)) := by norm_num
            _ ≤ ((2 : ℝ) ^ (-(2 * s)) * denQ (subWord j w) ^ (-(2 * δ))) *
                  denQ (subWord j w) ^ (-(2 * s₀)) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul h2s_ge hqδ_ge (by positivity) (by positivity)) hq_nn
            _ = (2 * denQ (subWord j w)) ^ (-(2 * s)) := by rw [h_split]; ring
            _ ≤ (denQ (subWord j w) + denP (subWord j w) * y) ^ (-(2 * s)) := h1
        have hws : 1 ≤ wordSum S (2 * s₀) j :=
          one_le_wordSum_poincareAbscissa hS1 hs₀_pos j hj1
        have hsum_ge : (1 / 24 : ℝ) * wordSum S (2 * s₀) j ≤
            ∑ w : Fin j → {a : ℕ // a ∈ S},
              (denQ (subWord j w) + denP (subWord j w) * y) ^ (-(2 * s)) := by
          unfold wordSum
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun w _ => hterm w
        linarith
    exact ⟨ENNReal.ofReal_le_ofReal h_lb, ENNReal.ofReal_le_ofReal h_ub⟩
  let v : ℝ → ℝ≥0∞ := fun x => ∑ j ∈ Finset.range n, (transferOp (S : Set ℕ) s)^[j] (fun _ => 1) x
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal 1 ≤ v x ∧ v x ≤ ENNReal.ofReal (4 * (n : ℝ)) := fun x hx => by
    constructor
    · have h0 : (transferOp (S : Set ℕ) s)^[0] (fun _ => 1) x = 1 := rfl
      have hmem0 : 0 ∈ Finset.range n := Finset.mem_range.mpr hn_pos_nat
      calc ENNReal.ofReal 1 = 1 := by simp
        _ = (transferOp (S : Set ℕ) s)^[0] (fun _ => 1) x := rfl
        _ ≤ v x := Finset.single_le_sum
            (f := fun j => (transferOp (S : Set ℕ) s)^[j] (fun _ => 1) x)
            (fun _ _ => zero_le) hmem0
    · calc v x ≤ ∑ _j ∈ Finset.range n, ENNReal.ofReal 4 :=
            Finset.sum_le_sum fun j hj => (hiter_bd j (Finset.mem_range.mp hj) x hx).2
        _ = ENNReal.ofReal (4 * (n : ℝ)) := by
            rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by norm_num :
              ∀ _ ∈ Finset.range n, (0 : ℝ) ≤ 4), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring_nf
  have hsuper_op : ∀ x ∈ Set.Icc (0 : ℝ) 1, v x ≤ transferOp (A₁ : Set ℕ) s v x := fun x hx => by
    have hv_lo_br : ∀ y ∈ Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((n : ℝ) / 48) ≤ v y := fun y hy => by
      calc ENNReal.ofReal ((n : ℝ) / 48)
          = ENNReal.ofReal (∑ _j ∈ Finset.range n, (1 / 48 : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring_nf
        _ = ∑ _j ∈ Finset.range n, ENNReal.ofReal (1 / 48) :=
            ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)
        _ ≤ v y := Finset.sum_le_sum fun j hj => (hiter_bd j (Finset.mem_range.mp hj) y hy).1
    have ha₁_ge1 : (1 : ℝ) ≤ (a₁ : ℝ) + x := by
      have : (1 : ℝ) ≤ (a₁ : ℝ) := by exact_mod_cast (by omega : 1 ≤ a₁)
      linarith [hx.1]
    have ha₁_le_2m : (a₁ : ℝ) + x ≤ 2 * (m : ℝ) := by
      have hm_le : (a₁ : ℝ) + x ≤ (m : ℝ) + (r₀ : ℝ) + 1 := by
        dsimp [a₁]; push_cast; linarith [hx.2]
      have hr1_le : (r₀ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (by omega : r₀ + 1 ≤ m)
      linarith
    have hy₀_mem : (1 / ((a₁ : ℝ) + x)) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, div_le_one_of_le₀ ha₁_ge1 (by linarith)⟩
    have ha₁_pow_ge : (1 / 12 : ℝ) * (m : ℝ) ^ (-(2 * s₀)) ≤ ((a₁ : ℝ) + x) ^ (-(2 * s)) := by
      have h1 := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < (a₁ : ℝ) + x) ha₁_le_2m
        (by linarith : -(2 * s) ≤ 0)
      have hsplit : (2 * (m : ℝ)) ^ (-(2 * s)) =
          (2 : ℝ) ^ (-(2 * s₀)) * (m : ℝ) ^ (-(2 * s₀)) * (2 * (m : ℝ)) ^ (-(2 * δ)) := by
        rw [Real.mul_rpow zero_le_two hm_pos.le,
          show -(2 * s) = -(2 * s₀) + -(2 * δ) by dsimp [s]; ring,
          Real.rpow_add two_pos, Real.rpow_add hm_pos, Real.mul_rpow zero_le_two hm_pos.le]
        ring
      have h2s0_ge : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (-(2 * s₀)) := by
        calc (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by norm_num
          _ ≤ (2 : ℝ) ^ (-(2 * s₀)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
      have hm2δ_ge : (1 / 3 : ℝ) ≤ (2 * (m : ℝ)) ^ (-(2 * δ)) := by
        have h2m_pos : 0 < 2 * (m : ℝ) := by linarith
        rw [Real.rpow_def_of_pos h2m_pos,
          show Real.log (2 * (m : ℝ)) * -(2 * δ) = -(2 * δ * Real.log (2 * (m : ℝ))) by ring]
        exact hexp_neg1_ge.trans (Real.exp_le_exp.mpr (by linarith [h2m_lt.le]))
      have hm_nn : 0 ≤ (m : ℝ) ^ (-(2 * s₀)) := Real.rpow_nonneg hm_pos.le _
      calc (1 / 12 : ℝ) * (m : ℝ) ^ (-(2 * s₀))
          = ((1 / 4 : ℝ) * (1 / 3 : ℝ)) * (m : ℝ) ^ (-(2 * s₀)) := by norm_num
        _ ≤ ((2 : ℝ) ^ (-(2 * s₀)) * (2 * (m : ℝ)) ^ (-(2 * δ))) * (m : ℝ) ^ (-(2 * s₀)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul h2s0_ge hm2δ_ge (by positivity) (by positivity)) hm_nn
        _ = (2 * (m : ℝ)) ^ (-(2 * s)) := by rw [hsplit]; ring
        _ ≤ ((a₁ : ℝ) + x) ^ (-(2 * s)) := h1
    have ha₁_branch_ge1 : ENNReal.ofReal 1 ≤
        v (1 / ((a₁ : ℝ) + x)) * ENNReal.ofReal (((a₁ : ℝ) + x) ^ (-(2 * s))) := by
      have hmul_real : 1 ≤ ((n : ℝ) / 48) * ((1 / 12 : ℝ) * (m : ℝ) ^ (-(2 * s₀))) := by
        have h1 : (1 / (2 * δ * L) / 48) * ((1 / 12 : ℝ) * (m : ℝ) ^ (-(2 * s₀))) =
            1024 / 576 := by
          have hm_pow_ne : (m : ℝ) ^ (-(2 * s₀)) ≠ 0 := (Real.rpow_pos_of_pos hm_pos _).ne'
          dsimp only [δ, K₁]
          field_simp [hm_pow_ne, hL_pos.ne']
          ring
        have h2 : (1 / (2 * δ * L) / 48) * ((1 / 12 : ℝ) * (m : ℝ) ^ (-(2 * s₀))) ≤
            ((n : ℝ) / 48) * ((1 / 12 : ℝ) * (m : ℝ) ^ (-(2 * s₀))) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hn_ge_half (by norm_num)) (by positivity)
        linarith
      calc ENNReal.ofReal 1
          ≤ ENNReal.ofReal (((n : ℝ) / 48) * ((1 / 12 : ℝ) * (m : ℝ) ^ (-(2 * s₀)))) :=
            ENNReal.ofReal_le_ofReal hmul_real
        _ = ENNReal.ofReal ((n : ℝ) / 48) * ENNReal.ofReal ((1 / 12 : ℝ) * (m : ℝ) ^ (-(2 * s₀))) :=
            ENNReal.ofReal_mul (by positivity)
        _ ≤ v (1 / ((a₁ : ℝ) + x)) * ENNReal.ofReal (((a₁ : ℝ) + x) ^ (-(2 * s))) :=
            mul_le_mul' (hv_lo_br _ hy₀_mem) (ENNReal.ofReal_le_ofReal ha₁_pow_ge)
    have hsplit_op : transferOp (A₁ : Set ℕ) s v x =
        v (1 / ((a₁ : ℝ) + x)) * ENNReal.ofReal (((a₁ : ℝ) + x) ^ (-(2 * s))) +
          transferOp (S : Set ℕ) s v x := by
      rw [transferOp_finset_eq, show A₁ = insert a₁ S from rfl, Finset.sum_insert ha₁_notMem,
        transferOp_finset_eq]
    have h_tele : v x ≤ ENNReal.ofReal 1 + transferOp (S : Set ℕ) s v x := by
      have hsum_op : transferOp (S : Set ℕ) s v x =
          ∑ j ∈ Finset.range n, (transferOp (S : Set ℕ) s)^[j + 1] (fun _ => 1) x := by
        dsimp only [v]
        rw [transferOp_finset_sum_fun]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Function.iterate_succ_apply']
      calc v x ≤ v x + (transferOp (S : Set ℕ) s)^[n] (fun _ => 1) x := le_self_add
        _ = ∑ j ∈ Finset.range (n + 1), (transferOp (S : Set ℕ) s)^[j] (fun _ => 1) x := by
            rw [Finset.sum_range_succ]
        _ = ∑ j ∈ Finset.range n, (transferOp (S : Set ℕ) s)^[j + 1] (fun _ => 1) x +
              (transferOp (S : Set ℕ) s)^[0] (fun _ => 1) x :=
            Finset.sum_range_succ' _ _
        _ = ENNReal.ofReal 1 + transferOp (S : Set ℕ) s v x := by
            rw [← hsum_op, add_comm]
            have h0 : (transferOp (S : Set ℕ) s)^[0] (fun _ => 1) x = ENNReal.ofReal 1 := by simp
            rw [h0]
    rw [hsplit_op]
    exact h_tele.trans (add_le_add_left ha₁_branch_ge1 _)
  have hsub_dim : ENNReal.ofReal s ≤ dimH (cfAlphabetSet (A₁ : Set ℕ)) :=
    le_dimH_of_transferOp_ge hA₁_ne hA₁_1 hs_pos
      (by simp : (0 : ℝ≥0∞) < ENNReal.ofReal 1) ENNReal.ofReal_lt_top hv_bd hsuper_op
  have hset_mono : cfAlphabetSet (A₁ : Set ℕ) ⊆ multiResidueSet m S B := by
    rintro x ⟨hx01, hirr, hadm⟩
    exact ⟨hx01, hirr, fun i => hA₁_sub (hadm i)⟩
  have hlo_enn : ENNReal.ofReal s ≤ dimH (multiResidueSet m S B) :=
    hsub_dim.trans (dimH_mono hset_mono)
  have hne_top : dimH (multiResidueSet m S B) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_dim_enn
  have hle_real : s ≤ (dimH (multiResidueSet m S B)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hne_top).mp hlo_enn
  dsimp only [s] at hle_real
  linarith

/-- **Supercritical Exact Two-Sided Power-Law Convergence Rate**:
    when `1 / 2 < s₀ := poincareAbscissa S`, there exist `K₁, K₂ > 0` such that
    for all sufficiently large `m`, `K₁ * m^(-2 s₀) ≤ dimH (multiResidueSet m S B) - s₀ ≤ K₂ * m^(-2 s₀)`. -/
theorem dimH_multiResidueSet_supercritical_rate {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hsuper : (1 / 2 : ℝ) < poincareAbscissa S) :
    ∃ K₁ > 0, ∃ K₂ > 0, ∀ᶠ m : ℕ in atTop,
      K₁ * (m : ℝ) ^ (-(2 * poincareAbscissa S)) ≤
          (dimH (multiResidueSet m S B)).toReal - poincareAbscissa S ∧
        (dimH (multiResidueSet m S B)).toReal - poincareAbscissa S ≤
          K₂ * (m : ℝ) ^ (-(2 * poincareAbscissa S)) := by
  obtain ⟨K₁, hK₁, h_lo⟩ := dimH_multiResidueSet_supercritical_lower hS1 hsuper
  obtain ⟨K₂, hK₂, h_up⟩ := dimH_multiResidueSet_supercritical_upper hS1 hsuper
  refine ⟨K₁, hK₁, K₂, hK₂, ?_⟩
  filter_upwards [h_lo, h_up] with m hml hmu
  exact ⟨hml, hmu⟩

/-- Concrete supercritical power-law convergence rate `Θ(m ^ (-2 s₀))` for `S = {1, 2}`
    (arbitrary auxiliary `B : Finset ℕ`). -/
theorem dimH_multiResidueSet_one_two_supercritical_rate (B : Finset ℕ) :
    ∃ K₁ > 0, ∃ K₂ > 0, ∀ᶠ m : ℕ in atTop,
      K₁ * (m : ℝ) ^ (-(2 * poincareAbscissa ({1, 2} : Finset ℕ))) ≤
          (dimH (multiResidueSet m ({1, 2} : Finset ℕ) B)).toReal -
            poincareAbscissa ({1, 2} : Finset ℕ) ∧
        (dimH (multiResidueSet m ({1, 2} : Finset ℕ) B)).toReal -
            poincareAbscissa ({1, 2} : Finset ℕ) ≤
          K₂ * (m : ℝ) ^ (-(2 * poincareAbscissa ({1, 2} : Finset ℕ))) :=
  dimH_multiResidueSet_supercritical_rate (by decide) supercritical_pair_one_two.2

end

end ResidueMultiAsymptotic
