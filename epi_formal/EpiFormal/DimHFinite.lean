import Mathlib
import EpiFormal.DimHCore
import EpiFormal.SpectralGap

open Real Filter MeasureTheory Topology Set
open scoped ENNReal NNReal

namespace DimHFinite
open DimHCore SpectralGap

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000

noncomputable section

/-! ## 1. 覆盖区间与分支 -/

def interv (t : ℝ) (j : ℕ) (k : ℕ) : Set ℝ :=
  Icc ((k : ℝ) / (Qsel j : ℝ) - rad t j) ((k : ℝ) / (Qsel j : ℝ) + rad t j)

lemma ediam_interv_le (t : ℝ) (ht : 0 ≤ t) (j k : ℕ) :
    Metric.ediam (interv t j k) ≤ ENNReal.ofReal (2 * rad t j) := by
  have hsub : ((k : ℝ) / (Qsel j : ℝ) + rad t j) - ((k : ℝ) / (Qsel j : ℝ) - rad t j)
      = 2 * rad t j := by ring
  rw [interv, Real.ediam_Icc, hsub]

def branchCond (t : ℝ) (j : ℕ) (k k' : ℕ) : Prop :=
  |(k : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤ rad t j + rad t (j + 1)

def branchSet (t : ℝ) (j k : ℕ) : Finset ℕ :=
  (Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun k' => branchCond t j k k')

def survSet (t : ℝ) (J : ℕ) : ℕ → Finset ℕ
  | 0 => Finset.range ((Qsel J).toNat + 1)
  | n + 1 => (survSet t J n).biUnion (fun k => branchSet t (J + n) k)

lemma survSet_succ (t : ℝ) (J n : ℕ) :
    survSet t J (n + 1) = (survSet t J n).biUnion (fun k => branchSet t (J + n) k) := rfl

lemma card_branchSet_le (t : ℝ) (ht : 0 ≤ t) (j : ℕ) (hj : 1 ≤ j) (k : ℕ) :
    (branchSet t j k).card ≤ branchB t := by
  classical
  have h := fiber_card_le t ht j hj k
  have hsub : branchSet t j k ⊆
      (Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun (k' : ℕ) =>
        |(k : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤ rad t j + rad t (j + 1)) := by
    intro k' hk'
    simp only [branchSet, branchCond] at hk' ⊢
    exact hk'
  exact Finset.card_le_card hsub |>.trans h

lemma card_survSet_le (t : ℝ) (ht : 0 ≤ t) (J : ℕ) (hJ : 1 ≤ J) (n : ℕ) :
    (survSet t J n).card ≤ ((Qsel J).toNat + 1) * (branchB t) ^ n := by
  induction n with
  | zero =>
      have h1 : survSet t J 0 = Finset.range ((Qsel J).toNat + 1) := rfl
      rw [h1, Finset.card_range, pow_zero, Nat.mul_one]
  | succ n ih =>
      have hJn : 1 ≤ J + n := by omega
      have hstep : ∀ k ∈ survSet t J n, (branchSet t (J + n) k).card ≤ branchB t := by
        intro k _; exact card_branchSet_le t ht (J + n) hJn k
      calc (survSet t J (n + 1)).card
          = ((survSet t J n).biUnion (fun k => branchSet t (J + n) k)).card := by rw [survSet_succ]
        _ ≤ (survSet t J n).card * branchB t := Finset.card_biUnion_le_card_mul _ _ _ hstep
        _ ≤ (((Qsel J).toNat + 1) * (branchB t) ^ n) * branchB t := Nat.mul_le_mul_right _ ih
        _ = ((Qsel J).toNat + 1) * (branchB t) ^ (n + 1) := by rw [pow_succ]; ring

/-! ## 2. 中心序列 -/

def centerOf (x : ℝ) (j : ℕ) : ℕ := (round ((Qsel j : ℝ) * x)).toNat

lemma Qsel_real_nonneg (j : ℕ) : 0 ≤ (Qsel j : ℝ) := by
  by_cases hj : 1 ≤ j
  · exact le_of_lt (by exact_mod_cast Qsel_pos j hj)
  · have hj0 : j = 0 := by omega
    subst hj0
    have hq : Qsel 0 = 1 := Qsel_zero
    simp [hq]

lemma round_centerOf_nonneg (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
    0 ≤ round ((Qsel j : ℝ) * x) := by
  set y := (Qsel j : ℝ) * x with hydef
  have hy : 0 ≤ y := mul_nonneg (Qsel_real_nonneg j) hx
  have h1 : |y - (round y : ℝ)| ≤ |y - (0 : ℤ)| := round_le y 0
  have h2 : |y - (0 : ℤ)| = y := by push_cast; rw [sub_zero, abs_of_nonneg hy]
  rw [h2] at h1
  have h3 : y - (round y : ℝ) ≤ y := le_trans (le_abs_self _) h1
  have h4 : 0 ≤ (round y : ℝ) := by linarith
  exact_mod_cast h4

lemma cast_centerOf (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
    (centerOf x j : ℝ) = (round ((Qsel j : ℝ) * x) : ℝ) := by
  have hrnn := round_centerOf_nonneg x hx j
  have htoNat : ((round ((Qsel j : ℝ) * x)).toNat : ℤ) = round ((Qsel j : ℝ) * x) :=
    Int.toNat_of_nonneg hrnn
  unfold centerOf; exact_mod_cast htoNat

lemma round_centerOf_le_Qsel (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ) (hj : 1 ≤ j) :
    round ((Qsel j : ℝ) * x) ≤ Qsel j := by
  set y := (Qsel j : ℝ) * x with hydef
  have hQreal : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hyQ : y ≤ (Qsel j : ℝ) := by
    have := mul_le_mul_of_nonneg_left hx1 (le_of_lt hQreal); simpa using this
  have h1 : |y - (round y : ℝ)| ≤ |y - (Qsel j : ℝ)| := round_le y (Qsel j)
  have h2 : |y - (Qsel j : ℝ)| = (Qsel j : ℝ) - y := by
    rw [abs_of_nonpos (by linarith)]; ring
  rw [h2] at h1
  have h3 : (round y : ℝ) - y ≤ |y - (round y : ℝ)| := by
    rw [← neg_sub (y : ℝ) (round y : ℝ)]; exact neg_le_abs _
  have h4 : (round y : ℝ) ≤ (Qsel j : ℝ) := by linarith
  exact_mod_cast h4

lemma centerOf_lt_Qsel (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (J : ℕ) (hJ : 1 ≤ J) :
    centerOf x J < (Qsel J).toNat + 1 := by
  have hQpos : 0 < Qsel J := Qsel_pos J hJ
  have hrnn := round_centerOf_nonneg x hx0 J
  have hrle := round_centerOf_le_Qsel x hx0 hx1 J hJ
  have htoNatJ : ((Qsel J).toNat : ℤ) = Qsel J := Int.toNat_of_nonneg (le_of_lt hQpos)
  have hmono : ((round ((Qsel J : ℝ) * x)).toNat : ℤ) ≤ ((Qsel J).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hrnn, htoNatJ]; exact hrle
  unfold centerOf
  have hnat : (round ((Qsel J : ℝ) * x)).toNat ≤ (Qsel J).toNat := by exact_mod_cast hmono
  omega

/-! ## 3. 中心 ∈ 覆盖（假设 j·‖Q_j x‖≤t） -/

lemma centerOf_mem_interv (t : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx0 : 0 ≤ x)
    (j : ℕ) (hj : 1 ≤ j) (h : (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x) ≤ t) :
    x ∈ interv t j (centerOf x j) := by
  have hQ : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hdist : distToNearestInt ((Qsel j : ℝ) * x) =
      |(Qsel j : ℝ) * x - (centerOf x j : ℝ)| := by
    simp only [distToNearestInt]; rw [← cast_centerOf x hx0 j]
  have h1 : |(Qsel j : ℝ) * x - (centerOf x j : ℝ)| ≤ t / (j : ℝ) := by
    rw [← hdist]; exact (le_div_iff₀ hjpos).mpr (by rw [mul_comm]; exact h)
  have hkey : (Qsel j : ℝ) * x - (centerOf x j : ℝ)
      = (Qsel j : ℝ) * (x - (centerOf x j : ℝ) / (Qsel j : ℝ)) := by field_simp
  rw [hkey, abs_mul, abs_of_pos hQ] at h1
  have h2 : |x - (centerOf x j : ℝ) / (Qsel j : ℝ)| ≤ (t / (j : ℝ)) / (Qsel j : ℝ) :=
    (le_div_iff₀ hQ).mpr (by rw [mul_comm]; exact h1)
  have h3 : (t / (j : ℝ)) / (Qsel j : ℝ) = rad t j := by unfold rad; field_simp
  rw [h3] at h2
  have hle := abs_le.mp h2
  unfold interv; constructor <;> linarith [rad_nonneg t ht j]

lemma centerOf_branchCond (t : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx0 : 0 ≤ x)
    (J : ℕ) (hJ : 1 ≤ J) (n : ℕ)
    (h : ∀ m, ((J + m : ℕ) : ℝ) * distToNearestInt ((Qsel (J + m) : ℝ) * x) ≤ t) :
    branchCond t (J + n) (centerOf x (J + n)) (centerOf x (J + n + 1)) := by
  have hJn : 1 ≤ J + n := by omega
  have hJn1 : 1 ≤ J + n + 1 := by omega
  have h1 := centerOf_mem_interv t ht x hx0 (J + n) hJn (h n)
  have h2 := centerOf_mem_interv t ht x hx0 (J + n + 1) hJn1 (h (n + 1))
  unfold interv at h1 h2
  have h1' := mem_Icc.mp h1
  have h2' := mem_Icc.mp h2
  have ha : |((centerOf x (J + n) : ℝ) / (Qsel (J + n) : ℝ)) - x| ≤ rad t (J + n) := by
    rw [abs_le]; constructor <;> linarith [rad_nonneg t ht (J + n)]
  have hb : |x - ((centerOf x (J + n + 1) : ℝ) / (Qsel (J + n + 1) : ℝ))| ≤ rad t (J + n + 1) := by
    rw [abs_le]; constructor <;> linarith [rad_nonneg t ht (J + n + 1)]
  unfold branchCond
  calc |((centerOf x (J + n) : ℝ) / (Qsel (J + n) : ℝ))
          - ((centerOf x (J + n + 1) : ℝ) / (Qsel (J + n + 1) : ℝ))|
      ≤ |((centerOf x (J + n) : ℝ) / (Qsel (J + n) : ℝ)) - x|
          + |x - ((centerOf x (J + n + 1) : ℝ) / (Qsel (J + n + 1) : ℝ))| := abs_sub_le _ _ _
    _ ≤ rad t (J + n) + rad t (J + n + 1) := by linarith

lemma centerOf_mem_survSet (t : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (J : ℕ) (hJ : 1 ≤ J) (n : ℕ)
    (h : ∀ m, ((J + m : ℕ) : ℝ) * distToNearestInt ((Qsel (J + m) : ℝ) * x) ≤ t) :
    centerOf x (J + n) ∈ survSet t J n := by
  induction n with
  | zero =>
      have hJ0 : J + 0 = J := by omega
      have hmem : centerOf x J ∈ Finset.range ((Qsel J).toNat + 1) := by
        rw [Finset.mem_range]; exact centerOf_lt_Qsel x hx0 hx1 J hJ
      have h0 : survSet t J 0 = Finset.range ((Qsel J).toNat + 1) := rfl
      rw [h0, ← hJ0]; exact hmem
  | succ n ih =>
      rw [survSet_succ]
      have hJn1 : J + (n + 1) = J + n + 1 := by omega
      have hbranch := centerOf_branchCond t ht x hx0 J hJ n h
      have hin : centerOf x (J + n + 1) ∈ branchSet t (J + n) (centerOf x (J + n)) := by
        unfold branchSet; rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_range]; exact centerOf_lt_Qsel x hx0 hx1 (J + n + 1) (by omega)
        · exact hbranch
      rw [Finset.mem_biUnion]
      exact ⟨centerOf x (J + n), ih, by rw [hJn1]; exact hin⟩

/-! ## 4. 水平集尾部 ⊆ 覆盖 -/

def tailSet (t : ℝ) (J : ℕ) : Set ℝ :=
  {x | 0 ≤ x ∧ x ≤ 1 ∧ ∀ m, J ≤ m → apprSeq x m ≤ t}

lemma tailSet_cover (t : ℝ) (ht : 0 ≤ t) (J : ℕ) (hJ : 1 ≤ J) (n : ℕ) :
    tailSet t J ⊆ ⋃ k : (survSet t J n : Set ℕ), interv t (J + n) (k : ℕ) := by
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2.1
  have htail : ∀ m, J ≤ m → apprSeq x m ≤ t := hx.2.2
  have h : ∀ m, ((J + m : ℕ) : ℝ) * distToNearestInt ((Qsel (J + m) : ℝ) * x) ≤ t := by
    intro m
    have hm : J ≤ J + m := by omega
    have := htail (J + m) hm
    simpa [apprSeq] using this
  have hmem := centerOf_mem_survSet t ht x hx0 hx1 J hJ n h
  have hinterv := centerOf_mem_interv t ht x hx0 (J + n) (by omega) (h n)
  refine Set.mem_iUnion.mpr ?_
  exact ⟨⟨centerOf x (J + n), hmem⟩, hinterv⟩

/-! ## 5. 内容估计 → 0 -/

lemma tendsto_powB_div_factorial_rpow (B : ℝ) (hB : 0 ≤ B) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => B ^ n / (Nat.factorial n : ℝ) ^ s) atTop (nhds 0) := by
  set c := B ^ (1 / s) with hcdef
  have h1 : Tendsto (fun n : ℕ => c ^ n / (Nat.factorial n : ℝ)) atTop (nhds 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop c
  have h2 : Tendsto (fun n : ℕ => (c ^ n / (Nat.factorial n : ℝ)) ^ s) atTop (nhds 0) :=
    h1.rpow_const_nhds_zero hs
  refine h2.congr' ?_
  refine Filter.Eventually.of_forall ?_
  intro n
  have hfactpos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hc : 0 ≤ c := by rw [hcdef]; exact Real.rpow_nonneg hB _
  have hstep1 : (c ^ n : ℝ) = B ^ ((n : ℝ) / s) := by
    calc (c ^ n : ℝ) = c ^ (n : ℝ) := by rw [← Real.rpow_natCast]
      _ = (B ^ (1 / s)) ^ (n : ℝ) := by rw [hcdef]
      _ = B ^ ((1 / s) * (n : ℝ)) := (Real.rpow_mul hB (1 / s) (n : ℝ)).symm
      _ = B ^ ((n : ℝ) / s) := by congr 1; field_simp
  have hstep2 : (c ^ n : ℝ) ^ s = B ^ n := by
    calc (c ^ n : ℝ) ^ s = (B ^ ((n : ℝ) / s)) ^ s := by rw [hstep1]
      _ = B ^ (((n : ℝ) / s) * s) := (Real.rpow_mul hB ((n : ℝ) / s) s).symm
      _ = B ^ (n : ℝ) := by congr 1; field_simp
      _ = B ^ n := by rw [Real.rpow_natCast]
  calc (c ^ n / (Nat.factorial n : ℝ)) ^ s
      = (c ^ n) ^ s / ((Nat.factorial n : ℝ) ^ s) :=
        Real.div_rpow (by positivity) (le_of_lt hfactpos) s
    _ = B ^ n / (Nat.factorial n : ℝ) ^ s := by rw [hstep2]

/-- rad t (J+n) ≤ t/((J+n)·(J+n)!)。 -/
lemma rad_le_factorial (t : ℝ) (ht : 0 ≤ t) (J n : ℕ) (hJn : 1 ≤ J + n) :
    rad t (J + n) ≤ t / (((J + n : ℕ) : ℝ) * (Nat.factorial (J + n) : ℝ)) := by
  have hQ : (Nat.factorial (J + n) : ℝ) ≤ (Qsel (J + n) : ℝ) := by
    exact_mod_cast Qsel_ge_factorial (J + n) hJn
  have hjpos : 0 < ((J + n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < J + n)
  have hfactpos : 0 < (Nat.factorial (J + n) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hdenpos : 0 < ((J + n : ℕ) : ℝ) * (Nat.factorial (J + n) : ℝ) := mul_pos hjpos hfactpos
  have hden : ((J + n : ℕ) : ℝ) * (Nat.factorial (J + n) : ℝ) ≤
      ((J + n : ℕ) : ℝ) * (Qsel (J + n) : ℝ) :=
    mul_le_mul_of_nonneg_left hQ (le_of_lt hjpos)
  unfold rad
  exact div_le_div_of_nonneg_left ht hdenpos hden

/-- 内容上界函数 → 0。 -/
lemma tendsto_contentBound (t : ℝ) (ht : 0 ≤ t) (J : ℕ) (hJ : 1 ≤ J) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => (((Qsel J).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ s *
        ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J + n) : ℝ) ^ s) atTop (nhds 0) := by
  have hB1 : 1 ≤ ((branchB t : ℕ) : ℝ) := by
    have := branchB_pos t; exact_mod_cast (by omega : 1 ≤ branchB t)
  have hkey := tendsto_powB_div_factorial_rpow ((branchB t : ℕ) : ℝ) (by positivity) s hs
  have hshift : Tendsto (fun n : ℕ => J + n) atTop atTop := by
    have h := tendsto_add_atTop_nat J
    exact h.congr (fun n => Nat.add_comm n J)
  have hcomp : Tendsto (fun n : ℕ => ((branchB t : ℕ) : ℝ) ^ (J + n) /
      (Nat.factorial (J + n) : ℝ) ^ s) atTop (nhds 0) := hkey.comp hshift
  have hle : ∀ n : ℕ, ((branchB t : ℕ) : ℝ) ^ n ≤ ((branchB t : ℕ) : ℝ) ^ (J + n) := by
    intro n; exact pow_le_pow_right₀ hB1 (by omega)
  have hfactpos : ∀ n : ℕ, 0 < (Nat.factorial (J + n) : ℝ) ^ s := by
    intro n; exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.factorial_pos _) _
  have hbound : ∀ n : ℕ, ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J + n) : ℝ) ^ s ≤
      ((branchB t : ℕ) : ℝ) ^ (J + n) / (Nat.factorial (J + n) : ℝ) ^ s := by
    intro n; exact div_le_div_of_nonneg_right (hle n) (le_of_lt (hfactpos n))
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have hnn : ∀ n : ℕ, 0 ≤ ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J + n) : ℝ) ^ s := by
    intro n; exact div_nonneg (by positivity) (le_of_lt (hfactpos n))
  have hsqueeze : Tendsto (fun n : ℕ => ((branchB t : ℕ) : ℝ) ^ n /
      (Nat.factorial (J + n) : ℝ) ^ s) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hzero hcomp
      (Filter.Eventually.of_forall hnn) (Filter.Eventually.of_forall hbound)
  have hC : Tendsto (fun n : ℕ => (((Qsel J).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ s *
      (((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J + n) : ℝ) ^ s)) atTop
      (nhds ((((Qsel J).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ s * 0)) :=
    hsqueeze.const_mul _
  have hmul0 : (((Qsel J).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ s * 0 = 0 := by ring
  rw [hmul0] at hC
  refine hC.congr' ?_
  refine Filter.Eventually.of_forall ?_
  intro n
  simp only
  rw [mul_div_assoc]

/-! ## 6. Hausdorff 对接 -/

lemma hausdorffMeasure_tailSet_zero (t : ℝ) (ht : 0 ≤ t) (J : ℕ) (hJ : 1 ≤ J)
    (s : ℝ) (hs : 0 < s) : μH[s] (tailSet t J) = 0 := by
  let ι : ℕ → Type _ := fun n => {k // k ∈ survSet t J n}
  let r : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (2 * rad t (J + n))
  let cov : ∀ n, ι n → Set ℝ := fun n k => interv t (J + n) k.1
  have hr : Tendsto r atTop (nhds 0) := by
    have hrad0 : Tendsto (fun n : ℕ => 2 * rad t (J + n)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => rad t (J + n)) atTop (nhds 0) := by
        have hle : ∀ n : ℕ, rad t (J + n) ≤ t / ((J + n : ℕ) : ℝ) := by
          intro n
          have hJn : 1 ≤ J + n := by omega
          have hQ1 : 1 ≤ (Qsel (J + n) : ℝ) := by exact_mod_cast Qsel_ge_one (J + n) hJn
          have hjpos : 0 < ((J + n : ℕ) : ℝ) := by positivity
          have hden : ((J + n : ℕ) : ℝ) * 1 ≤ ((J + n : ℕ) : ℝ) * (Qsel (J + n) : ℝ) :=
            mul_le_mul_of_nonneg_left hQ1 (le_of_lt hjpos)
          unfold rad
          have hstep : t / (((J + n : ℕ) : ℝ) * (Qsel (J + n) : ℝ)) ≤
              t / (((J + n : ℕ) : ℝ) * 1) :=
            div_le_div_of_nonneg_left ht (by simpa using hjpos) hden
          simpa using hstep
        have hnn : ∀ n : ℕ, 0 ≤ rad t (J + n) := by
          intro n; exact rad_nonneg t ht (J + n)
        have ht0 : Tendsto (fun n : ℕ => t / ((J + n : ℕ) : ℝ)) atTop (nhds 0) := by
          have hden : Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ)) atTop atTop := by
            have hshift : Tendsto (fun n : ℕ => J + n) atTop atTop :=
              (tendsto_add_atTop_nat J).congr (fun n => Nat.add_comm n J)
            exact tendsto_natCast_atTop_atTop.comp hshift
          exact tendsto_const_nhds.div_atTop hden
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht0
          (Filter.Eventually.of_forall hnn) (Filter.Eventually.of_forall hle)
      have h2 : Tendsto (fun n : ℕ => 2 * rad t (J + n)) atTop (nhds (2 * 0)) :=
        h1.const_mul 2
      simpa using h2
    have hof : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * rad t (J + n))) atTop
        (nhds (ENNReal.ofReal 0)) := ENNReal.tendsto_ofReal hrad0
    simpa [r] using hof
  have ht_diam : ∀ᶠ n in atTop, ∀ k : ι n, Metric.ediam (cov n k) ≤ r n := by
    refine Filter.Eventually.of_forall ?_
    intro n k
    exact ediam_interv_le t ht (J + n) k.1
  have hst : ∀ᶠ n in atTop, tailSet t J ⊆ ⋃ k : ι n, cov n k := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hcov := tailSet_cover t ht J hJ n
    intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨⟨k.1, k.2⟩, hk⟩
  have hmain := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum s (tailSet t J) r hr cov ht_diam hst
  -- 内容界（实数域）
  have hcontent : ∀ n : ℕ, ((survSet t J n).card : ℝ) * (2 * rad t (J + n)) ^ s ≤
      (((Qsel J).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ s *
        ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J + n) : ℝ) ^ s := by
    intro n
    have hcard : (survSet t J n).card ≤ ((Qsel J).toNat + 1) * (branchB t) ^ n :=
      card_survSet_le t ht J hJ n
    have hcardR : ((survSet t J n).card : ℝ) ≤
        (((Qsel J).toNat + 1 : ℕ) : ℝ) * ((branchB t : ℕ) : ℝ) ^ n := by
      exact_mod_cast hcard
    have hJn : 1 ≤ J + n := by omega
    have hfactpos : 0 < (Nat.factorial (J + n) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hradnn : 0 ≤ 2 * rad t (J + n) := by
      exact mul_nonneg (by norm_num) (rad_nonneg t ht (J + n))
    have hradle : 2 * rad t (J + n) ≤
        (2 * t) / (((J + n : ℕ) : ℝ) * (Nat.factorial (J + n) : ℝ)) := by
      calc 2 * rad t (J + n)
          ≤ 2 * (t / (((J + n : ℕ) : ℝ) * (Nat.factorial (J + n) : ℝ))) := by
            gcongr; exact rad_le_factorial t ht J n hJn
        _ = (2 * t) / (((J + n : ℕ) : ℝ) * (Nat.factorial (J + n) : ℝ)) := by ring
    have hradle2 : 2 * rad t (J + n) ≤ (2 * t) / (Nat.factorial (J + n) : ℝ) := by
      have hm1 : 1 ≤ ((J + n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ J + n)
      have hden2 : (Nat.factorial (J + n) : ℝ) ≤
          ((J + n : ℕ) : ℝ) * (Nat.factorial (J + n) : ℝ) := by nlinarith
      calc 2 * rad t (J + n)
          ≤ (2 * t) / (((J + n : ℕ) : ℝ) * (Nat.factorial (J + n) : ℝ)) := hradle
        _ ≤ (2 * t) / (Nat.factorial (J + n) : ℝ) :=
          div_le_div_of_nonneg_left (by linarith) (by positivity) hden2
    have hpow : (2 * rad t (J + n)) ^ s ≤
        (2 * t) ^ s / (Nat.factorial (J + n) : ℝ) ^ s := by
      calc (2 * rad t (J + n)) ^ s
          ≤ ((2 * t) / (Nat.factorial (J + n) : ℝ)) ^ s :=
            Real.rpow_le_rpow hradnn hradle2 (le_of_lt hs)
        _ = (2 * t) ^ s / (Nat.factorial (J + n) : ℝ) ^ s :=
          Real.div_rpow (by linarith) (le_of_lt hfactpos) s
    calc ((survSet t J n).card : ℝ) * (2 * rad t (J + n)) ^ s
        ≤ ((((Qsel J).toNat + 1 : ℕ) : ℝ) * ((branchB t : ℕ) : ℝ) ^ n) *
          ((2 * t) ^ s / (Nat.factorial (J + n) : ℝ) ^ s) := by
          gcongr
      _ = (((Qsel J).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ s *
          ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J + n) : ℝ) ^ s := by
          field_simp
  -- 求和界（ENNReal）
  have hsum_le : ∀ n : ℕ, ∑ k : ι n, Metric.ediam (cov n k) ^ s ≤
      ENNReal.ofReal ((((Qsel J).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ s *
        ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J + n) : ℝ) ^ s) := by
    intro n
    have h1 : ∑ k : ι n, Metric.ediam (cov n k) ^ s ≤
        ((survSet t J n).card : ℝ≥0∞) * ENNReal.ofReal (2 * rad t (J + n)) ^ s := by
      calc ∑ k : ι n, Metric.ediam (cov n k) ^ s
          = ∑ k ∈ survSet t J n, Metric.ediam (interv t (J + n) k) ^ s := by
            change ∑ k : {k // k ∈ survSet t J n},
              Metric.ediam (interv t (J + n) k.1) ^ s = _
            apply Eq.symm
            apply Finset.sum_bij (fun (k : ℕ) _ => (⟨k, by assumption⟩ : {k // k ∈ survSet t J n}))
            · intro k hk; exact Finset.mem_univ _
            · intro k₁ _ k₂ _ h; exact Subtype.mk.inj h
            · intro k hk; exact ⟨k.1, k.2, rfl⟩
            · intro k _; rfl
        _ ≤ ∑ k ∈ survSet t J n, ENNReal.ofReal (2 * rad t (J + n)) ^ s := by
            apply Finset.sum_le_sum; intro k _
            exact ENNReal.rpow_le_rpow (ediam_interv_le t ht (J + n) k) (le_of_lt hs)
        _ = ((survSet t J n).card : ℝ≥0∞) * ENNReal.ofReal (2 * rad t (J + n)) ^ s := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ((survSet t J n).card : ℝ≥0∞) * ENNReal.ofReal (2 * rad t (J + n)) ^ s =
        ENNReal.ofReal (((survSet t J n).card : ℝ) * (2 * rad t (J + n)) ^ s) := by
      have hcast : ((survSet t J n).card : ℝ≥0∞) =
          ENNReal.ofReal ((survSet t J n).card : ℝ) := by simp
      rw [hcast, ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (by norm_num) (rad_nonneg t ht (J + n))) (le_of_lt hs),
        ENNReal.ofReal_mul (by positivity)]
    have h3 : ENNReal.ofReal (((survSet t J n).card : ℝ) * (2 * rad t (J + n)) ^ s) ≤
        ENNReal.ofReal ((((Qsel J).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ s *
          ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J + n) : ℝ) ^ s) :=
      ENNReal.ofReal_le_ofReal (hcontent n)
    exact le_trans h1 (le_of_eq h2 |>.trans h3)
  have hlim : Filter.liminf (fun n => ∑ k : ι n, Metric.ediam (cov n k) ^ s) atTop ≤ 0 := by
    have hbound0 : Tendsto (fun n : ℕ => ENNReal.ofReal
        ((((Qsel J).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ s *
          ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J + n) : ℝ) ^ s)) atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal (tendsto_contentBound t ht J hJ s hs)
    have hle' : ∀ᶠ n in atTop, (∑ k : ι n, Metric.ediam (cov n k) ^ s : ℝ≥0∞) ≤
        ENNReal.ofReal ((((Qsel J).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ s *
          ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J + n) : ℝ) ^ s) :=
      Filter.Eventually.of_forall hsum_le
    have hlimsup0 : Filter.limsup (fun n => ∑ k : ι n, Metric.ediam (cov n k) ^ s) atTop ≤ 0 := by
      have hmono := Filter.limsup_le_limsup hle'
      have heq := hbound0.limsup_eq
      rw [heq] at hmono
      exact hmono
    exact le_trans Filter.liminf_le_limsup hlimsup0
  have hnonneg : 0 ≤ Filter.liminf (fun n => ∑ k : ι n, Metric.ediam (cov n k) ^ s) atTop :=
    bot_le
  have hlim0 : Filter.liminf (fun n => ∑ k : ι n, Metric.ediam (cov n k) ^ s) atTop = 0 :=
    le_antisymm hlim hnonneg
  rw [hlim0] at hmain
  exact le_antisymm hmain bot_le

lemma dimH_tailSet_zero (t : ℝ) (ht : 0 ≤ t) (J : ℕ) (hJ : 1 ≤ J) :
    dimH (tailSet t J) = 0 := by
  apply le_antisymm _ bot_le
  rw [dimH_eq_iInf]
  by_contra hne
  have hpos : 0 < ⨅ (d : ℝ≥0) (_ : μH[d] (tailSet t J) = 0), (d : ℝ≥0∞) :=
    not_le.mp hne
  obtain ⟨r, hr0, hrlt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr0
  have hr2 : 0 < (r : ℝ) / 2 := by positivity
  have hmu : μH[(r : ℝ) / 2] (tailSet t J) = 0 :=
    hausdorffMeasure_tailSet_zero t ht J hJ ((r : ℝ) / 2) hr2
  have hle : (⨅ (d : ℝ≥0) (_ : μH[d] (tailSet t J) = 0), (d : ℝ≥0∞)) ≤
      ((r / 2 : ℝ≥0) : ℝ≥0∞) := by
    apply iInf₂_le (⟨(r : ℝ) / 2, le_of_lt hr2⟩ : ℝ≥0)
    show μH[(⟨(r : ℝ) / 2, le_of_lt hr2⟩ : ℝ≥0)] (tailSet t J) = 0
    exact hmu
  have hlt : ((r / 2 : ℝ≥0) : ℝ≥0∞) < (r : ℝ≥0∞) := by
    exact_mod_cast (by linarith : (r : ℝ) / 2 < (r : ℝ))
  exact (not_le.mpr (lt_of_lt_of_le hrlt hle)) (le_of_lt hlt)

/-! ## 7. 周期性：dist(Q_j(x+m)) = dist(Q_j x)（m : Z） -/

lemma distToNearestInt_add_intCast (x : ℝ) (m : ℤ) :
    distToNearestInt (x + m) = distToNearestInt x := by
  unfold distToNearestInt
  have hr : round (x + m) = round x + m := round_add_intCast x m
  rw [hr]
  push_cast
  ring_nf

lemma apprSeq_add_intCast (x : ℝ) (m : ℤ) (j : ℕ) :
    apprSeq (x + m) j = apprSeq x j := by
  unfold apprSeq
  have hcast : (Qsel j : ℝ) * (x + m) = (Qsel j : ℝ) * x + (Qsel j * m : ℤ) := by
    push_cast; ring
  rw [hcast, distToNearestInt_add_intCast]

lemma apprSeqE_add_intCast (x : ℝ) (m : ℤ) (j : ℕ) :
    apprSeqE (x + m) j = apprSeqE x j := by
  unfold apprSeqE
  rw [apprSeq_add_intCast]

lemma apprExponent_add_intCast (x : ℝ) (m : ℤ) :
    apprExponent (x + m) = apprExponent x := by
  unfold apprExponent
  congr 1
  funext j
  exact apprSeqE_add_intCast x m j

/-! ## 8. 水平集 ⊆ tailSet 的可数并（J ≥ 1） -/

lemma levelSet_subset_iUnion_tailSet (c t : ℝ) (hc0 : 0 ≤ c) (hct : c < t) :
    levelSet (ENNReal.ofReal c) ⊆
      ⋃ (J : {J : ℕ // 1 ≤ J}) (m : ℤ), (fun y : ℝ => y + (m : ℝ)) '' tailSet t J.1 := by
  intro x hx
  have hxlim : apprExponent x ≤ ENNReal.ofReal c := hx
  have hctE : ENNReal.ofReal c < ENNReal.ofReal t :=
    (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hc0 hct)).mpr hct
  have hlt : apprExponent x < ENNReal.ofReal t := lt_of_le_of_lt hxlim hctE
  have hev : ∀ᶠ j : ℕ in atTop, apprSeqE x j < ENNReal.ofReal t :=
    eventually_lt_of_limsup_lt hlt
  have ht0 : 0 < t := lt_of_le_of_lt hc0 hct
  have hev' : ∀ᶠ j : ℕ in atTop, apprSeq x j ≤ t := by
    filter_upwards [hev] with j hj
    have := (ENNReal.ofReal_lt_ofReal_iff ht0).mp hj
    exact le_of_lt this
  obtain ⟨J0, hJ0⟩ := (Filter.eventually_atTop.mp hev')
  set J := max 1 J0 with hJdef
  have hJ1 : 1 ≤ J := le_max_left _ _
  have hJ : ∀ j, J ≤ j → apprSeq x j ≤ t := by
    intro j hj
    exact hJ0 j (le_trans (le_max_right _ _) hj)
  set m := ⌊x⌋ with hmdef
  set y := x - (m : ℝ) with hydef
  have hy0 : 0 ≤ y := by
    have := Int.floor_le x
    linarith
  have hy1 : y ≤ 1 := by
    have := Int.lt_floor_add_one x
    linarith
  have hym : x = y + (m : ℝ) := by linarith
  have htail : ∀ j, J ≤ j → apprSeq y j ≤ t := by
    intro j hj
    have := hJ j hj
    rw [hym, apprSeq_add_intCast] at this
    exact this
  have hytail : y ∈ tailSet t J := ⟨hy0, hy1, htail⟩
  refine Set.mem_iUnion.mpr ⟨⟨J, hJ1⟩, ?_⟩
  refine Set.mem_iUnion.mpr ⟨m, ?_⟩
  exact ⟨y, hytail, by linarith⟩

/-! ## 9. T-finite：dimH{Lam ≤ c} = 0 对一切实数 c（仅基础公理）

    证明只用覆盖论证：先单调归约到 c' = max c 0 ≥ 0，取 t = c'+1 > c'，
    水平集 ⊆ 可数个 tailSet t J（J ≥ 1）的整数平移像；每个 tailSet 维数零
    （存活中心 Finset 递归 + 一致分支界 + 阶乘增长压过分支数 + Hausdorff 判据），
    Lipschitz 平移与可数并保持维数零。不依赖 deltaSel 公理、不依赖分类定理。 -/

theorem dimH_levelSet_finite (c : ℝ) :
    dimH (levelSet (ENNReal.ofReal c)) = 0 := by
  set c' := max c 0 with hc'def
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hmono0 : levelSet (ENNReal.ofReal c) ⊆ levelSet (ENNReal.ofReal c') := by
    intro x hx
    exact le_trans hx (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  set t := c' + 1 with htdef
  have hct : c' < t := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hsub := Set.Subset.trans hmono0 (levelSet_subset_iUnion_tailSet c' t hc'0 hct)
  have hdim : dimH (⋃ (J : {J : ℕ // 1 ≤ J}) (m : ℤ),
      (fun y : ℝ => y + (m : ℝ)) '' tailSet t J.1) = 0 := by
    have h1 : ∀ J : {J : ℕ // 1 ≤ J},
        dimH (⋃ m : ℤ, (fun y : ℝ => y + (m : ℝ)) '' tailSet t J.1) = 0 := by
      intro J
      have hJ : 1 ≤ J.1 := J.2
      have h2 : ∀ m : ℤ, dimH ((fun y : ℝ => y + (m : ℝ)) '' tailSet t J.1) = 0 := by
        intro m
        have hlip : LipschitzWith 1 (fun y : ℝ => y + (m : ℝ)) := by
          apply LipschitzWith.of_dist_le_mul
          intro y₁ y₂
          simp only [dist_eq_norm, NNReal.coe_one, one_mul]
          have hshift : (y₁ + (m : ℝ)) - (y₂ + (m : ℝ)) = y₁ - y₂ := by ring
          rw [hshift]
        have := hlip.dimH_image_le (tailSet t J.1)
        rw [dimH_tailSet_zero t ht0 J.1 hJ] at this
        exact le_antisymm this bot_le
      have h3 : dimH (⋃ m : ℤ, (fun y : ℝ => y + (m : ℝ)) '' tailSet t J.1) ≤
          ⨆ m : ℤ, dimH ((fun y : ℝ => y + (m : ℝ)) '' tailSet t J.1) := by
        rw [dimH_iUnion]
      have h4 : (⨆ m : ℤ, dimH ((fun y : ℝ => y + (m : ℝ)) '' tailSet t J.1)) = 0 := by
        apply iSup_eq_bot.mpr
        intro m
        exact h2 m
      rw [h4] at h3
      exact le_antisymm h3 bot_le
    have h6 : dimH (⋃ (J : {J : ℕ // 1 ≤ J}) (m : ℤ),
        (fun y : ℝ => y + (m : ℝ)) '' tailSet t J.1) ≤
        ⨆ J : {J : ℕ // 1 ≤ J}, dimH (⋃ m : ℤ, (fun y : ℝ => y + (m : ℝ)) '' tailSet t J.1) := by
      rw [dimH_iUnion]
    have h7 : (⨆ J : {J : ℕ // 1 ≤ J},
        dimH (⋃ m : ℤ, (fun y : ℝ => y + (m : ℝ)) '' tailSet t J.1)) = 0 := by
      apply iSup_eq_bot.mpr
      intro J
      exact h1 J
    rw [h7] at h6
    exact le_antisymm h6 bot_le
  have hmono := dimH_mono hsub
  rw [hdim] at hmono
  exact le_antisymm hmono bot_le

end

end DimHFinite

#print axioms DimHFinite.centerOf_mem_survSet
#print axioms DimHFinite.tailSet_cover
#print axioms DimHFinite.tendsto_contentBound
#print axioms DimHFinite.hausdorffMeasure_tailSet_zero
#print axioms DimHFinite.dimH_tailSet_zero
