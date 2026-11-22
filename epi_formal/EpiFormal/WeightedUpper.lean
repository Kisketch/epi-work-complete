import Mathlib
import EpiFormal.WeightedDimHCore
import EpiFormal.SpectralGap
import EpiFormal.DimHFinite

open Real Filter Topology Set Polynomial Finset MeasureTheory intervalIntegral DimHCore WeightedFiber WeightedDimH SpectralGap
open scoped Interval ENNReal NNReal

namespace WeightedUpper

noncomputable section

/-- 加权逼近序列 j^α‖Q_j x‖。 -/
def apprSeqα (α : ℝ) (x : ℝ) (j : ℕ) : ℝ := (j : ℝ) ^ α * distToNearestInt ((Qsel j : ℝ) * x)
def apprSeqαE (α : ℝ) (x : ℝ) (j : ℕ) : ℝ≥0∞ := ENNReal.ofReal (apprSeqα α x j)
def apprExponentα (α : ℝ) (x : ℝ) : ℝ≥0∞ := limsup (apprSeqαE α x) atTop
def levelSetα (α : ℝ) (c : ℝ≥0∞) : Set ℝ := {x | apprExponentα α x ≤ c}

/-- 中心 round(Q_j x).toNat。 -/
def centerOf (x : ℝ) (j : ℕ) : ℕ := (round ((Qsel j : ℝ) * x)).toNat

lemma Qsel_real_nonneg (j : ℕ) : 0 ≤ (Qsel j : ℝ) := by
  rcases j with _ | k
  · simp [Qsel_zero]
  · exact le_of_lt (by exact_mod_cast Qsel_pos (k + 1) (by omega))

lemma round_centerOf_nonneg (x : ℝ) (hx : 0 ≤ x) (j : ℕ) : 0 ≤ round ((Qsel j : ℝ) * x) := by
  set y := (Qsel j : ℝ) * x
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
  have hto : ((round ((Qsel j : ℝ) * x)).toNat : ℤ) = round ((Qsel j : ℝ) * x) := Int.toNat_of_nonneg hrnn
  unfold centerOf; exact_mod_cast hto

lemma round_centerOf_le_Qsel (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ) (hj : 1 ≤ j) :
    round ((Qsel j : ℝ) * x) ≤ Qsel j := by
  set y := (Qsel j : ℝ) * x
  have hQreal : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hyQ : y ≤ (Qsel j : ℝ) := by
    have := mul_le_mul_of_nonneg_left hx1 (le_of_lt hQreal); simpa using this
  have h1 : |y - (round y : ℝ)| ≤ |y - (Qsel j : ℝ)| := round_le y (Qsel j)
  have h2 : |y - (Qsel j : ℝ)| = (Qsel j : ℝ) - y := by rw [abs_of_nonpos (by linarith)]; ring
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
  have htoJ : ((Qsel J).toNat : ℤ) = Qsel J := Int.toNat_of_nonneg (le_of_lt hQpos)
  have hmono : ((round ((Qsel J : ℝ) * x)).toNat : ℤ) ≤ ((Qsel J).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hrnn, htoJ]; exact hrle
  unfold centerOf
  have hnat : (round ((Qsel J : ℝ) * x)).toNat ≤ (Qsel J).toNat := by exact_mod_cast hmono
  omega

/-- 加权中心成员：j^α‖Q_j x‖≤t ⇒ x∈winterv t α j (centerOf x j)。 -/
lemma centerOf_mem_winterv (t α : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx0 : 0 ≤ x)
    (j : ℕ) (hj : 1 ≤ j) (h : (j : ℝ) ^ α * distToNearestInt ((Qsel j : ℝ) * x) ≤ t) :
    x ∈ winterv t α j (centerOf x j) := by
  have hQ : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hjα : 0 < (j : ℝ) ^ α := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < j)) α
  have hdist : distToNearestInt ((Qsel j : ℝ) * x) = |(Qsel j : ℝ) * x - (centerOf x j : ℝ)| := by
    simp only [distToNearestInt]; rw [← cast_centerOf x hx0 j]
  have h1 : |(Qsel j : ℝ) * x - (centerOf x j : ℝ)| ≤ t / (j : ℝ) ^ α := by
    rw [← hdist]; exact (le_div_iff₀ hjα).mpr (by rw [mul_comm]; exact h)
  have hkey : (Qsel j : ℝ) * x - (centerOf x j : ℝ) =
      (Qsel j : ℝ) * (x - (centerOf x j : ℝ) / (Qsel j : ℝ)) := by field_simp
  rw [hkey, abs_mul, abs_of_pos hQ] at h1
  have h2 : |x - (centerOf x j : ℝ) / (Qsel j : ℝ)| ≤ (t / (j : ℝ) ^ α) / (Qsel j : ℝ) :=
    (le_div_iff₀ hQ).mpr (by rw [mul_comm]; exact h1)
  have h3 : (t / (j : ℝ) ^ α) / (Qsel j : ℝ) = wrad t α j := by unfold wrad; field_simp
  rw [h3] at h2
  have hle := abs_le.mp h2
  unfold winterv; constructor <;> linarith [wrad_nonneg t α ht j]

lemma centerOf_wbranchCond (t α : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx0 : 0 ≤ x)
    (J : ℕ) (hJ : 1 ≤ J) (n : ℕ)
    (h : ∀ m, ((J + m : ℕ) : ℝ) ^ α * distToNearestInt ((Qsel (J + m) : ℝ) * x) ≤ t) :
    |(centerOf x (J + n) : ℝ) / (Qsel (J + n) : ℝ) - (centerOf x (J + n + 1) : ℝ) / (Qsel (J + n + 1) : ℝ)|
      ≤ wrad t α (J + n) + wrad t α (J + n + 1) := by
  have h1 := centerOf_mem_winterv t α ht x hx0 (J + n) (by omega) (h n)
  have h2 := centerOf_mem_winterv t α ht x hx0 (J + n + 1) (by omega) (h (n + 1))
  unfold winterv at h1 h2
  have h1' := mem_Icc.mp h1
  have h2' := mem_Icc.mp h2
  have ha : |(centerOf x (J + n) : ℝ) / (Qsel (J + n) : ℝ) - x| ≤ wrad t α (J + n) := by
    rw [abs_le]; constructor <;> linarith [wrad_nonneg t α ht (J + n)]
  have hb : |x - (centerOf x (J + n + 1) : ℝ) / (Qsel (J + n + 1) : ℝ)| ≤ wrad t α (J + n + 1) := by
    rw [abs_le]; constructor <;> linarith [wrad_nonneg t α ht (J + n + 1)]
  calc _ ≤ |(centerOf x (J + n) : ℝ) / (Qsel (J + n) : ℝ) - x| +
        |x - (centerOf x (J + n + 1) : ℝ) / (Qsel (J + n + 1) : ℝ)| := abs_sub_le _ _ _
    _ ≤ wrad t α (J + n) + wrad t α (J + n + 1) := by linarith

lemma centerOf_mem_wsurvSet (t α : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (J : ℕ) (hJ : 1 ≤ J) (n : ℕ)
    (h : ∀ m, ((J + m : ℕ) : ℝ) ^ α * distToNearestInt ((Qsel (J + m) : ℝ) * x) ≤ t) :
    centerOf x (J + n) ∈ wsurvSet t α J n := by
  induction n with
  | zero =>
      have hJ0 : J + 0 = J := by omega
      have hmem : centerOf x J ∈ Finset.range ((Qsel J).toNat + 1) := by
        rw [Finset.mem_range]; exact centerOf_lt_Qsel x hx0 hx1 J hJ
      have h0 : wsurvSet t α J 0 = Finset.range ((Qsel J).toNat + 1) := rfl
      rw [h0, ← hJ0]; exact hmem
  | succ n ih =>
      rw [wsurvSet_succ]
      have hJn1 : J + (n + 1) = J + n + 1 := by omega
      have hbranch := centerOf_wbranchCond t α ht x hx0 J hJ n h
      have hin : centerOf x (J + n + 1) ∈ wbranchSet t α (J + n) (centerOf x (J + n)) := by
        unfold wbranchSet; rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_range]; exact centerOf_lt_Qsel x hx0 hx1 (J + n + 1) (by omega)
        · exact hbranch
      rw [Finset.mem_biUnion]
      exact ⟨centerOf x (J + n), ih, by rw [hJn1]; exact hin⟩

/-- 加权尾部集。 -/
def wtailSet (t α : ℝ) (J : ℕ) : Set ℝ :=
  {x | 0 ≤ x ∧ x ≤ 1 ∧ ∀ m, J ≤ m → apprSeqα α x m ≤ t}

lemma wtailSet_cover (t α : ℝ) (ht : 0 ≤ t) (J : ℕ) (hJ : 1 ≤ J) (n : ℕ) :
    wtailSet t α J ⊆ ⋃ k : (wsurvSet t α J n : Set ℕ), winterv t α (J + n) (k : ℕ) := by
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2.1
  have htail : ∀ m, J ≤ m → apprSeqα α x m ≤ t := hx.2.2
  have h : ∀ m, ((J + m : ℕ) : ℝ) ^ α * distToNearestInt ((Qsel (J + m) : ℝ) * x) ≤ t := by
    intro m
    have := htail (J + m) (by omega)
    simpa [apprSeqα] using this
  have hmem := centerOf_mem_wsurvSet t α ht x hx0 hx1 J hJ n h
  have hinterv := centerOf_mem_winterv t α ht x hx0 (J + n) (by omega) (h n)
  refine Set.mem_iUnion.mpr ?_
  exact ⟨⟨centerOf x (J + n), hmem⟩, hinterv⟩

/-- wrad t α (J+n) ≤ t/(J+n)!（j^α≥1, Q_j≥j!）。 -/
lemma wrad_le_fact (t α : ℝ) (ht : 0 ≤ t) (hα0 : 0 ≤ α) (J n : ℕ) (hJn : 1 ≤ J + n) :
    wrad t α (J + n) ≤ t / (Nat.factorial (J + n) : ℝ) := by
  have hjα : (1 : ℝ) ≤ ((J + n : ℕ) : ℝ) ^ α :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ J + n)) hα0
  have hQ : (Nat.factorial (J + n) : ℝ) ≤ (Qsel (J + n) : ℝ) := by
    exact_mod_cast DimHCore.Qsel_ge_factorial (J + n) hJn
  have hfactpos : 0 < (Nat.factorial (J + n) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  unfold wrad
  calc t / (((J + n : ℕ) : ℝ) ^ α * (Qsel (J + n) : ℝ))
      ≤ t / (1 * (Nat.factorial (J + n) : ℝ)) := by
        apply div_le_div_of_nonneg_left ht (by positivity)
        nlinarith [hjα, hQ, hfactpos]
    _ = t / (Nat.factorial (J + n) : ℝ) := by ring

/-- 内容界：card·(2wrad)^s ≤ C0·(2t)^s·K^n·((J+n)!)^{1−α−s}。 -/
lemma wcontent_bound (t α s : ℝ) (ht : 0 ≤ t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 0 < s)
    (J : ℕ) (hJ : 1 ≤ J) (n : ℕ) :
    ((wsurvSet t α J n).card : ℝ) * (2 * wrad t α (J + n)) ^ s ≤
      ((Qsel J).toNat + 1 : ℝ) * (2 * t) ^ s * (16 * t + 1) ^ n *
        (Nat.factorial (J + n) : ℝ) ^ (1 - α - s) := by
  have hcard := card_wsurvSet_le t α ht hα0 hα1 J hJ n
  have hJn : 1 ≤ J + n := by omega
  have hwr := wrad_le_fact t α ht hα0 J n hJn
  have hfactpos : 0 < (Nat.factorial (J + n) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h2wr : 0 ≤ 2 * wrad t α (J + n) := by
    apply mul_nonneg (by norm_num) (wrad_nonneg t α ht (J + n))
  have hpow : (2 * wrad t α (J + n)) ^ s ≤ (2 * t / (Nat.factorial (J + n) : ℝ)) ^ s := by
    apply Real.rpow_le_rpow h2wr _ (le_of_lt hs)
    calc 2 * wrad t α (J + n) ≤ 2 * (t / (Nat.factorial (J + n) : ℝ)) := by gcongr
      _ = 2 * t / (Nat.factorial (J + n) : ℝ) := by ring
  have hdiv : (2 * t / (Nat.factorial (J + n) : ℝ)) ^ s =
      (2 * t) ^ s / (Nat.factorial (J + n) : ℝ) ^ s :=
    Real.div_rpow (by linarith) (le_of_lt hfactpos) s
  have hcardnn : 0 ≤ ((wsurvSet t α J n).card : ℝ) := by positivity
  calc ((wsurvSet t α J n).card : ℝ) * (2 * wrad t α (J + n)) ^ s
      ≤ ((wsurvSet t α J n).card : ℝ) * ((2 * t) ^ s / (Nat.factorial (J + n) : ℝ) ^ s) := by
        gcongr
        rw [← hdiv]; exact hpow
    _ ≤ (((Qsel J).toNat + 1 : ℝ) * (16 * t + 1) ^ n * (Nat.factorial (J + n) : ℝ) ^ (1 - α)) *
        ((2 * t) ^ s / (Nat.factorial (J + n) : ℝ) ^ s) := by gcongr
    _ = ((Qsel J).toNat + 1 : ℝ) * (2 * t) ^ s * (16 * t + 1) ^ n *
        ((Nat.factorial (J + n) : ℝ) ^ (1 - α) / (Nat.factorial (J + n) : ℝ) ^ s) := by
        field_simp
    _ = ((Qsel J).toNat + 1 : ℝ) * (2 * t) ^ s * (16 * t + 1) ^ n *
        (Nat.factorial (J + n) : ℝ) ^ (1 - α - s) := by
        have hr : (Nat.factorial (J + n) : ℝ) ^ (1 - α) / (Nat.factorial (J + n) : ℝ) ^ s =
            (Nat.factorial (J + n) : ℝ) ^ (1 - α - s) := by
          rw [← Real.rpow_sub hfactpos]
        rw [hr]

/-- 内容 →0（s>1−α）。 -/
lemma wcontent_tendsto (t α s : ℝ) (ht : 0 ≤ t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : 1 - α < s)
    (J : ℕ) (hJ : 1 ≤ J) :
    Tendsto (fun n => ((wsurvSet t α J n).card : ℝ) * (2 * wrad t α (J + n)) ^ s) atTop (nhds 0) := by
  have hs0 : 0 < s := by linarith
  have hbound := wcontent_bound t α s ht hα0 hα1 hs0 J hJ
  -- C0(2t)^s·K^n·(J+n)!^{1−α−s} →0
  have hcore := WeightedPhase.content_core_tendsto (16 * t + 1) (by linarith) α s hs
  have hshift : Tendsto (fun n : ℕ => J + n) atTop atTop :=
    (tendsto_add_atTop_nat J).congr (fun n => Nat.add_comm n J)
  have hcomp : Tendsto (fun n => (16 * t + 1) ^ (J + n) * (Nat.factorial (J + n) : ℝ) ^ (1 - α - s))
      atTop (nhds 0) := hcore.comp hshift
  have hK1 : (1 : ℝ) ≤ 16 * t + 1 := by linarith
  have hle_pow : ∀ n, (16 * t + 1 : ℝ) ^ n ≤ (16 * t + 1) ^ (J + n) :=
    fun n => pow_le_pow_right₀ hK1 (by omega)
  have hfactpos : ∀ n, 0 < (Nat.factorial (J + n) : ℝ) ^ (1 - α - s) :=
    fun n => Real.rpow_pos_of_pos (by exact_mod_cast Nat.factorial_pos _) _
  have hprod_le : ∀ n, (16 * t + 1 : ℝ) ^ n * (Nat.factorial (J + n) : ℝ) ^ (1 - α - s) ≤
      (16 * t + 1) ^ (J + n) * (Nat.factorial (J + n) : ℝ) ^ (1 - α - s) :=
    fun n => mul_le_mul_of_nonneg_right (hle_pow n) (le_of_lt (hfactpos n))
  have hprod_nn : ∀ n, 0 ≤ (16 * t + 1 : ℝ) ^ n * (Nat.factorial (J + n) : ℝ) ^ (1 - α - s) :=
    fun n => mul_nonneg (pow_nonneg (by linarith) n) (le_of_lt (hfactpos n))
  have hprod0 : Tendsto (fun n => (16 * t + 1 : ℝ) ^ n * (Nat.factorial (J + n) : ℝ) ^ (1 - α - s))
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomp
      (Filter.Eventually.of_forall hprod_nn) (Filter.Eventually.of_forall hprod_le)
  have hC : Tendsto (fun n => ((Qsel J).toNat + 1 : ℝ) * (2 * t) ^ s *
      ((16 * t + 1 : ℝ) ^ n * (Nat.factorial (J + n) : ℝ) ^ (1 - α - s))) atTop
      (nhds (((Qsel J).toNat + 1 : ℝ) * (2 * t) ^ s * 0)) := hprod0.const_mul _
  have h0 : ((Qsel J).toNat + 1 : ℝ) * (2 * t) ^ s * 0 = 0 := by ring
  rw [h0] at hC
  have hnn : ∀ n, 0 ≤ ((wsurvSet t α J n).card : ℝ) * (2 * wrad t α (J + n)) ^ s :=
    fun n => mul_nonneg (by positivity) (Real.rpow_nonneg (by
      apply mul_nonneg (by norm_num) (wrad_nonneg t α ht (J + n))) s)
  have hbound' : ∀ n, ((wsurvSet t α J n).card : ℝ) * (2 * wrad t α (J + n)) ^ s ≤
      ((Qsel J).toNat + 1 : ℝ) * (2 * t) ^ s * ((16 * t + 1) ^ n * (Nat.factorial (J + n) : ℝ) ^ (1 - α - s)) := by
    intro n
    have := hbound n
    have heq : ((Qsel J).toNat + 1 : ℝ) * (2 * t) ^ s * (16 * t + 1) ^ n * (Nat.factorial (J + n) : ℝ) ^ (1 - α - s) =
        ((Qsel J).toNat + 1 : ℝ) * (2 * t) ^ s * ((16 * t + 1) ^ n * (Nat.factorial (J + n) : ℝ) ^ (1 - α - s)) := by ring
    linarith [heq]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
    (Filter.Eventually.of_forall hnn) (Filter.Eventually.of_forall hbound')

/-- Hausdorff 测度零。 -/
lemma hausdorffMeasure_wtailSet_zero (t α s : ℝ) (ht : 0 ≤ t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hs : 1 - α < s) (J : ℕ) (hJ : 1 ≤ J) : μH[s] (wtailSet t α J) = 0 := by
  let ι : ℕ → Type _ := fun n => {k // k ∈ wsurvSet t α J n}
  let r : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (2 * wrad t α (J + n))
  let cov : ∀ n, ι n → Set ℝ := fun n k => winterv t α (J + n) k.1
  have hr : Tendsto r atTop (nhds 0) := by
    have hw : Tendsto (fun n => wrad t α (J + n)) atTop (nhds 0) := by
      have hle : ∀ n, wrad t α (J + n) ≤ t / (Nat.factorial (J + n) : ℝ) :=
        fun n => wrad_le_fact t α ht hα0 J n (by omega)
      have hnn : ∀ n, 0 ≤ wrad t α (J + n) := fun n => wrad_nonneg t α ht (J + n)
      have hf : Tendsto (fun n => t / (Nat.factorial (J + n) : ℝ)) atTop (nhds 0) := by
        have hden : Tendsto (fun n => (Nat.factorial (J + n) : ℝ)) atTop atTop := by
          have hfact_nat : Tendsto (fun n => Nat.factorial (J + n)) atTop atTop := by
            rw [Filter.tendsto_atTop_atTop]
            intro b
            obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp factorial_tendsto_atTop b
            exact ⟨N, fun n hn => hN (J + n) (by omega)⟩
          exact tendsto_natCast_atTop_atTop.comp hfact_nat
        exact tendsto_const_nhds.div_atTop hden
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hf
        (Filter.Eventually.of_forall hnn) (Filter.Eventually.of_forall hle)
    have h2 : Tendsto (fun n => 2 * wrad t α (J + n)) atTop (nhds 0) := by
      have := hw.const_mul 2; simpa using this
    have hof := ENNReal.tendsto_ofReal h2
    simpa [r] using hof
  have ht_diam : ∀ᶠ n in atTop, ∀ k : ι n, Metric.ediam (cov n k) ≤ r n :=
    Filter.Eventually.of_forall (fun n k => ediam_winterv_le t α ht (J + n) k.1)
  have hst : ∀ᶠ n in atTop, wtailSet t α J ⊆ ⋃ k : ι n, cov n k := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hcov := wtailSet_cover t α ht J hJ n
    intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨⟨k.1, k.2⟩, hk⟩
  have hmain := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum s (wtailSet t α J) r hr cov ht_diam hst
  have hsum_le : ∀ n, ∑ k : ι n, Metric.ediam (cov n k) ^ s ≤
      ENNReal.ofReal (((wsurvSet t α J n).card : ℝ) * (2 * wrad t α (J + n)) ^ s) := by
    intro n
    calc ∑ k : ι n, Metric.ediam (cov n k) ^ s
        = ∑ k ∈ wsurvSet t α J n, Metric.ediam (winterv t α (J + n) k) ^ s := by
          change ∑ k : {k // k ∈ wsurvSet t α J n}, Metric.ediam (winterv t α (J + n) k.1) ^ s = _
          apply Eq.symm
          apply Finset.sum_bij (fun (k : ℕ) _ => (⟨k, by assumption⟩ : {k // k ∈ wsurvSet t α J n}))
          · intro k hk; exact Finset.mem_univ _
          · intro k₁ _ k₂ _ h; exact Subtype.mk.inj h
          · intro k hk; exact ⟨k.1, k.2, rfl⟩
          · intro k _; rfl
      _ ≤ ∑ k ∈ wsurvSet t α J n, ENNReal.ofReal (2 * wrad t α (J + n)) ^ s := by
          apply Finset.sum_le_sum; intro k _
          exact ENNReal.rpow_le_rpow (ediam_winterv_le t α ht (J + n) k) (by linarith)
      _ = ((wsurvSet t α J n).card : ℝ≥0∞) * ENNReal.ofReal (2 * wrad t α (J + n)) ^ s := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (((wsurvSet t α J n).card : ℝ) * (2 * wrad t α (J + n)) ^ s) := by
          have hcast : ((wsurvSet t α J n).card : ℝ≥0∞) = ENNReal.ofReal ((wsurvSet t α J n).card : ℝ) := by simp
          rw [hcast, ENNReal.ofReal_rpow_of_nonneg
            (mul_nonneg (by norm_num) (wrad_nonneg t α ht (J + n))) (by linarith),
            ENNReal.ofReal_mul (by positivity)]
  have hlim : Filter.liminf (fun n => ∑ k : ι n, Metric.ediam (cov n k) ^ s) atTop ≤ 0 := by
    have hbound0 : Tendsto (fun n => ENNReal.ofReal (((wsurvSet t α J n).card : ℝ) *
        (2 * wrad t α (J + n)) ^ s)) atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal (wcontent_tendsto t α s ht hα0 hα1 hs J hJ)
    have hle' : ∀ᶠ n in atTop, (∑ k : ι n, Metric.ediam (cov n k) ^ s : ℝ≥0∞) ≤
        ENNReal.ofReal (((wsurvSet t α J n).card : ℝ) * (2 * wrad t α (J + n)) ^ s) :=
      Filter.Eventually.of_forall hsum_le
    have hlimsup0 : Filter.limsup (fun n => ∑ k : ι n, Metric.ediam (cov n k) ^ s) atTop ≤ 0 := by
      have hmono := Filter.limsup_le_limsup hle'
      have heq := hbound0.limsup_eq
      rw [heq] at hmono; exact hmono
    exact le_trans Filter.liminf_le_limsup hlimsup0
  have hlim0 : Filter.liminf (fun n => ∑ k : ι n, Metric.ediam (cov n k) ^ s) atTop = 0 :=
    le_antisymm hlim bot_le
  rw [hlim0] at hmain
  exact le_antisymm hmain bot_le

/-- **加权上界**：dimH(wtailSet) ≤ 1−α。 -/
lemma dimH_wtailSet_le (t α : ℝ) (ht : 0 ≤ t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (J : ℕ) (hJ : 1 ≤ J) : dimH (wtailSet t α J) ≤ ENNReal.ofReal (1 - α) := by
  rw [dimH_eq_iInf]
  by_contra hne
  have hgt : ENNReal.ofReal (1 - α) < ⨅ (d : ℝ≥0) (_ : μH[d] (wtailSet t α J) = 0), (d : ℝ≥0∞) :=
    not_le.mp hne
  -- iInf ≤ 1（因 μH[2]=0，2>1−α），故 iInf < ⊤，可取实数 r∈(1−α, iInf)
  have hmu2 : μH[(2 : ℝ)] (wtailSet t α J) = 0 :=
    hausdorffMeasure_wtailSet_zero t α 2 ht hα0 hα1 (by linarith) J hJ
  have hle1 : (⨅ (d : ℝ≥0) (_ : μH[d] (wtailSet t α J) = 0), (d : ℝ≥0∞)) ≤ (2 : ℝ≥0∞) :=
    iInf₂_le (2 : ℝ≥0) hmu2
  have hiInf_ne_top : (⨅ (d : ℝ≥0) (_ : μH[d] (wtailSet t α J) = 0), (d : ℝ≥0∞)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hle1 (by norm_num))
  set iR := (⨅ (d : ℝ≥0) (_ : μH[d] (wtailSet t α J) = 0), (d : ℝ≥0∞)).toReal with hiRdef
  have hgtR : 1 - α < iR := by
    have h1 : (ENNReal.ofReal (1 - α)).toReal = 1 - α := ENNReal.toReal_ofReal (sub_nonneg.mpr hα1)
    have h2 := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hiInf_ne_top).mpr hgt
    rw [h1] at h2
    simpa [iR] using h2
  obtain ⟨rR, hr_gt, hr_lt⟩ := exists_between hgtR
  have hr0 : 0 < rR := by linarith [sub_nonneg.mpr hα1]
  set s := (1 - α + rR) / 2 with hsdef
  have hs : 1 - α < s := by linarith
  have hs0 : 0 < s := by linarith [sub_nonneg.mpr hα1]
  have hmu : μH[s] (wtailSet t α J) = 0 := hausdorffMeasure_wtailSet_zero t α s ht hα0 hα1 hs J hJ
  set d0 : ℝ≥0 := NNReal.mk s (le_of_lt hs0) with hd0def
  have hmu' : μH[(d0 : ℝ)] (wtailSet t α J) = 0 := by
    have : (d0 : ℝ) = s := rfl
    rw [this]; exact hmu
  have hle : (⨅ (d : ℝ≥0) (_ : μH[d] (wtailSet t α J) = 0), (d : ℝ≥0∞)) ≤ (d0 : ℝ≥0∞) :=
    iInf₂_le d0 hmu'
  have hlt : (d0 : ℝ≥0∞) < (ENNReal.ofReal rR) := by
    have hd0 : (d0 : ℝ≥0∞) = ENNReal.ofReal s := by
      rw [hd0def]
      simp only [ENNReal.ofReal]
      congr 1
      exact (Real.toNNReal_of_nonneg (le_of_lt hs0)).symm
    rw [hd0]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).mpr (by linarith)
  have hr_lt_iInf : ENNReal.ofReal rR < ⨅ (d : ℝ≥0) (_ : μH[d] (wtailSet t α J) = 0), (d : ℝ≥0∞) := by
    have hiRpos : 0 < iR := by linarith [sub_nonneg.mpr hα1]
    have hstep := (ENNReal.ofReal_lt_ofReal_iff hiRpos).mpr hr_lt
    have hiR_coe : ENNReal.ofReal iR = ⨅ (d : ℝ≥0) (_ : μH[d] (wtailSet t α J) = 0), (d : ℝ≥0∞) := by
      rw [hiRdef]; exact ENNReal.ofReal_toReal hiInf_ne_top
    rwa [hiR_coe] at hstep
  exact (not_le.mpr (lt_of_lt_of_le hr_lt_iInf hle)) (le_of_lt hlt)

end

end WeightedUpper

#print axioms WeightedUpper.centerOf_mem_wsurvSet
#print axioms WeightedUpper.wtailSet_cover
#print axioms WeightedUpper.wcontent_tendsto
#print axioms WeightedUpper.hausdorffMeasure_wtailSet_zero
#print axioms WeightedUpper.dimH_wtailSet_le
