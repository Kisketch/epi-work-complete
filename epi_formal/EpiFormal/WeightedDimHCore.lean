import Mathlib
import EpiFormal.WeightedFiber

open Real Filter Topology Set Polynomial Finset DimHCore WeightedFiber

namespace WeightedDimH

noncomputable section

/-- 加权覆盖区间。 -/
def winterv (t α : ℝ) (j : ℕ) (k : ℕ) : Set ℝ :=
  Icc ((k : ℝ) / (Qsel j : ℝ) - wrad t α j) ((k : ℝ) / (Qsel j : ℝ) + wrad t α j)

lemma ediam_winterv_le (t α : ℝ) (ht : 0 ≤ t) (j k : ℕ) :
    Metric.ediam (winterv t α j k) ≤ ENNReal.ofReal (2 * wrad t α j) := by
  have hsub : ((k : ℝ) / (Qsel j : ℝ) + wrad t α j) - ((k : ℝ) / (Qsel j : ℝ) - wrad t α j) =
      2 * wrad t α j := by ring
  rw [winterv, Real.ediam_Icc, hsub]

/-- 加权分支集。 -/
def wbranchSet (t α : ℝ) (j k : ℕ) : Finset ℕ :=
  (Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun k' =>
    |(k : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤ wrad t α j + wrad t α (j + 1))

lemma card_wbranchSet_le (t α : ℝ) (ht : 0 ≤ t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (j : ℕ) (hj : 1 ≤ j) (k : ℕ) :
    (wbranchSet t α j k).card ≤ branchB (t * ((j + 1 : ℕ) : ℝ) ^ (1 - α)) := by
  classical
  have h := fiber_card_weighted_le t α ht hα0 hα1 j hj k
  have hsub : wbranchSet t α j k ⊆
      (Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun k' =>
        |(k : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤ wrad t α j + wrad t α (j + 1)) := by
    intro k' hk'; simp only [wbranchSet] at hk' ⊢; exact hk'
  exact (Finset.card_le_card hsub).trans h

/-- 加权存活中心递归。 -/
def wsurvSet (t α : ℝ) (J : ℕ) : ℕ → Finset ℕ
  | 0 => Finset.range ((Qsel J).toNat + 1)
  | n + 1 => (wsurvSet t α J n).biUnion (fun k => wbranchSet t α (J + n) k)

lemma wsurvSet_succ (t α : ℝ) (J n : ℕ) :
    wsurvSet t α J (n + 1) = (wsurvSet t α J n).biUnion (fun k => wbranchSet t α (J + n) k) := rfl

/-- 分支常数 K = 16t+1 的实数上界：branchB(t·x) ≤ K·x（x≥1）。 -/
lemma branchB_le_K (t : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx : 1 ≤ x) :
    (branchB (t * x) : ℝ) ≤ (16 * t + 1) * x := by
  have hfloor : (Nat.floor (16 * (t * x)) : ℝ) ≤ 16 * (t * x) := Nat.floor_le (by positivity)
  have h1 : (branchB (t * x) : ℝ) = (Nat.floor (16 * (t * x)) : ℝ) + 1 := by
    simp only [branchB, Nat.cast_add, Nat.cast_one]
  rw [h1]
  nlinarith [hfloor, hx, ht]

/-- **加权基数界**：card(wsurvSet n) ≤ C0·K^n·((J+n)!)^{1−α}。 -/
lemma card_wsurvSet_le (t α : ℝ) (ht : 0 ≤ t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (J : ℕ) (hJ : 1 ≤ J) (n : ℕ) :
    ((wsurvSet t α J n).card : ℝ) ≤
      ((Qsel J).toNat + 1 : ℝ) * (16 * t + 1) ^ n * (Nat.factorial (J + n) : ℝ) ^ (1 - α) := by
  induction n with
  | zero =>
      have h1 : wsurvSet t α J 0 = Finset.range ((Qsel J).toNat + 1) := rfl
      rw [h1, Finset.card_range]
      push_cast
      have hp : (1 : ℝ) ≤ (Nat.factorial J : ℝ) ^ (1 - α) := by
        apply Real.one_le_rpow
        · exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos J)
        · linarith
      have hK : (16 * t + 1 : ℝ) ^ 0 = 1 := pow_zero _
      rw [hK]
      have hC0 : (0 : ℝ) ≤ ((Qsel J).toNat + 1 : ℝ) := by positivity
      have hJ0 : J + 0 = J := by omega
      rw [hJ0]
      nlinarith [hp, hC0]
  | succ n ih =>
      have hJn : 1 ≤ J + n := by omega
      have hstep : ∀ k ∈ wsurvSet t α J n,
          (wbranchSet t α (J + n) k).card ≤ branchB (t * ((J + n + 1 : ℕ) : ℝ) ^ (1 - α)) := by
        intro k _
        exact card_wbranchSet_le t α ht hα0 hα1 (J + n) hJn k
      have hcard_nat : (wsurvSet t α J (n + 1)).card ≤
          (wsurvSet t α J n).card * branchB (t * ((J + n + 1 : ℕ) : ℝ) ^ (1 - α)) := by
        rw [wsurvSet_succ]
        exact Finset.card_biUnion_le_card_mul _ _ _ hstep
      have hcardR : ((wsurvSet t α J (n + 1)).card : ℝ) ≤
          ((wsurvSet t α J n).card : ℝ) * (branchB (t * ((J + n + 1 : ℕ) : ℝ) ^ (1 - α)) : ℝ) := by
        exact_mod_cast hcard_nat
      have hx : (1 : ℝ) ≤ ((J + n + 1 : ℕ) : ℝ) ^ (1 - α) := by
        apply Real.one_le_rpow
        · exact_mod_cast (by omega : 1 ≤ J + n + 1)
        · linarith
      have hB := branchB_le_K t ht (((J + n + 1 : ℕ) : ℝ) ^ (1 - α)) hx
      have hnn : 0 ≤ ((wsurvSet t α J n).card : ℝ) := by positivity
      calc ((wsurvSet t α J (n + 1)).card : ℝ)
          ≤ ((wsurvSet t α J n).card : ℝ) * (branchB (t * ((J + n + 1 : ℕ) : ℝ) ^ (1 - α)) : ℝ) := hcardR
        _ ≤ ((wsurvSet t α J n).card : ℝ) * ((16 * t + 1) * ((J + n + 1 : ℕ) : ℝ) ^ (1 - α)) := by
            gcongr
        _ ≤ (((Qsel J).toNat + 1 : ℝ) * (16 * t + 1) ^ n * (Nat.factorial (J + n) : ℝ) ^ (1 - α)) *
            ((16 * t + 1) * ((J + n + 1 : ℕ) : ℝ) ^ (1 - α)) := by gcongr
        _ = ((Qsel J).toNat + 1 : ℝ) * (16 * t + 1) ^ (n + 1) *
            ((Nat.factorial (J + n) : ℝ) * ((J + n + 1 : ℕ) : ℝ)) ^ (1 - α) := by
            have hmul : (Nat.factorial (J + n) : ℝ) ^ (1 - α) * ((J + n + 1 : ℕ) : ℝ) ^ (1 - α) =
                ((Nat.factorial (J + n) : ℝ) * ((J + n + 1 : ℕ) : ℝ)) ^ (1 - α) := by
              rw [← Real.mul_rpow (by positivity) (by positivity)]
            rw [pow_succ (16 * t + 1 : ℝ) n, ← hmul]
            ring
        _ = ((Qsel J).toNat + 1 : ℝ) * (16 * t + 1) ^ (n + 1) * (Nat.factorial (J + n + 1) : ℝ) ^ (1 - α) := by
            have hf : (Nat.factorial (J + n) : ℝ) * ((J + n + 1 : ℕ) : ℝ) =
                (Nat.factorial (J + n + 1) : ℝ) := by
              have hfs : Nat.factorial (J + n + 1) = (J + n + 1) * Nat.factorial (J + n) := by
                rw [Nat.factorial_succ]
              rw [hfs]; push_cast; ring
            rw [hf]

end

end WeightedDimH

#print axioms WeightedDimH.ediam_winterv_le
#print axioms WeightedDimH.card_wbranchSet_le
#print axioms WeightedDimH.card_wsurvSet_le
