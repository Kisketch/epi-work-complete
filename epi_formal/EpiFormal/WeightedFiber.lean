import Mathlib
import EpiFormal.DimHCore
import EpiFormal.WeightedPhase

open Real Filter Topology Set DimHCore

namespace WeightedFiber

noncomputable section

/-- 加权半径 wrad t α j = t / (j^α · Q_j)。 -/
def wrad (t α : ℝ) (j : ℕ) : ℝ := t / ((j : ℝ) ^ α * (Qsel j : ℝ))

lemma wrad_nonneg (t α : ℝ) (ht : 0 ≤ t) (j : ℕ) : 0 ≤ wrad t α j := by
  unfold wrad
  apply div_nonneg ht
  apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) α)
  by_cases hj : 1 ≤ j
  · exact le_of_lt (by exact_mod_cast Qsel_pos j hj)
  · have : j = 0 := by omega
    subst this; simp [Qsel_zero]

/-- 关键幂不等式：j ≤ j^α · (j+1)^{1−α}（0≤α≤1，j≥1）。 -/
lemma pow_cross (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (j : ℕ) (hj : 1 ≤ j) :
    (j : ℝ) ≤ (j : ℝ) ^ α * ((j + 1 : ℕ) : ℝ) ^ (1 - α) := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have h1α : 0 ≤ 1 - α := by linarith
  have hjle : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j ≤ j + 1)
  have hpow_mono : (j : ℝ) ^ (1 - α) ≤ ((j + 1 : ℕ) : ℝ) ^ (1 - α) :=
    Real.rpow_le_rpow (le_of_lt hjpos) hjle h1α
  calc (j : ℝ) = (j : ℝ) ^ α * (j : ℝ) ^ (1 - α) := by
        rw [← Real.rpow_add hjpos]
        have : α + (1 - α) = 1 := by ring
        rw [this, Real.rpow_one]
    _ ≤ (j : ℝ) ^ α * ((j + 1 : ℕ) : ℝ) ^ (1 - α) :=
        mul_le_mul_of_nonneg_left hpow_mono (Real.rpow_nonneg (le_of_lt hjpos) α)

/-- 加权半径被 rad t' 控制（t' = t·(j+1)^{1−α}），逐点。 -/
lemma wrad_le_rad (t α : ℝ) (ht : 0 ≤ t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (j : ℕ) (hj : 1 ≤ j) :
    wrad t α j + wrad t α (j + 1) ≤
      DimHCore.rad (t * ((j + 1 : ℕ) : ℝ) ^ (1 - α)) j +
        DimHCore.rad (t * ((j + 1 : ℕ) : ℝ) ^ (1 - α)) (j + 1) := by
  set t' := t * ((j + 1 : ℕ) : ℝ) ^ (1 - α) with ht'def
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hj1pos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hQj : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hQj1 : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hjαpos : (0 : ℝ) < (j : ℝ) ^ α := Real.rpow_pos_of_pos hjpos α
  have hj1αpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) ^ α := Real.rpow_pos_of_pos hj1pos α
  have hcross := pow_cross α hα0 hα1 j hj
  -- 第一项：wrad t α j ≤ rad t' j
  have h1 : wrad t α j ≤ DimHCore.rad t' j := by
    unfold wrad DimHCore.rad
    rw [div_le_div_iff₀ (mul_pos hjαpos hQj) (mul_pos hjpos hQj)]
    have hkey : (j : ℝ) * (t * (Qsel j : ℝ)) ≤
        ((j : ℝ) ^ α * ((j + 1 : ℕ) : ℝ) ^ (1 - α)) * (t * (Qsel j : ℝ)) :=
      mul_le_mul_of_nonneg_right hcross (mul_nonneg ht (le_of_lt hQj))
    have ht'expand : t' = t * ((j + 1 : ℕ) : ℝ) ^ (1 - α) := ht'def
    nlinarith [hkey, ht'expand]
  -- 第二项：wrad t α (j+1) ≤ rad t' (j+1)（恰好相等化简）
  have h2 : wrad t α (j + 1) ≤ DimHCore.rad t' (j + 1) := by
    unfold wrad DimHCore.rad
    rw [div_le_div_iff₀ (mul_pos hj1αpos hQj1) (mul_pos hj1pos hQj1)]
    have hpow : ((j + 1 : ℕ) : ℝ) ^ α * ((j + 1 : ℕ) : ℝ) ^ (1 - α) = ((j + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_add hj1pos]
      have : α + (1 - α) = 1 := by ring
      rw [this, Real.rpow_one]
    have hprod : t' * (((j + 1 : ℕ) : ℝ) ^ α * (Qsel (j + 1) : ℝ)) =
        t * (((j + 1 : ℕ) : ℝ) * (Qsel (j + 1) : ℝ)) := by
      rw [ht'def]
      have hre : (t * ((j + 1 : ℕ) : ℝ) ^ (1 - α)) *
          (((j + 1 : ℕ) : ℝ) ^ α * (Qsel (j + 1) : ℝ)) =
          t * (((j + 1 : ℕ) : ℝ) ^ (1 - α) * ((j + 1 : ℕ) : ℝ) ^ α) * (Qsel (j + 1) : ℝ) := by ring
      rw [hre, mul_comm (((j + 1 : ℕ) : ℝ) ^ (1 - α)) (((j + 1 : ℕ) : ℝ) ^ α), hpow]
      ring
    linarith [hprod]
  linarith [h1, h2]

/-- **加权分支上界**：子中心数 ≤ branchB(t·(j+1)^{1−α}) = ⌊16t(j+1)^{1−α}⌋+1。
    由 wrad ≤ rad t' 的 filter 单调性 + 已验证 fiber_card_le。 -/
lemma fiber_card_weighted_le (t α : ℝ) (ht : 0 ≤ t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (j : ℕ) (hj : 1 ≤ j) (c : ℕ) :
    ((Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun (k' : ℕ) =>
      |(c : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤
        wrad t α j + wrad t α (j + 1))).card ≤
      DimHCore.branchB (t * ((j + 1 : ℕ) : ℝ) ^ (1 - α)) := by
  classical
  set t' := t * ((j + 1 : ℕ) : ℝ) ^ (1 - α) with ht'def
  have ht' : 0 ≤ t' :=
    mul_nonneg ht (Real.rpow_nonneg (by positivity) (1 - α))
  have hmono := wrad_le_rad t α ht hα0 hα1 j hj
  have hsub :
      ((Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun (k' : ℕ) =>
        |(c : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤
          wrad t α j + wrad t α (j + 1))) ⊆
      ((Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun (k' : ℕ) =>
        |(c : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤
          DimHCore.rad t' j + DimHCore.rad t' (j + 1))) := by
    intro k' hk'
    simp only [Finset.mem_filter] at hk' ⊢
    exact ⟨hk'.1, le_trans hk'.2 hmono⟩
  exact (Finset.card_le_card hsub).trans (DimHCore.fiber_card_le t' ht' j hj c)

end

end WeightedFiber

#print axioms WeightedFiber.pow_cross
#print axioms WeightedFiber.wrad_le_rad
#print axioms WeightedFiber.fiber_card_weighted_le
