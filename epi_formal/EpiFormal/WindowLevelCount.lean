import Mathlib

/-!
# 多层分支计数（paper2 §7 windows 质量界）

对应论文 L2536–2543：每层保留父柱分裂出众多子柱时，
第 J 层保留总数 `≥ ∏_{i<j} B i`（`B i` 为第 i 层每父分支数下界）。
质量界 `μ(I_J) ≤ ∏ B_i^{-1}` 由归一化计数直接得到（推论）。

本文件只做组合计数；分支数 `B i ≥ C_1 i^b` 的具体下界与
对数渐近比较留用方（需 `H_j` 增长 + Stirling/积分比较）。
-/

namespace WindowLevelCount

variable {α : Type} [DecidableEq α]

/-- 多层分支计数：每父至少 `B i` 个互不交子 ⇒ 第 J 层总数 `≥ ∏ B`. -/
theorem level_count_ge
    (C : ℕ → Finset α) (B : ℕ → ℕ) (child : ℕ → α → Finset α)
    (j0 J : ℕ) (hle : j0 ≤ J)
    (hne : (C j0).Nonempty)
    (hchild_mem : ∀ j a, a ∈ C j → child j a ⊆ C (j + 1))
    (hchild_card : ∀ j a, a ∈ C j → B j ≤ (child j a).card)
    (hdisj : ∀ j a₁, a₁ ∈ C j → ∀ a₂, a₂ ∈ C j → a₁ ≠ a₂ →
      Disjoint (child j a₁) (child j a₂)) :
    ∏ i ∈ Finset.Ico j0 J, B i ≤ (C J).card := by
  induction J, hle using Nat.le_induction with
  | base =>
    rw [Finset.Ico_self, Finset.prod_empty]
    exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hne)
  | succ J hle ih =>
    have hsub : (C J).biUnion (child J) ⊆ C (J + 1) := by
      intro x hx
      obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
      exact hchild_mem J a ha hxa
    have hcard_eq : ((C J).biUnion (child J)).card =
        ∑ a ∈ C J, (child J a).card := by
      apply Finset.card_biUnion
      intro x hx y hy hne
      exact hdisj J x hx y hy hne
    have hsum_ge : (C J).card * B J ≤ ((C J).biUnion (child J)).card := by
      rw [hcard_eq]
      have heq : (C J).card * B J = ∑ _a ∈ C J, B J := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      rw [heq]
      exact Finset.sum_le_sum (fun a ha => hchild_card J a ha)
    have hmono : ((C J).biUnion (child J)).card ≤ (C (J + 1)).card :=
      Finset.card_le_card hsub
    have hstep : (∏ i ∈ Finset.Ico j0 J, B i) * B J ≤ (C (J + 1)).card :=
      le_trans (Nat.mul_le_mul_right _ ih |>.trans hsum_ge) hmono
    have hexpand : ∏ i ∈ Finset.Ico j0 (J + 1), B i
        = (∏ i ∈ Finset.Ico j0 J, B i) * B J :=
      Finset.prod_Ico_succ_top (by omega : j0 ≤ J) B
    rw [hexpand]
    exact hstep

#print axioms WindowLevelCount.level_count_ge

end WindowLevelCount
