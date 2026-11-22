import Mathlib
import EpiFormal.WeightedFiber

open Real Filter Topology Set Polynomial Finset DimHCore WeightedFiber

namespace WeightedLower

noncomputable section

/-- 分支区间端点（加权）。 -/
def wA (t α : ℝ) (j : ℕ) (c : ℕ) : ℝ :=
  (Qsel (j + 1) : ℝ) * ((c : ℝ) / (Qsel j : ℝ) - (wrad t α j + wrad t α (j + 1)))
def wB (t α : ℝ) (j : ℕ) (c : ℕ) : ℝ :=
  (Qsel (j + 1) : ℝ) * ((c : ℝ) / (Qsel j : ℝ) + (wrad t α j + wrad t α (j + 1)))

lemma wB_sub_wA (t α : ℝ) (j : ℕ) (c : ℕ) :
    wB t α j c - wA t α j c = 2 * (wrad t α j + wrad t α (j + 1)) * (Qsel (j + 1) : ℝ) := by
  simp only [wA, wB]; ring

/-- 分支宽度下界：B−A ≥ 8t·j^{1−α}（用 Q_{j+1}≥4jQ_j）。 -/
lemma width_ge (t α : ℝ) (ht : 0 ≤ t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (j : ℕ) (hj : 1 ≤ j) (c : ℕ) :
    8 * t * (j : ℝ) ^ (1 - α) ≤ wB t α j c - wA t α j c := by
  rw [wB_sub_wA]
  have hQj : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hrec := DimHCore.Qsel_rec1 j hj
  have hQprev0 : 0 ≤ Qsel (j - 1) := by
    by_cases hj1 : j = 1
    · subst hj1; simp only [Nat.sub_self]; norm_num [Qsel]
    · exact le_of_lt (Qsel_pos (j - 1) (by omega))
  have hfour : 4 * (j : ℤ) * Qsel j ≤ Qsel (j + 1) := by
    have hj0 : 0 ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
    have hQj0 : 0 ≤ Qsel j := by exact_mod_cast le_of_lt (Qsel_pos j hj)
    nlinarith
  have hfourR : (4 * (j : ℝ)) * (Qsel j : ℝ) ≤ (Qsel (j + 1) : ℝ) := by exact_mod_cast hfour
  have hjαpos : 0 < (j : ℝ) ^ α := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < j)) α
  have hw : t / ((j : ℝ) ^ α * (Qsel j : ℝ)) ≤ wrad t α j + wrad t α (j + 1) := by
    have := wrad_nonneg t α ht (j + 1)
    unfold wrad at *
    linarith
  have hQnext0 : 0 ≤ (Qsel (j + 1) : ℝ) := by exact_mod_cast le_of_lt (Qsel_pos (j + 1) (by omega))
  have hmain : 2 * (t / ((j : ℝ) ^ α * (Qsel j : ℝ))) * (Qsel (j + 1) : ℝ) ≤
      2 * (wrad t α j + wrad t α (j + 1)) * (Qsel (j + 1) : ℝ) := by
    gcongr
  have hcalc : 2 * (t / ((j : ℝ) ^ α * (Qsel j : ℝ))) * (Qsel (j + 1) : ℝ) ≥
      8 * t * (j : ℝ) ^ (1 - α) := by
    have h1 : 2 * (t / ((j : ℝ) ^ α * (Qsel j : ℝ))) * (Qsel (j + 1) : ℝ) ≥
        2 * (t / ((j : ℝ) ^ α * (Qsel j : ℝ))) * (4 * (j : ℝ) * (Qsel j : ℝ)) := by
      gcongr
    have h2 : 2 * (t / ((j : ℝ) ^ α * (Qsel j : ℝ))) * (4 * (j : ℝ) * (Qsel j : ℝ)) =
        8 * t * ((j : ℝ) / (j : ℝ) ^ α) := by
      field_simp; ring
    have h3 : (j : ℝ) / (j : ℝ) ^ α = (j : ℝ) ^ (1 - α) := by
      have hjpos : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
      calc (j : ℝ) / (j : ℝ) ^ α
          = (j : ℝ) ^ (1 : ℝ) / (j : ℝ) ^ α := by rw [Real.rpow_one]
        _ = (j : ℝ) ^ ((1 : ℝ) - α) := (Real.rpow_sub hjpos 1 α).symm
        _ = (j : ℝ) ^ (1 - α) := by norm_num
    rw [h3] at h2
    linarith
  linarith

/-- 条件等价于 A≤k'≤B。 -/
lemma cond_iff (t α : ℝ) (j : ℕ) (hj : 1 ≤ j) (c k' : ℕ) :
    |(c : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤ wrad t α j + wrad t α (j + 1) ↔
      wA t α j c ≤ (k' : ℝ) ∧ (k' : ℝ) ≤ wB t α j c := by
  have hQ : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  set Q := (Qsel (j + 1) : ℝ) with hQdef
  set R := wrad t α j + wrad t α (j + 1) with hRdef
  set u := (c : ℝ) / (Qsel j : ℝ) with hudef
  have hAu : wA t α j c = Q * (u - R) := by simp [wA, hQdef, hRdef, hudef]
  have hBu : wB t α j c = Q * (u + R) := by simp [wB, hQdef, hRdef, hudef]
  have hmul : Q * ((k' : ℝ) / Q) = (k' : ℝ) := by field_simp
  constructor
  · intro h
    have hl := abs_le.mp h
    have hl1 : u - R ≤ (k' : ℝ) / Q := by linarith [hl.1]
    have hl2 : (k' : ℝ) / Q ≤ u + R := by linarith [hl.2]
    constructor
    · have h1 : Q * (u - R) ≤ Q * ((k' : ℝ) / Q) := mul_le_mul_of_nonneg_left hl1 (le_of_lt hQ)
      rw [hmul] at h1; rw [hAu]; exact h1
    · have h1 : Q * ((k' : ℝ) / Q) ≤ Q * (u + R) := mul_le_mul_of_nonneg_left hl2 (le_of_lt hQ)
      rw [hmul] at h1; rw [hBu]; exact h1
  · rintro ⟨hA, hB⟩
    rw [hAu] at hA; rw [hBu] at hB
    have hA' : Q * (u - R) ≤ Q * ((k' : ℝ) / Q) := by rw [hmul]; exact hA
    have hB' : Q * ((k' : ℝ) / Q) ≤ Q * (u + R) := by rw [hmul]; exact hB
    have h1 : u - R ≤ (k' : ℝ) / Q := le_of_mul_le_mul_left hA' hQ
    have h2 : (k' : ℝ) / Q ≤ u + R := le_of_mul_le_mul_left hB' hQ
    rw [abs_le]
    exact ⟨by linarith [h1], by linarith [h2]⟩

/-- **分支下界**：内部父中心的孩子数 ≥ ⌊B−A⌋。 -/
lemma fiber_card_weighted_ge (t α : ℝ) (ht : 0 ≤ t) (j : ℕ) (hj : 1 ≤ j) (c : ℕ)
    (hA : 0 ≤ wA t α j c) (hB : wB t α j c ≤ (Qsel (j + 1) : ℝ)) :
    Nat.floor (wB t α j c - wA t α j c) ≤
      ((Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun (k' : ℕ) =>
        |(c : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤ wrad t α j + wrad t α (j + 1))).card := by
  classical
  set A := wA t α j c
  set B := wB t α j c
  set L := Nat.floor (B - A)
  -- 单射 m ↦ ceil(A)+m（m<L）进入 filter
  have hAB : A ≤ B := by
    have hR : 0 ≤ wrad t α j + wrad t α (j + 1) :=
      add_nonneg (wrad_nonneg t α ht j) (wrad_nonneg t α ht (j + 1))
    have hQ : 0 ≤ (Qsel (j + 1) : ℝ) := by exact_mod_cast le_of_lt (Qsel_pos (j + 1) (by omega))
    show (Qsel (j + 1) : ℝ) * ((c : ℝ) / (Qsel j : ℝ) - (wrad t α j + wrad t α (j + 1))) ≤
      (Qsel (j + 1) : ℝ) * ((c : ℝ) / (Qsel j : ℝ) + (wrad t α j + wrad t α (j + 1)))
    nlinarith
  set a0 := Nat.ceil A with ha0def
  have ha0A : A ≤ (a0 : ℝ) := Nat.le_ceil A
  have inj : ∀ m ∈ Finset.range L, a0 + m ∈
      (Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun (k' : ℕ) =>
        |(c : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤ wrad t α j + wrad t α (j + 1)) := by
    intro m hm
    have hmL : m < L := Finset.mem_range.mp hm
    have hmR : (m : ℝ) < (L : ℝ) := by exact_mod_cast hmL
    have hL : (L : ℝ) ≤ B - A := Nat.floor_le (by linarith)
    have hkA : A ≤ (a0 + m : ℝ) := by
      have : (a0 : ℝ) + (m : ℝ) ≥ A := by linarith [ha0A]
      exact_mod_cast this
    have hkB : (a0 + m : ℝ) ≤ B := by
      have hceil : (a0 : ℝ) < A + 1 := Nat.ceil_lt_add_one hA
      have hm1 : (m : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ L)
      have hsum : (a0 : ℝ) + (m : ℝ) + 1 < A + 1 + (B - A) := by linarith [hceil, hm1, hL]
      have hsimpl : A + 1 + (B - A) = B + 1 := by ring
      rw [hsimpl] at hsum
      have hle : (a0 : ℝ) + (m : ℝ) ≤ B := by linarith [hsum]
      exact_mod_cast hle
    have hkQ : (a0 + m : ℝ) ≤ (Qsel (j + 1) : ℝ) := by linarith [hB]
    have hk0 : 0 ≤ (a0 + m : ℝ) := by linarith [hA, ha0A]
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · have hcast : ((a0 + m : ℕ) : ℝ) ≤ (Qsel (j + 1) : ℝ) := by push_cast; linarith [hkQ]
      have hnat : a0 + m ≤ Qsel (j + 1) := by exact_mod_cast hcast
      omega
    · rw [cond_iff t α j hj c (a0 + m)]
      constructor
      · push_cast at hkA ⊢; exact hkA
      · push_cast at hkB ⊢; exact hkB
  have hinj : Set.InjOn (fun m => a0 + m) (Finset.range L : Set ℕ) := by
    intro m₁ _ m₂ _ h
    exact add_left_cancel h
  have hcard : (Finset.range L).card ≤
      ((Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun (k' : ℕ) =>
        |(c : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤ wrad t α j + wrad t α (j + 1))).card := by
    apply Finset.card_le_card_of_injOn (fun m => a0 + m)
    · intro m hm; exact inj m hm
    · exact hinj
  simpa using hcard

/-- **分支下界（标度形式）**：孩子数 ≥ ⌊8t·j^{1−α}⌋。 -/
lemma fiber_card_weighted_ge_scale (t α : ℝ) (ht : 0 ≤ t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (j : ℕ) (hj : 1 ≤ j) (c : ℕ)
    (hA : 0 ≤ wA t α j c) (hB : wB t α j c ≤ (Qsel (j + 1) : ℝ)) :
    Nat.floor (8 * t * (j : ℝ) ^ (1 - α)) ≤
      ((Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun (k' : ℕ) =>
        |(c : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤ wrad t α j + wrad t α (j + 1))).card := by
  have hw := width_ge t α ht hα0 hα1 j hj c
  have h1 := fiber_card_weighted_ge t α ht j hj c hA hB
  have hmono : Nat.floor (8 * t * (j : ℝ) ^ (1 - α)) ≤ Nat.floor (wB t α j c - wA t α j c) :=
    Nat.floor_mono hw
  exact le_trans hmono h1

end

end WeightedLower

#print axioms WeightedLower.width_ge
#print axioms WeightedLower.fiber_card_weighted_ge
#print axioms WeightedLower.fiber_card_weighted_ge_scale
