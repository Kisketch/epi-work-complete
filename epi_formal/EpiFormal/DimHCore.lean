import Mathlib
import EpiFormal.SpectralGap

open Real Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace DimHCore

noncomputable section

/-! ## 1. Q_j 阶乘级增长（覆盖论证基石） -/

lemma Qsel_succ_ge_mul (j : ℕ) (hj : 1 ≤ j) :
    ((j + 1 : ℕ) : ℤ) * Qsel j ≤ Qsel (j + 1) := by
  rcases j with _ | _ | k
  · omega
  · simp [Qsel_one, Qsel_two]
  · have hrec := Qsel_rec (k + 2) (by omega)
    have hpos : 0 ≤ Qsel (k + 1) := le_of_lt (Qsel_pos (k + 1) (by omega))
    have hcoef : ((k + 2 + 1 : ℕ) : ℤ) ≤ 4 * ((k + 2 : ℕ) : ℤ) + 2 := by
      push_cast; omega
    have hQpos : 0 ≤ Qsel (k + 2) := le_of_lt (Qsel_pos (k + 2) (by omega))
    calc ((k + 2 + 1 : ℕ) : ℤ) * Qsel (k + 2)
        ≤ (4 * ((k + 2 : ℕ) : ℤ) + 2) * Qsel (k + 2) := by
          exact mul_le_mul_of_nonneg_right hcoef hQpos
      _ ≤ (4 * ((k + 2 : ℕ) : ℤ) + 2) * Qsel (k + 2) + Qsel (k + 1) := by linarith
      _ = Qsel (k + 2 + 1) := by rw [hrec]; push_cast; ring

lemma Qsel_ge_factorial (j : ℕ) (hj : 1 ≤ j) : (Nat.factorial j : ℤ) ≤ Qsel j := by
  induction j, hj using Nat.le_induction with
  | base => simp [Qsel_one]
  | succ j hj ih =>
      have hmul := Qsel_succ_ge_mul j hj
      have hfact : (Nat.factorial (j + 1) : ℤ) = ((j + 1 : ℕ) : ℤ) * (Nat.factorial j : ℤ) := by
        push_cast [Nat.factorial_succ]; ring
      rw [hfact]
      have hjpos : 0 ≤ ((j + 1 : ℕ) : ℤ) := by positivity
      calc ((j + 1 : ℕ) : ℤ) * (Nat.factorial j : ℤ)
          ≤ ((j + 1 : ℕ) : ℤ) * Qsel j := mul_le_mul_of_nonneg_left ih hjpos
        _ ≤ Qsel (j + 1) := hmul

lemma Qsel_ge_one (j : ℕ) (hj : 1 ≤ j) : 1 ≤ Qsel j := by
  have := Qsel_ge_factorial j hj
  have hfact : 1 ≤ (Nat.factorial j : ℤ) := by exact_mod_cast Nat.factorial_pos j
  linarith

/-- j≥1 的递推（含 j=1，用 Qsel 0 = 1 闭合）。 -/
lemma Qsel_rec1 (j : ℕ) (hj : 1 ≤ j) :
    Qsel (j + 1) = (4 * (j : ℤ) + 2) * Qsel j + Qsel (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have h := selPair_rec 1 1 k
  simp only [Qsel] at h ⊢
  convert h using 1 <;> push_cast <;> ring

/-- Q_{j+1} ≤ (4j+3) Q_j（j≥1）。 -/
lemma Qsel_succ_le (j : ℕ) (hj : 1 ≤ j) : Qsel (j + 1) ≤ (4 * (j : ℤ) + 3) * Qsel j := by
  have hrec := Qsel_rec1 j hj
  have hprev : Qsel (j - 1) ≤ Qsel j := by
    by_cases hj1 : j = 1
    · subst hj1; simp [Qsel_zero, Qsel_one]
    · have hj2 : 2 ≤ j := by omega
      have hj1 : 1 ≤ j - 1 := by omega
      have hlt : Qsel (j - 1) < Qsel j :=
        Qsel_strictMono (Set.mem_Ici.mpr hj1) (Set.mem_Ici.mpr hj) (by omega)
      exact le_of_lt hlt
  have hQpos : 0 ≤ Qsel j := le_of_lt (Qsel_pos j hj)
  linarith

/-! ## 2. 分支常数与区间 -/

def branchB (t : ℝ) : ℕ := Nat.floor (16 * t) + 1

lemma branchB_pos (t : ℝ) : 0 < branchB t := Nat.succ_pos _

def rad (t : ℝ) (j : ℕ) : ℝ := t / ((j : ℝ) * (Qsel j : ℝ))

lemma rad_nonneg (t : ℝ) (ht : 0 ≤ t) (j : ℕ) : 0 ≤ rad t j := by
  unfold rad
  apply div_nonneg ht
  have hj : 0 ≤ (j : ℝ) := by positivity
  have hQ : 0 ≤ (Qsel j : ℝ) := by
    by_cases hj1 : 1 ≤ j
    · exact le_of_lt (by exact_mod_cast Qsel_pos j hj1)
    · have hj0 : j = 0 := by omega
      subst hj0; simp [Qsel_zero]
  nlinarith

/-- 固定父中心 c，满足分支条件的子中心 k' 个数 ≤ branchB t。
    证明：k' 落在长度 ≤ 16t 的实区间 [A,B]，映射 k'↦⌊k'−A⌋₊ 单射，像 ⊆ [0,⌊16t⌋]。 -/
lemma fiber_card_le (t : ℝ) (ht : 0 ≤ t) (j : ℕ) (hj : 1 ≤ j) (c : ℕ) :
    ((Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun (k' : ℕ) =>
      |(c : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤
        rad t j + rad t (j + 1))).card ≤ branchB t := by
  classical
  have hQj : 0 < Qsel j := Qsel_pos j hj
  have hQj1 : 0 < Qsel (j + 1) := Qsel_pos (j + 1) (by omega)
  have hQjR : 0 < (Qsel j : ℝ) := by exact_mod_cast hQj
  have hQj1R : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast hQj1
  have hjR : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  set R := rad t j + rad t (j + 1) with hRdef
  set A := (Qsel (j + 1) : ℝ) * ((c : ℝ) / (Qsel j : ℝ) - R) with hAdef
  set B := (Qsel (j + 1) : ℝ) * ((c : ℝ) / (Qsel j : ℝ) + R) with hBdef
  set S := (Finset.range ((Qsel (j + 1)).toNat + 1)).filter (fun (k' : ℕ) =>
      |(c : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤ R)
  have hAB : ∀ k' ∈ S, A ≤ (k' : ℝ) ∧ (k' : ℝ) ≤ B := by
    intro k' hk'
    have hdist : |(c : ℝ) / (Qsel j : ℝ) - (k' : ℝ) / (Qsel (j + 1) : ℝ)| ≤ R :=
      (Finset.mem_filter.mp hk').2
    have hle := abs_le.mp hdist
    constructor
    · have h1 : (c : ℝ) / (Qsel j : ℝ) - R ≤ (k' : ℝ) / (Qsel (j + 1) : ℝ) := by linarith
      have h2 : (Qsel (j + 1) : ℝ) * ((c : ℝ) / (Qsel j : ℝ) - R) ≤
          (Qsel (j + 1) : ℝ) * ((k' : ℝ) / (Qsel (j + 1) : ℝ)) := by gcongr
      have h3 : (Qsel (j + 1) : ℝ) * ((k' : ℝ) / (Qsel (j + 1) : ℝ)) = (k' : ℝ) := by field_simp
      linarith
    · have h1 : (k' : ℝ) / (Qsel (j + 1) : ℝ) ≤ (c : ℝ) / (Qsel j : ℝ) + R := by linarith
      have h2 : (Qsel (j + 1) : ℝ) * ((k' : ℝ) / (Qsel (j + 1) : ℝ)) ≤
          (Qsel (j + 1) : ℝ) * ((c : ℝ) / (Qsel j : ℝ) + R) := by gcongr
      have h3 : (Qsel (j + 1) : ℝ) * ((k' : ℝ) / (Qsel (j + 1) : ℝ)) = (k' : ℝ) := by field_simp
      linarith
  have hBA : B - A ≤ 16 * t := by
    have hBAeq : B - A = 2 * R * (Qsel (j + 1) : ℝ) := by simp only [A, B]; ring
    rw [hBAeq]
    have hRQ : R * (Qsel (j + 1) : ℝ) =
        t * (Qsel (j + 1) : ℝ) / ((j : ℝ) * (Qsel j : ℝ)) + t / ((j + 1 : ℕ) : ℝ) := by
      simp only [R, rad]; field_simp
    have hQle : (Qsel (j + 1) : ℝ) ≤ (4 * (j : ℝ) + 3) * (Qsel j : ℝ) := by
      have hleZ := Qsel_succ_le j hj
      have hcast : ((4 * (j : ℤ) + 3) * Qsel j : ℝ) = (4 * (j : ℝ) + 3) * (Qsel j : ℝ) := by
        push_cast; ring
      have hR : (Qsel (j + 1) : ℝ) ≤ ((4 * (j : ℤ) + 3) * Qsel j : ℝ) := by exact_mod_cast hleZ
      linarith [hcast]
    have hterm1 : t * (Qsel (j + 1) : ℝ) / ((j : ℝ) * (Qsel j : ℝ)) ≤ 7 * t := by
      have hden : 0 < (j : ℝ) * (Qsel j : ℝ) := mul_pos hjR hQjR
      rw [div_le_iff₀ hden]
      have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      have hfrac : (Qsel (j + 1) : ℝ) ≤ 7 * (j : ℝ) * (Qsel j : ℝ) := by
        have h4j3 : (4 * (j : ℝ) + 3) ≤ 7 * (j : ℝ) := by nlinarith
        calc (Qsel (j + 1) : ℝ) ≤ (4 * (j : ℝ) + 3) * (Qsel j : ℝ) := hQle
          _ ≤ (7 * (j : ℝ)) * (Qsel j : ℝ) := by gcongr
          _ = 7 * (j : ℝ) * (Qsel j : ℝ) := by ring
      have htQ : 0 ≤ t * (Qsel j : ℝ) := mul_nonneg ht (le_of_lt hQjR)
      nlinarith
    have hterm2 : t / ((j + 1 : ℕ) : ℝ) ≤ t := by
      have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
        have : 1 ≤ j + 1 := by omega
        exact_mod_cast this
      have := div_le_self ht h1
      simpa using this
    have hsum : R * (Qsel (j + 1) : ℝ) ≤ 8 * t := by rw [hRQ]; linarith
    nlinarith
  let g : ℕ → ℕ := fun k' => Nat.floor ((k' : ℝ) - A)
  have hg_inj : Set.InjOn g (S : Set ℕ) := by
    intro k1 hk1 k2 hk2 hgeq
    by_contra hne
    have hlt : k1 < k2 ∨ k2 < k1 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hA1 : A ≤ (k1 : ℝ) := (hAB k1 hk1).1
    have hA2 : A ≤ (k2 : ℝ) := (hAB k2 hk2).1
    have hnn1 : 0 ≤ (k1 : ℝ) - A := by linarith
    have hnn2 : 0 ≤ (k2 : ℝ) - A := by linarith
    have hf1 : (g k1 : ℝ) ≤ (k1 : ℝ) - A := Nat.floor_le hnn1
    have hf1' : (k1 : ℝ) - A < (g k1 : ℝ) + 1 := Nat.lt_floor_add_one _
    have hf2 : (g k2 : ℝ) ≤ (k2 : ℝ) - A := Nat.floor_le hnn2
    have hf2' : (k2 : ℝ) - A < (g k2 : ℝ) + 1 := Nat.lt_floor_add_one _
    have hgeqR : (g k1 : ℝ) = (g k2 : ℝ) := by exact_mod_cast hgeq
    rcases hlt with hlt | hlt
    · have hkR : (k1 : ℝ) + 1 ≤ (k2 : ℝ) := by
        have : k1 + 1 ≤ k2 := by omega
        exact_mod_cast this
      have hfloor : (g k1 : ℝ) + 1 ≤ (g k2 : ℝ) := by
        have h1 : (g k1 : ℝ) + 1 ≤ (k1 : ℝ) - A + 1 := by linarith [hf1']
        have h2 : (k1 : ℝ) - A + 1 ≤ (k2 : ℝ) - A := by linarith
        have h3 : (k2 : ℝ) - A < (g k2 : ℝ) + 1 := hf2'
        have h4 : (g k1 : ℝ) + 1 < (g k2 : ℝ) + 1 := by linarith
        have h5 : (g k1 : ℝ) < (g k2 : ℝ) := by linarith
        have h6 : g k1 < g k2 := by exact_mod_cast h5
        have h7 : g k1 + 1 ≤ g k2 := by omega
        exact_mod_cast h7
      linarith
    · have hkR : (k2 : ℝ) + 1 ≤ (k1 : ℝ) := by
        have : k2 + 1 ≤ k1 := by omega
        exact_mod_cast this
      have hfloor : (g k2 : ℝ) + 1 ≤ (g k1 : ℝ) := by
        have h1 : (g k2 : ℝ) + 1 ≤ (k2 : ℝ) - A + 1 := by linarith [hf2']
        have h2 : (k2 : ℝ) - A + 1 ≤ (k1 : ℝ) - A := by linarith
        have h3 : (k1 : ℝ) - A < (g k1 : ℝ) + 1 := hf1'
        have h4 : (g k2 : ℝ) + 1 < (g k1 : ℝ) + 1 := by linarith
        have h5 : (g k2 : ℝ) < (g k1 : ℝ) := by linarith
        have h6 : g k2 < g k1 := by exact_mod_cast h5
        have h7 : g k2 + 1 ≤ g k1 := by omega
        exact_mod_cast h7
      linarith
  have hg_range : ∀ k' ∈ S, g k' ≤ Nat.floor (16 * t) := by
    intro k' hk'
    have hBk : (k' : ℝ) ≤ B := (hAB k' hk').2
    have hAk : A ≤ (k' : ℝ) := (hAB k' hk').1
    have hsub : (k' : ℝ) - A ≤ B - A := by linarith
    have hle : (k' : ℝ) - A ≤ 16 * t := by linarith [hBA]
    have hnn : 0 ≤ (k' : ℝ) - A := by linarith
    exact Nat.floor_mono hle
  have hcard : S.card ≤ Nat.floor (16 * t) + 1 := by
    have himg : S.card = (S.image g).card := (Finset.card_image_of_injOn hg_inj).symm
    have hsub : S.image g ⊆ Finset.range (Nat.floor (16 * t) + 1) := by
      intro n hn
      obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hn
      have := hg_range k' hk'
      simp only [Finset.mem_range]; omega
    have hle : (S.image g).card ≤ (Finset.range (Nat.floor (16 * t) + 1)).card :=
      Finset.card_le_card hsub
    have hrange : (Finset.range (Nat.floor (16 * t) + 1)).card = Nat.floor (16 * t) + 1 := by simp
    linarith
  have hB : Nat.floor (16 * t) + 1 = branchB t := rfl
  linarith

end

end DimHCore

#print axioms DimHCore.Qsel_ge_factorial
#print axioms DimHCore.Qsel_succ_le
#print axioms DimHCore.fiber_card_le