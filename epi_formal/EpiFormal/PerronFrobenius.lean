import Mathlib
import EpiFormal.FiniteStateComplete

/-!
# Finite-Dimensional Perron-Frobenius Theorem via Wielandt Minimax Compactness
and Unconditional Finite-State Tail Theorems (`ℝ` and `UnitAddCircle`)

Proves the finite-dimensional Perron-Frobenius theorem completely from scratch without
any fixed-point theorem (Brouwer-free) via Collatz-Wielandt minimax optimization over
the compact image `P '' Δ` of the standard simplex under `P = (I + A)^{|V|-1}`:

1. **Perron-Frobenius (`PerronFrobenius`)**:
   - `perron_eigenvalue_unique`: any two strictly positive eigenvectors of a nonnegative
     matrix on a finite nonempty index type share the same eigenvalue.
   - `perron_frobenius_pos`: for any nonnegative irreducible matrix on a finite nonempty
     type with at least one positive entry, there exist a positive eigenvalue `r > 0`
     and a uniformly bounded positive right eigenvector `0 < lo ≤ w u ≤ hi`.
   - `perron_frobenius_ge_one`: if additionally all entries satisfy `A u v = 0 ∨ 1 ≤ A u v`
     (e.g., integer adjacency matrices of directed multigraphs), then `1 ≤ r`.

2. **Unconditional Finite-State Tail Theorems (`FiniteStateUnconditional`)**:
   Applying `PerronFrobenius.perron_frobenius_ge_one` and `perron_eigenvalue_unique` to each
   marked strongly connected component `Component edges v` discharges ALL external
   Perron-Frobenius eigenvector and `lamStar` hypotheses in
   `FiniteStateComplete.thm_finite_state_tail_complete` and
   `FiniteStateComplete.thm_finite_state_tail_circle_complete`, yielding unconditional
   theorems on both `ℝ` and `UnitAddCircle`.
-/

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace PerronFrobenius

noncomputable section

section MatrixOps

variable {α : Type*} [Fintype α]

/-- Matrix-vector product `(A *ᵥ x) u = ∑ z, A u z * x z`. -/
def linOp (A : α → α → ℝ) (x : α → ℝ) (u : α) : ℝ :=
  ∑ z, A u z * x z

/-- Matrix powers `A ^ n` defined recursively on `ℕ`. -/
def matPow [DecidableEq α] (A : α → α → ℝ) : ℕ → α → α → ℝ
  | 0, u, v => if u = v then 1 else 0
  | n + 1, u, v => ∑ z, A u z * matPow A n z v

lemma matPow_zero [DecidableEq α] (A : α → α → ℝ) (u v : α) :
    matPow A 0 u v = if u = v then 1 else 0 := rfl

lemma matPow_succ_left [DecidableEq α] (A : α → α → ℝ) (n : ℕ) (u v : α) :
    matPow A (n + 1) u v = ∑ z, A u z * matPow A n z v := rfl

lemma matPow_succ_right [DecidableEq α] (A : α → α → ℝ) (n : ℕ) (u v : α) :
    matPow A (n + 1) u v = ∑ z, matPow A n u z * A z v := by
  induction n generalizing u v with
  | zero =>
    simp [matPow]
  | succ n ih =>
    calc matPow A (n + 2) u v
        = ∑ z, A u z * matPow A (n + 1) z v := rfl
      _ = ∑ z, A u z * ∑ y, matPow A n z y * A y v := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [ih z v]
      _ = ∑ z, ∑ y, A u z * (matPow A n z y * A y v) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ y, ∑ z, (A u z * matPow A n z y) * A y v := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
          ring
      _ = ∑ y, matPow A (n + 1) u y * A y v := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_mul, ← matPow_succ_left]

lemma matPow_nonneg [DecidableEq α] (A : α → α → ℝ) (hA : ∀ u v, 0 ≤ A u v) :
    ∀ n u v, 0 ≤ matPow A n u v
  | 0, u, v => by
    by_cases h : u = v <;> simp [matPow, h]
  | n + 1, u, v =>
    Finset.sum_nonneg fun z _ => mul_nonneg (hA u z) (matPow_nonneg A hA n z v)

lemma linOp_add_vec (A : α → α → ℝ) (x y : α → ℝ) :
    linOp A (x + y) = linOp A x + linOp A y := by
  ext u
  simp only [linOp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma linOp_sub_vec (A : α → α → ℝ) (x y : α → ℝ) :
    linOp A (x - y) = linOp A x - linOp A y := by
  ext u
  simp only [linOp, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma linOp_smul_vec (A : α → α → ℝ) (c : ℝ) (x : α → ℝ) :
    linOp A (c • x) = c • linOp A x := by
  ext u
  simp only [linOp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => by ring

lemma linOp_matPow_zero [DecidableEq α] (A : α → α → ℝ) (x : α → ℝ) :
    linOp (matPow A 0) x = x := by
  ext u
  simp [linOp, matPow]

lemma linOp_matPow_succ [DecidableEq α] (A : α → α → ℝ) (n : ℕ) (x : α → ℝ) :
    linOp (matPow A (n + 1)) x = linOp A (linOp (matPow A n) x) := by
  ext u
  simp only [linOp, matPow_succ_left, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => by ring

lemma linOp_matPow_eigenvector [DecidableEq α] (A : α → α → ℝ) (w : α → ℝ) (r : ℝ)
    (hw : ∀ u, (∑ z, A u z * w z) = r * w u) (n : ℕ) :
    ∀ u, linOp (matPow A n) w u = r ^ n * w u := by
  induction n with
  | zero =>
    intro u
    simp [linOp_matPow_zero]
  | succ n ih =>
    intro u
    rw [linOp_matPow_succ]
    have h1 : linOp (matPow A n) w = (r ^ n) • w := funext ih
    rw [h1, linOp_smul_vec]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show linOp A w u = r * w u from hw u, pow_succ']
    ring

lemma continuous_linOp (A : α → α → ℝ) : Continuous (linOp A) := by
  refine continuous_pi fun u => ?_
  refine continuous_finsetSum Finset.univ fun z _ => ?_
  exact continuous_const.mul (continuous_apply z)

end MatrixOps

section Uniqueness

/-- Uniqueness of the Perron eigenvalue: any two strictly positive eigenvectors of a
nonnegative matrix on a finite nonempty type share the same eigenvalue. -/
theorem perron_eigenvalue_unique {α : Type*} [Fintype α] [Nonempty α]
    (A : α → α → ℝ) (hA : ∀ u v, 0 ≤ A u v)
    (w₁ w₂ : α → ℝ) (hw₁_pos : ∀ u, 0 < w₁ u) (hw₂_pos : ∀ u, 0 < w₂ u)
    (r₁ r₂ : ℝ)
    (hr₁ : ∀ u, (∑ z, A u z * w₁ z) = r₁ * w₁ u)
    (hr₂ : ∀ u, (∑ z, A u z * w₂ z) = r₂ * w₂ u) :
    r₁ = r₂ := by
  have hle : ∀ (v₁ v₂ : α → ℝ) (hv₁ : ∀ u, 0 < v₁ u) (hv₂ : ∀ u, 0 < v₂ u) (s₁ s₂ : ℝ),
      (∀ u, (∑ z, A u z * v₁ z) = s₁ * v₁ u) →
      (∀ u, (∑ z, A u z * v₂ z) = s₂ * v₂ u) →
      s₁ ≤ s₂ := by
    intro v₁ v₂ hv₁ hv₂ s₁ s₂ hs₁ hs₂
    obtain ⟨u₀, _, hu₀⟩ := Finset.univ.exists_min_image (fun u => v₂ u / v₁ u) Finset.univ_nonempty
    set c : ℝ := v₂ u₀ / v₁ u₀
    have hc_pos : 0 < c := div_pos (hv₂ u₀) (hv₁ u₀)
    have hc_eq : v₂ u₀ = c * v₁ u₀ := (div_mul_cancel₀ _ (hv₁ u₀).ne').symm
    have hc_le : ∀ z, c * v₁ z ≤ v₂ z := fun z =>
      (le_div_iff₀ (hv₁ z)).mp (hu₀ z (Finset.mem_univ z))
    have hmul : s₁ * (c * v₁ u₀) ≤ s₂ * (c * v₁ u₀) := by
      calc s₁ * (c * v₁ u₀)
          = c * (s₁ * v₁ u₀) := by ring
        _ = c * (∑ z, A u₀ z * v₁ z) := by rw [hs₁ u₀]
        _ = ∑ z, A u₀ z * (c * v₁ z) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun z _ => by ring
        _ ≤ ∑ z, A u₀ z * v₂ z :=
            Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hc_le z) (hA u₀ z)
        _ = s₂ * v₂ u₀ := hs₂ u₀
        _ = s₂ * (c * v₁ u₀) := by rw [hc_eq]
    exact le_of_mul_le_mul_right hmul (mul_pos hc_pos (hv₁ u₀))
  exact le_antisymm
    (hle w₁ w₂ hw₁_pos hw₂_pos r₁ r₂ hr₁ hr₂)
    (hle w₂ w₁ hw₂_pos hw₁_pos r₂ r₁ hr₂ hr₁)

end Uniqueness

section CompactnessAndPositivity

private def simplex (α : Type*) [Fintype α] : Set (α → ℝ) :=
  {x | (∀ u, 0 ≤ x u) ∧ (∑ u, x u) = 1}

private lemma simplex_nonempty (α : Type*) [Fintype α] [Nonempty α] :
    (simplex α).Nonempty := by
  classical
  let u₀ : α := Classical.arbitrary α
  refine ⟨fun u => if u = u₀ then 1 else 0, ?_, ?_⟩
  · intro u
    dsimp only
    split_ifs <;> norm_num
  · simp

private lemma isClosed_simplex (α : Type*) [Fintype α] : IsClosed (simplex α) := by
  have hset : simplex α = (⋂ u, {x : α → ℝ | 0 ≤ x u}) ∩ {x : α → ℝ | (∑ u, x u) = 1} := by
    ext x
    simp [simplex]
  rw [hset]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_iInter fun u => isClosed_le continuous_const (continuous_apply u)
  · exact isClosed_eq (continuous_finsetSum Finset.univ fun u _ => continuous_apply u)
      continuous_const

private lemma simplex_subset_Icc (α : Type*) [Fintype α] :
    simplex α ⊆ Set.Icc (fun _ : α => (0 : ℝ)) (fun _ : α => (1 : ℝ)) := by
  rintro x ⟨hx0, hx1⟩
  refine ⟨hx0, fun u => ?_⟩
  calc x u ≤ ∑ v, x v := Finset.single_le_sum (fun v _ => hx0 v) (Finset.mem_univ u)
    _ = 1 := hx1

private lemma isCompact_simplex (α : Type*) [Fintype α] : IsCompact (simplex α) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_simplex α) (simplex_subset_Icc α)

private lemma continuousOn_finset_inf' {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → X → ℝ) (K : Set X)
    (hf : ∀ i ∈ s, ContinuousOn (f i) K) :
    ContinuousOn (fun x => s.inf' hs (fun i => f i x)) K := fun x hx =>
  Filter.Tendsto.finset_inf'_nhds_apply hs fun i hi => hf i hi x hx

private def lazyShiftMat {α : Type*} [DecidableEq α] (A : α → α → ℝ) (u v : α) : ℝ :=
  A u v + if u = v then 1 else 0

private lemma lazyShiftMat_nonneg {α : Type*} [DecidableEq α] (A : α → α → ℝ)
    (hA : ∀ u v, 0 ≤ A u v) (u v : α) : 0 ≤ lazyShiftMat A u v := by
  unfold lazyShiftMat
  split_ifs <;> linarith [hA u v]

private lemma one_le_lazyShiftMat_diag {α : Type*} [DecidableEq α] (A : α → α → ℝ)
    (hA : ∀ u v, 0 ≤ A u v) (u : α) : 1 ≤ lazyShiftMat A u u := by
  simp [lazyShiftMat, hA u u]

private lemma matPow_lazyShift_mono {α : Type*} [Fintype α] [DecidableEq α]
    (A : α → α → ℝ) (hA : ∀ u v, 0 ≤ A u v) (u v : α) :
    Monotone (fun n => matPow (lazyShiftMat A) n u v) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [matPow_succ_left]
  have hsingle : lazyShiftMat A u u * matPow (lazyShiftMat A) n u v ≤
      ∑ z, lazyShiftMat A u z * matPow (lazyShiftMat A) n z v :=
    Finset.single_le_sum
      (fun z _ => mul_nonneg (lazyShiftMat_nonneg A hA u z)
        (matPow_nonneg (lazyShiftMat A) (lazyShiftMat_nonneg A hA) n z v))
      (Finset.mem_univ u)
  have hdiag : matPow (lazyShiftMat A) n u v ≤
      lazyShiftMat A u u * matPow (lazyShiftMat A) n u v := by
    simpa using mul_le_mul_of_nonneg_right (one_le_lazyShiftMat_diag A hA u)
      (matPow_nonneg (lazyShiftMat A) (lazyShiftMat_nonneg A hA) n u v)
  exact hdiag.trans hsingle

private lemma linOp_comm_lazyShift {α : Type*} [Fintype α] [DecidableEq α]
    (A : α → α → ℝ) (x : α → ℝ) :
    linOp A (linOp (lazyShiftMat A) x) = linOp (lazyShiftMat A) (linOp A x) := by
  have hB : ∀ y : α → ℝ, linOp (lazyShiftMat A) y = linOp A y + y := by
    intro y
    ext u
    simp only [linOp, lazyShiftMat, add_mul, Finset.sum_add_distrib, Pi.add_apply]
    simp
  rw [hB x, hB (linOp A x), linOp_add_vec]

private lemma linOp_comm_matPow_lazyShift {α : Type*} [Fintype α] [DecidableEq α]
    (A : α → α → ℝ) (n : ℕ) (x : α → ℝ) :
    linOp A (linOp (matPow (lazyShiftMat A) n) x) =
      linOp (matPow (lazyShiftMat A) n) (linOp A x) := by
  induction n with
  | zero =>
    simp [linOp_matPow_zero]
  | succ n ih =>
    rw [linOp_matPow_succ, linOp_comm_lazyShift, ih, ← linOp_matPow_succ]

private lemma matPow_lazyShift_pos_of_irr {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (A : α → α → ℝ) (hA : ∀ u v, 0 ≤ A u v)
    (hIrr : ∀ u v, Relation.ReflTransGen (fun x y => 0 < A x y) u v) :
    ∀ u v, 0 < matPow (lazyShiftMat A) (Fintype.card α - 1) u v := by
  let B := lazyShiftMat A
  let N := Fintype.card α
  let reach : α → ℕ → Finset α := fun u n =>
    Finset.univ.filter (fun v => 0 < matPow B n u v)
  have hreach_zero : ∀ u, u ∈ reach u 0 := fun u =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ u, by simp [matPow]⟩
  have hreach_mono : ∀ u {m n : ℕ}, m ≤ n → reach u m ⊆ reach u n := by
    intro u m n hmn v hv
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.trans_le (matPow_lazyShift_mono A hA u v hmn)
  have hstab : ∀ u, ∃ n < N, reach u n = reach u (n + 1) := by
    intro u
    by_contra hno
    push Not at hno
    have hlt : ∀ n < N, (reach u n).card + 1 ≤ (reach u (n + 1)).card := fun n hn => by
      have hssub : reach u n ⊂ reach u (n + 1) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hreach_mono u (Nat.le_succ n), hno n hn⟩
      exact Finset.card_lt_card hssub
    have hgrowth : ∀ k ≤ N, (reach u 0).card + k ≤ (reach u k).card := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have hkN : k < N := hk
        have h1 := ih hkN.le
        have h2 := hlt k hkN
        omega
    have hN1 : (reach u 0).card + N ≤ (reach u N).card := hgrowth N le_rfl
    have h0pos : 1 ≤ (reach u 0).card := Finset.card_pos.mpr ⟨u, hreach_zero u⟩
    have hNle : (reach u N).card ≤ N := Finset.card_le_univ _
    omega
  have hstep : ∀ u n, reach u n = reach u (n + 1) →
      ∀ x y, x ∈ reach u n → 0 < A x y → y ∈ reach u n := by
    intro u n heq x y hx hxy
    rw [heq]
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [matPow_succ_right]
    have hBxy : 0 < B x y := by
      have hnonneg : (0 : ℝ) ≤ if x = y then 1 else 0 := by split_ifs <;> norm_num
      change 0 < A x y + if x = y then 1 else 0
      linarith
    have hterm : 0 < matPow B n u x * B x y := mul_pos hx hBxy
    have hle : matPow B n u x * B x y ≤ ∑ z, matPow B n u z * B z y :=
      Finset.single_le_sum
        (fun z _ => mul_nonneg (matPow_nonneg B (lazyShiftMat_nonneg A hA) n u z)
          (lazyShiftMat_nonneg A hA z y))
        (Finset.mem_univ x)
    exact hterm.trans_le hle
  intro u v
  obtain ⟨n, hnN, heq⟩ := hstab u
  have hv_n : v ∈ reach u n := by
    have hu_n : u ∈ reach u n := hreach_mono u (Nat.zero_le n) (hreach_zero u)
    induction hIrr u v with
    | refl => exact hu_n
    | tail _ hbc ih => exact hstep u n heq _ _ ih hbc
  have hv_N1 : v ∈ reach u (N - 1) :=
    hreach_mono u (Nat.le_sub_one_of_lt hnN) hv_n
  simpa [reach] using hv_N1

end CompactnessAndPositivity

section MainPerronFrobenius

/-- **Brouwer-free Finite-Dimensional Perron-Frobenius Theorem (Positive Entries)**:
For any finite nonempty type `α` and nonnegative matrix `A : α → α → ℝ` that is irreducible
(`∀ u v, Relation.ReflTransGen (fun x y => 0 < A x y) u v`) with at least one positive entry
(`∃ u₁ u₂, 0 < A u₁ u₂`), there exist a strictly positive eigenvalue `r > 0` and a uniformly
bounded positive right eigenvector `lo ≤ w u ≤ hi` with `0 < lo ≤ hi`. -/
theorem perron_frobenius_pos {α : Type*} [Fintype α] [Nonempty α]
    (A : α → α → ℝ) (hA : ∀ u v, 0 ≤ A u v)
    (hIrr : ∀ u v, Relation.ReflTransGen (fun x y => 0 < A x y) u v)
    (hEdge : ∃ u₁ u₂, 0 < A u₁ u₂) :
    ∃ (r : ℝ) (w : α → ℝ) (lo hi : ℝ),
      0 < r ∧ 0 < lo ∧ 0 < hi ∧
      (∀ u, lo ≤ w u) ∧ (∀ u, w u ≤ hi) ∧
      (∀ u, (∑ z, A u z * w z) = r * w u) := by
  classical
  let M : ℕ := Fintype.card α - 1
  let Pmat : α → α → ℝ := matPow (lazyShiftMat A) M
  have hP_pos : ∀ u v, 0 < Pmat u v := matPow_lazyShift_pos_of_irr A hA hIrr
  let P : (α → ℝ) → (α → ℝ) := linOp Pmat
  let T : (α → ℝ) → (α → ℝ) := linOp A
  have hP_cont : Continuous P := continuous_linOp Pmat
  let K : Set (α → ℝ) := P '' simplex α
  have hK_ne : K.Nonempty := (simplex_nonempty α).image P
  have hK_compact : IsCompact K := (isCompact_simplex α).image hP_cont
  let c_min : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun p : α × α => Pmat p.1 p.2)
  have hc_min_pos : 0 < c_min :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun p _ => hP_pos p.1 p.2
  have hc_min_le : ∀ u v, c_min ≤ Pmat u v := fun u v =>
    Finset.inf'_le (fun p : α × α => Pmat p.1 p.2) (Finset.mem_univ (u, v))
  have hK_lower : ∀ y ∈ K, ∀ u, c_min ≤ y u := by
    rintro y ⟨x, ⟨hx0, hx1⟩, rfl⟩ u
    calc c_min = c_min * 1 := (mul_one c_min).symm
      _ = c_min * ∑ z, x z := by rw [hx1]
      _ = ∑ z, c_min * x z := Finset.mul_sum Finset.univ x c_min
      _ ≤ ∑ z, Pmat u z * x z :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hc_min_le u z) (hx0 z)
      _ = P x u := rfl
  have hK_pos : ∀ y ∈ K, ∀ u, 0 < y u := fun y hy u =>
    hc_min_pos.trans_le (hK_lower y hy u)
  have hout : ∀ u : α, ∃ v : α, 0 < A u v := by
    intro u
    by_cases hsub : Subsingleton α
    · rcases hEdge with ⟨u₁, u₂, hu12⟩
      rw [Subsingleton.elim u₁ u, Subsingleton.elim u₂ u] at hu12
      exact ⟨u, hu12⟩
    · rw [not_subsingleton_iff_nontrivial] at hsub
      obtain ⟨v, hv⟩ := exists_ne u
      have hreach := hIrr u v
      cases hreach using Relation.ReflTransGen.head_induction_on with
      | refl => exact (hv rfl).elim
      | head hxy _ => exact ⟨_, hxy⟩
  let rho : (α → ℝ) → ℝ := fun y =>
    Finset.univ.inf' Finset.univ_nonempty (fun u => T y u / y u)
  have hrho_cont : ContinuousOn rho K := by
    refine continuousOn_finset_inf' Finset.univ Finset.univ_nonempty _ K fun u _ => ?_
    exact (continuous_apply u |>.comp (continuous_linOp A)).continuousOn.div
      (continuous_apply u).continuousOn fun y hy => (hK_pos y hy u).ne'
  obtain ⟨w, hw_mem, hw_max⟩ := hK_compact.exists_isMaxOn hK_ne hrho_cont
  let r : ℝ := rho w
  have hr_pos : 0 < r := by
    refine (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun u _ => ?_
    obtain ⟨v, huv⟩ := hout u
    have hterm : 0 < A u v * w v := mul_pos huv (hK_pos w hw_mem v)
    have hTpos : 0 < T w u :=
      hterm.trans_le (Finset.single_le_sum
        (fun z _ => mul_nonneg (hA u z) (hK_pos w hw_mem z).le) (Finset.mem_univ v))
    exact div_pos hTpos (hK_pos w hw_mem u)
  have hr_le : ∀ u, r * w u ≤ T w u := fun u => by
    have h1 : r ≤ T w u / w u :=
      Finset.inf'_le (fun z => T w z / w z) (Finset.mem_univ u)
    exact (le_div_iff₀ (hK_pos w hw_mem u)).mp h1
  have hw_eig : ∀ u, T w u = r * w u := by
    by_contra hne
    push Not at hne
    obtain ⟨u₀, hu₀⟩ := hne
    have hdiff_nonneg : ∀ z, 0 ≤ (T w - r • w) z := fun z =>
      sub_nonneg.mpr (hr_le z)
    have hdiff_pos : 0 < (T w - r • w) u₀ :=
      sub_pos.mpr ((hr_le u₀).lt_of_ne' hu₀)
    let s : ℝ := ∑ u, w u
    have hs_pos : 0 < s :=
      Finset.sum_pos (fun u _ => hK_pos w hw_mem u) Finset.univ_nonempty
    let z₀ : α → ℝ := fun u => w u / s
    have hz₀_mem : z₀ ∈ simplex α := by
      refine ⟨fun u => div_nonneg (hK_pos w hw_mem u).le hs_pos.le, ?_⟩
      change (∑ u, w u / s) = 1
      rw [← Finset.sum_div, div_self hs_pos.ne']
    let y₁ : α → ℝ := P z₀
    have hy₁_mem : y₁ ∈ K := ⟨z₀, hz₀_mem, rfl⟩
    have hz₀_eq : z₀ = s⁻¹ • w := by
      ext u
      simp [z₀, div_eq_mul_inv, mul_comm]
    have hy₁_eq : y₁ = s⁻¹ • P w := by
      change linOp Pmat z₀ = s⁻¹ • linOp Pmat w
      rw [hz₀_eq, linOp_smul_vec]
    have hcomm : T (P w) = P (T w) := linOp_comm_matPow_lazyShift A M w
    have hstrict : ∀ u, r * P w u < T (P w) u := fun u => by
      have hpos_P : 0 < P (T w - r • w) u := by
        have hterm : 0 < Pmat u u₀ * (T w - r • w) u₀ :=
          mul_pos (hP_pos u u₀) hdiff_pos
        exact hterm.trans_le (Finset.single_le_sum
          (fun z _ => mul_nonneg (hP_pos u z).le (hdiff_nonneg z)) (Finset.mem_univ u₀))
      have h_sub : P (T w - r • w) = P (T w) - r • P w := by
        change linOp Pmat (T w - r • w) = linOp Pmat (T w) - r • linOp Pmat w
        rw [linOp_sub_vec, linOp_smul_vec]
      have h_id : P (T w - r • w) u = T (P w) u - r * P w u := by
        rw [congrFun h_sub u, ← hcomm]
        simp
      linarith
    have hr_lt_y₁ : r < rho y₁ := by
      refine (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun u _ => ?_
      have hy₁_pos : 0 < y₁ u := hK_pos y₁ hy₁_mem u
      have hT_y₁ : T y₁ = s⁻¹ • T (P w) := by
        change linOp A y₁ = s⁻¹ • linOp A (P w)
        rw [hy₁_eq, linOp_smul_vec]
      have h_eq_ratio : T y₁ u / y₁ u = T (P w) u / P w u := by
        rw [hT_y₁, hy₁_eq]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_div_mul_left _ _ (inv_ne_zero hs_pos.ne')
      have hPw_pos : 0 < P w u := by
        have h := hy₁_pos
        rw [hy₁_eq, Pi.smul_apply, smul_eq_mul] at h
        exact (pos_iff_pos_of_mul_pos h).mp (inv_pos.mpr hs_pos)
      rw [h_eq_ratio]
      exact (lt_div_iff₀ hPw_pos).mpr (hstrict u)
    exact absurd (hw_max hy₁_mem) (not_le_of_gt hr_lt_y₁)
  let hi : ℝ := Finset.univ.sup' Finset.univ_nonempty w
  have hhi_pos : 0 < hi :=
    (hK_pos w hw_mem (Classical.arbitrary α)).trans_le
      (Finset.le_sup' w (Finset.mem_univ (Classical.arbitrary α)))
  exact ⟨r, w, c_min, hi, hr_pos, hc_min_pos, hhi_pos,
    hK_lower w hw_mem,
    fun u => Finset.le_sup' w (Finset.mem_univ u),
    hw_eig⟩

/-- **Integer/Unit-Threshold Perron-Frobenius Theorem**:
If in addition every entry satisfies `A u v = 0 ∨ 1 ≤ A u v` (for instance, adjacency counts
of a directed multigraph), then the Perron eigenvalue satisfies `1 ≤ r`. -/
theorem perron_frobenius_ge_one {α : Type*} [Fintype α] [Nonempty α]
    (A : α → α → ℝ) (hA : ∀ u v, 0 ≤ A u v)
    (hInt : ∀ u v, A u v = 0 ∨ 1 ≤ A u v)
    (hIrr : ∀ u v, Relation.ReflTransGen (fun x y => 0 < A x y) u v)
    (hEdge : ∃ u₁ u₂, 0 < A u₁ u₂) :
    ∃ (r : ℝ) (w : α → ℝ) (lo hi : ℝ),
      1 ≤ r ∧ 0 < lo ∧ 0 < hi ∧
      (∀ u, lo ≤ w u) ∧ (∀ u, w u ≤ hi) ∧
      (∀ u, (∑ z, A u z * w z) = r * w u) := by
  classical
  obtain ⟨r, w, lo, hi, hr_pos, hlo_pos, hhi_pos, hlo, hhi, hw⟩ :=
    perron_frobenius_pos A hA hIrr hEdge
  have hA_ge_one : ∀ u v, 0 < A u v → 1 ≤ A u v := fun u v huv => by
    rcases hInt u v with h0 | h1
    · linarith
    · exact h1
  have hwalk_ge_one : ∀ a b : α, Relation.ReflTransGen (fun x y => 0 < A x y) a b →
      ∃ n : ℕ, 1 ≤ matPow A n a b := by
    intro a b hab
    induction hab with
    | refl =>
      exact ⟨0, by simp [matPow]⟩
    | tail _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [matPow_succ_right]
      have hprod : 1 ≤ matPow A n a _ * A _ _ :=
        one_le_mul_of_one_le_of_one_le hn (hA_ge_one _ _ hbc)
      exact hprod.trans (Finset.single_le_sum
        (fun z _ => mul_nonneg (matPow_nonneg A hA n a z) (hA z _))
        (Finset.mem_univ _))
  obtain ⟨u₁, u₂, hu12⟩ := hEdge
  obtain ⟨L, hL⟩ := hwalk_ge_one u₂ u₁ (hIrr u₂ u₁)
  have hloop : 1 ≤ matPow A (L + 1) u₁ u₁ := by
    rw [matPow_succ_left]
    have hprod : 1 ≤ A u₁ u₂ * matPow A L u₂ u₁ :=
      one_le_mul_of_one_le_of_one_le (hA_ge_one u₁ u₂ hu12) hL
    exact hprod.trans (Finset.single_le_sum
      (fun z _ => mul_nonneg (hA u₁ z) (matPow_nonneg A hA L z u₁))
      (Finset.mem_univ u₂))
  have hw_pos : ∀ u, 0 < w u := fun u => hlo_pos.trans_le (hlo u)
  have hpow_eq : r ^ (L + 1) * w u₁ = linOp (matPow A (L + 1)) w u₁ :=
    (linOp_matPow_eigenvector A w r hw (L + 1) u₁).symm
  have hpow_ge : w u₁ ≤ r ^ (L + 1) * w u₁ := by
    rw [hpow_eq]
    have hsingle : matPow A (L + 1) u₁ u₁ * w u₁ ≤
        ∑ z, matPow A (L + 1) u₁ z * w z :=
      Finset.single_le_sum
        (fun z _ => mul_nonneg (matPow_nonneg A hA (L + 1) u₁ z) (hw_pos z).le)
        (Finset.mem_univ u₁)
    have h1 : w u₁ ≤ matPow A (L + 1) u₁ u₁ * w u₁ := by
      simpa using mul_le_mul_of_nonneg_right hloop (hw_pos u₁).le
    exact h1.trans hsingle
  have hrpow : 1 ≤ r ^ (L + 1) := by
    have h1 : 1 * w u₁ ≤ r ^ (L + 1) * w u₁ := by simpa using hpow_ge
    exact le_of_mul_le_mul_right h1 (hw_pos u₁)
  have hr1 : 1 ≤ r := by
    by_contra hlt
    push Not at hlt
    have hpow_lt : r ^ (L + 1) < 1 := pow_lt_one₀ hr_pos.le hlt (Nat.succ_ne_zero L)
    linarith
  exact ⟨r, w, lo, hi, hr1, hlo_pos, hhi_pos, hlo, hhi, hw⟩

end MainPerronFrobenius

end

end PerronFrobenius

namespace FiniteStateUnconditional

open FiniteStateGauge FiniteStateComplete PerronFrobenius

noncomputable section

/-- Predicate asserting that `edges` contains a directed cycle traversing a marked `±k` edge. -/
def HasMarkedCycle {V : Type*} (edges : V → V → Finset ℤ) (k : ℕ) : Prop :=
  ∃ u v : V, ∃ a, a ∈ edges u v ∧ |a| = (k : ℤ) ∧
    Relation.ReflTransGen (edgeRel edges) v u

/-- Predicate asserting that the strongly connected component of `v` contains a marked `±k` edge. -/
def MarkedComponent {V : Type*} (edges : V → V → Finset ℤ) (k : ℕ) (v : V) : Prop :=
  ∃ u₁ u₂ : Component edges v, ∃ a, a ∈ componentEdges edges v u₁ u₂ ∧ |a| = (k : ℤ)

private lemma component_stronglyConnected_adj {V : Type*} (edges : V → V → Finset ℤ) (v : V) :
    ∀ u₁ u₂ : Component edges v,
      Relation.ReflTransGen
        (fun x y => 0 < adjacency (componentEdges edges v) x y) u₁ u₂ := by
  have hrel : ∀ x y : Component edges v,
      edgeRel (componentEdges edges v) x y →
        0 < adjacency (componentEdges edges v) x y := by
    intro x y ⟨a, ha⟩
    unfold adjacency
    exact_mod_cast Finset.card_pos.mpr ⟨a, ha⟩
  have hreach : ∀ {a b : V} (hab : Relation.ReflTransGen (edgeRel edges) a b)
      (ha : Relation.ReflTransGen (edgeRel edges) v a)
      (hb : Relation.ReflTransGen (edgeRel edges) b v),
      Relation.ReflTransGen (edgeRel (componentEdges edges v))
        ⟨a, ha, hab.trans hb⟩ ⟨b, ha.trans hab, hb⟩ := by
    intro a b hab ha hb
    induction hab with
    | refl => exact .refl
    | tail had hdb ih =>
      have hdv : Relation.ReflTransGen (edgeRel edges) _ v := .head hdb hb
      exact (ih hdv).tail hdb
  intro u₁ u₂
  have h12 : Relation.ReflTransGen (edgeRel (componentEdges edges v)) u₁ u₂ :=
    hreach (u₁.2.2.trans u₂.2.1) u₁.2.1 u₂.2.2
  induction h12 with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (hrel _ _ h)

/-- Every marked strongly connected component automatically carries an integer-threshold
Perron eigenvalue `r ≥ 1` and a uniformly bounded positive right eigenvector. -/
theorem markedComponent_perron_eigenvector {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) (k : ℕ) (v : V) (hv : MarkedComponent edges k v) :
    ∃ (r : ℝ) (w : Component edges v → ℝ) (lo hi : ℝ),
      1 ≤ r ∧ 0 < lo ∧ 0 < hi ∧
      (∀ u, lo ≤ w u) ∧ (∀ u, w u ≤ hi) ∧
      (∀ u, (∑ z, adjacency (componentEdges edges v) u z * w z) = r * w u) := by
  have : Nonempty (Component edges v) :=
    ⟨⟨v, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩⟩
  let A : Component edges v → Component edges v → ℝ := adjacency (componentEdges edges v)
  have hA : ∀ x y, 0 ≤ A x y := fun x y => Nat.cast_nonneg _
  have hInt : ∀ x y, A x y = 0 ∨ 1 ≤ A x y := by
    intro x y
    rcases Nat.eq_zero_or_pos (componentEdges edges v x y).card with h0 | hpos
    · left; simp [A, adjacency, h0]
    · right
      dsimp only [A, adjacency]
      exact_mod_cast hpos
  have hIrr := component_stronglyConnected_adj edges v
  have hEdge : ∃ u₁ u₂, 0 < A u₁ u₂ := by
    rcases hv with ⟨u₁, u₂, a, ha, _⟩
    refine ⟨u₁, u₂, ?_⟩
    dsimp only [A, adjacency]
    exact_mod_cast Finset.card_pos.mpr ⟨a, ha⟩
  exact perron_frobenius_ge_one A hA hInt hIrr hEdge

private lemma exists_markedComponent_of_hasMarkedCycle {V : Type*}
    (edges : V → V → Finset ℤ) (k : ℕ) (hcyc : HasMarkedCycle edges k) :
    ∃ v : V, MarkedComponent edges k v := by
  rcases hcyc with ⟨u, v, a, ha, hmark, hvu⟩
  refine ⟨u, ⟨u, .refl, .refl⟩,
    ⟨v, Relation.ReflTransGen.single ⟨a, ha⟩, hvu⟩, a, ha, hmark⟩

/-- Canonical Perron root of a marked component. -/
def componentPerronRoot {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) (k : ℕ) (v : V) (hv : MarkedComponent edges k v) : ℝ :=
  (markedComponent_perron_eigenvector edges k v hv).choose

private lemma componentPerronRoot_spec {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) (k : ℕ) (v : V) (hv : MarkedComponent edges k v) :
    ∃ (w : Component edges v → ℝ) (lo hi : ℝ),
      1 ≤ componentPerronRoot edges k v hv ∧ 0 < lo ∧ 0 < hi ∧
      (∀ u, lo ≤ w u) ∧ (∀ u, w u ≤ hi) ∧
      (∀ u, (∑ z, adjacency (componentEdges edges v) u z * w z) =
        componentPerronRoot edges k v hv * w u) :=
  (markedComponent_perron_eigenvector edges k v hv).choose_spec

private lemma exists_dominantPerronRoot {V : Type*} [Fintype V]
    (edges : V → V → Finset ℤ) (k : ℕ) (hcyc : HasMarkedCycle edges k) :
    ∃ lamStar : ℝ, 1 ≤ lamStar ∧
      (∀ v : V, MarkedComponent edges k v →
        ∃ (w : Component edges v → ℝ) (growth lo hi : ℝ),
          0 < lo ∧ 0 < hi ∧ 1 ≤ growth ∧ growth ≤ lamStar ∧
          (∀ u, (∑ z, adjacency (componentEdges edges v) u z * w z) = growth * w u) ∧
          (∀ u, lo ≤ w u) ∧ (∀ u, w u ≤ hi)) ∧
      (∃ (v₀ : V) (u₁ u₂ : Component edges v₀) (a_mark : ℤ),
        a_mark ∈ componentEdges edges v₀ u₁ u₂ ∧ |a_mark| = (k : ℤ) ∧
        ∃ (w : Component edges v₀ → ℝ) (lo hi : ℝ), 0 < lo ∧ 0 < hi ∧
          (∀ u, (∑ z, adjacency (componentEdges edges v₀) u z * w z) = lamStar * w u) ∧
          (∀ u, lo ≤ w u) ∧ (∀ u, w u ≤ hi)) := by
  classical
  let M : Finset V := Finset.univ.filter (fun v => MarkedComponent edges k v)
  have hM_ne : M.Nonempty := by
    obtain ⟨v, hv⟩ := exists_markedComponent_of_hasMarkedCycle edges k hcyc
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
  let r : V → ℝ := fun v =>
    if hv : MarkedComponent edges k v then componentPerronRoot edges k v hv else 1
  obtain ⟨v₀, hv₀_mem, hv₀_max⟩ := M.exists_max_image r hM_ne
  have hv₀ : MarkedComponent edges k v₀ := (Finset.mem_filter.mp hv₀_mem).2
  let lamStar : ℝ := r v₀
  have hlamStar_eq : lamStar = componentPerronRoot edges k v₀ hv₀ := by
    simp [lamStar, r, hv₀]
  obtain ⟨w₀, lo₀, hi₀, hr₀_ge1, hlo₀, hhi₀, hl₀, hu₀, hw₀⟩ :=
    componentPerronRoot_spec edges k v₀ hv₀
  have hlamStar_ge1 : 1 ≤ lamStar := hlamStar_eq.symm ▸ hr₀_ge1
  refine ⟨lamStar, hlamStar_ge1, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, lo, hi, hr_ge1, hlo, hhi, hl, hu, hw⟩ :=
      componentPerronRoot_spec edges k v hv
    have hv_mem : v ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
    have hr_le : componentPerronRoot edges k v hv ≤ lamStar := by
      have hmax := hv₀_max v hv_mem
      simpa [r, hv, lamStar] using hmax
    exact ⟨w, componentPerronRoot edges k v hv, lo, hi, hlo, hhi, hr_ge1, hr_le, hw, hl, hu⟩
  · rcases hv₀ with ⟨u₁, u₂, a_mark, ha_mem, ha_abs⟩
    refine ⟨v₀, u₁, u₂, a_mark, ha_mem, ha_abs, w₀, lo₀, hi₀, hlo₀, hhi₀, ?_, hl₀, hu₀⟩
    intro u
    rw [hlamStar_eq]
    exact hw₀ u

/-- **Unconditional Joint Finite-State Tail Theorem (`ℝ` and `UnitAddCircle`)**:
Eliminates ALL Perron-Frobenius eigenvector and `lamStar` hypotheses from
`thm_finite_state_tail_complete` and `thm_finite_state_tail_circle_complete`,
exhibiting a single canonical dominant Perron root `lamStar ≥ 1` governing both spaces
simultaneously. -/
theorem thm_finite_state_tail_joint_unconditional {V : Type*} [Finite V]
    (edges : V → V → Finset ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges) :
    (¬ HasMarkedCycle edges k →
      exactTail edges k = ∅ ∧ circleExactTail edges k = ∅) ∧
    (HasMarkedCycle edges k →
      ∃ lamStar : ℝ, 1 ≤ lamStar ∧
        (lamStar = 1 → (exactTail edges k).Countable ∧ (circleExactTail edges k).Countable) ∧
        (1 < lamStar →
          ∀ (g : ℝ≥0∞ → ℝ≥0∞), Monotone g →
            ((liminf (perronCost lamStar g) atTop = 0 →
              Measure.mkMetric g (exactTail edges k) = 0 ∧
              Measure.mkMetric g (circleExactTail edges k) = 0) ∧
            (0 < liminf (perronCost lamStar g) atTop →
              (∀ a b : ℝ, a < b → Measure.mkMetric g (exactTail edges k ∩ Set.Ioo a b) = ⊤) ∧
              Measure.mkMetric g (exactTail edges k) = ⊤ ∧
              (∀ U : Set UnitAddCircle, IsOpen U → U.Nonempty →
                Measure.mkMetric g (circleExactTail edges k ∩ U) = ⊤) ∧
              Measure.mkMetric g (circleExactTail edges k) = ⊤) ∧
            (liminf (perronCost lamStar g) atTop < ⊤ →
              (∃ E : ℕ → Set ℝ, exactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
              (∃ E : ℕ → Set UnitAddCircle,
                circleExactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤)) ∧
            (liminf (perronCost lamStar g) atTop = ⊤ →
              (¬ ∃ E : ℕ → Set ℝ,
                exactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
              (¬ ∃ E : ℕ → Set UnitAddCircle,
                circleExactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤))))) := by
  let inst : Fintype V := Fintype.ofFinite V
  have hR := @thm_finite_state_tail_complete V inst edges k hk hlabels hdet
  have hC := @thm_finite_state_tail_circle_complete V inst edges k hk hlabels hdet
  refine ⟨?_, ?_⟩
  · intro hno
    exact ⟨hR.1 hno, hC.1 hno⟩
  · intro hcyc
    obtain ⟨lamStar, hlam1, hcomp_bd, hex_dom⟩ := @exists_dominantPerronRoot V inst edges k hcyc
    refine ⟨lamStar, hlam1, ?_, ?_⟩
    · intro hlam_eq
      have hroot1 : ∀ v : V, MarkedComponent edges k v →
          ∃ (w : Component edges v → ℝ) (lo : ℝ), 0 < lo ∧
            (∀ u, (∑ z, adjacency (componentEdges edges v) u z * w z) = w u) ∧
            ∀ u, lo ≤ w u := by
        intro v hv
        obtain ⟨w, growth, lo, _, hlo, _, hge1, hle_lam, hw, hl, _⟩ := hcomp_bd v hv
        have hgrowth1 : growth = 1 := le_antisymm (hle_lam.trans hlam_eq.le) hge1
        refine ⟨w, lo, hlo, fun u => by simpa [hgrowth1] using hw u, hl⟩
      exact ⟨hR.2.1 hroot1, hC.2.1 hroot1⟩
    · intro hlam_gt g hg
      have hR3 := hR.2.2 lamStar hlam_gt hcomp_bd hex_dom g hg
      have hC3 := hC.2.2 lamStar hlam_gt hcomp_bd hex_dom g hg
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hz
        exact ⟨hR3.1 hz, hC3.1 hz⟩
      · intro hpos
        obtain ⟨hR_Ioo, hR_tot⟩ := hR3.2.1 hpos
        obtain ⟨hC_open, hC_tot⟩ := hC3.2.1 hpos
        exact ⟨hR_Ioo, hR_tot, hC_open, hC_tot⟩
      · intro hfin
        exact ⟨hR3.2.2.1 hfin, hC3.2.2.1 hfin⟩
      · intro htop
        exact ⟨hR3.2.2.2 htop, hC3.2.2.2 htop⟩

/-- **Unconditional Finite-State Tail Theorem on `ℝ`** (Paper 2 Theorem `thm:finite-state-tail`
with all external Perron-Frobenius hypotheses discharged). -/
theorem thm_finite_state_tail_unconditional {V : Type*} [Finite V]
    (edges : V → V → Finset ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges) :
    (¬ HasMarkedCycle edges k → exactTail edges k = ∅) ∧
    (HasMarkedCycle edges k →
      ∃ lamStar : ℝ, 1 ≤ lamStar ∧
        (lamStar = 1 → (exactTail edges k).Countable) ∧
        (1 < lamStar →
          ∀ (g : ℝ≥0∞ → ℝ≥0∞), Monotone g →
            (liminf (perronCost lamStar g) atTop = 0 →
              Measure.mkMetric g (exactTail edges k) = 0) ∧
            (0 < liminf (perronCost lamStar g) atTop →
              (∀ a b : ℝ, a < b → Measure.mkMetric g (exactTail edges k ∩ Set.Ioo a b) = ⊤) ∧
              Measure.mkMetric g (exactTail edges k) = ⊤) ∧
            (liminf (perronCost lamStar g) atTop < ⊤ →
              ∃ E : ℕ → Set ℝ, exactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
            (liminf (perronCost lamStar g) atTop = ⊤ →
              ¬ ∃ E : ℕ → Set ℝ,
                exactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤))) := by
  have hJ := thm_finite_state_tail_joint_unconditional edges k hk hlabels hdet
  refine ⟨fun hno => (hJ.1 hno).1, fun hcyc => ?_⟩
  obtain ⟨lamStar, hlam1, hcnt, hsup⟩ := hJ.2 hcyc
  refine ⟨lamStar, hlam1, fun h1 => (hcnt h1).1, fun hgt g hg => ?_⟩
  have h := hsup hgt g hg
  exact ⟨fun hz => (h.1 hz).1,
    fun hpos => ⟨(h.2.1 hpos).1, (h.2.1 hpos).2.1⟩,
    fun hfin => (h.2.2.1 hfin).1,
    fun htop => (h.2.2.2 htop).1⟩

/-- **Unconditional Finite-State Tail Theorem on `UnitAddCircle`** (with all external
Perron-Frobenius hypotheses discharged). -/
theorem thm_finite_state_tail_circle_unconditional {V : Type*} [Finite V]
    (edges : V → V → Finset ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges) :
    (¬ HasMarkedCycle edges k → circleExactTail edges k = ∅) ∧
    (HasMarkedCycle edges k →
      ∃ lamStar : ℝ, 1 ≤ lamStar ∧
        (lamStar = 1 → (circleExactTail edges k).Countable) ∧
        (1 < lamStar →
          ∀ (g : ℝ≥0∞ → ℝ≥0∞), Monotone g →
            (liminf (perronCost lamStar g) atTop = 0 →
              Measure.mkMetric g (circleExactTail edges k) = 0) ∧
            (0 < liminf (perronCost lamStar g) atTop →
              (∀ U : Set UnitAddCircle, IsOpen U → U.Nonempty →
                Measure.mkMetric g (circleExactTail edges k ∩ U) = ⊤) ∧
              Measure.mkMetric g (circleExactTail edges k) = ⊤) ∧
            (liminf (perronCost lamStar g) atTop < ⊤ →
              ∃ E : ℕ → Set UnitAddCircle,
                circleExactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
            (liminf (perronCost lamStar g) atTop = ⊤ →
              ¬ ∃ E : ℕ → Set UnitAddCircle,
                circleExactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤))) := by
  have hJ := thm_finite_state_tail_joint_unconditional edges k hk hlabels hdet
  refine ⟨fun hno => (hJ.1 hno).2, fun hcyc => ?_⟩
  obtain ⟨lamStar, hlam1, hcnt, hsup⟩ := hJ.2 hcyc
  refine ⟨lamStar, hlam1, fun h1 => (hcnt h1).2, fun hgt g hg => ?_⟩
  have h := hsup hgt g hg
  exact ⟨fun hz => (h.1 hz).2,
    fun hpos => ⟨(h.2.1 hpos).2.2.1, (h.2.1 hpos).2.2.2⟩,
    fun hfin => (h.2.2.1 hfin).2,
    fun htop => (h.2.2.2 htop).2⟩

/-- Pure three-way disjunction form of `thm_finite_state_tail_unconditional` on `ℝ`. -/
theorem thm_finite_state_tail_trichotomy {V : Type*} [Finite V]
    (edges : V → V → Finset ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges) :
    exactTail edges k = ∅ ∨
    (exactTail edges k).Countable ∨
    (∃ lamStar : ℝ, 1 < lamStar ∧
      ∀ (g : ℝ≥0∞ → ℝ≥0∞), Monotone g →
        (liminf (perronCost lamStar g) atTop = 0 →
          Measure.mkMetric g (exactTail edges k) = 0) ∧
        (0 < liminf (perronCost lamStar g) atTop →
          (∀ a b : ℝ, a < b → Measure.mkMetric g (exactTail edges k ∩ Set.Ioo a b) = ⊤) ∧
          Measure.mkMetric g (exactTail edges k) = ⊤) ∧
        (liminf (perronCost lamStar g) atTop < ⊤ →
          ∃ E : ℕ → Set ℝ, exactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
        (liminf (perronCost lamStar g) atTop = ⊤ →
          ¬ ∃ E : ℕ → Set ℝ,
            exactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤)) := by
  have h := thm_finite_state_tail_unconditional edges k hk hlabels hdet
  by_cases hcyc : HasMarkedCycle edges k
  · obtain ⟨lamStar, hlam1, hcnt, hsup⟩ := h.2 hcyc
    rcases eq_or_lt_of_le hlam1 with rfl | hgt
    · exact Or.inr (Or.inl (hcnt rfl))
    · exact Or.inr (Or.inr ⟨lamStar, hgt, hsup hgt⟩)
  · exact Or.inl (h.1 hcyc)

/-- Pure three-way disjunction form of `thm_finite_state_tail_circle_unconditional`
on `UnitAddCircle`. -/
theorem thm_finite_state_tail_circle_trichotomy {V : Type*} [Finite V]
    (edges : V → V → Finset ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hlabels : edgeLabelsLe edges k) (hdet : Deterministic edges) :
    circleExactTail edges k = ∅ ∨
    (circleExactTail edges k).Countable ∨
    (∃ lamStar : ℝ, 1 < lamStar ∧
      ∀ (g : ℝ≥0∞ → ℝ≥0∞), Monotone g →
        (liminf (perronCost lamStar g) atTop = 0 →
          Measure.mkMetric g (circleExactTail edges k) = 0) ∧
        (0 < liminf (perronCost lamStar g) atTop →
          (∀ U : Set UnitAddCircle, IsOpen U → U.Nonempty →
            Measure.mkMetric g (circleExactTail edges k ∩ U) = ⊤) ∧
          Measure.mkMetric g (circleExactTail edges k) = ⊤) ∧
        (liminf (perronCost lamStar g) atTop < ⊤ →
          ∃ E : ℕ → Set UnitAddCircle,
            circleExactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
        (liminf (perronCost lamStar g) atTop = ⊤ →
          ¬ ∃ E : ℕ → Set UnitAddCircle,
            circleExactTail edges k ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤)) := by
  have h := thm_finite_state_tail_circle_unconditional edges k hk hlabels hdet
  by_cases hcyc : HasMarkedCycle edges k
  · obtain ⟨lamStar, hlam1, hcnt, hsup⟩ := h.2 hcyc
    rcases eq_or_lt_of_le hlam1 with rfl | hgt
    · exact Or.inr (Or.inl (hcnt rfl))
    · exact Or.inr (Or.inr ⟨lamStar, hgt, hsup hgt⟩)
  · exact Or.inl (h.1 hcyc)

end

end FiniteStateUnconditional
