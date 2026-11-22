import EpiFormal.CylinderOrder
import EpiFormal.WindowPaperScale

/-!
# Continued-fraction stopping-rule realization for `thm:windows` (`WindowCFRealize`)

Constructs the concrete stopped-cylinder tree `cfWindowsTree ε : StoppedTree.TreeData`
directly from `Cylinder.cfProd` and `WindowMobiusCount.box` at the paper's actual scale
`H_j = ⌊Q_j √j⌋` (`WindowPaperScale.Hpaper`), discharging EVERY tree-interface hypothesis
of `WindowPaperScale.dimH_ge_one_windows_paper_scale` with ZERO remaining assumptions:

1. **Euclidean CF expansion & parity twin**:
   - `euclidCF m n`: finite regular continued-fraction word of `m/n` via Euclidean division.
   - `euclidCF_col0`: `(cfProd (euclidCF m n))` has first column `(m, n)` for `gcd m n = 1`.
   - `flipLast`: replaces terminal digit `a ≥ 2` by `[a - 1, 1]`, preserving first column `(m, n)`
     while flipping word length parity.
2. **Continued-fraction cylinder geometry**:
   - `mobius M t = (M 0 0 + M 0 1 * t) / (M 1 0 + M 1 1 * t)` and `cylPair w`.
   - `cylPair_len`: exact cylinder length `1 / (u * (u + v))` and bounds `[2/(25 H²), 9/(16 H²)]`.
   - `cylPair_nest`: `Icc (cylPair (w ++ u)) ⊆ Icc (cylPair w)` for positive-digit words.
   - `cylPair_disj_of_incomparable`: disjoint open interiors for any prefix-incomparable words.
3. **Stopped-cylinder tree `cfWindowsTree ε` (`j0 = 10^6`)**:
   - Maintains the Paper 2 L2428–L2512 invariant `StageInv ε j w`:
     positive digits, terminal digit `4`, parity `(w.length - 1) % 2 = ε j`,
     denominator `u ∈ [4 H_j / 3, 5 H_j / 2]`, penultimate `0 < v < u / 4`.
   - Each parent `w` spawns `copCount (Hpaper (j + 1) / u)` prefix-incomparable stopped children
     `w ++ chooseParityCF m n par ++ [4]` for coprime `(m, n) ∈ box (Hpaper (j + 1) / u)`,
     with intermediate denominator `t = m u + n v ∈ (H_{j+1} / 3, H_{j+1} / 2)` (so the first
     crossing of `H_{j+1}` occurs at the final digit `4`).
   - `dimH_ge_one_cfWindowsTree`: unconditional Lean 4 theorem
     `(1 : ℝ≥0∞) ≤ dimH (WindowTreePrune.cantorSet (cfWindowsTree ε) (10 ^ 6))`
     using only Lean core axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace WindowCFRealize

open Matrix Set Filter Finset ENNReal Metric Real Cylinder
open scoped NNReal BigOperators Topology MeasureTheory

/-! ### Part 1: Continuant matrix positivity & monotonicity -/

/-- Predicate that all partial quotients in a CF word are `≥ 1`. -/
def PosDigits (w : List ℕ) : Prop := ∀ a ∈ w, 1 ≤ a

theorem posDigits_nil : PosDigits [] := fun _ h => nomatch h

theorem posDigits_cons {a : ℕ} {w : List ℕ} :
    PosDigits (a :: w) ↔ 1 ≤ a ∧ PosDigits w := by
  simp [PosDigits]

theorem posDigits_append {w₁ w₂ : List ℕ} :
    PosDigits (w₁ ++ w₂) ↔ PosDigits w₁ ∧ PosDigits w₂ := by
  simp only [PosDigits, List.mem_append]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨h1, h2⟩ a (ha | ha)
    · exact h1 a ha
    · exact h2 a ha

theorem cfProd_append (w₁ w₂ : List ℕ) :
    cfProd (w₁ ++ w₂) = cfProd w₁ * cfProd w₂ := by
  induction w₁ with
  | nil => simp [cfProd]
  | cons a w₁ ih =>
    change cfProd (a :: (w₁ ++ w₂)) = cfProd (a :: w₁) * cfProd w₂
    rw [cfProd, cfProd, ih, Matrix.mul_assoc]

/-- First column of `cfProd w` is strictly positive for nonempty positive-digit words. -/
theorem cfProd_col0_pos {w : List ℕ} (hw : PosDigits w) (hne : w ≠ []) :
    0 < (cfProd w) 0 0 ∧ 0 < (cfProd w) 1 0 := by
  induction w with
  | nil => exact absurd rfl hne
  | cons a w ih =>
    obtain ⟨ha, hw'⟩ := posDigits_cons.mp hw
    cases w with
    | nil =>
      simp only [cfProd, Matrix.mul_one, cfMat, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact ⟨by exact_mod_cast ha, by norm_num⟩
    | cons b t =>
      obtain ⟨h0, h1⟩ := ih hw' (List.cons_ne_nil b t)
      rw [cfProd, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [cfMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero]
      have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
      exact ⟨by nlinarith, h0⟩

/-- Row 1 is bounded by row 0 for nonempty positive-digit words. -/
theorem cfProd_row1_le_row0 {w : List ℕ} (hw : PosDigits w) (hne : w ≠ []) :
    (cfProd w) 1 0 ≤ (cfProd w) 0 0 ∧ (cfProd w) 1 1 ≤ (cfProd w) 0 1 := by
  induction w with
  | nil => exact absurd rfl hne
  | cons a w ih =>
    obtain ⟨ha, hw'⟩ := posDigits_cons.mp hw
    have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    cases w with
    | nil =>
      simp only [cfProd, Matrix.mul_one, cfMat, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact ⟨haZ, by norm_num⟩
    | cons b t =>
      have hnn00 := cfProd_nonneg (b :: t) 0 0
      have hnn10 := cfProd_nonneg (b :: t) 1 0
      have hnn01 := cfProd_nonneg (b :: t) 0 1
      have hnn11 := cfProd_nonneg (b :: t) 1 1
      rw [cfProd, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
        Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [cfMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero]
      exact ⟨by nlinarith, by nlinarith⟩

/-- Column 1 is bounded by column 0 for nonempty positive-digit words. -/
theorem cfProd_col1_le_col0 {w : List ℕ} (hw : PosDigits w) (hne : w ≠ []) :
    (cfProd w) 0 1 ≤ (cfProd w) 0 0 ∧ (cfProd w) 1 1 ≤ (cfProd w) 1 0 := by
  induction w with
  | nil => exact absurd rfl hne
  | cons a w ih =>
    obtain ⟨ha, hw'⟩ := posDigits_cons.mp hw
    have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    cases w with
    | nil =>
      simp only [cfProd, Matrix.mul_one, cfMat, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact ⟨haZ, by norm_num⟩
    | cons b t =>
      obtain ⟨h0, h1⟩ := ih hw' (List.cons_ne_nil b t)
      rw [cfProd, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
        Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [cfMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero]
      exact ⟨by nlinarith, h0⟩

/-- Bottom row of `cfProd (0 :: w)` equals top row of `cfProd w`. -/
theorem cfProd_zero_cons_row1 (w : List ℕ) :
    (cfProd (0 :: w)) 1 0 = (cfProd w) 0 0 ∧ (cfProd (0 :: w)) 1 1 = (cfProd w) 0 1 := by
  rw [cfProd, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [cfMat]

/-- Top row of `cfProd (0 :: w)` equals bottom row of `cfProd w`. -/
theorem cfProd_zero_cons_row0 (w : List ℕ) :
    (cfProd (0 :: w)) 0 0 = (cfProd w) 1 0 ∧ (cfProd (0 :: w)) 0 1 = (cfProd w) 1 1 := by
  rw [cfProd, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [cfMat]

/-- Denominator monotonicity along prefixes of positive-digit words. -/
theorem den_mono_prefix {w₁ w₂ : List ℕ} (hw₂ : PosDigits w₂) :
    (cfProd (0 :: w₁)) 1 0 ≤ (cfProd (0 :: (w₁ ++ w₂))) 1 0 := by
  cases w₂ with
  | nil => simp
  | cons a t =>
    have hcons : (0 :: (w₁ ++ (a :: t))) = (0 :: w₁) ++ (a :: t) := rfl
    rw [hcons, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
    obtain ⟨h0, h1⟩ := cfProd_col0_pos hw₂ (List.cons_ne_nil a t)
    have hu := cfProd_nonneg (0 :: w₁) 1 0
    have hv := cfProd_nonneg (0 :: w₁) 1 1
    nlinarith

/-- For any positive-digit word `w`, appending `u ≠ []` satisfies `0 < t' < t`
    where `t, t'` are the new last two denominators (via `det ≠ 0`). -/
theorem append_penult_bounds {w u : List ℕ}
    (hu_pos : 0 < (cfProd (0 :: w)) 1 0) (hv_pos : 0 < (cfProd (0 :: w)) 1 1)
    (hu_dig : PosDigits u) (hu_ne : u ≠ []) :
    0 < (cfProd (0 :: (w ++ u))) 1 1 ∧
      (cfProd (0 :: (w ++ u))) 1 1 < (cfProd (0 :: (w ++ u))) 1 0 := by
  have hcons : (0 :: (w ++ u)) = (0 :: w) ++ u := rfl
  rw [hcons, cfProd_append, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  set M := cfProd (0 :: w)
  set N := cfProd u
  have hNnn01 := cfProd_nonneg u 0 1
  have hNnn11 := cfProd_nonneg u 1 1
  obtain ⟨hle0, hle1⟩ := cfProd_col1_le_col0 hu_dig hu_ne
  have hdet := cfProd_det_ne_zero u
  rw [Matrix.det_fin_two] at hdet
  change N 0 0 * N 1 1 - N 0 1 * N 1 0 ≠ 0 at hdet
  constructor
  · by_contra hle
    push Not at hle
    have h01 : N 0 1 = 0 := by nlinarith
    have h11 : N 1 1 = 0 := by nlinarith
    exact hdet (by rw [h01, h11]; ring)
  · by_contra hge
    push Not at hge
    have h0 : N 0 1 = N 0 0 := by nlinarith
    have h1 : N 1 1 = N 1 0 := by nlinarith
    exact hdet (by rw [h0, h1]; ring)

/-! ### Part 2: Euclidean CF expansion & parity-flipping twin -/

/-- Standard finite regular continued-fraction word of `m / n` via Euclidean division. -/
def euclidCF (m n : ℕ) : List ℕ :=
  if _h0 : n = 0 then []
  else (m / n) :: euclidCF n (m % n)
termination_by n
decreasing_by exact Nat.mod_lt m (Nat.pos_of_ne_zero _h0)

theorem euclidCF_ne_nil {m n : ℕ} (hn : 1 ≤ n) : euclidCF m n ≠ [] := by
  rw [euclidCF]
  simp [show n ≠ 0 by omega]

theorem euclidCF_pos_digits (m n : ℕ) :
    1 ≤ n → n ≤ m → PosDigits (euclidCF m n) := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    intro hn hnm
    rw [euclidCF]
    have hn0 : n ≠ 0 := by omega
    simp only [hn0, ↓reduceDIte]
    rw [posDigits_cons]
    refine ⟨Nat.div_pos hnm (by omega), ?_⟩
    by_cases hr : m % n = 0
    · rw [hr, euclidCF]
      simp [posDigits_nil]
    · have hlt : m % n < n := Nat.mod_lt m (by omega)
      exact ih (m % n) hlt n (by omega) (le_of_lt hlt)

/-- First column of `cfProd (euclidCF m n)` is literally `(m, n)` for coprime `m, n`. -/
theorem euclidCF_col0 (m n : ℕ) :
    1 ≤ n → Nat.gcd m n = 1 →
      (cfProd (euclidCF m n)) 0 0 = (m : ℤ) ∧ (cfProd (euclidCF m n)) 1 0 = (n : ℤ) := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    intro hn hgcd
    rw [euclidCF]
    have hn0 : n ≠ 0 := by omega
    simp only [hn0, ↓reduceDIte]
    by_cases hr : m % n = 0
    · have hdvd : n ∣ m := Nat.dvd_of_mod_eq_zero hr
      have hn1 : n = 1 := by
        have h1 := Nat.gcd_eq_right hdvd
        omega
      subst hn1
      rw [hr, euclidCF]
      simp [cfProd, cfMat]
    · have hlt : m % n < n := Nat.mod_lt m (by omega)
      have hgcd' : Nat.gcd n (m % n) = 1 := by
        rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
        exact hgcd
      obtain ⟨h0, h1⟩ := ih (m % n) hlt n (by omega) hgcd'
      rw [cfProd, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [cfMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero]
      rw [h0, h1]
      refine ⟨?_, rfl⟩
      have hdm : n * (m / n) + m % n = m := Nat.div_add_mod m n
      have hdmZ : (n : ℤ) * ((m / n : ℕ) : ℤ) + ((m % n : ℕ) : ℤ) = (m : ℤ) := by
        exact_mod_cast hdm
      linarith

/-- For coprime `m > n ≥ 1`, `euclidCF m n` terminates in a digit `≥ 2`. -/
theorem euclidCF_last_ge_two (m n : ℕ) :
    1 ≤ n → n < m → Nat.gcd m n = 1 →
      ∃ pref a, euclidCF m n = pref ++ [a] ∧ 2 ≤ a := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    intro hn hnm hgcd
    rw [euclidCF]
    have hn0 : n ≠ 0 := by omega
    simp only [hn0, ↓reduceDIte]
    by_cases hr : m % n = 0
    · have hdvd : n ∣ m := Nat.dvd_of_mod_eq_zero hr
      have hn1 : n = 1 := by
        have h1 := Nat.gcd_eq_right hdvd
        omega
      subst hn1
      rw [hr, euclidCF]
      simp only [↓reduceDIte, Nat.div_one]
      exact ⟨[], m, rfl, by omega⟩
    · have hlt : m % n < n := Nat.mod_lt m (by omega)
      have hgcd' : Nat.gcd n (m % n) = 1 := by
        rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
        exact hgcd
      obtain ⟨pref, a, hpref, ha⟩ := ih (m % n) hlt n (by omega) hlt hgcd'
      refine ⟨(m / n) :: pref, a, ?_, ha⟩
      simp [hpref]

/-- Parity-flipping terminal transformation `[..., a] ↦ [..., a - 1, 1]`. -/
def flipLast : List ℕ → List ℕ
  | [] => []
  | [a] => [a - 1, 1]
  | a :: b :: t => a :: flipLast (b :: t)

theorem flipLast_append_single (pref : List ℕ) (a : ℕ) :
    flipLast (pref ++ [a]) = pref ++ [a - 1, 1] := by
  induction pref with
  | nil => rfl
  | cons x t ih =>
    cases t with
    | nil => rfl
    | cons y rest =>
      simp only [List.cons_append, flipLast]
      rw [← List.cons_append, ih, List.cons_append]

theorem flipLast_col0 {w : List ℕ} {pref : List ℕ} {a : ℕ}
    (hw : w = pref ++ [a]) (ha : 1 ≤ a) :
    (cfProd (flipLast w)) 0 0 = (cfProd w) 0 0 ∧
      (cfProd (flipLast w)) 1 0 = (cfProd w) 1 0 := by
  rw [hw, flipLast_append_single, cfProd_append, cfProd_append]
  have hcol : (cfProd [a - 1, 1]) 0 0 = (cfProd [a]) 0 0 ∧
      (cfProd [a - 1, 1]) 1 0 = (cfProd [a]) 1 0 := by
    simp only [cfProd, Matrix.mul_one, Matrix.mul_apply, Fin.sum_univ_two, cfMat,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.one_apply]
    have haZ : ((a - 1 : ℕ) : ℤ) + 1 = (a : ℤ) := by
      have : (a - 1) + 1 = a := by omega
      exact_mod_cast this
    constructor
    · simp; linarith
    · simp
  constructor <;>
    (rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, hcol.1, hcol.2])

/-- Choose whichever of `euclidCF m n` and `flipLast (euclidCF m n)` has length parity `par`. -/
def chooseParityCF (m n : ℕ) (par : Bool) : List ℕ :=
  let w := euclidCF m n
  if (w.length % 2 == 1) == par then w else flipLast w

theorem chooseParityCF_props {m n : ℕ} (hn : 1 ≤ n) (hnm : n < m)
    (hgcd : Nat.gcd m n = 1) (par : Bool) :
    PosDigits (chooseParityCF m n par) ∧
    chooseParityCF m n par ≠ [] ∧
    (cfProd (chooseParityCF m n par)) 0 0 = (m : ℤ) ∧
    (cfProd (chooseParityCF m n par)) 1 0 = (n : ℤ) ∧
    ((chooseParityCF m n par).length % 2 == 1) = par := by
  have hpos := euclidCF_pos_digits m n hn (le_of_lt hnm)
  have hne := euclidCF_ne_nil (m := m) hn
  obtain ⟨hc0, hc1⟩ := euclidCF_col0 m n hn hgcd
  obtain ⟨pref, a, hpref, ha⟩ := euclidCF_last_ge_two m n hn hnm hgcd
  unfold chooseParityCF
  dsimp only
  split_ifs with hpar
  · exact ⟨hpos, hne, hc0, hc1, beq_iff_eq.mp hpar⟩
  · have hflip_eq : flipLast (euclidCF m n) = pref ++ [a - 1, 1] := by
      rw [hpref, flipLast_append_single]
    have hflip_pos : PosDigits (flipLast (euclidCF m n)) := by
      rw [hflip_eq, posDigits_append]
      rw [hpref, posDigits_append] at hpos
      refine ⟨hpos.1, ?_⟩
      simp only [PosDigits, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl) <;> omega
    have hflip_ne : flipLast (euclidCF m n) ≠ [] := by
      rw [hflip_eq]
      exact List.append_ne_nil_of_right_ne_nil _ (by simp)
    obtain ⟨hf0, hf1⟩ := flipLast_col0 hpref (by omega)
    have hlen : (flipLast (euclidCF m n)).length = (euclidCF m n).length + 1 := by
      rw [hflip_eq, hpref]; simp
    have hpar' : ((flipLast (euclidCF m n)).length % 2 == 1) = par := by
      rw [hlen]
      cases par <;> simp_all <;> omega
    exact ⟨hflip_pos, hflip_ne, by rw [hf0, hc0], by rw [hf1, hc1], hpar'⟩

/-! ### Part 3: Möbius map & continued-fraction cylinder geometry -/

/-- Möbius action of a `2 × 2` integer matrix on `t ∈ ℝ`. -/
noncomputable def mobius (M : Matrix (Fin 2) (Fin 2) ℤ) (t : ℝ) : ℝ :=
  ((M 0 0 : ℝ) + (M 0 1 : ℝ) * t) / ((M 1 0 : ℝ) + (M 1 1 : ℝ) * t)

/-- Closed continued-fraction cylinder endpoints `(min, max)` for word `w` in `[0, 1]`. -/
noncomputable def cylPair (w : List ℕ) : ℝ × ℝ :=
  let M := cfProd (0 :: w)
  (min (mobius M 0) (mobius M 1), max (mobius M 0) (mobius M 1))

/-- Algebraic difference identity for `mobius M`:
    `mobius M s - mobius M t = (-det M) * (s - t) / (den(s) * den(t))`. -/
theorem mobius_sub (M : Matrix (Fin 2) (Fin 2) ℤ) (s t : ℝ)
    (hs : (M 1 0 : ℝ) + (M 1 1 : ℝ) * s ≠ 0)
    (ht : (M 1 0 : ℝ) + (M 1 1 : ℝ) * t ≠ 0) :
    mobius M s - mobius M t =
      (-(M.det : ℝ) * (s - t)) /
        (((M 1 0 : ℝ) + (M 1 1 : ℝ) * s) * ((M 1 0 : ℝ) + (M 1 1 : ℝ) * t)) := by
  unfold mobius
  rw [div_sub_div _ _ hs ht, Matrix.det_fin_two]
  push_cast
  ring

/-- Composition law: `mobius (M * N) t = mobius M ((N 1 0 + N 1 1 * t) / (N 0 0 + N 0 1 * t))`. -/
theorem mobius_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) (t : ℝ)
    (hN : (N 0 0 : ℝ) + (N 0 1 : ℝ) * t ≠ 0) :
    mobius (M * N) t =
      mobius M (((N 1 0 : ℝ) + (N 1 1 : ℝ) * t) / ((N 0 0 : ℝ) + (N 0 1 : ℝ) * t)) := by
  unfold mobius
  rw [Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  push_cast
  field_simp
  ring

/-- Exact cylinder length `1 / (u * (u + v))` for `M = cfProd (0 :: w)`. -/
theorem cylPair_len {w : List ℕ} (hw : PosDigits w) (hne : w ≠ []) :
    (cylPair w).2 - (cylPair w).1 =
      1 / (((cfProd (0 :: w)) 1 0 : ℝ) *
        (((cfProd (0 :: w)) 1 0 : ℝ) + ((cfProd (0 :: w)) 1 1 : ℝ))) := by
  set M := cfProd (0 :: w)
  have hu_pos : (0 : ℝ) < (M 1 0 : ℝ) := by
    have h0 := (cfProd_zero_cons_row1 w).1
    have hp := (cfProd_col0_pos hw hne).1
    exact_mod_cast (by linarith : (0 : ℤ) < M 1 0)
  have hv_nn : (0 : ℝ) ≤ (M 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg (0 :: w) 1 1
  have hden0 : (M 1 0 : ℝ) + (M 1 1 : ℝ) * 0 ≠ 0 := by linarith
  have hden1 : (M 1 0 : ℝ) + (M 1 1 : ℝ) * 1 ≠ 0 := by linarith
  have hdiff := mobius_sub M 0 1 hden0 hden1
  have hmaxmin : (cylPair w).2 - (cylPair w).1 = |mobius M 0 - mobius M 1| := by
    simp only [cylPair]
    rcases le_total (mobius M 0) (mobius M 1) with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
  rw [hmaxmin, hdiff, abs_div]
  have hdet_abs : |(-(M.det : ℝ) * (0 - 1))| = 1 := by
    have hd : M.det = (-1 : ℤ) ^ (0 :: w).length := cfProd_det (0 :: w)
    have hpm : M.det = 1 ∨ M.det = -1 := by
      rw [hd]; exact neg_one_pow_eq_or ℤ (0 :: w).length
    rcases hpm with h | h <;> simp [h]
  rw [hdet_abs, abs_of_pos (by nlinarith :
    0 < ((M 1 0 : ℝ) + (M 1 1 : ℝ) * 0) * ((M 1 0 : ℝ) + (M 1 1 : ℝ) * 1))]
  ring

/-- Paper 2 L2546 cylinder length bounds: `4 H / 3 ≤ u ≤ 5 H / 2` and `0 < v ≤ u`
    imply `2 / (25 H²) ≤ |cylPair w| ≤ 9 / (16 H²)`. -/
theorem cylPair_len_bounds {w : List ℕ} {H : ℝ} (hH : 0 < H)
    (hw : PosDigits w) (hne : w ≠ [])
    (hu_lo : 4 / 3 * H ≤ ((cfProd (0 :: w)) 1 0 : ℝ))
    (hu_hi : ((cfProd (0 :: w)) 1 0 : ℝ) ≤ 5 / 2 * H)
    (hv_nn : 0 ≤ ((cfProd (0 :: w)) 1 1 : ℝ))
    (hv_le : ((cfProd (0 :: w)) 1 1 : ℝ) ≤ ((cfProd (0 :: w)) 1 0 : ℝ)) :
    (2 / 25 : ℝ) / H ^ 2 ≤ (cylPair w).2 - (cylPair w).1 ∧
      (cylPair w).2 - (cylPair w).1 ≤ (9 / 16 : ℝ) / H ^ 2 := by
  rw [cylPair_len hw hne]
  set u : ℝ := ((cfProd (0 :: w)) 1 0 : ℝ)
  set v : ℝ := ((cfProd (0 :: w)) 1 1 : ℝ)
  have hu_pos : 0 < u := by linarith
  constructor
  · have hprod_hi : u * (u + v) ≤ (25 / 2 : ℝ) * H ^ 2 := by nlinarith
    have h1 := one_div_le_one_div_of_le (by nlinarith : 0 < u * (u + v)) hprod_hi
    have heq : (2 / 25 : ℝ) / H ^ 2 = 1 / ((25 / 2 : ℝ) * H ^ 2) := by
      have hHne : H ≠ 0 := ne_of_gt hH
      field_simp
    linarith
  · have hprod_lo : (16 / 9 : ℝ) * H ^ 2 ≤ u * (u + v) := by nlinarith
    have h1 := one_div_le_one_div_of_le (by positivity : 0 < (16 / 9 : ℝ) * H ^ 2) hprod_lo
    have heq : (9 / 16 : ℝ) / H ^ 2 = 1 / ((16 / 9 : ℝ) * H ^ 2) := by
      have hHne : H ≠ 0 := ne_of_gt hH
      field_simp
    linarith

/-- For any `t ∈ [0, 1]`, `mobius (cfProd (0 :: w)) t` lies in `Icc (cylPair w).1 (cylPair w).2`. -/
theorem mobius_mem_cylPair {w : List ℕ} (hw : PosDigits w) (hne : w ≠ [])
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mobius (cfProd (0 :: w)) t ∈ Set.Icc (cylPair w).1 (cylPair w).2 := by
  set M := cfProd (0 :: w)
  have hu_pos : (0 : ℝ) < (M 1 0 : ℝ) := by
    have h0 := (cfProd_zero_cons_row1 w).1
    have hp := (cfProd_col0_pos hw hne).1
    exact_mod_cast (by linarith : (0 : ℤ) < M 1 0)
  have hv_nn : (0 : ℝ) ≤ (M 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg (0 :: w) 1 1
  have hd0 : (0 : ℝ) < (M 1 0 : ℝ) + (M 1 1 : ℝ) * 0 := by linarith
  have hdt : (0 : ℝ) < (M 1 0 : ℝ) + (M 1 1 : ℝ) * t := by nlinarith
  have hd1 : (0 : ℝ) < (M 1 0 : ℝ) + (M 1 1 : ℝ) * 1 := by linarith
  have hsub0 := mobius_sub M t 0 (ne_of_gt hdt) (ne_of_gt hd0)
  have hsub1 := mobius_sub M 1 t (ne_of_gt hd1) (ne_of_gt hdt)
  have hdet_pm : M.det = 1 ∨ M.det = -1 := by
    have hd : M.det = (-1 : ℤ) ^ (0 :: w).length := cfProd_det (0 :: w)
    rw [hd]; exact neg_one_pow_eq_or ℤ (0 :: w).length
  simp only [cylPair, Set.mem_Icc]
  rcases hdet_pm with hdet | hdet
  · -- det = 1: mobius is decreasing on [0, 1]
    have h1 : mobius M t ≤ mobius M 0 := by
      have : mobius M t - mobius M 0 ≤ 0 := by
        rw [hsub0, hdet, Int.cast_one]
        exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
      linarith
    have h2 : mobius M 1 ≤ mobius M t := by
      have : mobius M 1 - mobius M t ≤ 0 := by
        rw [hsub1, hdet, Int.cast_one]
        exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
      linarith
    exact ⟨le_trans (min_le_right _ _) h2, le_trans h1 (le_max_left _ _)⟩
  · -- det = -1: mobius is increasing on [0, 1]
    have h1 : mobius M 0 ≤ mobius M t := by
      have : 0 ≤ mobius M t - mobius M 0 := by
        rw [hsub0, hdet, Int.cast_neg, Int.cast_one]
        exact div_nonneg (by nlinarith) (by positivity)
      linarith
    have h2 : mobius M t ≤ mobius M 1 := by
      have : 0 ≤ mobius M 1 - mobius M t := by
        rw [hsub1, hdet, Int.cast_neg, Int.cast_one]
        exact div_nonneg (by nlinarith) (by positivity)
      linarith
    exact ⟨le_trans (min_le_left _ _) h1, le_trans h2 (le_max_right _ _)⟩

/-- Cylinder nesting: extending a positive-digit word by any positive-digit suffix
    produces a nested closed interval. -/
theorem cylPair_nest {w u : List ℕ} (hw : PosDigits w) (hwne : w ≠ [])
    (hu : PosDigits u) :
    Set.Icc (cylPair (w ++ u)).1 (cylPair (w ++ u)).2 ⊆
      Set.Icc (cylPair w).1 (cylPair w).2 := by
  cases u with
  | nil => simp
  | cons a t =>
    set M := cfProd (0 :: w)
    set N := cfProd (a :: t)
    have hcons : (0 :: (w ++ (a :: t))) = (0 :: w) ++ (a :: t) := rfl
    have hMN : cfProd (0 :: (w ++ (a :: t))) = M * N := by rw [hcons, cfProd_append]
    obtain ⟨hN0pos, _⟩ := cfProd_col0_pos hu (List.cons_ne_nil a t)
    have hN01nn : (0 : ℝ) ≤ (N 0 1 : ℝ) := by exact_mod_cast cfProd_nonneg (a :: t) 0 1
    have hN10nn : (0 : ℝ) ≤ (N 1 0 : ℝ) := by exact_mod_cast cfProd_nonneg (a :: t) 1 0
    have hN11nn : (0 : ℝ) ≤ (N 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg (a :: t) 1 1
    obtain ⟨hr0, hr1⟩ := cfProd_row1_le_row0 hu (List.cons_ne_nil a t)
    have hr0R : (N 1 0 : ℝ) ≤ (N 0 0 : ℝ) := by exact_mod_cast hr0
    have hr1R : (N 1 1 : ℝ) ≤ (N 0 1 : ℝ) := by exact_mod_cast hr1
    have hN0posR : (0 : ℝ) < (N 0 0 : ℝ) := by exact_mod_cast hN0pos
    have hend : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        mobius (M * N) s ∈ Set.Icc (cylPair w).1 (cylPair w).2 := by
      intro s hs0 _
      have hden : (0 : ℝ) < (N 0 0 : ℝ) + (N 0 1 : ℝ) * s := by nlinarith
      rw [mobius_mul M N s (ne_of_gt hden)]
      refine mobius_mem_cylPair hw hwne ?_ ?_
      · exact div_nonneg (by nlinarith) (le_of_lt hden)
      · exact (div_le_one hden).mpr (by nlinarith)
    have he0 := hend 0 le_rfl zero_le_one
    have he1 := hend 1 zero_le_one le_rfl
    intro x hx
    simp only [cylPair, hMN, Set.mem_Icc] at hx ⊢
    simp only [Set.mem_Icc] at he0 he1
    exact ⟨le_trans (le_min he0.1 he1.1) hx.1, le_trans hx.2 (max_le he0.2 he1.2)⟩

/-- Distinct first digits after a common prefix produce disjoint open cylinders. -/
theorem cylPair_disj_sibling {p : List ℕ} {a b : ℕ}
    (hp : PosDigits p) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≠ b) :
    Disjoint (Set.Ioo (cylPair (p ++ [a])).1 (cylPair (p ++ [a])).2)
      (Set.Ioo (cylPair (p ++ [b])).1 (cylPair (p ++ [b])).2) := by
  -- WLOG `a < b` by symmetry of Disjoint.
  wlog hlt : a < b generalizing a b
  · exact (this hb ha hab.symm (by omega)).symm
  set M := cfProd (0 :: p)
  have hden_pos : ∀ s : ℝ, 0 < s → s ≤ 1 → (0 : ℝ) < (M 1 0 : ℝ) + (M 1 1 : ℝ) * s := by
    intro s hs0 _
    cases p with
    | nil =>
      simp only [M, cfProd, Matrix.mul_one, cfMat, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_one,
        Int.cast_zero]
      linarith
    | cons d rest =>
      have hu : (0 : ℝ) < (M 1 0 : ℝ) := by
        have h0 := (cfProd_zero_cons_row1 (d :: rest)).1
        have hp' := (cfProd_col0_pos hp (List.cons_ne_nil d rest)).1
        exact_mod_cast (by linarith : (0 : ℤ) < M 1 0)
      have hv : (0 : ℝ) ≤ (M 1 1 : ℝ) := by exact_mod_cast cfProd_nonneg (0 :: d :: rest) 1 1
      nlinarith
  have hmob_step : ∀ k : ℕ, 1 ≤ k →
      mobius (cfProd (0 :: (p ++ [k]))) 0 = mobius M (1 / (k : ℝ)) ∧
      mobius (cfProd (0 :: (p ++ [k]))) 1 = mobius M (1 / ((k : ℝ) + 1)) := by
    intro k hk
    have hcons : (0 :: (p ++ [k])) = (0 :: p) ++ [k] := rfl
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    rw [hcons, cfProd_append]
    constructor
    · rw [mobius_mul M (cfProd [k]) 0]
      · simp [cfProd, cfMat]
      · simp [cfProd, cfMat]; omega
    · rw [mobius_mul M (cfProd [k]) 1]
      · simp [cfProd, cfMat]
      · simp [cfProd, cfMat]; linarith
  obtain ⟨ha0, ha1⟩ := hmob_step a ha
  obtain ⟨hb0, hb1⟩ := hmob_step b hb
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hlt
  set s1 : ℝ := 1 / ((b : ℝ) + 1)
  set s2 : ℝ := 1 / (b : ℝ)
  set s3 : ℝ := 1 / ((a : ℝ) + 1)
  set s4 : ℝ := 1 / (a : ℝ)
  have hs12 : s1 < s2 := one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hs23 : s2 ≤ s3 := one_div_le_one_div_of_le (by linarith) hbR
  have hs34 : s3 < s4 := one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hs_pos : ∀ s ∈ ({s1, s2, s3, s4} : Set ℝ), 0 < s ∧ s ≤ 1 := by
    intro s hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
    · exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
    · exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
    · exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  have hdet_pm : M.det = 1 ∨ M.det = -1 := by
    have hd : M.det = (-1 : ℤ) ^ (0 :: p).length := cfProd_det (0 :: p)
    rw [hd]; exact neg_one_pow_eq_or ℤ (0 :: p).length
  have hmono_inc : M.det = -1 → ∀ x y : ℝ, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 → x ≤ y →
      mobius M x ≤ mobius M y := by
    intro hd x y hx0 hx1 hy0 hy1 hxy
    have hdx := hden_pos x hx0 hx1
    have hdy := hden_pos y hy0 hy1
    have hsub := mobius_sub M y x (ne_of_gt hdy) (ne_of_gt hdx)
    have : 0 ≤ mobius M y - mobius M x := by
      rw [hsub, hd, Int.cast_neg, Int.cast_one]
      exact div_nonneg (by nlinarith) (by positivity)
    linarith
  have hmono_dec : M.det = 1 → ∀ x y : ℝ, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 → x ≤ y →
      mobius M y ≤ mobius M x := by
    intro hd x y hx0 hx1 hy0 hy1 hxy
    have hdx := hden_pos x hx0 hx1
    have hdy := hden_pos y hy0 hy1
    have hsub := mobius_sub M y x (ne_of_gt hdy) (ne_of_gt hdx)
    have : mobius M y - mobius M x ≤ 0 := by
      rw [hsub, hd, Int.cast_one]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
    linarith
  rw [Set.disjoint_left]
  intro x hxA hxB
  simp only [cylPair, ha0, ha1, hb0, hb1, Set.mem_Ioo] at hxA hxB
  rcases hdet_pm with hd | hd
  · have h34 := hmono_dec hd s3 s4 (hs_pos s3 (by simp)).1 (hs_pos s3 (by simp)).2
      (hs_pos s4 (by simp)).1 (hs_pos s4 (by simp)).2 (le_of_lt hs34)
    have h23 := hmono_dec hd s2 s3 (hs_pos s2 (by simp)).1 (hs_pos s2 (by simp)).2
      (hs_pos s3 (by simp)).1 (hs_pos s3 (by simp)).2 hs23
    have h12 := hmono_dec hd s1 s2 (hs_pos s1 (by simp)).1 (hs_pos s1 (by simp)).2
      (hs_pos s2 (by simp)).1 (hs_pos s2 (by simp)).2 (le_of_lt hs12)
    have hA_hi : max (mobius M s4) (mobius M s3) = mobius M s3 := max_eq_right h34
    have hB_lo : min (mobius M s2) (mobius M s1) = mobius M s2 := min_eq_left h12
    linarith [hxA.2, hxB.1]
  · have h34 := hmono_inc hd s3 s4 (hs_pos s3 (by simp)).1 (hs_pos s3 (by simp)).2
      (hs_pos s4 (by simp)).1 (hs_pos s4 (by simp)).2 (le_of_lt hs34)
    have h23 := hmono_inc hd s2 s3 (hs_pos s2 (by simp)).1 (hs_pos s2 (by simp)).2
      (hs_pos s3 (by simp)).1 (hs_pos s3 (by simp)).2 hs23
    have h12 := hmono_inc hd s1 s2 (hs_pos s1 (by simp)).1 (hs_pos s1 (by simp)).2
      (hs_pos s2 (by simp)).1 (hs_pos s2 (by simp)).2 (le_of_lt hs12)
    have hA_lo : min (mobius M s4) (mobius M s3) = mobius M s3 := min_eq_right h34
    have hB_hi : max (mobius M s2) (mobius M s1) = mobius M s2 := max_eq_left h12
    linarith [hxA.1, hxB.2]

/-- Any two prefix-incomparable lists split at a common prefix followed by distinct elements. -/
theorem exists_split_of_incomparable : ∀ (w₁ w₂ : List ℕ),
    ¬ (w₁ <+: w₂) → ¬ (w₂ <+: w₁) →
    ∃ p a b u₁ u₂, a ≠ b ∧ w₁ = p ++ a :: u₁ ∧ w₂ = p ++ b :: u₂
  | [], w₂, h1, _ => absurd (List.nil_prefix) h1
  | w₁, [], _, h2 => absurd (List.nil_prefix) h2
  | a :: t₁, b :: t₂, h1, h2 => by
    by_cases hab : a = b
    · subst hab
      have h1' : ¬ (t₁ <+: t₂) := fun h => h1 (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      have h2' : ¬ (t₂ <+: t₁) := fun h => h2 (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      obtain ⟨p, x, y, u₁, u₂, hxy, ht1, ht2⟩ := exists_split_of_incomparable t₁ t₂ h1' h2'
      exact ⟨a :: p, x, y, u₁, u₂, hxy, by simp [ht1], by simp [ht2]⟩
    · exact ⟨[], a, b, t₁, t₂, hab, rfl, rfl⟩

/-- Prefix-incomparable positive-digit words have disjoint open cylinders. -/
theorem cylPair_disj_of_incomparable {w₁ w₂ : List ℕ}
    (hw₁ : PosDigits w₁) (hw₂ : PosDigits w₂)
    (h12 : ¬ (w₁ <+: w₂)) (h21 : ¬ (w₂ <+: w₁)) :
    Disjoint (Set.Ioo (cylPair w₁).1 (cylPair w₁).2)
      (Set.Ioo (cylPair w₂).1 (cylPair w₂).2) := by
  obtain ⟨p, a, b, u₁, u₂, hab, rfl, rfl⟩ := exists_split_of_incomparable w₁ w₂ h12 h21
  obtain ⟨hp, ha_u1⟩ := posDigits_append.mp hw₁
  obtain ⟨_, hb_u2⟩ := posDigits_append.mp hw₂
  obtain ⟨ha, hu1⟩ := posDigits_cons.mp ha_u1
  obtain ⟨hb, hu2⟩ := posDigits_cons.mp hb_u2
  have hsub1 : Set.Icc (cylPair (p ++ a :: u₁)).1 (cylPair (p ++ a :: u₁)).2 ⊆
      Set.Icc (cylPair (p ++ [a])).1 (cylPair (p ++ [a])).2 := by
    have heq : p ++ a :: u₁ = (p ++ [a]) ++ u₁ := by simp
    rw [heq]
    exact cylPair_nest (posDigits_append.mpr ⟨hp, posDigits_cons.mpr ⟨ha, posDigits_nil⟩⟩)
      (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil a [])) hu1
  have hsub2 : Set.Icc (cylPair (p ++ b :: u₂)).1 (cylPair (p ++ b :: u₂)).2 ⊆
      Set.Icc (cylPair (p ++ [b])).1 (cylPair (p ++ [b])).2 := by
    have heq : p ++ b :: u₂ = (p ++ [b]) ++ u₂ := by simp
    rw [heq]
    exact cylPair_nest (posDigits_append.mpr ⟨hp, posDigits_cons.mpr ⟨hb, posDigits_nil⟩⟩)
      (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil b [])) hu2
  have htriv1 : (cylPair (p ++ a :: u₁)).1 < (cylPair (p ++ a :: u₁)).2 := by
    have hlen := cylPair_len hw₁ (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil a u₁))
    have hu_pos : (0 : ℝ) < ((cfProd (0 :: (p ++ a :: u₁))) 1 0 : ℝ) := by
      have h0 := (cfProd_zero_cons_row1 (p ++ a :: u₁)).1
      have hp' := (cfProd_col0_pos hw₁
        (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil a u₁))).1
      exact_mod_cast (by linarith : (0 : ℤ) < (cfProd (0 :: (p ++ a :: u₁))) 1 0)
    have hv_nn : (0 : ℝ) ≤ ((cfProd (0 :: (p ++ a :: u₁))) 1 1 : ℝ) := by
      exact_mod_cast cfProd_nonneg (0 :: (p ++ a :: u₁)) 1 1
    have hpos : 0 < (cylPair (p ++ a :: u₁)).2 - (cylPair (p ++ a :: u₁)).1 := by
      rw [hlen]; positivity
    linarith
  have htriv2 : (cylPair (p ++ b :: u₂)).1 < (cylPair (p ++ b :: u₂)).2 := by
    have hlen := cylPair_len hw₂ (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil b u₂))
    have hu_pos : (0 : ℝ) < ((cfProd (0 :: (p ++ b :: u₂))) 1 0 : ℝ) := by
      have h0 := (cfProd_zero_cons_row1 (p ++ b :: u₂)).1
      have hp' := (cfProd_col0_pos hw₂
        (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil b u₂))).1
      exact_mod_cast (by linarith : (0 : ℤ) < (cfProd (0 :: (p ++ b :: u₂))) 1 0)
    have hv_nn : (0 : ℝ) ≤ ((cfProd (0 :: (p ++ b :: u₂))) 1 1 : ℝ) := by
      exact_mod_cast cfProd_nonneg (0 :: (p ++ b :: u₂)) 1 1
    have hpos : 0 < (cylPair (p ++ b :: u₂)).2 - (cylPair (p ++ b :: u₂)).1 := by
      rw [hlen]; positivity
    linarith
  have hoo1 := StoppedTree.Ioo_subset_of_Icc_subset (le_of_lt htriv1) hsub1
  have hoo2 := StoppedTree.Ioo_subset_of_Icc_subset (le_of_lt htriv2) hsub2
  exact Disjoint.mono hoo1 hoo2 (cylPair_disj_sibling hp ha hb hab)

/-! ### Part 4: Paper 2 `thm:windows` stopped-cylinder tree `cfWindowsTree` -/

/-- Starting stage for the concrete CF stopped-cylinder tree (`j0 = 10^6`). -/
def j0CF : ℕ := 10 ^ 6

/-- Stage-`j` Paper 2 L2428–L2507 invariant for a stopped CF word `w`. -/
def StageInv (ε : ℕ → Bool) (j : ℕ) (w : List ℕ) : Prop :=
  PosDigits w ∧
  w ≠ [] ∧
  ((w.length - 1) % 2 == 1) = ε j ∧
  (4 / 3 : ℝ) * WindowPaperScale.Hpaper j ≤ ((cfProd (0 :: w)) 1 0 : ℝ) ∧
  ((cfProd (0 :: w)) 1 0 : ℝ) ≤ (5 / 2 : ℝ) * WindowPaperScale.Hpaper j ∧
  0 < (cfProd (0 :: w)) 1 1 ∧
  4 * (cfProd (0 :: w)) 1 1 < (cfProd (0 :: w)) 1 0

/-- Initial stage-`j0CF` word matching parity `ε j0CF` (Paper 2 L2435–L2442). -/
noncomputable def initWord (ε : ℕ → Bool) : List ℕ :=
  let d : ℕ := Nat.floor (WindowPaperScale.Hpaper j0CF / 2)
  if ε j0CF then [d, 4] else [d - 1, 1, 4]

theorem initWord_inv (ε : ℕ → Bool) : StageInv ε j0CF (initWord ε) := by
  have hH_big : (100 : ℝ) ≤ WindowPaperScale.Hpaper j0CF := by
    have h3 := WindowPaperScale.Hpaper_ge_three_pow (j := j0CF) (by norm_num [j0CF])
    have hpow : (3 : ℝ) ^ 5 ≤ (3 : ℝ) ^ (j0CF - 1) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num [j0CF])
    have h243 : (100 : ℝ) ≤ (3 : ℝ) ^ 5 := by norm_num
    linarith
  set H0 : ℝ := WindowPaperScale.Hpaper j0CF
  set d : ℕ := Nat.floor (H0 / 2)
  have hd_le : (d : ℝ) ≤ H0 / 2 := Nat.floor_le (by linarith)
  have hd_gt : H0 / 2 - 1 < (d : ℝ) := by
    have := Nat.lt_floor_add_one (H0 / 2); linarith
  have hd_ge : 49 ≤ d := by
    have : (49 : ℝ) ≤ (d : ℝ) := by linarith
    exact_mod_cast this
  have hdZ : (49 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd_ge
  unfold initWord
  change StageInv ε j0CF (if ε j0CF then [d, 4] else [d - 1, 1, 4])
  split_ifs with hε
  · -- [d, 4]
    have hM : cfProd (0 :: [d, 4]) = !![(4 : ℤ), 1; 4 * (d : ℤ) + 1, (d : ℤ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [cfProd, cfMat, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
    refine ⟨?_, by simp, by simp [hε], ?_, ?_, ?_, ?_⟩
    · simp only [PosDigits, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl) <;> omega
    · rw [hM]; simp; linarith
    · rw [hM]; simp; linarith
    · rw [hM]; simp; linarith
    · rw [hM]; simp
  · -- [d - 1, 1, 4]
    have hM : cfProd (0 :: [d - 1, 1, 4]) = !![(5 : ℤ), 1; 5 * (d : ℤ) - 1, (d : ℤ)] := by
      have hd1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [cfProd, cfMat, Matrix.mul_apply, Fin.sum_univ_two, hd1]; try ring)
    refine ⟨?_, by simp, by simp [hε], ?_, ?_, ?_, ?_⟩
    · simp only [PosDigits, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl) <;> omega
    · rw [hM]; simp; linarith
    · rw [hM]; simp; linarith
    · rw [hM]; simp; linarith
    · rw [hM]; simp; linarith

/-- Parent-dependent scale `R(j, w) = Hpaper (j + 1) / u` (Paper 2 L2446). -/
noncomputable def parentScale (j : ℕ) (w : List ℕ) : ℝ :=
  WindowPaperScale.Hpaper (j + 1) / ((cfProd (0 :: w)) 1 0 : ℝ)

/-- Target tail parity so `(w ++ tail ++ [4]).length - 1` has parity `ε (j + 1)`. -/
def targetTailParity (ε : ℕ → Bool) (j : ℕ) (w : List ℕ) : Bool :=
  xor (w.length % 2 == 1) (ε (j + 1))

/-- Child word produced from parent `w` and coprime pair `(m, n)`. -/
def makeChildWord (ε : ℕ → Bool) (j : ℕ) (w : List ℕ) (p : ℕ × ℕ) : List ℕ :=
  w ++ chooseParityCF p.1 p.2 (targetTailParity ε j w) ++ [4]

/-- Finite set of stopped child words of `w` at stage `j → j + 1`. -/
noncomputable def cfWordChild (ε : ℕ → Bool) (j : ℕ) (w : List ℕ) : Finset (List ℕ) :=
  let R := parentScale j w
  ((WindowMobiusCount.box R).filter (fun p => Nat.gcd p.1 p.2 = 1)).image
    (makeChildWord ε j w)

/-- Stage-`j` stopped words, recursively generated from `{initWord ε}` at `j0CF`. -/
noncomputable def cfWordAtomsAux (ε : ℕ → Bool) : ℕ → Finset (List ℕ)
  | 0 => {initWord ε}
  | d + 1 => (cfWordAtomsAux ε d).biUnion (cfWordChild ε (j0CF + d))

noncomputable def cfWordAtoms (ε : ℕ → Bool) (j : ℕ) : Finset (List ℕ) :=
  if j0CF ≤ j then cfWordAtomsAux ε (j - j0CF) else ∅

theorem parentScale_ge {ε : ℕ → Bool} {j : ℕ} {w : List ℕ} (hw : StageInv ε j w) :
    (2 / 5 : ℝ) * WindowPaperScale.Rpaper j ≤ parentScale j w := by
  have hHj := WindowPaperScale.Hpaper_pos j
  have hHj1 := WindowPaperScale.Hpaper_pos (j + 1)
  have hu_pos : (0 : ℝ) < ((cfProd (0 :: w)) 1 0 : ℝ) := by linarith [hw.2.2.2.1]
  have hu_hi := hw.2.2.2.2.1
  unfold parentScale WindowPaperScale.Rpaper
  have h1 := div_le_div_of_nonneg_left (le_of_lt hHj1) hu_pos hu_hi
  have heq : WindowPaperScale.Hpaper (j + 1) / (5 / 2 * WindowPaperScale.Hpaper j) =
      2 / 5 * (WindowPaperScale.Hpaper (j + 1) / WindowPaperScale.Hpaper j) := by
    field_simp
  linarith

/-- Core transition step (Paper 2 L2480–L2507): for any coprime `(m, n) ∈ box (parentScale j w)`,
    the intermediate denominator `t = m u + n v` stays strictly in `(H_{j+1} / 3, H_{j+1} / 2)`,
    and appending `[4]` yields a child word satisfying `StageInv ε (j + 1)`. -/
theorem childWord_transition {ε : ℕ → Bool} {j : ℕ} (hj : j0CF ≤ j) {w : List ℕ}
    (hw : StageInv ε j w) {p : ℕ × ℕ}
    (hp_box : p ∈ WindowMobiusCount.box (parentScale j w)) (hgcd : Nat.gcd p.1 p.2 = 1) :
    let tail := chooseParityCF p.1 p.2 (targetTailParity ε j w)
    ((cfProd (0 :: (w ++ tail))) 1 0 : ℝ) < (1 / 2 : ℝ) * WindowPaperScale.Hpaper (j + 1) ∧
    StageInv ε (j + 1) (makeChildWord ε j w p) := by
  set R : ℝ := parentScale j w
  set T : ℝ := WindowPaperScale.Hpaper (j + 1)
  have hTpos : 0 < T := WindowPaperScale.Hpaper_pos (j + 1)
  have hR_lo : (10 ^ 6 : ℝ) ≤ R := by
    have h1 := parentScale_ge hw
    have h2 := WindowPaperScale.Rpaper_ge_three_mul (by unfold j0CF at hj; omega : 1 ≤ j)
    have h3 : (10 ^ 6 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  obtain ⟨hm_mem, hn_mem⟩ := (WindowMobiusCount.box_mem_iff R p).mp hp_box
  simp only [Finset.mem_Icc] at hm_mem hn_mem
  have hm_gt : 0.34 * R < (p.1 : ℝ) := by
    have h1 : ((WindowMobiusCount.Mlo R : ℕ) : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hm_mem.1
    have h2 : 0.34 * R < ((Nat.floor (0.34 * R) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    simp only [WindowMobiusCount.Mlo, Nat.cast_add, Nat.cast_one] at h1
    linarith
  have hm_le : (p.1 : ℝ) ≤ 0.36 * R := by
    have h1 : (p.1 : ℝ) ≤ ((WindowMobiusCount.Mhi R : ℕ) : ℝ) := by exact_mod_cast hm_mem.2
    have h2 : ((Nat.floor (0.36 * R) : ℕ) : ℝ) ≤ 0.36 * R := Nat.floor_le (by linarith)
    simp only [WindowMobiusCount.Mhi] at h1
    linarith
  have hn_gt : 0.20 * R < (p.2 : ℝ) := by
    have h1 : ((WindowMobiusCount.Nlo R : ℕ) : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hn_mem.1
    have h2 : 0.20 * R < ((Nat.floor (0.20 * R) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    simp only [WindowMobiusCount.Nlo, Nat.cast_add, Nat.cast_one] at h1
    linarith
  have hn_le : (p.2 : ℝ) ≤ 0.22 * R := by
    have h1 : (p.2 : ℝ) ≤ ((WindowMobiusCount.Nhi R : ℕ) : ℝ) := by exact_mod_cast hn_mem.2
    have h2 : ((Nat.floor (0.22 * R) : ℕ) : ℝ) ≤ 0.22 * R := Nat.floor_le (by linarith)
    simp only [WindowMobiusCount.Nhi] at h1
    linarith
  have hn1 : 1 ≤ p.2 := (WindowMobiusCount.box_mem_pos R p hp_box).2
  have hnm : p.2 < p.1 := by
    have : (p.2 : ℝ) < (p.1 : ℝ) := by linarith
    exact_mod_cast this
  set tail := chooseParityCF p.1 p.2 (targetTailParity ε j w)
  obtain ⟨htail_pos, htail_ne, hcol0, hcol1, htail_par⟩ :=
    chooseParityCF_props hn1 hnm hgcd (targetTailParity ε j w)
  set u : ℤ := (cfProd (0 :: w)) 1 0
  set v : ℤ := (cfProd (0 :: w)) 1 1
  have hu_posR : (0 : ℝ) < (u : ℝ) := by
    have := WindowPaperScale.Hpaper_pos j
    linarith [hw.2.2.2.1]
  have hu_posZ : 0 < u := by exact_mod_cast hu_posR
  have hv_posZ : 0 < v := hw.2.2.2.2.2.1
  have hv_posR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv_posZ
  have hv_lt : (4 : ℝ) * (v : ℝ) < (u : ℝ) := by exact_mod_cast hw.2.2.2.2.2.2
  have hRu : R * (u : ℝ) = T := div_mul_cancel₀ T (ne_of_gt hu_posR)
  set t : ℤ := (cfProd (0 :: (w ++ tail))) 1 0
  set t' : ℤ := (cfProd (0 :: (w ++ tail))) 1 1
  have ht_eq : (t : ℝ) = (p.1 : ℝ) * (u : ℝ) + (p.2 : ℝ) * (v : ℝ) := by
    have hcons : (0 :: (w ++ tail)) = (0 :: w) ++ tail := rfl
    have hZ : t = u * (cfProd tail) 0 0 + v * (cfProd tail) 1 0 := by
      dsimp only [t, u, v]
      rw [hcons, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hZ, hcol0, hcol1]
    push_cast; ring
  have ht_lo : (1 / 3 : ℝ) * T < (t : ℝ) := by nlinarith
  have ht_hi : (t : ℝ) < (1 / 2 : ℝ) * T := by nlinarith
  obtain ⟨ht'_pos, ht'_lt⟩ := append_penult_bounds hu_posZ hv_posZ htail_pos htail_ne
  have ht'_posR : (0 : ℝ) < (t' : ℝ) := by exact_mod_cast ht'_pos
  have ht'_ltR : (t' : ℝ) < (t : ℝ) := by exact_mod_cast ht'_lt
  -- Appending `[4]` gives `u_new = 4 t + t'`, `v_new = t`.
  have hcons4 : (0 :: makeChildWord ε j w p) = (0 :: (w ++ tail)) ++ [4] := by
    simp [makeChildWord, tail]
  have hu_new : (cfProd (0 :: makeChildWord ε j w p)) 1 0 = 4 * t + t' := by
    rw [hcons4, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfProd, cfMat, t, t']; ring
  have hv_new : (cfProd (0 :: makeChildWord ε j w p)) 1 1 = t := by
    rw [hcons4, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfProd, cfMat, t]
  refine ⟨ht_hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold makeChildWord
    exact posDigits_append.mpr ⟨posDigits_append.mpr ⟨hw.1, htail_pos⟩,
      posDigits_cons.mpr ⟨by omega, posDigits_nil⟩⟩
  · unfold makeChildWord
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil 4 [])
  · unfold makeChildWord
    have hlen : (w ++ tail ++ [4]).length - 1 = w.length + tail.length := by simp
    rw [hlen]
    have hpar_eq : ((w.length + tail.length) % 2 == 1) =
        xor (w.length % 2 == 1) (tail.length % 2 == 1) := by
      have : (w.length + tail.length) % 2 = (w.length % 2 + tail.length % 2) % 2 :=
        Nat.add_mod _ _ _
      rw [this]
      rcases Nat.mod_two_eq_zero_or_one w.length with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one tail.length with h2 | h2 <;>
        simp [h1, h2]
    rw [hpar_eq, htail_par, targetTailParity]
    cases (w.length % 2 == 1) <;> cases (ε (j + 1)) <;> rfl
  · rw [hu_new]; push_cast; linarith
  · rw [hu_new]; push_cast; linarith
  · rw [hv_new]; exact lt_trans ht'_pos ht'_lt
  · rw [hu_new, hv_new]; linarith [ht'_pos]

/-- Distinct coprime pairs in `box (parentScale j w)` produce prefix-incomparable child words. -/
theorem childWord_incomparable {ε : ℕ → Bool} {j : ℕ} (hj : j0CF ≤ j) {w : List ℕ}
    (hw : StageInv ε j w) {p₁ p₂ : ℕ × ℕ}
    (hp₁ : p₁ ∈ WindowMobiusCount.box (parentScale j w)) (hg₁ : Nat.gcd p₁.1 p₁.2 = 1)
    (hp₂ : p₂ ∈ WindowMobiusCount.box (parentScale j w)) (hg₂ : Nat.gcd p₂.1 p₂.2 = 1)
    (hne : p₁ ≠ p₂) :
    ¬ (makeChildWord ε j w p₁ <+: makeChildWord ε j w p₂) := by
  intro hpref
  obtain ⟨ht₁_hi, hinv₁⟩ := childWord_transition hj hw hp₁ hg₁
  obtain ⟨ht₂_hi, _⟩ := childWord_transition hj hw hp₂ hg₂
  set t₁ := chooseParityCF p₁.1 p₁.2 (targetTailParity ε j w)
  set t₂ := chooseParityCF p₂.1 p₂.2 (targetTailParity ε j w)
  have hTpos := WindowPaperScale.Hpaper_pos (j + 1)
  have h1_ge : (4 / 3 : ℝ) * WindowPaperScale.Hpaper (j + 1) ≤
      ((cfProd (0 :: makeChildWord ε j w p₁)) 1 0 : ℝ) := hinv₁.2.2.2.1
  by_cases heq : makeChildWord ε j w p₁ = makeChildWord ε j w p₂
  · unfold makeChildWord at heq
    have h1 := List.append_inj_left' heq rfl
    have ht_eq : t₁ = t₂ := List.append_cancel_left h1
    have hn1 := (WindowMobiusCount.box_mem_pos _ p₁ hp₁).2
    have hn2 := (WindowMobiusCount.box_mem_pos _ p₂ hp₂).2
    have hR_lo : (10 ^ 6 : ℝ) ≤ parentScale j w := by
      have ha := parentScale_ge hw
      have hb := WindowPaperScale.Rpaper_ge_three_mul (by unfold j0CF at hj; omega : 1 ≤ j)
      have hc : (10 ^ 6 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      linarith
    have hlt_of_box : ∀ p ∈ WindowMobiusCount.box (parentScale j w), p.2 < p.1 := by
      intro p hp
      obtain ⟨hm, hn⟩ := (WindowMobiusCount.box_mem_iff _ p).mp hp
      simp only [Finset.mem_Icc] at hm hn
      have h1' : ((WindowMobiusCount.Mlo (parentScale j w) : ℕ) : ℝ) ≤ (p.1 : ℝ) := by
        exact_mod_cast hm.1
      have h2' : 0.34 * parentScale j w < ((Nat.floor (0.34 * parentScale j w) : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h3' : (p.2 : ℝ) ≤ ((WindowMobiusCount.Nhi (parentScale j w) : ℕ) : ℝ) := by
        exact_mod_cast hn.2
      have h4' : ((Nat.floor (0.22 * parentScale j w) : ℕ) : ℝ) ≤ 0.22 * parentScale j w :=
        Nat.floor_le (by linarith)
      simp only [WindowMobiusCount.Mlo, WindowMobiusCount.Nhi, Nat.cast_add, Nat.cast_one]
        at h1' h3'
      exact_mod_cast (by linarith : (p.2 : ℝ) < (p.1 : ℝ))
    have hc1 := chooseParityCF_props hn1 (hlt_of_box p₁ hp₁) hg₁ (targetTailParity ε j w)
    have hc2 := chooseParityCF_props hn2 (hlt_of_box p₂ hp₂) hg₂ (targetTailParity ε j w)
    dsimp only [t₁, t₂] at ht_eq
    have hm_eq : (p₁.1 : ℤ) = (p₂.1 : ℤ) := by rw [← hc1.2.2.1, ← hc2.2.2.1, ht_eq]
    have hn_eq : (p₁.2 : ℤ) = (p₂.2 : ℤ) := by rw [← hc1.2.2.2.1, ← hc2.2.2.2.1, ht_eq]
    exact hne (Prod.ext (by exact_mod_cast hm_eq) (by exact_mod_cast hn_eq))
  · -- Proper prefix of `w ++ t₂ ++ [4]` is a prefix of `w ++ t₂`.
    obtain ⟨suf, hsuf⟩ := hpref
    have hsuf_ne : suf ≠ [] := by
      intro h; apply heq; simpa [h] using hsuf
    have hpre_t2 : makeChildWord ε j w p₁ <+: w ++ t₂ := by
      rcases List.eq_nil_or_concat suf with rfl | ⟨init, last, hlast⟩
      · exact absurd rfl hsuf_ne
      · rw [hlast, List.concat_eq_append, ← List.append_assoc] at hsuf
        have hsuf' : (makeChildWord ε j w p₁ ++ init) ++ [last] = (w ++ t₂) ++ [4] := hsuf
        exact ⟨init, List.append_inj_left' hsuf' rfl⟩
    obtain ⟨suf', hsuf'⟩ := hpre_t2
    have hsuf'_pos : PosDigits suf' := by
      have hpos_wt2 : PosDigits (w ++ t₂) := by
        have hn2 := (WindowMobiusCount.box_mem_pos _ p₂ hp₂).2
        have hR_lo : (10 ^ 6 : ℝ) ≤ parentScale j w := by
          have ha := parentScale_ge hw
          have hb := WindowPaperScale.Rpaper_ge_three_mul (by unfold j0CF at hj; omega : 1 ≤ j)
          have hc : (10 ^ 6 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
          linarith
        have hlt2 : p₂.2 < p₂.1 := by
          obtain ⟨hm, hn⟩ := (WindowMobiusCount.box_mem_iff _ p₂).mp hp₂
          simp only [Finset.mem_Icc] at hm hn
          have h1' : ((WindowMobiusCount.Mlo (parentScale j w) : ℕ) : ℝ) ≤ (p₂.1 : ℝ) := by
            exact_mod_cast hm.1
          have h2' : 0.34 * parentScale j w <
              ((Nat.floor (0.34 * parentScale j w) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
          have h3' : (p₂.2 : ℝ) ≤ ((WindowMobiusCount.Nhi (parentScale j w) : ℕ) : ℝ) := by
            exact_mod_cast hn.2
          have h4' : ((Nat.floor (0.22 * parentScale j w) : ℕ) : ℝ) ≤ 0.22 * parentScale j w :=
            Nat.floor_le (by linarith)
          simp only [WindowMobiusCount.Mlo, WindowMobiusCount.Nhi, Nat.cast_add, Nat.cast_one]
            at h1' h3'
          exact_mod_cast (by linarith : (p₂.2 : ℝ) < (p₂.1 : ℝ))
        exact posDigits_append.mpr
          ⟨hw.1, (chooseParityCF_props hn2 hlt2 hg₂ (targetTailParity ε j w)).1⟩
      rw [← hsuf'] at hpos_wt2
      exact (posDigits_append.mp hpos_wt2).2
    have hmono : (cfProd (0 :: makeChildWord ε j w p₁)) 1 0 ≤ (cfProd (0 :: (w ++ t₂))) 1 0 := by
      rw [← hsuf']
      exact den_mono_prefix hsuf'_pos
    have hmonoR : ((cfProd (0 :: makeChildWord ε j w p₁)) 1 0 : ℝ) ≤
        ((cfProd (0 :: (w ++ t₂))) 1 0 : ℝ) := by exact_mod_cast hmono
    linarith

theorem cfWordAtoms_base (ε : ℕ → Bool) : cfWordAtoms ε j0CF = {initWord ε} := by
  simp [cfWordAtoms, cfWordAtomsAux]

theorem cfWordAtoms_succ (ε : ℕ → Bool) {j : ℕ} (hj : j0CF ≤ j) :
    cfWordAtoms ε (j + 1) = (cfWordAtoms ε j).biUnion (cfWordChild ε j) := by
  have hj1 : j0CF ≤ j + 1 := by omega
  have hsub : j + 1 - j0CF = (j - j0CF) + 1 := by omega
  have hadd : j0CF + (j - j0CF) = j := by omega
  simp only [cfWordAtoms, hj, hj1, ↓reduceIte, hsub, cfWordAtomsAux, hadd]

/-- Every word in `cfWordAtoms ε j` satisfies `StageInv ε j` and any two distinct words
    at level `j` are prefix-incomparable. -/
theorem cfWordAtoms_inv_and_incomp (ε : ℕ → Bool) :
    ∀ j ≥ j0CF,
      (∀ w ∈ cfWordAtoms ε j, StageInv ε j w) ∧
      (∀ w₁ ∈ cfWordAtoms ε j, ∀ w₂ ∈ cfWordAtoms ε j, w₁ ≠ w₂ → ¬ (w₁ <+: w₂)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    rw [cfWordAtoms_base]
    refine ⟨fun w hw => ?_, fun w₁ h1 w₂ h2 hne => ?_⟩
    · rw [Finset.mem_singleton.mp hw]; exact initWord_inv ε
    · rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2] at hne
      exact absurd rfl hne
  | succ j hj ih =>
    obtain ⟨ih_inv, ih_inc⟩ := ih
    rw [cfWordAtoms_succ ε hj]
    constructor
    · intro c hc
      obtain ⟨w, hw, hcw⟩ := Finset.mem_biUnion.mp hc
      simp only [cfWordChild, Finset.mem_image, Finset.mem_filter] at hcw
      obtain ⟨p, ⟨hp_box, hgcd⟩, rfl⟩ := hcw
      exact (childWord_transition hj (ih_inv w hw) hp_box hgcd).2
    · intro c₁ hc₁ c₂ hc₂ hne hpref
      obtain ⟨w₁, hw₁, hcw₁⟩ := Finset.mem_biUnion.mp hc₁
      obtain ⟨w₂, hw₂, hcw₂⟩ := Finset.mem_biUnion.mp hc₂
      simp only [cfWordChild, Finset.mem_image, Finset.mem_filter] at hcw₁ hcw₂
      obtain ⟨p₁, ⟨hp₁, hg₁⟩, rfl⟩ := hcw₁
      obtain ⟨p₂, ⟨hp₂, hg₂⟩, rfl⟩ := hcw₂
      by_cases hw_eq : w₁ = w₂
      · subst hw_eq
        have hp_ne : p₁ ≠ p₂ := fun h => hne (by subst h; rfl)
        exact childWord_incomparable hj (ih_inv w₁ hw₁) hp₁ hg₁ hp₂ hg₂ hp_ne hpref
      · -- Distinct parents `w₁ ≠ w₂` are prefix-incomparable; their extensions cannot compare.
        have hw1_pre : w₁ <+: makeChildWord ε j w₁ p₁ := by
          unfold makeChildWord
          rw [List.append_assoc]
          exact List.prefix_append w₁ _
        have hw2_pre : w₂ <+: makeChildWord ε j w₂ p₂ := by
          unfold makeChildWord
          rw [List.append_assoc]
          exact List.prefix_append w₂ _
        have hw1_in_c2 : w₁ <+: makeChildWord ε j w₂ p₂ := List.IsPrefix.trans hw1_pre hpref
        rcases List.prefix_or_prefix_of_prefix hw1_in_c2 hw2_pre with h12 | h21
        · exact ih_inc w₁ hw₁ w₂ hw₂ hw_eq h12
        · exact ih_inc w₂ hw₂ w₁ hw₁ (Ne.symm hw_eq) h21

/-- `cylPair` is injective on `cfWordAtoms ε j`
    (incomparable words have disjoint nonempty `Ioo`). -/
theorem cylPair_injOn_atoms (ε : ℕ → Bool) {j : ℕ} (hj : j0CF ≤ j) :
    Set.InjOn cylPair ↑(cfWordAtoms ε j) := by
  obtain ⟨hinv, hinc⟩ := cfWordAtoms_inv_and_incomp ε j hj
  intro w₁ hw₁ w₂ hw₂ heq
  by_contra hne
  have h1 := Finset.mem_coe.mp hw₁
  have h2 := Finset.mem_coe.mp hw₂
  have hdisj := cylPair_disj_of_incomparable (hinv w₁ h1).1 (hinv w₂ h2).1
    (hinc w₁ h1 w₂ h2 hne) (hinc w₂ h2 w₁ h1 (Ne.symm hne))
  rw [heq] at hdisj
  have hlen := cylPair_len_bounds (WindowPaperScale.Hpaper_pos j) (hinv w₂ h2).1 (hinv w₂ h2).2.1
    (hinv w₂ h2).2.2.2.1 (hinv w₂ h2).2.2.2.2.1
    (by exact_mod_cast le_of_lt (hinv w₂ h2).2.2.2.2.2.1)
    (by exact_mod_cast (by linarith [(hinv w₂ h2).2.2.2.2.2.1, (hinv w₂ h2).2.2.2.2.2.2] :
      (cfProd (0 :: w₂)) 1 1 ≤ (cfProd (0 :: w₂)) 1 0))
  have hlt : (cylPair w₂).1 < (cylPair w₂).2 := by
    have : (0 : ℝ) < (2 / 25 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 := by
      have := WindowPaperScale.Hpaper_pos j; positivity
    linarith [hlen.1]
  have hmid : ((cylPair w₂).1 + (cylPair w₂).2) / 2 ∈
      Set.Ioo (cylPair w₂).1 (cylPair w₂).2 := ⟨by linarith, by linarith⟩
  exact Set.disjoint_left.mp hdisj hmid hmid

open Classical in
/-- Concrete `StoppedTree.TreeData` realizing Paper 2's `thm:windows` CF stopping rule. -/
noncomputable def cfWindowsTree (ε : ℕ → Bool) : StoppedTree.TreeData where
  atoms := fun j => (cfWordAtoms ε j).image cylPair
  child := fun j I =>
    if h : ∃ w ∈ cfWordAtoms ε j, cylPair w = I then
      (cfWordChild ε j (Classical.choose h)).image cylPair
    else ∅

/-- Unconditional Lean 4 Hausdorff dimension lower bound for Paper 2's concrete
    continued-fraction stopped-cylinder tree `cfWindowsTree ε` (`j0 = 10^6`):
    discharges ALL tree-interface hypotheses of `WindowPaperScale.dimH_ge_one_windows_paper_scale`
    with ZERO unproved hypotheses beyond Lean core axioms. -/
theorem dimH_ge_one_cfWindowsTree (ε : ℕ → Bool) :
    (1 : ℝ≥0∞) ≤ dimH (WindowTreePrune.cantorSet (cfWindowsTree ε) j0CF) := by
  classical
  -- Parent-dependent scale `R j I` matching Paper 2 L2446 `H_{j+1} / u`.
  let R : ℕ → (ℝ × ℝ) → ℝ := fun j I =>
    if h : ∃ w ∈ cfWordAtoms ε j, cylPair w = I then
      parentScale j (Classical.choose h)
    else (2 / 5 : ℝ) * WindowPaperScale.Rpaper j
  have hchoose_eq : ∀ j ≥ j0CF, ∀ w ∈ cfWordAtoms ε j,
      ∀ h : ∃ w' ∈ cfWordAtoms ε j, cylPair w' = cylPair w,
        Classical.choose h = w := by
    intro j hj w hw h
    obtain ⟨hw', heq⟩ := Classical.choose_spec h
    exact cylPair_injOn_atoms ε hj (Finset.mem_coe.mpr hw') (Finset.mem_coe.mpr hw) heq
  have hR_lo : ∀ j ≥ j0CF, ∀ I ∈ (cfWindowsTree ε).atoms j,
      (2 / 5 : ℝ) * WindowPaperScale.Rpaper j ≤ R j I := by
    intro j hj I hI
    simp only [cfWindowsTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hex : ∃ w' ∈ cfWordAtoms ε j, cylPair w' = cylPair w := ⟨w, hw, rfl⟩
    simp only [R, hex, ↓reduceDIte, hchoose_eq j hj w hw hex]
    exact parentScale_ge ((cfWordAtoms_inv_and_incomp ε j hj).1 w hw)
  have hne0 : ((cfWindowsTree ε).atoms j0CF).Nonempty := by
    refine ⟨cylPair (initWord ε), ?_⟩
    simp [cfWindowsTree, cfWordAtoms_base]
  have hlen : ∀ j ≥ j0CF, ∀ I ∈ (cfWindowsTree ε).atoms j,
      (2 / 25 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 ≤ I.2 - I.1 ∧
      I.2 - I.1 ≤ (9 / 16 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 := by
    intro j hj I hI
    simp only [cfWindowsTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hinv := (cfWordAtoms_inv_and_incomp ε j hj).1 w hw
    exact cylPair_len_bounds (WindowPaperScale.Hpaper_pos j) hinv.1 hinv.2.1
      hinv.2.2.2.1 hinv.2.2.2.2.1
      (by exact_mod_cast le_of_lt hinv.2.2.2.2.2.1)
      (by exact_mod_cast (by linarith [hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2] :
        (cfProd (0 :: w)) 1 1 ≤ (cfProd (0 :: w)) 1 0))
  have htriv : ∀ j ≥ j0CF, ∀ I ∈ (cfWindowsTree ε).atoms j, I.1 < I.2 := by
    intro j hj I hI
    have h1 := (hlen j hj I hI).1
    have hpos : (0 : ℝ) < (2 / 25 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 := by
      have := WindowPaperScale.Hpaper_pos j; positivity
    linarith
  have hdisj : ∀ j ≥ j0CF, ∀ I ∈ (cfWindowsTree ε).atoms j, ∀ J ∈ (cfWindowsTree ε).atoms j,
      I ≠ J → Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2) := by
    intro j hj I hI J hJ hne
    simp only [cfWindowsTree, Finset.mem_image] at hI hJ
    obtain ⟨w₁, hw₁, rfl⟩ := hI
    obtain ⟨w₂, hw₂, rfl⟩ := hJ
    have hw_ne : w₁ ≠ w₂ := fun h => hne (by subst h; rfl)
    obtain ⟨hinv, hinc⟩ := cfWordAtoms_inv_and_incomp ε j hj
    exact cylPair_disj_of_incomparable (hinv w₁ hw₁).1 (hinv w₂ hw₂).1
      (hinc w₁ hw₁ w₂ hw₂ hw_ne) (hinc w₂ hw₂ w₁ hw₁ (Ne.symm hw_ne))
  have hchild_mem : ∀ j ≥ j0CF, ∀ I ∈ (cfWindowsTree ε).atoms j,
      (cfWindowsTree ε).child j I ⊆ (cfWindowsTree ε).atoms (j + 1) := by
    intro j hj I hI c hc
    simp only [cfWindowsTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hex : ∃ w' ∈ cfWordAtoms ε j, cylPair w' = cylPair w := ⟨w, hw, rfl⟩
    simp only [cfWindowsTree, hex, ↓reduceDIte, hchoose_eq j hj w hw hex, Finset.mem_image] at hc ⊢
    obtain ⟨cw, hcw, rfl⟩ := hc
    refine ⟨cw, ?_, rfl⟩
    rw [cfWordAtoms_succ ε hj]
    exact Finset.mem_biUnion.mpr ⟨w, hw, hcw⟩
  have hchild_cop : ∀ j ≥ j0CF, ∀ I ∈ (cfWindowsTree ε).atoms j,
      WindowMobiusCount.copCount (R j I) ≤ ((cfWindowsTree ε).child j I).card := by
    intro j hj I hI
    simp only [cfWindowsTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hex : ∃ w' ∈ cfWordAtoms ε j, cylPair w' = cylPair w := ⟨w, hw, rfl⟩
    have hinv := (cfWordAtoms_inv_and_incomp ε j hj).1 w hw
    simp only [R, cfWindowsTree, hex, ↓reduceDIte, hchoose_eq j hj w hw hex]
    have hsub_atoms : cfWordChild ε j w ⊆ cfWordAtoms ε (j + 1) := by
      intro c hc
      rw [cfWordAtoms_succ ε hj]
      exact Finset.mem_biUnion.mpr ⟨w, hw, hc⟩
    have hinj_cyl : Set.InjOn cylPair ↑(cfWordChild ε j w) :=
      (cylPair_injOn_atoms ε (by omega : j0CF ≤ j + 1)).mono
        (Finset.coe_subset.mpr hsub_atoms)
    rw [Finset.card_image_of_injOn hinj_cyl]
    unfold cfWordChild WindowMobiusCount.copCount
    have hinj_word : Set.InjOn (makeChildWord ε j w)
        ↑((WindowMobiusCount.box (parentScale j w)).filter (fun p => Nat.gcd p.1 p.2 = 1)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      by_contra hne
      simp only [Finset.mem_coe, Finset.mem_filter] at hp₁ hp₂
      exact childWord_incomparable hj hinv hp₁.1 hp₁.2 hp₂.1 hp₂.2 hne (by rw [heq])
    rw [Finset.card_image_of_injOn hinj_word]
  have hdisj_child : ∀ j ≥ j0CF, ∀ I₁ ∈ (cfWindowsTree ε).atoms j,
      ∀ I₂ ∈ (cfWindowsTree ε).atoms j, I₁ ≠ I₂ →
      Disjoint ((cfWindowsTree ε).child j I₁) ((cfWindowsTree ε).child j I₂) := by
    intro j hj I₁ hI₁ I₂ hI₂ hne
    simp only [cfWindowsTree, Finset.mem_image] at hI₁ hI₂
    obtain ⟨w₁, hw₁, rfl⟩ := hI₁
    obtain ⟨w₂, hw₂, rfl⟩ := hI₂
    have hw_ne : w₁ ≠ w₂ := fun h => hne (by subst h; rfl)
    have hex₁ : ∃ w' ∈ cfWordAtoms ε j, cylPair w' = cylPair w₁ := ⟨w₁, hw₁, rfl⟩
    have hex₂ : ∃ w' ∈ cfWordAtoms ε j, cylPair w' = cylPair w₂ := ⟨w₂, hw₂, rfl⟩
    simp only [cfWindowsTree, hex₁, hex₂, ↓reduceDIte,
      hchoose_eq j hj w₁ hw₁ hex₁, hchoose_eq j hj w₂ hw₂ hex₂]
    rw [Finset.disjoint_left]
    intro c hc₁ hc₂
    simp only [Finset.mem_image] at hc₁ hc₂
    obtain ⟨c₁, hc₁', rfl⟩ := hc₁
    obtain ⟨c₂, hc₂', heq⟩ := hc₂
    have hc₁_atoms : c₁ ∈ cfWordAtoms ε (j + 1) := by
      rw [cfWordAtoms_succ ε hj]; exact Finset.mem_biUnion.mpr ⟨w₁, hw₁, hc₁'⟩
    have hc₂_atoms : c₂ ∈ cfWordAtoms ε (j + 1) := by
      rw [cfWordAtoms_succ ε hj]; exact Finset.mem_biUnion.mpr ⟨w₂, hw₂, hc₂'⟩
    have hc_eq : c₁ = c₂ :=
      cylPair_injOn_atoms ε (by omega : j0CF ≤ j + 1)
        (Finset.mem_coe.mpr hc₁_atoms) (Finset.mem_coe.mpr hc₂_atoms) heq.symm
    subst hc_eq
    simp only [cfWordChild, Finset.mem_image, Finset.mem_filter] at hc₁' hc₂'
    obtain ⟨p₁, _, hp₁_eq⟩ := hc₁'
    obtain ⟨p₂, _, hp₂_eq⟩ := hc₂'
    have hpre₁ : w₁ <+: c₁ := by
      rw [← hp₁_eq]; unfold makeChildWord; rw [List.append_assoc]; exact List.prefix_append w₁ _
    have hpre₂ : w₂ <+: c₁ := by
      rw [← hp₂_eq]; unfold makeChildWord; rw [List.append_assoc]; exact List.prefix_append w₂ _
    have hinc := (cfWordAtoms_inv_and_incomp ε j hj).2
    rcases List.prefix_or_prefix_of_prefix hpre₁ hpre₂ with h12 | h21
    · exact hinc w₁ hw₁ w₂ hw₂ hw_ne h12
    · exact hinc w₂ hw₂ w₁ hw₁ (Ne.symm hw_ne) h21
  have hnest : ∀ j ≥ j0CF, ∀ I ∈ (cfWindowsTree ε).atoms j,
      ∀ C ∈ (cfWindowsTree ε).child j I, Set.Icc C.1 C.2 ⊆ Set.Icc I.1 I.2 := by
    intro j hj I hI C hC
    simp only [cfWindowsTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hex : ∃ w' ∈ cfWordAtoms ε j, cylPair w' = cylPair w := ⟨w, hw, rfl⟩
    simp only [cfWindowsTree, hex, ↓reduceDIte, hchoose_eq j hj w hw hex, Finset.mem_image] at hC
    obtain ⟨cw, hcw, rfl⟩ := hC
    have hinv_w := (cfWordAtoms_inv_and_incomp ε j hj).1 w hw
    have hinv_cw := (cfWordAtoms_inv_and_incomp ε (j + 1) (by omega)).1 cw
      (by rw [cfWordAtoms_succ ε hj]; exact Finset.mem_biUnion.mpr ⟨w, hw, hcw⟩)
    simp only [cfWordChild, Finset.mem_image, Finset.mem_filter] at hcw
    obtain ⟨p, _, rfl⟩ := hcw
    unfold makeChildWord at hinv_cw ⊢
    rw [List.append_assoc] at hinv_cw ⊢
    exact cylPair_nest hinv_w.1 hinv_w.2.1 (posDigits_append.mp hinv_cw.1).2
  exact WindowPaperScale.dimH_ge_one_windows_paper_scale (T := cfWindowsTree ε) (j0 := j0CF)
    le_rfl hR_lo hne0 htriv hlen hdisj hchild_mem hchild_cop hdisj_child hnest

#print axioms WindowCFRealize.cfProd_append
#print axioms WindowCFRealize.cfProd_col0_pos
#print axioms WindowCFRealize.cfProd_row1_le_row0
#print axioms WindowCFRealize.cfProd_col1_le_col0
#print axioms WindowCFRealize.den_mono_prefix
#print axioms WindowCFRealize.append_penult_bounds
#print axioms WindowCFRealize.euclidCF_pos_digits
#print axioms WindowCFRealize.euclidCF_col0
#print axioms WindowCFRealize.euclidCF_last_ge_two
#print axioms WindowCFRealize.flipLast_col0
#print axioms WindowCFRealize.chooseParityCF_props
#print axioms WindowCFRealize.mobius_sub
#print axioms WindowCFRealize.mobius_mul
#print axioms WindowCFRealize.cylPair_len
#print axioms WindowCFRealize.cylPair_len_bounds
#print axioms WindowCFRealize.mobius_mem_cylPair
#print axioms WindowCFRealize.cylPair_nest
#print axioms WindowCFRealize.cylPair_disj_sibling
#print axioms WindowCFRealize.cylPair_disj_of_incomparable
#print axioms WindowCFRealize.initWord_inv
#print axioms WindowCFRealize.parentScale_ge
#print axioms WindowCFRealize.childWord_transition
#print axioms WindowCFRealize.childWord_incomparable
#print axioms WindowCFRealize.cfWordAtoms_inv_and_incomp
#print axioms WindowCFRealize.cylPair_injOn_atoms
#print axioms WindowCFRealize.dimH_ge_one_cfWindowsTree

end WindowCFRealize
