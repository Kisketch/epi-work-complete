import Mathlib
import EpiFormal.EulerConvergents
import EpiFormal.FullSpectrumDiscrete
import EpiFormal.GaugeLiminfComplete
import EpiFormal.TrichotomyAndPolyExtension
import EpiFormal.FiniteStateTail
import EpiFormal.DimHFinite

/-!
# Full-Convergent Spectrum and Kraaikamp–Liardet Theory for `e` (`FullConvergentSpectrum`)

Formalizes the complete theory of the **full** simple continued fraction convergents
`pFull n / qFull n` of `e = [2; 1, 2, 1, 1, 4, 1, 1, 6, ...]` unconditionally on Lean's core
axioms `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero custom axioms):

1. **Exact Full-Convergent & Error Formulas (`pFull`, `qFull`, `fullDelta`)**:
   Using `0`-based indexing for `e = [2; 1, 2, 1, 1, 4, ...]` (`pFull 0 / qFull 0 = 2/1`,
   `pFull 1 / qFull 1 = 3/1 = Psel 1 / Qsel 1`, `pFull 2 / qFull 2 = 8/3`,
   `pFull 3 / qFull 3 = 11/4`, `pFull 4 / qFull 4 = 19/7 = Psel 2 / Qsel 2`, ...):
   - For all `j : ℕ`:
     `2 * qFull (3 * j) = Qsel (j + 1) + Qsel j`,
     `qFull (3 * j + 1) = Qsel (j + 1)`,
     `2 * qFull (3 * j + 2) = Qsel (j + 2) - Qsel (j + 1)`,
     and for `1 ≤ j`:
     `qFull (3 * j - 2) = Qsel j`,
     `qFull (3 * j - 1) = (Qsel (j + 1) - Qsel j) / 2`,
     `qFull (3 * j) = (Qsel (j + 1) + Qsel j) / 2`,
     with identical formulas for `pFull` and `Psel`.
   - Unimodular determinant `pFull n * qFull (n + 1) - pFull (n + 1) * qFull n = (-1) ^ (n + 1)`,
     coprimality `Int.gcd (pFull n) (qFull n) = 1`, and `pFull n / qFull n → exp 1`.
   - Exact error formulas `fullDelta n := qFull n * exp 1 - pFull n` in terms of `deltaSel`
     and exact Kraaikamp–Liardet weight asymptotics:
     `fullKLWeight (3 * j + 1) / (j + 1) → 2` (with `2 * j + 1 < fullKLWeight (3 * j - 2)`),
     `fullKLWeight (3 * j + 2) → 2`, and `fullKLWeight (3 * j + 3) → 2`.

2. **Full-Convergent Kraaikamp–Liardet and Raw Partial-Quotient Spectra**:
   - `fullKLSpectrum x := limsup_n (‖qFull n * x‖ / (qFull n * |qFull n * e - pFull n|))`:
     equals `⊤` when `apprExponent x = ⊤`, and
     `max (2 * apprExponent x) (if parityFlip x then 1 else 0)` when `apprExponent x ≠ ⊤`.
     Its exact spectrum is `{0} ∪ {k / 2 : k ≥ 2} ∪ {∞}`, with giant initial gap `(0, 1)`
     (created because `k = 1` forces `parityFlip x`), zero-level collapse to `ℤ + ℤ e`,
     level-`1` absorption `(ℤ + ℤ e + (e + 1) / 2) ∪ {Λ = 1/4} ∪ {Λ = 1/2}` (gauge base `5`),
     exact level coincidence `{fullKLSpectrum = k / 2} = {Λ = k / 4}` for all `k ≥ 3`
     (gauge base `2 * k + 1`), and coarse collapse (`dimH {< ⊤} = 0`, `ae (= ⊤)`).
   - `fullRawSpectrum x := limsup_n (a_{n+1} * ‖qFull n * x‖)`:
     equals `max (2 * apprExponent x) (if parityFlip x then 1 / 2 else 0)`
     when `apprExponent x ≠ ⊤`, with full spectrum `(1 / 2) ℤ_{≥ 0} ∪ {∞}`,
     zero level `ℤ + ℤ e`, level `1 / 2` of gauge base `3`,
     and exact coincidence `{fullRawSpectrum = k / 2} = {Λ = k / 4}` for all `k ≥ 2`.
-/

open Filter Topology Set MeasureTheory Classification SpectralGap FullSpectrumDiscrete
open GaugeExact GaugeCircle GaugeLiminf TrichotomyAndPolyExtension
open scoped ENNReal NNReal

namespace FullConvergentSpectrum

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Part 1: Full Regular Continued Fraction Digits and Convergents of `e` -/

/-- The `n`-th regular continued fraction partial quotient `a_n`
of `e = [2; 1, 2, 1, 1, 4, ...]`. -/
def eulerCFDigit : ℕ → ℤ
  | 0 => 2
  | n + 1 => if n % 3 = 1 then 2 * (((n + 2) / 3 : ℕ) : ℤ) else 1

@[simp] lemma eulerCFDigit_zero : eulerCFDigit 0 = 2 := rfl
@[simp] lemma eulerCFDigit_one : eulerCFDigit 1 = 1 := rfl
@[simp] lemma eulerCFDigit_two : eulerCFDigit 2 = 2 := rfl
@[simp] lemma eulerCFDigit_three : eulerCFDigit 3 = 1 := rfl
@[simp] lemma eulerCFDigit_four : eulerCFDigit 4 = 1 := rfl

lemma eulerCFDigit_three_mul_add_one (j : ℕ) : eulerCFDigit (3 * j + 1) = 1 := by
  simp [eulerCFDigit, Nat.mul_mod_right]

lemma eulerCFDigit_three_mul_add_two (j : ℕ) :
    eulerCFDigit (3 * j + 2) = 2 * ((j + 1 : ℕ) : ℤ) := by
  have hmod : (3 * j + 1) % 3 = 1 := by omega
  have hdiv : (3 * j + 1 + 2) / 3 = j + 1 := by omega
  simp [eulerCFDigit, hmod, hdiv]

lemma eulerCFDigit_three_mul_add_three (j : ℕ) : eulerCFDigit (3 * j + 3) = 1 := by
  have hmod : (3 * j + 2) % 3 = 2 := by omega
  simp [eulerCFDigit, hmod]

lemma eulerCFDigit_three_mul_sub_one (j : ℕ) (hj : 1 ≤ j) :
    eulerCFDigit (3 * j - 1) = 2 * (j : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [show 3 * (m + 1) - 1 = 3 * m + 2 by omega]
  exact eulerCFDigit_three_mul_add_two m

lemma eulerCFDigit_three_mul (j : ℕ) (hj : 1 ≤ j) : eulerCFDigit (3 * j) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  exact eulerCFDigit_three_mul_add_three m

lemma eulerCFDigit_pos (n : ℕ) : 0 < eulerCFDigit n := by
  rcases n with _ | n
  · norm_num
  · simp only [eulerCFDigit]
    split_ifs with h
    · have : 1 ≤ (n + 2) / 3 := by omega
      have : (1 : ℤ) ≤ ((n + 2) / 3 : ℕ) := by exact_mod_cast this
      linarith
    · norm_num

/-- Paired two-step recursion `(X_n, X_{n+1})` for the full convergents of `e`. -/
def fullConvPair (x0 x1 : ℤ) : ℕ → ℤ × ℤ
  | 0 => (x0, x1)
  | n + 1 =>
    let prev := fullConvPair x0 x1 n
    (prev.2, eulerCFDigit (n + 2) * prev.2 + prev.1)

/-- Full regular convergent numerators `p_n` of `e`: `2, 3, 8, 11, 19, 87, 106, 193, ...`. -/
def pFull (n : ℕ) : ℤ := (fullConvPair 2 3 n).1

/-- Full regular convergent denominators `q_n` of `e`: `1, 1, 3, 4, 7, 32, 39, 71, ...`. -/
def qFull (n : ℕ) : ℤ := (fullConvPair 1 1 n).1

@[simp] lemma pFull_zero : pFull 0 = 2 := rfl
@[simp] lemma pFull_one : pFull 1 = 3 := rfl
@[simp] lemma pFull_two : pFull 2 = 8 := rfl
@[simp] lemma pFull_three : pFull 3 = 11 := rfl
@[simp] lemma pFull_four : pFull 4 = 19 := rfl

@[simp] lemma qFull_zero : qFull 0 = 1 := rfl
@[simp] lemma qFull_one : qFull 1 = 1 := rfl
@[simp] lemma qFull_two : qFull 2 = 3 := rfl
@[simp] lemma qFull_three : qFull 3 = 4 := rfl
@[simp] lemma qFull_four : qFull 4 = 7 := rfl

private lemma fullConvPair_snd (x0 x1 : ℤ) (n : ℕ) :
    (fullConvPair x0 x1 n).2 = (fullConvPair x0 x1 (n + 1)).1 := by
  cases n <;> rfl

private lemma fullConvPair_rec (x0 x1 : ℤ) (n : ℕ) :
    (fullConvPair x0 x1 (n + 2)).1 =
      eulerCFDigit (n + 2) * (fullConvPair x0 x1 (n + 1)).1 + (fullConvPair x0 x1 n).1 := by
  have h := congrArg Prod.fst (show fullConvPair x0 x1 (n + 2) = _ from rfl)
  dsimp only [fullConvPair] at h
  rw [fullConvPair_snd] at h
  exact h

lemma pFull_rec (n : ℕ) :
    pFull (n + 2) = eulerCFDigit (n + 2) * pFull (n + 1) + pFull n :=
  fullConvPair_rec 2 3 n

lemma qFull_rec (n : ℕ) :
    qFull (n + 2) = eulerCFDigit (n + 2) * qFull (n + 1) + qFull n :=
  fullConvPair_rec 1 1 n

/-- Unified block induction relating full convergents `(fullConvPair x0 x1)` to
selected convergents `(selPair s0 s1)`. -/
private lemma fullConvPair_block_eq (x0 x1 s0 s1 : ℤ)
    (h0 : 2 * x0 = s1 + s0) (h1 : x1 = s1) (j : ℕ) :
    2 * (fullConvPair x0 x1 (3 * j)).1 = (selPair s0 s1 (j + 1)).1 + (selPair s0 s1 j).1 ∧
    (fullConvPair x0 x1 (3 * j + 1)).1 = (selPair s0 s1 (j + 1)).1 ∧
    2 * (fullConvPair x0 x1 (3 * j + 2)).1 =
      (selPair s0 s1 (j + 2)).1 - (selPair s0 s1 (j + 1)).1 := by
  induction j with
  | zero =>
    have hrec0 := fullConvPair_rec x0 x1 0
    have hsrec0 := selPair_rec s0 s1 0
    have ha0 : (fullConvPair x0 x1 0).1 = x0 := rfl
    have ha1 : (fullConvPair x0 x1 1).1 = x1 := rfl
    have hs0 : (selPair s0 s1 0).1 = s0 := rfl
    have hs1 : (selPair s0 s1 1).1 = s1 := rfl
    rw [Nat.mul_zero, Nat.zero_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [ha0, hs1, hs0, h0]
    · rw [ha1, hs1, h1]
    · rw [hrec0, hsrec0, ha0, ha1, hs0, hs1, eulerCFDigit_two]
      norm_num at *
      linarith
  | succ j ih =>
    rcases ih with ⟨ih0, ih1, ih2⟩
    have h_a3 : (fullConvPair x0 x1 (3 * (j + 1))).1 =
        eulerCFDigit (3 * j + 3) * (fullConvPair x0 x1 (3 * j + 2)).1 +
          (fullConvPair x0 x1 (3 * j + 1)).1 := by
      simpa [Nat.mul_add, Nat.add_assoc] using fullConvPair_rec x0 x1 (3 * j + 1)
    have h_a4 : (fullConvPair x0 x1 (3 * (j + 1) + 1)).1 =
        eulerCFDigit (3 * j + 4) * (fullConvPair x0 x1 (3 * (j + 1))).1 +
          (fullConvPair x0 x1 (3 * j + 2)).1 := by
      simpa [Nat.mul_add, Nat.add_assoc] using fullConvPair_rec x0 x1 (3 * j + 2)
    have h_a5 : (fullConvPair x0 x1 (3 * (j + 1) + 2)).1 =
        eulerCFDigit (3 * j + 5) * (fullConvPair x0 x1 (3 * (j + 1) + 1)).1 +
          (fullConvPair x0 x1 (3 * (j + 1))).1 := by
      simpa [Nat.mul_add, Nat.add_assoc] using fullConvPair_rec x0 x1 (3 * j + 3)
    have hd3 : eulerCFDigit (3 * j + 3) = 1 := eulerCFDigit_three_mul_add_three j
    have hd4 : eulerCFDigit (3 * j + 4) = 1 := by
      rw [show 3 * j + 4 = 3 * (j + 1) + 1 by ring]
      exact eulerCFDigit_three_mul_add_one (j + 1)
    have hd5 : eulerCFDigit (3 * j + 5) = 2 * ((j + 2 : ℕ) : ℤ) := by
      simpa [Nat.mul_add, Nat.add_assoc] using eulerCFDigit_three_mul_add_two (j + 1)
    have h_step0 : 2 * (fullConvPair x0 x1 (3 * (j + 1))).1 =
        (selPair s0 s1 (j + 2)).1 + (selPair s0 s1 (j + 1)).1 := by
      rw [h_a3, hd3]; linarith
    have h_step1 : (fullConvPair x0 x1 (3 * (j + 1) + 1)).1 = (selPair s0 s1 (j + 2)).1 := by
      have h2 : 2 * (fullConvPair x0 x1 (3 * (j + 1) + 1)).1 = 2 * (selPair s0 s1 (j + 2)).1 := by
        rw [h_a4, hd4]; linarith
      linarith
    have hsrec : (selPair s0 s1 (j + 3)).1 =
        (4 * ((j + 2 : ℕ) : ℤ) + 2) * (selPair s0 s1 (j + 2)).1 + (selPair s0 s1 (j + 1)).1 := by
      simpa [Nat.add_assoc] using selPair_rec s0 s1 (j + 1)
    have h_step2 : 2 * (fullConvPair x0 x1 (3 * (j + 1) + 2)).1 =
        (selPair s0 s1 (j + 3)).1 - (selPair s0 s1 (j + 2)).1 := by
      rw [h_a5, hd5, h_step1]
      have hcast : ((j + 2 : ℕ) : ℤ) = (j : ℤ) + 2 := by push_cast; ring
      linarith [h_step0, hsrec, hcast]
    exact ⟨h_step0, h_step1, h_step2⟩

lemma two_mul_qFull_three_mul (j : ℕ) :
    2 * qFull (3 * j) = Qsel (j + 1) + Qsel j :=
  (fullConvPair_block_eq 1 1 1 1 (by norm_num) rfl j).1

lemma qFull_three_mul_add_one (j : ℕ) :
    qFull (3 * j + 1) = Qsel (j + 1) :=
  (fullConvPair_block_eq 1 1 1 1 (by norm_num) rfl j).2.1

lemma two_mul_qFull_three_mul_add_two (j : ℕ) :
    2 * qFull (3 * j + 2) = Qsel (j + 2) - Qsel (j + 1) :=
  (fullConvPair_block_eq 1 1 1 1 (by norm_num) rfl j).2.2

lemma two_mul_pFull_three_mul (j : ℕ) :
    2 * pFull (3 * j) = Psel (j + 1) + Psel j :=
  (fullConvPair_block_eq 2 3 1 3 (by norm_num) rfl j).1

lemma pFull_three_mul_add_one (j : ℕ) :
    pFull (3 * j + 1) = Psel (j + 1) :=
  (fullConvPair_block_eq 2 3 1 3 (by norm_num) rfl j).2.1

lemma two_mul_pFull_three_mul_add_two (j : ℕ) :
    2 * pFull (3 * j + 2) = Psel (j + 2) - Psel (j + 1) :=
  (fullConvPair_block_eq 2 3 1 3 (by norm_num) rfl j).2.2

lemma qFull_three_mul (j : ℕ) :
    qFull (3 * j) = (Qsel (j + 1) + Qsel j) / 2 := by
  have h := two_mul_qFull_three_mul j
  omega

lemma qFull_three_mul_sub_two (j : ℕ) (hj : 1 ≤ j) :
    qFull (3 * j - 2) = Qsel j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [show 3 * (m + 1) - 2 = 3 * m + 1 by omega]
  exact qFull_three_mul_add_one m

lemma qFull_three_mul_sub_one (j : ℕ) (hj : 1 ≤ j) :
    qFull (3 * j - 1) = (Qsel (j + 1) - Qsel j) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [show 3 * (m + 1) - 1 = 3 * m + 2 by omega, show m + 1 + 1 = m + 2 by ring]
  have h := two_mul_qFull_three_mul_add_two m
  omega

lemma pFull_three_mul (j : ℕ) :
    pFull (3 * j) = (Psel (j + 1) + Psel j) / 2 := by
  have h := two_mul_pFull_three_mul j
  omega

lemma pFull_three_mul_sub_two (j : ℕ) (hj : 1 ≤ j) :
    pFull (3 * j - 2) = Psel j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [show 3 * (m + 1) - 2 = 3 * m + 1 by omega]
  exact pFull_three_mul_add_one m

lemma pFull_three_mul_sub_one (j : ℕ) (hj : 1 ≤ j) :
    pFull (3 * j - 1) = (Psel (j + 1) - Psel j) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [show 3 * (m + 1) - 1 = 3 * m + 2 by omega, show m + 1 + 1 = m + 2 by ring]
  have h := two_mul_pFull_three_mul_add_two m
  omega

lemma qFull_pos (n : ℕ) : 0 < qFull n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · norm_num
    · norm_num
    · rw [qFull_rec]
      have hd : 0 < eulerCFDigit (k + 2) := eulerCFDigit_pos (k + 2)
      have h1 : 0 < qFull (k + 1) := ih (k + 1) (by omega)
      have h0 : 0 < qFull k := ih k (by omega)
      nlinarith

lemma qFull_mono : Monotone qFull := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases n with _ | k
  · norm_num
  · rw [qFull_rec]
    have hd : 1 ≤ eulerCFDigit (k + 2) := eulerCFDigit_pos (k + 2)
    have h1 : 0 < qFull (k + 1) := qFull_pos (k + 1)
    have h0 : 0 < qFull k := qFull_pos k
    nlinarith

lemma qFull_tendsto_atTop : Tendsto (fun n : ℕ => (qFull n : ℝ)) atTop atTop := by
  have hsub : Tendsto (fun j : ℕ => (qFull (3 * j + 1) : ℝ)) atTop atTop := by
    simp_rw [qFull_three_mul_add_one]
    exact _root_.Qsel_tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  rw [tendsto_atTop_atTop] at hsub ⊢
  intro b
  obtain ⟨J, hJ⟩ := hsub b
  refine ⟨3 * J + 1, fun n hn => ?_⟩
  exact (hJ J le_rfl).trans (by exact_mod_cast qFull_mono hn)

/-- Standard unimodular determinant of adjacent full convergents:
`pFull n * qFull (n + 1) - pFull (n + 1) * qFull n = (-1) ^ (n + 1)`. -/
theorem fullConv_det (n : ℕ) :
    pFull n * qFull (n + 1) - pFull (n + 1) * qFull n = (-1 : ℤ) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pFull_rec, qFull_rec]
    have hstep : pFull (n + 1) * (eulerCFDigit (n + 2) * qFull (n + 1) + qFull n) -
        (eulerCFDigit (n + 2) * pFull (n + 1) + pFull n) * qFull (n + 1) =
        -(pFull n * qFull (n + 1) - pFull (n + 1) * qFull n) := by ring
    rw [hstep, ih, pow_succ]
    ring

theorem fullConv_coprime (n : ℕ) : Int.gcd (pFull n) (qFull n) = 1 := by
  have hdet := fullConv_det n
  have hdvd1 : (Int.gcd (pFull n) (qFull n) : ℤ) ∣ pFull n :=
    Int.gcd_dvd_left _ _
  have hdvd2 : (Int.gcd (pFull n) (qFull n) : ℤ) ∣ qFull n :=
    Int.gcd_dvd_right _ _
  have h1 : (Int.gcd (pFull n) (qFull n) : ℤ) ∣
      (pFull n * qFull (n + 1) - pFull (n + 1) * qFull n) :=
    dvd_sub (dvd_mul_of_dvd_left hdvd1 _) (dvd_mul_of_dvd_right hdvd2 _)
  rw [hdet] at h1
  have hnat : (Int.gcd (pFull n) (qFull n) : ℤ) ∣ 1 := by
    rcases Nat.even_or_odd (n + 1) with he | ho
    · rwa [he.neg_one_pow] at h1
    · rw [ho.neg_one_pow] at h1; exact dvd_neg.mp h1
  have hnat' : Int.gcd (pFull n) (qFull n) ∣ 1 := by exact_mod_cast hnat
  exact Nat.eq_one_of_dvd_one hnat'

/-! ## Part 2: Exact Error Identities and Kraaikamp–Liardet Weights -/

/-- Exact continued fraction error `fullDelta n = q_n * e - p_n` for all convergents of `e`. -/
def fullDelta (n : ℕ) : ℝ := (qFull n : ℝ) * Real.exp 1 - (pFull n : ℝ)

lemma fullDelta_three_mul (j : ℕ) :
    fullDelta (3 * j) = (deltaSel (j + 1) + deltaSel j) / 2 := by
  have hq : (qFull (3 * j) : ℝ) = ((Qsel (j + 1) : ℝ) + (Qsel j : ℝ)) / 2 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (two_mul_qFull_three_mul j)
    push_cast at h
    linarith
  have hp : (pFull (3 * j) : ℝ) = ((Psel (j + 1) : ℝ) + (Psel j : ℝ)) / 2 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (two_mul_pFull_three_mul j)
    push_cast at h
    linarith
  unfold fullDelta deltaSel
  rw [hq, hp]
  ring

lemma fullDelta_three_mul_add_one (j : ℕ) :
    fullDelta (3 * j + 1) = deltaSel (j + 1) := by
  unfold fullDelta deltaSel
  rw [qFull_three_mul_add_one, pFull_three_mul_add_one]

lemma fullDelta_three_mul_add_two (j : ℕ) :
    fullDelta (3 * j + 2) = (deltaSel (j + 2) - deltaSel (j + 1)) / 2 := by
  have hq : (qFull (3 * j + 2) : ℝ) = ((Qsel (j + 2) : ℝ) - (Qsel (j + 1) : ℝ)) / 2 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (two_mul_qFull_three_mul_add_two j)
    push_cast at h
    linarith
  have hp : (pFull (3 * j + 2) : ℝ) = ((Psel (j + 2) : ℝ) - (Psel (j + 1) : ℝ)) / 2 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (two_mul_pFull_three_mul_add_two j)
    push_cast at h
    linarith
  unfold fullDelta deltaSel
  rw [hq, hp]
  ring

lemma abs_deltaSel_succ_lt (m : ℕ) (hm : 1 ≤ m) :
    |deltaSel (m + 1)| < |deltaSel m| := by
  have h1 : |deltaSel (m + 1)| ≤ 2 / (Qsel (m + 2) : ℝ) :=
    abs_deltaSel_le_two_div (m + 1) (by omega)
  have hsum : (Qsel m : ℝ) * |deltaSel (m + 1)| + (Qsel (m + 1) : ℝ) * |deltaSel m| = 2 :=
    abs_sum_eq_two m hm
  have hQm_pos : (0 : ℝ) < (Qsel m : ℝ) := by exact_mod_cast Classification.Qsel_pos m
  have hQm1_pos : (0 : ℝ) < (Qsel (m + 1) : ℝ) := by
    exact_mod_cast Classification.Qsel_pos (m + 1)
  have hQm2_pos : (0 : ℝ) < (Qsel (m + 2) : ℝ) := by
    exact_mod_cast Classification.Qsel_pos (m + 2)
  have hrec2 : (Qsel (m + 2) : ℝ) =
      (4 * ((m + 1 : ℕ) : ℝ) + 2) * (Qsel (m + 1) : ℝ) + (Qsel m : ℝ) := by
    exact_mod_cast Classification.Qsel_rec' (m + 1) (by omega)
  have h6 : 6 * (Qsel (m + 1) : ℝ) < (Qsel (m + 2) : ℝ) := by
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
    rw [hrec2]
    nlinarith
  have h2m : 2 * (Qsel m : ℝ) ≤ (Qsel (m + 1) : ℝ) := by
    exact_mod_cast Classification.Qsel_double m hm
  have h4m : 4 * (Qsel m : ℝ) < (Qsel (m + 2) : ℝ) := by linarith
  have hprod_le : (Qsel m : ℝ) * |deltaSel (m + 1)| ≤ 1 / 2 := by
    calc (Qsel m : ℝ) * |deltaSel (m + 1)|
        ≤ (Qsel m : ℝ) * (2 / (Qsel (m + 2) : ℝ)) := mul_le_mul_of_nonneg_left h1 hQm_pos.le
      _ = (2 * (Qsel m : ℝ)) / (Qsel (m + 2) : ℝ) := by ring
      _ ≤ (2 * (Qsel m : ℝ)) / (4 * (Qsel m : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h4m.le
      _ = 1 / 2 := by field_simp; ring
  have hlower : 3 / (2 * (Qsel (m + 1) : ℝ)) ≤ |deltaSel m| := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hupper : |deltaSel (m + 1)| < 1 / (3 * (Qsel (m + 1) : ℝ)) := by
    calc |deltaSel (m + 1)| ≤ 2 / (Qsel (m + 2) : ℝ) := h1
      _ < 2 / (6 * (Qsel (m + 1) : ℝ)) :=
          div_lt_div_of_pos_left (by positivity) (by positivity) h6
      _ = 1 / (3 * (Qsel (m + 1) : ℝ)) := by ring
  have hgap : 1 / (3 * (Qsel (m + 1) : ℝ)) < 3 / (2 * (Qsel (m + 1) : ℝ)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

lemma abs_deltaSel_pos (m : ℕ) (hm : 1 ≤ m) : 0 < |deltaSel m| := by
  have hs := Hermite.sign_alternation m hm
  rw [← sign_eq_abs m hm]
  exact hs

lemma abs_fullDelta_three_mul_add_one (j : ℕ) :
    |fullDelta (3 * j + 1)| = |deltaSel (j + 1)| := by
  rw [fullDelta_three_mul_add_one]

lemma abs_fullDelta_three_mul_add_two (j : ℕ) :
    |fullDelta (3 * j + 2)| = (|deltaSel (j + 1)| + |deltaSel (j + 2)|) / 2 := by
  rw [fullDelta_three_mul_add_two]
  have hs1 := sign_eq_abs (j + 1) (by omega)
  have hs2 := sign_eq_abs (j + 2) (by omega)
  have hpow : (-1 : ℝ) ^ (j + 2) = -((-1 : ℝ) ^ (j + 1)) := by rw [pow_succ]; ring
  have hmul : (-1 : ℝ) ^ (j + 2) * (deltaSel (j + 2) - deltaSel (j + 1)) =
      |deltaSel (j + 2)| + |deltaSel (j + 1)| := by
    rw [mul_sub, hs2, hpow, neg_mul, hs1]
    ring
  have hpos : 0 ≤ |deltaSel (j + 2)| + |deltaSel (j + 1)| := by positivity
  have habs_sign : |(-1 : ℝ) ^ (j + 2) * (deltaSel (j + 2) - deltaSel (j + 1))| =
      |deltaSel (j + 2) - deltaSel (j + 1)| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), ← habs_sign, hmul, abs_of_nonneg hpos]
  ring

lemma abs_fullDelta_three_mul_add_three (j : ℕ) :
    |fullDelta (3 * j + 3)| = (|deltaSel (j + 1)| - |deltaSel (j + 2)|) / 2 := by
  have h3 : 3 * j + 3 = 3 * (j + 1) := by ring
  rw [h3, fullDelta_three_mul]
  have hs1 := sign_eq_abs (j + 1) (by omega)
  have hs2 := sign_eq_abs (j + 2) (by omega)
  have hpow : (-1 : ℝ) ^ (j + 1) = -((-1 : ℝ) ^ (j + 2)) := by
    have : (-1 : ℝ) ^ (j + 2) = -((-1 : ℝ) ^ (j + 1)) := by rw [pow_succ]; ring
    linarith
  have hmul : (-1 : ℝ) ^ (j + 1) * (deltaSel (j + 2) + deltaSel (j + 1)) =
      |deltaSel (j + 1)| - |deltaSel (j + 2)| := by
    rw [mul_add, hs1, hpow, neg_mul, hs2]
    ring
  have hnonneg : 0 ≤ |deltaSel (j + 1)| - |deltaSel (j + 2)| :=
    sub_nonneg.mpr (abs_deltaSel_succ_lt (j + 1) (by omega)).le
  have habs_sign : |(-1 : ℝ) ^ (j + 1) * (deltaSel (j + 2) + deltaSel (j + 1))| =
      |deltaSel (j + 2) + deltaSel (j + 1)| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), ← habs_sign, hmul, abs_of_nonneg hnonneg]

lemma abs_fullDelta_zero_pos : 0 < |fullDelta 0| := by
  have hexp : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  have hfd : fullDelta 0 = Real.exp 1 - 2 := by
    simp [fullDelta, qFull_zero, pFull_zero]
  rw [hfd]
  exact abs_pos.mpr (by linarith)

lemma abs_fullDelta_pos (n : ℕ) : 0 < |fullDelta n| := by
  rcases n with _ | n
  · exact abs_fullDelta_zero_pos
  · have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hmod with h | h | h
    · rw [show n + 1 = 3 * (n / 3) + 1 by omega, abs_fullDelta_three_mul_add_one]
      exact abs_deltaSel_pos _ (by omega)
    · rw [show n + 1 = 3 * (n / 3) + 2 by omega, abs_fullDelta_three_mul_add_two]
      have h1 := abs_deltaSel_pos (n / 3 + 1) (by omega)
      have h2 := abs_deltaSel_pos (n / 3 + 2) (by omega)
      linarith
    · rw [show n + 1 = 3 * (n / 3) + 3 by omega, abs_fullDelta_three_mul_add_three]
      have hlt := abs_deltaSel_succ_lt (n / 3 + 1) (by omega)
      linarith

theorem pFull_div_qFull_tendsto_exp :
    Tendsto (fun n : ℕ => (pFull n : ℝ) / (qFull n : ℝ)) atTop (nhds (Real.exp 1)) := by
  have hdelta : Tendsto fullDelta atTop (nhds 0) := by
    have h0 : Tendsto (fun j : ℕ => |fullDelta (3 * j)|) atTop (nhds 0) := by
      have heq : ∀ j : ℕ, |fullDelta (3 * j)| = |deltaSel (j + 1) + deltaSel j| / 2 := fun j => by
        rw [fullDelta_three_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp_rw [heq]
      have h1 : Tendsto (fun j : ℕ => deltaSel (j + 1)) atTop (nhds 0) :=
        deltaSel_tendsto_zero.comp (tendsto_add_atTop_nat 1)
      simpa using ((h1.add deltaSel_tendsto_zero).abs).div_const 2
    have h1 : Tendsto (fun j : ℕ => |fullDelta (3 * j + 1)|) atTop (nhds 0) := by
      simp_rw [abs_fullDelta_three_mul_add_one]
      simpa using (deltaSel_tendsto_zero.comp (tendsto_add_atTop_nat 1)).abs
    have h2 : Tendsto (fun j : ℕ => |fullDelta (3 * j + 2)|) atTop (nhds 0) := by
      simp_rw [abs_fullDelta_three_mul_add_two]
      have ha : Tendsto (fun j : ℕ => |deltaSel (j + 1)|) atTop (nhds 0) := by
        simpa using (deltaSel_tendsto_zero.comp (tendsto_add_atTop_nat 1)).abs
      have hb : Tendsto (fun j : ℕ => |deltaSel (j + 2)|) atTop (nhds 0) := by
        simpa using (deltaSel_tendsto_zero.comp (tendsto_add_atTop_nat 2)).abs
      simpa using (ha.add hb).div_const 2
    have habs : Tendsto (fun n : ℕ => |fullDelta n|) atTop (nhds 0) := by
      rw [Metric.tendsto_atTop] at h0 h1 h2 ⊢
      intro ε hε
      obtain ⟨J0, hJ0⟩ := h0 ε hε
      obtain ⟨J1, hJ1⟩ := h1 ε hε
      obtain ⟨J2, hJ2⟩ := h2 ε hε
      refine ⟨3 * max J0 (max J1 J2), fun n hn => ?_⟩
      have hm : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hm with h | h | h
      · have hj : J0 ≤ n / 3 := by omega
        have := hJ0 (n / 3) hj
        rwa [show 3 * (n / 3) = n by omega] at this
      · have hj : J1 ≤ n / 3 := by omega
        have := hJ1 (n / 3) hj
        rwa [show 3 * (n / 3) + 1 = n by omega] at this
      · have hj : J2 ≤ n / 3 := by omega
        have := hJ2 (n / 3) hj
        rwa [show 3 * (n / 3) + 2 = n by omega] at this
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using habs)
  have hdiv : Tendsto (fun n : ℕ => fullDelta n / (qFull n : ℝ)) atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℕ => (qFull n : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp qFull_tendsto_atTop
    simpa [div_eq_mul_inv] using hdelta.mul hinv
  have hsub : Tendsto (fun n : ℕ => Real.exp 1 - fullDelta n / (qFull n : ℝ))
      atTop (nhds (Real.exp 1)) := by
    simpa using tendsto_const_nhds.sub hdiv
  refine hsub.congr fun n => ?_
  have hq : (qFull n : ℝ) ≠ 0 := (by exact_mod_cast qFull_pos n : (0 : ℝ) < (qFull n : ℝ)).ne'
  unfold fullDelta
  field_simp
  ring

/-- Kraaikamp–Liardet denominator product `q_n * |q_n * e - p_n|`. -/
def fullKLProd (n : ℕ) : ℝ := (qFull n : ℝ) * |fullDelta n|

/-- Kraaikamp–Liardet weight `1 / (q_n * |q_n * e - p_n|)`. -/
def fullKLWeight (n : ℕ) : ℝ := (fullKLProd n)⁻¹

lemma fullKLProd_pos (n : ℕ) : 0 < fullKLProd n :=
  mul_pos (by exact_mod_cast qFull_pos n) (abs_fullDelta_pos n)

lemma fullKLWeight_pos (n : ℕ) : 0 < fullKLWeight n :=
  inv_pos.mpr (fullKLProd_pos n)

private lemma Qsel_mul_abs_deltaSel_succ_tendsto_zero :
    Tendsto (fun m : ℕ => (Qsel m : ℝ) * |deltaSel (m + 1)|) atTop (nhds 0) := by
  have hle : ∀ᶠ m : ℕ in atTop,
      0 ≤ (Qsel m : ℝ) * |deltaSel (m + 1)| ∧
      (Qsel m : ℝ) * |deltaSel (m + 1)| ≤ 2 / ((4 * ((m + 1 : ℕ) : ℝ) + 2)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hQm : (0 : ℝ) < (Qsel m : ℝ) := by exact_mod_cast Classification.Qsel_pos m
    have hQm1 : (0 : ℝ) < (Qsel (m + 1) : ℝ) := by exact_mod_cast Classification.Qsel_pos (m + 1)
    have hQm2 : (0 : ℝ) < (Qsel (m + 2) : ℝ) := by exact_mod_cast Classification.Qsel_pos (m + 2)
    refine ⟨mul_nonneg hQm.le (abs_nonneg _), ?_⟩
    have h1 := abs_deltaSel_le_two_div (m + 1) (by omega)
    have h2 : (Qsel m : ℝ) ≤ (Qsel (m + 1) : ℝ) := by
      have hInt : Qsel m ≤ Qsel (m + 1) := by
        have := Classification.Qsel_double m hm
        have hQp : 0 < Qsel m := Classification.Qsel_pos m
        omega
      exact_mod_cast hInt
    have hrec : (Qsel (m + 2) : ℝ) =
        (4 * ((m + 1 : ℕ) : ℝ) + 2) * (Qsel (m + 1) : ℝ) + (Qsel m : ℝ) := by
      exact_mod_cast Classification.Qsel_rec' (m + 1) (by omega)
    have hgrow : (4 * ((m + 1 : ℕ) : ℝ) + 2) * (Qsel m : ℝ) ≤ (Qsel (m + 2) : ℝ) := by
      rw [hrec]
      have hc : (0 : ℝ) < 4 * ((m + 1 : ℕ) : ℝ) + 2 := by positivity
      nlinarith
    calc (Qsel m : ℝ) * |deltaSel (m + 1)|
        ≤ (Qsel m : ℝ) * (2 / (Qsel (m + 2) : ℝ)) := mul_le_mul_of_nonneg_left h1 hQm.le
      _ = (2 * (Qsel m : ℝ)) / (Qsel (m + 2) : ℝ) := by ring
      _ ≤ (2 * (Qsel m : ℝ)) / ((4 * ((m + 1 : ℕ) : ℝ) + 2) * (Qsel m : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hgrow
      _ = 2 / (4 * ((m + 1 : ℕ) : ℝ) + 2) := by field_simp
  have hden : Tendsto (fun m : ℕ => 4 * ((m + 1 : ℕ) : ℝ) + 2) atTop atTop := by
    have h1 : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact (h1.const_mul_atTop (by norm_num)).atTop_add tendsto_const_nhds
  have htop : Tendsto (fun m : ℕ => 2 / (4 * ((m + 1 : ℕ) : ℝ) + 2)) atTop (nhds 0) :=
    hden.const_div_atTop 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
    (hle.mono fun _ h => h.1) (hle.mono fun _ h => h.2)

private lemma Qsel_succ_mul_abs_deltaSel_tendsto_two :
    Tendsto (fun m : ℕ => (Qsel (m + 1) : ℝ) * |deltaSel m|) atTop (nhds 2) := by
  have heq : ∀ᶠ m : ℕ in atTop,
      (Qsel (m + 1) : ℝ) * |deltaSel m| = 2 - (Qsel m : ℝ) * |deltaSel (m + 1)| := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    linarith [abs_sum_eq_two m hm]
  have hlim : Tendsto (fun m : ℕ => 2 - (Qsel m : ℝ) * |deltaSel (m + 1)|) atTop (nhds 2) := by
    simpa using tendsto_const_nhds.sub Qsel_mul_abs_deltaSel_succ_tendsto_zero
  exact hlim.congr' (heq.mono fun _ h => h.symm)

private lemma Qsel_mul_abs_deltaSel_tendsto_zero :
    Tendsto (fun m : ℕ => (Qsel m : ℝ) * |deltaSel m|) atTop (nhds 0) := by
  have hle : ∀ᶠ m : ℕ in atTop,
      0 ≤ (Qsel m : ℝ) * |deltaSel m| ∧
      (Qsel m : ℝ) * |deltaSel m| ≤ 1 / (2 * (m : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hQm : (0 : ℝ) < (Qsel m : ℝ) := by exact_mod_cast Classification.Qsel_pos m
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    refine ⟨mul_nonneg hQm.le (abs_nonneg _), ?_⟩
    have hlt := abs_deltaSel_lt m hm
    calc (Qsel m : ℝ) * |deltaSel m|
        ≤ (Qsel m : ℝ) * (1 / (2 * (m : ℝ) * (Qsel m : ℝ))) :=
          mul_le_mul_of_nonneg_left hlt.le hQm.le
      _ = 1 / (2 * (m : ℝ)) := by field_simp
  have htop : Tendsto (fun m : ℕ => 1 / (2 * (m : ℝ))) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)).const_div_atTop 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
    (hle.mono fun _ h => h.1) (hle.mono fun _ h => h.2)

lemma two_mul_add_one_lt_fullKLWeight_sub (j : ℕ) (hj : 1 ≤ j) :
    2 * (j : ℝ) + 1 < fullKLWeight (3 * j - 2) := by
  have hq : qFull (3 * j - 2) = Qsel j := qFull_three_mul_sub_two j hj
  have hd : |fullDelta (3 * j - 2)| = |deltaSel j| := by
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [show 3 * (m + 1) - 2 = 3 * m + 1 by omega]
    exact abs_fullDelta_three_mul_add_one m
  have hprod_eq : fullKLProd (3 * j - 2) = (Qsel j : ℝ) * |deltaSel j| := by
    rw [fullKLProd, hq, hd]
  have hsum := abs_sum_eq_two j hj
  have hQm : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Classification.Qsel_pos j
  have hQm1 : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast Classification.Qsel_pos (j + 1)
  have hQm_prev : (0 : ℝ) < (Qsel (j - 1) : ℝ) := by
    exact_mod_cast Classification.Qsel_pos (j - 1)
  have hpos2 : 0 < (Qsel j : ℝ) * |deltaSel (j + 1)| :=
    mul_pos hQm (abs_deltaSel_pos (j + 1) (by omega))
  have hlt2 : (Qsel (j + 1) : ℝ) * |deltaSel j| < 2 := by linarith
  have hrec : (Qsel (j + 1) : ℝ) =
      (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by
    exact_mod_cast Classification.Qsel_rec' j hj
  have hprod_lt : (2 * (j : ℝ) + 1) * fullKLProd (3 * j - 2) < 1 := by
    rw [hprod_eq]
    have hmul : (4 * (j : ℝ) + 2) * (Qsel j : ℝ) < (Qsel (j + 1) : ℝ) := by linarith
    have hδpos : 0 < |deltaSel j| := abs_deltaSel_pos j hj
    have h1 : (4 * (j : ℝ) + 2) * ((Qsel j : ℝ) * |deltaSel j|) <
        (Qsel (j + 1) : ℝ) * |deltaSel j| := by
      calc (4 * (j : ℝ) + 2) * ((Qsel j : ℝ) * |deltaSel j|)
          = ((4 * (j : ℝ) + 2) * (Qsel j : ℝ)) * |deltaSel j| := by ring
        _ < (Qsel (j + 1) : ℝ) * |deltaSel j| := mul_lt_mul_of_pos_right hmul hδpos
    linarith
  have hklp : 0 < fullKLProd (3 * j - 2) := fullKLProd_pos _
  rw [fullKLWeight, inv_eq_one_div, lt_div_iff₀ hklp]
  exact hprod_lt

theorem tendsto_fullKLWeight_mod1_div :
    Tendsto (fun j : ℕ => fullKLWeight (3 * j + 1) / (2 * ((j + 1 : ℕ) : ℝ)))
      atTop (nhds 1) := by
  have hrec_ratio : Tendsto
      (fun j : ℕ => ((Qsel (j + 2) : ℝ) / (Qsel (j + 1) : ℝ)) / ((j + 1 : ℕ) : ℝ))
      atTop (nhds 4) := by
    have heq : ∀ᶠ j : ℕ in atTop,
        ((Qsel (j + 2) : ℝ) / (Qsel (j + 1) : ℝ)) / ((j + 1 : ℕ) : ℝ) =
          4 + (2 + (Qsel j : ℝ) / (Qsel (j + 1) : ℝ)) / ((j + 1 : ℕ) : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with j hj
      have hj1 : (Qsel (j + 1) : ℝ) ≠ 0 :=
        (by exact_mod_cast Classification.Qsel_pos (j + 1) : (0 : ℝ) < _).ne'
      have hjpos : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hrec : (Qsel (j + 2) : ℝ) =
          (4 * ((j + 1 : ℕ) : ℝ) + 2) * (Qsel (j + 1) : ℝ) + (Qsel j : ℝ) := by
        exact_mod_cast Classification.Qsel_rec' (j + 1) (by omega)
      rw [hrec]
      field_simp
      ring
    have hrem : Tendsto (fun j : ℕ => (2 + (Qsel j : ℝ) / (Qsel (j + 1) : ℝ)) / ((j + 1 : ℕ) : ℝ))
        atTop (nhds 0) := by
      have hbd : ∀ᶠ j : ℕ in atTop,
          0 ≤ (2 + (Qsel j : ℝ) / (Qsel (j + 1) : ℝ)) / ((j + 1 : ℕ) : ℝ) ∧
          (2 + (Qsel j : ℝ) / (Qsel (j + 1) : ℝ)) / ((j + 1 : ℕ) : ℝ) ≤
            3 / ((j + 1 : ℕ) : ℝ) := by
        filter_upwards [eventually_ge_atTop 1] with j hj
        have hQj : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Classification.Qsel_pos j
        have hQj1 : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by
          exact_mod_cast Classification.Qsel_pos (j + 1)
        have hle1 : (Qsel j : ℝ) / (Qsel (j + 1) : ℝ) ≤ 1 := by
          rw [div_le_one hQj1]
          exact_mod_cast (_root_.Qsel_lt_succ j hj).le
        refine ⟨div_nonneg (by positivity) (by positivity), ?_⟩
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      have h3 : Tendsto (fun j : ℕ => 3 / ((j + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).const_div_atTop 3
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
        (hbd.mono fun _ h => h.1) (hbd.mono fun _ h => h.2)
    have h4 : Tendsto (fun j : ℕ => 4 + (2 + (Qsel j : ℝ) / (Qsel (j + 1) : ℝ)) / ((j + 1 : ℕ) : ℝ))
        atTop (nhds 4) := by
      simpa using tendsto_const_nhds.add hrem
    exact h4.congr' (heq.mono fun _ h => h.symm)
  have hnum : Tendsto (fun j : ℕ => (Qsel (j + 2) : ℝ) * |deltaSel (j + 1)|) atTop (nhds 2) :=
    Qsel_succ_mul_abs_deltaSel_tendsto_two.comp (tendsto_add_atTop_nat 1)
  have hprod : Tendsto
      (fun j : ℕ => 2 * ((j + 1 : ℕ) : ℝ) * fullKLProd (3 * j + 1)) atTop (nhds 1) := by
    have hdiv := (hnum.div hrec_ratio (by norm_num)).const_mul 2
    have hlim : (2 : ℝ) * (2 / 4) = 1 := by norm_num
    rw [hlim] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j _
    have hj1 : (Qsel (j + 1) : ℝ) ≠ 0 :=
      (by exact_mod_cast Classification.Qsel_pos (j + 1) : (0 : ℝ) < _).ne'
    have hj2 : (Qsel (j + 2) : ℝ) ≠ 0 :=
      (by exact_mod_cast Classification.Qsel_pos (j + 2) : (0 : ℝ) < _).ne'
    have hjpos : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hden : ((Qsel (j + 2) : ℝ) / (Qsel (j + 1) : ℝ)) / ((j + 1 : ℕ) : ℝ) ≠ 0 :=
      div_ne_zero (div_ne_zero hj2 hj1) hjpos
    rw [fullKLProd, qFull_three_mul_add_one, abs_fullDelta_three_mul_add_one]
    simp only [Pi.div_apply]
    field_simp
  have hinv := hprod.inv₀ (by norm_num)
  rw [inv_one] at hinv
  refine hinv.congr fun j => ?_
  rw [fullKLWeight, div_eq_mul_inv, mul_inv]
  ring

theorem tendsto_fullKLWeight_mod2 :
    Tendsto (fun j : ℕ => fullKLWeight (3 * j + 2)) atTop (nhds 2) := by
  have h4 : Tendsto (fun j : ℕ => 4 * fullKLProd (3 * j + 2)) atTop (nhds 2) := by
    have heq : ∀ j : ℕ, 4 * fullKLProd (3 * j + 2) =
        (Qsel (j + 2) : ℝ) * |deltaSel (j + 1)| + (Qsel (j + 2) : ℝ) * |deltaSel (j + 2)|
          - (Qsel (j + 1) : ℝ) * |deltaSel (j + 1)| - (Qsel (j + 1) : ℝ) * |deltaSel (j + 2)| := by
      intro j
      have hq : (qFull (3 * j + 2) : ℝ) = ((Qsel (j + 2) : ℝ) - (Qsel (j + 1) : ℝ)) / 2 := by
        have h := congrArg (fun z : ℤ => (z : ℝ)) (two_mul_qFull_three_mul_add_two j)
        push_cast at h
        linarith
      rw [fullKLProd, hq, abs_fullDelta_three_mul_add_two]
      ring
    simp_rw [heq]
    have h1 := Qsel_succ_mul_abs_deltaSel_tendsto_two.comp (tendsto_add_atTop_nat 1)
    have h2 := Qsel_mul_abs_deltaSel_tendsto_zero.comp (tendsto_add_atTop_nat 2)
    have h3 := Qsel_mul_abs_deltaSel_tendsto_zero.comp (tendsto_add_atTop_nat 1)
    have h4' := Qsel_mul_abs_deltaSel_succ_tendsto_zero.comp (tendsto_add_atTop_nat 1)
    simpa using (((h1.add h2).sub h3).sub h4')
  have hp : Tendsto (fun j : ℕ => fullKLProd (3 * j + 2)) atTop (nhds (1 / 2)) := by
    convert h4.const_mul (1 / 4 : ℝ) using 1
    · funext j; ring
    · norm_num
  have hinv := hp.inv₀ (by norm_num)
  simpa [fullKLWeight] using hinv

theorem tendsto_fullKLWeight_mod0 :
    Tendsto (fun j : ℕ => fullKLWeight (3 * j + 3)) atTop (nhds 2) := by
  have h4 : Tendsto (fun j : ℕ => 4 * fullKLProd (3 * j + 3)) atTop (nhds 2) := by
    have heq : ∀ j : ℕ, 4 * fullKLProd (3 * j + 3) =
        (Qsel (j + 2) : ℝ) * |deltaSel (j + 1)| - (Qsel (j + 2) : ℝ) * |deltaSel (j + 2)|
          + (Qsel (j + 1) : ℝ) * |deltaSel (j + 1)| - (Qsel (j + 1) : ℝ) * |deltaSel (j + 2)| := by
      intro j
      have h3 : 3 * j + 3 = 3 * (j + 1) := by ring
      have hq : (qFull (3 * j + 3) : ℝ) = ((Qsel (j + 2) : ℝ) + (Qsel (j + 1) : ℝ)) / 2 := by
        have h := congrArg (fun z : ℤ => (z : ℝ)) (two_mul_qFull_three_mul (j + 1))
        push_cast at h
        rw [← h3] at h
        linarith
      rw [fullKLProd, hq, abs_fullDelta_three_mul_add_three]
      ring
    simp_rw [heq]
    have h1 := Qsel_succ_mul_abs_deltaSel_tendsto_two.comp (tendsto_add_atTop_nat 1)
    have h2 := Qsel_mul_abs_deltaSel_tendsto_zero.comp (tendsto_add_atTop_nat 2)
    have h3 := Qsel_mul_abs_deltaSel_tendsto_zero.comp (tendsto_add_atTop_nat 1)
    have h4' := Qsel_mul_abs_deltaSel_succ_tendsto_zero.comp (tendsto_add_atTop_nat 1)
    simpa using (((h1.sub h2).add h3).sub h4')
  have hp : Tendsto (fun j : ℕ => fullKLProd (3 * j + 3)) atTop (nhds (1 / 2)) := by
    convert h4.const_mul (1 / 4 : ℝ) using 1
    · funext j; ring
    · norm_num
  have hinv := hp.inv₀ (by norm_num)
  simpa [fullKLWeight] using hinv

/-! ## Part 3: Lattices, Parity Flip, and Full-Convergent Spectrum Functionals -/

/-- Unimodular integer lattice `ℤ + ℤ e`. -/
def latticeE : Set ℝ :=
  {x | ∃ m n : ℤ, x = (m : ℝ) + (n : ℝ) * Real.exp 1}

/-- The odd coset `(e + 1) / 2 + (ℤ + ℤ e)`. -/
def oddCosetE : Set ℝ :=
  {x | ∃ m n : ℤ, x = (Real.exp 1 + 1) / 2 + ((m : ℝ) + (n : ℝ) * Real.exp 1)}

/-- Parity-flip predicate along the selected nearest integers `M_j(x) = round(Q_j x)`. -/
def parityFlip (x : ℝ) : Prop :=
  ∃ᶠ j : ℕ in atTop, Odd (nearestInt ((Qsel (j + 1) : ℝ) * x) - nearestInt ((Qsel j : ℝ) * x))

/-- Kraaikamp–Liardet normalized error sequence along all convergents of `e`. -/
def fullKLSeq (x : ℝ) (n : ℕ) : ℝ :=
  fullKLWeight n * distToNearestInt ((qFull n : ℝ) * x)

/-- Full-convergent Kraaikamp–Liardet spectrum functional `Λ_full^KL(x)`. -/
def fullKLSpectrum (x : ℝ) : ℝ≥0∞ :=
  limsup (fun n : ℕ => ENNReal.ofReal (fullKLSeq x n)) atTop

/-- Raw partial-quotient sequence `a_{n+1} * ‖q_n x‖` along all convergents of `e`. -/
def fullRawSeq (x : ℝ) (n : ℕ) : ℝ :=
  (eulerCFDigit (n + 1) : ℝ) * distToNearestInt ((qFull n : ℝ) * x)

/-- Raw partial-quotient full-convergent spectrum functional `Λ_full^raw(x)`. -/
def fullRawSpectrum (x : ℝ) : ℝ≥0∞ :=
  limsup (fun n : ℕ => ENNReal.ofReal (fullRawSeq x n)) atTop

lemma latticeE_subset_latticeL : latticeE ⊆ latticeL := by
  rintro x ⟨m, n, rfl⟩
  refine ⟨m - n, 2 * n, ?_⟩
  push_cast
  ring

lemma oddCosetE_subset_latticeL : oddCosetE ⊆ latticeL := by
  rintro x ⟨m, n, rfl⟩
  refine ⟨m - n, 2 * n + 1, ?_⟩
  push_cast
  ring

lemma latticeL_eq_union : latticeL = latticeE ∪ oddCosetE := by
  ext x
  constructor
  · rintro ⟨m, n, rfl⟩
    rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · left
      refine ⟨m + k, k, ?_⟩
      push_cast
      ring
    · right
      refine ⟨m + k, k, ?_⟩
      push_cast
      ring
  · rintro (hx | hx)
    · exact latticeE_subset_latticeL hx
    · exact oddCosetE_subset_latticeL hx

lemma latticeE_countable : latticeE.Countable :=
  latticeL_countable.mono latticeE_subset_latticeL

lemma oddCosetE_countable : oddCosetE.Countable :=
  latticeL_countable.mono oddCosetE_subset_latticeL

private lemma half_sum_Psel_Qsel_odd_diff (j : ℕ) :
    Odd ((Psel (j + 1) + Qsel (j + 1)) / 2 - (Psel j + Qsel j) / 2) := by
  let R : ℕ → ℤ := fun m => (Psel m + Qsel m) / 2
  have hPQ_even : ∀ m, Even (Psel m + Qsel m) := fun m => by
    obtain ⟨u, hu⟩ := Classification.Psel_odd m
    obtain ⟨v, hv⟩ := Classification.Qsel_odd m
    exact ⟨u + v + 1, by linarith⟩
  have hR_mul : ∀ m, 2 * R m = Psel m + Qsel m := fun m => by
    dsimp [R]
    have hdiv := Int.ediv_mul_cancel (even_iff_two_dvd.mp (hPQ_even m))
    linarith
  have hR_rec : ∀ m, R (m + 2) = (4 * (m : ℤ) + 6) * R (m + 1) + R m := fun m => by
    have hP := Classification.Psel_rec m
    have hQ := Classification.Qsel_rec m
    have h0 := hR_mul m
    have h1 := hR_mul (m + 1)
    have h2 := hR_mul (m + 2)
    have htwo : 2 * R (m + 2) = 2 * ((4 * (m : ℤ) + 6) * R (m + 1) + R m) := by
      linear_combination h2 + hP + hQ - (4 * (m : ℤ) + 6) * h1 - h0
    linarith
  have hR_sum_odd : ∀ m, Odd (R (m + 1) + R m) := by
    intro m
    induction m with
    | zero =>
      have hR0 : R 0 = 1 := by simp [R]
      have hR1 : R 1 = 2 := by simp [R]
      rw [hR0, hR1]
      exact ⟨1, by norm_num⟩
    | succ m ih =>
      rw [hR_rec m]
      have he : Even ((4 * (m : ℤ) + 6) * R (m + 1)) :=
        ⟨(2 * (m : ℤ) + 3) * R (m + 1), by ring⟩
      have hid : (4 * (m : ℤ) + 6) * R (m + 1) + R m + R (m + 1) =
          (4 * (m : ℤ) + 6) * R (m + 1) + (R (m + 1) + R m) := by ring
      rw [hid]
      exact he.add_odd ih
  have hid : R (j + 1) - R j = (R (j + 1) + R j) - 2 * R j := by ring
  rw [show (Psel (j + 1) + Qsel (j + 1)) / 2 - (Psel j + Qsel j) / 2 = R (j + 1) - R j from rfl,
    hid]
  obtain ⟨t, ht⟩ := hR_sum_odd j
  exact ⟨t - R j, by linarith⟩

private lemma nearestInt_latticeL_eventually (m n : ℤ) :
    ∀ᶠ j : ℕ in atTop,
      nearestInt ((Qsel j : ℝ) * ((m : ℝ) + (n : ℝ) * (Real.exp 1 + 1) / 2)) =
        m * Qsel j + n * ((Psel j + Qsel j) / 2) := by
  let K : ℕ → ℤ := fun j => m * Qsel j + n * ((Psel j + Qsel j) / 2)
  have hKint : ∀ j : ℕ, (K j : ℝ) =
      (m : ℝ) * (Qsel j : ℝ) + (n : ℝ) * ((Psel j : ℝ) + (Qsel j : ℝ)) / 2 := fun j => by
    have hPQ : Even (Psel j + Qsel j) := by
      obtain ⟨u, hu⟩ := Classification.Psel_odd j
      obtain ⟨v, hv⟩ := Classification.Qsel_odd j
      exact ⟨u + v + 1, by linarith⟩
    have hdiv : ((Psel j + Qsel j) / 2 : ℤ) * 2 = Psel j + Qsel j :=
      Int.ediv_mul_cancel (even_iff_two_dvd.mp hPQ)
    have hhalf : (((Psel j + Qsel j) / 2 : ℤ) : ℝ) = ((Psel j : ℝ) + (Qsel j : ℝ)) / 2 := by
      have := congrArg (fun t : ℤ => (t : ℝ)) hdiv
      push_cast at this
      linarith
    simp only [K]
    push_cast
    rw [hhalf]
    ring
  have hdiff : ∀ j : ℕ, (Qsel j : ℝ) * ((m : ℝ) + (n : ℝ) * (Real.exp 1 + 1) / 2) - (K j : ℝ) =
      (n : ℝ) * deltaSel j / 2 := fun j => by
    rw [hKint j]
    simp only [deltaSel]
    ring
  have hδ0 : Tendsto (fun j : ℕ => (n : ℝ) * deltaSel j / 2) atTop (nhds 0) := by
    simpa using (deltaSel_tendsto_zero.const_mul (n : ℝ)).div_const 2
  have hsmall : ∀ᶠ j : ℕ in atTop, |(n : ℝ) * deltaSel j / 2| < 1 / 2 := by
    have hδ_abs : Tendsto (fun j : ℕ => |(n : ℝ) * deltaSel j / 2|) atTop (nhds 0) := by
      simpa using hδ0.abs
    exact hδ_abs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall] with j hj
  unfold nearestInt
  rw [round_eq_iff]
  have habs := abs_lt.mp hj
  have hd := hdiff j
  constructor <;> linarith

lemma not_parityFlip_of_mem_latticeE {x : ℝ} (hx : x ∈ latticeE) : ¬ parityFlip x := by
  rcases hx with ⟨m, n, rfl⟩
  have hx_eq : (m : ℝ) + (n : ℝ) * Real.exp 1 =
      ((m - n : ℤ) : ℝ) + ((2 * n : ℤ) : ℝ) * (Real.exp 1 + 1) / 2 := by
    push_cast; ring
  rw [hx_eq]
  have hev := nearestInt_latticeL_eventually (m - n) (2 * n)
  rw [parityFlip, Filter.not_frequently]
  filter_upwards [hev, (tendsto_add_atTop_nat 1).eventually hev] with j hj0 hj1
  rw [hj1, hj0]
  have hQdiff : Even (Qsel (j + 1) - Qsel j) := by
    obtain ⟨u, hu⟩ := Classification.Qsel_odd j
    obtain ⟨v, hv⟩ := Classification.Qsel_odd (j + 1)
    exact ⟨v - u, by linarith⟩
  obtain ⟨t, ht⟩ := hQdiff
  have hev_diff : Even (((m - n) * Qsel (j + 1) + 2 * n * ((Psel (j + 1) + Qsel (j + 1)) / 2)) -
      ((m - n) * Qsel j + 2 * n * ((Psel j + Qsel j) / 2))) := by
    refine ⟨(m - n) * t + n * ((Psel (j + 1) + Qsel (j + 1)) / 2 - (Psel j + Qsel j) / 2), ?_⟩
    linear_combination (m - n) * ht
  exact Int.not_odd_iff_even.mpr hev_diff

lemma parityFlip_of_mem_oddCosetE {x : ℝ} (hx : x ∈ oddCosetE) : parityFlip x := by
  rcases hx with ⟨m, n, rfl⟩
  have hx_eq : (Real.exp 1 + 1) / 2 + ((m : ℝ) + (n : ℝ) * Real.exp 1) =
      ((m - n : ℤ) : ℝ) + ((2 * n + 1 : ℤ) : ℝ) * (Real.exp 1 + 1) / 2 := by
    push_cast; ring
  rw [hx_eq]
  have hev := nearestInt_latticeL_eventually (m - n) (2 * n + 1)
  have hev2 := hev.and ((tendsto_add_atTop_nat 1).eventually hev)
  rw [parityFlip, frequently_atTop]
  intro N
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev2
  obtain ⟨hj0, hj1⟩ := hN₀ (max N N₀) (le_max_right N N₀)
  refine ⟨max N N₀, le_max_left N N₀, ?_⟩
  rw [hj1, hj0]
  have hQdiff : Even (Qsel (max N N₀ + 1) - Qsel (max N N₀)) := by
    obtain ⟨u, hu⟩ := Classification.Qsel_odd (max N N₀)
    obtain ⟨v, hv⟩ := Classification.Qsel_odd (max N N₀ + 1)
    exact ⟨v - u, by linarith⟩
  obtain ⟨t, ht⟩ := hQdiff
  obtain ⟨s, hs⟩ := half_sum_Psel_Qsel_odd_diff (max N N₀)
  refine ⟨(m - n) * t + n * (2 * s + 1) + s, ?_⟩
  linear_combination (m - n) * ht + (2 * n + 1) * hs

theorem disjoint_latticeE_oddCosetE : Disjoint latticeE oddCosetE :=
  Set.disjoint_left.mpr fun _ hxE hxO =>
    not_parityFlip_of_mem_latticeE hxE (parityFlip_of_mem_oddCosetE hxO)

lemma mem_latticeE_iff_mem_latticeL_and_not_parityFlip {x : ℝ} :
    x ∈ latticeE ↔ x ∈ latticeL ∧ ¬ parityFlip x := by
  constructor
  · intro hx
    exact ⟨latticeE_subset_latticeL hx, not_parityFlip_of_mem_latticeE hx⟩
  · rintro ⟨hxL, hnp⟩
    rw [latticeL_eq_union] at hxL
    rcases hxL with hxE | hxO
    · exact hxE
    · exact (hnp (parityFlip_of_mem_oddCosetE hxO)).elim

lemma parityFlip_of_apprExponent_eq_quarter {x : ℝ}
    (hx : apprExponent x = ENNReal.ofReal (1 / 4)) : parityFlip x := by
  have hfreq := FiniteStateGauge.frequently_defectShift_eq_level (x := x) (k := 1) le_rfl
    (by simpa using hx) 0
  have hodd : ∃ᶠ j : ℕ in atTop, Odd (defect x j) := by
    rw [frequently_atTop] at hfreq ⊢
    intro N
    obtain ⟨i, hi, hid⟩ := hfreq N
    refine ⟨i + 1, by omega, ?_⟩
    rw [GaugeNull.defectShift_eq_defect_succ, zero_add] at hid
    rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.mp hid with h1 | hm1
    · rw [h1]; exact odd_one
    · rw [hm1]; exact ⟨-1, by norm_num⟩
  have hodd2 : ∃ᶠ j : ℕ in atTop, 1 ≤ j ∧ Odd (defect x j) :=
    hodd.and_eventually (eventually_ge_atTop 1) |>.mono fun _ h => ⟨h.2, h.1⟩
  rw [parityFlip, frequently_atTop]
  intro N
  obtain ⟨j, hjN, hj1, hdef⟩ := hodd2.forall_exists_of_atTop (N + 1)
  have hpar : Odd (nearestInt ((Qsel (j + 1) : ℝ) * x) - nearestInt ((Qsel (j - 1) : ℝ) * x)) := by
    obtain ⟨s, hs⟩ := hdef
    have hdef_eq : defect x j = nearestInt ((Qsel (j + 1) : ℝ) * x) -
        (4 * (j : ℤ) + 2) * nearestInt ((Qsel j : ℝ) * x) -
        nearestInt ((Qsel (j - 1) : ℝ) * x) := rfl
    refine ⟨s + (2 * (j : ℤ) + 1) * nearestInt ((Qsel j : ℝ) * x), ?_⟩
    linarith
  have hsplit : nearestInt ((Qsel (j + 1) : ℝ) * x) - nearestInt ((Qsel (j - 1) : ℝ) * x) =
      (nearestInt ((Qsel (j + 1) : ℝ) * x) - nearestInt ((Qsel j : ℝ) * x)) +
      (nearestInt ((Qsel j : ℝ) * x) - nearestInt ((Qsel (j - 1) : ℝ) * x)) := by ring
  rw [hsplit] at hpar
  by_cases h1 : Odd (nearestInt ((Qsel (j + 1) : ℝ) * x) - nearestInt ((Qsel j : ℝ) * x))
  · exact ⟨j, by omega, h1⟩
  · have he1 : Even (nearestInt ((Qsel (j + 1) : ℝ) * x) - nearestInt ((Qsel j : ℝ) * x)) :=
      Int.not_odd_iff_even.mp h1
    by_cases h2 : Odd (nearestInt ((Qsel j : ℝ) * x) - nearestInt ((Qsel (j - 1) : ℝ) * x))
    · refine ⟨j - 1, by omega, ?_⟩
      rwa [show j - 1 + 1 = j by omega]
    · exfalso
      have he2 : Even (nearestInt ((Qsel j : ℝ) * x) - nearestInt ((Qsel (j - 1) : ℝ) * x)) :=
        Int.not_odd_iff_even.mp h2
      exact (Int.not_odd_iff_even.mpr (he1.add he2)) hpar

/-! ## Part 4: Residue-Class `limsup` Tools and Master Spectrum Theorems -/

private lemma limsup_mod3_eq_sup (f : ℕ → ℝ≥0∞) :
    limsup f atTop =
      max (limsup (fun j : ℕ => f (3 * j + 1)) atTop)
        (max (limsup (fun j : ℕ => f (3 * j + 2)) atTop)
          (limsup (fun j : ℕ => f (3 * j + 3)) atTop)) := by
  have hcomp_le : ∀ r : ℕ, limsup (fun j : ℕ => f (3 * j + r)) atTop ≤ limsup f atTop := by
    intro r
    refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
    have hev : ∀ᶠ n : ℕ in atTop, f n < b :=
      Filter.eventually_lt_of_limsup_lt hb (by isBoundedDefault)
    have ht : Tendsto (fun j : ℕ => 3 * j + r) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro M
      exact ⟨M, fun j hj => by omega⟩
    have hev' : ∀ᶠ j : ℕ in atTop, f (3 * j + r) ≤ b :=
      (ht.eventually hev).mono fun _ h => h.le
    exact Filter.limsup_le_of_le (by isBoundedDefault) hev'
  refine le_antisymm ?_ (max_le (hcomp_le 1) (max_le (hcomp_le 2) (hcomp_le 3)))
  refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
  have hb1 : limsup (fun j : ℕ => f (3 * j + 1)) atTop < b := (le_max_left _ _).trans_lt hb
  have hb2 : limsup (fun j : ℕ => f (3 * j + 2)) atTop < b :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hb
  have hb3 : limsup (fun j : ℕ => f (3 * j + 3)) atTop < b :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hb
  obtain ⟨J1, hJ1⟩ := eventually_atTop.mp
    (Filter.eventually_lt_of_limsup_lt hb1 (by isBoundedDefault))
  obtain ⟨J2, hJ2⟩ := eventually_atTop.mp
    (Filter.eventually_lt_of_limsup_lt hb2 (by isBoundedDefault))
  obtain ⟨J3, hJ3⟩ := eventually_atTop.mp
    (Filter.eventually_lt_of_limsup_lt hb3 (by isBoundedDefault))
  refine Filter.limsup_le_of_le (by isBoundedDefault) (eventually_atTop.mpr ?_)
  refine ⟨3 * max J1 (max J2 J3) + 1, fun n hn => ?_⟩
  have hmod : (n - 1) % 3 = 0 ∨ (n - 1) % 3 = 1 ∨ (n - 1) % 3 = 2 := by omega
  rcases hmod with h | h | h
  · have hlt := hJ1 ((n - 1) / 3) (by omega)
    rw [show 3 * ((n - 1) / 3) + 1 = n by omega] at hlt
    exact hlt.le
  · have hlt := hJ2 ((n - 1) / 3) (by omega)
    rw [show 3 * ((n - 1) / 3) + 2 = n by omega] at hlt
    exact hlt.le
  · have hlt := hJ3 ((n - 1) / 3) (by omega)
    rw [show 3 * ((n - 1) / 3) + 3 = n by omega] at hlt
    exact hlt.le

private lemma limsup_ofReal_mul_tendsto {u a : ℕ → ℝ} {c : ℝ}
    (hu : ∀ᶠ n : ℕ in atTop, 0 ≤ u n) (ha : Tendsto a atTop (nhds c)) (hc : 0 < c) :
    limsup (fun n : ℕ => ENNReal.ofReal (a n * u n)) atTop =
      ENNReal.ofReal c * limsup (fun n : ℕ => ENNReal.ofReal (u n)) atTop := by
  have h_lower : ∀ {b v : ℕ → ℝ} {d : ℝ}, (∀ᶠ n in atTop, 0 ≤ v n) →
      Tendsto b atTop (nhds d) → 0 < d →
      ENNReal.ofReal d * limsup (fun n => ENNReal.ofReal (v n)) atTop ≤
        limsup (fun n => ENNReal.ofReal (b n * v n)) atTop := by
    intro b v d hv hb hd
    set L := limsup (fun n => ENNReal.ofReal (v n)) atTop
    set M := limsup (fun n => ENNReal.ofReal (b n * v n)) atTop
    have ht_le : ∀ t : ℝ, 0 < t → t < d → ENNReal.ofReal t * L ≤ M := by
      intro t ht htd
      have hev_t : ∀ᶠ n in atTop, t ≤ b n := hb.eventually (le_mem_nhds htd)
      have hM_ge : limsup (fun n => ENNReal.ofReal t * ENNReal.ofReal (v n)) atTop ≤ M := by
        refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
        filter_upwards [hev_t, hv] with n hbn hvn
        rw [← ENNReal.ofReal_mul ht.le]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hbn hvn)
      refine le_trans ?_ hM_ge
      refine le_of_not_gt fun hlt => ?_
      obtain ⟨y, hy1, hy2⟩ := exists_between hlt
      have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
      have htT : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
      have hyL : y / ENNReal.ofReal t < L :=
        (ENNReal.div_lt_iff (Or.inl ht0) (Or.inl htT)).mpr (by simpa [mul_comm] using hy2)
      have hfreq := Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hyL
      have hfreq2 : ∃ᶠ n in atTop, y ≤ ENNReal.ofReal t * ENNReal.ofReal (v n) := by
        refine hfreq.mono fun n hn => ?_
        have hlt' : y < ENNReal.ofReal t * ENNReal.ofReal (v n) := by
          have := (ENNReal.div_lt_iff (Or.inl ht0) (Or.inl htT)).mp hn
          simpa [mul_comm] using this
        exact hlt'.le
      exact not_lt_of_ge (Filter.le_limsup_of_frequently_le hfreq2 (by isBoundedDefault)) hy1
    by_cases hL : L = ⊤
    · have hhalf := ht_le (d / 2) (half_pos hd) (half_lt_self hd)
      rw [hL, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (half_pos hd)).ne'] at hhalf
      rw [hL, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hd).ne']
      exact hhalf
    · let tSeq : ℕ → ℝ := fun n => d * (1 - 1 / ((n : ℝ) + 2))
      have ht_tend : Tendsto (fun n => ENNReal.ofReal (tSeq n) * L) atTop
          (nhds (ENNReal.ofReal d * L)) := by
        have htR : Tendsto tSeq atTop (nhds d) := by
          have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (nhds 0) :=
            (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr
              (fun n => by dsimp only [Function.comp_def]; push_cast; ring)
          have h1 : Tendsto (fun n : ℕ => d * (1 - 1 / ((n : ℝ) + 2))) atTop
              (nhds (d * (1 - 0))) := tendsto_const_nhds.mul (tendsto_const_nhds.sub hinv)
          simpa [tSeq] using h1
        exact ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal htR) (Or.inr hL)
      refine le_of_tendsto ht_tend (Eventually.of_forall fun n => ?_)
      have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hpos1 : 0 < 1 - 1 / ((n : ℝ) + 2) := by
        have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
        linarith
      have hlt1 : 1 - 1 / ((n : ℝ) + 2) < 1 := by
        have : 0 < 1 / ((n : ℝ) + 2) := by positivity
        linarith
      exact ht_le (tSeq n) (mul_pos hd hpos1) (by nlinarith)
  have h1 := h_lower hu ha hc
  have ha_pos : ∀ᶠ n in atTop, 0 < a n := ha.eventually (lt_mem_nhds hc)
  have huv : ∀ᶠ n in atTop, 0 ≤ a n * u n := by
    filter_upwards [ha_pos, hu] with n han hun
    exact mul_nonneg han.le hun
  have ha_inv : Tendsto (fun n => (a n)⁻¹) atTop (nhds c⁻¹) := ha.inv₀ hc.ne'
  have h2 := h_lower huv ha_inv (inv_pos.mpr hc)
  have hcongr : limsup (fun n => ENNReal.ofReal ((a n)⁻¹ * (a n * u n))) atTop =
      limsup (fun n => ENNReal.ofReal (u n)) atTop := by
    refine Filter.limsup_congr ?_
    filter_upwards [ha_pos] with n han
    rw [← mul_assoc, inv_mul_cancel₀ han.ne', one_mul]
  rw [hcongr] at h2
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hcT : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmul : limsup (fun n => ENNReal.ofReal (a n * u n)) atTop ≤
      ENNReal.ofReal c * limsup (fun n => ENNReal.ofReal (u n)) atTop := by
    calc limsup (fun n => ENNReal.ofReal (a n * u n)) atTop
        = ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ *
            limsup (fun n => ENNReal.ofReal (a n * u n)) atTop) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
            one_mul]
      _ ≤ ENNReal.ofReal c * limsup (fun n => ENNReal.ofReal (u n)) atTop :=
          mul_le_mul_of_nonneg_left h2 bot_le
  exact le_antisymm hmul h1

private lemma ofReal_half : ENNReal.ofReal (1 / 2) = (1 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

private lemma ofReal_quarter : ENNReal.ofReal (1 / 4) = (1 / 4 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

private lemma two_mul_half_ennreal : (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 := by
  rw [← ofReal_half, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.ofReal_one]

private lemma two_mul_quarter_ennreal : (2 : ℝ≥0∞) * (1 / 4 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by
  rw [← ofReal_quarter, ← ofReal_half, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
    show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num]

private lemma two_mul_ofReal_quarter : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 4) = (1 / 2 : ℝ≥0∞) := by
  rw [ofReal_quarter, two_mul_quarter_ennreal]

private lemma distToNearestInt_int_add_eq {m : ℤ} {δ : ℝ} (hδ : |δ| < 1 / 2) :
    distToNearestInt ((m : ℝ) + δ) = |δ| := by
  have hr : round ((m : ℝ) + δ) = m := by
    rw [round_eq_iff]
    have h := abs_lt.mp hδ
    constructor <;> linarith
  unfold distToNearestInt
  rw [hr]
  ring_nf

private lemma half_sub_abs_le_distToNearestInt_int_add_half {m : ℤ} {δ : ℝ} (hδ : |δ| ≤ 1 / 2) :
    1 / 2 - |δ| ≤ distToNearestInt ((m : ℝ) + 1 / 2 + δ) := by
  have h1 : ∀ z : ℤ, 1 / 2 - |δ| ≤ |(m : ℝ) + 1 / 2 + δ - (z : ℝ)| := by
    intro z
    have hδb := abs_le.mp hδ
    by_cases hz : z ≤ m
    · have hzR : (z : ℝ) ≤ (m : ℝ) := by exact_mod_cast hz
      have hnn : 0 ≤ (m : ℝ) + 1 / 2 + δ - (z : ℝ) := by linarith
      rw [abs_of_nonneg hnn]
      linarith [neg_le_abs δ]
    · have hz1 : m + 1 ≤ z := by omega
      have hz1R : (m : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hz1
      have hnp : (m : ℝ) + 1 / 2 + δ - (z : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonpos hnp]
      linarith [le_abs_self δ]
  exact h1 _

private lemma fullKLSeq_mod1_limsup (x : ℝ) :
    limsup (fun j : ℕ => ENNReal.ofReal (fullKLSeq x (3 * j + 1))) atTop =
      2 * apprExponent x := by
  have heq : ∀ j : ℕ, fullKLSeq x (3 * j + 1) =
      (fullKLWeight (3 * j + 1) / (2 * ((j + 1 : ℕ) : ℝ))) *
        (2 * apprSeq x (j + 1)) := fun j => by
    have hjpos : (2 * ((j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    simp only [fullKLSeq, apprSeq, qFull_three_mul_add_one]
    field_simp
  simp_rw [heq]
  rw [limsup_ofReal_mul_tendsto
    (Eventually.of_forall fun j => mul_nonneg (by norm_num) (apprSeq_nonneg x (j + 1)))
    tendsto_fullKLWeight_mod1_div one_pos]
  rw [ENNReal.ofReal_one, one_mul]
  have hshift : limsup (fun j : ℕ => ENNReal.ofReal (2 * apprSeq x (j + 1))) atTop =
      limsup (fun j : ℕ => ENNReal.ofReal (2 * apprSeq x j)) atTop := by
    simpa [Nat.add_comm] using
      (Filter.limsup_nat_add (fun j : ℕ => ENNReal.ofReal (2 * apprSeq x j)) 1)
  rw [hshift]
  have h2 := limsup_ofReal_mul_tendsto (Eventually.of_forall fun j => apprSeq_nonneg x j)
    (tendsto_const_nhds (x := (2 : ℝ))) (by norm_num)
  rw [h2]
  unfold apprExponent
  rw [ENNReal.ofReal_ofNat]
  rfl

private lemma fullRawSeq_mod1_limsup (x : ℝ) :
    limsup (fun j : ℕ => ENNReal.ofReal (fullRawSeq x (3 * j + 1))) atTop =
      2 * apprExponent x := by
  have heq : ∀ j : ℕ, fullRawSeq x (3 * j + 1) = 2 * apprSeq x (j + 1) := fun j => by
    have hd : eulerCFDigit (3 * j + 2) = 2 * ((j + 1 : ℕ) : ℤ) :=
      eulerCFDigit_three_mul_add_two j
    simp only [fullRawSeq, apprSeq, qFull_three_mul_add_one, show 3 * j + 1 + 1 = 3 * j + 2 by ring,
      hd]
    push_cast
    ring
  simp_rw [heq]
  have hshift : limsup (fun j : ℕ => ENNReal.ofReal (2 * apprSeq x (j + 1))) atTop =
      limsup (fun j : ℕ => ENNReal.ofReal (2 * apprSeq x j)) atTop := by
    simpa [Nat.add_comm] using
      (Filter.limsup_nat_add (fun j : ℕ => ENNReal.ofReal (2 * apprSeq x j)) 1)
  rw [hshift, limsup_ofReal_mul_tendsto (Eventually.of_forall fun j => apprSeq_nonneg x j)
    (tendsto_const_nhds (x := (2 : ℝ))) (by norm_num)]
  unfold apprExponent
  rw [ENNReal.ofReal_ofNat]
  rfl

private lemma odd_diff_iff_add (a b : ℤ) : Odd (b - a) ↔ Odd (b + a) := by
  have h : b + a = (b - a) + 2 * a := by ring
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k + a, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k - a, by linarith⟩

private lemma parityFlip_succ_iff (x : ℝ) :
    parityFlip x ↔
      ∃ᶠ j : ℕ in atTop,
        Odd (nearestInt ((Qsel (j + 2) : ℝ) * x) - nearestInt ((Qsel (j + 1) : ℝ) * x)) := by
  unfold parityFlip
  constructor
  · intro h
    rw [frequently_atTop] at h ⊢
    intro N
    obtain ⟨j, hj, ho⟩ := h (N + 1)
    refine ⟨j - 1, by omega, ?_⟩
    rwa [show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega]
  · intro h
    rw [frequently_atTop] at h ⊢
    intro N
    obtain ⟨j, hj, ho⟩ := h N
    exact ⟨j + 1, by omega, ho⟩

private lemma dist_mod2_mod0_of_eps_tendsto_zero {x : ℝ}
    (hε : Tendsto (eps x) atTop (nhds 0)) :
    (¬ parityFlip x →
      Tendsto (fun j : ℕ => distToNearestInt ((qFull (3 * j + 2) : ℝ) * x)) atTop (nhds 0) ∧
      Tendsto (fun j : ℕ => distToNearestInt ((qFull (3 * j + 3) : ℝ) * x)) atTop (nhds 0)) ∧
    (parityFlip x →
      limsup (fun j : ℕ => ENNReal.ofReal (distToNearestInt ((qFull (3 * j + 2) : ℝ) * x)))
        atTop = (1 / 2 : ℝ≥0∞) ∧
      limsup (fun j : ℕ => ENNReal.ofReal (distToNearestInt ((qFull (3 * j + 3) : ℝ) * x)))
        atTop = (1 / 2 : ℝ≥0∞)) := by
  let M : ℕ → ℤ := fun j => nearestInt ((Qsel j : ℝ) * x)
  have hδm : Tendsto (fun j : ℕ => (eps x (j + 2) - eps x (j + 1)) / 2) atTop (nhds 0) := by
    have h1 := hε.comp (tendsto_add_atTop_nat 2)
    have h2 := hε.comp (tendsto_add_atTop_nat 1)
    simpa using (h1.sub h2).div_const 2
  have hδp : Tendsto (fun j : ℕ => (eps x (j + 2) + eps x (j + 1)) / 2) atTop (nhds 0) := by
    have h1 := hε.comp (tendsto_add_atTop_nat 2)
    have h2 := hε.comp (tendsto_add_atTop_nat 1)
    simpa using (h1.add h2).div_const 2
  have hδm_abs : Tendsto (fun j : ℕ => |(eps x (j + 2) - eps x (j + 1)) / 2|) atTop (nhds 0) := by
    simpa using hδm.abs
  have hδp_abs : Tendsto (fun j : ℕ => |(eps x (j + 2) + eps x (j + 1)) / 2|) atTop (nhds 0) := by
    simpa using hδp.abs
  have hsm_m : ∀ᶠ j : ℕ in atTop, |(eps x (j + 2) - eps x (j + 1)) / 2| < 1 / 2 :=
    hδm_abs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hsm_p : ∀ᶠ j : ℕ in atTop, |(eps x (j + 2) + eps x (j + 1)) / 2| < 1 / 2 :=
    hδp_abs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hq2 : ∀ j : ℕ, (qFull (3 * j + 2) : ℝ) * x =
      ((M (j + 2) - M (j + 1) : ℤ) : ℝ) / 2 + (eps x (j + 2) - eps x (j + 1)) / 2 := fun j => by
    have hq : (qFull (3 * j + 2) : ℝ) = ((Qsel (j + 2) : ℝ) - (Qsel (j + 1) : ℝ)) / 2 := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) (two_mul_qFull_three_mul_add_two j)
      push_cast at h
      linarith
    rw [hq]
    simp only [M, eps, nearestInt]
    push_cast
    ring
  have hq3 : ∀ j : ℕ, (qFull (3 * j + 3) : ℝ) * x =
      ((M (j + 2) + M (j + 1) : ℤ) : ℝ) / 2 + (eps x (j + 2) + eps x (j + 1)) / 2 := fun j => by
    have h3 : 3 * j + 3 = 3 * (j + 1) := by ring
    have hq : (qFull (3 * j + 3) : ℝ) = ((Qsel (j + 2) : ℝ) + (Qsel (j + 1) : ℝ)) / 2 := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) (two_mul_qFull_three_mul (j + 1))
      push_cast at h
      rw [← h3] at h
      linarith
    rw [hq]
    simp only [M, eps, nearestInt]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · intro hnp
    rw [parityFlip_succ_iff, Filter.not_frequently] at hnp
    have hm_eq : ∀ᶠ j : ℕ in atTop,
        distToNearestInt ((qFull (3 * j + 2) : ℝ) * x) =
          |(eps x (j + 2) - eps x (j + 1)) / 2| := by
      filter_upwards [hnp, hsm_m] with j hj_even hj_sm
      obtain ⟨k, hk⟩ := Int.not_odd_iff_even.mp hj_even
      rw [hq2 j]
      have hcast : ((M (j + 2) - M (j + 1) : ℤ) : ℝ) / 2 = (k : ℝ) := by
        have : M (j + 2) - M (j + 1) = 2 * k := by linarith
        rw [this]
        push_cast
        ring
      rw [hcast]
      exact distToNearestInt_int_add_eq hj_sm
    have hp_eq : ∀ᶠ j : ℕ in atTop,
        distToNearestInt ((qFull (3 * j + 3) : ℝ) * x) =
          |(eps x (j + 2) + eps x (j + 1)) / 2| := by
      filter_upwards [hnp, hsm_p] with j hj_even hj_sm
      have h_even_add : Even (M (j + 2) + M (j + 1)) :=
        Int.not_odd_iff_even.mp fun ho =>
          hj_even ((odd_diff_iff_add (M (j + 1)) (M (j + 2))).mpr ho)
      obtain ⟨k, hk⟩ := h_even_add
      rw [hq3 j]
      have hcast : ((M (j + 2) + M (j + 1) : ℤ) : ℝ) / 2 = (k : ℝ) := by
        have : M (j + 2) + M (j + 1) = 2 * k := by linarith
        rw [this]
        push_cast
        ring
      rw [hcast]
      exact distToNearestInt_int_add_eq hj_sm
    exact ⟨hδm_abs.congr' (hm_eq.mono fun _ h => h.symm),
      hδp_abs.congr' (hp_eq.mono fun _ h => h.symm)⟩
  · intro hp
    rw [parityFlip_succ_iff] at hp
    have h_upper : ∀ seq : ℕ → ℝ,
        limsup (fun j : ℕ => ENNReal.ofReal (distToNearestInt (seq j))) atTop ≤
          (1 / 2 : ℝ≥0∞) := fun seq => by
      refine Filter.limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun j => ?_)
      rw [← ofReal_half]
      exact ENNReal.ofReal_le_ofReal (distToNearestInt_le_half _)
    have hm_ge : ∀ δ : ℝ, 0 < δ → ∃ᶠ j : ℕ in atTop,
        1 / 2 - δ ≤ distToNearestInt ((qFull (3 * j + 2) : ℝ) * x) := by
      intro δ hδ_pos
      have hev_d := hδm_abs.eventually (Iio_mem_nhds hδ_pos)
      refine ((hp.and_eventually hsm_m).and_eventually hev_d).mono ?_
      rintro j ⟨⟨ho, hsm⟩, hd⟩
      obtain ⟨k, hk⟩ := ho
      rw [hq2 j]
      have hcast : ((M (j + 2) - M (j + 1) : ℤ) : ℝ) / 2 = (k : ℝ) + 1 / 2 := by
        rw [hk]; push_cast; ring
      rw [hcast]
      have h1 := half_sub_abs_le_distToNearestInt_int_add_half (m := k) hsm.le
      linarith
    have hp_ge : ∀ δ : ℝ, 0 < δ → ∃ᶠ j : ℕ in atTop,
        1 / 2 - δ ≤ distToNearestInt ((qFull (3 * j + 3) : ℝ) * x) := by
      intro δ hδ_pos
      have hev_d := hδp_abs.eventually (Iio_mem_nhds hδ_pos)
      refine ((hp.and_eventually hsm_p).and_eventually hev_d).mono ?_
      rintro j ⟨⟨ho, hsm⟩, hd⟩
      obtain ⟨k, hk⟩ := (odd_diff_iff_add (M (j + 1)) (M (j + 2))).mp ho
      rw [hq3 j]
      have hcast : ((M (j + 2) + M (j + 1) : ℤ) : ℝ) / 2 = (k : ℝ) + 1 / 2 := by
        rw [hk]; push_cast; ring
      rw [hcast]
      have h1 := half_sub_abs_le_distToNearestInt_int_add_half (m := k) hsm.le
      linarith
    have h_lower_lim : ∀ f : ℕ → ℝ,
        (∀ δ : ℝ, 0 < δ → ∃ᶠ j : ℕ in atTop, 1 / 2 - δ ≤ f j) →
        (1 / 2 : ℝ≥0∞) ≤ limsup (fun j => ENNReal.ofReal (f j)) atTop := by
      intro f hf
      have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / 2 - 1 / ((n : ℝ) + 3))) atTop
          (nhds (1 / 2 : ℝ≥0∞)) := by
        have htR : Tendsto (fun n : ℕ => (1 / 2 : ℝ) - 1 / ((n : ℝ) + 3)) atTop (nhds (1 / 2)) := by
          have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 3)) atTop (nhds 0) :=
            (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)).congr
              (fun n => by dsimp only [Function.comp_def]; push_cast; ring)
          simpa using tendsto_const_nhds.sub hinv
        rw [← ofReal_half]
        exact ENNReal.tendsto_ofReal htR
      refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 3) := by positivity
      have hfreq := (hf _ hpos).mono fun j hj => ENNReal.ofReal_le_ofReal hj
      exact Filter.le_limsup_of_frequently_le hfreq (by isBoundedDefault)
    exact ⟨le_antisymm (h_upper _) (h_lower_lim _ hm_ge),
      le_antisymm (h_upper _) (h_lower_lim _ hp_ge)⟩

/-- **Master Formula for the Full-Convergent Kraaikamp–Liardet Spectrum `fullKLSpectrum`**:
- If `apprExponent x = ⊤`, then `fullKLSpectrum x = ⊤`.
- If `apprExponent x ≠ ⊤`, then
  `fullKLSpectrum x = max (2 * apprExponent x) (if parityFlip x then 1 else 0)`. -/
theorem fullKLSpectrum_eq (x : ℝ) :
    (apprExponent x = ⊤ → fullKLSpectrum x = ⊤) ∧
    (apprExponent x ≠ ⊤ →
      fullKLSpectrum x = max (2 * apprExponent x) (if parityFlip x then 1 else 0)) := by
  have hmod : fullKLSpectrum x =
      max (2 * apprExponent x)
        (max (limsup (fun j : ℕ => ENNReal.ofReal (fullKLSeq x (3 * j + 2))) atTop)
          (limsup (fun j : ℕ => ENNReal.ofReal (fullKLSeq x (3 * j + 3))) atTop)) := by
    unfold fullKLSpectrum
    rw [limsup_mod3_eq_sup, fullKLSeq_mod1_limsup]
  refine ⟨?_, ?_⟩
  · intro htop
    rw [hmod, htop, ENNReal.mul_top (by norm_num)]
    simp
  · intro hfin
    have hε := FullSpectrumDiscrete.eps_tendsto_zero_of_apprExponent_ne_top x hfin
    have hdist := dist_mod2_mod0_of_eps_tendsto_zero hε
    have hm2 : limsup (fun j : ℕ => ENNReal.ofReal (fullKLSeq x (3 * j + 2))) atTop =
        2 * limsup (fun j : ℕ =>
          ENNReal.ofReal (distToNearestInt ((qFull (3 * j + 2) : ℝ) * x))) atTop := by
      have h := limsup_ofReal_mul_tendsto
        (u := fun j => distToNearestInt ((qFull (3 * j + 2) : ℝ) * x))
        (Eventually.of_forall fun j => distToNearestInt_nonneg _)
        tendsto_fullKLWeight_mod2 (by norm_num : (0 : ℝ) < 2)
      simpa [fullKLSeq] using h
    have hm3 : limsup (fun j : ℕ => ENNReal.ofReal (fullKLSeq x (3 * j + 3))) atTop =
        2 * limsup (fun j : ℕ =>
          ENNReal.ofReal (distToNearestInt ((qFull (3 * j + 3) : ℝ) * x))) atTop := by
      have h := limsup_ofReal_mul_tendsto
        (u := fun j => distToNearestInt ((qFull (3 * j + 3) : ℝ) * x))
        (Eventually.of_forall fun j => distToNearestInt_nonneg _)
        tendsto_fullKLWeight_mod0 (by norm_num : (0 : ℝ) < 2)
      simpa [fullKLSeq] using h
    by_cases hp : parityFlip x
    · obtain ⟨h2, h3⟩ := hdist.2 hp
      rw [hmod, hm2, hm3, h2, h3]
      simp only [hp, ↓reduceIte]
      rw [two_mul_half_ennreal, max_self]
    · obtain ⟨h2, h3⟩ := hdist.1 hp
      have hz2 : limsup (fun j : ℕ =>
          ENNReal.ofReal (distToNearestInt ((qFull (3 * j + 2) : ℝ) * x))) atTop = 0 := by
        simpa using (ENNReal.tendsto_ofReal h2).limsup_eq
      have hz3 : limsup (fun j : ℕ =>
          ENNReal.ofReal (distToNearestInt ((qFull (3 * j + 3) : ℝ) * x))) atTop = 0 := by
        simpa using (ENNReal.tendsto_ofReal h3).limsup_eq
      rw [hmod, hm2, hm3, hz2, hz3]
      simp [hp]

/-- **Master Formula for the Raw Partial-Quotient Full Spectrum `fullRawSpectrum`**:
- If `apprExponent x = ⊤`, then `fullRawSpectrum x = ⊤`.
- If `apprExponent x ≠ ⊤`, then
  `fullRawSpectrum x = max (2 * apprExponent x) (if parityFlip x then 1 / 2 else 0)`. -/
theorem fullRawSpectrum_eq (x : ℝ) :
    (apprExponent x = ⊤ → fullRawSpectrum x = ⊤) ∧
    (apprExponent x ≠ ⊤ →
      fullRawSpectrum x =
        max (2 * apprExponent x) (if parityFlip x then (1 / 2 : ℝ≥0∞) else 0)) := by
  have hmod : fullRawSpectrum x =
      max (2 * apprExponent x)
        (max (limsup (fun j : ℕ => ENNReal.ofReal (fullRawSeq x (3 * j + 2))) atTop)
          (limsup (fun j : ℕ => ENNReal.ofReal (fullRawSeq x (3 * j + 3))) atTop)) := by
    unfold fullRawSpectrum
    rw [limsup_mod3_eq_sup, fullRawSeq_mod1_limsup]
  have hd2 : ∀ j : ℕ, fullRawSeq x (3 * j + 2) =
      distToNearestInt ((qFull (3 * j + 2) : ℝ) * x) := fun j => by
    simp [fullRawSeq, show 3 * j + 2 + 1 = 3 * j + 3 by ring,
      eulerCFDigit_three_mul_add_three]
  have hd3 : ∀ j : ℕ, fullRawSeq x (3 * j + 3) =
      distToNearestInt ((qFull (3 * j + 3) : ℝ) * x) := fun j => by
    simp [fullRawSeq, show 3 * j + 3 + 1 = 3 * (j + 1) + 1 by ring,
      eulerCFDigit_three_mul_add_one]
  refine ⟨?_, ?_⟩
  · intro htop
    rw [hmod, htop, ENNReal.mul_top (by norm_num)]
    simp
  · intro hfin
    have hε := FullSpectrumDiscrete.eps_tendsto_zero_of_apprExponent_ne_top x hfin
    have hdist := dist_mod2_mod0_of_eps_tendsto_zero hε
    simp_rw [hd2, hd3] at hmod
    by_cases hp : parityFlip x
    · obtain ⟨h2, h3⟩ := hdist.2 hp
      rw [hmod, h2, h3]
      simp [hp]
    · obtain ⟨h2, h3⟩ := hdist.1 hp
      have hz2 : limsup (fun j : ℕ =>
          ENNReal.ofReal (distToNearestInt ((qFull (3 * j + 2) : ℝ) * x))) atTop = 0 := by
        simpa using (ENNReal.tendsto_ofReal h2).limsup_eq
      have hz3 : limsup (fun j : ℕ =>
          ENNReal.ofReal (distToNearestInt ((qFull (3 * j + 3) : ℝ) * x))) atTop = 0 := by
        simpa using (ENNReal.tendsto_ofReal h3).limsup_eq
      rw [hmod, hz2, hz3]
      simp [hp]

/-! ## Part 5: Zero-Level Rigidity, Spectral Gaps, Spectrum Range, and Level-Set Geometry -/

/-- **Zero-Level Kraaikamp–Liardet Rigidity (`TFAE`)**:
Along the full convergents of `e`, the enlarged selected lattice `L = ℤ + ℤ(e+1)/2` collapses
back to the unimodular lattice `ℤ + ℤe`:
`fullKLSpectrum x = 0 ↔ fullKLSpectrum x < 1 ↔ fullRawSpectrum x = 0 ↔`
`fullRawSpectrum x < 1/2 ↔ x ∈ ℤ + ℤe`. -/
theorem fullKLSpectrum_zero_tfae (x : ℝ) :
    [ fullKLSpectrum x = 0,
      fullKLSpectrum x < 1,
      fullRawSpectrum x = 0,
      fullRawSpectrum x < (1 / 2 : ℝ≥0∞),
      x ∈ latticeE ].TFAE := by
  have h12 : fullKLSpectrum x = 0 → fullKLSpectrum x < 1 := fun h => by
    rw [h]; exact zero_lt_one
  have h25 : fullKLSpectrum x < 1 → x ∈ latticeE := by
    intro hlt
    have hfin : apprExponent x ≠ ⊤ := fun htop => by
      rw [(fullKLSpectrum_eq x).1 htop] at hlt
      exact (not_lt_of_ge le_top) hlt
    rw [(fullKLSpectrum_eq x).2 hfin] at hlt
    have h2lam : 2 * apprExponent x < 1 := (le_max_left _ _).trans_lt hlt
    have hlam : apprExponent x < ENNReal.ofReal (1 / 4) ∨
        apprExponent x = ENNReal.ofReal (1 / 4) := by
      rw [ofReal_quarter]
      by_cases hq : apprExponent x < (1 / 4 : ℝ≥0∞)
      · exact Or.inl hq
      · push Not at hq
        have hlt_half : apprExponent x < (1 / 2 : ℝ≥0∞) := by
          by_contra hge
          push Not at hge
          have hle := mul_le_mul_of_nonneg_left hge (bot_le : (0 : ℝ≥0∞) ≤ 2)
          rw [two_mul_half_ennreal] at hle
          exact not_le_of_gt h2lam hle
        by_contra hne
        rw [not_or] at hne
        have hgt : (1 / 4 : ℝ≥0∞) < apprExponent x := lt_of_le_of_ne hq (Ne.symm hne.2)
        have hgap := FullSpectrumDiscrete.spectral_gap_open_interval 1
          (L := (apprExponent x).toReal) ?_ ?_ x
        · apply hgap
          rw [ENNReal.ofReal_toReal hfin]
        · have h14_real : (1 / 4 : ℝ) = ((1 : ℕ) : ℝ) / 4 := by norm_num
          rw [← h14_real]
          have h14' : ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ℝ≥0∞) := ofReal_quarter
          have := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfin).mpr (h14'.symm ▸ hgt)
          simpa using this
        · have h12' : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := ofReal_half
          have hltR :=
            (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr (h12'.symm ▸ hlt_half)
          rw [ENNReal.toReal_ofReal (by norm_num)] at hltR
          norm_num
          linarith
    rcases hlam with hlt_q | heq_q
    · have hxL : x ∈ latticeL := by
        rcases SpectralGap.spectral_gap x with h0 | hge
        · exact (Classification.theorem2_classification x).mp ((apprExponent_eq_zero_iff x).mp h0)
        · exact (not_lt_of_ge hge (ofReal_quarter ▸ hlt_q)).elim
      have hnp : ¬ parityFlip x := fun hp => by
        simp only [hp, ↓reduceIte] at hlt
        exact (not_lt_of_ge (le_max_right _ _) hlt)
      exact mem_latticeE_iff_mem_latticeL_and_not_parityFlip.mpr ⟨hxL, hnp⟩
    · have hp : parityFlip x := parityFlip_of_apprExponent_eq_quarter heq_q
      simp only [hp, ↓reduceIte] at hlt
      exact ((not_lt_of_ge (le_max_right _ _) hlt)).elim
  have h53 : x ∈ latticeE → fullRawSpectrum x = 0 := by
    intro hx
    have hxL := latticeE_subset_latticeL hx
    have h0 : apprExponent x = 0 := (apprExponent_eq_zero_iff x).mpr
      ((Classification.theorem2_classification x).mpr hxL)
    have hnp := not_parityFlip_of_mem_latticeE hx
    rw [(fullRawSpectrum_eq x).2 (by rw [h0]; simp), h0]
    simp [hnp]
  have h34 : fullRawSpectrum x = 0 → fullRawSpectrum x < (1 / 2 : ℝ≥0∞) := fun h => by
    rw [h, ← ofReal_half, ← ENNReal.ofReal_zero]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have h45 : fullRawSpectrum x < (1 / 2 : ℝ≥0∞) → x ∈ latticeE := by
    intro hlt
    have hfin : apprExponent x ≠ ⊤ := fun htop => by
      rw [(fullRawSpectrum_eq x).1 htop] at hlt
      exact (not_lt_of_ge le_top) hlt
    rw [(fullRawSpectrum_eq x).2 hfin] at hlt
    have h2lam : 2 * apprExponent x < (1 / 2 : ℝ≥0∞) := (le_max_left _ _).trans_lt hlt
    have hlam : apprExponent x < (1 / 4 : ℝ≥0∞) := by
      by_contra hge
      push Not at hge
      have hle := mul_le_mul_of_nonneg_left hge (bot_le : (0 : ℝ≥0∞) ≤ 2)
      rw [two_mul_quarter_ennreal] at hle
      exact not_le_of_gt h2lam hle
    have hxL : x ∈ latticeL := by
      rcases SpectralGap.spectral_gap x with h0 | hge
      · exact (Classification.theorem2_classification x).mp ((apprExponent_eq_zero_iff x).mp h0)
      · exact (not_lt_of_ge hge hlam).elim
    have hnp : ¬ parityFlip x := fun hp => by
      simp only [hp, ↓reduceIte] at hlt
      exact not_lt_of_ge (le_max_right _ _) hlt
    exact mem_latticeE_iff_mem_latticeL_and_not_parityFlip.mpr ⟨hxL, hnp⟩
  have h51 : x ∈ latticeE → fullKLSpectrum x = 0 := by
    intro hx
    have hxL := latticeE_subset_latticeL hx
    have h0 : apprExponent x = 0 := (apprExponent_eq_zero_iff x).mpr
      ((Classification.theorem2_classification x).mpr hxL)
    have hnp := not_parityFlip_of_mem_latticeE hx
    rw [(fullKLSpectrum_eq x).2 (by rw [h0]; simp), h0]
    simp [hnp]
  tfae_have 1 → 2 := h12
  tfae_have 2 → 5 := h25
  tfae_have 5 → 3 := h53
  tfae_have 3 → 4 := h34
  tfae_have 4 → 5 := h45
  tfae_have 5 → 1 := h51
  tfae_finish

/-- **Giant First Spectral Gap `(0, 1)`**: NO `x ∈ ℝ` has `0 < fullKLSpectrum x < 1`. -/
theorem fullKLSpectrum_first_gap (x : ℝ) :
    ¬ (0 < fullKLSpectrum x ∧ fullKLSpectrum x < 1) := by
  rintro ⟨hpos, hlt⟩
  have h0 : fullKLSpectrum x = 0 := ((fullKLSpectrum_zero_tfae x).out 2 1).mp hlt
  exact hpos.ne' h0

/-- **Infinite Half-Integer Spectral Gaps for `fullKLSpectrum`**:
For every `k ≥ 2` and `L ∈ (k / 2, (k + 1) / 2)`, `fullKLSpectrum x ≠ ENNReal.ofReal L`. -/
theorem fullKLSpectrum_open_gap (k : ℕ) (hk : 2 ≤ k) {L : ℝ}
    (hkL : (k : ℝ) / 2 < L) (hLk1 : L < ((k : ℝ) + 1) / 2) (x : ℝ) :
    fullKLSpectrum x ≠ ENNReal.ofReal L := by
  intro hEq
  have hfin : apprExponent x ≠ ⊤ := fun htop => by
    rw [(fullKLSpectrum_eq x).1 htop] at hEq
    exact ENNReal.ofReal_ne_top hEq.symm
  rw [(fullKLSpectrum_eq x).2 hfin] at hEq
  have hk2 : (1 : ℝ) ≤ (k : ℝ) / 2 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have h1lt : (1 : ℝ≥0∞) < ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hind_le : (if parityFlip x then (1 : ℝ≥0∞) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have h2lam : 2 * apprExponent x = ENNReal.ofReal L := by
    by_contra hne
    have hgt : 2 * apprExponent x < ENNReal.ofReal L :=
      lt_of_le_of_ne (hEq ▸ le_max_left _ _) hne
    have hmax_le : max (2 * apprExponent x) (if parityFlip x then (1 : ℝ≥0∞) else 0) <
        ENNReal.ofReal L := max_lt hgt (hind_le.trans_lt h1lt)
    rw [hEq] at hmax_le
    exact (lt_irrefl _) hmax_le
  have hlam_eq : apprExponent x = ENNReal.ofReal (L / 2) := by
    have hL2 : 0 < L / 2 := by linarith
    have h2 : ENNReal.ofReal L = 2 * ENNReal.ofReal (L / 2) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [h2] at h2lam
    exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h2lam
  exact FullSpectrumDiscrete.spectral_gap_open_interval k
    (by linarith) (by linarith) x hlam_eq

/-- **Open Spectral Gaps for `fullRawSpectrum`**:
For every `k ≥ 0` and `L ∈ (k / 2, (k + 1) / 2)`, `fullRawSpectrum x ≠ ENNReal.ofReal L`. -/
theorem fullRawSpectrum_open_gap (k : ℕ) {L : ℝ}
    (hkL : (k : ℝ) / 2 < L) (hLk1 : L < ((k : ℝ) + 1) / 2) (x : ℝ) :
    fullRawSpectrum x ≠ ENNReal.ofReal L := by
  intro hEq
  have hfin : apprExponent x ≠ ⊤ := fun htop => by
    rw [(fullRawSpectrum_eq x).1 htop] at hEq
    exact ENNReal.ofReal_ne_top hEq.symm
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have hlt : fullRawSpectrum x < (1 / 2 : ℝ≥0∞) := by
      rw [hEq, ← ofReal_half]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by simpa using hLk1)
    have h0 : fullRawSpectrum x = 0 := ((fullKLSpectrum_zero_tfae x).out 4 3).mp hlt
    rw [h0] at hEq
    have hLpos : 0 < L := by simpa using hkL
    exact (ENNReal.ofReal_pos.mpr hLpos).ne' hEq.symm
  · rw [(fullRawSpectrum_eq x).2 hfin] at hEq
    have hk2 : (1 / 2 : ℝ) ≤ (k : ℝ) / 2 := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      linarith
    have h12lt : (1 / 2 : ℝ≥0∞) < ENNReal.ofReal L := by
      rw [← ofReal_half]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    have hind_le : (if parityFlip x then (1 / 2 : ℝ≥0∞) else 0) ≤ (1 / 2 : ℝ≥0∞) := by
      split_ifs
      · exact le_rfl
      · exact bot_le
    have h2lam : 2 * apprExponent x = ENNReal.ofReal L := by
      by_contra hne
      have hgt : 2 * apprExponent x < ENNReal.ofReal L :=
        lt_of_le_of_ne (hEq ▸ le_max_left _ _) hne
      have hmax_le : max (2 * apprExponent x) (if parityFlip x then (1 / 2 : ℝ≥0∞) else 0) <
          ENNReal.ofReal L := max_lt hgt (hind_le.trans_lt h12lt)
      rw [hEq] at hmax_le
      exact (lt_irrefl _) hmax_le
    have hlam_eq : apprExponent x = ENNReal.ofReal (L / 2) := by
      have h2 : ENNReal.ofReal L = 2 * ENNReal.ofReal (L / 2) := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
      rw [h2] at h2lam
      exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h2lam
    exact FullSpectrumDiscrete.spectral_gap_open_interval k
      (by linarith) (by linarith) x hlam_eq

private lemma apprExponent_xPlus (k : ℕ) (hk : 1 ≤ k) :
    apprExponent (xPlus k) = ENNReal.ofReal ((k : ℝ) / 4) := by
  have hmem := xPlus_mem_signedExactLimitSet k hk
  have hlim : Tendsto (apprSeq (xPlus k)) atTop (nhds ((k : ℝ) / 4)) := by
    have habs := hmem.abs
    have hk0 : 0 ≤ (k : ℝ) / 4 := by positivity
    rw [abs_of_nonneg hk0] at habs
    refine habs.congr fun j => ?_
    simp only [apprSeq, eps, nearestInt, distToNearestInt]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
  exact (ENNReal.tendsto_ofReal hlim).limsup_eq

/-- **Exact Full-Convergent Kraaikamp–Liardet Spectrum Range**:
`fullKLSpectrum (ℝ) = {0} ∪ {k / 2 : k ∈ ℕ, 2 ≤ k} ∪ {⊤}`. -/
theorem fullKLSpectrum_range :
    (∀ x : ℝ, fullKLSpectrum x = 0 ∨
      (∃ k : ℕ, 2 ≤ k ∧ fullKLSpectrum x = ENNReal.ofReal ((k : ℝ) / 2)) ∨
      fullKLSpectrum x = ⊤) ∧
    (∃ x : ℝ, fullKLSpectrum x = 0) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ x : ℝ, fullKLSpectrum x = ENNReal.ofReal ((k : ℝ) / 2)) ∧
    (∀ᵐ x ∂MeasureTheory.volume, fullKLSpectrum x = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    by_cases htop : fullKLSpectrum x = ⊤
    · exact Or.inr (Or.inr htop)
    · by_cases hlt1 : fullKLSpectrum x < 1
      · exact Or.inl (((fullKLSpectrum_zero_tfae x).out 2 1).mp hlt1)
      · push Not at hlt1
        right; left
        set L : ℝ := (fullKLSpectrum x).toReal
        have hL_ge1 : 1 ≤ L := by
          have := (ENNReal.toReal_le_toReal (by norm_num) htop).mpr hlt1
          simpa [L] using this
        have hEqL : fullKLSpectrum x = ENNReal.ofReal L := (ENNReal.ofReal_toReal htop).symm
        let k : ℕ := ⌊2 * L⌋₊
        have hk2 : 2 ≤ k := by
          have h2L : (2 : ℝ) ≤ 2 * L := by linarith
          exact Nat.le_floor h2L
        have hk_le : (k : ℝ) / 2 ≤ L := by
          have := Nat.floor_le (by linarith : 0 ≤ 2 * L)
          linarith
        have hlt_succ : L < ((k : ℝ) + 1) / 2 := by
          have := Nat.lt_floor_add_one (2 * L)
          linarith
        rcases eq_or_lt_of_le hk_le with heq | hgt
        · rw [← heq] at hEqL
          exact ⟨k, hk2, hEqL⟩
        · exact (fullKLSpectrum_open_gap k hk2 hgt hlt_succ x hEqL).elim
  · refine ⟨0, ?_⟩
    have hx0 : (0 : ℝ) ∈ latticeE := ⟨0, 0, by norm_num⟩
    exact ((fullKLSpectrum_zero_tfae 0).out 5 1).mp hx0
  · intro k hk
    refine ⟨xPlus k, ?_⟩
    have hk_one : 1 ≤ k := by omega
    have happ := apprExponent_xPlus k hk_one
    have hfin : apprExponent (xPlus k) ≠ ⊤ := by rw [happ]; exact ENNReal.ofReal_ne_top
    rw [(fullKLSpectrum_eq (xPlus k)).2 hfin, happ]
    have h2 : 2 * ENNReal.ofReal ((k : ℝ) / 4) = ENNReal.ofReal ((k : ℝ) / 2) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [h2]
    have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((k : ℝ) / 2) := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hind : (if parityFlip (xPlus k) then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal ((k : ℝ) / 2) :=
      le_trans (by split_ifs <;> norm_num) h1le
    exact max_eq_left hind
  · exact GaugeExact.ae_apprExponent_eq_top.mono fun x hx => (fullKLSpectrum_eq x).1 hx

/-- **Exact Raw Partial-Quotient Full Spectrum Range**:
`fullRawSpectrum (ℝ) = (1 / 2) ℤ_{≥ 0} ∪ {⊤}`. -/
theorem fullRawSpectrum_range :
    (∀ x : ℝ, (∃ k : ℕ, fullRawSpectrum x = ENNReal.ofReal ((k : ℝ) / 2)) ∨
      fullRawSpectrum x = ⊤) ∧
    (∀ k : ℕ, ∃ x : ℝ, fullRawSpectrum x = ENNReal.ofReal ((k : ℝ) / 2)) ∧
    (∀ᵐ x ∂MeasureTheory.volume, fullRawSpectrum x = ⊤) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    by_cases htop : fullRawSpectrum x = ⊤
    · exact Or.inr htop
    · left
      set L : ℝ := (fullRawSpectrum x).toReal
      have hEqL : fullRawSpectrum x = ENNReal.ofReal L := (ENNReal.ofReal_toReal htop).symm
      let k : ℕ := ⌊2 * L⌋₊
      have hk_le : (k : ℝ) / 2 ≤ L := by
        have := Nat.floor_le (by positivity : 0 ≤ 2 * L)
        linarith
      have hlt_succ : L < ((k : ℝ) + 1) / 2 := by
        have := Nat.lt_floor_add_one (2 * L)
        linarith
      rcases eq_or_lt_of_le hk_le with heq | hgt
      · rw [← heq] at hEqL
        exact ⟨k, hEqL⟩
      · exact (fullRawSpectrum_open_gap k hgt hlt_succ x hEqL).elim
  · intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · refine ⟨0, ?_⟩
      have hx0 : (0 : ℝ) ∈ latticeE := ⟨0, 0, by norm_num⟩
      have h0 : fullRawSpectrum 0 = 0 := ((fullKLSpectrum_zero_tfae 0).out 5 3).mp hx0
      simpa using h0
    · refine ⟨xPlus k, ?_⟩
      have happ := apprExponent_xPlus k hk1
      have hfin : apprExponent (xPlus k) ≠ ⊤ := by rw [happ]; exact ENNReal.ofReal_ne_top
      rw [(fullRawSpectrum_eq (xPlus k)).2 hfin, happ]
      have h2 : 2 * ENNReal.ofReal ((k : ℝ) / 4) = ENNReal.ofReal ((k : ℝ) / 2) := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
      rw [h2]
      have h12le : (1 / 2 : ℝ≥0∞) ≤ ENNReal.ofReal ((k : ℝ) / 2) := by
        rw [← ofReal_half]
        apply ENNReal.ofReal_le_ofReal
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        linarith
      have hind : (if parityFlip (xPlus k) then (1 / 2 : ℝ≥0∞) else 0) ≤
          ENNReal.ofReal ((k : ℝ) / 2) := by
        split_ifs
        · exact h12le
        · exact bot_le
      exact max_eq_left hind
  · exact GaugeExact.ae_apprExponent_eq_top.mono fun x hx => (fullRawSpectrum_eq x).1 hx

/-! ## Part 6: Exact Level-Set Identifications, Critical Gauges, and Coarse Collapse -/

/-- The zero level set of `fullKLSpectrum` and `fullRawSpectrum` is `ℤ + ℤ e`. -/
theorem fullKLSpectrum_zero_set :
    {x : ℝ | fullKLSpectrum x = 0} = latticeE ∧
    {x : ℝ | fullRawSpectrum x = 0} = latticeE :=
  ⟨Set.ext fun x => (fullKLSpectrum_zero_tfae x).out 1 5,
   Set.ext fun x => (fullKLSpectrum_zero_tfae x).out 3 5⟩

/-- Exact level-`1` set of `fullKLSpectrum`: `oddCosetE ∪ {Λ = 1/4} ∪ {Λ = 1/2}`
(three disjoint pieces; dominated by `Λ = 1/2`, gauge base `5`). -/
theorem fullKLSpectrum_one_set :
    {x : ℝ | fullKLSpectrum x = 1} =
      oddCosetE ∪
      {x : ℝ | apprExponent x = ENNReal.ofReal (1 / 4)} ∪
      {x : ℝ | apprExponent x = ENNReal.ofReal (1 / 2)} := by
  ext x
  simp only [mem_ofPred_eq, mem_union]
  constructor
  · intro h1
    have h1_orig : fullKLSpectrum x = 1 := h1
    have hfin : apprExponent x ≠ ⊤ := fun htop => by
      rw [(fullKLSpectrum_eq x).1 htop] at h1
      exact ENNReal.one_ne_top h1.symm
    rw [(fullKLSpectrum_eq x).2 hfin] at h1
    have h2lam_le : 2 * apprExponent x ≤ 1 := h1 ▸ le_max_left _ _
    have hlam_le : apprExponent x ≤ ENNReal.ofReal (1 / 2) := by
      have hto : (2 * apprExponent x).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top h2lam_le
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_one] at hto
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    rcases eq_or_lt_of_le hlam_le with heq2 | hlt2
    · exact Or.inr heq2
    · by_cases h14 : apprExponent x = ENNReal.ofReal (1 / 4)
      · exact Or.inl (Or.inr h14)
      · have hlt14 : apprExponent x < ENNReal.ofReal (1 / 4) := by
          by_contra hge
          push Not at hge
          have hgt : ENNReal.ofReal (1 / 4) < apprExponent x := lt_of_le_of_ne hge (Ne.symm h14)
          have hgap := FullSpectrumDiscrete.spectral_gap_open_interval 1
            (L := (apprExponent x).toReal) ?_ ?_ x
          · exact hgap (ENNReal.ofReal_toReal hfin).symm
          · have hltR := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfin).mpr hgt
            rw [ENNReal.toReal_ofReal (by norm_num)] at hltR
            norm_num
            linarith
          · have hltR := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hlt2
            rw [ENNReal.toReal_ofReal (by norm_num)] at hltR
            norm_num
            linarith
        have hxL : x ∈ latticeL := by
          rcases SpectralGap.spectral_gap x with h0 | hge
          · exact (Classification.theorem2_classification x).mp ((apprExponent_eq_zero_iff x).mp h0)
          · exact (not_lt_of_ge hge (ofReal_quarter ▸ hlt14)).elim
        rw [latticeL_eq_union] at hxL
        rcases hxL with hxE | hxO
        · have h0 := ((fullKLSpectrum_zero_tfae x).out 5 1).mp hxE
          rw [h0] at h1_orig
          exact absurd h1_orig zero_ne_one
        · exact Or.inl (Or.inl hxO)
  · rintro ((hxO | h14) | h12)
    · have hxL := oddCosetE_subset_latticeL hxO
      have h0 : apprExponent x = 0 := (apprExponent_eq_zero_iff x).mpr
        ((Classification.theorem2_classification x).mpr hxL)
      have hp := parityFlip_of_mem_oddCosetE hxO
      rw [(fullKLSpectrum_eq x).2 (by rw [h0]; simp), h0]
      simp [hp]
    · have hfin : apprExponent x ≠ ⊤ := by rw [h14]; exact ENNReal.ofReal_ne_top
      have hp := parityFlip_of_apprExponent_eq_quarter h14
      rw [(fullKLSpectrum_eq x).2 hfin, h14]
      simp only [hp, ↓reduceIte]
      rw [two_mul_ofReal_quarter]
      exact max_eq_right
        (by rw [← ofReal_half, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num))
    · have hfin : apprExponent x ≠ ⊤ := by rw [h12]; exact ENNReal.ofReal_ne_top
      rw [(fullKLSpectrum_eq x).2 hfin, h12]
      have h2 : 2 * ENNReal.ofReal (1 / 2) = 1 := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
          show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.ofReal_one]
      rw [h2]
      exact max_eq_left (by split_ifs <;> norm_num)

/-- For every `k ≥ 3`, the full-convergent KL level `{fullKLSpectrum = k / 2}` coincides
identically with `{apprExponent = k / 4}` (critical gauge base `2k + 1`). -/
theorem fullKLSpectrum_eq_exactLevel_of_three_le (k : ℕ) (hk : 3 ≤ k) :
    {x : ℝ | fullKLSpectrum x = ENNReal.ofReal ((k : ℝ) / 2)} =
      {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} := by
  ext x
  simp only [mem_ofPred_eq]
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1lt : (1 : ℝ≥0∞) < ENNReal.ofReal ((k : ℝ) / 2) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have h2eq : 2 * ENNReal.ofReal ((k : ℝ) / 4) = ENNReal.ofReal ((k : ℝ) / 2) := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  constructor
  · intro hx
    have hfin : apprExponent x ≠ ⊤ := fun htop => by
      rw [(fullKLSpectrum_eq x).1 htop] at hx
      exact ENNReal.ofReal_ne_top hx.symm
    rw [(fullKLSpectrum_eq x).2 hfin] at hx
    have hind : (if parityFlip x then (1 : ℝ≥0∞) else 0) ≤ 1 := by split_ifs <;> norm_num
    have h2lam : 2 * apprExponent x = ENNReal.ofReal ((k : ℝ) / 2) := by
      by_contra hne
      have hlt : 2 * apprExponent x < ENNReal.ofReal ((k : ℝ) / 2) :=
        lt_of_le_of_ne (hx ▸ le_max_left _ _) hne
      have hmax := max_lt hlt (hind.trans_lt h1lt)
      rw [hx] at hmax
      exact lt_irrefl _ hmax
    rw [← h2eq] at h2lam
    exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h2lam
  · intro hx
    have hfin : apprExponent x ≠ ⊤ := by rw [hx]; exact ENNReal.ofReal_ne_top
    rw [(fullKLSpectrum_eq x).2 hfin, hx, h2eq]
    exact max_eq_left (le_trans (by split_ifs <;> norm_num) h1lt.le)

/-- Exact level-`1/2` set of `fullRawSpectrum`: `oddCosetE ∪ {Λ = 1/4}` (gauge base `3`),
and for all `k ≥ 2`, `{fullRawSpectrum = k / 2} = {Λ = k / 4}` (gauge base `2k + 1`). -/
theorem fullRawSpectrum_level_sets :
    {x : ℝ | fullRawSpectrum x = (1 / 2 : ℝ≥0∞)} =
      oddCosetE ∪ {x : ℝ | apprExponent x = ENNReal.ofReal (1 / 4)} ∧
    ∀ k : ℕ, 2 ≤ k →
      {x : ℝ | fullRawSpectrum x = ENNReal.ofReal ((k : ℝ) / 2)} =
        {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} := by
  refine ⟨?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_union]
    constructor
    · intro h12
      have h12_orig : fullRawSpectrum x = (1 / 2 : ℝ≥0∞) := h12
      have hfin : apprExponent x ≠ ⊤ := fun htop => by
        rw [(fullRawSpectrum_eq x).1 htop, ← ofReal_half] at h12
        exact ENNReal.ofReal_ne_top h12.symm
      rw [(fullRawSpectrum_eq x).2 hfin] at h12
      have h2lam_le : 2 * apprExponent x ≤ (1 / 2 : ℝ≥0∞) := h12 ▸ le_max_left _ _
      have hlam_le : apprExponent x ≤ ENNReal.ofReal (1 / 4) := by
        have hto : (2 * apprExponent x).toReal ≤ (1 / 2 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono (by rw [← ofReal_half]; exact ENNReal.ofReal_ne_top) h2lam_le
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← ofReal_half,
          ENNReal.toReal_ofReal (by norm_num)] at hto
        rw [← ENNReal.ofReal_toReal hfin]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      rcases eq_or_lt_of_le hlam_le with heq | hlt
      · exact Or.inr heq
      · have hxL : x ∈ latticeL := by
          rcases SpectralGap.spectral_gap x with h0 | hge
          · exact (Classification.theorem2_classification x).mp ((apprExponent_eq_zero_iff x).mp h0)
          · exact (not_lt_of_ge hge (ofReal_quarter ▸ hlt)).elim
        rw [latticeL_eq_union] at hxL
        rcases hxL with hxE | hxO
        · have h0 := ((fullKLSpectrum_zero_tfae x).out 5 3).mp hxE
          rw [h0, ← ofReal_half, ← ENNReal.ofReal_zero] at h12_orig
          have := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)).mp h12_orig
          norm_num at this
        · exact Or.inl hxO
    · rintro (hxO | h14)
      · have hxL := oddCosetE_subset_latticeL hxO
        have h0 : apprExponent x = 0 := (apprExponent_eq_zero_iff x).mpr
          ((Classification.theorem2_classification x).mpr hxL)
        have hp := parityFlip_of_mem_oddCosetE hxO
        rw [(fullRawSpectrum_eq x).2 (by rw [h0]; simp), h0]
        simp [hp]
      · have hfin : apprExponent x ≠ ⊤ := by rw [h14]; exact ENNReal.ofReal_ne_top
        have hp := parityFlip_of_apprExponent_eq_quarter h14
        rw [(fullRawSpectrum_eq x).2 hfin, h14]
        simp only [hp, ↓reduceIte]
        rw [two_mul_ofReal_quarter, max_self]
  · intro k hk
    ext x
    simp only [mem_ofPred_eq]
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h12lt : (1 / 2 : ℝ≥0∞) < ENNReal.ofReal ((k : ℝ) / 2) := by
      rw [← ofReal_half]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    have h2eq : 2 * ENNReal.ofReal ((k : ℝ) / 4) = ENNReal.ofReal ((k : ℝ) / 2) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    constructor
    · intro hx
      have hfin : apprExponent x ≠ ⊤ := fun htop => by
        rw [(fullRawSpectrum_eq x).1 htop] at hx
        exact ENNReal.ofReal_ne_top hx.symm
      rw [(fullRawSpectrum_eq x).2 hfin] at hx
      have hind : (if parityFlip x then (1 / 2 : ℝ≥0∞) else 0) ≤ (1 / 2 : ℝ≥0∞) := by
        split_ifs
        · exact le_rfl
        · exact bot_le
      have h2lam : 2 * apprExponent x = ENNReal.ofReal ((k : ℝ) / 2) := by
        by_contra hne
        have hlt : 2 * apprExponent x < ENNReal.ofReal ((k : ℝ) / 2) :=
          lt_of_le_of_ne (hx ▸ le_max_left _ _) hne
        have hmax := max_lt hlt (hind.trans_lt h12lt)
        rw [hx] at hmax
        exact lt_irrefl _ hmax
      rw [← h2eq] at h2lam
      exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h2lam
    · intro hx
      have hfin : apprExponent x ≠ ⊤ := by rw [hx]; exact ENNReal.ofReal_ne_top
      rw [(fullRawSpectrum_eq x).2 hfin, hx, h2eq]
      refine max_eq_left ?_
      split_ifs
      · exact h12lt.le
      · exact bot_le

/-- **Critical Gauge Transfer for `fullKLSpectrum` and `fullRawSpectrum`**:
- At `fullKLSpectrum = 1`, `critGauge 2` (`base = 5`) gives infinite measure `⊤` (and `dimH = 0`);
- For `k ≥ 3`, `fullKLSpectrum = k / 2` has the exact critical gauge `critGauge k`
  (`base = 2k + 1`) and full `liminf` classification;
- At `fullRawSpectrum = 1 / 2`, `critGauge 1` (`base = 3`) gives infinite measure `⊤`;
- For `k ≥ 2`, `fullRawSpectrum = k / 2` has exact critical gauge `critGauge k` (`base = 2k+1`). -/
theorem fullSpectrum_critical_gauges :
    (Measure.mkMetric (critGauge 2) {x : ℝ | fullKLSpectrum x = 1} = ⊤) ∧
    (∀ k : ℕ, 3 ≤ k →
      Measure.mkMetric (critGauge k) {x : ℝ | fullKLSpectrum x = ENNReal.ofReal ((k : ℝ) / 2)} = ⊤ ∧
      dimH {x : ℝ | fullKLSpectrum x = ENNReal.ofReal ((k : ℝ) / 2)} = 0) ∧
    (Measure.mkMetric (critGauge 1) {x : ℝ | fullRawSpectrum x = (1 / 2 : ℝ≥0∞)} = ⊤) ∧
    (∀ k : ℕ, 2 ≤ k →
      Measure.mkMetric (critGauge k)
        {x : ℝ | fullRawSpectrum x = ENNReal.ofReal ((k : ℝ) / 2)} = ⊤ ∧
      dimH {x : ℝ | fullRawSpectrum x = ENNReal.ofReal ((k : ℝ) / 2)} = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fullKLSpectrum_one_set]
    have h24 : ((2 : ℕ) : ℝ) / 4 = 1 / 2 := by norm_num
    have hsub : {x : ℝ | apprExponent x = ENNReal.ofReal (((2 : ℕ) : ℝ) / 4)} ⊆
        oddCosetE ∪ {x : ℝ | apprExponent x = ENNReal.ofReal (1 / 4)} ∪
          {x : ℝ | apprExponent x = ENNReal.ofReal (1 / 2)} := by
      rw [h24]
      exact Set.subset_union_right
    exact top_unique ((mkMetric_critGauge_exactLevel_eq_top 2 (by omega)).symm.trans_le
      (measure_mono hsub))
  · intro k hk
    rw [fullKLSpectrum_eq_exactLevel_of_three_le k hk]
    refine ⟨mkMetric_critGauge_exactLevel_eq_top k (by omega), le_antisymm ?_ zero_le⟩
    exact (dimH_mono (t := SpectralGap.levelSet (ENNReal.ofReal ((k : ℝ) / 4)))
      fun _ (hx : apprExponent _ = _) => le_of_eq hx).trans
      (DimHFinite.dimH_levelSet_finite ((k : ℝ) / 4)).le
  · rw [fullRawSpectrum_level_sets.1]
    have h14 : ((1 : ℕ) : ℝ) / 4 = 1 / 4 := by norm_num
    have hsub : {x : ℝ | apprExponent x = ENNReal.ofReal (((1 : ℕ) : ℝ) / 4)} ⊆
        oddCosetE ∪ {x : ℝ | apprExponent x = ENNReal.ofReal (1 / 4)} := by
      rw [h14]
      exact Set.subset_union_right
    exact top_unique ((mkMetric_critGauge_exactLevel_eq_top 1 le_rfl).symm.trans_le
      (measure_mono hsub))
  · intro k hk
    rw [fullRawSpectrum_level_sets.2 k hk]
    refine ⟨mkMetric_critGauge_exactLevel_eq_top k (by omega), le_antisymm ?_ zero_le⟩
    exact (dimH_mono (t := SpectralGap.levelSet (ENNReal.ofReal ((k : ℝ) / 4)))
      fun _ (hx : apprExponent _ = _) => le_of_eq hx).trans
      (DimHFinite.dimH_levelSet_finite ((k : ℝ) / 4)).le

/-- **Coarse Metric Collapse for Both Full-Convergent Spectra**:
`{fullKLSpectrum < ⊤} = {fullRawSpectrum < ⊤} = {apprExponent < ⊤}`, hence Hausdorff dimension `0`
and Lebesgue measure `0`, while both spectra equal `⊤` Lebesgue-a.e. with full dimension `1`. -/
theorem fullSpectrum_coarse_collapse :
    {x : ℝ | fullKLSpectrum x < ⊤} = {x : ℝ | apprExponent x < ⊤} ∧
    {x : ℝ | fullRawSpectrum x < ⊤} = {x : ℝ | apprExponent x < ⊤} ∧
    dimH {x : ℝ | fullKLSpectrum x < ⊤} = 0 ∧
    MeasureTheory.volume {x : ℝ | fullKLSpectrum x < ⊤} = 0 ∧
    dimH {x : ℝ | fullKLSpectrum x = ⊤} = 1 ∧
    (∀ᵐ x ∂MeasureTheory.volume, fullKLSpectrum x = ⊤) := by
  have hKL : {x : ℝ | fullKLSpectrum x < ⊤} = {x : ℝ | apprExponent x < ⊤} := by
    ext x
    simp only [mem_ofPred_eq, lt_top_iff_ne_top]
    constructor
    · intro hfin htop
      exact hfin ((fullKLSpectrum_eq x).1 htop)
    · intro hfin
      rw [(fullKLSpectrum_eq x).2 hfin]
      exact (max_lt (ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr hfin))
        (by split_ifs <;> simp)).ne
  have hRaw : {x : ℝ | fullRawSpectrum x < ⊤} = {x : ℝ | apprExponent x < ⊤} := by
    ext x
    simp only [mem_ofPred_eq, lt_top_iff_ne_top]
    constructor
    · intro hfin htop
      exact hfin ((fullRawSpectrum_eq x).1 htop)
    · intro hfin
      rw [(fullRawSpectrum_eq x).2 hfin]
      refine (max_lt (ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr hfin)) ?_).ne
      split_ifs
      · rw [← ofReal_half]; exact ENNReal.ofReal_lt_top
      · exact ENNReal.zero_lt_top
  have hInf : {x : ℝ | fullKLSpectrum x = ⊤} = {x : ℝ | apprExponent x = ⊤} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor
    · intro htop
      by_contra hfin
      have hlt : fullKLSpectrum x < ⊤ := by
        rw [(fullKLSpectrum_eq x).2 hfin]
        exact max_lt (ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr hfin))
          (by split_ifs <;> simp)
      exact hlt.ne htop
    · exact (fullKLSpectrum_eq x).1
  refine ⟨hKL, hRaw, ?_, ?_, ?_, ?_⟩
  · rw [hKL]; exact GaugeExact.dimH_finiteLevel_zero
  · rw [hKL]; exact GaugeExact.volume_finiteLevel_zero
  · rw [hInf]; exact GaugeExact.dimH_infiniteLevel_eq_one
  · exact fullKLSpectrum_range.2.2.2

end

end FullConvergentSpectrum
