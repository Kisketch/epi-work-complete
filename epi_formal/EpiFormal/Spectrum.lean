/-
Copyright (c) 2026. All rights reserved.
Task C: S3 Lemma 5 + S4 Theorem 6 — the finite spectrum of j‖Q_j x‖ is exactly {k/4}.

SELF-CONTAINED single file (imports only Mathlib). Does NOT modify the main project.
Does NOT prove or claim that e + π is irrational (that problem remains open).

Foundation (方式二, self-built): selected convergents Psel/Qsel of e.
Only the two `deltaSel` analytic axioms are assumed; all integer algebra is proved.
The spectrum results (Lemma 5 / Theorem 6) depend only on the Qsel recurrence.
-/
import Mathlib

set_option maxHeartbeats 1600000

open Filter Topology

namespace CSpectrum

/-! ## Foundation: selected convergents -/

-- Paired primitive recursion: pAux n = (P_{n+1}, P_{n+2}), qAux n = (Q_{n+1}, Q_{n+2}).
-- Coefficient 4n+10 = 4(n+2)+2 matches X_{j+1} = (4j+2) X_j + X_{j-1} at j = n+2.
private def pAux : ℕ → ℤ × ℤ
  | 0 => (3, 19)
  | n + 1 => let p := pAux n; (p.2, (4 * (n : ℤ) + 10) * p.2 + p.1)

private def qAux : ℕ → ℤ × ℤ
  | 0 => (1, 7)
  | n + 1 => let p := qAux n; (p.2, (4 * (n : ℤ) + 10) * p.2 + p.1)

/-- Numerators of selected convergents: 3, 19, 193, ... (index 0 is a placeholder 0). -/
def Psel : ℕ → ℤ
  | 0 => 0
  | n + 1 => (pAux n).1

/-- Denominators of selected convergents: 1, 7, 71, 1001, ... (index 0 is a placeholder 0). -/
def Qsel : ℕ → ℤ
  | 0 => 0
  | n + 1 => (qAux n).1

@[simp] lemma Psel_one : Psel 1 = 3 := rfl
@[simp] lemma Psel_two : Psel 2 = 19 := rfl
@[simp] lemma Qsel_one : Qsel 1 = 1 := rfl
@[simp] lemma Qsel_two : Qsel 2 = 7 := rfl

private lemma idx1 (n : ℕ) : n + 2 - 1 = n + 1 := by omega

lemma Psel_rec (j : ℕ) (hj : 2 ≤ j) :
    Psel (j + 1) = (4 * (j : ℤ) + 2) * Psel j + Psel (j - 1) := by
  rcases j with (_ | _ | n)
  · omega
  · omega
  · simp only [Psel]
    have h1 : (pAux (n + 2)).1 = (pAux (n + 1)).2 := rfl
    have h2 : (pAux (n + 1)).2 = (4 * (n : ℤ) + 10) * (pAux n).2 + (pAux n).1 := rfl
    have h3 : (pAux n).2 = (pAux (n + 1)).1 := rfl
    have hsub : n + 2 - 1 = n + 1 := idx1 n
    rw [h1, h2, h3, hsub]
    push_cast
    ring

lemma Qsel_rec (j : ℕ) (hj : 2 ≤ j) :
    Qsel (j + 1) = (4 * (j : ℤ) + 2) * Qsel j + Qsel (j - 1) := by
  rcases j with (_ | _ | n)
  · omega
  · omega
  · simp only [Qsel]
    have h1 : (qAux (n + 2)).1 = (qAux (n + 1)).2 := rfl
    have h2 : (qAux (n + 1)).2 = (4 * (n : ℤ) + 10) * (qAux n).2 + (qAux n).1 := rfl
    have h3 : (qAux n).2 = (qAux (n + 1)).1 := rfl
    have hsub : n + 2 - 1 = n + 1 := idx1 n
    rw [h1, h2, h3, hsub]
    push_cast
    ring

private lemma qAux_pos (n : ℕ) : 0 < (qAux n).1 ∧ 0 < (qAux n).2 := by
  induction n with
  | zero =>
    change 0 < (1 : ℤ) ∧ 0 < (7 : ℤ)
    norm_num
  | succ n ih =>
    simp only [qAux]
    constructor
    · exact ih.2
    · have hcoef : (0 : ℤ) < 4 * (n : ℤ) + 10 := by
        have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
        linarith
      nlinarith [ih.1, ih.2]

lemma Qsel_pos (j : ℕ) (hj : 1 ≤ j) : 0 < Qsel j := by
  rcases j with (_ | n)
  · omega
  · exact (qAux_pos n).1

lemma Qsel_double (j : ℕ) (hj : 1 ≤ j) : 2 * Qsel j ≤ Qsel (j + 1) := by
  rcases j with (_ | n)
  · omega
  · rcases n with (_ | n)
    · norm_num [Qsel, qAux]
    · have hrec := Qsel_rec (n + 2) (by omega)
      have hsub : n + 2 - 1 = n + 1 := idx1 n
      rw [hsub] at hrec
      rw [hrec]
      have hpos := Qsel_pos (n + 2) (by omega)
      have hprev : 0 ≤ Qsel (n + 1) := le_of_lt (Qsel_pos (n + 1) (by omega))
      have hcoef : (2 : ℤ) ≤ 4 * ((n + 2 : ℕ) : ℤ) + 2 := by
        have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hcoef (le_of_lt hpos)]

lemma Qsel_ge_pow (j : ℕ) : (2 : ℤ) ^ j ≤ Qsel (j + 1) := by
  induction j with
  | zero =>
    change (1 : ℤ) ≤ Qsel 1
    norm_num [Qsel, qAux]
  | succ j ih =>
    calc (2 : ℤ) ^ (j + 1) = 2 * (2 : ℤ) ^ j := by ring
      _ ≤ 2 * Qsel (j + 1) := by gcongr
      _ ≤ Qsel (j + 2) := Qsel_double (j + 1) (by omega)

lemma Qsel_tendsto_atTop : Tendsto (fun j => (Qsel j : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun j : ℕ => (2 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hge : ∀ j, (2 : ℝ) ^ j ≤ (Qsel (j + 1) : ℝ) := by
    intro j
    exact_mod_cast Qsel_ge_pow j
  have hshift : Tendsto (fun j => (Qsel (j + 1) : ℝ)) atTop atTop :=
    tendsto_atTop_mono hge hpow
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

lemma Qsel_strictMono : StrictMonoOn Qsel (Set.Ici 1) := by
  have hstep : ∀ n, 1 ≤ n → Qsel n < Qsel (n + 1) := by
    intro n hn
    have hd := Qsel_double n hn
    have hp := Qsel_pos n hn
    linarith
  have hmono : ∀ m d, 1 ≤ m → Qsel m < Qsel (m + d + 1) := by
    intro m d hm
    induction' d with d IH
    · simpa using hstep m hm
    · have := hstep (m + d + 1) (by omega)
      simpa [Nat.add_assoc] using lt_trans IH this
  intro a ha b hb hab
  have hd : ∃ d, b = a + d + 1 := by
    refine ⟨b - a - 1, ?_⟩
    omega
  rcases hd with ⟨d, rfl⟩
  exact hmono a d ha

lemma sel_determinant (j : ℕ) (hj : 1 ≤ j) :
    Psel j * Qsel (j + 1) - Psel (j + 1) * Qsel j = 2 * (-1 : ℤ) ^ (j + 1) := by
  rcases j with (_ | n)
  · omega
  · revert hj
    induction n with
    | zero =>
      intro hj
      norm_num [Psel, Qsel, pAux, qAux]
    | succ n ih =>
      intro hj
      have hp := Psel_rec (n + 2) (by omega)
      have hq := Qsel_rec (n + 2) (by omega)
      have hsub : n + 2 - 1 = n + 1 := idx1 n
      rw [hsub] at hp hq
      have ihn := ih (by omega)
      rw [hp, hq]
      have hsign : (2 : ℤ) * (-1 : ℤ) ^ (n + 3) = -(2 * (-1 : ℤ) ^ (n + 2)) := by
        rw [show (n + 3 : ℕ) = (n + 2) + 1 by ring, pow_succ]
        ring
      rw [hsign, ← ihn]
      ring

-- Joint paired induction: oddness of both components + coprimality of the Q-pair.
private lemma pair_props (n : ℕ) :
    Odd (pAux n).1 ∧ Odd (pAux n).2 ∧ Odd (qAux n).1 ∧ Odd (qAux n).2 ∧
    Int.gcd (qAux n).1 (qAux n).2 = 1 := by
  induction n with
  | zero =>
    refine ⟨⟨1, ?_⟩, ⟨9, ?_⟩, ⟨0, ?_⟩, ⟨3, ?_⟩, ?_⟩ <;>
      norm_num [pAux, qAux, Int.gcd]
  | succ n ih =>
    rcases ih with ⟨hp1, hp2, hq1, hq2, hcop⟩
    have heven : Even (4 * (n : ℤ) + 10) := by
      refine ⟨2 * (n : ℤ) + 5, ?_⟩
      ring
    have hp2' : Odd ((4 * (n : ℤ) + 10) * (pAux n).2 + (pAux n).1) :=
      (heven.mul_right _).add_odd hp1
    have hq2' : Odd ((4 * (n : ℤ) + 10) * (qAux n).2 + (qAux n).1) :=
      (heven.mul_right _).add_odd hq1
    have hcop' : Int.gcd (qAux n).2 ((4 * (n : ℤ) + 10) * (qAux n).2 + (qAux n).1) = 1 := by
      have hcopr : IsCoprime (qAux n).1 (qAux n).2 :=
        Int.isCoprime_iff_gcd_eq_one.mpr hcop
      rcases hcopr with ⟨a, b, hab⟩
      have hnew : IsCoprime (qAux n).2 ((4 * (n : ℤ) + 10) * (qAux n).2 + (qAux n).1) := by
        refine ⟨b - a * (4 * (n : ℤ) + 10), a, ?_⟩
        have : (b - a * (4 * (n : ℤ) + 10)) * (qAux n).2
            + a * ((4 * (n : ℤ) + 10) * (qAux n).2 + (qAux n).1)
            = a * (qAux n).1 + b * (qAux n).2 := by ring
        rw [this, hab]
      exact Int.isCoprime_iff_gcd_eq_one.mp hnew
    simp only [pAux, qAux]
    exact ⟨hp2, hp2', hq2, hq2', hcop'⟩

lemma Psel_odd (j : ℕ) (hj : 1 ≤ j) : Odd (Psel j) := by
  rcases j with (_ | n)
  · omega
  · exact (pair_props n).1

lemma Qsel_odd (j : ℕ) (hj : 1 ≤ j) : Odd (Qsel j) := by
  rcases j with (_ | n)
  · omega
  · exact (pair_props n).2.2.1

lemma Qsel_succ_coprime (j : ℕ) (hj : 1 ≤ j) : Int.gcd (Qsel j) (Qsel (j + 1)) = 1 := by
  rcases j with (_ | n)
  · omega
  · exact (pair_props n).2.2.2.2

/-! ## 联合编译归一说明

C 组谱分类核心定理（Lemma 5 / Theorem 6 / xOf 构造）只依赖 Qsel 整数递推与实数极限，
**不依赖** e 连分数误差估计。原文件中孤立的 `deltaSel` 定义、两条 deltaSel 公理与
`Psel_div_Qsel_tendsto_exp` 引理（仅服务于该孤立引理，核心定理从未引用）已在归一时删除，
使本文件**无任何公理、完全机器验证**。

地基占位约定说明：C 的 `Psel 0 = Qsel 0 = 0`（与 A 组 `Psel 0 = Qsel 0 = 1` 不同），
该占位被 C 的 `Mk`/`xOf` 构造在 j=0 处依赖；j≥1 时 C 与 A 的选定收敛子数值完全一致。
因占位约定差异，C 保留独立命名空间 `CSpectrum` 内的自建地基（数学等价于 A 在 j≥1），
不强行替换为 A 的顶层定义，以免破坏 j=0 处的构造证明。
-/

/-! ## Notation for the spectrum -/

/-- Distance to the nearest integer, ‖y‖ = |y - [y]|. -/
noncomputable def distInt (y : ℝ) : ℝ := |y - (round y : ℝ)|

lemma distInt_nonneg (y : ℝ) : 0 ≤ distInt y := abs_nonneg _

/-- ε_j(x) = Q_j x - M_j where M_j = [Q_j x]. -/
noncomputable def eps (x : ℝ) (j : ℕ) : ℝ :=
  (Qsel j : ℝ) * x - (round ((Qsel j : ℝ) * x) : ℝ)

/-- Integer defect D_j = M_{j+1} - (4j+2) M_j - M_{j-1}. -/
noncomputable def defect (x : ℝ) (j : ℕ) : ℤ :=
  round ((Qsel (j + 1) : ℝ) * x) - (4 * (j : ℤ) + 2) * round ((Qsel j : ℝ) * x)
    - round ((Qsel (j - 1) : ℝ) * x)

/-- S(x) = limsup_j j‖Q_j x‖, as an extended nonnegative real. -/
noncomputable def S (x : ℝ) : ENNReal :=
  limsup (fun j : ℕ => ENNReal.ofReal ((j : ℝ) * distInt ((Qsel j : ℝ) * x))) atTop

/-- Real-valued upper limit of j‖Q_j x‖ (finite when S(x) is finite). -/
noncomputable def SReal (x : ℝ) : ℝ :=
  limsup (fun j : ℕ => (j : ℝ) * distInt ((Qsel j : ℝ) * x)) atTop

/-- Defect identity: D_j - 4j ε_j = 2ε_j + ε_{j-1} - ε_{j+1}, using the Qsel recurrence. -/
lemma defect_identity (x : ℝ) (j : ℕ) (hj : 2 ≤ j) :
    (defect x j : ℝ) - 4 * (j : ℝ) * eps x j =
      2 * eps x j + eps x (j - 1) - eps x (j + 1) := by
  have hq := Qsel_rec j hj
  have hq' : (Qsel (j + 1) : ℝ) = (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by
    exact_mod_cast hq
  simp only [defect, eps]
  push_cast
  rw [hq']
  ring

/-! ## Bounded integer sequences: integer upper limit -/

/-- A bounded integer sequence takes some value infinitely often (finite range + pigeonhole). -/
lemma bounded_int_frequently (a : ℕ → ℤ) (C : ℕ) (hC : ∀ j, |a j| ≤ C) :
    ∃ v : ℤ, ∃ᶠ j in atTop, a j = v := by
  classical
  have hfin : Set.Finite (Set.range a) := by
    apply Set.Finite.subset (Set.finite_Icc (-(C : ℤ)) (C : ℤ))
    intro v hv
    rcases hv with ⟨j, rfl⟩
    have := hC j
    rw [abs_le] at this
    exact ⟨this.1, this.2⟩
  have hfreq : ∃ᶠ j in atTop, ∃ v ∈ Set.range a, a j = v := by
    apply Frequently.of_forall
    intro j
    exact ⟨a j, Set.mem_range_self j, rfl⟩
  rw [hfin.frequently_exists] at hfreq
  rcases hfreq with ⟨v, _, hv⟩
  exact ⟨v, hv⟩

/-- The upper limit of |a_j| for a bounded integer sequence is a natural number.
Proof: the limsup L is a cluster point; if L were not an integer, the open interval
(floor L, floor L + 1) contains L but no integer, contradicting that |a_j| is integer-valued
and frequently near L. -/
lemma bounded_int_limsup_nat (a : ℕ → ℤ) (C : ℕ) (hC : ∀ j, |a j| ≤ C) :
    ∃ m : ℕ, limsup (fun j => (|a j| : ℝ)) atTop = (m : ℝ) := by
  classical
  set L := limsup (fun j : ℕ => (|a j| : ℝ)) atTop with hLdef
  have hbound : ∀ j, (|a j| : ℝ) ≤ C := fun j => by exact_mod_cast hC j
  have hnn : ∀ j, 0 ≤ (|a j| : ℝ) := fun j => abs_nonneg _
  have ha_bdd : IsBoundedUnder (· ≤ ·) atTop (fun j : ℕ => (|a j| : ℝ)) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hbound)
  have ha_cobdd : IsCoboundedUnder (· ≤ ·) atTop (fun j : ℕ => (|a j| : ℝ)) :=
    IsCoboundedUnder.of_frequently_ge (Frequently.of_forall hnn)
  have hLnn : 0 ≤ L := by
    apply le_limsup_of_frequently_le (a := 0) (hu_le := ha_bdd)
    apply Frequently.of_forall; intro j; exact hnn j
  have hLC : L ≤ C := by
    apply limsup_le_of_le (hf := ha_cobdd)
    exact Eventually.of_forall hbound
  -- L is an integer: suppose not, then floor L < L < floor L + 1
  by_cases hint : ∃ m : ℤ, L = m
  · rcases hint with ⟨m, hm⟩
    have hmnn : 0 ≤ m := by
      have := hLnn
      rw [hm] at this
      exact_mod_cast this
    refine ⟨Int.toNat m, ?_⟩
    have hcast : (Int.toNat m : ℝ) = (m : ℝ) := by
      norm_cast
      <;> rw [Int.toNat_of_nonneg hmnn]
    linarith [hm, hcast]
  · -- L not integer: floor L < L < floor L + 1
    push Not at hint
    set n := Int.floor L with hndef
    have hn_lt : (n : ℝ) < L := by
      have hne : L ≠ (n : ℝ) := hint n
      have hle : (n : ℝ) ≤ L := Int.floor_le L
      exact lt_of_le_of_ne hle (Ne.symm hne)
    have hL_lt : L < (n : ℝ) + 1 := Int.lt_floor_add_one L
    have hfreq : ∃ᶠ j in atTop, (n : ℝ) < (|a j| : ℝ) := by
      apply frequently_lt_of_lt_limsup (α := ℕ) (β := ℝ) (f := atTop)
        (u := fun j : ℕ => (|a j| : ℝ)) (b := (n : ℝ)) (hu := ha_cobdd)
      exact hn_lt
    have hev : ∀ᶠ j in atTop, (|a j| : ℝ) < (n : ℝ) + 1 := by
      have hlim_lt : limsup (fun j : ℕ => (|a j| : ℝ)) atTop < (n : ℝ) + 1 := hL_lt
      exact (limsup_le_iff (h₁ := ha_cobdd) (h₂ := ha_bdd)).mp
        le_rfl ((n : ℝ) + 1) hlim_lt
    have hboth : ∃ᶠ j in atTop, (n : ℝ) < (|a j| : ℝ) ∧ (|a j| : ℝ) < (n : ℝ) + 1 :=
      hfreq.and_eventually hev
    have himp : ∃ᶠ j in (atTop : Filter ℕ), False := by
      apply hboth.mono
      intro j hj
      rcases hj with ⟨hj1, hj2⟩
      have h1' : n < |a j| := by
        have := hj1
        rw [← Int.cast_abs] at this
        exact_mod_cast this
      have h2' : |a j| < n + 1 := by
        have := hj2
        rw [← Int.cast_abs] at this
        exact_mod_cast this
      omega
    exact (frequently_false (atTop : Filter ℕ) himp).elim

/-! ## Reverse triangle inequality -/

lemma abs_diff_ineq (D e : ℝ) :
    |abs D - abs e| ≤ |D - e| :=
  abs_abs_sub_abs_le D e

/-! ## δ-lemma: integer upper limit identified via vanishing perturbation -/

/-- If a_j is a bounded integer sequence, b_j ≥ 0, and |a_j| - b_j → 0,
then limsup b_j equals the integer upper limit of |a_j| (a natural number).
Proof: |a_j| and b_j differ by a null sequence, so their limsups coincide (ε-squeeze). -/
lemma integer_limsup_identify (a : ℕ → ℤ) (b : ℕ → ℝ) (C : ℕ)
    (hC : ∀ j, |a j| ≤ C) (hb : ∀ j, 0 ≤ b j)
    (hconv : Tendsto (fun j => (|a j| : ℝ) - b j) atTop (nhds 0)) :
    ∃ m : ℕ, limsup (fun j => (|a j| : ℝ)) atTop = (m : ℝ) ∧
      limsup b atTop = (m : ℝ) := by
  obtain ⟨m, hm⟩ := bounded_int_limsup_nat a C hC
  refine ⟨m, hm, ?_⟩
  have ha_bdd : IsBoundedUnder (· ≤ ·) atTop (fun j : ℕ => (|a j| : ℝ)) :=
    isBoundedUnder_of_eventually_le (a := (C : ℝ))
      (Eventually.of_forall (fun j => by
        have := hC j
        exact mod_cast this))
  have ha_cobdd : IsCoboundedUnder (· ≤ ·) atTop (fun j : ℕ => (|a j| : ℝ)) :=
    IsCoboundedUnder.of_frequently_ge
      (Frequently.of_forall (fun j => abs_nonneg _))
  have hb_cobdd : IsCoboundedUnder (· ≤ ·) atTop b :=
    IsCoboundedUnder.of_frequently_ge (Frequently.of_forall hb)
  have habs_conv : Tendsto (fun j => |( |a j| : ℝ) - b j|) atTop (nhds 0) := by
    have hdist : Tendsto (fun j => dist ((|a j| : ℝ) - b j) 0) atTop (nhds 0) :=
      tendsto_iff_dist_tendsto_zero.mp hconv
    have heq : (fun j => dist ((|a j| : ℝ) - b j) 0) =
        (fun j => |( |a j| : ℝ) - b j|) := by
      funext j
      simp [abs_sub_comm]
    rw [heq] at hdist
    exact hdist
  have hsmall : ∀ ε > 0, ∀ᶠ j in atTop, |( |a j| : ℝ) - b j| < ε := by
    intro ε hε
    have := (Metric.tendsto_nhds.mp habs_conv) ε hε
    filter_upwards [this] with j hj
    simpa [abs_sub_comm] using hj
  have hb_bdd : IsBoundedUnder (· ≤ ·) atTop b := by
    apply isBoundedUnder_of_eventually_le (a := (C + 1 : ℝ))
    filter_upwards [hsmall 1 zero_lt_one] with j hj
    have hCj : (|a j| : ℝ) ≤ C := by
      have := hC j
      exact mod_cast this
    have htri : b j ≤ (|a j| : ℝ) + |( |a j| : ℝ) - b j| := by
      have h1 : b j - (|a j| : ℝ) ≤ |( |a j| : ℝ) - b j| := by
        calc b j - (|a j| : ℝ) = -((|a j| : ℝ) - b j) := by ring
          _ ≤ |( |a j| : ℝ) - b j| := neg_le_abs _
      linarith
    linarith
  -- limsup b ≤ m
  have hle : limsup b atTop ≤ (m : ℝ) := by
    rw [limsup_le_iff (h₁ := hb_cobdd) (h₂ := hb_bdd)]
    intro y hy
    have hε : 0 < y - (m : ℝ) := by linarith
    set ε := (y - (m : ℝ)) / 2 with hεdef
    have hεpos : 0 < ε := by linarith
    have hlim_le : limsup (fun j : ℕ => (|a j| : ℝ)) atTop ≤ (m : ℝ) := by
      linarith [hm]
    have ha_ev : ∀ᶠ j in atTop, (|a j| : ℝ) < (m : ℝ) + ε := by
      have := (limsup_le_iff (h₁ := ha_cobdd) (h₂ := ha_bdd)).mp
        hlim_le ((m : ℝ) + ε)
      apply this
      linarith
    filter_upwards [hsmall ε hεpos, ha_ev] with j hj1 hj2
    have htri : b j ≤ (|a j| : ℝ) + |( |a j| : ℝ) - b j| := by
      have h1 : b j - (|a j| : ℝ) ≤ |( |a j| : ℝ) - b j| := by
        calc b j - (|a j| : ℝ) = -((|a j| : ℝ) - b j) := by ring
          _ ≤ |( |a j| : ℝ) - b j| := neg_le_abs _
      linarith
    linarith
  -- m ≤ limsup b
  have hge : (m : ℝ) ≤ limsup b atTop := by
    rw [le_limsup_iff (h₁ := hb_cobdd) (h₂ := hb_bdd)]
    intro y hy
    have hε : 0 < (m : ℝ) - y := by linarith
    set δ := ((m : ℝ) - y) / 2 with hδdef
    have hδpos : 0 < δ := by linarith
    have hfreq_a : ∃ᶠ j in atTop, y + δ < (|a j| : ℝ) := by
      apply frequently_lt_of_lt_limsup (α := ℕ) (β := ℝ) (f := atTop)
        (u := fun j : ℕ => (|a j| : ℝ)) (b := y + δ) (hu := ha_cobdd)
      linarith [hm]
    have hev_small : ∀ᶠ j in atTop, |( |a j| : ℝ) - b j| < δ := hsmall δ hδpos
    have hfreq := hfreq_a.and_eventually hev_small
    apply hfreq.mono
    intro j hj
    rcases hj with ⟨hj_a, hj_small⟩
    have htri : (|a j| : ℝ) ≤ b j + |( |a j| : ℝ) - b j| := by
      have h1 : (|a j| : ℝ) - b j ≤ |( |a j| : ℝ) - b j| := le_abs_self _
      linarith
    linarith
  linarith

/-! ## S3 Construction: the sequence M_j for a fixed defect k -/

-- Paired recursion: mAux k n = (M_{n+1}, M_{n+2}), M_1 = M_2 = 0,
-- M_{j+1} = (4j+2) M_j + M_{j-1} + k for j ≥ 2.
private def mAux (k : ℕ) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 => let p := mAux k n; (p.2, (4 * (n : ℤ) + 10) * p.2 + p.1 + (k : ℤ))

/-- The constructed integer sequence M_j (index 0 is a placeholder 0). -/
def Mk (k : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (mAux k n).1

@[simp] lemma Mk_one (k : ℕ) : Mk k 1 = 0 := rfl
@[simp] lemma Mk_two (k : ℕ) : Mk k 2 = 0 := rfl

lemma Mk_rec (k : ℕ) (j : ℕ) (hj : 2 ≤ j) :
    Mk k (j + 1) = (4 * (j : ℤ) + 2) * Mk k j + Mk k (j - 1) + (k : ℤ) := by
  rcases j with (_ | _ | n)
  · omega
  · omega
  · simp only [Mk]
    have h1 : (mAux k (n + 2)).1 = (mAux k (n + 1)).2 := rfl
    have h2 : (mAux k (n + 1)).2 =
        (4 * (n : ℤ) + 10) * (mAux k n).2 + (mAux k n).1 + (k : ℤ) := rfl
    have h3 : (mAux k n).2 = (mAux k (n + 1)).1 := rfl
    have hsub : n + 2 - 1 = n + 1 := idx1 n
    rw [h1, h2, h3, hsub]
    push_cast
    ring

/-- W_j = M_{j+1} Q_j - M_j Q_{j+1}. -/
def W (k : ℕ) (j : ℕ) : ℤ := Mk k (j + 1) * Qsel j - Mk k j * Qsel (j + 1)

@[simp] lemma W_one (k : ℕ) : W k 1 = 0 := by
  simp [W, Mk, Qsel, mAux, qAux]

/-- W_j = k Q_j - W_{j-1} for j ≥ 2 (pure integer algebra). -/
lemma W_rec (k : ℕ) (j : ℕ) (hj : 2 ≤ j) :
    W k j = (k : ℤ) * Qsel j - W k (j - 1) := by
  have hm := Mk_rec k j hj
  have hq := Qsel_rec j hj
  have hidx : j - 1 + 1 = j := Nat.sub_add_cancel (by omega : 1 ≤ j)
  simp only [W]
  rw [hm, hq, hidx]
  ring

/-- 0 ≤ W_j ≤ k Q_j for j ≥ 1 (induction using Qsel doubling). -/
lemma W_bounds (k : ℕ) (j : ℕ) (hj : 1 ≤ j) :
    0 ≤ W k j ∧ W k j ≤ (k : ℤ) * Qsel j := by
  rcases j with (_ | n)
  · omega
  · revert hj
    induction n with
    | zero =>
      intro hj
      constructor <;> simp [W, Mk, Qsel, mAux, qAux]
    | succ n ih =>
      intro hj
      rcases n with (_ | n)
      · -- j = 2: W_2 = k Q_2 - W_1 = 7k
        have hw := W_rec k 2 (by omega)
        rw [W_one, sub_zero] at hw
        have hq2 : Qsel 2 = 7 := rfl
        constructor
        · rw [hw, hq2]; positivity
        · rw [hw, hq2]
      · -- j = n + 3. ih gives bounds for W k (n+2).
        have ihn := ih (by omega)
        -- ihn : 0 ≤ W k (n+1+1) ∧ W k (n+1+1) ≤ k * Qsel (n+1+1)
        have hidx : n + 1 + 1 = n + 2 := by ring
        rw [hidx] at ihn
        -- W k (n+3) = k * Qsel (n+3) - W k (n+2)
        have hw := W_rec k (n + 3) (by omega)
        have hsub : n + 3 - 1 = n + 2 := by omega
        rw [hsub] at hw
        -- goal: 0 ≤ W k (n+1+1+1) ∧ ...; normalize to n+3
        have hgoal : n + 1 + 1 + 1 = n + 3 := by ring
        rw [hgoal]
        constructor
        · -- 0 ≤ k * Qsel(n+3) - W k (n+2)
          rw [hw]
          have h1 : W k (n + 2) ≤ (k : ℤ) * Qsel (n + 2) := ihn.2
          have h2 : (k : ℤ) * Qsel (n + 2) ≤ (k : ℤ) * Qsel (n + 3) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hd := Qsel_double (n + 2) (by omega)
            have hidx' : n + 2 + 1 = n + 3 := by ring
            rw [hidx'] at hd
            have hpos : 0 ≤ Qsel (n + 2) := le_of_lt (Qsel_pos (n + 2) (by omega))
            linarith
          linarith
        · -- k * Qsel(n+3) - W k (n+2) ≤ k * Qsel(n+3)
          rw [hw]
          have h1 : 0 ≤ W k (n + 2) := ihn.1
          linarith

/-- Increment bound: 0 ≤ M_{j+1}/Q_{j+1} - M_j/Q_j ≤ k/Q_{j+1} for j ≥ 1. -/
lemma increment_bounds (k : ℕ) (j : ℕ) (hj : 1 ≤ j) :
    0 ≤ (Mk k (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) - (Mk k j : ℝ) / (Qsel j : ℝ) ∧
    (Mk k (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) - (Mk k j : ℝ) / (Qsel j : ℝ)
      ≤ (k : ℝ) / (Qsel (j + 1) : ℝ) := by
  have hw := W_bounds k j hj
  have hqj : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hqj1 : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hW_def : (W k j : ℝ) = (Mk k (j + 1) : ℝ) * (Qsel j : ℝ)
      - (Mk k j : ℝ) * (Qsel (j + 1) : ℝ) := by
    simp only [W]
    push_cast
    ring
  have hdiff : (Mk k (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) - (Mk k j : ℝ) / (Qsel j : ℝ)
      = (W k j : ℝ) / ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ)) := by
    field_simp [hqj.ne', hqj1.ne']
    linarith [hW_def]
  rw [hdiff]
  have hden : 0 < (Qsel j : ℝ) * (Qsel (j + 1) : ℝ) := mul_pos hqj hqj1
  constructor
  · apply div_nonneg _ (le_of_lt hden)
    exact_mod_cast hw.1
  · have hnum : (W k j : ℝ) ≤ (k : ℝ) * (Qsel j : ℝ) := by exact_mod_cast hw.2
    calc (W k j : ℝ) / ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ))
        ≤ ((k : ℝ) * (Qsel j : ℝ)) / ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ)) := by
          gcongr
      _ = (k : ℝ) / (Qsel (j + 1) : ℝ) := by
          field_simp [hqj.ne', hqj1.ne']

/-- The ratio sequence r_j = M_j / Q_j (j ≥ 1) is monotone increasing. -/
lemma ratio_mono (k : ℕ) : MonotoneOn (fun j : ℕ => (Mk k j : ℝ) / (Qsel j : ℝ)) (Set.Ici 1) := by
  intro a ha b hb hab
  -- use increment_bounds iteratively; simpler: show successive increase then transitivity
  have hstep : ∀ n, 1 ≤ n →
      (Mk k n : ℝ) / (Qsel n : ℝ) ≤ (Mk k (n + 1) : ℝ) / (Qsel (n + 1) : ℝ) := by
    intro n hn
    have := (increment_bounds k n hn).1
    linarith
  have hmono : ∀ m d, 1 ≤ m →
      (Mk k m : ℝ) / (Qsel m : ℝ) ≤ (Mk k (m + d) : ℝ) / (Qsel (m + d) : ℝ) := by
    intro m d hm
    induction' d with d IH
    · simpa using le_rfl
    · have := hstep (m + d) (by omega)
      have hidx : m + d + 1 = m + (d + 1) := by ring
      rw [← hidx]
      exact le_trans IH this
  have hd : ∃ d, b = a + d := by
    refine ⟨b - a, ?_⟩
    omega
  rcases hd with ⟨d, rfl⟩
  exact hmono a d ha

/-- Geometric lower bound: Q_{m+2} ≥ 7 · 2^m for m ≥ 0 (from Q_2 = 7 and doubling). -/
lemma Qsel_ge_seven_pow (m : ℕ) :
    (7 : ℤ) * (2 : ℤ) ^ m ≤ Qsel (m + 2) := by
  induction m with
  | zero => norm_num [Qsel, qAux]
  | succ m ih =>
    have hd := Qsel_double (m + 2) (by omega)
    have hidx : m + 2 + 1 = m + 3 := by ring
    rw [hidx] at hd
    have hpow : (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m := by ring
    rw [hpow]
    have hpos : 0 ≤ (7 : ℤ) * (2 : ℤ) ^ m := by positivity
    nlinarith

/-- The ratio sequence is bounded above by 2k/7 (telescoping geometric sum). -/
lemma ratio_bddAbove (k : ℕ) :
    BddAbove (Set.range (fun j : ℕ => (Mk k j : ℝ) / (Qsel j : ℝ))) := by
  refine ⟨max 0 ((2 : ℝ) * (k : ℝ) / 7), ?_⟩
  intro y hy
  rcases hy with ⟨j, rfl⟩
  by_cases hj : 1 ≤ j
  · -- r_j = sum_{i=1}^{j-1} (r_{i+1} - r_i) ≤ sum k/Q_{i+1} ≤ 2k/7
    have hbound : (Mk k j : ℝ) / (Qsel j : ℝ) ≤ (2 : ℝ) * (k : ℝ) / 7 := by
      set r := (fun n : ℕ => (Mk k n : ℝ) / (Qsel n : ℝ)) with hrdef
      -- telescoping: r j - r 1 = sum_{i ∈ range (j-1)} (r (i+2) - r (i+1))
      have hr1 : r 1 = 0 := by simp [r, Mk, Qsel, mAux, qAux]
      have hgen : ∀ m, r (m + 1) - r 1 = ∑ i ∈ Finset.range m, (r (i + 2) - r (i + 1)) := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ, ← ih]
          ring
      have htel : r j = ∑ i ∈ Finset.range (j - 1), (r (i + 2) - r (i + 1)) := by
        have hj' : j = (j - 1) + 1 := by omega
        have := hgen (j - 1)
        rw [hr1, sub_zero] at this
        rw [hj']
        exact this
      change r j ≤ (2 : ℝ) * (k : ℝ) / 7
      rw [htel]
      -- each increment ≤ k/Q_{i+2} ≤ k/(7·2^i)
      have hterm : ∀ i ∈ Finset.range (j - 1),
          r (i + 2) - r (i + 1) ≤ (k : ℝ) / 7 * ((1 : ℝ) / 2) ^ i := by
        intro i hi
        have hi' : 1 ≤ i + 1 := by omega
        have hinc := (increment_bounds k (i + 1) hi').2
        have hQ : (Qsel (i + 2) : ℝ) ≥ 7 * (2 : ℝ) ^ i := by
          have := Qsel_ge_seven_pow i
          exact_mod_cast this
        have hfrac : (k : ℝ) / (Qsel (i + 2) : ℝ) ≤ (k : ℝ) / (7 * (2 : ℝ) ^ i) := by
          apply div_le_div_of_nonneg_left (by positivity) _ hQ
          positivity
        have heq : (k : ℝ) / (7 * (2 : ℝ) ^ i) = (k : ℝ) / 7 * ((1 : ℝ) / 2) ^ i := by
          have hpow : ((1 : ℝ) / 2) ^ i = 1 / (2 : ℝ) ^ i := by
            rw [one_div, inv_pow]
            <;> field_simp
          rw [hpow]
          field_simp
          <;> ring
        have hinc' : r (i + 2) - r (i + 1) ≤ (k : ℝ) / (Qsel (i + 2) : ℝ) := by
          have hidx : i + 1 + 1 = i + 2 := by ring
          have := hinc
          rw [hidx] at this
          simpa [r] using this
        linarith
      calc ∑ i ∈ Finset.range (j - 1), (r (i + 2) - r (i + 1))
          ≤ ∑ i ∈ Finset.range (j - 1), ((k : ℝ) / 7 * ((1 : ℝ) / 2) ^ i) :=
            Finset.sum_le_sum hterm
        _ = (k : ℝ) / 7 * ∑ i ∈ Finset.range (j - 1), ((1 : ℝ) / 2) ^ i := by
            rw [Finset.mul_sum]
        _ ≤ (k : ℝ) / 7 * 2 := by
            gcongr
            apply sum_geometric_two_le
        _ = (2 : ℝ) * (k : ℝ) / 7 := by ring
    apply le_max_of_le_right
    exact hbound
  · have hj0 : j = 0 := by omega
    subst hj0
    simp [Mk, Qsel]

/-- The limit x of the increasing bounded ratio sequence M_j/Q_j. -/
noncomputable def xOf (k : ℕ) : ℝ :=
  ⨆ j : ℕ, (Mk k j : ℝ) / (Qsel j : ℝ)

lemma ratio_tendsto_xOf (k : ℕ) :
    Tendsto (fun j : ℕ => (Mk k j : ℝ) / (Qsel j : ℝ)) atTop (nhds (xOf k)) := by
  -- extend monotonicity to all ℕ (j=0 has r_0 = 0 ≤ r_1)
  have hmono : Monotone (fun j : ℕ => (Mk k j : ℝ) / (Qsel j : ℝ)) := by
    intro a b hab
    change (Mk k a : ℝ) / (Qsel a : ℝ) ≤ (Mk k b : ℝ) / (Qsel b : ℝ)
    by_cases ha : 1 ≤ a
    · have hb : 1 ≤ b := by omega
      exact ratio_mono k ha hb hab
    · have ha0 : a = 0 := by omega
      subst ha0
      have hr0 : (Mk k 0 : ℝ) / (Qsel 0 : ℝ) = 0 := by simp [Mk, Qsel]
      rw [hr0]
      by_cases hb : 1 ≤ b
      · have hr1 : (Mk k 1 : ℝ) / (Qsel 1 : ℝ) = 0 := by simp [Mk, Qsel, mAux, qAux]
        have := ratio_mono k (by omega : 1 ≤ 1) hb (by omega : 1 ≤ b)
        linarith [hr1]
      · have hb0 : b = 0 := by omega
        subst hb0
        simp [Mk, Qsel]
  exact tendsto_atTop_ciSup hmono (ratio_bddAbove k)

/-- Residual bound: 0 ≤ Q_j·xOf k - M_j ≤ 2k·Q_j/Q_{j+1} for j ≥ 1. -/
lemma residual_bound (k : ℕ) (j : ℕ) (hj : 1 ≤ j) :
    0 ≤ (Qsel j : ℝ) * xOf k - (Mk k j : ℝ) ∧
    (Qsel j : ℝ) * xOf k - (Mk k j : ℝ) ≤ 2 * (k : ℝ) * (Qsel j : ℝ) / (Qsel (j + 1) : ℝ) := by
  set r := (fun n : ℕ => (Mk k n : ℝ) / (Qsel n : ℝ)) with hrdef
  have hlim := ratio_tendsto_xOf k
  have hqj : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  -- xOf - r_j = sum_{i ≥ j} (r_{i+1} - r_i); bound by geometric tail
  -- For each i ≥ j, r_{i+1} - r_i ≤ k/Q_{i+1} ≤ k/(7·2^{i-1})
  -- Q_j·(xOf - r_j) = Q_j·sum_{i≥j} increment_i ≤ Q_j·sum_{i≥j} k/Q_{i+1}
  -- ≤ Q_j·(k/Q_{j+1})·sum_{m≥0} (1/2)^m = 2k·Q_j/Q_{j+1}
  have htail : xOf k - r j ≤ 2 * (k : ℝ) / (Qsel (j + 1) : ℝ) := by
    -- use: xOf - r_j = lim_{N} (r_N - r_j) = lim sum_{i=j}^{N-1} increment_i
    -- bound each partial sum by 2k/Q_{j+1}
    have hpartial : ∀ N, j ≤ N → r N - r j ≤ 2 * (k : ℝ) / (Qsel (j + 1) : ℝ) := by
      intro N hjN
      -- r_N - r_j = sum_{i=j}^{N-1} (r_{i+1} - r_i)
      have htel : r N - r j = ∑ i ∈ Finset.Ico j N, (r (i + 1) - r i) := by
        have hgen : ∀ a b, a ≤ b → r b - r a = ∑ i ∈ Finset.Ico a b, (r (i + 1) - r i) := by
          intro a b hab
          induction' hab with b hab IH
          · simp
          · rw [Finset.sum_Ico_succ_top hab, ← IH]
            ring
        exact hgen j N hjN
      rw [htel]
      have hterm : ∀ i ∈ Finset.Ico j N,
          r (i + 1) - r i ≤ (k : ℝ) / (Qsel (j + 1) : ℝ) * ((1 : ℝ) / 2) ^ (i - j) := by
        intro i hi
        have hij : j ≤ i := (Finset.mem_Ico.mp hi).1
        have hi1 : 1 ≤ i := by omega
        have hinc := (increment_bounds k i hi1).2
        have hQ : (Qsel (i + 1) : ℝ) ≥ (Qsel (j + 1) : ℝ) * (2 : ℝ) ^ (i - j) := by
          -- Q_{i+1} ≥ Q_{j+1}·2^{i-j} by iterating doubling
          have hqj1pos : 0 < (Qsel (j + 1) : ℝ) := by
            exact_mod_cast Qsel_pos (j + 1) (by omega)
          have hgen : ∀ m, (Qsel (j + 1 + m) : ℝ) ≥ (Qsel (j + 1) : ℝ) * (2 : ℝ) ^ m := by
            intro m
            induction m with
            | zero => simp
            | succ m ih =>
              have hd := Qsel_double (j + 1 + m) (by omega)
              have hidx : j + 1 + m + 1 = j + 1 + (m + 1) := by ring
              rw [hidx] at hd
              have hd' : (2 : ℝ) * (Qsel (j + 1 + m) : ℝ) ≤ (Qsel (j + 1 + (m + 1)) : ℝ) := by
                exact_mod_cast hd
              have hpow : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by ring
              rw [hpow]
              have hpos : 0 ≤ (Qsel (j + 1) : ℝ) * (2 : ℝ) ^ m := by positivity
              nlinarith
          have := hgen (i - j)
          have hidx : j + 1 + (i - j) = i + 1 := by omega
          rw [hidx] at this
          exact this
        have hfrac : (k : ℝ) / (Qsel (i + 1) : ℝ)
            ≤ (k : ℝ) / ((Qsel (j + 1) : ℝ) * (2 : ℝ) ^ (i - j)) := by
          apply div_le_div_of_nonneg_left (by positivity) _ hQ
          have : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
          positivity
        have heq : (k : ℝ) / ((Qsel (j + 1) : ℝ) * (2 : ℝ) ^ (i - j))
            = (k : ℝ) / (Qsel (j + 1) : ℝ) * ((1 : ℝ) / 2) ^ (i - j) := by
          have hpow : ((1 : ℝ) / 2) ^ (i - j) = 1 / (2 : ℝ) ^ (i - j) := by
            rw [one_div, inv_pow]
            <;> field_simp
          rw [hpow]
          field_simp
          <;> ring
        have hinc' : r (i + 1) - r i ≤ (k : ℝ) / (Qsel (i + 1) : ℝ) := by
          simpa [r] using hinc
        linarith
      calc ∑ i ∈ Finset.Ico j N, (r (i + 1) - r i)
          ≤ ∑ i ∈ Finset.Ico j N,
              ((k : ℝ) / (Qsel (j + 1) : ℝ) * ((1 : ℝ) / 2) ^ (i - j)) :=
            Finset.sum_le_sum hterm
        _ = (k : ℝ) / (Qsel (j + 1) : ℝ) *
            ∑ i ∈ Finset.Ico j N, ((1 : ℝ) / 2) ^ (i - j) := by rw [Finset.mul_sum]
        _ ≤ (k : ℝ) / (Qsel (j + 1) : ℝ) * 2 := by
            have hqj1pos : 0 < (Qsel (j + 1) : ℝ) := by
              exact_mod_cast Qsel_pos (j + 1) (by omega)
            have hcoeff : 0 ≤ (k : ℝ) / (Qsel (j + 1) : ℝ) := by positivity
            have hsum : ∑ i ∈ Finset.Ico j N, ((1 : ℝ) / 2) ^ (i - j) ≤ 2 := by
              have hsub : ∑ i ∈ Finset.Ico j N, ((1 : ℝ) / 2) ^ (i - j)
                  = ∑ m ∈ Finset.range (N - j), ((1 : ℝ) / 2) ^ m := by
                rw [Finset.sum_Ico_eq_sum_range]
                <;> simp
              rw [hsub]
              apply sum_geometric_two_le
            nlinarith
        _ = 2 * (k : ℝ) / (Qsel (j + 1) : ℝ) := by ring
    -- take limit N → ∞
    have hlim' : Tendsto (fun N => r N - r j) atTop (nhds (xOf k - r j)) :=
      hlim.sub tendsto_const_nhds
    have hev : ∀ᶠ N in atTop, r N - r j ≤ 2 * (k : ℝ) / (Qsel (j + 1) : ℝ) := by
      apply Filter.eventually_atTop.mpr
      refine ⟨j, fun N hN => hpartial N hN⟩
    exact le_of_tendsto hlim' hev
  constructor
  · -- 0 ≤ Q_j·xOf - M_j
    have hmono : r j ≤ xOf k := by
      apply le_ciSup (ratio_bddAbove k) j
    have : (Qsel j : ℝ) * xOf k - (Mk k j : ℝ)
        = (Qsel j : ℝ) * (xOf k - r j) := by
      simp [r]
      <;> field_simp [hqj.ne']
      <;> ring
    rw [this]
    apply mul_nonneg (le_of_lt hqj)
    linarith
  · -- Q_j·xOf - M_j ≤ 2k·Q_j/Q_{j+1}
    have : (Qsel j : ℝ) * xOf k - (Mk k j : ℝ)
        = (Qsel j : ℝ) * (xOf k - r j) := by
      simp [r]
      <;> field_simp [hqj.ne']
      <;> ring
    rw [this]
    have hqj1 : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
    calc (Qsel j : ℝ) * (xOf k - r j)
        ≤ (Qsel j : ℝ) * (2 * (k : ℝ) / (Qsel (j + 1) : ℝ)) := by
          gcongr
      _ = 2 * (k : ℝ) * (Qsel j : ℝ) / (Qsel (j + 1) : ℝ) := by ring

/-- The residual Q_j·xOf k - M_j tends to 0. -/
lemma residual_tendsto_zero (k : ℕ) :
    Tendsto (fun j => (Qsel j : ℝ) * xOf k - (Mk k j : ℝ)) atTop (nhds 0) := by
  have hbound : ∀ᶠ j in atTop,
      |(Qsel j : ℝ) * xOf k - (Mk k j : ℝ)| ≤ 2 * (k : ℝ) / (4 * (j : ℝ) + 2) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨2, fun j hj => ?_⟩
    have hj1 : 1 ≤ j := by omega
    have hr := residual_bound k j hj1
    have hnn : 0 ≤ (Qsel j : ℝ) * xOf k - (Mk k j : ℝ) := hr.1
    rw [abs_of_nonneg hnn]
    have h1 : (Qsel j : ℝ) * xOf k - (Mk k j : ℝ)
        ≤ 2 * (k : ℝ) * (Qsel j : ℝ) / (Qsel (j + 1) : ℝ) := hr.2
    have h2 : 2 * (k : ℝ) * (Qsel j : ℝ) / (Qsel (j + 1) : ℝ) ≤ 2 * (k : ℝ) / (4 * (j : ℝ) + 2) := by
      have hq := Qsel_rec j hj
      have hq' : (Qsel (j + 1) : ℝ) = (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by
        exact_mod_cast hq
      have hqj : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj1
      have hqj1 : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
      have hden : (Qsel (j + 1) : ℝ) ≥ (4 * (j : ℝ) + 2) * (Qsel j : ℝ) := by
        rw [hq']
        have : 0 ≤ (Qsel (j - 1) : ℝ) := by
          have : 1 ≤ j - 1 := by omega
          exact le_of_lt (by exact_mod_cast Qsel_pos (j - 1) this)
        linarith
      have h4j2 : 0 < (4 * (j : ℝ) + 2) := by positivity
      calc 2 * (k : ℝ) * (Qsel j : ℝ) / (Qsel (j + 1) : ℝ)
          ≤ 2 * (k : ℝ) * (Qsel j : ℝ) / ((4 * (j : ℝ) + 2) * (Qsel j : ℝ)) := by
            gcongr
        _ = 2 * (k : ℝ) / (4 * (j : ℝ) + 2) := by
            field_simp [hqj.ne', h4j2.ne']
            <;> ring
    linarith
  have hzero : Tendsto (fun j : ℕ => 2 * (k : ℝ) / (4 * (j : ℝ) + 2)) atTop (nhds 0) := by
    have hden : Tendsto (fun j : ℕ => (4 * (j : ℝ) + 2)) atTop atTop := by
      have hnat : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop (R := ℝ)
      have h4 : Tendsto (fun j : ℕ => (4 : ℝ) * (j : ℝ)) atTop atTop :=
        hnat.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
      apply tendsto_atTop_mono' _ _ h4
      apply Eventually.of_forall
      intro j
      linarith
    exact tendsto_const_nhds.div_atTop hden
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hbound' : ∀ᶠ j : ℕ in atTop, 2 * (k : ℝ) / (4 * (j : ℝ) + 2) < ε := by
    have := (Metric.tendsto_nhds.mp hzero) ε hε
    filter_upwards [this] with j hj
    have hnn : 0 ≤ 2 * (k : ℝ) / (4 * (j : ℝ) + 2) := by positivity
    have hj' : dist (2 * (k : ℝ) / (4 * (j : ℝ) + 2)) 0 < ε := hj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hj'
    exact hj'
  have hnn_ev : ∀ᶠ j : ℕ in atTop, 0 ≤ (Qsel j : ℝ) * xOf k - (Mk k j : ℝ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨1, fun j hj => (residual_bound k j hj).1⟩
  filter_upwards [hbound, hbound', hnn_ev] with j hj1 hj2 hj3
  have hgoal : dist ((Qsel j : ℝ) * xOf k - (Mk k j : ℝ)) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hj3]
    have hj1' : (Qsel j : ℝ) * xOf k - (Mk k j : ℝ) ≤ 2 * (k : ℝ) / (4 * (j : ℝ) + 2) := by
      rwa [abs_of_nonneg hj3] at hj1
    linarith
  exact hgoal

/-- Eventually M_j is the nearest integer to Q_j·xOf k. -/
lemma eventually_nearest (k : ℕ) :
    ∀ᶠ j in atTop, round ((Qsel j : ℝ) * xOf k) = Mk k j := by
  have hres := residual_tendsto_zero k
  have hsmall : ∀ᶠ j in atTop, |(Qsel j : ℝ) * xOf k - (Mk k j : ℝ)| < 1 / 2 := by
    have := (Metric.tendsto_nhds.mp hres) (1 / 2) (by norm_num)
    filter_upwards [this] with j hj
    simpa [Real.dist_eq, abs_sub_comm] using hj
  filter_upwards [hsmall] with j hj
  have hround : round ((Qsel j : ℝ) * xOf k) = Mk k j := by
    rw [round_eq_iff, Set.mem_Ico]
    have h1 : (Qsel j : ℝ) * xOf k - (Mk k j : ℝ) < 1 / 2 := by
      linarith [abs_lt.mp hj]
    have h2 : -(1 / 2) < (Qsel j : ℝ) * xOf k - (Mk k j : ℝ) := by
      linarith [abs_lt.mp hj]
    constructor <;> linarith
  exact hround

/-! ## Lemma 5: S(x) finite ⇒ 4·S(x) is a nonnegative integer -/

/-- The defect of xOf k is eventually constantly k. -/
lemma defect_xOf_eventually (k : ℕ) :
    ∀ᶠ j in atTop, defect (xOf k) j = (k : ℤ) := by
  have hnear := eventually_nearest k
  have h1 : ∃ N, ∀ i ≥ N, round ((Qsel i : ℝ) * xOf k) = Mk k i :=
    Filter.eventually_atTop.mp hnear
  rcases h1 with ⟨N, hN⟩
  apply Filter.eventually_atTop.mpr
  refine ⟨max N 2 + 1, fun j hj => ?_⟩
  have hj2 : 2 ≤ j := by omega
  have hjN : N ≤ j := by omega
  have hj1N : N ≤ j - 1 := by omega
  have hj1N' : N ≤ j + 1 := by omega
  have hround_j : round ((Qsel j : ℝ) * xOf k) = Mk k j := hN j hjN
  have hround_j1 : round ((Qsel (j - 1) : ℝ) * xOf k) = Mk k (j - 1) := hN (j - 1) hj1N
  have hround_jp1 : round ((Qsel (j + 1) : ℝ) * xOf k) = Mk k (j + 1) := hN (j + 1) hj1N'
  simp only [defect, hround_j, hround_j1, hround_jp1]
  have hm := Mk_rec k j hj2
  linarith

/-! ## Lemma 5: S(x) finite ⇒ 4·S(x) is a nonnegative integer -/

/-- If j‖Q_j x‖ is eventually bounded, then 4·SReal(x) is a nonnegative integer.
This is the formalized Lemma 5 (elementary bounded form; see report for relation to limsup). -/
lemma lemma5_four_S_integer (x : ℝ) (C : ℝ)
    (hC : ∀ᶠ j : ℕ in atTop, (j : ℝ) * distInt ((Qsel j : ℝ) * x) ≤ C) :
    ∃ k : ℕ, 4 * SReal x = (k : ℝ) := by
  -- |eps x j| = distInt(Q_j x)
  have heps_abs : ∀ j : ℕ, |eps x j| = distInt ((Qsel j : ℝ) * x) := by
    intro j
    rfl
  -- j·|eps_j| ≤ C eventually
  have hC' : ∀ᶠ j : ℕ in atTop, (j : ℝ) * |eps x j| ≤ C := by
    filter_upwards [hC] with j hj
    rw [heps_abs]
    exact hj
  -- eps_j → 0 (since |eps_j| ≤ C/j for j ≥ 1, and distInt ≤ 1/2)
  have heps_zero : Tendsto (eps x) atTop (nhds 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    -- for j large, j·|eps_j| ≤ C so |eps_j| ≤ C/j < ε
    have hC'' : ∃ N : ℕ, ∀ j ≥ N, (j : ℝ) * |eps x j| ≤ C := Filter.eventually_atTop.mp hC'
    rcases hC'' with ⟨N, hN⟩
    -- choose j ≥ max N 1 and C/j < ε
    have harch : ∃ M : ℕ, C / ε < M := exists_nat_gt (C / ε)
    rcases harch with ⟨M, hM⟩
    apply Filter.eventually_atTop.mpr
    refine ⟨max N (max M 1), fun j hj => ?_⟩
    have hjN : N ≤ j := by omega
    have hjM : M ≤ j := by omega
    have hj1 : 1 ≤ j := by omega
    have hjpos : 0 < (j : ℝ) := by positivity
    have h1 : (j : ℝ) * |eps x j| ≤ C := hN j hjN
    have h2 : |eps x j| ≤ C / (j : ℝ) := by
      rw [le_div_iff₀ hjpos]
      linarith
    have h3 : C / (j : ℝ) < ε := by
      have hjM' : (M : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjM
      have hM' : C / ε < (M : ℝ) := by exact_mod_cast hM
      have hεpos : 0 < ε := hε
      have hCε : C / ε < (j : ℝ) := by linarith
      rw [div_lt_iff₀ hjpos]
      have : C < ε * (j : ℝ) := by
        calc C = (C / ε) * ε := by field_simp [hεpos.ne']
          _ < (j : ℝ) * ε := by gcongr
          _ = ε * (j : ℝ) := by ring
      linarith
    have hdist : dist (eps x j) 0 < ε := by
      rw [Real.dist_eq, sub_zero]
      linarith [abs_nonneg (eps x j)]
    exact hdist
  -- RHS = 2eps_j + eps_{j-1} - eps_{j+1} → 0
  have hRHS : Tendsto (fun j : ℕ => 2 * eps x j + eps x (j - 1) - eps x (j + 1))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun j : ℕ => (2 : ℝ) * eps x j) atTop (nhds 0) := by
      have := heps_zero.const_mul (2 : ℝ)
      convert this using 1 <;> ring
    have h2 : Tendsto (fun j : ℕ => eps x (j - 1)) atTop (nhds 0) :=
      heps_zero.comp (tendsto_sub_atTop_nat 1)
    have h3 : Tendsto (fun j : ℕ => eps x (j + 1)) atTop (nhds 0) :=
      heps_zero.comp (tendsto_add_atTop_nat 1)
    have := (h1.add h2).sub h3
    simpa using this
  -- D_j - 4j eps_j → 0
  have hdiff : Tendsto (fun j : ℕ => (defect x j : ℝ) - 4 * (j : ℝ) * eps x j)
      atTop (nhds 0) := by
    have hident : ∀ᶠ j : ℕ in atTop,
        (defect x j : ℝ) - 4 * (j : ℝ) * eps x j
          = 2 * eps x j + eps x (j - 1) - eps x (j + 1) := by
      apply Filter.eventually_atTop.mpr
      refine ⟨2, fun j hj => defect_identity x j hj⟩
    exact hRHS.congr' (EventuallyEq.symm hident)
  -- 4j|eps_j| bounded (≤ 4C eventually); D_j bounded integer
  have h4eps_bdd : ∀ᶠ j : ℕ in atTop, 4 * (j : ℝ) * |eps x j| ≤ 4 * C := by
    filter_upwards [hC'] with j hj
    have : 4 * (j : ℝ) * |eps x j| = 4 * ((j : ℝ) * |eps x j|) := by ring
    rw [this]
    linarith
  -- |D_j| - 4j|eps_j| → 0 (reverse triangle + hdiff)
  have habs_diff : Tendsto (fun j : ℕ => |(defect x j : ℝ)| - 4 * (j : ℝ) * |eps x j|)
      atTop (nhds 0) := by
    have htri : ∀ j : ℕ, abs (abs (defect x j : ℝ) - 4 * (j : ℝ) * abs (eps x j))
        ≤ abs ((defect x j : ℝ) - 4 * (j : ℝ) * eps x j) := by
      intro j
      have := abs_abs_sub_abs_le (defect x j : ℝ) (4 * (j : ℝ) * eps x j)
      have habs : abs (4 * (j : ℝ) * eps x j) = 4 * (j : ℝ) * abs (eps x j) := by
        simp [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (4 : ℝ) * (j : ℝ))]
      convert this using 1
      <;> simp [habs]
    have hconv : Tendsto (fun j : ℕ => |(defect x j : ℝ) - 4 * (j : ℝ) * eps x j|)
        atTop (nhds 0) := by
      have := hdiff
      have := tendsto_iff_dist_tendsto_zero.mp this
      have heq : (fun j : ℕ => dist ((defect x j : ℝ) - 4 * (j : ℝ) * eps x j) 0)
          = (fun j : ℕ => |(defect x j : ℝ) - 4 * (j : ℝ) * eps x j|) := by
        funext j; simp [Real.dist_eq, abs_sub_comm]
      rw [heq] at this
      exact this
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have := (Metric.tendsto_nhds.mp hconv) ε hε
    filter_upwards [this] with j hj
    have h1 : abs (abs (defect x j : ℝ) - 4 * (j : ℝ) * abs (eps x j)) ≤
        abs ((defect x j : ℝ) - 4 * (j : ℝ) * eps x j) := htri j
    have h2 : abs ((defect x j : ℝ) - 4 * (j : ℝ) * eps x j) < ε := by
      simpa [Real.dist_eq, abs_sub_comm] using hj
    have h3 : abs (abs (defect x j : ℝ) - 4 * (j : ℝ) * abs (eps x j)) < ε := by linarith
    simpa [Real.dist_eq, abs_sub_comm] using h3
  -- D_j bounded integer: |D_j| ≤ 4C + 1 eventually
  have hD_bdd : ∃ B : ℕ, ∀ j, |defect x j| ≤ B := by
    classical
    -- |D_j| ≤ 4C + 1 eventually
    have h1 : ∃ N1 : ℕ, ∀ j ≥ N1, 4 * (j : ℝ) * |eps x j| ≤ 4 * C :=
      Filter.eventually_atTop.mp h4eps_bdd
    rcases h1 with ⟨N1, hN1⟩
    have h2 : ∃ N2 : ℕ, ∀ j ≥ N2, |(defect x j : ℝ) - 4 * (j : ℝ) * eps x j| ≤ 1 := by
      have := (Metric.tendsto_nhds.mp hdiff) 1 (by norm_num)
      have heq : ∀ᶠ j : ℕ in atTop, |(defect x j : ℝ) - 4 * (j : ℝ) * eps x j| ≤ 1 := by
        filter_upwards [this] with j hj
        have : dist ((defect x j : ℝ) - 4 * (j : ℝ) * eps x j) 0 < 1 := hj
        rw [Real.dist_eq, sub_zero] at this
        linarith [abs_nonneg ((defect x j : ℝ) - 4 * (j : ℝ) * eps x j)]
      exact Filter.eventually_atTop.mp heq
    rcases h2 with ⟨N2, hN2⟩
    set N := max N1 N2 with hNdef
    have hbound_large : ∀ j : ℕ, N ≤ j → |(defect x j : ℝ)| ≤ 4 * C + 1 := by
      intro j hj
      have hj1 : N1 ≤ j := by omega
      have hj2 : N2 ≤ j := by omega
      have h4 : 4 * (j : ℝ) * |eps x j| ≤ 4 * C := hN1 j hj1
      have hdiff' : |(defect x j : ℝ) - 4 * (j : ℝ) * eps x j| ≤ 1 := hN2 j hj2
      have habs : |4 * (j : ℝ) * eps x j| = 4 * (j : ℝ) * |eps x j| := by
        simp [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (4 : ℝ) * (j : ℝ))]
      have htri : |(defect x j : ℝ)| ≤ |4 * (j : ℝ) * eps x j| +
          |(defect x j : ℝ) - 4 * (j : ℝ) * eps x j| := by
        have h1 : 4 * (j : ℝ) * eps x j + ((defect x j : ℝ) - 4 * (j : ℝ) * eps x j)
            = (defect x j : ℝ) := by ring
        have := abs_add_le (4 * (j : ℝ) * eps x j) ((defect x j : ℝ) - 4 * (j : ℝ) * eps x j)
        rw [h1] at this
        exact this
      linarith
    -- global bound: max over finite initial segment + ceil(4C+1)
    set B0 : ℕ := Nat.ceil (4 * C + 1) with hB0def
    set finMax : ℕ := (Finset.range N).sup (fun j => Int.natAbs (defect x j)) with hfinMax
    refine ⟨max B0 finMax, fun j => ?_⟩
    by_cases hjN : N ≤ j
    · have h1 : |(defect x j : ℝ)| ≤ 4 * C + 1 := hbound_large j hjN
      have h2 : (Int.natAbs (defect x j) : ℝ) ≤ 4 * C + 1 := by
        have hcast : (Int.natAbs (defect x j) : ℝ) = |(defect x j : ℝ)| := by
          rw [← Int.cast_abs, Int.abs_eq_natAbs]
          <;> simp
        rw [hcast]; exact h1
      have h3 : Int.natAbs (defect x j) ≤ B0 := by
        rw [hB0def]
        have hceil : (4 * C + 1 : ℝ) ≤ (Nat.ceil (4 * C + 1) : ℝ) := by
          exact_mod_cast Nat.le_ceil (4 * C + 1)
        have : (Int.natAbs (defect x j) : ℝ) ≤ (Nat.ceil (4 * C + 1) : ℝ) := by
          linarith
        exact_mod_cast this
      have : Int.natAbs (defect x j) ≤ max B0 finMax := by
        apply le_max_of_le_left; exact h3
      have hcast : |defect x j| = (Int.natAbs (defect x j) : ℤ) := by
        rw [Int.abs_eq_natAbs]
      rw [hcast]
      exact_mod_cast this
    · have hjN' : j < N := by omega
      have hmem : j ∈ Finset.range N := Finset.mem_range.mpr hjN'
      have hle : Int.natAbs (defect x j) ≤ finMax := by
        rw [hfinMax]
        apply Finset.le_sup hmem
      have : Int.natAbs (defect x j) ≤ max B0 finMax := by
        apply le_max_of_le_right; exact hle
      have hcast : |defect x j| = (Int.natAbs (defect x j) : ℤ) := by
        rw [Int.abs_eq_natAbs]
      rw [hcast]
      exact_mod_cast this
  rcases hD_bdd with ⟨B, hB⟩
  -- apply integer_limsup_identify to a_j = defect x j, b_j = 4j|eps_j|
  have hidentify := integer_limsup_identify (defect x) (fun j => 4 * (j : ℝ) * |eps x j|) B hB
    (fun j => by positivity) habs_diff
  rcases hidentify with ⟨m, hm1, hm2⟩
  -- hm2 : limsup (4j|eps_j|) = m; SReal x = limsup j|eps_j| = m/4
  refine ⟨m, ?_⟩
  have hSReal : SReal x = limsup (fun j : ℕ => (j : ℝ) * |eps x j|) atTop := by
    simp only [SReal]
    apply limsup_congr
    apply Eventually.of_forall
    intro j
    rw [heps_abs]
  -- use: limsup (4·f) = 4·limsup f for bounded f (via ENNReal bridge)
  have hf_bdd : IsBoundedUnder (· ≤ ·) atTop (fun j : ℕ => (j : ℝ) * |eps x j|) := by
    apply isBoundedUnder_of_eventually_le (a := C)
    filter_upwards [hC'] with j hj
    exact hj
  have hf_cobdd : IsCoboundedUnder (· ≤ ·) atTop (fun j : ℕ => (j : ℝ) * |eps x j|) :=
    IsCoboundedUnder.of_frequently_ge
      (Frequently.of_forall (fun j => by positivity))
  -- Bridge to ENNReal to use limsup_const_mul, then back.
  set f := (fun j : ℕ => (j : ℝ) * |eps x j|) with hfdef
  have hf_nn : ∀ j, 0 ≤ f j := fun j => by positivity
  have h4 : limsup (fun j : ℕ => 4 * (j : ℝ) * |eps x j|) atTop
      = 4 * limsup f atTop := by
    have heq : (fun j : ℕ => 4 * (j : ℝ) * |eps x j|) = (fun j => (4 : ℝ) * f j) := by
      funext j; simp [f]; ring
    rw [heq]
    -- use ENNReal.ofReal_limsup bridge
    have h4f_bdd : IsBoundedUnder (· ≤ ·) atTop (fun j : ℕ => (4 : ℝ) * f j) := by
      apply isBoundedUnder_of_eventually_le (a := 4 * C)
      filter_upwards [hC'] with j hj
      have : (4 : ℝ) * f j = 4 * ((j : ℝ) * |eps x j|) := by simp [f]
      linarith
    have h4f_cobdd : IsCoboundedUnder (· ≤ ·) atTop (fun j : ℕ => (4 : ℝ) * f j) :=
      IsCoboundedUnder.of_frequently_ge
        (Frequently.of_forall (fun j => by positivity))
    have hL : ENNReal.ofReal (limsup (fun j => (4 : ℝ) * f j) atTop)
        = limsup (fun j => ENNReal.ofReal ((4 : ℝ) * f j)) atTop :=
      ENNReal.ofReal_limsup (h₁ := h4f_cobdd) (h₂ := h4f_bdd)
    have hR : ENNReal.ofReal (limsup f atTop) = limsup (fun j => ENNReal.ofReal (f j)) atTop :=
      ENNReal.ofReal_limsup (h₁ := hf_cobdd) (h₂ := hf_bdd)
    have hmul : limsup (fun j => ENNReal.ofReal ((4 : ℝ) * f j)) atTop
        = (4 : ENNReal) * limsup (fun j => ENNReal.ofReal (f j)) atTop := by
      have heq' : (fun j => ENNReal.ofReal ((4 : ℝ) * f j))
          = (fun j => (4 : ENNReal) * ENNReal.ofReal (f j)) := by
        funext j
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (4 : ℝ))]
        <;> simp
      rw [heq']
      exact ENNReal.limsup_const_mul_of_ne_top (by norm_num : (4 : ENNReal) ≠ ⊤)
    have hinj : ENNReal.ofReal (limsup (fun j => (4 : ℝ) * f j) atTop)
        = ENNReal.ofReal (4 * limsup f atTop) := by
      rw [hL, hmul, ← hR]
      <;> simp [ENNReal.ofReal_mul (by positivity : 0 ≤ (4 : ℝ))]
    have hnn1 : 0 ≤ limsup (fun j => (4 : ℝ) * f j) atTop :=
      le_limsup_of_frequently_le (a := 0) (hu_le := h4f_bdd)
        (Frequently.of_forall (fun j => by positivity))
    have hnn2 : 0 ≤ 4 * limsup f atTop := by
      apply mul_nonneg (by norm_num)
      exact le_limsup_of_frequently_le (a := 0) (hu_le := hf_bdd)
        (Frequently.of_forall (fun j => hf_nn j))
    exact (ENNReal.ofReal_eq_ofReal_iff hnn1 hnn2).mp hinj
  rw [hSReal, ← h4, hm2]
  <;> ring

/-! ## Theorem 6: the finite spectrum is exactly {k/4} -/

/-- eps xOf k j equals the residual Q_j·xOf - M_j eventually. -/
lemma eps_xOf_eq_residual (k : ℕ) :
    ∀ᶠ j in atTop, eps (xOf k) j = (Qsel j : ℝ) * xOf k - (Mk k j : ℝ) := by
  filter_upwards [eventually_nearest k] with j hj
  simp only [eps, hj]
  <;> push_cast <;> ring

/-- eps xOf k → 0. -/
lemma eps_xOf_tendsto_zero (k : ℕ) :
    Tendsto (eps (xOf k)) atTop (nhds 0) := by
  have := (residual_tendsto_zero k).congr' (EventuallyEq.symm (eps_xOf_eq_residual k))
  exact this

/-- 4·j·eps xOf k j → k. -/
lemma four_j_eps_xOf_tendsto (k : ℕ) :
    Tendsto (fun j : ℕ => 4 * (j : ℝ) * eps (xOf k) j) atTop (nhds (k : ℝ)) := by
  have hdef := defect_xOf_eventually k
  have heps := eps_xOf_tendsto_zero k
  have hRHS : Tendsto (fun j : ℕ => 2 * eps (xOf k) j + eps (xOf k) (j - 1)
      - eps (xOf k) (j + 1)) atTop (nhds 0) := by
    have h1 : Tendsto (fun j : ℕ => (2 : ℝ) * eps (xOf k) j) atTop (nhds 0) := by
      have := heps.const_mul (2 : ℝ)
      convert this using 1 <;> ring
    have h2 : Tendsto (fun j : ℕ => eps (xOf k) (j - 1)) atTop (nhds 0) :=
      heps.comp (tendsto_sub_atTop_nat 1)
    have h3 : Tendsto (fun j : ℕ => eps (xOf k) (j + 1)) atTop (nhds 0) :=
      heps.comp (tendsto_add_atTop_nat 1)
    have := (h1.add h2).sub h3
    simpa using this
  -- D_j - 4j eps_j = RHS → 0, and D_j = k eventually, so k - 4j eps_j → 0
  have hdiff : Tendsto (fun j : ℕ => (defect (xOf k) j : ℝ) - 4 * (j : ℝ) * eps (xOf k) j)
      atTop (nhds 0) := by
    have hident : ∀ᶠ j in atTop,
        (defect (xOf k) j : ℝ) - 4 * (j : ℝ) * eps (xOf k) j
          = 2 * eps (xOf k) j + eps (xOf k) (j - 1) - eps (xOf k) (j + 1) := by
      apply Filter.eventually_atTop.mpr
      refine ⟨2, fun j hj => defect_identity (xOf k) j hj⟩
    exact hRHS.congr' (EventuallyEq.symm hident)
  have hD : Tendsto (fun j : ℕ => (defect (xOf k) j : ℝ)) atTop (nhds (k : ℝ)) := by
    have : (fun j : ℕ => (defect (xOf k) j : ℝ)) =ᶠ[atTop] (fun _ => (k : ℝ)) := by
      filter_upwards [hdef] with j hj
      simp [hj]
    exact tendsto_const_nhds.congr' (EventuallyEq.symm this)
  have h4eps : Tendsto (fun j : ℕ => 4 * (j : ℝ) * eps (xOf k) j) atTop (nhds (k : ℝ)) := by
    have := hD.sub hdiff
    -- this : (D_j - (D_j - 4j eps_j)) → k - 0 = k
    have heq : (fun j : ℕ => (defect (xOf k) j : ℝ)
        - ((defect (xOf k) j : ℝ) - 4 * (j : ℝ) * eps (xOf k) j))
        = (fun j : ℕ => 4 * (j : ℝ) * eps (xOf k) j) := by
      funext j; ring
    rw [heq] at this
    simpa using this
  exact h4eps

/-- Theorem 6(a): for each k, j‖Q_j·xOf k‖ → k/4. -/
lemma theorem6_a (k : ℕ) :
    Tendsto (fun j : ℕ => (j : ℝ) * distInt ((Qsel j : ℝ) * xOf k)) atTop
      (nhds ((k : ℝ) / 4)) := by
  -- get N such that for j ≥ N: nearest, eps = residual, residual ≥ 0
  have hnear := eventually_nearest k
  have hres := eps_xOf_eq_residual k
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hnear
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hres
  set N := max N1 (max N2 1) with hNdef
  have hdist : ∀ᶠ j in atTop,
      distInt ((Qsel j : ℝ) * xOf k) = eps (xOf k) j := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N, fun j hj => ?_⟩
    have hj1 : N1 ≤ j := by omega
    have hj2 : N2 ≤ j := by omega
    have hj1' : 1 ≤ j := by omega
    have hround := hN1 j hj1
    have heps := hN2 j hj2
    have hnn : 0 ≤ (Qsel j : ℝ) * xOf k - (Mk k j : ℝ) := (residual_bound k j hj1').1
    simp only [distInt, hround, heps]
    rw [abs_of_nonneg hnn]
    <;> push_cast <;> ring
  have heq : (fun j : ℕ => (j : ℝ) * distInt ((Qsel j : ℝ) * xOf k))
      =ᶠ[atTop] (fun j : ℕ => (j : ℝ) * eps (xOf k) j) := by
    filter_upwards [hdist] with j hj
    rw [hj]
  have h4 := four_j_eps_xOf_tendsto k
  have hjeps : Tendsto (fun j : ℕ => (j : ℝ) * eps (xOf k) j) atTop (nhds ((k : ℝ) / 4)) := by
    have := h4.const_mul (1 / 4 : ℝ)
    have heq' : (fun j : ℕ => (1 / 4 : ℝ) * (4 * (j : ℝ) * eps (xOf k) j))
        = (fun j : ℕ => (j : ℝ) * eps (xOf k) j) := by
      funext j; ring
    rw [heq'] at this
    convert this using 1
    ring
  exact hjeps.congr' (EventuallyEq.symm heq)

/-- Theorem 6(b): if S(x) is finite, then S(x) = k/4 for some k. -/
lemma theorem6_b (x : ℝ) (hfin : S x ≠ ⊤) :
    ∃ k : ℕ, S x = ENNReal.ofReal ((k : ℝ) / 4) := by
  set g := (fun j : ℕ => (j : ℝ) * distInt ((Qsel j : ℝ) * x)) with hgdef
  have hg_nn : ∀ j, 0 ≤ g j := fun j => by
    apply mul_nonneg (by positivity) (distInt_nonneg _)
  have hS : S x = limsup (fun j => ENNReal.ofReal (g j)) atTop := rfl
  -- finite limsup ⇒ bounded by some NNReal C
  have hlt : limsup (fun j => ENNReal.ofReal (g j)) atTop < ⊤ := by
    rw [← hS]; exact lt_top_iff_ne_top.mpr hfin
  obtain ⟨C, hCeq, _⟩ := ENNReal.lt_iff_exists_coe.mp hlt
  -- limsup = C ⇒ eventually ofReal g ≤ C + 1 (use limsup_le_iff generic)
  have hC_le : limsup (fun j => ENNReal.ofReal (g j)) atTop ≤ (C : ENNReal) := by
    rw [hCeq]
  have hev : ∀ᶠ j : ℕ in atTop, ENNReal.ofReal (g j) ≤ (C : ENNReal) + 1 := by
    have hC_lt : (C : ENNReal) < (C : ENNReal) + 1 := by
      apply ENNReal.lt_add_right (by simp) (by norm_num : (1 : ENNReal) ≠ 0)
    have hlim : limsup (fun j => ENNReal.ofReal (g j)) atTop < (C : ENNReal) + 1 :=
      lt_of_le_of_lt hC_le hC_lt
    exact (eventually_lt_of_limsup_lt hlim (by isBoundedDefault)).mono (fun j hj => le_of_lt hj)
  have hbounded : ∃ B : ℝ, ∀ᶠ j : ℕ in atTop, g j ≤ B := by
    refine ⟨(C : ℝ) + 1, ?_⟩
    filter_upwards [hev] with j hj
    have hcoe : ((C : ENNReal) + 1 : ENNReal) = ENNReal.ofReal ((C : ℝ) + 1) := by
      simp [ENNReal.ofReal_add (by positivity : 0 ≤ (C : ℝ)) (by norm_num : 0 ≤ (1 : ℝ))]
    rw [hcoe] at hj
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (C : ℝ) + 1)).mp hj
  rcases hbounded with ⟨B, hB⟩
  have hlemma := lemma5_four_S_integer x B hB
  rcases hlemma with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hg_bdd : IsBoundedUnder (· ≤ ·) atTop g :=
    isBoundedUnder_of_eventually_le hB
  have hg_cobdd : IsCoboundedUnder (· ≤ ·) atTop g :=
    IsCoboundedUnder.of_frequently_ge (Frequently.of_forall hg_nn)
  have hSReal : S x = ENNReal.ofReal (SReal x) := by
    change limsup (fun j : ℕ => ENNReal.ofReal ((j : ℝ) * distInt ((Qsel j : ℝ) * x))) atTop
      = ENNReal.ofReal (limsup (fun j : ℕ => (j : ℝ) * distInt ((Qsel j : ℝ) * x)) atTop)
    rw [ENNReal.ofReal_limsup (h₁ := hg_cobdd) (h₂ := hg_bdd)]
  have hSReal_val : SReal x = (k : ℝ) / 4 := by
    have : 4 * SReal x = (k : ℝ) := hk
    linarith
  rw [hSReal, hSReal_val]

end CSpectrum

/-! ## Axiom audit -/
#print axioms CSpectrum.Qsel_pos
#print axioms CSpectrum.Psel_rec
#print axioms CSpectrum.Qsel_rec
#print axioms CSpectrum.sel_determinant
#print axioms CSpectrum.Psel_odd
#print axioms CSpectrum.Qsel_odd
#print axioms CSpectrum.Qsel_double
#print axioms CSpectrum.Qsel_succ_coprime
#print axioms CSpectrum.Qsel_tendsto_atTop
#print axioms CSpectrum.defect_identity
#print axioms CSpectrum.bounded_int_frequently
#print axioms CSpectrum.bounded_int_limsup_nat
#print axioms CSpectrum.integer_limsup_identify
#print axioms CSpectrum.Mk_rec
#print axioms CSpectrum.W_rec
#print axioms CSpectrum.W_bounds
#print axioms CSpectrum.increment_bounds
#print axioms CSpectrum.ratio_mono
#print axioms CSpectrum.ratio_bddAbove
#print axioms CSpectrum.ratio_tendsto_xOf
#print axioms CSpectrum.residual_bound
#print axioms CSpectrum.residual_tendsto_zero
#print axioms CSpectrum.eventually_nearest
#print axioms CSpectrum.defect_xOf_eventually
#print axioms CSpectrum.eps_xOf_tendsto_zero
#print axioms CSpectrum.four_j_eps_xOf_tendsto
#print axioms CSpectrum.theorem6_a
#print axioms CSpectrum.lemma5_four_S_integer
#print axioms CSpectrum.theorem6_b