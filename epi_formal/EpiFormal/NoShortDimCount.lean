import Mathlib
import EpiFormal.WindowMobiusCount
import EpiFormal.WindowMobiusPartial
import EpiFormal.WindowWindowBounds
import EpiFormal.WindowMainBound

open ArithmeticFunction Finset Real
open scoped BigOperators

namespace NoShortDim

/-!
# Coprime count in the no-short-dim rectangle (paper2 §7, thm:no-short-dim phase 1, L06).

Paper anchor: tex L2779–2785 (`R'_R := [0.34R,0.35R] × [0.12R,0.13R]`,
`≫ R² ≫ j^{2γ}`). This mirrors `WindowMobiusCount` (which handles the
0.34–0.36 × 0.20–0.22 rectangle) with the new constants, reusing its generic
lemmas (`nat_div_mono`, `countMultiples`, `intervalCount`,
`nat_div_cast_lower/upper`, `moebius_indicator`, `moebius_partial`,
`harmonic_le`, `one_div_le_log_pred`) and the `log 10^6 < 18` bridge
(`WindowMobiusCount.log106_lt`).

Main result: `coprime_count_geS : R^2/100000 ≤ copCountS R` for `R ≥ 10^6`.
The constant is not optimal; downstream only needs `≫ R²` (absorbed into the
mass-distribution `O(j)` by taking logs).
-/

/-! ## 1. The new rectangle. -/

/-- Left end of the `m`-range. -/
noncomputable def MloS (R : ℝ) : ℕ := ⌊0.34 * R⌋₊ + 1

/-- Right end of the `m`-range. -/
noncomputable def MhiS (R : ℝ) : ℕ := ⌊0.35 * R⌋₊

/-- Left end of the `n`-range. -/
noncomputable def NloS (R : ℝ) : ℕ := ⌊0.12 * R⌋₊ + 1

/-- Right end of the `n`-range. -/
noncomputable def NhiS (R : ℝ) : ℕ := ⌊0.13 * R⌋₊

/-- Real widths. -/
noncomputable def W1S (R : ℝ) : ℝ := (MhiS R : ℝ) - (MloS R : ℝ) + 1

noncomputable def W2S (R : ℝ) : ℝ := (NhiS R : ℝ) - (NloS R : ℝ) + 1

/-- The integer rectangle. -/
noncomputable def boxS (R : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.Icc (MloS R) (MhiS R)) ×ˢ (Finset.Icc (NloS R) (NhiS R))

/-- Coprime pairs in the box. -/
noncomputable def copCountS (R : ℝ) : ℕ :=
  ((boxS R).filter (fun p => Nat.gcd p.1 p.2 = 1)).card

/-- Multiples of `d` in the `m`-interval. -/
noncomputable def AcountS (R : ℝ) (d : ℕ) : ℕ :=
  (((Finset.Icc (MloS R) (MhiS R)).filter (fun m => d ∣ m))).card

/-- Multiples of `d` in the `n`-interval. -/
noncomputable def BcountS (R : ℝ) (d : ℕ) : ℕ :=
  (((Finset.Icc (NloS R) (NhiS R)).filter (fun n => d ∣ n))).card

theorem boxS_mem_iff (R : ℝ) (p : ℕ × ℕ) :
    p ∈ boxS R ↔
      p.1 ∈ Finset.Icc (MloS R) (MhiS R) ∧ p.2 ∈ Finset.Icc (NloS R) (NhiS R) := by
  unfold boxS
  exact Finset.mem_product

theorem MloS_ge_one (R : ℝ) : 1 ≤ MloS R := by
  have : MloS R = ⌊0.34 * R⌋₊ + 1 := rfl
  omega

theorem NloS_ge_one (R : ℝ) : 1 ≤ NloS R := by
  have : NloS R = ⌊0.12 * R⌋₊ + 1 := rfl
  omega

/-- Every box coordinate is positive. -/
theorem boxS_mem_pos (R : ℝ) (p : ℕ × ℕ) (hp : p ∈ boxS R) :
    1 ≤ p.1 ∧ 1 ≤ p.2 := by
  have h1 := MloS_ge_one R
  have h2 := NloS_ge_one R
  rw [boxS_mem_iff] at hp
  simp only [Finset.mem_Icc] at hp
  omega

/-- The box is nonempty for `R ≥ 300` (width `0.01R ≥ 3` absorbs the floors). -/
theorem boxS_nonempty (R : ℝ) (hR : 300 ≤ R) :
    MloS R ≤ MhiS R ∧ NloS R ≤ NhiS R := by
  have e1 : ((⌊0.34 * R⌋₊ : ℕ) : ℝ) ≤ 0.34 * R :=
    Nat.floor_le (by nlinarith [hR])
  have e2 : (0.35 : ℝ) * R < ((⌊0.35 * R⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have e3 : ((⌊0.12 * R⌋₊ : ℕ) : ℝ) ≤ 0.12 * R :=
    Nat.floor_le (by nlinarith [hR])
  have e4 : (0.13 : ℝ) * R < ((⌊0.13 * R⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have cM : ((MloS R : ℕ) : ℝ) ≤ ((MhiS R : ℕ) : ℝ) := by
    have hMlo : MloS R = ⌊0.34 * R⌋₊ + 1 := rfl
    have hMhi : MhiS R = ⌊0.35 * R⌋₊ := rfl
    rw [hMlo, hMhi]
    push_cast
    nlinarith [e1, e2, hR]
  have cN : ((NloS R : ℕ) : ℝ) ≤ ((NhiS R : ℕ) : ℝ) := by
    have hNlo : NloS R = ⌊0.12 * R⌋₊ + 1 := rfl
    have hNhi : NhiS R = ⌊0.13 * R⌋₊ := rfl
    rw [hNlo, hNhi]
    push_cast
    nlinarith [e3, e4, hR]
  exact ⟨Nat.cast_le.mp cM, Nat.cast_le.mp cN⟩

/-! ## 2. Width bounds. -/

theorem W1S_lo (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) : 0.009 * R ≤ W1S R := by
  have e1 : ((⌊0.35 * R⌋₊ : ℕ) : ℝ) ≤ 0.35 * R := Nat.floor_le (by nlinarith [hR])
  have e2 : 0.35 * R < ((⌊0.35 * R⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have e3 : ((⌊0.34 * R⌋₊ : ℕ) : ℝ) ≤ 0.34 * R := Nat.floor_le (by nlinarith [hR])
  unfold W1S MhiS MloS
  push_cast
  nlinarith [e1, e2, e3, hR]

theorem W1S_hi (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) : W1S R ≤ 0.011 * R := by
  have e1 : ((⌊0.35 * R⌋₊ : ℕ) : ℝ) ≤ 0.35 * R := Nat.floor_le (by nlinarith [hR])
  have e3 : 0.34 * R < ((⌊0.34 * R⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  unfold W1S MhiS MloS
  push_cast
  nlinarith [e1, e3, hR]

theorem W2S_lo (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) : 0.009 * R ≤ W2S R := by
  have e1 : ((⌊0.13 * R⌋₊ : ℕ) : ℝ) ≤ 0.13 * R := Nat.floor_le (by nlinarith [hR])
  have e2 : 0.13 * R < ((⌊0.13 * R⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have e3 : ((⌊0.12 * R⌋₊ : ℕ) : ℝ) ≤ 0.12 * R := Nat.floor_le (by nlinarith [hR])
  unfold W2S NhiS NloS
  push_cast
  nlinarith [e1, e2, e3, hR]

theorem W2S_hi (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) : W2S R ≤ 0.011 * R := by
  have e1 : ((⌊0.13 * R⌋₊ : ℕ) : ℝ) ≤ 0.13 * R := Nat.floor_le (by nlinarith [hR])
  have e3 : 0.12 * R < ((⌊0.12 * R⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  unfold W2S NhiS NloS
  push_cast
  nlinarith [e1, e3, hR]

/-! ## 3. Multiples of `d` in each window. -/

/-- `W1S R = ↑(MhiS R) - ↑(MloS R - 1)`. -/
theorem W1S_eq_cast (R : ℝ) :
    W1S R = (MhiS R : ℝ) - ((MloS R - 1 : ℕ) : ℝ) := by
  have h : ((MloS R - 1 : ℕ) : ℝ) = (MloS R : ℝ) - 1 := by
    simpa using Nat.cast_sub (MloS_ge_one R) (m := 1)
  unfold W1S
  rw [h]
  ring

/-- Lower bound: `m`-window multiple count within `1` below `W1S R / d`. -/
theorem AcountS_lo (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) (d : ℕ) (hd : 1 ≤ d) :
    W1S R / (d : ℝ) - 1 ≤ (AcountS R d : ℝ) := by
  obtain ⟨hMle, -⟩ := boxS_nonempty R (by linarith : (300 : ℝ) ≤ R)
  have hd0 : 0 < d := by omega
  have hdle : (MloS R - 1) / d ≤ MhiS R / d :=
    WindowMobiusCount.nat_div_mono (by omega)
  have hAcard : AcountS R d = MhiS R / d - (MloS R - 1) / d := by
    unfold AcountS
    exact WindowMobiusCount.intervalCount (MloS R) (MhiS R) d hd (MloS_ge_one R)
  have hAc : (AcountS R d : ℝ) =
      ((MhiS R / d : ℕ) : ℝ) - (((MloS R - 1) / d : ℕ) : ℝ) := by
    rw [hAcard]
    exact Nat.cast_sub hdle
  have low1 : (MhiS R : ℝ) / (d : ℝ) - 1 ≤ ((MhiS R / d : ℕ) : ℝ) :=
    WindowMobiusCount.nat_div_cast_lower _ _ hd0
  have up2 : (((MloS R - 1) / d : ℕ) : ℝ) ≤ ((MloS R - 1 : ℕ) : ℝ) / (d : ℝ) :=
    WindowMobiusCount.nat_div_cast_upper _ _ hd0
  have heq : W1S R / (d : ℝ) - 1 =
      (MhiS R : ℝ) / (d : ℝ) - ((MloS R - 1 : ℕ) : ℝ) / (d : ℝ) - 1 := by
    rw [W1S_eq_cast R, sub_div]
  rw [hAc, heq]
  linarith

/-- Upper bound: `m`-window multiple count within `1` above `W1S R / d`. -/
theorem AcountS_hi (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) (d : ℕ) (hd : 1 ≤ d) :
    (AcountS R d : ℝ) ≤ W1S R / (d : ℝ) + 1 := by
  obtain ⟨hMle, -⟩ := boxS_nonempty R (by linarith : (300 : ℝ) ≤ R)
  have hd0 : 0 < d := by omega
  have hdle : (MloS R - 1) / d ≤ MhiS R / d :=
    WindowMobiusCount.nat_div_mono (by omega)
  have hAcard : AcountS R d = MhiS R / d - (MloS R - 1) / d := by
    unfold AcountS
    exact WindowMobiusCount.intervalCount (MloS R) (MhiS R) d hd (MloS_ge_one R)
  have hAc : (AcountS R d : ℝ) =
      ((MhiS R / d : ℕ) : ℝ) - (((MloS R - 1) / d : ℕ) : ℝ) := by
    rw [hAcard]
    exact Nat.cast_sub hdle
  have up1 : ((MhiS R / d : ℕ) : ℝ) ≤ (MhiS R : ℝ) / (d : ℝ) :=
    WindowMobiusCount.nat_div_cast_upper _ _ hd0
  have low2 : ((MloS R - 1 : ℕ) : ℝ) / (d : ℝ) - 1 ≤
      (((MloS R - 1) / d : ℕ) : ℝ) :=
    WindowMobiusCount.nat_div_cast_lower _ _ hd0
  have heq : W1S R / (d : ℝ) + 1 =
      (MhiS R : ℝ) / (d : ℝ) - ((MloS R - 1 : ℕ) : ℝ) / (d : ℝ) + 1 := by
    rw [W1S_eq_cast R, sub_div]
  rw [hAc, heq]
  linarith

/-- `W2S R = ↑(NhiS R) - ↑(NloS R - 1)`. -/
theorem W2S_eq_cast (R : ℝ) :
    W2S R = (NhiS R : ℝ) - ((NloS R - 1 : ℕ) : ℝ) := by
  have h : ((NloS R - 1 : ℕ) : ℝ) = (NloS R : ℝ) - 1 := by
    simpa using Nat.cast_sub (NloS_ge_one R) (m := 1)
  unfold W2S
  rw [h]
  ring

/-- Lower bound: `n`-window multiple count within `1` below `W2S R / d`. -/
theorem BcountS_lo (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) (d : ℕ) (hd : 1 ≤ d) :
    W2S R / (d : ℝ) - 1 ≤ (BcountS R d : ℝ) := by
  obtain ⟨-, hNle⟩ := boxS_nonempty R (by linarith : (300 : ℝ) ≤ R)
  have hd0 : 0 < d := by omega
  have hdle : (NloS R - 1) / d ≤ NhiS R / d :=
    WindowMobiusCount.nat_div_mono (by omega)
  have hBcard : BcountS R d = NhiS R / d - (NloS R - 1) / d := by
    unfold BcountS
    exact WindowMobiusCount.intervalCount (NloS R) (NhiS R) d hd (NloS_ge_one R)
  have hBc : (BcountS R d : ℝ) =
      ((NhiS R / d : ℕ) : ℝ) - (((NloS R - 1) / d : ℕ) : ℝ) := by
    rw [hBcard]
    exact Nat.cast_sub hdle
  have low1 : (NhiS R : ℝ) / (d : ℝ) - 1 ≤ ((NhiS R / d : ℕ) : ℝ) :=
    WindowMobiusCount.nat_div_cast_lower _ _ hd0
  have up2 : (((NloS R - 1) / d : ℕ) : ℝ) ≤ ((NloS R - 1 : ℕ) : ℝ) / (d : ℝ) :=
    WindowMobiusCount.nat_div_cast_upper _ _ hd0
  have heq : W2S R / (d : ℝ) - 1 =
      (NhiS R : ℝ) / (d : ℝ) - ((NloS R - 1 : ℕ) : ℝ) / (d : ℝ) - 1 := by
    rw [W2S_eq_cast R, sub_div]
  rw [hBc, heq]
  linarith

/-- Upper bound: `n`-window multiple count within `1` above `W2S R / d`. -/
theorem BcountS_hi (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) (d : ℕ) (hd : 1 ≤ d) :
    (BcountS R d : ℝ) ≤ W2S R / (d : ℝ) + 1 := by
  obtain ⟨-, hNle⟩ := boxS_nonempty R (by linarith : (300 : ℝ) ≤ R)
  have hd0 : 0 < d := by omega
  have hdle : (NloS R - 1) / d ≤ NhiS R / d :=
    WindowMobiusCount.nat_div_mono (by omega)
  have hBcard : BcountS R d = NhiS R / d - (NloS R - 1) / d := by
    unfold BcountS
    exact WindowMobiusCount.intervalCount (NloS R) (NhiS R) d hd (NloS_ge_one R)
  have hBc : (BcountS R d : ℝ) =
      ((NhiS R / d : ℕ) : ℝ) - (((NloS R - 1) / d : ℕ) : ℝ) := by
    rw [hBcard]
    exact Nat.cast_sub hdle
  have up1 : ((NhiS R / d : ℕ) : ℝ) ≤ (NhiS R : ℝ) / (d : ℝ) :=
    WindowMobiusCount.nat_div_cast_upper _ _ hd0
  have low2 : ((NloS R - 1 : ℕ) : ℝ) / (d : ℝ) - 1 ≤
      (((NloS R - 1) / d : ℕ) : ℝ) :=
    WindowMobiusCount.nat_div_cast_lower _ _ hd0
  have heq : W2S R / (d : ℝ) + 1 =
      (NhiS R : ℝ) / (d : ℝ) - ((NloS R - 1 : ℕ) : ℝ) / (d : ℝ) + 1 := by
    rw [W2S_eq_cast R, sub_div]
  rw [hBc, heq]
  linarith

/-! ## 4. Exact coprime-count identity. -/

/-- Membership in `divisors (gcd)` unfolds to joint divisibility. -/
theorem keyS_mem_iff (R : ℝ) (d : ℕ) (p : ℕ × ℕ) (hp : p ∈ boxS R) :
    (d ∈ (Nat.gcd p.1 p.2).divisors) ↔ (d ∣ p.1 ∧ d ∣ p.2) := by
  obtain ⟨h1, h2⟩ := boxS_mem_pos R p hp
  rw [Nat.mem_divisors]
  constructor
  · rintro ⟨hdvd, -⟩
    exact ⟨dvd_trans hdvd (Nat.gcd_dvd_left _ _),
      dvd_trans hdvd (Nat.gcd_dvd_right _ _)⟩
  · rintro ⟨h1d, h2d⟩
    refine ⟨Nat.dvd_gcd h1d h2d, ?_⟩
    have hg : 0 < Nat.gcd p.1 p.2 :=
      Nat.gcd_pos_of_pos_left _ (by omega)
    omega

/-- The filtered box product splits as a product of filtered intervals. -/
theorem prodS_filter_eq (R : ℝ) (d : ℕ) :
    ((boxS R).filter (fun p => d ∈ (Nat.gcd p.1 p.2).divisors)) =
      (((Finset.Icc (MloS R) (MhiS R)).filter (fun m => d ∣ m)) ×ˢ
        (((Finset.Icc (NloS R) (NhiS R)).filter (fun n => d ∣ n)))) := by
  have h1 : ((boxS R).filter (fun p => d ∈ (Nat.gcd p.1 p.2).divisors)) =
      ((boxS R).filter (fun p => d ∣ p.1 ∧ d ∣ p.2)) := by
    apply Finset.filter_congr
    intro x hx
    exact keyS_mem_iff R d x hx
  rw [h1]
  unfold boxS
  rw [Finset.filter_product]

/-- Exact identity: the coprime count is `∑ μ(d) · A(d) · B(d)`. -/
theorem coprimeS_count_eq (R : ℝ) :
    (copCountS R : ℤ) = ∑ d ∈ Finset.Icc 1 (MhiS R),
      (moebius d : ℤ) * ((AcountS R d : ℤ) * (BcountS R d : ℤ)) := by
  have step1 : (copCountS R : ℤ) = ∑ p ∈ boxS R,
      (if Nat.gcd p.1 p.2 = 1 then (1:ℤ) else 0) :=
    (Finset.sum_boole _ _).symm
  have step2 : ∀ p ∈ boxS R, (if Nat.gcd p.1 p.2 = 1 then (1:ℤ) else 0) =
      ∑ d ∈ Finset.Icc 1 (MhiS R),
        (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0) := by
    intro p hp
    obtain ⟨h1, h2⟩ := boxS_mem_pos R p hp
    have hsub : (Nat.gcd p.1 p.2).divisors ⊆ Finset.Icc 1 (MhiS R) := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      have hdm : d ∣ p.1 := dvd_trans hd.1 (Nat.gcd_dvd_left _ _)
      have hle : d ≤ p.1 := Nat.le_of_dvd (by omega) hdm
      have hMhi : p.1 ≤ MhiS R := by
        have hmem := (boxS_mem_iff R p).mp hp
        exact (Finset.mem_Icc.mp hmem.1).2
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdm (by omega)
      simp only [Finset.mem_Icc]
      exact ⟨hd1, le_trans hle hMhi⟩
    have h0 : ∀ d ∈ Finset.Icc 1 (MhiS R),
        d ∉ (Nat.gcd p.1 p.2).divisors →
          (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0) = 0 :=
      fun d _ hnd => by simp [hnd]
    have hbase : (∑ d ∈ Finset.Icc 1 (MhiS R),
          (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0)) =
        (∑ d ∈ (Nat.gcd p.1 p.2).divisors, (moebius d : ℤ)) := by
      calc (∑ d ∈ Finset.Icc 1 (MhiS R),
              (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0))
          = (∑ d ∈ (Nat.gcd p.1 p.2).divisors,
              (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0)) :=
            (Finset.sum_subset hsub h0).symm
        _ = (∑ d ∈ (Nat.gcd p.1 p.2).divisors, (moebius d : ℤ)) := by
            apply Finset.sum_congr rfl
            intro d hd
            simp [hd]
    have hmi := WindowMobiusCount.moebius_indicator (Nat.gcd p.1 p.2)
    rw [← hbase] at hmi
    exact hmi.symm
  calc (copCountS R : ℤ)
      = ∑ p ∈ boxS R, (if Nat.gcd p.1 p.2 = 1 then (1:ℤ) else 0) := step1
    _ = ∑ p ∈ boxS R, ∑ d ∈ Finset.Icc 1 (MhiS R),
          (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0) :=
        Finset.sum_congr rfl (fun p hp => step2 p hp)
    _ = ∑ d ∈ Finset.Icc 1 (MhiS R), ∑ p ∈ boxS R,
          (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 (MhiS R),
          (moebius d : ℤ) * ((AcountS R d : ℤ) * (BcountS R d : ℤ)) := by
        apply Finset.sum_congr rfl
        intro d _
        have hfac : (∑ p ∈ boxS R, (if d ∈ (Nat.gcd p.1 p.2).divisors
            then (moebius d : ℤ) else 0)) =
            (moebius d : ℤ) * ∑ p ∈ boxS R,
              (if d ∈ (Nat.gcd p.1 p.2).divisors then (1:ℤ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          by_cases h : d ∈ (Nat.gcd p.1 p.2).divisors
          · simp [h]
          · simp [h]
        rw [hfac]
        have hcard : ((AcountS R d : ℤ) * (BcountS R d : ℤ)) =
            ∑ p ∈ boxS R, (if d ∈ (Nat.gcd p.1 p.2).divisors then (1:ℤ) else 0) := by
          have hcardN : AcountS R d * BcountS R d =
              #((boxS R).filter (fun p => d ∈ (Nat.gcd p.1 p.2).divisors)) := by
            unfold AcountS BcountS
            rw [← Finset.card_product, ← prodS_filter_eq R d]
          have hboole : (∑ p ∈ boxS R,
              (if d ∈ (Nat.gcd p.1 p.2).divisors then (1:ℤ) else 0)) =
              ((((boxS R).filter
                (fun p => d ∈ (Nat.gcd p.1 p.2).divisors)).card) : ℤ) :=
            Finset.sum_boole _ _
          rw [← Nat.cast_mul, hcardN, hboole]
        rw [hcard]

/-! ## 5. Log and error bounds. -/

/-- Log of the window top. -/
theorem logMhiS_le (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) :
    Real.log ((MhiS R : ℕ) : ℝ) ≤ ((MhiS R : ℕ) : ℝ) / 10 ^ 6 + 17 := by
  have hMhi1 : 1 ≤ MhiS R :=
    le_trans (MloS_ge_one R) (boxS_nonempty R (by linarith : (300 : ℝ) ≤ R)).1
  have hMhipos : (0 : ℝ) < ((MhiS R : ℕ) : ℝ) := by
    have hN : 0 < MhiS R := by omega
    exact_mod_cast hN
  have h106ne : ((10 : ℝ) ^ 6) ≠ 0 := by norm_num
  have hdiv : Real.log (((MhiS R : ℕ) : ℝ) / 10 ^ 6) =
      Real.log ((MhiS R : ℕ) : ℝ) - Real.log ((10 : ℝ) ^ 6) :=
    Real.log_div (ne_of_gt hMhipos) h106ne
  have hle : Real.log (((MhiS R : ℕ) : ℝ) / 10 ^ 6) ≤
      ((MhiS R : ℕ) : ℝ) / 10 ^ 6 - 1 :=
    Real.log_le_sub_one_of_pos
      (div_pos hMhipos (by norm_num : (0 : ℝ) < 10 ^ 6))
  calc Real.log ((MhiS R : ℕ) : ℝ)
      = Real.log (((MhiS R : ℕ) : ℝ) / 10 ^ 6) + Real.log ((10 : ℝ) ^ 6) := by
        rw [hdiv]; ring
    _ ≤ (((MhiS R : ℕ) : ℝ) / 10 ^ 6 - 1) + 18 :=
        add_le_add hle WindowMobiusCount.log106_lt.le
    _ = ((MhiS R : ℕ) : ℝ) / 10 ^ 6 + 17 := by ring

/-- Per-`d` transfer-operator error. -/
theorem errS_bound (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) (d : ℕ) (hd : 1 ≤ d) :
    |((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2| ≤
      (0.022 * R) * (1 / (d : ℝ)) + 1 := by
  have hR0 : (0 : ℝ) ≤ R := by linarith [hR]
  have hdrpos : (0 : ℝ) < (d : ℝ) := by
    have hdN : 0 < d := by omega
    exact_mod_cast hdN
  have hW1nn : 0 ≤ W1S R := by
    have h := W1S_lo R hR
    have hR0' : (0 : ℝ) ≤ 0.009 * R := mul_nonneg (by norm_num) hR0
    linarith [h]
  have hW2nn : 0 ≤ W2S R := by
    have h := W2S_lo R hR
    have hR0' : (0 : ℝ) ≤ 0.009 * R := mul_nonneg (by norm_num) hR0
    linarith [h]
  have hAnn : (0 : ℝ) ≤ (AcountS R d : ℝ) := Nat.cast_nonneg _
  have hBnn : (0 : ℝ) ≤ (BcountS R d : ℝ) := Nat.cast_nonneg _
  have ha_nn : (0 : ℝ) ≤ W1S R / (d : ℝ) := div_nonneg hW1nn (le_of_lt hdrpos)
  have hb_nn : (0 : ℝ) ≤ W2S R / (d : ℝ) := div_nonneg hW2nn (le_of_lt hdrpos)
  have hA1 : |(AcountS R d : ℝ) - W1S R / (d : ℝ)| ≤ 1 := by
    have hlo := AcountS_lo R hR d hd
    have hhi := AcountS_hi R hR d hd
    exact abs_le.mpr ⟨by linarith [hlo], by linarith [hhi]⟩
  have hB1 : |(BcountS R d : ℝ) - W2S R / (d : ℝ)| ≤ 1 := by
    have hlo := BcountS_lo R hR d hd
    have hhi := BcountS_hi R hR d hd
    exact abs_le.mpr ⟨by linarith [hlo], by linarith [hhi]⟩
  have hBub : (BcountS R d : ℝ) ≤ W2S R / (d : ℝ) + 1 := by
    linarith [BcountS_hi R hR d hd]
  have ha : W1S R / (d : ℝ) ≤ 0.011 * R / (d : ℝ) :=
    div_le_div_of_nonneg_right (W1S_hi R hR) (le_of_lt hdrpos)
  have hb : W2S R / (d : ℝ) ≤ 0.011 * R / (d : ℝ) :=
    div_le_div_of_nonneg_right (W2S_hi R hR) (le_of_lt hdrpos)
  have hadd : (0.011 * R) / (d : ℝ) + (0.011 * R) / (d : ℝ) =
      (0.022 * R) / (d : ℝ) := by
    rw [← add_div]
    congr 1
    ring
  have hmul0 : (0.022 * R) * (1 / (d : ℝ)) = (0.022 * R) / (d : ℝ) := by ring
  have e2 : (W1S R / (d : ℝ)) * (W2S R / (d : ℝ)) =
      (W1S R * W2S R) / (d : ℝ) ^ 2 := by
    rw [div_mul_div_comm, pow_two]
  have htri : |((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2| ≤
      1 * (BcountS R d : ℝ) + (W1S R / (d : ℝ)) * 1 := by
    have e12 : ((AcountS R d : ℝ) - W1S R / (d : ℝ)) * (BcountS R d : ℝ) +
        (W1S R / (d : ℝ)) * ((BcountS R d : ℝ) - W2S R / (d : ℝ)) =
        ((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R / (d : ℝ)) * (W2S R / (d : ℝ)) := by
      ring
    calc |((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2|
        = |(((AcountS R d : ℝ) - W1S R / (d : ℝ)) * (BcountS R d : ℝ) +
          (W1S R / (d : ℝ)) * ((BcountS R d : ℝ) - W2S R / (d : ℝ)))| := by
          rw [← e2, ← e12]
      _ ≤ |((AcountS R d : ℝ) - W1S R / (d : ℝ))| * |(BcountS R d : ℝ)| +
          |(W1S R / (d : ℝ))| * |((BcountS R d : ℝ) - W2S R / (d : ℝ))| := by
        have eX : |((AcountS R d : ℝ) - W1S R / (d : ℝ)) * (BcountS R d : ℝ)| =
            |((AcountS R d : ℝ) - W1S R / (d : ℝ))| * |(BcountS R d : ℝ)| := abs_mul _ _
        have eY : |(W1S R / (d : ℝ)) * ((BcountS R d : ℝ) - W2S R / (d : ℝ))| =
            |(W1S R / (d : ℝ))| * |((BcountS R d : ℝ) - W2S R / (d : ℝ))| := abs_mul _ _
        have hX1 := neg_abs_le (((AcountS R d : ℝ) - W1S R / (d : ℝ)) * (BcountS R d : ℝ))
        have hX2 := le_abs_self (((AcountS R d : ℝ) - W1S R / (d : ℝ)) * (BcountS R d : ℝ))
        have hY1 := neg_abs_le ((W1S R / (d : ℝ)) * ((BcountS R d : ℝ) - W2S R / (d : ℝ)))
        have hY2 := le_abs_self ((W1S R / (d : ℝ)) * ((BcountS R d : ℝ) - W2S R / (d : ℝ)))
        have hT : |(((AcountS R d : ℝ) - W1S R / (d : ℝ)) * (BcountS R d : ℝ) +
            (W1S R / (d : ℝ)) * ((BcountS R d : ℝ) - W2S R / (d : ℝ)))| ≤
            |((AcountS R d : ℝ) - W1S R / (d : ℝ)) * (BcountS R d : ℝ)| +
            |(W1S R / (d : ℝ)) * ((BcountS R d : ℝ) - W2S R / (d : ℝ))| :=
          abs_le.mpr ⟨by linarith [hX1, hY1], by linarith [hX2, hY2]⟩
        linarith [hT, eX, eY]
      _ = |((AcountS R d : ℝ) - W1S R / (d : ℝ))| * (BcountS R d : ℝ) +
          (W1S R / (d : ℝ)) * |((BcountS R d : ℝ) - W2S R / (d : ℝ))| := by
          rw [abs_of_nonneg hBnn, abs_of_nonneg ha_nn]
      _ ≤ 1 * (BcountS R d : ℝ) + (W1S R / (d : ℝ)) * 1 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hA1 hBnn
          · exact mul_le_mul_of_nonneg_left hB1 ha_nn
  have hfin : 1 * (BcountS R d : ℝ) + (W1S R / (d : ℝ)) * 1 ≤
      (0.022 * R) * (1 / (d : ℝ)) + 1 := by
    have h1 : (BcountS R d : ℝ) + W1S R / (d : ℝ) ≤
        (0.011 * R) / (d : ℝ) + (0.011 * R) / (d : ℝ) + 1 := by
      linarith [hBub, ha]
    linarith [h1, hadd, hmul0]
  linarith [htri, hfin]

/-- The new-rectangle count is at least `R²/100000`. -/
theorem coprimeS_count_ge (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) :
    R ^ 2 / 100000 ≤ ((copCountS R : ℕ) : ℝ) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith [hR]
  have hMhi1 : 1 ≤ MhiS R :=
    le_trans (MloS_ge_one R) (boxS_nonempty R (by linarith : (300 : ℝ) ≤ R)).1
  have hMhi_ub : ((MhiS R : ℕ) : ℝ) ≤ 0.35 * R :=
    Nat.floor_le (mul_nonneg (by norm_num) hR0)
  have hW1nn : 0 ≤ W1S R := by
    have h := W1S_lo R hR
    have hR0' : (0 : ℝ) ≤ 0.009 * R := mul_nonneg (by norm_num) hR0
    linarith [h]
  have hW2nn : 0 ≤ W2S R := by
    have h := W2S_lo R hR
    have hR0' : (0 : ℝ) ≤ 0.009 * R := mul_nonneg (by norm_num) hR0
    linarith [h]
  have hS : (359 / 900 : ℝ) ≤
      ∑ d ∈ Finset.Icc 1 (MhiS R), (moebius d : ℝ) / (d : ℝ) ^ 2 :=
    WindowMobiusCount.moebius_partial (MhiS R) hMhi1
  have hcast : ((copCountS R : ℝ)) = ∑ d ∈ Finset.Icc 1 (MhiS R),
      (moebius d : ℝ) * (((AcountS R d : ℝ)) * ((BcountS R d : ℝ))) := by
    exact_mod_cast coprimeS_count_eq R
  have hS2 : (W1S R * W2S R) *
      (∑ d ∈ Finset.Icc 1 (MhiS R), (moebius d : ℝ) / (d : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 (MhiS R),
        (moebius d : ℝ) * ((W1S R * W2S R) / (d : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hdiff : ((copCountS R : ℝ)) -
      (W1S R * W2S R) * (∑ d ∈ Finset.Icc 1 (MhiS R), (moebius d : ℝ) / (d : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 (MhiS R), (moebius d : ℝ) *
        (((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2) := by
    rw [hcast, hS2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hsum1 : ∑ _d ∈ Finset.Icc 1 (MhiS R), (1 : ℝ) = ((MhiS R : ℕ) : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have hHerr : |(∑ d ∈ Finset.Icc 1 (MhiS R), (moebius d : ℝ) *
      (((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2))| ≤
      (0.022 * R) * (∑ d ∈ Finset.Icc 1 (MhiS R), 1 / (d : ℝ)) + ((MhiS R : ℕ) : ℝ) := by
    have h1 : |∑ d ∈ Finset.Icc 1 (MhiS R), (moebius d : ℝ) *
        (((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2)| ≤
        ∑ d ∈ Finset.Icc 1 (MhiS R),
          |(moebius d : ℝ) *
            (((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ d ∈ Finset.Icc 1 (MhiS R),
        |(moebius d : ℝ) *
          (((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2)| ≤
        (0.022 * R) * (1 / (d : ℝ)) + 1 := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hmu : |(moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast abs_moebius_le_one (n := d)
      have herr := errS_bound R hR d hd1
      have e1 : |(moebius d : ℝ) *
          (((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2)| =
          |(moebius d : ℝ)| *
            |((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2| :=
        abs_mul _ _
      have e2 : |(moebius d : ℝ)| *
          |((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2| ≤
          1 * ((0.022 * R) * (1 / (d : ℝ)) + 1) := by
        have g1 : |(moebius d : ℝ)| *
            |((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2| ≤
            1 * |((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2| :=
          mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        have g2 : (1 : ℝ) *
            |((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2| ≤
            1 * ((0.022 * R) * (1 / (d : ℝ)) + 1) :=
          mul_le_mul_of_nonneg_left herr zero_le_one
        linarith [g1, g2, e1]
      calc |(moebius d : ℝ) *
            (((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2)|
          = |(moebius d : ℝ)| *
            |((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2| := abs_mul _ _
        _ ≤ 1 * ((0.022 * R) * (1 / (d : ℝ)) + 1) := e2
        _ = (0.022 * R) * (1 / (d : ℝ)) + 1 := by ring
    have h3 := Finset.sum_le_sum h2
    have h4 : (∑ d ∈ Finset.Icc 1 (MhiS R), ((0.022 * R) * (1 / (d : ℝ)) + 1)) =
        (0.022 * R) * (∑ d ∈ Finset.Icc 1 (MhiS R), 1 / (d : ℝ)) + ((MhiS R : ℕ) : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum1]
    linarith [h1, h3, h4]
  have hH : (∑ d ∈ Finset.Icc 1 (MhiS R), 1 / (d : ℝ)) ≤
      ((MhiS R : ℕ) : ℝ) / 10 ^ 6 + 18 := by
    have hbase := WindowMobiusCount.harmonic_le (MhiS R) hMhi1
    have hlog := logMhiS_le R hR
    have hMhi6 : ((MhiS R : ℕ) : ℝ) / 10 ^ 6 ≤ (0.35 * R) / 10 ^ 6 :=
      div_le_div_of_nonneg_right hMhi_ub (by norm_num : (0 : ℝ) ≤ 10 ^ 6)
    linarith [hbase, hlog, hMhi6]
  have hW12 : (0.009 * R) ^ 2 ≤ (W1S R) * (W2S R) := by
    have h1 : (0.009 * R) * (0.009 * R) ≤ (W1S R) * (0.009 * R) :=
      mul_le_mul_of_nonneg_right (W1S_lo R hR) (by positivity)
    have e2 : (W1S R) * (0.009 * R) ≤ (W1S R) * (W2S R) :=
      mul_le_mul_of_nonneg_left (W2S_lo R hR) hW1nn
    have e3 : (0.009 * R) ^ 2 = (0.009 * R) * (0.009 * R) := by ring
    linarith [h1, e2, e3]
  have hM2 : (0.009 * R) ^ 2 * (359 / 900 : ℝ) ≤
      (W1S R * W2S R) * (359 / 900 : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith [hW12]
  have hM3 : (W1S R * W2S R) * (359 / 900 : ℝ) ≤
      (W1S R * W2S R) * (∑ d ∈ Finset.Icc 1 (MhiS R), (moebius d : ℝ) / (d : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_left hS _
    apply mul_nonneg hW1nn hW2nn
  have hEfin : (0.022 * R) *
      (((0.35 * R) / 10 ^ 6 + 18)) + ((MhiS R : ℕ) : ℝ) ≤
      0.746 * R + 0.0000000077 * R ^ 2 := by
    have e1 : (0.022 * R) * (((0.35 * R) / 10 ^ 6 + 18)) =
        0.022 * R * ((0.35 * R) / 10 ^ 6) + 0.022 * R * 18 := by ring
    have e2 : (0.022 * R) * ((0.35 * R) / 10 ^ 6) ≤ 0.0000000077 * R ^ 2 := by
      have e2a : (0.022 * R) * ((0.35 * R) / 10 ^ 6) =
          (0.022 * 0.35 / 10 ^ 6) * (R * R) := by ring
      have e2b : (0.022 * 0.35 / 10 ^ 6 : ℝ) ≤ 0.0000000077 := by norm_num
      have e2c : (0.022 * 0.35 / 10 ^ 6) * (R * R) ≤
          0.0000000077 * (R * R) :=
        mul_le_mul_of_nonneg_right e2b (mul_nonneg hR0 hR0)
      have e2d : (0.0000000077 : ℝ) * (R * R) = 0.0000000077 * R ^ 2 := by ring
      linarith [e2a, e2c, e2d]
    have e3 : (0.022 * R) * 18 = 0.396 * R := by ring
    have hM : ((MhiS R : ℕ) : ℝ) ≤ 0.35 * R := hMhi_ub
    linarith [e1, e2, hM, e3]
  have hfin : R ^ 2 / 100000 ≤
      (0.009 * R) ^ 2 * (359 / 900 : ℝ) - (0.746 * R + 0.0000000077 * R ^ 2) := by
    have hbig : (10 ^ 6 : ℝ) ≤ R := hR
    have hRnn : (0 : ℝ) ≤ R := by linarith [hR]
    have hC : (0.0000223 : ℝ) ≤
        (0.009) ^ 2 * (359 / 900) - 1 / 100000 - 0.0000000077 := by norm_num
    have hP : (0 : ℝ) ≤ (R - 10 ^ 6) * R :=
      mul_nonneg (by linarith [hbig]) hRnn
    nlinarith [hbig, hRnn, hC, hP, sq_nonneg R]
  have hErrNeg : -((0.022 * R) *
      ((∑ d ∈ Finset.Icc 1 (MhiS R), 1 / (d : ℝ))) + ((MhiS R : ℕ) : ℝ)) ≤
      ((copCountS R : ℝ)) - (W1S R * W2S R) *
        (∑ d ∈ Finset.Icc 1 (MhiS R), (moebius d : ℝ) / (d : ℝ) ^ 2) := by
    have h1 := neg_le_neg hHerr
    have h2 := neg_abs_le (∑ d ∈ Finset.Icc 1 (MhiS R), (moebius d : ℝ) *
      (((AcountS R d : ℝ) * (BcountS R d : ℝ)) - (W1S R * W2S R) / (d : ℝ) ^ 2))
    linarith [h1, h2, hdiff]
  have hStep1 : (0.009 * R) ^ 2 * (359 / 900 : ℝ) - ((0.022 * R) *
      ((0.35 * R) / 10 ^ 6 + 18) + ((MhiS R : ℕ) : ℝ)) ≤ ((copCountS R : ℝ)) := by
    have eA : (0.009 * R) ^ 2 * (359 / 900 : ℝ) ≤
        (W1S R * W2S R) * (359 / 900 : ℝ) := hM2
    have eB : (W1S R * W2S R) * (359 / 900 : ℝ) ≤
        (W1S R * W2S R) *
          (∑ d ∈ Finset.Icc 1 (MhiS R), (moebius d : ℝ) / (d : ℝ) ^ 2) := hM3
    have eC : (W1S R * W2S R) *
        (∑ d ∈ Finset.Icc 1 (MhiS R), (moebius d : ℝ) / (d : ℝ) ^ 2) -
        ((0.022 * R) * ((0.35 * R) / 10 ^ 6 + 18) + ((MhiS R : ℕ) : ℝ)) ≤
        ((copCountS R : ℝ)) := by
      have hE1 : (0.022 * R) * (∑ d ∈ Finset.Icc 1 (MhiS R), 1 / (d : ℝ)) ≤
          (0.022 * R) * ((0.35 * R) / 10 ^ 6 + 18) := by
        apply mul_le_mul_of_nonneg_left _ _
        · have hH0 : (∑ d ∈ Finset.Icc 1 (MhiS R), 1 / (d : ℝ)) ≤
              ((MhiS R : ℕ) : ℝ) / 10 ^ 6 + 18 := by
            have hb := WindowMobiusCount.harmonic_le (MhiS R) hMhi1
            have hl := logMhiS_le R hR
            linarith [hb, hl]
          have hM0 : ((MhiS R : ℕ) : ℝ) / 10 ^ 6 ≤ (0.35 * R) / 10 ^ 6 :=
            div_le_div_of_nonneg_right hMhi_ub (by norm_num : (0 : ℝ) ≤ 10 ^ 6)
          linarith [hH0, hM0]
        · have hR0' : (0 : ℝ) ≤ 0.022 * R :=
            mul_nonneg (by norm_num) hR0
          linarith [hR0']
      have hE2 : (0.022 * R) * (∑ d ∈ Finset.Icc 1 (MhiS R), 1 / (d : ℝ)) +
          ((MhiS R : ℕ) : ℝ) ≤
          (0.022 * R) * ((0.35 * R) / 10 ^ 6 + 18) + ((MhiS R : ℕ) : ℝ) := by
        linarith [hE1]
      linarith [hErrNeg, hE2, hdiff]
    linarith [eA, eB, eC]
  have hStep2 : (0.009 * R) ^ 2 * (359 / 900 : ℝ) - (0.746 * R + 0.0000000077 * R ^ 2) ≤
      (0.009 * R) ^ 2 * (359 / 900 : ℝ) -
        ((0.022 * R) * ((0.35 * R) / 10 ^ 6 + 18) + ((MhiS R : ℕ) : ℝ)) := by
    linarith [hEfin]
  linarith [hStep1, hStep2, hfin]

#print axioms W1S_lo
#print axioms W1S_hi
#print axioms W2S_lo
#print axioms W2S_hi
#print axioms AcountS_lo
#print axioms AcountS_hi
#print axioms BcountS_lo
#print axioms BcountS_hi
#print axioms logMhiS_le
#print axioms errS_bound
#print axioms coprimeS_count_ge

end NoShortDim
