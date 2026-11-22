import Mathlib

open ArithmeticFunction Finset Real
open scoped BigOperators

namespace WindowMobiusCount

/-!
# Möbius coprime count in the Hermite window rectangle (paper2 §7, thm:windows)

Paper: `thm:windows` parity construction (paper L2444–L2465). For stage `j`,
with `T := H_{j+1}` and `R := T / u ≍ j`, the number of coprime integer pairs
in the rectangle `R_R = [0.34R, 0.36R] × [0.20R, 0.22R]` is `≫ R²`, proved via
Möbius inversion. This file formalizes the counting core with fully explicit
constants (no `O`-notation, no zeta values):

* `moebius_indicator`: `∑ d ∈ divisors g, μ d = [g = 1]` (from
  `moebius_mul_coe_zeta`).
* `coprime_count_eq`: the rectangle coprime count equals
  `∑ d, μ d · A d · B d` (exact, by swapping finite sums).
* `coprime_count_ge`: for `R ≥ 10^6`, the count is `≥ R² / 10000`.
  The main term uses `∑_{d ≤ D} μ d / d² ≥ 359/900` (first five terms minus an
  explicit tail); the error term uses an explicit harmonic bound.

What is NOT proved here (paper interfaces): the continuant-matrix identity
`t = mu + nv`, the disjointness of stopped cylinders, and the Frostman mass
distribution assembly (`dim ≥ b/2`). Those remain paper-side; the count proved
here is exactly the `≫ R²` input they consume.
-/

/-! ## 1. The window rectangle. -/

/-- Left end of the `m`-range: `⌊0.34R⌋ + 1 > 0.34R`. -/
noncomputable def Mlo (R : ℝ) : ℕ := ⌊0.34 * R⌋₊ + 1

/-- Right end of the `m`-range: `⌊0.36R⌋ ≤ 0.36R`. -/
noncomputable def Mhi (R : ℝ) : ℕ := ⌊0.36 * R⌋₊

/-- Left end of the `n`-range. -/
noncomputable def Nlo (R : ℝ) : ℕ := ⌊0.20 * R⌋₊ + 1

/-- Right end of the `n`-range. -/
noncomputable def Nhi (R : ℝ) : ℕ := ⌊0.22 * R⌋₊

/-- Real widths of the two ranges. -/
noncomputable def W1 (R : ℝ) : ℝ := (Mhi R : ℝ) - (Mlo R : ℝ) + 1

noncomputable def W2 (R : ℝ) : ℝ := (Nhi R : ℝ) - (Nlo R : ℝ) + 1

/-- The integer rectangle (paper L2447–L2449). -/
noncomputable def box (R : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.Icc (Mlo R) (Mhi R)) ×ˢ (Finset.Icc (Nlo R) (Nhi R))

/-- Coprime pairs in the box (`gcd = 1`, paper L2451–L2465). -/
noncomputable def copCount (R : ℝ) : ℕ :=
  ((box R).filter (fun p => Nat.gcd p.1 p.2 = 1)).card

/-- Multiples of `d` in the `m`-interval. -/
noncomputable def Acount (R : ℝ) (d : ℕ) : ℕ :=
  (((Finset.Icc (Mlo R) (Mhi R)).filter (fun m => d ∣ m))).card

/-- Multiples of `d` in the `n`-interval. -/
noncomputable def Bcount (R : ℝ) (d : ℕ) : ℕ :=
  (((Finset.Icc (Nlo R) (Nhi R)).filter (fun n => d ∣ n))).card

theorem box_mem_iff (R : ℝ) (p : ℕ × ℕ) :
    p ∈ box R ↔
      p.1 ∈ Finset.Icc (Mlo R) (Mhi R) ∧ p.2 ∈ Finset.Icc (Nlo R) (Nhi R) := by
  unfold box
  exact Finset.mem_product

theorem Mlo_ge_one (R : ℝ) : 1 ≤ Mlo R := by
  have : Mlo R = ⌊0.34 * R⌋₊ + 1 := rfl
  omega

theorem Nlo_ge_one (R : ℝ) : 1 ≤ Nlo R := by
  have : Nlo R = ⌊0.20 * R⌋₊ + 1 := rfl
  omega

/-- Every box coordinate is positive (needs no nonemptiness). -/
theorem box_mem_pos (R : ℝ) (p : ℕ × ℕ) (hp : p ∈ box R) :
    1 ≤ p.1 ∧ 1 ≤ p.2 := by
  have h1 := Mlo_ge_one R
  have h2 := Nlo_ge_one R
  rw [box_mem_iff] at hp
  simp only [Finset.mem_Icc] at hp
  omega

/-- The box is nonempty for `R ≥ 100` (width `0.02R ≥ 2` absorbs the floors). -/
theorem box_nonempty (R : ℝ) (hR : 100 ≤ R) :
    Mlo R ≤ Mhi R ∧ Nlo R ≤ Nhi R := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have e1 : ((⌊0.34 * R⌋₊ : ℕ) : ℝ) ≤ 0.34 * R :=
    Nat.floor_le (by nlinarith [hR])
  have e2 : (0.36 : ℝ) * R < ((⌊0.36 * R⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have e3 : ((⌊0.20 * R⌋₊ : ℕ) : ℝ) ≤ 0.20 * R :=
    Nat.floor_le (by nlinarith [hR])
  have e4 : (0.22 : ℝ) * R < ((⌊0.22 * R⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have cM : ((Mlo R : ℕ) : ℝ) ≤ ((Mhi R : ℕ) : ℝ) := by
    have hMlo : Mlo R = ⌊0.34 * R⌋₊ + 1 := rfl
    have hMhi : Mhi R = ⌊0.36 * R⌋₊ := rfl
    rw [hMlo, hMhi]
    push_cast
    nlinarith [e1, e2, hR]
  have cN : ((Nlo R : ℕ) : ℝ) ≤ ((Nhi R : ℕ) : ℝ) := by
    have hNlo : Nlo R = ⌊0.20 * R⌋₊ + 1 := rfl
    have hNhi : Nhi R = ⌊0.22 * R⌋₊ := rfl
    rw [hNlo, hNhi]
    push_cast
    nlinarith [e3, e4, hR]
  exact ⟨Nat.cast_le.mp cM, Nat.cast_le.mp cN⟩

/-! ## 2. Counting multiples in intervals. -/

/-- Nat division is monotone in the numerator. -/
theorem nat_div_mono {a b d : ℕ} (h : a ≤ b) : a / d ≤ b / d := by
  rcases eq_or_ne d 0 with rfl | hd0
  · simp
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    have e1 := Nat.div_add_mod a d
    have e2 := Nat.div_add_mod b d
    have r2 := Nat.mod_lt b hd
    have hle : a / d < b / d + 1 := by
      have key : (a / d) * d < (b / d + 1) * d := by
        have e1' : (a / d) * d + a % d = a := by
          rw [mul_comm]; exact e1
        have e2' : (b / d) * d + b % d = b := by
          rw [mul_comm]; exact e2
        have e3 : ((b / d + 1)) * d = (b / d) * d + d := by ring
        rw [e3]
        omega
      exact lt_of_mul_lt_mul_right key (Nat.zero_le _)
    omega

/-- Multiples of `d ≥ 1` in `[1, M]` are counted by `M / d`. -/
theorem countMultiples (M d : ℕ) (hd : 1 ≤ d) :
    (((Finset.Icc 1 M).filter (fun m => d ∣ m))).card = M / d := by
  have hd0 : d ≠ 0 := by omega
  have hinj : Function.Injective (fun k : ℕ => k * d) := by
    intro a b h
    simp only at h
    exact mul_right_cancel₀ hd0 h
  have himg : ((Finset.Icc 1 (M / d)).image (fun k : ℕ => k * d)) =
      ((Finset.Icc 1 M).filter (fun m => d ∣ m)) := by
    ext m
    simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_left d k⟩
      · calc (1 : ℕ) = 1 * 1 := by ring
          _ ≤ k * d :=
            Nat.mul_le_mul hk1 hd
      · have hkd : k * d ≤ M := by
          have hle := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hk2
          rwa [mul_comm k d] at hle ⊢
        exact hkd
    · rintro ⟨⟨h1, hM⟩, hdvd⟩
      obtain ⟨k, hk⟩ := hdvd
      refine ⟨k, ⟨?_, ?_⟩, ?_⟩
      · by_contra hcon
        push Not at hcon
        have hk0 : k = 0 := Nat.lt_one_iff.mp hcon
        subst hk0
        simp at hk
        omega
      · have hkd : k * d ≤ M := by
          rw [mul_comm]
          omega
        exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr hkd
      · rw [mul_comm]
        exact hk.symm
  rw [← himg, Finset.card_image_of_injective _ hinj, Nat.card_Icc,
    Nat.add_sub_cancel]

/-- Multiples of `d ≥ 1` in `[Mlo, Mhi]` (needs `1 ≤ Mlo`). -/
theorem intervalCount (Mlo Mhi d : ℕ) (hd : 1 ≤ d) (h1 : 1 ≤ Mlo) :
    (((Finset.Icc Mlo Mhi).filter (fun m => d ∣ m))).card =
      Mhi / d - (Mlo - 1) / d := by
  by_cases hle : Mlo ≤ Mhi
  · have hsub : (Finset.Icc 1 (Mlo - 1)) ⊆ (Finset.Icc 1 Mhi) := by
      intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    have hsubf : (((Finset.Icc 1 (Mlo - 1)).filter (fun m => d ∣ m))) ⊆
        (((Finset.Icc 1 Mhi).filter (fun m => d ∣ m))) := by
      intro m hm
      simp only [Finset.mem_filter] at hm ⊢
      exact ⟨hsub hm.1, hm.2⟩
    have hsd : ((Finset.Icc 1 Mhi) \ (Finset.Icc 1 (Mlo - 1))).filter
        (fun m => d ∣ m) =
        ((Finset.Icc 1 Mhi).filter (fun m => d ∣ m)) \
          (((Finset.Icc 1 (Mlo - 1)).filter (fun m => d ∣ m))) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      tauto
    have hset : (Finset.Icc 1 Mhi) \ (Finset.Icc 1 (Mlo - 1)) =
        (Finset.Icc Mlo Mhi) := by
      ext m
      simp only [Finset.mem_sdiff, Finset.mem_Icc]
      omega
    have hcard := Finset.card_sdiff_add_card_eq_card hsubf
    rw [← hsd, hset] at hcard
    rw [countMultiples _ _ hd, countMultiples _ _ hd] at hcard
    omega
  · have hempty : ((Finset.Icc Mlo Mhi).filter (fun m => d ∣ m)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm
      omega
    rw [hempty, Finset.card_empty]
    have hle' : Mhi ≤ Mlo - 1 := by omega
    have hdiv : Mhi / d ≤ (Mlo - 1) / d :=
      nat_div_mono hle'
    exact (Nat.sub_eq_zero_of_le hdiv).symm

/-! ## 3. Möbius indicator identity. -/

/-- `∑_{d | g} μ d = [g = 1]`, from `moebius_mul_coe_zeta`. -/
theorem moebius_indicator (g : ℕ) :
    (∑ d ∈ g.divisors, (moebius d : ℤ)) = if g = 1 then 1 else 0 := by
  have h : ((moebius * ↑zeta : ArithmeticFunction ℤ)) g =
      (∑ d ∈ g.divisors, (moebius d : ℤ)) :=
    ArithmeticFunction.coe_mul_zeta_apply
  rw [← h, ArithmeticFunction.moebius_mul_coe_zeta]
  by_cases hg : g = 1
  · subst hg
    rw [ArithmeticFunction.one_apply]
  · have h2 : (1 : ArithmeticFunction ℤ) g = 0 :=
      ArithmeticFunction.one_apply_ne hg
    rw [h2]
    simp [hg]

/-! ## 4. Exact coprime-count identity. -/

/-- Membership in `divisors (gcd)` unfolds to joint divisibility. -/
theorem key_mem_iff (R : ℝ) (d : ℕ) (p : ℕ × ℕ) (hp : p ∈ box R) :
    (d ∈ (Nat.gcd p.1 p.2).divisors) ↔ (d ∣ p.1 ∧ d ∣ p.2) := by
  obtain ⟨h1, h2⟩ := box_mem_pos R p hp
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
theorem prod_filter_eq (R : ℝ) (d : ℕ) :
    ((box R).filter (fun p => d ∈ (Nat.gcd p.1 p.2).divisors)) =
      (((Finset.Icc (Mlo R) (Mhi R)).filter (fun m => d ∣ m)) ×ˢ
        (((Finset.Icc (Nlo R) (Nhi R)).filter (fun n => d ∣ n)))) := by
  have h1 : ((box R).filter (fun p => d ∈ (Nat.gcd p.1 p.2).divisors)) =
      ((box R).filter (fun p => d ∣ p.1 ∧ d ∣ p.2)) := by
    apply Finset.filter_congr
    intro x hx
    exact key_mem_iff R d x hx
  rw [h1]
  unfold box
  rw [Finset.filter_product]

/-- Exact identity: the coprime count is `∑ μ(d) · A(d) · B(d)`. -/
theorem coprime_count_eq (R : ℝ) :
    (copCount R : ℤ) = ∑ d ∈ Finset.Icc 1 (Mhi R),
      (moebius d : ℤ) * ((Acount R d : ℤ) * (Bcount R d : ℤ)) := by
  have step1 : (copCount R : ℤ) = ∑ p ∈ box R,
      (if Nat.gcd p.1 p.2 = 1 then (1:ℤ) else 0) :=
    (Finset.sum_boole _ _).symm
  have step2 : ∀ p ∈ box R, (if Nat.gcd p.1 p.2 = 1 then (1:ℤ) else 0) =
      ∑ d ∈ Finset.Icc 1 (Mhi R),
        (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0) := by
    intro p hp
    obtain ⟨h1, h2⟩ := box_mem_pos R p hp
    have hsub : (Nat.gcd p.1 p.2).divisors ⊆ Finset.Icc 1 (Mhi R) := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      have hdm : d ∣ p.1 := dvd_trans hd.1 (Nat.gcd_dvd_left _ _)
      have hle : d ≤ p.1 := Nat.le_of_dvd (by omega) hdm
      have hMhi : p.1 ≤ Mhi R := by
        have hmem := (box_mem_iff R p).mp hp
        exact (Finset.mem_Icc.mp hmem.1).2
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdm (by omega)
      simp only [Finset.mem_Icc]
      exact ⟨hd1, le_trans hle hMhi⟩
    have h0 : ∀ d ∈ Finset.Icc 1 (Mhi R),
        d ∉ (Nat.gcd p.1 p.2).divisors →
          (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0) = 0 :=
      fun d _ hnd => by simp [hnd]
    have hbase : (∑ d ∈ Finset.Icc 1 (Mhi R),
          (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0)) =
        (∑ d ∈ (Nat.gcd p.1 p.2).divisors, (moebius d : ℤ)) := by
      calc (∑ d ∈ Finset.Icc 1 (Mhi R),
              (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0))
          = (∑ d ∈ (Nat.gcd p.1 p.2).divisors,
              (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0)) :=
            (Finset.sum_subset hsub h0).symm
        _ = (∑ d ∈ (Nat.gcd p.1 p.2).divisors, (moebius d : ℤ)) := by
            apply Finset.sum_congr rfl
            intro d hd
            simp [hd]
    have hmi := moebius_indicator (Nat.gcd p.1 p.2)
    rw [← hbase] at hmi
    exact hmi.symm
  calc (copCount R : ℤ)
      = ∑ p ∈ box R, (if Nat.gcd p.1 p.2 = 1 then (1:ℤ) else 0) := step1
    _ = ∑ p ∈ box R, ∑ d ∈ Finset.Icc 1 (Mhi R),
          (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0) :=
        Finset.sum_congr rfl (fun p hp => step2 p hp)
    _ = ∑ d ∈ Finset.Icc 1 (Mhi R), ∑ p ∈ box R,
          (if d ∈ (Nat.gcd p.1 p.2).divisors then (moebius d : ℤ) else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 (Mhi R),
          (moebius d : ℤ) * ((Acount R d : ℤ) * (Bcount R d : ℤ)) := by
        apply Finset.sum_congr rfl
        intro d _
        have hfac : (∑ p ∈ box R, (if d ∈ (Nat.gcd p.1 p.2).divisors
            then (moebius d : ℤ) else 0)) =
            (moebius d : ℤ) * ∑ p ∈ box R,
              (if d ∈ (Nat.gcd p.1 p.2).divisors then (1:ℤ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          by_cases h : d ∈ (Nat.gcd p.1 p.2).divisors
          · simp [h]
          · simp [h]
        rw [hfac]
        have hcard : ((Acount R d : ℤ) * (Bcount R d : ℤ)) =
            ∑ p ∈ box R, (if d ∈ (Nat.gcd p.1 p.2).divisors then (1:ℤ) else 0) := by
          have hcardN : Acount R d * Bcount R d =
              #((box R).filter (fun p => d ∈ (Nat.gcd p.1 p.2).divisors)) := by
            unfold Acount Bcount
            rw [← Finset.card_product, ← prod_filter_eq R d]
          have hboole : (∑ p ∈ box R,
              (if d ∈ (Nat.gcd p.1 p.2).divisors then (1:ℤ) else 0)) =
              ((((box R).filter
                (fun p => d ∈ (Nat.gcd p.1 p.2).divisors)).card) : ℤ) :=
            Finset.sum_boole _ _
          rw [← Nat.cast_mul, hcardN, hboole]
        rw [hcard]

/-! ## 5. Real analytic bounds. -/

/-- Nat-division cast lower bound. -/
theorem nat_div_cast_lower (a d : ℕ) (hd : 0 < d) :
    (a : ℝ) / (d : ℝ) - 1 ≤ ((a / d : ℕ) : ℝ) := by
  have e1 := Nat.div_add_mod a d
  have e1' : (a / d) * d + a % d = a := by
    rw [mul_comm]; exact e1
  have hr : a % d < d := Nat.mod_lt _ hd
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcast : ((a / d : ℕ) : ℝ) * (d : ℝ) + ((a % d : ℕ) : ℝ) = (a : ℝ) := by
    exact_mod_cast e1'
  have hle : ((a % d : ℕ) : ℝ) ≤ (d : ℝ) - 1 := by
    have h1 : a % d ≤ d - 1 := by omega
    have h2 : (((a % d : ℕ)) : ℝ) ≤ (((d - 1 : ℕ)) : ℝ) := by
      exact_mod_cast h1
    rwa [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] at h2
  have key : (a : ℝ) - (d : ℝ) ≤ ((a / d : ℕ) : ℝ) * (d : ℝ) := by
    nlinarith [hcast, hle, hdr]
  have hfin : ((a : ℝ) - (d : ℝ)) / (d : ℝ) ≤ ((a / d : ℕ) : ℝ) := by
    rw [div_le_iff₀ hdr]
    linarith [key]
  calc (a : ℝ) / (d : ℝ) - 1 = ((a : ℝ) - (d : ℝ)) / (d : ℝ) := by
          rw [sub_div, div_self (ne_of_gt hdr)]
    _ ≤ ((a / d : ℕ) : ℝ) := hfin

/-- Nat-division cast upper bound. -/
theorem nat_div_cast_upper (a d : ℕ) (hd : 0 < d) :
    ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / (d : ℝ) := by
  have e1 := Nat.div_add_mod a d
  have e1' : (a / d) * d + a % d = a := by
    rw [mul_comm]; exact e1
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcast : ((a / d : ℕ) : ℝ) * (d : ℝ) + ((a % d : ℕ) : ℝ) = (a : ℝ) := by
    exact_mod_cast e1'
  have hnn : (0 : ℝ) ≤ ((a % d : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [le_div_iff₀ hdr]
  linarith [hcast, hnn]

/-- One-step log difference: `1/d ≤ log d - log (d-1)` for `d ≥ 2`. -/
theorem one_div_le_log_pred {d : ℕ} (hd : 2 ≤ d) :
    (1 : ℝ) / (d : ℝ) ≤ Real.log (d : ℝ) - Real.log ((d : ℝ) - 1) := by
  have h1 : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have h0 : (0 : ℝ) < (d : ℝ) - 1 := by
    have h1' : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
    linarith
  have hpos : (0 : ℝ) < ((d : ℝ) - 1) / (d : ℝ) := div_pos h0 h1
  have hlog := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (ne_of_gt h0) (ne_of_gt h1)] at hlog
  have heq : ((d : ℝ) - 1) / (d : ℝ) - 1 = - (1 / (d : ℝ)) := by
    have hd' : (d : ℝ) ≠ 0 := ne_of_gt h1
    field_simp
    ring
  rw [heq] at hlog
  linarith [hlog]

/-- Harmonic sum over `[2, ·]` is bounded by `log`. -/
theorem harmonic_tail_aux (n : ℕ) :
    (∑ d ∈ Finset.Icc 2 (2 + n), (1 : ℝ) / (d : ℝ)) ≤
      Real.log (((2 + n : ℕ)) : ℝ) := by
  induction n with
  | zero =>
    have hset : Finset.Icc 2 (0 + 2) = ({2} : Finset ℕ) := by decide
    rw [hset, Finset.sum_singleton]
    show (1 : ℝ) / ((2 : ℕ) : ℝ) ≤ Real.log ((2 : ℕ) : ℝ)
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2]
    have he : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
      have h2mul : (((2 : ℕ)) : ℝ) * ((1 : ℝ) / 2) = 1 := by norm_num
      have hexp : (Real.exp ((1 : ℝ) / 2)) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul, h2mul]
      nlinarith [hexp, Real.exp_one_lt_d9, Real.exp_pos ((1 : ℝ) / 2),
        sq_nonneg (Real.exp ((1 : ℝ) / 2) - 2)]
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 :=
      (Real.le_log_iff_exp_le (show (0 : ℝ) < 2 by norm_num)).mpr he
    exact hlog
  | succ n ih =>
    show (∑ d ∈ Finset.Icc 2 ((2 + n) + 1), (1 : ℝ) / (d : ℝ)) ≤
      Real.log ((((2 + n) + 1 : ℕ)) : ℝ)
    have hset : insert ((2 + n) + 1) (Finset.Icc 2 (2 + n)) =
        Finset.Icc 2 ((2 + n) + 1) := by
      ext d
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hmem : (2 + n) + 1 ∉ Finset.Icc 2 (2 + n) := by
      simp only [Finset.mem_Icc, not_and]
      intro _ h
      omega
    rw [← hset, Finset.sum_insert hmem]
    have hstep := one_div_le_log_pred (d := (2 + n) + 1) (by omega)
    have hb : ((((2 + n) + 1 : ℕ)) : ℝ) - 1 = (((2 + n : ℕ)) : ℝ) := by
      have hcast : ((((2 + n) + 1 : ℕ)) : ℝ) = (((2 + n : ℕ)) : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hcast]
      ring
    rw [hb] at hstep
    have hlog : Real.log ((((2 + n) + 1 : ℕ)) : ℝ) =
        Real.log ((((2 + n : ℕ)) : ℝ) + 1) := by
      congr 1
      rw [Nat.cast_add, Nat.cast_one]
    rw [hlog]
    linarith [ih, hstep]

/-- Harmonic bound on `[1, D]`. -/
theorem harmonic_le (D : ℕ) (hD : 1 ≤ D) :
    (∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ)) ≤ 1 + Real.log (D : ℝ) := by
  have hset : insert 1 (Finset.Icc 2 D) = Finset.Icc 1 D := by
    ext d
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hmem : (1 : ℕ) ∉ Finset.Icc 2 D := by
    simp only [Finset.mem_Icc, not_and]
    intro _ h
    omega
  rw [← hset, Finset.sum_insert hmem]
  by_cases h2 : 2 ≤ D
  · obtain ⟨k, hk⟩ : ∃ k, D = 2 + k := ⟨D - 2, by omega⟩
    subst hk
    have ht := harmonic_tail_aux k
    have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h1]
    linarith [ht]
  · have hempty : Finset.Icc 2 D = ∅ :=
      Finset.Icc_eq_empty_iff.mpr h2
    rw [hempty, Finset.sum_empty]
    have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h1]
    have hlognn : (0 : ℝ) ≤ Real.log ((D : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hD)
    linarith [hlognn]

/-- Harmonic tail of squares: `∑_{d ≥ 6} 1/d² ≤ 1/5`. -/
theorem moebius_tail_sq (D : ℕ) :
    (∑ d ∈ Finset.Icc 6 D, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 1 / 5 := by
  have key : ∀ k : ℕ, (∑ d ∈ Finset.Icc 6 (5 + k), (1 : ℝ) / (d : ℝ) ^ 2) ≤
      1 / 5 - 1 / ((((5 + k : ℕ)) : ℝ)) := by
    intro k
    induction k with
    | zero =>
      have hset : Finset.Icc 6 (5 + 0) = (∅ : Finset ℕ) := by decide
      rw [hset, Finset.sum_empty]
      norm_num
    | succ k ih =>
      have hset : insert ((5 + k) + 1) (Finset.Icc 6 (5 + k)) =
          Finset.Icc 6 (5 + (k + 1)) := by
        ext d
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hmem : (5 + k) + 1 ∉ Finset.Icc 6 (5 + k) := by
        simp only [Finset.mem_Icc, not_and]
        intro _ h
        omega
      rw [← hset, Finset.sum_insert hmem]
      have hN : (5 : ℝ) ≤ (((5 + k : ℕ)) : ℝ) := by
        have h : 5 ≤ 5 + k := Nat.le_add_right _ _
        exact_mod_cast h
      have hN0 : (0 : ℝ) < (((5 + k : ℕ)) : ℝ) := by linarith
      have hN1 : (0 : ℝ) < (((5 + k : ℕ)) : ℝ) + 1 := by linarith
      have hstep : (1 : ℝ) / ((((5 + k : ℕ)) : ℝ) + 1) ^ 2 ≤
          1 / (((5 + k : ℕ)) : ℝ) - 1 / ((((5 + k : ℕ)) : ℝ) + 1) := by
        have h3 : (0 : ℝ) < (((5 + k : ℕ)) : ℝ) * ((((5 + k : ℕ)) : ℝ) + 1) :=
          mul_pos hN0 hN1
        have h4 : (0 : ℝ) < ((((5 + k : ℕ)) : ℝ) + 1) ^ 2 := pow_pos hN1 2
        have hpos : (0:ℝ) < (((5 + k : ℕ)) : ℝ) + 1 := hN1
        have key2 : (1 : ℝ) / ((((5 + k : ℕ)) : ℝ) + 1) ^ 2 ≤
            1 / ((((5 + k : ℕ)) : ℝ) * ((((5 + k : ℕ)) : ℝ) + 1)) := by
          apply one_div_le_one_div_of_le h3
          nlinarith [hN1]
        have e2 : (1 : ℝ) / ((((5 + k : ℕ)) : ℝ) * ((((5 + k : ℕ)) : ℝ) + 1)) =
            1 / (((5 + k : ℕ)) : ℝ) - 1 / ((((5 + k : ℕ)) : ℝ) + 1) := by
          have hNe0 := ne_of_gt hN0
          have hNe1 := ne_of_gt hN1
          field_simp
          ring
        linarith [key2, e2]
      have hcast : ((((5 + k) + 1 : ℕ)) : ℝ) = (((5 + k : ℕ)) : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      have hcast2 : ((((5 + (k + 1) : ℕ)) : ℝ)) = ((((5 + k) + 1 : ℕ)) : ℝ) := rfl
      rw [hcast2, hcast]
      linarith [ih, hstep]
  by_cases h6 : 6 ≤ D
  · have hD' : D = 5 + (D - 5) := by omega
    rw [hD']
    have hnn : (0 : ℝ) ≤ 1 / ((((5 + (D - 5) : ℕ)) : ℝ)) := by
      apply div_nonneg (by norm_num)
      exact_mod_cast Nat.zero_le _
    linarith [key (D - 5), hnn]
  · have hempty : Finset.Icc 6 D = ∅ :=
      Finset.Icc_eq_empty_iff.mpr (by omega)
    rw [hempty, Finset.sum_empty]
    norm_num

end WindowMobiusCount
