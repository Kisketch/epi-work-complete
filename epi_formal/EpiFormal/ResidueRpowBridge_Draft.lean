import Mathlib

/-
  ResidueRpowBridge_DRAFT.lean — DRAFT, NOT TYPECHECKED (in progress).

  Status: CHECKED 2026-11-23 via `lake env lean` (exit 0) + `lake build`; #print axioms = base three for both lemmas. Still DRAFT: not imported.
  Do NOT import from `EpiFormal.lean` / `Audit.lean` until checked
  (currently inert: no importer).
-/

/-- Lower integer certificate row implies the real lower rpow bound. -/
theorem enclose_rpow_lower {num den lo SCALE p q : ℕ} (hq : 1 ≤ q)
    (hden : 0 < den) (hnum : 0 < num) (hS : 0 < SCALE)
    (hlo : lo ^ q * num ^ p ≤ SCALE ^ q * den ^ p) :
    (lo : ℝ) / (SCALE : ℝ) ≤ ((num : ℝ) / (den : ℝ)) ^ (-((p : ℝ) / (q : ℝ))) := by
  have hnumR : (0 : ℝ) < (num : ℝ) := by exact_mod_cast hnum
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hSR : (0 : ℝ) < (SCALE : ℝ) := by exact_mod_cast hS
  have hNp : (0 : ℝ) < ((num : ℝ) ^ (p : ℕ)) := by positivity
  have hSq : (0 : ℝ) < ((SCALE : ℝ) ^ (q : ℕ)) := by positivity
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hnd : (0 : ℝ) ≤ (num : ℝ) / (den : ℝ) := by positivity
  have hbase : (0 : ℝ) ≤ ((num : ℝ) / (den : ℝ)) ^ (-((p : ℝ) / (q : ℝ))) := by
    positivity
  have h1 : ((p : ℝ) / (q : ℝ)) * (q : ℝ) = (p : ℝ) := div_mul_cancel₀ _ hq0
  have hexp : -((p : ℝ) / (q : ℝ)) * (q : ℝ) = -((p : ℝ)) := by
    rw [neg_mul, h1]
  have hrhs : ((((num : ℝ) / (den : ℝ)) ^ (-((p : ℝ) / (q : ℝ)))) ^ (q : ℕ))
      = (den : ℝ) ^ (p : ℕ) / (num : ℝ) ^ (p : ℕ) := by
    rw [← Real.rpow_natCast _ _, ← Real.rpow_mul hnd, hexp,
      Real.rpow_neg hnd _, Real.rpow_natCast _ _, ← inv_pow, inv_div, div_pow]
  apply le_of_pow_le_pow_left₀ (n := q) (by omega) hbase
  rw [hrhs, div_pow, div_le_iff₀ hSq, div_mul_eq_mul_div, le_div_iff₀ hNp]
  have hcast : ((lo ^ q * num ^ p : ℕ) : ℝ) ≤ ((SCALE ^ q * den ^ p : ℕ) : ℝ) := by
    exact_mod_cast hlo
  push_cast at hcast
  linear_combination hcast

/-- Upper integer certificate row implies the real upper rpow bound. -/
theorem enclose_rpow_upper {num den hi SCALE p q : ℕ} (hq : 1 ≤ q)
    (hden : 0 < den) (hnum : 0 < num) (hS : 0 < SCALE)
    (hhi : SCALE ^ q * den ^ p ≤ hi ^ q * num ^ p) :
    ((num : ℝ) / (den : ℝ)) ^ (-((p : ℝ) / (q : ℝ))) ≤ (hi : ℝ) / (SCALE : ℝ) := by
  have hnumR : (0 : ℝ) < (num : ℝ) := by exact_mod_cast hnum
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hSR : (0 : ℝ) < (SCALE : ℝ) := by exact_mod_cast hS
  have hNp : (0 : ℝ) < ((num : ℝ) ^ (p : ℕ)) := by positivity
  have hSq : (0 : ℝ) < ((SCALE : ℝ) ^ (q : ℕ)) := by positivity
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hnd : (0 : ℝ) ≤ (num : ℝ) / (den : ℝ) := by positivity
  have hhiR : (0 : ℝ) ≤ (hi : ℝ) / (SCALE : ℝ) := by positivity
  have h1 : ((p : ℝ) / (q : ℝ)) * (q : ℝ) = (p : ℝ) := div_mul_cancel₀ _ hq0
  have hexp : -((p : ℝ) / (q : ℝ)) * (q : ℝ) = -((p : ℝ)) := by
    rw [neg_mul, h1]
  have hrhs : ((((num : ℝ) / (den : ℝ)) ^ (-((p : ℝ) / (q : ℝ)))) ^ (q : ℕ))
      = (den : ℝ) ^ (p : ℕ) / (num : ℝ) ^ (p : ℕ) := by
    rw [← Real.rpow_natCast _ _, ← Real.rpow_mul hnd, hexp,
      Real.rpow_neg hnd _, Real.rpow_natCast _ _, ← inv_pow, inv_div, div_pow]
  have hbase : (0 : ℝ) ≤ ((num : ℝ) / (den : ℝ)) ^ (-((p : ℝ) / (q : ℝ))) := by
    positivity
  apply le_of_pow_le_pow_left₀ (n := q) (by omega) hhiR
  rw [hrhs, div_pow, div_le_iff₀ hNp, div_mul_eq_mul_div, le_div_iff₀ hSq]
  have hcast : ((SCALE ^ q * den ^ p : ℕ) : ℝ) ≤ ((hi ^ q * num ^ p : ℕ) : ℝ) := by
    exact_mod_cast hhi
  push_cast at hcast
  linear_combination hcast
