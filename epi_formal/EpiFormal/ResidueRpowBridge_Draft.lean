/-
  ResidueRpowBridge_DRAFT.lean — DRAFT, NOT TYPECHECKED.

  Status: proof text only; pending `lake env lean` check after the serial
  build completes. Do NOT import from `EpiFormal.lean` or `Audit.lean`
  until checked (currently inert: no importer).

  Purpose: bridge the exact-integer script
  `verification/residue_certificate_general*.py` (`enclose_power`) to the
  real-number hypothesis `hcert` of `step_cert_upper_sound` /
  `step_cert_lower_sound` in `TransferOperatorDim.lean`.

  Script invariant (exact integers, zero float trust):
    lo^q * num^p ≤ SCALE^q * den^p   (lower certificate row)
    hi^q * num^p ≥ SCALE^q * den^p   (upper certificate row)
  where base = num/den > 0, power = p/q > 0, SCALE ≥ 1.
  Needed real conclusion:
    (lo/SCALE : ℝ) ≤ ((num/den : ℝ)) ^ (-(p/q : ℝ)) ≤ (hi/SCALE : ℝ).

  Proof method: raise both sides to the q-th (natural) power, following the
  house style of `dimH_residueMod4_le_four_fifths` (`le_of_pow_le_pow_left₀`).
-/

/-- Lower integer certificate row implies the real lower rpow bound. -/
theorem enclose_rpow_lower {num den lo SCALE p q : ℕ} (hq : 1 ≤ q)
    (hden : 0 < den) (hnum : 0 < num) (hS : 0 < SCALE)
    (hlo : lo ^ q * num ^ p ≤ SCALE ^ q * den ^ p) :
    (lo : ℝ) / (SCALE : ℝ) ≤ ((num : ℝ) / (den : ℝ)) ^ (-((p : ℝ) / (q : ℝ))) := by
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hnumR : (0 : ℝ) < (num : ℝ) := by exact_mod_cast hnum
  have hSR : (0 : ℝ) < (SCALE : ℝ) := by exact_mod_cast hS
  have hloR : (0 : ℝ) ≤ (lo : ℝ) / (SCALE : ℝ) := by positivity
  have hnd : (0 : ℝ) ≤ (num : ℝ) / (den : ℝ) := by positivity
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqr
  apply le_of_pow_le_pow_left₀ (n := q) (by omega) hloR
  have hrhs : ((((num : ℝ) / (den : ℝ)) ^ (-((p : ℝ) / (q : ℝ)))) ^ (q : ℕ))
      = (den : ℝ) ^ (p : ℕ) / (num : ℝ) ^ (p : ℕ) := by
    rw [← Real.rpow_natCast _ _, ← Real.rpow_mul hnd]
    have hexp : -((p : ℝ) / (q : ℝ)) * (q : ℝ) = -((p : ℝ)) := by
      field_simp
      ring
    rw [hexp, Real.rpow_neg hnd _, Real.rpow_natCast _ _, inv_pow, inv_div,
      div_pow]
  rw [hrhs]
  have hcast : ((lo ^ q * num ^ p : ℕ) : ℝ) ≤ ((SCALE ^ q * den ^ p : ℕ) : ℝ) := by
    exact_mod_cast hlo
  push_cast at hcast
  have hNp : (0 : ℝ) < ((num : ℝ) ^ (p : ℕ)) := by positivity
  have hSq : (0 : ℝ) < ((SCALE : ℝ) ^ (q : ℕ)) := by positivity
  rw [div_pow, div_le_div_iff hSq hNp]
  calc (lo : ℝ) ^ (q : ℕ) * (num : ℝ) ^ (p : ℕ)
      ≤ (SCALE : ℝ) ^ (q : ℕ) * (den : ℝ) ^ (p : ℕ) := hcast
    _ = (den : ℝ) ^ (p : ℕ) * (SCALE : ℝ) ^ (q : ℕ) := by ring

/-- Upper integer certificate row implies the real upper rpow bound. -/
theorem enclose_rpow_upper {num den hi SCALE p q : ℕ} (hq : 1 ≤ q)
    (hden : 0 < den) (hnum : 0 < num) (hS : 0 < SCALE)
    (hhi : SCALE ^ q * den ^ p ≤ hi ^ q * num ^ p) :
    ((num : ℝ) / (den : ℝ)) ^ (-((p : ℝ) / (q : ℝ))) ≤ (hi : ℝ) / (SCALE : ℝ) := by
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hnumR : (0 : ℝ) < (num : ℝ) := by exact_mod_cast hnum
  have hSR : (0 : ℝ) < (SCALE : ℝ) := by exact_mod_cast hS
  have hhiR : (0 : ℝ) ≤ (hi : ℝ) / (SCALE : ℝ) := by positivity
  have hnd : (0 : ℝ) ≤ (num : ℝ) / (den : ℝ) := by positivity
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqr
  have hbase : (0 : ℝ) ≤ ((num : ℝ) / (den : ℝ)) ^ (-((p : ℝ) / (q : ℝ))) := by
    positivity
  apply le_of_pow_le_pow_left₀ (n := q) (by omega) hbase
  have hrhs : ((((num : ℝ) / (den : ℝ)) ^ (-((p : ℝ) / (q : ℝ)))) ^ (q : ℕ))
      = (den : ℝ) ^ (p : ℕ) / (num : ℝ) ^ (p : ℕ) := by
    rw [← Real.rpow_natCast _ _, ← Real.rpow_mul hnd]
    have hexp : -((p : ℝ) / (q : ℝ)) * (q : ℝ) = -((p : ℝ)) := by
      field_simp
      ring
    rw [hexp, Real.rpow_neg hnd _, Real.rpow_natCast _ _, inv_pow, inv_div,
      div_pow]
  rw [hrhs]
  have hcast : ((SCALE ^ q * den ^ p : ℕ) : ℝ) ≤ ((hi ^ q * num ^ p : ℕ) : ℝ) := by
    exact_mod_cast hhi
  push_cast at hcast
  have hNp : (0 : ℝ) < ((num : ℝ) ^ (p : ℕ)) := by positivity
  have hSq : (0 : ℝ) < ((SCALE : ℝ) ^ (q : ℕ)) := by positivity
  rw [div_pow, div_le_div_iff hNp hSq]
  calc (den : ℝ) ^ (p : ℕ) * (SCALE : ℝ) ^ (q : ℕ)
      = (SCALE : ℝ) ^ (q : ℕ) * (den : ℝ) ^ (p : ℕ) := by ring
    _ ≤ (hi : ℝ) ^ (q : ℕ) * (num : ℝ) ^ (p : ℕ) := hcast
