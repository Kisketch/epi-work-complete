import EpiFormal.ResidueCertGenSound
import EpiFormal.ResidueCertGen.M2R1LAll
import EpiFormal.ResidueCertGen.M2R1UAll
import EpiFormal.ResidueCertGen.M2R2LAll
import EpiFormal.ResidueCertGen.M2R2UAll
import EpiFormal.ResidueCertGen.M3R1LAll
import EpiFormal.ResidueCertGen.M3R1UAll
import EpiFormal.ResidueCertGen.M3R3LAll
import EpiFormal.ResidueCertGen.M3R3UAll
import EpiFormal.ResidueCertGen.M4R1LAll
import EpiFormal.ResidueCertGen.M4R1UAll
import EpiFormal.ResidueCertGen.M4R4LAll
import EpiFormal.ResidueCertGen.M4R4UAll
import EpiFormal.ResidueCertGen.M5R1LAll
import EpiFormal.ResidueCertGen.M5R1UAll
import EpiFormal.ResidueCertGen.M5R5LAll
import EpiFormal.ResidueCertGen.M5R5UAll
import EpiFormal.ResidueCertGen.M6R1LAll
import EpiFormal.ResidueCertGen.M6R1UAll
import EpiFormal.ResidueCertGen.M6R6LAll
import EpiFormal.ResidueCertGen.M6R6UAll

/-!
# Strict Open Transfer-Operator Certificate Bounds (Bowen-Free, Zero Recomputation)

Upgrades the closed bounds `dimH_le_of_certU` / `le_dimH_of_certL` in
`EpiFormal/ResidueCertGenSound.lean` to strict open inequalities
`dimH_lt_of_certU` / `lt_dimH_of_certL`, exploiting the fact that `ResidueCertGen.rowU`
and `ResidueCertGen.rowL` already verify strict `Nat.blt` (`<`) inequalities in all
200 existing `ResidueCertGen/` kernel-checked certificates.

By continuity in `t ∈ (1/2, ∞)` of the finite `K`-term sum plus closed-form integral tail
across the finitely many grid cells `j : Fin N`, the strict inequality at `s = p/(2q)`
persists on a neighborhood `(s - δ, s + δ)`, yielding `t < s` (upper) or `s < t` (lower)
with `dimH F_{m,r} ≤ ENNReal.ofReal t < ENNReal.ofReal s` or
`ENNReal.ofReal s < ENNReal.ofReal t ≤ dimH F_{m,r}` directly from
`TransferOperatorDim.step_cert_upper_sound` / `step_cert_lower_sound`.

This completely eliminates any Bowen/pressure continuity dependency for open brackets
across all 20 certified endpoints `m ∈ {2,3,4,5,6}, r ∈ {1,m}` with zero recomputation.
-/

namespace ResidueCertStrictOpen

open Finset Filter Topology ResidueCertGen TransferOperatorDim ResidueModGeneral
open scoped ENNReal

/-- **Strict Upper Bound from a Checked Certificate** (`dimH F_{m,r} < p / (2q)`). -/
theorem dimH_lt_of_certU {m r K p q N S tail u : ℕ} {vec : List ℕ} (row : ℕ → List ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hK : 1 ≤ K) (hN : 1 ≤ N) (hcut : N + 1 ≤ m * K + r)
    (hq : 1 ≤ q) (hpq : q < p) (hS : 0 < S)
    (hvec : vecOK vec N = true) (htail : tailU m r K p q S tail u = true)
    (hrows : ∀ j < N, rowU vec N m r K p q S tail j (row j) = true) :
    dimH (residueConstSet m r) < ENNReal.ofReal ((p : ℝ) / (2 * q)) := by
  obtain ⟨hlen, hanti, hposv⟩ := vecOK_spec hvec
  set s : ℝ := (p : ℝ) / (2 * q) with hs_def
  have hs_half : 1 / 2 < s := half_lt_s p q hq hpq
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hbase_tail_pos : (0 : ℝ) < ((m * (K - 1) + r : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < m * (K - 1) + r)
  let fU : Fin N → ℝ → ℝ := fun j t =>
    (∑ k ∈ range K,
      (vec.getD (binLeft N hN (m * k + r) j).1 0 : ℝ) *
        (((m * k + r : ℕ) : ℝ) + (j.1 : ℝ) / (N : ℝ)) ^ (-(2 * t))) +
    (vec.getD 0 0 : ℝ) *
      ((((m * (K - 1) + r : ℕ) : ℝ) ^ (1 - 2 * t)) / ((m : ℝ) * (2 * t - 1)))
  have hstrict : ∀ j : Fin N, fU j s < (vec.getD j.1 0 : ℝ) := by
    intro j
    have hrow := hrows j.1 j.2
    simp only [rowU, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hrow
    obtain ⟨⟨hclen, hpow⟩, hlt⟩ := hrow
    set c := row j.1 with hc_def
    have hbl : ∀ k, (binLeft N hN (m * k + r) j).val = cellAt N (m * (0 + k) + r) (j.1 + 1) :=
      fun k => by rw [zero_add]; exact binLeft_val N _ hN j
    set R : ℝ := (∑ k ∈ range K,
        (vec.getD (cellAt N (m * (0 + k) + r) (j.1 + 1)) 0 : ℝ) * ((c.getD k 0 : ℝ) / S)) +
        (vec.getD 0 0 : ℝ) * ((tail : ℝ) / S) with hR
    have hRlt : R < (vec.getD j.1 0 : ℝ) := by
      have hX : ((rowSum vec N m r j.1 1 c 0 + tail * vec.getD 0 0 : ℕ) : ℝ)
          < ((S * vec.getD j.1 0 : ℕ) : ℝ) := by exact_mod_cast hlt
      have hRX : R = ((rowSum vec N m r j.1 1 c 0 + tail * vec.getD 0 0 : ℕ) : ℝ) / S := by
        rw [hR, rowSum_eq, hclen]
        push_cast
        rw [add_div, Finset.sum_div]
        congr 1
        · exact Finset.sum_congr rfl fun k _ => by ring
        · ring
      rw [hRX, div_lt_iff₀ hSR]
      push_cast at hX ⊢
      linarith
    have hleR : fU j s ≤ R := by
      dsimp only [fU]
      rw [hR]
      refine add_le_add (Finset.sum_le_sum fun k hk => ?_) ?_
      · have hk' : k < K := Finset.mem_range.mp hk
        have hck := powU_spec N m r p q S j.1 c 0 hpow k (by rw [hclen]; exact hk')
        rw [zero_add] at hck
        have ht := term_upper (k := k) (j := j.1) hN hq hS hck
          (Nat.add_pos_left (Nat.mul_pos (by omega) (by omega)) _)
        rw [hbl k]
        exact mul_le_mul_of_nonneg_left (by simpa only [hs_def] using ht) (Nat.cast_nonneg _)
      · exact mul_le_mul_of_nonneg_left
          (by simpa only [hs_def] using tail_upper hm hq hpq hS (by omega) htail)
          (Nat.cast_nonneg _)
    exact lt_of_le_of_lt hleR hRlt
  have hcont : ∀ j : Fin N, ContinuousAt (fU j) s := by
    intro j
    have hsum_cont : Continuous (fun t : ℝ =>
        ∑ k ∈ range K,
          (vec.getD (binLeft N hN (m * k + r) j).1 0 : ℝ) *
            (((m * k + r : ℕ) : ℝ) + (j.1 : ℝ) / (N : ℝ)) ^ (-(2 * t))) := by
      refine continuous_finsetSum _ fun k _ => ?_
      have hbase : (0 : ℝ) < ((m * k + r : ℕ) : ℝ) + (j.1 : ℝ) / (N : ℝ) := by
        have h1 : (0 : ℝ) < ((m * k + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m * k + r)
        positivity
      exact continuous_const.mul
        (Continuous.rpow continuous_const (continuous_const.mul continuous_id).neg
          (fun _ => Or.inl hbase.ne'))
    have htail_num : ContinuousAt (fun t : ℝ => ((m * (K - 1) + r : ℕ) : ℝ) ^ (1 - 2 * t)) s :=
      (Continuous.rpow continuous_const
        (continuous_const.sub (continuous_const.mul continuous_id))
        (fun _ => Or.inl hbase_tail_pos.ne')).continuousAt
    have htail_den : ContinuousAt (fun t : ℝ => (m : ℝ) * (2 * t - 1)) s :=
      (continuous_const.mul
        ((continuous_const.mul continuous_id).sub continuous_const)).continuousAt
    have hden_ne : (m : ℝ) * (2 * s - 1) ≠ 0 := (mul_pos hmR (by linarith)).ne'
    exact hsum_cont.continuousAt.add (continuousAt_const.mul (htail_num.div htail_den hden_ne))
  have hev_all : ∀ᶠ t in 𝓝 s, (1 / 2 : ℝ) < t ∧ ∀ j : Fin N, fU j t < (vec.getD j.1 0 : ℝ) := by
    refine Filter.Eventually.and (Ioi_mem_nhds hs_half) (Filter.eventually_all.mpr fun j => ?_)
    exact (hcont j).eventually (Iio_mem_nhds (hstrict j))
  rw [Metric.eventually_nhds_iff] at hev_all
  obtain ⟨δ, hδ_pos, hδ_prop⟩ := hev_all
  set t : ℝ := s - δ / 2 with ht_def
  have hdist : dist t s < δ := by
    rw [Real.dist_eq, ht_def, show s - δ / 2 - s = -(δ / 2) by ring, abs_neg,
      abs_of_pos (half_pos hδ_pos)]
    linarith
  obtain ⟨ht_half, ht_lt⟩ := hδ_prop hdist
  have ht_lt_s : t < s := by rw [ht_def]; linarith
  let v : Fin N → ℝ≥0∞ := fun j => ((vec.getD j.1 0 : ℕ) : ℝ≥0∞)
  have hdim_le : dimH (residueConstSet m r) ≤ ENNReal.ofReal t := by
    refine step_cert_upper_sound hm hr hK hN hcut ht_half v ?_ ?_
      (fun j k => v (binLeft N hN (m * k + r) j)) ?_ ?_
    · intro j
      have := hposv j.1 j.2
      change (0 : ℝ≥0∞) < ((vec.getD j.1 0 : ℕ) : ℝ≥0∞)
      exact_mod_cast (by omega : 0 < vec.getD j.1 0)
    · intro j
      exact (ENNReal.natCast_ne_top _).lt_top
    · intro j k _ i hL _
      have hL' : (binLeft N hN (m * k + r) j).val ≤ i.val := hL
      change ((vec.getD i.1 0 : ℕ) : ℝ≥0∞) ≤
        ((vec.getD (binLeft N hN (m * k + r) j).1 0 : ℕ) : ℝ≥0∞)
      exact_mod_cast antiOK_getD vec hanti _ _ hL' (by rw [hlen]; exact i.2)
    · intro j
      have hnn : ∀ k ∈ range K,
          0 ≤ (vec.getD (binLeft N hN (m * k + r) j).1 0 : ℝ) *
            (((m * k + r : ℕ) : ℝ) + (j.1 : ℝ) / (N : ℝ)) ^ (-(2 * t)) := fun k _ => by
        have hbase : (0 : ℝ) ≤ ((m * k + r : ℕ) : ℝ) + (j.1 : ℝ) / (N : ℝ) := by positivity
        exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hbase _)
      have htail_nn : 0 ≤ (vec.getD 0 0 : ℝ) *
          ((((m * (K - 1) + r : ℕ) : ℝ) ^ (1 - 2 * t)) / ((m : ℝ) * (2 * t - 1))) := by
        have h1 : 0 ≤ ((m * (K - 1) + r : ℕ) : ℝ) ^ (1 - 2 * t) :=
          Real.rpow_nonneg hbase_tail_pos.le _
        have h2 : 0 < (m : ℝ) * (2 * t - 1) := mul_pos hmR (by linarith)
        exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg h1 h2.le)
      have heq_lhs : (∑ k ∈ range K,
            v (binLeft N hN (m * k + r) j) *
              ENNReal.ofReal (((m * k + r : ℕ) + (j.1 : ℝ) / (N : ℝ)) ^ (-(2 * t)))) +
          v ⟨0, hN⟩ *
            ENNReal.ofReal ((((m * (K - 1) + r : ℕ) : ℝ) ^ (1 - 2 * t)) /
              ((m : ℝ) * (2 * t - 1))) = ENNReal.ofReal (fU j t) := by
        dsimp only [v, fU]
        rw [ENNReal.ofReal_add (Finset.sum_nonneg hnn) htail_nn, ENNReal.ofReal_sum_of_nonneg hnn]
        congr 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      rw [heq_lhs]
      calc ENNReal.ofReal (fU j t) ≤ ENNReal.ofReal (vec.getD j.1 0 : ℝ) :=
            ENNReal.ofReal_le_ofReal (ht_lt j).le
        _ = v j := ENNReal.ofReal_natCast _
  exact lt_of_le_of_lt hdim_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr ht_lt_s)

/-- **Strict Lower Bound from a Checked Certificate** (`p / (2q) < dimH F_{m,r}`). -/
theorem lt_dimH_of_certL {m r K Kmax p q N S tail l u : ℕ} {vec : List ℕ} (row : ℕ → List ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hK : 1 ≤ K) (hKK : K ≤ Kmax) (hN : 1 ≤ N)
    (hcut : N + 1 ≤ m * K + r) (hq : 1 ≤ q) (hpq : q < p) (hS : 0 < S)
    (hvec : vecOK vec N = true) (htail : tailL m r K Kmax p q S tail l u = true)
    (hrows : ∀ j < N, rowL vec N m r K p q S tail j (row j) = true) :
    ENNReal.ofReal ((p : ℝ) / (2 * q)) < dimH (residueConstSet m r) := by
  obtain ⟨hlen, hanti, hposv⟩ := vecOK_spec hvec
  set s : ℝ := (p : ℝ) / (2 * q) with hs_def
  have hs_half : 1 / 2 < s := half_lt_s p q hq hpq
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hbaseK_pos : (0 : ℝ) < ((m * K + r + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < m * K + r + 1)
  have hbaseKmax_pos : (0 : ℝ) < ((m * Kmax + r + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < m * Kmax + r + 1)
  let fL : Fin N → ℝ → ℝ := fun j t =>
    (∑ k ∈ range K,
      (vec.getD (binRight N hN (m * k + r) j).1 0 : ℝ) *
        (((m * k + r : ℕ) : ℝ) + ((j.1 : ℝ) + 1) / (N : ℝ)) ^ (-(2 * t))) +
    (vec.getD 0 0 : ℝ) *
      (((((m * K + r + 1 : ℕ) : ℝ) ^ (1 - 2 * t)) -
        (((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * t))) / ((m : ℝ) * (2 * t - 1)))
  have hstrict : ∀ j : Fin N, (vec.getD j.1 0 : ℝ) < fL j s := by
    intro j
    have hrow := hrows j.1 j.2
    simp only [rowL, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hrow
    obtain ⟨⟨hclen, hpow⟩, hlt⟩ := hrow
    set c := row j.1 with hc_def
    have hbr : ∀ k, (binRight N hN (m * k + r) j).val = cellAt N (m * (0 + k) + r) (j.1 + 0) :=
      fun k => by rw [zero_add]; exact binRight_val N _ hN (by nlinarith) j
    set R : ℝ := (∑ k ∈ range K,
        (vec.getD (cellAt N (m * (0 + k) + r) (j.1 + 0)) 0 : ℝ) * ((c.getD k 0 : ℝ) / S)) +
        (vec.getD 0 0 : ℝ) * ((tail : ℝ) / S) with hR
    have hRgt : (vec.getD j.1 0 : ℝ) < R := by
      have hX : ((S * vec.getD j.1 0 : ℕ) : ℝ)
          < ((rowSum vec N m r j.1 0 c 0 + tail * vec.getD 0 0 : ℕ) : ℝ) := by
        exact_mod_cast hlt
      have hRX : R = ((rowSum vec N m r j.1 0 c 0 + tail * vec.getD 0 0 : ℕ) : ℝ) / S := by
        rw [hR, rowSum_eq, hclen]
        push_cast
        rw [add_div, Finset.sum_div]
        congr 1
        · exact Finset.sum_congr rfl fun k _ => by ring
        · ring
      rw [hRX, lt_div_iff₀ hSR]
      push_cast at hX ⊢
      linarith
    have hRle : R ≤ fL j s := by
      dsimp only [fL]
      rw [hR]
      refine add_le_add (Finset.sum_le_sum fun k hk => ?_) ?_
      · have hk' : k < K := Finset.mem_range.mp hk
        have hck := powL_spec N m r p q S j.1 c 0 hpow k (by rw [hclen]; exact hk')
        rw [zero_add] at hck
        have ht := term_lower (k := k) (j := j.1) hN hq hS hck
        rw [hbr k]
        exact mul_le_mul_of_nonneg_left (by simpa only [hs_def] using ht) (Nat.cast_nonneg _)
      · exact mul_le_mul_of_nonneg_left
          (by simpa only [hs_def] using tail_lower hm hq hpq hS htail)
          (Nat.cast_nonneg _)
    exact lt_of_lt_of_le hRgt hRle
  have hcont : ∀ j : Fin N, ContinuousAt (fL j) s := by
    intro j
    have hsum_cont : Continuous (fun t : ℝ =>
        ∑ k ∈ range K,
          (vec.getD (binRight N hN (m * k + r) j).1 0 : ℝ) *
            (((m * k + r : ℕ) : ℝ) + ((j.1 : ℝ) + 1) / (N : ℝ)) ^ (-(2 * t))) := by
      refine continuous_finsetSum _ fun k _ => ?_
      have hbase : (0 : ℝ) < ((m * k + r : ℕ) : ℝ) + ((j.1 : ℝ) + 1) / (N : ℝ) := by
        have h1 : (0 : ℝ) < ((m * k + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m * k + r)
        positivity
      exact continuous_const.mul
        (Continuous.rpow continuous_const (continuous_const.mul continuous_id).neg
          (fun _ => Or.inl hbase.ne'))
    have htail_num : ContinuousAt (fun t : ℝ =>
        (((m * K + r + 1 : ℕ) : ℝ) ^ (1 - 2 * t)) -
        (((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * t))) s :=
      ((Continuous.rpow continuous_const
          (continuous_const.sub (continuous_const.mul continuous_id))
          (fun _ => Or.inl hbaseK_pos.ne')).sub
        (Continuous.rpow continuous_const
          (continuous_const.sub (continuous_const.mul continuous_id))
          (fun _ => Or.inl hbaseKmax_pos.ne'))).continuousAt
    have htail_den : ContinuousAt (fun t : ℝ => (m : ℝ) * (2 * t - 1)) s :=
      (continuous_const.mul
        ((continuous_const.mul continuous_id).sub continuous_const)).continuousAt
    have hden_ne : (m : ℝ) * (2 * s - 1) ≠ 0 := (mul_pos hmR (by linarith)).ne'
    exact hsum_cont.continuousAt.add (continuousAt_const.mul (htail_num.div htail_den hden_ne))
  have hev_all : ∀ᶠ t in 𝓝 s, ∀ j : Fin N, (vec.getD j.1 0 : ℝ) < fL j t :=
    Filter.eventually_all.mpr fun j => (hcont j).eventually (Ioi_mem_nhds (hstrict j))
  rw [Metric.eventually_nhds_iff] at hev_all
  obtain ⟨δ, hδ_pos, hδ_prop⟩ := hev_all
  set t : ℝ := s + δ / 2 with ht_def
  have hdist : dist t s < δ := by
    rw [Real.dist_eq, ht_def, show s + δ / 2 - s = δ / 2 by ring,
      abs_of_pos (half_pos hδ_pos)]
    linarith
  have ht_gt : ∀ j : Fin N, (vec.getD j.1 0 : ℝ) < fL j t := hδ_prop hdist
  have hs_lt_t : s < t := by rw [ht_def]; linarith
  have ht_half : 1 / 2 < t := lt_trans hs_half hs_lt_t
  let v : Fin N → ℝ≥0∞ := fun j => ((vec.getD j.1 0 : ℕ) : ℝ≥0∞)
  have hdim_ge : ENNReal.ofReal t ≤ dimH (residueConstSet m r) := by
    refine step_cert_lower_sound hm hr hK hKK hN hcut ht_half v ?_ ?_
      (fun j k => v (binRight N hN (m * k + r) j)) ?_ ?_
    · intro j
      have := hposv j.1 j.2
      change (0 : ℝ≥0∞) < ((vec.getD j.1 0 : ℕ) : ℝ≥0∞)
      exact_mod_cast (by omega : 0 < vec.getD j.1 0)
    · intro j
      exact (ENNReal.natCast_ne_top _).lt_top
    · intro j k _ i _ hR
      have hR' : i.val ≤ (binRight N hN (m * k + r) j).val := hR
      change ((vec.getD (binRight N hN (m * k + r) j).1 0 : ℕ) : ℝ≥0∞) ≤
        ((vec.getD i.1 0 : ℕ) : ℝ≥0∞)
      exact_mod_cast antiOK_getD vec hanti _ _ hR'
        (by rw [hlen]; exact (binRight N hN (m * k + r) j).2)
    · intro j
      have hnn : ∀ k ∈ range K,
          0 ≤ (vec.getD (binRight N hN (m * k + r) j).1 0 : ℝ) *
            (((m * k + r : ℕ) : ℝ) + ((j.1 : ℝ) + 1) / (N : ℝ)) ^ (-(2 * t)) := fun k _ => by
        have hbase : (0 : ℝ) ≤ ((m * k + r : ℕ) : ℝ) + ((j.1 : ℝ) + 1) / (N : ℝ) := by positivity
        exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hbase _)
      have htail_nn : 0 ≤ (vec.getD 0 0 : ℝ) *
          (((((m * K + r + 1 : ℕ) : ℝ) ^ (1 - 2 * t)) -
            (((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * t))) / ((m : ℝ) * (2 * t - 1))) := by
        have hle_base : ((m * K + r + 1 : ℕ) : ℝ) ≤ ((m * Kmax + r + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by nlinarith : m * K + r + 1 ≤ m * Kmax + r + 1)
        have hpow_le : ((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * t) ≤
            ((m * K + r + 1 : ℕ) : ℝ) ^ (1 - 2 * t) :=
          Real.rpow_le_rpow_of_nonpos hbaseK_pos hle_base (by linarith)
        have h2 : 0 < (m : ℝ) * (2 * t - 1) := mul_pos hmR (by linarith)
        exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (sub_nonneg.mpr hpow_le) h2.le)
      have heq_rhs : (∑ k ∈ range K,
            v (binRight N hN (m * k + r) j) *
              ENNReal.ofReal (((m * k + r : ℕ) + ((j.1 : ℝ) + 1) / (N : ℝ)) ^ (-(2 * t)))) +
          v ⟨0, hN⟩ *
            ENNReal.ofReal (((((m * K + r + 1 : ℕ) : ℝ) ^ (1 - 2 * t)) -
              (((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * t))) / ((m : ℝ) * (2 * t - 1))) =
          ENNReal.ofReal (fL j t) := by
        dsimp only [v, fL]
        rw [ENNReal.ofReal_add (Finset.sum_nonneg hnn) htail_nn, ENNReal.ofReal_sum_of_nonneg hnn]
        congr 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      rw [heq_rhs]
      calc v j = ENNReal.ofReal (vec.getD j.1 0 : ℝ) := (ENNReal.ofReal_natCast _).symm
        _ ≤ ENNReal.ofReal (fL j t) := ENNReal.ofReal_le_ofReal (ht_gt j).le
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hs_lt_t) hdim_ge

/-! ### All 20 Strict Open Bounds (`m ∈ {2,3,4,5,6}`, `r ∈ {1, m}`, zero recomputation) -/

theorem lt_dimH_F21 : ENNReal.ofReal (105 / 128 : ℝ) < dimH (residueConstSet 2 1) := by
  have h := lt_dimH_of_certL (m := 2) (r := 1) (K := 258) (Kmax := 1208925819614629174706176)
    (p := 105) (q := 64) (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M2R1L.tail) (l := ResidueCertGen.M2R1L.lt)
    (u := ResidueCertGen.M2R1L.ut) (vec := ResidueCertGen.M2R1L.vec)
    (fun j => (ResidueCertGen.M2R1L.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    ResidueCertGen.M2R1L.vec_ok ResidueCertGen.M2R1L.tail_ok
    (fun j hj => rows_of_chunksL (C := 64) (nc := 8) ResidueCertGen.M2R1L.tab
      ResidueCertGen.M2R1L.tab_length ResidueCertGen.M2R1L.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem dimH_F21_lt : dimH (residueConstSet 2 1) < ENNReal.ofReal (421 / 512 : ℝ) := by
  have h := dimH_lt_of_certU (m := 2) (r := 1) (K := 258) (p := 421) (q := 256)
    (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M2R1U.tail) (u := ResidueCertGen.M2R1U.ut)
    (vec := ResidueCertGen.M2R1U.vec)
    (fun j => (ResidueCertGen.M2R1U.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ResidueCertGen.M2R1U.vec_ok ResidueCertGen.M2R1U.tail_ok
    (fun j hj => rows_of_chunksU (C := 64) (nc := 8) ResidueCertGen.M2R1U.tab
      ResidueCertGen.M2R1U.tab_length ResidueCertGen.M2R1U.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem lt_dimH_F22 : ENNReal.ofReal (23 / 32 : ℝ) < dimH (residueConstSet 2 2) := by
  have h := lt_dimH_of_certL (m := 2) (r := 2) (K := 258) (Kmax := 1208925819614629174706176)
    (p := 23) (q := 16) (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M2R2L.tail) (l := ResidueCertGen.M2R2L.lt)
    (u := ResidueCertGen.M2R2L.ut) (vec := ResidueCertGen.M2R2L.vec)
    (fun j => (ResidueCertGen.M2R2L.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    ResidueCertGen.M2R2L.vec_ok ResidueCertGen.M2R2L.tail_ok
    (fun j hj => rows_of_chunksL (C := 64) (nc := 8) ResidueCertGen.M2R2L.tab
      ResidueCertGen.M2R2L.tab_length ResidueCertGen.M2R2L.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem dimH_F22_lt : dimH (residueConstSet 2 2) < ENNReal.ofReal (369 / 512 : ℝ) := by
  have h := dimH_lt_of_certU (m := 2) (r := 2) (K := 258) (p := 369) (q := 256)
    (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M2R2U.tail) (u := ResidueCertGen.M2R2U.ut)
    (vec := ResidueCertGen.M2R2U.vec)
    (fun j => (ResidueCertGen.M2R2U.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ResidueCertGen.M2R2U.vec_ok ResidueCertGen.M2R2U.tail_ok
    (fun j hj => rows_of_chunksU (C := 64) (nc := 8) ResidueCertGen.M2R2U.tab
      ResidueCertGen.M2R2U.tab_length ResidueCertGen.M2R2U.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem lt_dimH_F31 : ENNReal.ofReal (95 / 128 : ℝ) < dimH (residueConstSet 3 1) := by
  have h := lt_dimH_of_certL (m := 3) (r := 1) (K := 172) (Kmax := 1208925819614629174706176)
    (p := 95) (q := 64) (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M3R1L.tail) (l := ResidueCertGen.M3R1L.lt)
    (u := ResidueCertGen.M3R1L.ut) (vec := ResidueCertGen.M3R1L.vec)
    (fun j => (ResidueCertGen.M3R1L.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    ResidueCertGen.M3R1L.vec_ok ResidueCertGen.M3R1L.tail_ok
    (fun j hj => rows_of_chunksL (C := 64) (nc := 8) ResidueCertGen.M3R1L.tab
      ResidueCertGen.M3R1L.tab_length ResidueCertGen.M3R1L.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem dimH_F31_lt : dimH (residueConstSet 3 1) < ENNReal.ofReal (381 / 512 : ℝ) := by
  have h := dimH_lt_of_certU (m := 3) (r := 1) (K := 172) (p := 381) (q := 256)
    (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M3R1U.tail) (u := ResidueCertGen.M3R1U.ut)
    (vec := ResidueCertGen.M3R1U.vec)
    (fun j => (ResidueCertGen.M3R1U.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ResidueCertGen.M3R1U.vec_ok ResidueCertGen.M3R1U.tail_ok
    (fun j hj => rows_of_chunksU (C := 64) (nc := 8) ResidueCertGen.M3R1U.tab
      ResidueCertGen.M3R1U.tab_length ResidueCertGen.M3R1U.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem lt_dimH_F33 : ENNReal.ofReal (41 / 64 : ℝ) < dimH (residueConstSet 3 3) := by
  have h := lt_dimH_of_certL (m := 3) (r := 3) (K := 172) (Kmax := 1208925819614629174706176)
    (p := 41) (q := 32) (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M3R3L.tail) (l := ResidueCertGen.M3R3L.lt)
    (u := ResidueCertGen.M3R3L.ut) (vec := ResidueCertGen.M3R3L.vec)
    (fun j => (ResidueCertGen.M3R3L.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    ResidueCertGen.M3R3L.vec_ok ResidueCertGen.M3R3L.tail_ok
    (fun j hj => rows_of_chunksL (C := 64) (nc := 8) ResidueCertGen.M3R3L.tab
      ResidueCertGen.M3R3L.tab_length ResidueCertGen.M3R3L.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem dimH_F33_lt : dimH (residueConstSet 3 3) < ENNReal.ofReal (329 / 512 : ℝ) := by
  have h := dimH_lt_of_certU (m := 3) (r := 3) (K := 172) (p := 329) (q := 256)
    (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M3R3U.tail) (u := ResidueCertGen.M3R3U.ut)
    (vec := ResidueCertGen.M3R3U.vec)
    (fun j => (ResidueCertGen.M3R3U.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ResidueCertGen.M3R3U.vec_ok ResidueCertGen.M3R3U.tail_ok
    (fun j hj => rows_of_chunksU (C := 64) (nc := 8) ResidueCertGen.M3R3U.tab
      ResidueCertGen.M3R3U.tab_length ResidueCertGen.M3R3U.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem lt_dimH_F41 : ENNReal.ofReal (357 / 512 : ℝ) < dimH (residueConstSet 4 1) := by
  have h := lt_dimH_of_certL (m := 4) (r := 1) (K := 130) (Kmax := 1208925819614629174706176)
    (p := 357) (q := 256) (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M4R1L.tail) (l := ResidueCertGen.M4R1L.lt)
    (u := ResidueCertGen.M4R1L.ut) (vec := ResidueCertGen.M4R1L.vec)
    (fun j => (ResidueCertGen.M4R1L.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    ResidueCertGen.M4R1L.vec_ok ResidueCertGen.M4R1L.tail_ok
    (fun j hj => rows_of_chunksL (C := 64) (nc := 8) ResidueCertGen.M4R1L.tab
      ResidueCertGen.M4R1L.tab_length ResidueCertGen.M4R1L.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem dimH_F41_lt : dimH (residueConstSet 4 1) < ENNReal.ofReal (179 / 256 : ℝ) := by
  have h := dimH_lt_of_certU (m := 4) (r := 1) (K := 130) (p := 179) (q := 128)
    (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M4R1U.tail) (u := ResidueCertGen.M4R1U.ut)
    (vec := ResidueCertGen.M4R1U.vec)
    (fun j => (ResidueCertGen.M4R1U.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ResidueCertGen.M4R1U.vec_ok ResidueCertGen.M4R1U.tail_ok
    (fun j hj => rows_of_chunksU (C := 64) (nc := 8) ResidueCertGen.M4R1U.tab
      ResidueCertGen.M4R1U.tab_length ResidueCertGen.M4R1U.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem lt_dimH_F44 : ENNReal.ofReal (309 / 512 : ℝ) < dimH (residueConstSet 4 4) := by
  have h := lt_dimH_of_certL (m := 4) (r := 4) (K := 130) (Kmax := 1208925819614629174706176)
    (p := 309) (q := 256) (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M4R4L.tail) (l := ResidueCertGen.M4R4L.lt)
    (u := ResidueCertGen.M4R4L.ut) (vec := ResidueCertGen.M4R4L.vec)
    (fun j => (ResidueCertGen.M4R4L.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    ResidueCertGen.M4R4L.vec_ok ResidueCertGen.M4R4L.tail_ok
    (fun j hj => rows_of_chunksL (C := 64) (nc := 8) ResidueCertGen.M4R4L.tab
      ResidueCertGen.M4R4L.tab_length ResidueCertGen.M4R4L.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem dimH_F44_lt : dimH (residueConstSet 4 4) < ENNReal.ofReal (155 / 256 : ℝ) := by
  have h := dimH_lt_of_certU (m := 4) (r := 4) (K := 130) (p := 155) (q := 128)
    (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M4R4U.tail) (u := ResidueCertGen.M4R4U.ut)
    (vec := ResidueCertGen.M4R4U.vec)
    (fun j => (ResidueCertGen.M4R4U.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ResidueCertGen.M4R4U.vec_ok ResidueCertGen.M4R4U.tail_ok
    (fun j hj => rows_of_chunksU (C := 64) (nc := 8) ResidueCertGen.M4R4U.tab
      ResidueCertGen.M4R4U.tab_length ResidueCertGen.M4R4U.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem lt_dimH_F51 : ENNReal.ofReal (171 / 256 : ℝ) < dimH (residueConstSet 5 1) := by
  have h := lt_dimH_of_certL (m := 5) (r := 1) (K := 120) (Kmax := 1208925819614629174706176)
    (p := 171) (q := 128) (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M5R1L.tail) (l := ResidueCertGen.M5R1L.lt)
    (u := ResidueCertGen.M5R1L.ut) (vec := ResidueCertGen.M5R1L.vec)
    (fun j => (ResidueCertGen.M5R1L.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    ResidueCertGen.M5R1L.vec_ok ResidueCertGen.M5R1L.tail_ok
    (fun j hj => rows_of_chunksL (C := 64) (nc := 8) ResidueCertGen.M5R1L.tab
      ResidueCertGen.M5R1L.tab_length ResidueCertGen.M5R1L.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem dimH_F51_lt : dimH (residueConstSet 5 1) < ENNReal.ofReal (343 / 512 : ℝ) := by
  have h := dimH_lt_of_certU (m := 5) (r := 1) (K := 120) (p := 343) (q := 256)
    (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M5R1U.tail) (u := ResidueCertGen.M5R1U.ut)
    (vec := ResidueCertGen.M5R1U.vec)
    (fun j => (ResidueCertGen.M5R1U.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ResidueCertGen.M5R1U.vec_ok ResidueCertGen.M5R1U.tail_ok
    (fun j hj => rows_of_chunksU (C := 64) (nc := 8) ResidueCertGen.M5R1U.tab
      ResidueCertGen.M5R1U.tab_length ResidueCertGen.M5R1U.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem lt_dimH_F55 : ENNReal.ofReal (149 / 256 : ℝ) < dimH (residueConstSet 5 5) := by
  have h := lt_dimH_of_certL (m := 5) (r := 5) (K := 120) (Kmax := 1208925819614629174706176)
    (p := 149) (q := 128) (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M5R5L.tail) (l := ResidueCertGen.M5R5L.lt)
    (u := ResidueCertGen.M5R5L.ut) (vec := ResidueCertGen.M5R5L.vec)
    (fun j => (ResidueCertGen.M5R5L.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    ResidueCertGen.M5R5L.vec_ok ResidueCertGen.M5R5L.tail_ok
    (fun j hj => rows_of_chunksL (C := 64) (nc := 8) ResidueCertGen.M5R5L.tab
      ResidueCertGen.M5R5L.tab_length ResidueCertGen.M5R5L.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem dimH_F55_lt : dimH (residueConstSet 5 5) < ENNReal.ofReal (299 / 512 : ℝ) := by
  have h := dimH_lt_of_certU (m := 5) (r := 5) (K := 120) (p := 299) (q := 256)
    (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M5R5U.tail) (u := ResidueCertGen.M5R5U.ut)
    (vec := ResidueCertGen.M5R5U.vec)
    (fun j => (ResidueCertGen.M5R5U.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ResidueCertGen.M5R5U.vec_ok ResidueCertGen.M5R5U.tail_ok
    (fun j hj => rows_of_chunksU (C := 64) (nc := 8) ResidueCertGen.M5R5U.tab
      ResidueCertGen.M5R5U.tab_length ResidueCertGen.M5R5U.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem lt_dimH_F61 : ENNReal.ofReal (331 / 512 : ℝ) < dimH (residueConstSet 6 1) := by
  have h := lt_dimH_of_certL (m := 6) (r := 1) (K := 120) (Kmax := 1208925819614629174706176)
    (p := 331) (q := 256) (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M6R1L.tail) (l := ResidueCertGen.M6R1L.lt)
    (u := ResidueCertGen.M6R1L.ut) (vec := ResidueCertGen.M6R1L.vec)
    (fun j => (ResidueCertGen.M6R1L.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    ResidueCertGen.M6R1L.vec_ok ResidueCertGen.M6R1L.tail_ok
    (fun j hj => rows_of_chunksL (C := 64) (nc := 8) ResidueCertGen.M6R1L.tab
      ResidueCertGen.M6R1L.tab_length ResidueCertGen.M6R1L.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem dimH_F61_lt : dimH (residueConstSet 6 1) < ENNReal.ofReal (83 / 128 : ℝ) := by
  have h := dimH_lt_of_certU (m := 6) (r := 1) (K := 120) (p := 83) (q := 64)
    (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M6R1U.tail) (u := ResidueCertGen.M6R1U.ut)
    (vec := ResidueCertGen.M6R1U.vec)
    (fun j => (ResidueCertGen.M6R1U.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ResidueCertGen.M6R1U.vec_ok ResidueCertGen.M6R1U.tail_ok
    (fun j hj => rows_of_chunksU (C := 64) (nc := 8) ResidueCertGen.M6R1U.tab
      ResidueCertGen.M6R1U.tab_length ResidueCertGen.M6R1U.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem lt_dimH_F66 : ENNReal.ofReal (291 / 512 : ℝ) < dimH (residueConstSet 6 6) := by
  have h := lt_dimH_of_certL (m := 6) (r := 6) (K := 120) (Kmax := 1208925819614629174706176)
    (p := 291) (q := 256) (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M6R6L.tail) (l := ResidueCertGen.M6R6L.lt)
    (u := ResidueCertGen.M6R6L.ut) (vec := ResidueCertGen.M6R6L.vec)
    (fun j => (ResidueCertGen.M6R6L.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    ResidueCertGen.M6R6L.vec_ok ResidueCertGen.M6R6L.tail_ok
    (fun j hj => rows_of_chunksL (C := 64) (nc := 8) ResidueCertGen.M6R6L.tab
      ResidueCertGen.M6R6L.tab_length ResidueCertGen.M6R6L.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

theorem dimH_F66_lt : dimH (residueConstSet 6 6) < ENNReal.ofReal (73 / 128 : ℝ) := by
  have h := dimH_lt_of_certU (m := 6) (r := 6) (K := 120) (p := 73) (q := 64)
    (N := 512) (S := 10000000000000)
    (tail := ResidueCertGen.M6R6U.tail) (u := ResidueCertGen.M6R6U.ut)
    (vec := ResidueCertGen.M6R6U.vec)
    (fun j => (ResidueCertGen.M6R6U.tab (j / 64)).getD (j % 64) [])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ResidueCertGen.M6R6U.vec_ok ResidueCertGen.M6R6U.tail_ok
    (fun j hj => rows_of_chunksU (C := 64) (nc := 8) ResidueCertGen.M6R6U.tab
      ResidueCertGen.M6R6U.tab_length ResidueCertGen.M6R6U.tab_ok j (by norm_num; exact hj))
  convert h using 2; norm_num

end ResidueCertStrictOpen
