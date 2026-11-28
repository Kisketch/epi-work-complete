import EpiFormal.R6S2Blocks

/-!
# R6-S2, phase 2b: R6-S1(d) (the realization lemma, `proofs/R6-S2.md` §5.6)

Statement layer (blueprint §0.4): nearest-integer selections are quantified over **all**
tie-breakings (`IsNearSel`, `near_iff_nearest`), the canonical label is
`lab lam k = (lam k : ℤ/K)` for any nearest-integer selection `lam k` of `K y_{n_k+1}`
(`IsLabelSel`), and `r_0` is part of the given data.

`StatementS1d X` is R6-S1(d) for the block Hurwitz number `X`; `S1d` proves it for all `X`,
together with `𝒦_α(β) < ∞` for the constructed `β` (proved in §5.6 (d4)).

Construction (§5.6): `U_j = T'_{j+1}` (block index `j = k - 1`), `x_j = (-1)^{n_{j+1}} U_j`,
`β = (1/K) Σ_j x_j ε_{n_{j+1}} = (1/K) Σ_j U_j |ε_{n_{j+1}}|` (`betaU`). (d1) is `decomp`,
(d2) is `residue`, (d3) are `fut_bound`, `past_bound`, `pre_succ_bound`, `futBig_bound`,
`E_bound`, `lab_err`, (d4) is the assembly in `S1d`.

No proof-escape tactics, no project axioms.
-/

open Filter Topology

namespace R6S2

/-! ## Part 1. Selections and the S1 quantities (statement layer) -/

/-- `ρ` is a nearest-integer selection for `f` (any tie-breaking): `|f n - ρ n| ≤ 1/2` -/
def IsNearSel (f : ℕ → ℝ) (ρ : ℕ → ℤ) : Prop := ∀ n, |f n - ρ n| ≤ 1 / 2

/-- (alignment) `|x - m| ≤ 1/2` iff `m` is a nearest integer to `x` (ties allowed) -/
theorem near_iff_nearest (x : ℝ) (m : ℤ) :
    |x - m| ≤ 1 / 2 ↔ ∀ n : ℤ, |x - m| ≤ |x - n| := by
  constructor
  · intro h n
    by_cases hn : n = m
    · rw [hn]
    · have h1 : (1 : ℝ) ≤ |(m : ℝ) - n| := by
        have : (1 : ℤ) ≤ |m - n| := Int.one_le_abs (sub_ne_zero.2 (Ne.symm hn))
        exact_mod_cast this
      have h2 := abs_sub_le (m : ℝ) x n
      rw [abs_sub_comm (m : ℝ) x] at h2
      linarith
  · intro h
    exact (h (round x)).trans (abs_sub_round x)

namespace BH

variable (X : BH)

/-- `y_n = q_nβ - ρ_n` for a nearest-integer selection `ρ` -/
noncomputable def yv (β : ℝ) (ρ : ℕ → ℤ) (n : ℕ) : ℝ := (q X.a n : ℝ) * β - ρ n

/-- `t_k = A_k y_{n_k}` -/
noncomputable def tv (β : ℝ) (ρ : ℕ → ℤ) (k : ℕ) : ℝ := (X.A k : ℝ) * X.yv β ρ (X.nk k)

/-- label selections: `lam k` is a nearest integer to `K y_{n_k+1}` (any tie-breaking) -/
def IsLabelSel (β : ℝ) (ρ : ℕ → ℤ) (lam : ℕ → ℤ) : Prop :=
  IsNearSel (fun k => (R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1)) lam

/-- canonical label `r_k = round(K y_{n_k+1}) mod K ∈ ℤ/K` -/
def lab (lam : ℕ → ℤ) (k : ℕ) : ZMod (R6S7.contK X.W) := (lam k : ZMod (R6S7.contK X.W))

end BH

/-- **Statement of R6-S1(d)** (realization), for the block Hurwitz number `X`: for every
`(r_k)_{k ≥ 0}` in `ℤ/K` (`r_0` given data) and every bounded real `(τ_k)_{k ≥ 1}` with
`τ_k ∈ (r_k - σ r_{k-1})/K + ℤ`, there is `β` such that, for every tie-breaking of the roundings,
the canonical labels are eventually `r_k` and `t_k - τ_k → 0`. We also record `𝒦_α(β) < ∞`. -/
def StatementS1d (X : BH) : Prop :=
  ∀ (r : ℕ → ZMod (R6S7.contK X.W)) (τ : ℕ → ℝ),
    (∃ B : ℝ, ∀ k, 1 ≤ k → |τ k| ≤ B) →
    (∀ k, 1 ≤ k → ∃ z : ℤ, τ k =
      (((r k).val : ℝ) - (R6S7.sigma X.W : ℝ) * ((r (k-1)).val : ℝ)) / (R6S7.contK X.W : ℝ) + z) →
    ∃ β : ℝ, KL X.a β < ⊤ ∧
      ∀ ρ lam, IsNearSel (fun n => (q X.a n : ℝ) * β) ρ → X.IsLabelSel β ρ lam →
        (∀ᶠ k in atTop, X.lab lam k = r k) ∧
        Tendsto (fun k => X.tv β ρ k - τ k) atTop (𝓝 0)

/-- (alignment) the coset condition `τ ∈ (u - σ v)/K + ℤ` does not depend on the integer
representatives `u, v` of `r_k, r_{k-1}`; `StatementS1d` uses the representatives `val`. -/
theorem coset_indep (K : ℕ) [NeZero K] (σ : ℕ) (r1 r0 : ZMod K) (u v : ℤ)
    (hu : (u : ZMod K) = r1) (hv : (v : ZMod K) = r0) (τ : ℝ) :
    (∃ z : ℤ, τ = ((u : ℝ) - σ * v) / K + z) ↔
      (∃ z : ℤ, τ = ((r1.val : ℝ) - σ * (r0.val : ℝ)) / K + z) := by
  have hK : (0 : ℝ) < K := by have := NeZero.pos K; exact_mod_cast this
  have h1 : ((r1.val : ℤ) : ZMod K) = (u : ZMod K) := by rw [hu]; simp
  have h0 : ((r0.val : ℤ) : ZMod K) = (v : ZMod K) := by rw [hv]; simp
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
  obtain ⟨m', hm'⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h0
  have hmR : (u : ℝ) = r1.val + K * m := by
    have : (u : ℝ) - (r1.val : ℤ) = (K : ℤ) * m := by exact_mod_cast hm
    push_cast at this; linarith
  have hmR' : (v : ℝ) = r0.val + K * m' := by
    have : (v : ℝ) - (r0.val : ℤ) = (K : ℤ) * m' := by exact_mod_cast hm'
    push_cast at this; linarith
  have key : ((u : ℝ) - σ * v) / K = ((r1.val : ℝ) - σ * (r0.val : ℝ)) / K + (m - σ * m' : ℤ) := by
    rw [hmR, hmR']; push_cast; field_simp; ring
  constructor
  · rintro ⟨z, hz⟩; exact ⟨(m - σ * m') + z, by rw [hz, key]; push_cast; ring⟩
  · rintro ⟨z, hz⟩; exact ⟨z - (m - σ * m'), by rw [hz, key]; push_cast; ring⟩

/-! ## Part 2. Auxiliary facts -/

theorem getD_le_sum (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.sum := by
  by_cases h : i < l.length
  · rw [getD_eq_getElem' h]; exact List.le_sum_of_mem (List.getElem_mem h)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact Nat.zero_le _

/-- every index `n ≥ N` is a big index `n_{J+1}`, or `a_{n+1}` is a letter of `W` -/
theorem BH.pos_cases (X : BH) (n : ℕ) (hn : X.N ≤ n) :
    (∃ J, n = X.mm J) ∨ X.a (n+1) ≤ (X.W.sum : ℤ) := by
  have e : n + 1 - X.N - 1 = n - X.N := by omega
  unfold BH.a
  simp only [show n + 1 ≠ 0 by omega, show ¬ (n + 1 ≤ X.N) by omega, ite_false, e]
  split_ifs with h
  · left
    refine ⟨(n - X.N) / (X.ell + 1), ?_⟩
    have := Nat.div_add_mod (n - X.N) (X.ell + 1)
    rw [h, add_zero] at this
    unfold BH.mm; rw [Nat.mul_comm]; omega
  · right; exact_mod_cast getD_le_sum _ _

theorem aux_ratio {A1 A2 q0 Q c : ℝ} (hA1 : 1 ≤ A1) (hA2 : 1 ≤ A2) (hq0 : 0 < q0) (hc : 0 ≤ c)
    (hQ : A1 * A2 * q0 ≤ Q) : A1 * (c * q0 / Q) ≤ c / A2 := by
  have hA : 0 < A1 * A2 := by nlinarith
  have hQp : 0 < Q := by have := mul_pos hA hq0; linarith
  rw [mul_div_assoc', div_le_div_iff₀ hQp (by linarith)]
  have := mul_le_mul_of_nonneg_left hQ hc
  nlinarith

theorem BH.Qchain (X : BH) (J : ℕ) :
    (X.A (J+2) : ℝ) * X.A (J+1) * q X.a (X.mm J) ≤ q X.a (X.mm (J+1) + 1) := by
  have h1 := X.q_step_mm (J+1)
  have h2 : (q X.a (X.mm J + 1) : ℝ) ≤ q X.a (X.mm (J+1)) := qR_mono X.isCF (X.mm_step J)
  have h3 := X.q_step_mm J
  have hA := X.A_succ_pos (J+1)
  have : (X.A (J+2) : ℝ) * (X.A (J+1) * q X.a (X.mm J)) ≤ X.A (J+2) * q X.a (X.mm (J+1)) :=
    mul_le_mul_of_nonneg_left (h3.trans h2) (by linarith)
  linarith

/-! ## Part 3. The construction (§5.6) -/

section Core

variable (X : BH) (U : ℕ → ℤ)

/-- `x_j = (-1)^{n_{j+1}} U_j` -/
def xs (j : ℕ) : ℤ := (-1) ^ (X.mm j) * U j

/-- `β = (1/K) Σ_j x_j ε_{n_{j+1}}` -/
noncomputable def betaU : ℝ := (∑' j, (xs X U j : ℝ) * eps X.a (X.mm j)) / R6S7.contK X.W

/-- `P^{(J)}_n = Σ_{i ≤ J} x_i D(n_{i+1}, n) ∈ ℤ` -/
def PP (J n : ℕ) : ℤ := ∑ i ∈ Finset.range (J+1), xs X U i * Dm X.a (X.mm i) n

/-- `Σ_{i ≤ J} x_i q_{n_{i+1}}` -/
noncomputable def past (J : ℕ) : ℝ := ∑ i ∈ Finset.range (J+1), (xs X U i : ℝ) * q X.a (X.mm i)

/-- `Σ_{i < J} x_i q_{n_{i+1}}` -/
noncomputable def pre (J : ℕ) : ℝ := ∑ i ∈ Finset.range J, (xs X U i : ℝ) * q X.a (X.mm i)

/-- `K E^{fut}_n = Σ_{i > J} x_i q_n ε_{n_{i+1}}` -/
noncomputable def fut (J n : ℕ) : ℝ :=
  ∑' i, (q X.a n : ℝ) * ((xs X U (i + (J+1)) : ℝ) * eps X.a (X.mm (i + (J+1))))

theorem Kpos : (0 : ℝ) < R6S7.contK X.W := by
  have := R6S7.contK_pos X.W X.hW; exact_mod_cast (by omega : 0 < R6S7.contK X.W)

theorem Kge1 : (1 : ℝ) ≤ R6S7.contK X.W := by exact_mod_cast R6S7.contK_pos X.W X.hW

theorem neg_one_pow_mul_self (m : ℕ) : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

theorem xs_eps (j : ℕ) : (xs X U j : ℝ) * eps X.a (X.mm j) = U j * |eps X.a (X.mm j)| := by
  have h := eps_sign X.isCF (X.mm j)
  have h1 := neg_one_pow_mul_self (X.mm j)
  unfold xs; push_cast
  set e := |eps X.a (X.mm j)|
  rw [h]
  linear_combination ((U j : ℝ) * e) * h1

theorem abs_xs (j : ℕ) : |(xs X U j : ℝ)| = |(U j : ℝ)| := by
  unfold xs; push_cast
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

theorem xs_Dm_succ (j : ℕ) : xs X U j * Dm X.a (X.mm j) (X.mm j + 1) = U j := by
  rw [Dm_succ]; unfold xs
  have : ((-1 : ℤ) ^ (X.mm j)) * (-1) ^ (X.mm j) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination U j * this

theorem xs_q_eps (J : ℕ) : (xs X U J : ℝ) * q X.a (X.mm J) * eps X.a (X.mm J)
    = U J * theta X.a (X.mm J) := by
  rw [mul_right_comm, xs_eps, theta_eq_mul]; ring

theorem past_eq (J : ℕ) : past X U J = pre X U J + (xs X U J : ℝ) * q X.a (X.mm J) :=
  Finset.sum_range_succ _ _

theorem pre_succ (J : ℕ) : pre X U (J+1) = past X U J := rfl

theorem pre_zero : pre X U 0 = 0 := by simp [pre]

variable {C : ℝ} (hU : ∀ j, |(U j : ℝ)| ≤ C)
include hU

theorem C_nonneg : 0 ≤ C := (abs_nonneg _).trans (hU 0)

theorem xs_bound (j : ℕ) :
    ‖(xs X U j : ℝ) * eps X.a (X.mm j)‖ ≤ C * (1 / q X.a (X.mm j + 1)) := by
  rw [Real.norm_eq_abs, abs_mul, abs_xs]
  exact mul_le_mul (hU j) (abs_eps_lt X.isCF _).le (abs_nonneg _) (C_nonneg U hU)

theorem summ : Summable (fun j => (xs X U j : ℝ) * eps X.a (X.mm j)) := by
  have hs := (D4ii_mm X 0).1
  simp only [zero_add] at hs
  exact Summable.of_norm_bounded (hs.mul_left C) (xs_bound X U hU)

/-- (d1) exact decomposition: `K q_n β = P^{(J)}_n + (Σ_{i ≤ J} x_i q_{n_{i+1}}) ε_n + fut` -/
theorem decomp (n J : ℕ) :
    (R6S7.contK X.W : ℝ) * ((q X.a n : ℝ) * betaU X U) =
      PP X U J n + past X U J * eps X.a n + fut X U J n := by
  have hK := Kpos X
  have hs := (summ X U hU).mul_left (q X.a n : ℝ)
  have hsplit := hs.sum_add_tsum_nat_add (J+1)
  have e1 : (R6S7.contK X.W : ℝ) * ((q X.a n : ℝ) * betaU X U) =
      ∑' j, (q X.a n : ℝ) * ((xs X U j : ℝ) * eps X.a (X.mm j)) := by
    rw [tsum_mul_left, betaU]; field_simp
  rw [e1, ← hsplit]
  have e2 : ∑ i ∈ Finset.range (J+1), (q X.a n : ℝ) * ((xs X U i : ℝ) * eps X.a (X.mm i)) =
      (PP X U J n : ℝ) + past X U J * eps X.a n := by
    simp only [PP, past, Finset.sum_mul, Int.cast_sum, ← Finset.sum_add_distrib, Int.cast_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have := D3_eq X.a (X.mm i) n
    linear_combination (xs X U i : ℝ) * this
  rw [e2]; rfl

/-- (d3) future part: `|K E^{fut}_n| ≤ C q_n · 4/q_{n_{J+2}+1}` (D4 (ii)) -/
theorem fut_bound (n J : ℕ) :
    |fut X U J n| ≤ C * q X.a n * (4 / q X.a (X.mm (J+1) + 1)) := by
  obtain ⟨hs, hle⟩ := D4ii_mm X (J+1)
  have hq := qR_pos X.isCF n
  have hC := C_nonneg U hU
  have hg := (hs.mul_left (C * q X.a n)).hasSum
  have hb : ‖∑' i, (q X.a n : ℝ) * ((xs X U (i + (J+1)) : ℝ) * eps X.a (X.mm (i + (J+1))))‖ ≤
      ∑' i, C * q X.a n * (1 / (q X.a (X.mm (J + 1 + i) + 1) : ℝ)) :=
    tsum_of_norm_bounded hg (fun i => by
      have h1 := xs_bound X U hU (i + (J+1))
      rw [show i + (J+1) = J + 1 + i by ring, Real.norm_eq_abs] at h1
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hq, show i + (J+1) = J + 1 + i by ring]
      have h2 := mul_le_mul_of_nonneg_left h1 hq.le
      linarith)
  have e : ∑' i, C * q X.a n * (1 / (q X.a (X.mm (J + 1 + i) + 1) : ℝ)) =
      C * q X.a n * ∑' i, 1 / (q X.a (X.mm (J + 1 + i) + 1) : ℝ) := tsum_mul_left
  calc |fut X U J n| = ‖∑' i, (q X.a n : ℝ) * ((xs X U (i + (J+1)) : ℝ) *
        eps X.a (X.mm (i + (J+1))))‖ := rfl
    _ ≤ _ := hb.trans_eq e
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (by positivity)

/-- (d3) past part: `|Σ_{i ≤ J} x_i q_{n_{i+1}}| ≤ 4 C q_{n_{J+1}}` (D4 (i)) -/
theorem past_bound (J : ℕ) : |past X U J| ≤ 4 * C * q X.a (X.mm J) := by
  have hC := C_nonneg U hU
  have h1 : |past X U J| ≤ ∑ i ∈ Finset.range (J+1), C * q X.a (X.mm i) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_xs, abs_of_pos (qR_pos X.isCF _)]
    exact mul_le_mul_of_nonneg_right (hU i) (qR_pos X.isCF _).le
  rw [← Finset.mul_sum] at h1
  have h2 := D4i_mm X J
  have := mul_le_mul_of_nonneg_left h2 hC
  linarith

/-- big index decomposition: `K q_{n_{J+1}} β - P^{(J)}_{n_{J+1}} = U_J θ + pre + fut` -/
theorem big_decomp (J : ℕ) :
    (R6S7.contK X.W : ℝ) * ((q X.a (X.mm J) : ℝ) * betaU X U) - PP X U J (X.mm J) =
      U J * theta X.a (X.mm J) + pre X U J * eps X.a (X.mm J) + fut X U J (X.mm J) := by
  rw [decomp X U hU (X.mm J) J, past_eq, add_mul, xs_q_eps]; ring

/-- (d3) `n = n_k`, past part beyond the diagonal term: `A_k |…| ≤ 4C/A_{k-1}` -/
theorem pre_succ_bound (J : ℕ) :
    (X.A (J+2) : ℝ) * |pre X U (J+1) * eps X.a (X.mm (J+1))| ≤ 4 * C / X.A (J+1) := by
  have hC := C_nonneg U hU
  have hp := past_bound X U hU J
  have he := (abs_eps_lt X.isCF (X.mm (J+1))).le
  have hq := qR_pos X.isCF (X.mm J)
  have hQ := qR_pos X.isCF (X.mm (J+1) + 1)
  have hA2 := X.A_succ_pos (J+1)
  have key := aux_ratio (X.A_succ_pos (J+1)) (X.A_succ_pos J) hq (by positivity : 0 ≤ 4 * C)
    (X.Qchain J)
  rw [pre_succ, abs_mul]
  have : |past X U J| * |eps X.a (X.mm (J+1))| ≤ 4 * C * q X.a (X.mm J) / q X.a (X.mm (J+1) + 1) := by
    calc |past X U J| * |eps X.a (X.mm (J+1))| ≤ (4 * C * q X.a (X.mm J)) *
          (1 / q X.a (X.mm (J+1) + 1)) :=
          mul_le_mul hp he (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc (X.A (J+2) : ℝ) * (|past X U J| * |eps X.a (X.mm (J+1))|)
      ≤ X.A (J+2) * (4 * C * q X.a (X.mm J) / q X.a (X.mm (J+1) + 1)) :=
        mul_le_mul_of_nonneg_left this (by linarith)
    _ ≤ _ := key

/-- (d3) `n = n_k`, future part: `A_k |K E^{fut}_{n_k}| ≤ 4C/A_{k+1}` -/
theorem futBig_bound (J : ℕ) :
    (X.A (J+1) : ℝ) * |fut X U J (X.mm J)| ≤ 4 * C / X.A (J+2) := by
  have hC := C_nonneg U hU
  have hf := fut_bound X U hU (X.mm J) J
  have hq := qR_pos X.isCF (X.mm J)
  have hA1 := X.A_succ_pos J
  have key := aux_ratio (X.A_succ_pos J) (X.A_succ_pos (J+1)) hq (by positivity : 0 ≤ 4 * C)
    (by have := X.Qchain J; linarith [mul_comm (X.A (J+2) : ℝ) (X.A (J+1))])
  calc (X.A (J+1) : ℝ) * |fut X U J (X.mm J)|
      ≤ X.A (J+1) * (C * q X.a (X.mm J) * (4 / q X.a (X.mm (J+1) + 1))) :=
        mul_le_mul_of_nonneg_left hf (by linarith)
    _ = X.A (J+1) * (4 * C * q X.a (X.mm J) / q X.a (X.mm (J+1) + 1)) := by ring
    _ ≤ _ := key

/-- (d3) `n = n_k`: `A_k |K q_{n_k}β - P_{n_k}| ≤ 9C` -/
theorem E_bound (J : ℕ) :
    (X.A (J+1) : ℝ) * |(R6S7.contK X.W : ℝ) * ((q X.a (X.mm J) : ℝ) * betaU X U)
      - PP X U J (X.mm J)| ≤ 9 * C := by
  have hC := C_nonneg U hU
  have hA := X.A_succ_pos J
  rw [big_decomp X U hU J]
  have h1 : (X.A (J+1) : ℝ) * |(U J : ℝ) * theta X.a (X.mm J)| ≤ C := by
    have ht := X.theta_pos (X.mm J)
    have hlt := X.A_theta_lt_one (J+1) (by omega)
    rw [X.nk_eq_mm] at hlt
    rw [abs_mul, abs_of_pos ht]
    nlinarith [hU J, abs_nonneg (U J : ℝ)]
  have h2 : (X.A (J+1) : ℝ) * |pre X U J * eps X.a (X.mm J)| ≤ 4 * C := by
    rcases J with _ | J
    · simp [pre_zero]; linarith
    · have := pre_succ_bound X U hU J
      have hA' := X.A_succ_pos J
      have : 4 * C / X.A (J+1) ≤ 4 * C := div_le_self (by positivity) hA'
      linarith
  have h3 : (X.A (J+1) : ℝ) * |fut X U J (X.mm J)| ≤ 4 * C := by
    have := futBig_bound X U hU J
    have : 4 * C / X.A (J+2) ≤ 4 * C := div_le_self (by positivity) (X.A_succ_pos (J+1))
    linarith
  have htri := abs_add_three ((U J : ℝ) * theta X.a (X.mm J)) (pre X U J * eps X.a (X.mm J))
    (fut X U J (X.mm J))
  have := mul_le_mul_of_nonneg_left htri (by linarith : (0 : ℝ) ≤ X.A (J+1))
  nlinarith

/-- (d3) label position `n = n_k + 1`: `|K q_{n_k+1}β - P_{n_k+1}| ≤ 4C/A_k + 4C/A_{k+1}` -/
theorem lab_err (J : ℕ) :
    |(R6S7.contK X.W : ℝ) * ((q X.a (X.mm J + 1) : ℝ) * betaU X U) - PP X U J (X.mm J + 1)|
      ≤ 4 * C / X.A (J+1) + 4 * C / X.A (J+2) := by
  have hC := C_nonneg U hU
  rw [decomp X U hU (X.mm J + 1) J,
    show ∀ a b c : ℝ, a + b + c - a = b + c from fun a b c => by ring]
  have hp := past_bound X U hU J
  have he := (abs_eps_lt X.isCF (X.mm J + 1)).le
  have hq := qR_pos X.isCF (X.mm J)
  have hq1 := qR_pos X.isCF (X.mm J + 1)
  have hQ2 := qR_pos X.isCF (X.mm J + 1 + 1)
  have h1 : |past X U J * eps X.a (X.mm J + 1)| ≤ 4 * C / X.A (J+1) := by
    have key := aux_ratio le_rfl (X.A_succ_pos J) hq (by positivity : 0 ≤ 4 * C)
      (by have := X.q_step_mm J; have := qR_mono X.isCF (Nat.le_succ (X.mm J + 1)); linarith)
    rw [abs_mul]
    calc |past X U J| * |eps X.a (X.mm J + 1)| ≤ (4 * C * q X.a (X.mm J)) *
          (1 / q X.a (X.mm J + 1 + 1)) := mul_le_mul hp he (abs_nonneg _) (by positivity)
      _ = 1 * (4 * C * q X.a (X.mm J) / q X.a (X.mm J + 1 + 1)) := by ring
      _ ≤ _ := key
  have h2 : |fut X U J (X.mm J + 1)| ≤ 4 * C / X.A (J+2) := by
    have hf := fut_bound X U hU (X.mm J + 1) J
    have key := aux_ratio le_rfl (X.A_succ_pos (J+1)) hq1 (by positivity : 0 ≤ 4 * C)
      (by have := X.q_step_mm (J+1); have := qR_mono X.isCF (X.mm_step J)
          have := X.A_succ_pos (J+1)
          nlinarith)
    calc |fut X U J (X.mm J + 1)| ≤ C * q X.a (X.mm J + 1) * (4 / q X.a (X.mm (J+1) + 1)) := hf
      _ = 1 * (4 * C * q X.a (X.mm J + 1) / q X.a (X.mm (J+1) + 1)) := by ring
      _ ≤ _ := key
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

end Core

/-! ## Part 4. (d2) residues modulo `K` -/

section Residue

variable (X : BH) (U : ℕ → ℤ)

theorem PP_rec (J n : ℕ) : PP X U J (n+2) = X.a (n+2) * PP X U J (n+1) + PP X U J n := by
  simp only [PP, Dm_rec, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem PP_succ (J n : ℕ) :
    PP X U (J+1) n = PP X U J n + xs X U (J+1) * Dm X.a (X.mm (J+1)) n :=
  Finset.sum_range_succ _ _

/-- (d2): `P^{(J)}_{n_{J+1}} ≡ 0` and `s_J = P^{(J)}_{n_{J+1}+1} ≡ r_{J+1} (mod K)` -/
theorem residue (r : ℕ → ZMod (R6S7.contK X.W))
    (h0 : (U 0 : ZMod (R6S7.contK X.W)) = r 1)
    (h1 : ∀ j, (U (j+1) : ZMod (R6S7.contK X.W)) =
      r (j+2) - (R6S7.sigma X.W : ZMod (R6S7.contK X.W)) * r (j+1)) :
    ∀ J, (PP X U J (X.mm J) : ZMod (R6S7.contK X.W)) = 0 ∧
      (PP X U J (X.mm J + 1) : ZMod (R6S7.contK X.W)) = r (J+1) := by
  by_cases hl : X.ell = 0
  · have hW : X.W = [] := List.eq_nil_of_length_eq_zero hl
    have hK1 : R6S7.contK X.W = 1 := by rw [hW]; rfl
    have : Subsingleton (ZMod (R6S7.contK X.W)) := ZMod.subsingleton_iff.2 hK1
    intro J; exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hl1 : 1 ≤ X.W.length := by have := X.ell_def; omega
  have link := R6S7.link X.W X.hW
  have hcK : R6S7.cseq X.W (X.W.length + 1) = R6S7.contK X.W := link.2.2.2.2.2.2.2.1
  have hcσ : R6S7.cseq X.W X.W.length = R6S7.sigma X.W := by
    simp only [R6S7.cseq, R6S7.sigma, show X.W.length ≠ 0 by omega, ite_false,
      List.dropLast_eq_take]
  intro J
  induction J with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [PP, Dm_self]
    · simp only [PP, zero_add, Finset.sum_range_one]
      rw [xs_Dm_succ, h0]
  | succ J ih =>
    obtain ⟨ih0, ih1⟩ := ih
    set Xs : ℕ → ZMod (R6S7.contK X.W) := fun n => (PP X U J n : ZMod (R6S7.contK X.W))
      with hXs
    have hrec : ∀ i (hi : i < X.W.length), Xs (X.mm J + i + 2) =
        (X.W[i] : ZMod (R6S7.contK X.W)) * Xs (X.mm J + i + 1) + Xs (X.mm J + i) := by
      intro i hi
      simp only [hXs]
      rw [PP_rec]
      have ha : X.a (X.mm J + i + 2) = (X.W[i] : ℤ) := by
        rw [show X.mm J + i + 2 = X.nk (J+1) + 1 + (i+1) by rw [X.nk_eq_mm]; ring,
          X.a_word (J+1) (i+1) (by omega) (by have := X.ell_def; omega)]
        rfl
      rw [ha]; push_cast; ring
    have hA := A1 X.W X.hW Xs (X.mm J) hrec
    have hmm : X.mm (J+1) = X.mm J + 1 + X.W.length := by rw [X.mm_succ, X.ell_def]; ring
    have e1 : Xs (X.mm (J+1)) = 0 := by
      rw [hmm, hA X.W.length le_rfl, hcK, ZMod.natCast_self]
      simp only [hXs] at ih0 ⊢
      rw [ih0]; ring
    have e2 : Xs (X.mm (J+1) + 1) = (R6S7.sigma X.W : ZMod (R6S7.contK X.W)) * r (J+1) := by
      have h3 := hA (X.W.length - 1) (by omega)
      rw [show X.W.length - 1 + 1 = X.W.length by omega, hcσ] at h3
      have hrec2 := PP_rec X U J (X.mm J + 1 + (X.W.length - 1))
      have i1 : X.mm J + 1 + (X.W.length - 1) + 2 = X.mm (J+1) + 1 := by rw [hmm]; omega
      have i2 : X.mm J + 1 + (X.W.length - 1) + 1 = X.mm (J+1) := by rw [hmm]; omega
      rw [i1, i2] at hrec2
      simp only [hXs] at h3 e1 ih0 ih1 ⊢
      rw [hrec2]; push_cast
      rw [e1, h3, ih0, ih1]; ring
    refine ⟨?_, ?_⟩
    · rw [PP_succ, Dm_self, mul_zero, add_zero]; exact e1
    · rw [PP_succ, xs_Dm_succ]; push_cast
      simp only [hXs] at e2
      rw [e2, h1 J]; ring

end Residue

/-! ## Part 5. R6-S1(d) -/

/-- **R6-S1(d)** (realization), for every block Hurwitz number. -/
theorem S1d (X : BH) : StatementS1d X := by
  intro r τ ⟨B, hB⟩ hτ
  -- data
  have hK1 : 1 ≤ (R6S7.contK X.W) := R6S7.contK_pos X.W X.hW
  have : NeZero (R6S7.contK X.W) := ⟨by omega⟩
  have hKR : (0 : ℝ) < (R6S7.contK X.W) := by exact_mod_cast (by omega : 0 < (R6S7.contK X.W))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1 le_rfl)
  have hτ' : ∀ k, ∃ z : ℤ, 1 ≤ k → τ k =
      (((r k).val : ℝ) - ((R6S7.sigma X.W) : ℝ) * ((r (k-1)).val : ℝ)) / ((R6S7.contK X.W) : ℝ) + z := by
    intro k
    by_cases hk : 1 ≤ k
    · obtain ⟨z, hz⟩ := hτ k hk; exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose z hz using hτ'
  -- `U_j = T'_{j+1}`
  set U : ℕ → ℤ := fun j => ((r (j+1)).val : ℤ) - ((R6S7.sigma X.W) : ℤ) * (r j).val + ((R6S7.contK X.W) : ℤ) * z (j+1)
    + (if j = 0 then ((R6S7.sigma X.W) : ℤ) * (r 0).val else 0) with hUdef
  have hUR : ∀ j, (U j : ℝ) = ((R6S7.contK X.W) : ℝ) * τ (j+1) + (if j = 0 then ((R6S7.sigma X.W) : ℝ) * (r 0).val else 0) := by
    intro j
    have h := hz (j+1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    simp only [hUdef]
    rw [h]
    push_cast
    split_ifs <;> field_simp
  have hUZ : ∀ j, (U j : ZMod (R6S7.contK X.W)) = r (j+1) - ((R6S7.sigma X.W) : ZMod (R6S7.contK X.W)) * r j
      + (if j = 0 then ((R6S7.sigma X.W) : ZMod (R6S7.contK X.W)) * r 0 else 0) := by
    intro j
    simp only [hUdef]
    push_cast
    split_ifs <;> simp
  set C : ℝ := ((R6S7.contK X.W) : ℝ) * B + ((R6S7.sigma X.W) : ℝ) * (R6S7.contK X.W) with hCdef
  have hU : ∀ j, |(U j : ℝ)| ≤ C := by
    intro j
    rw [hUR j]
    have h1 : |((R6S7.contK X.W) : ℝ) * τ (j+1)| ≤ (R6S7.contK X.W) * B := by
      rw [abs_mul, abs_of_pos hKR]; exact mul_le_mul_of_nonneg_left (hB _ (by omega)) hKR.le
    have h2 : |(if j = 0 then ((R6S7.sigma X.W) : ℝ) * (r 0).val else 0)| ≤ (R6S7.sigma X.W) * (R6S7.contK X.W) := by
      split_ifs
      · rw [abs_of_nonneg (by positivity)]
        have : ((r 0).val : ℝ) ≤ (R6S7.contK X.W) := by exact_mod_cast (ZMod.val_lt (r 0)).le
        exact mul_le_mul_of_nonneg_left this (by positivity)
      · simp; positivity
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hC0 : 0 ≤ C := C_nonneg U hU
  have hres := residue X U r (by rw [hUZ 0]; simp) (fun j => by rw [hUZ (j+1)]; simp)
  set β := betaU X U with hβ
  -- integrality of `P^{(J)}_{n_{J+1}} / (R6S7.contK X.W)`
  have hw : ∀ J, ∃ w : ℤ, PP X U J (X.mm J) = ((R6S7.contK X.W) : ℤ) * w := fun J =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (hres J).1
  choose w hwJ using hw
  -- `E_J := (R6S7.contK X.W) q_{n_{J+1}} β - (R6S7.contK X.W) w_J`
  have hEb : ∀ J, (X.A (J+1) : ℝ) * |((R6S7.contK X.W) : ℝ) * ((q X.a (X.mm J) : ℝ) * β) - (R6S7.contK X.W) * w J| ≤ 9 * C := by
    intro J
    have := E_bound X U hU J
    rw [hwJ J] at this; push_cast at this; exact this
  have hdist : ∀ J, |(q X.a (X.mm J) : ℝ) * β - w J| ≤ 9 * C / (R6S7.contK X.W) / X.A (J+1) := by
    intro J
    have hA := X.A_succ_pos J
    have h := hEb J
    rw [← mul_sub, abs_mul, abs_of_pos hKR] at h
    rw [div_div, le_div_iff₀ (by positivity)]
    nlinarith
  refine ⟨β, ?_, ?_⟩
  · ---------------- `𝒦_α(β) < ∞`
    refine KL_lt_top_of_bdd X.a β (max (27 * C / (R6S7.contK X.W)) (((X.W.sum : ℝ) + 2) / 2)) ?_
    filter_upwards [eventually_ge_atTop X.N] with n hn
    have ht := X.theta_pos n
    rcases X.pos_cases n hn with ⟨J, rfl⟩ | hlet
    · refine le_trans ?_ (le_max_left _ _)
      have hA := X.A_succ_pos J
      have h1 : dist0 ((q X.a (X.mm J) : ℝ) * β) ≤ 9 * C / (R6S7.contK X.W) / X.A (J+1) :=
        (round_le _ (w J)).trans (hdist J)
      have h2 : 1 / theta X.a (X.mm J) ≤ 3 * X.A (J+1) := by
        have := (inv_theta_mem X.isCF (X.mm J)).2
        rw [X.a_mm J] at this; push_cast at this; linarith
      rw [div_eq_mul_one_div]
      calc dist0 ((q X.a (X.mm J) : ℝ) * β) * (1 / theta X.a (X.mm J))
          ≤ (9 * C / (R6S7.contK X.W) / X.A (J+1)) * (3 * X.A (J+1)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 27 * C / (R6S7.contK X.W) := by field_simp; ring
    · refine le_trans ?_ (le_max_right _ _)
      have h1 : dist0 ((q X.a n : ℝ) * β) ≤ 1 / 2 := abs_sub_round _
      have h2 : 1 / theta X.a n ≤ (X.W.sum : ℝ) + 2 := by
        have := (inv_theta_mem X.isCF n).2
        have h' := (Int.cast_le (R := ℝ)).2 hlet
        rw [Int.cast_natCast] at h'
        linarith
      rw [div_eq_mul_one_div]
      calc dist0 ((q X.a n : ℝ) * β) * (1 / theta X.a n) ≤ (1 / 2) * ((X.W.sum : ℝ) + 2) :=
            mul_le_mul h1 h2 (by positivity) (by norm_num)
        _ = _ := by ring
  · ---------------- labels and `t_k - τ_k → 0`, for every tie-breaking
    intro ρ lam hρ hl
    have hAinv1 : Tendsto (fun J => 1 / (X.A (J+1) : ℝ)) atTop (𝓝 0) :=
      X.A_inv_tendsto.comp (tendsto_add_atTop_nat 1)
    have hAinv2 : Tendsto (fun J => 1 / (X.A (J+2) : ℝ)) atTop (𝓝 0) :=
      X.A_inv_tendsto.comp (tendsto_add_atTop_nat 2)
    have hAinv3 : Tendsto (fun J => 1 / (X.A (J+3) : ℝ)) atTop (𝓝 0) :=
      X.A_inv_tendsto.comp (tendsto_add_atTop_nat 3)
    refine ⟨?_, ?_⟩
    · -- canonical labels
      have hg : Tendsto (fun J => 4 * C * (1 / (X.A (J+1) : ℝ)) + 4 * C * (1 / (X.A (J+2) : ℝ)))
          atTop (𝓝 0) := by
        simpa using (hAinv1.const_mul (4 * C)).add (hAinv2.const_mul (4 * C))
      have hev := (tendsto_order.1 hg).2 (1 / 2) (by norm_num)
      rw [← tendsto_add_atTop_iff_nat 1] at hg
      rw [eventually_atTop] at hev ⊢
      obtain ⟨J0, hJ0⟩ := hev
      refine ⟨J0 + 1, fun k hk => ?_⟩
      obtain ⟨J, rfl⟩ : ∃ J, k = J + 1 := ⟨k - 1, by omega⟩
      have hsmall := hJ0 J (by omega)
      have herr := lab_err X U hU J
      have hsel := hl (J+1)
      simp only [BH.yv, X.nk_eq_mm] at hsel
      -- `lam_{J+1} = P^{(J)}_{n+1} - (R6S7.contK X.W) ρ_{n+1}`
      have hint : lam (J+1) = PP X U J (X.mm J + 1) - ((R6S7.contK X.W) : ℤ) * ρ (X.mm J + 1) := by
        have hlt : |((lam (J+1) - (PP X U J (X.mm J + 1) - ((R6S7.contK X.W) : ℤ) * ρ (X.mm J + 1)) : ℤ) : ℝ)|
            < 1 := by
          push_cast
          have e : (lam (J+1) : ℝ) - ((PP X U J (X.mm J + 1) : ℝ) - (R6S7.contK X.W) * ρ (X.mm J + 1)) =
              (((R6S7.contK X.W) : ℝ) * ((q X.a (X.mm J + 1) : ℝ) * β) - PP X U J (X.mm J + 1)) -
              (((R6S7.contK X.W) : ℝ) * ((q X.a (X.mm J + 1) : ℝ) * β - ρ (X.mm J + 1)) - lam (J+1)) := by ring
          rw [e]
          calc _ ≤ |((R6S7.contK X.W) : ℝ) * ((q X.a (X.mm J + 1) : ℝ) * β) - PP X U J (X.mm J + 1)| +
                |((R6S7.contK X.W) : ℝ) * ((q X.a (X.mm J + 1) : ℝ) * β - ρ (X.mm J + 1)) - lam (J+1)| :=
                abs_sub _ _
            _ ≤ (4 * C / X.A (J+1) + 4 * C / X.A (J+2)) + 1 / 2 := add_le_add herr hsel
            _ < 1 := by
              have : 4 * C / X.A (J+1) + 4 * C / X.A (J+2) < 1 / 2 := by
                have e : 4 * C / (X.A (J+1) : ℝ) + 4 * C / X.A (J+2) =
                    4 * C * (1 / (X.A (J+1) : ℝ)) + 4 * C * (1 / (X.A (J+2) : ℝ)) := by ring
                rw [e]; exact hsmall
              linarith
        have := Int.abs_lt_one_iff.1 (by exact_mod_cast hlt)
        linarith
      simp only [BH.lab]
      rw [hint]; push_cast
      rw [ZMod.natCast_self, zero_mul, sub_zero]
      exact (hres J).2
    · -- `t_k - τ_k → 0`
      -- eventually `ρ_{n_{J+1}} = w_J`
      have hd : Tendsto (fun J => 9 * C / (R6S7.contK X.W) * (1 / (X.A (J+1) : ℝ))) atTop (𝓝 0) := by
        simpa using hAinv1.const_mul (9 * C / (R6S7.contK X.W))
      have hev := (tendsto_order.1 hd).2 (1 / 2) (by norm_num)
      have hρw : ∀ᶠ J in atTop, ρ (X.mm J) = w J := by
        filter_upwards [hev] with J hJ
        have h1 := hdist J
        have h2 := hρ (X.mm J)
        simp only at h2
        have hlt : |((ρ (X.mm J) - w J : ℤ) : ℝ)| < 1 := by
          push_cast
          have e : (ρ (X.mm J) : ℝ) - w J =
              ((q X.a (X.mm J) : ℝ) * β - w J) - ((q X.a (X.mm J) : ℝ) * β - ρ (X.mm J)) := by
            ring
          rw [e]
          have : 9 * C / (R6S7.contK X.W) / X.A (J+1) < 1 / 2 := by
            have e2 : 9 * C / (R6S7.contK X.W : ℝ) / X.A (J+1) =
                9 * C / (R6S7.contK X.W : ℝ) * (1 / X.A (J+1)) := by ring
            rw [e2]; exact hJ
          calc _ ≤ |(q X.a (X.mm J) : ℝ) * β - w J| + |(q X.a (X.mm J) : ℝ) * β - ρ (X.mm J)| :=
                abs_sub _ _
            _ < 1 := by linarith
        have := Int.abs_lt_one_iff.1 (by exact_mod_cast hlt)
        linarith
      -- bound on `t_{J+2} - τ_{J+2}`
      have hθ : Tendsto (fun J => |(X.A (J+2) : ℝ) * theta X.a (X.mm (J+1)) - 1|) atTop (𝓝 0) := by
        have h := (X.A_theta_tendsto.comp (tendsto_add_atTop_nat 2)).sub_const 1
        simp only [sub_self] at h
        have h' := h.abs
        rw [abs_zero] at h'
        refine h'.congr (fun J => ?_)
        simp only [Function.comp_apply, show J + 2 = (J+1) + 1 by ring, X.nk_eq_mm]
      have hbound : Tendsto (fun J => B * |(X.A (J+2) : ℝ) * theta X.a (X.mm (J+1)) - 1|
          + (4 * C * (1 / (X.A (J+1) : ℝ)) + 4 * C * (1 / (X.A (J+3) : ℝ))) / (R6S7.contK X.W)) atTop (𝓝 0) := by
        simpa using (hθ.const_mul B).add
          (((hAinv1.const_mul (4 * C)).add (hAinv3.const_mul (4 * C))).div_const ((R6S7.contK X.W) : ℝ))
      rw [← tendsto_add_atTop_iff_nat 2]
      refine squeeze_zero_norm' ?_ hbound
      obtain ⟨J0, hJ0⟩ := Filter.eventually_atTop.1 hρw
      filter_upwards [eventually_ge_atTop J0] with J hJ
      have hρJ := hJ0 (J+1) (by omega)
      -- `t_{J+2} = A_{J+2} (q β - w)`
      have htv : X.tv β ρ (J+2) = (X.A (J+2) : ℝ) * ((q X.a (X.mm (J+1)) : ℝ) * β - w (J+1)) := by
        simp only [BH.tv, BH.yv, show J + 2 = (J+1) + 1 by ring, X.nk_eq_mm, hρJ]
      have hdec := big_decomp X U hU (J+1)
      rw [hwJ (J+1), pre_succ] at hdec
      push_cast at hdec
      have hτU : (U (J+1) : ℝ) = (R6S7.contK X.W) * τ (J+2) := by
        rw [hUR (J+1)]; simp
      have hpre := pre_succ_bound X U hU J
      rw [pre_succ] at hpre
      have hfut := futBig_bound X U hU (J+1)
      have hA2 := X.A_succ_pos (J+1)
      have hτb := hB (J+2) (by omega)
      -- the identity
      have key : X.tv β ρ (J+2) - τ (J+2) =
          τ (J+2) * ((X.A (J+2) : ℝ) * theta X.a (X.mm (J+1)) - 1) +
          ((X.A (J+2) : ℝ) * (past X U J * eps X.a (X.mm (J+1))) +
            (X.A (J+2) : ℝ) * fut X U (J+1) (X.mm (J+1))) / (R6S7.contK X.W) := by
        rw [htv]
        have e : (q X.a (X.mm (J+1)) : ℝ) * β - w (J+1) =
            (((R6S7.contK X.W) : ℝ) * ((q X.a (X.mm (J+1)) : ℝ) * β) - (R6S7.contK X.W) * w (J+1)) / (R6S7.contK X.W) := by
          field_simp
        rw [e, hdec, hτU]
        field_simp
        ring
      rw [Real.norm_eq_abs, key]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hτb (abs_nonneg _)
      · rw [abs_div, abs_of_pos hKR]
        refine div_le_div_of_nonneg_right ?_ hKR.le
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < X.A (J+2))]
          rw [mul_one_div]; exact hpre
        · rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < X.A (J+2))]
          rw [mul_one_div]; exact hfut

/-! ## Part 6. R6-S1(a) (a consequence of Lemma B and `KL_lt_top_bound`) -/

/-- for a nearest-integer selection, `|x - ρ| = ‖x‖` (independent of tie-breaking) -/
theorem near_abs_eq_dist0 (x : ℝ) (m : ℤ) (h : |x - m| ≤ 1 / 2) : |x - m| = dist0 x :=
  le_antisymm (((near_iff_nearest x m).1 h) (round x)) (round_le x m)

theorem BH.nk_tendsto (X : BH) : Tendsto X.nk atTop atTop := by
  refine tendsto_atTop_atTop.2 (fun b => ⟨b + 1, fun k hk => ?_⟩)
  have : k - 1 ≤ (k - 1) * (X.ell + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold BH.nk; omega

/-- **R6-S1(a)**: if `𝒦_α(β) < ∞` then, for every tie-breaking `ρ`, `y_{n_k} → 0`;
`A_k θ_{n_k} → 1`; and `1/θ_{n_k+i} → K/(c_i c'_i)` for `1 ≤ i ≤ ℓ`. -/
theorem S1a (X : BH) (β : ℝ) (hK : KL X.a β < ⊤) (ρ : ℕ → ℤ)
    (hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ) :
    Tendsto (fun k => X.yv β ρ (X.nk k)) atTop (𝓝 0) ∧
    Tendsto (fun k => (X.A k : ℝ) * theta X.a (X.nk k)) atTop (𝓝 1) ∧
    ∀ i, 1 ≤ i → i ≤ X.ell → Tendsto (fun k => 1 / theta X.a (X.nk k + i)) atTop
      (𝓝 ((R6S7.contK X.W : ℝ) / ((R6S7.cc X.W (i-1) : ℝ) * R6S7.cc' X.W (i-1)))) := by
  refine ⟨?_, X.A_theta_tendsto, fun i h1 h2 => B4 X i h1 h2⟩
  obtain ⟨M, hM⟩ := KL_lt_top_bound X.isCF β hK
  have hM' := X.nk_tendsto.eventually hM
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hlim : Tendsto (fun k => max M 0 * (1 / (X.A k : ℝ))) atTop (𝓝 0) := by
    simpa using X.A_inv_tendsto.const_mul (max M 0)
  refine squeeze_zero' (Eventually.of_forall fun k => abs_nonneg _) ?_ hlim
  filter_upwards [hM', eventually_ge_atTop 1] with k hk hk1
  have ht := X.theta_pos (X.nk k)
  have hlt := theta_lt X.isCF (X.nk k)
  rw [X.a_big k hk1] at hlt
  push_cast at hlt
  have hy : |X.yv β ρ (X.nk k)| = dist0 ((q X.a (X.nk k) : ℝ) * β) :=
    near_abs_eq_dist0 _ _ (hρ (X.nk k))
  have hR : dist0 ((q X.a (X.nk k) : ℝ) * β) ≤ max M 0 * theta X.a (X.nk k) := by
    have := (div_le_iff₀ ht).1 hk
    nlinarith [le_max_left M 0, le_max_right M 0]
  simp only [Function.comp_apply]
  rw [hy]
  refine hR.trans (mul_le_mul_of_nonneg_left hlt.le (le_max_right _ _))

end R6S2

#print axioms R6S2.near_iff_nearest
#print axioms R6S2.coset_indep
#print axioms R6S2.getD_le_sum
#print axioms R6S2.BH.pos_cases
#print axioms R6S2.aux_ratio
#print axioms R6S2.BH.Qchain
#print axioms R6S2.xs_eps
#print axioms R6S2.xs_Dm_succ
#print axioms R6S2.xs_q_eps
#print axioms R6S2.summ
#print axioms R6S2.decomp
#print axioms R6S2.fut_bound
#print axioms R6S2.past_bound
#print axioms R6S2.big_decomp
#print axioms R6S2.pre_succ_bound
#print axioms R6S2.futBig_bound
#print axioms R6S2.E_bound
#print axioms R6S2.lab_err
#print axioms R6S2.PP_rec
#print axioms R6S2.residue
#print axioms R6S2.S1d
#print axioms R6S2.near_abs_eq_dist0
#print axioms R6S2.BH.nk_tendsto
#print axioms R6S2.S1a
