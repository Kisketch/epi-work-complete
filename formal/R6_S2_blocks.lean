import EpiFormal.R6S2Kl

/-!
# R6-S2, phase 2a: D4, Lemma B (B1 corollary, B2, B3, B4) and the `𝒦 < ∞` criteria

Phase 2 of the formalization of R6-S2 (`proofs/R6-S2.md` v2, PASSED_L2); see
`formal/R6_S2_blueprint.md`. Builds on `EpiFormal.R6S2Kl` (phase 1).

* D4 (`D4i`, `D4ii`), via the abstract geometric lemmas `geo_sum`, `geo_recip`.
* B1 corollary `BH.A_theta_tendsto` (`A_k θ_{n_k} → 1`), B2 (`B2`), B3 (`B3`), B4 (`B4`).
* `KL_lt_top_of_bdd` (eventually bounded ratios give `𝒦 < ∞`) and its converse
  `KL_lt_top_bound`.
* Internal block index `BH.mm j = n_{j+1} = N + j(ℓ+1)` (`BH.nk_eq_mm`).

No proof-escape tactics, no project axioms.
-/

open Filter Topology

namespace R6S2

/-! ## Geometric sums (the core of D4) -/

/-- if `0 ≤ v_j ≤ v_{j+1}` and `2 v_j ≤ v_{j+2}` then `Σ_{j ≤ k} v_j ≤ 4 v_k` -/
theorem geo_sum (v : ℕ → ℝ) (h0 : ∀ j, 0 ≤ v j) (h1 : ∀ j, v j ≤ v (j+1))
    (h2 : ∀ j, 2 * v j ≤ v (j+2)) : ∀ k, ∑ j ∈ Finset.range (k+1), v j ≤ 4 * v k := by
  have key : ∀ k, ∑ j ∈ Finset.range (k+2), v j ≤ 2 * v (k+1) + 2 * v k := by
    intro k
    induction k with
    | zero => simp [Finset.sum_range_succ]; linarith [h0 0, h0 1]
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have := h2 k
      linarith
  intro k
  rcases k with _ | k
  · simp; linarith [h0 0]
  · have := key k; have := h1 k; linarith

/-- if `0 < w_j ≤ w_{j+1}` and `2 w_j ≤ w_{j+2}` then `Σ_j 1/w_j` converges and is `≤ 4/w_0` -/
theorem geo_recip (w : ℕ → ℝ) (h0 : ∀ j, 0 < w j) (h1 : ∀ j, w j ≤ w (j+1))
    (h2 : ∀ j, 2 * w j ≤ w (j+2)) :
    Summable (fun j => 1 / w j) ∧ ∑' j, 1 / w j ≤ 4 / w 0 := by
  have z0 : ∀ j, 0 ≤ 1 / w j := fun j => (one_div_pos.2 (h0 j)).le
  have z1 : ∀ j, 1 / w (j+1) ≤ 1 / w j := fun j => one_div_le_one_div_of_le (h0 j) (h1 j)
  have z2 : ∀ j, 2 * (1 / w (j+2)) ≤ 1 / w j := by
    intro j
    rw [mul_one_div, div_le_div_iff₀ (h0 _) (h0 _)]
    linarith [h2 j]
  have key : ∀ M, ∑ j ∈ Finset.range M, 1 / w j + 2 * (1 / w M) + 2 * (1 / w (M+1))
      ≤ 4 * (1 / w 0) := by
    intro M
    induction M with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add]; linarith [z1 0]
    | succ M ih => rw [Finset.sum_range_succ]; linarith [z2 M]
  have hb : ∀ M, ∑ j ∈ Finset.range M, 1 / w j ≤ 4 * (1 / w 0) := fun M => by
    linarith [key M, z0 M, z0 (M+1)]
  refine ⟨summable_of_sum_range_le z0 hb, ?_⟩
  have := Real.tsum_le_of_sum_range_le z0 hb
  rwa [mul_one_div] at this

section QBlock

variable {a : ℕ → ℤ}

theorem qR_mono (ha : IsCF a) {m m' : ℕ} (h : m ≤ m') : (q a m : ℝ) ≤ q a m' := by
  exact_mod_cast q_monotone ha h

theorem qR_two (ha : IsCF a) {m m' : ℕ} (h : m + 2 ≤ m') : 2 * (q a m : ℝ) ≤ q a m' := by
  have h1 : 2 * q a m ≤ q a (m+2) := q_two ha m
  have h2 : q a (m+2) ≤ q a m' := q_monotone ha h
  exact_mod_cast h1.trans h2

/-- for indices increasing by at least one, the shifted denominators satisfy the hypotheses
of `geo_sum` / `geo_recip` -/
theorem q_index_facts (ha : IsCF a) (μ : ℕ → ℕ) (hμ : ∀ j, μ j + 1 ≤ μ (j+1)) (c : ℕ) :
    (∀ j, (q a (μ j + c) : ℝ) ≤ q a (μ (j+1) + c)) ∧
    (∀ j, 2 * (q a (μ j + c) : ℝ) ≤ q a (μ (j+2) + c)) := by
  refine ⟨fun j => qR_mono ha (by have := hμ j; omega), fun j => qR_two ha ?_⟩
  have h1 := hμ j
  have h2 : μ (j+1) + 1 ≤ μ (j+2) := hμ (j+1)
  omega

end QBlock

/-! ## Block index, D4 -/

namespace BH

variable (X : BH)

/-- internal block index: `mm j = n_{j+1} = N + j(ℓ+1)` (`j ≥ 0`) -/
def mm (j : ℕ) : ℕ := X.N + j * (X.ell + 1)

theorem ell_def : X.ell = X.W.length := rfl

theorem nk_eq_mm (j : ℕ) : X.nk (j+1) = X.mm j := by simp [nk, mm]

theorem mm_succ (j : ℕ) : X.mm (j+1) = X.mm j + X.ell + 1 := by simp only [mm]; ring

theorem mm_mono {j j' : ℕ} (h : j ≤ j') : X.mm j ≤ X.mm j' := by
  simp only [mm]; have := Nat.mul_le_mul_right (X.ell + 1) h; omega

theorem mm_step (j : ℕ) : X.mm j + 1 ≤ X.mm (j+1) := by rw [mm_succ]; omega

/-- `a_{mm j + 1} = A_{j+1}` -/
theorem a_mm (j : ℕ) : X.a (X.mm j + 1) = (X.A (j+1) : ℤ) := by
  rw [← nk_eq_mm]; exact X.a_big (j+1) (by omega)

theorem A_succ_pos (j : ℕ) : (1 : ℝ) ≤ X.A (j+1) := by exact_mod_cast X.hA (j+1) (by omega)

/-- `A_{j+1} q_{mm j} ≤ q_{mm j + 1}` -/
theorem q_step_mm (j : ℕ) : (X.A (j+1) : ℝ) * q X.a (X.mm j) ≤ q X.a (X.mm j + 1) := by
  have h := q_step X.isCF (X.mm j)
  rw [X.a_mm j] at h
  exact_mod_cast h

end BH

/-- D4 (i): `Σ_{j=1}^k q_{n_j} ≤ 4 q_{n_k}` (stated for all `k`; for `k = 0` the sum is empty) -/
theorem D4i (X : BH) (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, (q X.a (X.nk j) : ℝ) ≤ 4 * q X.a (X.nk k) := by
  rcases k with _ | k
  · simp only [show Finset.Icc 1 0 = ∅ by rfl, Finset.sum_empty]
    have := qR_pos X.isCF (X.nk 0); linarith
  have e : ∑ j ∈ Finset.Icc 1 (k+1), (q X.a (X.nk j) : ℝ)
      = ∑ j ∈ Finset.range (k+1), (q X.a (X.mm j) : ℝ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) (fun j _ => ?_)
    rw [add_comm 1 j, X.nk_eq_mm]
  rw [e, X.nk_eq_mm]
  obtain ⟨h1, h2⟩ := q_index_facts X.isCF X.mm X.mm_step 0
  simp only [add_zero] at h1 h2
  exact geo_sum _ (fun j => (qR_pos X.isCF _).le) h1 h2 k

/-- D4 (ii): `Σ_{j>k} 1/q_{n_j+1}` converges and is `≤ 4/q_{n_{k+1}+1}` (stated for all `k`) -/
theorem D4ii (X : BH) (k : ℕ) :
    Summable (fun j => 1 / (q X.a (X.nk (k + 1 + j) + 1) : ℝ)) ∧
    ∑' j, 1 / (q X.a (X.nk (k + 1 + j) + 1) : ℝ) ≤ 4 / q X.a (X.nk (k+1) + 1) := by
  have e : ∀ j, X.nk (k + 1 + j) = X.mm (k + j) := fun j => by
    rw [show k + 1 + j = (k + j) + 1 by ring, X.nk_eq_mm]
  simp only [e]
  obtain ⟨h1, h2⟩ := q_index_facts X.isCF (fun j => X.mm (k + j))
    (fun j => by simpa [add_assoc] using X.mm_step (k + j)) 1
  exact geo_recip _ (fun j => qR_pos X.isCF _) h1 h2

/-- internal form of D4 (ii) in the block index `mm` -/
theorem D4ii_mm (X : BH) (J : ℕ) :
    Summable (fun i => 1 / (q X.a (X.mm (J + i) + 1) : ℝ)) ∧
    ∑' i, 1 / (q X.a (X.mm (J + i) + 1) : ℝ) ≤ 4 / q X.a (X.mm J + 1) := by
  obtain ⟨h1, h2⟩ := q_index_facts X.isCF (fun j => X.mm (J + j))
    (fun j => by simpa [add_assoc] using X.mm_step (J + j)) 1
  simpa using geo_recip _ (fun j => qR_pos X.isCF _) h1 h2

/-- internal form of D4 (i) in the block index `mm` -/
theorem D4i_mm (X : BH) (J : ℕ) :
    ∑ j ∈ Finset.range (J+1), (q X.a (X.mm j) : ℝ) ≤ 4 * q X.a (X.mm J) := by
  obtain ⟨h1, h2⟩ := q_index_facts X.isCF X.mm X.mm_step 0
  simp only [add_zero] at h1 h2
  exact geo_sum _ (fun j => (qR_pos X.isCF _).le) h1 h2 J

/-! ## Lemma B -/

/-- `A_k → ∞` in `ℝ`, hence `1/A_k → 0` -/
theorem BH.A_inv_tendsto (X : BH) : Tendsto (fun k => 1 / (X.A k : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun k => (X.A k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp X.hAt
  exact h.inv_tendsto_atTop.congr (fun k => by simp [one_div])

/-- B1 corollary: `A_k θ_{n_k} → 1` -/
theorem BH.A_theta_tendsto (X : BH) :
    Tendsto (fun k => (X.A k : ℝ) * theta X.a (X.nk k)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun k => 1 - 2 * (1 / (X.A k : ℝ))) atTop (𝓝 1) := by
    simpa using (X.A_inv_tendsto.const_mul 2).const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    obtain ⟨h1, h2⟩ := X.inv_theta_nk k hk
    have hA : (1 : ℝ) ≤ X.A k := by exact_mod_cast X.hA k hk
    have ht := X.theta_pos (X.nk k)
    rw [div_lt_iff₀ ht] at h2
    rw [lt_div_iff₀ ht] at h1
    have hth : theta X.a (X.nk k) ≤ 1 / (X.A k : ℝ) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with k hk
    obtain ⟨h1, _⟩ := X.inv_theta_nk k hk
    have ht := X.theta_pos (X.nk k)
    rw [lt_div_iff₀ ht] at h1
    linarith

/-- B1 corollary, non-asymptotic: `A_k θ_{n_k} < 1` (`k ≥ 1`) -/
theorem BH.A_theta_lt_one (X : BH) (k : ℕ) (hk : 1 ≤ k) :
    (X.A k : ℝ) * theta X.a (X.nk k) < 1 := by
  obtain ⟨h1, _⟩ := X.inv_theta_nk k hk
  have ht := X.theta_pos (X.nk k)
  rw [lt_div_iff₀ ht] at h1
  linarith

theorem contK_pos_drop (W : List ℕ) (hW : ∀ x ∈ W, 1 ≤ x) (i : ℕ) :
    (0 : ℝ) < R6S7.contK (W.drop i) := by
  have := R6S7.contK_pos (W.drop i) (fun x hx => hW x (List.mem_of_mem_drop hx))
  exact_mod_cast (by omega : 0 < R6S7.contK (W.drop i))

/-- B2: for `1 ≤ i ≤ ℓ`, `α_{n_k+i+1} → K_{[i,ℓ]}/K_{[i+1,ℓ]}`
(`K_{[i,ℓ]} = contK (W.drop (i-1))`). -/
theorem B2 (X : BH) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ X.ell) :
    Tendsto (fun k => cq X.a (X.nk k + i + 1)) atTop
      (𝓝 ((R6S7.contK (X.W.drop (i-1)) : ℝ) / R6S7.contK (X.W.drop i))) := by
  have ha := X.isCF
  -- `α_{n_{k+1}+1} → ∞`
  have hbig : Tendsto (fun k => 1 / cq X.a (X.nk (k+1) + 1)) atTop (𝓝 0) := by
    have hA : Tendsto (fun k => (X.A (k+1) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp X.hAt).comp (tendsto_add_atTop_nat 1)
    have : Tendsto (fun k => cq X.a (X.nk (k+1) + 1)) atTop atTop := by
      refine tendsto_atTop_mono (fun k => ?_) hA
      have := cq_gt ha (X.nk (k+1) + 1)
      rw [X.a_big (k+1) (by omega)] at this
      exact_mod_cast this.le
    exact this.inv_tendsto_atTop.congr (fun k => by simp [one_div])
  -- reverse induction: `i = ℓ - d`
  suffices H : ∀ d, d < X.ell → Tendsto (fun k => cq X.a (X.nk k + (X.ell - d) + 1)) atTop
      (𝓝 ((R6S7.contK (X.W.drop (X.ell - d - 1)) : ℝ) / R6S7.contK (X.W.drop (X.ell - d)))) by
    have := H (X.ell - i) (by omega)
    rwa [show X.ell - (X.ell - i) = i by omega] at this
  intro d
  induction d with
  | zero =>
    intro hl
    simp only [Nat.sub_zero]
    have hword : ∀ k, 1 ≤ k → cq X.a (X.nk k + X.ell + 1) =
        (X.W[X.ell - 1]'(by have := X.ell_def; omega) : ℝ) + 1 / cq X.a (X.nk (k+1) + 1) := by
      intro k hk
      rw [cq_rec ha, show X.nk k + X.ell + 1 = X.nk k + 1 + X.ell by ring,
        X.a_word k X.ell hl le_rfl, show X.nk k + 1 + X.ell + 1 = X.nk (k+1) + 1 by
          rw [X.nk_succ k hk]; ring]
      push_cast; ring
    have hlim : (R6S7.contK (X.W.drop (X.ell - 1)) : ℝ) / R6S7.contK (X.W.drop X.ell)
        = (X.W[X.ell - 1]'(by have := X.ell_def; omega) : ℝ) := by
      have e1 : X.W.drop X.ell = [] := by simp [BH.ell]
      have e2 : X.W.drop (X.ell - 1) = [X.W[X.ell - 1]'(by have := X.ell_def; omega)] := by
        rw [List.drop_eq_getElem_cons (by have := X.ell_def; omega),
          show X.ell - 1 + 1 = X.ell by omega, e1]
      rw [e1, e2, R6S7.contK_singleton, R6S7.contK_nil]; simp
    rw [hlim]
    have := (hbig.const_add (X.W[X.ell - 1]'(by have := X.ell_def; omega) : ℝ))
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [hword k hk]
  | succ d ih =>
    intro hl
    have ih' := ih (by omega)
    set i := X.ell - (d+1) with hi
    have hi1 : 1 ≤ i := by omega
    have hil : i < X.ell := by omega
    rw [show X.ell - d = i + 1 by omega] at ih'
    rw [show X.ell - (d+1) - 1 = i - 1 by omega]
    have hpos1 := contK_pos_drop X.W X.hW i
    have hpos2 := contK_pos_drop X.W X.hW (i+1)
    have hinv := ih'.inv₀ (div_pos hpos1 hpos2).ne'
    have hrec : ∀ k, cq X.a (X.nk k + i + 1) =
        (X.W[i - 1]'(by have := X.ell_def; omega) : ℝ) + 1 / cq X.a (X.nk k + (i+1) + 1) := by
      intro k
      rw [cq_rec ha, show X.nk k + i + 1 = X.nk k + 1 + i by ring, X.a_word k i hi1 hil.le,
        show X.nk k + 1 + i + 1 = X.nk k + (i+1) + 1 by ring]
      push_cast; ring
    have hlim : (R6S7.contK (X.W.drop (i - 1)) : ℝ) / R6S7.contK (X.W.drop i)
        = (X.W[i - 1]'(by have := X.ell_def; omega) : ℝ) +
          ((R6S7.contK (X.W.drop i) : ℝ) / R6S7.contK (X.W.drop (i+1)))⁻¹ := by
      have e1 : X.W.drop (i - 1) = X.W[i-1]'(by have := X.ell_def; omega) ::
          X.W[i]'(by have := X.ell_def; omega) :: X.W.drop (i+1) := by
        rw [List.drop_eq_getElem_cons (by have := X.ell_def; omega), show i - 1 + 1 = i by omega,
          List.drop_eq_getElem_cons (by have := X.ell_def; omega)]
      have e2 : X.W.drop i = X.W[i]'(by have := X.ell_def; omega) :: X.W.drop (i+1) :=
        List.drop_eq_getElem_cons (by have := X.ell_def; omega)
      rw [e1, R6S7.contK_cons_cons, ← e2, inv_div]
      push_cast
      field_simp
    rw [hlim]
    refine ((hinv.const_add _)).congr (fun k => ?_)
    rw [hrec k, one_div]

/-- B3: for `1 ≤ i ≤ ℓ`, `q_{n_k+i-1}/q_{n_k+i} → K_{[1,i-2]}/c_i`
(`qq a n = q_{n-1}`, `K_{[1,i-2]} = cseq W (i-1)`, `c_i = cc W (i-1)`). -/
theorem B3 (X : BH) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ X.ell) :
    Tendsto (fun k => (qq X.a (X.nk k + i) : ℝ) / q X.a (X.nk k + i)) atTop
      (𝓝 ((R6S7.cseq X.W (i-1) : ℝ) / R6S7.cc X.W (i-1))) := by
  have ha := X.isCF
  -- `ρ_k = q_{n_k}/q_{n_k+1} → 0`
  have hρ : Tendsto (fun k => (q X.a (X.nk k) : ℝ) / q X.a (X.nk k + 1)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun k =>
      div_nonneg (qR_pos ha _).le (qR_pos ha _).le) ?_ X.A_inv_tendsto
    filter_upwards [eventually_ge_atTop 1] with k hk
    have h := q_step ha (X.nk k)
    rw [X.a_big k hk] at h
    have hR : (X.A k : ℝ) * q X.a (X.nk k) ≤ q X.a (X.nk k + 1) := by exact_mod_cast h
    have hA : (1 : ℝ) ≤ X.A k := by exact_mod_cast X.hA k hk
    have hq := qR_pos ha (X.nk k)
    rw [div_le_div_iff₀ (qR_pos ha _) (by linarith)]
    nlinarith
  -- (A1) for `q`
  have hrec : ∀ k j (hj : j < X.W.length), (q X.a (X.nk k + j + 2) : ℝ) =
      (X.W[j] : ℝ) * q X.a (X.nk k + j + 1) + q X.a (X.nk k + j) := by
    intro k j hj
    have e : q X.a (X.nk k + j + 2) = X.a (X.nk k + j + 2) * q X.a (X.nk k + j + 1)
        + q X.a (X.nk k + j) := q_succ X.a (X.nk k + j + 1)
    rw [show X.nk k + j + 2 = X.nk k + 1 + (j+1) by ring,
      X.a_word k (j+1) (by omega) (by have := X.ell_def; omega)] at e
    rw [show X.nk k + j + 2 = X.nk k + 1 + (j+1) by ring]
    exact_mod_cast e
  have hA1 := fun k => A1 X.W X.hW (fun m => (q X.a m : ℝ)) (X.nk k) (hrec k)
  have link := R6S7.link X.W X.hW
  have hcc : R6S7.cseq X.W i = R6S7.cc X.W (i-1) := by
    rw [← link.2.2.2.2.2.2.2.2.1 (i-1), show i - 1 + 1 = i by omega]
  have hcpos : (0 : ℝ) < R6S7.cc X.W (i-1) := by
    have := R6S7.contK_pos (X.W.take (i-1)) (fun x hx => X.hW x (List.mem_of_mem_take hx))
    unfold R6S7.cc; exact_mod_cast (by omega : 0 < R6S7.contK (X.W.take (i-1)))
  rcases Nat.lt_or_ge i 2 with hi | hi
  · -- `i = 1`
    obtain rfl : i = 1 := by omega
    have e0 : R6S7.cseq X.W 0 = 0 := by simp [R6S7.cseq]
    simp only [Nat.sub_self, e0, Nat.cast_zero, zero_div]
    refine hρ.congr (fun k => ?_)
    rw [qq_succ]
  · -- `i ≥ 2`: divide numerator and denominator by `q_{n_k+1}`
    have hnum : ∀ k, (qq X.a (X.nk k + i) : ℝ) = (R6S7.cseq X.W (i-1) : ℝ) * q X.a (X.nk k + 1)
        + (R6S7.cseq X.W.tail (i-2) : ℝ) * q X.a (X.nk k) := by
      intro k
      have := hA1 k (i-2) (by unfold BH.ell at hi2; omega)
      rw [show X.nk k + i = (X.nk k + 1 + (i-2)) + 1 by omega, qq_succ, this,
        show i - 2 + 1 = i - 1 by omega]
    have hden : ∀ k, (q X.a (X.nk k + i) : ℝ) = (R6S7.cseq X.W i : ℝ) * q X.a (X.nk k + 1)
        + (R6S7.cseq X.W.tail (i-1) : ℝ) * q X.a (X.nk k) := by
      intro k
      have := hA1 k (i-1) (by unfold BH.ell at hi2; omega)
      rw [show X.nk k + i = X.nk k + 1 + (i-1) by omega, this, show i - 1 + 1 = i by omega]
    have hlim : Tendsto (fun k => ((R6S7.cseq X.W (i-1) : ℝ)
        + (R6S7.cseq X.W.tail (i-2) : ℝ) * ((q X.a (X.nk k) : ℝ) / q X.a (X.nk k + 1))) /
        ((R6S7.cseq X.W i : ℝ) + (R6S7.cseq X.W.tail (i-1) : ℝ) *
          ((q X.a (X.nk k) : ℝ) / q X.a (X.nk k + 1)))) atTop
        (𝓝 ((R6S7.cseq X.W (i-1) : ℝ) / R6S7.cc X.W (i-1))) := by
      have := ((hρ.const_mul (R6S7.cseq X.W.tail (i-2) : ℝ)).const_add
        (R6S7.cseq X.W (i-1) : ℝ)).div ((hρ.const_mul (R6S7.cseq X.W.tail (i-1) : ℝ)).const_add
        (R6S7.cseq X.W i : ℝ)) (by rw [hcc]; simp only [mul_zero, add_zero]; exact hcpos.ne')
      rw [hcc] at this ⊢; simp only [mul_zero, add_zero] at this; exact this
    refine hlim.congr (fun k => ?_)
    have hq1 := qR_pos ha (X.nk k + 1)
    rw [hnum k, hden k]
    field_simp

/-- B4: for `1 ≤ i ≤ ℓ`, `1/θ_{n_k+i} → K/(c_i c'_i)` -/
theorem B4 (X : BH) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ X.ell) :
    Tendsto (fun k => 1 / theta X.a (X.nk k + i)) atTop
      (𝓝 ((R6S7.contK X.W : ℝ) / ((R6S7.cc X.W (i-1) : ℝ) * R6S7.cc' X.W (i-1)))) := by
  have ha := X.isCF
  have h2 := B2 X i hi1 hi2
  have h3 := B3 X i hi1 hi2
  have hsplit := A2a X.W X.hW i hi1 (by unfold BH.ell at hi2; exact hi2)
  have hc' : R6S7.cc' X.W (i-1) = R6S7.contK (X.W.drop i) := by
    simp [R6S7.cc', show i - 1 + 1 = i by omega]
  have hcpos : (0 : ℝ) < R6S7.cc X.W (i-1) := by
    have := R6S7.contK_pos (X.W.take (i-1)) (fun x hx => X.hW x (List.mem_of_mem_take hx))
    unfold R6S7.cc; exact_mod_cast (by omega : 0 < R6S7.contK (X.W.take (i-1)))
  have hdpos := contK_pos_drop X.W X.hW i
  have hlim : (R6S7.contK X.W : ℝ) / ((R6S7.cc X.W (i-1) : ℝ) * R6S7.cc' X.W (i-1)) =
      (R6S7.contK (X.W.drop (i-1)) : ℝ) / R6S7.contK (X.W.drop i)
        + (R6S7.cseq X.W (i-1) : ℝ) / R6S7.cc X.W (i-1) := by
    rw [hsplit, hc']; push_cast
    field_simp
  rw [hlim]
  refine (h2.add h3).congr (fun k => ?_)
  rw [theta_eq ha, one_div_one_div, show X.nk k + i + 1 = X.nk k + i + 1 from rfl]

/-! ## `𝒦 < ∞` criteria -/

/-- if the ratios `‖q_nβ‖/θ_n` are eventually bounded, then `𝒦_α(β) < ∞` -/
theorem KL_lt_top_of_bdd (a : ℕ → ℤ) (β : ℝ) (M : ℝ)
    (h : ∀ᶠ n in atTop, dist0 ((q a n : ℝ) * β) / theta a n ≤ M) : KL a β < ⊤ := by
  have h' : ∀ᶠ n in atTop, ENNReal.ofReal (dist0 ((q a n : ℝ) * β) / theta a n)
      ≤ ENNReal.ofReal M := h.mono fun n hn => ENNReal.ofReal_le_ofReal hn
  exact lt_of_le_of_lt (limsup_le_of_le (h := h')) ENNReal.ofReal_lt_top

/-- conversely, `𝒦_α(β) < ∞` gives an eventual bound on the ratios -/
theorem KL_lt_top_bound {a : ℕ → ℤ} (ha : IsCF a) (β : ℝ) (h : KL a β < ⊤) :
    ∃ M : ℝ, ∀ᶠ n in atTop, dist0 ((q a n : ℝ) * β) / theta a n ≤ M := by
  obtain ⟨b, hb1, hb2⟩ := exists_between h
  refine ⟨b.toReal, ?_⟩
  have := eventually_lt_of_limsup_lt hb1 (by isBoundedDefault)
  filter_upwards [this] with n hn
  have h0 : 0 ≤ dist0 ((q a n : ℝ) * β) / theta a n :=
    div_nonneg (abs_nonneg _) (theta_pos ha n).le
  exact ((ENNReal.ofReal_lt_iff_lt_toReal h0 hb2.ne).1 hn).le

end R6S2

#print axioms R6S2.geo_sum
#print axioms R6S2.geo_recip
#print axioms R6S2.q_index_facts
#print axioms R6S2.BH.nk_eq_mm
#print axioms R6S2.BH.a_mm
#print axioms R6S2.BH.q_step_mm
#print axioms R6S2.D4i
#print axioms R6S2.D4ii
#print axioms R6S2.D4i_mm
#print axioms R6S2.D4ii_mm
#print axioms R6S2.BH.A_inv_tendsto
#print axioms R6S2.BH.A_theta_tendsto
#print axioms R6S2.BH.A_theta_lt_one
#print axioms R6S2.B2
#print axioms R6S2.B3
#print axioms R6S2.B4
#print axioms R6S2.KL_lt_top_of_bdd
#print axioms R6S2.KL_lt_top_bound
