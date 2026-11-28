import EpiFormal.R6S2Localize

/-!
# R6-S2, phase 4: lower bound, upper bound and attainment, main theorem

Formalizes `proofs/R6-S2.md` v2 §7 and assembles the main statement `StatementR6S2`
(defined in `EpiFormal.R6S2Kl`, used verbatim):

* `lower` (§7.1, steps 1–7): for every `β ∉ ℤα + ℤ`, `ν(W) ≤ 𝒦_α(β)`. Proof by contradiction
  with a margin: if `𝒦_α(β) < Λ < ν(W)`, then eventually all ratios `R_n < Λ`; by S1(a)(b)
  (`R_big_tendsto`, `R_word_tendsto`) the vertex costs `v(r_k)` and the rounded edge values `τ_k`
  are eventually `≤ μ < ν(W)`; by S1(c) some edge is nontrivial infinitely often; a vertex value
  that recurs infinitely often closes a walk through such an edge (`R6S7.ClosedWalk`) whose cost is
  `≤ μ < ν(W)`, contradicting the minimality of `ν(W)` (`nu_isLeast`).
  This avoids the limsup equality of steps 2–4 (only inequalities are needed).
* `upper` (§7.2, steps 8–10): periodize a minimal closed walk `C*` (`nu_isLeast`), realize it with
  S1(d) (`S1d`), show `𝒦_α(β) ≤ ν(W)` block by block (`BH.block_of`, `R_big_tendsto`,
  `R_word_tendsto`) and `β ∉ ℤα + ℤ` by S1(c) (`S1c`); equality then follows from `lower`.
* `main : StatementR6S2`.
* `StatementS1` / `S1_all`: R6-S1 (a)–(d) in one statement (for the R6-S1 L3 audit).
* Sanity: `main_example11` (the hypotheses are met by `BH.example11`), `nu_one_one`
  (`ν((1,1)) = 1`, a calibration value of PLAN_GRAPH) and `cstar_example11`.

No proof-escape tactics, no project axioms.
-/

open Filter Topology

namespace R6S2

/-! ## Part 1. Generic helpers -/

/-- `finRotate L i = i + 1 mod L` -/
theorem finRotate_val (L : ℕ) (hL : 0 < L) (i : Fin L) :
    ((finRotate L i : Fin L) : ℕ) = (i.val + 1) % L := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  rw [coe_finRotate]
  split_ifs with h
  · subst h; simp
  · have := Fin.val_lt_last h
    rw [Nat.mod_eq_of_lt (by omega)]

/-- vertex costs along a closed walk are bounded by its cost -/
theorem _root_.R6S7.ClosedWalk.vcost_le {W : List ℕ} (C : R6S7.ClosedWalk W) (i : Fin C.L) :
    ((R6S7.vcost W (C.vert i) : ℚ) : ℝ) ≤ C.cost :=
  (le_max_left _ _).trans
    (Finset.le_sup' (fun k => max ((R6S7.vcost W (C.vert k) : ℚ) : ℝ) |C.t k|) (Finset.mem_univ i))

/-- edge costs along a closed walk are bounded by its cost -/
theorem _root_.R6S7.ClosedWalk.t_le {W : List ℕ} (C : R6S7.ClosedWalk W) (i : Fin C.L) :
    |C.t i| ≤ C.cost :=
  (le_max_right _ _).trans
    (Finset.le_sup' (fun k => max ((R6S7.vcost W (C.vert k) : ℚ) : ℝ) |C.t k|) (Finset.mem_univ i))

/-- `v_i(r) ≤ v(r)` for `1 ≤ i ≤ ℓ` (0-indexed `i - 1`) -/
theorem vterm_le_vcost (W : List ℕ) (r : ZMod (R6S7.contK W)) (i : ℕ) (hi : i < W.length) :
    R6S7.vterm W r i ≤ R6S7.vcost W r :=
  R6S7.le_foldr_max _ _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)

/-- if all `v_i(r) ≤ c` (`1 ≤ i ≤ ℓ`) and `c ≥ 0`, then `v(r) ≤ c` -/
theorem vcost_le_of (W : List ℕ) (r : ZMod (R6S7.contK W)) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, i < W.length → ((R6S7.vterm W r i : ℚ) : ℝ) ≤ c) :
    ((R6S7.vcost W r : ℚ) : ℝ) ≤ c := by
  rcases Nat.eq_zero_or_pos W.length with h0 | hpos
  · rw [R6S7.vcost_of_length_zero W h0]; simpa using hc
  · obtain ⟨⟨i, hi, he⟩, -⟩ := R6S7.vcost_isGreatest W hpos r
    rw [he]; exact h i hi

/-- a `limsup` upper bound for `𝒦` from eventual bounds with arbitrarily small margin -/
theorem KL_le_ofReal (a : ℕ → ℤ) (β c : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, dist0 ((q a n : ℝ) * β) / theta a n ≤ c + ε) :
    KL a β ≤ ENNReal.ofReal c := by
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  have h' := (h ε (by exact_mod_cast hε)).mono fun n hn => ENNReal.ofReal_le_ofReal hn
  have hle : KL a β ≤ ENNReal.ofReal (c + ε) := limsup_le_of_le (h := h')
  calc KL a β ≤ ENNReal.ofReal (c + ε) := hle
    _ ≤ ENNReal.ofReal c + ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal c + ε := by rw [ENNReal.ofReal_coe_nnreal]

/-- the canonical round selections used in `lower` and `upper` -/
theorem BH.round_label_sel (X : BH) (β : ℝ) (ρ : ℕ → ℤ) :
    X.IsLabelSel β ρ (fun k => round ((R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1))) :=
  fun _ => abs_sub_round _

/-! ## Part 2. Lower bound (§7.1) -/

/-- **§7.1 (lower bound).** For every block Hurwitz number and every `β ∉ ℤα + ℤ`,
`ν(W) ≤ 𝒦_α(β)`. -/
theorem lower (X : BH) (β : ℝ) (hβ : β ∉ lattice (alpha X.a)) :
    ENNReal.ofReal (R6S7.nu X.W) ≤ KL X.a β := by
  by_contra hlt
  push Not at hlt
  have hK1 : 1 ≤ R6S7.contK X.W := R6S7.contK_pos X.W X.hW
  have : NeZero (R6S7.contK X.W) := ⟨by omega⟩
  obtain ⟨b, hb1, hb2⟩ := exists_between hlt
  have hbtop : b ≠ ⊤ := ne_top_of_lt hb2
  have hKtop : KL X.a β < ⊤ := hlt.trans ENNReal.ofReal_lt_top
  set Λ : ℝ := b.toReal with hΛdef
  have hΛν : Λ < R6S7.nu X.W := (ENNReal.lt_ofReal_iff_toReal_lt hbtop).1 hb2
  have hΛ0 : 0 ≤ Λ := ENNReal.toReal_nonneg
  set δ : ℝ := (R6S7.nu X.W - Λ) / 3 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  -- eventually all ratios are `< Λ`
  have hR : ∀ᶠ n in atTop, dist0 ((q X.a n : ℝ) * β) / theta X.a n < Λ := by
    have := eventually_lt_of_limsup_lt hb1 (by isBoundedDefault)
    filter_upwards [this] with n hn
    have h0 : 0 ≤ dist0 ((q X.a n : ℝ) * β) / theta X.a n :=
      div_nonneg (abs_nonneg _) (X.theta_pos n).le
    exact (ENNReal.ofReal_lt_iff_lt_toReal h0 hbtop).1 hn
  -- canonical selections and labels
  set ρ : ℕ → ℤ := fun n => round ((q X.a n : ℝ) * β) with hρdef
  have hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ := X.round_sel β
  set lam : ℕ → ℤ := fun k => round ((R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1)) with hlamdef
  have hl : X.IsLabelSel β ρ lam := X.round_label_sel β ρ
  set r : ℕ → ZMod (R6S7.contK X.W) := fun k => X.lab lam k with hrdef
  -- rounded edge values: edge `j` goes from `r j` to `r (j+1)` and carries `τ j`
  set c : ℕ → ℝ := fun j => (((r (j+1)).val : ℝ) - (R6S7.sigma X.W : ℝ) * ((r j).val : ℝ))
    / (R6S7.contK X.W : ℝ) with hcdef
  set τ : ℕ → ℝ := fun j => c j + round (X.tv β ρ (j+1) - c j) with hτdef
  have hτ : Tendsto (fun j => X.tv β ρ (j+1) - τ j) atTop (𝓝 0) := by
    have h3 := (S1b X β hKtop ρ lam hρ hl).2.2
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine h3.congr (fun j => ?_)
    simp only [hτdef, dist0]
    congr 1; ring
  -- (E1) `|t_k| < Λ + δ` eventually
  have hE1 : ∀ᶠ k in atTop, |X.tv β ρ k| < Λ + δ := by
    have hb := R_big_tendsto X β hKtop ρ hρ
    have hb' := (tendsto_order.1 hb).1 (-δ) (by linarith)
    filter_upwards [hb', X.nk_tendsto.eventually hR] with k hk1 hk2
    linarith
  -- (E2) `v(r_k) ≤ Λ + δ` eventually
  have hE2 : ∀ᶠ k in atTop, ((R6S7.vcost X.W (r k) : ℚ) : ℝ) ≤ Λ + δ := by
    have hi : ∀ i ∈ Finset.range X.ell, ∀ᶠ k in atTop,
        ((R6S7.vterm X.W (r k) i : ℚ) : ℝ) ≤ Λ + δ := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have hw := R_word_tendsto X β hKtop ρ lam hρ hl (i+1) (by omega) (by omega)
      have hw' := (tendsto_order.1 hw).1 (-δ) (by linarith)
      have hn := (tendsto_add_atTop_nat (i+1)).comp X.nk_tendsto
      filter_upwards [hw', hn.eventually hR] with k hk1 hk2
      simp only [Nat.add_sub_cancel] at hk1
      simp only [Function.comp_apply] at hk2
      simp only [hrdef]
      linarith
    filter_upwards [(Filter.eventually_all_finset (Finset.range X.ell)).2 hi] with k hk
    exact vcost_le_of X.W (r k) (Λ + δ) (by linarith)
      (fun i hi => hk i (Finset.mem_range.2 hi))
  -- (E3) `|τ_j| < Λ + 2δ` eventually
  have hE3 : ∀ᶠ j in atTop, |τ j| < Λ + 2 * δ := by
    have h1 := (tendsto_order.1 hτ.abs).2 δ (by rw [abs_zero]; exact hδ)
    filter_upwards [h1, (tendsto_add_atTop_nat 1).eventually hE1] with j hj1 hj2
    have : |τ j| ≤ |X.tv β ρ (j+1)| + |X.tv β ρ (j+1) - τ j| := by
      have := abs_sub_abs_le_abs_sub (X.tv β ρ (j+1)) (X.tv β ρ (j+1) - τ j)
      rw [sub_sub_cancel] at this
      have h2 := abs_sub_le (τ j) (X.tv β ρ (j+1)) 0
      rw [sub_zero, sub_zero, abs_sub_comm (τ j)] at h2
      linarith [abs_sub_comm (X.tv β ρ (j+1)) (τ j)]
    linarith
  obtain ⟨k2, hk2⟩ := eventually_atTop.1 (hE2.and hE3)
  -- (step 6) some edge is nontrivial infinitely often
  have hfreq : ∃ᶠ j in atTop, r j ≠ 0 ∨ τ j ≠ 0 := by
    by_contra hcon
    rw [Filter.not_frequently] at hcon
    apply hβ
    refine (S1c X β hKtop ρ lam hρ hl).2 ⟨?_, ?_⟩
    · filter_upwards [hcon] with j hj
      push Not at hj
      exact hj.1
    · rw [← tendsto_add_atTop_iff_nat 1]
      refine hτ.congr' ?_
      filter_upwards [hcon] with j hj
      push Not at hj
      rw [hj.2, sub_zero]
  -- a vertex value recurring infinitely often
  have hv : ∃ v, ∃ᶠ j in atTop, r j = v := by
    by_contra hcon
    simp only [not_exists, Filter.not_frequently] at hcon
    obtain ⟨j, hj⟩ := (Filter.eventually_all.2 hcon).exists
    exact hj (r j) rfl
  obtain ⟨v, hvf⟩ := hv
  obtain ⟨a, ha1, ha2⟩ := (hvf.and_eventually (eventually_ge_atTop k2)).exists
  obtain ⟨j0, hj01, hj02⟩ := (hfreq.and_eventually (eventually_ge_atTop a)).exists
  obtain ⟨b', hb'1, hb'2⟩ := (hvf.and_eventually (eventually_ge_atTop (j0 + 1))).exists
  -- (step 7) the closed walk `r_a → r_{a+1} → ⋯ → r_{b'} = r_a`
  have hvert : ∀ i : Fin (b' - a),
      r (a + ((finRotate (b' - a) i : Fin (b' - a)) : ℕ)) = r (a + i.val + 1) := by
    intro i
    rw [finRotate_val _ (by omega)]
    by_cases h : i.val + 1 < b' - a
    · rw [Nat.mod_eq_of_lt h, add_assoc]
    · have e : i.val + 1 = b' - a := by have := i.2; omega
      rw [e, Nat.mod_self, add_zero, ha1, show a + i.val + 1 = b' by omega, hb'1]
  let C : R6S7.ClosedWalk X.W :=
    { L := b' - a
      hL := by omega
      vert := fun i => r (a + i.val)
      t := fun i => τ (a + i.val)
      edge := fun i => ⟨round (X.tv β ρ (a + i.val + 1) - c (a + i.val)), by
        rw [hvert i]⟩ }
  have hC : ¬ C.allTrivial := by
    intro h
    have h0 := h ⟨j0 - a, show j0 - a < b' - a by omega⟩
    simp only [C, show a + (j0 - a) = j0 by omega] at h0
    rcases hj01 with h1 | h1
    · exact h1 h0.1
    · exact h1 h0.2
  have hcost : C.cost ≤ Λ + 2 * δ := by
    refine Finset.sup'_le _ _ (fun i _ => max_le ?_ ?_)
    · have := (hk2 (a + i.val) (by omega)).1
      simp only [C]; linarith
    · exact (hk2 (a + i.val) (by omega)).2.le
  have hnu := (nu_isLeast X.W X.hW).2 ⟨C, hC, rfl⟩
  rw [hδdef] at hcost
  linarith

/-! ## Part 3. Upper bound and attainment (§7.2) -/

/-- **§7.2 (upper bound and attainment).** For every block Hurwitz number there is
`β ∉ ℤα + ℤ` with `𝒦_α(β) = ν(W)`. -/
theorem upper (X : BH) :
    ∃ β : ℝ, β ∉ lattice (alpha X.a) ∧ KL X.a β = ENNReal.ofReal (R6S7.nu X.W) := by
  have hK1 : 1 ≤ R6S7.contK X.W := R6S7.contK_pos X.W X.hW
  have : NeZero (R6S7.contK X.W) := ⟨by omega⟩
  -- (step 8) a minimal closed walk and its periodization
  obtain ⟨⟨C, hCnt, hCcost⟩, -⟩ := nu_isLeast X.W X.hW
  have hL := C.hL
  set r : ℕ → ZMod (R6S7.contK X.W) := fun k => C.vert ⟨k % C.L, Nat.mod_lt _ hL⟩ with hrdef
  set τ : ℕ → ℝ := fun k => C.t ⟨(k - 1) % C.L, Nat.mod_lt _ hL⟩ with hτdef
  have hτB : ∃ B : ℝ, ∀ k, 1 ≤ k → |τ k| ≤ B := ⟨C.cost, fun k _ => C.t_le _⟩
  have hτc : ∀ k, 1 ≤ k → ∃ z : ℤ, τ k =
      (((r k).val : ℝ) - (R6S7.sigma X.W : ℝ) * ((r (k-1)).val : ℝ)) / (R6S7.contK X.W : ℝ)
        + z := by
    intro k hk
    obtain ⟨z, hz⟩ := C.edge ⟨(k - 1) % C.L, Nat.mod_lt _ hL⟩
    refine ⟨z, ?_⟩
    have e : C.vert (finRotate C.L ⟨(k - 1) % C.L, Nat.mod_lt _ hL⟩) = r k := by
      simp only [hrdef]
      congr 1
      ext
      rw [finRotate_val _ hL]
      simp only
      rw [Nat.mod_add_mod, Nat.sub_add_cancel hk]
    rw [e] at hz
    exact hz
  obtain ⟨β, hKtop, hβ⟩ := S1d X r τ hτB hτc
  set ρ : ℕ → ℤ := fun n => round ((q X.a n : ℝ) * β) with hρdef
  have hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ := X.round_sel β
  set lam : ℕ → ℤ := fun k => round ((R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1)) with hlamdef
  have hl : X.IsLabelSel β ρ lam := X.round_label_sel β ρ
  obtain ⟨hlab, htau⟩ := hβ ρ lam hρ hl
  -- (step 10) `β ∉ ℤα + ℤ`
  have hnot : β ∉ lattice (alpha X.a) := by
    intro hmem
    obtain ⟨hl0, ht0⟩ := (S1c X β hKtop ρ lam hρ hl).1 hmem
    have hr0 : ∀ᶠ k in atTop, r k = 0 := by
      filter_upwards [hl0, hlab] with k h1 h2
      rw [← h2, h1]
    have hτ0 : Tendsto τ atTop (𝓝 0) := by
      have h := ht0.sub htau
      rw [sub_zero] at h
      exact h.congr (fun k => by ring)
    obtain ⟨K0, hK0⟩ := eventually_atTop.1 hr0
    obtain ⟨K1, hK1'⟩ := eventually_atTop.1
      ((tendsto_order.1 hτ0.abs).2 1 (by rw [abs_zero]; exact one_pos))
    have hvert0 : ∀ i : Fin C.L, C.vert i = 0 := by
      intro i
      have hle : K0 ≤ C.L * K0 := Nat.le_mul_of_pos_left _ hL
      have h := hK0 (i.val + C.L * K0) (by omega)
      simp only [hrdef] at h
      rw [← h]
      congr 1
      ext
      simp only
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2]
    apply hCnt
    intro i
    refine ⟨hvert0 i, ?_⟩
    have hle : K1 ≤ C.L * K1 := Nat.le_mul_of_pos_left _ hL
    have h := hK1' (i.val + 1 + C.L * K1) (by omega)
    have e : τ (i.val + 1 + C.L * K1) = C.t i := by
      simp only [hτdef]
      congr 1
      ext
      simp only
      rw [show i.val + 1 + C.L * K1 - 1 = i.val + C.L * K1 by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2]
    rw [e] at h
    obtain ⟨z, hz⟩ := C.edge i
    rw [hvert0, hvert0] at hz
    simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero, zero_div, zero_add] at hz
    rw [hz] at h ⊢
    have hz0 : z = 0 := by
      have h' : |z| < 1 := by exact_mod_cast h
      rcases abs_lt.1 h' with ⟨h1, h2⟩
      omega
    rw [hz0]; simp
  -- (step 9) `𝒦_α(β) ≤ ν(W)`, block by block
  have hup : KL X.a β ≤ ENNReal.ofReal (R6S7.nu X.W) := by
    refine KL_le_ofReal X.a β _ (fun ε hε => ?_)
    have hε2 : 0 < ε / 2 := by linarith
    -- big indices
    have hB1 := (tendsto_order.1 (R_big_tendsto X β hKtop ρ hρ)).2 (ε / 2) hε2
    have hB2 := (tendsto_order.1 htau.abs).2 (ε / 2) (by rw [abs_zero]; exact hε2)
    -- word indices
    have hWi : ∀ i ∈ Finset.Icc 1 X.ell, ∀ᶠ k in atTop,
        dist0 ((q X.a (X.nk k + i) : ℝ) * β) / theta X.a (X.nk k + i)
          - ((R6S7.vterm X.W (X.lab lam k) (i-1) : ℚ) : ℝ) < ε := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
      exact (tendsto_order.1 (R_word_tendsto X β hKtop ρ lam hρ hl i hi1 hi2)).2 ε hε
    obtain ⟨k0, hk0⟩ := eventually_atTop.1
      ((((hB1.and hB2).and ((Filter.eventually_all_finset _).2 hWi)).and hlab).and
        (eventually_ge_atTop 1))
    have hk01 : 1 ≤ k0 := (hk0 k0 le_rfl).2
    filter_upwards [eventually_ge_atTop (X.nk k0)] with n hn
    obtain ⟨k, i, hk, hi, rfl⟩ := X.block_of k0 hk01 n hn
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hk0 k hk
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · -- `n = n_k`: `R_{n_k} < |t_k| + ε/2 < |τ_k| + ε ≤ ν + ε`
      rw [add_zero]
      have hτk : |τ k| ≤ R6S7.nu X.W := hCcost ▸ C.t_le _
      have : |X.tv β ρ k| < |τ k| + ε / 2 := by
        have := abs_sub_abs_le_abs_sub (X.tv β ρ k) (τ k)
        linarith
      linarith
    · -- `n = n_k + i`: `R_{n_k+i} < v_i(r_k) + ε ≤ v(r_k) + ε ≤ ν + ε`
      have h3i := h3 i (Finset.mem_Icc.2 ⟨hipos, hi⟩)
      rw [h4] at h3i
      have hv1 : ((R6S7.vterm X.W (r k) (i-1) : ℚ) : ℝ) ≤ ((R6S7.vcost X.W (r k) : ℚ) : ℝ) := by
        exact_mod_cast vterm_le_vcost X.W (r k) (i-1) (by unfold BH.ell at hi; omega)
      have hv2 : ((R6S7.vcost X.W (r k) : ℚ) : ℝ) ≤ R6S7.nu X.W := hCcost ▸ C.vcost_le _
      linarith
  exact ⟨β, hnot, le_antisymm hup (lower X β hnot)⟩

/-! ## Part 4. Main theorem -/

/-- **R6-S2 (main theorem).** For every block Hurwitz number `α` with block word `W`,
`c*(α) = ν(W)`, and the infimum is attained by some `β ∉ ℤα + ℤ`. -/
theorem main : StatementR6S2 := by
  intro X
  obtain ⟨β, hβ, hK⟩ := upper X
  refine ⟨le_antisymm ?_ ?_, β, hβ, hK⟩
  · exact (iInf₂_le β hβ).trans hK.le
  · exact le_iInf₂ (fun β' hβ' => lower X β' hβ')

/-- R6-S2, clause "only depends on `W`", now unconditional -/
theorem cstar_only_W' (X Y : BH) (hXY : X.W = Y.W) : cstar X.a = cstar Y.a :=
  cstar_only_W main X Y hXY

/-! ## Part 5. R6-S1 (a)–(d) in one statement -/

/-- **Statement of R6-S1** (a)–(d), with the tie-breaking convention of blueprint §0.4: for every
block Hurwitz number, every `β` with `𝒦_α(β) < ∞` and every nearest-integer selection `ρ`, (a)
holds; for every label selection `lam`, (b) and (c) hold for the canonical labels `lab lam`; and
(d) holds (`StatementS1d`). The conclusions are copied verbatim from `S1a`, `S1b`, `S1c`. -/
def StatementS1 : Prop :=
  ∀ X : BH,
    (∀ (β : ℝ), KL X.a β < ⊤ → ∀ ρ : ℕ → ℤ, IsNearSel (fun n => (q X.a n : ℝ) * β) ρ →
      -- (a)
      (Tendsto (fun k => X.yv β ρ (X.nk k)) atTop (𝓝 0) ∧
        Tendsto (fun k => (X.A k : ℝ) * theta X.a (X.nk k)) atTop (𝓝 1) ∧
        ∀ i, 1 ≤ i → i ≤ X.ell → Tendsto (fun k => 1 / theta X.a (X.nk k + i)) atTop
          (𝓝 ((R6S7.contK X.W : ℝ) / ((R6S7.cc X.W (i-1) : ℝ) * R6S7.cc' X.W (i-1))))) ∧
      ∀ lam : ℕ → ℤ, X.IsLabelSel β ρ lam →
        -- (b)
        ((∀ i, 1 ≤ i → i ≤ X.ell → Tendsto (fun k => |X.yv β ρ (X.nk k + i)|
          - (R6S7.dK (R6S7.contK X.W) ((R6S7.cc X.W (i-1) : ℤ) * ((X.lab lam k).val : ℤ)) : ℝ)
            / (R6S7.contK X.W : ℝ)) atTop (𝓝 0)) ∧
        (∃ B : ℝ, ∀ k, |X.tv β ρ k| ≤ B) ∧
        Tendsto (fun k => dist0 (X.tv β ρ (k+1) - (((X.lab lam (k+1)).val : ℝ)
          - (R6S7.sigma X.W : ℝ) * ((X.lab lam k).val : ℝ)) / (R6S7.contK X.W : ℝ)))
          atTop (𝓝 0)) ∧
        -- (c)
        (β ∈ lattice (alpha X.a) ↔
          ((∀ᶠ k in atTop, X.lab lam k = 0) ∧ Tendsto (X.tv β ρ) atTop (𝓝 0)))) ∧
    -- (d)
    StatementS1d X

/-- **R6-S1** (a)–(d) -/
theorem S1_all : StatementS1 := fun X =>
  ⟨fun β hK ρ hρ => ⟨S1a X β hK ρ hρ,
    fun lam hl => ⟨S1b X β hK ρ lam hρ hl, S1c X β hK ρ lam hρ hl⟩⟩,
    S1d X⟩

/-! ## Part 6. Sanity: the hypotheses are satisfiable; a calibration value -/

/-- the main theorem applies to the concrete datum `BH.example11` (`W = (1,1)`, `A_k = k`) -/
theorem main_example11 :
    cstar BH.example11.a = ENNReal.ofReal (R6S7.nu [1, 1]) ∧
    ∃ β : ℝ, β ∉ lattice (alpha BH.example11.a) ∧
      KL BH.example11.a β = ENNReal.ofReal (R6S7.nu [1, 1]) :=
  main BH.example11

/-- calibration (PLAN_GRAPH R6-S2): `ν((1,1)) = 1` -/
theorem nu_one_one : R6S7.nu [1, 1] = 1 := by
  obtain ⟨-, h, -, -⟩ := R6S7.cor2_K_ge_two [1, 1] (by decide) (by decide)
  rw [h]
  apply min_eq_left
  obtain ⟨⟨r, hr, he⟩, -⟩ := R6S7.mstar_isLeast [1, 1] (by decide)
  rw [he]
  have hr1 : r = 1 := by
    have key : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
    exact key r hr
  subst hr1
  have : R6S7.vcost [1, 1] 1 = 1 := by decide +kernel
  rw [this]; norm_num

/-- consequently `c*([0; 1, 1, 1, 2, 1, 1, 3, 1, 1, …]) = 1` -/
theorem cstar_example11 : cstar BH.example11.a = 1 := by
  rw [main_example11.1, nu_one_one, ENNReal.ofReal_one]

end R6S2

#print axioms R6S2.finRotate_val
#print axioms R6S2.KL_le_ofReal
#print axioms R6S2.lower
#print axioms R6S2.upper
#print axioms R6S2.main
#print axioms R6S2.cstar_only_W'
#print axioms R6S2.S1_all
#print axioms R6S2.main_example11
#print axioms R6S2.nu_one_one
#print axioms R6S2.cstar_example11
