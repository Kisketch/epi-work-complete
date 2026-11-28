import EpiFormal.R6S2Realize
import Mathlib.NumberTheory.Real.Irrational

/-!
# R6-S2, phase 3: Lemma 0, Corollary 0′, canonical labels (§5.2), R6-S1(b), R6-S1(c)

Formalizes `proofs/R6-S2.md` v2:

* §4 Lemma 0 (`lemma0`) and Corollary 0′ (`cor0'`, `cstar_ge_quarter`), for every
  `α = alpha a` with `IsCF a` (regular continued fraction, F1–F3 proved in `R6S2Kl`);
* §5.2 canonical labels: `S1_label` (for `k ≥ k₁`, uniformly in all tie-breakings, the nearest
  integer to `K y_{n_k+1}` is unique, its distance is `< 1/2`, and the label does not depend on
  the tie-breaking), `S1_label_tendsto` (`g_k = y_{n_k+1} - s_k/K → 0`);
* §5.3–§5.4 R6-S1(b) (`S1b`), §5.5 R6-S1(c) (`S1c`).

Tie-breaking convention (blueprint §0.4, as in `StatementS1d`): every statement is quantified over
**all** nearest-integer selections `ρ` (`IsNearSel`) and **all** label selections `lam`
(`BH.IsLabelSel`); the canonical label is `BH.lab lam k = (lam k : ℤ/K)`.

No proof-escape tactics, no project axioms.
-/

open Filter Topology

namespace R6S2

/-! ## Part 1. Elementary facts on `‖·‖` and integers -/

theorem int_eq_of_close {m m' : ℤ} (h : |(m : ℝ) - m'| < 1) : m = m' := by
  have h' : |m - m'| < 1 := by exact_mod_cast h
  have := Int.abs_lt_one_iff.1 h'
  omega

theorem dist0_nonneg (x : ℝ) : 0 ≤ dist0 x := abs_nonneg _

theorem dist0_le_abs_sub (x : ℝ) (m : ℤ) : dist0 x ≤ |x - m| := round_le x m

theorem dist0_le_abs (x : ℝ) : dist0 x ≤ |x| := by
  have := round_le x 0
  rw [Int.cast_zero, sub_zero] at this
  exact this

theorem dist0_add_int (x : ℝ) (m : ℤ) : dist0 (x + m) = dist0 x := by
  unfold dist0
  rw [round_add_intCast]
  push_cast
  congr 1; ring

theorem dist0_of_eq_add_int {x y : ℝ} (h : ∃ m : ℤ, x = y + m) : dist0 x = dist0 y := by
  obtain ⟨m, rfl⟩ := h; exact dist0_add_int y m

theorem dist0_add_le (x y : ℝ) : dist0 (x + y) ≤ dist0 x + dist0 y := by
  refine (dist0_le_abs_sub (x + y) (round x + round y)).trans ?_
  have e : x + y - ((round x + round y : ℤ) : ℝ) = (x - round x) + (y - round y) := by
    push_cast; ring
  rw [e]; exact abs_add_le _ _

theorem dist0_neg (x : ℝ) : dist0 (-x) = dist0 x := by
  apply le_antisymm
  · refine (dist0_le_abs_sub (-x) (-round x)).trans (le_of_eq ?_)
    rw [show -x - ((-round x : ℤ) : ℝ) = -(x - round x) by push_cast; ring, abs_neg]; rfl
  · refine (dist0_le_abs_sub x (-round (-x))).trans (le_of_eq ?_)
    rw [show x - ((-round (-x) : ℤ) : ℝ) = -(-x - round (-x)) by push_cast; ring, abs_neg]; rfl

/-- `‖·‖` is 1-Lipschitz for the quotient metric -/
theorem dist0_sub_dist0_le (x y : ℝ) : |dist0 x - dist0 y| ≤ dist0 (x - y) := by
  have h1 := dist0_add_le (x - y) y
  have h2 := dist0_add_le (y - x) x
  rw [sub_add_cancel] at h1 h2
  rw [show y - x = -(x - y) by ring, dist0_neg] at h2
  rw [abs_le]; constructor <;> linarith

/-- `‖x/K‖ = d_K(x)/K` -/
theorem dist0_div_eq_dK (K : ℕ) (hK : 1 ≤ K) (x : ℤ) :
    dist0 ((x : ℝ) / K) = (R6S7.dK K x : ℝ) / K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨⟨s, hs⟩, hlow⟩ := R6S7.dK_isLeast K hK x
  have hsR : ((R6S7.dK K x : ℕ) : ℝ) = |(x : ℝ) - s * K| := by exact_mod_cast hs
  have key : ∀ t : ℝ, |(x : ℝ) / K - t| = |(x : ℝ) - t * K| / K := by
    intro t
    have e : (x : ℝ) - t * K = ((x : ℝ) / K - t) * K := by
      rw [sub_mul, div_mul_cancel₀ _ hKR.ne']
    rw [e, abs_mul, abs_of_pos hKR, mul_div_assoc, div_self hKR.ne', mul_one]
  apply le_antisymm
  · refine (dist0_le_abs_sub _ s).trans (le_of_eq ?_)
    rw [key, hsR]
  · have h := hlow ⟨round ((x : ℝ) / K), rfl⟩
    have h' : ((R6S7.dK K x : ℕ) : ℝ) ≤ |(x : ℝ) - (round ((x : ℝ) / K) : ℝ) * K| := by
      exact_mod_cast h
    show _ ≤ |(x : ℝ) / K - round ((x : ℝ) / K)|
    rw [key]
    exact div_le_div_of_nonneg_right h' hKR.le

theorem near_int_unique {x e : ℝ} {Z : ℤ} (hx : x = e + Z) (he : |e| < 1 / 2) (m : ℤ)
    (hm : |x - m| ≤ 1 / 2) : m = Z := by
  apply int_eq_of_close
  have e1 : (m : ℝ) - Z = e - (x - m) := by rw [hx]; ring
  rw [e1]
  calc |e - (x - m)| ≤ |e| + |x - m| := abs_sub _ _
    _ < 1 := by linarith

theorem near_unique {x : ℝ} {m m' : ℤ} (hm : |x - m| ≤ 1 / 2) (hm' : |x - m'| ≤ 1 / 2)
    (hd : dist0 x < 1 / 2) : m = m' := by
  apply int_eq_of_close
  have h1 := near_abs_eq_dist0 x m hm
  have h2 := near_abs_eq_dist0 x m' hm'
  calc |(m : ℝ) - m'| = |(x - m') - (x - m)| := by congr 1; ring
    _ ≤ |x - m'| + |x - m| := abs_sub _ _
    _ < 1 := by linarith

/-- (alignment) `dist(t - (u - σ v)/K, ℤ)` does not depend on the integer representatives
`u, v` of `r_{k+1}, r_k ∈ ℤ/K`; `S1b` uses the representatives `val`. -/
theorem dist0_label_rep (K : ℕ) [NeZero K] (σ : ℕ) (r1 r0 : ZMod K) (u v : ℤ)
    (hu : (u : ZMod K) = r1) (hv : (v : ZMod K) = r0) (t : ℝ) :
    dist0 (t - ((u : ℝ) - σ * v) / K) = dist0 (t - ((r1.val : ℝ) - σ * (r0.val : ℝ)) / K) := by
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
  refine dist0_of_eq_add_int ⟨-(m - σ * m'), ?_⟩
  rw [hmR, hmR']; push_cast; field_simp; ring

/-! ## Part 2. Lemma 0 and Corollary 0′ (§4) -/

/-- **Lemma 0** (§4; the half of KL 1991 Thm 1 that is used, self-proved): if
`‖q_nβ‖ < θ_n/4` for all `n ≥ n₀` (`n₀ = n* - 1`, `n* ≥ 1`), then `β ∈ ℤα + ℤ`. -/
theorem lemma0 {a : ℕ → ℤ} (ha : IsCF a) (β : ℝ) (n0 : ℕ)
    (h : ∀ n, n0 ≤ n → dist0 ((q a n : ℝ) * β) < theta a n / 4) : β ∈ lattice (alpha a) := by
  set ρ : ℕ → ℤ := fun n => round ((q a n : ℝ) * β) with hρdef
  have hy : ∀ n, n0 ≤ n → |(q a n : ℝ) * β - ρ n| < theta a n / 4 := fun n hn => h n hn
  -- 0.1–0.2: the defect `m_n` vanishes, i.e. `ρ` satisfies F1 from `n0` on
  have hrec : ∀ n, n0 ≤ n → ρ (n+2) = a (n+2) * ρ (n+1) + ρ n := by
    intro n hn
    have e : (q a (n+2) : ℝ) = a (n+2) * q a (n+1) + q a n := by exact_mod_cast q_succ a (n+1)
    have h0 := hy n hn
    have h1 := hy (n+1) (by omega)
    have h2 := hy (n+2) (by omega)
    have t0 := theta_lt_one ha n
    have t2 := theta_lt_one ha (n+2)
    have t1 : theta a (n+1) < 1 / (a (n+2) : ℝ) := theta_lt ha (n+1)
    have hA : (1 : ℝ) ≤ a (n+2) := by exact_mod_cast ha (n+2) (by omega)
    have hAt : (a (n+2) : ℝ) * theta a (n+1) < 1 := by
      rw [lt_div_iff₀ (by linarith)] at t1; linarith
    apply int_eq_of_close
    push_cast
    have key : (ρ (n+2) : ℝ) - (a (n+2) * ρ (n+1) + ρ n) = -(((q a (n+2) : ℝ) * β - ρ (n+2))
        - (a (n+2) : ℝ) * ((q a (n+1) : ℝ) * β - ρ (n+1)) - ((q a n : ℝ) * β - ρ n)) := by
      rw [e]; ring
    rw [key, abs_neg]
    have hm : |(a (n+2) : ℝ) * ((q a (n+1) : ℝ) * β - ρ (n+1))|
        < (a (n+2) : ℝ) * (theta a (n+1) / 4) := by
      rw [abs_mul, abs_of_pos (by linarith)]
      exact mul_lt_mul_of_pos_left h1 (by linarith)
    calc _ ≤ |((q a (n+2) : ℝ) * β - ρ (n+2)) - (a (n+2) : ℝ) * ((q a (n+1) : ℝ) * β - ρ (n+1))|
          + |(q a n : ℝ) * β - ρ n| := abs_sub _ _
      _ ≤ |(q a (n+2) : ℝ) * β - ρ (n+2)| + |(a (n+2) : ℝ) * ((q a (n+1) : ℝ) * β - ρ (n+1))|
          + |(q a n : ℝ) * β - ρ n| := by gcongr; exact abs_sub _ _
      _ < 1 := by nlinarith
  -- 0.3: Bezout coefficients from F2
  obtain ⟨s, hsdef⟩ : ∃ s : ℤ, s = (-1) ^ n0 := ⟨_, rfl⟩
  have hdet : p a (n0+1) * q a n0 - p a n0 * q a (n0+1) = s := by rw [hsdef]; exact det a n0
  have hs : s * s = 1 := by rw [hsdef, ← mul_pow]; simp
  set u : ℤ := s * (ρ (n0+1) * q a n0 - ρ n0 * q a (n0+1)) with hu
  set v : ℤ := s * (ρ n0 * p a (n0+1) - ρ (n0+1) * p a n0) with hv
  have hb : ∀ j, ρ (n0+j) = u * p a (n0+j) + v * q a (n0+j) ∧
      ρ (n0+j+1) = u * p a (n0+j+1) + v * q a (n0+j+1) := by
    intro j
    induction j with
    | zero =>
      simp only [add_zero]
      constructor
      · rw [hu, hv]; linear_combination (-s * ρ n0) * hdet + (-ρ n0) * hs
      · rw [hu, hv]; linear_combination (-s * ρ (n0+1)) * hdet + (-ρ (n0+1)) * hs
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have hr := hrec (n0+j) (by omega)
      have hp : p a (n0+j+2) = a (n0+j+2) * p a (n0+j+1) + p a (n0+j) := p_succ a (n0+j+1)
      have hq : q a (n0+j+2) = a (n0+j+2) * q a (n0+j+1) + q a (n0+j) := q_succ a (n0+j+1)
      rw [show n0 + (j + 1) + 1 = n0 + j + 2 by ring, hr, hp, hq, ih.1, ih.2]
      ring
  -- 0.4: `q_n |β - v - uα| ≤ 1/2 + |u|` for all `n ≥ n0`, and `q_n → ∞`
  by_contra hcon
  have hne : β - u * alpha a - v ≠ 0 := by
    intro h0; exact hcon ⟨u, v, by linarith⟩
  have hc : 0 < |β - u * alpha a - v| := abs_pos.2 hne
  have hev := (q_tendsto ha).eventually_gt_atTop ((1 / 2 + |(u : ℝ)|) / |β - u * alpha a - v|)
  obtain ⟨n, hn1, hn2⟩ := (hev.and (eventually_ge_atTop n0)).exists
  obtain ⟨j, rfl⟩ : ∃ j, n = n0 + j := ⟨n - n0, by omega⟩
  have hρn := (hb j).1
  have hyn : |(q a (n0+j) : ℝ) * β - ρ (n0+j)| ≤ 1 / 2 := abs_sub_round _
  have heps := abs_eps_lt ha (n0+j)
  have hq1 : (1 : ℝ) ≤ q a (n0+j+1) := by exact_mod_cast q_pos ha (n0+j+1)
  have heps1 : |eps a (n0+j)| ≤ 1 := by
    have : 1 / (q a (n0+j+1) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hq1
    linarith
  have hqpos := qR_pos ha (n0+j)
  have key : (q a (n0+j) : ℝ) * (β - u * alpha a - v) =
      ((q a (n0+j) : ℝ) * β - ρ (n0+j)) - u * eps a (n0+j) := by
    rw [hρn]; simp only [eps]; push_cast; ring
  have hbd : (q a (n0+j) : ℝ) * |β - u * alpha a - v| ≤ 1 / 2 + |(u : ℝ)| := by
    rw [← abs_of_pos hqpos, ← abs_mul, key]
    calc _ ≤ |(q a (n0+j) : ℝ) * β - ρ (n0+j)| + |(u : ℝ) * eps a (n0+j)| := abs_sub _ _
      _ ≤ 1 / 2 + |(u : ℝ)| * 1 := by
        rw [abs_mul]; gcongr
      _ = _ := by ring
  rw [div_lt_iff₀ hc] at hn1
  linarith

/-- **Corollary 0′** (§4): `β ∉ ℤα + ℤ ⇒ 𝒦_α(β) ≥ 1/4` -/
theorem cor0' {a : ℕ → ℤ} (ha : IsCF a) (β : ℝ) (hβ : β ∉ lattice (alpha a)) :
    ENNReal.ofReal (1 / 4) ≤ KL a β := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hev := eventually_lt_of_limsup_lt hlt (by isBoundedDefault)
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hev
  apply hβ
  refine lemma0 ha β n0 (fun n hn => ?_)
  have h := hn0 n hn
  have ht := theta_pos ha n
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num), div_lt_iff₀ ht] at h
  linarith

/-- **Corollary 0′**, second clause: `c*(α) ≥ 1/4` -/
theorem cstar_ge_quarter {a : ℕ → ℤ} (ha : IsCF a) : ENNReal.ofReal (1 / 4) ≤ cstar a :=
  le_iInf₂ (fun β hβ => cor0' ha β hβ)

/-- complete quotients of `x` under the regular continued fraction algorithm -/
noncomputable def cfSeq (x : ℝ) : ℕ → ℝ
  | 0 => x
  | (m+1) => 1 / (cfSeq x m - ⌊cfSeq x m⌋)

/-- (alignment for Lemma 0 / Corollary 0′: "α 为任意无理数") every irrational `x` is `alpha a` for
some `a` with `IsCF a` (namely its regular continued fraction; by `cf_algorithm`, `a` is then the
output of the algorithm on `alpha a`). Hence `lemma0`, `cor0'`, `cstar_ge_quarter`, stated for
`alpha a` with `IsCF a`, cover every irrational `α`. -/
theorem exists_isCF_alpha (x : ℝ) (hx : Irrational x) : ∃ a : ℕ → ℤ, IsCF a ∧ alpha a = x := by
  have hirr : ∀ m, Irrational (cfSeq x m) := by
    intro m
    induction m with
    | zero => exact hx
    | succ m ih =>
      show Irrational (1 / (cfSeq x m - ⌊cfSeq x m⌋))
      rw [one_div]; exact (ih.sub_intCast _).inv
  have hfr : ∀ m, 0 < cfSeq x m - ⌊cfSeq x m⌋ ∧ cfSeq x m - ⌊cfSeq x m⌋ < 1 := by
    intro m
    have h1 := Int.floor_le (cfSeq x m)
    have h2 := Int.lt_floor_add_one (cfSeq x m)
    have h3 := (hirr m).ne_int ⌊cfSeq x m⌋
    refine ⟨lt_of_le_of_ne (by linarith) (fun h => h3 (by linarith)), by linarith⟩
  have hS : ∀ m, cfSeq x (m+1) = 1 / (cfSeq x m - ⌊cfSeq x m⌋) := fun m => rfl
  have hgt : ∀ m, 1 < cfSeq x (m+1) := by
    intro m
    rw [hS]; obtain ⟨h1, h2⟩ := hfr m
    rw [lt_div_iff₀ h1]; linarith
  set a : ℕ → ℤ := fun m => ⌊cfSeq x m⌋ with hadef
  have ha : IsCF a := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := hgt m
    exact Int.le_floor.2 (by push_cast; linarith)
  have hrec : ∀ m, cfSeq x (m+1) = a (m+1) + 1 / cfSeq x (m+2) := by
    intro m
    have h := hS (m+1)
    have hp := (hfr (m+1)).1
    rw [h, one_div_one_div]; simp only [hadef]; ring
  -- `x (q_n x_{n+1} + q_{n-1}) = p_n x_{n+1} + p_{n-1}`
  have key : ∀ n, x * ((q a n : ℝ) * cfSeq x (n+1) + qq a n) = (p a n : ℝ) * cfSeq x (n+1) + pp a n := by
    intro n
    induction n with
    | zero =>
      have h : 0 < x - (a 0 : ℝ) := (hfr 0).1
      have e : cfSeq x 1 = 1 / (x - a 0) := hS 0
      rw [q_zero, p_zero, qq_zero, pp_zero, e]
      push_cast
      field_simp
      ring
    | succ n ih =>
      have hz := lt_trans one_pos (hgt (n+1))
      have hyz : cfSeq x (n+1) * cfSeq x (n+2) = a (n+1) * cfSeq x (n+2) + 1 := by
        rw [hrec n]; field_simp
      have eq1 : (q a (n+1) : ℝ) = a (n+1) * q a n + qq a n := by exact_mod_cast q_succ a n
      have ep1 : (p a (n+1) : ℝ) = a (n+1) * p a n + pp a n := by exact_mod_cast p_succ a n
      have eqq : (qq a (n+1) : ℝ) = q a n := rfl
      have epp : (pp a (n+1) : ℝ) = p a n := rfl
      rw [eq1, ep1, eqq, epp]
      linear_combination cfSeq x (n+2) * ih + ((p a n : ℝ) - x * q a n) * hyz
  have h1 : Tendsto (fun n => (q a n : ℝ)⁻¹) atTop (𝓝 0) := (q_tendsto ha).inv_tendsto_atTop
  have hbound : ∀ n, |(p a n : ℝ) / q a n - x| ≤ (q a n : ℝ)⁻¹ := by
    intro n
    have hq := qR_pos ha n
    have hY := hgt n
    have hqq : (0 : ℝ) ≤ qq a n := by exact_mod_cast qq_nonneg ha n
    set D : ℝ := (q a n : ℝ) * cfSeq x (n+1) + qq a n with hD
    have hD1 : 1 ≤ D := by
      have : (1 : ℝ) ≤ q a n := by exact_mod_cast q_pos ha n
      nlinarith
    have hdet : (q a n : ℝ) * pp a n - p a n * qq a n = (-1) ^ n := by exact_mod_cast det' a n
    have e : (x - (p a n : ℝ) / q a n) * ((q a n : ℝ) * D) = (-1) ^ n := by
      have e1 : (x - (p a n : ℝ) / q a n) * ((q a n : ℝ) * D) = x * ((q a n : ℝ) * D) - p a n * D := by
        rw [sub_mul, ← mul_assoc ((p a n : ℝ) / q a n), div_mul_cancel₀ _ hq.ne']
      rw [e1]
      have k := key n
      rw [← hD] at k
      linear_combination (q a n : ℝ) * k + hdet
    have habs : |x - (p a n : ℝ) / q a n| * ((q a n : ℝ) * D) = 1 := by
      have := congrArg abs e
      rwa [abs_mul, abs_of_pos (mul_pos hq (by linarith) : (0 : ℝ) < (q a n : ℝ) * D), abs_pow,
        abs_neg, abs_one, one_pow] at this
    rw [abs_sub_comm, ← one_div, le_div_iff₀ hq]
    have h0 := abs_nonneg (x - (p a n : ℝ) / q a n)
    nlinarith
  have hconv : Tendsto (fun n => (p a n : ℝ) / q a n) atTop (𝓝 x) := by
    have h0 : Tendsto (fun n => (p a n : ℝ) / q a n - x) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      exact squeeze_zero (fun n => abs_nonneg _) hbound h1
    simpa using h0.add_const x
  exact ⟨a, ha, tendsto_nhds_unique (tendsto_conv ha) hconv⟩

/-- Corollary 0′ for an arbitrary irrational `α` (via `exists_isCF_alpha`) -/
theorem cstar_ge_quarter_irrational (x : ℝ) (hx : Irrational x) :
    ∃ a : ℕ → ℤ, IsCF a ∧ alpha a = x ∧ ENNReal.ofReal (1 / 4) ≤ cstar a := by
  obtain ⟨a, ha, hax⟩ := exists_isCF_alpha x hx
  exact ⟨a, ha, hax, cstar_ge_quarter ha⟩


/-! ## Part 3. Block identities for `y_n` -/

namespace BH

variable (X : BH)

/-- (A1) for `q` at block `k` (`0 ≤ j ≤ ℓ`):
`q_{n_k+1+j} = K_{[1,j]} q_{n_k+1} + K_{[2,j]} q_{n_k}` -/
theorem q_block (k j : ℕ) (hj : j ≤ X.ell) :
    q X.a (X.nk k + 1 + j) = (R6S7.cseq X.W (j+1) : ℤ) * q X.a (X.nk k + 1)
      + (R6S7.cseq X.W.tail j : ℤ) * q X.a (X.nk k) := by
  have hrec : ∀ j (hj : j < X.W.length), q X.a (X.nk k + j + 2) =
      (X.W[j] : ℤ) * q X.a (X.nk k + j + 1) + q X.a (X.nk k + j) := by
    intro j hj
    have e : q X.a (X.nk k + j + 2) = X.a (X.nk k + j + 2) * q X.a (X.nk k + j + 1)
        + q X.a (X.nk k + j) := q_succ X.a (X.nk k + j + 1)
    rw [show X.nk k + j + 2 = X.nk k + 1 + (j+1) by ring,
      X.a_word k (j+1) (by omega) (by have := X.ell_def; omega)] at e
    rw [show X.nk k + j + 2 = X.nk k + 1 + (j+1) by ring]
    exact_mod_cast e
  exact A1 X.W X.hW (fun m => q X.a m) (X.nk k) hrec j hj

/-- `y_{n_k+1+j} ≡ K_{[1,j]} y_{n_k+1} + K_{[2,j]} y_{n_k} (mod 1)` -/
theorem yv_block (β : ℝ) (ρ : ℕ → ℤ) (k j : ℕ) (hj : j ≤ X.ell) :
    ∃ m : ℤ, X.yv β ρ (X.nk k + 1 + j) = (R6S7.cseq X.W (j+1) : ℝ) * X.yv β ρ (X.nk k + 1)
      + (R6S7.cseq X.W.tail j : ℝ) * X.yv β ρ (X.nk k) + m := by
  have h : (q X.a (X.nk k + 1 + j) : ℝ) = (R6S7.cseq X.W (j+1) : ℝ) * q X.a (X.nk k + 1)
      + (R6S7.cseq X.W.tail j : ℝ) * q X.a (X.nk k) := by exact_mod_cast X.q_block k j hj
  refine ⟨(R6S7.cseq X.W (j+1) : ℤ) * ρ (X.nk k + 1) + (R6S7.cseq X.W.tail j : ℤ) * ρ (X.nk k)
    - ρ (X.nk k + 1 + j), ?_⟩
  simp only [yv]; push_cast
  linear_combination β * h

/-- the integer `Z_k` of §5.2: `K y_{n_k+1} = y_{n_{k+1}} - K_{[2,ℓ]} y_{n_k} + Z_k` -/
def Zl (ρ : ℕ → ℤ) (k : ℕ) : ℤ :=
  ρ (X.nk (k+1)) - (R6S7.cseq X.W.tail X.ell : ℤ) * ρ (X.nk k)
    - (R6S7.contK X.W : ℤ) * ρ (X.nk k + 1)

theorem Ky_eq (β : ℝ) (ρ : ℕ → ℤ) (k : ℕ) (hk : 1 ≤ k) :
    (R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1) =
      (X.yv β ρ (X.nk (k+1)) - (R6S7.cseq X.W.tail X.ell : ℝ) * X.yv β ρ (X.nk k))
        + (X.Zl ρ k : ℝ) := by
  have h : (q X.a (X.nk (k+1)) : ℝ) = (R6S7.contK X.W : ℝ) * q X.a (X.nk k + 1)
      + (R6S7.cseq X.W.tail X.ell : ℝ) * q X.a (X.nk k) := by
    have h0 := X.q_block k X.ell le_rfl
    have hcK : R6S7.cseq X.W (X.ell + 1) = R6S7.contK X.W :=
      (R6S7.link X.W X.hW).2.2.2.2.2.2.2.1
    rw [hcK, show X.nk k + 1 + X.ell = X.nk (k+1) by rw [X.nk_succ k hk]; ring] at h0
    exact_mod_cast h0
  simp only [yv, Zl]; push_cast
  linear_combination (-β) * h

/-- `y_{n_{k+1}+1} ≡ t_{k+1} + y_{n_k+ℓ} (mod 1)` (F1 at the big index, `n_{k+1} - 1 = n_k + ℓ`) -/
theorem yv_big (β : ℝ) (ρ : ℕ → ℤ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ m : ℤ, X.yv β ρ (X.nk (k+1) + 1) = X.tv β ρ (k+1) + X.yv β ρ (X.nk k + X.ell) + m := by
  have hq : (q X.a (X.nk (k+1) + 1) : ℝ) =
      (X.A (k+1) : ℝ) * q X.a (X.nk (k+1)) + q X.a (X.nk k + X.ell) := by
    have e := q_succ X.a (X.nk (k+1))
    rw [X.a_big (k+1) (by omega)] at e
    have e2 : qq X.a (X.nk (k+1)) = q X.a (X.nk k + X.ell) := by rw [X.nk_succ k hk]; rfl
    rw [e2] at e
    exact_mod_cast e
  refine ⟨(X.A (k+1) : ℤ) * ρ (X.nk (k+1)) + ρ (X.nk k + X.ell) - ρ (X.nk (k+1) + 1), ?_⟩
  simp only [yv, tv]; push_cast
  linear_combination β * hq

theorem abs_yv (β : ℝ) (ρ : ℕ → ℤ) (hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ) (n : ℕ) :
    |X.yv β ρ n| = dist0 ((q X.a n : ℝ) * β) := near_abs_eq_dist0 _ _ (hρ n)

theorem dist0_yv (β : ℝ) (ρ : ℕ → ℤ) (n : ℕ) :
    dist0 (X.yv β ρ n) = dist0 ((q X.a n : ℝ) * β) :=
  dist0_of_eq_add_int ⟨-ρ n, by simp only [yv]; push_cast; ring⟩

theorem round_sel (β : ℝ) :
    IsNearSel (fun n => (q X.a n : ℝ) * β) (fun n => round ((q X.a n : ℝ) * β)) :=
  fun _ => abs_sub_round _

theorem dist0_nk_tendsto (β : ℝ) (hK : KL X.a β < ⊤) :
    Tendsto (fun k => dist0 ((q X.a (X.nk k) : ℝ) * β)) atTop (𝓝 0) := by
  have h := (S1a X β hK _ (X.round_sel β)).1.abs
  rw [abs_zero] at h
  exact h.congr (fun k => X.abs_yv β _ (X.round_sel β) _)

/-- integer representatives of the canonical label: `val (lam k mod K) = lam k + K m` -/
theorem lab_val (lam : ℕ → ℤ) (k : ℕ) :
    ∃ m : ℤ, (((X.lab lam k).val : ℕ) : ℝ) = lam k + (R6S7.contK X.W : ℝ) * m := by
  have : NeZero (R6S7.contK X.W) := ⟨by have := R6S7.contK_pos X.W X.hW; omega⟩
  refine ⟨-(lam k / (R6S7.contK X.W : ℤ)), ?_⟩
  have h1 : (((X.lab lam k).val : ℕ) : ℤ) = lam k % (R6S7.contK X.W : ℤ) := ZMod.val_intCast (lam k)
  have h3 : (((X.lab lam k).val : ℕ) : ℝ) = ((lam k % (R6S7.contK X.W : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast h1
  rw [h3, Int.emod_def]; push_cast; ring

/-- every `n ≥ n_{k₀}` lies in a block `k ≥ k₀`: `n = n_k + i`, `0 ≤ i ≤ ℓ` -/
theorem block_of (k0 : ℕ) (hk0 : 1 ≤ k0) (n : ℕ) (hn : X.nk k0 ≤ n) :
    ∃ k i, k0 ≤ k ∧ i ≤ X.ell ∧ n = X.nk k + i := by
  have hpos : 0 < X.ell + 1 := by omega
  refine ⟨(n - X.N) / (X.ell + 1) + 1, (n - X.N) % (X.ell + 1), ?_, ?_, ?_⟩
  · have h1 : (k0 - 1) * (X.ell + 1) ≤ n - X.N := by unfold BH.nk at hn; omega
    have := (Nat.le_div_iff_mul_le hpos).2 h1
    omega
  · have := Nat.mod_lt (n - X.N) hpos; omega
  · have h1 := Nat.div_add_mod' (n - X.N) (X.ell + 1)
    have h2 : X.N ≤ n := le_trans (by unfold BH.nk; omega) hn
    unfold BH.nk; simp only [Nat.add_sub_cancel]
    omega

/-! ## Part 4. Canonical labels (§5.2) -/

theorem lab_core (β : ℝ) (ρ lam : ℕ → ℤ) (hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ)
    (hl : X.IsLabelSel β ρ lam) (k : ℕ) (hk : 1 ≤ k)
    (hs : dist0 ((q X.a (X.nk (k+1)) : ℝ) * β)
      + (R6S7.cseq X.W.tail X.ell : ℝ) * dist0 ((q X.a (X.nk k) : ℝ) * β) < 1 / 2) :
    lam k = X.Zl ρ k ∧
    (R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1) - lam k =
      X.yv β ρ (X.nk (k+1)) - (R6S7.cseq X.W.tail X.ell : ℝ) * X.yv β ρ (X.nk k) ∧
    |(R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1) - lam k| < 1 / 2 ∧
    ∀ m : ℤ, |(R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1) - m| ≤ 1 / 2 → m = lam k := by
  have hZ := X.Ky_eq β ρ k hk
  have hc0 : (0 : ℝ) ≤ (R6S7.cseq X.W.tail X.ell : ℝ) := Nat.cast_nonneg _
  have he : |X.yv β ρ (X.nk (k+1)) - (R6S7.cseq X.W.tail X.ell : ℝ) * X.yv β ρ (X.nk k)|
      < 1 / 2 := by
    calc _ ≤ |X.yv β ρ (X.nk (k+1))| + |(R6S7.cseq X.W.tail X.ell : ℝ) * X.yv β ρ (X.nk k)| :=
          abs_sub _ _
      _ = dist0 ((q X.a (X.nk (k+1)) : ℝ) * β)
          + (R6S7.cseq X.W.tail X.ell : ℝ) * dist0 ((q X.a (X.nk k) : ℝ) * β) := by
          rw [abs_mul, abs_of_nonneg hc0, X.abs_yv β ρ hρ, X.abs_yv β ρ hρ]
      _ < 1 / 2 := hs
  have huniq : ∀ m : ℤ, |(R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1) - m| ≤ 1 / 2 →
      m = X.Zl ρ k := fun m hm => near_int_unique hZ he m hm
  have hlam : lam k = X.Zl ρ k := huniq (lam k) (hl k)
  have heq : (R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1) - lam k =
      X.yv β ρ (X.nk (k+1)) - (R6S7.cseq X.W.tail X.ell : ℝ) * X.yv β ρ (X.nk k) := by
    rw [hZ, hlam]; ring
  exact ⟨hlam, heq, by rw [heq]; exact he, fun m hm => (huniq m hm).trans hlam.symm⟩

theorem lab_eventually (β : ℝ) (hK : KL X.a β < ⊤) :
    ∃ k1, 1 ≤ k1 ∧ ∀ k, k1 ≤ k →
      dist0 ((q X.a (X.nk (k+1)) : ℝ) * β)
        + (R6S7.cseq X.W.tail X.ell : ℝ) * dist0 ((q X.a (X.nk k) : ℝ) * β) < 1 / 2 ∧
      dist0 ((q X.a (X.nk k) : ℝ) * β) < 1 / 2 ∧
      dist0 ((q X.a (X.nk (k+1)) : ℝ) * β) < 1 / 2 := by
  have hdt := X.dist0_nk_tendsto β hK
  have hF : Tendsto (fun k => (dist0 ((q X.a (X.nk (k+1)) : ℝ) * β)
      + (R6S7.cseq X.W.tail X.ell : ℝ) * dist0 ((q X.a (X.nk k) : ℝ) * β))
      + dist0 ((q X.a (X.nk k) : ℝ) * β)) atTop (𝓝 0) := by
    have h := ((hdt.comp (tendsto_add_atTop_nat 1)).add
      (hdt.const_mul (R6S7.cseq X.W.tail X.ell : ℝ))).add hdt
    rw [mul_zero, add_zero, add_zero] at h
    exact h
  have hev := (tendsto_order.1 hF).2 (1 / 2) (by norm_num)
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop 1))
  refine ⟨k1, (hk1 k1 le_rfl).2, fun k hk => ?_⟩
  have h : (dist0 ((q X.a (X.nk (k+1)) : ℝ) * β)
      + (R6S7.cseq X.W.tail X.ell : ℝ) * dist0 ((q X.a (X.nk k) : ℝ) * β))
      + dist0 ((q X.a (X.nk k) : ℝ) * β) < 1 / 2 := (hk1 k hk).1
  have h0 := dist0_nonneg ((q X.a (X.nk k) : ℝ) * β)
  have h1 := dist0_nonneg ((q X.a (X.nk (k+1)) : ℝ) * β)
  have hc : (0 : ℝ) ≤ (R6S7.cseq X.W.tail X.ell : ℝ) := Nat.cast_nonneg _
  have := mul_nonneg hc h0
  exact ⟨by linarith, by linarith, by linarith⟩

end BH

/-- **§5.2 (canonical labels; uniqueness and tie-breaking).** If `𝒦_α(β) < ∞`, there is `k₁ ≥ 1`
such that for **all** nearest-integer selections `ρ, ρ'` and **all** label selections
`lam, lam'` and all `k ≥ k₁`: `dist(K y_{n_k+1}, ℤ) = |K y_{n_k+1} - lam_k| < 1/2`, the nearest
integer `s_k = lam_k` to `K y_{n_k+1}` is unique (no tie), and the canonical label
`r_k = lam_k mod K` does not depend on the tie-breaking. -/
theorem S1_label (X : BH) (β : ℝ) (hK : KL X.a β < ⊤) :
    ∃ k1, 1 ≤ k1 ∧ ∀ ρ lam ρ' lam',
      IsNearSel (fun n => (q X.a n : ℝ) * β) ρ → X.IsLabelSel β ρ lam →
      IsNearSel (fun n => (q X.a n : ℝ) * β) ρ' → X.IsLabelSel β ρ' lam' →
      ∀ k, k1 ≤ k →
        |(R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1) - lam k| < 1 / 2 ∧
        (∀ m : ℤ, |(R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1) - m| ≤ 1 / 2 → m = lam k) ∧
        X.lab lam k = X.lab lam' k := by
  obtain ⟨k1, hk1, H⟩ := X.lab_eventually β hK
  refine ⟨k1, hk1, fun ρ lam ρ' lam' hρ hl hρ' hl' k hk => ?_⟩
  obtain ⟨hs, hd0, hd1⟩ := H k hk
  have hk' : 1 ≤ k := le_trans hk1 hk
  obtain ⟨hlam, -, hlt, huniq⟩ := X.lab_core β ρ lam hρ hl k hk' hs
  obtain ⟨hlam', -, -, -⟩ := X.lab_core β ρ' lam' hρ' hl' k hk' hs
  refine ⟨hlt, huniq, ?_⟩
  have e0 : ρ' (X.nk k) = ρ (X.nk k) := near_unique (hρ' _) (hρ _) hd0
  have e1 : ρ' (X.nk (k+1)) = ρ (X.nk (k+1)) := near_unique (hρ' _) (hρ _) hd1
  simp only [BH.lab]
  rw [hlam, hlam']
  simp only [BH.Zl]
  push_cast
  rw [e0, e1, ZMod.natCast_self]
  ring

/-- **§5.2, `g_k → 0`**: for every tie-breaking, `y_{n_k+1} - s_k/K → 0` (`s_k = lam_k`). -/
theorem S1_label_tendsto (X : BH) (β : ℝ) (hK : KL X.a β < ⊤) (ρ lam : ℕ → ℤ)
    (hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ) (hl : X.IsLabelSel β ρ lam) :
    Tendsto (fun k => X.yv β ρ (X.nk k + 1) - lam k / (R6S7.contK X.W : ℝ)) atTop (𝓝 0) := by
  obtain ⟨k1, hk1, H⟩ := X.lab_eventually β hK
  have hKR : (0 : ℝ) < R6S7.contK X.W := by
    exact_mod_cast (by have := R6S7.contK_pos X.W X.hW; omega : 0 < R6S7.contK X.W)
  have hy := (S1a X β hK ρ hρ).1
  have he : Tendsto (fun k => (X.yv β ρ (X.nk (k+1))
      - (R6S7.cseq X.W.tail X.ell : ℝ) * X.yv β ρ (X.nk k)) / (R6S7.contK X.W : ℝ))
      atTop (𝓝 0) := by
    have h := ((hy.comp (tendsto_add_atTop_nat 1)).sub
      (hy.const_mul (R6S7.cseq X.W.tail X.ell : ℝ))).div_const (R6S7.contK X.W : ℝ)
    rw [mul_zero, sub_zero, zero_div] at h
    exact h
  refine he.congr' ?_
  filter_upwards [eventually_ge_atTop k1] with k hk
  obtain ⟨hs, -, -⟩ := H k hk
  obtain ⟨-, heq, -, -⟩ := X.lab_core β ρ lam hρ hl k (le_trans hk1 hk) hs
  rw [← heq, sub_div, mul_div_cancel_left₀ _ hKR.ne']

/-- §5.3: `y_{n_k+i} ≡ c_i s_k/K (mod 1)` up to `o(1)`, for every tie-breaking -/
theorem BH.blk_near (X : BH) (β : ℝ) (hK : KL X.a β < ⊤) (ρ lam : ℕ → ℤ)
    (hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ) (hl : X.IsLabelSel β ρ lam)
    (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ X.ell) :
    Tendsto (fun k => dist0 (X.yv β ρ (X.nk k + i)
      - (R6S7.cc X.W (i-1) : ℝ) * lam k / (R6S7.contK X.W : ℝ))) atTop (𝓝 0) := by
  have hg := S1_label_tendsto X β hK ρ lam hρ hl
  have hy := (S1a X β hK ρ hρ).1
  have hb : Tendsto (fun k => |(R6S7.cc X.W (i-1) : ℝ) * (X.yv β ρ (X.nk k + 1)
      - lam k / (R6S7.contK X.W : ℝ)) + (R6S7.cseq X.W.tail (i-1) : ℝ) * X.yv β ρ (X.nk k)|)
      atTop (𝓝 0) := by
    have h := ((hg.const_mul (R6S7.cc X.W (i-1) : ℝ)).add
      (hy.const_mul (R6S7.cseq X.W.tail (i-1) : ℝ))).abs
    rw [mul_zero, mul_zero, add_zero, abs_zero] at h
    exact h
  refine squeeze_zero (fun k => dist0_nonneg _) (fun k => ?_) hb
  obtain ⟨m, hm⟩ := X.yv_block β ρ k (i-1) (by omega)
  have hcc : R6S7.cseq X.W (i - 1 + 1) = R6S7.cc X.W (i-1) :=
    (R6S7.link X.W X.hW).2.2.2.2.2.2.2.2.1 (i-1)
  rw [hcc, show X.nk k + 1 + (i-1) = X.nk k + i by omega] at hm
  rw [dist0_of_eq_add_int (y := (R6S7.cc X.W (i-1) : ℝ) * (X.yv β ρ (X.nk k + 1)
      - lam k / (R6S7.contK X.W : ℝ)) + (R6S7.cseq X.W.tail (i-1) : ℝ) * X.yv β ρ (X.nk k))
    ⟨m, by rw [hm]; ring⟩]
  exact dist0_le_abs _

/-! ## Part 5. R6-S1(b) -/

/-- **R6-S1(b)** (`proofs/R6-S2.md` §5.3–§5.4). Let `𝒦_α(β) < ∞`. For every tie-breaking
`ρ` of `round(q_nβ)` and every tie-breaking `lam` of `round(K y_{n_k+1})`, the canonical labels
`r_k = lab lam k ∈ ℤ/K` satisfy:
* for `1 ≤ i ≤ ℓ`, `|y_{n_k+i}| - d_K(c_i r_k)/K → 0` (`c_i = cc W (i-1)`);
* `(t_k)` is bounded;
* `dist(t_{k+1} - (r_{k+1} - σ r_k)/K, ℤ) → 0`. -/
theorem S1b (X : BH) (β : ℝ) (hK : KL X.a β < ⊤) (ρ lam : ℕ → ℤ)
    (hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ) (hl : X.IsLabelSel β ρ lam) :
    (∀ i, 1 ≤ i → i ≤ X.ell → Tendsto (fun k => |X.yv β ρ (X.nk k + i)|
      - (R6S7.dK (R6S7.contK X.W) ((R6S7.cc X.W (i-1) : ℤ) * ((X.lab lam k).val : ℤ)) : ℝ)
        / (R6S7.contK X.W : ℝ)) atTop (𝓝 0)) ∧
    (∃ B : ℝ, ∀ k, |X.tv β ρ k| ≤ B) ∧
    Tendsto (fun k => dist0 (X.tv β ρ (k+1) - (((X.lab lam (k+1)).val : ℝ)
      - (R6S7.sigma X.W : ℝ) * ((X.lab lam k).val : ℝ)) / (R6S7.contK X.W : ℝ))) atTop (𝓝 0) := by
  have hK1 : 1 ≤ R6S7.contK X.W := R6S7.contK_pos X.W X.hW
  have hKR : (0 : ℝ) < R6S7.contK X.W := by exact_mod_cast (by omega : 0 < R6S7.contK X.W)
  refine ⟨fun i hi1 hi2 => ?_, ?_, ?_⟩
  · ---------------- first clause
    have hb := X.blk_near β hK ρ lam hρ hl i hi1 hi2
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun k => abs_nonneg _) (fun k => ?_) hb
    have e1 : |X.yv β ρ (X.nk k + i)| = dist0 (X.yv β ρ (X.nk k + i)) := by
      rw [X.abs_yv β ρ hρ, X.dist0_yv]
    obtain ⟨m, hm⟩ := X.lab_val lam k
    have e2 : (R6S7.dK (R6S7.contK X.W) ((R6S7.cc X.W (i-1) : ℤ) * ((X.lab lam k).val : ℤ)) : ℝ)
        / (R6S7.contK X.W : ℝ) = dist0 ((R6S7.cc X.W (i-1) : ℝ) * lam k / (R6S7.contK X.W : ℝ)) := by
      rw [← dist0_div_eq_dK _ hK1]
      refine dist0_of_eq_add_int ⟨(R6S7.cc X.W (i-1) : ℤ) * m, ?_⟩
      push_cast
      rw [hm]
      field_simp
    simp only [Function.comp_apply]
    rw [e1, e2]
    exact dist0_sub_dist0_le _ _
  · ---------------- `(t_k)` bounded
    obtain ⟨M, hM⟩ := KL_lt_top_bound X.isCF β hK
    have hM' := X.nk_tendsto.eventually hM
    have hev : ∀ᶠ k in atTop, |X.tv β ρ k| ≤ max M 0 := by
      filter_upwards [hM', eventually_ge_atTop 1] with k hk hk1
      have ht := X.theta_pos (X.nk k)
      have hAθ := X.A_theta_lt_one k hk1
      have hA0 : (0 : ℝ) ≤ X.A k := Nat.cast_nonneg _
      have hd : dist0 ((q X.a (X.nk k) : ℝ) * β) ≤ max M 0 * theta X.a (X.nk k) := by
        have := (div_le_iff₀ ht).1 hk
        nlinarith [le_max_left M 0, le_max_right M 0]
      simp only [BH.tv]
      rw [abs_mul, abs_of_nonneg hA0, X.abs_yv β ρ hρ]
      calc (X.A k : ℝ) * dist0 ((q X.a (X.nk k) : ℝ) * β)
          ≤ (X.A k : ℝ) * (max M 0 * theta X.a (X.nk k)) := mul_le_mul_of_nonneg_left hd hA0
        _ = ((X.A k : ℝ) * theta X.a (X.nk k)) * max M 0 := by ring
        _ ≤ 1 * max M 0 := mul_le_mul_of_nonneg_right hAθ.le (le_max_right _ _)
        _ = max M 0 := one_mul _
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
    refine ⟨max (max M 0) (∑ k ∈ Finset.range N0, |X.tv β ρ k|), fun k => ?_⟩
    rcases lt_or_ge k N0 with h | h
    · exact le_max_of_le_right (Finset.single_le_sum (f := fun j => |X.tv β ρ j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.2 h))
    · exact le_max_of_le_left (hN0 k h)
  · ---------------- coupling
    have H3 : Tendsto (fun k => dist0 (X.yv β ρ (X.nk k + X.ell)
        - (R6S7.sigma X.W : ℝ) * lam k / (R6S7.contK X.W : ℝ))) atTop (𝓝 0) := by
      by_cases hl0 : X.ell = 0
      · have hW : X.W = [] := List.eq_nil_of_length_eq_zero hl0
        have hKe : R6S7.contK X.W = 1 := by rw [hW]; rfl
        have hse : R6S7.sigma X.W = 1 := by simp [R6S7.sigma, hW]
        have hy := (S1a X β hK ρ hρ).1.abs
        rw [abs_zero] at hy
        refine squeeze_zero (fun k => dist0_nonneg _) (fun k => ?_) hy
        rw [hl0, add_zero, hKe, hse]
        rw [dist0_of_eq_add_int (y := X.yv β ρ (X.nk k)) ⟨-lam k, by push_cast; ring⟩]
        exact dist0_le_abs _
      · have hσ : R6S7.cc X.W (X.ell - 1) = R6S7.sigma X.W := by
          have hl0' : X.W.length ≠ 0 := hl0
          simp only [R6S7.cc, R6S7.sigma, hl0', ite_false, List.dropLast_eq_take, BH.ell]
        have h := X.blk_near β hK ρ lam hρ hl X.ell (by omega) le_rfl
        rw [hσ] at h
        exact h
    have hg := (S1_label_tendsto X β hK ρ lam hρ hl).comp (tendsto_add_atTop_nat 1)
    have hb := hg.abs.add H3
    rw [abs_zero, zero_add] at hb
    refine squeeze_zero' (Eventually.of_forall fun k => dist0_nonneg _) ?_ hb
    filter_upwards [eventually_ge_atTop 1] with k hk
    obtain ⟨m, hm⟩ := X.yv_big β ρ k hk
    obtain ⟨m1, hm1⟩ := X.lab_val lam (k+1)
    obtain ⟨m0, hm0⟩ := X.lab_val lam k
    have e : X.tv β ρ (k+1) - (((X.lab lam (k+1)).val : ℝ)
        - (R6S7.sigma X.W : ℝ) * ((X.lab lam k).val : ℝ)) / (R6S7.contK X.W : ℝ) =
        ((X.yv β ρ (X.nk (k+1) + 1) - lam (k+1) / (R6S7.contK X.W : ℝ))
          + -(X.yv β ρ (X.nk k + X.ell) - (R6S7.sigma X.W : ℝ) * lam k / (R6S7.contK X.W : ℝ)))
        + ((-m - m1 + (R6S7.sigma X.W : ℤ) * m0 : ℤ) : ℝ) := by
      rw [hm1, hm0, hm]; push_cast; field_simp; ring
    rw [e, dist0_add_int]
    refine (dist0_add_le _ _).trans ?_
    rw [dist0_neg]
    have := dist0_le_abs (X.yv β ρ (X.nk (k+1) + 1) - lam (k+1) / (R6S7.contK X.W : ℝ))
    simp only [Function.comp_apply]
    linarith

/-! ## Part 6. R6-S1(c) -/

theorem abs_eps_le_inv {a : ℕ → ℤ} (ha : IsCF a) (n : ℕ) : |eps a n| ≤ 1 / (q a n : ℝ) :=
  (abs_eps_lt ha n).le.trans (one_div_le_one_div_of_le (qR_pos ha n) (qR_mono ha (by omega)))

theorem abs_eps_tendsto {a : ℕ → ℤ} (ha : IsCF a) :
    Tendsto (fun n => |eps a n|) atTop (𝓝 0) := by
  have h := (q_tendsto ha).inv_tendsto_atTop
  refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) h
  have := abs_eps_le_inv ha n
  simpa [one_div] using this

/-- for `β = uα + v`, eventually `y_n = u ε_n` (any tie-breaking) -/
theorem BH.yv_lattice (X : BH) (β : ℝ) (ρ : ℕ → ℤ)
    (hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ) (u v : ℤ) (hβ : β = u * alpha X.a + v) :
    ∀ᶠ n in atTop, X.yv β ρ n = u * eps X.a n := by
  have hev := ((abs_eps_tendsto X.isCF).const_mul |(u : ℝ)|)
  rw [mul_zero] at hev
  filter_upwards [(tendsto_order.1 hev).2 (1 / 2) (by norm_num)] with n hn
  have hsmall : |(u : ℝ) * eps X.a n| < 1 / 2 := by rw [abs_mul]; exact hn
  have e : X.yv β ρ n = u * eps X.a n + ((u * p X.a n + v * q X.a n - ρ n : ℤ) : ℝ) := by
    simp only [BH.yv, eps]; rw [hβ]; push_cast; ring
  have hint : (u * p X.a n + v * q X.a n - ρ n : ℤ) = 0 := by
    apply int_eq_of_close
    have e2 : (((u * p X.a n + v * q X.a n - ρ n : ℤ) : ℝ) - ((0 : ℤ) : ℝ)) =
        X.yv β ρ n - u * eps X.a n := by rw [e]; push_cast; ring
    rw [e2]
    have hy : |X.yv β ρ n| ≤ 1 / 2 := hρ n
    calc |X.yv β ρ n - u * eps X.a n| ≤ |X.yv β ρ n| + |(u : ℝ) * eps X.a n| := abs_sub _ _
      _ < 1 := by linarith
  rw [e, hint]; simp

/-- **R6-S1(c)** (`proofs/R6-S2.md` §5.5). Let `𝒦_α(β) < ∞`. For every tie-breaking `ρ` of
`round(q_nβ)` and every tie-breaking `lam` of `round(K y_{n_k+1})`:
`β ∈ ℤα + ℤ ⟺ (eventually r_k = 0) ∧ t_k → 0`, where `r_k = lab lam k` is the canonical label. -/
theorem S1c (X : BH) (β : ℝ) (hK : KL X.a β < ⊤) (ρ lam : ℕ → ℤ)
    (hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ) (hl : X.IsLabelSel β ρ lam) :
    β ∈ lattice (alpha X.a) ↔
      ((∀ᶠ k in atTop, X.lab lam k = 0) ∧ Tendsto (X.tv β ρ) atTop (𝓝 0)) := by
  have hK1 : 1 ≤ R6S7.contK X.W := R6S7.contK_pos X.W X.hW
  have : NeZero (R6S7.contK X.W) := ⟨by omega⟩
  have hKR : (0 : ℝ) < R6S7.contK X.W := by exact_mod_cast (by omega : 0 < R6S7.contK X.W)
  constructor
  · ---------------- (⇒)
    rintro ⟨u, v, hβ⟩
    have hyl := X.yv_lattice β ρ hρ u v hβ
    refine ⟨?_, ?_⟩
    · -- labels: `K y_{n_k+1} = K u ε_{n_k+1} → 0`
      have h1 : Tendsto (fun k => X.nk k + 1) atTop atTop :=
        (tendsto_add_atTop_nat 1).comp X.nk_tendsto
      have hev := ((abs_eps_tendsto X.isCF).const_mul ((R6S7.contK X.W : ℝ) * |(u : ℝ)|))
      rw [mul_zero] at hev
      have hev2 := h1.eventually ((tendsto_order.1 hev).2 (1 / 2) (by norm_num))
      filter_upwards [hev2, h1.eventually hyl] with k hk hyk
      have hlk : |(R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1) - lam k| ≤ 1 / 2 := hl k
      have hsmall : |(R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1)| < 1 / 2 := by
        rw [hyk, abs_mul, abs_mul, abs_of_pos hKR, ← mul_assoc]; exact hk
      have h0 : lam k = 0 := by
        apply int_eq_of_close
        have e : ((lam k : ℝ) - ((0 : ℤ) : ℝ)) = (R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1)
            - ((R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1) - lam k) := by push_cast; ring
        rw [e]
        calc _ ≤ |(R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1)|
              + |(R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1) - lam k| := abs_sub _ _
          _ < 1 := by linarith
      simp only [BH.lab, h0, Int.cast_zero]
    · -- `|t_k| ≤ |u| / q_{n_k} → 0`
      have hq : Tendsto (fun k => (q X.a (X.nk k) : ℝ)⁻¹) atTop (𝓝 0) :=
        ((q_tendsto X.isCF).comp X.nk_tendsto).inv_tendsto_atTop
      have hb := hq.const_mul |(u : ℝ)|
      rw [mul_zero] at hb
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun k => abs_nonneg _) ?_ hb
      filter_upwards [X.nk_tendsto.eventually hyl, eventually_ge_atTop 1] with k hyk hk1
      have hA0 : (0 : ℝ) ≤ X.A k := Nat.cast_nonneg _
      have hqp := qR_pos X.isCF (X.nk k)
      have hq1 := qR_pos X.isCF (X.nk k + 1)
      have hstep : (X.A k : ℝ) * q X.a (X.nk k) ≤ q X.a (X.nk k + 1) := by
        have h := q_step X.isCF (X.nk k)
        rw [X.a_big k hk1] at h
        exact_mod_cast h
      have he := abs_eps_lt X.isCF (X.nk k)
      have he' : |eps X.a (X.nk k)| * q X.a (X.nk k + 1) < 1 := by
        rwa [lt_div_iff₀ hq1] at he
      have hAe : (X.A k : ℝ) * |eps X.a (X.nk k)| ≤ (q X.a (X.nk k) : ℝ)⁻¹ := by
        rw [← one_div, le_div_iff₀ hqp]
        nlinarith [abs_nonneg (eps X.a (X.nk k)),
          mul_le_mul_of_nonneg_left hstep (abs_nonneg (eps X.a (X.nk k)))]
      simp only [Function.comp_apply, BH.tv]
      rw [hyk, abs_mul, abs_mul, abs_of_nonneg hA0]
      calc (X.A k : ℝ) * (|(u : ℝ)| * |eps X.a (X.nk k)|)
          = |(u : ℝ)| * ((X.A k : ℝ) * |eps X.a (X.nk k)|) := by ring
        _ ≤ |(u : ℝ)| * (q X.a (X.nk k) : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hAe (abs_nonneg _)
  · ---------------- (⇐): `R_n → 0`, then Lemma 0
    rintro ⟨hlab, ht⟩
    have hSpos : (0 : ℝ) < (X.W.sum : ℝ) + 2 := by positivity
    have hEi : ∀ i ∈ Finset.Icc 1 X.ell, ∀ᶠ k in atTop,
        dist0 ((q X.a (X.nk k + i) : ℝ) * β) < 1 / (4 * ((X.W.sum : ℝ) + 2)) := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
      have hb := X.blk_near β hK ρ lam hρ hl i hi1 hi2
      have hb' : Tendsto (fun k => dist0 ((q X.a (X.nk k + i) : ℝ) * β)) atTop (𝓝 0) := by
        refine hb.congr' ?_
        filter_upwards [hlab] with k hk
        have hk' : ((lam k : ℤ) : ZMod (R6S7.contK X.W)) = 0 := hk
        obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hk'
        rw [← X.dist0_yv β ρ]
        refine dist0_of_eq_add_int ⟨-((R6S7.cc X.W (i-1) : ℤ) * w), ?_⟩
        rw [hw]; push_cast; field_simp; ring
      exact (tendsto_order.1 hb').2 _ (by positivity)
    have hE0 : ∀ᶠ k in atTop, |X.tv β ρ k| < 1 / 12 := by
      have h := ht.abs
      rw [abs_zero] at h
      exact (tendsto_order.1 h).2 _ (by norm_num)
    obtain ⟨k0, hk0⟩ := eventually_atTop.1
      ((hE0.and ((Filter.eventually_all_finset (Finset.Icc 1 X.ell)).2 hEi)).and
        (eventually_ge_atTop 1))
    have hk01 : 1 ≤ k0 := (hk0 k0 le_rfl).2
    refine lemma0 X.isCF β (X.nk k0) (fun n hn => ?_)
    obtain ⟨k, i, hk, hi, rfl⟩ := X.block_of k0 hk01 n hn
    obtain ⟨⟨ht0, hti⟩, hk1⟩ := hk0 k hk
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · -- big index `n = n_k`: `‖q_{n_k}β‖ = |t_k|/A_k`, `θ_{n_k} > 1/(3A_k)`
      rw [add_zero]
      have hA : (1 : ℝ) ≤ X.A k := by exact_mod_cast X.hA k hk1
      have hθ := (X.inv_theta_nk k hk1).2
      have hθp := X.theta_pos (X.nk k)
      have hd : dist0 ((q X.a (X.nk k) : ℝ) * β) * X.A k = |X.tv β ρ k| := by
        rw [← X.abs_yv β ρ hρ]
        simp only [BH.tv]
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ X.A k)]; ring
      rw [div_lt_iff₀ hθp] at hθ
      have h4 : (4 * dist0 ((q X.a (X.nk k) : ℝ) * β)) * (3 * X.A k)
          < theta X.a (X.nk k) * (3 * X.A k) := by nlinarith
      have h5 := lt_of_mul_lt_mul_right h4 (by positivity)
      linarith
    · -- `n = n_k + i`, `1 ≤ i ≤ ℓ`: `a_{n+1} = w_i`, so `θ_n > 1/(Σ W + 2)`
      have hd := hti i (Finset.mem_Icc.2 ⟨hipos, hi⟩)
      have hθ := (inv_theta_mem X.isCF (X.nk k + i)).2
      have ha : X.a (X.nk k + i + 1) ≤ (X.W.sum : ℤ) := by
        rw [show X.nk k + i + 1 = X.nk k + 1 + i by ring, X.a_word k i hipos hi]
        exact Nat.cast_le.2 (List.le_sum_of_mem (List.getElem_mem _))
      have haR : ((X.a (X.nk k + i + 1) : ℤ) : ℝ) ≤ (((X.W.sum : ℕ) : ℤ) : ℝ) := Int.cast_le.2 ha
      rw [Int.cast_natCast] at haR
      have hθp := X.theta_pos (X.nk k + i)
      rw [div_lt_iff₀ hθp] at hθ
      rw [lt_div_iff₀ (by positivity)] at hd
      have h1 : 1 < theta X.a (X.nk k + i) * ((X.W.sum : ℝ) + 2) := by nlinarith
      nlinarith


/-! ## Part 7. Block limits of `R_n = ‖q_nβ‖/θ_n` (preparation for §7, step 3) -/

/-- `R_{n_k} - |t_k| → 0` (any tie-breaking) -/
theorem R_big_tendsto (X : BH) (β : ℝ) (hK : KL X.a β < ⊤) (ρ : ℕ → ℤ)
    (hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ) :
    Tendsto (fun k => dist0 ((q X.a (X.nk k) : ℝ) * β) / theta X.a (X.nk k) - |X.tv β ρ k|)
      atTop (𝓝 0) := by
  have hl : X.IsLabelSel β ρ (fun k => round ((R6S7.contK X.W : ℝ) * X.yv β ρ (X.nk k + 1))) :=
    fun _ => abs_sub_round _
  obtain ⟨B, hB⟩ := (S1b X β hK ρ _ hρ hl).2.1
  have hinv : Tendsto (fun k => ((X.A k : ℝ) * theta X.a (X.nk k))⁻¹ - 1) atTop (𝓝 0) := by
    have h := (X.A_theta_tendsto.inv₀ one_ne_zero).sub_const 1
    rw [inv_one, sub_self] at h
    exact h
  have hb := (hinv.abs.const_mul B)
  rw [abs_zero, mul_zero] at hb
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hA : (1 : ℝ) ≤ X.A k := by exact_mod_cast X.hA k hk
  have ht := X.theta_pos (X.nk k)
  have e : dist0 ((q X.a (X.nk k) : ℝ) * β) / theta X.a (X.nk k) - |X.tv β ρ k| =
      |X.tv β ρ k| * (((X.A k : ℝ) * theta X.a (X.nk k))⁻¹ - 1) := by
    rw [← X.abs_yv β ρ hρ]
    simp only [BH.tv]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ X.A k)]
    field_simp
  rw [Real.norm_eq_abs, e, abs_mul]
  exact mul_le_mul_of_nonneg_right ((abs_abs _).le.trans (hB k)) (abs_nonneg _)

/-- for `1 ≤ i ≤ ℓ`: `R_{n_k+i} - v_i(r_k) → 0`, where
`v_i(r) = d_K(c_i r)/(c_i c'_i) = vterm W r (i-1)` and `r_k` is the canonical label -/
theorem R_word_tendsto (X : BH) (β : ℝ) (hK : KL X.a β < ⊤) (ρ lam : ℕ → ℤ)
    (hρ : IsNearSel (fun n => (q X.a n : ℝ) * β) ρ) (hl : X.IsLabelSel β ρ lam)
    (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ X.ell) :
    Tendsto (fun k => dist0 ((q X.a (X.nk k + i) : ℝ) * β) / theta X.a (X.nk k + i)
      - ((R6S7.vterm X.W (X.lab lam k) (i-1) : ℚ) : ℝ)) atTop (𝓝 0) := by
  have hK1 : 1 ≤ R6S7.contK X.W := R6S7.contK_pos X.W X.hW
  have hKR : (0 : ℝ) < R6S7.contK X.W := by exact_mod_cast (by omega : 0 < R6S7.contK X.W)
  have hcpos : (0 : ℝ) < R6S7.cc X.W (i-1) := by
    have := R6S7.contK_pos (X.W.take (i-1)) (fun x hx => X.hW x (List.mem_of_mem_take hx))
    unfold R6S7.cc; exact_mod_cast (by omega : 0 < R6S7.contK (X.W.take (i-1)))
  have hc'pos : (0 : ℝ) < R6S7.cc' X.W (i-1) := by
    have h := contK_pos_drop X.W X.hW i
    simpa [R6S7.cc', show i - 1 + 1 = i by omega] using h
  set L : ℝ := (R6S7.contK X.W : ℝ) / ((R6S7.cc X.W (i-1) : ℝ) * R6S7.cc' X.W (i-1)) with hL
  set D : ℕ → ℝ := fun k =>
    (R6S7.dK (R6S7.contK X.W) ((R6S7.cc X.W (i-1) : ℤ) * ((X.lab lam k).val : ℤ)) : ℝ)
      / (R6S7.contK X.W : ℝ) with hDdef
  have hD : ∀ k, 0 ≤ D k ∧ D k ≤ 1 := by
    intro k
    refine ⟨by positivity, ?_⟩
    simp only [hDdef]
    rw [div_le_one hKR]
    have : R6S7.dK (R6S7.contK X.W) ((R6S7.cc X.W (i-1) : ℤ) * ((X.lab lam k).val : ℤ))
        ≤ R6S7.contK X.W := by
      unfold R6S7.dK; exact (min_le_right _ _).trans (Nat.sub_le _ _)
    exact_mod_cast this
  have hb := (S1b X β hK ρ lam hρ hl).1 i hi1 hi2
  have h4 := B4 X i hi1 hi2
  have h1 := hb.mul h4
  rw [zero_mul] at h1
  have h2 : Tendsto (fun k => D k * (1 / theta X.a (X.nk k + i) - L)) atTop (𝓝 0) := by
    have h := (h4.sub_const L).abs
    rw [sub_self, abs_zero] at h
    refine squeeze_zero_norm (fun k => ?_) h
    rw [Real.norm_eq_abs, abs_mul]
    have := hD k
    rw [abs_of_nonneg this.1]
    exact mul_le_of_le_one_left (abs_nonneg _) this.2
  have h12 := h1.add h2
  rw [add_zero] at h12
  refine h12.congr (fun k => ?_)
  have ht := X.theta_pos (X.nk k + i)
  simp only [hDdef, hL, R6S7.vterm]
  rw [← X.abs_yv β ρ hρ]
  push_cast
  field_simp
  ring


/-- (§6, C1–C2 wrapper) `ν(W)` is attained: `IsLeast (costSet W) (ν W)` -/
theorem nu_isLeast (W : List ℕ) (hW : ∀ x ∈ W, 1 ≤ x) : IsLeast (R6S7.costSet W) (R6S7.nu W) := by
  have hK1 := R6S7.contK_pos W hW
  rcases Nat.lt_or_ge (R6S7.contK W) 2 with h | h
  · have h1 := R6S7.cor2_K_eq_one W (by omega)
    rw [h1.2.1]; exact h1.1
  · have h2 := R6S7.cor2_K_ge_two W hW h
    rw [h2.2.1]; exact h2.1

end R6S2

#print axioms R6S2.int_eq_of_close
#print axioms R6S2.dist0_add_int
#print axioms R6S2.dist0_add_le
#print axioms R6S2.dist0_neg
#print axioms R6S2.dist0_sub_dist0_le
#print axioms R6S2.dist0_div_eq_dK
#print axioms R6S2.near_int_unique
#print axioms R6S2.near_unique
#print axioms R6S2.dist0_label_rep
#print axioms R6S2.lemma0
#print axioms R6S2.exists_isCF_alpha
#print axioms R6S2.cstar_ge_quarter_irrational
#print axioms R6S2.cor0'
#print axioms R6S2.cstar_ge_quarter
#print axioms R6S2.BH.q_block
#print axioms R6S2.BH.yv_block
#print axioms R6S2.BH.Ky_eq
#print axioms R6S2.BH.yv_big
#print axioms R6S2.BH.dist0_nk_tendsto
#print axioms R6S2.BH.lab_val
#print axioms R6S2.BH.block_of
#print axioms R6S2.BH.lab_core
#print axioms R6S2.BH.lab_eventually
#print axioms R6S2.S1_label
#print axioms R6S2.S1_label_tendsto
#print axioms R6S2.BH.blk_near
#print axioms R6S2.S1b
#print axioms R6S2.abs_eps_le_inv
#print axioms R6S2.abs_eps_tendsto
#print axioms R6S2.BH.yv_lattice
#print axioms R6S2.S1c
#print axioms R6S2.R_big_tendsto
#print axioms R6S2.R_word_tendsto
#print axioms R6S2.nu_isLeast
