import EpiFormal.R6S7Mstar
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# R6-S2 (KL sharp constant of block Hurwitz numbers): statement and base layer

Phase 1 of the formalization of R6-S2 (`proofs/R6-S2.md` v2, PASSED_L2).

* All objects of PLAN_GRAPH.md §S.1 that R6-S2 mentions are defined here, literally:
  block Hurwitz data `BH` (partial quotients by position, `n_k = N + (k-1)(ℓ+1)`), the
  convergents `p_n, q_n` (F1), the value `α = lim p_n/q_n` (`alpha`, `tendsto_conv`,
  `cf_algorithm`), `θ_n` (`theta`), `‖·‖` (`dist0`), `𝒦_α(β)` (`KL`, a `limsup` in `ℝ≥0∞`),
  `c*(α)` (`cstar`) and the lattice `ℤα+ℤ`. The constant `ν(W)` is `R6S7.nu` (reused, not
  redefined).
* `StatementR6S2` is the main statement of R6-S2, as a `Prop`. It is **not** proved in this
  module; only `nu_bounds` (the clause `1/4 ≤ ν ≤ 1`) and `cstar_only_W` (the clause
  "depends only on `W`", derived from `StatementR6S2`) are proved.
* Proved base layer: F1, F2 (`det`), D1, convergence, F3 (`alpha_eq`, `cq_rec`, `cq_gt`,
  `cq_lt`), D2 (`eps_eq`, `theta_eq`, `theta_lt`, `abs_eps_lt`), D3 (`D3_eq`, `Dm_rec`),
  (A1) (`A1`), (A2a) (`A2a`), B1 (`inv_theta_mem`, `BH.inv_theta_nk`).

No proof-escape tactics, no project axioms; standalone apart from `EpiFormal.R6S7Mstar`.
-/

open Filter Topology

namespace R6S2

/-! ## Part 1. Two-term recurrences (F1, F2, D1) -/

/-- shifted two-term recurrence: index `m` here is CF index `m - 1`. -/
def crec (a : ℕ → ℤ) (x y : ℤ) : ℕ → ℤ
  | 0 => x
  | 1 => y
  | (m+2) => a (m+1) * crec a x y (m+1) + crec a x y m

@[simp] theorem crec_zero (a : ℕ → ℤ) (x y : ℤ) : crec a x y 0 = x := rfl
@[simp] theorem crec_one (a : ℕ → ℤ) (x y : ℤ) : crec a x y 1 = y := rfl
theorem crec_succ_succ (a : ℕ → ℤ) (x y : ℤ) (m : ℕ) :
    crec a x y (m+2) = a (m+1) * crec a x y (m+1) + crec a x y m := rfl

/-- linearity of the recurrence in the initial data -/
theorem crec_linear (a : ℕ → ℤ) (u v x y x' y' : ℤ) : ∀ m,
    crec a (u * x + v * x') (u * y + v * y') m = u * crec a x y m + v * crec a x' y' m
  | 0 => rfl
  | 1 => rfl
  | (m+2) => by
    rw [crec_succ_succ, crec_succ_succ, crec_succ_succ, crec_linear a u v x y x' y' (m+1),
      crec_linear a u v x y x' y' m]
    ring

/-- the regular continued fraction hypothesis: `a n ≥ 1` for `n ≥ 1` (`a 0 ∈ ℤ` arbitrary) -/
def IsCF (a : ℕ → ℤ) : Prop := ∀ n, 1 ≤ n → 1 ≤ a n

/-- `qq a m = q_{m-1}`: `qq a 0 = q_{-1} = 0`, `qq a 1 = q_0 = 1` -/
def qq (a : ℕ → ℤ) : ℕ → ℤ := crec a 0 1
/-- `pp a m = p_{m-1}`: `pp a 0 = p_{-1} = 1`, `pp a 1 = p_0 = a_0` -/
def pp (a : ℕ → ℤ) : ℕ → ℤ := crec a 1 (a 0)
/-- convergent denominator `q_n` (`n ≥ 0`), F1 -/
def q (a : ℕ → ℤ) (n : ℕ) : ℤ := qq a (n+1)
/-- convergent numerator `p_n` (`n ≥ 0`), F1 -/
def p (a : ℕ → ℤ) (n : ℕ) : ℤ := pp a (n+1)

theorem q_zero (a : ℕ → ℤ) : q a 0 = 1 := rfl
theorem p_zero (a : ℕ → ℤ) : p a 0 = a 0 := rfl
theorem qq_zero (a : ℕ → ℤ) : qq a 0 = 0 := rfl
theorem pp_zero (a : ℕ → ℤ) : pp a 0 = 1 := rfl
theorem q_one (a : ℕ → ℤ) : q a 1 = a 1 := by simp [q, qq, crec_succ_succ]
theorem p_one (a : ℕ → ℤ) : p a 1 = a 1 * a 0 + 1 := by simp [p, pp, crec_succ_succ]
/-- F1: `q_{n+1} = a_{n+1} q_n + q_{n-1}` (with `q_{-1} = qq a 0 = 0`) -/
theorem q_succ (a : ℕ → ℤ) (n : ℕ) : q a (n+1) = a (n+1) * q a n + qq a n := rfl
theorem p_succ (a : ℕ → ℤ) (n : ℕ) : p a (n+1) = a (n+1) * p a n + pp a n := rfl
theorem qq_succ (a : ℕ → ℤ) (n : ℕ) : qq a (n+1) = q a n := rfl
theorem pp_succ (a : ℕ → ℤ) (n : ℕ) : pp a (n+1) = p a n := rfl

/-- F2 (shifted form) -/
theorem det_shift (a : ℕ → ℤ) : ∀ m : ℕ,
    pp a (m+1) * qq a m - pp a m * qq a (m+1) = (-1) ^ (m+1)
  | 0 => by simp [pp, qq]
  | (m+1) => by
    have ih := det_shift a m
    simp only [pp, qq] at ih ⊢
    rw [crec_succ_succ, crec_succ_succ, pow_succ]
    linear_combination (-1 : ℤ) * ih

/-- F2: `p_{n+1} q_n - p_n q_{n+1} = (-1)^n` -/
theorem det (a : ℕ → ℤ) (n : ℕ) : p a (n+1) * q a n - p a n * q a (n+1) = (-1) ^ n := by
  have h := det_shift a (n+1)
  simp only [p, q]
  rw [h, pow_succ, pow_succ]; ring

/-- F2 at index `n - 1`: `q_n p_{n-1} - p_n q_{n-1} = (-1)^n` -/
theorem det' (a : ℕ → ℤ) (n : ℕ) : q a n * pp a n - p a n * qq a n = (-1) ^ n := by
  have h := det_shift a n
  simp only [p, q]
  rw [pow_succ] at h
  linear_combination (-1 : ℤ) * h

section D1

variable {a : ℕ → ℤ}

theorem qq_facts (ha : IsCF a) : ∀ m, 0 ≤ qq a m ∧ 1 ≤ qq a (m+1) ∧ qq a m ≤ qq a (m+1)
  | 0 => by simp [qq]
  | (m+1) => by
    obtain ⟨h0, h1, h2⟩ := qq_facts ha m
    have hA := ha (m+1) (by omega)
    have e : qq a (m+2) = a (m+1) * qq a (m+1) + qq a m := crec_succ_succ _ _ _ _
    refine ⟨by omega, ?_, ?_⟩
    · rw [e]; nlinarith
    · rw [e]; nlinarith

theorem qq_nonneg (ha : IsCF a) (m : ℕ) : 0 ≤ qq a m := (qq_facts ha m).1
/-- D1: `q_n ≥ 1` -/
theorem q_pos (ha : IsCF a) (n : ℕ) : 1 ≤ q a n := (qq_facts ha n).2.1
/-- D1: `q_{n-1} ≤ q_n` -/
theorem qq_le_q (ha : IsCF a) (n : ℕ) : qq a n ≤ q a n := (qq_facts ha n).2.2
/-- D1: `q_n ≤ q_{n+1}` -/
theorem q_mono_succ (ha : IsCF a) (n : ℕ) : q a n ≤ q a (n+1) := qq_le_q ha (n+1)
/-- D1: `a_{n+1} q_n ≤ q_{n+1}` -/
theorem q_step (ha : IsCF a) (n : ℕ) : a (n+1) * q a n ≤ q a (n+1) := by
  rw [q_succ]; have := qq_nonneg ha n; linarith
/-- D1: `2 q_n ≤ q_{n+2}` -/
theorem q_two (ha : IsCF a) (n : ℕ) : 2 * q a n ≤ q a (n+2) := by
  have e : q a (n+2) = a (n+2) * q a (n+1) + q a n := q_succ a (n+1)
  have h1 := q_mono_succ ha n
  have h2 := ha (n+2) (by omega)
  have h3 := q_pos ha (n+1)
  rw [e]; nlinarith

theorem q_monotone (ha : IsCF a) : Monotone (q a) :=
  monotone_nat_of_le_succ (q_mono_succ ha)

/-- `q_n ≥ n` -/
theorem q_ge_self (ha : IsCF a) : ∀ n : ℕ, (n : ℤ) ≤ q a n ∧ ((n : ℤ) + 1 ≤ q a (n+1))
  | 0 => by
    refine ⟨by rw [q_zero]; norm_num, ?_⟩
    rw [q_one]; have := ha 1 le_rfl; simpa using this
  | (n+1) => by
    obtain ⟨h0, h1⟩ := q_ge_self ha n
    refine ⟨by exact_mod_cast h1, ?_⟩
    have e : q a (n+2) = a (n+2) * q a (n+1) + q a n := q_succ a (n+1)
    have h2 := ha (n+2) (by omega)
    have h3 := q_pos ha n
    have h4 := q_pos ha (n+1)
    push_cast
    rw [e]; nlinarith

/-- D1: `q_n → ∞` -/
theorem q_tendsto (ha : IsCF a) : Tendsto (fun n => (q a n : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  exact_mod_cast (q_ge_self ha n).1

/-- `q_n q_{n+1} ≥ 2^n` -/
theorem q_mul_ge (ha : IsCF a) : ∀ n, (2 : ℤ) ^ n ≤ q a n * q a (n+1)
  | 0 => by rw [q_zero, one_mul, pow_zero]; exact q_pos ha 1
  | (n+1) => by
    have ih := q_mul_ge ha n
    have h2 := q_two ha n
    have h1 := q_pos ha (n+1)
    rw [pow_succ]
    nlinarith

end D1

/-! ## Part 2. The value `α = [a_0; a_1, a_2, …]` and the convergents -/

/-- `(-1)^j / (q_j q_{j+1})` -/
noncomputable def term (a : ℕ → ℤ) (j : ℕ) : ℝ := (-1 : ℝ) ^ j / ((q a j : ℝ) * q a (j+1))

/-- the value of the infinite continued fraction (`α = a_0 + Σ_j (-1)^j/(q_j q_{j+1})`);
`tendsto_conv` shows it is `lim p_n/q_n`. -/
noncomputable def alpha (a : ℕ → ℤ) : ℝ := (a 0 : ℝ) + ∑' j, term a j

section Conv

variable {a : ℕ → ℤ}

theorem qR_pos (ha : IsCF a) (n : ℕ) : (0 : ℝ) < q a n := by
  have := q_pos ha n; exact_mod_cast (by omega : (0 : ℤ) < q a n)

theorem abs_term_le (ha : IsCF a) (j : ℕ) : |term a j| ≤ (1 / 2 : ℝ) ^ j := by
  have h := q_mul_ge ha j
  have hR : (2 : ℝ) ^ j ≤ (q a j : ℝ) * q a (j+1) := by exact_mod_cast h
  have hp : (0 : ℝ) < (q a j : ℝ) * q a (j+1) := mul_pos (qR_pos ha j) (qR_pos ha (j+1))
  unfold term
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hp, one_div_pow,
    div_le_div_iff₀ hp (by positivity)]
  linarith

theorem term_summable (ha : IsCF a) : Summable (term a) :=
  Summable.of_norm_bounded summable_geometric_two (fun j => by
    rw [Real.norm_eq_abs]; exact abs_term_le ha j)

/-- `p_n / q_n = a_0 + Σ_{j<n} (-1)^j/(q_j q_{j+1})` -/
theorem conv_eq (ha : IsCF a) : ∀ n,
    (p a n : ℝ) / q a n = (a 0 : ℝ) + ∑ j ∈ Finset.range n, term a j
  | 0 => by simp [p_zero, q_zero]
  | (n+1) => by
    rw [Finset.sum_range_succ, ← add_assoc, ← conv_eq ha n]
    have h := det a n
    have hR : (p a (n+1) : ℝ) * q a n - p a n * q a (n+1) = (-1) ^ n := by exact_mod_cast h
    have h0 := qR_pos ha n
    have h1 := qR_pos ha (n+1)
    unfold term
    field_simp
    linear_combination hR

/-- the convergents tend to `α` -/
theorem tendsto_conv (ha : IsCF a) :
    Tendsto (fun n => (p a n : ℝ) / q a n) atTop (𝓝 (alpha a)) := by
  have := ((term_summable ha).hasSum.tendsto_sum_nat).const_add (a 0 : ℝ)
  refine this.congr (fun n => ?_)
  rw [conv_eq ha n]

end Conv

/-! ## Part 3. Complete quotients (F3) and the error formula (D2) -/

/-- the tail sequence `(a_m, a_{m+1}, …)` -/
def tail (a : ℕ → ℤ) (m : ℕ) : ℕ → ℤ := fun j => a (m + j)

/-- complete quotient `α_m = [a_m; a_{m+1}, …]` -/
noncomputable def cq (a : ℕ → ℤ) (m : ℕ) : ℝ := alpha (tail a m)

/-- the error `ε_n = q_n α - p_n` -/
noncomputable def eps (a : ℕ → ℤ) (n : ℕ) : ℝ := (q a n : ℝ) * alpha a - p a n

/-- `θ_n = q_n |q_n α - p_n|` -/
noncomputable def theta (a : ℕ → ℤ) (n : ℕ) : ℝ := (q a n : ℝ) * |(q a n : ℝ) * alpha a - p a n|

theorem tail_zero (a : ℕ → ℤ) : tail a 0 = a := by funext j; simp [tail]
theorem tail_tail (a : ℕ → ℤ) (m k : ℕ) : tail (tail a m) k = tail a (m + k) := by
  funext j; simp [tail, add_assoc]
theorem cq_zero (a : ℕ → ℤ) : cq a 0 = alpha a := by rw [cq, tail_zero]

/-- concatenation: `X_{n+1+m} = X_{n+1} P'_{m} + X_n Q'_{m}` for the tail recurrence -/
theorem crec_concat (a : ℕ → ℤ) (x y : ℤ) (n : ℕ) : ∀ m,
    crec a x y (n+1+m) = crec a x y (n+1) * pp (tail a (n+1)) m
      + crec a x y n * qq (tail a (n+1)) m := by
  have key : ∀ m, (crec a x y (n+1+m) = crec a x y (n+1) * pp (tail a (n+1)) m
      + crec a x y n * qq (tail a (n+1)) m) ∧ (crec a x y (n+1+(m+1)) =
      crec a x y (n+1) * pp (tail a (n+1)) (m+1) + crec a x y n * qq (tail a (n+1)) (m+1)) := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simp [pp, qq], ?_⟩
      change crec a x y (n + 2) = crec a x y (n+1) * a (n+1+0) + crec a x y n * 1
      rw [crec_succ_succ, add_zero]; ring
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n + 1 + (m + 1 + 1) = (n + 1 + m) + 2 by ring, crec_succ_succ,
        show n + 1 + m + 1 = n + 1 + (m + 1) by ring, ih.1, ih.2]
      simp only [pp, qq, crec_succ_succ, tail]
      rw [show n + 1 + (m + 1) = n + 1 + m + 1 by ring]
      ring
  exact fun m => (key m).1

section CQ

variable {a : ℕ → ℤ}

theorem tail_isCF (ha : IsCF a) (m : ℕ) : IsCF (tail a m) := fun j hj => ha (m + j) (by omega)

theorem p_concat (a : ℕ → ℤ) (n m : ℕ) :
    p a (n+1+m) = p a n * p (tail a (n+1)) m + pp a n * q (tail a (n+1)) m := by
  have h := crec_concat a 1 (a 0) n (m+1)
  simp only [p, pp, q, qq] at h ⊢
  rw [show n + 1 + m + 1 = n + 1 + (m + 1) by ring, h]

theorem q_concat (a : ℕ → ℤ) (n m : ℕ) :
    q a (n+1+m) = q a n * p (tail a (n+1)) m + qq a n * q (tail a (n+1)) m := by
  have h := crec_concat a 0 1 n (m+1)
  simp only [p, pp, q, qq] at h ⊢
  rw [show n + 1 + m + 1 = n + 1 + (m + 1) by ring, h]

theorem crec_one_zero_nonneg (ha : IsCF a) : ∀ m, 0 ≤ crec a 1 0 m ∧ 0 ≤ crec a 1 0 (m+1)
  | 0 => by simp
  | (m+1) => by
    obtain ⟨h0, h1⟩ := crec_one_zero_nonneg ha m
    refine ⟨h1, ?_⟩
    rw [crec_succ_succ]
    have := ha (m+1) (by omega)
    nlinarith

/-- `α ≥ a_0` -/
theorem alpha_ge (ha : IsCF a) : (a 0 : ℝ) ≤ alpha a := by
  refine ge_of_tendsto' (tendsto_conv ha) (fun m => ?_)
  have hlin := crec_linear a 1 (-(a 0)) 1 (a 0) 0 1 (m+1)
  simp only [one_mul, mul_zero, add_zero, mul_one, add_neg_cancel] at hlin
  have hnn := (crec_one_zero_nonneg ha (m+1)).1
  have e : p a m - a 0 * q a m = crec a 1 0 (m+1) := by
    simp only [p, q, pp, qq]; rw [hlin]; ring
  have hq := qR_pos ha m
  rw [le_div_iff₀ hq]
  have : (0 : ℝ) ≤ (p a m : ℝ) - a 0 * q a m := by exact_mod_cast (e ▸ hnn)
  linarith

/-- `α_m ≥ a_m` -/
theorem cq_ge (ha : IsCF a) (m : ℕ) : (a m : ℝ) ≤ cq a m := by
  have h := alpha_ge (tail_isCF ha m)
  have e : ((tail a m 0 : ℤ) : ℝ) = a m := by simp [tail]
  rw [e] at h
  exact h

theorem cq_ge_one (ha : IsCF a) (m : ℕ) (hm : 1 ≤ m) : (1 : ℝ) ≤ cq a m :=
  le_trans (by exact_mod_cast ha m hm) (cq_ge ha m)

/-- F3: `α = (p_n α_{n+1} + p_{n-1}) / (q_n α_{n+1} + q_{n-1})` -/
theorem alpha_eq (ha : IsCF a) (n : ℕ) :
    alpha a = ((p a n : ℝ) * cq a (n+1) + pp a n) / ((q a n : ℝ) * cq a (n+1) + qq a n) := by
  set b := tail a (n+1) with hbdef
  have hb : IsCF b := tail_isCF ha (n+1)
  set x := alpha b with hxdef
  have hx : (1 : ℝ) ≤ x := cq_ge_one ha (n+1) (by omega)
  have hq := qR_pos ha n
  have hqq : (0 : ℝ) ≤ qq a n := by exact_mod_cast qq_nonneg ha n
  have hden : (0 : ℝ) < (q a n : ℝ) * x + qq a n := by nlinarith
  have h1 : Tendsto (fun m => (p a (n+1+m) : ℝ) / q a (n+1+m)) atTop (𝓝 (alpha a)) := by
    have := (tendsto_add_atTop_iff_nat (f := fun k => (p a k : ℝ) / q a k) (n+1)).2
      (tendsto_conv ha)
    refine this.congr (fun m => ?_)
    simp only [add_comm m (n+1)]
  have h2 : Tendsto (fun m => ((p a n : ℝ) * ((p b m : ℝ) / q b m) + pp a n) /
      ((q a n : ℝ) * ((p b m : ℝ) / q b m) + qq a n)) atTop
      (𝓝 (((p a n : ℝ) * x + pp a n) / ((q a n : ℝ) * x + qq a n))) := by
    have hc := tendsto_conv hb
    exact (((hc.const_mul _).add_const _).div ((hc.const_mul _).add_const _) hden.ne')
  have h3 : ∀ m, (p a (n+1+m) : ℝ) / q a (n+1+m) = ((p a n : ℝ) * ((p b m : ℝ) / q b m)
      + pp a n) / ((q a n : ℝ) * ((p b m : ℝ) / q b m) + qq a n) := by
    intro m
    have hpm : (p a (n+1+m) : ℝ) = p a n * p b m + pp a n * q b m := by
      exact_mod_cast p_concat a n m
    have hqm : (q a (n+1+m) : ℝ) = q a n * p b m + qq a n * q b m := by
      exact_mod_cast q_concat a n m
    have hQ := qR_pos hb m
    have hPb : (b 0 : ℝ) ≤ (p b m : ℝ) / q b m := by
      have := alpha_ge hb
      have hlin := crec_linear b 1 (-(b 0)) 1 (b 0) 0 1 (m+1)
      simp only [one_mul, mul_zero, add_zero, mul_one, add_neg_cancel] at hlin
      have hnn := (crec_one_zero_nonneg hb (m+1)).1
      have e : p b m - b 0 * q b m = crec b 1 0 (m+1) := by
        simp only [p, q, pp, qq]; rw [hlin]; ring
      rw [le_div_iff₀ hQ]
      have : (0 : ℝ) ≤ (p b m : ℝ) - b 0 * q b m := by exact_mod_cast (e ▸ hnn)
      linarith
    have hb0 : (1 : ℝ) ≤ b 0 := by
      have := ha (n+1) (by omega); simp only [hbdef, tail, add_zero]; exact_mod_cast this
    have hPpos : (0 : ℝ) < p b m := by
      have := (le_div_iff₀ hQ).1 hPb; nlinarith
    have hden2 : (0 : ℝ) < (q a n : ℝ) * p b m + qq a n * q b m := by nlinarith
    rw [hpm, hqm]
    field_simp
  rw [funext h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- `α_m = a_m + 1/α_{m+1}` -/
theorem cq_rec (ha : IsCF a) (m : ℕ) : cq a m = a m + 1 / cq a (m+1) := by
  have h := alpha_eq (tail_isCF ha m) 0
  have hx := cq_ge_one ha (m+1) (by omega)
  have e1 : cq (tail a m) 1 = cq a (m+1) := by rw [cq, cq, tail_tail]
  rw [e1] at h
  rw [cq, h, p_zero, q_zero, pp_zero, qq_zero]
  simp only [tail, add_zero, Int.cast_one, one_mul, Int.cast_zero]
  field_simp

/-- F3: `α_m > a_m` -/
theorem cq_gt (ha : IsCF a) (m : ℕ) : (a m : ℝ) < cq a m := by
  rw [cq_rec ha m]
  have := cq_ge_one ha (m+1) (by omega)
  have : (0 : ℝ) < 1 / cq a (m+1) := by positivity
  linarith

/-- `α_m < a_m + 1` -/
theorem cq_lt (ha : IsCF a) (m : ℕ) : cq a m < a m + 1 := by
  rw [cq_rec ha m]
  have h1 := cq_gt ha (m+1)
  have h2 : (1 : ℝ) ≤ a (m+1) := by exact_mod_cast ha (m+1) (by omega)
  have : 1 / cq a (m+1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  linarith

/-- D2: `ε_n = (-1)^n / (q_n α_{n+1} + q_{n-1})` -/
theorem eps_eq (ha : IsCF a) (n : ℕ) :
    eps a n = (-1 : ℝ) ^ n / ((q a n : ℝ) * cq a (n+1) + qq a n) := by
  have hx := cq_ge_one ha (n+1) (by omega)
  have hq := qR_pos ha n
  have hqq : (0 : ℝ) ≤ qq a n := by exact_mod_cast qq_nonneg ha n
  have hden : (0 : ℝ) < (q a n : ℝ) * cq a (n+1) + qq a n := by nlinarith
  have hd : ((q a n : ℝ) * pp a n - p a n * qq a n) = (-1) ^ n := by exact_mod_cast det' a n
  rw [eps, alpha_eq ha n]
  field_simp
  linear_combination hd

theorem den_pos (ha : IsCF a) (n : ℕ) : (0 : ℝ) < (q a n : ℝ) * cq a (n+1) + qq a n := by
  have hx := cq_ge_one ha (n+1) (by omega)
  have hq := qR_pos ha n
  have hqq : (0 : ℝ) ≤ qq a n := by exact_mod_cast qq_nonneg ha n
  nlinarith

theorem abs_eps_eq (ha : IsCF a) (n : ℕ) :
    |eps a n| = 1 / ((q a n : ℝ) * cq a (n+1) + qq a n) := by
  rw [eps_eq ha n, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (den_pos ha n)]

/-- D2: the sign of `ε_n` is `(-1)^n` -/
theorem eps_sign (ha : IsCF a) (n : ℕ) : eps a n = (-1 : ℝ) ^ n * |eps a n| := by
  rw [abs_eps_eq ha n, eps_eq ha n]; ring

/-- D2: `θ_n = 1 / (α_{n+1} + q_{n-1}/q_n)` -/
theorem theta_eq (ha : IsCF a) (n : ℕ) :
    theta a n = 1 / (cq a (n+1) + (qq a n : ℝ) / q a n) := by
  have hq := qR_pos ha n
  have := abs_eps_eq ha n
  rw [eps] at this
  rw [theta, this]
  field_simp

theorem theta_eq_mul (a : ℕ → ℤ) (n : ℕ) : theta a n = (q a n : ℝ) * |eps a n| := rfl

theorem theta_pos (ha : IsCF a) (n : ℕ) : 0 < theta a n := by
  rw [theta_eq_mul, abs_eps_eq ha n]
  have := qR_pos ha n; have := den_pos ha n; positivity

/-- `q_{n-1}/q_n ∈ [0, 1]` -/
theorem qq_div_q_mem (ha : IsCF a) (n : ℕ) :
    0 ≤ (qq a n : ℝ) / q a n ∧ (qq a n : ℝ) / q a n ≤ 1 := by
  have hq := qR_pos ha n
  have h0 : (0 : ℝ) ≤ qq a n := by exact_mod_cast qq_nonneg ha n
  have h1 : (qq a n : ℝ) ≤ q a n := by exact_mod_cast qq_le_q ha n
  exact ⟨div_nonneg h0 hq.le, (div_le_one hq).2 h1⟩

/-- B1 (general form): `1/θ_n ∈ (a_{n+1}, a_{n+1} + 2)` -/
theorem inv_theta_mem (ha : IsCF a) (n : ℕ) :
    (a (n+1) : ℝ) < 1 / theta a n ∧ 1 / theta a n < a (n+1) + 2 := by
  have hpos : 0 < cq a (n+1) + (qq a n : ℝ) / q a n := by
    have := cq_ge_one ha (n+1) (by omega); have := (qq_div_q_mem ha n).1; linarith
  rw [theta_eq ha n, one_div_one_div]
  have h1 := cq_gt ha (n+1)
  have h2 := cq_lt ha (n+1)
  have h3 := qq_div_q_mem ha n
  constructor <;> linarith [h3.1, h3.2]

/-- D2: `θ_n < 1/a_{n+1}` -/
theorem theta_lt (ha : IsCF a) (n : ℕ) : theta a n < 1 / (a (n+1) : ℝ) := by
  have h := (inv_theta_mem ha n).1
  have hA : (0 : ℝ) < a (n+1) := by
    have := ha (n+1) (by omega); exact_mod_cast (by omega : (0:ℤ) < a (n+1))
  have ht := theta_pos ha n
  rw [lt_div_iff₀ ht] at h
  rw [lt_div_iff₀ hA]; linarith [mul_comm (theta a n) (a (n+1) : ℝ)]

theorem theta_lt_one (ha : IsCF a) (n : ℕ) : theta a n < 1 := by
  have h := theta_lt ha n
  have hA : (1 : ℝ) ≤ a (n+1) := by exact_mod_cast ha (n+1) (by omega)
  have : 1 / (a (n+1) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hA
  linarith

/-- D2: `|ε_n| < 1/q_{n+1}` -/
theorem abs_eps_lt (ha : IsCF a) (n : ℕ) : |eps a n| < 1 / (q a (n+1) : ℝ) := by
  rw [abs_eps_eq ha n]
  have hq1 := qR_pos ha (n+1)
  have hden := den_pos ha n
  have hg := cq_gt ha (n+1)
  have hq := qR_pos ha n
  have e : (q a (n+1) : ℝ) = a (n+1) * q a n + qq a n := by exact_mod_cast q_succ a n
  rw [one_div_lt_one_div hden hq1, e]
  nlinarith

/-- (alignment) the regular continued fraction algorithm applied to `α` returns `a`:
`α_0 = α`, `⌊α_m⌋ = a_m` and `α_{m+1} = 1/(α_m - a_m)` (`m ≥ 0`). Hence `(a_n)` is the
regular CF expansion of `α`, and `p_n/q_n` are its convergents. -/
theorem cf_algorithm (ha : IsCF a) :
    cq a 0 = alpha a ∧ ∀ m, ⌊cq a m⌋ = a m ∧ cq a (m+1) = 1 / (cq a m - a m) := by
  refine ⟨cq_zero a, fun m => ⟨?_, ?_⟩⟩
  · rw [Int.floor_eq_iff]; exact ⟨(cq_gt ha m).le, cq_lt ha m⟩
  · rw [cq_rec ha m]
    have := cq_ge_one ha (m+1) (by omega)
    field_simp
    ring

end CQ

/-! ## Part 4. Block Hurwitz numbers (S.1), partial quotients by position -/

/-- Data of a block Hurwitz number `α = [a_0; a_1, …, a_N, A_1, W, A_2, W, A_3, …]`
(`N = pre.length ≥ 0`, `a_0 ∈ ℤ`, `a_1..a_N ≥ 1`, `A_k ≥ 1`, `A_k → ∞`, `W ∈ ℤ_{≥1}^ℓ`).
The sequence `A` is indexed by `k ≥ 1`; its value at `0` is never used. -/
structure BH where
  a0 : ℤ
  pre : List ℕ
  hpre : ∀ x ∈ pre, 1 ≤ x
  A : ℕ → ℕ
  hA : ∀ k, 1 ≤ k → 1 ≤ A k
  hAt : Tendsto A atTop atTop
  W : List ℕ
  hW : ∀ x ∈ W, 1 ≤ x

theorem getD_eq_getElem' {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

namespace BH

/-- `N` -/
def N (X : BH) : ℕ := X.pre.length
/-- `ℓ = |W|` -/
def ell (X : BH) : ℕ := X.W.length
/-- big index by position: `n_k = N + (k-1)(ℓ+1)` (`k ≥ 1`) -/
def nk (X : BH) (k : ℕ) : ℕ := X.N + (k - 1) * (X.ell + 1)

/-- the full sequence of partial quotients, by position -/
def a (X : BH) (n : ℕ) : ℤ :=
  if n = 0 then X.a0
  else if n ≤ X.N then (X.pre.getD (n - 1) 0 : ℤ)
  else if (n - X.N - 1) % (X.ell + 1) = 0 then (X.A ((n - X.N - 1) / (X.ell + 1) + 1) : ℤ)
  else (X.W.getD ((n - X.N - 1) % (X.ell + 1) - 1) 0 : ℤ)

variable (X : BH)

theorem a_zero : X.a 0 = X.a0 := by simp [a]

theorem a_pre (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ X.N) :
    X.a n = (X.pre[n - 1]'(by unfold N at h2; omega) : ℤ) := by
  simp only [a, show n ≠ 0 by omega, h2, ite_true, ite_false]
  rw [getD_eq_getElem']

theorem nk_succ (k : ℕ) (hk : 1 ≤ k) : X.nk (k+1) = X.nk k + X.ell + 1 := by
  unfold nk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  simp only [Nat.add_sub_cancel]
  ring

theorem nk_one : X.nk 1 = X.N := by simp [nk]

/-- `a_{n_k + 1} = A_k` -/
theorem a_big (k : ℕ) (hk : 1 ≤ k) : X.a (X.nk k + 1) = (X.A k : ℤ) := by
  have e : X.nk k + 1 - X.N - 1 = (k - 1) * (X.ell + 1) := by unfold nk; omega
  simp only [a, show X.nk k + 1 ≠ 0 by omega, show ¬ (X.nk k + 1 ≤ X.N) by unfold nk; omega,
    ite_false, e, Nat.mul_mod_left, ite_true]
  rw [Nat.mul_div_cancel _ (by omega), Nat.sub_add_cancel hk]

/-- `a_{n_k + 1 + i} = w_i` for `1 ≤ i ≤ ℓ` -/
theorem a_word (k : ℕ) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ X.ell) :
    X.a (X.nk k + 1 + i) = (X.W[i - 1]'(by unfold ell at hi2; omega) : ℤ) := by
  have e : X.nk k + 1 + i - X.N - 1 = (k - 1) * (X.ell + 1) + i := by unfold nk; omega
  have hm : ((k - 1) * (X.ell + 1) + i) % (X.ell + 1) = i := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  simp only [a, show X.nk k + 1 + i ≠ 0 by omega,
    show ¬ (X.nk k + 1 + i ≤ X.N) by unfold nk; omega, ite_false, e, hm,
    show i ≠ 0 by omega]
  rw [getD_eq_getElem']

/-- block Hurwitz partial quotients satisfy the regular CF hypothesis (F4) -/
theorem isCF : IsCF X.a := by
  intro n hn
  unfold a
  simp only [show n ≠ 0 by omega, ite_false]
  split_ifs with h1 h2
  · rw [getD_eq_getElem' (by unfold N at h1; omega)]
    exact_mod_cast X.hpre _ (List.getElem_mem _)
  · exact_mod_cast X.hA _ (Nat.le_add_left _ _)
  · have hlt := Nat.mod_lt (n - X.N - 1) (by omega : 0 < X.ell + 1)
    simp only [ell] at hlt h2 ⊢
    rw [getD_eq_getElem' (by omega)]
    exact_mod_cast X.hW _ (List.getElem_mem _)

end BH

/-! ## Part 5. Lemma A: continuants inside a block -/

/-- (A1) block propagation: if `X_{M+j+2} = w_{j+1} X_{M+j+1} + X_{M+j}` for `0 ≤ j < ℓ`, then
`X_{M+1+j} = K_{[1,j]} X_{M+1} + K_{[2,j]} X_M` for `0 ≤ j ≤ ℓ`, where
`K_{[1,j]} = cseq W (j+1) = K(w_1..w_j)` and `K_{[2,j]} = cseq W.tail j` (`= 0` for `j = 0`). -/
theorem A1 {R : Type*} [CommRing R] (W : List ℕ) (hW : ∀ x ∈ W, 1 ≤ x) (X : ℕ → R) (M : ℕ)
    (h : ∀ j (hj : j < W.length), X (M + j + 2) = (W[j] : R) * X (M + j + 1) + X (M + j)) :
    ∀ j, j ≤ W.length →
      X (M + 1 + j) = (R6S7.cseq W (j+1) : R) * X (M+1) + (R6S7.cseq W.tail j : R) * X M := by
  have hWt : ∀ x ∈ W.tail, 1 ≤ x := fun x hx => hW x (List.mem_of_mem_tail hx)
  have recW := (R6S7.link W hW).2.2.2.1
  have recT := (R6S7.link W.tail hWt).2.2.2.1
  have wW : ∀ j (hj : j < W.length), R6S7.wseq W (j+1) = W[j] := by
    intro j hj; simp [R6S7.wseq, hj]
  have key : ∀ j, j + 1 ≤ W.length →
      (X (M + 1 + j) = (R6S7.cseq W (j+1) : R) * X (M+1) + (R6S7.cseq W.tail j : R) * X M) ∧
      (X (M + 1 + (j+1)) = (R6S7.cseq W (j+2) : R) * X (M+1)
        + (R6S7.cseq W.tail (j+1) : R) * X M) := by
    intro j
    induction j with
    | zero =>
      intro hl
      have h0 := h 0 (by omega)
      have c1 : R6S7.cseq W 1 = 1 := by simp [R6S7.cseq, R6S7.contK_nil]
      have c2 : R6S7.cseq W 2 = W[0] := by
        obtain ⟨b, t, rfl⟩ : ∃ b t, W = b :: t := by
          rcases W with _ | ⟨b, t⟩
          · simp at hl
          · exact ⟨b, t, rfl⟩
        simp [R6S7.cseq, R6S7.contK_singleton]
      have t0 : R6S7.cseq W.tail 0 = 0 := by simp [R6S7.cseq]
      have t1 : R6S7.cseq W.tail 1 = 1 := by simp [R6S7.cseq, R6S7.contK_nil]
      refine ⟨by rw [c1, t0]; simp, ?_⟩
      rw [c2, t1, show M + 1 + (0 + 1) = M + 0 + 2 by ring, h0]
      simp
    | succ j ih =>
      intro hl
      obtain ⟨i1, i2⟩ := ih (by omega)
      refine ⟨i2, ?_⟩
      have hj := h (j+1) (by omega)
      have cW := recW (j+1) (by omega)
      have cT := recT j (by simp; omega)
      rw [wW (j+1) (by omega)] at cW
      have wT : R6S7.wseq W.tail (j+1) = W[j+1] := by
        simp only [R6S7.wseq, Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
          List.getElem?_tail]
        rw [List.getElem?_eq_getElem (by omega)]; rfl
      rw [wT] at cT
      rw [show M + 1 + (j + 1 + 1) = M + (j+1) + 2 by ring, hj,
        show M + (j + 1) + 1 = M + 1 + (j+1) by ring, show M + (j+1) = M + 1 + j by ring,
        i1, i2, cW, cT]
      push_cast
      ring
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · simp [R6S7.cseq, R6S7.contK_nil]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact (key i hj).2

/-- (A2a) splitting identity: for `1 ≤ i ≤ ℓ`, `K = c_i K_{[i,ℓ]} + K_{[1,i-2]} c'_i`
(`c_i = cc W (i-1)`, `c'_i = cc' W (i-1)`, `K_{[i,ℓ]} = K(W.drop (i-1))`,
`K_{[1,i-2]} = cseq W (i-1)`). -/
theorem A2a (W : List ℕ) (hW : ∀ x ∈ W, 1 ≤ x) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ W.length) :
    R6S7.contK W = R6S7.cc W (i-1) * R6S7.contK (W.drop (i-1))
      + R6S7.cseq W (i-1) * R6S7.cc' W (i-1) := by
  obtain ⟨hw, hc0, hc1, hcR, hd0, hd1, hdL, hcK, hcc, hdd⟩ := R6S7.link W hW
  have hs := R6S7.core_split W.length (R6S7.wseq W) (R6S7.cseq W) (R6S7.dseq W) hcR hd0 hd1 hdL
    (i-1) (by omega)
  rw [hcK, show i - 1 + 1 = i by omega] at hs
  have e1 : R6S7.cseq W i = R6S7.cc W (i-1) := by
    rw [← hcc (i-1), show i - 1 + 1 = i by omega]
  have e2 : R6S7.dseq W (i-1) = R6S7.contK (W.drop (i-1)) := by
    simp [R6S7.dseq, show ¬ W.length < i - 1 by omega]
  have e3 : R6S7.dseq W i = R6S7.cc' W (i-1) := by
    rw [← hdd (i-1) (by omega), show i - 1 + 1 = i by omega]
  rw [← e1, ← e2, ← e3, hs]

/-! ### D3: the symmetric relation `q_n ε_m - q_m ε_n = D(m,n)` -/

/-- `D(m,n) = q_m p_n - p_m q_n ∈ ℤ` -/
def Dm (a : ℕ → ℤ) (m n : ℕ) : ℤ := q a m * p a n - p a m * q a n

theorem D3_eq (a : ℕ → ℤ) (m n : ℕ) :
    (q a n : ℝ) * eps a m - q a m * eps a n = Dm a m n := by
  simp only [eps, Dm]; push_cast; ring

theorem Dm_self (a : ℕ → ℤ) (m : ℕ) : Dm a m m = 0 := by simp only [Dm]; ring

theorem Dm_succ (a : ℕ → ℤ) (m : ℕ) : Dm a m (m+1) = (-1) ^ m := by
  have h := det a m; simp only [Dm]; linear_combination h

/-- `n ↦ D(m,n)` satisfies the F1 recurrence -/
theorem Dm_rec (a : ℕ → ℤ) (m n : ℕ) : Dm a m (n+2) = a (n+2) * Dm a m (n+1) + Dm a m n := by
  have hq : q a (n+2) = a (n+2) * q a (n+1) + q a n := q_succ a (n+1)
  have hp : p a (n+2) = a (n+2) * p a (n+1) + p a n := p_succ a (n+1)
  simp only [Dm]; rw [hq, hp]; ring

/-! ### Non-vacuity: a concrete block Hurwitz datum (`W = (1,1)`, `A_k = k`, `N = 0`) -/

/-- `[0; A_1, 1, 1, A_2, 1, 1, …]` with `A_k = k` -/
def BH.example11 : BH where
  a0 := 0
  pre := []
  hpre := by simp
  A := id
  hA := fun k hk => hk
  hAt := tendsto_id
  W := [1, 1]
  hW := by simp

example : BH.example11.a 1 = 1 ∧ BH.example11.a 2 = 1 ∧ BH.example11.a 3 = 1 ∧
    BH.example11.a 4 = 2 ∧ BH.example11.a 7 = 3 := by decide

/-! ## Part 6. The KL functional, `c*(α)` and the statement of R6-S2 -/

/-- `‖x‖`, the distance to the nearest integer -/
noncomputable def dist0 (x : ℝ) : ℝ := |x - round x|

/-- (alignment) `‖x‖ = min_{n ∈ ℤ} |x - n|` -/
theorem dist0_isLeast (x : ℝ) : IsLeast {d | ∃ n : ℤ, d = |x - n|} (dist0 x) :=
  ⟨⟨round x, rfl⟩, by rintro d ⟨n, rfl⟩; exact round_le x n⟩

/-- the lattice `ℤα + ℤ` -/
def lattice (α : ℝ) : Set ℝ := {β | ∃ u v : ℤ, β = u * α + v}

/-- KL functional `𝒦_α(β) = limsup_n ‖q_n β‖ / θ_n ∈ [0, ∞]`, computed in `ℝ≥0∞` -/
noncomputable def KL (a : ℕ → ℤ) (β : ℝ) : ENNReal :=
  limsup (fun n => ENNReal.ofReal (dist0 ((q a n : ℝ) * β) / theta a n)) atTop

/-- KL sharp constant `c*(α) = inf_{β ∉ ℤα+ℤ} 𝒦_α(β)` -/
noncomputable def cstar (a : ℕ → ℤ) : ENNReal := ⨅ β ∈ (lattice (alpha a))ᶜ, KL a β

/-- **Statement of R6-S2** (main part): for every block Hurwitz number `α` with block word `W`,
`c*(α) = ν(W)`, and the infimum is attained by some `β ∉ ℤα + ℤ`. -/
def StatementR6S2 : Prop :=
  ∀ X : BH, cstar X.a = ENNReal.ofReal (R6S7.nu X.W) ∧
    ∃ β : ℝ, β ∉ lattice (alpha X.a) ∧ KL X.a β = ENNReal.ofReal (R6S7.nu X.W)

/-- R6-S2, last clause: `1/4 ≤ ν(W) ≤ 1` (in fact `1/2 ≤ ν(W)`, by R6-S7). -/
theorem nu_bounds (W : List ℕ) (hW : ∀ x ∈ W, 1 ≤ x) :
    (1 : ℝ) / 4 ≤ R6S7.nu W ∧ R6S7.nu W ≤ 1 := by
  refine ⟨le_trans (by norm_num) (R6S7.nu_ge_half W hW).1, ?_⟩
  have hK1 := R6S7.contK_pos W hW
  rcases Nat.lt_or_ge (R6S7.contK W) 2 with h | h
  · rw [(R6S7.cor2_K_eq_one W (by omega)).2.1]
  · rw [(R6S7.cor2_K_ge_two W hW h).2.1]; exact min_le_left _ _

/-- R6-S2, clause "only depends on `W`": a consequence of the main part. -/
theorem cstar_only_W (hS : StatementR6S2) (X Y : BH) (hXY : X.W = Y.W) :
    cstar X.a = cstar Y.a := by
  rw [(hS X).1, (hS Y).1, hXY]

/-- (alignment) `θ_n > 0` for block Hurwitz numbers, so `‖q_nβ‖/θ_n` is a genuine quotient -/
theorem BH.theta_pos (X : BH) (n : ℕ) : 0 < theta X.a n := R6S2.theta_pos X.isCF n

/-- B1 for block Hurwitz numbers: `1/θ_{n_k} ∈ (A_k, A_k + 2)` -/
theorem BH.inv_theta_nk (X : BH) (k : ℕ) (hk : 1 ≤ k) :
    (X.A k : ℝ) < 1 / theta X.a (X.nk k) ∧ 1 / theta X.a (X.nk k) < X.A k + 2 := by
  have h := inv_theta_mem X.isCF (X.nk k)
  rw [X.a_big k hk] at h
  exact_mod_cast h

end R6S2

#print axioms R6S2.det
#print axioms R6S2.det'
#print axioms R6S2.q_pos
#print axioms R6S2.q_step
#print axioms R6S2.q_two
#print axioms R6S2.q_mul_ge
#print axioms R6S2.q_tendsto
#print axioms R6S2.conv_eq
#print axioms R6S2.tendsto_conv
#print axioms R6S2.crec_concat
#print axioms R6S2.alpha_ge
#print axioms R6S2.alpha_eq
#print axioms R6S2.cq_rec
#print axioms R6S2.cq_gt
#print axioms R6S2.cq_lt
#print axioms R6S2.cf_algorithm
#print axioms R6S2.eps_eq
#print axioms R6S2.eps_sign
#print axioms R6S2.theta_eq
#print axioms R6S2.theta_pos
#print axioms R6S2.inv_theta_mem
#print axioms R6S2.theta_lt
#print axioms R6S2.theta_lt_one
#print axioms R6S2.abs_eps_lt
#print axioms R6S2.BH.a_zero
#print axioms R6S2.BH.a_pre
#print axioms R6S2.BH.nk_succ
#print axioms R6S2.BH.a_big
#print axioms R6S2.BH.a_word
#print axioms R6S2.BH.isCF
#print axioms R6S2.A1
#print axioms R6S2.A2a
#print axioms R6S2.D3_eq
#print axioms R6S2.Dm_succ
#print axioms R6S2.Dm_rec
#print axioms R6S2.dist0_isLeast
#print axioms R6S2.nu_bounds
#print axioms R6S2.cstar_only_W
#print axioms R6S2.BH.theta_pos
#print axioms R6S2.BH.inv_theta_nk
