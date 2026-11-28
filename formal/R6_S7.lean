import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.LinearCombination

/-!
# R6-S7: `m*(W) ≥ 1/2` and `ν(W) = min(1, m*(W))` (standalone, narrow Mathlib imports)

Formalizes Proposition 1 and Corollary 2 of `proofs/R6-S7-mstar.md`, with every object
(`K`, `c_i`, `c'_i`, `σ`, `d_K`, `v`, the local graph `G_W`, `ν`) defined literally after
PLAN_GRAPH.md §S.1. No proof-escape tactics (enforced by the CI siege gate), no project axioms.

Corollary 3 (the transfer `c*(α) = ν(W)`, i.e. R6-S2) is NOT formalized here.
-/

namespace R6S7

/-! ## Part 0. Definitions, literally following PLAN_GRAPH.md S.1 -/

/-- Auxiliary: the S.1 right recursion read on the *reversed* word.
`revK (b :: a :: t) = b * revK (a :: t) + revK t` is
`K(w_1..w_m) = w_m K(w_1..w_{m-1}) + K(w_1..w_{m-2})` with `w_m = b`. -/
def revK : List ℕ → ℕ
  | [] => 1
  | [a] => a
  | b :: a :: t => b * revK (a :: t) + revK t

/-- S.1 continuant `K(w_1,…,w_m)`: `K() = 1`, `K(w_1) = w_1`,
`K(w_1..w_m) = w_m K(w_1..w_{m-1}) + K(w_1..w_{m-2})`. -/
def contK (W : List ℕ) : ℕ := revK W.reverse

theorem contK_nil : contK [] = 1 := rfl
theorem contK_singleton (a : ℕ) : contK [a] = a := rfl
theorem contK_append_two (l : List ℕ) (a b : ℕ) :
    contK (l ++ [a, b]) = b * contK (l ++ [a]) + contK l := by
  simp [contK, revK]

/-- `c_i = K(w_1..w_{i-1})` for `1 ≤ i ≤ ℓ`; here indexed by `i - 1`. -/
def cc (W : List ℕ) (i : ℕ) : ℕ := contK (W.take i)
/-- `c'_i = K(w_{i+1}..w_ℓ)` for `1 ≤ i ≤ ℓ`; here indexed by `i - 1`. -/
def cc' (W : List ℕ) (i : ℕ) : ℕ := contK (W.drop (i + 1))

/-- `σ := c_ℓ = K(w_1..w_{ℓ-1})` if `ℓ ≥ 1`, and `σ := 1` if `ℓ = 0`. -/
def sigma (W : List ℕ) : ℕ := if W.length = 0 then 1 else contK W.dropLast

/-- `d_K(x)`, computed from the residue; `dK_isLeast` shows it is `min_s |x - sK|`. -/
def dK (K : ℕ) (x : ℤ) : ℕ := min ((x : ZMod K).val) (K - (x : ZMod K).val)

/-- The `i`-th term (0-indexed, `i = i₁ - 1`) `d_K(c_{i₁} r) / (c_{i₁} c'_{i₁})`. -/
def vterm (W : List ℕ) (r : ZMod (contK W)) (i : ℕ) : ℚ :=
  (dK (contK W) ((cc W i : ℤ) * (r.val : ℤ)) : ℚ) / ((cc W i : ℚ) * (cc' W i : ℚ))

/-- Vertex cost `v(r) = max_{1 ≤ i ≤ ℓ} d_K(c_i r)/(c_i c'_i)`, and `v ≡ 0` if `ℓ = 0`.
(`foldr max 0`; `vcost_isGreatest` shows it is the max for `ℓ ≥ 1`.) -/
def vcost (W : List ℕ) (r : ZMod (contK W)) : ℚ :=
  ((List.range W.length).map (vterm W r)).foldr max 0


theorem le_foldr_max : ∀ (L : List ℚ) (x : ℚ), x ∈ L → x ≤ L.foldr max 0
  | [], _, h => absurd h List.not_mem_nil
  | y :: L, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (le_foldr_max L x h).trans (le_max_right _ _)

/-! ## Part 1. Alignment lemmas for the definitions -/

theorem dK_isLeast (K : ℕ) (hK : 1 ≤ K) (x : ℤ) :
    IsLeast {n : ℤ | ∃ s : ℤ, n = |x - s * K|} (dK K x : ℤ) := by
  have : NeZero K := ⟨by omega⟩
  have hv := ZMod.val_intCast (n := K) x
  have hlt := ZMod.val_lt (x : ZMod K)
  set a := (x : ZMod K).val with ha
  have hdiv := Int.emod_def x K
  have hK' : (0 : ℤ) < K := by exact_mod_cast hK
  have hx : x = a + (x / K) * K := by linarith
  have hsub : ((K - a : ℕ) : ℤ) = K - a := by push_cast [Nat.cast_sub hlt.le]; ring
  have hltZ : (a : ℤ) < K := by exact_mod_cast hlt
  have ha0 : (0 : ℤ) ≤ a := by positivity
  constructor
  · unfold dK
    rw [← ha]
    rcases le_total a (K - a) with h | h
    · refine ⟨x / K, ?_⟩
      rw [min_eq_left h, abs_of_nonneg (by linarith)]
      linarith
    · refine ⟨x / K + 1, ?_⟩
      rw [min_eq_right h, hsub, abs_of_nonpos (by linarith)]
      linarith
  · rintro n ⟨s, rfl⟩
    unfold dK
    rw [← ha]
    rcases lt_trichotomy s (x / K) with h | h | h
    · have h1 : s + 1 ≤ x / K := h
      have : (K : ℤ) ≤ x - s * K := by nlinarith
      calc ((min a (K - a) : ℕ) : ℤ) ≤ (a : ℤ) := by exact_mod_cast min_le_left _ _
        _ ≤ |x - s * K| := by rw [abs_of_nonneg (by linarith)]; linarith
    · subst h
      calc ((min a (K - a) : ℕ) : ℤ) ≤ (a : ℤ) := by exact_mod_cast min_le_left _ _
        _ ≤ |x - x / K * K| := le_of_eq (by rw [abs_of_nonneg] <;> linarith)
    · have h1 : x / K + 1 ≤ s := h
      have : x - s * K ≤ a - K := by nlinarith
      calc ((min a (K - a) : ℕ) : ℤ) ≤ ((K - a : ℕ) : ℤ) := by exact_mod_cast min_le_right _ _
        _ = K - a := hsub
        _ ≤ |x - s * K| := by rw [abs_of_neg (by linarith)]; linarith

/-! ## Part 2. Abstract core (steps 0–6 of proofs/R6-S7-mstar.md)

Indices follow the proof: `c j = c_j`, `d j = c'_j` for `0 ≤ j ≤ ℓ+1`, with
`c_0 = 0, c_1 = 1, c'_{ℓ+1} = 0, c'_ℓ = 1`, (R) and (L). -/

/-- residue form of `d_K` -/
def dZ (K : ℕ) (y : ZMod K) : ℕ := min y.val (K - y.val)

theorem dK_eq_dZ (K : ℕ) (x : ℤ) : dK K x = dZ K (x : ZMod K) := rfl

theorem dZ_neg (K : ℕ) [NeZero K] (y : ZMod K) : dZ K (-y) = dZ K y := by
  unfold dZ
  rw [ZMod.neg_val]
  split_ifs with h
  · subst h; simp
  · have := ZMod.val_lt y
    rw [Nat.sub_sub_self this.le, min_comm]

theorem dZ_natCast_small (K : ℕ) (n : ℕ) (h : 2 * n ≤ K) (hK : 1 ≤ K) :
    dZ K (n : ZMod K) = n := by
  unfold dZ
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  omega

section Core

variable (ℓ : ℕ) (w c d : ℕ → ℕ)

theorem core_c_pos (hw : ∀ j, j < ℓ → 1 ≤ w (j + 1)) (hc1 : c 1 = 1)
    (hcR : ∀ j, j < ℓ → c (j + 2) = w (j + 1) * c (j + 1) + c j) :
    ∀ k, k ≤ ℓ → 1 ≤ c (k + 1) := by
  intro k
  induction k with
  | zero => intro _; simp [hc1]
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    rw [hcR k (by omega)]
    have := hw k (by omega)
    nlinarith

theorem core_d_pos (hw : ∀ j, j < ℓ → 1 ≤ w (j + 1)) (hd1 : d ℓ = 1)
    (hdL : ∀ j, j < ℓ → d j = w (j + 1) * d (j + 1) + d (j + 2)) :
    ∀ j, j ≤ ℓ → 1 ≤ d j := by
  have key : ∀ k, k ≤ ℓ → 1 ≤ d (ℓ - k) := by
    intro k
    induction k with
    | zero => intro _; simp [hd1]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have e := hdL (ℓ - (k + 1)) (by omega)
      rw [show ℓ - (k + 1) + 1 = ℓ - k by omega] at e
      rw [e]
      have := hw (ℓ - (k + 1)) (by omega)
      rw [show ℓ - (k + 1) + 1 = ℓ - k by omega] at this
      nlinarith
  intro j hj
  have := key (ℓ - j) (by omega)
  rwa [show ℓ - (ℓ - j) = j by omega] at this

/-- Step 2 (splitting identity) `c_{j+1} c'_j + c_j c'_{j+1} = K` for `0 ≤ j ≤ ℓ`. -/
theorem core_split (hcR : ∀ j, j < ℓ → c (j + 2) = w (j + 1) * c (j + 1) + c j)
    (hd0 : d (ℓ + 1) = 0) (hd1 : d ℓ = 1)
    (hdL : ∀ j, j < ℓ → d j = w (j + 1) * d (j + 1) + d (j + 2)) :
    ∀ j, j ≤ ℓ → c (j + 1) * d j + c j * d (j + 1) = c (ℓ + 1) := by
  have step : ∀ j, j ≤ ℓ → c (j + 1) * d j + c j * d (j + 1) = c 1 * d 0 + c 0 * d 1 := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [← ih (by omega), hcR j (by omega), hdL j (by omega)]
      ring
  intro j hj
  rw [step j hj, ← step ℓ le_rfl, hd0, hd1]
  ring

/-- Step 3: `gcd(c'_1, K) = 1`. -/
theorem core_coprime (hd0 : d (ℓ + 1) = 0) (hd1 : d ℓ = 1)
    (hdL : ∀ j, j < ℓ → d j = w (j + 1) * d (j + 1) + d (j + 2)) :
    Nat.gcd (d 0) (d 1) = 1 := by
  have key : ∀ k, k ≤ ℓ → Nat.gcd (d (ℓ - k)) (d (ℓ - k + 1)) = 1 := by
    intro k
    induction k with
    | zero => intro _; simp [hd0, hd1]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have e := hdL (ℓ - (k + 1)) (by omega)
      rw [show ℓ - (k + 1) + 1 = ℓ - k by omega,
        show ℓ - (k + 1) + 2 = ℓ - k + 1 by omega] at e
      rw [show ℓ - (k + 1) + 1 = ℓ - k by omega, e, mul_comm (w (ℓ - k)),
        Nat.gcd_mul_left_add_left, Nat.gcd_comm]
      exact h1
  have := key ℓ le_rfl
  simpa using this

/-- Step 4 (congruence duality), multiplied through by `c'_1`:
`c'_1 c_j ≡ (-1)^(j+1) c'_j (mod K)` for `0 ≤ j ≤ ℓ+1`. -/
theorem core_dual (hc0 : c 0 = 0) (hc1 : c 1 = 1)
    (hcR : ∀ j, j < ℓ → c (j + 2) = w (j + 1) * c (j + 1) + c j)
    (hdL : ∀ j, j < ℓ → d j = w (j + 1) * d (j + 1) + d (j + 2))
    (hdK : d 0 = c (ℓ + 1)) :
    ∀ j, j ≤ ℓ + 1 →
      ((d 1 : ZMod (c (ℓ + 1))) * c j = (-1) ^ (j + 1) * (d j : ZMod (c (ℓ + 1)))) := by
  have two : ∀ j, j ≤ ℓ →
      ((d 1 : ZMod (c (ℓ + 1))) * c j = (-1) ^ (j + 1) * (d j : ZMod (c (ℓ + 1)))) ∧
      ((d 1 : ZMod (c (ℓ + 1))) * c (j + 1) =
        (-1) ^ (j + 2) * (d (j + 1) : ZMod (c (ℓ + 1)))) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [hc0, hdK]; simp
      · rw [hc1]; simp
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      refine ⟨h2, ?_⟩
      have eR : ((c (j + 2) : ℕ) : ZMod (c (ℓ + 1))) =
          (w (j + 1) : ZMod (c (ℓ + 1))) * c (j + 1) + c j := by
        rw [hcR j (by omega)]; push_cast; ring
      have eL : ((d j : ℕ) : ZMod (c (ℓ + 1))) =
          (w (j + 1) : ZMod (c (ℓ + 1))) * d (j + 1) + d (j + 2) := by
        rw [hdL j (by omega)]; push_cast; ring
      rw [eR]
      linear_combination (w (j + 1) : ZMod (c (ℓ + 1))) * h2 + h1 + (-1) ^ (j + 1) * eL
  intro j hj
  rcases Nat.lt_or_ge j (ℓ + 1) with h | h
  · exact (two j (by omega)).1
  · obtain rfl : j = ℓ + 1 := by omega
    exact (two ℓ le_rfl).2

/-- Steps 5–6: selection of the index. -/
theorem core_select (hw : ∀ j, j < ℓ → 1 ≤ w (j + 1))
    (hcR : ∀ j, j < ℓ → c (j + 2) = w (j + 1) * c (j + 1) + c j)
    (hd0 : d (ℓ + 1) = 0) (hd1 : d ℓ = 1)
    (hdL : ∀ j, j < ℓ → d j = w (j + 1) * d (j + 1) + d (j + 2))
    (m : ℕ) (hm : 2 * m ≤ c (ℓ + 1)) :
    ∀ j, 1 ≤ j → j ≤ ℓ → c j ≤ 2 * m →
      ∃ j', 1 ≤ j' ∧ j' ≤ ℓ ∧ c j' ≤ 2 * m ∧ 2 * (m * d j') ≤ c (ℓ + 1) := by
  have dpos := core_d_pos ℓ w d hw hd1 hdL
  have split := core_split ℓ w c d hcR hd0 hd1 hdL
  have key : ∀ n, ∀ j, ℓ - j = n → 1 ≤ j → j ≤ ℓ → c j ≤ 2 * m →
      ∃ j', 1 ≤ j' ∧ j' ≤ ℓ ∧ c j' ≤ 2 * m ∧ 2 * (m * d j') ≤ c (ℓ + 1) := by
    intro n
    induction n with
    | zero =>
      intro j hn h1 h2 h3
      exact ⟨j, h1, h2, h3, by rw [show j = ℓ by omega, hd1]; omega⟩
    | succ n ih =>
      intro j hn h1 h2 h3
      by_cases hc : c (j + 1) ≤ 2 * m
      · exact ih (j + 1) (by omega) (by omega) (by omega) hc
      · refine ⟨j, h1, h2, h3, ?_⟩
        have hs := split j h2
        have hdj := dpos j h2
        push Not at hc
        have : 2 * m * d j < c (j + 1) * d j := Nat.mul_lt_mul_of_pos_right hc hdj
        nlinarith
  intro j h1 h2 h3
  exact key (ℓ - j) j rfl h1 h2 h3

/-- Proposition 1, abstract form. -/
theorem core_main (hℓ : 1 ≤ ℓ) (hw : ∀ j, j < ℓ → 1 ≤ w (j + 1))
    (hc0 : c 0 = 0) (hc1 : c 1 = 1)
    (hcR : ∀ j, j < ℓ → c (j + 2) = w (j + 1) * c (j + 1) + c j)
    (hd0 : d (ℓ + 1) = 0) (hd1 : d ℓ = 1)
    (hdL : ∀ j, j < ℓ → d j = w (j + 1) * d (j + 1) + d (j + 2))
    (K : ℕ) (hK : c (ℓ + 1) = K) (hK2 : 2 ≤ K) (r : ZMod K) (hr : r ≠ 0) :
    ∃ j, 1 ≤ j ∧ j ≤ ℓ ∧
      (1 : ℚ) / 2 ≤ (dK K ((c j : ℤ) * (r.val : ℤ)) : ℚ) / ((c j : ℚ) * (d j : ℚ)) := by
  subst hK
  have : NeZero (c (ℓ + 1)) := ⟨by omega⟩
  have split := core_split ℓ w c d hcR hd0 hd1 hdL
  have hdK : d 0 = (c (ℓ + 1)) := by
    have := split 0 (Nat.zero_le _)
    rw [hc1, hc0] at this; simpa using this
  have hcop : Nat.Coprime (d 1) (c (ℓ + 1)) := by
    have := core_coprime ℓ w d hd0 hd1 hdL
    rw [hdK] at this
    exact Nat.Coprime.symm this
  have dual := core_dual ℓ w c d hc0 hc1 hcR hdL hdK
  have cpos := core_c_pos ℓ w c hw hc1 hcR
  have dpos := core_d_pos ℓ w d hw hd1 hdL
  -- u = λ r with λ = (c'_1)⁻¹
  set p : (ZMod (c (ℓ + 1)))ˣ := ZMod.unitOfCoprime (d 1) hcop with hp
  have hpv : ((p : ZMod (c (ℓ + 1)))) = (d 1 : ZMod (c (ℓ + 1))) := ZMod.coe_unitOfCoprime _ _
  set u : ZMod (c (ℓ + 1)) := r * ((p⁻¹ : (ZMod (c (ℓ + 1)))ˣ) : ZMod (c (ℓ + 1))) with hu
  have hru : (d 1 : ZMod (c (ℓ + 1))) * u = r := by
    rw [hu, ← hpv, mul_comm r, ← mul_assoc, Units.mul_inv, one_mul]
  have hu0 : u ≠ 0 := by
    intro h; apply hr; rw [← hru, h, mul_zero]
  -- m = |u| with 1 ≤ m ≤ (c (ℓ + 1))/2
  set m := dZ (c (ℓ + 1)) u with hmdef
  have hult := ZMod.val_lt u
  have hupos : u.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  have hm1 : 1 ≤ m := by
    simp only [hmdef, dZ]; omega
  have hm2 : 2 * m ≤ (c (ℓ + 1)) := by
    simp only [hmdef, dZ]; omega
  have hmu : (m : ZMod (c (ℓ + 1))) = u ∨ (m : ZMod (c (ℓ + 1))) = -u := by
    simp only [hmdef, dZ]
    rcases le_total u.val ((c (ℓ + 1)) - u.val) with h | h
    · left; rw [min_eq_left h, ZMod.natCast_zmod_val]
    · right
      rw [min_eq_right h, Nat.cast_sub hult.le, ZMod.natCast_self, ZMod.natCast_zmod_val]
      ring
  obtain ⟨j, hj1, hj2, hcj, hmd⟩ :=
    core_select ℓ w c d hw hcR hd0 hd1 hdL m hm2 1 le_rfl hℓ (by rw [hc1]; omega)
  refine ⟨j, hj1, hj2, ?_⟩
  -- the residue of c_j r is ± (m c'_j)
  have hres : (((c j : ℤ) * (r.val : ℤ) : ℤ) : ZMod (c (ℓ + 1))) =
        ((m * d j : ℕ) : ZMod (c (ℓ + 1))) ∨
      (((c j : ℤ) * (r.val : ℤ) : ℤ) : ZMod (c (ℓ + 1))) =
        -((m * d j : ℕ) : ZMod (c (ℓ + 1))) := by
    have e1 : (((c j : ℤ) * (r.val : ℤ) : ℤ) : ZMod (c (ℓ + 1))) =
        (c j : ZMod (c (ℓ + 1))) * r := by
      push_cast; rw [ZMod.natCast_zmod_val]
    have e2 : (c j : ZMod (c (ℓ + 1))) * r = (-1) ^ (j + 1) * (d j : ZMod (c (ℓ + 1))) * u := by
      rw [← hru, ← mul_assoc, mul_comm (c j : ZMod (c (ℓ + 1))), dual j (by omega)]
    rw [e1, e2]
    push_cast
    rcases neg_one_pow_eq_or (ZMod (c (ℓ + 1))) (j + 1) with hs | hs <;> rw [hs] <;>
      rcases hmu with hm | hm <;> rw [hm]
    · left; ring
    · right; ring
    · right; ring
    · left; ring
  have hdval : dK (c (ℓ + 1)) ((c j : ℤ) * (r.val : ℤ)) = m * d j := by
    rw [dK_eq_dZ]
    rcases hres with h | h
    · rw [h, dZ_natCast_small (c (ℓ + 1)) _ hmd (by omega)]
    · rw [h, dZ_neg, dZ_natCast_small (c (ℓ + 1)) _ hmd (by omega)]
  rw [hdval]
  have hcj1 : 1 ≤ c j := by
    have := cpos (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this
  have hdj1 : 1 ≤ d j := dpos j hj2
  have hpos : (0 : ℚ) < (c j : ℚ) * (d j : ℚ) := by positivity
  rw [le_div_iff₀ hpos]
  have hcjq : (c j : ℚ) ≤ 2 * (m : ℚ) := by exact_mod_cast hcj
  have hdjq : (0 : ℚ) ≤ (d j : ℚ) := by positivity
  push_cast
  nlinarith

end Core

/-! ## Part 3. Continuant facts on lists and Proposition 1 -/

/-- left-recursive continuant (auxiliary; shown equal to `contK`) -/
def Kl : List ℕ → ℕ
  | [] => 1
  | [a] => a
  | a :: b :: s => a * Kl (b :: s) + Kl s

theorem Kl_append_two : ∀ (l : List ℕ) (a b : ℕ), Kl (l ++ [a, b]) = b * Kl (l ++ [a]) + Kl l
  | [], a, b => by simp [Kl]; ring
  | [x], a, b => by simp [Kl]; ring
  | x :: y :: s, a, b => by
    have h1 := Kl_append_two (y :: s) a b
    have h2 := Kl_append_two s a b
    simp only [List.cons_append] at h1 ⊢
    rw [Kl, Kl, h1, h2, Kl]
    ring

theorem revK_eq : ∀ L : List ℕ, revK L = Kl L.reverse
  | [] => rfl
  | [_] => rfl
  | b :: a :: t => by
    rw [revK, revK_eq (a :: t), revK_eq t]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [Kl_append_two]

theorem contK_eq_Kl (W : List ℕ) : contK W = Kl W := by
  rw [contK, revK_eq, List.reverse_reverse]

/-- (LL) left recursion. -/
theorem contK_cons_cons (a b : ℕ) (s : List ℕ) :
    contK (a :: b :: s) = a * contK (b :: s) + contK s := by
  simp only [contK_eq_Kl, Kl]

theorem take_succ_eq {W : List ℕ} {n : ℕ} (h : n < W.length) :
    W.take (n + 1) = W.take n ++ [W[n]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl

/-- the extended sequences `c_j`, `c'_j` (`0 ≤ j ≤ ℓ+1`) and the letters `w_j` of the proof -/
def cseq (W : List ℕ) (j : ℕ) : ℕ := if j = 0 then 0 else contK (W.take (j - 1))
def dseq (W : List ℕ) (j : ℕ) : ℕ := if W.length < j then 0 else contK (W.drop j)
def wseq (W : List ℕ) (j : ℕ) : ℕ := W.getD (j - 1) 0

theorem link (W : List ℕ) (hW : ∀ a ∈ W, 1 ≤ a) :
    (∀ j, j < W.length → 1 ≤ wseq W (j + 1)) ∧ cseq W 0 = 0 ∧ cseq W 1 = 1 ∧
    (∀ j, j < W.length → cseq W (j + 2) = wseq W (j + 1) * cseq W (j + 1) + cseq W j) ∧
    dseq W (W.length + 1) = 0 ∧ dseq W W.length = 1 ∧
    (∀ j, j < W.length → dseq W j = wseq W (j + 1) * dseq W (j + 1) + dseq W (j + 2)) ∧
    cseq W (W.length + 1) = contK W ∧
    (∀ i, cseq W (i + 1) = cc W i) ∧ (∀ i, i < W.length → dseq W (i + 1) = cc' W i) := by
  have hwj : ∀ j, (hj : j < W.length) → wseq W (j + 1) = W[j] := by
    intro j hj; simp [wseq, hj]
  refine ⟨?_, by simp [cseq], by simp [cseq, contK_nil], ?_, by simp [dseq], ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [hwj j hj]; exact hW _ (List.getElem_mem hj)
  · intro j hj
    rw [hwj j hj]
    rcases j with _ | i
    · simp only [cseq]; simp [take_succ_eq hj, List.take_zero, contK_singleton, contK_nil]
    · simp only [cseq, Nat.add_eq_zero_iff, one_ne_zero, OfNat.ofNat_ne_zero, and_false,
        ↓reduceIte,
        show i + 1 + 2 - 1 = i + 2 by omega, show i + 1 + 1 - 1 = i + 1 by omega,
        show i + 1 - 1 = i by omega]
      rw [take_succ_eq (by omega : i + 1 < W.length), take_succ_eq (by omega : i < W.length),
        List.append_assoc, List.singleton_append, contK_append_two]
  · simp [dseq, contK_nil]
  · intro j hj
    rw [hwj j hj]
    simp only [dseq, show ¬ W.length < j by omega, show ¬ W.length < j + 1 by omega, ↓reduceIte]
    rw [List.drop_eq_getElem_cons hj]
    by_cases hl : j + 1 = W.length
    · have : W.drop (j + 1) = [] := by simp [hl]
      simp only [show W.length < j + 2 by omega, ↓reduceIte, this, contK_singleton, contK_nil]
      ring
    · simp only [show ¬ W.length < j + 2 by omega, ↓reduceIte]
      rw [List.drop_eq_getElem_cons (by omega : j + 1 < W.length),
        contK_cons_cons]
  · simp [cseq]
  · intro i; simp [cseq, cc]
  · intro i hi; simp [dseq, cc', show ¬ W.length < i + 1 by omega]

/-- **Proposition 1.** For every block word `W` (list of positive integers) with
`K(W) ≥ 2` and every nonzero `r ∈ ℤ/K`, `v(r) ≥ 1/2`. -/
theorem prop1 (W : List ℕ) (hW : ∀ a ∈ W, 1 ≤ a) (hK : 2 ≤ contK W)
    (r : ZMod (contK W)) (hr : r ≠ 0) :
    (1 : ℚ) / 2 ≤ vcost W r := by
  obtain ⟨hw, hc0, hc1, hcR, hd0, hd1, hdL, hcK, hcc, hdd⟩ := link W hW
  have hℓ : 1 ≤ W.length := by
    rcases W with _ | ⟨a, W⟩
    · simp [contK_nil] at hK
    · simp
  obtain ⟨j, hj1, hj2, hj⟩ := core_main W.length (wseq W) (cseq W) (dseq W) hℓ hw hc0 hc1 hcR
    hd0 hd1 hdL (contK W) hcK hK r hr
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [hcc i, hdd i (by omega)] at hj
  refine hj.trans ?_
  apply le_foldr_max
  exact List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩

/-! ## Part 4. Alignment lemmas: `vcost` is the max over `1 ≤ i ≤ ℓ`; `dK` is residue-invariant -/

theorem foldr_max_mem : ∀ (L : List ℚ), L ≠ [] → (∀ x ∈ L, 0 ≤ x) → L.foldr max 0 ∈ L
  | [], h, _ => absurd rfl h
  | [y], _, h => by
    simp only [List.foldr, List.mem_singleton]
    exact max_eq_left (h y (by simp))
  | y :: z :: L, _, h => by
    have ih := foldr_max_mem (z :: L) (by simp) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.foldr_cons]
    rcases le_total y ((z :: L).foldr max 0) with hle | hle
    · rw [max_eq_right hle]; exact List.mem_cons_of_mem _ ih
    · rw [max_eq_left hle]; exact List.mem_cons_self

theorem vterm_nonneg (W : List ℕ) (r : ZMod (contK W)) (i : ℕ) : 0 ≤ vterm W r i := by
  unfold vterm; positivity

/-- For `ℓ ≥ 1`, `vcost W r` is the greatest of the `ℓ` terms `d_K(c_i r)/(c_i c'_i)`. -/
theorem vcost_isGreatest (W : List ℕ) (hℓ : 1 ≤ W.length) (r : ZMod (contK W)) :
    IsGreatest {x : ℚ | ∃ i, i < W.length ∧ x = vterm W r i} (vcost W r) := by
  constructor
  · have hne : (List.range W.length).map (vterm W r) ≠ [] := by
      simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega
    have hmem := foldr_max_mem _ hne (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact vterm_nonneg W r i)
    obtain ⟨i, hi, he⟩ := List.mem_map.1 hmem
    exact ⟨i, List.mem_range.1 hi, he.symm⟩
  · rintro x ⟨i, hi, rfl⟩
    exact le_foldr_max _ _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)

theorem vcost_of_length_zero (W : List ℕ) (h : W.length = 0) (r : ZMod (contK W)) :
    vcost W r = 0 := by
  simp [vcost, h]

/-- `d_K(x)` depends only on `x mod K`, so `d_K(c_i r)` does not depend on the lift of `r`. -/
theorem dK_congr (K : ℕ) (x y : ℤ) (h : (x : ZMod K) = (y : ZMod K)) : dK K x = dK K y := by
  simp only [dK, h]

theorem vterm_lift (W : List ℕ) (hK : 1 ≤ contK W) (r : ZMod (contK W)) (x : ℤ)
    (hx : (x : ZMod (contK W)) = r) (i : ℕ) : vterm W r i =
      (dK (contK W) ((cc W i : ℤ) * x) : ℚ) / ((cc W i : ℚ) * (cc' W i : ℚ)) := by
  have : NeZero (contK W) := ⟨by omega⟩
  unfold vterm
  rw [dK_congr (contK W) ((cc W i : ℤ) * (r.val : ℤ)) ((cc W i : ℤ) * x)
    (by push_cast; rw [hx, ZMod.natCast_val, ZMod.cast_id', id])]

theorem vcost_zero (W : List ℕ) : vcost W 0 = 0 := by
  have h : ∀ i, vterm W 0 i = 0 := by
    intro i; simp [vterm, dK]
  have : ∀ n, ((List.range n).map (vterm W 0)).foldr max 0 = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.map_append, List.foldr_append]; simp [h, ih]
  exact this _

/-- positivity of `K(W)` for positive words -/
theorem contK_pos (W : List ℕ) (hW : ∀ a ∈ W, 1 ≤ a) : 1 ≤ contK W := by
  obtain ⟨hw, -, hc1, hcR, -, -, -, hcK, -, -⟩ := link W hW
  rw [← hcK]
  exact core_c_pos W.length (wseq W) (cseq W) hw hc1 hcR W.length le_rfl

/-! ## Part 5. The local graph `G_W` and `ν(W)` (Corollary 2) -/

/-- A directed closed walk `r^0 → r^1 → ⋯ → r^{L-1} → r^0` in `G_W` (`L ≥ 1`); edge `i` goes
from `vert i` to `vert (i+1 mod L)` and carries a real `t i ≡ (r' - σ r)/K (mod 1)`. -/
structure ClosedWalk (W : List ℕ) where
  L : ℕ
  hL : 0 < L
  vert : Fin L → ZMod (contK W)
  t : Fin L → ℝ
  edge : ∀ i, ∃ n : ℤ, t i =
    (((vert (finRotate L i)).val : ℝ) - (sigma W : ℝ) * ((vert i).val : ℝ)) / (contK W : ℝ) + n

/-- all edges are trivial loops (self-loops at `0` with `t = 0`) -/
def ClosedWalk.allTrivial {W : List ℕ} (C : ClosedWalk W) : Prop := ∀ i, C.vert i = 0 ∧ C.t i = 0

/-- cost = max of the vertex costs and edge costs along the walk -/
noncomputable def ClosedWalk.cost {W : List ℕ} (C : ClosedWalk W) : ℝ :=
  Finset.univ.sup' ⟨⟨0, C.hL⟩, Finset.mem_univ _⟩
    (fun i => max ((vcost W (C.vert i) : ℚ) : ℝ) |C.t i|)

/-- costs of nontrivial closed walks (reading "闭途径") -/
def costSet (W : List ℕ) : Set ℝ := {x | ∃ C : ClosedWalk W, ¬ C.allTrivial ∧ C.cost = x}
/-- costs of nontrivial simple cycles (reading "简单圈": pairwise distinct vertices) -/
def costSetSimple (W : List ℕ) : Set ℝ :=
  {x | ∃ C : ClosedWalk W, Function.Injective C.vert ∧ ¬ C.allTrivial ∧ C.cost = x}

/-- `ν(W)` (closed-walk reading) and its simple-cycle variant -/
noncomputable def nu (W : List ℕ) : ℝ := sInf (costSet W)
noncomputable def nuSimple (W : List ℕ) : ℝ := sInf (costSetSimple W)

/-- `m* = min_{r ≠ 0} v(r)` -/
noncomputable def mstar (W : List ℕ) : ℝ :=
  sInf {x : ℝ | ∃ r : ZMod (contK W), r ≠ 0 ∧ x = ((vcost W r : ℚ) : ℝ)}

theorem mstar_isLeast (W : List ℕ) (hK : 2 ≤ contK W) :
    IsLeast {x : ℝ | ∃ r : ZMod (contK W), r ≠ 0 ∧ x = ((vcost W r : ℚ) : ℝ)} (mstar W) := by
  have : NeZero (contK W) := ⟨by omega⟩
  set S := {x : ℝ | ∃ r : ZMod (contK W), r ≠ 0 ∧ x = ((vcost W r : ℚ) : ℝ)}
  have hne : S.Nonempty := by
    refine ⟨_, 1, ?_, rfl⟩
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_one'' (by omega), ZMod.val_zero] at this
    exact one_ne_zero this
  have hfin : S.Finite := by
    have : S ⊆ Set.range (fun r : ZMod (contK W) => ((vcost W r : ℚ) : ℝ)) := by
      rintro x ⟨r, -, rfl⟩; exact ⟨r, rfl⟩
    exact (Set.finite_range _).subset this
  exact ⟨hne.csInf_mem hfin, fun x hx => csInf_le hfin.bddBelow hx⟩

theorem mstar_ge_half (W : List ℕ) (hW : ∀ a ∈ W, 1 ≤ a) (hK : 2 ≤ contK W) :
    (1 : ℝ) / 2 ≤ mstar W := by
  obtain ⟨⟨r, hr, he⟩, -⟩ := mstar_isLeast W hK
  rw [he]
  have := prop1 W hW hK r hr
  calc (1 : ℝ) / 2 = (((1 : ℚ) / 2 : ℚ) : ℝ) := by norm_num
    _ ≤ _ := by exact_mod_cast this

/-- the cost of a one-vertex walk -/
theorem cost_one {W : List ℕ} (C : ClosedWalk W) (h1 : C.L = 1) (i : Fin C.L) :
    C.cost = max ((vcost W (C.vert i) : ℚ) : ℝ) |C.t i| := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun k _ => ?_)
    have : k = i := by ext; have := k.2; have := i.2; omega
    rw [this]
  · exact Finset.le_sup' (fun k => max ((vcost W (C.vert k) : ℚ) : ℝ) |C.t k|) (Finset.mem_univ i)

/-- self-loop at `r` with prescribed admissible `t` -/
def loopAt (W : List ℕ) (r : ZMod (contK W)) (t : ℝ)
    (ht : ∃ n : ℤ, t = ((r.val : ℝ) - (sigma W : ℝ) * (r.val : ℝ)) / (contK W : ℝ) + n) :
    ClosedWalk W where
  L := 1
  hL := Nat.one_pos
  vert := fun _ => r
  t := fun _ => t
  edge := fun _ => ht

theorem loopAt_injective (W : List ℕ) (r : ZMod (contK W)) (t : ℝ) (ht) :
    Function.Injective (loopAt W r t ht).vert := by
  intro a b _; ext; have := a.2; have := b.2; simp only [loopAt] at *; omega

theorem loopAt_cost (W : List ℕ) (r : ZMod (contK W)) (t : ℝ) (ht) :
    (loopAt W r t ht).cost = max ((vcost W r : ℚ) : ℝ) |t| :=
  cost_one _ rfl ⟨0, Nat.one_pos⟩

/-- the loop at `0` with `t = 1` -/
def loopZero (W : List ℕ) : ClosedWalk W :=
  loopAt W 0 1 ⟨1, by simp⟩

theorem loopZero_nontrivial (W : List ℕ) : ¬ (loopZero W).allTrivial := by
  intro h
  have := (h ⟨0, Nat.one_pos⟩).2
  simp [loopZero, loopAt] at this

theorem loopZero_cost (W : List ℕ) : (loopZero W).cost = 1 := by
  rw [loopZero, loopAt_cost, vcost_zero]; simp

/-- lower bound: every nontrivial closed walk has cost `≥ 1` or `≥ v(r)` for some visited `r ≠ 0` -/
theorem cost_lower {W : List ℕ} (C : ClosedWalk W) (hC : ¬ C.allTrivial) :
    1 ≤ C.cost ∨ ∃ r, r ≠ 0 ∧ ((vcost W r : ℚ) : ℝ) ≤ C.cost := by
  have hle : ∀ i, max ((vcost W (C.vert i) : ℚ) : ℝ) |C.t i| ≤ C.cost := fun i =>
    Finset.le_sup' (fun k => max ((vcost W (C.vert k) : ℚ) : ℝ) |C.t k|) (Finset.mem_univ i)
  by_cases hv : ∃ i, C.vert i ≠ 0
  · obtain ⟨i, hi⟩ := hv
    exact Or.inr ⟨C.vert i, hi, (le_max_left _ _).trans (hle i)⟩
  · push Not at hv
    left
    have : ∃ i, C.t i ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hC fun i => ⟨hv i, h' i⟩
    obtain ⟨i, hi⟩ := this
    obtain ⟨n, hn⟩ := C.edge i
    rw [hv i, hv (finRotate C.L i)] at hn
    simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero, zero_div, zero_add] at hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hi (by rw [hn]; simp)
    have h1 : (1 : ℝ) ≤ |C.t i| := by
      rw [hn]; exact_mod_cast Int.one_le_abs hn0
    exact h1.trans ((le_max_right _ _).trans (hle i))

/-- witness achieving `min(1, m*)` (a self-loop, hence also a simple cycle) -/
theorem witness (W : List ℕ) (hW : ∀ a ∈ W, 1 ≤ a) (hK : 2 ≤ contK W) :
    ∃ C : ClosedWalk W, Function.Injective C.vert ∧ ¬ C.allTrivial ∧
      C.cost = min 1 (mstar W) := by
  rcases le_total 1 (mstar W) with h | h
  · refine ⟨loopZero W, loopAt_injective _ _ _ _, loopZero_nontrivial W, ?_⟩
    rw [loopZero_cost, min_eq_left h]
  · obtain ⟨⟨r, hr, he⟩, -⟩ := mstar_isLeast W hK
    set x : ℝ := ((r.val : ℝ) - (sigma W : ℝ) * (r.val : ℝ)) / (contK W : ℝ)
    have ht : ∃ n : ℤ, x - round x = x + n := ⟨-round x, by push_cast; ring⟩
    refine ⟨loopAt W r (x - round x) ht, loopAt_injective _ _ _ _, ?_, ?_⟩
    · intro hC
      exact hr (hC ⟨0, Nat.one_pos⟩).1
    · rw [loopAt_cost, min_eq_right h, ← he]
      apply max_eq_left
      exact (abs_sub_round x).trans (he ▸ mstar_ge_half W hW hK)

/-- **Corollary 2 (K ≥ 2).** `ν(W) = min(1, m*)`, the minimum being attained; same for the
simple-cycle reading. -/
theorem cor2_K_ge_two (W : List ℕ) (hW : ∀ a ∈ W, 1 ≤ a) (hK : 2 ≤ contK W) :
    IsLeast (costSet W) (min 1 (mstar W)) ∧ nu W = min 1 (mstar W) ∧
    IsLeast (costSetSimple W) (min 1 (mstar W)) ∧ nuSimple W = min 1 (mstar W) := by
  obtain ⟨C, hinj, hC, hcost⟩ := witness W hW hK
  have lower : ∀ C : ClosedWalk W, ¬ C.allTrivial → min 1 (mstar W) ≤ C.cost := by
    intro C hC
    rcases cost_lower C hC with h | ⟨r, hr, h⟩
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans
        (((mstar_isLeast W hK).2 ⟨r, hr, rfl⟩).trans h)
  have h1 : IsLeast (costSet W) (min 1 (mstar W)) :=
    ⟨⟨C, hC, hcost⟩, by rintro x ⟨C', hC', rfl⟩; exact lower C' hC'⟩
  have h2 : IsLeast (costSetSimple W) (min 1 (mstar W)) :=
    ⟨⟨C, hinj, hC, hcost⟩, by rintro x ⟨C', -, hC', rfl⟩; exact lower C' hC'⟩
  exact ⟨h1, h1.csInf_eq, h2, h2.csInf_eq⟩

/-- **Corollary 2 (K = 1).** `ν(W) = 1`; same for the simple-cycle reading. -/
theorem cor2_K_eq_one (W : List ℕ) (hK : contK W = 1) :
    IsLeast (costSet W) 1 ∧ nu W = 1 ∧ IsLeast (costSetSimple W) 1 ∧ nuSimple W = 1 := by
  have lower : ∀ C : ClosedWalk W, ¬ C.allTrivial → 1 ≤ C.cost := by
    intro C hC
    rcases cost_lower C hC with h | ⟨r, hr, -⟩
    · exact h
    · exfalso; apply hr
      have : Subsingleton (ZMod (contK W)) := by rw [hK]; infer_instance
      exact Subsingleton.elim _ _
  have h1 : IsLeast (costSet W) 1 :=
    ⟨⟨loopZero W, loopZero_nontrivial W, loopZero_cost W⟩,
      by rintro x ⟨C', hC', rfl⟩; exact lower C' hC'⟩
  have h2 : IsLeast (costSetSimple W) 1 :=
    ⟨⟨loopZero W, loopAt_injective _ _ _ _, loopZero_nontrivial W, loopZero_cost W⟩,
      by rintro x ⟨C', -, hC', rfl⟩; exact lower C' hC'⟩
  exact ⟨h1, h1.csInf_eq, h2, h2.csInf_eq⟩

/-- **Corollary 2 (conclusion).** `ν(W) ≥ 1/2` for every block word. -/
theorem nu_ge_half (W : List ℕ) (hW : ∀ a ∈ W, 1 ≤ a) :
    (1 : ℝ) / 2 ≤ nu W ∧ (1 : ℝ) / 2 ≤ nuSimple W := by
  have hK1 := contK_pos W hW
  rcases Nat.lt_or_ge (contK W) 2 with h | h
  · obtain ⟨-, h1, -, h2⟩ := cor2_K_eq_one W (by omega)
    rw [h1, h2]; norm_num
  · obtain ⟨-, h1, -, h2⟩ := cor2_K_ge_two W hW h
    have := mstar_ge_half W hW h
    rw [h1, h2]
    exact ⟨le_min (by norm_num) this, le_min (by norm_num) this⟩

/-! ## Sanity checks of the definitions (kernel `rfl` / `decide`) -/

example : contK [] = 1 := rfl
example : contK [7] = 7 := rfl
example : contK [1, 1] = 2 := rfl
example : contK [5, 1, 1, 1, 5] = 96 := rfl
example : sigma [5, 1, 1, 1, 5] = 17 := rfl
example : dK 96 (-50) = 46 := by decide
example : cc [5, 1, 1, 1, 5] 3 = 11 ∧ cc' [5, 1, 1, 1, 5] 3 = 5 := ⟨rfl, rfl⟩
/-- the extremal value `12/17` reported by the finite search (W = (5,1,1,1,5), r = 12) -/
theorem sanity_extremal : vcost [5, 1, 1, 1, 5] 12 = 12 / 17 := by decide +kernel
/-- non-vacuity of Proposition 1's hypotheses -/
theorem sanity_prop1_instance : (1 : ℚ) / 2 ≤ vcost [5, 1, 1, 1, 5] 12 :=
  prop1 _ (by decide) (by decide) 12 (by decide)

end R6S7

#print axioms R6S7.dK_isLeast
#print axioms R6S7.contK_append_two
#print axioms R6S7.contK_cons_cons
#print axioms R6S7.vcost_isGreatest
#print axioms R6S7.dK_congr
#print axioms R6S7.vterm_lift
#print axioms R6S7.core_main
#print axioms R6S7.prop1
#print axioms R6S7.mstar_isLeast
#print axioms R6S7.mstar_ge_half
#print axioms R6S7.cor2_K_ge_two
#print axioms R6S7.cor2_K_eq_one
#print axioms R6S7.nu_ge_half
#print axioms R6S7.sanity_extremal
#print axioms R6S7.sanity_prop1_instance
