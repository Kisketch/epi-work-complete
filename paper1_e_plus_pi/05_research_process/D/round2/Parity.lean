import Prop81

open DVerify GenContFract
namespace RoundTwoD
noncomputable section

theorem forced_identity (B A : ℤ) (j : ℕ) (p d : ℤ)
    (hB : 0 < B) (hj : (3 * (B : ℝ) / 2)^2 < j)
    (hA : (B : ℝ) * (Real.exp 1 + Real.pi) = A)
    (hd : 1 ≤ d) (hH : d ≤ (H j : ℤ))
    (he : |(d:ℝ)*Real.pi-p| ≤ 1 / ((H j : ℝ)+1)) :
    A * Qsel j * d = B * (Psel j * d + p * Qsel j) :=
  sub_eq_zero.mp (linForm_eq_zero B A j p d hB hj hA hd hH he)

theorem forced_opposition (B A : ℤ) (j : ℕ) (p d : ℤ)
    (hB : 0 < B) (hj : (3 * (B : ℝ) / 2)^2 < j)
    (hA : (B : ℝ) * (Real.exp 1 + Real.pi) = A)
    (hd : 1 ≤ d) (hH : d ≤ (H j : ℤ))
    (he : |(d:ℝ)*Real.pi-p| ≤ 1 / ((H j : ℝ)+1)) :
    (-1 : ℝ)^j * ((d:ℝ)*Real.pi-p) < 0 := by
  have h := linForm_identity A B j p d hA
  rw [linForm_eq_zero B A j p d hB hj hA hd hH he] at h
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hc : (d:ℝ)*deltaSel j + (Qsel j:ℝ)*((d:ℝ)*Real.pi-p) = 0 :=
    (mul_eq_zero.mp (by simpa using h.symm)).resolve_left hBr.ne'
  have hj1 : 1 ≤ j := by
    by_contra! h0
    have : j = 0 := by omega
    subst j
    norm_num at hj
    nlinarith [sq_nonneg (3*(B:ℝ)/2)]
  have hs := Hermite.sign_alternation j hj1
  have hq : (0:ℝ) < Qsel j := by exact_mod_cast Qsel_pos_all j
  have hd' : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  by_contra! hnonneg
  nlinarith only [mul_nonneg hq.le hnonneg, mul_pos hd' hs, congrArg (fun y : ℝ => (-1:ℝ)^j*y) hc]

private abbrev G := GenContFract.of Real.pi

private theorem alive (k : ℕ) : ¬G.TerminatedAt k := by
  intro h
  obtain ⟨r,hr⟩ := (GenContFract.terminates_iff_rat Real.pi).mp ⟨k,h⟩
  exact irrational_pi ⟨r,hr.symm⟩

private theorem int_cont (k : ℕ) : ∃ a b : ℤ,
    (G.contsAux k).a = a ∧ (G.contsAux k).b = b := by
  induction k using Nat.twoStepInduction with
  | zero => exact ⟨1,0,by simp [GenContFract.zeroth_contAux_eq_one_zero],by simp [GenContFract.zeroth_contAux_eq_one_zero]⟩
  | one => exact ⟨⌊Real.pi⌋,1,rfl,by simp [GenContFract.first_contAux_eq_h_one]⟩
  | more k h₀ h₁ =>
    obtain ⟨a,b,ha,hb⟩ := h₀
    obtain ⟨c,d,hc,hd⟩ := h₁
    obtain ⟨z,hz⟩ := Option.ne_none_iff_exists'.mp (alive k)
    obtain ⟨ha',i,hi⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hz
    rw [GenContFract.contsAux_recurrence hz rfl rfl]
    exact ⟨i*c+a,i*d+b,by simp [hi,ha',ha,hc],by simp [hi,ha',hb,hd]⟩

private theorem nd_int (k : ℕ) : ∃ p d : ℤ, G.nums k = p ∧ G.dens k = d := int_cont (k+1)

theorem pi_cutoff_opposition (B A : ℤ) (j k : ℕ)
    (hB : 0 < B) (hj : (3 * (B : ℝ) / 2)^2 < j)
    (hA : (B : ℝ) * (Real.exp 1 + Real.pi) = A)
    (hlo : G.dens k ≤ H j) (hhi : (H j : ℝ) < G.dens (k+1)) :
    (-1:ℝ)^j * (G.dens k * Real.pi - G.nums k) < 0 := by
  obtain ⟨p,d,hp,hd⟩ := nd_int k
  obtain ⟨_,s,_,hs⟩ := nd_int (k+1)
  have h0 : (0:ℝ) < G.dens k := lt_of_lt_of_le
    (by exact_mod_cast (Nat.fib_pos.mpr (Nat.succ_pos k)))
    (GenContFract.succ_nth_fib_le_of_nth_den (v:=Real.pi) (n:=k) (Or.inr (alive _)))
  have h1 : (0:ℝ) < G.dens (k+1) := lt_of_le_of_lt (by positivity : (0:ℝ) ≤ H j) hhi
  have herr := GenContFract.abs_sub_convs_le (alive k)
  rw [GenContFract.conv_eq_num_div_den] at herr
  have eq : G.dens k * (Real.pi - G.nums k / G.dens k) = G.dens k*Real.pi-G.nums k := by
    field_simp
  have herr' : |G.dens k * Real.pi - G.nums k| ≤ 1 / G.dens (k+1) := by
    rw [←eq, abs_mul, abs_of_pos h0]
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left herr h0.le
      _ = _ := by field_simp
  rw [hd,hp] at herr' ⊢
  rw [hd] at h0 hlo
  rw [hs] at hhi
  have ds : (H j : ℤ) < s := by exact_mod_cast hhi
  have hs' : (H j:ℝ)+1 ≤ G.dens (k+1) := by rw [hs]; exact_mod_cast (show (H j:ℤ)+1 ≤ s by omega)
  have hd' : (0:ℤ) < d := by exact_mod_cast h0
  exact forced_opposition B A j p d hB hj hA (by omega) (by exact_mod_cast hlo)
    (herr'.trans (one_div_le_one_div_of_le (by positivity) hs'))

theorem pi_cutoff_parity (B A : ℤ) (j k : ℕ)
    (hB : 0 < B) (hj : (3 * (B : ℝ) / 2)^2 < j)
    (hA : (B : ℝ) * (Real.exp 1 + Real.pi) = A)
    (hlo : G.dens k ≤ H j) (hhi : (H j : ℝ) < G.dens (k+1)) :
    ¬ Even (j+k) := by
  intro he
  have h := pi_cutoff_opposition B A j k hB hj hA hlo hhi
  have hst : IntFractPair.stream Real.pi k ≠ none := by
    cases k with
    | zero => simp [IntFractPair.stream_zero]
    | succ n => exact fun hn => alive n (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr hn)
  obtain ⟨t,ht⟩ := Option.ne_none_iff_exists'.mp hst
  have hD : (0:ℝ) < G.dens k := lt_of_lt_of_le
    (by exact_mod_cast (Nat.fib_pos.mpr (Nat.succ_pos k)))
    (GenContFract.succ_nth_fib_le_of_nth_den (v:=Real.pi) (n:=k) (Or.inr (alive _)))
  have hprev : 0 ≤ (G.contsAux k).b :=
    le_trans (by positivity : 0 ≤ (Nat.fib k : ℝ)) (GenContFract.fib_le_of_contsAux_b (Or.inr (alive _)))
  have heq : G.dens k * (Real.pi-G.convs k) = G.dens k*Real.pi-G.nums k := by
    rw [GenContFract.conv_eq_num_div_den]; field_simp
  rw [←heq] at h
  have hs := GenContFract.sub_convs_eq ht
  change Real.pi-G.convs k = if t.fr=0 then 0 else
    (-1:ℝ)^k/(G.dens k*(t.fr⁻¹*G.dens k+(G.contsAux k).b)) at hs
  rw [hs] at h
  split at h
  · simp at h
  · have ht0 := IntFractPair.nth_stream_fr_nonneg ht
    have hden : 0 ≤ G.dens k * (t.fr⁻¹ * G.dens k + (G.contsAux k).b) := by positivity
    have hnn := div_nonneg hD.le hden
    have hp : (-1:ℝ)^j * (-1:ℝ)^k = 1 := by rw [← pow_add]; exact he.neg_one_pow
    rw [show (-1:ℝ)^j * (G.dens k * ((-1:ℝ)^k / _)) =
      ((-1:ℝ)^j * (-1:ℝ)^k) * (G.dens k / (G.dens k*(t.fr⁻¹*G.dens k+(G.contsAux k).b))) by ring,
      hp, one_mul] at h
    exact (not_lt_of_ge hnn) h

/-- Every positive-index window has a genuine terminal convergent. -/
theorem cutoff_exists (j : ℕ) (hj : 1 ≤ j) :
    ∃ k, G.dens k ≤ H j ∧ (H j:ℝ) < G.dens (k+1) := by
  classical
  have hex : ∃ k : ℕ, (H j:ℝ) < G.dens (k+1) := by
    let t := H j+6
    refine ⟨t,?_⟩
    apply lt_of_lt_of_le _ (GenContFract.succ_nth_fib_le_of_nth_den
      (v:=Real.pi) (n:=t+1) (Or.inr (alive _)))
    exact_mod_cast (show H j < Nat.fib (t+1+1) from lt_of_lt_of_le
      (by dsimp [t]; omega) (Nat.le_fib_self (by dsimp [t]; omega)))
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  cases heq : Nat.find hex with
  | zero =>
    rw [GenContFract.zeroth_den_eq_one]
    exact_mod_cast H_pos j hj
  | succ n =>
    exact le_of_not_gt (Nat.find_min hex (show n < Nat.find hex by omega))

/-- The unresolved premise is infinitely many parity agreements for the true π. -/
theorem irrational_of_parity_agreements
    (h : ∀ N : ℕ, ∃ j k : ℕ, N ≤ j ∧ G.dens k ≤ H j ∧
        (H j : ℝ) < G.dens (k+1) ∧ Even (j+k)) :
    Irrational (Real.exp 1 + Real.pi) := by
  rintro ⟨r, hr⟩
  have hA : ((r.den : ℤ):ℝ) * (Real.exp 1 + Real.pi) = r.num := by
    rw [← hr, Rat.cast_def]
    push_cast
    field_simp
  have hB : (0:ℤ) < r.den := by exact_mod_cast r.den_pos
  obtain ⟨N,hN⟩ := exists_nat_gt ((3 * ((r.den:ℤ):ℝ) / 2)^2)
  obtain ⟨j,k,hj,hl,hu,he⟩ := h N
  exact pi_cutoff_parity r.den r.num j k hB (lt_of_lt_of_le hN (by exact_mod_cast hj)) hA hl hu he

#print axioms cutoff_exists
#print axioms irrational_of_parity_agreements

#print axioms pi_cutoff_parity

#print axioms pi_cutoff_opposition

#print axioms forced_identity
#print axioms forced_opposition
end
end RoundTwoD




