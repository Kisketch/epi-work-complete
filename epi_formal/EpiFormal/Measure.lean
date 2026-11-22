import Mathlib
import EpiFormal.Axioms

/-!
# T2 层：无理性度量（整数分子 + ENNReal 值域）、定理 E 恒等式、不变性与定理 A

**定义修正（2026-11-13）**：
1. 逼近对分子为整数 ℤ（非 ℚ，否则定义退化：固定 q=1 即无穷多有理分子）。
2. 值域用 ENNReal（ENNReal）：ℝ 的 sSup 无法表示 +∞，Liouville 数度量应为 ⊤。
   μ(x) = sSup{ν≥0 : 无穷多 (p,q)∈ℤ×ℕ, q>0, |x−p/q| < q^(−ν)} ∈ ENNReal。
-/

open Real Set Filter

/-- 逼近对集合：A(x,ν) = {(p,q)∈ℤ×ℕ : q>0 ∧ |x−p/q| < q^(−ν)}。 -/
def apprPairs (x : ℝ) (ν : ℝ) : Set (ℤ × ℕ) :=
  {pq | 0 < pq.2 ∧ |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < (pq.2 : ℝ) ^ (-ν)}

/-- 逼近指数集合（非负实指数）：S(x) = {ν≥0 : A(x,ν) 无穷}。 -/
def apprSet (x : ℝ) : Set NNReal := {ν | (apprPairs x (ν : ℝ)).Infinite}

/-- 无理性度量 μ(x) ∈ ENNReal = sSup (S(x))（嵌入 ENNReal）。 -/
noncomputable def irrMeasure (x : ℝ) : ENNReal :=
  sSup ((fun ν : NNReal => (ν : ENNReal)) '' apprSet x)

/-- 公理：μ(e)=2（Bundschuh 结果）。 -/
axiom mu_e_eq_two : irrMeasure (exp 1) = 2

/-- 定理 E 的对数恒等式（M3，已证）：μ₀ = 1 + 1/(M−1)。 -/
theorem mu0_identity (D ρ : ℝ) (hD : 1 < D) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    log (D / ρ) / log D = 1 + 1 / (log D / log (1 / ρ)) := by
  have hD0 : 0 < D := by linarith
  have hlogD : log D ≠ 0 := ne_of_gt (Real.log_pos hD)
  have hlogρ : log ρ ≠ 0 := ne_of_lt (Real.log_neg hρ0 hρ1)
  have hρinv : 1 < (1 : ℝ) / ρ := one_lt_one_div hρ0 hρ1
  have hlog1ρ : log (1 / ρ) = -log ρ := by
    rw [Real.log_div one_ne_zero hρ0.ne', Real.log_one, zero_sub]
  rw [hlog1ρ]
  field_simp
  rw [Real.log_div hD0.ne' hρ0.ne']
  ring

/-- 下闭性：ν∈S(x) 且 ν'≤ν ⇒ ν'∈S(x)。 -/
lemma apprSet_downward {x : ℝ} {ν ν' : NNReal} (hν : ν ∈ apprSet x) (hle : ν' ≤ ν) :
    ν' ∈ apprSet x := by
  simp only [apprSet, apprPairs, Set.mem_setOf_eq] at hν ⊢
  refine hν.mono ?_
  intro ⟨p, q⟩ hpq
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast hpq.1
  have hcoe : (ν' : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hle
  have hrpow : (q : ℝ) ^ (-(ν : ℝ)) ≤ (q : ℝ) ^ (-(ν' : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  exact ⟨hpq.1, lt_of_lt_of_le hpq.2 hrpow⟩

/-- sSup 单调（ENNReal，无需有上界）：S(x) ⊆ S(y) ⇒ μ(x) ≤ μ(y)。 -/
lemma irrMeasure_mono {x y : ℝ} (h : apprSet x ⊆ apprSet y) :
    irrMeasure x ≤ irrMeasure y := by
  simp only [irrMeasure]
  apply sSup_le_sSup
  intro a ha
  obtain ⟨ν, hν, rfl⟩ := ha
  exact ⟨ν, h hν, rfl⟩

/-- 集合相等 ⇒ μ 相等。 -/
lemma irrMeasure_congr {x y : ℝ} (h : apprSet x = apprSet y) :
    irrMeasure x = irrMeasure y := by
  simp only [irrMeasure, h]

/-- ε-吸收比较：若 ν∈S(y) ⇒ 对任意 0<ε≤ν 有 ν−ε∈S(x)，则 μ(y)≤μ(x)。
    用 ENNReal.le_of_forall_pos_le_add：有限时以 ε 逼近，无穷时平凡。 -/
lemma irrMeasure_le_of_eps {x y : ℝ}
    (h : ∀ ν ∈ apprSet y, ∀ ε : NNReal, 0 < ε → ε ≤ ν →
      (ν - ε) ∈ apprSet x) :
    irrMeasure y ≤ irrMeasure x := by
  simp only [irrMeasure]
  apply sSup_le
  intro a ha
  obtain ⟨ν, hν, rfl⟩ := ha
  -- 目标 (ν:ENNReal) ≤ sSup (coe '' S(x))
  by_cases htop : sSup ((fun ν : NNReal => (ν : ENNReal)) '' apprSet x) = ⊤
  · rw [htop]; exact le_top
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    -- 取 δ = min(ε, ν) 的一半思路：用 ε' = min ε ν（若 ν=0 则平凡）
    by_cases hν0 : ν = 0
    · subst hν0
      simp only [NNReal.coe_zero]
      exact bot_le
    · have hνpos : 0 < ν := by
        contrapose! hν0
        exact le_antisymm hν0 (bot_le : (0 : NNReal) ≤ ν)
      have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
      have hνR : 0 < (ν : ℝ) := by exact_mod_cast hνpos
      have hminpos : 0 < min (ε : ℝ) (ν : ℝ) / 2 := by
        apply div_pos (lt_min hεR hνR) (by norm_num)
      set ε' : NNReal := ⟨min (ε : ℝ) (ν : ℝ) / 2, le_of_lt hminpos⟩ with hε'def
      have hε'coe : (ε' : ℝ) = min (ε : ℝ) (ν : ℝ) / 2 := rfl
      have hε'pos : 0 < ε' := by
        rw [← NNReal.coe_pos, hε'coe]; exact hminpos
      have hε'le : ε' ≤ ν := by
        apply NNReal.coe_le_coe.mp
        rw [hε'coe]
        linarith [min_le_right (ε : ℝ) (ν : ℝ)]
      have hmem : (ν - ε') ∈ apprSet x := h ν hν ε' hε'pos hε'le
      have hle : ((ν - ε' : NNReal) : ENNReal) ≤
          sSup ((fun ν : NNReal => (ν : ENNReal)) '' apprSet x) :=
        le_sSup ⟨ν - ε', hmem, rfl⟩
      have hνle : (ν : ENNReal) ≤ ((ν - ε' : NNReal) : ENNReal) + (ε : ENNReal) := by
        have hreal : (ν : ℝ) ≤ ((ν - ε' : NNReal) : ℝ) + (ε : ℝ) := by
          rw [NNReal.coe_sub hε'le, hε'coe]
          linarith [min_le_left (ε : ℝ) (ν : ℝ)]
        exact_mod_cast hreal
      calc (ν : ENNReal) ≤ ((ν - ε' : NNReal) : ENNReal) + (ε : ENNReal) := hνle
        _ ≤ sSup ((fun ν : NNReal => (ν : ENNReal)) '' apprSet x) + (ε : ENNReal) :=
          add_le_add hle (le_refl _)

/-- 符号不变性：μ(−x)=μ(x)。（已证，双射 (p,q)↦(−p,q)） -/
theorem irrMeasure_neg (x : ℝ) : irrMeasure (-x) = irrMeasure x := by
  apply irrMeasure_congr
  ext ν
  simp only [apprSet, apprPairs, Set.mem_setOf_eq]
  have hbij : {pq : ℤ × ℕ | 0 < pq.2 ∧ |(-x) - (pq.1 : ℝ) / (pq.2 : ℝ)| < (pq.2 : ℝ) ^ (-(ν : ℝ))}
      = (fun pq : ℤ × ℕ => (-pq.1, pq.2)) ''
        {pq : ℤ × ℕ | 0 < pq.2 ∧ |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < (pq.2 : ℝ) ^ (-(ν : ℝ))} := by
    ext ⟨p, q⟩
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq]
    constructor
    · intro h
      refine ⟨(-p, q), ?_, ?_⟩
      · have hq : 0 < q := h.1
        have hine : |(-x) - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-(ν : ℝ)) := h.2
        have heq : |x - ((-p : ℤ) : ℝ) / (q : ℝ)| = |(-x) - (p : ℝ) / (q : ℝ)| := by
          push_cast
          rw [← abs_neg]
          congr 1
          ring
        exact ⟨hq, by rw [heq]; exact hine⟩
      · simp
    · rintro ⟨⟨a, b⟩, ⟨hb, hine⟩, h1, h2⟩
      simp only at h1 h2
      subst h1; subst h2
      refine ⟨hb, ?_⟩
      have heq : |(-x) - ((-a : ℤ) : ℝ) / (b : ℝ)| = |x - (a : ℝ) / (b : ℝ)| := by
        push_cast
        rw [← abs_neg]
        congr 1
        ring
      rw [heq]; exact hine
  rw [hbij]
  rw [Set.infinite_image_iff]
  intro ⟨a, b⟩ _ ⟨c, d⟩ _ h
  simp only [Prod.mk.injEq] at h ⊢
  have hac : a = c := by linarith [h.1]
  exact ⟨hac, h.2⟩

/-- 分母无界：若 A(x,ν) 无穷，则对任意 N 存在 (p,q)∈A 使 q>N。
    因固定 q 时 |x−p/q|<q^(−ν) 把整数 p 限制在有限区间。 -/
lemma apprPairs_denom_unbounded {x : ℝ} {ν : ℝ} (hinf : (apprPairs x ν).Infinite)
    (N : ℕ) : ∃ pq ∈ apprPairs x ν, N < pq.2 := by
  by_contra h
  push_neg at h
  have hfin : (apprPairs x ν).Finite := by
    -- 包含于 ⋃_{q≤N} {p : ⌊(x−q^(−ν))q⌋ ≤ p ≤ ⌈(x+q^(−ν))q⌉} × {q}
    have hsub : apprPairs x ν ⊆
        ⋃ q ∈ {q : ℕ | q ≤ N}, (fun p : ℤ => (p, q)) ''
          Set.Icc ⌊(x - (q : ℝ) ^ (-ν)) * (q : ℝ)⌋ ⌈(x + (q : ℝ) ^ (-ν)) * (q : ℝ)⌉ := by
      intro ⟨p, q⟩ hpq
      simp only [apprPairs, Set.mem_setOf_eq] at hpq
      have hqN : q ≤ N := h (p, q) hpq
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_Icc, Set.mem_setOf_eq]
      refine ⟨q, hqN, p, ?_, rfl⟩
      have hqpos : 0 < (q : ℝ) := by exact_mod_cast hpq.1
      rw [abs_lt] at hpq
      have hupper : (p : ℝ) < (x + (q : ℝ) ^ (-ν)) * (q : ℝ) := by
        have h1 : (p : ℝ) / (q : ℝ) < x + (q : ℝ) ^ (-ν) := by linarith [hpq.2.1]
        rwa [div_lt_iff₀ hqpos] at h1
      have hlower : (x - (q : ℝ) ^ (-ν)) * (q : ℝ) < (p : ℝ) := by
        have h1 : x - (q : ℝ) ^ (-ν) < (p : ℝ) / (q : ℝ) := by linarith [hpq.2.2]
        rwa [lt_div_iff₀ hqpos] at h1
      constructor
      · calc ⌊(x - (q : ℝ) ^ (-ν)) * (q : ℝ)⌋ ≤ ⌊(p : ℝ)⌋ :=
            Int.floor_mono (le_of_lt hlower)
          _ = p := Int.floor_intCast p
      · calc (p : ℤ) = ⌈(p : ℝ)⌉ := (Int.ceil_intCast p).symm
          _ ≤ ⌈(x + (q : ℝ) ^ (-ν)) * (q : ℝ)⌉ := Int.ceil_mono (le_of_lt hupper)
    refine Set.Finite.subset ?_ hsub
    apply Set.Finite.biUnion (Set.finite_le_nat N)
    intro q _
    exact (Set.finite_Icc _ _).image _
  exact hinf hfin

/-- 常数吸收：若无穷多 (P,Q) 使 |x−P/Q| < C·Q^(−ν)（C>0），则对 0<ε≤ν 有 ν−ε∈S(x)。
    取阈值 T 使 C≤T^ε；限制 Q>T 的子集仍无穷（分母无界），其上 C·Q^(−ν)≤Q^(−(ν−ε))。 -/
lemma const_absorption {x : ℝ} {ν : ℝ} {C : ℝ} (hC : 0 < C)
    (hinf : Set.Infinite {pq : ℤ × ℕ | 0 < pq.2 ∧
      |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < C * (pq.2 : ℝ) ^ (-ν)})
    (ε : NNReal) (hεpos : 0 < ε) (hεle : (ε : ℝ) ≤ ν) :
    (⟨ν - (ε : ℝ), by linarith⟩ : NNReal) ∈ apprSet x := by
  simp only [apprSet, apprPairs, Set.mem_setOf_eq]
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hεpos
  -- 阈值 T 使 C ≤ T^ε
  obtain ⟨T, hT⟩ : ∃ T : ℕ, C ≤ (T : ℝ) ^ (ε : ℝ) := by
    obtain ⟨T, hT⟩ := exists_nat_gt (C ^ (1 / (ε : ℝ)) + 1)
    refine ⟨T, ?_⟩
    have hCpow : 0 ≤ C ^ (1 / (ε : ℝ)) := Real.rpow_nonneg (le_of_lt hC) _
    have hTpos : 0 < (T : ℝ) := by linarith
    have h1 : C ^ (1 / (ε : ℝ)) < (T : ℝ) := by linarith
    have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hεR
    have h2 : C = (C ^ (1 / (ε : ℝ))) ^ (ε : ℝ) := by
      have hmul : (1 / (ε : ℝ)) * (ε : ℝ) = 1 := by
        rw [one_div, inv_mul_cancel₀ hεne]
      calc C = C ^ (1 : ℝ) := (Real.rpow_one C).symm
        _ = C ^ ((1 / (ε : ℝ)) * (ε : ℝ)) := by rw [hmul]
        _ = (C ^ (1 / (ε : ℝ))) ^ (ε : ℝ) := Real.rpow_mul (le_of_lt hC) _ _
    rw [h2]
    exact Real.rpow_le_rpow (by positivity) (le_of_lt h1) (le_of_lt hεR)
  -- 带常数界且 Q>T 的子集
  set S := {pq : ℤ × ℕ | 0 < pq.2 ∧
      |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < C * (pq.2 : ℝ) ^ (-ν) ∧ T < pq.2} with hSdef
  -- S 无穷：原集无穷且分母无界 ⇒ 去掉 Q≤T 的有限部分仍无穷
  have hSinf : S.Infinite := by
    have hfin : {pq : ℤ × ℕ | 0 < pq.2 ∧
        |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < C * (pq.2 : ℝ) ^ (-ν) ∧ pq.2 ≤ T}.Finite := by
      -- 分母 ≤T，对每个分母分子有限（同分母无界引理的有限性论证）
      have hsub : {pq : ℤ × ℕ | 0 < pq.2 ∧
          |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < C * (pq.2 : ℝ) ^ (-ν) ∧ pq.2 ≤ T} ⊆
          ⋃ q ∈ {q : ℕ | q ≤ T}, (fun p : ℤ => (p, q)) ''
            Set.Icc ⌊(x - C * (q : ℝ) ^ (-ν)) * (q : ℝ)⌋
              ⌈(x + C * (q : ℝ) ^ (-ν)) * (q : ℝ)⌉ := by
        intro ⟨p, q⟩ hpq
        simp only [Set.mem_setOf_eq] at hpq
        simp only [Set.mem_iUnion, Set.mem_image, Set.mem_Icc, Set.mem_setOf_eq]
        refine ⟨q, hpq.2.2, p, ?_, rfl⟩
        have hqpos : 0 < (q : ℝ) := by exact_mod_cast hpq.1
        rw [abs_lt] at hpq
        have hupper : (p : ℝ) < (x + C * (q : ℝ) ^ (-ν)) * (q : ℝ) := by
          have h1 : (p : ℝ) / (q : ℝ) < x + C * (q : ℝ) ^ (-ν) := by linarith [hpq.2.1.1]
          rwa [div_lt_iff₀ hqpos] at h1
        have hlower : (x - C * (q : ℝ) ^ (-ν)) * (q : ℝ) < (p : ℝ) := by
          have h1 : x - C * (q : ℝ) ^ (-ν) < (p : ℝ) / (q : ℝ) := by linarith [hpq.2.1.2]
          rwa [lt_div_iff₀ hqpos] at h1
        constructor
        · calc ⌊(x - C * (q : ℝ) ^ (-ν)) * (q : ℝ)⌋ ≤ ⌊(p : ℝ)⌋ :=
              Int.floor_mono (le_of_lt hlower)
            _ = p := Int.floor_intCast p
        · calc (p : ℤ) = ⌈(p : ℝ)⌉ := (Int.ceil_intCast p).symm
            _ ≤ ⌈(x + C * (q : ℝ) ^ (-ν)) * (q : ℝ)⌉ := Int.ceil_mono (le_of_lt hupper)
      refine Set.Finite.subset ?_ hsub
      apply Set.Finite.biUnion (Set.finite_le_nat T)
      intro q _
      exact (Set.finite_Icc _ _).image _
    -- 原集 = S ∪ {Q≤T 部分}；原集无穷、后者有限 ⇒ S 无穷
    have hunion : {pq : ℤ × ℕ | 0 < pq.2 ∧
        |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < C * (pq.2 : ℝ) ^ (-ν)} ⊆
        S ∪ {pq : ℤ × ℕ | 0 < pq.2 ∧
          |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < C * (pq.2 : ℝ) ^ (-ν) ∧ pq.2 ≤ T} := by
      intro ⟨p, q⟩ hpq
      simp only [Set.mem_setOf_eq, Set.mem_union, hSdef] at hpq ⊢
      by_cases hqT : T < q
      · exact Or.inl ⟨hpq.1, hpq.2, hqT⟩
      · exact Or.inr ⟨hpq.1, hpq.2, le_of_not_gt hqT⟩
    by_contra hSfin
    have hSfin' : S.Finite := Set.not_infinite.mp hSfin
    have : {pq : ℤ × ℕ | 0 < pq.2 ∧
        |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < C * (pq.2 : ℝ) ^ (-ν)}.Finite :=
      Set.Finite.subset (Set.Finite.union hSfin' hfin) hunion
    exact hinf this
  -- S ⊆ A(x, ν−ε)
  have hsub : S ⊆ apprPairs x (ν - (ε : ℝ)) := by
    intro ⟨P, Q⟩ hpq
    simp only [hSdef, Set.mem_setOf_eq, apprPairs] at hpq ⊢
    have hQT : (T : ℝ) < (Q : ℝ) := by exact_mod_cast hpq.2.2
    have hQpos : 0 < (Q : ℝ) := by linarith
    have habs : C ≤ (Q : ℝ) ^ (ε : ℝ) := by
      calc C ≤ (T : ℝ) ^ (ε : ℝ) := hT
        _ ≤ (Q : ℝ) ^ (ε : ℝ) :=
          Real.rpow_le_rpow (by positivity) (le_of_lt hQT) (le_of_lt hεR)
    refine ⟨hpq.1, ?_⟩
    calc |x - (P : ℝ) / (Q : ℝ)| < C * (Q : ℝ) ^ (-ν) := hpq.2.1
      _ ≤ (Q : ℝ) ^ (ε : ℝ) * (Q : ℝ) ^ (-ν) :=
        mul_le_mul_of_nonneg_right habs (Real.rpow_nonneg (le_of_lt hQpos) _)
      _ = (Q : ℝ) ^ (-(ν - (ε : ℝ))) := by
        rw [← Real.rpow_add hQpos]
        congr 1
        ring
  exact Set.Infinite.mono hsub hSinf

/-- NNReal 版常数吸收：匹配 irrMeasure_le_of_eps 的类型。 -/
lemma const_absorption_nn {x : ℝ} {ν : NNReal} {C : ℝ} (hC : 0 < C)
    (hinf : Set.Infinite {pq : ℤ × ℕ | 0 < pq.2 ∧
      |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < C * (pq.2 : ℝ) ^ (-(ν : ℝ))})
    (ε : NNReal) (hεpos : 0 < ε) (hεle : ε ≤ ν) :
    (ν - ε) ∈ apprSet x := by
  have hεleR : (ε : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hεle
  have h := const_absorption hC hinf ε hεpos hεleR
  have hcoe : ((ν - ε : NNReal) : ℝ) = (ν : ℝ) - (ε : ℝ) := NNReal.coe_sub hεle
  have heq : (ν - ε : NNReal) = ⟨(ν : ℝ) - (ε : ℝ), by linarith⟩ := by
    ext
    exact hcoe
  rw [heq]
  exact h

/-- 单向平移：μ(x+q) ≤ μ(x)。通分双射 (p,q')↦(pb−aq,bq') + 常数吸收。 -/
lemma add_rat_le (x : ℝ) (q : ℚ) : irrMeasure (x + q) ≤ irrMeasure x := by
  set a := q.num with ha
  set b := q.den with hb
  have hbpos : 0 < b := q.den_pos
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hbpos
  have hqeq : (q : ℝ) = (a : ℝ) / (b : ℝ) := by
    have := Rat.num_div_den q
    rw [ha, hb]
    exact_mod_cast this.symm
  apply irrMeasure_le_of_eps
  intro ν hν ε hεpos hεle
  simp only [apprSet, apprPairs, Set.mem_setOf_eq] at hν
  have hC : 0 < (b : ℝ) ^ (ν : ℝ) := Real.rpow_pos_of_pos hbR _
  have hinf : Set.Infinite {pq : ℤ × ℕ | 0 < pq.2 ∧
      |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < (b : ℝ) ^ (ν : ℝ) * (pq.2 : ℝ) ^ (-(ν : ℝ))} := by
    have hsubset : (fun pq : ℤ × ℕ => (pq.1 * b - a * pq.2, b * pq.2)) ''
        apprPairs (x + q) (ν : ℝ) ⊆
        {pq : ℤ × ℕ | 0 < pq.2 ∧
          |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < (b : ℝ) ^ (ν : ℝ) * (pq.2 : ℝ) ^ (-(ν : ℝ))} := by
      intro ⟨P, Q⟩ hmem
      simp only [Set.mem_image, Set.mem_setOf_eq, apprPairs] at hmem ⊢
      obtain ⟨⟨p, q'⟩, ⟨hq'pos, hine⟩, hPQ⟩ := hmem
      simp only [Prod.mk.injEq] at hPQ
      obtain ⟨rfl, rfl⟩ := hPQ
      have hq'R : 0 < (q' : ℝ) := by exact_mod_cast hq'pos
      refine ⟨by positivity, ?_⟩
      have heq : |x - ((p * b - a * q' : ℤ) : ℝ) / ((b * q' : ℕ) : ℝ)|
          = |(x + q) - (p : ℝ) / (q' : ℝ)| := by
        rw [hqeq]; push_cast; congr 1; field_simp; ring
      rw [heq]
      have hbound : (q' : ℝ) ^ (-(ν : ℝ))
          = (b : ℝ) ^ (ν : ℝ) * ((b * q' : ℕ) : ℝ) ^ (-(ν : ℝ)) := by
        have hb1 : ((b * q' : ℕ) : ℝ) ^ (-(ν : ℝ))
            = (b : ℝ) ^ (-(ν : ℝ)) * (q' : ℝ) ^ (-(ν : ℝ)) := by
          push_cast
          rw [mul_rpow (le_of_lt hbR) (le_of_lt hq'R)]
        rw [hb1]
        have hb2 : (b : ℝ) ^ (ν : ℝ) * (b : ℝ) ^ (-(ν : ℝ)) = 1 := by
          rw [← Real.rpow_add hbR]; simp
        rw [← mul_assoc, hb2, one_mul]
      rw [hbound] at hine
      exact hine
    have hinj : Set.InjOn (fun pq : ℤ × ℕ => (pq.1 * b - a * pq.2, b * pq.2))
        (apprPairs (x + q) (ν : ℝ)) := by
      intro ⟨p1, q1⟩ _ ⟨p2, q2⟩ _ h
      simp only [Prod.mk.injEq] at h ⊢
      have hq : q1 = q2 := Nat.eq_of_mul_eq_mul_left hbpos h.2
      have hp : p1 = p2 := by
        have h1 : p1 * b - a * q1 = p2 * b - a * q2 := h.1
        rw [hq] at h1
        have h2 : p1 * b = p2 * b := by linarith
        exact Int.eq_of_mul_eq_mul_right (by positivity : (b : ℤ) ≠ 0) h2
      exact ⟨hp, hq⟩
    exact Set.Infinite.mono hsubset ((Set.infinite_image_iff hinj).mpr hν)
  exact const_absorption_nn hC hinf ε hεpos hεle

/-- 平移不变性：μ(x+q)=μ(x)。（已证） -/
theorem irrMeasure_add_rat (x : ℝ) (q : ℚ) : irrMeasure (x + q) = irrMeasure x := by
  apply le_antisymm
  · exact add_rat_le x q
  · have h := add_rat_le (x + q) (-q)
    have hx : x + (q : ℝ) + ((-q : ℚ) : ℝ) = x := by push_cast; ring
    rw [hx] at h
    exact h


/-- 正整数缩放单向：μ(c·x) ≤ μ(x)，c>0 整数。 -/
lemma mul_nat_le (x : ℝ) (c : ℕ) (hc : 0 < c) : irrMeasure ((c : ℝ) * x) ≤ irrMeasure x := by
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  apply irrMeasure_le_of_eps
  intro ν hν ε hεpos hεle
  simp only [apprSet, apprPairs, Set.mem_setOf_eq] at hν
  -- |c x − p/q'| < q'^(−ν) ⇒ |x − p/(c q')| < c^(−1) q'^(−ν) = c^(ν−1) (c q')^(−ν)
  have hC : 0 < (c : ℝ) ^ ((ν : ℝ) - 1) := Real.rpow_pos_of_pos hcR _
  have hinf : Set.Infinite {pq : ℤ × ℕ | 0 < pq.2 ∧
      |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < (c : ℝ) ^ ((ν : ℝ) - 1) * (pq.2 : ℝ) ^ (-(ν : ℝ))} := by
    have hsubset : (fun pq : ℤ × ℕ => (pq.1, c * pq.2)) '' apprPairs ((c : ℝ) * x) (ν : ℝ) ⊆
        {pq : ℤ × ℕ | 0 < pq.2 ∧
          |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < (c : ℝ) ^ ((ν : ℝ) - 1) * (pq.2 : ℝ) ^ (-(ν : ℝ))} := by
      intro ⟨P, Q⟩ hmem
      simp only [Set.mem_image, Set.mem_setOf_eq, apprPairs] at hmem ⊢
      obtain ⟨⟨p, q'⟩, ⟨hq'pos, hine⟩, hPQ⟩ := hmem
      simp only [Prod.mk.injEq] at hPQ
      obtain ⟨rfl, rfl⟩ := hPQ
      have hq'R : 0 < (q' : ℝ) := by exact_mod_cast hq'pos
      refine ⟨by positivity, ?_⟩
      push_cast
      have hcne : (c : ℝ) ≠ 0 := ne_of_gt hcR
      have hqne : (q' : ℝ) ≠ 0 := ne_of_gt hq'R
      have heq : |x - (p : ℝ) / ((c : ℝ) * (q' : ℝ))|
          = |(c : ℝ) * x - (p : ℝ) / (q' : ℝ)| / (c : ℝ) := by
        have hinner : x - (p : ℝ) / ((c : ℝ) * (q' : ℝ))
            = ((c : ℝ) * x - (p : ℝ) / (q' : ℝ)) / (c : ℝ) := by
          field_simp
        rw [hinner, abs_div, abs_of_pos hcR]
      rw [heq]
      have hine' : |(c : ℝ) * x - (p : ℝ) / (q' : ℝ)| / (c : ℝ)
          < (q' : ℝ) ^ (-(ν : ℝ)) / (c : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_lt_mul_of_pos_right hine (inv_pos.mpr hcR)
      have hbound : (q' : ℝ) ^ (-(ν : ℝ)) / (c : ℝ)
          = (c : ℝ) ^ ((ν : ℝ) - 1) * ((c : ℝ) * (q' : ℝ)) ^ (-(ν : ℝ)) := by
        have h1 : (c : ℝ) ^ ((ν : ℝ) - 1) = (c : ℝ) ^ (ν : ℝ) / (c : ℝ) := by
          rw [Real.rpow_sub hcR, Real.rpow_one]
        rw [h1]
        have h2 : ((c : ℝ) * (q' : ℝ)) ^ (-(ν : ℝ))
            = (c : ℝ) ^ (-(ν : ℝ)) * (q' : ℝ) ^ (-(ν : ℝ)) := by
          rw [mul_rpow (le_of_lt hcR) (le_of_lt hq'R)]
        rw [h2]
        field_simp
        rw [← Real.rpow_add hcR]
        simp
      rw [hbound] at hine'
      exact hine'
    have hinj : Set.InjOn (fun pq : ℤ × ℕ => (pq.1, c * pq.2)) (apprPairs ((c : ℝ) * x) (ν : ℝ)) := by
      intro ⟨p1, q1⟩ _ ⟨p2, q2⟩ _ h
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, Nat.eq_of_mul_eq_mul_left hc h.2⟩
    exact Set.Infinite.mono hsubset ((Set.infinite_image_iff hinj).mpr hν)
  exact const_absorption_nn hC hinf ε hεpos hεle

/-- 反向整数缩放：μ(x) ≤ μ(c·x)，c>0。分子乘 c：|c x−cp/q| = c|x−p/q| < c·q^(−ν)。 -/
lemma mul_nat_le_rev (x : ℝ) (c : ℕ) (hc : 0 < c) : irrMeasure x ≤ irrMeasure ((c : ℝ) * x) := by
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  apply irrMeasure_le_of_eps
  intro ν hν ε hεpos hεle
  simp only [apprSet, apprPairs, Set.mem_setOf_eq] at hν
  have hinf : Set.Infinite {pq : ℤ × ℕ | 0 < pq.2 ∧
      |(c : ℝ) * x - (pq.1 : ℝ) / (pq.2 : ℝ)| < (c : ℝ) * (pq.2 : ℝ) ^ (-(ν : ℝ))} := by
    have hsubset : (fun pq : ℤ × ℕ => ((c : ℤ) * pq.1, pq.2)) '' apprPairs x (ν : ℝ) ⊆
        {pq : ℤ × ℕ | 0 < pq.2 ∧
          |(c : ℝ) * x - (pq.1 : ℝ) / (pq.2 : ℝ)| < (c : ℝ) * (pq.2 : ℝ) ^ (-(ν : ℝ))} := by
      intro ⟨P, Q⟩ hmem
      simp only [Set.mem_image, Set.mem_setOf_eq, apprPairs] at hmem ⊢
      obtain ⟨⟨p, q'⟩, ⟨hq'pos, hine⟩, hPQ⟩ := hmem
      simp only [Prod.mk.injEq] at hPQ
      obtain ⟨rfl, rfl⟩ := hPQ
      refine ⟨hq'pos, ?_⟩
      push_cast
      calc |(c : ℝ) * x - (c : ℝ) * (p : ℝ) / (q' : ℝ)|
          = (c : ℝ) * |x - (p : ℝ) / (q' : ℝ)| := by
            rw [show (c : ℝ) * x - (c : ℝ) * (p : ℝ) / (q' : ℝ)
                = (c : ℝ) * (x - (p : ℝ) / (q' : ℝ)) by ring]
            rw [abs_mul, abs_of_pos hcR]
        _ < (c : ℝ) * (q' : ℝ) ^ (-(ν : ℝ)) := mul_lt_mul_of_pos_left hine hcR
    have hinj : Set.InjOn (fun pq : ℤ × ℕ => ((c : ℤ) * pq.1, pq.2)) (apprPairs x (ν : ℝ)) := by
      intro ⟨p1, q1⟩ _ ⟨p2, q2⟩ _ h
      simp only [Prod.mk.injEq] at h ⊢
      have hp : (c : ℤ) * p1 = (c : ℤ) * p2 := h.1
      exact ⟨Int.eq_of_mul_eq_mul_left (by positivity : (c : ℤ) ≠ 0) hp, h.2⟩
    exact Set.Infinite.mono hsubset ((Set.infinite_image_iff hinj).mpr hν)
  exact const_absorption_nn hcR hinf ε hεpos hεle

/-- 整数缩放不变：μ(c·x)=μ(x)，c>0。 -/
lemma mul_nat_eq (x : ℝ) (c : ℕ) (hc : 0 < c) : irrMeasure ((c : ℝ) * x) = irrMeasure x :=
  le_antisymm (mul_nat_le x c hc) (mul_nat_le_rev x c hc)

/-- 缩放不变性：μ(qx)=μ(x)，q≠0。（已证） -/
theorem irrMeasure_mul_rat (x : ℝ) (q : ℚ) (hq : q ≠ 0) : irrMeasure (q * x) = irrMeasure x := by
  -- q = a/b，a≠0。μ(qx)=μ(a·(x/b))，用整数缩放不变 + 符号。
  set a := q.num with ha
  set b := q.den with hb
  have hbpos : 0 < b := q.den_pos
  have ha0 : a ≠ 0 := by
    intro h
    apply hq
    rw [Rat.num_eq_zero] at h
    exact h
  have hqeq : (q : ℝ) = (a : ℝ) / (b : ℝ) := by
    have := Rat.num_div_den q
    rw [ha, hb]; exact_mod_cast this.symm
  -- μ(qx) = μ(a · (x/b))；先证 μ(x/b)=μ(x)（整数缩放的逆）
  have hdiv : irrMeasure (x / (b : ℝ)) = irrMeasure x := by
    have h1 := mul_nat_eq (x / (b : ℝ)) b hbpos
    have harg : (b : ℝ) * (x / (b : ℝ)) = x := by field_simp
    rw [harg] at h1
    exact h1.symm
  -- 处理 a 的符号与绝对值
  have habs : irrMeasure ((a : ℝ) * (x / (b : ℝ))) = irrMeasure (x / (b : ℝ)) := by
    set n := Int.natAbs a with hn
    have hn0 : 0 < n := Int.natAbs_pos.mpr ha0
    have hnat : irrMeasure ((n : ℝ) * (x / (b : ℝ))) = irrMeasure (x / (b : ℝ)) :=
      mul_nat_eq (x / (b : ℝ)) n hn0
    by_cases ha_nonneg : 0 ≤ a
    · have ha_eq : (a : ℝ) = (n : ℝ) := by
        have h1 : (n : ℤ) = a := by
          simp only [hn]
          exact Int.natAbs_of_nonneg ha_nonneg
        have h2 : (a : ℝ) = (n : ℝ) := by
          have := congr_arg (Int.cast : ℤ → ℝ) h1.symm
          simpa using this
        exact h2
      rw [ha_eq]; exact hnat
    · have ha_neg : a < 0 := by linarith
      have ha_eq : (a : ℝ) = -(n : ℝ) := by
        have h1 : (n : ℤ) = -a := by
          simp only [hn]
          rw [← Int.natAbs_neg a]
          exact Int.natAbs_of_nonneg (by linarith)
        have h2 : (a : ℝ) = -(n : ℝ) := by
          have hz : (a : ℤ) = -(n : ℤ) := by linarith
          have := congr_arg (Int.cast : ℤ → ℝ) hz
          simpa using this
        exact h2
      have hneg : irrMeasure (-(n : ℝ) * (x / (b : ℝ))) = irrMeasure (x / (b : ℝ)) := by
        have harg : -(n : ℝ) * (x / (b : ℝ)) = -((n : ℝ) * (x / (b : ℝ))) := by ring
        rw [harg, irrMeasure_neg, hnat]
      rw [ha_eq]; exact hneg
  calc irrMeasure (q * x) = irrMeasure ((a : ℝ) / (b : ℝ) * x) := by rw [hqeq]
    _ = irrMeasure ((a : ℝ) * (x / (b : ℝ))) := by congr 1; ring
    _ = irrMeasure (x / (b : ℝ)) := habs
    _ = irrMeasure x := hdiv

/-- 分子无界：无理 y 的无穷逼近对集，对任意 N 存在 |p|>N。
    固定 p 时，|y−p/q|<q^(−ν)（ν>0）仅有限多 q（因 q→∞ 时左→|y|>0，右→0）。 -/
lemma apprPairs_num_unbounded {y : ℝ} (hy : Irrational y) {ν : ℝ} (hν : 0 < ν)
    (hinf : (apprPairs y ν).Infinite) (N : ℕ) :
    ∃ pq ∈ apprPairs y ν, N < Int.natAbs pq.1 := by
  by_contra h
  push_neg at h
  -- 所有 |p|≤N；对每个 p，q 有限
  have hfin : (apprPairs y ν).Finite := by
    have hy0 : y ≠ 0 := by
      intro h0
      apply hy
      rw [h0]
      exact ⟨0, by simp⟩
    have hyabs : 0 < |y| := abs_pos.mpr hy0
    -- 对每个 p，存在 Q_p 使 q>Q_p 时 |y−p/q|≥q^(−ν)
    -- 取 Q_p 使 q>Q_p ⇒ |p|/q < |y|/2 且 q^(−ν) < |y|/2
    have hbound : ∀ p : ℤ, ∃ Q : ℕ, ∀ q : ℕ, Q < q →
        ¬(0 < q ∧ |y - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν)) := by
      intro p
      -- 取 Q 大：q>Q ⇒ |p|/q < |y|/2 且 q^(-ν) < |y|/2
      obtain ⟨Q1, hQ1⟩ := exists_nat_gt (2 * |(p : ℝ)| / |y|)
      obtain ⟨Q2, hQ2⟩ := exists_nat_gt ((2 / |y|) ^ (1 / ν))
      use max Q1 Q2
      intro q hq hcontra
      have hq1 : Q1 < q := by omega
      have hq2 : Q2 < q := by omega
      have hqR : 0 < (q : ℝ) := by
        have : 0 < q := by omega
        exact_mod_cast this
      have h1 : |(p : ℝ)| / (q : ℝ) < |y| / 2 := by
        have hq1R : (Q1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
        have hbig : (2 * |(p : ℝ)| / |y| : ℝ) < (q : ℝ) := lt_trans hQ1 hq1R
        have hmid : |(p : ℝ)| < (q : ℝ) * |y| / 2 := by
          have hy' : 0 < |y| := hyabs
          field_simp at hbig ⊢
          nlinarith
        rw [div_lt_iff₀ hqR]
        nlinarith
      have h2 : (q : ℝ) ^ (-ν) < |y| / 2 := by
        have hq2R : (Q2 : ℝ) < (q : ℝ) := by exact_mod_cast hq2
        have hbig : ((2 / |y|) ^ (1 / ν) : ℝ) < (q : ℝ) := lt_trans hQ2 hq2R
        have hpow : (q : ℝ) ^ ν > 2 / |y| := by
          have hstep := Real.rpow_lt_rpow (by positivity) hbig hν
          have hinv : ((2 / |y|) ^ (1 / ν)) ^ ν = 2 / |y| := by
            rw [← Real.rpow_mul (by positivity), one_div,
              inv_mul_cancel₀ (ne_of_gt hν), Real.rpow_one]
          nlinarith
        have hneg : (q : ℝ) ^ (-ν) = 1 / (q : ℝ) ^ ν := by
          rw [Real.rpow_neg (le_of_lt hqR)]
          field_simp
        rw [hneg]
        have hpos : 0 < (q : ℝ) ^ ν := Real.rpow_pos_of_pos hqR _
        rw [div_lt_iff₀ hpos]
        have hy' : 0 < |y| := hyabs
        have := hpow
        field_simp at this ⊢
        nlinarith
      have htri : |y| - |(p : ℝ)| / (q : ℝ) ≤ |y - (p : ℝ) / (q : ℝ)| := by
        have := abs_sub_abs_le_abs_sub y ((p : ℝ) / (q : ℝ))
        have habs : |(p : ℝ) / (q : ℝ)| = |(p : ℝ)| / (q : ℝ) := by
          rw [abs_div, abs_of_pos hqR]
        nlinarith
      have : |y| / 2 < |y - (p : ℝ) / (q : ℝ)| := by nlinarith
      nlinarith [hcontra.2]
    -- 有限并
    have hsub : apprPairs y ν ⊆
        ⋃ p ∈ {p : ℤ | Int.natAbs p ≤ N},
          (fun q : ℕ => (p, q)) '' {q : ℕ | 0 < q ∧ |y - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν)} := by
      intro ⟨p, q⟩ hpq
      simp only [apprPairs, Set.mem_setOf_eq] at hpq
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
      refine ⟨p, h (p, q) hpq, q, hpq, rfl⟩
    refine Set.Finite.subset ?_ hsub
    apply Set.Finite.biUnion
    · -- {p : |p|≤N} 有限
      have : {p : ℤ | Int.natAbs p ≤ N} ⊆ Set.Icc (-(N : ℤ)) (N : ℤ) := by
        intro p hp
        simp only [Set.mem_setOf_eq, Set.mem_Icc] at hp ⊢
        have hN : (Int.natAbs p : ℤ) ≤ N := by exact_mod_cast hp
        rcases Int.natAbs_eq p with h | h
        · have hp' : p = (Int.natAbs p : ℤ) := by linarith
          rw [hp']; constructor <;> linarith [(by positivity : 0 ≤ (Int.natAbs p : ℤ))]
        · have hp' : p = -(Int.natAbs p : ℤ) := by linarith
          rw [hp']; constructor <;> linarith [(by positivity : 0 ≤ (Int.natAbs p : ℤ))]
      exact Set.Finite.subset (Set.finite_Icc _ _) this
    · intro p _
      -- {q : ...} 有限（由 hbound）
      obtain ⟨Q, hQ⟩ := hbound p
      have hqsub : {q : ℕ | 0 < q ∧ |y - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν)} ⊆
          Set.Iic Q := by
        intro q hq
        simp only [Set.mem_setOf_eq, Set.mem_Iic] at hq ⊢
        by_contra hqQ
        push Not at hqQ
        exact hQ q hqQ hq
      exact ((Set.finite_Iic Q).subset hqsub).image _
  exact hinf hfin

/-- 倒数逼近代数恒等式：|x − q/p| = |x|·(q/|p|)·|x⁻¹ − p/q|（x≠0, p≠0, q>0）。 -/
lemma abs_inv_sub_eq (x : ℝ) (hx0 : x ≠ 0) (p : ℤ) (hp0 : p ≠ 0) (q : ℕ) (hq0 : 0 < q) :
    |x - (q : ℝ) / (p : ℝ)| = |x| * ((q : ℝ) / |(p : ℝ)|) * |x⁻¹ - (p : ℝ) / (q : ℝ)| := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq0)
  have h1 : x - (q : ℝ) / (p : ℝ) = (x * (p : ℝ) - (q : ℝ)) / (p : ℝ) := by
    field_simp
  have h2 : x⁻¹ - (p : ℝ) / (q : ℝ) = ((q : ℝ) - x * (p : ℝ)) / (x * (q : ℝ)) := by
    field_simp
  rw [h1, h2]
  have habs1 : |(x * (p : ℝ) - (q : ℝ)) / (p : ℝ)| = |x * (p : ℝ) - (q : ℝ)| / |(p : ℝ)| := by
    rw [abs_div]
  have habs2 : |((q : ℝ) - x * (p : ℝ)) / (x * (q : ℝ))|
      = |(q : ℝ) - x * (p : ℝ)| / (|x| * (q : ℝ)) := by
    rw [abs_div, abs_mul, abs_of_pos (by exact_mod_cast hq0 : 0 < (q : ℝ))]
  rw [habs1, habs2]
  have hneg : |x * (p : ℝ) - (q : ℝ)| = |(q : ℝ) - x * (p : ℝ)| := by
    rw [← abs_neg]; congr 1; ring
  rw [hneg]
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq0
  field_simp

/-- 符号一致性：若 |y⁻¹ − p/q| < |y⁻¹|/2 且 q>0，则 p≠0 且 p 与 y⁻¹ 同号。 -/
lemma sign_coherent (y : ℝ) (hy0 : y ≠ 0) (p : ℤ) (q : ℕ) (hq0 : 0 < q)
    (h : |y⁻¹ - (p : ℝ) / (q : ℝ)| < |y⁻¹| / 2) :
    p ≠ 0 ∧ (0 < (p : ℝ) ↔ 0 < y⁻¹) := by
  have hyinv0 : y⁻¹ ≠ 0 := inv_ne_zero hy0
  have hyinv_abs : 0 < |y⁻¹| := abs_pos.mpr hyinv0
  have hpq_abs : |(p : ℝ) / (q : ℝ)| > |y⁻¹| / 2 := by
    have := abs_sub_abs_le_abs_sub y⁻¹ ((p : ℝ) / (q : ℝ))
    have h' : |y⁻¹ - (p : ℝ) / (q : ℝ)| < |y⁻¹| / 2 := h
    nlinarith
  have hp_ne : p ≠ 0 := by
    intro h0
    have hpq0 : (p : ℝ) / (q : ℝ) = 0 := by rw [h0]; simp
    rw [hpq0] at hpq_abs
    simp at hpq_abs
    have hpos : 0 < |y|⁻¹ := inv_pos.mpr (abs_pos.mpr hy0)
    linarith
  constructor
  · exact hp_ne
  · have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq0
    constructor
    · intro hp
      by_contra hyinv_neg
      push Not at hyinv_neg
      have hpq_pos : 0 < (p : ℝ) / (q : ℝ) := div_pos hp hqpos
      have hpq_gt : (p : ℝ) / (q : ℝ) > |y⁻¹| / 2 := by
        have habs : |(p : ℝ) / (q : ℝ)| = (p : ℝ) / (q : ℝ) := abs_of_pos hpq_pos
        nlinarith [hpq_abs]
      have hyinv_le : y⁻¹ ≤ 0 := hyinv_neg
      have hdiff : (p : ℝ) / (q : ℝ) - y⁻¹ ≥ (p : ℝ) / (q : ℝ) := by linarith
      have hnonneg : 0 ≤ (p : ℝ) / (q : ℝ) - y⁻¹ := by linarith [hdiff, hpq_pos]
      have habs_ge : |(p : ℝ) / (q : ℝ) - y⁻¹| ≥ (p : ℝ) / (q : ℝ) := by
        rw [abs_of_nonneg hnonneg]
        exact hdiff
      have hclose : |(p : ℝ) / (q : ℝ) - y⁻¹| < |y⁻¹| / 2 := by
        rw [abs_sub_comm]; exact h
      nlinarith
    · intro hyinv
      by_contra hp_neg
      push Not at hp_neg
      have hpq_nonpos : (p : ℝ) / (q : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hp_neg (le_of_lt hqpos)
      have hdiff : y⁻¹ - (p : ℝ) / (q : ℝ) ≥ y⁻¹ := by linarith [hpq_nonpos]
      have hnonneg : 0 ≤ y⁻¹ - (p : ℝ) / (q : ℝ) := by linarith [hdiff, hyinv]
      have habs_ge : |y⁻¹ - (p : ℝ) / (q : ℝ)| ≥ y⁻¹ := by
        rw [abs_of_nonneg hnonneg]
        exact hdiff
      have hyinv_eq : y⁻¹ = |y⁻¹| := (abs_of_pos hyinv).symm
      nlinarith [h, hyinv_abs]

set_option maxHeartbeats 1600000 in
/-- 取倒数不变性：μ(x⁻¹)=μ(x)。（已证：互换双射 (p,q)↦(q·sign p, |p|) + 常数吸收） -/
theorem irrMeasure_inv (x : ℝ) (hx : Irrational x) : irrMeasure (x⁻¹) = irrMeasure x := by
  have hx0 : x ≠ 0 := by
    intro h0; apply hx; rw [h0]; exact ⟨0, by simp⟩
  have hxinv_irr : Irrational x⁻¹ := by
    intro h
    simp only [Irrational, Set.mem_range, not_forall, not_not] at h
    obtain ⟨q, hq⟩ := h
    have hqR : (q : ℝ) = x⁻¹ := by exact_mod_cast hq
    have hq0 : q ≠ 0 := by
      intro h0
      have : (q : ℝ) = 0 := by rw [h0]; simp
      have : x⁻¹ = 0 := by linarith [hqR]
      exact (inv_ne_zero hx0) this
    apply hx
    refine ⟨q⁻¹, ?_⟩
    have h2 : (q : ℝ) * x = 1 := by
      have := congr_arg (fun t : ℝ => t * x) hqR
      have : x⁻¹ * x = 1 := by field_simp
      nlinarith
    have hqR0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
    have h3 : x = 1 / (q : ℝ) := by field_simp at h2 ⊢; nlinarith
    have h4 : ((q⁻¹ : ℚ) : ℝ) = x := by
      have : ((q⁻¹ : ℚ) : ℝ) = 1 / (q : ℝ) := by push_cast; field_simp
      linarith [h3]
    exact_mod_cast h4
  have hdir : ∀ y : ℝ, Irrational y → irrMeasure (y⁻¹) ≤ irrMeasure y := by
    intro y hy
    have hy0 : y ≠ 0 := by
      intro h0; apply hy; rw [h0]; exact ⟨0, by simp⟩
    have hyR : 0 < |y| := abs_pos.mpr hy0
    have hyinv_abs : 0 < |y⁻¹| := abs_pos.mpr (inv_ne_zero hy0)
    apply irrMeasure_le_of_eps
    intro ν hν ε hεpos hεle
    simp only [apprSet, apprPairs, Set.mem_setOf_eq] at hν
    have hνpos : 0 < (ν : ℝ) := by
      by_cases h0 : ν = 0
      · have hε0 : ε ≤ 0 := by simpa [h0] using hεle
        have hε0' : ε = 0 := le_antisymm hε0 bot_le
        exact absurd hε0' (ne_of_gt hεpos)
      · have hνpos' : 0 < ν := lt_of_le_of_ne bot_le (Ne.symm h0)
        exact_mod_cast hνpos'
    obtain ⟨Q0, hQ0⟩ : ∃ Q0 : ℕ, ∀ q : ℕ, Q0 < q → (q : ℝ) ^ (-(ν : ℝ)) < |y⁻¹| / 2 := by
      obtain ⟨Q0, hQ0⟩ := exists_nat_gt ((2 / |y⁻¹|) ^ (1 / (ν : ℝ)))
      refine ⟨Q0, ?_⟩
      intro q hq
      have hqR : (Q0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      have hbig : ((2 / |y⁻¹|) ^ (1 / (ν : ℝ)) : ℝ) < (q : ℝ) := lt_trans hQ0 hqR
      have hqpos : 0 < (q : ℝ) := by
        have : 0 < (2 / |y⁻¹| : ℝ) ^ (1 / (ν : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
        linarith
      have hpow : (q : ℝ) ^ (ν : ℝ) > 2 / |y⁻¹| := by
        have := Real.rpow_lt_rpow (by positivity) hbig hνpos
        have hinv : ((2 / |y⁻¹|) ^ (1 / (ν : ℝ))) ^ (ν : ℝ) = 2 / |y⁻¹| := by
          rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ (ne_of_gt hνpos), Real.rpow_one]
        nlinarith
      have hneg : (q : ℝ) ^ (-(ν : ℝ)) = 1 / (q : ℝ) ^ (ν : ℝ) := by
        rw [Real.rpow_neg (le_of_lt hqpos)]; field_simp
      rw [hneg]
      have hpos : 0 < (q : ℝ) ^ (ν : ℝ) := Real.rpow_pos_of_pos hqpos _
      rw [div_lt_iff₀ hpos]
      have := hpow
      field_simp at this ⊢
      nlinarith
    have hinf_big : {pq : ℤ × ℕ | pq ∈ apprPairs y⁻¹ (ν : ℝ) ∧ Q0 < pq.2}.Infinite := by
      have hfin : {pq : ℤ × ℕ | pq ∈ apprPairs y⁻¹ (ν : ℝ) ∧ pq.2 ≤ Q0}.Finite := by
        have hsub : {pq : ℤ × ℕ | pq ∈ apprPairs y⁻¹ (ν : ℝ) ∧ pq.2 ≤ Q0} ⊆
            ⋃ q ∈ {q : ℕ | q ≤ Q0}, (fun p : ℤ => (p, q)) ''
              Set.Icc ⌊(y⁻¹ - (q : ℝ) ^ (-(ν : ℝ))) * (q : ℝ)⌋
                ⌈(y⁻¹ + (q : ℝ) ^ (-(ν : ℝ))) * (q : ℝ)⌉ := by
          intro ⟨p, q⟩ hpq
          simp only [Set.mem_setOf_eq, apprPairs] at hpq
          simp only [Set.mem_iUnion, Set.mem_image, Set.mem_Icc, Set.mem_setOf_eq]
          refine ⟨q, hpq.2, p, ?_, rfl⟩
          have hqpos : 0 < (q : ℝ) := by exact_mod_cast hpq.1.1
          rw [abs_lt] at hpq
          constructor
          · have : (y⁻¹ - (q : ℝ) ^ (-(ν : ℝ))) * (q : ℝ) < (p : ℝ) := by
              have := hpq.1.2.2
              have : y⁻¹ - (q : ℝ) ^ (-(ν : ℝ)) < (p : ℝ) / (q : ℝ) := by linarith
              rwa [lt_div_iff₀ hqpos] at this
            calc ⌊(y⁻¹ - (q : ℝ) ^ (-(ν : ℝ))) * (q : ℝ)⌋ ≤ ⌊(p : ℝ)⌋ :=
                Int.floor_mono (le_of_lt this)
              _ = p := Int.floor_intCast p
          · have : (p : ℝ) < (y⁻¹ + (q : ℝ) ^ (-(ν : ℝ))) * (q : ℝ) := by
              have := hpq.1.2.1
              have : (p : ℝ) / (q : ℝ) < y⁻¹ + (q : ℝ) ^ (-(ν : ℝ)) := by linarith
              rwa [div_lt_iff₀ hqpos] at this
            calc (p : ℤ) = ⌈(p : ℝ)⌉ := (Int.ceil_intCast p).symm
              _ ≤ ⌈(y⁻¹ + (q : ℝ) ^ (-(ν : ℝ))) * (q : ℝ)⌉ := Int.ceil_mono (le_of_lt this)
        refine Set.Finite.subset ?_ hsub
        apply Set.Finite.biUnion (Set.finite_le_nat Q0)
        intro q _
        exact (Set.finite_Icc _ _).image _
      have hunion : apprPairs y⁻¹ (ν : ℝ) ⊆
          {pq | pq ∈ apprPairs y⁻¹ (ν : ℝ) ∧ Q0 < pq.2} ∪
          {pq | pq ∈ apprPairs y⁻¹ (ν : ℝ) ∧ pq.2 ≤ Q0} := by
        intro ⟨p, q⟩ hpq
        simp only [Set.mem_setOf_eq, Set.mem_union]
        by_cases hq : Q0 < q
        · exact Or.inl ⟨hpq, hq⟩
        · exact Or.inr ⟨hpq, le_of_not_gt hq⟩
      by_contra hfin'
      have : (apprPairs y⁻¹ (ν : ℝ)).Finite :=
        Set.Finite.subset (Set.Finite.union (Set.not_infinite.mp hfin') hfin) hunion
      exact hν this
    set C := 2 * |y| ^ 2 * (|y⁻¹| + 1) ^ (ν : ℝ) with hCdef
    have hCpos : 0 < C := by
      apply mul_pos (mul_pos (by norm_num) (pow_pos hyR 2))
      exact Real.rpow_pos_of_pos (by positivity) _
    have hinf_img : Set.Infinite {pq : ℤ × ℕ | 0 < pq.2 ∧
        |y - (pq.1 : ℝ) / (pq.2 : ℝ)| < C * (pq.2 : ℝ) ^ (-(ν : ℝ))} := by
      -- 映射 (p,q) ↦ (q·sign p, |p|)；(q·sign p)/|p| = q/p
      have hsubset : (fun pq : ℤ × ℕ => ((pq.2 : ℤ) * Int.sign pq.1, Int.natAbs pq.1)) ''
          {pq : ℤ × ℕ | pq ∈ apprPairs y⁻¹ (ν : ℝ) ∧ Q0 < pq.2} ⊆
          {pq : ℤ × ℕ | 0 < pq.2 ∧
            |y - (pq.1 : ℝ) / (pq.2 : ℝ)| < C * (pq.2 : ℝ) ^ (-(ν : ℝ))} := by
        intro ⟨P, Q⟩ hmem
        simp only [Set.mem_image, Set.mem_setOf_eq, apprPairs] at hmem ⊢
        obtain ⟨⟨p, q⟩, ⟨⟨hqpos, hine⟩, hqbig⟩, hPQ⟩ := hmem
        simp only [Prod.mk.injEq] at hPQ
        obtain ⟨rfl, rfl⟩ := hPQ
        have hqR : 0 < (q : ℝ) := by exact_mod_cast hqpos
        have hsmall : (q : ℝ) ^ (-(ν : ℝ)) < |y⁻¹| / 2 := hQ0 q hqbig
        have hclose : |y⁻¹ - (p : ℝ) / (q : ℝ)| < |y⁻¹| / 2 := lt_trans hine hsmall
        have hsign := sign_coherent y hy0 p q hqpos hclose
        have hp_ne : p ≠ 0 := hsign.1
        have hp_abs : 0 < Int.natAbs p := Int.natAbs_pos.mpr hp_ne
        refine ⟨by exact_mod_cast hp_abs, ?_⟩
        have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp_ne
        -- (q·sign p)/|p| = q/p
        have hcast : (((q : ℤ) * Int.sign p : ℤ) : ℝ) / (Int.natAbs p : ℝ) = (q : ℝ) / (p : ℝ) := by
          have hsign_mulR : (Int.sign p : ℝ) * (Int.natAbs p : ℝ) = (p : ℝ) := by
            have h := Int.sign_mul_natAbs p
            have hc := congr_arg (Int.cast : ℤ → ℝ) h
            simpa [Int.cast_mul] using hc
          have hnp : (Int.natAbs p : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt hp_abs)
          have hsign_div : (Int.sign p : ℝ) = (p : ℝ) / (Int.natAbs p : ℝ) := by
            field_simp [hnp]
            linarith [hsign_mulR]
          have hsq : (Int.natAbs p : ℝ) ^ 2 = (p : ℝ) ^ 2 := by
            have : (Int.natAbs p : ℝ) = |(p : ℝ)| := by simp
            rw [this, sq_abs]
          push_cast
          rw [hsign_div]
          field_simp
          nlinarith [hsq]
        rw [hcast]
        have hid := abs_inv_sub_eq y hy0 p hp_ne q hqpos
        rw [hid]
        have hpq_abs : |(p : ℝ)| / (q : ℝ) > |y⁻¹| / 2 := by
          have h1 : |(p : ℝ) / (q : ℝ)| = |(p : ℝ)| / (q : ℝ) := by
            rw [abs_div, abs_of_pos hqR]
          have := abs_sub_abs_le_abs_sub y⁻¹ ((p : ℝ) / (q : ℝ))
          nlinarith
        have h_ratio : (q : ℝ) / |(p : ℝ)| < 2 * |y| := by
          have hinv : |y⁻¹| = |y|⁻¹ := by rw [abs_inv]
          have h1 : |(p : ℝ)| / (q : ℝ) > |y|⁻¹ / 2 := by nlinarith
          have hp_abs_pos : 0 < |(p : ℝ)| := abs_pos.mpr hpR
          have : (q : ℝ) / |(p : ℝ)| < 2 * |y| := by
            have h2 : 0 < (q : ℝ) := hqR
            have h3 : 0 < |(p : ℝ)| := hp_abs_pos
            have h4 : 0 < |y| := hyR
            rw [div_lt_iff₀ h3]
            have h1' : |y|⁻¹ / 2 < |(p : ℝ)| / (q : ℝ) := h1
            field_simp at h1' ⊢
            nlinarith
          exact this
        have h1 : |y| * ((q : ℝ) / |(p : ℝ)|) * |y⁻¹ - (p : ℝ) / (q : ℝ)|
            < |y| * (2 * |y|) * (q : ℝ) ^ (-(ν : ℝ)) := by
          have h2 : (q : ℝ) / |(p : ℝ)| < 2 * |y| := h_ratio
          have h3 : |y⁻¹ - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-(ν : ℝ)) := hine
          calc |y| * ((q : ℝ) / |(p : ℝ)|) * |y⁻¹ - (p : ℝ) / (q : ℝ)|
              ≤ |y| * (2 * |y|) * |y⁻¹ - (p : ℝ) / (q : ℝ)| := by gcongr
            _ < |y| * (2 * |y|) * (q : ℝ) ^ (-(ν : ℝ)) := by gcongr
        -- q/|p| > 1/(|y⁻¹|+1)（因 |p/q| < |y⁻¹|+1），故 (q/|p|)^(−ν) ≤ (|y⁻¹|+1)^ν
        have hpq_upper : |(p : ℝ)| / (q : ℝ) < |y⁻¹| + 1 := by
          have hqpow_le : (q : ℝ) ^ (-(ν : ℝ)) ≤ 1 := by
            apply Real.rpow_le_one_of_one_le_of_nonpos
            · exact_mod_cast (Nat.succ_le_of_lt hqpos)
            · linarith
          have htri := abs_sub_abs_le_abs_sub ((p : ℝ) / (q : ℝ)) y⁻¹
          have hine' : |(p : ℝ) / (q : ℝ) - y⁻¹| < (q : ℝ) ^ (-(ν : ℝ)) := by
            rw [abs_sub_comm]; exact hine
          have h1 : |(p : ℝ) / (q : ℝ)| < |y⁻¹| + 1 := by nlinarith
          have h2 : |(p : ℝ) / (q : ℝ)| = |(p : ℝ)| / (q : ℝ) := by
            rw [abs_div, abs_of_pos hqR]
          nlinarith
        have h_ratio_lower : (1 : ℝ) / (|y⁻¹| + 1) < (q : ℝ) / |(p : ℝ)| := by
          have hp_abs_pos : 0 < |(p : ℝ)| := abs_pos.mpr hpR
          have h1 : |(p : ℝ)| / (q : ℝ) < |y⁻¹| + 1 := hpq_upper
          have h2 : 0 < (q : ℝ) := hqR
          have h3 : 0 < |y⁻¹| + 1 := by positivity
          rw [lt_div_iff₀ hp_abs_pos]
          field_simp at h1 ⊢
          nlinarith
        have h2 : (q : ℝ) ^ (-(ν : ℝ)) ≤ (|y⁻¹| + 1) ^ (ν : ℝ) * (Int.natAbs p : ℝ) ^ (-(ν : ℝ)) := by
          have habs_p : (Int.natAbs p : ℝ) = |(p : ℝ)| := by simp
          have hp_abs_pos : 0 < |(p : ℝ)| := abs_pos.mpr hpR
          have hqp : ((q : ℝ) / |(p : ℝ)|) * |(p : ℝ)| = (q : ℝ) := by
            field_simp
          have hqpow : (q : ℝ) ^ (-(ν : ℝ))
              = ((q : ℝ) / |(p : ℝ)|) ^ (-(ν : ℝ)) * |(p : ℝ)| ^ (-(ν : ℝ)) := by
            conv_lhs => rw [← hqp]
            have hq_nonneg : 0 ≤ (q : ℝ) / |(p : ℝ)| :=
              div_nonneg (by exact_mod_cast (Nat.zero_le q)) (le_of_lt hp_abs_pos)
            exact mul_rpow (z := -(ν : ℝ)) hq_nonneg (le_of_lt hp_abs_pos)
          rw [hqpow, ← habs_p]
          have h_ratio_pow : ((q : ℝ) / |(p : ℝ)|) ^ (-(ν : ℝ)) ≤ (|y⁻¹| + 1) ^ (ν : ℝ) := by
            have hbase : (1 : ℝ) / (|y⁻¹| + 1) ≤ (q : ℝ) / |(p : ℝ)| := le_of_lt h_ratio_lower
            have hpow : ((1 : ℝ) / (|y⁻¹| + 1)) ^ (ν : ℝ) ≤ ((q : ℝ) / |(p : ℝ)|) ^ (ν : ℝ) :=
              Real.rpow_le_rpow (by positivity) hbase (by linarith)
            have h1 : ((q : ℝ) / |(p : ℝ)|) ^ (-(ν : ℝ)) = 1 / ((q : ℝ) / |(p : ℝ)|) ^ (ν : ℝ) := by
              rw [Real.rpow_neg (by positivity), one_div]
            rw [h1]
            have h2 : ((1 : ℝ) / (|y⁻¹| + 1)) ^ (ν : ℝ) = 1 / (|y⁻¹| + 1) ^ (ν : ℝ) := by
              rw [one_div, Real.inv_rpow (by positivity), one_div]
            have h3 : (|y⁻¹| + 1 : ℝ) ^ (ν : ℝ) = 1 / ((1 : ℝ) / (|y⁻¹| + 1)) ^ (ν : ℝ) := by
              rw [h2]; field_simp
            rw [h3]
            apply one_div_le_one_div_of_le (by positivity) hpow
          have hnonneg : 0 ≤ (Int.natAbs p : ℝ) ^ (-(ν : ℝ)) := by positivity
          have hstep := mul_le_mul_of_nonneg_right h_ratio_pow hnonneg
          simpa [habs_p] using hstep
        calc |y| * ((q : ℝ) / |(p : ℝ)|) * |y⁻¹ - (p : ℝ) / (q : ℝ)|
            < |y| * (2 * |y|) * (q : ℝ) ^ (-(ν : ℝ)) := h1
          _ ≤ |y| * (2 * |y|) * ((|y⁻¹| + 1) ^ (ν : ℝ) * (Int.natAbs p : ℝ) ^ (-(ν : ℝ))) := by gcongr
          _ = C * (Int.natAbs p : ℝ) ^ (-(ν : ℝ)) := by simp only [hCdef]; ring
      have hinj : Set.InjOn (fun pq : ℤ × ℕ => ((pq.2 : ℤ) * Int.sign pq.1, Int.natAbs pq.1))
          {pq : ℤ × ℕ | pq ∈ apprPairs y⁻¹ (ν : ℝ) ∧ Q0 < pq.2} := by
        intro ⟨p1, q1⟩ h1 ⟨p2, q2⟩ h2 heq
        simp only [Prod.mk.injEq] at heq ⊢
        have hnum : (q1 : ℤ) * Int.sign p1 = (q2 : ℤ) * Int.sign p2 := heq.1
        have hden : Int.natAbs p1 = Int.natAbs p2 := heq.2
        have hs1 := sign_coherent y hy0 p1 q1 h1.1.1 (lt_trans h1.1.2 (hQ0 q1 h1.2))
        have hs2 := sign_coherent y hy0 p2 q2 h2.1.1 (lt_trans h2.1.2 (hQ0 q2 h2.2))
        have hq : q1 = q2 := by
          have h1' : Int.natAbs ((q1 : ℤ) * Int.sign p1) = q1 := by
            rw [Int.natAbs_mul, Int.natAbs_sign, Int.natAbs_natCast]
            simp [hs1.1]
          have h2' : Int.natAbs ((q2 : ℤ) * Int.sign p2) = q2 := by
            rw [Int.natAbs_mul, Int.natAbs_sign, Int.natAbs_natCast]
            simp [hs2.1]
          have := congr_arg Int.natAbs hnum
          nlinarith
        have hp_sign : Int.sign p1 = Int.sign p2 := by
          have hqne1 : (q1 : ℤ) ≠ 0 := by
            exact_mod_cast (ne_of_gt h1.1.1)
          have hnum' : (q1 : ℤ) * Int.sign p1 = (q1 : ℤ) * Int.sign p2 := by
            have := hnum
            rw [← hq] at this
            exact this
          exact Int.eq_of_mul_eq_mul_left hqne1 hnum'
        have hp : p1 = p2 := by
          have h1' : p1 = Int.sign p1 * Int.natAbs p1 := (Int.sign_mul_natAbs p1).symm
          have h2' : p2 = Int.sign p2 * Int.natAbs p2 := (Int.sign_mul_natAbs p2).symm
          rw [h1', h2', hp_sign, hden]
        exact ⟨hp, hq⟩
      exact Set.Infinite.mono hsubset ((Set.infinite_image_iff hinj).mpr hinf_big)
    exact const_absorption_nn hCpos hinf_img ε hεpos hεle
  have h1 := hdir x hx
  have h2 := hdir x⁻¹ hxinv_irr
  rw [inv_inv x] at h2
  exact le_antisymm h1 h2

/-- 定理 A 和情形：e+π 有理 ⇒ μ(π)=2。（待填） -/
theorem theoremA_sum (h : ∃ q : ℚ, exp 1 + π = q) : irrMeasure π = 2 := by
  obtain ⟨q, hq⟩ := h
  have hpi : π = (-exp 1) + (q : ℝ) := by
    have : (exp 1 : ℝ) + π = (q : ℝ) := by exact_mod_cast hq
    linarith
  rw [hpi, irrMeasure_add_rat, irrMeasure_neg, mu_e_eq_two]

/-- 定理 A 差情形：e−π 有理 ⇒ μ(π)=2。（待填） -/
theorem theoremA_diff (h : ∃ q : ℚ, exp 1 - π = q) : irrMeasure π = 2 := by
  obtain ⟨q, hq⟩ := h
  have hpi : π = exp 1 + ((-q : ℚ) : ℝ) := by
    have : (exp 1 : ℝ) - π = (q : ℝ) := by exact_mod_cast hq
    have : π = exp 1 - (q : ℝ) := by linarith
    rw [this]; push_cast; ring
  rw [hpi, irrMeasure_add_rat, mu_e_eq_two]

/-- 定理 A 积情形：eπ 有理 ⇒ μ(π)=2。（依赖 inv） -/
theorem theoremA_prod (h : ∃ q : ℚ, exp 1 * π = q) : irrMeasure π = 2 := by
  obtain ⟨q, hq⟩ := h
  have hq0 : q ≠ 0 := by
    intro h0
    have h1 : (exp 1 : ℝ) * π = 0 := by rw [hq, h0]; simp
    have : (exp 1 : ℝ) = 0 ∨ π = 0 := mul_eq_zero.mp h1
    rcases this with h | h
    · exact (ne_of_gt (exp_pos 1)) h
    · exact (ne_of_gt pi_pos) h
  have hpi : π = (q : ℝ) * (exp 1)⁻¹ := by
    have h1 : (exp 1 : ℝ) * π = (q : ℝ) := by exact_mod_cast hq
    have he0 : (exp 1 : ℝ) ≠ 0 := ne_of_gt (exp_pos 1)
    field_simp at h1 ⊢
    linarith
  rw [hpi]
  have hmul := irrMeasure_mul_rat ((exp 1)⁻¹) q hq0
  rw [hmul]
  have hinv := irrMeasure_inv (exp 1) (Transcendental.irrational e_transcendental)
  rw [hinv, mu_e_eq_two]

/-- 定理 A 商情形：e/π 有理 ⇒ μ(π)=2。（已证） -/
theorem theoremA_quot (h : ∃ q : ℚ, exp 1 / π = q) : irrMeasure π = 2 := by
  obtain ⟨q, hq⟩ := h
  have hq0 : q ≠ 0 := by
    intro h0
    have h1 : (exp 1 : ℝ) / π = 0 := by rw [hq, h0]; simp
    have h2 : (exp 1 : ℝ) = 0 := by
      have := div_eq_zero_iff.mp h1
      rcases this with h | h
      · exact h
      · exact (ne_of_gt pi_pos h).elim
    exact (ne_of_gt (exp_pos 1)) h2
  have hpi : π = (q⁻¹ : ℚ) * exp 1 := by
    have h1 : (exp 1 : ℝ) / π = (q : ℝ) := by exact_mod_cast hq
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
    have h2 : (exp 1 : ℝ) = (q : ℝ) * π := by
      have := (div_eq_iff (ne_of_gt pi_pos)).mp h1
      linarith
    have h3 : π = (exp 1 : ℝ) / (q : ℝ) := by
      field_simp at h2 ⊢
      linarith
    rw [h3]
    push_cast
    ring
  rw [hpi]
  have hmul := irrMeasure_mul_rat (exp 1) (q⁻¹) (by simpa using hq0)
  rw [hmul, mu_e_eq_two]
