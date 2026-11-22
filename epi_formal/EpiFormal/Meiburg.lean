import Mathlib
import EpiFormal.Measure

/-!
# F2：Meiburg 判据形式化（μ(π)<5/2 ⇒ Flint Hills 收敛）

策略：H′ 只需 μ(π)=2 特例。用二进块计数直接论证（比完整 Meiburg 精细划分更可行）：
1. 好逼近对集有限性（μ 定义直接推论）；
2. sin 下界 → 项上界（复用 FlintHills.abs_sin_int_le）；
3. 二进块计数引理（μ=2 ⇒ 块内好逼近 O(2^{kε})）；
4. 分块求和收敛（好/坏项拆分，p-级数）；
5. 接线 meiburg_criterion 为定理。

依据：Meiburg 2022 (arXiv:2208.13356)，证明结构第八九轮已完整人工核验。
-/

open Real Set Filter

/-- 基础引理：若 μ(x) ≤ M（M 有限），则对任何 ν>M，ν-好逼近对集有限。
    μ 定义直接推论：无穷多 ν-逼近 ⇒ ν∈S(x) ⇒ μ(x)≥ν>M，矛盾。 -/
lemma apprPairs_finite_of_mu_lt {x : ℝ} {M : NNReal} (hM : irrMeasure x ≤ (M : ENNReal))
    {ν : ℝ} (hν : (M : ℝ) < ν) : (apprPairs x ν).Finite := by
  by_contra hinf
  have hinf' : (apprPairs x ν).Infinite := not_finite.mp hinf
  have hνpos : 0 < ν := by
    have : (0 : ℝ) ≤ (M : ℝ) := NNReal.coe_nonneg M
    linarith
  set ν' : NNReal := ⟨ν, le_of_lt hνpos⟩ with hν'def
  have hν'coe : (ν' : ℝ) = ν := rfl
  have hmem : ν' ∈ apprSet x := by
    simp only [apprSet, Set.mem_setOf_eq]
    convert hinf' using 1
    simp [hν'coe]
  have hle : (ν' : ENNReal) ≤ irrMeasure x := by
    simp only [irrMeasure]
    exact le_sSup ⟨ν', hmem, rfl⟩
  have hνM : (ν' : ENNReal) ≤ (M : ENNReal) := le_trans hle hM
  have hνM' : (ν' : ℝ) ≤ (M : ℝ) := by exact_mod_cast hνM
  linarith [hν'coe]

/-- μ 上界 ⇒ 最终逼近下界（n 作分母）：μ(x)≤M ⇒ ∀ε>0，∃N，∀n≥N, ∀m:ℤ，
    |x−m/n| ≥ n^(−(M+ε))。μ 定义直接推论：(M+ε)-好逼近对集有限，取分母 max。
    注意：此引理走 μ 上界方向，用 n 分母，避开 T3 alekseyev_diophantine 的分子分母障碍。 -/
lemma eventual_approx_lower_bound {x : ℝ} {M : NNReal} (hM : irrMeasure x ≤ (M : ENNReal))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℤ,
      |x - (m : ℝ) / (n : ℝ)| ≥ (n : ℝ) ^ (-((M : ℝ) + ε)) := by
  set ν : ℝ := (M : ℝ) + ε with hνdef
  have hνgt : (M : ℝ) < ν := by linarith
  have hfin : (apprPairs x ν).Finite := apprPairs_finite_of_mu_lt hM hνgt
  -- 有限集的分母投影有界
  set S : Finset ℕ := hfin.toFinset.image (fun pq : ℤ × ℕ => pq.2) with hSdef
  by_cases hSne : S.Nonempty
  · use S.max' hSne + 1
    intro n hn m
    have hn0 : 0 < n := by
      have : 0 < S.max' hSne + 1 := Nat.succ_pos _
      omega
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
    by_contra hlt
    push Not at hlt
    -- hlt : |x−m/n| < n^(−ν)，即 (m,n)∈apprPairs x ν
    have hmem : (m, n) ∈ apprPairs x ν := by
      simp only [apprPairs, Set.mem_setOf_eq]
      exact ⟨hn0, by simpa [hνdef] using hlt⟩
    have hmemS : n ∈ S := by
      simp only [hSdef, Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨(m, n), hmem, rfl⟩
    have hle : n ≤ S.max' hSne := Finset.le_max' S n hmemS
    omega
  · use 1
    intro n hn m
    have hn0 : 0 < n := by omega
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
    by_contra hlt
    push Not at hlt
    have hmem : (m, n) ∈ apprPairs x ν := by
      simp only [apprPairs, Set.mem_setOf_eq]
      exact ⟨hn0, by simpa [hνdef] using hlt⟩
    have hmemS : n ∈ S := by
      simp only [hSdef, Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨(m, n), hmem, rfl⟩
    exact hSne ⟨n, hmemS⟩

/-- 差商逼近误差界（稀疏性引理核心代数）：
    若 |x−p₁/q₁|≤A, |x−p₂/q₂|≤B，q₁<q₂，则差商 (p₂−p₁)/(q₂−q₁) 满足
    |x−(p₂−p₁)/(q₂−q₁)| ≤ (q₁·A + q₂·B)/(q₂−q₁)。
    纯代数恒等式 + 三角不等式，已证。 -/
lemma diff_quotient_error_bound (x : ℝ) (p₁ p₂ : ℤ) (q₁ q₂ : ℕ)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hlt : q₁ < q₂)
    (A B : ℝ) (hA : |x - (p₁ : ℝ) / (q₁ : ℝ)| ≤ A) (hB : |x - (p₂ : ℝ) / (q₂ : ℝ)| ≤ B) :
    |x - ((p₂ - p₁ : ℤ) : ℝ) / ((q₂ - q₁ : ℕ) : ℝ)| ≤
      ((q₁ : ℝ) * A + (q₂ : ℝ) * B) / ((q₂ : ℝ) - (q₁ : ℝ)) := by
  have hq₁R : 0 < (q₁ : ℝ) := by exact_mod_cast hq₁
  have hq₂R : 0 < (q₂ : ℝ) := by exact_mod_cast hq₂
  have hdiff_pos : 0 < (q₂ : ℝ) - (q₁ : ℝ) := by
    have : (q₁ : ℝ) < (q₂ : ℝ) := by exact_mod_cast hlt
    linarith
  have hdiff_cast : ((q₂ - q₁ : ℕ) : ℝ) = (q₂ : ℝ) - (q₁ : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hlt)]
  -- 关键恒等式：x − (p₂−p₁)/(q₂−q₁) = (q₂(x−p₂/q₂) − q₁(x−p₁/q₁))/(q₂−q₁)
  have hkey : x - ((p₂ - p₁ : ℤ) : ℝ) / ((q₂ - q₁ : ℕ) : ℝ) =
      ((q₂ : ℝ) * (x - (p₂ : ℝ) / (q₂ : ℝ)) - (q₁ : ℝ) * (x - (p₁ : ℝ) / (q₁ : ℝ))) /
        ((q₂ : ℝ) - (q₁ : ℝ)) := by
    rw [hdiff_cast]
    field_simp
    push_cast
    ring
  rw [hkey]
  have hnum : |(q₂ : ℝ) * (x - (p₂ : ℝ) / (q₂ : ℝ)) - (q₁ : ℝ) * (x - (p₁ : ℝ) / (q₁ : ℝ))| ≤
      (q₁ : ℝ) * A + (q₂ : ℝ) * B := by
    calc |(q₂ : ℝ) * (x - (p₂ : ℝ) / (q₂ : ℝ)) - (q₁ : ℝ) * (x - (p₁ : ℝ) / (q₁ : ℝ))|
        ≤ |(q₂ : ℝ) * (x - (p₂ : ℝ) / (q₂ : ℝ))| + |(q₁ : ℝ) * (x - (p₁ : ℝ) / (q₁ : ℝ))| :=
          abs_sub _ _
      _ = (q₂ : ℝ) * |x - (p₂ : ℝ) / (q₂ : ℝ)| + (q₁ : ℝ) * |x - (p₁ : ℝ) / (q₁ : ℝ)| := by
          rw [abs_mul, abs_mul, abs_of_pos hq₂R, abs_of_pos hq₁R]
      _ ≤ (q₂ : ℝ) * B + (q₁ : ℝ) * A := by
          gcongr
      _ = (q₁ : ℝ) * A + (q₂ : ℝ) * B := by ring
  rw [abs_div, abs_of_pos hdiff_pos]
  exact (div_le_div_iff_of_pos_right hdiff_pos).mpr hnum

/-- 好逼近差商误差上界（稀疏性引理核心）：
    若 (p₁,q₁),(p₂,q₂) 都是 ν-好逼近（|x−pᵢ/qᵢ|<qᵢ^(−ν)），q₁<q₂，则差商满足
    |x−(p₂−p₁)/(q₂−q₁)| < (q₁^(1−ν)+q₂^(1−ν))/(q₂−q₁)。
    由 diff_quotient_error_bound 代入 A=q₁^(−ν),B=q₂^(−ν)。 -/
lemma good_approx_diff_quotient_bound (x : ℝ) (ν : ℝ) (p₁ p₂ : ℤ) (q₁ q₂ : ℕ)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hlt : q₁ < q₂)
    (h₁ : |x - (p₁ : ℝ) / (q₁ : ℝ)| < (q₁ : ℝ) ^ (-ν))
    (h₂ : |x - (p₂ : ℝ) / (q₂ : ℝ)| < (q₂ : ℝ) ^ (-ν)) :
    |x - ((p₂ - p₁ : ℤ) : ℝ) / ((q₂ - q₁ : ℕ) : ℝ)| <
      ((q₁ : ℝ) ^ (1 - ν) + (q₂ : ℝ) ^ (1 - ν)) / ((q₂ : ℝ) - (q₁ : ℝ)) := by
  have hq₁R : 0 < (q₁ : ℝ) := by exact_mod_cast hq₁
  have hq₂R : 0 < (q₂ : ℝ) := by exact_mod_cast hq₂
  have hdiff_pos : 0 < (q₂ : ℝ) - (q₁ : ℝ) := by
    have : (q₁ : ℝ) < (q₂ : ℝ) := by exact_mod_cast hlt
    linarith
  have hdiff_cast : ((q₂ - q₁ : ℕ) : ℝ) = (q₂ : ℝ) - (q₁ : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hlt)]
  have hkey : x - ((p₂ - p₁ : ℤ) : ℝ) / ((q₂ - q₁ : ℕ) : ℝ) =
      ((q₂ : ℝ) * (x - (p₂ : ℝ) / (q₂ : ℝ)) - (q₁ : ℝ) * (x - (p₁ : ℝ) / (q₁ : ℝ))) /
        ((q₂ : ℝ) - (q₁ : ℝ)) := by
    rw [hdiff_cast]; field_simp; push_cast; ring
  rw [hkey, abs_div, abs_of_pos hdiff_pos]
  apply (div_lt_div_iff_of_pos_right hdiff_pos).mpr
  have hp₁ : (q₁ : ℝ) * (q₁ : ℝ) ^ (-ν) = (q₁ : ℝ) ^ (1 - ν) := by
    rw [show (1 - ν : ℝ) = 1 + (-ν) by ring, Real.rpow_add hq₁R, Real.rpow_one]
  have hp₂ : (q₂ : ℝ) * (q₂ : ℝ) ^ (-ν) = (q₂ : ℝ) ^ (1 - ν) := by
    rw [show (1 - ν : ℝ) = 1 + (-ν) by ring, Real.rpow_add hq₂R, Real.rpow_one]
  calc |(q₂ : ℝ) * (x - (p₂ : ℝ) / (q₂ : ℝ)) - (q₁ : ℝ) * (x - (p₁ : ℝ) / (q₁ : ℝ))|
      ≤ (q₂ : ℝ) * |x - (p₂ : ℝ) / (q₂ : ℝ)| + (q₁ : ℝ) * |x - (p₁ : ℝ) / (q₁ : ℝ)| := by
        calc _ ≤ |(q₂ : ℝ) * (x - (p₂ : ℝ) / (q₂ : ℝ))| +
            |(q₁ : ℝ) * (x - (p₁ : ℝ) / (q₁ : ℝ))| := abs_sub _ _
          _ = (q₂ : ℝ) * |x - (p₂ : ℝ) / (q₂ : ℝ)| +
            (q₁ : ℝ) * |x - (p₁ : ℝ) / (q₁ : ℝ)| := by
            rw [abs_mul, abs_mul, abs_of_pos hq₂R, abs_of_pos hq₁R]
    _ < (q₂ : ℝ) * (q₂ : ℝ) ^ (-ν) + (q₁ : ℝ) * (q₁ : ℝ) ^ (-ν) := by
        gcongr
    _ = (q₁ : ℝ) ^ (1 - ν) + (q₂ : ℝ) ^ (1 - ν) := by rw [hp₁, hp₂]; ring

/-- 稀疏性指数估计（实数核心）：设 ν>1, δ>0, 1≤q₁<q₂≤2q₁, Q=q₂−q₁>0。
    若 2·q₁^(1−ν) < Q^(1−ν−δ)，则 (q₁^(1−ν)+q₂^(1−ν))/Q < Q^(−ν−δ)。
    证明：ν>1 ⇒ 1−ν<0 ⇒ q₂^(1−ν)≤q₁^(1−ν)（底数递增、负指数反序），故分子≤2q₁^(1−ν)；
    再由 Q^(1−ν−δ)=Q^(−ν−δ)·Q 与条件即得。 -/
lemma sparsity_exponent_estimate (ν δ : ℝ) (hν : 1 < ν) (q₁ q₂ Q : ℝ)
    (hq₁ : 1 ≤ q₁) (hq₂ : q₁ < q₂) (hq₂le : q₂ ≤ 2 * q₁) (hQ : 0 < Q)
    (hQdef : Q = q₂ - q₁)
    (hcond : 2 * q₁ ^ (1 - ν) < Q ^ (1 - ν - δ)) :
    (q₁ ^ (1 - ν) + q₂ ^ (1 - ν)) / Q < Q ^ (-ν - δ) := by
  have hq₁pos : 0 < q₁ := by linarith
  -- ν>1 ⇒ 1−ν<0，底数 q₁≤q₂ ⇒ q₂^(1−ν)≤q₁^(1−ν)
  have hmono : q₂ ^ (1 - ν) ≤ q₁ ^ (1 - ν) :=
    Real.rpow_le_rpow_of_nonpos hq₁pos (by linarith : q₁ ≤ q₂) (by linarith)
  have hnum : q₁ ^ (1 - ν) + q₂ ^ (1 - ν) ≤ 2 * q₁ ^ (1 - ν) := by linarith
  have hstep : (2 * q₁ ^ (1 - ν)) / Q < Q ^ (-ν - δ) := by
    rw [div_lt_iff₀ hQ]
    have hpow : Q ^ (1 - ν - δ) = Q ^ (-ν - δ) * Q := by
      have : (1 - ν - δ : ℝ) = (-ν - δ) + 1 := by ring
      rw [this, Real.rpow_add hQ, Real.rpow_one]
    linarith
  calc (q₁ ^ (1 - ν) + q₂ ^ (1 - ν)) / Q
      ≤ (2 * q₁ ^ (1 - ν)) / Q := by gcongr
    _ < Q ^ (-ν - δ) := hstep

/-- 稀疏性核心定理：设 ν>1, δ>0。若 (p₁,q₁),(p₂,q₂) 是 ν-好逼近，q₁≥2, q₁<q₂≤2q₁，
    Q=q₂−q₁>0 满足 2·q₁^(1−ν) < Q^(1−ν−δ)，则差商 (p₂−p₁)/Q 是 (ν+δ)-好逼近：
    |x−(p₂−p₁)/Q| < Q^(−(ν+δ))。
    组合 good_approx_diff_quotient_bound + sparsity_exponent_estimate。 -/
lemma sparsity_diff_quotient_good (x : ℝ) (ν δ : ℝ) (hν : 1 < ν) (hδ : 0 < δ)
    (p₁ p₂ : ℤ) (q₁ q₂ : ℕ) (hq₁ : 2 ≤ q₁) (hq₂ : 0 < q₂) (hlt : q₁ < q₂)
    (hle2 : q₂ ≤ 2 * q₁)
    (h₁ : |x - (p₁ : ℝ) / (q₁ : ℝ)| < (q₁ : ℝ) ^ (-ν))
    (h₂ : |x - (p₂ : ℝ) / (q₂ : ℝ)| < (q₂ : ℝ) ^ (-ν))
    (hcond : 2 * (q₁ : ℝ) ^ (1 - ν) < ((q₂ - q₁ : ℕ) : ℝ) ^ (1 - ν - δ)) :
    |x - ((p₂ - p₁ : ℤ) : ℝ) / ((q₂ - q₁ : ℕ) : ℝ)| <
      ((q₂ - q₁ : ℕ) : ℝ) ^ (-(ν + δ)) := by
  have hq₁pos : 0 < q₁ := by omega
  have hQpos : 0 < (q₂ - q₁ : ℕ) := Nat.sub_pos_of_lt hlt
  have hQposR : 0 < ((q₂ - q₁ : ℕ) : ℝ) := by exact_mod_cast hQpos
  have hq₁R : 1 ≤ (q₁ : ℝ) := by exact_mod_cast (by omega : 1 ≤ q₁)
  have hq₂R : (q₁ : ℝ) < (q₂ : ℝ) := by exact_mod_cast hlt
  have hq₂leR : (q₂ : ℝ) ≤ 2 * (q₁ : ℝ) := by exact_mod_cast hle2
  have hQdef : ((q₂ - q₁ : ℕ) : ℝ) = (q₂ : ℝ) - (q₁ : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hlt)]
  have hbound := good_approx_diff_quotient_bound x ν p₁ p₂ q₁ q₂ hq₁pos hq₂ hlt h₁ h₂
  -- 把 hbound 的分母统一为 ((q₂−q₁:ℕ):ℝ)
  have hbound' : |x - ((p₂ - p₁ : ℤ) : ℝ) / ((q₂ - q₁ : ℕ) : ℝ)| <
      ((q₁ : ℝ) ^ (1 - ν) + (q₂ : ℝ) ^ (1 - ν)) / ((q₂ - q₁ : ℕ) : ℝ) := by
    simpa only [hQdef] using hbound
  have hcond' : 2 * (q₁ : ℝ) ^ (1 - ν) < ((q₂ - q₁ : ℕ) : ℝ) ^ (1 - ν - δ) := hcond
  have hest := sparsity_exponent_estimate ν δ hν (q₁ : ℝ) (q₂ : ℝ) ((q₂ - q₁ : ℕ) : ℝ)
    hq₁R hq₂R hq₂leR hQposR hQdef hcond'
  have htarget : ((q₂ - q₁ : ℕ) : ℝ) ^ (-(ν + δ)) =
      ((q₂ - q₁ : ℕ) : ℝ) ^ (-ν - δ) := by congr 1; ring
  rw [htarget]
  linarith

/-- 固定分母纤维有限（重数界定基础）：对固定 d>0 与任意 ν，
    满足 |x−p/d|<d^(−ν) 的整数 p 只有有限多（p 落在开区间 (d·x−d^(1−ν), d·x+d^(1−ν)) 内）。
    这是 Meiburg Q_max 重数界定的基础：同一差商分母对应的分子有限。 -/
lemma fixed_denom_fiber_finite (x : ℝ) (d : ℕ) (hd : 0 < d) (ν : ℝ) :
    {p : ℤ | |x - (p : ℝ) / (d : ℝ)| < (d : ℝ) ^ (-ν)}.Finite := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  set L : ℝ := (d : ℝ) * x - (d : ℝ) ^ (1 - ν)
  set U : ℝ := (d : ℝ) * x + (d : ℝ) ^ (1 - ν)
  apply Set.Finite.subset (Set.finite_Icc ⌊L⌋ ⌈U⌉)
  intro p hp
  simp only [Set.mem_setOf_eq, Set.mem_Icc] at hp ⊢
  have h : |x - (p : ℝ) / (d : ℝ)| < (d : ℝ) ^ (-ν) := hp
  have hpow : (d : ℝ) * (d : ℝ) ^ (-ν) = (d : ℝ) ^ (1 - ν) := by
    rw [show (1 - ν : ℝ) = 1 + (-ν) by ring, Real.rpow_add hdR, Real.rpow_one]
  have h' : |(d : ℝ) * x - (p : ℝ)| < (d : ℝ) ^ (1 - ν) := by
    have heq : (d : ℝ) * x - (p : ℝ) = (d : ℝ) * (x - (p : ℝ) / (d : ℝ)) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hdR, ← hpow]
    gcongr
  rw [abs_lt] at h'
  constructor
  · have : (⌊L⌋ : ℝ) ≤ (p : ℝ) := by
      have := Int.floor_le L
      have := Int.lt_floor_add_one L
      linarith
    exact_mod_cast this
  · have : (p : ℝ) ≤ (⌈U⌉ : ℝ) := by
      have := Int.le_ceil U
      have := Int.ceil_lt_add_one U
      linarith
    exact_mod_cast this