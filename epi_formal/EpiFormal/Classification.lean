import Mathlib
import EpiFormal.EulerConvergents
import EpiFormal.Measure
import EpiFormal.MeiburgConvergence
import EpiFormal.Alekseyev

/-!
# 子任务 B：S1 Theorem 2（分类格）+ S2 Corollary 3（定量间隙 1/4）—— 联合编译归一版

来源：用户修订包扩展材料 S1/S2。本文件为「总」联合编译归一版：
地基统一取用 A 组 `EpiFormal.EulerConvergents`（顶层 Psel/Qsel/deltaSel 与两条 deltaSel 公理），
删除 B 原自建地基定义与重复公理；B 下游所需的全下标/三指标桥接引理在此从 A 接口重证，
Theorem 2 / Corollary 3 主体证明原样保留。

核心数学路线（避开整除性泥潭）：
  Cramér 行列式 det = P_j Q_{j+1} − P_{j+1} Q_j = 2(−1)^{j+1} = ±2。
  取 s = (−1)^{j+1} = det/2 ∈ {±1}，直接构造整数 a,b，则 2M_j = aP_j + bQ_j 自动成立。
  共同递推传播到尾部；除以 Q_j 取极限得 2x = ae + b；P_j,Q_j 均奇 ⇒ a+b 偶 ⇒ x ∈ L。

e+π 无理性仍开放；本文件是分类定理，不判定该问题。
-/

open Real Set Filter Int

namespace Classification

noncomputable section

/-! ## 地基桥接：从 A 组重证 B 下游所需引理（同名同陈述） -/

-- A 已提供顶层 Psel/Qsel/deltaSel、Psel_zero/one/two、Qsel_zero/one/two（simp）、
-- Psel_rec/Qsel_rec（j≥2 三指标）、sel_determinant（j≥1）、Qsel_pos（j≥1）、
-- Psel_odd/Qsel_odd（j≥1）、Qsel_double（j≥2）、Qsel_succ_coprime（j≥1）、
-- Qsel_tendsto_atTop、Psel_div_Qsel_tendsto_exp、两条 deltaSel 公理。
-- 以下补 B 需要的全下标 / 系数 4j+6 / j≥1 版本。

/-- 系数 4j+6 形式的 P 递推（全 j）。 -/
lemma Psel_rec (j : ℕ) : Psel (j + 2) = (4 * (j : ℤ) + 6) * Psel (j + 1) + Psel j := by
  have h := selPair_rec 1 3 j
  simp only [Psel] at h ⊢
  convert h using 1 <;> push_cast <;> ring

/-- 系数 4j+6 形式的 Q 递推（全 j）。 -/
lemma Qsel_rec (j : ℕ) : Qsel (j + 2) = (4 * (j : ℤ) + 6) * Qsel (j + 1) + Qsel j := by
  have h := selPair_rec 1 1 j
  simp only [Qsel] at h ⊢
  convert h using 1 <;> push_cast <;> ring

/-- 三指标 P 递推（j≥1）。 -/
lemma Psel_rec' (j : ℕ) (hj : 1 ≤ j) :
    Psel (j + 1) = (4 * (j : ℤ) + 2) * Psel j + Psel (j - 1) := by
  by_cases hj2 : 2 ≤ j
  · exact _root_.Psel_rec j hj2
  · have hj1 : j = 1 := by omega
    subst hj1
    norm_num [Psel, selPair]

/-- 三指标 Q 递推（j≥1）。 -/
lemma Qsel_rec' (j : ℕ) (hj : 1 ≤ j) :
    Qsel (j + 1) = (4 * (j : ℤ) + 2) * Qsel j + Qsel (j - 1) := by
  by_cases hj2 : 2 ≤ j
  · exact _root_.Qsel_rec j hj2
  · have hj1 : j = 1 := by omega
    subst hj1
    norm_num [Qsel, selPair]

/-- Q 正性（全 j，含 j=0 占位 1）。 -/
lemma Qsel_pos (j : ℕ) : 0 < Qsel j :=
  (selPair_pos_odd 1 1 (by norm_num) (by norm_num) odd_one odd_one j).1

/-- P 正性（全 j）。 -/
lemma Psel_pos (j : ℕ) : 0 < Psel j :=
  (selPair_pos_odd 1 3 (by norm_num) (by norm_num) odd_one (by decide : Odd (3 : ℤ)) j).1

/-- 行列式（全 j，含 j=0）。 -/
lemma sel_determinant (j : ℕ) :
    Psel j * Qsel (j + 1) - Psel (j + 1) * Qsel j = 2 * (-1 : ℤ) ^ (j + 1) := by
  rcases j with (_ | k)
  · norm_num [Psel, Qsel, selPair]
  · exact _root_.sel_determinant (k + 1) (by omega)

/-- 行列式绝对值为 2。 -/
lemma sel_determinant_abs (j : ℕ) :
    |Psel j * Qsel (j + 1) - Psel (j + 1) * Qsel j| = 2 := by
  rw [sel_determinant]
  have h : (-1 : ℤ) ^ (j + 1) = 1 ∨ (-1 : ℤ) ^ (j + 1) = -1 := by
    rcases Nat.even_or_odd (j + 1) with he | ho
    · left; exact he.neg_one_pow
    · right; exact ho.neg_one_pow
  rcases h with h | h <;> rw [h] <;> norm_num

/-- P 奇性（全 j）。 -/
lemma Psel_odd (j : ℕ) : Odd (Psel j) :=
  (selPair_pos_odd 1 3 (by norm_num) (by norm_num) odd_one (by decide : Odd (3 : ℤ)) j).2.2.1

/-- Q 奇性（全 j）。 -/
lemma Qsel_odd (j : ℕ) : Odd (Qsel j) :=
  (selPair_pos_odd 1 1 (by norm_num) (by norm_num) odd_one odd_one j).2.2.1

/-- Q 倍增（j≥1）。 -/
lemma Qsel_double (j : ℕ) (hj : 1 ≤ j) : 2 * Qsel j ≤ Qsel (j + 1) := by
  rcases j with (_ | k)
  · omega
  · cases k with
    | zero => norm_num [Qsel, selPair]
    | succ k => exact _root_.Qsel_double (k + 2) (by omega)

/-- 相邻 Q 互素（j≥1），直接取 A。 -/
lemma Qsel_succ_coprime (j : ℕ) (hj : 1 ≤ j) : Int.gcd (Qsel j) (Qsel (j + 1)) = 1 :=
  _root_.Qsel_succ_coprime j hj

/-- Q_j → +∞，直接取 A。 -/
lemma Qsel_tendsto_atTop : Tendsto (fun j : ℕ => (Qsel j : ℝ)) atTop atTop :=
  _root_.Qsel_tendsto_atTop

/-- P_j/Q_j → e，直接取 A。 -/
lemma Psel_div_Qsel_tendsto_exp :
    Tendsto (fun j : ℕ => (Psel j : ℝ) / (Qsel j : ℝ)) atTop (nhds (Real.exp 1)) :=
  _root_.Psel_div_Qsel_tendsto_exp

/-! ## 记号定义 -/

/-- 最近整数 [y]。 -/
noncomputable def nearestInt (x : ℝ) : ℤ := round x

/-- ε_j(x) = Q_j x − [Q_j x]。 -/
noncomputable def eps (x : ℝ) (j : ℕ) : ℝ :=
  (Qsel j : ℝ) * x - (nearestInt ((Qsel j : ℝ) * x) : ℝ)

/-- 整数缺陷 D_j = M_{j+1} − (4j+2)M_j − M_{j−1}（j≥2 时 j−1 为真前驱）。 -/
noncomputable def defect (x : ℝ) (j : ℕ) : ℤ :=
  nearestInt ((Qsel (j + 1) : ℝ) * x) - (4 * (j : ℤ) + 2) * nearestInt ((Qsel j : ℝ) * x)
    - nearestInt ((Qsel (j - 1) : ℝ) * x)

/-- 分类格 L = ℤ + ℤ(e+1)/2。 -/
def latticeL : Set ℝ := {x | ∃ m n : ℤ, x = (m : ℝ) + (n : ℝ) * (Real.exp 1 + 1) / 2}

/-! ## 基础性质 -/

lemma abs_eps_le_half (x : ℝ) (j : ℕ) : |eps x j| ≤ 1 / 2 := by
  unfold eps nearestInt
  exact abs_sub_round _

/-- ε_j/Q_j → 0：由 |ε_j|≤1/2 与 Q_j→∞。 -/
lemma eps_div_Qsel_tendsto_zero (x : ℝ) :
    Tendsto (fun j : ℕ => eps x j / (Qsel j : ℝ)) atTop (nhds 0) := by
  have hbound : ∀ j : ℕ, |eps x j / (Qsel j : ℝ)| ≤ (1 / 2) / (Qsel j : ℝ) := by
    intro j
    have hq : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j
    have h1 : |eps x j| ≤ 1 / 2 := abs_eps_le_half x j
    calc |eps x j / (Qsel j : ℝ)| = |eps x j| / (Qsel j : ℝ) := by rw [abs_div, abs_of_pos hq]
      _ ≤ (1 / 2) / (Qsel j : ℝ) := by gcongr
  have hsqueeze : Tendsto (fun j : ℕ => (1 / 2) / (Qsel j : ℝ)) atTop (nhds 0) :=
    Qsel_tendsto_atTop.const_div_atTop (1 / 2)
  have hneg : Tendsto (fun j : ℕ => -((1 / 2) / (Qsel j : ℝ))) atTop (nhds 0) := by
    simpa using hsqueeze.neg
  have hlower : ∀ᶠ j : ℕ in atTop, -((1 / 2) / (Qsel j : ℝ)) ≤ eps x j / (Qsel j : ℝ) := by
    apply Filter.eventually_of_mem Filter.univ_mem
    intro j _
    have := abs_le.mp (hbound j)
    linarith
  have hupper : ∀ᶠ j : ℕ in atTop, eps x j / (Qsel j : ℝ) ≤ (1 / 2) / (Qsel j : ℝ) := by
    apply Filter.eventually_of_mem Filter.univ_mem
    intro j _
    have := abs_le.mp (hbound j)
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hsqueeze hlower hupper

/-- 缺陷恒等式（纯代数，j≥1）：D_j = −ε_{j+1} + (4j+2)ε_j + ε_{j−1}。 -/
lemma defect_identity (x : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    (defect x j : ℝ) = -eps x (j + 1) + (4 * (j : ℝ) + 2) * eps x j + eps x (j - 1) := by
  have hQ : (Qsel (j + 1) : ℝ) = (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by
    have := Qsel_rec' j hj
    exact_mod_cast this
  simp only [defect, eps, nearestInt]
  push_cast
  rw [hQ]
  ring

/-- 整数值序列绝对值最终 <1 ⇒ 最终为 0。 -/
lemma int_eventually_zero_of_abs_lt_one {f : ℕ → ℤ}
    (h : ∀ᶠ j : ℕ in atTop, |(f j : ℝ)| < 1) : ∀ᶠ j : ℕ in atTop, f j = 0 := by
  apply h.mono
  intro j hj
  have h2 : |f j| < 1 := by exact_mod_cast hj
  have h3 : -1 < f j ∧ f j < 1 := abs_lt.mp h2
  have h4 : f j = 0 := by omega
  exact h4

/-! ## 核心：defect 最终为 0 ⇒ x ∈ L -/

/-- 传播：若尾部缺陷全为 0，则 2M_j = aP_j + bQ_j 对整个尾部成立。 -/
lemma propagate (x : ℝ) (N : ℕ) (hN : 2 ≤ N)
    (hD : ∀ j : ℕ, N ≤ j → defect x j = 0) :
    ∃ a b : ℤ, ∀ j : ℕ, N ≤ j →
      2 * nearestInt ((Qsel j : ℝ) * x) = a * Psel j + b * Qsel j := by
  let M : ℕ → ℤ := fun j => nearestInt ((Qsel j : ℝ) * x)
  change ∃ a b : ℤ, ∀ j : ℕ, N ≤ j → 2 * M j = a * Psel j + b * Qsel j
  set s : ℤ := (-1 : ℤ) ^ (N + 1) with hsdef
  set a : ℤ := s * (Qsel (N + 1) * M N - Qsel N * M (N + 1)) with hadef
  set b : ℤ := s * (Psel N * M (N + 1) - Psel (N + 1) * M N) with hbdef
  have hs2 : s * (Psel N * Qsel (N + 1) - Psel (N + 1) * Qsel N) = 2 := by
    rw [hsdef, sel_determinant]
    have hpow : (-1 : ℤ) ^ (N + 1) * (-1 : ℤ) ^ (N + 1) = 1 := by
      have h1 : (-1 : ℤ) ^ (N + 1) * (-1 : ℤ) ^ (N + 1) = (-1 : ℤ) ^ ((N + 1) + (N + 1)) := by
        rw [← pow_add]
      have h2 : (N + 1) + (N + 1) = 2 * (N + 1) := by ring
      rw [h1, h2]
      have he : Even (2 * (N + 1)) := ⟨N + 1, by linarith⟩
      rw [he.neg_one_pow]
    nlinarith
  have hbase : 2 * M N = a * Psel N + b * Qsel N := by
    simp only [hadef, hbdef]
    have hcalc : s * (Qsel (N + 1) * M N - Qsel N * M (N + 1)) * Psel N
        + s * (Psel N * M (N + 1) - Psel (N + 1) * M N) * Qsel N
        = M N * (s * (Psel N * Qsel (N + 1) - Psel (N + 1) * Qsel N)) := by ring
    rw [hcalc, hs2]; ring
  have hbase2 : 2 * M (N + 1) = a * Psel (N + 1) + b * Qsel (N + 1) := by
    simp only [hadef, hbdef]
    have hcalc : s * (Qsel (N + 1) * M N - Qsel N * M (N + 1)) * Psel (N + 1)
        + s * (Psel N * M (N + 1) - Psel (N + 1) * M N) * Qsel (N + 1)
        = M (N + 1) * (s * (Psel N * Qsel (N + 1) - Psel (N + 1) * Qsel N)) := by ring
    rw [hcalc, hs2]; ring
  refine ⟨a, b, ?_⟩
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hjN : j = N
    · subst hjN; exact hbase
    · by_cases hjN1 : j = N + 1
      · subst hjN1; exact hbase2
      · have hj2 : N + 2 ≤ j := by omega
        have hjm1N : N ≤ j - 1 := by omega
        have hjm2N : N ≤ j - 2 := by omega
        have hDj : defect x (j - 1) = 0 := hD (j - 1) hjm1N
        have hrecM : M j = (4 * ((j - 1 : ℕ) : ℤ) + 2) * M (j - 1) + M (j - 2) := by
          have := hDj
          simp only [defect] at this
          change nearestInt ((Qsel ((j - 1) + 1) : ℝ) * x)
            - (4 * ((j - 1 : ℕ) : ℤ) + 2) * nearestInt ((Qsel (j - 1) : ℝ) * x)
            - nearestInt ((Qsel ((j - 1) - 1) : ℝ) * x) = 0 at this
          have hc1 : (j - 1 + 1 : ℕ) = j := by omega
          have hc2 : (j - 1 - 1 : ℕ) = j - 2 := by omega
          rw [hc1, hc2] at this
          change M j = (4 * ((j - 1 : ℕ) : ℤ) + 2) * M (j - 1) + M (j - 2)
          simp only [M]
          omega
        have hrecP : Psel j = (4 * ((j - 1 : ℕ) : ℤ) + 2) * Psel (j - 1) + Psel (j - 2) := by
          have := Psel_rec' (j - 1) (by omega)
          have hc1 : (j - 1 + 1 : ℕ) = j := by omega
          have hc2 : (j - 1 - 1 : ℕ) = j - 2 := by omega
          simpa [hc1, hc2] using this
        have hrecQ : Qsel j = (4 * ((j - 1 : ℕ) : ℤ) + 2) * Qsel (j - 1) + Qsel (j - 2) := by
          have := Qsel_rec' (j - 1) (by omega)
          have hc1 : (j - 1 + 1 : ℕ) = j := by omega
          have hc2 : (j - 1 - 1 : ℕ) = j - 2 := by omega
          simpa [hc1, hc2] using this
        have ih1 : 2 * M (j - 1) = a * Psel (j - 1) + b * Qsel (j - 1) :=
          ih (j - 1) (by omega) hjm1N
        have ih2 : 2 * M (j - 2) = a * Psel (j - 2) + b * Qsel (j - 2) :=
          ih (j - 2) (by omega) hjm2N
        rw [hrecM, hrecP, hrecQ]
        nlinarith

/-- 核心引理：defect 最终为 0 ⇒ x ∈ L。 -/
lemma mem_latticeL_of_eventually_defect_zero (x : ℝ)
    (h : ∀ᶠ j : ℕ in atTop, defect x j = 0) : x ∈ latticeL := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  set N' := max N 2 with hN'def
  have hN'2 : 2 ≤ N' := by simp [N']
  have hD : ∀ j : ℕ, N' ≤ j → defect x j = 0 := by
    intro j hj; exact hN j (by simp [N'] at hj; omega)
  obtain ⟨a, b, hab⟩ := propagate x N' hN'2 hD
  have hM : Tendsto (fun j : ℕ => (2 * nearestInt ((Qsel j : ℝ) * x) : ℝ) / (Qsel j : ℝ))
      atTop (nhds (2 * x)) := by
    have heq : (fun j : ℕ => (2 * nearestInt ((Qsel j : ℝ) * x) : ℝ) / (Qsel j : ℝ))
        = (fun j : ℕ => 2 * x - 2 * eps x j / (Qsel j : ℝ)) := by
      funext j
      have hq : (Qsel j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Qsel_pos j)
      simp only [eps, nearestInt]
      field_simp
      ring
    rw [heq]
    have hεQ : Tendsto (fun j : ℕ => 2 * eps x j / (Qsel j : ℝ)) atTop (nhds 0) := by
      have h1 : Tendsto (fun j : ℕ => eps x j / (Qsel j : ℝ)) atTop (nhds 0) :=
        eps_div_Qsel_tendsto_zero x
      have h2 : Tendsto (fun j : ℕ => 2 * (eps x j / (Qsel j : ℝ))) atTop (nhds (2 * 0)) :=
        h1.const_mul (2 : ℝ)
      have h3 : (fun j : ℕ => 2 * (eps x j / (Qsel j : ℝ)))
          = (fun j : ℕ => 2 * eps x j / (Qsel j : ℝ)) := by funext j; ring
      rw [h3] at h2
      simpa using h2
    have hsub : Tendsto (fun j : ℕ => 2 * x - 2 * eps x j / (Qsel j : ℝ)) atTop (nhds (2 * x - 0)) :=
      tendsto_const_nhds.sub hεQ
    simpa using hsub
  have hlin : Tendsto (fun j : ℕ => ((a * Psel j + b * Qsel j : ℤ) : ℝ) / (Qsel j : ℝ))
      atTop (nhds ((a : ℝ) * Real.exp 1 + (b : ℝ))) := by
    have heq : (fun j : ℕ => ((a * Psel j + b * Qsel j : ℤ) : ℝ) / (Qsel j : ℝ))
        = (fun j : ℕ => (a : ℝ) * ((Psel j : ℝ) / (Qsel j : ℝ)) + (b : ℝ)) := by
      funext j
      have hq : (Qsel j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Qsel_pos j)
      push_cast
      field_simp
    rw [heq]
    exact (Psel_div_Qsel_tendsto_exp.const_mul (a : ℝ)).add tendsto_const_nhds
  have hevent : ∀ᶠ j : ℕ in atTop,
      ((a * Psel j + b * Qsel j : ℤ) : ℝ) / (Qsel j : ℝ)
        = (2 * nearestInt ((Qsel j : ℝ) * x) : ℝ) / (Qsel j : ℝ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N', ?_⟩
    intro j hj
    have h := hab j hj
    have hq : (Qsel j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Qsel_pos j)
    have hcast : ((a * Psel j + b * Qsel j : ℤ) : ℝ) = (2 * nearestInt ((Qsel j : ℝ) * x) : ℝ) := by
      exact_mod_cast h.symm
    rw [hcast]
  have hlin' : Tendsto (fun j : ℕ => (2 * nearestInt ((Qsel j : ℝ) * x) : ℝ) / (Qsel j : ℝ))
      atTop (nhds ((a : ℝ) * Real.exp 1 + (b : ℝ))) :=
    hlin.congr' hevent
  have hlim : 2 * x = (a : ℝ) * Real.exp 1 + (b : ℝ) :=
    tendsto_nhds_unique hM hlin'
  have hparity : Even (a + b) := by
    have h2M : Even (2 * nearestInt ((Qsel N' : ℝ) * x)) := ⟨nearestInt ((Qsel N' : ℝ) * x), by ring⟩
    have h_eq : 2 * nearestInt ((Qsel N' : ℝ) * x) = a * Psel N' + b * Qsel N' := hab N' (by simp [N'])
    rw [h_eq] at h2M
    obtain ⟨t, ht⟩ := h2M
    have hP : ∃ u, Psel N' = 2 * u + 1 := by
      obtain ⟨u, hu⟩ := Psel_odd N'; exact ⟨u, by linarith⟩
    have hQ : ∃ v, Qsel N' = 2 * v + 1 := by
      obtain ⟨v, hv⟩ := Qsel_odd N'; exact ⟨v, by linarith⟩
    obtain ⟨u, hu⟩ := hP
    obtain ⟨v, hv⟩ := hQ
    rw [hu, hv] at ht
    have hab2 : a + b = (t - a * u - b * v) + (t - a * u - b * v) := by linarith
    exact ⟨t - a * u - b * v, hab2⟩
  obtain ⟨k, hk⟩ := hparity
  refine ⟨k - a, a, ?_⟩
  have hb : (b : ℝ) = 2 * (k : ℝ) - (a : ℝ) := by
    have : (b : ℤ) = 2 * k - a := by linarith
    exact_mod_cast this
  have h2x : 2 * x = (a : ℝ) * Real.exp 1 + (b : ℝ) := hlim
  rw [hb] at h2x
  have hx : x = ((a : ℝ) * Real.exp 1 + 2 * (k : ℝ) - (a : ℝ)) / 2 := by linarith
  rw [hx]
  push_cast
  ring

/-! ## Theorem 2 -/

/-- (i) j‖Q_j x‖→0 ⇒ defect 最终为 0。 -/
lemma defect_eventually_zero_of_tendsto (x : ℝ)
    (h : Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x)) atTop (nhds 0)) :
    ∀ᶠ j : ℕ in atTop, defect x j = 0 := by
  have heps : ∀ j : ℕ, |eps x j| = distToNearestInt ((Qsel j : ℝ) * x) := by intro j; rfl
  have hjε : Tendsto (fun j : ℕ => (j : ℝ) * |eps x j|) atTop (nhds 0) := by
    have heq : (fun j : ℕ => (j : ℝ) * |eps x j|)
        = (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x)) := by
      funext j; rw [heps]
    rw [heq]; exact h
  have hsmall : ∀ᶠ j : ℕ in atTop, (j : ℝ) * |eps x j| < 1 / 8 :=
    hjε.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  set N' := max N 3 + 1 with hN'def
  have hDlt : ∀ᶠ j : ℕ in atTop, |(defect x j : ℝ)| < 1 := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N', ?_⟩
    intro j hj
    have hjmaxlt : max N 3 < j := Nat.lt_of_succ_le hj
    have hjmax : max N 3 ≤ j := le_of_lt hjmaxlt
    have hjN' : N ≤ j := le_trans (le_max_left N 3) hjmax
    have hj3 : 3 ≤ j := le_trans (le_max_right N 3) hjmax
    have hj1 : 1 ≤ j := by omega
    have hjN : N ≤ j := hjN'
    have hjNlt : N < j := lt_of_le_of_lt (le_max_left N 3) hjmaxlt
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hjm1pos : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j - 1)
    have hjne : (j : ℝ) ≠ 0 := ne_of_gt hjpos
    have hjp1ne : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hεj : |eps x j| < 1 / (8 * (j : ℝ)) := by
      have h := hN j hjN
      have hdiv : (j : ℝ) * |eps x j| / (j : ℝ) < (1 / 8) / (j : ℝ) :=
        (div_lt_div_iff_of_pos_right hjpos).mpr h
      have heq : (j : ℝ) * |eps x j| / (j : ℝ) = |eps x j| := by field_simp
      rw [heq] at hdiv
      convert hdiv using 1 <;> ring
    have hεjp1 : |eps x (j + 1)| < 1 / (8 * ((j + 1 : ℕ) : ℝ)) := by
      have hjp1N : N ≤ j + 1 := by omega
      have h := hN (j + 1) hjp1N
      have hjp1pos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
      have hdiv : ((j + 1 : ℕ) : ℝ) * |eps x (j + 1)| / ((j + 1 : ℕ) : ℝ) < (1 / 8) / ((j + 1 : ℕ) : ℝ) :=
        (div_lt_div_iff_of_pos_right hjp1pos).mpr h
      have heq : ((j + 1 : ℕ) : ℝ) * |eps x (j + 1)| / ((j + 1 : ℕ) : ℝ) = |eps x (j + 1)| := by field_simp
      rw [heq] at hdiv
      convert hdiv using 1 <;> ring
    have hεjm1 : |eps x (j - 1)| < 1 / (8 * ((j - 1 : ℕ) : ℝ)) := by
      have hjm1N : N ≤ j - 1 := Nat.le_sub_one_of_lt hjNlt
      have h := hN (j - 1) hjm1N
      have hdiv : ((j - 1 : ℕ) : ℝ) * |eps x (j - 1)| / ((j - 1 : ℕ) : ℝ) < (1 / 8) / ((j - 1 : ℕ) : ℝ) :=
        (div_lt_div_iff_of_pos_right hjm1pos).mpr h
      have heq : ((j - 1 : ℕ) : ℝ) * |eps x (j - 1)| / ((j - 1 : ℕ) : ℝ) = |eps x (j - 1)| := by field_simp
      rw [heq] at hdiv
      convert hdiv using 1 <;> ring
    have hD : (defect x j : ℝ) = -eps x (j + 1) + (4 * (j : ℝ) + 2) * eps x j + eps x (j - 1) :=
      defect_identity x j hj1
    have habs : |(defect x j : ℝ)| ≤ |eps x (j + 1)| + (4 * (j : ℝ) + 2) * |eps x j| + |eps x (j - 1)| := by
      rw [hD]
      have h1 : |-eps x (j + 1) + (4 * (j : ℝ) + 2) * eps x j + eps x (j - 1)|
          ≤ |-eps x (j + 1)| + |(4 * (j : ℝ) + 2) * eps x j| + |eps x (j - 1)| := by
        apply le_trans (abs_add_le _ _)
        gcongr
        exact abs_add_le _ _
      have h2 : |-eps x (j + 1)| = |eps x (j + 1)| := abs_neg _
      have h3 : |(4 * (j : ℝ) + 2) * eps x j| = (4 * (j : ℝ) + 2) * |eps x j| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (j : ℝ) + 2)]
      linarith
    have hbound : |eps x (j + 1)| + (4 * (j : ℝ) + 2) * |eps x j| + |eps x (j - 1)|
        < 1 / (8 * ((j + 1 : ℕ) : ℝ)) + (4 * (j : ℝ) + 2) / (8 * (j : ℝ)) + 1 / (8 * ((j - 1 : ℕ) : ℝ)) := by
      apply add_lt_add (add_lt_add hεjp1 ?_) hεjm1
      have hpos : (0 : ℝ) < 4 * (j : ℝ) + 2 := by positivity
      calc (4 * (j : ℝ) + 2) * |eps x j| < (4 * (j : ℝ) + 2) * (1 / (8 * (j : ℝ))) := by
            apply mul_lt_mul_of_pos_left hεj hpos
        _ = (4 * (j : ℝ) + 2) / (8 * (j : ℝ)) := by ring
    have hfinal : 1 / (8 * ((j + 1 : ℕ) : ℝ)) + (4 * (j : ℝ) + 2) / (8 * (j : ℝ)) + 1 / (8 * ((j - 1 : ℕ) : ℝ)) < 1 := by
      have hjp1 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ j)]; simp
      rw [hjp1, hcast]
      have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 2 ≤ j)
      have h1 : 1 / (8 * ((j : ℝ) + 1)) ≤ 1 / 24 := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      have h2 : (4 * (j : ℝ) + 2) / (8 * (j : ℝ)) ≤ 5 / 8 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have h3 : 1 / (8 * ((j : ℝ) - 1)) ≤ 1 / 8 := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      linarith
    linarith
  exact int_eventually_zero_of_abs_lt_one hDlt

/-- Theorem 2 必要性：(i) ⇒ (ii)。 -/
theorem theorem2_necessity (x : ℝ)
    (h : Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x)) atTop (nhds 0)) :
    x ∈ latticeL :=
  mem_latticeL_of_eventually_defect_zero x (defect_eventually_zero_of_tendsto x h)

/-- Theorem 2 充分性：(ii) ⇒ (i)。 -/
theorem theorem2_sufficiency (x : ℝ) (hx : x ∈ latticeL) :
    Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x)) atTop (nhds 0) := by
  obtain ⟨m, n, rfl⟩ := hx
  set K : ℕ → ℤ := fun j => m * Qsel j + n * ((Psel j + Qsel j) / 2) with hKdef
  have hKint : ∀ j : ℕ, (K j : ℝ) = (m : ℝ) * (Qsel j : ℝ) + (n : ℝ) * ((Psel j : ℝ) + (Qsel j : ℝ)) / 2 := by
    intro j
    have hPQ : Even (Psel j + Qsel j) := by
      obtain ⟨u, hu⟩ := Psel_odd j
      obtain ⟨v, hv⟩ := Qsel_odd j
      exact ⟨u + v + 1, by linarith⟩
    have hdiv : ((Psel j + Qsel j) / 2 : ℤ) * 2 = Psel j + Qsel j := by
      exact Int.ediv_mul_cancel (even_iff_two_dvd.mp hPQ)
    simp only [K]
    push_cast
    have hhalf : (((Psel j + Qsel j) / 2 : ℤ) : ℝ) = ((Psel j : ℝ) + (Qsel j : ℝ)) / 2 := by
      have := congrArg (fun t : ℤ => (t : ℝ)) hdiv
      push_cast at this
      linarith
    rw [hhalf]
    ring
  have hdiff : ∀ j : ℕ, (Qsel j : ℝ) * ((m : ℝ) + (n : ℝ) * (Real.exp 1 + 1) / 2) - (K j : ℝ)
      = (n : ℝ) * deltaSel j / 2 := by
    intro j
    rw [hKint j]
    simp only [deltaSel]
    ring
  have hδ0 : Tendsto (fun j : ℕ => (n : ℝ) * deltaSel j / 2) atTop (nhds 0) := by
    have h1 := deltaSel_tendsto_zero.const_mul (n : ℝ)
    have h2 := h1.div_const 2
    have h3 : (fun j : ℕ => (n : ℝ) * deltaSel j / 2)
        = (fun j : ℕ => ((n : ℝ) * deltaSel j) / 2) := by funext j; ring
    rw [h3]
    simpa using h2
  have hsmall : ∀ᶠ j : ℕ in atTop, |(n : ℝ) * deltaSel j / 2| < 1 / 2 := by
    have habs : Tendsto (fun j : ℕ => |(n : ℝ) * deltaSel j / 2|) atTop (nhds 0) := by
      simpa using hδ0.abs
    exact habs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have heq : ∀ᶠ j : ℕ in atTop, distToNearestInt ((Qsel j : ℝ) * ((m : ℝ) + (n : ℝ) * (Real.exp 1 + 1) / 2))
      = |(n : ℝ) * deltaSel j / 2| := by
    apply hsmall.mono
    intro j hj
    have hdiffj := hdiff j
    have hK : round ((Qsel j : ℝ) * ((m : ℝ) + (n : ℝ) * (Real.exp 1 + 1) / 2)) = K j := by
      apply round_eq_iff.mpr
      constructor
      · have := abs_lt.mp hj
        linarith [hdiffj]
      · have := abs_lt.mp hj
        linarith [hdiffj]
    simp only [distToNearestInt, hK]
    rw [hdiffj]
  have hbound : ∀ᶠ j : ℕ in atTop,
      (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * ((m : ℝ) + (n : ℝ) * (Real.exp 1 + 1) / 2))
        ≤ |(n : ℝ)| / (4 * (Qsel j : ℝ)) := by
    apply (heq.and (hsmall.and (Filter.eventually_ge_atTop 1))).mono
    intro j hj
    have hdist := hj.1
    have hj1 : 1 ≤ j := hj.2.2
    have hδ := abs_deltaSel_lt j hj1
    rw [hdist]
    have habs : |(n : ℝ) * deltaSel j / 2| = |(n : ℝ)| * |deltaSel j| / 2 := by
      have h1 : (n : ℝ) * deltaSel j / 2 = ((n : ℝ) * deltaSel j) / 2 := by ring
      rw [h1, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs]
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hqpos : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j
    have hinner : |(n : ℝ)| * |deltaSel j| / 2 ≤ |(n : ℝ)| * (1 / (2 * (j : ℝ) * (Qsel j : ℝ))) / 2 := by
      have h1 : |(n : ℝ)| * |deltaSel j| ≤ |(n : ℝ)| * (1 / (2 * (j : ℝ) * (Qsel j : ℝ))) :=
        mul_le_mul_of_nonneg_left hδ.le (abs_nonneg _)
      have h2 : |(n : ℝ)| * |deltaSel j| / 2 ≤ |(n : ℝ)| * (1 / (2 * (j : ℝ) * (Qsel j : ℝ))) / 2 := by
        have := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        convert this using 1 <;> ring
      exact h2
    calc (j : ℝ) * (|(n : ℝ)| * |deltaSel j| / 2)
        ≤ (j : ℝ) * (|(n : ℝ)| * (1 / (2 * (j : ℝ) * (Qsel j : ℝ))) / 2) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = |(n : ℝ)| / (4 * (Qsel j : ℝ)) := by field_simp; ring
  have hsqueeze : Tendsto (fun j : ℕ => |(n : ℝ)| / (4 * (Qsel j : ℝ))) atTop (nhds 0) := by
    have h4Q : Tendsto (fun j : ℕ => 4 * (Qsel j : ℝ)) atTop atTop :=
      Qsel_tendsto_atTop.const_mul_atTop (by norm_num)
    exact h4Q.const_div_atTop |(n : ℝ)|
  have hnonneg : ∀ᶠ j : ℕ in atTop, 0 ≤ (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * ((m : ℝ) + (n : ℝ) * (Real.exp 1 + 1) / 2)) := by
    apply Filter.eventually_of_mem Filter.univ_mem
    intro j _
    apply mul_nonneg
    · positivity
    · exact distToNearestInt_nonneg _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqueeze hnonneg hbound

/-- **Theorem 2（分类格）**：j‖Q_j x‖→0 ⇔ x ∈ L = ℤ + ℤ(e+1)/2。 -/
theorem theorem2_classification (x : ℝ) :
    Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x)) atTop (nhds 0)
      ↔ x ∈ latticeL :=
  ⟨theorem2_necessity x, theorem2_sufficiency x⟩

/-! ## Corollary 3（定量间隙 1/4） -/

/-- 若最终 j‖Q_j x‖ ≤ c 且 0<c<1/4，则 defect 最终为 0。 -/
lemma defect_eventually_zero_of_le_lt_quarter (x : ℝ) (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 4)
    (h : ∀ᶠ j : ℕ in atTop, (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x) ≤ c) :
    ∀ᶠ j : ℕ in atTop, defect x j = 0 := by
  have heps : ∀ j : ℕ, |eps x j| = distToNearestInt ((Qsel j : ℝ) * x) := by intro j; rfl
  let g : ℕ → ℝ := fun j => 1 / ((j + 1 : ℕ) : ℝ) + (4 * (j : ℝ) + 2) / (j : ℝ) + 1 / ((j - 1 : ℕ) : ℝ)
  have hg4 : Tendsto g atTop (nhds 4) := by
    have hnat : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
      have hj1 : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) atTop atTop := by
        have hcomp : Tendsto (fun j : ℕ => j + 1) atTop atTop := tendsto_add_atTop_nat 1
        exact hnat.comp hcomp
      exact hj1.const_div_atTop 1
    have h2 : Tendsto (fun j : ℕ => (4 * (j : ℝ) + 2) / (j : ℝ)) atTop (nhds 4) := by
      have heq : ∀ᶠ j : ℕ in atTop, (4 * (j : ℝ) + 2) / (j : ℝ) = 4 + 2 / (j : ℝ) := by
        apply (Filter.eventually_ge_atTop 1).mono
        intro j hj1
        have hjne : (j : ℝ) ≠ 0 := by
          have : 0 < j := by omega
          exact_mod_cast (ne_of_gt this)
        field_simp
      have h2j : Tendsto (fun j : ℕ => 2 / (j : ℝ)) atTop (nhds 0) := hnat.const_div_atTop 2
      have hsum : Tendsto (fun j : ℕ => (4 : ℝ) + 2 / (j : ℝ)) atTop (nhds (4 + 0)) :=
        tendsto_const_nhds.add h2j
      have hsum' : Tendsto (fun j : ℕ => (4 : ℝ) + 2 / (j : ℝ)) atTop (nhds 4) := by
        convert hsum using 1; norm_num
      exact hsum'.congr' (heq.mono (fun j hj => hj.symm))
    have h3 : Tendsto (fun j : ℕ => 1 / ((j - 1 : ℕ) : ℝ)) atTop (nhds 0) := by
      have hjm1 : Tendsto (fun j : ℕ => ((j - 1 : ℕ) : ℝ)) atTop atTop := by
        have heq : ∀ᶠ j : ℕ in atTop, ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
          apply (Filter.eventually_ge_atTop 1).mono
          intro j hj1
          rw [Nat.cast_sub hj1, Nat.cast_one]
        have hsub : Tendsto (fun j : ℕ => (j : ℝ) - 1) atTop atTop := by
          rw [tendsto_atTop_atTop]
          intro B
          use ⌈B⌉₊ + 1
          intro j hj
          have hB : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
          have hjr : (⌈B⌉₊ + 1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
          have : (⌈B⌉₊ : ℝ) + 1 ≤ (j : ℝ) := by
            push_cast at hjr ⊢
            exact hjr
          linarith
        exact hsub.congr' (heq.mono (fun j hj => hj.symm))
      exact hjm1.const_div_atTop 1
    have hsum : Tendsto (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) + ((4 * (j : ℝ) + 2) / (j : ℝ) + 1 / ((j - 1 : ℕ) : ℝ)))
        atTop (nhds (0 + (4 + 0))) := h1.add (h2.add h3)
    have heq : g = (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) + ((4 * (j : ℝ) + 2) / (j : ℝ) + 1 / ((j - 1 : ℕ) : ℝ))) := by
      funext j; simp only [g]; ring
    rw [heq]
    convert hsum using 1
    norm_num
  have h4c : 4 * c < 1 := by linarith
  have hcg : Tendsto (fun j : ℕ => c * g j) atTop (nhds (c * 4)) := hg4.const_mul c
  have hcg1 : ∀ᶠ j : ℕ in atTop, c * g j < 1 := by
    have hlt : c * 4 < 1 := by linarith
    have := hcg.eventually (Iio_mem_nhds hlt)
    convert this using 1 <;> simp [mul_comm]
  have hε : ∀ᶠ j : ℕ in atTop, |eps x j| ≤ c / (j : ℝ) := by
    apply (h.and (Filter.eventually_ge_atTop 1)).mono
    intro j hj
    have hj1 : 1 ≤ j := hj.2
    have hj0 : j ≠ 0 := by omega
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj0
    have hj' : (j : ℝ) * |eps x j| ≤ c := by
      have heq := heps j
      rw [heq]
      exact hj.1
    have hdiv : (j : ℝ) * |eps x j| / (j : ℝ) ≤ c / (j : ℝ) :=
      (div_le_div_iff_of_pos_right hjpos).mpr hj'
    have heq : (j : ℝ) * |eps x j| / (j : ℝ) = |eps x j| := by field_simp
    rw [heq] at hdiv
    exact hdiv
  obtain ⟨Nε, hNε⟩ := Filter.eventually_atTop.mp hε
  obtain ⟨Ng, hNg⟩ := Filter.eventually_atTop.mp hcg1
  set M := max Nε Ng with hMdef
  set N := max M 3 + 1 with hNdef
  have hDlt : ∀ᶠ j : ℕ in atTop, |(defect x j : ℝ)| < 1 := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro j hj
    have hjmaxlt : max M 3 < j := Nat.lt_of_succ_le hj
    have hjM : M < j := lt_of_le_of_lt (le_max_left M 3) hjmaxlt
    have hj3 : 3 ≤ j := by
      have : 3 ≤ max M 3 := le_max_right M 3
      omega
    have hjNε : Nε < j := lt_of_le_of_lt (le_trans (le_max_left Nε Ng) (le_of_eq hMdef.symm)) hjM
    have hjNg : Ng ≤ j := by
      have : Ng ≤ M := le_trans (le_max_right Nε Ng) (le_of_eq hMdef.symm)
      omega
    have hjNε' : Nε ≤ j := le_of_lt hjNε
    have hjm1Nε : Nε ≤ j - 1 := Nat.le_sub_one_of_lt hjNε
    have hjp1Nε : Nε ≤ j + 1 := by omega
    have hj1 : 1 ≤ j := by omega
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hjm1pos : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j - 1)
    have hεj : |eps x j| ≤ c / (j : ℝ) := hNε j hjNε'
    have hεjp1 : |eps x (j + 1)| ≤ c / ((j + 1 : ℕ) : ℝ) := hNε (j + 1) hjp1Nε
    have hεjm1 : |eps x (j - 1)| ≤ c / ((j - 1 : ℕ) : ℝ) := hNε (j - 1) hjm1Nε
    have hcgj : c * g j < 1 := hNg j hjNg
    have hD : (defect x j : ℝ) = -eps x (j + 1) + (4 * (j : ℝ) + 2) * eps x j + eps x (j - 1) :=
      defect_identity x j hj1
    have habs : |(defect x j : ℝ)| ≤ |eps x (j + 1)| + (4 * (j : ℝ) + 2) * |eps x j| + |eps x (j - 1)| := by
      rw [hD]
      have h1 : |-eps x (j + 1) + (4 * (j : ℝ) + 2) * eps x j + eps x (j - 1)|
          ≤ |-eps x (j + 1)| + |(4 * (j : ℝ) + 2) * eps x j| + |eps x (j - 1)| := by
        apply le_trans (abs_add_le _ _)
        gcongr
        exact abs_add_le _ _
      have h2 : |-eps x (j + 1)| = |eps x (j + 1)| := abs_neg _
      have h3 : |(4 * (j : ℝ) + 2) * eps x j| = (4 * (j : ℝ) + 2) * |eps x j| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (j : ℝ) + 2)]
      linarith
    have hbound : |eps x (j + 1)| + (4 * (j : ℝ) + 2) * |eps x j| + |eps x (j - 1)| ≤ c * g j := by
      have hb1 : |eps x (j + 1)| ≤ c / ((j + 1 : ℕ) : ℝ) := hεjp1
      have hb2 : (4 * (j : ℝ) + 2) * |eps x j| ≤ (4 * (j : ℝ) + 2) * c / (j : ℝ) := by
        calc (4 * (j : ℝ) + 2) * |eps x j| ≤ (4 * (j : ℝ) + 2) * (c / (j : ℝ)) := by
              apply mul_le_mul_of_nonneg_left hεj
              positivity
          _ = (4 * (j : ℝ) + 2) * c / (j : ℝ) := by ring
      have hb3 : |eps x (j - 1)| ≤ c / ((j - 1 : ℕ) : ℝ) := hεjm1
      have hsum : |eps x (j + 1)| + (4 * (j : ℝ) + 2) * |eps x j| + |eps x (j - 1)|
          ≤ c / ((j + 1 : ℕ) : ℝ) + (4 * (j : ℝ) + 2) * c / (j : ℝ) + c / ((j - 1 : ℕ) : ℝ) :=
        add_le_add (add_le_add hb1 hb2) hb3
      have heq : c / ((j + 1 : ℕ) : ℝ) + (4 * (j : ℝ) + 2) * c / (j : ℝ) + c / ((j - 1 : ℕ) : ℝ) = c * g j := by
        simp only [g]
        ring
      linarith
    linarith
  exact int_eventually_zero_of_abs_lt_one hDlt

/-- **Corollary 3（定量间隙）**：x ∉ L ⇒ 对任意 c<1/4，不能最终 j‖Q_j x‖≤c。 -/
theorem corollary3_gap (x : ℝ) (hx : x ∉ latticeL) :
    ∀ c : ℝ, c < 1 / 4 → ¬ (∀ᶠ j : ℕ in atTop, (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x) ≤ c) := by
  intro c hc h
  by_cases hc0 : 0 < c
  · have hD := defect_eventually_zero_of_le_lt_quarter x c hc0 hc h
    exact hx (mem_latticeL_of_eventually_defect_zero x hD)
  · have hc0' : c ≤ 0 := le_of_not_gt hc0
    have hzero : ∀ᶠ j : ℕ in atTop, (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x) = 0 := by
      apply (h.and (Filter.eventually_ge_atTop 1)).mono
      intro j hj
      have hnn : 0 ≤ (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x) := by
        apply mul_nonneg
        · positivity
        · exact distToNearestInt_nonneg _
      linarith
    have htend : Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x)) atTop (nhds 0) := by
      have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
      exact hconst.congr' (hzero.mono (fun j hj => hj.symm))
    exact hx (theorem2_necessity x htend)

end

/-! ## 公理审计 -/

#print axioms Qsel_pos
#print axioms Psel_rec
#print axioms Qsel_rec
#print axioms sel_determinant
#print axioms Psel_odd
#print axioms Qsel_odd
#print axioms Qsel_double
#print axioms Qsel_succ_coprime
#print axioms Qsel_tendsto_atTop
#print axioms Psel_div_Qsel_tendsto_exp
#print axioms defect_identity
#print axioms eps_div_Qsel_tendsto_zero
#print axioms propagate
#print axioms mem_latticeL_of_eventually_defect_zero
#print axioms defect_eventually_zero_of_tendsto
#print axioms theorem2_necessity
#print axioms theorem2_sufficiency
#print axioms theorem2_classification
#print axioms defect_eventually_zero_of_le_lt_quarter
#print axioms corollary3_gap

end Classification