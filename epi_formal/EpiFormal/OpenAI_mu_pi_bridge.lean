import Mathlib
import EpiFormal.Measure
import EpiFormal.MeiburgConvergence
import EpiFormal.FlintHills

/-!
# 独立内核检验：OpenAI μ(π)=2 声称与本项目的对接（条件性桥）

## 背景与诚实声明

2026-09-24 OpenAI 在 openai/math 仓库发布预印本 *The Irrationality Exponent of π Is 2*
（family 017），附 Lean 形式化 `OAI/NumberTheory/PiExponent/`，工具链 Lean v4.34.1，
mathlib4 锁定提交 d13f23b723b8a846827a245b89c10fc7d3f11612，依赖 30+ 外部库，
证明走代数几何/上同调/jets 路线（AdmissibleMatrixInterpolation.globalInterpolation）。

**验证状态（截至 2026-11，MathWorld 记载）**：独立专家对完整证明的验证尚未见报道；
OpenAI 仓库 README 自承「部分未形式化结果可能有问题」。故 μ(π)=2 目前是**声称（claim），
不是已确立定理**。完整编译该证明需重建整个 OAI 库（与本项目 mathlib v4.35.0 缓存不兼容），
本机不可行；本文件**不声称**已独立验证 OpenAI 的证明。

## 本文件做什么（完全在本项目内核内可验证）

1. 原样纳入 OpenAI `Statement.lean` 的定义（只依赖 Mathlib），内核检查良构性。
2. 证明 OpenAI 的最终下界陈述 `PiEventualLowerBound` 蕴含本项目 `irrMeasure π ≤ 2`。
3. 用本项目**已机器验证**的 `meiburg_criterion` 接出**条件性定理**：
   若 OpenAI 的 μ(π)=2 陈述成立，则 Flint Hills 收敛。

**e+π 无理性仍开放**；本文件不判定它。条件性桥的前提（μ(π)=2）本身是未验证声称。
-/

open Real Set Filter

namespace OpenAIBridge

/-! ## 1. OpenAI Statement.lean 的定义（原样纳入，仅依赖 Mathlib） -/

def GoodRationalApproximations (x ν : ℝ) : Set ℚ :=
  {r | 2 ≤ r.den ∧ 0 < |x - (r : ℝ)| ∧ |x - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}

def ApproximationExponents (x : ℝ) : Set ℝ :=
  {ν | 0 < ν ∧ (GoodRationalApproximations x ν).Infinite}

noncomputable def irrationalityExponent (x : ℝ) : ℝ := sSup (ApproximationExponents x)

def EventualLowerBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
    ∀ (p : ℤ) (q : ℕ), Q ≤ q → (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)|

def PiEventualLowerBound : Prop := EventualLowerBound Real.pi

/-! ## 2. 对接：OpenAI 最终下界 ⇒ 本项目 irrMeasure π ≤ 2 -/

/-- 固定分母 q≥1，满足 |x − p/q| < c 的分子 p 构成有限集（有界整数集）。 -/
lemma finite_numerators (x : ℝ) (q : ℕ) (hq : 1 ≤ q) (c : ℝ) :
    {p : ℤ | |x - (p : ℝ) / (q : ℝ)| < c}.Finite := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hsub : {p : ℤ | |x - (p : ℝ) / (q : ℝ)| < c} ⊆
      Set.Icc ⌊(q : ℝ) * (x - c)⌋ ⌈(q : ℝ) * (x + c)⌉ := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    have habs := abs_lt.mp hp
    constructor
    · have hlower : (q : ℝ) * (x - c) < (p : ℝ) := by
        have : x - c < (p : ℝ) / (q : ℝ) := by linarith
        calc (q : ℝ) * (x - c) < (q : ℝ) * ((p : ℝ) / (q : ℝ)) := by gcongr
          _ = (p : ℝ) := by field_simp
      exact_mod_cast (Int.floor_le _).trans (le_of_lt hlower)
    · have hupper : (p : ℝ) < (q : ℝ) * (x + c) := by
        have : (p : ℝ) / (q : ℝ) < x + c := by linarith
        calc (p : ℝ) = (q : ℝ) * ((p : ℝ) / (q : ℝ)) := by field_simp
          _ < (q : ℝ) * (x + c) := by gcongr
      have := hupper.trans_le (Int.le_ceil _)
      exact_mod_cast this.le
  exact (Set.finite_Icc _ _).subset hsub

/-- 最终下界 ⇒ 对 ν>2，好逼近对集有限。
    全局界：分母 q<Q；分子 |p| < Q·(|x|+1)（因 q≥1,ν>0 ⇒ q^(−ν)≤1）。
    故好逼近对落在有限矩形积内。 -/
lemma apprPairs_finite_of_eventualLowerBound {x : ℝ}
    (h : EventualLowerBound x) {ν : ℝ} (hν : 2 < ν) :
    (apprPairs x ν).Finite := by
  obtain ⟨Q, hQ2, hQ⟩ := h ν hν
  set M : ℤ := ⌈(Q : ℝ) * (|x| + 1)⌉ with hMdef
  -- 好逼近对 ⊆ Icc (−M) M ×ˢ Icc 0 (Q−1)
  have hsub : apprPairs x ν ⊆
      Set.Icc (-M) M ×ˢ Set.Icc (0 : ℕ) (Q - 1) := by
    intro pq hpq
    simp only [apprPairs, Set.mem_setOf_eq] at hpq
    have hqpos : 0 < pq.2 := hpq.1
    have hlt : pq.2 < Q := by
      by_contra hge
      push Not at hge
      have hlower := hQ pq.1 pq.2 hge
      linarith [hpq.2]
    have hq1 : (1 : ℝ) ≤ (pq.2 : ℝ) := by exact_mod_cast (by omega : 1 ≤ pq.2)
    have hνpos : (0 : ℝ) ≤ ν := by linarith
    have hpow : (pq.2 : ℝ) ^ (-ν) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
    have happrox : |x - (pq.1 : ℝ) / (pq.2 : ℝ)| < 1 := by linarith [hpq.2, hpow]
    have habs := abs_lt.mp happrox
    -- |p/q| < |x| + 1 ⇒ |p| < q(|x|+1) ≤ Q(|x|+1)
    have hpq_bound : |(pq.1 : ℝ)| < (Q : ℝ) * (|x| + 1) := by
      have h1 : |(pq.1 : ℝ) / (pq.2 : ℝ)| < |x| + 1 := by
        calc |(pq.1 : ℝ) / (pq.2 : ℝ)|
            = |(pq.1 : ℝ) / (pq.2 : ℝ) - x + x| := by ring_nf
          _ ≤ |(pq.1 : ℝ) / (pq.2 : ℝ) - x| + |x| := abs_add_le _ _
          _ = |x - (pq.1 : ℝ) / (pq.2 : ℝ)| + |x| := by rw [abs_sub_comm]
          _ < 1 + |x| := by gcongr
          _ = |x| + 1 := by ring
      have h2 : |(pq.1 : ℝ)| = (pq.2 : ℝ) * |(pq.1 : ℝ) / (pq.2 : ℝ)| := by
        have hqne : (pq.2 : ℝ) ≠ 0 := by exact_mod_cast (by omega : pq.2 ≠ 0)
        rw [abs_div, abs_of_pos (by exact_mod_cast hqpos : (0:ℝ) < (pq.2:ℝ))]
        field_simp
      calc |(pq.1 : ℝ)| = (pq.2 : ℝ) * |(pq.1 : ℝ) / (pq.2 : ℝ)| := h2
        _ < (pq.2 : ℝ) * (|x| + 1) := by gcongr
        _ ≤ (Q : ℝ) * (|x| + 1) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast (show pq.2 ≤ Q by omega)
          · positivity
    constructor
    · -- −M ≤ p ≤ M
      simp only [Set.mem_Icc]
      have hM : (Q : ℝ) * (|x| + 1) ≤ (M : ℝ) := by
        rw [hMdef]; exact Int.le_ceil _
      have hpR : |(pq.1 : ℝ)| ≤ (M : ℝ) := by linarith
      constructor
      · have : -(M : ℝ) ≤ (pq.1 : ℝ) := by linarith [abs_le.mp hpR]
        exact_mod_cast this
      · have : (pq.1 : ℝ) ≤ (M : ℝ) := by linarith [abs_le.mp hpR]
        exact_mod_cast this
    · -- 0 ≤ q ≤ Q−1
      simp only [Set.mem_Icc]
      constructor
      · omega
      · omega
  exact (Set.Finite.prod (Set.finite_Icc _ _) (Set.finite_Icc _ _)).subset hsub

/-- 最终下界 ⇒ apprSet x ⊆ [0,2]。 -/
lemma apprSet_subset_Icc_of_eventualLowerBound {x : ℝ}
    (h : EventualLowerBound x) : apprSet x ⊆ Set.Icc (0 : NNReal) 2 := by
  intro ν hν
  simp only [apprSet, Set.mem_setOf_eq] at hν
  simp only [Set.mem_Icc]
  constructor
  · exact NNReal.coe_nonneg _
  · by_contra hgt
    push Not at hgt
    have hν2 : (2 : ℝ) < (ν : ℝ) := by exact_mod_cast hgt
    exact hν (apprPairs_finite_of_eventualLowerBound h hν2)

/-- **对接定理**：OpenAI 最终下界 ⇒ 本项目 irrMeasure π ≤ 2。 -/
theorem irrMeasure_le_two_of_PiEventualLowerBound
    (h : PiEventualLowerBound) : irrMeasure Real.pi ≤ 2 := by
  have hsub := apprSet_subset_Icc_of_eventualLowerBound h
  have himage : (fun ν : NNReal => (ν : ENNReal)) '' apprSet Real.pi ⊆
      (fun ν : NNReal => (ν : ENNReal)) '' Set.Icc (0 : NNReal) 2 :=
    Set.image_mono hsub
  have hIcc : sSup ((fun ν : NNReal => (ν : ENNReal)) '' Set.Icc (0 : NNReal) 2) = 2 := by
    apply le_antisymm
    · apply sSup_le
      intro y hy
      obtain ⟨ν, hν, rfl⟩ := hy
      have : (ν : ENNReal) ≤ (2 : NNReal) := by exact_mod_cast hν.2
      simpa using this
    · have h2 : (2 : NNReal) ∈ Set.Icc (0 : NNReal) 2 := by simp
      exact le_sSup ⟨2, h2, rfl⟩
  calc irrMeasure Real.pi
      = sSup ((fun ν : NNReal => (ν : ENNReal)) '' apprSet Real.pi) := rfl
    _ ≤ sSup ((fun ν : NNReal => (ν : ENNReal)) '' Set.Icc (0 : NNReal) 2) := sSup_le_sSup himage
    _ = 2 := hIcc

/-! ## 3. 条件性桥：若 OpenAI μ(π)=2 成立 ⇒ Flint Hills 收敛 -/

/-- **条件性定理**：若 OpenAI 的 π 最终下界（μ(π)=2）成立，则 Flint Hills 收敛。
    前提未独立验证；结论依赖本项目已验证的 Meiburg 判据。 -/
theorem flint_hills_of_PiEventualLowerBound
    (h : PiEventualLowerBound) : FlintHillsConjecture := by
  apply meiburg_criterion
  calc irrMeasure Real.pi ≤ 2 := irrMeasure_le_two_of_PiEventualLowerBound h
    _ < 5 / 2 := by
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num

end OpenAIBridge

/-! ## 公理审计 -/

#print axioms OpenAIBridge.finite_numerators
#print axioms OpenAIBridge.apprPairs_finite_of_eventualLowerBound
#print axioms OpenAIBridge.irrMeasure_le_two_of_PiEventualLowerBound
#print axioms OpenAIBridge.flint_hills_of_PiEventualLowerBound