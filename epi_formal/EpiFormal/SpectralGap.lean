import Mathlib
import EpiFormal.EulerConvergents
import EpiFormal.Classification

/-!
# 第二阶段：沿 e 收敛子分母的逼近谱隙与水平集维数（SpectralGap）

研究逼近指数 Lam(x) = limsup_j j·‖Q_j x‖（ENNReal 值），其中 Q_j 是 e 的选定
收敛子分母，‖y‖ = distToNearestInt y。复用第一阶段已机器验证的分类定理与间隙定理。

## 可信度分层
- 机器验证：谱隙（Lam(x)=0 或 Lam(x)≥1/4）、阈下水平集 = L、可数水平集维数 0。
- 本文件不声称证明 e+π 无理性（仍开放）。

## 与文献的关系
现象（谱隙+阈下维0）有经典先例（Lagrange 谱、Kraaikamp–Liardet 1991、
Bíró–Deshouillers–Sós 2001）；本实例的新颖签名是「e 收敛子分母子列 + 权重 j +
格 L=ℤ+ℤ(e+1)/2 + sharp 1/4」。详见独立论文。
-/

open Real Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace SpectralGap

noncomputable section

/-- 实值逼近序列 a_j(x) = j·‖Q_j x‖（非负）。 -/
def apprSeq (x : ℝ) (j : ℕ) : ℝ := (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x)

lemma apprSeq_nonneg (x : ℝ) (j : ℕ) : 0 ≤ apprSeq x j :=
  mul_nonneg (Nat.cast_nonneg _) (distToNearestInt_nonneg _)

/-- ENNReal 值逼近序列。 -/
def apprSeqE (x : ℝ) (j : ℕ) : ℝ≥0∞ := ENNReal.ofReal (apprSeq x j)

/-- 逼近指数 Lam(x) = limsup_j ofReal(a_j(x))（ENNReal 值）。 -/
def apprExponent (x : ℝ) : ℝ≥0∞ := limsup (apprSeqE x) atTop

/-- 水平集 {x | Lam(x) ≤ c}。 -/
def levelSet (c : ℝ≥0∞) : Set ℝ := {x | apprExponent x ≤ c}

/-! ## 谱隙 -/

/-- ofReal(a_j)→0 ⇔ a_j→0（非负）。 -/
lemma tendsto_ofReal_zero_iff (x : ℝ) :
    Tendsto (apprSeqE x) atTop (nhds 0) ↔ Tendsto (apprSeq x) atTop (nhds 0) := by
  constructor
  · intro h
    have hto : Tendsto ENNReal.toReal (nhds (0 : ℝ≥0∞)) (nhds 0) := by
      have := ENNReal.tendsto_toReal (a := 0) (by simp)
      simpa using this
    have hcomp : Tendsto (ENNReal.toReal ∘ apprSeqE x) atTop (nhds 0) := hto.comp h
    have heq : ENNReal.toReal ∘ apprSeqE x = apprSeq x := by
      funext j
      simp [apprSeqE, ENNReal.toReal_ofReal (apprSeq_nonneg x j)]
    rw [heq] at hcomp
    exact hcomp
  · intro h
    have := ENNReal.tendsto_ofReal h
    have heq : (fun j => ENNReal.ofReal (apprSeq x j)) = apprSeqE x := by funext j; rfl
    rw [heq] at this
    simpa using this

/-- Lam(x)=0 ⇔ a_j(x)→0。 -/
lemma apprExponent_eq_zero_iff (x : ℝ) :
    apprExponent x = 0 ↔ Tendsto (apprSeq x) atTop (nhds 0) := by
  rw [← tendsto_ofReal_zero_iff]
  constructor
  · intro h
    -- Lam=0 ⇒ 对任意 ε>0 最终 ofReal(a_j)≤ε ⇒ 趋于0（ENNReal）
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hev : ∀ᶠ j : ℕ in atTop, apprSeqE x j < ε :=
      (Filter.limsup_le_iff (u := apprSeqE x) (f := atTop) (x := 0)).mp
        (le_of_eq h) ε hε
    exact hev.mono (fun _ hj => le_of_lt hj)
  · intro h
    exact h.limsup_eq

/-- **谱隙定理**：Lam(x)=0 或 Lam(x)≥1/4。即值域 ⊆ {0}∪[1/4,∞]。 -/
theorem spectral_gap (x : ℝ) : apprExponent x = 0 ∨ (1 / 4 : ℝ≥0∞) ≤ apprExponent x := by
  by_cases hx : x ∈ Classification.latticeL
  · left
    rw [apprExponent_eq_zero_iff]
    exact (Classification.theorem2_classification x).mpr hx
  · right
    apply le_of_not_gt
    intro hlt
    -- hlt : Lam(x) < 1/4 = ofReal(1/4)，故 Lam(x) ≠ ⊤
    have hne : apprExponent x ≠ ⊤ := ne_of_lt (lt_trans hlt (by norm_num))
    set L := (apprExponent x).toReal with hLdef
    have hL : L < 1 / 4 := by
      have := (ENNReal.toReal_lt_toReal hne (by norm_num : (1 / 4 : ℝ≥0∞) ≠ ⊤)).mpr hlt
      simpa [L] using this
    obtain ⟨c, hcL, hc14⟩ := exists_between hL
    have hcpos : (0 : ℝ) < c := lt_of_le_of_lt (by
      have : 0 ≤ L := ENNReal.toReal_nonneg
      linarith) hcL
    have hLc : apprExponent x < ENNReal.ofReal c := by
      rw [← ENNReal.ofReal_toReal hne]
      exact ENNReal.ofReal_lt_ofReal_iff hcpos |>.mpr hcL
    -- Lam < ofReal c ⇒ 最终 ofReal(a_j) < ofReal c
    have hev : ∀ᶠ j : ℕ in atTop, apprSeqE x j < ENNReal.ofReal c :=
      eventually_lt_of_limsup_lt hLc
    have hev' : ∀ᶠ j : ℕ in atTop, apprSeq x j ≤ c := by
      filter_upwards [hev] with j hj
      have := (ENNReal.ofReal_lt_ofReal_iff hcpos).mp hj
      exact le_of_lt this
    have hgap := Classification.corollary3_gap x hx c hc14
    exact hgap (by simpa [apprSeq] using hev')

/-! ## 阈下水平集 -/

/-- **阈下水平集 = L**：c<1/4 时 {Lam≤c}=L。 -/
theorem levelSet_below_eq_lattice (c : ℝ≥0∞) (hc : c < 1 / 4) :
    levelSet c = Classification.latticeL := by
  ext x
  simp only [levelSet, mem_ofPred_eq]
  constructor
  · intro h
    by_contra hx
    rcases spectral_gap x with h0 | hge
    · have htend := (apprExponent_eq_zero_iff x).mp h0
      exact hx ((Classification.theorem2_classification x).mp htend)
    · have : (1 / 4 : ℝ≥0∞) ≤ c := le_trans hge h
      exact (not_le.mpr hc) this
  · intro hx
    have htend := (Classification.theorem2_classification x).mpr hx
    have h0 : apprExponent x = 0 := (apprExponent_eq_zero_iff x).mpr htend
    rw [h0]
    exact bot_le

/-- 格 L = ℤ + ℤ(e+1)/2 可数。 -/
lemma latticeL_countable : (Classification.latticeL).Countable := by
  have h : Classification.latticeL =
      (fun p : ℤ × ℤ => (p.1 : ℝ) + (p.2 : ℝ) * (Real.exp 1 + 1) / 2) '' Set.univ := by
    ext x
    simp only [Classification.latticeL, mem_ofPred_eq, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨(m, n), rfl⟩
    · rintro ⟨⟨m, n⟩, rfl⟩
      exact ⟨m, n, rfl⟩
  rw [h]
  exact (Set.countable_univ.image _)

/-- **可数水平集维数 0**：c<1/4 时 dimH{Lam≤c}=0。 -/
theorem dimH_levelSet_below (c : ℝ≥0∞) (hc : c < 1 / 4) :
    dimH (levelSet c) = 0 := by
  rw [levelSet_below_eq_lattice c hc]
  exact latticeL_countable.dimH_zero

end

end SpectralGap

/-! ## 公理审计 -/

#print axioms SpectralGap.apprExponent_eq_zero_iff
#print axioms SpectralGap.spectral_gap
#print axioms SpectralGap.levelSet_below_eq_lattice
#print axioms SpectralGap.latticeL_countable
#print axioms SpectralGap.dimH_levelSet_below