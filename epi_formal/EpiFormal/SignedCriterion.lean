import Mathlib
import EpiFormal.EulerConvergents
import EpiFormal.Measure
import EpiFormal.MeiburgConvergence
import EpiFormal.Alekseyev

/-!
# H 组：补充页 Proposition 3 符号判据（双向）—— 联合编译归一版

来源：用户修订包补充材料第 1 页（epi-pdf-qa/supp.pdf），纸面证明，本文件首次 Lean 验证。

## 联合编译归一说明（2026-11-14，总执行）

本文件由并发子任务 H 的 `SignedCriterion.lean` 归一而来：
- **删除自建地基**（原 `pairSel` 双步递归与全部地基引理）与**两条自建公理**，
  改为 `import EpiFormal.EulerConvergents`（A 组地基，唯一地基）。
- H 的 `pairSel` 与 A 的 `selPair` 数值序列完全一致
  （P: 1,3,19,193,2721,...；Q: 1,1,7,71,1001,...），仅定义方式不同。
  本文件用 A 的 `Psel`/`Qsel`/`deltaSel` 与公理，重证 H 主体所需的桥接引理
  `Qsel_pos_all`（全下标正性，A 的 `Qsel_pos` 仅 j≥1，此处补 j=0）。
- Prop3 主体证明（forward/converse/双向判据/绝对值注记）**原样保留**，数学内容不变。
- 公理唯一来源为 A 的 `deltaSel_tendsto_zero`、`abs_deltaSel_lt`；本文件不新增任何公理。

## 诚实声明（必须保留）

1. **e+π 无理性仍是开放问题**。本文件只机器验证一个等价判据
   （e+π ∈ ℚ ↔ 存在正整数 B 使符号残差等式最终成立），不证明也不暗示 e+π 无理。
2. 原文 Open step（逐字保留）：
   "For each B, infinitely many positive products (B Q_j π − [B Q_j π]) d_j > 0
   would suffice. No such estimate is established here.
   Taking absolute values loses the sign: e and −e give identical absolute errors."
   该**符号估计未建立，仍开放**。本文件不试图证明它（见文件末节）。
-/

open Filter Topology Real

-- 整数代数归纳 / ring / nlinarith 较重，放宽确定性心跳上限（避免误判超时）。
set_option maxHeartbeats 1600000

namespace EpiFormalH

/-! ## 地基桥接：取用 A 的 Psel/Qsel/deltaSel，补全下标正性 -/

-- A 的 Psel/Qsel/deltaSel 直接可用（顶层定义）。
-- H 主体用到全下标正性 Qsel_pos_all（含 j=0）；A 的 Qsel_pos 仅 j≥1，此处补 j=0。

/-- Q_j 恒正（含占位 j=0）。由 A 的配对正性引理 selPair_pos_odd 取第一分量。 -/
lemma Qsel_pos_all (j : ℕ) : 0 < Qsel j :=
  (selPair_pos_odd 1 1 (by norm_num) (by norm_num) odd_one odd_one j).1

lemma Qsel_pos (j : ℕ) (hj : 1 ≤ j) : 0 < Qsel j := Qsel_pos_all j

/-! ## Proposition 3：符号判据 -/

/-- 符号残差：B·Q_j·π 减去其最近整数。 -/
noncomputable def signedResidual (B : ℕ) (j : ℕ) : ℝ :=
  (B : ℝ) * (Qsel j : ℝ) * Real.pi - (round ((B : ℝ) * (Qsel j : ℝ) * Real.pi) : ℝ)

/-- 关键代数恒等式：B·Q_j·π = (A·Q_j − B·P_j) − B·δ_j（当 e+π = A/B）。 -/
lemma signedResidual_decomp (A : ℤ) (B : ℕ) (j : ℕ)
    (hsum : Real.exp 1 + Real.pi = (A : ℝ) / (B : ℝ)) (hB : (B : ℝ) ≠ 0) :
    (B : ℝ) * (Qsel j : ℝ) * Real.pi =
    ((A * Qsel j - (B : ℤ) * Psel j : ℤ) : ℝ) - (B : ℝ) * deltaSel j := by
  have hpi : Real.pi = (A : ℝ) / (B : ℝ) - Real.exp 1 := by linarith
  rw [hpi]
  simp only [deltaSel]
  push_cast
  field_simp
  ring

/-- 整数候选最终是最近整数：|x − z| < 1/2 ⇒ round x = z。
用 round_le 的最小性 + 不同整数间距 ≥ 1。 -/
lemma round_eq_of_abs_sub_lt_half (x : ℝ) (z : ℤ) (h : |x - (z : ℝ)| < 1 / 2) :
    round x = z := by
  by_contra hne
  have hmin : |x - (round x : ℝ)| ≤ |x - (z : ℝ)| := round_le x z
  have hlt : |x - (round x : ℝ)| < 1 / 2 := lt_of_le_of_lt hmin h
  have hdist : |(round x : ℝ) - (z : ℝ)| < 1 := by
    have htri : |(round x : ℝ) - (z : ℝ)| ≤ |x - (z : ℝ)| + |x - (round x : ℝ)| := by
      have hid : (round x : ℝ) - (z : ℝ) = (x - (z : ℝ)) - (x - (round x : ℝ)) := by ring
      rw [hid]
      exact abs_sub _ _
    linarith
  have hge1 : (1 : ℝ) ≤ |(round x : ℝ) - (z : ℝ)| := by
    have hne' : round x - z ≠ 0 := by
      intro h0
      apply hne
      omega
    have := Int.one_le_abs hne'
    have hcast : ((round x - z : ℤ) : ℝ) = (round x : ℝ) - (z : ℝ) := by push_cast; ring
    rw [← hcast]
    exact_mod_cast this
  linarith

/-- forward：e+π = A/B（B>0）⇒ 最终 signedResidual B j = −B·δ_j。 -/
lemma proposition3_forward (A : ℤ) (B : ℕ) (hB : 0 < B)
    (hsum : Real.exp 1 + Real.pi = (A : ℝ) / (B : ℝ)) :
    ∀ᶠ j : ℕ in atTop, signedResidual B j = -(B : ℝ) * deltaSel j := by
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  -- |B·δ_j| < 1/2 最终成立（δ_j → 0）
  have hsmall : ∀ᶠ j : ℕ in atTop, |(B : ℝ) * deltaSel j| < 1 / 2 := by
    have hlim : Tendsto (fun j => |(B : ℝ) * deltaSel j|) atTop (nhds 0) := by
      simpa [mul_comm] using (deltaSel_tendsto_zero.const_mul (B : ℝ)).abs
    exact hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  apply hsmall.mono
  intro j hj
  have hdecomp := signedResidual_decomp A B j hsum hB'
  set z : ℤ := A * Qsel j - (B : ℤ) * Psel j with hzdef
  have hround : round ((B : ℝ) * (Qsel j : ℝ) * Real.pi) = z := by
    apply round_eq_of_abs_sub_lt_half
    have hid : (B : ℝ) * (Qsel j : ℝ) * Real.pi - (z : ℝ) = -((B : ℝ) * deltaSel j) := by
      rw [hdecomp]
      simp only [hzdef]
      push_cast
      ring
    rw [hid, abs_neg]
    exact hj
  simp only [signedResidual, hround]
  rw [hdecomp]
  simp only [hzdef]
  push_cast
  ring

/-- converse 核心：单个 j 的精确等式 ⇒ B·Q_j·(e+π) ∈ ℤ。 -/
lemma proposition3_converse_core (B : ℕ) (j : ℕ)
    (h : signedResidual B j = -(B : ℝ) * deltaSel j) :
    ∃ m : ℤ, (B : ℝ) * (Qsel j : ℝ) * (Real.exp 1 + Real.pi) = (m : ℝ) := by
  use round ((B : ℝ) * (Qsel j : ℝ) * Real.pi) + (B : ℤ) * Psel j
  simp only [signedResidual, deltaSel] at h ⊢
  push_cast at h ⊢
  linarith

/-- converse：某一个 j 的精确等式 ⇒ e+π ∈ ℚ（B>0，Q_j≠0）。
原文「even one exact equality gives B Q_j(e+π) in Z」，除以 Q_j≠0 得有理性。 -/
lemma proposition3_converse (B : ℕ) (hB : 0 < B) (j : ℕ)
    (h : signedResidual B j = -(B : ℝ) * deltaSel j) :
    ∃ q : ℚ, Real.exp 1 + Real.pi = (q : ℝ) := by
  obtain ⟨m, hm⟩ := proposition3_converse_core B j h
  have hq0 : (Qsel j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Qsel_pos_all j)
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  have hprod : (B : ℝ) * (Qsel j : ℝ) ≠ 0 := mul_ne_zero hB' hq0
  have hsum : Real.exp 1 + Real.pi = (m : ℝ) / ((B : ℝ) * (Qsel j : ℝ)) := by
    have hid2 : (Real.exp 1 + Real.pi) * ((B : ℝ) * (Qsel j : ℝ)) = (m : ℝ) := by
      linarith [hm]
    exact (eq_div_iff hprod).mpr hid2
  refine ⟨(m : ℚ) / ((B : ℚ) * (Qsel j : ℚ)), ?_⟩
  rw [hsum]
  push_cast
  ring

/-- **Proposition 3（符号判据，双向，机器验证）**：
e+π ∈ ℚ ↔ ∃ B>0，最终 signedResidual B j = −B·δ_j。
正向用 proposition3_forward；反向用 proposition3_converse
（∀ᶠ ⇒ 存在某个 j，atTop 非空）。 -/
theorem proposition3_signed_criterion :
    (∃ q : ℚ, Real.exp 1 + Real.pi = (q : ℝ)) ↔
    (∃ B : ℕ, 0 < B ∧ ∀ᶠ j : ℕ in atTop, signedResidual B j = -(B : ℝ) * deltaSel j) := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h
    obtain ⟨A, B, hB, hqAB⟩ : ∃ A : ℤ, ∃ B : ℕ, 0 < B ∧ q = (A : ℚ) / (B : ℚ) := by
      refine ⟨q.num, q.den, q.den_pos, ?_⟩
      exact (Rat.num_div_den q).symm
    use B, hB
    have hsum : Real.exp 1 + Real.pi = (A : ℝ) / (B : ℝ) := by
      rw [hq, hqAB]
      push_cast
      ring
    exact proposition3_forward A B hB hsum
  · intro h
    obtain ⟨B, hB, hev⟩ := h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    exact proposition3_converse B hB N (hN N (le_refl N))

/-! ## 辅助观察：绝对值判据无法区分 e 与 −e（不是开放步骤的解决）

最终等式成立时 |signedResidual B j| = B·|δ_j|，与 δ_j 的符号无关。
因此任何只依赖绝对值的判据对 e 与 −e 给出相同结果——这正是原文
"Taking absolute values loses the sign" 的形式化注记。
**这不构成对开放符号估计的证明。** -/

lemma abs_signedResidual_eventually (B : ℕ)
    (h : ∀ᶠ j : ℕ in atTop, signedResidual B j = -(B : ℝ) * deltaSel j) :
    ∀ᶠ j : ℕ in atTop, |signedResidual B j| = (B : ℝ) * |deltaSel j| := by
  apply h.mono
  intro j hj
  rw [hj, abs_mul, abs_neg,
    abs_of_nonneg (by exact_mod_cast (Nat.zero_le B) : (0 : ℝ) ≤ (B : ℝ))]

/-! ## 开放步骤的如实记录（不试图证明）

原文 Open step：
"For each B, infinitely many positive products (B Q_j π − [B Q_j π]) d_j > 0
would suffice. No such estimate is established here."

形式化坐标：对每个 B>0，命题
  ∃ᶠ j in atTop, signedResidual B j * deltaSel j > 0
（无穷多正乘积）**未建立**。若它成立，结合 proposition3_signed_criterion
可推出 e+π 无理（反证：若有理，最终 signedResidual = −B·δ_j，
乘积 = −B·δ_j² ≤ 0，与无穷多正乘积矛盾）。但该符号估计本身是开放问题，
本文件不声称证明它。e+π 无理性仍开放。
-/

end EpiFormalH

/-! ## 公理审计（联合编译归一版） -/

#print axioms EpiFormalH.Qsel_pos_all
#print axioms EpiFormalH.round_eq_of_abs_sub_lt_half
#print axioms EpiFormalH.proposition3_forward
#print axioms EpiFormalH.proposition3_converse_core
#print axioms EpiFormalH.proposition3_converse
#print axioms EpiFormalH.proposition3_signed_criterion
#print axioms EpiFormalH.abs_signedResidual_eventually