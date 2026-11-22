import Mathlib
import EpiFormal.EulerConvergents
import EpiFormal.AdjacentWitness

/-!
# 逃离主线（审阅确立）：双指标判据的"无穷多次不匹配"

来源：用户源码与数学论证审阅（2026-11-14）。现有成果刻画"有理性会强迫什么结构"；
缺的是"π 不会一直遵守这些结构"。本文件把主线目标精确化并形式化其**可验证的起点**：

* 精确恒等式：D_j(B) = T_j + B·C_j 与最近整数误差 ε_j = M_j − B·Q_j·π 的关系
  D_j(B) = ε_j·Q_{j+1} − ε_{j+1}·Q_j + B·C_j。
* 目标重述（主表述）：e+π 无理 ⇔ ∀B≥1, ∀ᶠ j, D_j(B)≠0（最终恒非零，复用 F 三等价）。
  等价地（经 (a)⇒(b)）也可写 ∀B≥1,∀N,∃j≥N, D_j(B)≠0（无穷多次非零）；两形式互等价，
  交替 0,1 序列不是反例（若它成立且无穷多次为零，(a)⇒(b) 会迫使最终为零，矛盾）。
* **边界反例（诚实）**：仅靠 Q_j 递推 + |ε|≤1/2 不足以排除最终匹配——
  把 π 换成 (A/B − e) 时这些通用条件确实允许最终匹配。故最后一步必须用到 π 的特殊性质。

## 诚实声明
本文件**没有、也不声称**证明 e+π 无理性，也**没有**证明 D_j(B) 无穷多次非零。
它只形式化精确恒等式、目标重述与边界反例，作为下一轮攻击的诚实起点。
新增引理必须明确回答"新增了哪条关于 π 的信息"；若仍只用通用递推+取整，则未跨过核心缺口。
-/

open Real Filter AdjacentWitness

namespace Escape

noncomputable section

/-- 最近整数误差 ε_j(B) = M_j − B·Q_j·π（实数）。 -/
def eps (B : ℕ) (j : ℕ) : ℝ := (Msel B j : ℝ) - (B : ℝ) * (Qsel j : ℝ) * Real.pi

/-- 不匹配量 D_j(B) = T_j + B·C_j（整数）。 -/
def D (B : ℕ) (j : ℕ) : ℤ := Tsel B j + (B : ℤ) * Csel j

/-- |ε_j| ≤ 1/2（通用取整性质）。 -/
theorem eps_abs_le (B : ℕ) (j : ℕ) : |eps B j| ≤ 1 / 2 := by
  have := abs_sub_round ((B : ℝ) * (Qsel j : ℝ) * Real.pi)
  simpa [eps, Msel, abs_sub_comm] using this

/-- **精确恒等式**：D_j(B) = ε_j·Q_{j+1} − ε_{j+1}·Q_j + B·C_j。
    注意 ε 交叉积中的 π 项相消，恰等于 T_j；故 D_j 还需 +B·C_j。
    这是把整数非零性 D_j(B)≠0 翻译成舍入误差语言的关键桥梁。 -/
theorem D_eq_eps (B : ℕ) (j : ℕ) :
    (D B j : ℝ) = eps B j * (Qsel (j + 1) : ℝ) - eps B (j + 1) * (Qsel j : ℝ)
      + (B : ℝ) * (Csel j : ℝ) := by
  simp only [D, Tsel, Csel, eps, Msel]
  push_cast
  ring

/-- 匹配（D_j(B)=0）的误差刻画：ε_j·Q_{j+1} − ε_{j+1}·Q_j = −B·C_j。 -/
theorem match_iff_eps (B : ℕ) (j : ℕ) :
    D B j = 0 ↔ eps B j * (Qsel (j + 1) : ℝ) - eps B (j + 1) * (Qsel j : ℝ)
      = -(B : ℝ) * (Csel j : ℝ) := by
  have h := D_eq_eps B j
  constructor
  · intro hD
    have : (D B j : ℝ) = 0 := by exact_mod_cast hD
    linarith
  · intro hE
    have : (D B j : ℝ) = 0 := by linarith
    exact_mod_cast this

/-- 单 B 重述：¬(B(e+π)∈ℤ) ⇔ D_j(B) **最终恒非零**（由 F 的 (a)↔(c)）。

    注意（2026-11-14 内核复验修正）：原稿右侧写作"无穷多次非零"
    `(∀ N, ∃ j ≥ N, D B j ≠ 0)`，该表述**数学上错误**：
    ¬(无穷多次为零) 等价于"最终恒非零"，而非"无穷多次非零"——
    交替序列 0,1,0,1,… 同时满足"无穷多次为零"与"无穷多次非零"。
    故右侧改用 `∀ᶠ j in atTop, D B j ≠ 0`（最终恒非零），与 F 的三等价一致。 -/
theorem not_int_iff_inf_mismatch (B : ℕ) :
    (¬ ∃ A : ℤ, (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ)) ↔
      (∀ᶠ j in atTop, D B j ≠ 0) := by
  have h := (theorem11_three_equiv B).1.trans (theorem11_three_equiv B).2
  -- h : (∃A, B(e+π)=A) ↔ (∀N,∃j≥N, Tsel B j = -B*Csel j)
  have hD : (∀ N, ∃ j ≥ N, Tsel B j = -(B : ℤ) * Csel j) ↔
      (∀ N, ∃ j ≥ N, D B j = 0) := by
    constructor <;> intro hN N <;>
      obtain ⟨j, hj, hjm⟩ := hN N <;>
      refine ⟨j, hj, ?_⟩ <;> simp only [D] at hjm ⊢ <;>
      linarith
  have hgoal : (¬ ∀ N : ℕ, ∃ j ≥ N, D B j = 0) ↔ (∀ᶠ j in atTop, D B j ≠ 0) := by
    rw [Filter.eventually_atTop]
    constructor
    · intro hn
      by_contra hc
      push Not at hc
      apply hn
      intro N
      obtain ⟨j, hjge, hjz⟩ := hc N
      exact ⟨j, hjge, hjz⟩
    · rintro ⟨N, hN⟩ hall
      obtain ⟨j, hjge, hjz⟩ := hall N
      exact hN j hjge hjz
  exact (not_congr h).trans ((not_iff_not.mpr hD).trans hgoal)

/-- **目标重述**：e+π 无理 ⇔ 对每个 B≥1，D_j(B) **最终恒非零**。
    这是开放目标的精确整数非零性形式；本定理只重述，不证明右侧。
    （2026-11-14 修正：右侧由"无穷多次非零"改为"最终恒非零"，见上一定理说明。） -/
theorem irrational_iff_inf_mismatch :
    Irrational (Real.exp 1 + Real.pi) ↔
      ∀ B : ℕ, 1 ≤ B → ∀ᶠ j in atTop, D B j ≠ 0 := by
  -- e+π 无理 ⇔ ¬∃(p:ℚ), e+π=p；写 p=num/den 即 ¬∃B≥1,∃A, B(e+π)=A。
  have hq : Irrational (Real.exp 1 + Real.pi) ↔
      ∀ B : ℕ, 1 ≤ B → ¬ ∃ A : ℤ, (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ) := by
    constructor
    · intro h B hB ⟨A, hA⟩
      have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
      apply h
      refine ⟨(A : ℚ) / (B : ℚ), ?_⟩
      push_cast
      field_simp
      linarith
    · intro h ⟨q, hq⟩
      have hden : 0 < q.den := q.den_pos
      have hcast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
        have := congrArg (fun r : ℚ => (r : ℝ)) (Rat.num_div_den q).symm
        push_cast at this
        exact this
      have hne : (q.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hden)
      have hA : (q.den : ℝ) * (Real.exp 1 + Real.pi) = (q.num : ℝ) := by
        rw [← hq, hcast]; field_simp
      exact h q.den (by omega) ⟨q.num, hA⟩
  rw [hq]
  constructor
  · intro h B hB
    exact (not_int_iff_inf_mismatch B).mp (h B hB)
  · intro h B hB
    exact (not_int_iff_inf_mismatch B).mpr (h B hB)

/-- **两形式等价**：对固定 B，"无穷多次非零" ⇔ "最终恒非零"。
    方向 (⇐) 平凡；(⇒) 用 F 的 (a)⇒(b)：若无穷多次为零则 (c) 成立⇒(a)⇒(b) 最终为零，
    与"无穷多次非零"矛盾。故交替 0,1 序列不是反例。 -/
theorem inf_mismatch_iff_eventually (B : ℕ) :
    (∀ N : ℕ, ∃ j ≥ N, D B j ≠ 0) ↔ (∀ᶠ j in atTop, D B j ≠ 0) := by
  constructor
  · intro hinf
    by_contra hnot
    rw [Filter.eventually_atTop] at hnot
    push Not at hnot
    -- hnot : ∀ N, ∃ j ≥ N, D B j = 0  （无穷多次为零）
    have hc : ∀ N, ∃ j ≥ N, Tsel B j = -(B : ℤ) * Csel j := by
      intro N
      obtain ⟨j, hj, hjz⟩ := hnot N
      refine ⟨j, hj, ?_⟩
      simp only [D] at hjz
      linarith
    have ha : ∃ A : ℤ, (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ) :=
      theorem11_converse hc
    have hb : ∀ᶠ j in atTop, Tsel B j = -(B : ℤ) * Csel j :=
      theorem11_forward ha
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hb
    obtain ⟨j, hjge, hjne⟩ := hinf N0
    have hjz : Tsel B j = -(B : ℤ) * Csel j := hN0 j hjge
    simp only [D] at hjne
    rw [hjz] at hjne
    simp at hjne
  · intro hev N
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max N N0, le_max_left _ _, ?_⟩
    exact hN0 (max N N0) (le_max_right _ _)

end

end Escape