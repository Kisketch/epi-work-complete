import Mathlib
import EpiFormal.EulerConvergents
import EpiFormal.AdjacentWitness
import EpiFormal.Axioms

/-!
# 核心边界的机器验证：仅通用条件不足以排除最终匹配（EscapeBoundary）

来源：审阅强调的核心边界（2026-11-14）。把 π 换成 `A/B − e` 后，
双指标判据的全部**通用条件**（Q_j 递推、|ε|≤1/2、δ_j→0）仍然成立，
且 D'_j **最终恒为 0**。这认证了「最后一步必须用 π 的特殊性质」：
任何只依赖通用递推 + 取整误差的论证都无法排除最终匹配。

## 诚实声明
本文件**没有、也不声称**证明 e+π 无理性；恰恰相反，它机器验证了
通用条件的不足。公理唯一来源为 A 组的 `deltaSel_tendsto_zero`
（本文件未使用 `abs_deltaSel_lt`，也未使用 Axioms.lean 的超越性公理）。
-/

open Real Filter Set

namespace EscapeBoundary

noncomputable section

/-- 替代值 π' = A/B − e（B≥1 时良定）。 -/
def pi' (A : ℤ) (B : ℕ) : ℝ := (A : ℝ) / B - exp 1

/-- M'_j = round(B·Q_j·π')。 -/
def M' (A : ℤ) (B : ℕ) (j : ℕ) : ℤ :=
  round ((B : ℝ) * (Qsel j : ℝ) * pi' A B)

/-- T'_j = M'_j Q_{j+1} − M'_{j+1} Q_j。 -/
def T' (A : ℤ) (B : ℕ) (j : ℕ) : ℤ :=
  M' A B j * Qsel (j + 1) - M' A B (j + 1) * Qsel j

/-- D'_j = T'_j + B·C_j。 -/
def D' (A : ℤ) (B : ℕ) (j : ℕ) : ℤ :=
  T' A B j + (B : ℤ) * AdjacentWitness.Csel j

/-- 由 δ_j→0：最终 |B·δ_j| < 1/2。 -/
lemma eventually_abs_B_deltaSel_lt (B : ℕ) :
    ∀ᶠ j in atTop, |(B : ℝ) * deltaSel j| < 1 / 2 := by
  have hB : Tendsto (fun j => (B : ℝ) * deltaSel j) atTop (nhds 0) := by
    simpa using deltaSel_tendsto_zero.const_mul (B : ℝ)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hB (1 / 2) (by norm_num)
  apply Filter.eventually_atTop.mpr
  refine ⟨N, fun j hj => ?_⟩
  have := hN j hj
  simpa [Real.dist_eq] using this

/-- 关键取整步：最终 round(B·Q_j·e) = B·P_j。
    因 B·Q_j·e = B·P_j + B·δ_j 且最终 |B·δ_j| < 1/2，用 round_eq_iff + abs_lt。 -/
lemma eventually_round_BQe (B : ℕ) :
    ∀ᶠ j in atTop, round ((B : ℝ) * (Qsel j : ℝ) * exp 1) = (B : ℤ) * Psel j := by
  filter_upwards [eventually_abs_B_deltaSel_lt B] with j hj
  set K : ℤ := (B : ℤ) * Psel j
  have hdecomp : (B : ℝ) * (Qsel j : ℝ) * exp 1 = (K : ℝ) + (B : ℝ) * deltaSel j := by
    simp only [deltaSel, K]
    push_cast
    ring
  have hreal : |(B : ℝ) * (Qsel j : ℝ) * exp 1 - (K : ℝ)| < 1 / 2 := by
    rw [hdecomp]
    have : (K : ℝ) + (B : ℝ) * deltaSel j - (K : ℝ) = (B : ℝ) * deltaSel j := by ring
    rw [this]
    exact hj
  rw [round_eq_iff]
  have := abs_lt.mp hreal
  constructor <;> linarith

/-- 整数减实数的取整（非半整数点）：round(n − x) = n − round(x)。
    mathlib v4.35.0 无此直接引理，由 round_eq_iff 自证。 -/
lemma round_intCast_sub_of_abs_lt {x : ℝ} {m : ℤ}
    (hm : |x - (m : ℝ)| < 1 / 2) (n : ℤ) :
    round ((n : ℝ) - x) = n - m := by
  rw [round_eq_iff]
  have hcast : ((n - m : ℤ) : ℝ) = (n : ℝ) - (m : ℝ) := by push_cast; ring
  rw [hcast]
  have := abs_lt.mp hm
  constructor <;> linarith

/-- 最终 M'_j = A·Q_j − B·P_j。 -/
lemma eventually_M' (A : ℤ) (B : ℕ) (hB : 1 ≤ B) :
    ∀ᶠ j in atTop, M' A B j = A * Qsel j - (B : ℤ) * Psel j := by
  have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  filter_upwards [eventually_round_BQe B, eventually_abs_B_deltaSel_lt B] with j hj hδ
  set x : ℝ := (B : ℝ) * (Qsel j : ℝ) * exp 1
  set n : ℤ := A * Qsel j
  have hx : |x - ((B : ℝ) * (Psel j : ℝ))| < 1 / 2 := by
    -- x − B·P_j = B·δ_j，而 |B·δ_j| < 1/2（严格，来自 δ_j→0）。
    have hdecomp : x - (B : ℝ) * (Psel j : ℝ) = (B : ℝ) * deltaSel j := by
      simp only [deltaSel, x]
      push_cast
      ring
    rw [hdecomp]
    exact hδ
  have harg : (B : ℝ) * (Qsel j : ℝ) * pi' A B = (n : ℝ) - x := by
    simp only [pi', x, n]
    push_cast
    field_simp
  show round ((B : ℝ) * (Qsel j : ℝ) * pi' A B) = A * Qsel j - (B : ℤ) * Psel j
  rw [harg]
  have hx' : |x - (((B : ℤ) * Psel j : ℤ) : ℝ)| < 1 / 2 := by
    convert hx using 1
    push_cast
    ring
  exact round_intCast_sub_of_abs_lt hx' n

/-- **核心边界定理**：把 π 换成 A/B − e 后，D'_j 最终恒为 0。
    即仅通用条件（递推 + 取整 + δ_j→0）不足以排除最终匹配；
    要排除真实 π 的最终匹配，最后一步必须用 π 的特殊性质。 -/
theorem boundary_eventual_match (A : ℤ) (B : ℕ) (hB : 1 ≤ B) :
    ∃ N, ∀ j ≥ N, D' A B j = 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_M' A B hB)
  refine ⟨N, fun j hj => ?_⟩
  have hj1 : M' A B j = A * Qsel j - (B : ℤ) * Psel j := hN j hj
  have hj2 : M' A B (j + 1) = A * Qsel (j + 1) - (B : ℤ) * Psel (j + 1) :=
    hN (j + 1) (by omega)
  simp only [D', T', AdjacentWitness.Csel, hj1, hj2]
  ring

end

end EscapeBoundary