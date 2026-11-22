import Mathlib
import EpiFormal.DimHFinite

open Real Filter Topology

namespace WeightedPhase

noncomputable section

/-- 一般 α 的内容解析核心：若 s > 1−α，则 K^n · (n!)^{1−α−s} → 0。
    归约到已验证的 tendsto_powB_div_factorial_rpow（β = s−(1−α) > 0）。 -/
lemma content_core_tendsto (K : ℝ) (hK : 0 ≤ K) (α s : ℝ) (hs : 1 - α < s) :
    Tendsto (fun n : ℕ => K ^ n * (Nat.factorial n : ℝ) ^ (1 - α - s)) atTop (nhds 0) := by
  set β := s - (1 - α) with hβdef
  have hβ : 0 < β := by linarith
  -- 已验证：K^n / (n!)^β → 0
  have h := DimHFinite.tendsto_powB_div_factorial_rpow K hK β hβ
  -- K^n * (n!)^{−β} = K^n / (n!)^β
  have heq : (fun n : ℕ => K ^ n * (Nat.factorial n : ℝ) ^ (1 - α - s)) =
      (fun n : ℕ => K ^ n / (Nat.factorial n : ℝ) ^ β) := by
    funext n
    have hpos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hexp : 1 - α - s = -β := by linarith
    rw [hexp, Real.rpow_neg (le_of_lt hpos), div_eq_mul_inv, mul_comm]
  rw [heq]
  exact h

end

end WeightedPhase

#print axioms WeightedPhase.content_core_tendsto
