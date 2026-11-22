import Mathlib
import EpiFormal.Classification

open Real Filter Topology Set

namespace ThresholdAttained

open Classification

noncomputable section

/-! ## OBL-2：阈值 1/4 的可达性机制

    核心引理：若 defect 最终恒为整数 d，且 ε_j → 0，则
      (4j+2)·ε_j → d，故 j·‖Q_j x‖ → |d|/4。
    取 d = ±1 即得极限**恰为 1/4**（强于 limsup），说明 1/4 是可达的候选值。
    这解释了 corollary3_gap 中 c < 1/4 的严格性：c = 1/4 时 c·g(j) > 1，
    只能得 |D_j| ≤ 1，挤不出 D_j = 0，故 defect ≡ ±1 与 c = 1/4 相容。 -/

/-- 由缺陷恒等式解出 (4j+2)ε_j = D_j + ε_{j+1} − ε_{j−1}。 -/
lemma eps_mul_eq (x : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    (4 * (j : ℝ) + 2) * eps x j = (defect x j : ℝ) + eps x (j + 1) - eps x (j - 1) := by
  have h := defect_identity x j hj
  linarith [h]

/-- **核心引理**：defect 最终 ≡ d 且 ε_j → 0 ⇒ (4j+2)ε_j → d。 -/
lemma eps_mul_tendsto_of_defect_const (x : ℝ) (d : ℤ)
    (hd : ∀ᶠ j in atTop, defect x j = d)
    (hε : Tendsto (eps x) atTop (nhds 0)) :
    Tendsto (fun j : ℕ => (4 * (j : ℝ) + 2) * eps x j) atTop (nhds (d : ℝ)) := by
  -- ε_{j+1} → 0
  have h1 : Tendsto (fun j : ℕ => eps x (j + 1)) atTop (nhds 0) :=
    hε.comp (tendsto_add_atTop_nat 1)
  -- ε_{j−1} → 0（j−1 = j+(-1) 用 Nat 减法，最终等于 pred 复合）
  have h2 : Tendsto (fun j : ℕ => eps x (j - 1)) atTop (nhds 0) := by
    -- 用 tendsto_atTop 的显式刻画：∀N, 最终 j−1 ≥ N
    have hshift : Tendsto (fun j : ℕ => j - 1) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro N
      exact ⟨N + 1, fun j hj => by omega⟩
    exact hε.comp hshift
  -- (d : ℝ) 常数
  have hdR : Tendsto (fun j : ℕ => (defect x j : ℝ)) atTop (nhds (d : ℝ)) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hd] with j hj
    simp [hj]
  -- 组合：D_j + ε_{j+1} − ε_{j−1} → d + 0 − 0
  have hsum : Tendsto (fun j : ℕ => (defect x j : ℝ) + eps x (j + 1) - eps x (j - 1))
      atTop (nhds ((d : ℝ) + 0 - 0)) := (hdR.add h1).sub h2
  have hlim : (d : ℝ) + 0 - 0 = (d : ℝ) := by ring
  rw [hlim] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with j hj
  exact (eps_mul_eq x j hj).symm

/-- j·ε_j → d/4（由 (4j+2)ε_j → d 除以 4，并吸收 2ε_j → 0）。 -/
lemma j_mul_eps_tendsto (x : ℝ) (d : ℤ)
    (hd : ∀ᶠ j in atTop, defect x j = d)
    (hε : Tendsto (eps x) atTop (nhds 0)) :
    Tendsto (fun j : ℕ => (j : ℝ) * eps x j) atTop (nhds ((d : ℝ) / 4)) := by
  have h := eps_mul_tendsto_of_defect_const x d hd hε
  -- (4j+2)ε_j = 4·(j ε_j) + 2ε_j
  have hdecomp : (fun j : ℕ => (4 * (j : ℝ) + 2) * eps x j) =
      (fun j : ℕ => 4 * ((j : ℝ) * eps x j) + 2 * eps x j) := by
    funext j; ring
  rw [hdecomp] at h
  have h2ε : Tendsto (fun j : ℕ => 2 * eps x j) atTop (nhds 0) := by
    have := hε.const_mul (2 : ℝ)
    simpa using this
  -- 4·(j ε_j) = (4j+2)ε_j − 2ε_j → d − 0
  have h4 : Tendsto (fun j : ℕ => 4 * ((j : ℝ) * eps x j)) atTop (nhds ((d : ℝ) - 0)) := by
    have := h.sub h2ε
    apply this.congr'
    filter_upwards with j
    ring
  have hd0 : (d : ℝ) - 0 = (d : ℝ) := by ring
  rw [hd0] at h4
  have := h4.const_mul (1 / 4 : ℝ)
  have hgoal : (1 / 4 : ℝ) * (d : ℝ) = (d : ℝ) / 4 := by ring
  rw [hgoal] at this
  apply this.congr'
  filter_upwards with j
  ring

/-- **j·‖Q_j x‖ → |d|/4**（取绝对值；‖Q_j x‖ = |ε_j|）。 -/
theorem apprSeq_tendsto_of_defect_const (x : ℝ) (d : ℤ)
    (hd : ∀ᶠ j in atTop, defect x j = d)
    (hε : Tendsto (eps x) atTop (nhds 0)) :
    Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x))
      atTop (nhds (|(d : ℝ)| / 4)) := by
  have habs_eps : (fun j : ℕ => distToNearestInt ((Qsel j : ℝ) * x)) =
      (fun j : ℕ => |eps x j|) := by
    funext j
    simp [eps, nearestInt, distToNearestInt]
  have hj := j_mul_eps_tendsto x d hd hε
  have habs : Tendsto (fun j : ℕ => |(j : ℝ) * eps x j|) atTop (nhds |(d : ℝ) / 4|) :=
    hj.abs
  have hnn : (fun j : ℕ => |(j : ℝ) * eps x j|) =
      (fun j : ℕ => (j : ℝ) * |eps x j|) := by
    funext j
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
  rw [hnn] at habs
  have hlim : |(d : ℝ) / 4| = |(d : ℝ)| / 4 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]
  rw [hlim] at habs
  apply habs.congr'
  filter_upwards with j
  simp only [eps, nearestInt, distToNearestInt]

/-- **推论：d = 1 时极限恰为 1/4**（阈值可达的机制）。 -/
theorem apprSeq_tendsto_quarter (x : ℝ)
    (hd : ∀ᶠ j in atTop, defect x j = 1)
    (hε : Tendsto (eps x) atTop (nhds 0)) :
    Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x))
      atTop (nhds (1 / 4 : ℝ)) := by
  have h := apprSeq_tendsto_of_defect_const x 1 hd hε
  simpa using h

end

end ThresholdAttained

#print axioms ThresholdAttained.eps_mul_eq
#print axioms ThresholdAttained.eps_mul_tendsto_of_defect_const
#print axioms ThresholdAttained.j_mul_eps_tendsto
#print axioms ThresholdAttained.apprSeq_tendsto_of_defect_const
#print axioms ThresholdAttained.apprSeq_tendsto_quarter
