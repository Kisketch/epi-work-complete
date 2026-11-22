import Mathlib
import EpiFormal.Series

/-!
# 补充页 Proposition 4：阶乘判据（双向）—— 并发子任务 G

来源：用户修订包补充材料第 2 页（epi-pdf-qa/supp.pdf）的纸面证明，本文件完整形式化。

**重要**：本定理是「e + π 有理」的一个*等价判据*。e + π 的无理性仍是世界开放问题；
本文件不证明、也不暗示该问题已解决。判据右侧 `n·{-n!π} → 1` 是否成立，本文件不作断言。

## 结构
- `uFrac n = {-n!π}`，`tFrac n = {n!e}`（`Int.fract`，值域 [0,1)）。
- 尾和 `tail n = Σ_{k>n} n!/k!` 复用主项目 `EpiFormal.Series`（只读导入）。
- 引理链：尾和恒等式 → 双侧界 `1/(n+1) < tₙ < 1/n`（n≥2）→ `n·tₙ → 1` →
  有理 ⇒ 最终 `uₙ = tₙ`；反向：整值递推序列收敛 ⇒ 最终恒 1 ⇒ 迭代恒等式 +
  有界性 ⇒ `u_N = t_N` ⇒ `N!(e+π) ∈ ℤ` ⇒ 有理。
- 全部真证：无 sorry / admit / native_decide，无新增公理。
-/

open Real Filter
open scoped Nat Topology

namespace FactorialCriterion

/-- uₙ = {-n!π}。 -/
noncomputable def uFrac (n : ℕ) : ℝ := Int.fract (-(n.factorial : ℝ) * Real.pi)

/-- tₙ = {n!e}。 -/
noncomputable def tFrac (n : ℕ) : ℝ := Int.fract ((n.factorial : ℝ) * Real.exp 1)

/-! ### 基础事实 -/

/-- e 的阶乘级数展开：e = Σₖ 1/k!。 -/
lemma exp_one_eq_tsum : Real.exp 1 = ∑' k : ℕ, 1 / (Nat.factorial k : ℝ) := by
  have h := congr_fun (Real.exp_eq_exp_ℝ.trans NormedSpace.exp_eq_tsum_div) 1
  simpa using h

/-- Σₖ 1/k! 可和。 -/
lemma summable_inv_factorial : Summable (fun k : ℕ => 1 / (Nat.factorial k : ℝ)) := by
  have h := Real.summable_pow_div_factorial 1
  convert h using 1 with k
  simp

/-- 尾和定义展开（与主项目 `tail` 逐项一致）。 -/
lemma tail_eq (n : ℕ) :
    tail n = ∑' k : ℕ, if n < k then (n.factorial : ℝ) / (k.factorial : ℝ) else 0 := rfl

set_option maxHeartbeats 1600000 in
/-- 移位尾和的可和性。 -/
lemma summable_shift (n : ℕ) :
    Summable (fun j : ℕ => (n.factorial : ℝ) / ((n + 1 + j).factorial : ℝ)) := by
  have hbase : Summable (fun k : ℕ => (n.factorial : ℝ) / (k.factorial : ℝ)) := by
    have := summable_inv_factorial.mul_left (n.factorial : ℝ)
    refine this.congr (fun k => ?_)
    ring
  have h := (summable_nat_add_iff (n + 1)).mpr hbase
  refine h.congr (fun j => ?_)
  rw [show j + (n + 1) = n + 1 + j by omega]

set_option maxHeartbeats 1600000 in
/-- 尾和的移位表示：tail n = Σⱼ n!/(n+1+j)!。 -/
lemma tail_eq_shift (n : ℕ) :
    tail n = ∑' j : ℕ, (n.factorial : ℝ) / ((n + 1 + j).factorial : ℝ) := by
  have h := Summable.sum_add_tsum_nat_add (n + 1) (tail_summable n)
  have hfront : ∑ j ∈ Finset.range (n + 1),
      (if n < j then (n.factorial : ℝ) / (j.factorial : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j ≤ n := by
      have := Finset.mem_range.mp hj
      omega
    simp [Nat.not_lt.mpr hjn]
  have hnorm : ∑' k : ℕ, (if n < k then (n.factorial : ℝ) / (k.factorial : ℝ) else 0) =
      ∑' j : ℕ, (n.factorial : ℝ) / ((n + 1 + j).factorial : ℝ) := by
    have h1 : ∑' k : ℕ, (if n < k then (n.factorial : ℝ) / (k.factorial : ℝ) else 0) =
        (∑ j ∈ Finset.range (n + 1), (if n < j then (n.factorial : ℝ) / (j.factorial : ℝ) else 0)) +
        ∑' j : ℕ, (if n < j + (n + 1) then (n.factorial : ℝ) / ((j + (n + 1)).factorial : ℝ) else 0) := by
      linarith [h]
    rw [hfront, zero_add] at h1
    rw [h1]
    apply tsum_congr
    intro j
    have hlt : n < j + (n + 1) := by omega
    simp only [hlt, ite_true]
    rw [show j + (n + 1) = n + 1 + j by omega]
  rw [tail_eq]
  exact hnorm

/-- 阶乘比的几何控制：n!/(n+j)! ≤ (1/(n+1))^j。 -/
lemma factorial_ratio_le (n j : ℕ) :
    (n.factorial : ℝ) / ((n + j).factorial : ℝ) ≤ (1 / ((n : ℝ) + 1)) ^ j := by
  induction j with
  | zero =>
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [Nat.add_zero, div_self hf, pow_zero]
  | succ j ih =>
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hstep : (n.factorial : ℝ) / ((n + (j + 1)).factorial : ℝ) =
        ((n.factorial : ℝ) / ((n + j).factorial : ℝ)) * (1 / ((n + j : ℝ) + 1)) := by
      have hfac : ((n + (j + 1)).factorial : ℝ) =
          ((n + j).factorial : ℝ) * ((n + j : ℝ) + 1) := by
        have : n + (j + 1) = (n + j) + 1 := by omega
        rw [this, Nat.factorial_succ]
        push_cast
        ring
      rw [hfac]
      field_simp
    rw [hstep, pow_succ]
    have hle : 1 / ((n + j : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le hn1
      have : (n : ℝ) ≤ (n + j : ℝ) := by exact_mod_cast Nat.le_add_right n j
      linarith
    calc (n.factorial : ℝ) / ((n + j).factorial : ℝ) * (1 / ((n + j : ℝ) + 1))
        ≤ (1 / ((n : ℝ) + 1)) ^ j * (1 / ((n + j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ (1 / ((n : ℝ) + 1)) ^ j * (1 / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)

/-- 尾和为正（对一切 n）。 -/
lemma tail_pos (n : ℕ) : 0 < tail n := by
  have h0 : 0 < (n.factorial : ℝ) / ((n + 1).factorial : ℝ) := by positivity
  have hle : (n.factorial : ℝ) / ((n + 1).factorial : ℝ) ≤ tail n := by
    rw [tail_eq_shift]
    have := Summable.sum_le_tsum ({0} : Finset ℕ)
      (fun j _ => by positivity) (summable_shift n)
    simpa using this
  exact lt_of_lt_of_le h0 hle

/-- 几何级数移位和：Σⱼ r^(j+1) = r/(1-r)（0 ≤ r < 1）。 -/
lemma tsum_pow_succ (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    ∑' j : ℕ, r ^ (j + 1) = r / (1 - r) := by
  have hg := summable_geometric_of_lt_one h0 h1
  have hsplit := hg.sum_add_tsum_nat_add 1
  have htsum : ∑' j : ℕ, r ^ j = (1 - r)⁻¹ := tsum_geometric_of_lt_one h0 h1
  have hfront : ∑ j ∈ Finset.range 1, r ^ j = 1 := by simp
  have hshift : ∑' j : ℕ, r ^ (j + 1) = (1 - r)⁻¹ - 1 := by
    simp only [hfront] at hsplit
    linarith [hsplit, htsum]
  rw [hshift]
  have hne : 1 - r ≠ 0 := by linarith
  field_simp [hne]
  ring

set_option maxHeartbeats 1600000 in
/-- 尾和上界（n ≥ 1）：tail n < 1。
n = 0 时几何公比 r = 1 不可和，故此引理必须限制 n ≥ 1（数学原因见报告）。 -/
lemma tail_lt_one (n : ℕ) (hn : 1 ≤ n) : tail n < 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hr : 1 / ((n : ℝ) + 1) < 1 := by
    rw [div_lt_one hn1]; linarith
  have hle : ∀ j : ℕ, (n.factorial : ℝ) / ((n + 1 + j).factorial : ℝ) ≤
      (1 / ((n : ℝ) + 1)) ^ (j + 1) := by
    intro j
    have h := factorial_ratio_le n (j + 1)
    rw [show n + (j + 1) = n + 1 + j by omega] at h
    exact h
  have hstrict : (n.factorial : ℝ) / ((n + 1 + 1).factorial : ℝ) <
      (1 / ((n : ℝ) + 1)) ^ (1 + 1) := by
    have hfac : ((n + 2).factorial : ℝ) =
        (n.factorial : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
      rw [show n + 1 + 1 = n + 2 by omega, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [show n + 1 + 1 = n + 2 by omega, hfac]
    have hlhs : (n.factorial : ℝ) / ((n.factorial : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
        1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by field_simp
    rw [hlhs]
    have hrhs : (1 / ((n : ℝ) + 1)) ^ 2 = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by
      rw [div_pow, one_pow, pow_two]
    rw [hrhs]
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  have hgeo : Summable (fun j : ℕ => (1 / ((n : ℝ) + 1)) ^ (j + 1)) :=
    (summable_geometric_of_lt_one (by positivity) hr).comp_injective (add_left_injective 1)
  have hsumlt := Summable.tsum_lt_tsum_of_nonneg (fun j => by positivity) hle hstrict hgeo
  have hgeosum : ∑' j : ℕ, (1 / ((n : ℝ) + 1)) ^ (j + 1) = 1 / (n : ℝ) := by
    rw [tsum_pow_succ (1 / ((n : ℝ) + 1)) (by positivity) hr]
    field_simp [ne_of_gt hn0]
    ring
  have hbound : ∑' j : ℕ, (n.factorial : ℝ) / ((n + 1 + j).factorial : ℝ) < 1 / (n : ℝ) := by
    rw [← hgeosum]; exact hsumlt
  have h1n : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn0]; exact_mod_cast hn
  rw [tail_eq_shift]
  exact lt_of_lt_of_le hbound h1n

/-- 尾和 ∈ (0,1)（n ≥ 1）。 -/
lemma tail_mem_Ioo (n : ℕ) (hn : 1 ≤ n) : tail n ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨tail_pos n, tail_lt_one n hn⟩

/-! ### 关键引理 1：tFrac = 尾和 -/

/-- n!·e = Σₖ n!/k!。 -/
lemma nfact_mul_exp (n : ℕ) :
    (n.factorial : ℝ) * Real.exp 1 = ∑' k : ℕ, (n.factorial : ℝ) / (k.factorial : ℝ) := by
  rw [exp_one_eq_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

/-- 前段 Σ_{k≤n} n!/k! 是整数（每项 n!/k! = ↑(n!/k!)，k! ∣ n!）。 -/
lemma front_is_int (n : ℕ) :
    ∃ z : ℤ, ∑ k ∈ Finset.range (n + 1), (n.factorial : ℝ) / (k.factorial : ℝ) = z := by
  refine ⟨∑ k ∈ Finset.range (n + 1), ((n.factorial / k.factorial : ℕ) : ℤ), ?_⟩
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  have hdiv : ((n.factorial / k.factorial : ℕ) : ℝ) =
      (n.factorial : ℝ) / (k.factorial : ℝ) :=
    Nat.cast_div (Nat.factorial_dvd_factorial hkn)
      (by positivity : (k.factorial : ℝ) ≠ 0)
  exact hdiv.symm

set_option maxHeartbeats 1600000 in
/-- **引理 1**：tFrac n = tail n（n ≥ 1）。
n!·e 的前 n+1 项为整数，小数部分 = 尾和；尾和 ∈ (0,1)。 -/
theorem tFrac_eq_tail (n : ℕ) (hn : 1 ≤ n) : tFrac n = tail n := by
  have hsum : Summable (fun k : ℕ => (n.factorial : ℝ) / (k.factorial : ℝ)) := by
    have := summable_inv_factorial.mul_left (n.factorial : ℝ)
    refine this.congr (fun k => ?_)
    ring
  have htail : ∑' k : ℕ, (n.factorial : ℝ) / ((k + (n + 1)).factorial : ℝ) = tail n := by
    rw [tail_eq_shift]
    apply tsum_congr
    intro j
    rw [show j + (n + 1) = n + 1 + j by omega]
  have hsplit : ∑' k : ℕ, (n.factorial : ℝ) / (k.factorial : ℝ) =
      (∑ k ∈ Finset.range (n + 1), (n.factorial : ℝ) / (k.factorial : ℝ)) + tail n := by
    have h1 := hsum.sum_add_tsum_nat_add (n + 1)
    have h2 : ∑' k : ℕ, (n.factorial : ℝ) / (k.factorial : ℝ) =
        (∑ k ∈ Finset.range (n + 1), (n.factorial : ℝ) / (k.factorial : ℝ)) +
        ∑' k : ℕ, (n.factorial : ℝ) / ((k + (n + 1)).factorial : ℝ) := by
      linarith [h1]
    rw [htail] at h2
    exact h2
  obtain ⟨z, hz⟩ := front_is_int n
  have hcast : (n.factorial : ℝ) * Real.exp 1 = (z : ℝ) + tail n := by
    rw [nfact_mul_exp, hsplit, hz]
  have hfract : Int.fract ((z : ℝ) + tail n) = tail n := by
    rw [Int.fract_intCast_add]
    have hmem := tail_mem_Ioo n hn
    exact Int.fract_eq_self.mpr ⟨le_of_lt hmem.1, hmem.2⟩
  show Int.fract ((n.factorial : ℝ) * Real.exp 1) = tail n
  rw [hcast, hfract]

/-! ### 关键引理 2：双侧界 -/

set_option maxHeartbeats 1600000 in
/-- **引理 2**：1/(n+1) < tFrac n < 1/n（n ≥ 2）。
下界：尾和首项 1/(n+1)，其余项正。上界：几何控制 + j=1 处严格。 -/
theorem tFrac_bounds (n : ℕ) (hn : 2 ≤ n) :
    1 / ((n : ℝ) + 1) < tFrac n ∧ tFrac n < 1 / (n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [tFrac_eq_tail n hn1]
  constructor
  · -- 下界
    have hfirst : (n.factorial : ℝ) / ((n + 1).factorial : ℝ) = 1 / ((n : ℝ) + 1) := by
      have hfac : ((n + 1).factorial : ℝ) = (n.factorial : ℝ) * ((n : ℝ) + 1) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hfac]; field_simp
    have hle : (n.factorial : ℝ) / ((n + 1).factorial : ℝ) ≤ tail n := by
      rw [tail_eq_shift]
      have := Summable.sum_le_tsum ({0} : Finset ℕ)
        (fun j _ => by positivity) (summable_shift n)
      simpa using this
    have hpos_rest : 0 < ∑' j : ℕ, (n.factorial : ℝ) / ((n + 1 + (j + 1)).factorial : ℝ) := by
      have hsum : Summable (fun j : ℕ =>
          (n.factorial : ℝ) / ((n + 1 + (j + 1)).factorial : ℝ)) :=
        (summable_shift n).comp_injective (add_left_injective 1)
      exact Summable.tsum_pos hsum (fun j => by positivity) 0 (by positivity)
    have hsplit : tail n = (n.factorial : ℝ) / ((n + 1).factorial : ℝ) +
        ∑' j : ℕ, (n.factorial : ℝ) / ((n + 1 + (j + 1)).factorial : ℝ) := by
      rw [tail_eq_shift]
      have h1 := (summable_shift n).sum_add_tsum_nat_add 1
      have hfront : ∑ j ∈ Finset.range 1,
          (n.factorial : ℝ) / ((n + 1 + j).factorial : ℝ) =
          (n.factorial : ℝ) / ((n + 1).factorial : ℝ) := by
        simp
      have h2 : ∑' j : ℕ, (n.factorial : ℝ) / ((n + 1 + j).factorial : ℝ) =
          (n.factorial : ℝ) / ((n + 1).factorial : ℝ) +
          ∑' j : ℕ, (n.factorial : ℝ) / ((n + 1 + (j + 1)).factorial : ℝ) := by
        simp only [hfront] at h1
        linarith [h1]
      exact h2
    rw [hsplit, hfirst]
    linarith
  · -- 上界
    have hr : 1 / ((n : ℝ) + 1) < 1 := by rw [div_lt_one hn1']; linarith
    have hle : ∀ j : ℕ, (n.factorial : ℝ) / ((n + 1 + j).factorial : ℝ) ≤
        (1 / ((n : ℝ) + 1)) ^ (j + 1) := by
      intro j
      have h := factorial_ratio_le n (j + 1)
      rw [show n + (j + 1) = n + 1 + j by omega] at h
      exact h
    have hstrict : (n.factorial : ℝ) / ((n + 1 + 1).factorial : ℝ) <
        (1 / ((n : ℝ) + 1)) ^ (1 + 1) := by
      have hfac : ((n + 2).factorial : ℝ) =
          (n.factorial : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
        rw [show n + 1 + 1 = n + 2 by omega, Nat.factorial_succ, Nat.factorial_succ]
        push_cast; ring
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      rw [show n + 1 + 1 = n + 2 by omega, hfac]
      have hlhs : (n.factorial : ℝ) / ((n.factorial : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
          1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by field_simp
      rw [hlhs]
      have hrhs : (1 / ((n : ℝ) + 1)) ^ 2 = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by
        rw [div_pow, one_pow, pow_two]
      rw [hrhs]
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    have hgeo : Summable (fun j : ℕ => (1 / ((n : ℝ) + 1)) ^ (j + 1)) :=
      (summable_geometric_of_lt_one (by positivity) hr).comp_injective (add_left_injective 1)
    have hsumlt := Summable.tsum_lt_tsum_of_nonneg (fun j => by positivity) hle hstrict hgeo
    have hgeosum : ∑' j : ℕ, (1 / ((n : ℝ) + 1)) ^ (j + 1) = 1 / (n : ℝ) := by
      rw [tsum_pow_succ (1 / ((n : ℝ) + 1)) (by positivity) hr]
      field_simp [ne_of_gt hn0]
      ring
    rw [tail_eq_shift, ← hgeosum]
    exact hsumlt

/-! ### 关键引理 3：n·tFrac n → 1 -/

set_option maxHeartbeats 1600000 in
/-- **引理 3**：Tendsto (n·tFrac n) atTop (nhds 1)（夹逼）。 -/
theorem tFrac_tendsto : Tendsto (fun n : ℕ => (n : ℝ) * tFrac n) atTop (nhds 1) := by
  have hlower : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (nhds 1) := by
    have h : (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) =ᶠ[atTop]
        (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hn1]
      ring
    refine (tendsto_congr' h).mpr ?_
    have hdiv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds.sub hdiv)
  have hupper : Tendsto (fun n : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hb := (tFrac_bounds n hn).1
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have := mul_lt_mul_of_pos_left hb hn0
    have hmul : (n : ℝ) * (1 / ((n : ℝ) + 1)) = (n : ℝ) / ((n : ℝ) + 1) := by ring
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hb := (tFrac_bounds n hn).2
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have := mul_lt_mul_of_pos_left hb hn0
    have hmul : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
    linarith

/-! ### 关键引理 4：有理 ⇒ 最终 uFrac = tFrac -/

/-- **引理 4**：若 e+π 有理，则最终 uFrac n = tFrac n。
n!(e+π) 最终为整数 ⇒ {−n!π} = {n!e}（和为整数，非互为相反数）。 -/
theorem uFrac_eq_tFrac_of_rational (h : ∃ q : ℚ, Real.exp 1 + Real.pi = q) :
    ∀ᶠ n : ℕ in atTop, uFrac n = tFrac n := by
  obtain ⟨q, hq⟩ := h
  have hq' : (q : ℝ) = Real.exp 1 + Real.pi := by exact_mod_cast hq.symm
  filter_upwards [eventually_ge_atTop q.den] with n hn
  have hdvd : q.den ∣ n.factorial := Nat.dvd_factorial q.den_pos hn
  have hz : ∃ z : ℤ, (n.factorial : ℝ) * (Real.exp 1 + Real.pi) = z := by
    use (n.factorial / q.den : ℕ) * q.num
    have hcast : ((n.factorial / q.den : ℕ) : ℝ) =
        (n.factorial : ℝ) / (q.den : ℝ) :=
      Nat.cast_div hdvd (by positivity)
    have hqcast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    have hfinal : ((n.factorial / q.den : ℕ) : ℝ) * (q.num : ℝ) =
        (((n.factorial / q.den : ℕ) * q.num : ℤ) : ℝ) := by
      push_cast
      rfl
    calc (n.factorial : ℝ) * (Real.exp 1 + Real.pi)
        = (n.factorial : ℝ) * (q : ℝ) := by rw [hq']
      _ = (n.factorial : ℝ) * ((q.num : ℝ) / (q.den : ℝ)) := by rw [hqcast]
      _ = ((n.factorial : ℝ) / (q.den : ℝ)) * (q.num : ℝ) := by ring
      _ = ((n.factorial / q.den : ℕ) : ℝ) * (q.num : ℝ) := by rw [← hcast]
      _ = (((n.factorial / q.den : ℕ) * q.num : ℤ) : ℝ) := hfinal
  obtain ⟨z, hz⟩ := hz
  -- n!e + n!π = z（整数），故 n!e 与 -n!π 相差整数 -z
  have hsum : (n.factorial : ℝ) * Real.exp 1 + (n.factorial : ℝ) * Real.pi = (z : ℝ) := by
    have hexpand : (n.factorial : ℝ) * (Real.exp 1 + Real.pi) =
        (n.factorial : ℝ) * Real.exp 1 + (n.factorial : ℝ) * Real.pi := by ring
    linarith [hexpand, hz]
  show Int.fract (-(n.factorial : ℝ) * Real.pi) = Int.fract ((n.factorial : ℝ) * Real.exp 1)
  apply Int.fract_eq_fract.mpr
  use -z
  have hneg' : (-(n.factorial : ℝ) * Real.pi) - (n.factorial : ℝ) * Real.exp 1 =
      -((n.factorial : ℝ) * Real.exp 1 + (n.factorial : ℝ) * Real.pi) := by ring
  rw [hneg', hsum]
  simp

/-! ### 关键引理 5：整数递推 -/

/-- 整数平移不变性：fract((n+1)x) 与 (n+1)fract(x) 相差整数。 -/
lemma fract_mul_succ (x : ℝ) (n : ℕ) :
    ∃ z : ℤ, (n + 1 : ℝ) * Int.fract x - Int.fract ((n + 1 : ℝ) * x) = z := by
  use ⌊(n + 1 : ℝ) * x⌋ - (n + 1 : ℤ) * ⌊x⌋
  simp only [Int.fract]
  push_cast
  ring

/-- **引理 5a**：(n+1)·uFrac n − uFrac(n+1) 是整数。 -/
theorem recurrence_u (n : ℕ) :
    ∃ z : ℤ, (n + 1 : ℝ) * uFrac n - uFrac (n + 1) = z := by
  have h := fract_mul_succ (-(n.factorial : ℝ) * Real.pi) n
  obtain ⟨z, hz⟩ := h
  use z
  have harg : ((n + 1 : ℝ) * (-(n.factorial : ℝ) * Real.pi)) =
      (-((n + 1).factorial : ℝ) * Real.pi) := by
    have hfac : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac]; ring
  convert hz using 1
  · show (n + 1 : ℝ) * Int.fract (-(n.factorial : ℝ) * Real.pi) -
      Int.fract (-((n + 1).factorial : ℝ) * Real.pi) =
      (n + 1 : ℝ) * Int.fract (-(n.factorial : ℝ) * Real.pi) -
      Int.fract ((n + 1 : ℝ) * (-(n.factorial : ℝ) * Real.pi))
    rw [harg]

/-- **引理 5b**：(n+1)·tFrac n − tFrac(n+1) 是整数。 -/
theorem recurrence_t (n : ℕ) :
    ∃ z : ℤ, (n + 1 : ℝ) * tFrac n - tFrac (n + 1) = z := by
  have h := fract_mul_succ ((n.factorial : ℝ) * Real.exp 1) n
  obtain ⟨z, hz⟩ := h
  use z
  have harg : ((n + 1 : ℝ) * ((n.factorial : ℝ) * Real.exp 1)) =
      (((n + 1).factorial : ℝ) * Real.exp 1) := by
    have hfac : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac]; ring
  convert hz using 1
  · show (n + 1 : ℝ) * Int.fract ((n.factorial : ℝ) * Real.exp 1) -
      Int.fract (((n + 1).factorial : ℝ) * Real.exp 1) =
      (n + 1 : ℝ) * Int.fract ((n.factorial : ℝ) * Real.exp 1) -
      Int.fract ((n + 1 : ℝ) * ((n.factorial : ℝ) * Real.exp 1))
    rw [harg]

/-! ### 关键引理 6：整值序列收敛 ⇒ 最终恒定 -/

/-- **引理 6**：整数值序列若收敛到整数 z，则最终恒为 z。
证明用「整数间距 ≥ 1」：取 ε = 1/2 邻域球。 -/
theorem int_tendsto_eventually_const (a : ℕ → ℤ) (z : ℤ)
    (h : Tendsto (fun n => (a n : ℝ)) atTop (nhds (z : ℝ))) :
    ∀ᶠ n : ℕ in atTop, a n = z := by
  have hball : Metric.ball (z : ℝ) (1 / 2) ∈ nhds (z : ℝ) :=
    Metric.ball_mem_nhds _ (by norm_num)
  have hev := h hball
  filter_upwards [hev] with n hn
  have hdist : dist ((a n : ℝ)) (z : ℝ) < 1 / 2 := hn
  have habs : |(a n : ℝ) - (z : ℝ)| < 1 / 2 := by
    simpa [Real.dist_eq] using hdist
  have hcast : |(a n - z : ℤ)| < 1 := by
    have h1 : |((a n - z : ℤ) : ℝ)| < 1 := by
      have : ((a n - z : ℤ) : ℝ) = (a n : ℝ) - (z : ℝ) := by push_cast; ring
      rw [this]
      linarith
    have h2 : ((|a n - z| : ℤ) : ℝ) < (1 : ℝ) := by
      rw [Int.cast_abs]; exact h1
    exact_mod_cast h2
  have hzero : a n - z = 0 := Int.abs_lt_one_iff.mp hcast
  omega

/-! ### 关键引理 7：迭代恒等式 -/

/-- **引理 7**：两序列在 n≥N 上满足同一递推 (n+1)aₙ − aₙ₊₁ = 1，
则对 m≥N：a_N − b_N = (N!/m!)·(a_m − b_m)。纯代数归纳。 -/
theorem iterate_ratio (a b : ℕ → ℝ) (N : ℕ)
    (ha : ∀ n, N ≤ n → (n + 1 : ℝ) * a n - a (n + 1) = 1)
    (hb : ∀ n, N ≤ n → (n + 1 : ℝ) * b n - b (n + 1) = 1) :
    ∀ m, N ≤ m → a N - b N =
      ((N.factorial : ℝ) / (m.factorial : ℝ)) * (a m - b m) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have hf : (N.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  | succ m hm ih =>
    have hd : a (m + 1) - b (m + 1) = (m + 1 : ℝ) * (a m - b m) := by
      have ha' := ha m hm
      have hb' := hb m hm
      linarith
    have hfac : ((m + 1).factorial : ℝ) = (m + 1 : ℝ) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hm1 : (m + 1 : ℝ) ≠ 0 := by positivity
    calc a N - b N
        = ((N.factorial : ℝ) / (m.factorial : ℝ)) * (a m - b m) := ih
      _ = ((N.factorial : ℝ) / (m.factorial : ℝ)) *
          ((a (m + 1) - b (m + 1)) / (m + 1 : ℝ)) := by
          rw [hd]; field_simp
      _ = ((N.factorial : ℝ) / ((m + 1).factorial : ℝ)) * (a (m + 1) - b (m + 1)) := by
          rw [hfac]; field_simp

/-! ### 主定理 -/

set_option maxHeartbeats 1600000 in
/-- **主定理（Proposition 4，双向）**：
e + π 有理 ↔ n·{-n!π} → 1。

这是等价判据，不是 e+π 无理性的证明；右侧极限是否成立仍开放。 -/
theorem factorial_criterion :
    (∃ q : ℚ, Real.exp 1 + Real.pi = q) ↔
    Tendsto (fun n : ℕ => (n : ℝ) * uFrac n) atTop (nhds 1) := by
  constructor
  · -- 正向：有理 ⇒ 最终 u = t ⇒ n·u → 1
    intro h
    have hev := uFrac_eq_tFrac_of_rational h
    have hcong : (fun n : ℕ => (n : ℝ) * uFrac n) =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) * tFrac n) := by
      filter_upwards [hev] with n hn
      rw [hn]
    exact (tendsto_congr' hcong).mpr tFrac_tendsto
  · -- 反向：n·u → 1 ⇒ 有理
    intro h
    -- 整值递推序列 cₙ = (n+1)uₙ − uₙ₊₁
    let c : ℕ → ℤ := fun n => Classical.choose (recurrence_u n)
    have hc : ∀ n : ℕ, (n + 1 : ℝ) * uFrac n - uFrac (n + 1) = (c n : ℝ) :=
      fun n => Classical.choose_spec (recurrence_u n)
    -- uₙ → 0（由 n·uₙ → 1 除以 n）
    have hu0 : Tendsto uFrac atTop (nhds 0) := by
      have hdiv : Tendsto (fun n : ℕ => ((n : ℝ) * uFrac n) / (n : ℝ))
          atTop (nhds 0) :=
        h.div_atTop tendsto_natCast_atTop_atTop
      have hcong' : (fun n : ℕ => ((n : ℝ) * uFrac n) / (n : ℝ)) =ᶠ[atTop] uFrac := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        field_simp
      exact (tendsto_congr' hcong').mp hdiv
    -- cₙ → 1
    have hc_tendsto : Tendsto (fun n => (c n : ℝ)) atTop (nhds (1 : ℝ)) := by
      have h1 : Tendsto (fun n : ℕ => (n + 1 : ℝ) * uFrac n) atTop (nhds 1) := by
        have hcong : (fun n : ℕ => (n + 1 : ℝ) * uFrac n) =ᶠ[atTop]
            (fun n : ℕ => ((n : ℝ) * uFrac n) + uFrac n) := by
          filter_upwards with n
          ring
        refine (tendsto_congr' hcong).mpr ?_
        simpa using (h.add hu0)
      have h2 : Tendsto (fun n : ℕ => uFrac (n + 1)) atTop (nhds 0) :=
        hu0.comp (tendsto_add_atTop_nat 1)
      have hsub : Tendsto (fun n : ℕ => (n + 1 : ℝ) * uFrac n - uFrac (n + 1))
          atTop (nhds (1 - 0)) := h1.sub h2
      have hcong'' : (fun n : ℕ => (c n : ℝ)) =ᶠ[atTop]
          (fun n : ℕ => (n + 1 : ℝ) * uFrac n - uFrac (n + 1)) := by
        filter_upwards with n
        exact (hc n).symm
      simpa using ((tendsto_congr' hcong'').mpr hsub)
    -- 最终 cₙ = 1
    have hev1 : ∀ᶠ n : ℕ in atTop, c n = 1 := by
      have hcast : Tendsto (fun n => (c n : ℝ)) atTop (nhds ((1 : ℤ) : ℝ)) := by
        convert hc_tendsto using 1
        simp
      exact int_tendsto_eventually_const c 1 hcast
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev1
    -- t 的递推恒 = 1（n ≥ 1）
    have ht_rec : ∀ n : ℕ, 1 ≤ n → (n + 1 : ℝ) * tFrac n - tFrac (n + 1) = 1 := by
      intro n hn
      have := tail_recurrence n
      have ht1 : tFrac n = tail n := tFrac_eq_tail n hn
      have ht2 : tFrac (n + 1) = tail (n + 1) := tFrac_eq_tail (n + 1) (by omega)
      rw [ht1, ht2]
      linarith
    -- 取公共尾部 N ≥ 2
    let N := max N₁ 2
    have hN1 : N₁ ≤ N := le_max_left _ _
    have hN2 : 2 ≤ N := le_max_right _ _
    have hu_rec : ∀ n : ℕ, N ≤ n → (n + 1 : ℝ) * uFrac n - uFrac (n + 1) = 1 := by
      intro n hn
      have hc1 : c n = 1 := hN₁ n (le_trans hN1 hn)
      simpa [hc1] using hc n
    have ht_rec' : ∀ n : ℕ, N ≤ n → (n + 1 : ℝ) * tFrac n - tFrac (n + 1) = 1 :=
      fun n hn => ht_rec n (by omega)
    -- 迭代恒等式
    have hiter := iterate_ratio uFrac tFrac N hu_rec ht_rec'
    -- |u_N − t_N| ≤ N!/m! → 0
    have hdiff0 : uFrac N - tFrac N = 0 := by
      have hbound : ∀ m : ℕ, N ≤ m → |uFrac N - tFrac N| ≤
          (N.factorial : ℝ) / (m.factorial : ℝ) := by
        intro m hm
        have him := hiter m hm
        have hsub : |uFrac m - tFrac m| ≤ 1 := by
          have hu0 : 0 ≤ uFrac m := Int.fract_nonneg _
          have ht0 : 0 ≤ tFrac m := Int.fract_nonneg _
          have hu1 : uFrac m < 1 := Int.fract_lt_one _
          have ht1 : tFrac m < 1 := Int.fract_lt_one _
          rw [abs_le]
          constructor <;> linarith
        calc |uFrac N - tFrac N|
            = |((N.factorial : ℝ) / (m.factorial : ℝ)) * (uFrac m - tFrac m)| := by
              rw [him]
          _ = ((N.factorial : ℝ) / (m.factorial : ℝ)) * |uFrac m - tFrac m| := by
              rw [abs_mul, abs_of_nonneg (by positivity)]
          _ ≤ ((N.factorial : ℝ) / (m.factorial : ℝ)) * 1 :=
              mul_le_mul_of_nonneg_left hsub (by positivity)
          _ = (N.factorial : ℝ) / (m.factorial : ℝ) := by ring
      have htend : Tendsto (fun m : ℕ => (N.factorial : ℝ) / (m.factorial : ℝ))
          atTop (nhds 0) := by
        have hfac : Tendsto (fun m : ℕ => (m.factorial : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop
        exact tendsto_const_nhds.div_atTop hfac
      have h0 : |uFrac N - tFrac N| ≤ 0 := by
        apply ge_of_tendsto htend
        filter_upwards [eventually_ge_atTop N] with m hm
        exact hbound m hm
      have habs0 : |uFrac N - tFrac N| = 0 := by
        linarith [abs_nonneg (uFrac N - tFrac N)]
      exact abs_eq_zero.mp habs0
    have huN : uFrac N = tFrac N := by linarith
    -- N!(e+π) ∈ ℤ
    have hz : ∃ z : ℤ, (N.factorial : ℝ) * (Real.exp 1 + Real.pi) = z := by
      have hfract : Int.fract ((N.factorial : ℝ) * Real.exp 1 +
          (N.factorial : ℝ) * Real.pi) = 0 := by
        have harg : (N.factorial : ℝ) * Real.exp 1 + (N.factorial : ℝ) * Real.pi =
            (N.factorial : ℝ) * Real.exp 1 - (-(N.factorial : ℝ) * Real.pi) := by ring
        rw [harg]
        have hsub : Int.fract ((N.factorial : ℝ) * Real.exp 1 -
            (-(N.factorial : ℝ) * Real.pi)) =
            Int.fract (Int.fract ((N.factorial : ℝ) * Real.exp 1) -
              Int.fract (-(N.factorial : ℝ) * Real.pi)) := by
          rw [← Int.fract_fract_sub_fract]
        rw [hsub]
        have hu : Int.fract (-(N.factorial : ℝ) * Real.pi) = uFrac N := rfl
        have ht : Int.fract ((N.factorial : ℝ) * Real.exp 1) = tFrac N := rfl
        rw [hu, ht, huN]
        simp
      have := Int.fract_eq_zero_iff.mp hfract
      obtain ⟨z, hz⟩ := this
      use z
      linarith
    obtain ⟨z, hz⟩ := hz
    have hfac : (N.factorial : ℝ) ≠ 0 := by positivity
    have hrat : Real.exp 1 + Real.pi = (z : ℝ) / (N.factorial : ℝ) := by
      field_simp at hz ⊢
      linarith
    use (z / (N.factorial : ℤ) : ℚ)
    have hcast : ((z / (N.factorial : ℤ) : ℚ) : ℝ) = (z : ℝ) / (N.factorial : ℝ) := by
      push_cast
      rfl
    rw [hrat, ← hcast]

end FactorialCriterion

/-! ### 公理审计（逐字输出，见报告） -/
#print axioms FactorialCriterion.exp_one_eq_tsum
#print axioms FactorialCriterion.summable_inv_factorial
#print axioms FactorialCriterion.summable_shift
#print axioms FactorialCriterion.tail_eq_shift
#print axioms FactorialCriterion.factorial_ratio_le
#print axioms FactorialCriterion.tail_pos
#print axioms FactorialCriterion.tsum_pow_succ
#print axioms FactorialCriterion.tail_lt_one
#print axioms FactorialCriterion.tail_mem_Ioo
#print axioms FactorialCriterion.nfact_mul_exp
#print axioms FactorialCriterion.front_is_int
#print axioms FactorialCriterion.tFrac_eq_tail
#print axioms FactorialCriterion.tFrac_bounds
#print axioms FactorialCriterion.tFrac_tendsto
#print axioms FactorialCriterion.uFrac_eq_tFrac_of_rational
#print axioms FactorialCriterion.fract_mul_succ
#print axioms FactorialCriterion.recurrence_u
#print axioms FactorialCriterion.recurrence_t
#print axioms FactorialCriterion.int_tendsto_eventually_const
#print axioms FactorialCriterion.iterate_ratio
#print axioms FactorialCriterion.factorial_criterion