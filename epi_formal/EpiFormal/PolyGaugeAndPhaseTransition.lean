import Mathlib
import EpiFormal.TrichotomyAndPolyExtension
import EpiFormal.GaugeCircle
import EpiFormal.GaugeLiminfComplete
import EpiFormal.WeightedExactDim

/-!
# 一般多项式增长递推的临界 Hausdorff 规范三分法、精确规范与加权相变维数

本模块完成论文二 §6.3 剩余核心定理在 Lean 4（仅依赖标准基础公理
`[propext, Classical.choice, Quot.sound]`，零 `sorry`）中的完整形式化，覆盖任意
`P : PolyRecData`（`r ≥ 1`, `c ≥ 1`, `d : ℤ`, `Q_{j+1} = (c j^r + d) Q_j + Q_{j-1}`）：

1. **`lem:poly-growth(iv)` 与阶乘上界**：
   - `poly_Q_le_factorial_of_ge` / `poly_Q_le_factorial`：`Q_m ≤ C_hi * K^m * (m!)^r`；
   - `poly_log_Q_asymptotic`：`log Q_n = r n log n + (log c - r) n + O(log n)`。

2. **分片线性规范函数与 `rem:poly-gauge-scale`**：
   - `polyCritGauge P k`（节点 `1/Q_n` 处取 `(2k+1)^{-n}`）与 `polyBinaryGauge P`（取 `2^{-n}`）；
   - 单调性、连续性、端点精确值与对数渐近标度 `-log h_k(t) ~ (log(2k+1)/r) * log(1/t)/log log(1/t)`。

3. **内蕴晶格 `P.latticePoly` 的模 `1` 稠密性与无符号精确极限集数字刻画**：
   - `exists_mem_latticePoly_pos_lt`：由 `theta_sub_ratio_pos_and_lt` 直接构造任意小正晶格元；
   - `poly_unsigned_exact_limit_iff_defect_binary` 与空集刻画 `t ∉ (1/c)ℤ≥0`。

4. **`thm:poly-gauge-trichotomy(i),(ii)`、`cor:poly-exact-gauge` 与 `cor:poly-liminf-gauges`**：
   - 统一的参数化 `b`-叉紧致 Cantor 树 `PolyWordTree`（同时实例化 `(2k+1)`-叉与 `2`-叉）；
   - 在 `ℝ` 与 `UnitAddCircle`（`ℝ/ℤ`）上完整证明严格子水平集零测度、精确水平集正测度/局部无穷测度、
     `σ`-有限覆盖、无符号精确极限集在 `polyCritGauge` 下零测度及在 `polyBinaryGauge` 下正/局部无穷测度与
     `σ`-有限覆盖，以及慢/快规范两分支与 `liminf` 四分法。

5. **`thm:poly-phase-transition(ii)`（一般 `0 ≤ α < r` 精确 Hausdorff 维数 `1 - α/r`）**：
   - 上界 `dimH {x : ℝ | P.polyWeightedExponent α x ≤ ENNReal.ofReal t} ≤ ENNReal.ofReal (1 - α / r)`；
   - 下界 `ENNReal.ofReal (1 - α / r) ≤ dimH {x ∈ [0, 1] | j^α ‖Q_j x‖ → t}`；
   - 合并精确维数等式（含 `α = 0` 时 `0 ≤ t ≤ 1/2` 与 `t > 1/2` 情形）。
-/

open Real Filter Topology Set Finset MeasureTheory Classification SpectralGap DimHCore DimHFinite
  FullSpectrumDiscrete GaugeNull GaugeExact GaugeCircle GaugeLiminf GaugeScaleComparison
  WeightedExactDim TrichotomyAndPolyExtension
open scoped ENNReal NNReal BigOperators

namespace PolyGaugeAndPhaseTransition

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 第一部分：`lem:poly-growth(iv)` 与阶乘上界 -/

/-- 非渐近阶乘上界底数常数 $K := c + |d| + 1 > 1$。 -/
def polyKUpper (P : PolyRecData) : ℝ :=
  (P.c : ℝ) + |(P.d : ℝ)| + 1

lemma one_lt_polyKUpper (P : PolyRecData) : 1 < polyKUpper P := by
  unfold polyKUpper
  have hc : (1 : ℝ) ≤ (P.c : ℝ) := by exact_mod_cast P.hc
  have hd : 0 ≤ |(P.d : ℝ)| := abs_nonneg _
  linarith

lemma polyKUpper_pos (P : PolyRecData) : 0 < polyKUpper P :=
  lt_trans zero_lt_one (one_lt_polyKUpper P)

/-- 非渐近阶乘上界前置常数 $C_{\mathrm{hi}} := Q_{J_0+1} / (K^{J_0+1} ((J_0+1)!)^r) > 0$。 -/
def polyCHi (P : PolyRecData) : ℝ :=
  (P.Q (P.J₀ + 1) : ℝ) /
    ((polyKUpper P) ^ (P.J₀ + 1) * (Nat.factorial (P.J₀ + 1) : ℝ) ^ P.r)

lemma polyCHi_pos (P : PolyRecData) : 0 < polyCHi P := by
  unfold polyCHi
  have hQ : (0 : ℝ) < (P.Q (P.J₀ + 1) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ + 1)
  have hK : 0 < polyKUpper P := polyKUpper_pos P
  have hf : (0 : ℝ) < (Nat.factorial (P.J₀ + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (P.J₀ + 1)
  positivity

/-- **Lemma `lem:poly-growth` 阶乘上界（$m \ge J_0 + 1$）**：
    对一切 $m \ge J_0 + 1$，有 $Q_m \le C_{\mathrm{hi}} K^m (m!)^r$。 -/
theorem poly_Q_le_factorial_of_ge (P : PolyRecData) {m : ℕ} (hm : P.J₀ + 1 ≤ m) :
    (P.Q m : ℝ) ≤ polyCHi P * (polyKUpper P) ^ m * (Nat.factorial m : ℝ) ^ P.r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  set J := P.J₀ + 1 with hJdef
  have hind : ∀ k : ℕ, (P.Q (J + k) : ℝ) ≤
      (P.Q J : ℝ) * (polyKUpper P) ^ k *
        ((Nat.factorial (J + k) : ℝ) / (Nat.factorial J : ℝ)) ^ P.r := by
    intro k
    induction k with
    | zero =>
        have hf : (Nat.factorial J : ℝ) ≠ 0 := by positivity
        simp [hf]
    | succ k ih =>
        have hJk : P.J₀ + 1 ≤ J + k := by omega
        have hratio := P.poly_Q_ratio_bounds hJk
        have hQj : (0 : ℝ) < (P.Q (J + k) : ℝ) := by exact_mod_cast P.hQ_pos (J + k)
        have hstep1 : (P.Q (J + k + 1) : ℝ) ≤
            polyKUpper P * ((J + k : ℕ) : ℝ) ^ P.r * (P.Q (J + k) : ℝ) := by
          have h1 : (P.Q (J + k + 1) : ℝ) / (P.Q (J + k) : ℝ) ≤
              polyKUpper P * ((J + k : ℕ) : ℝ) ^ P.r := by
            simpa [polyKUpper] using le_trans (le_of_lt hratio.2.1) hratio.2.2
          have h2 := (div_le_iff₀ hQj).mp h1
          linarith
        have hle_succ : ((J + k : ℕ) : ℝ) ≤ ((J + k + 1 : ℕ) : ℝ) := by
          push_cast; linarith
        have hpow_succ : ((J + k : ℕ) : ℝ) ^ P.r ≤ ((J + k + 1 : ℕ) : ℝ) ^ P.r :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hle_succ P.r
        have hKnn : 0 ≤ polyKUpper P := le_of_lt (polyKUpper_pos P)
        have hstep2 : (P.Q (J + k + 1) : ℝ) ≤
            polyKUpper P * ((J + k + 1 : ℕ) : ℝ) ^ P.r * (P.Q (J + k) : ℝ) := by
          calc (P.Q (J + k + 1) : ℝ)
              ≤ polyKUpper P * ((J + k : ℕ) : ℝ) ^ P.r * (P.Q (J + k) : ℝ) := hstep1
            _ ≤ polyKUpper P * ((J + k + 1 : ℕ) : ℝ) ^ P.r * (P.Q (J + k) : ℝ) := by
                gcongr
        have hfact : (Nat.factorial (J + (k + 1)) : ℝ) =
            ((J + k + 1 : ℕ) : ℝ) * (Nat.factorial (J + k) : ℝ) := by
          have hadd : J + (k + 1) = (J + k) + 1 := by omega
          rw [hadd, Nat.factorial_succ]
          push_cast; ring
        have hadd : J + (k + 1) = J + k + 1 := by omega
        rw [hadd]
        calc (P.Q (J + k + 1) : ℝ)
            ≤ polyKUpper P * ((J + k + 1 : ℕ) : ℝ) ^ P.r * (P.Q (J + k) : ℝ) := hstep2
          _ ≤ polyKUpper P * ((J + k + 1 : ℕ) : ℝ) ^ P.r *
                ((P.Q J : ℝ) * (polyKUpper P) ^ k *
                  ((Nat.factorial (J + k) : ℝ) / (Nat.factorial J : ℝ)) ^ P.r) := by
                gcongr
          _ = (P.Q J : ℝ) * (polyKUpper P) ^ (k + 1) *
                ((Nat.factorial (J + (k + 1)) : ℝ) / (Nat.factorial J : ℝ)) ^ P.r := by
                rw [hfact, mul_div_assoc, mul_pow, pow_succ]
                ring
          _ = (P.Q J : ℝ) * (polyKUpper P) ^ (k + 1) *
                ((Nat.factorial (J + k + 1) : ℝ) / (Nat.factorial J : ℝ)) ^ P.r := by
                rw [hadd]
  have hmain := hind n
  have hK : (polyKUpper P) ^ J ≠ 0 := pow_ne_zero J (ne_of_gt (polyKUpper_pos P))
  have hf : (Nat.factorial J : ℝ) ^ P.r ≠ 0 := by positivity
  have heq : (P.Q J : ℝ) * (polyKUpper P) ^ n *
      ((Nat.factorial (J + n) : ℝ) / (Nat.factorial J : ℝ)) ^ P.r =
      polyCHi P * (polyKUpper P) ^ (J + n) * (Nat.factorial (J + n) : ℝ) ^ P.r := by
    have hK1 : polyKUpper P ≠ 0 := (polyKUpper_pos P).ne'
    have hf_ne : (Nat.factorial (P.J₀ + 1) : ℝ) ^ P.r ≠ 0 := by positivity
    unfold polyCHi
    dsimp [J]
    rw [div_pow, pow_add (polyKUpper P) (P.J₀ + 1) n]
    field_simp [hK1, hf_ne]
  linarith

/-- 对所有 $m \in \mathbb{N}$ 成立的全局阶乘上界 $Q_m \le C K^m (m!)^r$。 -/
theorem poly_Q_le_factorial (P : PolyRecData) :
    ∃ C K : ℝ, 0 < C ∧ 1 < K ∧
      ∀ m : ℕ, (P.Q m : ℝ) ≤ C * K ^ m * (Nat.factorial m : ℝ) ^ P.r := by
  set J := P.J₀ + 1
  let f : ℕ → ℝ := fun m =>
    (P.Q m : ℝ) / ((polyKUpper P) ^ m * (Nat.factorial m : ℝ) ^ P.r)
  set C₀ : ℝ := max (polyCHi P) ((Finset.range (J + 1)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ f)
  have hC₀_ge_chi : polyCHi P ≤ C₀ := le_max_left _ _
  have hC₀_pos : 0 < C₀ := lt_of_lt_of_le (polyCHi_pos P) hC₀_ge_chi
  refine ⟨C₀, polyKUpper P, hC₀_pos, one_lt_polyKUpper P, fun m => ?_⟩
  have hK := polyKUpper_pos P
  have hf_pos : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  by_cases hm : J ≤ m
  · have h1 := poly_Q_le_factorial_of_ge P hm
    have hnn : 0 ≤ (polyKUpper P) ^ m * (Nat.factorial m : ℝ) ^ P.r := by positivity
    calc (P.Q m : ℝ)
        ≤ polyCHi P * (polyKUpper P) ^ m * (Nat.factorial m : ℝ) ^ P.r := h1
      _ = polyCHi P * ((polyKUpper P) ^ m * (Nat.factorial m : ℝ) ^ P.r) := by ring
      _ ≤ C₀ * ((polyKUpper P) ^ m * (Nat.factorial m : ℝ) ^ P.r) :=
            mul_le_mul_of_nonneg_right hC₀_ge_chi hnn
      _ = C₀ * (polyKUpper P) ^ m * (Nat.factorial m : ℝ) ^ P.r := by ring
  · have hm_lt : m < J + 1 := by omega
    have hmem : m ∈ Finset.range (J + 1) := Finset.mem_range.mpr hm_lt
    have hle_sup : f m ≤ (Finset.range (J + 1)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ f :=
      Finset.le_sup' f hmem
    have hle_C₀ : f m ≤ C₀ := le_trans hle_sup (le_max_right _ _)
    have hden_pos : 0 < (polyKUpper P) ^ m * (Nat.factorial m : ℝ) ^ P.r := by positivity
    have h1 := (div_le_iff₀ hden_pos).mp hle_C₀
    linarith

/-- 对任意实底数 $b \in \mathbb{R}$，有 $b^m / Q_m \to 0$（$m \to \infty$）。 -/
theorem poly_pow_div_Q_of_base_tendsto_zero (P : PolyRecData) (b : ℝ) :
    Tendsto (fun m : ℕ => b ^ m / (P.Q m : ℝ)) atTop (nhds 0) := by
  set B : ℝ := (P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)
  have hB_pos : 0 < B := by
    have hc : (1 : ℝ) ≤ (P.c : ℝ) := by exact_mod_cast P.hc
    positivity
  set R : ℝ := |b| / B
  have hfact_lim : Tendsto (fun m : ℕ => R ^ m / (Nat.factorial m : ℝ)) atTop (nhds 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop R
  have hlim : Tendsto (fun m : ℕ => (1 / P.C_J₁) * (R ^ m / (Nat.factorial m : ℝ)))
      atTop (nhds 0) := by
    simpa using hfact_lim.const_mul (1 / P.C_J₁)
  have hlim_neg : Tendsto (fun m : ℕ => -((1 / P.C_J₁) * (R ^ m / (Nat.factorial m : ℝ))))
      atTop (nhds 0) := by
    simpa using hlim.neg
  have hbound : ∀ᶠ m : ℕ in atTop,
      |b ^ m / (P.Q m : ℝ)| ≤ (1 / P.C_J₁) * (R ^ m / (Nat.factorial m : ℝ)) := by
    filter_upwards [eventually_ge_atTop P.J₁] with m hm
    have hQge := P.poly_Q_ge_factorial hm
    have hfact1 : (1 : ℝ) ≤ (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hfactr : (Nat.factorial m : ℝ) ≤ (Nat.factorial m : ℝ) ^ P.r := by
      calc (Nat.factorial m : ℝ) = (Nat.factorial m : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (Nat.factorial m : ℝ) ^ P.r := pow_le_pow_right₀ hfact1 P.hr
    have hQge' : P.C_J₁ * B ^ m * (Nat.factorial m : ℝ) ≤ (P.Q m : ℝ) := by
      have hCB : 0 ≤ P.C_J₁ * B ^ m := mul_nonneg (le_of_lt P.C_J₁_pos) (by positivity)
      exact le_trans (mul_le_mul_of_nonneg_left hfactr hCB) hQge
    have hQpos : (0 : ℝ) < (P.Q m : ℝ) := by exact_mod_cast P.hQ_pos m
    have hCpos := P.C_J₁_pos
    have hden_pos : 0 < P.C_J₁ * B ^ m * (Nat.factorial m : ℝ) := by positivity
    rw [abs_div, abs_of_pos hQpos, abs_pow]
    calc |b| ^ m / (P.Q m : ℝ)
        ≤ |b| ^ m / (P.C_J₁ * B ^ m * (Nat.factorial m : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) hden_pos hQge'
      _ = (1 / P.C_J₁) * (R ^ m / (Nat.factorial m : ℝ)) := by
          dsimp [R, B]; simp only [div_pow]; field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim_neg hlim
    (hbound.mono fun _ hm => (abs_le.mp hm).1)
    (hbound.mono fun _ hm => (abs_le.mp hm).2)

/-- 初等对数界：对 $|u| \le 1/2$，有 $|\log(1 + u)| \le 2 |u|$。 -/
lemma abs_log_one_add_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u)| ≤ 2 * |u| := by
  have hu_bounds := abs_le.mp hu
  have h1u : 0 < 1 + u := by linarith
  have hupper : Real.log (1 + u) ≤ u := Real.log_le_sub_one_of_pos h1u |>.trans_eq (by ring)
  have hlower : -(2 * |u|) ≤ Real.log (1 + u) := by
    by_cases hu0 : 0 ≤ u
    · have hlog_nn : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
      have habs_nn : 0 ≤ 2 * |u| := by positivity
      linarith
    · have hu_neg : u < 0 := lt_of_not_ge hu0
      have hinv_pos : 0 < (1 + u)⁻¹ := inv_pos.mpr h1u
      have hlog_inv : Real.log ((1 + u)⁻¹) ≤ (1 + u)⁻¹ - 1 :=
        Real.log_le_sub_one_of_pos hinv_pos
      rw [Real.log_inv] at hlog_inv
      have hfrac : (1 + u)⁻¹ - 1 = (-u) / (1 + u) := by field_simp; ring
      have h2u : (-u) / (1 + u) ≤ 2 * (-u) := by
        rw [div_le_iff₀ h1u]
        nlinarith
      have habs_eq : |u| = -u := abs_of_neg hu_neg
      linarith
  rw [abs_le]
  exact ⟨hlower, by linarith [le_abs_self u, abs_nonneg u]⟩

/-- 调和和界：对 $n \ge 1$，有 $\sum_{j=1}^{n-1} \frac{1}{j+1} \le \log n$，从而 $\sum_{j=1}^{n-1} \frac{1}{j} \le 1 + \log n$。 -/
lemma sum_inv_succ_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / ((j : ℝ) + 1) ≤ Real.log (n : ℝ) := by
  have hstep : ∀ j ∈ Finset.Ico 1 n,
      (1 : ℝ) / ((j : ℝ) + 1) ≤ Real.log ((j : ℝ) + 1) - Real.log (j : ℝ) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by linarith
    have hlog := Real.log_le_sub_one_of_pos (div_pos hjpos hj1pos)
    have hlog_eq : Real.log ((j : ℝ) / ((j : ℝ) + 1)) = Real.log (j : ℝ) - Real.log ((j : ℝ) + 1) :=
      Real.log_div hjpos.ne' hj1pos.ne'
    have hsub : (j : ℝ) / ((j : ℝ) + 1) - 1 = -(1 / ((j : ℝ) + 1)) := by field_simp; ring
    linarith
  calc ∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / ((j : ℝ) + 1)
      ≤ ∑ j ∈ Finset.Ico 1 n, (Real.log ((j : ℝ) + 1) - Real.log (j : ℝ)) :=
        Finset.sum_le_sum hstep
    _ = Real.log (n : ℝ) - Real.log ((1 : ℕ) : ℝ) := by
        simpa using Finset.sum_Ico_sub (fun j : ℕ => Real.log (j : ℝ)) hn
    _ = Real.log (n : ℝ) := by simp

lemma sum_inv_le_one_add_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / (j : ℝ) ≤ 1 + Real.log (n : ℝ) := by
  rcases eq_or_lt_of_le hn with rfl | hn2
  · simp
  · have hsplit : Finset.Ico 1 n = insert 1 (Finset.Ico 2 n) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnot : 1 ∉ Finset.Ico 2 n := by simp
    rw [hsplit, Finset.sum_insert hnot]
    have hshift : ∑ j ∈ Finset.Ico 2 n, (1 : ℝ) / (j : ℝ) =
        ∑ j ∈ Finset.Ico 1 (n - 1), (1 : ℝ) / ((j : ℝ) + 1) := by
      refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_Ico] at hj ⊢
        omega
      · intro j₁ hj₁ j₂ hj₂ h
        simp only [Finset.mem_Ico] at hj₁ hj₂
        omega
      · intro j hj
        simp only [Finset.mem_Ico] at hj
        refine ⟨j + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro j hj
        simp only [Finset.mem_Ico] at hj
        have h1 : 1 ≤ j := by omega
        have hcast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
          have : (j - 1) + 1 = j := Nat.sub_add_cancel h1
          exact_mod_cast this
        rw [hcast]
    rw [hshift]
    have h1 : ∑ j ∈ Finset.Ico 1 (n - 1), (1 : ℝ) / ((j : ℝ) + 1) ≤ Real.log ((n - 1 : ℕ) : ℝ) :=
      sum_inv_succ_le_log (n - 1) (by omega)
    have h2 : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast (by omega : 0 < n - 1)
      · exact_mod_cast (by omega : n - 1 ≤ n)
    have h1_inv : (1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h1_inv]
    linarith [h1, h2]

/-- 对数和渐近：对 $n \ge 2$，
    $\left|\sum_{j=1}^{n-1} \log j - (n \log n - n)\right| \le 1 + 2 \log n$。 -/
lemma sum_log_asymptotic (n : ℕ) (hn : 2 ≤ n) :
    |∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ) - ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ))| ≤
      1 + 2 * Real.log (n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hdiff_bounds : ∀ j ∈ Finset.Ico 1 n,
      1 - (1 : ℝ) / ((j : ℝ) + 1) ≤
        ((j : ℝ) + 1) * Real.log ((j : ℝ) + 1) - (j : ℝ) * Real.log (j : ℝ) - Real.log ((j : ℝ) + 1) ∧
      ((j : ℝ) + 1) * Real.log ((j : ℝ) + 1) - (j : ℝ) * Real.log (j : ℝ) - Real.log ((j : ℝ) + 1) ≤ 1 := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by linarith
    have heq : ((j : ℝ) + 1) * Real.log ((j : ℝ) + 1) - (j : ℝ) * Real.log (j : ℝ) -
        Real.log ((j : ℝ) + 1) = (j : ℝ) * (Real.log ((j : ℝ) + 1) - Real.log (j : ℝ)) := by ring
    rw [heq]
    constructor
    · have h1 := Real.log_le_sub_one_of_pos (div_pos hjpos hj1pos)
      rw [Real.log_div hjpos.ne' hj1pos.ne'] at h1
      have h2 : (1 : ℝ) / ((j : ℝ) + 1) ≤ Real.log ((j : ℝ) + 1) - Real.log (j : ℝ) := by
        have hs : (j : ℝ) / ((j : ℝ) + 1) - 1 = -(1 / ((j : ℝ) + 1)) := by field_simp; ring
        linarith
      have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt hjpos)
      have hfr : (j : ℝ) * (1 / ((j : ℝ) + 1)) = 1 - 1 / ((j : ℝ) + 1) := by field_simp; ring
      linarith
    · have h1 := Real.log_le_sub_one_of_pos (div_pos hj1pos hjpos)
      rw [Real.log_div hj1pos.ne' hjpos.ne'] at h1
      have h2 : Real.log ((j : ℝ) + 1) - Real.log (j : ℝ) ≤ 1 / (j : ℝ) := by
        have hs : ((j : ℝ) + 1) / (j : ℝ) - 1 = 1 / (j : ℝ) := by field_simp; ring
        linarith
      have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt hjpos)
      have hfr : (j : ℝ) * (1 / (j : ℝ)) = 1 := by field_simp
      linarith
  have htel : ∑ j ∈ Finset.Ico 1 n,
      (((j : ℝ) + 1) * Real.log ((j : ℝ) + 1) - (j : ℝ) * Real.log (j : ℝ)) =
      (n : ℝ) * Real.log (n : ℝ) := by
    have h := Finset.sum_Ico_sub (fun j : ℕ => (j : ℝ) * Real.log (j : ℝ)) hn1
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hshift_log : ∑ j ∈ Finset.Ico 1 n, Real.log ((j : ℝ) + 1) =
      ∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ) + Real.log (n : ℝ) := by
    have h := Finset.sum_Ico_sub (fun j : ℕ => Real.log (j : ℝ)) hn1
    have h1 : ∑ j ∈ Finset.Ico 1 n, Real.log ((j : ℝ) + 1) -
        ∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ) = Real.log (n : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      simpa using h
    linarith
  have hsum_lo : ((n : ℝ) - 1) - Real.log (n : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ) + Real.log (n : ℝ)) := by
    have hs1 : ∑ j ∈ Finset.Ico 1 n, (1 - (1 : ℝ) / ((j : ℝ) + 1)) ≤
        ∑ j ∈ Finset.Ico 1 n,
          (((j : ℝ) + 1) * Real.log ((j : ℝ) + 1) - (j : ℝ) * Real.log (j : ℝ) -
            Real.log ((j : ℝ) + 1)) :=
      Finset.sum_le_sum fun j hj => (hdiff_bounds j hj).1
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
      Finset.sum_sub_distrib, htel, hshift_log] at hs1
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simpa using Nat.cast_sub hn1
    rw [hcast] at hs1
    have hinv := sum_inv_succ_le_log n hn1
    linarith
  have hsum_hi :
      (n : ℝ) * Real.log (n : ℝ) - (∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ) + Real.log (n : ℝ)) ≤
        (n : ℝ) - 1 := by
    have hs2 : ∑ j ∈ Finset.Ico 1 n,
        (((j : ℝ) + 1) * Real.log ((j : ℝ) + 1) - (j : ℝ) * Real.log (j : ℝ) -
          Real.log ((j : ℝ) + 1)) ≤
        ∑ _j ∈ Finset.Ico 1 n, (1 : ℝ) :=
      Finset.sum_le_sum fun j hj => (hdiff_bounds j hj).2
    rw [Finset.sum_sub_distrib, htel, hshift_log, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      mul_one] at hs2
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simpa using Nat.cast_sub hn1
    rw [hcast] at hs2
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Lemma `lem:poly-growth`(iv)**：
    $\log Q_n = r n \log n + (\log c - r) n + O(\log n)$。 -/
theorem poly_log_Q_asymptotic (P : PolyRecData) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      |Real.log (P.Q n : ℝ) -
        ((P.r : ℝ) * (n : ℝ) * Real.log (n : ℝ) +
          (Real.log (P.c : ℝ) - (P.r : ℝ)) * (n : ℝ))| ≤ C * Real.log (n : ℝ) := by
  set J₂ : ℕ := max P.J₁ (2 * P.d.natAbs + 3)
  have hJ₂_J₁ : P.J₁ ≤ J₂ := le_max_left _ _
  have hJ₂_J₀ : P.J₀ + 1 ≤ J₂ := le_trans P.J₁_ge_J₀_succ hJ₂_J₁
  have hJ₂_abs : 2 * P.d.natAbs + 3 ≤ J₂ := le_max_right _ _
  have hJ₂_ge3 : 3 ≤ J₂ := by omega
  have hc_pos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
  have hc1 : (1 : ℝ) ≤ (P.c : ℝ) := by exact_mod_cast P.hc
  have hlogc_nn : 0 ≤ Real.log (P.c : ℝ) := Real.log_nonneg hc1
  let u : ℕ → ℝ := fun j =>
    ((P.Q (j + 1) : ℝ) / (P.Q j : ℝ)) / ((P.c : ℝ) * (j : ℝ) ^ P.r) - 1
  have hu_bound : ∀ j : ℕ, J₂ ≤ j → |u j| ≤ 1 / 2 ∧
      |Real.log (1 + u j)| ≤ 2 * (((|(P.d : ℝ)| + 1) / (P.c : ℝ)) * (1 / (j : ℝ))) := by
    intro j hj
    have hj_J₀ : P.J₀ + 1 ≤ j := le_trans hJ₂_J₀ hj
    have hj_abs : 2 * P.d.natAbs + 3 ≤ j := le_trans hJ₂_abs hj
    have hj1 : 1 ≤ j := by omega
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hjr_ge_j : (j : ℝ) ≤ (j : ℝ) ^ P.r := by
      calc (j : ℝ) = (j : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (j : ℝ) ^ P.r := pow_le_pow_right₀ hj1R P.hr
    have hjr_pos : (0 : ℝ) < (j : ℝ) ^ P.r := pow_pos hjpos P.r
    have hcjr_pos : 0 < (P.c : ℝ) * (j : ℝ) ^ P.r := mul_pos hc_pos hjr_pos
    have hratio := P.poly_Q_ratio_bounds hj_J₀
    have hd_nat : (P.d.natAbs : ℝ) = |(P.d : ℝ)| :=
      (Int.cast_natCast P.d.natAbs).symm.trans
        ((congrArg (Int.cast : ℤ → ℝ) (Int.natCast_natAbs P.d)).trans Int.cast_abs)
    have hd1_le : |(P.d : ℝ)| + 1 ≤ (j : ℝ) / 2 := by
      have hj_r : 2 * (P.d.natAbs : ℝ) + 3 ≤ (j : ℝ) := by exact_mod_cast hj_abs
      linarith
    have hu_abs : |u j| ≤ (|(P.d : ℝ)| + 1) / ((P.c : ℝ) * (j : ℝ) ^ P.r) := by
      have hlo : (P.d : ℝ) / ((P.c : ℝ) * (j : ℝ) ^ P.r) < u j := by
        dsimp [u]
        rw [lt_sub_iff_add_lt, lt_div_iff₀ hcjr_pos]
        have h1 := hratio.1
        have heq : ((P.d : ℝ) / ((P.c : ℝ) * (j : ℝ) ^ P.r) + 1) * ((P.c : ℝ) * (j : ℝ) ^ P.r) =
            (P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ) := by field_simp; ring
        linarith
      have hhi : u j < ((P.d : ℝ) + 1) / ((P.c : ℝ) * (j : ℝ) ^ P.r) := by
        dsimp [u]
        rw [sub_lt_iff_lt_add, div_lt_iff₀ hcjr_pos]
        have h2 := hratio.2.1
        have heq : (((P.d : ℝ) + 1) / ((P.c : ℝ) * (j : ℝ) ^ P.r) + 1) * ((P.c : ℝ) * (j : ℝ) ^ P.r) =
            (P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ) + 1 := by field_simp; ring
        linarith
      have hneg : -(|(P.d : ℝ)| + 1) ≤ (P.d : ℝ) := by linarith [neg_abs_le (P.d : ℝ)]
      have hpos : (P.d : ℝ) + 1 ≤ |(P.d : ℝ)| + 1 := by linarith [le_abs_self (P.d : ℝ)]
      rw [abs_le]
      constructor
      · have : -( (|(P.d : ℝ)| + 1) / ((P.c : ℝ) * (j : ℝ) ^ P.r) ) =
            (-( |(P.d : ℝ)| + 1 )) / ((P.c : ℝ) * (j : ℝ) ^ P.r) := by ring
        rw [this]
        exact le_trans (div_le_div_of_nonneg_right hneg (le_of_lt hcjr_pos)) (le_of_lt hlo)
      · exact le_trans (le_of_lt hhi) (div_le_div_of_nonneg_right hpos (le_of_lt hcjr_pos))
    have hhalf : (|(P.d : ℝ)| + 1) / ((P.c : ℝ) * (j : ℝ) ^ P.r) ≤ 1 / 2 := by
      rw [div_le_iff₀ hcjr_pos]
      have hcj : (j : ℝ) ≤ (P.c : ℝ) * (j : ℝ) ^ P.r := by nlinarith
      linarith
    have hdiv_j : (|(P.d : ℝ)| + 1) / ((P.c : ℝ) * (j : ℝ) ^ P.r) ≤
        ((|(P.d : ℝ)| + 1) / (P.c : ℝ)) * (1 / (j : ℝ)) := by
      have h1 : (|(P.d : ℝ)| + 1) / ((P.c : ℝ) * (j : ℝ) ^ P.r) ≤
          (|(P.d : ℝ)| + 1) / ((P.c : ℝ) * (j : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hc_pos hjpos)
          (mul_le_mul_of_nonneg_left hjr_ge_j (le_of_lt hc_pos))
      have h2 : (|(P.d : ℝ)| + 1) / ((P.c : ℝ) * (j : ℝ)) =
          ((|(P.d : ℝ)| + 1) / (P.c : ℝ)) * (1 / (j : ℝ)) := by ring
      linarith
    have hu_half : |u j| ≤ 1 / 2 := le_trans hu_abs hhalf
    refine ⟨hu_half, le_trans (abs_log_one_add_le hu_half) ?_⟩
    exact mul_le_mul_of_nonneg_left (le_trans hu_abs hdiv_j) (by norm_num)
  have hstep_eq : ∀ j : ℕ, J₂ ≤ j →
      Real.log (P.Q (j + 1) : ℝ) - Real.log (P.Q j : ℝ) =
        Real.log (P.c : ℝ) + (P.r : ℝ) * Real.log (j : ℝ) + Real.log (1 + u j) := by
    intro j hj
    have hj_J₀ : P.J₀ + 1 ≤ j := le_trans hJ₂_J₀ hj
    have hj1 : 1 ≤ j := by omega
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hQj : (0 : ℝ) < (P.Q j : ℝ) := by exact_mod_cast P.hQ_pos j
    have hQj1 : (0 : ℝ) < (P.Q (j + 1) : ℝ) := by exact_mod_cast P.hQ_pos (j + 1)
    have h1u : 1 + u j = ((P.Q (j + 1) : ℝ) / (P.Q j : ℝ)) / ((P.c : ℝ) * (j : ℝ) ^ P.r) := by
      dsimp [u]; ring
    have hcjr_pos : 0 < (P.c : ℝ) * (j : ℝ) ^ P.r := by positivity
    rw [← Real.log_div hQj1.ne' hQj.ne', h1u, Real.log_div (div_pos hQj1 hQj).ne' hcjr_pos.ne',
      Real.log_mul hc_pos.ne' (pow_pos hjpos P.r).ne', Real.log_pow]
    ring
  set A_const : ℝ := 2 * ((|(P.d : ℝ)| + 1) / (P.c : ℝ))
  have hA_nn : 0 ≤ A_const := by positivity
  -- 对 n ≥ J₂ 估计误差界
  have htail_err : ∀ n : ℕ, J₂ ≤ n →
      |Real.log (P.Q n : ℝ) -
        ((P.r : ℝ) * (n : ℝ) * Real.log (n : ℝ) +
          (Real.log (P.c : ℝ) - (P.r : ℝ)) * (n : ℝ))| ≤
      (|Real.log (P.Q J₂ : ℝ)| + (J₂ : ℝ) * Real.log (P.c : ℝ) +
        (P.r : ℝ) * (∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ)) +
        (P.r : ℝ) + A_const) +
      (2 * (P.r : ℝ) + A_const) * Real.log (n : ℝ) := by
    intro n hn
    have hn2 : 2 ≤ n := by omega
    have htelQ : Real.log (P.Q n : ℝ) - Real.log (P.Q J₂ : ℝ) =
        ∑ j ∈ Finset.Ico J₂ n, (Real.log (P.Q (j + 1) : ℝ) - Real.log (P.Q j : ℝ)) := by
      symm
      exact Finset.sum_Ico_sub (fun j : ℕ => Real.log (P.Q j : ℝ)) hn
    have hsum_step : ∑ j ∈ Finset.Ico J₂ n, (Real.log (P.Q (j + 1) : ℝ) - Real.log (P.Q j : ℝ)) =
        ((n : ℝ) - (J₂ : ℝ)) * Real.log (P.c : ℝ) +
        (P.r : ℝ) * ∑ j ∈ Finset.Ico J₂ n, Real.log (j : ℝ) +
        ∑ j ∈ Finset.Ico J₂ n, Real.log (1 + u j) := by
      have hcongr : ∑ j ∈ Finset.Ico J₂ n, (Real.log (P.Q (j + 1) : ℝ) - Real.log (P.Q j : ℝ)) =
          ∑ j ∈ Finset.Ico J₂ n, (Real.log (P.c : ℝ) + (P.r : ℝ) * Real.log (j : ℝ) + Real.log (1 + u j)) :=
        Finset.sum_congr rfl fun j hj => hstep_eq j (Finset.mem_Ico.mp hj).1
      rw [hcongr, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
        nsmul_eq_mul, ← Finset.mul_sum]
      have hcast : ((n - J₂ : ℕ) : ℝ) = (n : ℝ) - (J₂ : ℝ) := Nat.cast_sub hn
      rw [hcast]
    have hlog_split : ∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ) =
        ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ) + ∑ j ∈ Finset.Ico J₂ n, Real.log (j : ℝ) := by
      have := Finset.sum_Ico_consecutive (fun j : ℕ => Real.log (j : ℝ)) (show 1 ≤ J₂ by omega) hn
      exact this.symm
    have hlog_asym := sum_log_asymptotic n hn2
    have hu_sum : |∑ j ∈ Finset.Ico J₂ n, Real.log (1 + u j)| ≤
        A_const * (1 + Real.log (n : ℝ)) := by
      have hIco_sub : Finset.Ico J₂ n ⊆ Finset.Ico 1 n := Finset.Ico_subset_Ico (by omega) le_rfl
      calc |∑ j ∈ Finset.Ico J₂ n, Real.log (1 + u j)|
          ≤ ∑ j ∈ Finset.Ico J₂ n, |Real.log (1 + u j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.Ico J₂ n, A_const * (1 / (j : ℝ)) := by
            apply Finset.sum_le_sum
            intro j hj
            have h1 := (hu_bound j (Finset.mem_Ico.mp hj).1).2
            simpa [A_const, mul_assoc] using h1
        _ = A_const * ∑ j ∈ Finset.Ico J₂ n, (1 : ℝ) / (j : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ A_const * ∑ j ∈ Finset.Ico 1 n, (1 : ℝ) / (j : ℝ) := by
            gcongr
        _ ≤ A_const * (1 + Real.log (n : ℝ)) := by
            gcongr
            exact sum_inv_le_one_add_log n (by omega)
    have hdiff_id : Real.log (P.Q n : ℝ) -
        ((P.r : ℝ) * (n : ℝ) * Real.log (n : ℝ) +
          (Real.log (P.c : ℝ) - (P.r : ℝ)) * (n : ℝ)) =
        Real.log (P.Q J₂ : ℝ) - (J₂ : ℝ) * Real.log (P.c : ℝ) -
          (P.r : ℝ) * ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ) +
          (P.r : ℝ) * (∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ) - ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ))) +
          ∑ j ∈ Finset.Ico J₂ n, Real.log (1 + u j) := by
      rw [hlog_split] at *
      have hQn_eq : Real.log (P.Q n : ℝ) =
          Real.log (P.Q J₂ : ℝ) + ((n : ℝ) - (J₂ : ℝ)) * Real.log (P.c : ℝ) +
          (P.r : ℝ) * ∑ j ∈ Finset.Ico J₂ n, Real.log (j : ℝ) +
          ∑ j ∈ Finset.Ico J₂ n, Real.log (1 + u j) := by
        linarith [htelQ, hsum_step]
      rw [hQn_eq]
      ring
    rw [hdiff_id]
    have hr_nn : (0 : ℝ) ≤ (P.r : ℝ) := Nat.cast_nonneg _
    have hsum1J_nn : 0 ≤ ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ) := by
      apply Finset.sum_nonneg
      intro j hj
      exact Real.log_nonneg (by exact_mod_cast (Finset.mem_Ico.mp hj).1)
    calc |Real.log (P.Q J₂ : ℝ) - (J₂ : ℝ) * Real.log (P.c : ℝ) -
            (P.r : ℝ) * ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ) +
            (P.r : ℝ) * (∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ) - ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ))) +
            ∑ j ∈ Finset.Ico J₂ n, Real.log (1 + u j)|
        ≤ |Real.log (P.Q J₂ : ℝ) - (J₂ : ℝ) * Real.log (P.c : ℝ) -
            (P.r : ℝ) * ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ)| +
          |(P.r : ℝ) * (∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ) - ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)))| +
          |∑ j ∈ Finset.Ico J₂ n, Real.log (1 + u j)| := by
            calc _ ≤ |Real.log (P.Q J₂ : ℝ) - (J₂ : ℝ) * Real.log (P.c : ℝ) -
                      (P.r : ℝ) * ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ) +
                      (P.r : ℝ) * (∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ) - ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)))| +
                    |∑ j ∈ Finset.Ico J₂ n, Real.log (1 + u j)| := abs_add_le _ _
              _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ ≤ (|Real.log (P.Q J₂ : ℝ)| + (J₂ : ℝ) * Real.log (P.c : ℝ) +
            (P.r : ℝ) * ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ)) +
          (P.r : ℝ) * (1 + 2 * Real.log (n : ℝ)) +
          A_const * (1 + Real.log (n : ℝ)) := by
            gcongr
            · calc |Real.log (P.Q J₂ : ℝ) - (J₂ : ℝ) * Real.log (P.c : ℝ) -
                      (P.r : ℝ) * ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ)|
                  ≤ |Real.log (P.Q J₂ : ℝ) - (J₂ : ℝ) * Real.log (P.c : ℝ)| +
                      |(P.r : ℝ) * ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ)| := abs_sub _ _
                _ ≤ (|Real.log (P.Q J₂ : ℝ)| + |(J₂ : ℝ) * Real.log (P.c : ℝ)|) +
                      |(P.r : ℝ) * ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ)| := by
                      gcongr; exact abs_sub _ _
                _ = |Real.log (P.Q J₂ : ℝ)| + (J₂ : ℝ) * Real.log (P.c : ℝ) +
                      (P.r : ℝ) * ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ) := by
                      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogc_nn),
                        abs_of_nonneg (mul_nonneg hr_nn hsum1J_nn)]
            · rw [abs_mul, abs_of_nonneg hr_nn]
              exact mul_le_mul_of_nonneg_left hlog_asym hr_nn
      _ = (|Real.log (P.Q J₂ : ℝ)| + (J₂ : ℝ) * Real.log (P.c : ℝ) +
            (P.r : ℝ) * ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ) +
            (P.r : ℝ) + A_const) +
          (2 * (P.r : ℝ) + A_const) * Real.log (n : ℝ) := by ring
  set C_tail0 : ℝ := |Real.log (P.Q J₂ : ℝ)| + (J₂ : ℝ) * Real.log (P.c : ℝ) +
    (P.r : ℝ) * ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ) + (P.r : ℝ) + A_const
  set C_tail1 : ℝ := 2 * (P.r : ℝ) + A_const
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let g : ℕ → ℝ := fun n =>
    |Real.log (P.Q n : ℝ) -
      ((P.r : ℝ) * (n : ℝ) * Real.log (n : ℝ) +
        (Real.log (P.c : ℝ) - (P.r : ℝ)) * (n : ℝ))| / Real.log (n : ℝ)
  set C_init : ℝ :=
    if hne : (Finset.Ico 2 J₂).Nonempty then (Finset.Ico 2 J₂).sup' hne g else 0
  set C : ℝ := max (C_tail0 / Real.log 2 + C_tail1) (max C_init 0)
  have hC_nn : 0 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, hC_nn, fun n hn => ?_⟩
  have hlogn_ge : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogn_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le hlog2_pos hlogn_ge
  by_cases hnJ : J₂ ≤ n
  · have h1 := htail_err n hnJ
    have hC_tail0_nn : 0 ≤ C_tail0 := by
      dsimp [C_tail0]
      have hsum_nn : 0 ≤ ∑ j ∈ Finset.Ico 1 J₂, Real.log (j : ℝ) :=
        Finset.sum_nonneg fun j hj => Real.log_nonneg (by exact_mod_cast (Finset.mem_Ico.mp hj).1)
      positivity
    have h2 : C_tail0 ≤ (C_tail0 / Real.log 2) * Real.log (n : ℝ) := by
      calc C_tail0 = (C_tail0 / Real.log 2) * Real.log 2 := by field_simp
        _ ≤ (C_tail0 / Real.log 2) * Real.log (n : ℝ) := by gcongr
    have h3 : C_tail0 + C_tail1 * Real.log (n : ℝ) ≤
        (C_tail0 / Real.log 2 + C_tail1) * Real.log (n : ℝ) := by linarith
    have h4 : C_tail0 / Real.log 2 + C_tail1 ≤ C := le_max_left _ _
    exact le_trans h1 (le_trans h3 (mul_le_mul_of_nonneg_right h4 (le_of_lt hlogn_pos)))
  · have hmem : n ∈ Finset.Ico 2 J₂ := Finset.mem_Ico.mpr ⟨hn, lt_of_not_ge hnJ⟩
    have hne : (Finset.Ico 2 J₂).Nonempty := ⟨n, hmem⟩
    have hle1 : g n ≤ C_init := by
      simp only [C_init, hne, ↓reduceDIte]
      exact Finset.le_sup' g hmem
    have hle2 : g n ≤ C := le_trans hle1 (le_trans (le_max_left _ _) (le_max_right _ _))
    exact (div_le_iff₀ hlogn_pos).mp hle2

/-- `lem:poly-growth`(iv) 推论：$\frac{\log Q_n}{n \log n} \to r$。 -/
theorem poly_log_Q_div_n_log_n_tendsto (P : PolyRecData) :
    Tendsto (fun n : ℕ => Real.log (P.Q n : ℝ) / ((n : ℝ) * Real.log (n : ℝ)))
      atTop (nhds (P.r : ℝ)) := by
  obtain ⟨C, _, hC⟩ := poly_log_Q_asymptotic P
  have h1_inv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop 1
  have hlog_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2_inv : Tendsto (fun n : ℕ => (Real.log (P.c : ℝ) - (P.r : ℝ)) / Real.log (n : ℝ))
      atTop (nhds 0) :=
    hlog_top.const_div_atTop _
  have hC_inv : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using h1_inv.const_mul C
  have hdiff0 : Tendsto (fun n : ℕ =>
      Real.log (P.Q n : ℝ) / ((n : ℝ) * Real.log (n : ℝ)) -
        ((P.r : ℝ) + (Real.log (P.c : ℝ) - (P.r : ℝ)) / Real.log (n : ℝ))) atTop (nhds 0) := by
    have hev : ∀ᶠ n : ℕ in atTop,
        |Real.log (P.Q n : ℝ) / ((n : ℝ) * Real.log (n : ℝ)) -
          ((P.r : ℝ) + (Real.log (P.c : ℝ) - (P.r : ℝ)) / Real.log (n : ℝ))| ≤ C / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
      have hden_pos : 0 < (n : ℝ) * Real.log (n : ℝ) := mul_pos hn_pos hlogn_pos
      have heq : Real.log (P.Q n : ℝ) / ((n : ℝ) * Real.log (n : ℝ)) -
          ((P.r : ℝ) + (Real.log (P.c : ℝ) - (P.r : ℝ)) / Real.log (n : ℝ)) =
          (Real.log (P.Q n : ℝ) - ((P.r : ℝ) * (n : ℝ) * Real.log (n : ℝ) +
            (Real.log (P.c : ℝ) - (P.r : ℝ)) * (n : ℝ))) / ((n : ℝ) * Real.log (n : ℝ)) := by
        field_simp
      rw [heq, abs_div, abs_of_pos hden_pos, div_le_iff₀ hden_pos]
      calc |Real.log (P.Q n : ℝ) - ((P.r : ℝ) * (n : ℝ) * Real.log (n : ℝ) +
              (Real.log (P.c : ℝ) - (P.r : ℝ)) * (n : ℝ))|
          ≤ C * Real.log (n : ℝ) := hC n hn
        _ = (C / (n : ℝ)) * ((n : ℝ) * Real.log (n : ℝ)) := by field_simp
    have hneg := hC_inv.neg
    rw [neg_zero] at hneg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hC_inv
      (hev.mono fun n hn => (abs_le.mp hn).1)
      (hev.mono fun n hn => (abs_le.mp hn).2)
  have hr_lim : Tendsto (fun n : ℕ =>
      (P.r : ℝ) + (Real.log (P.c : ℝ) - (P.r : ℝ)) / Real.log (n : ℝ)) atTop (nhds (P.r : ℝ)) := by
    simpa using tendsto_const_nhds.add h2_inv
  have hsum := hdiff0.add hr_lim
  simpa using hsum

/-! ## 第二部分：一般多项式递推显式分片线性规范函数与对数标度 (`rem:poly-gauge-scale`) -/

def polyInvQ (P : PolyRecData) (n : ℕ) : ℝ :=
  1 / (P.Q n : ℝ)

lemma polyInvQ_pos (P : PolyRecData) (n : ℕ) : 0 < polyInvQ P n := by
  unfold polyInvQ
  have hQ : (0 : ℝ) < (P.Q n : ℝ) := by exact_mod_cast P.hQ_pos n
  positivity

lemma polyInvQ_succ_lt (P : PolyRecData) {n : ℕ} (hn : P.J₀ ≤ n) :
    polyInvQ P (n + 1) < polyInvQ P n := by
  unfold polyInvQ
  have hQ : (0 : ℝ) < (P.Q n : ℝ) := by exact_mod_cast P.hQ_pos n
  have hlt : (P.Q n : ℝ) < (P.Q (n + 1) : ℝ) := by exact_mod_cast P.poly_Q_lt_succ hn
  exact one_div_lt_one_div_of_lt hQ hlt

lemma polyInvQ_antitoneOn (P : PolyRecData) :
    AntitoneOn (polyInvQ P) (Set.Ici P.J₀) := by
  intro m hm n hn hmn
  unfold polyInvQ
  have hQpos : (0 : ℝ) < (P.Q m : ℝ) := by exact_mod_cast P.hQ_pos m
  have hQle : (P.Q m : ℝ) ≤ (P.Q n : ℝ) := by
    exact_mod_cast P.poly_Q_strictMonoOn.monotoneOn hm hn hmn
  exact one_div_le_one_div_of_le hQpos hQle

lemma polyInvQ_le_J₀ (P : PolyRecData) {n : ℕ} (hn : P.J₀ ≤ n) :
    polyInvQ P n ≤ polyInvQ P P.J₀ :=
  polyInvQ_antitoneOn P (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hn) hn

lemma tendsto_polyInvQ (P : PolyRecData) : Tendsto (polyInvQ P) atTop (nhds 0) :=
  P.poly_Q_tendsto_atTop.const_div_atTop 1

/-- 第 $n$ 段 $[1/Q_{n+1}, 1/Q_n]$（$n \ge J_0$）上的线性插值函数。 -/
def polySegVal (P : PolyRecData) (b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  b ^ (-((n + 1 : ℕ) : ℤ)) +
    ((t - polyInvQ P (n + 1)) / (polyInvQ P n - polyInvQ P (n + 1))) *
      (b ^ (-(n : ℤ)) - b ^ (-((n + 1 : ℕ) : ℤ)))

lemma polySegVal_at_left (P : PolyRecData) (b : ℝ) (n : ℕ) :
    polySegVal P b n (polyInvQ P (n + 1)) = b ^ (-((n + 1 : ℕ) : ℤ)) := by
  simp [polySegVal]

lemma polySegVal_at_right (P : PolyRecData) (b : ℝ) {n : ℕ} (hn : P.J₀ ≤ n) :
    polySegVal P b n (polyInvQ P n) = b ^ (-(n : ℤ)) := by
  have hne : polyInvQ P n - polyInvQ P (n + 1) ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (polyInvQ_succ_lt P hn))
  simp [polySegVal, hne]

lemma polySegVal_continuous (P : PolyRecData) (b : ℝ) (n : ℕ) :
    Continuous (polySegVal P b n) := by
  unfold polySegVal
  fun_prop

lemma polySegVal_mono (P : PolyRecData) {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : P.J₀ ≤ n) :
    Monotone (polySegVal P b n) := by
  intro s t hst
  have hq : 0 < polyInvQ P n - polyInvQ P (n + 1) := sub_pos.mpr (polyInvQ_succ_lt P hn)
  have hpow : b ^ (-((n + 1 : ℕ) : ℤ)) ≤ b ^ (-(n : ℤ)) := by
    rw [zpow_le_zpow_iff_right₀ hb]
    omega
  have hdiff : 0 ≤ b ^ (-(n : ℤ)) - b ^ (-((n + 1 : ℕ) : ℤ)) := sub_nonneg.mpr hpow
  unfold polySegVal
  gcongr

lemma polySegVal_nonneg (P : PolyRecData) {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : P.J₀ ≤ n)
    {t : ℝ} (ht : polyInvQ P (n + 1) ≤ t) : 0 ≤ polySegVal P b n t := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have h1 : 0 ≤ b ^ (-((n + 1 : ℕ) : ℤ)) := zpow_nonneg (le_of_lt hb0) _
  have h2 := polySegVal_mono P hb hn ht
  rw [polySegVal_at_left] at h2
  exact le_trans h1 h2

lemma polySegVal_le_right (P : PolyRecData) {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : P.J₀ ≤ n)
    {t : ℝ} (ht : t ≤ polyInvQ P n) : polySegVal P b n t ≤ b ^ (-(n : ℤ)) := by
  have h := polySegVal_mono P hb hn ht
  rwa [polySegVal_at_right P b hn] at h

/-- 对 $0 < t < 1/Q_{J_0}$，找出满足 $1/Q_{n+1} \le t < 1/Q_n$ 的唯一指标 $n \ge J_0$。 -/
def polyInterpIdx (P : PolyRecData) (t : ℝ) : ℕ :=
  if h : 0 < t ∧ t < polyInvQ P P.J₀ then
    Nat.find (show ∃ n : ℕ, P.J₀ ≤ n ∧ polyInvQ P (n + 1) ≤ t by
      have hev := (tendsto_polyInvQ P).eventually (Iio_mem_nhds h.1)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
      refine ⟨max P.J₀ N, le_max_left _ _, ?_⟩
      have h1 : polyInvQ P (max P.J₀ N + 1) ≤ polyInvQ P (max P.J₀ N) :=
        le_of_lt (polyInvQ_succ_lt P (le_max_left _ _))
      have h2 : polyInvQ P (max P.J₀ N) < t := hN (max P.J₀ N) (le_max_right _ _)
      exact le_trans h1 (le_of_lt h2))
  else P.J₀

lemma polyInterpIdx_spec (P : PolyRecData) {t : ℝ} (ht0 : 0 < t) (ht1 : t < polyInvQ P P.J₀) :
    P.J₀ ≤ polyInterpIdx P t ∧
    polyInvQ P (polyInterpIdx P t + 1) ≤ t ∧
    t < polyInvQ P (polyInterpIdx P t) := by
  have h : 0 < t ∧ t < polyInvQ P P.J₀ := ⟨ht0, ht1⟩
  have hex : ∃ n : ℕ, P.J₀ ≤ n ∧ polyInvQ P (n + 1) ≤ t := by
    have hev := (tendsto_polyInvQ P).eventually (Iio_mem_nhds h.1)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max P.J₀ N, le_max_left _ _, ?_⟩
    have h1 : polyInvQ P (max P.J₀ N + 1) ≤ polyInvQ P (max P.J₀ N) :=
      le_of_lt (polyInvQ_succ_lt P (le_max_left _ _))
    have h2 : polyInvQ P (max P.J₀ N) < t := hN (max P.J₀ N) (le_max_right _ _)
    exact le_trans h1 (le_of_lt h2)
  have hdef : polyInterpIdx P t = Nat.find hex := by simp [polyInterpIdx, h]
  have hspec := Nat.find_spec hex
  rw [← hdef] at hspec
  refine ⟨hspec.1, hspec.2, ?_⟩
  by_cases hnJ : polyInterpIdx P t = P.J₀
  · rw [hnJ]; exact ht1
  · have hm1 : P.J₀ ≤ polyInterpIdx P t - 1 := by omega
    have hlt : polyInterpIdx P t - 1 < polyInterpIdx P t := by omega
    have hmin := Nat.find_min hex (by rw [← hdef]; exact hlt)
    push Not at hmin
    have hadd : polyInterpIdx P t - 1 + 1 = polyInterpIdx P t := by omega
    rw [hadd] at hmin
    exact hmin hm1

lemma polyInterpIdx_eq_of_mem_Ico (P : PolyRecData) {t : ℝ} {n : ℕ} (hn : P.J₀ ≤ n)
    (hlo : polyInvQ P (n + 1) ≤ t) (hhi : t < polyInvQ P n) :
    polyInterpIdx P t = n := by
  have ht0 : 0 < t := lt_of_lt_of_le (polyInvQ_pos P (n + 1)) hlo
  have ht1 : t < polyInvQ P P.J₀ := lt_of_lt_of_le hhi (polyInvQ_le_J₀ P hn)
  obtain ⟨hm1, hmlo, hmhi⟩ := polyInterpIdx_spec P ht0 ht1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : polyInterpIdx P t + 1 ≤ n := by omega
    have hq : polyInvQ P n ≤ polyInvQ P (polyInterpIdx P t + 1) :=
      polyInvQ_antitoneOn P (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hn) hle
    linarith
  · have hle : n + 1 ≤ polyInterpIdx P t := by omega
    have hq : polyInvQ P (polyInterpIdx P t) ≤ polyInvQ P (n + 1) :=
      polyInvQ_antitoneOn P (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hm1) hle
    linarith

lemma polyInterpIdx_antitone (P : PolyRecData) {s t : ℝ} (hs0 : 0 < s)
    (ht1 : t < polyInvQ P P.J₀) (hst : s ≤ t) :
    polyInterpIdx P t ≤ polyInterpIdx P s := by
  have hs1 : s < polyInvQ P P.J₀ := lt_of_le_of_lt hst ht1
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  obtain ⟨_, hnlo, _⟩ := polyInterpIdx_spec P hs0 hs1
  obtain ⟨hm1, _, hmhi⟩ := polyInterpIdx_spec P ht0 ht1
  by_contra hlt
  push Not at hlt
  have hle : polyInterpIdx P s + 1 ≤ polyInterpIdx P t := by omega
  have hq : polyInvQ P (polyInterpIdx P t) ≤ polyInvQ P (polyInterpIdx P s + 1) :=
    polyInvQ_antitoneOn P (Set.mem_Ici.mpr (by have := (polyInterpIdx_spec P hs0 hs1).1; omega))
      (Set.mem_Ici.mpr hm1) hle
  linarith

/-- 实轴上一般递推的分片线性规范函数（$t \le 0$ 取 $0$，$t \ge 1/Q_{J_0}$ 取 $b^{-J_0}$）。 -/
def polyInterpGaugeReal (P : PolyRecData) (b : ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0
  else if polyInvQ P P.J₀ ≤ t then b ^ (-(P.J₀ : ℤ))
  else polySegVal P b (polyInterpIdx P t) t

lemma polyInterpGaugeReal_le_zero (P : PolyRecData) (b : ℝ) {t : ℝ} (ht : t ≤ 0) :
    polyInterpGaugeReal P b t = 0 := by
  simp [polyInterpGaugeReal, ht]

lemma polyInterpGaugeReal_zero (P : PolyRecData) (b : ℝ) :
    polyInterpGaugeReal P b 0 = 0 :=
  polyInterpGaugeReal_le_zero P b (le_refl 0)

lemma polyInterpGaugeReal_ge_J₀ (P : PolyRecData) (b : ℝ) {t : ℝ} (ht : polyInvQ P P.J₀ ≤ t) :
    polyInterpGaugeReal P b t = b ^ (-(P.J₀ : ℤ)) := by
  have hnot : ¬ t ≤ 0 := not_le.mpr (lt_of_lt_of_le (polyInvQ_pos P P.J₀) ht)
  simp [polyInterpGaugeReal, hnot, ht]

lemma polyInterpGaugeReal_eq_segVal (P : PolyRecData) {b : ℝ} (_hb : 1 < b)
    {n : ℕ} (hn : P.J₀ ≤ n) {t : ℝ} (hlo : polyInvQ P (n + 1) ≤ t) (hhi : t ≤ polyInvQ P n) :
    polyInterpGaugeReal P b t = polySegVal P b n t := by
  have ht0 : 0 < t := lt_of_lt_of_le (polyInvQ_pos P (n + 1)) hlo
  have hnot0 : ¬ t ≤ 0 := not_le.mpr ht0
  rcases eq_or_lt_of_le hhi with rfl | ht_lt
  · rw [polySegVal_at_right P b hn]
    by_cases hnJ : n = P.J₀
    · subst hnJ
      exact polyInterpGaugeReal_ge_J₀ P b (le_refl _)
    · have hn' : P.J₀ ≤ n - 1 := by omega
      have hadd : n - 1 + 1 = n := by omega
      have hlo' : polyInvQ P (n - 1 + 1) ≤ polyInvQ P n := by rw [hadd]
      have hhi' : polyInvQ P n < polyInvQ P (n - 1) := by
        simpa [hadd] using polyInvQ_succ_lt P hn'
      have ht1 : ¬ polyInvQ P P.J₀ ≤ polyInvQ P n := by
        have := lt_of_lt_of_le hhi' (polyInvQ_le_J₀ P hn')
        linarith
      simp only [polyInterpGaugeReal, hnot0, ↓reduceIte, ht1]
      rw [polyInterpIdx_eq_of_mem_Ico P hn' hlo' hhi']
      conv_lhs => rhs; rw [← hadd]
      rw [polySegVal_at_left, hadd]
  · have ht1 : ¬ polyInvQ P P.J₀ ≤ t := by
      have := lt_of_lt_of_le ht_lt (polyInvQ_le_J₀ P hn)
      linarith
    simp only [polyInterpGaugeReal, hnot0, ↓reduceIte, ht1]
    rw [polyInterpIdx_eq_of_mem_Ico P hn hlo ht_lt]

lemma polyInterpGaugeReal_at_invQ (P : PolyRecData) {b : ℝ} (hb : 1 < b)
    {n : ℕ} (hn : P.J₀ ≤ n) :
    polyInterpGaugeReal P b (polyInvQ P n) = b ^ (-(n : ℤ)) := by
  rw [polyInterpGaugeReal_eq_segVal P hb hn (le_of_lt (polyInvQ_succ_lt P hn)) (le_refl _),
    polySegVal_at_right P b hn]

lemma polyInterpGaugeReal_nonneg (P : PolyRecData) {b : ℝ} (hb : 1 < b) (t : ℝ) :
    0 ≤ polyInterpGaugeReal P b t := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  by_cases ht0 : t ≤ 0
  · rw [polyInterpGaugeReal_le_zero P b ht0]
  · by_cases ht1 : polyInvQ P P.J₀ ≤ t
    · rw [polyInterpGaugeReal_ge_J₀ P b ht1]; positivity
    · have ht0' : 0 < t := lt_of_not_ge ht0
      have ht1' : t < polyInvQ P P.J₀ := lt_of_not_ge ht1
      obtain ⟨hn1, hnlo, _⟩ := polyInterpIdx_spec P ht0' ht1'
      simp only [polyInterpGaugeReal, ht0, ↓reduceIte, ht1]
      exact polySegVal_nonneg P hb hn1 hnlo

lemma polyInterpGaugeReal_mono (P : PolyRecData) {b : ℝ} (hb : 1 < b) :
    Monotone (polyInterpGaugeReal P b) := by
  intro s t hst
  by_cases hs0 : s ≤ 0
  · rw [polyInterpGaugeReal_le_zero P b hs0]
    exact polyInterpGaugeReal_nonneg P hb t
  · have hs0' : 0 < s := lt_of_not_ge hs0
    have ht0' : 0 < t := lt_of_lt_of_le hs0' hst
    have ht0 : ¬ t ≤ 0 := not_le.mpr ht0'
    by_cases ht1 : polyInvQ P P.J₀ ≤ t
    · rw [polyInterpGaugeReal_ge_J₀ P b ht1]
      by_cases hs1 : polyInvQ P P.J₀ ≤ s
      · rw [polyInterpGaugeReal_ge_J₀ P b hs1]
      · have hs1' : s < polyInvQ P P.J₀ := lt_of_not_ge hs1
        obtain ⟨hn1, _, hnhi⟩ := polyInterpIdx_spec P hs0' hs1'
        simp only [polyInterpGaugeReal, hs0, ↓reduceIte, hs1]
        have h1 := polySegVal_le_right P hb hn1 (le_of_lt hnhi)
        have h2 : b ^ (-(polyInterpIdx P s : ℤ)) ≤ b ^ (-(P.J₀ : ℤ)) := by
          rw [zpow_le_zpow_iff_right₀ hb]
          omega
        exact le_trans h1 h2
    · have ht1' : t < polyInvQ P P.J₀ := lt_of_not_ge ht1
      have hs1' : s < polyInvQ P P.J₀ := lt_of_le_of_lt hst ht1'
      have hs1 : ¬ polyInvQ P P.J₀ ≤ s := not_le.mpr hs1'
      obtain ⟨hn1, hnlo, hnhi⟩ := polyInterpIdx_spec P hs0' hs1'
      obtain ⟨hm1, hmlo, hmhi⟩ := polyInterpIdx_spec P ht0' ht1'
      have hidx : polyInterpIdx P t ≤ polyInterpIdx P s :=
        polyInterpIdx_antitone P hs0' ht1' hst
      simp only [polyInterpGaugeReal, hs0, ht0, ↓reduceIte, hs1, ht1]
      rcases eq_or_lt_of_le hidx with heq | hlt
      · rw [heq]
        exact polySegVal_mono P hb hn1 hst
      · have h1 := polySegVal_le_right P hb hn1 (le_of_lt hnhi)
        have h2 := polySegVal_mono P hb hm1 hmlo
        rw [polySegVal_at_left] at h2
        have hpow : b ^ (-(polyInterpIdx P s : ℤ)) ≤ b ^ (-((polyInterpIdx P t + 1 : ℕ) : ℤ)) := by
          rw [zpow_le_zpow_iff_right₀ hb]
          omega
        exact le_trans h1 (le_trans hpow h2)

lemma polyInterpGaugeReal_continuous (P : PolyRecData) {b : ℝ} (hb : 1 < b) :
    Continuous (polyInterpGaugeReal P b) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with ht_neg | rfl | ht_pos
  · have hev : ∀ᶠ y in nhds t, (0 : ℝ) = polyInterpGaugeReal P b y := by
      filter_upwards [Iio_mem_nhds ht_neg] with y hy
      exact (polyInterpGaugeReal_le_zero P b (le_of_lt hy)).symm
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t).congr hev
  · rw [Metric.continuousAt_iff]
    intro ε hε
    have hb_inv : 0 ≤ b⁻¹ := by positivity
    have hb_lt1 : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
    have hpow0 : Tendsto (fun n : ℕ => b⁻¹ ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hb_inv hb_lt1
    obtain ⟨N, hN⟩ := (hpow0.eventually (Iio_mem_nhds hε)).exists
    set n := max P.J₀ N
    have hn1 : P.J₀ ≤ n := le_max_left _ _
    have hNle : N ≤ n := le_max_right _ _
    have hbn : b ^ (-(n : ℤ)) < ε := by
      have h1 : b ^ (-(n : ℤ)) = b⁻¹ ^ n := by rw [zpow_neg, zpow_natCast, inv_pow]
      have h2 : b⁻¹ ^ n ≤ b⁻¹ ^ N := pow_le_pow_of_le_one hb_inv (le_of_lt hb_lt1) hNle
      linarith
    refine ⟨polyInvQ P n, polyInvQ_pos P n, fun {y} hy => ?_⟩
    rw [polyInterpGaugeReal_zero, Real.dist_eq, sub_zero,
      abs_of_nonneg (polyInterpGaugeReal_nonneg P hb y)]
    have hy_lt : y < polyInvQ P n := by
      rw [Real.dist_eq, sub_zero] at hy
      exact (abs_lt.mp hy).2
    calc polyInterpGaugeReal P b y
        ≤ polyInterpGaugeReal P b (polyInvQ P n) := polyInterpGaugeReal_mono P hb (le_of_lt hy_lt)
      _ = b ^ (-(n : ℤ)) := polyInterpGaugeReal_at_invQ P hb hn1
      _ < ε := hbn
  · rcases lt_trichotomy t (polyInvQ P P.J₀) with ht_lt1 | ht_eq | ht_gt1
    · set n := polyInterpIdx P t
      obtain ⟨hn1, hnlo, hnhi⟩ := polyInterpIdx_spec P ht_pos ht_lt1
      rcases eq_or_lt_of_le hnlo with h_eq | h_gt
      · have hleft : ContinuousWithinAt (polyInterpGaugeReal P b) (Iic t) t := by
          have hmem : Ioc (polyInvQ P (n + 2)) t ∈ nhdsWithin t (Iic t) := by
            rw [← Ioi_inter_Iic]
            exact Filter.inter_mem
              (nhdsWithin_le_nhds (Ioi_mem_nhds
                (by rw [← h_eq]; exact polyInvQ_succ_lt P (by omega))))
              self_mem_nhdsWithin
          have heq : ∀ᶠ y in nhdsWithin t (Iic t),
              polyInterpGaugeReal P b y = polySegVal P b (n + 1) y := by
            filter_upwards [hmem] with y hy
            exact polyInterpGaugeReal_eq_segVal P hb (by omega) (le_of_lt hy.1)
              (by rw [h_eq]; exact hy.2)
          have hfx : polyInterpGaugeReal P b t = polySegVal P b (n + 1) t :=
            polyInterpGaugeReal_eq_segVal P hb (by omega)
              (le_of_lt (by rw [← h_eq]; exact polyInvQ_succ_lt P (by omega))) (by rw [h_eq])
          exact (polySegVal_continuous P b (n + 1)).continuousWithinAt.congr_of_eventuallyEq heq hfx
        have hright : ContinuousWithinAt (polyInterpGaugeReal P b) (Ici t) t := by
          have hmem : Ico t (polyInvQ P n) ∈ nhdsWithin t (Ici t) := by
            rw [← Ici_inter_Iio]
            exact Filter.inter_mem self_mem_nhdsWithin
              (nhdsWithin_le_nhds (Iio_mem_nhds hnhi))
          have heq : ∀ᶠ y in nhdsWithin t (Ici t),
              polyInterpGaugeReal P b y = polySegVal P b n y := by
            filter_upwards [hmem] with y hy
            exact polyInterpGaugeReal_eq_segVal P hb hn1 (by rw [h_eq]; exact hy.1) (le_of_lt hy.2)
          have hfx : polyInterpGaugeReal P b t = polySegVal P b n t :=
            polyInterpGaugeReal_eq_segVal P hb hn1 hnlo (le_of_lt hnhi)
          exact (polySegVal_continuous P b n).continuousWithinAt.congr_of_eventuallyEq heq hfx
        have hunion := hleft.union hright
        rwa [Iic_union_Ici, continuousWithinAt_univ] at hunion
      · have hev : ∀ᶠ y in nhds t, polySegVal P b n y = polyInterpGaugeReal P b y := by
          filter_upwards [Ioo_mem_nhds h_gt hnhi] with y hy
          exact (polyInterpGaugeReal_eq_segVal P hb hn1 (le_of_lt hy.1) (le_of_lt hy.2)).symm
        exact (polySegVal_continuous P b n).continuousAt.congr hev
    · rw [ht_eq]
      have hleft : ContinuousWithinAt (polyInterpGaugeReal P b) (Iic (polyInvQ P P.J₀))
          (polyInvQ P P.J₀) := by
        have hmem : Ioc (polyInvQ P (P.J₀ + 1)) (polyInvQ P P.J₀) ∈
            nhdsWithin (polyInvQ P P.J₀) (Iic (polyInvQ P P.J₀)) := by
          rw [← Ioi_inter_Iic]
          exact Filter.inter_mem
            (nhdsWithin_le_nhds (Ioi_mem_nhds (polyInvQ_succ_lt P le_rfl)))
            self_mem_nhdsWithin
        have heq : ∀ᶠ y in nhdsWithin (polyInvQ P P.J₀) (Iic (polyInvQ P P.J₀)),
            polyInterpGaugeReal P b y = polySegVal P b P.J₀ y := by
          filter_upwards [hmem] with y hy
          exact polyInterpGaugeReal_eq_segVal P hb le_rfl (le_of_lt hy.1) hy.2
        have hfx : polyInterpGaugeReal P b (polyInvQ P P.J₀) =
            polySegVal P b P.J₀ (polyInvQ P P.J₀) :=
          polyInterpGaugeReal_eq_segVal P hb le_rfl
            (le_of_lt (polyInvQ_succ_lt P le_rfl)) (le_refl _)
        exact (polySegVal_continuous P b P.J₀).continuousWithinAt.congr_of_eventuallyEq heq hfx
      have hright : ContinuousWithinAt (polyInterpGaugeReal P b) (Ici (polyInvQ P P.J₀))
          (polyInvQ P P.J₀) := by
        have heq : ∀ᶠ y in nhdsWithin (polyInvQ P P.J₀) (Ici (polyInvQ P P.J₀)),
            polyInterpGaugeReal P b y = b ^ (-(P.J₀ : ℤ)) := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          exact polyInterpGaugeReal_ge_J₀ P b hy
        exact continuousWithinAt_const.congr_of_eventuallyEq heq
          (polyInterpGaugeReal_ge_J₀ P b (le_refl _))
      have hunion := hleft.union hright
      rwa [Iic_union_Ici, continuousWithinAt_univ] at hunion
    · have hev : ∀ᶠ y in nhds t, b ^ (-(P.J₀ : ℤ)) = polyInterpGaugeReal P b y := by
        filter_upwards [Ioi_mem_nhds ht_gt1] with y hy
        exact (polyInterpGaugeReal_ge_J₀ P b (le_of_lt hy)).symm
      exact (continuousAt_const : ContinuousAt (fun _ : ℝ => b ^ (-(P.J₀ : ℤ))) t).congr hev

/-- `ℝ≥0∞` 上的一般递推分片线性规范函数 $g_b^{(r,c,d)}$（$1 < b$）。 -/
def polyInterpGauge (P : PolyRecData) (b : ℝ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  if ENNReal.ofReal (polyInvQ P P.J₀) ≤ x then ENNReal.ofReal (b ^ (-(P.J₀ : ℤ)))
  else ENNReal.ofReal (polyInterpGaugeReal P b x.toReal)

lemma polyInterpGauge_eq_ofReal_toReal (P : PolyRecData) {b : ℝ} (_hb : 1 < b)
    {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    polyInterpGauge P b x = ENNReal.ofReal (polyInterpGaugeReal P b x.toReal) := by
  by_cases hx1 : ENNReal.ofReal (polyInvQ P P.J₀) ≤ x
  · have hx1R : polyInvQ P P.J₀ ≤ x.toReal := by
      have h1 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hx).mpr hx1
      rwa [ENNReal.toReal_ofReal (le_of_lt (polyInvQ_pos P P.J₀))] at h1
    simp [polyInterpGauge, hx1, polyInterpGaugeReal_ge_J₀ P b hx1R]
  · simp [polyInterpGauge, hx1]

lemma polyInterpGauge_zero (P : PolyRecData) (b : ℝ) : polyInterpGauge P b 0 = 0 := by
  have h0 : ¬ ENNReal.ofReal (polyInvQ P P.J₀) ≤ 0 := by
    rw [not_le]
    exact ENNReal.ofReal_pos.mpr (polyInvQ_pos P P.J₀)
  simp [polyInterpGauge, h0, polyInterpGaugeReal_zero]

lemma polyInterpGauge_at_inv_Q (P : PolyRecData) {b : ℝ} (hb : 1 < b)
    {n : ℕ} (hn : P.J₀ ≤ n) :
    polyInterpGauge P b (ENNReal.ofReal (1 / (P.Q n : ℝ))) = ENNReal.ofReal (b ^ (-(n : ℤ))) := by
  rw [polyInterpGauge_eq_ofReal_toReal P hb ENNReal.ofReal_ne_top]
  have hpos : 0 ≤ 1 / (P.Q n : ℝ) := le_of_lt (polyInvQ_pos P n)
  rw [ENNReal.toReal_ofReal hpos]
  change ENNReal.ofReal (polyInterpGaugeReal P b (polyInvQ P n)) = _
  rw [polyInterpGaugeReal_at_invQ P hb hn]

lemma polyInterpGauge_mono (P : PolyRecData) {b : ℝ} (hb : 1 < b) :
    Monotone (polyInterpGauge P b) := by
  intro x y hxy
  by_cases hy1 : ENNReal.ofReal (polyInvQ P P.J₀) ≤ y
  · by_cases hx1 : ENNReal.ofReal (polyInvQ P P.J₀) ≤ x
    · simp [polyInterpGauge, hx1, hy1]
    · have hx_lt : x < ENNReal.ofReal (polyInvQ P P.J₀) := lt_of_not_ge hx1
      have hx_ne : x ≠ ⊤ := ne_of_lt (lt_trans hx_lt ENNReal.ofReal_lt_top)
      have hx1R : x.toReal ≤ polyInvQ P P.J₀ := by
        have h1 := (ENNReal.toReal_le_toReal hx_ne ENNReal.ofReal_ne_top).mpr hx_lt.le
        rwa [ENNReal.toReal_ofReal (le_of_lt (polyInvQ_pos P P.J₀))] at h1
      simp only [polyInterpGauge, hx1, ↓reduceIte, hy1]
      apply ENNReal.ofReal_le_ofReal
      calc polyInterpGaugeReal P b x.toReal
          ≤ polyInterpGaugeReal P b (polyInvQ P P.J₀) := polyInterpGaugeReal_mono P hb hx1R
        _ = b ^ (-(P.J₀ : ℤ)) := polyInterpGaugeReal_ge_J₀ P b le_rfl
  · have hx1 : ¬ ENNReal.ofReal (polyInvQ P P.J₀) ≤ x := fun h => hy1 (le_trans h hxy)
    have hy_ne : y ≠ ⊤ := ne_of_lt (lt_trans (lt_of_not_ge hy1) ENNReal.ofReal_lt_top)
    rw [polyInterpGauge_eq_ofReal_toReal P hb (ne_top_of_le_ne_top hy_ne hxy),
      polyInterpGauge_eq_ofReal_toReal P hb hy_ne]
    exact ENNReal.ofReal_le_ofReal
      (polyInterpGaugeReal_mono P hb ((ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hy_ne hxy) hy_ne).mpr hxy))

lemma polyInterpGauge_continuous (P : PolyRecData) {b : ℝ} (hb : 1 < b) :
    Continuous (polyInterpGauge P b) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx1 : ENNReal.ofReal (polyInvQ P P.J₀) < x
  · have hev : ∀ᶠ y in nhds x, ENNReal.ofReal (b ^ (-(P.J₀ : ℤ))) = polyInterpGauge P b y := by
      filter_upwards [Ioi_mem_nhds hx1] with y hy
      have hy1 : ENNReal.ofReal (polyInvQ P P.J₀) ≤ y := le_of_lt hy
      simp [polyInterpGauge, hy1]
    exact (continuousAt_const :
      ContinuousAt (fun _ : ℝ≥0∞ => ENNReal.ofReal (b ^ (-(P.J₀ : ℤ)))) x).congr hev
  · have hx_le : x ≤ ENNReal.ofReal (polyInvQ P P.J₀) := le_of_not_gt hx1
    have hx_lt_top : x < ⊤ := lt_of_le_of_lt hx_le ENNReal.ofReal_lt_top
    have hx_ne : x ≠ ⊤ := ne_of_lt hx_lt_top
    have hev : ∀ᶠ y in nhds x, ENNReal.ofReal (polyInterpGaugeReal P b y.toReal) =
        polyInterpGauge P b y := by
      filter_upwards [Iio_mem_nhds hx_lt_top] with y hy
      exact (polyInterpGauge_eq_ofReal_toReal P hb (ne_of_lt hy)).symm
    have hcomp : ContinuousAt (fun y : ℝ≥0∞ => ENNReal.ofReal (polyInterpGaugeReal P b y.toReal)) x :=
      ENNReal.continuous_ofReal.continuousAt.comp
        ((polyInterpGaugeReal_continuous P hb).continuousAt.comp (ENNReal.continuousAt_toReal hx_ne))
    exact hcomp.congr hev

lemma polyInterpGauge_ratio_tendsto_zero (P : PolyRecData) {b₁ b₂ : ℝ}
    (hb₁ : 1 < b₁) (hb₂ : b₁ < b₂) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → polyInterpGauge P b₂ r ≤ (ε : ℝ≥0∞) * polyInterpGauge P b₁ r := by
  intro ε hε
  have hb₁_pos : 0 < b₁ := lt_trans zero_lt_one hb₁
  have hb₂_pos : 0 < b₂ := lt_trans hb₁_pos hb₂
  have hb₂_gt1 : 1 < b₂ := lt_trans hb₁ hb₂
  have hratio_nn : 0 ≤ b₁ / b₂ := div_nonneg (le_of_lt hb₁_pos) (le_of_lt hb₂_pos)
  have hratio_lt : b₁ / b₂ < 1 := (div_lt_one hb₂_pos).mpr hb₂
  have hpow0 : Tendsto (fun n : ℕ => b₁ * (b₁ / b₂) ^ n) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nn hratio_lt).const_mul b₁
  have hεR : (0 : ℝ) < (ε : ℝ) := hε
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hpow0.eventually (Iio_mem_nhds hεR))
  set N := max P.J₀ N0
  have hNJ₀ : P.J₀ ≤ N := le_max_left _ _
  have hN_bound : b₁ * (b₁ / b₂) ^ N ≤ (ε : ℝ) := le_of_lt (hN0 N (le_max_right _ _))
  refine ⟨ENNReal.ofReal (polyInvQ P (N + 1)), ENNReal.ofReal_pos.mpr (polyInvQ_pos P (N + 1)), ?_⟩
  intro r hr
  by_cases hr0 : r = 0
  · subst hr0
    simp [polyInterpGauge_zero]
  · have hr_lt_top : r < ⊤ := lt_of_le_of_lt hr ENNReal.ofReal_lt_top
    have hr_ne_top : r ≠ ⊤ := ne_of_lt hr_lt_top
    have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos hr0 hr_ne_top
    have hr_real_le : r.toReal ≤ polyInvQ P (N + 1) := by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
      rwa [ENNReal.toReal_ofReal (le_of_lt (polyInvQ_pos P (N + 1)))] at h1
    have hr_lt_invQN : r.toReal < polyInvQ P N :=
      lt_of_le_of_lt hr_real_le (polyInvQ_succ_lt P hNJ₀)
    have hr_lt_J₀ : r.toReal < polyInvQ P P.J₀ :=
      lt_of_lt_of_le hr_lt_invQN (polyInvQ_le_J₀ P hNJ₀)
    set n := polyInterpIdx P r.toReal
    obtain ⟨hn1, hnlo, hnhi⟩ := polyInterpIdx_spec P hr_real_pos hr_lt_J₀
    have hN_le_n : N ≤ n := by
      by_contra hlt
      push Not at hlt
      have hle : n + 1 ≤ N := by omega
      have hq : polyInvQ P N ≤ polyInvQ P (n + 1) :=
        polyInvQ_antitoneOn P (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hNJ₀) hle
      linarith
    have hb₂_le : polyInterpGaugeReal P b₂ r.toReal ≤ b₂ ^ (-(n : ℤ)) := by
      calc polyInterpGaugeReal P b₂ r.toReal
          ≤ polyInterpGaugeReal P b₂ (polyInvQ P n) := polyInterpGaugeReal_mono P hb₂_gt1 (le_of_lt hnhi)
        _ = b₂ ^ (-(n : ℤ)) := polyInterpGaugeReal_at_invQ P hb₂_gt1 hn1
    have hb₁_ge : b₁ ^ (-((n + 1 : ℕ) : ℤ)) ≤ polyInterpGaugeReal P b₁ r.toReal := by
      calc b₁ ^ (-((n + 1 : ℕ) : ℤ))
          = polyInterpGaugeReal P b₁ (polyInvQ P (n + 1)) :=
            (polyInterpGaugeReal_at_invQ P hb₁ (by omega)).symm
        _ ≤ polyInterpGaugeReal P b₁ r.toReal := polyInterpGaugeReal_mono P hb₁ hnlo
    have hpow_mono : b₁ * (b₁ / b₂) ^ n ≤ b₁ * (b₁ / b₂) ^ N :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hratio_nn (le_of_lt hratio_lt) hN_le_n)
        (le_of_lt hb₁_pos)
    have halg : b₂ ^ (-(n : ℤ)) = (b₁ * (b₁ / b₂) ^ n) * b₁ ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ, div_pow]
      have hb1n : b₁ ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hb₁_pos)
      have hb2n : b₂ ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hb₂_pos)
      have hb10 : b₁ ≠ 0 := ne_of_gt hb₁_pos
      field_simp
    have hreal : polyInterpGaugeReal P b₂ r.toReal ≤ (ε : ℝ) * polyInterpGaugeReal P b₁ r.toReal := by
      calc polyInterpGaugeReal P b₂ r.toReal
          ≤ b₂ ^ (-(n : ℤ)) := hb₂_le
        _ = (b₁ * (b₁ / b₂) ^ n) * b₁ ^ (-((n + 1 : ℕ) : ℤ)) := halg
        _ ≤ (b₁ * (b₁ / b₂) ^ N) * polyInterpGaugeReal P b₁ r.toReal :=
            mul_le_mul hpow_mono hb₁_ge (zpow_nonneg (le_of_lt hb₁_pos) _) (by positivity)
        _ ≤ (ε : ℝ) * polyInterpGaugeReal P b₁ r.toReal := by
            gcongr
            exact polyInterpGaugeReal_nonneg P hb₁ r.toReal
    rw [polyInterpGauge_eq_ofReal_toReal P hb₂_gt1 hr_ne_top,
      polyInterpGauge_eq_ofReal_toReal P hb₁ hr_ne_top]
    have hεE : (ε : ℝ≥0∞) = ENNReal.ofReal (ε : ℝ) := by simp
    rw [hεE, ← ENNReal.ofReal_mul (by exact hε.le)]
    exact ENNReal.ofReal_le_ofReal hreal

/-- 一般递推临界能级 $k/c$ 的分片线性临界规范 $h_k^{(r,c,d)}$（底数 $2k+1$）。 -/
def polyCritGauge (P : PolyRecData) (k : ℕ) : ℝ≥0∞ → ℝ≥0∞ :=
  polyInterpGauge P (2 * (k : ℝ) + 1)

/-- 一般递推无符号精确极限集 $E_{\mathrm{lim}}^{(r,c,d)}(k/c)$ 的普适二进规范 $g_2^{(r,c,d)}$（底数 $2$）。 -/
def polyBinaryGauge (P : PolyRecData) : ℝ≥0∞ → ℝ≥0∞ :=
  polyInterpGauge P 2

lemma polyCritGauge_zero (P : PolyRecData) (k : ℕ) : polyCritGauge P k 0 = 0 :=
  polyInterpGauge_zero P _

lemma polyCritGauge_mono (P : PolyRecData) (k : ℕ) (hk : 1 ≤ k) :
    Monotone (polyCritGauge P k) :=
  polyInterpGauge_mono P (GaugeCircle.critGauge_base_gt_one k hk)

lemma polyCritGauge_continuous (P : PolyRecData) (k : ℕ) (hk : 1 ≤ k) :
    Continuous (polyCritGauge P k) :=
  polyInterpGauge_continuous P (GaugeCircle.critGauge_base_gt_one k hk)

lemma polyCritGauge_at_inv_Q (P : PolyRecData) (k : ℕ) (hk : 1 ≤ k)
    {n : ℕ} (hn : P.J₀ ≤ n) :
    polyCritGauge P k (ENNReal.ofReal (1 / (P.Q n : ℝ))) =
      ENNReal.ofReal ((2 * (k : ℝ) + 1) ^ (-(n : ℤ))) :=
  polyInterpGauge_at_inv_Q P (GaugeCircle.critGauge_base_gt_one k hk) hn

lemma polyBinaryGauge_zero (P : PolyRecData) : polyBinaryGauge P 0 = 0 :=
  polyInterpGauge_zero P 2

lemma polyBinaryGauge_mono (P : PolyRecData) : Monotone (polyBinaryGauge P) :=
  polyInterpGauge_mono P (by norm_num)

lemma polyBinaryGauge_continuous (P : PolyRecData) : Continuous (polyBinaryGauge P) :=
  polyInterpGauge_continuous P (by norm_num)

lemma polyBinaryGauge_at_inv_Q (P : PolyRecData) {n : ℕ} (hn : P.J₀ ≤ n) :
    polyBinaryGauge P (ENNReal.ofReal (1 / (P.Q n : ℝ))) =
      ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ))) :=
  polyInterpGauge_at_inv_Q P (by norm_num) hn

/-- **Remark `rem:poly-gauge-scale`**：插值无关的对数标度渐近（含 $1/r$ 因子）。
    当 $t \to 0^+$ 时，
    $\frac{-\log g_b^{(r,c,d)}(t)}{\log(1/t) / \log\log(1/t)} \longrightarrow \frac{\log b}{r}$。 -/
theorem polyInterpGauge_log_scale_tendsto (P : PolyRecData) {b : ℝ} (hb : 1 < b) :
    Tendsto (fun t : ℝ =>
      -Real.log (polyInterpGaugeReal P b t) /
        (Real.log (1 / t) / Real.log (Real.log (1 / t))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log b / (P.r : ℝ))) := by
  have hlogb_pos : 0 < Real.log b := Real.log_pos hb
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hr_pos : (0 : ℝ) < (P.r : ℝ) := by exact_mod_cast P.hr
  have hQ_lim := poly_log_Q_div_n_log_n_tendsto P
  have hlog_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog_succ_ratio : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (nhds 1) := by
    have hdiff0 : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
        atTop (nhds 0) := by
      have hinv0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
        tendsto_natCast_atTop_atTop.const_div_atTop 1
      have hle : ∀ᶠ n : ℕ in atTop,
          0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ∧
          Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hn1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        constructor
        · exact sub_nonneg.mpr (Real.log_le_log hnpos (by push_cast; linarith))
        · have h1 := Real.log_le_sub_one_of_pos (div_pos hn1pos hnpos)
          rw [Real.log_div hn1pos.ne' hnpos.ne'] at h1
          have h2 : ((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
            push_cast; field_simp; ring
          linarith
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv0
        (hle.mono fun _ h => h.1) (hle.mono fun _ h => h.2)
    have hdiv0 : Tendsto (fun n : ℕ =>
        (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (nhds 0) :=
      hdiff0.div_atTop hlog_top
    have hsum := hdiv0.add tendsto_const_nhds (b := (1 : ℝ))
    simp only [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog_ne : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    field_simp
    ring
  have hQ_succ_div : Tendsto (fun n : ℕ =>
      Real.log (P.Q (n + 1) : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) atTop (nhds (P.r : ℝ)) := by
    have hshift := hQ_lim.comp (tendsto_add_atTop_nat 1)
    have hfac : Tendsto (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) / (n : ℝ)) * (Real.log ((n + 1 : ℕ) : ℝ) / Real.log (n : ℝ)))
        atTop (nhds 1) := by
      have hn1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 1) := by
        have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
          tendsto_natCast_atTop_atTop.const_div_atTop 1
        have h1 := h0.add tendsto_const_nhds (b := (1 : ℝ))
        simp only [zero_add] at h1
        refine h1.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        push_cast; field_simp; ring
      simpa using hn1.mul hlog_succ_ratio
    have hprod := hshift.mul hfac
    rw [mul_one] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hn1_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hlogn_ne : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    have hlogn1_ne : Real.log ((n + 1 : ℕ) : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne'
    simp only [Function.comp_apply]
    field_simp
  -- log log Q_n / log n → 1 与 log log Q_{n+1} / log n → 1
  have hloglogQ : Tendsto (fun n : ℕ => Real.log (Real.log (P.Q n : ℝ)) / Real.log (n : ℝ))
      atTop (nhds 1) := by
    have h1 : Tendsto (fun n : ℕ =>
        Real.log (Real.log (P.Q n : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) / Real.log (n : ℝ))
        atTop (nhds 0) :=
      ((Real.continuousAt_log hr_pos.ne').tendsto.comp hQ_lim).div_atTop hlog_top
    have h2 : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
        atTop (nhds 0) := by
      have hdiv := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
      exact hdiv.comp hlog_top
    have hsum := (h1.add h2).add tendsto_const_nhds (b := (1 : ℝ))
    simp only [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 2, hQ_lim.eventually (Ioi_mem_nhds (by linarith : (P.r : ℝ) / 2 < (P.r : ℝ)))] with n hn hQr
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hQn_pos : 0 < Real.log (P.Q n : ℝ) := by
      have h1 : 0 < Real.log (P.Q n : ℝ) / ((n : ℝ) * Real.log (n : ℝ)) := lt_trans (by positivity) hQr
      exact (div_pos_iff_of_pos_right (mul_pos hn_pos hlogn_pos)).mp h1
    have hprod_ne : ((n : ℝ) * Real.log (n : ℝ)) ≠ 0 := (mul_pos hn_pos hlogn_pos).ne'
    rw [Real.log_div hQn_pos.ne' hprod_ne, Real.log_mul hn_pos.ne' hlogn_pos.ne']
    field_simp; ring
  have hloglogQ_succ : Tendsto (fun n : ℕ => Real.log (Real.log (P.Q (n + 1) : ℝ)) / Real.log (n : ℝ))
      atTop (nhds 1) := by
    have h1 := (hloglogQ.comp (tendsto_add_atTop_nat 1)).mul hlog_succ_ratio
    rw [one_mul] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hne : Real.log ((n + 1 : ℕ) : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne'
    simp only [Function.comp_apply]
    field_simp
  -- 上下界夹逼序列 loSeq n ≤ f t ≤ hiSeq n，均收敛到 log b / r
  let loSeq : ℕ → ℝ := fun n =>
    Real.log b * (Real.log (Real.log (P.Q n : ℝ)) / Real.log (n : ℝ)) /
      (Real.log (P.Q (n + 1) : ℝ) / ((n : ℝ) * Real.log (n : ℝ)))
  let hiSeq : ℕ → ℝ := fun n =>
    (((n + 1 : ℕ) : ℝ) / (n : ℝ)) * Real.log b *
      (Real.log (Real.log (P.Q (n + 1) : ℝ)) / Real.log (n : ℝ)) /
      (Real.log (P.Q n : ℝ) / ((n : ℝ) * Real.log (n : ℝ)))
  have hn1_ratio : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_natCast_atTop_atTop.const_div_atTop 1
    have h1 := h0.add tendsto_const_nhds (b := (1 : ℝ))
    simp only [zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    push_cast; field_simp; ring
  have hlo_lim : Tendsto loSeq atTop (nhds (Real.log b / (P.r : ℝ))) := by
    have hnum : Tendsto (fun n : ℕ => Real.log b * (Real.log (Real.log (P.Q n : ℝ)) / Real.log (n : ℝ)))
        atTop (nhds (Real.log b * 1)) := tendsto_const_nhds.mul hloglogQ
    have hdiv := hnum.div hQ_succ_div hr_pos.ne'
    rw [mul_one] at hdiv
    exact hdiv
  have hhi_lim : Tendsto hiSeq atTop (nhds (Real.log b / (P.r : ℝ))) := by
    have hnum : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) / (n : ℝ)) * Real.log b *
        (Real.log (Real.log (P.Q (n + 1) : ℝ)) / Real.log (n : ℝ)))
        atTop (nhds (1 * Real.log b * 1)) := ((hn1_ratio.mul tendsto_const_nhds).mul hloglogQ_succ)
    have hdiv := hnum.div hQ_lim hr_pos.ne'
    rw [one_mul, mul_one] at hdiv
    exact hdiv
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hev_Q : ∀ᶠ n : ℕ in atTop, (P.J₀ ≤ n) ∧ (2 ≤ n) ∧
      (1 < Real.log (P.Q n : ℝ)) ∧ (1 < Real.log (P.Q (n + 1) : ℝ)) := by
    have hQ_gt_e : ∀ᶠ n : ℕ in atTop, Real.exp 1 < (P.Q n : ℝ) :=
      P.poly_Q_tendsto_atTop.eventually_gt_atTop (Real.exp 1)
    filter_upwards [eventually_ge_atTop (max P.J₀ 2), hQ_gt_e,
      (tendsto_add_atTop_nat 1).eventually hQ_gt_e] with n hn hQn hQn1
    refine ⟨le_trans (le_max_left _ _) hn, le_trans (le_max_right _ _) hn, ?_, ?_⟩
    · rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) hQn
    · rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) hQn1
  have hev_lo := hlo_lim.eventually (Metric.ball_mem_nhds _ hε)
  have hev_hi := hhi_lim.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hev_Q.and (hev_lo.and hev_hi))
  refine ⟨polyInvQ P N, polyInvQ_pos P N, fun {t} ht_pos ht_dist => ?_⟩
  have ht_lt_N : t < polyInvQ P N := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos] at ht_dist
    exact ht_dist
  have hNJ₀ : P.J₀ ≤ N := (hN N le_rfl).1.1
  have ht_lt_J₀ : t < polyInvQ P P.J₀ := lt_of_lt_of_le ht_lt_N (polyInvQ_le_J₀ P hNJ₀)
  set n := polyInterpIdx P t
  obtain ⟨hnJ₀, hnlo, hnhi⟩ := polyInterpIdx_spec P ht_pos ht_lt_J₀
  have hN_le_n : N ≤ n := by
    by_contra hlt
    push Not at hlt
    have hle : n + 1 ≤ N := by omega
    have hq : polyInvQ P N ≤ polyInvQ P (n + 1) :=
      polyInvQ_antitoneOn P (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hNJ₀) hle
    linarith
  obtain ⟨⟨_, hn2, hlogQn, hlogQn1⟩, hlo_ball, hhi_ball⟩ := hN n hN_le_n
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hQn_pos : (0 : ℝ) < (P.Q n : ℝ) := by exact_mod_cast P.hQ_pos n
  have hQn1_pos : (0 : ℝ) < (P.Q (n + 1) : ℝ) := by exact_mod_cast P.hQ_pos (n + 1)
  have hinv_t_lo : (P.Q n : ℝ) < 1 / t := by
    have h1 : t < 1 / (P.Q n : ℝ) := by simpa [polyInvQ] using hnhi
    rw [lt_div_iff₀ ht_pos]
    have h2 := (lt_div_iff₀ hQn_pos).mp h1
    linarith
  have hinv_t_hi : 1 / t ≤ (P.Q (n + 1) : ℝ) := by
    have h1 : 1 / (P.Q (n + 1) : ℝ) ≤ t := by simpa [polyInvQ] using hnlo
    rw [div_le_iff₀ ht_pos]
    have h2 := (div_le_iff₀ hQn1_pos).mp h1
    linarith
  have hlog_t_lo : Real.log (P.Q n : ℝ) ≤ Real.log (1 / t) :=
    Real.log_le_log hQn_pos hinv_t_lo.le
  have hlog_t_hi : Real.log (1 / t) ≤ Real.log (P.Q (n + 1) : ℝ) :=
    Real.log_le_log (one_div_pos.mpr ht_pos) hinv_t_hi
  have hloglog_t_lo : Real.log (Real.log (P.Q n : ℝ)) ≤ Real.log (Real.log (1 / t)) :=
    Real.log_le_log (by linarith) hlog_t_lo
  have hloglog_t_hi : Real.log (Real.log (1 / t)) ≤ Real.log (Real.log (P.Q (n + 1) : ℝ)) :=
    Real.log_le_log (by linarith) hlog_t_hi
  have hloglog_Qn_pos : 0 < Real.log (Real.log (P.Q n : ℝ)) := Real.log_pos hlogQn
  have hloglog_t_pos : 0 < Real.log (Real.log (1 / t)) := lt_of_lt_of_le hloglog_Qn_pos hloglog_t_lo
  have hg_lo : b ^ (-((n + 1 : ℕ) : ℤ)) ≤ polyInterpGaugeReal P b t := by
    calc b ^ (-((n + 1 : ℕ) : ℤ))
        = polyInterpGaugeReal P b (polyInvQ P (n + 1)) :=
          (polyInterpGaugeReal_at_invQ P hb (by omega)).symm
      _ ≤ polyInterpGaugeReal P b t := polyInterpGaugeReal_mono P hb hnlo
  have hg_hi : polyInterpGaugeReal P b t ≤ b ^ (-(n : ℤ)) := by
    calc polyInterpGaugeReal P b t
        ≤ polyInterpGaugeReal P b (polyInvQ P n) := polyInterpGaugeReal_mono P hb hnhi.le
      _ = b ^ (-(n : ℤ)) := polyInterpGaugeReal_at_invQ P hb hnJ₀
  have hg_pos : 0 < polyInterpGaugeReal P b t :=
    lt_of_lt_of_le (zpow_pos hb0 _) hg_lo
  have hneglog_lo : (n : ℝ) * Real.log b ≤ -Real.log (polyInterpGaugeReal P b t) := by
    have h1 := Real.log_le_log hg_pos hg_hi
    rw [Real.log_zpow] at h1
    push_cast at h1 ⊢
    linarith
  have hneglog_hi : -Real.log (polyInterpGaugeReal P b t) ≤ ((n + 1 : ℕ) : ℝ) * Real.log b := by
    have h1 := Real.log_le_log (zpow_pos hb0 _) hg_lo
    rw [Real.log_zpow] at h1
    push_cast at h1 ⊢
    linarith
  have hden_pos : 0 < Real.log (1 / t) / Real.log (Real.log (1 / t)) :=
    div_pos (by linarith) hloglog_t_pos
  have hden_hi : Real.log (1 / t) / Real.log (Real.log (1 / t)) ≤
      Real.log (P.Q (n + 1) : ℝ) / Real.log (Real.log (P.Q n : ℝ)) :=
    div_le_div₀ (by linarith) hlog_t_hi hloglog_Qn_pos hloglog_t_lo
  have hden_lo : Real.log (P.Q n : ℝ) / Real.log (Real.log (P.Q (n + 1) : ℝ)) ≤
      Real.log (1 / t) / Real.log (Real.log (1 / t)) :=
    div_le_div₀ (by linarith) hlog_t_lo hloglog_t_pos hloglog_t_hi
  have hden_lo_pos : 0 < Real.log (P.Q n : ℝ) / Real.log (Real.log (P.Q (n + 1) : ℝ)) :=
    div_pos (by linarith) (lt_of_lt_of_le hloglog_t_pos hloglog_t_hi)
  have hf_lo : loSeq n ≤
      -Real.log (polyInterpGaugeReal P b t) / (Real.log (1 / t) / Real.log (Real.log (1 / t))) := by
    have hlo_eq : loSeq n = ((n : ℝ) * Real.log b) /
        (Real.log (P.Q (n + 1) : ℝ) / Real.log (Real.log (P.Q n : ℝ))) := by
      dsimp [loSeq]
      have hlog_ne : Real.log (n : ℝ) ≠ 0 := hlogn_pos.ne'
      have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
      field_simp
    rw [hlo_eq]
    calc ((n : ℝ) * Real.log b) /
          (Real.log (P.Q (n + 1) : ℝ) / Real.log (Real.log (P.Q n : ℝ)))
        ≤ ((n : ℝ) * Real.log b) / (Real.log (1 / t) / Real.log (Real.log (1 / t))) := by
          gcongr
      _ ≤ (-Real.log (polyInterpGaugeReal P b t)) /
            (Real.log (1 / t) / Real.log (Real.log (1 / t))) := by
          gcongr
  have hf_hi : -Real.log (polyInterpGaugeReal P b t) / (Real.log (1 / t) / Real.log (Real.log (1 / t))) ≤
      hiSeq n := by
    have hhi_eq : hiSeq n = (((n + 1 : ℕ) : ℝ) * Real.log b) /
        (Real.log (P.Q n : ℝ) / Real.log (Real.log (P.Q (n + 1) : ℝ))) := by
      dsimp [hiSeq]
      have hlog_ne : Real.log (n : ℝ) ≠ 0 := hlogn_pos.ne'
      have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
      field_simp
    rw [hhi_eq]
    calc (-Real.log (polyInterpGaugeReal P b t)) /
          (Real.log (1 / t) / Real.log (Real.log (1 / t)))
        ≤ (((n + 1 : ℕ) : ℝ) * Real.log b) /
            (Real.log (1 / t) / Real.log (Real.log (1 / t))) := by
          gcongr
      _ ≤ (((n + 1 : ℕ) : ℝ) * Real.log b) /
            (Real.log (P.Q n : ℝ) / Real.log (Real.log (P.Q (n + 1) : ℝ))) := by
          gcongr
  rw [Real.dist_eq, abs_lt] at hlo_ball hhi_ball ⊢
  constructor <;> linarith


/-! ## 第三部分：`P.latticePoly` 的小正元、平移不变性与无符号极限刻画 -/

lemma nat_mul_mem_latticePoly (P : PolyRecData) {y : ℝ} (hy : y ∈ P.latticePoly) (m : ℕ) :
    (m : ℝ) * y ∈ P.latticePoly := by
  rcases hy with ⟨a, b, rfl⟩
  refine ⟨(m : ℤ) * a, (m : ℤ) * b, ?_⟩
  push_cast; ring

lemma int_mul_mem_latticePoly (P : PolyRecData) {y : ℝ} (hy : y ∈ P.latticePoly) (m : ℤ) :
    (m : ℝ) * y ∈ P.latticePoly := by
  rcases hy with ⟨a, b, rfl⟩
  refine ⟨m * a, m * b, ?_⟩
  push_cast; ring

/-- 由 `theta_sub_ratio_pos_and_lt` 直接构造 `P.latticePoly` 中任意小的正元（模 $1$ 稠密）。 -/
lemma exists_mem_latticePoly_pos_lt (P : PolyRecData) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ P.latticePoly, 0 < y ∧ y < ε := by
  have hev : ∀ᶠ j : ℕ in atTop, 1 / (P.Q (j + 1) : ℝ) < ε := by
    have h0 : Tendsto (fun j : ℕ => 1 / (P.Q (j + 1) : ℝ)) atTop (nhds 0) :=
      (P.poly_Q_tendsto_atTop.comp (tendsto_add_atTop_nat 1)).const_div_atTop 1
    exact h0.eventually (Iio_mem_nhds hε)
  obtain ⟨j, hjε, hjJ₀⟩ := (hev.and (eventually_ge_atTop P.J₀)).exists
  have hth := P.theta_sub_ratio_pos_and_lt hjJ₀
  have hQt_pos : (0 : ℝ) < (P.Qtilde j : ℝ) := by exact_mod_cast P.Qtilde_pos (by omega)
  have hQt1_pos : (0 : ℝ) < (P.Qtilde (j + 1) : ℝ) := by exact_mod_cast P.Qtilde_pos (by omega)
  have hg_pos : (0 : ℝ) < (P.gFactor : ℝ) := by exact_mod_cast P.gFactor_pos
  have hgQ1 : (P.gFactor : ℝ) * (P.Qtilde (j + 1) : ℝ) = (P.Q (j + 1) : ℝ) := by
    exact_mod_cast P.g_mul_Qtilde (by omega)
  set z : ℝ := ((P.Qtilde j : ℝ) * P.theta - (P.Ptilde j : ℝ)) / (P.gFactor : ℝ)
  have hz_abs : |z| = (P.Qtilde j : ℝ) * |P.theta - (P.Ptilde j : ℝ) / (P.Qtilde j : ℝ)| /
      (P.gFactor : ℝ) := by
    have h1 : z = ((P.Qtilde j : ℝ) * (P.theta - (P.Ptilde j : ℝ) / (P.Qtilde j : ℝ))) /
        (P.gFactor : ℝ) := by
      dsimp [z]; field_simp
    rw [h1, abs_div, abs_mul, abs_of_pos hQt_pos, abs_of_pos hg_pos]
  have hz_pos : 0 < |z| := by
    rw [hz_abs]
    exact div_pos (mul_pos hQt_pos hth.1) hg_pos
  have hz_lt : |z| < ε := by
    rw [hz_abs]
    have h1 : (P.Qtilde j : ℝ) * |P.theta - (P.Ptilde j : ℝ) / (P.Qtilde j : ℝ)| <
        1 / (P.Qtilde (j + 1) : ℝ) := by
      have hmul := mul_lt_mul_of_pos_left hth.2 hQt_pos
      have hrhs : (P.Qtilde j : ℝ) * (1 / ((P.Qtilde j : ℝ) * (P.Qtilde (j + 1) : ℝ))) =
          1 / (P.Qtilde (j + 1) : ℝ) := by field_simp
      linarith
    have h2 : (P.Qtilde j : ℝ) * |P.theta - (P.Ptilde j : ℝ) / (P.Qtilde j : ℝ)| / (P.gFactor : ℝ) <
        (1 / (P.Qtilde (j + 1) : ℝ)) / (P.gFactor : ℝ) :=
      div_lt_div_of_pos_right h1 hg_pos
    have h3 : (1 / (P.Qtilde (j + 1) : ℝ)) / (P.gFactor : ℝ) = 1 / (P.Q (j + 1) : ℝ) := by
      rw [← hgQ1]; field_simp
    linarith
  have hz_mem : z ∈ P.latticePoly := by
    rw [P.latticePoly_eq_inv_g_lattice]
    refine ⟨-P.Ptilde j, P.Qtilde j, ?_⟩
    push_cast
    dsimp [z]
    ring
  rcases le_or_gt 0 z with hz0 | hz0
  · refine ⟨z, hz_mem, ?_, ?_⟩
    · rwa [abs_of_nonneg hz0] at hz_pos
    · rwa [abs_of_nonneg hz0] at hz_lt
  · refine ⟨-z, P.neg_mem_latticePoly hz_mem, ?_, ?_⟩
    · rwa [abs_of_neg hz0] at hz_pos
    · rwa [abs_of_neg hz0] at hz_lt

/-- 在任意非空开区间 $(a, b)$ 内放置 $N = \lfloor (b-a)/(3r) \rfloor$ 个互不相交的
    $[c - r, c + r]$ 的 $L^{(r,c,d)}$-平移拷贝。 -/
lemma exists_disjoint_latticePoly_translates_in_Ioo (P : PolyRecData)
    {a b c r : ℝ} (hab : a < b) (hr : 0 < r) :
    let N : ℕ := Nat.floor ((b - a) / (3 * r))
    ∃ t : Fin N → ℝ,
      (∀ i, t i ∈ P.latticePoly) ∧
      (∀ i, Set.Icc (c + t i - r) (c + t i + r) ⊆ Set.Ioo a b) ∧
      Pairwise (fun i j =>
        Disjoint (Set.Icc (c + t i - r) (c + t i + r))
                 (Set.Icc (c + t j - r) (c + t j + r))) := by
  intro N
  obtain ⟨y, hyL, hy_pos, hy_lt⟩ := exists_mem_latticePoly_pos_lt P hr
  set m : ℕ := Nat.floor (2 * r / y) + 1
  set s : ℝ := (m : ℝ) * y
  have hs_mem : s ∈ P.latticePoly := nat_mul_mem_latticePoly P hyL m
  have hs_gt : 2 * r < s := by
    have hm_gt : 2 * r / y < (m : ℝ) := by
      dsimp [m]; push_cast; exact Nat.lt_floor_add_one _
    have := (div_lt_iff₀ hy_pos).mp hm_gt
    linarith
  have hs_lt : s < 3 * r := by
    have hm_le : (m : ℝ) ≤ 2 * r / y + 1 := by
      dsimp [m]; push_cast
      linarith [Nat.floor_le (by positivity : 0 ≤ 2 * r / y)]
    have hmul : (m : ℝ) * y ≤ (2 * r / y + 1) * y :=
      mul_le_mul_of_nonneg_right hm_le (le_of_lt hy_pos)
    have heq : (2 * r / y + 1) * y = 2 * r + y := by field_simp
    linarith
  set k₀ : ℤ := Int.floor ((a + r - c) / y) + 1
  set t₀ : ℝ := (k₀ : ℝ) * y
  have ht₀_mem : t₀ ∈ P.latticePoly := int_mul_mem_latticePoly P hyL k₀
  have ht₀_gt : a + r < c + t₀ := by
    have hk_gt : (a + r - c) / y < (k₀ : ℝ) := by
      dsimp [k₀]; push_cast; exact Int.lt_floor_add_one _
    have := (div_lt_iff₀ hy_pos).mp hk_gt
    linarith
  have ht₀_lt : c + t₀ < a + 2 * r := by
    have hk_le : (k₀ : ℝ) ≤ (a + r - c) / y + 1 := by
      dsimp [k₀]; push_cast
      linarith [Int.floor_le ((a + r - c) / y)]
    have hmul : (k₀ : ℝ) * y ≤ ((a + r - c) / y + 1) * y :=
      mul_le_mul_of_nonneg_right hk_le (le_of_lt hy_pos)
    have heq : ((a + r - c) / y + 1) * y = a + r - c + y := by field_simp
    linarith
  refine ⟨fun i => t₀ + (i.1 : ℝ) * s, ?_, ?_, ?_⟩
  · intro i
    exact P.add_mem_latticePoly ht₀_mem (nat_mul_mem_latticePoly P hs_mem i.1)
  · intro i x hx
    have hi_nonneg : 0 ≤ (i.1 : ℝ) * s := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have hlo : a < x := by linarith [hx.1]
    have hi_le : ((i.1 + 1 : ℕ) : ℝ) ≤ (b - a) / (3 * r) := by
      have h1 : i.1 + 1 ≤ N := i.2
      have h2 : ((i.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
      have h3 : (N : ℝ) ≤ (b - a) / (3 * r) :=
        Nat.floor_le (div_nonneg (sub_nonneg.mpr (le_of_lt hab)) (by positivity))
      exact le_trans h2 h3
    have hmul3 : 3 * ((i.1 + 1 : ℕ) : ℝ) * r ≤ b - a := by
      have h3r : 0 < 3 * r := by positivity
      have := (le_div_iff₀ h3r).mp hi_le
      linarith
    have hhi : x < b := by
      have hmul_s : (i.1 : ℝ) * s ≤ (i.1 : ℝ) * (3 * r) :=
        mul_le_mul_of_nonneg_left (le_of_lt hs_lt) (Nat.cast_nonneg _)
      have hcast : ((i.1 + 1 : ℕ) : ℝ) = (i.1 : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hmul3
      linarith [hx.2]
    exact ⟨hlo, hhi⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · have hij1 : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hlt
      have hstep : (i.1 : ℝ) * s + r < (j.1 : ℝ) * s - r := by
        have h1 : ((i.1 : ℝ) + 1) * s ≤ (j.1 : ℝ) * s :=
          mul_le_mul_of_nonneg_right hij1 (by linarith)
        linarith
      linarith [hxi.2, hxj.1]
    · have hji1 : (j.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by exact_mod_cast hlt
      have hstep : (j.1 : ℝ) * s + r < (i.1 : ℝ) * s - r := by
        have h1 : ((j.1 : ℝ) + 1) * s ≤ (i.1 : ℝ) * s :=
          mul_le_mul_of_nonneg_right hji1 (by linarith)
        linarith
      linarith [hxj.2, hxi.1]

/-- 严格子水平集 $\{\Lambda^{(r,c,d)} < k/c\}$。 -/
def polyStrictLevel (P : PolyRecData) (k : ℕ) : Set ℝ :=
  {x : ℝ | P.polyApprExponent x < ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))}

/-- 精确水平集 $S_k^{(r,c,d)} = \{\Lambda^{(r,c,d)} = k/c\}$。 -/
def polyExactLevel (P : PolyRecData) (k : ℕ) : Set ℝ :=
  {x : ℝ | P.polyApprExponent x = ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))}

/-- 无符号精确极限集 $E_{\mathrm{lim}}^{(r,c,d)}(t) = \{x \in \mathbb{R} : j^r \|Q_j x\| \to t\}$。 -/
def polyUnsignedExactLimitSet (P : PolyRecData) (t : ℝ) : Set ℝ :=
  {x : ℝ | Tendsto (P.polyWeightedSeq (P.r : ℝ) x) atTop (nhds t)}

/-- **Theorem `thm:poly-gauge-trichotomy`(ii) 数字刻画**：
    $j^r \|Q_j x\| \to k/c \iff u_j(x) \to 0 \land \forall^\infty j,\, d_j(x) \in \{-k, +k\}$。 -/
theorem poly_unsigned_exact_limit_iff_defect_binary (P : PolyRecData) (x : ℝ) (k : ℕ) :
    x ∈ polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ↔
      Tendsto (P.polyEps x) atTop (nhds 0) ∧
        ∀ᶠ j : ℕ in atTop, P.polyDefect x j = (k : ℤ) ∨ P.polyDefect x j = -(k : ℤ) := by
  have hc_pos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
  constructor
  · intro hx
    have hε : Tendsto (P.polyEps x) atTop (nhds 0) := by
      have hev : ∀ᶠ j : ℕ in atTop,
          P.polyWeightedSeq (P.r : ℝ) x j < (k : ℝ) / (P.c : ℝ) + 1 :=
        hx.eventually (Iio_mem_nhds (by linarith))
      have hbound : ∀ᶠ j : ℕ in atTop,
          |P.polyEps x j| ≤ ((k : ℝ) / (P.c : ℝ) + 1) / (j : ℝ) := by
        filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
        have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
        have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
        have hjr : (j : ℝ) ≤ (j : ℝ) ^ P.r := by
          calc (j : ℝ) = (j : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (j : ℝ) ^ P.r := pow_le_pow_right₀ hj1R P.hr
        have hseq : (j : ℝ) ^ P.r * |P.polyEps x j| = P.polyWeightedSeq (P.r : ℝ) x j := by
          unfold PolyRecData.polyWeightedSeq
          rw [Real.rpow_natCast, P.abs_polyEps_eq_dist]
        have hmul : (j : ℝ) * |P.polyEps x j| ≤ (k : ℝ) / (P.c : ℝ) + 1 := by
          have h1 : (j : ℝ) * |P.polyEps x j| ≤ (j : ℝ) ^ P.r * |P.polyEps x j| :=
            mul_le_mul_of_nonneg_right hjr (abs_nonneg _)
          linarith [hseq, hj]
        exact (le_div_iff₀ hjpos).mpr (by linarith)
      exact FullSpectrumDiscrete.tendsto_zero_of_eventually_abs_le_div hbound
    have happrox := P.poly_abs_defect_approx x hε
    have hclim : Tendsto (fun j : ℕ => (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j)
        atTop (nhds (k : ℝ)) := by
      have h1 := hx.const_mul (P.c : ℝ)
      have heq : (P.c : ℝ) * ((k : ℝ) / (P.c : ℝ)) = (k : ℝ) := by field_simp
      rwa [heq] at h1
    have hdef_abs_lim : Tendsto (fun j : ℕ => |(P.polyDefect x j : ℝ)|) atTop (nhds (k : ℝ)) := by
      have hsum := happrox.add hclim
      rw [zero_add] at hsum
      refine hsum.congr' (Filter.Eventually.of_forall fun j => ?_)
      dsimp [PolyRecData.polyWeightedSeq]
      rw [Real.rpow_natCast]
      ring
    have hev_eq : ∀ᶠ j : ℕ in atTop, |P.polyDefect x j| = (k : ℤ) := by
      have hball : ∀ᶠ j : ℕ in atTop, |(P.polyDefect x j : ℝ)| ∈
          Metric.ball (k : ℝ) (1 / 2) :=
        hdef_abs_lim.eventually (Metric.ball_mem_nhds _ (by norm_num))
      filter_upwards [hball] with j hj
      rw [Metric.mem_ball, Real.dist_eq, ← Int.cast_abs, abs_lt] at hj
      have hlt1 : |P.polyDefect x j| - (k : ℤ) < 1 := by
        have hR : ((|P.polyDefect x j| - (k : ℤ) : ℤ) : ℝ) < (1 : ℤ) := by
          rw [Int.cast_sub, Int.cast_natCast, Int.cast_one]
          linarith
        exact Int.cast_lt.mp hR
      have hgt1 : (-1 : ℤ) < |P.polyDefect x j| - (k : ℤ) := by
        have hR : ((-1 : ℤ) : ℝ) < ((|P.polyDefect x j| - (k : ℤ) : ℤ) : ℝ) := by
          rw [Int.cast_sub, Int.cast_natCast, Int.cast_neg, Int.cast_one]
          linarith
        exact Int.cast_lt.mp hR
      omega
    refine ⟨hε, hev_eq.mono fun j hj => abs_eq (Int.natCast_nonneg k) |>.mp hj⟩
  · rintro ⟨hε, hbin⟩
    have hev_abs : ∀ᶠ j : ℕ in atTop, |(P.polyDefect x j : ℝ)| = (k : ℝ) := by
      filter_upwards [hbin] with j hj
      rcases hj with hj | hj <;> simp [hj]
    have hlim_abs : Tendsto (fun j : ℕ => |(P.polyDefect x j : ℝ)|) atTop (nhds (k : ℝ)) :=
      tendsto_const_nhds.congr' (hev_abs.mono fun _ h => h.symm)
    have happrox := P.poly_abs_defect_approx x hε
    have hclim : Tendsto (fun j : ℕ => (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j)
        atTop (nhds (k : ℝ)) := by
      have hsub := hlim_abs.sub happrox
      rw [sub_zero] at hsub
      refine hsub.congr' (Filter.Eventually.of_forall fun j => ?_)
      dsimp [PolyRecData.polyWeightedSeq]
      rw [Real.rpow_natCast]
      ring
    have hdiv := hclim.const_mul (1 / (P.c : ℝ))
    have heq : (1 / (P.c : ℝ)) * (k : ℝ) = (k : ℝ) / (P.c : ℝ) := by ring
    rw [heq] at hdiv
    refine hdiv.congr' (Filter.Eventually.of_forall fun j => ?_)
    field_simp

/-- **Theorem `thm:poly-gauge-trichotomy`(ii) 空集刻画**：若 $t \notin \frac{1}{c}\mathbb{Z}_{\ge 0}$，
    则 $E_{\mathrm{lim}}^{(r,c,d)}(t) = \varnothing$。 -/
theorem poly_unsigned_exact_limit_empty_of_not_div_c (P : PolyRecData) {t : ℝ}
    (ht : ∀ k : ℕ, t ≠ (k : ℝ) / (P.c : ℝ)) :
    polyUnsignedExactLimitSet P t = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have ht_nn : 0 ≤ t := ge_of_tendsto hx
    (Filter.Eventually.of_forall (P.polyWeightedSeq_nonneg (P.r : ℝ) x))
  have hexp : P.polyApprExponent x = ENNReal.ofReal t :=
    (ENNReal.tendsto_ofReal hx).limsup_eq
  have hmem : ENNReal.ofReal t ∈ Set.range P.polyApprExponent := ⟨x, hexp⟩
  rw [P.poly_range_apprExponent] at hmem
  rcases hmem with ⟨k, hk⟩ | htop
  · have hEq : t = (k : ℝ) / (P.c : ℝ) := by
      have := congrArg ENNReal.toReal hk
      rwa [ENNReal.toReal_ofReal ht_nn, ENNReal.toReal_ofReal (by positivity)] at this
    exact ht k hEq
  · exact ENNReal.ofReal_ne_top htop

/-- $L^{(r,c,d)}$-平移不变性（对 $\Lambda_\alpha^{(r,c,d)}$、$\Lambda^{(r,c,d)}$ 及无符号精确极限集）。 -/
lemma abs_polyWeightedSeq_add_sub_le (P : PolyRecData) (α x y : ℝ) (j : ℕ) :
    |P.polyWeightedSeq α (x + y) j - P.polyWeightedSeq α x j| ≤ P.polyWeightedSeq α y j := by
  unfold PolyRecData.polyWeightedSeq
  have hpow : 0 ≤ (j : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg j) α
  have heq : (j : ℝ) ^ α * distToNearestInt ((P.Q j : ℝ) * (x + y)) -
      (j : ℝ) ^ α * distToNearestInt ((P.Q j : ℝ) * x) =
      (j : ℝ) ^ α * (distToNearestInt ((P.Q j : ℝ) * x + (P.Q j : ℝ) * y) -
        distToNearestInt ((P.Q j : ℝ) * x)) := by
    rw [mul_add]; ring
  rw [heq, abs_mul, abs_of_nonneg hpow]
  exact mul_le_mul_of_nonneg_left (GaugeExact.abs_distToNearestInt_add_sub_le _ _) hpow

lemma polyWeightedExponent_add_latticePoly (P : PolyRecData) (α x : ℝ)
    {y : ℝ} (hy : y ∈ P.latticePoly) :
    P.polyWeightedExponent α (x + y) = P.polyWeightedExponent α x := by
  have hle : ∀ (z w : ℝ), w ∈ P.latticePoly →
      P.polyWeightedExponent α (z + w) ≤ P.polyWeightedExponent α z := by
    intro z w hw
    have hw0 : Tendsto (P.polyWeightedSeq α w) atTop (nhds 0) :=
      (P.polyWeightedExponent_eq_zero_iff α w).mp
        (P.polyWeightedExponent_eq_zero_of_mem_latticePoly hw α)
    by_cases hz_top : P.polyWeightedExponent α z = ⊤
    · simp [hz_top]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hδ_pos : (0 : ℝ) < (ε : ℝ) / 2 := half_pos (by exact_mod_cast hε)
    have hδ_enn : (0 : ℝ≥0∞) < ENNReal.ofReal ((ε : ℝ) / 2) :=
      ENNReal.ofReal_pos.mpr hδ_pos
    have hz_lt : P.polyWeightedExponent α z <
        P.polyWeightedExponent α z + ENNReal.ofReal ((ε : ℝ) / 2) :=
      ENNReal.lt_add_right hz_top hδ_enn.ne'
    have hev_z : ∀ᶠ j : ℕ in atTop,
        ENNReal.ofReal (P.polyWeightedSeq α z j) <
          P.polyWeightedExponent α z + ENNReal.ofReal ((ε : ℝ) / 2) :=
      eventually_lt_of_limsup_lt hz_lt
    have hev_w : ∀ᶠ j : ℕ in atTop, P.polyWeightedSeq α w j < (ε : ℝ) / 2 :=
      hw0.eventually (Iio_mem_nhds hδ_pos)
    have hev_zw : ∀ᶠ j : ℕ in atTop,
        ENNReal.ofReal (P.polyWeightedSeq α (z + w) j) ≤
          P.polyWeightedExponent α z + (ε : ℝ≥0∞) := by
      filter_upwards [hev_z, hev_w] with j hzj hwj
      have h1 : P.polyWeightedSeq α (z + w) j ≤
          P.polyWeightedSeq α z j + P.polyWeightedSeq α w j := by
        have h := (abs_le.mp (abs_polyWeightedSeq_add_sub_le P α z w j)).2
        linarith
      have hsumδ : ENNReal.ofReal ((ε : ℝ) / 2) + ENNReal.ofReal ((ε : ℝ) / 2) = (ε : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_add hδ_pos.le hδ_pos.le]
        have hhalf : (ε : ℝ) / 2 + (ε : ℝ) / 2 = (ε : ℝ) := add_halves _
        rw [hhalf, ENNReal.ofReal_coe_nnreal]
      calc ENNReal.ofReal (P.polyWeightedSeq α (z + w) j)
          ≤ ENNReal.ofReal (P.polyWeightedSeq α z j + P.polyWeightedSeq α w j) :=
            ENNReal.ofReal_le_ofReal h1
        _ = ENNReal.ofReal (P.polyWeightedSeq α z j) +
              ENNReal.ofReal (P.polyWeightedSeq α w j) :=
            ENNReal.ofReal_add (P.polyWeightedSeq_nonneg α z j)
              (P.polyWeightedSeq_nonneg α w j)
        _ ≤ (P.polyWeightedExponent α z + ENNReal.ofReal ((ε : ℝ) / 2)) +
              ENNReal.ofReal ((ε : ℝ) / 2) := by
            gcongr
        _ = P.polyWeightedExponent α z + (ε : ℝ≥0∞) := by rw [add_assoc, hsumδ]
    exact limsup_le_of_le (by isBoundedDefault) hev_zw
  refine le_antisymm (hle x y hy) ?_
  have h2 := hle (x + y) (-y) (P.neg_mem_latticePoly hy)
  have heq : x + y + -y = x := by ring
  rwa [heq] at h2

lemma polyExactLevel_add_latticePoly (P : PolyRecData) (k : ℕ) {y : ℝ} (hy : y ∈ P.latticePoly) :
    (fun x : ℝ => x + y) ⁻¹' polyExactLevel P k = polyExactLevel P k := by
  ext x
  simp only [Set.mem_preimage, polyExactLevel, Set.mem_ofPred_eq, PolyRecData.polyApprExponent,
    polyWeightedExponent_add_latticePoly P (P.r : ℝ) x hy]

lemma polyUnsignedExactLimit_add_latticePoly (P : PolyRecData) (t : ℝ)
    {y : ℝ} (hy : y ∈ P.latticePoly) :
    (fun x : ℝ => x + y) ⁻¹' polyUnsignedExactLimitSet P t = polyUnsignedExactLimitSet P t := by
  have hfwd : ∀ (z w : ℝ), w ∈ P.latticePoly →
      z ∈ polyUnsignedExactLimitSet P t → z + w ∈ polyUnsignedExactLimitSet P t := by
    intro z w hw hz
    have hw0 : Tendsto (P.polyWeightedSeq (P.r : ℝ) w) atTop (nhds 0) :=
      (P.polyWeightedExponent_eq_zero_iff (P.r : ℝ) w).mp
        (P.polyWeightedExponent_eq_zero_of_mem_latticePoly hw (P.r : ℝ))
    have hdiff0 : Tendsto (fun j : ℕ =>
        P.polyWeightedSeq (P.r : ℝ) (z + w) j - P.polyWeightedSeq (P.r : ℝ) z j)
        atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hw0.neg) hw0 ?_ ?_
      · filter_upwards with j
        exact (abs_le.mp (abs_polyWeightedSeq_add_sub_le P (P.r : ℝ) z w j)).1
      · filter_upwards with j
        exact (abs_le.mp (abs_polyWeightedSeq_add_sub_le P (P.r : ℝ) z w j)).2
    have hsum := hz.add hdiff0
    simpa [polyUnsignedExactLimitSet, add_zero] using hsum
  ext x
  simp only [Set.mem_preimage]
  constructor
  · intro hx
    have h := hfwd (x + y) (-y) (P.neg_mem_latticePoly hy) hx
    have heq : x + y + -y = x := by ring
    rwa [heq] at h
  · intro hx
    exact hfwd x y hy hx


/-! ## 第四部分：多项式递推的统一数字字母表覆盖、`liminf` 规范判据、零测度与 $\sigma$-有限性 -/

/-- 第 `j` 步围绕 `m / Q_j` 半径为 `1 / (2 Q_j)` 的闭区间，直径为 `1 / Q_j`。 -/
def polyGaugeInterv (P : PolyRecData) (j : ℕ) (m : ℤ) : Set ℝ :=
  Set.Icc ((m : ℝ) / (P.Q j : ℝ) - 1 / (2 * (P.Q j : ℝ)))
          ((m : ℝ) / (P.Q j : ℝ) + 1 / (2 * (P.Q j : ℝ)))

lemma ediam_polyGaugeInterv_le (P : PolyRecData) (j : ℕ) (m : ℤ) :
    Metric.ediam (polyGaugeInterv P j m) ≤ ENNReal.ofReal (1 / (P.Q j : ℝ)) := by
  unfold polyGaugeInterv
  rw [Real.ediam_Icc]
  apply ENNReal.ofReal_le_ofReal
  have hQ : (0 : ℝ) < (P.Q j : ℝ) := by exact_mod_cast P.hQ_pos j
  have hid : ((m : ℝ) / (P.Q j : ℝ) + 1 / (2 * (P.Q j : ℝ))) -
      ((m : ℝ) / (P.Q j : ℝ) - 1 / (2 * (P.Q j : ℝ))) = 1 / (P.Q j : ℝ) := by
    field_simp; ring
  rw [hid]

lemma mem_polyGaugeInterv_round (P : PolyRecData) (x : ℝ) (j : ℕ) :
    x ∈ polyGaugeInterv P j (round ((P.Q j : ℝ) * x)) := by
  have hQ : (0 : ℝ) < (P.Q j : ℝ) := by exact_mod_cast P.hQ_pos j
  have hle := P.abs_polyEps_le_half x j
  unfold PolyRecData.polyEps at hle
  rw [abs_le] at hle
  have hdiv1 := div_le_div_of_nonneg_right hle.1 (le_of_lt hQ)
  have hdiv2 := div_le_div_of_nonneg_right hle.2 (le_of_lt hQ)
  have heq1 : ((P.Q j : ℝ) * x - (round ((P.Q j : ℝ) * x) : ℝ)) / (P.Q j : ℝ) =
      x - (round ((P.Q j : ℝ) * x) : ℝ) / (P.Q j : ℝ) := by field_simp
  have heq2 : (-((1 : ℝ) / 2)) / (P.Q j : ℝ) = -(1 / (2 * (P.Q j : ℝ))) := by ring
  have heq3 : (1 / 2 : ℝ) / (P.Q j : ℝ) = 1 / (2 * (P.Q j : ℝ)) := by ring
  rw [heq1, heq2] at hdiv1
  rw [heq1, heq3] at hdiv2
  exact ⟨by linarith, by linarith⟩

/-- 一般数字字母表 `D : Finset ℤ` 上的存活整数对有限树（从下标 `N ≥ P.J₀` 开始）。 -/
def polyPairTreeA (P : PolyRecData) (D : Finset ℤ) (N : ℕ) (m₀ m₁ : ℤ) :
    ℕ → Finset (ℤ × ℤ)
  | 0 => {(m₀, m₁)}
  | n + 1 => (polyPairTreeA P D N m₀ m₁ n).biUnion fun p =>
      D.image fun d => (p.2, P.A (N + n + 1) * p.2 + p.1 + d)

lemma card_polyPairTreeA_le (P : PolyRecData) (D : Finset ℤ) (N : ℕ) (m₀ m₁ : ℤ) :
    ∀ n : ℕ, (polyPairTreeA P D N m₀ m₁ n).card ≤ D.card ^ n
  | 0 => by simp [polyPairTreeA]
  | n + 1 => by
      have ih := card_polyPairTreeA_le P D N m₀ m₁ n
      calc (polyPairTreeA P D N m₀ m₁ (n + 1)).card
          ≤ ∑ p ∈ polyPairTreeA P D N m₀ m₁ n,
              (D.image fun d => (p.2, P.A (N + n + 1) * p.2 + p.1 + d)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ polyPairTreeA P D N m₀ m₁ n, D.card := by
            gcongr
            exact Finset.card_image_le
        _ = (polyPairTreeA P D N m₀ m₁ n).card * D.card := by
            simp [Finset.sum_const]
        _ ≤ D.card ^ n * D.card := Nat.mul_le_mul_right _ ih
        _ = D.card ^ (n + 1) := by rw [pow_succ]

/-- 尾部分支数字均落入 `D` 且起点处最近整数为 `(m₀, m₁)` 的集合。 -/
def polyAlphabetClass (P : PolyRecData) (D : Finset ℤ) (N : ℕ) (m₀ m₁ : ℤ) : Set ℝ :=
  {x : ℝ | round ((P.Q N : ℝ) * x) = m₀ ∧
    round ((P.Q (N + 1) : ℝ) * x) = m₁ ∧
    ∀ j : ℕ, N ≤ j → P.polyDefect x (j + 1) ∈ D}

lemma round_pair_mem_polyPairTreeA (P : PolyRecData) (D : Finset ℤ) (N : ℕ)
    (m₀ m₁ : ℤ) {x : ℝ} (hx : x ∈ polyAlphabetClass P D N m₀ m₁) :
    ∀ n : ℕ, (round ((P.Q (N + n) : ℝ) * x), round ((P.Q (N + n + 1) : ℝ) * x)) ∈
      polyPairTreeA P D N m₀ m₁ n
  | 0 => by
      simp [polyPairTreeA, hx.1, hx.2.1]
  | n + 1 => by
      have ih := round_pair_mem_polyPairTreeA P D N m₀ m₁ hx n
      refine Finset.mem_biUnion.mpr ⟨_, ih, Finset.mem_image.mpr ⟨P.polyDefect x (N + n + 1),
        hx.2.2 (N + n) (by omega), ?_⟩⟩
      have hdef : P.polyDefect x (N + n + 1) =
          round ((P.Q (N + n + 2) : ℝ) * x) -
            P.A (N + n + 1) * round ((P.Q (N + n + 1) : ℝ) * x) -
            round ((P.Q (N + n) : ℝ) * x) := by
        unfold PolyRecData.polyDefect
        have h1 : N + n + 1 + 1 = N + n + 2 := by omega
        have h2 : N + n + 1 - 1 = N + n := by omega
        rw [h1, h2]
      ext
      · rfl
      · change P.A (N + n + 1) * round ((P.Q (N + n + 1) : ℝ) * x) +
            round ((P.Q (N + n) : ℝ) * x) + P.polyDefect x (N + n + 1) =
            round ((P.Q (N + (n + 1) + 1) : ℝ) * x)
        rw [hdef]
        have hidx : N + (n + 1) + 1 = N + n + 2 := by omega
        rw [hidx]
        ring

lemma polyAlphabetClass_subset_cover (P : PolyRecData) (D : Finset ℤ) (N : ℕ)
    (m₀ m₁ : ℤ) (n : ℕ) :
    polyAlphabetClass P D N m₀ m₁ ⊆
      ⋃ p : (polyPairTreeA P D N m₀ m₁ n : Set (ℤ × ℤ)), polyGaugeInterv P (N + n) p.1.1 := by
  intro x hx
  have hp := round_pair_mem_polyPairTreeA P D N m₀ m₁ hx n
  refine Set.mem_iUnion.mpr ⟨⟨_, hp⟩, ?_⟩
  exact mem_polyGaugeInterv_round P x (N + n)

/-- 一般多项式递推的归一化规范代价函数：$b^n \cdot g(1 / Q_n)$。 -/
def polyNormalizedGaugeCost (P : PolyRecData) (b : ℝ) (g : ℝ≥0∞ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (b ^ n) * g (ENNReal.ofReal (1 / (P.Q n : ℝ)))

/-- 通用序列覆盖测度上界：`mkMetric g S ≤ liminf_n card(ι n) * g(r_n)`（当 `r_n → 0`）。 -/
lemma mkMetric_le_liminf_of_seq_cover (S : Set ℝ)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (nhds 0))
    (t : ∀ n : ℕ, ι n → Set ℝ)
    (ht : ∀ᶠ n in atTop, ∀ i, Metric.ediam (t n i) ≤ r n)
    (hst : ∀ᶠ n in atTop, S ⊆ ⋃ i, t n i)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g) :
    Measure.mkMetric g S ≤ liminf (fun n : ℕ => ((Fintype.card (ι n) : ℕ) : ℝ≥0∞) * g (r n)) atTop := by
  have hmain := Measure.mkMetric_le_liminf_sum S r hr t ht hst g
  have hle : ∀ᶠ n in atTop, (∑ i : ι n, g (Metric.ediam (t n i))) ≤
      ((Fintype.card (ι n) : ℕ) : ℝ≥0∞) * g (r n) := by
    filter_upwards [ht] with n htn
    calc ∑ i : ι n, g (Metric.ediam (t n i))
        ≤ ∑ _i : ι n, g (r n) := Finset.sum_le_sum fun i _ => hg (htn i)
      _ = ((Fintype.card (ι n) : ℕ) : ℝ≥0∞) * g (r n) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  exact le_trans hmain (Filter.liminf_le_liminf hle (by isBoundedDefault) (by isBoundedDefault))

theorem mkMetric_polyAlphabetClass_le_liminf (P : PolyRecData) (D : Finset ℤ)
    (hD : 1 ≤ D.card) (N : ℕ) (m₀ m₁ : ℤ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g) :
    Measure.mkMetric g (polyAlphabetClass P D N m₀ m₁) ≤
      liminf (polyNormalizedGaugeCost P (D.card : ℝ) g) atTop := by
  let ι : ℕ → Type := fun n => (polyPairTreeA P D N m₀ m₁ (n - N) : Set (ℤ × ℤ))
  have hr0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (P.Q n : ℝ))) atTop (nhds 0) := by
    have hreal : Tendsto (fun n : ℕ => 1 / (P.Q n : ℝ)) atTop (nhds 0) :=
      P.poly_Q_tendsto_atTop.const_div_atTop 1
    simpa using ENNReal.tendsto_ofReal hreal
  have ht : ∀ᶠ n in atTop, ∀ i : ι n,
      Metric.ediam (polyGaugeInterv P n i.1.1) ≤ ENNReal.ofReal (1 / (P.Q n : ℝ)) :=
    Filter.Eventually.of_forall fun n i => ediam_polyGaugeInterv_le P n i.1.1
  have hst : ∀ᶠ n in atTop, polyAlphabetClass P D N m₀ m₁ ⊆
      ⋃ i : ι n, polyGaugeInterv P n i.1.1 := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hadd : N + (n - N) = n := Nat.add_sub_of_le hn
    have hcov := polyAlphabetClass_subset_cover P D N m₀ m₁ (n - N)
    rwa [hadd] at hcov
  have hmain := mkMetric_le_liminf_of_seq_cover (polyAlphabetClass P D N m₀ m₁)
    (fun n => ENNReal.ofReal (1 / (P.Q n : ℝ))) hr0
    (fun n (i : ι n) => polyGaugeInterv P n i.1.1) ht hst g hg
  have hcost_le : ∀ᶠ n in atTop,
      ((Fintype.card (ι n) : ℕ) : ℝ≥0∞) * g (ENNReal.ofReal (1 / (P.Q n : ℝ))) ≤
        polyNormalizedGaugeCost P (D.card : ℝ) g n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcard : Fintype.card (ι n) = (polyPairTreeA P D N m₀ m₁ (n - N)).card := by
      simp [ι]
    have hpow_nat : (polyPairTreeA P D N m₀ m₁ (n - N)).card ≤ D.card ^ n :=
      le_trans (card_polyPairTreeA_le P D N m₀ m₁ (n - N))
        (Nat.pow_le_pow_right hD (Nat.sub_le n N))
    have hpow_enn : ((Fintype.card (ι n) : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal ((D.card : ℝ) ^ n) := by
      rw [hcard, ← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      exact_mod_cast hpow_nat
    exact mul_le_mul_of_nonneg_right hpow_enn bot_le
  exact le_trans hmain (Filter.liminf_le_liminf hcost_le (by isBoundedDefault) (by isBoundedDefault))

lemma eventually_abs_defect_le_of_apprExponent_le_div_c (P : PolyRecData) (r : ℕ)
    {x : ℝ} (hx : P.polyApprExponent x ≤ ENNReal.ofReal ((r : ℝ) / (P.c : ℝ))) :
    ∀ᶠ j : ℕ in atTop, |P.polyDefect x j| ≤ (r : ℤ) := by
  have hc_pos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
  have hne : P.polyApprExponent x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  have hu := P.polyEps_tendsto_zero_of_apprExponent_ne_top hne
  have happrox := P.poly_abs_defect_approx x hu
  have hlt_exp : P.polyApprExponent x < ENNReal.ofReal (((r : ℝ) + 1 / 2) / (P.c : ℝ)) := by
    refine lt_of_le_of_lt hx (ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr ?_)
    exact div_lt_div_of_pos_right (by linarith) hc_pos
  have hev_seq : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (P.polyWeightedSeq (P.r : ℝ) x j) <
        ENNReal.ofReal (((r : ℝ) + 1 / 2) / (P.c : ℝ)) :=
    eventually_lt_of_limsup_lt hlt_exp
  have hev_err : ∀ᶠ j : ℕ in atTop,
      |(P.polyDefect x j : ℝ)| -
        (P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x) < 1 / 4 := by
    have hball := happrox.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 4))
    filter_upwards [hball] with j hj
    rw [Real.dist_eq, sub_zero, abs_lt] at hj
    exact hj.2
  filter_upwards [hev_seq, hev_err] with j hj_seq hj_err
  have hreal : P.polyWeightedSeq (P.r : ℝ) x j < ((r : ℝ) + 1 / 2) / (P.c : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hj_seq
  have hcmul : (P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x) <
      (r : ℝ) + 1 / 2 := by
    have hmul := mul_lt_mul_of_pos_left hreal hc_pos
    have hrhs : (P.c : ℝ) * (((r : ℝ) + 1 / 2) / (P.c : ℝ)) = (r : ℝ) + 1 / 2 := by field_simp
    have hlhs : (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j =
        (P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x) := by
      dsimp [PolyRecData.polyWeightedSeq]
      rw [Real.rpow_natCast]
      ring
    linarith
  have habs_lt : ((|P.polyDefect x j| : ℤ) : ℝ) < (r : ℝ) + 3 / 4 := by
    rw [Int.cast_abs]; linarith
  have hZ_lt : |P.polyDefect x j| < (r : ℤ) + 1 := by
    have hR : ((|P.polyDefect x j| : ℤ) : ℝ) < (((r : ℤ) + 1 : ℤ) : ℝ) := by
      push_cast; linarith
    exact Int.cast_lt.mp hR
  omega

lemma levelSet_div_c_subset_iUnion_polyAlphabetClass (P : PolyRecData) (r : ℕ) :
    {x : ℝ | P.polyApprExponent x ≤ ENNReal.ofReal ((r : ℝ) / (P.c : ℝ))} ⊆
      ⋃ p : ℕ × ℤ × ℤ,
        polyAlphabetClass P (Finset.Icc (-(r : ℤ)) (r : ℤ)) (P.J₀ + p.1) p.2.1 p.2.2 := by
  intro x hx
  have hev := eventually_abs_defect_le_of_apprExponent_le_div_c P r hx
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  set kN := max P.J₀ N0 - P.J₀
  have hJN : P.J₀ + kN = max P.J₀ N0 := Nat.add_sub_of_le (le_max_left P.J₀ N0)
  refine Set.mem_iUnion.mpr ⟨(kN, round ((P.Q (P.J₀ + kN) : ℝ) * x),
    round ((P.Q (P.J₀ + kN + 1) : ℝ) * x)), rfl, rfl, fun j hj => ?_⟩
  have hj' : P.J₀ + kN ≤ j := hj
  have hle := hN0 (j + 1) (by omega)
  exact Finset.mem_Icc.mpr (abs_le.mp hle)

lemma strictLevel_subset_iUnion_polyAlphabetClass (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    polyStrictLevel P k ⊆
      ⋃ p : ℕ × ℤ × ℤ,
        polyAlphabetClass P (Finset.Icc (-((k - 1 : ℕ) : ℤ)) ((k - 1 : ℕ) : ℤ))
          (P.J₀ + p.1) p.2.1 p.2.2 := by
  intro x hx
  dsimp [polyStrictLevel] at hx
  have hle : P.polyApprExponent x ≤ ENNReal.ofReal (((k - 1 : ℕ) : ℝ) / (P.c : ℝ)) := by
    have hne : P.polyApprExponent x ≠ ⊤ :=
      ne_top_of_lt (lt_of_lt_of_le hx (by exact le_of_lt ENNReal.ofReal_lt_top))
    have hmem : P.polyApprExponent x ∈ Set.range P.polyApprExponent := ⟨x, rfl⟩
    rw [P.poly_range_apprExponent] at hmem
    rcases hmem with ⟨m, hm⟩ | htop
    · have hm_lt : m < k := by
        rw [hm] at hx
        have hc_pos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
        have hR : (m : ℝ) / (P.c : ℝ) < (k : ℝ) / (P.c : ℝ) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hx
        have hmk : (m : ℝ) < (k : ℝ) := (div_lt_div_iff_of_pos_right hc_pos).mp hR
        exact Nat.cast_lt.mp hmk
      rw [hm]
      apply ENNReal.ofReal_le_ofReal
      have hc_pos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
      exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : m ≤ k - 1)) hc_pos.le
    · exact absurd htop hne
  exact levelSet_div_c_subset_iUnion_polyAlphabetClass P (k - 1) hle

lemma unsignedExactLimit_subset_iUnion_polyAlphabetClass (P : PolyRecData) (k : ℕ) :
    polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ⊆
      ⋃ p : ℕ × ℤ × ℤ,
        polyAlphabetClass P {-(k : ℤ), (k : ℤ)} (P.J₀ + p.1) p.2.1 p.2.2 := by
  intro x hx
  have hbin := ((poly_unsigned_exact_limit_iff_defect_binary P x k).mp hx).2
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hbin
  set kN := max P.J₀ N0 - P.J₀
  have hJN : P.J₀ + kN = max P.J₀ N0 := Nat.add_sub_of_le (le_max_left P.J₀ N0)
  refine Set.mem_iUnion.mpr ⟨(kN, round ((P.Q (P.J₀ + kN) : ℝ) * x),
    round ((P.Q (P.J₀ + kN + 1) : ℝ) * x)), rfl, rfl, fun j hj => ?_⟩
  have hj' : P.J₀ + kN ≤ j := hj
  rcases hN0 (j + 1) (by omega) with hpos | hneg
  · simp [hpos]
  · simp [hneg]

private lemma card_Icc_symm (r : ℕ) :
    (Finset.Icc (-(r : ℤ)) (r : ℤ)).card = 2 * r + 1 := by
  rw [Int.card_Icc]
  omega

/-- 小底数归一化规范代价自动归零：`b₁ < b₂` 且 `liminf (b₂^n g(1/Q_n)) < ⊤` 蕴涵 `liminf (b₁^n g(1/Q_n)) = 0`。 -/
lemma poly_liminf_normalizedGaugeCost_zero_of_smaller_base (P : PolyRecData)
    {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (hb₁₂ : b₁ < b₂)
    (g : ℝ≥0∞ → ℝ≥0∞)
    (hfin : liminf (polyNormalizedGaugeCost P b₂ g) atTop < ⊤) :
    liminf (polyNormalizedGaugeCost P b₁ g) atTop = 0 := by
  have hb₂ : 0 < b₂ := lt_of_le_of_lt hb₁ hb₁₂
  have hratio_nn : 0 ≤ b₁ / b₂ := div_nonneg hb₁ hb₂.le
  have hratio_lt : b₁ / b₂ < 1 := (div_lt_one hb₂).mpr hb₁₂
  have hpow0 : Tendsto (fun n : ℕ => (b₁ / b₂) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nn hratio_lt
  set L := liminf (polyNormalizedGaugeCost P b₂ g) atTop
  set C : ℝ := L.toReal + 1
  have hC_pos : 0 < C := by positivity
  have hL_lt : L < ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hfin.ne]
    exact ENNReal.ofReal_lt_ofReal_iff hC_pos |>.mpr (by linarith)
  have hfreq : ∃ᶠ n : ℕ in atTop,
      polyNormalizedGaugeCost P b₂ g n < ENNReal.ofReal C :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hL_lt
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  have hε_pos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hev_pow : ∀ᶠ n : ℕ in atTop, (b₁ / b₂) ^ n < (ε : ℝ) / C :=
    hpow0.eventually (Iio_mem_nhds (div_pos hε_pos hC_pos))
  have hfreq_small : ∃ᶠ n : ℕ in atTop,
      polyNormalizedGaugeCost P b₁ g n ≤ (ε : ℝ≥0∞) := by
    refine (hfreq.and_eventually hev_pow).mono fun n ⟨hn_cost, hn_pow⟩ => ?_
    have hsplit : b₁ ^ n = (b₁ / b₂) ^ n * b₂ ^ n := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hb₂.ne')]
    calc polyNormalizedGaugeCost P b₁ g n
        = ENNReal.ofReal ((b₁ / b₂) ^ n) * polyNormalizedGaugeCost P b₂ g n := by
          unfold polyNormalizedGaugeCost
          rw [hsplit, ENNReal.ofReal_mul (pow_nonneg hratio_nn n), mul_assoc]
      _ ≤ ENNReal.ofReal ((ε : ℝ) / C) * ENNReal.ofReal C := by
          gcongr
      _ = (ε : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_mul (div_pos hε_pos hC_pos).le, div_mul_cancel₀ _ hC_pos.ne',
            ENNReal.ofReal_coe_nnreal]
  exact Filter.liminf_le_of_frequently_le' hfreq_small

/-- `polyInterpGauge P b` 的 `liminf` 归一化代价（当底数为 `b > 1`）有界为 `1 < ⊤`。 -/
lemma poly_liminf_normalizedGaugeCost_interp_le_one (P : PolyRecData)
    {b : ℝ} (hb : 1 < b) :
    liminf (polyNormalizedGaugeCost P b (polyInterpGauge P b)) atTop ≤ 1 := by
  have hev : ∀ᶠ n : ℕ in atTop,
      polyNormalizedGaugeCost P b (polyInterpGauge P b) n = 1 := by
    filter_upwards [eventually_ge_atTop P.J₀] with n hn
    unfold polyNormalizedGaugeCost
    rw [polyInterpGauge_at_inv_Q P hb hn]
    have hb_pos : 0 < b := lt_trans zero_lt_one hb
    rw [← ENNReal.ofReal_mul (pow_nonneg hb_pos.le n), zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (pow_ne_zero n hb_pos.ne'), ENNReal.ofReal_one]
  exact le_of_eq (Filter.liminf_congr hev |>.trans (Filter.liminf_const 1))

/-- 多项式递推严格子水平集 `{Λ < k/c}` 在一切 `liminf (2k+1)^n g(1/Q_n) < ⊤` 的规范下零测度。 -/
theorem mkMetric_polyStrictLevel_null_of_liminf_lt_top (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hlim : liminf (polyNormalizedGaugeCost P (2 * (k : ℝ) + 1) g) atTop < ⊤) :
    Measure.mkMetric g (polyStrictLevel P k) = 0 := by
  have hsub := strictLevel_subset_iUnion_polyAlphabetClass P hk
  apply measure_mono_null hsub
  apply measure_iUnion_null
  intro p
  set D := Finset.Icc (-((k - 1 : ℕ) : ℤ)) ((k - 1 : ℕ) : ℤ)
  have hD_card : D.card = 2 * (k - 1) + 1 := card_Icc_symm (k - 1)
  have hD_pos : 1 ≤ D.card := by omega
  have hD_lt : (D.card : ℝ) < 2 * (k : ℝ) + 1 := by
    rw [hD_card]
    have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by simpa using Nat.cast_sub hk
    push_cast; rw [hk1]; linarith
  have hle := mkMetric_polyAlphabetClass_le_liminf P D hD_pos (P.J₀ + p.1) p.2.1 p.2.2 g hg
  have hzero := poly_liminf_normalizedGaugeCost_zero_of_smaller_base P
    (Nat.cast_nonneg D.card) hD_lt g hlim
  exact le_antisymm (hle.trans_eq hzero) bot_le

/-- **`thm:poly-gauge-trichotomy`(i) 严格子水平集零测度**：
    $\mathcal{H}^{h_k}(\{x \in \mathbb{R} : \Lambda^{(r,c,d)}(x) < k/c\}) = 0$（对一切 $k \ge 1$）。 -/
theorem mkMetric_polyCritGauge_polyStrictLevel_null (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (polyCritGauge P k) (polyStrictLevel P k) = 0 := by
  apply mkMetric_polyStrictLevel_null_of_liminf_lt_top P hk _ (polyCritGauge_mono P k hk)
  exact lt_of_le_of_lt
    (poly_liminf_normalizedGaugeCost_interp_le_one P (GaugeCircle.critGauge_base_gt_one k hk))
    ENNReal.one_lt_top

/-- 非严格子水平集 `{Λ ≤ k/c}` 在 `liminf (2k+1)^n g(1/Q_n) = 0` 下零测度（含 `k = 0`）。 -/
theorem mkMetric_polyLevelSet_null_of_liminf_zero (P : PolyRecData) (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hzero : liminf (polyNormalizedGaugeCost P (2 * (k : ℝ) + 1) g) atTop = 0) :
    Measure.mkMetric g {x : ℝ | P.polyApprExponent x ≤ ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))} = 0 := by
  apply measure_mono_null (levelSet_div_c_subset_iUnion_polyAlphabetClass P k)
  apply measure_iUnion_null
  intro p
  set D := Finset.Icc (-(k : ℤ)) (k : ℤ)
  have hD_card : D.card = 2 * k + 1 := card_Icc_symm k
  have hD_pos : 1 ≤ D.card := by omega
  have hD_eq : (D.card : ℝ) = 2 * (k : ℝ) + 1 := by rw [hD_card]; push_cast; ring
  have hle := mkMetric_polyAlphabetClass_le_liminf P D hD_pos (P.J₀ + p.1) p.2.1 p.2.2 g hg
  rw [hD_eq] at hle
  exact le_antisymm (hle.trans_eq hzero) bot_le

/-- 非严格子水平集在 `liminf (2k+1)^n g(1/Q_n) < ⊤` 下的 $\sigma$-有限可数分解。 -/
theorem polyLevelSet_sigma_finite_of_liminf_lt_top (P : PolyRecData) (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hfin : liminf (polyNormalizedGaugeCost P (2 * (k : ℝ) + 1) g) atTop < ⊤) :
    ∃ E : ℕ → Set ℝ,
      {x : ℝ | P.polyApprExponent x ≤ ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))} ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  classical
  let e : ℕ ≃ (ℕ × ℤ × ℤ) := (Denumerable.eqv _).symm
  refine ⟨fun i => polyAlphabetClass P (Finset.Icc (-(k : ℤ)) (k : ℤ))
      (P.J₀ + (e i).1) (e i).2.1 (e i).2.2, ?_, fun i => ?_⟩
  · intro x hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (levelSet_div_c_subset_iUnion_polyAlphabetClass P k hx)
    refine Set.mem_iUnion.mpr ⟨e.symm p, ?_⟩
    simpa [e.apply_symm_apply] using hp
  · set D := Finset.Icc (-(k : ℤ)) (k : ℤ)
    have hD_card : D.card = 2 * k + 1 := card_Icc_symm k
    have hD_pos : 1 ≤ D.card := by omega
    have hD_eq : (D.card : ℝ) = 2 * (k : ℝ) + 1 := by rw [hD_card]; push_cast; ring
    have hle := mkMetric_polyAlphabetClass_le_liminf P D hD_pos (P.J₀ + (e i).1) (e i).2.1 (e i).2.2 g hg
    rw [hD_eq] at hle
    exact lt_of_le_of_lt hle hfin

/-- 精确水平集 $S_k$ 在临界规范 `polyCritGauge P k` 下的 $\sigma$-有限可数覆盖。 -/
theorem polyExactLevel_critGauge_sigma_finite (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    ∃ E : ℕ → Set ℝ, polyExactLevel P k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (polyCritGauge P k) (E i) < ⊤ := by
  obtain ⟨E, hcov, hfin⟩ := polyLevelSet_sigma_finite_of_liminf_lt_top P k (polyCritGauge P k)
    (polyCritGauge_mono P k hk)
    (lt_of_le_of_lt
      (poly_liminf_normalizedGaugeCost_interp_le_one P (GaugeCircle.critGauge_base_gt_one k hk))
      ENNReal.one_lt_top)
  exact ⟨E, Set.Subset.trans (fun _ hx => le_of_eq hx) hcov, hfin⟩

/-- 无符号精确极限集 $E_{\mathrm{lim}}^{(r,c,d)}(k/c)$ 在 `liminf (2^n g(1/Q_n)) = 0` 下零测度。 -/
theorem mkMetric_polyUnsignedExactLimit_null_of_liminf_zero (P : PolyRecData) (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hzero : liminf (polyNormalizedGaugeCost P 2 g) atTop = 0) :
    Measure.mkMetric g (polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ))) = 0 := by
  apply measure_mono_null (unsignedExactLimit_subset_iUnion_polyAlphabetClass P k)
  apply measure_iUnion_null
  intro p
  set D : Finset ℤ := {-(k : ℤ), (k : ℤ)}
  have hD_pos : 1 ≤ D.card := Finset.card_pos.mpr ⟨-(k : ℤ), by simp [D]⟩
  have hD_le2 : (D.card : ℝ) ≤ 2 := by
    have h1 : D.card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    exact_mod_cast h1
  have hle := mkMetric_polyAlphabetClass_le_liminf P D hD_pos (P.J₀ + p.1) p.2.1 p.2.2 g hg
  have hcost_le : ∀ n : ℕ, polyNormalizedGaugeCost P (D.card : ℝ) g n ≤
      polyNormalizedGaugeCost P 2 g n := fun n => by
    unfold polyNormalizedGaugeCost
    gcongr
  have h0 : liminf (polyNormalizedGaugeCost P (D.card : ℝ) g) atTop = 0 := by
    refine le_antisymm ?_ bot_le
    calc liminf (polyNormalizedGaugeCost P (D.card : ℝ) g) atTop
        ≤ liminf (polyNormalizedGaugeCost P 2 g) atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hcost_le)
            (by isBoundedDefault) (by isBoundedDefault)
      _ = 0 := hzero
  exact le_antisymm (hle.trans_eq h0) bot_le

/-- 无符号精确极限集在 `polyCritGauge P k` 下测度为 `0`（因为 `2 < 2k + 1` 对一切 `k ≥ 1`）。 -/
theorem mkMetric_polyUnsignedExactLimit_null_of_critGauge (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (polyCritGauge P k) (polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ))) = 0 := by
  apply mkMetric_polyUnsignedExactLimit_null_of_liminf_zero P k _ (polyCritGauge_mono P k hk)
  have h2lt : (2 : ℝ) < 2 * (k : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  apply poly_liminf_normalizedGaugeCost_zero_of_smaller_base P (by norm_num) h2lt (polyCritGauge P k)
  exact lt_of_le_of_lt
    (poly_liminf_normalizedGaugeCost_interp_le_one P (GaugeCircle.critGauge_base_gt_one k hk))
    ENNReal.one_lt_top

/-- 无符号精确极限集在 `liminf (2^n g(1/Q_n)) < ⊤` 下的 $\sigma$-有限可数覆盖（特别是普适规范 $g_2$）。 -/
theorem polyUnsignedExactLimit_sigma_finite_of_liminf_lt_top (P : PolyRecData) (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hfin : liminf (polyNormalizedGaugeCost P 2 g) atTop < ⊤) :
    ∃ E : ℕ → Set ℝ,
      polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  classical
  let e : ℕ ≃ (ℕ × ℤ × ℤ) := (Denumerable.eqv _).symm
  refine ⟨fun i => polyAlphabetClass P {-(k : ℤ), (k : ℤ)}
      (P.J₀ + (e i).1) (e i).2.1 (e i).2.2, ?_, fun i => ?_⟩
  · intro x hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (unsignedExactLimit_subset_iUnion_polyAlphabetClass P k hx)
    refine Set.mem_iUnion.mpr ⟨e.symm p, ?_⟩
    simpa [e.apply_symm_apply] using hp
  · set D : Finset ℤ := {-(k : ℤ), (k : ℤ)}
    have hD_pos : 1 ≤ D.card := Finset.card_pos.mpr ⟨-(k : ℤ), by simp [D]⟩
    have hD_le2 : (D.card : ℝ) ≤ 2 := by
      have h1 : D.card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
      exact_mod_cast h1
    have hle := mkMetric_polyAlphabetClass_le_liminf P D hD_pos (P.J₀ + (e i).1) (e i).2.1 (e i).2.2 g hg
    have hcost_le : ∀ n : ℕ, polyNormalizedGaugeCost P (D.card : ℝ) g n ≤
        polyNormalizedGaugeCost P 2 g n := fun n => by
      unfold polyNormalizedGaugeCost
      gcongr
    have hlim_le := Filter.liminf_le_liminf
      (show ∀ᶠ n : ℕ in atTop, polyNormalizedGaugeCost P (D.card : ℝ) g n ≤
        polyNormalizedGaugeCost P 2 g n from Filter.Eventually.of_forall hcost_le)
      (by isBoundedDefault) (by isBoundedDefault)
    exact lt_of_le_of_lt (le_trans hle hlim_le) hfin

theorem polyUnsignedExactLimit_binaryGauge_sigma_finite (P : PolyRecData) (k : ℕ) :
    ∃ E : ℕ → Set ℝ, polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (polyBinaryGauge P) (E i) < ⊤ :=
  polyUnsignedExactLimit_sigma_finite_of_liminf_lt_top P k (polyBinaryGauge P)
    (polyBinaryGauge_mono P)
    (lt_of_le_of_lt (poly_liminf_normalizedGaugeCost_interp_le_one P (by norm_num)) ENNReal.one_lt_top)

/-- 规范对比引理（正下极限 `0 < liminf (b^n g(1/Q_n))` 蕴涵小尺度 `polyInterpGauge P b ≤ C * g`）。 -/
lemma exists_polyInterpGauge_le_mul_of_liminf_pos (P : PolyRecData) {b : ℝ} (hb : 1 < b)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hpos : 0 < liminf (polyNormalizedGaugeCost P b g) atTop) :
    ∃ (c : ℝ≥0) (δ : ℝ≥0∞), 0 < c ∧ 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → polyInterpGauge P b r ≤ (c : ℝ≥0∞) * g r := by
  have hb_pos : 0 < b := lt_trans zero_lt_one hb
  set L : ℝ≥0∞ := min 1 (liminf (polyNormalizedGaugeCost P b g) atTop) / 2
  have hL_pos : 0 < L :=
    ENNReal.div_pos (lt_min one_pos hpos).ne' (by norm_num)
  have hL_lt : L < liminf (polyNormalizedGaugeCost P b g) atTop := by
    have h1 : min 1 (liminf (polyNormalizedGaugeCost P b g) atTop) ≤
        liminf (polyNormalizedGaugeCost P b g) atTop := min_le_right _ _
    have hhalf : min 1 (liminf (polyNormalizedGaugeCost P b g) atTop) / 2 <
        min 1 (liminf (polyNormalizedGaugeCost P b g) atTop) :=
      ENNReal.half_lt_self (lt_min one_pos hpos).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _))
    exact lt_of_lt_of_le hhalf h1
  have hL_ne_top : L ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_trans (ENNReal.div_le_of_le_mul (by exact le_mul_of_one_le_right bot_le (by norm_num)))
        (min_le_left _ _))
  have hev : ∀ᶠ n : ℕ in atTop, L < polyNormalizedGaugeCost P b g n :=
    Filter.eventually_lt_of_lt_liminf hL_lt
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  set N := max P.J₀ N0
  have hNJ₀ : P.J₀ ≤ N := le_max_left _ _
  have hNN0 : N0 ≤ N := le_max_right _ _
  set η : ℝ := L.toReal
  have hη_pos : 0 < η := ENNReal.toReal_pos hL_pos.ne' hL_ne_top
  have hη_le : ENNReal.ofReal η ≤ L := by rw [ENNReal.ofReal_toReal hL_ne_top]
  set c0 : ℝ≥0 := ⟨b / η, by positivity⟩
  have hc0_pos : 0 < c0 := by change 0 < b / η; positivity
  refine ⟨c0, ENNReal.ofReal (polyInvQ P (N + 1)), hc0_pos,
    ENNReal.ofReal_pos.mpr (polyInvQ_pos P (N + 1)), fun r hr => ?_⟩
  by_cases hr0 : r = 0
  · subst hr0; simp [polyInterpGauge_zero]
  have hr_lt_top : r < ⊤ := lt_of_le_of_lt hr ENNReal.ofReal_lt_top
  have hr_ne_top : r ≠ ⊤ := ne_of_lt hr_lt_top
  have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos hr0 hr_ne_top
  have hr_real_le : r.toReal ≤ polyInvQ P (N + 1) := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
    rwa [ENNReal.toReal_ofReal (le_of_lt (polyInvQ_pos P (N + 1)))] at h1
  have hr_lt_N : r.toReal < polyInvQ P N :=
    lt_of_le_of_lt hr_real_le (polyInvQ_succ_lt P hNJ₀)
  have hr_lt_J₀ : r.toReal < polyInvQ P P.J₀ :=
    lt_of_lt_of_le hr_lt_N (polyInvQ_le_J₀ P hNJ₀)
  set n := polyInterpIdx P r.toReal
  obtain ⟨hnJ₀, hnlo, hnhi⟩ := polyInterpIdx_spec P hr_real_pos hr_lt_J₀
  have hN_le_n : N ≤ n := by
    by_contra hlt
    push Not at hlt
    have hle : n + 1 ≤ N := by omega
    have hq : polyInvQ P N ≤ polyInvQ P (n + 1) :=
      polyInvQ_antitoneOn P (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hNJ₀) hle
    linarith
  have hn1_ge_N0 : N0 ≤ n + 1 := by omega
  have hcost_n1 : ENNReal.ofReal η < polyNormalizedGaugeCost P b g (n + 1) :=
    lt_of_le_of_lt hη_le (hN0 (n + 1) hn1_ge_N0)
  have hb_inv_le : ENNReal.ofReal (b ^ (-(n : ℤ))) ≤
      (c0 : ℝ≥0∞) * g (ENNReal.ofReal (polyInvQ P (n + 1))) := by
    have hc_eq : (c0 : ℝ≥0∞) * ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ)) * η) =
        ENNReal.ofReal (b ^ (-(n : ℤ))) := by
      have hc0R : ((c0 : ℝ≥0∞)) = ENNReal.ofReal (b / η) := by
        rw [← ENNReal.ofReal_coe_nnreal]; rfl
      rw [hc0R, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ]
      field_simp
    have hmult : ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal η ≤
        g (ENNReal.ofReal (polyInvQ P (n + 1))) := by
      have hmul := mul_le_mul_of_nonneg_left hcost_n1.le
        (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))))
      unfold polyNormalizedGaugeCost at hmul
      have hid : ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal (b ^ (n + 1)) = 1 := by
        rw [← ENNReal.ofReal_mul (by positivity), zpow_neg, zpow_natCast,
          inv_mul_cancel₀ (pow_ne_zero (n + 1) hb_pos.ne'), ENNReal.ofReal_one]
      rw [← mul_assoc, hid, one_mul] at hmul
      simpa [polyInvQ] using hmul
    calc ENNReal.ofReal (b ^ (-(n : ℤ)))
        = (c0 : ℝ≥0∞) * (ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal η) := by
          rw [← hc_eq, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ (c0 : ℝ≥0∞) * g (ENNReal.ofReal (polyInvQ P (n + 1))) := by gcongr
  have hr_eq : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hr_ne_top
  calc polyInterpGauge P b r
      = ENNReal.ofReal (polyInterpGaugeReal P b r.toReal) :=
        polyInterpGauge_eq_ofReal_toReal P hb hr_ne_top
    _ ≤ ENNReal.ofReal (b ^ (-(n : ℤ))) := by
        apply ENNReal.ofReal_le_ofReal
        calc polyInterpGaugeReal P b r.toReal
            ≤ polyInterpGaugeReal P b (polyInvQ P n) := polyInterpGaugeReal_mono P hb hnhi.le
          _ = b ^ (-(n : ℤ)) := polyInterpGaugeReal_at_invQ P hb hnJ₀
    _ ≤ (c0 : ℝ≥0∞) * g (ENNReal.ofReal (polyInvQ P (n + 1))) := hb_inv_le
    _ ≤ (c0 : ℝ≥0∞) * g r := by
        gcongr
        exact hg (by rw [← hr_eq]; exact ENNReal.ofReal_le_ofReal hnlo)

/-- 若 `liminf (b^n g(1/Q_n)) = ⊤`，则 `polyInterpGauge P b r / g r → 0`（用于强非 $\sigma$-有限性）。 -/
lemma polyInterpGauge_ratio_tendsto_zero_of_liminf_top (P : PolyRecData) {b : ℝ} (hb : 1 < b)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (htop : liminf (polyNormalizedGaugeCost P b g) atTop = ⊤) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → polyInterpGauge P b r ≤ (ε : ℝ≥0∞) * g r := by
  intro ε hε
  have hb_pos : 0 < b := lt_trans zero_lt_one hb
  have hεR : (0 : ℝ) < (ε : ℝ) := hε
  set M : ℝ := b / (ε : ℝ)
  have hev : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal M < polyNormalizedGaugeCost P b g n :=
    Filter.eventually_lt_of_lt_liminf (by rw [htop]; exact ENNReal.ofReal_lt_top)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  set N := max P.J₀ N0
  have hNJ₀ : P.J₀ ≤ N := le_max_left _ _
  refine ⟨ENNReal.ofReal (polyInvQ P (N + 1)),
    ENNReal.ofReal_pos.mpr (polyInvQ_pos P (N + 1)), fun r hr => ?_⟩
  by_cases hr0 : r = 0
  · subst hr0; simp [polyInterpGauge_zero]
  have hr_lt_top : r < ⊤ := lt_of_le_of_lt hr ENNReal.ofReal_lt_top
  have hr_ne_top : r ≠ ⊤ := ne_of_lt hr_lt_top
  have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos hr0 hr_ne_top
  have hr_real_le : r.toReal ≤ polyInvQ P (N + 1) := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
    rwa [ENNReal.toReal_ofReal (le_of_lt (polyInvQ_pos P (N + 1)))] at h1
  have hr_lt_N : r.toReal < polyInvQ P N :=
    lt_of_le_of_lt hr_real_le (polyInvQ_succ_lt P hNJ₀)
  have hr_lt_J₀ : r.toReal < polyInvQ P P.J₀ :=
    lt_of_lt_of_le hr_lt_N (polyInvQ_le_J₀ P hNJ₀)
  set n := polyInterpIdx P r.toReal
  obtain ⟨hnJ₀, hnlo, hnhi⟩ := polyInterpIdx_spec P hr_real_pos hr_lt_J₀
  have hN_le_n : N ≤ n := by
    by_contra hlt
    push Not at hlt
    have hle : n + 1 ≤ N := by omega
    have hq : polyInvQ P N ≤ polyInvQ P (n + 1) :=
      polyInvQ_antitoneOn P (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hNJ₀) hle
    linarith
  have hcost : ENNReal.ofReal M < polyNormalizedGaugeCost P b g (n + 1) :=
    hN0 (n + 1) (by omega)
  have hmult : ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal M ≤
      g (ENNReal.ofReal (polyInvQ P (n + 1))) := by
    have hmul := mul_le_mul_of_nonneg_left hcost.le
      (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))))
    unfold polyNormalizedGaugeCost at hmul
    have hid : ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal (b ^ (n + 1)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero (n + 1) hb_pos.ne'), ENNReal.ofReal_one]
    rw [← mul_assoc, hid, one_mul] at hmul
    simpa [polyInvQ] using hmul
  have hid2 : (ε : ℝ≥0∞) * (ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal M) =
      ENNReal.ofReal (b ^ (-(n : ℤ))) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [M]
    rw [zpow_neg, zpow_neg]
    norm_cast
    rw [pow_succ]
    field_simp
  have hr_eq : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hr_ne_top
  calc polyInterpGauge P b r
      = ENNReal.ofReal (polyInterpGaugeReal P b r.toReal) :=
        polyInterpGauge_eq_ofReal_toReal P hb hr_ne_top
    _ ≤ ENNReal.ofReal (b ^ (-(n : ℤ))) := by
        apply ENNReal.ofReal_le_ofReal
        calc polyInterpGaugeReal P b r.toReal
            ≤ polyInterpGaugeReal P b (polyInvQ P n) := polyInterpGaugeReal_mono P hb hnhi.le
          _ = b ^ (-(n : ℤ)) := polyInterpGaugeReal_at_invQ P hb hnJ₀
    _ = (ε : ℝ≥0∞) * (ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal M) := hid2.symm
    _ ≤ (ε : ℝ≥0∞) * g (ENNReal.ofReal (polyInvQ P (n + 1))) := by gcongr
    _ ≤ (ε : ℝ≥0∞) * g r := by
        gcongr
        exact hg (by rw [← hr_eq]; exact ENNReal.ofReal_le_ofReal hnlo)


/-! ## 第五部分：参数化 `b`-叉 Cantor 树、`thm:poly-gauge-trichotomy(i),(ii)`、`cor:poly-exact-gauge` 与 `cor:poly-liminf-gauges` -/

/-- 参数化编码字母表（同时实例 `(2k+1)`-叉精确水平树与 `2`-叉无符号极限树）。 -/
structure PolyDigitCode (k : ℕ) where
  b : ℕ
  hb : 1 ≤ b
  digit : Fin b → ℤ
  abs_le : ∀ a, |digit a| ≤ (k : ℤ)
  inj : Function.Injective digit

def PolyDigitCode.exact (k : ℕ) : PolyDigitCode k where
  b := 2 * k + 1
  hb := by omega
  digit := GaugeExact.digitOf k
  abs_le := GaugeExact.abs_digitOf_le k
  inj := GaugeExact.digitOf_injective k

def PolyDigitCode.binary (k : ℕ) (hk : 1 ≤ k) : PolyDigitCode k where
  b := 2
  hb := by norm_num
  digit := GaugeCircle.binDigitOf k
  abs_le := GaugeCircle.abs_binDigitOf_le k
  inj := GaugeCircle.binDigitOf_injective k hk

/-- 统一 Cantor 树起始下标：$J := \max(P.J_1,\, \max(P.N_{\mathrm{witness}}(k),\, 18))$。 -/
def polyTreeJ (P : PolyRecData) (k : ℕ) : ℕ :=
  max P.J₁ (max (P.N_witness k) 18)

lemma polyTreeJ_ge_J₁ (P : PolyRecData) (k : ℕ) : P.J₁ ≤ polyTreeJ P k := le_max_left _ _
lemma polyTreeJ_ge_Nw (P : PolyRecData) (k : ℕ) : P.N_witness k ≤ polyTreeJ P k :=
  le_trans (le_max_left _ _) (le_max_right _ _)
lemma polyTreeJ_ge_18 (P : PolyRecData) (k : ℕ) : 18 ≤ polyTreeJ P k :=
  le_trans (le_max_right _ _) (le_max_right _ _)
lemma polyTreeJ_ge_J₀_succ (P : PolyRecData) (k : ℕ) : P.J₀ + 1 ≤ polyTreeJ P k :=
  le_trans P.J₁_ge_J₀_succ (polyTreeJ_ge_J₁ P k)

/-- 对任意 `n : ℕ`，在 `j = polyTreeJ P k + n` 处均有 `P.A (j + 1) ≥ 8 * k + 9`（同时适应 `k = 0` 与 `k ≥ 1`）。 -/
lemma polyA_ge_tree_bound (P : PolyRecData) (k m : ℕ) (hm : polyTreeJ P k + 1 ≤ m) :
    8 * (k : ℤ) + 9 ≤ P.A m := by
  by_cases hk : k = 0
  · subst hk
    have hJ₁ : P.J₁ ≤ m := le_trans (polyTreeJ_ge_J₁ P 0) (by omega)
    have h19 : 19 ≤ m := le_trans (by have := polyTreeJ_ge_18 P 0; omega) le_rfl
    have hA_R := P.poly_A_ge_half_c hJ₁
    have hc1 : (1 : ℝ) ≤ (P.c : ℝ) := by exact_mod_cast P.hc
    have hmR : (19 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h19
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by linarith
    have hm_r : (m : ℝ) ≤ (m : ℝ) ^ P.r := by
      calc (m : ℝ) = (m : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (m : ℝ) ^ P.r := pow_le_pow_right₀ hm1R P.hr
    have hA9 : (8 : ℝ) < (P.A m : ℝ) := by nlinarith
    have hZ : (8 : ℤ) < P.A m := by exact_mod_cast hA9
    omega
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hNw : P.N_witness k - 1 ≤ m := by
      have := polyTreeJ_ge_Nw P k
      omega
    have hgt := lt_of_lt_of_le (P.A_pred_N_witness_gt k) (P.A_mono hNw)
    omega

/-- 参数化 Cantor 树第 `n` 层相邻整数对 `(M_{J+n}, M_{J+n+1})`。 -/
def polyPairOfWord (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) :
    ∀ n : ℕ, (Fin n → Fin C.b) → ℤ × ℤ
  | 0, _ => (0, 0)
  | n + 1, w =>
      let p := polyPairOfWord P C n (fun i => w i.castSucc)
      (p.2, P.A (polyTreeJ P k + n + 1) * p.2 + p.1 + C.digit (w (Fin.last n)))

def polyCenterInt (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : ℤ :=
  (polyPairOfWord P C n w).2

lemma polyPairOfWord_fst_succ (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin (n + 1) → Fin C.b) :
    (polyPairOfWord P C (n + 1) w).1 =
      polyCenterInt P C n (fun i => w i.castSucc) := rfl

/-- Casorati Wronskian `W_n := M_{J+n+1} Q_{J+n} - M_{J+n} Q_{J+n+1}`。 -/
def polyWOfWord (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : ℤ :=
  (polyPairOfWord P C n w).2 * P.Q (polyTreeJ P k + n) -
    (polyPairOfWord P C n w).1 * P.Q (polyTreeJ P k + n + 1)

lemma polyWOfWord_zero (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (w : Fin 0 → Fin C.b) :
    polyWOfWord P C 0 w = 0 := by
  simp [polyWOfWord, polyPairOfWord]

lemma polyWOfWord_succ (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin (n + 1) → Fin C.b) :
    polyWOfWord P C (n + 1) w =
      -polyWOfWord P C n (fun i => w i.castSucc) +
        C.digit (w (Fin.last n)) * P.Q (polyTreeJ P k + n + 1) := by
  have hJ₀ : P.J₀ ≤ polyTreeJ P k + n + 1 := by
    have := polyTreeJ_ge_J₀_succ P k; omega
  have hQrec : P.Q (polyTreeJ P k + n + 2) =
      P.A (polyTreeJ P k + n + 1) * P.Q (polyTreeJ P k + n + 1) +
        P.Q (polyTreeJ P k + n) := by
    have h := P.hQ_rec (polyTreeJ P k + n + 1) hJ₀
    have hs1 : polyTreeJ P k + n + 1 + 1 = polyTreeJ P k + n + 2 := by omega
    have hs2 : polyTreeJ P k + n + 1 - 1 = polyTreeJ P k + n := by omega
    rw [hs1, hs2] at h
    exact h
  unfold polyWOfWord
  dsimp [polyPairOfWord]
  have hidx1 : polyTreeJ P k + (n + 1) = polyTreeJ P k + n + 1 := by omega
  have hidx3 : polyTreeJ P k + n + 1 + 1 = polyTreeJ P k + n + 2 := by omega
  rw [hidx1, hidx3, hQrec]
  ring

lemma abs_polyWOfWord_le (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) :
    |polyWOfWord P C n w| ≤ ((k : ℤ) + 1) * P.Q (polyTreeJ P k + n) := by
  induction n with
  | zero =>
      rw [polyWOfWord_zero, abs_zero]
      exact mul_nonneg (by positivity) (le_of_lt (P.hQ_pos _))
  | succ n ih =>
      rw [polyWOfWord_succ]
      set p_w := fun i : Fin n => w i.castSucc
      have ih' := ih p_w
      have hd : |C.digit (w (Fin.last n))| ≤ (k : ℤ) := C.abs_le (w (Fin.last n))
      have hQ_pos : 0 ≤ P.Q (polyTreeJ P k + n + 1) := le_of_lt (P.hQ_pos _)
      have hQ_J₀ : P.J₀ ≤ polyTreeJ P k + n := by
        have := polyTreeJ_ge_J₀_succ P k; omega
      have hQ_gt : P.A (polyTreeJ P k + n) * P.Q (polyTreeJ P k + n) <
          P.Q (polyTreeJ P k + n + 1) := P.poly_Q_succ_gt_A_mul hQ_J₀
      -- Either n = 0 (W_0 = 0) or n ≥ 1 (A ≥ 8k + 9 ≥ 2k + 2): actually for n = 0, W_0 = 0!
      by_cases hn0 : n = 0
      · subst hn0
        rw [polyWOfWord_zero, neg_zero, zero_add, abs_mul, abs_of_nonneg hQ_pos]
        have h1 : |C.digit (w (Fin.last 0))| * P.Q (polyTreeJ P k + 0 + 1) ≤
            (k : ℤ) * P.Q (polyTreeJ P k + 0 + 1) := mul_le_mul_of_nonneg_right hd hQ_pos
        nlinarith [hQ_pos]
      · have hm : polyTreeJ P k + 1 ≤ polyTreeJ P k + n := by omega
        have hA : 8 * (k : ℤ) + 9 ≤ P.A (polyTreeJ P k + n) :=
          polyA_ge_tree_bound P k (polyTreeJ P k + n) hm
        have hQ_prev_pos : 0 ≤ P.Q (polyTreeJ P k + n) := le_of_lt (P.hQ_pos _)
        have hstep_prev : ((k : ℤ) + 1) * P.Q (polyTreeJ P k + n) ≤
            P.Q (polyTreeJ P k + n + 1) := by
          have h1 : ((k : ℤ) + 1) * P.Q (polyTreeJ P k + n) ≤
              P.A (polyTreeJ P k + n) * P.Q (polyTreeJ P k + n) := by
            exact mul_le_mul_of_nonneg_right (by omega) hQ_prev_pos
          exact le_trans h1 (le_of_lt hQ_gt)
        have htri : |-polyWOfWord P C n p_w +
            C.digit (w (Fin.last n)) * P.Q (polyTreeJ P k + n + 1)| ≤
            |polyWOfWord P C n p_w| + |C.digit (w (Fin.last n))| * P.Q (polyTreeJ P k + n + 1) := by
          calc |-polyWOfWord P C n p_w +
                  C.digit (w (Fin.last n)) * P.Q (polyTreeJ P k + n + 1)|
              ≤ |-polyWOfWord P C n p_w| +
                  |C.digit (w (Fin.last n)) * P.Q (polyTreeJ P k + n + 1)| := abs_add_le _ _
            _ = |polyWOfWord P C n p_w| +
                  |C.digit (w (Fin.last n))| * P.Q (polyTreeJ P k + n + 1) := by
                  rw [abs_neg, abs_mul, abs_of_nonneg hQ_pos]
        have hsum : |polyWOfWord P C n p_w| +
            |C.digit (w (Fin.last n))| * P.Q (polyTreeJ P k + n + 1) ≤
            ((k : ℤ) + 1) * P.Q (polyTreeJ P k + (n + 1)) := by
          have hidx : polyTreeJ P k + (n + 1) = polyTreeJ P k + n + 1 := by omega
          rw [hidx]
          calc |polyWOfWord P C n p_w| + |C.digit (w (Fin.last n))| * P.Q (polyTreeJ P k + n + 1)
              ≤ ((k : ℤ) + 1) * P.Q (polyTreeJ P k + n) +
                  (k : ℤ) * P.Q (polyTreeJ P k + n + 1) := by
                  gcongr
            _ ≤ P.Q (polyTreeJ P k + n + 1) + (k : ℤ) * P.Q (polyTreeJ P k + n + 1) := by
                  gcongr
            _ = ((k : ℤ) + 1) * P.Q (polyTreeJ P k + n + 1) := by ring
        exact le_trans htri hsum

def polyCenter (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : ℝ :=
  (polyCenterInt P C n w : ℝ) / (P.Q (polyTreeJ P k + n + 1) : ℝ)

def polyRadC (P : PolyRecData) (k n : ℕ) : ℝ :=
  (2 * (k : ℝ) + 2) / (P.Q (polyTreeJ P k + n + 2) : ℝ)

lemma polyRadC_pos (P : PolyRecData) (k n : ℕ) : 0 < polyRadC P k n := by
  unfold polyRadC
  have hQ : (0 : ℝ) < (P.Q (polyTreeJ P k + n + 2) : ℝ) := by exact_mod_cast P.hQ_pos _
  positivity

lemma polyRadC_twice_lt (P : PolyRecData) (k n : ℕ) :
    2 * polyRadC P k n < (1 / 2 : ℝ) / (P.Q (polyTreeJ P k + n + 1) : ℝ) := by
  unfold polyRadC
  have hQ1 : (0 : ℝ) < (P.Q (polyTreeJ P k + n + 1) : ℝ) := by exact_mod_cast P.hQ_pos _
  have hQ2 : (0 : ℝ) < (P.Q (polyTreeJ P k + n + 2) : ℝ) := by exact_mod_cast P.hQ_pos _
  have hJ₀ : P.J₀ ≤ polyTreeJ P k + n + 1 := by
    have := polyTreeJ_ge_J₀_succ P k; omega
  have hgt : (P.A (polyTreeJ P k + n + 1) : ℝ) * (P.Q (polyTreeJ P k + n + 1) : ℝ) <
      (P.Q (polyTreeJ P k + n + 2) : ℝ) := by
    exact_mod_cast P.poly_Q_succ_gt_A_mul hJ₀
  have hA : (8 * (k : ℝ) + 9) ≤ (P.A (polyTreeJ P k + n + 1) : ℝ) := by
    exact_mod_cast polyA_ge_tree_bound P k (polyTreeJ P k + n + 1) (by omega)
  have h8k8_lt : (8 * (k : ℝ) + 8) * (P.Q (polyTreeJ P k + n + 1) : ℝ) <
      (P.Q (polyTreeJ P k + n + 2) : ℝ) := by
    nlinarith
  rw [show 2 * ((2 * (k : ℝ) + 2) / (P.Q (polyTreeJ P k + n + 2) : ℝ)) =
      (4 * (k : ℝ) + 4) / (P.Q (polyTreeJ P k + n + 2) : ℝ) by ring]
  rw [div_lt_div_iff₀ hQ2 hQ1]
  nlinarith

lemma polyCenter_step_sub_abs_le (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin (n + 1) → Fin C.b) :
    |polyCenter P C (n + 1) w - polyCenter P C n (fun i => w i.castSucc)| ≤
      ((k : ℝ) + 1) / (P.Q (polyTreeJ P k + n + 2) : ℝ) := by
  have hQ1 : (0 : ℝ) < (P.Q (polyTreeJ P k + n + 1) : ℝ) := by exact_mod_cast P.hQ_pos _
  have hQ2 : (0 : ℝ) < (P.Q (polyTreeJ P k + n + 2) : ℝ) := by exact_mod_cast P.hQ_pos _
  have hdiff : polyCenter P C (n + 1) w - polyCenter P C n (fun i => w i.castSucc) =
      (polyWOfWord P C (n + 1) w : ℝ) /
        ((P.Q (polyTreeJ P k + n + 1) : ℝ) * (P.Q (polyTreeJ P k + n + 2) : ℝ)) := by
    unfold polyCenter polyWOfWord polyCenterInt
    rw [polyPairOfWord_fst_succ]
    have hidx1 : polyTreeJ P k + (n + 1) + 1 = polyTreeJ P k + n + 2 := by omega
    have hidx2 : polyTreeJ P k + (n + 1) = polyTreeJ P k + n + 1 := by omega
    rw [hidx1, hidx2]
    push_cast [polyCenterInt]
    field_simp
  rw [hdiff, abs_div, abs_of_pos (mul_pos hQ1 hQ2)]
  have hW : |(polyWOfWord P C (n + 1) w : ℝ)| ≤
      ((k : ℝ) + 1) * (P.Q (polyTreeJ P k + n + 1) : ℝ) := by
    have h := abs_polyWOfWord_le P C (n + 1) w
    have hidx : polyTreeJ P k + (n + 1) = polyTreeJ P k + n + 1 := by omega
    rw [hidx] at h
    exact_mod_cast h
  calc |(polyWOfWord P C (n + 1) w : ℝ)| /
        ((P.Q (polyTreeJ P k + n + 1) : ℝ) * (P.Q (polyTreeJ P k + n + 2) : ℝ))
      ≤ (((k : ℝ) + 1) * (P.Q (polyTreeJ P k + n + 1) : ℝ)) /
          ((P.Q (polyTreeJ P k + n + 1) : ℝ) * (P.Q (polyTreeJ P k + n + 2) : ℝ)) :=
        div_le_div_of_nonneg_right hW (mul_pos hQ1 hQ2).le
    _ = ((k : ℝ) + 1) / (P.Q (polyTreeJ P k + n + 2) : ℝ) := by field_simp

def polyCInterv (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : Set ℝ :=
  Set.Icc (polyCenter P C n w - polyRadC P k n) (polyCenter P C n w + polyRadC P k n)

lemma polyCInterv_nonempty (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : (polyCInterv P C n w).Nonempty :=
  ⟨polyCenter P C n w, by
    have hr := (polyRadC_pos P k n).le
    exact ⟨by linarith, by linarith⟩⟩

lemma polyCInterv_isClosed (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : IsClosed (polyCInterv P C n w) := isClosed_Icc

lemma polyCInterv_isCompact (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : IsCompact (polyCInterv P C n w) := isCompact_Icc

lemma polyCInterv_succ_subset (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin (n + 1) → Fin C.b) :
    polyCInterv P C (n + 1) w ⊆ polyCInterv P C n (fun i => w i.castSucc) := by
  intro x hx
  have hstep := polyCenter_step_sub_abs_le P C n w
  have hrad_succ : polyRadC P k (n + 1) ≤ ((k : ℝ) + 1) / (P.Q (polyTreeJ P k + n + 2) : ℝ) := by
    have hlt := polyRadC_twice_lt P k (n + 1)
    have hidx : polyTreeJ P k + (n + 1) + 1 = polyTreeJ P k + n + 2 := by omega
    rw [hidx] at hlt
    have hQ2 : (0 : ℝ) < (P.Q (polyTreeJ P k + n + 2) : ℝ) := by exact_mod_cast P.hQ_pos _
    have hrad_pos := polyRadC_pos P k (n + 1)
    have h1 : (1 / 2 : ℝ) / (P.Q (polyTreeJ P k + n + 2) : ℝ) ≤
        ((k : ℝ) + 1) / (P.Q (polyTreeJ P k + n + 2) : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hQ2.le
    linarith
  have hrad_sum : ((k : ℝ) + 1) / (P.Q (polyTreeJ P k + n + 2) : ℝ) + polyRadC P k (n + 1) ≤
      polyRadC P k n := by
    have hbase : polyRadC P k n = 2 * (((k : ℝ) + 1) / (P.Q (polyTreeJ P k + n + 2) : ℝ)) := by
      unfold polyRadC; ring
    linarith
  rw [abs_le] at hstep
  exact ⟨by linarith [hx.1, hstep.1], by linarith [hx.2, hstep.2]⟩

def polyPrefix (n : ℕ) {α : Type*} (w : ℕ → α) : Fin n → α := fun i => w i.1

def polyCantorSet (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) : Set ℝ :=
  {x : ℝ | ∃ w : ℕ → Fin C.b, ∀ n : ℕ, x ∈ polyCInterv P C n (polyPrefix n w)}

/-- 分离引理：`w1 ≠ w2`（同长 `n`）时，整数中心满足 `polyCenterInt P C n w1 ≠ polyCenterInt P C n w2`。 -/
lemma polyCenterInt_injective (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ) :
    Function.Injective (polyCenterInt P C n) := by
  intro w1 w2 heq
  by_contra hne
  have hex : ∃ i : Fin n, w1 i ≠ w2 i := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  let S : Finset ℕ := (Finset.univ : Finset (Fin n)).filter (fun i => w1 i ≠ w2 i)
    |>.image (fun i => i.1)
  have hS_ne : S.Nonempty := by
    rcases hex with ⟨i, hi⟩
    exact ⟨i.1, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩⟩
  set i₀ := S.min' hS_ne
  have hi₀_mem : i₀ ∈ S := Finset.min'_mem S hS_ne
  obtain ⟨i₀Fin, hi₀Fin, hi₀_val⟩ := Finset.mem_image.mp hi₀_mem
  have hi₀_lt : i₀ < n := by rw [← hi₀_val]; exact i₀Fin.2
  have hi₀_ne : w1 ⟨i₀, hi₀_lt⟩ ≠ w2 ⟨i₀, hi₀_lt⟩ := by
    have h1 := (Finset.mem_filter.mp hi₀Fin).2
    have hfin : i₀Fin = ⟨i₀, hi₀_lt⟩ := Fin.ext hi₀_val
    rwa [hfin] at h1
  have hagree : ∀ t : ℕ, (ht : t ≤ i₀) →
      (fun j : Fin t => w1 ⟨j.1, by omega⟩) = (fun j : Fin t => w2 ⟨j.1, by omega⟩) := by
    intro t ht
    funext j
    by_contra hj
    have hj_mem : j.1 ∈ S := Finset.mem_image.mpr ⟨⟨j.1, by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
    have := Finset.min'_le S j.1 hj_mem
    omega
  let pref1 : ∀ t : ℕ, t ≤ n → Fin t → Fin C.b := fun t _ j => w1 ⟨j.1, by omega⟩
  let pref2 : ∀ t : ℕ, t ≤ n → Fin t → Fin C.b := fun t _ j => w2 ⟨j.1, by omega⟩
  have hagree_pref : ∀ (t : ℕ) (ht : t ≤ n), t ≤ i₀ → pref1 t ht = pref2 t ht := by
    intro t ht hti
    funext j
    exact congrFun (hagree t hti) j
  let Δ : ∀ t : ℕ, ℤ := fun t =>
    if ht : t ≤ n then polyCenterInt P C t (pref1 t ht) - polyCenterInt P C t (pref2 t ht) else 0
  have hΔ_zero : ∀ t : ℕ, t ≤ i₀ → Δ t = 0 := by
    intro t ht
    have htn : t ≤ n := by omega
    dsimp [Δ]
    simp only [htn, ↓reduceDIte]
    rw [hagree_pref t htn ht, sub_self]
  have hΔ_i₀1 : 1 ≤ |Δ (i₀ + 1)| := by
    have htn : i₀ + 1 ≤ n := by omega
    have hi0n : i₀ ≤ n := by omega
    have h1 : pref1 (i₀ + 1) htn (Fin.last i₀) = w1 ⟨i₀, hi₀_lt⟩ := by
      simp [pref1, Fin.last]
    have h2 : pref2 (i₀ + 1) htn (Fin.last i₀) = w2 ⟨i₀, hi₀_lt⟩ := by
      simp [pref2, Fin.last]
    have hpre : (fun j : Fin i₀ => pref1 (i₀ + 1) htn j.castSucc) = pref1 i₀ hi0n := rfl
    have hpre2 : (fun j : Fin i₀ => pref2 (i₀ + 1) htn j.castSucc) = pref2 i₀ hi0n := rfl
    have hpeq : polyPairOfWord P C i₀ (pref1 i₀ hi0n) = polyPairOfWord P C i₀ (pref2 i₀ hi0n) := by
      rw [hagree_pref i₀ hi0n le_rfl]
    have hΔ_eq : Δ (i₀ + 1) = C.digit (w1 ⟨i₀, hi₀_lt⟩) - C.digit (w2 ⟨i₀, hi₀_lt⟩) := by
      dsimp [Δ, polyCenterInt]
      simp only [htn, ↓reduceDIte]
      dsimp [polyPairOfWord]
      rw [hpre, hpre2, hpeq, h1, h2]
      ring
    rw [hΔ_eq]
    have hd_ne : C.digit (w1 ⟨i₀, hi₀_lt⟩) ≠ C.digit (w2 ⟨i₀, hi₀_lt⟩) :=
      fun h => hi₀_ne (C.inj h)
    exact Int.one_le_abs (sub_ne_zero.mpr hd_ne)
  have hΔ_growth : ∀ t : ℕ, i₀ + 1 ≤ t → t ≤ n →
      1 ≤ |Δ t| ∧ |Δ (t - 1)| < |Δ t| := by
    intro t ht_lo ht_hi
    induction t with
    | zero => omega
    | succ t ih =>
        by_cases hteq : t = i₀
        · subst hteq
          have h0 : Δ i₀ = 0 := hΔ_zero i₀ le_rfl
          simp only [Nat.add_sub_cancel]
          rw [h0, abs_zero]
          exact ⟨hΔ_i₀1, by omega⟩
        · have ht_lo' : i₀ + 1 ≤ t := by omega
          have ⟨ih1, ih2⟩ := ih ht_lo' (by omega)
          have htn : t ≤ n := by omega
          have ht1n : t + 1 ≤ n := ht_hi
          have htm1n : t - 1 ≤ n := by omega
          have hΔ_rec : Δ (t + 1) = P.A (polyTreeJ P k + t + 1) * Δ t + Δ (t - 1) +
              (C.digit (pref1 (t + 1) ht1n (Fin.last t)) -
                C.digit (pref2 (t + 1) ht1n (Fin.last t))) := by
            have hpre1 : (fun j : Fin t => pref1 (t + 1) ht1n j.castSucc) = pref1 t htn := rfl
            have hpre2 : (fun j : Fin t => pref2 (t + 1) ht1n j.castSucc) = pref2 t htn := rfl
            have hfst1 : (polyPairOfWord P C t (pref1 t htn)).1 =
                polyCenterInt P C (t - 1) (pref1 (t - 1) htm1n) := by
              obtain ⟨m, hm⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
              subst hm
              exact polyPairOfWord_fst_succ P C m _
            have hfst2 : (polyPairOfWord P C t (pref2 t htn)).1 =
                polyCenterInt P C (t - 1) (pref2 (t - 1) htm1n) := by
              obtain ⟨m, hm⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
              subst hm
              exact polyPairOfWord_fst_succ P C m _
            dsimp [Δ, polyCenterInt]
            simp only [ht1n, htn, htm1n, ↓reduceDIte]
            dsimp [polyPairOfWord]
            rw [hpre1, hpre2, hfst1, hfst2]
            dsimp [polyCenterInt]
            ring
          have hA := polyA_ge_tree_bound P k (polyTreeJ P k + t + 1) (by omega)
          have hd1 := C.abs_le (pref1 (t + 1) ht1n (Fin.last t))
          have hd2 := C.abs_le (pref2 (t + 1) ht1n (Fin.last t))
          set δ : ℤ := C.digit (pref1 (t + 1) ht1n (Fin.last t)) -
            C.digit (pref2 (t + 1) ht1n (Fin.last t))
          have hδ : |δ| ≤ 2 * (k : ℤ) := by
            calc |δ| ≤ |C.digit _| + |C.digit _| := abs_sub _ _
              _ ≤ (k : ℤ) + (k : ℤ) := add_le_add hd1 hd2
              _ = 2 * (k : ℤ) := by ring
          have hrev : P.A (polyTreeJ P k + t + 1) * |Δ t| - |Δ (t - 1)| - |δ| ≤ |Δ (t + 1)| := by
            have hA_nn : 0 ≤ P.A (polyTreeJ P k + t + 1) := by omega
            have hmul_eq : P.A (polyTreeJ P k + t + 1) * Δ t = Δ (t + 1) - (Δ (t - 1) + δ) := by
              linarith
            have htri1 : |P.A (polyTreeJ P k + t + 1) * Δ t| ≤ |Δ (t + 1)| + |Δ (t - 1) + δ| := by
              rw [hmul_eq]; exact abs_sub _ _
            rw [abs_mul, abs_of_nonneg hA_nn] at htri1
            have h2 := abs_add_le (Δ (t - 1)) δ
            linarith
          have hbig : 2 * |Δ t| ≤ |Δ (t + 1)| := by
            have h1 : (8 * (k : ℤ) + 9) * |Δ t| ≤ P.A (polyTreeJ P k + t + 1) * |Δ t| :=
              mul_le_mul_of_nonneg_right hA (abs_nonneg _)
            have h2 : 2 * (k : ℤ) ≤ 2 * (k : ℤ) * |Δ t| := by
              nlinarith
            nlinarith
          simp only [Nat.add_sub_cancel]
          exact ⟨by omega, by omega⟩
  have hΔ_ne : Δ n ≠ 0 := by
    have h1 := (hΔ_growth n (by omega) le_rfl).1
    intro h0; rw [h0, abs_zero] at h1; omega
  dsimp [Δ] at hΔ_ne
  simp only [le_rfl, ↓reduceDIte] at hΔ_ne
  have h1 : pref1 n le_rfl = w1 := rfl
  have h2 : pref2 n le_rfl = w2 := rfl
  rw [h1, h2, heq, sub_self] at hΔ_ne
  exact hΔ_ne rfl

lemma poly_round_eq_of_abs_sub_lt_half {y : ℝ} {m : ℤ} (h : |y - (m : ℝ)| < 1 / 2) :
    round y = m := by
  have h1 : |y - (round y : ℝ)| ≤ 1 / 2 := abs_sub_round y
  have hdiff : |((round y : ℝ) - (m : ℝ))| < 1 := by
    calc |((round y : ℝ) - (m : ℝ))|
        = |(-(y - (round y : ℝ))) + (y - (m : ℝ))| := by ring_nf
      _ ≤ |-(y - (round y : ℝ))| + |y - (m : ℝ)| := abs_add_le _ _
      _ = |y - (round y : ℝ)| + |y - (m : ℝ)| := by rw [abs_neg]
      _ < 1 / 2 + 1 / 2 := add_lt_add_of_le_of_lt h1 h
      _ = 1 := by norm_num
  have hZ : |round y - m| < 1 := by
    have hR : ((|round y - m| : ℤ) : ℝ) < (1 : ℤ) := by
      rw [Int.cast_abs, Int.cast_sub, Int.cast_one]
      exact hdiff
    exact Int.cast_lt.mp hR
  rw [abs_lt] at hZ
  omega

lemma polyCInterv_prefix_subset (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k)
    {m n : ℕ} (hmn : m ≤ n) (w : Fin n → Fin C.b) :
    polyCInterv P C n w ⊆ polyCInterv P C m (fun i => w ⟨i.1, by omega⟩) := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst hm
      exact subset_rfl
  | succ n ih =>
      rcases eq_or_lt_of_le hmn with rfl | hlt
      · exact subset_rfl
      · have hle : m ≤ n := Nat.lt_succ_iff.mp hlt
        exact Set.Subset.trans (polyCInterv_succ_subset P C n w) (ih hle _)

lemma polyCantorSet_inter_polyCInterv_nonempty (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k)
    (n : ℕ) (u : Fin n → Fin C.b) :
    (polyCantorSet P C ∩ polyCInterv P C n u).Nonempty := by
  let w : ℕ → Fin C.b := fun m => if h : m < n then u ⟨m, h⟩ else ⟨0, C.hb⟩
  let F : ℕ → Set ℝ := fun m => polyCInterv P C (n + m) (polyPrefix (n + m) w)
  have hanti : ∀ m : ℕ, F (m + 1) ⊆ F m := fun m => polyCInterv_succ_subset P C (n + m) _
  have hne : ∀ m : ℕ, (F m).Nonempty := fun m => polyCInterv_nonempty P C _ _
  have hcomp : IsCompact (F 0) := polyCInterv_isCompact P C _ _
  have hclosed : ∀ m : ℕ, IsClosed (F m) := fun m => polyCInterv_isClosed P C _ _
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    F hanti hne hcomp hclosed
  have hpre_u : polyPrefix n w = u := by
    funext i
    simp [polyPrefix, w, i.2]
  have hx_all : ∀ m : ℕ, x ∈ polyCInterv P C m (polyPrefix m w) := by
    intro m
    rcases le_or_gt n m with hnm | hmn
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnm
      exact Set.mem_iInter.mp hx t
    · have h0 : x ∈ polyCInterv P C (n + 0) (polyPrefix (n + 0) w) := Set.mem_iInter.mp hx 0
      have hsub := polyCInterv_prefix_subset P C (by omega : m ≤ n + 0) (polyPrefix (n + 0) w) h0
      have heq_w : (fun i : Fin m => polyPrefix (n + 0) w ⟨i.1, by omega⟩) = polyPrefix m w := by
        funext i; rfl
      rwa [heq_w] at hsub
  refine ⟨x, ⟨w, hx_all⟩, ?_⟩
  have h0 := hx_all n
  rwa [hpre_u] at h0

lemma polyCInterv_disjoint_of_ne (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    {u₁ u₂ : Fin n → Fin C.b} (hne : u₁ ≠ u₂) :
    Disjoint (polyCInterv P C n u₁) (polyCInterv P C n u₂) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hIntNe : polyCenterInt P C n u₁ ≠ polyCenterInt P C n u₂ :=
    fun h => hne (polyCenterInt_injective P C n h)
  have hQ_pos : (0 : ℝ) < (P.Q (polyTreeJ P k + n + 1) : ℝ) := by exact_mod_cast P.hQ_pos _
  have hZ_ge1 : (1 : ℤ) ≤ |polyCenterInt P C n u₁ - polyCenterInt P C n u₂| :=
    Int.one_le_abs (sub_ne_zero.mpr hIntNe)
  have hR_ge1 : (1 : ℝ) ≤ |(polyCenterInt P C n u₁ : ℝ) - (polyCenterInt P C n u₂ : ℝ)| := by
    exact_mod_cast hZ_ge1
  have hcdiff : 1 / (P.Q (polyTreeJ P k + n + 1) : ℝ) ≤
      |polyCenter P C n u₁ - polyCenter P C n u₂| := by
    unfold polyCenter
    rw [← sub_div, abs_div, abs_of_pos hQ_pos]
    exact div_le_div_of_nonneg_right hR_ge1 hQ_pos.le
  have h1 : |x - polyCenter P C n u₁| ≤ polyRadC P k n := abs_sub_le_iff.mpr ⟨by linarith [hx1.2], by linarith [hx1.1]⟩
  have h2 : |x - polyCenter P C n u₂| ≤ polyRadC P k n := abs_sub_le_iff.mpr ⟨by linarith [hx2.2], by linarith [hx2.1]⟩
  have htri : |polyCenter P C n u₁ - polyCenter P C n u₂| ≤ 2 * polyRadC P k n := by
    calc |polyCenter P C n u₁ - polyCenter P C n u₂|
        = |(x - polyCenter P C n u₂) - (x - polyCenter P C n u₁)| := by ring_nf
      _ ≤ |x - polyCenter P C n u₂| + |x - polyCenter P C n u₁| := abs_sub _ _
      _ ≤ 2 * polyRadC P k n := by linarith
  have hlt := polyRadC_twice_lt P k n
  have hhalf : (1 / 2 : ℝ) / (P.Q (polyTreeJ P k + n + 1) : ℝ) < 1 / (P.Q (polyTreeJ P k + n + 1) : ℝ) := by
    apply div_lt_div_of_pos_right (by norm_num) hQ_pos
  linarith

lemma polyCantorSet_isCompact (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) :
    IsCompact (polyCantorSet P C) := by
  let U : ℕ → Set ℝ := fun n => ⋃ u ∈ (Finset.univ : Finset (Fin n → Fin C.b)), polyCInterv P C n u
  have hEq : polyCantorSet P C = ⋂ n : ℕ, U n := by
    ext x
    constructor
    · rintro ⟨w, hw⟩
      exact Set.mem_iInter.mpr fun n =>
        Set.mem_iUnion₂.mpr ⟨polyPrefix n w, Finset.mem_univ _, hw n⟩
    · intro hx
      have huniq : ∀ n : ℕ, ∃! u : Fin n → Fin C.b, x ∈ polyCInterv P C n u := by
        intro n
        obtain ⟨u, _, hu⟩ := Set.mem_iUnion₂.mp (Set.mem_iInter.mp hx n)
        refine ⟨u, hu, fun v hv => ?_⟩
        by_contra hne
        exact (Set.disjoint_left.mp (polyCInterv_disjoint_of_ne P C n hne)) hv hu
      choose u hu using fun n => (huniq n).exists
      have huniq_u : ∀ n v, x ∈ polyCInterv P C n v → v = u n := fun n v hv =>
        (huniq n).unique hv (hu n)
      have hcompat : ∀ n : ℕ, (fun i : Fin n => u (n + 1) i.castSucc) = u n := fun n =>
        huniq_u n _ (polyCInterv_succ_subset P C n (u (n + 1)) (hu (n + 1)))
      let w : ℕ → Fin C.b := fun n => u (n + 1) (Fin.last n)
      have hpref : ∀ n : ℕ, polyPrefix n w = u n := by
        intro n
        induction n with
        | zero => funext i; exact Fin.elim0 i
        | succ n ih =>
            funext i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simp [polyPrefix, w]
            · change w j.1 = u (n + 1) j.castSucc
              have hj : polyPrefix n w j = u n j := congrFun ih j
              have hc := congrFun (hcompat n) j
              exact hj.trans hc.symm
      exact ⟨w, fun n => by rw [hpref n]; exact hu n⟩
  rw [hEq]
  have hclosed_U : ∀ n : ℕ, IsClosed (U n) := fun n =>
    isClosed_biUnion_finset fun u _ => polyCInterv_isClosed P C n u
  have hclosed : IsClosed (⋂ n : ℕ, U n) := isClosed_iInter hclosed_U
  have hsub0 : (⋂ n : ℕ, U n) ⊆ polyCInterv P C 0 ![] := by
    intro x hx
    obtain ⟨u, _, hu⟩ := Set.mem_iUnion₂.mp (Set.mem_iInter.mp hx 0)
    have heq : u = ![] := Subsingleton.elim _ _
    rwa [← heq]
  exact (polyCInterv_isCompact P C 0 ![]).of_isClosed_subset hclosed hsub0

lemma polyCantorSet_isClosed (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) :
    IsClosed (polyCantorSet P C) :=
  (polyCantorSet_isCompact P C).isClosed

private lemma poly_fin_ext_card (b n N : ℕ) (h : n ≤ N) (v : Fin n → Fin b) :
    (Finset.univ.filter (fun w : Fin N → Fin b =>
      (fun t : Fin n => w ⟨t.1, Nat.lt_of_lt_of_le t.2 h⟩) = v)).card ≤ b ^ (N - n) := by
  let proj : {w : Fin N → Fin b // (fun t : Fin n => w ⟨t.1, Nat.lt_of_lt_of_le t.2 h⟩) = v} →
      (Fin (N - n) → Fin b) :=
    fun ⟨w, _⟩ t => w ⟨n + t.1, by omega⟩
  have hinj : Function.Injective proj := by
    rintro ⟨w1, hw1⟩ ⟨w2, hw2⟩ heq
    ext s
    by_cases hs : s.1 < n
    · have h1 := congrFun hw1 ⟨s.1, hs⟩
      have h2 := congrFun hw2 ⟨s.1, hs⟩
      exact congrArg Fin.val (h1.trans h2.symm)
    · have h1 := congrFun heq ⟨s.1 - n, by omega⟩
      have hid : n + (s.1 - n) = s.1 := by omega
      have hval := congrArg Fin.val h1
      dsimp [proj] at hval
      simpa [hid] using hval
  have hcard := Fintype.card_le_of_injective proj hinj
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_subtype] at hcard
  exact hcard

/-- 核心有限覆盖下界：在均匀 $b$-叉子树上（$2 \le b$），任取有限正直径覆盖集 `V_i`（$0 < \mathrm{ediam}(V_i) < 1/Q_{J+M+1}$），
    必有 $b^{-M} \le \sum 2 b^{J+2} h(\mathrm{ediam}(V_i))$。 -/
lemma poly_subtree_inv_pow_le_sum_of_cover (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k)
    (hb2 : 2 ≤ C.b) (M : ℕ) (u₀ : Fin M → Fin C.b)
    {ι : Type*} (F : Finset ι) (V : ι → Set ℝ)
    (hcov : polyCantorSet P C ∩ polyCInterv P C M u₀ ⊆ ⋃ i ∈ F, V i)
    (hpos_diam : ∀ i ∈ F, 0 < Metric.ediam (V i))
    (hsmall_diam : ∀ i ∈ F, Metric.ediam (V i) < ENNReal.ofReal (1 / (P.Q (polyTreeJ P k + M + 1) : ℝ))) :
    ((C.b : ℝ) ^ M)⁻¹ ≤ ∑ i ∈ F, (2 * (C.b : ℝ) ^ (polyTreeJ P k + 2)) *
      (polyInterpGauge P (C.b : ℝ) (Metric.ediam (V i))).toReal := by
  have hb_pos : (0 : ℝ) < (C.b : ℝ) := by exact_mod_cast C.hb
  have hb1 : (1 : ℝ) < (C.b : ℝ) := by exact_mod_cast (by omega : 1 < C.b)
  have hex_lvl : ∀ i : ι, i ∈ F → ∃ n : ℕ, M ≤ n ∧
      ENNReal.ofReal (1 / (P.Q (polyTreeJ P k + n + 2) : ℝ)) ≤ Metric.ediam (V i) ∧
      Metric.ediam (V i) < ENNReal.ofReal (1 / (P.Q (polyTreeJ P k + n + 1) : ℝ)) := by
    intro i hi
    have h0 : 0 < Metric.ediam (V i) := hpos_diam i hi
    have hlt_top : Metric.ediam (V i) < ⊤ :=
      lt_of_lt_of_le (hsmall_diam i hi) (le_of_lt ENNReal.ofReal_lt_top)
    set r := (Metric.ediam (V i)).toReal
    have hr_pos : 0 < r := ENNReal.toReal_pos h0.ne' hlt_top.ne
    have hQM_pos : (0 : ℝ) < (P.Q (polyTreeJ P k + M + 1) : ℝ) := by exact_mod_cast P.hQ_pos _
    have hlt_invM : r < 1 / (P.Q (polyTreeJ P k + M + 1) : ℝ) := by
      have h1 := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top (hsmall_diam i hi)
      rwa [ENNReal.toReal_ofReal (by positivity)] at h1
    have ht0 : Tendsto (fun m : ℕ => 1 / (P.Q m : ℝ)) atTop (nhds 0) :=
      P.poly_Q_tendsto_atTop.const_div_atTop 1
    obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp (ht0.eventually (Iio_mem_nhds hr_pos))
    let S := (Finset.range (M + m0 + 2)).filter fun n =>
      M ≤ n ∧ r < 1 / (P.Q (polyTreeJ P k + n + 1) : ℝ)
    have hMS : M ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), le_rfl, hlt_invM⟩
    set n := S.max' ⟨M, hMS⟩
    have hn_mem := Finset.mem_filter.mp (S.max'_mem ⟨M, hMS⟩)
    have hnM : M ≤ n := hn_mem.2.1
    have hn_lt : r < 1 / (P.Q (polyTreeJ P k + n + 1) : ℝ) := hn_mem.2.2
    have hn_bound : n < M + m0 + 1 := by
      by_contra hge
      have hm_ge : m0 ≤ polyTreeJ P k + n + 1 := by omega
      have hcontra := hm0 _ hm_ge
      linarith
    have hn1_ge : 1 / (P.Q (polyTreeJ P k + n + 2) : ℝ) ≤ r := by
      by_contra hlt_next
      push Not at hlt_next
      have hn1_mem : n + 1 ∈ S := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, ?_⟩
        have hidx : polyTreeJ P k + (n + 1) + 1 = polyTreeJ P k + n + 2 := by omega
        rwa [hidx]
      have hle_max := S.le_max' (n + 1) hn1_mem
      omega
    refine ⟨n, hnM, ?_, ?_⟩
    · rw [← ENNReal.ofReal_toReal hlt_top.ne]
      exact ENNReal.ofReal_le_ofReal hn1_ge
    · rw [← ENNReal.ofReal_toReal hlt_top.ne]
      exact (ENNReal.ofReal_lt_ofReal_iff (by have := P.hQ_pos (polyTreeJ P k + n + 1); positivity)).mpr hn_lt
  choose n_fun hnM hn_lo hn_hi using fun i (hi : i ∈ F) => hex_lvl i hi
  let ni : ι → ℕ := fun i => if hi : i ∈ F then n_fun i hi else M
  have hFne : F.Nonempty := by
    by_contra hFempty
    rw [Finset.not_nonempty_iff_eq_empty] at hFempty
    obtain ⟨x, hx⟩ := polyCantorSet_inter_polyCInterv_nonempty P C M u₀
    have hx_cov := hcov hx
    simp [hFempty] at hx_cov
  set N : ℕ := F.sup' hFne ni
  have hN_ge_M : M ≤ N := by
    obtain ⟨i0, hi0⟩ := hFne
    have hle : ni i0 ≤ N := Finset.le_sup' ni hi0
    have hM0 : M ≤ ni i0 := by dsimp [ni]; simp only [hi0, ↓reduceDIte]; exact hnM i0 hi0
    exact le_trans hM0 hle
  have hni_le_N : ∀ i ∈ F, ni i ≤ N := fun i hi => Finset.le_sup' ni hi
  let ExtN : Finset (Fin N → Fin C.b) :=
    Finset.univ.filter fun w => ∀ j : Fin M, w ⟨j.1, by omega⟩ = u₀ j
  have hExtN_card : ExtN.card = C.b ^ (N - M) := by
    let e : {w : Fin N → Fin C.b // ∀ j : Fin M, w ⟨j.1, by omega⟩ = u₀ j} ≃
        (Fin (N - M) → Fin C.b) :=
      { toFun := fun ⟨w, _⟩ t => w ⟨M + t.1, by omega⟩
        invFun := fun tail =>
          ⟨fun i => if hi : i.1 < M then u₀ ⟨i.1, hi⟩ else tail ⟨i.1 - M, by omega⟩, by
            intro j
            simp [j.2]⟩
        left_inv := fun ⟨w, hw⟩ => by
          ext i
          dsimp
          by_cases hi : i.1 < M
          · simp only [hi, ↓reduceDIte]
            exact congrArg Fin.val (hw ⟨i.1, hi⟩) |>.symm
          · simp only [hi, ↓reduceDIte]
            have hid : M + (i.1 - M) = i.1 := by omega
            simp [hid]
        right_inv := fun tail => by
          funext t
          have hnot : ¬ (M + t.1 < M) := by omega
          simp [hnot] }
    have h1 : ExtN.card = Fintype.card {w : Fin N → Fin C.b // ∀ j : Fin M, w ⟨j.1, by omega⟩ = u₀ j} := by
      rw [Fintype.card_subtype]
    rw [h1, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  let Act (i : ι) : Finset (Fin (ni i) → Fin C.b) :=
    Finset.univ.filter fun v => (V i ∩ polyCInterv P C (ni i) v).Nonempty
  have hactive_le_two : ∀ i ∈ F, (Act i).card ≤ 2 := by
    intro i hi
    by_contra hgt2
    have h3 : 3 ≤ (Act i).card := by omega
    obtain ⟨v1, hv1, v2, hv2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (Act i).card)
    have hne12 : 2 ≤ ((Act i).erase v1).card := by
      rw [Finset.card_erase_of_mem hv1]; omega
    have hpos3 : 0 < (((Act i).erase v1).erase v2).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h12.symm, hv2⟩)]; omega
    obtain ⟨v3, hv3'⟩ := Finset.card_pos.mp hpos3
    have hv3 : v3 ∈ Act i := (Finset.mem_erase.mp (Finset.mem_erase.mp hv3').2).2
    have h13 : v1 ≠ v3 := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hv3').2).1 h.symm
    have h23 : v2 ≠ v3 := fun h => (Finset.mem_erase.mp hv3').1 h.symm
    let m1 := polyCenterInt P C (ni i) v1
    let m2 := polyCenterInt P C (ni i) v2
    let m3 := polyCenterInt P C (ni i) v3
    have hm12 : m1 ≠ m2 := fun h => h12 (polyCenterInt_injective P C (ni i) h)
    have hm13 : m1 ≠ m3 := fun h => h13 (polyCenterInt_injective P C (ni i) h)
    have hm23 : m2 ≠ m3 := fun h => h23 (polyCenterInt_injective P C (ni i) h)
    have hpair2 : ∃ va ∈ Act i, ∃ vb ∈ Act i,
        (2 : ℝ) ≤ |(polyCenterInt P C (ni i) va : ℝ) - (polyCenterInt P C (ni i) vb : ℝ)| := by
      have hZ : 2 ≤ |m1 - m2| ∨ 2 ≤ |m1 - m3| ∨ 2 ≤ |m2 - m3| := by
        by_contra hcon
        push Not at hcon
        rcases hcon with ⟨h12_lt, h13_lt, h23_lt⟩
        have a12 := abs_lt.mp (by omega : |m1 - m2| < 2)
        have a13 := abs_lt.mp (by omega : |m1 - m3| < 2)
        have a23 := abs_lt.mp (by omega : |m2 - m3| < 2)
        omega
      rcases hZ with h | h | h
      · exact ⟨v1, hv1, v2, hv2, by exact_mod_cast h⟩
      · exact ⟨v1, hv1, v3, hv3, by exact_mod_cast h⟩
      · exact ⟨v2, hv2, v3, hv3, by exact_mod_cast h⟩
    rcases hpair2 with ⟨va, hva, vb, hvb, hmab⟩
    obtain ⟨xa, hxaV, hxaC⟩ := (Finset.mem_filter.mp hva).2
    obtain ⟨xb, hxbV, hxbC⟩ := (Finset.mem_filter.mp hvb).2
    have hQ_pos : (0 : ℝ) < (P.Q (polyTreeJ P k + ni i + 1) : ℝ) := by exact_mod_cast P.hQ_pos _
    have hcdiff : 2 / (P.Q (polyTreeJ P k + ni i + 1) : ℝ) ≤
        |polyCenter P C (ni i) va - polyCenter P C (ni i) vb| := by
      unfold polyCenter
      rw [← sub_div, abs_div, abs_of_pos hQ_pos]
      exact div_le_div_of_nonneg_right hmab hQ_pos.le
    have hxa_diff : |xa - polyCenter P C (ni i) va| ≤ polyRadC P k (ni i) :=
      abs_sub_le_iff.mpr ⟨by linarith [hxaC.2], by linarith [hxaC.1]⟩
    have hxb_diff : |xb - polyCenter P C (ni i) vb| ≤ polyRadC P k (ni i) :=
      abs_sub_le_iff.mpr ⟨by linarith [hxbC.2], by linarith [hxbC.1]⟩
    have hdist_lo : 2 / (P.Q (polyTreeJ P k + ni i + 1) : ℝ) - 2 * polyRadC P k (ni i) ≤ |xa - xb| := by
      have htri : |polyCenter P C (ni i) va - polyCenter P C (ni i) vb| ≤
          |xa - xb| + |xa - polyCenter P C (ni i) va| + |xb - polyCenter P C (ni i) vb| := by
        calc |polyCenter P C (ni i) va - polyCenter P C (ni i) vb|
            = |((xa - xb) - (xa - polyCenter P C (ni i) va)) + (xb - polyCenter P C (ni i) vb)| := by
                congr 1; ring
          _ ≤ |(xa - xb) - (xa - polyCenter P C (ni i) va)| + |xb - polyCenter P C (ni i) vb| := abs_add_le _ _
          _ ≤ |xa - xb| + |xa - polyCenter P C (ni i) va| + |xb - polyCenter P C (ni i) vb| := by
              gcongr; exact abs_sub _ _
      linarith
    have h2rad := polyRadC_twice_lt P k (ni i)
    have hinv_lt : 1 / (P.Q (polyTreeJ P k + ni i + 1) : ℝ) < |xa - xb| := by
      have hhalf : 2 / (P.Q (polyTreeJ P k + ni i + 1) : ℝ) -
          (1 / 2 : ℝ) / (P.Q (polyTreeJ P k + ni i + 1) : ℝ) =
          (3 / 2 : ℝ) / (P.Q (polyTreeJ P k + ni i + 1) : ℝ) := by ring
      have h1_lt : 1 / (P.Q (polyTreeJ P k + ni i + 1) : ℝ) <
          (3 / 2 : ℝ) / (P.Q (polyTreeJ P k + ni i + 1) : ℝ) :=
        div_lt_div_of_pos_right (by norm_num) hQ_pos
      linarith
    have hed_lt : ENNReal.ofReal (1 / (P.Q (polyTreeJ P k + ni i + 1) : ℝ)) < edist xa xb := by
      rw [edist_dist, Real.dist_eq]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans (div_pos one_pos hQ_pos) hinv_lt)).mpr hinv_lt
    have hed_le : edist xa xb ≤ Metric.ediam (V i) := Metric.edist_le_ediam_of_mem hxaV hxbV
    have hni_eq : ni i = n_fun i hi := by dsimp [ni]; simp only [hi, ↓reduceDIte]
    have hhi := hn_hi i hi
    rw [← hni_eq] at hhi
    exact not_lt_of_ge (le_trans hed_lt.le hed_le) hhi |>.elim
  have hex_witness : ∀ w ∈ ExtN, ∃ i ∈ F, ∃ hle : ni i ≤ N,
      (fun t : Fin (ni i) => w ⟨t.1, Nat.lt_of_lt_of_le t.2 hle⟩) ∈ Act i := by
    intro w hw
    have hw_ext := (Finset.mem_filter.mp hw).2
    obtain ⟨x, hxK, hxw⟩ := polyCantorSet_inter_polyCInterv_nonempty P C N w
    have hxu₀ : x ∈ polyCInterv P C M u₀ := by
      have hsub := polyCInterv_prefix_subset P C hN_ge_M w hxw
      have heq : (fun j : Fin M => w ⟨j.1, by omega⟩) = u₀ := funext hw_ext
      rwa [heq] at hsub
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hcov ⟨hxK, hxu₀⟩)
    refine ⟨i, hi, hni_le_N i hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨x, hxi, polyCInterv_prefix_subset P C (hni_le_N i hi) w hxw⟩
  let branchFin (i : ι) : Finset (Fin N → Fin C.b) :=
    if h : ni i ≤ N then
      (Act i).biUnion fun v =>
        Finset.univ.filter fun w : Fin N → Fin C.b =>
          (fun t : Fin (ni i) => w ⟨t.1, Nat.lt_of_lt_of_le t.2 h⟩) = v
    else ∅
  have hbranch_card : ∀ i ∈ F, (branchFin i).card ≤ 2 * C.b ^ (N - ni i) := by
    intro i hi
    have hle := hni_le_N i hi
    dsimp [branchFin]
    simp only [hle, ↓reduceDIte]
    calc ((Act i).biUnion fun v => Finset.univ.filter fun w : Fin N → Fin C.b =>
            (fun t : Fin (ni i) => w ⟨t.1, Nat.lt_of_lt_of_le t.2 hle⟩) = v).card
        ≤ ∑ v ∈ Act i, (Finset.univ.filter fun w : Fin N → Fin C.b =>
            (fun t : Fin (ni i) => w ⟨t.1, Nat.lt_of_lt_of_le t.2 hle⟩) = v).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ Act i, C.b ^ (N - ni i) := by
          gcongr with v _
          exact poly_fin_ext_card C.b (ni i) N hle v
      _ = (Act i).card * C.b ^ (N - ni i) := by simp [Finset.sum_const]
      _ ≤ 2 * C.b ^ (N - ni i) := Nat.mul_le_mul_right _ (hactive_le_two i hi)
  have hExtN_sub_biUnion : ExtN ⊆ F.biUnion branchFin := by
    intro w hw
    obtain ⟨i, hi, hle, hv⟩ := hex_witness w hw
    refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
    dsimp [branchFin]
    simp only [hle, ↓reduceDIte]
    exact Finset.mem_biUnion.mpr ⟨_, hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hExtN_sub : ExtN.card ≤ ∑ i ∈ F, 2 * C.b ^ (N - ni i) := by
    calc ExtN.card ≤ (F.biUnion branchFin).card := Finset.card_le_card hExtN_sub_biUnion
      _ ≤ ∑ i ∈ F, (branchFin i).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ F, 2 * C.b ^ (N - ni i) := Finset.sum_le_sum hbranch_card
  rw [hExtN_card] at hExtN_sub
  have hR_le : ((C.b : ℝ) ^ (N - M)) ≤ ∑ i ∈ F, 2 * (C.b : ℝ) ^ (N - ni i) := by
    exact_mod_cast hExtN_sub
  have hbN_pos : 0 < (C.b : ℝ) ^ N := pow_pos hb_pos N
  have hdiv := div_le_div_of_nonneg_right hR_le hbN_pos.le
  have hlhs : ((C.b : ℝ) ^ (N - M)) / (C.b : ℝ) ^ N = ((C.b : ℝ) ^ M)⁻¹ := by
    have hsplit : (C.b : ℝ) ^ N = (C.b : ℝ) ^ M * (C.b : ℝ) ^ (N - M) := by
      rw [← pow_add, Nat.add_sub_of_le hN_ge_M]
    rw [hsplit]
    field_simp
  have hrhs_eq : (∑ i ∈ F, 2 * (C.b : ℝ) ^ (N - ni i)) / (C.b : ℝ) ^ N =
      ∑ i ∈ F, 2 * ((C.b : ℝ) ^ ni i)⁻¹ := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hni := hni_le_N i hi
    have hsplit : (C.b : ℝ) ^ N = (C.b : ℝ) ^ ni i * (C.b : ℝ) ^ (N - ni i) := by
      rw [← pow_add, Nat.add_sub_of_le hni]
    rw [hsplit]
    field_simp
  rw [hlhs, hrhs_eq] at hdiv
  have hsum_term : ∀ i ∈ F,
      2 * ((C.b : ℝ) ^ ni i)⁻¹ ≤
        (2 * (C.b : ℝ) ^ (polyTreeJ P k + 2)) *
          (polyInterpGauge P (C.b : ℝ) (Metric.ediam (V i))).toReal := by
    intro i hi
    have hni_eq : ni i = n_fun i hi := by dsimp [ni]; simp only [hi, ↓reduceDIte]
    have hni_J₀ : P.J₀ ≤ polyTreeJ P k + ni i + 2 := by
      have := polyTreeJ_ge_J₀_succ P k; omega
    have hlo_i := hn_lo i hi
    rw [← hni_eq] at hlo_i
    have hgauge_lo : ENNReal.ofReal ((C.b : ℝ) ^ (-((polyTreeJ P k + ni i + 2 : ℕ) : ℤ))) ≤
        polyInterpGauge P (C.b : ℝ) (Metric.ediam (V i)) := by
      calc ENNReal.ofReal ((C.b : ℝ) ^ (-((polyTreeJ P k + ni i + 2 : ℕ) : ℤ)))
          = polyInterpGauge P (C.b : ℝ) (ENNReal.ofReal (1 / (P.Q (polyTreeJ P k + ni i + 2) : ℝ))) :=
            (polyInterpGauge_at_inv_Q P hb1 hni_J₀).symm
        _ ≤ polyInterpGauge P (C.b : ℝ) (Metric.ediam (V i)) :=
            polyInterpGauge_mono P hb1 hlo_i
    have hlt_top_V : Metric.ediam (V i) < ⊤ :=
      lt_of_lt_of_le (hsmall_diam i hi) (le_of_lt ENNReal.ofReal_lt_top)
    have hgauge_ne_top : polyInterpGauge P (C.b : ℝ) (Metric.ediam (V i)) ≠ ⊤ := by
      rw [polyInterpGauge_eq_ofReal_toReal P hb1 hlt_top_V.ne]
      exact ENNReal.ofReal_ne_top
    have hreal_lo : (C.b : ℝ) ^ (-((polyTreeJ P k + ni i + 2 : ℕ) : ℤ)) ≤
        (polyInterpGauge P (C.b : ℝ) (Metric.ediam (V i))).toReal := by
      have h1 := ENNReal.toReal_mono hgauge_ne_top hgauge_lo
      rwa [ENNReal.toReal_ofReal (zpow_nonneg hb_pos.le _)] at h1
    have hid_pow : 2 * ((C.b : ℝ) ^ ni i)⁻¹ =
        (2 * (C.b : ℝ) ^ (polyTreeJ P k + 2)) *
          (C.b : ℝ) ^ (-((polyTreeJ P k + ni i + 2 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_natCast]
      have hadd : (C.b : ℝ) ^ (polyTreeJ P k + ni i + 2) =
          (C.b : ℝ) ^ (polyTreeJ P k + 2) * (C.b : ℝ) ^ ni i := by
        rw [← pow_add, show polyTreeJ P k + 2 + ni i = polyTreeJ P k + ni i + 2 by omega]
      rw [hadd]
      field_simp
    rw [hid_pow]
    exact mul_le_mul_of_nonneg_left hreal_lo (by positivity)
  exact le_trans hdiv (Finset.sum_le_sum hsum_term)

/-- 子树下界定理：当 `2 ≤ C.b` 时，对任意 `M` 与前缀 `u₀`，有正的规范测度显式下界。 -/
theorem mkMetric_polyWordTree_subtree_pos (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k)
    (hb2 : 2 ≤ C.b) (M : ℕ) (u₀ : Fin M → Fin C.b) :
    ENNReal.ofReal (((C.b : ℝ) ^ M)⁻¹ / (2 * (C.b : ℝ) ^ (polyTreeJ P k + 2))) ≤
      Measure.mkMetric (polyInterpGauge P (C.b : ℝ)) (polyCantorSet P C ∩ polyCInterv P C M u₀) := by
  have hb_pos : (0 : ℝ) < (C.b : ℝ) := by exact_mod_cast C.hb
  have hb1 : (1 : ℝ) < (C.b : ℝ) := by exact_mod_cast (by omega : 1 < C.b)
  have hQ_pos : (0 : ℝ) < (P.Q (polyTreeJ P k + M + 1) : ℝ) := by exact_mod_cast P.hQ_pos _
  set Ctree : ℝ := 2 * (C.b : ℝ) ^ (polyTreeJ P k + 2)
  have hCtree_pos : 0 < Ctree := by positivity
  set r₀ : ℝ := (1 / 2 : ℝ) / (P.Q (polyTreeJ P k + M + 1) : ℝ)
  have hr₀_pos : 0 < r₀ := by positivity
  rw [Measure.mkMetric_apply]
  refine le_iSup₂_of_le (ENNReal.ofReal r₀) (ENNReal.ofReal_pos.mpr hr₀_pos) ?_
  refine le_iInf fun t => le_iInf fun ht_cov => le_iInf fun ht_diam => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  by_cases htop : (∑' n : ℕ, ⨆ _ : (t n).Nonempty, polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))) = ⊤
  · rw [htop]
    exact le_trans le_top (le_add_right le_rfl)
  have hcont := polyInterpGaugeReal_continuous P hb1
  have hε_pos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hη : ∀ n : ℕ, ∃ η : ℝ, 0 < η ∧ ∀ y : ℝ, |y - (Metric.ediam (t n)).toReal| < η →
      |polyInterpGaugeReal P (C.b : ℝ) y -
        polyInterpGaugeReal P (C.b : ℝ) (Metric.ediam (t n)).toReal| <
        (ε : ℝ) / (2 ^ (n + 2) * Ctree) := fun n =>
    Metric.continuousAt_iff.mp (hcont.continuousAt (x := (Metric.ediam (t n)).toReal)) _
      (by positivity)
  choose η_fun hη_pos hη_spec using hη
  let δ_fun : ℕ → ℝ := fun n => min (η_fun n / 4) ((1 / 8 : ℝ) / (P.Q (polyTreeJ P k + M + 1) : ℝ))
  have hδ_pos : ∀ n : ℕ, 0 < δ_fun n := fun n => lt_min (by linarith [hη_pos n]) (by positivity)
  let V : ℕ → Set ℝ := fun n => if (t n).Nonempty then Metric.thickening (δ_fun n) (t n) else ∅
  have hV_open : ∀ n : ℕ, IsOpen (V n) := fun n => by
    dsimp [V]; split_ifs; exact Metric.isOpen_thickening; exact isOpen_empty
  have hV_cov : polyCantorSet P C ∩ polyCInterv P C M u₀ ⊆ ⋃ n : ℕ, V n := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (ht_cov hx)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    have hne : (t n).Nonempty := ⟨x, hn⟩
    dsimp [V]
    simp only [hne, ↓reduceIte]
    exact Metric.self_subset_thickening (hδ_pos n) _ hn
  have hK_comp : IsCompact (polyCantorSet P C ∩ polyCInterv P C M u₀) :=
    (polyCantorSet_isCompact P C).inter_right (polyCInterv_isClosed P C M u₀)
  obtain ⟨F₀, hF₀⟩ := hK_comp.elim_finite_subcover V hV_open hV_cov
  set F : Finset ℕ := F₀.filter fun n => (t n).Nonempty
  have hF_cov : polyCantorSet P C ∩ polyCInterv P C M u₀ ⊆ ⋃ n ∈ F, V n := by
    intro x hx
    obtain ⟨n, hnF, hxn⟩ := Set.mem_iUnion₂.mp (hF₀ hx)
    have hne : (t n).Nonempty := by
      by_contra hempty
      simp [V, hempty] at hxn
    exact Set.mem_iUnion₂.mpr ⟨n, Finset.mem_filter.mpr ⟨hnF, hne⟩, hxn⟩
  have hV_pos : ∀ n ∈ F, 0 < Metric.ediam (V n) := by
    intro n hn
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hn).2
    have hne : (t n).Nonempty := ⟨x, hx⟩
    have h1 : x ∈ V n := by
      dsimp [V]; simp only [hne, ↓reduceIte]; exact Metric.self_subset_thickening (hδ_pos n) _ hx
    have h2 : x + δ_fun n / 2 ∈ V n := by
      dsimp [V]; simp only [hne, ↓reduceIte]
      rw [Metric.mem_thickening_iff]
      refine ⟨x, hx, ?_⟩
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos (hδ_pos n))]
      linarith [hδ_pos n]
    have hed : edist x (x + δ_fun n / 2) = ENNReal.ofReal (δ_fun n / 2) := by
      rw [edist_dist, Real.dist_eq, sub_add_cancel_left, abs_neg, abs_of_pos (half_pos (hδ_pos n))]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (half_pos (hδ_pos n)))
      (hed ▸ Metric.edist_le_ediam_of_mem h1 h2)
  have hV_small : ∀ n ∈ F, Metric.ediam (V n) <
      ENNReal.ofReal (1 / (P.Q (polyTreeJ P k + M + 1) : ℝ)) := by
    intro n hn
    have hne : (t n).Nonempty := (Finset.mem_filter.mp hn).2
    have hthick : Metric.ediam (V n) ≤ Metric.ediam (t n) + 2 * ENNReal.ofReal (δ_fun n) := by
      dsimp [V]; simp only [hne, ↓reduceIte]
      exact WeightedExactDim.ediam_thickening_le (hδ_pos n).le
    have hbound_R : Metric.ediam (t n) + 2 * ENNReal.ofReal (δ_fun n) ≤
        ENNReal.ofReal (r₀ + 2 * ((1 / 8 : ℝ) / (P.Q (polyTreeJ P k + M + 1) : ℝ))) := by
      have h1 := ht_diam n
      have h2 : δ_fun n ≤ (1 / 8 : ℝ) / (P.Q (polyTreeJ P k + M + 1) : ℝ) := min_le_right _ _
      calc Metric.ediam (t n) + 2 * ENNReal.ofReal (δ_fun n)
          ≤ ENNReal.ofReal r₀ + ENNReal.ofReal (2 * ((1 / 8 : ℝ) / (P.Q (polyTreeJ P k + M + 1) : ℝ))) := by
            gcongr
            rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
            exact ENNReal.ofReal_le_ofReal (by linarith)
        _ = ENNReal.ofReal (r₀ + 2 * ((1 / 8 : ℝ) / (P.Q (polyTreeJ P k + M + 1) : ℝ))) :=
            (ENNReal.ofReal_add hr₀_pos.le (by positivity)).symm
    have hlt_R : r₀ + 2 * ((1 / 8 : ℝ) / (P.Q (polyTreeJ P k + M + 1) : ℝ)) <
        1 / (P.Q (polyTreeJ P k + M + 1) : ℝ) := by
      dsimp [r₀]
      have h1 : (1 / 2 : ℝ) / (P.Q (polyTreeJ P k + M + 1) : ℝ) +
          2 * ((1 / 8 : ℝ) / (P.Q (polyTreeJ P k + M + 1) : ℝ)) =
          (3 / 4 : ℝ) / (P.Q (polyTreeJ P k + M + 1) : ℝ) := by ring
      rw [h1]
      exact div_lt_div_of_pos_right (by norm_num) hQ_pos
    exact lt_of_le_of_lt (le_trans hthick hbound_R)
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt_R)
  have hcov_low := poly_subtree_inv_pow_le_sum_of_cover P C hb2 M u₀ F V hF_cov hV_pos hV_small
  have hterm_le : ∀ n ∈ F,
      Ctree * (polyInterpGauge P (C.b : ℝ) (Metric.ediam (V n))).toReal ≤
        Ctree * (polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal + (ε : ℝ) / 2 ^ (n + 2) := by
    intro n hn
    have hne : (t n).Nonempty := (Finset.mem_filter.mp hn).2
    have hV_ne_top : Metric.ediam (V n) ≠ ⊤ :=
      ne_of_lt (lt_of_lt_of_le (hV_small n hn) (le_of_lt ENNReal.ofReal_lt_top))
    have ht_ne_top : Metric.ediam (t n) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (ht_diam n) ENNReal.ofReal_lt_top)
    have hthick : Metric.ediam (V n) ≤ Metric.ediam (t n) + 2 * ENNReal.ofReal (δ_fun n) := by
      dsimp [V]; simp only [hne, ↓reduceIte]
      exact WeightedExactDim.ediam_thickening_le (hδ_pos n).le
    have hdiff_R : |(Metric.ediam (V n)).toReal - (Metric.ediam (t n)).toReal| < η_fun n := by
      have hle_V : (Metric.ediam (V n)).toReal ≤ (Metric.ediam (t n)).toReal + 2 * δ_fun n := by
        have hnn : 0 ≤ 2 * δ_fun n := mul_nonneg (by norm_num) (hδ_pos n).le
        have hsum_eq : Metric.ediam (t n) + 2 * ENNReal.ofReal (δ_fun n) =
            ENNReal.ofReal ((Metric.ediam (t n)).toReal + 2 * δ_fun n) := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hnn, ENNReal.ofReal_toReal ht_ne_top,
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        rw [hsum_eq] at hthick
        have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hthick
        have hnn2 : 0 ≤ (Metric.ediam (t n)).toReal + 2 * δ_fun n :=
          add_nonneg ENNReal.toReal_nonneg hnn
        rwa [ENNReal.toReal_ofReal hnn2] at h1
      have hge_V : (Metric.ediam (t n)).toReal ≤ (Metric.ediam (V n)).toReal := by
        apply ENNReal.toReal_mono hV_ne_top
        dsimp [V]; simp only [hne, ↓reduceIte]
        exact Metric.ediam_mono (Metric.self_subset_thickening (hδ_pos n) _)
      rw [abs_of_nonneg (by linarith)]
      have hδ_eta : δ_fun n ≤ η_fun n / 4 := min_le_left _ _
      linarith [hη_pos n]
    have hη_s := hη_spec n (Metric.ediam (V n)).toReal hdiff_R
    have hgV : (polyInterpGauge P (C.b : ℝ) (Metric.ediam (V n))).toReal =
        polyInterpGaugeReal P (C.b : ℝ) (Metric.ediam (V n)).toReal := by
      rw [polyInterpGauge_eq_ofReal_toReal P hb1 hV_ne_top,
        ENNReal.toReal_ofReal (polyInterpGaugeReal_nonneg P hb1 _)]
    have hgt : (polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal =
        polyInterpGaugeReal P (C.b : ℝ) (Metric.ediam (t n)).toReal := by
      rw [polyInterpGauge_eq_ofReal_toReal P hb1 ht_ne_top,
        ENNReal.toReal_ofReal (polyInterpGaugeReal_nonneg P hb1 _)]
    rw [hgV, hgt]
    have h1 := (abs_lt.mp hη_s).2
    have h2 : Ctree * polyInterpGaugeReal P (C.b : ℝ) (Metric.ediam (V n)).toReal ≤
        Ctree * (polyInterpGaugeReal P (C.b : ℝ) (Metric.ediam (t n)).toReal +
          (ε : ℝ) / (2 ^ (n + 2) * Ctree)) := by
      gcongr; linarith
    have heq : Ctree * ((ε : ℝ) / (2 ^ (n + 2) * Ctree)) = (ε : ℝ) / 2 ^ (n + 2) := by
      field_simp
    linarith
  have hsum1 : ((C.b : ℝ) ^ M)⁻¹ ≤
      Ctree * (∑ n ∈ F, (polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal) +
        (ε : ℝ) * (∑ n ∈ F, ((1 / 2 : ℝ) ^ (n + 2))) := by
    have hε2 : ∀ n : ℕ, (ε : ℝ) / 2 ^ (n + 2) = (ε : ℝ) * ((1 / 2 : ℝ) ^ (n + 2)) :=
      fun n => by rw [one_div, inv_pow, div_eq_mul_inv]
    calc ((C.b : ℝ) ^ M)⁻¹
        ≤ ∑ n ∈ F, Ctree * (polyInterpGauge P (C.b : ℝ) (Metric.ediam (V n))).toReal := hcov_low
      _ ≤ ∑ n ∈ F, (Ctree * (polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal +
            (ε : ℝ) / 2 ^ (n + 2)) := Finset.sum_le_sum hterm_le
      _ = Ctree * (∑ n ∈ F, (polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal) +
            (ε : ℝ) * (∑ n ∈ F, ((1 / 2 : ℝ) ^ (n + 2))) := by
          simp_rw [hε2]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hgeom : ∑ n ∈ F, ((1 / 2 : ℝ) ^ (n + 2)) ≤ 1 / 2 := by
    have hsumm : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 2)) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective (fun _ _ h => by omega)
    have hsum_val : (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 2)) = 1 / 2 := by
      have h0 : ∀ n : ℕ, (1 / 2 : ℝ) ^ (n + 2) = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := fun n => by ring
      simp_rw [h0, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)]
      norm_num
    calc ∑ n ∈ F, (1 / 2 : ℝ) ^ (n + 2)
        ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 2) :=
          Summable.sum_le_tsum F (fun _ _ => by positivity) hsumm
      _ = 1 / 2 := hsum_val
  have hsum_t_enn : ENNReal.ofReal (∑ n ∈ F, (polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal) ≤
      ∑' n : ℕ, ⨆ _ : (t n).Nonempty, polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n)) := by
    have hFin : ENNReal.ofReal (∑ n ∈ F, (polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal) =
        ∑ n ∈ F, ⨆ _ : (t n).Nonempty, polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hne : (t n).Nonempty := (Finset.mem_filter.mp hn).2
      have hne_top : polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n)) ≠ ⊤ := by
        have ht_ne : Metric.ediam (t n) ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt (ht_diam n) ENNReal.ofReal_lt_top)
        rw [polyInterpGauge_eq_ofReal_toReal P hb1 ht_ne]
        exact ENNReal.ofReal_ne_top
      rw [ciSup_pos hne, ENNReal.ofReal_toReal hne_top]
    rw [hFin]
    exact ENNReal.sum_le_tsum F
  have hR_bound : ((C.b : ℝ) ^ M)⁻¹ / Ctree ≤
      (∑' n : ℕ, ⨆ _ : (t n).Nonempty, polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal +
        (ε : ℝ) := by
    have hsum_t_real : ∑ n ∈ F, (polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal ≤
        (∑' n : ℕ, ⨆ _ : (t n).Nonempty, polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal := by
      have h1 := ENNReal.toReal_mono htop hsum_t_enn
      rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)] at h1
    have hstep1 : ((C.b : ℝ) ^ M)⁻¹ ≤
        Ctree * (∑' n : ℕ, ⨆ _ : (t n).Nonempty, polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal +
          (ε : ℝ) * (1 / 2) := by
      nlinarith
    have hC1 : 1 ≤ Ctree := by
      have h1 : (1 : ℝ) ≤ (C.b : ℝ) ^ (polyTreeJ P k + 2) :=
        one_le_pow₀ (le_of_lt hb1)
      dsimp [Ctree]; linarith
    have hdiv := div_le_div_of_nonneg_right hstep1 hCtree_pos.le
    calc ((C.b : ℝ) ^ M)⁻¹ / Ctree
        ≤ (Ctree * (∑' n : ℕ, ⨆ _ : (t n).Nonempty,
              polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal +
            (ε : ℝ) * (1 / 2)) / Ctree := hdiv
      _ = (∑' n : ℕ, ⨆ _ : (t n).Nonempty,
              polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal +
            ((ε : ℝ) * (1 / 2)) / Ctree := by field_simp
      _ ≤ (∑' n : ℕ, ⨆ _ : (t n).Nonempty,
              polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal + (ε : ℝ) := by
          gcongr
          calc ((ε : ℝ) * (1 / 2)) / Ctree ≤ ((ε : ℝ) * (1 / 2)) / 1 :=
                div_le_div_of_nonneg_left (by positivity) one_pos hC1
            _ ≤ (ε : ℝ) := by linarith
  calc ENNReal.ofReal (((C.b : ℝ) ^ M)⁻¹ / Ctree)
      ≤ ENNReal.ofReal ((∑' n : ℕ, ⨆ _ : (t n).Nonempty,
            polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))).toReal + (ε : ℝ)) :=
          ENNReal.ofReal_le_ofReal hR_bound
    _ = (∑' n : ℕ, ⨆ _ : (t n).Nonempty, polyInterpGauge P (C.b : ℝ) (Metric.ediam (t n))) +
          (ε : ℝ≥0∞) := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hε_pos.le, ENNReal.ofReal_toReal htop,
            ENNReal.ofReal_coe_nnreal]

/-- Cantor 树内任一点 `x` 在所有充分大指标处满足 `round(Q_j x)` 与缺陷精确匹配 `C.digit`，且 `u_j(x) → 0`。 -/
lemma polyCantorSet_spec (P : PolyRecData) {k : ℕ} (C : PolyDigitCode k) {x : ℝ}
    (hx : x ∈ polyCantorSet P C) :
    ∃ w : ℕ → Fin C.b,
      Tendsto (P.polyEps x) atTop (nhds 0) ∧
      (∀ n : ℕ, round ((P.Q (polyTreeJ P k + n + 1) : ℝ) * x) =
        polyCenterInt P C n (polyPrefix n w)) ∧
      (∀ n : ℕ, P.polyDefect x (polyTreeJ P k + n + 2) = C.digit (w (n + 1))) := by
  obtain ⟨w, hw⟩ := hx
  have hQ_pos : ∀ j : ℕ, (0 : ℝ) < (P.Q j : ℝ) := fun j => by exact_mod_cast P.hQ_pos j
  have hrad_mul_lt : ∀ n : ℕ,
      (P.Q (polyTreeJ P k + n + 1) : ℝ) * polyRadC P k n < 1 / 4 := by
    intro n
    have h2 := polyRadC_twice_lt P k n
    have hQ := hQ_pos (polyTreeJ P k + n + 1)
    have hmul := mul_lt_mul_of_pos_left h2 hQ
    have hlhs : (P.Q (polyTreeJ P k + n + 1) : ℝ) * (2 * polyRadC P k n) =
        2 * ((P.Q (polyTreeJ P k + n + 1) : ℝ) * polyRadC P k n) := by ring
    have hrhs : (P.Q (polyTreeJ P k + n + 1) : ℝ) *
        ((1 / 2 : ℝ) / (P.Q (polyTreeJ P k + n + 1) : ℝ)) = 1 / 2 := by field_simp
    linarith
  have hround : ∀ n : ℕ, round ((P.Q (polyTreeJ P k + n + 1) : ℝ) * x) =
      polyCenterInt P C n (polyPrefix n w) := by
    intro n
    have hxn := hw n
    have hdiff : |x - polyCenter P C n (polyPrefix n w)| ≤ polyRadC P k n :=
      abs_sub_le_iff.mpr ⟨by linarith [hxn.2], by linarith [hxn.1]⟩
    have hQ := hQ_pos (polyTreeJ P k + n + 1)
    have hmul : |(P.Q (polyTreeJ P k + n + 1) : ℝ) * x -
        (polyCenterInt P C n (polyPrefix n w) : ℝ)| ≤
        (P.Q (polyTreeJ P k + n + 1) : ℝ) * polyRadC P k n := by
      unfold polyCenter at hdiff
      have heq : (P.Q (polyTreeJ P k + n + 1) : ℝ) * x -
          (polyCenterInt P C n (polyPrefix n w) : ℝ) =
          (P.Q (polyTreeJ P k + n + 1) : ℝ) *
            (x - (polyCenterInt P C n (polyPrefix n w) : ℝ) /
              (P.Q (polyTreeJ P k + n + 1) : ℝ)) := by field_simp
      rw [heq, abs_mul, abs_of_pos hQ]
      exact mul_le_mul_of_nonneg_left hdiff hQ.le
    exact poly_round_eq_of_abs_sub_lt_half (lt_of_le_of_lt hmul (lt_trans (hrad_mul_lt n) (by norm_num)))
  have hratio_zero : Tendsto (fun n : ℕ =>
      (P.Q (polyTreeJ P k + n + 1) : ℝ) / (P.Q (polyTreeJ P k + n + 2) : ℝ)) atTop (nhds 0) := by
    have hA_top : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hbound : ∀ n : ℕ,
        0 ≤ (P.Q (polyTreeJ P k + n + 1) : ℝ) / (P.Q (polyTreeJ P k + n + 2) : ℝ) ∧
        (P.Q (polyTreeJ P k + n + 1) : ℝ) / (P.Q (polyTreeJ P k + n + 2) : ℝ) ≤
          2 / ((n : ℝ) + 1) := by
      intro n
      have hQ1 := hQ_pos (polyTreeJ P k + n + 1)
      have hQ2 := hQ_pos (polyTreeJ P k + n + 2)
      refine ⟨div_nonneg hQ1.le hQ2.le, ?_⟩
      have hJ₁ : P.J₁ ≤ polyTreeJ P k + n + 1 := by
        have := polyTreeJ_ge_J₁ P k; omega
      have hJ₀ : P.J₀ ≤ polyTreeJ P k + n + 1 := by
        have := polyTreeJ_ge_J₀_succ P k; omega
      have hgt : (P.A (polyTreeJ P k + n + 1) : ℝ) * (P.Q (polyTreeJ P k + n + 1) : ℝ) <
          (P.Q (polyTreeJ P k + n + 2) : ℝ) := by
        exact_mod_cast P.poly_Q_succ_gt_A_mul hJ₀
      have hA_lo := P.poly_A_ge_half_c hJ₁
      have hc1 : (1 : ℝ) ≤ (P.c : ℝ) := by exact_mod_cast P.hc
      have hn1_le : (n : ℝ) + 1 ≤ ((polyTreeJ P k + n + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have hj1 : (1 : ℝ) ≤ ((polyTreeJ P k + n + 1 : ℕ) : ℝ) := by linarith
      have hjr : ((polyTreeJ P k + n + 1 : ℕ) : ℝ) ≤ ((polyTreeJ P k + n + 1 : ℕ) : ℝ) ^ P.r := by
        calc ((polyTreeJ P k + n + 1 : ℕ) : ℝ) = ((polyTreeJ P k + n + 1 : ℕ) : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ ((polyTreeJ P k + n + 1 : ℕ) : ℝ) ^ P.r := pow_le_pow_right₀ hj1 P.hr
      have hA_ge : ((n : ℝ) + 1) / 2 ≤ (P.A (polyTreeJ P k + n + 1) : ℝ) := by nlinarith
      have hmul_pos : 0 < ((n : ℝ) + 1) / 2 := by positivity
      rw [div_le_div_iff₀ hQ2 (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith
    have hzero : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_div_atTop 2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
      (Filter.Eventually.of_forall fun n => (hbound n).1)
      (Filter.Eventually.of_forall fun n => (hbound n).2)
  have heps : Tendsto (P.polyEps x) atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ => P.polyEps x (polyTreeJ P k + n + 1)) atTop (nhds 0) := by
      have hrad_zero : Tendsto (fun n : ℕ =>
          (2 * (k : ℝ) + 2) * ((P.Q (polyTreeJ P k + n + 1) : ℝ) /
            (P.Q (polyTreeJ P k + n + 2) : ℝ))) atTop (nhds 0) := by
        simpa using hratio_zero.const_mul (2 * (k : ℝ) + 2)
      have hnorm : Tendsto (fun n : ℕ => |P.polyEps x (polyTreeJ P k + n + 1)|) atTop (nhds 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrad_zero
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (Filter.Eventually.of_forall fun n => ?_)
        have hxn := hw n
        have hdiff : |x - polyCenter P C n (polyPrefix n w)| ≤ polyRadC P k n :=
          abs_sub_le_iff.mpr ⟨by linarith [hxn.2], by linarith [hxn.1]⟩
        have hQ := hQ_pos (polyTreeJ P k + n + 1)
        unfold PolyRecData.polyEps
        rw [hround n]
        have heq : (P.Q (polyTreeJ P k + n + 1) : ℝ) * x -
            (polyCenterInt P C n (polyPrefix n w) : ℝ) =
            (P.Q (polyTreeJ P k + n + 1) : ℝ) *
              (x - polyCenter P C n (polyPrefix n w)) := by
          unfold polyCenter; field_simp
        rw [heq, abs_mul, abs_of_pos hQ]
        calc (P.Q (polyTreeJ P k + n + 1) : ℝ) * |x - polyCenter P C n (polyPrefix n w)|
            ≤ (P.Q (polyTreeJ P k + n + 1) : ℝ) * polyRadC P k n :=
              mul_le_mul_of_nonneg_left hdiff hQ.le
          _ = (2 * (k : ℝ) + 2) * ((P.Q (polyTreeJ P k + n + 1) : ℝ) /
                (P.Q (polyTreeJ P k + n + 2) : ℝ)) := by
              unfold polyRadC; ring
      exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hnorm)
    have hid : (fun n : ℕ => P.polyEps x (n + (polyTreeJ P k + 1))) =
        (fun n : ℕ => P.polyEps x (polyTreeJ P k + n + 1)) := by
      ext n; congr 1; omega
    rw [← hid] at hshift
    exact (tendsto_add_atTop_iff_nat (polyTreeJ P k + 1)).mp hshift
  have hdef : ∀ n : ℕ, P.polyDefect x (polyTreeJ P k + n + 2) = C.digit (w (n + 1)) := by
    intro n
    unfold PolyRecData.polyDefect
    have hidx1 : polyTreeJ P k + n + 2 + 1 = polyTreeJ P k + (n + 2) + 1 := by omega
    have hidx2 : polyTreeJ P k + n + 2 = polyTreeJ P k + (n + 1) + 1 := by omega
    have hidx0 : polyTreeJ P k + (n + 1) + 1 - 1 = polyTreeJ P k + n + 1 := by omega
    rw [hidx1, hidx2, hround (n + 2), hround (n + 1), hidx0, hround n]
    have hpre2 : (fun i : Fin (n + 1) => (polyPrefix (n + 2) w) i.castSucc) = polyPrefix (n + 1) w := rfl
    have hlast : polyPrefix (n + 2) w (Fin.last (n + 1)) = w (n + 1) := rfl
    have hfst : (polyPairOfWord P C (n + 1) (polyPrefix (n + 1) w)).1 =
        polyCenterInt P C n (polyPrefix n w) :=
      polyPairOfWord_fst_succ P C n _
    change (polyPairOfWord P C (n + 2) (polyPrefix (n + 2) w)).2 -
        P.A (polyTreeJ P k + (n + 1) + 1) * (polyPairOfWord P C (n + 1) (polyPrefix (n + 1) w)).2 -
        (polyPairOfWord P C n (polyPrefix n w)).2 = C.digit (w (n + 1))
    rw [show polyPairOfWord P C (n + 2) (polyPrefix (n + 2) w) =
        let p := polyPairOfWord P C (n + 1) (fun i : Fin (n + 1) => (polyPrefix (n + 2) w) i.castSucc)
        (p.2, P.A (polyTreeJ P k + (n + 1) + 1) * p.2 + p.1 +
          C.digit (polyPrefix (n + 2) w (Fin.last (n + 1)))) from rfl, hpre2, hlast]
    dsimp only
    rw [show (polyPairOfWord P C (n + 1) (polyPrefix (n + 1) w)).1 =
        (polyPairOfWord P C n (polyPrefix n w)).2 from hfst]
    ring
  exact ⟨w, heps, hround, hdef⟩

lemma polyCantorSet_exact_subset_levelSet (P : PolyRecData) (k : ℕ) :
    polyCantorSet P (PolyDigitCode.exact k) ⊆
      {x : ℝ | P.polyApprExponent x ≤ ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))} := by
  intro x hx
  obtain ⟨w, heps, _, hdef⟩ := polyCantorSet_spec P (PolyDigitCode.exact k) hx
  have happrox := P.poly_abs_defect_approx x heps
  have hev_bound : ∀ᶠ j : ℕ in atTop,
      (P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x) ≤
        (k : ℝ) + |(P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x) -
          (|(P.polyDefect x j : ℝ)|)| := by
    filter_upwards [eventually_ge_atTop (polyTreeJ P k + 2)] with j hj
    obtain ⟨n, rfl⟩ : ∃ n, j = polyTreeJ P k + n + 2 := ⟨j - (polyTreeJ P k + 2), by omega⟩
    have hd : |(P.polyDefect x (polyTreeJ P k + n + 2) : ℝ)| ≤ (k : ℝ) := by
      rw [hdef n]
      exact_mod_cast (PolyDigitCode.exact k).abs_le (w (n + 1))
    have h1 := le_abs_self ((P.c : ℝ) * ((polyTreeJ P k + n + 2 : ℕ) : ℝ) ^ P.r *
      distToNearestInt ((P.Q (polyTreeJ P k + n + 2) : ℝ) * x) -
      |(P.polyDefect x (polyTreeJ P k + n + 2) : ℝ)|)
    linarith
  have hc_pos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε_pos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hev_err : ∀ᶠ j : ℕ in atTop,
      |(P.polyDefect x j : ℝ)| -
        (P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x) ∈
        Metric.ball (0 : ℝ) ((P.c : ℝ) * (ε : ℝ)) :=
    happrox.eventually (Metric.ball_mem_nhds 0 (mul_pos hc_pos hε_pos))
  have hev_seq : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (P.polyWeightedSeq (P.r : ℝ) x j) ≤
        ENNReal.ofReal ((k : ℝ) / (P.c : ℝ)) + (ε : ℝ≥0∞) := by
    filter_upwards [hev_bound, hev_err] with j hbd herr
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_sub_comm] at herr
    have hle_R : (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j ≤
        (k : ℝ) + (P.c : ℝ) * (ε : ℝ) := by
      have hid : (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j =
          (P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x) := by
        dsimp [PolyRecData.polyWeightedSeq]; rw [Real.rpow_natCast]; ring
      linarith [herr.le]
    have hdiv : P.polyWeightedSeq (P.r : ℝ) x j ≤ (k : ℝ) / (P.c : ℝ) + (ε : ℝ) := by
      have h1 := div_le_div_of_nonneg_right hle_R hc_pos.le
      have heq1 : ((P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j) / (P.c : ℝ) =
          P.polyWeightedSeq (P.r : ℝ) x j := by field_simp
      have heq2 : ((k : ℝ) + (P.c : ℝ) * (ε : ℝ)) / (P.c : ℝ) =
          (k : ℝ) / (P.c : ℝ) + (ε : ℝ) := by field_simp
      linarith
    calc ENNReal.ofReal (P.polyWeightedSeq (P.r : ℝ) x j)
        ≤ ENNReal.ofReal ((k : ℝ) / (P.c : ℝ) + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hdiv
      _ = ENNReal.ofReal ((k : ℝ) / (P.c : ℝ)) + (ε : ℝ≥0∞) := by
          rw [ENNReal.ofReal_add (by positivity) hε_pos.le, ENNReal.ofReal_coe_nnreal]
  exact limsup_le_of_le (by isBoundedDefault) hev_seq

lemma polyCantorSet_binary_subset_unsignedExactLimit (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    polyCantorSet P (PolyDigitCode.binary k hk) ⊆
      polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) := by
  intro x hx
  obtain ⟨w, heps, _, hdef⟩ := polyCantorSet_spec P (PolyDigitCode.binary k hk) hx
  rw [poly_unsigned_exact_limit_iff_defect_binary]
  refine ⟨heps, ?_⟩
  filter_upwards [eventually_ge_atTop (polyTreeJ P k + 2)] with j hj
  obtain ⟨n, rfl⟩ : ∃ n, j = polyTreeJ P k + n + 2 := ⟨j - (polyTreeJ P k + 2), by omega⟩
  rw [hdef n]
  exact GaugeCircle.binDigitOf_mem_binary k (w (n + 1))

/-- 通用局部无穷测度提升引理：只要紧致 Cantor 树 `polyCantorSet P C ⊆ E`（$2 \le C.b$）且 $E$ 在
    $L^{(r,c,d)}$ 下平移不变，则对任意非空开区间 `(a, b)` 均有 $\mathcal{H}^{g_b}(E \cap (a, b)) = \infty$。 -/
theorem mkMetric_poly_inter_Ioo_eq_top_of_compact_tree (P : PolyRecData) {k : ℕ}
    (C : PolyDigitCode k) (hb2 : 2 ≤ C.b)
    {E : Set ℝ} (hKE : polyCantorSet P C ⊆ E)
    (hE_inv : ∀ {y : ℝ}, y ∈ P.latticePoly → (fun x : ℝ => x + y) ⁻¹' E = E)
    {a b : ℝ} (hab : a < b) :
    Measure.mkMetric (polyInterpGauge P (C.b : ℝ)) (E ∩ Set.Ioo a b) = ⊤ := by
  have hb_pos : (0 : ℝ) < (C.b : ℝ) := by exact_mod_cast C.hb
  have hb1 : (1 : ℝ) < (C.b : ℝ) := by exact_mod_cast (by omega : 1 < C.b)
  set h := polyInterpGauge P (C.b : ℝ)
  set Ctree : ℝ := 2 * (C.b : ℝ) ^ (polyTreeJ P k + 2)
  have hCtree_pos : 0 < Ctree := by positivity
  -- Prove ∀ R : ℝ, ENNReal.ofReal R ≤ Measure.mkMetric h (E ∩ Ioo a b)
  rw [eq_top_iff]
  refine le_of_forall_lt fun R hR => ?_
  have hR_ne_top : R ≠ ⊤ := hR.ne
  -- Need M so large that ⌊(b - a)/(3 * radC M)⌋ * (b^M)⁻¹ / Ctree > R.toReal
  have hdiv0 : Tendsto (fun M : ℕ =>
      (C.b : ℝ) ^ M / (P.Q (polyTreeJ P k + M + 2) : ℝ)) atTop (nhds 0) := by
    have h0 := poly_pow_div_Q_of_base_tendsto_zero P (C.b : ℝ)
    have h0' : Tendsto (fun M : ℕ =>
        (C.b : ℝ) ^ (M + (polyTreeJ P k + 2)) / (P.Q (M + (polyTreeJ P k + 2)) : ℝ))
        atTop (nhds 0) := h0.comp (tendsto_add_atTop_nat (polyTreeJ P k + 2))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0' ?_ ?_
    · intro M
      exact div_nonneg (pow_nonneg hb_pos.le _)
        (le_of_lt (Int.cast_pos.mpr (P.hQ_pos (polyTreeJ P k + M + 2))))
    · intro M
      have hidx : polyTreeJ P k + M + 2 = M + (polyTreeJ P k + 2) := by omega
      dsimp only
      rw [hidx]
      have hQpos : (0 : ℝ) < (P.Q (M + (polyTreeJ P k + 2)) : ℝ) := by exact_mod_cast P.hQ_pos _
      have hpow : (C.b : ℝ) ^ M ≤ (C.b : ℝ) ^ (M + (polyTreeJ P k + 2)) :=
        pow_le_pow_right₀ hb1.le (by omega)
      exact div_le_div_of_nonneg_right hpow hQpos.le
  -- Specifically Q_{J+M+2} / b^M → ∞! Wait: simpler, b^M / Q_{J+M+2} < ε!
  set goal_R : ℝ := max R.toReal 1
  have hgoal_pos : 0 < goal_R := lt_of_lt_of_le one_pos (le_max_right _ _)
  set eps : ℝ := (b - a) / (12 * (2 * (k : ℝ) + 2) * Ctree * goal_R)
  have heps_pos : 0 < eps := by positivity
  obtain ⟨M, hM⟩ := (hdiv0.eventually (Iio_mem_nhds heps_pos)).exists
  let u₀ : Fin M → Fin C.b := fun _ => ⟨0, C.hb⟩
  have hsub_pos := mkMetric_polyWordTree_subtree_pos P C hb2 M u₀
  have hK_closed : IsClosed (polyCantorSet P C ∩ polyCInterv P C M u₀) :=
    (polyCantorSet_isClosed P C).inter (polyCInterv_isClosed P C M u₀)
  set N : ℕ := Nat.floor ((b - a) / (3 * polyRadC P k M))
  obtain ⟨tvec, htL, htI, hdisj⟩ := exists_disjoint_latticePoly_translates_in_Ioo P
    (c := polyCenter P C M u₀) (r := polyRadC P k M) hab (polyRadC_pos P k M)
  let piece : Fin N → Set ℝ := fun i =>
    (fun x : ℝ => x + tvec i) '' (polyCantorSet P C ∩ polyCInterv P C M u₀)
  have hpiece_meas : ∀ i : Fin N, MeasurableSet (piece i) := fun i => by
    have hcls : IsClosed (piece i) := by
      have himg : piece i = (fun y : ℝ => y - tvec i) ⁻¹' (polyCantorSet P C ∩ polyCInterv P C M u₀) := by
        ext y; simp [piece, sub_eq_add_neg]
      rw [himg]
      exact hK_closed.preimage (continuous_id.sub continuous_const)
    exact hcls.measurableSet
  have hpiece_sub : ∀ i : Fin N, piece i ⊆ E ∩ Set.Ioo a b := by
    intro i y hy
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨?_, htI i ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩⟩
    have hxE : x ∈ E := hKE hx.1
    rw [← hE_inv (htL i)] at hxE
    exact hxE
  have hpiece_disj : Pairwise (fun i j => Disjoint (piece i) (piece j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun y hyi hyj => ?_
    rcases hyi with ⟨xi, hxi, rfl⟩
    rcases hyj with ⟨xj, hxj, heq⟩
    have hmem_i : xi + tvec i ∈ Set.Icc (polyCenter P C M u₀ + tvec i - polyRadC P k M)
        (polyCenter P C M u₀ + tvec i + polyRadC P k M) :=
      ⟨by linarith [hxi.2.1], by linarith [hxi.2.2]⟩
    have hmem_j : xi + tvec i ∈ Set.Icc (polyCenter P C M u₀ + tvec j - polyRadC P k M)
        (polyCenter P C M u₀ + tvec j + polyRadC P k M) := by
      change xj + tvec j = xi + tvec i at heq
      rw [← heq]
      exact ⟨by linarith [hxj.2.1], by linarith [hxj.2.2]⟩
    exact Set.disjoint_left.mp (hdisj hij) hmem_i hmem_j
  have hUnion_sub : (⋃ i : Fin N, piece i) ⊆ E ∩ Set.Ioo a b :=
    Set.iUnion_subset hpiece_sub
  have hmeas_sum : (∑ i : Fin N, Measure.mkMetric h (piece i)) ≤
      Measure.mkMetric h (E ∩ Set.Ioo a b) := by
    calc (∑ i : Fin N, Measure.mkMetric h (piece i))
        = ∑' i : Fin N, Measure.mkMetric h (piece i) := (tsum_fintype _).symm
      _ = Measure.mkMetric h (⋃ i : Fin N, piece i) := (measure_iUnion hpiece_disj hpiece_meas).symm
      _ ≤ Measure.mkMetric h (E ∩ Set.Ioo a b) := measure_mono hUnion_sub
  have hpiece_eq : ∀ i : Fin N, Measure.mkMetric h (piece i) =
      Measure.mkMetric h (polyCantorSet P C ∩ polyCInterv P C M u₀) := fun i => by
    dsimp [piece]
    simpa [add_comm] using GaugeExact.mkMetric_image_add h (tvec i)
      (polyCantorSet P C ∩ polyCInterv P C M u₀)
  have hN_ge : (N : ℝ) * (((C.b : ℝ) ^ M)⁻¹ / Ctree) > goal_R := by
    have hQ2 : (0 : ℝ) < (P.Q (polyTreeJ P k + M + 2) : ℝ) := by exact_mod_cast P.hQ_pos _
    have hinv_gt : 1 / eps < (P.Q (polyTreeJ P k + M + 2) : ℝ) / (C.b : ℝ) ^ M := by
      have hpos : 0 < (C.b : ℝ) ^ M / (P.Q (polyTreeJ P k + M + 2) : ℝ) := by positivity
      have h1 := one_div_lt_one_div_of_lt hpos hM
      have hrhs : 1 / ((C.b : ℝ) ^ M / (P.Q (polyTreeJ P k + M + 2) : ℝ)) =
          (P.Q (polyTreeJ P k + M + 2) : ℝ) / (C.b : ℝ) ^ M := one_div_div _ _
      linarith [h1, hrhs]
    have hN_gt : (b - a) / (3 * polyRadC P k M) - 1 < (N : ℝ) := by
      dsimp [N]; linarith [Nat.lt_floor_add_one ((b - a) / (3 * polyRadC P k M))]
    have hratio_eq : ((b - a) / (3 * polyRadC P k M)) * (((C.b : ℝ) ^ M)⁻¹ / Ctree) =
        ((b - a) / (3 * (2 * (k : ℝ) + 2) * Ctree)) *
          ((P.Q (polyTreeJ P k + M + 2) : ℝ) / (C.b : ℝ) ^ M) := by
      unfold polyRadC
      field_simp
    have hbig : 4 * goal_R <
        ((b - a) / (3 * polyRadC P k M)) * (((C.b : ℝ) ^ M)⁻¹ / Ctree) := by
      rw [hratio_eq]
      have hmul := mul_lt_mul_of_pos_left hinv_gt
        (by positivity : 0 < (b - a) / (3 * (2 * (k : ℝ) + 2) * Ctree))
      have heq4 : ((b - a) / (3 * (2 * (k : ℝ) + 2) * Ctree)) * (1 / eps) = 4 * goal_R := by
        dsimp [eps]; field_simp; ring
      linarith
    have h1 : (((C.b : ℝ) ^ M)⁻¹ / Ctree) ≤ 1 := by
      have hC1 : 1 ≤ Ctree := by
        have h1' : (1 : ℝ) ≤ (C.b : ℝ) ^ (polyTreeJ P k + 2) := one_le_pow₀ hb1.le
        dsimp [Ctree]; linarith
      have hbM1 : 1 ≤ (C.b : ℝ) ^ M := one_le_pow₀ hb1.le
      calc (((C.b : ℝ) ^ M)⁻¹ / Ctree) ≤ 1 / 1 := by
            gcongr
            exact inv_le_one_of_one_le₀ hbM1
        _ = 1 := by norm_num
    have hpos_m : 0 < ((C.b : ℝ) ^ M)⁻¹ / Ctree := by positivity
    have hgoal1 : 1 ≤ goal_R := le_max_right _ _
    have hNm := mul_lt_mul_of_pos_right hN_gt hpos_m
    linarith [mul_sub_right_distrib ((b - a) / (3 * polyRadC P k M)) 1 (((C.b : ℝ) ^ M)⁻¹ / Ctree),
      one_mul (((C.b : ℝ) ^ M)⁻¹ / Ctree)]
  have hR_lt_prod : R < ENNReal.ofReal ((N : ℝ) * (((C.b : ℝ) ^ M)⁻¹ / Ctree)) := by
    calc R ≤ ENNReal.ofReal goal_R := by
          rw [← ENNReal.ofReal_toReal hR_ne_top]
          exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
      _ < ENNReal.ofReal ((N : ℝ) * (((C.b : ℝ) ^ M)⁻¹ / Ctree)) :=
          (ENNReal.ofReal_lt_ofReal_iff (lt_trans hgoal_pos hN_ge)).mpr hN_ge
  have hprod_le : ENNReal.ofReal ((N : ℝ) * (((C.b : ℝ) ^ M)⁻¹ / Ctree)) ≤
      Measure.mkMetric h (E ∩ Set.Ioo a b) := by
    calc ENNReal.ofReal ((N : ℝ) * (((C.b : ℝ) ^ M)⁻¹ / Ctree))
        = ((N : ℕ) : ℝ≥0∞) * ENNReal.ofReal (((C.b : ℝ) ^ M)⁻¹ / Ctree) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
      _ ≤ ((N : ℕ) : ℝ≥0∞) * Measure.mkMetric h (polyCantorSet P C ∩ polyCInterv P C M u₀) := by
          gcongr
      _ = ∑ i : Fin N, Measure.mkMetric h (piece i) := by
          simp [hpiece_eq, Finset.sum_const]
      _ ≤ Measure.mkMetric h (E ∩ Set.Ioo a b) := hmeas_sum
  exact lt_of_lt_of_le hR_lt_prod hprod_le


/-! ### 5.2 `thm:poly-gauge-trichotomy(i),(ii)`、`cor:poly-exact-gauge` 与 `cor:poly-liminf-gauges` 完整汇集 -/

/-- 圆周 $\mathbb{R}/\mathbb{Z}$ 上的严格子水平集、子水平集、精确水平集与无符号精确极限集。 -/
def polyCircleStrictLevel (P : PolyRecData) (k : ℕ) : Set UnitAddCircle :=
  circleProj '' polyStrictLevel P k

def polyCircleLevelSet (P : PolyRecData) (k : ℕ) : Set UnitAddCircle :=
  circleProj '' {x : ℝ | P.polyApprExponent x ≤ ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))}

def polyCircleExactLevel (P : PolyRecData) (k : ℕ) : Set UnitAddCircle :=
  circleProj '' polyExactLevel P k

def polyCircleUnsignedExactLimitSet (P : PolyRecData) (t : ℝ) : Set UnitAddCircle :=
  circleProj '' polyUnsignedExactLimitSet P t

/-- **`thm:poly-gauge-trichotomy`(i) `ℝ` 上任意非空开区间无穷测度**（先对子水平集、再减去零测严格子水平集）。 -/
theorem mkMetric_polyCritGauge_polyExactLevel_inter_Ioo_eq_top (P : PolyRecData)
    {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (hab : a < b) :
    Measure.mkMetric (polyCritGauge P k) (polyExactLevel P k ∩ Set.Ioo a b) = ⊤ := by
  have hsub_eq_top : Measure.mkMetric (polyCritGauge P k)
      ({x : ℝ | P.polyApprExponent x ≤ ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))} ∩ Set.Ioo a b) = ⊤ := by
    have hCode := mkMetric_poly_inter_Ioo_eq_top_of_compact_tree P (PolyDigitCode.exact k)
      (by simp [PolyDigitCode.exact]; omega) (polyCantorSet_exact_subset_levelSet P k)
      (fun {y} hy => by
        ext x
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, PolyRecData.polyApprExponent,
          polyWeightedExponent_add_latticePoly P (P.r : ℝ) x hy])
      hab
    simpa [polyCritGauge, PolyDigitCode.exact] using hCode
  have hcov : {x : ℝ | P.polyApprExponent x ≤ ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))} ∩ Set.Ioo a b ⊆
      (polyExactLevel P k ∩ Set.Ioo a b) ∪ polyStrictLevel P k := by
    rintro x ⟨hx_le, hxI⟩
    rcases eq_or_lt_of_le (show P.polyApprExponent x ≤ ENNReal.ofReal ((k : ℝ) / (P.c : ℝ)) from hx_le) with h_eq | h_lt
    · exact Or.inl ⟨h_eq, hxI⟩
    · exact Or.inr h_lt
  have hle : Measure.mkMetric (polyCritGauge P k)
      ({x : ℝ | P.polyApprExponent x ≤ ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))} ∩ Set.Ioo a b) ≤
      Measure.mkMetric (polyCritGauge P k) (polyExactLevel P k ∩ Set.Ioo a b) +
        Measure.mkMetric (polyCritGauge P k) (polyStrictLevel P k) :=
    le_trans (measure_mono hcov) (measure_union_le _ _)
  rw [hsub_eq_top, mkMetric_polyCritGauge_polyStrictLevel_null P hk, add_zero] at hle
  exact eq_top_iff.mpr hle

theorem mkMetric_polyCritGauge_polyExactLevel_eq_top (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (polyCritGauge P k) (polyExactLevel P k) = ⊤ := by
  rw [eq_top_iff, ← mkMetric_polyCritGauge_polyExactLevel_inter_Ioo_eq_top P hk zero_lt_one]
  exact measure_mono Set.inter_subset_left

theorem mkMetric_polyCritGauge_polyExactLevel_pos (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    0 < Measure.mkMetric (polyCritGauge P k) (polyExactLevel P k) := by
  rw [mkMetric_polyCritGauge_polyExactLevel_eq_top P hk]
  exact ENNReal.zero_lt_top

theorem mkMetric_polyCritGauge_polyExactLevel_inter_open_eq_top (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k)
    {U : Set ℝ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    Measure.mkMetric (polyCritGauge P k) (polyExactLevel P k ∩ U) = ⊤ := by
  obtain ⟨x₀, hx₀⟩ := hU_ne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU_open x₀ hx₀
  have hsub : Set.Ioo (x₀ - ε) (x₀ + ε) ⊆ U := fun y hy => by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  rw [eq_top_iff, ← mkMetric_polyCritGauge_polyExactLevel_inter_Ioo_eq_top P hk
    (by linarith : x₀ - ε < x₀ + ε)]
  exact measure_mono (Set.inter_subset_inter_right _ hsub)

/-- **`thm:poly-gauge-trichotomy`(ii) `ℝ` 上普适二进规范 $g_2$ 任意非空开区间/开集无穷测度**。 -/
theorem mkMetric_polyBinaryGauge_unsignedExactLimit_inter_Ioo_eq_top (P : PolyRecData)
    {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (hab : a < b) :
    Measure.mkMetric (polyBinaryGauge P)
      (polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ Set.Ioo a b) = ⊤ := by
  have hCode := mkMetric_poly_inter_Ioo_eq_top_of_compact_tree P (PolyDigitCode.binary k hk)
    (by simp [PolyDigitCode.binary]) (polyCantorSet_binary_subset_unsignedExactLimit P hk)
    (fun {y} hy => polyUnsignedExactLimit_add_latticePoly P _ hy) hab
  simpa [polyBinaryGauge, PolyDigitCode.binary] using hCode

theorem mkMetric_polyBinaryGauge_unsignedExactLimit_eq_top (P : PolyRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (polyBinaryGauge P)
      (polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ))) = ⊤ := by
  rw [eq_top_iff, ← mkMetric_polyBinaryGauge_unsignedExactLimit_inter_Ioo_eq_top P hk zero_lt_one]
  exact measure_mono Set.inter_subset_left

theorem mkMetric_polyBinaryGauge_unsignedExactLimit_pos (P : PolyRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    0 < Measure.mkMetric (polyBinaryGauge P)
      (polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ))) := by
  rw [mkMetric_polyBinaryGauge_unsignedExactLimit_eq_top P hk]
  exact ENNReal.zero_lt_top

theorem mkMetric_polyBinaryGauge_unsignedExactLimit_inter_open_eq_top (P : PolyRecData)
    {k : ℕ} (hk : 1 ≤ k) {U : Set ℝ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    Measure.mkMetric (polyBinaryGauge P)
      (polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ U) = ⊤ := by
  obtain ⟨x₀, hx₀⟩ := hU_ne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU_open x₀ hx₀
  have hsub : Set.Ioo (x₀ - ε) (x₀ + ε) ⊆ U := fun y hy => by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  rw [eq_top_iff, ← mkMetric_polyBinaryGauge_unsignedExactLimit_inter_Ioo_eq_top P hk
    (by linarith : x₀ - ε < x₀ + ε)]
  exact measure_mono (Set.inter_subset_inter_right _ hsub)

/-- 圆周 $\mathbb{R}/\mathbb{Z}$ 上的 `thm:poly-gauge-trichotomy`(i) 完整结论。 -/
theorem mkMetric_polyCritGauge_polyCircleStrictLevel_null (P : PolyRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (polyCritGauge P k) (polyCircleStrictLevel P k) = 0 :=
  le_antisymm ((mkMetric_circleProj_image_le (polyCritGauge P k) (polyCritGauge_mono P k hk) _).trans_eq
    (mkMetric_polyCritGauge_polyStrictLevel_null P hk)) bot_le

theorem mkMetric_polyCritGauge_polyCircleExactLevel_inter_open_eq_top (P : PolyRecData)
    {k : ℕ} (hk : 1 ≤ k) {U : Set UnitAddCircle} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    Measure.mkMetric (polyCritGauge P k) (polyCircleExactLevel P k ∩ U) = ⊤ := by
  obtain ⟨a, b, hab, hwidth, hsub⟩ := exists_Ioo_subset_preimage_of_isOpen_circle hU_open hU_ne
  set A : Set ℝ := polyExactLevel P k ∩ Set.Ioo a b
  have hA_img : circleProj '' A ⊆ polyCircleExactLevel P k ∩ U := by
    rintro _ ⟨x, ⟨hxE, hxI⟩, rfl⟩
    exact ⟨⟨x, hxE, rfl⟩, hsub hxI⟩
  have hle := le_trans
    (mkMetric_le_circleProj_image_of_subset_Ioo (polyCritGauge P k) (polyCritGauge_mono P k hk)
      hwidth Set.inter_subset_right)
    (measure_mono hA_img)
  rw [mkMetric_polyCritGauge_polyExactLevel_inter_Ioo_eq_top P hk hab] at hle
  exact eq_top_iff.mpr hle

theorem mkMetric_polyCritGauge_polyCircleExactLevel_eq_top (P : PolyRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (polyCritGauge P k) (polyCircleExactLevel P k) = ⊤ := by
  have h1 := mkMetric_polyCritGauge_polyCircleExactLevel_inter_open_eq_top P hk isOpen_univ
    ⟨0, Set.mem_univ _⟩
  simpa using h1

theorem polyCircleExactLevel_critGauge_sigma_finite (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    ∃ E : ℕ → Set UnitAddCircle, polyCircleExactLevel P k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (polyCritGauge P k) (E i) < ⊤ := by
  obtain ⟨E, hcov, hfin⟩ := polyExactLevel_critGauge_sigma_finite P hk
  refine ⟨fun i => circleProj '' (E i), ?_, fun i => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
  · exact lt_of_le_of_lt (mkMetric_circleProj_image_le (polyCritGauge P k)
      (polyCritGauge_mono P k hk) _) (hfin i)

/-- 圆周 $\mathbb{R}/\mathbb{Z}$ 上的 `thm:poly-gauge-trichotomy`(ii) 完整结论。 -/
theorem mkMetric_polyCircleUnsignedExactLimit_null_of_critGauge (P : PolyRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (polyCritGauge P k)
      (polyCircleUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ))) = 0 :=
  le_antisymm ((mkMetric_circleProj_image_le (polyCritGauge P k) (polyCritGauge_mono P k hk) _).trans_eq
    (mkMetric_polyUnsignedExactLimit_null_of_critGauge P hk)) bot_le

theorem mkMetric_polyBinaryGauge_polyCircleUnsignedExactLimit_inter_open_eq_top (P : PolyRecData)
    {k : ℕ} (hk : 1 ≤ k) {U : Set UnitAddCircle} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    Measure.mkMetric (polyBinaryGauge P)
      (polyCircleUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ U) = ⊤ := by
  obtain ⟨a, b, hab, hwidth, hsub⟩ := exists_Ioo_subset_preimage_of_isOpen_circle hU_open hU_ne
  set A : Set ℝ := polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ Set.Ioo a b
  have hA_img : circleProj '' A ⊆
      polyCircleUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ U := by
    rintro _ ⟨x, ⟨hxE, hxI⟩, rfl⟩
    exact ⟨⟨x, hxE, rfl⟩, hsub hxI⟩
  have hle := le_trans
    (mkMetric_le_circleProj_image_of_subset_Ioo (polyBinaryGauge P) (polyBinaryGauge_mono P)
      hwidth Set.inter_subset_right)
    (measure_mono hA_img)
  rw [mkMetric_polyBinaryGauge_unsignedExactLimit_inter_Ioo_eq_top P hk hab] at hle
  exact eq_top_iff.mpr hle

theorem polyCircleUnsignedExactLimit_binaryGauge_sigma_finite (P : PolyRecData) (k : ℕ) :
    ∃ E : ℕ → Set UnitAddCircle,
      polyCircleUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (polyBinaryGauge P) (E i) < ⊤ := by
  obtain ⟨E, hcov, hfin⟩ := polyUnsignedExactLimit_binaryGauge_sigma_finite P k
  refine ⟨fun i => circleProj '' (E i), ?_, fun i => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
  · exact lt_of_le_of_lt (mkMetric_circleProj_image_le (polyBinaryGauge P)
      (polyBinaryGauge_mono P) _) (hfin i)

/-- **`cor:poly-exact-gauge`（慢规范非 $\sigma$-有限性 + 快规范零测度，含 `ℝ` 与 `UnitAddCircle`）**。 -/
theorem polyExactLevel_slow_gauge_non_sigma_finite (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞)
    (hratio : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → polyCritGauge P k r ≤ (ε : ℝ≥0∞) * g r) :
    (∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
      Measure.mkMetric g (polyExactLevel P k ∩ U) = ⊤ ∧
      ¬ ∃ E : ℕ → Set ℝ, polyExactLevel P k ∩ U ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
    (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
      Measure.mkMetric g (polyCircleExactLevel P k ∩ U) = ⊤ ∧
      ¬ ∃ E : ℕ → Set UnitAddCircle, polyCircleExactLevel P k ∩ U ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤) := by
  refine ⟨fun {U} hUo hUne => ?_, fun {U} hUo hUne => ?_⟩
  · have hpos : 0 < Measure.mkMetric (polyCritGauge P k) (polyExactLevel P k ∩ U) := by
      rw [mkMetric_polyCritGauge_polyExactLevel_inter_open_eq_top P hk hUo hUne]
      exact ENNReal.zero_lt_top
    exact not_countable_union_finite_of_ratio_tendsto_zero (polyCritGauge P k) g hratio hpos
  · have hpos : 0 < Measure.mkMetric (polyCritGauge P k) (polyCircleExactLevel P k ∩ U) := by
      rw [mkMetric_polyCritGauge_polyCircleExactLevel_inter_open_eq_top P hk hUo hUne]
      exact ENNReal.zero_lt_top
    exact not_countable_union_finite_of_ratio_tendsto_zero_circle (polyCritGauge P k) g hratio hpos

theorem polyExactLevel_fast_gauge_null (P : PolyRecData) (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hfast : Tendsto (polyNormalizedGaugeCost P (2 * (k : ℝ) + 1) g) atTop (nhds 0)) :
    Measure.mkMetric g (polyExactLevel P k) = 0 ∧
    Measure.mkMetric g (polyCircleExactLevel P k) = 0 := by
  have hlim0 : liminf (polyNormalizedGaugeCost P (2 * (k : ℝ) + 1) g) atTop = 0 := hfast.liminf_eq
  have hℝ : Measure.mkMetric g (polyExactLevel P k) = 0 :=
    measure_mono_null (fun _ hx => le_of_eq hx)
      (mkMetric_polyLevelSet_null_of_liminf_zero P k g hg hlim0)
  have hT : Measure.mkMetric g (polyCircleExactLevel P k) = 0 :=
    le_antisymm ((mkMetric_circleProj_image_le g hg _).trans_eq hℝ) bot_le
  exact ⟨hℝ, hT⟩

/-- 显式幂规范 $g_\beta = \mathrm{polyInterpGauge}(P, \beta)$ 的双分支推论（$1 < \beta < 2k+1$ vs $\beta > 2k+1$）。 -/
theorem polyExactLevel_power_gauge_dichotomy (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k)
    {β : ℝ} (hβ1 : 1 < β) :
    (β < 2 * (k : ℝ) + 1 →
      ∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        Measure.mkMetric (polyInterpGauge P β) (polyExactLevel P k ∩ U) = ⊤ ∧
        ¬ ∃ E : ℕ → Set ℝ, polyExactLevel P k ∩ U ⊆ ⋃ i, E i ∧
          ∀ i, Measure.mkMetric (polyInterpGauge P β) (E i) < ⊤) ∧
    (2 * (k : ℝ) + 1 < β →
      Measure.mkMetric (polyInterpGauge P β) (polyExactLevel P k) = 0 ∧
      Measure.mkMetric (polyInterpGauge P β) (polyCircleExactLevel P k) = 0) := by
  constructor
  · intro hlt U hUo hUne
    have hratio := polyInterpGauge_ratio_tendsto_zero P hβ1 hlt
    exact (polyExactLevel_slow_gauge_non_sigma_finite P hk (polyInterpGauge P β) hratio).1 hUo hUne
  · intro hgt
    apply polyExactLevel_fast_gauge_null P k (polyInterpGauge P β) (polyInterpGauge_mono P hβ1)
    have hcost0 := poly_liminf_normalizedGaugeCost_zero_of_smaller_base P
      (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ) + 1) hgt (polyInterpGauge P β)
      (lt_of_le_of_lt (poly_liminf_normalizedGaugeCost_interp_le_one P hβ1) ENNReal.one_lt_top)
    -- Also tends to 0 directly!
    have hpow0 : Tendsto (fun n : ℕ => ((2 * (k : ℝ) + 1) / β) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one (by linarith)).mpr hgt)
    have hof0 : Tendsto (fun n : ℕ => ENNReal.ofReal (((2 * (k : ℝ) + 1) / β) ^ n)) atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hpow0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof0
      (Filter.Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_ge_atTop P.J₀] with n hn
    unfold polyNormalizedGaugeCost
    rw [polyInterpGauge_at_inv_Q P hβ1 hn,
      ← ENNReal.ofReal_mul (pow_nonneg (by positivity) n)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_pow, zpow_neg, zpow_natCast]
    simp [div_eq_mul_inv]

/-- **`cor:poly-liminf-gauges` 四分法（对 `polyExactLevel` 与 `polyCircleExactLevel`，任意单调规范 `g`）**：
    设 `k ≥ 1`，`ρ := liminf_{n→∞} (2k+1)^n g(1/Q_n)`，则在 `ℝ` 与 `UnitAddCircle` 上全面成立四分支结论。 -/
theorem polyExactLevel_liminf_four_way (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g) :
    let ρ := liminf (polyNormalizedGaugeCost P (2 * (k : ℝ) + 1) g) atTop
    (ρ = 0 → Measure.mkMetric g (polyExactLevel P k) = 0 ∧
             Measure.mkMetric g (polyCircleExactLevel P k) = 0) ∧
    (ρ < ⊤ →
      (∃ E : ℕ → Set ℝ, polyExactLevel P k ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
      (∃ E : ℕ → Set UnitAddCircle, polyCircleExactLevel P k ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤)) ∧
    (0 < ρ →
      (∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        Measure.mkMetric g (polyExactLevel P k ∩ U) = ⊤) ∧
      (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
        Measure.mkMetric g (polyCircleExactLevel P k ∩ U) = ⊤)) ∧
    (ρ = ⊤ →
      (∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        ¬ ∃ E : ℕ → Set ℝ, polyExactLevel P k ∩ U ⊆ ⋃ i, E i ∧
          ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
      (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
        ¬ ∃ E : ℕ → Set UnitAddCircle, polyCircleExactLevel P k ∩ U ⊆ ⋃ i, E i ∧
          ∀ i, Measure.mkMetric g (E i) < ⊤)) := by
  intro ρ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    have hℝ : Measure.mkMetric g (polyExactLevel P k) = 0 :=
      measure_mono_null (fun _ hx => le_of_eq hx) (mkMetric_polyLevelSet_null_of_liminf_zero P k g hg h0)
    exact ⟨hℝ, le_antisymm ((mkMetric_circleProj_image_le g hg _).trans_eq hℝ) bot_le⟩
  · intro hfin
    obtain ⟨E, hcov, hE⟩ := polyLevelSet_sigma_finite_of_liminf_lt_top P k g hg hfin
    refine ⟨⟨E, Set.Subset.trans (fun _ hx => le_of_eq hx) hcov, hE⟩,
      fun i => circleProj '' (E i), ?_, fun i => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov (le_of_eq hx))
      exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
    · exact lt_of_le_of_lt (mkMetric_circleProj_image_le g hg _) (hE i)
  · intro hpos
    obtain ⟨c, δ, hc_pos, hδ_pos, hle⟩ := exists_polyInterpGauge_le_mul_of_liminf_pos P
      (GaugeCircle.critGauge_base_gt_one k hk) g hg hpos
    refine ⟨fun {U} hUo hUne => ?_, fun {U} hUo hUne => ?_⟩
    · have hcmp := GaugeExact.mkMetric_le_mul_of_eventually_le (polyCritGauge P k) g c hδ_pos hle
        (polyExactLevel P k ∩ U)
      rw [mkMetric_polyCritGauge_polyExactLevel_inter_open_eq_top P hk hUo hUne] at hcmp
      by_contra hlt_top
      have hfin : Measure.mkMetric g (polyExactLevel P k ∩ U) < ⊤ := lt_top_iff_ne_top.mpr hlt_top
      exact (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin).ne (eq_top_iff.mpr hcmp)
    · have hcmp := GaugeCircle.mkMetric_le_mul_of_eventually_le_circle (polyCritGauge P k) g c hδ_pos hle
        (polyCircleExactLevel P k ∩ U)
      rw [mkMetric_polyCritGauge_polyCircleExactLevel_inter_open_eq_top P hk hUo hUne] at hcmp
      by_contra hlt_top
      have hfin : Measure.mkMetric g (polyCircleExactLevel P k ∩ U) < ⊤ := lt_top_iff_ne_top.mpr hlt_top
      exact (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin).ne (eq_top_iff.mpr hcmp)
  · intro htop
    have hratio := polyInterpGauge_ratio_tendsto_zero_of_liminf_top P
      (GaugeCircle.critGauge_base_gt_one k hk) g hg htop
    exact ⟨fun hUo hUne => (polyExactLevel_slow_gauge_non_sigma_finite P hk g hratio).1 hUo hUne |>.2,
           fun hUo hUne => (polyExactLevel_slow_gauge_non_sigma_finite P hk g hratio).2 hUo hUne |>.2⟩

/-- 无符号精确极限集 $E_{\mathrm{lim}}^{(r,c,d)}(k/c)$ 在普适底数 `2` 下的 `liminf` 四分法。 -/
theorem polyUnsignedExactLimit_liminf_four_way (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g) :
    let ρ := liminf (polyNormalizedGaugeCost P 2 g) atTop
    (ρ = 0 → Measure.mkMetric g (polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ))) = 0 ∧
             Measure.mkMetric g (polyCircleUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ))) = 0) ∧
    (ρ < ⊤ →
      (∃ E : ℕ → Set ℝ, polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
      (∃ E : ℕ → Set UnitAddCircle,
        polyCircleUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤)) ∧
    (0 < ρ →
      (∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        Measure.mkMetric g (polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ U) = ⊤) ∧
      (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
        Measure.mkMetric g (polyCircleUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ U) = ⊤)) ∧
    (ρ = ⊤ →
      (∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        ¬ ∃ E : ℕ → Set ℝ, polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ U ⊆ ⋃ i, E i ∧
          ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
      (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
        ¬ ∃ E : ℕ → Set UnitAddCircle,
          polyCircleUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ U ⊆ ⋃ i, E i ∧
          ∀ i, Measure.mkMetric g (E i) < ⊤)) := by
  intro ρ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    have hℝ := mkMetric_polyUnsignedExactLimit_null_of_liminf_zero P k g hg h0
    exact ⟨hℝ, le_antisymm ((mkMetric_circleProj_image_le g hg _).trans_eq hℝ) bot_le⟩
  · intro hfin
    obtain ⟨E, hcov, hE⟩ := polyUnsignedExactLimit_sigma_finite_of_liminf_lt_top P k g hg hfin
    refine ⟨⟨E, hcov, hE⟩, fun i => circleProj '' (E i), ?_, fun i => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
      exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
    · exact lt_of_le_of_lt (mkMetric_circleProj_image_le g hg _) (hE i)
  · intro hpos
    obtain ⟨c, δ, hc_pos, hδ_pos, hle⟩ := exists_polyInterpGauge_le_mul_of_liminf_pos P
      (by norm_num : (1 : ℝ) < 2) g hg hpos
    refine ⟨fun {U} hUo hUne => ?_, fun {U} hUo hUne => ?_⟩
    · have hcmp := GaugeExact.mkMetric_le_mul_of_eventually_le (polyBinaryGauge P) g c hδ_pos hle
        (polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ U)
      rw [mkMetric_polyBinaryGauge_unsignedExactLimit_inter_open_eq_top P hk hUo hUne] at hcmp
      by_contra hlt_top
      have hfin : Measure.mkMetric g _ < ⊤ := lt_top_iff_ne_top.mpr hlt_top
      exact (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin).ne (eq_top_iff.mpr hcmp)
    · have hcmp := GaugeCircle.mkMetric_le_mul_of_eventually_le_circle (polyBinaryGauge P) g c hδ_pos hle
        (polyCircleUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ U)
      rw [mkMetric_polyBinaryGauge_polyCircleUnsignedExactLimit_inter_open_eq_top P hk hUo hUne] at hcmp
      by_contra hlt_top
      have hfin : Measure.mkMetric g _ < ⊤ := lt_top_iff_ne_top.mpr hlt_top
      exact (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin).ne (eq_top_iff.mpr hcmp)
  · intro htop
    have hratio := polyInterpGauge_ratio_tendsto_zero_of_liminf_top P
      (by norm_num : (1 : ℝ) < 2) g hg htop
    refine ⟨fun {U} hUo hUne => ?_, fun {U} hUo hUne => ?_⟩
    · have hpos : 0 < Measure.mkMetric (polyBinaryGauge P)
          (polyUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ U) := by
        rw [mkMetric_polyBinaryGauge_unsignedExactLimit_inter_open_eq_top P hk hUo hUne]
        exact ENNReal.zero_lt_top
      exact (not_countable_union_finite_of_ratio_tendsto_zero (polyBinaryGauge P) g hratio hpos).2
    · have hpos : 0 < Measure.mkMetric (polyBinaryGauge P)
          (polyCircleUnsignedExactLimitSet P ((k : ℝ) / (P.c : ℝ)) ∩ U) := by
        rw [mkMetric_polyBinaryGauge_polyCircleUnsignedExactLimit_inter_open_eq_top P hk hUo hUne]
        exact ENNReal.zero_lt_top
      exact (not_countable_union_finite_of_ratio_tendsto_zero_circle (polyBinaryGauge P) g hratio hpos).2

end

end PolyGaugeAndPhaseTransition
