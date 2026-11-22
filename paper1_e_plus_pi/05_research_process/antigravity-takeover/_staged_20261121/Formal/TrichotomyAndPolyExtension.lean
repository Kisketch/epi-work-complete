import Mathlib
import EpiFormal.GaugeExact

/-!
# Theorem 16(iii) 完整补全与 §6.3 一般多项式增长递推理论（TrichotomyAndPolyExtension）

本模块在 Lean 4（仅依赖标准基础公理 `[propext, Classical.choice, Quot.sound]`，零 `sorry`）中形式化：

## 第一部分：Theorem 16(iii)（Euler 收敛子情形的完整有符号精确极限陪集坍缩）
1. 定义 `signedExactLimitSet t := {x : ℝ | Tendsto (fun j => (j : ℝ) * eps x j) atTop (nhds t)}`；
2. 对任意正整数 `k ≥ 1`，取起点 `N = 8 * k + 1`，以 `M_{N-1} = M_N = 0` 与常值缺陷 `d_j ≡ k`（`j ≥ N`）
   构造显式有符号见证 `xPlus k : ℝ`，证明 `round (Qsel m * xPlus k) = MPlus k m`（`m ≥ 8 * k`）、
   `defect (xPlus k) j = k`（`j ≥ 8 * k + 1`）、`eps (xPlus k) → 0`，从而
   `xPlus k ∈ signedExactLimitSet ((k : ℝ) / 4)` 与 `-xPlus k ∈ signedExactLimitSet (-((k : ℝ) / 4))`；
3. 证明 `add_latticeL_mem_signedExactLimitSet`（`latticeL` 平移不变性）与完整集合等式：
   - `signedExactLimitSet ((k : ℝ) / 4) = (fun z => xPlus k + z) '' Classification.latticeL`；
   - `signedExactLimitSet (-((k : ℝ) / 4)) = (fun z => -xPlus k + z) '' Classification.latticeL`；
   - 零能级 `signedExactLimitSet 0 = Classification.latticeL`、非 `ℤ/4` 能级为空、可数性、Hausdorff 维数为 `0`，
     以及任意无原子 Hausdorff 规范测度为 `0`。

## 第二部分：§6.3 一般 $r \ge 1$ 多项式增长递推 $Q_{j+1} = (c j^r + d) Q_j + Q_{j-1}$
1. **`PolyRecData`** 结构体封装 `(r, c, d, J₀, Q)`（$r \ge 1, c \ge 1, J_0 \ge 1, c J_0^r + d \ge 2, Q_j > 0$）；
2. **`lem:poly-growth`**：相邻比值严格双侧界、`J₁ := max (J₀ + 1) (2 * |d| + 1)` 下的非渐近阶乘下界
   $Q_m \ge C_{J_1} (c / 2^{r+1})^m (m!)^r$，以及对任意 $\alpha \in \mathbb{R}$ 的 $m^\alpha / Q_m \to 0$；
3. **`lem:poly-lattice`**：基本解 `fundU, fundV`、Casorati 恒等式 `U_j V_{j+1} - U_{j+1} V_j = (-1)^{j+1-J₀}`、
   交错级数收敛与误差界 $|\alpha_U - U_j/Q_j| < Q_{J_0}/(Q_j Q_{j+1})$、`Q_{J₀-1} α_U + Q_{J₀} α_V = 1`、
   无理斜率 $\theta \notin \mathbb{Q}$ 与内蕴晶格 $L^{(r,c,d)} = \mathbb{Z}\alpha_U + \mathbb{Z}\alpha_V = \frac{1}{g}(\mathbb{Z} + \mathbb{Z}\theta)$，
   以及 $\Lambda^{(r,c,d)}(x) = 0 \iff (u_j \to 0 \land \forall^\infty j,\, d_j = 0) \iff x \in L^{(r,c,d)}$
   和 $\Lambda_\alpha^{(r,c,d)}(x) = 0$（$\forall \alpha \in \mathbb{R}$）；
4. **`thm:general-rec`（全 $r \ge 1$ 全谱完全离散化）**：
   - `(i)` $u_j \to 0 \implies d_j - c j^r u_j \to 0$ 与 $|d_j| - c j^r \|Q_j x\| \to 0$；
   - `(ii)` 构造见证 `xPlusPoly P k` 实现 $\Lambda^{(r,c,d)} = k/c$、排除全部开谱隙 $(k/c, (k+1)/c)$、
     刻画区间 $[k/c, (k+1)/c)$ 上的水平集恒等及 $t < 1/c$ 坍缩为 $L^{(r,c,d)}$；
5. **`thm:poly-gauge-trichotomy(iii)`**：一般 $(r, c, d)$ 下的有符号精确极限陪集坍缩
   $E_{\mathrm{lim}}^{(r,c,d),\pm}(k/c) = \pm x_k^+ + L^{(r,c,d)}$、可数性与零维零规范测度；
6. **`thm:poly-phase-transition(i), (iii)`**：
   - `(i)` 临界权 $\alpha = r$ 的有限水平集维数为 $0$、Lebesgue 零测度、无限水平集 $\Lambda^{(r,c,d)} = \infty$ 满测度且在任意 $[a, b]$（$a < b$）上 Hausdorff 维数为 $1$；
   - `(iii)` 超临界权 $\alpha > r$ 在 $t \ge 0$ 时坍缩为 $L^{(r,c,d)}$（$t < 0$ 为空集）。
-/

open Real Filter Topology Set MeasureTheory Classification SpectralGap DimHCore DimHFinite
  FullSpectrumDiscrete GaugeExact
open scoped ENNReal NNReal

namespace TrichotomyAndPolyExtension

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 第一部分：Theorem 16(iii) 完整补全（Euler 收敛子情形） -/

/-- 有符号精确极限集 $E_{\mathrm{lim}}^{\mathrm{signed}}(t) := \{x \in \mathbb{R} : \lim_{j\to\infty} j \varepsilon_j(x) = t\}$。 -/
def signedExactLimitSet (t : ℝ) : Set ℝ :=
  {x : ℝ | Tendsto (fun j : ℕ => (j : ℝ) * eps x j) atTop (nhds t)}

/-- 起点 $N = 8k+1$、初始值 $M_{N-1} = M_N = 0$、尾缺陷恒为 $+k$ 的整数分子序列 `MPlus k`。 -/
def MPlus (k : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
      if n + 1 < 8 * k + 1 then 0
      else (4 * ((n + 1 : ℕ) : ℤ) + 2) * MPlus k (n + 1) + MPlus k n + (k : ℤ)

@[simp] lemma MPlus_zero (k : ℕ) : MPlus k 0 = 0 := rfl
@[simp] lemma MPlus_one (k : ℕ) : MPlus k 1 = 0 := rfl

lemma MPlus_eq_zero_of_le (k m : ℕ) (hm : m ≤ 8 * k + 1) : MPlus k m = 0 := by
  rcases m with _ | _ | n
  · rfl
  · rfl
  · simp only [MPlus]
    have hlt : n + 1 < 8 * k + 1 := by omega
    simp [hlt]

lemma MPlus_rec (k j : ℕ) (hj : 8 * k + 1 ≤ j) :
    MPlus k (j + 1) = (4 * (j : ℤ) + 2) * MPlus k j + MPlus k (j - 1) + (k : ℤ) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have hnot : ¬ (n + 1 < 8 * k + 1) := by omega
  have hsub : n + 1 - 1 = n := by omega
  have hadd : n + 1 + 1 = n + 2 := by omega
  rw [hadd, hsub]
  simp [MPlus, hnot]

/-- Wronskian 差序列 $W_j = M_{j+1} Q_j - M_j Q_{j+1}$。 -/
def WPlus (k j : ℕ) : ℤ := MPlus k (j + 1) * Qsel j - MPlus k j * Qsel (j + 1)

lemma WPlus_init (k : ℕ) : WPlus k (8 * k) = 0 := by
  unfold WPlus
  rw [MPlus_eq_zero_of_le k (8 * k + 1) (le_refl _), MPlus_eq_zero_of_le k (8 * k) (by omega)]
  ring

lemma WPlus_rec (k j : ℕ) (hj : 8 * k + 1 ≤ j) :
    WPlus k j = (k : ℤ) * Qsel j - WPlus k (j - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hsub : m + 1 - 1 = m := by omega
  rw [hsub]
  have hQ := Classification.Qsel_rec' (m + 1) (by omega)
  rw [hsub] at hQ
  have hM := MPlus_rec k (m + 1) hj
  rw [hsub] at hM
  simp only [WPlus]
  rw [hM, hQ]
  ring

lemma WPlus_bounds (k : ℕ) (j : ℕ) (hj : 8 * k ≤ j) :
    0 ≤ WPlus k j ∧ WPlus k j ≤ (k : ℤ) * Qsel j := by
  obtain ⟨n, rfl⟩ : ∃ n, j = 8 * k + n := ⟨j - 8 * k, by omega⟩
  induction n with
  | zero =>
      rw [Nat.add_zero, WPlus_init]
      exact ⟨le_refl 0, mul_nonneg (Int.natCast_nonneg k) (le_of_lt (Classification.Qsel_pos (8 * k)))⟩
  | succ n ih =>
      have ihn := ih (by omega)
      have hrec := WPlus_rec k (8 * k + n + 1) (by omega)
      have hsub : 8 * k + n + 1 - 1 = 8 * k + n := by omega
      rw [hsub] at hrec
      have hmono : Qsel (8 * k + n) ≤ Qsel (8 * k + n + 1) := by
        by_cases h0 : 8 * k + n = 0
        · rw [h0]; simp [Qsel_zero, Qsel_one]
        · exact le_of_lt (_root_.Qsel_lt_succ (8 * k + n) (by omega))
      have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
      have hkQ : (k : ℤ) * Qsel (8 * k + n) ≤ (k : ℤ) * Qsel (8 * k + n + 1) :=
        mul_le_mul_of_nonneg_left hmono hk0
      have hadd : 8 * k + (n + 1) = 8 * k + n + 1 := by omega
      rw [hadd]
      constructor <;> linarith [ihn.1, ihn.2, hrec, hkQ]

/-- 有符号构造的比值差分序列 $r_{j+1} - r_j$。 -/
def diffPlus (k j : ℕ) : ℝ :=
  (MPlus k (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) - (MPlus k j : ℝ) / (Qsel j : ℝ)

lemma diffPlus_eq_zero_of_lt (k j : ℕ) (hj : j < 8 * k) : diffPlus k j = 0 := by
  unfold diffPlus
  rw [MPlus_eq_zero_of_le k (j + 1) (by omega), MPlus_eq_zero_of_le k j (by omega)]
  simp

lemma diffPlus_eq_WPlus (k j : ℕ) :
    diffPlus k j = (WPlus k j : ℝ) / ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ)) := by
  have hQ1 : (Qsel j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Classification.Qsel_pos j)
  have hQ2 : (Qsel (j + 1) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Classification.Qsel_pos (j + 1))
  simp only [diffPlus, WPlus]
  push_cast
  field_simp

lemma diffPlus_nonneg (k j : ℕ) (hj : 8 * k ≤ j) : 0 ≤ diffPlus k j := by
  rw [diffPlus_eq_WPlus]
  have hQ1 : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Classification.Qsel_pos j
  have hQ2 : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast Classification.Qsel_pos (j + 1)
  have hW : (0 : ℝ) ≤ (WPlus k j : ℝ) := by exact_mod_cast (WPlus_bounds k j hj).1
  exact div_nonneg hW (le_of_lt (mul_pos hQ1 hQ2))

lemma diffPlus_le (k j : ℕ) (hj : 8 * k ≤ j) :
    diffPlus k j ≤ (k : ℝ) / (Qsel (j + 1) : ℝ) := by
  rw [diffPlus_eq_WPlus]
  have hQ1 : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Classification.Qsel_pos j
  have hQ2 : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast Classification.Qsel_pos (j + 1)
  have hW : (WPlus k j : ℝ) ≤ (k : ℝ) * (Qsel j : ℝ) := by
    exact_mod_cast (WPlus_bounds k j hj).2
  rw [div_le_div_iff₀ (mul_pos hQ1 hQ2) hQ2]
  nlinarith

lemma Qsel_real_ge_two_mul (j : ℕ) (hj : 1 ≤ j) :
    2 * (Qsel j : ℝ) ≤ (Qsel (j + 1) : ℝ) := by
  exact_mod_cast Classification.Qsel_double j hj

lemma Qsel_real_geom (j : ℕ) (hj : 1 ≤ j) (m : ℕ) :
    (2 : ℝ) ^ m * (Qsel j : ℝ) ≤ (Qsel (j + m) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h2 := Qsel_real_ge_two_mul (j + m) (by omega)
      have hadd : j + (m + 1) = (j + m) + 1 := by omega
      rw [hadd]
      calc (2 : ℝ) ^ (m + 1) * (Qsel j : ℝ)
          = 2 * ((2 : ℝ) ^ m * (Qsel j : ℝ)) := by ring
        _ ≤ 2 * (Qsel (j + m) : ℝ) := by gcongr
        _ ≤ (Qsel (j + m + 1) : ℝ) := h2

lemma summable_inv_Qsel_local : Summable (fun j : ℕ => 1 / (Qsel j : ℝ)) := by
  have hgrow : ∀ j : ℕ, (2 : ℝ) ^ j ≤ 2 * (Qsel j : ℝ) := by
    intro j
    induction j with
    | zero => simp [Qsel_zero]
    | succ n ih =>
        by_cases hn0 : n = 0
        · subst hn0; simp [Qsel_one]
        · have h2 := Qsel_real_ge_two_mul n (by omega)
          calc (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by ring
            _ ≤ 2 * (2 * (Qsel n : ℝ)) := by gcongr
            _ ≤ 2 * (Qsel (n + 1) : ℝ) := by gcongr
  have hbound : ∀ j : ℕ, 1 / (Qsel j : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ j := by
    intro j
    have hQ : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Classification.Qsel_pos j
    rw [div_le_iff₀ hQ]
    have hg := hgrow j
    have hpow : (1 / 2 : ℝ) ^ j = ((2 : ℝ) ^ j)⁻¹ := by rw [div_pow, one_pow, one_div]
    calc (1 : ℝ) = ((2 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ j := by field_simp
      _ ≤ ((2 : ℝ) ^ j)⁻¹ * (2 * (Qsel j : ℝ)) := by gcongr
      _ = 2 * (1 / 2 : ℝ) ^ j * (Qsel j : ℝ) := by rw [hpow]; ring
  exact Summable.of_nonneg_of_le
    (fun j => div_nonneg zero_le_one (by exact_mod_cast (Classification.Qsel_pos j).le))
    hbound ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2)

lemma summable_diffPlus (k : ℕ) : Summable (diffPlus k) := by
  have hshift : Summable (fun j : ℕ => (k : ℝ) * (1 / (Qsel (j + 1) : ℝ))) :=
    ((summable_nat_add_iff 1).mpr summable_inv_Qsel_local).mul_left (k : ℝ)
  have hnorm : ∀ᶠ j in atTop, ‖diffPlus k j‖ ≤ (k : ℝ) * (1 / (Qsel (j + 1) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (8 * k)] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg (diffPlus_nonneg k j hj), mul_one_div]
    exact diffPlus_le k j hj
  exact Summable.of_norm_bounded_eventually_nat hshift hnorm

/-- Theorem 16(iii) 正有符号精确极限见证 $x_k^+$（由恒定尾缺陷 $+k$ 构造）。 -/
def xPlus (k : ℕ) : ℝ := ∑' j : ℕ, diffPlus k j

lemma sum_diffPlus_eq (k m : ℕ) :
    ∑ j ∈ Finset.range m, diffPlus k j = (MPlus k m : ℝ) / (Qsel m : ℝ) := by
  have h := Finset.sum_range_sub (fun j => (MPlus k j : ℝ) / (Qsel j : ℝ)) m
  have h0 : (MPlus k 0 : ℝ) / (Qsel 0 : ℝ) = 0 := by simp
  calc ∑ j ∈ Finset.range m, diffPlus k j
      = ∑ j ∈ Finset.range m, ((MPlus k (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) -
          (MPlus k j : ℝ) / (Qsel j : ℝ)) := rfl
    _ = (MPlus k m : ℝ) / (Qsel m : ℝ) - (MPlus k 0 : ℝ) / (Qsel 0 : ℝ) := h
    _ = (MPlus k m : ℝ) / (Qsel m : ℝ) := by rw [h0, sub_zero]

lemma xPlus_sub_ratio (k m : ℕ) :
    xPlus k - (MPlus k m : ℝ) / (Qsel m : ℝ) = ∑' s : ℕ, diffPlus k (s + m) := by
  have hsplit := (summable_diffPlus k).sum_add_tsum_nat_add m
  rw [sum_diffPlus_eq] at hsplit
  unfold xPlus
  linarith [hsplit]

lemma xPlus_sub_ratio_bounds (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : 8 * k ≤ m) :
    0 ≤ xPlus k - (MPlus k m : ℝ) / (Qsel m : ℝ) ∧
    xPlus k - (MPlus k m : ℝ) / (Qsel m : ℝ) ≤ (2 * (k : ℝ)) / (Qsel (m + 1) : ℝ) := by
  rw [xPlus_sub_ratio]
  have hs_sum : Summable (fun s : ℕ => diffPlus k (s + m)) :=
    (summable_diffPlus k).comp_injective (add_left_injective m)
  have hm1 : 1 ≤ m := by omega
  have hQ1 : (0 : ℝ) < (Qsel (m + 1) : ℝ) := by exact_mod_cast Classification.Qsel_pos (m + 1)
  have hgeom_sum : Summable (fun s : ℕ => ((k : ℝ) / (Qsel (m + 1) : ℝ)) * (1 / 2 : ℝ) ^ s) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  constructor
  · apply tsum_nonneg
    intro s
    exact diffPlus_nonneg k (s + m) (by omega)
  · have hle : ∀ s : ℕ,
        diffPlus k (s + m) ≤ ((k : ℝ) / (Qsel (m + 1) : ℝ)) * (1 / 2 : ℝ) ^ s := by
      intro s
      have h1 := diffPlus_le k (s + m) (by omega)
      have h2 := Qsel_real_geom (m + 1) (by omega) s
      have hadd : m + 1 + s = s + m + 1 := by omega
      rw [hadd] at h2
      have hQsm1 : (0 : ℝ) < (Qsel (s + m + 1) : ℝ) := by
        exact_mod_cast Classification.Qsel_pos (s + m + 1)
      have h2s : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
      have hinv : 1 / (Qsel (s + m + 1) : ℝ) ≤ (1 / 2 : ℝ) ^ s / (Qsel (m + 1) : ℝ) := by
        rw [div_le_div_iff₀ hQsm1 hQ1]
        have hpow : (1 / 2 : ℝ) ^ s * (2 : ℝ) ^ s = 1 := by
          rw [← mul_pow]; norm_num
        calc (1 : ℝ) * (Qsel (m + 1) : ℝ) = (Qsel (m + 1) : ℝ) := one_mul _
          _ = (1 / 2 : ℝ) ^ s * ((2 : ℝ) ^ s * (Qsel (m + 1) : ℝ)) := by
              rw [← mul_assoc, hpow, one_mul]
          _ ≤ (1 / 2 : ℝ) ^ s * (Qsel (s + m + 1) : ℝ) := by gcongr
      calc diffPlus k (s + m)
          ≤ (k : ℝ) / (Qsel (s + m + 1) : ℝ) := h1
        _ = (k : ℝ) * (1 / (Qsel (s + m + 1) : ℝ)) := by ring
        _ ≤ (k : ℝ) * ((1 / 2 : ℝ) ^ s / (Qsel (m + 1) : ℝ)) := by gcongr
        _ = ((k : ℝ) / (Qsel (m + 1) : ℝ)) * (1 / 2 : ℝ) ^ s := by ring
    have htsum := Summable.tsum_le_tsum hle hs_sum hgeom_sum
    have hval : ∑' s : ℕ, ((k : ℝ) / (Qsel (m + 1) : ℝ)) * (1 / 2 : ℝ) ^ s =
        (2 * (k : ℝ)) / (Qsel (m + 1) : ℝ) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
    linarith

lemma Qsel_mul_xPlus_sub_MPlus (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : 8 * k ≤ m) :
    0 ≤ (Qsel m : ℝ) * xPlus k - (MPlus k m : ℝ) ∧
    (Qsel m : ℝ) * xPlus k - (MPlus k m : ℝ) ≤
      (2 * (k : ℝ) * (Qsel m : ℝ)) / (Qsel (m + 1) : ℝ) := by
  have hQ : (0 : ℝ) < (Qsel m : ℝ) := by exact_mod_cast Classification.Qsel_pos m
  have hb := xPlus_sub_ratio_bounds k hk m hm
  have heq : (Qsel m : ℝ) * xPlus k - (MPlus k m : ℝ) =
      (Qsel m : ℝ) * (xPlus k - (MPlus k m : ℝ) / (Qsel m : ℝ)) := by
    field_simp
  rw [heq]
  constructor
  · exact mul_nonneg (le_of_lt hQ) hb.1
  · calc (Qsel m : ℝ) * (xPlus k - (MPlus k m : ℝ) / (Qsel m : ℝ))
        ≤ (Qsel m : ℝ) * ((2 * (k : ℝ)) / (Qsel (m + 1) : ℝ)) := by gcongr; exact hb.2
      _ = (2 * (k : ℝ) * (Qsel m : ℝ)) / (Qsel (m + 1) : ℝ) := by ring

lemma Qsel_mul_xPlus_sub_MPlus_lt_half (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : 8 * k ≤ m) :
    (Qsel m : ℝ) * xPlus k - (MPlus k m : ℝ) < 1 / 2 := by
  have hb := (Qsel_mul_xPlus_sub_MPlus k hk m hm).2
  have hm1 : 1 ≤ m := by omega
  have hQ : (0 : ℝ) < (Qsel m : ℝ) := by exact_mod_cast Classification.Qsel_pos m
  have hQ1 : (0 : ℝ) < (Qsel (m + 1) : ℝ) := by exact_mod_cast Classification.Qsel_pos (m + 1)
  have hrec := Classification.Qsel_rec' m hm1
  have hprev : (0 : ℝ) ≤ (Qsel (m - 1) : ℝ) := by
    exact_mod_cast (Classification.Qsel_pos (m - 1)).le
  have hrecR : (Qsel (m + 1) : ℝ) =
      (4 * (m : ℝ) + 2) * (Qsel m : ℝ) + (Qsel (m - 1) : ℝ) := by exact_mod_cast hrec
  have hmR : (8 * (k : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hQgrow : (32 * (k : ℝ)) * (Qsel m : ℝ) < (Qsel (m + 1) : ℝ) := by
    rw [hrecR]
    nlinarith
  have hdiv : (2 * (k : ℝ) * (Qsel m : ℝ)) / (Qsel (m + 1) : ℝ) < 1 / 2 := by
    rw [div_lt_iff₀ hQ1]
    nlinarith
  linarith

lemma xPlus_nearestInt_eq (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : 8 * k ≤ m) :
    nearestInt ((Qsel m : ℝ) * xPlus k) = MPlus k m := by
  have hlo := (Qsel_mul_xPlus_sub_MPlus k hk m hm).1
  have hhi := Qsel_mul_xPlus_sub_MPlus_lt_half k hk m hm
  unfold nearestInt
  rw [round_eq_iff]
  constructor <;> linarith

lemma neg_xPlus_nearestInt_eq (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : 8 * k ≤ m) :
    nearestInt ((Qsel m : ℝ) * (-xPlus k)) = -MPlus k m := by
  have hlo := (Qsel_mul_xPlus_sub_MPlus k hk m hm).1
  have hhi := Qsel_mul_xPlus_sub_MPlus_lt_half k hk m hm
  unfold nearestInt
  rw [round_eq_iff]
  push_cast
  constructor <;> linarith

lemma xPlus_defect_eq (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ j : ℕ in atTop, defect (xPlus k) j = (k : ℤ) := by
  filter_upwards [eventually_ge_atTop (8 * k + 1)] with j hj
  have h1 := xPlus_nearestInt_eq k hk (j + 1) (by omega)
  have h2 := xPlus_nearestInt_eq k hk j (by omega)
  have h3 := xPlus_nearestInt_eq k hk (j - 1) (by omega)
  unfold defect
  rw [h1, h2, h3, MPlus_rec k j hj]
  ring

lemma neg_xPlus_defect_eq (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ j : ℕ in atTop, defect (-xPlus k) j = -(k : ℤ) := by
  filter_upwards [eventually_ge_atTop (8 * k + 1)] with j hj
  have h1 := neg_xPlus_nearestInt_eq k hk (j + 1) (by omega)
  have h2 := neg_xPlus_nearestInt_eq k hk j (by omega)
  have h3 := neg_xPlus_nearestInt_eq k hk (j - 1) (by omega)
  unfold defect
  rw [h1, h2, h3, MPlus_rec k j hj]
  ring

lemma xPlus_eps_tendsto_zero (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (eps (xPlus k)) atTop (nhds 0) := by
  have hbound : ∀ᶠ j : ℕ in atTop, |eps (xPlus k) j| ≤ ((k : ℝ) / 2) / (j : ℝ) := by
    filter_upwards [eventually_ge_atTop (8 * k + 1)] with j hj
    have hr := xPlus_nearestInt_eq k hk j (by omega)
    have hnn := (Qsel_mul_xPlus_sub_MPlus k hk j (by omega)).1
    have hle := (Qsel_mul_xPlus_sub_MPlus k hk j (by omega)).2
    have heps : eps (xPlus k) j = (Qsel j : ℝ) * xPlus k - (MPlus k j : ℝ) := by
      simp only [eps, hr]
    rw [heps, abs_of_nonneg hnn]
    have hQ : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Classification.Qsel_pos j
    have hQ1 : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast Classification.Qsel_pos (j + 1)
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hrec : (Qsel (j + 1) : ℝ) =
        (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by
      exact_mod_cast Classification.Qsel_rec' j (by omega)
    have hprev : (0 : ℝ) ≤ (Qsel (j - 1) : ℝ) := by
      exact_mod_cast (Classification.Qsel_pos (j - 1)).le
    have hgrow : 4 * (j : ℝ) * (Qsel j : ℝ) ≤ (Qsel (j + 1) : ℝ) := by
      rw [hrec]; nlinarith
    calc (Qsel j : ℝ) * xPlus k - (MPlus k j : ℝ)
        ≤ (2 * (k : ℝ) * (Qsel j : ℝ)) / (Qsel (j + 1) : ℝ) := hle
      _ ≤ (2 * (k : ℝ) * (Qsel j : ℝ)) / (4 * (j : ℝ) * (Qsel j : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hgrow
      _ = ((k : ℝ) / 2) / (j : ℝ) := by field_simp; ring
  exact FullSpectrumDiscrete.tendsto_zero_of_eventually_abs_le_div hbound

lemma neg_xPlus_eps_tendsto_zero (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (eps (-xPlus k)) atTop (nhds 0) := by
  have heq : ∀ᶠ j : ℕ in atTop, eps (-xPlus k) j = -eps (xPlus k) j := by
    filter_upwards [eventually_ge_atTop (8 * k)] with j hj
    have h1 := xPlus_nearestInt_eq k hk j hj
    have h2 := neg_xPlus_nearestInt_eq k hk j hj
    simp only [eps, h1, h2]
    push_cast
    ring
  have hneg : Tendsto (fun j : ℕ => -eps (xPlus k) j) atTop (nhds 0) := by
    simpa using (xPlus_eps_tendsto_zero k hk).neg
  exact hneg.congr' (heq.mono fun _ h => h.symm)

/-- 正有符号见证 $x_k^+ \in E_{\mathrm{lim}}^+(k/4)$。 -/
theorem xPlus_mem_signedExactLimitSet (k : ℕ) (hk : 1 ≤ k) :
    xPlus k ∈ signedExactLimitSet ((k : ℝ) / 4) := by
  have h := (FullSpectrumDiscrete.signed_exact_limit_iff_defect_const (xPlus k) (k : ℤ)).mpr
    ⟨xPlus_eps_tendsto_zero k hk, xPlus_defect_eq k hk⟩
  simpa [signedExactLimitSet] using h

/-- 负有符号见证 $x_k^- = -x_k^+ \in E_{\mathrm{lim}}^-(k/4)$。 -/
theorem neg_xPlus_mem_signedExactLimitSet (k : ℕ) (hk : 1 ≤ k) :
    -xPlus k ∈ signedExactLimitSet (-((k : ℝ) / 4)) := by
  have h := (FullSpectrumDiscrete.signed_exact_limit_iff_defect_const (-xPlus k) (-(k : ℤ))).mpr
    ⟨neg_xPlus_eps_tendsto_zero k hk, neg_xPlus_defect_eq k hk⟩
  simp only [signedExactLimitSet, Int.cast_neg, Int.cast_natCast, neg_div] at h ⊢
  exact h

/-- 若 $j \varepsilon_j(x) \to t$，则 $\varepsilon_j(x) \to 0$。 -/
lemma eps_tendsto_zero_of_mem_signedExactLimitSet {x t : ℝ}
    (hx : x ∈ signedExactLimitSet t) :
    Tendsto (eps x) atTop (nhds 0) := by
  have habs : Tendsto (fun j : ℕ => |(j : ℝ) * eps x j|) atTop (nhds |t|) := hx.abs
  have hev : ∀ᶠ j : ℕ in atTop, |(j : ℝ) * eps x j| < |t| + 1 :=
    habs.eventually (Iio_mem_nhds (by linarith))
  have hbound : ∀ᶠ j : ℕ in atTop, |eps x j| ≤ (|t| + 1) / (j : ℝ) := by
    filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hmul : (j : ℝ) * |eps x j| ≤ |t| + 1 := by
      have : |(j : ℝ) * eps x j| = (j : ℝ) * |eps x j| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
      linarith
    exact (le_div_iff₀ hjpos).mpr (by linarith)
  exact FullSpectrumDiscrete.tendsto_zero_of_eventually_abs_le_div hbound

/-- **格平移不变性**：若 $x \in E_{\mathrm{lim}}^{\mathrm{signed}}(t)$ 且 $z \in L$，则
    $x + z \in E_{\mathrm{lim}}^{\mathrm{signed}}(t)$。 -/
theorem add_latticeL_mem_signedExactLimitSet {x t z : ℝ}
    (hx : x ∈ signedExactLimitSet t) (hz : z ∈ Classification.latticeL) :
    x + z ∈ signedExactLimitSet t := by
  have hεx := eps_tendsto_zero_of_mem_signedExactLimitSet hx
  have hz_appr : Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * z))
      atTop (nhds 0) := (Classification.theorem2_classification z).mpr hz
  have hεz : Tendsto (eps z) atTop (nhds 0) := by
    have hev : ∀ᶠ j : ℕ in atTop, (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * z) < 1 :=
      hz_appr.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have hbound : ∀ᶠ j : ℕ in atTop, |eps z j| ≤ 1 / (j : ℝ) := by
      filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
      have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
      have heps : |eps z j| = distToNearestInt ((Qsel j : ℝ) * z) := rfl
      have hmul : (j : ℝ) * |eps z j| < 1 := by simpa [heps] using hj
      exact (le_div_iff₀ hjpos).mpr (by linarith)
    exact FullSpectrumDiscrete.tendsto_zero_of_eventually_abs_le_div hbound
  have hsum_eps : Tendsto (fun j : ℕ => eps x j + eps z j) atTop (nhds 0) := by
    simpa using hεx.add hεz
  have hlt_half : ∀ᶠ j : ℕ in atTop, |eps x j + eps z j| < 1 / 2 :=
    (by simpa using hsum_eps.abs : Tendsto (fun j : ℕ => |eps x j + eps z j|) atTop (nhds 0)).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have heps_add : ∀ᶠ j : ℕ in atTop, eps (x + z) j = eps x j + eps z j := by
    filter_upwards [hlt_half] with j hj
    have hround : nearestInt ((Qsel j : ℝ) * (x + z)) =
        nearestInt ((Qsel j : ℝ) * x) + nearestInt ((Qsel j : ℝ) * z) := by
      unfold nearestInt at *
      rw [round_eq_iff]
      have hid : (Qsel j : ℝ) * (x + z) =
          ((round ((Qsel j : ℝ) * x) + round ((Qsel j : ℝ) * z) : ℤ) : ℝ) +
            (eps x j + eps z j) := by
        simp only [eps, nearestInt]
        push_cast
        ring
      have habs := abs_lt.mp hj
      rw [hid]
      constructor <;> linarith
    simp only [eps, hround]
    push_cast
    ring
  have hj_z : Tendsto (fun j : ℕ => (j : ℝ) * eps z j) atTop (nhds 0) := by
    have hneg : Tendsto (fun j : ℕ => -((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * z)))
        atTop (nhds 0) := by simpa using hz_appr.neg
    have hlo : ∀ᶠ j : ℕ in atTop,
        -((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * z)) ≤ (j : ℝ) * eps z j := by
      filter_upwards with j
      have h1 := (abs_le.mp (le_refl |eps z j|)).1
      have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have heps : |eps z j| = distToNearestInt ((Qsel j : ℝ) * z) := rfl
      nlinarith
    have hhi : ∀ᶠ j : ℕ in atTop,
        (j : ℝ) * eps z j ≤ (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * z) := by
      filter_upwards with j
      have h1 := (abs_le.mp (le_refl |eps z j|)).2
      have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have heps : |eps z j| = distToNearestInt ((Qsel j : ℝ) * z) := rfl
      nlinarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hz_appr hlo hhi
  have hlim : Tendsto (fun j : ℕ => (j : ℝ) * (eps x j + eps z j)) atTop (nhds t) := by
    have hsum := hx.add hj_z
    simpa [mul_add] using hsum
  exact hlim.congr' (heps_add.mono fun j hj => by simp [hj])

/-- **Theorem 16(iii) 正支完整陪集坍缩**：
    对一切 $k \ge 1$，$E_{\mathrm{lim}}^+(k/4) = x_k^+ + L$。 -/
theorem signedExactLimitSet_pos_eq_coset (k : ℕ) (hk : 1 ≤ k) :
    signedExactLimitSet ((k : ℝ) / 4) = (fun z : ℝ => xPlus k + z) '' Classification.latticeL := by
  ext y
  constructor
  · intro hy
    have hdiff : y - xPlus k ∈ Classification.latticeL :=
      FullSpectrumDiscrete.sub_mem_latticeL_of_same_signed_limit y (xPlus k) (k : ℤ)
        hy (xPlus_mem_signedExactLimitSet k hk)
    exact ⟨y - xPlus k, hdiff, by ring⟩
  · rintro ⟨z, hz, rfl⟩
    exact add_latticeL_mem_signedExactLimitSet (xPlus_mem_signedExactLimitSet k hk) hz

/-- **Theorem 16(iii) 负支完整陪集坍缩**：
    对一切 $k \ge 1$，$E_{\mathrm{lim}}^-(k/4) = x_k^- + L$（其中 $x_k^- = -x_k^+$）。 -/
theorem signedExactLimitSet_neg_eq_coset (k : ℕ) (hk : 1 ≤ k) :
    signedExactLimitSet (-((k : ℝ) / 4)) =
      (fun z : ℝ => -xPlus k + z) '' Classification.latticeL := by
  ext y
  constructor
  · intro hy
    have hy' : Tendsto (fun j : ℕ => (j : ℝ) * eps y j) atTop (nhds (((-(k : ℤ) : ℤ) : ℝ) / 4)) := by
      have heq : (((-(k : ℤ) : ℤ) : ℝ) / 4) = -((k : ℝ) / 4) := by push_cast; ring
      rwa [heq]
    have hx' : Tendsto (fun j : ℕ => (j : ℝ) * eps (-xPlus k) j) atTop
        (nhds (((-(k : ℤ) : ℤ) : ℝ) / 4)) := by
      have heq : (((-(k : ℤ) : ℤ) : ℝ) / 4) = -((k : ℝ) / 4) := by push_cast; ring
      rw [heq]
      exact neg_xPlus_mem_signedExactLimitSet k hk
    have hdiff : y - (-xPlus k) ∈ Classification.latticeL :=
      FullSpectrumDiscrete.sub_mem_latticeL_of_same_signed_limit y (-xPlus k) (-(k : ℤ)) hy' hx'
    exact ⟨y - (-xPlus k), hdiff, by ring⟩
  · rintro ⟨z, hz, rfl⟩
    exact add_latticeL_mem_signedExactLimitSet (neg_xPlus_mem_signedExactLimitSet k hk) hz

/-- 零能级情形：$E_{\mathrm{lim}}^{\mathrm{signed}}(0) = L$。 -/
theorem signedExactLimitSet_zero_eq_latticeL :
    signedExactLimitSet 0 = Classification.latticeL := by
  ext x
  constructor
  · intro hx
    have habs : Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun j : ℕ => |(j : ℝ) * eps x j|) atTop (nhds 0) := by
        simpa using hx.abs
      apply h1.congr'
      filter_upwards with j
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
      rfl
    exact (Classification.theorem2_classification x).mp habs
  · intro hx
    have h1 : (0 : ℝ) ∈ signedExactLimitSet 0 := by
      simp [signedExactLimitSet, eps, nearestInt]
    simpa using add_latticeL_mem_signedExactLimitSet h1 hx

/-- 若 $4 t \notin \mathbb{Z}$，则 $E_{\mathrm{lim}}^{\mathrm{signed}}(t) = \emptyset$。 -/
theorem signedExactLimitSet_empty_of_not_quarter_int {t : ℝ}
    (ht : ∀ d : ℤ, 4 * t ≠ (d : ℝ)) :
    signedExactLimitSet t = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hε := eps_tendsto_zero_of_mem_signedExactLimitSet hx
  have happrox := FullSpectrumDiscrete.euler_signed_defect_approx x hε
  have h4lim : Tendsto (fun j : ℕ => 4 * (j : ℝ) * eps x j) atTop (nhds (4 * t)) := by
    have h := hx.const_mul 4
    apply h.congr'
    filter_upwards with j
    ring
  set k := ⌊4 * t⌋
  have hk_lt : (k : ℝ) < 4 * t := lt_of_le_of_ne (Int.floor_le (4 * t)) (ht k).symm
  have hlt_k1 : 4 * t < (k : ℝ) + 1 := Int.lt_floor_add_one (4 * t)
  exact FullSpectrumDiscrete.not_tendsto_open_interval_of_int_approx happrox k hk_lt hlt_k1 h4lim

/-- 任意点 $x \in \mathbb{R}$ 在满足 $m(r) \to 0$（$r \to 0^+$）的 Hausdorff 规范测度下测度为 $0$。 -/
lemma mkMetric_singleton_zero (m : ℝ≥0∞ → ℝ≥0∞)
    (hm0 : Tendsto m (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) (x : ℝ) :
    Measure.mkMetric m ({x} : Set ℝ) = 0 := by
  let r2 : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n : ℝ) + 1))
  let cov2 : ℕ → Unit → Set ℝ := fun n _ =>
    Set.Icc (x - 1 / (2 * ((n : ℝ) + 1))) (x + 1 / (2 * ((n : ℝ) + 1)))
  have hr2 : Tendsto r2 atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [r2] using ENNReal.tendsto_ofReal h1
  have hdiam_eq : ∀ n : ℕ, Metric.ediam (cov2 n ()) = r2 n := fun n => by
    dsimp [cov2, r2]
    rw [Real.ediam_Icc]
    congr 1
    field_simp
    ring
  have ht2 : ∀ᶠ n in atTop, ∀ u : Unit, Metric.ediam (cov2 n u) ≤ r2 n :=
    Filter.Eventually.of_forall (fun n _ => le_of_eq (hdiam_eq n))
  have hst2 : ∀ᶠ n in atTop, ({x} : Set ℝ) ⊆ ⋃ u : Unit, cov2 n u :=
    Filter.Eventually.of_forall (fun n => by
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      refine Set.mem_iUnion.mpr ⟨(), ?_⟩
      dsimp [cov2]
      have hpos : (0 : ℝ) ≤ 1 / (2 * ((n : ℝ) + 1)) := by positivity
      exact ⟨by linarith, by linarith⟩)
  have hmain2 := MeasureTheory.Measure.mkMetric_le_liminf_sum
    ({x} : Set ℝ) r2 hr2 cov2 ht2 hst2 m
  have hr2_pos : ∀ n : ℕ, 0 < r2 n := fun n => ENNReal.ofReal_pos.mpr (by positivity)
  have hm_tend : Tendsto (fun n : ℕ => m (r2 n)) atTop (nhds 0) := by
    refine hm0.comp ?_
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hr2, Filter.Eventually.of_forall hr2_pos⟩
  have hsum_tend : Tendsto (fun n : ℕ => ∑ u : Unit, m (Metric.ediam (cov2 n u))) atTop (nhds 0) := by
    refine hm_tend.congr' (Filter.Eventually.of_forall fun n => ?_)
    simp [hdiam_eq n]
  have hlim0 : Filter.liminf (fun n : ℕ => ∑ u : Unit, m (Metric.ediam (cov2 n u))) atTop = 0 :=
    hsum_tend.liminf_eq
  rw [hlim0] at hmain2
  exact le_antisymm hmain2 bot_le

/-- 可数集合在任意满足 $m(r) \to 0$（$r \to 0^+$）的 Hausdorff 规范测度下测度为 $0$。 -/
lemma mkMetric_countable_zero (m : ℝ≥0∞ → ℝ≥0∞)
    (hm0 : Tendsto m (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) {S : Set ℝ} (hS : S.Countable) :
    Measure.mkMetric m S = 0 := by
  have hsub : S ⊆ ⋃ x : S, ({(x : ℝ)} : Set ℝ) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Set.mem_singleton x⟩
  have : Countable S := hS.to_subtype
  refine measure_mono_null hsub (measure_iUnion_null fun x => mkMetric_singleton_zero m hm0 x.1)

/-- Theorem 16(iii) 完整打包：对 $k \ge 1$，正负有符号精确极限集均为单可数 $L$-陪集，
    可数、Hausdorff 维数为 $0$，且对一切满足 $m(r) \to 0^+$ 的 Hausdorff 规范测度为 $0$。 -/
theorem trichotomy_part_iii_complete (k : ℕ) (hk : 1 ≤ k) :
    signedExactLimitSet ((k : ℝ) / 4) =
      (fun z : ℝ => xPlus k + z) '' Classification.latticeL ∧
    signedExactLimitSet (-((k : ℝ) / 4)) =
      (fun z : ℝ => -xPlus k + z) '' Classification.latticeL ∧
    (signedExactLimitSet ((k : ℝ) / 4)).Countable ∧
    (signedExactLimitSet (-((k : ℝ) / 4))).Countable ∧
    dimH (signedExactLimitSet ((k : ℝ) / 4)) = 0 ∧
    dimH (signedExactLimitSet (-((k : ℝ) / 4))) = 0 ∧
    (∀ m : ℝ≥0∞ → ℝ≥0∞, Tendsto m (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Measure.mkMetric m (signedExactLimitSet ((k : ℝ) / 4)) = 0 ∧
      Measure.mkMetric m (signedExactLimitSet (-((k : ℝ) / 4))) = 0) := by
  have hpos_eq := signedExactLimitSet_pos_eq_coset k hk
  have hneg_eq := signedExactLimitSet_neg_eq_coset k hk
  have hc_pos : (signedExactLimitSet ((k : ℝ) / 4)).Countable := by
    rw [hpos_eq]; exact SpectralGap.latticeL_countable.image _
  have hc_neg : (signedExactLimitSet (-((k : ℝ) / 4))).Countable := by
    rw [hneg_eq]; exact SpectralGap.latticeL_countable.image _
  refine ⟨hpos_eq, hneg_eq, hc_pos, hc_neg, hc_pos.dimH_zero, hc_neg.dimH_zero, ?_⟩
  intro m hm0
  exact ⟨mkMetric_countable_zero m hm0 hc_pos, mkMetric_countable_zero m hm0 hc_neg⟩

/-! ## 第二部分：§6.3 一般 $r \ge 1$ 多项式增长递推与 `lem:poly-growth` -/

/-- 一般多项式增长三项递推数据 $Q_{j+1} = (c j^r + d) Q_j + Q_{j-1}$（$j \ge J_0$）。 -/
structure PolyRecData where
  r : ℕ
  c : ℕ
  d : ℤ
  J₀ : ℕ
  hr : 1 ≤ r
  hc : 1 ≤ c
  hJ₀ : 1 ≤ J₀
  hinit : (2 : ℤ) ≤ (c : ℤ) * ((J₀ : ℤ) ^ r) + d
  Q : ℕ → ℤ
  hQ_pos : ∀ j : ℕ, 0 < Q j
  hQ_rec : ∀ j : ℕ, J₀ ≤ j → Q (j + 1) = ((c : ℤ) * ((j : ℤ) ^ r) + d) * Q j + Q (j - 1)

namespace PolyRecData

/-- 递推系数 $A_j := c j^r + d$。 -/
def A (P : PolyRecData) (j : ℕ) : ℤ := (P.c : ℤ) * ((j : ℤ) ^ P.r) + P.d

/-- 稳定起算指标 $J_1 := \max(J_0 + 1,\, 2|d| + 1)$。 -/
def J₁ (P : PolyRecData) : ℕ := max (P.J₀ + 1) (2 * P.d.natAbs + 1)

lemma J₁_ge_J₀_succ (P : PolyRecData) : P.J₀ + 1 ≤ P.J₁ := le_max_left _ _
lemma J₁_ge_two_abs_d_succ (P : PolyRecData) : 2 * P.d.natAbs + 1 ≤ P.J₁ := le_max_right _ _
lemma two_le_J₁ (P : PolyRecData) : 2 ≤ P.J₁ := by
  have := P.hJ₀; have := P.J₁_ge_J₀_succ; omega

lemma A_mono {P : PolyRecData} {i j : ℕ} (hij : i ≤ j) : P.A i ≤ P.A j := by
  unfold A
  have hc0 : (0 : ℤ) ≤ (P.c : ℤ) := Int.natCast_nonneg P.c
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
  have hijZ : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
  have hpow : (i : ℤ) ^ P.r ≤ (j : ℤ) ^ P.r := pow_le_pow_left₀ hi0 hijZ P.r
  nlinarith

lemma A_ge_two (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) : (2 : ℤ) ≤ P.A j := by
  exact le_trans P.hinit (A_mono hj)

/-- **Lemma `lem:poly-growth`(i)**：对一切 $j \ge J_0$，$Q_{j+1} > A_j Q_j \ge 2 Q_j$。 -/
lemma poly_Q_succ_gt_A_mul (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    P.A j * P.Q j < P.Q (j + 1) := by
  rw [P.hQ_rec j hj]
  have hprev := P.hQ_pos (j - 1)
  change P.A j * P.Q j < P.A j * P.Q j + P.Q (j - 1)
  linarith

lemma poly_Q_succ_ge_two_mul (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    2 * P.Q j ≤ P.A j * P.Q j ∧ P.A j * P.Q j < P.Q (j + 1) := by
  have hA := P.A_ge_two hj
  have hQ := P.hQ_pos j
  exact ⟨by nlinarith, P.poly_Q_succ_gt_A_mul hj⟩

lemma poly_Q_lt_succ (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    P.Q j < P.Q (j + 1) := by
  have h := P.poly_Q_succ_ge_two_mul hj
  have hQ := P.hQ_pos j
  linarith

lemma poly_Q_strictMonoOn (P : PolyRecData) : StrictMonoOn P.Q (Set.Ici P.J₀) := by
  intro a ha b _ hab
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k + 1 := ⟨b - a - 1, by omega⟩
  have haJ : P.J₀ ≤ a := ha
  have hstep : ∀ k : ℕ, P.Q a < P.Q (a + k + 1) := by
    intro k
    induction k with
    | zero => exact P.poly_Q_lt_succ haJ
    | succ k ih => exact lt_trans ih (P.poly_Q_lt_succ (by omega))
  exact hstep k

lemma poly_Q_geom (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) (m : ℕ) :
    (2 : ℝ) ^ m * (P.Q j : ℝ) ≤ (P.Q (j + m) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h := P.poly_Q_succ_ge_two_mul (show P.J₀ ≤ j + m by omega)
      have h2 : 2 * (P.Q (j + m) : ℝ) ≤ (P.Q (j + m + 1) : ℝ) := by
        exact_mod_cast le_trans h.1 (le_of_lt h.2)
      have hadd : j + (m + 1) = j + m + 1 := by omega
      rw [hadd]
      calc (2 : ℝ) ^ (m + 1) * (P.Q j : ℝ)
          = 2 * ((2 : ℝ) ^ m * (P.Q j : ℝ)) := by ring
        _ ≤ 2 * (P.Q (j + m) : ℝ) := by gcongr
        _ ≤ (P.Q (j + m + 1) : ℝ) := h2

/-- **Lemma `lem:poly-growth`(ii)**：对 $j \ge J_0 + 1$，$0 < Q_{j-1} < \frac{1}{2} Q_j < Q_j$ 与比值双侧界。 -/
lemma poly_Q_prev_lt_half (P : PolyRecData) {j : ℕ} (hj : P.J₀ + 1 ≤ j) :
    0 < (P.Q (j - 1) : ℝ) ∧ (P.Q (j - 1) : ℝ) < (1 / 2 : ℝ) * (P.Q j : ℝ) := by
  have hjm : P.J₀ ≤ j - 1 := by omega
  have h := P.poly_Q_succ_ge_two_mul hjm
  have hsub : j - 1 + 1 = j := by omega
  rw [hsub] at h
  have hQ : 2 * (P.Q (j - 1) : ℝ) < (P.Q j : ℝ) := by exact_mod_cast lt_of_le_of_lt h.1 h.2
  have hpos : 0 < (P.Q (j - 1) : ℝ) := by exact_mod_cast P.hQ_pos (j - 1)
  exact ⟨hpos, by linarith⟩

lemma poly_Q_ratio_bounds (P : PolyRecData) {j : ℕ} (hj : P.J₀ + 1 ≤ j) :
    (P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ) < (P.Q (j + 1) : ℝ) / (P.Q j : ℝ) ∧
    (P.Q (j + 1) : ℝ) / (P.Q j : ℝ) < (P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ) + 1 ∧
    (P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ) + 1 ≤
      ((P.c : ℝ) + |(P.d : ℝ)| + 1) * (j : ℝ) ^ P.r := by
  have hQpos : (0 : ℝ) < (P.Q j : ℝ) := by exact_mod_cast P.hQ_pos j
  have hprev := P.poly_Q_prev_lt_half hj
  have hrec : (P.Q (j + 1) : ℝ) =
      ((P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ)) * (P.Q j : ℝ) + (P.Q (j - 1) : ℝ) := by
    exact_mod_cast P.hQ_rec j (by omega)
  have h1 : (P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ) < (P.Q (j + 1) : ℝ) / (P.Q j : ℝ) := by
    rw [lt_div_iff₀ hQpos, hrec]
    linarith [hprev.1]
  have h2 : (P.Q (j + 1) : ℝ) / (P.Q j : ℝ) < (P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ) + 1 := by
    rw [div_lt_iff₀ hQpos, hrec]
    linarith [hprev.2]
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
    have := P.hJ₀
    exact_mod_cast (by omega : 1 ≤ j)
  have hjr : (1 : ℝ) ≤ (j : ℝ) ^ P.r := one_le_pow₀ hj1
  have h3 : (P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ) + 1 ≤
      ((P.c : ℝ) + |(P.d : ℝ)| + 1) * (j : ℝ) ^ P.r := by
    have hd : (P.d : ℝ) ≤ |(P.d : ℝ)| := le_abs_self _
    have hdpow : |(P.d : ℝ)| ≤ |(P.d : ℝ)| * (j : ℝ) ^ P.r := by nlinarith [abs_nonneg (P.d : ℝ)]
    nlinarith
  exact ⟨h1, h2, h3⟩

/-- **Lemma `lem:poly-growth`(iii)**：$j \ge J_1$ 时 $A_j \ge \frac{c}{2} j^r$ 与非渐近阶乘下界。 -/
lemma poly_A_ge_half_c (P : PolyRecData) {j : ℕ} (hj : P.J₁ ≤ j) :
    ((P.c : ℝ) / 2) * (j : ℝ) ^ P.r ≤ (P.A j : ℝ) := by
  have hj_abs : 2 * P.d.natAbs + 1 ≤ j := le_trans P.J₁_ge_two_abs_d_succ hj
  have hd_le : |(P.d : ℝ)| ≤ (j : ℝ) / 2 := by
    have hnat : (P.d.natAbs : ℝ) = |(P.d : ℝ)| :=
      (Int.cast_natCast P.d.natAbs).symm.trans
        ((congrArg (Int.cast : ℤ → ℝ) (Int.natCast_natAbs P.d)).trans Int.cast_abs)
    rw [← hnat]
    have hj_r : 2 * (P.d.natAbs : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj_abs
    linarith
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1 ≤ j)
  have hjr_ge_j : (j : ℝ) ≤ (j : ℝ) ^ P.r := by
    calc (j : ℝ) = (j : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (j : ℝ) ^ P.r := pow_le_pow_right₀ hj1 P.hr
  have hc1 : (1 : ℝ) ≤ (P.c : ℝ) := by exact_mod_cast P.hc
  have hcj : (j : ℝ) / 2 ≤ ((P.c : ℝ) / 2) * (j : ℝ) ^ P.r := by nlinarith
  have hd_neg : -|(P.d : ℝ)| ≤ (P.d : ℝ) := neg_abs_le _
  have hA : (P.A j : ℝ) = (P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ) := by
    unfold A; push_cast; ring
  linarith

/-- 非渐近阶乘下界常数 $C_{J_1} > 0$。 -/
def C_J₁ (P : PolyRecData) : ℝ :=
  (P.Q P.J₁ : ℝ) / (((P.c : ℝ) / 2) ^ P.J₁ * ((Nat.factorial (P.J₁ - 1) : ℝ) ^ P.r))

lemma C_J₁_pos (P : PolyRecData) : 0 < P.C_J₁ := by
  unfold C_J₁
  have hQ : (0 : ℝ) < (P.Q P.J₁ : ℝ) := by exact_mod_cast P.hQ_pos P.J₁
  have hc : (0 : ℝ) < (P.c : ℝ) / 2 := by
    have : (1 : ℝ) ≤ (P.c : ℝ) := by exact_mod_cast P.hc
    linarith
  have hf : (0 : ℝ) < (Nat.factorial (P.J₁ - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (P.J₁ - 1)
  positivity

lemma poly_Q_ge_half_c_factorial_aux (P : PolyRecData) (n : ℕ) :
    (P.Q P.J₁ : ℝ) * ((P.c : ℝ) / 2) ^ n *
      ((Nat.factorial (P.J₁ + n - 1) : ℝ) / (Nat.factorial (P.J₁ - 1) : ℝ)) ^ P.r ≤
      (P.Q (P.J₁ + n) : ℝ) := by
  induction n with
  | zero =>
      have hf : (Nat.factorial (P.J₁ - 1) : ℝ) ≠ 0 := by positivity
      simp [hf]
  | succ n ih =>
      have hJ : P.J₁ ≤ P.J₁ + n := by omega
      have hJ₀ : P.J₀ ≤ P.J₁ + n := le_trans (by have := P.J₁_ge_J₀_succ; omega) hJ
      have hsucc := P.poly_Q_succ_gt_A_mul hJ₀
      have hA := P.poly_A_ge_half_c hJ
      have hQpos : (0 : ℝ) < (P.Q (P.J₁ + n) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₁ + n)
      have hsuccR : (P.A (P.J₁ + n) : ℝ) * (P.Q (P.J₁ + n) : ℝ) < (P.Q (P.J₁ + n + 1) : ℝ) := by
        exact_mod_cast hsucc
      have hstep : ((P.c : ℝ) / 2) * ((P.J₁ + n : ℕ) : ℝ) ^ P.r * (P.Q (P.J₁ + n) : ℝ) ≤
          (P.Q (P.J₁ + n + 1) : ℝ) := by
        have h1 : ((P.c : ℝ) / 2) * ((P.J₁ + n : ℕ) : ℝ) ^ P.r * (P.Q (P.J₁ + n) : ℝ) ≤
            (P.A (P.J₁ + n) : ℝ) * (P.Q (P.J₁ + n) : ℝ) :=
          mul_le_mul_of_nonneg_right hA (le_of_lt hQpos)
        exact le_trans h1 (le_of_lt hsuccR)
      have h2_le : 2 ≤ P.J₁ + n := le_trans P.two_le_J₁ hJ
      have hsub1 : P.J₁ + (n + 1) - 1 = (P.J₁ + n - 1) + 1 := by omega
      have hfact : (Nat.factorial (P.J₁ + (n + 1) - 1) : ℝ) =
          ((P.J₁ + n : ℕ) : ℝ) * (Nat.factorial (P.J₁ + n - 1) : ℝ) := by
        rw [hsub1, Nat.factorial_succ]
        have heq : P.J₁ + n - 1 + 1 = P.J₁ + n := by omega
        rw [heq]
        push_cast
        ring
      have hadd : P.J₁ + (n + 1) = P.J₁ + n + 1 := by omega
      rw [hadd]
      calc (P.Q P.J₁ : ℝ) * ((P.c : ℝ) / 2) ^ (n + 1) *
            ((Nat.factorial (P.J₁ + (n + 1) - 1) : ℝ) / (Nat.factorial (P.J₁ - 1) : ℝ)) ^ P.r
          = ((P.c : ℝ) / 2) * ((P.J₁ + n : ℕ) : ℝ) ^ P.r *
              ((P.Q P.J₁ : ℝ) * ((P.c : ℝ) / 2) ^ n *
                ((Nat.factorial (P.J₁ + n - 1) : ℝ) / (Nat.factorial (P.J₁ - 1) : ℝ)) ^ P.r) := by
              rw [hfact, mul_div_assoc, mul_pow, pow_succ]
              ring
        _ ≤ ((P.c : ℝ) / 2) * ((P.J₁ + n : ℕ) : ℝ) ^ P.r * (P.Q (P.J₁ + n) : ℝ) := by
              have hc0 : 0 ≤ ((P.c : ℝ) / 2) * ((P.J₁ + n : ℕ) : ℝ) ^ P.r := by positivity
              exact mul_le_mul_of_nonneg_left ih hc0
        _ ≤ (P.Q (P.J₁ + n + 1) : ℝ) := hstep

/-- **Lemma `lem:poly-growth`(iii)（非渐近阶乘下界）**：对所有 $m \ge J_1$，
    $Q_m \ge C_{J_1} \left(\frac{c}{2^{r+1}}\right)^m (m!)^r$。 -/
theorem poly_Q_ge_factorial (P : PolyRecData) {m : ℕ} (hm : P.J₁ ≤ m) :
    P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ m * (Nat.factorial m : ℝ) ^ P.r ≤
      (P.Q m : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  have haux := P.poly_Q_ge_half_c_factorial_aux n
  have h2J : 2 ≤ P.J₁ := P.two_le_J₁
  have hm_ge1 : 1 ≤ P.J₁ + n := by omega
  have hm_pos : (0 : ℝ) < ((P.J₁ + n : ℕ) : ℝ) := by exact_mod_cast hm_ge1
  have hfact_eq : (Nat.factorial (P.J₁ + n) : ℝ) =
      ((P.J₁ + n : ℕ) : ℝ) * (Nat.factorial (P.J₁ + n - 1) : ℝ) := by
    have hsucc : P.J₁ + n = (P.J₁ + n - 1) + 1 := by omega
    conv_lhs => rw [hsucc, Nat.factorial_succ]
    rw [← hsucc]
    push_cast
    ring
  have hf_pos : (0 : ℝ) < (Nat.factorial (P.J₁ - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (P.J₁ - 1)
  have hc_pos : (0 : ℝ) < (P.c : ℝ) / 2 := by
    have : (1 : ℝ) ≤ (P.c : ℝ) := by exact_mod_cast P.hc
    linarith
  have hm_le_pow2 : ((P.J₁ + n : ℕ) : ℝ) ≤ (2 : ℝ) ^ (P.J₁ + n) := by
    exact_mod_cast Nat.le_of_lt (Nat.lt_pow_self (n := P.J₁ + n) (by norm_num : 1 < 2))
  have hmr_le : ((P.J₁ + n : ℕ) : ℝ) ^ P.r ≤ ((2 : ℝ) ^ P.r) ^ (P.J₁ + n) := by
    calc ((P.J₁ + n : ℕ) : ℝ) ^ P.r
        ≤ ((2 : ℝ) ^ (P.J₁ + n)) ^ P.r := pow_le_pow_left₀ (le_of_lt hm_pos) hm_le_pow2 P.r
      _ = ((2 : ℝ) ^ P.r) ^ (P.J₁ + n) := by rw [← pow_mul, mul_comm, pow_mul]
  have hrhs_eq :
      (P.Q P.J₁ : ℝ) * ((P.c : ℝ) / 2) ^ n *
        ((Nat.factorial (P.J₁ + n - 1) : ℝ) / (Nat.factorial (P.J₁ - 1) : ℝ)) ^ P.r =
      P.C_J₁ * ((P.c : ℝ) / 2) ^ (P.J₁ + n) *
        ((Nat.factorial (P.J₁ + n) : ℝ) ^ P.r / ((P.J₁ + n : ℕ) : ℝ) ^ P.r) := by
    unfold C_J₁
    have hc0 : (P.c : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.hc)
    have hpow_ne : ((P.c : ℝ) / 2) ^ P.J₁ ≠ 0 := by positivity
    have hf_ne : (Nat.factorial (P.J₁ - 1) : ℝ) ^ P.r ≠ 0 := by positivity
    have hm_ne : ((P.J₁ + n : ℕ) : ℝ) ^ P.r ≠ 0 := by positivity
    rw [hfact_eq, mul_pow, pow_add]
    simp only [div_pow]
    field_simp
  have hdiv_le : ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (P.J₁ + n) ≤
      ((P.c : ℝ) / 2) ^ (P.J₁ + n) / ((P.J₁ + n : ℕ) : ℝ) ^ P.r := by
    have h2r_pos : (0 : ℝ) < ((2 : ℝ) ^ P.r) ^ (P.J₁ + n) := by positivity
    have hmr_pos : (0 : ℝ) < ((P.J₁ + n : ℕ) : ℝ) ^ P.r := by positivity
    have h1 : ((P.c : ℝ) / 2) ^ (P.J₁ + n) / ((2 : ℝ) ^ P.r) ^ (P.J₁ + n) ≤
        ((P.c : ℝ) / 2) ^ (P.J₁ + n) / ((P.J₁ + n : ℕ) : ℝ) ^ P.r :=
      div_le_div_of_nonneg_left (by positivity) hmr_pos hmr_le
    have h2 : ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (P.J₁ + n) =
        ((P.c : ℝ) / 2) ^ (P.J₁ + n) / ((2 : ℝ) ^ P.r) ^ (P.J₁ + n) := by
      rw [← div_pow]
      congr 1
      rw [pow_succ']
      ring
    rwa [h2]
  have hC_nn : 0 ≤ P.C_J₁ * (Nat.factorial (P.J₁ + n) : ℝ) ^ P.r :=
    mul_nonneg (le_of_lt P.C_J₁_pos) (by positivity)
  calc P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (P.J₁ + n) *
        (Nat.factorial (P.J₁ + n) : ℝ) ^ P.r
      = (P.C_J₁ * (Nat.factorial (P.J₁ + n) : ℝ) ^ P.r) *
          ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (P.J₁ + n) := by ring
    _ ≤ (P.C_J₁ * (Nat.factorial (P.J₁ + n) : ℝ) ^ P.r) *
          (((P.c : ℝ) / 2) ^ (P.J₁ + n) / ((P.J₁ + n : ℕ) : ℝ) ^ P.r) :=
        mul_le_mul_of_nonneg_left hdiv_le hC_nn
    _ = P.C_J₁ * ((P.c : ℝ) / 2) ^ (P.J₁ + n) *
          ((Nat.factorial (P.J₁ + n) : ℝ) ^ P.r / ((P.J₁ + n : ℕ) : ℝ) ^ P.r) := by ring
    _ = (P.Q P.J₁ : ℝ) * ((P.c : ℝ) / 2) ^ n *
          ((Nat.factorial (P.J₁ + n - 1) : ℝ) / (Nat.factorial (P.J₁ - 1) : ℝ)) ^ P.r :=
        hrhs_eq.symm
    _ ≤ (P.Q (P.J₁ + n) : ℝ) := haux

/-- **Lemma `lem:poly-growth` 推论**：对任意实指数 $\alpha \in \mathbb{R}$，
    $m^\alpha / Q_m \to 0$（$m \to \infty$）。 -/
theorem poly_pow_div_Q_tendsto_zero (P : PolyRecData) (α : ℝ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ α / (P.Q m : ℝ)) atTop (nhds 0) := by
  obtain ⟨K, hK⟩ := exists_nat_ge α
  set B : ℝ := (P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)
  have hBpos : 0 < B := by
    have : (1 : ℝ) ≤ (P.c : ℝ) := by exact_mod_cast P.hc
    positivity
  set R : ℝ := (2 : ℝ) ^ K / B
  have hfact_lim : Tendsto (fun m : ℕ => R ^ m / (Nat.factorial m : ℝ)) atTop (nhds 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop R
  have hlim : Tendsto (fun m : ℕ => (1 / P.C_J₁) * (R ^ m / (Nat.factorial m : ℝ)))
      atTop (nhds 0) := by
    simpa using hfact_lim.const_mul (1 / P.C_J₁)
  have hbound : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ α / (P.Q m : ℝ) ≤ (1 / P.C_J₁) * (R ^ m / (Nat.factorial m : ℝ)) := by
    filter_upwards [eventually_ge_atTop P.J₁] with m hm
    have hm1 : 1 ≤ m := le_trans (by have := P.two_le_J₁; omega) hm
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hm_pow : (m : ℝ) ^ α ≤ (m : ℝ) ^ K := by
      calc (m : ℝ) ^ α ≤ (m : ℝ) ^ (K : ℝ) := Real.rpow_le_rpow_of_exponent_le hm_ge1 hK
        _ = (m : ℝ) ^ K := Real.rpow_natCast _ _
    have hm_le_pow2 : (m : ℝ) ≤ (2 : ℝ) ^ m := by
      exact_mod_cast Nat.le_of_lt (Nat.lt_pow_self (n := m) (by norm_num : 1 < 2))
    have hmK : (m : ℝ) ^ K ≤ ((2 : ℝ) ^ K) ^ m := by
      calc (m : ℝ) ^ K ≤ ((2 : ℝ) ^ m) ^ K := pow_le_pow_left₀ (le_of_lt hm_pos) hm_le_pow2 K
        _ = ((2 : ℝ) ^ K) ^ m := by rw [← pow_mul, mul_comm, pow_mul]
    have hfact1 : (1 : ℝ) ≤ (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hfactr : (Nat.factorial m : ℝ) ≤ (Nat.factorial m : ℝ) ^ P.r := by
      calc (Nat.factorial m : ℝ) = (Nat.factorial m : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (Nat.factorial m : ℝ) ^ P.r := pow_le_pow_right₀ hfact1 P.hr
    have hQge := P.poly_Q_ge_factorial hm
    have hQge' : P.C_J₁ * B ^ m * (Nat.factorial m : ℝ) ≤ (P.Q m : ℝ) := by
      have hC_B : 0 ≤ P.C_J₁ * B ^ m := mul_nonneg (le_of_lt P.C_J₁_pos) (by positivity)
      calc P.C_J₁ * B ^ m * (Nat.factorial m : ℝ)
          ≤ P.C_J₁ * B ^ m * (Nat.factorial m : ℝ) ^ P.r :=
            mul_le_mul_of_nonneg_left hfactr hC_B
        _ ≤ (P.Q m : ℝ) := hQge
    have hCpos := P.C_J₁_pos
    have hden_pos : 0 < P.C_J₁ * B ^ m * (Nat.factorial m : ℝ) := by positivity
    have hQpos : (0 : ℝ) < (P.Q m : ℝ) := by exact_mod_cast P.hQ_pos m
    calc (m : ℝ) ^ α / (P.Q m : ℝ)
        ≤ ((2 : ℝ) ^ K) ^ m / (P.Q m : ℝ) :=
          div_le_div_of_nonneg_right (le_trans hm_pow hmK) (le_of_lt hQpos)
      _ ≤ ((2 : ℝ) ^ K) ^ m / (P.C_J₁ * B ^ m * (Nat.factorial m : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) hden_pos hQge'
      _ = (1 / P.C_J₁) * (R ^ m / (Nat.factorial m : ℝ)) := by
          dsimp [R, B]
          simp only [div_pow]
          field_simp
  have hnn : ∀ᶠ m : ℕ in atTop, 0 ≤ (m : ℝ) ^ α / (P.Q m : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hQpos : (0 : ℝ) < (P.Q m : ℝ) := by exact_mod_cast P.hQ_pos m
    have hm0 : 0 ≤ (m : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg m) α
    exact div_nonneg hm0 (le_of_lt hQpos)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hnn hbound

lemma poly_Q_tendsto_atTop (P : PolyRecData) :
    Tendsto (fun j : ℕ => (P.Q j : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun j : ℕ => (2 : ℝ) ^ j * (P.Q P.J₀ : ℝ)) atTop atTop := by
    have hQ0 : (0 : ℝ) < (P.Q P.J₀ : ℝ) := by exact_mod_cast P.hQ_pos P.J₀
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hQ0
  have hshift : Tendsto (fun j : ℕ => (P.Q (P.J₀ + j) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun j => P.poly_Q_geom (le_refl P.J₀) j) hpow
  have hcomp : Tendsto (fun j : ℕ => (P.Q (j + P.J₀) : ℝ)) atTop atTop := by
    simpa [Nat.add_comm] using hshift
  exact (tendsto_add_atTop_iff_nat P.J₀).mp hcomp

/-! ## 第三部分：`lem:poly-lattice`（基本解、Casorati 行列式、交错收敛与内蕴晶格） -/

/-- 从 $J_0 - 1$ 起步的配对递推 $X_{j+1} = A_j X_j + X_{j-1}$。 -/
def recPair (P : PolyRecData) (u0 u1 : ℤ) : ℕ → ℤ × ℤ
  | 0 => (u0, u1)
  | n + 1 =>
      let prev := recPair P u0 u1 n
      (prev.2, P.A (P.J₀ + n) * prev.2 + prev.1)

@[simp] lemma recPair_zero (P : PolyRecData) (u0 u1 : ℤ) :
    recPair P u0 u1 0 = (u0, u1) := rfl

lemma recPair_succ (P : PolyRecData) (u0 u1 : ℤ) (n : ℕ) :
    recPair P u0 u1 (n + 1) =
      ((recPair P u0 u1 n).2, P.A (P.J₀ + n) * (recPair P u0 u1 n).2 + (recPair P u0 u1 n).1) :=
  rfl

lemma recPair_snd (P : PolyRecData) (u0 u1 : ℤ) (n : ℕ) :
    (recPair P u0 u1 n).2 = (recPair P u0 u1 (n + 1)).1 := by
  cases n <;> rfl

/-- 基本解 $U_j$（$U_{J_0-1} = 1, U_{J_0} = 0$）。 -/
def fundU (P : PolyRecData) (j : ℕ) : ℤ := (recPair P 1 0 (j - (P.J₀ - 1))).1

/-- 基本解 $V_j$（$V_{J_0-1} = 0, V_{J_0} = 1$）。 -/
def fundV (P : PolyRecData) (j : ℕ) : ℤ := (recPair P 0 1 (j - (P.J₀ - 1))).1

lemma fundU_init0 (P : PolyRecData) : P.fundU (P.J₀ - 1) = 1 := by
  simp [fundU]

lemma fundU_init1 (P : PolyRecData) : P.fundU P.J₀ = 0 := by
  have hsub : P.J₀ - (P.J₀ - 1) = 1 := by have := P.hJ₀; omega
  simp [fundU, hsub, recPair]

lemma fundV_init0 (P : PolyRecData) : P.fundV (P.J₀ - 1) = 0 := by
  simp [fundV]

lemma fundV_init1 (P : PolyRecData) : P.fundV P.J₀ = 1 := by
  have hsub : P.J₀ - (P.J₀ - 1) = 1 := by have := P.hJ₀; omega
  simp [fundV, hsub, recPair]

lemma recPair_rec_idx (P : PolyRecData) (u0 u1 : ℤ) {j : ℕ} (hj : P.J₀ ≤ j) :
    (recPair P u0 u1 (j + 1 - (P.J₀ - 1))).1 =
      P.A j * (recPair P u0 u1 (j - (P.J₀ - 1))).1 +
        (recPair P u0 u1 (j - 1 - (P.J₀ - 1))).1 := by
  have hJ := P.hJ₀
  obtain ⟨n, hn⟩ : ∃ n, j = P.J₀ + n := ⟨j - P.J₀, by omega⟩
  subst hn
  have h1 : P.J₀ + n + 1 - (P.J₀ - 1) = n + 2 := by omega
  have h2 : P.J₀ + n - (P.J₀ - 1) = n + 1 := by omega
  have h3 : P.J₀ + n - 1 - (P.J₀ - 1) = n := by omega
  rw [h1, h2, h3]
  have hr := congrArg Prod.fst (recPair_succ P u0 u1 (n + 1))
  rw [recPair_snd] at hr
  exact hr

lemma fundU_rec (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    P.fundU (j + 1) = P.A j * P.fundU j + P.fundU (j - 1) :=
  recPair_rec_idx P 1 0 hj

lemma fundV_rec (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    P.fundV (j + 1) = P.A j * P.fundV j + P.fundV (j - 1) :=
  recPair_rec_idx P 0 1 hj

/-- **Lemma `lem:poly-lattice`(i) 第一部分**：对一切 $j \ge J_0 - 1$，
    $Q_j = Q_{J_0-1} U_j + Q_{J_0} V_j$。 -/
theorem poly_Q_eq_lincomb (P : PolyRecData) {j : ℕ} (hj : P.J₀ - 1 ≤ j) :
    P.Q j = P.Q (P.J₀ - 1) * P.fundU j + P.Q P.J₀ * P.fundV j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases h0 : j = P.J₀ - 1
      · subst h0; simp [fundU_init0, fundV_init0]
      · by_cases h1 : j = P.J₀
        · subst h1; simp [fundU_init1, fundV_init1]
        · have hj_ge : P.J₀ + 1 ≤ j := by omega
          have hjm : P.J₀ ≤ j - 1 := by omega
          have hQ := P.hQ_rec (j - 1) hjm
          have hU := P.fundU_rec hjm
          have hV := P.fundV_rec hjm
          have hs : j - 1 + 1 = j := by omega
          rw [hs] at hQ hU hV
          have ih1 := ih (j - 1) (by omega) (by omega)
          have ih2 := ih (j - 1 - 1) (by omega) (by omega)
          rw [hQ, hU, hV, ih1, ih2]
          change P.A (j - 1) * (P.Q (P.J₀ - 1) * P.fundU (j - 1) + P.Q P.J₀ * P.fundV (j - 1)) +
              (P.Q (P.J₀ - 1) * P.fundU (j - 1 - 1) + P.Q P.J₀ * P.fundV (j - 1 - 1)) =
            P.Q (P.J₀ - 1) * (P.A (j - 1) * P.fundU (j - 1) + P.fundU (j - 1 - 1)) +
              P.Q P.J₀ * (P.A (j - 1) * P.fundV (j - 1) + P.fundV (j - 1 - 1))
          ring

/-- **Lemma `lem:poly-lattice`(i) 第二部分（Casorati 恒等式）**：
    对一切 $j \ge J_0 - 1$，$U_j V_{j+1} - U_{j+1} V_j = (-1)^{j + 1 - J_0}$。 -/
theorem poly_casorati (P : PolyRecData) {j : ℕ} (hj : P.J₀ - 1 ≤ j) :
    P.fundU j * P.fundV (j + 1) - P.fundU (j + 1) * P.fundV j =
      (-1 : ℤ) ^ (j + 1 - P.J₀) := by
  obtain ⟨n, hn⟩ : ∃ n, j = (P.J₀ - 1) + n := ⟨j - (P.J₀ - 1), by omega⟩
  subst hn
  induction n with
  | zero =>
      have hsub : P.J₀ - 1 + 0 + 1 - P.J₀ = 0 := by have := P.hJ₀; omega
      have hadd1 : P.J₀ - 1 + 0 + 1 = P.J₀ := by have := P.hJ₀; omega
      rw [Nat.add_zero, hsub, hadd1, fundU_init0, fundU_init1, fundV_init0, fundV_init1]
      norm_num
  | succ n ih =>
      have hJ := P.hJ₀
      have hidx : P.J₀ ≤ P.J₀ - 1 + (n + 1) := by omega
      have hU := P.fundU_rec hidx
      have hV := P.fundV_rec hidx
      have hsub1 : P.J₀ - 1 + (n + 1) - 1 = P.J₀ - 1 + n := by omega
      rw [hsub1] at hU hV
      rw [hU, hV]
      have ih' := ih (by omega)
      calc P.fundU (P.J₀ - 1 + (n + 1)) *
              (P.A (P.J₀ - 1 + (n + 1)) * P.fundV (P.J₀ - 1 + (n + 1)) +
                P.fundV (P.J₀ - 1 + n)) -
            (P.A (P.J₀ - 1 + (n + 1)) * P.fundU (P.J₀ - 1 + (n + 1)) +
                P.fundU (P.J₀ - 1 + n)) *
              P.fundV (P.J₀ - 1 + (n + 1))
          = -(P.fundU (P.J₀ - 1 + n) * P.fundV (P.J₀ - 1 + (n + 1)) -
              P.fundU (P.J₀ - 1 + (n + 1)) * P.fundV (P.J₀ - 1 + n)) := by ring
        _ = -((-1 : ℤ) ^ (P.J₀ - 1 + n + 1 - P.J₀)) := by
              have hadd_n : P.J₀ - 1 + (n + 1) = P.J₀ - 1 + n + 1 := by omega
              rw [hadd_n, ih']
        _ = (-1 : ℤ) ^ (P.J₀ - 1 + n + 1 - P.J₀) * (-1 : ℤ) := by ring
        _ = (-1 : ℤ) ^ (P.J₀ - 1 + (n + 1) + 1 - P.J₀) := by
              have hexp : P.J₀ - 1 + (n + 1) + 1 - P.J₀ = (P.J₀ - 1 + n + 1 - P.J₀) + 1 := by omega
              rw [hexp, pow_succ]

lemma poly_ratio_diff_U (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    (P.fundU (j + 1) : ℝ) / (P.Q (j + 1) : ℝ) - (P.fundU j : ℝ) / (P.Q j : ℝ) =
      (-1 : ℝ) ^ (j - P.J₀) * (P.Q P.J₀ : ℝ) / ((P.Q j : ℝ) * (P.Q (j + 1) : ℝ)) := by
  have hQ1 : (P.Q j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.hQ_pos j)
  have hQ2 : (P.Q (j + 1) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.hQ_pos (j + 1))
  have hlin1 : (P.Q j : ℝ) =
      (P.Q (P.J₀ - 1) : ℝ) * (P.fundU j : ℝ) + (P.Q P.J₀ : ℝ) * (P.fundV j : ℝ) := by
    exact_mod_cast P.poly_Q_eq_lincomb (by omega)
  have hlin2 : (P.Q (j + 1) : ℝ) =
      (P.Q (P.J₀ - 1) : ℝ) * (P.fundU (j + 1) : ℝ) + (P.Q P.J₀ : ℝ) * (P.fundV (j + 1) : ℝ) := by
    exact_mod_cast P.poly_Q_eq_lincomb (by omega)
  have hcas : (P.fundU j : ℝ) * (P.fundV (j + 1) : ℝ) -
      (P.fundU (j + 1) : ℝ) * (P.fundV j : ℝ) = (-1 : ℝ) ^ (j + 1 - P.J₀) := by
    exact_mod_cast P.poly_casorati (by omega)
  have hexp : j + 1 - P.J₀ = (j - P.J₀) + 1 := by omega
  rw [hexp, pow_succ] at hcas
  field_simp
  rw [hlin1, hlin2]
  linear_combination -(P.Q P.J₀ : ℝ) * hcas

lemma poly_ratio_diff_V (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    (P.fundV (j + 1) : ℝ) / (P.Q (j + 1) : ℝ) - (P.fundV j : ℝ) / (P.Q j : ℝ) =
      (-1 : ℝ) ^ (j + 1 - P.J₀) * (P.Q (P.J₀ - 1) : ℝ) / ((P.Q j : ℝ) * (P.Q (j + 1) : ℝ)) := by
  have hQ1 : (P.Q j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.hQ_pos j)
  have hQ2 : (P.Q (j + 1) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.hQ_pos (j + 1))
  have hlin1 : (P.Q j : ℝ) =
      (P.Q (P.J₀ - 1) : ℝ) * (P.fundU j : ℝ) + (P.Q P.J₀ : ℝ) * (P.fundV j : ℝ) := by
    exact_mod_cast P.poly_Q_eq_lincomb (by omega)
  have hlin2 : (P.Q (j + 1) : ℝ) =
      (P.Q (P.J₀ - 1) : ℝ) * (P.fundU (j + 1) : ℝ) + (P.Q P.J₀ : ℝ) * (P.fundV (j + 1) : ℝ) := by
    exact_mod_cast P.poly_Q_eq_lincomb (by omega)
  have hcas : (P.fundU j : ℝ) * (P.fundV (j + 1) : ℝ) -
      (P.fundU (j + 1) : ℝ) * (P.fundV j : ℝ) = (-1 : ℝ) ^ (j + 1 - P.J₀) := by
    exact_mod_cast P.poly_casorati (by omega)
  field_simp
  rw [hlin1, hlin2]
  linear_combination (P.Q (P.J₀ - 1) : ℝ) * hcas

/-- 严格递减正项交错级数的界：`0 < b 0 - b 1 ≤ ∑' n, (-1)^n b_n ≤ b 0 - (b 1 - b 2) < b 0`。 -/
lemma alt_tsum_bounds {b : ℕ → ℝ} (hb_pos : ∀ n : ℕ, 0 < b n)
    (hb_dec : ∀ n : ℕ, b (n + 1) < b n) (hb_sum : Summable b) :
    0 < ∑' n : ℕ, (-1 : ℝ) ^ n * b n ∧
    ∑' n : ℕ, (-1 : ℝ) ^ n * b n < b 0 := by
  let f : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * b n
  have hf_sum : Summable f := by
    refine Summable.of_norm_bounded hb_sum (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (hb_pos n)]
  have hlim := hf_sum.hasSum.tendsto_sum_nat
  let S : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, f n
  have hS_even_mono : ∀ k : ℕ, S (2 * k) ≤ S (2 * (k + 1)) := by
    intro k
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    dsimp [S]
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ]
    have hf1 : f (2 * k) = b (2 * k) := by simp [f]
    have hf2 : f (2 * k + 1) = -b (2 * k + 1) := by simp [f, pow_succ]
    linarith [hb_dec (2 * k)]
  have hS_odd_anti : ∀ k : ℕ, S (2 * (k + 1) + 1) ≤ S (2 * k + 1) := by
    intro k
    have h2 : 2 * (k + 1) + 1 = (2 * k + 2) + 1 := by ring
    have h1 : 2 * k + 2 = (2 * k + 1) + 1 := by ring
    dsimp [S]
    rw [h2, Finset.sum_range_succ, h1, Finset.sum_range_succ]
    have hf1 : f (2 * k + 1) = -b (2 * k + 1) := by simp [f, pow_succ]
    have hf2 : f (2 * k + 2) = b (2 * k + 2) := by
      have : 2 * k + 2 = 2 * (k + 1) := by ring
      simp [f, this]
    linarith [hb_dec (2 * k + 1)]
  have hS_even_ge : ∀ k : ℕ, b 0 - b 1 ≤ S (2 * (k + 1)) := by
    intro k
    induction k with
    | zero =>
        dsimp [S]
        norm_num [Finset.sum_range_succ, f]
    | succ k ih => exact le_trans ih (hS_even_mono (k + 1))
  have hS_odd_le : ∀ k : ℕ, S (2 * (k + 1) + 1) ≤ b 0 - b 1 + b 2 := by
    intro k
    induction k with
    | zero =>
        dsimp [S]
        norm_num [Finset.sum_range_succ, f]
    | succ k ih => exact le_trans (hS_odd_anti (k + 1)) ih
  have hlim_even : Tendsto (fun k : ℕ => S (2 * (k + 1))) atTop (nhds (∑' n, f n)) := by
    refine hlim.comp ?_
    rw [tendsto_atTop_atTop]
    intro N; exact ⟨N, fun k hk => by omega⟩
  have hlim_odd : Tendsto (fun k : ℕ => S (2 * (k + 1) + 1)) atTop (nhds (∑' n, f n)) := by
    refine hlim.comp ?_
    rw [tendsto_atTop_atTop]
    intro N; exact ⟨N, fun k hk => by omega⟩
  have hlo : b 0 - b 1 ≤ ∑' n, f n :=
    ge_of_tendsto hlim_even (Filter.Eventually.of_forall hS_even_ge)
  have hhi : ∑' n, f n ≤ b 0 - b 1 + b 2 :=
    le_of_tendsto hlim_odd (Filter.Eventually.of_forall hS_odd_le)
  exact ⟨lt_of_lt_of_le (sub_pos.mpr (hb_dec 0)) hlo,
    lt_of_le_of_lt hhi (by linarith [hb_dec 1])⟩

lemma poly_summable_inv_Q_mul_succ (P : PolyRecData) :
    Summable (fun j : ℕ => 1 / ((P.Q (P.J₀ + j) : ℝ) * (P.Q (P.J₀ + j + 1) : ℝ))) := by
  have hQ0 : (0 : ℝ) < (P.Q P.J₀ : ℝ) := by exact_mod_cast P.hQ_pos P.J₀
  have hQ1 : (0 : ℝ) < (P.Q (P.J₀ + 1) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ + 1)
  have hbound : ∀ j : ℕ,
      1 / ((P.Q (P.J₀ + j) : ℝ) * (P.Q (P.J₀ + j + 1) : ℝ)) ≤
        (1 / ((P.Q P.J₀ : ℝ) * (P.Q (P.J₀ + 1) : ℝ))) * (1 / 4 : ℝ) ^ j := by
    intro j
    have hg1 := P.poly_Q_geom (le_refl P.J₀) j
    have hg2 := P.poly_Q_geom (by omega : P.J₀ ≤ P.J₀ + 1) j
    have hadd : P.J₀ + 1 + j = P.J₀ + j + 1 := by omega
    rw [hadd] at hg2
    have hQa : (0 : ℝ) < (P.Q (P.J₀ + j) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ + j)
    have hQb : (0 : ℝ) < (P.Q (P.J₀ + j + 1) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ + j + 1)
    have hmul : (4 : ℝ) ^ j * ((P.Q P.J₀ : ℝ) * (P.Q (P.J₀ + 1) : ℝ)) ≤
        (P.Q (P.J₀ + j) : ℝ) * (P.Q (P.J₀ + j + 1) : ℝ) := by
      calc (4 : ℝ) ^ j * ((P.Q P.J₀ : ℝ) * (P.Q (P.J₀ + 1) : ℝ))
          = ((2 : ℝ) ^ j * (P.Q P.J₀ : ℝ)) * ((2 : ℝ) ^ j * (P.Q (P.J₀ + 1) : ℝ)) := by
              rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
        _ ≤ (P.Q (P.J₀ + j) : ℝ) * (P.Q (P.J₀ + j + 1) : ℝ) :=
              mul_le_mul hg1 hg2 (by positivity) (le_of_lt hQa)
    rw [div_le_iff₀ (mul_pos hQa hQb)]
    have hpow : (1 / 4 : ℝ) ^ j * (4 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
    calc (1 : ℝ) = (1 / 4 : ℝ) ^ j * (4 : ℝ) ^ j := hpow.symm
      _ = ((1 / ((P.Q P.J₀ : ℝ) * (P.Q (P.J₀ + 1) : ℝ))) * (1 / 4 : ℝ) ^ j) *
            ((4 : ℝ) ^ j * ((P.Q P.J₀ : ℝ) * (P.Q (P.J₀ + 1) : ℝ))) := by field_simp
      _ ≤ ((1 / ((P.Q P.J₀ : ℝ) * (P.Q (P.J₀ + 1) : ℝ))) * (1 / 4 : ℝ) ^ j) *
            ((P.Q (P.J₀ + j) : ℝ) * (P.Q (P.J₀ + j + 1) : ℝ)) := by
            gcongr
  exact Summable.of_nonneg_of_le
    (fun j => div_nonneg zero_le_one
      (mul_nonneg (by exact_mod_cast (P.hQ_pos _).le) (by exact_mod_cast (P.hQ_pos _).le)))
    hbound ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)

/-- 基本解极限 $\alpha_U := \lim_{j\to\infty} U_j / Q_j$。 -/
def alphaU (P : PolyRecData) : ℝ :=
  ∑' n : ℕ, ((P.fundU (P.J₀ + n + 1) : ℝ) / (P.Q (P.J₀ + n + 1) : ℝ) -
    (P.fundU (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ))

/-- 基本解极限 $\alpha_V := \lim_{j\to\infty} V_j / Q_j$。 -/
def alphaV (P : PolyRecData) : ℝ :=
  (1 : ℝ) / (P.Q P.J₀ : ℝ) +
    ∑' n : ℕ, ((P.fundV (P.J₀ + n + 1) : ℝ) / (P.Q (P.J₀ + n + 1) : ℝ) -
      (P.fundV (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ))

lemma summable_diffU (P : PolyRecData) :
    Summable (fun n : ℕ => (P.fundU (P.J₀ + n + 1) : ℝ) / (P.Q (P.J₀ + n + 1) : ℝ) -
      (P.fundU (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ)) := by
  have hsum : Summable (fun n : ℕ =>
      (P.Q P.J₀ : ℝ) / ((P.Q (P.J₀ + n) : ℝ) * (P.Q (P.J₀ + n + 1) : ℝ))) :=
    (P.poly_summable_inv_Q_mul_succ).mul_left (P.Q P.J₀ : ℝ) |>.congr (fun n => by ring)
  refine Summable.of_norm_bounded hsum (fun n => ?_)
  rw [P.poly_ratio_diff_U (by omega)]
  have hsub : P.J₀ + n - P.J₀ = n := by omega
  rw [hsub, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hQ0 : (0 : ℝ) < (P.Q P.J₀ : ℝ) := by exact_mod_cast P.hQ_pos P.J₀
  have hQa : (0 : ℝ) < (P.Q (P.J₀ + n) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ + n)
  have hQb : (0 : ℝ) < (P.Q (P.J₀ + n + 1) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ + n + 1)
  rw [abs_of_pos hQ0, abs_of_pos (mul_pos hQa hQb)]

lemma summable_diffV (P : PolyRecData) :
    Summable (fun n : ℕ => (P.fundV (P.J₀ + n + 1) : ℝ) / (P.Q (P.J₀ + n + 1) : ℝ) -
      (P.fundV (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ)) := by
  have hsum : Summable (fun n : ℕ =>
      (P.Q (P.J₀ - 1) : ℝ) / ((P.Q (P.J₀ + n) : ℝ) * (P.Q (P.J₀ + n + 1) : ℝ))) :=
    (P.poly_summable_inv_Q_mul_succ).mul_left (P.Q (P.J₀ - 1) : ℝ) |>.congr (fun n => by ring)
  refine Summable.of_norm_bounded hsum (fun n => ?_)
  rw [P.poly_ratio_diff_V (by omega)]
  have hsub : P.J₀ + n + 1 - P.J₀ = n + 1 := by omega
  rw [hsub, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hQ0 : (0 : ℝ) < (P.Q (P.J₀ - 1) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ - 1)
  have hQa : (0 : ℝ) < (P.Q (P.J₀ + n) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ + n)
  have hQb : (0 : ℝ) < (P.Q (P.J₀ + n + 1) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ + n + 1)
  rw [abs_of_pos hQ0, abs_of_pos (mul_pos hQa hQb)]

/-- **Lemma `lem:poly-lattice`(ii)**：$\alpha_U, \alpha_V$ 存在且满足交错误差界与归一化等式。 -/
theorem alphaU_error_bound (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    0 < (-1 : ℝ) ^ (j - P.J₀) * (P.alphaU - (P.fundU j : ℝ) / (P.Q j : ℝ)) ∧
    (-1 : ℝ) ^ (j - P.J₀) * (P.alphaU - (P.fundU j : ℝ) / (P.Q j : ℝ)) <
      (P.Q P.J₀ : ℝ) / ((P.Q j : ℝ) * (P.Q (j + 1) : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = P.J₀ + m := ⟨j - P.J₀, by omega⟩
  have hsplit := P.summable_diffU.sum_add_tsum_nat_add m
  have htel : ∑ n ∈ Finset.range m,
      ((P.fundU (P.J₀ + n + 1) : ℝ) / (P.Q (P.J₀ + n + 1) : ℝ) -
        (P.fundU (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ)) =
      (P.fundU (P.J₀ + m) : ℝ) / (P.Q (P.J₀ + m) : ℝ) := by
    have h := Finset.sum_range_sub (fun n => (P.fundU (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ)) m
    have h0 : (P.fundU (P.J₀ + 0) : ℝ) / (P.Q (P.J₀ + 0) : ℝ) = 0 := by
      simp [fundU_init1]
    have hcongr : ∑ n ∈ Finset.range m,
        ((P.fundU (P.J₀ + n + 1) : ℝ) / (P.Q (P.J₀ + n + 1) : ℝ) -
          (P.fundU (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ)) =
        ∑ n ∈ Finset.range m,
          ((P.fundU (P.J₀ + (n + 1)) : ℝ) / (P.Q (P.J₀ + (n + 1)) : ℝ) -
            (P.fundU (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ)) := by
      refine Finset.sum_congr rfl (fun n _ => by simp only [add_assoc])
    rw [hcongr, h, h0, sub_zero]
  have hrem : P.alphaU - (P.fundU (P.J₀ + m) : ℝ) / (P.Q (P.J₀ + m) : ℝ) =
      ∑' n : ℕ, ((P.fundU (P.J₀ + (n + m) + 1) : ℝ) / (P.Q (P.J₀ + (n + m) + 1) : ℝ) -
        (P.fundU (P.J₀ + (n + m)) : ℝ) / (P.Q (P.J₀ + (n + m)) : ℝ)) := by
    unfold alphaU
    linarith [hsplit, htel]
  have hsub_m : P.J₀ + m - P.J₀ = m := by omega
  rw [hsub_m, hrem, ← tsum_mul_left]
  let b : ℕ → ℝ := fun n =>
    (P.Q P.J₀ : ℝ) / ((P.Q (P.J₀ + m + n) : ℝ) * (P.Q (P.J₀ + m + n + 1) : ℝ))
  have hb_pos : ∀ n : ℕ, 0 < b n := fun n => by
    have hQ0 : (0 : ℝ) < (P.Q P.J₀ : ℝ) := by exact_mod_cast P.hQ_pos P.J₀
    have hQa : (0 : ℝ) < (P.Q (P.J₀ + m + n) : ℝ) := by exact_mod_cast P.hQ_pos _
    have hQb : (0 : ℝ) < (P.Q (P.J₀ + m + n + 1) : ℝ) := by exact_mod_cast P.hQ_pos _
    positivity
  have hb_dec : ∀ n : ℕ, b (n + 1) < b n := fun n => by
    dsimp [b]
    have hQ0 : (0 : ℝ) < (P.Q P.J₀ : ℝ) := by exact_mod_cast P.hQ_pos P.J₀
    have h1 : P.Q (P.J₀ + m + n) < P.Q (P.J₀ + m + n + 1) := P.poly_Q_lt_succ (by omega)
    have h2 : P.Q (P.J₀ + m + n + 1) < P.Q (P.J₀ + m + n + 1 + 1) := P.poly_Q_lt_succ (by omega)
    have hQa : (0 : ℝ) < (P.Q (P.J₀ + m + n) : ℝ) := by exact_mod_cast P.hQ_pos _
    have hQb : (0 : ℝ) < (P.Q (P.J₀ + m + n + 1) : ℝ) := by exact_mod_cast P.hQ_pos _
    have hQc : (0 : ℝ) < (P.Q (P.J₀ + m + (n + 1) + 1) : ℝ) := by exact_mod_cast P.hQ_pos _
    have h1R : (P.Q (P.J₀ + m + n) : ℝ) < (P.Q (P.J₀ + m + n + 1) : ℝ) := by exact_mod_cast h1
    have h2R : (P.Q (P.J₀ + m + n + 1) : ℝ) < (P.Q (P.J₀ + m + (n + 1) + 1) : ℝ) := by
      exact_mod_cast (by simpa [add_assoc] using h2)
    have hden : (P.Q (P.J₀ + m + n) : ℝ) * (P.Q (P.J₀ + m + n + 1) : ℝ) <
        (P.Q (P.J₀ + m + (n + 1)) : ℝ) * (P.Q (P.J₀ + m + (n + 1) + 1) : ℝ) := by
      have heq1 : P.J₀ + m + (n + 1) = P.J₀ + m + n + 1 := by omega
      rw [heq1]
      rw [heq1] at h2R
      nlinarith
    exact div_lt_div_of_pos_left hQ0 (mul_pos hQa hQb) hden
  have hb_sum : Summable b := by
    have h := (P.poly_summable_inv_Q_mul_succ).comp_injective (add_left_injective m)
    have h' := h.mul_left (P.Q P.J₀ : ℝ)
    refine h'.congr (fun n => ?_)
    dsimp [b]
    have hadd1 : P.J₀ + (n + m) = P.J₀ + m + n := by omega
    rw [hadd1]
    ring
  have heq_term : ∀ n : ℕ, (-1 : ℝ) ^ m *
      ((P.fundU (P.J₀ + (n + m) + 1) : ℝ) / (P.Q (P.J₀ + (n + m) + 1) : ℝ) -
        (P.fundU (P.J₀ + (n + m)) : ℝ) / (P.Q (P.J₀ + (n + m)) : ℝ)) = (-1 : ℝ) ^ n * b n := by
    intro n
    rw [P.poly_ratio_diff_U (by omega)]
    have hsub_nm : P.J₀ + (n + m) - P.J₀ = n + m := by omega
    have hadd_nm : P.J₀ + (n + m) = P.J₀ + m + n := by omega
    rw [hsub_nm, hadd_nm]
    dsimp [b]
    have hpow : (-1 : ℝ) ^ m * (-1 : ℝ) ^ (n + m) = (-1 : ℝ) ^ n := by
      rw [← pow_add, show m + (n + m) = n + 2 * m by ring, pow_add]
      have : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      rw [this, mul_one]
    calc (-1 : ℝ) ^ m *
          ((-1 : ℝ) ^ (n + m) * (P.Q P.J₀ : ℝ) /
            ((P.Q (P.J₀ + m + n) : ℝ) * (P.Q (P.J₀ + m + n + 1) : ℝ)))
        = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ (n + m)) *
            ((P.Q P.J₀ : ℝ) / ((P.Q (P.J₀ + m + n) : ℝ) * (P.Q (P.J₀ + m + n + 1) : ℝ))) := by
            ring
      _ = (-1 : ℝ) ^ n *
            ((P.Q P.J₀ : ℝ) / ((P.Q (P.J₀ + m + n) : ℝ) * (P.Q (P.J₀ + m + n + 1) : ℝ))) := by
            rw [hpow]
  have hcongr : ∑' n : ℕ, (-1 : ℝ) ^ m *
      ((P.fundU (P.J₀ + (n + m) + 1) : ℝ) / (P.Q (P.J₀ + (n + m) + 1) : ℝ) -
        (P.fundU (P.J₀ + (n + m)) : ℝ) / (P.Q (P.J₀ + (n + m)) : ℝ)) =
      ∑' n : ℕ, (-1 : ℝ) ^ n * b n := tsum_congr heq_term
  rw [hcongr]
  simpa [b] using alt_tsum_bounds hb_pos hb_dec hb_sum

theorem alphaV_error_bound (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    0 < (-1 : ℝ) ^ (j + 1 - P.J₀) * (P.alphaV - (P.fundV j : ℝ) / (P.Q j : ℝ)) ∧
    (-1 : ℝ) ^ (j + 1 - P.J₀) * (P.alphaV - (P.fundV j : ℝ) / (P.Q j : ℝ)) <
      (P.Q (P.J₀ - 1) : ℝ) / ((P.Q j : ℝ) * (P.Q (j + 1) : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = P.J₀ + m := ⟨j - P.J₀, by omega⟩
  have hsplit := P.summable_diffV.sum_add_tsum_nat_add m
  have htel : (1 : ℝ) / (P.Q P.J₀ : ℝ) + ∑ n ∈ Finset.range m,
      ((P.fundV (P.J₀ + n + 1) : ℝ) / (P.Q (P.J₀ + n + 1) : ℝ) -
        (P.fundV (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ)) =
      (P.fundV (P.J₀ + m) : ℝ) / (P.Q (P.J₀ + m) : ℝ) := by
    have h := Finset.sum_range_sub (fun n => (P.fundV (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ)) m
    have h0 : (P.fundV (P.J₀ + 0) : ℝ) / (P.Q (P.J₀ + 0) : ℝ) = (1 : ℝ) / (P.Q P.J₀ : ℝ) := by
      simp [fundV_init1]
    have hcongr : ∑ n ∈ Finset.range m,
        ((P.fundV (P.J₀ + n + 1) : ℝ) / (P.Q (P.J₀ + n + 1) : ℝ) -
          (P.fundV (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ)) =
        ∑ n ∈ Finset.range m,
          ((P.fundV (P.J₀ + (n + 1)) : ℝ) / (P.Q (P.J₀ + (n + 1)) : ℝ) -
            (P.fundV (P.J₀ + n) : ℝ) / (P.Q (P.J₀ + n) : ℝ)) := by
      refine Finset.sum_congr rfl (fun n _ => by simp only [add_assoc])
    rw [hcongr, h, h0]
    ring
  have hrem : P.alphaV - (P.fundV (P.J₀ + m) : ℝ) / (P.Q (P.J₀ + m) : ℝ) =
      ∑' n : ℕ, ((P.fundV (P.J₀ + (n + m) + 1) : ℝ) / (P.Q (P.J₀ + (n + m) + 1) : ℝ) -
        (P.fundV (P.J₀ + (n + m)) : ℝ) / (P.Q (P.J₀ + (n + m)) : ℝ)) := by
    unfold alphaV
    linarith [hsplit, htel]
  have hsub_m : P.J₀ + m + 1 - P.J₀ = m + 1 := by omega
  rw [hsub_m, hrem, ← tsum_mul_left]
  let b : ℕ → ℝ := fun n =>
    (P.Q (P.J₀ - 1) : ℝ) / ((P.Q (P.J₀ + m + n) : ℝ) * (P.Q (P.J₀ + m + n + 1) : ℝ))
  have hb_pos : ∀ n : ℕ, 0 < b n := fun n => by
    have hQ0 : (0 : ℝ) < (P.Q (P.J₀ - 1) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ - 1)
    have hQa : (0 : ℝ) < (P.Q (P.J₀ + m + n) : ℝ) := by exact_mod_cast P.hQ_pos _
    have hQb : (0 : ℝ) < (P.Q (P.J₀ + m + n + 1) : ℝ) := by exact_mod_cast P.hQ_pos _
    positivity
  have hb_dec : ∀ n : ℕ, b (n + 1) < b n := fun n => by
    dsimp [b]
    have hQ0 : (0 : ℝ) < (P.Q (P.J₀ - 1) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ - 1)
    have h1 : P.Q (P.J₀ + m + n) < P.Q (P.J₀ + m + n + 1) := P.poly_Q_lt_succ (by omega)
    have h2 : P.Q (P.J₀ + m + n + 1) < P.Q (P.J₀ + m + n + 1 + 1) := P.poly_Q_lt_succ (by omega)
    have hQa : (0 : ℝ) < (P.Q (P.J₀ + m + n) : ℝ) := by exact_mod_cast P.hQ_pos _
    have hQb : (0 : ℝ) < (P.Q (P.J₀ + m + n + 1) : ℝ) := by exact_mod_cast P.hQ_pos _
    have hden : (P.Q (P.J₀ + m + n) : ℝ) * (P.Q (P.J₀ + m + n + 1) : ℝ) <
        (P.Q (P.J₀ + m + (n + 1)) : ℝ) * (P.Q (P.J₀ + m + (n + 1) + 1) : ℝ) := by
      have heq : P.J₀ + m + (n + 1) = P.J₀ + m + n + 1 := by omega
      rw [heq]
      have h1R : (P.Q (P.J₀ + m + n) : ℝ) < (P.Q (P.J₀ + m + n + 1) : ℝ) := by exact_mod_cast h1
      have h2R : (P.Q (P.J₀ + m + n + 1) : ℝ) < (P.Q (P.J₀ + m + n + 1 + 1) : ℝ) := by
        exact_mod_cast h2
      nlinarith
    exact div_lt_div_of_pos_left hQ0 (mul_pos hQa hQb) hden
  have hb_sum : Summable b := by
    have h := (P.poly_summable_inv_Q_mul_succ).comp_injective (add_left_injective m)
    have h' := h.mul_left (P.Q (P.J₀ - 1) : ℝ)
    refine h'.congr (fun n => ?_)
    dsimp [b]
    have hadd1 : P.J₀ + (n + m) = P.J₀ + m + n := by omega
    rw [hadd1]
    ring
  have heq_term : ∀ n : ℕ, (-1 : ℝ) ^ (m + 1) *
      ((P.fundV (P.J₀ + (n + m) + 1) : ℝ) / (P.Q (P.J₀ + (n + m) + 1) : ℝ) -
        (P.fundV (P.J₀ + (n + m)) : ℝ) / (P.Q (P.J₀ + (n + m)) : ℝ)) = (-1 : ℝ) ^ n * b n := by
    intro n
    rw [P.poly_ratio_diff_V (by omega)]
    have hsub_nm : P.J₀ + (n + m) + 1 - P.J₀ = n + m + 1 := by omega
    have hadd_nm : P.J₀ + (n + m) = P.J₀ + m + n := by omega
    rw [hsub_nm, hadd_nm]
    dsimp [b]
    have hpow : (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (n + m + 1) = (-1 : ℝ) ^ n := by
      rw [← pow_add, show m + 1 + (n + m + 1) = n + 2 * (m + 1) by ring, pow_add]
      have : (-1 : ℝ) ^ (2 * (m + 1)) = 1 := by rw [pow_mul]; norm_num
      rw [this, mul_one]
    calc (-1 : ℝ) ^ (m + 1) *
          ((-1 : ℝ) ^ (n + m + 1) * (P.Q (P.J₀ - 1) : ℝ) /
            ((P.Q (P.J₀ + m + n) : ℝ) * (P.Q (P.J₀ + m + n + 1) : ℝ)))
        = ((-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (n + m + 1)) *
            ((P.Q (P.J₀ - 1) : ℝ) / ((P.Q (P.J₀ + m + n) : ℝ) * (P.Q (P.J₀ + m + n + 1) : ℝ))) := by
            ring
      _ = (-1 : ℝ) ^ n *
            ((P.Q (P.J₀ - 1) : ℝ) / ((P.Q (P.J₀ + m + n) : ℝ) * (P.Q (P.J₀ + m + n + 1) : ℝ))) := by
            rw [hpow]
  have hcongr : ∑' n : ℕ, (-1 : ℝ) ^ (m + 1) *
      ((P.fundV (P.J₀ + (n + m) + 1) : ℝ) / (P.Q (P.J₀ + (n + m) + 1) : ℝ) -
        (P.fundV (P.J₀ + (n + m)) : ℝ) / (P.Q (P.J₀ + (n + m)) : ℝ)) =
      ∑' n : ℕ, (-1 : ℝ) ^ n * b n := tsum_congr heq_term
  rw [hcongr]
  simpa [b] using alt_tsum_bounds hb_pos hb_dec hb_sum

lemma abs_alphaU_sub_lt (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    0 < |P.alphaU - (P.fundU j : ℝ) / (P.Q j : ℝ)| ∧
    |P.alphaU - (P.fundU j : ℝ) / (P.Q j : ℝ)| <
      (P.Q P.J₀ : ℝ) / ((P.Q j : ℝ) * (P.Q (j + 1) : ℝ)) := by
  have h := P.alphaU_error_bound hj
  have habs : |(-1 : ℝ) ^ (j - P.J₀) * (P.alphaU - (P.fundU j : ℝ) / (P.Q j : ℝ))| =
      |P.alphaU - (P.fundU j : ℝ) / (P.Q j : ℝ)| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [← habs, abs_of_pos h.1]
  exact h

lemma abs_alphaV_sub_lt (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    0 < |P.alphaV - (P.fundV j : ℝ) / (P.Q j : ℝ)| ∧
    |P.alphaV - (P.fundV j : ℝ) / (P.Q j : ℝ)| <
      (P.Q (P.J₀ - 1) : ℝ) / ((P.Q j : ℝ) * (P.Q (j + 1) : ℝ)) := by
  have h := P.alphaV_error_bound hj
  have habs : |(-1 : ℝ) ^ (j + 1 - P.J₀) * (P.alphaV - (P.fundV j : ℝ) / (P.Q j : ℝ))| =
      |P.alphaV - (P.fundV j : ℝ) / (P.Q j : ℝ)| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [← habs, abs_of_pos h.1]
  exact h

lemma tendsto_fundU_div_Q (P : PolyRecData) :
    Tendsto (fun j : ℕ => (P.fundU j : ℝ) / (P.Q j : ℝ)) atTop (nhds P.alphaU) := by
  have hzero : Tendsto (fun j : ℕ => (P.Q P.J₀ : ℝ) / ((P.Q j : ℝ) * (P.Q (j + 1) : ℝ)))
      atTop (nhds 0) := by
    have hmul : Tendsto (fun j : ℕ => (P.Q j : ℝ) * (P.Q (j + 1) : ℝ)) atTop atTop := by
      refine tendsto_atTop_mono (fun j => ?_) P.poly_Q_tendsto_atTop
      have h1 : (1 : ℝ) ≤ (P.Q (j + 1) : ℝ) := by exact_mod_cast P.hQ_pos (j + 1)
      have h0 : (0 : ℝ) ≤ (P.Q j : ℝ) := by exact_mod_cast (P.hQ_pos j).le
      exact le_mul_of_one_le_right h0 h1
    exact hmul.const_div_atTop (P.Q P.J₀ : ℝ)
  have hdist : Tendsto (fun j : ℕ => |((P.fundU j : ℝ) / (P.Q j : ℝ)) - P.alphaU|)
      atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_
    filter_upwards [eventually_ge_atTop P.J₀] with j hj
    rw [abs_sub_comm]
    exact le_of_lt (P.abs_alphaU_sub_lt hj).2
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hdist)

lemma tendsto_fundV_div_Q (P : PolyRecData) :
    Tendsto (fun j : ℕ => (P.fundV j : ℝ) / (P.Q j : ℝ)) atTop (nhds P.alphaV) := by
  have hzero : Tendsto (fun j : ℕ => (P.Q (P.J₀ - 1) : ℝ) / ((P.Q j : ℝ) * (P.Q (j + 1) : ℝ)))
      atTop (nhds 0) := by
    have hmul : Tendsto (fun j : ℕ => (P.Q j : ℝ) * (P.Q (j + 1) : ℝ)) atTop atTop := by
      refine tendsto_atTop_mono (fun j => ?_) P.poly_Q_tendsto_atTop
      have h1 : (1 : ℝ) ≤ (P.Q (j + 1) : ℝ) := by exact_mod_cast P.hQ_pos (j + 1)
      have h0 : (0 : ℝ) ≤ (P.Q j : ℝ) := by exact_mod_cast (P.hQ_pos j).le
      exact le_mul_of_one_le_right h0 h1
    exact hmul.const_div_atTop (P.Q (P.J₀ - 1) : ℝ)
  have hdist : Tendsto (fun j : ℕ => |((P.fundV j : ℝ) / (P.Q j : ℝ)) - P.alphaV|)
      atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_
    filter_upwards [eventually_ge_atTop P.J₀] with j hj
    rw [abs_sub_comm]
    exact le_of_lt (P.abs_alphaV_sub_lt hj).2
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hdist)

theorem poly_alpha_linear_relation (P : PolyRecData) :
    (P.Q (P.J₀ - 1) : ℝ) * P.alphaU + (P.Q P.J₀ : ℝ) * P.alphaV = 1 := by
  have hlim : Tendsto (fun j : ℕ =>
      (P.Q (P.J₀ - 1) : ℝ) * ((P.fundU j : ℝ) / (P.Q j : ℝ)) +
        (P.Q P.J₀ : ℝ) * ((P.fundV j : ℝ) / (P.Q j : ℝ)))
      atTop (nhds ((P.Q (P.J₀ - 1) : ℝ) * P.alphaU + (P.Q P.J₀ : ℝ) * P.alphaV)) :=
    (P.tendsto_fundU_div_Q.const_mul _).add (P.tendsto_fundV_div_Q.const_mul _)
  have hconst : ∀ᶠ j : ℕ in atTop,
      (P.Q (P.J₀ - 1) : ℝ) * ((P.fundU j : ℝ) / (P.Q j : ℝ)) +
        (P.Q P.J₀ : ℝ) * ((P.fundV j : ℝ) / (P.Q j : ℝ)) = 1 := by
    filter_upwards [eventually_ge_atTop P.J₀] with j hj
    have hQ : (P.Q j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.hQ_pos j)
    have hlin : (P.Q j : ℝ) =
        (P.Q (P.J₀ - 1) : ℝ) * (P.fundU j : ℝ) + (P.Q P.J₀ : ℝ) * (P.fundV j : ℝ) := by
      exact_mod_cast P.poly_Q_eq_lincomb (by omega)
    field_simp
    linarith [hlin]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconst.mono fun _ h => h.symm))

/-- **Lemma `lem:poly-lattice`(iii)**：初值最大公因子 $g = \gcd(Q_{J_0-1}, Q_{J_0})$、互素基 $(q_0, q_1)$、
    Bezout 对偶 $(p_0, p_1)$、无理极限 $\theta = g(p_0\alpha_U + p_1\alpha_V) \notin \mathbb{Q}$ 与内蕴晶格。 -/
def gFactor (P : PolyRecData) : ℕ := Int.gcd (P.Q (P.J₀ - 1)) (P.Q P.J₀)

lemma gFactor_pos (P : PolyRecData) : 0 < P.gFactor := by
  unfold gFactor
  exact Int.gcd_pos_iff.mpr (Or.inl (ne_of_gt (P.hQ_pos (P.J₀ - 1))))

def q₀ (P : PolyRecData) : ℤ := P.Q (P.J₀ - 1) / (P.gFactor : ℤ)
def q₁ (P : PolyRecData) : ℤ := P.Q P.J₀ / (P.gFactor : ℤ)

lemma q₀_mul_g (P : PolyRecData) : (P.gFactor : ℤ) * P.q₀ = P.Q (P.J₀ - 1) := by
  unfold q₀ gFactor
  exact Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)

lemma q₁_mul_g (P : PolyRecData) : (P.gFactor : ℤ) * P.q₁ = P.Q P.J₀ := by
  unfold q₁ gFactor
  exact Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)

lemma q₀_q₁_coprime (P : PolyRecData) : IsCoprime P.q₀ P.q₁ := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hpos : (0 : ℕ) < P.gFactor := P.gFactor_pos
  have hdiv : Int.gcd (P.Q (P.J₀ - 1)) (P.Q P.J₀) = P.gFactor := rfl
  have h1 : Int.gcd ((P.gFactor : ℤ) * P.q₀) ((P.gFactor : ℤ) * P.q₁) =
      P.gFactor * Int.gcd P.q₀ P.q₁ := by
    rw [Int.gcd_mul_left, Int.natAbs_natCast]
  rw [P.q₀_mul_g, P.q₁_mul_g, hdiv] at h1
  nlinarith

def p₀ (P : PolyRecData) : ℤ := Int.gcdB P.q₀ P.q₁
def p₁ (P : PolyRecData) : ℤ := -Int.gcdA P.q₀ P.q₁

lemma p₀q₁_sub_p₁q₀ (P : PolyRecData) : P.p₀ * P.q₁ - P.p₁ * P.q₀ = 1 := by
  have hg : (Int.gcd P.q₀ P.q₁ : ℤ) = P.q₀ * Int.gcdA P.q₀ P.q₁ + P.q₁ * Int.gcdB P.q₀ P.q₁ :=
    Int.gcd_eq_gcd_ab P.q₀ P.q₁
  have hcop : Int.gcd P.q₀ P.q₁ = 1 := Int.isCoprime_iff_gcd_eq_one.mp P.q₀_q₁_coprime
  have hg' : (1 : ℤ) = P.q₀ * Int.gcdA P.q₀ P.q₁ + P.q₁ * Int.gcdB P.q₀ P.q₁ := by
    simpa [hcop] using hg
  unfold p₀ p₁
  linarith

def Qtilde (P : PolyRecData) (j : ℕ) : ℤ := P.q₀ * P.fundU j + P.q₁ * P.fundV j
def Ptilde (P : PolyRecData) (j : ℕ) : ℤ := P.p₀ * P.fundU j + P.p₁ * P.fundV j

lemma g_mul_Qtilde (P : PolyRecData) {j : ℕ} (hj : P.J₀ - 1 ≤ j) :
    (P.gFactor : ℤ) * P.Qtilde j = P.Q j := by
  have hlin := P.poly_Q_eq_lincomb hj
  rw [← P.q₀_mul_g, ← P.q₁_mul_g] at hlin
  unfold Qtilde
  linarith

lemma Qtilde_pos (P : PolyRecData) {j : ℕ} (hj : P.J₀ - 1 ≤ j) : 0 < P.Qtilde j := by
  have hg : (0 : ℤ) < (P.gFactor : ℤ) := by exact_mod_cast P.gFactor_pos
  have hQ := P.hQ_pos j
  rw [← P.g_mul_Qtilde hj] at hQ
  nlinarith

lemma Qtilde_lt_succ (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    P.Qtilde j < P.Qtilde (j + 1) := by
  have hg : (0 : ℤ) < (P.gFactor : ℤ) := by exact_mod_cast P.gFactor_pos
  have hlt := P.poly_Q_lt_succ hj
  rw [← P.g_mul_Qtilde (by omega), ← P.g_mul_Qtilde (by omega)] at hlt
  nlinarith

lemma Ptilde_Qtilde_det (P : PolyRecData) {j : ℕ} (hj : P.J₀ - 1 ≤ j) :
    P.Ptilde j * P.Qtilde (j + 1) - P.Ptilde (j + 1) * P.Qtilde j =
      (-1 : ℤ) ^ (j + 1 - P.J₀) := by
  have hcas := P.poly_casorati hj
  have hbez := P.p₀q₁_sub_p₁q₀
  have halg : P.Ptilde j * P.Qtilde (j + 1) - P.Ptilde (j + 1) * P.Qtilde j =
      (P.p₀ * P.q₁ - P.p₁ * P.q₀) *
        (P.fundU j * P.fundV (j + 1) - P.fundU (j + 1) * P.fundV j) := by
    unfold Ptilde Qtilde; ring
  rw [halg, hbez, one_mul, hcas]

/-- 内蕴无理斜率 $\theta := g (p_0 \alpha_U + p_1 \alpha_V)$。 -/
def theta (P : PolyRecData) : ℝ :=
  (P.gFactor : ℝ) * ((P.p₀ : ℝ) * P.alphaU + (P.p₁ : ℝ) * P.alphaV)

lemma theta_eq_ratio_limit (P : PolyRecData) :
    Tendsto (fun j : ℕ => (P.Ptilde j : ℝ) / (P.Qtilde j : ℝ)) atTop (nhds P.theta) := by
  have hlim : Tendsto (fun j : ℕ =>
      (P.gFactor : ℝ) * ((P.p₀ : ℝ) * ((P.fundU j : ℝ) / (P.Q j : ℝ)) +
        (P.p₁ : ℝ) * ((P.fundV j : ℝ) / (P.Q j : ℝ)))) atTop (nhds P.theta) := by
    unfold theta
    exact ((P.tendsto_fundU_div_Q.const_mul _).add (P.tendsto_fundV_div_Q.const_mul _)).const_mul _
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop P.J₀] with j hj
  have hgQ : (P.gFactor : ℝ) * (P.Qtilde j : ℝ) = (P.Q j : ℝ) := by
    exact_mod_cast P.g_mul_Qtilde (by omega)
  have hgne : (P.gFactor : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt P.gFactor_pos
  have hQne : (P.Q j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.hQ_pos j)
  have hQtne : (P.Qtilde j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.Qtilde_pos (by omega))
  unfold Ptilde
  push_cast
  rw [← hgQ]
  field_simp

lemma theta_sub_ratio_pos_and_lt (P : PolyRecData) {j : ℕ} (hj : P.J₀ ≤ j) :
    0 < |P.theta - (P.Ptilde j : ℝ) / (P.Qtilde j : ℝ)| ∧
    |P.theta - (P.Ptilde j : ℝ) / (P.Qtilde j : ℝ)| <
      1 / ((P.Qtilde j : ℝ) * (P.Qtilde (j + 1) : ℝ)) := by
  -- 用 `Q_j = g Qtilde_j` 与 `theta = g(p₀ α_U + p₁ α_V)` 的非对称或交错差分数列
  -- 直接构造交错差分 `Ptilde (J₀ + n + 1)/Qtilde (J₀ + n + 1) - Ptilde (J₀ + n)/Qtilde (J₀ + n)`
  have hdiff : ∀ m : ℕ, P.J₀ ≤ m →
      (P.Ptilde (m + 1) : ℝ) / (P.Qtilde (m + 1) : ℝ) - (P.Ptilde m : ℝ) / (P.Qtilde m : ℝ) =
        (-1 : ℝ) ^ (m - P.J₀) / ((P.Qtilde m : ℝ) * (P.Qtilde (m + 1) : ℝ)) := by
    intro m hm
    have h1 : (P.Qtilde m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.Qtilde_pos (by omega))
    have h2 : (P.Qtilde (m + 1) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.Qtilde_pos (by omega))
    have hdet : (P.Ptilde m : ℝ) * (P.Qtilde (m + 1) : ℝ) -
        (P.Ptilde (m + 1) : ℝ) * (P.Qtilde m : ℝ) = (-1 : ℝ) ^ (m + 1 - P.J₀) := by
      exact_mod_cast P.Ptilde_Qtilde_det (by omega)
    have hexp : m + 1 - P.J₀ = (m - P.J₀) + 1 := by omega
    rw [hexp, pow_succ] at hdet
    field_simp
    linarith [hdet]
  have hsum_inv : Summable (fun n : ℕ =>
      1 / ((P.Qtilde (P.J₀ + n) : ℝ) * (P.Qtilde (P.J₀ + n + 1) : ℝ))) := by
    have hbase := P.poly_summable_inv_Q_mul_succ
    have hg : (0 : ℝ) < (P.gFactor : ℝ) := by exact_mod_cast P.gFactor_pos
    refine (hbase.mul_left ((P.gFactor : ℝ) ^ 2)).congr (fun n => ?_)
    have h1 : (P.gFactor : ℝ) * (P.Qtilde (P.J₀ + n) : ℝ) = (P.Q (P.J₀ + n) : ℝ) := by
      exact_mod_cast P.g_mul_Qtilde (by omega)
    have h2 : (P.gFactor : ℝ) * (P.Qtilde (P.J₀ + n + 1) : ℝ) = (P.Q (P.J₀ + n + 1) : ℝ) := by
      exact_mod_cast P.g_mul_Qtilde (by omega)
    rw [← h1, ← h2]
    field_simp
  have hsum_PQ : Summable (fun n : ℕ =>
      (P.Ptilde (P.J₀ + n + 1) : ℝ) / (P.Qtilde (P.J₀ + n + 1) : ℝ) -
        (P.Ptilde (P.J₀ + n) : ℝ) / (P.Qtilde (P.J₀ + n) : ℝ)) := by
    refine Summable.of_norm_bounded hsum_inv (fun n => ?_)
    rw [hdiff (P.J₀ + n) (by omega)]
    have hsub : P.J₀ + n - P.J₀ = n := by omega
    rw [hsub, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow]
    have ha : (0 : ℝ) < (P.Qtilde (P.J₀ + n) : ℝ) := by exact_mod_cast P.Qtilde_pos (by omega)
    have hb : (0 : ℝ) < (P.Qtilde (P.J₀ + n + 1) : ℝ) := by exact_mod_cast P.Qtilde_pos (by omega)
    rw [abs_of_pos (mul_pos ha hb)]
  have hlim_sum : P.theta - (P.Ptilde P.J₀ : ℝ) / (P.Qtilde P.J₀ : ℝ) =
      ∑' n : ℕ, ((P.Ptilde (P.J₀ + n + 1) : ℝ) / (P.Qtilde (P.J₀ + n + 1) : ℝ) -
        (P.Ptilde (P.J₀ + n) : ℝ) / (P.Qtilde (P.J₀ + n) : ℝ)) := by
    have hpart := hsum_PQ.hasSum.tendsto_sum_nat
    have htel : ∀ N : ℕ, ∑ n ∈ Finset.range N,
        ((P.Ptilde (P.J₀ + n + 1) : ℝ) / (P.Qtilde (P.J₀ + n + 1) : ℝ) -
          (P.Ptilde (P.J₀ + n) : ℝ) / (P.Qtilde (P.J₀ + n) : ℝ)) =
        (P.Ptilde (P.J₀ + N) : ℝ) / (P.Qtilde (P.J₀ + N) : ℝ) -
          (P.Ptilde P.J₀ : ℝ) / (P.Qtilde P.J₀ : ℝ) := by
      intro N
      simpa [add_assoc] using
        Finset.sum_range_sub (fun n => (P.Ptilde (P.J₀ + n) : ℝ) / (P.Qtilde (P.J₀ + n) : ℝ)) N
    have hlim_ratio : Tendsto (fun N : ℕ => (P.Ptilde (P.J₀ + N) : ℝ) / (P.Qtilde (P.J₀ + N) : ℝ) -
        (P.Ptilde P.J₀ : ℝ) / (P.Qtilde P.J₀ : ℝ))
        atTop (nhds (P.theta - (P.Ptilde P.J₀ : ℝ) / (P.Qtilde P.J₀ : ℝ))) := by
      have hshift : Tendsto (fun N : ℕ => (P.Ptilde (P.J₀ + N) : ℝ) / (P.Qtilde (P.J₀ + N) : ℝ))
          atTop (nhds P.theta) :=
        P.theta_eq_ratio_limit.comp ((tendsto_add_atTop_nat P.J₀).congr (fun n => Nat.add_comm n P.J₀))
      exact hshift.sub_const _
    have hlim_part : Tendsto (fun N : ℕ =>
        (P.Ptilde (P.J₀ + N) : ℝ) / (P.Qtilde (P.J₀ + N) : ℝ) -
          (P.Ptilde P.J₀ : ℝ) / (P.Qtilde P.J₀ : ℝ))
        atTop (nhds (∑' n : ℕ, ((P.Ptilde (P.J₀ + n + 1) : ℝ) / (P.Qtilde (P.J₀ + n + 1) : ℝ) -
          (P.Ptilde (P.J₀ + n) : ℝ) / (P.Qtilde (P.J₀ + n) : ℝ)))) :=
      hpart.congr htel
    exact tendsto_nhds_unique hlim_ratio hlim_part
  obtain ⟨m, rfl⟩ : ∃ m, j = P.J₀ + m := ⟨j - P.J₀, by omega⟩
  have hsplit := hsum_PQ.sum_add_tsum_nat_add m
  have htel_m : ∑ n ∈ Finset.range m,
      ((P.Ptilde (P.J₀ + n + 1) : ℝ) / (P.Qtilde (P.J₀ + n + 1) : ℝ) -
        (P.Ptilde (P.J₀ + n) : ℝ) / (P.Qtilde (P.J₀ + n) : ℝ)) =
      (P.Ptilde (P.J₀ + m) : ℝ) / (P.Qtilde (P.J₀ + m) : ℝ) -
        (P.Ptilde P.J₀ : ℝ) / (P.Qtilde P.J₀ : ℝ) := by
    simpa [add_assoc] using
      Finset.sum_range_sub (fun n => (P.Ptilde (P.J₀ + n) : ℝ) / (P.Qtilde (P.J₀ + n) : ℝ)) m
  have hrem : P.theta - (P.Ptilde (P.J₀ + m) : ℝ) / (P.Qtilde (P.J₀ + m) : ℝ) =
      ∑' n : ℕ, ((P.Ptilde (P.J₀ + (n + m) + 1) : ℝ) / (P.Qtilde (P.J₀ + (n + m) + 1) : ℝ) -
        (P.Ptilde (P.J₀ + (n + m)) : ℝ) / (P.Qtilde (P.J₀ + (n + m)) : ℝ)) := by
    linarith [hlim_sum, hsplit, htel_m]
  let b : ℕ → ℝ := fun n =>
    1 / ((P.Qtilde (P.J₀ + m + n) : ℝ) * (P.Qtilde (P.J₀ + m + n + 1) : ℝ))
  have hb_pos : ∀ n : ℕ, 0 < b n := fun n => by
    have ha : (0 : ℝ) < (P.Qtilde (P.J₀ + m + n) : ℝ) := by exact_mod_cast P.Qtilde_pos (by omega)
    have hb : (0 : ℝ) < (P.Qtilde (P.J₀ + m + n + 1) : ℝ) := by exact_mod_cast P.Qtilde_pos (by omega)
    positivity
  have hb_dec : ∀ n : ℕ, b (n + 1) < b n := fun n => by
    dsimp [b]
    have ha : (0 : ℝ) < (P.Qtilde (P.J₀ + m + n) : ℝ) := by exact_mod_cast P.Qtilde_pos (by omega)
    have hb : (0 : ℝ) < (P.Qtilde (P.J₀ + m + n + 1) : ℝ) := by exact_mod_cast P.Qtilde_pos (by omega)
    have h1 : (P.Qtilde (P.J₀ + m + n) : ℝ) < (P.Qtilde (P.J₀ + m + n + 1) : ℝ) := by
      exact_mod_cast P.Qtilde_lt_succ (by omega)
    have h2 : (P.Qtilde (P.J₀ + m + n + 1) : ℝ) < (P.Qtilde (P.J₀ + m + n + 1 + 1) : ℝ) := by
      exact_mod_cast P.Qtilde_lt_succ (by omega)
    have heq : P.J₀ + m + (n + 1) = P.J₀ + m + n + 1 := by omega
    rw [heq]
    have hden : (P.Qtilde (P.J₀ + m + n) : ℝ) * (P.Qtilde (P.J₀ + m + n + 1) : ℝ) <
        (P.Qtilde (P.J₀ + m + n + 1) : ℝ) * (P.Qtilde (P.J₀ + m + n + 1 + 1) : ℝ) := by nlinarith
    exact div_lt_div_of_pos_left zero_lt_one (mul_pos ha hb) hden
  have hb_sum : Summable b := by
    have h := hsum_inv.comp_injective (add_left_injective m)
    refine h.congr (fun n => ?_)
    dsimp [b]
    have hadd1 : P.J₀ + (n + m) = P.J₀ + m + n := by omega
    rw [hadd1]
  have halt := alt_tsum_bounds hb_pos hb_dec hb_sum
  have hcongr : (-1 : ℝ) ^ m * (P.theta - (P.Ptilde (P.J₀ + m) : ℝ) / (P.Qtilde (P.J₀ + m) : ℝ)) =
      ∑' n : ℕ, (-1 : ℝ) ^ n * b n := by
    rw [hrem, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [hdiff (P.J₀ + (n + m)) (by omega)]
    have hsub : P.J₀ + (n + m) - P.J₀ = n + m := by omega
    have hadd : P.J₀ + (n + m) = P.J₀ + m + n := by omega
    rw [hsub, hadd]
    dsimp [b]
    have hpow : (-1 : ℝ) ^ m * (-1 : ℝ) ^ (n + m) = (-1 : ℝ) ^ n := by
      rw [← pow_add, show m + (n + m) = n + 2 * m by ring, pow_add]
      have : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      rw [this, mul_one]
    calc (-1 : ℝ) ^ m *
          ((-1 : ℝ) ^ (n + m) / ((P.Qtilde (P.J₀ + m + n) : ℝ) * (P.Qtilde (P.J₀ + m + n + 1) : ℝ)))
        = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ (n + m)) *
            (1 / ((P.Qtilde (P.J₀ + m + n) : ℝ) * (P.Qtilde (P.J₀ + m + n + 1) : ℝ))) := by ring
      _ = (-1 : ℝ) ^ n *
            (1 / ((P.Qtilde (P.J₀ + m + n) : ℝ) * (P.Qtilde (P.J₀ + m + n + 1) : ℝ))) := by rw [hpow]
  have habs_eq : |P.theta - (P.Ptilde (P.J₀ + m) : ℝ) / (P.Qtilde (P.J₀ + m) : ℝ)| =
      ∑' n : ℕ, (-1 : ℝ) ^ n * b n := by
    have h1 : |(-1 : ℝ) ^ m * (P.theta - (P.Ptilde (P.J₀ + m) : ℝ) / (P.Qtilde (P.J₀ + m) : ℝ))| =
        |P.theta - (P.Ptilde (P.J₀ + m) : ℝ) / (P.Qtilde (P.J₀ + m) : ℝ)| := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [← h1, hcongr, abs_of_pos halt.1]
  rw [habs_eq]
  simpa [b] using halt

/-- $\theta \notin \mathbb{Q}$（无理性）。 -/
theorem theta_irrational (P : PolyRecData) : Irrational P.theta := by
  rw [irrational_iff_ne_rational]
  intro p q hq htheta
  have hQ_tend : Tendsto (fun j : ℕ => (P.Qtilde j : ℝ)) atTop atTop := by
    have hg : (0 : ℝ) < (P.gFactor : ℝ) := by exact_mod_cast P.gFactor_pos
    have h1 := P.poly_Q_tendsto_atTop.const_mul_atTop (inv_pos.mpr hg)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop P.J₀] with j hj
    have hgQ : (P.gFactor : ℝ) * (P.Qtilde j : ℝ) = (P.Q j : ℝ) := by
      exact_mod_cast P.g_mul_Qtilde (by omega)
    rw [← hgQ]
    field_simp
  have hqR_pos : (0 : ℝ) < |(q : ℝ)| := abs_pos.mpr (by exact_mod_cast hq)
  have hev_Q : ∀ᶠ j : ℕ in atTop, |(q : ℝ)| < (P.Qtilde (j + 1) : ℝ) :=
    (hQ_tend.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop |(q : ℝ)|
  obtain ⟨j, hj1, hj2⟩ := (hev_Q.and (eventually_ge_atTop P.J₀)).exists
  have hb := P.theta_sub_ratio_pos_and_lt hj2
  have hQt_pos : (0 : ℝ) < (P.Qtilde j : ℝ) := by exact_mod_cast P.Qtilde_pos (by omega)
  have hQt1_pos : (0 : ℝ) < (P.Qtilde (j + 1) : ℝ) := by exact_mod_cast P.Qtilde_pos (by omega)
  have hmul_pos : (0 : ℝ) < |(q : ℝ)| * (P.Qtilde j : ℝ) := mul_pos hqR_pos hQt_pos
  have hdiff_eq : |(q : ℝ) * (P.Ptilde j : ℝ) - (p : ℝ) * (P.Qtilde j : ℝ)| =
      |(q : ℝ)| * (P.Qtilde j : ℝ) * |P.theta - (P.Ptilde j : ℝ) / (P.Qtilde j : ℝ)| := by
    rw [htheta]
    have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    have hQtne : (P.Qtilde j : ℝ) ≠ 0 := ne_of_gt hQt_pos
    have hid : (q : ℝ) * (P.Ptilde j : ℝ) - (p : ℝ) * (P.Qtilde j : ℝ) =
        -(q : ℝ) * (P.Qtilde j : ℝ) * ((p : ℝ) / (q : ℝ) - (P.Ptilde j : ℝ) / (P.Qtilde j : ℝ)) := by
      field_simp; ring
    rw [hid, abs_mul, abs_mul, abs_neg, abs_of_pos hQt_pos]
  have hposZ : 0 < |q * P.Ptilde j - p * P.Qtilde j| := by
    have h0 : 0 < |(q : ℝ) * (P.Ptilde j : ℝ) - (p : ℝ) * (P.Qtilde j : ℝ)| := by
      rw [hdiff_eq]
      exact mul_pos hmul_pos hb.1
    exact_mod_cast h0
  have hlt1 : |q * P.Ptilde j - p * P.Qtilde j| < 1 := by
    have h1 : |(q : ℝ) * (P.Ptilde j : ℝ) - (p : ℝ) * (P.Qtilde j : ℝ)| < 1 := by
      rw [hdiff_eq]
      calc |(q : ℝ)| * (P.Qtilde j : ℝ) * |P.theta - (P.Ptilde j : ℝ) / (P.Qtilde j : ℝ)|
          < (|(q : ℝ)| * (P.Qtilde j : ℝ)) *
              (1 / ((P.Qtilde j : ℝ) * (P.Qtilde (j + 1) : ℝ))) :=
            mul_lt_mul_of_pos_left hb.2 hmul_pos
        _ = |(q : ℝ)| / (P.Qtilde (j + 1) : ℝ) := by field_simp
        _ < 1 := (div_lt_one hQt1_pos).mpr hj1
    exact_mod_cast h1
  omega

/-- 一般多项式递推的内蕴零能级晶格 $L^{(r,c,d)} := \mathbb{Z}\alpha_U + \mathbb{Z}\alpha_V$。 -/
def latticePoly (P : PolyRecData) : Set ℝ :=
  {x : ℝ | ∃ a b : ℤ, x = (a : ℝ) * P.alphaU + (b : ℝ) * P.alphaV}

lemma latticePoly_eq_inv_g_lattice (P : PolyRecData) :
    P.latticePoly = {x : ℝ | ∃ m n : ℤ, x = ((m : ℝ) + (n : ℝ) * P.theta) / (P.gFactor : ℝ)} := by
  ext x
  have hgne : (P.gFactor : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt P.gFactor_pos
  have hq_rel : (P.q₀ : ℝ) * P.alphaU + (P.q₁ : ℝ) * P.alphaV = 1 / (P.gFactor : ℝ) := by
    have h1 := P.poly_alpha_linear_relation
    have hq0 : (P.Q (P.J₀ - 1) : ℝ) = (P.gFactor : ℝ) * (P.q₀ : ℝ) := by
      exact_mod_cast P.q₀_mul_g.symm
    have hq1 : (P.Q P.J₀ : ℝ) = (P.gFactor : ℝ) * (P.q₁ : ℝ) := by
      exact_mod_cast P.q₁_mul_g.symm
    rw [hq0, hq1] at h1
    field_simp
    linarith [h1]
  have hp_rel : (P.p₀ : ℝ) * P.alphaU + (P.p₁ : ℝ) * P.alphaV = P.theta / (P.gFactor : ℝ) := by
    unfold theta
    field_simp
  have hbez : (P.p₀ : ℝ) * (P.q₁ : ℝ) - (P.p₁ : ℝ) * (P.q₀ : ℝ) = 1 := by
    exact_mod_cast P.p₀q₁_sub_p₁q₀
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨b * P.p₀ - a * P.p₁, a * P.q₁ - b * P.q₀, ?_⟩
    push_cast
    calc (a : ℝ) * P.alphaU + (b : ℝ) * P.alphaV
        = ((b : ℝ) * (P.p₀ : ℝ) - (a : ℝ) * (P.p₁ : ℝ)) *
            ((P.q₀ : ℝ) * P.alphaU + (P.q₁ : ℝ) * P.alphaV) +
          ((a : ℝ) * (P.q₁ : ℝ) - (b : ℝ) * (P.q₀ : ℝ)) *
            ((P.p₀ : ℝ) * P.alphaU + (P.p₁ : ℝ) * P.alphaV) := by
            -- 利用 p₀ q₁ - p₁ q₀ = 1
            have hA : ((b : ℝ) * (P.p₀ : ℝ) - (a : ℝ) * (P.p₁ : ℝ)) * (P.q₀ : ℝ) +
                ((a : ℝ) * (P.q₁ : ℝ) - (b : ℝ) * (P.q₀ : ℝ)) * (P.p₀ : ℝ) = (a : ℝ) := by
              linear_combination (a : ℝ) * hbez
            have hB : ((b : ℝ) * (P.p₀ : ℝ) - (a : ℝ) * (P.p₁ : ℝ)) * (P.q₁ : ℝ) +
                ((a : ℝ) * (P.q₁ : ℝ) - (b : ℝ) * (P.q₀ : ℝ)) * (P.p₁ : ℝ) = (b : ℝ) := by
              linear_combination (b : ℝ) * hbez
            linear_combination P.alphaU * hA.symm + P.alphaV * hB.symm
      _ = (((b : ℝ) * (P.p₀ : ℝ) - (a : ℝ) * (P.p₁ : ℝ)) +
            ((a : ℝ) * (P.q₁ : ℝ) - (b : ℝ) * (P.q₀ : ℝ)) * P.theta) / (P.gFactor : ℝ) := by
            rw [hq_rel, hp_rel]; ring
  · rintro ⟨m, n, rfl⟩
    refine ⟨m * P.q₀ + n * P.p₀, m * P.q₁ + n * P.p₁, ?_⟩
    push_cast
    calc ((m : ℝ) + (n : ℝ) * P.theta) / (P.gFactor : ℝ)
        = (m : ℝ) * ((P.q₀ : ℝ) * P.alphaU + (P.q₁ : ℝ) * P.alphaV) +
          (n : ℝ) * ((P.p₀ : ℝ) * P.alphaU + (P.p₁ : ℝ) * P.alphaV) := by
            rw [hq_rel, hp_rel]; ring
      _ = ((m : ℝ) * (P.q₀ : ℝ) + (n : ℝ) * (P.p₀ : ℝ)) * P.alphaU +
          ((m : ℝ) * (P.q₁ : ℝ) + (n : ℝ) * (P.p₁ : ℝ)) * P.alphaV := by ring

lemma intCast_mem_latticePoly (P : PolyRecData) (k : ℤ) : (k : ℝ) ∈ P.latticePoly := by
  rw [P.latticePoly_eq_inv_g_lattice]
  refine ⟨k * (P.gFactor : ℤ), 0, ?_⟩
  have hgne : (P.gFactor : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt P.gFactor_pos
  push_cast
  field_simp
  ring

lemma zero_mem_latticePoly (P : PolyRecData) : (0 : ℝ) ∈ P.latticePoly := by
  simpa using P.intCast_mem_latticePoly 0

lemma neg_mem_latticePoly (P : PolyRecData) {y : ℝ} (hy : y ∈ P.latticePoly) :
    -y ∈ P.latticePoly := by
  rcases hy with ⟨a, b, rfl⟩
  refine ⟨-a, -b, ?_⟩
  push_cast; ring

lemma add_mem_latticePoly (P : PolyRecData) {x y : ℝ}
    (hx : x ∈ P.latticePoly) (hy : y ∈ P.latticePoly) :
    x + y ∈ P.latticePoly := by
  rcases hx with ⟨a₁, b₁, rfl⟩
  rcases hy with ⟨a₂, b₂, rfl⟩
  refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
  push_cast; ring

lemma latticePoly_countable (P : PolyRecData) : P.latticePoly.Countable := by
  have h : P.latticePoly =
      (fun p : ℤ × ℤ => (p.1 : ℝ) * P.alphaU + (p.2 : ℝ) * P.alphaV) '' Set.univ := by
    ext x
    simp only [latticePoly, Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ, true_and]
    constructor
    · rintro ⟨a, b, rfl⟩; exact ⟨(a, b), rfl⟩
    · rintro ⟨⟨a, b⟩, rfl⟩; exact ⟨a, b, rfl⟩
  rw [h]
  exact Set.countable_univ.image _

/-! ## 第四部分：一般递推逼近函数、缺陷与 `lem:poly-lattice`(iv) + `thm:general-rec` -/

/-- 有符号逼近余项 $u_j(x) = Q_j x - \mathrm{round}(Q_j x)$。 -/
def polyEps (P : PolyRecData) (x : ℝ) (j : ℕ) : ℝ :=
  (P.Q j : ℝ) * x - (round ((P.Q j : ℝ) * x) : ℝ)

/-- 一般多项式递推整数缺陷 $d_j(x) = M_{j+1}(x) - A_j M_j(x) - M_{j-1}(x)$。 -/
def polyDefect (P : PolyRecData) (x : ℝ) (j : ℕ) : ℤ :=
  round ((P.Q (j + 1) : ℝ) * x) - P.A j * round ((P.Q j : ℝ) * x) -
    round ((P.Q (j - 1) : ℝ) * x)

/-- 加权逼近序列 $j^\alpha \|Q_j x\|$。 -/
def polyWeightedSeq (P : PolyRecData) (α : ℝ) (x : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) ^ α * distToNearestInt ((P.Q j : ℝ) * x)

lemma polyWeightedSeq_nonneg (P : PolyRecData) (α : ℝ) (x : ℝ) (j : ℕ) :
    0 ≤ P.polyWeightedSeq α x j :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) α) (distToNearestInt_nonneg _)

/-- 加权逼近指数 $\Lambda_\alpha^{(r,c,d)}(x) := \limsup_{j\to\infty} j^\alpha \|Q_j x\|$。 -/
def polyWeightedExponent (P : PolyRecData) (α : ℝ) (x : ℝ) : ℝ≥0∞ :=
  limsup (fun j : ℕ => ENNReal.ofReal (P.polyWeightedSeq α x j)) atTop

/-- 临界逼近指数 $\Lambda^{(r,c,d)}(x) := \Lambda_r^{(r,c,d)}(x)$。 -/
def polyApprExponent (P : PolyRecData) (x : ℝ) : ℝ≥0∞ :=
  P.polyWeightedExponent (P.r : ℝ) x

/-- 水平集 $\{x : \Lambda^{(r,c,d)}(x) \le t\}$。 -/
def polyLevelSet (P : PolyRecData) (t : ℝ≥0∞) : Set ℝ :=
  {x : ℝ | P.polyApprExponent x ≤ t}

lemma abs_polyEps_eq_dist (P : PolyRecData) (x : ℝ) (j : ℕ) :
    |P.polyEps x j| = distToNearestInt ((P.Q j : ℝ) * x) := rfl

lemma abs_polyEps_le_half (P : PolyRecData) (x : ℝ) (j : ℕ) :
    |P.polyEps x j| ≤ 1 / 2 :=
  abs_sub_round _

lemma poly_defect_identity (P : PolyRecData) (x : ℝ) {j : ℕ} (hj : P.J₀ ≤ j) :
    (P.polyDefect x j : ℝ) =
      (P.A j : ℝ) * P.polyEps x j - P.polyEps x (j + 1) + P.polyEps x (j - 1) := by
  have hQ : (P.Q (j + 1) : ℝ) = (P.A j : ℝ) * (P.Q j : ℝ) + (P.Q (j - 1) : ℝ) := by
    exact_mod_cast P.hQ_rec j hj
  simp only [polyDefect, polyEps]
  push_cast
  rw [hQ]
  ring

/-- `lem:poly-lattice`(iv) 定量核：$x \in L^{(r,c,d)} \implies \|Q_j x\| \le C / Q_{j+1}$。 -/
theorem poly_dist_le_of_mem_latticePoly (P : PolyRecData) {x : ℝ} (hx : x ∈ P.latticePoly) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, P.J₀ ≤ j →
      distToNearestInt ((P.Q j : ℝ) * x) ≤ C / (P.Q (j + 1) : ℝ) := by
  rcases hx with ⟨a, b, rfl⟩
  have hQ0nn : (0 : ℝ) ≤ (P.Q P.J₀ : ℝ) := by exact_mod_cast (P.hQ_pos P.J₀).le
  have hQ1nn : (0 : ℝ) ≤ (P.Q (P.J₀ - 1) : ℝ) := by exact_mod_cast (P.hQ_pos (P.J₀ - 1)).le
  refine ⟨|(a : ℝ)| * (P.Q P.J₀ : ℝ) + |(b : ℝ)| * (P.Q (P.J₀ - 1) : ℝ), by positivity, ?_⟩
  intro j hj
  have hQa : (0 : ℝ) < (P.Q j : ℝ) := by exact_mod_cast P.hQ_pos j
  have hQb : (0 : ℝ) < (P.Q (j + 1) : ℝ) := by exact_mod_cast P.hQ_pos (j + 1)
  let M : ℤ := a * P.fundU j + b * P.fundV j
  have h1 := distToNearestInt_le ((P.Q j : ℝ) * ((a : ℝ) * P.alphaU + (b : ℝ) * P.alphaV)) M
  have heq : (P.Q j : ℝ) * ((a : ℝ) * P.alphaU + (b : ℝ) * P.alphaV) - (M : ℝ) =
      (a : ℝ) * (P.Q j : ℝ) * (P.alphaU - (P.fundU j : ℝ) / (P.Q j : ℝ)) +
        (b : ℝ) * (P.Q j : ℝ) * (P.alphaV - (P.fundV j : ℝ) / (P.Q j : ℝ)) := by
    simp only [M]; push_cast; field_simp; ring
  have hU := (P.abs_alphaU_sub_lt hj).2
  have hV := (P.abs_alphaV_sub_lt hj).2
  calc distToNearestInt ((P.Q j : ℝ) * ((a : ℝ) * P.alphaU + (b : ℝ) * P.alphaV))
      ≤ |(P.Q j : ℝ) * ((a : ℝ) * P.alphaU + (b : ℝ) * P.alphaV) - (M : ℝ)| := h1
    _ ≤ |(a : ℝ) * (P.Q j : ℝ) * (P.alphaU - (P.fundU j : ℝ) / (P.Q j : ℝ))| +
          |(b : ℝ) * (P.Q j : ℝ) * (P.alphaV - (P.fundV j : ℝ) / (P.Q j : ℝ))| := by
        rw [heq]; exact abs_add_le _ _
    _ = |(a : ℝ)| * (P.Q j : ℝ) * |P.alphaU - (P.fundU j : ℝ) / (P.Q j : ℝ)| +
          |(b : ℝ)| * (P.Q j : ℝ) * |P.alphaV - (P.fundV j : ℝ) / (P.Q j : ℝ)| := by
        simp only [abs_mul, abs_of_pos hQa]
    _ ≤ |(a : ℝ)| * (P.Q j : ℝ) * ((P.Q P.J₀ : ℝ) / ((P.Q j : ℝ) * (P.Q (j + 1) : ℝ))) +
          |(b : ℝ)| * (P.Q j : ℝ) *
            ((P.Q (P.J₀ - 1) : ℝ) / ((P.Q j : ℝ) * (P.Q (j + 1) : ℝ))) := by
        gcongr
    _ = (|(a : ℝ)| * (P.Q P.J₀ : ℝ) + |(b : ℝ)| * (P.Q (P.J₀ - 1) : ℝ)) / (P.Q (j + 1) : ℝ) := by
        field_simp

lemma polyWeightedExponent_eq_zero_iff (P : PolyRecData) (α : ℝ) (x : ℝ) :
    P.polyWeightedExponent α x = 0 ↔
      Tendsto (P.polyWeightedSeq α x) atTop (nhds 0) := by
  have hof : Tendsto (fun j : ℕ => ENNReal.ofReal (P.polyWeightedSeq α x j)) atTop (nhds 0) ↔
      Tendsto (P.polyWeightedSeq α x) atTop (nhds 0) := by
    constructor
    · intro h
      have hto : Tendsto ENNReal.toReal (nhds (0 : ℝ≥0∞)) (nhds 0) := by
        simpa using ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)
      have hcomp := hto.comp h
      refine hcomp.congr (fun j => ?_)
      simp [ENNReal.toReal_ofReal (P.polyWeightedSeq_nonneg α x j)]
    · intro h
      simpa using ENNReal.tendsto_ofReal h
  rw [← hof]
  constructor
  · intro h
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hev : ∀ᶠ j : ℕ in atTop, ENNReal.ofReal (P.polyWeightedSeq α x j) < ε :=
      (Filter.limsup_le_iff (u := fun j => ENNReal.ofReal (P.polyWeightedSeq α x j))
        (f := atTop) (x := 0)).mp (le_of_eq h) ε hε
    exact hev.mono (fun _ hj => le_of_lt hj)
  · intro h
    exact h.limsup_eq

/-- **Lemma `lem:poly-lattice`(iv)**：若 $x \in L^{(r,c,d)}$，则对一切 $\alpha \in \mathbb{R}$，
    $\Lambda_\alpha^{(r,c,d)}(x) = 0$。 -/
theorem polyWeightedExponent_eq_zero_of_mem_latticePoly (P : PolyRecData)
    {x : ℝ} (hx : x ∈ P.latticePoly) (α : ℝ) :
    P.polyWeightedExponent α x = 0 := by
  rw [P.polyWeightedExponent_eq_zero_iff]
  obtain ⟨C, hC0, hC⟩ := P.poly_dist_le_of_mem_latticePoly hx
  have hlim_div : Tendsto (fun j : ℕ => C * (((j : ℝ) ^ α) / (P.Q (j + 1) : ℝ))) atTop (nhds 0) := by
    have hpow : Tendsto (fun m : ℕ => (m : ℝ) ^ α / (P.Q m : ℝ)) atTop (nhds 0) :=
      P.poly_pow_div_Q_tendsto_zero α
    have hshift : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ α / (P.Q (j + 1) : ℝ)) atTop (nhds 0) :=
      hpow.comp (tendsto_add_atTop_nat 1)
    by_cases hα : 0 ≤ α
    · have hle : ∀ᶠ j : ℕ in atTop,
          (j : ℝ) ^ α / (P.Q (j + 1) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ α / (P.Q (j + 1) : ℝ) := by
        filter_upwards [eventually_ge_atTop 1] with j hj
        have hQ : (0 : ℝ) < (P.Q (j + 1) : ℝ) := by exact_mod_cast P.hQ_pos (j + 1)
        apply div_le_div_of_nonneg_right _ (le_of_lt hQ)
        exact Real.rpow_le_rpow (Nat.cast_nonneg j) (by push_cast; linarith) hα
      have h0 : Tendsto (fun j : ℕ => (j : ℝ) ^ α / (P.Q (j + 1) : ℝ)) atTop (nhds 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hshift
          (Filter.Eventually.of_forall fun j => div_nonneg
            (Real.rpow_nonneg (Nat.cast_nonneg j) α) (by exact_mod_cast (P.hQ_pos (j + 1)).le))
          hle
      simpa using h0.const_mul C
    · have hα_neg : α ≤ 0 := le_of_not_ge hα
      have hle : ∀ᶠ j : ℕ in atTop,
          (j : ℝ) ^ α / (P.Q (j + 1) : ℝ) ≤ 1 / (P.Q (j + 1) : ℝ) := by
        filter_upwards [eventually_ge_atTop 1] with j hj
        have hQ : (0 : ℝ) < (P.Q (j + 1) : ℝ) := by exact_mod_cast P.hQ_pos (j + 1)
        apply div_le_div_of_nonneg_right _ (le_of_lt hQ)
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hj) hα_neg
      have h0_inv : Tendsto (fun j : ℕ => 1 / (P.Q (j + 1) : ℝ)) atTop (nhds 0) :=
        (P.poly_Q_tendsto_atTop.comp (tendsto_add_atTop_nat 1)).const_div_atTop 1
      have h0 : Tendsto (fun j : ℕ => (j : ℝ) ^ α / (P.Q (j + 1) : ℝ)) atTop (nhds 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0_inv
          (Filter.Eventually.of_forall fun j => div_nonneg
            (Real.rpow_nonneg (Nat.cast_nonneg j) α) (by exact_mod_cast (P.hQ_pos (j + 1)).le))
          hle
      simpa using h0.const_mul C
  have hbound : ∀ᶠ j : ℕ in atTop,
      P.polyWeightedSeq α x j ≤ C * (((j : ℝ) ^ α) / (P.Q (j + 1) : ℝ)) := by
    filter_upwards [eventually_ge_atTop P.J₀] with j hj
    unfold polyWeightedSeq
    calc (j : ℝ) ^ α * distToNearestInt ((P.Q j : ℝ) * x)
        ≤ (j : ℝ) ^ α * (C / (P.Q (j + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC j hj) (Real.rpow_nonneg (Nat.cast_nonneg j) α)
      _ = C * (((j : ℝ) ^ α) / (P.Q (j + 1) : ℝ)) := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_div
    (Filter.Eventually.of_forall (P.polyWeightedSeq_nonneg α x)) hbound

lemma polyEps_tendsto_zero_of_apprExponent_ne_top (P : PolyRecData) {x : ℝ}
    (hfin : P.polyApprExponent x ≠ ⊤) :
    Tendsto (P.polyEps x) atTop (nhds 0) := by
  set B := (P.polyApprExponent x).toReal + 1
  have hlt : P.polyApprExponent x < ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hev : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (P.polyWeightedSeq (P.r : ℝ) x j) < ENNReal.ofReal B :=
    eventually_lt_of_limsup_lt hlt
  have hbound : ∀ᶠ j : ℕ in atTop, |P.polyEps x j| ≤ B / (j : ℝ) := by
    filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
    have hBpos : 0 < B := by positivity
    have hle : P.polyWeightedSeq (P.r : ℝ) x j ≤ B :=
      le_of_lt ((ENNReal.ofReal_lt_ofReal_iff hBpos).mp hj)
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hjr : (j : ℝ) ≤ (j : ℝ) ^ P.r := by
      have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      calc (j : ℝ) = (j : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (j : ℝ) ^ P.r := pow_le_pow_right₀ hj1R P.hr
    have hmul : (j : ℝ) * |P.polyEps x j| ≤ B := by
      have h1 : (j : ℝ) ^ (P.r : ℝ) * |P.polyEps x j| ≤ B := by
        simpa [polyWeightedSeq, abs_polyEps_eq_dist] using hle
      have h2 : (j : ℝ) * |P.polyEps x j| ≤ (j : ℝ) ^ (P.r : ℝ) * |P.polyEps x j| := by
        rw [Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_right hjr (abs_nonneg _)
      exact le_trans h2 h1
    exact (le_div_iff₀ hjpos).mpr (by linarith)
  exact FullSpectrumDiscrete.tendsto_zero_of_eventually_abs_le_div hbound

/-- **Theorem `thm:general-rec`(i)**：若 $u_j(x) \to 0$，则
    $d_j(x) - c j^r u_j(x) \to 0$ 且 $|d_j(x)| - c j^r \|Q_j x\| \to 0$。 -/
theorem poly_signed_defect_approx (P : PolyRecData) (x : ℝ)
    (hu : Tendsto (P.polyEps x) atTop (nhds 0)) :
    Tendsto (fun j : ℕ => (P.polyDefect x j : ℝ) - (P.c : ℝ) * (j : ℝ) ^ P.r * P.polyEps x j)
      atTop (nhds 0) := by
  have hu_next : Tendsto (fun j : ℕ => P.polyEps x (j + 1)) atTop (nhds 0) :=
    hu.comp (tendsto_add_atTop_nat 1)
  have hu_prev : Tendsto (fun j : ℕ => P.polyEps x (j - 1)) atTop (nhds 0) :=
    hu.comp FullSpectrumDiscrete.tendsto_sub_one_atTop
  have hdu : Tendsto (fun j : ℕ => (P.d : ℝ) * P.polyEps x j) atTop (nhds 0) := by
    simpa using hu.const_mul (P.d : ℝ)
  have hrhs : Tendsto (fun j : ℕ =>
      (P.d : ℝ) * P.polyEps x j - P.polyEps x (j + 1) + P.polyEps x (j - 1))
      atTop (nhds 0) := by
    simpa using (hdu.sub hu_next).add hu_prev
  refine hrhs.congr' ?_
  filter_upwards [eventually_ge_atTop P.J₀] with j hj
  have hid := P.poly_defect_identity x hj
  have hA : (P.A j : ℝ) = (P.c : ℝ) * (j : ℝ) ^ P.r + (P.d : ℝ) := by
    unfold A; push_cast; ring
  rw [hA] at hid
  linarith [hid]

theorem poly_abs_defect_approx (P : PolyRecData) (x : ℝ)
    (hu : Tendsto (P.polyEps x) atTop (nhds 0)) :
    Tendsto (fun j : ℕ => |(P.polyDefect x j : ℝ)| -
        (P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x))
      atTop (nhds 0) := by
  have hs := P.poly_signed_defect_approx x hu
  have habs_s : Tendsto (fun j : ℕ =>
      |(P.polyDefect x j : ℝ) - (P.c : ℝ) * (j : ℝ) ^ P.r * P.polyEps x j|) atTop (nhds 0) := by
    simpa using hs.abs
  have hneg : Tendsto (fun j : ℕ =>
      -|(P.polyDefect x j : ℝ) - (P.c : ℝ) * (j : ℝ) ^ P.r * P.polyEps x j|) atTop (nhds 0) := by
    simpa using habs_s.neg
  have hbound : ∀ j : ℕ,
      abs (|(P.polyDefect x j : ℝ)| - (P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x)) ≤
        |(P.polyDefect x j : ℝ) - (P.c : ℝ) * (j : ℝ) ^ P.r * P.polyEps x j| := by
    intro j
    have hcj : 0 ≤ (P.c : ℝ) * (j : ℝ) ^ P.r := by positivity
    have heps : |P.polyEps x j| = distToNearestInt ((P.Q j : ℝ) * x) := rfl
    have hmul : (P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x) =
        |(P.c : ℝ) * (j : ℝ) ^ P.r * P.polyEps x j| := by
      rw [← heps, abs_mul, abs_of_nonneg hcj]
    rw [hmul]
    exact abs_abs_sub_abs_le_abs_sub _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg habs_s
    (Filter.Eventually.of_forall fun j => (abs_le.mp (hbound j)).1)
    (Filter.Eventually.of_forall fun j => (abs_le.mp (hbound j)).2)

lemma poly_mem_latticePoly_of_eventually_defect_zero (P : PolyRecData) (x : ℝ)
    (hu : Tendsto (P.polyEps x) atTop (nhds 0))
    (hD : ∀ᶠ j : ℕ in atTop, P.polyDefect x j = 0) :
    x ∈ P.latticePoly := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hD
  set N := max N₀ (P.J₀ + 1)
  have hN_J₀ : P.J₀ + 1 ≤ N := le_max_right _ _
  have hDN : ∀ j : ℕ, N ≤ j → P.polyDefect x j = 0 := fun j hj =>
    hN₀ j (le_trans (le_max_left _ _) hj)
  let M : ℕ → ℤ := fun j => round ((P.Q j : ℝ) * x)
  set s : ℤ := (-1 : ℤ) ^ (N - P.J₀)
  have hs2 : s * (P.fundU (N - 1) * P.fundV N - P.fundU N * P.fundV (N - 1)) = 1 := by
    have hcas := P.poly_casorati (show P.J₀ - 1 ≤ N - 1 by omega)
    have hsub1 : N - 1 + 1 = N := by omega
    rw [hsub1] at hcas
    rw [hcas]
    dsimp [s]
    rw [← pow_add, show (N - P.J₀) + (N - P.J₀) = 2 * (N - P.J₀) by ring, pow_mul]
    norm_num
  set a : ℤ := s * (M (N - 1) * P.fundV N - M N * P.fundV (N - 1))
  set b : ℤ := s * (P.fundU (N - 1) * M N - P.fundU N * M (N - 1))
  have hprop : ∀ j : ℕ, N - 1 ≤ j → M j = a * P.fundU j + b * P.fundV j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hj
        by_cases hj1 : j = N - 1
        · subst hj1
          have halg : a * P.fundU (N - 1) + b * P.fundV (N - 1) =
              M (N - 1) * (s * (P.fundU (N - 1) * P.fundV N - P.fundU N * P.fundV (N - 1))) := by
            dsimp [a, b]; ring
          rw [halg, hs2, mul_one]
        · by_cases hj2 : j = N
          · subst hj2
            have halg : a * P.fundU N + b * P.fundV N =
                M N * (s * (P.fundU (N - 1) * P.fundV N - P.fundU N * P.fundV (N - 1))) := by
              dsimp [a, b]; ring
            rw [halg, hs2, mul_one]
          · have hjN1 : N + 1 ≤ j := by omega
            have hjm : N ≤ j - 1 := by omega
            have hDj := hDN (j - 1) hjm
            have hrecM : M j = P.A (j - 1) * M (j - 1) + M (j - 1 - 1) := by
              have h1 : j - 1 + 1 = j := by omega
              have hd := hDj
              unfold polyDefect at hd
              change round ((P.Q ((j - 1) + 1) : ℝ) * x) -
                  P.A (j - 1) * round ((P.Q (j - 1) : ℝ) * x) -
                  round ((P.Q ((j - 1) - 1) : ℝ) * x) = 0 at hd
              rw [h1] at hd
              change M j - P.A (j - 1) * M (j - 1) - M (j - 1 - 1) = 0 at hd
              omega
            have hrecU : P.fundU j = P.A (j - 1) * P.fundU (j - 1) + P.fundU (j - 1 - 1) := by
              have h1 : j - 1 + 1 = j := by omega
              have := P.fundU_rec (show P.J₀ ≤ j - 1 by omega)
              rwa [h1] at this
            have hrecV : P.fundV j = P.A (j - 1) * P.fundV (j - 1) + P.fundV (j - 1 - 1) := by
              have h1 : j - 1 + 1 = j := by omega
              have := P.fundV_rec (show P.J₀ ≤ j - 1 by omega)
              rwa [h1] at this
            have ih1 := ih (j - 1) (by omega) (by omega)
            have ih2 := ih (j - 1 - 1) (by omega) (by omega)
            rw [hrecM, hrecU, hrecV, ih1, ih2]
            ring
  have hlim_M : Tendsto (fun j : ℕ => (M j : ℝ) / (P.Q j : ℝ)) atTop (nhds x) := by
    have heq : ∀ j : ℕ, (M j : ℝ) / (P.Q j : ℝ) = x - P.polyEps x j / (P.Q j : ℝ) := by
      intro j
      have hQ : (P.Q j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.hQ_pos j)
      simp only [M, polyEps]
      field_simp
      ring
    have hdiv : Tendsto (fun j : ℕ => P.polyEps x j / (P.Q j : ℝ)) atTop (nhds 0) := by
      have hinv : Tendsto (fun j : ℕ => (P.Q j : ℝ)⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp P.poly_Q_tendsto_atTop
      simpa [div_eq_mul_inv] using hu.mul hinv
    have hsub : Tendsto (fun j : ℕ => x - P.polyEps x j / (P.Q j : ℝ)) atTop (nhds x) := by
      simpa using tendsto_const_nhds.sub hdiv
    exact hsub.congr (fun j => (heq j).symm)
  have hlim_UV : Tendsto (fun j : ℕ =>
      (a : ℝ) * ((P.fundU j : ℝ) / (P.Q j : ℝ)) + (b : ℝ) * ((P.fundV j : ℝ) / (P.Q j : ℝ)))
      atTop (nhds ((a : ℝ) * P.alphaU + (b : ℝ) * P.alphaV)) :=
    (P.tendsto_fundU_div_Q.const_mul _).add (P.tendsto_fundV_div_Q.const_mul _)
  have heq_tail : ∀ᶠ j : ℕ in atTop,
      (M j : ℝ) / (P.Q j : ℝ) =
        (a : ℝ) * ((P.fundU j : ℝ) / (P.Q j : ℝ)) + (b : ℝ) * ((P.fundV j : ℝ) / (P.Q j : ℝ)) := by
    filter_upwards [eventually_ge_atTop (N - 1)] with j hj
    have hMj : (M j : ℝ) = (a : ℝ) * (P.fundU j : ℝ) + (b : ℝ) * (P.fundV j : ℝ) := by
      exact_mod_cast hprop j hj
    rw [hMj]
    ring
  have hx_eq : x = (a : ℝ) * P.alphaU + (b : ℝ) * P.alphaV :=
    tendsto_nhds_unique hlim_M (hlim_UV.congr' (heq_tail.mono fun _ h => h.symm))
  exact ⟨a, b, hx_eq⟩

/-- **Lemma `lem:poly-lattice`(iv) 完整刻画**：
    $\Lambda^{(r,c,d)}(x) = 0 \iff (u_j(x) \to 0 \land \forall^\infty j,\, d_j(x) = 0) \iff x \in L^{(r,c,d)}$。 -/
theorem polyApprExponent_eq_zero_tfae (P : PolyRecData) (x : ℝ) :
    P.polyApprExponent x = 0 ↔
      (Tendsto (P.polyEps x) atTop (nhds 0) ∧ ∀ᶠ j : ℕ in atTop, P.polyDefect x j = 0) ∧
      (x ∈ P.latticePoly) := by
  constructor
  · intro h0
    have hfin : P.polyApprExponent x ≠ ⊤ := by rw [h0]; exact ENNReal.zero_ne_top
    have hu := P.polyEps_tendsto_zero_of_apprExponent_ne_top hfin
    have hseq0 : Tendsto (P.polyWeightedSeq (P.r : ℝ) x) atTop (nhds 0) :=
      (P.polyWeightedExponent_eq_zero_iff (P.r : ℝ) x).mp h0
    have happrox := P.poly_abs_defect_approx x hu
    have hclim : Tendsto (fun j : ℕ =>
        (P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x)) atTop (nhds 0) := by
      have h1 := hseq0.const_mul (P.c : ℝ)
      simpa [polyWeightedSeq, mul_assoc, Real.rpow_natCast] using h1
    have happrox' : Tendsto (fun j : ℕ => (((|P.polyDefect x j| : ℤ) : ℝ) -
        (P.c : ℝ) * (j : ℝ) ^ P.r * distToNearestInt ((P.Q j : ℝ) * x))) atTop (nhds 0) := by
      refine happrox.congr (fun j => ?_)
      rw [Int.cast_abs]
    have hDabs : ∀ᶠ j : ℕ in atTop, |P.polyDefect x j| = (0 : ℤ) :=
      FullSpectrumDiscrete.eventually_eq_int_of_tendsto happrox' 0 (by simpa using hclim)
    have hD0 : ∀ᶠ j : ℕ in atTop, P.polyDefect x j = 0 := by
      filter_upwards [hDabs] with j hj
      exact abs_eq_zero.mp hj
    exact ⟨⟨hu, hD0⟩, P.poly_mem_latticePoly_of_eventually_defect_zero x hu hD0⟩
  · rintro ⟨_, hxL⟩
    exact P.polyWeightedExponent_eq_zero_of_mem_latticePoly hxL (P.r : ℝ)

theorem polyApprExponent_eq_zero_iff_mem_latticePoly (P : PolyRecData) (x : ℝ) :
    P.polyApprExponent x = 0 ↔ x ∈ P.latticePoly :=
  ⟨fun h => ((P.polyApprExponent_eq_zero_tfae x).mp h).2,
   fun hx => P.polyWeightedExponent_eq_zero_of_mem_latticePoly hx (P.r : ℝ)⟩

theorem polyApprExponent_eq_zero_iff_defect_zero (P : PolyRecData) (x : ℝ) :
    P.polyApprExponent x = 0 ↔
      Tendsto (P.polyEps x) atTop (nhds 0) ∧ ∀ᶠ j : ℕ in atTop, P.polyDefect x j = 0 :=
  ⟨fun h => ((P.polyApprExponent_eq_zero_tfae x).mp h).1,
   fun ⟨hu, hD⟩ => P.polyWeightedExponent_eq_zero_of_mem_latticePoly
     (P.poly_mem_latticePoly_of_eventually_defect_zero x hu hD) (P.r : ℝ)⟩

/-! ## 第五部分：一般多项式递推的常值缺陷见证 `xPlusPoly` 与全谱离散化 (`thm:general-rec`) -/

/-- 常值缺陷 $+k$ 的起始指标 $N_k := \max(J_0 + 1,\, 32k + |d| + 2)$。 -/
def N_witness (P : PolyRecData) (k : ℕ) : ℕ :=
  max (P.J₀ + 1) (32 * k + P.d.natAbs + 2)

lemma N_witness_ge_J₀_succ (P : PolyRecData) (k : ℕ) : P.J₀ + 1 ≤ P.N_witness k :=
  le_max_left _ _

lemma A_pred_N_witness_gt (P : PolyRecData) (k : ℕ) :
    32 * (k : ℤ) < P.A (P.N_witness k - 1) := by
  have h1 : 32 * k + P.d.natAbs + 2 ≤ P.N_witness k := le_max_right _ _
  have h2 : 32 * k + P.d.natAbs + 1 ≤ P.N_witness k - 1 := by omega
  have hm_ge1 : 1 ≤ P.N_witness k - 1 := by omega
  have hmR : (32 * (k : ℤ) + (P.d.natAbs : ℤ) + 1) ≤ ((P.N_witness k - 1 : ℕ) : ℤ) := by
    exact_mod_cast h2
  have hpow : ((P.N_witness k - 1 : ℕ) : ℤ) ≤ ((P.N_witness k - 1 : ℕ) : ℤ) ^ P.r := by
    have h1Z : (1 : ℤ) ≤ ((P.N_witness k - 1 : ℕ) : ℤ) := by exact_mod_cast hm_ge1
    calc ((P.N_witness k - 1 : ℕ) : ℤ)
        = ((P.N_witness k - 1 : ℕ) : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ ((P.N_witness k - 1 : ℕ) : ℤ) ^ P.r := pow_le_pow_right₀ h1Z P.hr
  have hc1 : (1 : ℤ) ≤ (P.c : ℤ) := by exact_mod_cast P.hc
  have hpow_pos : (0 : ℤ) ≤ ((P.N_witness k - 1 : ℕ) : ℤ) ^ P.r := by positivity
  have hcmul : ((P.N_witness k - 1 : ℕ) : ℤ) ^ P.r ≤
      (P.c : ℤ) * ((P.N_witness k - 1 : ℕ) : ℤ) ^ P.r := by nlinarith
  have hd_le : -(P.d.natAbs : ℤ) ≤ P.d := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le P.d
  unfold A
  linarith

/-- 一般 $(c j^r + d)$ 递推的常值缺陷 $+k$ 分子序列（$m \le N_k$ 时为 $0$）。 -/
def MPlusPoly (P : PolyRecData) (k : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
      if n + 1 < P.N_witness k then 0
      else P.A (n + 1) * MPlusPoly P k (n + 1) + MPlusPoly P k n + (k : ℤ)

lemma MPlusPoly_eq_zero_of_le (P : PolyRecData) (k m : ℕ) (hm : m ≤ P.N_witness k) :
    P.MPlusPoly k m = 0 := by
  rcases m with _ | _ | n
  · rfl
  · rfl
  · simp only [MPlusPoly]
    have hlt : n + 1 < P.N_witness k := by omega
    simp [hlt]

lemma MPlusPoly_rec (P : PolyRecData) (k j : ℕ) (hj : P.N_witness k ≤ j) :
    P.MPlusPoly k (j + 1) = P.A j * P.MPlusPoly k j + P.MPlusPoly k (j - 1) + (k : ℤ) := by
  have hge1 : 1 ≤ j := by have := P.N_witness_ge_J₀_succ k; have := P.hJ₀; omega
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have hnot : ¬ (n + 1 < P.N_witness k) := by omega
  have hsub : n + 1 - 1 = n := by omega
  have hadd : n + 1 + 1 = n + 2 := by omega
  rw [hadd, hsub]
  simp [MPlusPoly, hnot]

def WPlusPoly (P : PolyRecData) (k j : ℕ) : ℤ :=
  P.MPlusPoly k (j + 1) * P.Q j - P.MPlusPoly k j * P.Q (j + 1)

lemma WPlusPoly_init (P : PolyRecData) (k : ℕ) :
    P.WPlusPoly k (P.N_witness k - 1) = 0 := by
  have hN : 1 ≤ P.N_witness k := by have := P.N_witness_ge_J₀_succ k; have := P.hJ₀; omega
  have hadd : P.N_witness k - 1 + 1 = P.N_witness k := by omega
  unfold WPlusPoly
  rw [hadd, P.MPlusPoly_eq_zero_of_le k (P.N_witness k) (le_refl _),
    P.MPlusPoly_eq_zero_of_le k (P.N_witness k - 1) (by omega)]
  ring

lemma WPlusPoly_rec (P : PolyRecData) (k j : ℕ) (hj : P.N_witness k ≤ j) :
    P.WPlusPoly k j = (k : ℤ) * P.Q j - P.WPlusPoly k (j - 1) := by
  have hj1 : 1 ≤ j := by have := P.N_witness_ge_J₀_succ k; have := P.hJ₀; omega
  have hj_J₀ : P.J₀ ≤ j := le_trans (by have := P.N_witness_ge_J₀_succ k; omega) hj
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hsub : m + 1 - 1 = m := by omega
  rw [hsub]
  have hQ := P.hQ_rec (m + 1) hj_J₀
  rw [hsub] at hQ
  have hM := P.MPlusPoly_rec k (m + 1) hj
  rw [hsub] at hM
  simp only [WPlusPoly]
  rw [hM, hQ]
  change (P.A (m + 1) * P.MPlusPoly k (m + 1) + P.MPlusPoly k m + (k : ℤ)) * P.Q (m + 1) -
      P.MPlusPoly k (m + 1) * (P.A (m + 1) * P.Q (m + 1) + P.Q m) =
    (k : ℤ) * P.Q (m + 1) - (P.MPlusPoly k (m + 1) * P.Q m - P.MPlusPoly k m * P.Q (m + 1))
  ring

lemma WPlusPoly_bounds (P : PolyRecData) (k j : ℕ) (hj : P.N_witness k - 1 ≤ j) :
    0 ≤ P.WPlusPoly k j ∧ P.WPlusPoly k j ≤ (k : ℤ) * P.Q j := by
  have hN_ge : P.J₀ + 1 ≤ P.N_witness k := P.N_witness_ge_J₀_succ k
  obtain ⟨n, hn⟩ : ∃ n, j = (P.N_witness k - 1) + n := ⟨j - (P.N_witness k - 1), by omega⟩
  subst hn
  induction n with
  | zero =>
      rw [Nat.add_zero, P.WPlusPoly_init k]
      exact ⟨le_refl 0, mul_nonneg (Int.natCast_nonneg k) (le_of_lt (P.hQ_pos _))⟩
  | succ n ih =>
      have ihn := ih (by omega)
      have hidx : P.N_witness k ≤ (P.N_witness k - 1) + (n + 1) := by omega
      have hrec := P.WPlusPoly_rec k ((P.N_witness k - 1) + (n + 1)) hidx
      have hsub : (P.N_witness k - 1) + (n + 1) - 1 = (P.N_witness k - 1) + n := by omega
      rw [hsub] at hrec
      have hJ₀_idx : P.J₀ ≤ (P.N_witness k - 1) + n := by omega
      have hmono : P.Q ((P.N_witness k - 1) + n) ≤ P.Q ((P.N_witness k - 1) + (n + 1)) := by
        have hlt := P.poly_Q_lt_succ hJ₀_idx
        have hadd : (P.N_witness k - 1) + n + 1 = (P.N_witness k - 1) + (n + 1) := by omega
        rw [hadd] at hlt
        exact le_of_lt hlt
      have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
      have hkQ : (k : ℤ) * P.Q ((P.N_witness k - 1) + n) ≤
          (k : ℤ) * P.Q ((P.N_witness k - 1) + (n + 1)) :=
        mul_le_mul_of_nonneg_left hmono hk0
      constructor <;> linarith [ihn.1, ihn.2, hrec, hkQ]

def diffPlusPoly (P : PolyRecData) (k j : ℕ) : ℝ :=
  (P.MPlusPoly k (j + 1) : ℝ) / (P.Q (j + 1) : ℝ) - (P.MPlusPoly k j : ℝ) / (P.Q j : ℝ)

lemma diffPlusPoly_eq_WPlusPoly (P : PolyRecData) (k j : ℕ) :
    P.diffPlusPoly k j = (P.WPlusPoly k j : ℝ) / ((P.Q j : ℝ) * (P.Q (j + 1) : ℝ)) := by
  have hQ1 : (P.Q j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.hQ_pos j)
  have hQ2 : (P.Q (j + 1) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast P.hQ_pos (j + 1))
  simp only [diffPlusPoly, WPlusPoly]
  push_cast
  field_simp

lemma diffPlusPoly_nonneg (P : PolyRecData) (k j : ℕ) (hj : P.N_witness k - 1 ≤ j) :
    0 ≤ P.diffPlusPoly k j := by
  rw [P.diffPlusPoly_eq_WPlusPoly]
  have hQ1 : (0 : ℝ) < (P.Q j : ℝ) := by exact_mod_cast P.hQ_pos j
  have hQ2 : (0 : ℝ) < (P.Q (j + 1) : ℝ) := by exact_mod_cast P.hQ_pos (j + 1)
  have hW : (0 : ℝ) ≤ (P.WPlusPoly k j : ℝ) := by exact_mod_cast (P.WPlusPoly_bounds k j hj).1
  exact div_nonneg hW (le_of_lt (mul_pos hQ1 hQ2))

lemma diffPlusPoly_le (P : PolyRecData) (k j : ℕ) (hj : P.N_witness k - 1 ≤ j) :
    P.diffPlusPoly k j ≤ (k : ℝ) / (P.Q (j + 1) : ℝ) := by
  rw [P.diffPlusPoly_eq_WPlusPoly]
  have hQ1 : (0 : ℝ) < (P.Q j : ℝ) := by exact_mod_cast P.hQ_pos j
  have hQ2 : (0 : ℝ) < (P.Q (j + 1) : ℝ) := by exact_mod_cast P.hQ_pos (j + 1)
  have hW : (P.WPlusPoly k j : ℝ) ≤ (k : ℝ) * (P.Q j : ℝ) := by
    exact_mod_cast (P.WPlusPoly_bounds k j hj).2
  rw [div_le_div_iff₀ (mul_pos hQ1 hQ2) hQ2]
  nlinarith

lemma poly_summable_inv_Q (P : PolyRecData) :
    Summable (fun j : ℕ => 1 / (P.Q j : ℝ)) := by
  have hshift : Summable (fun n : ℕ => 1 / (P.Q (P.J₀ + n) : ℝ)) := by
    have hQ0 : (0 : ℝ) < (P.Q P.J₀ : ℝ) := by exact_mod_cast P.hQ_pos P.J₀
    have hbound : ∀ n : ℕ, 1 / (P.Q (P.J₀ + n) : ℝ) ≤ (1 / (P.Q P.J₀ : ℝ)) * (1 / 2 : ℝ) ^ n := by
      intro n
      have hQn : (0 : ℝ) < (P.Q (P.J₀ + n) : ℝ) := by exact_mod_cast P.hQ_pos (P.J₀ + n)
      have hg := P.poly_Q_geom (le_refl P.J₀) n
      rw [div_le_iff₀ hQn]
      have hpow : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
      calc (1 : ℝ) = (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n := hpow.symm
        _ = ((1 / (P.Q P.J₀ : ℝ)) * (1 / 2 : ℝ) ^ n) * ((2 : ℝ) ^ n * (P.Q P.J₀ : ℝ)) := by
            field_simp
        _ ≤ ((1 / (P.Q P.J₀ : ℝ)) * (1 / 2 : ℝ) ^ n) * (P.Q (P.J₀ + n) : ℝ) := by gcongr
    exact Summable.of_nonneg_of_le
      (fun n => div_nonneg zero_le_one (by exact_mod_cast (P.hQ_pos (P.J₀ + n)).le))
      hbound ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
  exact (summable_nat_add_iff P.J₀).mp (hshift.congr (fun n => by rw [Nat.add_comm]))

lemma summable_diffPlusPoly (P : PolyRecData) (k : ℕ) : Summable (P.diffPlusPoly k) := by
  have hshift : Summable (fun j : ℕ => (k : ℝ) * (1 / (P.Q (j + 1) : ℝ))) :=
    ((summable_nat_add_iff 1).mpr P.poly_summable_inv_Q).mul_left (k : ℝ)
  have hnorm : ∀ᶠ j in atTop, ‖P.diffPlusPoly k j‖ ≤ (k : ℝ) * (1 / (P.Q (j + 1) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (P.N_witness k - 1)] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg (P.diffPlusPoly_nonneg k j hj), mul_one_div]
    exact P.diffPlusPoly_le k j hj
  exact Summable.of_norm_bounded_eventually_nat hshift hnorm

/-- 一般 $(c j^r + d)$ 递推的常值缺陷 $+k$ 构造见证 $x_k^+$。 -/
def xPlusPoly (P : PolyRecData) (k : ℕ) : ℝ := ∑' j : ℕ, P.diffPlusPoly k j

lemma xPlusPoly_sub_ratio_bounds (P : PolyRecData) (k m : ℕ) (hm : P.N_witness k - 1 ≤ m) :
    0 ≤ P.xPlusPoly k - (P.MPlusPoly k m : ℝ) / (P.Q m : ℝ) ∧
    P.xPlusPoly k - (P.MPlusPoly k m : ℝ) / (P.Q m : ℝ) ≤ (2 * (k : ℝ)) / (P.Q (m + 1) : ℝ) := by
  have hsplit := (P.summable_diffPlusPoly k).sum_add_tsum_nat_add m
  have hsum_m : ∑ j ∈ Finset.range m, P.diffPlusPoly k j =
      (P.MPlusPoly k m : ℝ) / (P.Q m : ℝ) := by
    have h := Finset.sum_range_sub (fun j => (P.MPlusPoly k j : ℝ) / (P.Q j : ℝ)) m
    have h0 : (P.MPlusPoly k 0 : ℝ) / (P.Q 0 : ℝ) = 0 := by simp [MPlusPoly]
    simpa [diffPlusPoly, h0] using h
  have hrem : P.xPlusPoly k - (P.MPlusPoly k m : ℝ) / (P.Q m : ℝ) =
      ∑' s : ℕ, P.diffPlusPoly k (s + m) := by
    unfold xPlusPoly; linarith [hsplit, hsum_m]
  rw [hrem]
  have hs_sum : Summable (fun s : ℕ => P.diffPlusPoly k (s + m)) :=
    (P.summable_diffPlusPoly k).comp_injective (add_left_injective m)
  have hm_J₀ : P.J₀ ≤ m + 1 := by
    have := P.N_witness_ge_J₀_succ k; omega
  have hQ1 : (0 : ℝ) < (P.Q (m + 1) : ℝ) := by exact_mod_cast P.hQ_pos (m + 1)
  have hgeom_sum : Summable (fun s : ℕ => ((k : ℝ) / (P.Q (m + 1) : ℝ)) * (1 / 2 : ℝ) ^ s) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  constructor
  · exact tsum_nonneg (fun s => P.diffPlusPoly_nonneg k (s + m) (by omega))
  · have hle : ∀ s : ℕ,
        P.diffPlusPoly k (s + m) ≤ ((k : ℝ) / (P.Q (m + 1) : ℝ)) * (1 / 2 : ℝ) ^ s := by
      intro s
      have h1 := P.diffPlusPoly_le k (s + m) (by omega)
      have h2 := P.poly_Q_geom hm_J₀ s
      have hadd : m + 1 + s = s + m + 1 := by omega
      rw [hadd] at h2
      have hQsm1 : (0 : ℝ) < (P.Q (s + m + 1) : ℝ) := by exact_mod_cast P.hQ_pos (s + m + 1)
      have hinv : 1 / (P.Q (s + m + 1) : ℝ) ≤ (1 / 2 : ℝ) ^ s / (P.Q (m + 1) : ℝ) := by
        rw [div_le_div_iff₀ hQsm1 hQ1]
        have hpow : (1 / 2 : ℝ) ^ s * (2 : ℝ) ^ s = 1 := by rw [← mul_pow]; norm_num
        calc (1 : ℝ) * (P.Q (m + 1) : ℝ) = (P.Q (m + 1) : ℝ) := one_mul _
          _ = (1 / 2 : ℝ) ^ s * ((2 : ℝ) ^ s * (P.Q (m + 1) : ℝ)) := by
              rw [← mul_assoc, hpow, one_mul]
          _ ≤ (1 / 2 : ℝ) ^ s * (P.Q (s + m + 1) : ℝ) := by gcongr
      calc P.diffPlusPoly k (s + m)
          ≤ (k : ℝ) / (P.Q (s + m + 1) : ℝ) := h1
        _ = (k : ℝ) * (1 / (P.Q (s + m + 1) : ℝ)) := by ring
        _ ≤ (k : ℝ) * ((1 / 2 : ℝ) ^ s / (P.Q (m + 1) : ℝ)) := by gcongr
        _ = ((k : ℝ) / (P.Q (m + 1) : ℝ)) * (1 / 2 : ℝ) ^ s := by ring
    have htsum := Summable.tsum_le_tsum hle hs_sum hgeom_sum
    have hval : ∑' s : ℕ, ((k : ℝ) / (P.Q (m + 1) : ℝ)) * (1 / 2 : ℝ) ^ s =
        (2 * (k : ℝ)) / (P.Q (m + 1) : ℝ) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
    linarith

lemma Q_mul_xPlusPoly_sub_MPlusPoly (P : PolyRecData) (k m : ℕ) (hm : P.N_witness k - 1 ≤ m) :
    0 ≤ (P.Q m : ℝ) * P.xPlusPoly k - (P.MPlusPoly k m : ℝ) ∧
    (P.Q m : ℝ) * P.xPlusPoly k - (P.MPlusPoly k m : ℝ) ≤
      (2 * (k : ℝ) * (P.Q m : ℝ)) / (P.Q (m + 1) : ℝ) := by
  have hQ : (0 : ℝ) < (P.Q m : ℝ) := by exact_mod_cast P.hQ_pos m
  have hb := P.xPlusPoly_sub_ratio_bounds k m hm
  have heq : (P.Q m : ℝ) * P.xPlusPoly k - (P.MPlusPoly k m : ℝ) =
      (P.Q m : ℝ) * (P.xPlusPoly k - (P.MPlusPoly k m : ℝ) / (P.Q m : ℝ)) := by
    field_simp
  rw [heq]
  constructor
  · exact mul_nonneg (le_of_lt hQ) hb.1
  · calc (P.Q m : ℝ) * (P.xPlusPoly k - (P.MPlusPoly k m : ℝ) / (P.Q m : ℝ))
        ≤ (P.Q m : ℝ) * ((2 * (k : ℝ)) / (P.Q (m + 1) : ℝ)) := by gcongr; exact hb.2
      _ = (2 * (k : ℝ) * (P.Q m : ℝ)) / (P.Q (m + 1) : ℝ) := by ring

lemma Q_mul_xPlusPoly_sub_MPlusPoly_lt_half (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) (m : ℕ)
    (hm : P.N_witness k - 1 ≤ m) :
    (P.Q m : ℝ) * P.xPlusPoly k - (P.MPlusPoly k m : ℝ) < 1 / 2 := by
  have hb := (P.Q_mul_xPlusPoly_sub_MPlusPoly k m hm).2
  have hJ₀_m : P.J₀ ≤ m := by have := P.N_witness_ge_J₀_succ k; omega
  have hQ : (0 : ℝ) < (P.Q m : ℝ) := by exact_mod_cast P.hQ_pos m
  have hQ1 : (0 : ℝ) < (P.Q (m + 1) : ℝ) := by exact_mod_cast P.hQ_pos (m + 1)
  have hgt := P.poly_Q_succ_gt_A_mul hJ₀_m
  have hA : 32 * (k : ℤ) < P.A m := lt_of_lt_of_le (P.A_pred_N_witness_gt k) (A_mono hm)
  have hAR : 32 * (k : ℝ) < (P.A m : ℝ) := by exact_mod_cast hA
  have hgtR : (P.A m : ℝ) * (P.Q m : ℝ) < (P.Q (m + 1) : ℝ) := by exact_mod_cast hgt
  have hgrow : (32 * (k : ℝ)) * (P.Q m : ℝ) < (P.Q (m + 1) : ℝ) := by nlinarith
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hdiv : (2 * (k : ℝ) * (P.Q m : ℝ)) / (P.Q (m + 1) : ℝ) < 1 / 2 := by
    rw [div_lt_iff₀ hQ1]
    nlinarith
  linarith

lemma xPlusPoly_round_eq (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) (m : ℕ)
    (hm : P.N_witness k - 1 ≤ m) :
    round ((P.Q m : ℝ) * P.xPlusPoly k) = P.MPlusPoly k m := by
  have hlo := (P.Q_mul_xPlusPoly_sub_MPlusPoly k m hm).1
  have hhi := P.Q_mul_xPlusPoly_sub_MPlusPoly_lt_half hk m hm
  rw [round_eq_iff]
  constructor <;> linarith

lemma neg_xPlusPoly_round_eq (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) (m : ℕ)
    (hm : P.N_witness k - 1 ≤ m) :
    round ((P.Q m : ℝ) * (-P.xPlusPoly k)) = -P.MPlusPoly k m := by
  have hlo := (P.Q_mul_xPlusPoly_sub_MPlusPoly k m hm).1
  have hhi := P.Q_mul_xPlusPoly_sub_MPlusPoly_lt_half hk m hm
  rw [round_eq_iff]
  push_cast
  constructor <;> linarith

lemma xPlusPoly_defect_eq (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᶠ j : ℕ in atTop, P.polyDefect (P.xPlusPoly k) j = (k : ℤ) := by
  filter_upwards [eventually_ge_atTop (P.N_witness k)] with j hj
  have h1 := P.xPlusPoly_round_eq hk (j + 1) (by omega)
  have h2 := P.xPlusPoly_round_eq hk j (by omega)
  have h3 := P.xPlusPoly_round_eq hk (j - 1) (by omega)
  unfold polyDefect
  rw [h1, h2, h3, P.MPlusPoly_rec k j hj]
  ring

lemma neg_xPlusPoly_defect_eq (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᶠ j : ℕ in atTop, P.polyDefect (-P.xPlusPoly k) j = -(k : ℤ) := by
  filter_upwards [eventually_ge_atTop (P.N_witness k)] with j hj
  have h1 := P.neg_xPlusPoly_round_eq hk (j + 1) (by omega)
  have h2 := P.neg_xPlusPoly_round_eq hk j (by omega)
  have h3 := P.neg_xPlusPoly_round_eq hk (j - 1) (by omega)
  unfold polyDefect
  rw [h1, h2, h3, P.MPlusPoly_rec k j hj]
  ring

lemma xPlusPoly_eps_tendsto_zero (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (P.polyEps (P.xPlusPoly k)) atTop (nhds 0) := by
  have hbound : ∀ᶠ j : ℕ in atTop,
      |P.polyEps (P.xPlusPoly k) j| ≤ (4 * (k : ℝ) / (P.c : ℝ)) / (j : ℝ) := by
    filter_upwards [eventually_ge_atTop (max (P.N_witness k) P.J₁)] with j hj
    have hjN : P.N_witness k ≤ j := le_trans (le_max_left _ _) hj
    have hjJ₁ : P.J₁ ≤ j := le_trans (le_max_right _ _) hj
    have hr := P.xPlusPoly_round_eq hk j (by omega)
    have hnn := (P.Q_mul_xPlusPoly_sub_MPlusPoly k j (by omega)).1
    have hle := (P.Q_mul_xPlusPoly_sub_MPlusPoly k j (by omega)).2
    have heps : P.polyEps (P.xPlusPoly k) j = (P.Q j : ℝ) * P.xPlusPoly k - (P.MPlusPoly k j : ℝ) := by
      simp only [polyEps, hr]
    rw [heps, abs_of_nonneg hnn]
    have hJ₀_j : P.J₀ ≤ j := le_trans (by have := P.N_witness_ge_J₀_succ k; omega) hjN
    have hgt : (P.A j : ℝ) * (P.Q j : ℝ) < (P.Q (j + 1) : ℝ) := by
      exact_mod_cast P.poly_Q_succ_gt_A_mul hJ₀_j
    have hA : ((P.c : ℝ) / 2) * (j : ℝ) ^ P.r ≤ (P.A j : ℝ) := P.poly_A_ge_half_c hjJ₁
    have hQ : (0 : ℝ) < (P.Q j : ℝ) := by exact_mod_cast P.hQ_pos j
    have hj1 : 1 ≤ j := le_trans (by have := P.two_le_J₁; omega) hjJ₁
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hjr : (j : ℝ) ≤ (j : ℝ) ^ P.r := by
      have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      calc (j : ℝ) = (j : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (j : ℝ) ^ P.r := pow_le_pow_right₀ hj1R P.hr
    have hc_pos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
    have hgrow : ((P.c : ℝ) / 2) * (j : ℝ) * (P.Q j : ℝ) ≤ (P.Q (j + 1) : ℝ) := by
      have h1 : ((P.c : ℝ) / 2) * (j : ℝ) * (P.Q j : ℝ) ≤
          ((P.c : ℝ) / 2) * (j : ℝ) ^ P.r * (P.Q j : ℝ) := by
        have hc0 : 0 ≤ ((P.c : ℝ) / 2) := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hjr hc0) (le_of_lt hQ)
      have h2 : ((P.c : ℝ) / 2) * (j : ℝ) ^ P.r * (P.Q j : ℝ) ≤ (P.A j : ℝ) * (P.Q j : ℝ) :=
        mul_le_mul_of_nonneg_right hA (le_of_lt hQ)
      exact le_trans (le_trans h1 h2) (le_of_lt hgt)
    have hden_pos : 0 < ((P.c : ℝ) / 2) * (j : ℝ) * (P.Q j : ℝ) := by positivity
    calc (P.Q j : ℝ) * P.xPlusPoly k - (P.MPlusPoly k j : ℝ)
        ≤ (2 * (k : ℝ) * (P.Q j : ℝ)) / (P.Q (j + 1) : ℝ) := hle
      _ ≤ (2 * (k : ℝ) * (P.Q j : ℝ)) / (((P.c : ℝ) / 2) * (j : ℝ) * (P.Q j : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) hden_pos hgrow
      _ = (4 * (k : ℝ) / (P.c : ℝ)) / (j : ℝ) := by field_simp; ring
  exact FullSpectrumDiscrete.tendsto_zero_of_eventually_abs_le_div hbound

lemma neg_xPlusPoly_eps_tendsto_zero (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (P.polyEps (-P.xPlusPoly k)) atTop (nhds 0) := by
  have heq : ∀ᶠ j : ℕ in atTop, P.polyEps (-P.xPlusPoly k) j = -P.polyEps (P.xPlusPoly k) j := by
    filter_upwards [eventually_ge_atTop (P.N_witness k - 1)] with j hj
    have h1 := P.xPlusPoly_round_eq hk j hj
    have h2 := P.neg_xPlusPoly_round_eq hk j hj
    simp only [polyEps, h1, h2]
    push_cast
    ring
  have hneg : Tendsto (fun j : ℕ => -P.polyEps (P.xPlusPoly k) j) atTop (nhds 0) := by
    simpa using (P.xPlusPoly_eps_tendsto_zero hk).neg
  exact hneg.congr' (heq.mono fun _ h => h.symm)

/-- 给定最终常值缺陷 $d \in \mathbb{Z}$ 与 $u_j(x) \to 0$，必有 $j^r u_j(x) \to d / c$。 -/
theorem poly_jr_mul_eps_tendsto_of_defect_const (P : PolyRecData) (x : ℝ) (d : ℤ)
    (hu : Tendsto (P.polyEps x) atTop (nhds 0))
    (hd : ∀ᶠ j : ℕ in atTop, P.polyDefect x j = d) :
    Tendsto (fun j : ℕ => (j : ℝ) ^ P.r * P.polyEps x j) atTop (nhds ((d : ℝ) / (P.c : ℝ))) := by
  have happrox := P.poly_signed_defect_approx x hu
  have hdR : Tendsto (fun j : ℕ => (P.polyDefect x j : ℝ)) atTop (nhds (d : ℝ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hd] with j hj
    simp [hj]
  have hc_lim : Tendsto (fun j : ℕ => (P.c : ℝ) * (j : ℝ) ^ P.r * P.polyEps x j)
      atTop (nhds (d : ℝ)) := by
    have hsub := hdR.sub happrox
    have h0 : (d : ℝ) - 0 = (d : ℝ) := by ring
    rw [h0] at hsub
    refine hsub.congr' (Filter.Eventually.of_forall fun j => by ring)
  have hcne : (P.c : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt P.hc
  have hdiv := hc_lim.const_mul (1 / (P.c : ℝ))
  have hgoal : (1 / (P.c : ℝ)) * (d : ℝ) = (d : ℝ) / (P.c : ℝ) := by ring
  rw [hgoal] at hdiv
  refine hdiv.congr' (Filter.Eventually.of_forall fun j => ?_)
  field_simp

theorem polyApprExponent_xPlusPoly (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    P.polyApprExponent (P.xPlusPoly k) = ENNReal.ofReal ((k : ℝ) / (P.c : ℝ)) := by
  have hjr := P.poly_jr_mul_eps_tendsto_of_defect_const (P.xPlusPoly k) (k : ℤ)
    (P.xPlusPoly_eps_tendsto_zero hk) (P.xPlusPoly_defect_eq hk)
  have habs : Tendsto (fun j : ℕ => P.polyWeightedSeq (P.r : ℝ) (P.xPlusPoly k) j)
      atTop (nhds ((k : ℝ) / (P.c : ℝ))) := by
    have h1 := hjr.abs
    have hlim : |((k : ℤ) : ℝ) / (P.c : ℝ)| = (k : ℝ) / (P.c : ℝ) := by
      push_cast; exact abs_of_nonneg (by positivity)
    rw [hlim] at h1
    refine h1.congr' (Filter.Eventually.of_forall fun j => ?_)
    dsimp [polyWeightedSeq]
    rw [Real.rpow_natCast, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg j : 0 ≤ (j : ℝ)) _)]
    rfl
  exact (ENNReal.tendsto_ofReal habs).limsup_eq

/-- **Theorem `thm:general-rec`(ii) 第一部分**：一切开区间 $(k/c, (k+1)/c)$ 均为 $\Lambda^{(r,c,d)}$ 的空谱隙。 -/
theorem poly_spectral_gap_open_interval (P : PolyRecData) (k : ℕ) {L : ℝ}
    (hkL : (k : ℝ) / (P.c : ℝ) < L) (hLk1 : L < ((k : ℝ) + 1) / (P.c : ℝ)) (x : ℝ) :
    P.polyApprExponent x ≠ ENNReal.ofReal L := by
  intro hEq
  have hcpos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
  have hLpos : 0 < L := lt_of_le_of_lt (by positivity) hkL
  have hfin : P.polyApprExponent x ≠ ⊤ := by rw [hEq]; exact ENNReal.ofReal_ne_top
  have hu := P.polyEps_tendsto_zero_of_apprExponent_ne_top hfin
  have happrox : Tendsto (fun j : ℕ => (((|P.polyDefect x j| : ℤ) : ℝ) -
      (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j)) atTop (nhds 0) := by
    refine (P.poly_abs_defect_approx x hu).congr' (Filter.Eventually.of_forall fun j => ?_)
    simp only [polyWeightedSeq, Int.cast_abs, Real.rpow_natCast]
    ring
  set B := ((P.c : ℝ) * L + ((k : ℝ) + 1)) / 2
  set A := ((k : ℝ) + (P.c : ℝ) * L) / 2
  have hLB : L < B / (P.c : ℝ) := by
    dsimp [B]
    have : (P.c : ℝ) * L < (k : ℝ) + 1 := (lt_div_iff₀' hcpos).mp hLk1
    rw [lt_div_iff₀' hcpos]
    linarith
  have hAL : A / (P.c : ℝ) < L := by
    dsimp [A]
    have : (k : ℝ) < (P.c : ℝ) * L := (div_lt_iff₀' hcpos).mp hkL
    rw [div_lt_iff₀' hcpos]
    linarith
  have hBpos : 0 < B / (P.c : ℝ) := lt_trans hLpos hLB
  have hApos : 0 < A / (P.c : ℝ) := by
    dsimp [A]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have : 0 < (P.c : ℝ) * L := mul_pos hcpos hLpos
    positivity
  have hltB : P.polyApprExponent x < ENNReal.ofReal (B / (P.c : ℝ)) := by
    rw [hEq]
    exact (ENNReal.ofReal_lt_ofReal_iff hBpos).mpr hLB
  have hevB : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (P.polyWeightedSeq (P.r : ℝ) x j) < ENNReal.ofReal (B / (P.c : ℝ)) :=
    eventually_lt_of_limsup_lt hltB
  have hyB : ∀ᶠ j : ℕ in atTop, (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j ≤ B := by
    filter_upwards [hevB] with j hj
    have h1 : P.polyWeightedSeq (P.r : ℝ) x j < B / (P.c : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff hBpos).mp hj
    have := (lt_div_iff₀' hcpos).mp h1
    linarith
  have hkA : ((k : ℤ) : ℝ) < A := by
    dsimp [A]
    have : (k : ℝ) < (P.c : ℝ) * L := (div_lt_iff₀' hcpos).mp hkL
    simp only [Int.cast_natCast]; linarith
  have hBk1 : B < ((k : ℤ) : ℝ) + 1 := by
    dsimp [B]
    have : (P.c : ℝ) * L < (k : ℝ) + 1 := (lt_div_iff₀' hcpos).mp hLk1
    simp only [Int.cast_natCast]; linarith
  have hyA : ∀ᶠ j : ℕ in atTop, (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j ≤ A :=
    FullSpectrumDiscrete.eventually_le_of_int_approx_in_gap happrox (k : ℤ) hkA hBk1 hyB
  have hevA : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (P.polyWeightedSeq (P.r : ℝ) x j) ≤ ENNReal.ofReal (A / (P.c : ℝ)) := by
    filter_upwards [hyA] with j hj
    apply ENNReal.ofReal_le_ofReal
    exact (le_div_iff₀' hcpos).mpr hj
  have hleA : P.polyApprExponent x ≤ ENNReal.ofReal (A / (P.c : ℝ)) :=
    limsup_le_of_le (by isBoundedDefault) hevA
  rw [hEq] at hleA
  have hltA : ENNReal.ofReal (A / (P.c : ℝ)) < ENNReal.ofReal L :=
    (ENNReal.ofReal_lt_ofReal_iff hLpos).mpr hAL
  exact not_lt_of_ge hleA hltA

lemma poly_eventually_abs_defect_le_of_apprExponent_le (P : PolyRecData) (k : ℕ) {t : ℝ}
    (ht : t < ((k : ℝ) + 1) / (P.c : ℝ)) (x : ℝ)
    (hx : P.polyApprExponent x ≤ ENNReal.ofReal t) :
    ∀ᶠ j : ℕ in atTop, |P.polyDefect x j| ≤ (k : ℤ) := by
  have hcpos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
  have hfin : P.polyApprExponent x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hx ENNReal.ofReal_lt_top)
  have hu := P.polyEps_tendsto_zero_of_apprExponent_ne_top hfin
  have happrox : Tendsto (fun j : ℕ => (((|P.polyDefect x j| : ℤ) : ℝ) -
      (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j)) atTop (nhds 0) := by
    refine (P.poly_abs_defect_approx x hu).congr' (Filter.Eventually.of_forall fun j => ?_)
    simp only [polyWeightedSeq, Int.cast_abs, Real.rpow_natCast]
    ring
  set B := (max ((P.c : ℝ) * t) (k : ℝ) + ((k : ℝ) + 1)) / 2
  have hct_lt : (P.c : ℝ) * t < (k : ℝ) + 1 := (lt_div_iff₀' hcpos).mp ht
  have hBk1 : B < ((k : ℤ) : ℝ) + 1 := by
    dsimp [B]
    have : max ((P.c : ℝ) * t) (k : ℝ) < (k : ℝ) + 1 := max_lt hct_lt (by linarith)
    simp only [Int.cast_natCast]; linarith
  have htB : t < B / (P.c : ℝ) := by
    dsimp [B]
    have h1 : (P.c : ℝ) * t ≤ max ((P.c : ℝ) * t) (k : ℝ) := le_max_left _ _
    have h2 : max ((P.c : ℝ) * t) (k : ℝ) < (k : ℝ) + 1 := max_lt hct_lt (by linarith)
    rw [lt_div_iff₀' hcpos]
    linarith
  have hBpos : 0 < B / (P.c : ℝ) := by
    dsimp [B]
    have : (k : ℝ) ≤ max ((P.c : ℝ) * t) (k : ℝ) := le_max_right _ _
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    positivity
  have hltB : P.polyApprExponent x < ENNReal.ofReal (B / (P.c : ℝ)) :=
    lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff hBpos).mpr htB)
  have hevB : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (P.polyWeightedSeq (P.r : ℝ) x j) < ENNReal.ofReal (B / (P.c : ℝ)) :=
    eventually_lt_of_limsup_lt hltB
  have hyB : ∀ᶠ j : ℕ in atTop, (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j ≤ B := by
    filter_upwards [hevB] with j hj
    have h1 : P.polyWeightedSeq (P.r : ℝ) x j < B / (P.c : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff hBpos).mp hj
    exact le_of_lt ((lt_div_iff₀' hcpos).mp h1)
  exact FullSpectrumDiscrete.eventually_int_le_of_eventually_le_lt_succ happrox (k : ℤ) hBk1 hyB

/-- **Theorem `thm:general-rec`(ii) 第二部分**：水平集在每个谱隙 $[k/c, (k+1)/c)$ 上恒定，
    并等价于 $u_j(x) \to 0 \land \forall^\infty j,\, |d_j(x)| \le k$。 -/
theorem poly_levelSet_eq_on_gap (P : PolyRecData) (k : ℕ) {t : ℝ}
    (hkt : (k : ℝ) / (P.c : ℝ) ≤ t) (ht : t < ((k : ℝ) + 1) / (P.c : ℝ)) :
    P.polyLevelSet (ENNReal.ofReal t) = P.polyLevelSet (ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))) ∧
    P.polyLevelSet (ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))) =
      {x : ℝ | Tendsto (P.polyEps x) atTop (nhds 0) ∧
        ∀ᶠ j : ℕ in atTop, |P.polyDefect x j| ≤ (k : ℤ)} := by
  have hcpos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
  have hchar : P.polyLevelSet (ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))) =
      {x : ℝ | Tendsto (P.polyEps x) atTop (nhds 0) ∧
        ∀ᶠ j : ℕ in atTop, |P.polyDefect x j| ≤ (k : ℤ)} := by
    ext x
    simp only [polyLevelSet, Set.mem_ofPred_eq]
    constructor
    · intro hx
      have hfin : P.polyApprExponent x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hx ENNReal.ofReal_lt_top)
      have hlt_k : (k : ℝ) / (P.c : ℝ) < ((k : ℝ) + 1) / (P.c : ℝ) :=
        div_lt_div_of_pos_right (by linarith) hcpos
      exact ⟨P.polyEps_tendsto_zero_of_apprExponent_ne_top hfin,
        P.poly_eventually_abs_defect_le_of_apprExponent_le k hlt_k x hx⟩
    · rintro ⟨hu, hdef⟩
      have happrox := P.poly_abs_defect_approx x hu
      have hneg : Tendsto (fun j : ℕ =>
          (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j - |(P.polyDefect x j : ℝ)|)
          atTop (nhds 0) := by
        have h1 := happrox.neg
        rw [neg_zero] at h1
        refine h1.congr' (Filter.Eventually.of_forall fun j => ?_)
        dsimp [polyWeightedSeq]
        rw [Real.rpow_natCast]
        ring
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
      have hev : ∀ᶠ j : ℕ in atTop,
          (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j - |(P.polyDefect x j : ℝ)| <
            (P.c : ℝ) * (ε : ℝ) :=
        hneg.eventually (Iio_mem_nhds (mul_pos hcpos hεR))
      have hev2 : ∀ᶠ j : ℕ in atTop,
          ENNReal.ofReal (P.polyWeightedSeq (P.r : ℝ) x j) ≤
            ENNReal.ofReal ((k : ℝ) / (P.c : ℝ)) + (ε : ℝ≥0∞) := by
        filter_upwards [hdef, hev] with j hj1 hj2
        have hj1R : |(P.polyDefect x j : ℝ)| ≤ (k : ℝ) := by
          rw [← Int.cast_abs]; exact_mod_cast hj1
        have hle : P.polyWeightedSeq (P.r : ℝ) x j ≤ (k : ℝ) / (P.c : ℝ) + (ε : ℝ) := by
          have hmul : (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j ≤
              (k : ℝ) + (P.c : ℝ) * (ε : ℝ) := by linarith
          have hdiv := div_le_div_of_nonneg_right hmul (le_of_lt hcpos)
          have heq1 : (P.c : ℝ) * P.polyWeightedSeq (P.r : ℝ) x j / (P.c : ℝ) =
              P.polyWeightedSeq (P.r : ℝ) x j := by field_simp
          have heq2 : ((k : ℝ) + (P.c : ℝ) * (ε : ℝ)) / (P.c : ℝ) =
              (k : ℝ) / (P.c : ℝ) + (ε : ℝ) := by field_simp
          linarith
        calc ENNReal.ofReal (P.polyWeightedSeq (P.r : ℝ) x j)
            ≤ ENNReal.ofReal ((k : ℝ) / (P.c : ℝ) + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hle
          _ = ENNReal.ofReal ((k : ℝ) / (P.c : ℝ)) + ENNReal.ofReal (ε : ℝ) :=
              ENNReal.ofReal_add (by positivity) (by positivity)
          _ = ENNReal.ofReal ((k : ℝ) / (P.c : ℝ)) + (ε : ℝ≥0∞) := by simp
      exact limsup_le_of_le (by isBoundedDefault) hev2
  refine ⟨?_, hchar⟩
  ext x
  simp only [polyLevelSet, Set.mem_ofPred_eq]
  constructor
  · intro hx
    have hfin : P.polyApprExponent x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hx ENNReal.ofReal_lt_top)
    have hmem : x ∈ {y : ℝ | Tendsto (P.polyEps y) atTop (nhds 0) ∧
        ∀ᶠ j : ℕ in atTop, |P.polyDefect y j| ≤ (k : ℤ)} :=
      ⟨P.polyEps_tendsto_zero_of_apprExponent_ne_top hfin,
        P.poly_eventually_abs_defect_le_of_apprExponent_le k ht x hx⟩
    rw [← hchar] at hmem
    exact hmem
  · intro hx
    exact le_trans hx (ENNReal.ofReal_le_ofReal hkt)

/-- **Theorem `thm:general-rec`(ii) 第三部分**：$t < 1/c$ 时子水平集坍缩为 $L^{(r,c,d)}$。 -/
theorem poly_levelSet_below_eq_lattice (P : PolyRecData) {t : ℝ≥0∞}
    (ht : t < ENNReal.ofReal (1 / (P.c : ℝ))) :
    P.polyLevelSet t = P.latticePoly := by
  have hcpos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
  have hfin : t ≠ ⊤ := ne_of_lt (lt_trans ht ENNReal.ofReal_lt_top)
  have htR : t.toReal < 1 / (P.c : ℝ) := by
    have h1 : ENNReal.ofReal t.toReal < ENNReal.ofReal (1 / (P.c : ℝ)) := by
      rwa [ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h1
  have h0_eq : P.polyLevelSet (ENNReal.ofReal ((0 : ℕ) / (P.c : ℝ))) = P.latticePoly := by
    ext x
    simp only [polyLevelSet, Set.mem_ofPred_eq, Nat.cast_zero, zero_div, ENNReal.ofReal_zero,
      le_zero_iff]
    exact P.polyApprExponent_eq_zero_iff_mem_latticePoly x
  have hgap := (P.poly_levelSet_eq_on_gap 0 (t := t.toReal) (by simp [ENNReal.toReal_nonneg])
    (by simpa using htR)).1
  rw [ENNReal.ofReal_toReal hfin, h0_eq] at hgap
  exact hgap

/-! ## 第六部分：`thm:poly-gauge-trichotomy(iii)`（一般多项式递推有符号精确极限陪集坍缩） -/

/-- 一般多项式递推有符号精确极限集 $E_{\mathrm{lim}}^{(r,c,d),\mathrm{signed}}(t)$。 -/
def polySignedExactLimitSet (P : PolyRecData) (t : ℝ) : Set ℝ :=
  {x : ℝ | Tendsto (fun j : ℕ => (j : ℝ) ^ P.r * P.polyEps x j) atTop (nhds t)}

/-- **Theorem `thm:poly-gauge-trichotomy(iii)` 数字刻画**：
    $j^r u_j(x) \to d / c \iff u_j(x) \to 0 \land \forall^\infty j,\, d_j(x) = d$。 -/
theorem poly_signed_exact_limit_iff_defect_const (P : PolyRecData) (x : ℝ) (d : ℤ) :
    x ∈ P.polySignedExactLimitSet ((d : ℝ) / (P.c : ℝ)) ↔
      Tendsto (P.polyEps x) atTop (nhds 0) ∧ ∀ᶠ j : ℕ in atTop, P.polyDefect x j = d := by
  have hcpos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
  constructor
  · intro hx
    have hu : Tendsto (P.polyEps x) atTop (nhds 0) := by
      have habs : Tendsto (fun j : ℕ => |(j : ℝ) ^ P.r * P.polyEps x j|)
          atTop (nhds |(d : ℝ) / (P.c : ℝ)|) := hx.abs
      have hev : ∀ᶠ j : ℕ in atTop,
          |(j : ℝ) ^ P.r * P.polyEps x j| < |(d : ℝ) / (P.c : ℝ)| + 1 :=
        habs.eventually (Iio_mem_nhds (by linarith [abs_nonneg ((d : ℝ) / (P.c : ℝ))]))
      have hbound : ∀ᶠ j : ℕ in atTop,
          |P.polyEps x j| ≤ (|(d : ℝ) / (P.c : ℝ)| + 1) / (j : ℝ) := by
        filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
        have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
        have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
        have hjr : (j : ℝ) ≤ (j : ℝ) ^ P.r := by
          calc (j : ℝ) = (j : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (j : ℝ) ^ P.r := pow_le_pow_right₀ hj1R P.hr
        have hmul1 : |(j : ℝ) ^ P.r * P.polyEps x j| = (j : ℝ) ^ P.r * |P.polyEps x j| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg j) _)]
        have hmul2 : (j : ℝ) * |P.polyEps x j| ≤ (j : ℝ) ^ P.r * |P.polyEps x j| :=
          mul_le_mul_of_nonneg_right hjr (abs_nonneg _)
        exact (le_div_iff₀ hjpos).mpr (by linarith [hmul1, hmul2, hj])
      exact FullSpectrumDiscrete.tendsto_zero_of_eventually_abs_le_div hbound
    have happrox := P.poly_signed_defect_approx x hu
    have hclim : Tendsto (fun j : ℕ => (P.c : ℝ) * (j : ℝ) ^ P.r * P.polyEps x j)
        atTop (nhds (d : ℝ)) := by
      have h1 := hx.const_mul (P.c : ℝ)
      have heq : (P.c : ℝ) * ((d : ℝ) / (P.c : ℝ)) = (d : ℝ) := by field_simp
      rw [heq] at h1
      refine h1.congr' (Filter.Eventually.of_forall fun j => by ring)
    exact ⟨hu, FullSpectrumDiscrete.eventually_eq_int_of_tendsto happrox d hclim⟩
  · rintro ⟨hu, hD⟩
    exact P.poly_jr_mul_eps_tendsto_of_defect_const x d hu hD

lemma poly_eps_tendsto_zero_of_mem_signedExactLimitSet (P : PolyRecData) {x t : ℝ}
    (hx : x ∈ P.polySignedExactLimitSet t) :
    Tendsto (P.polyEps x) atTop (nhds 0) := by
  have habs : Tendsto (fun j : ℕ => |(j : ℝ) ^ P.r * P.polyEps x j|) atTop (nhds |t|) := hx.abs
  have hev : ∀ᶠ j : ℕ in atTop, |(j : ℝ) ^ P.r * P.polyEps x j| < |t| + 1 :=
    habs.eventually (Iio_mem_nhds (by linarith [abs_nonneg t]))
  have hbound : ∀ᶠ j : ℕ in atTop, |P.polyEps x j| ≤ (|t| + 1) / (j : ℝ) := by
    filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hjr : (j : ℝ) ≤ (j : ℝ) ^ P.r := by
      calc (j : ℝ) = (j : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (j : ℝ) ^ P.r := pow_le_pow_right₀ hj1R P.hr
    have hmul1 : |(j : ℝ) ^ P.r * P.polyEps x j| = (j : ℝ) ^ P.r * |P.polyEps x j| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg j) _)]
    have hmul2 : (j : ℝ) * |P.polyEps x j| ≤ (j : ℝ) ^ P.r * |P.polyEps x j| :=
      mul_le_mul_of_nonneg_right hjr (abs_nonneg _)
    exact (le_div_iff₀ hjpos).mpr (by linarith [hmul1, hmul2, hj])
  exact FullSpectrumDiscrete.tendsto_zero_of_eventually_abs_le_div hbound

theorem xPlusPoly_mem_signedExactLimitSet (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    P.xPlusPoly k ∈ P.polySignedExactLimitSet ((k : ℝ) / (P.c : ℝ)) :=
  (P.poly_signed_exact_limit_iff_defect_const (P.xPlusPoly k) (k : ℤ)).mpr
    ⟨P.xPlusPoly_eps_tendsto_zero hk, P.xPlusPoly_defect_eq hk⟩

theorem neg_xPlusPoly_mem_signedExactLimitSet (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    -P.xPlusPoly k ∈ P.polySignedExactLimitSet (-((k : ℝ) / (P.c : ℝ))) := by
  have h := (P.poly_signed_exact_limit_iff_defect_const (-P.xPlusPoly k) (-(k : ℤ))).mpr
    ⟨P.neg_xPlusPoly_eps_tendsto_zero hk, P.neg_xPlusPoly_defect_eq hk⟩
  simp only [polySignedExactLimitSet, Int.cast_neg, Int.cast_natCast, neg_div] at h ⊢
  exact h

theorem poly_sub_mem_latticePoly_of_same_signed_limit (P : PolyRecData) {x y t : ℝ}
    (hx : x ∈ P.polySignedExactLimitSet t)
    (hy : y ∈ P.polySignedExactLimitSet t) :
    x - y ∈ P.latticePoly := by
  have hdiff : Tendsto (fun j : ℕ => (j : ℝ) ^ P.r * (P.polyEps x j - P.polyEps y j))
      atTop (nhds 0) := by
    have hsub := hx.sub hy
    have h0 : t - t = 0 := by ring
    rw [h0] at hsub
    refine hsub.congr' (Filter.Eventually.of_forall fun j => by ring)
  have habs_diff : Tendsto (fun j : ℕ => (j : ℝ) ^ P.r * |P.polyEps x j - P.polyEps y j|)
      atTop (nhds 0) := by
    have h1 : Tendsto (fun j : ℕ => |(j : ℝ) ^ P.r * (P.polyEps x j - P.polyEps y j)|)
        atTop (nhds 0) := by simpa using hdiff.abs
    refine h1.congr' (Filter.Eventually.of_forall fun j => ?_)
    rw [abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg j) _)]
  have hdist_le : ∀ j : ℕ,
      distToNearestInt ((P.Q j : ℝ) * (x - y)) ≤ |P.polyEps x j - P.polyEps y j| := by
    intro j
    set K : ℤ := round ((P.Q j : ℝ) * x) - round ((P.Q j : ℝ) * y)
    have hId : (P.Q j : ℝ) * (x - y) - (K : ℝ) = P.polyEps x j - P.polyEps y j := by
      simp only [K, polyEps]; push_cast; ring
    rw [← hId]
    exact distToNearestInt_le ((P.Q j : ℝ) * (x - y)) K
  have htend0 : Tendsto (P.polyWeightedSeq (P.r : ℝ) (x - y)) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds habs_diff
      (Filter.Eventually.of_forall (P.polyWeightedSeq_nonneg (P.r : ℝ) (x - y))) ?_
    filter_upwards with j
    unfold polyWeightedSeq
    rw [Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left (hdist_le j) (pow_nonneg (Nat.cast_nonneg j) _)
  have h0 : P.polyApprExponent (x - y) = 0 :=
    (P.polyWeightedExponent_eq_zero_iff (P.r : ℝ) (x - y)).mpr htend0
  exact (P.polyApprExponent_eq_zero_iff_mem_latticePoly (x - y)).mp h0

theorem poly_add_latticePoly_mem_signedExactLimitSet (P : PolyRecData) {x t z : ℝ}
    (hx : x ∈ P.polySignedExactLimitSet t) (hz : z ∈ P.latticePoly) :
    x + z ∈ P.polySignedExactLimitSet t := by
  have hεx := P.poly_eps_tendsto_zero_of_mem_signedExactLimitSet hx
  have hz_exp0 : P.polyApprExponent z = 0 :=
    P.polyWeightedExponent_eq_zero_of_mem_latticePoly hz (P.r : ℝ)
  have hεz := P.polyEps_tendsto_zero_of_apprExponent_ne_top (by rw [hz_exp0]; exact ENNReal.zero_ne_top)
  have hsum_eps : Tendsto (fun j : ℕ => P.polyEps x j + P.polyEps z j) atTop (nhds 0) := by
    simpa using hεx.add hεz
  have hlt_half : ∀ᶠ j : ℕ in atTop, |P.polyEps x j + P.polyEps z j| < 1 / 2 :=
    (by simpa using hsum_eps.abs :
      Tendsto (fun j : ℕ => |P.polyEps x j + P.polyEps z j|) atTop (nhds 0)).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have heps_add : ∀ᶠ j : ℕ in atTop,
      P.polyEps (x + z) j = P.polyEps x j + P.polyEps z j := by
    filter_upwards [hlt_half] with j hj
    have hround : round ((P.Q j : ℝ) * (x + z)) =
        round ((P.Q j : ℝ) * x) + round ((P.Q j : ℝ) * z) := by
      rw [round_eq_iff]
      have hid : (P.Q j : ℝ) * (x + z) =
          ((round ((P.Q j : ℝ) * x) + round ((P.Q j : ℝ) * z) : ℤ) : ℝ) +
            (P.polyEps x j + P.polyEps z j) := by
        simp only [polyEps]; push_cast; ring
      have habs := abs_lt.mp hj
      rw [hid]
      constructor <;> linarith
    simp only [polyEps, hround]
    push_cast; ring
  have hz_seq : Tendsto (P.polyWeightedSeq (P.r : ℝ) z) atTop (nhds 0) :=
    (P.polyWeightedExponent_eq_zero_iff (P.r : ℝ) z).mp hz_exp0
  have hj_z : Tendsto (fun j : ℕ => (j : ℝ) ^ P.r * P.polyEps z j) atTop (nhds 0) := by
    have hneg : Tendsto (fun j : ℕ => -P.polyWeightedSeq (P.r : ℝ) z j) atTop (nhds 0) := by
      simpa using hz_seq.neg
    have hseq' : Tendsto (fun j : ℕ => (j : ℝ) ^ P.r * |P.polyEps z j|) atTop (nhds 0) := by
      refine hz_seq.congr (fun j => ?_)
      simp [polyWeightedSeq, Real.rpow_natCast, abs_polyEps_eq_dist]
    have hneg' : Tendsto (fun j : ℕ => -((j : ℝ) ^ P.r * |P.polyEps z j|)) atTop (nhds 0) := by
      simpa using hseq'.neg
    have hlo : ∀ᶠ j : ℕ in atTop,
        -((j : ℝ) ^ P.r * |P.polyEps z j|) ≤ (j : ℝ) ^ P.r * P.polyEps z j := by
      filter_upwards with j
      have h1 := (abs_le.mp (le_refl |P.polyEps z j|)).1
      nlinarith [pow_nonneg (Nat.cast_nonneg j : 0 ≤ (j : ℝ)) P.r]
    have hhi : ∀ᶠ j : ℕ in atTop,
        (j : ℝ) ^ P.r * P.polyEps z j ≤ (j : ℝ) ^ P.r * |P.polyEps z j| := by
      filter_upwards with j
      have h1 := (abs_le.mp (le_refl |P.polyEps z j|)).2
      nlinarith [pow_nonneg (Nat.cast_nonneg j : 0 ≤ (j : ℝ)) P.r]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg' hseq' hlo hhi
  have hlim : Tendsto (fun j : ℕ => (j : ℝ) ^ P.r * (P.polyEps x j + P.polyEps z j))
      atTop (nhds t) := by
    simpa [mul_add] using hx.add hj_z
  exact hlim.congr' (heps_add.mono fun j hj => by simp [hj])

/-- **Theorem `thm:poly-gauge-trichotomy`(iii) 完整陪集坍缩**：
    对一切 $k \ge 1$，$E_{\mathrm{lim}}^{(r,c,d),\pm}(k/c) = \pm x_k^+ + L^{(r,c,d)}$，
    可数、Hausdorff 维数为 $0$，且对任意非原子 Hausdorff 规范测度为 $0$。 -/
theorem poly_trichotomy_part_iii_complete (P : PolyRecData) {k : ℕ} (hk : 1 ≤ k) :
    P.polySignedExactLimitSet ((k : ℝ) / (P.c : ℝ)) =
      (fun z : ℝ => P.xPlusPoly k + z) '' P.latticePoly ∧
    P.polySignedExactLimitSet (-((k : ℝ) / (P.c : ℝ))) =
      (fun z : ℝ => -P.xPlusPoly k + z) '' P.latticePoly ∧
    (P.polySignedExactLimitSet ((k : ℝ) / (P.c : ℝ))).Countable ∧
    (P.polySignedExactLimitSet (-((k : ℝ) / (P.c : ℝ)))).Countable ∧
    dimH (P.polySignedExactLimitSet ((k : ℝ) / (P.c : ℝ))) = 0 ∧
    dimH (P.polySignedExactLimitSet (-((k : ℝ) / (P.c : ℝ)))) = 0 ∧
    (∀ m : ℝ≥0∞ → ℝ≥0∞, Tendsto m (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Measure.mkMetric m (P.polySignedExactLimitSet ((k : ℝ) / (P.c : ℝ))) = 0 ∧
      Measure.mkMetric m (P.polySignedExactLimitSet (-((k : ℝ) / (P.c : ℝ)))) = 0) := by
  have hpos : P.polySignedExactLimitSet ((k : ℝ) / (P.c : ℝ)) =
      (fun z : ℝ => P.xPlusPoly k + z) '' P.latticePoly := by
    ext y
    constructor
    · intro hy
      exact ⟨y - P.xPlusPoly k, P.poly_sub_mem_latticePoly_of_same_signed_limit hy
        (P.xPlusPoly_mem_signedExactLimitSet hk), by ring⟩
    · rintro ⟨z, hz, rfl⟩
      exact P.poly_add_latticePoly_mem_signedExactLimitSet (P.xPlusPoly_mem_signedExactLimitSet hk) hz
  have hneg : P.polySignedExactLimitSet (-((k : ℝ) / (P.c : ℝ))) =
      (fun z : ℝ => -P.xPlusPoly k + z) '' P.latticePoly := by
    ext y
    constructor
    · intro hy
      exact ⟨y - (-P.xPlusPoly k), P.poly_sub_mem_latticePoly_of_same_signed_limit hy
        (P.neg_xPlusPoly_mem_signedExactLimitSet hk), by ring⟩
    · rintro ⟨z, hz, rfl⟩
      exact P.poly_add_latticePoly_mem_signedExactLimitSet
        (P.neg_xPlusPoly_mem_signedExactLimitSet hk) hz
  have hc_pos : (P.polySignedExactLimitSet ((k : ℝ) / (P.c : ℝ))).Countable := by
    rw [hpos]; exact P.latticePoly_countable.image _
  have hc_neg : (P.polySignedExactLimitSet (-((k : ℝ) / (P.c : ℝ)))).Countable := by
    rw [hneg]; exact P.latticePoly_countable.image _
  refine ⟨hpos, hneg, hc_pos, hc_neg, hc_pos.dimH_zero, hc_neg.dimH_zero, ?_⟩
  intro m hm0
  exact ⟨mkMetric_countable_zero m hm0 hc_pos, mkMetric_countable_zero m hm0 hc_neg⟩

/-! ## 第七部分：`thm:poly-phase-transition`(i), (iii)（临界维数零与超临界坍缩） -/

/-- **Theorem `thm:poly-phase-transition`(iii)（超临界坍缩 $\alpha > r$）**：
    对一切 $\alpha > r$ 与有限 $t \ge 0$，$\{x : \Lambda_\alpha^{(r,c,d)}(x) \le t\} = L^{(r,c,d)}$
    （可数、维数 $0$）；而对 $t < 0$，无任何点满足 $\Lambda_\alpha^{(r,c,d)}(x) \le t$。 -/
theorem poly_supercritical_levelSet_eq_lattice (P : PolyRecData) {α t : ℝ}
    (hα : (P.r : ℝ) < α) (ht : 0 ≤ t) :
    {x : ℝ | P.polyWeightedExponent α x ≤ ENNReal.ofReal t} = P.latticePoly := by
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hx
    have hlt : P.polyWeightedExponent α x < ENNReal.ofReal (t + 1) :=
      lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
    have hev : ∀ᶠ j : ℕ in atTop,
        ENNReal.ofReal (P.polyWeightedSeq α x j) < ENNReal.ofReal (t + 1) :=
      eventually_lt_of_limsup_lt hlt
    have hbound : ∀ᶠ j : ℕ in atTop,
        P.polyWeightedSeq (P.r : ℝ) x j ≤ (t + 1) * (j : ℝ) ^ ((P.r : ℝ) - α) := by
      filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
      have h1 : P.polyWeightedSeq α x j ≤ t + 1 :=
        le_of_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hj)
      have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
      have hrpow_pos : 0 < (j : ℝ) ^ α := Real.rpow_pos_of_pos hjpos α
      have hsub : (j : ℝ) ^ (P.r : ℝ) = (j : ℝ) ^ ((P.r : ℝ) - α) * (j : ℝ) ^ α := by
        rw [← Real.rpow_add hjpos]; congr 1; ring
      unfold polyWeightedSeq at h1 ⊢
      calc (j : ℝ) ^ (P.r : ℝ) * distToNearestInt ((P.Q j : ℝ) * x)
          = (j : ℝ) ^ ((P.r : ℝ) - α) * ((j : ℝ) ^ α * distToNearestInt ((P.Q j : ℝ) * x)) := by
              rw [hsub, mul_assoc]
        _ ≤ (j : ℝ) ^ ((P.r : ℝ) - α) * (t + 1) :=
              mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (Nat.cast_nonneg j) _)
        _ = (t + 1) * (j : ℝ) ^ ((P.r : ℝ) - α) := by ring
    have hneg_exp : (P.r : ℝ) - α < 0 := by linarith
    have hlim_rhs : Tendsto (fun j : ℕ => (t + 1) * (j : ℝ) ^ ((P.r : ℝ) - α)) atTop (nhds 0) := by
      have hpow : Tendsto (fun j : ℕ => (j : ℝ) ^ ((P.r : ℝ) - α)) atTop (nhds 0) :=
        ((tendsto_rpow_neg_atTop (by linarith : 0 < α - (P.r : ℝ))).comp
          tendsto_natCast_atTop_atTop).congr (fun j => by dsimp; rw [neg_sub])
      simpa using hpow.const_mul (t + 1)
    have hseq0 : Tendsto (P.polyWeightedSeq (P.r : ℝ) x) atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_rhs
        (Filter.Eventually.of_forall (P.polyWeightedSeq_nonneg (P.r : ℝ) x)) hbound
    have h0 : P.polyApprExponent x = 0 :=
      (P.polyWeightedExponent_eq_zero_iff (P.r : ℝ) x).mpr hseq0
    exact (P.polyApprExponent_eq_zero_iff_mem_latticePoly x).mp h0
  · intro hx
    rw [P.polyWeightedExponent_eq_zero_of_mem_latticePoly hx α]
    exact bot_le

theorem poly_supercritical_dimH_zero (P : PolyRecData) {α t : ℝ}
    (hα : (P.r : ℝ) < α) (ht : 0 ≤ t) :
    ({x : ℝ | P.polyWeightedExponent α x ≤ ENNReal.ofReal t}).Countable ∧
    dimH {x : ℝ | P.polyWeightedExponent α x ≤ ENNReal.ofReal t} = 0 := by
  rw [P.poly_supercritical_levelSet_eq_lattice hα ht]
  exact ⟨P.latticePoly_countable, P.latticePoly_countable.dimH_zero⟩

theorem poly_supercritical_empty_neg (P : PolyRecData) (α : ℝ) {t : ℝ} (ht : t < 0) :
    {x : ℝ | P.polyWeightedExponent α x ≠ ⊤ ∧ (P.polyWeightedExponent α x).toReal ≤ t} = ∅ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, hy⟩
  linarith [ENNReal.toReal_nonneg (a := P.polyWeightedExponent α x)]

/-! ### 临界权 $\alpha = r$ 的 `dimH {Λ ≤ t} = 0`、Lebesgue 零测度与全谱 $\infty$ 点存在性 (`thm:poly-phase-transition`(i)) -/

def polyRad (P : PolyRecData) (t : ℝ) (j : ℕ) : ℝ :=
  t / ((j : ℝ) ^ P.r * (P.Q j : ℝ))

lemma polyRad_nonneg (P : PolyRecData) {t : ℝ} (ht : 0 ≤ t) (j : ℕ) : 0 ≤ P.polyRad t j := by
  unfold polyRad
  have hQ : (0 : ℝ) < (P.Q j : ℝ) := by exact_mod_cast P.hQ_pos j
  positivity

def polyInterv (P : PolyRecData) (t : ℝ) (j k : ℕ) : Set ℝ :=
  Set.Icc ((k : ℝ) / (P.Q j : ℝ) - P.polyRad t j) ((k : ℝ) / (P.Q j : ℝ) + P.polyRad t j)

lemma ediam_polyInterv_le (P : PolyRecData) {t : ℝ} (_ht : 0 ≤ t) (j k : ℕ) :
    Metric.ediam (P.polyInterv t j k) ≤ ENNReal.ofReal (2 * P.polyRad t j) := by
  have hsub : ((k : ℝ) / (P.Q j : ℝ) + P.polyRad t j) -
      ((k : ℝ) / (P.Q j : ℝ) - P.polyRad t j) = 2 * P.polyRad t j := by ring
  rw [polyInterv, Real.ediam_Icc, hsub]

def polyBranchB (P : PolyRecData) (t : ℝ) : ℕ :=
  Nat.floor (2 * t * ((P.c : ℝ) + |(P.d : ℝ)| + 2)) + 1

lemma polyBranchB_pos (P : PolyRecData) (t : ℝ) : 0 < P.polyBranchB t := Nat.succ_pos _

def polyBranchSet (P : PolyRecData) (t : ℝ) (j k : ℕ) : Finset ℕ :=
  (Finset.range ((P.Q (j + 1)).toNat + 1)).filter (fun k' =>
    |(k : ℝ) / (P.Q j : ℝ) - (k' : ℝ) / (P.Q (j + 1) : ℝ)| ≤
      P.polyRad t j + P.polyRad t (j + 1))

def polySurvSet (P : PolyRecData) (t : ℝ) (J : ℕ) : ℕ → Finset ℕ
  | 0 => Finset.range ((P.Q J).toNat + 1)
  | n + 1 => (P.polySurvSet t J n).biUnion (fun k => P.polyBranchSet t (J + n) k)

lemma polySurvSet_succ (P : PolyRecData) (t : ℝ) (J n : ℕ) :
    P.polySurvSet t J (n + 1) =
      (P.polySurvSet t J n).biUnion (fun k => P.polyBranchSet t (J + n) k) := rfl

lemma poly_fiber_card_le (P : PolyRecData) {t : ℝ} (ht : 0 ≤ t) {j : ℕ} (hj : P.J₀ + 1 ≤ j)
    (c : ℕ) :
    (P.polyBranchSet t j c).card ≤ P.polyBranchB t := by
  classical
  have hj1 : 1 ≤ j := by have := P.hJ₀; omega
  have hQj : (0 : ℝ) < (P.Q j : ℝ) := by exact_mod_cast P.hQ_pos j
  have hQj1 : (0 : ℝ) < (P.Q (j + 1) : ℝ) := by exact_mod_cast P.hQ_pos (j + 1)
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hjr : (0 : ℝ) < (j : ℝ) ^ P.r := pow_pos hjR P.r
  set R := P.polyRad t j + P.polyRad t (j + 1)
  set A := (P.Q (j + 1) : ℝ) * ((c : ℝ) / (P.Q j : ℝ) - R)
  set B := (P.Q (j + 1) : ℝ) * ((c : ℝ) / (P.Q j : ℝ) + R)
  set S := P.polyBranchSet t j c
  have hAB : ∀ k' ∈ S, A ≤ (k' : ℝ) ∧ (k' : ℝ) ≤ B := by
    intro k' hk'
    have hdist : |(c : ℝ) / (P.Q j : ℝ) - (k' : ℝ) / (P.Q (j + 1) : ℝ)| ≤ R :=
      (Finset.mem_filter.mp hk').2
    have hle := abs_le.mp hdist
    constructor
    · have h1 : (c : ℝ) / (P.Q j : ℝ) - R ≤ (k' : ℝ) / (P.Q (j + 1) : ℝ) := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hQj1)
      have h3 : (P.Q (j + 1) : ℝ) * ((k' : ℝ) / (P.Q (j + 1) : ℝ)) = (k' : ℝ) := by field_simp
      linarith
    · have h1 : (k' : ℝ) / (P.Q (j + 1) : ℝ) ≤ (c : ℝ) / (P.Q j : ℝ) + R := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hQj1)
      have h3 : (P.Q (j + 1) : ℝ) * ((k' : ℝ) / (P.Q (j + 1) : ℝ)) = (k' : ℝ) := by field_simp
      linarith
  have hBA : B - A ≤ 2 * t * ((P.c : ℝ) + |(P.d : ℝ)| + 2) := by
    have hBAeq : B - A = 2 * R * (P.Q (j + 1) : ℝ) := by simp only [A, B]; ring
    rw [hBAeq]
    have hRQ : R * (P.Q (j + 1) : ℝ) =
        t * (P.Q (j + 1) : ℝ) / ((j : ℝ) ^ P.r * (P.Q j : ℝ)) +
          t / (((j + 1 : ℕ) : ℝ) ^ P.r) := by
      simp only [R, polyRad]; field_simp
    have hratio := P.poly_Q_ratio_bounds hj
    have hQle : (P.Q (j + 1) : ℝ) ≤ ((P.c : ℝ) + |(P.d : ℝ)| + 1) * (j : ℝ) ^ P.r * (P.Q j : ℝ) := by
      have h1 : (P.Q (j + 1) : ℝ) / (P.Q j : ℝ) ≤ ((P.c : ℝ) + |(P.d : ℝ)| + 1) * (j : ℝ) ^ P.r :=
        le_trans (le_of_lt hratio.2.1) hratio.2.2
      exact (div_le_iff₀ hQj).mp h1
    have hterm1 : t * (P.Q (j + 1) : ℝ) / ((j : ℝ) ^ P.r * (P.Q j : ℝ)) ≤
        t * ((P.c : ℝ) + |(P.d : ℝ)| + 1) := by
      rw [div_le_iff₀ (mul_pos hjr hQj)]
      have ht0 : 0 ≤ t := ht
      calc t * (P.Q (j + 1) : ℝ)
          ≤ t * (((P.c : ℝ) + |(P.d : ℝ)| + 1) * (j : ℝ) ^ P.r * (P.Q j : ℝ)) :=
            mul_le_mul_of_nonneg_left hQle ht0
        _ = t * ((P.c : ℝ) + |(P.d : ℝ)| + 1) * ((j : ℝ) ^ P.r * (P.Q j : ℝ)) := by ring
    have hterm2 : t / (((j + 1 : ℕ) : ℝ) ^ P.r) ≤ t := by
      have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j + 1)
      exact div_le_self ht (one_le_pow₀ h1)
    have hsum : R * (P.Q (j + 1) : ℝ) ≤ t * ((P.c : ℝ) + |(P.d : ℝ)| + 2) := by
      rw [hRQ]; linarith
    linarith
  let g : ℕ → ℕ := fun k' => Nat.floor ((k' : ℝ) - A)
  have hg_inj : Set.InjOn g (S : Set ℕ) := by
    intro k1 hk1 k2 hk2 hgeq
    by_contra hne
    have hA1 : A ≤ (k1 : ℝ) := (hAB k1 hk1).1
    have hA2 : A ≤ (k2 : ℝ) := (hAB k2 hk2).1
    have hf1 := Nat.lt_floor_add_one ((k1 : ℝ) - A)
    have hf2 := Nat.lt_floor_add_one ((k2 : ℝ) - A)
    have hgeqR : (g k1 : ℝ) = (g k2 : ℝ) := by exact_mod_cast hgeq
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hkR : (k1 : ℝ) + 1 ≤ (k2 : ℝ) := by exact_mod_cast (by omega : k1 + 1 ≤ k2)
      have : (g k1 : ℝ) + 1 ≤ (g k2 : ℝ) := by
        have h1 : (g k1 : ℝ) < (g k2 : ℝ) := by
          have : (g k1 : ℝ) ≤ (k1 : ℝ) - A := Nat.floor_le (by linarith)
          linarith
        have h2 : g k1 < g k2 := by exact_mod_cast h1
        exact_mod_cast (by omega : g k1 + 1 ≤ g k2)
      linarith
    · have hkR : (k2 : ℝ) + 1 ≤ (k1 : ℝ) := by exact_mod_cast (by omega : k2 + 1 ≤ k1)
      have : (g k2 : ℝ) + 1 ≤ (g k1 : ℝ) := by
        have h1 : (g k2 : ℝ) < (g k1 : ℝ) := by
          have : (g k2 : ℝ) ≤ (k2 : ℝ) - A := Nat.floor_le (by linarith)
          linarith
        have h2 : g k2 < g k1 := by exact_mod_cast h1
        exact_mod_cast (by omega : g k2 + 1 ≤ g k1)
      linarith
  have hg_img : (S : Set ℕ) ⊆ g ⁻¹' (Finset.range (P.polyBranchB t) : Set ℕ) := by
    intro k' hk'
    simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_range, polyBranchB]
    have hsub : (k' : ℝ) - A ≤ 2 * t * ((P.c : ℝ) + |(P.d : ℝ)| + 2) :=
      le_trans (by linarith [(hAB k' hk').2]) hBA
    have hfl : g k' ≤ Nat.floor (2 * t * ((P.c : ℝ) + |(P.d : ℝ)| + 2)) :=
      Nat.floor_mono hsub
    omega
  have hcard : S.card ≤ (Finset.range (P.polyBranchB t)).card :=
    Finset.card_le_card_of_injOn g (fun k' hk' => hg_img hk') hg_inj
  simpa [S] using hcard

lemma card_polySurvSet_le (P : PolyRecData) {t : ℝ} (ht : 0 ≤ t) {J : ℕ} (hJ : P.J₀ + 1 ≤ J)
    (n : ℕ) :
    (P.polySurvSet t J n).card ≤ ((P.Q J).toNat + 1) * (P.polyBranchB t) ^ n := by
  induction n with
  | zero =>
      simp [polySurvSet]
  | succ n ih =>
      rw [polySurvSet_succ]
      have hstep : ∀ k ∈ P.polySurvSet t J n,
          (P.polyBranchSet t (J + n) k).card ≤ P.polyBranchB t :=
        fun k _ => P.poly_fiber_card_le ht (by omega) k
      calc ((P.polySurvSet t J n).biUnion (fun k => P.polyBranchSet t (J + n) k)).card
          ≤ (P.polySurvSet t J n).card * P.polyBranchB t :=
            Finset.card_biUnion_le_card_mul _ _ _ hstep
        _ ≤ (((P.Q J).toNat + 1) * (P.polyBranchB t) ^ n) * P.polyBranchB t :=
            Nat.mul_le_mul_right _ ih
        _ = ((P.Q J).toNat + 1) * (P.polyBranchB t) ^ (n + 1) := by rw [pow_succ]; ring

def polyCenterOf (P : PolyRecData) (x : ℝ) (j : ℕ) : ℕ :=
  (round ((P.Q j : ℝ) * x)).toNat

lemma polyCenterOf_cast (P : PolyRecData) {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    (P.polyCenterOf x j : ℝ) = (round ((P.Q j : ℝ) * x) : ℝ) := by
  set y := (P.Q j : ℝ) * x
  have hy : 0 ≤ y := mul_nonneg (by exact_mod_cast (P.hQ_pos j).le) hx
  have h1 : |y - (round y : ℝ)| ≤ |y - (0 : ℤ)| := round_le y 0
  have h2 : |y - (0 : ℤ)| = y := by push_cast; rw [sub_zero, abs_of_nonneg hy]
  rw [h2] at h1
  have h4 : 0 ≤ (round y : ℝ) := by linarith [(abs_le.mp h1).2]
  have hrnn : 0 ≤ round y := by exact_mod_cast h4
  unfold polyCenterOf
  exact_mod_cast Int.toNat_of_nonneg hrnn

lemma polyCenterOf_lt_Q (P : PolyRecData) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ) :
    P.polyCenterOf x j < (P.Q j).toNat + 1 := by
  set y := (P.Q j : ℝ) * x
  have hQpos : 0 < P.Q j := P.hQ_pos j
  have hQreal : (0 : ℝ) < (P.Q j : ℝ) := by exact_mod_cast hQpos
  have hyQ : y ≤ (P.Q j : ℝ) := by simpa [y] using mul_le_mul_of_nonneg_left hx1 (le_of_lt hQreal)
  have h1 : |y - (round y : ℝ)| ≤ |y - (P.Q j : ℝ)| := round_le y (P.Q j)
  have h2 : |y - (P.Q j : ℝ)| = (P.Q j : ℝ) - y := by rw [abs_of_nonpos (by linarith)]; ring
  rw [h2] at h1
  have hrle : round y ≤ P.Q j := by
    have : (round y : ℝ) ≤ (P.Q j : ℝ) := by linarith [(abs_le.mp h1).1]
    exact_mod_cast this
  have hcast : (P.polyCenterOf x j : ℝ) = (round y : ℝ) := P.polyCenterOf_cast hx0 j
  have hle_Z : (P.polyCenterOf x j : ℤ) ≤ P.Q j := by
    have : ((P.polyCenterOf x j : ℤ) : ℝ) ≤ (P.Q j : ℝ) := by
      have : ((P.polyCenterOf x j : ℤ) : ℝ) = (P.polyCenterOf x j : ℝ) := by norm_cast
      linarith [hcast, (by exact_mod_cast hrle : (round y : ℝ) ≤ (P.Q j : ℝ))]
    exact_mod_cast this
  have htoNat : ((P.Q j).toNat : ℤ) = P.Q j := Int.toNat_of_nonneg (le_of_lt hQpos)
  omega

def polyTailSet (P : PolyRecData) (t : ℝ) (J : ℕ) : Set ℝ :=
  {x : ℝ | 0 ≤ x ∧ x ≤ 1 ∧ ∀ m : ℕ, J ≤ m → P.polyWeightedSeq (P.r : ℝ) x m ≤ t}

lemma polyTailSet_cover (P : PolyRecData) {t : ℝ} (_ht : 0 ≤ t) {J : ℕ} (hJ : P.J₀ + 1 ≤ J)
    (n : ℕ) :
    P.polyTailSet t J ⊆ ⋃ k : (P.polySurvSet t J n : Set ℕ), P.polyInterv t (J + n) (k : ℕ) := by
  intro x hx
  rcases hx with ⟨hx0, hx1, htail⟩
  have hmem_interv : ∀ m : ℕ, J ≤ m → x ∈ P.polyInterv t m (P.polyCenterOf x m) := by
    intro m hm
    have hm1 : 1 ≤ m := by have := P.hJ₀; omega
    have hQ : (0 : ℝ) < (P.Q m : ℝ) := by exact_mod_cast P.hQ_pos m
    have hmr : (0 : ℝ) < (m : ℝ) ^ P.r := pow_pos (by exact_mod_cast hm1) P.r
    have hbound := htail m hm
    unfold polyWeightedSeq at hbound
    rw [Real.rpow_natCast] at hbound
    have hdist : distToNearestInt ((P.Q m : ℝ) * x) =
        |(P.Q m : ℝ) * x - (P.polyCenterOf x m : ℝ)| := by
      simp only [distToNearestInt]; rw [← P.polyCenterOf_cast hx0 m]
    have h1 : |(P.Q m : ℝ) * x - (P.polyCenterOf x m : ℝ)| ≤ t / (m : ℝ) ^ P.r := by
      rw [← hdist]; exact (le_div_iff₀ hmr).mpr (by rw [mul_comm]; exact hbound)
    have hkey : (P.Q m : ℝ) * x - (P.polyCenterOf x m : ℝ) =
        (P.Q m : ℝ) * (x - (P.polyCenterOf x m : ℝ) / (P.Q m : ℝ)) := by field_simp
    rw [hkey, abs_mul, abs_of_pos hQ] at h1
    have h2 : |x - (P.polyCenterOf x m : ℝ) / (P.Q m : ℝ)| ≤ (t / (m : ℝ) ^ P.r) / (P.Q m : ℝ) :=
      (le_div_iff₀ hQ).mpr (by rw [mul_comm]; exact h1)
    have h3 : (t / (m : ℝ) ^ P.r) / (P.Q m : ℝ) = P.polyRad t m := by unfold polyRad; field_simp
    rw [h3] at h2
    have hle := abs_le.mp h2
    unfold polyInterv; constructor <;> linarith
  have hsurv : ∀ m : ℕ, P.polyCenterOf x (J + m) ∈ P.polySurvSet t J m := by
    intro m
    induction m with
    | zero =>
        simp only [polySurvSet, Nat.add_zero, Finset.mem_range]
        exact P.polyCenterOf_lt_Q hx0 hx1 J
    | succ m ih =>
        rw [polySurvSet_succ, Finset.mem_biUnion]
        refine ⟨P.polyCenterOf x (J + m), ih, ?_⟩
        unfold polyBranchSet
        rw [Finset.mem_filter, Finset.mem_range]
        have hadd : J + (m + 1) = J + m + 1 := by omega
        rw [hadd]
        refine ⟨P.polyCenterOf_lt_Q hx0 hx1 (J + m + 1), ?_⟩
        have h1 := Set.mem_Icc.mp (hmem_interv (J + m) (by omega))
        have h2 := Set.mem_Icc.mp (hmem_interv (J + m + 1) (by omega))
        have ha : |(P.polyCenterOf x (J + m) : ℝ) / (P.Q (J + m) : ℝ) - x| ≤
            P.polyRad t (J + m) := by
          rw [abs_le]; constructor <;> linarith
        have hb : |x - (P.polyCenterOf x (J + m + 1) : ℝ) / (P.Q (J + m + 1) : ℝ)| ≤
            P.polyRad t (J + m + 1) := by
          rw [abs_le]; constructor <;> linarith
        calc |(P.polyCenterOf x (J + m) : ℝ) / (P.Q (J + m) : ℝ) -
                (P.polyCenterOf x (J + m + 1) : ℝ) / (P.Q (J + m + 1) : ℝ)|
            ≤ |(P.polyCenterOf x (J + m) : ℝ) / (P.Q (J + m) : ℝ) - x| +
                |x - (P.polyCenterOf x (J + m + 1) : ℝ) / (P.Q (J + m + 1) : ℝ)| :=
              abs_sub_le _ _ _
          _ ≤ P.polyRad t (J + m) + P.polyRad t (J + m + 1) := by linarith
  exact Set.mem_iUnion.mpr ⟨⟨P.polyCenterOf x (J + n), hsurv n⟩, hmem_interv (J + n) (by omega)⟩

lemma poly_content_tendsto_zero (P : PolyRecData) {t : ℝ} (_ht : 0 ≤ t) {J : ℕ} (_hJ : P.J₁ ≤ J)
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ =>
        (((P.Q J).toNat + 1 : ℕ) : ℝ) * (2 * t / P.C_J₁) ^ s *
          ((P.polyBranchB t : ℝ) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ s) ^ (J + n) /
            (Nat.factorial (J + n) : ℝ) ^ s)
      atTop (nhds 0) := by
  set B : ℝ := (P.polyBranchB t : ℝ) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ s
  have hB0 : 0 ≤ B := by positivity
  have hkey := DimHFinite.tendsto_powB_div_factorial_rpow B hB0 s hs
  have hshift : Tendsto (fun n : ℕ => J + n) atTop atTop :=
    (tendsto_add_atTop_nat J).congr (fun n => Nat.add_comm n J)
  have hcomp := (hkey.comp hshift).const_mul
    ((((P.Q J).toNat + 1 : ℕ) : ℝ) * (2 * t / P.C_J₁) ^ s)
  have h0 : ((((P.Q J).toNat + 1 : ℕ) : ℝ) * (2 * t / P.C_J₁) ^ s) * 0 = 0 := by ring
  rw [h0] at hcomp
  refine hcomp.congr' (Filter.Eventually.of_forall fun n => ?_)
  dsimp [B]; ring

lemma poly_hausdorffMeasure_tailSet_zero (P : PolyRecData) {t : ℝ} (ht : 0 ≤ t)
    {J : ℕ} (hJ : P.J₁ ≤ J) {s : ℝ} (hs : 0 < s) :
    μH[s] (P.polyTailSet t J) = 0 := by
  have hJ₀ : P.J₀ + 1 ≤ J := le_trans P.J₁_ge_J₀_succ hJ
  let ι : ℕ → Type _ := fun n => {k // k ∈ P.polySurvSet t J n}
  let rSeq : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (2 * P.polyRad t (J + n))
  let cov : ∀ n, ι n → Set ℝ := fun n k => P.polyInterv t (J + n) k.1
  have hr : Tendsto rSeq atTop (nhds 0) := by
    have hrad0 : Tendsto (fun n : ℕ => 2 * P.polyRad t (J + n)) atTop (nhds 0) := by
      have hdiv : Tendsto (fun n : ℕ => 2 * t / (P.Q (J + n) : ℝ)) atTop (nhds 0) := by
        have hQ : Tendsto (fun n : ℕ => (P.Q (J + n) : ℝ)) atTop atTop :=
          P.poly_Q_tendsto_atTop.comp ((tendsto_add_atTop_nat J).congr (fun n => Nat.add_comm n J))
        exact hQ.const_div_atTop (2 * t)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv
        (Filter.Eventually.of_forall fun n => mul_nonneg (by norm_num) (P.polyRad_nonneg ht (J + n)))
        (Filter.Eventually.of_forall fun n => ?_)
      have h1 : 1 ≤ ((J + n : ℕ) : ℝ) := by
        have : 1 ≤ J + n := by have := P.two_le_J₁; omega
        exact_mod_cast this
      have hpow : (1 : ℝ) ≤ ((J + n : ℕ) : ℝ) ^ P.r := one_le_pow₀ h1
      have hQ : (0 : ℝ) < (P.Q (J + n) : ℝ) := by exact_mod_cast P.hQ_pos (J + n)
      unfold polyRad
      have hden : (P.Q (J + n) : ℝ) ≤ ((J + n : ℕ) : ℝ) ^ P.r * (P.Q (J + n) : ℝ) := by
        nlinarith
      calc 2 * (t / (((J + n : ℕ) : ℝ) ^ P.r * (P.Q (J + n) : ℝ)))
          = (2 * t) / (((J + n : ℕ) : ℝ) ^ P.r * (P.Q (J + n) : ℝ)) := by ring
        _ ≤ (2 * t) / (P.Q (J + n) : ℝ) := div_le_div_of_nonneg_left (by linarith) hQ hden
    simpa [rSeq] using ENNReal.tendsto_ofReal hrad0
  have ht_diam : ∀ᶠ n in atTop, ∀ k : ι n, Metric.ediam (cov n k) ≤ rSeq n :=
    Filter.Eventually.of_forall fun n k => P.ediam_polyInterv_le ht (J + n) k.1
  have hst : ∀ᶠ n in atTop, P.polyTailSet t J ⊆ ⋃ k : ι n, cov n k :=
    Filter.Eventually.of_forall fun n x hx => by
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (P.polyTailSet_cover ht hJ₀ n hx)
      exact Set.mem_iUnion.mpr ⟨⟨k.1, k.2⟩, hk⟩
  have hmain := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum s
    (P.polyTailSet t J) rSeq hr cov ht_diam hst
  have hcontent : ∀ n : ℕ,
      ((P.polySurvSet t J n).card : ℝ) * (2 * P.polyRad t (J + n)) ^ s ≤
        (((P.Q J).toNat + 1 : ℕ) : ℝ) * (2 * t / P.C_J₁) ^ s *
          ((P.polyBranchB t : ℝ) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ s) ^ (J + n) /
            (Nat.factorial (J + n) : ℝ) ^ s := by
    intro n
    have hcardR : ((P.polySurvSet t J n).card : ℝ) ≤
        (((P.Q J).toNat + 1 : ℕ) : ℝ) * (P.polyBranchB t : ℝ) ^ n := by
      exact_mod_cast P.card_polySurvSet_le ht hJ₀ n
    have hB1 : (1 : ℝ) ≤ (P.polyBranchB t : ℝ) := by
      exact_mod_cast P.polyBranchB_pos t
    have hBn : (P.polyBranchB t : ℝ) ^ n ≤ (P.polyBranchB t : ℝ) ^ (J + n) :=
      pow_le_pow_right₀ hB1 (by omega)
    have hQge := P.poly_Q_ge_factorial (show P.J₁ ≤ J + n by omega)
    have hfact1 : (1 : ℝ) ≤ (Nat.factorial (J + n) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (J + n)
    have hfactr : (Nat.factorial (J + n) : ℝ) ≤ (Nat.factorial (J + n) : ℝ) ^ P.r := by
      calc (Nat.factorial (J + n) : ℝ) = (Nat.factorial (J + n) : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (Nat.factorial (J + n) : ℝ) ^ P.r := pow_le_pow_right₀ hfact1 P.hr
    have hc_pos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
    have hC_pos : 0 < P.C_J₁ := P.C_J₁_pos
    have hQge' : P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (J + n) *
        (Nat.factorial (J + n) : ℝ) ≤ (P.Q (J + n) : ℝ) := by
      have hnn : 0 ≤ P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (J + n) := by positivity
      exact le_trans (mul_le_mul_of_nonneg_left hfactr hnn) hQge
    have h1 : (1 : ℝ) ≤ ((J + n : ℕ) : ℝ) := by
      have : 1 ≤ J + n := by have := P.two_le_J₁; omega
      exact_mod_cast this
    have hpow : (1 : ℝ) ≤ ((J + n : ℕ) : ℝ) ^ P.r := one_le_pow₀ h1
    have hden_pos : 0 < P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (J + n) *
        (Nat.factorial (J + n) : ℝ) := by positivity
    have hrad_le : 2 * P.polyRad t (J + n) ≤
        (2 * t / P.C_J₁) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ (J + n) /
          (Nat.factorial (J + n) : ℝ) := by
      unfold polyRad
      have hden_le : P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (J + n) *
          (Nat.factorial (J + n) : ℝ) ≤
          ((J + n : ℕ) : ℝ) ^ P.r * (P.Q (J + n) : ℝ) := by
        calc P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (J + n) * (Nat.factorial (J + n) : ℝ)
            ≤ (P.Q (J + n) : ℝ) := hQge'
          _ ≤ ((J + n : ℕ) : ℝ) ^ P.r * (P.Q (J + n) : ℝ) := by
              nlinarith [P.hQ_pos (J + n)]
      have hdiv := div_le_div_of_nonneg_left (by linarith : 0 ≤ 2 * t) hden_pos hden_le
      calc 2 * (t / (((J + n : ℕ) : ℝ) ^ P.r * (P.Q (J + n) : ℝ)))
          = (2 * t) / (((J + n : ℕ) : ℝ) ^ P.r * (P.Q (J + n) : ℝ)) := by ring
        _ ≤ (2 * t) / (P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (J + n) *
              (Nat.factorial (J + n) : ℝ)) := hdiv
        _ = (2 * t / P.C_J₁) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ (J + n) /
              (Nat.factorial (J + n) : ℝ) := by
            rw [div_pow, div_pow]; field_simp
    have hrad_nn : 0 ≤ 2 * P.polyRad t (J + n) :=
      mul_nonneg (by norm_num) (P.polyRad_nonneg ht (J + n))
    have hrpow_rad : (2 * P.polyRad t (J + n)) ^ s ≤
        (2 * t / P.C_J₁) ^ s * (((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ s) ^ (J + n) /
          (Nat.factorial (J + n) : ℝ) ^ s := by
      have h1 := Real.rpow_le_rpow hrad_nn hrad_le (le_of_lt hs)
      have hrp : (((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ (J + n)) ^ s =
          (((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ s) ^ (J + n) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
          Real.rpow_mul (by positivity), Real.rpow_natCast]
      have h2t : 0 ≤ 2 * t / P.C_J₁ := div_nonneg (by linarith) (le_of_lt hC_pos)
      have h2c : 0 ≤ ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ (J + n) := by positivity
      conv_rhs at h1 =>
        rw [Real.div_rpow (mul_nonneg h2t h2c) (by positivity),
          Real.mul_rpow h2t h2c, hrp]
      exact h1
    have hcard_full : ((P.polySurvSet t J n).card : ℝ) ≤
        (((P.Q J).toNat + 1 : ℕ) : ℝ) * (P.polyBranchB t : ℝ) ^ (J + n) :=
      le_trans hcardR (mul_le_mul_of_nonneg_left hBn (by positivity))
    calc ((P.polySurvSet t J n).card : ℝ) * (2 * P.polyRad t (J + n)) ^ s
        ≤ ((((P.Q J).toNat + 1 : ℕ) : ℝ) * (P.polyBranchB t : ℝ) ^ (J + n)) *
            ((2 * t / P.C_J₁) ^ s * (((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ s) ^ (J + n) /
              (Nat.factorial (J + n) : ℝ) ^ s) :=
          mul_le_mul hcard_full hrpow_rad (Real.rpow_nonneg hrad_nn s) (by positivity)
      _ = (((P.Q J).toNat + 1 : ℕ) : ℝ) * (2 * t / P.C_J₁) ^ s *
            ((P.polyBranchB t : ℝ) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ s) ^ (J + n) /
              (Nat.factorial (J + n) : ℝ) ^ s := by
          rw [mul_pow]; ring
  have hsum_le : ∀ n : ℕ, ∑ k : ι n, Metric.ediam (cov n k) ^ s ≤
      ENNReal.ofReal ((((P.Q J).toNat + 1 : ℕ) : ℝ) * (2 * t / P.C_J₁) ^ s *
        ((P.polyBranchB t : ℝ) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ s) ^ (J + n) /
          (Nat.factorial (J + n) : ℝ) ^ s) := by
    intro n
    have h1 : ∑ k : ι n, Metric.ediam (cov n k) ^ s ≤
        ((P.polySurvSet t J n).card : ℝ≥0∞) * ENNReal.ofReal (2 * P.polyRad t (J + n)) ^ s := by
      calc ∑ k : ι n, Metric.ediam (cov n k) ^ s
          = ∑ k ∈ P.polySurvSet t J n, Metric.ediam (P.polyInterv t (J + n) k) ^ s := by
            symm
            apply Finset.sum_bij (fun k _ => (⟨k, by assumption⟩ : ι n))
            · intro _ _; exact Finset.mem_univ _
            · intro _ _ _ _ h; exact Subtype.mk.inj h
            · intro k _; exact ⟨k.1, k.2, rfl⟩
            · intro _ _; rfl
        _ ≤ ∑ k ∈ P.polySurvSet t J n, ENNReal.ofReal (2 * P.polyRad t (J + n)) ^ s := by
            apply Finset.sum_le_sum; intro k _
            exact ENNReal.rpow_le_rpow (P.ediam_polyInterv_le ht (J + n) k) (le_of_lt hs)
        _ = ((P.polySurvSet t J n).card : ℝ≥0∞) * ENNReal.ofReal (2 * P.polyRad t (J + n)) ^ s := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ((P.polySurvSet t J n).card : ℝ≥0∞) * ENNReal.ofReal (2 * P.polyRad t (J + n)) ^ s =
        ENNReal.ofReal (((P.polySurvSet t J n).card : ℝ) * (2 * P.polyRad t (J + n)) ^ s) := by
      have hcast : ((P.polySurvSet t J n).card : ℝ≥0∞) =
          ENNReal.ofReal ((P.polySurvSet t J n).card : ℝ) := by simp
      rw [hcast, ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (by norm_num) (P.polyRad_nonneg ht (J + n))) (le_of_lt hs),
        ENNReal.ofReal_mul (by positivity)]
    exact le_trans h1 (le_of_eq h2 |>.trans (ENNReal.ofReal_le_ofReal (hcontent n)))
  have hlim : Filter.liminf (fun n => ∑ k : ι n, Metric.ediam (cov n k) ^ s) atTop ≤ 0 := by
    have hbound0 : Tendsto (fun n : ℕ => ENNReal.ofReal
        ((((P.Q J).toNat + 1 : ℕ) : ℝ) * (2 * t / P.C_J₁) ^ s *
          ((P.polyBranchB t : ℝ) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ s) ^ (J + n) /
            (Nat.factorial (J + n) : ℝ) ^ s)) atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal (P.poly_content_tendsto_zero ht hJ hs)
    have hle' : ∀ᶠ n in atTop, (∑ k : ι n, Metric.ediam (cov n k) ^ s : ℝ≥0∞) ≤ _ :=
      Filter.Eventually.of_forall hsum_le
    have hlimsup0 : Filter.limsup (fun n => ∑ k : ι n, Metric.ediam (cov n k) ^ s) atTop ≤ 0 := by
      have hmono := Filter.limsup_le_limsup hle'
      rwa [hbound0.limsup_eq] at hmono
    exact le_trans Filter.liminf_le_limsup hlimsup0
  have hlim0 : Filter.liminf (fun n => ∑ k : ι n, Metric.ediam (cov n k) ^ s) atTop = 0 :=
    le_antisymm hlim bot_le
  rw [hlim0] at hmain
  exact le_antisymm hmain bot_le

lemma poly_dimH_tailSet_zero (P : PolyRecData) {t : ℝ} (ht : 0 ≤ t) {J : ℕ} (hJ : P.J₁ ≤ J) :
    dimH (P.polyTailSet t J) = 0 := by
  apply le_antisymm _ bot_le
  rw [dimH_eq_iInf]
  by_contra hne
  have hpos : 0 < ⨅ (d : ℝ≥0) (_ : μH[d] (P.polyTailSet t J) = 0), (d : ℝ≥0∞) :=
    not_le.mp hne
  obtain ⟨r, hr0, hrlt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
  have hrpos : 0 < (r : ℝ) := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hr0)
  have hr2 : 0 < (r : ℝ) / 2 := by linarith
  have hmu := P.poly_hausdorffMeasure_tailSet_zero ht hJ hr2
  let r2 : ℝ≥0 := ⟨(r : ℝ) / 2, le_of_lt hr2⟩
  have hle : (⨅ (d : ℝ≥0) (_ : μH[d] (P.polyTailSet t J) = 0), (d : ℝ≥0∞)) ≤ (r2 : ℝ≥0∞) :=
    iInf₂_le r2 hmu
  have hlt : (r2 : ℝ≥0∞) < (r : ℝ≥0∞) := by
    exact_mod_cast (by linarith : (r : ℝ) / 2 < (r : ℝ))
  exact (not_le.mpr (lt_of_lt_of_le hrlt hle)) (le_of_lt hlt)

lemma polyWeightedSeq_add_intCast (P : PolyRecData) (α : ℝ) (x : ℝ) (m : ℤ) (j : ℕ) :
    P.polyWeightedSeq α (x + (m : ℝ)) j = P.polyWeightedSeq α x j := by
  unfold polyWeightedSeq
  have hcast : (P.Q j : ℝ) * (x + (m : ℝ)) = (P.Q j : ℝ) * x + ((P.Q j * m : ℤ) : ℝ) := by
    push_cast; ring
  rw [hcast, DimHFinite.distToNearestInt_add_intCast]

lemma polyApprExponent_add_intCast (P : PolyRecData) (x : ℝ) (m : ℤ) :
    P.polyApprExponent (x + (m : ℝ)) = P.polyApprExponent x := by
  unfold polyApprExponent polyWeightedExponent
  congr 1; funext j
  rw [P.polyWeightedSeq_add_intCast]

lemma poly_levelSet_subset_iUnion_tailSet (P : PolyRecData) {c t : ℝ} (hc0 : 0 ≤ c) (hct : c < t) :
    P.polyLevelSet (ENNReal.ofReal c) ⊆
      ⋃ (J : {J : ℕ // P.J₁ ≤ J}) (m : ℤ), (fun y : ℝ => y + (m : ℝ)) '' P.polyTailSet t J.1 := by
  intro x hx
  have ht0 : 0 < t := lt_of_le_of_lt hc0 hct
  have hlt : P.polyApprExponent x < ENNReal.ofReal t :=
    lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff ht0).mpr hct)
  have hev : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (P.polyWeightedSeq (P.r : ℝ) x j) < ENNReal.ofReal t :=
    eventually_lt_of_limsup_lt hlt
  have hev' : ∀ᶠ j : ℕ in atTop, P.polyWeightedSeq (P.r : ℝ) x j ≤ t :=
    hev.mono fun j hj => le_of_lt ((ENNReal.ofReal_lt_ofReal_iff ht0).mp hj)
  obtain ⟨J₀', hJ₀'⟩ := Filter.eventually_atTop.mp hev'
  set J := max P.J₁ J₀'
  have hJ1 : P.J₁ ≤ J := le_max_left _ _
  set m := ⌊x⌋
  set y := x - (m : ℝ)
  have hy0 : 0 ≤ y := sub_nonneg.mpr (Int.floor_le x)
  have hy1 : y ≤ 1 := by linarith [Int.lt_floor_add_one x]
  have hym : x = y + (m : ℝ) := by ring
  have htail : ∀ j : ℕ, J ≤ j → P.polyWeightedSeq (P.r : ℝ) y j ≤ t := by
    intro j hj
    have h1 := hJ₀' j (le_trans (le_max_right _ _) hj)
    rwa [hym, P.polyWeightedSeq_add_intCast] at h1
  refine Set.mem_iUnion.mpr ⟨⟨J, hJ1⟩, Set.mem_iUnion.mpr ⟨m, y, ⟨hy0, hy1, htail⟩, by linarith⟩⟩

/-- **Theorem `thm:poly-phase-transition`(i)（临界权 $\alpha = r$ 维数零定理）**：
    对一切有限 $t \in \mathbb{R}$，$\dim_H \{x : \Lambda^{(r,c,d)}(x) \le t\} = 0$。 -/
theorem poly_dimH_levelSet_finite (P : PolyRecData) (t : ℝ) :
    dimH (P.polyLevelSet (ENNReal.ofReal t)) = 0 := by
  set c' := max t 0
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hmono0 : P.polyLevelSet (ENNReal.ofReal t) ⊆ P.polyLevelSet (ENNReal.ofReal c') :=
    fun x hx => le_trans hx (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  set T := c' + 1
  have hsub := Set.Subset.trans hmono0 (P.poly_levelSet_subset_iUnion_tailSet (t := T) hc'0 (by linarith))
  have hdim : dimH (⋃ (J : {J : ℕ // P.J₁ ≤ J}) (m : ℤ),
      (fun y : ℝ => y + (m : ℝ)) '' P.polyTailSet T J.1) = 0 := by
    rw [dimH_iUnion]
    apply iSup_eq_bot.mpr
    intro J
    rw [dimH_iUnion]
    apply iSup_eq_bot.mpr
    intro m
    have hlip : LipschitzWith 1 (fun y : ℝ => y + (m : ℝ)) :=
      LipschitzWith.of_dist_le_mul fun y₁ y₂ => by simp [dist_eq_norm]
    have hle := hlip.dimH_image_le (P.polyTailSet T J.1)
    rw [P.poly_dimH_tailSet_zero (by linarith) J.2] at hle
    exact le_antisymm hle bot_le
  exact le_antisymm (le_trans (dimH_mono hsub) (le_of_eq hdim)) bot_le

lemma poly_volume_tailSet_zero (P : PolyRecData) {t : ℝ} (ht : 0 ≤ t) {J : ℕ} (hJ : P.J₁ ≤ J) :
    MeasureTheory.volume (P.polyTailSet t J) = 0 := by
  have hJ₀ : P.J₀ + 1 ≤ J := le_trans P.J₁_ge_J₀_succ hJ
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  simp only [zero_add]
  have hlim := P.poly_content_tendsto_zero ht hJ (by norm_num : (0 : ℝ) < 1)
  have hof : Tendsto (fun n : ℕ => ENNReal.ofReal
      ((((P.Q J).toNat + 1 : ℕ) : ℝ) * (2 * t / P.C_J₁) ^ (1 : ℝ) *
        ((P.polyBranchB t : ℝ) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ (1 : ℝ)) ^ (J + n) /
          (Nat.factorial (J + n) : ℝ) ^ (1 : ℝ))) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hlim
  obtain ⟨n, hn⟩ := (hof.eventually (Iio_mem_nhds (ENNReal.coe_pos.mpr hε))).exists
  have hcov := P.polyTailSet_cover ht hJ₀ n
  have hvol_i : ∀ k : ℕ, MeasureTheory.volume (P.polyInterv t (J + n) k) =
      ENNReal.ofReal (2 * P.polyRad t (J + n)) := fun k => by
    unfold polyInterv
    rw [Real.volume_Icc]
    congr 1; ring
  have hrad_le : 2 * P.polyRad t (J + n) ≤
      (2 * t / P.C_J₁) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ (J + n) /
        (Nat.factorial (J + n) : ℝ) := by
    have hQge := P.poly_Q_ge_factorial (show P.J₁ ≤ J + n by omega)
    have hfact1 : (1 : ℝ) ≤ (Nat.factorial (J + n) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (J + n)
    have hfactr : (Nat.factorial (J + n) : ℝ) ≤ (Nat.factorial (J + n) : ℝ) ^ P.r := by
      calc (Nat.factorial (J + n) : ℝ) = (Nat.factorial (J + n) : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (Nat.factorial (J + n) : ℝ) ^ P.r := pow_le_pow_right₀ hfact1 P.hr
    have hc_pos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
    have hC_pos : 0 < P.C_J₁ := P.C_J₁_pos
    have hden_pos : 0 < P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (J + n) *
        (Nat.factorial (J + n) : ℝ) := by positivity
    have h1 : (1 : ℝ) ≤ ((J + n : ℕ) : ℝ) := by
      have : 1 ≤ J + n := by have := P.two_le_J₁; omega
      exact_mod_cast this
    have hpow : (1 : ℝ) ≤ ((J + n : ℕ) : ℝ) ^ P.r := one_le_pow₀ h1
    have hden_le : P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (J + n) *
        (Nat.factorial (J + n) : ℝ) ≤
        ((J + n : ℕ) : ℝ) ^ P.r * (P.Q (J + n) : ℝ) := by
      have hnn : 0 ≤ P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (J + n) := by positivity
      have hQge' : P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (J + n) *
          (Nat.factorial (J + n) : ℝ) ≤ (P.Q (J + n) : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left hfactr hnn) hQge
      nlinarith [P.hQ_pos (J + n)]
    have hdiv := div_le_div_of_nonneg_left (by linarith : 0 ≤ 2 * t) hden_pos hden_le
    unfold polyRad
    calc 2 * (t / (((J + n : ℕ) : ℝ) ^ P.r * (P.Q (J + n) : ℝ)))
        = (2 * t) / (((J + n : ℕ) : ℝ) ^ P.r * (P.Q (J + n) : ℝ)) := by ring
      _ ≤ (2 * t) / (P.C_J₁ * ((P.c : ℝ) / (2 : ℝ) ^ (P.r + 1)) ^ (J + n) *
            (Nat.factorial (J + n) : ℝ)) := hdiv
      _ = (2 * t / P.C_J₁) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ (J + n) /
            (Nat.factorial (J + n) : ℝ) := by rw [div_pow, div_pow]; field_simp
  have hB1 : (1 : ℝ) ≤ (P.polyBranchB t : ℝ) := by exact_mod_cast P.polyBranchB_pos t
  have hBn : (P.polyBranchB t : ℝ) ^ n ≤ (P.polyBranchB t : ℝ) ^ (J + n) :=
    pow_le_pow_right₀ hB1 (by omega)
  have hcardR : ((P.polySurvSet t J n).card : ℝ) ≤
      (((P.Q J).toNat + 1 : ℕ) : ℝ) * (P.polyBranchB t : ℝ) ^ (J + n) := by
    have h := (by exact_mod_cast P.card_polySurvSet_le ht hJ₀ n :
      ((P.polySurvSet t J n).card : ℝ) ≤ (((P.Q J).toNat + 1 : ℕ) : ℝ) * (P.polyBranchB t : ℝ) ^ n)
    exact le_trans h (mul_le_mul_of_nonneg_left hBn (by positivity))
  calc MeasureTheory.volume (P.polyTailSet t J)
      ≤ MeasureTheory.volume (⋃ k : (P.polySurvSet t J n : Set ℕ), P.polyInterv t (J + n) k.1) :=
        measure_mono hcov
    _ ≤ ∑ k : (P.polySurvSet t J n : Set ℕ), MeasureTheory.volume (P.polyInterv t (J + n) k.1) :=
        measure_iUnion_fintype_le _ _
    _ = ((P.polySurvSet t J n).card : ℝ≥0∞) * ENNReal.ofReal (2 * P.polyRad t (J + n)) := by
        simp [hvol_i, Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal (((P.polySurvSet t J n).card : ℝ) * (2 * P.polyRad t (J + n))) := by
        have hcast : ((P.polySurvSet t J n).card : ℝ≥0∞) =
            ENNReal.ofReal ((P.polySurvSet t J n).card : ℝ) := by simp
        rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((((P.Q J).toNat + 1 : ℕ) : ℝ) * (2 * t / P.C_J₁) ^ (1 : ℝ) *
          ((P.polyBranchB t : ℝ) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ (1 : ℝ)) ^ (J + n) /
            (Nat.factorial (J + n) : ℝ) ^ (1 : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        simp only [Real.rpow_one]
        calc ((P.polySurvSet t J n).card : ℝ) * (2 * P.polyRad t (J + n))
            ≤ ((((P.Q J).toNat + 1 : ℕ) : ℝ) * (P.polyBranchB t : ℝ) ^ (J + n)) *
                ((2 * t / P.C_J₁) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ)) ^ (J + n) /
                  (Nat.factorial (J + n) : ℝ)) := by
              gcongr
              exact mul_nonneg (by norm_num) (P.polyRad_nonneg ht (J + n))
          _ = (((P.Q J).toNat + 1 : ℕ) : ℝ) * (2 * t / P.C_J₁) *
                ((P.polyBranchB t : ℝ) * ((2 : ℝ) ^ (P.r + 1) / (P.c : ℝ))) ^ (J + n) /
                  (Nat.factorial (J + n) : ℝ) := by rw [mul_pow]; ring
    _ ≤ (ε : ℝ≥0∞) := le_of_lt hn

lemma poly_finiteLevel_eq_iUnion_nat (P : PolyRecData) :
    {x : ℝ | P.polyApprExponent x < ⊤} = ⋃ n : ℕ, P.polyLevelSet (ENNReal.ofReal (n : ℝ)) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, polyLevelSet]
  constructor
  · intro hx
    have hfin : P.polyApprExponent x ≠ ⊤ := ne_of_lt hx
    obtain ⟨n, hn⟩ := exists_nat_ge (P.polyApprExponent x).toReal
    refine ⟨n, ?_⟩
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hn
  · rintro ⟨n, hn⟩
    exact lt_of_le_of_lt hn ENNReal.ofReal_lt_top

theorem poly_dimH_finiteLevel_zero (P : PolyRecData) :
    dimH {x : ℝ | P.polyApprExponent x < ⊤} = 0 := by
  apply le_antisymm _ bot_le
  rw [P.poly_finiteLevel_eq_iUnion_nat, dimH_iUnion]
  apply iSup_le
  intro n
  exact (P.poly_dimH_levelSet_finite (n : ℝ)).le

theorem poly_volume_finiteLevel_zero (P : PolyRecData) :
    MeasureTheory.volume {x : ℝ | P.polyApprExponent x < ⊤} = 0 := by
  rw [P.poly_finiteLevel_eq_iUnion_nat]
  apply measure_iUnion_null
  intro n
  set T := (n : ℝ) + 1
  have hsub := P.poly_levelSet_subset_iUnion_tailSet (t := T) (Nat.cast_nonneg n) (by linarith)
  refine measure_mono_null hsub (measure_iUnion_null fun J => measure_iUnion_null fun m => ?_)
  have himg : (fun y : ℝ => y + (m : ℝ)) '' P.polyTailSet T J.1 =
      (fun y : ℝ => y + -(m : ℝ)) ⁻¹' P.polyTailSet T J.1 := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨x + -(m : ℝ), hx, by ring⟩
  rw [himg, measure_preimage_add_right]
  exact P.poly_volume_tailSet_zero (by positivity) J.2

theorem poly_ae_apprExponent_eq_top (P : PolyRecData) :
    ∀ᵐ x ∂MeasureTheory.volume, P.polyApprExponent x = ⊤ := by
  rw [ae_iff]
  have heq : {x : ℝ | ¬ P.polyApprExponent x = ⊤} = {x : ℝ | P.polyApprExponent x < ⊤} := by
    ext x; simp [lt_top_iff_ne_top]
  rw [heq]
  exact P.poly_volume_finiteLevel_zero

theorem poly_volume_infiniteLevel_Icc (P : PolyRecData) (a b : ℝ) :
    MeasureTheory.volume ({x : ℝ | P.polyApprExponent x = ⊤} ∩ Set.Icc a b) =
      ENNReal.ofReal (b - a) := by
  have hsub : Set.Icc a b ⊆
      ({x : ℝ | P.polyApprExponent x = ⊤} ∩ Set.Icc a b) ∪ {x : ℝ | P.polyApprExponent x < ⊤} := by
    intro x hx
    by_cases htop : P.polyApprExponent x = ⊤
    · exact Or.inl ⟨htop, hx⟩
    · exact Or.inr (lt_top_iff_ne_top.mpr htop)
  apply le_antisymm
  · rw [← Real.volume_Icc]; exact measure_mono Set.inter_subset_right
  · calc ENNReal.ofReal (b - a)
        = MeasureTheory.volume (Set.Icc a b) := Real.volume_Icc.symm
      _ ≤ MeasureTheory.volume (({x : ℝ | P.polyApprExponent x = ⊤} ∩ Set.Icc a b) ∪
            {x : ℝ | P.polyApprExponent x < ⊤}) := measure_mono hsub
      _ ≤ MeasureTheory.volume ({x : ℝ | P.polyApprExponent x = ⊤} ∩ Set.Icc a b) +
            MeasureTheory.volume {x : ℝ | P.polyApprExponent x < ⊤} := measure_union_le _ _
      _ = MeasureTheory.volume ({x : ℝ | P.polyApprExponent x = ⊤} ∩ Set.Icc a b) := by
            rw [P.poly_volume_finiteLevel_zero, add_zero]

/-- 正 Lebesgue 测度实数子集必有 $\dim_H(S) = 1$（且由此得 $[a,b]$ 上 $\Lambda^{(r,c,d)} = \infty$ 集合维数 $1$）。 -/
lemma dimH_eq_one_of_volume_pos {S : Set ℝ} (hvol : 0 < MeasureTheory.volume S) :
    dimH S = 1 := by
  apply le_antisymm (GaugeExact.dimH_real_subset_le_one S)
  rw [dimH_eq_iInf]
  apply le_iInf₂
  intro s hs
  by_contra hlt
  have hs1 : (s : ℝ) < 1 := by
    have : (s : ℝ≥0∞) < 1 := not_le.mp hlt
    exact_mod_cast this
  have hvol_le : ∀ t : Set ℝ, Metric.ediam t ≤ 1 →
      MeasureTheory.volume t ≤ 2 * (Metric.ediam t) ^ (s : ℝ) := by
    intro t ht1
    by_cases hne : t.Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hd_ne_top : Metric.ediam t ≠ ⊤ := ne_of_lt (lt_of_le_of_lt ht1 ENNReal.one_lt_top)
      have hsub : t ⊆ Set.Icc (x - (Metric.ediam t).toReal) (x + (Metric.ediam t).toReal) := by
        intro y hy
        have hdist : dist y x ≤ (Metric.ediam t).toReal := by
          have hed := Metric.edist_le_ediam_of_mem hy hx
          rw [edist_dist, ← ENNReal.ofReal_toReal hd_ne_top] at hed
          exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hed
        rw [Real.dist_eq] at hdist
        have habs := abs_le.mp hdist
        exact ⟨by linarith, by linarith⟩
      have hvol_t : MeasureTheory.volume t ≤ 2 * Metric.ediam t := by
        calc MeasureTheory.volume t
            ≤ MeasureTheory.volume (Set.Icc (x - (Metric.ediam t).toReal)
                (x + (Metric.ediam t).toReal)) := measure_mono hsub
          _ = ENNReal.ofReal (2 * (Metric.ediam t).toReal) := by
                rw [Real.volume_Icc]; congr 1; ring
          _ = 2 * Metric.ediam t := by
                rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
                  ENNReal.ofReal_toReal hd_ne_top]
      have hed_le_pow : Metric.ediam t ≤ (Metric.ediam t) ^ (s : ℝ) := by
        by_cases h0 : Metric.ediam t = 0
        · rw [h0]; exact bot_le
        · have hpos : 0 < (Metric.ediam t).toReal :=
            ENNReal.toReal_pos h0 hd_ne_top
          have hle1 : (Metric.ediam t).toReal ≤ 1 := by
            have : ENNReal.ofReal (Metric.ediam t).toReal ≤ ENNReal.ofReal 1 := by
              simpa [ENNReal.ofReal_toReal hd_ne_top] using ht1
            exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp this
          have hpowR : (Metric.ediam t).toReal ≤ (Metric.ediam t).toReal ^ (s : ℝ) := by
            conv_lhs => rw [← Real.rpow_one (Metric.ediam t).toReal]
            exact Real.rpow_le_rpow_of_exponent_ge hpos hle1 (le_of_lt hs1)
          have hpowE : (Metric.ediam t) ^ (s : ℝ) =
              ENNReal.ofReal ((Metric.ediam t).toReal ^ (s : ℝ)) := by
            conv_lhs => rw [← ENNReal.ofReal_toReal hd_ne_top]
            exact ENNReal.ofReal_rpow_of_nonneg
              (ENNReal.toReal_nonneg : 0 ≤ (Metric.ediam t).toReal) s.2
          rw [hpowE]
          conv_lhs => rw [← ENNReal.ofReal_toReal hd_ne_top]
          exact ENNReal.ofReal_le_ofReal hpowR
      exact le_trans hvol_t (mul_le_mul_of_nonneg_left hed_le_pow (by norm_num : (0 : ℝ≥0∞) ≤ 2))
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp
  have hvol0 : MeasureTheory.volume S = 0 := by
    apply le_antisymm _ zero_le
    have hμ0 : μH[(s : ℝ)] S = 0 := hs
    rw [Measure.hausdorffMeasure_apply] at hμ0
    have hsup1 : ⨅ (t : ℕ → Set ℝ) (_ : S ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ 1),
        ∑' n, ⨆ _ : (t n).Nonempty, (Metric.ediam (t n)) ^ (s : ℝ) = 0 := by
      have hle := le_iSup₂ (1 : ℝ≥0∞) (zero_lt_one)
        (f := fun r : ℝ≥0∞ => fun _ : 0 < r =>
          ⨅ (t : ℕ → Set ℝ) (_ : S ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
            ∑' n, ⨆ _ : (t n).Nonempty, (Metric.ediam (t n)) ^ (s : ℝ))
      exact le_antisymm (le_trans hle (le_of_eq hμ0)) bot_le
    have hvol_le_2sum : ∀ (t : ℕ → Set ℝ) (_ : S ⊆ ⋃ n, t n)
        (_ : ∀ n, Metric.ediam (t n) ≤ 1),
        MeasureTheory.volume S ≤
          2 * ∑' n, ⨆ _ : (t n).Nonempty, (Metric.ediam (t n)) ^ (s : ℝ) := by
      intro t hcov hdiam
      calc MeasureTheory.volume S
          ≤ MeasureTheory.volume (⋃ n, t n) := measure_mono hcov
        _ ≤ ∑' n, MeasureTheory.volume (t n) := measure_iUnion_le t
        _ ≤ ∑' n, 2 * (⨆ _ : (t n).Nonempty, (Metric.ediam (t n)) ^ (s : ℝ)) := by
            apply ENNReal.tsum_le_tsum
            intro n
            by_cases hne : (t n).Nonempty
            · simp only [hne, ciSup_pos]
              exact hvol_le (t n) (hdiam n)
            · have he : t n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
              simp [he]
        _ = 2 * ∑' n, ⨆ _ : (t n).Nonempty, (Metric.ediam (t n)) ^ (s : ℝ) :=
            ENNReal.tsum_mul_left
    have hvol_le_2inf : MeasureTheory.volume S ≤
        2 * ⨅ (t : ℕ → Set ℝ) (_ : S ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ 1),
          ∑' n, ⨆ _ : (t n).Nonempty, (Metric.ediam (t n)) ^ (s : ℝ) := by
      rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
      refine le_iInf fun t => ?_
      rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
      refine le_iInf fun hcov => ?_
      rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
      refine le_iInf fun hdiam => hvol_le_2sum t hcov hdiam
    rw [hsup1, mul_zero] at hvol_le_2inf
    exact hvol_le_2inf
  exact (ne_of_gt hvol) hvol0

theorem poly_dimH_infiniteLevel_inter_Icc_eq_one (P : PolyRecData) {a b : ℝ} (hab : a < b) :
    dimH ({x : ℝ | P.polyApprExponent x = ⊤} ∩ Set.Icc a b) = 1 := by
  apply dimH_eq_one_of_volume_pos
  rw [P.poly_volume_infiniteLevel_Icc a b]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)

theorem poly_dimH_infiniteLevel_eq_one (P : PolyRecData) :
    dimH {x : ℝ | P.polyApprExponent x = ⊤} = 1 := by
  apply le_antisymm (GaugeExact.dimH_real_subset_le_one _)
  rw [← P.poly_dimH_infiniteLevel_inter_Icc_eq_one (by norm_num : (0 : ℝ) < 1)]
  exact dimH_mono Set.inter_subset_left

/-- **Theorem `thm:general-rec`(ii) 全谱完整集合等式**：
    $\Lambda^{(r,c,d)}(\mathbb{R}) = \frac{1}{c}\mathbb{Z}_{\ge 0} \cup \{\infty\}$。 -/
theorem poly_range_apprExponent (P : PolyRecData) :
    Set.range P.polyApprExponent =
      {y : ℝ≥0∞ | ∃ k : ℕ, y = ENNReal.ofReal ((k : ℝ) / (P.c : ℝ))} ∪ {⊤} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    by_cases htop : P.polyApprExponent x = ⊤
    · exact Or.inr htop
    · left
      set rVal := (P.polyApprExponent x).toReal
      have hcpos : (0 : ℝ) < (P.c : ℝ) := by exact_mod_cast P.hc
      set m : ℤ := ⌊(P.c : ℝ) * rVal⌋
      have hm_nn : 0 ≤ m := Int.floor_nonneg.mpr (mul_nonneg (le_of_lt hcpos) ENNReal.toReal_nonneg)
      set k : ℕ := m.toNat
      have hk_cast : (k : ℤ) = m := Int.toNat_of_nonneg hm_nn
      have hk_le : (k : ℝ) / (P.c : ℝ) ≤ rVal := by
        have h1 : (m : ℝ) ≤ (P.c : ℝ) * rVal := Int.floor_le _
        have h2 : (k : ℝ) = (m : ℝ) := by exact_mod_cast hk_cast
        rw [h2]; exact (div_le_iff₀' hcpos).mpr h1
      have hk1_gt : rVal < ((k : ℝ) + 1) / (P.c : ℝ) := by
        have h1 : (P.c : ℝ) * rVal < (m : ℝ) + 1 := Int.lt_floor_add_one _
        have h2 : (k : ℝ) = (m : ℝ) := by exact_mod_cast hk_cast
        rw [h2]; exact (lt_div_iff₀' hcpos).mpr h1
      have h_eq : rVal = (k : ℝ) / (P.c : ℝ) := by
        by_contra hne
        have hlt : (k : ℝ) / (P.c : ℝ) < rVal := lt_of_le_of_ne hk_le (Ne.symm hne)
        have hgap := P.poly_spectral_gap_open_interval k hlt hk1_gt x
        rw [ENNReal.ofReal_toReal htop] at hgap
        exact hgap rfl
      refine ⟨k, ?_⟩
      dsimp [rVal] at h_eq
      rw [← ENNReal.ofReal_toReal htop, h_eq]
  · rintro (⟨k, rfl⟩ | htop)
    · by_cases hk0 : k = 0
      · subst hk0
        refine ⟨0, ?_⟩
        have h0 := P.polyWeightedExponent_eq_zero_of_mem_latticePoly P.zero_mem_latticePoly (P.r : ℝ)
        simpa [polyApprExponent] using h0
      · exact ⟨P.xPlusPoly k, P.polyApprExponent_xPlusPoly (by omega)⟩
    · rw [Set.mem_singleton_iff.mp htop]
      have hvol : 0 < MeasureTheory.volume ({x : ℝ | P.polyApprExponent x = ⊤} ∩ Set.Icc (0 : ℝ) 1) := by
        rw [P.poly_volume_infiniteLevel_Icc 0 1]
        norm_num
      have hne : ({x : ℝ | P.polyApprExponent x = ⊤} ∩ Set.Icc (0 : ℝ) 1).Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty.mp hempty, measure_empty] at hvol
        exact lt_irrefl 0 hvol
      obtain ⟨x, hx, _⟩ := hne
      exact ⟨x, hx⟩

end PolyRecData

end

end TrichotomyAndPolyExtension

/-! ## 公理审计（必须全部仅依赖 `[propext, Classical.choice, Quot.sound]`，零 `sorryAx`） -/

#print axioms TrichotomyAndPolyExtension.xPlus_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.neg_xPlus_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.add_latticeL_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.signedExactLimitSet_pos_eq_coset
#print axioms TrichotomyAndPolyExtension.signedExactLimitSet_neg_eq_coset
#print axioms TrichotomyAndPolyExtension.signedExactLimitSet_zero_eq_latticeL
#print axioms TrichotomyAndPolyExtension.signedExactLimitSet_empty_of_not_quarter_int
#print axioms TrichotomyAndPolyExtension.trichotomy_part_iii_complete
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_Q_ge_factorial
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_pow_div_Q_tendsto_zero
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_Q_eq_lincomb
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_casorati
#print axioms TrichotomyAndPolyExtension.PolyRecData.alphaU_error_bound
#print axioms TrichotomyAndPolyExtension.PolyRecData.alphaV_error_bound
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_alpha_linear_relation
#print axioms TrichotomyAndPolyExtension.PolyRecData.theta_irrational
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_dist_le_of_mem_latticePoly
#print axioms TrichotomyAndPolyExtension.PolyRecData.polyWeightedExponent_eq_zero_of_mem_latticePoly
#print axioms TrichotomyAndPolyExtension.PolyRecData.polyApprExponent_eq_zero_tfae
#print axioms TrichotomyAndPolyExtension.PolyRecData.polyApprExponent_eq_zero_iff_mem_latticePoly
#print axioms TrichotomyAndPolyExtension.PolyRecData.polyApprExponent_eq_zero_iff_defect_zero
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_signed_defect_approx
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_abs_defect_approx
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_jr_mul_eps_tendsto_of_defect_const
#print axioms TrichotomyAndPolyExtension.PolyRecData.polyApprExponent_xPlusPoly
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_spectral_gap_open_interval
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_levelSet_eq_on_gap
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_levelSet_below_eq_lattice
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_signed_exact_limit_iff_defect_const
#print axioms TrichotomyAndPolyExtension.PolyRecData.xPlusPoly_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.PolyRecData.neg_xPlusPoly_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_sub_mem_latticePoly_of_same_signed_limit
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_add_latticePoly_mem_signedExactLimitSet
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_trichotomy_part_iii_complete
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_supercritical_levelSet_eq_lattice
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_supercritical_dimH_zero
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_supercritical_empty_neg
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_dimH_levelSet_finite
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_dimH_finiteLevel_zero
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_volume_finiteLevel_zero
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_ae_apprExponent_eq_top
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_volume_infiniteLevel_Icc
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_dimH_infiniteLevel_inter_Icc_eq_one
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_dimH_infiniteLevel_eq_one
#print axioms TrichotomyAndPolyExtension.PolyRecData.poly_range_apprExponent
