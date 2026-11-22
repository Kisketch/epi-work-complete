import Mathlib
import EpiFormal.Classification
import EpiFormal.SpectralGap
import EpiFormal.ThresholdAttained
import EpiFormal.QuarterPointFinal

/-!
# 全谱完全离散化、正能级精确三分法与一般 (cj+d) 递推推广（FullSpectrumDiscrete）

本模块在 Lean 4 中形式化论文二（第二阶段：沿 e 收敛子分母的逼近谱隙与水平集维数）的三个核心升级结果：
1. **一般线性增长递推 $Q_{j+1} = (c j + d) Q_j + Q_{j-1}$ 的整数差商逼近引理**：
   若误差序列 $u_j \to 0$ 且整数缺陷满足 $D_j = (c j + d) u_j - u_{j+1} + u_{j-1} \in \mathbb{Z}$，
   则 $D_j - c j u_j \to 0$ 且 $|D_j| - c j |u_j| \to 0$。
2. **整数序列离散刚性引理与无穷等距谱隙排除**：
   若整数序列 $n_j \in \mathbb{Z}$ 与实数序列 $y_j$ 满足 $n_j - y_j \to 0$：
   - **无穷等距开谱隙排除**：对任意整数 $k \in \mathbb{Z}$ 与开区间内的实数 $L \in (k, k+1)$，
     既不可能有 $y_j \to L$，也不可能有 $\limsup_{j\to\infty} y_j = L$（以标准上极限特征刻画：
     不存在任何序列 $y_j$ 同时满足「最终 $y_j \le L + \varepsilon$」与「频繁 $y_j \ge L - \varepsilon$」）。
   - **极限整值刚性**：若 $y_j \to k$（$k \in \mathbb{Z}$），则最终 $n_j = k$。
3. **专门化到 Euler 分母递推（$c = 4, d = 2$）的全谱完全离散化与正能级 $k/4$ 三分法代数骨架**：
   - 只要 $\varepsilon_j(x) \to 0$（对一切 $\Lambda(x) < \infty$ 成立），就有
     $\mathrm{defect}(x, j) - 4 j \varepsilon_j(x) \to 0$ 及
     $|\mathrm{defect}(x, j)| - 4 j \|Q_j x\| \to 0$；
   - **全谱离散化（无穷等距谱隙族）**：对任意整数 $k \ge 0$ 与 $L \in (k/4, (k+1)/4)$，
     开区间 $(k/4, (k+1)/4)$ 为 $\Lambda$ 的无条件空谱隙（$\Lambda(x) \ne L$），
     从而 $\Lambda(\mathbb{R}) \subseteq \frac{1}{4}\mathbb{Z}_{\ge 0} \cup \{\infty\}$；
   - **正能级 $k/4$（$k \ge 1$）精确三分法**：
     1. 上极限集 $\Lambda(x) \le k/4$：最终 $|\mathrm{defect}(x, j)| \le k$（$2k+1$ 分支字母表 $\{-k,\dots,k\}$）；
     2. 无符号精确极限集 $\lim_{j\to\infty} j\|Q_j x\| = k/4$：最终 $|\mathrm{defect}(x, j)| = k$，
        等价于 $\mathrm{defect}(x, j) \in \{-k, k\}$（普适 $2$ 分支字母表，与 $k \ge 1$ 无关）；
     3. 有符号精确极限集 $\lim_{j\to\infty} j \varepsilon_j(x) = d/4$（$d \in \{\pm k\}$）：
        最终 $\mathrm{defect}(x, j) = d$（唯一尾分支）；若 $x, y$ 具有同一有符号极限，
        则最终 $\mathrm{defect}(x, j) = \mathrm{defect}(y, j)$，且存在单格陪集关系 $x - y \in L = \mathbb{Z} + \mathbb{Z}\frac{e+1}{2}$。
-/

open Real Filter Topology Set Classification SpectralGap

namespace FullSpectrumDiscrete

noncomputable section

/-! ## 第一部分：一般线性增长递推 $Q_{j+1} = (c j + d) Q_j + Q_{j-1}$ 的差商逼近 -/

/-- 一般递推下的缺陷恒等式解耦：
    若 $D_j = (c j + d) u_j - u_{j+1} + u_{j-1}$，则 $D_j - c j u_j = d u_j - u_{j+1} + u_{j-1}$。 -/
lemma general_defect_sub_main {c d : ℝ} {u : ℕ → ℝ} {D : ℕ → ℤ} {j : ℕ}
    (hD : (D j : ℝ) = (c * (j : ℝ) + d) * u j - u (j + 1) + u (j - 1)) :
    (D j : ℝ) - c * (j : ℝ) * u j = d * u j - u (j + 1) + u (j - 1) := by
  linarith [hD]

/-- 下标前移 $j - 1 \to \infty$。 -/
lemma tendsto_sub_one_atTop : Tendsto (fun j : ℕ => j - 1) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro N
  exact ⟨N + 1, fun j hj => by omega⟩

/-- **一般 $(c j + d)$ 递推有符号差商逼近引理**：
    若 $u_j \to 0$ 且对 $j \ge 1$ 有 $D_j = (c j + d) u_j - u_{j+1} + u_{j-1}$，
    则 $(D_j - c j u_j) \to 0$。 -/
theorem general_signed_defect_approx {c d : ℝ} {u : ℕ → ℝ} {D : ℕ → ℤ}
    (hD : ∀ᶠ j in atTop, (D j : ℝ) = (c * (j : ℝ) + d) * u j - u (j + 1) + u (j - 1))
    (hu : Tendsto u atTop (nhds 0)) :
    Tendsto (fun j : ℕ => (D j : ℝ) - c * (j : ℝ) * u j) atTop (nhds 0) := by
  have hu_next : Tendsto (fun j : ℕ => u (j + 1)) atTop (nhds 0) :=
    hu.comp (tendsto_add_atTop_nat 1)
  have hu_prev : Tendsto (fun j : ℕ => u (j - 1)) atTop (nhds 0) :=
    hu.comp tendsto_sub_one_atTop
  have hdu : Tendsto (fun j : ℕ => d * u j) atTop (nhds 0) := by
    simpa using hu.const_mul d
  have hrhs : Tendsto (fun j : ℕ => d * u j - u (j + 1) + u (j - 1)) atTop (nhds 0) := by
    simpa using (hdu.sub hu_next).add hu_prev
  apply hrhs.congr'
  filter_upwards [hD] with j hj
  exact (general_defect_sub_main hj).symm

/-- **一般 $(c j + d)$ 递推无符号差商逼近引理**：
    若 $c \ge 0$、$u_j \to 0$ 且最终 $D_j = (c j + d) u_j - u_{j+1} + u_{j-1}$，
    则 $(|D_j| - c j |u_j|) \to 0$。 -/
theorem general_abs_defect_approx {c d : ℝ} (hc : 0 ≤ c) {u : ℕ → ℝ} {D : ℕ → ℤ}
    (hD : ∀ᶠ j in atTop, (D j : ℝ) = (c * (j : ℝ) + d) * u j - u (j + 1) + u (j - 1))
    (hu : Tendsto u atTop (nhds 0)) :
    Tendsto (fun j : ℕ => |(D j : ℝ)| - c * (j : ℝ) * |u j|) atTop (nhds 0) := by
  have hsigned := general_signed_defect_approx hD hu
  have habs_signed : Tendsto (fun j : ℕ => |(D j : ℝ) - c * (j : ℝ) * u j|) atTop (nhds 0) := by
    simpa using hsigned.abs
  have hneg : Tendsto (fun j : ℕ => -|(D j : ℝ) - c * (j : ℝ) * u j|) atTop (nhds 0) := by
    simpa using habs_signed.neg
  have hbound : ∀ j : ℕ, |(|(D j : ℝ)| - c * (j : ℝ) * |u j|)| ≤ |(D j : ℝ) - c * (j : ℝ) * u j| := by
    intro j
    have hcj : 0 ≤ c * (j : ℝ) := mul_nonneg hc (Nat.cast_nonneg j)
    have hmul : c * (j : ℝ) * |u j| = |c * (j : ℝ) * u j| := by
      rw [abs_mul, abs_of_nonneg hcj]
    rw [hmul]
    exact abs_abs_sub_abs_le_abs_sub (D j : ℝ) (c * (j : ℝ) * u j)
  have hlo : ∀ᶠ j in atTop, -|(D j : ℝ) - c * (j : ℝ) * u j| ≤ |(D j : ℝ)| - c * (j : ℝ) * |u j| := by
    filter_upwards with j
    exact (abs_le.mp (hbound j)).1
  have hhi : ∀ᶠ j in atTop, |(D j : ℝ)| - c * (j : ℝ) * |u j| ≤ |(D j : ℝ) - c * (j : ℝ) * u j| := by
    filter_upwards with j
    exact (abs_le.mp (hbound j)).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg habs_signed hlo hhi

/-- 充分大的 $j$ 下 $|u_j| \le C / j$ 蕴涵 $u_j \to 0$。 -/
lemma tendsto_zero_of_eventually_abs_le_div {u : ℕ → ℝ} {C : ℝ}
    (hu : ∀ᶠ j : ℕ in atTop, |u j| ≤ C / (j : ℝ)) :
    Tendsto u atTop (nhds 0) := by
  have hdiv : Tendsto (fun j : ℕ => |C| / (j : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hneg : Tendsto (fun j : ℕ => -(|C| / (j : ℝ))) atTop (nhds 0) := by
    simpa using hdiv.neg
  have hbound : ∀ᶠ j : ℕ in atTop, |u j| ≤ |C| / (j : ℝ) := by
    filter_upwards [hu] with j hj
    have hC : C ≤ |C| := le_abs_self C
    have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    exact le_trans hj (div_le_div_of_nonneg_right hC hjnn)
  have hlo : ∀ᶠ j : ℕ in atTop, -(|C| / (j : ℝ)) ≤ u j := by
    filter_upwards [hbound] with j hj
    exact (abs_le.mp hj).1
  have hhi : ∀ᶠ j : ℕ in atTop, u j ≤ |C| / (j : ℝ) := by
    filter_upwards [hbound] with j hj
    exact (abs_le.mp hj).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hdiv hlo hhi

/-! ## 第二部分：整数序列离散刚性引理与谱隙排除 -/

/-- 任意整数 $n \in \mathbb{Z}$ 到开区间 $(k, k+1)$ 内实数 $L$ 的距离至少为
    $\min(L - k, k + 1 - L) > 0$。 -/
lemma int_dist_open_unit_interval (k n : ℤ) {L : ℝ}
    (hkL : (k : ℝ) < L) (hLk1 : L < (k : ℝ) + 1) :
    min (L - (k : ℝ)) ((k : ℝ) + 1 - L) ≤ |(n : ℝ) - L| := by
  by_cases hnk : n ≤ k
  · have hnkR : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk
    have hpos : 0 < L - (n : ℝ) := by linarith
    have habs : |(n : ℝ) - L| = L - (n : ℝ) := by
      rw [abs_sub_comm, abs_of_pos hpos]
    rw [habs]
    exact le_trans (min_le_left _ _) (by linarith)
  · have hkn1 : k + 1 ≤ n := by omega
    have hkn1R : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hkn1
    have hpos : 0 ≤ (n : ℝ) - L := by linarith
    have habs : |(n : ℝ) - L| = (n : ℝ) - L := abs_of_nonneg hpos
    rw [habs]
    exact le_trans (min_le_right _ _) (by linarith)

/-- **整数邻近序列的开区间极限排除**：
    若 $n_j - y_j \to 0$（$n_j \in \mathbb{Z}$），则对任何 $k \in \mathbb{Z}$ 和 $L \in (k, k+1)$，
    不可能有 $y_j \to L$。 -/
theorem not_tendsto_open_interval_of_int_approx {n : ℕ → ℤ} {y : ℕ → ℝ}
    (happrox : Tendsto (fun j : ℕ => (n j : ℝ) - y j) atTop (nhds 0))
    (k : ℤ) {L : ℝ} (hkL : (k : ℝ) < L) (hLk1 : L < (k : ℝ) + 1) :
    ¬ Tendsto y atTop (nhds L) := by
  intro hy
  have hn : Tendsto (fun j : ℕ => (n j : ℝ) - L) atTop (nhds 0) := by
    have hsum := happrox.add (hy.sub_const L)
    simpa using hsum
  set δ := min (L - (k : ℝ)) ((k : ℝ) + 1 - L)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hev : ∀ᶠ j : ℕ in atTop, |(n j : ℝ) - L| < δ := by
    have habs : Tendsto (fun j : ℕ => |(n j : ℝ) - L|) atTop (nhds 0) := by
      simpa using hn.abs
    exact habs.eventually (Iio_mem_nhds hδ)
  obtain ⟨j, hj⟩ := hev.exists
  have hge := int_dist_open_unit_interval k (n j) hkL hLk1
  linarith

/-- **整数邻近序列的最终上界向下取整刚性**：
    若 $n_j - y_j \to 0$ 且存在严格小于 $k + 1$ 的实数 $B < k + 1$ 使最终 $y_j \le B$，
    则最终 $n_j \le k$，进而对一切 $\varepsilon > 0$ 最终 $y_j \le k + \varepsilon$。 -/
theorem eventually_int_le_of_eventually_le_lt_succ {n : ℕ → ℤ} {y : ℕ → ℝ}
    (happrox : Tendsto (fun j : ℕ => (n j : ℝ) - y j) atTop (nhds 0))
    (k : ℤ) {B : ℝ} (hB : B < (k : ℝ) + 1)
    (hyB : ∀ᶠ j : ℕ in atTop, y j ≤ B) :
    ∀ᶠ j : ℕ in atTop, n j ≤ k := by
  have hgap : 0 < (k : ℝ) + 1 - B := by linarith
  have hev : ∀ᶠ j : ℕ in atTop, (n j : ℝ) - y j < (k : ℝ) + 1 - B :=
    happrox.eventually (Iio_mem_nhds hgap)
  filter_upwards [hev, hyB] with j hj1 hj2
  have hlt : (n j : ℝ) < (k : ℝ) + 1 := by linarith
  have hltZ : n j < k + 1 := by exact_mod_cast hlt
  omega

/-- **整数邻近序列的开区间上极限排除（离散谱隙核心引理）**：
    若 $n_j - y_j \to 0$（$n_j \in \mathbb{Z}$），且 $L \in (k, k+1)$，
    则 $y_j$ 不可能以 $L$ 为上极限：具体地，若对某 $B \in (L, k+1)$ 最终 $y_j \le B$，
    则对任何 $A \in (k, L)$，最终必有 $y_j \le A$（从而不可能无穷多次 $y_j > A$）。 -/
theorem eventually_le_of_int_approx_in_gap {n : ℕ → ℤ} {y : ℕ → ℝ}
    (happrox : Tendsto (fun j : ℕ => (n j : ℝ) - y j) atTop (nhds 0))
    (k : ℤ) {A B : ℝ} (hkA : (k : ℝ) < A) (hB : B < (k : ℝ) + 1)
    (hyB : ∀ᶠ j : ℕ in atTop, y j ≤ B) :
    ∀ᶠ j : ℕ in atTop, y j ≤ A := by
  have hnle : ∀ᶠ j : ℕ in atTop, n j ≤ k :=
    eventually_int_le_of_eventually_le_lt_succ happrox k hB hyB
  have hneg : Tendsto (fun j : ℕ => y j - (n j : ℝ)) atTop (nhds 0) := by
    have := happrox.neg
    simpa using this
  have hgap : 0 < A - (k : ℝ) := by linarith
  have hev : ∀ᶠ j : ℕ in atTop, y j - (n j : ℝ) < A - (k : ℝ) :=
    hneg.eventually (Iio_mem_nhds hgap)
  filter_upwards [hnle, hev] with j hnj hj
  have hnjR : (n j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnj
  linarith

/-- **整数邻近序列的整点极限刚性（最终常值化）**：
    若 $n_j - y_j \to 0$ 且 $y_j \to k$（$k \in \mathbb{Z}$），则最终 $n_j = k$。 -/
theorem eventually_eq_int_of_tendsto {n : ℕ → ℤ} {y : ℕ → ℝ}
    (happrox : Tendsto (fun j : ℕ => (n j : ℝ) - y j) atTop (nhds 0))
    (k : ℤ) (hy : Tendsto y atTop (nhds (k : ℝ))) :
    ∀ᶠ j : ℕ in atTop, n j = k := by
  have hn : Tendsto (fun j : ℕ => (n j : ℝ) - (k : ℝ)) atTop (nhds 0) := by
    have hsum := happrox.add (hy.sub_const (k : ℝ))
    simpa using hsum
  have habs : Tendsto (fun j : ℕ => |((n j - k : ℤ) : ℝ)|) atTop (nhds 0) := by
    have h1 := hn.abs
    simpa using h1
  have hlt : ∀ᶠ j : ℕ in atTop, |((n j - k : ℤ) : ℝ)| < 1 :=
    habs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hzero := Classification.int_eventually_zero_of_abs_lt_one hlt
  filter_upwards [hzero] with j hj
  omega

/-- **整数绝对值常值等价于二值分支**：
    对正整数 $k \in \mathbb{N}$ 与整数 $d \in \mathbb{Z}$，$|d| = k \iff d = k \lor d = -k$。 -/
lemma int_abs_eq_iff (d : ℤ) (k : ℕ) :
    |(d : ℝ)| = (k : ℝ) ↔ d = (k : ℤ) ∨ d = -(k : ℤ) := by
  have hcast : |(d : ℝ)| = ((|d| : ℤ) : ℝ) := (Int.cast_abs (R := ℝ)).symm
  rw [hcast]
  constructor
  · intro h
    have hZ : |d| = (k : ℤ) := by exact_mod_cast h
    exact abs_eq (Nat.cast_nonneg k) |>.mp hZ
  · intro h
    have hZ : |d| = (k : ℤ) := abs_eq (Nat.cast_nonneg k) |>.mpr h
    exact_mod_cast hZ

/-! ## 第三部分：专门化到 Euler 收敛子分母 $Q_{j+1} = (4j+2)Q_j + Q_{j-1}$ -/

/-- Euler 分母递推满足一般递推条件（$c = 4, d = 2, u_j = \varepsilon_j(x), D_j = \mathrm{defect}(x, j)$）。 -/
lemma euler_defect_eq_general (x : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      (defect x j : ℝ) = (4 * (j : ℝ) + 2) * eps x j - eps x (j + 1) + eps x (j - 1) := by
  filter_upwards [eventually_ge_atTop 1] with j hj
  have h := defect_identity x j hj
  linarith [h]

/-- **Euler 有符号缺陷渐近等式**：
    若 $\varepsilon_j(x) \to 0$，则 $\mathrm{defect}(x, j) - 4 j \varepsilon_j(x) \to 0$。 -/
theorem euler_signed_defect_approx (x : ℝ) (hε : Tendsto (eps x) atTop (nhds 0)) :
    Tendsto (fun j : ℕ => (defect x j : ℝ) - 4 * (j : ℝ) * eps x j) atTop (nhds 0) :=
  general_signed_defect_approx (euler_defect_eq_general x) hε

/-- **Euler 无符号缺陷渐近等式**：
    若 $\varepsilon_j(x) \to 0$，则 $|\mathrm{defect}(x, j)| - 4 j \|Q_j x\| \to 0$。 -/
theorem euler_abs_defect_approx (x : ℝ) (hε : Tendsto (eps x) atTop (nhds 0)) :
    Tendsto (fun j : ℕ => |(defect x j : ℝ)| - 4 * apprSeq x j) atTop (nhds 0) := by
  have h := general_abs_defect_approx (by norm_num : (0 : ℝ) ≤ 4) (euler_defect_eq_general x) hε
  apply h.congr'
  filter_upwards with j
  have heps : |eps x j| = distToNearestInt ((Qsel j : ℝ) * x) := rfl
  simp only [apprSeq, heps]
  ring

/-- 有限上极限 $\Lambda(x) < \top$ 蕴涵 $\varepsilon_j(x) \to 0$。 -/
lemma eps_tendsto_zero_of_apprExponent_ne_top (x : ℝ) (hfin : apprExponent x ≠ ⊤) :
    Tendsto (eps x) atTop (nhds 0) := by
  set C := (apprExponent x).toReal + 1
  have hlt : apprExponent x < ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hfin]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
    linarith
  have hev : ∀ᶠ j : ℕ in atTop, apprSeqE x j < ENNReal.ofReal C :=
    eventually_lt_of_limsup_lt hlt
  have hbound : ∀ᶠ j : ℕ in atTop, |eps x j| ≤ C / (j : ℝ) := by
    filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
    have hCpos : 0 < C := by positivity
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hle : apprSeq x j ≤ C := le_of_lt ((ENNReal.ofReal_lt_ofReal_iff hCpos).mp hj)
    have heps : |eps x j| = distToNearestInt ((Qsel j : ℝ) * x) := rfl
    have hmul : (j : ℝ) * |eps x j| ≤ C := by simpa [apprSeq, heps] using hle
    exact (le_div_iff₀ hjR).mpr (by linarith)
  exact tendsto_zero_of_eventually_abs_le_div hbound

/-- **定理 1（全谱完全离散化与无穷等距空谱隙）**：
    对每个非负整数 $k \in \mathbb{N}$ 及开区间 $(k/4, (k+1)/4)$ 内的任意实数 $L$，
    不存在 $x \in \mathbb{R}$ 使得 $\Lambda(x) = \mathrm{ENNReal.ofReal}(L)$。
    结合 $\Lambda(x) \ge 0$ 与各能级 $k/4$ 可达，这意味着
    $\Lambda(\mathbb{R}) = \frac{1}{4}\mathbb{Z}_{\ge 0} \cup \{\infty\}$，
    且每个开区间 $(k/4, (k+1)/4)$ 均为 $\Lambda$ 的无条件空谱隙。 -/
theorem spectral_gap_open_interval (k : ℕ) {L : ℝ}
    (hkL : (k : ℝ) / 4 < L) (hLk1 : L < ((k : ℝ) + 1) / 4) (x : ℝ) :
    apprExponent x ≠ ENNReal.ofReal L := by
  intro hEq
  have hLpos : 0 < L := by
    have : (0 : ℝ) ≤ (k : ℝ) / 4 := by positivity
    linarith
  have hfin : apprExponent x ≠ ⊤ := by
    rw [hEq]; exact ENNReal.ofReal_ne_top
  have hε : Tendsto (eps x) atTop (nhds 0) := eps_tendsto_zero_of_apprExponent_ne_top x hfin
  have happrox : Tendsto (fun j : ℕ => (((|defect x j| : ℤ) : ℝ) - 4 * apprSeq x j)) atTop (nhds 0) := by
    have h := euler_abs_defect_approx x hε
    apply h.congr'
    filter_upwards with j
    have hcast : (((|defect x j| : ℤ) : ℝ)) = |(defect x j : ℝ)| :=
      Int.cast_abs (R := ℝ)
    rw [hcast]
  -- 取 B = (4L + (k+1))/2 ∈ (4L, k+1) 与 A = (k + 4L)/2 ∈ (k, 4L)
  set B := (4 * L + ((k : ℝ) + 1)) / 2
  set A := ((k : ℝ) + 4 * L) / 2
  have hLB : L < B / 4 := by simp only [B]; linarith
  have hAL : A / 4 < L := by simp only [A]; linarith
  have hBpos : 0 < B / 4 := lt_trans hLpos hLB
  have hApos : 0 < A / 4 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    simp only [A]; linarith
  -- 由 Lam(x) = ofReal L < ofReal (B/4)，最终 apprSeq x j ≤ B/4，故 4 * apprSeq x j ≤ B
  have hltB : apprExponent x < ENNReal.ofReal (B / 4) := by
    rw [hEq]
    exact (ENNReal.ofReal_lt_ofReal_iff hBpos).mpr hLB
  have hevB : ∀ᶠ j : ℕ in atTop, apprSeqE x j < ENNReal.ofReal (B / 4) :=
    eventually_lt_of_limsup_lt hltB
  have hyB : ∀ᶠ j : ℕ in atTop, 4 * apprSeq x j ≤ B := by
    filter_upwards [hevB] with j hj
    have h1 : apprSeq x j < B / 4 := (ENNReal.ofReal_lt_ofReal_iff hBpos).mp hj
    linarith
  have hkA : ((k : ℤ) : ℝ) < A := by simp only [Int.cast_natCast, A]; linarith
  have hBk1 : B < ((k : ℤ) : ℝ) + 1 := by simp only [Int.cast_natCast, B]; linarith
  have hyA : ∀ᶠ j : ℕ in atTop, 4 * apprSeq x j ≤ A :=
    eventually_le_of_int_approx_in_gap happrox (k : ℤ) hkA hBk1 hyB
  -- 于是最终 apprSeqE x j ≤ ofReal (A/4)，导出 Lam(x) ≤ ofReal (A/4) < ofReal L，矛盾！
  have hevA : ∀ᶠ j : ℕ in atTop, apprSeqE x j ≤ ENNReal.ofReal (A / 4) := by
    filter_upwards [hyA] with j hj
    unfold apprSeqE
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hleA : apprExponent x ≤ ENNReal.ofReal (A / 4) := limsup_le_of_le (by isBoundedDefault) hevA
  rw [hEq] at hleA
  have hltA : ENNReal.ofReal (A / 4) < ENNReal.ofReal L :=
    (ENNReal.ofReal_lt_ofReal_iff hLpos).mpr hAL
  exact not_lt_of_ge hleA hltA

/-- **推论：次能级水平集在谱隙内恒定（阶梯坍缩）**：
    对任意 $k \in \mathbb{N}$ 与 $c \in [k/4, (k+1)/4)$，
    $\Lambda(x) \le c \iff \Lambda(x) \le k/4$，且最终 $|\mathrm{defect}(x, j)| \le k$。 -/
theorem eventually_abs_defect_le_of_apprExponent_le (k : ℕ) {c : ℝ}
    (hc : c < ((k : ℝ) + 1) / 4) (x : ℝ)
    (hx : apprExponent x ≤ ENNReal.ofReal c) :
    ∀ᶠ j : ℕ in atTop, |defect x j| ≤ (k : ℤ) := by
  have hfin : apprExponent x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hx ENNReal.ofReal_lt_top)
  have hε : Tendsto (eps x) atTop (nhds 0) := eps_tendsto_zero_of_apprExponent_ne_top x hfin
  have happrox : Tendsto (fun j : ℕ => (((|defect x j| : ℤ) : ℝ) - 4 * apprSeq x j)) atTop (nhds 0) := by
    have h := euler_abs_defect_approx x hε
    apply h.congr'
    filter_upwards with j
    have hcast : (((|defect x j| : ℤ) : ℝ)) = |(defect x j : ℝ)| :=
      Int.cast_abs (R := ℝ)
    rw [hcast]
  set B := (max (4 * c) (k : ℝ) + ((k : ℝ) + 1)) / 2
  have hBk1 : B < ((k : ℤ) : ℝ) + 1 := by
    simp only [Int.cast_natCast, B]
    have : max (4 * c) (k : ℝ) < (k : ℝ) + 1 := max_lt (by linarith) (by linarith)
    linarith
  have hcB : c < B / 4 := by
    simp only [B]
    have h1 : 4 * c ≤ max (4 * c) (k : ℝ) := le_max_left _ _
    have h2 : max (4 * c) (k : ℝ) < (k : ℝ) + 1 := max_lt (by linarith) (by linarith)
    linarith
  have hBpos : 0 < B / 4 := by
    simp only [B]
    have h1 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h2 : (k : ℝ) ≤ max (4 * c) (k : ℝ) := le_max_right _ _
    linarith
  have hltB : apprExponent x < ENNReal.ofReal (B / 4) :=
    lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff hBpos).mpr hcB)
  have hevB : ∀ᶠ j : ℕ in atTop, apprSeqE x j < ENNReal.ofReal (B / 4) :=
    eventually_lt_of_limsup_lt hltB
  have hyB : ∀ᶠ j : ℕ in atTop, 4 * apprSeq x j ≤ B := by
    filter_upwards [hevB] with j hj
    have h1 : apprSeq x j < B / 4 := (ENNReal.ofReal_lt_ofReal_iff hBpos).mp hj
    linarith
  exact eventually_int_le_of_eventually_le_lt_succ happrox (k : ℤ) hBk1 hyB

/-- **水平集在每个谱隙 $[k/4, (k+1)/4)$ 上恒等**：
    对一切 $c \in [k/4, (k+1)/4)$，`levelSet (ofReal c) = levelSet (ofReal (k/4))`。 -/
theorem levelSet_eq_on_gap (k : ℕ) {c : ℝ}
    (hkc : (k : ℝ) / 4 ≤ c) (hc : c < ((k : ℝ) + 1) / 4) :
    levelSet (ENNReal.ofReal c) = levelSet (ENNReal.ofReal ((k : ℝ) / 4)) := by
  ext x
  simp only [levelSet, mem_ofPred_eq]
  constructor
  · intro hx
    have hfin : apprExponent x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hx ENNReal.ofReal_lt_top)
    have hε : Tendsto (eps x) atTop (nhds 0) := eps_tendsto_zero_of_apprExponent_ne_top x hfin
    have happrox : Tendsto (fun j : ℕ => (((|defect x j| : ℤ) : ℝ) - 4 * apprSeq x j)) atTop (nhds 0) := by
      have h := euler_abs_defect_approx x hε
      apply h.congr'
      filter_upwards with j
      have hcast : (((|defect x j| : ℤ) : ℝ)) = |(defect x j : ℝ)| :=
        Int.cast_abs (R := ℝ)
      rw [hcast]
    have hdef : ∀ᶠ j : ℕ in atTop, |defect x j| ≤ (k : ℤ) :=
      eventually_abs_defect_le_of_apprExponent_le k hc x hx
    -- 对任意 ε > 0，最终 4 * apprSeq x j ≤ k + 4ε，即 apprSeq x j ≤ k/4 + ε
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hεpos _
    have hneg : Tendsto (fun j : ℕ => 4 * apprSeq x j - ((|defect x j| : ℤ) : ℝ)) atTop (nhds 0) := by
      simpa using happrox.neg
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hεpos
    have hev : ∀ᶠ j : ℕ in atTop, 4 * apprSeq x j - ((|defect x j| : ℤ) : ℝ) < 4 * (ε : ℝ) :=
      hneg.eventually (Iio_mem_nhds (by positivity))
    have hev2 : ∀ᶠ j : ℕ in atTop, apprSeqE x j ≤ ENNReal.ofReal ((k : ℝ) / 4) + ε := by
      filter_upwards [hdef, hev] with j hj1 hj2
      have hj1R : (((|defect x j| : ℤ) : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hj1
      have hle : apprSeq x j ≤ (k : ℝ) / 4 + (ε : ℝ) := by linarith
      unfold apprSeqE
      calc ENNReal.ofReal (apprSeq x j)
          ≤ ENNReal.ofReal ((k : ℝ) / 4 + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal ((k : ℝ) / 4) + ENNReal.ofReal (ε : ℝ) :=
            ENNReal.ofReal_add (by positivity) (by positivity)
        _ = ENNReal.ofReal ((k : ℝ) / 4) + ε := by simp
    exact limsup_le_of_le (by isBoundedDefault) hev2
  · intro hx
    exact le_trans hx (ENNReal.ofReal_le_ofReal hkc)

/-! ## 第四部分：定理 2（正能级 $c = k/4$ 精确三分法） -/

/-- **三分法第二支（无符号精确极限集的二值刚性）**：
    对任意整数 $k \ge 0$，$j \|Q_j x\| \to k/4$ 当且仅当 $\varepsilon_j(x) \to 0$ 且
    最终 $\mathrm{defect}(x, j) \in \{-k, k\}$（对 $k \ge 1$ 每步恰有 2 个分支，与 $k$ 无关）。 -/
theorem unsigned_exact_limit_iff_defect_binary (x : ℝ) (k : ℕ) :
    Tendsto (apprSeq x) atTop (nhds ((k : ℝ) / 4)) ↔
      Tendsto (eps x) atTop (nhds 0) ∧
        ∀ᶠ j : ℕ in atTop, defect x j = (k : ℤ) ∨ defect x j = -(k : ℤ) := by
  constructor
  · intro hlim
    -- 由 j‖Q_j x‖ → k/4 知最终 |eps x j| ≤ (k/4 + 1)/j，故 eps x j → 0
    have hε : Tendsto (eps x) atTop (nhds 0) := by
      have hev : ∀ᶠ j : ℕ in atTop, apprSeq x j < (k : ℝ) / 4 + 1 :=
        hlim.eventually (Iio_mem_nhds (by linarith))
      have hbound : ∀ᶠ j : ℕ in atTop, |eps x j| ≤ ((k : ℝ) / 4 + 1) / (j : ℝ) := by
        filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
        have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
        have heps : |eps x j| = distToNearestInt ((Qsel j : ℝ) * x) := rfl
        have hmul : (j : ℝ) * |eps x j| ≤ (k : ℝ) / 4 + 1 := by
          simpa [apprSeq, heps] using le_of_lt hj
        exact (le_div_iff₀ hjR).mpr (by linarith)
      exact tendsto_zero_of_eventually_abs_le_div hbound
    have happrox : Tendsto (fun j : ℕ => (((|defect x j| : ℤ) : ℝ) - 4 * apprSeq x j)) atTop (nhds 0) := by
      have h := euler_abs_defect_approx x hε
      apply h.congr'
      filter_upwards with j
      have hcast : (((|defect x j| : ℤ) : ℝ)) = |(defect x j : ℝ)| :=
        Int.cast_abs (R := ℝ)
      rw [hcast]
    have h4lim : Tendsto (fun j : ℕ => 4 * apprSeq x j) atTop (nhds ((k : ℤ) : ℝ)) := by
      have h1 := hlim.const_mul 4
      have heq : 4 * ((k : ℝ) / 4) = ((k : ℤ) : ℝ) := by push_cast; ring
      rwa [heq] at h1
    have habs_eq : ∀ᶠ j : ℕ in atTop, |defect x j| = (k : ℤ) :=
      eventually_eq_int_of_tendsto happrox (k : ℤ) h4lim
    refine ⟨hε, ?_⟩
    filter_upwards [habs_eq] with j hj
    exact abs_eq (Nat.cast_nonneg k) |>.mp hj
  · rintro ⟨hε, hbin⟩
    have happrox := euler_abs_defect_approx x hε
    have habs_const : ∀ᶠ j : ℕ in atTop, |(defect x j : ℝ)| = (k : ℝ) := by
      filter_upwards [hbin] with j hj
      have hZ : |defect x j| = (k : ℤ) := abs_eq (Nat.cast_nonneg k) |>.mpr hj
      have hcast : |(defect x j : ℝ)| = ((|defect x j| : ℤ) : ℝ) :=
        (Int.cast_abs (R := ℝ)).symm
      rw [hcast]
      exact_mod_cast hZ
    have h4 : Tendsto (fun j : ℕ => 4 * apprSeq x j) atTop (nhds (k : ℝ)) := by
      have hconst : Tendsto (fun _ : ℕ => (k : ℝ)) atTop (nhds (k : ℝ)) := tendsto_const_nhds
      have hsub := hconst.sub happrox
      have hlim : (k : ℝ) - 0 = (k : ℝ) := by ring
      rw [hlim] at hsub
      apply hsub.congr'
      filter_upwards [habs_const] with j hj
      linarith
    have hdiv := h4.const_mul (1 / 4 : ℝ)
    have hgoal : (1 / 4 : ℝ) * (k : ℝ) = (k : ℝ) / 4 := by ring
    rw [hgoal] at hdiv
    apply hdiv.congr'
    filter_upwards with j
    ring

/-- **三分法第三支（有符号精确极限集的常值刚性）**：
    对任意整数 $d \in \mathbb{Z}$，$j \varepsilon_j(x) \to d/4$ 当且仅当
    $\varepsilon_j(x) \to 0$ 且最终 $\mathrm{defect}(x, j) = d$。 -/
theorem signed_exact_limit_iff_defect_const (x : ℝ) (d : ℤ) :
    Tendsto (fun j : ℕ => (j : ℝ) * eps x j) atTop (nhds ((d : ℝ) / 4)) ↔
      Tendsto (eps x) atTop (nhds 0) ∧ ∀ᶠ j : ℕ in atTop, defect x j = d := by
  constructor
  · intro hlim
    have hε : Tendsto (eps x) atTop (nhds 0) := by
      have habs := hlim.abs
      have hev : ∀ᶠ j : ℕ in atTop, |(j : ℝ) * eps x j| < |(d : ℝ) / 4| + 1 :=
        habs.eventually (Iio_mem_nhds (by linarith))
      have hbound : ∀ᶠ j : ℕ in atTop, |eps x j| ≤ (|(d : ℝ) / 4| + 1) / (j : ℝ) := by
        filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
        have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
        have hmul : (j : ℝ) * |eps x j| ≤ |(d : ℝ) / 4| + 1 := by
          have : |(j : ℝ) * eps x j| = (j : ℝ) * |eps x j| := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
          linarith
        exact (le_div_iff₀ hjR).mpr (by linarith)
      exact tendsto_zero_of_eventually_abs_le_div hbound
    have happrox := euler_signed_defect_approx x hε
    have h4lim : Tendsto (fun j : ℕ => 4 * (j : ℝ) * eps x j) atTop (nhds (d : ℝ)) := by
      have h1 := hlim.const_mul 4
      have heq : 4 * ((d : ℝ) / 4) = (d : ℝ) := by ring
      rw [heq] at h1
      apply h1.congr'
      filter_upwards with j
      ring
    exact ⟨hε, eventually_eq_int_of_tendsto happrox d h4lim⟩
  · rintro ⟨hε, hd⟩
    exact ThresholdAttained.j_mul_eps_tendsto x d hd hε

/-- **有符号精确极限集的陪集刚性定理（差落入格 $L = \mathbb{Z} + \mathbb{Z}\frac{e+1}{2}$）**：
    若 $x, y \in \mathbb{R}$ 满足同一有符号精确极限
    $\lim_{j\to\infty} j \varepsilon_j(x) = \lim_{j\to\infty} j \varepsilon_j(y) = d/4$（$d \in \mathbb{Z}$），
    则：
    1. 最终 $\mathrm{defect}(x, j) = \mathrm{defect}(y, j) = d$；
    2. 差值 $x - y \in L = \mathbb{Z} + \mathbb{Z}\frac{e+1}{2}$（因此每个非空有符号精确极限集
       严格包含于单个可数 $L$-陪集 $x_* + L$，其 Hausdorff 维数为 $0$）。 -/
theorem sub_mem_latticeL_of_same_signed_limit (x y : ℝ) (d : ℤ)
    (hx : Tendsto (fun j : ℕ => (j : ℝ) * eps x j) atTop (nhds ((d : ℝ) / 4)))
    (hy : Tendsto (fun j : ℕ => (j : ℝ) * eps y j) atTop (nhds ((d : ℝ) / 4))) :
    x - y ∈ latticeL := by
  -- j (eps x j - eps y j) → 0
  have hdiff : Tendsto (fun j : ℕ => (j : ℝ) * (eps x j - eps y j)) atTop (nhds 0) := by
    have hsub := hx.sub hy
    have h0 : (d : ℝ) / 4 - (d : ℝ) / 4 = 0 := by ring
    rw [h0] at hsub
    apply hsub.congr'
    filter_upwards with j
    ring
  have habs_diff : Tendsto (fun j : ℕ => (j : ℝ) * |eps x j - eps y j|) atTop (nhds 0) := by
    have h1 : Tendsto (fun j : ℕ => |(j : ℝ) * (eps x j - eps y j)|) atTop (nhds 0) := by
      simpa using hdiff.abs
    apply h1.congr'
    filter_upwards with j
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
  -- Q_j(x - y) = (M_j(x) - M_j(y)) + (eps x j - eps y j)，故 distToNearestInt(Q_j(x-y)) ≤ |eps x j - eps y j|
  have hdist_le : ∀ j : ℕ,
      distToNearestInt ((Qsel j : ℝ) * (x - y)) ≤ |eps x j - eps y j| := by
    intro j
    set K : ℤ := nearestInt ((Qsel j : ℝ) * x) - nearestInt ((Qsel j : ℝ) * y)
    have hId : (Qsel j : ℝ) * (x - y) - (K : ℝ) = eps x j - eps y j := by
      simp only [K, eps]
      push_cast
      ring
    rw [← hId]
    exact distToNearestInt_le ((Qsel j : ℝ) * (x - y)) K
  have hnonneg : ∀ᶠ j : ℕ in atTop,
      0 ≤ (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * (x - y)) := by
    filter_upwards with j
    exact mul_nonneg (Nat.cast_nonneg j) (distToNearestInt_nonneg _)
  have hupper : ∀ᶠ j : ℕ in atTop,
      (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * (x - y)) ≤ (j : ℝ) * |eps x j - eps y j| := by
    filter_upwards with j
    exact mul_le_mul_of_nonneg_left (hdist_le j) (Nat.cast_nonneg j)
  have htend0 : Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * (x - y)))
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds habs_diff hnonneg hupper
  exact (theorem2_classification (x - y)).mp htend0

/-- **有符号精确极限集的可数性与零维性**：
    对任意 $d \in \mathbb{Z}$，有符号精确极限集
    $E_{\mathrm{lim}}^{\mathrm{signed}}(d/4) := \{x \in \mathbb{R} : \lim_{j\to\infty} j \varepsilon_j(x) = d/4\}$
    是可数集，且其 Hausdorff 维数 $\dim_H E_{\mathrm{lim}}^{\mathrm{signed}}(d/4) = 0$。 -/
theorem signed_exact_limit_set_countable (d : ℤ) :
    {x : ℝ | Tendsto (fun j : ℕ => (j : ℝ) * eps x j) atTop (nhds ((d : ℝ) / 4))}.Countable := by
  set S := {x : ℝ | Tendsto (fun j : ℕ => (j : ℝ) * eps x j) atTop (nhds ((d : ℝ) / 4))}
  by_cases hne : S.Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    have hsub : S ⊆ (fun z : ℝ => x0 + z) '' latticeL := by
      intro x hx
      refine ⟨x - x0, sub_mem_latticeL_of_same_signed_limit x x0 d hx hx0, ?_⟩
      ring
    exact (latticeL_countable.image _).mono hsub
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.countable_empty

/-- 有符号精确极限集的 Hausdorff 维数恒为 0。 -/
theorem dimH_signed_exact_limit_set_zero (d : ℤ) :
    dimH {x : ℝ | Tendsto (fun j : ℕ => (j : ℝ) * eps x j) atTop (nhds ((d : ℝ) / 4))} = 0 :=
  (signed_exact_limit_set_countable d).dimH_zero

end

end FullSpectrumDiscrete
