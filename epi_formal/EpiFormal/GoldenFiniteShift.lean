import Mathlib
import EpiFormal.GoldenOrbitRigidity
import EpiFormal.GeneralEndpointRigidity

/-!
# Golden-orbit finite spectrum: three-family completeness assembly
# (`thm:golden-finite-shift`, Triage #3)

主算术结果的最后一块拼图：`thm:golden-finite-shift` 的三族完备性组装。
刚性件（`mobius_error_identity`、`GoldenOrbitRigidity` 全系、
`GoldenOrbitB2Rigidity`、`GeneralEndpointRigidity` 全系）均已核实（仅 Lean 基础公理），
本模块只读复用它们，形式化剩余的有限枚举完备性骨架。

## 与纸面证明（§4 Thm 4.14，p.1924–1962）的对应

- A 组（搜索界）：纸面 p.1924–1940。
  `search_bound_fixed_q`（固定 `q` 头分支 `q ≤ 2H+2`）、
  `search_bound_strong_a`（`θ ≠ φ-1` 时 `a ≤ H√5/2`）、
  `search_bound_moving_dist` + `search_bound_moving_offset`（移动偏移 `|d₀| ≤ 2H+1`）、
  `search_bound_gen_height`（`r>0` 通用高度界）、
  `search_bound_norm_cutoff`（`r=0, d₀=-1` 时由 `|F(1)| ≥ 1` 得 `a ≤ 5H(H+2)/4`）、
  `search_bound_suffix_m`（后缀分支 `(1-H)p√5 ≤ m ≤ (1+H)p√5`）。
- B 组（格点形）：纸面 p.1949–1955。
  `quadratic_tail_value_mem_lattice`（两头分支经 `2aθ = -c ± √5`、
  `h(θ) = 2a/√5` 化为 `|m/(D√5) - 1|`，符号不同时取 `m ↦ -m`）、
  `suffix_value_mem_lattice`（后缀分支经公分母 `D` 化为同形，要求 `p ∣ D`）。
- C 组（离散性）：纸面 p.1956–1960。
  `Dsqrt5_irrational`、`dist_int_pos`、`lattice_spectrum_pos_min`
  （正最小值 `‖D√5‖/(D√5)`）、`lattice_values_separated`
  （互异值之差 `≥ min(1, ‖2D√5‖)/(D√5)`，同侧差 `≥ 1/(D√5)`，异侧差 `≥ ‖2D√5‖/(D√5)`）。
- D 组（`H = 3` 前两值）：纸面 p.1960–1962。
  `first_two_below_three`（`θ = φ-1` 处移动偏移 `d₀ = 1, 2` 给出两个 `< 3` 的互异值，
  格点形为 `m = -1, -3`，`D = 1`）。
- E 组（三族定义与有限性）：`suffixCand`、`fixedCand`、`movingCand` 为三族候选集
  （容纳谓词 `divOk`/`fixedOk`/`movingOk` 为纸面接口：范数除子检验与轨道成员检查），
  各自有限（`latticeSlab_finite` 经 `mem_latticeSlab_of_abs_le`），各自格点化。
- F 组（条件组装）：`finite_shift_of_covers`（覆盖假设 ⟹ 有限交集 + 格点含入）、
  `finite_shift_separated`（覆盖假设 ⟹ 一致分离）。
  `suffix_divisor_candidates_finite` 把后缀除子有限性锚定到
  `GeneralEndpointRigidity.Muv_norm_ne_zero`（Part 4：商非零）。

## 诚实说明：仍为纸面接口的部分（未在本模块形式化）

1. 窗口相位提取（`thm:affine-window` 的锁定有理收敛子、周期与奇偶性）无 Lean 对应；
   三族容纳谓词与覆盖假设 `hcover` 即为该接口的形式化占位。
2. 有限枚举的逐分支 case 覆盖（后缀 `u` 端点公式的有限个 `η` 反演、
   头分支的 `q ≤ b_j/2` 与 `q > b_j/2` 穷举、`r = 0, d₀ = -1` 的多项式论证）为纸面证明；
   本模块证明“界成立 ⟹ 枚举有限”，不证明“枚举已穷举”。
3. `B ≥ 7` 的开放情形：纸面未给出 `B ≥ 7` 的 exact 值，
   本模块的界与离散性对一切 `B` 成立，但 exact 常数仍开放（稿件自承）。
4. 达到性（每个候选值确被某高度趋于无穷的轨道尾实现，经 Bugeaud (3.4)）为纸面证明。
5. 数值断言另经 `mpmath` 50 位精度独立复算（`V₁ ≈ 1.4472135954…`、
   `V₂ ≈ 2.3416407864…`，均 `< 3` 且互异，格点形式吻合），Lean 内再以
   `sqrt5_bounds`（`2 < √5 < 5/2`）证出同等定性结论。

公理审计：本模块仅用 Lean 基础公理（`propext, Classical.choice, Quot.sound`），
`#print axioms` 见文件末尾；零 `sorry`；不引 `e_transcendental` 等项目自加公理。
-/

namespace GoldenFiniteShift

/-! ## A 组：三族显式搜索界（纸面 p.1924–1940） -/

/-- 固定-`q` 头分支：`|q+θ'+v| ≥ q-2`、`h(θ) > 1/2`、`h·|·| ≤ H` 蕴含 `q ≤ 2H+2`。 -/
theorem search_bound_fixed_q {H q f g : ℝ} (hH : 0 < H) (_hq : 1 ≤ q)
    (hf : 1 / 2 < f) (_hg_nn : 0 ≤ g) (hg : q - 2 ≤ g) (hle : f * g ≤ H) :
    q ≤ 2 * H + 2 := by
  have hf0 : (0 : ℝ) < f := by linarith
  have hfg : f * (q - 2) ≤ H :=
    le_trans (mul_le_mul_of_nonneg_left hg (le_of_lt hf0)) hle
  by_cases hq2 : q ≤ 2
  · linarith
  · push_neg at hq2
    have hpos : (0 : ℝ) < q - 2 := by linarith
    have hlt : (1 : ℝ) / 2 * (q - 2) < f * (q - 2) :=
      mul_lt_mul_of_pos_right hf hpos
    linarith

/-- 固定-`q` 头分支加强（`θ ≠ φ-1`）：`|q+θ'+v| ≥ q ≥ 1` 蕴含首项系数 `a ≤ H√5/2`。 -/
theorem search_bound_strong_a {H s a g : ℝ} (hs : 0 < s)
    (ha1 : 1 ≤ a) (hg1 : 1 ≤ g) (hle : 2 * a / s * g ≤ H) :
    a ≤ H * s / 2 := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hnn : (0 : ℝ) ≤ 2 * a / s := by positivity
  have hmul := mul_le_mul_of_nonneg_left hg1 hnn
  rw [mul_one] at hmul
  have h2 : 2 * a / s ≤ H := le_trans hmul hle
  have h3 : 2 * a ≤ H * s := (div_le_iff₀ hs).mp h2
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- 移动偏移分支：`r, θ ∈ [0,1]` 蕴含 `|r - d₀ - θ| ≥ |d₀| - 1`。 -/
theorem search_bound_moving_dist {r θ : ℝ} {d0 : ℤ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : |(d0 : ℝ)| - 1 ≤ |r - (d0 : ℝ) - θ| := by
  have h1 : |r - θ| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have htri : |(d0 : ℝ)| ≤ |r - θ| + |r - (d0 : ℝ) - θ| := by
    have hsub := abs_sub (r - θ) (r - (d0 : ℝ) - θ)
    have heq : (r - θ) - (r - (d0 : ℝ) - θ) = (d0 : ℝ) := by ring
    rwa [heq] at hsub
  linarith

/-- 移动偏移分支：`h > 1/2` 与上界蕴含 `|d₀| ≤ 2H+1`。 -/
theorem search_bound_moving_offset {H f g : ℝ} {d0 : ℤ} (hH : 0 < H)
    (hf : 1 / 2 < f) (_hg_nn : 0 ≤ g) (hg : |(d0 : ℝ)| - 1 ≤ g)
    (hle : f * g ≤ H) :
    |(d0 : ℝ)| ≤ 2 * H + 1 := by
  have hf0 : (0 : ℝ) < f := by linarith
  have hfg : f * (|(d0 : ℝ)| - 1) ≤ H :=
    le_trans (mul_le_mul_of_nonneg_left hg (le_of_lt hf0)) hle
  by_cases hd : |(d0 : ℝ)| ≤ 1
  · linarith
  · push_neg at hd
    have hpos : (0 : ℝ) < |(d0 : ℝ)| - 1 := by linarith
    have hlt : (1 : ℝ) / 2 * (|(d0 : ℝ)| - 1) < f * (|(d0 : ℝ)| - 1) :=
      mul_lt_mul_of_pos_right hf hpos
    linarith

/-- 通用高度界：距离下界 `g ≥ c > 0` 蕴含 `a ≤ H·s/(2c)`（覆盖 `r>0` 情形）。 -/
theorem search_bound_gen_height {H s a g c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (ha1 : 1 ≤ a) (hg : c ≤ g) (hle : 2 * a / s * g ≤ H) :
    a ≤ H * s / (2 * c) := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hnn : (0 : ℝ) ≤ 2 * a / s := by positivity
  have h1 : 2 * a / s * c ≤ H :=
    le_trans (mul_le_mul_of_nonneg_left hg hnn) hle
  have h2 : (2 * a * c) / s ≤ H := by
    have heq : (2 * a * c) / s = 2 * a / s * c := by ring
    rwa [heq]
  have h3 : 2 * a * c ≤ H * s := (div_le_iff₀ hs).mp h2
  have h2c : (0 : ℝ) < 2 * c := by linarith
  rw [le_div_iff₀ h2c]
  linarith

/-- 空后缀范数截断（`r=0, d₀=-1`）：`M = a(1-θ) ≤ H√5/2` 且 `1 ≤ M(M+√5)/a`
    蕴含 `a ≤ 5H(H+2)/4`。 -/
theorem search_bound_norm_cutoff {H s M a : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 5)
    (hH : 0 < H) (ha : 0 < a) (hM0 : 0 < M) (hM : M ≤ H * s / 2)
    (hnorm : 1 ≤ M * (M + s) / a) : a ≤ 5 * H * (H + 2) / 4 := by
  have h1 : 1 * a ≤ M * (M + s) := (le_div_iff₀ ha).mp hnorm
  have hMs : M + s ≤ H * s / 2 + s := by linarith
  have hsnn : (0 : ℝ) ≤ s := le_of_lt hs
  have hMnn : (0 : ℝ) ≤ M := le_of_lt hM0
  have hMsnn : (0 : ℝ) ≤ M + s := by linarith
  have hHnn : (0 : ℝ) ≤ H * s / 2 := by
    have h1 := mul_nonneg (le_of_lt hH) hsnn
    linarith
  have hnn2 : (0 : ℝ) ≤ H * s / 2 + s := by linarith
  have hM2 : M * (M + s) ≤ (H * s / 2) * (H * s / 2 + s) :=
    mul_le_mul hM hMs hMsnn hHnn
  have hexpand : (H * s / 2) * (H * s / 2 + s) = 5 * H * (H + 2) / 4 := by
    linear_combination (H ^ 2 / 4 + H / 2) * hsq
  linarith

/-- 后缀分支 `m` 范围：`|m/(p√5) - 1| ≤ H` 蕴含 `(1-H)p√5 ≤ m ≤ (1+H)p√5`。 -/
theorem search_bound_suffix_m {H p s m : ℝ} (hs : 0 < s) (hp : 0 < p)
    (hle : |m / (p * s) - 1| ≤ H) :
    (1 - H) * (p * s) ≤ m ∧ m ≤ (1 + H) * (p * s) := by
  have hps : (0 : ℝ) < p * s := mul_pos hp hs
  obtain ⟨hlo, hhi⟩ := abs_le.mp hle
  constructor
  · have h1 : 1 - H ≤ m / (p * s) := by linarith
    exact (le_div_iff₀ hps).mp h1
  · have h2 : m / (p * s) ≤ 1 + H := by linarith
    exact (div_le_iff₀ hps).mp h2

/-- 轨道高度一致下界：首项系数 `a ≥ 1` 时 `2a/√5 > 1/2`
    （A 组界中 `h(θ) > 1/2` 的来源；`√5 < 5/2`）。 -/
theorem orbit_height_lower_bound (a : ℕ) (ha : 1 ≤ a) :
    (1 : ℝ) / 2 < 2 * ((a : ℕ) : ℝ) / Real.sqrt 5 := by
  have hb := GoldenOrbitRigidity.sqrt5_bounds
  have hs25 := hb.2
  have hs0 : (0 : ℝ) < Real.sqrt 5 := by linarith [hb.1]
  have haR : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast ha
  rw [lt_div_iff₀ hs0]
  linarith

/-! ## B 组：格点形 `|1 - m/(D√5)|`（纸面 p.1949–1955） -/

/-- 两头分支格点形：`V = (2a/s)·|(M - σDs)/(2aD)|` 化为 `|m/(Ds) - 1|`；
    `σ = -1` 时取 `m ↦ -m`（纸面“changing its sign if necessary”）。 -/
theorem quadratic_tail_value_mem_lattice {a M D : ℤ} (ha : 0 < a) (hD : 0 < D)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (s : ℝ) (hs : 0 < s)
    (V : ℝ) (hV : V = 2 * (a : ℝ) / s *
      |(M : ℝ) - (σ : ℝ) * (D : ℝ) * s| / ((2 * (a : ℝ)) * (D : ℝ))) :
    ∃ m : ℤ, V = |(m : ℝ) / ((D : ℝ) * s) - 1| := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have haRn : (a : ℝ) ≠ 0 := ne_of_gt haR
  have hDRn : (D : ℝ) ≠ 0 := ne_of_gt hDR
  have hsn : s ≠ 0 := ne_of_gt hs
  have h2aD : (0 : ℝ) < (2 * (a : ℝ)) * (D : ℝ) := by positivity
  have hV2 : V = |(M : ℝ) - (σ : ℝ) * (D : ℝ) * s| / ((D : ℝ) * s) := by
    rw [hV]
    field_simp
  have hDs : (0 : ℝ) < (D : ℝ) * s := mul_pos hDR hs
  rcases hσ with rfl | rfl
  · refine ⟨M, ?_⟩
    have heq : (M : ℝ) / ((D : ℝ) * s) - 1 =
        ((M : ℝ) - (D : ℝ) * s) / ((D : ℝ) * s) := by
      rw [sub_div, div_self (ne_of_gt hDs)]
    have h1 : (((1 : ℤ)) : ℝ) = 1 := by simp
    rw [hV2, heq, abs_div, abs_of_pos hDs, h1, one_mul]
  · refine ⟨-M, ?_⟩
    have heq : (((-M : ℤ)) : ℝ) / ((D : ℝ) * s) - 1 =
        -(((M : ℝ) + (D : ℝ) * s) / ((D : ℝ) * s)) := by
      field_simp
      push_cast
      ring
    have hneg : (((-1 : ℤ)) : ℝ) = -1 := by simp
    rw [hV2, heq, hneg, abs_neg, abs_div, abs_of_pos hDs]
    congr 1
    congr 1
    ring

/-- 后缀分支格点形：`p ∣ D` 时 `|m/(p√5) - 1| = |m'/(D√5) - 1|`。 -/
theorem suffix_value_mem_lattice (p D : ℕ) (hp : 1 ≤ p) (hD : 1 ≤ D)
    (hpD : p ∣ D) (m : ℤ) (V : ℝ)
    (hV : V = |(m : ℝ) / ((p : ℝ) * Real.sqrt 5) - 1|) :
    ∃ m' : ℤ, V = |(m' : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1| := by
  obtain ⟨t, ht⟩ := hpD
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exfalso
      rw [h0, Nat.mul_zero] at ht
      omega
    · exact h0
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
  have hs := GoldenOrbitRigidity.sqrt5_pos
  have hDtR : (D : ℝ) = (p : ℝ) * (t : ℝ) := by
    rw [ht]
    push_cast
    ring
  have hpsn : (p : ℝ) * Real.sqrt 5 ≠ 0 := ne_of_gt (mul_pos hpR hs)
  have heq : (m : ℝ) * (t : ℝ) / (((p : ℝ) * (t : ℝ)) * Real.sqrt 5) =
      (m : ℝ) / ((p : ℝ) * Real.sqrt 5) := by
    field_simp
  refine ⟨m * (t : ℤ), ?_⟩
  rw [hDtR, hV, Int.cast_mul, Int.cast_natCast, heq]

/-! ## C 组：格点谱离散性（纸面 p.1956–1960） -/

/-- `D ≥ 1` 时 `X = D√5 > 0`。 -/
theorem Dsqrt5_pos (D : ℕ) (hD : 1 ≤ D) :
    (0 : ℝ) < (D : ℝ) * Real.sqrt 5 := by
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  exact mul_pos hD0 GoldenOrbitRigidity.sqrt5_pos

/-- `D ≥ 1` 时 `D√5` 无理（`√5` 无理的整数倍）。 -/
theorem Dsqrt5_irrational (D : ℕ) (hD : 1 ≤ D) :
    Irrational (((D : ℝ)) * Real.sqrt 5) := by
  have hirr5 : Irrational (Real.sqrt 5) :=
    Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 5)
  have hD0 : (0 : ℝ) < (((D : ℕ)) : ℝ) := by exact_mod_cast hD
  have hDn : (((D : ℕ)) : ℝ) ≠ 0 := ne_of_gt hD0
  unfold Irrational
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  have hsqrt : Real.sqrt 5 = (q : ℝ) / (((D : ℕ)) : ℝ) := by
    rw [hq, eq_div_iff hDn]
    ring
  exact hirr5 ⟨q / (D : ℚ), by push_cast; exact hsqrt.symm⟩

/-- 无理数到 `ℤ` 的距离为正：`δ = min (Y - ⌊Y⌋, ⌊Y⌋ + 1 - Y)`。 -/
theorem dist_int_pos (Y : ℝ) (hYirr : Irrational Y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, δ ≤ |(m : ℝ) - Y| := by
  unfold Irrational at hYirr
  have hne : ∀ k : ℤ, ((k : ℝ)) ≠ Y := by
    intro k hk
    exact hYirr ⟨(k : ℚ), by exact_mod_cast hk⟩
  have hflt : ((((⌊Y⌋ : ℤ))) : ℝ) < Y := by
    by_contra hle
    push_neg at hle
    have hge := Int.floor_le Y
    have heq : ((((⌊Y⌋ : ℤ))) : ℝ) = Y := le_antisymm hge hle
    exact hne ⌊Y⌋ heq
  have hflt2 : Y < ((((⌊Y⌋ : ℤ))) : ℝ) + 1 := Int.lt_floor_add_one Y
  refine ⟨min (Y - ((((⌊Y⌋ : ℤ))) : ℝ)) (((((⌊Y⌋ : ℤ))) : ℝ) + 1 - Y), ?_, ?_⟩
  · exact lt_min_iff.mpr ⟨by linarith, by linarith⟩
  · intro m
    by_cases h : m ≤ ⌊Y⌋
    · have hmR : ((m : ℝ)) ≤ ((((⌊Y⌋ : ℤ))) : ℝ) := by exact_mod_cast h
      have habs : |(m : ℝ) - Y| = Y - (m : ℝ) := by
        rw [abs_sub_comm]
        exact abs_of_pos (by linarith)
      rw [habs]
      have hmin := min_le_left (Y - ((((⌊Y⌋ : ℤ))) : ℝ))
        (((((⌊Y⌋ : ℤ))) : ℝ) + 1 - Y)
      linarith
    · push_neg at h
      have h1 : ⌊Y⌋ + 1 ≤ m := by omega
      have hmR : ((((⌊Y⌋ : ℤ))) : ℝ) + 1 ≤ ((m : ℝ)) := by exact_mod_cast h1
      have habs : |(m : ℝ) - Y| = (m : ℝ) - Y := abs_of_pos (by linarith)
      rw [habs]
      have hmin := min_le_right (Y - ((((⌊Y⌋ : ℤ))) : ℝ))
        (((((⌊Y⌋ : ℤ))) : ℝ) + 1 - Y)
      linarith

/-- 格点谱正最小值：一切 `|m/(D√5) - 1|` 不小于 `δ = ‖D√5‖/(D√5) > 0`。 -/
theorem lattice_spectrum_pos_min (D : ℕ) (hD : 1 ≤ D) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ m : ℤ, δ ≤ |(m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1| := by
  have hX0 := Dsqrt5_pos D hD
  obtain ⟨δ0, hδ0, hδ⟩ := dist_int_pos _ (Dsqrt5_irrational D hD)
  refine ⟨δ0 / ((D : ℝ) * Real.sqrt 5), div_pos hδ0 hX0, ?_⟩
  intro m
  have hXn : ((D : ℝ) * Real.sqrt 5) ≠ 0 := ne_of_gt hX0
  have heq : ((m : ℝ) - (D : ℝ) * Real.sqrt 5) / ((D : ℝ) * Real.sqrt 5) =
      (m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1 := by
    rw [sub_div, div_self hXn]
  have hdiv : ∀ a b : ℝ, a ≤ b → a / ((D : ℝ) * Real.sqrt 5) ≤
      b / ((D : ℝ) * Real.sqrt 5) := by
    intro a b hab
    have e1 : a / ((D : ℝ) * Real.sqrt 5) = a * (((D : ℝ) * Real.sqrt 5)⁻¹) :=
      div_eq_mul_inv a _
    have e2 : b / ((D : ℝ) * Real.sqrt 5) = b * (((D : ℝ) * Real.sqrt 5)⁻¹) :=
      div_eq_mul_inv b _
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hab (le_of_lt (inv_pos.mpr hX0))
  rw [← heq, abs_div, abs_of_pos hX0]
  exact hdiv _ _ (hδ m)

/-- 格点谱一致分离：互异两值之差 `≥ min(1, ‖2D√5‖)/(D√5) > 0`
    （同侧差 `≥ 1/(D√5)`，异侧差 `≥ ‖2D√5‖/(D√5)`）。 -/
theorem lattice_values_separated (D : ℕ) (hD : 1 ≤ D) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ m1 m2 : ℤ,
      |(m1 : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1| =
        |(m2 : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1| ∨
      γ ≤ |(|(m1 : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1|) -
        (|(m2 : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1|)| := by
  have hX0 := Dsqrt5_pos D hD
  have hXn : ((D : ℝ) * Real.sqrt 5) ≠ 0 := ne_of_gt hX0
  obtain ⟨δ2, hδ2, hδ⟩ := dist_int_pos _ (Dsqrt5_irrational (2 * D) (by omega))
  have h2X : (2 : ℝ) * ((D : ℝ) * Real.sqrt 5) =
      ((2 * D : ℕ) : ℝ) * Real.sqrt 5 := by
    rw [Nat.cast_mul]
    ring
  refine ⟨min 1 δ2 / ((D : ℝ) * Real.sqrt 5),
    div_pos (lt_min_iff.mpr ⟨by norm_num, hδ2⟩) hX0, ?_⟩
  have hdiv : ∀ a b : ℝ, a ≤ b → a / ((D : ℝ) * Real.sqrt 5) ≤
      b / ((D : ℝ) * Real.sqrt 5) := by
    intro a b hab
    have e1 : a / ((D : ℝ) * Real.sqrt 5) = a * (((D : ℝ) * Real.sqrt 5)⁻¹) :=
      div_eq_mul_inv a _
    have e2 : b / ((D : ℝ) * Real.sqrt 5) = b * (((D : ℝ) * Real.sqrt 5)⁻¹) :=
      div_eq_mul_inv b _
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hab (le_of_lt (inv_pos.mpr hX0))
  have hrew : ∀ m : ℤ, |(m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1| =
      |(m : ℝ) - (D : ℝ) * Real.sqrt 5| / ((D : ℝ) * Real.sqrt 5) := by
    intro m
    have heq : ((m : ℝ) - (D : ℝ) * Real.sqrt 5) / ((D : ℝ) * Real.sqrt 5) =
        (m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1 := by
      rw [sub_div, div_self hXn]
    rw [← heq, abs_div, abs_of_pos hX0]
  have hXirr := Dsqrt5_irrational D hD
  unfold Irrational at hXirr
  have hXne : ∀ k : ℤ, ((k : ℝ)) ≠ ((D : ℝ) * Real.sqrt 5) := by
    intro k hk
    exact hXirr ⟨(k : ℚ), by exact_mod_cast hk⟩
  have hside : ∀ m : ℤ, (m : ℝ) < (D : ℝ) * Real.sqrt 5 ∨
      (D : ℝ) * Real.sqrt 5 < (m : ℝ) :=
    fun m => lt_or_gt_of_ne (hXne m)
  have hint : ∀ m1 m2 : ℤ, m1 ≠ m2 → (1 : ℝ) ≤ |(m2 : ℝ) - (m1 : ℝ)| := by
    intro m1 m2 hne
    have hkk : m2 - m1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hsub : (m2 : ℝ) - (m1 : ℝ) = ((((m2 - m1 : ℤ))) : ℝ) :=
      (Int.cast_sub m2 m1).symm
    rw [hsub]
    by_cases hpos : 0 ≤ m2 - m1
    · have h1 : 1 ≤ m2 - m1 := by omega
      rw [abs_of_nonneg (by exact_mod_cast hpos)]
      exact_mod_cast h1
    · push_neg at hpos
      have h1 : m2 - m1 ≤ -1 := by omega
      rw [abs_of_neg (by exact_mod_cast hpos)]
      have hle : ((((m2 - m1 : ℤ))) : ℝ) ≤ -1 := by exact_mod_cast h1
      linarith
  intro m1 m2
  by_cases heq : m1 = m2
  · subst heq
    left
    rfl
  · right
    have hI := hint m1 m2 heq
    rcases hside m1 with h1 | h1 <;> rcases hside m2 with h2 | h2
    · have e1 : |(m1 : ℝ) - (D : ℝ) * Real.sqrt 5| =
          (D : ℝ) * Real.sqrt 5 - (m1 : ℝ) := by
        rw [abs_of_neg (sub_neg.mpr h1)]
        ring
      have e2 : |(m2 : ℝ) - (D : ℝ) * Real.sqrt 5| =
          (D : ℝ) * Real.sqrt 5 - (m2 : ℝ) := by
        rw [abs_of_neg (sub_neg.mpr h2)]
        ring
      have ediff : |((D : ℝ) * Real.sqrt 5 - (m1 : ℝ)) /
            ((D : ℝ) * Real.sqrt 5) -
          ((D : ℝ) * Real.sqrt 5 - (m2 : ℝ)) / ((D : ℝ) * Real.sqrt 5)| =
          |(m2 : ℝ) - (m1 : ℝ)| / ((D : ℝ) * Real.sqrt 5) := by
        have hsub : ((D : ℝ) * Real.sqrt 5 - (m1 : ℝ)) / ((D : ℝ) * Real.sqrt 5) -
            ((D : ℝ) * Real.sqrt 5 - (m2 : ℝ)) / ((D : ℝ) * Real.sqrt 5) =
            ((m2 : ℝ) - (m1 : ℝ)) / ((D : ℝ) * Real.sqrt 5) := by
          rw [← sub_div]
          congr 1
          ring
        rw [hsub, abs_div, abs_of_pos hX0]
      rw [hrew m1, hrew m2, e1, e2, ediff]
      exact hdiv _ _ (le_trans (min_le_left _ _) hI)
    · have e1 : |(m1 : ℝ) - (D : ℝ) * Real.sqrt 5| =
          (D : ℝ) * Real.sqrt 5 - (m1 : ℝ) := by
        rw [abs_of_neg (sub_neg.mpr h1)]
        ring
      have e2 : |(m2 : ℝ) - (D : ℝ) * Real.sqrt 5| =
          (m2 : ℝ) - (D : ℝ) * Real.sqrt 5 :=
        abs_of_pos (sub_pos.mpr h2)
      have hδm2 : δ2 ≤
          |2 * ((D : ℝ) * Real.sqrt 5) - ((m1 : ℝ) + (m2 : ℝ))| := by
        have h := hδ (m1 + m2)
        rw [← h2X] at h
        have hc : ((((m1 + m2 : ℤ))) : ℝ) = (m1 : ℝ) + (m2 : ℝ) :=
          Int.cast_add m1 m2
        rw [hc, abs_sub_comm] at h
        exact h
      have ediff : |((D : ℝ) * Real.sqrt 5 - (m1 : ℝ)) /
            ((D : ℝ) * Real.sqrt 5) -
          ((m2 : ℝ) - (D : ℝ) * Real.sqrt 5) / ((D : ℝ) * Real.sqrt 5)| =
          |2 * ((D : ℝ) * Real.sqrt 5) - ((m1 : ℝ) + (m2 : ℝ))| /
            ((D : ℝ) * Real.sqrt 5) := by
        have hsub : ((D : ℝ) * Real.sqrt 5 - (m1 : ℝ)) / ((D : ℝ) * Real.sqrt 5) -
            ((m2 : ℝ) - (D : ℝ) * Real.sqrt 5) / ((D : ℝ) * Real.sqrt 5) =
            (2 * ((D : ℝ) * Real.sqrt 5) - ((m1 : ℝ) + (m2 : ℝ))) /
              ((D : ℝ) * Real.sqrt 5) := by
          rw [← sub_div]
          congr 1
          ring
        rw [hsub, abs_div, abs_of_pos hX0]
      rw [hrew m1, hrew m2, e1, e2, ediff]
      exact hdiv _ _ (le_trans (min_le_right _ _) hδm2)
    · have e1 : |(m1 : ℝ) - (D : ℝ) * Real.sqrt 5| =
          (m1 : ℝ) - (D : ℝ) * Real.sqrt 5 :=
        abs_of_pos (sub_pos.mpr h1)
      have e2 : |(m2 : ℝ) - (D : ℝ) * Real.sqrt 5| =
          (D : ℝ) * Real.sqrt 5 - (m2 : ℝ) := by
        rw [abs_of_neg (sub_neg.mpr h2)]
        ring
      have hδm2 : δ2 ≤
          |2 * ((D : ℝ) * Real.sqrt 5) - ((m1 : ℝ) + (m2 : ℝ))| := by
        have h := hδ (m1 + m2)
        rw [← h2X] at h
        have hc : ((((m1 + m2 : ℤ))) : ℝ) = (m1 : ℝ) + (m2 : ℝ) :=
          Int.cast_add m1 m2
        rw [hc, abs_sub_comm] at h
        exact h
      have ediff : |((m1 : ℝ) - (D : ℝ) * Real.sqrt 5) /
            ((D : ℝ) * Real.sqrt 5) -
          ((D : ℝ) * Real.sqrt 5 - (m2 : ℝ)) / ((D : ℝ) * Real.sqrt 5)| =
          |2 * ((D : ℝ) * Real.sqrt 5) - ((m1 : ℝ) + (m2 : ℝ))| /
            ((D : ℝ) * Real.sqrt 5) := by
        have hsub : ((m1 : ℝ) - (D : ℝ) * Real.sqrt 5) / ((D : ℝ) * Real.sqrt 5) -
            ((D : ℝ) * Real.sqrt 5 - (m2 : ℝ)) / ((D : ℝ) * Real.sqrt 5) =
            (((m1 : ℝ) + (m2 : ℝ)) - 2 * ((D : ℝ) * Real.sqrt 5)) /
              ((D : ℝ) * Real.sqrt 5) := by
          rw [← sub_div]
          congr 1
          ring
        rw [hsub, abs_div, abs_of_pos hX0, abs_sub_comm]
      rw [hrew m1, hrew m2, e1, e2, ediff]
      exact hdiv _ _ (le_trans (min_le_right _ _) hδm2)
    · have e1 : |(m1 : ℝ) - (D : ℝ) * Real.sqrt 5| =
          (m1 : ℝ) - (D : ℝ) * Real.sqrt 5 :=
        abs_of_pos (sub_pos.mpr h1)
      have e2 : |(m2 : ℝ) - (D : ℝ) * Real.sqrt 5| =
          (m2 : ℝ) - (D : ℝ) * Real.sqrt 5 :=
        abs_of_pos (sub_pos.mpr h2)
      have ediff : |((m1 : ℝ) - (D : ℝ) * Real.sqrt 5) /
            ((D : ℝ) * Real.sqrt 5) -
          ((m2 : ℝ) - (D : ℝ) * Real.sqrt 5) / ((D : ℝ) * Real.sqrt 5)| =
          |(m2 : ℝ) - (m1 : ℝ)| / ((D : ℝ) * Real.sqrt 5) := by
        have hsub : ((m1 : ℝ) - (D : ℝ) * Real.sqrt 5) / ((D : ℝ) * Real.sqrt 5) -
            ((m2 : ℝ) - (D : ℝ) * Real.sqrt 5) / ((D : ℝ) * Real.sqrt 5) =
            ((m1 : ℝ) - (m2 : ℝ)) / ((D : ℝ) * Real.sqrt 5) := by
          rw [← sub_div]
          congr 1
          ring
        rw [hsub, abs_div, abs_of_pos hX0, abs_sub_comm]
      rw [hrew m1, hrew m2, e1, e2, ediff]
      exact hdiv _ _ (le_trans (min_le_left _ _) hI)

/-! ## D 组：`H = 3` 时前两个值（纸面 p.1960–1962） -/

/-- `θ = φ-1` 处移动偏移 `d₀ = 1, 2` 给出两个 `< 3` 的互异极限值，
    格点形为 `m = -1, -3`（`D = 1`）。 -/
theorem first_two_below_three :
    ∃ V1 V2 : ℝ, V1 = 2 / Real.sqrt 5 * (1 + (GoldenOrbitRigidity.φ - 1)) ∧
      V2 = 2 / Real.sqrt 5 * (2 + (GoldenOrbitRigidity.φ - 1)) ∧
      V1 = |(((-1 : ℤ)) : ℝ) / Real.sqrt 5 - 1| ∧
      V2 = |(((-3 : ℤ)) : ℝ) / Real.sqrt 5 - 1| ∧
      V1 < 3 ∧ V2 < 3 ∧ V1 ≠ V2 := by
  have hb := GoldenOrbitRigidity.sqrt5_bounds
  have hs : (2 : ℝ) < Real.sqrt 5 := hb.1
  have hs0 : (0 : ℝ) < Real.sqrt 5 := by linarith
  have hsn : Real.sqrt 5 ≠ 0 := ne_of_gt hs0
  have hφ : GoldenOrbitRigidity.φ = (1 + Real.sqrt 5) / 2 := rfl
  have e1 : 2 / Real.sqrt 5 * (1 + (GoldenOrbitRigidity.φ - 1)) =
      (1 + Real.sqrt 5) / Real.sqrt 5 := by
    rw [hφ]
    field_simp
    ring
  have e2 : 2 / Real.sqrt 5 * (2 + (GoldenOrbitRigidity.φ - 1)) =
      (3 + Real.sqrt 5) / Real.sqrt 5 := by
    rw [hφ]
    field_simp
    ring
  have c1 : (((-1 : ℤ)) : ℝ) = -1 := by simp
  have c2 : (((-3 : ℤ)) : ℝ) = -3 := by simp
  have a1 : (((-1 : ℤ)) : ℝ) / Real.sqrt 5 - 1 =
      -((1 + Real.sqrt 5) / Real.sqrt 5) := by
    rw [c1]
    field_simp
    ring
  have a2 : (((-3 : ℤ)) : ℝ) / Real.sqrt 5 - 1 =
      -((3 + Real.sqrt 5) / Real.sqrt 5) := by
    rw [c2]
    field_simp
    ring
  have hV1 : (0 : ℝ) < (1 + Real.sqrt 5) / Real.sqrt 5 := by positivity
  have hV2 : (0 : ℝ) < (3 + Real.sqrt 5) / Real.sqrt 5 := by positivity
  refine ⟨(1 + Real.sqrt 5) / Real.sqrt 5, (3 + Real.sqrt 5) / Real.sqrt 5,
    e1.symm, e2.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a1, abs_neg]
    exact (abs_of_pos hV1).symm
  · rw [a2, abs_neg]
    exact (abs_of_pos hV2).symm
  · rw [div_lt_iff₀ hs0]
    linarith
  · rw [div_lt_iff₀ hs0]
    linarith
  · intro h
    have h2 := congrArg (fun x : ℝ => x * Real.sqrt 5) h
    rw [div_mul_cancel₀ _ hsn, div_mul_cancel₀ _ hsn] at h2
    linarith

/-! ## E 组：三族候选集、有限性与格点含入 -/

/-- 格点板：以 `D√5` 为界的有限候选值集合。 -/
def latticeSlab (D : ℕ) (H : ℝ) : Set ℝ :=
  {V | ∃ m : ℤ, |(m : ℝ) - (D : ℝ) * Real.sqrt 5| ≤
    H * ((D : ℝ) * Real.sqrt 5) ∧
    V = |(m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1|}

/-- 格点板有限：`m` 被夹在 `⌊X-HX⌋…⌈X+HX⌉` 之间。 -/
theorem latticeSlab_finite (D : ℕ) (hD : 1 ≤ D) (H : ℝ) :
    (latticeSlab D H).Finite := by
  have hX0 := Dsqrt5_pos D hD
  have hfin : ((fun m : ℤ => |(m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1|) ''
      (Set.Icc ⌊(D : ℝ) * Real.sqrt 5 - H * ((D : ℝ) * Real.sqrt 5)⌋
        ⌈(D : ℝ) * Real.sqrt 5 + H * ((D : ℝ) * Real.sqrt 5)⌉)).Finite :=
    (Set.finite_Icc _ _).image _
  refine Set.Finite.subset hfin ?_
  intro V hV
  obtain ⟨m, hm, rfl⟩ := hV
  have hlo : ((((⌊(D : ℝ) * Real.sqrt 5 -
      H * ((D : ℝ) * Real.sqrt 5)⌋ : ℤ))) : ℝ) ≤
    (D : ℝ) * Real.sqrt 5 - H * ((D : ℝ) * Real.sqrt 5) :=
    Int.floor_le _
  have hhi : (D : ℝ) * Real.sqrt 5 + H * ((D : ℝ) * Real.sqrt 5) ≤
      ((((⌈(D : ℝ) * Real.sqrt 5 +
        H * ((D : ℝ) * Real.sqrt 5)⌉ : ℤ))) : ℝ) := Int.le_ceil _
  have habs := abs_le.mp hm
  have lower : ⌊(D : ℝ) * Real.sqrt 5 - H * ((D : ℝ) * Real.sqrt 5)⌋ ≤ m := by
    by_contra hlt
    push_neg at hlt
    have hmR : ((m : ℝ)) <
        ((((⌊(D : ℝ) * Real.sqrt 5 - H * ((D : ℝ) * Real.sqrt 5)⌋ : ℤ))) : ℝ) := by
      exact_mod_cast hlt
    linarith [hlo, habs.1]
  have upper : m ≤ ⌈(D : ℝ) * Real.sqrt 5 + H * ((D : ℝ) * Real.sqrt 5)⌉ := by
    by_contra hlt
    push_neg at hlt
    have hmR : ((((⌈(D : ℝ) * Real.sqrt 5 +
        H * ((D : ℝ) * Real.sqrt 5)⌉ : ℤ))) : ℝ) < ((m : ℝ)) := by
      exact_mod_cast hlt
    linarith [hhi, habs.2]
  exact ⟨m, Set.mem_Icc.mpr ⟨lower, upper⟩, rfl⟩

/-- 界内格点值落入格点板。 -/
theorem mem_latticeSlab_of_abs_le (D : ℕ) (hD : 1 ≤ D) (H : ℝ) (m : ℤ)
    (hle : |(m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1| ≤ H) :
    |(m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1| ∈ latticeSlab D H := by
  have hX0 := Dsqrt5_pos D hD
  have hXn : ((D : ℝ) * Real.sqrt 5) ≠ 0 := ne_of_gt hX0
  refine ⟨m, ?_, rfl⟩
  have heq : (m : ℝ) - (D : ℝ) * Real.sqrt 5 =
      ((m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1) * ((D : ℝ) * Real.sqrt 5) := by
    rw [sub_mul, div_mul_cancel₀ _ hXn, one_mul]
  rw [heq, abs_mul, abs_of_pos hX0]
  exact mul_le_mul_of_nonneg_right hle (le_of_lt hX0)

/-- 后缀分支候选集（`p` 为后缀端点 `u` 的分母；`divOk` 为纸面接口：
    符号范数除子检验与后缀失配检查）。 -/
def suffixCand (p : ℕ) (H : ℝ) (divOk : ℤ → Prop) : Set ℝ :=
  {V | ∃ m : ℤ, divOk m ∧
    |(m : ℝ) / ((p : ℝ) * Real.sqrt 5) - 1| ≤ H ∧
    V = |(m : ℝ) / ((p : ℝ) * Real.sqrt 5) - 1|}

/-- 固定-`q` 头分支候选集（`(a, q)` 为尾参数与整数头；
    `fixedOk` 为纸面接口：轨道成员与头失配检查）。 -/
def fixedCand (D : ℕ) (H : ℝ) (fixedOk : ℤ → ℤ → Prop) : Set ℝ :=
  {V | ∃ a q m : ℤ, fixedOk a q ∧
    |(m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1| ≤ H ∧
    V = |(m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1|}

/-- 移动偏移头分支候选集（`(a, d₀)` 为尾参数与偏移；
    `movingOk` 为纸面接口：轨道成员与偏移检查）。 -/
def movingCand (D : ℕ) (H : ℝ) (movingOk : ℤ → ℤ → Prop) : Set ℝ :=
  {V | ∃ a d0 m : ℤ, movingOk a d0 ∧
    |(m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1| ≤ H ∧
    V = |(m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1|}

theorem suffixCand_finite (p : ℕ) (hp : 1 ≤ p) (H : ℝ) (divOk : ℤ → Prop) :
    (suffixCand p H divOk).Finite := by
  apply Set.Finite.subset (latticeSlab_finite p hp H)
  intro V hV
  obtain ⟨m, _, hle, rfl⟩ := hV
  exact mem_latticeSlab_of_abs_le p hp H m hle

theorem fixedCand_finite (D : ℕ) (hD : 1 ≤ D) (H : ℝ) (fixedOk : ℤ → ℤ → Prop) :
    (fixedCand D H fixedOk).Finite := by
  apply Set.Finite.subset (latticeSlab_finite D hD H)
  intro V hV
  obtain ⟨a, q, m, _, hle, rfl⟩ := hV
  exact mem_latticeSlab_of_abs_le D hD H m hle

theorem movingCand_finite (D : ℕ) (hD : 1 ≤ D) (H : ℝ)
    (movingOk : ℤ → ℤ → Prop) :
    (movingCand D H movingOk).Finite := by
  apply Set.Finite.subset (latticeSlab_finite D hD H)
  intro V hV
  obtain ⟨a, d0, m, _, hle, rfl⟩ := hV
  exact mem_latticeSlab_of_abs_le D hD H m hle

/-- 格点值谓词 `∃ m, V = |m/(D√5) - 1|`。 -/
def latticeVal (D : ℕ) (V : ℝ) : Prop :=
  ∃ m : ℤ, V = |(m : ℝ) / ((D : ℝ) * Real.sqrt 5) - 1|

/-- 格点形与纸面 `|1 - m/(D√5)|` 一致（差一符号）。 -/
theorem latticeVal_comm (D : ℕ) (V : ℝ) (hV : latticeVal D V) :
    ∃ m : ℤ, V = |1 - (m : ℝ) / ((D : ℝ) * Real.sqrt 5)| := by
  obtain ⟨m, hm⟩ := hV
  exact ⟨m, by rw [hm, abs_sub_comm]⟩

theorem suffixCand_mem_lattice (p D : ℕ) (hp : 1 ≤ p) (hD : 1 ≤ D) (hpD : p ∣ D)
    (H : ℝ) (divOk : ℤ → Prop) (V : ℝ) (hV : V ∈ suffixCand p H divOk) :
    latticeVal D V := by
  obtain ⟨m, _, _, rfl⟩ := hV
  exact suffix_value_mem_lattice p D hp hD hpD m _ rfl

theorem fixedCand_mem_lattice (D : ℕ) (hD : 1 ≤ D)
    (H : ℝ) (fixedOk : ℤ → ℤ → Prop) (V : ℝ) (hV : V ∈ fixedCand D H fixedOk) :
    latticeVal D V := by
  obtain ⟨a, q, m, _, _, rfl⟩ := hV
  exact ⟨m, rfl⟩

theorem movingCand_mem_lattice (D : ℕ) (hD : 1 ≤ D)
    (H : ℝ) (movingOk : ℤ → ℤ → Prop) (V : ℝ)
    (hV : V ∈ movingCand D H movingOk) :
    latticeVal D V := by
  obtain ⟨a, d0, m, _, _, rfl⟩ := hV
  exact ⟨m, rfl⟩

/-- 后缀除子有限性：范数商的除子集有限（纸面“apply … to its signed norm divisors”）。
    非零性来自 `GeneralEndpointRigidity.Muv_norm_ne_zero`（Part 4）。 -/
theorem norm_divisor_finite (N : ℤ) (hN : N ≠ 0) : {d : ℤ | d ∣ N}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-|N|) |N|)
  intro d hd
  obtain ⟨k, hk⟩ := hd
  have hk0 : k ≠ 0 := by
    intro h0
    apply hN
    rw [h0, mul_zero] at hk
    exact hk
  have hle : |d| ≤ |N| := by
    have hkk : |N| = |d| * |k| := by rw [hk, abs_mul]
    have hk1 : (1 : ℤ) ≤ |k| := by
      by_contra hlt
      push_neg at hlt
      have h0 : |k| = 0 := by
        have hle0 : |k| ≤ 0 := by omega
        exact le_antisymm hle0 (abs_nonneg _)
      exact hk0 (abs_eq_zero.mp h0)
    calc |d| = |d| * 1 := (mul_one _).symm
      _ ≤ |d| * |k| := mul_le_mul_of_nonneg_left hk1 (abs_nonneg _)
      _ = |N| := hkk.symm
  rw [Set.mem_Icc]
  exact ⟨neg_le_of_abs_le hle, le_of_abs_le hle⟩

/-- 后缀分支除子候选有限：每个端点的范数商非零（刚性 Part 4），故其除子有限。 -/
theorem suffix_divisor_candidates_finite (p1 q1 p2 q2 a b c d : ℤ)
    (hdet : |a * d - b * c| = 1) (hD : p1 * q2 + p2 * q1 ≠ 0) :
    {t : ℤ | t ∣ ((GoldenOrbitB2Rigidity.M_uv p1 q1 p2 q2 a b c d) ^ 2 -
      5 * (p1 * q2 + p2 * q1) ^ 2) / 4}.Finite :=
  norm_divisor_finite _
    (GeneralEndpointRigidity.Muv_norm_ne_zero _ _ _ _ _ _ _ _ hdet hD).2

/-! ## F 组：条件组装（覆盖假设为纸面接口） -/

/-- 三族完备性组装：若每个 `≤ H` 的有限极限值落入三族之一（纸面接口 `hcover`：
    窗口相位提取 + 分支穷举 + Bugeaud (3.4) 达到性），则 `L ∩ [0,H]` 有限且格点化。 -/
theorem finite_shift_of_covers (D p : ℕ) (hD : 1 ≤ D) (hp : 1 ≤ p) (hpD : p ∣ D)
    (H : ℝ) (L : Set ℝ) (divOk : ℤ → Prop) (fixedOk movingOk : ℤ → ℤ → Prop)
    (hcover : ∀ V ∈ L, V ≤ H →
      V ∈ suffixCand p H divOk ∨ V ∈ fixedCand D H fixedOk ∨
        V ∈ movingCand D H movingOk) :
    Set.Finite (L ∩ {V | V ≤ H}) ∧ ∀ V ∈ L ∩ {V | V ≤ H}, latticeVal D V := by
  have hfinS := suffixCand_finite p hp H divOk
  have hfinF := fixedCand_finite D hD H fixedOk
  have hfinM := movingCand_finite D hD H movingOk
  refine ⟨?_, ?_⟩
  · apply Set.Finite.subset (hfinS.union (hfinF.union hfinM))
    intro V hV
    obtain ⟨hVL, hVH⟩ := hV
    have hle : V ≤ H := hVH
    rcases hcover V hVL hle with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro V hV
    obtain ⟨hVL, hVH⟩ := hV
    have hle : V ≤ H := hVH
    rcases hcover V hVL hle with h | h | h
    · exact suffixCand_mem_lattice p D hp hD hpD H divOk V h
    · exact fixedCand_mem_lattice D hD H fixedOk V h
    · exact movingCand_mem_lattice D hD H movingOk V h

/-- 三族一致分离：覆盖假设下，`L ∩ [0,H]` 中互异两值之差一致有下界。 -/
theorem finite_shift_separated (D p : ℕ) (hD : 1 ≤ D) (hp : 1 ≤ p) (hpD : p ∣ D)
    (H : ℝ) (L : Set ℝ) (divOk : ℤ → Prop) (fixedOk movingOk : ℤ → ℤ → Prop)
    (hcover : ∀ V ∈ L, V ≤ H →
      V ∈ suffixCand p H divOk ∨ V ∈ fixedCand D H fixedOk ∨
        V ∈ movingCand D H movingOk) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ V1 V2 : ℝ, V1 ∈ L ∩ {V | V ≤ H} →
      V2 ∈ L ∩ {V | V ≤ H} → V1 = V2 ∨ γ ≤ |V1 - V2| := by
  obtain ⟨γ, hγ, hsep⟩ := lattice_values_separated D hD
  have hlat := (finite_shift_of_covers D p hD hp hpD H L divOk fixedOk movingOk
    hcover).2
  refine ⟨γ, hγ, ?_⟩
  intro V1 V2 h1 h2
  obtain ⟨m1, hm1⟩ := hlat V1 h1
  obtain ⟨m2, hm2⟩ := hlat V2 h2
  have h := hsep m1 m2
  rw [hm1, hm2]
  exact h

/-! ## 公理审计（`#print axioms` 输出随单文件验证一并捕获） -/

#print axioms search_bound_fixed_q
#print axioms search_bound_strong_a
#print axioms search_bound_moving_dist
#print axioms search_bound_moving_offset
#print axioms search_bound_gen_height
#print axioms search_bound_norm_cutoff
#print axioms search_bound_suffix_m
#print axioms orbit_height_lower_bound
#print axioms quadratic_tail_value_mem_lattice
#print axioms suffix_value_mem_lattice
#print axioms Dsqrt5_pos
#print axioms Dsqrt5_irrational
#print axioms dist_int_pos
#print axioms lattice_spectrum_pos_min
#print axioms lattice_values_separated
#print axioms first_two_below_three
#print axioms latticeSlab_finite
#print axioms mem_latticeSlab_of_abs_le
#print axioms suffixCand_finite
#print axioms fixedCand_finite
#print axioms movingCand_finite
#print axioms latticeVal_comm
#print axioms suffixCand_mem_lattice
#print axioms fixedCand_mem_lattice
#print axioms movingCand_mem_lattice
#print axioms norm_divisor_finite
#print axioms suffix_divisor_candidates_finite
#print axioms finite_shift_of_covers
#print axioms finite_shift_separated

end GoldenFiniteShift
