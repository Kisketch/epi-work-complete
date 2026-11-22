import Mathlib
import EpiFormal.EulerConvergents
import EpiFormal.MeiburgConvergence
import EpiFormal.Alekseyev

/-!
# F 组：S7 Theorem 11（双指标检验，三等价）与定量推论 —— 联合编译归一版

来源：用户修订包扩展材料 S7（epi-pdf-qa/witness.py 内嵌原文），纸面证明，本文件做 Lean 机器验证。

## 联合编译归一说明（2026-11-14，总执行）

本文件由并发子任务 F 的 `AdjacentWitness.lean` 归一而来：
- **删除自建地基定义**（原 `Psel`/`Qsel` 直接递归）与**两条自建公理**，
  改为 `import EpiFormal.EulerConvergents`（A 组地基，唯一地基）。
- F 的 `Psel`/`Qsel` 数值序列与 A 完全一致（P: 1,3,19,193,...；Q: 1,1,7,71,...），
  且 F 递推 `X_{j+2}=(4j+6)X_{j+1}+X_j` 恰为 A 的 `selPair_rec`（系数 4(j+1)+2=4j+6）。
  本文件用 A 的 `Psel`/`Qsel`/`deltaSel` 与公理，重证 F 主体所需的同名同陈述桥接引理
  （全下标 `Qsel_pos`、`Qsel_monotone`、2^j 下界 `Qsel_double`、`Qsel_succ_coprime` 等）。
- theorem11 主体证明（Msel/Tsel/pair_iff/limit_integer/forward/converse/三等价/定量推论）
  **原样保留**，数学内容不变。
- 公理唯一来源为 A 的 `deltaSel_tendsto_zero`、`abs_deltaSel_lt`；本文件不新增任何公理。

## 诚实声明（必须保留）

e+π 的无理性是世界开放问题。本文件**没有、也不声称**证明该问题。
Theorem 11 给出的是**等价判据**：对固定正整数 B，
  (a) B(e+π) ∈ ℤ  ↔  (b) 最终 T_j = −B·C_j  ↔  (c) 无穷多 j 使 T_j = −B·C_j。
其「对每个 B 匹配集有限」的研究目标**仍开放**（原文 Research target 诚实声明）：
Irrationality is now equivalent to finiteness of the match set for every B.
Proving that finiteness for the specific nearest integers of π is still open in this approach.
The target concerns a signed integer of magnitude 2B with the alternating sign prescribed by C_j.
-/

open Real Filter

namespace AdjacentWitness

-- 本文件含较多 ring/positivity/极限链计算，放宽心跳上限以避免确定性超时（非逻辑需要）。
set_option maxHeartbeats 1600000

/-! ## 0. 地基桥接：取用 A 的 Psel/Qsel/deltaSel，重证 F 所需同名引理 -/

-- A 的 Psel/Qsel/deltaSel 直接可用（顶层定义）。以下重证 F 主体引用的引理。

/-- 分子递推（F 索引形式）：P_{j+2}=(4j+6)P_{j+1}+P_j。即 A 的 selPair_rec。 -/
theorem Psel_rec (j : ℕ) :
    Psel (j + 2) = (4 * (j : ℤ) + 6) * Psel (j + 1) + Psel j := by
  have := selPair_rec 1 3 j
  simp only [Psel] at this ⊢
  convert this using 1
  push_cast
  ring

/-- 分母递推（F 索引形式）：Q_{j+2}=(4j+6)Q_{j+1}+Q_j。 -/
theorem Qsel_rec (j : ℕ) :
    Qsel (j + 2) = (4 * (j : ℤ) + 6) * Qsel (j + 1) + Qsel j := by
  have := selPair_rec 1 1 j
  simp only [Qsel] at this ⊢
  convert this using 1
  push_cast
  ring

/-- Qsel 恒正（全下标，含 j=0）。由 A 的配对正性引理。 -/
theorem Qsel_pos (j : ℕ) : 0 < Qsel j :=
  (selPair_pos_odd 1 1 (by norm_num) (by norm_num) odd_one odd_one j).1

/-- Qsel ≥ 1。 -/
theorem Qsel_ge_one (j : ℕ) : 1 ≤ Qsel j := by
  have := Qsel_pos j
  omega

/-- Qsel 单调不减（全局）。 -/
theorem Qsel_monotone : Monotone Qsel := by
  apply monotone_nat_of_le_succ
  intro j
  match j with
  | 0 => decide
  | j + 1 =>
    show Qsel (j + 1) ≤ (4 * (j : ℤ) + 6) * Qsel (j + 1) + Qsel j
    have h1 : 0 ≤ Qsel (j + 1) := le_of_lt (Qsel_pos (j + 1))
    have h0 : 0 ≤ Qsel j := le_of_lt (Qsel_pos j)
    have hc : (1 : ℤ) ≤ 4 * (j : ℤ) + 6 := by
      have : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      linarith
    nlinarith

/-- Qsel 下界 Qsel (j+2) ≥ 2^(j+2)（真证：系数 ≥6，归纳）。
    注意 j=1 时 2^1=2>Qsel 1=1，故从 j+2 起索引（Qsel 2=7≥4）。 -/
theorem Qsel_double (j : ℕ) : (2 : ℤ) ^ (j + 2) ≤ Qsel (j + 2) := by
  induction j with
  | zero => decide
  | succ j ih =>
    show (2 : ℤ) ^ (j + 3) ≤ (4 * ((j + 1) : ℤ) + 6) * Qsel (j + 2) + Qsel (j + 1)
    have hQ2pos : 0 < Qsel (j + 2) := Qsel_pos (j + 2)
    have hcoeff : (2 : ℤ) ≤ 4 * ((j + 1) : ℤ) + 6 := by
      have : (0 : ℤ) ≤ ((j + 1) : ℤ) := Int.natCast_nonneg (j + 1)
      linarith
    have hstep : (2 : ℤ) ^ (j + 3) ≤ (4 * ((j + 1) : ℤ) + 6) * Qsel (j + 2) := by
      calc (2 : ℤ) ^ (j + 3) = 2 * (2 : ℤ) ^ (j + 2) := by ring
        _ ≤ 2 * Qsel (j + 2) := by nlinarith
        _ ≤ (4 * ((j + 1) : ℤ) + 6) * Qsel (j + 2) := by nlinarith
    have hQ1 : 0 ≤ Qsel (j + 1) := le_of_lt (Qsel_pos (j + 1))
    nlinarith

/-- Qsel → +∞（沿 atTop，整数版）。 -/
theorem Qsel_tendsto_atTop : Tendsto (fun j : ℕ => Qsel j) atTop atTop := by
  apply tendsto_atTop_mono' atTop
  · apply Filter.eventually_atTop.mpr
    refine ⟨2, fun j hj => ?_⟩
    have hk : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    obtain ⟨k, rfl⟩ := hk
    exact Qsel_double k
  · exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℤ) < 2)

/-- 行列式（交叉积）：Csel j = P_j Q_{j+1} − P_{j+1} Q_j。 -/
def Csel (j : ℕ) : ℤ := Psel j * Qsel (j + 1) - Psel (j + 1) * Qsel j

/-- 行列式公式 C_j = 2(−1)^{j+1}（由 A 的 sel_determinant，补 j=0）。 -/
theorem sel_determinant (j : ℕ) : Csel j = 2 * (-1 : ℤ) ^ (j + 1) := by
  by_cases hj : 1 ≤ j
  · exact _root_.sel_determinant j hj
  · have hj0 : j = 0 := by omega
    subst hj0
    show Csel 0 = 2 * (-1 : ℤ) ^ 1
    simp only [Csel]
    norm_num [Psel, Qsel, selPair]

/-- |C_j| = 2。 -/
theorem Csel_abs (j : ℕ) : |Csel j| = 2 := by
  rw [sel_determinant, abs_mul]
  have hp : |(-1 : ℤ) ^ (j + 1)| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [hp]
  norm_num

/-- Psel 恒奇（全下标）。由 A 的配对奇性引理。 -/
theorem Psel_odd (j : ℕ) : Odd (Psel j) :=
  (selPair_pos_odd 1 3 (by norm_num) (by norm_num) odd_one (by decide : Odd (3 : ℤ)) j).2.2.1

/-- Qsel 恒奇（全下标）。 -/
theorem Qsel_odd (j : ℕ) : Odd (Qsel j) :=
  (selPair_pos_odd 1 1 (by norm_num) (by norm_num) odd_one odd_one j).2.2.1

/-- Qsel 的自然数版本（Qsel 恒正，取 natAbs）。 -/
def Qnat (j : ℕ) : ℕ := (Qsel j).natAbs

/-- Qnat 与 Qsel 的 cast 关系。 -/
theorem Qnat_cast (j : ℕ) : (Qnat j : ℤ) = Qsel j := by
  simp only [Qnat]
  exact Int.natAbs_of_nonneg (le_of_lt (Qsel_pos j))

/-- Qnat 递推（自然数版）。 -/
theorem Qnat_rec (j : ℕ) : Qnat (j + 2) = (4 * j + 6) * Qnat (j + 1) + Qnat j := by
  have hZ : Qsel (j + 2) = (4 * (j : ℤ) + 6) * Qsel (j + 1) + Qsel j := Qsel_rec j
  have hcast : (Qnat (j + 2) : ℤ) = ((4 * j + 6 : ℕ) : ℤ) * (Qnat (j + 1) : ℤ) + (Qnat j : ℤ) := by
    rw [Qnat_cast, Qnat_cast, Qnat_cast]
    push_cast
    exact hZ
  exact_mod_cast hcast

/-- **相邻分母互素**（全下标）：gcd(Q_j, Q_{j+1}) = 1。
    在自然数版 Qnat 上归纳，归纳到 gcd(Q₀,Q₁)=gcd(1,1)=1。
    注意：行列式是 ±2 而非 ±1，互素性必须用 Q 自身递推。 -/
theorem Qsel_succ_coprime (j : ℕ) : Int.gcd (Qsel j) (Qsel (j + 1)) = 1 := by
  have hnat : Nat.gcd (Qnat j) (Qnat (j + 1)) = 1 := by
    induction j with
    | zero => decide
    | succ j ih =>
      show Nat.gcd (Qnat (j + 1)) (Qnat (j + 2)) = 1
      rw [Qnat_rec]
      rw [Nat.gcd_mul_right_add_right, Nat.gcd_comm]
      exact ih
  have hbridge : Int.gcd (Qsel j) (Qsel (j + 1)) = Nat.gcd (Qnat j) (Qnat (j + 1)) := by
    rw [← Qnat_cast, ← Qnat_cast, Int.gcd_natCast_natCast]
  rw [hbridge, hnat]

/-! ### deltaSel：取用 A 的定义与公理（不新增公理） -/

-- A 的 deltaSel j = (Qsel j : ℝ) * Real.exp 1 - (Psel j : ℝ)。
-- F 原约定 Real.exp 1 * (Qsel j) - Psel j，乘法交换后相同；下游证明用 simp only [deltaSel] 展开，兼容。

/-- 实数分母序列 QR j = (Qsel j : ℝ)。 -/
def QR (j : ℕ) : ℝ := (Qsel j : ℝ)

/-- QR 恒正。 -/
theorem QR_pos (j : ℕ) : 0 < QR j := by
  simp only [QR]
  exact_mod_cast Qsel_pos j

/-- QR → +∞。 -/
theorem QR_tendsto_atTop : Tendsto QR atTop atTop := by
  have hge : ∀ᶠ j : ℕ in atTop, (2 : ℝ) ^ j ≤ QR j := by
    apply Filter.eventually_atTop.mpr
    refine ⟨2, fun j hj => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have hZ := Qsel_double k
    have hR : ((2 : ℤ) ^ (k + 2) : ℝ) ≤ (Qsel (k + 2) : ℝ) := by
      exact_mod_cast hZ
    have hpow : ((2 : ℤ) ^ (k + 2) : ℝ) = (2 : ℝ) ^ (k + 2) := by
      push_cast
      ring
    rw [hpow] at hR
    show (2 : ℝ) ^ (k + 2) ≤ QR (k + 2)
    simpa [QR] using hR
  exact tendsto_atTop_mono' atTop hge
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

/-- P_j/Q_j → e（取用 A 的定理）。 -/
theorem Psel_div_Qsel_tendsto_exp :
    Tendsto (fun j : ℕ => (Psel j : ℝ) / (Qsel j : ℝ)) atTop (nhds (Real.exp 1)) :=
  _root_.Psel_div_Qsel_tendsto_exp

/-! ## 1. 记号：Msel / Tsel -/

/-- M_j = round(B·Q_j·π)（最近整数）。 -/
noncomputable def Msel (B : ℕ) (j : ℕ) : ℤ :=
  round ((B : ℝ) * (Qsel j : ℝ) * Real.pi)

/-- T_j = M_j Q_{j+1} − M_{j+1} Q_j（整数交叉积）。 -/
noncomputable def Tsel (B : ℕ) (j : ℕ) : ℤ :=
  Msel B j * Qsel (j + 1) - Msel B (j + 1) * Qsel j

/-- round 误差：|M_j − B Q_j π| ≤ 1/2。 -/
theorem Msel_abs_sub_le (B j : ℕ) :
    |(Msel B j : ℝ) - (B : ℝ) * (Qsel j : ℝ) * Real.pi| ≤ 1 / 2 := by
  have := abs_sub_round ((B : ℝ) * (Qsel j : ℝ) * Real.pi)
  rw [abs_sub_comm]
  simpa [Msel] using this

/-- round 商误差：|M_j/Q_j − Bπ| ≤ 1/(2Q_j)。 -/
theorem Msel_div_sub_le (B j : ℕ) :
    |(Msel B j : ℝ) / (Qsel j : ℝ) - (B : ℝ) * Real.pi| ≤
      1 / (2 * (Qsel j : ℝ)) := by
  have hQpos : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j
  have h := Msel_abs_sub_le B j
  have hdiv : |(Msel B j : ℝ) / (Qsel j : ℝ) - (B : ℝ) * Real.pi| =
      |(Msel B j : ℝ) - (B : ℝ) * (Qsel j : ℝ) * Real.pi| / (Qsel j : ℝ) := by
    have hinner : (Msel B j : ℝ) / (Qsel j : ℝ) - (B : ℝ) * Real.pi =
        ((Msel B j : ℝ) - (B : ℝ) * (Qsel j : ℝ) * Real.pi) / (Qsel j : ℝ) := by
      field_simp
    rw [hinner, abs_div, abs_of_pos hQpos]
  rw [hdiv]
  calc |(Msel B j : ℝ) - (B : ℝ) * (Qsel j : ℝ) * Real.pi| / (Qsel j : ℝ)
      ≤ (1 / 2) / (Qsel j : ℝ) := by gcongr
    _ = 1 / (2 * (Qsel j : ℝ)) := by ring

/-! ## 2. pair_iff：Bézout 交叉积等价（技术核心之一） -/

/-- **pair_iff**：设 gcd(a,b)=1，U,V 整数，则
    U·b = V·a ↔ ∃ A:ℤ, U = A·a ∧ V = A·b。
    证明：Bézout 取 r,s 使 r·a+s·b=1，令 A = r·U+s·V。 -/
theorem pair_iff {a b U V : ℤ} (hgcd : Int.gcd a b = 1) :
    U * b = V * a ↔ ∃ A : ℤ, U = A * a ∧ V = A * b := by
  constructor
  · intro h
    have hbz : (Int.gcd a b : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b :=
      Int.gcd_eq_gcd_ab a b
    rw [hgcd] at hbz
    norm_num at hbz
    set r := Int.gcdA a b
    set s := Int.gcdB a b
    use r * U + s * V
    constructor
    · have h1 : U = U * (a * r + b * s) := by rw [← hbz]; ring
      have h2 : U * (a * r + b * s) = (r * U + s * V) * a := by
        calc U * (a * r + b * s) = U * a * r + U * b * s := by ring
          _ = U * a * r + V * a * s := by rw [h]
          _ = (r * U + s * V) * a := by ring
      linarith
    · have h1 : V = V * (a * r + b * s) := by rw [← hbz]; ring
      have h2 : V * (a * r + b * s) = (r * U + s * V) * b := by
        calc V * (a * r + b * s) = V * a * r + V * b * s := by ring
          _ = U * b * r + V * b * s := by rw [← h]
          _ = (r * U + s * V) * b := by ring
      linarith
  · rintro ⟨A, rfl, rfl⟩
    ring

/-! ## 3. limit_integer：整数序列收敛 ⇒ 极限为整数（技术核心之二） -/

/-- **limit_integer**：整数值实序列收敛，则极限是整数。
    自证（ε=1/3）：收敛 ⇒ 最终常数（两整数距离 <1 必相等）。 -/
theorem limit_integer {a : ℕ → ℤ} {L : ℝ}
    (h : Tendsto (fun j : ℕ => (a j : ℝ)) atTop (nhds L)) :
    ∃ A : ℤ, L = (A : ℝ) := by
  have hmetric := Metric.tendsto_atTop.mp h (1 / 3) (by norm_num)
  obtain ⟨N, hN⟩ := hmetric
  have heq : ∀ j ≥ N, ∀ k ≥ N, a j = a k := by
    intro j hj k hk
    have hj' := hN j hj
    have hk' := hN k hk
    have hdist : dist ((a j : ℝ)) ((a k : ℝ)) < 1 := by
      have h1 : dist ((a j : ℝ)) ((a k : ℝ)) ≤
          dist ((a j : ℝ)) L + dist L ((a k : ℝ)) := dist_triangle _ _ _
      have h2 : dist ((a j : ℝ)) L < 1 / 3 := hj'
      have h3 : dist L ((a k : ℝ)) < 1 / 3 := by
        rw [dist_comm]; exact hk'
      linarith
    have hreal : |(a j : ℝ) - (a k : ℝ)| < 1 := by
      simpa [Real.dist_eq] using hdist
    have hz : |a j - a k| < 1 := by
      have := hreal
      rw [← Int.cast_sub] at this
      exact_mod_cast this
    have hz' : a j - a k = 0 := by
      have : |a j - a k| = 0 := by
        have hnonneg : 0 ≤ |a j - a k| := abs_nonneg _
        omega
      exact abs_eq_zero.mp this
    omega
  use a N
  have hevent : ∀ᶠ j in atTop, (a j : ℝ) = (a N : ℝ) := by
    apply Filter.eventually_atTop.mpr
    exact ⟨N, fun j hj => by rw [heq j hj N (le_rfl)]⟩
  have hconst : Tendsto (fun _ : ℕ => (a N : ℝ)) atTop (nhds (a N : ℝ)) :=
    tendsto_const_nhds
  have hL : Tendsto (fun j : ℕ => (a j : ℝ)) atTop (nhds (a N : ℝ)) := by
    apply hconst.congr'
    filter_upwards [hevent] with j hj
    exact hj.symm
  exact tendsto_nhds_unique h hL

/-! ## 4. forward：(a) ⇒ (b) -/

/-- 若 B(e+π)=A 整数，则最终 M_j = A·Q_j − B·P_j。 -/
theorem forward_Msel {B : ℕ} {A : ℤ}
    (hA : (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ)) :
    ∀ᶠ j in atTop, Msel B j = A * Qsel j - (B : ℤ) * Psel j := by
  have hδ : ∀ᶠ j in atTop, |(B : ℝ) * deltaSel j| < 1 / 2 := by
    have hB : Tendsto (fun j => (B : ℝ) * deltaSel j) atTop (nhds 0) := by
      simpa using deltaSel_tendsto_zero.const_mul (B : ℝ)
    have := Metric.tendsto_atTop.mp hB (1 / 2) (by norm_num)
    obtain ⟨N, hN⟩ := this
    apply Filter.eventually_atTop.mpr
    refine ⟨N, fun j hj => ?_⟩
    have := hN j hj
    simpa [Real.dist_eq] using this
  apply Filter.eventually_atTop.mpr
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hδ
  refine ⟨N, fun j hj => ?_⟩
  have hsmall := hN j hj
  set K : ℤ := A * Qsel j - (B : ℤ) * Psel j
  have hreal : |(B : ℝ) * (Qsel j : ℝ) * Real.pi - (K : ℝ)| < 1 / 2 := by
    have hdecomp : (B : ℝ) * (Qsel j : ℝ) * Real.pi =
        (A : ℝ) * (Qsel j : ℝ) - (B : ℝ) * (Psel j : ℝ) - (B : ℝ) * deltaSel j := by
      have hBpi : (B : ℝ) * Real.pi = (A : ℝ) - (B : ℝ) * Real.exp 1 := by linarith
      calc (B : ℝ) * (Qsel j : ℝ) * Real.pi
          = ((B : ℝ) * Real.pi) * (Qsel j : ℝ) := by ring
        _ = ((A : ℝ) - (B : ℝ) * Real.exp 1) * (Qsel j : ℝ) := by rw [hBpi]
        _ = (A : ℝ) * (Qsel j : ℝ) - (B : ℝ) * (Real.exp 1 * (Qsel j : ℝ)) := by ring
        _ = (A : ℝ) * (Qsel j : ℝ) - (B : ℝ) * ((Psel j : ℝ) + deltaSel j) := by
            simp only [deltaSel]; ring
        _ = (A : ℝ) * (Qsel j : ℝ) - (B : ℝ) * (Psel j : ℝ) - (B : ℝ) * deltaSel j := by ring
    have hKreal : (K : ℝ) = (A : ℝ) * (Qsel j : ℝ) - (B : ℝ) * (Psel j : ℝ) := by
      simp only [K]; push_cast; ring
    rw [hdecomp, hKreal]
    have : (A : ℝ) * (Qsel j : ℝ) - (B : ℝ) * (Psel j : ℝ) - (B : ℝ) * deltaSel j -
        ((A : ℝ) * (Qsel j : ℝ) - (B : ℝ) * (Psel j : ℝ)) = -((B : ℝ) * deltaSel j) := by ring
    rw [this, abs_neg]
    exact hsmall
  have hround : round ((B : ℝ) * (Qsel j : ℝ) * Real.pi) = K := by
    rw [round_eq_iff]
    constructor
    · have := abs_lt.mp hreal
      linarith
    · have := abs_lt.mp hreal
      linarith
  exact hround

/-- **(a) ⇒ (b)**：B(e+π) 整数 ⇒ 最终 T_j = −B·C_j。 -/
theorem theorem11_forward {B : ℕ} :
    (∃ A : ℤ, (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ)) →
    ∀ᶠ j in atTop, Tsel B j = -(B : ℤ) * Csel j := by
  rintro ⟨A, hA⟩
  have hM := forward_Msel hA
  apply Filter.eventually_atTop.mpr
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hM
  refine ⟨N, fun j hj => ?_⟩
  have hj1 : Msel B j = A * Qsel j - (B : ℤ) * Psel j := hN j hj
  have hj2 : Msel B (j + 1) = A * Qsel (j + 1) - (B : ℤ) * Psel (j + 1) :=
    hN (j + 1) (by omega)
  simp only [Tsel, Csel, hj1, hj2]
  ring

/-! ## 5. converse：(c) ⇒ (a) -/

/-- 无穷多匹配 ⇒ 存在严格递增子列 φ 使每对都匹配。 -/
theorem exists_strictMono_match {B : ℕ}
    (hc : ∀ N : ℕ, ∃ j ≥ N, Tsel B j = -(B : ℤ) * Csel j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, Tsel B (φ k) = -(B : ℤ) * Csel (φ k) := by
  have hstep : ∀ n : ℕ, ∃ j > n, Tsel B j = -(B : ℤ) * Csel j := by
    intro n
    obtain ⟨j, hj, hjm⟩ := hc (n + 1)
    exact ⟨j, by omega, hjm⟩
  choose f hf using hstep
  let φ : ℕ → ℕ := fun k => Nat.recOn k (f 0) (fun _ prev => f prev)
  have hφsucc : ∀ k, φ (k + 1) = f (φ k) := fun _ => rfl
  have hmatch : ∀ k, Tsel B (φ k) = -(B : ℤ) * Csel (φ k) := by
    intro k
    induction k with
    | zero => exact (hf 0).2
    | succ k ih =>
      rw [hφsucc]
      exact (hf (φ k)).2
  have hstrict : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro k
    rw [hφsucc]
    exact (hf (φ k)).1
  exact ⟨φ, hstrict, hmatch⟩

/-- 匹配指标处的交叉积等式：T_j = −B·C_j ⇒ U_j·Q_{j+1} = U_{j+1}·Q_j，
    其中 U_j = M_j + B·P_j。 -/
theorem match_cross {B j : ℕ}
    (hm : Tsel B j = -(B : ℤ) * Csel j) :
    (Msel B j + (B : ℤ) * Psel j) * Qsel (j + 1) =
      (Msel B (j + 1) + (B : ℤ) * Psel (j + 1)) * Qsel j := by
  simp only [Tsel, Csel] at hm
  linarith

/-- **(c) ⇒ (a)**：无穷多匹配 ⇒ B(e+π) 整数。 -/
theorem theorem11_converse {B : ℕ} :
    (∀ N : ℕ, ∃ j ≥ N, Tsel B j = -(B : ℤ) * Csel j) →
    ∃ A : ℤ, (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ) := by
  intro hc
  obtain ⟨φ, hφstrict, hφmatch⟩ := exists_strictMono_match hc
  let U : ℕ → ℤ := fun j => Msel B j + (B : ℤ) * Psel j
  have hcross : ∀ k, U (φ k) * Qsel (φ k + 1) = U (φ k + 1) * Qsel (φ k) := by
    intro k
    exact match_cross (hφmatch k)
  have hcoprime : ∀ k, Int.gcd (Qsel (φ k)) (Qsel (φ k + 1)) = 1 :=
    fun k => Qsel_succ_coprime (φ k)
  have hA : ∀ k, ∃ A : ℤ, U (φ k) = A * Qsel (φ k) ∧ U (φ k + 1) = A * Qsel (φ k + 1) := by
    intro k
    exact (pair_iff (hcoprime k)).mp (hcross k)
  choose Ak hAk using hA
  have hAreal : ∀ k, (Ak k : ℝ) =
      (Msel B (φ k) : ℝ) / (Qsel (φ k) : ℝ) +
      (B : ℝ) * ((Psel (φ k) : ℝ) / (Qsel (φ k) : ℝ)) := by
    intro k
    have hQne : (Qsel (φ k) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Qsel_pos (φ k))
    have hU := (hAk k).1
    have hdiv : (Ak k : ℝ) = (U (φ k) : ℝ) / (Qsel (φ k) : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hU
      push_cast at this
      field_simp at this ⊢
      linarith
    rw [hdiv]
    simp only [U]
    push_cast
    field_simp
  have hAk_tendsto : Tendsto (fun k => (Ak k : ℝ)) atTop
      (nhds ((B : ℝ) * (Real.pi + Real.exp 1))) := by
    have hQφ : Tendsto (fun k => QR (φ k)) atTop atTop :=
      QR_tendsto_atTop.comp hφstrict.tendsto_atTop
    have herr : Tendsto (fun k => 1 / (2 * QR (φ k))) atTop (nhds 0) := by
      have hbase := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hQφ
      have hfeq : (fun k => 1 / (2 * QR (φ k))) = (fun k => (1 / 2) * (1 / QR (φ k))) := by
        funext k
        field_simp
      rw [hfeq]
      simpa using hbase.const_mul (1 / 2 : ℝ)
    have hM_tendsto : Tendsto (fun k => (Msel B (φ k) : ℝ) / (Qsel (φ k) : ℝ))
        atTop (nhds ((B : ℝ) * Real.pi)) := by
      have hbound : ∀ k, |(Msel B (φ k) : ℝ) / (Qsel (φ k) : ℝ) - (B : ℝ) * Real.pi| ≤
          1 / (2 * QR (φ k)) := by
        intro k
        simpa [QR] using Msel_div_sub_le B (φ k)
      have hlower : ∀ k, -(1 / (2 * QR (φ k))) ≤
          (Msel B (φ k) : ℝ) / (Qsel (φ k) : ℝ) - (B : ℝ) * Real.pi := by
        intro k
        exact (abs_le.mp (hbound k)).1
      have hupper : ∀ k, (Msel B (φ k) : ℝ) / (Qsel (φ k) : ℝ) - (B : ℝ) * Real.pi ≤
          1 / (2 * QR (φ k)) := by
        intro k
        exact (abs_le.mp (hbound k)).2
      have hnegε : Tendsto (fun k => -(1 / (2 * QR (φ k)))) atTop (nhds 0) := by
        simpa using herr.neg
      have hsub : Tendsto (fun k => (Msel B (φ k) : ℝ) / (Qsel (φ k) : ℝ) - (B : ℝ) * Real.pi)
          atTop (nhds 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' hnegε herr
          (by filter_upwards with k; exact hlower k)
          (by filter_upwards with k; exact hupper k)
      have hbase := (tendsto_const_nhds (x := (B : ℝ) * Real.pi)).add hsub
      have hfeq : (fun k => (Msel B (φ k) : ℝ) / (Qsel (φ k) : ℝ)) =
          (fun k => (B : ℝ) * Real.pi +
            ((Msel B (φ k) : ℝ) / (Qsel (φ k) : ℝ) - (B : ℝ) * Real.pi)) := by
        funext k
        ring
      rw [hfeq]
      simpa using hbase
    have hP_tendsto : Tendsto (fun k => (B : ℝ) * ((Psel (φ k) : ℝ) / (Qsel (φ k) : ℝ)))
        atTop (nhds ((B : ℝ) * Real.exp 1)) := by
      have := Psel_div_Qsel_tendsto_exp.comp hφstrict.tendsto_atTop
      exact this.const_mul (B : ℝ)
    have hsum := hM_tendsto.add hP_tendsto
    convert hsum using 1
    · funext k
      exact hAreal k
    · ring_nf
  obtain ⟨A, hA⟩ := limit_integer hAk_tendsto
  use A
  linarith

/-! ## 6. theorem11_three_equiv：三等价 -/

/-- (b) ⇒ (c)：最终 ⇒ 无穷多（atTop 无穷）。 -/
theorem eventually_imp_infinite {B : ℕ}
    (hb : ∀ᶠ j in atTop, Tsel B j = -(B : ℤ) * Csel j) :
    ∀ N : ℕ, ∃ j ≥ N, Tsel B j = -(B : ℤ) * Csel j := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hb
  intro N
  refine ⟨max N N₀, le_max_left _ _, ?_⟩
  exact hN₀ (max N N₀) (le_max_right _ _)

/-- **Theorem 11（三等价）**：对固定 B，
    (a) B(e+π)∈ℤ ↔ (b) 最终 T_j=−B·C_j ↔ (c) 无穷多匹配。
    这是等价判据，不是 e+π 无理性的证明；「对每个 B 匹配集有限」仍开放。 -/
theorem theorem11_three_equiv (B : ℕ) :
    ((∃ A : ℤ, (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ)) ↔
      (∀ᶠ j in atTop, Tsel B j = -(B : ℤ) * Csel j)) ∧
    ((∀ᶠ j in atTop, Tsel B j = -(B : ℤ) * Csel j) ↔
      (∀ N : ℕ, ∃ j ≥ N, Tsel B j = -(B : ℤ) * Csel j)) := by
  constructor
  · constructor
    · exact theorem11_forward
    · intro hb
      exact theorem11_converse (eventually_imp_infinite hb)
  · constructor
    · exact eventually_imp_infinite
    · intro hc
      exact theorem11_forward (theorem11_converse hc)

/-! ## 7. quantitative_bound：定量推论 -/

/-- 匹配指标处：h = dist(B(e+π), ℤ) ≤ (1/2 + B|δ_j|)/Q_j。 -/
theorem quantitative_bound {B j : ℕ}
    (hm : Tsel B j = -(B : ℤ) * Csel j) :
    distToNearestInt ((B : ℝ) * (Real.exp 1 + Real.pi)) ≤
      (1 / 2 + (B : ℝ) * |deltaSel j|) / (Qsel j : ℝ) := by
  have hcross := match_cross hm
  have hcoprime := Qsel_succ_coprime j
  obtain ⟨Aj, hAj1, hAj2⟩ := (pair_iff hcoprime).mp hcross
  have hdist : distToNearestInt ((B : ℝ) * (Real.exp 1 + Real.pi)) ≤
      |(B : ℝ) * (Real.exp 1 + Real.pi) - (Aj : ℝ)| :=
    distToNearestInt_le _ Aj
  have hQpos : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j
  have hQne : (Qsel j : ℝ) ≠ 0 := ne_of_gt hQpos
  have hAjreal : (Aj : ℝ) = (Msel B j : ℝ) / (Qsel j : ℝ) +
      (B : ℝ) * ((Psel j : ℝ) / (Qsel j : ℝ)) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hAj1
    push_cast at this
    have hdiv : (Aj : ℝ) = ((Msel B j : ℝ) + (B : ℝ) * (Psel j : ℝ)) / (Qsel j : ℝ) := by
      field_simp at this ⊢
      linarith
    rw [hdiv]
    field_simp
  have hbound : |(B : ℝ) * (Real.exp 1 + Real.pi) - (Aj : ℝ)| ≤
      (1 / 2 + (B : ℝ) * |deltaSel j|) / (Qsel j : ℝ) := by
    rw [hAjreal]
    have hdecomp : (B : ℝ) * (Real.exp 1 + Real.pi) -
        ((Msel B j : ℝ) / (Qsel j : ℝ) + (B : ℝ) * ((Psel j : ℝ) / (Qsel j : ℝ))) =
        ((B : ℝ) * Real.pi - (Msel B j : ℝ) / (Qsel j : ℝ)) +
        (B : ℝ) * deltaSel j / (Qsel j : ℝ) := by
      simp only [deltaSel]
      field_simp
      ring
    rw [hdecomp]
    have htri : |((B : ℝ) * Real.pi - (Msel B j : ℝ) / (Qsel j : ℝ)) +
        (B : ℝ) * deltaSel j / (Qsel j : ℝ)| ≤
        |(B : ℝ) * Real.pi - (Msel B j : ℝ) / (Qsel j : ℝ)| +
        |(B : ℝ) * deltaSel j / (Qsel j : ℝ)| := abs_add_le _ _
    have h1 : |(B : ℝ) * Real.pi - (Msel B j : ℝ) / (Qsel j : ℝ)| ≤
        1 / (2 * (Qsel j : ℝ)) := by
      have := Msel_div_sub_le B j
      rw [abs_sub_comm]
      exact this
    have h2 : |(B : ℝ) * deltaSel j / (Qsel j : ℝ)| =
        (B : ℝ) * |deltaSel j| / (Qsel j : ℝ) := by
      rw [abs_div, abs_mul, abs_of_nonneg (by exact_mod_cast Nat.zero_le B : (0:ℝ) ≤ (B:ℝ)),
        abs_of_pos hQpos]
    have hsum : 1 / (2 * (Qsel j : ℝ)) + (B : ℝ) * |deltaSel j| / (Qsel j : ℝ) =
        (1 / 2 + (B : ℝ) * |deltaSel j|) / (Qsel j : ℝ) := by
      field_simp
    linarith
  linarith

/-- 更强界（j+1 代替 j，同一 A_j）：h ≤ (1/2 + B|δ_{j+1}|)/Q_{j+1}。 -/
theorem quantitative_bound_succ {B j : ℕ}
    (hm : Tsel B j = -(B : ℤ) * Csel j) :
    distToNearestInt ((B : ℝ) * (Real.exp 1 + Real.pi)) ≤
      (1 / 2 + (B : ℝ) * |deltaSel (j + 1)|) / (Qsel (j + 1) : ℝ) := by
  have hcross := match_cross hm
  have hcoprime := Qsel_succ_coprime j
  obtain ⟨Aj, hAj1, hAj2⟩ := (pair_iff hcoprime).mp hcross
  have hdist : distToNearestInt ((B : ℝ) * (Real.exp 1 + Real.pi)) ≤
      |(B : ℝ) * (Real.exp 1 + Real.pi) - (Aj : ℝ)| :=
    distToNearestInt_le _ Aj
  have hQpos : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1)
  have hQne : (Qsel (j + 1) : ℝ) ≠ 0 := ne_of_gt hQpos
  have hAjreal : (Aj : ℝ) = (Msel B (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) +
      (B : ℝ) * ((Psel (j + 1) : ℝ) / (Qsel (j + 1) : ℝ)) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hAj2
    push_cast at this
    have hdiv : (Aj : ℝ) = ((Msel B (j + 1) : ℝ) + (B : ℝ) * (Psel (j + 1) : ℝ)) /
        (Qsel (j + 1) : ℝ) := by
      field_simp at this ⊢
      linarith
    rw [hdiv]
    field_simp
  have hbound : |(B : ℝ) * (Real.exp 1 + Real.pi) - (Aj : ℝ)| ≤
      (1 / 2 + (B : ℝ) * |deltaSel (j + 1)|) / (Qsel (j + 1) : ℝ) := by
    rw [hAjreal]
    have hdecomp : (B : ℝ) * (Real.exp 1 + Real.pi) -
        ((Msel B (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) +
          (B : ℝ) * ((Psel (j + 1) : ℝ) / (Qsel (j + 1) : ℝ))) =
        ((B : ℝ) * Real.pi - (Msel B (j + 1) : ℝ) / (Qsel (j + 1) : ℝ)) +
        (B : ℝ) * deltaSel (j + 1) / (Qsel (j + 1) : ℝ) := by
      simp only [deltaSel]
      field_simp
      ring
    rw [hdecomp]
    have htri := abs_add_le ((B : ℝ) * Real.pi - (Msel B (j + 1) : ℝ) / (Qsel (j + 1) : ℝ))
      ((B : ℝ) * deltaSel (j + 1) / (Qsel (j + 1) : ℝ))
    have h1 : |(B : ℝ) * Real.pi - (Msel B (j + 1) : ℝ) / (Qsel (j + 1) : ℝ)| ≤
        1 / (2 * (Qsel (j + 1) : ℝ)) := by
      have := Msel_div_sub_le B (j + 1)
      rw [abs_sub_comm]
      exact this
    have h2 : |(B : ℝ) * deltaSel (j + 1) / (Qsel (j + 1) : ℝ)| =
        (B : ℝ) * |deltaSel (j + 1)| / (Qsel (j + 1) : ℝ) := by
      rw [abs_div, abs_mul, abs_of_nonneg (by exact_mod_cast Nat.zero_le B : (0:ℝ) ≤ (B:ℝ)),
        abs_of_pos hQpos]
    have hsum : 1 / (2 * (Qsel (j + 1) : ℝ)) +
        (B : ℝ) * |deltaSel (j + 1)| / (Qsel (j + 1) : ℝ) =
        (1 / 2 + (B : ℝ) * |deltaSel (j + 1)|) / (Qsel (j + 1) : ℝ) := by
      field_simp
    linarith
  linarith

/-- （可选推论）h > 0 ⇒ 最终所有对都失配（由 quantitative_bound_succ 与 Q_j→∞）。 -/
theorem hpos_eventually_mismatch {B : ℕ}
    (hpos : 0 < distToNearestInt ((B : ℝ) * (Real.exp 1 + Real.pi))) :
    ∀ᶠ j in atTop, Tsel B j ≠ -(B : ℤ) * Csel j := by
  have hδabs : Tendsto (fun j => |deltaSel j|) atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero deltaSel).mp deltaSel_tendsto_zero
  have hδ : Tendsto (fun j => (B : ℝ) * |deltaSel j|) atTop (nhds 0) := by
    simpa using hδabs.const_mul (B : ℝ)
  have hnum : Tendsto (fun j => 1 / 2 + (B : ℝ) * |deltaSel j|) atTop (nhds (1 / 2)) := by
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add hδ
  have hbound_tendsto : Tendsto (fun j => (1 / 2 + (B : ℝ) * |deltaSel (j + 1)|) /
      QR (j + 1)) atTop (nhds 0) := by
    have hnum' : Tendsto (fun j => 1 / 2 + (B : ℝ) * |deltaSel (j + 1)|) atTop (nhds (1 / 2)) :=
      hnum.comp (tendsto_add_atTop_nat 1)
    have hQ' : Tendsto (fun j => QR (j + 1)) atTop atTop :=
      QR_tendsto_atTop.comp (tendsto_add_atTop_nat 1)
    exact hnum'.div_atTop hQ'
  have hlt : ∀ᶠ j in atTop, (1 / 2 + (B : ℝ) * |deltaSel (j + 1)|) /
      QR (j + 1) < distToNearestInt ((B : ℝ) * (Real.exp 1 + Real.pi)) := by
    have := Metric.tendsto_atTop.mp hbound_tendsto
      (distToNearestInt ((B : ℝ) * (Real.exp 1 + Real.pi))) hpos
    obtain ⟨N, hN⟩ := this
    apply Filter.eventually_atTop.mpr
    refine ⟨N, fun j hj => ?_⟩
    have := hN j hj
    have hnonneg : 0 ≤ (1 / 2 + (B : ℝ) * |deltaSel (j + 1)|) / QR (j + 1) := by
      apply div_nonneg
      · positivity
      · exact le_of_lt (QR_pos (j + 1))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at this
    exact this
  filter_upwards [hlt] with j hj
  intro hm
  have := quantitative_bound_succ hm
  have hQR : QR (j + 1) = (Qsel (j + 1) : ℝ) := rfl
  rw [hQR] at hj
  linarith

/-! ## 8. 诚实声明（定理形式记录开放目标，不作为已证结论） -/

/-- 研究目标（开放，**未证明**，仅以注释形式记录，不声明为定理）：
    「对每个正整数 B，匹配集 {j | Tsel B j = −B·Csel j} 有限」
    等价于 e+π 无理（由 theorem11_three_equiv：若 B(e+π) 非整数则匹配集有限）。
    对 π 的特定最近整数证明该有限性，在本方法中仍开放。
    本文件不声称解决 e+π 无理性。 -/
theorem honesty_note : True := trivial

end AdjacentWitness

/-! ## #print axioms 审计（联合编译归一版） -/

#print axioms AdjacentWitness.Psel_rec
#print axioms AdjacentWitness.Qsel_rec
#print axioms AdjacentWitness.Qsel_pos
#print axioms AdjacentWitness.Qsel_ge_one
#print axioms AdjacentWitness.Qsel_monotone
#print axioms AdjacentWitness.Qsel_double
#print axioms AdjacentWitness.Qsel_tendsto_atTop
#print axioms AdjacentWitness.sel_determinant
#print axioms AdjacentWitness.Csel_abs
#print axioms AdjacentWitness.Psel_odd
#print axioms AdjacentWitness.Qsel_odd
#print axioms AdjacentWitness.Qnat_cast
#print axioms AdjacentWitness.Qnat_rec
#print axioms AdjacentWitness.Qsel_succ_coprime
#print axioms AdjacentWitness.QR_pos
#print axioms AdjacentWitness.QR_tendsto_atTop
#print axioms AdjacentWitness.Psel_div_Qsel_tendsto_exp
#print axioms AdjacentWitness.Msel_abs_sub_le
#print axioms AdjacentWitness.Msel_div_sub_le
#print axioms AdjacentWitness.pair_iff
#print axioms AdjacentWitness.limit_integer
#print axioms AdjacentWitness.forward_Msel
#print axioms AdjacentWitness.theorem11_forward
#print axioms AdjacentWitness.exists_strictMono_match
#print axioms AdjacentWitness.match_cross
#print axioms AdjacentWitness.theorem11_converse
#print axioms AdjacentWitness.eventually_imp_infinite
#print axioms AdjacentWitness.theorem11_three_equiv
#print axioms AdjacentWitness.quantitative_bound
#print axioms AdjacentWitness.quantitative_bound_succ
#print axioms AdjacentWitness.hpos_eventually_mismatch
#print axioms AdjacentWitness.honesty_note