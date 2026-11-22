import Mathlib
import EpiFormal.EulerConvergents
import EpiFormal.Measure
import EpiFormal.MeiburgConvergence
import EpiFormal.Alekseyev

/-!
# 子任务 D：符号聚类（S5 Theorem 7 + Theorem 8）—— 联合编译归一版

本文件为「总」联合编译归一版：地基统一取用 A 组 `EpiFormal.EulerConvergents`
（顶层 Psel/Qsel/deltaSel/selPair 与全部已证引理、两条 deltaSel 公理），
删除 D 原逐字内联的地基副本；Theorem 7 / Theorem 8 主体证明原样保留。

**范围声明（Arithmetic scope，原文诚实声明，必须保留）**：这些构造自由选取 `x`，
没有任何一个确定了 `x = Bπ` 的实际缺陷。在有理和假设下那些缺陷最终消失；
对每个 `B` 排除该行为将排除所有有理仿射关系。**e+π 无理性仍是开放问题**，
本文件不声称、也不暗示解决该问题。

定理 7 与定理 8 的证明均不依赖两条 deltaSel 公理（关于任意实数 x 的结构定理）。
-/

open Filter Topology Real Set
open scoped ENNReal

/-! ## D 组主体：符号聚类 -/

namespace SignedClusters

/-! ## 基本定义 -/

/-- 最近整数 `M_j(x) = round(Q_j x)`。 -/
noncomputable def Mseq (x : ℝ) (j : ℕ) : ℤ := round ((Qsel j : ℝ) * x)

/-- 符号残差 `ε_j(x) = Q_j x − M_j(x)`。 -/
noncomputable def eps (x : ℝ) (j : ℕ) : ℝ := (Qsel j : ℝ) * x - (Mseq x j : ℝ)

/-- 整数缺陷 `D_j(x) = M_{j+1} − (4j+2)M_j − M_{j−1}`。 -/
noncomputable def defect (x : ℝ) (j : ℕ) : ℤ :=
  Mseq x (j + 1) - (4 * (j : ℤ) + 2) * Mseq x j - Mseq x (j - 1)

/-- `S(x) = limsup_j j·‖Q_j x‖`（ENNReal 值域，有限即 `< ∞`）。 -/
noncomputable def S (x : ℝ) : ℝ≥0∞ :=
  ⨅ N : ℕ, ⨆ j : {j // N ≤ j}, ENNReal.ofReal ((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x))

/-- 聚类集：严格递增子列的极限全体。 -/
def clusterSet (a : ℕ → ℝ) : Set ℝ :=
  {t | ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (a ∘ φ) atTop (nhds t)}

/-- 无穷多次取到的整数缺陷值。 -/
def recurrentDefects (x : ℝ) : Set ℤ :=
  {k | ∀ N, ∃ j, j ≥ N ∧ defect x j = k}

/-! ## 缺陷恒等式与 tracking -/

/-- 缺陷恒等式（实数形式）：`D_j − 4j·ε_j = 2ε_j + ε_{j−1} − ε_{j+1}`。 -/
lemma defect_identity (x : ℝ) (j : ℕ) (hj : 2 ≤ j) :
    (defect x j : ℝ) - 4 * (j : ℝ) * eps x j =
      2 * eps x j + eps x (j - 1) - eps x (j + 1) := by
  have hQ : (Qsel (j + 1) : ℝ) = (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by
    have h := Qsel_rec j hj
    exact_mod_cast h
  simp only [defect, eps, Mseq]
  push_cast
  rw [hQ]
  ring

/-- `S(x)` 有限 ⇒ `ε_j = O(1/j)`。 -/
lemma eps_bigO_of_S_finite (x : ℝ) (hS : S x < ∞) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ j ≥ N, (j : ℝ) * |eps x j| ≤ C := by
  have hS' : S x ≠ ∞ := ne_of_lt hS
  have hfin : ∃ N : ℕ, (⨆ j : {j // N ≤ j},
      ENNReal.ofReal ((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x))) < ∞ := by
    by_contra h
    push Not at h
    have : S x = ∞ := by
      simp only [S]
      apply le_antisymm le_top
      apply le_iInf
      intro N
      exact h N
    exact hS' this
  obtain ⟨N, hN⟩ := hfin
  use (⨆ j : {j // N ≤ j},
      ENNReal.ofReal ((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x))).toReal + 1
  use N
  intro j hj
  have hjN : N ≤ j := hj
  have hle : ENNReal.ofReal ((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x)) ≤
      ⨆ j : {j // N ≤ j}, ENNReal.ofReal ((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x)) :=
    le_iSup (fun j : {j // N ≤ j} =>
      ENNReal.ofReal ((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x))) ⟨j, hjN⟩
  have htop : (⨆ j : {j // N ≤ j},
      ENNReal.ofReal ((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x))) ≠ ∞ := ne_of_lt hN
  have hreal : (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x) ≤
      (⨆ j : {j // N ≤ j},
        ENNReal.ofReal ((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x))).toReal := by
    have := ENNReal.ofReal_le_iff_le_toReal htop |>.mp hle
    exact this
  have habs : |eps x j| = distToNearestInt ((Qsel j : ℝ) * x) := by
    simp only [eps, Mseq, distToNearestInt]
  rw [habs]
  linarith

/-- tracking：`S(x)` 有限 ⇒ `D_j − 4j·ε_j → 0`。 -/
lemma tracking (x : ℝ) (hS : S x < ∞) :
    Tendsto (fun j => (defect x j : ℝ) - 4 * (j : ℝ) * eps x j) atTop (nhds 0) := by
  obtain ⟨C, N, hC⟩ := eps_bigO_of_S_finite x hS
  have hε : ∀ j ≥ N + 1, |eps x j| ≤ C / (j : ℝ) := by
    intro j hj
    have hjN : N ≤ j := by omega
    have hjpos : (0 : ℝ) < (j : ℝ) := by
      have : (0 : ℕ) < j := by omega
      exact_mod_cast this
    have := hC j hjN
    rw [le_div_iff₀ hjpos]
    linarith
  have absTendsto : ∀ (f : ℕ → ℝ) (g : ℕ → ℝ),
      (∀ᶠ j in atTop, |f j| ≤ g j) → Tendsto g atTop (nhds 0) → Tendsto f atTop (nhds 0) := by
    intro f g he hg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hg.neg) hg ?_ ?_
    · filter_upwards [he] with j hj
      exact (abs_le.mp hj).1
    · filter_upwards [he] with j hj
      exact (abs_le.mp hj).2
  have hmain : Tendsto (fun j => 2 * eps x j + eps x (j - 1) - eps x (j + 1)) atTop (nhds 0) := by
    have h1 : Tendsto (fun j => 2 * eps x j) atTop (nhds 0) := by
      apply absTendsto (g := fun j : ℕ => 2 * C / (j : ℝ))
      · apply Filter.eventually_atTop.mpr
        use N + 1
        intro j hj
        have hjε := hε j hj
        have hstep : |2 * eps x j| = 2 * |eps x j| := by
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
        have hstep2 : 2 * |eps x j| ≤ 2 * (C / (j : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hjε (by norm_num)
        have hstep3 : 2 * (C / (j : ℝ)) = 2 * C / (j : ℝ) := by ring
        linarith
      · simpa using tendsto_const_div_atTop_nhds_zero_nat (2 * C)
    have h2 : Tendsto (fun j => eps x (j - 1)) atTop (nhds 0) := by
      apply absTendsto (g := fun j : ℕ => C / ((j : ℝ) - 1))
      · apply Filter.eventually_atTop.mpr
        use N + 2
        intro j hj
        have hj1 : 1 ≤ j := by omega
        have := hε (j - 1) (by omega)
        have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
          rw [Nat.cast_sub hj1]
          simp
        rw [hcast] at this
        exact this
      · have hden : Tendsto (fun j : ℕ => (j : ℝ) - 1) atTop atTop := by
          have := tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
          convert this using 1
        exact tendsto_const_nhds.div_atTop hden
    have h3 : Tendsto (fun j => eps x (j + 1)) atTop (nhds 0) := by
      apply absTendsto (g := fun j : ℕ => C / ((j : ℝ) + 1))
      · apply Filter.eventually_atTop.mpr
        use N
        intro j hj
        have := hε (j + 1) (by omega)
        have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        rw [hcast] at this
        exact this
      · have hden : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
          tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
        exact tendsto_const_nhds.div_atTop hden
    have := h1.add h2 |>.sub h3
    simpa using this
  have heq : ∀ᶠ j : ℕ in atTop,
      (defect x j : ℝ) - 4 * (j : ℝ) * eps x j = 2 * eps x j + eps x (j - 1) - eps x (j + 1) := by
    apply Filter.eventually_atTop.mpr
    use 2
    intro j hj
    exact defect_identity x j hj
  exact hmain.congr' (by filter_upwards [heq] with j hj; exact hj.symm)

/-! ## 整数稳定化 -/

/-- 两个整数若距离 < 1 则相等。 -/
lemma integer_gap (a b : ℤ) (h : |(a : ℝ) - (b : ℝ)| < 1) : a = b := by
  by_contra hne
  have h1 : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
    have hne' : a - b ≠ 0 := by
      intro h0; apply hne; linarith
    have := Int.one_le_abs hne'
    have hcast : ((a - b : ℤ) : ℝ) = (a : ℝ) - (b : ℝ) := by push_cast; ring
    rw [← hcast]
    exact_mod_cast this
  linarith

/-- 整数值序列沿子列收敛 ⇒ 最终常数。 -/
lemma stabilizes (a : ℕ → ℤ) (φ : ℕ → ℕ) (_hφ : StrictMono φ) (t : ℝ)
    (ht : Tendsto (fun n => (a (φ n) : ℝ)) atTop (nhds t)) :
    ∃ k : ℤ, ∃ N : ℕ, ∀ n ≥ N, a (φ n) = k := by
  have hε : ∀ᶠ n : ℕ in atTop, |(a (φ n) : ℝ) - t| < 1 / 3 := by
    have := Metric.tendsto_atTop.mp ht (1 / 3) (by norm_num)
    obtain ⟨N, hN⟩ := this
    apply Filter.eventually_atTop.mpr
    use N
    intro n hn
    have := hN n hn
    simpa [Real.dist_eq] using this
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hε
  use a (φ N)
  use N
  intro n hn
  have hn' : |(a (φ n) : ℝ) - t| < 1 / 3 := hN n hn
  have hN' : |(a (φ N) : ℝ) - t| < 1 / 3 := hN N (le_refl N)
  have hdiff : |(a (φ n) : ℝ) - (a (φ N) : ℝ)| < 1 := by
    calc |(a (φ n) : ℝ) - (a (φ N) : ℝ)|
        = |((a (φ n) : ℝ) - t) - ((a (φ N) : ℝ) - t)| := by ring_nf
      _ ≤ |(a (φ n) : ℝ) - t| + |(a (φ N) : ℝ) - t| := abs_sub _ _
      _ < 1 / 3 + 1 / 3 := add_lt_add hn' hN'
      _ < 1 := by norm_num
  exact integer_gap (a (φ n)) (a (φ N)) hdiff

/-! ## Theorem 7：符号聚类集刻画 -/

/-- 缺陷有界：`S(x)` 有限 ⇒ `D_j` 最终有界。 -/
lemma defect_bounded (x : ℝ) (hS : S x < ∞) :
    ∃ B : ℤ, ∃ N : ℕ, ∀ j ≥ N, |defect x j| ≤ B := by
  obtain ⟨C, N, hC⟩ := eps_bigO_of_S_finite x hS
  have htrack := tracking x hS
  have hδ : ∀ᶠ j : ℕ in atTop, |(defect x j : ℝ) - 4 * (j : ℝ) * eps x j| < 1 := by
    have := Metric.tendsto_atTop.mp htrack 1 (by norm_num)
    obtain ⟨N', hN'⟩ := this
    apply Filter.eventually_atTop.mpr
    use N'
    intro j hj
    simpa [Real.dist_eq] using hN' j hj
  obtain ⟨N', hN'⟩ := Filter.eventually_atTop.mp hδ
  use ⌈4 * C⌉₊ + 2
  use max N (max N' 2) + 1
  intro j hj
  have hjN : N ≤ j := by omega
  have hjN' : N' ≤ j := by omega
  have hj2 : 2 ≤ j := by omega
  have h1 : |(defect x j : ℝ) - 4 * (j : ℝ) * eps x j| < 1 := hN' j hjN'
  have h2 : (j : ℝ) * |eps x j| ≤ C := hC j hjN
  have h3 : |(defect x j : ℝ)| ≤ 4 * C + 1 := by
    have htri : |(defect x j : ℝ)| ≤
        |(defect x j : ℝ) - 4 * (j : ℝ) * eps x j| + |4 * (j : ℝ) * eps x j| := by
      have heq : (defect x j : ℝ) =
          ((defect x j : ℝ) - 4 * (j : ℝ) * eps x j) + 4 * (j : ℝ) * eps x j := by ring
      conv_lhs => rw [heq]
      exact abs_add_le ((defect x j : ℝ) - 4 * (j : ℝ) * eps x j) (4 * (j : ℝ) * eps x j)
    have habs4 : |4 * (j : ℝ) * eps x j| = 4 * ((j : ℝ) * |eps x j|) := by
      have hjnn : (0 : ℝ) ≤ (j : ℝ) := by positivity
      calc |4 * (j : ℝ) * eps x j| = |4 * (j : ℝ)| * |eps x j| := by rw [abs_mul]
        _ = 4 * (j : ℝ) * |eps x j| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4), abs_of_nonneg hjnn]
        _ = 4 * ((j : ℝ) * |eps x j|) := by ring
    have hle : |(defect x j : ℝ) - 4 * (j : ℝ) * eps x j| + |4 * (j : ℝ) * eps x j| ≤
        1 + 4 * C := by
      rw [habs4]
      have : |(defect x j : ℝ) - 4 * (j : ℝ) * eps x j| ≤ 1 := le_of_lt h1
      linarith
    linarith
  have h4 : (|defect x j| : ℝ) ≤ 4 * C + 1 := by
    have : (|defect x j| : ℝ) = |(defect x j : ℝ)| := by rfl
    rw [this]; exact h3
  have h5 : (|defect x j| : ℝ) ≤ (⌈4 * C⌉₊ + 2 : ℝ) := by
    have hceil : (4 * C : ℝ) ≤ ⌈4 * C⌉₊ := Nat.le_ceil _
    linarith
  exact_mod_cast h5

/-- **Theorem 7**：`S(x)` 有限 ⇒ `clusterSet (j·ε_j) = (k ↦ k/4) '' recurrentDefects x`。 -/
theorem theorem7_cluster_set (x : ℝ) (hS : S x < ∞) :
    clusterSet (fun j => (j : ℝ) * eps x j) =
      (fun k : ℤ => (k : ℝ) / 4) '' recurrentDefects x := by
  ext t
  constructor
  · intro ht
    obtain ⟨φ, hφ, htφ⟩ := ht
    have htφ' : Tendsto (fun n => (φ n : ℝ) * eps x (φ n)) atTop (nhds t) := by
      convert htφ using 1
      funext n
      rfl
    have htrack := tracking x hS
    have htrackφ : Tendsto (fun n => (defect x (φ n) : ℝ) - 4 * ((φ n) : ℝ) * eps x (φ n))
        atTop (nhds 0) := by
      have := htrack.comp hφ.tendsto_atTop
      convert this using 1
      funext n
      rfl
    have h4t : Tendsto (fun n => 4 * ((φ n : ℝ) * eps x (φ n))) atTop (nhds (4 * t)) := by
      have := htφ'.const_mul 4
      convert this using 1
    have hDφ : Tendsto (fun n => (defect x (φ n) : ℝ)) atTop (nhds (4 * t)) := by
      have hsum := htrackφ.add h4t
      have hlim : Tendsto (fun n => (defect x (φ n) : ℝ)) atTop (nhds (0 + 4 * t)) := by
        convert hsum using 1
        funext n
        ring
      simpa using hlim
    obtain ⟨k, N, hk⟩ := stabilizes (defect x) φ hφ (4 * t) hDφ
    have hk4t : (k : ℝ) = 4 * t := by
      have hconst : Tendsto (fun n => (defect x (φ n) : ℝ)) atTop (nhds (k : ℝ)) := by
        have heq : ∀ᶠ n : ℕ in atTop, (defect x (φ n) : ℝ) = (k : ℝ) := by
          apply Filter.eventually_atTop.mpr
          use N
          intro n hn
          exact_mod_cast hk n hn
        exact tendsto_const_nhds.congr' (by filter_upwards [heq] with n hn; exact hn.symm)
      exact (tendsto_nhds_unique hDφ hconst).symm
    have hkrec : k ∈ recurrentDefects x := by
      intro N'
      have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
      obtain ⟨n, hn⟩ := (hφtop.eventually (Filter.eventually_ge_atTop N')).exists
      use φ (max n N)
      constructor
      · have : N' ≤ φ (max n N) := by
          have := hn
          have hmono : φ n ≤ φ (max n N) := hφ.monotone (le_max_left _ _)
          linarith
        exact this
      · exact hk (max n N) (le_max_right _ _)
    use k
    constructor
    · exact hkrec
    · linarith
  · intro ht
    obtain ⟨k, hkrec, rfl⟩ := ht
    have hocc : ∀ N, ∃ j, j ≥ N ∧ defect x j = k := hkrec
    let f : ℕ → ℕ := fun n => Nat.recOn n (Nat.find (hocc 0))
      (fun _ prev => Nat.find (hocc (prev + 1)))
    have hf_mono : StrictMono f := by
      apply strictMono_nat_of_lt_succ
      intro n
      show f n < f (n + 1)
      have hspec := (Nat.find_spec (hocc (f n + 1))).1
      have hfnext : f (n + 1) = Nat.find (hocc (f n + 1)) := by
        simp only [f]
      omega
    have hf_occ : ∀ n, defect x (f n) = k := by
      intro n
      induction n with
      | zero =>
        simp only [f]
        exact (Nat.find_spec (hocc 0)).2
      | succ n ih =>
        simp only [f]
        exact (Nat.find_spec (hocc (f n + 1))).2
    use f
    constructor
    · exact hf_mono
    · have htrack := tracking x hS
      have htrackf' : Tendsto (fun (n : ℕ) => (defect x (f n) : ℝ) - 4 * (Nat.cast (f n) : ℝ) * eps x (f n))
          atTop (nhds 0) := by
        have := htrack.comp hf_mono.tendsto_atTop
        convert this using 1
        funext n
        rfl
      have hDf : Tendsto (fun n => (defect x (f n) : ℝ)) atTop (nhds (k : ℝ)) := by
        have heq : (fun n => (defect x (f n) : ℝ)) = (fun _ => (k : ℝ)) := by
          funext n
          exact_mod_cast hf_occ n
        rw [heq]
        exact tendsto_const_nhds
      have h4 : Tendsto (fun (n : ℕ) => 4 * (Nat.cast (f n) * eps x (f n))) atTop (nhds (k : ℝ)) := by
        have hsub := hDf.sub htrackf'
        have hlim : Tendsto (fun (n : ℕ) => 4 * (Nat.cast (f n) * eps x (f n))) atTop (nhds ((k : ℝ) - 0)) := by
          convert hsub using 1
          funext n
          ring
        simpa using hlim
      have := h4.const_mul (1 / 4 : ℝ)
      have hgoal : Tendsto (fun (n : ℕ) => Nat.cast (f n) * eps x (f n)) atTop (nhds ((k : ℝ) / 4)) := by
        convert this using 1
        · funext n
          ring
        · field_simp
      exact hgoal

/-- 聚类集有限。 -/
theorem theorem7_finite (x : ℝ) (hS : S x < ∞) :
    (clusterSet (fun j => (j : ℝ) * eps x j)).Finite := by
  rw [theorem7_cluster_set x hS]
  obtain ⟨B, N, hB⟩ := defect_bounded x hS
  have hsub : recurrentDefects x ⊆ {k : ℤ | |k| ≤ B} := by
    intro k hk
    obtain ⟨j, hjN, hjk⟩ := hk N
    have := hB j hjN
    rw [← hjk]
    exact this
  have hfin : {k : ℤ | |k| ≤ B}.Finite := by
    have : {k : ℤ | |k| ≤ B} ⊆ Set.Icc (-B) B := by
      intro k hk
      simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hk ⊢
      exact abs_le.mp hk
    exact (Set.finite_Icc (-B) B).subset this
  exact (hfin.subset hsub).image _

/-- 聚类集非空。 -/
theorem theorem7_nonempty (x : ℝ) (hS : S x < ∞) :
    (clusterSet (fun j => (j : ℝ) * eps x j)).Nonempty := by
  rw [theorem7_cluster_set x hS]
  obtain ⟨B, N, hB⟩ := defect_bounded x hS
  have hrec : ∃ k : ℤ, k ∈ recurrentDefects x := by
    by_contra h
    push Not at h
    have hfin : {k : ℤ | |k| ≤ B}.Finite := by
      have : {k : ℤ | |k| ≤ B} ⊆ Set.Icc (-B) B := by
        intro k hk
        simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hk ⊢
        exact abs_le.mp hk
      exact (Set.finite_Icc (-B) B).subset this
    classical
    have hex : ∀ k : ℤ, k ∉ recurrentDefects x → ∃ N, ∀ j ≥ N, defect x j ≠ k := by
      intro k hk
      by_contra h'
      push Not at h'
      apply hk
      intro N
      obtain ⟨j, hjN, hjk⟩ := h' N
      exact ⟨j, hjN, hjk⟩
    let Nk : ℤ → ℕ := fun k => if hk : k ∈ recurrentDefects x then 0 else
      Nat.find (hex k hk)
    let S : Finset ℤ := hfin.toFinset
    let Nmax : ℕ := S.sup Nk
    have hj : ∃ j, j ≥ N ∧ j ≥ Nmax + 1 := ⟨max N (Nmax + 1), le_max_left _ _, le_max_right _ _⟩
    obtain ⟨j, hjN, hjmax⟩ := hj
    have hjB : |defect x j| ≤ B := hB j hjN
    have hjin : defect x j ∈ S := by
      simp only [S, Set.Finite.mem_toFinset]
      exact hjB
    have hne : defect x j ≠ defect x j := by
      have hNk : Nk (defect x j) ≤ Nmax := Finset.le_sup hjin
      have hjge : Nk (defect x j) ≤ j := by omega
      have hnotrec : defect x j ∉ recurrentDefects x := h (defect x j)
      have hspec : ∀ j' ≥ Nk (defect x j), defect x j' ≠ defect x j := by
        simp only [Nk, hnotrec, dite_false]
        exact Nat.find_spec (hex (defect x j) hnotrec)
      exact hspec j hjge
    exact hne rfl
  obtain ⟨k, hk⟩ := hrec
  use (k : ℝ) / 4
  use k, hk

/-! ## Theorem 8：实现构造 -/

/-- 带变号缺陷的整数序列 `M^d`。 -/
def MdPair (d : ℕ → ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | 1 => (0, 0)
  | n + 2 =>
    let prev := MdPair d (n + 1)
    (prev.2, (4 * ((n + 2 : ℕ) : ℤ) + 2) * prev.2 + prev.1 + d (n + 2))

def Md (d : ℕ → ℤ) (j : ℕ) : ℤ := (MdPair d j).1

@[simp] lemma Md_zero (d : ℕ → ℤ) : Md d 0 = 0 := rfl
@[simp] lemma Md_one (d : ℕ → ℤ) : Md d 1 = 0 := rfl
@[simp] lemma Md_two (d : ℕ → ℤ) : Md d 2 = 0 := rfl

lemma MdPair_succ (d : ℕ → ℤ) (n : ℕ) :
    MdPair d (n + 2) = ((MdPair d (n + 1)).2,
      (4 * ((n + 2 : ℕ) : ℤ) + 2) * (MdPair d (n + 1)).2 + (MdPair d (n + 1)).1 + d (n + 2)) := rfl

lemma MdPair_snd (d : ℕ → ℤ) (j : ℕ) : (MdPair d j).2 = (MdPair d (j + 1)).1 := by
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero => rfl
    | succ j => rfl

lemma Md_rec_shift (d : ℕ → ℤ) (k : ℕ) :
    Md d (k + 3) = (4 * ((k + 2 : ℕ) : ℤ) + 2) * Md d (k + 2) + Md d (k + 1) + d (k + 2) := by
  have h := congrArg Prod.snd (MdPair_succ d k)
  simp only [Md]
  rw [← MdPair_snd d (k + 2), ← MdPair_snd d (k + 1)]
  exact h

lemma Md_rec (d : ℕ → ℤ) (j : ℕ) (hj : 2 ≤ j) :
    Md d (j + 1) = (4 * (j : ℤ) + 2) * Md d j + Md d (j - 1) + d j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have h := Md_rec_shift d k
  convert h using 1; push_cast; ring

/-- W_j = M_{j+1}Q_j − M_j Q_{j+1}。 -/
def Wd (d : ℕ → ℤ) (j : ℕ) : ℤ := Md d (j + 1) * Qsel j - Md d j * Qsel (j + 1)

@[simp] lemma Wd_one (d : ℕ → ℤ) : Wd d 1 = 0 := by
  simp only [Wd]
  norm_num [Md_two, Md_one]

/-- W 递推：`W_j = d_j·Q_j − W_{j−1}`（j≥2）。 -/
lemma W_rec_d (d : ℕ → ℤ) (j : ℕ) (hj : 2 ≤ j) :
    Wd d j = d j * Qsel j - Wd d (j - 1) := by
  have hj1 : 1 ≤ j := by omega
  have hsub : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  have hM := Md_rec d j hj
  have hQ := Qsel_rec j hj
  simp only [Wd]
  rw [hM, hQ]
  have hR : d j * Qsel j - (Md d (j - 1 + 1) * Qsel (j - 1) - Md d (j - 1) * Qsel (j - 1 + 1)) =
      d j * Qsel j - (Md d j * Qsel (j - 1) - Md d (j - 1) * Qsel j) := by
    rw [hsub]
  rw [hR]
  ring

/-- W 界：`|d_j| ≤ K` ⇒ `|W_j| ≤ 2K·Q_j`（j≥1）。 -/
lemma W_bound_d (d : ℕ → ℤ) (K : ℕ) (hK : ∀ j ≥ 2, |d j| ≤ K) :
    ∀ j ≥ 1, |Wd d j| ≤ 2 * (K : ℤ) * Qsel j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    simp only [Wd_one, abs_zero]
    have hQ : 0 < Qsel 1 := Qsel_pos 1 (by norm_num)
    positivity
  | succ j hj ih =>
    have hj2 : 2 ≤ j + 1 := by omega
    have hrec := W_rec_d d (j + 1) hj2
    have hrec' : Wd d (j + 1) = d (j + 1) * Qsel (j + 1) - Wd d j := by
      have : j + 1 - 1 = j := by omega
      simpa [this] using hrec
    have hQdbl : 2 * Qsel j ≤ Qsel (j + 1) := by
      by_cases hj2' : 2 ≤ j
      · exact Qsel_double j hj2'
      · have hj1' : j = 1 := by omega
        subst hj1'
        norm_num [Qsel, selPair]
    have hQpos : 0 < Qsel (j + 1) := Qsel_pos (j + 1) (by omega)
    have hd : |d (j + 1)| ≤ (K : ℤ) := by exact_mod_cast hK (j + 1) hj2
    have hKnn : (0 : ℤ) ≤ (K : ℤ) := by positivity
    have hstep1 : |d (j + 1)| * Qsel (j + 1) ≤ (K : ℤ) * Qsel (j + 1) :=
      mul_le_mul_of_nonneg_right hd (le_of_lt hQpos)
    have hstep2 : 2 * (K : ℤ) * Qsel j ≤ (K : ℤ) * Qsel (j + 1) := by
      have : 2 * (K : ℤ) * Qsel j = (K : ℤ) * (2 * Qsel j) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hQdbl hKnn
    calc |Wd d (j + 1)|
        = |d (j + 1) * Qsel (j + 1) - Wd d j| := by rw [hrec']
      _ ≤ |d (j + 1) * Qsel (j + 1)| + |Wd d j| := abs_sub _ _
      _ = |d (j + 1)| * Qsel (j + 1) + |Wd d j| := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hQpos)]
      _ ≤ (K : ℤ) * Qsel (j + 1) + 2 * (K : ℤ) * Qsel j :=
        add_le_add hstep1 ih
      _ ≤ (K : ℤ) * Qsel (j + 1) + (K : ℤ) * Qsel (j + 1) :=
        add_le_add (le_refl _) hstep2
      _ = 2 * (K : ℤ) * Qsel (j + 1) := by ring

/-- 增量界。 -/
lemma increments_bound_d (d : ℕ → ℤ) (K : ℕ) (hK : ∀ j ≥ 2, |d j| ≤ K) :
    ∀ j ≥ 1, |(Md d (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) - (Md d j : ℝ) / (Qsel j : ℝ)| ≤
      2 * (K : ℝ) / (Qsel (j + 1) : ℝ) := by
  intro j hj
  have hW := W_bound_d d K hK j hj
  have hQpos : 0 < Qsel j := Qsel_pos j hj
  have hQpos' : 0 < Qsel (j + 1) := Qsel_pos (j + 1) (by omega)
  have hQne : (Qsel j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hQpos)
  have hQne' : (Qsel (j + 1) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hQpos')
  have hdiff : (Md d (j + 1) : ℝ) / (Qsel (j + 1) : ℝ) - (Md d j : ℝ) / (Qsel j : ℝ) =
      (Wd d j : ℝ) / ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ)) := by
    simp only [Wd]
    push_cast
    field_simp [hQne, hQne']
  rw [hdiff]
  have hdenpos : (0 : ℝ) < (Qsel j : ℝ) * (Qsel (j + 1) : ℝ) := by
    exact mul_pos (by exact_mod_cast hQpos) (by exact_mod_cast hQpos')
  have habs : |(Wd d j : ℝ) / ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ))| =
      |(Wd d j : ℝ)| / ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ)) := by
    rw [abs_div, abs_of_pos hdenpos]
  rw [habs]
  have hWreal : |(Wd d j : ℝ)| ≤ 2 * (K : ℝ) * (Qsel j : ℝ) := by
    have : |(Wd d j : ℝ)| = (|Wd d j| : ℝ) := by rfl
    rw [this]
    exact_mod_cast hW
  have hden : (0 : ℝ) < (Qsel j : ℝ) * (Qsel (j + 1) : ℝ) := by positivity
  rw [div_le_iff₀ hden]
  have : (2 * (K : ℝ) / (Qsel (j + 1) : ℝ)) * ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ)) =
      2 * (K : ℝ) * (Qsel j : ℝ) := by
    field_simp [hQne']
  linarith

/-- 增量可和。 -/
lemma increments_summable_d (_d : ℕ → ℤ) (K : ℕ) :
    Summable (fun j : ℕ => 2 * (K : ℝ) / (Qsel (j + 1) : ℝ)) := by
  have hQge : ∀ j : ℕ, (2 : ℝ) ^ j ≤ (Qsel (j + 1) : ℝ) := by
    intro j
    induction j with
    | zero =>
      norm_num [Qsel, selPair]
    | succ n ih =>
      have hdbl : 2 * Qsel (n + 1) ≤ Qsel (n + 2) := Qsel_double_all n
      have hcast : (2 * Qsel (n + 1) : ℝ) ≤ (Qsel (n + 2) : ℝ) := by exact_mod_cast hdbl
      have hpow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by ring
      rw [hpow]
      linarith
  have hle : ∀ j : ℕ, 2 * (K : ℝ) / (Qsel (j + 1) : ℝ) ≤ 2 * (K : ℝ) * (1 / 2 : ℝ) ^ j := by
    intro j
    have hQpos : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by
      exact_mod_cast Qsel_pos (j + 1) (by omega)
    have hQge' : (2 : ℝ) ^ j ≤ (Qsel (j + 1) : ℝ) := hQge j
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    calc 2 * (K : ℝ) / (Qsel (j + 1) : ℝ)
        ≤ 2 * (K : ℝ) / (2 : ℝ) ^ j := by gcongr
      _ = 2 * (K : ℝ) * (1 / 2 : ℝ) ^ j := by
        rw [div_eq_mul_inv, ← inv_pow]
        norm_num
  have hsumm : Summable (fun j : ℕ => 2 * (K : ℝ) * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hnn : ∀ j : ℕ, 0 ≤ 2 * (K : ℝ) / (Qsel (j + 1) : ℝ) := by
    intro j
    apply div_nonneg
    · exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    · exact le_of_lt (by exact_mod_cast Qsel_pos (j + 1) (by omega))
  exact Summable.of_nonneg_of_le hnn hle hsumm

/-- 比值序列收敛。 -/
lemma ratio_converges_d (d : ℕ → ℤ) (K : ℕ) (hK : ∀ j ≥ 2, |d j| ≤ K) :
    ∃ x : ℝ, Tendsto (fun j => (Md d j : ℝ) / (Qsel j : ℝ)) atTop (nhds x) := by
  have hdist : ∀ j : ℕ, dist ((Md d j : ℝ) / (Qsel j : ℝ))
      ((Md d (j + 1) : ℝ) / (Qsel (j + 1) : ℝ)) ≤ 2 * (K : ℝ) / (Qsel (j + 1) : ℝ) := by
    intro j
    by_cases hj : 1 ≤ j
    · have h := increments_bound_d d K hK j hj
      rw [Real.dist_eq, abs_sub_comm]
      exact h
    · have hj0 : j = 0 := by omega
      subst hj0
      simp only [Md_zero]
      norm_num
  have hsumm := increments_summable_d d K
  have hcauchy : CauchySeq (fun j => (Md d j : ℝ) / (Qsel j : ℝ)) :=
    cauchySeq_of_dist_le_of_summable _ hdist hsumm
  exact cauchySeq_tendsto_of_complete hcauchy

/-- 构造的实数 `xOfSeq d`。 -/
noncomputable def xOfSeq (d : ℕ → ℤ) : ℝ := by
  classical
  exact if h : ∃ K : ℕ, ∀ j ≥ 2, |d j| ≤ K then
    Classical.choose (ratio_converges_d d (Classical.choose h) (Classical.choose_spec h))
  else 0

lemma xOfSeq_tendsto (d : ℕ → ℤ) (K : ℕ) (hK : ∀ j ≥ 2, |d j| ≤ K) :
    Tendsto (fun j => (Md d j : ℝ) / (Qsel j : ℝ)) atTop (nhds (xOfSeq d)) := by
  classical
  have h : ∃ K : ℕ, ∀ j ≥ 2, |d j| ≤ K := ⟨K, hK⟩
  have hdef : xOfSeq d =
      Classical.choose (ratio_converges_d d (Classical.choose h) (Classical.choose_spec h)) := by
    simp only [xOfSeq, h, dite_true]
  rw [hdef]
  exact Classical.choose_spec (ratio_converges_d d (Classical.choose h) (Classical.choose_spec h))

/-- 残差界。 -/
lemma residual_bound_d (d : ℕ → ℤ) (K : ℕ) (hK : ∀ j ≥ 2, |d j| ≤ K) :
    ∀ j ≥ 2, |(Qsel j : ℝ) * xOfSeq d - (Md d j : ℝ)| ≤ 4 * (K : ℝ) / (4 * (j : ℝ) + 2) := by
  intro j hj
  have hx := xOfSeq_tendsto d K hK
  have hdist : ∀ n : ℕ, dist ((Md d n : ℝ) / (Qsel n : ℝ))
      ((Md d (n + 1) : ℝ) / (Qsel (n + 1) : ℝ)) ≤ 2 * (K : ℝ) / (Qsel (n + 1) : ℝ) := by
    intro n
    by_cases hn : 1 ≤ n
    · have h := increments_bound_d d K hK n hn
      rw [Real.dist_eq, abs_sub_comm]
      exact h
    · have hn0 : n = 0 := by omega
      subst hn0
      simp only [Md_zero]
      norm_num
  have hsumm := increments_summable_d d K
  have htail : dist ((Md d j : ℝ) / (Qsel j : ℝ)) (xOfSeq d) ≤
      ∑' m : ℕ, 2 * (K : ℝ) / (Qsel (j + m + 1) : ℝ) := by
    have := dist_le_tsum_of_dist_le_of_tendsto (fun n => 2 * (K : ℝ) / (Qsel (n + 1) : ℝ))
      hdist hsumm hx j
    convert this using 1
  have hQge : ∀ m : ℕ, (2 : ℝ) ^ m * (Qsel (j + 1) : ℝ) ≤ (Qsel (j + m + 1) : ℝ) := by
    intro m
    induction m with
    | zero => norm_num
    | succ n ih =>
      have hdbl : 2 * Qsel (j + n + 1) ≤ Qsel (j + n + 2) := by
        have := Qsel_double_all (j + n)
        convert this using 1
      have hcast : (2 * Qsel (j + n + 1) : ℝ) ≤ (Qsel (j + n + 2) : ℝ) := by exact_mod_cast hdbl
      have hmul : 2 * ((2 : ℝ) ^ n * (Qsel (j + 1) : ℝ)) ≤ 2 * (Qsel (j + n + 1) : ℝ) := by
        exact mul_le_mul_of_nonneg_left ih (by norm_num)
      have hpow : (2 : ℝ) ^ (n + 1) * (Qsel (j + 1) : ℝ) =
          2 * ((2 : ℝ) ^ n * (Qsel (j + 1) : ℝ)) := by ring
      have hidx : (j + (n + 1) + 1 : ℕ) = j + n + 2 := by ring_nf
      rw [hpow, hidx]
      linarith
  have htail' : ∑' m : ℕ, 2 * (K : ℝ) / (Qsel (j + m + 1) : ℝ) ≤
      4 * (K : ℝ) / (Qsel (j + 1) : ℝ) := by
    have hle : ∀ m : ℕ, 2 * (K : ℝ) / (Qsel (j + m + 1) : ℝ) ≤
        2 * (K : ℝ) / (Qsel (j + 1) : ℝ) * (1 / 2 : ℝ) ^ m := by
      intro m
      have hQpos : (0 : ℝ) < (Qsel (j + m + 1) : ℝ) := by
        exact_mod_cast Qsel_pos (j + m + 1) (by omega)
      have hQpos' : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by
        exact_mod_cast Qsel_pos (j + 1) (by omega)
      have hQge' : (2 : ℝ) ^ m * (Qsel (j + 1) : ℝ) ≤ (Qsel (j + m + 1) : ℝ) := hQge m
      calc 2 * (K : ℝ) / (Qsel (j + m + 1) : ℝ)
          ≤ 2 * (K : ℝ) / ((2 : ℝ) ^ m * (Qsel (j + 1) : ℝ)) := by gcongr
        _ = 2 * (K : ℝ) / (Qsel (j + 1) : ℝ) * (1 / 2 : ℝ) ^ m := by
          rw [div_eq_mul_inv, mul_inv, ← inv_pow]
          norm_num
          ring_nf
    have hsumm : Summable (fun m : ℕ => 2 * (K : ℝ) / (Qsel (j + 1) : ℝ) * (1 / 2 : ℝ) ^ m) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hsummL : Summable (fun m : ℕ => 2 * (K : ℝ) / (Qsel (j + m + 1) : ℝ)) :=
      (increments_summable_d d K).comp_injective (fun _ _ h => by simpa using h)
    calc ∑' m : ℕ, 2 * (K : ℝ) / (Qsel (j + m + 1) : ℝ)
        ≤ ∑' m : ℕ, 2 * (K : ℝ) / (Qsel (j + 1) : ℝ) * (1 / 2 : ℝ) ^ m :=
          hsummL.tsum_le_tsum hle hsumm
      _ = 2 * (K : ℝ) / (Qsel (j + 1) : ℝ) * (1 - 1 / 2)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      _ = 4 * (K : ℝ) / (Qsel (j + 1) : ℝ) := by norm_num; ring
  have hQpos : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j (by omega)
  have heq : |(Qsel j : ℝ) * xOfSeq d - (Md d j : ℝ)| =
      (Qsel j : ℝ) * dist ((Md d j : ℝ) / (Qsel j : ℝ)) (xOfSeq d) := by
    have hQne : (Qsel j : ℝ) ≠ 0 := ne_of_gt hQpos
    have hfactor : (Qsel j : ℝ) * xOfSeq d - (Md d j : ℝ) =
        (Qsel j : ℝ) * (xOfSeq d - (Md d j : ℝ) / (Qsel j : ℝ)) := by
      field_simp [hQne]
    rw [hfactor, abs_mul, abs_of_pos hQpos, Real.dist_eq, abs_sub_comm]
  rw [heq]
  have h1 : (Qsel j : ℝ) * dist ((Md d j : ℝ) / (Qsel j : ℝ)) (xOfSeq d) ≤
      (Qsel j : ℝ) * (4 * (K : ℝ) / (Qsel (j + 1) : ℝ)) := by
    gcongr
    exact le_trans htail htail'
  have h2 : (Qsel j : ℝ) * (4 * (K : ℝ) / (Qsel (j + 1) : ℝ)) ≤
      4 * (K : ℝ) / (4 * (j : ℝ) + 2) := by
    have hQrec : (Qsel (j + 1) : ℝ) ≥ (4 * (j : ℝ) + 2) * (Qsel j : ℝ) := by
      have hrec := Qsel_rec j hj
      have hpos : 0 ≤ (Qsel (j - 1) : ℝ) := by
        exact_mod_cast le_of_lt (Qsel_pos (j - 1) (by omega))
      have hcast : (Qsel (j + 1) : ℝ) =
          (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by
        exact_mod_cast hrec
      linarith
    have hQpos' : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
    have hcoef : (0 : ℝ) < 4 * (j : ℝ) + 2 := by positivity
    have hratio : (Qsel j : ℝ) / (Qsel (j + 1) : ℝ) ≤ 1 / (4 * (j : ℝ) + 2) := by
      rw [div_le_div_iff₀ hQpos' hcoef]
      linarith
    calc (Qsel j : ℝ) * (4 * (K : ℝ) / (Qsel (j + 1) : ℝ))
        = 4 * (K : ℝ) * ((Qsel j : ℝ) / (Qsel (j + 1) : ℝ)) := by ring
      _ ≤ 4 * (K : ℝ) * (1 / (4 * (j : ℝ) + 2)) := by gcongr
      _ = 4 * (K : ℝ) / (4 * (j : ℝ) + 2) := by ring
  linarith

/-- 最终最近整数。 -/
lemma eventually_nearest_d (d : ℕ → ℤ) (K : ℕ) (hK : ∀ j ≥ 2, |d j| ≤ K) :
    ∃ N : ℕ, ∀ j ≥ N, Mseq (xOfSeq d) j = Md d j := by
  have hres := residual_bound_d d K hK
  have hsmall : ∃ N : ℕ, ∀ j ≥ N, 4 * (K : ℝ) / (4 * (j : ℝ) + 2) < 1 / 2 := by
    have htend : Tendsto (fun j : ℕ => 4 * (K : ℝ) / (4 * (j : ℝ) + 2)) atTop (nhds 0) := by
      have hden : Tendsto (fun j : ℕ => 4 * (j : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right atTop (2 : ℝ)
          (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
      exact tendsto_const_nhds.div_atTop hden
    have := Metric.tendsto_atTop.mp htend (1 / 2) (by norm_num)
    obtain ⟨N, hN⟩ := this
    use N
    intro j hj
    have h := hN j hj
    have hnn : (0 : ℝ) ≤ 4 * (K : ℝ) / (4 * (j : ℝ) + 2) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h
    exact h
  obtain ⟨N, hN⟩ := hsmall
  use max N 2
  intro j hj
  have hjN : N ≤ j := by omega
  have hj2 : 2 ≤ j := by omega
  have hres' : |(Qsel j : ℝ) * xOfSeq d - (Md d j : ℝ)| < 1 / 2 := by
    calc |(Qsel j : ℝ) * xOfSeq d - (Md d j : ℝ)|
        ≤ 4 * (K : ℝ) / (4 * (j : ℝ) + 2) := hres j hj2
      _ < 1 / 2 := hN j hjN
  have hround : round ((Qsel j : ℝ) * xOfSeq d) = Md d j := by
    apply round_eq_iff.mpr
    constructor
    · linarith [abs_lt.mp hres']
    · linarith [abs_lt.mp hres']
  simp only [Mseq]
  exact hround

/-- 构造的缺陷最终等于 d。 -/
lemma defect_eq_d (d : ℕ → ℤ) (K : ℕ) (hK : ∀ j ≥ 2, |d j| ≤ K) :
    ∃ N : ℕ, ∀ j ≥ N, defect (xOfSeq d) j = d j := by
  obtain ⟨N, hN⟩ := eventually_nearest_d d K hK
  use max (N + 1) 3
  intro j hj
  have hjN : N ≤ j := by omega
  have hj3 : 3 ≤ j := by omega
  have hj2 : 2 ≤ j := by omega
  have hMj : Mseq (xOfSeq d) j = Md d j := hN j hjN
  have hMj1 : Mseq (xOfSeq d) (j + 1) = Md d (j + 1) := hN (j + 1) (by omega)
  have hj1N : N ≤ j - 1 := by omega
  have hMj_1 : Mseq (xOfSeq d) (j - 1) = Md d (j - 1) := hN (j - 1) hj1N
  simp only [defect, hMj, hMj1, hMj_1]
  have hrec := Md_rec d j hj2
  linarith

/-- 构造的 S 有限。 -/
lemma S_finite_d (d : ℕ → ℤ) (K : ℕ) (hK : ∀ j ≥ 2, |d j| ≤ K) :
    S (xOfSeq d) < ∞ := by
  have hres := residual_bound_d d K hK
  have hM := eventually_nearest_d d K hK
  obtain ⟨N, hN⟩ := hM
  have hbound : ∀ j ≥ max N 2, (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * xOfSeq d) ≤ (K : ℝ) := by
    intro j hj
    have hjN : N ≤ j := by omega
    have hj2 : 2 ≤ j := by omega
    have hMj : Mseq (xOfSeq d) j = Md d j := hN j hjN
    have heps : distToNearestInt ((Qsel j : ℝ) * xOfSeq d) =
        |(Qsel j : ℝ) * xOfSeq d - (Md d j : ℝ)| := by
      simp only [distToNearestInt]
      rw [show round ((Qsel j : ℝ) * xOfSeq d) = Md d j by simpa [Mseq] using hMj]
    rw [heps]
    have hres' : |(Qsel j : ℝ) * xOfSeq d - (Md d j : ℝ)| ≤ 4 * (K : ℝ) / (4 * (j : ℝ) + 2) :=
      hres j hj2
    have hjpos : (0 : ℝ) < (j : ℝ) := by
      have : (0 : ℕ) < j := by omega
      exact_mod_cast this
    calc (j : ℝ) * |(Qsel j : ℝ) * xOfSeq d - (Md d j : ℝ)|
        ≤ (j : ℝ) * (4 * (K : ℝ) / (4 * (j : ℝ) + 2)) := by gcongr
      _ = 4 * (K : ℝ) * (j : ℝ) / (4 * (j : ℝ) + 2) := by ring
      _ ≤ (K : ℝ) := by
        have hden : (0 : ℝ) < 4 * (j : ℝ) + 2 := by positivity
        rw [div_le_iff₀ hden]
        have : (4 : ℝ) * (j : ℝ) ≤ 4 * (j : ℝ) + 2 := by linarith
        nlinarith
  have hS : S (xOfSeq d) ≤ ENNReal.ofReal (K : ℝ) := by
    simp only [S]
    apply le_trans (iInf_le (fun N' => ⨆ j : {j : ℕ // N' ≤ j},
      ENNReal.ofReal ((j : ℝ) * distToNearestInt ((Qsel j : ℝ) * xOfSeq d))) (max N 2))
    apply iSup_le
    intro ⟨j, hj⟩
    exact ENNReal.ofReal_le_ofReal (hbound j hj)
  exact lt_of_le_of_lt hS ENNReal.ofReal_lt_top

/-- **Theorem 8**：任意有界整数序列可实现为某 S 有限实数的最终符号缺陷序列。 -/
theorem theorem8_realization (d : ℕ → ℤ) (K : ℕ) (hK : ∀ j ≥ 2, |d j| ≤ K) :
    ∃ x : ℝ, S x < ∞ ∧ ∃ N : ℕ, ∀ j ≥ N, defect x j = d j := by
  use xOfSeq d
  constructor
  · exact S_finite_d d K hK
  · exact defect_eq_d d K hK

/-! ## 公理审计 -/

#print axioms defect_identity
#print axioms tracking
#print axioms integer_gap
#print axioms stabilizes
#print axioms theorem7_cluster_set
#print axioms theorem7_finite
#print axioms theorem7_nonempty
#print axioms W_rec_d
#print axioms W_bound_d
#print axioms increments_summable_d
#print axioms ratio_converges_d
#print axioms residual_bound_d
#print axioms eventually_nearest_d
#print axioms defect_eq_d
#print axioms S_finite_d
#print axioms theorem8_realization

end SignedClusters