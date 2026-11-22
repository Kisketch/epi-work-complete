import Mathlib
import EpiFormal.Measure
import EpiFormal.Meiburg

/-!
# F2 收敛层：圆周间距 → 二进块计数 → 几何求和 → Meiburg 判据定理

依据参考证明（Epi_F1_F4.pdf §9.5，Lemma 9.11–9.14）：
1. distToNearestInt 与圆周间距引理（μ(π)<s ⇒ ‖h/π‖≥c·h^(1−s)）；
2. 二进块计数（N≤n<2N 内 ‖n/π‖≤t 的点数 ≤2⌊t/δ⌋）；
3. Jordan 不等式 |sin n|≥2‖n/π‖ + 块和 ≤C_s·N^(2s−5)；
4. N=2^k 几何级数收敛（2s−5<0）⇒ FlintHillsConjecture；
5. 接线 meiburg_criterion 为定理。

关键：用统一正数处理所有有限例外；最近整数为零单独处理。
-/

open Real Set Filter Int

/-- 到最近整数的距离 ‖x‖ = min_{j∈ℤ}|x−j|，用 round 实现。 -/
noncomputable def distToNearestInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

/-- round 给出最小距离：‖x‖≤|x−j| 对任意整数 j。 -/
lemma distToNearestInt_le (x : ℝ) (j : ℤ) : distToNearestInt x ≤ |x - (j : ℝ)| := by
  unfold distToNearestInt
  exact round_le x j

/-- ‖x‖≤1/2。 -/
lemma distToNearestInt_le_half (x : ℝ) : distToNearestInt x ≤ 1 / 2 := by
  unfold distToNearestInt
  exact abs_sub_round x

/-- ‖x‖≥0。 -/
lemma distToNearestInt_nonneg (x : ℝ) : 0 ≤ distToNearestInt x := abs_nonneg _

/-- 周期性：‖x+1‖=‖x‖（round(x+1)=round(x)+1）。 -/
lemma distToNearestInt_add_one (x : ℝ) : distToNearestInt (x + 1) = distToNearestInt x := by
  unfold distToNearestInt
  have hr : round (x + 1) = round x + 1 := round_add_one x
  rw [hr]
  push_cast
  ring_nf

/-- 统一常数下界：若 μ(π)≤M 且 M<s，则存在 C>0，使对所有整数 a 与正整数 b，
    |π−a/b| ≥ C·b^(−s)。
    证明：A(π,s) 有限（μ 定义），例外集 E 上 bˢ|π−a/b|>0（π 无理），取有限正最小值与 1 的 min。
    非例外对天然 |π−a/b|≥b^(−s)≥C·b^(−s)（C≤1）。 -/
lemma uniform_approx_bound {M : NNReal} {s : ℝ}
    (hM : irrMeasure π ≤ (M : ENNReal)) (hMs : (M : ℝ) < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℤ) (b : ℕ), 0 < b →
      |π - (a : ℝ) / (b : ℝ)| ≥ C * (b : ℝ) ^ (-s) := by
  have hs_pos : 0 < s := by linarith [NNReal.coe_nonneg M]
  have hfin : (apprPairs π s).Finite := apprPairs_finite_of_mu_lt hM hMs
  -- 例外集 E = A(π,s)（有限）。对 E 中元素 bˢ|π−a/b|>0；取这些正值与 1 的最小值。
  -- 构造有限集 {bˢ|π−a/b| : (a,b)∈E} ∪ {1}
  let f : ℤ × ℕ → ℝ := fun pq => (pq.2 : ℝ) ^ s * |π - (pq.1 : ℝ) / (pq.2 : ℝ)|
  let E : Finset (ℤ × ℕ) := hfin.toFinset
  let vals : Finset ℝ := E.image f ∪ {1}
  have hvals_ne : vals.Nonempty := ⟨1, by simp [vals]⟩
  set C := vals.min' hvals_ne with hCdef
  have hC_mem : C ∈ vals := Finset.min'_mem vals hvals_ne
  have hC_pos : 0 < C := by
    simp only [vals, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hC_mem
    rcases hC_mem with ⟨pq, hpq, hCeq⟩ | hCeq
    · have hpq' : pq ∈ apprPairs π s := by
        simpa [E] using hpq
      have hb : 0 < pq.2 := hpq'.1
      have hbR : 0 < (pq.2 : ℝ) := by exact_mod_cast hb
      have hpos : 0 < |π - (pq.1 : ℝ) / (pq.2 : ℝ)| := by
        apply abs_pos.mpr
        intro h
        have hpi : π = (pq.1 : ℝ) / (pq.2 : ℝ) := by linarith
        exact pi_irrational ⟨pq.1 / pq.2, by push_cast; exact hpi.symm⟩
      have hfpos : 0 < f pq := mul_pos (Real.rpow_pos_of_pos hbR s) hpos
      linarith
    · have : C = 1 := by linarith
      linarith
  have hC_le_one : C ≤ 1 := by
    apply Finset.min'_le
    simp [vals]
  refine ⟨C, hC_pos, ?_⟩
  intro a b hb
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  by_cases hex : (a, b) ∈ apprPairs π s
  · -- 例外对：bˢ|π−a/b| ∈ vals，故 ≥ C
    have hmem : f (a, b) ∈ vals := by
      simp only [vals, Finset.mem_union, Finset.mem_image]
      left
      exact ⟨(a, b), by simpa [E] using hex, rfl⟩
    have hge : C ≤ f (a, b) := Finset.min'_le vals (f (a, b)) hmem
    -- f(a,b) = bˢ|π−a/b| ≥ C ⇒ |π−a/b| ≥ C·b^(−s)
    have hf : f (a, b) = (b : ℝ) ^ s * |π - (a : ℝ) / (b : ℝ)| := rfl
    rw [hf] at hge
    have : |π - (a : ℝ) / (b : ℝ)| ≥ C * (b : ℝ) ^ (-s) := by
      have hbs : (b : ℝ) ^ s > 0 := Real.rpow_pos_of_pos hbR s
      calc |π - (a : ℝ) / (b : ℝ)| = (b : ℝ) ^ (-s) * ((b : ℝ) ^ s * |π - (a : ℝ) / (b : ℝ)|) := by
            rw [← mul_assoc, ← Real.rpow_add hbR, neg_add_cancel, Real.rpow_zero, one_mul]
        _ ≥ (b : ℝ) ^ (-s) * C := by gcongr
        _ = C * (b : ℝ) ^ (-s) := by ring
    exact this
  · -- 非例外对：|π−a/b| ≥ b^(−s) ≥ C·b^(−s)
    have hge : |π - (a : ℝ) / (b : ℝ)| ≥ (b : ℝ) ^ (-s) := by
      simp only [apprPairs, Set.mem_setOf_eq] at hex
      push Not at hex
      exact hex hb
    calc |π - (a : ℝ) / (b : ℝ)| ≥ (b : ℝ) ^ (-s) := hge
      _ ≥ C * (b : ℝ) ^ (-s) := by
        have hbs : 0 ≤ (b : ℝ) ^ (-s) := le_of_lt (Real.rpow_pos_of_pos hbR (-s))
        nlinarith

/-- 圆周间距引理（Lemma 9.11）：若 μ(π)≤M<s<5/2 且 s>1，则存在 c>0，
    使每个正整数 h 满足 ‖h/π‖ ≥ c·h^(1−s)。
    证明：取统一常数 C（uniform_approx_bound）。j=round(h/π)。
    j≥1：‖h/π‖=(j/π)|π−h/j|≥(C/π)j^(1−s)≥(C/π)h^(1−s)（j≤h, 1−s<0）。
    j=0：‖h/π‖=h/π≥h^(1−s)/π。取 c=min(C,1)/π。 -/
lemma circle_spacing {M : NNReal} {s : ℝ}
    (hM : irrMeasure π ≤ (M : ENNReal)) (hMs : (M : ℝ) < s) (hs1 : 1 < s) :
    ∃ c : ℝ, 0 < c ∧ ∀ h : ℕ, 0 < h →
      distToNearestInt ((h : ℝ) / π) ≥ c * (h : ℝ) ^ (1 - s) := by
  obtain ⟨C, hC_pos, hC⟩ := uniform_approx_bound hM hMs
  set c := min C 1 / π with hcdef
  have hc_pos : 0 < c := by
    apply div_pos (lt_min hC_pos zero_lt_one) pi_pos
  refine ⟨c, hc_pos, ?_⟩
  intro h hh
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have h1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hh)
  set j := round ((h : ℝ) / π) with hjdef
  have hj_min : distToNearestInt ((h : ℝ) / π) = |(h : ℝ) / π - (j : ℝ)| := rfl
  rw [hj_min]
  have hpow_nonneg : 0 ≤ (h : ℝ) ^ (1 - s) := le_of_lt (Real.rpow_pos_of_pos hhR (1 - s))
  have hpow_le_one : (h : ℝ) ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  have hc_le_invpi : c ≤ 1 / π := by
    rw [hcdef]; apply (div_le_div_iff_of_pos_right pi_pos).mpr; exact min_le_right C 1
  have hc_le_Cpi : c ≤ C / π := by
    rw [hcdef]; apply (div_le_div_iff_of_pos_right pi_pos).mpr; exact min_le_left C 1
  by_cases hj0 : j = 0
  · -- j=0：‖h/π‖=h/π
    have hjR : (j : ℝ) = 0 := by exact_mod_cast hj0
    rw [hjR, sub_zero, abs_of_nonneg (by positivity : 0 ≤ (h : ℝ) / π)]
    calc (h : ℝ) / π ≥ 1 / π := by gcongr
      _ ≥ (h : ℝ) ^ (1 - s) / π := by gcongr
      _ = (1 / π) * (h : ℝ) ^ (1 - s) := by ring
      _ ≥ c * (h : ℝ) ^ (1 - s) := by gcongr
  · -- j≥1
    have hj_nonneg : 0 ≤ j := by
      have hround : round ((h : ℝ) / π) = ⌊(h : ℝ) / π + 1 / 2⌋ := round_eq _
      have : 0 ≤ ⌊(h : ℝ) / π + 1 / 2⌋ := by
        apply Int.floor_nonneg.mpr
        positivity
      linarith [hround, hjdef]
    have hj_pos : 0 < j := by
      contrapose! hj0
      linarith
    have hjR_pos : 0 < (j : ℝ) := by exact_mod_cast hj_pos
    have hbound := hC (h : ℤ) j.natAbs (Int.natAbs_pos.mpr (ne_of_gt hj_pos))
    have hjnatZ : (j.natAbs : ℤ) = j := by
      exact Int.natAbs_of_nonneg hj_nonneg
    have hjnatR : (j.natAbs : ℝ) = (j : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hjnatZ
      simpa using this
    have hbound' : |π - (h : ℝ) / (j : ℝ)| ≥ C * (j : ℝ) ^ (-s) := by
      simpa [hjnatR, div_eq_mul_inv] using hbound
    have heq : |(h : ℝ) / π - (j : ℝ)| = ((j : ℝ) / π) * |π - (h : ℝ) / (j : ℝ)| := by
      have hinner : (h : ℝ) / π - (j : ℝ) = ((j : ℝ) / π) * ((h : ℝ) / (j : ℝ) - π) := by
        field_simp
      rw [hinner, abs_mul, abs_of_pos (div_pos hjR_pos pi_pos), abs_sub_comm]
    rw [heq]
    have hsimplify : ((j : ℝ) / π) * (C * (j : ℝ) ^ (-s)) = (C / π) * (j : ℝ) ^ (1 - s) := by
      have hp : (j : ℝ) * (j : ℝ) ^ (-s) = (j : ℝ) ^ (1 - s) := by
        rw [show (1 - s : ℝ) = 1 + (-s) by ring, Real.rpow_add hjR_pos, Real.rpow_one]
      calc ((j : ℝ) / π) * (C * (j : ℝ) ^ (-s))
          = (C / π) * ((j : ℝ) * (j : ℝ) ^ (-s)) := by ring
        _ = (C / π) * (j : ℝ) ^ (1 - s) := by rw [hp]
    have hj_le_h : (j : ℝ) ≤ (h : ℝ) := by
      have hj_le : (j : ℝ) ≤ (h : ℝ) / π + 1 / 2 := round_le_add_half _
      have hpi_gt2 : (2 : ℝ) < π := by linarith [Real.pi_gt_three]
      have hmid : (h : ℝ) / π + 1 / 2 ≤ (h : ℝ) := by
        have h1pi : 0 < 1 - 1 / π := by
          have : (1 : ℝ) / π < 1 := by
            rw [div_lt_one pi_pos]; linarith [Real.pi_gt_three]
          linarith
        have hkey : (h : ℝ) - ((h : ℝ) / π + 1 / 2) = (h : ℝ) * (1 - 1 / π) - 1 / 2 := by
          ring
        have hnonneg : 0 ≤ (h : ℝ) * (1 - 1 / π) - 1 / 2 := by
          have : (h : ℝ) * (1 - 1 / π) ≥ 1 - 1 / π := by
            nlinarith [h1]
          have : 1 - 1 / π ≥ 1 / 2 := by
            have hpi2 : (2 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
            have : (1 : ℝ) / π ≤ 1 / 2 := by
              apply one_div_le_one_div_of_le (by positivity) hpi2
            linarith
          nlinarith
        linarith [hkey]
      linarith
    have hpow_mono : (h : ℝ) ^ (1 - s) ≤ (j : ℝ) ^ (1 - s) :=
      Real.rpow_le_rpow_of_nonpos hjR_pos hj_le_h (by linarith)
    calc ((j : ℝ) / π) * |π - (h : ℝ) / (j : ℝ)|
        ≥ ((j : ℝ) / π) * (C * (j : ℝ) ^ (-s)) := by gcongr
      _ = (C / π) * (j : ℝ) ^ (1 - s) := hsimplify
      _ ≥ (C / π) * (h : ℝ) ^ (1 - s) := by gcongr
      _ ≥ c * (h : ℝ) ^ (1 - s) := by gcongr

/-- 取负不变性：‖−x‖=‖x‖（最近整数距离对称，用双向最小性）。 -/
lemma distToNearestInt_neg (x : ℝ) : distToNearestInt (-x) = distToNearestInt x := by
  apply le_antisymm
  · -- ‖−x‖ ≤ |−x − (−round x)| = |x − round x| = ‖x‖
    have := distToNearestInt_le (-x) (-round x)
    have heq : |(-x) - ((-round x : ℤ) : ℝ)| = distToNearestInt x := by
      unfold distToNearestInt
      have hinner : (-x) - ((-round x : ℤ) : ℝ) = -(x - (round x : ℝ)) := by
        push_cast; ring
      rw [hinner, abs_neg]
    linarith
  · -- ‖x‖ ≤ |x − (−round(−x))| = |−x − round(−x)| = ‖−x‖
    have := distToNearestInt_le x (-round (-x))
    have heq : |x - ((-round (-x) : ℤ) : ℝ)| = distToNearestInt (-x) := by
      unfold distToNearestInt
      have hinner : x - ((-round (-x) : ℤ) : ℝ) = -((-x) - (round (-x) : ℝ)) := by
        push_cast; ring
      rw [hinner, abs_neg]
    linarith

/-- 块内单点下界：若 ‖h/π‖≥c·h^(1−s) 对所有 h>0，且 1−s<0，
    则对 N≤n<2N（N≥1），‖n/π‖≥c·(2N)^(1−s)。
    证明：n<2N 且 1−s<0 ⇒ n^(1−s)≥(2N)^(1−s)。 -/
lemma block_point_lower {c s : ℝ} (hc : 0 < c) (hs1 : 1 < s)
    (hspacing : ∀ h : ℕ, 0 < h → distToNearestInt ((h : ℝ) / π) ≥ c * (h : ℝ) ^ (1 - s))
    (N n : ℕ) (hn0 : 0 < n) (hn2N : n < 2 * N) :
    distToNearestInt ((n : ℝ) / π) ≥ c * (2 * N : ℝ) ^ (1 - s) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hn2NR : (n : ℝ) < (2 * N : ℝ) := by exact_mod_cast hn2N
  have hpow : (n : ℝ) ^ (1 - s) ≥ (2 * N : ℝ) ^ (1 - s) :=
    Real.rpow_le_rpow_of_nonpos hnR (le_of_lt hn2NR) (by linarith)
  calc distToNearestInt ((n : ℝ) / π) ≥ c * (n : ℝ) ^ (1 - s) := hspacing n hn0
    _ ≥ c * (2 * N : ℝ) ^ (1 - s) := by gcongr

/-- 块内两点圆周距下界：对 N≤n,m<2N，n≠m，‖(n−m)/π‖≥c·(2N)^(1−s)。
    证明：1≤|n−m|<2N，用 block_point_lower 于 |n−m|（注意 ‖(n−m)/π‖=‖|n−m|/π‖）。 -/
lemma block_pair_spacing {c s : ℝ} (hc : 0 < c) (hs1 : 1 < s)
    (hspacing : ∀ h : ℕ, 0 < h → distToNearestInt ((h : ℝ) / π) ≥ c * (h : ℝ) ^ (1 - s))
    (N n m : ℕ) (hN : 1 ≤ N) (hnN : N ≤ n) (hn2N : n < 2 * N)
    (hmN : N ≤ m) (hm2N : m < 2 * N) (hne : n ≠ m) :
    distToNearestInt (((n : ℝ) - (m : ℝ)) / π) ≥ c * (2 * N : ℝ) ^ (1 - s) := by
  -- d = max n m − min n m 是正整数，<2N，且 (d:ℝ)=|n−m|
  set d := max n m - min n m with hddef
  have hd0 : 0 < d := by
    simp only [hddef]
    have : min n m < max n m := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp [min_eq_left_of_lt hlt, max_eq_right_of_lt hlt, hlt]
      · simp [min_eq_right_of_lt hgt, max_eq_left_of_lt hgt, hgt]
    omega
  have hd2N : d < 2 * N := by
    simp only [hddef]
    have : max n m < 2 * N := by
      simp [max_lt, hn2N, hm2N]
    have : min n m ≥ 0 := by positivity
    omega
  have hdN : 1 ≤ d := by omega
  have hd_cast : (d : ℝ) = |(n : ℝ) - (m : ℝ)| := by
    simp only [hddef]
    rcases le_total n m with hnm | hnm
    · have hmin : min n m = n := min_eq_left hnm
      have hmax : max n m = m := max_eq_right hnm
      rw [hmin, hmax, Nat.cast_sub hnm]
      rw [abs_of_nonpos (by
        have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
        linarith)]
      ring
    · have hmin : min n m = m := min_eq_right hnm
      have hmax : max n m = n := max_eq_left hnm
      rw [hmin, hmax, Nat.cast_sub hnm]
      rw [abs_of_nonneg (by
        have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
        linarith)]
  have heq : distToNearestInt (((n : ℝ) - (m : ℝ)) / π) =
      distToNearestInt ((d : ℝ) / π) := by
    rw [hd_cast]
    have hdiv : |(n : ℝ) - (m : ℝ)| / π = |((n : ℝ) - (m : ℝ)) / π| := by
      rw [abs_div, abs_of_pos pi_pos]
    rw [hdiv]
    rcases lt_or_ge 0 (((n : ℝ) - (m : ℝ)) / π) with hy | hy
    · rw [abs_of_pos hy]
    · rw [abs_of_nonpos hy, distToNearestInt_neg]
  rw [heq]
  exact block_point_lower hc hs1 hspacing N d hd0 hd2N

/-- sin 整数倍 π 平移绝对值不变：|sin(x + mπ)| = |sin x|（m:ℤ）。 -/
lemma abs_sin_add_int_mul_pi (x : ℝ) (m : ℤ) : |sin (x + (m : ℝ) * π)| = |sin x| := by
  have h := Real.sin_add_int_mul_pi x m
  rw [h]
  simp [abs_mul, abs_zpow]

/-- Jordan 不等式（Lemma 9.13 核心）：|sin n| ≥ 2·‖n/π‖。
    证明：n = π·(n/π)；设 j=round(n/π)，y=n/π−j，|y|=‖n/π‖≤1/2。
    sin n = sin(πy + jπ)，绝对值 = |sin(πy)|；|πy|≤π/2，Jordan 给 |sin(πy)|≥(2/π)|πy|=2|y|。 -/
lemma sin_ge_two_distToNearestInt (n : ℕ) :
    |sin (n : ℝ)| ≥ 2 * distToNearestInt ((n : ℝ) / π) := by
  set j := round ((n : ℝ) / π) with hjdef
  set y := (n : ℝ) / π - (j : ℝ) with hydef
  have hy_abs : |y| = distToNearestInt ((n : ℝ) / π) := rfl
  have hy_le : |y| ≤ 1 / 2 := by
    rw [hy_abs]; exact distToNearestInt_le_half _
  -- n = π·y + j·π
  have hn_decomp : (n : ℝ) = π * y + (j : ℝ) * π := by
    simp only [hydef]
    field_simp
    ring
  -- |sin n| = |sin(πy)|
  have hsin_eq : |sin (n : ℝ)| = |sin (π * y)| := by
    rw [hn_decomp]
    exact abs_sin_add_int_mul_pi (π * y) j
  rw [hsin_eq, ← hy_abs]
  -- Jordan：|πy|≤π/2 ⇒ |sin(πy)|≥(2/π)|πy|
  have hπy_le : |π * y| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos pi_pos]
    have : π * |y| ≤ π * (1 / 2) := by gcongr
    linarith
  have hjordan := Real.mul_abs_le_abs_sin hπy_le
  -- (2/π)|πy| = 2|y|
  have hsimplify : (2 / π) * |π * y| = 2 * |y| := by
    rw [abs_mul, abs_of_pos pi_pos]
    field_simp
  linarith

/-- 单侧 packing 计数（floor 单射法）：有限集 S⊂ℝ，元素均≥δ>0，两两距≥δ，
    则 S 中 ≤t 的元素个数 ≤ ⌊t/δ⌋₊ + 1。
    证明：x↦⌊x/δ⌋₊ 是单射（同值则同长度 δ 区间，距<δ 矛盾）；
    像含于 [0, ⌊t/δ⌋₊]，基数 ⌊t/δ⌋₊+1。 -/
lemma packing_count {δ t : ℝ} (hδ : 0 < δ) (S : Finset ℝ)
    (hlower : ∀ x ∈ S, δ ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (S.filter (fun x => x ≤ t)).card ≤ Nat.floor (t / δ) + 1 := by
  set T := S.filter (fun x => x ≤ t) with hTdef
  -- 映射 f(x) = ⌊x/δ⌋₊
  let f : ℝ → ℕ := fun x => Nat.floor (x / δ)
  -- f 在 T 上单射
  have hinj : Set.InjOn f (T : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hxT : x ∈ T := hx
    have hyT : y ∈ T := hy
    have hxS : x ∈ S := (Finset.mem_filter.mp hxT).1
    have hyS : y ∈ S := (Finset.mem_filter.mp hyT).1
    have hsep' : δ ≤ |x - y| := hsep x hxS y hyS hne
    -- f x = f y ⇒ ⌊x/δ⌋=⌊y/δ⌋ ⇒ |x/δ−y/δ|<1 ⇒ |x−y|<δ
    have hfloor : Nat.floor (x / δ) = Nat.floor (y / δ) := hxy
    have hxδ : 0 ≤ x / δ := by
      apply div_nonneg (by linarith [hlower x hxS]) (le_of_lt hδ)
    have hyδ : 0 ≤ y / δ := by
      apply div_nonneg (by linarith [hlower y hyS]) (le_of_lt hδ)
    have hlt : |x / δ - y / δ| < 1 := by
      have hx' : (Nat.floor (x / δ) : ℝ) ≤ x / δ := Nat.floor_le hxδ
      have hx'' : x / δ < (Nat.floor (x / δ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have hy' : (Nat.floor (y / δ) : ℝ) ≤ y / δ := Nat.floor_le hyδ
      have hy'' : y / δ < (Nat.floor (y / δ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hfloor] at *
      rw [abs_lt]
      constructor <;> linarith
    have hlt' : |x - y| < δ := by
      have : |x / δ - y / δ| = |x - y| / δ := by
        rw [← sub_div, abs_div, abs_of_pos hδ]
      rw [this] at hlt
      rw [div_lt_iff₀ hδ] at hlt
      simpa using hlt
    linarith
  -- 像含于 Icc 0 ⌊t/δ⌋
  have himage : T.image f ⊆ Finset.Icc 0 (Nat.floor (t / δ)) := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_Icc] at hn ⊢
    obtain ⟨x, hx, rfl⟩ := hn
    have hxT : x ∈ T := hx
    have hxle : x ≤ t := (Finset.mem_filter.mp hxT).2
    have hxS : x ∈ S := (Finset.mem_filter.mp hxT).1
    have hxδ : 0 ≤ x / δ := by
      apply div_nonneg (by linarith [hlower x hxS]) (le_of_lt hδ)
    constructor
    · exact Nat.zero_le _
    · apply Nat.floor_mono
      apply (div_le_div_iff_of_pos_right hδ).mpr
      exact hxle
  -- card T = card (image f) ≤ card (Icc 0 ⌊t/δ⌋) = ⌊t/δ⌋+1
  have hcard : T.card = (T.image f).card := by
    rw [Finset.card_image_of_injOn hinj]
  have hle : (T.image f).card ≤ (Finset.Icc 0 (Nat.floor (t / δ))).card :=
    Finset.card_le_card himage
  have hIcc : (Finset.Icc 0 (Nat.floor (t / δ))).card = Nat.floor (t / δ) + 1 := by
    simp
  linarith

/-- 代表元单射：y(n)=n/π−round(n/π) 在整数上单射（π 无理）。
    y(n)=y(m) ⇒ (n−m)/π∈ℤ ⇒ n−m=kπ ⇒ k=0（π 无理）⇒ n=m。 -/
lemma rep_injective : Function.Injective
    (fun n : ℕ => (n : ℝ) / π - (round ((n : ℝ) / π) : ℝ)) := by
  intro n m hnm
  have heq : ((n : ℝ) - (m : ℝ)) / π =
      ((round ((n : ℝ) / π) - round ((m : ℝ) / π) : ℤ) : ℝ) := by
    have h1 : (n : ℝ) / π - (m : ℝ) / π =
        (round ((n : ℝ) / π) : ℝ) - (round ((m : ℝ) / π) : ℝ) := by linarith
    have h2 : (n : ℝ) / π - (m : ℝ) / π = ((n : ℝ) - (m : ℝ)) / π := by ring
    have h3 : (round ((n : ℝ) / π) : ℝ) - (round ((m : ℝ) / π) : ℝ) =
        ((round ((n : ℝ) / π) - round ((m : ℝ) / π) : ℤ) : ℝ) := by push_cast; ring
    linarith
  set k := round ((n : ℝ) / π) - round ((m : ℝ) / π) with hkdef
  have hπ : (n : ℝ) - (m : ℝ) = (k : ℝ) * π := by
    have := heq
    field_simp at this
    linarith
  by_cases hk0 : k = 0
  · have : (n : ℝ) = (m : ℝ) := by
      rw [hk0] at hπ
      simp at hπ
      linarith
    exact_mod_cast this
  · -- k≠0 ⇒ π=(n−m)/k 有理，矛盾
    have hrat : π = ((n : ℝ) - (m : ℝ)) / (k : ℝ) := by
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
      field_simp at hπ ⊢
      linarith
    have : Irrational π := pi_irrational
    have hq : π = (((n : ℤ) - (m : ℤ)) / (k : ℤ) : ℚ) := by
      push_cast
      exact hrat
    exact absurd ⟨((n : ℤ) - (m : ℤ)) / k, hq.symm⟩ this

/-- 二进块计数（Lemma 9.12）：设 spacing 常数 c>0, s>1，δ=c(2N)^(1−s)。
    对 N≥1，块 {N≤n<2N} 中满足 ‖n/π‖≤t（t≤1/2）的 n 个数 ≤ 2(⌊t/δ⌋+1)。
    证明：代表元 yₙ=n/π−round(n/π)∈[−1/2,1/2]，‖n/π‖=|yₙ|。
    正侧 yₙ>0 与负侧 −yₙ>0 各用 packing_count（离零≥δ，两两距≥δ）。 -/
lemma dyadic_block_count {c s : ℝ} (hc : 0 < c) (hs1 : 1 < s)
    (hspacing : ∀ h : ℕ, 0 < h → distToNearestInt ((h : ℝ) / π) ≥ c * (h : ℝ) ^ (1 - s))
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ≤ 1 / 2) :
    ((Finset.Ico N (2 * N)).filter
      (fun (n : ℕ) => distToNearestInt ((n : ℝ) / π) ≤ t)).card ≤
      2 * (Nat.floor (t / (c * (2 * N : ℝ) ^ (1 - s))) + 1) := by
  set δ := c * (2 * N : ℝ) ^ (1 - s) with hδdef
  have hδ : 0 < δ := by
    apply mul_pos hc (Real.rpow_pos_of_pos (by positivity) (1 - s))
  have hpoint : ∀ n ∈ Finset.Ico N (2 * N), δ ≤ distToNearestInt ((n : ℝ) / π) := by
    intro n hn
    have hn2N : n < 2 * N := (Finset.mem_Ico.mp hn).2
    exact block_point_lower hc hs1 hspacing N n (by
      have : N ≤ n := (Finset.mem_Ico.mp hn).1
      omega) hn2N
  let y : ℕ → ℝ := fun n => (n : ℝ) / π - (round ((n : ℝ) / π) : ℝ)
  have hy_abs : ∀ n, |y n| = distToNearestInt ((n : ℝ) / π) := fun n => rfl
  have hsep_y : ∀ n ∈ Finset.Ico N (2 * N), ∀ m ∈ Finset.Ico N (2 * N),
      n ≠ m → δ ≤ |y n - y m| := by
    intro n hn m hm hne
    have hnN : N ≤ n := (Finset.mem_Ico.mp hn).1
    have hn2N : n < 2 * N := (Finset.mem_Ico.mp hn).2
    have hmN : N ≤ m := (Finset.mem_Ico.mp hm).1
    have hm2N : m < 2 * N := (Finset.mem_Ico.mp hm).2
    have hdiff : distToNearestInt (((n : ℝ) - (m : ℝ)) / π) ≤ |y n - y m| := by
      have heq : y n - y m = ((n : ℝ) - (m : ℝ)) / π -
          ((round ((n : ℝ) / π) - round ((m : ℝ) / π) : ℤ) : ℝ) := by
        simp only [y]; push_cast; ring
      rw [heq]
      exact distToNearestInt_le _ _
    have hpair := block_pair_spacing hc hs1 hspacing N n m hN hnN hn2N hmN hm2N hne
    linarith
  let block := Finset.Ico N (2 * N)
  let good := block.filter (fun (n : ℕ) => distToNearestInt ((n : ℝ) / π) ≤ t)
  let pos := good.filter (fun (n : ℕ) => 0 < y n)
  let neg := good.filter (fun (n : ℕ) => y n < 0)
  have hsplit : good.card = pos.card + neg.card := by
    have hunion : good = pos ∪ neg := by
      ext n
      simp only [pos, neg, good, Finset.mem_filter, Finset.mem_union]
      constructor
      · intro hn
        have hδle : δ ≤ distToNearestInt ((n : ℝ) / π) := hpoint n hn.1
        have hy0 : y n ≠ 0 := by
          intro h
          have : distToNearestInt ((n : ℝ) / π) = 0 := by rw [← hy_abs, h]; simp
          linarith
        rcases lt_or_gt_of_ne hy0 with hlt | hgt
        · right; exact ⟨hn, hlt⟩
        · left; exact ⟨hn, hgt⟩
      · intro hn
        rcases hn with ⟨hn, _⟩ | ⟨hn, _⟩ <;> exact hn
    have hdisj : Disjoint pos neg := by
      simp only [pos, neg, Finset.disjoint_left, Finset.mem_filter]
      intro n hn hneg
      linarith [hn.2, hneg.2]
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hpos_count : pos.card ≤ Nat.floor (t / δ) + 1 := by
    let Spos := pos.image y
    have hcard : pos.card = Spos.card := by
      symm; apply Finset.card_image_of_injective; exact rep_injective
    have hlower : ∀ x ∈ Spos, δ ≤ x := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      have hn' : n ∈ good := (Finset.mem_filter.mp hn).1
      have hypos : 0 < y n := (Finset.mem_filter.mp hn).2
      have : δ ≤ distToNearestInt ((n : ℝ) / π) := hpoint n (Finset.mem_filter.mp hn').1
      rw [← hy_abs, abs_of_pos hypos] at this
      exact this
    have hsep : ∀ x ∈ Spos, ∀ z ∈ Spos, x ≠ z → δ ≤ |x - z| := by
      intro x hx z hz hxz
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
      have hne : n ≠ m := by intro h; apply hxz; simp [h]
      have hnblock : n ∈ block := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      have hmblock : m ∈ block := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
      exact hsep_y n hnblock m hmblock hne
    have hupper : ∀ x ∈ Spos, x ≤ t := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      have hn' : n ∈ good := (Finset.mem_filter.mp hn).1
      have hle : distToNearestInt ((n : ℝ) / π) ≤ t := (Finset.mem_filter.mp hn').2
      have hypos : 0 < y n := (Finset.mem_filter.mp hn).2
      rw [← hy_abs, abs_of_pos hypos] at hle
      exact hle
    have hfilter : Spos.filter (fun x => x ≤ t) = Spos :=
      Finset.filter_true_of_mem hupper
    have := packing_count (t := t) hδ Spos hlower hsep
    rw [hfilter] at this
    linarith
  have hneg_count : neg.card ≤ Nat.floor (t / δ) + 1 := by
    let Sneg := neg.image (fun n => -y n)
    have hcard : neg.card = Sneg.card := by
      symm; apply Finset.card_image_of_injective
      intro n m hnm
      have : y n = y m := by linarith
      exact rep_injective this
    have hlower : ∀ x ∈ Sneg, δ ≤ x := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      have hn' : n ∈ good := (Finset.mem_filter.mp hn).1
      have hyneg : y n < 0 := (Finset.mem_filter.mp hn).2
      have : δ ≤ distToNearestInt ((n : ℝ) / π) := hpoint n (Finset.mem_filter.mp hn').1
      rw [← hy_abs, abs_of_neg hyneg] at this
      linarith
    have hsep : ∀ x ∈ Sneg, ∀ z ∈ Sneg, x ≠ z → δ ≤ |x - z| := by
      intro x hx z hz hxz
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
      have hne : n ≠ m := by intro h; apply hxz; simp [h]
      have hnblock : n ∈ block := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      have hmblock : m ∈ block := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
      have := hsep_y n hnblock m hmblock hne
      have : |(-y n) - (-y m)| = |y n - y m| := by rw [← abs_neg]; congr 1; ring
      linarith
    have hupper : ∀ x ∈ Sneg, x ≤ t := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      have hn' : n ∈ good := (Finset.mem_filter.mp hn).1
      have hle : distToNearestInt ((n : ℝ) / π) ≤ t := (Finset.mem_filter.mp hn').2
      have hyneg : y n < 0 := (Finset.mem_filter.mp hn).2
      rw [← hy_abs, abs_of_neg hyneg] at hle
      linarith
    have hfilter : Sneg.filter (fun x => x ≤ t) = Sneg :=
      Finset.filter_true_of_mem hupper
    have := packing_count (t := t) hδ Sneg hlower hsep
    rw [hfilter] at this
    linarith
  linarith [hsplit, hpos_count, hneg_count]

/-- 块内单项上界：N≤n<2N ⇒ 1/(n³sin²n) ≤ 1/(4N³‖n/π‖²)。
    证明：n≥N ⇒ n³≥N³；Jordan |sin n|≥2‖n/π‖ ⇒ sin²n≥4‖n/π‖²。 -/
lemma block_term_bound {N n : ℕ} (hN : 1 ≤ N) (hnN : N ≤ n) (hn2N : n < 2 * N) :
    1 / (((n : ℝ)) ^ 3 * (sin (n : ℝ)) ^ 2) ≤
      1 / (4 * (N : ℝ) ^ 3 * (distToNearestInt ((n : ℝ) / π)) ^ 2) := by
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hdist_pos : 0 < distToNearestInt ((n : ℝ) / π) := by
    -- π 无理 ⇒ n/π 非整数 ⇒ 距离>0
    apply lt_of_le_of_ne (distToNearestInt_nonneg _)
    intro h
    have : distToNearestInt ((n : ℝ) / π) = 0 := h.symm
    -- 距离=0 ⇒ n/π 是整数 ⇒ π 有理
    have hround : |(n : ℝ) / π - (round ((n : ℝ) / π) : ℝ)| = 0 := this
    have heq : (n : ℝ) / π = (round ((n : ℝ) / π) : ℝ) := by
      linarith [abs_eq_zero.mp hround]
    have hπ : π = (n : ℝ) / (round ((n : ℝ) / π) : ℝ) := by
      have hr0 : (round ((n : ℝ) / π) : ℝ) ≠ 0 := by
        intro h
        rw [h] at heq
        have : (n : ℝ) / π = 0 := heq
        have : (n : ℝ) = 0 := by
          field_simp at this
          linarith
        linarith
      field_simp at heq ⊢
      linarith
    exact pi_irrational ⟨(n : ℤ) / round ((n : ℝ) / π), by
      push_cast
      exact hπ.symm⟩
  have hsin := sin_ge_two_distToNearestInt n
  have hsin2 : (sin (n : ℝ)) ^ 2 ≥ 4 * (distToNearestInt ((n : ℝ) / π)) ^ 2 := by
    have h1 : |sin (n : ℝ)| ≥ 2 * distToNearestInt ((n : ℝ) / π) := hsin
    have h2 : 0 ≤ 2 * distToNearestInt ((n : ℝ) / π) := by positivity
    nlinarith [sq_abs (sin (n : ℝ))]
  have hn3 : (n : ℝ) ^ 3 ≥ (N : ℝ) ^ 3 := by
    have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    gcongr
  have hden : (n : ℝ) ^ 3 * (sin (n : ℝ)) ^ 2 ≥
      4 * (N : ℝ) ^ 3 * (distToNearestInt ((n : ℝ) / π)) ^ 2 := by
    have h1 : (n : ℝ) ^ 3 * (sin (n : ℝ)) ^ 2 ≥
        (N : ℝ) ^ 3 * (4 * (distToNearestInt ((n : ℝ) / π)) ^ 2) := by
      gcongr
    have h2 : (N : ℝ) ^ 3 * (4 * (distToNearestInt ((n : ℝ) / π)) ^ 2) =
        4 * (N : ℝ) ^ 3 * (distToNearestInt ((n : ℝ) / π)) ^ 2 := by ring
    linarith
  have hden_pos : 0 < 4 * (N : ℝ) ^ 3 * (distToNearestInt ((n : ℝ) / π)) ^ 2 := by positivity
  exact one_div_le_one_div_of_le hden_pos hden

/-- 计数控制平方倒数和：有限集 S⊂ℝ，元素≥δ>0，两两距≥δ，
    则 ∑_{x∈S} 1/x² ≤ (2/δ²)·∑_{i≥1}1/i²（用 packing 排序距离 ≥iδ）。
    此处用宽松界 ∑≤(1/δ²)·(card S)（每项≤1/δ²），足够后续几何收敛。 -/
lemma sum_inv_sq_le_card {δ : ℝ} (hδ : 0 < δ) (S : Finset ℝ)
    (hlower : ∀ x ∈ S, δ ≤ x) :
    ∑ x ∈ S, 1 / x ^ 2 ≤ (S.card : ℝ) / δ ^ 2 := by
  have hterm : ∀ x ∈ S, 1 / x ^ 2 ≤ 1 / δ ^ 2 := by
    intro x hx
    have hxδ : δ ≤ x := hlower x hx
    have hx0 : 0 < x := by linarith
    have hx2 : δ ^ 2 ≤ x ^ 2 := by gcongr
    exact one_div_le_one_div_of_le (by positivity) hx2
  calc ∑ x ∈ S, 1 / x ^ 2 ≤ ∑ x ∈ S, 1 / δ ^ 2 := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (1 / δ ^ 2) := by simp [Finset.sum_const]
    _ = (S.card : ℝ) / δ ^ 2 := by ring

/-- 精确平方倒数和常数界：S 元素≥δ>0、两两距≥δ ⇒
    ∑_{x∈S}1/x² ≤ (2/δ²)·∑'_{i}1/(i+1)²。
    证明：按 j=⌊x/δ⌋₊≥1 分层，层 j 至多 2 点（packing_count 差），
    每项≤1/(jδ)²；∑≤∑_j 2/(jδ)²。用 tsum 比较。 -/
lemma sum_inv_sq_const {δ : ℝ} (hδ : 0 < δ) (S : Finset ℝ)
    (hlower : ∀ x ∈ S, δ ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    ∑ x ∈ S, 1 / x ^ 2 ≤ (2 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by
  -- 单射 g(x)=⌊x/δ⌋₊−1；层 j 至多 1 点 ⇒ g 单射
  let g : ℝ → ℕ := fun x => Nat.floor (x / δ) - 1
  have hg_inj : Set.InjOn g (S : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hxδ : δ ≤ x := hlower x hx
    have hyδ : δ ≤ y := hlower y hy
    have hsep' : δ ≤ |x - y| := hsep x hx y hy hne
    have hfloor : Nat.floor (x / δ) = Nat.floor (y / δ) := by
      simp only [g] at hxy
      have hx1 : 1 ≤ Nat.floor (x / δ) := by
        apply Nat.succ_le_of_lt; apply Nat.floor_pos.mpr
        apply (one_le_div hδ).mpr; exact hxδ
      have hy1 : 1 ≤ Nat.floor (y / δ) := by
        apply Nat.succ_le_of_lt; apply Nat.floor_pos.mpr
        apply (one_le_div hδ).mpr; exact hyδ
      omega
    have hx0 : 0 ≤ x / δ := div_nonneg (by linarith [hlower x hx]) (le_of_lt hδ)
    have hy0 : 0 ≤ y / δ := div_nonneg (by linarith [hlower y hy]) (le_of_lt hδ)
    have hlt : |x - y| < δ := by
      have ha' : (Nat.floor (x / δ) : ℝ) ≤ x / δ := Nat.floor_le hx0
      have ha'' : x / δ < (Nat.floor (x / δ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have hb' : (Nat.floor (y / δ) : ℝ) ≤ y / δ := Nat.floor_le hy0
      have hb'' : y / δ < (Nat.floor (y / δ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [← hfloor] at hb' hb''
      have habs : |x / δ - y / δ| < 1 := by rw [abs_lt]; constructor <;> linarith
      have heq : |x / δ - y / δ| = |x - y| / δ := by
        rw [← sub_div, abs_div, abs_of_pos hδ]
      rw [heq] at habs
      rw [div_lt_iff₀ hδ] at habs
      simpa using habs
    linarith
  -- 逐项界：1/x² ≤ (1/δ²)·1/(g(x)+1)²
  have hterm : ∀ x ∈ S, 1 / x ^ 2 ≤ (1 / δ ^ 2) * (1 / ((g x + 1 : ℝ) ^ 2)) := by
    intro x hx
    have hxδ : δ ≤ x := hlower x hx
    have hx0 : 0 < x := by linarith
    have hg1 : (g x + 1 : ℕ) = Nat.floor (x / δ) := by
      simp only [g]
      have : 1 ≤ Nat.floor (x / δ) := by
        apply Nat.succ_le_of_lt; apply Nat.floor_pos.mpr
        apply (one_le_div hδ).mpr; exact hxδ
      omega
    have hxge : (Nat.floor (x / δ) : ℝ) * δ ≤ x := by
      have := Nat.floor_le (div_nonneg (by linarith) (le_of_lt hδ) : 0 ≤ x / δ)
      rw [le_div_iff₀ hδ] at this
      linarith
    have hcast : (g x + 1 : ℝ) = (Nat.floor (x / δ) : ℝ) := by
      norm_cast
    rw [hcast]
    have hfloor_pos : 0 < (Nat.floor (x / δ) : ℝ) := by
      have : 1 ≤ Nat.floor (x / δ) := by
        apply Nat.succ_le_of_lt; apply Nat.floor_pos.mpr
        apply (one_le_div hδ).mpr; exact hxδ
      exact_mod_cast (by omega : 0 < Nat.floor (x / δ))
    have hden_pos : 0 < (Nat.floor (x / δ) : ℝ) * δ := mul_pos hfloor_pos hδ
    have hx2 : ((Nat.floor (x / δ) : ℝ) * δ) ^ 2 ≤ x ^ 2 := by gcongr
    have h1 : 1 / x ^ 2 ≤ 1 / ((Nat.floor (x / δ) : ℝ) * δ) ^ 2 :=
      one_div_le_one_div_of_le (pow_pos hden_pos 2) hx2
    have h2 : 1 / ((Nat.floor (x / δ) : ℝ) * δ) ^ 2 =
        (1 / δ ^ 2) * (1 / (Nat.floor (x / δ) : ℝ) ^ 2) := by field_simp
    linarith
  -- ∑_S ≤ (1/δ²)∑_S 1/(g x+1)²
  have hsum1 : ∑ x ∈ S, 1 / x ^ 2 ≤ (1 / δ ^ 2) * ∑ x ∈ S, 1 / ((g x + 1 : ℝ) ^ 2) := by
    calc ∑ x ∈ S, 1 / x ^ 2 ≤ ∑ x ∈ S, (1 / δ ^ 2) * (1 / (g x + 1 : ℝ) ^ 2) :=
        Finset.sum_le_sum hterm
      _ = (1 / δ ^ 2) * ∑ x ∈ S, 1 / (g x + 1 : ℝ) ^ 2 := by rw [Finset.mul_sum]
  -- ∑_S 1/(g x+1)² = ∑_{i∈g''S} 1/(i+1)² ≤ ∑' 1/(i+1)²
  have hsum2 : ∑ x ∈ S, 1 / ((g x + 1 : ℝ) ^ 2) ≤ ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by
    have hreindex : ∑ x ∈ S, 1 / ((g x + 1 : ℝ) ^ 2) =
        ∑ i ∈ S.image g, 1 / ((i + 1 : ℝ) ^ 2) := by
      symm
      apply Finset.sum_image
      intro x hx y hy hxy
      exact hg_inj hx hy hxy
    rw [hreindex]
    have hsumm : Summable (fun i : ℕ => 1 / ((i + 1 : ℝ) ^ 2)) := by
      have h : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
        summable_one_div_nat_pow.mpr (by norm_num)
      have hc : Summable (fun i : ℕ => 1 / (((Nat.succ i) : ℝ) ^ 2)) :=
        h.comp_injective Nat.succ_injective
      convert hc using 1
      ext i
      simp [Nat.cast_add_one]
    exact hsumm.sum_le_tsum (S.image g) (fun i _ => by positivity)
  -- 组装：(1/δ²)·∑' ≤ (2/δ²)·∑'
  have hfinal : (1 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) ≤
      (2 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by
    have htsum_nonneg : 0 ≤ ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) :=
      tsum_nonneg (fun i => by positivity)
    have hcoef : 1 / δ ^ 2 ≤ 2 / δ ^ 2 := by
      apply (div_le_div_iff_of_pos_right (by positivity : 0 < δ ^ 2)).mpr
      norm_num
    gcongr
  calc ∑ x ∈ S, 1 / x ^ 2
      ≤ (1 / δ ^ 2) * ∑ x ∈ S, 1 / ((g x + 1 : ℝ) ^ 2) := hsum1
    _ ≤ (1 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by
        gcongr
    _ ≤ (2 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := hfinal

/-- 块和估计：∑_{N≤n<2N} 1/(n³sin²n) ≤ C_s·N^(2s−5)，
    其中 C_s = (1/(2c²))·∑'1/(i+1)²·2^(2s−2)（与 N 无关）。
    证明：单项≤1/(4N³‖n/π‖²)；代表元绝对值集用 sum_inv_sq_const（≥δ,两两距≥δ）；
    δ=c(2N)^(1−s)，1/(N³δ²)∝N^(2s−5)。 -/
lemma block_sum_bound {c s : ℝ} (hc : 0 < c) (hs1 : 1 < s)
    (hspacing : ∀ h : ℕ, 0 < h → distToNearestInt ((h : ℝ) / π) ≥ c * (h : ℝ) ^ (1 - s))
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ico N (2 * N), 1 / (((n : ℝ)) ^ 3 * (sin (n : ℝ)) ^ 2) ≤
      ((2 ^ (2 * s - 2) / c ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2)) *
      (N : ℝ) ^ (2 * s - 5) := by
  set δ := c * (2 * N : ℝ) ^ (1 - s) with hδdef
  have hδ : 0 < δ := mul_pos hc (Real.rpow_pos_of_pos (by positivity) (1 - s))
  -- 单项上界求和
  have hterm_sum : ∑ n ∈ Finset.Ico N (2 * N), 1 / ((n : ℝ) ^ 3 * (sin (n : ℝ)) ^ 2) ≤
      (1 / (4 * (N : ℝ) ^ 3)) * ∑ n ∈ Finset.Ico N (2 * N),
        1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 := by
    calc ∑ n ∈ Finset.Ico N (2 * N), 1 / ((n : ℝ) ^ 3 * (sin (n : ℝ)) ^ 2)
        ≤ ∑ n ∈ Finset.Ico N (2 * N), 1 / (4 * (N : ℝ) ^ 3 * (distToNearestInt ((n : ℝ) / π)) ^ 2) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnN : N ≤ n := (Finset.mem_Ico.mp hn).1
          have hn2N : n < 2 * N := (Finset.mem_Ico.mp hn).2
          exact block_term_bound hN hnN hn2N
      _ = (1 / (4 * (N : ℝ) ^ 3)) * ∑ n ∈ Finset.Ico N (2 * N),
          1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 := by
        have : ∀ n : ℕ, 1 / (4 * (N : ℝ) ^ 3 * (distToNearestInt ((n : ℝ) / π)) ^ 2) =
            (1 / (4 * (N : ℝ) ^ 3)) * (1 / (distToNearestInt ((n : ℝ) / π)) ^ 2) := by
          intro n; field_simp
        simp_rw [this]
        rw [Finset.mul_sum]
  -- 代表元绝对值集 S = {|y n| : n∈块}，≥δ，两两距≥δ（用 block_pair_spacing）
  -- 用 sum_inv_sq_const 于正负侧合并：∑_块 1/‖n/π‖² ≤ (4/δ²)∑'1/(i+1)²
  have hdist_sum : ∑ n ∈ Finset.Ico N (2 * N), 1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 ≤
      (4 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by
    let y : ℕ → ℝ := fun n => (n : ℝ) / π - (round ((n : ℝ) / π) : ℝ)
    have hy_abs : ∀ n, |y n| = distToNearestInt ((n : ℝ) / π) := fun n => rfl
    let block := Finset.Ico N (2 * N)
    let pos := block.filter (fun (n : ℕ) => 0 < y n)
    let neg := block.filter (fun (n : ℕ) => y n < 0)
    -- 块分割：pos ∪ neg = block（y n≠0 因 π 无理）
    have hsplit : block = pos ∪ neg := by
      ext n
      simp only [pos, neg, block, Finset.mem_filter, Finset.mem_union, Finset.mem_Ico]
      constructor
      · intro hn
        have hn0 : 0 < n := by omega
        have hy0 : y n ≠ 0 := by
          intro h
          have : distToNearestInt ((n : ℝ) / π) = 0 := by rw [← hy_abs, h]; simp
          have hround : |(n : ℝ) / π - (round ((n : ℝ) / π) : ℝ)| = 0 := this
          have heq : (n : ℝ) / π = (round ((n : ℝ) / π) : ℝ) := by
            linarith [abs_eq_zero.mp hround]
          have hr0 : (round ((n : ℝ) / π) : ℝ) ≠ 0 := by
            intro h
            have heq' : (n : ℝ) / π = 0 := by linarith [heq, h]
            have hn0' : (n : ℝ) = 0 := by
              have := congrArg (fun x => x * π) heq'
              field_simp at this
              linarith
            have : (n : ℝ) > 0 := by exact_mod_cast hn0
            linarith
          have hπ : π = (n : ℝ) / (round ((n : ℝ) / π) : ℝ) := by
            have := heq
            field_simp at this ⊢
            linarith
          exact pi_irrational ⟨(n : ℤ) / round ((n : ℝ) / π), by push_cast; exact hπ.symm⟩
        rcases lt_or_gt_of_ne hy0 with hlt | hgt
        · right; exact ⟨hn, hlt⟩
        · left; exact ⟨hn, hgt⟩
      · intro hn
        rcases hn with ⟨hn, _⟩ | ⟨hn, _⟩ <;> exact hn
    have hdisj : Disjoint pos neg := by
      simp only [pos, neg, Finset.disjoint_left, Finset.mem_filter]
      intro n hn hneg
      linarith [hn.2, hneg.2]
    -- 正侧代表元集
    have hpos_sum : ∑ n ∈ pos, 1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 ≤
        (2 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by
      let Spos := pos.image y
      have hcard : ∑ n ∈ pos, 1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 =
          ∑ x ∈ Spos, 1 / x ^ 2 := by
        have : ∑ n ∈ pos, 1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 =
            ∑ n ∈ pos, 1 / (y n) ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          have hypos : 0 < y n := (Finset.mem_filter.mp hn).2
          rw [← hy_abs, abs_of_pos hypos]
        rw [this]
        symm
        apply Finset.sum_image
        intro n hn m hm hnm
        exact rep_injective hnm
      rw [hcard]
      apply sum_inv_sq_const hδ Spos
      · intro x hx
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
        have hnblock : n ∈ Finset.Ico N (2 * N) := (Finset.mem_filter.mp hn).1
        have hypos : 0 < y n := (Finset.mem_filter.mp hn).2
        have : δ ≤ distToNearestInt ((n : ℝ) / π) :=
          block_point_lower hc hs1 hspacing N n (by
            have : N ≤ n := (Finset.mem_Ico.mp hnblock).1; omega)
            (Finset.mem_Ico.mp hnblock).2
        rw [← hy_abs, abs_of_pos hypos] at this
        exact this
      · intro x hx z hz hxz
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
        have hne : n ≠ m := by intro h; apply hxz; simp [h]
        have hnblock : n ∈ Finset.Ico N (2 * N) := (Finset.mem_filter.mp hn).1
        have hmblock : m ∈ Finset.Ico N (2 * N) := (Finset.mem_filter.mp hm).1
        have hpair := block_pair_spacing hc hs1 hspacing N n m hN
          (Finset.mem_Ico.mp hnblock).1 (Finset.mem_Ico.mp hnblock).2
          (Finset.mem_Ico.mp hmblock).1 (Finset.mem_Ico.mp hmblock).2 hne
        have hdiff : distToNearestInt (((n : ℝ) - (m : ℝ)) / π) ≤ |y n - y m| := by
          have heq : y n - y m = ((n : ℝ) - (m : ℝ)) / π -
              ((round ((n : ℝ) / π) - round ((m : ℝ) / π) : ℤ) : ℝ) := by
            simp only [y]; push_cast; ring
          rw [heq]
          exact distToNearestInt_le _ _
        have hδeq : δ = c * (2 * N : ℝ) ^ (1 - s) := hδdef
        linarith
    -- 负侧代表元集（用 −y）
    have hneg_sum : ∑ n ∈ neg, 1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 ≤
        (2 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by
      let Sneg := neg.image (fun n => -y n)
      have hcard : ∑ n ∈ neg, 1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 =
          ∑ x ∈ Sneg, 1 / x ^ 2 := by
        have : ∑ n ∈ neg, 1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 =
            ∑ n ∈ neg, 1 / (-y n) ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          have hyneg : y n < 0 := (Finset.mem_filter.mp hn).2
          rw [← hy_abs, abs_of_neg hyneg]
        rw [this]
        symm
        apply Finset.sum_image
        intro n hn m hm hnm
        have : y n = y m := by linarith
        exact rep_injective this
      rw [hcard]
      apply sum_inv_sq_const hδ Sneg
      · intro x hx
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
        have hnblock : n ∈ Finset.Ico N (2 * N) := (Finset.mem_filter.mp hn).1
        have hyneg : y n < 0 := (Finset.mem_filter.mp hn).2
        have : δ ≤ distToNearestInt ((n : ℝ) / π) :=
          block_point_lower hc hs1 hspacing N n (by
            have : N ≤ n := (Finset.mem_Ico.mp hnblock).1; omega)
            (Finset.mem_Ico.mp hnblock).2
        rw [← hy_abs, abs_of_neg hyneg] at this
        linarith
      · intro x hx z hz hxz
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
        have hne : n ≠ m := by intro h; apply hxz; simp [h]
        have hnblock : n ∈ Finset.Ico N (2 * N) := (Finset.mem_filter.mp hn).1
        have hmblock : m ∈ Finset.Ico N (2 * N) := (Finset.mem_filter.mp hm).1
        have hpair := block_pair_spacing hc hs1 hspacing N n m hN
          (Finset.mem_Ico.mp hnblock).1 (Finset.mem_Ico.mp hnblock).2
          (Finset.mem_Ico.mp hmblock).1 (Finset.mem_Ico.mp hmblock).2 hne
        have hdiff : distToNearestInt (((n : ℝ) - (m : ℝ)) / π) ≤ |y n - y m| := by
          have heq : y n - y m = ((n : ℝ) - (m : ℝ)) / π -
              ((round ((n : ℝ) / π) - round ((m : ℝ) / π) : ℤ) : ℝ) := by
            simp only [y]; push_cast; ring
          rw [heq]
          exact distToNearestInt_le _ _
        have habs : |(-y n) - (-y m)| = |y n - y m| := by rw [← abs_neg]; congr 1; ring
        have hδeq : δ = c * (2 * N : ℝ) ^ (1 - s) := hδdef
        linarith
    -- 合并
    have hsum_split : ∑ n ∈ block, 1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 =
        ∑ n ∈ pos, 1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 +
        ∑ n ∈ neg, 1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 := by
      rw [hsplit, Finset.sum_union hdisj]
    rw [hsum_split]
    have htsum_nn : 0 ≤ ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) :=
      tsum_nonneg (fun i => by positivity)
    have h4 : (4 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) =
        (2 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) +
        (2 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by ring
    linarith [hpos_sum, hneg_sum]
  -- 组装：1/(4N³)·4/δ² = 1/(N³δ²) = 2^(2s−2)/c²·N^(2s−5)
  have hδ2 : δ ^ 2 = c ^ 2 * (2 * N : ℝ) ^ (2 - 2 * s) := by
    have h2N : 0 ≤ (2 * N : ℝ) := by positivity
    have hpow : ((2 * N : ℝ) ^ (1 - s)) ^ 2 = (2 * N : ℝ) ^ (2 - 2 * s) := by
      have : ((2 * N : ℝ) ^ (1 - s)) ^ 2 = ((2 * N : ℝ) ^ (1 - s)) ^ (2 : ℝ) := by
        simp [Real.rpow_natCast]
      rw [this, ← Real.rpow_mul h2N]
      congr 1
      ring
    calc δ ^ 2 = (c * (2 * N : ℝ) ^ (1 - s)) ^ 2 := by rw [hδdef]
      _ = c ^ 2 * ((2 * N : ℝ) ^ (1 - s)) ^ 2 := by ring
      _ = c ^ 2 * (2 * N : ℝ) ^ (2 - 2 * s) := by rw [hpow]
  have hcombine : (1 / (4 * (N : ℝ) ^ 3)) * ((4 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2)) =
      ((2 ^ (2 * s - 2) / c ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2)) *
      (N : ℝ) ^ (2 * s - 5) := by
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hc0 : c ≠ 0 := by linarith
    have h2N0 : (2 * N : ℝ) ≠ 0 := by positivity
    -- 1/(4N³)·4/δ² = 1/(N³·c²·(2N)^(2−2s))
    have h1 : (1 / (4 * (N : ℝ) ^ 3)) * (4 / δ ^ 2) =
        1 / ((N : ℝ) ^ 3 * c ^ 2 * (2 * N : ℝ) ^ (2 - 2 * s)) := by
      rw [hδ2]
      field_simp
    -- (2N)^(2−2s) = 2^(2−2s)·N^(2−2s)
    have h2 : (2 * N : ℝ) ^ (2 - 2 * s) = (2 : ℝ) ^ (2 - 2 * s) * (N : ℝ) ^ (2 - 2 * s) := by
      rw [mul_rpow (by positivity) (by positivity)]
    -- N³·N^(2−2s) = N^(5−2s)
    have h3 : (N : ℝ) ^ 3 * (N : ℝ) ^ (2 - 2 * s) = (N : ℝ) ^ (5 - 2 * s) := by
      rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_add (by positivity : 0 < (N : ℝ))]
      congr 1; ring
    -- 1/N^(5−2s) = N^(2s−5)
    have h4 : 1 / (N : ℝ) ^ (5 - 2 * s) = (N : ℝ) ^ (2 * s - 5) := by
      rw [show (2 * s - 5 : ℝ) = -(5 - 2 * s) by ring, Real.rpow_neg (by positivity)]
      field_simp
    -- 1/2^(2−2s) = 2^(2s−2)
    have h5 : 1 / (2 : ℝ) ^ (2 - 2 * s) = (2 : ℝ) ^ (2 * s - 2) := by
      rw [show (2 * s - 2 : ℝ) = -(2 - 2 * s) by ring, Real.rpow_neg (by positivity)]
      field_simp
    calc (1 / (4 * (N : ℝ) ^ 3)) * ((4 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2))
        = ((1 / (4 * (N : ℝ) ^ 3)) * (4 / δ ^ 2)) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by ring
      _ = (1 / ((N : ℝ) ^ 3 * c ^ 2 * (2 * N : ℝ) ^ (2 - 2 * s))) *
          ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by rw [h1]
      _ = (1 / ((N : ℝ) ^ 3 * c ^ 2 * ((2 : ℝ) ^ (2 - 2 * s) * (N : ℝ) ^ (2 - 2 * s)))) *
          ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by rw [h2]
      _ = (1 / (c ^ 2 * (2 : ℝ) ^ (2 - 2 * s) * ((N : ℝ) ^ 3 * (N : ℝ) ^ (2 - 2 * s)))) *
          ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by ring
      _ = (1 / (c ^ 2 * (2 : ℝ) ^ (2 - 2 * s) * (N : ℝ) ^ (5 - 2 * s))) *
          ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by rw [h3]
      _ = ((2 ^ (2 * s - 2) / c ^ 2) * (N : ℝ) ^ (2 * s - 5)) *
          ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) := by
        have hkey : 1 / (c ^ 2 * (2 : ℝ) ^ (2 - 2 * s) * (N : ℝ) ^ (5 - 2 * s)) =
            (2 ^ (2 * s - 2) / c ^ 2) * (N : ℝ) ^ (2 * s - 5) := by
          have h2 : (2 : ℝ) ^ (2 * s - 2) = 1 / (2 : ℝ) ^ (2 - 2 * s) := by
            rw [show (2 * s - 2 : ℝ) = -(2 - 2 * s) by ring, Real.rpow_neg (by positivity)]
            field_simp
          have hN : (N : ℝ) ^ (2 * s - 5) = 1 / (N : ℝ) ^ (5 - 2 * s) := by
            rw [show (2 * s - 5 : ℝ) = -(5 - 2 * s) by ring, Real.rpow_neg (by positivity)]
            field_simp
          rw [h2, hN]
          field_simp
        rw [hkey]
      _ = ((2 ^ (2 * s - 2) / c ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2)) *
          (N : ℝ) ^ (2 * s - 5) := by ring
  calc ∑ n ∈ Finset.Ico N (2 * N), 1 / ((n : ℝ) ^ 3 * (sin (n : ℝ)) ^ 2)
      ≤ (1 / (4 * (N : ℝ) ^ 3)) * ∑ n ∈ Finset.Ico N (2 * N),
        1 / (distToNearestInt ((n : ℝ) / π)) ^ 2 := hterm_sum
    _ ≤ (1 / (4 * (N : ℝ) ^ 3)) * ((4 / δ ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2)) := by
        gcongr
    _ = ((2 ^ (2 * s - 2) / c ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2)) *
        (N : ℝ) ^ (2 * s - 5) := hcombine

/-- 几何级数收敛因子：s<5/2 ⇒ 2^(2s−5)<1。 -/
lemma geom_ratio_lt_one {s : ℝ} (hs : s < 5 / 2) : (2 : ℝ) ^ (2 * s - 5) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  linarith

/-- Flint Hills 收敛（Meiburg 判据，μ(π)<5/2）：用二进块分解 + 几何级数。
    块 k 的和 ≤C_s·2^(k(2s−5))，∑_k 几何收敛（2s−5<0）。 -/
theorem flint_hills_converges_of_mu_lt (hμ : irrMeasure π < 5 / 2) :
    Summable (fun n : ℕ => 1 / (((n + 1) : ℝ) ^ 3 * (sin (n + 1)) ^ 2)) := by
  -- μ(π) 有限（<5/2<⊤）
  have h5top : (5 / 2 : ENNReal) < ⊤ := by
    simpa using (ENNReal.coe_lt_top : ((5 / 2 : NNReal) : ENNReal) < ⊤)
  have hμ_fin : irrMeasure π ≠ ⊤ := ne_of_lt (lt_trans hμ h5top)
  -- 取 NNReal M = μ(π).toReal
  let M : NNReal := ⟨(irrMeasure π).toReal, ENNReal.toReal_nonneg⟩
  have hM_coe : (M : ENNReal) = irrMeasure π := by
    have hbridge : (M : ENNReal) = ENNReal.ofReal (irrMeasure π).toReal := by
      have : (M : ℝ) = (irrMeasure π).toReal := rfl
      rw [ENNReal.coe_nnreal_eq, this]
    rw [hbridge, ENNReal.ofReal_toReal hμ_fin]
  have hμ_le_M : irrMeasure π ≤ (M : ENNReal) := le_of_eq hM_coe.symm
  have hM_lt : (M : ℝ) < 5 / 2 := by
    have h5fin : (5 / 2 : ENNReal) ≠ ⊤ := ne_of_lt h5top
    have h := (ENNReal.toReal_lt_toReal hμ_fin h5fin).2 hμ
    have h5 : (5 / 2 : ENNReal).toReal = (5 / 2 : ℝ) := by
      have : (5 / 2 : ENNReal) = ((5 / 2 : NNReal) : ENNReal) := by norm_num
      rw [this]
      simp
    change (irrMeasure π).toReal < 5 / 2
    linarith
  set s := ((M : ℝ) + 5 / 2) / 2 with hsdef
  have hs_lt : s < 5 / 2 := by linarith
  have hM_lt_s : (M : ℝ) < s := by linarith
  have hs1 : 1 < s := by
    have : 0 ≤ (M : ℝ) := NNReal.coe_nonneg M
    linarith
  obtain ⟨c, hc, hspacing⟩ := circle_spacing hμ_le_M hM_lt_s hs1
  set Cs := (2 ^ (2 * s - 2) / c ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2) with hCsdef
  have hCs_nn : 0 ≤ Cs := by
    apply mul_nonneg
    · apply div_nonneg (Real.rpow_nonneg (by norm_num) _) (by positivity)
    · exact tsum_nonneg (fun i => by positivity)
  have hratio : (2 : ℝ) ^ (2 * s - 5) < 1 := geom_ratio_lt_one hs_lt
  have hratio_nn : 0 ≤ (2 : ℝ) ^ (2 * s - 5) := Real.rpow_nonneg (by norm_num) _
  have hgeom : Summable (fun k : ℕ => Cs * ((2 : ℝ) ^ (2 * s - 5)) ^ k) :=
    (summable_geometric_of_lt_one hratio_nn hratio).mul_left Cs
  have hterm_nn : ∀ n : ℕ, 0 ≤ 1 / (((n + 1) : ℝ) ^ 3 * (sin (n + 1)) ^ 2) := by
    intro n; positivity
  -- 部分和单调
  have hmono : Monotone (fun N : ℕ => ∑ n ∈ Finset.range N,
      1 / (((n + 1) : ℝ) ^ 3 * (sin (n + 1)) ^ 2)) := by
    intro a b hab
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono hab
    · intro i _ _; exact hterm_nn i
  -- 块和界
  have hblock : ∀ k : ℕ, ∑ m ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ),
      1 / ((m : ℝ) ^ 3 * (sin (m : ℝ)) ^ 2) ≤ Cs * (2 : ℝ) ^ (k * (2 * s - 5)) := by
    intro k
    have h2k : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow _ _ (by norm_num)
    have hb := block_sum_bound hc hs1 hspacing (2 ^ k) h2k
    have hbound_eq : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have hpow : ((2 ^ k : ℕ) : ℝ) ^ (2 * s - 5) = (2 : ℝ) ^ (k * (2 * s - 5)) := by
      have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k : ℝ) := by
        rw [show ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k by norm_cast, Real.rpow_natCast]
      rw [hcast, ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
    have hb' : ∑ m ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ),
        1 / ((m : ℝ) ^ 3 * (sin (m : ℝ)) ^ 2) ≤
        ((2 ^ (2 * s - 2) / c ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2)) *
        ((2 ^ k : ℕ) : ℝ) ^ (2 * s - 5) := by
      convert hb using 1
      · rw [hbound_eq]
    calc ∑ m ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ),
        1 / ((m : ℝ) ^ 3 * (sin (m : ℝ)) ^ 2)
        ≤ ((2 ^ (2 * s - 2) / c ^ 2) * ∑' i : ℕ, 1 / ((i + 1 : ℝ) ^ 2)) *
          ((2 ^ k : ℕ) : ℝ) ^ (2 * s - 5) := hb'
      _ = Cs * (2 : ℝ) ^ (k * (2 * s - 5)) := by rw [hCsdef, hpow]
  -- 部分和有界
  set B := Cs / (1 - (2 : ℝ) ^ (2 * s - 5)) with hBdef
  have hbdd : BddAbove (Set.range (fun N : ℕ => ∑ n ∈ Finset.range N,
      1 / (((n + 1) : ℝ) ^ 3 * (sin (n + 1)) ^ 2))) := by
    use B
    intro x hx
    obtain ⟨N, rfl⟩ := hx
    have hgeom_sum : ∑' k : ℕ, Cs * ((2 : ℝ) ^ (2 * s - 5)) ^ k = B := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hratio_nn hratio, hBdef]
      ring
    have hshift : ∑ n ∈ Finset.range N, 1 / (((n + 1) : ℝ) ^ 3 * (sin (n + 1)) ^ 2) =
        ∑ m ∈ Finset.Ico (1 : ℕ) (N + 1), 1 / ((m : ℝ) ^ 3 * (sin (m : ℝ)) ^ 2) := by
      have h := Finset.sum_Ico_eq_sum_range (f := fun m : ℕ => 1 / ((m : ℝ) ^ 3 * (sin (m : ℝ)) ^ 2)) 1 (N + 1)
      -- h : ∑ m∈Ico 1 (N+1), f m = ∑ x∈range N, f (x+1)
      have hcong : ∑ x ∈ Finset.range N, 1 / (((x + 1 : ℕ) : ℝ) ^ 3 * (sin ((x + 1 : ℕ) : ℝ)) ^ 2) =
          ∑ n ∈ Finset.range N, 1 / (((n + 1) : ℝ) ^ 3 * (sin (n + 1)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro n _
        simp [Nat.cast_add_one]
      have hsymm : ∑ x ∈ Finset.range N, 1 / (((x + 1 : ℕ) : ℝ) ^ 3 * (sin ((x + 1 : ℕ) : ℝ)) ^ 2) =
          ∑ m ∈ Finset.Ico (1 : ℕ) (N + 1), 1 / ((m : ℝ) ^ 3 * (sin (m : ℝ)) ^ 2) := by
        convert h.symm using 1
        apply Finset.sum_congr rfl
        intro x _
        field_simp
        push_cast
        ring
      calc ∑ n ∈ Finset.range N, 1 / (((n + 1) : ℝ) ^ 3 * (sin (n + 1)) ^ 2)
          = ∑ x ∈ Finset.range N, 1 / (((x + 1 : ℕ) : ℝ) ^ 3 * (sin ((x + 1 : ℕ) : ℝ)) ^ 2) := hcong.symm
        _ = ∑ m ∈ Finset.Ico (1 : ℕ) (N + 1), 1 / ((m : ℝ) ^ 3 * (sin (m : ℝ)) ^ 2) := hsymm
    have hK : ∃ K : ℕ, N + 1 ≤ 2 ^ K := by
      use N + 1
      exact Nat.le_of_lt (Nat.lt_pow_self (by norm_num : 1 < 2))
    obtain ⟨K, hK⟩ := hK
    have hsub : Finset.Ico (1 : ℕ) (N + 1) ⊆ Finset.Ico (1 : ℕ) (2 ^ K) :=
      Finset.Ico_subset_Ico_right hK
    have hsplit : Finset.Ico (1 : ℕ) (2 ^ K) =
        Finset.biUnion (Finset.range K) (fun k => Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ)) := by
      have hgen : ∀ K : ℕ, Finset.Ico (2 ^ 0 : ℕ) (2 ^ K) =
          Finset.biUnion (Finset.range K) (fun k => Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ)) := by
        intro K
        induction K with
        | zero => simp
        | succ K ih =>
          rw [Finset.range_add_one, Finset.biUnion_insert, ← ih]
          have h1 : (2 : ℕ) ^ 0 ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2 : (2 : ℕ) ^ K ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have hunion : Finset.Ico (2 ^ 0 : ℕ) (2 ^ K) ∪ Finset.Ico (2 ^ K) (2 ^ (K + 1)) =
              Finset.Ico (2 ^ 0 : ℕ) (2 ^ (K + 1)) := Finset.Ico_union_Ico_eq_Ico h1 h2
          rw [Finset.union_comm, hunion]
      have h20 : (2 : ℕ) ^ 0 = 1 := by norm_num
      rw [← h20]; exact hgen K
    have hdisj : ∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K, i ≠ j →
        Disjoint (Finset.Ico (2 ^ i : ℕ) (2 ^ (i + 1) : ℕ))
          (Finset.Ico (2 ^ j : ℕ) (2 ^ (j + 1) : ℕ)) := by
      intro i hi j hj hij
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      have hi2 : x < 2 ^ (i + 1) := (Finset.mem_Ico.mp hx1).2
      have hj1 : 2 ^ j ≤ x := (Finset.mem_Ico.mp hx2).1
      have hj2 : x < 2 ^ (j + 1) := (Finset.mem_Ico.mp hx2).2
      have hi1 : 2 ^ i ≤ x := (Finset.mem_Ico.mp hx1).1
      have : i < j ∨ j < i := by omega
      rcases this with h | h
      · have : (2 : ℕ) ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · have : (2 : ℕ) ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    have hfin : ∑ m ∈ Finset.Ico (1 : ℕ) (N + 1), 1 / ((m : ℝ) ^ 3 * (sin (m : ℝ)) ^ 2) ≤
        ∑ k ∈ Finset.range K, Cs * ((2 : ℝ) ^ (2 * s - 5)) ^ k := by
      calc ∑ m ∈ Finset.Ico (1 : ℕ) (N + 1), 1 / ((m : ℝ) ^ 3 * (sin (m : ℝ)) ^ 2)
          ≤ ∑ m ∈ Finset.Ico (1 : ℕ) (2 ^ K), 1 / ((m : ℝ) ^ 3 * (sin (m : ℝ)) ^ 2) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro m _ _; positivity
        _ = ∑ k ∈ Finset.range K, ∑ m ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ),
            1 / ((m : ℝ) ^ 3 * (sin (m : ℝ)) ^ 2) := by
            rw [hsplit, Finset.sum_biUnion]; exact hdisj
        _ ≤ ∑ k ∈ Finset.range K, Cs * ((2 : ℝ) ^ (2 * s - 5)) ^ k := by
            apply Finset.sum_le_sum
            intro k hk
            have := hblock k
            have hpoweq : (2 : ℝ) ^ (k * (2 * s - 5)) = ((2 : ℝ) ^ (2 * s - 5)) ^ k := by
              have : ((2 : ℝ) ^ (2 * s - 5)) ^ k = (2 : ℝ) ^ ((2 * s - 5) * k) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
              rw [this]
              push_cast
              ring_nf
            simpa [hpoweq] using this
    have hle_tsum : ∑ k ∈ Finset.range K, Cs * ((2 : ℝ) ^ (2 * s - 5)) ^ k ≤
        ∑' k : ℕ, Cs * ((2 : ℝ) ^ (2 * s - 5)) ^ k :=
      hgeom.sum_le_tsum _ (fun k _ => mul_nonneg hCs_nn (pow_nonneg hratio_nn k))
    have hgoal : (fun N : ℕ => ∑ n ∈ Finset.range N,
        1 / (((n + 1) : ℝ) ^ 3 * (sin (n + 1)) ^ 2)) N ≤ B := by
      change ∑ n ∈ Finset.range N, 1 / (((n + 1) : ℝ) ^ 3 * (sin (n + 1)) ^ 2) ≤ B
      rw [hshift]
      linarith [hfin, hle_tsum, hgeom_sum]
    exact hgoal
  have hL := tendsto_atTop_ciSup hmono hbdd
  have hhas := (hasSum_iff_tendsto_nat_of_nonneg hterm_nn _).mpr hL
  exact hhas.summable
