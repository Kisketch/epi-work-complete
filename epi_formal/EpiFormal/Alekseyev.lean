import Mathlib
import EpiFormal.Measure
import EpiFormal.FlintHills

/-!
# T3：Alekseyev 方向形式化（Flint Hills 收敛 ⇒ μ(π) ≤ 5/2）

路线（2026-11-14 修订包更正 1：最近整数论证；参考 Alekseyev 2011 推论 4）：
1. 对每个 q≥1 取 p = round(qπ)（最近整数）：|p−qπ|≤1/2、p≤4q、p→∞；
2. |sin p| ≤ |p−qπ|（周期平移 + Lipschitz，abs_sin_int_le）；
3. Flint Hills 收敛 ⇒ 项→0 ⇒ p^(3/2)|sin p|→∞；
4. q^(5/2)|π−a/q| = q^(3/2)|qπ−a| ≥ q^(3/2)|qπ−p| ≥ 4^(−3/2)·p^(3/2)|sin p|，
   对**所有整数 a 一致**地→∞；吸收有限例外后得最终一致下界 q^(−(5/2+ε))；
5. ν>5/2 的好逼近对集有限 ⇒ apprSet 上界 ⇒ μ(π)≤5/2。

关键修正（历史教训）：sin 下界给 |n−mπ|=|m|·|π−n/m|（n 分子、m 分母）。
早期头注释曾误写 |n−mπ|=n|π−m/n|，该恒等式为假（n−mπ≠−n(π−m/n)），已修正。
朴素逐项法对所有大 n 用统一下界，方向不匹配（见文件末节障碍记录）；
最近整数论证只对 p=round(qπ)（自动满足 p≍q）用下界，绕开该障碍，无需密度论证。
原 alekseyev_diophantine 陈述方向写反，已弃用删除。
-/

open Filter Topology Real

/-- sin 整数非零：n≥1 ⇒ sin n ≠ 0（π 无理）。 -/
lemma sin_nat_ne_zero (n : ℕ) (hn : 0 < n) : sin (n : ℝ) ≠ 0 := by
  intro h
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  have hm0 : m ≠ 0 := by
    intro hm0
    rw [hm0, Int.cast_zero, zero_mul] at hm
    have hn0' : (n : ℝ) = 0 := by linarith
    exact (Nat.ne_of_gt hn) (by exact_mod_cast hn0')
  have hpi : π = (n : ℝ) / (m : ℝ) := by
    have := hm.symm
    field_simp at this ⊢
    linarith
  have hrat : ∃ q : ℚ, (q : ℝ) = π := by
    refine ⟨(n : ℚ) / (m : ℚ), ?_⟩
    push_cast
    exact hpi.symm
  exact pi_irrational hrat

/-- T3 第一步：项→0 ⇒ 最终 |sin n| ≥ n^(−3/2−ε)。
    证明：aₙ=1/(n³sin²n)→0 ⇒ 最终 aₙ<1 ⇒ n³sin²n>1 ⇒ |sin n|>n^(−3/2)≥n^(−3/2−ε)。 -/
lemma sin_eventual_lower (hterm : Tendsto
    (fun n : ℕ => 1 / (((n + 1) : ℝ)^3 * (sin (n + 1))^2)) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |sin (n : ℝ)| ≥ (n : ℝ) ^ (-(3 / 2 + ε)) := by
  have h1 : ∀ᶠ n : ℕ in atTop, 1 / (((n + 1) : ℝ)^3 * (sin (n + 1))^2) < 1 :=
    hterm.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h1
  use N + 1
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hkN : N ≤ n - 1 := by omega
  have hak : 1 / ((n : ℝ)^3 * (sin (n : ℝ))^2) < 1 := by
    have := hN (n - 1) hkN
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      ring
    simpa only [hcast] using this
  have hsin0 : sin (n : ℝ) ≠ 0 := sin_nat_ne_zero n hn0
  have hden_pos : (0 : ℝ) < (n : ℝ)^3 * (sin (n : ℝ))^2 :=
    mul_pos (pow_pos hnpos 3) (sq_pos_of_ne_zero hsin0)
  have hge : (n : ℝ)^3 * (sin (n : ℝ))^2 > 1 :=
    (div_lt_one hden_pos).mp hak
  have hge' : (n : ℝ)^3 * (sin (n : ℝ))^2 ≥ 1 := le_of_lt hge
  have hsin2 : (sin (n : ℝ))^2 ≥ (n : ℝ) ^ (-(3 : ℝ)) := by
    calc (sin (n : ℝ))^2 = ((n : ℝ)^3 * (sin (n : ℝ))^2) / (n : ℝ)^3 := by field_simp
      _ ≥ 1 / (n : ℝ)^3 := by gcongr
      _ = (n : ℝ) ^ (-(3 : ℝ)) := by
        rw [Real.rpow_neg (le_of_lt hnpos)]
        norm_num
  have habs : |sin (n : ℝ)| ≥ (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hb : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt hnpos) _
    have hsq : ((n : ℝ) ^ (-(3 / 2 : ℝ)))^2 ≤ (sin (n : ℝ))^2 := by
      have heq : ((n : ℝ) ^ (-(3 / 2 : ℝ)))^2 = (n : ℝ) ^ (-(3 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hnpos)]
        congr 1
        ring
      rw [heq]
      exact hsin2
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hb] at this
  have hmono : (n : ℝ) ^ (-(3 / 2 : ℝ)) ≥ (n : ℝ) ^ (-(3 / 2 + ε)) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast hn1
    · linarith
  linarith

/-- 辅助恒等式（已证）：|n − mπ| = |m|·|π − n/m|（m≠0）。
    注意方向：n 是 sin 参数（分子），m 是 π 系数（分母）。 -/
lemma abs_sub_mul_pi_factor (n : ℕ) (m : ℤ) (hm0 : m ≠ 0) :
    |(n : ℝ) - (m : ℝ) * π| = |(m : ℝ)| * |π - (n : ℝ) / (m : ℝ)| := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  have h : (n : ℝ) - (m : ℝ) * π = -((m : ℝ) * (π - (n : ℝ) / (m : ℝ))) := by
    field_simp
    ring
  rw [h, abs_neg, abs_mul]

/-!
## T3 障碍的精确坐标（历史记录，保留备查）

由 sin_eventual_lower 得最终 |sin n| ≥ n^(−3/2−ε)；由 abs_sin_int_le 与
abs_sub_mul_pi_factor 得 |m|·|π − n/m| ≥ |sin n| ≥ n^(−3/2−ε)，故
  |π − n/m| ≥ n^(−3/2−ε) / |m|。
要推出 μ(π) ≤ 5/2 所需的 |π − n/m| ≥ C·|m|^(−5/2−ε)，等价于
  n^(−3/2−ε) ≥ C·|m|^(−3/2−ε)  ⟺  n ≤ C'·|m|（指数为负）。
但 sin 下界对**所有**充分大 n 成立，包括 n > π·|m| 的情形，此时方向反转。
因此"逐项 sin 下界 ⇒ μ(π)≤5/2"的直接论证**不成立**——这正是档案第七轮记录的
分子分母障碍。

**2026-11-14 修订包更正 1**：最近整数论证绕开该障碍——只对 p=round(qπ)
（自动满足 p≍q，p≤4q）用 sin 下界，q^(3/2) 换 p^(3/2) 仅损失常数 4^(−3/2)，
无需密度论证。以下将该纸面证明完整形式化（机器验证）。
-/

/-- 最近整数 p=round(qπ) 的上界：p ≤ 4q（q≥1）。
    round(qπ) ≤ qπ+1/2 ≤ 4q−q+1/2 ≤ 4q（π<4，q≥1）。 -/
lemma nearest_int_le_four_mul (q : ℕ) (hq : 1 ≤ q) :
    round ((q : ℝ) * π) ≤ 4 * (q : ℤ) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have h1 : (round ((q : ℝ) * π) : ℝ) ≤ (q : ℝ) * π + 1 / 2 := round_le_add_half _
  have h2 : (q : ℝ) * π < 4 * (q : ℝ) := by
    have := mul_lt_mul_of_pos_left Real.pi_lt_four hqpos
    linarith
  -- round(qπ) ≤ qπ+1/2 < 4q+1/2 < 4q+1；整数性 ⇒ round(qπ) ≤ 4q。
  have h3 : (round ((q : ℝ) * π) : ℝ) < 4 * (q : ℝ) + 1 := by linarith
  have h4 : round ((q : ℝ) * π) < 4 * (q : ℤ) + 1 := by exact_mod_cast h3
  linarith

/-- p=round(qπ) 沿 atTop 趋于 +∞：p > qπ−1/2 → ∞。 -/
lemma nearest_int_tendsto_atTop :
    Tendsto (fun q : ℕ => round ((q : ℝ) * π)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (((b : ℝ) + 1 / 2) / π)
  use N
  intro q hq
  have hqR : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : ((b : ℝ) + 1 / 2) / π < (q : ℝ) := lt_of_lt_of_le hN hqR
  have h2 : (b : ℝ) + 1 / 2 < (q : ℝ) * π := by
    rwa [div_lt_iff₀ Real.pi_pos] at h1
  have h3 : (q : ℝ) * π - 1 / 2 < (round ((q : ℝ) * π) : ℝ) := sub_half_lt_round _
  have h4 : (b : ℝ) < (round ((q : ℝ) * π) : ℝ) := by linarith
  exact le_of_lt (by exact_mod_cast h4)

/-- 项→0 ⇒ 最终 n³sin²n > B（任意 B>0）。 -/
lemma term_tendsto_eventually_gt (hterm : Tendsto
    (fun n : ℕ => 1 / (((n + 1) : ℝ)^3 * (sin (n + 1))^2)) atTop (nhds 0))
    (B : ℝ) (hB : 0 < B) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ)^3 * (sin (n : ℝ))^2 > B := by
  have h1 : ∀ᶠ n : ℕ in atTop,
      1 / (((n + 1) : ℝ)^3 * (sin (n + 1))^2) < 1 / B :=
    hterm.eventually (Iio_mem_nhds (one_div_pos.mpr hB))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h1
  use N + 1
  intro n hn
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hkN : N ≤ n - 1 := by omega
  have hak : 1 / ((n : ℝ)^3 * (sin (n : ℝ))^2) < 1 / B := by
    have := hN (n - 1) hkN
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      ring
    simpa only [hcast] using this
  have hsin0 : sin (n : ℝ) ≠ 0 := sin_nat_ne_zero n hn0
  have hden_pos : (0 : ℝ) < (n : ℝ)^3 * (sin (n : ℝ))^2 :=
    mul_pos (pow_pos hnpos 3) (sq_pos_of_ne_zero hsin0)
  have := (one_div_lt_one_div hden_pos hB).mp hak
  linarith

/-- 核心一致下界（修订包更正 1 的形式化）：Flint Hills 收敛 ⇒ ∀ε>0，最终对所有整数 a，
    |π−a/q| ≥ q^(−(5/2+ε))。
    证明：p=round(qπ)，|p−qπ|≤1/2、p≤4q、p→∞；|sin p|≤|p−qπ|；
    项→0 ⇒ p³sin²p 最终任意大 ⇒ p^(3/2)|sin p|→∞；
    q^(5/2)|π−a/q| = q^(3/2)|qπ−a| ≥ q^(3/2)|qπ−p| ≥ 4^(−3/2)·p^(3/2)|sin p|，
    对 a 一致。取 B=(4^(3/2))²=64 吸收常数与有限例外。 -/
theorem alekseyev_eventual_lower (hconv : FlintHillsConjecture) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q → ∀ a : ℤ,
      |π - (a : ℝ) / (q : ℝ)| ≥ (q : ℝ) ^ (-(5 / 2 + ε)) := by
  have hterm := flint_hills_term_tendsto_zero hconv
  -- 常数 C₀ = 4^(3/2) = 8
  have hC0 : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
    have h4 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
    calc (4 : ℝ) ^ (3 / 2 : ℝ) = (2 ^ (2 : ℝ)) ^ (3 / 2 : ℝ) := by rw [h4]
      _ = 2 ^ ((2 : ℝ) * (3 / 2)) := (Real.rpow_mul (by norm_num) 2 (3 / 2)).symm
      _ = 2 ^ (3 : ℝ) := by norm_num
      _ = 8 := by norm_num
  -- 取 B = (4^(3/2))² = 64；项→0 ⇒ 最终 n³sin²n > B
  obtain ⟨N1, hN1⟩ := term_tendsto_eventually_gt hterm (64 : ℝ) (by norm_num)
  -- p=round(qπ)→∞ ⇒ 最终 p ≥ N1
  obtain ⟨N2, hN2⟩ :=
    (Filter.tendsto_atTop_atTop.mp nearest_int_tendsto_atTop) (N1 : ℤ)
  use max N2 1
  intro q hq a
  have hqN2 : N2 ≤ q := le_trans (le_max_left _ _) hq
  have hq1 : 1 ≤ q := le_trans (le_max_right _ _) hq
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  set p : ℤ := round ((q : ℝ) * π) with hpdef
  have hpN1 : (N1 : ℤ) ≤ p := hN2 q hqN2
  have hpN1' : N1 ≤ p.toNat := by
    have : (N1 : ℤ) ≤ p := hpN1
    omega
  have hp_toNat : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (by linarith : 0 ≤ p)
  have hp3 : (p : ℝ)^3 * (sin (p : ℝ))^2 > (64 : ℝ) := by
    have := hN1 p.toNat hpN1'
    have hcast : (p.toNat : ℝ) = (p : ℝ) := by exact_mod_cast hp_toNat
    simpa only [hcast] using this
  -- p^(3/2)|sin p| > 4^(3/2)（两边开方，用 sq_lt_sq）
  have hpR0 : (0 : ℝ) ≤ (p : ℝ) := by
    have : (0 : ℤ) ≤ p := by linarith
    exact_mod_cast this
  have hp3' : ((p : ℝ) ^ (3 / 2 : ℝ) * |sin (p : ℝ)|) ^ 2 >
      ((4 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 := by
    have heq : ((p : ℝ) ^ (3 / 2 : ℝ) * |sin (p : ℝ)|) ^ 2 =
        (p : ℝ)^3 * (sin (p : ℝ))^2 := by
      calc ((p : ℝ) ^ (3 / 2 : ℝ) * |sin (p : ℝ)|) ^ 2 =
          ((p : ℝ) ^ (3 / 2 : ℝ)) ^ 2 * |sin (p : ℝ)| ^ 2 := by ring
        _ = (p : ℝ) ^ ((3 / 2 : ℝ) * 2) * (sin (p : ℝ)) ^ 2 := by
          rw [sq_abs]
          congr 1
          rw [← Real.rpow_natCast ((p : ℝ) ^ (3 / 2 : ℝ)) 2,
            ← Real.rpow_mul hpR0]
          norm_num
        _ = (p : ℝ) ^ (3 : ℝ) * (sin (p : ℝ)) ^ 2 := by norm_num
        _ = (p : ℝ)^3 * (sin (p : ℝ))^2 := by norm_num
    have h4sq : ((4 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (64 : ℝ) := by
      rw [hC0]
      norm_num
    rw [heq, h4sq]
    exact hp3
  have hp_gt : (p : ℝ) ^ (3 / 2 : ℝ) * |sin (p : ℝ)| > (4 : ℝ) ^ (3 / 2 : ℝ) := by
    have := sq_lt_sq.mp hp3'
    rwa [abs_of_nonneg (by positivity : 0 ≤ (p : ℝ) ^ (3 / 2 : ℝ) * |sin (p : ℝ)|),
      abs_of_nonneg (by positivity : 0 ≤ (4 : ℝ) ^ (3 / 2 : ℝ))] at this
  -- q^(3/2) ≥ 4^(−3/2)·p^(3/2)（p≤4q，指数单调）
  have hp_le4q : (p : ℝ) ≤ 4 * (q : ℝ) := by
    have := nearest_int_le_four_mul q hq1
    exact_mod_cast this
  have hq32 : (q : ℝ) ^ (3 / 2 : ℝ) ≥
      (4 : ℝ) ^ (-(3 / 2 : ℝ)) * (p : ℝ) ^ (3 / 2 : ℝ) := by
    have hpR : (0 : ℝ) ≤ (p : ℝ) := by
      have : (0 : ℤ) ≤ p := by linarith
      exact_mod_cast this
    have h1 : (p : ℝ) ^ (3 / 2 : ℝ) ≤ (4 * (q : ℝ)) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hpR hp_le4q (by norm_num)
    have h2 : (4 * (q : ℝ)) ^ (3 / 2 : ℝ) =
        (4 : ℝ) ^ (3 / 2 : ℝ) * (q : ℝ) ^ (3 / 2 : ℝ) :=
      Real.mul_rpow (by norm_num) (le_of_lt hqR)
    have h3 : (4 : ℝ) ^ (-(3 / 2 : ℝ)) * (4 : ℝ) ^ (3 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
      norm_num
    calc (q : ℝ) ^ (3 / 2 : ℝ) =
        ((4 : ℝ) ^ (-(3 / 2 : ℝ)) * (4 : ℝ) ^ (3 / 2 : ℝ)) * (q : ℝ) ^ (3 / 2 : ℝ) := by
          rw [h3]; ring
      _ = (4 : ℝ) ^ (-(3 / 2 : ℝ)) *
          ((4 : ℝ) ^ (3 / 2 : ℝ) * (q : ℝ) ^ (3 / 2 : ℝ)) := by ring
      _ ≥ (4 : ℝ) ^ (-(3 / 2 : ℝ)) * (p : ℝ) ^ (3 / 2 : ℝ) := by
          gcongr
          rw [← h2]
          exact h1
  -- 误差链：|qπ−a| ≥ |qπ−p| ≥ |sin p|
  have herr : |(q : ℝ) * π - (a : ℝ)| ≥ |(q : ℝ) * π - (p : ℝ)| := by
    have := round_le ((q : ℝ) * π) a
    simpa [abs_sub_comm] using this
  have hsin : |(q : ℝ) * π - (p : ℝ)| ≥ |sin (p : ℝ)| := by
    have h0 : |sin (p.toNat : ℝ)| ≤ |(p.toNat : ℝ) - (q : ℝ) * π| :=
      abs_sin_int_le p.toNat (q : ℤ)
    have hcast : (p.toNat : ℝ) = (p : ℝ) := by exact_mod_cast hp_toNat
    have h1 : |sin (p : ℝ)| ≤ |(p : ℝ) - (q : ℝ) * π| := by
      simpa only [hcast] using h0
    have hflip : |(p : ℝ) - (q : ℝ) * π| = |(q : ℝ) * π - (p : ℝ)| :=
      abs_sub_comm _ _
    linarith
  -- 合并：q^(5/2)|π−a/q| ≥ 4^(−3/2)·p^(3/2)|sin p| > 1
  have hmain : (q : ℝ) ^ (5 / 2 : ℝ) * |π - (a : ℝ) / (q : ℝ)| > 1 := by
    have hid : (q : ℝ) ^ (5 / 2 : ℝ) * |π - (a : ℝ) / (q : ℝ)| =
        (q : ℝ) ^ (3 / 2 : ℝ) * |(q : ℝ) * π - (a : ℝ)| := by
      have hinner : π - (a : ℝ) / (q : ℝ) = ((q : ℝ) * π - (a : ℝ)) / (q : ℝ) := by
        field_simp
      rw [hinner, abs_div, abs_of_pos hqR]
      have hsplit : (q : ℝ) ^ (5 / 2 : ℝ) = (q : ℝ) ^ (3 / 2 : ℝ) * (q : ℝ) := by
        have : (5 / 2 : ℝ) = (3 / 2 : ℝ) + 1 := by norm_num
        rw [this, Real.rpow_add hqR, Real.rpow_one]
      rw [hsplit]
      field_simp
    rw [hid]
    calc (q : ℝ) ^ (3 / 2 : ℝ) * |(q : ℝ) * π - (a : ℝ)| ≥
        (q : ℝ) ^ (3 / 2 : ℝ) * |(q : ℝ) * π - (p : ℝ)| := by
          gcongr
      _ ≥ (q : ℝ) ^ (3 / 2 : ℝ) * |sin (p : ℝ)| := by gcongr
      _ ≥ ((4 : ℝ) ^ (-(3 / 2 : ℝ)) * (p : ℝ) ^ (3 / 2 : ℝ)) * |sin (p : ℝ)| := by
          gcongr
      _ = (4 : ℝ) ^ (-(3 / 2 : ℝ)) * ((p : ℝ) ^ (3 / 2 : ℝ) * |sin (p : ℝ)|) := by ring
      _ > (4 : ℝ) ^ (-(3 / 2 : ℝ)) * (4 : ℝ) ^ (3 / 2 : ℝ) := by
          apply mul_lt_mul_of_pos_left hp_gt
          positivity
      _ = 1 := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
          norm_num
  -- 吸收 ε：q≥1 ⇒ q^(−ε)≤1
  have hεabs : (q : ℝ) ^ (-ε) ≤ 1 := by
    have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    calc (q : ℝ) ^ (-ε) ≤ (q : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq1R (by linarith)
      _ = 1 := Real.rpow_zero _
  have hgoal : |π - (a : ℝ) / (q : ℝ)| ≥ (q : ℝ) ^ (-(5 / 2 + ε)) := by
    have h1 : |π - (a : ℝ) / (q : ℝ)| > (q : ℝ) ^ (-(5 / 2 : ℝ)) := by
      have hq52 : (0 : ℝ) < (q : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hqR _
      have hstep : (q : ℝ) ^ (-(5 / 2 : ℝ)) * (q : ℝ) ^ (5 / 2 : ℝ) <
          |π - (a : ℝ) / (q : ℝ)| * (q : ℝ) ^ (5 / 2 : ℝ) := by
        have hinv : (q : ℝ) ^ (-(5 / 2 : ℝ)) * (q : ℝ) ^ (5 / 2 : ℝ) = 1 := by
          rw [← Real.rpow_add hqR]
          norm_num
        rw [hinv, mul_comm]
        exact hmain
      exact lt_of_mul_lt_mul_right hstep (le_of_lt hq52)
    have h2 : (q : ℝ) ^ (-(5 / 2 + ε)) =
        (q : ℝ) ^ (-(5 / 2 : ℝ)) * (q : ℝ) ^ (-ε) := by
      have : -(5 / 2 + ε) = (-(5 / 2 : ℝ)) + (-ε) := by ring
      rw [this, Real.rpow_add hqR]
    rw [h2]
    calc (q : ℝ) ^ (-(5 / 2 : ℝ)) * (q : ℝ) ^ (-ε) ≤
        (q : ℝ) ^ (-(5 / 2 : ℝ)) * 1 := by
          gcongr
      _ = (q : ℝ) ^ (-(5 / 2 : ℝ)) := by ring
      _ ≤ |π - (a : ℝ) / (q : ℝ)| := le_of_lt h1
  exact hgoal

/-- ν>5/2 的好逼近对集有限（由一致下界）。 -/
lemma apprPairs_finite_of_flintHills (hconv : FlintHillsConjecture) {ν : ℝ}
    (hν : (5 / 2 : ℝ) < ν) : (apprPairs π ν).Finite := by
  have hε : 0 < ν - 5 / 2 := by linarith
  obtain ⟨N, hN⟩ := alekseyev_eventual_lower hconv (ν - 5 / 2) hε
  by_contra hinf
  have hinf' : (apprPairs π ν).Infinite := Set.not_finite.mp hinf
  obtain ⟨⟨a, q⟩, hpq, hqN⟩ := apprPairs_denom_unbounded hinf' N
  simp only [apprPairs, Set.mem_setOf_eq] at hpq
  have hq1 : 1 ≤ q := by omega
  have hlower := hN q (le_of_lt hqN) a
  have heq : (-(5 / 2 + (ν - 5 / 2)) : ℝ) = -ν := by ring
  rw [heq] at hlower
  linarith

/-- **T3 主定理（Alekseyev 方向，机器验证）**：Flint Hills 收敛 ⇒ μ(π) ≤ 5/2。
    证明：ν>5/2 ⇒ 好逼近对集有限 ⇒ apprSet ⊆ [0,5/2] ⇒ sSup ≤ 5/2。
    这是修订包更正 1 的最近整数论证，绕开分子分母障碍，无需密度论证。
    条件性：前提 FlintHillsConjecture 本身是开放问题。 -/
theorem alekseyev_bound (hconv : FlintHillsConjecture) : irrMeasure π ≤ 5 / 2 := by
  -- 第一步：ν ∈ apprSet π ⇒ ν ≤ 5/2（否则好逼近对集无穷，与有限性矛盾）
  have hle : ∀ ν ∈ apprSet π, (ν : ℝ) ≤ 5 / 2 := by
    intro ν hν
    by_contra hgt
    push Not at hgt
    have hνgt : (5 / 2 : ℝ) < (ν : ℝ) := by linarith
    have hfin : (apprPairs π (ν : ℝ)).Finite :=
      apprPairs_finite_of_flintHills hconv hνgt
    have hinf : (apprPairs π (ν : ℝ)).Infinite := by
      simpa only [apprSet, Set.mem_setOf_eq] using hν
    exact hinf hfin
  -- 第二步：sSup 上界。像集含于 [0, (5/2:ENNReal)]，故 sSup ≤ 5/2。
  simp only [irrMeasure]
  apply sSup_le
  intro a ha
  obtain ⟨ν, hν, rfl⟩ := ha
  have hνR : (ν : ℝ) ≤ 5 / 2 := hle ν hν
  have hνE : (ν : ENNReal) ≤ ((5 / 2 : NNReal) : ENNReal) := by
    exact_mod_cast hνR
  simpa using hνE