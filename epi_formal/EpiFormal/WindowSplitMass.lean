import EpiFormal.WindowMainBound

/-!
F3d：均匀分裂质量界（windows 质量论证的计数 → 质量桥）。

论文对应：paper2 §7 质量分布（L2536–2544）——父柱质量按等条件概率
均分给 retained children，每父分支数 `≫ R²`（Möbius 计数），故每原子
质量 `m0 ≤ Mpar / K`，`K ≥ R²/10000`。

本文件把分支数输入真实化为已验证的
`WindowMobiusCount.coprime_count_ge`（`R ≥ 10^6 ⇒ R²/10000 ≤ copCount R`），
得显式上界 `m0 ≤ Mpar * 10000 / R^2`。

显式纸面接口（用方 discharge）：
- `hK`：被计数的互素对单射地实现为互不相同的子柱（realize 桥）；
- `hsplit`：等条件概率均分（每原子质量 ≤ 父质量 / 分支数）。
-/

namespace WindowSplitMass

open WindowMobiusCount

/-- 均匀分裂：分支数经 coprime 计数下界化后，每原子质量的显式上界。 -/
theorem uniform_split_mass_bound
    (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R)
    (K : ℕ) (hK : ((copCount R : ℕ) : ℝ) ≤ (K : ℝ))
    (Mpar m0 : ℝ) (_hM : 0 ≤ Mpar)
    (hsplit : m0 ≤ Mpar / (K : ℝ))
    : m0 ≤ Mpar * 10000 / R ^ 2 := by
  have hcnt := coprime_count_ge R hR
  have hRp : (0 : ℝ) < R := by
    have h1M : (0 : ℝ) < (10 ^ 6 : ℝ) := by norm_num
    linarith [hR]
  have hR2 : (0 : ℝ) < R ^ 2 := pow_pos hRp 2
  have h1 : (1 : ℝ) / (K : ℝ) ≤ 10000 / R ^ 2 := by
    have hbase : (R ^ 2 / 10000 : ℝ) ≤ (K : ℝ) := le_trans hcnt hK
    have hpos : (0 : ℝ) < R ^ 2 / 10000 :=
      div_pos hR2 (by norm_num)
    have h := one_div_le_one_div_of_le hpos hbase
    rwa [one_div_div] at h
  calc m0 ≤ Mpar / (K : ℝ) := hsplit
    _ = Mpar * (1 / (K : ℝ)) := by ring
    _ ≤ Mpar * (10000 / R ^ 2) := by
        apply mul_le_mul_of_nonneg_left h1 _hM
    _ = Mpar * 10000 / R ^ 2 := by ring

end WindowSplitMass

#print axioms WindowSplitMass.uniform_split_mass_bound
