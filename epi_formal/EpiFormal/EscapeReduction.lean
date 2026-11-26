import Mathlib
import EpiFormal.EulerConvergents
import EpiFormal.AdjacentWitness
import EpiFormal.Escape
import EpiFormal.Classification

/-!
# Dj 路线归约链（EscapeReduction）

按《Dj路线攻关清单》§2 实现 D2-1 ~ D2-6：把「D_j(B)=0 eventually」归约为
「Bπ ∈ L = ℤ + ℤ(e+1)/2」。这是**换靶不是降难**（清单 D2-9）：终点 P1
（∀B≥1, Bπ∉L）的 n≠0 情形与原问题同族，仍开放。本文件不声称证明 e+π 无理性。

## 记号对齐（D1-1）
- `Escape.eps B j = Msel B j - B·Qsel j·π`（Msel = round）。
- `Classification.eps x j = Qsel j·x - nearestInt(Qsel j·x)`，nearestInt = round。
  故 `Classification.eps (Bπ) j = -Escape.eps B j`，绝对值相等。
- `distToNearestInt x = |x - round x|`，故
  `distToNearestInt (Qsel j·(Bπ)) = |Escape.eps B j|`。
- `Escape.D B j = Tsel B j + B·Csel j`，恒等式 `Escape.D_eq_eps`。

## 可信度分层
- 机器验证：D2-1（匹配超逼近界）、D2-3（尖锐界 1/8）、D2-4（最终 1/5）、
  D2-6（归约定理）。
- 依赖定理：仅 `deltaSel_tendsto_zero`、`abs_deltaSel_lt`（经 corollary3_gap）
  + Lean 基础公理。不新增公理，无 sorry。
  （2026-11-25 勘正：原文写作「公理化依赖」，易误读为项目公理；二者均为
  `EulerConvergents.lean` 中已证定理（l.516、l.540）。本机复跑
  `#print axioms Classification.corollary3_gap` 仅含 propext / Classical.choice /
  Quot.sound，见 logs/verification/LEAN-THM-0003.log。）

## 边界测试（D1-5）
本归约链的每一步对 π' = A/B - e 同样成立（通用递推 + 取整），故归约本身
不产生矛盾；矛盾只能来自 P1（Bπ∉L），而 P1 对 π' 失败（π' 使 Bπ'∈L）。
这正是清单红线：归约把缺口精确隔离到 P1，未跨过核心缺口。
-/

open Real Filter Topology Set

namespace EscapeReduction

noncomputable section

/-! ## 记号衔接 -/

/-- Classification.eps 与 Escape.eps 符号相反：`eps_cl (Bπ) j = -eps_esc B j`。 -/
lemma eps_cl_eq_neg_eps_esc (B : ℕ) (j : ℕ) :
    Classification.eps ((B : ℝ) * Real.pi) j = -Escape.eps B j := by
  simp only [Classification.eps, Escape.eps, Classification.nearestInt, AdjacentWitness.Msel]
  ring_nf

/-- 最近整数距离等于 Escape.eps 的绝对值。 -/
lemma dist_eq_abs_eps_esc (B : ℕ) (j : ℕ) :
    distToNearestInt ((Qsel j : ℝ) * ((B : ℝ) * Real.pi)) = |Escape.eps B j| := by
  have h : distToNearestInt ((Qsel j : ℝ) * ((B : ℝ) * Real.pi))
      = |Classification.eps ((B : ℝ) * Real.pi) j| := by
    simp only [distToNearestInt, Classification.eps, Classification.nearestInt]
  rw [h, eps_cl_eq_neg_eps_esc, abs_neg]

/-! ## D2-1：匹配 ⇒ 超逼近界 -/

/-- **D2-1（引理 A）**：若 D_j(B)=0，则 |ε_j(B)| ≤ (Q_j/2 + 2B)/Q_{j+1}。
    证明：D_j=0 ⇒ ε_j·Q_{j+1} = ε_{j+1}·Q_j - B·C_j，取绝对值用
    |ε_{j+1}|≤1/2、|C_j|=2。 -/
theorem match_eps_bound (B : ℕ) (j : ℕ) (hj : 1 ≤ j) (hD : Escape.D B j = 0) :
    |Escape.eps B j| ≤ ((Qsel j : ℝ) / 2 + 2 * (B : ℝ)) / (Qsel (j + 1) : ℝ) := by
  have hQpos : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by
    exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hQnn : (0 : ℝ) ≤ (Qsel j : ℝ) := by
    exact_mod_cast le_of_lt (Qsel_pos j hj)
  have hBnn : (0 : ℝ) ≤ (B : ℝ) := by positivity
  have hident := (Escape.match_iff_eps B j).mp hD
  have hC : |(AdjacentWitness.Csel j : ℝ)| = 2 := by
    have hdet := AdjacentWitness.sel_determinant j
    have hp : (-1 : ℤ) ^ (j + 1) = 1 ∨ (-1 : ℤ) ^ (j + 1) = -1 := by
      rcases Nat.even_or_odd (j + 1) with he | ho
      · left; exact he.neg_one_pow
      · right; exact ho.neg_one_pow
    rcases hp with hp | hp
    · have hc : AdjacentWitness.Csel j = 2 := by rw [hdet, hp]; norm_num
      rw [hc]; norm_num
    · have hc : AdjacentWitness.Csel j = -2 := by rw [hdet, hp]; norm_num
      rw [hc]; norm_num
  have hstep : Escape.eps B j * (Qsel (j + 1) : ℝ)
      = Escape.eps B (j + 1) * (Qsel j : ℝ) - (B : ℝ) * (AdjacentWitness.Csel j : ℝ) := by
    linarith
  have habs : |Escape.eps B j| * (Qsel (j + 1) : ℝ)
      ≤ (Qsel j : ℝ) / 2 + 2 * (B : ℝ) := by
    calc |Escape.eps B j| * (Qsel (j + 1) : ℝ)
        = |Escape.eps B j * (Qsel (j + 1) : ℝ)| := by
          rw [abs_mul, abs_of_nonneg (le_of_lt hQpos)]
      _ = |Escape.eps B (j + 1) * (Qsel j : ℝ) - (B : ℝ) * (AdjacentWitness.Csel j : ℝ)| := by
          rw [hstep]
      _ ≤ |Escape.eps B (j + 1) * (Qsel j : ℝ)| + |(B : ℝ) * (AdjacentWitness.Csel j : ℝ)| :=
          abs_sub _ _
      _ = |Escape.eps B (j + 1)| * |(Qsel j : ℝ)| + |(B : ℝ)| * |(AdjacentWitness.Csel j : ℝ)| := by
          rw [abs_mul, abs_mul]
      _ = |Escape.eps B (j + 1)| * (Qsel j : ℝ) + (B : ℝ) * |(AdjacentWitness.Csel j : ℝ)| := by
          rw [abs_of_nonneg hQnn, abs_of_nonneg hBnn]
      _ ≤ (1 / 2) * (Qsel j : ℝ) + (B : ℝ) * 2 := by
          gcongr
          · exact Escape.eps_abs_le B (j + 1)
          · exact hC.le
      _ = (Qsel j : ℝ) / 2 + 2 * (B : ℝ) := by ring
  rw [le_div_iff₀ hQpos]
  linarith [mul_comm (|Escape.eps B j|) (Qsel (j + 1) : ℝ)]

/-! ## D2-3：尖锐界（比值收敛） -/

/-- Q_{j-1}/Q_j → 0。由递推 Q_{j+1} ≥ (4j+2)Q_j 得
    Q_{j-1}/Q_j ≤ 1/(4j-2)（j≥2）→ 0，夹逼。 -/
lemma Qsel_pred_div_tendsto_zero :
    Tendsto (fun j : ℕ => (Qsel (j - 1) : ℝ) / (Qsel j : ℝ)) atTop (nhds 0) := by
  have hbound : ∀ᶠ j : ℕ in atTop,
      (Qsel (j - 1) : ℝ) / (Qsel j : ℝ) ≤ 1 / (4 * (j : ℝ) - 2) := by
    apply Filter.eventually_atTop.mpr
    use 3
    intro j hj
    have hj3 : 3 ≤ j := hj
    have hj2 : 2 ≤ j := by omega
    -- Qsel j = (4(j-1)+2) Qsel(j-1) + Qsel(j-2)，用 Qsel_rec (j-1)
    have hrec := Qsel_rec (j - 1) (by omega)
    -- hrec : Qsel (j-1+1) = (4*(j-1)+2)*Qsel(j-1) + Qsel(j-1-1)
    have hjp : j - 1 + 1 = j := by omega
    have hjm : j - 1 - 1 = j - 2 := by omega
    rw [hjp, hjm] at hrec
    have hcoef : (4 * ((j - 1 : ℕ) : ℤ) + 2) = 4 * (j : ℤ) - 2 := by
      omega
    have hge : (4 * (j : ℤ) - 2) * Qsel (j - 1) ≤ Qsel j := by
      rw [hrec, hcoef]
      have hnn : 0 ≤ Qsel (j - 2) := by
        have : 1 ≤ j - 2 := by omega
        exact le_of_lt (Qsel_pos (j - 2) this)
      linarith
    have hQpos : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j (by omega)
    have hcoefpos : (0 : ℝ) < 4 * (j : ℝ) - 2 := by
      have : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3
      linarith
    have hgeR : (4 * (j : ℝ) - 2) * (Qsel (j - 1) : ℝ) ≤ (Qsel j : ℝ) := by
      exact_mod_cast hge
    rw [div_le_div_iff₀ hQpos hcoefpos]
    linarith
  have hnonneg : ∀ᶠ j : ℕ in atTop,
      0 ≤ (Qsel (j - 1) : ℝ) / (Qsel j : ℝ) := by
    apply Filter.eventually_atTop.mpr
    use 2
    intro j hj
    apply div_nonneg
    · exact_mod_cast le_of_lt (Qsel_pos (j - 1) (by omega))
    · exact_mod_cast le_of_lt (Qsel_pos j (by omega))
  have hupper : Tendsto (fun j : ℕ => 1 / (4 * (j : ℝ) - 2)) atTop (nhds 0) := by
    have hden : Tendsto (fun j : ℕ => 4 * (j : ℝ) - 2) atTop atTop := by
      have hnat : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop (R := ℝ)
      have h4 : Tendsto (fun j : ℕ => (4 : ℝ) * (j : ℝ)) atTop atTop :=
        hnat.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
      have := tendsto_atTop_add_const_right atTop (-2 : ℝ) h4
      convert this using 1
    exact tendsto_const_nhds.div_atTop hden
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper hnonneg hbound

/-- j·Q_j/Q_{j+1} → 1/4。由 Q_{j+1} = (4j+2)Q_j + Q_{j-1}，
    j·Q_j/Q_{j+1} = 1/(4 + 2/j + Q_{j-1}/(j·Q_j)) → 1/4。 -/
lemma jQsel_div_Qsel_succ_tendsto :
    Tendsto (fun j : ℕ => (j : ℝ) * (Qsel j : ℝ) / (Qsel (j + 1) : ℝ)) atTop (nhds (1 / 4)) := by
  have heq : ∀ᶠ j : ℕ in atTop,
      (j : ℝ) * (Qsel j : ℝ) / (Qsel (j + 1) : ℝ)
        = 1 / (4 + 2 / (j : ℝ) + (Qsel (j - 1) : ℝ) / ((j : ℝ) * (Qsel j : ℝ))) := by
    apply Filter.eventually_atTop.mpr
    use 2
    intro j hj
    have hj2 : 2 ≤ j := hj
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hQpos : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j (by omega)
    have hQ1pos : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by
      exact_mod_cast Qsel_pos (j + 1) (by omega)
    have hrec := Qsel_rec j hj2
    have hrecR : (Qsel (j + 1) : ℝ)
        = (4 * (j : ℝ) + 2) * (Qsel j : ℝ) + (Qsel (j - 1) : ℝ) := by exact_mod_cast hrec
    have hden : (4 + 2 / (j : ℝ) + (Qsel (j - 1) : ℝ) / ((j : ℝ) * (Qsel j : ℝ)))
        = (Qsel (j + 1) : ℝ) / ((j : ℝ) * (Qsel j : ℝ)) := by
      field_simp
      linarith
    rw [hden]
    field_simp
  have hpred : Tendsto (fun j : ℕ => (Qsel (j - 1) : ℝ) / ((j : ℝ) * (Qsel j : ℝ)))
      atTop (nhds 0) := by
    have hle : ∀ᶠ j : ℕ in atTop,
        (Qsel (j - 1) : ℝ) / ((j : ℝ) * (Qsel j : ℝ))
          ≤ (Qsel (j - 1) : ℝ) / (Qsel j : ℝ) := by
      apply Filter.eventually_atTop.mpr
      use 2
      intro j hj
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1 ≤ j)
      have hQpos : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j (by omega)
      have hQprednn : (0 : ℝ) ≤ (Qsel (j - 1) : ℝ) := by
        exact_mod_cast le_of_lt (Qsel_pos (j - 1) (by omega))
      apply div_le_div_of_nonneg_left hQprednn hQpos
      have hjQ : (Qsel j : ℝ) ≤ (j : ℝ) * (Qsel j : ℝ) := by
        nlinarith
      exact hjQ
    have hnn : ∀ᶠ j : ℕ in atTop,
        0 ≤ (Qsel (j - 1) : ℝ) / ((j : ℝ) * (Qsel j : ℝ)) := by
      apply Filter.eventually_atTop.mpr
      use 2
      intro j hj
      apply div_nonneg
      · exact_mod_cast le_of_lt (Qsel_pos (j - 1) (by omega))
      · exact mul_nonneg (by positivity) (by exact_mod_cast le_of_lt (Qsel_pos j (by omega)))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      Qsel_pred_div_tendsto_zero hnn hle
  have hden : Tendsto (fun j : ℕ =>
      4 + 2 / (j : ℝ) + (Qsel (j - 1) : ℝ) / ((j : ℝ) * (Qsel j : ℝ))) atTop (nhds 4) := by
    have hnat : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop (R := ℝ)
    have h2j : Tendsto (fun j : ℕ => 2 / (j : ℝ)) atTop (nhds 0) := hnat.const_div_atTop 2
    have hsum : Tendsto (fun j : ℕ => (4 : ℝ) + (2 / (j : ℝ) +
        (Qsel (j - 1) : ℝ) / ((j : ℝ) * (Qsel j : ℝ)))) atTop (nhds (4 + (0 + 0))) :=
      tendsto_const_nhds.add (h2j.add hpred)
    convert hsum using 1 <;> ring
  have hdiv : Tendsto (fun j : ℕ =>
      1 / (4 + 2 / (j : ℝ) + (Qsel (j - 1) : ℝ) / ((j : ℝ) * (Qsel j : ℝ)))) atTop (nhds (1 / 4)) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have := hconst.div hden (by norm_num : (4 : ℝ) ≠ 0)
    convert this using 1
  exact hdiv.congr' (heq.mono (fun j hj => hj.symm))

/-- j/Q_{j+1} → 0。由 Q_{j+1} ≥ (4j+2)Q_j ≥ (4j+2)j。 -/
lemma j_div_Qsel_succ_tendsto_zero :
    Tendsto (fun j : ℕ => (j : ℝ) / (Qsel (j + 1) : ℝ)) atTop (nhds 0) := by
  have hle : ∀ᶠ j : ℕ in atTop,
      (j : ℝ) / (Qsel (j + 1) : ℝ) ≤ 1 / (4 * (j : ℝ) + 2) := by
    apply Filter.eventually_atTop.mpr
    use 2
    intro j hj
    have hj2 : 2 ≤ j := hj
    have hrec := Qsel_rec j hj2
    have hge : (4 * (j : ℤ) + 2) * Qsel j ≤ Qsel (j + 1) := by
      rw [hrec]
      have hnn : 0 ≤ Qsel (j - 1) := by
        have : 1 ≤ j - 1 := by omega
        exact le_of_lt (Qsel_pos (j - 1) this)
      linarith
    have hQj : (j : ℤ) ≤ Qsel j := by
      have hge := Qsel_ge_index (j - 1)
      have hjp : j - 1 + 1 = j := by omega
      have hge' : (j : ℤ) ≤ Qsel j := by
        convert hge using 1
        · omega
        · rw [hjp]
      exact hge'
    have hQpos : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by
      exact_mod_cast Qsel_pos (j + 1) (by omega)
    have hcoefpos : (0 : ℝ) < 4 * (j : ℝ) + 2 := by positivity
    have hgeR : (4 * (j : ℝ) + 2) * (Qsel j : ℝ) ≤ (Qsel (j + 1) : ℝ) := by
      exact_mod_cast hge
    have hjQj : (j : ℝ) ≤ (Qsel j : ℝ) := by exact_mod_cast hQj
    rw [div_le_div_iff₀ hQpos hcoefpos]
    nlinarith
  have hnn : ∀ᶠ j : ℕ in atTop, 0 ≤ (j : ℝ) / (Qsel (j + 1) : ℝ) := by
    apply Filter.eventually_atTop.mpr
    use 0
    intro j _
    apply div_nonneg
    · positivity
    · exact_mod_cast le_of_lt (Qsel_pos (j + 1) (by omega))
  have hupper : Tendsto (fun j : ℕ => 1 / (4 * (j : ℝ) + 2)) atTop (nhds 0) := by
    have hden : Tendsto (fun j : ℕ => 4 * (j : ℝ) + 2) atTop atTop := by
      have hnat : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop (R := ℝ)
      have h4 : Tendsto (fun j : ℕ => (4 : ℝ) * (j : ℝ)) atTop atTop :=
        hnat.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
      apply tendsto_atTop_mono' _ _ h4
      apply Eventually.of_forall
      intro j
      linarith
    exact tendsto_const_nhds.div_atTop hden
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper hnn hle

/-- **D2-3（尖锐界）**：j·(Q_j/2+2B)/Q_{j+1} → 1/8。 -/
theorem sharp_bound_tendsto (B : ℕ) :
    Tendsto (fun j : ℕ => (j : ℝ) * ((Qsel j : ℝ) / 2 + 2 * (B : ℝ)) / (Qsel (j + 1) : ℝ))
      atTop (nhds (1 / 8)) := by
  have heq : (fun j : ℕ => (j : ℝ) * ((Qsel j : ℝ) / 2 + 2 * (B : ℝ)) / (Qsel (j + 1) : ℝ))
      = (fun j : ℕ => (1 / 2) * ((j : ℝ) * (Qsel j : ℝ) / (Qsel (j + 1) : ℝ))
          + 2 * (B : ℝ) * ((j : ℝ) / (Qsel (j + 1) : ℝ))) := by
    funext j
    have hQ1pos : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by
      exact_mod_cast Qsel_pos (j + 1) (by omega)
    field_simp
  rw [heq]
  have h1 : Tendsto (fun j : ℕ => (1 / 2) * ((j : ℝ) * (Qsel j : ℝ) / (Qsel (j + 1) : ℝ)))
      atTop (nhds ((1 / 2) * (1 / 4))) :=
    jQsel_div_Qsel_succ_tendsto.const_mul (1 / 2)
  have h2 : Tendsto (fun j : ℕ => 2 * (B : ℝ) * ((j : ℝ) / (Qsel (j + 1) : ℝ)))
      atTop (nhds (2 * (B : ℝ) * 0)) :=
    j_div_Qsel_succ_tendsto_zero.const_mul (2 * (B : ℝ))
  have hsum := h1.add h2
  have hlim : (1 / 2 : ℝ) * (1 / 4) + 2 * (B : ℝ) * 0 = 1 / 8 := by ring
  rw [hlim] at hsum
  exact hsum

/-- **D2-3 推论**：存在 J_0(B)，j≥J_0 时 j·(Q_j/2+2B)/Q_{j+1} ≤ 1/5。 -/
theorem sharp_bound_eventually (B : ℕ) :
    ∀ᶠ j : ℕ in atTop,
      (j : ℝ) * ((Qsel j : ℝ) / 2 + 2 * (B : ℝ)) / (Qsel (j + 1) : ℝ) ≤ 1 / 5 := by
  have h := sharp_bound_tendsto B
  have hlt : (1 / 8 : ℝ) < 1 / 5 := by norm_num
  exact (h.eventually (Iio_mem_nhds hlt)).mono (fun j hj => le_of_lt hj)

/-! ## D2-4：匹配 eventually ⇒ j·‖BQ_jπ‖ ≤ 1/5 eventually -/

/-- **D2-4（引理 C）**：若 D_j(B)=0 eventually，则 j·‖BQ_jπ‖ ≤ 1/5 eventually。 -/
theorem match_eventually_eps_le_fifth (B : ℕ)
    (hD : ∀ᶠ j : ℕ in atTop, Escape.D B j = 0) :
    ∀ᶠ j : ℕ in atTop,
      (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * ((B : ℝ) * Real.pi)) ≤ 1 / 5 := by
  have hJ0 := sharp_bound_eventually B
  have hge1 : ∀ᶠ j : ℕ in atTop, 1 ≤ j := Filter.eventually_ge_atTop 1
  apply (hD.and (hJ0.and hge1)).mono
  intro j hj
  obtain ⟨hDj, hJ0j, hj1⟩ := hj
  have hbound := match_eps_bound B j hj1 hDj
  have hjpos : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hmul : (j : ℝ) * |Escape.eps B j|
      ≤ (j : ℝ) * ((Qsel j : ℝ) / 2 + 2 * (B : ℝ)) / (Qsel (j + 1) : ℝ) := by
    calc (j : ℝ) * |Escape.eps B j|
        ≤ (j : ℝ) * (((Qsel j : ℝ) / 2 + 2 * (B : ℝ)) / (Qsel (j + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound hjpos
      _ = (j : ℝ) * ((Qsel j : ℝ) / 2 + 2 * (B : ℝ)) / (Qsel (j + 1) : ℝ) := by ring
  rw [dist_eq_abs_eps_esc]
  linarith

/-! ## D2-6：归约定理 -/

/-- **D2-6（归约定理）**：若 D_j(B)=0 eventually，则 Bπ ∈ L。
    证明：D2-4 给 j·‖Q_j·Bπ‖ ≤ 1/5 eventually，与 corollary3_gap（c=1/5<1/4）
    对撞（取 x = Bπ）。这是换靶不是降难：P1（Bπ∉L）仍开放。 -/
theorem reduction_to_lattice (B : ℕ)
    (hD : ∀ᶠ j : ℕ in atTop, Escape.D B j = 0) :
    (B : ℝ) * Real.pi ∈ Classification.latticeL := by
  by_contra hnot
  have hgap := Classification.corollary3_gap ((B : ℝ) * Real.pi) hnot (1 / 5) (by norm_num)
  have hle := match_eventually_eps_le_fifth B hD
  exact hgap hle

/-- **P1（归约终点，开放）**：∀B≥1, Bπ ∉ L。本文件不证明 P1；
    其 n≠0 情形与原问题同族（清单 D2-9），仍开放。 -/
def P1 : Prop := ∀ B : ℕ, 1 ≤ B → (B : ℝ) * Real.pi ∉ Classification.latticeL

/-- **D2-6 等价形式（条件结果）**：P1 ⇒ e+π 无理。
    证明：若 e+π 有理，则某 B≥1 使 B(e+π)∈ℤ，由三等价 D_j(B)=0 eventually，
    由 reduction_to_lattice 得 Bπ∈L，与 P1 矛盾。
    **前提 P1 开放**，故本定理是条件结果，不声称解决 e+π 无理性。 -/
theorem P1_imp_irrational (hP1 : P1) : Irrational (Real.exp 1 + Real.pi) := by
  rw [Escape.irrational_iff_inf_mismatch]
  intro B hB
  by_contra hnot
  have hinf : ∀ N : ℕ, ∃ j ≥ N, Escape.D B j = 0 := by
    rw [Filter.eventually_atTop] at hnot
    push Not at hnot
    exact hnot
  have ha : ∃ A : ℤ, (B : ℝ) * (Real.exp 1 + Real.pi) = (A : ℝ) :=
    AdjacentWitness.theorem11_converse (by
      intro N
      obtain ⟨j, hj, hjz⟩ := hinf N
      refine ⟨j, hj, ?_⟩
      simp only [Escape.D] at hjz
      linarith)
  have hev : ∀ᶠ j : ℕ in atTop, Escape.D B j = 0 := by
    have hb := AdjacentWitness.theorem11_forward ha
    apply hb.mono
    intro j hj
    simp only [Escape.D]
    linarith
  have hL := reduction_to_lattice B hev
  exact hP1 B hB hL

end

end EscapeReduction

/-! ## 公理审计 -/

#print axioms EscapeReduction.match_eps_bound
#print axioms EscapeReduction.Qsel_pred_div_tendsto_zero
#print axioms EscapeReduction.jQsel_div_Qsel_succ_tendsto
#print axioms EscapeReduction.sharp_bound_tendsto
#print axioms EscapeReduction.match_eventually_eps_le_fifth
#print axioms EscapeReduction.reduction_to_lattice
#print axioms EscapeReduction.P1_imp_irrational