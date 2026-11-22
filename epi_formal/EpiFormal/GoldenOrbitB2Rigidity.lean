import Mathlib
import EpiFormal.GoldenOrbitRigidity

/-!
# 有理端点 $\mathbb{Z}[\varphi]$ 范数同余刚性、Pell 谱隙与 $B=2$ 对照模型精确值定理

本模块无条件形式化论文一 §8 中关于一般有理端点 $(u,v) = (p_1/q_1, p_2/q_2)$ 范数同余刚性、
$\mathbb{Z}[\varphi]$ 模 $5$ 分歧判据、以及 $B=2$ 对照模型 $x = \frac{11}{2} - e$（周期 10 Hurwitz 块
$(2, k, 2, 1, 1, 1, k, 1, 1, 1)$）的精确值定理（`thm:golden-b2-exact`）与配对刚性引理（`lem:pell-b2-rigidity`）
的核心代数骨架（零 `sorry`，仅依赖 Lean 基础公理）：

1. **一般有理端点 $(u,v) = (p_1/q_1, p_2/q_2)$ 的线性-范数恒等式**：
   - `xi1_mul_xi2Conj`：$2 \xi_1 \xi_2' = M_{u,v} - (ad-bc)(p_1 q_2 + p_2 q_1)\sqrt{5}$；
   - `M_uv_norm_identity`：$M_{u,v}^2 - 5(ad-bc)^2 (p_1 q_2 + p_2 q_1)^2 = 4 N(\xi_1) N(\xi_2)$；
   - `rational_endpoint_rigidity_identity`：对任意 $|ad-bc|=1$ 与 $q_1,q_2 > 0, D = p_1 q_2 + p_2 q_1 > 0$，
     $$h(\eta)\frac{|p_1/q_1 - \eta|\,|\eta' + p_2/q_2|}{p_1/q_1 + p_2/q_2}
       = \left|\frac{(ad-bc)M_{u,v}}{D\sqrt{5}} - 1\right|.$$
2. **$\mathbb{Z}[\varphi]$ 范数模 $5$ 完全分歧恒等式**：
   - `zphiNorm_mod5_identity`：$-p^2 + pq + q^2 = -(p + 2q)^2 + 5(p + q)q$；
   - `five_dvd_zphiNorm_iff`：$5 \mid N(p\varphi+q) \iff 5 \mid (p + 2q)$。
3. **$B=2$ 周期 10 模型的 $D=8$ Pell-范数同余刚性引理（`lem:pell-b2-rigidity`）**：
   - `m8q_mod4_identity`：$m_{8,q_1}(a,b,c,d) + q_1 N(a\varphi+b) = 4(-2ac + 2bd + ad + bc)$；
   - `m85_odd` 与 `m83_odd`：当 $|ad-bc|=1$ 时，$m_{8,5}$ 与 $m_{8,3}$ 必为奇数；
   - `pell_b2_spectral_gap`：基于 Pell 基本解 $9^2 - 5\cdot 4^2 = 1$（$4\sqrt{5} = \sqrt{80} < 9$），
     证明 $0 < \frac{9}{4\sqrt{5}} - 1 < 1 - \frac{2}{\sqrt{5}} < 1 - \frac{7}{4\sqrt{5}} < \frac{11}{4\sqrt{5}} - 1$，
     对一切整数 $m \ne 9$ 有 $\left|\frac{m}{4\sqrt{5}}-1\right| \ge 1 - \frac{2}{\sqrt{5}}$，且对一切**奇整数**
     $m \ne 9$ 有 $\left|\frac{m}{4\sqrt{5}}-1\right| \ge 1 - \frac{7}{4\sqrt{5}}$；
   - `phi85_eq_min_iff` 与 `phi85_ge_second`：
     $h(\eta)\frac{|8/5-\eta|\,|\eta'|}{8/5} = \frac{9}{4\sqrt{5}}-1 \iff \eta = \varphi$，且对一切 $\eta \ne \varphi$
     恒有 $h(\eta)\frac{|8/5-\eta|\,|\eta'|}{8/5} \ge 1 - \frac{7}{4\sqrt{5}}$；
   - `phi83_eq_min_iff` 与 `phi83_ge_second`：
     $h(\eta)\frac{|8/3-\eta|\,|\eta'|}{8/3} = \frac{9}{4\sqrt{5}}-1 \iff \eta = \varphi + 1$，且对一切 $\eta \ne \varphi + 1$
     恒有 $h(\eta)\frac{|8/3-\eta|\,|\eta'|}{8/3} \ge 1 - \frac{7}{4\sqrt{5}}$；
   - `phi85_second_attained` 与 `phi83_second_attained`：次小值 $1 - \frac{7}{4\sqrt{5}}$ 分别由
     $\eta = \varphi + 1$（在 $8/5$ 处）与 $\eta = \varphi$（在 $8/3$ 处）精确取到。
4. **定理 `thm:golden-b2-exact` 的分歧位置一致下界与凹二次函数下界**：
   - `b2_case1_85_lower_bound` 与 `b2_case1_83_lower_bound`：周期 10 有界块内的分歧一致下界；
   - `b2_case2_sk_sub1_endpoint`、`b2_case2_tk_sub1_quadratic_ge`、`b2_case2_sk_sub1_quadratic_ge`：
     大商位置 $m = s_k, t_k$ 处的精确端点与凹二次下界。

公理审计：本模块仅依赖 Lean 基础公理 `[propext, Classical.choice, Quot.sound]`。
-/

namespace GoldenOrbitB2Rigidity

open Real GoldenOrbitRigidity

/-! ### 1. 一般有理端点 $(u,v) = (p_1/q_1, p_2/q_2)$ 的线性-范数恒等式 -/

/-- 一般有理端点 $(p_1/q_1, p_2/q_2)$ 处 $2\xi_1\xi_2'$ 的整数有理部 $M_{u,v}$。 -/
def M_uv (p1 q1 p2 q2 a b c d : ℤ) : ℤ :=
  2 * a ^ 2 * q1 * q2 - 2 * a * b * q1 * q2 - 2 * a * c * p1 * q2 + 2 * a * c * p2 * q1 +
    a * d * p1 * q2 - a * d * p2 * q1 - 2 * b ^ 2 * q1 * q2 + b * c * p1 * q2 -
    b * c * p2 * q1 + 2 * b * d * p1 * q2 - 2 * b * d * p2 * q1 - 2 * c ^ 2 * p1 * p2 +
    2 * c * d * p1 * p2 + 2 * d ^ 2 * p1 * p2

/-- 一般有理端点共轭乘积展开：
    $2((p_1 c - q_1 a)\varphi + (p_1 d - q_1 b))((q_2 a + p_2 c)\varphi' + (q_2 b + p_2 d))
     = M_{u,v} - (ad-bc)(p_1 q_2 + p_2 q_1)\sqrt{5}$。 -/
theorem xi1_mul_xi2Conj (p1 q1 p2 q2 a b c d : ℤ) :
    2 * ((((p1 * c - q1 * a : ℤ) : ℝ) * φ + ((p1 * d - q1 * b : ℤ) : ℝ)) *
      (((q2 * a + p2 * c : ℤ) : ℝ) * φ' + ((q2 * b + p2 * d : ℤ) : ℝ))) =
    (M_uv p1 q1 p2 q2 a b c d : ℝ) -
      ((a * d - b * c : ℤ) : ℝ) * ((p1 * q2 + p2 * q1 : ℤ) : ℝ) * Real.sqrt 5 := by
  unfold M_uv φ φ'
  push_cast
  linear_combination
    (-(((p1 : ℝ) * (c : ℝ) - (q1 : ℝ) * (a : ℝ)) *
      ((q2 : ℝ) * (a : ℝ) + (p2 : ℝ) * (c : ℝ))) / 2) * sqrt5_sq

/-- 一般有理端点范数恒等式：
    $M_{u,v}^2 - 5(ad-bc)^2(p_1 q_2 + p_2 q_1)^2 = 4 N(\xi_1) N(\xi_2)$。 -/
theorem M_uv_norm_identity (p1 q1 p2 q2 a b c d : ℤ) :
    (M_uv p1 q1 p2 q2 a b c d) ^ 2 - 5 * (a * d - b * c) ^ 2 * (p1 * q2 + p2 * q1) ^ 2 =
      4 * zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b) *
        zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d) := by
  unfold M_uv zphiNorm
  ring

/-- 一般有理端点 $(u,v) = (p_1/q_1, p_2/q_2)$ 的精确刚性公式：
    对任意 $|ad-bc|=1$ 且 $q_1, q_2 > 0, D = p_1 q_2 + p_2 q_1 > 0$，
    $h(\eta)\frac{|p_1/q_1 - \eta|\,|\eta' + p_2/q_2|}{p_1/q_1 + p_2/q_2}
     = \left|\frac{(ad-bc)M_{u,v}}{(p_1 q_2 + p_2 q_1)\sqrt{5}} - 1\right|$。 -/
theorem rational_endpoint_rigidity_identity (p1 q1 p2 q2 a b c d : ℤ)
    (hdet : |a * d - b * c| = 1)
    (hq1 : (0 : ℝ) < (q1 : ℝ)) (hq2 : (0 : ℝ) < (q2 : ℝ))
    (hD : (0 : ℝ) < ((p1 * q2 + p2 * q1 : ℤ) : ℝ)) :
    orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
      (|(p1 : ℝ) / (q1 : ℝ) - orbitPt a b c d| *
        |orbitPtConj a b c d + (p2 : ℝ) / (q2 : ℝ)| /
        ((p1 : ℝ) / (q1 : ℝ) + (p2 : ℝ) / (q2 : ℝ))) =
    |(((a * d - b * c) * M_uv p1 q1 p2 q2 a b c d : ℤ) : ℝ) /
      (((p1 * q2 + p2 * q1 : ℤ) : ℝ) * Real.sqrt 5) - 1| := by
  have hcd := linear_phi_ne_zero (cd_ne_zero_of_det hdet)
  have hq1_ne : (q1 : ℝ) ≠ 0 := ne_of_gt hq1
  have hq2_ne : (q2 : ℝ) ≠ 0 := ne_of_gt hq2
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  have hD_ne : ((p1 * q2 + p2 * q1 : ℤ) : ℝ) ≠ 0 := ne_of_gt hD
  have hsub1 : (p1 : ℝ) / (q1 : ℝ) - orbitPt a b c d =
      (((p1 * c - q1 * a : ℤ) : ℝ) * φ + ((p1 * d - q1 * b : ℤ) : ℝ)) /
        ((q1 : ℝ) * ((c : ℝ) * φ + (d : ℝ))) := by
    unfold orbitPt mobius
    rw [div_sub_div _ _ hq1_ne hcd.1]
    push_cast; ring
  have hadd2 : orbitPtConj a b c d + (p2 : ℝ) / (q2 : ℝ) =
      (((q2 * a + p2 * c : ℤ) : ℝ) * φ' + ((q2 * b + p2 * d : ℤ) : ℝ)) /
        ((q2 : ℝ) * ((c : ℝ) * φ' + (d : ℝ))) := by
    unfold orbitPtConj mobius
    rw [div_add_div _ _ hcd.2 hq2_ne]
    push_cast; ring
  have hsum : (p1 : ℝ) / (q1 : ℝ) + (p2 : ℝ) / (q2 : ℝ) =
      ((p1 * q2 + p2 * q1 : ℤ) : ℝ) / ((q1 : ℝ) * (q2 : ℝ)) := by
    rw [div_add_div _ _ hq1_ne hq2_ne]
    push_cast; ring
  rw [orbitHeight_eq hdet, hsub1, hadd2, hsum]
  rw [abs_div, abs_div, abs_mul, abs_mul, abs_of_pos hq1, abs_of_pos hq2,
    ← zphi_mul_conj c d, abs_mul]
  have h1_ne : |(c : ℝ) * φ + (d : ℝ)| ≠ 0 := abs_ne_zero.mpr hcd.1
  have h2_ne : |(c : ℝ) * φ' + (d : ℝ)| ≠ 0 := abs_ne_zero.mpr hcd.2
  set ξ1 : ℝ := ((p1 * c - q1 * a : ℤ) : ℝ) * φ + ((p1 * d - q1 * b : ℤ) : ℝ)
  set ξ2' : ℝ := ((q2 * a + p2 * c : ℤ) : ℝ) * φ' + ((q2 * b + p2 * d : ℤ) : ℝ)
  set D : ℝ := ((p1 * q2 + p2 * q1 : ℤ) : ℝ)
  have hcancel_lhs :
      2 * (|(c : ℝ) * φ + (d : ℝ)| * |(c : ℝ) * φ' + (d : ℝ)|) / Real.sqrt 5 *
        (|ξ1| / ((q1 : ℝ) * |(c : ℝ) * φ + (d : ℝ)|) *
          (|ξ2'| / ((q2 : ℝ) * |(c : ℝ) * φ' + (d : ℝ)|)) /
          (D / ((q1 : ℝ) * (q2 : ℝ)))) =
      |2 * (ξ1 * ξ2')| / (D * Real.sqrt 5) := by
    have h2abs : |2 * (ξ1 * ξ2')| = 2 * (|ξ1| * |ξ2'|) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [h2abs]
    field_simp [h1_ne, h2_ne, hq1_ne, hq2_ne, h5_ne, hD_ne]
  have hxi : 2 * (ξ1 * ξ2') =
      (M_uv p1 q1 p2 q2 a b c d : ℝ) - ((a * d - b * c : ℤ) : ℝ) * D * Real.sqrt 5 :=
    xi1_mul_xi2Conj p1 q1 p2 q2 a b c d
  rw [hcancel_lhs, hxi]
  have hε : a * d - b * c = 1 ∨ a * d - b * c = -1 :=
    (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
  have hD5_pos : 0 < D * Real.sqrt 5 := mul_pos hD h5_pos
  have hD5_ne : D * Real.sqrt 5 ≠ 0 := ne_of_gt hD5_pos
  rcases hε with h1 | hm1
  · rw [h1]; push_cast; rw [one_mul, one_mul]
    rw [show |(M_uv p1 q1 p2 q2 a b c d : ℝ) - D * Real.sqrt 5| / (D * Real.sqrt 5) =
        |((M_uv p1 q1 p2 q2 a b c d : ℝ) - D * Real.sqrt 5) / (D * Real.sqrt 5)| by
      rw [abs_div, abs_of_pos hD5_pos]]
    congr 1; field_simp [hD5_ne]
  · rw [hm1]; push_cast
    rw [show |(M_uv p1 q1 p2 q2 a b c d : ℝ) - (-1 : ℝ) * D * Real.sqrt 5| / (D * Real.sqrt 5) =
        |((M_uv p1 q1 p2 q2 a b c d : ℝ) - (-1 : ℝ) * D * Real.sqrt 5) / (D * Real.sqrt 5)| by
      rw [abs_div, abs_of_pos hD5_pos]]
    rw [← abs_neg ((-1 * (M_uv p1 q1 p2 q2 a b c d : ℝ)) / (D * Real.sqrt 5) - 1)]
    congr 1; field_simp [hD5_ne]; ring

/-! ### 2. $\mathbb{Z}[\varphi]$ 范数模 $5$ 完全分歧恒等式 -/

/-- $\mathbb{Z}[\varphi]$ 范数模 $5$ 分歧配方恒等式：
    $N(p\varphi+q) = -p^2 + pq + q^2 = -(p + 2q)^2 + 5(p + q)q$。 -/
theorem zphiNorm_mod5_identity (p q : ℤ) :
    zphiNorm p q = -(p + 2 * q) ^ 2 + 5 * (p + q) * q := by
  unfold zphiNorm; ring

/-- $(5) = (\sqrt{5})^2$ 在 $\mathbb{Z}[\varphi]$ 中完全分歧：
    $5 \mid N(p\varphi+q) \iff 5 \mid (p + 2q)$。 -/
theorem five_dvd_zphiNorm_iff (p q : ℤ) :
    (5 : ℤ) ∣ zphiNorm p q ↔ (5 : ℤ) ∣ (p + 2 * q) := by
  rw [zphiNorm_mod5_identity]
  constructor
  · rintro ⟨k, hk⟩
    set x := p + 2 * q
    have hx_decomp : x = 5 * (x / 5) + x % 5 := by omega
    set r := x % 5
    set qx := x / 5
    have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
    have hsq : x ^ 2 = 5 * (5 * qx ^ 2 + 2 * qx * r) + r ^ 2 := by
      rw [hx_decomp]; ring
    have hdiv5 : x ^ 2 = 5 * ((p + q) * q - k) := by linarith
    rcases hr with h0 | h1 | h2 | h3 | h4
    · exact ⟨qx, by omega⟩
    · rw [h1] at hsq; omega
    · rw [h2] at hsq; omega
    · rw [h3] at hsq; omega
    · rw [h4] at hsq; omega
  · rintro ⟨k, hk⟩
    refine ⟨-5 * k ^ 2 + (p + q) * q, ?_⟩
    rw [hk]; ring

/-! ### 3. $B=2$ 对照模型（$D=8$）的 Pell-范数同余刚性引理（`lem:pell-b2-rigidity`） -/

/-- 端点 $(8/q_1, 0)$ 处的整数有理部 $m_{8,q_1}(a,b,c,d)$（对应 $M_{8,q_1,0,1}/2$）。 -/
def m8q (q1 a b c d : ℤ) : ℤ :=
  q1 * a ^ 2 - q1 * a * b - 8 * a * c + 4 * a * d - q1 * b ^ 2 + 4 * b * c + 8 * b * d

/-- 模 $4$ 同余分解恒等式：
    $m_{8,q_1}(a,b,c,d) + q_1 N(a\varphi+b) = 4(-2ac + 2bd + ad + bc)$。 -/
theorem m8q_mod4_identity (q1 a b c d : ℤ) :
    m8q q1 a b c d + q1 * zphiNorm a b = 4 * (-2 * a * c + 2 * b * d + a * d + b * c) := by
  unfold m8q zphiNorm; ring

/-- 共轭乘积展开：
    $((8c - q_1 a)\varphi + (8d - q_1 b))(a\varphi' + b) = m_{8,q_1}(a,b,c,d) - 4(ad-bc)\sqrt{5}$。 -/
theorem alpha8q_mul_gammaConj (q1 a b c d : ℤ) :
    (((8 * c - q1 * a : ℤ) : ℝ) * φ + ((8 * d - q1 * b : ℤ) : ℝ)) *
      ((a : ℝ) * φ' + (b : ℝ)) =
    (m8q q1 a b c d : ℝ) - 4 * ((a * d - b * c : ℤ) : ℝ) * Real.sqrt 5 := by
  unfold m8q φ φ'
  push_cast
  linear_combination (-((8 * (c : ℝ) - (q1 : ℝ) * (a : ℝ)) * (a : ℝ)) / 4) * sqrt5_sq

/-- 范数恒等式：
    $m_{8,q_1}^2 - 80(ad-bc)^2 = N((8c - q_1 a)\varphi + (8d - q_1 b)) \cdot N(a\varphi+b)$。 -/
theorem m8q_norm_identity (q1 a b c d : ℤ) :
    (m8q q1 a b c d) ^ 2 - 80 * (a * d - b * c) ^ 2 =
      zphiNorm (8 * c - q1 * a) (8 * d - q1 * b) * zphiNorm a b := by
  unfold m8q zphiNorm; ring

/-- 当 $q_1$ 为奇数且 $|ad-bc|=1$ 时，$m_{8,q_1}(a,b,c,d)$ 必为奇数。 -/
theorem m8q_odd {q1 a b c d : ℤ} (hq1 : Odd q1) (hdet : |a * d - b * c| = 1) :
    Odd (m8q q1 a b c d) := by
  have hnot_ab : ¬ (Even a ∧ Even b) := by
    rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩
    have hmul : (a' + a') * d - (b' + b') * c = 2 * (a' * d - b' * c) := by ring
    rw [hmul] at hdet
    have : (2 * (a' * d - b' * c)) = 1 ∨ (2 * (a' * d - b' * c)) = -1 :=
      (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
    omega
  have hN_not_even : ¬ Even (zphiNorm a b) := by rwa [zphiNorm_even_iff]
  have hN_odd : Odd (zphiNorm a b) := Int.not_even_iff_odd.mp hN_not_even
  rcases hq1 with ⟨k1, rfl⟩
  rcases hN_odd with ⟨k2, hk2⟩
  have hmod4 := m8q_mod4_identity (2 * k1 + 1) a b c d
  rw [hk2] at hmod4
  refine ⟨2 * (-2 * a * c + 2 * b * d + a * d + b * c) - 2 * k1 * k2 - k1 - k2 - 1, ?_⟩
  linarith

/-- 泛函 $\Phi_{8/q_1, 0}(\eta)$ 的精确代数表达：
    $h(\eta)\frac{|8/q_1 - \eta|\,|\eta'|}{8/q_1} = \frac{|m_{8,q_1} - 4(ad-bc)\sqrt{5}|}{4\sqrt{5}}$。 -/
lemma phi8q_lhs_eq {q1 a b c d : ℤ} (hq1 : (0 : ℝ) < (q1 : ℝ)) (hdet : |a * d - b * c| = 1) :
    orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
      (|(8 : ℝ) / (q1 : ℝ) - orbitPt a b c d| * |orbitPtConj a b c d| / ((8 : ℝ) / (q1 : ℝ))) =
    |(m8q q1 a b c d : ℝ) - 4 * ((a * d - b * c : ℤ) : ℝ) * Real.sqrt 5| /
      (4 * Real.sqrt 5) := by
  have hcd := linear_phi_ne_zero (cd_ne_zero_of_det hdet)
  have hq1_ne : (q1 : ℝ) ≠ 0 := ne_of_gt hq1
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt sqrt5_pos
  have hsub : (8 : ℝ) / (q1 : ℝ) - orbitPt a b c d =
      (((8 * c - q1 * a : ℤ) : ℝ) * φ + ((8 * d - q1 * b : ℤ) : ℝ)) /
        ((q1 : ℝ) * ((c : ℝ) * φ + (d : ℝ))) := by
    unfold orbitPt mobius
    rw [div_sub_div _ _ hq1_ne hcd.1]
    push_cast; congr 1; ring
  rw [orbitHeight_eq hdet, hsub]
  unfold orbitPtConj mobius
  rw [abs_div, abs_div, abs_mul, abs_of_pos hq1, ← zphi_mul_conj c d, abs_mul]
  have h1_ne : |(c : ℝ) * φ + (d : ℝ)| ≠ 0 := abs_ne_zero.mpr hcd.1
  have h2_ne : |(c : ℝ) * φ' + (d : ℝ)| ≠ 0 := abs_ne_zero.mpr hcd.2
  have hprod := alpha8q_mul_gammaConj q1 a b c d
  calc 2 * (|(c : ℝ) * φ + (d : ℝ)| * |(c : ℝ) * φ' + (d : ℝ)|) / Real.sqrt 5 *
        (|((8 * c - q1 * a : ℤ) : ℝ) * φ + ((8 * d - q1 * b : ℤ) : ℝ)| /
          ((q1 : ℝ) * |(c : ℝ) * φ + (d : ℝ)|) *
          (|(a : ℝ) * φ' + (b : ℝ)| / |(c : ℝ) * φ' + (d : ℝ)|) / ((8 : ℝ) / (q1 : ℝ)))
      = |((8 * c - q1 * a : ℤ) : ℝ) * φ + ((8 * d - q1 * b : ℤ) : ℝ)| *
          |(a : ℝ) * φ' + (b : ℝ)| / (4 * Real.sqrt 5) := by
        field_simp [h1_ne, h2_ne, hq1_ne, h5_ne]; ring
    _ = |(((8 * c - q1 * a : ℤ) : ℝ) * φ + ((8 * d - q1 * b : ℤ) : ℝ)) *
          ((a : ℝ) * φ' + (b : ℝ))| / (4 * Real.sqrt 5) := by rw [abs_mul]
    _ = |(m8q q1 a b c d : ℝ) - 4 * ((a * d - b * c : ℤ) : ℝ) * Real.sqrt 5| /
          (4 * Real.sqrt 5) := by rw [hprod]

/-- 引理 `lem:pell-b2-rigidity` 第一部分：对奇数 $q_1 > 0$ 与 $|ad-bc|=1$，存在**奇整数** $m$ 使
    $h(\eta)\frac{|8/q_1 - \eta|\,|\eta'|}{8/q_1} = \left|\frac{m}{4\sqrt{5}} - 1\right|$。 -/
theorem phi8q_odd_rigidity_identity {q1 a b c d : ℤ}
    (hq1_pos : (0 : ℝ) < (q1 : ℝ)) (hq1_odd : Odd q1) (hdet : |a * d - b * c| = 1) :
    ∃ m : ℤ, Odd m ∧
      orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
        (|(8 : ℝ) / (q1 : ℝ) - orbitPt a b c d| * |orbitPtConj a b c d| / ((8 : ℝ) / (q1 : ℝ))) =
      |(m : ℝ) / (4 * Real.sqrt 5) - 1| := by
  have hε : a * d - b * c = 1 ∨ a * d - b * c = -1 :=
    (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
  have hε_odd : Odd (a * d - b * c) := by
    rcases hε with h1 | hm1
    · rw [h1]; exact ⟨0, by ring⟩
    · rw [hm1]; exact ⟨-1, by ring⟩
  have hm8_odd : Odd (m8q q1 a b c d) := m8q_odd hq1_odd hdet
  refine ⟨(a * d - b * c) * m8q q1 a b c d, hε_odd.mul hm8_odd, ?_⟩
  rw [phi8q_lhs_eq hq1_pos hdet]
  have h45_pos : (0 : ℝ) < 4 * Real.sqrt 5 := mul_pos (by norm_num) sqrt5_pos
  have h45_ne : 4 * Real.sqrt 5 ≠ 0 := ne_of_gt h45_pos
  rcases hε with h1 | hm1
  · rw [h1]; push_cast; rw [one_mul, mul_one]
    rw [show |(m8q q1 a b c d : ℝ) - 4 * Real.sqrt 5| / (4 * Real.sqrt 5) =
        |((m8q q1 a b c d : ℝ) - 4 * Real.sqrt 5) / (4 * Real.sqrt 5)| by
      rw [abs_div, abs_of_pos h45_pos]]
    congr 1; field_simp [h45_ne]
  · rw [hm1]; push_cast
    rw [show |(m8q q1 a b c d : ℝ) - 4 * (-1 : ℝ) * Real.sqrt 5| / (4 * Real.sqrt 5) =
        |((m8q q1 a b c d : ℝ) - 4 * (-1 : ℝ) * Real.sqrt 5) / (4 * Real.sqrt 5)| by
      rw [abs_div, abs_of_pos h45_pos]]
    rw [← abs_neg ((-1 * (m8q q1 a b c d : ℝ)) / (4 * Real.sqrt 5) - 1)]
    congr 1; field_simp [h45_ne]; ring

/-- $4\sqrt{5} = \sqrt{80}$ 的精确 Pell 界：$44/5 < 4\sqrt{5} < 9$（特别地 $8 < 17/2 < 44/5 < 4\sqrt{5} < 9$）。 -/
lemma four_sqrt5_bounds :
    (8 : ℝ) < 4 * Real.sqrt 5 ∧ (44 : ℝ) / 5 < 4 * Real.sqrt 5 ∧ 4 * Real.sqrt 5 < (9 : ℝ) := by
  have h5_pos := sqrt5_pos
  have h5_sq := sqrt5_sq
  have h44 : (44 : ℝ) / 5 < 4 * Real.sqrt 5 := by
    have hlt : ((44 : ℝ) / 5) ^ 2 < (4 * Real.sqrt 5) ^ 2 := by nlinarith [h5_sq]
    nlinarith
  have h9 : 4 * Real.sqrt 5 < (9 : ℝ) := by
    have hlt : (4 * Real.sqrt 5) ^ 2 < 9 ^ 2 := by nlinarith [h5_sq]
    nlinarith
  exact ⟨by linarith, h44, h9⟩

/-- Pell $9^2 - 5\cdot 4^2 = 1$ 谱隙定理：
    1. $0 < \frac{9}{4\sqrt{5}} - 1 < 1 - \frac{2}{\sqrt{5}} < 1 - \frac{7}{4\sqrt{5}} < \frac{11}{4\sqrt{5}} - 1$；
    2. 对任意整数 $m \ne 9$，$\left|\frac{m}{4\sqrt{5}} - 1\right| \ge 1 - \frac{2}{\sqrt{5}}$；
    3. 对任意**奇整数** $m \ne 9$，$\left|\frac{m}{4\sqrt{5}} - 1\right| \ge 1 - \frac{7}{4\sqrt{5}}$。 -/
theorem pell_b2_spectral_gap :
    (0 : ℝ) < 9 / (4 * Real.sqrt 5) - 1 ∧
    9 / (4 * Real.sqrt 5) - 1 < 1 - 2 / Real.sqrt 5 ∧
    1 - 2 / Real.sqrt 5 < 1 - 7 / (4 * Real.sqrt 5) ∧
    1 - 7 / (4 * Real.sqrt 5) < 11 / (4 * Real.sqrt 5) - 1 ∧
    (∀ m : ℤ, m ≠ 9 → 1 - 2 / Real.sqrt 5 ≤ |(m : ℝ) / (4 * Real.sqrt 5) - 1|) ∧
    (∀ m : ℤ, Odd m → m ≠ 9 → 1 - 7 / (4 * Real.sqrt 5) ≤ |(m : ℝ) / (4 * Real.sqrt 5) - 1|) := by
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  have h45_pos : (0 : ℝ) < 4 * Real.sqrt 5 := mul_pos (by norm_num) h5_pos
  have h8 : (8 : ℝ) < 4 * Real.sqrt 5 := four_sqrt5_bounds.1
  have h44 : (44 : ℝ) / 5 < 4 * Real.sqrt 5 := four_sqrt5_bounds.2.1
  have h9 : 4 * Real.sqrt 5 < (9 : ℝ) := four_sqrt5_bounds.2.2
  have h28 : 2 / Real.sqrt 5 = 8 / (4 * Real.sqrt 5) := by field_simp [h5_ne]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sub_pos, one_lt_div h45_pos]; exact h9
  · rw [h28]
    have h17_div : (17 : ℝ) / (4 * Real.sqrt 5) < 2 := by
      rw [div_lt_iff₀ h45_pos]; linarith
    have hsplit : (17 : ℝ) / (4 * Real.sqrt 5) =
        9 / (4 * Real.sqrt 5) + 8 / (4 * Real.sqrt 5) := by ring
    linarith
  · rw [h28]
    have : 7 / (4 * Real.sqrt 5) < 8 / (4 * Real.sqrt 5) :=
      div_lt_div_of_pos_right (by norm_num) h45_pos
    linarith
  · have : (2 : ℝ) < 18 / (4 * Real.sqrt 5) := by
      rw [lt_div_iff₀ h45_pos]; linarith
    have hsplit : (18 : ℝ) / (4 * Real.sqrt 5) =
        11 / (4 * Real.sqrt 5) + 7 / (4 * Real.sqrt 5) := by ring
    linarith
  · intro m hm
    rw [h28]
    have hcases : m ≤ 8 ∨ 10 ≤ m := by omega
    rcases hcases with hle8 | hge10
    · have hmR : (m : ℝ) ≤ 8 := by exact_mod_cast hle8
      have hle : (m : ℝ) / (4 * Real.sqrt 5) ≤ 8 / (4 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h45_pos)
      have hlt1 : 8 / (4 * Real.sqrt 5) < 1 := (div_lt_one h45_pos).mpr h8
      rw [abs_of_neg (by linarith)]
      linarith
    · have hmR : (10 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hge10
      have hge : 10 / (4 * Real.sqrt 5) ≤ (m : ℝ) / (4 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h45_pos)
      have hgt1 : 1 < 10 / (4 * Real.sqrt 5) := (one_lt_div h45_pos).mpr (by linarith)
      rw [abs_of_pos (by linarith)]
      have : (2 : ℝ) < 18 / (4 * Real.sqrt 5) := by
        rw [lt_div_iff₀ h45_pos]; linarith
      have hsplit : (18 : ℝ) / (4 * Real.sqrt 5) =
          10 / (4 * Real.sqrt 5) + 8 / (4 * Real.sqrt 5) := by ring
      linarith
  · intro m hodd hm
    rcases hodd with ⟨k, rfl⟩
    have hcases : 2 * k + 1 ≤ 7 ∨ 11 ≤ 2 * k + 1 := by omega
    rcases hcases with hle7 | hge11
    · have hmR : ((2 * k + 1 : ℤ) : ℝ) ≤ 7 := by exact_mod_cast hle7
      have hle : ((2 * k + 1 : ℤ) : ℝ) / (4 * Real.sqrt 5) ≤ 7 / (4 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h45_pos)
      have hlt1 : 7 / (4 * Real.sqrt 5) < 1 := (div_lt_one h45_pos).mpr (by linarith)
      rw [abs_of_neg (by linarith)]
      linarith
    · have hmR : (11 : ℝ) ≤ ((2 * k + 1 : ℤ) : ℝ) := by exact_mod_cast hge11
      have hge : 11 / (4 * Real.sqrt 5) ≤ ((2 * k + 1 : ℤ) : ℝ) / (4 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h45_pos)
      have hgt1 : 1 < 11 / (4 * Real.sqrt 5) := (one_lt_div h45_pos).mpr (by linarith)
      rw [abs_of_pos (by linarith)]
      have : (2 : ℝ) < 18 / (4 * Real.sqrt 5) := by
        rw [lt_div_iff₀ h45_pos]; linarith
      have hsplit : (18 : ℝ) / (4 * Real.sqrt 5) =
          11 / (4 * Real.sqrt 5) + 7 / (4 * Real.sqrt 5) := by ring
      linarith

/-- $\Phi_{8/5, 0}(\eta) = \frac{9}{4\sqrt{5}} - 1$ 的唯一性定理：
    $h(\eta)\frac{|8/5 - \eta|\,|\eta'|}{8/5} = \frac{9}{4\sqrt{5}} - 1 \iff \eta = \varphi$。 -/
theorem phi85_eq_min_iff {a b c d : ℤ} (hdet : |a * d - b * c| = 1) :
    orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
      (|(8 : ℝ) / 5 - orbitPt a b c d| * |orbitPtConj a b c d| / ((8 : ℝ) / 5)) =
      9 / (4 * Real.sqrt 5) - 1 ↔
    orbitPt a b c d = φ := by
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  have h5_sq := sqrt5_sq
  have h45_pos : (0 : ℝ) < 4 * Real.sqrt 5 := mul_pos (by norm_num) h5_pos
  have h45_ne : 4 * Real.sqrt 5 ≠ 0 := ne_of_gt h45_pos
  have hcd := linear_phi_ne_zero (cd_ne_zero_of_det hdet)
  have hab := linear_phi_ne_zero (ab_ne_zero_of_det hdet)
  constructor
  · intro heq
    set ε : ℤ := a * d - b * c with hε_def
    have hε : ε = 1 ∨ ε = -1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
    have hε_sq : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
    set m : ℤ := ε * m8q 5 a b c d
    have hval : |(m : ℝ) / (4 * Real.sqrt 5) - 1| = 9 / (4 * Real.sqrt 5) - 1 := by
      have hlhs := phi8q_lhs_eq (q1 := 5) (by norm_num) hdet
      change orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
        (|(8 : ℝ) / 5 - orbitPt a b c d| * |orbitPtConj a b c d| / ((8 : ℝ) / 5)) =
        |(m8q 5 a b c d : ℝ) - 4 * ((a * d - b * c : ℤ) : ℝ) * Real.sqrt 5| / (4 * Real.sqrt 5) at hlhs
      rw [hlhs] at heq
      rw [← heq, ← hε_def]
      dsimp only [m]
      rcases hε with h1 | hm1
      · rw [h1]; push_cast; rw [one_mul, mul_one]
        rw [show |(m8q 5 a b c d : ℝ) - 4 * Real.sqrt 5| / (4 * Real.sqrt 5) =
            |((m8q 5 a b c d : ℝ) - 4 * Real.sqrt 5) / (4 * Real.sqrt 5)| by
          rw [abs_div, abs_of_pos h45_pos]]
        congr 1; field_simp [h45_ne]
      · rw [hm1]; push_cast
        rw [show |(m8q 5 a b c d : ℝ) - 4 * (-1 : ℝ) * Real.sqrt 5| / (4 * Real.sqrt 5) =
            |((m8q 5 a b c d : ℝ) - 4 * (-1 : ℝ) * Real.sqrt 5) / (4 * Real.sqrt 5)| by
          rw [abs_div, abs_of_pos h45_pos]]
        rw [← abs_neg ((-1 * (m8q 5 a b c d : ℝ)) / (4 * Real.sqrt 5) - 1)]
        congr 1; field_simp [h45_ne]; ring
    have hm9 : m = 9 := by
      by_contra hne
      have hge := pell_b2_spectral_gap.2.2.2.2.1 m hne
      have hlt := pell_b2_spectral_gap.2.1
      linarith
    have hm8_eq : m8q 5 a b c d = 9 * ε := by
      have : ε * (ε * m8q 5 a b c d) = ε * 9 := congrArg (ε * ·) hm9
      have : ε ^ 2 * m8q 5 a b c d = 9 * ε := by linarith
      rw [hε_sq, one_mul] at this
      exact this
    have hnorm := m8q_norm_identity 5 a b c d
    rw [hm8_eq, ← hε_def] at hnorm
    have hNprod : zphiNorm (8 * c - 5 * a) (8 * d - 5 * b) * zphiNorm a b = 1 := by
      nlinarith [hnorm, hε_sq]
    have hNγ : zphiNorm a b = 1 ∨ zphiNorm a b = -1 := by
      have hdvd : zphiNorm a b ∣ 1 := ⟨zphiNorm (8 * c - 5 * a) (8 * d - 5 * b), by linarith⟩
      exact Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
    -- 模 4 判别式：9ε + 5 N(γ) = 4(...)，故 ε * N(γ) = -1！
    have hmod4 := m8q_mod4_identity 5 a b c d
    rw [hm8_eq] at hmod4
    have hσ_neg1 : ε * zphiNorm a b = -1 := by
      rcases hε with h1 | hm1 <;> rcases hNγ with h2 | hm2
      · rw [h1, h2] at hmod4; omega
      · rw [h1, hm2]; ring
      · rw [hm1, h2]; ring
      · rw [hm1, hm2] at hmod4; omega
    set αR : ℝ := ((8 * c - 5 * a : ℤ) : ℝ) * φ + ((8 * d - 5 * b : ℤ) : ℝ)
    set γR : ℝ := (a : ℝ) * φ + (b : ℝ)
    set γ'R : ℝ := (a : ℝ) * φ' + (b : ℝ)
    have hαγ' : αR * γ'R = (ε : ℝ) * (9 - 4 * Real.sqrt 5) := by
      have h1 := alpha8q_mul_gammaConj 5 a b c d
      change αR * γ'R = _ at h1
      rw [h1, hm8_eq, ← hε_def]
      push_cast; ring
    have hγγ' : γR * γ'R = (zphiNorm a b : ℝ) := zphi_mul_conj a b
    have hsum : αR + 5 * γR = 8 * ((c : ℝ) * φ + (d : ℝ)) := by
      dsimp only [αR, γR]; push_cast; ring
    have hα_eq : αR = -(9 - 4 * Real.sqrt 5) * γR := by
      have hγ'_ne : γ'R ≠ 0 := hab.2
      have hNγ_sq : (zphiNorm a b : ℝ) ^ 2 = 1 := by
        rcases hNγ with h | h <;> rw [h] <;> norm_num
      have hσR : (ε : ℝ) * (zphiNorm a b : ℝ) = -1 := by exact_mod_cast hσ_neg1
      have hmul : αR * γ'R = (-(9 - 4 * Real.sqrt 5) * γR) * γ'R := by
        calc αR * γ'R = (ε : ℝ) * (9 - 4 * Real.sqrt 5) * 1 := by rw [hαγ']; ring
          _ = (ε : ℝ) * (9 - 4 * Real.sqrt 5) * ((zphiNorm a b : ℝ) ^ 2) := by rw [hNγ_sq]
          _ = ((ε : ℝ) * (zphiNorm a b : ℝ)) * (9 - 4 * Real.sqrt 5) * (γR * γ'R) := by
                rw [hγγ']; ring
          _ = (-(9 - 4 * Real.sqrt 5) * γR) * γ'R := by rw [hσR]; ring
      exact mul_right_cancel₀ hγ'_ne hmul
    unfold orbitPt mobius
    change γR / ((c : ℝ) * φ + (d : ℝ)) = φ
    have h8denom : 8 * ((c : ℝ) * φ + (d : ℝ)) = 4 * (Real.sqrt 5 - 1) * γR := by
      linarith [hsum, hα_eq]
    have hdenom_eq : (c : ℝ) * φ + (d : ℝ) = ((Real.sqrt 5 - 1) / 2) * γR := by linarith
    rw [hdenom_eq]
    have h5m1 : (Real.sqrt 5 - 1) / 2 ≠ 0 := by
      have := sqrt5_bounds.1; linarith
    rw [div_eq_iff (mul_ne_zero h5m1 hab.1)]
    unfold φ
    ring_nf; rw [h5_sq]; ring
  · intro hφ
    have hlin : ∀ (u v : ℤ), (u : ℝ) * φ + (v : ℝ) = 0 → u = 0 ∧ v = 0 := by
      intro u v huv
      by_contra h
      have hne : u ≠ 0 ∨ v ≠ 0 := by tauto
      exact (linear_phi_ne_zero hne).1 huv
    have hφ' : orbitPtConj a b c d = φ' := by
      unfold orbitPt mobius at hφ
      have h0 : (a : ℝ) * φ + (b : ℝ) = φ * ((c : ℝ) * φ + (d : ℝ)) :=
        (div_eq_iff hcd.1).mp hφ
      have h1 : ((a - c - d : ℤ) : ℝ) * φ + ((b - c : ℤ) : ℝ) = 0 := by
        push_cast; linear_combination h0 + (c : ℝ) * phi_sq
      rcases hlin _ _ h1 with ⟨hu, hv⟩
      unfold orbitPtConj mobius
      rw [div_eq_iff hcd.2]
      have ha : (a : ℝ) = (c : ℝ) + (d : ℝ) := by exact_mod_cast (show a = c + d by omega)
      have hb : (b : ℝ) = (c : ℝ) := by exact_mod_cast (show b = c by omega)
      rw [ha, hb]; linear_combination -(c : ℝ) * phi'_sq
    rw [hφ, hφ']
    unfold orbitHeight
    rw [phi_sub_phi', abs_of_pos h5_pos]
    have h85mφ : (8 : ℝ) / 5 - φ < 0 := by unfold φ; linarith [four_sqrt5_bounds.2.1]
    have hφ'_neg : φ' < 0 := by unfold φ'; linarith [sqrt5_bounds.1]
    rw [abs_of_neg h85mφ, abs_of_neg hφ'_neg]
    unfold φ φ'
    field_simp [h5_ne]
    ring_nf; rw [h5_sq]; ring

/-- $\Phi_{8/3, 0}(\eta) = \frac{9}{4\sqrt{5}} - 1$ 的唯一性定理：
    $h(\eta)\frac{|8/3 - \eta|\,|\eta'|}{8/3} = \frac{9}{4\sqrt{5}} - 1 \iff \eta = \varphi + 1$。 -/
theorem phi83_eq_min_iff {a b c d : ℤ} (hdet : |a * d - b * c| = 1) :
    orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
      (|(8 : ℝ) / 3 - orbitPt a b c d| * |orbitPtConj a b c d| / ((8 : ℝ) / 3)) =
      9 / (4 * Real.sqrt 5) - 1 ↔
    orbitPt a b c d = φ + 1 := by
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  have h5_sq := sqrt5_sq
  have h45_pos : (0 : ℝ) < 4 * Real.sqrt 5 := mul_pos (by norm_num) h5_pos
  have h45_ne : 4 * Real.sqrt 5 ≠ 0 := ne_of_gt h45_pos
  have hcd := linear_phi_ne_zero (cd_ne_zero_of_det hdet)
  have hab := linear_phi_ne_zero (ab_ne_zero_of_det hdet)
  constructor
  · intro heq
    set ε : ℤ := a * d - b * c with hε_def
    have hε : ε = 1 ∨ ε = -1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
    have hε_sq : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
    set m : ℤ := ε * m8q 3 a b c d
    have hval : |(m : ℝ) / (4 * Real.sqrt 5) - 1| = 9 / (4 * Real.sqrt 5) - 1 := by
      have hlhs := phi8q_lhs_eq (q1 := 3) (by norm_num) hdet
      change orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
        (|(8 : ℝ) / 3 - orbitPt a b c d| * |orbitPtConj a b c d| / ((8 : ℝ) / 3)) =
        |(m8q 3 a b c d : ℝ) - 4 * ((a * d - b * c : ℤ) : ℝ) * Real.sqrt 5| / (4 * Real.sqrt 5) at hlhs
      rw [hlhs] at heq
      rw [← heq, ← hε_def]
      dsimp only [m]
      rcases hε with h1 | hm1
      · rw [h1]; push_cast; rw [one_mul, mul_one]
        rw [show |(m8q 3 a b c d : ℝ) - 4 * Real.sqrt 5| / (4 * Real.sqrt 5) =
            |((m8q 3 a b c d : ℝ) - 4 * Real.sqrt 5) / (4 * Real.sqrt 5)| by
          rw [abs_div, abs_of_pos h45_pos]]
        congr 1; field_simp [h45_ne]
      · rw [hm1]; push_cast
        rw [show |(m8q 3 a b c d : ℝ) - 4 * (-1 : ℝ) * Real.sqrt 5| / (4 * Real.sqrt 5) =
            |((m8q 3 a b c d : ℝ) - 4 * (-1 : ℝ) * Real.sqrt 5) / (4 * Real.sqrt 5)| by
          rw [abs_div, abs_of_pos h45_pos]]
        rw [← abs_neg ((-1 * (m8q 3 a b c d : ℝ)) / (4 * Real.sqrt 5) - 1)]
        congr 1; field_simp [h45_ne]; ring
    have hm9 : m = 9 := by
      by_contra hne
      have hge := pell_b2_spectral_gap.2.2.2.2.1 m hne
      have hlt := pell_b2_spectral_gap.2.1
      linarith
    have hm8_eq : m8q 3 a b c d = 9 * ε := by
      have : ε * (ε * m8q 3 a b c d) = ε * 9 := congrArg (ε * ·) hm9
      have : ε ^ 2 * m8q 3 a b c d = 9 * ε := by linarith
      rw [hε_sq, one_mul] at this
      exact this
    have hnorm := m8q_norm_identity 3 a b c d
    rw [hm8_eq, ← hε_def] at hnorm
    have hNprod : zphiNorm (8 * c - 3 * a) (8 * d - 3 * b) * zphiNorm a b = 1 := by
      nlinarith [hnorm, hε_sq]
    have hNγ : zphiNorm a b = 1 ∨ zphiNorm a b = -1 := by
      have hdvd : zphiNorm a b ∣ 1 := ⟨zphiNorm (8 * c - 3 * a) (8 * d - 3 * b), by linarith⟩
      exact Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
    -- 模 4 判别式：9ε + 3 N(γ) = 4(...)，故 ε * N(γ) = +1！
    have hmod4 := m8q_mod4_identity 3 a b c d
    rw [hm8_eq] at hmod4
    have hσ_pos1 : ε * zphiNorm a b = 1 := by
      rcases hε with h1 | hm1 <;> rcases hNγ with h2 | hm2
      · rw [h1, h2]; ring
      · rw [h1, hm2] at hmod4; omega
      · rw [hm1, h2] at hmod4; omega
      · rw [hm1, hm2]; ring
    set αR : ℝ := ((8 * c - 3 * a : ℤ) : ℝ) * φ + ((8 * d - 3 * b : ℤ) : ℝ)
    set γR : ℝ := (a : ℝ) * φ + (b : ℝ)
    set γ'R : ℝ := (a : ℝ) * φ' + (b : ℝ)
    have hαγ' : αR * γ'R = (ε : ℝ) * (9 - 4 * Real.sqrt 5) := by
      have h1 := alpha8q_mul_gammaConj 3 a b c d
      change αR * γ'R = _ at h1
      rw [h1, hm8_eq, ← hε_def]
      push_cast; ring
    have hγγ' : γR * γ'R = (zphiNorm a b : ℝ) := zphi_mul_conj a b
    have hsum : αR + 3 * γR = 8 * ((c : ℝ) * φ + (d : ℝ)) := by
      dsimp only [αR, γR]; push_cast; ring
    have hα_eq : αR = (9 - 4 * Real.sqrt 5) * γR := by
      have hγ'_ne : γ'R ≠ 0 := hab.2
      have hNγ_sq : (zphiNorm a b : ℝ) ^ 2 = 1 := by
        rcases hNγ with h | h <;> rw [h] <;> norm_num
      have hσR : (ε : ℝ) * (zphiNorm a b : ℝ) = 1 := by exact_mod_cast hσ_pos1
      have hmul : αR * γ'R = ((9 - 4 * Real.sqrt 5) * γR) * γ'R := by
        calc αR * γ'R = (ε : ℝ) * (9 - 4 * Real.sqrt 5) * 1 := by rw [hαγ']; ring
          _ = (ε : ℝ) * (9 - 4 * Real.sqrt 5) * ((zphiNorm a b : ℝ) ^ 2) := by rw [hNγ_sq]
          _ = ((ε : ℝ) * (zphiNorm a b : ℝ)) * (9 - 4 * Real.sqrt 5) * (γR * γ'R) := by
                rw [hγγ']; ring
          _ = ((9 - 4 * Real.sqrt 5) * γR) * γ'R := by rw [hσR]; ring
      exact mul_right_cancel₀ hγ'_ne hmul
    unfold orbitPt mobius
    change γR / ((c : ℝ) * φ + (d : ℝ)) = φ + 1
    have h8denom : 8 * ((c : ℝ) * φ + (d : ℝ)) = 4 * (3 - Real.sqrt 5) * γR := by
      linarith [hsum, hα_eq]
    have hdenom_eq : (c : ℝ) * φ + (d : ℝ) = ((3 - Real.sqrt 5) / 2) * γR := by linarith
    rw [hdenom_eq]
    have h3m5 : (3 - Real.sqrt 5) / 2 ≠ 0 := by
      have := sqrt5_bounds.2; linarith
    rw [div_eq_iff (mul_ne_zero h3m5 hab.1)]
    unfold φ
    ring_nf; rw [h5_sq]; ring
  · intro hφ1
    have hlin : ∀ (u v : ℤ), (u : ℝ) * φ + (v : ℝ) = 0 → u = 0 ∧ v = 0 := by
      intro u v huv
      by_contra h
      have hne : u ≠ 0 ∨ v ≠ 0 := by tauto
      exact (linear_phi_ne_zero hne).1 huv
    have hφ1' : orbitPtConj a b c d = φ' + 1 := by
      unfold orbitPt mobius at hφ1
      have h0 : (a : ℝ) * φ + (b : ℝ) = (φ + 1) * ((c : ℝ) * φ + (d : ℝ)) :=
        (div_eq_iff hcd.1).mp hφ1
      have h1 : ((a - 2 * c - d : ℤ) : ℝ) * φ + ((b - c - d : ℤ) : ℝ) = 0 := by
        push_cast; linear_combination h0 + (c : ℝ) * phi_sq
      rcases hlin _ _ h1 with ⟨hu, hv⟩
      unfold orbitPtConj mobius
      rw [div_eq_iff hcd.2]
      have ha : (a : ℝ) = 2 * (c : ℝ) + (d : ℝ) := by
        exact_mod_cast (show a = 2 * c + d by omega)
      have hb : (b : ℝ) = (c : ℝ) + (d : ℝ) := by exact_mod_cast (show b = c + d by omega)
      rw [ha, hb]; linear_combination -(c : ℝ) * phi'_sq
    rw [hφ1, hφ1']
    unfold orbitHeight
    rw [show (φ + 1) - (φ' + 1) = φ - φ' by ring, phi_sub_phi', abs_of_pos h5_pos]
    have h83mφ1 : 0 < (8 : ℝ) / 3 - (φ + 1) := by unfold φ; linarith [four_sqrt5_bounds.2.2]
    have hφ'1_pos : 0 < φ' + 1 := by unfold φ'; linarith [sqrt5_bounds.2]
    rw [abs_of_pos h83mφ1, abs_of_pos hφ'1_pos]
    unfold φ φ'
    field_simp [h5_ne]
    ring_nf; rw [h5_sq]; ring

/-- $\Phi_{8/5, 0}$ 的严格次小谱隙下界：对一切 $\eta \ne \varphi$，
    $h(\eta)\frac{|8/5 - \eta|\,|\eta'|}{8/5} \ge 1 - \frac{7}{4\sqrt{5}}$。 -/
theorem phi85_ge_second {a b c d : ℤ} (hdet : |a * d - b * c| = 1)
    (hne : orbitPt a b c d ≠ φ) :
    1 - 7 / (4 * Real.sqrt 5) ≤
      orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
        (|(8 : ℝ) / 5 - orbitPt a b c d| * |orbitPtConj a b c d| / ((8 : ℝ) / 5)) := by
  have h5_odd : Odd (5 : ℤ) := ⟨2, by ring⟩
  rcases phi8q_odd_rigidity_identity (q1 := 5) (by norm_num) h5_odd hdet with ⟨m, hm_odd, hm_eq⟩
  push_cast at hm_eq
  rw [hm_eq]
  have hm_ne9 : m ≠ 9 := by
    intro h9
    subst h9
    have hval : |((9 : ℤ) : ℝ) / (4 * Real.sqrt 5) - 1| = 9 / (4 * Real.sqrt 5) - 1 := by
      push_cast
      rw [abs_of_pos pell_b2_spectral_gap.1]
    rw [hval] at hm_eq
    exact hne ((phi85_eq_min_iff hdet).mp hm_eq)
  exact pell_b2_spectral_gap.2.2.2.2.2 m hm_odd hm_ne9

/-- $\Phi_{8/3, 0}$ 的严格次小谱隙下界：对一切 $\eta \ne \varphi + 1$，
    $h(\eta)\frac{|8/3 - \eta|\,|\eta'|}{8/3} \ge 1 - \frac{7}{4\sqrt{5}}$。 -/
theorem phi83_ge_second {a b c d : ℤ} (hdet : |a * d - b * c| = 1)
    (hne : orbitPt a b c d ≠ φ + 1) :
    1 - 7 / (4 * Real.sqrt 5) ≤
      orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
        (|(8 : ℝ) / 3 - orbitPt a b c d| * |orbitPtConj a b c d| / ((8 : ℝ) / 3)) := by
  have h3_odd : Odd (3 : ℤ) := ⟨1, by ring⟩
  rcases phi8q_odd_rigidity_identity (q1 := 3) (by norm_num) h3_odd hdet with ⟨m, hm_odd, hm_eq⟩
  push_cast at hm_eq
  rw [hm_eq]
  have hm_ne9 : m ≠ 9 := by
    intro h9
    subst h9
    have hval : |((9 : ℤ) : ℝ) / (4 * Real.sqrt 5) - 1| = 9 / (4 * Real.sqrt 5) - 1 := by
      push_cast
      rw [abs_of_pos pell_b2_spectral_gap.1]
    rw [hval] at hm_eq
    exact hne ((phi83_eq_min_iff hdet).mp hm_eq)
  exact pell_b2_spectral_gap.2.2.2.2.2 m hm_odd hm_ne9

/-- 次小极限点 $1 - \frac{7}{4\sqrt{5}}$ 在 $u = 8/5$ 处由 $\eta = \varphi + 1$ 精确取到。 -/
theorem phi85_second_attained :
    orbitHeight (φ + 1) (φ' + 1) * (|(8 : ℝ) / 5 - (φ + 1)| * |φ' + 1| / ((8 : ℝ) / 5)) =
      1 - 7 / (4 * Real.sqrt 5) := by
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  have h5_sq := sqrt5_sq
  unfold orbitHeight
  rw [show (φ + 1) - (φ' + 1) = φ - φ' by ring, phi_sub_phi', abs_of_pos h5_pos]
  have h1 : (8 : ℝ) / 5 - (φ + 1) < 0 := by unfold φ; linarith [sqrt5_bounds.1]
  have h2 : 0 < φ' + 1 := by unfold φ'; linarith [sqrt5_bounds.2]
  rw [abs_of_neg h1, abs_of_pos h2]
  unfold φ φ'
  field_simp [h5_ne]
  ring_nf; rw [h5_sq]; ring

/-- 次小极限点 $1 - \frac{7}{4\sqrt{5}}$ 在 $u = 8/3$ 处由 $\eta = \varphi$ 精确取到。 -/
theorem phi83_second_attained :
    orbitHeight φ φ' * (|(8 : ℝ) / 3 - φ| * |φ'| / ((8 : ℝ) / 3)) =
      1 - 7 / (4 * Real.sqrt 5) := by
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  have h5_sq := sqrt5_sq
  unfold orbitHeight
  rw [phi_sub_phi', abs_of_pos h5_pos]
  have h1 : 0 < (8 : ℝ) / 3 - φ := by unfold φ; linarith [sqrt5_bounds.2]
  have h2 : φ' < 0 := by unfold φ'; linarith [sqrt5_bounds.1]
  rw [abs_of_pos h1, abs_of_neg h2]
  unfold φ φ'
  field_simp [h5_ne]
  ring_nf; rw [h5_sq]; ring

/-! ### 4. 定理 `thm:golden-b2-exact` 的分歧位置一致下界与大商凹二次下界 -/

/-- 周期 10 有界块 $(1,1,1,2)$（即 $u = 8/5$）处的分歧一致下界：
    对一切 $\eta \ne \varphi$，若 $\eta > 8/5$ 或 $\eta < 11/7$，且 $|\eta'| > 1/2$，则
    $h(\eta)\frac{|(8/5-\delta)-\eta|\,|\eta'+z|}{(8/5-\delta)+z}
     \ge \frac{(1-35\delta)(1-2z)}{1+5z/8}\left(1 - \frac{7}{4\sqrt{5}}\right)$。 -/
theorem b2_case1_85_lower_bound {a b c d : ℤ} (hdet : |a * d - b * c| = 1)
    (hne : orbitPt a b c d ≠ φ)
    {δ z : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 35) (hz0 : 0 ≤ z) (hz1 : z < 1 / 2)
    (hconj : 1 / 2 < |orbitPtConj a b c d|)
    (hsep : (8 : ℝ) / 5 < orbitPt a b c d ∨ orbitPt a b c d < 11 / 7) :
    ((1 - 35 * δ) * (1 - 2 * z) / (1 + 5 * z / 8)) * (1 - 7 / (4 * Real.sqrt 5)) ≤
      orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
        (|((8 : ℝ) / 5 - δ) - orbitPt a b c d| * |orbitPtConj a b c d + z| /
          (((8 : ℝ) / 5 - δ) + z)) := by
  set η := orbitPt a b c d
  set η' := orbitPtConj a b c d
  set H := orbitHeight η η'
  have hH_nonneg : 0 ≤ H := by unfold H orbitHeight; positivity
  have hη'_bound : (1 - 2 * z) * |η'| ≤ |η' + z| := by
    have htri : |η'| - |z| ≤ |η' + z| := by
      have := abs_sub_abs_le_abs_sub η' (-z)
      simpa [sub_neg_eq_add] using this
    rw [abs_of_nonneg hz0] at htri
    nlinarith
  have hT_bound : (1 - 35 * δ) * |(8 : ℝ) / 5 - η| ≤ |((8 : ℝ) / 5 - δ) - η| := by
    rcases hsep with hgt | hlt
    · rw [abs_of_neg (by linarith : (8 : ℝ) / 5 - η < 0),
        abs_of_neg (by linarith : ((8 : ℝ) / 5 - δ) - η < 0)]
      nlinarith
    · rw [abs_of_pos (by linarith : 0 < (8 : ℝ) / 5 - η),
        abs_of_pos (by linarith : 0 < ((8 : ℝ) / 5 - δ) - η)]
      nlinarith
  have hdenom_pos : 0 < ((8 : ℝ) / 5 - δ) + z := by linarith
  have hdenom_le : ((8 : ℝ) / 5 - δ) + z ≤ ((8 : ℝ) / 5) * (1 + 5 * z / 8) := by linarith
  have h1 : (1 - 35 * δ) * (1 - 2 * z) * (|(8 : ℝ) / 5 - η| * |η'|) ≤
      |((8 : ℝ) / 5 - δ) - η| * |η' + z| := by
    have hmul := mul_le_mul hT_bound hη'_bound
      (mul_nonneg (by linarith) (abs_nonneg η'))
      (abs_nonneg (((8 : ℝ) / 5 - δ) - η))
    linarith
  have h2 : ((1 - 35 * δ) * (1 - 2 * z) / (1 + 5 * z / 8)) *
      (|(8 : ℝ) / 5 - η| * |η'| / ((8 : ℝ) / 5)) ≤
      |((8 : ℝ) / 5 - δ) - η| * |η' + z| / (((8 : ℝ) / 5 - δ) + z) := by
    have hdiv1 : ((1 - 35 * δ) * (1 - 2 * z) * (|(8 : ℝ) / 5 - η| * |η'|)) /
        (((8 : ℝ) / 5) * (1 + 5 * z / 8)) ≤
        (|((8 : ℝ) / 5 - δ) - η| * |η' + z|) / (((8 : ℝ) / 5) * (1 + 5 * z / 8)) :=
      div_le_div_of_nonneg_right h1 (by linarith)
    have hdiv2 : (|((8 : ℝ) / 5 - δ) - η| * |η' + z|) / (((8 : ℝ) / 5) * (1 + 5 * z / 8)) ≤
        (|((8 : ℝ) / 5 - δ) - η| * |η' + z|) / (((8 : ℝ) / 5 - δ) + z) :=
      div_le_div_of_nonneg_left (by positivity) hdenom_pos hdenom_le
    have h1z_ne : 1 + 5 * z / 8 ≠ 0 := by linarith
    have hrew : ((1 - 35 * δ) * (1 - 2 * z) / (1 + 5 * z / 8)) *
        (|(8 : ℝ) / 5 - η| * |η'| / ((8 : ℝ) / 5)) =
        ((1 - 35 * δ) * (1 - 2 * z) * (|(8 : ℝ) / 5 - η| * |η'|)) /
          (((8 : ℝ) / 5) * (1 + 5 * z / 8)) := by
      field_simp [h1z_ne]
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hH_nonneg
  have hrig := phi85_ge_second hdet hne
  have hfac_nonneg : 0 ≤ (1 - 35 * δ) * (1 - 2 * z) / (1 + 5 * z / 8) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h4 := mul_le_mul_of_nonneg_left hrig hfac_nonneg
  linarith

/-- 周期 10 有界块 $(2,1,1,1)$（即 $u = 8/3$）处的分歧一致下界：
    对一切 $\eta \ne \varphi + 1$，若 $\eta > 8/3$ 或 $\eta < 13/5$，且 $|\eta'| > 1/2$，则
    $h(\eta)\frac{|(8/3-\delta)-\eta|\,|\eta'+z|}{(8/3-\delta)+z}
     \ge \frac{(1-15\delta)(1-2z)}{1+3z/8}\left(1 - \frac{7}{4\sqrt{5}}\right)$。 -/
theorem b2_case1_83_lower_bound {a b c d : ℤ} (hdet : |a * d - b * c| = 1)
    (hne : orbitPt a b c d ≠ φ + 1)
    {δ z : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 15) (hz0 : 0 ≤ z) (hz1 : z < 1 / 2)
    (hconj : 1 / 2 < |orbitPtConj a b c d|)
    (hsep : (8 : ℝ) / 3 < orbitPt a b c d ∨ orbitPt a b c d < 13 / 5) :
    ((1 - 15 * δ) * (1 - 2 * z) / (1 + 3 * z / 8)) * (1 - 7 / (4 * Real.sqrt 5)) ≤
      orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
        (|((8 : ℝ) / 3 - δ) - orbitPt a b c d| * |orbitPtConj a b c d + z| /
          (((8 : ℝ) / 3 - δ) + z)) := by
  set η := orbitPt a b c d
  set η' := orbitPtConj a b c d
  set H := orbitHeight η η'
  have hH_nonneg : 0 ≤ H := by unfold H orbitHeight; positivity
  have hη'_bound : (1 - 2 * z) * |η'| ≤ |η' + z| := by
    have htri : |η'| - |z| ≤ |η' + z| := by
      have := abs_sub_abs_le_abs_sub η' (-z)
      simpa [sub_neg_eq_add] using this
    rw [abs_of_nonneg hz0] at htri
    nlinarith
  have hT_bound : (1 - 15 * δ) * |(8 : ℝ) / 3 - η| ≤ |((8 : ℝ) / 3 - δ) - η| := by
    rcases hsep with hgt | hlt
    · rw [abs_of_neg (by linarith : (8 : ℝ) / 3 - η < 0),
        abs_of_neg (by linarith : ((8 : ℝ) / 3 - δ) - η < 0)]
      nlinarith
    · rw [abs_of_pos (by linarith : 0 < (8 : ℝ) / 3 - η),
        abs_of_pos (by linarith : 0 < ((8 : ℝ) / 3 - δ) - η)]
      nlinarith
  have hdenom_pos : 0 < ((8 : ℝ) / 3 - δ) + z := by linarith
  have hdenom_le : ((8 : ℝ) / 3 - δ) + z ≤ ((8 : ℝ) / 3) * (1 + 3 * z / 8) := by linarith
  have h1 : (1 - 15 * δ) * (1 - 2 * z) * (|(8 : ℝ) / 3 - η| * |η'|) ≤
      |((8 : ℝ) / 3 - δ) - η| * |η' + z| := by
    have hmul := mul_le_mul hT_bound hη'_bound
      (mul_nonneg (by linarith) (abs_nonneg η'))
      (abs_nonneg (((8 : ℝ) / 3 - δ) - η))
    linarith
  have h2 : ((1 - 15 * δ) * (1 - 2 * z) / (1 + 3 * z / 8)) *
      (|(8 : ℝ) / 3 - η| * |η'| / ((8 : ℝ) / 3)) ≤
      |((8 : ℝ) / 3 - δ) - η| * |η' + z| / (((8 : ℝ) / 3 - δ) + z) := by
    have hdiv1 : ((1 - 15 * δ) * (1 - 2 * z) * (|(8 : ℝ) / 3 - η| * |η'|)) /
        (((8 : ℝ) / 3) * (1 + 3 * z / 8)) ≤
        (|((8 : ℝ) / 3 - δ) - η| * |η' + z|) / (((8 : ℝ) / 3) * (1 + 3 * z / 8)) :=
      div_le_div_of_nonneg_right h1 (by linarith)
    have hdiv2 : (|((8 : ℝ) / 3 - δ) - η| * |η' + z|) / (((8 : ℝ) / 3) * (1 + 3 * z / 8)) ≤
        (|((8 : ℝ) / 3 - δ) - η| * |η' + z|) / (((8 : ℝ) / 3 - δ) + z) :=
      div_le_div_of_nonneg_left (by positivity) hdenom_pos hdenom_le
    have h1z_ne : 1 + 3 * z / 8 ≠ 0 := by linarith
    have hrew : ((1 - 15 * δ) * (1 - 2 * z) / (1 + 3 * z / 8)) *
        (|(8 : ℝ) / 3 - η| * |η'| / ((8 : ℝ) / 3)) =
        ((1 - 15 * δ) * (1 - 2 * z) * (|(8 : ℝ) / 3 - η| * |η'|)) /
          (((8 : ℝ) / 3) * (1 + 3 * z / 8)) := by
      field_simp [h1z_ne]
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hH_nonneg
  have hrig := phi83_ge_second hdet hne
  have hfac_nonneg : 0 ≤ (1 - 15 * δ) * (1 - 2 * z) / (1 + 3 * z / 8) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h4 := mul_le_mul_of_nonneg_left hrig hfac_nonneg
  linarith

/-- 大商位置 $m = s_k$（$r = 3/8$）处 $\theta = \varphi - 1, Q = 1$ 的精确极限恒等式：
    $\frac{2}{\sqrt{5}}\left|1 - \varphi + \frac{3}{8}\right| = 1 - \frac{7}{4\sqrt{5}}$。 -/
theorem b2_case2_sk_Q1_limit :
    (2 / Real.sqrt 5) * |1 - φ + (3 : ℝ) / 8| = 1 - 7 / (4 * Real.sqrt 5) := by
  have h5_pos := sqrt5_pos
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt h5_pos
  have hneg : 1 - φ + (3 : ℝ) / 8 < 0 := by unfold φ; linarith [four_sqrt5_bounds.1]
  rw [abs_of_neg hneg]
  unfold φ
  field_simp [h5_ne]; ring

/-- 大商位置 $m = s_k, t_k$（$r \in \{3/8, 5/8\}$）处 $\theta = \varphi - 1$、$2 \le Q \le A - 1$
    的通用凹二次下界：
    $(A + r - Q - (\varphi - 1))(Q - \varphi + r)
     \ge (A - 2 + r - (\varphi - 1))(2 - \varphi + r)$。 -/
theorem b2_case2_sub1_quadratic_ge {A Q r : ℝ} (hQ1 : 2 ≤ Q) (hQ2 : Q ≤ A - 1) :
    (A - 2 + r - (φ - 1)) * (2 - φ + r) ≤
      (A + r - Q - (φ - 1)) * (Q - φ + r) := by
  have hdiff : (A + r - Q - (φ - 1)) * (Q - φ + r) -
      (A - 2 + r - (φ - 1)) * (2 - φ + r) = (Q - 2) * (A - 1 - Q) := by ring
  nlinarith

/-- 大商位置 $m = s_k, t_k$ 处高度 $\ge 2\sqrt{5}$（$\theta \notin \{\varphi-1, 2-\varphi\}$）
    的通用凹二次下界：对 $2 \le Q \le A - 1$ 与 $r \ge 3/8$，
    $(A - Q - (1 - r))(Q - 1 + r) \ge \frac{3}{8}(A - 2 + r)$。 -/
theorem b2_case2_sub3_quadratic_ge {A Q r : ℝ}
    (hr : (3 : ℝ) / 8 ≤ r) (hQ1 : 2 ≤ Q) (hQ2 : Q ≤ A - 1) :
    ((3 : ℝ) / 8) * (A - 2 + r) ≤ (A - Q - (1 - r)) * (Q - 1 + r) := by
  have hdiff : (A - Q - (1 - r)) * (Q - 1 + r) - r * (A - 2 + r) =
      (A - 1 - Q) * (Q - 1) := by ring
  have hA2 : 0 ≤ A - 2 + r := by linarith
  nlinarith

end GoldenOrbitB2Rigidity
