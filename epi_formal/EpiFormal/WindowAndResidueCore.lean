import Mathlib

open Real Finset
open scoped BigOperators

namespace WindowAndResidueCore

/-!
# §7 Hermite 窗口约束与模 4 部分商残差维数核心形式化引理
(`WindowAndResidueCore.lean`)

本模块无条件形式化论文二 §7（Theorems 18, 19, 20, 21）的核心代数、概率与分析引理：
1. **Theorem 18**：Hermite 窗口内目标有理数 $m/n$ 的终端连分母范围 $(T/3, T/2)$、追加部分商 $4$ 后的首次跨阈值区间 $(4T/3, 5T/2)$，以及有界增量 $r_j = m_j$ 构造中终端部分商的可选区间长度 $\frac{7T}{6u_*}$。
2. **Theorem 19**：Gauss–Kuzmin 型条件密度积分恒等式、条件概率一致下界 $\frac{H_j}{2H_{j+1}}$，以及指示变量指数矩单步收缩不等式 $e^{-1}p + (1-p) \le \exp(-(1-e^{-1})p_0)$。
3. **Theorem 20**：发散窗口计数 $r_j \ge \eta\log j$ 构造中有理数 $m/n \in (2,3)$ 的严格包络与终端连分母边界。
4. **Theorem 21**：模 $4$ 偏移映射精确落入字母表 $\mathcal{A} = \{d \ge 1 : d \equiv 1 \pmod 4\}$、尾部间隙比恒等式与 $\le 10/3$ 上界、前缀恢复导数因子范围 $[1/(4q^2), 1/q^2]$ 与总双 Lipschitz 常数 $40/3$、`residue_certificate.py` 整数幂证书的有理幂包络可靠性定理，以及有限转移矩阵的次/超特征向量迭代界。
-/

/-! ## 1. Theorem 18：Hermite 窗口奇偶与有界增量定理核心引理 -/

/-- **Theorem 18 终端分母边界引理**：
当 $0 < u, 0 < T, 0 \le v \le u/4$，且 $m \in [0.34 T/u, 0.36 T/u]$、$n \in [0.20 T/u, 0.22 T/u]$ 时，
终端分母 $t = m u + n v$ 严格满足 $T / 3 < t < T / 2$。 -/
theorem thm18_terminal_denom_bounds
    (u v T m n : ℝ)
    (hu : 0 < u) (hT : 0 < T)
    (hv0 : 0 ≤ v) (hvu : v ≤ u / 4)
    (hm1 : (17 : ℝ) / 50 * (T / u) ≤ m) (hm2 : m ≤ (9 : ℝ) / 25 * (T / u))
    (hn1 : (1 : ℝ) / 5 * (T / u) ≤ n) (hn2 : n ≤ (11 : ℝ) / 50 * (T / u)) :
    T / 3 < m * u + n * v ∧ m * u + n * v < T / 2 := by
  have hTu : (T / u) * u = T := div_mul_cancel₀ T (ne_of_gt hu)
  have hmu1 : (17 : ℝ) / 50 * T ≤ m * u := by nlinarith
  have hmu2 : m * u ≤ (9 : ℝ) / 25 * T := by nlinarith
  have hnu1 : (1 : ℝ) / 5 * T ≤ n * u := by nlinarith
  have hnu2 : n * u ≤ (11 : ℝ) / 50 * T := by nlinarith
  have hn0 : 0 ≤ n := by nlinarith
  have hnv0 : 0 ≤ n * v := mul_nonneg hn0 hv0
  have hnv2 : n * v ≤ (11 : ℝ) / 200 * T := by nlinarith
  constructor <;> linarith

/-- **Theorem 18 追加部分商 $4$ 跨阈值与停止柱集不变式引理**：
若终端分母满足 $T / 3 < t < T / 2$ 且前一分母满足 $0 \le t' \le t$，
则追加部分商 $4$ 后的新分母 $q_{\mathrm{new}} = 4 t + t'$ 严格满足 $4 T / 3 < 4 t + t' < 5 T / 2$。 -/
theorem thm18_append_four_crosses
    (T t t' : ℝ)
    (ht1 : T / 3 < t) (ht2 : t < T / 2)
    (ht'0 : 0 ≤ t') (ht't : t' ≤ t) :
    4 * T / 3 < 4 * t + t' ∧ 4 * t + t' < 5 * T / 2 := by
  constructor <;> linarith

/-- **Theorem 18 有界增量 $r_j = m_j$ 构造的跨阈值与可选区间长度引理**：
若 $0 < u_* < T$，$0 \le v_* \le u_*$，且终端部分商 $a$ 满足
$(4T/3 - v_*)/u_* \le a \le (5T/2 - v_*)/u_*$，则新分母 $a u_* + v_* \in [4T/3, 5T/2]$，
且可选区间长度恒等于 $\frac{7T}{6u_*}$。 -/
theorem thm18_prescribed_count_crossing
    (T u_star v_star a : ℝ)
    (hu : 0 < u_star) (_hT : u_star < T)
    (_hv0 : 0 ≤ v_star) (_hvu : v_star ≤ u_star)
    (ha1 : (4 * T / 3 - v_star) / u_star ≤ a)
    (ha2 : a ≤ (5 * T / 2 - v_star) / u_star) :
    (4 * T / 3 ≤ a * u_star + v_star ∧ a * u_star + v_star ≤ 5 * T / 2) ∧
      ((5 * T / 2 - v_star) / u_star - (4 * T / 3 - v_star) / u_star = 7 * T / (6 * u_star)) := by
  have hu_ne : u_star ≠ 0 := ne_of_gt hu
  have h1 : 4 * T / 3 - v_star ≤ a * u_star := (div_le_iff₀ hu).mp ha1
  have h2 : a * u_star ≤ 5 * T / 2 - v_star := (le_div_iff₀ hu).mp ha2
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  field_simp
  ring

/-! ## 2. Theorem 19：几乎处处短窗口出现频率 $\ge c\log J$ 定理核心引理 -/

/-- **Theorem 19 Gauss–Kuzmin 型条件密度积分恒等式**：
验证 $\frac{q(q+q')}{q+q'} - \frac{q(q+q')}{Aq+q'} = \frac{(A-1)q^2}{Aq+q'}$、
$\frac{q(q+q')}{q} - \frac{q(q+q')}{Aq+q'} = \frac{((A-1)q + q')(q+q')}{Aq+q'}$
以及 $1 - \frac{A-1}{Aq+q'} q = \frac{q+q'}{Aq+q'}$。 -/
theorem thm19_cond_prob_integral_identity
    (q q' A : ℝ)
    (hq : 0 < q) (hq' : 0 ≤ q') (hA : 0 < A) :
    (q * (q + q') / (q + q') - q * (q + q') / (A * q + q') =
      (A - 1) * q ^ 2 / (A * q + q')) ∧
    (q * (q + q') / q - q * (q + q') / (A * q + q') =
      ((A - 1) * q + q') * (q + q') / (A * q + q')) ∧
    (1 - (A - 1) / (A * q + q') * q = (q + q') / (A * q + q')) := by
  have hq_ne : q ≠ 0 := ne_of_gt hq
  have hqq'_pos : 0 < q + q' := by linarith
  have hqq'_ne : q + q' ≠ 0 := ne_of_gt hqq'_pos
  have hAq_pos : 0 < A * q + q' := by nlinarith
  have hAq_ne : A * q + q' ≠ 0 := ne_of_gt hAq_pos
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring

/-- **Theorem 19 条件概率一致下界引理**：
当 $0 < H_j < q$，$0 \le q' \le q$，且 $1 \le A \le \frac{2 H_{j+1}}{H_j}$ 时，
条件概率下界满足 $\frac{H_j}{2 H_{j+1}} \le \frac{1}{A} \le \frac{q + q'}{A q + q'}$。 -/
theorem thm19_cond_prob_lower_bound
    (Hj Hj1 q q' A : ℝ)
    (hHj : 0 < Hj) (hq : Hj < q)
    (hq'0 : 0 ≤ q') (_hq'q : q' ≤ q)
    (hA1 : 1 ≤ A) (hA2 : A ≤ 2 * Hj1 / Hj) :
    Hj / (2 * Hj1) ≤ 1 / A ∧ 1 / A ≤ (q + q') / (A * q + q') := by
  have hA_pos : 0 < A := by linarith
  have hAHj : A * Hj ≤ 2 * Hj1 := (le_div_iff₀ hHj).mp hA2
  have h2Hj1_pos : 0 < 2 * Hj1 := by nlinarith
  have hAq_pos : 0 < A * q + q' := by nlinarith
  constructor
  · rw [div_le_div_iff₀ h2Hj1_pos hA_pos]
    nlinarith
  · rw [div_le_div_iff₀ hA_pos hAq_pos]
    nlinarith

/-- **Theorem 19 指示随机变量指数矩单步收缩引理**：
对任意条件概率 $p \ge p_0 \ge 0$，单步条件指数矩满足
$e^{-1} p + (1 - p) \le 1 - (1 - e^{-1}) p_0 \le \exp(-(1 - e^{-1}) p_0)$。 -/
theorem thm19_exp_moment_step_le
    (p p0 : ℝ)
    (_hp0 : 0 ≤ p0) (hpp0 : p0 ≤ p) :
    Real.exp (-1) * p + (1 - p) ≤ 1 - (1 - Real.exp (-1)) * p0 ∧
      1 - (1 - Real.exp (-1)) * p0 ≤ Real.exp (-(1 - Real.exp (-1)) * p0) := by
  have hexp_le_one : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hsub_nonneg : 0 ≤ 1 - Real.exp (-1) := by linarith
  constructor
  · nlinarith
  · have hexp := Real.add_one_le_exp (-(1 - Real.exp (-1)) * p0)
    linarith

/-! ## 3. Theorem 20：发散窗口计数 $r_j \ge \eta\log j$ 满维数定理核心引理 -/

/-- **Theorem 20 目标有理数 $m/n \in (2, 3)$ 包络引理**：
若 $R > 0$ 且 $0.34 R \le m \le 0.35 R$，$0.12 R \le n \le 0.13 R$，
则 $2 < m / n < 3$（从而 $\lfloor m/n \rfloor = 2$，恰有两个奇偶相反的连分数展开）。 -/
theorem thm20_rational_between_two_and_three
    (R m n : ℝ)
    (hR : 0 < R)
    (hm1 : (34 : ℝ) / 100 * R ≤ m) (hm2 : m ≤ (35 : ℝ) / 100 * R)
    (hn1 : (12 : ℝ) / 100 * R ≤ n) (hn2 : n ≤ (13 : ℝ) / 100 * R) :
    2 < m / n ∧ m / n < 3 := by
  have hn_pos : 0 < n := by linarith
  constructor
  · rw [lt_div_iff₀ hn_pos]
    linarith
  · rw [div_lt_iff₀ hn_pos]
    linarith

/-- **Theorem 20 终端分母与跨阈值边界引理**：
若 $0 < u'$, $0 < T$, $0 \le v' \le u'$, $0.34 (T/u') \le m \le 0.35 (T/u')$,
$0.12 (T/u') \le n \le 0.13 (T/u')$，且前一分母 $0 \le t' \le m u' + n v'$，
则终端分母 $t = m u' + n v'$ 严格满足 $T / 3 < t < T / 2$，且追加部分商 $4$ 后满足
$4 T / 3 < 4 t + t' < 5 T / 2$。 -/
theorem thm20_terminal_denom_bounds
    (u' v' T m n t' : ℝ)
    (hu' : 0 < u') (hT : 0 < T)
    (hv'0 : 0 ≤ v') (hv'u : v' ≤ u')
    (hm1 : (34 : ℝ) / 100 * (T / u') ≤ m) (hm2 : m ≤ (35 : ℝ) / 100 * (T / u'))
    (hn1 : (12 : ℝ) / 100 * (T / u') ≤ n) (hn2 : n ≤ (13 : ℝ) / 100 * (T / u'))
    (ht'0 : 0 ≤ t') (ht't : t' ≤ m * u' + n * v') :
    let t := m * u' + n * v'
    (T / 3 < t ∧ t < T / 2) ∧ (4 * T / 3 < 4 * t + t' ∧ 4 * t + t' < 5 * T / 2) := by
  dsimp only
  have hTu : (T / u') * u' = T := div_mul_cancel₀ T (ne_of_gt hu')
  have hmu1 : (34 : ℝ) / 100 * T ≤ m * u' := by nlinarith
  have hmu2 : m * u' ≤ (35 : ℝ) / 100 * T := by nlinarith
  have hnu1 : (12 : ℝ) / 100 * T ≤ n * u' := by nlinarith
  have hnu2 : n * u' ≤ (13 : ℝ) / 100 * T := by nlinarith
  have hn0 : 0 ≤ n := by nlinarith
  have hnv0 : 0 ≤ n * v' := mul_nonneg hn0 hv'0
  have hnv2 : n * v' ≤ (13 : ℝ) / 100 * T := by nlinarith
  have ht1 : T / 3 < m * u' + n * v' := by linarith
  have ht2 : m * u' + n * v' < T / 2 := by linarith
  exact ⟨⟨ht1, ht2⟩, thm18_append_four_crosses T (m * u' + n * v') t' ht1 ht2 ht'0 ht't⟩

/-! ## 4. Theorem 21：模 4 部分商残差集双 Lipschitz 与整数证书可靠性引理 -/

/-- **Theorem 21 模 4 偏移投射引理**：
对任意正整数 $d \ge 1$，令偏移 $c = (d - 1) \bmod 4$，则 $c \in \{0, 1, 2, 3\}$，
且 $d - c \ge 1$、$(d - c) \bmod 4 = 1$（即精确落入固定字母表 $\mathcal{A} = \{1, 5, 9, \dots\}$）。 -/
theorem thm21_shift_mod4_mem_alphabet
    (d : ℕ) (hd : 1 ≤ d) :
    let c := (d - 1) % 4
    c < 4 ∧ 1 ≤ d - c ∧ (d - c) % 4 = 1 := by
  dsimp only
  omega

/-- **Theorem 21 尾部距离比恒等式**：
对满足 $1 \le a$ 且 $a + 4 \le b$ 的部分商 $a, b$，尾部包络与内部间隙之比满足
$\frac{1/a - 1/(b+1)}{1/(a+1) - 1/b} = \frac{b - a + 1}{b - a - 1} \cdot \frac{(a + 1)b}{a(b + 1)}$。 -/
theorem thm21_tail_distance_ratio_identity
    (a b : ℝ) (ha : 1 ≤ a) (hab : a + 4 ≤ b) :
    (1 / a - 1 / (b + 1)) / (1 / (a + 1) - 1 / b) =
      ((b - a + 1) / (b - a - 1)) * (((a + 1) * b) / (a * (b + 1))) := by
  have ha_ne : a ≠ 0 := by linarith
  have ha1_ne : a + 1 ≠ 0 := by linarith
  have hb_ne : b ≠ 0 := by linarith
  have hb1_ne : b + 1 ≠ 0 := by linarith
  have hba_ne : b - a - 1 ≠ 0 := by linarith
  have hnum : 1 / a - 1 / (b + 1) = (b - a + 1) / (a * (b + 1)) := by
    field_simp
    ring
  have hden : 1 / (a + 1) - 1 / b = (b - a - 1) / ((a + 1) * b) := by
    field_simp
    ring
  rw [hnum, hden]
  field_simp

/-- **Theorem 21 尾部距离比一致上界 $\le 10/3$ 引理**：
当 $1 \le a$ 且 $a + 4 \le b$（即 $a \equiv b \pmod 4$ 且 $a < b$）时，
尾部距离比一致满足 $\frac{1/a - 1/(b+1)}{1/(a+1) - 1/b} \le \frac{10}{3}$。 -/
theorem thm21_tail_distance_ratio_le
    (a b : ℝ) (ha : 1 ≤ a) (hab : a + 4 ≤ b) :
    (1 / a - 1 / (b + 1)) / (1 / (a + 1) - 1 / b) ≤ 10 / 3 := by
  rw [thm21_tail_distance_ratio_identity a b ha hab]
  have hba_pos : 0 < b - a - 1 := by linarith
  have hab_pos : 0 < a * (b + 1) := by nlinarith
  have h1 : (b - a + 1) / (b - a - 1) ≤ 5 / 3 := by
    rw [div_le_div_iff₀ hba_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have h2 : ((a + 1) * b) / (a * (b + 1)) ≤ 2 := by
    rw [div_le_iff₀ hab_pos]
    nlinarith
  have h2_nonneg : 0 ≤ ((a + 1) * b) / (a * (b + 1)) := by
    apply div_nonneg <;> nlinarith
  calc
    ((b - a + 1) / (b - a - 1)) * (((a + 1) * b) / (a * (b + 1)))
        ≤ (5 / 3) * 2 := mul_le_mul h1 h2 h2_nonneg (by norm_num)
    _ = 10 / 3 := by norm_num

/-- **Theorem 21 前缀导数因子与总双 Lipschitz 常数 $40/3$ 引理**：
对任意前缀连分母 $q > 0, 0 \le q' \le q$ 及尾点 $x \in [0, 1]$，
前缀雅可比因子满足 $\frac{1}{4q^2} \le \frac{1}{(q + x q')^2} \le \frac{1}{q^2}$；
结合尾部距离比 $\le 10/3$，恢复长度为 $N$ 的有限前缀后的总双 Lipschitz 失真常数上界为 $4 \cdot \frac{10}{3} = \frac{40}{3}$。 -/
theorem thm21_prefix_factor_bounds
    (q q' x r_tail : ℝ)
    (hq : 0 < q) (hq'0 : 0 ≤ q') (hq'q : q' ≤ q)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (_hr0 : 0 ≤ r_tail) (hr : r_tail ≤ 10 / 3) :
    (1 / (4 * q ^ 2) ≤ 1 / (q + x * q') ^ 2 ∧ 1 / (q + x * q') ^ 2 ≤ 1 / q ^ 2) ∧
      ((1 / q ^ 2) / (1 / (4 * q ^ 2)) * r_tail ≤ 40 / 3) := by
  have hq2_pos : 0 < q ^ 2 := sq_pos_of_pos hq
  have h4q2_pos : 0 < 4 * q ^ 2 := by positivity
  have hqx_ge : q ≤ q + x * q' := by
    have : 0 ≤ x * q' := mul_nonneg hx0 hq'0
    linarith
  have hqx_le : q + x * q' ≤ 2 * q := by nlinarith
  have hqx_pos : 0 < q + x * q' := by linarith
  have hqx2_pos : 0 < (q + x * q') ^ 2 := sq_pos_of_pos hqx_pos
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [div_le_div_iff₀ h4q2_pos hqx2_pos]
    nlinarith
  · rw [div_le_div_iff₀ hqx2_pos hq2_pos]
    nlinarith
  · have hq2_ne : q ^ 2 ≠ 0 := ne_of_gt hq2_pos
    have hratio : (1 / q ^ 2) / (1 / (4 * q ^ 2)) = 4 := by
      field_simp
    rw [hratio]
    linarith

/-- **Theorem 21 整数幂算术证书可靠性定理 (`residue_certificate.py`)**：
若正实数 $L, U, S, y, z > 0$ 与正整数 $m, d \ge 1$ 满足精确幂不等式
$L^d y^m \le S^d z^m \le U^d y^m$，
则有理幂 $(z/y)^{m/d} = (y/z)^{-m/d}$ 严格被包络在区间 $[L/S, U/S]$ 内：
$\frac{L}{S} \le \left(\frac{z}{y}\right)^{m/d} \le \frac{U}{S}$。 -/
theorem thm21_integer_certificate_power_enclosure
    (L U S y z : ℝ) (m d : ℕ)
    (_hL : 0 < L) (_hU : 0 < U) (hS : 0 < S)
    (hy : 0 < y) (hz : 0 < z)
    (_hm : 1 ≤ m) (hd : 1 ≤ d)
    (hlow : L ^ d * y ^ m ≤ S ^ d * z ^ m)
    (hhigh : S ^ d * z ^ m ≤ U ^ d * y ^ m) :
    L / S ≤ (z / y) ^ ((m : ℝ) / (d : ℝ)) ∧
      (z / y) ^ ((m : ℝ) / (d : ℝ)) ≤ U / S := by
  have hd_ne : d ≠ 0 := by omega
  have hdR_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_ne
  have hzy_pos : 0 < z / y := div_pos hz hy
  have hr_pos : 0 < (z / y) ^ ((m : ℝ) / (d : ℝ)) := Real.rpow_pos_of_pos hzy_pos _
  have hSd_pos : 0 < S ^ d := pow_pos hS d
  have hym_pos : 0 < y ^ m := pow_pos hy m
  have hSzym_pos : 0 < S ^ d * y ^ m := mul_pos hSd_pos hym_pos
  have hr_pow : ((z / y) ^ ((m : ℝ) / (d : ℝ))) ^ d = z ^ m / y ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hzy_pos), div_mul_cancel₀ _ hdR_ne,
      Real.rpow_natCast, div_pow]
  constructor
  · apply le_of_pow_le_pow_left₀ hd_ne (le_of_lt hr_pos)
    rw [div_pow, hr_pow, div_le_div_iff₀ hSd_pos hym_pos]
    linarith
  · have hUS_nonneg : 0 ≤ U / S := div_nonneg (le_of_lt _hU) (le_of_lt hS)
    apply le_of_pow_le_pow_left₀ hd_ne hUS_nonneg
    rw [div_pow, hr_pow, div_le_div_iff₀ hym_pos hSd_pos]
    linarith

/-- **Theorem 21 转移矩阵次/超特征向量迭代界定理**：
设有限指标集 $\iota$ 上的非负矩阵 $M_{i,j} \ge 0$ 与正向量 $v_i \in [v_{\min}, v_{\max}]$ ($0 < v_{\min} \le v_{\max}$)
满足逐点次特征向量条件 $\sum_j M_{i,j} v_j \le \rho_{\mathrm{up}} v_i$ ($\rho_{\mathrm{up}} \ge 0$)
及超特征向量条件 $\rho_{\mathrm{low}} v_i \le \sum_j M_{i,j} v_j$ ($\rho_{\mathrm{low}} \ge 0$)，
则对任意 $i$，行和 $\sum_j M_{i,j} \cdot 1$ 满足一致双边包络：
$\rho_{\mathrm{low}} \frac{v_{\min}}{v_{\max}} \le \sum_j M_{i,j} \le \rho_{\mathrm{up}} \frac{v_{\max}}{v_{\min}}$。 -/
theorem thm21_transfer_operator_sub_super_iteration
    {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (v : ι → ℝ)
    (vmin vmax ρ_low ρ_up : ℝ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hv_low : ∀ i, vmin ≤ v i)
    (hv_high : ∀ i, v i ≤ vmax)
    (hvmin : 0 < vmin) (hvmax : 0 < vmax)
    (hρ_low : 0 ≤ ρ_low) (hρ_up : 0 ≤ ρ_up)
    (hsuper : ∀ i, ρ_low * v i ≤ ∑ j, M i j * v j)
    (hsub : ∀ i, ∑ j, M i j * v j ≤ ρ_up * v i)
    (i : ι) :
    ρ_low * (vmin / vmax) ≤ ∑ j, M i j ∧ ∑ j, M i j ≤ ρ_up * (vmax / vmin) := by
  have hsum_low : (∑ j, M i j) * vmin ≤ ∑ j, M i j * v j := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hv_low j) (hM i j))
  have hsum_high : ∑ j, M i j * v j ≤ (∑ j, M i j) * vmax := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hv_high j) (hM i j))
  have hvi_low := hv_low i
  have hvi_high := hv_high i
  have hsuper_i := hsuper i
  have hsub_i := hsub i
  constructor
  · rw [ ← mul_div_assoc, div_le_iff₀ hvmax]
    have : ρ_low * vmin ≤ ρ_low * v i := mul_le_mul_of_nonneg_left hvi_low hρ_low
    linarith
  · rw [← mul_div_assoc, le_div_iff₀ hvmin]
    have : ρ_up * v i ≤ ρ_up * vmax := mul_le_mul_of_nonneg_left hvi_high hρ_up
    linarith

#print axioms thm18_terminal_denom_bounds
#print axioms thm18_append_four_crosses
#print axioms thm18_prescribed_count_crossing
#print axioms thm19_cond_prob_integral_identity
#print axioms thm19_cond_prob_lower_bound
#print axioms thm19_exp_moment_step_le
#print axioms thm20_rational_between_two_and_three
#print axioms thm20_terminal_denom_bounds
#print axioms thm21_shift_mod4_mem_alphabet
#print axioms thm21_tail_distance_ratio_identity
#print axioms thm21_tail_distance_ratio_le
#print axioms thm21_prefix_factor_bounds
#print axioms thm21_integer_certificate_power_enclosure
#print axioms thm21_transfer_operator_sub_super_iteration

end WindowAndResidueCore
