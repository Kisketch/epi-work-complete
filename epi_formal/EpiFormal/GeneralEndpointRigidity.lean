import Mathlib
import EpiFormal.GoldenOrbitRigidity
import EpiFormal.GoldenOrbitB2Rigidity

/-!
# Path 2A：共轭正性、一般有理端点四重算术刚性与 $B = 3, 4, 5, 6$ 谱隙核心

本模块形式化论文一 §8 Path 2A 的以下核心命题、引理与算术/谱分离定理（全部无条件，
零 `sorry`，仅依赖 Lean 基础公理 `[propext, Classical.choice, Quot.sound]`）：

1. **`prop:conjugate-positivity`**：
   - `cfTail`、`cfTailOne`、`cfConjTailOne` 及 $2\times 2$ 连分数矩阵 `cfMatrix`；
   - `eta_conj_ge_inv_sq_of_gt_one`：对一切终为 $\overline{1}$ 的连分数
     $\eta = [a_0; a_1, \dots, a_k, \overline{1}] > 1$（$a_0 \ge 1$，尾部各项 $\ge 1$，
     且 $(k = 0 \land a_0 \ge 2)$ 或 $(k \ge 1 \land a_k \ge 2)$），其共轭满足
     $\eta' \ge \frac{3 - \sqrt{5}}{2} = \varphi^{-2} > 0$；
   - `eta_conj_add_pos_gt_abs`：对任意 $z > 0$ 恒有 $|\eta' + z| = \eta' + z > |\eta'|$。

2. **`lem:general-endpoint-rigidity`（全部四部分及精确代数恒等式）**：
   - `xi1_xi2Conj_identity`、`Muv_norm_identity`、`mobius_ratio_identity`、
     `ratio_eq_Muv_sub_div`；
   - Part (1)：`inert_legendreSym_five_eq_neg_one`、
     `inert_prime_not_dvd_zphiNorm`（含对任意奇素数 $p \equiv 2, 3 \pmod{5}$ 的
     二次互反律证明及 $p = 2, 3, 7$ 显式实例）；
   - Part (2)：`even_D_rigidity` 与 `even_D_rigidity_functional`（偶 $D = 2 d_0$
     情形下 $2 \mid M_{u,v}$、$m^2 - 5 d_0^2 = N(\xi_1) N(\xi_2)$、$m \equiv d_0 + 1 \pmod 2$
     及惰性素因子排除）；
   - Part (3)：`mod_2D_sieve_q`、`mod_2D_sieve_p`、`mod_2d_sieve_special`（模 $2D$/$2d_0$
     同余筛及其在 $(2d_0 / q_1, 0)$ 处的特化 $m \equiv d_0 - \varepsilon q_1 N(\gamma) \pmod{2 d_0}$）；
   - Part (4)：`Muv_norm_ne_zero` 与 `zphiNorm_xi2_dvd_norm_quot`（非零范数整除性）。

3. **$B = 3, 4, 5, 6$ 算术筛与谱隙核心定理**：
   - $B = 3$（$D = 18, d = 9$）：`b3_inert_three_not_dvd_m` 与 `b3_spectral_gap`；
   - $B = 4$（$D = 32, d = 16$）：模 $16$ 乘法子群 $\{1, 7, 9, 15\}$ 封闭性、
     `b4_mod16_excludes_37` 与 `b4_spectral_gap`；
   - $B = 5$（$D = 50, d = 25$）：`b5_even_m` 与 `b5_spectral_gap`；
   - $B = 6$（$D = 72, d = 36$）：`b6_inert_three_not_dvd_m` 与 `b6_spectral_gap`。
-/

namespace GeneralEndpointRigidity

open Real GoldenOrbitRigidity GoldenOrbitB2Rigidity

/-! ### 1. `prop:conjugate-positivity`：$\eta \in E_\varphi \cap (1, \infty) \setminus \{\varphi\}$ 的共轭正性与精确下界 -/

/-- 将实数 `x` 接在有限部分商列表末尾的连分数求值 `[l_0; l_1, ..., l_{k-1}, x]`。 -/
noncomputable def cfTail (x : ℝ) : List ℕ → ℝ
  | [] => x
  | a :: as => (a : ℝ) + 1 / cfTail x as

/-- 终为 `1` 的正则连分数 `[a_0; tail, 1, 1, ...]` 的实数值。 -/
noncomputable def cfTailOne (a0 : ℕ) (tail : List ℕ) : ℝ :=
  (a0 : ℝ) + 1 / cfTail φ tail

/-- 终为 `1` 的正则连分数 `[a_0; tail, 1, 1, ...]` 的 Galois 共轭值（以 `φ'` 替换 `φ`）。 -/
noncomputable def cfConjTailOne (a0 : ℕ) (tail : List ℕ) : ℝ :=
  (a0 : ℝ) + 1 / cfTail φ' tail

/-- 部分商列表对应的 $2\times 2$ 整数矩阵 `(a, b, c, d)`，对应 $\begin{pmatrix} a & b \\ c & d \end{pmatrix}$。 -/
def cfMatrix : List ℕ → ℤ × ℤ × ℤ × ℤ
  | [] => (1, 0, 0, 1)
  | n :: ns =>
      let (a, b, c, d) := cfMatrix ns
      ((n : ℤ) * a + c, (n : ℤ) * b + d, a, b)

lemma inv_phi_eq : 1 / φ = φ - 1 := by
  have h5_sq := sqrt5_sq
  have hφ_ne : φ ≠ 0 := by
    unfold φ; linarith [sqrt5_pos]
  rw [div_eq_iff hφ_ne]
  unfold φ
  ring_nf; rw [h5_sq]; ring

lemma inv_phi'_eq : 1 / φ' = φ' - 1 := by
  have h5_sq := sqrt5_sq
  have hφ'_ne : φ' ≠ 0 := by
    unfold φ'; linarith [sqrt5_bounds.1]
  rw [div_eq_iff hφ'_ne]
  unfold φ'
  ring_nf; rw [h5_sq]; ring

lemma inv_sq_goldenRatio_eq : (3 - Real.sqrt 5) / 2 = Real.goldenRatio ^ (-2 : ℤ) := by
  have h5_sq := sqrt5_sq
  rw [zpow_neg, zpow_two, Real.goldenRatio]
  symm
  apply inv_eq_of_mul_eq_one_right
  ring_nf
  rw [show Real.sqrt 5 ^ 3 = Real.sqrt 5 * Real.sqrt 5 ^ 2 by ring, h5_sq]
  ring

lemma inv_sq_pos : (0 : ℝ) < (3 - Real.sqrt 5) / 2 := by
  have hlt : Real.sqrt 5 < 3 := lt_trans sqrt5_bounds.2 (by norm_num)
  linarith

lemma cfTail_phi_gt_one :
    ∀ (l : List ℕ), (∀ x ∈ l, 1 ≤ x) → 1 < cfTail φ l := by
  intro l hl
  induction l with
  | nil =>
      unfold cfTail φ
      linarith [sqrt5_bounds.1]
  | cons a as ih =>
      have ha : 1 ≤ a := hl a (by simp)
      have has : ∀ x ∈ as, 1 ≤ x := fun x hx => hl x (by simp [hx])
      have hsub : 1 < cfTail φ as := ih has
      have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have hpos : 0 < 1 / cfTail φ as := div_pos one_pos (lt_trans zero_lt_one hsub)
      unfold cfTail
      linarith

lemma cfTail_phi'_ge_inv_sq_of_last_ge_two :
    ∀ (l : List ℕ) (hne : l ≠ []),
      (∀ x ∈ l, 1 ≤ x) → 2 ≤ l.getLast hne →
      (3 - Real.sqrt 5) / 2 ≤ cfTail φ' l ∧ 0 < cfTail φ' l := by
  intro l
  induction l with
  | nil =>
      intro hne _ _
      exact False.elim (hne rfl)
  | cons a as ih =>
      intro hne hl hlast
      cases as with
      | nil =>
          have ha2 : 2 ≤ a := by simpa using hlast
          have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
          have hval : cfTail φ' [a] = (a : ℝ) - 1 + φ' := by
            simp only [cfTail]
            rw [inv_phi'_eq]
            ring
          have h1phi' : 1 + φ' = (3 - Real.sqrt 5) / 2 := by
            unfold φ'; ring
          have hge : (3 - Real.sqrt 5) / 2 ≤ cfTail φ' [a] := by
            linarith
          exact ⟨hge, lt_of_lt_of_le inv_sq_pos hge⟩
      | cons b bs =>
          have hne' : b :: bs ≠ [] := List.cons_ne_nil b bs
          have hsub_all : ∀ x ∈ b :: bs, 1 ≤ x := fun x hx => hl x (by simp [hx])
          have hlast' : 2 ≤ (b :: bs).getLast hne' := by
            simpa [List.getLast_cons hne'] using hlast
          have hsub := ih hne' hsub_all hlast'
          have ha : 1 ≤ a := hl a (by simp)
          have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
          have hinv_pos : 0 < 1 / cfTail φ' (b :: bs) := div_pos one_pos hsub.2
          have hge1 : 1 < cfTail φ' (a :: b :: bs) := by
            change 1 < (a : ℝ) + 1 / cfTail φ' (b :: bs)
            linarith
          have hlt1 : (3 - Real.sqrt 5) / 2 < 1 := by
            linarith [sqrt5_bounds.1]
          exact ⟨le_of_lt (lt_trans hlt1 hge1), lt_trans zero_lt_one hge1⟩

/-- 连分数矩阵 `cfMatrix ns` 的行列式恒为 $\pm 1$。 -/
theorem cfMatrix_det (ns : List ℕ) :
    let m := cfMatrix ns
    |m.1 * m.2.2.2 - m.2.1 * m.2.2.1| = 1 := by
  induction ns with
  | nil =>
      simp [cfMatrix]
  | cons n ns ih =>
      rcases h : cfMatrix ns with ⟨a, b, c, d⟩
      rw [h] at ih
      dsimp only at ih ⊢
      simp only [cfMatrix, h]
      have hdet : ((n : ℤ) * a + c) * b - ((n : ℤ) * b + d) * a = -(a * d - b * c) := by ring
      rw [hdet, abs_neg]
      exact ih

lemma cfMatrix_mobius_phi :
    ∀ (l : List ℕ), (∀ x ∈ l, 1 ≤ x) →
      let m := cfMatrix l
      ((m.2.2.1 : ℝ) * φ + (m.2.2.2 : ℝ) ≠ 0) ∧
      ((m.1 : ℝ) * φ + (m.2.1 : ℝ) ≠ 0) ∧
      mobius m.1 m.2.1 m.2.2.1 m.2.2.2 φ = cfTail φ l := by
  intro l
  induction l with
  | nil =>
      intro _
      have hφ_ne : φ ≠ 0 := by unfold φ; linarith [sqrt5_pos]
      simp [cfMatrix, cfTail, mobius, hφ_ne]
  | cons n ns ih =>
      intro hl
      have hn : 1 ≤ n := hl n (by simp)
      have hns : ∀ x ∈ ns, 1 ≤ x := fun x hx => hl x (by simp [hx])
      rcases hmat : cfMatrix ns with ⟨a, b, c, d⟩
      have ih' := ih hns
      rw [hmat] at ih'
      rcases ih' with ⟨hden, hnum, hmob⟩
      simp only [cfMatrix, hmat]
      have hnum_new : (((n : ℤ) * a + c : ℤ) : ℝ) * φ + (((n : ℤ) * b + d : ℤ) : ℝ) =
          (n : ℝ) * ((a : ℝ) * φ + (b : ℝ)) + ((c : ℝ) * φ + (d : ℝ)) := by
        push_cast; ring
      have hmob_new : mobius ((n : ℤ) * a + c) ((n : ℤ) * b + d) a b φ = cfTail φ (n :: ns) := by
        unfold mobius at hmob ⊢
        rw [hnum_new, cfTail, ← hmob]
        field_simp [hnum, hden]
      have h0 : cfTail φ (n :: ns) ≠ 0 :=
        ne_of_gt (lt_trans zero_lt_one (cfTail_phi_gt_one (n :: ns) hl))
      have hnum_new_ne : (((n : ℤ) * a + c : ℤ) : ℝ) * φ + (((n : ℤ) * b + d : ℤ) : ℝ) ≠ 0 := by
        intro hz
        have hmob0 : mobius ((n : ℤ) * a + c) ((n : ℤ) * b + d) a b φ = 0 := by
          unfold mobius; rw [hz, zero_div]
        rw [hmob_new] at hmob0
        exact h0 hmob0
      exact ⟨hnum, hnum_new_ne, hmob_new⟩

lemma cfMatrix_mobius_phi'_of_nonempty :
    ∀ (l : List ℕ) (hne : l ≠ []), (∀ x ∈ l, 1 ≤ x) → 2 ≤ l.getLast hne →
      let m := cfMatrix l
      ((m.2.2.1 : ℝ) * φ' + (m.2.2.2 : ℝ) ≠ 0) ∧
      ((m.1 : ℝ) * φ' + (m.2.1 : ℝ) ≠ 0) ∧
      mobius m.1 m.2.1 m.2.2.1 m.2.2.2 φ' = cfTail φ' l := by
  intro l
  induction l with
  | nil =>
      intro hne _ _
      exact False.elim (hne rfl)
  | cons n ns ih =>
      intro hne hl hlast
      have hφ'_ne : φ' ≠ 0 := by unfold φ'; linarith [sqrt5_bounds.1]
      cases ns with
      | nil =>
          have hval_pos := (cfTail_phi'_ge_inv_sq_of_last_ge_two [n] hne hl hlast).2
          have hmat0 : cfMatrix [n] = ((n : ℤ), 1, 1, 0) := by simp [cfMatrix]
          rw [hmat0]
          have hmob : mobius (n : ℤ) 1 1 0 φ' = (n : ℝ) + 1 / φ' := by
            unfold mobius
            push_cast
            field_simp [hφ'_ne]
            ring
          have hnum_ne : ((n : ℤ) : ℝ) * φ' + (1 : ℤ) ≠ 0 := by
            intro hz
            have h0 : mobius (n : ℤ) 1 1 0 φ' = 0 := by
              unfold mobius; rw [hz, zero_div]
            rw [hmob] at h0
            have : (n : ℝ) + 1 / φ' = cfTail φ' [n] := rfl
            linarith
          exact ⟨by simpa using hφ'_ne, hnum_ne, hmob⟩
      | cons b bs =>
          have hne' : b :: bs ≠ [] := List.cons_ne_nil b bs
          have hsub_all : ∀ x ∈ b :: bs, 1 ≤ x := fun x hx => hl x (by simp [hx])
          have hlast' : 2 ≤ (b :: bs).getLast hne' := by
            simpa [List.getLast_cons hne'] using hlast
          rcases hmat : cfMatrix (b :: bs) with ⟨a, b', c, d⟩
          have ih' := ih hne' hsub_all hlast'
          rw [hmat] at ih'
          rcases ih' with ⟨hden, hnum, hmob⟩
          have hmat_new : cfMatrix (n :: b :: bs) = ((n : ℤ) * a + c, (n : ℤ) * b' + d, a, b') := by
            change (let (a0, b0, c0, d0) := cfMatrix (b :: bs)
              ((n : ℤ) * a0 + c0, (n : ℤ) * b0 + d0, a0, b0)) = _
            rw [hmat]
          rw [hmat_new]
          have hnum_new : (((n : ℤ) * a + c : ℤ) : ℝ) * φ' + (((n : ℤ) * b' + d : ℤ) : ℝ) =
              (n : ℝ) * ((a : ℝ) * φ' + (b' : ℝ)) + ((c : ℝ) * φ' + (d : ℝ)) := by
            push_cast; ring
          have hmob_new : mobius ((n : ℤ) * a + c) ((n : ℤ) * b' + d) a b' φ' =
              cfTail φ' (n :: b :: bs) := by
            unfold mobius at hmob ⊢
            rw [hnum_new, cfTail, ← hmob]
            field_simp [hnum, hden]
          have hpos := (cfTail_phi'_ge_inv_sq_of_last_ge_two (n :: b :: bs) hne hl hlast).2
          have hnum_new_ne : (((n : ℤ) * a + c : ℤ) : ℝ) * φ' + (((n : ℤ) * b' + d : ℤ) : ℝ) ≠ 0 := by
            intro hz
            have h0 : mobius ((n : ℤ) * a + c) ((n : ℤ) * b' + d) a b' φ' = 0 := by
              unfold mobius; rw [hz, zero_div]
            rw [hmob_new] at h0
            linarith
          exact ⟨hnum, hnum_new_ne, hmob_new⟩

/-- 2×2 矩阵表示验证：`cfMatrix (a0 :: tail)` 作用于 `φ` 与 `φ'` 分别给出 `cfTailOne a0 tail` 与 `cfConjTailOne a0 tail`。 -/
theorem cfMatrix_eval_eq (a0 : ℕ) (tail : List ℕ)
    (ha0 : 1 ≤ a0) (htail : ∀ x ∈ tail, 1 ≤ x)
    (hgt : (tail = [] ∧ 2 ≤ a0) ∨ (∃ hne : tail ≠ [], 2 ≤ tail.getLast hne)) :
    let m := cfMatrix (a0 :: tail)
    |m.1 * m.2.2.2 - m.2.1 * m.2.2.1| = 1 ∧
    orbitPt m.1 m.2.1 m.2.2.1 m.2.2.2 = cfTailOne a0 tail ∧
    orbitPtConj m.1 m.2.1 m.2.2.1 m.2.2.2 = cfConjTailOne a0 tail := by
  have hall : ∀ x ∈ a0 :: tail, 1 ≤ x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact ha0
    · exact htail x hmem
  have h1 := cfMatrix_mobius_phi (a0 :: tail) hall
  have h2 : mobius (cfMatrix (a0 :: tail)).1 (cfMatrix (a0 :: tail)).2.1
      (cfMatrix (a0 :: tail)).2.2.1 (cfMatrix (a0 :: tail)).2.2.2 φ' = cfTail φ' (a0 :: tail) := by
    rcases hgt with ⟨rfl, ha2⟩ | ⟨hne, hlast⟩
    · have hne0 : [a0] ≠ [] := List.cons_ne_nil a0 []
      have hlast0 : 2 ≤ ([a0] : List ℕ).getLast hne0 := by simpa using ha2
      exact (cfMatrix_mobius_phi'_of_nonempty [a0] hne0 hall hlast0).2.2
    · have hne0 : a0 :: tail ≠ [] := List.cons_ne_nil a0 tail
      have hlast0 : 2 ≤ (a0 :: tail).getLast hne0 := by
        simpa [List.getLast_cons hne] using hlast
      exact (cfMatrix_mobius_phi'_of_nonempty (a0 :: tail) hne0 hall hlast0).2.2
  refine ⟨cfMatrix_det (a0 :: tail), ?_, ?_⟩
  · simpa [orbitPt, cfTailOne, cfTail] using h1.2.2
  · simpa [orbitPtConj, cfConjTailOne, cfTail] using h2

/-- 命题 `prop:conjugate-positivity`：
    对任意终为 $\overline{1}$ 的连分数 $\eta = [a_0; a_1, \dots, a_k, \overline{1}] > 1$ 且 $\eta \ne \varphi$
    （即 $a_0 \ge 1$，尾部各项 $\ge 1$，且 $k = 0 \implies a_0 \ge 2$、$k \ge 1 \implies a_k \ge 2$），
    恒有 $\eta' \ge \frac{3 - \sqrt{5}}{2} = \varphi^{-2} > 0$，且 $\eta > 1$。 -/
theorem eta_conj_ge_inv_sq_of_gt_one (a0 : ℕ) (tail : List ℕ)
    (ha0 : 1 ≤ a0) (htail : ∀ x ∈ tail, 1 ≤ x)
    (hgt : (tail = [] ∧ 2 ≤ a0) ∨ (∃ hne : tail ≠ [], 2 ≤ tail.getLast hne)) :
    (3 - Real.sqrt 5) / 2 = Real.goldenRatio ^ (-2 : ℤ) ∧
    0 < (3 - Real.sqrt 5) / 2 ∧
    (3 - Real.sqrt 5) / 2 ≤ cfConjTailOne a0 tail ∧
    1 < cfTailOne a0 tail := by
  refine ⟨inv_sq_goldenRatio_eq, inv_sq_pos, ?_, ?_⟩
  · rcases hgt with ⟨rfl, ha2⟩ | ⟨hne, hlast⟩
    · unfold cfConjTailOne cfTail
      rw [inv_phi'_eq]
      have haR : (2 : ℝ) ≤ (a0 : ℝ) := by exact_mod_cast ha2
      unfold φ'
      linarith
    · have hsub := (cfTail_phi'_ge_inv_sq_of_last_ge_two tail hne htail hlast).2
      have haR : (1 : ℝ) ≤ (a0 : ℝ) := by exact_mod_cast ha0
      have hinv : 0 < 1 / cfTail φ' tail := div_pos one_pos hsub
      have hlt1 : (3 - Real.sqrt 5) / 2 < 1 := by linarith [sqrt5_bounds.1]
      unfold cfConjTailOne
      linarith
  · have hsub := cfTail_phi_gt_one tail htail
    have haR : (1 : ℝ) ≤ (a0 : ℝ) := by exact_mod_cast ha0
    have hinv : 0 < 1 / cfTail φ tail := div_pos one_pos (lt_trans zero_lt_one hsub)
    unfold cfTailOne
    linarith

/-- `prop:conjugate-positivity` 推论：对任意 $z > 0$ 恒有 $|\eta' + z| = \eta' + z > |\eta'|$。 -/
theorem eta_conj_add_pos_gt_abs (a0 : ℕ) (tail : List ℕ)
    (ha0 : 1 ≤ a0) (htail : ∀ x ∈ tail, 1 ≤ x)
    (hgt : (tail = [] ∧ 2 ≤ a0) ∨ (∃ hne : tail ≠ [], 2 ≤ tail.getLast hne))
    {z : ℝ} (hz : 0 < z) :
    |cfConjTailOne a0 tail + z| = cfConjTailOne a0 tail + z ∧
    |cfConjTailOne a0 tail| < cfConjTailOne a0 tail + z := by
  have hmain := eta_conj_ge_inv_sq_of_gt_one a0 tail ha0 htail hgt
  have hpos : 0 < cfConjTailOne a0 tail := lt_of_lt_of_le hmain.2.1 hmain.2.2.1
  rw [abs_of_pos (add_pos hpos hz), abs_of_pos hpos]
  exact ⟨rfl, lt_add_of_pos_right _ hz⟩

/-- 等号取在 $\eta = \varphi + 1 = [2; \overline{1}]$：$\eta' = \frac{3 - \sqrt{5}}{2}$。 -/
theorem eta_conj_eq_inv_sq_at_two :
    cfTailOne 2 [] = φ + 1 ∧ cfConjTailOne 2 [] = (3 - Real.sqrt 5) / 2 := by
  constructor
  · unfold cfTailOne cfTail
    rw [inv_phi_eq]
    norm_num
    ring
  · unfold cfConjTailOne cfTail
    rw [inv_phi'_eq]
    unfold φ'
    norm_num
    ring

/-! ### 2. `lem:general-endpoint-rigidity`：一般有理端点四重算术刚性与代数反演 -/

/-- 一般有理端点处分子线性型 $\xi_1 = (p_1 c - q_1 a)\varphi + (p_1 d - q_1 b)$。 -/
noncomputable def xi1 (p1 q1 a b c d : ℤ) : ℝ :=
  ((p1 * c - q1 * a : ℤ) : ℝ) * φ + ((p1 * d - q1 * b : ℤ) : ℝ)

/-- 一般有理端点处分母线性型 $\xi_2 = (q_2 a + p_2 c)\varphi + (q_2 b + p_2 d)$。 -/
noncomputable def xi2 (p2 q2 a b c d : ℤ) : ℝ :=
  ((q2 * a + p2 * c : ℤ) : ℝ) * φ + ((q2 * b + p2 * d : ℤ) : ℝ)

/-- $\xi_2$ 的 Galois 共轭 $\xi_2' = (q_2 a + p_2 c)\varphi' + (q_2 b + p_2 d)$。 -/
noncomputable def xi2Conj (p2 q2 a b c d : ℤ) : ℝ :=
  ((q2 * a + p2 * c : ℤ) : ℝ) * φ' + ((q2 * b + p2 * d : ℤ) : ℝ)

/-- 共轭乘积恒等式：$2 \xi_1 \xi_2' = M_{u,v} - \varepsilon D \sqrt{5}$。 -/
theorem xi1_xi2Conj_identity (p1 q1 p2 q2 a b c d : ℤ) :
    2 * xi1 p1 q1 a b c d * xi2Conj p2 q2 a b c d =
      (M_uv p1 q1 p2 q2 a b c d : ℝ) -
        ((a * d - b * c : ℤ) : ℝ) * ((p1 * q2 + p2 * q1 : ℤ) : ℝ) * Real.sqrt 5 := by
  unfold xi1 xi2Conj
  rw [mul_assoc]
  exact xi1_mul_xi2Conj p1 q1 p2 q2 a b c d

/-- 范数恒等式（当 $|ad-bc|=1$）：
    $M_{u,v}^2 - 5 D^2 = 4 N(\xi_1) N(\xi_2)$。 -/
theorem Muv_norm_identity (p1 q1 p2 q2 a b c d : ℤ) (hdet : |a * d - b * c| = 1) :
    (M_uv p1 q1 p2 q2 a b c d) ^ 2 - 5 * (p1 * q2 + p2 * q1) ^ 2 =
      4 * zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b) *
        zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d) := by
  have hdet_sq : (a * d - b * c) ^ 2 = 1 := by
    have : |a * d - b * c| ^ 2 = 1 ^ 2 := by rw [hdet]
    simpa [sq_abs] using this
  have h := M_uv_norm_identity p1 q1 p2 q2 a b c d
  rw [hdet_sq, mul_one] at h
  exact h

/-- 线性消元恒等式：$q_2 \xi_1 + q_1 \xi_2 = D(c\varphi+d)$ 与 $p_1 \xi_2 - p_2 \xi_1 = D(a\varphi+b)$。 -/
lemma xi1_xi2_linear_elim (p1 q1 p2 q2 a b c d : ℤ) :
    (q2 : ℝ) * xi1 p1 q1 a b c d + (q1 : ℝ) * xi2 p2 q2 a b c d =
      ((p1 * q2 + p2 * q1 : ℤ) : ℝ) * ((c : ℝ) * φ + (d : ℝ)) ∧
    (p1 : ℝ) * xi2 p2 q2 a b c d - (p2 : ℝ) * xi1 p1 q1 a b c d =
      ((p1 * q2 + p2 * q1 : ℤ) : ℝ) * ((a : ℝ) * φ + (b : ℝ)) := by
  unfold xi1 xi2
  push_cast
  constructor <;> ring

/-- 代数反演恒等式：当 $\xi_2 \ne 0$ 且 $D = p_1 q_2 + p_2 q_1 \ne 0$，令 $R := \xi_1 / \xi_2$，
    则 $q_1 + q_2 R \ne 0$ 且 $\eta = \frac{p_1 - p_2 R}{q_1 + q_2 R}$。 -/
theorem mobius_ratio_identity (p1 q1 p2 q2 a b c d : ℤ)
    (hdet : |a * d - b * c| = 1)
    (hD : p1 * q2 + p2 * q1 ≠ 0)
    (hxi2 : xi2 p2 q2 a b c d ≠ 0) :
    let R := xi1 p1 q1 a b c d / xi2 p2 q2 a b c d
    (q1 : ℝ) + (q2 : ℝ) * R ≠ 0 ∧
      orbitPt a b c d = ((p1 : ℝ) - (p2 : ℝ) * R) / ((q1 : ℝ) + (q2 : ℝ) * R) := by
  dsimp only
  have hcd := linear_phi_ne_zero (cd_ne_zero_of_det hdet)
  have hDR : ((p1 * q2 + p2 * q1 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD
  have helim := xi1_xi2_linear_elim p1 q1 p2 q2 a b c d
  have hden : (q1 : ℝ) + (q2 : ℝ) * (xi1 p1 q1 a b c d / xi2 p2 q2 a b c d) =
      ((p1 * q2 + p2 * q1 : ℤ) : ℝ) * ((c : ℝ) * φ + (d : ℝ)) / xi2 p2 q2 a b c d := by
    field_simp [hxi2]
    linarith [helim.1]
  have hnum : (p1 : ℝ) - (p2 : ℝ) * (xi1 p1 q1 a b c d / xi2 p2 q2 a b c d) =
      ((p1 * q2 + p2 * q1 : ℤ) : ℝ) * ((a : ℝ) * φ + (b : ℝ)) / xi2 p2 q2 a b c d := by
    field_simp [hxi2]
    linarith [helim.2]
  have hden_ne : (q1 : ℝ) + (q2 : ℝ) * (xi1 p1 q1 a b c d / xi2 p2 q2 a b c d) ≠ 0 := by
    rw [hden]
    exact div_ne_zero (mul_ne_zero hDR hcd.1) hxi2
  refine ⟨hden_ne, ?_⟩
  rw [hden, hnum]
  unfold orbitPt mobius
  field_simp [hDR, hxi2, hcd.1]

/-- 比值 $R = \xi_1 / \xi_2$ 的有理化显式表达式：$R = \frac{M_{u,v} - \varepsilon D\sqrt{5}}{2 N(\xi_2)}$。 -/
theorem ratio_eq_Muv_sub_div (p1 q1 p2 q2 a b c d : ℤ)
    (hxi2 : xi2 p2 q2 a b c d ≠ 0) (hxi2' : xi2Conj p2 q2 a b c d ≠ 0) :
    xi1 p1 q1 a b c d / xi2 p2 q2 a b c d =
      ((M_uv p1 q1 p2 q2 a b c d : ℝ) -
        ((a * d - b * c : ℤ) : ℝ) * ((p1 * q2 + p2 * q1 : ℤ) : ℝ) * Real.sqrt 5) /
        (2 * (zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d) : ℝ)) := by
  have hN2 : (zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d) : ℝ) =
      xi2 p2 q2 a b c d * xi2Conj p2 q2 a b c d := by
    unfold xi2 xi2Conj
    exact (zphi_mul_conj _ _).symm
  have hN2_ne : (zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d) : ℝ) ≠ 0 := by
    rw [hN2]; exact mul_ne_zero hxi2 hxi2'
  have hmul := xi1_xi2Conj_identity p1 q1 p2 q2 a b c d
  rw [← hmul, hN2]
  field_simp [hxi2, hxi2', hN2_ne]

/-! #### Part (1)：惰性素数非整除性与二次互反律 -/

private lemma mod5_two_not_sq : ∀ r : ZMod 5, ((2 : ℤ) : ZMod 5) ≠ r * r := by decide
private lemma mod5_three_not_sq : ∀ r : ZMod 5, ((3 : ℤ) : ZMod 5) ≠ r * r := by decide

/-- 对任意奇素数 $p \equiv 2, 3 \pmod 5$，由二次互反律得 $\left(\frac{5}{p}\right) = -1$。 -/
theorem inert_legendreSym_five_eq_neg_one {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (h5 : p % 5 = 2 ∨ p % 5 = 3) :
    legendreSym p 5 = -1 := by
  have h5prime : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hqr := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p)
    (by norm_num) hp2
  have hqr' : legendreSym p 5 = legendreSym 5 (p : ℤ) := by simpa using hqr
  rw [hqr', legendreSym.mod 5 (p : ℤ)]
  have hmod : (p : ℤ) % ((5 : ℕ) : ℤ) = 2 ∨ (p : ℤ) % ((5 : ℕ) : ℤ) = 3 := by
    omega
  rcases hmod with hm2 | hm3
  · rw [hm2]
    have hnsq : ¬ IsSquare ((2 : ℤ) : ZMod 5) := by
      rintro ⟨r, hr⟩
      exact mod5_two_not_sq r hr
    exact (legendreSym.eq_neg_one_iff 5).mpr hnsq
  · rw [hm3]
    have hnsq : ¬ IsSquare ((3 : ℤ) : ZMod 5) := by
      rintro ⟨r, hr⟩
      exact mod5_three_not_sq r hr
    exact (legendreSym.eq_neg_one_iff 5).mpr hnsq

/-- 在 `ZMod p` 上，若 $\left(\frac{5}{p}\right) = -1$ 且 $p \ne 2$，则 $(2x+y)^2 = 5y^2 \implies x = 0 \land y = 0$。 -/
lemma zmod_norm_eq_zero_of_inert {p : ℕ} (hp : Nat.Prime p)
    (hp2 : p ≠ 2) (h5 : p % 5 = 2 ∨ p % 5 = 3) (x y : ZMod p)
    (hxy : (2 * x + y) ^ 2 = 5 * y ^ 2) : x = 0 ∧ y = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hleg : legendreSym p 5 = -1 := inert_legendreSym_five_eq_neg_one hp2 h5
  have hp5 : p ≠ 5 := by omega
  have h5_ne0 : ((5 : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : (p : ℤ) ∣ 5 := (ZMod.intCast_zmod_eq_zero_iff_dvd 5 p).mp h0
    have hp_dvd5 : p ∣ 5 := Int.ofNat_dvd.mp hdvd
    have : p = 1 ∨ p = 5 := (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hp_dvd5
    omega
  have hy0 : y = 0 := by
    by_contra hy
    have hsub : (2 * x + y) ^ 2 - ((5 : ℤ) : ZMod p) * y ^ 2 = 0 := by
      push_cast; exact sub_eq_zero.mpr hxy
    have h1 := legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero (p := p) h5_ne0 hy hsub
    omega
  subst hy0
  have h2x0 : (2 * x) ^ 2 = 0 := by simpa using hxy
  have h2x : 2 * x = 0 := sq_eq_zero_iff.mp h2x0
  have h2_ne0 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    have : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).mp hdvd
    omega
  have hx0 : x = 0 := (mul_eq_zero.mp h2x).resolve_left h2_ne0
  exact ⟨hx0, rfl⟩

/-- 显式验证 $p = 3$ 时的 `ZMod 3` 判别条件。 -/
lemma zmod3_norm_eq_zero (x y : ZMod 3) (hxy : (2 * x + y) ^ 2 = 5 * y ^ 2) :
    x = 0 ∧ y = 0 :=
  zmod_norm_eq_zero_of_inert (by norm_num) (by norm_num) (Or.inr rfl) x y hxy

/-- 显式验证 $p = 7$ 时的 `ZMod 7` 判别条件。 -/
lemma zmod7_norm_eq_zero (x y : ZMod 7) (hxy : (2 * x + y) ^ 2 = 5 * y ^ 2) :
    x = 0 ∧ y = 0 :=
  zmod_norm_eq_zero_of_inert (by norm_num) (by norm_num) (Or.inl rfl) x y hxy

/-- 对任意在 $\mathbb{Z}[\varphi]$ 中惰性的素数 $p$（$p \equiv 2, 3 \pmod 5$，含 $p = 2$），
    $p \mid N(x\varphi + y) \iff p \mid x \land p \mid y$。 -/
theorem inert_prime_dvd_zphiNorm_iff {p : ℕ} (hp : Nat.Prime p)
    (h5 : p % 5 = 2 ∨ p % 5 = 3) (x y : ℤ) :
    (p : ℤ) ∣ zphiNorm x y ↔ (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  by_cases hp2 : p = 2
  · subst hp2
    have h2 : ((2 : ℕ) : ℤ) = 2 := rfl
    rw [h2, ← even_iff_two_dvd, ← even_iff_two_dvd, ← even_iff_two_dvd]
    exact zphiNorm_even_iff x y
  · constructor
    · intro hdvd
      have h4 : 4 * zphiNorm x y = -((2 * x - y) ^ 2 - 5 * y ^ 2) := by
        unfold zphiNorm; ring
      have hdvd_sq : (p : ℤ) ∣ (2 * x - y) ^ 2 - 5 * y ^ 2 := by
        rcases hdvd with ⟨k, hk⟩
        refine ⟨-4 * k, ?_⟩
        linarith [h4]
      have hzmod : ((2 * (x : ZMod p) + (- (y : ZMod p))) ^ 2) = 5 * (- (y : ZMod p)) ^ 2 := by
        have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 * x - y) ^ 2 - 5 * y ^ 2) p).mpr hdvd_sq
        push_cast at h0
        have h1 : (2 * (x : ZMod p) - (y : ZMod p)) ^ 2 = 5 * (y : ZMod p) ^ 2 := sub_eq_zero.mp h0
        simpa [sub_eq_add_neg, neg_sq] using h1
      have hxy0 := zmod_norm_eq_zero_of_inert hp hp2 h5 (x : ZMod p) (-(y : ZMod p)) hzmod
      have hy0 : (y : ZMod p) = 0 := neg_eq_zero.mp hxy0.2
      exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hxy0.1,
        (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp hy0⟩
    · rintro ⟨⟨kx, rfl⟩, ⟨ky, rfl⟩⟩
      refine ⟨(p : ℤ) * zphiNorm kx ky, ?_⟩
      unfold zphiNorm; ring

/-- 从一般 `ZMod p` 二次型消去条件出发的惰性素数非整除性。 -/
theorem inert_prime_not_dvd_zphiNorm_of_cond {p : ℕ} (hp : Nat.Prime p)
    (hcond : p = 2 ∨ ∀ x y : ZMod p, (2 * x + y) ^ 2 = 5 * y ^ 2 → x = 0 ∧ y = 0)
    {p1 q1 a b c d : ℤ} (hgcd : Int.gcd p1 q1 = 1) (hdet : |a * d - b * c| = 1) :
    ¬ ((p : ℤ) ∣ zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b)) := by
  intro hdvd
  set u := p1 * c - q1 * a
  set v := p1 * d - q1 * b
  have hdiv_uv : (p : ℤ) ∣ u ∧ (p : ℤ) ∣ v := by
    rcases hcond with rfl | hform
    · have h2 : ((2 : ℕ) : ℤ) = 2 := rfl
      rw [h2, ← even_iff_two_dvd, ← even_iff_two_dvd]
      rw [h2, ← even_iff_two_dvd] at hdvd
      exact (zphiNorm_even_iff u v).mp hdvd
    · have h4 : 4 * zphiNorm u v = -((2 * u - v) ^ 2 - 5 * v ^ 2) := by
        unfold zphiNorm; ring
      have hdvd_sq : (p : ℤ) ∣ (2 * u - v) ^ 2 - 5 * v ^ 2 := by
        rcases hdvd with ⟨k, hk⟩
        refine ⟨-4 * k, ?_⟩
        linarith [h4]
      have hzmod : ((2 * (u : ZMod p) + (- (v : ZMod p))) ^ 2) = 5 * (- (v : ZMod p)) ^ 2 := by
        have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 * u - v) ^ 2 - 5 * v ^ 2) p).mpr hdvd_sq
        push_cast at h0
        have h1 : (2 * (u : ZMod p) - (v : ZMod p)) ^ 2 = 5 * (v : ZMod p) ^ 2 := sub_eq_zero.mp h0
        simpa [sub_eq_add_neg, neg_sq] using h1
      have huv0 := hform (u : ZMod p) (-(v : ZMod p)) hzmod
      have hv0 : (v : ZMod p) = 0 := neg_eq_zero.mp huv0.2
      exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp huv0.1,
        (ZMod.intCast_zmod_eq_zero_iff_dvd v p).mp hv0⟩
  have hdet_sq : a * d - b * c = 1 ∨ a * d - b * c = -1 :=
    (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
  have hq1_id : d * u - c * v = -(a * d - b * c) * q1 := by dsimp [u, v]; ring
  have hp1_id : b * u - a * v = -(a * d - b * c) * p1 := by dsimp [u, v]; ring
  have hdiv_p1 : (p : ℤ) ∣ p1 := by
    have h1 := dvd_sub (dvd_mul_of_dvd_right hdiv_uv.1 b) (dvd_mul_of_dvd_right hdiv_uv.2 a)
    rw [hp1_id] at h1
    rcases hdet_sq with hpos | hneg
    · rw [hpos] at h1; simpa using dvd_neg.mp (by simpa using h1)
    · rw [hneg] at h1; simpa using h1
  have hdiv_q1 : (p : ℤ) ∣ q1 := by
    have h1 := dvd_sub (dvd_mul_of_dvd_right hdiv_uv.1 d) (dvd_mul_of_dvd_right hdiv_uv.2 c)
    rw [hq1_id] at h1
    rcases hdet_sq with hpos | hneg
    · rw [hpos] at h1; simpa using dvd_neg.mp (by simpa using h1)
    · rw [hneg] at h1; simpa using h1
  have hdiv_gcd : p ∣ Int.gcd p1 q1 := Nat.dvd_gcd (Int.natCast_dvd.mp hdiv_p1) (Int.natCast_dvd.mp hdiv_q1)
  rw [hgcd] at hdiv_gcd
  exact hp.not_dvd_one hdiv_gcd

/-- 引理 `lem:general-endpoint-rigidity`(1)：对任意惰性素数 $p$（$p \equiv 2, 3 \pmod 5$，含 $p = 2$），
    若 $\gcd(p_1, q_1) = 1$ 且 $|ad - bc| = 1$，则 $p \nmid N(\xi_1)$。 -/
theorem inert_prime_not_dvd_zphiNorm {p : ℕ} (hp : Nat.Prime p)
    (h5 : p % 5 = 2 ∨ p % 5 = 3)
    {p1 q1 a b c d : ℤ} (hgcd : Int.gcd p1 q1 = 1) (hdet : |a * d - b * c| = 1) :
    ¬ ((p : ℤ) ∣ zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b)) := by
  by_cases hp2 : p = 2
  · exact inert_prime_not_dvd_zphiNorm_of_cond hp (Or.inl hp2) hgcd hdet
  · exact inert_prime_not_dvd_zphiNorm_of_cond hp
      (Or.inr (zmod_norm_eq_zero_of_inert hp hp2 h5)) hgcd hdet

/-- 引理 `lem:general-endpoint-rigidity`(1) 对 $\xi_2$ 版本：
    若 $\gcd(p_2, q_2) = 1$ 且 $|ad - bc| = 1$，则对任意惰性素数 $p$ 亦有 $p \nmid N(\xi_2)$。 -/
theorem inert_prime_not_dvd_zphiNorm_xi2 {p : ℕ} (hp : Nat.Prime p)
    (h5 : p % 5 = 2 ∨ p % 5 = 3)
    {p2 q2 a b c d : ℤ} (hgcd : Int.gcd p2 q2 = 1) (hdet : |a * d - b * c| = 1) :
    ¬ ((p : ℤ) ∣ zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d)) := by
  intro hdvd
  have hdiv_uv := (inert_prime_dvd_zphiNorm_iff hp h5 _ _).mp hdvd
  set u := q2 * a + p2 * c
  set v := q2 * b + p2 * d
  have hdet_sq : a * d - b * c = 1 ∨ a * d - b * c = -1 :=
    (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
  have hq2_id : d * u - c * v = (a * d - b * c) * q2 := by dsimp [u, v]; ring
  have hp2_id : -(b * u) + a * v = (a * d - b * c) * p2 := by dsimp [u, v]; ring
  have hdiv_q2 : (p : ℤ) ∣ q2 := by
    have h1 := dvd_sub (dvd_mul_of_dvd_right hdiv_uv.1 d) (dvd_mul_of_dvd_right hdiv_uv.2 c)
    rw [hq2_id] at h1
    rcases hdet_sq with hpos | hneg
    · rw [hpos] at h1; simpa using h1
    · rw [hneg] at h1; simpa using dvd_neg.mp (by simpa using h1)
  have hdiv_p2 : (p : ℤ) ∣ p2 := by
    have h1 := dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_right hdiv_uv.1 b))
      (dvd_mul_of_dvd_right hdiv_uv.2 a)
    rw [hp2_id] at h1
    rcases hdet_sq with hpos | hneg
    · rw [hpos] at h1; simpa using h1
    · rw [hneg] at h1; simpa using dvd_neg.mp (by simpa using h1)
  have hdiv_gcd : p ∣ Int.gcd p2 q2 := Nat.dvd_gcd (Int.natCast_dvd.mp hdiv_p2) (Int.natCast_dvd.mp hdiv_q2)
  rw [hgcd] at hdiv_gcd
  exact hp.not_dvd_one hdiv_gcd

/-! #### Part (2)：偶 $D = 2 d_0$ 的奇偶刚性与惰性因子排除 -/

/-- 当 $D = p_1 q_2 + p_2 q_1 = 2 d_0$ 为偶数且 $|ad-bc|=1$ 时，$M_{u,v}$ 必为偶数。 -/
theorem even_D_Muv_even {p1 q1 p2 q2 a b c d d0 : ℤ}
    (hD : p1 * q2 + p2 * q1 = 2 * d0) (hdet : |a * d - b * c| = 1) :
    (2 : ℤ) ∣ M_uv p1 q1 p2 q2 a b c d := by
  have hnorm := Muv_norm_identity p1 q1 p2 q2 a b c d hdet
  rw [hD] at hnorm
  set M := M_uv p1 q1 p2 q2 a b c d
  have h4 : M ^ 2 = 4 * (5 * d0 ^ 2 + zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b) *
      zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d)) := by linarith
  have hdecomp : M = 2 * (M / 2) + M % 2 := by omega
  set q := M / 2
  set r := M % 2
  have hr : r = 0 ∨ r = 1 := by omega
  have hsq : M ^ 2 = 2 * (2 * q ^ 2 + 2 * q * r) + r ^ 2 := by rw [hdecomp]; ring
  rcases hr with hr0 | hr1
  · exact ⟨q, by omega⟩
  · rw [hr1] at hsq; omega

/-- 引理 `lem:general-endpoint-rigidity`(2)：
    当 $D = 2 d_0$、$\gcd(p_1,q_1)=\gcd(p_2,q_2)=1$ 且 $|ad-bc|=1$ 时，
    令 $m := (ad-bc)(M_{u,v}/2)$，则：
    1. $M_{u,v} = 2(ad-bc)m$；
    2. $m^2 - 5 d_0^2 = N(\xi_1) N(\xi_2)$；
    3. $m \equiv d_0 + 1 \pmod 2$（即 $m \bmod 2 \ne d_0 \bmod 2$）；
    4. 若惰性素数 $p \mid d_0$，则 $p \nmid m$。 -/
theorem even_D_rigidity {p1 q1 p2 q2 a b c d d0 : ℤ}
    (hD : p1 * q2 + p2 * q1 = 2 * d0)
    (hgcd1 : Int.gcd p1 q1 = 1) (hgcd2 : Int.gcd p2 q2 = 1)
    (hdet : |a * d - b * c| = 1) :
    let ε := a * d - b * c
    let m := ε * (M_uv p1 q1 p2 q2 a b c d / 2)
    M_uv p1 q1 p2 q2 a b c d = 2 * (ε * m) ∧
    m ^ 2 - 5 * d0 ^ 2 =
      zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b) *
        zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d) ∧
    m ≡ d0 + 1 [ZMOD 2] ∧
    (∀ p : ℕ, Nat.Prime p → (p % 5 = 2 ∨ p % 5 = 3) → (p : ℤ) ∣ d0 → ¬ ((p : ℤ) ∣ m)) := by
  dsimp only
  set ε := a * d - b * c
  set M := M_uv p1 q1 p2 q2 a b c d
  set m0 := M / 2
  set m := ε * m0
  have hε : ε = 1 ∨ ε = -1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
  have hε_sq : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hM2 : M = 2 * m0 := by
    rcases even_D_Muv_even hD hdet with ⟨k, hk⟩
    have hk' : M = 2 * k := hk
    have hm0k : m0 = k := by dsimp [m0]; rw [hk']; omega
    rw [hk', hm0k]
  have hm_eq : M = 2 * (ε * m) := by
    have hm_id : ε * m = m0 := by
      dsimp [m]
      calc ε * (ε * m0) = ε ^ 2 * m0 := by ring
        _ = 1 * m0 := by rw [hε_sq]
        _ = m0 := one_mul m0
    rw [hm_id, hM2]
  have hnorm_id := Muv_norm_identity p1 q1 p2 q2 a b c d hdet
  change M ^ 2 - 5 * (p1 * q2 + p2 * q1) ^ 2 = _ at hnorm_id
  rw [hD, hM2] at hnorm_id
  have hm_sq : m ^ 2 = m0 ^ 2 := by
    dsimp [m]; nlinarith [hε_sq]
  have hm_norm : m ^ 2 - 5 * d0 ^ 2 =
      zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b) *
        zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d) := by
    nlinarith [hnorm_id, hm_sq]
  have h2_ndvd1 : ¬ ((2 : ℤ) ∣ zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b)) :=
    inert_prime_not_dvd_zphiNorm Nat.prime_two (Or.inl rfl) hgcd1 hdet
  have h2_ndvd2 : ¬ ((2 : ℤ) ∣ zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d)) :=
    inert_prime_not_dvd_zphiNorm_xi2 Nat.prime_two (Or.inl rfl) hgcd2 hdet
  have hodd1 : Odd (zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b)) :=
    Int.not_even_iff_odd.mp (fun he => h2_ndvd1 (even_iff_two_dvd.mp he))
  have hodd2 : Odd (zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d)) :=
    Int.not_even_iff_odd.mp (fun he => h2_ndvd2 (even_iff_two_dvd.mp he))
  have hodd_prod : Odd (m ^ 2 - 5 * d0 ^ 2) := by
    rw [hm_norm]; exact hodd1.mul hodd2
  have hmod2 : m ≡ d0 + 1 [ZMOD 2] := by
    rcases hodd_prod with ⟨t, ht⟩
    rw [Int.modEq_iff_dvd]
    rcases Int.even_or_odd m with ⟨km, hm⟩ | ⟨km, hm⟩ <;>
      rcases Int.even_or_odd d0 with ⟨kd, hd⟩ | ⟨kd, hd⟩
    · have h2 : m ^ 2 - 5 * d0 ^ 2 = 2 * (2 * km ^ 2 - 10 * kd ^ 2) := by rw [hm, hd]; ring
      omega
    · refine ⟨kd + 1 - km, ?_⟩; linarith
    · refine ⟨kd - km, ?_⟩; linarith
    · have h2 : m ^ 2 - 5 * d0 ^ 2 =
          2 * (2 * km ^ 2 + 2 * km - 10 * kd ^ 2 - 10 * kd - 2) := by rw [hm, hd]; ring
      omega
  refine ⟨hm_eq, hm_norm, hmod2, ?_⟩
  intro p hp h5 hp_dvd_d0 hp_dvd_m
  have hp_dvd_lhs : (p : ℤ) ∣ m ^ 2 - 5 * d0 ^ 2 :=
    dvd_sub (dvd_pow hp_dvd_m (by norm_num)) (dvd_mul_of_dvd_right (dvd_pow hp_dvd_d0 (by norm_num)) 5)
  rw [hm_norm] at hp_dvd_lhs
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hp_int.dvd_or_dvd hp_dvd_lhs with h1 | h2
  · exact inert_prime_not_dvd_zphiNorm hp h5 hgcd1 hdet h1
  · exact inert_prime_not_dvd_zphiNorm_xi2 hp h5 hgcd2 hdet h2

/-- 偶 $D = 2 d_0$ 情形下误差泛函的精确化简：
    $\Phi_{u,v}(\eta) = \left|\frac{m}{d_0 \sqrt{5}} - 1\right|$。 -/
theorem even_D_rigidity_functional {p1 q1 p2 q2 a b c d d0 : ℤ}
    (hD : p1 * q2 + p2 * q1 = 2 * d0)
    (hdet : |a * d - b * c| = 1)
    (hq1 : (0 : ℝ) < (q1 : ℝ)) (hq2 : (0 : ℝ) < (q2 : ℝ))
    (hd0 : (0 : ℝ) < (d0 : ℝ)) :
    let m := (a * d - b * c) * (M_uv p1 q1 p2 q2 a b c d / 2)
    orbitHeight (orbitPt a b c d) (orbitPtConj a b c d) *
      (|(p1 : ℝ) / (q1 : ℝ) - orbitPt a b c d| *
        |orbitPtConj a b c d + (p2 : ℝ) / (q2 : ℝ)| /
        ((p1 : ℝ) / (q1 : ℝ) + (p2 : ℝ) / (q2 : ℝ))) =
      |(m : ℝ) / ((d0 : ℝ) * Real.sqrt 5) - 1| := by
  dsimp only
  have hD_pos : (0 : ℝ) < ((p1 * q2 + p2 * q1 : ℤ) : ℝ) := by
    rw [hD]; push_cast; linarith
  rw [rational_endpoint_rigidity_identity p1 q1 p2 q2 a b c d hdet hq1 hq2 hD_pos]
  rcases even_D_Muv_even hD hdet with ⟨k, hk⟩
  have hk_div : M_uv p1 q1 p2 q2 a b c d / 2 = k := by rw [hk]; omega
  rw [hk_div, hk, hD]
  push_cast
  have h5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt sqrt5_pos
  have hd0_ne : (d0 : ℝ) ≠ 0 := ne_of_gt hd0
  congr 1
  field_simp [hd0_ne, h5_ne]

/-! #### Part (3)：模 $2D$ / 模 $2d_0$ 同余筛 -/

/-- 引理 `lem:general-endpoint-rigidity`(3) 第一式：
    $2D \mid q_2 (M_{u,v} + \varepsilon D) + 2 q_1 N(\xi_2)$。 -/
theorem mod_2D_sieve_q (p1 q1 p2 q2 a b c d : ℤ) :
    (2 * (p1 * q2 + p2 * q1) : ℤ) ∣
      q2 * (M_uv p1 q1 p2 q2 a b c d + (a * d - b * c) * (p1 * q2 + p2 * q1)) +
        2 * q1 * zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d) := by
  refine ⟨d * (q2 * b + p2 * d) + (d - c) * (q2 * a + p2 * c), ?_⟩
  unfold M_uv zphiNorm
  ring

/-- 引理 `lem:general-endpoint-rigidity`(3) 第二式：
    $2D \mid p_2 (M_{u,v} + \varepsilon D) - 2 p_1 N(\xi_2)$。 -/
theorem mod_2D_sieve_p (p1 q1 p2 q2 a b c d : ℤ) :
    (2 * (p1 * q2 + p2 * q1) : ℤ) ∣
      p2 * (M_uv p1 q1 p2 q2 a b c d + (a * d - b * c) * (p1 * q2 + p2 * q1)) -
        2 * p1 * zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d) := by
  refine ⟨(a - b) * (q2 * a + p2 * c) - b * (q2 * b + p2 * d), ?_⟩
  unfold M_uv zphiNorm
  ring

/-- 引理 `lem:general-endpoint-rigidity`(3) 特化：在 $(u, v) = (2 d_0 / q_1, 0)$
    （即 $p_2 = 0, q_2 = 1, p_1 = 2 d_0$）处，$\gamma := a\varphi + b$，
    $m \equiv d_0 - \varepsilon q_1 N(\gamma) \pmod{2 d_0}$。 -/
theorem mod_2d_sieve_special (d0 q1 a b c d : ℤ) (hdet : |a * d - b * c| = 1) :
    let ε := a * d - b * c
    let m := ε * (M_uv (2 * d0) q1 0 1 a b c d / 2)
    m ≡ d0 - ε * q1 * zphiNorm a b [ZMOD 2 * d0] := by
  dsimp only
  set ε := a * d - b * c
  set m := ε * (M_uv (2 * d0) q1 0 1 a b c d / 2)
  have hε : ε = 1 ∨ ε = -1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
  have hε_sq : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hD : (2 * d0) * 1 + 0 * q1 = 2 * d0 := by ring
  rcases even_D_Muv_even hD hdet with ⟨k, hk⟩
  have hk_div : M_uv (2 * d0) q1 0 1 a b c d / 2 = k := by rw [hk]; omega
  have hm_eq : m = ε * k := by dsimp [m]; rw [hk_div]
  have hsieve := mod_2D_sieve_q (2 * d0) q1 0 1 a b c d
  rcases hsieve with ⟨K, hK⟩
  have hK' : 2 * k + ε * (2 * d0) + 2 * q1 * zphiNorm a b = 4 * d0 * K := by
    have h1 : (2 * d0) * 1 + 0 * q1 = 2 * d0 := by ring
    have h2 : zphiNorm (1 * a + 0 * c) (1 * b + 0 * d) = zphiNorm a b := by
      congr 1 <;> ring
    rw [hk, h1, h2] at hK
    linarith
  have hK_half : k + ε * d0 + q1 * zphiNorm a b = 2 * d0 * K := by linarith
  have hK_mul : ε * k + ε ^ 2 * d0 + ε * q1 * zphiNorm a b = 2 * d0 * (ε * K) := by
    calc ε * k + ε ^ 2 * d0 + ε * q1 * zphiNorm a b
        = ε * (k + ε * d0 + q1 * zphiNorm a b) := by ring
      _ = ε * (2 * d0 * K) := by rw [hK_half]
      _ = 2 * d0 * (ε * K) := by ring
  rw [hε_sq, one_mul, ← hm_eq] at hK_mul
  rw [Int.modEq_iff_dvd]
  refine ⟨-(ε * K - 1), ?_⟩
  linarith

/-! #### Part (4)：非零范数整除性 -/

/-- 当 $D = p_1 q_2 + p_2 q_1 \ne 0$ 且 $|ad-bc|=1$ 时，$M_{u,v}^2 - 5 D^2$ 为 $4$ 的非零整数倍。 -/
theorem Muv_norm_ne_zero (p1 q1 p2 q2 a b c d : ℤ)
    (hdet : |a * d - b * c| = 1) (hD : p1 * q2 + p2 * q1 ≠ 0) :
    (4 : ℤ) ∣ (M_uv p1 q1 p2 q2 a b c d) ^ 2 - 5 * (p1 * q2 + p2 * q1) ^ 2 ∧
    ((M_uv p1 q1 p2 q2 a b c d) ^ 2 - 5 * (p1 * q2 + p2 * q1) ^ 2) / 4 ≠ 0 := by
  have hnorm := Muv_norm_identity p1 q1 p2 q2 a b c d hdet
  set M := M_uv p1 q1 p2 q2 a b c d
  set D := p1 * q2 + p2 * q1
  have hdvd : (4 : ℤ) ∣ M ^ 2 - 5 * D ^ 2 := by
    rw [hnorm]
    exact ⟨zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b) *
      zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d), by ring⟩
  have hquot : (M ^ 2 - 5 * D ^ 2) / 4 =
      zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b) *
        zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d) := by
    rw [hnorm, mul_assoc]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hne0 : M ^ 2 - 5 * D ^ 2 ≠ 0 := by
    intro h0
    have hirr : Irrational (Real.sqrt 5) := Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 5)
    have hreal : (M : ℝ) ^ 2 = 5 * (D : ℝ) ^ 2 := by exact_mod_cast sub_eq_zero.mp h0
    have hDR : (D : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD
    have h5 := sqrt5_sq
    have hdiff : ((M : ℝ) / (D : ℝ) - Real.sqrt 5) * ((M : ℝ) / (D : ℝ) + Real.sqrt 5) = 0 := by
      field_simp [hDR]
      linear_combination hreal - (D : ℝ) ^ 2 * h5
    rcases mul_eq_zero.mp hdiff with hpos | hneg
    · exact hirr ⟨(M : ℚ) / (D : ℚ), by push_cast at hpos ⊢; exact sub_eq_zero.mp hpos⟩
    · exact hirr ⟨-((M : ℚ) / (D : ℚ)), by push_cast at hneg ⊢; linarith⟩
  refine ⟨hdvd, ?_⟩
  rw [hquot]
  intro hq0
  have : M ^ 2 - 5 * D ^ 2 = 0 := by
    rw [hnorm, mul_assoc, hq0, mul_zero]
  exact hne0 this

/-- 引理 `lem:general-endpoint-rigidity`(4)：
    $N(\xi_2) \mid \frac{M_{u,v}^2 - 5 D^2}{4}$，且当 $D \ne 0$、$|ad-bc|=1$ 时该商非零。 -/
theorem zphiNorm_xi2_dvd_norm_quot (p1 q1 p2 q2 a b c d : ℤ) (hdet : |a * d - b * c| = 1) :
    zphiNorm (q2 * a + p2 * c) (q2 * b + p2 * d) ∣
      ((M_uv p1 q1 p2 q2 a b c d) ^ 2 - 5 * (p1 * q2 + p2 * q1) ^ 2) / 4 := by
  have hnorm := Muv_norm_identity p1 q1 p2 q2 a b c d hdet
  refine ⟨zphiNorm (p1 * c - q1 * a) (p1 * d - q1 * b), ?_⟩
  rw [hnorm, mul_assoc, Int.mul_ediv_cancel_left _ (by norm_num)]
  ring

/-! ### 3. $B = 3, 4, 5, 6$ 算术筛与谱隙分离核心定理 -/

/-! #### 3.1 $B = 3$（$D = 18, d = 9$） -/

/-- $B = 3$（$D = 18, d_0 = 9$）：在 $\gcd(p_1,q_1)=\gcd(p_2,q_2)=1$ 与 $|ad-bc|=1$ 下，
    整数部分 $m$ 必为偶数且不被惰性素数 $3$ 整除。 -/
theorem b3_inert_three_not_dvd_m {p1 q1 p2 q2 a b c d : ℤ}
    (hD : p1 * q2 + p2 * q1 = 18)
    (hgcd1 : Int.gcd p1 q1 = 1) (hgcd2 : Int.gcd p2 q2 = 1)
    (hdet : |a * d - b * c| = 1) :
    let m := (a * d - b * c) * (M_uv p1 q1 p2 q2 a b c d / 2)
    Even m ∧ ¬ ((3 : ℤ) ∣ m) := by
  have hrig := even_D_rigidity (d0 := 9) (by linarith) hgcd1 hgcd2 hdet
  dsimp only at hrig ⊢
  refine ⟨?_, ?_⟩
  · have hmod := hrig.2.2.1
    rw [Int.modEq_iff_dvd] at hmod
    rcases hmod with ⟨k, hk⟩
    exact ⟨-k + 5, by linarith⟩
  · exact hrig.2.2.2 3 (by norm_num) (Or.inr rfl) (by norm_num)

lemma nine_sqrt5_bounds :
    (20 : ℝ) < 9 * Real.sqrt 5 ∧ 9 * Real.sqrt 5 < 21 := by
  have h5_pos := sqrt5_pos
  have h5_sq := sqrt5_sq
  constructor
  · have hlt : (20 : ℝ) ^ 2 < (9 * Real.sqrt 5) ^ 2 := by nlinarith [h5_sq]
    nlinarith
  · have hlt : (9 * Real.sqrt 5) ^ 2 < (21 : ℝ) ^ 2 := by nlinarith [h5_sq]
    nlinarith

/-- $B = 3$ 谱隙核心不等式：
    $0 < 1 - \frac{20}{9\sqrt{5}} < \frac{22}{9\sqrt{5}} - 1 < 1 - \frac{16}{9\sqrt{5}}$，
    且对一切不被 $3$ 整除的偶数 $m \ne 20$ 有 $\left|\frac{m}{9\sqrt{5}} - 1\right| \ge \frac{22}{9\sqrt{5}} - 1$
    （当 $m \ne 22$ 时严格大于）。 -/
theorem b3_spectral_gap :
    (0 : ℝ) < 1 - 20 / (9 * Real.sqrt 5) ∧
    1 - 20 / (9 * Real.sqrt 5) < 22 / (9 * Real.sqrt 5) - 1 ∧
    22 / (9 * Real.sqrt 5) - 1 < 1 - 16 / (9 * Real.sqrt 5) ∧
    (∀ m : ℤ, Even m → ¬ ((3 : ℤ) ∣ m) → m ≠ 20 →
      22 / (9 * Real.sqrt 5) - 1 ≤ |(m : ℝ) / (9 * Real.sqrt 5) - 1|) ∧
    (∀ m : ℤ, Even m → ¬ ((3 : ℤ) ∣ m) → m ≠ 20 → m ≠ 22 →
      22 / (9 * Real.sqrt 5) - 1 < |(m : ℝ) / (9 * Real.sqrt 5) - 1|) := by
  have h5_pos := sqrt5_pos
  have h95_pos : (0 : ℝ) < 9 * Real.sqrt 5 := mul_pos (by norm_num) h5_pos
  have h20 := nine_sqrt5_bounds.1
  have h21 := nine_sqrt5_bounds.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sub_pos, div_lt_one h95_pos]; exact h20
  · have hlt : (2 : ℝ) < 42 / (9 * Real.sqrt 5) := by
      rw [lt_div_iff₀ h95_pos]; linarith
    have hsplit : (42 : ℝ) / (9 * Real.sqrt 5) = 20 / (9 * Real.sqrt 5) + 22 / (9 * Real.sqrt 5) := by ring
    linarith
  · have hlt : (38 : ℝ) / (9 * Real.sqrt 5) < 2 := by
      rw [div_lt_iff₀ h95_pos]; linarith
    have hsplit : (38 : ℝ) / (9 * Real.sqrt 5) = 22 / (9 * Real.sqrt 5) + 16 / (9 * Real.sqrt 5) := by ring
    linarith
  · intro m hm_even hm_n3 hm20
    rcases hm_even with ⟨k, rfl⟩
    have hk_ne9 : k ≠ 9 := by
      intro h9; apply hm_n3; exact ⟨6, by omega⟩
    have hk_ne10 : k ≠ 10 := by intro h10; apply hm20; omega
    have hcases : k + k ≤ 16 ∨ 22 ≤ k + k := by omega
    rcases hcases with hle16 | hge22
    · have hmR : ((k + k : ℤ) : ℝ) ≤ 16 := by exact_mod_cast hle16
      have hdiv : ((k + k : ℤ) : ℝ) / (9 * Real.sqrt 5) ≤ 16 / (9 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h95_pos)
      have hlt1 : 16 / (9 * Real.sqrt 5) < 1 := (div_lt_one h95_pos).mpr (by linarith)
      rw [abs_of_neg (by linarith)]
      have h16 : (38 : ℝ) / (9 * Real.sqrt 5) < 2 := by
        rw [div_lt_iff₀ h95_pos]; linarith
      have hsplit : (38 : ℝ) / (9 * Real.sqrt 5) =
          22 / (9 * Real.sqrt 5) + 16 / (9 * Real.sqrt 5) := by ring
      linarith
    · have hmR : (22 : ℝ) ≤ ((k + k : ℤ) : ℝ) := by exact_mod_cast hge22
      have hdiv : 22 / (9 * Real.sqrt 5) ≤ ((k + k : ℤ) : ℝ) / (9 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h95_pos)
      have hgt1 : 1 < 22 / (9 * Real.sqrt 5) := (one_lt_div h95_pos).mpr (by linarith)
      rw [abs_of_pos (by linarith)]
      linarith
  · intro m hm_even hm_n3 hm20 hm22
    rcases hm_even with ⟨k, rfl⟩
    have hk_ne9 : k ≠ 9 := by
      intro h9; apply hm_n3; exact ⟨6, by omega⟩
    have hk_ne10 : k ≠ 10 := by intro h10; apply hm20; omega
    have hk_ne11 : k ≠ 11 := by intro h11; apply hm22; omega
    have hcases : k + k ≤ 16 ∨ 24 ≤ k + k := by omega
    rcases hcases with hle16 | hge24
    · have hmR : ((k + k : ℤ) : ℝ) ≤ 16 := by exact_mod_cast hle16
      have hdiv : ((k + k : ℤ) : ℝ) / (9 * Real.sqrt 5) ≤ 16 / (9 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h95_pos)
      have hlt1 : 16 / (9 * Real.sqrt 5) < 1 := (div_lt_one h95_pos).mpr (by linarith)
      rw [abs_of_neg (by linarith)]
      have h16 : (38 : ℝ) / (9 * Real.sqrt 5) < 2 := by
        rw [div_lt_iff₀ h95_pos]; linarith
      have hsplit : (38 : ℝ) / (9 * Real.sqrt 5) =
          22 / (9 * Real.sqrt 5) + 16 / (9 * Real.sqrt 5) := by ring
      linarith
    · have hmR : (24 : ℝ) ≤ ((k + k : ℤ) : ℝ) := by exact_mod_cast hge24
      have hdiv : 24 / (9 * Real.sqrt 5) ≤ ((k + k : ℤ) : ℝ) / (9 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h95_pos)
      have h22_lt : 22 / (9 * Real.sqrt 5) < 24 / (9 * Real.sqrt 5) :=
        div_lt_div_of_pos_right (by norm_num) h95_pos
      have hgt1 : 1 < 22 / (9 * Real.sqrt 5) := (one_lt_div h95_pos).mpr (by linarith)
      rw [abs_of_pos (by linarith)]
      linarith

/-! #### 3.2 $B = 4$（$D = 32, d = 16$）与模 $16$ 乘法子群禁除 $m = 37$ -/

/-- 模 $16$ 四元乘法子群 $\{1, 7, 9, 15\} \pmod{16}$（即 $\pm 1, \pm 7 \pmod{16}$）。 -/
def InMod16Subgroup (x : ℤ) : Prop :=
  x % 16 = 1 ∨ x % 16 = 7 ∨ x % 16 = 9 ∨ x % 16 = 15

lemma mod16_subgroup_neg {x : ℤ} (hx : InMod16Subgroup x) : InMod16Subgroup (-x) := by
  unfold InMod16Subgroup at hx ⊢
  rcases hx with h | h | h | h <;> omega

lemma mod16_subgroup_mul {x y : ℤ} (hx : InMod16Subgroup x) (hy : InMod16Subgroup y) :
    InMod16Subgroup (x * y) := by
  unfold InMod16Subgroup at hx hy ⊢
  have hmul : (x * y) % 16 = ((x % 16) * (y % 16)) % 16 := by
    rw [Int.mul_emod]
  rcases hx with h | h | h | h <;>
    rcases hy with h' | h' | h' | h' <;>
    rw [hmul, h, h'] <;> norm_num

lemma mod16_subgroup_dvd_89 {k : ℤ} (hk : k ∣ 89) : InMod16Subgroup k := by
  have h89_prime : Nat.Prime 89 := by norm_num
  have hnat_dvd : k.natAbs ∣ 89 := Int.natAbs_dvd_natAbs.mpr hk
  have hcases : k.natAbs = 1 ∨ k.natAbs = 89 := (Nat.dvd_prime h89_prime).mp hnat_dvd
  rcases Int.natAbs_eq k with hkpos | hkneg
  · rcases hcases with h1 | h89
    · have : k = 1 := by omega
      rw [this]; unfold InMod16Subgroup; left; norm_num
    · have : k = 89 := by omega
      rw [this]; unfold InMod16Subgroup; right; right; left; norm_num
  · rcases hcases with h1 | h89
    · have : k = -1 := by omega
      rw [this]; unfold InMod16Subgroup; right; right; right; norm_num
    · have : k = -89 := by omega
      rw [this]; unfold InMod16Subgroup; right; left; norm_num

/-- $B = 4$ 模 $16$ 子群禁除定理：在 $(32/q_1, 0)$ 处，若 $q_1 \bmod 16 \in \{1, 7, 9, 15\}$ 且
    $|ad-bc|=1$，则 $m$ 必为奇数且 $m \ne 37, m \ne -37$。 -/
theorem b4_mod16_excludes_37 {q1 a b c d : ℤ}
    (hq1 : InMod16Subgroup q1) (hdet : |a * d - b * c| = 1) :
    let m := (a * d - b * c) * (M_uv 32 q1 0 1 a b c d / 2)
    Odd m ∧ m ≠ 37 ∧ m ≠ -37 := by
  dsimp only
  set ε := a * d - b * c
  set m := ε * (M_uv 32 q1 0 1 a b c d / 2)
  have hgcd1 : Int.gcd 32 q1 = 1 := by
    have hq1_odd : q1 % 2 = 1 := by
      unfold InMod16Subgroup at hq1
      rcases hq1 with h | h | h | h <;> omega
    have hnot2 : ¬ (2 ∣ q1.natAbs) := by omega
    have hcop : Nat.Coprime (2 ^ 5) q1.natAbs :=
      Nat.Coprime.pow_left 5 (Nat.prime_two.coprime_iff_not_dvd.mpr hnot2)
    simpa [Int.gcd] using hcop
  have hgcd2 : Int.gcd (0 : ℤ) 1 = 1 := by decide
  have hD : (32 : ℤ) * 1 + 0 * q1 = 32 := by ring
  have hrig := even_D_rigidity (d0 := 16) hD hgcd1 hgcd2 hdet
  dsimp only at hrig
  have hm_odd : Odd m := by
    have hmod2 := hrig.2.2.1
    rw [Int.modEq_iff_dvd] at hmod2
    rcases hmod2 with ⟨k, hk⟩
    exact ⟨8 - k, by linarith⟩
  have hm_sub_of_sq : m ^ 2 = 37 ^ 2 → InMod16Subgroup m := by
    intro hsq
    have hm_norm := hrig.2.1
    change m ^ 2 - 5 * 16 ^ 2 = _ at hm_norm
    rw [hsq] at hm_norm
    have hdvd89 : zphiNorm (1 * a + 0 * c) (1 * b + 0 * d) ∣ 89 := by
      refine ⟨zphiNorm (32 * c - q1 * a) (32 * d - q1 * b), ?_⟩
      linarith [hm_norm]
    have hN_eq : zphiNorm (1 * a + 0 * c) (1 * b + 0 * d) = zphiNorm a b := by
      congr 1 <;> ring
    rw [hN_eq] at hdvd89
    have hN_sub : InMod16Subgroup (zphiNorm a b) := mod16_subgroup_dvd_89 hdvd89
    have hε_sub : InMod16Subgroup (-ε) := by
      have hε : ε = 1 ∨ ε = -1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hdet
      rcases hε with h1 | hm1
      · rw [h1]; unfold InMod16Subgroup; right; right; right; norm_num
      · rw [hm1]; unfold InMod16Subgroup; left; norm_num
    have hsieve := mod_2d_sieve_special 16 q1 a b c d hdet
    change m ≡ 16 - ε * q1 * zphiNorm a b [ZMOD 2 * 16] at hsieve
    rw [Int.modEq_iff_dvd] at hsieve
    rcases hsieve with ⟨K, hK⟩
    have hm_mod16 : m % 16 = ((-ε) * q1 * zphiNorm a b) % 16 := by
      have heq : m = (-ε) * q1 * zphiNorm a b + 16 * (1 - 2 * K) := by linarith
      rw [heq, Int.add_mul_emod_self_left]
    have hprod := mod16_subgroup_mul (mod16_subgroup_mul hε_sub hq1) hN_sub
    unfold InMod16Subgroup at hprod ⊢
    rwa [hm_mod16]
  refine ⟨hm_odd, ?_, ?_⟩
  · intro h37
    have hm_sub := hm_sub_of_sq (by rw [h37])
    rw [h37] at hm_sub
    unfold InMod16Subgroup at hm_sub
    omega
  · intro hm37
    have hm_sub := hm_sub_of_sq (by rw [hm37]; norm_num)
    rw [hm37] at hm_sub
    unfold InMod16Subgroup at hm_sub
    omega

lemma sixteen_sqrt5_bounds :
    (35 : ℝ) < 16 * Real.sqrt 5 ∧ 16 * Real.sqrt 5 < 36 := by
  have h5_pos := sqrt5_pos
  have h5_sq := sqrt5_sq
  constructor
  · have hlt : (35 : ℝ) ^ 2 < (16 * Real.sqrt 5) ^ 2 := by nlinarith [h5_sq]
    nlinarith
  · have hlt : (16 * Real.sqrt 5) ^ 2 < (36 : ℝ) ^ 2 := by nlinarith [h5_sq]
    nlinarith

/-- $B = 4$ 谱隙核心不等式：
    $0 < 1 - \frac{35}{16\sqrt{5}} < \frac{37}{16\sqrt{5}} - 1 < 1 - \frac{33}{16\sqrt{5}} < \frac{39}{16\sqrt{5}} - 1$，
    对一切满足 $m \bmod 16 \in \{1, 7, 9, 15\}$ 且 $m \ne 33$ 的整数有
    $1 - \frac{33}{16\sqrt{5}} < \left|\frac{m}{16\sqrt{5}} - 1\right|$，
    且对一切奇数 $m \notin \{35, 37\}$ 有 $1 - \frac{33}{16\sqrt{5}} \le \left|\frac{m}{16\sqrt{5}} - 1\right|$。 -/
theorem b4_spectral_gap :
    (0 : ℝ) < 1 - 35 / (16 * Real.sqrt 5) ∧
    1 - 35 / (16 * Real.sqrt 5) < 37 / (16 * Real.sqrt 5) - 1 ∧
    37 / (16 * Real.sqrt 5) - 1 < 1 - 33 / (16 * Real.sqrt 5) ∧
    1 - 33 / (16 * Real.sqrt 5) < 39 / (16 * Real.sqrt 5) - 1 ∧
    (∀ m : ℤ, InMod16Subgroup m → m ≠ 33 →
      1 - 33 / (16 * Real.sqrt 5) < |(m : ℝ) / (16 * Real.sqrt 5) - 1|) ∧
    (∀ m : ℤ, Odd m → m ≠ 35 → m ≠ 37 →
      1 - 33 / (16 * Real.sqrt 5) ≤ |(m : ℝ) / (16 * Real.sqrt 5) - 1|) := by
  have h5_pos := sqrt5_pos
  have h165_pos : (0 : ℝ) < 16 * Real.sqrt 5 := mul_pos (by norm_num) h5_pos
  have h35 := sixteen_sqrt5_bounds.1
  have h36 := sixteen_sqrt5_bounds.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sub_pos, div_lt_one h165_pos]; exact h35
  · have hlt : (32 : ℝ) * Real.sqrt 5 < 72 := by linarith
    have hdiv : (2 : ℝ) < 72 / (16 * Real.sqrt 5) := by
      rw [lt_div_iff₀ h165_pos]; linarith
    have hsplit : (72 : ℝ) / (16 * Real.sqrt 5) = 35 / (16 * Real.sqrt 5) + 37 / (16 * Real.sqrt 5) := by ring
    linarith
  · have hlt : (70 : ℝ) / (16 * Real.sqrt 5) < 2 := by
      rw [div_lt_iff₀ h165_pos]; linarith
    have hsplit : (70 : ℝ) / (16 * Real.sqrt 5) = 37 / (16 * Real.sqrt 5) + 33 / (16 * Real.sqrt 5) := by ring
    linarith
  · have hdiv : (2 : ℝ) < 72 / (16 * Real.sqrt 5) := by
      rw [lt_div_iff₀ h165_pos]; linarith
    have hsplit : (72 : ℝ) / (16 * Real.sqrt 5) = 33 / (16 * Real.sqrt 5) + 39 / (16 * Real.sqrt 5) := by ring
    linarith
  · intro m hm_sub hm33
    have hcases : m ≤ 31 ∨ 39 ≤ m := by
      unfold InMod16Subgroup at hm_sub
      rcases hm_sub with h | h | h | h <;> omega
    rcases hcases with hle31 | hge39
    · have hmR : (m : ℝ) ≤ 31 := by exact_mod_cast hle31
      have hdiv : (m : ℝ) / (16 * Real.sqrt 5) ≤ 31 / (16 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h165_pos)
      have hlt1 : 31 / (16 * Real.sqrt 5) < 1 := (div_lt_one h165_pos).mpr (by linarith)
      rw [abs_of_neg (by linarith)]
      have h31_lt : 31 / (16 * Real.sqrt 5) < 33 / (16 * Real.sqrt 5) :=
        div_lt_div_of_pos_right (by norm_num) h165_pos
      linarith
    · have hmR : (39 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hge39
      have hdiv : 39 / (16 * Real.sqrt 5) ≤ (m : ℝ) / (16 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h165_pos)
      have hgt1 : 1 < 39 / (16 * Real.sqrt 5) := (one_lt_div h165_pos).mpr (by linarith)
      rw [abs_of_pos (by linarith)]
      have hdiv72 : (2 : ℝ) < 72 / (16 * Real.sqrt 5) := by
        rw [lt_div_iff₀ h165_pos]; linarith
      have hsplit : (72 : ℝ) / (16 * Real.sqrt 5) =
          33 / (16 * Real.sqrt 5) + 39 / (16 * Real.sqrt 5) := by ring
      linarith
  · intro m hm_odd hm35 hm37
    rcases hm_odd with ⟨k, rfl⟩
    have hcases : 2 * k + 1 ≤ 33 ∨ 39 ≤ 2 * k + 1 := by omega
    rcases hcases with hle33 | hge39
    · have hmR : ((2 * k + 1 : ℤ) : ℝ) ≤ 33 := by exact_mod_cast hle33
      have hdiv : ((2 * k + 1 : ℤ) : ℝ) / (16 * Real.sqrt 5) ≤ 33 / (16 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h165_pos)
      have hlt1 : 33 / (16 * Real.sqrt 5) < 1 := (div_lt_one h165_pos).mpr (by linarith)
      rw [abs_of_neg (by linarith)]
      linarith
    · have hmR : (39 : ℝ) ≤ ((2 * k + 1 : ℤ) : ℝ) := by exact_mod_cast hge39
      have hdiv : 39 / (16 * Real.sqrt 5) ≤ ((2 * k + 1 : ℤ) : ℝ) / (16 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h165_pos)
      have hgt1 : 1 < 39 / (16 * Real.sqrt 5) := (one_lt_div h165_pos).mpr (by linarith)
      rw [abs_of_pos (by linarith)]
      have hdiv72 : (2 : ℝ) < 72 / (16 * Real.sqrt 5) := by
        rw [lt_div_iff₀ h165_pos]; linarith
      have hsplit : (72 : ℝ) / (16 * Real.sqrt 5) =
          33 / (16 * Real.sqrt 5) + 39 / (16 * Real.sqrt 5) := by ring
      linarith

/-! #### 3.3 $B = 5$（$D = 50, d = 25$）与 $B = 6$（$D = 72, d = 36$） -/

/-- $B = 5$（$D = 50, d_0 = 25$）：$m$ 必为偶数。 -/
theorem b5_even_m {p1 q1 p2 q2 a b c d : ℤ}
    (hD : p1 * q2 + p2 * q1 = 50)
    (hgcd1 : Int.gcd p1 q1 = 1) (hgcd2 : Int.gcd p2 q2 = 1)
    (hdet : |a * d - b * c| = 1) :
    Even ((a * d - b * c) * (M_uv p1 q1 p2 q2 a b c d / 2)) := by
  have hrig := even_D_rigidity (d0 := 25) (by linarith) hgcd1 hgcd2 hdet
  have hmod2 := hrig.2.2.1
  rw [Int.modEq_iff_dvd] at hmod2
  rcases hmod2 with ⟨k, hk⟩
  exact ⟨-k + 13, by linarith⟩

lemma twentyfive_sqrt5_bounds :
    (55 : ℝ) < 25 * Real.sqrt 5 ∧ 25 * Real.sqrt 5 < 56 := by
  have h5_pos := sqrt5_pos
  have h5_sq := sqrt5_sq
  constructor
  · have hlt : (55 : ℝ) ^ 2 < (25 * Real.sqrt 5) ^ 2 := by nlinarith [h5_sq]
    nlinarith
  · have hlt : (25 * Real.sqrt 5) ^ 2 < (56 : ℝ) ^ 2 := by nlinarith [h5_sq]
    nlinarith

/-- $B = 5$ 谱隙核心不等式：
    $0 < \frac{56}{25\sqrt{5}} - 1 < 1 - \frac{54}{25\sqrt{5}} < \frac{58}{25\sqrt{5}} - 1$，
    且对一切偶数 $m \ne 56$ 有 $1 - \frac{54}{25\sqrt{5}} \le \left|\frac{m}{25\sqrt{5}} - 1\right|$。 -/
theorem b5_spectral_gap :
    (0 : ℝ) < 56 / (25 * Real.sqrt 5) - 1 ∧
    56 / (25 * Real.sqrt 5) - 1 < 1 - 54 / (25 * Real.sqrt 5) ∧
    1 - 54 / (25 * Real.sqrt 5) < 58 / (25 * Real.sqrt 5) - 1 ∧
    (∀ m : ℤ, Even m → m ≠ 56 →
      1 - 54 / (25 * Real.sqrt 5) ≤ |(m : ℝ) / (25 * Real.sqrt 5) - 1|) ∧
    (∀ m : ℤ, Even m → m ≠ 56 → m ≠ 54 →
      1 - 54 / (25 * Real.sqrt 5) < |(m : ℝ) / (25 * Real.sqrt 5) - 1|) := by
  have h5_pos := sqrt5_pos
  have h255_pos : (0 : ℝ) < 25 * Real.sqrt 5 := mul_pos (by norm_num) h5_pos
  have h55 := twentyfive_sqrt5_bounds.1
  have h56 := twentyfive_sqrt5_bounds.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sub_pos, one_lt_div h255_pos]; exact h56
  · have hdiv : (110 : ℝ) / (25 * Real.sqrt 5) < 2 := by
      rw [div_lt_iff₀ h255_pos]; linarith
    have hsplit : (110 : ℝ) / (25 * Real.sqrt 5) =
        56 / (25 * Real.sqrt 5) + 54 / (25 * Real.sqrt 5) := by ring
    linarith
  · have hdiv : (2 : ℝ) < 112 / (25 * Real.sqrt 5) := by
      rw [lt_div_iff₀ h255_pos]; linarith
    have hsplit : (112 : ℝ) / (25 * Real.sqrt 5) =
        54 / (25 * Real.sqrt 5) + 58 / (25 * Real.sqrt 5) := by ring
    linarith
  · intro m hm_even hm56
    rcases hm_even with ⟨k, rfl⟩
    have hcases : k + k ≤ 54 ∨ 58 ≤ k + k := by omega
    rcases hcases with hle54 | hge58
    · have hmR : ((k + k : ℤ) : ℝ) ≤ 54 := by exact_mod_cast hle54
      have hdiv : ((k + k : ℤ) : ℝ) / (25 * Real.sqrt 5) ≤ 54 / (25 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h255_pos)
      have hlt1 : 54 / (25 * Real.sqrt 5) < 1 := (div_lt_one h255_pos).mpr (by linarith)
      rw [abs_of_neg (by linarith)]
      linarith
    · have hmR : (58 : ℝ) ≤ ((k + k : ℤ) : ℝ) := by exact_mod_cast hge58
      have hdiv : 58 / (25 * Real.sqrt 5) ≤ ((k + k : ℤ) : ℝ) / (25 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h255_pos)
      have hgt1 : 1 < 58 / (25 * Real.sqrt 5) := (one_lt_div h255_pos).mpr (by linarith)
      rw [abs_of_pos (by linarith)]
      have hdiv112 : (2 : ℝ) < 112 / (25 * Real.sqrt 5) := by
        rw [lt_div_iff₀ h255_pos]; linarith
      have hsplit : (112 : ℝ) / (25 * Real.sqrt 5) =
          54 / (25 * Real.sqrt 5) + 58 / (25 * Real.sqrt 5) := by ring
      linarith
  · intro m hm_even hm56 hm54
    rcases hm_even with ⟨k, rfl⟩
    have hcases : k + k ≤ 52 ∨ 58 ≤ k + k := by omega
    rcases hcases with hle52 | hge58
    · have hmR : ((k + k : ℤ) : ℝ) ≤ 52 := by exact_mod_cast hle52
      have hdiv : ((k + k : ℤ) : ℝ) / (25 * Real.sqrt 5) ≤ 52 / (25 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h255_pos)
      have hlt1 : 52 / (25 * Real.sqrt 5) < 1 := (div_lt_one h255_pos).mpr (by linarith)
      rw [abs_of_neg (by linarith)]
      have h52_lt : 52 / (25 * Real.sqrt 5) < 54 / (25 * Real.sqrt 5) :=
        div_lt_div_of_pos_right (by norm_num) h255_pos
      linarith
    · have hmR : (58 : ℝ) ≤ ((k + k : ℤ) : ℝ) := by exact_mod_cast hge58
      have hdiv : 58 / (25 * Real.sqrt 5) ≤ ((k + k : ℤ) : ℝ) / (25 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h255_pos)
      have hgt1 : 1 < 58 / (25 * Real.sqrt 5) := (one_lt_div h255_pos).mpr (by linarith)
      rw [abs_of_pos (by linarith)]
      have hdiv112 : (2 : ℝ) < 112 / (25 * Real.sqrt 5) := by
        rw [lt_div_iff₀ h255_pos]; linarith
      have hsplit : (112 : ℝ) / (25 * Real.sqrt 5) =
          54 / (25 * Real.sqrt 5) + 58 / (25 * Real.sqrt 5) := by ring
      linarith

/-- $B = 6$（$D = 72, d_0 = 36$）：$m$ 必为奇数且惰性素数 $3 \mid 36$ 刚性禁除 $3 \mid m$（特别地 $m \ne 81$）。 -/
theorem b6_inert_three_not_dvd_m {p1 q1 p2 q2 a b c d : ℤ}
    (hD : p1 * q2 + p2 * q1 = 72)
    (hgcd1 : Int.gcd p1 q1 = 1) (hgcd2 : Int.gcd p2 q2 = 1)
    (hdet : |a * d - b * c| = 1) :
    let m := (a * d - b * c) * (M_uv p1 q1 p2 q2 a b c d / 2)
    Odd m ∧ ¬ ((3 : ℤ) ∣ m) ∧ m ≠ 81 := by
  have hrig := even_D_rigidity (d0 := 36) (by linarith) hgcd1 hgcd2 hdet
  dsimp only at hrig ⊢
  have hodd : Odd ((a * d - b * c) * (M_uv p1 q1 p2 q2 a b c d / 2)) := by
    have hmod2 := hrig.2.2.1
    rw [Int.modEq_iff_dvd] at hmod2
    rcases hmod2 with ⟨k, hk⟩
    exact ⟨18 - k, by linarith⟩
  have hn3 : ¬ ((3 : ℤ) ∣ (a * d - b * c) * (M_uv p1 q1 p2 q2 a b c d / 2)) :=
    hrig.2.2.2 3 (by norm_num) (Or.inr rfl) (by norm_num)
  refine ⟨hodd, hn3, ?_⟩
  intro h81
  apply hn3
  rw [h81]
  exact ⟨27, by norm_num⟩

lemma thirtysix_sqrt5_bounds :
    (80 : ℝ) < 36 * Real.sqrt 5 ∧ 36 * Real.sqrt 5 < 81 := by
  have h5_pos := sqrt5_pos
  have h5_sq := sqrt5_sq
  constructor
  · have hlt : (80 : ℝ) ^ 2 < (36 * Real.sqrt 5) ^ 2 := by nlinarith [h5_sq]
    nlinarith
  · have hlt : (36 * Real.sqrt 5) ^ 2 < (81 : ℝ) ^ 2 := by nlinarith [h5_sq]
    nlinarith

/-- $B = 6$ 谱隙核心不等式：
    $0 < \frac{81}{36\sqrt{5}} - 1 < 1 - \frac{79}{36\sqrt{5}} < \frac{83}{36\sqrt{5}} - 1$，
    由惰性素数 $3$ 禁除 $m = 81$ 后，对一切不被 $3$ 整除的奇数 $m$ 恒有
    $1 - \frac{79}{36\sqrt{5}} \le \left|\frac{m}{36\sqrt{5}} - 1\right|$（$m \ne 79$ 时严格大于）。 -/
theorem b6_spectral_gap :
    (0 : ℝ) < 81 / (36 * Real.sqrt 5) - 1 ∧
    81 / (36 * Real.sqrt 5) - 1 < 1 - 79 / (36 * Real.sqrt 5) ∧
    1 - 79 / (36 * Real.sqrt 5) < 83 / (36 * Real.sqrt 5) - 1 ∧
    (∀ m : ℤ, Odd m → ¬ ((3 : ℤ) ∣ m) →
      1 - 79 / (36 * Real.sqrt 5) ≤ |(m : ℝ) / (36 * Real.sqrt 5) - 1|) ∧
    (∀ m : ℤ, Odd m → ¬ ((3 : ℤ) ∣ m) → m ≠ 79 →
      1 - 79 / (36 * Real.sqrt 5) < |(m : ℝ) / (36 * Real.sqrt 5) - 1|) := by
  have h5_pos := sqrt5_pos
  have h365_pos : (0 : ℝ) < 36 * Real.sqrt 5 := mul_pos (by norm_num) h5_pos
  have h80 := thirtysix_sqrt5_bounds.1
  have h81 := thirtysix_sqrt5_bounds.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sub_pos, one_lt_div h365_pos]; exact h81
  · have hdiv : (160 : ℝ) / (36 * Real.sqrt 5) < 2 := by
      rw [div_lt_iff₀ h365_pos]; linarith
    have hsplit : (160 : ℝ) / (36 * Real.sqrt 5) =
        81 / (36 * Real.sqrt 5) + 79 / (36 * Real.sqrt 5) := by ring
    linarith
  · have hdiv : (2 : ℝ) < 162 / (36 * Real.sqrt 5) := by
      rw [lt_div_iff₀ h365_pos]; linarith
    have hsplit : (162 : ℝ) / (36 * Real.sqrt 5) =
        79 / (36 * Real.sqrt 5) + 83 / (36 * Real.sqrt 5) := by ring
    linarith
  · intro m hm_odd hm_n3
    rcases hm_odd with ⟨k, rfl⟩
    have hk_ne40 : 2 * k + 1 ≠ 81 := by
      intro h; apply hm_n3; exact ⟨27, by omega⟩
    have hcases : 2 * k + 1 ≤ 79 ∨ 83 ≤ 2 * k + 1 := by omega
    rcases hcases with hle79 | hge83
    · have hmR : ((2 * k + 1 : ℤ) : ℝ) ≤ 79 := by exact_mod_cast hle79
      have hdiv : ((2 * k + 1 : ℤ) : ℝ) / (36 * Real.sqrt 5) ≤ 79 / (36 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h365_pos)
      have hlt1 : 79 / (36 * Real.sqrt 5) < 1 := (div_lt_one h365_pos).mpr (by linarith)
      rw [abs_of_neg (by linarith)]
      linarith
    · have hmR : (83 : ℝ) ≤ ((2 * k + 1 : ℤ) : ℝ) := by exact_mod_cast hge83
      have hdiv : 83 / (36 * Real.sqrt 5) ≤ ((2 * k + 1 : ℤ) : ℝ) / (36 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h365_pos)
      have hgt1 : 1 < 83 / (36 * Real.sqrt 5) := (one_lt_div h365_pos).mpr (by linarith)
      rw [abs_of_pos (by linarith)]
      have hdiv162 : (2 : ℝ) < 162 / (36 * Real.sqrt 5) := by
        rw [lt_div_iff₀ h365_pos]; linarith
      have hsplit : (162 : ℝ) / (36 * Real.sqrt 5) =
          79 / (36 * Real.sqrt 5) + 83 / (36 * Real.sqrt 5) := by ring
      linarith
  · intro m hm_odd hm_n3 hm79
    rcases hm_odd with ⟨k, rfl⟩
    have hk_ne40 : 2 * k + 1 ≠ 81 := by
      intro h; apply hm_n3; exact ⟨27, by omega⟩
    have hcases : 2 * k + 1 ≤ 77 ∨ 83 ≤ 2 * k + 1 := by omega
    rcases hcases with hle77 | hge83
    · have hmR : ((2 * k + 1 : ℤ) : ℝ) ≤ 77 := by exact_mod_cast hle77
      have hdiv : ((2 * k + 1 : ℤ) : ℝ) / (36 * Real.sqrt 5) ≤ 77 / (36 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h365_pos)
      have hlt1 : 77 / (36 * Real.sqrt 5) < 1 := (div_lt_one h365_pos).mpr (by linarith)
      rw [abs_of_neg (by linarith)]
      have h77_lt : 77 / (36 * Real.sqrt 5) < 79 / (36 * Real.sqrt 5) :=
        div_lt_div_of_pos_right (by norm_num) h365_pos
      linarith
    · have hmR : (83 : ℝ) ≤ ((2 * k + 1 : ℤ) : ℝ) := by exact_mod_cast hge83
      have hdiv : 83 / (36 * Real.sqrt 5) ≤ ((2 * k + 1 : ℤ) : ℝ) / (36 * Real.sqrt 5) :=
        div_le_div_of_nonneg_right hmR (le_of_lt h365_pos)
      have hgt1 : 1 < 83 / (36 * Real.sqrt 5) := (one_lt_div h365_pos).mpr (by linarith)
      rw [abs_of_pos (by linarith)]
      have hdiv162 : (2 : ℝ) < 162 / (36 * Real.sqrt 5) := by
        rw [lt_div_iff₀ h365_pos]; linarith
      have hsplit : (162 : ℝ) / (36 * Real.sqrt 5) =
          79 / (36 * Real.sqrt 5) + 83 / (36 * Real.sqrt 5) := by ring
      linarith

end GeneralEndpointRigidity

/-! ### 4. 本模块全量导出定理公理审计（仅允许 `[propext, Classical.choice, Quot.sound]`） -/

#print axioms GeneralEndpointRigidity.cfMatrix_det
#print axioms GeneralEndpointRigidity.cfMatrix_eval_eq
#print axioms GeneralEndpointRigidity.eta_conj_ge_inv_sq_of_gt_one
#print axioms GeneralEndpointRigidity.eta_conj_add_pos_gt_abs
#print axioms GeneralEndpointRigidity.eta_conj_eq_inv_sq_at_two
#print axioms GeneralEndpointRigidity.xi1_xi2Conj_identity
#print axioms GeneralEndpointRigidity.Muv_norm_identity
#print axioms GeneralEndpointRigidity.mobius_ratio_identity
#print axioms GeneralEndpointRigidity.ratio_eq_Muv_sub_div
#print axioms GeneralEndpointRigidity.inert_legendreSym_five_eq_neg_one
#print axioms GeneralEndpointRigidity.inert_prime_dvd_zphiNorm_iff
#print axioms GeneralEndpointRigidity.inert_prime_not_dvd_zphiNorm_of_cond
#print axioms GeneralEndpointRigidity.inert_prime_not_dvd_zphiNorm
#print axioms GeneralEndpointRigidity.inert_prime_not_dvd_zphiNorm_xi2
#print axioms GeneralEndpointRigidity.even_D_Muv_even
#print axioms GeneralEndpointRigidity.even_D_rigidity
#print axioms GeneralEndpointRigidity.even_D_rigidity_functional
#print axioms GeneralEndpointRigidity.mod_2D_sieve_q
#print axioms GeneralEndpointRigidity.mod_2D_sieve_p
#print axioms GeneralEndpointRigidity.mod_2d_sieve_special
#print axioms GeneralEndpointRigidity.Muv_norm_ne_zero
#print axioms GeneralEndpointRigidity.zphiNorm_xi2_dvd_norm_quot
#print axioms GeneralEndpointRigidity.b3_inert_three_not_dvd_m
#print axioms GeneralEndpointRigidity.b3_spectral_gap
#print axioms GeneralEndpointRigidity.b4_mod16_excludes_37
#print axioms GeneralEndpointRigidity.b4_spectral_gap
#print axioms GeneralEndpointRigidity.b5_even_m
#print axioms GeneralEndpointRigidity.b5_spectral_gap
#print axioms GeneralEndpointRigidity.b6_inert_three_not_dvd_m
#print axioms GeneralEndpointRigidity.b6_spectral_gap
