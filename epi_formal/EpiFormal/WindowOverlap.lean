import Mathlib
import EpiFormal.CylinderPhaseE
import EpiFormal.WindowCoverCount

/-!
# Stopped-cylinder length bounds and window overlap count (paper2 §7)

For stopped cylinders whose consecutive denominators lie in `[4H/3, 5H/2]`,
the length `1/(q₀q₁)` lies in `[4/(25H²), 9/(16H²)]` (cf. paper L2545-2547:
`(25/2)^{-1}H_j^{-2} ≤ |I_j| ≤ (9/16)H_j^{-2}`; our consecutive-children
diameter gives the marginally stronger lower constant `4/25`).

Corollary: any window of width `h ≤ 1/H²` meets at most `753/64 < 12`
cylinders (paper: `≤ 15` interiors `+ 2` endpoints `= 17`; any fixed
constant works for the `O(h^s)` conclusion).
-/

namespace CoverCount

/-- Pure length bounds from denominator ranges. -/
theorem child_len_bounds {q₀ q₁ H : ℝ} (hH : 0 < H)
    (hlo0 : 4 * H / 3 ≤ q₀) (hhi0 : q₀ ≤ 5 * H / 2)
    (hlo1 : 4 * H / 3 ≤ q₁) (hhi1 : q₁ ≤ 5 * H / 2) :
    4 / (25 * H ^ 2) ≤ 1 / (q₀ * q₁) ∧ 1 / (q₀ * q₁) ≤ 9 / (16 * H ^ 2) := by
  have hq0 : 0 < q₀ := lt_of_lt_of_le (by positivity) hlo0
  have hq1 : 0 < q₁ := lt_of_lt_of_le (by positivity) hlo1
  have hbase : (0 : ℝ) < 4 / (25 * H ^ 2) := by positivity
  constructor
  · have hprod : q₀ * q₁ ≤ (5 * H / 2) * (5 * H / 2) :=
      mul_le_mul hhi0 hhi1 (le_of_lt hq1) (by linarith)
    have e : (4 : ℝ) / (25 * H ^ 2) = 1 / ((5 * H / 2) ^ 2) := by
      field_simp
      ring
    rw [e]
    exact one_div_le_one_div_of_le (mul_pos hq0 hq1)
      (calc q₀ * q₁ ≤ (5 * H / 2) * (5 * H / 2) := hprod
        _ = (5 * H / 2) ^ 2 := by ring)
  · have hprod : (4 * H / 3) * (4 * H / 3) ≤ q₀ * q₁ :=
      mul_le_mul hlo0 hlo1 (by positivity) (le_of_lt hq0)
    have e : (9 : ℝ) / (16 * H ^ 2) = 1 / ((4 * H / 3) ^ 2) := by
      field_simp
      ring
    rw [e]
    exact one_div_le_one_div_of_le (by positivity)
      (calc (4 * H / 3) ^ 2 = (4 * H / 3) * (4 * H / 3) := by ring
        _ ≤ q₀ * q₁ := hprod)

/-- Instantiation to consecutive-children cylinder diameters. -/
theorem stopped_cyl_len_bounds (w : List ℕ) (k : ℕ) (hk : 1 ≤ k)
    (H : ℝ) (hH : 0 < H)
    (hlo : 4 * H / 3 ≤ Cylinder.cylDen (Cylinder.cfProd (w ++ [k])))
    (hhi : Cylinder.cylDen (Cylinder.cfProd (w ++ [k])) ≤ 5 * H / 2)
    (hlo' : 4 * H / 3 ≤ Cylinder.cylDen (Cylinder.cfProd (w ++ [k + 1])))
    (hhi' : Cylinder.cylDen (Cylinder.cfProd (w ++ [k + 1])) ≤ 5 * H / 2) :
    4 / (25 * H ^ 2) ≤ Metric.diam (Set.Icc
      (min (Cylinder.cylFrac (Cylinder.cfProd (w ++ [k + 1])))
        (Cylinder.cylFrac (Cylinder.cfProd (w ++ [k]))))
      (max (Cylinder.cylFrac (Cylinder.cfProd (w ++ [k + 1])))
        (Cylinder.cylFrac (Cylinder.cfProd (w ++ [k])))))
      ∧ Metric.diam (Set.Icc
      (min (Cylinder.cylFrac (Cylinder.cfProd (w ++ [k + 1])))
        (Cylinder.cylFrac (Cylinder.cfProd (w ++ [k]))))
      (max (Cylinder.cylFrac (Cylinder.cfProd (w ++ [k + 1])))
        (Cylinder.cylFrac (Cylinder.cfProd (w ++ [k])))))
      ≤ 9 / (16 * H ^ 2) := by
  rw [Cylinder.child_cyl_diam w k hk]
  exact child_len_bounds hH hlo' hhi' hlo hhi

/-- Window overlap bound: at most `753/64 < 12` cylinders meet a window
of width `h ≤ 1/H²` (paper: `≤ 15 + 2 = 17`). -/
theorem window_overlap_le {H h x : ℝ} (hH : 0 < H) (hh0 : 0 ≤ h)
    (hhH : h ≤ 1 / H ^ 2)
    (F : Finset (ℝ × ℝ))
    (htriv : ∀ I ∈ F, I.1 < I.2)
    (hlen : ∀ I ∈ F, 4 / (25 * H ^ 2) ≤ I.2 - I.1 ∧ I.2 - I.1 ≤ 9 / (16 * H ^ 2))
    (hdisj : ∀ I ∈ F, ∀ J ∈ F, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hmeet : ∀ I ∈ F, I.1 ≤ x ∧ x - h ≤ I.2) :
    ((F.card : ℕ) : ℝ) ≤ 753 / 64 := by
  have hm : (0 : ℝ) < 4 / (25 * H ^ 2) := by positivity
  have hM : (0 : ℝ) ≤ 9 / (16 * H ^ 2) := by positivity
  have hcard := CoverCount.meet_card_le hm (by linarith : x - h ≤ x) hM F htriv
    (fun I hI => (hlen I hI).1) (fun I hI => (hlen I hI).2) hdisj hmeet
  have hT : (0 : ℝ) < H ^ 2 := by positivity
  have hHne : H ≠ 0 := ne_of_gt hH
  have hwin : x - (x - h) = h := by ring
  rw [hwin] at hcard
  have e1 : (h + 9 / (16 * H ^ 2)) / (4 / (25 * H ^ 2)) + 2 ≤ 753 / 64 := by
    have h1 : (h + 9 / (16 * H ^ 2)) / (4 / (25 * H ^ 2))
        = (h + 9 / (16 * H ^ 2)) * (25 * H ^ 2 / 4) := by
      rw [div_eq_mul_inv, inv_div]
    rw [h1]
    have h2 : (h + 9 / (16 * H ^ 2)) * (25 * H ^ 2 / 4)
        ≤ (1 / H ^ 2 + 9 / (16 * H ^ 2)) * (25 * H ^ 2 / 4) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [hhH]
    have h3 : (1 / H ^ 2 + 9 / (16 * H ^ 2)) * (25 * H ^ 2 / 4) = 625 / 64 := by
      field_simp
      ring
    linarith
  linarith

#print axioms CoverCount.child_len_bounds
#print axioms CoverCount.stopped_cyl_len_bounds
#print axioms CoverCount.window_overlap_le

end CoverCount
