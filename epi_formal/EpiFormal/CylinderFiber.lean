import EpiFormal.CylinderPhaseE

/-!
# Cylinder Phase E4b：子柱纤维计数（paper2 §7 thm:windows 的 Frostman 组装）

子柱结构：词 `w` 的子柱为 `w ++ [k]`（`k ∈ Icc 1 K`，连分数部分商 ≥ 1）。
本文件提供子柱集的定义、基数与同层一致性——Hinter discharge
中"固定层的每个父柱细化数为同一常数"的组合输入。

- `children w K`：`w` 的子柱有限集。
- `card_children`：基数恒为 `K`（与父词无关——纤维一致性的定量形式）。
- `fiber_card_eq`：同层两父柱的子柱数相等（Hinter 接口形状）。
- `child_prefix_self`：子柱以前缀词为前缀（嵌套性）。

## 状态

部分验证：单文件 `lake env lean` 通过后接线。
-/

namespace Cylinder

/-- 词 `w` 的子柱集（部分商取 `1..K`）。 -/
noncomputable def children (w : List ℕ) (K : ℕ) : Finset (List ℕ) :=
  (Finset.Icc 1 K).image (fun k => w ++ [k])

theorem mem_children_iff (w : List ℕ) (K : ℕ) (v : List ℕ) :
    v ∈ children w K ↔ ∃ j ∈ Finset.Icc 1 K, w ++ [j] = v := by
  unfold children
  exact Finset.mem_image

theorem card_children (w : List ℕ) (K : ℕ) : (children w K).card = K := by
  unfold children
  rw [Finset.card_image_of_injective]
  · rw [Nat.card_Icc]
    exact Nat.add_sub_cancel K 1
  · intro a b hab
    simpa using hab

/-- 同层纤维一致性：两父柱的子柱数相等（仅依赖 K）。 -/
theorem fiber_card_eq (w₁ w₂ : List ℕ) (K : ℕ) :
    (children w₁ K).card = (children w₂ K).card := by
  rw [card_children, card_children]

/-- 子柱以父词为前缀。 -/
theorem child_prefix_self (w : List ℕ) (K : ℕ) (v : List ℕ)
    (hv : v ∈ children w K) : w <+: v := by
  obtain ⟨j, _, rfl⟩ := (mem_children_iff w K v).mp hv
  exact List.prefix_append w [j]

#print axioms Cylinder.children
#print axioms Cylinder.mem_children_iff
#print axioms Cylinder.card_children
#print axioms Cylinder.fiber_card_eq
#print axioms Cylinder.child_prefix_self

end Cylinder