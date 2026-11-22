import EpiFormal.WindowLevelCount
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic

/-!
# P2a：词树组合子（纯组合，无停止规则、无 H_j）

`levelWords D j` = 字母表 `D` 上的长 `j` 词全体（Finset）。
`childrenOf D w` = `w` 的单字母延长全体。
主结论：`uniform_level_count`（`D.card ^ J ≤ #(levelWords D J)`），
为多层分支计数的均匀分支特例（`level_count_ge` 的实例化）。
-/

namespace WindowWordTree

/-- 单字母延长全体。 -/
def childrenOf (D : Finset ℕ) (w : List ℕ) : Finset (List ℕ) :=
  D.image (fun a => w ++ [a])

/-- 长 j 词全体（递归构造）。 -/
def levelWords (D : Finset ℕ) : ℕ → Finset (List ℕ)
  | 0 => {([] : List ℕ)}
  | (j + 1) => (levelWords D j).biUnion (fun w => childrenOf D w)

/-- 成员刻画：`x ∈ childrenOf D w ↔ ∃ a ∈ D, x = w ++ [a]`。 -/
theorem mem_childrenOf (D : Finset ℕ) (w x : List ℕ) :
    x ∈ childrenOf D w ↔ ∃ a ∈ D, x = w ++ [a] := by
  simp [childrenOf, eq_comm]

/-- 单射性：`w ++ [·]` 单。 -/
theorem append_single_injective (w : List ℕ) :
    Function.Injective (fun a => w ++ [a]) := by
  intro a b hab
  have hlen : w.length = w.length := rfl
  have h := List.append_inj hab hlen
  simpa using h.right

/-- 子族基数：`|childrenOf D w| = |D|`。 -/
theorem childrenOf_card (D : Finset ℕ) (w : List ℕ) :
    (childrenOf D w).card = D.card := by
  rw [childrenOf, Finset.card_image_of_injective _ (append_single_injective w)]

/-- 落入下一层。 -/
theorem children_mem_next (D : Finset ℕ) (j : ℕ) (w : List ℕ)
    (hw : w ∈ levelWords D j) :
    childrenOf D w ⊆ levelWords D (j + 1) := by
  intro x hx
  rw [levelWords, Finset.mem_biUnion]
  exact ⟨w, hw, hx⟩

/-- 不同父词的子族不交（前缀唯一性）。 -/
theorem children_disjoint (D : Finset ℕ) (w₁ w₂ : List ℕ) (hne : w₁ ≠ w₂) :
    Disjoint (childrenOf D w₁) (childrenOf D w₂) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rw [mem_childrenOf] at hx1 hx2
  obtain ⟨a, -, rfl⟩ := hx1
  obtain ⟨b, -, hxb⟩ := hx2
  have hlen : w₁.length = w₂.length := by
    have h := congrArg List.length hxb
    simpa using h
  have h := List.append_inj hxb hlen
  exact absurd h.1 hne

/-- 空词在第 0 层。 -/
theorem nil_mem_levelWords_zero (D : Finset ℕ) : [] ∈ levelWords D 0 :=
  Finset.mem_singleton_self []

/-- 均匀分支计数：`|D|^J ≤ #(levelWords D J)`。 -/
theorem uniform_level_count (D : Finset ℕ) (J : ℕ) :
    D.card ^ J ≤ (levelWords D J).card := by
  have h := WindowLevelCount.level_count_ge (fun j => levelWords D j)
    (fun _ => D.card) (fun _ w => childrenOf D w) 0 J (Nat.zero_le J)
    (by exact Finset.singleton_nonempty _)
    (fun j a ha => children_mem_next D j a ha)
    (fun j a _ => by rw [childrenOf_card])
    (fun j a₁ ha₁ a₂ _ hne => children_disjoint D a₁ a₂ hne)
  simpa using h

#print axioms WindowWordTree.mem_childrenOf
#print axioms WindowWordTree.append_single_injective
#print axioms WindowWordTree.childrenOf_card
#print axioms WindowWordTree.children_mem_next
#print axioms WindowWordTree.children_disjoint
#print axioms WindowWordTree.nil_mem_levelWords_zero
#print axioms WindowWordTree.uniform_level_count

end WindowWordTree
