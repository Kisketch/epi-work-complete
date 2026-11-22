import Mathlib

/-!
# Hinter discharge 通用双件（Frostman S6/S7 形状）

`frostman_of_count_thresh` 的接口 `Hinter` 需要两件：
`Hcount : 1 ≤ Σ Kc/M`（S6，双计数）与 `Hthresh : Kc/M ≤ (diam)^s`（S7，阈值桥）。
本文件提供两者与具体几何无关的通用形式，应用方（windows）只需代入
`Kc`（交数）、`M`（原子总数）、`C`（一致交数上界）、`t`（直径下界）。
-/

namespace HinterBridge

/-- S7 阈值桥：一致交数界 + 阈值不等式 + 直径下界 ⇒ 逐点 Hinter 不等式。 -/
theorem thresh_bridge {ι : Type} {V : ι → Set ℝ} {F : Finset ι}
    {Kc : ι → ℕ} {M C t s : ℝ}
    (hM : 0 < M) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hKc : ∀ i ∈ F, (Kc i : ℝ) ≤ C)
    (hCM : C / M ≤ t ^ s)
    (hdiam : ∀ i ∈ F, t ≤ Metric.diam (V i))
    : ∀ i ∈ F, ((Kc i : ℝ) / M) ≤ (Metric.diam (V i)) ^ s := by
  intro i hi
  calc ((Kc i : ℝ) / M) ≤ C / M := by
        have h := hKc i hi
        gcongr
    _ ≤ t ^ s := hCM
    _ ≤ (Metric.diam (V i)) ^ s :=
        Real.rpow_le_rpow ht (hdiam i hi) hs

/-- S6 双计数：每个原子都交 F 中某集，则原子总数 ≤ 交数之和。
`meet` 为"原子 a 交集合 V i"的可判定关系，`Kc i` 为其上界计数。 -/
theorem fiber_count_ge {ι α : Type} [DecidableEq ι] [DecidableEq α]
    {F : Finset ι} {A : Finset α} {meet : α → ι → Prop} [∀ a i, Decidable (meet a i)]
    (hcover : ∀ a ∈ A, ∃ i ∈ F, meet a i)
    {Kc : ι → ℕ}
    (hKc : ∀ i ∈ F, ((A.filter (fun a => meet a i)).card : ℝ) ≤ Kc i)
    : (A.card : ℝ) ≤ ∑ i ∈ F, (Kc i : ℝ) := by
  by_cases hA : A.Nonempty
  · obtain ⟨a0, ha0⟩ := hA
    obtain ⟨i0, hi0F, _⟩ := hcover a0 ha0
    have hex : ∀ a : α, ∃ i : ι, a ∈ A → i ∈ F ∧ meet a i := by
      intro a
      by_cases ha : a ∈ A
      · obtain ⟨i, hiF, hmi⟩ := hcover a ha
        exact ⟨i, fun _ => ⟨hiF, hmi⟩⟩
      · exact ⟨i0, fun h => absurd h ha⟩
    choose f hf using hex
    have hfF : ∀ a, a ∈ A → f a ∈ F := fun a ha => (hf a ha).1
    have hfmeet : ∀ a, a ∈ A → meet a (f a) := fun a ha => (hf a ha).2
    have hsub : A.image f ⊆ F := by
      intro i hi
      simp only [Finset.mem_image] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      exact hfF a ha
    have hAeq : A = (A.image f).biUnion (fun i => A.filter (fun a => f a = i)) := by
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
      constructor
      · intro ha
        exact ⟨f a, ⟨a, ha, rfl⟩, ha, rfl⟩
      · rintro ⟨i, ⟨b, hb, rfl⟩, ha, -⟩
        exact ha
    have hdisj : Set.PairwiseDisjoint (↑(A.image f)) (fun i => A.filter (fun a => f a = i)) := by
      intro i _ j _ hij
      simp only [Finset.disjoint_filter]
      intro a _ hai haj
      have e1 : f a = i := hai
      have e2 : f a = j := haj
      exact hij (e1.symm.trans e2)
    have hcard : (A.card : ℝ)
        = ∑ i ∈ A.image f, (((A.filter (fun a => f a = i)).card : ℕ) : ℝ) := by
      conv_lhs => rw [hAeq, Finset.card_biUnion hdisj]
      simp only [Nat.cast_sum]
    rw [hcard]
    calc ∑ i ∈ A.image f, (((A.filter (fun a => f a = i)).card : ℕ) : ℝ)
        ≤ ∑ i ∈ A.image f, (Kc i : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have hiF : i ∈ F := hsub hi
          have hmono : A.filter (fun a => f a = i) ⊆ A.filter (fun a => meet a i) := by
            intro a ha
            simp only [Finset.mem_filter] at ha ⊢
            refine ⟨ha.1, ?_⟩
            exact ha.2 ▸ hfmeet a ha.1
          have hle : (A.filter (fun a => f a = i)).card ≤ (A.filter (fun a => meet a i)).card :=
            Finset.card_le_card hmono
          have h1 : (((A.filter (fun a => f a = i)).card : ℕ) : ℝ)
              ≤ ((A.filter (fun a => meet a i)).card : ℝ) := by
            exact_mod_cast hle
          exact le_trans h1 (hKc i hiF)
      _ ≤ ∑ i ∈ F, (Kc i : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.cast_nonneg _)
  · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst hA0
    simp only [Finset.card_empty, Nat.cast_zero]
    exact Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)

#print axioms thresh_bridge
#print axioms fiber_count_ge

end HinterBridge
