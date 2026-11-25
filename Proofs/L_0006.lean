import Specs.L_0006

namespace Proofs.L_0006

open Set

theorem main : Specs.L_0006.stmt := by
  unfold Specs.L_0006.stmt MSpace.Goals.T2c_stratifiable_perfectlyNormal
  intro X _ hX
  obtain ⟨_, G, hOpen, hSub, hInt, _⟩ := hX
  -- 有限共通部分で単調減少化
  let G' : ℕ → Set X → Set X := fun n H => ⋂ k ∈ Finset.range (n+1), G k H
  have G'open : ∀ n H, IsClosed H → IsOpen (G' n H) := fun n H hH =>
    isOpen_biInter_finset (fun k _ => hOpen k H hH)
  have G'le : ∀ n H, G' n H ⊆ G n H := fun n H =>
    biInter_subset_of_mem (Finset.mem_range.2 (Nat.lt_succ_self n))
  have G'anti : ∀ n m H, n ≤ m → G' m H ⊆ G' n H := by
    intro n m H hnm
    intro x hx
    simp only [G', mem_iInter, Finset.mem_range] at hx ⊢
    intro k hk
    exact hx k (by omega)
  have G'sub : ∀ n H, IsClosed H → H ⊆ G' n H := by
    intro n H hH x hx
    simp only [G', mem_iInter]
    intro k _
    exact hSub k H hH hx
  have G'cl : ∀ H, IsClosed H → ∀ x, x ∉ H → ∃ n, x ∉ closure (G' n H) := by
    intro H hH x hx
    rw [← hInt H hH, mem_iInter] at hx
    push_neg at hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, fun h => hn (closure_mono (G'le n H) h)⟩
  refine ⟨⟨fun H K hH hK hHK => ?_⟩, fun C hC => ?_⟩
  · refine ⟨⋃ n, (G' n H \ closure (G' n K)), ⋃ n, (G' n K \ closure (G' n H)),
      isOpen_iUnion fun n => (G'open n H hH).sdiff isClosed_closure,
      isOpen_iUnion fun n => (G'open n K hK).sdiff isClosed_closure, ?_, ?_, ?_⟩
    · intro x hx
      have hxK : x ∉ K := fun h => Set.disjoint_left.1 hHK hx h
      obtain ⟨n, hn⟩ := G'cl K hK x hxK
      exact mem_iUnion.2 ⟨n, G'sub n H hH hx, hn⟩
    · intro x hx
      have hxH : x ∉ H := fun h => Set.disjoint_left.1 hHK h hx
      obtain ⟨n, hn⟩ := G'cl H hH x hxH
      exact mem_iUnion.2 ⟨n, G'sub n K hK hx, hn⟩
    · rw [Set.disjoint_left]
      intro x hx1 hx2
      obtain ⟨n, hn1, hn2⟩ := mem_iUnion.1 hx1
      obtain ⟨m, hm1, hm2⟩ := mem_iUnion.1 hx2
      rcases le_total n m with h | h
      · exact hn2 (subset_closure (G'anti n m K h hm1))
      · exact hm2 (subset_closure (G'anti m n H h hn1))
  · have : C = ⋂ n, G n C := by
      apply Subset.antisymm
      · exact subset_iInter fun n => hSub n C hC
      · calc ⋂ n, G n C ⊆ ⋂ n, closure (G n C) := iInter_mono fun n => subset_closure
          _ = C := hInt C hC
    rw [this]
    exact IsGδ.iInter_of_isOpen fun n => hOpen n C hC

end Proofs.L_0006
