import Targets

namespace ChildResearch.BoundaryExpansion

open Set MSpace

theorem closure_expansions_inter_subset {X : Type} [TopologicalSpace X]
    (M : Set X) (O : ℕ → Set X) (G : ℕ → Set X → Set X)
    (hO : ∀ n, Disjoint (closure (O n)) M)
    (hmono : ∀ n, Monotone (G n))
    (hanti : ∀ C, Antitone (fun n => G n C))
    (hsep : ∀ C, IsClosed C → ∀ y ∉ C, ∃ n, y ∉ closure (G n C))
    (F : Set (Set X)) (hclosed : ∀ C ∈ F, IsClosed C)
    (hCP : ClosurePreserving F) :
    closure (⋃ C ∈ F, ⋃ n, O n ∩ G n C) ∩ M ⊆ (⋃₀ F) ∩ M := by
  have hF : IsClosed (⋃₀ F) := by
    rw [← closure_eq_iff_isClosed, hCP F Subset.rfl]
    congr 1
    ext C
    constructor
    · rintro ⟨B, hB, rfl⟩
      simpa only [(hclosed B hB).closure_eq] using hB
    · intro hC
      exact ⟨C, hC, (hclosed C hC).closure_eq⟩
  rintro y ⟨hy, hyM⟩
  refine ⟨?_, hyM⟩
  by_contra hyF
  obtain ⟨m, hm⟩ := hsep _ hF y hyF
  let E : Set X := ⋃ n ∈ Finset.range m, closure (O n)
  have hE : IsClosed E :=
    isClosed_biUnion_finset (fun _ _ => isClosed_closure)
  have hyE : y ∉ E := by
    intro h
    obtain ⟨n, _, hn⟩ := mem_iUnion₂.mp h
    exact Set.disjoint_left.mp (hO n) hn hyM
  have hcover : (⋃ C ∈ F, ⋃ n, O n ∩ G n C) ⊆ E ∪ closure (G m (⋃₀ F)) := by
    intro z hz
    obtain ⟨C, hC, hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    by_cases hnm : n < m
    · exact Or.inl (mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr hnm, subset_closure hn.1⟩)
    · exact Or.inr (subset_closure (hanti _ (Nat.le_of_not_gt hnm)
        (hmono n (subset_sUnion_of_mem hC) hn.2)))
  exact (closure_minimal hcover (hE.union isClosed_closure) hy).elim hyE hm

end ChildResearch.BoundaryExpansion
