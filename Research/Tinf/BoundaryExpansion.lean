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

/-- Glue CP on the complement to control on a closed wall. The absorption
hypothesis measures an arbitrary subfamily against its own closed anchors. -/
theorem cp_of_complement_and_anchor {X I : Type} [TopologicalSpace X]
    (M : Set X) (K W : I → Set X)
    (hsub : ∀ i, K i ⊆ W i)
    (hwall : ∀ A : Set I,
      closure (⋃ i ∈ A, W i) ∩ M ⊆ ⋃ i ∈ A, K i)
    (hout : ∀ A : Set I, closure (⋃ i ∈ A, W i) \ M ⊆
      ⋃ i ∈ A, closure (W i)) :
    ClosurePreserving (range W) := by
  intro H hH
  let A : Set I := {i | W i ∈ H}
  have heq : ⋃₀ H = ⋃ i ∈ A, W i := by
    ext y
    constructor
    · rintro ⟨C, hC, hy⟩
      obtain ⟨i, rfl⟩ := hH hC
      exact mem_iUnion₂.mpr ⟨i, hC, hy⟩
    · intro hy
      obtain ⟨i, hi, hy⟩ := mem_iUnion₂.mp hy
      exact ⟨W i, hi, hy⟩
  apply Subset.antisymm
  · intro y hy
    rw [heq] at hy
    by_cases hyM : y ∈ M
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hwall A ⟨hy, hyM⟩)
      exact ⟨closure (W i), mem_image_of_mem _ hi, subset_closure (hsub i hyi)⟩
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hout A ⟨hy, hyM⟩)
      exact ⟨closure (W i), mem_image_of_mem _ hi, hyi⟩
  · rintro y ⟨_, ⟨C, hC, rfl⟩, hy⟩
    exact closure_mono (subset_sUnion_of_mem hC) hy

end ChildResearch.BoundaryExpansion
