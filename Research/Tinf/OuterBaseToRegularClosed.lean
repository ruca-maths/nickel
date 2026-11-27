import Specs.L_0028
import Defs.D_0001

namespace ChildResearch.OuterBaseToRegularClosed

open Set MSpace Topology

theorem cp_closure_image {X : Type} [TopologicalSpace X]
    {F : Set (Set X)} (hF : ClosurePreserving F) :
    ClosurePreserving ((fun U : Set X => closure U) '' F) := by
  classical
  intro G hG
  let A : Set (Set X) := {U ∈ F | closure U ∈ G}
  have hA : A ⊆ F := fun _ h => h.1
  have hGrep : G = (fun U : Set X => closure U) '' A := by
    ext C
    constructor
    · intro hC
      obtain ⟨U, hU, rfl⟩ := hG hC
      exact ⟨U, ⟨hU, hC⟩, rfl⟩
    · rintro ⟨U, hU, rfl⟩
      change U ∈ F ∧ closure U ∈ G at hU
      exact hU.2
  have hClosureUnion : closure (⋃₀ G) = closure (⋃₀ A) := by
    apply Subset.antisymm
    · apply closure_minimal ?_ isClosed_closure
      rintro y ⟨C, hC, hy⟩
      obtain ⟨U, hU, rfl⟩ := hG hC
      have hUA : U ∈ A := by
        change U ∈ F ∧ closure U ∈ G
        exact ⟨hU, hC⟩
      exact closure_mono (subset_sUnion_of_mem hUA) hy
    · apply closure_minimal ?_ isClosed_closure
      rintro y ⟨U, hU, hy⟩
      change U ∈ F ∧ closure U ∈ G at hU
      exact subset_closure (mem_sUnion.mpr ⟨closure U, hU.2, subset_closure hy⟩)
  rw [hClosureUnion, hF A hA]
  rw [hGrep]
  ext y
  constructor
  · rintro ⟨C, ⟨U, hU, rfl⟩, hy⟩
    refine mem_sUnion.mpr ⟨closure (closure U), ⟨closure U, ?_, rfl⟩, ?_⟩
    · exact ⟨U, hU, rfl⟩
    · simpa using hy
  · rintro ⟨C, ⟨U, hU, rfl⟩, hy⟩
    obtain ⟨V, hV, rfl⟩ := hU
    exact mem_sUnion.mpr ⟨closure V, ⟨V, hV, rfl⟩, by simpa using hy⟩

theorem regular_closed_cp_base_of_cp_outer_base {X : Type} [TopologicalSpace X]
    [T3Space X] (x : X) (h : Defs.D_0001.HasCPOuterBase x) :
    ∃ K : Set (Set X),
      (∀ C ∈ K, IsClosed C ∧ closure (interior C) = C ∧ x ∈ interior C) ∧
      (∀ U : Set X, IsOpen U → x ∈ U → ∃ C ∈ K, C ⊆ U) ∧
      ClosurePreserving K := by
  classical
  obtain ⟨V, hVnbd, hVbase, hVcp⟩ := h
  refine ⟨closure '' V, ?_, ?_, cp_closure_image hVcp⟩
  · rintro C ⟨W, hW, rfl⟩
    refine ⟨isClosed_closure, ?_, ?_⟩
    · apply Subset.antisymm
      · simpa using closure_mono (show interior (closure W) ⊆ closure W from interior_subset)
      · simpa using closure_mono ((hVnbd W hW).1.subset_interior_closure)
    · exact (hVnbd W hW).1.subset_interior_closure (hVnbd W hW).2
  · intro U hU hxU
    obtain ⟨C, hCx, hCclosed, hCU⟩ :=
      exists_mem_nhds_isClosed_subset (hU.mem_nhds hxU)
    have hxC : x ∈ interior C := by
      obtain ⟨O, hOC, hOopen, hxO⟩ := mem_nhds_iff.mp hCx
      exact interior_maximal hOC hOopen hxO
    obtain ⟨W, hW, hWC⟩ := hVbase (interior C) isOpen_interior hxC
    refine ⟨closure W, ⟨W, hW, rfl⟩, ?_⟩
    exact (closure_mono hWC).trans (hCclosed.closure_interior_subset.trans hCU)

/-- The singleton instance of Mizokami's closed-set theorem suffices.
The literature theorem is a hypothesis of this reduction. -/
theorem L0028_of_mizokami
    (h : ∀ (X : Type) [TopologicalSpace X], IsM1 X → ∀ F : Set X,
      IsClosed F → ∃ V : Set (Set X),
        (∀ U ∈ V, IsOpen U ∧ F ⊆ U) ∧
        (∀ U : Set X, IsOpen U → F ⊆ U → ∃ W ∈ V, W ⊆ U) ∧
        ClosurePreserving V) : Specs.L_0028.stmt := by
  unfold Specs.L_0028.stmt
  intro X _ hM _ x _
  letI : T3Space X := hM.1
  apply regular_closed_cp_base_of_cp_outer_base x
  obtain ⟨V, hn, hb, hc⟩ := h X hM {x} isClosed_singleton
  exact ⟨V, fun U hU => ⟨(hn U hU).1, singleton_subset_iff.mp (hn U hU).2⟩,
    fun U hU hxU => hb U hU (singleton_subset_iff.mpr hxU), hc⟩

end ChildResearch.OuterBaseToRegularClosed
