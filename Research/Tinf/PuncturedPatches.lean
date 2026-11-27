import Targets

namespace ChildResearch.PuncturedPatches

open Set MSpace Topology

theorem exists_patches {X I : Type} [TopologicalSpace X] [T1Space X]
    (p : X) (a : I → X) (O : I → Set X) (B : I → Set (Set X))
    (ha : p ∈ closure (range a))
    (hN : ∀ y ≠ p, ∃ U : Set X, IsOpen U ∧ y ∈ U ∧
      {i | (U ∩ O i).Nonempty}.Finite)
    (hB : ∀ i, ∀ C ∈ B i, IsClosed C ∧ a i ∈ interior C ∧ C ⊆ O i)
    (hbase : ∀ i U, IsOpen U → a i ∈ U → ∃ C ∈ B i, C ⊆ U)
    (hcp : ∀ i, ClosurePreserving (B i)) :
    ∃ F : Set (Set X), ClosurePreserving F ∧
      (∀ C ∈ F, IsClosed C ∧ p ∈ closure (interior C)) ∧
      (∀ U : Set X, IsOpen U → p ∈ U → ∃ C ∈ F, C ⊆ U) := by
  classical
  let P := {s : I → Set X // (∀ i, s i = ∅ ∨ s i ∈ B i) ∧
    p ∈ closure (⋃ i, interior (s i))}
  let K := fun s : P => {p} ∪ ⋃ i, s.val i
  have closed_union : ∀ H : Set P, IsClosed (⋃ s ∈ H, K s) := by
    intro H
    rw [← closure_eq_iff_isClosed]
    apply Subset.antisymm _ subset_closure
    intro y hy
    by_cases hyP : y = p
    · obtain ⟨z, hz⟩ := Set.Nonempty.of_closure ⟨y, hy⟩
      obtain ⟨s, hs, _⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨s, hs, Or.inl (mem_singleton_iff.mpr hyP)⟩
    obtain ⟨U, hUo, hyU, hUfin⟩ := hN y hyP
    let V := U ∩ ({p} : Set X)ᶜ
    have hV : IsOpen V := hUo.inter isClosed_singleton.isOpen_compl
    let T := fun i => {C ∈ B i | ∃ s ∈ H, s.val i = C}
    have ht : ∀ i, IsClosed (⋃₀ T i) := by
      intro i
      rw [← closure_eq_iff_isClosed, hcp i (T i) (fun _ h => h.1)]
      congr 1
      ext C
      constructor
      · rintro ⟨D, hD, rfl⟩
        simpa only [(hB i D hD.1).1.closure_eq] using hD
      · intro hD
        exact ⟨C, hD, (hB i C hD.1).1.closure_eq⟩
    let E := ⋃ i ∈ {i | (U ∩ O i).Nonempty}, ⋃₀ T i
    have he : IsClosed E := hUfin.isClosed_biUnion fun i _ => ht i
    have hsub : V ∩ (⋃ s ∈ H, K s) ⊆ E := by
      rintro z ⟨hzV, hz⟩
      obtain ⟨s, hs, hz⟩ := mem_iUnion₂.mp hz
      rcases hz with hzp | hz
      · exact (hzV.2 hzp).elim
      obtain ⟨i, hz⟩ := mem_iUnion.mp hz
      have hsi : s.val i ∈ B i := (s.property.1 i).resolve_left
        (fun h => by rw [h] at hz; exact hz.elim)
      exact mem_iUnion₂.mpr ⟨i, ⟨z, hzV.1, (hB i _ hsi).2.2 hz⟩,
        mem_sUnion.mpr ⟨s.val i, ⟨hsi, s, hs, rfl⟩, hz⟩⟩
    have hyE := closure_minimal hsub he (hV.inter_closure ⟨⟨hyU, hyP⟩, hy⟩)
    obtain ⟨i, _, C, ⟨_, s, hs, hsi⟩, hyC⟩ := mem_iUnion₂.mp hyE
    exact mem_iUnion₂.mpr ⟨s, hs, Or.inr (mem_iUnion.mpr ⟨i, hsi.symm ▸ hyC⟩)⟩
  have hK_closed : ∀ s, IsClosed (K s) := by
    intro s
    simpa using closed_union {s}
  refine ⟨range K, ?_, ?_, ?_⟩
  · intro H hH
    let H' : Set P := {s | K s ∈ H}
    have heq : (⋃₀ H) = ⋃ s ∈ H', K s := by
      ext y
      constructor
      · rintro ⟨C, hC, hy⟩
        obtain ⟨s, rfl⟩ := hH hC
        exact mem_iUnion₂.mpr ⟨s, hC, hy⟩
      · intro hy
        obtain ⟨s, hs, hy⟩ := mem_iUnion₂.mp hy
        exact ⟨K s, hs, hy⟩
    rw [heq, (closed_union H').closure_eq, ← heq]
    ext y
    constructor
    · rintro ⟨C, hC, hy⟩
      obtain ⟨s, rfl⟩ := hH hC
      exact ⟨closure (K s), mem_image_of_mem _ hC, subset_closure hy⟩
    · rintro ⟨_, ⟨C, hC, rfl⟩, hy⟩
      obtain ⟨s, rfl⟩ := hH hC
      exact ⟨K s, hC, (hK_closed s).closure_eq ▸ hy⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨hK_closed s, closure_mono (iUnion_subset fun i =>
      interior_mono (fun z hz => Or.inr (mem_iUnion.mpr ⟨i, hz⟩))) s.property.2⟩
  · intro U hU hpU
    let s : I → Set X := fun i =>
      if h : a i ∈ U then (hbase i U hU h).choose else ∅
    have hs : ∀ i (h : a i ∈ U), s i ∈ B i ∧ s i ⊆ U := by
      intro i h
      simpa only [s, dite_eq_left h] using (hbase i U hU h).choose_spec
    have hsp : p ∈ closure (⋃ i, interior (s i)) := by
      apply mem_closure_iff.mpr
      intro V hV hpV
      obtain ⟨_, ⟨haV, haU⟩, i, rfl⟩ :=
        mem_closure_iff.mp ha (V ∩ U) (hV.inter hU) ⟨hpV, hpU⟩
      exact ⟨a i, haV, mem_iUnion.mpr ⟨i, (hB i _ (hs i haU).1).2.1⟩⟩
    let t : P := ⟨s, fun i => by
      by_cases h : a i ∈ U
      · exact Or.inr (hs i h).1
      · exact Or.inl (dite_eq_right h), hsp⟩
    refine ⟨K t, mem_range_self t, ?_⟩
    rintro z (hz | hz)
    · exact (mem_singleton_iff.mp hz).symm ▸ hpU
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
    by_cases h : a i ∈ U
    · exact (hs i h).2 hzi
    · exact (show z ∈ (∅ : Set X) by simpa only [t, s, dite_eq_right h] using hzi).elim

end ChildResearch.PuncturedPatches
