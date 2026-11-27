import Targets

namespace ChildResearch.MosaicTrace

open Set Topology

/-- Sample a common trace using indexed discrete layers of a mosaic
and a network. Mosaic cells are compatible with the entire family. -/
theorem exists_common_trace {X : Type} [TopologicalSpace X] [T1Space X]
    {I J : Type} (C : ℕ → I → Set X) (N : ℕ → J → Set X)
    (F : Set (Set X)) (hclosed : ∀ K ∈ F, IsClosed K)
    (hcover : ∀ x : X, ∃ n i, x ∈ C n i)
    (hcompatible : ∀ K ∈ F, ∀ n i, (C n i ∩ K).Nonempty → C n i ⊆ K)
    (hnetwork : ∀ (U : Set X), IsOpen U → ∀ x ∈ U, ∃ m j, x ∈ N m j ∧ N m j ⊆ U)
    (hC : ∀ n x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ i i', (U ∩ C n i).Nonempty → (U ∩ C n i').Nonempty → i = i')
    (hN : ∀ m x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ j j', (U ∩ N m j).Nonempty → (U ∩ N m j').Nonempty → j = j') :
    ∃ E : ℕ → ℕ → Set X,
      (∀ n m, ∀ A ⊆ E n m, IsClosed A) ∧
      ∀ K ∈ F, closure (K ∩ ⋃ n, ⋃ m, E n m) = K := by
  classical
  let P := fun n m => {ij : I × J // (C n ij.1 ∩ N m ij.2).Nonempty}
  let p := fun n m (a : P n m) => a.property.choose
  have hp : ∀ n m (a : P n m), p n m a ∈ C n a.val.1 ∩ N m a.val.2 :=
    fun _ _ a => a.property.choose_spec
  refine ⟨fun n m => range (p n m), ?_, ?_⟩
  · intro n m A hA
    rw [← closure_eq_iff_isClosed]
    apply Subset.antisymm _ subset_closure
    intro x hx
    obtain ⟨U, hUo, hxU, hUi⟩ := hC n x
    obtain ⟨V, hVo, hxV, hVj⟩ := hN m x
    obtain ⟨y, ⟨hyU, hyV⟩, hyA⟩ :=
      mem_closure_iff_nhds.mp hx (U ∩ V) ((hUo.inter hVo).mem_nhds ⟨hxU, hxV⟩)
    obtain ⟨a, rfl⟩ := hA hyA
    by_contra hxA
    let W := (U ∩ V) ∩ ({p n m a} : Set X)ᶜ
    have hWo : IsOpen W := (hUo.inter hVo).inter isClosed_singleton.isOpen_compl
    have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, fun he => hxA ((mem_singleton_iff.mp he).symm ▸ hyA)⟩
    obtain ⟨z, ⟨⟨hzU, hzV⟩, hz_ne⟩, hzA⟩ :=
      mem_closure_iff_nhds.mp hx W (hWo.mem_nhds hxW)
    obtain ⟨b, rfl⟩ := hA hzA
    have hi := hUi b.val.1 a.val.1 ⟨_, hzU, (hp n m b).1⟩ ⟨_, hyU, (hp n m a).1⟩
    have hj := hVj b.val.2 a.val.2 ⟨_, hzV, (hp n m b).2⟩ ⟨_, hyV, (hp n m a).2⟩
    have hba : b = a := Subtype.ext (Prod.ext hi hj)
    exact hz_ne (mem_singleton_iff.mpr (congrArg (p n m) hba))
  · intro K hK
    apply Subset.antisymm (closure_minimal inter_subset_left (hclosed K hK))
    intro x hx
    apply mem_closure_iff_nhds.mpr
    intro U hU
    obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
    obtain ⟨n, i, hxi⟩ := hcover x
    obtain ⟨m, j, hxj, hjV⟩ := hnetwork V hVo x hxV
    let a : P n m := ⟨(i, j), ⟨x, hxi, hxj⟩⟩
    exact ⟨p n m a, hVU (hjV (hp n m a).2),
      hcompatible K hK n i ⟨x, hxi, hx⟩ (hp n m a).1,
      mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨m, mem_range_self a⟩⟩⟩

end ChildResearch.MosaicTrace
