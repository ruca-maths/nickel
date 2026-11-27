import Targets

namespace ChildResearch.MosaicTrace

open Set Topology

/-- Sample good representatives only where regularization needs them. -/
theorem exists_good_defect_trace {X : Type} [TopologicalSpace X] [T1Space X]
    {I J : Type} (C : ℕ → I → Set X) (N : ℕ → J → Set X)
    (F : Set (Set X)) (Good : X → Prop)
    (havailable : ∀ K ∈ F, ∀ x ∈ K, x ∉ closure (interior K) →
      ∀ U : Set X, IsOpen U → x ∈ U →
        ∃ n m i j, C n i ⊆ K ∧ N m j ⊆ U ∧
          ∃ z ∈ C n i ∩ N m j, Good z)
    (hC : ∀ n x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ i i', (U ∩ C n i).Nonempty → (U ∩ C n i').Nonempty → i = i')
    (hN : ∀ m x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ j j', (U ∩ N m j).Nonempty → (U ∩ N m j').Nonempty → j = j') :
    ∃ E : ℕ → ℕ → Set X,
      (∀ n m, ∀ A ⊆ E n m, IsClosed A) ∧
      (∀ n m z, z ∈ E n m → Good z) ∧
      ∀ K ∈ F, K ⊆ closure (interior K ∪ (K ∩ ⋃ n, ⋃ m, E n m)) := by
  classical
  let P := fun n m => {ij : I × J // ∃ z ∈ C n ij.1 ∩ N m ij.2, Good z}
  let p := fun n m (a : P n m) => a.property.choose
  have hp : ∀ n m (a : P n m), p n m a ∈ C n a.val.1 ∩ N m a.val.2 :=
    fun _ _ a => a.property.choose_spec.1
  refine ⟨fun n m => range (p n m), ?_, ?_, ?_⟩
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
  · rintro n m _ ⟨a, rfl⟩
    exact a.property.choose_spec.2
  · intro K hK x hx
    by_cases hxint : x ∈ closure (interior K)
    · exact closure_mono subset_union_left hxint
    apply mem_closure_iff_nhds.mpr
    intro U hU
    obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
    obtain ⟨n, m, i, j, hiK, hjV, hgood⟩ := havailable K hK x hx hxint V hVo hxV
    let a : P n m := ⟨(i, j), hgood⟩
    exact ⟨p n m a, hVU (hjV (hp n m a).2),
      Or.inr ⟨hiK (hp n m a).1,
        mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨m, mem_range_self a⟩⟩⟩⟩

end ChildResearch.MosaicTrace
