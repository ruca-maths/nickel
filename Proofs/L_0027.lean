import Specs.L_0027

namespace Proofs.L_0027

open Set

theorem main : Specs.L_0027.stmt := by
  unfold Specs.L_0027.stmt
  intro X _ x 𝓚 h𝓚 hbase hcp
  refine ⟨interior '' 𝓚, ?_, ?_, ?_⟩
  · rintro V ⟨K, hK, rfl⟩
    exact ⟨isOpen_interior, (h𝓚 K hK).2.2⟩
  · intro U hU hxU
    obtain ⟨K, hK, hKU⟩ := hbase U hU hxU
    exact ⟨interior K, ⟨K, hK, rfl⟩, interior_subset.trans hKU⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · let 𝓗 : Set (Set X) := {K | K ∈ 𝓚 ∧ interior K ∈ 𝓖}
      have h1 : ⋃₀ 𝓖 ⊆ ⋃₀ 𝓗 := by
        rintro y ⟨V, hV, hyV⟩
        obtain ⟨K, hK, rfl⟩ := h𝓖 hV
        exact ⟨K, ⟨hK, hV⟩, interior_subset hyV⟩
      have h2 : closure (⋃₀ 𝓗) = ⋃₀ (closure '' 𝓗) := hcp 𝓗 (fun K hK => hK.1)
      calc closure (⋃₀ 𝓖) ⊆ closure (⋃₀ 𝓗) := closure_mono h1
        _ = ⋃₀ (closure '' 𝓗) := h2
        _ ⊆ ⋃₀ (closure '' 𝓖) := by
          rintro y ⟨C, ⟨K, hK, rfl⟩, hyC⟩
          refine ⟨closure (interior K), ⟨interior K, hK.2, rfl⟩, ?_⟩
          rw [(h𝓚 K hK.1).2.1]
          rwa [(h𝓚 K hK.1).1.closure_eq] at hyC
    · rintro y ⟨C, ⟨V, hV, rfl⟩, hyC⟩
      exact closure_mono (subset_sUnion_of_mem hV) hyC

end Proofs.L_0027
