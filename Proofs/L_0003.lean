import Mathlib.Topology.Separation.Regular
import Specs.L_0003

namespace Proofs.L_0003

open Set MSpace Topology

theorem cushioned_image {X : Type} [TopologicalSpace X] (𝓑 : Set (Set X))
    (h : ClosurePreserving 𝓑) :
    Cushioned ((fun B => (interior B, closure B)) '' 𝓑) := by
  intro 𝓠 h𝓠
  let 𝓖 : Set (Set X) := {B | B ∈ 𝓑 ∧ (interior B, closure B) ∈ 𝓠}
  have hG : 𝓖 ⊆ 𝓑 := fun B hB => hB.1
  have h1 : (⋃ p ∈ 𝓠, p.1) ⊆ ⋃₀ 𝓖 := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    obtain ⟨B, hB, rfl⟩ := h𝓠 hp
    exact ⟨B, ⟨hB, hp⟩, interior_subset hxp⟩
  have h2 : ⋃₀ (closure '' 𝓖) ⊆ ⋃ p ∈ 𝓠, p.2 := by
    rintro x ⟨C, ⟨B, ⟨_, hBQ⟩, rfl⟩, hxC⟩
    simp only [mem_iUnion]
    exact ⟨_, hBQ, hxC⟩
  calc closure (⋃ p ∈ 𝓠, p.1) ⊆ closure (⋃₀ 𝓖) := closure_mono h1
    _ = ⋃₀ (closure '' 𝓖) := h 𝓖 hG
    _ ⊆ _ := h2

theorem main : Specs.L_0003.stmt := by
  unfold Specs.L_0003.stmt MSpace.Goals.T1c_M2_imp_M3
  intro X _ hX
  obtain ⟨hT3, 𝓑, hQB, 𝓑', hcp, rfl⟩ := hX
  refine ⟨hT3, ⋃ n, (fun B => (interior B, closure B)) '' 𝓑' n, ⟨?_, ?_⟩,
    ⟨fun n => (fun B => (interior B, closure B)) '' 𝓑' n,
      fun n => cushioned_image _ (hcp n), rfl⟩⟩
  · intro p hp
    simp only [mem_iUnion, mem_image] at hp
    obtain ⟨n, B, _, rfl⟩ := hp
    exact ⟨isOpen_interior, interior_subset.trans subset_closure⟩
  · intro x U hU hxU
    obtain ⟨t, ht, htc, htU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hxU)
    obtain ⟨B, hB, hxB, hBt⟩ :=
      hQB x (interior t) isOpen_interior (mem_interior_iff_mem_nhds.mpr ht)
    obtain ⟨n, hn⟩ := mem_iUnion.mp hB
    refine ⟨(interior B, closure B), mem_iUnion.mpr ⟨n, mem_image_of_mem _ hn⟩, hxB, ?_⟩
    exact (closure_minimal (hBt.trans interior_subset) htc).trans htU

end Proofs.L_0003
