import Mathlib.Topology.Closure
import Specs.L_0016

namespace Proofs.L_0016

open MSpace Set Topology

theorem main : Specs.L_0016.stmt := by
  unfold Specs.L_0016.stmt
  intro X _ ⟨V, hV, hT, hS⟩
  have inv : ∀ n (A : Set X) z, z ∈ (⋃ y ∈ A, V n y) → V n z ⊆ ⋃ y ∈ A, V n y := by
    intro n A z hz
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp hz
    exact (hT n y z hzy).trans (subset_biUnion_of_mem hy)
  have Wopen : ∀ n (A : Set X), IsOpen (⋃ y ∈ A, V n y) := by
    intro n A
    exact isOpen_iff_mem_nhds.mpr fun z hz => Filter.mem_of_superset (hV n z) (inv n A z hz)
  let B' : ℕ → Set (Set X) := fun n => range (fun A : Set X => (⋃ y ∈ A, V n y)ᶜ)
  refine ⟨⋃ n, B' n, ?_, ⟨B', ?_, rfl⟩⟩
  · intro x U hU hxU
    obtain ⟨n, hn⟩ := hS Uᶜ hU.isClosed_compl x (by simpa using hxU)
    refine ⟨(⋃ y ∈ Uᶜ, V n y)ᶜ, mem_iUnion.mpr ⟨n, ⟨Uᶜ, rfl⟩⟩, ?_, ?_⟩
    · rw [interior_compl]; exact hn
    · intro z hz
      by_contra hzU
      exact hz (mem_iUnion₂.mpr ⟨z, hzU, mem_of_mem_nhds (hV n z)⟩)
  · intro n 𝓖 h𝓖
    have hcl : ∀ B ∈ 𝓖, IsClosed B := by
      intro B hB
      obtain ⟨A, rfl⟩ := h𝓖 hB
      exact (Wopen n A).isClosed_compl
    have hU : IsClosed (⋃₀ 𝓖) := by
      rw [← isOpen_compl_iff]
      refine isOpen_iff_mem_nhds.mpr fun z hz => Filter.mem_of_superset (hV n z) ?_
      intro w hw hw'
      obtain ⟨B, hB, hwB⟩ := hw'
      apply hz
      refine ⟨B, hB, ?_⟩
      obtain ⟨A, rfl⟩ := h𝓖 hB
      intro hzB
      have hzW : z ∈ ⋃ y ∈ A, V n y := by simpa using hzB
      exact hwB (inv n A z hzW hw)
    have him : closure '' 𝓖 = 𝓖 := by
      ext C
      constructor
      · rintro ⟨B, hB, rfl⟩; rw [(hcl B hB).closure_eq]; exact hB
      · intro hC; exact ⟨C, hC, (hcl C hC).closure_eq⟩
    rw [him, hU.closure_eq]

end Proofs.L_0016
