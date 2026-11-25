import Mathlib.Topology.Separation.Regular
import Specs.L_0018

namespace Proofs.L_0018

open MSpace Set Topology

theorem main : Specs.L_0018.stmt := by
  unfold Specs.L_0018.stmt
  intro X _ hT3 ⟨𝓑, hQB, 𝓑', hCP, h𝓑⟩
  have : T3Space X := hT3
  let G : ℕ → X → Set (Set X) := fun n x => {B ∈ 𝓑' n | x ∉ closure B}
  let V : ℕ → X → Set X := fun n x => (closure (⋃₀ G n x))ᶜ
  have hG_sub : ∀ n x, G n x ⊆ 𝓑' n := fun _ _ _ hB => hB.1
  have hV_mem : ∀ n x z, z ∈ V n x ↔ ∀ B ∈ 𝓑' n, x ∉ closure B → z ∉ closure B := by
    intro n x z
    change z ∉ closure (⋃₀ G n x) ↔ _
    rw [hCP n (G n x) (hG_sub n x)]
    constructor
    · intro hz B hB hxB hzB
      exact hz ⟨closure B, ⟨B, ⟨hB, hxB⟩, rfl⟩, hzB⟩
    · rintro h ⟨_, ⟨B, ⟨hB, hxB⟩, rfl⟩, hzB⟩
      exact h B hB hxB hzB
  refine ⟨V, ?_, ?_, ?_⟩
  · intro n x
    refine isClosed_closure.isOpen_compl.mem_nhds ?_
    exact (hV_mem n x x).mpr fun _ _ hxB => hxB
  · intro n x y hyx z hzy
    refine (hV_mem n x z).mpr fun B hB hxB => ?_
    exact (hV_mem n y z).mp hzy B hB ((hV_mem n x y).mp hyx B hB hxB)
  · intro H hH x hxH
    obtain ⟨t, ht_nhds, ht_closed, ht_sub⟩ :=
      exists_mem_nhds_isClosed_subset (hH.isOpen_compl.mem_nhds hxH)
    obtain ⟨B, hB𝓑, hx_intB, hB_sub⟩ :=
      hQB x (interior t) isOpen_interior (mem_interior_iff_mem_nhds.mpr ht_nhds)
    rw [h𝓑] at hB𝓑
    obtain ⟨n, hBn⟩ := mem_iUnion.mp hB𝓑
    have hclB_Hc : closure B ⊆ Hᶜ :=
      (closure_minimal (hB_sub.trans interior_subset) ht_closed).trans ht_sub
    have hU_sub : (⋃ y ∈ H, V n y) ⊆ (interior B)ᶜ := by
      intro z hz
      obtain ⟨y, hyH, hzy⟩ := mem_iUnion₂.mp hz
      have hy_not : y ∉ closure B := fun hycl => hclB_Hc hycl hyH
      have hz_not : z ∉ closure B := (hV_mem n y z).mp hzy B hBn hy_not
      exact fun hz_int => hz_not (subset_closure (interior_subset hz_int))
    refine ⟨n, fun hx_cl => ?_⟩
    exact closure_minimal hU_sub isOpen_interior.isClosed_compl hx_cl hx_intB

end Proofs.L_0018
