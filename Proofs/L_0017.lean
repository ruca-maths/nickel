import Specs.L_0017

namespace Proofs.L_0017
open MSpace Set Topology

theorem main : Specs.L_0017.stmt := by
  unfold Specs.L_0017.stmt
  intro X _ ⟨g, hOpen, _, hClos⟩
  refine ⟨fun n H => ⋃ y ∈ H, g n y, ?_, ?_, ?_, ?_⟩
  · intro n H _
    exact isOpen_biUnion fun y _ => (hOpen n y).1
  · intro n H _ x hx
    exact mem_biUnion hx (hOpen n x).2
  · intro H hH
    refine Subset.antisymm ?_ ?_
    · intro x hx
      by_contra hxH
      obtain ⟨n, hn⟩ := hClos H hH x hxH
      exact hn (mem_iInter.mp hx n)
    · exact subset_iInter fun n x hx => subset_closure (mem_biUnion hx (hOpen n x).2)
  · intro n H K _ _ hHK
    exact biUnion_subset_biUnion_left hHK

end Proofs.L_0017
