import Mathlib.Topology.LocallyFinite
import Specs.L_0001

namespace Proofs.L_0001

open Set

theorem main : Specs.L_0001.stmt := by
  unfold Specs.L_0001.stmt MSpace.Goals.T1a_closurePreserving_of_locallyFinite
  intro X _ F hF G hG
  have hG' : LocallyFinite (fun s : G => (s : Set X)) :=
    hF.comp_injective (g := fun s : G => (⟨s.1, hG s.2⟩ : F))
      (fun a b hab => Subtype.ext (congrArg Subtype.val hab :))
  rw [sUnion_eq_iUnion, hG'.closure_iUnion, sUnion_image]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨⟨s, hs⟩, hx⟩
    exact ⟨s, hs, hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨⟨s, hs⟩, hx⟩

end Proofs.L_0001
