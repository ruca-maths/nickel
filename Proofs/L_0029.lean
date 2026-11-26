import Specs.L_0029

namespace Proofs.L_0029

open Set TopologicalSpace

theorem main : Specs.L_0029.stmt := by
  unfold Specs.L_0029.stmt
  intro X _ hM x
  obtain ⟨_, 𝓑, hB, 𝓑', hCP, hEq⟩ := hM
  refine ⟨fun n => {B ∈ 𝓑' n | x ∈ B}, ?_, ?_, ?_⟩
  · intro n V hV
    refine ⟨hB.isOpen ?_, hV.2⟩
    rw [hEq]
    exact mem_iUnion.2 ⟨n, hV.1⟩
  · intro n 𝓖 h𝓖
    exact hCP n 𝓖 (fun B hB' => (h𝓖 hB').1)
  · intro U hU hxU
    obtain ⟨v, hv, hxv, hvU⟩ := hB.exists_subset_of_mem_open hxU hU
    rw [hEq] at hv
    obtain ⟨n, hn⟩ := mem_iUnion.1 hv
    exact ⟨n, v, ⟨hn, hxv⟩, hvU⟩

end Proofs.L_0029
