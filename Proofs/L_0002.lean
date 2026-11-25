import Mathlib.Topology.Bases
import Specs.L_0002

namespace Proofs.L_0002

theorem main : Specs.L_0002.stmt := by
  unfold Specs.L_0002.stmt MSpace.Goals.T1b_M1_imp_M2
  intro X _ h
  obtain ⟨hT, B, hB, hS⟩ := h
  refine ⟨hT, B, ?_, hS⟩
  intro x U hU hx
  obtain ⟨V, hVB, hxV, hVU⟩ := hB.exists_subset_of_mem_open hx hU
  exact ⟨V, hVB, by rwa [(hB.isOpen hVB).interior_eq], hVU⟩

end Proofs.L_0002
