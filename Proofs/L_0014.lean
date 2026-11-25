import Specs.L_0014

namespace Proofs.L_0014
open MSpace Set Topology

theorem main : Specs.L_0014.stmt := by
  unfold Specs.L_0014.stmt
  intro X _ hT1 ⟨G, hOpen, hSub, hInter, hMono⟩
  refine ⟨fun n x => ⋂ k ∈ Finset.range (n + 1), G k {x}, ?_, ?_, ?_⟩
  · intro n x
    refine ⟨isOpen_biInter_finset fun k _ => hOpen k {x} isClosed_singleton, ?_⟩
    simp only [mem_iInter]
    intro k _
    exact hSub k {x} isClosed_singleton rfl
  · intro n x
    simp only [subset_def, mem_iInter, Finset.mem_range]
    intro z hz k hk
    exact hz k (by omega)
  · intro H hH x hx
    have hx' : x ∉ ⋂ n, closure (G n H) := by rw [hInter H hH]; exact hx
    simp only [mem_iInter, not_forall] at hx'
    obtain ⟨n, hn⟩ := hx'
    refine ⟨n, fun h => hn (closure_mono ?_ h)⟩
    intro z hz
    simp only [mem_iUnion, mem_iInter, Finset.mem_range] at hz
    obtain ⟨y, hy, hz⟩ := hz
    exact hMono n {y} H isClosed_singleton hH (singleton_subset_iff.mpr hy) (hz n (by omega))

end Proofs.L_0014
