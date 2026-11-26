import Specs.L_0021
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Bases

namespace Proofs.L_0021

open Set TopologicalSpace Topology

theorem main : Specs.L_0021.stmt := by
  unfold Specs.L_0021.stmt
  intro X _ hM x
  obtain ⟨hT3, 𝓑, hB, 𝓑', hCP, rfl⟩ := hM
  have := hT3
  set A : ℕ → Set X := fun k => ⋃₀ (closure '' {B | B ∈ 𝓑' k ∧ x ∉ closure B}) with hA
  have hAc : ∀ k, IsClosed (A k) := by
    intro k
    show IsClosed (⋃₀ (closure '' {B | B ∈ 𝓑' k ∧ x ∉ closure B}))
    rw [← hCP k {B | B ∈ 𝓑' k ∧ x ∉ closure B} (fun B hB => hB.1)]
    exact isClosed_closure
  have hxA : ∀ k, x ∉ A k := by
    intro k h
    obtain ⟨C, ⟨B, hB, rfl⟩, hxC⟩ := h
    exact hB.2 hxC
  set W : ℕ → Set X := fun n => ⋂ k ∈ Iic n, (A k)ᶜ with hW
  have hWo : ∀ n, IsOpen (W n) := fun n =>
    (finite_Iic n).isOpen_biInter (fun k _ => (hAc k).isOpen_compl)
  have hxW : ∀ n, x ∈ W n := fun n => mem_iInter₂.2 (fun k _ => hxA k)
  have hWA : ∀ k n, k ≤ n → ∀ B ∈ 𝓑' k, x ∉ closure B → Disjoint (closure B) (W n) := by
    intro k n hkn B hB hxB
    rw [Set.disjoint_left]
    intro y hy hyW
    exact (mem_iInter₂.1 hyW k hkn) ⟨closure B, ⟨B, ⟨hB, hxB⟩, rfl⟩, hy⟩
  have hBo : ∀ n, ∀ B ∈ 𝓑' n, IsOpen B := fun n B hBn =>
    hB.isOpen (mem_iUnion.2 ⟨n, hBn⟩)
  refine ⟨{K | ∃ n, ∃ B ∈ 𝓑' n, x ∈ B ∧ K = closure B ∩ closure (W n)}, ?_, ?_, ?_⟩
  · rintro K ⟨n, B, hBn, hxB, rfl⟩
    refine ⟨isClosed_closure.inter isClosed_closure, ?_⟩
    exact interior_maximal (inter_subset_inter subset_closure subset_closure)
      ((hBo n B hBn).inter (hWo n)) ⟨hxB, hxW n⟩
  · intro U hU hxU
    obtain ⟨N, ⟨hN, hNc⟩, hNU⟩ := (closed_nhds_basis x).mem_iff.1 (hU.mem_nhds hxU)
    obtain ⟨B, hBm, hxB, hBN⟩ := hB.mem_nhds_iff.1 hN
    obtain ⟨n, hBn⟩ := mem_iUnion.1 hBm
    refine ⟨closure B ∩ closure (W n), ⟨n, B, hBn, hxB, rfl⟩, ?_⟩
    exact (inter_subset_left).trans ((closure_minimal hBN hNc).trans hNU)
  · intro 𝓖 h𝓖
    suffices H : closure (⋃₀ 𝓖) ⊆ ⋃₀ 𝓖 by
      apply Subset.antisymm
      · intro z hz
        obtain ⟨K, hK, hzK⟩ := H hz
        exact ⟨closure K, mem_image_of_mem _ hK, subset_closure hzK⟩
      · exact sUnion_subset (by
          rintro _ ⟨K, hK, rfl⟩
          exact closure_mono (subset_sUnion_of_mem hK))
    intro z hz
    by_cases hzx : z = x
    · subst hzx
      rcases 𝓖.eq_empty_or_nonempty with h | ⟨K, hK⟩
      · simp [h] at hz
      · obtain ⟨n, B, hBn, hxB, rfl⟩ := h𝓖 hK
        exact ⟨_, hK, subset_closure hxB, subset_closure (hxW n)⟩
    · obtain ⟨N, ⟨hN, hNc⟩, hNU⟩ :=
        (closed_nhds_basis z).mem_iff.1 (isOpen_compl_singleton.mem_nhds hzx)
      obtain ⟨B', hB'm, hzB', hB'N⟩ := hB.mem_nhds_iff.1 hN
      obtain ⟨m, hB'n⟩ := mem_iUnion.1 hB'm
      have hxB' : x ∉ closure B' := fun h => hNU (closure_minimal hB'N hNc h) rfl
      have hB'o : IsOpen B' := hBo m B' hB'n
      have hdis : ∀ n, m ≤ n → Disjoint B' (closure (W n)) := fun n hmn =>
        ((hWA m n hmn B' hB'n hxB').mono_left subset_closure).closure_right hB'o
      set G : ℕ → Set (Set X) := fun n =>
        {B | B ∈ 𝓑' n ∧ x ∈ B ∧ closure B ∩ closure (W n) ∈ 𝓖} with hG
      set T : ℕ → Set X := fun n => closure (⋃₀ G n) ∩ closure (W n) with hT
      have hTc : ∀ n, IsClosed (T n) := fun n => isClosed_closure.inter isClosed_closure
      have hTG : ∀ n, T n ⊆ ⋃₀ 𝓖 := by
        intro n y hy
        have hy1 : y ∈ closure (⋃₀ G n) := hy.1
        rw [hCP n (G n) (fun B hB => hB.1)] at hy1
        obtain ⟨C, ⟨B, hBG, rfl⟩, hyC⟩ := hy1
        exact ⟨_, hBG.2.2, hyC, hy.2⟩
      have hsub : B' ∩ ⋃₀ 𝓖 ⊆ ⋃ n ∈ Iio m, T n := by
        rintro y ⟨hyB', K, hK, hyK⟩
        have hK' := h𝓖 hK
        obtain ⟨n, B, hBn, hxB, rfl⟩ := hK'
        have hnm : n < m := by
          by_contra hnm
          exact Set.disjoint_left.1 (hdis n (not_lt.1 hnm)) hyB' hyK.2
        refine mem_iUnion₂.2 ⟨n, hnm, ?_, hyK.2⟩
        exact closure_mono (subset_sUnion_of_mem (show B ∈ G n from ⟨hBn, hxB, hK⟩)) hyK.1
      have hcl : IsClosed (⋃ n ∈ Iio m, T n) :=
        (finite_Iio m).isClosed_biUnion (fun n _ => hTc n)
      have hz' := closure_minimal hsub hcl (hB'o.inter_closure ⟨hzB', hz⟩)
      obtain ⟨n, _, hzT⟩ := mem_iUnion₂.1 hz'
      exact hTG n hzT

end Proofs.L_0021
