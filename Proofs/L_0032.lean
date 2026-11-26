import Mathlib.Topology.Closure
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Interval.Finset.Nat
import Specs.L_0032

namespace Proofs.L_0032

open Set

theorem main : Specs.L_0032.stmt := by
  unfold Specs.L_0032.stmt
  intro X _ x W hW hInt hB
  obtain ⟨𝓑, hBo, hBcp, hBbase⟩ := hB
  set W' : ℕ → Set X := fun n => ⋂ k ∈ Set.Iic n, W k with hW'def
  have hW'o : ∀ n, IsOpen (W' n) := fun n =>
    (Set.finite_Iic n).isOpen_biInter (fun k _ => (hW k).1)
  have hW'c : ∀ n, IsClosed (W' n) := fun n =>
    isClosed_biInter (fun k _ => (hW k).2.1)
  have hW'x : ∀ n, x ∈ W' n := fun n => by
    simp only [hW'def, mem_iInter]; intro k _; exact (hW k).2.2
  have hW'sub : ∀ i m, i ≤ m → W' m ⊆ W i := fun i m him =>
    biInter_subset_of_mem (show i ∈ Set.Iic m from him)
  refine ⟨{S | ∃ n, ∃ V ∈ 𝓑 n, S = V ∩ W' n}, ?_, ?_, ?_⟩
  · rintro S ⟨n, V, hV, rfl⟩
    exact ⟨(hBo n V hV).1.inter (hW'o n), (hBo n V hV).2, hW'x n⟩
  · intro U hU hxU
    obtain ⟨n, V, hV, hVU⟩ := hBbase U hU hxU
    exact ⟨V ∩ W' n, ⟨n, V, hV, rfl⟩, inter_subset_left.trans hVU⟩
  · intro 𝓖 h𝓖
    refine Subset.antisymm ?_ ?_
    swap
    · rintro y ⟨_, ⟨G, hG, rfl⟩, hy⟩
      exact closure_mono (subset_sUnion_of_mem hG) hy
    intro t ht
    by_cases htx : t = x
    · subst htx
      rcases 𝓖.eq_empty_or_nonempty with h | ⟨G, hG⟩
      · simp [h] at ht
      · obtain ⟨n, V, hV, rfl⟩ := h𝓖 hG
        exact ⟨closure (V ∩ W' n), ⟨_, hG, rfl⟩, subset_closure ⟨(hBo n V hV).2, hW'x n⟩⟩
    · have : t ∉ ⋂ n, W n := by rw [hInt]; exact htx
      simp only [mem_iInter, not_forall] at this
      obtain ⟨i₀, hti⟩ := this
      let A : ℕ → Set X := fun n => (⋃₀ {V ∈ 𝓑 n | V ∩ W' n ∈ 𝓖}) ∩ W' n
      have hsub : ⋃₀ 𝓖 ⊆ (⋃ n ∈ Set.Iio i₀, A n) ∪ W i₀ := by
        rintro y ⟨G, hG, hyG⟩
        obtain ⟨n, V, hV, rfl⟩ := h𝓖 hG
        by_cases hn : n < i₀
        · left
          exact mem_biUnion (show n ∈ Set.Iio i₀ from hn) ⟨⟨V, ⟨hV, hG⟩, hyG.1⟩, hyG.2⟩
        · right
          exact hW'sub i₀ n (not_lt.mp hn) hyG.2
      have hcl := closure_mono hsub ht
      rw [closure_union, (Set.finite_Iio i₀).closure_biUnion, (hW i₀).2.1.closure_eq] at hcl
      rcases hcl with hcl | hcl
      · simp only [mem_iUnion] at hcl
        obtain ⟨n, -, hn⟩ := hcl
        have h1 : t ∈ closure (⋃₀ {V ∈ 𝓑 n | V ∩ W' n ∈ 𝓖}) :=
          closure_mono inter_subset_left hn
        have h2 : t ∈ W' n := (hW'c n).closure_subset (closure_mono inter_subset_right hn)
        rw [hBcp n {V ∈ 𝓑 n | V ∩ W' n ∈ 𝓖} (fun V (hV : V ∈ {V ∈ 𝓑 n | V ∩ W' n ∈ 𝓖}) => hV.1)] at h1
        obtain ⟨_, ⟨V, ⟨hV, hVG⟩, rfl⟩, htV⟩ := h1
        exact ⟨closure (V ∩ W' n), ⟨_, hVG, rfl⟩,
          by rw [inter_comm]; exact (hW'o n).inter_closure ⟨h2, htV⟩⟩
      · exact absurd hcl hti

end Proofs.L_0032
