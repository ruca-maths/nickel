import Specs.L_0004

namespace Proofs.L_0004

open MSpace Set Topology TopologicalSpace

theorem m3_to_strat (X : Type) [TopologicalSpace X] (h : IsM3 X) : IsStratifiable X := by
  obtain ⟨hT3, 𝓟, ⟨hP1, hP2⟩, 𝓟', hcush, hU⟩ := h
  haveI := hT3
  let G : ℕ → Set X → Set X := fun n H =>
    (closure (⋃ p ∈ {p | p ∈ 𝓟' n ∧ Disjoint p.2 H}, p.1))ᶜ
  have hsub : ∀ n H, H ⊆ G n H := by
    intro n H x hx hxc
    have := hcush n {p | p ∈ 𝓟' n ∧ Disjoint p.2 H} (fun p hp => hp.1) hxc
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp this
    exact Set.disjoint_left.mp hp.2 hxp hx
  refine ⟨inferInstance, G, ?_, ?_, ?_, ?_⟩
  · intro n H _
    exact isClosed_closure.isOpen_compl
  · intro n H _
    exact hsub n H
  · intro H hH
    apply Subset.antisymm
    · intro x hx
      by_contra hxH
      obtain ⟨p, hp, hxp1, hp2⟩ := hP2 x Hᶜ hH.isOpen_compl hxH
      have hp' := hp
      rw [hU] at hp
      obtain ⟨n, hpn⟩ := mem_iUnion.mp hp
      have hxc : x ∈ closure (G n H) := mem_iInter.mp hx n
      have hGsub : G n H ⊆ p.1ᶜ := by
        intro y hy hyp
        apply hy
        apply subset_closure
        exact mem_iUnion₂.mpr ⟨p, ⟨hpn, Set.disjoint_left.mpr fun z hz => hp2 hz⟩, hyp⟩
      have hp1o : IsOpen p.1 := (hP1 p hp').1
      exact closure_minimal hGsub hp1o.isClosed_compl hxc hxp1
    · intro x hx
      exact mem_iInter.mpr fun n => subset_closure (hsub n H hx)
  · intro n H K _ _ hHK
    exact compl_subset_compl.mpr (closure_mono
      (biUnion_subset_biUnion_left fun p hp => ⟨hp.1, hp.2.mono_right hHK⟩))

theorem strat_to_m3 (X : Type) [TopologicalSpace X] (h : IsStratifiable X) : IsM3 X := by
  obtain ⟨hT1, G, hGo, hGs, hGi, hGm⟩ := h
  haveI := hT1
  have key : ∀ x U, IsOpen U → x ∈ U → ∃ n, x ∉ closure (G n Uᶜ) := by
    intro x U hU hx
    by_contra hc
    push_neg at hc
    have : x ∈ ⋂ n, closure (G n Uᶜ) := mem_iInter.mpr hc
    rw [hGi _ hU.isClosed_compl] at this
    exact this hx
  have hreg : RegularSpace X := by
    apply RegularSpace.of_exists_mem_nhds_isClosed_subset
    intro x s hs
    obtain ⟨n, hn⟩ := key x (interior s) isOpen_interior (mem_interior_iff_mem_nhds.mpr hs)
    refine ⟨(G n (interior s)ᶜ)ᶜ, ?_, (hGo _ _ isOpen_interior.isClosed_compl).isClosed_compl, ?_⟩
    · apply Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hn)
      exact compl_subset_compl.mpr subset_closure
    · intro y hy
      by_contra hys
      exact hy (hGs _ _ isOpen_interior.isClosed_compl (fun h => hys (interior_subset h)))
  have hT3 : T3Space X := { toT0Space := inferInstance, toRegularSpace := hreg }
  let 𝓟' : ℕ → Set (Set X × Set X) := fun n =>
    {p | ∃ U, IsOpen U ∧ p = ((closure (G n Uᶜ))ᶜ, U)}
  refine ⟨hT3, ⋃ n, 𝓟' n, ⟨?_, ?_⟩, 𝓟', ?_, rfl⟩
  · intro p hp
    obtain ⟨n, U, hU, rfl⟩ := mem_iUnion.mp hp
    refine ⟨isClosed_closure.isOpen_compl, fun y hy => ?_⟩
    by_contra hyU
    exact hy (subset_closure (hGs n Uᶜ hU.isClosed_compl hyU))
  · intro x U hU hx
    obtain ⟨n, hn⟩ := key x U hU hx
    exact ⟨((closure (G n Uᶜ))ᶜ, U), mem_iUnion.mpr ⟨n, U, hU, rfl⟩, hn, subset_rfl⟩
  · intro n 𝓠 h𝓠
    have hVo : IsOpen (⋃ p ∈ 𝓠, p.2) := isOpen_biUnion fun p hp => by
      obtain ⟨U, hU, rfl⟩ := h𝓠 hp
      exact hU
    have h1 : (⋃ p ∈ 𝓠, p.1) ⊆ (G n (⋃ p ∈ 𝓠, p.2)ᶜ)ᶜ := by
      refine iUnion₂_subset fun p hp => ?_
      obtain ⟨U, hU, rfl⟩ := h𝓠 hp
      intro y hy hyG
      apply hy
      apply subset_closure
      refine hGm n _ _ hVo.isClosed_compl hU.isClosed_compl ?_ hyG
      apply compl_subset_compl.mpr
      exact subset_biUnion_of_mem (u := fun p : Set X × Set X => p.2) hp
    calc closure (⋃ p ∈ 𝓠, p.1) ⊆ (G n (⋃ p ∈ 𝓠, p.2)ᶜ)ᶜ :=
          closure_minimal h1 (hGo _ _ hVo.isClosed_compl).isClosed_compl
      _ ⊆ ⋃ p ∈ 𝓠, p.2 := fun y hy => by
          by_contra hyV
          exact hy (hGs _ _ hVo.isClosed_compl hyV)

theorem main : Specs.L_0004.stmt := by
  unfold Specs.L_0004.stmt MSpace.Goals.T2a_M3_iff_stratifiable
  intro X _
  exact ⟨m3_to_strat X, strat_to_m3 X⟩

end Proofs.L_0004
