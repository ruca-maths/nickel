import Targets

namespace ChildResearch.ClosureFromConvergentCompanions

open Set Filter Topology

/-- A sequence of companion points contained in the selected neighborhoods
forces its limit into the closure of their union. This is the final
topological step in Chen--Wang Proposition 9.5(C). -/
theorem limit_mem_closure_iUnion {X : Type} [TopologicalSpace X]
    (t : X) (p : ℕ → X) (V : ℕ → Set X)
    (hp : Tendsto p atTop (𝓝 t))
    (hmem : ∀ n, p n ∈ V n) :
    t ∈ closure (⋃ n, V n) := by
  apply mem_closure_iff_nhds.mpr
  intro U hU
  have heventually : ∀ᶠ n : ℕ in atTop, p n ∈ U := hp hU
  obtain ⟨n, hn⟩ := heventually.exists
  exact ⟨p n, hn, mem_iUnion.mpr ⟨n, hmem n⟩⟩

/-- Package the exact endpoint of the published diagonal argument:
the stratification criterion supplies convergence, while the companion
construction supplies membership in the corresponding V_alpha. -/
theorem chenWang_endpoint {Y : Type} [TopologicalSpace Y]
    (g : ℕ → Y → Set Y) (p : ℕ → Y) (k : ℕ → ℕ) (t : Y)
    (V : ℕ → Set Y)
    (hanti : ∀ y, Antitone (fun n => g n y))
    (hsep : ∀ H : Set Y, IsClosed H → t ∉ H →
      ∃ m, t ∉ closure (⋃ y ∈ H, g m y))
    (hk : Tendsto k atTop atTop)
    (hcell : ∀ n, t ∈ g (k n) (p n))
    (hcompanion : ∀ n, p n ∈ V n) :
    t ∈ closure (⋃ n, V n) := by
  have hp : Tendsto p atTop (𝓝 t) := by
    apply tendsto_nhds.mpr
    intro U hU ht
    obtain ⟨m, hm⟩ := hsep Uᶜ hU.isClosed_compl (fun h => h ht)
    have he := hk.eventually (eventually_ge_atTop m)
    exact he.mono fun n hn => by
      by_contra hp
      apply hm
      exact subset_closure (mem_iUnion₂.mpr ⟨p n, hp, hanti (p n) hn (hcell n)⟩)
  exact limit_mem_closure_iUnion t p V hp hcompanion

end ChildResearch.ClosureFromConvergentCompanions
