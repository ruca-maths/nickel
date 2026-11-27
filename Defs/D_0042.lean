import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0041

namespace Defs.D_0042

/-!
τ はセル位相より粗い（Chen–Wang Prop 9.5 の最後の一歩「t^h_2 → t」の根拠）。

* `tauSub_SOpen` : τ の部分基の元はすべてセル位相で開（D_0040 と g, g[p,·] の性質から）。
* `tau_SOpen` : τ の開集合はすべてセル位相で開。
* `mem_closure_of_cells` : x のどの深さのセルも S と交われば x ∈ Cl_τ S。
  論文の Prop 9.5 では t^h_2 と t が深さ v_0^{α_h} → ∞ のセルを共有するので t ∈ Cl_τ ⋃ V_{α_h}。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025
  Defs.D_0031 Defs.D_0032 Defs.D_0034 Defs.D_0035 Defs.D_0036 Defs.D_0039 Defs.D_0040
  Defs.D_0041

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

theorem SOpen_compl_of_SClosed {A : Set (ℕ → α)} (h : SClosed q T A) : SOpen q T Aᶜ := by
  intro x hx
  obtain ⟨L, h0, hL⟩ := h x hx
  exact ⟨L, h0, Set.subset_compl_iff_disjoint_right.mpr hL⟩

theorem SOpen_inter {A B : Set (ℕ → α)} (hA : SOpen q T A) (hB : SOpen q T B) :
    SOpen q T (A ∩ B) := by
  intro x hx
  obtain ⟨L1, h1, hL1⟩ := hA x hx.1
  obtain ⟨L2, h2, hL2⟩ := hB x hx.2
  exact ⟨L1 + L2, by omega, Set.subset_inter ((Hcell_anti h1 (by omega) x).trans hL1)
    ((Hcell_anti h2 (by omega) x).trans hL2)⟩

theorem SOpen_sUnion {S : Set (Set (ℕ → α))} (h : ∀ s ∈ S, SOpen q T s) : SOpen q T (⋃₀ S) := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨L, h0, hL⟩ := h s hs x hx
  exact ⟨L, h0, hL.trans (Set.subset_sUnion_of_mem hs)⟩

theorem SOpen_univ : SOpen q T (Set.univ : Set (ℕ → α)) :=
  fun x _ => ⟨1, by omega, Set.subset_univ _⟩

theorem tauSub_SOpen (hc : Compat2 q T) (hm : 0 < m) {A : Set (ℕ → ℕ)} {s : Set (ℕ → α)}
    (hs : s ∈ tauSub q T m y0 A) : SOpen q T s := by
  rcases hs with (⟨l, x', hl, rfl | rfl⟩ | ⟨a, -, p, hp, k, rfl | rfl⟩) |
      ⟨a, -, p, hp, k, ℓ, ph, x, hℓ, hph, rfl | rfl⟩
  · exact gfun_SOpen hc hl x'
  · exact SOpen_compl_of_SClosed (gfun_SClosed hc hl x')
  · have hp0 : ∀ j, 0 < p j := fun j => lt_of_lt_of_le hp.2.2 (hp.1 (Nat.zero_le j))
    exact (EsetO_SOpen_SClosed (y0 := y0) hc hm a p hp0 (k + 1)).1
  · have hp0 : ∀ j, 0 < p j := fun j => lt_of_lt_of_le hp.2.2 (hp.1 (Nat.zero_le j))
    exact SOpen_compl_of_SClosed (EsetO_SOpen_SClosed (y0 := y0) hc hm a p hp0 (k + 1)).2
  · have : 0 < ph := by have := hp.2.1; have := hp.1 (show 1 ≤ k + 2 by omega); omega
    exact gset_SOpen hc this _
  · have : 0 < ph := by have := hp.2.1; have := hp.1 (show 1 ≤ k + 2 by omega); omega
    exact SOpen_compl_of_SClosed (gset_SClosed hc this _)

/-- τ の開集合はセル位相で開。 -/
theorem tau_SOpen (hc : Compat2 q T) (hm : 0 < m) {A : Set (ℕ → ℕ)} {U : Set (ℕ → α)}
    (hU : @IsOpen _ (tau q T m y0 A) U) : SOpen q T U := by
  induction hU with
  | basic s hs => exact tauSub_SOpen hc hm hs
  | univ => exact SOpen_univ
  | inter s t _ _ ihs iht => exact SOpen_inter ihs iht
  | sUnion S _ ih => exact SOpen_sUnion ih

/-- x のすべての深さのセルが S と交われば x ∈ Cl_τ S（セル位相での収束 ⇒ τ での収束）。 -/
theorem mem_closure_of_cells (hc : Compat2 q T) (hm : 0 < m) {A : Set (ℕ → ℕ)}
    {S : Set (ℕ → α)} {x : ℕ → α} (h : ∀ L, 0 < L → (Hcell q T L x ∩ S).Nonempty) :
    x ∈ @closure _ (tau q T m y0 A) S := by
  letI := tau q T m y0 A
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨L, h0, hL⟩ := tau_SOpen hc hm hU x hxU
  obtain ⟨w, hw1, hw2⟩ := h L h0
  exact ⟨w, hL hw1, hw2⟩

end Defs.D_0042
