import Mathlib.Topology.Compactness.Paracompact
import Targets
import Proofs.L_0002
import Proofs.L_0003
import Proofs.L_0005
import Proofs.L_0010

/-!
# Verified sub-lemmas for `L_0028` (Mizokami 2004 / Ito's method)

This file provides kernel-checked building blocks toward `Specs.L_0028`:

1. `M1_paracompact`: Every M₁ space is paracompact.
2. `discrete_open_expansion_of_closed_discrete`: Every closed discrete subset `E`
   (not containing `x`) in a paracompact `T3Space` (in particular, any M₁ space)
   admits a discrete open expansion `{O p | p ∈ E}` whose closures are pairwise
   disjoint, discrete, and bounded away from `x`.
3. `sigma_cp_basis_monotone_union_closed`: Every M₁ space has a monotone
   `σ`-closure-preserving open basis `𝓑'` where each `𝓑' n` is closed under
   arbitrary unions.
4. `stratification_localized_cp`: Combining `𝓑'`, a monotone stratification `G`,
   and a CP closed neighborhood base `𝓚` at `x`, the open neighborhood base
   `V K U := ⋃ n, ⋃₀ { B ∈ 𝓑' n | B ⊆ U ∧ B ⊆ G n K }` satisfies
   `interior K ⊆ V K U ⊆ U` and is closure-preserving except possibly at
   non-regular boundary points `y ∈ K \ closure (interior K)`.
5. `regular_closed_base_of_cp_open_base`: Converse of `L_0027` — any CP open
   neighborhood base yields a CP regular-closed neighborhood base.
6. `regular_closed_base_of_isolated` and `regular_closed_base_of_countable_nhds`:
   Direct proofs of the conclusion of `L_0028` for isolated points and
   first-countable points.
-/

namespace Research.L0028

open MSpace Set TopologicalSpace Topology

/-- Sub-lemma 1: Every M₁ space is paracompact. -/
theorem M1_paracompact (X : Type) [TopologicalSpace X] (hM1 : MSpace.IsM1 X) :
    ParacompactSpace X := by
  have : T3Space X := hM1.1
  have hM2 : MSpace.IsM2 X := Proofs.L_0002.main X hM1
  have hM3 : MSpace.IsM3 X := Proofs.L_0003.main X hM2
  have hG := Proofs.L_0010.main X hM3
  exact Proofs.L_0005.main X ⟨inferInstance, hG⟩

/-- Sub-lemma 2: In a paracompact `T3Space`, every closed discrete subset `E`
not containing `x` admits an open expansion `O : E → Set X` whose closures are
pairwise disjoint, form a discrete family, and stay bounded away from `x`. -/
theorem discrete_open_expansion_of_closed_discrete
    (X : Type) [TopologicalSpace X] [T3Space X] [ParacompactSpace X]
    (E : Set X) (hE : ∀ A ⊆ E, IsClosed A) (x : X) (hxE : x ∉ E) :
    ∃ O : E → Set X,
      (∀ p : E, IsOpen (O p) ∧ (p : X) ∈ O p) ∧
      Pairwise (fun p q : E => Disjoint (closure (O p)) (closure (O q))) ∧
      (∀ y : X, ∃ N : Set X, IsOpen N ∧ y ∈ N ∧
        ∀ p q : E, (N ∩ closure (O p)).Nonempty → (N ∩ closure (O q)).Nonempty → p = q) ∧
      x ∉ closure (⋃ p : E, O p) := by
  classical
  -- Step 1: Open cover W of X where each W z meets E in at most {z}, and avoids x if z ∈ E.
  let W : X → Set X := fun z =>
    if z ∈ E then (E \ {z})ᶜ ∩ ({x}ᶜ : Set X) else Eᶜ
  have hW_open : ∀ z, IsOpen (W z) := by
    intro z
    dsimp only [W]
    split_ifs
    · exact (hE (E \ {z}) sdiff_subset).isOpen_compl.inter isClosed_singleton.isOpen_compl
    · exact (hE E Subset.rfl).isOpen_compl
  have hW_mem : ∀ z, z ∈ W z := by
    intro z
    dsimp only [W]
    split_ifs with hz
    · refine ⟨fun h => h.2 rfl, ?_⟩
      intro hzx
      rw [mem_singleton_iff] at hzx
      exact hxE (hzx ▸ hz)
    · exact hz
  have hW_uniq : ∀ z, ∀ p q : E, (p : X) ∈ W z → (q : X) ∈ W z → p = q := by
    intro z p q hp hq
    dsimp only [W] at hp hq
    split_ifs at hp hq with hz
    · have hpz : (p : X) = z := by
        by_contra hne
        exact hp.1 ⟨p.2, hne⟩
      have hqz : (q : X) = z := by
        by_contra hne
        exact hq.1 ⟨q.2, hne⟩
      exact Subtype.ext (hpz.trans hqz.symm)
    · exact (hp p.2).elim
  -- Step 2: Shrink W z by regularity to W' z with closure (W' z) ⊆ W z.
  have hshrink : ∀ z : X, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ closure U ⊆ W z := by
    intro z
    obtain ⟨K, hK_nhds, hK_closed, hKW⟩ :=
      exists_mem_nhds_isClosed_subset ((hW_open z).mem_nhds (hW_mem z))
    obtain ⟨U, hUK, hU_open, hzU⟩ := mem_nhds_iff.mp hK_nhds
    exact ⟨U, hU_open, hzU, (hK_closed.closure_subset_iff.mpr hUK).trans hKW⟩
  choose W' hW'_open hW'_mem hW'_cl using hshrink
  have hW'_cover : ⋃ z : X, W' z = univ :=
    eq_univ_of_forall fun z => mem_iUnion.mpr ⟨z, hW'_mem z⟩
  -- Step 3: Locally finite open refinement v of W'.
  obtain ⟨v, hv_open, hv_cover, hv_lf, hv_sub⟩ :=
    precise_refinement W' hW'_open hW'_cover
  have hv_cl_sub : ∀ z, closure (v z) ⊆ W z := fun z =>
    (closure_mono (hv_sub z)).trans (hW'_cl z)
  -- Step 4: Define O₀ p := (⋃ z with p ∉ closure (v z), closure (v z))ᶜ.
  let O₀ : E → Set X := fun p =>
    (⋃ (z : X) (_ : (p : X) ∉ closure (v z)), closure (v z))ᶜ
  have hO₀_open : ∀ p : E, IsOpen (O₀ p) := by
    intro p
    rw [isOpen_compl_iff]
    have hlf : LocallyFinite (fun z : { z : X // (p : X) ∉ closure (v z) } => closure (v z.1)) :=
      hv_lf.closure.comp_injective Subtype.val_injective
    have heq : (⋃ (z : X) (_ : (p : X) ∉ closure (v z)), closure (v z)) =
        ⋃ z : { z : X // (p : X) ∉ closure (v z) }, closure (v z.1) := by
      ext y; simp
    rw [heq]
    exact hlf.isClosed_iUnion (fun _ => isClosed_closure)
  have hO₀_mem : ∀ p : E, (p : X) ∈ O₀ p := by
    intro p h
    simp only [mem_iUnion] at h
    obtain ⟨z, hz, hpz⟩ := h
    exact hz hpz
  have hv_hits_at_most_one : ∀ z : X, ∀ p : E, (v z ∩ O₀ p).Nonempty → (p : X) ∈ W z := by
    intro z p ⟨w, hwv, hwO⟩
    have hp_cl : (p : X) ∈ closure (v z) := by
      by_contra hnot
      exact hwO (mem_iUnion₂.mpr ⟨z, hnot, subset_closure hwv⟩)
    exact hv_cl_sub z hp_cl
  -- Step 5: Shrink each O₀ p by regularity to O p with closure (O p) ⊆ O₀ p.
  have hO_shrink : ∀ p : E, ∃ U : Set X, IsOpen U ∧ (p : X) ∈ U ∧ closure U ⊆ O₀ p := by
    intro p
    obtain ⟨K, hK_nhds, hK_closed, hKO⟩ :=
      exists_mem_nhds_isClosed_subset ((hO₀_open p).mem_nhds (hO₀_mem p))
    obtain ⟨U, hUK, hU_open, hpU⟩ := mem_nhds_iff.mp hK_nhds
    exact ⟨U, hU_open, hpU, (hK_closed.closure_subset_iff.mpr hUK).trans hKO⟩
  choose O hO_open hO_mem hO_cl using hO_shrink
  refine ⟨O, fun p => ⟨hO_open p, hO_mem p⟩, ?_, ?_, ?_⟩
  · -- Pairwise disjointness of closures
    intro p q hpq
    rw [Set.disjoint_left]
    intro y hyp hyq
    have hy_univ : y ∈ ⋃ z : X, v z := hv_cover.symm ▸ mem_univ y
    obtain ⟨z, hyz⟩ := mem_iUnion.mp hy_univ
    have hpW : (p : X) ∈ W z := hv_hits_at_most_one z p ⟨y, hyz, hO_cl p hyp⟩
    have hqW : (q : X) ∈ W z := hv_hits_at_most_one z q ⟨y, hyz, hO_cl q hyq⟩
    exact hpq (hW_uniq z p q hpW hqW)
  · -- Discreteness of {closure (O p)}
    intro y
    have hy_univ : y ∈ ⋃ z : X, v z := hv_cover.symm ▸ mem_univ y
    obtain ⟨z, hyz⟩ := mem_iUnion.mp hy_univ
    refine ⟨v z, hv_open z, hyz, fun p q ⟨w₁, hw₁v, hw₁p⟩ ⟨w₂, hw₂v, hw₂q⟩ => ?_⟩
    have hpW : (p : X) ∈ W z := hv_hits_at_most_one z p ⟨w₁, hw₁v, hO_cl p hw₁p⟩
    have hqW : (q : X) ∈ W z := hv_hits_at_most_one z q ⟨w₂, hw₂v, hO_cl q hw₂q⟩
    exact hW_uniq z p q hpW hqW
  · -- x ∉ closure (⋃ p, O p)
    have hx_univ : x ∈ ⋃ z : X, v z := hv_cover.symm ▸ mem_univ x
    obtain ⟨z, hxz⟩ := mem_iUnion.mp hx_univ
    intro hx_cl
    obtain ⟨w, hwv, hwU⟩ := mem_closure_iff.mp hx_cl (v z) (hv_open z) hxz
    obtain ⟨p, hwp⟩ := mem_iUnion.mp hwU
    have hpW : (p : X) ∈ W z := hv_hits_at_most_one z p ⟨w, hwv, hO_cl p (subset_closure hwp)⟩
    have hxW : x ∈ W z := hv_cl_sub z (subset_closure hxz)
    dsimp only [W] at hpW hxW
    split_ifs at hpW hxW with hz
    · exact hxW.2 rfl
    · exact hpW p.2

/-- Helper: Closure-preserving is preserved by taking arbitrary unions. -/
theorem closurePreserving_sUnion_closure {X : Type} [TopologicalSpace X]
    {𝓑 : Set (Set X)} (hcp : MSpace.ClosurePreserving 𝓑) :
    MSpace.ClosurePreserving { U : Set X | ∃ 𝓕 ⊆ 𝓑, U = ⋃₀ 𝓕 } := by
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · intro y hy
    let 𝓕_all : Set (Set X) := { B ∈ 𝓑 | ∃ U ∈ 𝓖, B ⊆ U }
    have hsub : ⋃₀ 𝓖 ⊆ ⋃₀ 𝓕_all := by
      rintro z ⟨U, hU𝓖, hzU⟩
      obtain ⟨𝓕, h𝓕𝓑, hUeq⟩ := h𝓖 hU𝓖
      rw [hUeq] at hzU
      obtain ⟨B, hB𝓕, hzB⟩ := hzU
      exact ⟨B, ⟨h𝓕𝓑 hB𝓕, U, hU𝓖, hUeq ▸ subset_sUnion_of_mem hB𝓕⟩, hzB⟩
    have hy' : y ∈ closure (⋃₀ 𝓕_all) := closure_mono hsub hy
    rw [hcp 𝓕_all (fun _ h => h.1)] at hy'
    obtain ⟨C, ⟨B, ⟨_, U, hU𝓖, hBU⟩, rfl⟩, hyB⟩ := hy'
    exact ⟨closure U, mem_image_of_mem _ hU𝓖, closure_mono hBU hyB⟩
  · exact sUnion_subset (by rintro _ ⟨U, hU, rfl⟩; exact closure_mono (subset_sUnion_of_mem hU))

/-- Helper: Finite union of closure-preserving families is closure-preserving. -/
theorem closurePreserving_biUnion_Iic {X : Type} [TopologicalSpace X]
    {𝓑' : ℕ → Set (Set X)} (hcp : ∀ n, MSpace.ClosurePreserving (𝓑' n)) (n : ℕ) :
    MSpace.ClosurePreserving (⋃ k ≤ n, 𝓑' k) := by
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · intro y hy
    have hsplit : ⋃₀ 𝓖 ⊆ ⋃ k ∈ Iic n, ⋃₀ (𝓖 ∩ 𝓑' k) := by
      rintro z ⟨B, hB𝓖, hzB⟩
      obtain ⟨k, hk, hBk⟩ := mem_iUnion₂.mp (h𝓖 hB𝓖)
      exact mem_iUnion₂.mpr ⟨k, hk, B, ⟨hB𝓖, hBk⟩, hzB⟩
    have hy' : y ∈ closure (⋃ k ∈ Iic n, ⋃₀ (𝓖 ∩ 𝓑' k)) := closure_mono hsplit hy
    rw [(finite_Iic n).closure_biUnion] at hy'
    obtain ⟨k, _, hyk⟩ := mem_iUnion₂.mp hy'
    rw [hcp k (𝓖 ∩ 𝓑' k) inter_subset_right] at hyk
    obtain ⟨C, ⟨B, hB, rfl⟩, hyB⟩ := hyk
    exact ⟨closure B, mem_image_of_mem _ hB.1, hyB⟩
  · exact sUnion_subset (by rintro _ ⟨B, hB, rfl⟩; exact closure_mono (subset_sUnion_of_mem hB))

/-- Sub-lemma 3: Every M₁ space has a monotone `σ`-CP open basis whose levels
are closed under arbitrary unions. -/
theorem sigma_cp_basis_monotone_union_closed (X : Type) [TopologicalSpace X]
    (hM1 : MSpace.IsM1 X) :
    ∃ 𝓑' : ℕ → Set (Set X),
      (∀ n, MSpace.ClosurePreserving (𝓑' n)) ∧
      (∀ n, 𝓑' n ⊆ 𝓑' (n + 1)) ∧
      (∀ n, ∀ 𝓕 ⊆ 𝓑' n, ⋃₀ 𝓕 ∈ 𝓑' n) ∧
      IsTopologicalBasis (⋃ n, 𝓑' n) := by
  obtain ⟨_, 𝓑, hB_basis, 𝓑₀, h𝓑₀_cp, h𝓑_eq⟩ := hM1
  let 𝓑₁ : ℕ → Set (Set X) := fun n => ⋃ k ≤ n, 𝓑₀ k
  let 𝓑' : ℕ → Set (Set X) := fun n => { U : Set X | ∃ 𝓕 ⊆ 𝓑₁ n, U = ⋃₀ 𝓕 }
  refine ⟨𝓑', ?_, ?_, ?_, ?_⟩
  · intro n
    exact closurePreserving_sUnion_closure (closurePreserving_biUnion_Iic h𝓑₀_cp n)
  · intro n U ⟨𝓕, h𝓕, hU⟩
    refine ⟨𝓕, h𝓕.trans ?_, hU⟩
    intro B hB
    obtain ⟨k, hk, hBk⟩ := mem_iUnion₂.mp hB
    exact mem_iUnion₂.mpr ⟨k, Nat.le_succ_of_le hk, hBk⟩
  · intro n 𝓖 h𝓖
    let 𝓕_all : Set (Set X) := { B ∈ 𝓑₁ n | ∃ U ∈ 𝓖, B ⊆ U }
    refine ⟨𝓕_all, fun _ h => h.1, ?_⟩
    ext z
    constructor
    · rintro ⟨U, hU𝓖, hzU⟩
      obtain ⟨𝓕, h𝓕, hUeq⟩ := h𝓖 hU𝓖
      rw [hUeq] at hzU
      obtain ⟨B, hB𝓕, hzB⟩ := hzU
      exact ⟨B, ⟨h𝓕 hB𝓕, U, hU𝓖, hUeq ▸ subset_sUnion_of_mem hB𝓕⟩, hzB⟩
    · rintro ⟨B, ⟨_, U, hU𝓖, hBU⟩, hzB⟩
      exact ⟨U, hU𝓖, hBU hzB⟩
  · have hopen : ∀ U ∈ ⋃ n, 𝓑' n, IsOpen U := by
      intro U hU
      obtain ⟨n, 𝓕, h𝓕, rfl⟩ := mem_iUnion.mp hU
      refine isOpen_sUnion fun B hB => ?_
      obtain ⟨k, _, hBk⟩ := mem_iUnion₂.mp (h𝓕 hB)
      exact hB_basis.isOpen (h𝓑_eq.symm ▸ mem_iUnion.mpr ⟨k, hBk⟩)
    refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    intro x U hxU hU_open
    obtain ⟨B, hB𝓑, hxB, hBU⟩ := hB_basis.exists_subset_of_mem_open hxU hU_open
    rw [h𝓑_eq, mem_iUnion] at hB𝓑
    obtain ⟨n, hBn⟩ := hB𝓑
    refine ⟨B, mem_iUnion.mpr ⟨n, {B}, ?_, (sUnion_singleton B).symm⟩, hxB, hBU⟩
    intro B' hB'
    rw [mem_singleton_iff] at hB'
    subst hB'
    exact mem_iUnion₂.mpr ⟨n, le_rfl, hBn⟩

/-- Sub-lemma 4 (Stratification-localized CP theorem):
Given a monotone union-closed `σ`-CP open basis `𝓑'`, a monotone stratification `G`,
and a CP closed neighborhood base `𝓚` at `x`, define
`V K U := ⋃ n, ⋃₀ { B ∈ 𝓑' n | B ⊆ U ∧ B ⊆ G n K }`.
Then `interior K ⊆ V K U ⊆ U`, and for any subfamily `𝓗`, any limit point `y` of
`⋃ p ∈ 𝓗, V p.1 p.2` either lies in `closure (V p.1 p.2)` for some `p ∈ 𝓗`
or lies in the non-regular boundary `p.1 \ closure (interior p.1)` of some `p ∈ 𝓗`. -/
theorem stratification_localized_cp (X : Type) [TopologicalSpace X]
    (𝓑' : ℕ → Set (Set X))
    (h𝓑'_cp : ∀ n, MSpace.ClosurePreserving (𝓑' n))
    (h𝓑'_union : ∀ n, ∀ 𝓕 ⊆ 𝓑' n, ⋃₀ 𝓕 ∈ 𝓑' n)
    (h𝓑'_basis : IsTopologicalBasis (⋃ n, 𝓑' n))
    (G : ℕ → Set X → Set X)
    (hG : MSpace.IsStratification G)
    (hG_dec : ∀ n H, IsClosed H → G (n + 1) H ⊆ G n H)
    (𝓚 : Set (Set X))
    (h𝓚_closed : ∀ K ∈ 𝓚, IsClosed K)
    (h𝓚_cp : MSpace.ClosurePreserving 𝓚) :
    let V : Set X → Set X → Set X := fun K U =>
      ⋃ n : ℕ, ⋃₀ { B ∈ 𝓑' n | B ⊆ U ∧ B ⊆ G n K }
    (∀ K U, IsOpen (V K U)) ∧
    (∀ K ∈ 𝓚, ∀ U, K ⊆ U → interior K ⊆ V K U ∧ V K U ⊆ U) ∧
    (∀ 𝓗 : Set (Set X × Set X),
      (∀ p ∈ 𝓗, p.1 ∈ 𝓚 ∧ p.1 ⊆ p.2) →
      ∀ y ∈ closure (⋃ p ∈ 𝓗, V p.1 p.2),
        (∃ p ∈ 𝓗, y ∈ closure (V p.1 p.2)) ∨
        (∃ p ∈ 𝓗, y ∈ p.1 \ closure (interior p.1))) := by
  intro V
  have hG_anti : ∀ {m n : ℕ} {H : Set X}, IsClosed H → m ≤ n → G n H ⊆ G m H := by
    intro m n H hH hmn
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hG_dec _ H hH).trans ih
  refine ⟨?_, ?_, ?_⟩
  · intro K U
    refine isOpen_iUnion fun n => isOpen_sUnion fun B hB => ?_
    exact h𝓑'_basis.isOpen (mem_iUnion.mpr ⟨n, hB.1⟩)
  · intro K hK U hKU
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨B, hB, hzB, hBint⟩ := h𝓑'_basis.exists_subset_of_mem_open hz isOpen_interior
      obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
      refine mem_iUnion.mpr ⟨n, B, ⟨hBn, ?_, ?_⟩, hzB⟩
      · exact hBint.trans (interior_subset.trans hKU)
      · exact hBint.trans (interior_subset.trans (hG.2.1 n K (h𝓚_closed K hK)))
    · intro z hz
      obtain ⟨n, B, ⟨_, hBU, _⟩, hzB⟩ := mem_iUnion.mp hz
      exact hBU hzB
  · intro 𝓗 h𝓗 y hy
    let F : Set X := ⋃ p ∈ 𝓗, p.1
    have hF_closed : IsClosed F := by
      have hF_eq : F = ⋃₀ (Prod.fst '' 𝓗) := by
        ext z; simp [F]
      have hsub : Prod.fst '' 𝓗 ⊆ 𝓚 := by
        rintro K ⟨p, hp, rfl⟩; exact (h𝓗 p hp).1
      have hcp := h𝓚_cp (Prod.fst '' 𝓗) hsub
      have himg : closure '' (Prod.fst '' 𝓗) = Prod.fst '' 𝓗 := by
        ext K
        constructor
        · rintro ⟨K', hK', rfl⟩
          rw [(h𝓚_closed K' (hsub hK')).closure_eq]
          exact hK'
        · intro hK
          exact ⟨K, hK, (h𝓚_closed K (hsub hK)).closure_eq⟩
      rw [hF_eq, ← himg, ← hcp]
      exact isClosed_closure
    by_cases hyF : y ∈ F
    · obtain ⟨p, hp𝓗, hyp⟩ := mem_iUnion₂.mp hyF
      by_cases hyint : y ∈ closure (interior p.1)
      · left
        refine ⟨p, hp𝓗, ?_⟩
        have hint : interior p.1 ⊆ V p.1 p.2 := by
          intro z hz
          obtain ⟨B, hB, hzB, hBint⟩ := h𝓑'_basis.exists_subset_of_mem_open hz isOpen_interior
          obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
          refine mem_iUnion.mpr ⟨n, B, ⟨hBn, ?_, ?_⟩, hzB⟩
          · exact hBint.trans (interior_subset.trans (h𝓗 p hp𝓗).2)
          · exact hBint.trans (interior_subset.trans (hG.2.1 n p.1 (h𝓚_closed p.1 (h𝓗 p hp𝓗).1)))
        exact closure_mono hint hyint
      · right
        exact ⟨p, hp𝓗, hyp, hyint⟩
    · left
      rw [← hG.2.2.1 F hF_closed, mem_iInter] at hyF
      push Not at hyF
      obtain ⟨N, hyN⟩ := hyF
      let Vn : ℕ → Set X × Set X → Set X := fun n p =>
        ⋃₀ { B ∈ 𝓑' n | B ⊆ p.2 ∧ B ⊆ G n p.1 }
      have hsplit : (⋃ p ∈ 𝓗, V p.1 p.2) ⊆
          (⋃ n ∈ Iio N, ⋃ p ∈ 𝓗, Vn n p) ∪ G N F := by
        intro z hz
        obtain ⟨p, hp𝓗, hzV⟩ := mem_iUnion₂.mp hz
        obtain ⟨n, hzVn⟩ := mem_iUnion.mp hzV
        by_cases hlt : n < N
        · exact Or.inl (mem_iUnion₂.mpr ⟨n, hlt, mem_iUnion₂.mpr ⟨p, hp𝓗, hzVn⟩⟩)
        · right
          obtain ⟨B, ⟨_, _, hBG⟩, hzB⟩ := hzVn
          have hpF : p.1 ⊆ F := fun w hw => mem_iUnion₂.mpr ⟨p, hp𝓗, hw⟩
          have h1 : G n p.1 ⊆ G n F := hG.2.2.2 n p.1 F (h𝓚_closed p.1 (h𝓗 p hp𝓗).1) hF_closed hpF
          have h2 : G n F ⊆ G N F := hG_anti hF_closed (not_lt.mp hlt)
          exact h2 (h1 (hBG hzB))
      have hy_union : y ∈ closure (⋃ n ∈ Iio N, ⋃ p ∈ 𝓗, Vn n p) ∪ closure (G N F) := by
        rw [← closure_union]
        exact closure_mono hsplit hy
      rcases hy_union with hy_low | hy_high
      · rw [(finite_Iio N).closure_biUnion] at hy_low
        obtain ⟨n, _, hyn⟩ := mem_iUnion₂.mp hy_low
        have hVn_mem : ∀ p ∈ 𝓗, Vn n p ∈ 𝓑' n := fun p _ =>
          h𝓑'_union n _ (fun _ h => h.1)
        have hEq : (⋃ p ∈ 𝓗, Vn n p) = ⋃₀ ((Vn n) '' 𝓗) := by
          ext z; simp
        rw [hEq, h𝓑'_cp n ((Vn n) '' 𝓗) (by rintro _ ⟨p, hp, rfl⟩; exact hVn_mem p hp)] at hyn
        obtain ⟨C, ⟨_, ⟨p, hp𝓗, rfl⟩, rfl⟩, hyp⟩ := hyn
        exact ⟨p, hp𝓗, closure_mono (fun z hz => mem_iUnion.mpr ⟨n, hz⟩) hyp⟩
      · exact (hyN hy_high).elim

/-- Sub-lemma 5 (Converse of `L_0027`): Any CP open neighborhood base at `x`
yields a CP regular-closed neighborhood base at `x`. -/
theorem regular_closed_base_of_cp_open_base (X : Type) [TopologicalSpace X] [T3Space X]
    (x : X) (𝓥 : Set (Set X))
    (h𝓥_open : ∀ V ∈ 𝓥, IsOpen V ∧ x ∈ V)
    (h𝓥_base : ∀ U : Set X, IsOpen U → x ∈ U → ∃ V ∈ 𝓥, V ⊆ U)
    (h𝓥_cp : MSpace.ClosurePreserving 𝓥) :
    ∃ 𝓚' : Set (Set X),
      (∀ K ∈ 𝓚', IsClosed K ∧ closure (interior K) = K ∧ x ∈ interior K) ∧
      (∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚', K ⊆ U) ∧
      MSpace.ClosurePreserving 𝓚' := by
  refine ⟨closure '' 𝓥, ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    refine ⟨isClosed_closure, ?_, ?_⟩
    · apply Subset.antisymm
      · exact closure_minimal interior_subset isClosed_closure
      · exact closure_mono (interior_maximal subset_closure (h𝓥_open V hV).1)
    · exact interior_maximal subset_closure (h𝓥_open V hV).1 (h𝓥_open V hV).2
  · intro U hU hxU
    obtain ⟨K, hK_nhds, hK_closed, hKU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hxU)
    obtain ⟨W, hWK, hW_open, hxW⟩ := mem_nhds_iff.mp hK_nhds
    obtain ⟨V, hV, hVW⟩ := h𝓥_base W hW_open hxW
    exact ⟨closure V, mem_image_of_mem _ hV,
      (hK_closed.closure_subset_iff.mpr (hVW.trans hWK)).trans hKU⟩
  · intro 𝓖 h𝓖
    let 𝓖₀ : Set (Set X) := { V ∈ 𝓥 | closure V ∈ 𝓖 }
    have himg : closure '' 𝓖₀ = 𝓖 := by
      ext K
      constructor
      · rintro ⟨V, hV, rfl⟩; exact hV.2
      · intro hK
        obtain ⟨V, hV, rfl⟩ := h𝓖 hK
        exact ⟨V, ⟨hV, hK⟩, rfl⟩
    have hcl_eq : ⋃₀ (closure '' 𝓖) = ⋃₀ 𝓖 := by
      ext z
      constructor
      · rintro ⟨C, ⟨K, hK, rfl⟩, hz⟩
        obtain ⟨V, _, rfl⟩ := h𝓖 hK
        rw [closure_closure] at hz
        exact ⟨closure V, hK, hz⟩
      · rintro ⟨K, hK, hz⟩
        exact ⟨closure K, mem_image_of_mem _ hK, subset_closure hz⟩
    have h𝓑_eq_aux : closure (⋃₀ (closure '' 𝓖₀)) = ⋃₀ (closure '' 𝓖₀) := by
      rw [← h𝓥_cp 𝓖₀ (fun _ h => h.1), closure_closure]
    rw [hcl_eq, ← himg, h𝓑_eq_aux]

/-- Sub-lemma 6a: `L_0028` holds directly at any isolated point `x`. -/
theorem regular_closed_base_of_isolated (X : Type) [TopologicalSpace X] [T1Space X]
    (x : X) (hx : IsOpen ({x} : Set X)) :
    ∃ 𝓚' : Set (Set X),
      (∀ K ∈ 𝓚', IsClosed K ∧ closure (interior K) = K ∧ x ∈ interior K) ∧
      (∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚', K ⊆ U) ∧
      MSpace.ClosurePreserving 𝓚' := by
  refine ⟨{{x}}, ?_, ?_, ?_⟩
  · rintro K hK
    rw [mem_singleton_iff] at hK
    subst hK
    refine ⟨isClosed_singleton, ?_, ?_⟩
    · rw [hx.interior_eq, isClosed_singleton.closure_eq]
    · rw [hx.interior_eq]; exact rfl
  · intro U _ hxU
    exact ⟨{x}, mem_singleton _, singleton_subset_iff.mpr hxU⟩
  · intro 𝓖 h𝓖
    rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨K, hK⟩
    · simp
    · have hEq : 𝓖 = {{x}} := by
        ext S
        constructor
        · intro hS; exact h𝓖 hS
        · intro hS
          rw [mem_singleton_iff] at hS
          have hKx := h𝓖 hK
          rw [mem_singleton_iff] at hKx
          exact hS.symm ▸ hKx.symm ▸ hK
      rw [hEq, sUnion_singleton, image_singleton, sUnion_singleton]

/-- Sub-lemma 6b: `L_0028` holds directly at any point `x` with a countable
neighborhood base (in particular, in any first-countable `T3Space`). -/
theorem regular_closed_base_of_countable_nhds (X : Type) [TopologicalSpace X] [T3Space X]
    (x : X) (B : ℕ → Set X)
    (hB_open : ∀ n, IsOpen (B n) ∧ x ∈ B n)
    (hB_base : ∀ U : Set X, IsOpen U → x ∈ U → ∃ n, B n ⊆ U) :
    ∃ 𝓚' : Set (Set X),
      (∀ K ∈ 𝓚', IsClosed K ∧ closure (interior K) = K ∧ x ∈ interior K) ∧
      (∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚', K ⊆ U) ∧
      MSpace.ClosurePreserving 𝓚' := by
  let V : ℕ → Set X := fun n => ⋂ k ∈ Iic n, B k
  have hV_open : ∀ n, IsOpen (V n) ∧ x ∈ V n := fun n =>
    ⟨(finite_Iic n).isOpen_biInter (fun k _ => (hB_open k).1),
     mem_iInter₂.mpr (fun k _ => (hB_open k).2)⟩
  have hV_sub_B : ∀ n, V n ⊆ B n := fun n _ hz => mem_iInter₂.mp hz n (mem_Iic.mpr le_rfl)
  have hV_anti : ∀ {m n : ℕ}, m ≤ n → V n ⊆ V m := fun hmn _ hz =>
    mem_iInter₂.mpr (fun k hk => mem_iInter₂.mp hz k (mem_Iic.mpr (le_trans (mem_Iic.mp hk) hmn)))
  refine regular_closed_base_of_cp_open_base X x (Set.range V) ?_ ?_ ?_
  · rintro _ ⟨n, rfl⟩; exact hV_open n
  · intro U hU hxU
    obtain ⟨n, hn⟩ := hB_base U hU hxU
    exact ⟨V n, ⟨n, rfl⟩, (hV_sub_B n).trans hn⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      by_cases hyx : y = x
      · subst hyx
        rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨U, hU⟩
        · simp at hy
        · obtain ⟨n, rfl⟩ := h𝓖 hU
          exact ⟨closure (V n), mem_image_of_mem _ hU, subset_closure (hV_open n).2⟩
      · obtain ⟨K, hK_nhds, hK_closed, hKsub⟩ :=
          exists_mem_nhds_isClosed_subset (isClosed_singleton.isOpen_compl.mem_nhds (Ne.symm hyx))
        obtain ⟨W, hWK, hW_open, hxW⟩ := mem_nhds_iff.mp hK_nhds
        obtain ⟨N, hNB⟩ := hB_base W hW_open hxW
        have hy_not_VN : y ∉ closure (V N) := by
          intro h
          have hyK : y ∈ K := (hK_closed.closure_subset_iff.mpr ((hV_sub_B N).trans (hNB.trans hWK))) h
          exact hKsub hyK rfl
        let 𝓖_low : Set (Set X) := { U ∈ 𝓖 | ∃ n < N, U = V n }
        have hsplit : ⋃₀ 𝓖 ⊆ ⋃₀ 𝓖_low ∪ V N := by
          rintro z ⟨U, hU𝓖, hzU⟩
          obtain ⟨n, rfl⟩ := h𝓖 hU𝓖
          by_cases hlt : n < N
          · exact Or.inl ⟨V n, ⟨hU𝓖, n, hlt, rfl⟩, hzU⟩
          · exact Or.inr (hV_anti (not_lt.mp hlt) hzU)
        have hy_u : y ∈ closure (⋃₀ 𝓖_low) ∪ closure (V N) := by
          rw [← closure_union]
          exact closure_mono hsplit hy
        rcases hy_u with hy_low | hy_high
        · have hfin : 𝓖_low.Finite := by
            refine ((finite_Iio N).image V).subset ?_
            rintro U ⟨_, n, hlt, rfl⟩
            exact ⟨n, hlt, rfl⟩
          rw [hfin.closure_sUnion] at hy_low
          obtain ⟨U, hU, hyU⟩ := mem_iUnion₂.mp hy_low
          exact ⟨closure U, mem_image_of_mem _ hU.1, hyU⟩
        · exact (hy_not_VN hy_high).elim
    · exact sUnion_subset (by rintro _ ⟨U, hU, rfl⟩; exact closure_mono (subset_sUnion_of_mem hU))

end Research.L0028
