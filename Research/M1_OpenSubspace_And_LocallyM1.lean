import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Compactness.Paracompact
import Targets.Defs
import Proofs.L_0004
import Proofs.L_0005

/-!
# Open Subspaces and Locally `M₁` Stratifiable / Paracompact Spaces

This standalone module proves:

1. **`isM1_open_subspace`**: Every open subspace `U` of an `M₁` space `X` is `M₁`.
2. **`isM1_of_locallyFinite_shrunk_open_M1_cover`**: If `X` is `T₃` and covered by a
   locally finite open family `{ W i }` whose closures lie inside open `M₁` subspaces
   `U i` (`closure (W i) ⊆ U i`), then `X` is `M₁`.
3. **`isM1_of_paracompact_locallyM1`**: Every locally `M₁` paracompact `T₃` space is `M₁`.
4. **`isM1_of_stratifiable_locallyM1`**: Every locally `M₁` stratifiable space is `M₁`
   (combining (3) with `Proofs.L_0004` and `Proofs.L_0005`).
5. **`exists_point_no_M1_open_nhd_of_not_isM1`**: Contrapositively, any stratifiable space
   `X` that is not `M₁` must contain a point `x₀ : X` admitting **no** open `M₁` neighborhood.
-/

namespace Research.LocallyM1

open Set Topology TopologicalSpace

/-! ## Theorem 1: Open subspaces of `M₁` spaces are `M₁` -/

/-- Every open subspace `U` of an `M₁` space `X` is `M₁`. -/
theorem isM1_open_subspace {X : Type*} [TopologicalSpace X]
    (hM1 : MSpace.IsM1 X) {U : Set X} (hUo : IsOpen U) :
    MSpace.IsM1 U := by
  obtain ⟨hT3, 𝓑, hB_basis, 𝓑', hB'_cp, hB_eq⟩ := hM1
  have : T3Space X := hT3
  let 𝓑U' : ℕ → Set (Set U) := fun n =>
    { V : Set U | ∃ B ∈ 𝓑' n, B ⊆ U ∧ V = (Subtype.val : U → X) ⁻¹' B }
  have hBU_cp : ∀ n, MSpace.ClosurePreserving (𝓑U' n) := by
    intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      let 𝓗 : Set (Set X) := { B ∈ 𝓑' n | B ⊆ U ∧ (Subtype.val : U → X) ⁻¹' B ∈ 𝓖 }
      have hH_sub : 𝓗 ⊆ 𝓑' n := fun _ h => h.1
      have hzX : z.1 ∈ closure (⋃₀ 𝓗) := by
        rw [mem_closure_iff]
        intro W hWo hzW
        have hWsub : IsOpen ((Subtype.val : U → X) ⁻¹' W) := hWo.preimage continuous_subtype_val
        obtain ⟨y, hyW, ⟨V, hVG, hyV⟩⟩ := mem_closure_iff.mp hz _ hWsub hzW
        obtain ⟨B, hBn, hBU, rfl⟩ := h𝓖 hVG
        exact ⟨y.1, hyW, ⟨B, ⟨hBn, hBU, hVG⟩, hyV⟩⟩
      rw [hB'_cp n 𝓗 hH_sub] at hzX
      obtain ⟨_, ⟨B, ⟨_, _, hBG⟩, rfl⟩, hzB⟩ := hzX
      refine ⟨closure ((Subtype.val : U → X) ⁻¹' B), ⟨(Subtype.val : U → X) ⁻¹' B, hBG, rfl⟩, ?_⟩
      rw [mem_closure_iff]
      intro W hWo hzW
      obtain ⟨W', hW'o, rfl⟩ := isOpen_induced_iff.mp hWo
      obtain ⟨y, hyW', hyB⟩ := mem_closure_iff.mp hzB (W' ∩ U) (hW'o.inter hUo) ⟨hzW, z.2⟩
      exact ⟨⟨y, hyW'.2⟩, hyW'.1, hyB⟩
    · rintro z ⟨_, ⟨V, hVG, rfl⟩, hzV⟩
      exact closure_mono (Set.subset_sUnion_of_mem hVG) hzV
  refine ⟨inferInstance, ⋃ n, 𝓑U' n, ?_, ⟨𝓑U', hBU_cp, rfl⟩⟩
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro V hV
    obtain ⟨n, B, hBn, _, rfl⟩ := mem_iUnion.mp hV
    have hBo : IsOpen B := hB_basis.isOpen (hB_eq ▸ mem_iUnion.mpr ⟨n, hBn⟩)
    exact hBo.preimage continuous_subtype_val
  · intro x V hxV hVo
    obtain ⟨V', hV'o, rfl⟩ := isOpen_induced_iff.mp hVo
    have hopen : IsOpen (V' ∩ U) := hV'o.inter hUo
    have hx_in : x.1 ∈ V' ∩ U := ⟨hxV, x.2⟩
    obtain ⟨B, hB, hxB, hBsub⟩ := hB_basis.exists_subset_of_mem_open hx_in hopen
    rw [hB_eq] at hB
    obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
    refine ⟨(Subtype.val : U → X) ⁻¹' B,
      mem_iUnion.mpr ⟨n, (⟨B, hBn, hBsub.trans inter_subset_right, rfl⟩ : (Subtype.val : U → X) ⁻¹' B ∈ 𝓑U' n)⟩,
      hxB, fun y hy => (hBsub hy).1⟩

/-! ## Theorem 2: Locally finite shrunk open `M₁` covers -/

/-- If `X` is `T₃` and covered by a locally finite open family `{ W i }` with
`closure (W i) ⊆ U i` where each `U i` is an open `M₁` subspace, then `X` is `M₁`. -/
theorem isM1_of_locallyFinite_shrunk_open_M1_cover {X ι : Type*} [TopologicalSpace X]
    [T3Space X] {W U : ι → Set X}
    (hWo : ∀ i, IsOpen (W i))
    (hUo : ∀ i, IsOpen (U i))
    (hlf : LocallyFinite W)
    (hcov : (⋃ i, W i) = Set.univ)
    (hshrink : ∀ i, closure (W i) ⊆ U i)
    (hM1 : ∀ i, MSpace.IsM1 (U i)) :
    MSpace.IsM1 X := by
  choose hT3_i 𝓑_i hB_basis_i 𝓑'_i hB'_cp_i hB_eq_i using hM1
  let 𝓑' : ℕ → Set (Set X) := fun n =>
    { B : Set X | ∃ i : ι, ∃ V ∈ 𝓑'_i i n,
        B = (Subtype.val : U i → X) '' V ∧ B ⊆ W i }
  have hB'_open : ∀ n, ∀ B ∈ 𝓑' n, IsOpen B := by
    rintro n _ ⟨i, V, hVn, rfl, _⟩
    have hVo : IsOpen V := (hB_basis_i i).isOpen (hB_eq_i i ▸ mem_iUnion.mpr ⟨n, hVn⟩)
    exact (hUo i).isOpenMap_subtype_val V hVo
  have hB'_cp : ∀ n, MSpace.ClosurePreserving (𝓑' n) := by
    intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      classical
      obtain ⟨O, hOnhd, hOfin⟩ := hlf z
      obtain ⟨O₀, hO₀_sub, hO₀_open, hzO₀⟩ := mem_nhds_iff.mp hOnhd
      let s : Finset ι := hOfin.toFinset
      choose idx_fn V_fn hV_mem hEq_fn hSub_fn using fun B : 𝓖 => h𝓖 B.2
      -- Partition `𝓖` by `i ∈ s`.
      let 𝓖_i : ι → Set (Set X) := fun i =>
        { B : Set X | ∃ hB : B ∈ 𝓖, idx_fn ⟨B, hB⟩ = i }
      have hz_fin : z ∈ closure (⋃ i ∈ (s : Set ι), ⋃₀ 𝓖_i i) := by
        rw [mem_closure_iff]
        intro P hPo hzP
        obtain ⟨y, hyOP, ⟨B, hBG, hyB⟩⟩ :=
          mem_closure_iff.mp hz (O₀ ∩ P) (hO₀_open.inter hPo) ⟨hzO₀, hzP⟩
        let i := idx_fn ⟨B, hBG⟩
        have hyW : y ∈ W i := hSub_fn ⟨B, hBG⟩ hyB
        have hi_s : i ∈ (s : Set ι) := by
          rw [Finset.mem_coe, Set.Finite.mem_toFinset]
          exact ⟨y, hyW, hO₀_sub hyOP.1⟩
        exact ⟨y, hyOP.2, mem_iUnion₂.mpr ⟨i, hi_s, ⟨B, ⟨hBG, rfl⟩, hyB⟩⟩⟩
      rw [s.finite_toSet.closure_biUnion] at hz_fin
      obtain ⟨i, _, hzi⟩ := mem_iUnion₂.mp hz_fin
      -- Since every `B ∈ 𝓖_i i` satisfies `B ⊆ W i`, `z ∈ closure (W i) ⊆ U i`.
      have hGi_sub_Wi : ⋃₀ 𝓖_i i ⊆ W i := by
        rintro y ⟨B, ⟨hBG, hidx⟩, hyB⟩
        have hsub : B ⊆ W (idx_fn ⟨B, hBG⟩) := hSub_fn ⟨B, hBG⟩
        rw [hidx] at hsub
        exact hsub hyB
      have hzU : z ∈ U i := hshrink i (closure_mono hGi_sub_Wi hzi)
      -- Pull `𝓖_i i` back to `U i` as a subfamily of `𝓑'_i i n`.
      let 𝓗 : Set (Set (U i)) :=
        { V ∈ 𝓑'_i i n | ∃ hB : ((Subtype.val : U i → X) '' V) ∈ 𝓖, idx_fn ⟨_, hB⟩ = i }
      have hH_sub : 𝓗 ⊆ 𝓑'_i i n := fun _ h => h.1
      have hz_sub : (⟨z, hzU⟩ : U i) ∈ closure (⋃₀ 𝓗) := by
        rw [mem_closure_iff]
        intro P hPo hzP
        obtain ⟨P', hP'o, rfl⟩ := isOpen_induced_iff.mp hPo
        obtain ⟨y, hyP', ⟨B, ⟨hBG, hidx⟩, hyB⟩⟩ :=
          mem_closure_iff.mp hzi (P' ∩ U i) (hP'o.inter (hUo i)) ⟨hzP, hzU⟩
        have hBeq : B = (Subtype.val : U i → X) '' (hidx ▸ V_fn ⟨B, hBG⟩) := by
          have h1 := hEq_fn ⟨B, hBG⟩
          cases hidx
          exact h1
        have hVmem : (hidx ▸ V_fn ⟨B, hBG⟩) ∈ 𝓑'_i i n := by
          have h1 := hV_mem ⟨B, hBG⟩
          cases hidx
          exact h1
        have hHmem : (hidx ▸ V_fn ⟨B, hBG⟩) ∈ 𝓗 := by
          refine ⟨hVmem, ?_, ?_⟩
          · rw [← hBeq]; exact hBG
          · convert hidx using 2
            exact Subtype.ext hBeq.symm
        rw [hBeq] at hyB
        obtain ⟨u, huV, rfl⟩ := hyB
        exact ⟨u, hyP'.1, ⟨hidx ▸ V_fn ⟨B, hBG⟩, hHmem, huV⟩⟩
      rw [hB'_cp_i i n 𝓗 hH_sub] at hz_sub
      obtain ⟨_, ⟨V, ⟨_, hBG, _⟩, rfl⟩, hzV⟩ := hz_sub
      refine ⟨closure ((Subtype.val : U i → X) '' V), ⟨_, hBG, rfl⟩, ?_⟩
      rw [mem_closure_iff]
      intro P hPo hzP
      obtain ⟨u, huP, huV⟩ :=
        mem_closure_iff.mp hzV ((Subtype.val : U i → X) ⁻¹' P) (hPo.preimage continuous_subtype_val) hzP
      exact ⟨u.1, huP, ⟨u, huV, rfl⟩⟩
    · rintro z ⟨_, ⟨B, hBG, rfl⟩, hzB⟩
      exact closure_mono (Set.subset_sUnion_of_mem hBG) hzB
  refine ⟨inferInstance, ⋃ n, 𝓑' n, ?_, ⟨𝓑', hB'_cp, rfl⟩⟩
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro B hB
    obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
    exact hB'_open n B hBn
  · intro x P hxP hPo
    have hx_cov : x ∈ (⋃ i, W i) := by rw [hcov]; trivial
    obtain ⟨i, hxW⟩ := mem_iUnion.mp hx_cov
    have hxU : x ∈ U i := hshrink i (subset_closure hxW)
    let Q : Set (U i) := (Subtype.val : U i → X) ⁻¹' (P ∩ W i)
    have hQo : IsOpen Q := (hPo.inter (hWo i)).preimage continuous_subtype_val
    have hxQ : (⟨x, hxU⟩ : U i) ∈ Q := ⟨hxP, hxW⟩
    obtain ⟨V, hV, hxV, hVQ⟩ := (hB_basis_i i).exists_subset_of_mem_open hxQ hQo
    rw [hB_eq_i i] at hV
    obtain ⟨n, hVn⟩ := mem_iUnion.mp hV
    let B : Set X := (Subtype.val : U i → X) '' V
    have hBW : B ⊆ W i := by
      rintro _ ⟨u, huV, rfl⟩
      exact (hVQ huV).2
    have hBP : B ⊆ P := by
      rintro _ ⟨u, huV, rfl⟩
      exact (hVQ huV).1
    exact ⟨B, mem_iUnion.mpr ⟨n, (⟨i, V, hVn, rfl, hBW⟩ : B ∈ 𝓑' n)⟩, ⟨⟨x, hxU⟩, hxV, rfl⟩, hBP⟩

/-! ## Theorem 3 & 4: Locally `M₁` paracompact / stratifiable spaces are `M₁` -/

/-- Every locally `M₁` paracompact `T₃` space is `M₁`. -/
theorem isM1_of_paracompact_locallyM1 {X : Type*} [TopologicalSpace X]
    [T3Space X] [ParacompactSpace X]
    (hloc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ MSpace.IsM1 U) :
    MSpace.IsM1 X := by
  choose U hUo hxU hUM1 using hloc
  -- By regularity, shrink each `U x` to an open `V x` with `x ∈ V x` and `closure (V x) ⊆ U x`.
  have hreg : ∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ closure V ⊆ U x := by
    intro x
    obtain ⟨t, ht, htc, htU⟩ := exists_mem_nhds_isClosed_subset ((hUo x).mem_nhds (hxU x))
    exact ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht,
      (closure_minimal interior_subset htc).trans htU⟩
  choose V hVo hxV hVcl using hreg
  have hVcov : (⋃ x : X, V x) = Set.univ := by
    ext y; simp only [mem_iUnion, mem_univ, iff_true]; exact ⟨y, hxV y⟩
  obtain ⟨W, hWo, hWcov, hWlf, hWref⟩ := precise_refinement V hVo hVcov
  exact isM1_of_locallyFinite_shrunk_open_M1_cover hWo hUo hWlf hWcov
    (fun x => (closure_mono (hWref x)).trans (hVcl x)) hUM1

/-- Every locally `M₁` stratifiable space is `M₁`. -/
theorem isM1_of_stratifiable_locallyM1 (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X)
    (hloc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ MSpace.IsM1 U) :
    MSpace.IsM1 X := by
  have : T3Space X := (Proofs.L_0004.strat_to_m3 X hStrat).1
  have : ParacompactSpace X := Proofs.L_0005.main X hStrat
  exact isM1_of_paracompact_locallyM1 hloc

/-- Contrapositive localization: every non-`M₁` stratifiable space contains a point
that admits **no** open `M₁` neighborhood. -/
theorem exists_point_no_M1_open_nhd_of_not_isM1 (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) (hnot : ¬ MSpace.IsM1 X) :
    ∃ x₀ : X, ∀ U : Set X, IsOpen U → x₀ ∈ U → ¬ MSpace.IsM1 U := by
  by_contra hall
  push Not at hall
  exact hnot (isM1_of_stratifiable_locallyM1 X hStrat hall)

end Research.LocallyM1
