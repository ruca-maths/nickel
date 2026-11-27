import Mathlib.Topology.LocallyFinite
import Targets.Defs

/-!
# Borges (1966): Perfect Images and Locally Finite Closed Covers of Stratifiable Spaces

This standalone module formalizes two classical permanence theorems of Borges (1966)
for stratifiable (`M₃`) spaces:

1. **Perfect Continuous Image Theorem** (`isStratifiable_of_perfectMap`):
   If `f : X → Y` is a closed continuous surjection with compact fibers from a
   stratifiable space `X` onto a `T₁` space `Y`, then `Y` is stratifiable.

2. **Locally Finite Closed Sum Theorem** (`isStratifiable_of_locallyFinite_closed_cover`):
   If `X` is a `T₁` space covered by a locally finite family `{ F i | i : ι }` of closed
   subsets such that each subspace `F i` is stratifiable, then `X` is stratifiable.
   As an immediate corollary (`isStratifiable_of_union_closed`), if `X = F₁ ∪ F₂` with
   `F₁, F₂` closed stratifiable subspaces, then `X` is stratifiable.
-/

namespace Research.BorgesPermanence

open Set Topology TopologicalSpace

/-! ## Helper: Decreasing stratification -/

private lemma exists_antitone_stratification {X : Type*} [TopologicalSpace X]
    {G : ℕ → Set X → Set X} (hG : MSpace.IsStratification G) :
    ∃ G' : ℕ → Set X → Set X,
      MSpace.IsStratification G' ∧
      (∀ n H, G' (n + 1) H ⊆ G' n H) := by
  rcases hG with ⟨hGo, hGs, hGi, hGm⟩
  let G' : ℕ → Set X → Set X := fun n H => ⋂ i ∈ Finset.range (n + 1), G i H
  refine ⟨G', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n H hH
    exact isOpen_biInter_finset fun i _ => hGo i H hH
  · intro n H hH x hx
    exact mem_iInter₂.mpr fun i _ => hGs i H hH hx
  · intro H hH
    apply Subset.antisymm
    · intro x hx
      rw [← hGi H hH]
      refine mem_iInter.mpr fun n => ?_
      have hxn : x ∈ closure (G' n H) := mem_iInter.mp hx n
      have hsub : G' n H ⊆ G n H := fun y hy =>
        mem_iInter₂.mp hy n (Finset.mem_range.mpr (Nat.lt_succ_self n))
      exact closure_mono hsub hxn
    · intro x hx
      refine mem_iInter.mpr fun n => subset_closure ?_
      exact mem_iInter₂.mpr fun i _ => hGs i H hH hx
  · intro n H K hH hK hHK x hx
    exact mem_iInter₂.mpr fun i hi => hGm i H K hH hK hHK (mem_iInter₂.mp hx i hi)
  · intro n H x hx
    exact mem_iInter₂.mpr fun i hi =>
      mem_iInter₂.mp hx i (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))

private lemma antitone_le {X : Type*} {G : ℕ → Set X → Set X}
    (hanti : ∀ n H, G (n + 1) H ⊆ G n H) {m n : ℕ} (hmn : m ≤ n) (H : Set X) :
    G n H ⊆ G m H := by
  induction hmn with
  | refl => exact Subset.rfl
  | step _ ih => exact (hanti _ H).trans ih

/-! ## Theorem 1: Perfect Continuous Images of Stratifiable Spaces -/

/-- Borges (1966): If `f : X → Y` is a closed continuous surjection with compact fibers
from a stratifiable space `X` onto a `T₁` space `Y`, then `Y` is stratifiable. -/
theorem isStratifiable_of_perfectMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space Y] (hStrat : MSpace.IsStratifiable X)
    {f : X → Y} (hcont : Continuous f) (hclosed : IsClosedMap f)
    (hsurj : Function.Surjective f) (hfib : ∀ y : Y, IsCompact (f ⁻¹' {y})) :
    MSpace.IsStratifiable Y := by
  obtain ⟨_, G₀, hG₀⟩ := hStrat
  obtain ⟨G, hG, hanti⟩ := exists_antitone_stratification hG₀
  let GY : ℕ → Set Y → Set Y := fun n C => (f '' (G n (f ⁻¹' C))ᶜ)ᶜ
  refine ⟨inferInstance, GY, ?_, ?_, ?_, ?_⟩
  · intro n C hC
    have hpre : IsClosed (f ⁻¹' C) := hC.preimage hcont
    exact (hclosed _ (hG.1 n _ hpre).isClosed_compl).isOpen_compl
  · intro n C hC y hyC
    have hpre : IsClosed (f ⁻¹' C) := hC.preimage hcont
    rintro ⟨x, hxnot, rfl⟩
    exact hxnot (hG.2.1 n _ hpre hyC)
  · intro C hC
    have hpre : IsClosed (f ⁻¹' C) := hC.preimage hcont
    apply Subset.antisymm
    · intro y hy
      by_contra hyC
      let K : Set X := f ⁻¹' {y}
      have hK_comp : IsCompact K := hfib y
      let S : ℕ → Set X := fun n => K ∩ closure (G n (f ⁻¹' C))
      have hS_closed : ∀ n, IsClosed (S n) := fun n =>
        (isClosed_singleton.preimage hcont).inter isClosed_closure
      have hS_anti : ∀ n, S (n + 1) ⊆ S n := fun n =>
        Set.inter_subset_inter_right K (closure_mono (hanti n (f ⁻¹' C)))
      have hS_empty : (⋂ n, S n) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        have hxK : f x = y := (mem_iInter.mp hx 0).1
        have hx_cl : x ∈ ⋂ n, closure (G n (f ⁻¹' C)) := mem_iInter.mpr fun n => (mem_iInter.mp hx n).2
        rw [hG.2.2.1 _ hpre] at hx_cl
        exact hyC (hxK ▸ hx_cl)
      have hex_empty : ∃ n, S n = ∅ := by
        by_contra hall
        push Not at hall
        have hne : (⋂ n, S n).Nonempty :=
          IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS_anti hall
            (hK_comp.of_isClosed_subset (hS_closed 0) inter_subset_left) hS_closed
        rw [hS_empty] at hne
        exact Set.not_nonempty_empty hne
      obtain ⟨n, hn⟩ := hex_empty
      let V : Set Y := (f '' closure (G n (f ⁻¹' C)))ᶜ
      have hVo : IsOpen V := (hclosed _ isClosed_closure).isOpen_compl
      have hyV : y ∈ V := by
        rintro ⟨x, hxcl, hfx⟩
        have hxS : x ∈ S n := ⟨hfx, hxcl⟩
        rw [hn] at hxS
        exact hxS
      have hyn : y ∈ closure (GY n C) := mem_iInter.mp hy n
      obtain ⟨z, hzV, hzGY⟩ := mem_closure_iff.mp hyn V hVo hyV
      obtain ⟨x, rfl⟩ := hsurj z
      have hxG : x ∈ G n (f ⁻¹' C) := by
        by_contra hxnot
        exact hzGY ⟨x, hxnot, rfl⟩
      exact hzV ⟨x, subset_closure hxG, rfl⟩
    · intro y hyC
      refine mem_iInter.mpr fun n => subset_closure ?_
      rintro ⟨x, hxnot, rfl⟩
      exact hxnot (hG.2.1 n _ hpre hyC)
  · intro n C₁ C₂ hC₁ hC₂ hC₁₂
    have h1 : IsClosed (f ⁻¹' C₁) := hC₁.preimage hcont
    have h2 : IsClosed (f ⁻¹' C₂) := hC₂.preimage hcont
    exact compl_subset_compl.mpr (Set.image_mono (compl_subset_compl.mpr
      (hG.2.2.2 n _ _ h1 h2 (Set.preimage_mono hC₁₂))))

/-! ## Theorem 2: Locally Finite Closed Sum Theorem for Stratifiable Spaces -/

/-- Borges (1966): If `X` is a `T₁` space covered by a locally finite family `{ F i | i : ι }`
of closed subsets such that each subspace `F i` is stratifiable, then `X` is stratifiable. -/
theorem isStratifiable_of_locallyFinite_closed_cover {X ι : Type*} [TopologicalSpace X]
    [T1Space X] {F : ι → Set X}
    (hclosed : ∀ i, IsClosed (F i))
    (hlf : LocallyFinite F)
    (hcover : (⋃ i, F i) = Set.univ)
    (hstrat : ∀ i, MSpace.IsStratifiable (F i)) :
    MSpace.IsStratifiable X := by
  choose G₀ hG₀ using fun i => (hstrat i).2
  choose G hG hanti using fun i => exists_antitone_stratification (hG₀ i)
  -- For each `i` and closed `H ⊆ X`, let `E n H i := F i \ val '' G i n (val ⁻¹' H)`.
  let E : ℕ → Set X → ι → Set X := fun n H i =>
    F i \ ((Subtype.val : F i → X) '' G i n ((Subtype.val : F i → X) ⁻¹' H))
  have hE_closed : ∀ n H, IsClosed H → ∀ i, IsClosed (E n H i) := by
    intro n H hH i
    have hHi : IsClosed ((Subtype.val : F i → X) ⁻¹' H) := hH.preimage continuous_subtype_val
    have hopen_sub : IsOpen (G i n ((Subtype.val : F i → X) ⁻¹' H)) := (hG i).1 n _ hHi
    obtain ⟨U, hUo, hUEq⟩ := isOpen_induced_iff.mp hopen_sub
    have hEq : E n H i = F i \ U := by
      ext x
      simp only [E, mem_sdiff, mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      constructor
      · rintro ⟨hxF, hnot⟩
        refine ⟨hxF, fun hxU => hnot ⟨hxF, ?_⟩⟩
        rw [← hUEq]
        exact hxU
      · rintro ⟨hxF, hxnotU⟩
        refine ⟨hxF, fun ⟨_, hxG⟩ => hxnotU ?_⟩
        rw [← hUEq] at hxG
        exact hxG
    rw [hEq]
    exact (hclosed i).sdiff hUo
  let GX : ℕ → Set X → Set X := fun n H => (⋃ i, E n H i)ᶜ
  refine ⟨inferInstance, GX, ?_, ?_, ?_, ?_⟩
  · intro n H hH
    have hlfE : LocallyFinite (E n H) := hlf.subset fun i => Set.sdiff_subset
    exact (hlfE.isClosed_iUnion (hE_closed n H hH)).isOpen_compl
  · intro n H hH x hxH
    simp only [GX, mem_compl_iff, mem_iUnion, not_exists]
    intro i ⟨hxF, hnot⟩
    have hHi : IsClosed ((Subtype.val : F i → X) ⁻¹' H) := hH.preimage continuous_subtype_val
    exact hnot ⟨⟨x, hxF⟩, (hG i).2.1 n _ hHi hxH, rfl⟩
  · intro H hH
    apply Subset.antisymm
    · intro x hx
      classical
      by_contra hxH
      obtain ⟨O, hOnhd, hOfin⟩ := hlf x
      obtain ⟨O₀, hO₀_sub, hO₀_open, hxO₀⟩ := mem_nhds_iff.mp hOnhd
      let s_all : Finset ι := hOfin.toFinset
      let s_miss : Finset ι := s_all.filter (fun i => x ∉ F i)
      let s_hit : Finset ι := s_all.filter (fun i => x ∈ F i)
      let O' : Set X := O₀ \ (⋃ i ∈ s_miss, F i)
      have hO'_open : IsOpen O' :=
        hO₀_open.sdiff (isClosed_biUnion_finset fun i _ => hclosed i)
      have hxO' : x ∈ O' := by
        refine ⟨hxO₀, ?_⟩
        simp only [mem_iUnion, not_exists]
        intro i hi hxF
        exact (Finset.mem_filter.mp hi).2 hxF
      have hsep : ∀ i : s_hit, ∃ n : ℕ, ∃ U : Set X,
          IsOpen U ∧ x ∈ U ∧ Disjoint U ((Subtype.val : F i.1 → X) '' G i.1 n ((Subtype.val : F i.1 → X) ⁻¹' H)) := by
        intro i
        have hxF : x ∈ F i.1 := (Finset.mem_filter.mp i.2).2
        have hHi : IsClosed ((Subtype.val : F i.1 → X) ⁻¹' H) := hH.preimage continuous_subtype_val
        have hnot : (⟨x, hxF⟩ : F i.1) ∉ (Subtype.val : F i.1 → X) ⁻¹' H := hxH
        rw [← (hG i.1).2.2.1 _ hHi, mem_iInter] at hnot
        push Not at hnot
        obtain ⟨n, hn⟩ := hnot
        have hopen_c : IsOpen (closure (G i.1 n ((Subtype.val : F i.1 → X) ⁻¹' H)))ᶜ :=
          isClosed_closure.isOpen_compl
        obtain ⟨U, hUo, hUEq⟩ := isOpen_induced_iff.mp hopen_c
        have hxU : x ∈ U := by
          have : (⟨x, hxF⟩ : F i.1) ∈ (Subtype.val : F i.1 → X) ⁻¹' U := by
            rw [hUEq]; exact hn
          exact this
        refine ⟨n, U, hUo, hxU, ?_⟩
        rw [Set.disjoint_left]
        rintro y hyU ⟨⟨z, hzF⟩, hzG, rfl⟩
        have hz_compl : (⟨z, hzF⟩ : F i.1) ∈ (closure (G i.1 n ((Subtype.val : F i.1 → X) ⁻¹' H)))ᶜ := by
          rw [← hUEq]; exact hyU
        exact hz_compl (subset_closure hzG)
      choose n_fn U_fn hU_open hxU hU_disj using hsep
      let N : ℕ := s_hit.attach.sup n_fn
      let W : Set X := O' ∩ (⋂ i ∈ s_hit.attach, U_fn i)
      have hWo : IsOpen W :=
        hO'_open.inter (isOpen_biInter_finset fun i _ => hU_open i)
      have hxW : x ∈ W := ⟨hxO', mem_iInter₂.mpr fun i _ => hxU i⟩
      have hxN : x ∈ closure (GX N H) := mem_iInter.mp hx N
      obtain ⟨y, hyW, hyGX⟩ := mem_closure_iff.mp hxN W hWo hxW
      have hy_cov : y ∈ (⋃ i, F i) := by rw [hcover]; trivial
      obtain ⟨i, hyF⟩ := mem_iUnion.mp hy_cov
      have hi_all : i ∈ s_all := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨y, hyF, hO₀_sub hyW.1.1⟩
      have hi_hit : i ∈ s_hit := by
        rw [Finset.mem_filter]
        refine ⟨hi_all, ?_⟩
        by_contra hxnotF
        have hi_miss : i ∈ s_miss := Finset.mem_filter.mpr ⟨hi_all, hxnotF⟩
        exact hyW.1.2 (mem_iUnion₂.mpr ⟨i, hi_miss, hyF⟩)
      let i_sub : s_hit := ⟨i, hi_hit⟩
      have hi_le : n_fn i_sub ≤ N := Finset.le_sup (f := n_fn) (Finset.mem_attach s_hit i_sub)
      have hyU : y ∈ U_fn i_sub := mem_iInter₂.mp hyW.2 i_sub (Finset.mem_attach s_hit i_sub)
      have hy_not_img : y ∉ (Subtype.val : F i → X) '' G i N ((Subtype.val : F i → X) ⁻¹' H) := by
        rintro ⟨z, hzG, rfl⟩
        have hzG' : z ∈ G i (n_fn i_sub) ((Subtype.val : F i → X) ⁻¹' H) :=
          antitone_le (hanti i) hi_le _ hzG
        exact Set.disjoint_left.mp (hU_disj i_sub) hyU ⟨z, hzG', rfl⟩
      exact hyGX (mem_iUnion.mpr ⟨i, hyF, hy_not_img⟩)
    · intro x hxH
      refine mem_iInter.mpr fun n => subset_closure ?_
      simp only [GX, mem_compl_iff, mem_iUnion, not_exists]
      intro i ⟨hxF, hnot⟩
      have hHi : IsClosed ((Subtype.val : F i → X) ⁻¹' H) := hH.preimage continuous_subtype_val
      exact hnot ⟨⟨x, hxF⟩, (hG i).2.1 n _ hHi hxH, rfl⟩
  · intro n H K hH hK hHK
    refine compl_subset_compl.mpr (Set.iUnion_mono fun i => ?_)
    have hHi : IsClosed ((Subtype.val : F i → X) ⁻¹' H) := hH.preimage continuous_subtype_val
    have hKi : IsClosed ((Subtype.val : F i → X) ⁻¹' K) := hK.preimage continuous_subtype_val
    exact Set.sdiff_subset_sdiff_right (Set.image_mono
      ((hG i).2.2.2 n _ _ hHi hKi (Set.preimage_mono hHK)))

/-- Corollary: If `X` is a `T₁` space and `X = F₁ ∪ F₂` where `F₁, F₂` are closed
stratifiable subspaces, then `X` is stratifiable. -/
theorem isStratifiable_of_union_closed {X : Type*} [TopologicalSpace X] [T1Space X]
    {F₁ F₂ : Set X} (h₁ : IsClosed F₁) (h₂ : IsClosed F₂) (hcov : F₁ ∪ F₂ = Set.univ)
    (hs₁ : MSpace.IsStratifiable F₁) (hs₂ : MSpace.IsStratifiable F₂) :
    MSpace.IsStratifiable X := by
  let F : Bool → Set X := fun b => cond b F₁ F₂
  refine isStratifiable_of_locallyFinite_closed_cover (F := F)
    (fun b => by cases b <;> simpa [F] using ‹_›)
    (locallyFinite_of_finite F)
    (by
      ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      have hx : x ∈ F₁ ∪ F₂ := by rw [hcov]; trivial
      rcases hx with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩)
    (fun b => by cases b <;> simpa [F] using ‹_›)

end Research.BorgesPermanence
