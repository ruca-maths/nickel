import Mathlib.Data.Nat.Pairing
import Targets.Defs
import Defs.D_0001
import Proofs.L_0004
import Proofs.L_0008

/-!
# Closed-Set CP Outer Base Algebra & Structural `M₁` Criteria for Stratifiable Spaces

This standalone module builds on the Heath (1969) $\sigma$-discrete closed network and
collectionwise normality of stratifiable spaces to establish sharp algebraic closure
properties of `HasCPOuterBaseSet` and structural `M₁` criteria:

1. **Singleton & Finite-Union Closure**:
   - `hasCPOuterBaseSet_singleton_iff`: `HasCPOuterBaseSet {x} ↔ Defs.D_0001.HasCPOuterBase x`.
   - `hasCPOuterBaseSet_union` & `hasCPOuterBaseSet_finset_biUnion`: finite unions preserve
     `HasCPOuterBaseSet` in any topological space.
2. **Discrete-Union & Closed-Discrete Closure in Stratifiable Spaces**:
   - `hasCPOuterBaseSet_sUnion_discrete`: in a stratifiable space, if `𝓕` is a discrete
     family of closed sets each having a CP open outer base, then `⋃₀ 𝓕` has a CP open
     outer base.
   - `hasCPOuterBaseSet_of_closed_discrete`: every closed discrete subset `D` of a
     stratifiable space whose points each have `HasCPOuterBase` satisfies `HasCPOuterBaseSet D`.
3. **Compact Sets with Compact Neighborhoods**:
   - `hasCPOuterBaseSet_of_compact_with_compact_nhd`: in any stratifiable space, every
     compact set `K` admitting a compact neighborhood has a decreasing countable (hence CP)
     open outer base.
4. **Structural `M₁` Criteria**:
   - `isM1_of_stratifiable_sigma_closed_discrete`: every stratifiable space expressible as
     a countable union of closed discrete subsets, whose points each have `HasCPOuterBase`,
     is `M₁`.
   - `isM1_of_stratifiable_locallyCompact_compl`: if `X` is stratifiable, every point
     `z ≠ y₀` has a compact neighborhood in `X`, and `Defs.D_0001.HasCPOuterBase y₀`, then
     `MSpace.IsM1 X` (contrapositively, any non-`M₁` stratifiable space with locally compact
     punctured complement `X \ {y₀}` automatically witnesses `¬ HasCPOuterBase y₀`).
-/

namespace Research.Ito1985Criteria

open Set Topology TopologicalSpace

/-! ## Part 1: Basic definitions & finite-union algebra -/

/-- A family `𝓕` of subsets of `X` is discrete if every point has an open neighborhood
meeting at most one member of `𝓕`. -/
def IsDiscreteFam {X : Type*} [TopologicalSpace X] (𝓕 : Set (Set X)) : Prop :=
  ∀ z : X, ∃ W : Set X, IsOpen W ∧ z ∈ W ∧
    ∀ F₁ ∈ 𝓕, ∀ F₂ ∈ 𝓕, (W ∩ F₁).Nonempty → (W ∩ F₂).Nonempty → F₁ = F₂

/-- An indexed family `W : ι → Set X` is discrete if every point has an open neighborhood
meeting `W i` for at most one index `i`. -/
def IsDiscreteIndexed {X ι : Type*} [TopologicalSpace X] (W : ι → Set X) : Prop :=
  ∀ z : X, ∃ O : Set X, IsOpen O ∧ z ∈ O ∧
    ∀ i j : ι, (O ∩ W i).Nonempty → (O ∩ W j).Nonempty → i = j

/-- Closure-preserving open outer base for a subset `F ⊆ X`. -/
def HasCPOuterBaseSet {X : Type*} [TopologicalSpace X] (F : Set X) : Prop :=
  ∃ 𝓤 : Set (Set X),
    (∀ U ∈ 𝓤, IsOpen U ∧ F ⊆ U) ∧
    MSpace.ClosurePreserving 𝓤 ∧
    (∀ W : Set X, IsOpen W → F ⊆ W → ∃ U ∈ 𝓤, U ⊆ W)

/-- `HasCPOuterBaseSet {x}` is equivalent to `Defs.D_0001.HasCPOuterBase x`. -/
theorem hasCPOuterBaseSet_singleton_iff {X : Type} [TopologicalSpace X] (x : X) :
    HasCPOuterBaseSet ({x} : Set X) ↔ Defs.D_0001.HasCPOuterBase x := by
  constructor
  · rintro ⟨𝓤, hUo, hUcp, hUbase⟩
    refine ⟨𝓤, fun U hU => ⟨(hUo U hU).1, (hUo U hU).2 rfl⟩,
      fun W hWo hxW => hUbase W hWo (Set.singleton_subset_iff.mpr hxW), hUcp⟩
  · rintro ⟨𝓤, hUo, hUbase, hUcp⟩
    refine ⟨𝓤, fun U hU => ⟨(hUo U hU).1, Set.singleton_subset_iff.mpr (hUo U hU).2⟩,
      hUcp, fun W hWo hsub => hUbase W hWo (hsub rfl)⟩

/-- `∅` always has a CP open outer base. -/
theorem hasCPOuterBaseSet_empty {X : Type*} [TopologicalSpace X] :
    HasCPOuterBaseSet (∅ : Set X) := by
  refine ⟨{∅}, ?_, ?_, fun W _ _ => ⟨∅, rfl, empty_subset W⟩⟩
  · rintro _ rfl
    exact ⟨isOpen_empty, Subset.rfl⟩
  · intro 𝓖 h𝓖
    by_cases hG : ∅ ∈ 𝓖
    · have hEq : 𝓖 = {∅} := Set.Subset.antisymm h𝓖 (Set.singleton_subset_iff.mpr hG)
      subst hEq; simp
    · have hEq : 𝓖 = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun U hU =>
        hG (Set.mem_singleton_iff.mp (h𝓖 hU) ▸ hU)
      subst hEq; simp

/-- Binary unions preserve `HasCPOuterBaseSet` in any topological space. -/
theorem hasCPOuterBaseSet_union {X : Type*} [TopologicalSpace X] {F₁ F₂ : Set X}
    (h₁ : HasCPOuterBaseSet F₁) (h₂ : HasCPOuterBaseSet F₂) :
    HasCPOuterBaseSet (F₁ ∪ F₂) := by
  obtain ⟨𝓤₁, h₁o, h₁cp, h₁b⟩ := h₁
  obtain ⟨𝓤₂, h₂o, h₂cp, h₂b⟩ := h₂
  let 𝓤 : Set (Set X) := { U : Set X | ∃ U₁ ∈ 𝓤₁, ∃ U₂ ∈ 𝓤₂, U = U₁ ∪ U₂ }
  refine ⟨𝓤, ?_, ?_, ?_⟩
  · rintro _ ⟨U₁, hU₁, U₂, hU₂, rfl⟩
    exact ⟨(h₁o U₁ hU₁).1.union (h₂o U₂ hU₂).1,
      Set.union_subset_union (h₁o U₁ hU₁).2 (h₂o U₂ hU₂).2⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      choose f₁ hf₁ f₂ hf₂ hfEq using fun (U : 𝓖) => h𝓖 U.2
      let 𝓖₁ : Set (Set X) := Set.range f₁
      let 𝓖₂ : Set (Set X) := Set.range f₂
      have hG_sub : ⋃₀ 𝓖 ⊆ ⋃₀ 𝓖₁ ∪ ⋃₀ 𝓖₂ := by
        rintro x ⟨U, hUG, hxU⟩
        have hEq : U = f₁ ⟨U, hUG⟩ ∪ f₂ ⟨U, hUG⟩ := hfEq ⟨U, hUG⟩
        rw [hEq] at hxU
        rcases hxU with hx₁ | hx₂
        · exact Or.inl ⟨f₁ ⟨U, hUG⟩, ⟨⟨U, hUG⟩, rfl⟩, hx₁⟩
        · exact Or.inr ⟨f₂ ⟨U, hUG⟩, ⟨⟨U, hUG⟩, rfl⟩, hx₂⟩
      have hz_u : z ∈ closure (⋃₀ 𝓖₁) ∪ closure (⋃₀ 𝓖₂) := by
        rw [← closure_union]
        exact closure_mono hG_sub hz
      rcases hz_u with hz₁ | hz₂
      · rw [h₁cp 𝓖₁ (by rintro _ ⟨U, rfl⟩; exact hf₁ U)] at hz₁
        obtain ⟨_, ⟨_, ⟨U, rfl⟩, rfl⟩, hzU₁⟩ := hz₁
        refine ⟨closure U.1, ⟨U.1, U.2, rfl⟩, ?_⟩
        rw [hfEq U]
        exact closure_mono subset_union_left hzU₁
      · rw [h₂cp 𝓖₂ (by rintro _ ⟨U, rfl⟩; exact hf₂ U)] at hz₂
        obtain ⟨_, ⟨_, ⟨U, rfl⟩, rfl⟩, hzU₂⟩ := hz₂
        refine ⟨closure U.1, ⟨U.1, U.2, rfl⟩, ?_⟩
        rw [hfEq U]
        exact closure_mono subset_union_right hzU₂
    · rintro z ⟨_, ⟨U, hUG, rfl⟩, hzU⟩
      exact closure_mono (Set.subset_sUnion_of_mem hUG) hzU
  · intro W hWo hsub
    obtain ⟨U₁, hU₁, hU₁W⟩ := h₁b W hWo (subset_union_left.trans hsub)
    obtain ⟨U₂, hU₂, hU₂W⟩ := h₂b W hWo (subset_union_right.trans hsub)
    exact ⟨U₁ ∪ U₂, ⟨U₁, hU₁, U₂, hU₂, rfl⟩, Set.union_subset hU₁W hU₂W⟩

/-- Finite unions preserve `HasCPOuterBaseSet` in any topological space. -/
theorem hasCPOuterBaseSet_finset_biUnion {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (F : ι → Set X) (h : ∀ i ∈ s, HasCPOuterBaseSet (F i)) :
    HasCPOuterBaseSet (⋃ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using hasCPOuterBaseSet_empty
  | @insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    exact hasCPOuterBaseSet_union (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## Part 2: Stratifiable helpers (collectionwise normality & Heath σ-discrete network) -/

private lemma isClosed_sUnion_of_isDiscreteFam {X : Type*} [TopologicalSpace X]
    {𝓕 𝓢 : Set (Set X)} (hdisc : IsDiscreteFam 𝓕) (hclosed : ∀ F ∈ 𝓕, IsClosed F)
    (hsub : 𝓢 ⊆ 𝓕) : IsClosed (⋃₀ 𝓢) := by
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
  obtain ⟨W, hWo, hzW, hWuniq⟩ := hdisc z
  by_cases hhit : ∃ F₀ ∈ 𝓢, (W ∩ F₀).Nonempty
  · obtain ⟨F₀, hF₀S, hne₀⟩ := hhit
    have hzF₀ : z ∉ F₀ := fun h => hz ⟨F₀, hF₀S, h⟩
    have hopen : IsOpen (W \ F₀) := hWo.sdiff (hclosed F₀ (hsub hF₀S))
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨hzW, hzF₀⟩) ?_
    rintro y ⟨hyW, hyF₀⟩ ⟨F, hFS, hyF⟩
    have hEq : F = F₀ := hWuniq F (hsub hFS) F₀ (hsub hF₀S) ⟨y, hyW, hyF⟩ hne₀
    exact hyF₀ (hEq ▸ hyF)
  · refine Filter.mem_of_superset (hWo.mem_nhds hzW) ?_
    rintro y hyW ⟨F, hFS, hyF⟩
    exact hhit ⟨F, hFS, y, hyW, hyF⟩

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

private def Hsep {X : Type*} [TopologicalSpace X] (G : ℕ → Set X → Set X) (A B : Set X) : Set X :=
  ⋃ n : ℕ, G n A \ closure (G n B)

private lemma isOpen_Hsep {X : Type*} [TopologicalSpace X] {G : ℕ → Set X → Set X}
    (hG : MSpace.IsStratification G) {A B : Set X} (hA : IsClosed A) :
    IsOpen (Hsep G A B) :=
  isOpen_iUnion fun n => (hG.1 n A hA).sdiff isClosed_closure

private lemma subset_Hsep {X : Type*} [TopologicalSpace X] {G : ℕ → Set X → Set X}
    (hG : MSpace.IsStratification G) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) : A ⊆ Hsep G A B := by
  intro x hxA
  have hxB : x ∉ B := Set.disjoint_left.mp hdisj hxA
  rw [← hG.2.2.1 B hB, mem_iInter] at hxB
  push Not at hxB
  obtain ⟨n, hn⟩ := hxB
  exact mem_iUnion.mpr ⟨n, hG.2.1 n A hA hxA, hn⟩

private lemma disjoint_Hsep {X : Type*} [TopologicalSpace X] {G : ℕ → Set X → Set X}
    (hanti : ∀ n H, G (n + 1) H ⊆ G n H) (A B : Set X) :
    Disjoint (Hsep G A B) (Hsep G B A) := by
  rw [Set.disjoint_left]
  intro x hxAB hxBA
  obtain ⟨n, hxnA, hxnB⟩ := mem_iUnion.mp hxAB
  obtain ⟨m, hxmB, hxmA⟩ := mem_iUnion.mp hxBA
  rcases le_total n m with hnm | hmn
  · exact hxnB (subset_closure (antitone_le hanti hnm B hxmB))
  · exact hxmA (subset_closure (antitone_le hanti hmn A hxnA))

private lemma Hsep_mono {X : Type*} [TopologicalSpace X] {G : ℕ → Set X → Set X}
    (hG : MSpace.IsStratification G) {A₁ A₂ B₁ B₂ : Set X}
    (hA₁ : IsClosed A₁) (hA₂ : IsClosed A₂) (hB₁ : IsClosed B₁) (hB₂ : IsClosed B₂)
    (hA : A₁ ⊆ A₂) (hB : B₂ ⊆ B₁) :
    Hsep G A₁ B₁ ⊆ Hsep G A₂ B₂ := by
  intro x hx
  obtain ⟨n, h1, h2⟩ := mem_iUnion.mp hx
  refine mem_iUnion.mpr ⟨n, hG.2.2.2 n A₁ A₂ hA₁ hA₂ hA h1, ?_⟩
  intro hc
  exact h2 (closure_mono (hG.2.2.2 n B₂ B₁ hB₂ hB₁ hB) hc)

private lemma stratifiable_discrete_open_expansion {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) {𝓕 : Set (Set X)}
    (hdisc : IsDiscreteFam 𝓕) (hclosed : ∀ F ∈ 𝓕, IsClosed F) :
    ∃ W : 𝓕 → Set X,
      (∀ F : 𝓕, IsOpen (W F)) ∧
      (∀ F : 𝓕, F.1 ⊆ W F) ∧
      IsDiscreteIndexed W := by
  obtain ⟨_, G₀, hG₀⟩ := hStrat
  obtain ⟨G, hG, hanti⟩ := exists_antitone_stratification hG₀
  let Fstar : 𝓕 → Set X := fun F => ⋃₀ (𝓕 \ {F.1})
  have hFstar_closed : ∀ F : 𝓕, IsClosed (Fstar F) := fun F =>
    isClosed_sUnion_of_isDiscreteFam hdisc hclosed Set.sdiff_subset
  have hFstar_disj : ∀ F : 𝓕, Disjoint F.1 (Fstar F) := by
    intro F
    rw [Set.disjoint_left]
    rintro z hzF ⟨F', ⟨hF'mem, hF'ne⟩, hzF'⟩
    obtain ⟨O, _, hzO, hOuniq⟩ := hdisc z
    exact hF'ne (hOuniq F' hF'mem F.1 F.2 ⟨z, hzO, hzF'⟩ ⟨z, hzO, hzF⟩)
  let V : 𝓕 → Set X := fun F => Hsep G F.1 (Fstar F)
  have hV_open : ∀ F : 𝓕, IsOpen (V F) := fun F => isOpen_Hsep hG (hclosed F.1 F.2)
  have hV_sub : ∀ F : 𝓕, F.1 ⊆ V F := fun F =>
    subset_Hsep hG (hclosed F.1 F.2) (hFstar_closed F) (hFstar_disj F)
  have hV_disj : ∀ F₁ F₂ : 𝓕, F₁ ≠ F₂ → Disjoint (V F₁) (V F₂) := by
    intro F₁ F₂ hne
    have hval_ne : F₁.1 ≠ F₂.1 := fun h => hne (Subtype.ext h)
    have hsub1 : F₂.1 ⊆ Fstar F₁ := Set.subset_sUnion_of_mem ⟨F₂.2, Ne.symm hval_ne⟩
    have hsub2 : F₁.1 ⊆ Fstar F₂ := Set.subset_sUnion_of_mem ⟨F₁.2, hval_ne⟩
    have h1 : V F₁ ⊆ Hsep G F₁.1 F₂.1 :=
      Hsep_mono hG (hclosed F₁.1 F₁.2) (hclosed F₁.1 F₁.2) (hFstar_closed F₁) (hclosed F₂.1 F₂.2)
        Subset.rfl hsub1
    have h2 : V F₂ ⊆ Hsep G F₂.1 F₁.1 :=
      Hsep_mono hG (hclosed F₂.1 F₂.2) (hclosed F₂.1 F₂.2) (hFstar_closed F₂) (hclosed F₁.1 F₁.2)
        Subset.rfl hsub2
    exact (disjoint_Hsep hanti F₁.1 F₂.1).mono h1 h2
  let E : Set X := ⋃₀ 𝓕
  have hE_closed : IsClosed E := isClosed_sUnion_of_isDiscreteFam hdisc hclosed Subset.rfl
  let U : Set X := ⋃ F : 𝓕, V F
  have hU_open : IsOpen U := isOpen_iUnion hV_open
  have hEU : Disjoint E Uᶜ := by
    rw [Set.disjoint_compl_right_iff_subset]
    rintro z ⟨F, hF, hzF⟩
    exact mem_iUnion.mpr ⟨⟨F, hF⟩, hV_sub ⟨F, hF⟩ hzF⟩
  let O : Set X := Hsep G E Uᶜ
  have hO_open : IsOpen O := isOpen_Hsep hG hE_closed
  have hEO : E ⊆ O := subset_Hsep hG hE_closed hU_open.isClosed_compl hEU
  have hclO_sub_U : closure O ⊆ U := by
    have hdisjO : Disjoint O (Hsep G Uᶜ E) := disjoint_Hsep hanti E Uᶜ
    have hO2_open : IsOpen (Hsep G Uᶜ E) := isOpen_Hsep hG hU_open.isClosed_compl
    have hUcompl_sub : Uᶜ ⊆ Hsep G Uᶜ E :=
      subset_Hsep hG hU_open.isClosed_compl hE_closed hEU.symm
    intro z hz
    by_contra hzU
    have hz2 : z ∈ Hsep G Uᶜ E := hUcompl_sub hzU
    obtain ⟨y, hy2, hyO⟩ := mem_closure_iff.mp hz (Hsep G Uᶜ E) hO2_open hz2
    exact Set.disjoint_left.mp hdisjO hyO hy2
  let W : 𝓕 → Set X := fun F => V F ∩ O
  refine ⟨W, fun F => (hV_open F).inter hO_open, fun F x hx => ⟨hV_sub F hx, hEO ⟨F.1, F.2, hx⟩⟩, ?_⟩
  intro z
  by_cases hzU : z ∈ U
  · obtain ⟨F₀, hzF₀⟩ := mem_iUnion.mp hzU
    refine ⟨V F₀, hV_open F₀, hzF₀, fun F₁ F₂ ⟨y₁, hy₁V₀, hy₁W₁⟩ ⟨y₂, hy₂V₀, hy₂W₂⟩ => ?_⟩
    have h1 : F₁ = F₀ := by
      by_contra hne
      exact Set.disjoint_left.mp (hV_disj F₁ F₀ hne) hy₁W₁.1 hy₁V₀
    have h2 : F₂ = F₀ := by
      by_contra hne
      exact Set.disjoint_left.mp (hV_disj F₂ F₀ hne) hy₂W₂.1 hy₂V₀
    rw [h1, h2]
  · refine ⟨(closure O)ᶜ, isClosed_closure.isOpen_compl, fun h => hzU (hclO_sub_U h), ?_⟩
    intro F₁ _ ⟨y₁, hy₁c, hy₁W₁⟩ _
    exact (hy₁c (subset_closure hy₁W₁.2)).elim

/-! ## Part 3: Discrete-union & closed-discrete closure of `HasCPOuterBaseSet` -/

/-- In a stratifiable space, if `𝓕` is a discrete family of closed sets and each `F ∈ 𝓕`
has a CP open outer base, then `⋃₀ 𝓕` has a CP open outer base. -/
theorem hasCPOuterBaseSet_sUnion_discrete {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) {𝓕 : Set (Set X)}
    (hdisc : IsDiscreteFam 𝓕) (hclosed : ∀ F ∈ 𝓕, IsClosed F)
    (hCP : ∀ F ∈ 𝓕, HasCPOuterBaseSet F) :
    HasCPOuterBaseSet (⋃₀ 𝓕) := by
  obtain ⟨W, hW_open, hW_sub, hW_disc⟩ :=
    stratifiable_discrete_open_expansion hStrat hdisc hclosed
  choose 𝓤 hU_open hU_cp hU_base using fun F : 𝓕 => hCP F.1 F.2
  let 𝓥 : Set (Set X) :=
    { V : Set X | ∃ u : 𝓕 → Set X, (∀ F : 𝓕, u F ∈ 𝓤 F ∧ u F ⊆ W F) ∧ V = ⋃ F : 𝓕, u F }
  refine ⟨𝓥, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨isOpen_iUnion fun F => (hU_open F (u F) (hu F).1).1, ?_⟩
    rintro x ⟨F, hF, hxF⟩
    exact mem_iUnion.mpr ⟨⟨F, hF⟩, (hU_open ⟨F, hF⟩ (u ⟨F, hF⟩) (hu ⟨F, hF⟩).1).2 hxF⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      obtain ⟨O, hOo, hzO, hOuniq⟩ := hW_disc z
      choose u hu huEq using fun V : 𝓖 => h𝓖 V.2
      have hne_hit : ∃ V : 𝓖, ∃ F₀ : 𝓕, (O ∩ u V F₀).Nonempty := by
        obtain ⟨y, hyO, ⟨V, hVG, hyV⟩⟩ := mem_closure_iff.mp hz O hOo hzO
        have hEq : V = ⋃ F, u ⟨V, hVG⟩ F := huEq ⟨V, hVG⟩
        rw [hEq] at hyV
        obtain ⟨F₀, hyF₀⟩ := mem_iUnion.mp hyV
        exact ⟨⟨V, hVG⟩, F₀, y, hyO, hyF₀⟩
      obtain ⟨V₀, F₀, hO_u₀⟩ := hne_hit
      have hO_W₀ : (O ∩ W F₀).Nonempty := hO_u₀.mono (inter_subset_inter_right O (hu V₀ F₀).2)
      let 𝓖₀ : Set (Set X) := Set.range (fun V : 𝓖 => u V F₀)
      have hG₀_sub : 𝓖₀ ⊆ 𝓤 F₀ := by
        rintro _ ⟨V, rfl⟩
        exact (hu V F₀).1
      have hz_cl0 : z ∈ closure (⋃₀ 𝓖₀) := by
        rw [mem_closure_iff]
        intro U hUo hzU
        obtain ⟨y, hyOU, ⟨V, hVG, hyV⟩⟩ :=
          mem_closure_iff.mp hz (O ∩ U) (hOo.inter hUo) ⟨hzO, hzU⟩
        have hEq : V = ⋃ F, u ⟨V, hVG⟩ F := huEq ⟨V, hVG⟩
        rw [hEq] at hyV
        obtain ⟨F, hyF⟩ := mem_iUnion.mp hyV
        have hF_eq : F = F₀ :=
          hOuniq F F₀ ⟨y, hyOU.1, (hu ⟨V, hVG⟩ F).2 hyF⟩ hO_W₀
        subst hF_eq
        exact ⟨y, hyOU.2, ⟨u ⟨V, hVG⟩ F, ⟨⟨V, hVG⟩, rfl⟩, hyF⟩⟩
      rw [hU_cp F₀ 𝓖₀ hG₀_sub] at hz_cl0
      obtain ⟨_, ⟨_, ⟨V, rfl⟩, rfl⟩, hzV⟩ := hz_cl0
      refine ⟨closure V.1, ⟨V.1, V.2, rfl⟩, ?_⟩
      rw [huEq V]
      exact closure_mono (Set.subset_iUnion (u V) F₀) hzV
    · rintro z ⟨_, ⟨V, hVG, rfl⟩, hzV⟩
      exact closure_mono (Set.subset_sUnion_of_mem hVG) hzV
  · intro U hUo hsub
    choose u hu_mem hu_sub using fun F : 𝓕 =>
      hU_base F (U ∩ W F) (hUo.inter (hW_open F))
        (fun x hx => ⟨hsub ⟨F.1, F.2, hx⟩, hW_sub F hx⟩)
    refine ⟨⋃ F : 𝓕, u F, ⟨u, fun F => ⟨hu_mem F, (hu_sub F).trans inter_subset_right⟩, rfl⟩, ?_⟩
    exact Set.iUnion_subset fun F => (hu_sub F).trans inter_subset_left

/-- In a stratifiable space, any closed discrete subset `D` (every subset of `D` is closed)
whose points each have `HasCPOuterBase` admits a CP open outer base `HasCPOuterBaseSet D`. -/
theorem hasCPOuterBaseSet_of_closed_discrete {X : Type} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) {D : Set X}
    (hD : ∀ S ⊆ D, IsClosed S)
    (hCP : ∀ x ∈ D, Defs.D_0001.HasCPOuterBase x) :
    HasCPOuterBaseSet D := by
  have : T1Space X := hStrat.1
  let 𝓕 : Set (Set X) := { S : Set X | ∃ x ∈ D, S = {x} }
  have hEq : ⋃₀ 𝓕 = D := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hyD, rfl⟩, rfl⟩; exact hyD
    · intro hxD; exact ⟨{x}, ⟨x, hxD, rfl⟩, rfl⟩
  rw [← hEq]
  refine hasCPOuterBaseSet_sUnion_discrete hStrat ?_ ?_ ?_
  · intro z
    by_cases hzD : z ∈ D
    · have hcl : IsClosed (D \ {z}) := hD (D \ {z}) Set.sdiff_subset
      refine ⟨(D \ {z})ᶜ, hcl.isOpen_compl, fun h => h.2 rfl, ?_⟩
      rintro _ ⟨x₁, hx₁D, rfl⟩ _ ⟨x₂, hx₂D, rfl⟩ ⟨y₁, hy₁c, rfl⟩ ⟨y₂, hy₂c, rfl⟩
      have h1 : y₁ = z := by by_contra hne; exact hy₁c ⟨hx₁D, hne⟩
      have h2 : y₂ = z := by by_contra hne; exact hy₂c ⟨hx₂D, hne⟩
      rw [h1, h2]
    · have hcl : IsClosed D := hD D Subset.rfl
      refine ⟨Dᶜ, hcl.isOpen_compl, hzD, ?_⟩
      rintro _ ⟨x₁, hx₁D, rfl⟩ _ _ ⟨y₁, hy₁c, rfl⟩ _
      exact (hy₁c hx₁D).elim
  · rintro _ ⟨x, _, rfl⟩
    exact isClosed_singleton
  · rintro _ ⟨x, hxD, rfl⟩
    exact (hasCPOuterBaseSet_singleton_iff x).mpr (hCP x hxD)

/-! ## Part 4: Compact sets with compact neighborhoods & structural `M₁` criteria -/

private lemma closurePreserving_range_antitone {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hanti : ∀ n, U (n + 1) ⊆ U n) :
    MSpace.ClosurePreserving (Set.range U) := by
  have hle : ∀ {m n : ℕ}, m ≤ n → U n ⊆ U m := by
    intro m n hmn
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hanti _).trans ih
  intro 𝓖 h𝓖
  by_cases hne : 𝓖.Nonempty
  · classical
    have hex : ∃ n : ℕ, U n ∈ 𝓖 := by
      obtain ⟨S, hSG⟩ := hne
      obtain ⟨n, rfl⟩ := h𝓖 hSG
      exact ⟨n, hSG⟩
    let n₀ : ℕ := Nat.find hex
    have hn₀ : U n₀ ∈ 𝓖 := Nat.find_spec hex
    have hEq : ⋃₀ 𝓖 = U n₀ := by
      apply Subset.antisymm
      · rintro x ⟨S, hSG, hxS⟩
        obtain ⟨n, rfl⟩ := h𝓖 hSG
        exact hle (Nat.find_min' hex hSG) hxS
      · exact Set.subset_sUnion_of_mem hn₀
    apply Subset.antisymm
    · rw [hEq]
      exact Set.subset_sUnion_of_mem ⟨U n₀, hn₀, rfl⟩
    · rintro x ⟨_, ⟨S, hSG, rfl⟩, hxS⟩
      exact closure_mono (Set.subset_sUnion_of_mem hSG) hxS
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp

/-- In any stratifiable space, a compact subset `K` that admits a compact neighborhood `C`
(with `K ⊆ interior C`) has a decreasing countable (hence CP) open outer base. -/
theorem hasCPOuterBaseSet_of_compact_with_compact_nhd (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) {K C : Set X}
    (hK : IsCompact K) (hC : IsCompact C) (hKC : K ⊆ interior C) :
    HasCPOuterBaseSet K := by
  have : T3Space X := (Proofs.L_0004.strat_to_m3 X hStrat).1
  have hKcl : IsClosed K := hK.isClosed
  obtain ⟨_, G₀, hG₀⟩ := hStrat
  obtain ⟨G, hG, hanti⟩ := exists_antitone_stratification hG₀
  let U : ℕ → Set X := fun n => G n K ∩ interior C
  have hU_anti : ∀ n, U (n + 1) ⊆ U n := fun n =>
    Set.inter_subset_inter_left (interior C) (hanti n K)
  refine ⟨Set.range U, ?_, closurePreserving_range_antitone U hU_anti, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨(hG.1 n K hKcl).inter isOpen_interior, fun x hx => ⟨hG.2.1 n K hKcl hx, hKC hx⟩⟩
  · intro W hWo hKW
    let S : ℕ → Set X := fun n => (C ∩ closure (G n K)) \ W
    have hS_closed : ∀ n, IsClosed (S n) := fun n =>
      (hC.isClosed.inter isClosed_closure).sdiff hWo
    have hS_anti : ∀ n, S (n + 1) ⊆ S n := fun n =>
      Set.sdiff_subset_sdiff_left (Set.inter_subset_inter_right C (closure_mono (hanti n K)))
    have hS_empty : (⋂ n, S n) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hx_cl : x ∈ ⋂ n, closure (G n K) := mem_iInter.mpr fun n => (mem_iInter.mp hx n).1.2
      rw [hG.2.2.1 K hKcl] at hx_cl
      exact (mem_iInter.mp hx 0).2 (hKW hx_cl)
    have hne_all : ∃ n, S n = ∅ := by
      by_contra hall
      push Not at hall
      have hnonempty : (⋂ n, S n).Nonempty :=
        IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS_anti hall
          (hC.of_isClosed_subset (hS_closed 0) (fun x hx => hx.1.1))
          hS_closed
      rw [hS_empty] at hnonempty
      exact Set.not_nonempty_empty hnonempty
    obtain ⟨n, hn⟩ := hne_all
    refine ⟨U n, ⟨n, rfl⟩, fun x hx => ?_⟩
    by_contra hxW
    have hxS : x ∈ S n := ⟨⟨interior_subset hx.2, subset_closure hx.1⟩, hxW⟩
    rw [hn] at hxS
    exact hxS

private lemma isM1_of_stratifiable_network_cp (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X)
    (𝓝_fam : ℕ → Set (Set X))
    (hN_closed : ∀ p, ∀ F ∈ 𝓝_fam p, IsClosed F)
    (hN_disc : ∀ p, IsDiscreteFam (𝓝_fam p))
    (hN_net : ∀ x : X, ∀ V : Set X, IsOpen V → x ∈ V → ∃ p, ∃ F ∈ 𝓝_fam p, x ∈ F ∧ F ⊆ V)
    (hN_cp : ∀ p, ∀ F ∈ 𝓝_fam p, HasCPOuterBaseSet F) :
    MSpace.IsM1 X := by
  have hT3 : T3Space X := (Proofs.L_0004.strat_to_m3 X hStrat).1
  choose W hW_open hW_sub hW_disc using
    fun p => stratifiable_discrete_open_expansion hStrat (hN_disc p) (hN_closed p)
  choose 𝓤 hU_open hU_cp hU_base using
    fun (p : ℕ) (F : 𝓝_fam p) => hN_cp p F.1 F.2
  let 𝓑' : ℕ → Set (Set X) := fun p =>
    { U : Set X | ∃ F : 𝓝_fam p, U ∈ 𝓤 p F ∧ U ⊆ W p F }
  have hB'_open : ∀ p, ∀ U ∈ 𝓑' p, IsOpen U := by
    rintro p U ⟨F, hUF, _⟩
    exact (hU_open p F U hUF).1
  have hB'_cp : ∀ p, MSpace.ClosurePreserving (𝓑' p) := by
    intro p 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      obtain ⟨O, hOo, hzO, hOuniq⟩ := hW_disc p z
      have hne_hit : ∃ U ∈ 𝓖, (O ∩ U).Nonempty := by
        obtain ⟨y, hyO, hyG⟩ := mem_closure_iff.mp hz O hOo hzO
        obtain ⟨U, hUG, hyU⟩ := hyG
        exact ⟨U, hUG, y, hyO, hyU⟩
      obtain ⟨U₀, hU₀G, hO_U₀⟩ := hne_hit
      obtain ⟨F₀, hU₀_mem, hU₀_sub⟩ := h𝓖 hU₀G
      have hO_W₀ : (O ∩ W p F₀).Nonempty := hO_U₀.mono (inter_subset_inter_right O hU₀_sub)
      let 𝓖₀ : Set (Set X) := { U ∈ 𝓖 | U ∈ 𝓤 p F₀ ∧ U ⊆ W p F₀ }
      have hG₀_sub : 𝓖₀ ⊆ 𝓤 p F₀ := fun _ h => h.2.1
      have hz_cl0 : z ∈ closure (⋃₀ 𝓖₀) := by
        rw [mem_closure_iff]
        intro V hVo hzV
        obtain ⟨y, hyOV, ⟨U, hUG, hyU⟩⟩ :=
          mem_closure_iff.mp hz (O ∩ V) (hOo.inter hVo) ⟨hzO, hzV⟩
        obtain ⟨F, hUF, hUW⟩ := h𝓖 hUG
        have hF_eq : F = F₀ :=
          hOuniq F F₀ ⟨y, hyOV.1, hUW hyU⟩ hO_W₀
        subst hF_eq
        exact ⟨y, hyOV.2, ⟨U, ⟨hUG, hUF, hUW⟩, hyU⟩⟩
      rw [hU_cp p F₀ 𝓖₀ hG₀_sub] at hz_cl0
      obtain ⟨C, ⟨U, hUG₀, rfl⟩, hzC⟩ := hz_cl0
      exact ⟨closure U, ⟨U, hUG₀.1, rfl⟩, hzC⟩
    · rintro z ⟨_, ⟨U, hUG, rfl⟩, hzU⟩
      exact closure_mono (Set.subset_sUnion_of_mem hUG) hzU
  refine ⟨hT3, ⋃ p, 𝓑' p, ?_, ⟨𝓑', hB'_cp, rfl⟩⟩
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U hU
    obtain ⟨p, hUp⟩ := mem_iUnion.mp hU
    exact hB'_open p U hUp
  · intro x V hxV hVo
    obtain ⟨p, F, hFp, hxF, hFV⟩ := hN_net x V hVo hxV
    let Fsub : 𝓝_fam p := ⟨F, hFp⟩
    have hopen_inter : IsOpen (V ∩ W p Fsub) := hVo.inter (hW_open p Fsub)
    have hF_inter : F ⊆ V ∩ W p Fsub := fun y hy => ⟨hFV hy, hW_sub p Fsub hy⟩
    obtain ⟨U, hUF, hU_sub⟩ := hU_base p Fsub (V ∩ W p Fsub) hopen_inter hF_inter
    refine ⟨U, mem_iUnion.mpr ⟨p, ⟨Fsub, hUF, hU_sub.trans inter_subset_right⟩⟩,
      (hU_open p Fsub U hUF).2 hxF, hU_sub.trans inter_subset_left⟩

/-- Every σ-closed-discrete stratifiable space (e.g. any countable stratifiable space or
scattered stratifiable space of finite Cantor–Bendixson rank) whose points each have
`HasCPOuterBase` is `M₁`. -/
theorem isM1_of_stratifiable_sigma_closed_discrete (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X)
    (D : ℕ → Set X)
    (hD_disc : ∀ n, ∀ S ⊆ D n, IsClosed S)
    (hD_cover : (⋃ n, D n) = Set.univ)
    (hCP : ∀ x : X, Defs.D_0001.HasCPOuterBase x) :
    MSpace.IsM1 X := by
  have : T1Space X := hStrat.1
  let 𝓝_fam : ℕ → Set (Set X) := fun n => { S : Set X | ∃ x ∈ D n, S = {x} }
  refine isM1_of_stratifiable_network_cp X hStrat 𝓝_fam ?_ ?_ ?_ ?_
  · rintro n _ ⟨x, _, rfl⟩
    exact isClosed_singleton
  · intro n z
    by_cases hz : z ∈ D n
    · have hcl : IsClosed (D n \ {z}) := hD_disc n (D n \ {z}) Set.sdiff_subset
      refine ⟨(D n \ {z})ᶜ, hcl.isOpen_compl, fun h => h.2 rfl, ?_⟩
      rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ ⟨y₁, hy₁c, rfl⟩ ⟨y₂, hy₂c, rfl⟩
      have h1 : y₁ = z := by by_contra hne; exact hy₁c ⟨hx₁, hne⟩
      have h2 : y₂ = z := by by_contra hne; exact hy₂c ⟨hx₂, hne⟩
      rw [h1, h2]
    · have hcl : IsClosed (D n) := hD_disc n (D n) Subset.rfl
      refine ⟨(D n)ᶜ, hcl.isOpen_compl, hz, ?_⟩
      rintro _ ⟨x₁, hx₁, rfl⟩ _ _ ⟨y₁, hy₁c, rfl⟩ _
      exact (hy₁c hx₁).elim
  · intro x V _ hxV
    have hxU : x ∈ (⋃ n, D n) := by rw [hD_cover]; trivial
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hxU
    exact ⟨n, {x}, ⟨x, hxn, rfl⟩, rfl, Set.singleton_subset_iff.mpr hxV⟩
  · rintro n _ ⟨x, _, rfl⟩
    exact (hasCPOuterBaseSet_singleton_iff x).mpr (hCP x)

private lemma closurePreserving_image_closure {X : Type*} [TopologicalSpace X]
    {𝓑 : Set (Set X)} (hcp : MSpace.ClosurePreserving 𝓑) :
    MSpace.ClosurePreserving (closure '' 𝓑) := by
  intro 𝓖 h𝓖
  let 𝓗 : Set (Set X) := { B ∈ 𝓑 | closure B ∈ 𝓖 }
  have hH_sub : 𝓗 ⊆ 𝓑 := fun _ h => h.1
  have h1 : ⋃₀ 𝓖 ⊆ closure (⋃₀ 𝓗) := by
    rintro x ⟨C, hCG, hxC⟩
    obtain ⟨B, hB, rfl⟩ := h𝓖 hCG
    exact closure_mono (Set.subset_sUnion_of_mem (⟨hB, hCG⟩ : B ∈ 𝓗)) hxC
  have h2 : ⋃₀ (closure '' 𝓗) ⊆ ⋃₀ (closure '' 𝓖) := by
    rintro x ⟨C, ⟨B, ⟨_, hBG⟩, rfl⟩, hxC⟩
    refine ⟨closure (closure B), ⟨closure B, hBG, rfl⟩, ?_⟩
    rwa [closure_closure]
  apply Subset.antisymm
  · calc closure (⋃₀ 𝓖) ⊆ closure (closure (⋃₀ 𝓗)) := closure_mono h1
      _ = closure (⋃₀ 𝓗) := closure_closure
      _ = ⋃₀ (closure '' 𝓗) := hcp 𝓗 hH_sub
      _ ⊆ ⋃₀ (closure '' 𝓖) := h2
  · rintro x ⟨_, ⟨C, hCG, rfl⟩, hxC⟩
    exact closure_mono (Set.subset_sUnion_of_mem hCG) hxC

private lemma stratifiable_has_sigma_discrete_closed_network (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) :
    ∃ 𝓝_fam : ℕ → Set (Set X),
      (∀ p, ∀ F ∈ 𝓝_fam p, IsClosed F) ∧
      (∀ p, IsDiscreteFam (𝓝_fam p)) ∧
      (∀ x : X, ∀ V : Set X, IsOpen V → x ∈ V → ∃ p, ∃ F ∈ 𝓝_fam p, x ∈ F ∧ F ⊆ V) := by
  have hM3 : MSpace.IsM3 X := Proofs.L_0004.strat_to_m3 X hStrat
  have hM2 : MSpace.IsM2 X := Proofs.L_0008.main X hM3
  obtain ⟨hT3, 𝓑, hQB, 𝓑', hcp, rfl⟩ := hM2
  have : T3Space X := hT3
  obtain ⟨_, G, hGo, hGs, hGi, hGm⟩ := hStrat
  let K' : ℕ → Set (Set X) := fun m => closure '' 𝓑' m
  have hK_closed : ∀ m, ∀ K ∈ K' m, IsClosed K := by
    rintro m _ ⟨B, _, rfl⟩; exact isClosed_closure
  have hK_cp : ∀ m, MSpace.ClosurePreserving (K' m) := fun m =>
    closurePreserving_image_closure (hcp m)
  let C : ℕ → X → Set X := fun m x => ⋂ K ∈ { K ∈ K' m | x ∈ K }, K
  let D : ℕ → X → Set X := fun m x => ⋃ K ∈ { K ∈ K' m | x ∉ K }, K
  have hC_closed : ∀ m x, IsClosed (C m x) := fun m x =>
    isClosed_biInter fun K hK => hK_closed m K hK.1
  have hD_closed : ∀ m x, IsClosed (D m x) := by
    intro m x
    have hEq : D m x = ⋃₀ { K ∈ K' m | x ∉ K } := by ext y; simp [D]
    rw [hEq, ← closure_eq_iff_isClosed, hK_cp m { K ∈ K' m | x ∉ K } (fun _ h => h.1)]
    ext y
    constructor
    · rintro ⟨_, ⟨K, hK, rfl⟩, hy⟩
      rw [(hK_closed m K hK.1).closure_eq] at hy
      exact ⟨K, hK, hy⟩
    · rintro ⟨K, hK, hy⟩
      exact ⟨closure K, ⟨K, hK, rfl⟩, subset_closure hy⟩
  let A : ℕ → ℕ → X → Set X := fun m k x => C m x \ G k (D m x)
  let 𝓝_fam : ℕ → Set (Set X) := fun p => Set.range (A (Nat.unpair p).1 (Nat.unpair p).2)
  refine ⟨𝓝_fam, ?_, ?_, ?_⟩
  · rintro p _ ⟨x, rfl⟩
    exact (hC_closed _ x).sdiff (hGo _ _ (hD_closed _ x))
  · intro p z
    let m := (Nat.unpair p).1
    let k := (Nat.unpair p).2
    let W : Set X := (D m z)ᶜ ∩ G k {z}
    have hWo : IsOpen W := (hD_closed m z).isOpen_compl.inter (hGo k {z} isClosed_singleton)
    have hzW : z ∈ W := by
      refine ⟨?_, hGs k {z} isClosed_singleton rfl⟩
      rintro hzD
      obtain ⟨K, hK, hzK⟩ := mem_iUnion₂.mp hzD
      exact hK.2 hzK
    refine ⟨W, hWo, hzW, ?_⟩
    rintro _ ⟨x₁, rfl⟩ _ ⟨x₂, rfl⟩ ⟨y₁, hy₁W, hy₁A⟩ ⟨y₂, hy₂W, hy₂A⟩
    have hsame : ∀ x y, y ∈ W → y ∈ A m k x → (∀ K ∈ K' m, x ∈ K ↔ z ∈ K) := by
      intro x y hyW hyA K hKm
      constructor
      · intro hxK
        have hyK : y ∈ K := mem_iInter₂.mp hyA.1 K ⟨hKm, hxK⟩
        by_contra hzK
        exact hyW.1 (mem_iUnion₂.mpr ⟨K, ⟨hKm, hzK⟩, hyK⟩)
      · intro hzK
        by_contra hxK
        have hsub : ({z} : Set X) ⊆ D m x := by
          intro w hw
          rw [mem_singleton_iff.mp hw]
          exact mem_iUnion₂.mpr ⟨K, ⟨hKm, hxK⟩, hzK⟩
        exact hyA.2 (hGm k {z} (D m x) isClosed_singleton (hD_closed m x) hsub hyW.2)
    have h1 := hsame x₁ y₁ hy₁W hy₁A
    have h2 := hsame x₂ y₂ hy₂W hy₂A
    have hCeq : C m x₁ = C m x₂ := by
      ext w
      simp only [C, mem_iInter, mem_ofPred_eq]
      exact ⟨fun h K ⟨hKm, hx₂K⟩ => h K ⟨hKm, (h1 K hKm).mpr ((h2 K hKm).mp hx₂K)⟩,
             fun h K ⟨hKm, hx₁K⟩ => h K ⟨hKm, (h2 K hKm).mpr ((h1 K hKm).mp hx₁K)⟩⟩
    have hDeq : D m x₁ = D m x₂ := by
      ext w
      simp only [D, mem_iUnion, mem_ofPred_eq]
      constructor
      · rintro ⟨K, ⟨hKm, hx₁K⟩, hwK⟩
        exact ⟨K, ⟨hKm, fun hx₂K => hx₁K ((h1 K hKm).mpr ((h2 K hKm).mp hx₂K))⟩, hwK⟩
      · rintro ⟨K, ⟨hKm, hx₂K⟩, hwK⟩
        exact ⟨K, ⟨hKm, fun hx₁K => hx₂K ((h2 K hKm).mpr ((h1 K hKm).mp hx₁K))⟩, hwK⟩
    show C m x₁ \ G k (D m x₁) = C m x₂ \ G k (D m x₂)
    rw [hCeq, hDeq]
  · intro x V hVo hxV
    obtain ⟨t, ht, htc, htV⟩ := exists_mem_nhds_isClosed_subset (hVo.mem_nhds hxV)
    obtain ⟨B, hB, hxB, hBt⟩ :=
      hQB x (interior t) isOpen_interior (mem_interior_iff_mem_nhds.mpr ht)
    obtain ⟨m, hBm⟩ := mem_iUnion.mp hB
    have hclB_mem : closure B ∈ K' m := ⟨B, hBm, rfl⟩
    have hx_clB : x ∈ closure B := subset_closure (interior_subset hxB)
    have hclB_sub : closure B ⊆ V := (closure_minimal (hBt.trans interior_subset) htc).trans htV
    have hx_not_D : x ∉ D m x := by
      intro hxD
      obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hxD
      exact hK.2 hxK
    rw [← hGi (D m x) (hD_closed m x), mem_iInter] at hx_not_D
    push Not at hx_not_D
    obtain ⟨k, hk⟩ := hx_not_D
    refine ⟨Nat.pair m k, A m k x, ?_, ?_, ?_⟩
    · simp only [𝓝_fam, Nat.unpair_pair]
      exact ⟨x, rfl⟩
    · refine ⟨?_, fun hxG => hk (subset_closure hxG)⟩
      exact mem_iInter₂.mpr fun K hK => hK.2
    · intro y hy
      exact hclB_sub (mem_iInter₂.mp hy.1 (closure B) ⟨hclB_mem, hx_clB⟩)

/-- If `X` is stratifiable, every point `z ≠ y₀` admits a compact neighborhood in `X`,
and `y₀` has a CP open outer base, then `X` is `M₁`.
Contrapositively: any non-`M₁` stratifiable space whose punctured complement `X \ {y₀}`
is locally compact automatically witnesses `¬ HasCPOuterBase y₀`! -/
theorem isM1_of_stratifiable_locallyCompact_compl (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) (y₀ : X)
    (hLC : ∀ z : X, z ≠ y₀ → ∃ C : Set X, IsCompact C ∧ z ∈ interior C)
    (hCP₀ : Defs.D_0001.HasCPOuterBase y₀) :
    MSpace.IsM1 X := by
  have : T1Space X := hStrat.1
  obtain ⟨𝓝_fam, hN_closed, hN_disc, hN_net⟩ :=
    stratifiable_has_sigma_discrete_closed_network X hStrat
  let 𝓝' : ℕ → Set (Set X) := fun p =>
    match p with
    | 0 => {{y₀}}
    | q + 1 => { F ∈ 𝓝_fam q | ∃ C : Set X, IsCompact C ∧ F ⊆ interior C }
  refine isM1_of_stratifiable_network_cp X hStrat 𝓝' ?_ ?_ ?_ ?_
  · intro p F hF
    cases p with
    | zero =>
      rw [Set.mem_singleton_iff.mp hF]
      exact isClosed_singleton
    | succ q => exact hN_closed q F hF.1
  · intro p z
    cases p with
    | zero =>
      refine ⟨Set.univ, isOpen_univ, trivial, fun F₁ hF₁ F₂ hF₂ _ _ => ?_⟩
      rw [Set.mem_singleton_iff.mp hF₁, Set.mem_singleton_iff.mp hF₂]
    | succ q =>
      obtain ⟨W, hWo, hzW, hWuniq⟩ := hN_disc q z
      exact ⟨W, hWo, hzW, fun F₁ hF₁ F₂ hF₂ h1 h2 => hWuniq F₁ hF₁.1 F₂ hF₂.1 h1 h2⟩
  · intro x V hVo hxV
    by_cases hx : x = y₀
    · subst hx
      exact ⟨0, {x}, rfl, rfl, Set.singleton_subset_iff.mpr hxV⟩
    · obtain ⟨C, hCc, hxC⟩ := hLC x hx
      obtain ⟨q, F, hFq, hxF, hFsub⟩ :=
        hN_net x (V ∩ interior C) (hVo.inter isOpen_interior) ⟨hxV, hxC⟩
      exact ⟨q + 1, F, ⟨hFq, C, hCc, hFsub.trans inter_subset_right⟩,
        hxF, hFsub.trans inter_subset_left⟩
  · intro p F hF
    cases p with
    | zero =>
      rw [Set.mem_singleton_iff.mp hF]
      exact (hasCPOuterBaseSet_singleton_iff y₀).mpr hCP₀
    | succ q =>
      obtain ⟨hFq, C, hCc, hFC⟩ := hF
      have hFcomp : IsCompact F :=
        hCc.of_isClosed_subset (hN_closed q F hFq) (hFC.trans interior_subset)
      exact hasCPOuterBaseSet_of_compact_with_compact_nhd X hStrat hFcomp hCc hFC

end Research.Ito1985Criteria
