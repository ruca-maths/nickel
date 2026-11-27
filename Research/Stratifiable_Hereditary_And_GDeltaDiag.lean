import Mathlib.Topology.GDelta.Basic
import Targets.Defs
import Proofs.L_0003
import Proofs.L_0004
import Proofs.L_0005
import Proofs.L_0006
import Proofs.L_0008

/-!
# Hereditary Properties and $G_\delta$-Diagonal of Stratifiable / $M_2$ / $M_3$ Spaces

This standalone module formalizes the hereditary permanence and diagonal theorems for
stratifiable ($M_3$) and $M_2$ spaces (Borges 1966; Gruenhage 1976; Junnila 1978):

1. **`isStratifiable_subtype`**: Every subspace `S : Set X` of a stratifiable space is
   stratifiable (Borges 1966).
2. **`isM3_subtype`** & **`isM2_subtype`**: Every subspace of an `M₃` (resp. `M₂`) space
   is `M₃` (resp. `M₂`), contrasting sharply with `M₁` where hereditary `M₁` is equivalent
   to Ceder's open problem `Tinf`.
3. **`paracompact_subtype_of_isStratifiable`** & **`perfectlyNormal_subtype_of_isStratifiable`**:
   Every stratifiable space is hereditarily paracompact and hereditarily perfectly normal.
4. **`gDelta_diagonal_of_isStratifiable`**: Every stratifiable space has a $G_\delta$-diagonal
   `IsGδ (Set.diagonal X)` (via finite-product stratifiability + `Proofs.L_0006`).
-/

namespace Research.StratifiableHereditary

open Set Topology TopologicalSpace

/-! ## Part 1: Arbitrary subspaces of stratifiable, `M₃`, and `M₂` spaces -/

/-- Borges (1966): Every subspace `S : Set X` of a stratifiable space `X` is stratifiable. -/
theorem isStratifiable_subtype {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) (S : Set X) :
    MSpace.IsStratifiable S := by
  have : T1Space X := hStrat.1
  obtain ⟨_, G, hGo, hGs, hGi, hGm⟩ := hStrat
  let GS : ℕ → Set S → Set S := fun n H =>
    (Subtype.val : S → X) ⁻¹' G n (closure ((Subtype.val : S → X) '' H))
  refine ⟨inferInstance, GS, ?_, ?_, ?_, ?_⟩
  · intro n H _
    exact (hGo n _ isClosed_closure).preimage continuous_subtype_val
  · intro n H _ x hxH
    exact hGs n _ isClosed_closure (subset_closure ⟨x, hxH, rfl⟩)
  · intro H hH
    apply Subset.antisymm
    · intro x hx
      have hx_cl : x.1 ∈ ⋂ n, closure (G n (closure ((Subtype.val : S → X) '' H))) := by
        refine mem_iInter.mpr fun n => ?_
        have hxn : x ∈ closure (GS n H) := mem_iInter.mp hx n
        have := continuous_subtype_val.closure_preimage_subset
          (G n (closure ((Subtype.val : S → X) '' H))) hxn
        exact this
      rw [hGi _ isClosed_closure] at hx_cl
      obtain ⟨C, hCcl, hCEq⟩ := isClosed_induced_iff.mp hH
      have hsub : (Subtype.val : S → X) '' H ⊆ C := by
        rintro _ ⟨y, hyH, rfl⟩
        rw [← hCEq] at hyH
        exact hyH
      have hxC : x.1 ∈ C := closure_minimal hsub hCcl hx_cl
      rw [← hCEq]
      exact hxC
    · intro x hxH
      refine mem_iInter.mpr fun n => subset_closure ?_
      exact hGs n _ isClosed_closure (subset_closure ⟨x, hxH, rfl⟩)
  · intro n H K _ _ hHK
    exact preimage_mono (hGm n _ _ isClosed_closure isClosed_closure (closure_mono (image_mono hHK)))

/-- Every subspace of an `M₃` space is `M₃`. -/
theorem isM3_subtype {X : Type} [TopologicalSpace X]
    (hM3 : MSpace.IsM3 X) (S : Set X) : MSpace.IsM3 S :=
  Proofs.L_0004.strat_to_m3 S (isStratifiable_subtype (Proofs.L_0004.m3_to_strat X hM3) S)

/-- Every subspace of an `M₂` space is `M₂`. -/
theorem isM2_subtype {X : Type} [TopologicalSpace X]
    (hM2 : MSpace.IsM2 X) (S : Set X) : MSpace.IsM2 S :=
  Proofs.L_0008.main S (isM3_subtype (Proofs.L_0003.main X hM2) S)

/-- Every stratifiable space is hereditarily paracompact. -/
theorem paracompact_subtype_of_isStratifiable {X : Type} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) (S : Set X) : ParacompactSpace S :=
  Proofs.L_0005.main S (isStratifiable_subtype hStrat S)

/-- Every stratifiable space is hereditarily perfectly normal. -/
theorem perfectlyNormal_subtype_of_isStratifiable {X : Type} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) (S : Set X) : MSpace.IsPerfectlyNormal S :=
  Proofs.L_0006.main S (isStratifiable_subtype hStrat S)

/-! ## Part 2: Every stratifiable space has a $G_\delta$-diagonal -/

private lemma exists_antitone_stratification {X : Type*} [TopologicalSpace X]
    {G : ℕ → Set X → Set X} (hG : MSpace.IsStratification G) :
    ∃ G' : ℕ → Set X → Set X,
      MSpace.IsStratification G' ∧ (∀ n H, G' (n + 1) H ⊆ G' n H) := by
  rcases hG with ⟨hGo, hGs, hGi, hGm⟩
  let G' : ℕ → Set X → Set X := fun n H => ⋂ i ∈ Finset.range (n + 1), G i H
  refine ⟨G', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n H hH; exact isOpen_biInter_finset fun i _ => hGo i H hH
  · intro n H hH x hx; exact mem_iInter₂.mpr fun i _ => hGs i H hH hx
  · intro H hH
    apply Subset.antisymm
    · intro x hx
      rw [← hGi H hH]
      refine mem_iInter.mpr fun n => closure_mono (fun y hy =>
        mem_iInter₂.mp hy n (Finset.mem_range.mpr (Nat.lt_succ_self n))) (mem_iInter.mp hx n)
    · intro x hx
      exact mem_iInter.mpr fun n => subset_closure (mem_iInter₂.mpr fun i _ => hGs i H hH hx)
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

private lemma isStratifiable_prod_self {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) : MSpace.IsStratifiable (X × X) := by
  have : T1Space X := hStrat.1
  obtain ⟨_, G₀, hG₀⟩ := hStrat
  obtain ⟨G, hG, hanti⟩ := exists_antitone_stratification hG₀
  let GP : ℕ → Set (X × X) → Set (X × X) := fun n H => ⋃ p ∈ H, G n {p.1} ×ˢ G n {p.2}
  refine ⟨inferInstance, GP, ?_, ?_, ?_, ?_⟩
  · intro n H _
    exact isOpen_biUnion fun p _ =>
      (hG.1 n {p.1} isClosed_singleton).prod (hG.1 n {p.2} isClosed_singleton)
  · intro n H _ p hpH
    exact mem_iUnion₂.mpr ⟨p, hpH, hG.2.1 n _ isClosed_singleton rfl, hG.2.1 n _ isClosed_singleton rfl⟩
  · intro H hH
    apply Subset.antisymm
    · intro ⟨x, y⟩ hxy
      by_contra hnot
      obtain ⟨U, V, hUo, hVo, hxU, hyV, hUV⟩ :=
        isOpen_prod_iff.mp hH.isOpen_compl x y hnot
      have hUc_cl : IsClosed Uᶜ := hUo.isClosed_compl
      have hVc_cl : IsClosed Vᶜ := hVo.isClosed_compl
      have hxUc : x ∉ Uᶜ := fun h => h hxU
      have hyVc : y ∉ Vᶜ := fun h => h hyV
      rw [← hG.2.2.1 Uᶜ hUc_cl, mem_iInter] at hxUc
      rw [← hG.2.2.1 Vᶜ hVc_cl, mem_iInter] at hyVc
      push Not at hxUc hyVc
      obtain ⟨n₁, hn₁⟩ := hxUc
      obtain ⟨n₂, hn₂⟩ := hyVc
      let n := max n₁ n₂
      let W₁ : Set X := (closure (G n Uᶜ))ᶜ
      let W₂ : Set X := (closure (G n Vᶜ))ᶜ
      have hxW₁ : x ∈ W₁ := fun h => hn₁ (closure_mono (antitone_le hanti (le_max_left _ _) Uᶜ) h)
      have hyW₂ : y ∈ W₂ := fun h => hn₂ (closure_mono (antitone_le hanti (le_max_right _ _) Vᶜ) h)
      have hWo : IsOpen (W₁ ×ˢ W₂) := isClosed_closure.isOpen_compl.prod isClosed_closure.isOpen_compl
      have hcl : (x, y) ∈ closure (GP n H) := mem_iInter.mp hxy n
      obtain ⟨⟨a, b⟩, ⟨haW₁, hbW₂⟩, habGP⟩ := mem_closure_iff.mp hcl (W₁ ×ˢ W₂) hWo ⟨hxW₁, hyW₂⟩
      obtain ⟨⟨p₁, p₂⟩, hpH, haGp, hbGp⟩ := mem_iUnion₂.mp habGP
      have hp_not_UV : (p₁, p₂) ∉ U ×ˢ V := fun h => hUV h hpH
      by_cases hp₁ : p₁ ∈ U
      · have hp₂ : p₂ ∈ Vᶜ := fun h => hp_not_UV ⟨hp₁, h⟩
        have hbG : b ∈ G n Vᶜ := hG.2.2.2 n {p₂} Vᶜ isClosed_singleton hVc_cl
          (Set.singleton_subset_iff.mpr hp₂) hbGp
        exact hbW₂ (subset_closure hbG)
      · have haG : a ∈ G n Uᶜ := hG.2.2.2 n {p₁} Uᶜ isClosed_singleton hUc_cl
          (Set.singleton_subset_iff.mpr hp₁) haGp
        exact haW₁ (subset_closure haG)
    · intro p hpH
      refine mem_iInter.mpr fun n => subset_closure ?_
      exact mem_iUnion₂.mpr ⟨p, hpH, hG.2.1 n _ isClosed_singleton rfl, hG.2.1 n _ isClosed_singleton rfl⟩
  · intro n H K _ _ hHK
    exact biUnion_subset_biUnion_left hHK

/-- Every stratifiable space has a $G_\delta$-diagonal `IsGδ (Set.diagonal X)`. -/
theorem gDelta_diagonal_of_isStratifiable (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) : IsGδ (Set.diagonal X) := by
  have : T3Space X := (Proofs.L_0004.strat_to_m3 X hStrat).1
  have hProd : MSpace.IsStratifiable (X × X) := isStratifiable_prod_self hStrat
  exact (Proofs.L_0006.main (X × X) hProd).2 (Set.diagonal X) isClosed_diagonal

end Research.StratifiableHereditary
