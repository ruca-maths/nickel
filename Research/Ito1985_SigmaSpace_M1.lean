import Mathlib.Data.Nat.Pairing
import Targets.Defs
import Targets.Goals
import Defs.D_0001
import Specs.L_0020
import Proofs.L_0004
import Proofs.L_0008

/-!
# Heath (1969), Collectionwise Normality, Ito (1985), and `¬ L_0020 → Tinf`

This standalone module formalizes four foundational theorems of $M_3 / M_1$ space theory:

1. **Monotone normality & collectionwise normality of stratifiable spaces**
   (`stratifiable_discrete_open_expansion`):
   Every discrete family of closed sets in a stratifiable space admits a discrete
   open expansion `{ W F | F ∈ 𝓕 }` with `F ⊆ W F`.

2. **Heath (1969): Every stratifiable space is a $\sigma$-space**
   (`stratifiable_has_sigma_discrete_closed_network`):
   Every stratifiable space admits a $\sigma$-discrete closed network
   `⋃ p : ℕ, 𝓝_fam p`, proved directly from `Proofs.L_0008` (`M₃ ⇒ M₂`) and a
   stratification via `A m k x := C_m(x) \ G_k(D_m(x))`.

3. **Ito (1985, closed-set form)** (`isM1_of_stratifiable_and_closed_hasCPOuterBase`):
   If `X` is stratifiable and every closed subset `F ⊆ X` has a closure-preserving
   open outer base, then `X` is `M₁`.

4. **Global Converse of `L0020_imp_not_Tinf`** (`not_L0020_imp_Tinf`):
   Combining (3) with the collapse quotient `X / F` (which preserves stratifiability
   and reduces `HasCPOuterBaseSet F` to `HasCPOuterBase (none : X / F)`), we prove:
   - `¬ Specs.L_0020.stmt → MSpace.Goals.Tinf_M3_imp_M1`.
   Together with `Research.ChenWangBoxFanEquiv.L0020_imp_not_Tinf`, this establishes
   the exact ZFC equivalence `MSpace.Goals.Tinf_M3_imp_M1 ↔ ¬ Specs.L_0020.stmt`
   (and hence `↔ ¬ Specs.L_0030.stmt ↔ ¬ Specs.L_0031.stmt`).
-/

namespace Research.Ito1985

open Set Topology TopologicalSpace

/-! ## Part 1: Basic definitions (discrete families, closed-set CP outer bases) -/

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

/-- Any subfamily of a discrete family of closed sets has a closed union. -/
theorem isClosed_sUnion_of_isDiscreteFam {X : Type*} [TopologicalSpace X]
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

/-! ## Part 2: Decreasing stratification, monotone normality, and collectionwise normality -/

/-- From any stratification `G`, obtain a decreasing stratification `G' n H = ⋂ i ≤ n, G i H`. -/
theorem exists_antitone_stratification {X : Type*} [TopologicalSpace X]
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

/-- Monotone normality operator `Hsep G A B = ⋃ n, (G n A \ closure (G n B))` from a
decreasing stratification `G`. -/
def Hsep {X : Type*} [TopologicalSpace X] (G : ℕ → Set X → Set X) (A B : Set X) : Set X :=
  ⋃ n : ℕ, G n A \ closure (G n B)

theorem isOpen_Hsep {X : Type*} [TopologicalSpace X] {G : ℕ → Set X → Set X}
    (hG : MSpace.IsStratification G) {A B : Set X} (hA : IsClosed A) :
    IsOpen (Hsep G A B) :=
  isOpen_iUnion fun n => (hG.1 n A hA).sdiff isClosed_closure

theorem subset_Hsep {X : Type*} [TopologicalSpace X] {G : ℕ → Set X → Set X}
    (hG : MSpace.IsStratification G) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) : A ⊆ Hsep G A B := by
  intro x hxA
  have hxB : x ∉ B := Set.disjoint_left.mp hdisj hxA
  rw [← hG.2.2.1 B hB, mem_iInter] at hxB
  push Not at hxB
  obtain ⟨n, hn⟩ := hxB
  exact mem_iUnion.mpr ⟨n, hG.2.1 n A hA hxA, hn⟩

theorem disjoint_Hsep {X : Type*} [TopologicalSpace X] {G : ℕ → Set X → Set X}
    (hanti : ∀ n H, G (n + 1) H ⊆ G n H) (A B : Set X) :
    Disjoint (Hsep G A B) (Hsep G B A) := by
  rw [Set.disjoint_left]
  intro x hxAB hxBA
  obtain ⟨n, hxnA, hxnB⟩ := mem_iUnion.mp hxAB
  obtain ⟨m, hxmB, hxmA⟩ := mem_iUnion.mp hxBA
  rcases le_total n m with hnm | hmn
  · exact hxnB (subset_closure (antitone_le hanti hnm B hxmB))
  · exact hxmA (subset_closure (antitone_le hanti hmn A hxnA))

theorem Hsep_mono {X : Type*} [TopologicalSpace X] {G : ℕ → Set X → Set X}
    (hG : MSpace.IsStratification G) {A₁ A₂ B₁ B₂ : Set X}
    (hA₁ : IsClosed A₁) (hA₂ : IsClosed A₂) (hB₁ : IsClosed B₁) (hB₂ : IsClosed B₂)
    (hA : A₁ ⊆ A₂) (hB : B₂ ⊆ B₁) :
    Hsep G A₁ B₁ ⊆ Hsep G A₂ B₂ := by
  intro x hx
  obtain ⟨n, h1, h2⟩ := mem_iUnion.mp hx
  refine mem_iUnion.mpr ⟨n, hG.2.2.2 n A₁ A₂ hA₁ hA₂ hA h1, ?_⟩
  intro hc
  exact h2 (closure_mono (hG.2.2.2 n B₂ B₁ hB₂ hB₁ hB) hc)

/-- Collectionwise normality of stratifiable spaces: every discrete family `𝓕` of closed sets
has a discrete open expansion `W : 𝓕 → Set X` with `F.1 ⊆ W F`. -/
theorem stratifiable_discrete_open_expansion {X : Type*} [TopologicalSpace X]
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

/-! ## Part 3: Heath (1969) — Every stratifiable space is a σ-space -/

/-- Helper: closure-preserving image under `closure` preserves `ClosurePreserving`. -/
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

/-- Heath (1969): Every stratifiable space has a σ-discrete closed network. -/
theorem stratifiable_has_sigma_discrete_closed_network (X : Type) [TopologicalSpace X]
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
    rintro m _ ⟨B, _, rfl⟩
    exact isClosed_closure
  have hK_cp : ∀ m, MSpace.ClosurePreserving (K' m) := fun m =>
    closurePreserving_image_closure (hcp m)
  let C : ℕ → X → Set X := fun m x => ⋂ K ∈ { K ∈ K' m | x ∈ K }, K
  let D : ℕ → X → Set X := fun m x => ⋃ K ∈ { K ∈ K' m | x ∉ K }, K
  have hC_closed : ∀ m x, IsClosed (C m x) := fun m x =>
    isClosed_biInter fun K hK => hK_closed m K hK.1
  have hD_closed : ∀ m x, IsClosed (D m x) := by
    intro m x
    have hEq : D m x = ⋃₀ { K ∈ K' m | x ∉ K } := by
      ext y; simp [D]
    rw [hEq, ← closure_eq_iff_isClosed]
    rw [hK_cp m { K ∈ K' m | x ∉ K } (fun _ h => h.1)]
    ext y
    constructor
    · rintro ⟨_, ⟨K, hK, rfl⟩, hy⟩
      rw [(hK_closed m K hK.1).closure_eq] at hy
      exact ⟨K, hK, hy⟩
    · rintro ⟨K, hK, hy⟩
      refine ⟨closure K, ⟨K, hK, rfl⟩, subset_closure hy⟩
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
        have hyG : y ∈ G k (D m x) := hGm k {z} (D m x) isClosed_singleton (hD_closed m x) hsub hyW.2
        exact hyA.2 hyG
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

/-! ## Part 4: Ito (1985, closed-set form) — Stratifiable + closed CP outer bases ⇒ M₁ -/

/-- Ito (1985, closed-set form): If `X` is stratifiable and every closed subset of `X` has a
closure-preserving open outer base, then `X` is `M₁`. -/
theorem isM1_of_stratifiable_and_closed_hasCPOuterBase (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X)
    (hCP : ∀ F : Set X, IsClosed F → HasCPOuterBaseSet F) :
    MSpace.IsM1 X := by
  have hT3 : T3Space X := (Proofs.L_0004.strat_to_m3 X hStrat).1
  obtain ⟨𝓝_fam, hN_closed, hN_disc, hN_net⟩ :=
    stratifiable_has_sigma_discrete_closed_network X hStrat
  choose W hW_open hW_sub hW_disc using
    fun p => stratifiable_discrete_open_expansion hStrat (hN_disc p) (hN_closed p)
  choose 𝓤 hU_open hU_cp hU_base using
    fun (p : ℕ) (F : 𝓝_fam p) => hCP F.1 (hN_closed p F.1 F.2)
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

/-! ## Part 5: Collapse quotient `X / F` and `¬ Specs.L_0020.stmt → Tinf` -/

/-- Collapse quotient `X / F`: points outside `F` plus a single collapsed point `none`. -/
abbrev CollapseQuot (X : Type) (F : Set X) : Type := Option { x : X // x ∉ F }

/-- Quotient projection `X → X / F` sending `F` to `none` and `x ∉ F` to `some ⟨x, hx⟩`. -/
noncomputable def cProj {X : Type} (F : Set X) (x : X) : CollapseQuot X F :=
  open Classical in
  if hx : x ∈ F then none else some ⟨x, hx⟩

/-- Quotient topology on `CollapseQuot X F` coinduced by `cProj F`. -/
@[instance_reducible]
noncomputable def collapseQuotTop {X : Type} [TopologicalSpace X] (F : Set X) :
    TopologicalSpace (CollapseQuot X F) :=
  TopologicalSpace.coinduced (cProj F) inferInstance

private lemma cProj_eq_none_iff {X : Type} {F : Set X} {x : X} :
    cProj F x = none ↔ x ∈ F := by
  classical
  unfold cProj
  split_ifs with hx
  · exact ⟨fun _ => hx, fun _ => rfl⟩
  · exact ⟨fun h => h.elim, fun h => (hx h).elim⟩

private lemma cProj_surjective {X : Type} {F : Set X} (hFne : F.Nonempty) :
    Function.Surjective (cProj F) := by
  classical
  rintro (_ | ⟨x, hx⟩)
  · obtain ⟨x₀, hx₀⟩ := hFne
    exact ⟨x₀, by simp [cProj, hx₀]⟩
  · exact ⟨x, by simp [cProj, hx]⟩

private lemma cProj_preimage_image_of_closed {X : Type} [TopologicalSpace X]
    {F : Set X} {C : Set (CollapseQuot X F)} :
    @IsClosed (CollapseQuot X F) (collapseQuotTop F) C ↔ IsClosed (cProj F ⁻¹' C) := by
  let : TopologicalSpace (CollapseQuot X F) := collapseQuotTop F
  rw [← isOpen_compl_iff]
  change IsOpen (cProj F ⁻¹' Cᶜ) ↔ IsClosed (cProj F ⁻¹' C)
  rw [Set.preimage_compl, isOpen_compl_iff]

private lemma cProj_isClosedMap {X : Type} [TopologicalSpace X] {F : Set X}
    (hFcl : IsClosed F) {A : Set X} (hAcl : IsClosed A) :
    @IsClosed (CollapseQuot X F) (collapseQuotTop F) (cProj F '' A) := by
  classical
  rw [cProj_preimage_image_of_closed]
  have hpre : cProj F ⁻¹' (cProj F '' A) = if (A ∩ F).Nonempty then A ∪ F else A := by
    ext x
    split_ifs with hhit
    · constructor
      · rintro ⟨a, haA, hEq⟩
        by_cases hxF : x ∈ F
        · exact Or.inr hxF
        · have haF : a ∉ F := fun haF =>
            hxF (cProj_eq_none_iff.mp (hEq.symm.trans (cProj_eq_none_iff.mpr haF)))
          simp only [cProj, haF, hxF, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hEq
          exact Or.inl (hEq ▸ haA)
      · rintro (hxA | hxF)
        · exact ⟨x, hxA, rfl⟩
        · obtain ⟨a, haA, haF⟩ := hhit
          exact ⟨a, haA, (cProj_eq_none_iff.mpr haF).trans (cProj_eq_none_iff.mpr hxF).symm⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hhit
      constructor
      · rintro ⟨a, haA, hEq⟩
        have haF : a ∉ F := fun haF => Set.eq_empty_iff_forall_notMem.mp hhit a ⟨haA, haF⟩
        have hxF : x ∉ F := fun hxF =>
          haF (cProj_eq_none_iff.mp (hEq.trans (cProj_eq_none_iff.mpr hxF)))
        simp only [cProj, haF, hxF, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hEq
        exact hEq ▸ haA
      · intro hxA
        exact ⟨x, hxA, rfl⟩
  rw [hpre]
  split_ifs
  · exact hAcl.union hFcl
  · exact hAcl

/-- Stratifiability of `CollapseQuot X F` for any nonempty closed `F ⊆ X`. -/
theorem collapseQuot_isStratifiable {X : Type} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) {F : Set X} (hFcl : IsClosed F) (hFne : F.Nonempty) :
    @MSpace.IsStratifiable (CollapseQuot X F) (collapseQuotTop F) := by
  let : TopologicalSpace (CollapseQuot X F) := collapseQuotTop F
  have hT1_X : T1Space X := hStrat.1
  obtain ⟨_, G₀, hG₀⟩ := hStrat
  obtain ⟨G, hG, hanti⟩ := exists_antitone_stratification hG₀
  have hT1_Q : T1Space (CollapseQuot X F) := by
    refine ⟨fun q => ?_⟩
    rw [cProj_preimage_image_of_closed]
    cases q with
    | none =>
      have : cProj F ⁻¹' {none} = F := by ext x; simp [cProj_eq_none_iff]
      rw [this]; exact hFcl
    | some x =>
      have : cProj F ⁻¹' {some x} = {x.1} := by
        classical
        ext y
        simp only [mem_preimage, mem_singleton_iff]
        unfold cProj
        split_ifs with hy
        · exact ⟨fun h => h.elim, fun h => (x.2 (h ▸ hy)).elim⟩
        · exact ⟨fun h => congrArg Subtype.val (Option.some.inj h), fun h => by subst h; rfl⟩
      rw [this]; exact isClosed_singleton
  let GQ : ℕ → Set (CollapseQuot X F) → Set (CollapseQuot X F) := fun n C =>
    open Classical in
    if none ∈ C then
      cProj F '' G n (cProj F ⁻¹' C)
    else
      cProj F '' (G n (cProj F ⁻¹' C) ∩ Hsep G (cProj F ⁻¹' C) F)
  have hpre_sat : ∀ (S : Set X), (F ⊆ S ∨ Disjoint S F) → cProj F ⁻¹' (cProj F '' S) = S := by
    classical
    intro S hS
    ext x
    constructor
    · rintro ⟨a, haS, hEq⟩
      by_cases hxF : x ∈ F
      · rcases hS with hFS | hdisj
        · exact hFS hxF
        · have haF : a ∈ F := cProj_eq_none_iff.mp (hEq.trans (cProj_eq_none_iff.mpr hxF))
          exact (Set.disjoint_left.mp hdisj haS haF).elim
      · have haF : a ∉ F := fun haF =>
          hxF (cProj_eq_none_iff.mp (hEq.symm.trans (cProj_eq_none_iff.mpr haF)))
        simp only [cProj, haF, hxF, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hEq
        exact hEq ▸ haS
    · intro hxS
      exact ⟨x, hxS, rfl⟩
  have hdisj_Hsep_F : ∀ n (A : Set X), Disjoint (G n A ∩ Hsep G A F) F := by
    intro n A
    rw [Set.disjoint_left]
    intro x ⟨_, hxH⟩ hxF
    obtain ⟨m, _, hxm⟩ := mem_iUnion.mp hxH
    exact hxm (subset_closure (hG.2.1 m F hFcl hxF))
  refine ⟨hT1_Q, GQ, ?_, ?_, ?_, ?_⟩
  · intro n C hC
    have hAcl : IsClosed (cProj F ⁻¹' C) := cProj_preimage_image_of_closed.mp hC
    show IsOpen (cProj F ⁻¹' GQ n C)
    classical
    dsimp only [GQ]
    split_ifs with hnone
    · have hFsub : F ⊆ G n (cProj F ⁻¹' C) := by
        intro x hxF
        exact hG.2.1 n _ hAcl (by simpa [cProj_eq_none_iff.mpr hxF] using hnone)
      rw [hpre_sat _ (Or.inl hFsub)]
      exact hG.1 n _ hAcl
    · rw [hpre_sat _ (Or.inr (hdisj_Hsep_F n _))]
      exact (hG.1 n _ hAcl).inter (isOpen_Hsep hG hAcl)
  · intro n C hC q hqC
    have hAcl : IsClosed (cProj F ⁻¹' C) := cProj_preimage_image_of_closed.mp hC
    obtain ⟨x, rfl⟩ := cProj_surjective hFne q
    classical
    dsimp only [GQ]
    split_ifs with hnone
    · exact ⟨x, hG.2.1 n _ hAcl hqC, rfl⟩
    · have hdisjAF : Disjoint (cProj F ⁻¹' C) F := by
        rw [Set.disjoint_left]
        intro y hyA hyF
        exact hnone (cProj_eq_none_iff.mpr hyF ▸ hyA)
      exact ⟨x, ⟨hG.2.1 n _ hAcl hqC, subset_Hsep hG hAcl hFcl hdisjAF hqC⟩, rfl⟩
  · intro C hC
    have hAcl : IsClosed (cProj F ⁻¹' C) := cProj_preimage_image_of_closed.mp hC
    apply Subset.antisymm
    · intro q hq
      obtain ⟨x, rfl⟩ := cProj_surjective hFne q
      have hx_in : ∀ n, cProj F x ∈ cProj F '' closure (G n (cProj F ⁻¹' C)) := by
        intro n
        have hqn : cProj F x ∈ closure (GQ n C) := mem_iInter.mp hq n
        have hsub : GQ n C ⊆ cProj F '' closure (G n (cProj F ⁻¹' C)) := by
          classical
          dsimp only [GQ]
          split_ifs
          · exact Set.image_mono subset_closure
          · exact Set.image_mono (inter_subset_left.trans subset_closure)
        exact closure_minimal hsub (cProj_isClosedMap hFcl isClosed_closure) hqn
      by_cases hnone : none ∈ C
      · by_cases hxF : x ∈ F
        · simpa [cProj_eq_none_iff.mpr hxF] using hnone
        · have hxA : x ∈ ⋂ n, closure (G n (cProj F ⁻¹' C)) := by
            refine mem_iInter.mpr fun n => ?_
            obtain ⟨y, hy, hEq⟩ := hx_in n
            have hyF : y ∉ F := fun hyF =>
              hxF (cProj_eq_none_iff.mp (hEq.symm.trans (cProj_eq_none_iff.mpr hyF)))
            classical
            simp only [cProj, hyF, hxF, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hEq
            exact hEq ▸ hy
          rw [hG.2.2.1 _ hAcl] at hxA
          exact hxA
      · by_cases hxF : x ∈ F
        · have hdisjAF : Disjoint (cProj F ⁻¹' C) F := by
            rw [Set.disjoint_left]
            intro y hyA hyF
            exact hnone (cProj_eq_none_iff.mpr hyF ▸ hyA)
          let V_F : Set (CollapseQuot X F) := cProj F '' Hsep G F (cProj F ⁻¹' C)
          have hVF_open : IsOpen V_F := by
            show IsOpen (cProj F ⁻¹' V_F)
            rw [hpre_sat _ (Or.inl (subset_Hsep hG hFcl hAcl hdisjAF.symm))]
            exact isOpen_Hsep hG hFcl
          have hnone_VF : cProj F x ∈ V_F :=
            ⟨x, subset_Hsep hG hFcl hAcl hdisjAF.symm hxF, rfl⟩
          have hq0 : cProj F x ∈ closure (GQ 0 C) := mem_iInter.mp hq 0
          obtain ⟨q', hq'V, hq'G⟩ := mem_closure_iff.mp hq0 V_F hVF_open hnone_VF
          have hq'G' : q' ∈ cProj F '' (G 0 (cProj F ⁻¹' C) ∩ Hsep G (cProj F ⁻¹' C) F) := by
            simpa [GQ, hnone] using hq'G
          obtain ⟨a, ⟨_, haH⟩, rfl⟩ := hq'G'
          have ha_pre : a ∈ cProj F ⁻¹' V_F := hq'V
          rw [hpre_sat _ (Or.inl (subset_Hsep hG hFcl hAcl hdisjAF.symm))] at ha_pre
          exact (Set.disjoint_left.mp (disjoint_Hsep hanti (cProj F ⁻¹' C) F) haH ha_pre).elim
        · have hxA : x ∈ ⋂ n, closure (G n (cProj F ⁻¹' C)) := by
            refine mem_iInter.mpr fun n => ?_
            obtain ⟨y, hy, hEq⟩ := hx_in n
            have hyF : y ∉ F := fun hyF =>
              hxF (cProj_eq_none_iff.mp (hEq.symm.trans (cProj_eq_none_iff.mpr hyF)))
            classical
            simp only [cProj, hyF, hxF, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hEq
            exact hEq ▸ hy
          rw [hG.2.2.1 _ hAcl] at hxA
          exact hxA
    · intro q hq
      refine mem_iInter.mpr fun n => subset_closure ?_
      obtain ⟨x, rfl⟩ := cProj_surjective hFne q
      classical
      dsimp only [GQ]
      split_ifs with hnone
      · exact ⟨x, hG.2.1 n _ hAcl hq, rfl⟩
      · have hdisjAF : Disjoint (cProj F ⁻¹' C) F := by
          rw [Set.disjoint_left]
          intro y hyA hyF
          exact hnone (cProj_eq_none_iff.mpr hyF ▸ hyA)
        exact ⟨x, ⟨hG.2.1 n _ hAcl hq, subset_Hsep hG hAcl hFcl hdisjAF hq⟩, rfl⟩
  · intro n C₁ C₂ hC₁ hC₂ hC₁₂
    have hA₁ : IsClosed (cProj F ⁻¹' C₁) := cProj_preimage_image_of_closed.mp hC₁
    have hA₂ : IsClosed (cProj F ⁻¹' C₂) := cProj_preimage_image_of_closed.mp hC₂
    have hA₁₂ : cProj F ⁻¹' C₁ ⊆ cProj F ⁻¹' C₂ := Set.preimage_mono hC₁₂
    classical
    dsimp only [GQ]
    split_ifs with h1 h2
    · exact Set.image_mono (hG.2.2.2 n _ _ hA₁ hA₂ hA₁₂)
    · exact (h2 (hC₁₂ h1)).elim
    · exact Set.image_mono (inter_subset_left.trans (hG.2.2.2 n _ _ hA₁ hA₂ hA₁₂))
    · refine Set.image_mono (Set.inter_subset_inter (hG.2.2.2 n _ _ hA₁ hA₂ hA₁₂) ?_)
      exact Hsep_mono hG hA₁ hA₂ hFcl hFcl hA₁₂ Subset.rfl

/-- If `none : CollapseQuot X F` has a CP open outer base, then `F` has a CP open outer base
in `X`. -/
theorem hasCPOuterBaseSet_of_collapseQuot {X : Type} [TopologicalSpace X]
    {F : Set X} (hFcl : IsClosed F) (hFne : F.Nonempty)
    (hcp : @Defs.D_0001.HasCPOuterBase (CollapseQuot X F) (collapseQuotTop F) none) :
    HasCPOuterBaseSet F := by
  let : TopologicalSpace (CollapseQuot X F) := collapseQuotTop F
  have hcont : Continuous (cProj F) := continuous_coinduced_rng
  obtain ⟨𝓑, hB_open, hB_base, hB_cp⟩ := hcp
  refine ⟨(fun B => cProj F ⁻¹' B) '' 𝓑, ?_, ?_, ?_⟩
  · rintro _ ⟨B, hB, rfl⟩
    refine ⟨(hB_open B hB).1.preimage hcont, fun x hxF => ?_⟩
    simpa [mem_preimage, cProj_eq_none_iff.mpr hxF] using (hB_open B hB).2
  · intro 𝓖 h𝓖
    let 𝓗 : Set (Set (CollapseQuot X F)) := { B ∈ 𝓑 | cProj F ⁻¹' B ∈ 𝓖 }
    have hH_sub : 𝓗 ⊆ 𝓑 := fun _ h => h.1
    have hpre_eq : ⋃₀ 𝓖 = cProj F ⁻¹' (⋃₀ 𝓗) := by
      ext x
      constructor
      · rintro ⟨U, hUG, hxU⟩
        obtain ⟨B, hB, rfl⟩ := h𝓖 hUG
        exact ⟨B, ⟨hB, hUG⟩, hxU⟩
      · rintro ⟨B, ⟨_, hBG⟩, hxB⟩
        exact ⟨cProj F ⁻¹' B, hBG, hxB⟩
    apply Subset.antisymm
    · intro x hx
      rw [hpre_eq] at hx
      have hx' : cProj F x ∈ closure (⋃₀ 𝓗) := hcont.closure_preimage_subset (⋃₀ 𝓗) hx
      rw [hB_cp 𝓗 hH_sub] at hx'
      obtain ⟨_, ⟨B, hBH, rfl⟩, hxB⟩ := hx'
      have hx_cl : x ∈ closure (cProj F ⁻¹' B) := by
        have hsub : B ⊆ cProj F '' closure (cProj F ⁻¹' B) := by
          intro q hqB
          obtain ⟨y, rfl⟩ := cProj_surjective hFne q
          exact ⟨y, subset_closure hqB, rfl⟩
        have hcl_mem : cProj F x ∈ cProj F '' closure (cProj F ⁻¹' B) :=
          closure_minimal hsub (cProj_isClosedMap hFcl isClosed_closure) hxB
        obtain ⟨y, hy_cl, hEq⟩ := hcl_mem
        by_cases hxF : x ∈ F
        · exact subset_closure (by simpa [mem_preimage, cProj_eq_none_iff.mpr hxF] using (hB_open B hBH.1).2)
        · have hyF : y ∉ F := fun hyF =>
            hxF (cProj_eq_none_iff.mp (hEq.symm.trans (cProj_eq_none_iff.mpr hyF)))
          classical
          simp only [cProj, hyF, hxF, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hEq
          exact hEq ▸ hy_cl
      exact ⟨closure (cProj F ⁻¹' B), ⟨cProj F ⁻¹' B, hBH.2, rfl⟩, hx_cl⟩
    · rintro x ⟨_, ⟨U, hUG, rfl⟩, hxU⟩
      exact closure_mono (Set.subset_sUnion_of_mem hUG) hxU
  · intro W hWo hFW
    let W' : Set (CollapseQuot X F) := cProj F '' W
    have hpre_W : cProj F ⁻¹' W' = W := by
      classical
      ext x
      constructor
      · rintro ⟨a, haW, hEq⟩
        by_cases hxF : x ∈ F
        · exact hFW hxF
        · have haF : a ∉ F := fun haF =>
            hxF (cProj_eq_none_iff.mp (hEq.symm.trans (cProj_eq_none_iff.mpr haF)))
          simp only [cProj, haF, hxF, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hEq
          exact hEq ▸ haW
      · intro hxW
        exact ⟨x, hxW, rfl⟩
    have hW'_open : IsOpen W' := by
      show IsOpen (cProj F ⁻¹' W')
      rwa [hpre_W]
    obtain ⟨x₀, hx₀⟩ := hFne
    have hnone_W' : none ∈ W' := ⟨x₀, hFW hx₀, cProj_eq_none_iff.mpr hx₀⟩
    obtain ⟨B, hB, hBW'⟩ := hB_base W' hW'_open hnone_W'
    refine ⟨cProj F ⁻¹' B, ⟨B, hB, rfl⟩, ?_⟩
    rw [← hpre_W]
    exact Set.preimage_mono hBW'

/-- Global converse of `L0020_imp_not_Tinf`: if every point of every stratifiable space
has a closure-preserving open outer base (`¬ Specs.L_0020.stmt`), then `M₃ ⇒ M₁` (`Tinf`)
holds! -/
theorem not_L0020_imp_Tinf (hnot : ¬ Specs.L_0020.stmt) : MSpace.Goals.Tinf_M3_imp_M1 := by
  intro X _ hM3
  have hStrat : MSpace.IsStratifiable X := Proofs.L_0004.m3_to_strat X hM3
  refine isM1_of_stratifiable_and_closed_hasCPOuterBase X hStrat fun F hFcl => ?_
  by_cases hFne : F.Nonempty
  · have hQ_strat : @MSpace.IsStratifiable (CollapseQuot X F) (collapseQuotTop F) :=
      collapseQuot_isStratifiable hStrat hFcl hFne
    have hQ_cp : @Defs.D_0001.HasCPOuterBase (CollapseQuot X F) (collapseQuotTop F) none := by
      by_contra hno
      exact hnot ⟨CollapseQuot X F, collapseQuotTop F, hQ_strat, none, hno⟩
    exact hasCPOuterBaseSet_of_collapseQuot hFcl hFne hQ_cp
  · rw [Set.not_nonempty_iff_eq_empty] at hFne
    subst hFne
    refine ⟨{∅}, ?_, ?_, ?_⟩
    · rintro _ rfl
      exact ⟨isOpen_empty, Subset.rfl⟩
    · intro 𝓖 h𝓖
      by_cases hG : ∅ ∈ 𝓖
      · have hEq : 𝓖 = {∅} := Set.Subset.antisymm h𝓖 (Set.singleton_subset_iff.mpr hG)
        subst hEq
        simp
      · have hEq : 𝓖 = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun U hU =>
          hG (Set.mem_singleton_iff.mp (h𝓖 hU) ▸ hU)
        subst hEq
        simp
    · intro W _ _
      exact ⟨∅, rfl, empty_subset W⟩

/-! ## Part 6: Corollaries — σ-closed-discrete dense subset, locally compact/compact M₁, countable M₁ -/

/-- Every stratifiable space has a σ-closed-discrete dense subset `⋃ p, D p`
(generalizing `Proofs.L_0026` from `M₁` to `M₃` / stratifiable spaces). -/
theorem stratifiable_has_sigma_closed_discrete_dense (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) :
    ∃ D : ℕ → Set X,
      (∀ p, ∀ S ⊆ D p, IsClosed S) ∧
      Dense (⋃ p, D p) := by
  have : T1Space X := hStrat.1
  obtain ⟨𝓝_fam, _, hN_disc, hN_net⟩ :=
    stratifiable_has_sigma_discrete_closed_network X hStrat
  let D : ℕ → Set X := fun p =>
    { x : X | ∃ F ∈ 𝓝_fam p, ∃ h : F.Nonempty, x = h.some }
  refine ⟨D, ?_, ?_⟩
  · intro p S hS
    rw [← isOpen_compl_iff]
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    obtain ⟨W, hWo, hzW, hWuniq⟩ := hN_disc p z
    by_cases hhit : ∃ x₀ ∈ S, x₀ ∈ W
    · obtain ⟨x₀, hx₀S, hx₀W⟩ := hhit
      have hzx₀ : z ≠ x₀ := fun h => hz (h ▸ hx₀S)
      obtain ⟨F₀, hF₀mem, hF₀ne, rfl⟩ := hS hx₀S
      have hopen : IsOpen (W \ {hF₀ne.some}) := hWo.sdiff isClosed_singleton
      refine Filter.mem_of_superset (hopen.mem_nhds ⟨hzW, hzx₀⟩) ?_
      rintro y ⟨hyW, hyne⟩ hyS
      obtain ⟨F, hFmem, hFne, rfl⟩ := hS hyS
      have hFeq : F = F₀ :=
        hWuniq F hFmem F₀ hF₀mem ⟨hFne.some, hyW, hFne.some_mem⟩ ⟨hF₀ne.some, hx₀W, hF₀ne.some_mem⟩
      subst hFeq
      exact hyne rfl
    · refine Filter.mem_of_superset (hWo.mem_nhds hzW) ?_
      intro y hyW hyS
      exact hhit ⟨y, hyS, hyW⟩
  · rw [dense_iff_inter_open]
    intro V hVo ⟨x, hxV⟩
    obtain ⟨p, F, hFp, hxF, hFV⟩ := hN_net x V hVo hxV
    have hFne : F.Nonempty := ⟨x, hxF⟩
    exact ⟨hFne.some, hFV hFne.some_mem, mem_iUnion.mpr ⟨p, F, hFp, hFne, rfl⟩⟩

/-- General network form of Ito (1985): if `X` is stratifiable and admits a σ-discrete
closed network whose members each have a CP open outer base, then `X` is `M₁`. -/
theorem isM1_of_stratifiable_and_network_hasCPOuterBase (X : Type) [TopologicalSpace X]
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

/-- A decreasing countable sequence of sets is always closure-preserving. -/
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

/-- In a locally compact stratifiable space, every compact subset `K` has a decreasing
countable (hence CP) open outer base. -/
theorem hasCPOuterBaseSet_of_compact_in_locallyCompact_stratifiable (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) [LocallyCompactSpace X]
    {K : Set X} (hK : IsCompact K) : HasCPOuterBaseSet K := by
  have : T3Space X := (Proofs.L_0004.strat_to_m3 X hStrat).1
  have hKcl : IsClosed K := hK.isClosed
  obtain ⟨_, G₀, hG₀⟩ := hStrat
  obtain ⟨G, hG, hanti⟩ := exists_antitone_stratification hG₀
  choose C_pt hC_comp hC_nhd using fun x : X => exists_compact_mem_nhds x
  have hK_sub_union : K ⊆ ⋃ x ∈ K, interior (C_pt x) := fun x hx =>
    mem_iUnion₂.mpr ⟨x, hx, mem_interior_iff_mem_nhds.mpr (hC_nhd x)⟩
  obtain ⟨t, _, htfin, hKt⟩ := hK.elim_finite_subcover_image (fun x _ => isOpen_interior) hK_sub_union
  let C : Set X := ⋃ x ∈ t, C_pt x
  have hC_compact : IsCompact C := htfin.isCompact_biUnion fun x _ => hC_comp x
  let O_int : Set X := ⋃ x ∈ t, interior (C_pt x)
  have hO_open : IsOpen O_int := isOpen_biUnion fun x _ => isOpen_interior
  have hK_sub_O : K ⊆ O_int := hKt
  have hO_sub_C : O_int ⊆ C := by
    rintro y hy
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨x, hxt, interior_subset hyx⟩
  let U : ℕ → Set X := fun n => G n K ∩ O_int
  have hU_anti : ∀ n, U (n + 1) ⊆ U n := fun n =>
    Set.inter_subset_inter_left O_int (hanti n K)
  refine ⟨Set.range U, ?_, closurePreserving_range_antitone U hU_anti, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨(hG.1 n K hKcl).inter hO_open, fun x hx => ⟨hG.2.1 n K hKcl hx, hK_sub_O hx⟩⟩
  · intro W hWo hKW
    let S : ℕ → Set X := fun n => (C ∩ closure (G n K)) \ W
    have hS_closed : ∀ n, IsClosed (S n) := fun n =>
      (hC_compact.isClosed.inter isClosed_closure).sdiff hWo
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
          (hC_compact.of_isClosed_subset (hS_closed 0) (fun x hx => hx.1.1))
          hS_closed
      rw [hS_empty] at hnonempty
      exact Set.not_nonempty_empty hnonempty
    obtain ⟨n, hn⟩ := hne_all
    refine ⟨U n, ⟨n, rfl⟩, fun x hx => ?_⟩
    by_contra hxW
    have hxS : x ∈ S n := ⟨⟨hO_sub_C hx.2, subset_closure hx.1⟩, hxW⟩
    rw [hn] at hxS
    exact hxS

/-- Every locally compact stratifiable space is `M₁`. -/
theorem isM1_of_stratifiable_locallyCompact (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) [LocallyCompactSpace X] :
    MSpace.IsM1 X := by
  obtain ⟨𝓝_fam, hN_closed, hN_disc, hN_net⟩ :=
    stratifiable_has_sigma_discrete_closed_network X hStrat
  let 𝓝' : ℕ → Set (Set X) := fun p => { F ∈ 𝓝_fam p | IsCompact F }
  refine isM1_of_stratifiable_and_network_hasCPOuterBase X hStrat 𝓝'
    (fun p F hF => hN_closed p F hF.1)
    (fun p z => by
      obtain ⟨W, hWo, hzW, hWuniq⟩ := hN_disc p z
      exact ⟨W, hWo, hzW, fun F₁ hF₁ F₂ hF₂ h1 h2 => hWuniq F₁ hF₁.1 F₂ hF₂.1 h1 h2⟩)
    (fun x V hVo hxV => by
      obtain ⟨K, hKc, hKnhd⟩ := exists_compact_mem_nhds x
      have hopen : IsOpen (V ∩ interior K) := hVo.inter isOpen_interior
      have hx_in : x ∈ V ∩ interior K := ⟨hxV, mem_interior_iff_mem_nhds.mpr hKnhd⟩
      obtain ⟨p, F, hFp, hxF, hFsub⟩ := hN_net x (V ∩ interior K) hopen hx_in
      have hFcomp : IsCompact F :=
        hKc.of_isClosed_subset (hN_closed p F hFp) (hFsub.trans (inter_subset_right.trans interior_subset))
      exact ⟨p, F, ⟨hFp, hFcomp⟩, hxF, hFsub.trans inter_subset_left⟩)
    (fun p F hF => hasCPOuterBaseSet_of_compact_in_locallyCompact_stratifiable X hStrat hF.2)

/-- Every compact stratifiable space is `M₁`. -/
theorem isM1_of_stratifiable_compact (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) [CompactSpace X] :
    MSpace.IsM1 X := by
  have : T3Space X := (Proofs.L_0004.strat_to_m3 X hStrat).1
  exact isM1_of_stratifiable_locallyCompact X hStrat

/-- Every countable `T₃` space whose points each have a CP open outer base is `M₁`. -/
theorem isM1_of_countable_t3_hasCPOuterBase (X : Type) [TopologicalSpace X]
    [T3Space X] [Countable X]
    (hCP : ∀ x : X, Defs.D_0001.HasCPOuterBase x) :
    MSpace.IsM1 X := by
  by_cases hne : Nonempty X
  · obtain ⟨f, hf⟩ := exists_surjective_nat X
    choose 𝓑 hB_open hB_base hB_cp using hCP
    refine ⟨inferInstance, ⋃ n : ℕ, 𝓑 (f n), ?_, ⟨fun n => 𝓑 (f n), fun n => hB_cp (f n), rfl⟩⟩
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro U hU
      obtain ⟨n, hUn⟩ := mem_iUnion.mp hU
      exact (hB_open (f n) U hUn).1
    · intro x V hxV hVo
      obtain ⟨n, rfl⟩ := hf x
      obtain ⟨U, hUn, hUV⟩ := hB_base (f n) V hVo hxV
      exact ⟨U, mem_iUnion.mpr ⟨n, hUn⟩, (hB_open (f n) U hUn).2, hUV⟩
  · rw [not_nonempty_iff] at hne
    refine ⟨inferInstance, ∅, ?_, ⟨fun _ => ∅, fun _ 𝓖 h𝓖 => by
      have hEq : 𝓖 = ∅ := Set.subset_empty_iff.mp h𝓖
      subst hEq; simp, by simp⟩⟩
    exact isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.elim) (fun x => isEmptyElim x)

end Research.Ito1985
