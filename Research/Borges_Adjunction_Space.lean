import Targets.Defs
import Proofs.L_0004

/-!
# Borges (1966) Theorem 3.7: Adjunction Spaces of Stratifiable Spaces are Stratifiable

Given two topological spaces `X` and `Y`, a closed subset `A ⊆ X`, and a continuous
attaching map `f : A → Y`, the **adjunction space** (topological pushout) `X ∪_f Y` is
represented as the disjoint union `AdjunctionSpace X Y A := { x : X // x ∉ A } ⊕ Y`
equipped with the quotient topology coinduced by the attaching projection
`adjProj : X ⊕ Y → AdjunctionSpace X Y A`.

This standalone module proves:
1. **`adjunctionSpace_isOpen_iff`** & **`adjunctionSpace_isClosed_iff`**: exact
   characterization of open and closed sets in `X ∪_f Y` via their preimages in `X` and `Y`.
2. **`adjunctionSpace_t1Space`**: if `X` and `Y` are `T₁` and `A` is closed in `X`, then
   `X ∪_f Y` is `T₁`.
3. **`adjunctionSpace_isStratifiable`** (Borges 1966, Theorem 3.7): if `X` and `Y` are
   stratifiable, `A ⊆ X` is closed, and `f : A → Y` is continuous, then `X ∪_f Y` is
   stratifiable.
-/

namespace Research.BorgesAdjunction

open Set Topology TopologicalSpace

/-! ## Part 1: Definition of `AdjunctionSpace X Y A` and quotient topology -/

/-- Underlying type of the adjunction space `X ∪_f Y`: points of `X \ A` plus points of `Y`. -/
abbrev AdjunctionSpace (X Y : Type*) (A : Set X) : Type _ :=
  { x : X // x ∉ A } ⊕ Y

/-- Canonical map `X → X ∪_f Y` sending `x ∈ A` to `Sum.inr (f ⟨x, hx⟩)` and `x ∉ A` to
`Sum.inl ⟨x, hx⟩`. -/
noncomputable def adjInX {X Y : Type*} {A : Set X} (f : A → Y) (x : X) :
    AdjunctionSpace X Y A :=
  open Classical in
  if hx : x ∈ A then Sum.inr (f ⟨x, hx⟩) else Sum.inl ⟨x, hx⟩

/-- Canonical quotient projection `X ⊕ Y → X ∪_f Y`. -/
noncomputable def adjProj {X Y : Type*} {A : Set X} (f : A → Y) :
    X ⊕ Y → AdjunctionSpace X Y A
  | Sum.inl x => adjInX f x
  | Sum.inr y => Sum.inr y

/-- Quotient topology on `X ∪_f Y` coinduced by `adjProj f`. -/
@[instance_reducible]
noncomputable def adjTop {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} (f : A → Y) : TopologicalSpace (AdjunctionSpace X Y A) :=
  TopologicalSpace.coinduced (adjProj f) inferInstance

/-- Exact characterization of open sets in `X ∪_f Y`. -/
theorem adjTop_isOpen_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} (f : A → Y) (U : Set (AdjunctionSpace X Y A)) :
    @IsOpen _ (adjTop f) U ↔ IsOpen (adjInX f ⁻¹' U) ∧ IsOpen (Sum.inr ⁻¹' U) := by
  change IsOpen (adjProj f ⁻¹' U) ↔ _
  rw [isOpen_sum_iff]
  rfl

/-- Exact characterization of closed sets in `X ∪_f Y`. -/
theorem adjTop_isClosed_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} (f : A → Y) (C : Set (AdjunctionSpace X Y A)) :
    @IsClosed _ (adjTop f) C ↔ IsClosed (adjInX f ⁻¹' C) ∧ IsClosed (Sum.inr ⁻¹' C) := by
  let : TopologicalSpace (AdjunctionSpace X Y A) := adjTop f
  rw [← isOpen_compl_iff, adjTop_isOpen_iff]
  simp only [Set.preimage_compl, isOpen_compl_iff]

/-- Assemble a subset of `X ∪_f Y` from `U_X ⊆ X` and `U_Y ⊆ Y`. -/
def glueSet {X Y : Type*} {A : Set X} (U_X : Set X) (U_Y : Set Y) :
    Set (AdjunctionSpace X Y A) :=
  { z | match z with
        | Sum.inl x => x.1 ∈ U_X
        | Sum.inr y => y ∈ U_Y }

private lemma glueSet_preimage_inr {X Y : Type*} {A : Set X} (U_X : Set X) (U_Y : Set Y) :
    Sum.inr ⁻¹' (glueSet (A := A) U_X U_Y) = U_Y := rfl

private lemma glueSet_preimage_inX {X Y : Type*} {A : Set X} (f : A → Y)
    {U_X : Set X} {U_Y : Set Y}
    (hcompat : ∀ (x : X) (hx : x ∈ A), x ∈ U_X ↔ f ⟨x, hx⟩ ∈ U_Y) :
    adjInX f ⁻¹' (glueSet (A := A) U_X U_Y) = U_X := by
  classical
  ext x
  simp only [mem_preimage, glueSet, adjInX]
  split_ifs with hx
  · exact (hcompat x hx).symm
  · rfl

private lemma glueSet_isOpen {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} (f : A → Y) {U_X : Set X} {U_Y : Set Y}
    (hXo : IsOpen U_X) (hYo : IsOpen U_Y)
    (hcompat : ∀ (x : X) (hx : x ∈ A), x ∈ U_X ↔ f ⟨x, hx⟩ ∈ U_Y) :
    @IsOpen _ (adjTop f) (glueSet (A := A) U_X U_Y) := by
  rw [adjTop_isOpen_iff, glueSet_preimage_inX f hcompat, glueSet_preimage_inr]
  exact ⟨hXo, hYo⟩

/-- If `X` and `Y` are `T₁`, `A ⊆ X` is closed, and `f : A → Y` is continuous, then
`X ∪_f Y` is `T₁`. -/
theorem adjunctionSpace_t1Space {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] [T1Space Y] {A : Set X} (hAcl : IsClosed A) {f : A → Y} (hf : Continuous f) :
    @T1Space (AdjunctionSpace X Y A) (adjTop f) := by
  let : TopologicalSpace (AdjunctionSpace X Y A) := adjTop f
  refine ⟨fun z => ?_⟩
  rw [adjTop_isClosed_iff]
  cases z with
  | inl x =>
    refine ⟨?_, ?_⟩
    · have hEq : adjInX f ⁻¹' {Sum.inl x} = {x.1} := by
        classical
        ext a
        simp only [mem_preimage, mem_singleton_iff, adjInX]
        split_ifs with ha
        · exact ⟨fun h => h.elim, fun h => (x.2 (h ▸ ha)).elim⟩
        · exact ⟨fun h => congrArg Subtype.val (Sum.inl.inj h), fun h => by subst h; rfl⟩
      rw [hEq]
      exact isClosed_singleton
    · have hEq : (Sum.inr ⁻¹' ({Sum.inl x} : Set (AdjunctionSpace X Y A))) = ∅ := by
        ext y; simp
      rw [hEq]
      exact isClosed_empty
  | inr y =>
    refine ⟨?_, ?_⟩
    · have hEq : adjInX f ⁻¹' {Sum.inr y} = (Subtype.val : A → X) '' (f ⁻¹' {y}) := by
        classical
        ext a
        simp only [mem_preimage, mem_singleton_iff, mem_image, Subtype.exists, exists_and_right,
          exists_eq_right, adjInX]
        split_ifs with ha
        · exact ⟨fun h => ⟨ha, Sum.inr.inj h⟩, fun ⟨_, h⟩ => congrArg Sum.inr h⟩
        · exact ⟨fun h => h.elim, fun ⟨h, _⟩ => (ha h).elim⟩
      rw [hEq]
      exact hAcl.isClosedMap_subtype_val _ (isClosed_singleton.preimage hf)
    · have hEq : (Sum.inr ⁻¹' ({Sum.inr y} : Set (AdjunctionSpace X Y A))) = {y} := by
        ext y'; simp
      rw [hEq]
      exact isClosed_singleton

/-! ## Part 2: Stratification helpers (`exists_antitone_stratification`, `Hsep`) -/

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

private lemma disjoint_Hsep_right {X : Type*} [TopologicalSpace X] {G : ℕ → Set X → Set X}
    (hG : MSpace.IsStratification G) {A B : Set X} (hB : IsClosed B) :
    Disjoint (Hsep G A B) B := by
  rw [Set.disjoint_left]
  intro x hxH hxB
  obtain ⟨n, _, hxnB⟩ := mem_iUnion.mp hxH
  exact hxnB (subset_closure (hG.2.1 n B hB hxB))

/-! ## Part 3: Borges (1966) Theorem 3.7 — `X ∪_f Y` is stratifiable -/

/-- Borges (1966, Theorem 3.7): If `X` and `Y` are stratifiable, `A ⊆ X` is closed, and
`f : A → Y` is continuous, then the adjunction space `X ∪_f Y` is stratifiable. -/
theorem adjunctionSpace_isStratifiable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : MSpace.IsStratifiable X) (hY : MSpace.IsStratifiable Y)
    {A : Set X} (hAcl : IsClosed A) {f : A → Y} (hf : Continuous f) :
    @MSpace.IsStratifiable (AdjunctionSpace X Y A) (adjTop f) := by
  let : TopologicalSpace (AdjunctionSpace X Y A) := adjTop f
  have : T1Space X := hX.1
  have : T1Space Y := hY.1
  have hT3_Y : T3Space Y := (Proofs.L_0004.strat_to_m3 Y hY).1
  have hT1_Z : T1Space (AdjunctionSpace X Y A) := adjunctionSpace_t1Space hAcl hf
  obtain ⟨_, GX₀, hGX₀⟩ := hX
  obtain ⟨_, GY₀, hGY₀⟩ := hY
  obtain ⟨GX, hGX, hantiX⟩ := exists_antitone_stratification hGX₀
  obtain ⟨GY, hGY, hantiY⟩ := exists_antitone_stratification hGY₀
  -- Helper: push a subset of `A` into `X`.
  let toX : Set A → Set X := fun S => (Subtype.val : A → X) '' S
  have htoX_closed : ∀ {S : Set A}, IsClosed S → IsClosed (toX S) := fun hS =>
    hAcl.isClosedMap_subtype_val _ hS
  -- For `n : ℕ` and `C : Set Z`:
  --   `CY C := Sum.inr ⁻¹' C`
  --   `CX C := adjInX f ⁻¹' C`
  --   `UY n C := GY n (CY C)`
  --   `B n C := toX (f ⁻¹' (UY n C)ᶜ)` (closed in `X` when `CY C` is closed!)
  --   `K n k C := (GY k (UY n C)ᶜ)ᶜ` (closed in `Y`, monotone in `C`, `⋃ k, K n k C = UY n C`)
  --   `Ank n k C := toX (f ⁻¹' K n k C)` (closed in `X`, disjoint from `B n C`)
  --   `UX n C := (GX n (CX C) ∩ Hsep GX (CX C) (B n C)) ∪
  --              ⋃ k, (GX (n + k) (Ank n k C) ∩ Hsep GX (Ank n k C) (B n C))`
  let CY : Set (AdjunctionSpace X Y A) → Set Y := fun C => Sum.inr ⁻¹' C
  let CX : Set (AdjunctionSpace X Y A) → Set X := fun C => adjInX f ⁻¹' C
  let UY : ℕ → Set (AdjunctionSpace X Y A) → Set Y := fun n C => GY n (CY C)
  let B : ℕ → Set (AdjunctionSpace X Y A) → Set X := fun n C => toX (f ⁻¹' (UY n C)ᶜ)
  let K : ℕ → ℕ → Set (AdjunctionSpace X Y A) → Set Y := fun n k C => (GY k (UY n C)ᶜ)ᶜ
  let Ank : ℕ → ℕ → Set (AdjunctionSpace X Y A) → Set X := fun n k C => toX (f ⁻¹' K n k C)
  let UX : ℕ → Set (AdjunctionSpace X Y A) → Set X := fun n C =>
    (GX n (CX C) ∩ Hsep GX (CX C) (B n C)) ∪
      ⋃ k : ℕ, (GX (n + k) (Ank n k C) ∩ Hsep GX (Ank n k C) (B n C))
  let GZ : ℕ → Set (AdjunctionSpace X Y A) → Set (AdjunctionSpace X Y A) := fun n C =>
    glueSet (A := A) (UX n C) (UY n C)
  have hB_closed : ∀ n C, IsClosed C → IsClosed (B n C) := by
    intro n C hC
    have hCY : IsClosed (CY C) := (adjTop_isClosed_iff f C).mp hC |>.2
    exact htoX_closed ((hGY.1 n _ hCY).isClosed_compl.preimage hf)
  have hK_closed : ∀ n k C, IsClosed C → IsClosed (K n k C) := by
    intro n k C hC
    have hCY : IsClosed (CY C) := (adjTop_isClosed_iff f C).mp hC |>.2
    exact (hGY.1 k _ (hGY.1 n _ hCY).isClosed_compl).isClosed_compl
  have hAnk_closed : ∀ n k C, IsClosed C → IsClosed (Ank n k C) := fun n k C hC =>
    htoX_closed ((hK_closed n k C hC).preimage hf)
  have hAnk_sub_A : ∀ n k C, Ank n k C ⊆ A := by
    rintro _ _ _ _ ⟨a, _, rfl⟩
    exact a.2
  have hAnk_disj_B : ∀ n k C, IsClosed C → Disjoint (Ank n k C) (B n C) := by
    intro n k C hC
    have hCY : IsClosed (CY C) := (adjTop_isClosed_iff f C).mp hC |>.2
    rw [Set.disjoint_left]
    rintro _ ⟨a, haK, rfl⟩ ⟨b, hbB, hab⟩
    have hEq : a = b := Subtype.ext hab.symm
    subst hEq
    exact haK (hGY.2.1 k _ (hGY.1 n _ hCY).isClosed_compl hbB)
  have hcompat : ∀ n C, IsClosed C →
      ∀ (x : X) (hx : x ∈ A), x ∈ UX n C ↔ f ⟨x, hx⟩ ∈ UY n C := by
    intro n C hC x hx
    have hCY : IsClosed (CY C) := (adjTop_isClosed_iff f C).mp hC |>.2
    have hBcl : IsClosed (B n C) := hB_closed n C hC
    constructor
    · intro hxUX
      by_contra hnot
      have hxB : x ∈ B n C := ⟨⟨x, hx⟩, hnot, rfl⟩
      rcases hxUX with ⟨_, hxH⟩ | hxU
      · exact Set.disjoint_left.mp (disjoint_Hsep_right hGX hBcl) hxH hxB
      · obtain ⟨k, _, hxH⟩ := mem_iUnion.mp hxU
        exact Set.disjoint_left.mp (disjoint_Hsep_right hGX hBcl) hxH hxB
    · intro hfx
      have hnot_compl : f ⟨x, hx⟩ ∉ (UY n C)ᶜ := fun h => h hfx
      rw [← hGY.2.2.1 _ (hGY.1 n _ hCY).isClosed_compl, mem_iInter] at hnot_compl
      push Not at hnot_compl
      obtain ⟨k, hk⟩ := hnot_compl
      have hxAnk : x ∈ Ank n k C := ⟨⟨x, hx⟩, fun h => hk (subset_closure h), rfl⟩
      refine Or.inr (mem_iUnion.mpr ⟨k, ?_, ?_⟩)
      · exact hGX.2.1 (n + k) _ (hAnk_closed n k C hC) hxAnk
      · exact subset_Hsep hGX (hAnk_closed n k C hC) hBcl (hAnk_disj_B n k C hC) hxAnk
  have hCX_disj_B : ∀ n C, IsClosed C → Disjoint (CX C) (B n C) := by
    intro n C hC
    have hCY : IsClosed (CY C) := (adjTop_isClosed_iff f C).mp hC |>.2
    rw [Set.disjoint_left]
    rintro x hxCX ⟨a, haB, rfl⟩
    have hfa : f a ∈ CY C := by
      classical
      simpa [CX, CY, adjInX, a.2] using hxCX
    exact haB (hGY.2.1 n _ hCY hfa)
  refine ⟨hT1_Z, GZ, ?_, ?_, ?_, ?_⟩
  · -- Openness of `GZ n C`
    intro n C hC
    have hCX : IsClosed (CX C) := (adjTop_isClosed_iff f C).mp hC |>.1
    have hCY : IsClosed (CY C) := (adjTop_isClosed_iff f C).mp hC |>.2
    refine glueSet_isOpen f ?_ (hGY.1 n _ hCY) (hcompat n C hC)
    refine ((hGX.1 n _ hCX).inter (isOpen_Hsep hGX hCX)).union ?_
    exact isOpen_iUnion fun k =>
      (hGX.1 (n + k) _ (hAnk_closed n k C hC)).inter (isOpen_Hsep hGX (hAnk_closed n k C hC))
  · -- `C ⊆ GZ n C`
    intro n C hC z hzC
    have hCX : IsClosed (CX C) := (adjTop_isClosed_iff f C).mp hC |>.1
    have hCY : IsClosed (CY C) := (adjTop_isClosed_iff f C).mp hC |>.2
    have hBcl : IsClosed (B n C) := hB_closed n C hC
    cases z with
    | inl x =>
      have hxCX : x.1 ∈ CX C := by
        classical
        simpa [CX, adjInX, x.2] using hzC
      exact Or.inl ⟨hGX.2.1 n _ hCX hxCX, subset_Hsep hGX hCX hBcl (hCX_disj_B n C hC) hxCX⟩
    | inr y =>
      exact hGY.2.1 n _ hCY hzC
  · -- `⋂ n, closure (GZ n C) = C`
    intro C hC
    have hCX : IsClosed (CX C) := (adjTop_isClosed_iff f C).mp hC |>.1
    have hCY : IsClosed (CY C) := (adjTop_isClosed_iff f C).mp hC |>.2
    apply Subset.antisymm
    · intro z hz
      by_contra hzC
      cases z with
      | inl x =>
        -- `x.1 ∉ CX C` and `x.1 ∉ A` (both closed in `X`).
        have hx_not_CX : x.1 ∉ CX C := by
          classical
          simpa [CX, adjInX, x.2] using hzC
        have hx_not_A : x.1 ∉ ⋂ n, closure (GX n A) := by
          rw [hGX.2.2.1 A hAcl]; exact x.2
        rw [← hGX.2.2.1 _ hCX, mem_iInter] at hx_not_CX
        rw [mem_iInter] at hx_not_A
        push Not at hx_not_CX hx_not_A
        obtain ⟨n₁, hn₁⟩ := hx_not_CX
        obtain ⟨n₂, hn₂⟩ := hx_not_A
        let n := max n₁ n₂
        let WX : Set X := (closure (GX n (CX C)))ᶜ ∩ (closure (GX n A))ᶜ
        have hWZo : IsOpen (glueSet (A := A) WX (∅ : Set Y)) := by
          refine glueSet_isOpen f (isClosed_closure.isOpen_compl.inter isClosed_closure.isOpen_compl)
            isOpen_empty fun a ha => ?_
          have ha_cl : a ∈ closure (GX n A) := subset_closure (hGX.2.1 n A hAcl ha)
          exact ⟨fun h => h.2 ha_cl, fun h => h.elim⟩
        have hxWZ : Sum.inl x ∈ glueSet (A := A) WX (∅ : Set Y) :=
          ⟨fun h => hn₁ (closure_mono (antitone_le hantiX (le_max_left _ _) _) h),
           fun h => hn₂ (closure_mono (antitone_le hantiX (le_max_right _ _) _) h)⟩
        have hzn : Sum.inl x ∈ closure (GZ n C) := mem_iInter.mp hz n
        obtain ⟨w, hwWZ, hwGZ⟩ := mem_closure_iff.mp hzn _ hWZo hxWZ
        cases w with
        | inr y => exact hwWZ
        | inl u =>
          rcases hwGZ with ⟨hu1, _⟩ | hu2
          · exact hwWZ.1 (subset_closure hu1)
          · obtain ⟨k, huG, _⟩ := mem_iUnion.mp hu2
            have huGA : u.1 ∈ GX n A :=
              antitone_le hantiX (Nat.le_add_right n k) A
                (hGX.2.2.2 (n + k) _ A (hAnk_closed n k C hC) hAcl (hAnk_sub_A n k C) huG)
            exact hwWZ.2 (subset_closure huGA)
      | inr y =>
        -- `y ∉ CY C`, so pick `n` with `y ∉ closure (GY n (CY C))`.
        have hy_not_CY : y ∉ CY C := hzC
        rw [← hGY.2.2.1 _ hCY, mem_iInter] at hy_not_CY
        push Not at hy_not_CY
        obtain ⟨n, hn⟩ := hy_not_CY
        -- By `T3Space Y`, pick an open neighborhood `WY` of `y` with `closure WY ∩ closure (UY n C) = ∅`.
        obtain ⟨t, ht_nhd, ht_cl, ht_sub⟩ :=
          exists_mem_nhds_isClosed_subset (isClosed_closure.isOpen_compl.mem_nhds hn)
        let WY : Set Y := interior t
        have hWYo : IsOpen WY := isOpen_interior
        have hyWY : y ∈ WY := mem_interior_iff_mem_nhds.mpr ht_nhd
        have hclWY_disj : Disjoint (closure WY) (closure (UY n C)) := by
          rw [Set.disjoint_left]
          intro u hu1 hu2
          exact ht_sub (closure_minimal interior_subset ht_cl hu1) hu2
        let D : Set X := toX (f ⁻¹' closure WY)
        let E : Set X := toX (f ⁻¹' closure (UY n C))
        have hDcl : IsClosed D := htoX_closed (isClosed_closure.preimage hf)
        have hEcl : IsClosed E := htoX_closed (isClosed_closure.preimage hf)
        have hBcl : IsClosed (B n C) := hB_closed n C hC
        have hD_sub_B : D ⊆ B n C := by
          rintro _ ⟨a, haD, rfl⟩
          exact ⟨a, fun h => Set.disjoint_left.mp hclWY_disj haD (subset_closure h), rfl⟩
        have hAnk_sub_E : ∀ k, Ank n k C ⊆ E := by
          rintro k _ ⟨a, haK, rfl⟩
          have hfa : f a ∈ UY n C := by
            by_contra hnot
            exact haK (hGY.2.1 k _ (hGY.1 n _ hCY).isClosed_compl hnot)
          exact ⟨a, subset_closure hfa, rfl⟩
        have hD_disj_CXE : Disjoint D (CX C ∪ E) := by
          rw [Set.disjoint_left]
          rintro x hxD (hxCX | hxE)
          · exact Set.disjoint_left.mp (hCX_disj_B n C hC) hxCX (hD_sub_B hxD)
          · obtain ⟨a, haD, rfl⟩ := hxD
            obtain ⟨b, hbE, hab⟩ := hxE
            have hEq : a = b := Subtype.ext hab.symm
            subst hEq
            exact Set.disjoint_left.mp hclWY_disj haD hbE
        -- `UX n C ⊆ Hsep GX (CX C ∪ E) D`!
        have hUX_sub : UX n C ⊆ Hsep GX (CX C ∪ E) D := by
          rintro x (⟨_, hxH⟩ | hxU)
          · exact Hsep_mono hGX hCX (hCX.union hEcl) hBcl hDcl subset_union_left hD_sub_B hxH
          · obtain ⟨k, _, hxH⟩ := mem_iUnion.mp hxU
            exact Hsep_mono hGX (hAnk_closed n k C hC) (hCX.union hEcl) hBcl hDcl
              ((hAnk_sub_E k).trans subset_union_right) hD_sub_B hxH
        let WX : Set X := Hsep GX D (CX C ∪ E) \ toX (f ⁻¹' WYᶜ)
        have hWXo : IsOpen WX :=
          (isOpen_Hsep hGX hDcl).sdiff (htoX_closed (hWYo.isClosed_compl.preimage hf))
        have hWcompat : ∀ (a : X) (ha : a ∈ A), a ∈ WX ↔ f ⟨a, ha⟩ ∈ WY := by
          intro a ha
          constructor
          · intro haWX
            by_contra hnot
            exact haWX.2 ⟨⟨a, ha⟩, hnot, rfl⟩
          · intro hfa
            refine ⟨subset_Hsep hGX hDcl (hCX.union hEcl) hD_disj_CXE ⟨⟨a, ha⟩, subset_closure hfa, rfl⟩, ?_⟩
            rintro ⟨b, hb, hab⟩
            have hEq : (⟨a, ha⟩ : A) = b := Subtype.ext hab.symm
            exact hb (hEq ▸ hfa)
        have hWZo : IsOpen (glueSet (A := A) WX WY) := glueSet_isOpen f hWXo hWYo hWcompat
        have hzn : Sum.inr y ∈ closure (GZ n C) := mem_iInter.mp hz n
        obtain ⟨w, hwWZ, hwGZ⟩ := mem_closure_iff.mp hzn _ hWZo hyWY
        cases w with
        | inl u =>
          exact Set.disjoint_left.mp (disjoint_Hsep hantiX D (CX C ∪ E)) hwWZ.1 (hUX_sub hwGZ)
        | inr v =>
          exact Set.disjoint_left.mp hclWY_disj (subset_closure hwWZ) (subset_closure hwGZ)
    · intro z hzC
      refine mem_iInter.mpr fun n => subset_closure ?_
      have hBcl : IsClosed (B n C) := hB_closed n C hC
      cases z with
      | inl x =>
        have hxCX : x.1 ∈ CX C := by
          classical
          simpa [CX, adjInX, x.2] using hzC
        exact Or.inl ⟨hGX.2.1 n _ hCX hxCX, subset_Hsep hGX hCX hBcl (hCX_disj_B n C hC) hxCX⟩
      | inr y =>
        exact hGY.2.1 n _ hCY hzC
  · -- Monotonicity of `GZ n`
    intro n C₁ C₂ hC₁ hC₂ hC₁₂ z hz
    have hCX₁ : IsClosed (CX C₁) := (adjTop_isClosed_iff f C₁).mp hC₁ |>.1
    have hCX₂ : IsClosed (CX C₂) := (adjTop_isClosed_iff f C₂).mp hC₂ |>.1
    have hCY₁ : IsClosed (CY C₁) := (adjTop_isClosed_iff f C₁).mp hC₁ |>.2
    have hCY₂ : IsClosed (CY C₂) := (adjTop_isClosed_iff f C₂).mp hC₂ |>.2
    have hCX₁₂ : CX C₁ ⊆ CX C₂ := preimage_mono hC₁₂
    have hCY₁₂ : CY C₁ ⊆ CY C₂ := preimage_mono hC₁₂
    have hUY₁₂ : UY n C₁ ⊆ UY n C₂ := hGY.2.2.2 n _ _ hCY₁ hCY₂ hCY₁₂
    have hB₂₁ : B n C₂ ⊆ B n C₁ := image_mono (preimage_mono (compl_subset_compl.mpr hUY₁₂))
    have hAnk₁₂ : ∀ k, Ank n k C₁ ⊆ Ank n k C₂ := fun k =>
      image_mono (preimage_mono (compl_subset_compl.mpr
        (hGY.2.2.2 k _ _ (hGY.1 n _ hCY₂).isClosed_compl (hGY.1 n _ hCY₁).isClosed_compl
          (compl_subset_compl.mpr hUY₁₂))))
    cases z with
    | inr y => exact hUY₁₂ hz
    | inl x =>
      rcases hz with ⟨hx1, hx2⟩ | hxU
      · exact Or.inl ⟨hGX.2.2.2 n _ _ hCX₁ hCX₂ hCX₁₂ hx1,
          Hsep_mono hGX hCX₁ hCX₂ (hB_closed n C₁ hC₁) (hB_closed n C₂ hC₂) hCX₁₂ hB₂₁ hx2⟩
      · obtain ⟨k, hx1, hx2⟩ := mem_iUnion.mp hxU
        exact Or.inr (mem_iUnion.mpr ⟨k,
          hGX.2.2.2 (n + k) _ _ (hAnk_closed n k C₁ hC₁) (hAnk_closed n k C₂ hC₂) (hAnk₁₂ k) hx1,
          Hsep_mono hGX (hAnk_closed n k C₁ hC₁) (hAnk_closed n k C₂ hC₂)
            (hB_closed n C₁ hC₁) (hB_closed n C₂ hC₂) (hAnk₁₂ k) hB₂₁ hx2⟩)

end Research.BorgesAdjunction
