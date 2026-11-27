import Targets.Defs
import Proofs.L_0004
import Proofs.L_0006

/-!
# Borges (1966) Theorem 7.2: Countable Weak-Topology Direct Limits of Stratifiable Spaces

Let `X` be a `T₁` space covered by an increasing sequence of closed subspaces
`F 0 ⊆ F 1 ⊆ F 2 ⊆ ⋯` with `⋃ m, F m = Set.univ`, carrying the **weak (coherent /
direct-limit) topology**: a set `U ⊆ X` is open iff `U ∩ F m` is open in `F m` for
every `m : ℕ`. (This includes countable CW-complexes, `ℝ^∞`, and `k_ω`-spaces
built from stratifiable strata.)

This standalone module proves:
- **`isStratifiable_of_weak_increasing_closed_cover`** (Borges 1966, Theorem 7.2):
  If every stratum `F m` is stratifiable, then `X` is stratifiable.
-/

namespace Research.BorgesDirectLimit

open Set Topology TopologicalSpace

/-! ## Part 1: Stratification helpers (`exists_antitone_stratification`, `Hsep`) -/

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

/-! ## Part 2: One-step canonical monotone extension between consecutive strata -/

section OneStep

variable {X : Type} [TopologicalSpace X]

/-- Inclusion `F m → F (m + 1)` given `F m ⊆ F (m + 1)`. -/
private def incl {A B : Set X} (hAB : A ⊆ B) (x : A) : B := ⟨x.1, hAB x.2⟩

omit [TopologicalSpace X] in
private lemma incl_injective {A B : Set X} (hAB : A ⊆ B) : Function.Injective (incl hAB) :=
  fun _ _ h => Subtype.ext (congrArg (Subtype.val : B → X) h)

private lemma incl_continuous {A B : Set X} (hAB : A ⊆ B) : Continuous (incl hAB) :=
  continuous_subtype_val.subtype_mk _

private lemma incl_isClosedMap {A B : Set X} (hAB : A ⊆ B) (hAcl : IsClosed A) :
    IsClosedMap (incl hAB) := by
  intro S hS
  obtain ⟨C, hCcl, rfl⟩ := isClosed_induced_iff.mp hS
  have hEq : incl hAB '' ((Subtype.val : A → X) ⁻¹' C) =
      (Subtype.val : B → X) ⁻¹' (A ∩ C) := by
    ext ⟨b, hb⟩
    simp only [incl, mem_image, mem_preimage, mem_inter_iff, Subtype.mk.injEq]
    constructor
    · rintro ⟨⟨a, ha⟩, haC, rfl⟩
      exact ⟨ha, haC⟩
    · rintro ⟨hbA, hbC⟩
      exact ⟨⟨b, hbA⟩, hbC, rfl⟩
  rw [hEq]
  exact (hAcl.inter hCcl).preimage continuous_subtype_val

/-- Canonical one-step monotone open extension of `U_A ⊆ A` to `B` (for closed `A ⊆ B`)
relative to a closed set `H ⊆ X` and level `n : ℕ`. -/
private def extStep {A B : Set X} (hAB : A ⊆ B)
    (GA : ℕ → Set A → Set A) (GB : ℕ → Set B → Set B)
    (n : ℕ) (H : Set X) (UA : Set A) : Set B :=
  let HB : Set B := (Subtype.val : B → X) ⁻¹' H
  let Bset : Set B := incl hAB '' UAᶜ
  let K : ℕ → Set A := fun k => (GA k UAᶜ)ᶜ
  let Ak : ℕ → Set B := fun k => incl hAB '' K k
  (GB n HB ∩ Hsep GB HB Bset) ∪ ⋃ k : ℕ, (GB (n + k) (Ak k) ∩ Hsep GB (Ak k) Bset)

private lemma extStep_isOpen {A B : Set X} (hAB : A ⊆ B) (hAcl : IsClosed A)
    {GA : ℕ → Set A → Set A} {GB : ℕ → Set B → Set B}
    (hGA : MSpace.IsStratification GA) (hGB : MSpace.IsStratification GB)
    (n : ℕ) {H : Set X} (hH : IsClosed H) {UA : Set A} (hUA : IsOpen UA) :
    IsOpen (extStep hAB GA GB n H UA) := by
  have hHB : IsClosed ((Subtype.val : B → X) ⁻¹' H) := hH.preimage continuous_subtype_val
  have hKcl : ∀ k, IsClosed (GA k UAᶜ)ᶜ := fun k => (hGA.1 k _ hUA.isClosed_compl).isClosed_compl
  have hAkcl : ∀ k, IsClosed (incl hAB '' (GA k UAᶜ)ᶜ) := fun k =>
    incl_isClosedMap hAB hAcl _ (hKcl k)
  refine ((hGB.1 n _ hHB).inter (isOpen_Hsep hGB hHB)).union ?_
  exact isOpen_iUnion fun k => (hGB.1 (n + k) _ (hAkcl k)).inter (isOpen_Hsep hGB (hAkcl k))

private lemma extStep_trace {A B : Set X} (hAB : A ⊆ B) (hAcl : IsClosed A)
    {GA : ℕ → Set A → Set A} {GB : ℕ → Set B → Set B}
    (hGA : MSpace.IsStratification GA) (hGB : MSpace.IsStratification GB)
    (n : ℕ) {H : Set X} (_hH : IsClosed H) {UA : Set A} (hUA : IsOpen UA) :
    incl hAB ⁻¹' (extStep hAB GA GB n H UA) = UA := by
  have hBcl : IsClosed (incl hAB '' UAᶜ) := incl_isClosedMap hAB hAcl _ hUA.isClosed_compl
  have hKcl : ∀ k, IsClosed (GA k UAᶜ)ᶜ := fun k => (hGA.1 k _ hUA.isClosed_compl).isClosed_compl
  have hAkcl : ∀ k, IsClosed (incl hAB '' (GA k UAᶜ)ᶜ) := fun k =>
    incl_isClosedMap hAB hAcl _ (hKcl k)
  ext a
  constructor
  · intro ha
    by_contra hnot
    have haB : incl hAB a ∈ incl hAB '' UAᶜ := ⟨a, hnot, rfl⟩
    rcases ha with ⟨_, haH⟩ | haU
    · exact Set.disjoint_left.mp (disjoint_Hsep_right hGB hBcl) haH haB
    · obtain ⟨k, _, haH⟩ := mem_iUnion.mp haU
      exact Set.disjoint_left.mp (disjoint_Hsep_right hGB hBcl) haH haB
  · intro haU
    have hnot : a ∉ UAᶜ := fun h => h haU
    rw [← hGA.2.2.1 _ hUA.isClosed_compl, mem_iInter] at hnot
    push Not at hnot
    obtain ⟨k, hk⟩ := hnot
    have haAk : incl hAB a ∈ incl hAB '' (GA k UAᶜ)ᶜ := ⟨a, fun h => hk (subset_closure h), rfl⟩
    have hdisj : Disjoint (incl hAB '' (GA k UAᶜ)ᶜ) (incl hAB '' UAᶜ) := by
      rw [Set.disjoint_left]
      rintro _ ⟨x, hxK, rfl⟩ ⟨y, hyU, hxy⟩
      have hEq : x = y := incl_injective hAB hxy.symm
      subst hEq
      exact hxK (hGA.2.1 k _ hUA.isClosed_compl hyU)
    exact Or.inr (mem_iUnion.mpr ⟨k, hGB.2.1 (n + k) _ (hAkcl k) haAk,
      subset_Hsep hGB (hAkcl k) hBcl hdisj haAk⟩)

private lemma extStep_subset_H {A B : Set X} (hAB : A ⊆ B) (hAcl : IsClosed A)
    {GA : ℕ → Set A → Set A} {GB : ℕ → Set B → Set B}
    (hGB : MSpace.IsStratification GB)
    (n : ℕ) {H : Set X} (hH : IsClosed H) {UA : Set A} (hUA : IsOpen UA)
    (hHA : (Subtype.val : A → X) ⁻¹' H ⊆ UA) :
    (Subtype.val : B → X) ⁻¹' H ⊆ extStep hAB GA GB n H UA := by
  have hHB : IsClosed ((Subtype.val : B → X) ⁻¹' H) := hH.preimage continuous_subtype_val
  have hBcl : IsClosed (incl hAB '' UAᶜ) := incl_isClosedMap hAB hAcl _ hUA.isClosed_compl
  have hdisj : Disjoint ((Subtype.val : B → X) ⁻¹' H) (incl hAB '' UAᶜ) := by
    rw [Set.disjoint_left]
    rintro b hbH ⟨a, haU, rfl⟩
    exact haU (hHA hbH)
  intro b hbH
  exact Or.inl ⟨hGB.2.1 n _ hHB hbH, subset_Hsep hGB hHB hBcl hdisj hbH⟩

private lemma extStep_mono {A B : Set X} (hAB : A ⊆ B) (hAcl : IsClosed A)
    {GA : ℕ → Set A → Set A} {GB : ℕ → Set B → Set B}
    (hGA : MSpace.IsStratification GA) (hGB : MSpace.IsStratification GB)
    (n : ℕ) {H₁ H₂ : Set X} (hH₁ : IsClosed H₁) (hH₂ : IsClosed H₂) (hH₁₂ : H₁ ⊆ H₂)
    {U₁ U₂ : Set A} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU₁₂ : U₁ ⊆ U₂) :
    extStep hAB GA GB n H₁ U₁ ⊆ extStep hAB GA GB n H₂ U₂ := by
  have hHB₁ : IsClosed ((Subtype.val : B → X) ⁻¹' H₁) := hH₁.preimage continuous_subtype_val
  have hHB₂ : IsClosed ((Subtype.val : B → X) ⁻¹' H₂) := hH₂.preimage continuous_subtype_val
  have hB₁ : IsClosed (incl hAB '' U₁ᶜ) := incl_isClosedMap hAB hAcl _ hU₁.isClosed_compl
  have hB₂ : IsClosed (incl hAB '' U₂ᶜ) := incl_isClosedMap hAB hAcl _ hU₂.isClosed_compl
  have hB₂₁ : incl hAB '' U₂ᶜ ⊆ incl hAB '' U₁ᶜ := image_mono (compl_subset_compl.mpr hU₁₂)
  have hAk₁ : ∀ k, IsClosed (incl hAB '' (GA k U₁ᶜ)ᶜ) := fun k =>
    incl_isClosedMap hAB hAcl _ (hGA.1 k _ hU₁.isClosed_compl).isClosed_compl
  have hAk₂ : ∀ k, IsClosed (incl hAB '' (GA k U₂ᶜ)ᶜ) := fun k =>
    incl_isClosedMap hAB hAcl _ (hGA.1 k _ hU₂.isClosed_compl).isClosed_compl
  have hAk₁₂ : ∀ k, incl hAB '' (GA k U₁ᶜ)ᶜ ⊆ incl hAB '' (GA k U₂ᶜ)ᶜ := fun k =>
    image_mono (compl_subset_compl.mpr (hGA.2.2.2 k _ _ hU₂.isClosed_compl hU₁.isClosed_compl
      (compl_subset_compl.mpr hU₁₂)))
  rintro b (⟨hb1, hb2⟩ | hbU)
  · exact Or.inl ⟨hGB.2.2.2 n _ _ hHB₁ hHB₂ (preimage_mono hH₁₂) hb1,
      Hsep_mono hGB hHB₁ hHB₂ hB₁ hB₂ (preimage_mono hH₁₂) hB₂₁ hb2⟩
  · obtain ⟨k, hb1, hb2⟩ := mem_iUnion.mp hbU
    exact Or.inr (mem_iUnion.mpr ⟨k,
      hGB.2.2.2 (n + k) _ _ (hAk₁ k) (hAk₂ k) (hAk₁₂ k) hb1,
      Hsep_mono hGB (hAk₁ k) (hAk₂ k) hB₁ hB₂ (hAk₁₂ k) hB₂₁ hb2⟩)

/-- Key separation extension lemma: if `WA ⊆ A` is open with `Disjoint (closure WA) (closure UA)`,
then there exists open `WB ⊆ B` with `incl⁻¹' WB = WA` and
`Disjoint (closure WB) (closure (extStep ... UA))`. -/
private lemma extStep_sep_extend {A B : Set X} (hAB : A ⊆ B) (hAcl : IsClosed A)
    (hStratB : MSpace.IsStratifiable B)
    {GA : ℕ → Set A → Set A} {GB : ℕ → Set B → Set B}
    (hGA : MSpace.IsStratification GA) (hGB : MSpace.IsStratification GB)
    (hantiB : ∀ n H, GB (n + 1) H ⊆ GB n H)
    (n : ℕ) {H : Set X} (hH : IsClosed H) {UA WA : Set A}
    (hUA : IsOpen UA) (hWA : IsOpen WA)
    (hHA : (Subtype.val : A → X) ⁻¹' H ⊆ UA)
    (hdisj_cl : Disjoint (closure WA) (closure UA)) :
    ∃ WB : Set B, IsOpen WB ∧ incl hAB ⁻¹' WB = WA ∧
      Disjoint (closure WB) (closure (extStep hAB GA GB n H UA)) := by
  have hNormB : NormalSpace B := (Proofs.L_0006.main B hStratB).1
  have hHB : IsClosed ((Subtype.val : B → X) ⁻¹' H) := hH.preimage continuous_subtype_val
  have hBcl : IsClosed (incl hAB '' UAᶜ) := incl_isClosedMap hAB hAcl _ hUA.isClosed_compl
  let D : Set B := incl hAB '' closure WA
  let E : Set B := incl hAB '' closure UA
  have hDcl : IsClosed D := incl_isClosedMap hAB hAcl _ isClosed_closure
  have hEcl : IsClosed E := incl_isClosedMap hAB hAcl _ isClosed_closure
  have hD_sub_B : D ⊆ incl hAB '' UAᶜ := by
    rintro _ ⟨a, haW, rfl⟩
    exact ⟨a, fun haU => Set.disjoint_left.mp hdisj_cl haW (subset_closure haU), rfl⟩
  have hAk_sub_E : ∀ k, incl hAB '' (GA k UAᶜ)ᶜ ⊆ E := by
    rintro k _ ⟨a, haK, rfl⟩
    have haU : a ∈ UA := by
      by_contra hnot
      exact haK (hGA.2.1 k _ hUA.isClosed_compl hnot)
    exact ⟨a, subset_closure haU, rfl⟩
  have hD_disj_HBE : Disjoint D ((Subtype.val : B → X) ⁻¹' H ∪ E) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, haW, rfl⟩ (haH | ⟨b, hbU, hab⟩)
    · exact Set.disjoint_left.mp hdisj_cl haW (subset_closure (hHA haH))
    · have hEq : a = b := incl_injective hAB hab.symm
      subst hEq
      exact Set.disjoint_left.mp hdisj_cl haW hbU
  have hExt_sub : extStep hAB GA GB n H UA ⊆ Hsep GB ((Subtype.val : B → X) ⁻¹' H ∪ E) D := by
    rintro b (⟨_, hbH⟩ | hbU)
    · exact Hsep_mono hGB hHB (hHB.union hEcl) hBcl hDcl subset_union_left hD_sub_B hbH
    · obtain ⟨k, _, hbH⟩ := mem_iUnion.mp hbU
      have hAkcl : IsClosed (incl hAB '' (GA k UAᶜ)ᶜ) :=
        incl_isClosedMap hAB hAcl _ (hGA.1 k _ hUA.isClosed_compl).isClosed_compl
      exact Hsep_mono hGB hAkcl (hHB.union hEcl) hBcl hDcl
        ((hAk_sub_E k).trans subset_union_right) hD_sub_B hbH
  -- `Hsep GB D (HB ∪ E)` is an open neighborhood of `D` disjoint from `extStep`, hence from `closure extStep`.
  have hD_disj_clExt : Disjoint D (closure (extStep hAB GA GB n H UA)) := by
    rw [Set.disjoint_left]
    intro b hbD hbcl
    have hbH : b ∈ Hsep GB D ((Subtype.val : B → X) ⁻¹' H ∪ E) :=
      subset_Hsep hGB hDcl (hHB.union hEcl) hD_disj_HBE hbD
    obtain ⟨c, hcH, hcExt⟩ :=
      mem_closure_iff.mp hbcl _ (isOpen_Hsep hGB hDcl) hbH
    exact Set.disjoint_left.mp (disjoint_Hsep hantiB D _) hcH (hExt_sub hcExt)
  obtain ⟨P, Q, hPo, hQo, hDP, hCQ, hPQ⟩ :=
    normal_separation hDcl isClosed_closure hD_disj_clExt
  let WB : Set B := P \ (incl hAB '' WAᶜ)
  have hWBo : IsOpen WB := hPo.sdiff (incl_isClosedMap hAB hAcl _ hWA.isClosed_compl)
  have hWB_trace : incl hAB ⁻¹' WB = WA := by
    ext a
    constructor
    · intro ha
      by_contra hnot
      exact ha.2 ⟨a, hnot, rfl⟩
    · intro haW
      refine ⟨hDP ⟨a, subset_closure haW, rfl⟩, ?_⟩
      rintro ⟨b, hbW, hab⟩
      have hEq : b = a := incl_injective hAB hab
      exact hbW (hEq ▸ haW)
  have hclWB_disj : Disjoint (closure WB) (closure (extStep hAB GA GB n H UA)) := by
    rw [Set.disjoint_left]
    intro b hb1 hb2
    have hbQ : b ∈ Q := hCQ hb2
    obtain ⟨c, hcQ, hcWB⟩ := mem_closure_iff.mp hb1 Q hQo hbQ
    exact Set.disjoint_left.mp hPQ hcWB.1 hcQ
  exact ⟨WB, hWBo, hWB_trace, hclWB_disj⟩

end OneStep

/-! ## Part 3: Borges (1966) Theorem 7.2 — Weak-Topology Direct Limit Theorem -/

/-- Borges (1966, Theorem 7.2): If `X` is a `T₁` space covered by an increasing sequence of
closed stratifiable subspaces `F 0 ⊆ F 1 ⊆ ⋯` with the weak topology
(`IsOpen U ↔ ∀ m, IsOpen (val ⁻¹' U)`), then `X` is stratifiable. -/
theorem isStratifiable_of_weak_increasing_closed_cover {X : Type} [TopologicalSpace X]
    [T1Space X] {F : ℕ → Set X}
    (hF_closed : ∀ m, IsClosed (F m))
    (hF_mono : ∀ m, F m ⊆ F (m + 1))
    (hF_cover : (⋃ m, F m) = Set.univ)
    (hF_weak : ∀ U : Set X, IsOpen U ↔ ∀ m, IsOpen ((Subtype.val : F m → X) ⁻¹' U))
    (hF_strat : ∀ m, MSpace.IsStratifiable (F m)) :
    MSpace.IsStratifiable X := by
  have hF_le : ∀ {a b : ℕ}, a ≤ b → F a ⊆ F b := by
    intro a b hab
    induction hab with
    | refl => exact Subset.rfl
    | step _ ih => exact ih.trans (hF_mono _)
  choose G₀ hG₀ using fun m => (hF_strat m).2
  choose G hG hanti using fun m => exists_antitone_stratification (hG₀ m)
  -- Recursive definition of `U n H m : Set (F m)`:
  let U : ℕ → Set X → (m : ℕ) → Set (F m) := fun n H m =>
    Nat.rec (G 0 n ((Subtype.val : F 0 → X) ⁻¹' H))
      (fun k Uk => extStep (hF_mono k) (G k) (G (k + 1)) n H Uk) m
  have hU_open : ∀ n H, IsClosed H → ∀ m, IsOpen (U n H m) := by
    intro n H hH m
    induction m with
    | zero => exact (hG 0).1 n _ (hH.preimage continuous_subtype_val)
    | succ k ih =>
      exact extStep_isOpen (hF_mono k) (hF_closed k) (hG k) (hG (k + 1)) n hH ih
  have hU_trace : ∀ n H, IsClosed H → ∀ m, incl (hF_mono m) ⁻¹' (U n H (m + 1)) = U n H m := by
    intro n H hH m
    exact extStep_trace (hF_mono m) (hF_closed m) (hG m) (hG (m + 1)) n hH (hU_open n H hH m)
  have hU_sub_H : ∀ n H, IsClosed H → ∀ m, (Subtype.val : F m → X) ⁻¹' H ⊆ U n H m := by
    intro n H hH m
    induction m with
    | zero => exact (hG 0).2.1 n _ (hH.preimage continuous_subtype_val)
    | succ k ih =>
      exact extStep_subset_H (hF_mono k) (hF_closed k) (hG (k + 1)) n hH (hU_open n H hH k) ih
  have hU_mono : ∀ n H₁ H₂, IsClosed H₁ → IsClosed H₂ → H₁ ⊆ H₂ → ∀ m, U n H₁ m ⊆ U n H₂ m := by
    intro n H₁ H₂ hH₁ hH₂ hH₁₂ m
    induction m with
    | zero =>
      exact (hG 0).2.2.2 n _ _ (hH₁.preimage continuous_subtype_val)
        (hH₂.preimage continuous_subtype_val) (preimage_mono hH₁₂)
    | succ k ih =>
      exact extStep_mono (hF_mono k) (hF_closed k) (hG k) (hG (k + 1)) n hH₁ hH₂ hH₁₂
        (hU_open n H₁ hH₁ k) (hU_open n H₂ hH₂ k) ih
  -- Assemble `GX n H := ⋃ m, val '' U n H m`.
  let GX : ℕ → Set X → Set X := fun n H => ⋃ m : ℕ, (Subtype.val : F m → X) '' U n H m
  -- Coherence helper: for any family `V : (m : ℕ) → Set (F m)` with `incl⁻¹' (V (m+1)) = V m`,
  -- `val ⁻¹' (⋃ m, val '' V m) = V k` for every `k`!
  have hcoh : ∀ (V : (m : ℕ) → Set (F m)),
      (∀ m, incl (hF_mono m) ⁻¹' (V (m + 1)) = V m) →
      ∀ k, (Subtype.val : F k → X) ⁻¹' (⋃ m, (Subtype.val : F m → X) '' V m) = V k := by
    intro V hV
    have hstep_le : ∀ {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) (x : F m₁) (y : F m₂),
        x.1 = y.1 → (x ∈ V m₁ ↔ y ∈ V m₂) := by
      intro m₁ m₂ h
      induction h with
      | refl =>
        intro x y hxy
        have : x = y := Subtype.ext hxy
        rw [this]
      | @step k hle ih =>
        intro x y hxy
        have hk : x.1 ∈ F k := by
          have : F m₁ ⊆ F k := by
            clear ih hxy y
            induction hle with
            | refl => exact Subset.rfl
            | step _ ih' => exact ih'.trans (hF_mono _)
          exact this x.2
        have h1 : x ∈ V m₁ ↔ (⟨x.1, hk⟩ : F k) ∈ V k := ih x ⟨x.1, hk⟩ rfl
        have h2 : incl (hF_mono k) ⟨x.1, hk⟩ = y := Subtype.ext hxy
        have h3 : (⟨x.1, hk⟩ : F k) ∈ V k ↔ y ∈ V (k + 1) := by
          rw [← hV k, mem_preimage, h2]
        exact h1.trans h3
    intro k
    ext x
    constructor
    · intro hx
      obtain ⟨m, y, hyV, hyx⟩ := mem_iUnion.mp hx
      rcases le_total k m with hkm | hmk
      · exact (hstep_le hkm x y hyx.symm).mpr hyV
      · exact (hstep_le hmk y x hyx).mp hyV
    · intro hxV
      exact mem_iUnion.mpr ⟨k, x, hxV, rfl⟩
  refine ⟨inferInstance, GX, ?_, ?_, ?_, ?_⟩
  · -- Openness of `GX n H`
    intro n H hH
    rw [hF_weak]
    intro m
    rw [hcoh (U n H) (hU_trace n H hH) m]
    exact hU_open n H hH m
  · -- `H ⊆ GX n H`
    intro n H hH x hxH
    have hx_cov : x ∈ (⋃ m, F m) := by rw [hF_cover]; trivial
    obtain ⟨m, hxm⟩ := mem_iUnion.mp hx_cov
    exact mem_iUnion.mpr ⟨m, ⟨x, hxm⟩, hU_sub_H n H hH m hxH, rfl⟩
  · -- `⋂ n, closure (GX n H) = H`
    intro H hH
    apply Subset.antisymm
    · intro x hx
      by_contra hxH
      classical
      have hex_m : ∃ m : ℕ, x ∈ F m := by
        have hx_cov : x ∈ (⋃ m, F m) := by rw [hF_cover]; trivial
        exact mem_iUnion.mp hx_cov
      obtain ⟨m₀, hxm₀, hm₀_min⟩ : ∃ m₀ : ℕ, x ∈ F m₀ ∧ ∀ j < m₀, x ∉ F j :=
        ⟨Nat.find hex_m, Nat.find_spec hex_m, fun j hj => Nat.find_min hex_m hj⟩
      -- Find `n : ℕ` and open `W₀ ⊆ F m₀` with `⟨x, hxm₀⟩ ∈ W₀`, `W₀ ∩ F j = ∅` for `j < m₀`,
      -- and `Disjoint (closure W₀) (closure (U n H m₀))`.
      have hex_nW : ∃ n : ℕ, ∃ W₀ : Set (F m₀),
          IsOpen W₀ ∧ (⟨x, hxm₀⟩ : F m₀) ∈ W₀ ∧
          (∀ j < m₀, ∀ y ∈ W₀, y.1 ∉ F j) ∧
          Disjoint (closure W₀) (closure (U n H m₀)) := by
        cases m₀ with
        | zero =>
          have hx_not_H0 : (⟨x, hxm₀⟩ : F 0) ∉ (Subtype.val : F 0 → X) ⁻¹' H := hxH
          rw [← (hG 0).2.2.1 _ (hH.preimage continuous_subtype_val), mem_iInter] at hx_not_H0
          push Not at hx_not_H0
          obtain ⟨n, hn⟩ := hx_not_H0
          have : T3Space (F 0) := (Proofs.L_0004.strat_to_m3 (F 0) (hF_strat 0)).1
          obtain ⟨t, ht_nhd, ht_cl, ht_sub⟩ :=
            exists_mem_nhds_isClosed_subset (isClosed_closure.isOpen_compl.mem_nhds hn)
          refine ⟨n, interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht_nhd,
            fun j hj => (Nat.not_lt_zero j hj).elim, ?_⟩
          rw [Set.disjoint_left]
          intro y hy1 hy2
          exact ht_sub (closure_minimal interior_subset ht_cl hy1) hy2
        | succ k =>
          have hx_not_Fk : x ∉ F k := hm₀_min k (Nat.lt_succ_self k)
          let A_k : Set (F (k + 1)) := Set.range (incl (hF_mono k))
          have hAk_cl : IsClosed A_k := by
            have hEq : A_k = incl (hF_mono k) '' Set.univ := by simp [A_k]
            rw [hEq]
            exact incl_isClosedMap (hF_mono k) (hF_closed k) _ isClosed_univ
          have hx_not_Ak : (⟨x, hxm₀⟩ : F (k + 1)) ∉ A_k := by
            rintro ⟨a, ha⟩
            have hax : a.1 = x := congrArg (Subtype.val : F (k + 1) → X) ha
            exact hx_not_Fk (hax ▸ a.2)
          have hx_not_Hk1 : (⟨x, hxm₀⟩ : F (k + 1)) ∉ (Subtype.val : F (k + 1) → X) ⁻¹' H := hxH
          rw [← (hG (k + 1)).2.2.1 _ (hH.preimage continuous_subtype_val), mem_iInter] at hx_not_Hk1
          rw [← (hG (k + 1)).2.2.1 _ hAk_cl, mem_iInter] at hx_not_Ak
          push Not at hx_not_Hk1 hx_not_Ak
          obtain ⟨n₁, hn₁⟩ := hx_not_Hk1
          obtain ⟨n₂, hn₂⟩ := hx_not_Ak
          let n := max n₁ n₂
          have hU_sub : U n H (k + 1) ⊆
              G (k + 1) n ((Subtype.val : F (k + 1) → X) ⁻¹' H) ∪ G (k + 1) n A_k := by
            rintro b (⟨hb1, _⟩ | hbU)
            · exact Or.inl hb1
            · obtain ⟨j, hb1, _⟩ := mem_iUnion.mp hbU
              have hAj_cl : IsClosed (incl (hF_mono k) '' (G k j (U n H k)ᶜ)ᶜ) :=
                incl_isClosedMap (hF_mono k) (hF_closed k) _
                  ((hG k).1 j _ (hU_open n H hH k).isClosed_compl).isClosed_compl
              have hAj_sub : incl (hF_mono k) '' (G k j (U n H k)ᶜ)ᶜ ⊆ A_k := by
                rintro _ ⟨a, _, rfl⟩; exact ⟨a, rfl⟩
              exact Or.inr (antitone_le (hanti (k + 1)) (Nat.le_add_right n j) A_k
                ((hG (k + 1)).2.2.2 (n + j) _ A_k hAj_cl hAk_cl hAj_sub hb1))
          have hx_not_clU : (⟨x, hxm₀⟩ : F (k + 1)) ∉ closure (U n H (k + 1)) := by
            intro hcl
            have hcl2 := closure_mono hU_sub hcl
            rw [closure_union] at hcl2
            rcases hcl2 with h1 | h2
            · exact hn₁ (closure_mono (antitone_le (hanti (k + 1)) (le_max_left _ _) _) h1)
            · exact hn₂ (closure_mono (antitone_le (hanti (k + 1)) (le_max_right _ _) _) h2)
          have : T3Space (F (k + 1)) := (Proofs.L_0004.strat_to_m3 (F (k + 1)) (hF_strat (k + 1))).1
          have hopen_nhd : IsOpen ((closure (U n H (k + 1)))ᶜ ∩ A_kᶜ) :=
            isClosed_closure.isOpen_compl.inter hAk_cl.isOpen_compl
          have hx_nhd : (⟨x, hxm₀⟩ : F (k + 1)) ∈ (closure (U n H (k + 1)))ᶜ ∩ A_kᶜ := by
            refine ⟨hx_not_clU, ?_⟩
            rintro ⟨a, ha⟩
            have hax : a.1 = x := congrArg (Subtype.val : F (k + 1) → X) ha
            exact hx_not_Fk (hax ▸ a.2)
          obtain ⟨t, ht_nhd, ht_cl, ht_sub⟩ :=
            exists_mem_nhds_isClosed_subset (hopen_nhd.mem_nhds hx_nhd)
          refine ⟨n, interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht_nhd, ?_, ?_⟩
          · intro j hj y hyW hyFj
            have hyAk : y ∈ A_k := ⟨⟨y.1, hF_le (Nat.le_of_lt_succ hj) hyFj⟩, rfl⟩
            exact (ht_sub (interior_subset hyW)).2 hyAk
          · rw [Set.disjoint_left]
            intro y hy1 hy2
            exact (ht_sub (closure_minimal interior_subset ht_cl hy1)).1 hy2
      obtain ⟨n, W₀, hW₀o, hxW₀, hW₀_miss, hW₀_disj⟩ := hex_nW
      -- Inductively extend `W₀` from `m₀` upward to all `m₀ + d`.
      let StepState : ℕ → Type := fun d =>
        { W : Set (F (m₀ + d)) // IsOpen W ∧ Disjoint (closure W) (closure (U n H (m₀ + d))) }
      let nextStep : ∀ d, StepState d → StepState (d + 1) := fun d st =>
        let hex := extStep_sep_extend (hF_mono (m₀ + d)) (hF_closed (m₀ + d))
          (hF_strat (m₀ + d + 1)) (hG (m₀ + d)) (hG (m₀ + d + 1)) (hanti (m₀ + d + 1))
          n hH (hU_open n H hH (m₀ + d)) st.2.1 (hU_sub_H n H hH (m₀ + d)) st.2.2
        ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2.2⟩
      let stateSeq : (d : ℕ) → StepState d := fun d =>
        Nat.rec ⟨W₀, hW₀o, hW₀_disj⟩ nextStep d
      have hstate_trace : ∀ d, incl (hF_mono (m₀ + d)) ⁻¹' (stateSeq (d + 1)).1 = (stateSeq d).1 := by
        intro d
        dsimp only [stateSeq, nextStep]
        exact (extStep_sep_extend (hF_mono (m₀ + d)) (hF_closed (m₀ + d))
          (hF_strat (m₀ + d + 1)) (hG (m₀ + d)) (hG (m₀ + d + 1)) (hanti (m₀ + d + 1))
          n hH (hU_open n H hH (m₀ + d)) (stateSeq d).2.1 (hU_sub_H n H hH (m₀ + d))
          (stateSeq d).2.2).choose_spec.2.1
      have hstate_le : ∀ {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) (u : F (m₀ + d₁)) (v : F (m₀ + d₂)),
          u.1 = v.1 → (u ∈ (stateSeq d₁).1 ↔ v ∈ (stateSeq d₂).1) := by
        intro d₁ d₂ h
        induction h with
        | refl =>
          intro u v huv
          have : u = v := Subtype.ext huv
          rw [this]
        | @step d hle ih =>
          intro u v huv
          have hd : u.1 ∈ F (m₀ + d) := by
            have : F (m₀ + d₁) ⊆ F (m₀ + d) := by
              clear ih huv v
              induction hle with
              | refl => exact Subset.rfl
              | step _ ih' => exact ih'.trans (hF_mono _)
            exact this u.2
          have h1 : u ∈ (stateSeq d₁).1 ↔ (⟨u.1, hd⟩ : F (m₀ + d)) ∈ (stateSeq d).1 :=
            ih u ⟨u.1, hd⟩ rfl
          have h2 : incl (hF_mono (m₀ + d)) ⟨u.1, hd⟩ = v := Subtype.ext huv
          have h3 : (⟨u.1, hd⟩ : F (m₀ + d)) ∈ (stateSeq d).1 ↔ v ∈ (stateSeq (d + 1)).1 := by
            rw [← hstate_trace d, mem_preimage, h2]
          exact h1.trans h3
      let W : Set X := ⋃ d : ℕ, (Subtype.val : F (m₀ + d) → X) '' (stateSeq d).1
      have hWo : IsOpen W := by
        rw [hF_weak]
        intro m
        by_cases hm : m₀ ≤ m
        · obtain ⟨d, rfl⟩ : ∃ d, m = m₀ + d := ⟨m - m₀, by omega⟩
          have hEq : (Subtype.val : F (m₀ + d) → X) ⁻¹' W = (stateSeq d).1 := by
            ext u
            constructor
            · intro hu
              obtain ⟨d', v, hv, hvu⟩ := mem_iUnion.mp hu
              rcases le_total d d' with hle | hle
              · exact (hstate_le hle u v hvu.symm).mpr hv
              · exact (hstate_le hle v u hvu).mp hv
            · intro hu
              exact mem_iUnion.mpr ⟨d, u, hu, rfl⟩
          rw [hEq]
          exact (stateSeq d).2.1
        · have hEq : (Subtype.val : F m → X) ⁻¹' W = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro u hu
            obtain ⟨d, v, hv, hvu⟩ := mem_iUnion.mp hu
            have hu0 : (⟨u.1, hF_le (by omega) u.2⟩ : F (m₀ + 0)) ∈ (stateSeq 0).1 :=
              (hstate_le (Nat.zero_le d) ⟨u.1, hF_le (by omega) u.2⟩ v hvu.symm).mpr hv
            exact hW₀_miss m (by omega) ⟨u.1, hF_le (by omega) u.2⟩ hu0 u.2
          rw [hEq]
          exact isOpen_empty
      have hxW : x ∈ W := mem_iUnion.mpr ⟨0, ⟨x, hxm₀⟩, hxW₀, rfl⟩
      have hW_disj_GX : Disjoint W (GX n H) := by
        rw [Set.disjoint_left]
        intro y hyW hyGX
        obtain ⟨d, u, huW, rfl⟩ := mem_iUnion.mp hyW
        have huGX : u ∈ (Subtype.val : F (m₀ + d) → X) ⁻¹' GX n H := hyGX
        rw [hcoh (U n H) (hU_trace n H hH) (m₀ + d)] at huGX
        exact Set.disjoint_left.mp ((stateSeq d).2.2.mono subset_closure subset_closure) huW huGX
      have hxn : x ∈ closure (GX n H) := mem_iInter.mp hx n
      obtain ⟨y, hyW, hyGX⟩ := mem_closure_iff.mp hxn W hWo hxW
      exact Set.disjoint_left.mp hW_disj_GX hyW hyGX
    · intro x hxH
      refine mem_iInter.mpr fun n => subset_closure ?_
      have hx_cov : x ∈ (⋃ m, F m) := by rw [hF_cover]; trivial
      obtain ⟨m, hxm⟩ := mem_iUnion.mp hx_cov
      exact mem_iUnion.mpr ⟨m, ⟨x, hxm⟩, hU_sub_H n H hH m hxH, rfl⟩
  · -- Monotonicity of `GX n`
    intro n H₁ H₂ hH₁ hH₂ hH₁₂
    exact iUnion_mono fun m => image_mono (hU_mono n H₁ H₂ hH₁ hH₂ hH₁₂ m)

end Research.BorgesDirectLimit
