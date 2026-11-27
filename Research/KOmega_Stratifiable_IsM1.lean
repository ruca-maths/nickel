import Mathlib.Data.Nat.Pairing
import Targets.Defs
import Proofs.L_0004
import Proofs.L_0006
import Proofs.L_0008

/-!
# $k_\omega$ Stratifiable Spaces (Countable Weak Limits of Compact Stratifiable Spaces) are $M_1$

Let `X` be a `T₁` space covered by an increasing sequence of **compact stratifiable**
subspaces `K 0 ⊆ K 1 ⊆ K 2 ⊆ ⋯` with `⋃ m, K m = Set.univ` and the **weak (coherent)
topology** (`IsOpen U ↔ ∀ m, IsOpen (val ⁻¹' U)`). This class includes `ℝ^∞`, sequential
fans `S_ω`, and all countable CW-complexes.

This standalone module proves:
1. **`dickson_fin_nat`** (Dickson's Lemma): every subset `S ⊆ (Fin d → ℕ)` has a finite
   subset `t ⊆ S` dominating `S` from below (`∀ f ∈ S, ∃ g ∈ t, ∀ i, g i ≤ f i`).
2. **`kOmega_isStratifiable`**: `X` is stratifiable (from the canonical monotone extension
   `extStep` and `extStep_sep_extend`).
3. **`kOmega_closed_hasCPOuterBaseSet`**: every closed subset `C ⊆ X` admits a
   closure-preserving open outer base `{ U f | f : ℕ → ℕ }`, proved via Dickson's Lemma
   on the finite-prefix dependence `(f 0, …, f r)` and exact closure trace
   `val⁻¹' (closure_X (U f)) = closure_{K r} (V f r)`.
4. **`isM1_of_kOmega_stratifiable`** (Ceder 1961 / Borges 1966 / Ito 1985):
   every $k_\omega$ stratifiable space is `M₁`.
-/

namespace Research.KOmegaM1

open Set Topology TopologicalSpace

/-! ## Part 1: Dickson's Lemma for `Fin d → ℕ` -/

/-- Dickson's Lemma: every subset `S ⊆ (Fin d → ℕ)` contains a finite subset `t ⊆ S`
such that every `f ∈ S` is coordinatewise `≥ g` for some `g ∈ t`. -/
theorem dickson_fin_nat : ∀ (d : ℕ) (S : Set (Fin d → ℕ)),
    ∃ t : Finset (Fin d → ℕ), (t : Set (Fin d → ℕ)) ⊆ S ∧
      ∀ f ∈ S, ∃ g ∈ t, ∀ i : Fin d, g i ≤ f i
  | 0, S => by
    classical
    by_cases hne : S.Nonempty
    · obtain ⟨f₀, hf₀⟩ := hne
      refine ⟨{f₀}, by simpa using hf₀, fun f _ => ⟨f₀, Finset.mem_singleton_self _, fun i => i.elim0⟩⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      subst hne
      exact ⟨∅, by simp, fun _ h => h.elim⟩
  | d + 1, S => by
    classical
    let proj : (Fin (d + 1) → ℕ) → (Fin d → ℕ) := fun f i => f i.castSucc
    obtain ⟨t₀, ht₀_sub, ht₀_cov⟩ := dickson_fin_nat d (proj '' S)
    choose wit hwit_S hwit_proj using fun (p : t₀) => ht₀_sub p.2
    let t_top : Finset (Fin (d + 1) → ℕ) := t₀.attach.image wit
    let M : ℕ := t_top.sup (fun f => f (Fin.last d))
    -- For each `v < M`, apply IH to the slice `{ f ∈ S | f (last d) = v }`.
    have hslice : ∀ v : ℕ, ∃ tv : Finset (Fin (d + 1) → ℕ),
        (tv : Set (Fin (d + 1) → ℕ)) ⊆ S ∧
        ∀ f ∈ S, f (Fin.last d) = v → ∃ g ∈ tv, ∀ i : Fin (d + 1), g i ≤ f i := by
      intro v
      let Sv : Set (Fin (d + 1) → ℕ) := { f ∈ S | f (Fin.last d) = v }
      obtain ⟨pv, hpv_sub, hpv_cov⟩ := dickson_fin_nat d (proj '' Sv)
      choose wv hwv_Sv hwv_proj using fun (p : pv) => hpv_sub p.2
      refine ⟨pv.attach.image wv, ?_, ?_⟩
      · intro g hg
        rcases Finset.mem_image.mp hg with ⟨p, _, rfl⟩
        exact (hwv_Sv p).1
      · intro f hfS hfv
        obtain ⟨q, hqv, hqle⟩ := hpv_cov (proj f) ⟨f, ⟨hfS, hfv⟩, rfl⟩
        refine ⟨wv ⟨q, hqv⟩, Finset.mem_image.mpr ⟨⟨q, hqv⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [(hwv_Sv ⟨q, hqv⟩).2, hfv]
        · have h1 : proj (wv ⟨q, hqv⟩) j = q j := congrFun (hwv_proj ⟨q, hqv⟩) j
          simpa [proj, h1] using hqle j
    choose tv htv_sub htv_cov using hslice
    let t : Finset (Fin (d + 1) → ℕ) := t_top ∪ (Finset.range M).biUnion tv
    refine ⟨t, ?_, ?_⟩
    · intro g hg
      rcases Finset.mem_union.mp hg with hg1 | hg2
      · rcases Finset.mem_image.mp hg1 with ⟨p, _, rfl⟩
        exact hwit_S p
      · rcases Finset.mem_biUnion.mp hg2 with ⟨v, _, hgv⟩
        exact htv_sub v hgv
    · intro f hfS
      by_cases hM : M ≤ f (Fin.last d)
      · obtain ⟨q, hqt₀, hqle⟩ := ht₀_cov (proj f) ⟨f, hfS, rfl⟩
        let g := wit ⟨q, hqt₀⟩
        have hg_top : g ∈ t_top := Finset.mem_image.mpr ⟨⟨q, hqt₀⟩, Finset.mem_attach _ _, rfl⟩
        refine ⟨g, Finset.mem_union_left _ hg_top, fun i => ?_⟩
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact le_trans (Finset.le_sup (f := fun h => h (Fin.last d)) hg_top) hM
        · have h1 : proj g j = q j := congrFun (hwit_proj ⟨q, hqt₀⟩) j
          simpa [proj, h1] using hqle j
      · have hlt : f (Fin.last d) < M := Nat.lt_of_not_ge hM
        obtain ⟨g, hgv, hgle⟩ := htv_cov (f (Fin.last d)) f hfS rfl
        exact ⟨g, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨f (Fin.last d),
          Finset.mem_range.mpr hlt, hgv⟩), hgle⟩

/-! ## Part 2: Stratification & monotone extension helpers -/

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

section OneStep

variable {X : Type} [TopologicalSpace X]

private def incl {A B : Set X} (hAB : A ⊆ B) (x : A) : B := ⟨x.1, hAB x.2⟩

omit [TopologicalSpace X] in
private lemma incl_injective {A B : Set X} (hAB : A ⊆ B) : Function.Injective (incl hAB) :=
  fun _ _ h => Subtype.ext (congrArg (Subtype.val : B → X) h)

private lemma incl_isClosedMap {A B : Set X} (hAB : A ⊆ B) (hAcl : IsClosed A) :
    IsClosedMap (incl hAB) := by
  intro S hS
  obtain ⟨C, hCcl, rfl⟩ := isClosed_induced_iff.mp hS
  have hEq : incl hAB '' ((Subtype.val : A → X) ⁻¹' C) =
      (Subtype.val : B → X) ⁻¹' (A ∩ C) := by
    ext ⟨b, hb⟩
    simp only [incl, mem_image, mem_preimage, mem_inter_iff, Subtype.mk.injEq]
    exact ⟨fun ⟨⟨a, ha⟩, haC, hba⟩ => hba ▸ ⟨ha, haC⟩, fun ⟨hbA, hbC⟩ => ⟨⟨b, hbA⟩, hbC, rfl⟩⟩
  rw [hEq]
  exact (hAcl.inter hCcl).preimage continuous_subtype_val

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
  have hAkcl : ∀ k, IsClosed (incl hAB '' (GA k UAᶜ)ᶜ) := fun k =>
    incl_isClosedMap hAB hAcl _ (hGA.1 k _ hUA.isClosed_compl).isClosed_compl
  refine ((hGB.1 n _ hHB).inter (isOpen_Hsep hGB hHB)).union ?_
  exact isOpen_iUnion fun k => (hGB.1 (n + k) _ (hAkcl k)).inter (isOpen_Hsep hGB (hAkcl k))

private lemma extStep_trace {A B : Set X} (hAB : A ⊆ B) (hAcl : IsClosed A)
    {GA : ℕ → Set A → Set A} {GB : ℕ → Set B → Set B}
    (hGA : MSpace.IsStratification GA) (hGB : MSpace.IsStratification GB)
    (n : ℕ) {H : Set X} {UA : Set A} (hUA : IsOpen UA) :
    incl hAB ⁻¹' (extStep hAB GA GB n H UA) = UA := by
  have hBcl : IsClosed (incl hAB '' UAᶜ) := incl_isClosedMap hAB hAcl _ hUA.isClosed_compl
  have hAkcl : ∀ k, IsClosed (incl hAB '' (GA k UAᶜ)ᶜ) := fun k =>
    incl_isClosedMap hAB hAcl _ (hGA.1 k _ hUA.isClosed_compl).isClosed_compl
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
      exact hxK (incl_injective hAB hxy.symm ▸ hGA.2.1 k _ hUA.isClosed_compl hyU)
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

private lemma extStep_mono_anti {A B : Set X} (hAB : A ⊆ B) (hAcl : IsClosed A)
    {GA : ℕ → Set A → Set A} {GB : ℕ → Set B → Set B}
    (hGA : MSpace.IsStratification GA) (hGB : MSpace.IsStratification GB)
    (hantiB : ∀ n H, GB (n + 1) H ⊆ GB n H)
    {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂)
    {H₁ H₂ : Set X} (hH₁ : IsClosed H₁) (hH₂ : IsClosed H₂) (hH₁₂ : H₁ ⊆ H₂)
    {U₁ U₂ : Set A} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU₁₂ : U₁ ⊆ U₂) :
    extStep hAB GA GB n₂ H₁ U₁ ⊆ extStep hAB GA GB n₁ H₂ U₂ := by
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
  · exact Or.inl ⟨antitone_le hantiB hn _ (hGB.2.2.2 n₂ _ _ hHB₁ hHB₂ (preimage_mono hH₁₂) hb1),
      Hsep_mono hGB hHB₁ hHB₂ hB₁ hB₂ (preimage_mono hH₁₂) hB₂₁ hb2⟩
  · obtain ⟨k, hb1, hb2⟩ := mem_iUnion.mp hbU
    exact Or.inr (mem_iUnion.mpr ⟨k,
      antitone_le hantiB (Nat.add_le_add_right hn k) _
        (hGB.2.2.2 (n₂ + k) _ _ (hAk₁ k) (hAk₂ k) (hAk₁₂ k) hb1),
      Hsep_mono hGB (hAk₁ k) (hAk₂ k) hB₁ hB₂ (hAk₁₂ k) hB₂₁ hb2⟩)

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
    · exact Set.disjoint_left.mp hdisj_cl haW (incl_injective hAB hab.symm ▸ hbU)
  have hExt_sub : extStep hAB GA GB n H UA ⊆ Hsep GB ((Subtype.val : B → X) ⁻¹' H ∪ E) D := by
    rintro b (⟨_, hbH⟩ | hbU)
    · exact Hsep_mono hGB hHB (hHB.union hEcl) hBcl hDcl subset_union_left hD_sub_B hbH
    · obtain ⟨k, _, hbH⟩ := mem_iUnion.mp hbU
      have hAkcl : IsClosed (incl hAB '' (GA k UAᶜ)ᶜ) :=
        incl_isClosedMap hAB hAcl _ (hGA.1 k _ hUA.isClosed_compl).isClosed_compl
      exact Hsep_mono hGB hAkcl (hHB.union hEcl) hBcl hDcl
        ((hAk_sub_E k).trans subset_union_right) hD_sub_B hbH
  have hD_disj_clExt : Disjoint D (closure (extStep hAB GA GB n H UA)) := by
    rw [Set.disjoint_left]
    intro b hbD hbcl
    have hbH : b ∈ Hsep GB D ((Subtype.val : B → X) ⁻¹' H ∪ E) :=
      subset_Hsep hGB hDcl (hHB.union hEcl) hD_disj_HBE hbD
    obtain ⟨c, hcH, hcExt⟩ := mem_closure_iff.mp hbcl _ (isOpen_Hsep hGB hDcl) hbH
    exact Set.disjoint_left.mp (disjoint_Hsep hantiB D _) hcH (hExt_sub hcExt)
  obtain ⟨P, Q, hPo, hQo, hDP, hCQ, hPQ⟩ :=
    normal_separation hDcl isClosed_closure hD_disj_clExt
  let WB : Set B := P \ (incl hAB '' WAᶜ)
  have hWBo : IsOpen WB := hPo.sdiff (incl_isClosedMap hAB hAcl _ hWA.isClosed_compl)
  have hWB_trace : incl hAB ⁻¹' WB = WA := by
    ext a
    constructor
    · intro ha; by_contra hnot; exact ha.2 ⟨a, hnot, rfl⟩
    · intro haW
      refine ⟨hDP ⟨a, subset_closure haW, rfl⟩, ?_⟩
      rintro ⟨b, hbW, hab⟩
      exact hbW (incl_injective hAB hab ▸ haW)
  have hclWB_disj : Disjoint (closure WB) (closure (extStep hAB GA GB n H UA)) := by
    rw [Set.disjoint_left]
    intro b hb1 hb2
    obtain ⟨c, hcQ, hcWB⟩ := mem_closure_iff.mp hb1 Q hQo (hCQ hb2)
    exact Set.disjoint_left.mp hPQ hcWB.1 hcQ
  exact ⟨WB, hWBo, hWB_trace, hclWB_disj⟩

/-- Compact shrinking for `G`: in a compact stratifiable space, for any closed `C ⊆ W` open,
there exists `n` with `closure (G n C) ⊆ W`. -/
private lemma compact_strat_shrink {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    {G : ℕ → Set Y → Set Y} (hG : MSpace.IsStratification G)
    (hanti : ∀ n H, G (n + 1) H ⊆ G n H)
    {C W : Set Y} (hC : IsClosed C) (hW : IsOpen W) (hCW : C ⊆ W) :
    ∃ n : ℕ, closure (G n C) ⊆ W := by
  let S : ℕ → Set Y := fun n => closure (G n C) \ W
  have hS_cl : ∀ n, IsClosed (S n) := fun n => isClosed_closure.sdiff hW
  have hS_anti : ∀ n, S (n + 1) ⊆ S n := fun n =>
    Set.sdiff_subset_sdiff_left (closure_mono (hanti n C))
  have hS_empty : (⋂ n, S n) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    have hyC : y ∈ ⋂ n, closure (G n C) := mem_iInter.mpr fun n => (mem_iInter.mp hy n).1
    rw [hG.2.2.1 C hC] at hyC
    exact (mem_iInter.mp hy 0).2 (hCW hyC)
  have hex : ∃ n, S n = ∅ := by
    by_contra hall
    push Not at hall
    have hne : (⋂ n, S n).Nonempty :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS_anti hall
        (hS_cl 0).isCompact hS_cl
    rw [hS_empty] at hne
    exact Set.not_nonempty_empty hne
  obtain ⟨n, hn⟩ := hex
  refine ⟨n, fun y hy => ?_⟩
  by_contra hyW
  have hyS : y ∈ S n := ⟨hy, hyW⟩
  rw [hn] at hyS
  exact hyS

end OneStep

/-! ## Part 3: Compact strata are closed, `X` is stratifiable, and every closed set has a CP open outer base -/

/-- Closure-preserving open outer base for a subset `F ⊆ X`. -/
def HasCPOuterBaseSet {X : Type*} [TopologicalSpace X] (F : Set X) : Prop :=
  ∃ 𝓤 : Set (Set X),
    (∀ U ∈ 𝓤, IsOpen U ∧ F ⊆ U) ∧
    MSpace.ClosurePreserving 𝓤 ∧
    (∀ W : Set X, IsOpen W → F ⊆ W → ∃ U ∈ 𝓤, U ⊆ W)

/-- Every `k_ω` stratifiable space is stratifiable, and every closed subset admits a
closure-preserving open outer base. -/
theorem kOmega_stratifiable_and_closed_outerBase {X : Type} [TopologicalSpace X] [T1Space X]
    {K : ℕ → Set X}
    (hK_comp : ∀ m, IsCompact (K m))
    (hK_mono : ∀ m, K m ⊆ K (m + 1))
    (hK_cover : (⋃ m, K m) = Set.univ)
    (hK_weak : ∀ U : Set X, IsOpen U ↔ ∀ m, IsOpen ((Subtype.val : K m → X) ⁻¹' U))
    (hK_strat : ∀ m, MSpace.IsStratifiable (K m)) :
    MSpace.IsStratifiable X ∧ ∀ C : Set X, IsClosed C → HasCPOuterBaseSet C := by
  have hK_le : ∀ {a b : ℕ}, a ≤ b → K a ⊆ K b := by
    intro a b hab
    induction hab with
    | refl => exact Subset.rfl
    | step _ ih => exact ih.trans (hK_mono _)
  -- Step 0: Every `K m` is closed in `X` (via `hK_weak` and compactness in `T₂` strata `K r`).
  have hK_closed : ∀ m, IsClosed (K m) := by
    intro m
    rw [← isOpen_compl_iff, hK_weak]
    intro r
    rw [Set.preimage_compl, isOpen_compl_iff]
    rcases le_total m r with hmr | hrm
    · have hT3_r : T3Space (K r) := (Proofs.L_0004.strat_to_m3 (K r) (hK_strat r)).1
      have hcomp_m : CompactSpace (K m) := isCompact_iff_compactSpace.mp (hK_comp m)
      have hEq : (Subtype.val : K r → X) ⁻¹' K m =
          (fun x : K m => (⟨x.1, hK_le hmr x.2⟩ : K r)) '' Set.univ := by
        ext ⟨y, hy⟩
        simp only [mem_preimage, mem_image, mem_univ, true_and, Subtype.mk.injEq]
        exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨⟨a, ha⟩, hay⟩ => hay ▸ ha⟩
      rw [hEq]
      have hcont : Continuous (fun x : K m => (⟨x.1, hK_le hmr x.2⟩ : K r)) :=
        continuous_subtype_val.subtype_mk _
      exact (isCompact_univ.image hcont).isClosed
    · have hEq : (Subtype.val : K r → X) ⁻¹' K m = Set.univ := by
        ext ⟨y, hy⟩; simp [hK_le hrm hy]
      rw [hEq]
      exact isClosed_univ
  choose G₀ hG₀ using fun m => (hK_strat m).2
  choose G hG hanti using fun m => exists_antitone_stratification (hG₀ m)
  -- Coherence helper for any sequence `V : (m : ℕ) → Set (K m)` with `incl⁻¹' (V (m+1)) = V m`.
  have hcoh : ∀ (V : (m : ℕ) → Set (K m)),
      (∀ m, incl (hK_mono m) ⁻¹' (V (m + 1)) = V m) →
      ∀ r, (Subtype.val : K r → X) ⁻¹' (⋃ m, (Subtype.val : K m → X) '' V m) = V r := by
    intro V hV
    have hstep : ∀ {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) (x : K m₁) (y : K m₂),
        x.1 = y.1 → (x ∈ V m₁ ↔ y ∈ V m₂) := by
      intro m₁ m₂ h
      induction h with
      | refl => intro x y hxy; rw [Subtype.ext hxy]
      | @step k hle ih =>
        intro x y hxy
        have hk : x.1 ∈ K k := hK_le hle x.2
        have h1 : x ∈ V m₁ ↔ (⟨x.1, hk⟩ : K k) ∈ V k := ih x ⟨x.1, hk⟩ rfl
        have h2 : incl (hK_mono k) ⟨x.1, hk⟩ = y := Subtype.ext hxy
        have h3 : (⟨x.1, hk⟩ : K k) ∈ V k ↔ y ∈ V (k + 1) := by rw [← hV k, mem_preimage, h2]
        exact h1.trans h3
    intro r
    ext x
    constructor
    · intro hx
      obtain ⟨m, y, hyV, hyx⟩ := mem_iUnion.mp hx
      rcases le_total r m with hrm | hmr
      · exact (hstep hrm x y hyx.symm).mpr hyV
      · exact (hstep hmr y x hyx).mp hyV
    · intro hxV
      exact mem_iUnion.mpr ⟨r, x, hxV, rfl⟩
  -- For ANY closed `C ⊆ X` and ANY `f : ℕ → ℕ`, define the coherent open neighborhood `U_seq C f`:
  let V_seq : Set X → (ℕ → ℕ) → (m : ℕ) → Set (K m) := fun C f m =>
    Nat.rec (G 0 (f 0) ((Subtype.val : K 0 → X) ⁻¹' C))
      (fun k Vk => extStep (hK_mono k) (G k) (G (k + 1)) (f (k + 1)) C Vk) m
  have hV_open : ∀ C, IsClosed C → ∀ f m, IsOpen (V_seq C f m) := by
    intro C hC f m
    induction m with
    | zero => exact (hG 0).1 (f 0) _ (hC.preimage continuous_subtype_val)
    | succ k ih => exact extStep_isOpen (hK_mono k) (hK_closed k) (hG k) (hG (k + 1)) (f (k + 1)) hC ih
  have hV_trace : ∀ C, IsClosed C → ∀ f m, incl (hK_mono m) ⁻¹' (V_seq C f (m + 1)) = V_seq C f m := by
    intro C hC f m
    exact extStep_trace (hK_mono m) (hK_closed m) (hG m) (hG (m + 1)) (f (m + 1)) (hV_open C hC f m)
  have hV_sub_C : ∀ C, IsClosed C → ∀ f m, (Subtype.val : K m → X) ⁻¹' C ⊆ V_seq C f m := by
    intro C hC f m
    induction m with
    | zero => exact (hG 0).2.1 (f 0) _ (hC.preimage continuous_subtype_val)
    | succ k ih =>
      exact extStep_subset_H (hK_mono k) (hK_closed k) (hG (k + 1)) (f (k + 1)) hC (hV_open C hC f k) ih
  have hV_mono_anti : ∀ {C₁ C₂ : Set X}, IsClosed C₁ → IsClosed C₂ → C₁ ⊆ C₂ →
      ∀ {f₁ f₂ : ℕ → ℕ} (r : ℕ), (∀ j ≤ r, f₁ j ≤ f₂ j) →
      V_seq C₁ f₂ r ⊆ V_seq C₂ f₁ r := by
    intro C₁ C₂ hC₁ hC₂ hC₁₂ f₁ f₂ r hle
    induction r with
    | zero =>
      exact ((hG 0).2.2.2 (f₂ 0) _ _ (hC₁.preimage continuous_subtype_val)
          (hC₂.preimage continuous_subtype_val) (preimage_mono hC₁₂)).trans
        (antitone_le (hanti 0) (hle 0 le_rfl) _)
    | succ k ih =>
      exact extStep_mono_anti (hK_mono k) (hK_closed k) (hG k) (hG (k + 1)) (hanti (k + 1))
        (hle (k + 1) le_rfl) hC₁ hC₂ hC₁₂ (hV_open C₁ hC₁ f₂ k) (hV_open C₂ hC₂ f₁ k)
        (ih fun j hj => hle j (Nat.le_succ_of_le hj))
  let U_seq : Set X → (ℕ → ℕ) → Set X := fun C f =>
    ⋃ m : ℕ, (Subtype.val : K m → X) '' V_seq C f m
  have hU_open : ∀ C, IsClosed C → ∀ f, IsOpen (U_seq C f) := by
    intro C hC f
    rw [hK_weak]
    intro m
    rw [hcoh (V_seq C f) (hV_trace C hC f) m]
    exact hV_open C hC f m
  have hU_sub_C : ∀ C, IsClosed C → ∀ f, C ⊆ U_seq C f := by
    intro C hC f x hxC
    have hx_cov : x ∈ (⋃ m, K m) := by rw [hK_cover]; trivial
    obtain ⟨m, hxm⟩ := mem_iUnion.mp hx_cov
    exact mem_iUnion.mpr ⟨m, ⟨x, hxm⟩, hV_sub_C C hC f m hxC, rfl⟩
  -- Key exact closure trace lemma: `val⁻¹' (closure_X (U_seq C f)) = closure_{K r} (V_seq C f r)`!
  have hU_closure_trace : ∀ C, IsClosed C → ∀ f r,
      (Subtype.val : K r → X) ⁻¹' closure (U_seq C f) = closure (V_seq C f r) := by
    intro C hC f r
    apply Subset.antisymm
    · intro x hx
      by_contra hxnot
      have hT3_r : T3Space (K r) := (Proofs.L_0004.strat_to_m3 (K r) (hK_strat r)).1
      obtain ⟨t, ht_nhd, ht_cl, ht_sub⟩ :=
        exists_mem_nhds_isClosed_subset (isClosed_closure.isOpen_compl.mem_nhds hxnot)
      let W₀ : Set (K r) := interior t
      have hW₀o : IsOpen W₀ := isOpen_interior
      have hxW₀ : x ∈ W₀ := mem_interior_iff_mem_nhds.mpr ht_nhd
      have hW₀_disj : Disjoint (closure W₀) (closure (V_seq C f r)) := by
        rw [Set.disjoint_left]
        intro y hy1 hy2
        exact ht_sub (closure_minimal interior_subset ht_cl hy1) hy2
      let StepState : ℕ → Type := fun d =>
        { W : Set (K (r + d)) // IsOpen W ∧ Disjoint (closure W) (closure (V_seq C f (r + d))) }
      let nextStep : ∀ d, StepState d → StepState (d + 1) := fun d st =>
        let hex := extStep_sep_extend (hK_mono (r + d)) (hK_closed (r + d))
          (hK_strat (r + d + 1)) (hG (r + d)) (hG (r + d + 1)) (hanti (r + d + 1))
          (f (r + d + 1)) hC (hV_open C hC f (r + d)) st.2.1 (hV_sub_C C hC f (r + d)) st.2.2
        ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2.2⟩
      let stateSeq : (d : ℕ) → StepState d := fun d =>
        Nat.rec ⟨W₀, hW₀o, hW₀_disj⟩ nextStep d
      have hstate_trace : ∀ d, incl (hK_mono (r + d)) ⁻¹' (stateSeq (d + 1)).1 = (stateSeq d).1 := by
        intro d
        dsimp only [stateSeq, nextStep]
        exact (extStep_sep_extend (hK_mono (r + d)) (hK_closed (r + d))
          (hK_strat (r + d + 1)) (hG (r + d)) (hG (r + d + 1)) (hanti (r + d + 1))
          (f (r + d + 1)) hC (hV_open C hC f (r + d)) (stateSeq d).2.1 (hV_sub_C C hC f (r + d))
          (stateSeq d).2.2).choose_spec.2.1
      have hstate_le : ∀ {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) (u : K (r + d₁)) (v : K (r + d₂)),
          u.1 = v.1 → (u ∈ (stateSeq d₁).1 ↔ v ∈ (stateSeq d₂).1) := by
        intro d₁ d₂ h
        induction h with
        | refl => intro u v huv; rw [Subtype.ext huv]
        | @step d hle ih =>
          intro u v huv
          have hd : u.1 ∈ K (r + d) := hK_le (Nat.add_le_add_left hle r) u.2
          have h1 : u ∈ (stateSeq d₁).1 ↔ (⟨u.1, hd⟩ : K (r + d)) ∈ (stateSeq d).1 :=
            ih u ⟨u.1, hd⟩ rfl
          have h2 : incl (hK_mono (r + d)) ⟨u.1, hd⟩ = v := Subtype.ext huv
          have h3 : (⟨u.1, hd⟩ : K (r + d)) ∈ (stateSeq d).1 ↔ v ∈ (stateSeq (d + 1)).1 := by
            rw [← hstate_trace d, mem_preimage, h2]
          exact h1.trans h3
      let W : Set X := ⋃ d : ℕ, (Subtype.val : K (r + d) → X) '' (stateSeq d).1
      have hWo : IsOpen W := by
        rw [hK_weak]
        intro m
        by_cases hm : r ≤ m
        · obtain ⟨d, rfl⟩ : ∃ d, m = r + d := ⟨m - r, by omega⟩
          have hEq : (Subtype.val : K (r + d) → X) ⁻¹' W = (stateSeq d).1 := by
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
        · have hle_r : m ≤ r := by omega
          have hEq : (Subtype.val : K m → X) ⁻¹' W =
              (fun u : K m => (⟨u.1, hK_le hle_r u.2⟩ : K r)) ⁻¹' W₀ := by
            ext u
            constructor
            · intro hu
              obtain ⟨d, v, hv, hvu⟩ := mem_iUnion.mp hu
              exact (hstate_le (Nat.zero_le d) ⟨u.1, hK_le hle_r u.2⟩ v hvu.symm).mpr hv
            · intro hu0
              exact mem_iUnion.mpr ⟨0, ⟨u.1, hK_le hle_r u.2⟩, hu0, rfl⟩
          rw [hEq]
          exact hW₀o.preimage (continuous_subtype_val.subtype_mk _)
      have hxW : x.1 ∈ W := mem_iUnion.mpr ⟨0, x, hxW₀, rfl⟩
      obtain ⟨y, hyW, hyU⟩ := mem_closure_iff.mp hx W hWo hxW
      obtain ⟨d, u, huW, rfl⟩ := mem_iUnion.mp hyW
      have huU : u ∈ (Subtype.val : K (r + d) → X) ⁻¹' U_seq C f := hyU
      rw [hcoh (V_seq C f) (hV_trace C hC f) (r + d)] at huU
      exact Set.disjoint_left.mp ((stateSeq d).2.2.mono subset_closure subset_closure) huW huU
    · intro x hx
      have h1 := (continuous_subtype_val (p := fun y : X => y ∈ K r)).closure_preimage_subset (U_seq C f)
      rw [hcoh (V_seq C f) (hV_trace C hC f) r] at h1
      exact h1 hx
  refine ⟨?_, ?_⟩
  · -- Part A: `X` is stratifiable via `GX n C := U_seq C (fun _ => n)`!
    let GX : ℕ → Set X → Set X := fun n C => U_seq C (fun _ => n)
    refine ⟨inferInstance, GX, fun n C hC => hU_open C hC (fun _ => n),
      fun n C hC => hU_sub_C C hC (fun _ => n), ?_, ?_⟩
    · intro C hC
      apply Subset.antisymm
      · intro x hx
        by_contra hxC
        classical
        have hex_m : ∃ m, x ∈ K m := by
          have : x ∈ (⋃ m, K m) := by rw [hK_cover]; trivial
          exact mem_iUnion.mp this
        obtain ⟨m₀, hxm₀, hm₀_min⟩ : ∃ m₀, x ∈ K m₀ ∧ ∀ j < m₀, x ∉ K j :=
          ⟨Nat.find hex_m, Nat.find_spec hex_m, fun j hj => Nat.find_min hex_m hj⟩
        cases m₀ with
        | zero =>
          have hx_not : (⟨x, hxm₀⟩ : K 0) ∉ (Subtype.val : K 0 → X) ⁻¹' C := hxC
          rw [← (hG 0).2.2.1 _ (hC.preimage continuous_subtype_val), mem_iInter] at hx_not
          push Not at hx_not
          obtain ⟨n, hn⟩ := hx_not
          have hxn : (⟨x, hxm₀⟩ : K 0) ∈ (Subtype.val : K 0 → X) ⁻¹' closure (GX n C) :=
            mem_iInter.mp hx n
          rw [hU_closure_trace C hC (fun _ => n) 0] at hxn
          exact hn hxn
        | succ k =>
          have hx_not_Kk : x ∉ K k := hm₀_min k (Nat.lt_succ_self k)
          let A_k : Set (K (k + 1)) := Set.range (incl (hK_mono k))
          have hAk_cl : IsClosed A_k := by
            have hEq : A_k = incl (hK_mono k) '' Set.univ := by simp [A_k]
            rw [hEq]; exact incl_isClosedMap (hK_mono k) (hK_closed k) _ isClosed_univ
          have hx_not_Ak : (⟨x, hxm₀⟩ : K (k + 1)) ∉ A_k := by
            rintro ⟨a, ha⟩
            have hax : a.1 = x := congrArg (Subtype.val : K (k + 1) → X) ha
            exact hx_not_Kk (hax ▸ a.2)
          have hx_not_Ck1 : (⟨x, hxm₀⟩ : K (k + 1)) ∉ (Subtype.val : K (k + 1) → X) ⁻¹' C := hxC
          rw [← (hG (k + 1)).2.2.1 _ (hC.preimage continuous_subtype_val), mem_iInter] at hx_not_Ck1
          rw [← (hG (k + 1)).2.2.1 _ hAk_cl, mem_iInter] at hx_not_Ak
          push Not at hx_not_Ck1 hx_not_Ak
          obtain ⟨n₁, hn₁⟩ := hx_not_Ck1
          obtain ⟨n₂, hn₂⟩ := hx_not_Ak
          let n := max n₁ n₂
          have hV_sub : V_seq C (fun _ => n) (k + 1) ⊆
              G (k + 1) n ((Subtype.val : K (k + 1) → X) ⁻¹' C) ∪ G (k + 1) n A_k := by
            rintro b (⟨hb1, _⟩ | hbU)
            · exact Or.inl hb1
            · obtain ⟨j, hb1, _⟩ := mem_iUnion.mp hbU
              have hAj_cl : IsClosed (incl (hK_mono k) '' (G k j (V_seq C (fun _ => n) k)ᶜ)ᶜ) :=
                incl_isClosedMap (hK_mono k) (hK_closed k) _
                  ((hG k).1 j _ (hV_open C hC (fun _ => n) k).isClosed_compl).isClosed_compl
              have hAj_sub : incl (hK_mono k) '' (G k j (V_seq C (fun _ => n) k)ᶜ)ᶜ ⊆ A_k := by
                rintro _ ⟨a, _, rfl⟩; exact ⟨a, rfl⟩
              exact Or.inr (antitone_le (hanti (k + 1)) (Nat.le_add_right n j) A_k
                ((hG (k + 1)).2.2.2 (n + j) _ A_k hAj_cl hAk_cl hAj_sub hb1))
          have hxn : (⟨x, hxm₀⟩ : K (k + 1)) ∈ (Subtype.val : K (k + 1) → X) ⁻¹' closure (GX n C) :=
            mem_iInter.mp hx n
          rw [hU_closure_trace C hC (fun _ => n) (k + 1)] at hxn
          have hcl2 := closure_mono hV_sub hxn
          rw [closure_union] at hcl2
          rcases hcl2 with h1 | h2
          · exact hn₁ (closure_mono (antitone_le (hanti (k + 1)) (le_max_left _ _) _) h1)
          · exact hn₂ (closure_mono (antitone_le (hanti (k + 1)) (le_max_right _ _) _) h2)
      · intro x hxC
        exact mem_iInter.mpr fun n => subset_closure (hU_sub_C C hC (fun _ => n) hxC)
    · intro n C₁ C₂ hC₁ hC₂ hC₁₂
      exact iUnion_mono fun m => image_mono (hV_mono_anti hC₁ hC₂ hC₁₂ (f₁ := fun _ => n) (f₂ := fun _ => n) m (fun _ _ => le_rfl))
  · -- Part B: Every closed `C ⊆ X` has the CP open outer base `Set.range (U_seq C)`!
    intro C hC
    refine ⟨Set.range (U_seq C), ?_, ?_, ?_⟩
    · rintro _ ⟨f, rfl⟩
      exact ⟨hU_open C hC f, hU_sub_C C hC f⟩
    · -- Closure-preserving via Dickson's Lemma + exact closure trace!
      intro 𝓖 h𝓖
      apply Subset.antisymm
      · -- Show `⋃₀ (closure '' 𝓖)` is CLOSED in `X` (using `hK_weak`), hence contains `closure (⋃₀ 𝓖)`!
        have hcl_union : IsClosed (⋃₀ (closure '' 𝓖)) := by
          rw [← isOpen_compl_iff, hK_weak]
          intro r
          rw [Set.preimage_compl, isOpen_compl_iff]
          let S : Set (ℕ → ℕ) := { f : ℕ → ℕ | U_seq C f ∈ 𝓖 }
          let proj : (ℕ → ℕ) → (Fin (r + 1) → ℕ) := fun f i => f i.1
          obtain ⟨t, ht_sub, ht_cov⟩ := dickson_fin_nat (r + 1) (proj '' S)
          choose wit hwit_S hwit_proj using fun (p : t) => ht_sub p.2
          have hEq : (Subtype.val : K r → X) ⁻¹' (⋃₀ (closure '' 𝓖)) =
              ⋃ p ∈ t.attach, closure (V_seq C (wit p) r) := by
            ext x
            constructor
            · rintro ⟨_, ⟨U, hUG, rfl⟩, hxU⟩
              obtain ⟨f, rfl⟩ := h𝓖 hUG
              have hxf : x ∈ closure (V_seq C f r) := by
                rw [← hU_closure_trace C hC f r]; exact hxU
              obtain ⟨q, hqt, hqle⟩ := ht_cov (proj f) ⟨f, hUG, rfl⟩
              have hle_r : ∀ j ≤ r, wit ⟨q, hqt⟩ j ≤ f j := by
                intro j hj
                have h1 : proj (wit ⟨q, hqt⟩) ⟨j, Nat.lt_succ_of_le hj⟩ = q ⟨j, Nat.lt_succ_of_le hj⟩ :=
                  congrFun (hwit_proj ⟨q, hqt⟩) ⟨j, Nat.lt_succ_of_le hj⟩
                simpa [proj, h1] using hqle ⟨j, Nat.lt_succ_of_le hj⟩
              have hsub : V_seq C f r ⊆ V_seq C (wit ⟨q, hqt⟩) r :=
                hV_mono_anti hC hC Subset.rfl r hle_r
              exact mem_iUnion₂.mpr ⟨⟨q, hqt⟩, Finset.mem_attach _ _, closure_mono hsub hxf⟩
            · intro hx
              obtain ⟨p, _, hxp⟩ := mem_iUnion₂.mp hx
              rw [← hU_closure_trace C hC (wit p) r] at hxp
              exact ⟨closure (U_seq C (wit p)), ⟨U_seq C (wit p), hwit_S p, rfl⟩, hxp⟩
          rw [hEq]
          exact isClosed_biUnion_finset fun p _ => isClosed_closure
        refine closure_minimal ?_ hcl_union
        rintro x ⟨U, hUG, hxU⟩
        exact ⟨closure U, ⟨U, hUG, rfl⟩, subset_closure hxU⟩
      · rintro x ⟨_, ⟨U, hUG, rfl⟩, hxU⟩
        exact closure_mono (subset_sUnion_of_mem hUG) hxU
    · -- Outer base property via compact shrinking at each stratum `K m`!
      intro W hWo hCW
      have hcomp_space : ∀ m, CompactSpace (K m) := fun m =>
        isCompact_iff_compactSpace.mp (hK_comp m)
      -- Inductively pick `(f m, V_m)` with `closure_{K m} V_m ⊆ val⁻¹' W`.
      let GoodState : ℕ → Type := fun m =>
        { p : ℕ × Set (K m) // IsOpen p.2 ∧ (Subtype.val : K m → X) ⁻¹' C ⊆ p.2 ∧
            closure p.2 ⊆ (Subtype.val : K m → X) ⁻¹' W }
      have hbase0 : ∃ n₀ : ℕ, closure (G 0 n₀ ((Subtype.val : K 0 → X) ⁻¹' C)) ⊆
          (Subtype.val : K 0 → X) ⁻¹' W :=
        compact_strat_shrink (hG 0) (hanti 0) (hC.preimage continuous_subtype_val)
          (hWo.preimage continuous_subtype_val) (preimage_mono hCW)
      let st0 : GoodState 0 :=
        ⟨(hbase0.choose, G 0 hbase0.choose ((Subtype.val : K 0 → X) ⁻¹' C)),
          (hG 0).1 _ _ (hC.preimage continuous_subtype_val),
          (hG 0).2.1 _ _ (hC.preimage continuous_subtype_val),
          hbase0.choose_spec⟩
      have hstep_ex : ∀ (m : ℕ) (st : GoodState m),
          ∃ n' : ℕ, closure (extStep (hK_mono m) (G m) (G (m + 1)) n' C st.1.2) ⊆
            (Subtype.val : K (m + 1) → X) ⁻¹' W := by
        intro m st
        let E : Set (K (m + 1)) :=
          (Subtype.val : K (m + 1) → X) ⁻¹' C ∪ incl (hK_mono m) '' closure st.1.2
        have hEcl : IsClosed E :=
          (hC.preimage continuous_subtype_val).union (incl_isClosedMap (hK_mono m) (hK_closed m) _ isClosed_closure)
        have hEW : E ⊆ (Subtype.val : K (m + 1) → X) ⁻¹' W := by
          rintro b (hbC | ⟨a, ha, rfl⟩)
          · exact hCW hbC
          · exact st.2.2.2 ha
        obtain ⟨n', hn'⟩ := compact_strat_shrink (hG (m + 1)) (hanti (m + 1)) hEcl
          (hWo.preimage continuous_subtype_val) hEW
        refine ⟨n', (closure_mono ?_).trans hn'⟩
        rintro b (⟨hb1, _⟩ | hbU)
        · exact (hG (m + 1)).2.2.2 n' _ E (hC.preimage continuous_subtype_val) hEcl
            subset_union_left hb1
        · obtain ⟨k, hb1, _⟩ := mem_iUnion.mp hbU
          have hAkcl : IsClosed (incl (hK_mono m) '' (G m k st.1.2ᶜ)ᶜ) :=
            incl_isClosedMap (hK_mono m) (hK_closed m) _
              ((hG m).1 k _ st.2.1.isClosed_compl).isClosed_compl
          have hAk_sub : incl (hK_mono m) '' (G m k st.1.2ᶜ)ᶜ ⊆ E := by
            rintro _ ⟨a, haK, rfl⟩
            have haU : a ∈ st.1.2 := by
              by_contra hnot
              exact haK ((hG m).2.1 k _ st.2.1.isClosed_compl hnot)
            exact Or.inr ⟨a, subset_closure haU, rfl⟩
          exact antitone_le (hanti (m + 1)) (Nat.le_add_right n' k) E
            ((hG (m + 1)).2.2.2 (n' + k) _ E hAkcl hEcl hAk_sub hb1)
      let stSeq : (m : ℕ) → GoodState m := fun m =>
        Nat.rec st0 (fun k stk =>
          let n' := (hstep_ex k stk).choose
          ⟨(n', extStep (hK_mono k) (G k) (G (k + 1)) n' C stk.1.2),
            extStep_isOpen (hK_mono k) (hK_closed k) (hG k) (hG (k + 1)) n' hC stk.2.1,
            extStep_subset_H (hK_mono k) (hK_closed k) (hG (k + 1)) n' hC stk.2.1 stk.2.2.1,
            (hstep_ex k stk).choose_spec⟩) m
      let f : ℕ → ℕ := fun m => (stSeq m).1.1
      have hV_eq : ∀ m, V_seq C f m = (stSeq m).1.2 := by
        intro m
        induction m with
        | zero => rfl
        | succ k ih =>
          change extStep (hK_mono k) (G k) (G (k + 1)) (f (k + 1)) C (V_seq C f k) = _
          rw [ih]
      refine ⟨U_seq C f, ⟨f, rfl⟩, ?_⟩
      rintro y hy
      obtain ⟨m, u, huV, rfl⟩ := mem_iUnion.mp hy
      rw [hV_eq m] at huV
      exact (stSeq m).2.2.2 (subset_closure huV)

/-! ## Part 4: Ito (1985) closed-set theorem ⇒ Every $k_\omega$ stratifiable space is `M₁` -/

private def IsDiscreteFam {X : Type*} [TopologicalSpace X] (𝓕 : Set (Set X)) : Prop :=
  ∀ z : X, ∃ W : Set X, IsOpen W ∧ z ∈ W ∧
    ∀ F₁ ∈ 𝓕, ∀ F₂ ∈ 𝓕, (W ∩ F₁).Nonempty → (W ∩ F₂).Nonempty → F₁ = F₂

private def IsDiscreteIndexed {X ι : Type*} [TopologicalSpace X] (W : ι → Set X) : Prop :=
  ∀ z : X, ∃ O : Set X, IsOpen O ∧ z ∈ O ∧
    ∀ i j : ι, (O ∩ W i).Nonempty → (O ∩ W j).Nonempty → i = j

private lemma isClosed_sUnion_of_isDiscreteFam {X : Type*} [TopologicalSpace X]
    {𝓕 𝓢 : Set (Set X)} (hdisc : IsDiscreteFam 𝓕) (hclosed : ∀ F ∈ 𝓕, IsClosed F)
    (hsub : 𝓢 ⊆ 𝓕) : IsClosed (⋃₀ 𝓢) := by
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
  obtain ⟨W, hWo, hzW, hWuniq⟩ := hdisc z
  by_cases hhit : ∃ F₀ ∈ 𝓢, (W ∩ F₀).Nonempty
  · obtain ⟨F₀, hF₀S, hne₀⟩ := hhit
    have hzF₀ : z ∉ F₀ := fun h => hz ⟨F₀, hF₀S, h⟩
    refine Filter.mem_of_superset ((hWo.sdiff (hclosed F₀ (hsub hF₀S))).mem_nhds ⟨hzW, hzF₀⟩) ?_
    rintro y ⟨hyW, hyF₀⟩ ⟨F, hFS, hyF⟩
    exact hyF₀ ((hWuniq F (hsub hFS) F₀ (hsub hF₀S) ⟨y, hyW, hyF⟩ hne₀) ▸ hyF)
  · refine Filter.mem_of_superset (hWo.mem_nhds hzW) ?_
    rintro y hyW ⟨F, hFS, hyF⟩
    exact hhit ⟨F, hFS, y, hyW, hyF⟩

private lemma stratifiable_discrete_open_expansion {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) {𝓕 : Set (Set X)}
    (hdisc : IsDiscreteFam 𝓕) (hclosed : ∀ F ∈ 𝓕, IsClosed F) :
    ∃ W : 𝓕 → Set X, (∀ F : 𝓕, IsOpen (W F)) ∧ (∀ F : 𝓕, F.1 ⊆ W F) ∧ IsDiscreteIndexed W := by
  obtain ⟨_, G₀, hG₀⟩ := hStrat
  obtain ⟨G, hG, hanti⟩ := exists_antitone_stratification hG₀
  let Fstar : 𝓕 → Set X := fun F => ⋃₀ (𝓕 \ {F.1})
  have hFstar_closed : ∀ F : 𝓕, IsClosed (Fstar F) := fun F =>
    isClosed_sUnion_of_isDiscreteFam hdisc hclosed Set.sdiff_subset
  have hFstar_disj : ∀ F : 𝓕, Disjoint F.1 (Fstar F) := by
    intro F; rw [Set.disjoint_left]
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
    exact (disjoint_Hsep hanti F₁.1 F₂.1).mono
      (Hsep_mono hG (hclosed F₁.1 F₁.2) (hclosed F₁.1 F₁.2) (hFstar_closed F₁) (hclosed F₂.1 F₂.2)
        Subset.rfl (Set.subset_sUnion_of_mem ⟨F₂.2, Ne.symm hval_ne⟩))
      (Hsep_mono hG (hclosed F₂.1 F₂.2) (hclosed F₂.1 F₂.2) (hFstar_closed F₂) (hclosed F₁.1 F₁.2)
        Subset.rfl (Set.subset_sUnion_of_mem ⟨F₁.2, hval_ne⟩))
  let E : Set X := ⋃₀ 𝓕
  have hE_closed : IsClosed E := isClosed_sUnion_of_isDiscreteFam hdisc hclosed Subset.rfl
  let U : Set X := ⋃ F : 𝓕, V F
  have hU_open : IsOpen U := isOpen_iUnion hV_open
  have hEU : Disjoint E Uᶜ := by
    rw [Set.disjoint_compl_right_iff_subset]
    rintro z ⟨F, hF, hzF⟩; exact mem_iUnion.mpr ⟨⟨F, hF⟩, hV_sub ⟨F, hF⟩ hzF⟩
  let O : Set X := Hsep G E Uᶜ
  have hO_open : IsOpen O := isOpen_Hsep hG hE_closed
  have hEO : E ⊆ O := subset_Hsep hG hE_closed hU_open.isClosed_compl hEU
  have hclO_sub_U : closure O ⊆ U := by
    intro z hz; by_contra hzU
    obtain ⟨y, hy2, hyO⟩ := mem_closure_iff.mp hz (Hsep G Uᶜ E) (isOpen_Hsep hG hU_open.isClosed_compl)
      (subset_Hsep hG hU_open.isClosed_compl hE_closed hEU.symm hzU)
    exact Set.disjoint_left.mp (disjoint_Hsep hanti E Uᶜ) hyO hy2
  refine ⟨fun F => V F ∩ O, fun F => (hV_open F).inter hO_open,
    fun F x hx => ⟨hV_sub F hx, hEO ⟨F.1, F.2, hx⟩⟩, fun z => ?_⟩
  by_cases hzU : z ∈ U
  · obtain ⟨F₀, hzF₀⟩ := mem_iUnion.mp hzU
    refine ⟨V F₀, hV_open F₀, hzF₀, fun F₁ F₂ ⟨y₁, hy₁V₀, hy₁W₁⟩ ⟨y₂, hy₂V₀, hy₂W₂⟩ => ?_⟩
    have h1 : F₁ = F₀ := by by_contra hne; exact Set.disjoint_left.mp (hV_disj F₁ F₀ hne) hy₁W₁.1 hy₁V₀
    have h2 : F₂ = F₀ := by by_contra hne; exact Set.disjoint_left.mp (hV_disj F₂ F₀ hne) hy₂W₂.1 hy₂V₀
    rw [h1, h2]
  · refine ⟨(closure O)ᶜ, isClosed_closure.isOpen_compl, fun h => hzU (hclO_sub_U h), ?_⟩
    intro F₁ _ ⟨y₁, hy₁c, hy₁W₁⟩ _; exact (hy₁c (subset_closure hy₁W₁.2)).elim

private lemma closurePreserving_image_closure {X : Type*} [TopologicalSpace X]
    {𝓑 : Set (Set X)} (hcp : MSpace.ClosurePreserving 𝓑) :
    MSpace.ClosurePreserving (closure '' 𝓑) := by
  intro 𝓖 h𝓖
  let 𝓗 : Set (Set X) := { B ∈ 𝓑 | closure B ∈ 𝓖 }
  have h1 : ⋃₀ 𝓖 ⊆ closure (⋃₀ 𝓗) := by
    rintro x ⟨C, hCG, hxC⟩; obtain ⟨B, hB, rfl⟩ := h𝓖 hCG
    exact closure_mono (Set.subset_sUnion_of_mem (⟨hB, hCG⟩ : B ∈ 𝓗)) hxC
  have h2 : ⋃₀ (closure '' 𝓗) ⊆ ⋃₀ (closure '' 𝓖) := by
    rintro x ⟨C, ⟨B, ⟨_, hBG⟩, rfl⟩, hxC⟩
    refine ⟨closure (closure B), ⟨closure B, hBG, rfl⟩, ?_⟩; rwa [closure_closure]
  apply Subset.antisymm
  · calc closure (⋃₀ 𝓖) ⊆ closure (closure (⋃₀ 𝓗)) := closure_mono h1
      _ = closure (⋃₀ 𝓗) := closure_closure
      _ = ⋃₀ (closure '' 𝓗) := hcp 𝓗 (fun _ h => h.1)
      _ ⊆ ⋃₀ (closure '' 𝓖) := h2
  · rintro x ⟨_, ⟨C, hCG, rfl⟩, hxC⟩; exact closure_mono (Set.subset_sUnion_of_mem hCG) hxC

private lemma isM1_of_stratifiable_closed_cp (X : Type) [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X)
    (hCP : ∀ F : Set X, IsClosed F → HasCPOuterBaseSet F) : MSpace.IsM1 X := by
  have hM3 : MSpace.IsM3 X := Proofs.L_0004.strat_to_m3 X hStrat
  have hM2 : MSpace.IsM2 X := Proofs.L_0008.main X hM3
  obtain ⟨hT3, 𝓑, hQB, 𝓑', hcp, rfl⟩ := hM2
  have : T3Space X := hT3
  have ⟨_, G, hGo, hGs, hGi, hGm⟩ := hStrat
  let K' : ℕ → Set (Set X) := fun m => closure '' 𝓑' m
  have hK_closed : ∀ m, ∀ K ∈ K' m, IsClosed K := by rintro m _ ⟨B, _, rfl⟩; exact isClosed_closure
  have hK_cp : ∀ m, MSpace.ClosurePreserving (K' m) := fun m => closurePreserving_image_closure (hcp m)
  let C : ℕ → X → Set X := fun m x => ⋂ K ∈ { K ∈ K' m | x ∈ K }, K
  let D : ℕ → X → Set X := fun m x => ⋃ K ∈ { K ∈ K' m | x ∉ K }, K
  have hC_closed : ∀ m x, IsClosed (C m x) := fun m x => isClosed_biInter fun K hK => hK_closed m K hK.1
  have hD_closed : ∀ m x, IsClosed (D m x) := by
    intro m x
    have hEq : D m x = ⋃₀ { K ∈ K' m | x ∉ K } := by ext y; simp [D]
    rw [hEq, ← closure_eq_iff_isClosed, hK_cp m { K ∈ K' m | x ∉ K } (fun _ h => h.1)]
    ext y
    constructor
    · rintro ⟨_, ⟨K, hK, rfl⟩, hy⟩; rw [(hK_closed m K hK.1).closure_eq] at hy; exact ⟨K, hK, hy⟩
    · rintro ⟨K, hK, hy⟩; exact ⟨closure K, ⟨K, hK, rfl⟩, subset_closure hy⟩
  let 𝓝_fam : ℕ → Set (Set X) := fun p =>
    Set.range (fun x => C (Nat.unpair p).1 x \ G (Nat.unpair p).2 (D (Nat.unpair p).1 x))
  have hN_closed : ∀ p, ∀ F ∈ 𝓝_fam p, IsClosed F := by
    rintro p _ ⟨x, rfl⟩; exact (hC_closed _ x).sdiff (hGo _ _ (hD_closed _ x))
  have hN_disc : ∀ p, IsDiscreteFam (𝓝_fam p) := by
    intro p z
    let m := (Nat.unpair p).1; let k := (Nat.unpair p).2
    let W : Set X := (D m z)ᶜ ∩ G k {z}
    have hWo : IsOpen W := (hD_closed m z).isOpen_compl.inter (hGo k {z} isClosed_singleton)
    have hzW : z ∈ W := ⟨fun hzD => by obtain ⟨K, hK, hzK⟩ := mem_iUnion₂.mp hzD; exact hK.2 hzK,
      hGs k {z} isClosed_singleton rfl⟩
    refine ⟨W, hWo, hzW, ?_⟩
    rintro _ ⟨x₁, rfl⟩ _ ⟨x₂, rfl⟩ ⟨y₁, hy₁W, hy₁A⟩ ⟨y₂, hy₂W, hy₂A⟩
    have hsame : ∀ x y, y ∈ W → y ∈ C m x \ G k (D m x) → (∀ K ∈ K' m, x ∈ K ↔ z ∈ K) := by
      intro x y hyW hyA K hKm
      constructor
      · intro hxK; by_contra hzK
        exact hyW.1 (mem_iUnion₂.mpr ⟨K, ⟨hKm, hzK⟩, mem_iInter₂.mp hyA.1 K ⟨hKm, hxK⟩⟩)
      · intro hzK; by_contra hxK
        exact hyA.2 (hGm k {z} (D m x) isClosed_singleton (hD_closed m x)
          (fun w hw => mem_singleton_iff.mp hw ▸ mem_iUnion₂.mpr ⟨K, ⟨hKm, hxK⟩, hzK⟩) hyW.2)
    have h1 := hsame x₁ y₁ hy₁W hy₁A; have h2 := hsame x₂ y₂ hy₂W hy₂A
    have hCeq : C m x₁ = C m x₂ := by
      ext w; simp only [C, mem_iInter, mem_ofPred_eq]
      exact ⟨fun h K ⟨hKm, hx₂K⟩ => h K ⟨hKm, (h1 K hKm).mpr ((h2 K hKm).mp hx₂K)⟩,
             fun h K ⟨hKm, hx₁K⟩ => h K ⟨hKm, (h2 K hKm).mpr ((h1 K hKm).mp hx₁K)⟩⟩
    have hDeq : D m x₁ = D m x₂ := by
      ext w; simp only [D, mem_iUnion, mem_ofPred_eq]
      exact ⟨fun ⟨K, ⟨hKm, hx₁K⟩, hwK⟩ => ⟨K, ⟨hKm, fun hx₂K => hx₁K ((h1 K hKm).mpr ((h2 K hKm).mp hx₂K))⟩, hwK⟩,
             fun ⟨K, ⟨hKm, hx₂K⟩, hwK⟩ => ⟨K, ⟨hKm, fun hx₁K => hx₂K ((h2 K hKm).mpr ((h1 K hKm).mp hx₁K))⟩, hwK⟩⟩
    show C m x₁ \ G k (D m x₁) = C m x₂ \ G k (D m x₂); rw [hCeq, hDeq]
  have hN_net : ∀ x : X, ∀ V : Set X, IsOpen V → x ∈ V → ∃ p, ∃ F ∈ 𝓝_fam p, x ∈ F ∧ F ⊆ V := by
    intro x V hVo hxV
    obtain ⟨t, ht, htc, htV⟩ := exists_mem_nhds_isClosed_subset (hVo.mem_nhds hxV)
    obtain ⟨B, hB, hxB, hBt⟩ := hQB x (interior t) isOpen_interior (mem_interior_iff_mem_nhds.mpr ht)
    obtain ⟨m, hBm⟩ := mem_iUnion.mp hB
    have hx_not_D : x ∉ D m x := fun hxD => by obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hxD; exact hK.2 hxK
    rw [← hGi (D m x) (hD_closed m x), mem_iInter] at hx_not_D; push Not at hx_not_D
    obtain ⟨k, hk⟩ := hx_not_D
    refine ⟨Nat.pair m k, C m x \ G k (D m x), by simp only [𝓝_fam, Nat.unpair_pair]; exact ⟨x, rfl⟩,
      ⟨mem_iInter₂.mpr fun K hK => hK.2, fun hxG => hk (subset_closure hxG)⟩, fun y hy => ?_⟩
    exact ((closure_minimal (hBt.trans interior_subset) htc).trans htV)
      (mem_iInter₂.mp hy.1 (closure B) ⟨⟨B, hBm, rfl⟩, subset_closure (interior_subset hxB)⟩)
  choose W hW_open hW_sub hW_disc using
    fun p => stratifiable_discrete_open_expansion hStrat (hN_disc p) (hN_closed p)
  choose 𝓤 hU_open hU_cp hU_base using fun (p : ℕ) (F : 𝓝_fam p) => hCP F.1 (hN_closed p F.1 F.2)
  let 𝓑'' : ℕ → Set (Set X) := fun p => { U : Set X | ∃ F : 𝓝_fam p, U ∈ 𝓤 p F ∧ U ⊆ W p F }
  have hB''_cp : ∀ p, MSpace.ClosurePreserving (𝓑'' p) := by
    intro p 𝓖 h𝓖; apply Subset.antisymm
    · intro z hz
      obtain ⟨O, hOo, hzO, hOuniq⟩ := hW_disc p z
      obtain ⟨y₀, hy₀O, ⟨U₀, hU₀G, hy₀U₀⟩⟩ := mem_closure_iff.mp hz O hOo hzO
      obtain ⟨F₀, _, hU₀_sub⟩ := h𝓖 hU₀G
      have hO_W₀ : (O ∩ W p F₀).Nonempty := ⟨y₀, hy₀O, hU₀_sub hy₀U₀⟩
      let 𝓖₀ : Set (Set X) := { U ∈ 𝓖 | U ∈ 𝓤 p F₀ ∧ U ⊆ W p F₀ }
      have hz_cl0 : z ∈ closure (⋃₀ 𝓖₀) := by
        rw [mem_closure_iff]; intro V hVo hzV
        obtain ⟨y, hyOV, ⟨U, hUG, hyU⟩⟩ := mem_closure_iff.mp hz (O ∩ V) (hOo.inter hVo) ⟨hzO, hzV⟩
        obtain ⟨F, hUF, hUW⟩ := h𝓖 hUG
        have hF_eq : F = F₀ := hOuniq F F₀ ⟨y, hyOV.1, hUW hyU⟩ hO_W₀
        subst hF_eq; exact ⟨y, hyOV.2, ⟨U, ⟨hUG, hUF, hUW⟩, hyU⟩⟩
      rw [hU_cp p F₀ 𝓖₀ (fun _ h => h.2.1)] at hz_cl0
      obtain ⟨_, ⟨U, hUG₀, rfl⟩, hzC⟩ := hz_cl0
      exact ⟨closure U, ⟨U, hUG₀.1, rfl⟩, hzC⟩
    · rintro z ⟨_, ⟨U, hUG, rfl⟩, hzU⟩; exact closure_mono (Set.subset_sUnion_of_mem hUG) hzU
  refine ⟨hT3, ⋃ p, 𝓑'' p, ?_, ⟨𝓑'', hB''_cp, rfl⟩⟩
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U hU; obtain ⟨p, F, hUF, _⟩ := mem_iUnion.mp hU; exact (hU_open p F U hUF).1
  · intro x V hxV hVo
    obtain ⟨p, F, hFp, hxF, hFV⟩ := hN_net x V hVo hxV
    obtain ⟨U, hUF, hU_sub⟩ := hU_base p ⟨F, hFp⟩ (V ∩ W p ⟨F, hFp⟩)
      (hVo.inter (hW_open p ⟨F, hFp⟩)) (fun y hy => ⟨hFV hy, hW_sub p ⟨F, hFp⟩ hy⟩)
    exact ⟨U, mem_iUnion.mpr ⟨p, ⟨F, hFp⟩, hUF, hU_sub.trans inter_subset_right⟩,
      (hU_open p ⟨F, hFp⟩ U hUF).2 hxF, hU_sub.trans inter_subset_left⟩

/-- Every $k_\omega$ stratifiable space (a `T₁` space carrying the weak topology from an
increasing countable cover by compact stratifiable subspaces — including `ℝ^∞`, `S_ω`,
and all countable CW-complexes) is `M₁`! -/
theorem isM1_of_kOmega_stratifiable {X : Type} [TopologicalSpace X] [T1Space X]
    {K : ℕ → Set X}
    (hK_comp : ∀ m, IsCompact (K m))
    (hK_mono : ∀ m, K m ⊆ K (m + 1))
    (hK_cover : (⋃ m, K m) = Set.univ)
    (hK_weak : ∀ U : Set X, IsOpen U ↔ ∀ m, IsOpen ((Subtype.val : K m → X) ⁻¹' U))
    (hK_strat : ∀ m, MSpace.IsStratifiable (K m)) :
    MSpace.IsM1 X := by
  obtain ⟨hStrat, hCP⟩ :=
    kOmega_stratifiable_and_closed_outerBase hK_comp hK_mono hK_cover hK_weak hK_strat
  exact isM1_of_stratifiable_closed_cp X hStrat hCP

end Research.KOmegaM1
