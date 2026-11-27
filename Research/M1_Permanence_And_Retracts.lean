import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Bases
import Mathlib.SetTheory.Cardinal.Basic
import Targets.Defs
import Proofs.L_0001

/-!
# `M₁` & Stratifiable Permanence Theorems and Jones's Lemma

This standalone module proves:

1. **Nagata–Smirnov / Second-Countable `M₁` Criteria**:
   - `isM1_of_sigma_locallyFinite_basis`: every `T₃` space with a σ-locally-finite open
     base is `M₁` (via `Proofs.L_0001`).
   - `isM1_of_secondCountable_t3`: every second-countable `T₃` space is `M₁`.
2. **Closed-Open Continuous Image Permanence**:
   - `isM1_of_isClosedMap_isOpenMap`: every closed, open, continuous surjection from an
     `M₁` space onto a `T₃` space preserves `MSpace.IsM1`.
   - `isStratifiable_of_isClosedMap_isOpenMap`: every closed, open, continuous surjection
     from a stratifiable space onto a `T₁` space preserves `MSpace.IsStratifiable`
     (without requiring compact fibers).
3. **Homeomorphism Invariance**:
   - `isM1_of_homeomorph` & `isStratifiable_of_homeomorph`.
4. **Jones's Lemma** (`jones_lemma` & `not_normalSpace_of_dense_closedDiscrete`):
   - In any `NormalSpace X` with a dense subset `Q` and a closed discrete subset `D`,
     there is an injection `Set D ↪ Set Q` (hence `¬ NormalSpace X` whenever `#(Set Q) < #(Set D)`).
-/

namespace Research.M1Permanence

open Set Topology TopologicalSpace

/-! ## Part 1: σ-locally-finite and second-countable `M₁` criteria -/

/-- Every `T₃` space admitting a σ-locally-finite open base is `M₁`. -/
theorem isM1_of_sigma_locallyFinite_basis {X : Type} [TopologicalSpace X] [T3Space X]
    (𝓑' : ℕ → Set (Set X))
    (hlf : ∀ n, LocallyFinite (fun B : 𝓑' n => B.1))
    (hbasis : IsTopologicalBasis (⋃ n, 𝓑' n)) :
    MSpace.IsM1 X := by
  refine ⟨inferInstance, ⋃ n, 𝓑' n, hbasis, ⟨𝓑', fun n => ?_, rfl⟩⟩
  exact Proofs.L_0001.main X (𝓑' n) (hlf n)

/-- Every second-countable `T₃` space is `M₁`. -/
theorem isM1_of_secondCountable_t3 {X : Type} [TopologicalSpace X] [T3Space X]
    [SecondCountableTopology X] :
    MSpace.IsM1 X := by
  obtain ⟨𝓑, hB_cnt, _, hB_basis⟩ := exists_countable_basis X
  by_cases hne : 𝓑.Nonempty
  · obtain ⟨f, hf⟩ := hB_cnt.exists_eq_range hne
    let 𝓑' : ℕ → Set (Set X) := fun n => {f n}
    have hEq : 𝓑 = ⋃ n, 𝓑' n := by
      rw [hf]
      ext U
      simp [𝓑']
    refine ⟨inferInstance, 𝓑, hB_basis, ⟨𝓑', fun n 𝓖 h𝓖 => ?_, hEq⟩⟩
    by_cases hmem : f n ∈ 𝓖
    · have hGeq : 𝓖 = {f n} := Subset.antisymm h𝓖 (singleton_subset_iff.mpr hmem)
      subst hGeq; simp
    · have hGeq : 𝓖 = ∅ := eq_empty_iff_forall_notMem.mpr fun U hU =>
        hmem (mem_singleton_iff.mp (h𝓖 hU) ▸ hU)
      subst hGeq; simp
  · rw [not_nonempty_iff_eq_empty] at hne
    subst hne
    refine ⟨inferInstance, ∅, hB_basis, ⟨fun _ => ∅, fun _ 𝓖 h𝓖 => ?_, by simp⟩⟩
    have hGeq : 𝓖 = ∅ := subset_empty_iff.mp h𝓖
    subst hGeq; simp

/-! ## Part 2: Closed-open continuous images of `M₁` and stratifiable spaces -/

private lemma closure_image_eq_of_isClosedMap_continuous {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hcont : Continuous f) (hclosed : IsClosedMap f) (S : Set X) :
    closure (f '' S) = f '' closure S := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono subset_closure) (hclosed _ isClosed_closure)
  · exact image_closure_subset_closure_image hcont

/-- Closed, open, continuous surjections preserve `MSpace.IsM1` (onto `T₃` targets). -/
theorem isM1_of_isClosedMap_isOpenMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T3Space Y] (hM1 : MSpace.IsM1 X)
    {f : X → Y} (hcont : Continuous f) (hclosed : IsClosedMap f)
    (hopen : IsOpenMap f) (hsurj : Function.Surjective f) :
    MSpace.IsM1 Y := by
  obtain ⟨_, 𝓑, hB_basis, 𝓑', hB'_cp, hB_eq⟩ := hM1
  let 𝓒' : ℕ → Set (Set Y) := fun n => (fun B => f '' B) '' 𝓑' n
  have hC'_open : ∀ n, ∀ U ∈ 𝓒' n, IsOpen U := by
    rintro n _ ⟨B, hBn, rfl⟩
    have hBo : IsOpen B := hB_basis.isOpen (hB_eq ▸ mem_iUnion.mpr ⟨n, hBn⟩)
    exact hopen B hBo
  have hC'_cp : ∀ n, MSpace.ClosurePreserving (𝓒' n) := by
    intro n 𝓖 h𝓖
    let 𝓗 : Set (Set X) := { B ∈ 𝓑' n | f '' B ∈ 𝓖 }
    have hH_sub : 𝓗 ⊆ 𝓑' n := fun _ h => h.1
    have hG_eq : ⋃₀ 𝓖 = f '' (⋃₀ 𝓗) := by
      ext y
      constructor
      · rintro ⟨U, hUG, hyU⟩
        obtain ⟨B, hBn, rfl⟩ := h𝓖 hUG
        obtain ⟨x, hxB, rfl⟩ := hyU
        exact ⟨x, ⟨B, ⟨hBn, hUG⟩, hxB⟩, rfl⟩
      · rintro ⟨x, ⟨B, ⟨_, hBG⟩, hxB⟩, rfl⟩
        exact ⟨f '' B, hBG, ⟨x, hxB, rfl⟩⟩
    apply Subset.antisymm
    · rw [hG_eq, closure_image_eq_of_isClosedMap_continuous hcont hclosed, hB'_cp n 𝓗 hH_sub]
      rintro y ⟨x, ⟨_, ⟨B, ⟨_, hBG⟩, rfl⟩, hxB⟩, rfl⟩
      refine ⟨closure (f '' B), ⟨f '' B, hBG, rfl⟩, ?_⟩
      rw [closure_image_eq_of_isClosedMap_continuous hcont hclosed]
      exact ⟨x, hxB, rfl⟩
    · rintro y ⟨_, ⟨U, hUG, rfl⟩, hyU⟩
      exact closure_mono (subset_sUnion_of_mem hUG) hyU
  refine ⟨inferInstance, ⋃ n, 𝓒' n, ?_, ⟨𝓒', hC'_cp, rfl⟩⟩
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U hU
    obtain ⟨n, hUn⟩ := mem_iUnion.mp hU
    exact hC'_open n U hUn
  · intro y V hyV hVo
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨B, hB, hxB, hBsub⟩ :=
      hB_basis.exists_subset_of_mem_open hyV (hVo.preimage hcont)
    rw [hB_eq] at hB
    obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
    refine ⟨f '' B, mem_iUnion.mpr ⟨n, B, hBn, rfl⟩, ⟨x, hxB, rfl⟩, ?_⟩
    rintro _ ⟨z, hzB, rfl⟩
    exact hBsub hzB

/-- Closed, open, continuous surjections preserve `MSpace.IsStratifiable` (onto `T₁` targets),
without requiring compact fibers. -/
theorem isStratifiable_of_isClosedMap_isOpenMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space Y] (hStrat : MSpace.IsStratifiable X)
    {f : X → Y} (hcont : Continuous f) (hclosed : IsClosedMap f)
    (hopen : IsOpenMap f) (hsurj : Function.Surjective f) :
    MSpace.IsStratifiable Y := by
  obtain ⟨_, G, hGo, hGs, hGi, hGm⟩ := hStrat
  let GY : ℕ → Set Y → Set Y := fun n C => (f '' (G n (f ⁻¹' C))ᶜ)ᶜ
  refine ⟨inferInstance, GY, ?_, ?_, ?_, ?_⟩
  · intro n C hC
    exact (hclosed _ (hGo n _ (hC.preimage hcont)).isClosed_compl).isOpen_compl
  · intro n C hC y hyC
    rintro ⟨x, hxnot, rfl⟩
    exact hxnot (hGs n _ (hC.preimage hcont) hyC)
  · intro C hC
    have hpre : IsClosed (f ⁻¹' C) := hC.preimage hcont
    apply Subset.antisymm
    · intro y hy
      by_contra hyC
      obtain ⟨x, rfl⟩ := hsurj y
      have hxnot : x ∉ f ⁻¹' C := hyC
      rw [← hGi _ hpre, mem_iInter] at hxnot
      push Not at hxnot
      obtain ⟨n, hn⟩ := hxnot
      let U : Set X := (closure (G n (f ⁻¹' C)))ᶜ
      have hUo : IsOpen U := isClosed_closure.isOpen_compl
      have hfUo : IsOpen (f '' U) := hopen U hUo
      have hfx : f x ∈ f '' U := ⟨x, hn, rfl⟩
      have hyn : f x ∈ closure (GY n C) := mem_iInter.mp hy n
      obtain ⟨z, ⟨u, huU, rfl⟩, hzGY⟩ := mem_closure_iff.mp hyn (f '' U) hfUo hfx
      have huG : u ∈ G n (f ⁻¹' C) := by
        by_contra hunot
        exact hzGY ⟨u, hunot, rfl⟩
      exact huU (subset_closure huG)
    · intro y hyC
      refine mem_iInter.mpr fun n => subset_closure ?_
      rintro ⟨x, hxnot, rfl⟩
      exact hxnot (hGs n _ hpre hyC)
  · intro n C₁ C₂ hC₁ hC₂ hC₁₂
    exact compl_subset_compl.mpr (image_mono (compl_subset_compl.mpr
      (hGm n _ _ (hC₁.preimage hcont) (hC₂.preimage hcont) (preimage_mono hC₁₂))))

/-! ## Part 3: Homeomorphism invariance -/

/-- `MSpace.IsM1` is invariant under homeomorphism. -/
theorem isM1_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hM1 : MSpace.IsM1 X) : MSpace.IsM1 Y := by
  have : T3Space X := hM1.1
  have : T3Space Y := e.symm.isEmbedding.t3Space
  exact isM1_of_isClosedMap_isOpenMap hM1 e.continuous e.isClosedMap e.isOpenMap e.surjective

/-- `MSpace.IsStratifiable` is invariant under homeomorphism. -/
theorem isStratifiable_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hStrat : MSpace.IsStratifiable X) : MSpace.IsStratifiable Y := by
  have : T1Space X := hStrat.1
  have : T1Space Y := e.symm.isEmbedding.t1Space
  exact isStratifiable_of_isClosedMap_isOpenMap hStrat e.continuous e.isClosedMap e.isOpenMap e.surjective

/-! ## Part 4: Jones's Lemma (normality obstruction from dense + closed discrete sets) -/

/-- Jones's Lemma: In a normal space `X` with a dense subset `Q` and a closed discrete subset
`D` (every subset of `D` is closed), there exists an injection `Set D → Set Q`. -/
theorem jones_lemma {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {Q D : Set X} (hQ : Dense Q) (hD : ∀ S ⊆ D, IsClosed S) :
    ∃ φ : Set D → Set Q, Function.Injective φ := by
  have hsep : ∀ A : Set D, ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧
      ((Subtype.val : D → X) '' A) ⊆ U ∧
      ((Subtype.val : D → X) '' Aᶜ) ⊆ V ∧
      Disjoint U V := by
    intro A
    have hA_cl : IsClosed ((Subtype.val : D → X) '' A) := hD _ (Subtype.coe_image_subset D A)
    have hAc_cl : IsClosed ((Subtype.val : D → X) '' Aᶜ) := hD _ (Subtype.coe_image_subset D Aᶜ)
    have hdisj : Disjoint ((Subtype.val : D → X) '' A) ((Subtype.val : D → X) '' Aᶜ) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, haA, rfl⟩ ⟨b, hbAc, hab⟩
      have hEq : a = b := Subtype.ext hab.symm
      exact hbAc (hEq ▸ haA)
    exact normal_separation hA_cl hAc_cl hdisj
  choose U V hUo hVo hAU hAcV hUV using hsep
  let φ : Set D → Set Q := fun A => (Subtype.val : Q → X) ⁻¹' U A
  refine ⟨φ, fun A₁ A₂ hEq => ?_⟩
  ext d
  constructor
  · intro hd₁
    by_contra hd₂
    have hne_open : IsOpen (U A₁ ∩ V A₂) := (hUo A₁).inter (hVo A₂)
    have hd_in : d.1 ∈ U A₁ ∩ V A₂ :=
      ⟨hAU A₁ ⟨d, hd₁, rfl⟩, hAcV A₂ ⟨d, hd₂, rfl⟩⟩
    obtain ⟨q, hqUV, hqQ⟩ := dense_iff_inter_open.mp hQ (U A₁ ∩ V A₂) hne_open ⟨d.1, hd_in⟩
    have hq₁ : (⟨q, hqQ⟩ : Q) ∈ φ A₁ := hqUV.1
    rw [hEq] at hq₁
    exact Set.disjoint_left.mp (hUV A₂) hq₁ hqUV.2
  · intro hd₂
    by_contra hd₁
    have hne_open : IsOpen (U A₂ ∩ V A₁) := (hUo A₂).inter (hVo A₁)
    have hd_in : d.1 ∈ U A₂ ∩ V A₁ :=
      ⟨hAU A₂ ⟨d, hd₂, rfl⟩, hAcV A₁ ⟨d, hd₁, rfl⟩⟩
    obtain ⟨q, hqUV, hqQ⟩ := dense_iff_inter_open.mp hQ (U A₂ ∩ V A₁) hne_open ⟨d.1, hd_in⟩
    have hq₂ : (⟨q, hqQ⟩ : Q) ∈ φ A₂ := hqUV.1
    rw [← hEq] at hq₂
    exact Set.disjoint_left.mp (hUV A₁) hq₂ hqUV.2

/-- Cardinality form of Jones's Lemma: if `Q` is dense, `D` is closed discrete, and
`#(Set Q) < #(Set D)`, then `X` is not normal. -/
theorem not_normalSpace_of_dense_closedDiscrete {X : Type*} [TopologicalSpace X]
    {Q D : Set X} (hQ : Dense Q) (hD : ∀ S ⊆ D, IsClosed S)
    (hcard : Cardinal.mk (Set Q) < Cardinal.mk (Set D)) :
    ¬ NormalSpace X := by
  intro hN
  obtain ⟨φ, hφ⟩ := jones_lemma hQ hD
  exact not_le_of_gt hcard (Cardinal.mk_le_of_injective hφ)

end Research.M1Permanence
