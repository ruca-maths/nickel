import Targets
import Defs.D_0001
import Defs.D_0010
import Proofs.L_0032

/-!
# Open-Subspace & Countable-Product Permanence for `HasCPOuterBase` and `HasSigmaCPLocalBase`

This file proves permanence theorems for `Defs.D_0001.HasCPOuterBase` and
`Defs.D_0010.HasSigmaCPLocalBase`:

1. `hasCPOuterBase_open_subspace` & `hasCPOuterBase_iff_open_subspace`:
   `HasCPOuterBase` is inherited by every open subspace (in ANY topological space)
   and is a purely local property in any `RegularSpace`.
2. `hasSigmaCPLocalBase_open_subspace` & `hasSigmaCPLocalBase_iff_open_subspace`:
   Same open-subspace localization for `HasSigmaCPLocalBase`.
3. `hasSigmaCPLocalBase_of_isClosedMap_isOpenMap`:
   `HasSigmaCPLocalBase` is preserved by continuous open closed maps.
4. `hasSigmaCPLocalBase_prod` & `hasSigmaCPLocalBase_countable_pi`:
   `HasSigmaCPLocalBase` is preserved by finite and countable products `∀ n : ℕ, X n`.
5. `hasCPOuterBase_countable_pi_of_clopen_gDelta`:
   In a countable product of spaces each having `HasSigmaCPLocalBase (x n)` and a
   clopen `G_δ` sequence at `x n`, the product point `x` admits a single-layer
   `HasCPOuterBase x` (via `Proofs.L_0032`).
-/

namespace Research.ChenWangSigmaCPPermanence

open MSpace Set Topology

section OpenSubspace

variable {X : Type*} [TopologicalSpace X]

/-- In ANY topological space, `HasCPOuterBase` is inherited by every open subspace. -/
theorem hasCPOuterBase_open_subspace {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    (hcp : Defs.D_0001.HasCPOuterBase x) :
    Defs.D_0001.HasCPOuterBase (⟨x, hx⟩ : U) := by
  obtain ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩ := hcp
  let 𝓥U : Set (Set U) := { S | ∃ V ∈ 𝓥, V ⊆ U ∧ S = ((↑) : U → X) ⁻¹' V }
  refine ⟨𝓥U, ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, _, rfl⟩
    exact ⟨(h𝓥_open V hV).1.preimage continuous_subtype_val, (h𝓥_open V hV).2⟩
  · intro W hW hxW
    have hWX : IsOpen (((↑) : U → X) '' W) := hU.isOpenMap_subtype_val W hW
    obtain ⟨V, hV, hVW⟩ := h𝓥_base _ hWX ⟨⟨x, hx⟩, hxW, rfl⟩
    have hVU : V ⊆ U := hVW.trans (by rintro _ ⟨y, _, rfl⟩; exact y.2)
    refine ⟨((↑) : U → X) ⁻¹' V, ⟨V, hV, hVU, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨y', hy'W, heq⟩ := hVW hy
    exact (Subtype.ext heq.symm) ▸ hy'W
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      let 𝓖X : Set (Set X) := { V ∈ 𝓥 | V ⊆ U ∧ ((↑) : U → X) ⁻¹' V ∈ 𝓖 }
      have hzX : (z : X) ∈ closure (⋃₀ 𝓖X) := by
        rw [mem_closure_iff]
        intro O hO hzO
        rw [mem_closure_iff] at hz
        obtain ⟨w, hwO, S, hS𝓖, hwS⟩ :=
          hz (((↑) : U → X) ⁻¹' O) (hO.preimage continuous_subtype_val) hzO
        obtain ⟨V, hV, hVU, rfl⟩ := h𝓖 hS𝓖
        exact ⟨(w : X), hwO, V, ⟨hV, hVU, hS𝓖⟩, hwS⟩
      rw [h𝓥_cp 𝓖X (fun V hV => hV.1)] at hzX
      obtain ⟨_, ⟨V, ⟨_, hVU, hVG⟩, rfl⟩, hzV⟩ := hzX
      refine ⟨closure (((↑) : U → X) ⁻¹' V), mem_image_of_mem _ hVG, ?_⟩
      rw [mem_closure_iff]
      intro O hO hzO
      have hOX : IsOpen (((↑) : U → X) '' O) := hU.isOpenMap_subtype_val O hO
      rw [mem_closure_iff] at hzV
      obtain ⟨y, ⟨w, hwO, rfl⟩, hwV⟩ := hzV _ hOX ⟨z, hzO, rfl⟩
      exact ⟨w, hwO, hwV⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- In any `RegularSpace`, `HasCPOuterBase x` is equivalent to `HasCPOuterBase ⟨x, hx⟩`
in any open neighborhood `U` of `x`. -/
theorem hasCPOuterBase_iff_open_subspace [RegularSpace X] {U : Set X} (hU : IsOpen U)
    {x : X} (hx : x ∈ U) :
    Defs.D_0001.HasCPOuterBase x ↔ Defs.D_0001.HasCPOuterBase (⟨x, hx⟩ : U) := by
  refine ⟨hasCPOuterBase_open_subspace hU hx, ?_⟩
  rintro ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩
  obtain ⟨K, hKnhds, hKclosed, hKU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hx)
  obtain ⟨W₀, hW₀K, hW₀open, hxW₀⟩ := mem_nhds_iff.mp hKnhds
  let 𝓥X : Set (Set X) :=
    { S | ∃ V ∈ 𝓥, ((↑) : U → X) '' V ⊆ W₀ ∧ S = ((↑) : U → X) '' V }
  refine ⟨𝓥X, ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, _, rfl⟩
    exact ⟨hU.isOpenMap_subtype_val V (h𝓥_open V hV).1, ⟨⟨x, hx⟩, (h𝓥_open V hV).2, rfl⟩⟩
  · intro O hO hxO
    let OW : Set U := ((↑) : U → X) ⁻¹' (O ∩ W₀)
    obtain ⟨V, hV, hVOW⟩ :=
      h𝓥_base OW ((hO.inter hW₀open).preimage continuous_subtype_val) ⟨hxO, hxW₀⟩
    have hVW₀ : ((↑) : U → X) '' V ⊆ W₀ := by
      rintro _ ⟨y, hyV, rfl⟩; exact (hVOW hyV).2
    refine ⟨((↑) : U → X) '' V, ⟨V, hV, hVW₀, rfl⟩, ?_⟩
    rintro _ ⟨y, hyV, rfl⟩; exact (hVOW hyV).1
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      have hsubK : ⋃₀ 𝓖 ⊆ K := by
        rintro y ⟨S, hS𝓖, hyS⟩
        obtain ⟨V, _, hVW₀, rfl⟩ := h𝓖 hS𝓖
        exact hW₀K (hVW₀ hyS)
      have hzU : z ∈ U := hKU (hKclosed.closure_subset (closure_mono hsubK hz))
      let 𝓖U : Set (Set U) := { V ∈ 𝓥 | ((↑) : U → X) '' V ⊆ W₀ ∧ ((↑) : U → X) '' V ∈ 𝓖 }
      have hz_sub : (⟨z, hzU⟩ : U) ∈ closure (⋃₀ 𝓖U) := by
        rw [mem_closure_iff]
        intro O hO hzO
        have hOX : IsOpen (((↑) : U → X) '' O) := hU.isOpenMap_subtype_val O hO
        rw [mem_closure_iff] at hz
        obtain ⟨y, ⟨w, hwO, rfl⟩, S, hS𝓖, hwS⟩ := hz _ hOX ⟨⟨z, hzU⟩, hzO, rfl⟩
        obtain ⟨V, hV, hVW₀, rfl⟩ := h𝓖 hS𝓖
        obtain ⟨w', hw'V, heq⟩ := hwS
        have hwV : w ∈ V := (Subtype.ext heq.symm) ▸ hw'V
        exact ⟨w, hwO, V, ⟨hV, hVW₀, hS𝓖⟩, hwV⟩
      rw [h𝓥_cp 𝓖U (fun V hV => hV.1)] at hz_sub
      obtain ⟨_, ⟨V, ⟨_, _, hVG⟩, rfl⟩, hzV⟩ := hz_sub
      refine ⟨closure (((↑) : U → X) '' V), mem_image_of_mem _ hVG, ?_⟩
      rw [mem_closure_iff]
      intro O hO hzO
      rw [mem_closure_iff] at hzV
      obtain ⟨w, hwO, hwV⟩ :=
        hzV (((↑) : U → X) ⁻¹' O) (hO.preimage continuous_subtype_val) hzO
      exact ⟨(w : X), hwO, w, hwV, rfl⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- In ANY topological space, `HasSigmaCPLocalBase` is inherited by every open subspace. -/
theorem hasSigmaCPLocalBase_open_subspace {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    (hsig : Defs.D_0010.HasSigmaCPLocalBase x) :
    Defs.D_0010.HasSigmaCPLocalBase (⟨x, hx⟩ : U) := by
  obtain ⟨𝓑, h𝓑_open, h𝓑_cp, h𝓑_base⟩ := hsig
  let 𝓑U : ℕ → Set (Set U) := fun n =>
    { S | ∃ V ∈ 𝓑 n, V ⊆ U ∧ S = ((↑) : U → X) ⁻¹' V }
  refine ⟨𝓑U, ?_, ?_, ?_⟩
  · rintro n _ ⟨V, hV, _, rfl⟩
    exact ⟨(h𝓑_open n V hV).1.preimage continuous_subtype_val, (h𝓑_open n V hV).2⟩
  · intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      let 𝓖X : Set (Set X) := { V ∈ 𝓑 n | V ⊆ U ∧ ((↑) : U → X) ⁻¹' V ∈ 𝓖 }
      have hzX : (z : X) ∈ closure (⋃₀ 𝓖X) := by
        rw [mem_closure_iff]
        intro O hO hzO
        rw [mem_closure_iff] at hz
        obtain ⟨w, hwO, S, hS𝓖, hwS⟩ :=
          hz (((↑) : U → X) ⁻¹' O) (hO.preimage continuous_subtype_val) hzO
        obtain ⟨V, hV, hVU, rfl⟩ := h𝓖 hS𝓖
        exact ⟨(w : X), hwO, V, ⟨hV, hVU, hS𝓖⟩, hwS⟩
      rw [h𝓑_cp n 𝓖X (fun V hV => hV.1)] at hzX
      obtain ⟨_, ⟨V, ⟨_, hVU, hVG⟩, rfl⟩, hzV⟩ := hzX
      refine ⟨closure (((↑) : U → X) ⁻¹' V), mem_image_of_mem _ hVG, ?_⟩
      rw [mem_closure_iff]
      intro O hO hzO
      have hOX : IsOpen (((↑) : U → X) '' O) := hU.isOpenMap_subtype_val O hO
      rw [mem_closure_iff] at hzV
      obtain ⟨y, ⟨w, hwO, rfl⟩, hwV⟩ := hzV _ hOX ⟨z, hzO, rfl⟩
      exact ⟨w, hwO, hwV⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  · intro W hW hxW
    have hWX : IsOpen (((↑) : U → X) '' W) := hU.isOpenMap_subtype_val W hW
    obtain ⟨n, V, hV, hVW⟩ := h𝓑_base _ hWX ⟨⟨x, hx⟩, hxW, rfl⟩
    have hVU : V ⊆ U := hVW.trans (by rintro _ ⟨y, _, rfl⟩; exact y.2)
    refine ⟨n, ((↑) : U → X) ⁻¹' V, ⟨V, hV, hVU, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨y', hy'W, heq⟩ := hVW hy
    exact (Subtype.ext heq.symm) ▸ hy'W

end OpenSubspace

section MapsAndProducts

/-- `HasSigmaCPLocalBase` is preserved by continuous open closed maps. -/
theorem hasSigmaCPLocalBase_of_isClosedMap_isOpenMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hcont : Continuous f) (hclosed : IsClosedMap f) (hopen : IsOpenMap f)
    {x : X} (hsig : Defs.D_0010.HasSigmaCPLocalBase x) :
    Defs.D_0010.HasSigmaCPLocalBase (f x) := by
  obtain ⟨𝓑, h𝓑_open, h𝓑_cp, h𝓑_base⟩ := hsig
  refine ⟨fun n => (fun U => f '' U) '' 𝓑 n, ?_, ?_, ?_⟩
  · rintro n _ ⟨U, hU, rfl⟩
    exact ⟨hopen U (h𝓑_open n U hU).1, x, (h𝓑_open n U hU).2, rfl⟩
  · intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      let 𝓖X : Set (Set X) := { U ∈ 𝓑 n | f '' U ∈ 𝓖 }
      have hsub : ⋃₀ 𝓖 ⊆ f '' (⋃₀ 𝓖X) := by
        rintro z ⟨S, hS𝓖, hzS⟩
        obtain ⟨U, hU, rfl⟩ := h𝓖 hS𝓖
        obtain ⟨a, haU, rfl⟩ := hzS
        exact ⟨a, ⟨U, ⟨hU, hS𝓖⟩, haU⟩, rfl⟩
      have hy_cl : y ∈ closure (f '' ⋃₀ 𝓖X) := closure_mono hsub hy
      have hcl_eq : closure (f '' ⋃₀ 𝓖X) ⊆ f '' closure (⋃₀ 𝓖X) :=
        closure_minimal (image_mono subset_closure) (hclosed _ isClosed_closure)
      obtain ⟨a, ha_cl, rfl⟩ := hcl_eq hy_cl
      rw [h𝓑_cp n 𝓖X (fun U hU => hU.1)] at ha_cl
      obtain ⟨_, ⟨U, ⟨_, hUG⟩, rfl⟩, haU⟩ := ha_cl
      exact ⟨closure (f '' U), mem_image_of_mem _ hUG,
        image_closure_subset_closure_image hcont ⟨a, haU, rfl⟩⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  · intro W hW hfxW
    obtain ⟨n, U, hU, hUf⟩ := h𝓑_base (f ⁻¹' W) (hW.preimage hcont) hfxW
    exact ⟨n, f '' U, ⟨U, hU, rfl⟩, image_subset_iff.mpr hUf⟩

/-- Helper: finite-product closure preservation for a family of rectangles. -/
private lemma closurePreserving_prod_rect
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {𝓕X : Set (Set X)} {𝓕Y : Set (Set Y)}
    (hX : MSpace.ClosurePreserving 𝓕X) (hY : MSpace.ClosurePreserving 𝓕Y) :
    MSpace.ClosurePreserving { W : Set (X × Y) | ∃ U ∈ 𝓕X, ∃ V ∈ 𝓕Y, W = U ×ˢ V } := by
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · rintro ⟨a, b⟩ hab
    let 𝓖X : Set (Set X) := { U ∈ 𝓕X | ∃ V ∈ 𝓕Y, U ×ˢ V ∈ 𝓖 ∧ b ∈ closure V }
    have ha_cl : a ∈ closure (⋃₀ 𝓖X) := by
      rw [mem_closure_iff]
      intro Oa hOa haOa
      let 𝓖Y_a : Set (Set Y) :=
        { V ∈ 𝓕Y | ∃ U ∈ 𝓕X, U ×ˢ V ∈ 𝓖 ∧ (Oa ∩ U).Nonempty }
      have hb_cl : b ∈ closure (⋃₀ 𝓖Y_a) := by
        rw [mem_closure_iff]
        intro Ob hOb hbOb
        rw [mem_closure_iff] at hab
        obtain ⟨⟨a', b'⟩, ⟨ha'Oa, hb'Ob⟩, W, hW𝓖, hWab⟩ :=
          hab (Oa ×ˢ Ob) (hOa.prod hOb) ⟨haOa, hbOb⟩
        obtain ⟨U, hU, V, hV, rfl⟩ := h𝓖 hW𝓖
        exact ⟨b', hb'Ob, V, ⟨hV, U, hU, hW𝓖, a', ha'Oa, hWab.1⟩, hWab.2⟩
      rw [hY 𝓖Y_a (fun V hV => hV.1)] at hb_cl
      obtain ⟨_, ⟨V, ⟨hV, U, hU, hW𝓖, a', ha'Oa, ha'U⟩, rfl⟩, hbV⟩ := hb_cl
      exact ⟨a', ha'Oa, U, ⟨hU, V, hV, hW𝓖, hbV⟩, ha'U⟩
    rw [hX 𝓖X (fun U hU => hU.1)] at ha_cl
    obtain ⟨_, ⟨U, ⟨_, V, _, hW𝓖, hbV⟩, rfl⟩, haU⟩ := ha_cl
    refine ⟨closure (U ×ˢ V), mem_image_of_mem _ hW𝓖, ?_⟩
    rw [closure_prod_eq]
    exact ⟨haU, hbV⟩
  · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- `HasSigmaCPLocalBase` is preserved by binary products. -/
theorem hasSigmaCPLocalBase_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (hX : Defs.D_0010.HasSigmaCPLocalBase x) (hY : Defs.D_0010.HasSigmaCPLocalBase y) :
    Defs.D_0010.HasSigmaCPLocalBase (x, y) := by
  obtain ⟨𝓑X, hBXo, hBXcp, hBXb⟩ := hX
  obtain ⟨𝓑Y, hBYo, hBYcp, hBYb⟩ := hY
  let 𝓑 : ℕ → Set (Set (X × Y)) := fun n =>
    { W | ∃ U ∈ 𝓑X (Nat.unpair n).1, ∃ V ∈ 𝓑Y (Nat.unpair n).2, W = U ×ˢ V }
  refine ⟨𝓑, ?_, ?_, ?_⟩
  · rintro n _ ⟨U, hU, V, hV, rfl⟩
    exact ⟨(hBXo _ U hU).1.prod (hBYo _ V hV).1, (hBXo _ U hU).2, (hBYo _ V hV).2⟩
  · intro n
    exact closurePreserving_prod_rect (hBXcp (Nat.unpair n).1) (hBYcp (Nat.unpair n).2)
  · intro O hO hxyO
    obtain ⟨U₀, V₀, hU₀, hV₀, hxU₀, hyV₀, hsub⟩ := isOpen_prod_iff.mp hO x y hxyO
    obtain ⟨n₁, U, hU, hUU₀⟩ := hBXb U₀ hU₀ hxU₀
    obtain ⟨n₂, V, hV, hVV₀⟩ := hBYb V₀ hV₀ hyV₀
    refine ⟨Nat.pair n₁ n₂, U ×ˢ V, ?_, (prod_mono hUU₀ hVV₀).trans hsub⟩
    dsimp only [𝓑]
    rw [Nat.unpair_pair]
    exact ⟨U, hU, V, hV, rfl⟩

/-- Helper: closure preservation for finite-prefix cylinders in `∀ k : ℕ, X k`. -/
private lemma closurePreserving_cyl_fin
    {X : ℕ → Type*} [∀ k, TopologicalSpace (X k)]
    (𝓕 : ∀ k, Set (Set (X k))) (h𝓕 : ∀ k, MSpace.ClosurePreserving (𝓕 k)) :
    ∀ N : ℕ, MSpace.ClosurePreserving
      { W : Set (∀ k, X k) | ∃ U : ∀ k : Fin N, Set (X k.1),
          (∀ k : Fin N, U k ∈ 𝓕 k.1) ∧ W = { y | ∀ k : Fin N, y k.1 ∈ U k } }
  | 0 => by
      intro 𝓖 h𝓖
      apply Subset.antisymm
      · rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨S, hS𝓖⟩
        · simp
        · obtain ⟨U, _, rfl⟩ := h𝓖 hS𝓖
          have hEq : { y : ∀ k, X k | ∀ k : Fin 0, y k.1 ∈ U k } = univ := by
            ext y; simp
          rw [hEq] at hS𝓖
          intro y _
          exact ⟨closure univ, mem_image_of_mem _ hS𝓖, by simp⟩
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  | N + 1 => by
      have ih := closurePreserving_cyl_fin 𝓕 h𝓕 N
      intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro y hy
        -- Split coordinates into `0..N-1` (via IH) and coordinate `N` (via `h𝓕 N`)
        let cylN : (∀ k : Fin N, Set (X k.1)) → Set (∀ k, X k) :=
          fun U => { w | ∀ k : Fin N, w k.1 ∈ U k }
        let 𝓖prev : Set (Set (∀ k, X k)) :=
          { C | ∃ U : ∀ k : Fin N, Set (X k.1), (∀ k, U k ∈ 𝓕 k.1) ∧ C = cylN U ∧
                ∃ V ∈ 𝓕 N, ({ w | w ∈ C ∧ w N ∈ V } : Set (∀ k, X k)) ∈ 𝓖 ∧ y N ∈ closure V }
        have hy_prev : y ∈ closure (⋃₀ 𝓖prev) := by
          rw [mem_closure_iff]
          intro O hO hyO
          obtain ⟨I, t, ht_all, htO⟩ := isOpen_pi_iff.mp hO y hyO
          let O' : Set (∀ k, X k) := { w | ∀ k ∈ I.erase N, w k ∈ t k }
          have hO'_open : IsOpen O' := by
            have hEq : O' = ⋂ k ∈ I.erase N, (fun w : ∀ j, X j => w k) ⁻¹' t k := by
              ext w; simp [O']
            rw [hEq]
            exact isOpen_biInter_finset fun k hk =>
              (ht_all k (Finset.mem_of_mem_erase hk)).1.preimage (continuous_apply k)
          have hyO' : y ∈ O' := fun k hk => (ht_all k (Finset.mem_of_mem_erase hk)).2
          let 𝓖N : Set (Set (X N)) :=
            { V ∈ 𝓕 N | ∃ U : ∀ k : Fin N, Set (X k.1), (∀ k, U k ∈ 𝓕 k.1) ∧
                ({ w | w ∈ cylN U ∧ w N ∈ V } : Set (∀ k, X k)) ∈ 𝓖 ∧
                (O' ∩ cylN U).Nonempty }
          have hyN_cl : y N ∈ closure (⋃₀ 𝓖N) := by
            rw [mem_closure_iff]
            intro ON hON hyON
            let Ocomb : Set (∀ k, X k) := O' ∩ (fun w => w N) ⁻¹' ON
            have hOcomb_open : IsOpen Ocomb :=
              hO'_open.inter (hON.preimage (continuous_apply N))
            rw [mem_closure_iff] at hy
            obtain ⟨w, ⟨hwO', hwN⟩, S, hS𝓖, hwS⟩ := hy Ocomb hOcomb_open ⟨hyO', hyON⟩
            obtain ⟨U, hU, rfl⟩ := h𝓖 hS𝓖
            let U' : ∀ k : Fin N, Set (X k.1) := fun k => U ⟨k.1, Nat.lt_succ_of_lt k.2⟩
            have hEqS : { z : ∀ k, X k | ∀ k : Fin (N + 1), z k.1 ∈ U k } =
                { z | z ∈ cylN U' ∧ z N ∈ U ⟨N, Nat.lt_succ_self N⟩ } := by
              ext z
              simp only [cylN, mem_ofPred_eq]
              constructor
              · intro hz
                exact ⟨fun k => hz ⟨k.1, Nat.lt_succ_of_lt k.2⟩, hz ⟨N, Nat.lt_succ_self N⟩⟩
              · rintro ⟨h1, h2⟩ ⟨k, hk⟩
                rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
                · exact h1 ⟨k, hlt⟩
                · exact h2
            rw [hEqS] at hS𝓖 hwS
            exact ⟨w N, hwN, U ⟨N, Nat.lt_succ_self N⟩,
              ⟨hU ⟨N, Nat.lt_succ_self N⟩, U', fun k => hU ⟨k.1, Nat.lt_succ_of_lt k.2⟩,
                hS𝓖, w, hwO', hwS.1⟩, hwS.2⟩
          rw [h𝓕 N 𝓖N (fun V hV => hV.1)] at hyN_cl
          obtain ⟨_, ⟨V, ⟨hV, U, hU, hSG, w, hwO', hwU⟩, rfl⟩, hyV⟩ := hyN_cl
          -- Adjust `w` at coordinate `N` to `y N` so it lies in `O` while remaining in `cylN U`
          classical
          let w' : ∀ k, X k := Function.update w N (y N)
          have hw'O : w' ∈ O := by
            apply htO
            intro k hkI
            by_cases hkN : k = N
            · subst hkN
              simp only [w', Function.update_self]
              exact (ht_all k hkI).2
            · simp only [w', Function.update_of_ne hkN]
              exact hwO' k (Finset.mem_erase.mpr ⟨hkN, hkI⟩)
          have hw'U : w' ∈ cylN U := by
            intro k
            have hkN : k.1 ≠ N := ne_of_lt k.2
            simp only [w', Function.update_of_ne hkN]
            exact hwU k
          exact ⟨w', hw'O, cylN U, ⟨U, hU, rfl, V, hV, hSG, hyV⟩, hw'U⟩
        have h𝓖prev_sub : 𝓖prev ⊆ { W : Set (∀ k, X k) | ∃ U : ∀ k : Fin N, Set (X k.1),
            (∀ k, U k ∈ 𝓕 k.1) ∧ W = cylN U } := by
          rintro _ ⟨U, hU, rfl, _⟩; exact ⟨U, hU, rfl⟩
        rw [ih 𝓖prev h𝓖prev_sub] at hy_prev
        obtain ⟨_, ⟨_, ⟨U, hU, rfl, V, hV, hSG, hyV⟩, rfl⟩, hyU⟩ := hy_prev
        refine ⟨closure { w | w ∈ cylN U ∧ w N ∈ V }, mem_image_of_mem _ hSG, ?_⟩
        rw [mem_closure_iff]
        intro O hO hyO
        obtain ⟨I, t, ht_all, htO⟩ := isOpen_pi_iff.mp hO y hyO
        let O' : Set (∀ k, X k) := { w | ∀ k ∈ I.erase N, w k ∈ t k }
        have hO'_open : IsOpen O' := by
          have hEq : O' = ⋂ k ∈ I.erase N, (fun w : ∀ j, X j => w k) ⁻¹' t k := by
            ext w; simp [O']
          rw [hEq]
          exact isOpen_biInter_finset fun k hk =>
            (ht_all k (Finset.mem_of_mem_erase hk)).1.preimage (continuous_apply k)
        have hyO' : y ∈ O' := fun k hk => (ht_all k (Finset.mem_of_mem_erase hk)).2
        rw [mem_closure_iff] at hyU
        obtain ⟨w₁, hw₁O', hw₁U⟩ := hyU O' hO'_open hyO'
        let ON : Set (X N) := if hN : N ∈ I then t N else univ
        have hON_open : IsOpen ON := by
          dsimp only [ON]; split_ifs with hN
          · exact (ht_all N hN).1
          · exact isOpen_univ
        have hyON : y N ∈ ON := by
          dsimp only [ON]; split_ifs with hN
          · exact (ht_all N hN).2
          · trivial
        rw [mem_closure_iff] at hyV
        obtain ⟨v, hvON, hvV⟩ := hyV ON hON_open hyON
        classical
        let w : ∀ k, X k := Function.update w₁ N v
        refine ⟨w, htO fun k hkI => ?_, ?_, ?_⟩
        · by_cases hkN : k = N
          · subst hkN
            simp only [w, Function.update_self]
            dsimp only [ON] at hvON
            split_ifs at hvON with h
            · exact hvON
            · exact (h hkI).elim
          · simp only [w, Function.update_of_ne hkN]
            exact hw₁O' k (Finset.mem_erase.mpr ⟨hkN, hkI⟩)
        · intro k
          have hkN : k.1 ≠ N := ne_of_lt k.2
          simp only [w, Function.update_of_ne hkN]
          exact hw₁U k
        · simp only [w, Function.update_self]
          exact hvV
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- **Countable-Product Permanence of `HasSigmaCPLocalBase`:**
If every coordinate `x k` has a `σ`-CP open local base in `X k`, then `x` has a
`σ`-CP open local base in the countable product `∀ k : ℕ, X k`. -/
theorem hasSigmaCPLocalBase_countable_pi
    {X : ℕ → Type*} [∀ k, TopologicalSpace (X k)] (x : ∀ k, X k)
    (hsig : ∀ k, Defs.D_0010.HasSigmaCPLocalBase (x k)) :
    Defs.D_0010.HasSigmaCPLocalBase x := by
  choose 𝓑 h𝓑o h𝓑cp h𝓑b using hsig
  -- Index all finite layer-choice lists `l : List ℕ` (countable via `Encodable (List ℕ)`)
  let lay : List ℕ → Set (Set (∀ k, X k)) := fun l =>
    { W | ∃ U : ∀ k : Fin l.length, Set (X k.1),
          (∀ k : Fin l.length, U k ∈ 𝓑 k.1 (l.get k)) ∧
          W = { y | ∀ k : Fin l.length, y k.1 ∈ U k } }
  have hlay_open : ∀ l, ∀ W ∈ lay l, IsOpen W ∧ x ∈ W := by
    rintro l _ ⟨U, hU, rfl⟩
    refine ⟨?_, fun k => (h𝓑o k.1 (l.get k) (U k) (hU k)).2⟩
    have hEq : { y : ∀ k, X k | ∀ k : Fin l.length, y k.1 ∈ U k } =
        ⋂ k : Fin l.length, (fun y : ∀ j, X j => y k.1) ⁻¹' U k := by
      ext y; simp
    rw [hEq]
    exact isOpen_iInter_of_finite fun k =>
      (h𝓑o k.1 (l.get k) (U k) (hU k)).1.preimage (continuous_apply k.1)
  have hlay_cp : ∀ l, MSpace.ClosurePreserving (lay l) := by
    intro l
    let 𝓕 : ∀ k : ℕ, Set (Set (X k)) := fun k =>
      if hk : k < l.length then 𝓑 k (l.get ⟨k, hk⟩) else ∅
    have h𝓕_cp : ∀ k, MSpace.ClosurePreserving (𝓕 k) := by
      intro k
      dsimp only [𝓕]
      split_ifs with hk
      · exact h𝓑cp k (l.get ⟨k, hk⟩)
      · intro 𝓖 h𝓖
        have hG : 𝓖 = ∅ := Set.subset_empty_iff.mp h𝓖
        simp [hG]
    have hEq : lay l = { W : Set (∀ k, X k) | ∃ U : ∀ k : Fin l.length, Set (X k.1),
        (∀ k : Fin l.length, U k ∈ 𝓕 k.1) ∧ W = { y | ∀ k : Fin l.length, y k.1 ∈ U k } } := by
      ext W
      simp only [lay, mem_ofPred_eq, 𝓕]
      constructor <;> (rintro ⟨U, hU, rfl⟩; refine ⟨U, fun k => ?_, rfl⟩; simpa [k.2] using hU k)
    rw [hEq]
    exact closurePreserving_cyl_fin 𝓕 h𝓕_cp l.length
  -- Re-index `List ℕ` by `ℕ` using `Denumerable.ofNat`
  let 𝓑prod : ℕ → Set (Set (∀ k, X k)) := fun n => lay (Denumerable.ofNat (List ℕ) n)
  refine ⟨𝓑prod, fun n W hW => hlay_open _ W hW, fun n => hlay_cp _, ?_⟩
  · intro O hO hxO
    obtain ⟨I, t, ht_all, htO⟩ := isOpen_pi_iff.mp hO x hxO
    let N : ℕ := I.sup id + 1
    have hcoord : ∀ k : Fin N, ∃ m : ℕ, ∃ U ∈ 𝓑 k.1 m, (k.1 ∈ I → U ⊆ t k.1) := by
      intro k
      by_cases hk : k.1 ∈ I
      · obtain ⟨m, U, hUm, hUt⟩ := h𝓑b k.1 (t k.1) (ht_all k.1 hk).1 (ht_all k.1 hk).2
        exact ⟨m, U, hUm, fun _ => hUt⟩
      · obtain ⟨m, U, hUm, _⟩ := h𝓑b k.1 univ isOpen_univ trivial
        exact ⟨m, U, hUm, fun h => (hk h).elim⟩
    choose m U hUm hUt using hcoord
    let l : List ℕ := List.ofFn m
    have hlen : l.length = N := List.length_ofFn
    let U' : ∀ k : Fin l.length, Set (X k.1) := fun k => U ⟨k.1, hlen ▸ k.2⟩
    refine ⟨Encodable.encode l, { y | ∀ k : Fin l.length, y k.1 ∈ U' k }, ?_, ?_⟩
    · dsimp only [𝓑prod]
      rw [Denumerable.ofNat_encode]
      refine ⟨U', fun k => ?_, rfl⟩
      have hget : l.get k = m ⟨k.1, hlen ▸ k.2⟩ := List.get_ofFn m k
      rw [hget]
      exact hUm ⟨k.1, hlen ▸ k.2⟩
    · intro y hy
      apply htO
      intro k hkI
      have hkN : k < N := Nat.lt_succ_of_le (Finset.le_sup (f := id) hkI)
      have hkl : k < l.length := hlen.symm ▸ hkN
      exact hUt ⟨k, hkN⟩ hkI (hy ⟨k, hkl⟩)

/-- **Countable-Product `HasCPOuterBase` Theorem:**
In a countable product `∀ k : ℕ, X k` where each `x k` has `HasSigmaCPLocalBase (x k)`
and a clopen `G_δ` sequence `W k m` with `⋂ m, W k m = {x k}`, the product point `x`
admits a single-layer CP open outer base `Defs.D_0001.HasCPOuterBase x`. -/
theorem hasCPOuterBase_countable_pi_of_clopen_gDelta
    {X : ℕ → Type} [∀ k, TopologicalSpace (X k)] (x : ∀ k, X k)
    (hsig : ∀ k, Defs.D_0010.HasSigmaCPLocalBase (x k))
    (W : ∀ k, ℕ → Set (X k))
    (hW : ∀ k m, IsOpen (W k m) ∧ IsClosed (W k m) ∧ x k ∈ W k m)
    (hW_inter : ∀ k, (⋂ m, W k m) = {x k}) :
    Defs.D_0001.HasCPOuterBase x := by
  have hsig_prod : Defs.D_0010.HasSigmaCPLocalBase x :=
    hasSigmaCPLocalBase_countable_pi x hsig
  let Wprod : ℕ → Set (∀ k, X k) := fun n =>
    { y | ∀ k : Fin n, ∀ m : Fin n, y k.1 ∈ W k.1 m.1 }
  have hWprod : ∀ n, IsOpen (Wprod n) ∧ IsClosed (Wprod n) ∧ x ∈ Wprod n := by
    intro n
    have hEq : Wprod n = ⋂ k : Fin n, ⋂ m : Fin n, (fun y : ∀ j, X j => y k.1) ⁻¹' W k.1 m.1 := by
      ext y; simp [Wprod]
    refine ⟨?_, ?_, fun k m => (hW k.1 m.1).2.2⟩
    · rw [hEq]
      exact isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun m =>
        (hW k.1 m.1).1.preimage (continuous_apply k.1)
    · rw [hEq]
      exact isClosed_iInter fun k => isClosed_iInter fun m =>
        (hW k.1 m.1).2.1.preimage (continuous_apply k.1)
  have hWprod_inter : (⋂ n, Wprod n) = {x} := by
    ext y
    simp only [mem_iInter, mem_singleton_iff]
    constructor
    · intro hy
      funext k
      have hyk : y k ∈ ⋂ m, W k m := mem_iInter.mpr fun m =>
        hy (max k m + 1) ⟨k, Nat.lt_succ_of_le (le_max_left k m)⟩
          ⟨m, Nat.lt_succ_of_le (le_max_right k m)⟩
      rw [hW_inter k, mem_singleton_iff] at hyk
      exact hyk
    · rintro rfl n k m
      exact (hW k.1 m.1).2.2
  exact Proofs.L_0032.main (∀ k, X k) x Wprod hWprod hWprod_inter hsig_prod

end MapsAndProducts

end Research.ChenWangSigmaCPPermanence
