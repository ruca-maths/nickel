import Targets
import Defs.D_0001
import Defs.D_0010
import Proofs.L_0004

/-!
# Permanence & Obstruction Theorems for `Defs.D_0001.HasCPOuterBase`

This file proves five sharp permanence and obstruction theorems for
`Defs.D_0001.HasCPOuterBase`, constraining any `L_0020` / `L_0030` / `L_0031`
counterexample `(Y, y₀)`:

1. `hasCPOuterBase_of_decreasing_base` & `hasCPOuterBase_of_firstCountable`:
   In any `T3Space`, every first-countable point admits a single-layer CP open
   outer base (`HasCPOuterBase x`). Thus any counterexample point `y₀` is
   strictly non-first-countable.
2. `hasCPOuterBase_prod`:
   For ANY topological spaces `X, Y`, if `HasCPOuterBase x` in `X` and
   `HasCPOuterBase y` in `Y`, then `HasCPOuterBase (x, y)` in `X × Y`.
3. `hasCPOuterBase_of_isClosedMap_isOpenMap`:
   `HasCPOuterBase` is preserved by continuous open closed maps.
4. `hasCPOuterBase_of_compact_nhd_gDelta` & `stratifiable_no_compact_nhd_of_not_hasCPOuterBase`:
   In any stratifiable space `Y`, any point `y` admitting a compact neighborhood
   is first-countable and therefore satisfies `HasCPOuterBase y`.
   Consequently, in any `L_0020` / `L_0030` / `L_0031` counterexample `(Y, y₀)`,
   `y₀` has NO compact neighborhood.
-/

namespace Research.ChenWangOuterBasePermanence

open MSpace Set Topology

section FirstCountableAndCompact

variable {X : Type*} [TopologicalSpace X]

/-- Any point with a decreasing open neighborhood base `B : ℕ → Set X` satisfying
`⋂ n, closure (B n) = {x}` admits a single-layer CP open outer base `range B`. -/
theorem hasCPOuterBase_of_decreasing_base {x : X} (B : ℕ → Set X)
    (hB_open : ∀ n, IsOpen (B n) ∧ x ∈ B n)
    (hB_dec : ∀ n, B (n + 1) ⊆ B n)
    (hB_base : ∀ U : Set X, IsOpen U → x ∈ U → ∃ n, B n ⊆ U)
    (hB_inter : (⋂ n, closure (B n)) = {x}) :
    Defs.D_0001.HasCPOuterBase x := by
  classical
  have hB_anti : ∀ {m n : ℕ}, m ≤ n → B n ⊆ B m := by
    intro m n hmn
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hB_dec _).trans ih
  refine ⟨range B, ?_, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩; exact hB_open n
  · intro U hU hxU
    obtain ⟨n, hn⟩ := hB_base U hU hxU
    exact ⟨B n, ⟨n, rfl⟩, hn⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      by_cases hzx : z = x
      · subst hzx
        rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨S, hS𝓖⟩
        · simp at hz
        · obtain ⟨n, rfl⟩ := h𝓖 hS𝓖
          exact ⟨closure (B n), mem_image_of_mem _ hS𝓖, subset_closure (hB_open n).2⟩
      · have hz_not : z ∉ ⋂ n, closure (B n) := by rw [hB_inter]; exact hzx
        rw [mem_iInter] at hz_not
        push Not at hz_not
        obtain ⟨N, hzBN⟩ := hz_not
        have hsub : ⋃₀ 𝓖 ⊆ (⋃ n ∈ Set.Iio N, if B n ∈ 𝓖 then B n else ∅) ∪ B N := by
          rintro w ⟨S, hS𝓖, hwS⟩
          obtain ⟨n, rfl⟩ := h𝓖 hS𝓖
          by_cases hn : n < N
          · left
            refine mem_biUnion (show n ∈ Set.Iio N from hn) ?_
            simp [hS𝓖, hwS]
          · right
            exact hB_anti (not_lt.mp hn) hwS
        have hcl := closure_mono hsub hz
        rw [closure_union, (Set.finite_Iio N).closure_biUnion] at hcl
        rcases hcl with hcl | hcl
        · simp only [mem_iUnion] at hcl
          obtain ⟨n, -, hn⟩ := hcl
          by_cases hBn : B n ∈ 𝓖
          · simp only [hBn, ↓reduceIte] at hn
            exact ⟨closure (B n), mem_image_of_mem _ hBn, hn⟩
          · simp only [hBn, ↓reduceIte, closure_empty, mem_empty_iff_false] at hn
        · exact absurd hcl hzBN
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- In any `T3Space`, every point with a countably generated neighborhood filter
(i.e. first-countable at `x`) admits a single-layer CP open outer base. -/
theorem hasCPOuterBase_of_firstCountable [T3Space X] {x : X}
    (hfc : (𝓝 x).IsCountablyGenerated) :
    Defs.D_0001.HasCPOuterBase x := by
  have : (𝓝 x).IsCountablyGenerated := hfc
  obtain ⟨u, hu_bas⟩ := Filter.exists_antitone_basis (𝓝 x)
  have hstep : ∀ n : ℕ, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ u n := by
    intro n
    obtain ⟨V, hVu, hVopen, hxV⟩ := mem_nhds_iff.mp (hu_bas.mem n)
    exact ⟨V, hVopen, hxV, hVu⟩
  choose V hV_open hxV hV_sub using hstep
  let B : ℕ → Set X := fun n => ⋂ k ∈ Set.Iic n, V k
  refine hasCPOuterBase_of_decreasing_base B
    (fun n => ⟨(Set.finite_Iic n).isOpen_biInter (fun k _ => hV_open k),
      mem_iInter₂.mpr fun k _ => hxV k⟩)
    (fun n y hy => mem_iInter₂.mpr fun k hk =>
      mem_iInter₂.mp hy k (le_trans hk (Nat.le_succ n)))
    (fun U hU hxU => by
      obtain ⟨n, hn⟩ := hu_bas.mem_iff.mp (hU.mem_nhds hxU)
      exact ⟨n, fun y hy => hn (hV_sub n (mem_iInter₂.mp hy n (Set.mem_Iic.mpr le_rfl)))⟩)
    ?_
  apply Subset.antisymm
  · intro z hz
    by_contra hzx
    obtain ⟨t, htnhds, htclosed, htsub⟩ :=
      exists_mem_nhds_isClosed_subset (isClosed_singleton.isOpen_compl.mem_nhds (Ne.symm hzx))
    obtain ⟨n, hn⟩ := hu_bas.mem_iff.mp htnhds
    have hBsub : B n ⊆ t := fun y hy => hn (hV_sub n (mem_iInter₂.mp hy n (Set.mem_Iic.mpr le_rfl)))
    have hzt : z ∈ t := htclosed.closure_subset (closure_mono hBsub (mem_iInter.mp hz n))
    exact htsub hzt rfl
  · exact subset_iInter fun n => singleton_subset_iff.mpr
      (subset_closure (mem_iInter₂.mpr fun k _ => hxV k))

/-- In any `T3Space`, a point `x` with a compact neighborhood `K ∈ 𝓝 x` and a
countable `G_δ` representation `⋂ n, U n = {x}` is first-countable and hence
satisfies `Defs.D_0001.HasCPOuterBase x`. -/
theorem hasCPOuterBase_of_compact_nhd_gDelta [T3Space X] {x : X}
    {K : Set X} (hK_nhd : K ∈ 𝓝 x) (hK_comp : IsCompact K)
    (U : ℕ → Set X) (hU_open : ∀ n, IsOpen (U n)) (hU_inter : (⋂ n, U n) = {x}) :
    Defs.D_0001.HasCPOuterBase x := by
  have hxU : ∀ n, x ∈ U n := fun n => mem_iInter.mp (hU_inter.symm ▸ rfl) n
  -- Recursively choose open `V n ∋ x` with `closure (V 0) ⊆ interior K ∩ U 0`
  -- and `closure (V (n+1)) ⊆ V n ∩ U (n+1)`.
  have hshrink : ∀ (W : { W : Set X // IsOpen W ∧ x ∈ W }),
      ∃ V : { V : Set X // IsOpen V ∧ x ∈ V }, closure V.1 ⊆ W.1 := by
    rintro ⟨W, hW, hxW⟩
    obtain ⟨t, htnhds, htclosed, htsub⟩ := exists_mem_nhds_isClosed_subset (hW.mem_nhds hxW)
    obtain ⟨V, hVt, hVopen, hxV⟩ := mem_nhds_iff.mp htnhds
    exact ⟨⟨V, hVopen, hxV⟩, (closure_minimal hVt htclosed).trans htsub⟩
  choose shrink hshrink_cl using hshrink
  let W0 : { W : Set X // IsOpen W ∧ x ∈ W } :=
    ⟨interior K ∩ U 0, isOpen_interior.inter (hU_open 0),
      mem_interior_iff_mem_nhds.mpr hK_nhd, hxU 0⟩
  let Vrec : ℕ → { V : Set X // IsOpen V ∧ x ∈ V } :=
    Nat.rec (shrink W0) (fun n prev =>
      shrink ⟨prev.1 ∩ U (n + 1), prev.2.1.inter (hU_open (n + 1)), prev.2.2, hxU (n + 1)⟩)
  let B : ℕ → Set X := fun n => (Vrec n).1
  have hB_open : ∀ n, IsOpen (B n) ∧ x ∈ B n := fun n => (Vrec n).2
  have hB_cl0 : closure (B 0) ⊆ interior K ∩ U 0 := hshrink_cl W0
  have hB_cl_succ : ∀ n, closure (B (n + 1)) ⊆ B n ∩ U (n + 1) := fun n =>
    hshrink_cl ⟨(Vrec n).1 ∩ U (n + 1), (Vrec n).2.1.inter (hU_open (n + 1)),
      (Vrec n).2.2, hxU (n + 1)⟩
  have hB_dec : ∀ n, B (n + 1) ⊆ B n := fun n =>
    subset_closure.trans ((hB_cl_succ n).trans inter_subset_left)
  have hB_anti : ∀ {m n : ℕ}, m ≤ n → B n ⊆ B m := by
    intro m n hmn
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hB_dec _).trans ih
  have hB_cl_sub_K : ∀ n, closure (B n) ⊆ K := fun n =>
    (closure_mono (hB_anti (Nat.zero_le n))).trans
      (hB_cl0.trans (inter_subset_left.trans interior_subset))
  have hB_inter : (⋂ n, closure (B n)) = {x} := by
    apply Subset.antisymm
    · rw [← hU_inter]
      intro z hz
      refine mem_iInter.mpr fun n => ?_
      cases n with
      | zero => exact (hB_cl0 (mem_iInter.mp hz 0)).2
      | succ n => exact (hB_cl_succ n (mem_iInter.mp hz (n + 1))).2
    · exact subset_iInter fun n => singleton_subset_iff.mpr (subset_closure (hB_open n).2)
  refine hasCPOuterBase_of_decreasing_base B hB_open hB_dec ?_ hB_inter
  intro O hO hxO
  have hne_iInter : K ∩ (⋂ n : ℕ, closure (B n) \ O) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_iInter, mem_sdiff, mem_empty_iff_false, iff_false, not_and]
    intro _ hz
    have hzx : z ∈ ⋂ n, closure (B n) := mem_iInter.mpr fun n => (hz n).1
    rw [hB_inter, mem_singleton_iff] at hzx
    subst hzx
    exact (hz 0).2 hxO
  have hfin := hK_comp.elim_finite_subfamily_closed (fun n => closure (B n) \ O)
    (fun n => isClosed_closure.sdiff hO) (Set.disjoint_iff_inter_eq_empty.mpr hne_iInter)
  obtain ⟨t, ht⟩ := hfin
  let N : ℕ := t.sup id
  refine ⟨N, fun y hy => ?_⟩
  by_contra hyO
  have hyK : y ∈ K := hB_cl_sub_K N (subset_closure hy)
  have hyInt : y ∈ ⋂ n ∈ t, (closure (B n) \ O) :=
    mem_iInter₂.mpr fun n hn => ⟨subset_closure (hB_anti (Finset.le_sup (f := id) hn) hy), hyO⟩
  exact Set.disjoint_left.mp ht hyK hyInt

/-- In any stratifiable space `Y`, if `¬ HasCPOuterBase y`, then `y` has NO compact
neighborhood. -/
theorem stratifiable_no_compact_nhd_of_not_hasCPOuterBase
    {Y : Type} [TopologicalSpace Y]
    (hStrat : MSpace.IsStratifiable Y) {y : Y}
    (hno : ¬ Defs.D_0001.HasCPOuterBase y) :
    ∀ K ∈ 𝓝 y, ¬ IsCompact K := by
  have hT3 : T3Space Y := ((Proofs.L_0004.main Y).mpr hStrat).1
  obtain ⟨_, G, hGo, hGs, hGi, _⟩ := hStrat
  have hG_inter : (⋂ n, G n {y}) = {y} := by
    apply Subset.antisymm
    · intro z hz
      rw [← hGi {y} isClosed_singleton]
      exact mem_iInter.mpr fun n => subset_closure (mem_iInter.mp hz n)
    · exact subset_iInter fun n => hGs n {y} isClosed_singleton
  intro K hKnhd hKcomp
  exact hno (hasCPOuterBase_of_compact_nhd_gDelta hKnhd hKcomp
    (fun n => G n {y}) (fun n => hGo n {y} isClosed_singleton) hG_inter)

end FirstCountableAndCompact

section ProductAndMaps

/-- **Product Permanence of `HasCPOuterBase`:**
In ANY topological spaces `X, Y`, if `HasCPOuterBase x` in `X` and
`HasCPOuterBase y` in `Y`, then `HasCPOuterBase (x, y)` in `X × Y`. -/
theorem hasCPOuterBase_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (hX : Defs.D_0001.HasCPOuterBase x) (hY : Defs.D_0001.HasCPOuterBase y) :
    Defs.D_0001.HasCPOuterBase (x, y) := by
  obtain ⟨𝓥X, hVXo, hVXb, hVXcp⟩ := hX
  obtain ⟨𝓥Y, hVYo, hVYb, hVYcp⟩ := hY
  refine ⟨{ W : Set (X × Y) | ∃ U ∈ 𝓥X, ∃ V ∈ 𝓥Y, W = U ×ˢ V }, ?_, ?_, ?_⟩
  · rintro _ ⟨U, hU, V, hV, rfl⟩
    exact ⟨(hVXo U hU).1.prod (hVYo V hV).1, (hVXo U hU).2, (hVYo V hV).2⟩
  · intro O hO hxyO
    obtain ⟨U₀, V₀, hU₀, hV₀, hxU₀, hyV₀, hsub⟩ := isOpen_prod_iff.mp hO x y hxyO
    obtain ⟨U, hU, hUU₀⟩ := hVXb U₀ hU₀ hxU₀
    obtain ⟨V, hV, hVV₀⟩ := hVYb V₀ hV₀ hyV₀
    exact ⟨U ×ˢ V, ⟨U, hU, V, hV, rfl⟩, (prod_mono hUU₀ hVV₀).trans hsub⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · rintro ⟨a, b⟩ hab
      let 𝓖X : Set (Set X) := { U ∈ 𝓥X | ∃ V ∈ 𝓥Y, U ×ˢ V ∈ 𝓖 ∧ b ∈ closure V }
      have ha_cl : a ∈ closure (⋃₀ 𝓖X) := by
        rw [mem_closure_iff]
        intro Oa hOa haOa
        let 𝓖Y_a : Set (Set Y) :=
          { V ∈ 𝓥Y | ∃ U ∈ 𝓥X, U ×ˢ V ∈ 𝓖 ∧ (Oa ∩ U).Nonempty }
        have hb_cl : b ∈ closure (⋃₀ 𝓖Y_a) := by
          rw [mem_closure_iff]
          intro Ob hOb hbOb
          rw [mem_closure_iff] at hab
          obtain ⟨⟨a', b'⟩, ⟨ha'Oa, hb'Ob⟩, W, hW𝓖, hWab⟩ :=
            hab (Oa ×ˢ Ob) (hOa.prod hOb) ⟨haOa, hbOb⟩
          obtain ⟨U, hU, V, hV, rfl⟩ := h𝓖 hW𝓖
          exact ⟨b', hb'Ob, V, ⟨hV, U, hU, hW𝓖, a', ha'Oa, hWab.1⟩, hWab.2⟩
        rw [hVYcp 𝓖Y_a (fun V hV => hV.1)] at hb_cl
        obtain ⟨_, ⟨V, ⟨hV, U, hU, hW𝓖, a', ha'Oa, ha'U⟩, rfl⟩, hbV⟩ := hb_cl
        exact ⟨a', ha'Oa, U, ⟨hU, V, hV, hW𝓖, hbV⟩, ha'U⟩
      rw [hVXcp 𝓖X (fun U hU => hU.1)] at ha_cl
      obtain ⟨_, ⟨U, ⟨_, V, _, hW𝓖, hbV⟩, rfl⟩, haU⟩ := ha_cl
      refine ⟨closure (U ×ˢ V), mem_image_of_mem _ hW𝓖, ?_⟩
      rw [closure_prod_eq]
      exact ⟨haU, hbV⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- `HasCPOuterBase` is preserved by continuous open closed maps. -/
theorem hasCPOuterBase_of_isClosedMap_isOpenMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hcont : Continuous f) (hclosed : IsClosedMap f) (hopen : IsOpenMap f)
    {x : X} (hcp : Defs.D_0001.HasCPOuterBase x) :
    Defs.D_0001.HasCPOuterBase (f x) := by
  obtain ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩ := hcp
  refine ⟨(fun U => f '' U) '' 𝓥, ?_, ?_, ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨hopen U (h𝓥_open U hU).1, x, (h𝓥_open U hU).2, rfl⟩
  · intro W hW hfxW
    obtain ⟨U, hU, hUf⟩ := h𝓥_base (f ⁻¹' W) (hW.preimage hcont) hfxW
    exact ⟨f '' U, ⟨U, hU, rfl⟩, image_subset_iff.mpr hUf⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      let 𝓖X : Set (Set X) := { U ∈ 𝓥 | f '' U ∈ 𝓖 }
      have hsub : ⋃₀ 𝓖 ⊆ f '' (⋃₀ 𝓖X) := by
        rintro z ⟨S, hS𝓖, hzS⟩
        obtain ⟨U, hU, rfl⟩ := h𝓖 hS𝓖
        obtain ⟨a, haU, rfl⟩ := hzS
        exact ⟨a, ⟨U, ⟨hU, hS𝓖⟩, haU⟩, rfl⟩
      have hy_cl : y ∈ closure (f '' ⋃₀ 𝓖X) := closure_mono hsub hy
      have hcl_eq : closure (f '' ⋃₀ 𝓖X) ⊆ f '' closure (⋃₀ 𝓖X) :=
        closure_minimal (image_mono subset_closure) (hclosed _ isClosed_closure)
      obtain ⟨a, ha_cl, rfl⟩ := hcl_eq hy_cl
      rw [h𝓥_cp 𝓖X (fun U hU => hU.1)] at ha_cl
      obtain ⟨_, ⟨U, ⟨_, hUG⟩, rfl⟩, haU⟩ := ha_cl
      exact ⟨closure (f '' U), mem_image_of_mem _ hUG,
        image_closure_subset_closure_image hcont ⟨a, haU, rfl⟩⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

end ProductAndMaps

end Research.ChenWangOuterBasePermanence
