import Targets
import Proofs.L_0002
import Proofs.L_0003
import Proofs.L_0004
import Proofs.L_0017

/-!
# Countable-Product Permanence: Borges (1966) & Ceder (1961)

This file formalizes the classic countable-product theorems for `M₃` (stratifiable)
and `M₁` spaces:

1. `isStratifiable_prod` & `isStratifiable_countable_pi` (Borges 1966):
   Binary and countable products `∀ k : ℕ, X k` of stratifiable spaces are stratifiable
   (via monotone `g`-functions and `Proofs.L_0017`).
2. `isM1_prod` & `isM1_countable_pi` (Ceder 1961):
   Binary and countable products `∀ k : ℕ, X k` of `M₁` spaces are `M₁`
   (via inductive closure-preservation of finite-prefix cylinder families and
   `Denumerable.ofNat (List ℕ)` re-indexing).
-/

namespace Research.StratifiableCountablePi

open MSpace Set Topology

section StratifiableProducts

/-- Binary products preserve `MSpace.IsStratifiable` (Borges 1966). -/
theorem isStratifiable_prod {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : MSpace.IsStratifiable X) (hY : MSpace.IsStratifiable Y) :
    MSpace.IsStratifiable (X × Y) := by
  have hT1X : T1Space X := hX.1
  have hT1Y : T1Space Y := hY.1
  have hT1 : T1Space (X × Y) := inferInstance
  obtain ⟨GX, hGXo, hGXs, hGXi, hGXm⟩ := hX.2
  obtain ⟨GY, hGYo, hGYs, hGYi, hGYm⟩ := hY.2
  let gX : ℕ → X → Set X := fun n x => ⋂ j ∈ Set.Iic n, GX j {x}
  let gY : ℕ → Y → Set Y := fun n y => ⋂ j ∈ Set.Iic n, GY j {y}
  let g : ℕ → X × Y → Set (X × Y) := fun n p => gX n p.1 ×ˢ gY n p.2
  have hgX_open : ∀ n x, IsOpen (gX n x) ∧ x ∈ gX n x := fun n x =>
    ⟨(Set.finite_Iic n).isOpen_biInter fun j _ => hGXo j {x} isClosed_singleton,
     mem_iInter₂.mpr fun j _ => hGXs j {x} isClosed_singleton rfl⟩
  have hgY_open : ∀ n y, IsOpen (gY n y) ∧ y ∈ gY n y := fun n y =>
    ⟨(Set.finite_Iic n).isOpen_biInter fun j _ => hGYo j {y} isClosed_singleton,
     mem_iInter₂.mpr fun j _ => hGYs j {y} isClosed_singleton rfl⟩
  refine ⟨hT1, Proofs.L_0017.main (X × Y) ⟨g, fun n p =>
    ⟨(hgX_open n p.1).1.prod (hgY_open n p.2).1, (hgX_open n p.1).2, (hgY_open n p.2).2⟩,
    fun n p => prod_mono
      (fun a ha => mem_iInter₂.mpr fun j hj => mem_iInter₂.mp ha j (le_trans hj (Nat.le_succ n)))
      (fun b hb => mem_iInter₂.mpr fun j hj => mem_iInter₂.mp hb j (le_trans hj (Nat.le_succ n))),
    ?_⟩⟩
  intro H hH ⟨x₀, y₀⟩ hx₀H
  obtain ⟨U, V, hUopen, hVopen, hx₀U, hy₀V, hUV⟩ :=
    isOpen_prod_iff.mp hH.isOpen_compl x₀ y₀ hx₀H
  have hx₀not : x₀ ∉ ⋂ n, closure (GX n Uᶜ) := by
    rw [hGXi Uᶜ hUopen.isClosed_compl]; exact fun h => h hx₀U
  have hy₀not : y₀ ∉ ⋂ n, closure (GY n Vᶜ) := by
    rw [hGYi Vᶜ hVopen.isClosed_compl]; exact fun h => h hy₀V
  rw [mem_iInter] at hx₀not hy₀not
  push Not at hx₀not hy₀not
  obtain ⟨n₁, hn₁⟩ := hx₀not
  obtain ⟨n₂, hn₂⟩ := hy₀not
  let n : ℕ := max n₁ n₂
  refine ⟨n, fun hcl => ?_⟩
  have hsub : (⋃ p ∈ H, g n p) ⊆ (GX n₁ Uᶜ ×ˢ univ) ∪ (univ ×ˢ GY n₂ Vᶜ) := by
    rintro ⟨a, b⟩ hab
    obtain ⟨⟨x, y⟩, hxyH, ha, hb⟩ := mem_iUnion₂.mp hab
    by_cases hxU : x ∈ U
    · have hyV : y ∉ V := fun hv => hUV ⟨hxU, hv⟩ hxyH
      right
      refine ⟨trivial, ?_⟩
      have h1 : b ∈ GY n₂ {y} := mem_iInter₂.mp hb n₂ (Set.mem_Iic.mpr (le_max_right n₁ n₂))
      exact hGYm n₂ {y} Vᶜ isClosed_singleton hVopen.isClosed_compl
        (singleton_subset_iff.mpr hyV) h1
    · left
      refine ⟨?_, trivial⟩
      have h1 : a ∈ GX n₁ {x} := mem_iInter₂.mp ha n₁ (Set.mem_Iic.mpr (le_max_left n₁ n₂))
      exact hGXm n₁ {x} Uᶜ isClosed_singleton hUopen.isClosed_compl
        (singleton_subset_iff.mpr hxU) h1
  have hcl' := closure_mono hsub hcl
  rw [closure_union, closure_prod_eq, closure_prod_eq] at hcl'
  rcases hcl' with ⟨hx1, _⟩ | ⟨_, hy2⟩
  · exact hn₁ hx1
  · exact hn₂ hy2

/-- **Borges (1966) Countable-Product Stratifiability Theorem:**
Every countable product `∀ k : ℕ, X k` of stratifiable spaces is stratifiable. -/
theorem isStratifiable_countable_pi {X : ℕ → Type} [∀ k, TopologicalSpace (X k)]
    (hStrat : ∀ k, MSpace.IsStratifiable (X k)) :
    MSpace.IsStratifiable (∀ k, X k) := by
  have hT1k : ∀ k, T1Space (X k) := fun k => (hStrat k).1
  have hT1 : T1Space (∀ k, X k) := inferInstance
  have hGk_ex : ∀ k, ∃ G : ℕ → Set (X k) → Set (X k), MSpace.IsStratification G :=
    fun k => (hStrat k).2
  choose G hGo hGs hGi hGm using hGk_ex
  let gk : ∀ k, ℕ → X k → Set (X k) := fun k n x => ⋂ j ∈ Set.Iic n, G k j {x}
  have hgk_open : ∀ k n x, IsOpen (gk k n x) ∧ x ∈ gk k n x := fun k n x =>
    ⟨(Set.finite_Iic n).isOpen_biInter fun j _ => hGo k j {x} isClosed_singleton,
     mem_iInter₂.mpr fun j _ => hGs k j {x} isClosed_singleton rfl⟩
  let g : ℕ → (∀ k, X k) → Set (∀ k, X k) := fun n x =>
    { y | ∀ k : Fin n, y k.1 ∈ gk k.1 n (x k.1) }
  have hg_open : ∀ n x, IsOpen (g n x) ∧ x ∈ g n x := by
    intro n x
    refine ⟨?_, fun k => (hgk_open k.1 n (x k.1)).2⟩
    have hEq : g n x = ⋂ k : Fin n, (fun y : ∀ j, X j => y k.1) ⁻¹' gk k.1 n (x k.1) := by
      ext y; simp [g]
    rw [hEq]
    exact isOpen_iInter_of_finite fun k =>
      (hgk_open k.1 n (x k.1)).1.preimage (continuous_apply k.1)
  have hg_dec : ∀ n x, g (n + 1) x ⊆ g n x := by
    intro n x y hy k
    have hk := hy ⟨k.1, Nat.lt_succ_of_lt k.2⟩
    exact mem_iInter₂.mpr fun j hj => mem_iInter₂.mp hk j (le_trans hj (Nat.le_succ n))
  refine ⟨hT1, Proofs.L_0017.main (∀ k, X k) ⟨g, hg_open, hg_dec, ?_⟩⟩
  intro H hH x₀ hx₀H
  obtain ⟨I, t, ht_all, htH⟩ := isOpen_pi_iff.mp hH.isOpen_compl x₀ hx₀H
  have hm_ex : ∀ k : ℕ, ∃ m : ℕ, k ∈ I → x₀ k ∉ closure (G k m (t k)ᶜ) := by
    intro k
    by_cases hk : k ∈ I
    · have hnot : x₀ k ∉ ⋂ m, closure (G k m (t k)ᶜ) := by
        rw [hGi k (t k)ᶜ (ht_all k hk).1.isClosed_compl]
        exact fun h => h (ht_all k hk).2
      rw [mem_iInter] at hnot
      push Not at hnot
      obtain ⟨m, hm⟩ := hnot
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose m hm using hm_ex
  let N : ℕ := max (I.sup id + 1) (I.sup m)
  refine ⟨N, fun hcl => ?_⟩
  have hsub : (⋃ y ∈ H, g N y) ⊆
      ⋃ k ∈ (I : Set ℕ), (fun z : ∀ j, X j => z k) ⁻¹' G k (m k) (t k)ᶜ := by
    intro z hz
    obtain ⟨y, hyH, hzgy⟩ := mem_iUnion₂.mp hz
    have hnot_all : ∃ k ∈ I, y k ∉ t k := by
      by_contra hall
      push Not at hall
      exact htH hall hyH
    obtain ⟨k, hkI, hyk⟩ := hnot_all
    have hkN : k < N := lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hkI))
      (le_max_left _ _)
    have hmkN : m k ≤ N := le_trans (Finset.le_sup (f := m) hkI) (le_max_right _ _)
    have hzk : z k ∈ gk k N (y k) := hzgy ⟨k, hkN⟩
    have hzk' : z k ∈ G k (m k) {y k} := mem_iInter₂.mp hzk (m k) (Set.mem_Iic.mpr hmkN)
    refine mem_biUnion hkI ?_
    exact hGm k (m k) {y k} (t k)ᶜ isClosed_singleton (ht_all k hkI).1.isClosed_compl
      (singleton_subset_iff.mpr hyk) hzk'
  have hcl' := closure_mono hsub hcl
  rw [I.finite_toSet.closure_biUnion] at hcl'
  obtain ⟨k, hkI, hxk⟩ := mem_iUnion₂.mp hcl'
  exact hm k hkI ((continuous_apply k).closure_preimage_subset _ hxk)

end StratifiableProducts

section M1Products

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

/-- Binary products preserve `MSpace.IsM1` (Ceder 1961). -/
theorem isM1_prod {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : MSpace.IsM1 X) (hY : MSpace.IsM1 Y) :
    MSpace.IsM1 (X × Y) := by
  have hT3X : T3Space X := hX.1
  have hT3Y : T3Space Y := hY.1
  have hT3 : T3Space (X × Y) := inferInstance
  obtain ⟨𝓑X, hBXbas, 𝓑X', hBX'cp, rfl⟩ := hX.2
  obtain ⟨𝓑Y, hBYbas, 𝓑Y', hBY'cp, rfl⟩ := hY.2
  let 𝓛 : ℕ → Set (Set (X × Y)) := fun n =>
    { W | ∃ U ∈ 𝓑X' (Nat.unpair n).1, ∃ V ∈ 𝓑Y' (Nat.unpair n).2, W = U ×ˢ V }
  refine ⟨hT3, ⋃ n, 𝓛 n, ?_, ⟨𝓛, fun n =>
    closurePreserving_prod_rect (hBX'cp _) (hBY'cp _), rfl⟩⟩
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro S hS
    obtain ⟨n, U, hU, V, hV, rfl⟩ := by simpa [𝓛] using hS
    exact (hBXbas.isOpen (mem_iUnion.mpr ⟨_, hU⟩)).prod (hBYbas.isOpen (mem_iUnion.mpr ⟨_, hV⟩))
  · rintro ⟨x, y⟩ O hxyO hOopen
    obtain ⟨U₀, V₀, hU₀, hV₀, hxU₀, hyV₀, hsub⟩ := isOpen_prod_iff.mp hOopen x y hxyO
    obtain ⟨U, hU, hxU, hUU₀⟩ := hBXbas.exists_subset_of_mem_open hxU₀ hU₀
    obtain ⟨V, hV, hyV, hVV₀⟩ := hBYbas.exists_subset_of_mem_open hyV₀ hV₀
    obtain ⟨n₁, hUn₁⟩ := mem_iUnion.mp hU
    obtain ⟨n₂, hVn₂⟩ := mem_iUnion.mp hV
    refine ⟨U ×ˢ V, mem_iUnion.mpr ⟨Nat.pair n₁ n₂, ?_⟩, ⟨hxU, hyV⟩,
      (prod_mono hUU₀ hVV₀).trans hsub⟩
    dsimp only [𝓛]
    rw [Nat.unpair_pair]
    exact ⟨U, hUn₁, V, hVn₂, rfl⟩

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
          have hEq : { y : ∀ k, X k | ∀ k : Fin 0, y k.1 ∈ U k } = univ := by ext y; simp
          rw [hEq] at hS𝓖
          intro y _
          exact ⟨closure univ, mem_image_of_mem _ hS𝓖, by simp⟩
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  | N + 1 => by
      have ih := closurePreserving_cyl_fin 𝓕 h𝓕 N
      intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro y hy
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

/-- **Ceder (1961) Countable-Product `M₁` Theorem:**
Every countable product `∀ k : ℕ, X k` of `M₁` spaces is `M₁`. -/
theorem isM1_countable_pi {X : ℕ → Type} [∀ k, TopologicalSpace (X k)]
    (hM1 : ∀ k, MSpace.IsM1 (X k)) :
    MSpace.IsM1 (∀ k, X k) := by
  have hStrat : ∀ k, MSpace.IsStratifiable (X k) := fun k =>
    (Proofs.L_0004.main (X k)).mp (Proofs.L_0003.main (X k) (Proofs.L_0002.main (X k) (hM1 k)))
  have hT3 : T3Space (∀ k, X k) :=
    ((Proofs.L_0004.main (∀ k, X k)).mpr (isStratifiable_countable_pi hStrat)).1
  have hbas_ex : ∀ k, ∃ 𝓑' : ℕ → Set (Set (X k)),
      TopologicalSpace.IsTopologicalBasis (⋃ m, 𝓑' m) ∧
      ∀ m, MSpace.ClosurePreserving (𝓑' m) := by
    intro k
    obtain ⟨𝓑, h𝓑bas, 𝓑', h𝓑'cp, rfl⟩ := (hM1 k).2
    exact ⟨𝓑', h𝓑bas, h𝓑'cp⟩
  choose 𝓑 h𝓑bas h𝓑cp using hbas_ex
  let lay : List ℕ → Set (Set (∀ k, X k)) := fun l =>
    { W | ∃ U : ∀ k : Fin l.length, Set (X k.1),
          (∀ k : Fin l.length, U k ∈ 𝓑 k.1 (l.get k)) ∧
          W = { y | ∀ k : Fin l.length, y k.1 ∈ U k } }
  have hlay_open : ∀ l, ∀ W ∈ lay l, IsOpen W := by
    rintro l _ ⟨U, hU, rfl⟩
    have hEq : { y : ∀ k, X k | ∀ k : Fin l.length, y k.1 ∈ U k } =
        ⋂ k : Fin l.length, (fun y : ∀ j, X j => y k.1) ⁻¹' U k := by
      ext y; simp
    rw [hEq]
    exact isOpen_iInter_of_finite fun k =>
      ((h𝓑bas k.1).isOpen (mem_iUnion.mpr ⟨l.get k, hU k⟩)).preimage (continuous_apply k.1)
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
  let 𝓑prod : ℕ → Set (Set (∀ k, X k)) := fun n => lay (Denumerable.ofNat (List ℕ) n)
  refine ⟨hT3, ⋃ n, 𝓑prod n, ?_, ⟨𝓑prod, fun n => hlay_cp _, rfl⟩⟩
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro W hW
    obtain ⟨n, hWn⟩ := mem_iUnion.mp hW
    exact hlay_open _ W hWn
  · intro x O hxO hO
    obtain ⟨I, t, ht_all, htO⟩ := isOpen_pi_iff.mp hO x hxO
    let N : ℕ := I.sup id + 1
    have hcoord : ∀ k : Fin N, ∃ m : ℕ, ∃ U ∈ 𝓑 k.1 m, x k.1 ∈ U ∧ (k.1 ∈ I → U ⊆ t k.1) := by
      intro k
      by_cases hk : k.1 ∈ I
      · obtain ⟨U, hU, hxkU, hUt⟩ :=
          (h𝓑bas k.1).exists_subset_of_mem_open (ht_all k.1 hk).2 (ht_all k.1 hk).1
        obtain ⟨m, hUm⟩ := mem_iUnion.mp hU
        exact ⟨m, U, hUm, hxkU, fun _ => hUt⟩
      · obtain ⟨U, hU, hxkU, _⟩ := (h𝓑bas k.1).exists_subset_of_mem_open trivial isOpen_univ
        obtain ⟨m, hUm⟩ := mem_iUnion.mp hU
        exact ⟨m, U, hUm, hxkU, fun h => (hk h).elim⟩
    choose m U hUm hxU hUt using hcoord
    let l : List ℕ := List.ofFn m
    have hlen : l.length = N := List.length_ofFn
    let U' : ∀ k : Fin l.length, Set (X k.1) := fun k => U ⟨k.1, hlen ▸ k.2⟩
    refine ⟨{ y | ∀ k : Fin l.length, y k.1 ∈ U' k }, mem_iUnion.mpr ⟨Encodable.encode l, ?_⟩,
      fun k => hxU ⟨k.1, hlen ▸ k.2⟩, ?_⟩
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

end M1Products

end Research.StratifiableCountablePi
