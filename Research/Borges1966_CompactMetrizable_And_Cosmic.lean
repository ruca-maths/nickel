import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Bases
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Basic.Countable.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Basic
import Proofs.L_0004
import Proofs.L_0008
import Targets.Defs

/-!
# Borges (1966) / Šneider (1945) / Michael (1966): Compact Stratifiable Spaces are Metrizable & Separable Stratifiable Spaces are Cosmic

We prove the classical network, cardinality, and metrizability structure theorems for stratifiable
spaces:

1. `stratifiable_has_sigma_discrete_closed_network` (**Heath 1969**):
   every stratifiable space has a σ-discrete closed network.
2. `countable_closed_network_of_compact_stratifiable`:
   in any compact stratifiable space, every discrete family of nonempty sets is finite, hence the
   space has a countable closed network.
3. `secondCountable_of_compact_stratifiable` & `metrizableSpace_of_compact_stratifiable`
   (**Borges 1966 / Šneider 1945**):
   every compact stratifiable space is **second-countable** and **metrizable**.
4. `metrizableSpace_compact_subtype_of_isStratifiable`:
   every compact subset `K` of **any** stratifiable space is second-countable and metrizable.
5. `countable_closed_network_of_separable_stratifiable` (**Borges 1966 / Michael 1966**):
   every separable stratifiable space has a countable closed network (is a **cosmic space**).
6. `hereditarily_separable_of_separable_stratifiable` &
   `hereditarily_lindelof_of_separable_stratifiable`:
   every subspace of a separable stratifiable space is separable and Lindelöf.
-/

namespace Research.BorgesCompactMetrizable

open Set Topology TopologicalSpace

/-! ## Part 1: Decreasing Stratification, Monotone Normality, and Disjoint Open Expansion -/

private theorem stratifiable_decreasing {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) :
    ∃ G : ℕ → Set X → Set X,
      (∀ n H, IsClosed H → IsOpen (G n H)) ∧
      (∀ n H, IsClosed H → H ⊆ G n H) ∧
      (∀ H, IsClosed H → (⋂ n, closure (G n H)) = H) ∧
      (∀ n H K, IsClosed H → IsClosed K → H ⊆ K → G n H ⊆ G n K) ∧
      (∀ n H, G (n + 1) H ⊆ G n H) := by
  obtain ⟨_, G₀, hG₀o, hG₀sub, hG₀inter, hG₀mono⟩ := hS
  let G : ℕ → Set X → Set X := fun n H => ⋂ k ∈ Finset.range (n + 1), G₀ k H
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · intro n H hH; exact isOpen_biInter_finset fun k _ => hG₀o k H hH
  · intro n H hH x hx; exact mem_iInter₂.mpr fun k _ => hG₀sub k H hH hx
  · intro H hH
    apply Subset.antisymm
    · have hsub_iInter : (⋂ n, closure (G n H)) ⊆ ⋂ n, closure (G₀ n H) := by
        intro x hx; rw [mem_iInter] at hx ⊢; intro n
        have hsub : G n H ⊆ G₀ n H := fun y hy =>
          mem_iInter₂.mp hy n (Finset.mem_range.mpr (Nat.lt_succ_self n))
        exact closure_mono hsub (hx n)
      exact hsub_iInter.trans (hG₀inter H hH).subset
    · intro x hx; rw [mem_iInter]; intro n
      exact subset_closure (mem_iInter₂.mpr fun k _ => hG₀sub k H hH hx)
  · intro n H K hH hK hsub x hx
    exact mem_iInter₂.mpr fun k hk => hG₀mono k H K hH hK hsub (mem_iInter₂.mp hx k hk)
  · intro n H x hx
    exact mem_iInter₂.mpr fun k hk =>
      mem_iInter₂.mp hx k (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))

private theorem stratifiable_mono_normal {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) :
    ∃ H : Set X → Set X → Set X,
      (∀ A B, IsClosed A → IsClosed B → IsOpen (H A B)) ∧
      (∀ A B, IsClosed A → IsClosed B → Disjoint A B → A ⊆ H A B) ∧
      (∀ A₁ A₂ B₁ B₂, IsClosed A₁ → IsClosed A₂ → IsClosed B₁ → IsClosed B₂ →
        A₁ ⊆ B₂ → A₂ ⊆ B₁ → Disjoint (H A₁ B₁) (H A₂ B₂)) := by
  obtain ⟨G, hGo, hGsub, hGinter, hGmono, hGdec⟩ := stratifiable_decreasing hS
  have hGanti : ∀ {m n} {F}, m ≤ n → G n F ⊆ G m F := by
    intro m n F hmn; induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hGdec _ F).trans ih
  let H : Set X → Set X → Set X := fun A B => ⋃ n, (G n A \ closure (G n B))
  refine ⟨H, ?_, ?_, ?_⟩
  · intro A B hA _; exact isOpen_iUnion fun n => (hGo n A hA).sdiff isClosed_closure
  · intro A B hA hB hdisj x hxA
    have hxNotB : x ∉ B := Set.disjoint_left.mp hdisj hxA
    rw [← hGinter B hB, mem_iInter] at hxNotB; push Not at hxNotB
    obtain ⟨n, hxn⟩ := hxNotB
    exact mem_iUnion.mpr ⟨n, hGsub n A hA hxA, hxn⟩
  · intro A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ h1 h2
    rw [Set.disjoint_left]; intro x hx1 hx2
    obtain ⟨m, hxmG, hxmNot⟩ := mem_iUnion.mp hx1
    obtain ⟨n, hxnG, hxnNot⟩ := mem_iUnion.mp hx2
    rcases le_total m n with hmn | hnm
    · exact hxmNot (subset_closure (hGmono m A₂ B₁ hA₂ hB₁ h2 (hGanti hmn hxnG)))
    · exact hxnNot (subset_closure (hGmono n A₁ B₂ hA₁ hB₂ h1 (hGanti hnm hxmG)))

private theorem normalSpace_of_isStratifiable {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) : NormalSpace X := by
  obtain ⟨H, hHo, hHsub, hHdisj⟩ := stratifiable_mono_normal hS
  exact ⟨fun A B hA hB hdisj =>
    ⟨H A B, H B A, hHo A B hA hB, hHo B A hB hA,
      hHsub A B hA hB hdisj, hHsub B A hB hA hdisj.symm,
      hHdisj A B B A hA hB hB hA Subset.rfl Subset.rfl⟩⟩

private theorem stratifiable_disjoint_open_expansion {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) {𝓕 : Set (Set X)}
    (hF_cl : ∀ F ∈ 𝓕, IsClosed F)
    (hF_disc : ∀ z : X, ∃ O : Set X, IsOpen O ∧ z ∈ O ∧
      ∀ F₁ ∈ 𝓕, ∀ F₂ ∈ 𝓕, (O ∩ F₁).Nonempty → (O ∩ F₂).Nonempty → F₁ = F₂) :
    ∃ W : 𝓕 → Set X,
      (∀ F : 𝓕, IsOpen (W F) ∧ F.1 ⊆ W F) ∧
      (∀ F₁ F₂ : 𝓕, F₁ ≠ F₂ → Disjoint (W F₁) (W F₂)) := by
  obtain ⟨H, hHo, hHsub, hHdisj⟩ := stratifiable_mono_normal hS
  have hUnion_cl : ∀ 𝓖 ⊆ 𝓕, IsClosed (⋃₀ 𝓖) := by
    intro 𝓖 h𝓖; rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]; intro z hz
    obtain ⟨O, hOo, hzO, hOuniq⟩ := hF_disc z
    by_cases hex : ∃ F ∈ 𝓖, (O ∩ F).Nonempty
    · obtain ⟨F₀, hF₀G, hF₀ne⟩ := hex
      have hzNot : z ∉ F₀ := fun h => hz ⟨F₀, hF₀G, h⟩
      refine Filter.mem_of_superset ((hOo.sdiff (hF_cl F₀ (h𝓖 hF₀G))).mem_nhds ⟨hzO, hzNot⟩) ?_
      rintro y ⟨hyO, hyNot⟩ ⟨F, hFG, hyF⟩
      have hEq : F = F₀ := hOuniq F (h𝓖 hFG) F₀ (h𝓖 hF₀G) ⟨y, hyO, hyF⟩ hF₀ne
      subst hEq; exact hyNot hyF
    · push Not at hex
      refine Filter.mem_of_superset (hOo.mem_nhds hzO) ?_
      rintro y hyO ⟨F, hFG, hyF⟩
      have hm : y ∈ O ∩ F := ⟨hyO, hyF⟩
      rw [hex F hFG] at hm; exact hm
  have hF_disj : ∀ F₁ F₂ : 𝓕, F₁ ≠ F₂ → Disjoint F₁.1 F₂.1 := by
    intro F₁ F₂ hne; rw [Set.disjoint_left]; intro z hz1 hz2
    obtain ⟨O, _, hzO, hOuniq⟩ := hF_disc z
    exact hne (Subtype.ext (hOuniq F₁.1 F₁.2 F₂.1 F₂.2 ⟨z, hzO, hz1⟩ ⟨z, hzO, hz2⟩))
  let W : 𝓕 → Set X := fun F => H F.1 (⋃₀ (𝓕 \ {F.1}))
  refine ⟨W, fun F => ⟨hHo _ _ (hF_cl F.1 F.2) (hUnion_cl _ sdiff_subset),
    hHsub _ _ (hF_cl F.1 F.2) (hUnion_cl _ sdiff_subset) (by
      rw [Set.disjoint_left]; rintro z hzF ⟨F', ⟨hF'mem, hF'ne⟩, hzF'⟩
      exact Set.disjoint_left.mp (hF_disj F ⟨F', hF'mem⟩
        (fun h => hF'ne (congrArg Subtype.val h.symm))) hzF hzF')⟩, ?_⟩
  intro F₁ F₂ hne
  have hne' : F₁.1 ≠ F₂.1 := fun h => hne (Subtype.ext h)
  exact hHdisj F₁.1 F₂.1 (⋃₀ (𝓕 \ {F₁.1})) (⋃₀ (𝓕 \ {F₂.1}))
    (hF_cl F₁.1 F₁.2) (hF_cl F₂.1 F₂.2)
    (hUnion_cl _ sdiff_subset) (hUnion_cl _ sdiff_subset)
    (fun z hz1 => ⟨F₁.1, ⟨F₁.2, hne'⟩, hz1⟩)
    (fun z hz2 => ⟨F₂.1, ⟨F₂.2, hne'.symm⟩, hz2⟩)

private theorem isStratifiable_subtype {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) (S : Set X) :
    MSpace.IsStratifiable S := by
  have : T1Space X := hS.1
  obtain ⟨_, G, hGo, hGs, hGi, hGm⟩ := hS
  refine ⟨inferInstance, fun n H => (Subtype.val : S → X) ⁻¹' G n (closure (Subtype.val '' H)),
    ?_, ?_, ?_, ?_⟩
  · intro n H _
    exact (hGo n _ isClosed_closure).preimage continuous_subtype_val
  · intro n H _ x hx
    exact hGs n _ isClosed_closure (subset_closure ⟨x, hx, rfl⟩)
  · intro H hH
    apply Subset.antisymm
    · intro x hx
      have hcl_in : x.1 ∈ closure (Subtype.val '' H) := by
        rw [← hGi _ isClosed_closure, mem_iInter]
        intro n
        have hxn : x ∈ closure ((Subtype.val : S → X) ⁻¹' G n (closure (Subtype.val '' H))) :=
          mem_iInter.mp hx n
        rw [mem_closure_iff] at hxn ⊢
        intro U hUo hxU
        obtain ⟨y, hyU, hyG⟩ := hxn ((Subtype.val : S → X) ⁻¹' U) (hUo.preimage continuous_subtype_val) hxU
        exact ⟨y.1, hyU, hyG⟩
      obtain ⟨C, hCcl, hCH⟩ := isClosed_induced_iff.mp hH
      have hsubC : Subtype.val '' H ⊆ C := by
        rintro _ ⟨y, hyH, rfl⟩
        rw [← hCH] at hyH; exact hyH
      have hxC : x.1 ∈ C := closure_minimal hsubC hCcl hcl_in
      rw [← hCH]; exact hxC
    · intro x hx; rw [mem_iInter]; intro n
      exact subset_closure (hGs n _ isClosed_closure (subset_closure ⟨x, hx, rfl⟩))
  · intro n H₁ H₂ _ _ hsub
    exact preimage_mono (hGm n _ _ isClosed_closure isClosed_closure (closure_mono (image_mono hsub)))

/-! ## Part 2: Heath (1969) σ-Discrete Closed Network -/

private lemma closurePreserving_image_closure {X : Type*} [TopologicalSpace X]
    {𝓑 : Set (Set X)} (hcp : MSpace.ClosurePreserving 𝓑) :
    MSpace.ClosurePreserving (closure '' 𝓑) := by
  intro 𝓖 h𝓖
  let 𝓗 : Set (Set X) := { B ∈ 𝓑 | closure B ∈ 𝓖 }
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
      _ = ⋃₀ (closure '' 𝓗) := hcp 𝓗 (fun _ h => h.1)
      _ ⊆ ⋃₀ (closure '' 𝓖) := h2
  · rintro x ⟨_, ⟨C, hCG, rfl⟩, hxC⟩
    exact closure_mono (Set.subset_sUnion_of_mem hCG) hxC

/-- **Heath (1969)**: Every stratifiable space has a σ-discrete closed network. -/
theorem stratifiable_has_sigma_discrete_closed_network {X : Type} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) :
    ∃ Net_fam : ℕ → Set (Set X),
      (∀ p, ∀ F ∈ Net_fam p, IsClosed F) ∧
      (∀ p z, ∃ O : Set X, IsOpen O ∧ z ∈ O ∧
        ∀ F₁ ∈ Net_fam p, ∀ F₂ ∈ Net_fam p, (O ∩ F₁).Nonempty → (O ∩ F₂).Nonempty → F₁ = F₂) ∧
      (∀ x : X, ∀ V : Set X, IsOpen V → x ∈ V → ∃ p, ∃ F ∈ Net_fam p, x ∈ F ∧ F ⊆ V) := by
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
    ext y; constructor
    · rintro ⟨_, ⟨K, hK, rfl⟩, hy⟩
      rw [(hK_closed m K hK.1).closure_eq] at hy; exact ⟨K, hK, hy⟩
    · rintro ⟨K, hK, hy⟩; exact ⟨closure K, ⟨K, hK, rfl⟩, subset_closure hy⟩
  let A : ℕ → ℕ → X → Set X := fun m k x => C m x \ G k (D m x)
  let Net_fam : ℕ → Set (Set X) := fun p => Set.range (A (Nat.unpair p).1 (Nat.unpair p).2)
  refine ⟨Net_fam, ?_, ?_, ?_⟩
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
          intro w hw; rw [mem_singleton_iff.mp hw]
          exact mem_iUnion₂.mpr ⟨K, ⟨hKm, hxK⟩, hzK⟩
        have hyG : y ∈ G k (D m x) := hGm k {z} (D m x) isClosed_singleton (hD_closed m x) hsub hyW.2
        exact hyA.2 hyG
    have h1 := hsame x₁ y₁ hy₁W hy₁A
    have h2 := hsame x₂ y₂ hy₂W hy₂A
    have hCeq : C m x₁ = C m x₂ := by
      ext w; simp only [C, mem_iInter, mem_ofPred_eq]
      exact ⟨fun h K ⟨hKm, hx₂K⟩ => h K ⟨hKm, (h1 K hKm).mpr ((h2 K hKm).mp hx₂K)⟩,
             fun h K ⟨hKm, hx₁K⟩ => h K ⟨hKm, (h2 K hKm).mpr ((h1 K hKm).mp hx₁K)⟩⟩
    have hDeq : D m x₁ = D m x₂ := by
      ext w; simp only [D, mem_iUnion, mem_ofPred_eq]
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
      intro hxD; obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hxD; exact hK.2 hxK
    rw [← hGi (D m x) (hD_closed m x), mem_iInter] at hx_not_D
    push Not at hx_not_D
    obtain ⟨k, hxk⟩ := hx_not_D
    refine ⟨Nat.pair m k, A m k x, ⟨x, by simp [Nat.unpair_pair]⟩, ?_, ?_⟩
    · exact ⟨mem_iInter₂.mpr fun K hK => hK.2, fun h => hxk (subset_closure h)⟩
    · intro y hyA
      exact hclB_sub (mem_iInter₂.mp hyA.1 (closure B) ⟨hclB_mem, hx_clB⟩)

/-! ## Part 3: Compact Stratifiable Spaces are Second-Countable and Metrizable (Borges 1966 / Šneider 1945) -/

/-- Every compact stratifiable space has a **countable closed network**. -/
theorem countable_closed_network_of_compact_stratifiable {X : Type} [TopologicalSpace X]
    [CompactSpace X] (hS : MSpace.IsStratifiable X) :
    ∃ Net : Set (Set X), Net.Countable ∧ (∀ F ∈ Net, IsClosed F) ∧
      (∀ x : X, ∀ V : Set X, IsOpen V → x ∈ V → ∃ F ∈ Net, x ∈ F ∧ F ⊆ V) := by
  classical
  obtain ⟨Net_fam, hNcl, hNdisc, hNnet⟩ := stratifiable_has_sigma_discrete_closed_network hS
  -- For each `p`, the family of nonempty sets in `Net_fam p` is finite by compactness of `X`.
  have hfin : ∀ p, { F ∈ Net_fam p | F.Nonempty }.Finite := by
    intro p
    choose O hOo hzO hOuniq using hNdisc p
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hOo (fun z _ => mem_iUnion.mpr ⟨z, hzO z⟩)
    -- Map each nonempty `F ∈ Net_fam p` to a `z ∈ s` with `(O z ∩ F).Nonempty`; this map is injective!
    have hex_z : ∀ F ∈ { F ∈ Net_fam p | F.Nonempty }, ∃ z ∈ s, (O z ∩ F).Nonempty := by
      rintro F ⟨_, ⟨x, hxF⟩⟩
      obtain ⟨z, hzs, hxz⟩ := mem_iUnion₂.mp (hs (mem_univ x))
      exact ⟨z, hzs, ⟨x, hxz, hxF⟩⟩
    let f : { F ∈ Net_fam p | F.Nonempty } → (s : Set X) :=
      fun F => ⟨(hex_z F.1 F.2).choose, (hex_z F.1 F.2).choose_spec.1⟩
    have hf_inj : Function.Injective f := by
      intro F₁ F₂ hEq
      have hz_eq : (hex_z F₁.1 F₁.2).choose = (hex_z F₂.1 F₂.2).choose := congrArg Subtype.val hEq
      have h1 := (hex_z F₁.1 F₁.2).choose_spec.2
      have h2 := (hex_z F₂.1 F₂.2).choose_spec.2
      rw [hz_eq] at h1
      exact Subtype.ext (hOuniq _ F₁.1 F₁.2.1 F₂.1 F₂.2.1 h1 h2)
    have : Finite (s : Set X) := s.finite_toSet.to_subtype
    have : Finite { F ∈ Net_fam p | F.Nonempty } := Finite.of_injective f hf_inj
    exact Set.toFinite _
  let Net : Set (Set X) := ⋃ p, { F ∈ Net_fam p | F.Nonempty }
  refine ⟨Net, Set.countable_iUnion fun p => (hfin p).countable, ?_, ?_⟩
  · rintro F hF
    obtain ⟨p, hFp, _⟩ := mem_iUnion.mp hF
    exact hNcl p F hFp
  · intro x V hVo hxV
    obtain ⟨p, F, hFp, hxF, hFV⟩ := hNnet x V hVo hxV
    exact ⟨F, mem_iUnion.mpr ⟨p, hFp, ⟨x, hxF⟩⟩, hxF, hFV⟩

/-- **Borges (1966) / Šneider (1945)**:
Every **compact stratifiable space** is **second-countable** (`SecondCountableTopology X`). -/
theorem secondCountable_of_compact_stratifiable {X : Type} [TopologicalSpace X]
    [CompactSpace X] (hS : MSpace.IsStratifiable X) :
    SecondCountableTopology X := by
  classical
  have : T1Space X := hS.1
  have : NormalSpace X := normalSpace_of_isStratifiable hS
  have : T3Space X := inferInstance
  obtain ⟨Net, hNcnt, hNcl, hNnet⟩ := countable_closed_network_of_compact_stratifiable hS
  -- For every disjoint pair `(A, B) ∈ Net × Net`, choose open `U A B` with `A ⊆ U A B` and `closure (U A B) ∩ B = ∅`.
  have hsep : ∀ p : { p : Net × Net // Disjoint p.1.1 p.2.1 },
      ∃ U : Set X, IsOpen U ∧ p.1.1.1 ⊆ U ∧ Disjoint (closure U) p.1.2.1 := by
    rintro ⟨⟨A, B⟩, hdisj⟩
    obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ :=
      normal_separation (hNcl A.1 A.2) (hNcl B.1 B.2) hdisj
    refine ⟨U, hUo, hAU, ?_⟩
    rw [Set.disjoint_left]; intro x hxCl hxB
    obtain ⟨y, hyV, hyU⟩ := mem_closure_iff.mp hxCl V hVo (hBV hxB)
    exact Set.disjoint_left.mp hUV hyU hyV
  choose U hUo hUsub hUdisj using hsep
  let 𝓢 : Set (Set X) := Set.range U
  have hScnt : 𝓢.Countable := by
    have : Countable Net := hNcnt.to_subtype
    exact Set.countable_range U
  -- Take all finite intersections of members of `𝓢` (indexed by `Finset` of `{ p : Net × Net // Disjoint p.1.1 p.2.1 }`).
  let P := { p : Net × Net // Disjoint p.1.1 p.2.1 }
  have : Countable Net := hNcnt.to_subtype
  have : Countable P := inferInstance
  let 𝓑 : Set (Set X) := Set.range fun s : Finset P => ⋂ p ∈ s, U p
  have hBcnt : 𝓑.Countable := Set.countable_range _
  have hBbasis : IsTopologicalBasis 𝓑 := by
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨s, rfl⟩
      exact isOpen_biInter_finset fun p _ => hUo p
    · intro x W hxW hWo
      -- `Wᶜ` is compact; cover `Wᶜ` by `(closure (U p))ᶜ` for `p = (A_y, B_y)` with `x ∈ A_y`, `y ∈ B_y`.
      have hcov_ex : ∀ y ∈ Wᶜ, ∃ p : P, x ∈ U p ∧ y ∈ (closure (U p))ᶜ := by
        intro y hyW
        have hxy : x ≠ y := fun h => hyW (h ▸ hxW)
        obtain ⟨Vx, Vy, hVxo, hVyo, hxVx, hyVy, hVdisj⟩ :=
          normal_separation isClosed_singleton isClosed_singleton
            (Set.disjoint_singleton.mpr hxy)
        obtain ⟨A, hAN, hxA, hAVx⟩ := hNnet x Vx hVxo (hxVx (mem_singleton x))
        obtain ⟨B, hBN, hyB, hBVy⟩ := hNnet y Vy hVyo (hyVy (mem_singleton y))
        have hABdisj : Disjoint A B := hVdisj.mono hAVx hBVy
        let p : P := ⟨(⟨A, hAN⟩, ⟨B, hBN⟩), hABdisj⟩
        refine ⟨p, hUsub p hxA, fun hyCl => Set.disjoint_left.mp (hUdisj p) hyCl hyB⟩
      obtain ⟨s, hs⟩ := hWo.isClosed_compl.isCompact.elim_finite_subcover
        (fun p : P => if x ∈ U p then (closure (U p))ᶜ else ∅)
        (fun p => by by_cases h : x ∈ U p <;> simp [h, isClosed_closure.isOpen_compl])
        (fun y hyW => by
          obtain ⟨p, hxp, hyp⟩ := hcov_ex y hyW
          exact mem_iUnion.mpr ⟨p, by simp only [ite_eq_left hxp]; exact hyp⟩)
      let s' : Finset P := s.filter (fun p => x ∈ U p)
      refine ⟨⋂ p ∈ s', U p, ⟨s', rfl⟩,
        mem_iInter₂.mpr fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
      intro z hz
      by_contra hzNotW
      obtain ⟨p, hps, hzp⟩ := mem_iUnion₂.mp (hs hzNotW)
      by_cases hxp : x ∈ U p
      · simp only [ite_eq_left hxp] at hzp
        exact hzp (subset_closure (mem_iInter₂.mp hz p (Finset.mem_filter.mpr ⟨hps, hxp⟩)))
      · simp only [ite_eq_right hxp] at hzp; exact hzp
  exact ⟨⟨𝓑, hBcnt, hBbasis.eq_generateFrom⟩⟩

/-- **Borges (1966) / Šneider (1945)**:
Every **compact stratifiable space** is **metrizable** (`MetrizableSpace X`). -/
theorem metrizableSpace_of_compact_stratifiable {X : Type} [TopologicalSpace X]
    [CompactSpace X] (hS : MSpace.IsStratifiable X) :
    MetrizableSpace X := by
  have : T1Space X := hS.1
  have : NormalSpace X := normalSpace_of_isStratifiable hS
  have : T3Space X := inferInstance
  have : SecondCountableTopology X := secondCountable_of_compact_stratifiable hS
  exact metrizableSpace_of_t3_secondCountable X

/-- Every **compact subset** `K` of **any** stratifiable space `X` is metrizable
(and second-countable) in the subspace topology. -/
theorem metrizableSpace_compact_subtype_of_isStratifiable {X : Type} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) {K : Set X} (hK : IsCompact K) :
    MetrizableSpace K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact metrizableSpace_of_compact_stratifiable (isStratifiable_subtype hS K)

/-! ## Part 4: Separable Stratifiable Spaces are Cosmic (Borges 1966 / Michael 1966) -/

/-- **Borges (1966) / Michael (1966)**:
Every **separable stratifiable space** has a **countable closed network** (i.e. is a cosmic space). -/
theorem countable_closed_network_of_separable_stratifiable {X : Type} [TopologicalSpace X]
    [SeparableSpace X] (hS : MSpace.IsStratifiable X) :
    ∃ Net : Set (Set X), Net.Countable ∧ (∀ F ∈ Net, IsClosed F) ∧
      (∀ x : X, ∀ V : Set X, IsOpen V → x ∈ V → ∃ F ∈ Net, x ∈ F ∧ F ⊆ V) := by
  classical
  obtain ⟨D, hDcnt, hDdense⟩ := exists_countable_dense X
  obtain ⟨Net_fam, hNcl, hNdisc, hNnet⟩ := stratifiable_has_sigma_discrete_closed_network hS
  have hcnt : ∀ p, { F ∈ Net_fam p | F.Nonempty }.Countable := by
    intro p
    let 𝓕 : Set (Set X) := { F ∈ Net_fam p | F.Nonempty }
    obtain ⟨W, hWprop, hWdisj⟩ := stratifiable_disjoint_open_expansion hS
      (𝓕 := 𝓕) (fun F hF => hNcl p F hF.1)
      (fun z => by
        obtain ⟨O, hOo, hzO, hOuniq⟩ := hNdisc p z
        exact ⟨O, hOo, hzO, fun F₁ hF₁ F₂ hF₂ => hOuniq F₁ hF₁.1 F₂ hF₂.1⟩)
    -- Each `W F` is nonempty open, hence meets the countable dense set `D`; disjointness gives injection `𝓕 ↪ D`.
    have hex_d : ∀ F : 𝓕, ∃ d ∈ D, d ∈ W F := fun F => by
      obtain ⟨x, hxF⟩ := F.2.2
      exact hDdense.exists_mem_open (hWprop F).1 ⟨x, (hWprop F).2 hxF⟩
    let f : 𝓕 → D := fun F => ⟨(hex_d F).choose, (hex_d F).choose_spec.1⟩
    have hf_inj : Function.Injective f := by
      intro F₁ F₂ hEq
      by_contra hne
      have hd_eq : (hex_d F₁).choose = (hex_d F₂).choose := congrArg Subtype.val hEq
      have h1 : (hex_d F₁).choose ∈ W F₁ := (hex_d F₁).choose_spec.2
      have h2 : (hex_d F₁).choose ∈ W F₂ := hd_eq ▸ (hex_d F₂).choose_spec.2
      exact Set.disjoint_left.mp (hWdisj F₁ F₂ hne) h1 h2
    have : Countable D := hDcnt.to_subtype
    have : Countable 𝓕 := Function.Injective.countable hf_inj
    exact Set.to_countable 𝓕
  let Net : Set (Set X) := ⋃ p, { F ∈ Net_fam p | F.Nonempty }
  refine ⟨Net, Set.countable_iUnion hcnt, ?_, ?_⟩
  · rintro F hF
    obtain ⟨p, hFp, _⟩ := mem_iUnion.mp hF
    exact hNcl p F hFp
  · intro x V hVo hxV
    obtain ⟨p, F, hFp, hxF, hFV⟩ := hNnet x V hVo hxV
    exact ⟨F, mem_iUnion.mpr ⟨p, hFp, ⟨x, hxF⟩⟩, hxF, hFV⟩

/-- Every subspace of a separable stratifiable space is **separable** (hereditary separability). -/
theorem hereditarily_separable_of_separable_stratifiable {X : Type} [TopologicalSpace X]
    [SeparableSpace X] (hS : MSpace.IsStratifiable X) (S : Set X) :
    SeparableSpace S := by
  classical
  obtain ⟨Net, hNcnt, _, hNnet⟩ := countable_closed_network_of_separable_stratifiable hS
  let NetS : Set (Set X) := { F ∈ Net | (F ∩ S).Nonempty }
  have hNScnt : NetS.Countable := hNcnt.mono (fun _ h => h.1)
  let pick : NetS → S := fun F => ⟨F.2.2.choose, F.2.2.choose_spec.2⟩
  have : Countable NetS := hNScnt.to_subtype
  refine ⟨⟨Set.range pick, Set.countable_range pick, ?_⟩⟩
  rw [dense_iff_inter_open]
  intro U hUo hUne
  obtain ⟨⟨x, hxS⟩, hxU⟩ := hUne
  obtain ⟨V, hVo, rfl⟩ := isOpen_induced_iff.mp hUo
  obtain ⟨F, hFN, hxF, hFV⟩ := hNnet x V hVo hxU
  let F' : NetS := ⟨F, hFN, ⟨x, hxF, hxS⟩⟩
  refine ⟨pick F', hFV F'.2.2.choose_spec.1, ⟨F', rfl⟩⟩

/-- Every subspace of a separable stratifiable space is **Lindelöf** (hereditary Lindelöf property):
every open cover of `S` has a countable subcover. -/
theorem hereditarily_lindelof_of_separable_stratifiable {X : Type} [TopologicalSpace X]
    [SeparableSpace X] (hS : MSpace.IsStratifiable X) (S : Set X)
    {ι : Type*} {U : ι → Set X} (hUo : ∀ i, IsOpen (U i)) (hUcov : S ⊆ ⋃ i, U i) :
    ∃ J : Set ι, J.Countable ∧ S ⊆ ⋃ i ∈ J, U i := by
  classical
  obtain ⟨Net, hNcnt, _, hNnet⟩ := countable_closed_network_of_separable_stratifiable hS
  let NetU : Set (Set X) := { F ∈ Net | ∃ i : ι, F ⊆ U i }
  have hNUcnt : NetU.Countable := hNcnt.mono (fun _ h => h.1)
  let idx : NetU → ι := fun F => F.2.2.choose
  have : Countable NetU := hNUcnt.to_subtype
  refine ⟨Set.range idx, Set.countable_range idx, ?_⟩
  intro x hxS
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hUcov hxS)
  obtain ⟨F, hFN, hxF, hFU⟩ := hNnet x (U i) (hUo i) hxi
  let F' : NetU := ⟨F, hFN, ⟨i, hFU⟩⟩
  exact mem_iUnion₂.mpr ⟨idx F', ⟨F', rfl⟩, F'.2.2.choose_spec hxF⟩

end Research.BorgesCompactMetrizable
