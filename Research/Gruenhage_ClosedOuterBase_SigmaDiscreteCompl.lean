import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Bases
import Mathlib.Basic.Countable.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Basic
import Defs.D_0001
import Targets.Defs

/-!
# Generalized Gruenhage Outer-Base Theorem: Closed Sets with σ-Discrete Complements in Stratifiable Spaces

We generalize Gruenhage (1978) to **arbitrary closed subsets** `A ⊆ X` of **any** stratifiable space
`X` whose complement `X \ A` is σ-discrete (not requiring `A` or `X` itself to be σ-discrete or
zero-dimensional!):

1. `hasCPClopenOuterBase_of_sigma_closedDiscrete_compl` &
   `hasCPClopenOuterBase_of_sigma_discrete_compl`:
   if `X` is stratifiable and `A ⊆ X` is closed with `X \ A` σ-discrete (in particular, countable),
   then `A` has a **single-layer closure-preserving clopen outer base** in `X`.
2. `closurePreserving_inter_open_of_clopen`:
   for any open set `D` and any closure-preserving family `𝓑` of clopen sets,
   `{ D ∩ B | B ∈ 𝓑 }` is closure-preserving.
3. `hasCPOuterBase_of_sigma_discrete_punctured_nhd`:
   in any stratifiable space `X`, any point `x₀` admitting an open neighborhood `U` with
   `U \ {x₀}` σ-discrete has `Defs.D_0001.HasCPOuterBase x₀`.
4. `isM1_of_stratifiable_secondCountable_closed_sigma_discrete_compl`:
   if `X` is stratifiable and `A ⊆ X` is a closed second-countable subspace (in particular, any
   compact subset of `X`, or any finite subset) such that `X \ A` is σ-discrete, then
   **`MSpace.IsM1 X`**.
-/

namespace Research.GruenhageSigmaDiscreteCompl

open Set Topology TopologicalSpace

/-! ## Part 1: Decreasing Stratification, Monotone Normality, and Discrete Open Expansion -/

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

private theorem isStratifiable_subtype {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) (S : Set X) :
    MSpace.IsStratifiable S := by
  have : T1Space X := hS.1
  obtain ⟨_, G, hGo, hGs, hGi, hGm⟩ := hS
  refine ⟨inferInstance, fun n H => (Subtype.val : S → X) ⁻¹' G n (closure (Subtype.val '' H)),
    ?_, ?_, ?_, ?_⟩
  · intro n H _; exact (hGo n _ isClosed_closure).preimage continuous_subtype_val
  · intro n H _ x hx; exact hGs n _ isClosed_closure (subset_closure ⟨x, hx, rfl⟩)
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
        obtain ⟨y, hyU, hyG⟩ := hxn ((Subtype.val : S → X) ⁻¹' U)
          (hUo.preimage continuous_subtype_val) hxU
        exact ⟨y.1, hyU, hyG⟩
      obtain ⟨C, hCcl, hCH⟩ := isClosed_induced_iff.mp hH
      have hsubC : Subtype.val '' H ⊆ C := by
        rintro _ ⟨y, hyH, rfl⟩; rw [← hCH] at hyH; exact hyH
      have hxC : x.1 ∈ C := closure_minimal hsubC hCcl hcl_in
      rw [← hCH]; exact hxC
    · intro x hx; rw [mem_iInter]; intro n
      exact subset_closure (hGs n _ isClosed_closure (subset_closure ⟨x, hx, rfl⟩))
  · intro n H₁ H₂ _ _ hsub
    exact preimage_mono (hGm n _ _ isClosed_closure isClosed_closure (closure_mono (image_mono hsub)))

private theorem stratifiable_discrete_open_expansion {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) {D : Set X}
    (hD_disc : ∀ S : Set X, S ⊆ D → IsClosed S) :
    ∃ W : D → Set X,
      (∀ d : D, IsOpen (W d) ∧ d.1 ∈ W d) ∧
      (∀ z : X, ∃ O : Set X, IsOpen O ∧ z ∈ O ∧
        ∀ d₁ d₂ : D, (O ∩ W d₁).Nonempty → (O ∩ W d₂).Nonempty → d₁ = d₂) := by
  have : T1Space X := hS.1
  obtain ⟨H, hHo, hHsub, hHdisj⟩ := stratifiable_mono_normal hS
  let U : D → Set X := fun d => H {d.1} (D \ {d.1})
  have hUo : ∀ d : D, IsOpen (U d) := fun d =>
    hHo {d.1} (D \ {d.1}) isClosed_singleton (hD_disc _ sdiff_subset)
  have hUmem : ∀ d : D, d.1 ∈ U d := fun d =>
    hHsub {d.1} (D \ {d.1}) isClosed_singleton (hD_disc _ sdiff_subset)
      (Set.disjoint_singleton_left.mpr fun h => h.2 rfl) (mem_singleton d.1)
  have hUdisj : ∀ d₁ d₂ : D, d₁ ≠ d₂ → Disjoint (U d₁) (U d₂) := fun d₁ d₂ hne =>
    hHdisj {d₁.1} {d₂.1} (D \ {d₁.1}) (D \ {d₂.1})
      isClosed_singleton isClosed_singleton (hD_disc _ sdiff_subset) (hD_disc _ sdiff_subset)
      (Set.singleton_subset_iff.mpr ⟨d₁.2, fun h => hne (Subtype.ext h)⟩)
      (Set.singleton_subset_iff.mpr ⟨d₂.2, fun h => hne (Subtype.ext h.symm)⟩)
  let W : D → Set X := fun d => H {d.1} (U d)ᶜ
  have hW_sub_U : ∀ d : D, W d ⊆ U d := fun d y hyW => by
    by_contra hyNot
    have hdisj := hHdisj {d.1} {y} (U d)ᶜ {d.1}
      isClosed_singleton isClosed_singleton (hUo d).isClosed_compl isClosed_singleton
      Subset.rfl (Set.singleton_subset_iff.mpr hyNot)
    exact Set.disjoint_left.mp hdisj hyW
      (hHsub {y} {d.1} isClosed_singleton isClosed_singleton
        (Set.disjoint_singleton_left.mpr fun e => hyNot (e ▸ hUmem d)) (mem_singleton y))
  refine ⟨W, fun d => ⟨hHo _ _ isClosed_singleton (hUo d).isClosed_compl,
    hHsub {d.1} (U d)ᶜ isClosed_singleton (hUo d).isClosed_compl
      (Set.disjoint_singleton_left.mpr fun h => h (hUmem d)) (mem_singleton d.1)⟩, ?_⟩
  intro z
  by_cases hzU : ∃ d₀ : D, z ∈ U d₀
  · obtain ⟨d₀, hzd₀⟩ := hzU
    refine ⟨U d₀, hUo d₀, hzd₀, fun d₁ d₂ ⟨y₁, hy₁U, hy₁W⟩ ⟨y₂, hy₂U, hy₂W⟩ => ?_⟩
    have h1 : d₁ = d₀ := by
      by_contra hne
      exact Set.disjoint_left.mp (hUdisj d₀ d₁ (Ne.symm hne)) hy₁U (hW_sub_U d₁ hy₁W)
    have h2 : d₂ = d₀ := by
      by_contra hne
      exact Set.disjoint_left.mp (hUdisj d₀ d₂ (Ne.symm hne)) hy₂U (hW_sub_U d₂ hy₂W)
    exact h1.trans h2.symm
  · push Not at hzU
    have hzNotD : z ∉ D := fun hzD => hzU ⟨z, hzD⟩ (hUmem ⟨z, hzD⟩)
    refine ⟨H {z} D, hHo _ _ isClosed_singleton (hD_disc D Subset.rfl),
      hHsub {z} D isClosed_singleton (hD_disc D Subset.rfl)
        (Set.disjoint_singleton_left.mpr hzNotD) (mem_singleton z),
      fun d₁ _ ⟨y₁, hy₁O, hy₁W⟩ _ => ?_⟩
    have hdisj := hHdisj {z} {d₁.1} D (U d₁)ᶜ
      isClosed_singleton isClosed_singleton (hD_disc D Subset.rfl) (hUo d₁).isClosed_compl
      (Set.singleton_subset_iff.mpr (hzU d₁)) (Set.singleton_subset_iff.mpr d₁.2)
    exact (Set.disjoint_left.mp hdisj hy₁O hy₁W).elim

private theorem normal_cl_separation {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint (closure U) (closure V) := by
  obtain ⟨U₁, V₁, hU₁o, hV₁o, hAU₁, hBV₁, hdisj₁⟩ := normal_separation hA hB hdisj
  have hclU₁_disj_B : Disjoint (closure U₁) B := by
    rw [Set.disjoint_left]; intro x hxCl hxB
    obtain ⟨y, hyV₁, hyU₁⟩ := mem_closure_iff.mp hxCl V₁ hV₁o (hBV₁ hxB)
    exact Set.disjoint_left.mp hdisj₁ hyU₁ hyV₁
  obtain ⟨U₂, V₂, hU₂o, hV₂o, hclU₁_U₂, hBV₂, hdisj₂⟩ :=
    normal_separation isClosed_closure hB hclU₁_disj_B
  refine ⟨U₁, V₂, hU₁o, hV₂o, hAU₁, hBV₂, ?_⟩
  rw [Set.disjoint_left]; intro x hxCl₁ hxCl₂
  obtain ⟨y, hyU₂, hyV₂⟩ := mem_closure_iff.mp hxCl₂ U₂ hU₂o (hclU₁_U₂ hxCl₁)
  exact Set.disjoint_left.mp hdisj₂ hyU₂ hyV₂

private theorem stronglyZeroDim_of_normal_sigma_closedDiscrete {X : Type*} [TopologicalSpace X]
    [NormalSpace X] {F : ℕ → Set X}
    (hF_disc : ∀ n (S : Set X), S ⊆ F n → IsClosed S)
    (hF_cover : (⋃ n, F n) = Set.univ) :
    ∀ A B : Set X, IsClosed A → IsClosed B → Disjoint A B →
      ∃ W : Set X, IsClopen W ∧ A ⊆ W ∧ Disjoint W B := by
  intro A B hA hB hdisj
  let State := { p : Set X × Set X //
    IsOpen p.1 ∧ IsOpen p.2 ∧ Disjoint (closure p.1) (closure p.2) }
  have h0_ex := normal_cl_separation hA hB hdisj
  let st0 : State := ⟨(h0_ex.choose, h0_ex.choose_spec.choose),
    h0_ex.choose_spec.choose_spec.1,
    h0_ex.choose_spec.choose_spec.2.1,
    h0_ex.choose_spec.choose_spec.2.2.2.2⟩
  have hA_st0 : A ⊆ st0.1.1 := h0_ex.choose_spec.choose_spec.2.2.1
  have hB_st0 : B ⊆ st0.1.2 := h0_ex.choose_spec.choose_spec.2.2.2.1
  have hstep_ex : ∀ (n : ℕ) (st : State),
      ∃ st' : State,
        closure st.1.1 ⊆ st'.1.1 ∧
        closure st.1.2 ⊆ st'.1.2 ∧
        F n ⊆ st'.1.1 ∪ st'.1.2 := by
    intro n st
    let D₂ : Set X := (F n \ (st.1.1 ∪ st.1.2)) \ closure st.1.1
    have hD₂_cl : IsClosed D₂ := hF_disc n D₂ (fun x hx => hx.1.1)
    have hdisj' : Disjoint (closure st.1.1) (closure st.1.2 ∪ D₂) := by
      rw [Set.disjoint_union_right]
      exact ⟨st.2.2.2, Set.disjoint_left.mpr fun x hxCl hxD₂ => hxD₂.2 hxCl⟩
    obtain ⟨U', V', hU'o, hV'o, hclU_U', hclVD₂_V', hdisj'⟩ :=
      normal_cl_separation isClosed_closure (isClosed_closure.union hD₂_cl) hdisj'
    refine ⟨⟨(U', V'), hU'o, hV'o, hdisj'⟩, hclU_U', subset_union_left.trans hclVD₂_V', ?_⟩
    intro x hxFn
    by_cases hUV : x ∈ st.1.1 ∪ st.1.2
    · rcases hUV with hU | hV
      · exact Or.inl (hclU_U' (subset_closure hU))
      · exact Or.inr (hclVD₂_V' (Or.inl (subset_closure hV)))
    · by_cases hclU : x ∈ closure st.1.1
      · exact Or.inl (hclU_U' hclU)
      · exact Or.inr (hclVD₂_V' (Or.inr ⟨⟨hxFn, hUV⟩, hclU⟩))
  let seq : ℕ → State := fun n =>
    Nat.rec st0 (fun k stk => (hstep_ex k stk).choose) n
  have hseq_U_succ : ∀ n, (seq n).1.1 ⊆ (seq (n + 1)).1.1 := fun n =>
    subset_closure.trans (hstep_ex n (seq n)).choose_spec.1
  have hseq_V_succ : ∀ n, (seq n).1.2 ⊆ (seq (n + 1)).1.2 := fun n =>
    subset_closure.trans (hstep_ex n (seq n)).choose_spec.2.1
  have hseq_U_mono : ∀ {m n}, m ≤ n → (seq m).1.1 ⊆ (seq n).1.1 := by
    intro m n hmn; induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact ih.trans (hseq_U_succ _)
  have hseq_V_mono : ∀ {m n}, m ≤ n → (seq m).1.2 ⊆ (seq n).1.2 := by
    intro m n hmn; induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact ih.trans (hseq_V_succ _)
  let W : Set X := ⋃ n, (seq n).1.1
  let W' : Set X := ⋃ n, (seq n).1.2
  have hWo : IsOpen W := isOpen_iUnion fun n => (seq n).2.1
  have hW'o : IsOpen W' := isOpen_iUnion fun n => (seq n).2.2.1
  have hdisjWW' : Disjoint W W' := by
    rw [Set.disjoint_left]; intro x hxW hxW'
    obtain ⟨m, hxm⟩ := mem_iUnion.mp hxW
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hxW'
    exact Set.disjoint_left.mp (seq (max m n)).2.2.2
      (subset_closure (hseq_U_mono (le_max_left m n) hxm))
      (subset_closure (hseq_V_mono (le_max_right m n) hxn))
  have hunionWW' : W ∪ W' = Set.univ := by
    ext x; simp only [mem_univ, iff_true]
    obtain ⟨n, hxn⟩ := mem_iUnion.mp (show x ∈ ⋃ n, F n by rw [hF_cover]; trivial)
    rcases (hstep_ex n (seq n)).choose_spec.2.2 hxn with hU | hV
    · exact Or.inl (mem_iUnion.mpr ⟨n + 1, hU⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨n + 1, hV⟩)
  have hWcl : IsClosed W := by
    have hEq : W = W'ᶜ := by
      ext x; constructor
      · exact fun hxW hxW' => Set.disjoint_left.mp hdisjWW' hxW hxW'
      · intro hxNot
        have hxU : x ∈ W ∪ W' := by rw [hunionWW']; trivial
        exact hxU.resolve_right hxNot
    rw [hEq]; exact hW'o.isClosed_compl
  refine ⟨W, ⟨hWcl, hWo⟩, fun x hxA => mem_iUnion.mpr ⟨0, hA_st0 hxA⟩, ?_⟩
  rw [Set.disjoint_left]; intro x hxW hxB
  exact Set.disjoint_left.mp hdisjWW' hxW (mem_iUnion.mpr ⟨0, hB_st0 hxB⟩)

/-! ## Part 2: Generalized Gruenhage CP Clopen Outer Base for Closed Sets with σ-Discrete Complement -/

/-- Helper: in a stratifiable space `X`, any open subset `O` that is a countable union of discrete
subspaces `D n` is a countable union of **closed discrete** (in `X`) subsets `F m ⊆ O`. -/
private theorem sigma_closedDiscrete_in_open_of_sigma_discrete {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) {O : Set X} (hOo : IsOpen O)
    {D : ℕ → Set X}
    (hD_disc : ∀ n, ∀ x ∈ D n, ∃ U : Set X, IsOpen U ∧ U ∩ D n = {x})
    (hD_eq : (⋃ n, D n) = O) :
    ∃ F : ℕ → Set X,
      (∀ m (S : Set X), S ⊆ F m → IsClosed S) ∧
      (⋃ m, F m) = O := by
  have : T1Space X := hS.1
  obtain ⟨G, hGo, hGsub, hGinter, _, _⟩ := stratifiable_decreasing hS
  have hO_ex : ∀ n, ∃ U_all : Set X, IsOpen U_all ∧ D n ⊆ U_all ∧ U_all ⊆ O ∧
      ∀ z ∈ U_all, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ ∃ x ∈ D n, U ∩ D n = {x} := by
    intro n
    choose U hUo hUeq using fun x : D n => hD_disc n x.1 x.2
    refine ⟨(⋃ x : D n, U x) ∩ O, (isOpen_iUnion hUo).inter hOo, fun x hx => ?_,
      inter_subset_right, fun z hz => ?_⟩
    · refine ⟨mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩, by rw [← hD_eq]; exact mem_iUnion.mpr ⟨n, hx⟩⟩
      have : x ∈ U ⟨x, hx⟩ ∩ D n := by rw [hUeq ⟨x, hx⟩]; exact mem_singleton x
      exact this.1
    · obtain ⟨x, hzx⟩ := mem_iUnion.mp hz.1
      exact ⟨U x, hUo x, hzx, x.1, x.2, hUeq x⟩
  choose U_all hUo hDU hUsubO hUloc using hO_ex
  let F : ℕ → Set X := fun m =>
    let p := Nat.unpair m
    D p.1 ∩ (G p.2 (U_all p.1)ᶜ)ᶜ
  refine ⟨F, ?_, ?_⟩
  · intro m S hSF
    set p := Nat.unpair m
    rw [← closure_subset_iff_isClosed]; intro z hzCl
    have hK_cl : IsClosed (G p.2 (U_all p.1)ᶜ)ᶜ :=
      (hGo p.2 (U_all p.1)ᶜ (hUo p.1).isClosed_compl).isClosed_compl
    have hzK : z ∈ (G p.2 (U_all p.1)ᶜ)ᶜ :=
      closure_minimal (hSF.trans inter_subset_right) hK_cl hzCl
    have hzUall : z ∈ U_all p.1 := by
      by_contra hzNot
      exact hzK (hGsub p.2 (U_all p.1)ᶜ (hUo p.1).isClosed_compl hzNot)
    obtain ⟨U, hUopen, hzU, x, hxD, hUeq⟩ := hUloc p.1 z hzUall
    obtain ⟨y, hyU, hyS⟩ := mem_closure_iff.mp hzCl U hUopen hzU
    have hyx : y = x := by
      have : y ∈ U ∩ D p.1 := ⟨hyU, (hSF hyS).1⟩
      rw [hUeq] at this; exact this
    subst hyx
    by_contra hzNotS
    have hzy : z ≠ y := fun h => hzNotS (h ▸ hyS)
    obtain ⟨w, ⟨hwU, hwy⟩, hwS⟩ :=
      mem_closure_iff.mp hzCl (U \ {y}) (hUopen.sdiff isClosed_singleton) ⟨hzU, hzy⟩
    have hwy' : w = y := by
      have : w ∈ U ∩ D p.1 := ⟨hwU, (hSF hwS).1⟩
      rw [hUeq] at this; exact this
    exact hwy hwy'
  · ext x; constructor
    · intro hx; obtain ⟨m, hxm⟩ := mem_iUnion.mp hx
      rw [← hD_eq]; exact mem_iUnion.mpr ⟨(Nat.unpair m).1, hxm.1⟩
    · intro hxO
      obtain ⟨n, hxn⟩ := mem_iUnion.mp (by rw [hD_eq]; exact hxO)
      have hxNotC : x ∉ (U_all n)ᶜ := fun h => h (hDU n hxn)
      rw [← hGinter (U_all n)ᶜ (hUo n).isClosed_compl, mem_iInter] at hxNotC
      push Not at hxNotC
      obtain ⟨k, hxk⟩ := hxNotC
      refine mem_iUnion.mpr ⟨Nat.pair n k, ?_⟩
      simp only [F, Nat.unpair_pair]
      exact ⟨hxn, fun h => hxk (subset_closure h)⟩

/-- **Generalized Gruenhage Outer-Base Theorem**:
Let `X` be any stratifiable space and `A ⊆ X` be any closed subset whose complement `X \ A` is a
countable union of closed discrete subsets `F n` of `X`. Then `A` has a **single-layer
closure-preserving clopen outer base** in `X`. -/
theorem hasCPClopenOuterBase_of_sigma_closedDiscrete_compl {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) {A : Set X} (hA : IsClosed A)
    {F : ℕ → Set X}
    (hF_disc : ∀ n (S : Set X), S ⊆ F n → IsClosed S)
    (hF_eq : (⋃ n, F n) = Aᶜ) :
    ∃ 𝓑 : Set (Set X),
      (∀ B ∈ 𝓑, IsClopen B ∧ A ⊆ B) ∧
      (∀ W : Set X, IsOpen W → A ⊆ W → ∃ B ∈ 𝓑, B ⊆ W) ∧
      MSpace.ClosurePreserving 𝓑 := by
  classical
  have : T1Space X := hS.1
  have : NormalSpace X := normalSpace_of_isStratifiable hS
  have : T3Space X := inferInstance
  -- `Aᶜ` is an open σ-closed-discrete stratifiable subspace, hence strongly zero-dimensional!
  have hS_compl : MSpace.IsStratifiable (Aᶜ : Set X) := isStratifiable_subtype hS Aᶜ
  have : NormalSpace (Aᶜ : Set X) := normalSpace_of_isStratifiable hS_compl
  have hF_sub_compl : ∀ n, F n ⊆ Aᶜ := fun n x hx => by
    rw [← hF_eq]; exact mem_iUnion.mpr ⟨n, hx⟩
  let Fsub : ℕ → Set (Aᶜ : Set X) := fun n => (Subtype.val : (Aᶜ : Set X) → X) ⁻¹' F n
  have hFsub_disc : ∀ n (S : Set (Aᶜ : Set X)), S ⊆ Fsub n → IsClosed S := fun n S hSsub => by
    have hIm_cl : IsClosed (Subtype.val '' S) :=
      hF_disc n (Subtype.val '' S) (by rintro _ ⟨y, hyS, rfl⟩; exact hSsub hyS)
    rw [isClosed_induced_iff]
    exact ⟨Subtype.val '' S, hIm_cl, by ext y; simp⟩
  have hFsub_cover : (⋃ n, Fsub n) = Set.univ := by
    ext y; simp only [mem_iUnion, mem_univ, iff_true, Fsub, mem_preimage]
    exact mem_iUnion.mp (by rw [hF_eq]; exact y.2)
  have hInd0_compl := stronglyZeroDim_of_normal_sigma_closedDiscrete hFsub_disc hFsub_cover
  -- Local clopen shrinking in `X` for any point `x ∈ Aᶜ` and open `U ⊆ Aᶜ` with `x ∈ U`:
  have hshrink_clopen : ∀ {x : X} {U : Set X}, x ∈ Aᶜ → IsOpen U → x ∈ U → U ⊆ Aᶜ →
      ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
    intro x U hxAc hUo hxU hUAc
    -- First shrink `U` by normality of `X` to open `U₁` with `x ∈ U₁` and `closure U₁ ⊆ U ⊆ Aᶜ`.
    obtain ⟨U₁, _, hU₁o, _, hxU₁, hUcV, hdisj₁⟩ :=
      normal_cl_separation isClosed_singleton hUo.isClosed_compl
        (Set.disjoint_singleton_left.mpr fun h => h hxU)
    have hclU₁_sub_U : closure U₁ ⊆ U := fun y hyCl => by
      by_contra hyNot; exact Set.disjoint_left.mp hdisj₁ hyCl (subset_closure (hUcV hyNot))
    -- Separate `{⟨x, hxAc⟩}` from `(Subtype.val ⁻¹' U₁)ᶜ` inside `Aᶜ` by a clopen `Vsub ⊆ Aᶜ`.
    let x' : (Aᶜ : Set X) := ⟨x, hxAc⟩
    let U₁sub : Set (Aᶜ : Set X) := (Subtype.val : (Aᶜ : Set X) → X) ⁻¹' U₁
    have hU₁sub_o : IsOpen U₁sub := hU₁o.preimage continuous_subtype_val
    obtain ⟨Vsub, hVsub_clop, hxVsub, hVsub_disj⟩ :=
      hInd0_compl {x'} U₁subᶜ isClosed_singleton hU₁sub_o.isClosed_compl
        (Set.disjoint_singleton_left.mpr fun h => h (hxU₁ (mem_singleton x)))
    have hVsub_sub : Vsub ⊆ U₁sub := fun y hy => by
      by_contra hyNot; exact Set.disjoint_left.mp hVsub_disj hy hyNot
    let V : Set X := Subtype.val '' Vsub
    have hVo : IsOpen V := hA.isOpen_compl.isOpenMap_subtype_val Vsub hVsub_clop.2
    have hVsub_U₁ : V ⊆ U₁ := by rintro _ ⟨y, hyV, rfl⟩; exact hVsub_sub hyV
    have hVcl : IsClosed V := by
      rw [← closure_subset_iff_isClosed]; intro z hzCl
      have hzU : z ∈ U := hclU₁_sub_U (closure_mono hVsub_U₁ hzCl)
      have hzAc : z ∈ Aᶜ := hUAc hzU
      have hzVsub : (⟨z, hzAc⟩ : (Aᶜ : Set X)) ∈ closure Vsub := by
        rw [mem_closure_iff]; intro W hWo hzW
        obtain ⟨W', hW'o, rfl⟩ := isOpen_induced_iff.mp hWo
        obtain ⟨q, hqW', ⟨y, hyV, rfl⟩⟩ := mem_closure_iff.mp hzCl W' hW'o hzW
        exact ⟨y, hqW', hyV⟩
      rw [hVsub_clop.1.closure_eq] at hzVsub
      exact ⟨⟨z, hzAc⟩, hzVsub, rfl⟩
    exact ⟨V, ⟨hVcl, hVo⟩, ⟨x', hxVsub (mem_singleton x'), rfl⟩, hVsub_U₁.trans (subset_closure.trans hclU₁_sub_U)⟩
  -- Step 1: Disjointify `F n` into pairwise disjoint closed discrete layers `E m` covering `Aᶜ`.
  obtain ⟨G, hGo, hGsub, hGinter, hGmono, hGdec⟩ := stratifiable_decreasing hS
  have hGanti : ∀ {m n} {K}, m ≤ n → G n K ⊆ G m K := by
    intro m n K hmn; induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hGdec _ K).trans ih
  let E : ℕ → Set X := fun m => F m \ (⋃ j < m, F j)
  have hE_disc : ∀ m (S : Set X), S ⊆ E m → IsClosed S := fun m S hSE =>
    hF_disc m S (hSE.trans sdiff_subset)
  have hE_sub_Ac : ∀ m, E m ⊆ Aᶜ := fun m x hx => hF_sub_compl m hx.1
  have hE_cover : ∀ x ∈ Aᶜ, ∃ m, x ∈ E m := by
    intro x hxAc
    have hex : ∃ n, x ∈ F n := mem_iUnion.mp (by rw [hF_eq]; exact hxAc)
    let m := Nat.find hex
    refine ⟨m, Nat.find_spec hex, ?_⟩
    intro hlt
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hlt
    exact Nat.find_min hex hj hxj
  -- Step 2: Discrete open expansion of each `E m`, then shrink to clopen `V m x` in `X` avoiding
  -- `A ∪ ⋃ j < m, E j` and contained in `G m {x}`.
  choose Wexp hWexp_open hWexp_disc using fun m =>
    stratifiable_discrete_open_expansion hS (hE_disc m)
  have hV_ex : ∀ (m : ℕ) (x : E m),
      ∃ V : Set X, IsClopen V ∧ x.1 ∈ V ∧ V ⊆ Wexp m x ∧ V ⊆ G m {x.1} ∧
        Disjoint V A ∧ ∀ j < m, Disjoint V (E j) := by
    intro m x
    let prev : Set X := A ∪ ⋃ j ∈ Finset.range m, E j
    have hprev_cl : IsClosed prev :=
      hA.union (isClosed_biUnion_finset fun j _ => hE_disc j (E j) Subset.rfl)
    have hx_not_prev : x.1 ∉ prev := by
      rintro (hxA | hxPrev)
      · exact hE_sub_Ac m x.2 hxA
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxPrev
        exact x.2.2 (mem_iUnion₂.mpr ⟨j, Finset.mem_range.mp hj, hxj.1⟩)
    let U : Set X := Wexp m x ∩ G m {x.1} ∩ prevᶜ
    have hUo : IsOpen U :=
      ((hWexp_open m x).1.inter (hGo m {x.1} isClosed_singleton)).inter hprev_cl.isOpen_compl
    have hxU : x.1 ∈ U :=
      ⟨⟨(hWexp_open m x).2, hGsub m {x.1} isClosed_singleton (mem_singleton x.1)⟩, hx_not_prev⟩
    have hUAc : U ⊆ Aᶜ := fun y hy hyA => hy.2 (Or.inl hyA)
    obtain ⟨V, hVclop, hxV, hVU⟩ := hshrink_clopen (hE_sub_Ac m x.2) hUo hxU hUAc
    refine ⟨V, hVclop, hxV, fun y hy => (hVU hy).1.1, fun y hy => (hVU hy).1.2,
      Set.disjoint_left.mpr fun y hyV hyA => (hVU hyV).2 (Or.inl hyA),
      fun j hjm => Set.disjoint_left.mpr fun y hyV hyEj =>
        (hVU hyV).2 (Or.inr (mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjm, hyEj⟩))⟩
  choose V hV_clop hV_mem hV_subW hV_subG hV_disjA hV_disjE using hV_ex
  -- Step 3: Define the Gruenhage clopen family `𝓑 = { B K | K closed, Disjoint K A }`.
  let B : Set X → Set X := fun K => (⋃ m, ⋃ x : E m, if x.1 ∈ K then V m x else ∅)ᶜ
  have hB_supA : ∀ K, A ⊆ B K := by
    intro K a ha haIn
    obtain ⟨m, haIn⟩ := mem_iUnion.mp haIn
    obtain ⟨x, hax⟩ := mem_iUnion.mp haIn
    by_cases hxK : x.1 ∈ K
    · simp only [ite_eq_left hxK] at hax
      exact Set.disjoint_left.mp (hV_disjA m x) hax ha
    · simp only [ite_eq_right hxK] at hax; exact hax
  have hB_disj : ∀ K, Disjoint K A → Disjoint (B K) K := by
    intro K hKA
    rw [Set.disjoint_left]; intro y hyB hyK
    have hyAc : y ∈ Aᶜ := fun hyA => Set.disjoint_left.mp hKA hyK hyA
    obtain ⟨m, hym⟩ := hE_cover y hyAc
    apply hyB
    refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨⟨y, hym⟩, ?_⟩⟩
    simp only [ite_eq_left hyK]; exact hV_mem m ⟨y, hym⟩
  have hB_clopen : ∀ K, IsClosed K → Disjoint K A → IsClopen (B K) := by
    intro K hK hKA
    have hB_cl : IsClosed (B K) := by
      refine IsOpen.isClosed_compl (isOpen_iUnion fun m => isOpen_iUnion fun x => ?_)
      by_cases hxK : x.1 ∈ K
      · simp only [ite_eq_left hxK]; exact (hV_clop m x).2
      · simp only [ite_eq_right hxK]; exact isOpen_empty
    have hB_open : IsOpen (B K) := by
      rw [isOpen_iff_mem_nhds]; intro z hzB
      have hzNotK : z ∉ K := Set.disjoint_left.mp (hB_disj K hKA) hzB
      rw [← hGinter K hK, mem_iInter] at hzNotK; push Not at hzNotK
      obtain ⟨N, hzNotGN⟩ := hzNotK
      let C : ℕ → Set X := fun m => ⋃ x : E m, if x.1 ∈ K then V m x else ∅
      have hC_cl : ∀ m, IsClosed (C m) := fun m => by
        rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]; intro q hqNotC
        obtain ⟨O, hOo, hqO, hOuniq⟩ := hWexp_disc m q
        by_cases hex : ∃ x : E m, (O ∩ Wexp m x).Nonempty
        · obtain ⟨x₀', hx₀'⟩ := hex
          have hqNotVx : q ∉ (if x₀'.1 ∈ K then V m x₀' else ∅) := fun h =>
            hqNotC (mem_iUnion.mpr ⟨x₀', h⟩)
          have hVx_cl : IsClosed (if x₀'.1 ∈ K then V m x₀' else ∅) := by
            by_cases h : x₀'.1 ∈ K
            · simp only [ite_eq_left h]; exact (hV_clop m x₀').1
            · simp only [ite_eq_right h]; exact isClosed_empty
          refine Filter.mem_of_superset ((hOo.sdiff hVx_cl).mem_nhds ⟨hqO, hqNotVx⟩) ?_
          intro r ⟨hrO, hrNotVx⟩ hrC
          obtain ⟨x, hrx⟩ := mem_iUnion.mp hrC
          by_cases hxK : x.1 ∈ K
          · simp only [ite_eq_left hxK] at hrx
            have hEq : x = x₀' := hOuniq x x₀' ⟨r, hrO, hV_subW m x hrx⟩ hx₀'
            subst hEq; exact hrNotVx (by simp only [ite_eq_left hxK]; exact hrx)
          · simp only [ite_eq_right hxK] at hrx; exact hrx
        · push Not at hex
          refine Filter.mem_of_superset (hOo.mem_nhds hqO) ?_
          intro r hrO hrC
          obtain ⟨x, hrx⟩ := mem_iUnion.mp hrC
          by_cases hxK : x.1 ∈ K
          · simp only [ite_eq_left hxK] at hrx
            have hmem : r ∈ O ∩ Wexp m x := ⟨hrO, hV_subW m x hrx⟩
            rw [hex x] at hmem; exact hmem
          · simp only [ite_eq_right hxK] at hrx; exact hrx
      let U : Set X := (closure (G N K))ᶜ ∩ ⋂ m ∈ Finset.range N, (C m)ᶜ
      have hUo : IsOpen U :=
        isClosed_closure.isOpen_compl.inter
          (isOpen_biInter_finset fun m _ => (hC_cl m).isOpen_compl)
      have hzU : z ∈ U := ⟨hzNotGN, mem_iInter₂.mpr fun m _ hzm => hzB (mem_iUnion.mpr ⟨m, hzm⟩)⟩
      refine Filter.mem_of_superset (hUo.mem_nhds hzU) ?_
      intro r hrU hrIn
      obtain ⟨m, hrm⟩ := mem_iUnion.mp hrIn
      by_cases hmN : m < N
      · exact (mem_iInter₂.mp hrU.2 m (Finset.mem_range.mpr hmN)) hrm
      · have hNm : N ≤ m := Nat.le_of_not_lt hmN
        obtain ⟨x, hrx⟩ := mem_iUnion.mp hrm
        by_cases hxK : x.1 ∈ K
        · simp only [ite_eq_left hxK] at hrx
          have hrG : r ∈ G N K :=
            hGanti hNm (hGmono m {x.1} K isClosed_singleton hK
              (Set.singleton_subset_iff.mpr hxK) (hV_subG m x hrx))
          exact hrU.1 (subset_closure hrG)
        · simp only [ite_eq_right hxK] at hrx; exact hrx
    exact ⟨hB_cl, hB_open⟩
  -- Step 4: Verify `𝓑` is a CP clopen outer base of `A`.
  let 𝓑 : Set (Set X) := { U : Set X | ∃ K : Set X, IsClosed K ∧ Disjoint K A ∧ U = B K }
  refine ⟨𝓑, ?_, ?_, ?_⟩
  · rintro U ⟨K, hK, hKA, rfl⟩
    exact ⟨hB_clopen K hK hKA, hB_supA K⟩
  · intro W hWo hAW
    have hdisj : Disjoint Wᶜ A := Set.disjoint_left.mpr fun x hxW hxA => hxW (hAW hxA)
    refine ⟨B Wᶜ, ⟨Wᶜ, hWo.isClosed_compl, hdisj, rfl⟩, ?_⟩
    intro y hyB; by_contra hyNotW
    exact Set.disjoint_left.mp (hB_disj Wᶜ hdisj) hyB hyNotW
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hzCl
      by_contra hzNot
      -- If `z ∈ A`, then `𝓖` must be nonempty (else `hzCl` fails), so `z ∈ B K` for any `B K ∈ 𝓖`.
      by_cases hzA : z ∈ A
      · have hGne : 𝓖.Nonempty := by
          by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
          rw [hemp, sUnion_empty, closure_empty] at hzCl; exact hzCl
        obtain ⟨U, hUG⟩ := hGne
        obtain ⟨K, _, _, rfl⟩ := h𝓖 hUG
        exact hzNot ⟨closure (B K), ⟨B K, hUG, rfl⟩, subset_closure (hB_supA K hzA)⟩
      · obtain ⟨k, hzk⟩ := hE_cover z hzA
        let O_m : ℕ → Set X := fun m =>
          if h : ∃ x : E m, z ∈ V m x then V m h.choose else Set.univ
        have hOm_open : ∀ m, IsOpen (O_m m) := fun m => by
          by_cases h : ∃ x : E m, z ∈ V m x
          · simp only [O_m, dite_eq_left h]; exact (hV_clop m h.choose).2
          · simp only [O_m, dite_eq_right h]; exact isOpen_univ
        have hOm_mem : ∀ m, z ∈ O_m m := fun m => by
          by_cases h : ∃ x : E m, z ∈ V m x
          · simp only [O_m, dite_eq_left h]; exact h.choose_spec
          · simp only [O_m, dite_eq_right h]; trivial
        let O : Set X := ⋂ m ∈ Finset.range (k + 1), O_m m
        have hOo : IsOpen O := isOpen_biInter_finset fun m _ => hOm_open m
        have hzO : z ∈ O := mem_iInter₂.mpr fun m _ => hOm_mem m
        obtain ⟨y, hyO, ⟨U, hUG, hyU⟩⟩ := mem_closure_iff.mp hzCl O hOo hzO
        obtain ⟨K, _, _, rfl⟩ := h𝓖 hUG
        have hzNotBK : z ∉ B K := fun hzBK =>
          hzNot ⟨closure (B K), ⟨B K, hUG, rfl⟩, subset_closure hzBK⟩
        have hzIn : z ∈ ⋃ m, ⋃ x : E m, if x.1 ∈ K then V m x else ∅ := by
          by_contra h; exact hzNotBK h
        obtain ⟨m, hzm⟩ := mem_iUnion.mp hzIn
        obtain ⟨x, hzx⟩ := mem_iUnion.mp hzm
        by_cases hxK : x.1 ∈ K
        · simp only [ite_eq_left hxK] at hzx
          have hmk : m ≤ k := by
            by_contra hgt
            exact Set.disjoint_left.mp (hV_disjE m x k (Nat.lt_of_not_ge hgt)) hzx hzk
          have hex : ∃ x' : E m, z ∈ V m x' := ⟨x, hzx⟩
          have hchoose_eq : hex.choose = x := by
            obtain ⟨O', _, hzO', hO'uniq⟩ := hWexp_disc m z
            exact hO'uniq hex.choose x ⟨z, hzO', hV_subW m _ hex.choose_spec⟩
              ⟨z, hzO', hV_subW m _ hzx⟩
          have hyOm : y ∈ O_m m := mem_iInter₂.mp hyO m (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
          simp only [O_m, dite_eq_left hex, hchoose_eq] at hyOm
          exact hyU (mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨x, by simp only [ite_eq_left hxK]; exact hyOm⟩⟩)
        · simp only [ite_eq_right hxK] at hzx; exact hzx
    · rintro z ⟨_, ⟨U, hUG, rfl⟩, hzU⟩
      exact closure_mono (Set.subset_sUnion_of_mem hUG) hzU

/-- **Generalized Gruenhage Outer-Base Theorem (σ-Discrete Complement Form)**:
If `X` is stratifiable and `A ⊆ X` is closed with `X \ A` a countable union of discrete subspaces,
then `A` has a single-layer closure-preserving clopen outer base in `X`. -/
theorem hasCPClopenOuterBase_of_sigma_discrete_compl {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) {A : Set X} (hA : IsClosed A)
    {D : ℕ → Set X}
    (hD_disc : ∀ n, ∀ x ∈ D n, ∃ U : Set X, IsOpen U ∧ U ∩ D n = {x})
    (hD_eq : (⋃ n, D n) = Aᶜ) :
    ∃ 𝓑 : Set (Set X),
      (∀ B ∈ 𝓑, IsClopen B ∧ A ⊆ B) ∧
      (∀ W : Set X, IsOpen W → A ⊆ W → ∃ B ∈ 𝓑, B ⊆ W) ∧
      MSpace.ClosurePreserving 𝓑 := by
  obtain ⟨F, hF_disc, hF_eq⟩ :=
    sigma_closedDiscrete_in_open_of_sigma_discrete hS hA.isOpen_compl hD_disc hD_eq
  exact hasCPClopenOuterBase_of_sigma_closedDiscrete_compl hS hA hF_disc hF_eq

/-- Intersecting a closure-preserving family `𝓑` of **clopen** sets with any fixed open set `D`
preserves the closure-preserving property! -/
theorem closurePreserving_inter_open_of_clopen {X : Type*} [TopologicalSpace X]
    {D : Set X} {𝓑 : Set (Set X)}
    (hBclop : ∀ B ∈ 𝓑, IsClopen B) (hBcp : MSpace.ClosurePreserving 𝓑) :
    MSpace.ClosurePreserving { W : Set X | ∃ B ∈ 𝓑, W = D ∩ B } := by
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · intro z hzCl
    let 𝓗 : Set (Set X) := { B ∈ 𝓑 | D ∩ B ∈ 𝓖 }
    have h1 : ⋃₀ 𝓖 ⊆ ⋃₀ 𝓗 := by
      rintro y ⟨W, hWG, hyW⟩
      obtain ⟨B, hB, rfl⟩ := h𝓖 hWG
      exact ⟨B, ⟨hB, hWG⟩, hyW.2⟩
    have hzH : z ∈ closure (⋃₀ 𝓗) := closure_mono h1 hzCl
    rw [hBcp 𝓗 (fun _ h => h.1)] at hzH
    obtain ⟨_, ⟨B₀, ⟨hB₀, hDB₀G⟩, rfl⟩, hzB₀cl⟩ := hzH
    rw [(hBclop B₀ hB₀).1.closure_eq] at hzB₀cl
    refine ⟨closure (D ∩ B₀), ⟨D ∩ B₀, hDB₀G, rfl⟩, ?_⟩
    rw [mem_closure_iff]
    intro O hOo hzO
    have hOB₀o : IsOpen (O ∩ B₀) := hOo.inter (hBclop B₀ hB₀).2
    have hzDcl : z ∈ closure D :=
      closure_mono (by rintro y ⟨W, hWG, hyW⟩; obtain ⟨B, _, rfl⟩ := h𝓖 hWG; exact hyW.1) hzCl
    obtain ⟨q, ⟨hqO, hqB₀⟩, hqD⟩ := mem_closure_iff.mp hzDcl (O ∩ B₀) hOB₀o ⟨hzO, hzB₀cl⟩
    exact ⟨q, hqO, hqD, hqB₀⟩
  · rintro z ⟨_, ⟨W, hWG, rfl⟩, hzW⟩
    exact closure_mono (Set.subset_sUnion_of_mem hWG) hzW

/-- **Local Pointwise Corollary**:
In any stratifiable space `X`, if a point `x₀` has an open neighborhood `U` such that `U \ {x₀}`
is σ-discrete (in particular, countable), then `Defs.D_0001.HasCPOuterBase x₀`. -/
theorem hasCPOuterBase_of_sigma_discrete_punctured_nhd {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) {x₀ : X} {U : Set X} (hUo : IsOpen U) (hx₀U : x₀ ∈ U)
    {D : ℕ → Set X}
    (hD_disc : ∀ n, ∀ x ∈ D n, ∃ V : Set X, IsOpen V ∧ V ∩ D n = {x})
    (hD_eq : (⋃ n, D n) = U \ {x₀}) :
    Defs.D_0001.HasCPOuterBase x₀ := by
  have : T1Space X := hS.1
  have : NormalSpace X := normalSpace_of_isStratifiable hS
  -- Shrink `U` to an open neighborhood `U₁` of `x₀` with `closure U₁ ⊆ U`.
  obtain ⟨U₁, _, hU₁o, _, hx₀U₁, hUcV, hdisj₁⟩ :=
    normal_cl_separation isClosed_singleton hUo.isClosed_compl
      (Set.disjoint_singleton_left.mpr fun h => h hx₀U)
  have hclU₁_sub : closure U₁ ⊆ U := fun y hyCl => by
    by_contra hyNot; exact Set.disjoint_left.mp hdisj₁ hyCl (subset_closure (hUcV hyNot))
  -- Apply `hasCPClopenOuterBase_of_sigma_discrete_compl` to `A := Uᶜ ∪ {x₀}` (complement `U \ {x₀}`).
  let A : Set X := Uᶜ ∪ {x₀}
  have hAcl : IsClosed A := hUo.isClosed_compl.union isClosed_singleton
  have hAc_eq : Aᶜ = U \ {x₀} := by ext y; simp [A, not_or, and_comm]
  obtain ⟨𝓑, hB_prop, hB_base, hB_cp⟩ :=
    hasCPClopenOuterBase_of_sigma_discrete_compl hS hAcl hD_disc (hD_eq.trans hAc_eq.symm)
  let 𝓤 : Set (Set X) := { W : Set X | ∃ B ∈ 𝓑, W = U₁ ∩ B }
  refine ⟨𝓤, ?_, ?_, ?_⟩
  · rintro W ⟨B, hB, rfl⟩
    exact ⟨hU₁o.inter (hB_prop B hB).1.2, hx₀U₁ (mem_singleton x₀), (hB_prop B hB).2 (Or.inr rfl)⟩
  · intro W hWo hx₀W
    let W' : Set X := W ∪ (closure U₁)ᶜ
    have hW'o : IsOpen W' := hWo.union isClosed_closure.isOpen_compl
    have hAW' : A ⊆ W' := by
      rintro y (hyNotU | rfl)
      · exact Or.inr fun hyCl => hyNotU (hclU₁_sub hyCl)
      · exact Or.inl hx₀W
    obtain ⟨B, hB, hBW'⟩ := hB_base W' hW'o hAW'
    refine ⟨U₁ ∩ B, ⟨B, hB, rfl⟩, ?_⟩
    rintro y ⟨hyU₁, hyB⟩
    rcases hBW' hyB with hyW | hyNotCl
    · exact hyW
    · exact (hyNotCl (subset_closure hyU₁)).elim
  · exact closurePreserving_inter_open_of_clopen (fun B hB => (hB_prop B hB).1) hB_cp

/-! ## Part 3: `M₁` Theorem for Second-Countable Closed Core + σ-Discrete Complement -/

/-- **Structural `M₁` Theorem (Second-Countable / Compact Core + σ-Discrete Complement)**:
If `X` is a stratifiable space and `A ⊆ X` is a closed **second-countable** subspace
(in particular, any compact subset of `X`) whose complement `X \ A` is σ-discrete, then
**`MSpace.IsM1 X`**. -/
theorem isM1_of_stratifiable_secondCountable_closed_sigma_discrete_compl {X : Type*}
    [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) {A : Set X} (hA : IsClosed A)
    [SecondCountableTopology A]
    {D : ℕ → Set X}
    (hD_disc : ∀ n, ∀ x ∈ D n, ∃ U : Set X, IsOpen U ∧ U ∩ D n = {x})
    (hD_eq : (⋃ n, D n) = Aᶜ) :
    MSpace.IsM1 X := by
  classical
  have : T1Space X := hS.1
  have : NormalSpace X := normalSpace_of_isStratifiable hS
  have : T3Space X := inferInstance
  -- Part A: Obtain a CP clopen outer base `𝓑_A` of `A` in `X`.
  obtain ⟨F, hF_disc, hF_eq⟩ :=
    sigma_closedDiscrete_in_open_of_sigma_discrete hS hA.isOpen_compl hD_disc hD_eq
  obtain ⟨𝓑_A, hBA_prop, hBA_base, hBA_cp⟩ :=
    hasCPClopenOuterBase_of_sigma_closedDiscrete_compl hS hA hF_disc hF_eq
  -- Part B: Obtain a countable open base `𝓤_A` of `A` and for each pair `(U₁, U₂)` with
  -- `closure_A U₁ ⊆ U₂`, choose an open set `E(U₁, U₂)` in `X` separating `closure_A U₁` from `A \ U₂`
  -- with `closure E(U₁, U₂) ∩ (A \ U₂) = ∅`.
  obtain ⟨𝓤_A, hUA_cnt, _, hUA_basis⟩ := exists_countable_basis A
  let P := { p : 𝓤_A × 𝓤_A // closure p.1.1 ⊆ p.2.1 }
  have : Countable 𝓤_A := hUA_cnt.to_subtype
  have : Countable P := inferInstance
  have hE_ex : ∀ p : P, ∃ E : Set X, IsOpen E ∧
      Subtype.val '' closure p.1.1.1 ⊆ E ∧
      Disjoint (closure E) (Subtype.val '' (p.1.2.1)ᶜ) := by
    intro p
    have hK₁ : IsClosed (Subtype.val '' closure p.1.1.1) :=
      hA.isClosedMap_subtype_val _ isClosed_closure
    have hK₂ : IsClosed (Subtype.val '' (p.1.2.1)ᶜ) :=
      hA.isClosedMap_subtype_val _ (hUA_basis.isOpen p.1.2.2).isClosed_compl
    have hdisj : Disjoint (Subtype.val '' closure p.1.1.1) (Subtype.val '' (p.1.2.1)ᶜ) := by
      rw [Set.disjoint_left]
      rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, hEq⟩
      have : y₁ = y₂ := Subtype.ext hEq.symm
      subst this; exact hy₂ (p.2 hy₁)
    obtain ⟨E, _, hEo, _, hK₁E, hK₂V, hdisjCl⟩ := normal_cl_separation hK₁ hK₂ hdisj
    exact ⟨E, hEo, hK₁E, hdisjCl.mono_right (hK₂V.trans subset_closure)⟩
  choose E hEo hE_sub hE_disj using hE_ex
  -- Index `P` by `ℕ` (or handle empty `P` cleanly).
  let 𝓕_A : P → Set (Set X) := fun p => { W : Set X | ∃ B ∈ 𝓑_A, W = E p ∩ B }
  have hFA_open : ∀ p, ∀ W ∈ 𝓕_A p, IsOpen W := by
    rintro p W ⟨B, hB, rfl⟩; exact (hEo p).inter (hBA_prop B hB).1.2
  have hFA_cp : ∀ p, MSpace.ClosurePreserving (𝓕_A p) := fun p =>
    closurePreserving_inter_open_of_clopen (fun B hB => (hBA_prop B hB).1) hBA_cp
  -- Part C: For `X \ A = ⋃ n, F n`, expand each closed discrete `F n` to a discrete open family
  -- `Wexp n d` with `closure (Wexp n d) ⊆ Aᶜ`, and give every `d ∈ F n` a CP open outer base
  -- inside `Wexp n d` (using `hasCPClopenOuterBase_of_sigma_closedDiscrete_compl`? Even simpler:
  -- `A ∪ {d}`? No: `{d}` has `Aᶜ \ {d}`... even simpler: apply `hasCPClopenOuterBase_of_sigma_closedDiscrete_compl`
  -- to `A ∪ {d}` and intersect with `Wexp n d`!).
  choose Wexp0 hWexp0_open hWexp0_disc using fun n =>
    stratifiable_discrete_open_expansion hS (hF_disc n)
  have hWexp_ex : ∀ (n : ℕ) (d : F n), ∃ W : Set X, IsOpen W ∧ d.1 ∈ W ∧
      W ⊆ Wexp0 n d ∧ Disjoint (closure W) A := by
    intro n d
    have hdAc : d.1 ∈ Aᶜ := by rw [← hF_eq]; exact mem_iUnion.mpr ⟨n, d.2⟩
    obtain ⟨U, _, hUo, _, hdU, hAV, hdisjCl⟩ :=
      normal_cl_separation isClosed_singleton hA (Set.disjoint_singleton_left.mpr hdAc)
    refine ⟨U ∩ Wexp0 n d, hUo.inter (hWexp0_open n d).1, ⟨hdU (mem_singleton d.1), (hWexp0_open n d).2⟩,
      inter_subset_right, hdisjCl.mono (closure_mono inter_subset_left) (hAV.trans subset_closure)⟩
  choose Wexp hWexp_open hWexp_mem hWexp_sub hWexp_disjA using hWexp_ex
  have hWexp_disc : ∀ n z, ∃ O : Set X, IsOpen O ∧ z ∈ O ∧
      ∀ d₁ d₂ : F n, (O ∩ Wexp n d₁).Nonempty → (O ∩ Wexp n d₂).Nonempty → d₁ = d₂ := by
    intro n z
    obtain ⟨O, hOo, hzO, hOuniq⟩ := hWexp0_disc n z
    exact ⟨O, hOo, hzO, fun d₁ d₂ ⟨y₁, hy₁O, hy₁W⟩ ⟨y₂, hy₂O, hy₂W⟩ =>
      hOuniq d₁ d₂ ⟨y₁, hy₁O, hWexp_sub n d₁ hy₁W⟩ ⟨y₂, hy₂O, hWexp_sub n d₂ hy₂W⟩⟩
  -- For each `n` and `d : F n`, `A ∪ {d.1}` is closed with complement `Aᶜ \ {d.1} = ⋃ k, F k \ {d.1}`,
  -- so `A ∪ {d.1}` has a CP clopen outer base `𝓑_d`, and intersecting with `Wexp n d` gives a CP
  -- open local base of `d.1` inside `Wexp n d`!
  have hUd_ex : ∀ (n : ℕ) (d : F n),
      ∃ 𝓤 : Set (Set X),
        (∀ V ∈ 𝓤, IsOpen V ∧ d.1 ∈ V ∧ V ⊆ Wexp n d) ∧
        (∀ W : Set X, IsOpen W → d.1 ∈ W → ∃ V ∈ 𝓤, V ⊆ W) ∧
        MSpace.ClosurePreserving 𝓤 := by
    intro n d
    let Ad : Set X := A ∪ {d.1}
    have hAd_cl : IsClosed Ad := hA.union isClosed_singleton
    let Fd : ℕ → Set X := fun k => F k \ {d.1}
    have hFd_disc : ∀ k (S : Set X), S ⊆ Fd k → IsClosed S := fun k S hSsub =>
      hF_disc k S (hSsub.trans sdiff_subset)
    have hFd_eq : (⋃ k, Fd k) = Adᶜ := by
      ext y; simp only [Fd, Ad, mem_iUnion, mem_sdiff, mem_singleton_iff, mem_compl_iff, mem_union, not_or]
      constructor
      · rintro ⟨k, hyk, hyne⟩
        exact ⟨by rw [← mem_compl_iff, ← hF_eq]; exact mem_iUnion.mpr ⟨k, hyk⟩, hyne⟩
      · rintro ⟨hyAc, hyne⟩
        obtain ⟨k, hyk⟩ := mem_iUnion.mp (by rw [hF_eq]; exact hyAc)
        exact ⟨k, hyk, hyne⟩
    obtain ⟨𝓑d, hBd_prop, hBd_base, hBd_cp⟩ :=
      hasCPClopenOuterBase_of_sigma_closedDiscrete_compl hS hAd_cl hFd_disc hFd_eq
    refine ⟨{ V : Set X | ∃ B ∈ 𝓑d, V = Wexp n d ∩ B }, ?_, ?_, ?_⟩
    · rintro V ⟨B, hB, rfl⟩
      exact ⟨(hWexp_open n d).inter (hBd_prop B hB).1.2,
        ⟨hWexp_mem n d, (hBd_prop B hB).2 (Or.inr rfl)⟩, inter_subset_left⟩
    · intro W hWo hdW
      let W' : Set X := W ∪ (closure (Wexp n d))ᶜ
      have hW'o : IsOpen W' := hWo.union isClosed_closure.isOpen_compl
      have hAdW' : Ad ⊆ W' := by
        rintro y (hyA | rfl)
        · exact Or.inr fun hyCl => Set.disjoint_left.mp (hWexp_disjA n d) hyCl hyA
        · exact Or.inl hdW
      obtain ⟨B, hB, hBW'⟩ := hBd_base W' hW'o hAdW'
      refine ⟨Wexp n d ∩ B, ⟨B, hB, rfl⟩, ?_⟩
      rintro y ⟨hyWexp, hyB⟩
      rcases hBW' hyB with hyW | hyNotCl
      · exact hyW
      · exact (hyNotCl (subset_closure hyWexp)).elim
    · exact closurePreserving_inter_open_of_clopen
        (fun B hB => (hBd_prop B hB).1) hBd_cp
  choose 𝓤d hUd_prop hUd_base hUd_cp using hUd_ex
  let 𝓒 : ℕ → Set (Set X) := fun n => { V : Set X | ∃ d : F n, V ∈ 𝓤d n d }
  have hC_open : ∀ n, ∀ V ∈ 𝓒 n, IsOpen V := by
    rintro n V ⟨d, hVd⟩; exact (hUd_prop n d V hVd).1
  have hC_cp : ∀ n, MSpace.ClosurePreserving (𝓒 n) := by
    intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      obtain ⟨O, hOo, hzO, hOuniq⟩ := hWexp_disc n z
      obtain ⟨y₀, hy₀O, ⟨B₀, hB₀G, hy₀B₀⟩⟩ := mem_closure_iff.mp hz O hOo hzO
      obtain ⟨d₀, hB₀d₀⟩ := h𝓖 hB₀G
      have hOd₀ : (O ∩ Wexp n d₀).Nonempty := ⟨y₀, hy₀O, (hUd_prop n d₀ B₀ hB₀d₀).2.2 hy₀B₀⟩
      let 𝓖₀ : Set (Set X) := { B ∈ 𝓖 | B ∈ 𝓤d n d₀ }
      have hz_cl0 : z ∈ closure (⋃₀ 𝓖₀) := by
        rw [mem_closure_iff]; intro W hWo hzW
        obtain ⟨q, hqOW, ⟨B, hBG, hqB⟩⟩ :=
          mem_closure_iff.mp hz (O ∩ W) (hOo.inter hWo) ⟨hzO, hzW⟩
        obtain ⟨d, hBd⟩ := h𝓖 hBG
        have hd_eq : d = d₀ := hOuniq d d₀ ⟨q, hqOW.1, (hUd_prop n d B hBd).2.2 hqB⟩ hOd₀
        subst hd_eq
        exact ⟨q, hqOW.2, ⟨B, ⟨hBG, hBd⟩, hqB⟩⟩
      rw [hUd_cp n d₀ 𝓖₀ (fun _ h => h.2)] at hz_cl0
      obtain ⟨_, ⟨B, hBG₀, rfl⟩, hzB⟩ := hz_cl0
      exact ⟨closure B, ⟨B, hBG₀.1, rfl⟩, hzB⟩
    · rintro z ⟨_, ⟨B, hBG, rfl⟩, hzB⟩
      exact closure_mono (Set.subset_sUnion_of_mem hBG) hzB
  -- Part D: Combine `𝓕_A` (indexed by countable `P`) and `𝓒` (indexed by `ℕ`) into a σ-CP open base!
  let 𝓛 : ℕ → Set (Set X) := fun n =>
    if n % 2 = 0 then 𝓒 (n / 2)
    else if hP : Nonempty P then
      let f := (exists_surjective_nat P).choose
      𝓕_A (f (n / 2))
    else ∅
  have hL_cp : ∀ n, MSpace.ClosurePreserving (𝓛 n) := fun n => by
    by_cases he : n % 2 = 0
    · simp only [𝓛, ite_eq_left he]; exact hC_cp (n / 2)
    · by_cases hP : Nonempty P
      · simp only [𝓛, ite_eq_right he, dite_eq_left hP]; exact hFA_cp _
      · simp only [𝓛, ite_eq_right he, dite_eq_right hP]
        intro 𝓖 h𝓖; have hEq : 𝓖 = ∅ := Set.subset_empty_iff.mp h𝓖; subst hEq; simp
  refine ⟨inferInstance, ⋃ n, 𝓛 n, ?_, ⟨𝓛, hL_cp, rfl⟩⟩
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro W hW
    obtain ⟨n, hWn⟩ := mem_iUnion.mp hW
    by_cases he : n % 2 = 0
    · simp only [𝓛, ite_eq_left he] at hWn; exact hC_open (n / 2) W hWn
    · by_cases hP : Nonempty P
      · simp only [𝓛, ite_eq_right he, dite_eq_left hP] at hWn; exact hFA_open _ W hWn
      · simp only [𝓛, ite_eq_right he, dite_eq_right hP] at hWn; exact hWn.elim
  · intro x W hxW hWo
    by_cases hxA : x ∈ A
    · -- Use `𝓕_A`: pick `U₂ ∈ 𝓤_A` with `x ∈ U₂ ⊆ W ∩ A`, then `U₁ ∈ 𝓤_A` with `x ∈ U₁ ⊆ closure_A U₁ ⊆ U₂`.
      let xA : A := ⟨x, hxA⟩
      have hWAo : IsOpen ((Subtype.val : A → X) ⁻¹' W) := hWo.preimage continuous_subtype_val
      obtain ⟨U₂, hU₂mem, hxU₂, hU₂W⟩ :=
        hUA_basis.exists_subset_of_mem_open (show xA ∈ (Subtype.val : A → X) ⁻¹' W from hxW) hWAo
      obtain ⟨t, ht, htc, htU₂⟩ :=
        exists_mem_nhds_isClosed_subset ((hUA_basis.isOpen hU₂mem).mem_nhds hxU₂)
      obtain ⟨U₁, hU₁mem, hxU₁, hU₁t⟩ :=
        hUA_basis.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.mpr ht) isOpen_interior
      have hclU₁_U₂ : closure U₁ ⊆ U₂ := (closure_minimal (hU₁t.trans interior_subset) htc).trans htU₂
      let p : P := ⟨(⟨U₁, hU₁mem⟩, ⟨U₂, hU₂mem⟩), hclU₁_U₂⟩
      have hPne : Nonempty P := ⟨p⟩
      obtain ⟨k, hk⟩ := (exists_surjective_nat P).choose_spec p
      let W' : Set X := W ∪ (closure (E p))ᶜ
      have hW'o : IsOpen W' := hWo.union isClosed_closure.isOpen_compl
      have hAW' : A ⊆ W' := by
        intro y hyA
        by_cases hyU₂ : (⟨y, hyA⟩ : A) ∈ U₂
        · exact Or.inl (hU₂W hyU₂)
        · exact Or.inr fun hyCl =>
            Set.disjoint_left.mp (hE_disj p) hyCl ⟨⟨y, hyA⟩, hyU₂, rfl⟩
      obtain ⟨B, hB, hBW'⟩ := hBA_base W' hW'o hAW'
      refine ⟨E p ∩ B, ?_, ⟨hE_sub p ⟨xA, subset_closure hxU₁, rfl⟩, (hBA_prop B hB).2 hxA⟩, ?_⟩
      · refine mem_iUnion.mpr ⟨2 * k + 1, ?_⟩
        have hodd : ¬ (2 * k + 1) % 2 = 0 := by omega
        have hdiv : (2 * k + 1) / 2 = k := by omega
        simp only [𝓛, ite_eq_right hodd, dite_eq_left hPne, hdiv, hk]
        exact ⟨B, hB, rfl⟩
      · rintro y ⟨hyE, hyB⟩
        rcases hBW' hyB with hyW | hyNotCl
        · exact hyW
        · exact (hyNotCl (subset_closure hyE)).elim
    · -- `x ∈ Aᶜ = ⋃ n, F n`: use `𝓒 n`!
      obtain ⟨n, hxn⟩ := mem_iUnion.mp (by rw [hF_eq]; exact hxA)
      obtain ⟨V, hVmem, hVW⟩ := hUd_base n ⟨x, hxn⟩ W hWo hxW
      refine ⟨V, ?_, (hUd_prop n ⟨x, hxn⟩ V hVmem).2.1, hVW⟩
      refine mem_iUnion.mpr ⟨2 * n, ?_⟩
      have heven : (2 * n) % 2 = 0 := by omega
      have hdiv : (2 * n) / 2 = n := by omega
      simp only [𝓛, ite_eq_left heven, hdiv]
      exact ⟨⟨x, hxn⟩, hVmem⟩

end Research.GruenhageSigmaDiscreteCompl
