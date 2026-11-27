import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Basic.Countable.Defs
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Basic
import Defs.D_0001
import Targets.Defs

/-!
# Gruenhage's Theorem (1978): Every σ-Discrete (and Every Countable) Stratifiable Space is `M₁`

We prove **Gruenhage (1978)** (*"Stratifiable σ-discrete spaces are M₁"*, Proc. Amer. Math. Soc. 72
(1978), 189–190) completely in ZFC:

1. `hasCPOuterBase_of_stratifiable_sigma_closedDiscrete`:
   in any stratifiable space `X` that is a countable union `⋃ n, F n` of closed discrete subsets,
   **every point** `x₀ : X` has a single-layer closure-preserving **clopen** outer base
   (`Defs.D_0001.HasCPOuterBase x₀`).
2. `isM1_of_stratifiable_sigma_closedDiscrete`:
   every σ-closed-discrete stratifiable space is an **`M₁`-space** (`MSpace.IsM1 X`).
3. `isM1_of_stratifiable_sigma_discrete` (**Gruenhage 1978**):
   every σ-discrete stratifiable space (a countable union `⋃ n, D n` of discrete subspaces,
   not assumed closed) is an **`M₁`-space**.
4. `isM1_of_countable_stratifiable`:
   every **countable** stratifiable space is an **`M₁`-space** (in particular, any counterexample
   to `Tinf` / `L_0020` / `L_0030` / `L_0031` must be uncountable and not σ-discrete).
-/

namespace Research.Gruenhage1978

open Set Topology

/-! ## Part 1: Decreasing Stratification, Monotone Normality, Normality, and Discrete Open Expansion -/

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
  · intro n H hH
    exact isOpen_biInter_finset fun k _ => hG₀o k H hH
  · intro n H hH x hx
    exact mem_iInter₂.mpr fun k _ => hG₀sub k H hH hx
  · intro H hH
    apply Subset.antisymm
    · have hsub_iInter : (⋂ n, closure (G n H)) ⊆ ⋂ n, closure (G₀ n H) := by
        intro x hx
        rw [mem_iInter] at hx ⊢
        intro n
        have hsub : G n H ⊆ G₀ n H := fun y hy =>
          mem_iInter₂.mp hy n (Finset.mem_range.mpr (Nat.lt_succ_self n))
        exact closure_mono hsub (hx n)
      exact hsub_iInter.trans (hG₀inter H hH).subset
    · intro x hx
      rw [mem_iInter]
      intro n
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
    intro m n F hmn
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hGdec _ F).trans ih
  let H : Set X → Set X → Set X := fun A B => ⋃ n, (G n A \ closure (G n B))
  refine ⟨H, ?_, ?_, ?_⟩
  · intro A B hA _
    exact isOpen_iUnion fun n => (hGo n A hA).sdiff isClosed_closure
  · intro A B hA hB hdisj x hxA
    have hxNotB : x ∉ B := Set.disjoint_left.mp hdisj hxA
    rw [← hGinter B hB, mem_iInter] at hxNotB
    push Not at hxNotB
    obtain ⟨n, hxn⟩ := hxNotB
    exact mem_iUnion.mpr ⟨n, hGsub n A hA hxA, hxn⟩
  · intro A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ h1 h2
    rw [Set.disjoint_left]
    intro x hx1 hx2
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

/-! ## Part 2: Strong Zero-Dimensionality (`Ind X = 0`) for σ-Closed-Discrete Normal Spaces -/

private theorem normal_cl_separation {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint (closure U) (closure V) := by
  obtain ⟨U₁, V₁, hU₁o, hV₁o, hAU₁, hBV₁, hdisj₁⟩ := normal_separation hA hB hdisj
  have hclU₁_disj_B : Disjoint (closure U₁) B := by
    rw [Set.disjoint_left]
    intro x hxCl hxB
    obtain ⟨y, hyV₁, hyU₁⟩ := mem_closure_iff.mp hxCl V₁ hV₁o (hBV₁ hxB)
    exact Set.disjoint_left.mp hdisj₁ hyU₁ hyV₁
  obtain ⟨U₂, V₂, hU₂o, hV₂o, hclU₁_U₂, hBV₂, hdisj₂⟩ :=
    normal_separation isClosed_closure hB hclU₁_disj_B
  refine ⟨U₁, V₂, hU₁o, hV₂o, hAU₁, hBV₂, ?_⟩
  rw [Set.disjoint_left]
  intro x hxCl₁ hxCl₂
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
  rw [Set.disjoint_left]
  intro x hxW hxB
  exact Set.disjoint_left.mp hdisjWW' hxW (mem_iUnion.mpr ⟨0, hB_st0 hxB⟩)

/-! ## Part 3: Gruenhage's Single-Layer CP Clopen Outer Base at Every Point -/

/-- **Gruenhage (1978), Key Pointwise Theorem**:
In any σ-closed-discrete stratifiable space `X = ⋃ n, F n`, **every point** `x₀ : X` has a
single-layer closure-preserving open (in fact clopen) outer base `Defs.D_0001.HasCPOuterBase x₀`. -/
theorem hasCPOuterBase_of_stratifiable_sigma_closedDiscrete {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) {F : ℕ → Set X}
    (hF_disc : ∀ n (S : Set X), S ⊆ F n → IsClosed S)
    (hF_cover : (⋃ n, F n) = Set.univ)
    (x₀ : X) :
    Defs.D_0001.HasCPOuterBase x₀ := by
  classical
  have : T1Space X := hS.1
  have : NormalSpace X := normalSpace_of_isStratifiable hS
  have hInd0 := stronglyZeroDim_of_normal_sigma_closedDiscrete hF_disc hF_cover
  obtain ⟨G, hGo, hGsub, hGinter, hGmono, hGdec⟩ := stratifiable_decreasing hS
  have hGanti : ∀ {m n} {K}, m ≤ n → G n K ⊆ G m K := by
    intro m n K hmn; induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hGdec _ K).trans ih
  -- Step 1: Partition `X` into pairwise disjoint closed discrete layers `E m` with `E 0 = {x₀}`.
  let E : ℕ → Set X := fun m =>
    match m with
    | 0 => {x₀}
    | n + 1 => F n \ ({x₀} ∪ ⋃ j < n, F j)
  have hE_disc : ∀ m (S : Set X), S ⊆ E m → IsClosed S := by
    intro m S hSE
    cases m with
    | zero =>
      by_cases hne : x₀ ∈ S
      · have hEq : S = {x₀} := Subset.antisymm hSE (Set.singleton_subset_iff.mpr hne)
        rw [hEq]; exact isClosed_singleton
      · have hEq : S = ∅ := Set.eq_empty_of_forall_notMem fun y hy => hne (hSE hy ▸ hy)
        rw [hEq]; exact isClosed_empty
    | succ n => exact hF_disc n S (hSE.trans sdiff_subset)
  have hE_cover : ∀ x : X, ∃ m, x ∈ E m := by
    intro x
    by_cases hx0 : x = x₀
    · exact ⟨0, hx0⟩
    · have hex : ∃ n, x ∈ F n := mem_iUnion.mp (by rw [hF_cover]; trivial)
      let n := Nat.find hex
      refine ⟨n + 1, Nat.find_spec hex, ?_⟩
      rintro (rfl | hlt)
      · exact hx0 rfl
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hlt
        exact Nat.find_min hex hj hxj
  -- Step 2: Discrete open expansion of each `E m`, then shrink to clopen `V m x` avoiding `⋃ j < m, E j`
  -- and contained in `G m {x}`.
  choose Wexp hWexp_open hWexp_disc using fun m =>
    stratifiable_discrete_open_expansion hS (hE_disc m)
  have hV_ex : ∀ (m : ℕ) (x : E m),
      ∃ V : Set X, IsClopen V ∧ x.1 ∈ V ∧ V ⊆ Wexp m x ∧ V ⊆ G m {x.1} ∧
        ∀ j < m, Disjoint V (E j) := by
    intro m x
    let prev : Set X := ⋃ j ∈ Finset.range m, E j
    have hprev_cl : IsClosed prev := isClosed_biUnion_finset fun j _ => hE_disc j (E j) Subset.rfl
    have hx_not_prev : x.1 ∉ prev := by
      intro hxP
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxP
      have hjm : j < m := Finset.mem_range.mp hj
      cases m with
      | zero => omega
      | succ n =>
        cases j with
        | zero => exact x.2.2 (Or.inl hxj)
        | succ j' =>
          have hj'n : j' < n := by omega
          exact x.2.2 (Or.inr (mem_iUnion₂.mpr ⟨j', hj'n, hxj.1⟩))
    let U : Set X := Wexp m x ∩ G m {x.1} ∩ prevᶜ
    have hUo : IsOpen U :=
      ((hWexp_open m x).1.inter (hGo m {x.1} isClosed_singleton)).inter hprev_cl.isOpen_compl
    have hxU : x.1 ∈ U :=
      ⟨⟨(hWexp_open m x).2, hGsub m {x.1} isClosed_singleton (mem_singleton x.1)⟩, hx_not_prev⟩
    obtain ⟨V, hVclop, hxV, hVdisj⟩ :=
      hInd0 {x.1} Uᶜ isClosed_singleton hUo.isClosed_compl
        (Set.disjoint_singleton_left.mpr fun h => h hxU)
    have hVU : V ⊆ U := fun y hyV => by
      by_contra hyNot; exact Set.disjoint_left.mp hVdisj hyV hyNot
    refine ⟨V, hVclop, hxV (mem_singleton x.1),
      fun y hy => (hVU hy).1.1, fun y hy => (hVU hy).1.2, fun j hjm => ?_⟩
    rw [Set.disjoint_left]
    intro y hyV hyEj
    exact (hVU hyV).2 (mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjm, hyEj⟩)
  choose V hV_clop hV_mem hV_subW hV_subG hV_disj using hV_ex
  -- Step 3: Define the Gruenhage clopen family `𝓑 = { B K | K closed, x₀ ∉ K }`.
  let B : Set X → Set X := fun K => (⋃ m, ⋃ x : E m, if x.1 ∈ K then V m x else ∅)ᶜ
  have hB_mem : ∀ K, x₀ ∉ K → x₀ ∈ B K := by
    intro K hx0K hxIn
    obtain ⟨m, hxIn⟩ := mem_iUnion.mp hxIn
    obtain ⟨x, hxV⟩ := mem_iUnion.mp hxIn
    by_cases hxK : x.1 ∈ K
    · simp only [ite_eq_left hxK] at hxV
      cases m with
      | zero =>
        have hEq : x.1 = x₀ := x.2
        exact hx0K (hEq ▸ hxK)
      | succ n =>
        exact Set.disjoint_left.mp (hV_disj (n + 1) x 0 (Nat.zero_lt_succ n)) hxV (mem_singleton x₀)
    · simp only [ite_eq_right hxK] at hxV
      exact hxV
  have hB_disj : ∀ K, Disjoint (B K) K := by
    intro K
    rw [Set.disjoint_left]
    intro y hyB hyK
    obtain ⟨m, hym⟩ := hE_cover y
    apply hyB
    refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨⟨y, hym⟩, ?_⟩⟩
    simp only [ite_eq_left hyK]
    exact hV_mem m ⟨y, hym⟩
  have hB_clopen : ∀ K, IsClosed K → IsClopen (B K) := by
    intro K hK
    have hB_cl : IsClosed (B K) := by
      refine IsOpen.isClosed_compl (isOpen_iUnion fun m => isOpen_iUnion fun x => ?_)
      by_cases hxK : x.1 ∈ K
      · simp only [ite_eq_left hxK]; exact (hV_clop m x).2
      · simp only [ite_eq_right hxK]; exact isOpen_empty
    have hB_open : IsOpen (B K) := by
      rw [isOpen_iff_mem_nhds]
      intro z hzB
      have hzNotK : z ∉ K := Set.disjoint_left.mp (hB_disj K) hzB
      rw [← hGinter K hK, mem_iInter] at hzNotK
      push Not at hzNotK
      obtain ⟨N, hzNotGN⟩ := hzNotK
      -- Tail `m ≥ N` is contained in `G N K`, hence disjoint from `(closure (G N K))ᶜ`.
      -- Prefix `m < N`: for each `m < N`, `C m := ⋃ x : E m, if x.1 ∈ K then V m x else ∅` is closed
      -- because `V m x` is closed and `{Wexp m x}` is discrete.
      let C : ℕ → Set X := fun m => ⋃ x : E m, if x.1 ∈ K then V m x else ∅
      have hC_cl : ∀ m, IsClosed (C m) := fun m => by
        rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
        intro q hqNotC
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
            subst hEq
            exact hrNotVx (by simp only [ite_eq_left hxK]; exact hrx)
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
  -- Step 4: Verify that `𝓑 := { U | ∃ K, IsClosed K ∧ x₀ ∉ K ∧ U = B K }` is a CP open outer base at `x₀`.
  let 𝓑 : Set (Set X) := { U : Set X | ∃ K : Set X, IsClosed K ∧ x₀ ∉ K ∧ U = B K }
  refine ⟨𝓑, ?_, ?_, ?_⟩
  · rintro U ⟨K, hK, hx0K, rfl⟩
    exact ⟨(hB_clopen K hK).2, hB_mem K hx0K⟩
  · intro W hWo hx0W
    refine ⟨B Wᶜ, ⟨Wᶜ, hWo.isClosed_compl, fun h => h hx0W, rfl⟩, ?_⟩
    intro y hyB
    by_contra hyNotW
    exact Set.disjoint_left.mp (hB_disj Wᶜ) hyB hyNotW
  · -- Closure-preserving: since every `U ∈ 𝓑` is clopen, it suffices that `⋃₀ 𝓖` is closed!
    intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hzCl
      by_contra hzNot
      obtain ⟨k, hzk⟩ := hE_cover z
      -- For each `m ≤ k`, since `{Wexp m x}` is discrete, there is at most one `x : E m` with `z ∈ V m x`.
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
      obtain ⟨K, hK, hx0K, rfl⟩ := h𝓖 hUG
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
          exact Set.disjoint_left.mp (hV_disj m x k (Nat.lt_of_not_ge hgt)) hzx hzk
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

/-! ## Part 4: Gruenhage's Theorem (1978) for σ-Closed-Discrete, σ-Discrete, and Countable Spaces -/

/-- **Gruenhage (1978), σ-Closed-Discrete Form**:
Every stratifiable space that is a countable union of closed discrete subsets is an **`M₁`-space**. -/
theorem isM1_of_stratifiable_sigma_closedDiscrete {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) {F : ℕ → Set X}
    (hF_disc : ∀ n (S : Set X), S ⊆ F n → IsClosed S)
    (hF_cover : (⋃ n, F n) = Set.univ) :
    MSpace.IsM1 X := by
  have : T1Space X := hS.1
  have : NormalSpace X := normalSpace_of_isStratifiable hS
  have : T3Space X := inferInstance
  choose Wexp hWexp_open hWexp_disc using fun n =>
    stratifiable_discrete_open_expansion hS (hF_disc n)
  choose 𝓤 hU_open hU_base hU_cp using fun x : X =>
    hasCPOuterBase_of_stratifiable_sigma_closedDiscrete hS hF_disc hF_cover x
  let 𝓒 : ℕ → Set (Set X) := fun n =>
    { B : Set X | ∃ d : F n, B ∈ 𝓤 d.1 ∧ B ⊆ Wexp n d }
  have hC_open : ∀ n, ∀ B ∈ 𝓒 n, IsOpen B := by
    rintro n B ⟨d, hBU, _⟩
    exact (hU_open d.1 B hBU).1
  have hC_cp : ∀ n, MSpace.ClosurePreserving (𝓒 n) := by
    intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      obtain ⟨O, hOo, hzO, hOuniq⟩ := hWexp_disc n z
      obtain ⟨y₀, hy₀O, ⟨B₀, hB₀G, hy₀B₀⟩⟩ := mem_closure_iff.mp hz O hOo hzO
      obtain ⟨d₀, _, hB₀W⟩ := h𝓖 hB₀G
      have hOd₀ : (O ∩ Wexp n d₀).Nonempty := ⟨y₀, hy₀O, hB₀W hy₀B₀⟩
      let 𝓖₀ : Set (Set X) := { B ∈ 𝓖 | B ∈ 𝓤 d₀.1 ∧ B ⊆ Wexp n d₀ }
      have hz_cl0 : z ∈ closure (⋃₀ 𝓖₀) := by
        rw [mem_closure_iff]; intro W hWo hzW
        obtain ⟨q, hqOW, ⟨B, hBG, hqB⟩⟩ :=
          mem_closure_iff.mp hz (O ∩ W) (hOo.inter hWo) ⟨hzO, hzW⟩
        obtain ⟨d, hBU, hBW⟩ := h𝓖 hBG
        have hd_eq : d = d₀ := hOuniq d d₀ ⟨q, hqOW.1, hBW hqB⟩ hOd₀
        subst hd_eq
        exact ⟨q, hqOW.2, ⟨B, ⟨hBG, hBU, hBW⟩, hqB⟩⟩
      rw [hU_cp d₀.1 𝓖₀ (fun _ h => h.2.1)] at hz_cl0
      obtain ⟨_, ⟨B, hBG₀, rfl⟩, hzB⟩ := hz_cl0
      exact ⟨closure B, ⟨B, hBG₀.1, rfl⟩, hzB⟩
    · rintro z ⟨_, ⟨B, hBG, rfl⟩, hzB⟩
      exact closure_mono (Set.subset_sUnion_of_mem hBG) hzB
  refine ⟨inferInstance, ⋃ n, 𝓒 n, ?_, ⟨𝓒, hC_cp, rfl⟩⟩
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro B hB
    obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
    exact hC_open n B hBn
  · intro x W hxW hWo
    obtain ⟨n, hxn⟩ := mem_iUnion.mp (show x ∈ ⋃ n, F n by rw [hF_cover]; trivial)
    obtain ⟨V, hVU, hVW⟩ := hU_base x (W ∩ Wexp n ⟨x, hxn⟩)
      (hWo.inter (hWexp_open n ⟨x, hxn⟩).1) ⟨hxW, (hWexp_open n ⟨x, hxn⟩).2⟩
    refine ⟨V, mem_iUnion.mpr ⟨n, ⟨⟨x, hxn⟩, hVU, hVW.trans inter_subset_right⟩⟩,
      (hU_open x V hVU).2, hVW.trans inter_subset_left⟩

/-- **Gruenhage (1978), Full σ-Discrete Form**:
Every σ-discrete stratifiable space (a countable union `⋃ n, D n` of discrete subspaces,
not assumed closed) is an **`M₁`-space**. -/
theorem isM1_of_stratifiable_sigma_discrete {X : Type*} [TopologicalSpace X]
    (hS : MSpace.IsStratifiable X) {D : ℕ → Set X}
    (hD_disc : ∀ n, ∀ x ∈ D n, ∃ U : Set X, IsOpen U ∧ U ∩ D n = {x})
    (hD_cover : (⋃ n, D n) = Set.univ) :
    MSpace.IsM1 X := by
  have : T1Space X := hS.1
  obtain ⟨G, hGo, hGsub, hGinter, _⟩ := hS.2
  -- Each `O n := ⋃ x ∈ D n, U n x` is open, hence `F_σ` via `G`: `O n = ⋃ k, (G k (O n)ᶜ)ᶜ`.
  have hO_ex : ∀ n, ∃ O : Set X, IsOpen O ∧ D n ⊆ O ∧
      ∀ z ∈ O, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ ∃ x ∈ D n, U ∩ D n = {x} := by
    intro n
    choose U hUo hUeq using fun x : D n => hD_disc n x.1 x.2
    refine ⟨⋃ x : D n, U x, isOpen_iUnion hUo, fun x hx => ?_, fun z hz => ?_⟩
    · refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      have : x ∈ U ⟨x, hx⟩ ∩ D n := by rw [hUeq ⟨x, hx⟩]; exact mem_singleton x
      exact this.1
    · obtain ⟨x, hzx⟩ := mem_iUnion.mp hz
      exact ⟨U x, hUo x, hzx, x.1, x.2, hUeq x⟩
  choose O hOo hDO hOloc using hO_ex
  let F : ℕ → Set X := fun m =>
    let p := Nat.unpair m
    D p.1 ∩ (G p.2 (O p.1)ᶜ)ᶜ
  have hF_disc : ∀ m (S : Set X), S ⊆ F m → IsClosed S := by
    intro m S hSF
    set p := Nat.unpair m
    rw [← closure_subset_iff_isClosed]
    intro z hzCl
    have hK_cl : IsClosed (G p.2 (O p.1)ᶜ)ᶜ := (hGo p.2 (O p.1)ᶜ (hOo p.1).isClosed_compl).isClosed_compl
    have hzK : z ∈ (G p.2 (O p.1)ᶜ)ᶜ := closure_minimal (hSF.trans inter_subset_right) hK_cl hzCl
    have hzO : z ∈ O p.1 := by
      by_contra hzNotO
      exact hzK (hGsub p.2 (O p.1)ᶜ (hOo p.1).isClosed_compl hzNotO)
    obtain ⟨U, hUo, hzU, x, hxD, hUeq⟩ := hOloc p.1 z hzO
    obtain ⟨y, hyU, hyS⟩ := mem_closure_iff.mp hzCl U hUo hzU
    have hyx : y = x := by
      have : y ∈ U ∩ D p.1 := ⟨hyU, (hSF hyS).1⟩
      rw [hUeq] at this; exact this
    subst hyx
    by_contra hzNotS
    have hzx : z ≠ y := fun h => hzNotS (h ▸ hyS)
    obtain ⟨w, ⟨hwU, hwy⟩, hwS⟩ :=
      mem_closure_iff.mp hzCl (U \ {y}) (hUo.sdiff isClosed_singleton) ⟨hzU, hzx⟩
    have hwy' : w = y := by
      have : w ∈ U ∩ D p.1 := ⟨hwU, (hSF hwS).1⟩
      rw [hUeq] at this; exact this
    exact hwy hwy'
  have hF_cover : (⋃ m, F m) = Set.univ := by
    ext x; simp only [mem_univ, iff_true]
    obtain ⟨n, hxn⟩ := mem_iUnion.mp (show x ∈ ⋃ n, D n by rw [hD_cover]; trivial)
    have hxNotC : x ∉ (O n)ᶜ := fun h => h (hDO n hxn)
    rw [← hGinter (O n)ᶜ (hOo n).isClosed_compl, mem_iInter] at hxNotC
    push Not at hxNotC
    obtain ⟨k, hxk⟩ := hxNotC
    refine mem_iUnion.mpr ⟨Nat.pair n k, ?_⟩
    simp only [F, Nat.unpair_pair]
    exact ⟨hxn, fun h => hxk (subset_closure h)⟩
  exact isM1_of_stratifiable_sigma_closedDiscrete hS hF_disc hF_cover

/-- **Corollary (Countable Stratifiable Spaces are `M₁`)**:
Every **countable** stratifiable space is an **`M₁`-space**.
In particular, any counterexample to `Tinf` (`M₃ ⇒ M₁`) / `L_0020` / `L_0030` / `L_0031`
must be **uncountable** (and not σ-discrete). -/
theorem isM1_of_countable_stratifiable {X : Type*} [TopologicalSpace X] [Countable X]
    (hS : MSpace.IsStratifiable X) :
    MSpace.IsM1 X := by
  have : T1Space X := hS.1
  by_cases hne : Nonempty X
  · obtain ⟨f, hf⟩ := exists_surjective_nat X
    let F : ℕ → Set X := fun n => {f n}
    refine isM1_of_stratifiable_sigma_closedDiscrete hS (F := F) ?_ ?_
    · intro n S hSsub
      by_cases hmem : f n ∈ S
      · have hEq : S = {f n} := Subset.antisymm hSsub (Set.singleton_subset_iff.mpr hmem)
        rw [hEq]; exact isClosed_singleton
      · have hEq : S = ∅ := Set.eq_empty_of_forall_notMem fun y hy => hmem (hSsub hy ▸ hy)
        rw [hEq]; exact isClosed_empty
    · ext x; simp only [mem_iUnion, mem_univ, iff_true]
      obtain ⟨n, rfl⟩ := hf x
      exact ⟨n, mem_singleton (f n)⟩
  · have : IsEmpty X := not_nonempty_iff.mp hne
    have : NormalSpace X := normalSpace_of_isStratifiable hS
    have : T3Space X := inferInstance
    refine ⟨inferInstance, ∅, ?_, ⟨fun _ => ∅, fun _ 𝓖 h𝓖 => by
      have hEq : 𝓖 = ∅ := Set.subset_empty_iff.mp h𝓖
      subst hEq; simp, by simp⟩⟩
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
      (fun _ h => h.elim) (fun x => IsEmpty.elim inferInstance x)

end Research.Gruenhage1978
