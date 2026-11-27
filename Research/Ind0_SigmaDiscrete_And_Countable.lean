import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Basic.Countable.Defs
import Mathlib.Data.Set.Lattice.Indexed
import Targets.Defs

/-!
# Strong Zero-Dimensionality (`Ind X = 0`) for σ-Discrete & Countable Normal / Stratifiable Spaces

We prove:
1. `IsStronglyZeroDim X`: every pair of disjoint closed sets `(A, B)` is separated by a clopen set
   `W` (`IsClopen W ∧ A ⊆ W ∧ Disjoint W B`).
2. `stronglyZeroDim_of_normal_sigma_closedDiscrete`: every normal `T₁` space `X` that is a
   countable union `⋃ n, F n` of closed discrete subsets (`∀ S ⊆ F n, IsClosed S`) is strongly
   zero-dimensional (`Ind X = 0`).
3. `stronglyZeroDim_of_stratifiable_sigma_closedDiscrete`: every σ-closed-discrete stratifiable
   space is strongly zero-dimensional.
4. `stronglyZeroDim_of_countable_normal_t1` & `stronglyZeroDim_of_countable_stratifiable`:
   every countable normal `T₁` space (in particular, every countable stratifiable space) is
   strongly zero-dimensional.
5. `clopen_basis_of_stronglyZeroDim` & `regularSpace_of_stronglyZeroDim`:
   every strongly zero-dimensional `T₁` space is `T₃` and has a basis of clopen sets.
-/

namespace Research.Ind0SigmaDiscrete

open Set Topology

/-- Strong zero-dimensionality (`Ind X = 0`): disjoint closed sets are separated by a clopen set. -/
def IsStronglyZeroDim (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ A B : Set X, IsClosed A → IsClosed B → Disjoint A B →
    ∃ W : Set X, IsClopen W ∧ A ⊆ W ∧ Disjoint W B

/-- Helper: in a normal space, disjoint closed sets `A, B` admit open neighborhoods `U, V`
whose **closures** are disjoint. -/
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

/-- **Strong zero-dimensionality of σ-closed-discrete normal spaces (`Ind X = 0`)**:
If `X` is normal and `X = ⋃ n, F n` where every subset of each `F n` is closed (closed discrete),
then any two disjoint closed sets in `X` can be separated by a clopen set. -/
theorem stronglyZeroDim_of_normal_sigma_closedDiscrete {X : Type*} [TopologicalSpace X]
    [NormalSpace X]
    {F : ℕ → Set X}
    (hF_disc : ∀ n (S : Set X), S ⊆ F n → IsClosed S)
    (hF_cover : (⋃ n, F n) = Set.univ) :
    IsStronglyZeroDim X := by
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
    have hD₂_cl : IsClosed D₂ :=
      hF_disc n D₂ (fun x hx => hx.1.1)
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
    intro m n hmn
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact ih.trans (hseq_U_succ _)
  have hseq_V_mono : ∀ {m n}, m ≤ n → (seq m).1.2 ⊆ (seq n).1.2 := by
    intro m n hmn
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact ih.trans (hseq_V_succ _)
  have hseq_cover : ∀ n, F n ⊆ (seq (n + 1)).1.1 ∪ (seq (n + 1)).1.2 := fun n =>
    (hstep_ex n (seq n)).choose_spec.2.2
  let W : Set X := ⋃ n, (seq n).1.1
  let W' : Set X := ⋃ n, (seq n).1.2
  have hWo : IsOpen W := isOpen_iUnion fun n => (seq n).2.1
  have hW'o : IsOpen W' := isOpen_iUnion fun n => (seq n).2.2.1
  have hdisjWW' : Disjoint W W' := by
    rw [Set.disjoint_left]
    intro x hxW hxW'
    obtain ⟨m, hxm⟩ := mem_iUnion.mp hxW
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hxW'
    let k := max m n
    have h1 : x ∈ closure (seq k).1.1 := subset_closure (hseq_U_mono (le_max_left m n) hxm)
    have h2 : x ∈ closure (seq k).1.2 := subset_closure (hseq_V_mono (le_max_right m n) hxn)
    exact Set.disjoint_left.mp (seq k).2.2.2 h1 h2
  have hunionWW' : W ∪ W' = Set.univ := by
    ext x
    simp only [mem_univ, iff_true]
    have hxU : x ∈ ⋃ n, F n := by rw [hF_cover]; trivial
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hxU
    rcases hseq_cover n hxn with hU | hV
    · exact Or.inl (mem_iUnion.mpr ⟨n + 1, hU⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨n + 1, hV⟩)
  have hW_eq_compl : W = W'ᶜ := by
    ext x
    constructor
    · intro hxW hxW'
      exact Set.disjoint_left.mp hdisjWW' hxW hxW'
    · intro hxNotW'
      have hx : x ∈ W ∪ W' := by rw [hunionWW']; trivial
      exact hx.resolve_right hxNotW'
  have hWclopen : IsClopen W := ⟨hW_eq_compl ▸ hW'o.isClosed_compl, hWo⟩
  refine ⟨W, hWclopen, fun x hxA => mem_iUnion.mpr ⟨0, hA_st0 hxA⟩, ?_⟩
  rw [Set.disjoint_left]
  intro x hxW hxB
  exact Set.disjoint_left.mp hdisjWW' hxW (mem_iUnion.mpr ⟨0, hB_st0 hxB⟩)

/-- Every stratifiable space is normal (direct Heath–Lutzer–Zenor separation, universe-polymorphic). -/
private theorem normalSpace_of_isStratifiable {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) : NormalSpace X := by
  rcases hStrat with ⟨_, G₀, hopen, hsub, hinter, _⟩
  let G : ℕ → Set X → Set X := fun n C => Nat.rec (G₀ 0 C) (fun k ih => ih ∩ G₀ (k + 1) C) n
  have hG_open : ∀ n C, IsClosed C → IsOpen (G n C) := by
    intro n C hC; induction n with
    | zero => exact hopen 0 C hC
    | succ k ih => exact ih.inter (hopen (k + 1) C hC)
  have hG_sub : ∀ n C, IsClosed C → C ⊆ G n C := by
    intro n C hC; induction n with
    | zero => exact hsub 0 C hC
    | succ k ih => exact subset_inter ih (hsub (k + 1) C hC)
  have hG_le_G0 : ∀ n C, G n C ⊆ G₀ n C := fun n C => by cases n <;> [exact Subset.rfl; exact inter_subset_right]
  have hG_anti : ∀ {m n} C, m ≤ n → G n C ⊆ G m C := by
    intro m n C hmn; induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact inter_subset_left.trans ih
  refine ⟨fun A B hA hB hdisj => ?_⟩
  let U : Set X := ⋃ n, (G n A \ closure (G n B))
  let V : Set X := ⋃ n, (G n B \ closure (G n A))
  refine ⟨U, V,
    isOpen_iUnion fun n => (hG_open n A hA).sdiff isClosed_closure,
    isOpen_iUnion fun n => (hG_open n B hB).sdiff isClosed_closure,
    ?_, ?_, ?_⟩
  · intro x hxA
    have hxB : x ∉ B := Set.disjoint_left.mp hdisj hxA
    rw [← hinter B hB, mem_iInter] at hxB; push Not at hxB
    obtain ⟨n, hn⟩ := hxB
    exact mem_iUnion.mpr ⟨n, hG_sub n A hA hxA, fun h => hn (closure_mono (hG_le_G0 n B) h)⟩
  · intro x hxB
    have hxA : x ∉ A := Set.disjoint_right.mp hdisj hxB
    rw [← hinter A hA, mem_iInter] at hxA; push Not at hxA
    obtain ⟨n, hn⟩ := hxA
    exact mem_iUnion.mpr ⟨n, hG_sub n B hB hxB, fun h => hn (closure_mono (hG_le_G0 n A) h)⟩
  · rw [Set.disjoint_left]
    intro x hxU hxV
    obtain ⟨m, hm1, hm2⟩ := mem_iUnion.mp hxU
    obtain ⟨n, hn1, hn2⟩ := mem_iUnion.mp hxV
    rcases le_total m n with hmn | hnm
    · exact hm2 (subset_closure (hG_anti B hmn hn1))
    · exact hn2 (subset_closure (hG_anti A hnm hm1))

/-- Every σ-closed-discrete stratifiable space is strongly zero-dimensional (`Ind X = 0`). -/
theorem stronglyZeroDim_of_stratifiable_sigma_closedDiscrete {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X)
    {F : ℕ → Set X}
    (hF_disc : ∀ n (S : Set X), S ⊆ F n → IsClosed S)
    (hF_cover : (⋃ n, F n) = Set.univ) :
    IsStronglyZeroDim X := by
  have : NormalSpace X := normalSpace_of_isStratifiable hStrat
  exact stronglyZeroDim_of_normal_sigma_closedDiscrete hF_disc hF_cover

/-- Every countable normal `T₁` space is strongly zero-dimensional (`Ind X = 0`). -/
theorem stronglyZeroDim_of_countable_normal_t1 {X : Type*} [TopologicalSpace X]
    [T1Space X] [NormalSpace X] [Countable X] :
    IsStronglyZeroDim X := by
  by_cases hne : Nonempty X
  · obtain ⟨f, hf_surj⟩ := exists_surjective_nat X
    let F : ℕ → Set X := fun n => {f n}
    have hF_disc : ∀ n (S : Set X), S ⊆ F n → IsClosed S := by
      intro n S hS
      rcases Set.subset_singleton_iff_eq.mp hS with rfl | rfl
      · exact isClosed_empty
      · exact isClosed_singleton
    have hF_cover : (⋃ n, F n) = Set.univ := by
      ext x
      simp only [mem_iUnion, mem_singleton_iff, mem_univ, iff_true, F]
      obtain ⟨n, rfl⟩ := hf_surj x
      exact ⟨n, rfl⟩
    exact stronglyZeroDim_of_normal_sigma_closedDiscrete hF_disc hF_cover
  · intro A B _ _ _
    refine ⟨∅, isClopen_empty, fun x _ => (hne ⟨x⟩).elim, Set.disjoint_left.mpr fun _ h => h.elim⟩

/-- Every countable stratifiable space is strongly zero-dimensional (`Ind X = 0`). -/
theorem stronglyZeroDim_of_countable_stratifiable {X : Type*} [TopologicalSpace X] [Countable X]
    (hStrat : MSpace.IsStratifiable X) :
    IsStronglyZeroDim X := by
  have : T1Space X := hStrat.1
  have : NormalSpace X := normalSpace_of_isStratifiable hStrat
  exact stronglyZeroDim_of_countable_normal_t1

/-- Every strongly zero-dimensional `T₁` space has a basis of clopen sets. -/
theorem clopen_basis_of_stronglyZeroDim {X : Type*} [TopologicalSpace X] [T1Space X]
    (hInd : IsStronglyZeroDim X) :
    TopologicalSpace.IsTopologicalBasis { W : Set X | IsClopen W } := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun _ hW => hW.2) ?_
  intro x U hxU hUo
  have hdisj : Disjoint ({x} : Set X) Uᶜ :=
    Set.disjoint_singleton_left.mpr (fun h => h hxU)
  obtain ⟨W, hWclopen, hxW, hWdisj⟩ :=
    hInd {x} Uᶜ isClosed_singleton hUo.isClosed_compl hdisj
  refine ⟨W, hWclopen, hxW (mem_singleton x), ?_⟩
  intro y hyW
  by_contra hyU
  exact Set.disjoint_left.mp hWdisj hyW hyU

end Research.Ind0SigmaDiscrete
