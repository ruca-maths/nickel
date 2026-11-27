import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Set.Lattice.Indexed
import Targets.Defs

/-!
# Borges (1966) Theorem 3.1 & Heath–Lutzer–Zenor (1973): Closed Images of Stratifiable Spaces

We prove:
1. `IsMonotonicallyNormal X` and `IsSemiStratifiable X` (classical generalized metric properties).
2. `stratifiable_imp_monotonicallyNormal` & `stratifiable_imp_semiStratifiable`.
3. `isStratifiable_of_monotonicallyNormal_semiStratifiable` &
   `isStratifiable_iff_monotonicallyNormal_and_semiStratifiable` (**Heath–Lutzer–Zenor 1973**,
   Theorem 2.5): a `T₁` space is stratifiable if and only if it is both monotonically normal
   and semi-stratifiable.
4. `t1Space_of_isClosedMap`, `monotonicallyNormal_of_isClosedMap`, &
   `semiStratifiable_of_isClosedMap`: all three properties are preserved by arbitrary closed
   continuous surjections `f : X → Y` (no compact fibers / perfectness needed!).
5. `isStratifiable_of_isClosedMap` (**Borges 1966**, Theorem 3.1):
   every closed continuous surjection `f : X → Y` from a stratifiable space `X` onto any
   topological space `Y` makes `Y` stratifiable (and `T₁` automatically).

This strictly generalizes `Borges_PerfectMap_And_ClosedSum.lean` (which assumed compact fibers)
and `CollapseQuotient_OuterBase.lean` (which collapsed a single closed set `F`).
-/

namespace Research.BorgesClosedImage

open Set Topology

/-- A `T₁` space `X` is **monotonically normal** (Heath–Lutzer–Zenor 1973) if to every pair
of disjoint closed sets `(A, B)` one can assign an open set `H A B` such that
`A ⊆ H A B`, `closure (H A B) ∩ B = ∅`, and `H` is monotone in `A` and antitone in `B`. -/
def IsMonotonicallyNormal (X : Type*) [TopologicalSpace X] : Prop :=
  T1Space X ∧
  ∃ H : Set X → Set X → Set X,
    (∀ A B, IsClosed A → IsClosed B → Disjoint A B → IsOpen (H A B)) ∧
    (∀ A B, IsClosed A → IsClosed B → Disjoint A B → A ⊆ H A B) ∧
    (∀ A B, IsClosed A → IsClosed B → Disjoint A B → Disjoint (closure (H A B)) B) ∧
    (∀ A₁ A₂ B₁ B₂,
      IsClosed A₁ → IsClosed A₂ → IsClosed B₁ → IsClosed B₂ →
      Disjoint A₁ B₁ → Disjoint A₂ B₂ →
      A₁ ⊆ A₂ → B₂ ⊆ B₁ → H A₁ B₁ ⊆ H A₂ B₂)

/-- A `T₁` space `X` is **semi-stratifiable** (Creede 1970) if to every open set `U` and `n : ℕ`
one can assign a closed set `K n U ⊆ U`, monotone in `U`, such that `⋃ n, K n U = U`. -/
def IsSemiStratifiable (X : Type*) [TopologicalSpace X] : Prop :=
  T1Space X ∧
  ∃ K : ℕ → Set X → Set X,
    (∀ n U, IsOpen U → IsClosed (K n U)) ∧
    (∀ n U, IsOpen U → K n U ⊆ U) ∧
    (∀ U, IsOpen U → (⋃ n, K n U) = U) ∧
    (∀ n U₁ U₂, IsOpen U₁ → IsOpen U₂ → U₁ ⊆ U₂ → K n U₁ ⊆ K n U₂)

/-- Every stratifiable space has an antitone stratification. -/
private theorem exists_antitone_stratification {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) :
    T1Space X ∧ ∃ G : ℕ → Set X → Set X,
      MSpace.IsStratification G ∧ ∀ m n C, m ≤ n → G n C ⊆ G m C := by
  rcases hStrat with ⟨hT1, G₀, hopen, hsub, hinter, hmono⟩
  let G : ℕ → Set X → Set X := fun n C => Nat.rec (G₀ 0 C) (fun k ih => ih ∩ G₀ (k + 1) C) n
  have hG_open : ∀ n C, IsClosed C → IsOpen (G n C) := by
    intro n C hC
    induction n with
    | zero => exact hopen 0 C hC
    | succ k ih => exact ih.inter (hopen (k + 1) C hC)
  have hG_sub : ∀ n C, IsClosed C → C ⊆ G n C := by
    intro n C hC
    induction n with
    | zero => exact hsub 0 C hC
    | succ k ih => exact subset_inter ih (hsub (k + 1) C hC)
  have hG_le_G0 : ∀ n C, G n C ⊆ G₀ n C := by
    intro n C
    cases n with
    | zero => exact Subset.rfl
    | succ k => exact inter_subset_right
  have hG_succ : ∀ n C, G (n + 1) C ⊆ G n C := fun _ _ => inter_subset_left
  have hG_anti : ∀ m n C, m ≤ n → G n C ⊆ G m C := by
    intro m n C hmn
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hG_succ _ C).trans ih
  refine ⟨hT1, G, ⟨hG_open, hG_sub, ?_, ?_⟩, hG_anti⟩
  · intro C hC
    apply Subset.antisymm
    · intro x hx
      rw [← hinter C hC, mem_iInter]
      intro n
      exact closure_mono (hG_le_G0 n C) (mem_iInter.mp hx n)
    · intro x hxC
      exact mem_iInter.mpr fun n => subset_closure (hG_sub n C hC hxC)
  · intro n C₁ C₂ hC₁ hC₂ hC₁₂
    induction n with
    | zero => exact hmono 0 C₁ C₂ hC₁ hC₂ hC₁₂
    | succ k ih => exact inter_subset_inter ih (hmono (k + 1) C₁ C₂ hC₁ hC₂ hC₁₂)

/-- Every stratifiable space is monotonically normal (Heath–Lutzer–Zenor 1973). -/
theorem stratifiable_imp_monotonicallyNormal {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) : IsMonotonicallyNormal X := by
  obtain ⟨hT1, G, ⟨hGopen, hGsub, hGinter, hGmono⟩, hGanti⟩ :=
    exists_antitone_stratification hStrat
  let H : Set X → Set X → Set X := fun A B => ⋃ n, (G n A \ closure (G n B))
  refine ⟨hT1, H, ?_, ?_, ?_, ?_⟩
  · intro A B hA hB _
    exact isOpen_iUnion fun n => (hGopen n A hA).sdiff isClosed_closure
  · intro A B hA hB hdisj x hxA
    have hxB : x ∉ B := Set.disjoint_left.mp hdisj hxA
    rw [← hGinter B hB, mem_iInter] at hxB
    push Not at hxB
    obtain ⟨n, hn⟩ := hxB
    exact mem_iUnion.mpr ⟨n, hGsub n A hA hxA, hn⟩
  · intro A B hA hB hdisj
    rw [Set.disjoint_left]
    intro x hxCl hxB
    have hxA : x ∉ A := Set.disjoint_right.mp hdisj hxB
    rw [← hGinter A hA, mem_iInter] at hxA
    push Not at hxA
    obtain ⟨m, hm⟩ := hxA
    let W : Set X := G m B \ closure (G m A)
    have hWo : IsOpen W := (hGopen m B hB).sdiff isClosed_closure
    have hxW : x ∈ W := ⟨hGsub m B hB hxB, hm⟩
    obtain ⟨y, hyW, hyH⟩ := mem_closure_iff.mp hxCl W hWo hxW
    obtain ⟨n, hyGnA, hyNotGnB⟩ := mem_iUnion.mp hyH
    rcases le_total n m with hnm | hmn
    · exact hyNotGnB (subset_closure (hGanti n m B hnm hyW.1))
    · exact hyW.2 (subset_closure (hGanti m n A hmn hyGnA))
  · intro A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ _ _ hA hB
    exact iUnion_mono fun n =>
      Set.sdiff_subset_sdiff (hGmono n A₁ A₂ hA₁ hA₂ hA)
        (closure_mono (hGmono n B₂ B₁ hB₂ hB₁ hB))

/-- Every stratifiable space is semi-stratifiable. -/
theorem stratifiable_imp_semiStratifiable {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) : IsSemiStratifiable X := by
  rcases hStrat with ⟨hT1, G, hGopen, hGsub, hGinter, hGmono⟩
  let K : ℕ → Set X → Set X := fun n U => (G n Uᶜ)ᶜ
  refine ⟨hT1, K, ?_, ?_, ?_, ?_⟩
  · intro n U hU
    exact (hGopen n Uᶜ hU.isClosed_compl).isClosed_compl
  · intro n U hU x hx
    by_contra hxU
    exact hx (hGsub n Uᶜ hU.isClosed_compl hxU)
  · intro U hU
    apply Subset.antisymm
    · intro x hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      by_contra hxU
      exact hxn (hGsub n Uᶜ hU.isClosed_compl hxU)
    · intro x hxU
      have hxUc : x ∉ Uᶜ := fun h => h hxU
      rw [← hGinter Uᶜ hU.isClosed_compl, mem_iInter] at hxUc
      push Not at hxUc
      obtain ⟨n, hn⟩ := hxUc
      exact mem_iUnion.mpr ⟨n, fun h => hn (subset_closure h)⟩
  · intro n U₁ U₂ hU₁ hU₂ hU₁₂ x hx h2
    exact hx (hGmono n U₂ᶜ U₁ᶜ hU₂.isClosed_compl hU₁.isClosed_compl
      (Set.compl_subset_compl.mpr hU₁₂) h2)

/-- **Heath–Lutzer–Zenor (1973), Theorem 2.5**:
Every monotonically normal, semi-stratifiable space is stratifiable. -/
theorem isStratifiable_of_monotonicallyNormal_semiStratifiable {X : Type*} [TopologicalSpace X]
    (hMN : IsMonotonicallyNormal X) (hSS : IsSemiStratifiable X) :
    MSpace.IsStratifiable X := by
  rcases hMN with ⟨hT1, H, hHopen, hHsub, hHdisj, hHmono⟩
  rcases hSS with ⟨_, K, hKcl, hKsub, hKunion, hKmono⟩
  let G : ℕ → Set X → Set X := fun n F => (closure (H (K n Fᶜ) F))ᶜ
  refine ⟨hT1, G, ?_, ?_, ?_, ?_⟩
  · intro n F _
    exact isClosed_closure.isOpen_compl
  · intro n F hF x hxF
    have hdisj : Disjoint (K n Fᶜ) F :=
      Set.disjoint_left.mpr fun y hyK hyF => (hKsub n Fᶜ hF.isOpen_compl hyK) hyF
    exact Set.disjoint_right.mp (hHdisj (K n Fᶜ) F (hKcl n Fᶜ hF.isOpen_compl) hF hdisj) hxF
  · intro F hF
    apply Subset.antisymm
    · intro x hx
      by_contra hxF
      have hxFc : x ∈ ⋃ n, K n Fᶜ := by rw [hKunion Fᶜ hF.isOpen_compl]; exact hxF
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hxFc
      have hdisj : Disjoint (K n Fᶜ) F :=
        Set.disjoint_left.mpr fun y hyK hyF => (hKsub n Fᶜ hF.isOpen_compl hyK) hyF
      have hHo : IsOpen (H (K n Fᶜ) F) := hHopen _ _ (hKcl n Fᶜ hF.isOpen_compl) hF hdisj
      have hxH : x ∈ H (K n Fᶜ) F := hHsub _ _ (hKcl n Fᶜ hF.isOpen_compl) hF hdisj hxn
      obtain ⟨y, hyH, hyG⟩ := mem_closure_iff.mp (mem_iInter.mp hx n) _ hHo hxH
      exact hyG (subset_closure hyH)
    · intro x hxF
      exact mem_iInter.mpr fun n => subset_closure (by
        have hdisj : Disjoint (K n Fᶜ) F :=
          Set.disjoint_left.mpr fun y hyK hyF => (hKsub n Fᶜ hF.isOpen_compl hyK) hyF
        exact Set.disjoint_right.mp (hHdisj _ _ (hKcl n Fᶜ hF.isOpen_compl) hF hdisj) hxF)
  · intro n F₁ F₂ hF₁ hF₂ hF₁₂
    have hdisj₁ : Disjoint (K n F₁ᶜ) F₁ :=
      Set.disjoint_left.mpr fun y hyK hyF => (hKsub n F₁ᶜ hF₁.isOpen_compl hyK) hyF
    have hdisj₂ : Disjoint (K n F₂ᶜ) F₂ :=
      Set.disjoint_left.mpr fun y hyK hyF => (hKsub n F₂ᶜ hF₂.isOpen_compl hyK) hyF
    have hK21 : K n F₂ᶜ ⊆ K n F₁ᶜ :=
      hKmono n F₂ᶜ F₁ᶜ hF₂.isOpen_compl hF₁.isOpen_compl (Set.compl_subset_compl.mpr hF₁₂)
    exact Set.compl_subset_compl.mpr (closure_mono
      (hHmono (K n F₂ᶜ) (K n F₁ᶜ) F₂ F₁
        (hKcl n F₂ᶜ hF₂.isOpen_compl) (hKcl n F₁ᶜ hF₁.isOpen_compl) hF₂ hF₁
        hdisj₂ hdisj₁ hK21 hF₁₂))

/-- **Heath–Lutzer–Zenor (1973), Theorem 2.5 (equivalence)**:
A space is stratifiable if and only if it is both monotonically normal and semi-stratifiable. -/
theorem isStratifiable_iff_monotonicallyNormal_and_semiStratifiable
    {X : Type*} [TopologicalSpace X] :
    MSpace.IsStratifiable X ↔ IsMonotonicallyNormal X ∧ IsSemiStratifiable X :=
  ⟨fun h => ⟨stratifiable_imp_monotonicallyNormal h, stratifiable_imp_semiStratifiable h⟩,
   fun ⟨hMN, hSS⟩ => isStratifiable_of_monotonicallyNormal_semiStratifiable hMN hSS⟩

/-- A closed surjection from a `T₁` space lands in a `T₁` space. -/
theorem t1Space_of_isClosedMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] {f : X → Y} (hf_surj : Function.Surjective f) (hf_closed : IsClosedMap f) :
    T1Space Y := by
  refine ⟨fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hf_surj y
  have hEq : ({f x} : Set Y) = f '' {x} := by simp
  rw [hEq]
  exact hf_closed {x} isClosed_singleton

/-- Monotone normality is preserved by arbitrary closed continuous surjections
(Heath–Lutzer–Zenor 1973, Theorem 2.6). -/
theorem monotonicallyNormal_of_isClosedMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf_cont : Continuous f) (hf_surj : Function.Surjective f)
    (hf_closed : IsClosedMap f) (hMN : IsMonotonicallyNormal X) :
    IsMonotonicallyNormal Y := by
  rcases hMN with ⟨hT1X, H, hHopen, hHsub, hHdisj, hHmono⟩
  have : T1Space X := hT1X
  have hT1Y : T1Space Y := t1Space_of_isClosedMap hf_surj hf_closed
  let HY : Set Y → Set Y → Set Y := fun A B => (f '' (H (f ⁻¹' A) (f ⁻¹' B))ᶜ)ᶜ
  refine ⟨hT1Y, HY, ?_, ?_, ?_, ?_⟩
  · intro A B hA hB hdisj
    have hdisj' : Disjoint (f ⁻¹' A) (f ⁻¹' B) := hdisj.preimage f
    exact (hf_closed _ (hHopen _ _ (hA.preimage hf_cont) (hB.preimage hf_cont)
      hdisj').isClosed_compl).isOpen_compl
  · intro A B hA hB hdisj y hyA
    have hdisj' : Disjoint (f ⁻¹' A) (f ⁻¹' B) := hdisj.preimage f
    rintro ⟨x, hxNot, rfl⟩
    exact hxNot (hHsub _ _ (hA.preimage hf_cont) (hB.preimage hf_cont) hdisj' hyA)
  · intro A B hA hB hdisj
    have hdisj' : Disjoint (f ⁻¹' A) (f ⁻¹' B) := hdisj.preimage f
    rw [Set.disjoint_left]
    intro y hyCl hyB
    let W : Set Y := (f '' closure (H (f ⁻¹' A) (f ⁻¹' B)))ᶜ
    have hWo : IsOpen W := (hf_closed _ isClosed_closure).isOpen_compl
    have hyW : y ∈ W := by
      rintro ⟨x, hxCl, rfl⟩
      exact Set.disjoint_left.mp
        (hHdisj _ _ (hA.preimage hf_cont) (hB.preimage hf_cont) hdisj') hxCl hyB
    obtain ⟨z, hzW, hzHY⟩ := mem_closure_iff.mp hyCl W hWo hyW
    obtain ⟨x, rfl⟩ := hf_surj z
    have hxH : x ∈ H (f ⁻¹' A) (f ⁻¹' B) := by
      by_contra hxNot
      exact hzHY ⟨x, hxNot, rfl⟩
    exact hzW ⟨x, subset_closure hxH, rfl⟩
  · intro A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ hdisj₁ hdisj₂ hA hB
    have hsubH : H (f ⁻¹' A₁) (f ⁻¹' B₁) ⊆ H (f ⁻¹' A₂) (f ⁻¹' B₂) :=
      hHmono _ _ _ _ (hA₁.preimage hf_cont) (hA₂.preimage hf_cont)
        (hB₁.preimage hf_cont) (hB₂.preimage hf_cont)
        (hdisj₁.preimage f) (hdisj₂.preimage f)
        (preimage_mono hA) (preimage_mono hB)
    exact Set.compl_subset_compl.mpr (image_mono (Set.compl_subset_compl.mpr hsubH))

/-- Semi-stratifiability is preserved by arbitrary closed continuous surjections
(Creede 1970). -/
theorem semiStratifiable_of_isClosedMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf_cont : Continuous f) (hf_surj : Function.Surjective f)
    (hf_closed : IsClosedMap f) (hSS : IsSemiStratifiable X) :
    IsSemiStratifiable Y := by
  rcases hSS with ⟨hT1X, K, hKcl, hKsub, hKunion, hKmono⟩
  have : T1Space X := hT1X
  have hT1Y : T1Space Y := t1Space_of_isClosedMap hf_surj hf_closed
  let KY : ℕ → Set Y → Set Y := fun n U => f '' K n (f ⁻¹' U)
  refine ⟨hT1Y, KY, ?_, ?_, ?_, ?_⟩
  · intro n U hU
    exact hf_closed _ (hKcl n _ (hU.preimage hf_cont))
  · intro n U hU
    rintro _ ⟨x, hxK, rfl⟩
    exact hKsub n _ (hU.preimage hf_cont) hxK
  · intro U hU
    apply Subset.antisymm
    · intro y hy
      obtain ⟨n, x, hxK, rfl⟩ := mem_iUnion.mp hy
      exact hKsub n _ (hU.preimage hf_cont) hxK
    · intro y hyU
      obtain ⟨x, rfl⟩ := hf_surj y
      have hx : x ∈ ⋃ n, K n (f ⁻¹' U) := by
        rw [hKunion _ (hU.preimage hf_cont)]; exact hyU
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨n, x, hxn, rfl⟩
  · intro n U₁ U₂ hU₁ hU₂ hU₁₂
    exact image_mono (hKmono n _ _ (hU₁.preimage hf_cont) (hU₂.preimage hf_cont)
      (preimage_mono hU₁₂))

/-- **Borges (1966), Theorem 3.1**:
Every closed continuous image of a stratifiable space is stratifiable. -/
theorem isStratifiable_of_isClosedMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf_cont : Continuous f) (hf_surj : Function.Surjective f)
    (hf_closed : IsClosedMap f) (hStrat : MSpace.IsStratifiable X) :
    MSpace.IsStratifiable Y :=
  isStratifiable_of_monotonicallyNormal_semiStratifiable
    (monotonicallyNormal_of_isClosedMap hf_cont hf_surj hf_closed
      (stratifiable_imp_monotonicallyNormal hStrat))
    (semiStratifiable_of_isClosedMap hf_cont hf_surj hf_closed
      (stratifiable_imp_semiStratifiable hStrat))

end Research.BorgesClosedImage
