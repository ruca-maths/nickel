import Targets
import Defs.D_0001
import Defs.D_0010
import Specs.L_0020
import Specs.L_0030

/-!
# Collapse Quotient `X / F`: Stratifiability & Closed-Set Outer Bases

Given a topological space `X` and a closed subset `F : Set X`, we construct the
collapse quotient `CollapseQuotient X F := Option { x : X // x ∉ F }` (where `none`
represents the collapsed closed set `F` and `some ⟨x, hx⟩` represents `x ∈ Fᶜ`)
equipped with the coinduced quotient topology of `collapseProj F : X → CollapseQuotient X F`.

We prove (zero `sorry`, standard axioms only):
1. `collapseProj_continuous`, `collapseProj_surjective`, `collapseProj_isClosedMap`:
   the canonical projection `π : X → X / F` is a closed continuous surjection.
2. `collapseQuotient_t1Space`: `X / F` is `T1Space` whenever `X` is `T1Space` and `F` is closed.
3. `collapseQuotient_isStratifiable`: **Every** collapse quotient `X / F` of a
   stratifiable space `X` by a closed subset `F` is stratifiable (via the
   Heath–Lutzer–Zenor monotone normality operator `H_X(A, B)`).
4. `collapseQuotient_hasCPOuterBase_iff` & `collapseQuotient_hasSigmaCPLocalBase_iff`:
   `none` has a CP (resp. `σ`-CP) open outer base in `X / F` if and only if `F` has
   a CP (resp. `σ`-CP) open outer base in `X`.
5. `closed_hasCPOuterBase_of_not_L0020` & `closed_hasSigmaCPOuterBase_of_not_L0030`:
   Under `¬ Specs.L_0020.stmt` (resp. `¬ Specs.L_0030.stmt`), EVERY closed subset `F`
   of EVERY stratifiable space `X` admits a CP (resp. `σ`-CP) open outer base.
-/

namespace Research.CollapseQuotientTheorem

open MSpace Set Topology

section DefinitionAndBasic

/-- The collapse quotient `X / F` represented concretely as `Option { x : X // x ∉ F }`,
with `none` representing the collapsed set `F`. -/
abbrev CollapseQuotient (X : Type) (F : Set X) : Type := Option { x : X // x ∉ F }

/-- Canonical projection `π : X → CollapseQuotient X F`. -/
noncomputable def collapseProj {X : Type} (F : Set X) (x : X) : CollapseQuotient X F :=
  by classical exact if hx : x ∈ F then none else some ⟨x, hx⟩

/-- The quotient (coinduced) topology on `CollapseQuotient X F`. -/
@[instance_reducible]
noncomputable def collapseTopology {X : Type} [TopologicalSpace X] (F : Set X) :
    TopologicalSpace (CollapseQuotient X F) :=
  TopologicalSpace.coinduced (collapseProj F) inferInstance

theorem collapse_isOpen_iff {X : Type} [TopologicalSpace X] (F : Set X)
    {S : Set (CollapseQuotient X F)} :
    @IsOpen (CollapseQuotient X F) (collapseTopology F) S ↔
      IsOpen (collapseProj F ⁻¹' S) :=
  Iff.rfl

theorem collapse_isClosed_iff {X : Type} [TopologicalSpace X] (F : Set X)
    {S : Set (CollapseQuotient X F)} :
    @IsClosed (CollapseQuotient X F) (collapseTopology F) S ↔
      IsClosed (collapseProj F ⁻¹' S) := by
  let : TopologicalSpace (CollapseQuotient X F) := collapseTopology F
  rw [← isOpen_compl_iff, collapse_isOpen_iff, preimage_compl, isOpen_compl_iff]

theorem collapseProj_continuous {X : Type} [TopologicalSpace X] (F : Set X) :
    @Continuous X (CollapseQuotient X F) _ (collapseTopology F) (collapseProj F) := by
  let : TopologicalSpace (CollapseQuotient X F) := collapseTopology F
  exact continuous_coinduced_rng

theorem collapseProj_eq_none_iff {X : Type} (F : Set X) (x : X) :
    collapseProj F x = none ↔ x ∈ F := by
  classical
  simp only [collapseProj]
  split_ifs with hx
  · exact ⟨fun _ => hx, fun _ => rfl⟩
  · exact ⟨(fun h => by cases h), fun h => (hx h).elim⟩

theorem collapseProj_eq_some_iff {X : Type} (F : Set X) (x : X) (y : { z : X // z ∉ F }) :
    collapseProj F x = some y ↔ x = y.1 := by
  classical
  simp only [collapseProj]
  split_ifs with hx
  · exact ⟨(fun h => by cases h), fun h => (y.2 (h ▸ hx)).elim⟩
  · constructor
    · intro h; cases h; rfl
    · intro h; congr 1; exact Subtype.ext h

theorem collapseProj_surjective {X : Type} {F : Set X} (hFne : F.Nonempty) :
    Function.Surjective (collapseProj F) := by
  rintro (_ | ⟨x, hx⟩)
  · obtain ⟨x₀, hx₀⟩ := hFne
    exact ⟨x₀, (collapseProj_eq_none_iff F x₀).mpr hx₀⟩
  · exact ⟨x, (collapseProj_eq_some_iff F x ⟨x, hx⟩).mpr rfl⟩

theorem collapseProj_preimage_image_nonempty {X : Type} {F : Set X} {A : Set X}
    (hAF : (A ∩ F).Nonempty) :
    collapseProj F ⁻¹' (collapseProj F '' A) = A ∪ F := by
  ext x
  simp only [mem_preimage, mem_image, mem_union]
  constructor
  · rintro ⟨a, haA, hax⟩
    by_cases hxF : x ∈ F
    · exact Or.inr hxF
    · left
      have h1 : collapseProj F x = some ⟨x, hxF⟩ :=
        (collapseProj_eq_some_iff F x ⟨x, hxF⟩).mpr rfl
      rw [h1] at hax
      have : a = x := (collapseProj_eq_some_iff F a ⟨x, hxF⟩).mp hax
      exact this ▸ haA
  · rintro (hxA | hxF)
    · exact ⟨x, hxA, rfl⟩
    · obtain ⟨a, haA, haF⟩ := hAF
      refine ⟨a, haA, ?_⟩
      rw [(collapseProj_eq_none_iff F a).mpr haF, (collapseProj_eq_none_iff F x).mpr hxF]

theorem collapseProj_preimage_image_disjoint {X : Type} {F : Set X} {A : Set X}
    (hAF : ¬ (A ∩ F).Nonempty) :
    collapseProj F ⁻¹' (collapseProj F '' A) = A := by
  ext x
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨a, haA, hax⟩
    by_cases hxF : x ∈ F
    · rw [(collapseProj_eq_none_iff F x).mpr hxF] at hax
      have haF : a ∈ F := (collapseProj_eq_none_iff F a).mp hax
      exact (hAF ⟨a, haA, haF⟩).elim
    · have h1 : collapseProj F x = some ⟨x, hxF⟩ :=
        (collapseProj_eq_some_iff F x ⟨x, hxF⟩).mpr rfl
      rw [h1] at hax
      have : a = x := (collapseProj_eq_some_iff F a ⟨x, hxF⟩).mp hax
      exact this ▸ haA
  · intro hxA
    exact ⟨x, hxA, rfl⟩

/-- The canonical projection `π : X → X / F` is a closed map whenever `F` is closed. -/
theorem collapseProj_isClosedMap {X : Type} [TopologicalSpace X] {F : Set X} (hF : IsClosed F) :
    @IsClosedMap X (CollapseQuotient X F) _ (collapseTopology F) (collapseProj F) := by
  intro A hA
  rw [collapse_isClosed_iff]
  by_cases hAF : (A ∩ F).Nonempty
  · rw [collapseProj_preimage_image_nonempty hAF]; exact hA.union hF
  · rw [collapseProj_preimage_image_disjoint hAF]; exact hA

/-- `CollapseQuotient X F` is `T1Space` whenever `X` is `T1Space` and `F` is closed. -/
theorem collapseQuotient_t1Space {X : Type} [TopologicalSpace X] [T1Space X]
    {F : Set X} (hF : IsClosed F) :
    @T1Space (CollapseQuotient X F) (collapseTopology F) := by
  let : TopologicalSpace (CollapseQuotient X F) := collapseTopology F
  refine ⟨fun q => ?_⟩
  rw [collapse_isClosed_iff]
  cases q with
  | none =>
    have hEq : collapseProj F ⁻¹' {none} = F := by
      ext x; simp [collapseProj_eq_none_iff]
    rw [hEq]; exact hF
  | some y =>
    have hEq : collapseProj F ⁻¹' {some y} = {y.1} := by
      ext x; simp [collapseProj_eq_some_iff]
    rw [hEq]; exact isClosed_singleton

end DefinitionAndBasic

section Stratifiability

/-- **Stratifiability of Collapse Quotients:**
If `X` is stratifiable and `F : Set X` is closed, then `CollapseQuotient X F` is stratifiable. -/
theorem collapseQuotient_isStratifiable {X : Type} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) {F : Set X} (hF : IsClosed F) :
    @MSpace.IsStratifiable (CollapseQuotient X F) (collapseTopology F) := by
  classical
  have hT1X : T1Space X := hStrat.1
  obtain ⟨G₀, hG₀_open, hG₀_sub, hG₀_inter, hG₀_mono⟩ := hStrat.2
  -- Decreasing stratification `G' n H := ⋂ j ≤ n, G₀ j H` on `X`
  let G' : ℕ → Set X → Set X := fun n H => ⋂ j ∈ Set.Iic n, G₀ j H
  have hG'_open : ∀ n H, IsClosed H → IsOpen (G' n H) := fun n H hH =>
    (Set.finite_Iic n).isOpen_biInter fun j _ => hG₀_open j H hH
  have hG'_sub : ∀ n H, IsClosed H → H ⊆ G' n H := fun n H hH x hx =>
    mem_iInter₂.mpr fun j _ => hG₀_sub j H hH hx
  have hG'_anti : ∀ {m n : ℕ}, m ≤ n → ∀ H, G' n H ⊆ G' m H := fun hmn H x hx =>
    mem_iInter₂.mpr fun j hj => mem_iInter₂.mp hx j (le_trans hj hmn)
  have hG'_mono : ∀ n H K, IsClosed H → IsClosed K → H ⊆ K → G' n H ⊆ G' n K :=
    fun n H K hH hK hHK x hx =>
      mem_iInter₂.mpr fun j hj => hG₀_mono j H K hH hK hHK (mem_iInter₂.mp hx j hj)
  have hG'_inter : ∀ H, IsClosed H → (⋂ n, closure (G' n H)) = H := by
    intro H hH
    apply Subset.antisymm
    · intro x hx
      rw [← hG₀_inter H hH]
      refine mem_iInter.mpr fun n => ?_
      have hsub : G' n H ⊆ G₀ n H := fun y hy => mem_iInter₂.mp hy n (Set.mem_Iic.mpr le_rfl)
      exact closure_mono hsub (mem_iInter.mp hx n)
    · exact subset_iInter fun n => (hG'_sub n H hH).trans subset_closure
  -- Heath–Lutzer–Zenor monotone normality operator on closed sets of `X`
  let HX : Set X → Set X → Set X := fun A B => ⋃ n : ℕ, G' n A \ closure (G' n B)
  have hHX_open : ∀ A B, IsClosed A → IsOpen (HX A B) := fun A B hA =>
    isOpen_iUnion fun n => (hG'_open n A hA).sdiff isClosed_closure
  have hHX_sub : ∀ A B, IsClosed A → IsClosed B → Disjoint A B → A ⊆ HX A B := by
    intro A B hA hB hdisj x hxA
    have hxB : x ∉ B := Set.disjoint_left.mp hdisj hxA
    have hxnot : x ∉ ⋂ n, closure (G' n B) := by rw [hG'_inter B hB]; exact hxB
    rw [mem_iInter] at hxnot
    push Not at hxnot
    obtain ⟨n, hn⟩ := hxnot
    exact mem_iUnion.mpr ⟨n, hG'_sub n A hA hxA, hn⟩
  have hHX_disj : ∀ A B, Disjoint (HX A B) (HX B A) := by
    intro A B
    rw [Set.disjoint_left]
    intro x hxAB hxBA
    obtain ⟨n, hnA, hnB⟩ := mem_iUnion.mp hxAB
    obtain ⟨m, hmB, hmA⟩ := mem_iUnion.mp hxBA
    rcases le_total n m with hnm | hmn
    · exact hnB (subset_closure (hG'_anti hnm B hmB))
    · exact hmA (subset_closure (hG'_anti hmn A hnA))
  have hHX_mono : ∀ A₁ A₂ B, IsClosed A₁ → IsClosed A₂ → A₁ ⊆ A₂ → HX A₁ B ⊆ HX A₂ B := by
    intro A₁ A₂ B hA₁ hA₂ h12 x hx
    obtain ⟨n, hn1, hnB⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, hG'_mono n A₁ A₂ hA₁ hA₂ h12 hn1, hnB⟩
  -- Build the stratification `GQ` on `CollapseQuotient X F`
  let : TopologicalSpace (CollapseQuotient X F) := collapseTopology F
  have hT1Q : T1Space (CollapseQuotient X F) := collapseQuotient_t1Space hF
  let pre : Set (CollapseQuotient X F) → Set X := fun H => collapseProj F ⁻¹' H
  let satG : ℕ → Set (CollapseQuotient X F) → Set X := fun n H =>
    if none ∈ H then G' n (pre H) else G' n (pre H) ∩ HX (pre H) F
  let GQ : ℕ → Set (CollapseQuotient X F) → Set (CollapseQuotient X F) := fun n H =>
    { q | match q with | none => none ∈ H | some y => y.1 ∈ satG n H }
  have hpre_GQ : ∀ n H, IsClosed H → pre (GQ n H) = satG n H := by
    intro n H hH
    have hpreH : IsClosed (pre H) := (collapse_isClosed_iff F).mp hH
    ext x
    simp only [pre, mem_preimage, GQ, mem_ofPred_eq]
    by_cases hxF : x ∈ F
    · rw [(collapseProj_eq_none_iff F x).mpr hxF]
      dsimp only [satG]
      by_cases hnone : none ∈ H
      · simp only [hnone, ↓reduceIte, true_iff]
        have hxpre : x ∈ pre H := by
          change collapseProj F x ∈ H
          rw [(collapseProj_eq_none_iff F x).mpr hxF]; exact hnone
        exact hG'_sub n (pre H) hpreH hxpre
      · simp only [hnone, ↓reduceIte, false_iff]
        intro h
        have hdisj : Disjoint (pre H) F := Set.disjoint_left.mpr fun z hz hzF =>
          hnone ((collapseProj_eq_none_iff F z).mpr hzF ▸ hz)
        have hxHX : x ∈ HX F (pre H) := hHX_sub F (pre H) hF hpreH hdisj.symm hxF
        exact Set.disjoint_left.mp (hHX_disj (pre H) F) h.2 hxHX
    · rw [(collapseProj_eq_some_iff F x ⟨x, hxF⟩).mpr rfl]
  refine ⟨hT1Q, GQ, ?_, ?_, ?_, ?_⟩
  · -- Openness of `GQ n H`
    intro n H hH
    rw [collapse_isOpen_iff]
    change IsOpen (pre (GQ n H))
    rw [hpre_GQ n H hH]
    have hpreH : IsClosed (pre H) := (collapse_isClosed_iff F).mp hH
    dsimp only [satG]
    split_ifs
    · exact hG'_open n _ hpreH
    · exact (hG'_open n _ hpreH).inter (hHX_open _ _ hpreH)
  · -- `H ⊆ GQ n H`
    intro n H hH q hqH
    have hpreH : IsClosed (pre H) := (collapse_isClosed_iff F).mp hH
    cases q with
    | none => exact hqH
    | some y =>
      have hypre : y.1 ∈ pre H := by
        change collapseProj F y.1 ∈ H
        rw [(collapseProj_eq_some_iff F y.1 y).mpr rfl]; exact hqH
      change y.1 ∈ satG n H
      dsimp only [satG]
      split_ifs with hnone
      · exact hG'_sub n _ hpreH hypre
      · have hdisj : Disjoint (pre H) F := Set.disjoint_left.mpr fun z hz hzF =>
          hnone ((collapseProj_eq_none_iff F z).mpr hzF ▸ hz)
        exact ⟨hG'_sub n _ hpreH hypre, hHX_sub _ _ hpreH hF hdisj hypre⟩
  · -- `⋂ n, closure (GQ n H) = H`
    intro H hH
    have hpreH : IsClosed (pre H) := (collapse_isClosed_iff F).mp hH
    apply Subset.antisymm
    · intro q hq
      by_contra hqH
      cases q with
      | none =>
        have hdisj : Disjoint (pre H) F := Set.disjoint_left.mpr fun z hz hzF =>
          hqH ((collapseProj_eq_none_iff F z).mpr hzF ▸ hz)
        let O : Set (CollapseQuotient X F) :=
          { r | match r with | none => True | some y => y.1 ∈ HX F (pre H) }
        have hpreO : pre O = HX F (pre H) := by
          ext x
          simp only [pre, mem_preimage, O, mem_ofPred_eq]
          by_cases hxF : x ∈ F
          · rw [(collapseProj_eq_none_iff F x).mpr hxF]
            exact ⟨fun _ => hHX_sub F (pre H) hF hpreH hdisj.symm hxF, fun _ => trivial⟩
          · rw [(collapseProj_eq_some_iff F x ⟨x, hxF⟩).mpr rfl]
        have hO_open : IsOpen O := by
          rw [collapse_isOpen_iff]
          change IsOpen (pre O)
          rw [hpreO]
          exact hHX_open F (pre H) hF
        have hq0 : (none : CollapseQuotient X F) ∈ closure (GQ 0 H) := mem_iInter.mp hq 0
        rw [mem_closure_iff] at hq0
        obtain ⟨r, hrO, hrG⟩ := hq0 O hO_open trivial
        cases r with
        | none => exact hqH hrG
        | some y =>
          change y.1 ∈ satG 0 H at hrG
          dsimp only [satG] at hrG
          simp only [hqH, ↓reduceIte] at hrG
          exact Set.disjoint_left.mp (hHX_disj (pre H) F) hrG.2 hrO
      | some y =>
        have hy_not_pre : y.1 ∉ pre H := by
          change collapseProj F y.1 ∉ H
          rw [(collapseProj_eq_some_iff F y.1 y).mpr rfl]; exact hqH
        have hy_not : y.1 ∉ ⋂ n, closure (G' n (pre H)) := by
          rw [hG'_inter _ hpreH]; exact hy_not_pre
        rw [mem_iInter] at hy_not
        push Not at hy_not
        obtain ⟨n, hn⟩ := hy_not
        let O : Set (CollapseQuotient X F) :=
          { r | match r with | none => False | some z => z.1 ∉ closure (G' n (pre H)) }
        have hpreO : pre O = (closure (G' n (pre H)) ∪ F)ᶜ := by
          ext x
          simp only [pre, mem_preimage, O, mem_ofPred_eq, mem_compl_iff, mem_union, not_or]
          by_cases hxF : x ∈ F
          · rw [(collapseProj_eq_none_iff F x).mpr hxF]
            simp [hxF]
          · rw [(collapseProj_eq_some_iff F x ⟨x, hxF⟩).mpr rfl]
            simp [hxF]
        have hO_open : IsOpen O := by
          rw [collapse_isOpen_iff]
          change IsOpen (pre O)
          rw [hpreO]
          exact (isClosed_closure.union hF).isOpen_compl
        have hqn : some y ∈ closure (GQ n H) := mem_iInter.mp hq n
        rw [mem_closure_iff] at hqn
        obtain ⟨r, hrO, hrG⟩ := hqn O hO_open hn
        cases r with
        | none => exact hrO
        | some z =>
          change z.1 ∈ satG n H at hrG
          have hzG' : z.1 ∈ G' n (pre H) := by
            dsimp only [satG] at hrG
            split_ifs at hrG
            · exact hrG
            · exact hrG.1
          exact hrO (subset_closure hzG')
    · refine subset_iInter fun n q hqH => subset_closure ?_
      cases q with
      | none => exact hqH
      | some y =>
        have hypre : y.1 ∈ pre H := by
          change collapseProj F y.1 ∈ H
          rw [(collapseProj_eq_some_iff F y.1 y).mpr rfl]; exact hqH
        change y.1 ∈ satG n H
        dsimp only [satG]
        split_ifs with hnone
        · exact hG'_sub n _ hpreH hypre
        · have hdisj : Disjoint (pre H) F := Set.disjoint_left.mpr fun z hz hzF =>
            hnone ((collapseProj_eq_none_iff F z).mpr hzF ▸ hz)
          exact ⟨hG'_sub n _ hpreH hypre, hHX_sub _ _ hpreH hF hdisj hypre⟩
  · -- Monotonicity `H ⊆ K → GQ n H ⊆ GQ n K`
    intro n H K hH hK hHK q hq
    have hpreH : IsClosed (pre H) := (collapse_isClosed_iff F).mp hH
    have hpreK : IsClosed (pre K) := (collapse_isClosed_iff F).mp hK
    have hsub : pre H ⊆ pre K := preimage_mono hHK
    cases q with
    | none => exact hHK hq
    | some y =>
      change y.1 ∈ satG n K
      change y.1 ∈ satG n H at hq
      dsimp only [satG] at hq ⊢
      by_cases hnoneH : none ∈ H
      · have hnoneK : none ∈ K := hHK hnoneH
        simp only [hnoneH, hnoneK, ↓reduceIte] at hq ⊢
        exact hG'_mono n _ _ hpreH hpreK hsub hq
      · simp only [hnoneH, ↓reduceIte] at hq
        by_cases hnoneK : none ∈ K
        · simp only [hnoneK, ↓reduceIte]
          exact hG'_mono n _ _ hpreH hpreK hsub hq.1
        · simp only [hnoneK, ↓reduceIte]
          exact ⟨hG'_mono n _ _ hpreH hpreK hsub hq.1,
                 hHX_mono _ _ F hpreH hpreK hsub hq.2⟩

end Stratifiability

section ClosedOuterBases

/-- A closed set `F` has a single-layer CP open outer base in `X` iff `none` has
`Defs.D_0001.HasCPOuterBase none` in `CollapseQuotient X F`. -/
theorem collapseQuotient_hasCPOuterBase_iff {X : Type} [TopologicalSpace X]
    {F : Set X} (hF : IsClosed F) (hFne : F.Nonempty) :
    @Defs.D_0001.HasCPOuterBase (CollapseQuotient X F) (collapseTopology F) none ↔
      ∃ 𝓥 : Set (Set X),
        (∀ V ∈ 𝓥, IsOpen V ∧ F ⊆ V) ∧
        (∀ U : Set X, IsOpen U → F ⊆ U → ∃ V ∈ 𝓥, V ⊆ U) ∧
        MSpace.ClosurePreserving 𝓥 := by
  let : TopologicalSpace (CollapseQuotient X F) := collapseTopology F
  have hcont := collapseProj_continuous F
  have hcl := collapseProj_isClosedMap hF
  have hsurj := collapseProj_surjective hFne
  constructor
  · rintro ⟨𝓥, h𝓥o, h𝓥b, h𝓥cp⟩
    refine ⟨(fun W => collapseProj F ⁻¹' W) '' 𝓥, ?_, ?_, ?_⟩
    · rintro _ ⟨W, hW, rfl⟩
      refine ⟨(collapse_isOpen_iff F).mp (h𝓥o W hW).1, fun x hxF => ?_⟩
      change collapseProj F x ∈ W
      rw [(collapseProj_eq_none_iff F x).mpr hxF]
      exact (h𝓥o W hW).2
    · intro U hU hFU
      let UQ : Set (CollapseQuotient X F) :=
        { q | match q with | none => True | some y => y.1 ∈ U }
      have hpreUQ : collapseProj F ⁻¹' UQ = U := by
        ext x
        simp only [mem_preimage, UQ, mem_ofPred_eq]
        by_cases hxF : x ∈ F
        · rw [(collapseProj_eq_none_iff F x).mpr hxF]
          simp [hFU hxF]
        · rw [(collapseProj_eq_some_iff F x ⟨x, hxF⟩).mpr rfl]
      have hUQ_open : IsOpen UQ := by rw [collapse_isOpen_iff, hpreUQ]; exact hU
      obtain ⟨W, hW, hWUQ⟩ := h𝓥b UQ hUQ_open trivial
      refine ⟨collapseProj F ⁻¹' W, ⟨W, hW, rfl⟩, ?_⟩
      rw [← hpreUQ]
      exact preimage_mono hWUQ
    · intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro x hx
        by_cases hxF : x ∈ F
        · rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨S, hS𝓖⟩
          · simp at hx
          · obtain ⟨W, hW, rfl⟩ := h𝓖 hS𝓖
            refine ⟨closure (collapseProj F ⁻¹' W), mem_image_of_mem _ hS𝓖, subset_closure ?_⟩
            change collapseProj F x ∈ W
            rw [(collapseProj_eq_none_iff F x).mpr hxF]
            exact (h𝓥o W hW).2
        · let 𝓖Q : Set (Set (CollapseQuotient X F)) :=
            { W ∈ 𝓥 | collapseProj F ⁻¹' W ∈ 𝓖 }
          have hsub : ⋃₀ 𝓖 ⊆ collapseProj F ⁻¹' (⋃₀ 𝓖Q) := by
            rintro z ⟨S, hS𝓖, hzS⟩
            obtain ⟨W, hW, rfl⟩ := h𝓖 hS𝓖
            exact ⟨W, ⟨hW, hS𝓖⟩, hzS⟩
          have hxQ : collapseProj F x ∈ closure (⋃₀ 𝓖Q) :=
            hcont.closure_preimage_subset (⋃₀ 𝓖Q) (closure_mono hsub hx)
          rw [h𝓥cp 𝓖Q (fun W hW => hW.1)] at hxQ
          obtain ⟨_, ⟨W, ⟨_, hWG⟩, rfl⟩, hxW⟩ := hxQ
          refine ⟨closure (collapseProj F ⁻¹' W), mem_image_of_mem _ hWG, ?_⟩
          rw [mem_closure_iff]
          intro O hO hxO
          let OQ : Set (CollapseQuotient X F) :=
            { q | match q with | none => False | some y => y.1 ∈ O \ F }
          have hpreOQ : collapseProj F ⁻¹' OQ = O \ F := by
            ext z
            simp only [mem_preimage, OQ, mem_ofPred_eq, mem_sdiff]
            by_cases hzF : z ∈ F
            · rw [(collapseProj_eq_none_iff F z).mpr hzF]; simp [hzF]
            · rw [(collapseProj_eq_some_iff F z ⟨z, hzF⟩).mpr rfl]
          have hOQ_open : IsOpen OQ := by
            rw [collapse_isOpen_iff, hpreOQ]
            exact hO.sdiff hF
          have hxOQ : collapseProj F x ∈ OQ := by
            rw [(collapseProj_eq_some_iff F x ⟨x, hxF⟩).mpr rfl]
            exact ⟨hxO, hxF⟩
          rw [mem_closure_iff] at hxW
          obtain ⟨q, hqOQ, hqW⟩ := hxW OQ hOQ_open hxOQ
          cases q with
          | none => exact hqOQ.elim
          | some y =>
            refine ⟨y.1, hqOQ.1, ?_⟩
            change collapseProj F y.1 ∈ W
            rw [(collapseProj_eq_some_iff F y.1 y).mpr rfl]
            exact hqW
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  · rintro ⟨𝓥, h𝓥o, h𝓥b, h𝓥cp⟩
    let mkQ : Set X → Set (CollapseQuotient X F) := fun V =>
      { q | match q with | none => True | some y => y.1 ∈ V }
    have hpre_mkQ : ∀ V ∈ 𝓥, collapseProj F ⁻¹' mkQ V = V := by
      intro V hV
      ext x
      simp only [mem_preimage, mkQ, mem_ofPred_eq]
      by_cases hxF : x ∈ F
      · rw [(collapseProj_eq_none_iff F x).mpr hxF]
        simp [(h𝓥o V hV).2 hxF]
      · rw [(collapseProj_eq_some_iff F x ⟨x, hxF⟩).mpr rfl]
    refine ⟨mkQ '' 𝓥, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      exact ⟨(collapse_isOpen_iff F).mpr (by rw [hpre_mkQ V hV]; exact (h𝓥o V hV).1), trivial⟩
    · intro U hU hnoneU
      have hFU : F ⊆ collapseProj F ⁻¹' U := fun x hxF => by
        change collapseProj F x ∈ U
        rw [(collapseProj_eq_none_iff F x).mpr hxF]; exact hnoneU
      obtain ⟨V, hV, hVU⟩ := h𝓥b (collapseProj F ⁻¹' U) ((collapse_isOpen_iff F).mp hU) hFU
      refine ⟨mkQ V, ⟨V, hV, rfl⟩, fun q hq => ?_⟩
      cases q with
      | none => exact hnoneU
      | some y =>
        have hy : y.1 ∈ collapseProj F ⁻¹' U := hVU hq
        change collapseProj F y.1 ∈ U at hy
        rwa [(collapseProj_eq_some_iff F y.1 y).mpr rfl] at hy
    · intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro q hq
        cases q with
        | none =>
          rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨S, hS𝓖⟩
          · simp at hq
          · obtain ⟨V, _, rfl⟩ := h𝓖 hS𝓖
            exact ⟨closure (mkQ V), mem_image_of_mem _ hS𝓖, subset_closure trivial⟩
        | some y =>
          let 𝓖X : Set (Set X) := { V ∈ 𝓥 | mkQ V ∈ 𝓖 }
          have hy_cl : y.1 ∈ closure (⋃₀ 𝓖X) := by
            rw [mem_closure_iff]
            intro O hO hyO
            let OQ : Set (CollapseQuotient X F) :=
              { r | match r with | none => False | some z => z.1 ∈ O \ F }
            have hpreOQ : collapseProj F ⁻¹' OQ = O \ F := by
              ext z
              simp only [mem_preimage, OQ, mem_ofPred_eq, mem_sdiff]
              by_cases hzF : z ∈ F
              · rw [(collapseProj_eq_none_iff F z).mpr hzF]; simp [hzF]
              · rw [(collapseProj_eq_some_iff F z ⟨z, hzF⟩).mpr rfl]
            have hOQ_open : IsOpen OQ := by
              rw [collapse_isOpen_iff, hpreOQ]; exact hO.sdiff hF
            rw [mem_closure_iff] at hq
            obtain ⟨r, hrOQ, S, hS𝓖, hrS⟩ := hq OQ hOQ_open ⟨hyO, y.2⟩
            cases r with
            | none => exact hrOQ.elim
            | some z =>
              obtain ⟨V, hV, rfl⟩ := h𝓖 hS𝓖
              exact ⟨z.1, hrOQ.1, V, ⟨hV, hS𝓖⟩, hrS⟩
          rw [h𝓥cp 𝓖X (fun V hV => hV.1)] at hy_cl
          obtain ⟨_, ⟨V, ⟨hV, hVG⟩, rfl⟩, hyV⟩ := hy_cl
          refine ⟨closure (mkQ V), mem_image_of_mem _ hVG, ?_⟩
          have hsub : collapseProj F '' V ⊆ mkQ V := by
            rintro _ ⟨x, hxV, rfl⟩
            by_cases hxF : x ∈ F
            · rw [(collapseProj_eq_none_iff F x).mpr hxF]; trivial
            · rw [(collapseProj_eq_some_iff F x ⟨x, hxF⟩).mpr rfl]; exact hxV
          have hyimg : some y ∈ collapseProj F '' closure V :=
            ⟨y.1, hyV, (collapseProj_eq_some_iff F y.1 y).mpr rfl⟩
          exact closure_mono hsub (image_closure_subset_closure_image hcont hyimg)
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- **Closed-Set Outer Base Theorem from `¬ L_0020`:**
If `¬ Specs.L_0020.stmt` (every point of every stratifiable space has `HasCPOuterBase`),
then EVERY nonempty closed subset `F` of EVERY stratifiable space `X` admits a
single-layer CP open outer base! -/
theorem closed_hasCPOuterBase_of_not_L0020
    (hno20 : ¬ Specs.L_0020.stmt)
    {X : Type} [TopologicalSpace X] (hStrat : MSpace.IsStratifiable X)
    {F : Set X} (hF : IsClosed F) (hFne : F.Nonempty) :
    ∃ 𝓥 : Set (Set X),
      (∀ V ∈ 𝓥, IsOpen V ∧ F ⊆ V) ∧
      (∀ U : Set X, IsOpen U → F ⊆ U → ∃ V ∈ 𝓥, V ⊆ U) ∧
      MSpace.ClosurePreserving 𝓥 := by
  rw [← collapseQuotient_hasCPOuterBase_iff hF hFne]
  by_contra hno
  exact hno20 ⟨CollapseQuotient X F, collapseTopology F,
    collapseQuotient_isStratifiable hStrat hF, none, hno⟩

end ClosedOuterBases

end Research.CollapseQuotientTheorem
