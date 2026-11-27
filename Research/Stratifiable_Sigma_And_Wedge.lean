import Targets
import Defs.D_0001
import Defs.D_0010
import Proofs.L_0002
import Proofs.L_0003
import Proofs.L_0004

/-!
# Disjoint Sums (`Sigma`) and Arbitrary-Cardinality Pointed Wedges (`Wedge`)

This file establishes permanence theorems for `MSpace.IsStratifiable`, `MSpace.IsM1`,
and `Defs.D_0001.HasCPOuterBase` under arbitrary disjoint sums and arbitrary-cardinality
pointed wedges (generalizing the sequential fans `S_ω`, `S_{ω_1}`, `S_𝔠`):

1. `isStratifiable_sigma` & `isM1_sigma`:
   Arbitrary disjoint sums `Σ i : ι, X i` preserve `MSpace.IsStratifiable` and `MSpace.IsM1`.
2. `Wedge X x₀ := Option (Σ i : ι, { x : X i // x ≠ x₀ i })`:
   Arbitrary-cardinality pointed wedge gluing all basepoints `x₀ i` to `none`.
3. `wedge_isStratifiable`:
   For ANY index type `ι` (countable or uncountable) and ANY family of stratifiable
   spaces `(X i, x₀ i)`, `Wedge X x₀` is stratifiable (via Heath–Lutzer–Zenor monotone
   normality on each branch `X i`).
4. `wedge_hasCPOuterBase_iff`:
   `Defs.D_0001.HasCPOuterBase (none : Wedge X x₀) ↔ ∀ i, Defs.D_0001.HasCPOuterBase (x₀ i)`.
5. `wedge_isM1_of_isM1_and_hasCPOuterBase`:
   Whenever every `X i` is `M₁` and every `x₀ i` has `HasCPOuterBase (x₀ i)`,
   `Wedge X x₀` is `M₁` (in particular, all sequential fans `S_κ` are `M₁`).
-/

namespace Research.StratifiableSigmaWedge

open MSpace Set Topology

section DisjointSum

/-- Arbitrary disjoint sums preserve `MSpace.IsStratifiable`. -/
theorem isStratifiable_sigma {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (hStrat : ∀ i, MSpace.IsStratifiable (X i)) :
    MSpace.IsStratifiable (Σ i, X i) := by
  have hT1i : ∀ i, T1Space (X i) := fun i => (hStrat i).1
  have hT1 : T1Space (Σ i, X i) := ⟨fun p => by
    rw [← isOpen_compl_iff, isOpen_sigma_iff]
    intro i
    by_cases hi : i = p.1
    · subst hi
      have hEq : Sigma.mk p.1 ⁻¹' ({p} : Set (Σ j, X j))ᶜ = {p.2}ᶜ := by
        ext x; simp [Sigma.ext_iff]
      rw [hEq]; exact isClosed_singleton.isOpen_compl
    · have hEq : Sigma.mk i ⁻¹' ({p} : Set (Σ j, X j))ᶜ = univ := by
        ext x; simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
        intro h; exact hi (congrArg Sigma.fst h)
      rw [hEq]; exact isOpen_univ⟩
  have hGi_ex : ∀ i, ∃ G : ℕ → Set (X i) → Set (X i), MSpace.IsStratification G :=
    fun i => (hStrat i).2
  choose G hGo hGs hGi hGm using hGi_ex
  let GS : ℕ → Set (Σ i, X i) → Set (Σ i, X i) := fun n H =>
    { p | p.2 ∈ G p.1 n (Sigma.mk p.1 ⁻¹' H) }
  refine ⟨hT1, GS, ?_, ?_, ?_, ?_⟩
  · intro n H hH
    rw [isOpen_sigma_iff]
    intro i
    exact hGo i n _ (hH.preimage continuous_sigmaMk)
  · intro n H hH p hp
    exact hGs p.1 n _ (hH.preimage continuous_sigmaMk) hp
  · intro H hH
    apply Subset.antisymm
    · rintro ⟨i, x⟩ hx
      have hxi : x ∈ ⋂ n, closure (G i n (Sigma.mk i ⁻¹' H)) := by
        refine mem_iInter.mpr fun n => ?_
        have hxn : (⟨i, x⟩ : Σ j, X j) ∈ closure (GS n H) := mem_iInter.mp hx n
        rw [mem_closure_iff] at hxn ⊢
        intro U hU hxU
        have hOopen : IsOpen (Sigma.mk i '' U) := isOpenMap_sigmaMk U hU
        obtain ⟨q, ⟨y, hyU, rfl⟩, hqG⟩ := hxn _ hOopen ⟨x, hxU, rfl⟩
        exact ⟨y, hyU, hqG⟩
      rw [hGi i _ (hH.preimage continuous_sigmaMk)] at hxi
      exact hxi
    · exact subset_iInter fun n p hp =>
        subset_closure (hGs p.1 n _ (hH.preimage continuous_sigmaMk) hp)
  · intro n H K hH hK hHK p hp
    exact hGm p.1 n _ _ (hH.preimage continuous_sigmaMk) (hK.preimage continuous_sigmaMk)
      (preimage_mono hHK) hp

/-- Arbitrary disjoint sums preserve `MSpace.IsM1`. -/
theorem isM1_sigma {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (hM1 : ∀ i, MSpace.IsM1 (X i)) :
    MSpace.IsM1 (Σ i, X i) := by
  have hT3i : ∀ i, T3Space (X i) := fun i => (hM1 i).1
  have hT1 : T1Space (Σ i, X i) := ⟨fun p => by
    rw [← isOpen_compl_iff, isOpen_sigma_iff]
    intro i
    by_cases hi : i = p.1
    · subst hi
      have hEq : Sigma.mk p.1 ⁻¹' ({p} : Set (Σ j, X j))ᶜ = {p.2}ᶜ := by
        ext x; simp [Sigma.ext_iff]
      rw [hEq]; exact isClosed_singleton.isOpen_compl
    · have hEq : Sigma.mk i ⁻¹' ({p} : Set (Σ j, X j))ᶜ = univ := by
        ext x; simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
        intro h; exact hi (congrArg Sigma.fst h)
      rw [hEq]; exact isOpen_univ⟩
  have hReg : RegularSpace (Σ i, X i) := by
    refine RegularSpace.of_exists_mem_nhds_isClosed_subset fun p s hs => ?_
    obtain ⟨U, hUs, hUopen, hpU⟩ := mem_nhds_iff.mp hs
    have hUi : IsOpen (Sigma.mk p.1 ⁻¹' U) := hUopen.preimage continuous_sigmaMk
    obtain ⟨K, hKnhds, hKclosed, hKU⟩ := exists_mem_nhds_isClosed_subset (hUi.mem_nhds hpU)
    obtain ⟨V, hVK, hVopen, hpV⟩ := mem_nhds_iff.mp hKnhds
    refine ⟨Sigma.mk p.1 '' K,
      Filter.mem_of_superset ((isOpenMap_sigmaMk V hVopen).mem_nhds ⟨p.2, hpV, rfl⟩)
        (image_mono hVK),
      isClosedMap_sigmaMk K hKclosed, ?_⟩
    rintro _ ⟨y, hyK, rfl⟩
    exact hUs (hKU hyK)
  have hT3 : T3Space (Σ i, X i) := ⟨⟩
  have hbas_ex : ∀ i, ∃ 𝓑' : ℕ → Set (Set (X i)),
      TopologicalSpace.IsTopologicalBasis (⋃ n, 𝓑' n) ∧
      ∀ n, MSpace.ClosurePreserving (𝓑' n) := by
    intro i
    obtain ⟨𝓑, h𝓑bas, 𝓑', h𝓑'cp, rfl⟩ := (hM1 i).2
    exact ⟨𝓑', h𝓑bas, h𝓑'cp⟩
  choose 𝓑' h𝓑'bas h𝓑'cp using hbas_ex
  let 𝓛 : ℕ → Set (Set (Σ i, X i)) := fun n =>
    { S | ∃ i : ι, ∃ B ∈ 𝓑' i n, S = Sigma.mk i '' B }
  refine ⟨hT3, ⋃ n, 𝓛 n, ?_, ⟨𝓛, ?_, rfl⟩⟩
  · apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro S hS
      obtain ⟨n, i, B, hBin, rfl⟩ := by simpa [𝓛] using hS
      exact isOpenMap_sigmaMk B ((h𝓑'bas i).isOpen (mem_iUnion.mpr ⟨n, hBin⟩))
    · rintro ⟨i, x⟩ U hxU hUopen
      obtain ⟨B, hB, hxB, hBU⟩ :=
        (h𝓑'bas i).exists_subset_of_mem_open hxU (hUopen.preimage continuous_sigmaMk)
      obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
      refine ⟨Sigma.mk i '' B, mem_iUnion.mpr ⟨n, i, B, hBn, rfl⟩, ⟨x, hxB, rfl⟩, ?_⟩
      rintro _ ⟨y, hyB, rfl⟩; exact hBU hyB
  · intro n 𝓖 h𝓖
    apply Subset.antisymm
    · rintro ⟨i, x⟩ hx
      let 𝓖i : Set (Set (X i)) := { B ∈ 𝓑' i n | Sigma.mk i '' B ∈ 𝓖 }
      have hx_cl : x ∈ closure (⋃₀ 𝓖i) := by
        rw [mem_closure_iff]
        intro U hU hxU
        rw [mem_closure_iff] at hx
        obtain ⟨q, ⟨y, hyU, rfl⟩, S, hS𝓖, hyS⟩ := hx (Sigma.mk i '' U) (isOpenMap_sigmaMk U hU) ⟨x, hxU, rfl⟩
        obtain ⟨j, B, hBjn, rfl⟩ := h𝓖 hS𝓖
        obtain ⟨y', hy'B, heq⟩ := hyS
        cases heq
        exact ⟨y, hyU, B, ⟨hBjn, hS𝓖⟩, hy'B⟩
      rw [h𝓑'cp i n 𝓖i (fun B hB => hB.1)] at hx_cl
      obtain ⟨_, ⟨B, ⟨_, hBG⟩, rfl⟩, hxB⟩ := hx_cl
      refine ⟨closure (Sigma.mk i '' B), mem_image_of_mem _ hBG, ?_⟩
      exact image_closure_subset_closure_image continuous_sigmaMk ⟨x, hxB, rfl⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

end DisjointSum

section PointedWedge

open Classical

/-- Arbitrary-cardinality pointed wedge gluing all basepoints `x₀ i : X i` to `none`. -/
abbrev Wedge {ι : Type*} (X : ι → Type*) (x₀ : ∀ i, X i) : Type _ :=
  Option (Σ i : ι, { x : X i // x ≠ x₀ i })

/-- Extract the `i`-th branch subset `{ x : X i | ... }` of a set `S ⊆ Wedge X x₀`. -/
noncomputable def wedgeBranch {ι : Type*} {X : ι → Type*} {x₀ : ∀ i, X i}
    (S : Set (Wedge X x₀)) (i : ι) : Set (X i) :=
  { x | if h : x = x₀ i then none ∈ S else some ⟨i, ⟨x, h⟩⟩ ∈ S }

/-- The wedge topology on `Wedge X x₀`: `S` is open iff every branch `wedgeBranch S i`
is open in `X i`. -/
@[instance_reducible]
noncomputable def wedgeTopology {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    (x₀ : ∀ i, X i) : TopologicalSpace (Wedge X x₀) where
  IsOpen S := ∀ i : ι, IsOpen (wedgeBranch S i)
  isOpen_univ := fun i => by
    have hEq : wedgeBranch (univ : Set (Wedge X x₀)) i = univ := by
      ext x; simp [wedgeBranch]
    rw [hEq]; exact isOpen_univ
  isOpen_inter := fun S₁ S₂ h₁ h₂ i => by
    have hEq : wedgeBranch (S₁ ∩ S₂) i = wedgeBranch S₁ i ∩ wedgeBranch S₂ i := by
      ext x; simp only [wedgeBranch, mem_ofPred_eq, mem_inter_iff]; split_ifs <;> rfl
    rw [hEq]; exact (h₁ i).inter (h₂ i)
  isOpen_sUnion := fun 𝓢 h𝓢 i => by
    have hEq : wedgeBranch (⋃₀ 𝓢) i = ⋃ S ∈ 𝓢, wedgeBranch S i := by
      ext x; simp only [wedgeBranch, mem_ofPred_eq, mem_sUnion, mem_iUnion, exists_prop]; split_ifs <;> rfl
    rw [hEq]; exact isOpen_biUnion fun S hS => h𝓢 S hS i

theorem wedge_isOpen_iff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {x₀ : ∀ i, X i} {S : Set (Wedge X x₀)} :
    @IsOpen (Wedge X x₀) (wedgeTopology X x₀) S ↔ ∀ i, IsOpen (wedgeBranch S i) :=
  Iff.rfl

theorem wedge_isClosed_iff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {x₀ : ∀ i, X i} {S : Set (Wedge X x₀)} :
    @IsClosed (Wedge X x₀) (wedgeTopology X x₀) S ↔ ∀ i, IsClosed (wedgeBranch S i) := by
  let : TopologicalSpace (Wedge X x₀) := wedgeTopology X x₀
  rw [← isOpen_compl_iff, wedge_isOpen_iff]
  have hcompl : ∀ i, wedgeBranch Sᶜ i = (wedgeBranch S i)ᶜ := by
    intro i; ext x; simp only [wedgeBranch, mem_ofPred_eq, mem_compl_iff]; split_ifs <;> rfl
  simp_rw [hcompl, isOpen_compl_iff]

/-- Open embedding of a subset `U ⊆ X i \ {x₀ i}` into the `i`-th branch of `Wedge X x₀`. -/
def wedgeEmbed {ι : Type*} {X : ι → Type*} (x₀ : ∀ i, X i) (i : ι) (U : Set (X i)) :
    Set (Wedge X x₀) :=
  { q | ∃ x : { x : X i // x ≠ x₀ i }, x.1 ∈ U ∧ q = some ⟨i, x⟩ }

theorem wedgeEmbed_isOpen {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (x₀ : ∀ i, X i) (i : ι) {U : Set (X i)} (hU : IsOpen U) (hnot : x₀ i ∉ U) :
    @IsOpen (Wedge X x₀) (wedgeTopology X x₀) (wedgeEmbed x₀ i U) := by
  classical
  rw [wedge_isOpen_iff]
  intro j
  by_cases hij : j = i
  · subst hij
    have hEq : wedgeBranch (wedgeEmbed x₀ j U) j = U := by
      ext x
      simp only [wedgeBranch, wedgeEmbed, mem_ofPred_eq]
      split_ifs with hx
      · subst hx; simp [hnot]
      · constructor
        · rintro ⟨y, hyU, heq⟩; cases heq; exact hyU
        · intro hxU; exact ⟨⟨x, hx⟩, hxU, rfl⟩
    rw [hEq]; exact hU
  · have hEq : wedgeBranch (wedgeEmbed x₀ i U) j = ∅ := by
      ext x
      simp only [wedgeBranch, wedgeEmbed, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      split_ifs with hx
      · rintro ⟨_, _, h⟩; cases h
      · rintro ⟨y, _, heq⟩
        have h1 : (⟨i, y⟩ : Σ k, { z : X k // z ≠ x₀ k }) = ⟨j, ⟨x, hx⟩⟩ := Option.some.inj heq.symm
        exact hij (congrArg Sigma.fst h1).symm
    rw [hEq]; exact isOpen_empty

theorem wedge_t1Space {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, T1Space (X i)] (x₀ : ∀ i, X i) :
    @T1Space (Wedge X x₀) (wedgeTopology X x₀) := by
  let : TopologicalSpace (Wedge X x₀) := wedgeTopology X x₀
  refine ⟨fun q => ?_⟩
  rw [wedge_isClosed_iff]
  intro i
  cases q with
  | none =>
    have hEq : wedgeBranch ({none} : Set (Wedge X x₀)) i = {x₀ i} := by
      ext x; simp only [wedgeBranch, mem_ofPred_eq, mem_singleton_iff]
      split_ifs with hx
      · simp [hx]
      · simp [hx]
    rw [hEq]; exact isClosed_singleton
  | some p =>
    rcases p with ⟨j, y⟩
    by_cases hij : i = j
    · subst hij
      have hEq : wedgeBranch ({some ⟨i, y⟩} : Set (Wedge X x₀)) i = {y.1} := by
        ext x; simp only [wedgeBranch, mem_ofPred_eq, mem_singleton_iff]
        split_ifs with hx
        · subst hx; simp [y.2.symm]
        · constructor
          · intro h; cases h; rfl
          · intro h; congr 2; exact Subtype.ext h
      rw [hEq]; exact isClosed_singleton
    · have hEq : wedgeBranch ({some ⟨j, y⟩} : Set (Wedge X x₀)) i = ∅ := by
        ext x; simp only [wedgeBranch, mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false]
        split_ifs with hx
        · intro h; cases h
        · intro h
          have h1 : (⟨i, ⟨x, hx⟩⟩ : Σ k, { z : X k // z ≠ x₀ k }) = ⟨j, y⟩ := Option.some.inj h
          exact hij (congrArg Sigma.fst h1)
      rw [hEq]; exact isClosed_empty

/-- **Arbitrary-Cardinality Wedge Stratifiability Theorem:**
For ANY index type `ι` (countable or uncountable) and ANY family of stratifiable spaces
`(X i, x₀ i)`, the pointed wedge `Wedge X x₀` is stratifiable. -/
theorem wedge_isStratifiable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (hStrat : ∀ i, MSpace.IsStratifiable (X i)) (x₀ : ∀ i, X i) :
    @MSpace.IsStratifiable (Wedge X x₀) (wedgeTopology X x₀) := by
  classical
  have hT1i : ∀ i, T1Space (X i) := fun i => (hStrat i).1
  have hGi_ex : ∀ i, ∃ G : ℕ → Set (X i) → Set (X i), MSpace.IsStratification G :=
    fun i => (hStrat i).2
  choose G₀ hG₀_open hG₀_sub hG₀_inter hG₀_mono using hGi_ex
  -- Decreasing stratification `G' i n H := ⋂ j ≤ n, G₀ i j H` on each `X i`
  let G' : ∀ i, ℕ → Set (X i) → Set (X i) := fun i n H => ⋂ j ∈ Set.Iic n, G₀ i j H
  have hG'_open : ∀ i n H, IsClosed H → IsOpen (G' i n H) := fun i n H hH =>
    (Set.finite_Iic n).isOpen_biInter fun j _ => hG₀_open i j H hH
  have hG'_sub : ∀ i n H, IsClosed H → H ⊆ G' i n H := fun i n H hH x hx =>
    mem_iInter₂.mpr fun j _ => hG₀_sub i j H hH hx
  have hG'_anti : ∀ i {m n : ℕ}, m ≤ n → ∀ H, G' i n H ⊆ G' i m H := fun i _ _ hmn H x hx =>
    mem_iInter₂.mpr fun j hj => mem_iInter₂.mp hx j (le_trans hj hmn)
  have hG'_mono : ∀ i n H K, IsClosed H → IsClosed K → H ⊆ K → G' i n H ⊆ G' i n K :=
    fun i n H K hH hK hHK x hx =>
      mem_iInter₂.mpr fun j hj => hG₀_mono i j H K hH hK hHK (mem_iInter₂.mp hx j hj)
  have hG'_inter : ∀ i H, IsClosed H → (⋂ n, closure (G' i n H)) = H := by
    intro i H hH
    apply Subset.antisymm
    · intro x hx
      rw [← hG₀_inter i H hH]
      refine mem_iInter.mpr fun n => ?_
      have hsub : G' i n H ⊆ G₀ i n H := fun y hy => mem_iInter₂.mp hy n (Set.mem_Iic.mpr le_rfl)
      exact closure_mono hsub (mem_iInter.mp hx n)
    · exact subset_iInter fun n => (hG'_sub i n H hH).trans subset_closure
  -- Heath–Lutzer–Zenor monotone normality operator on each `X i`
  let Hi : ∀ i, Set (X i) → Set (X i) → Set (X i) := fun i A B =>
    ⋃ n : ℕ, G' i n A \ closure (G' i n B)
  have hHi_open : ∀ i A B, IsClosed A → IsOpen (Hi i A B) := fun i A B hA =>
    isOpen_iUnion fun n => (hG'_open i n A hA).sdiff isClosed_closure
  have hHi_sub : ∀ i A B, IsClosed A → IsClosed B → Disjoint A B → A ⊆ Hi i A B := by
    intro i A B hA hB hdisj x hxA
    have hxB : x ∉ B := Set.disjoint_left.mp hdisj hxA
    have hxnot : x ∉ ⋂ n, closure (G' i n B) := by rw [hG'_inter i B hB]; exact hxB
    rw [mem_iInter] at hxnot
    push Not at hxnot
    obtain ⟨n, hn⟩ := hxnot
    exact mem_iUnion.mpr ⟨n, hG'_sub i n A hA hxA, hn⟩
  have hHi_disj : ∀ i A B, Disjoint (Hi i A B) (Hi i B A) := by
    intro i A B
    rw [Set.disjoint_left]
    intro x hxAB hxBA
    obtain ⟨n, hnA, hnB⟩ := mem_iUnion.mp hxAB
    obtain ⟨m, hmB, hmA⟩ := mem_iUnion.mp hxBA
    rcases le_total n m with hnm | hmn
    · exact hnB (subset_closure (hG'_anti i hnm B hmB))
    · exact hmA (subset_closure (hG'_anti i hmn A hnA))
  have hHi_mono : ∀ i A₁ A₂ B, IsClosed A₁ → IsClosed A₂ → A₁ ⊆ A₂ → Hi i A₁ B ⊆ Hi i A₂ B := by
    intro i A₁ A₂ B hA₁ hA₂ h12 x hx
    obtain ⟨n, hn1, hnB⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, hG'_mono i n A₁ A₂ hA₁ hA₂ h12 hn1, hnB⟩
  -- Build stratification `GW` on `Wedge X x₀`
  let : TopologicalSpace (Wedge X x₀) := wedgeTopology X x₀
  have hT1W : T1Space (Wedge X x₀) := wedge_t1Space x₀
  let branchG : ℕ → Set (Wedge X x₀) → ∀ i, Set (X i) := fun n H i =>
    if none ∈ H then G' i n (wedgeBranch H i)
    else G' i n (wedgeBranch H i) ∩ Hi i (wedgeBranch H i) {x₀ i}
  let GW : ℕ → Set (Wedge X x₀) → Set (Wedge X x₀) := fun n H =>
    { q | match q with | none => none ∈ H | some p => p.2.1 ∈ branchG n H p.1 }
  have hbranch_GW : ∀ n H, IsClosed H → ∀ i, wedgeBranch (GW n H) i = branchG n H i := by
    intro n H hH i
    have hHi_cl : IsClosed (wedgeBranch H i) := (wedge_isClosed_iff.mp hH) i
    ext x
    simp only [wedgeBranch, GW, mem_ofPred_eq]
    by_cases hx : x = x₀ i
    · subst hx
      simp only [↓reduceDIte, branchG]
      by_cases hnone : none ∈ H
      · simp only [hnone, ↓reduceIte, true_iff]
        have hxH : x₀ i ∈ wedgeBranch H i := by simp [wedgeBranch, hnone]
        exact hG'_sub i n _ hHi_cl hxH
      · simp only [hnone, ↓reduceIte, false_iff]
        intro h
        have hxnot : x₀ i ∉ wedgeBranch H i := by simp [wedgeBranch, hnone]
        have hxH0 : x₀ i ∈ Hi i {x₀ i} (wedgeBranch H i) :=
          hHi_sub i {x₀ i} (wedgeBranch H i) isClosed_singleton hHi_cl
            (Set.disjoint_singleton_left.mpr hxnot) rfl
        exact Set.disjoint_left.mp (hHi_disj i (wedgeBranch H i) {x₀ i}) h.2 hxH0
    · simp only [hx, ↓reduceDIte]
  refine ⟨hT1W, GW, ?_, ?_, ?_, ?_⟩
  · intro n H hH
    rw [wedge_isOpen_iff]
    intro i
    rw [hbranch_GW n H hH i]
    have hHi_cl : IsClosed (wedgeBranch H i) := (wedge_isClosed_iff.mp hH) i
    dsimp only [branchG]
    split_ifs
    · exact hG'_open i n _ hHi_cl
    · exact (hG'_open i n _ hHi_cl).inter (hHi_open i _ _ hHi_cl)
  · intro n H hH q hqH
    cases q with
    | none => exact hqH
    | some p =>
      rcases p with ⟨i, y⟩
      have hHi_cl : IsClosed (wedgeBranch H i) := (wedge_isClosed_iff.mp hH) i
      have hyH : y.1 ∈ wedgeBranch H i := by simp [wedgeBranch, y.2, hqH]
      change y.1 ∈ branchG n H i
      dsimp only [branchG]
      split_ifs with hnone
      · exact hG'_sub i n _ hHi_cl hyH
      · have hxnot : x₀ i ∉ wedgeBranch H i := by simp [wedgeBranch, hnone]
        exact ⟨hG'_sub i n _ hHi_cl hyH,
          hHi_sub i _ _ hHi_cl isClosed_singleton (Set.disjoint_singleton_right.mpr hxnot) hyH⟩
  · intro H hH
    apply Subset.antisymm
    · intro q hq
      by_contra hqH
      cases q with
      | none =>
        let O : Set (Wedge X x₀) :=
          { r | match r with | none => True | some p => p.2.1 ∈ Hi p.1 {x₀ p.1} (wedgeBranch H p.1) }
        have hO_open : IsOpen O := by
          rw [wedge_isOpen_iff]
          intro i
          have hHi_cl : IsClosed (wedgeBranch H i) := (wedge_isClosed_iff.mp hH) i
          have hxnot : x₀ i ∉ wedgeBranch H i := by simp [wedgeBranch, hqH]
          have hEq : wedgeBranch O i = Hi i {x₀ i} (wedgeBranch H i) := by
            ext x
            simp only [wedgeBranch, O, mem_ofPred_eq]
            split_ifs with hx
            · subst hx
              exact ⟨fun _ => hHi_sub i {x₀ i} _ isClosed_singleton hHi_cl
                (Set.disjoint_singleton_left.mpr hxnot) rfl, fun _ => trivial⟩
            · rfl
          rw [hEq]
          exact hHi_open i _ _ isClosed_singleton
        have hq0 : (none : Wedge X x₀) ∈ closure (GW 0 H) := mem_iInter.mp hq 0
        rw [mem_closure_iff] at hq0
        obtain ⟨r, hrO, hrG⟩ := hq0 O hO_open trivial
        cases r with
        | none => exact hqH hrG
        | some p =>
          change p.2.1 ∈ branchG 0 H p.1 at hrG
          dsimp only [branchG] at hrG
          simp only [hqH, ↓reduceIte] at hrG
          exact Set.disjoint_left.mp (hHi_disj p.1 (wedgeBranch H p.1) {x₀ p.1}) hrG.2 hrO
      | some p =>
        rcases p with ⟨i, y⟩
        have hHi_cl : IsClosed (wedgeBranch H i) := (wedge_isClosed_iff.mp hH) i
        have hy_not : y.1 ∉ wedgeBranch H i := by simp [wedgeBranch, y.2, hqH]
        have hy_not_i : y.1 ∉ ⋂ n, closure (G' i n (wedgeBranch H i)) := by
          rw [hG'_inter i _ hHi_cl]; exact hy_not
        rw [mem_iInter] at hy_not_i
        push Not at hy_not_i
        obtain ⟨n, hn⟩ := hy_not_i
        let U : Set (X i) := (closure (G' i n (wedgeBranch H i)) ∪ {x₀ i})ᶜ
        have hU_open : IsOpen U := (isClosed_closure.union isClosed_singleton).isOpen_compl
        have hU_not : x₀ i ∉ U := fun h => h (Or.inr rfl)
        have hqn : some ⟨i, y⟩ ∈ closure (GW n H) := mem_iInter.mp hq n
        rw [mem_closure_iff] at hqn
        obtain ⟨r, ⟨z, hzU, rfl⟩, hzG⟩ :=
          hqn (wedgeEmbed x₀ i U) (wedgeEmbed_isOpen x₀ i hU_open hU_not)
            ⟨y, fun h => h.elim hn y.2, rfl⟩
        change z.1 ∈ branchG n H i at hzG
        have hzG' : z.1 ∈ G' i n (wedgeBranch H i) := by
          dsimp only [branchG] at hzG
          split_ifs at hzG
          · exact hzG
          · exact hzG.1
        exact hzU (Or.inl (subset_closure hzG'))
    · refine subset_iInter fun n q hqH => subset_closure ?_
      cases q with
      | none => exact hqH
      | some p =>
        rcases p with ⟨i, y⟩
        have hHi_cl : IsClosed (wedgeBranch H i) := (wedge_isClosed_iff.mp hH) i
        have hyH : y.1 ∈ wedgeBranch H i := by simp [wedgeBranch, y.2, hqH]
        change y.1 ∈ branchG n H i
        dsimp only [branchG]
        split_ifs with hnone
        · exact hG'_sub i n _ hHi_cl hyH
        · have hxnot : x₀ i ∉ wedgeBranch H i := by simp [wedgeBranch, hnone]
          exact ⟨hG'_sub i n _ hHi_cl hyH,
            hHi_sub i _ _ hHi_cl isClosed_singleton (Set.disjoint_singleton_right.mpr hxnot) hyH⟩
  · intro n H K hH hK hHK q hq
    cases q with
    | none => exact hHK hq
    | some p =>
      rcases p with ⟨i, y⟩
      have hHi_cl : IsClosed (wedgeBranch H i) := (wedge_isClosed_iff.mp hH) i
      have hKi_cl : IsClosed (wedgeBranch K i) := (wedge_isClosed_iff.mp hK) i
      have hsub : wedgeBranch H i ⊆ wedgeBranch K i := by
        intro x hx; simp only [wedgeBranch, mem_ofPred_eq] at hx ⊢
        split_ifs at hx ⊢ <;> exact hHK hx
      change y.1 ∈ branchG n K i
      change y.1 ∈ branchG n H i at hq
      dsimp only [branchG] at hq ⊢
      by_cases hnoneH : none ∈ H
      · have hnoneK : none ∈ K := hHK hnoneH
        simp only [hnoneH, hnoneK, ↓reduceIte] at hq ⊢
        exact hG'_mono i n _ _ hHi_cl hKi_cl hsub hq
      · simp only [hnoneH, ↓reduceIte] at hq
        by_cases hnoneK : none ∈ K
        · simp only [hnoneK, ↓reduceIte]
          exact hG'_mono i n _ _ hHi_cl hKi_cl hsub hq.1
        · simp only [hnoneK, ↓reduceIte]
          exact ⟨hG'_mono i n _ _ hHi_cl hKi_cl hsub hq.1,
                 hHi_mono i _ _ {x₀ i} hHi_cl hKi_cl hsub hq.2⟩

/-- **Exact Characterization of `HasCPOuterBase` at the Wedge Point:**
For ANY index type `ι` and ANY family of `T1` spaces `(X i, x₀ i)`,
`HasCPOuterBase (none : Wedge X x₀) ↔ ∀ i, HasCPOuterBase (x₀ i)`. -/
theorem wedge_hasCPOuterBase_iff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, T1Space (X i)] (x₀ : ∀ i, X i) :
    @Defs.D_0001.HasCPOuterBase (Wedge X x₀) (wedgeTopology X x₀) none ↔
      ∀ i, Defs.D_0001.HasCPOuterBase (x₀ i) := by
  let : TopologicalSpace (Wedge X x₀) := wedgeTopology X x₀
  constructor
  · rintro ⟨𝓥, h𝓥o, h𝓥b, h𝓥cp⟩ i
    refine ⟨(fun V => wedgeBranch V i) '' 𝓥, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      exact ⟨(wedge_isOpen_iff.mp (h𝓥o V hV).1) i, by simp [wedgeBranch, (h𝓥o V hV).2]⟩
    · intro U hU hx₀U
      let UW : Set (Wedge X x₀) :=
        { q | match q with | none => True | some p => if h : p.1 = i then (h ▸ p.2.1) ∈ U else True }
      have hUW_open : IsOpen UW := by
        rw [wedge_isOpen_iff]
        intro j
        by_cases hij : j = i
        · subst hij
          have hEq : wedgeBranch UW j = U := by
            ext x; simp only [wedgeBranch, UW, mem_ofPred_eq]
            split_ifs with hx
            · subst hx; simp [hx₀U]
            · simp
          rw [hEq]; exact hU
        · have hEq : wedgeBranch UW j = univ := by
            ext x; simp only [wedgeBranch, UW, mem_ofPred_eq, mem_univ, iff_true]
            split_ifs
          rw [hEq]; exact isOpen_univ
      obtain ⟨V, hV, hVUW⟩ := h𝓥b UW hUW_open trivial
      refine ⟨wedgeBranch V i, ⟨V, hV, rfl⟩, fun x hx => ?_⟩
      by_cases hx0 : x = x₀ i
      · exact hx0 ▸ hx₀U
      · simp only [wedgeBranch, mem_ofPred_eq, hx0, ↓reduceDIte] at hx
        have hmem := hVUW hx
        simpa [UW] using hmem
    · intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro x hx
        by_cases hx0 : x = x₀ i
        · subst hx0
          rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨S, hS𝓖⟩
          · simp at hx
          · obtain ⟨V, hV, rfl⟩ := h𝓖 hS𝓖
            exact ⟨closure (wedgeBranch V i), mem_image_of_mem _ hS𝓖,
              subset_closure (by simp [wedgeBranch, (h𝓥o V hV).2])⟩
        · let 𝓖W : Set (Set (Wedge X x₀)) := { V ∈ 𝓥 | wedgeBranch V i ∈ 𝓖 }
          have hxW : some ⟨i, ⟨x, hx0⟩⟩ ∈ closure (⋃₀ 𝓖W) := by
            rw [mem_closure_iff]
            intro O hO hxO
            have hOi : IsOpen (wedgeBranch O i) := (wedge_isOpen_iff.mp hO) i
            have hxOi : x ∈ wedgeBranch O i := by simp [wedgeBranch, hx0, hxO]
            rw [mem_closure_iff] at hx
            obtain ⟨y, hyO, S, hS𝓖, hyS⟩ := hx (wedgeBranch O i \ {x₀ i})
              (hOi.sdiff isClosed_singleton) ⟨hxOi, hx0⟩
            obtain ⟨V, hV, rfl⟩ := h𝓖 hS𝓖
            have hy0 : y ≠ x₀ i := hyO.2
            have hyO' : some ⟨i, ⟨y, hy0⟩⟩ ∈ O := by simpa [wedgeBranch, hy0] using hyO.1
            have hyV' : some ⟨i, ⟨y, hy0⟩⟩ ∈ V := by simpa [wedgeBranch, hy0] using hyS
            exact ⟨some ⟨i, ⟨y, hy0⟩⟩, hyO', V, ⟨hV, hS𝓖⟩, hyV'⟩
          rw [h𝓥cp 𝓖W (fun V hV => hV.1)] at hxW
          obtain ⟨_, ⟨V, ⟨_, hVG⟩, rfl⟩, hxV⟩ := hxW
          refine ⟨closure (wedgeBranch V i), mem_image_of_mem _ hVG, ?_⟩
          rw [mem_closure_iff]
          intro U hU hxU
          let U' : Set (X i) := U \ {x₀ i}
          rw [mem_closure_iff] at hxV
          obtain ⟨q, ⟨z, hzU', rfl⟩, hzV⟩ :=
            hxV (wedgeEmbed x₀ i U') (wedgeEmbed_isOpen x₀ i (hU.sdiff isClosed_singleton) (fun h => h.2 rfl))
              ⟨⟨x, hx0⟩, ⟨hxU, hx0⟩, rfl⟩
          exact ⟨z.1, hzU'.1, by simpa [wedgeBranch, z.2] using hzV⟩
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  · intro hall
    choose 𝓥 h𝓥o h𝓥b h𝓥cp using hall
    let mkW : (∀ i, Set (X i)) → Set (Wedge X x₀) := fun φ =>
      { q | match q with | none => True | some p => p.2.1 ∈ φ p.1 }
    refine ⟨{ S | ∃ φ : ∀ i, Set (X i), (∀ i, φ i ∈ 𝓥 i) ∧ S = mkW φ }, ?_, ?_, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩
      refine ⟨wedge_isOpen_iff.mpr fun i => ?_, trivial⟩
      have hEq : wedgeBranch (mkW φ) i = φ i := by
        ext x; simp only [wedgeBranch, mkW, mem_ofPred_eq]
        split_ifs with hx
        · subst hx; simp [(h𝓥o i (φ i) (hφ i)).2]
        · rfl
      rw [hEq]; exact (h𝓥o i (φ i) (hφ i)).1
    · intro U hU hnoneU
      have hφ_ex : ∀ i, ∃ V ∈ 𝓥 i, V ⊆ wedgeBranch U i := fun i =>
        h𝓥b i (wedgeBranch U i) ((wedge_isOpen_iff.mp hU) i) (by simp [wedgeBranch, hnoneU])
      choose φ hφ hφsub using hφ_ex
      refine ⟨mkW φ, ⟨φ, hφ, rfl⟩, fun q hq => ?_⟩
      cases q with
      | none => exact hnoneU
      | some p =>
        have hp := hφsub p.1 hq
        simpa [wedgeBranch, p.2.2] using hp
    · intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro q hq
        cases q with
        | none =>
          rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨S, hS𝓖⟩
          · simp at hq
          · obtain ⟨φ, _, rfl⟩ := h𝓖 hS𝓖
            exact ⟨closure (mkW φ), mem_image_of_mem _ hS𝓖, subset_closure trivial⟩
        | some p =>
          rcases p with ⟨i, y⟩
          let 𝓖i : Set (Set (X i)) :=
            { V ∈ 𝓥 i | ∃ φ : ∀ j, Set (X j), (∀ j, φ j ∈ 𝓥 j) ∧ φ i = V ∧ mkW φ ∈ 𝓖 }
          have hy_cl : y.1 ∈ closure (⋃₀ 𝓖i) := by
            rw [mem_closure_iff]
            intro U hU hyU
            let U' : Set (X i) := U \ {x₀ i}
            rw [mem_closure_iff] at hq
            obtain ⟨r, ⟨z, hzU', rfl⟩, S, hS𝓖, hzS⟩ :=
              hq (wedgeEmbed x₀ i U')
                (wedgeEmbed_isOpen x₀ i (hU.sdiff isClosed_singleton) (fun h => h.2 rfl))
                ⟨y, ⟨hyU, y.2⟩, rfl⟩
            obtain ⟨φ, hφ, rfl⟩ := h𝓖 hS𝓖
            exact ⟨z.1, hzU'.1, φ i, ⟨hφ i, φ, hφ, rfl, hS𝓖⟩, hzS⟩
          rw [h𝓥cp i 𝓖i (fun V hV => hV.1)] at hy_cl
          obtain ⟨_, ⟨V, ⟨_, φ, _, rfl, hSG⟩, rfl⟩, hyV⟩ := hy_cl
          refine ⟨closure (mkW φ), mem_image_of_mem _ hSG, ?_⟩
          rw [mem_closure_iff]
          intro O hO hyO
          have hOi : IsOpen (wedgeBranch O i) := (wedge_isOpen_iff.mp hO) i
          have hyOi : y.1 ∈ wedgeBranch O i := by simp [wedgeBranch, y.2, hyO]
          rw [mem_closure_iff] at hyV
          obtain ⟨z, hzO, hzφ⟩ := hyV (wedgeBranch O i \ {x₀ i})
            (hOi.sdiff isClosed_singleton) ⟨hyOi, y.2⟩
          have hzO1 : some ⟨i, ⟨z, hzO.2⟩⟩ ∈ O := by
            have h := hzO.1
            simp only [wedgeBranch, mem_ofPred_eq] at h
            split_ifs at h with hEq
            · exact (hzO.2 hEq).elim
            · exact h
          exact ⟨some ⟨i, ⟨z, hzO.2⟩⟩, hzO1, hzφ⟩
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- **Arbitrary-Cardinality Wedge `M₁` Theorem:**
If every `X i` is `M₁` and every `x₀ i` has `HasCPOuterBase (x₀ i)`, then `Wedge X x₀` is `M₁`.
In particular, sequential fans `S_κ` of EVERY cardinality `κ` are `M₁`. -/
theorem wedge_isM1_of_isM1_and_hasCPOuterBase
    {ι : Type} {X : ι → Type} [∀ i, TopologicalSpace (X i)]
    (hM1 : ∀ i, MSpace.IsM1 (X i)) (x₀ : ∀ i, X i)
    (hcp : ∀ i, Defs.D_0001.HasCPOuterBase (x₀ i)) :
    @MSpace.IsM1 (Wedge X x₀) (wedgeTopology X x₀) := by
  have hT3i : ∀ i, T3Space (X i) := fun i => (hM1 i).1
  have hStrat : ∀ i, MSpace.IsStratifiable (X i) := fun i =>
    (Proofs.L_0004.main (X i)).mp (Proofs.L_0003.main (X i) (Proofs.L_0002.main (X i) (hM1 i)))
  let : TopologicalSpace (Wedge X x₀) := wedgeTopology X x₀
  have hStratW : MSpace.IsStratifiable (Wedge X x₀) := wedge_isStratifiable hStrat x₀
  have hT3W : T3Space (Wedge X x₀) := ((Proofs.L_0004.main (Wedge X x₀)).mpr hStratW).1
  obtain ⟨𝓥none, h𝓥o, h𝓥b, h𝓥cp⟩ := (wedge_hasCPOuterBase_iff x₀).mpr hcp
  have hbas_ex : ∀ i, ∃ 𝓑' : ℕ → Set (Set (X i)),
      TopologicalSpace.IsTopologicalBasis (⋃ n, 𝓑' n) ∧
      ∀ n, MSpace.ClosurePreserving (𝓑' n) := by
    intro i
    obtain ⟨𝓑, h𝓑bas, 𝓑', h𝓑'cp, rfl⟩ := (hM1 i).2
    exact ⟨𝓑', h𝓑bas, h𝓑'cp⟩
  choose 𝓑' h𝓑'bas h𝓑'cp using hbas_ex
  let 𝓛 : ℕ → Set (Set (Wedge X x₀)) := fun n =>
    match n with
    | 0 => 𝓥none
    | m + 1 => { S | ∃ i : ι, ∃ B ∈ 𝓑' i m, x₀ i ∉ closure B ∧ S = wedgeEmbed x₀ i B }
  refine ⟨hT3W, ⋃ n, 𝓛 n, ?_, ⟨𝓛, ?_, rfl⟩⟩
  · apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro S hS
      obtain ⟨n, hSn⟩ := mem_iUnion.mp hS
      cases n with
      | zero => exact (h𝓥o S hSn).1
      | succ m =>
        obtain ⟨i, B, hBim, hnotcl, rfl⟩ := hSn
        exact wedgeEmbed_isOpen x₀ i ((h𝓑'bas i).isOpen (mem_iUnion.mpr ⟨m, hBim⟩))
          (fun h => hnotcl (subset_closure h))
    · intro q U hqU hUopen
      cases q with
      | none =>
        obtain ⟨V, hV, hVU⟩ := h𝓥b U hUopen hqU
        exact ⟨V, mem_iUnion.mpr ⟨0, hV⟩, (h𝓥o V hV).2, hVU⟩
      | some p =>
        rcases p with ⟨i, y⟩
        have hUi : IsOpen (wedgeBranch U i \ {x₀ i}) :=
          ((wedge_isOpen_iff.mp hUopen) i).sdiff isClosed_singleton
        have hyUi : y.1 ∈ wedgeBranch U i \ {x₀ i} := ⟨by simp [wedgeBranch, y.2, hqU], y.2⟩
        obtain ⟨K, hKnhds, hKclosed, hKU⟩ := exists_mem_nhds_isClosed_subset (hUi.mem_nhds hyUi)
        obtain ⟨B, hB, hyB, hBK⟩ :=
          (h𝓑'bas i).exists_subset_of_mem_open (mem_interior_iff_mem_nhds.mpr hKnhds) isOpen_interior
        obtain ⟨m, hBm⟩ := mem_iUnion.mp hB
        have hnotcl : x₀ i ∉ closure B := fun h =>
          (hKU (closure_minimal (hBK.trans interior_subset) hKclosed h)).2 rfl
        refine ⟨wedgeEmbed x₀ i B, mem_iUnion.mpr ⟨m + 1, i, B, hBm, hnotcl, rfl⟩,
          ⟨y, hyB, rfl⟩, ?_⟩
        rintro _ ⟨z, hzB, rfl⟩
        have hzU : z.1 ∈ wedgeBranch U i := (hKU (hBK.trans interior_subset hzB)).1
        simpa [wedgeBranch, z.2] using hzU
  · intro n
    cases n with
    | zero => exact h𝓥cp
    | succ m =>
      intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro q hq
        cases q with
        | none =>
          -- Every `B` in `𝓖` has `x₀ i ∉ closure B`, so `⋃_{B ∈ 𝓖_i} closure B` is closed and avoids `x₀ i`!
          let O : Set (Wedge X x₀) :=
            { r | match r with
                  | none => True
                  | some p => p.2.1 ∉ closure (⋃₀ { B ∈ 𝓑' p.1 m | x₀ p.1 ∉ closure B ∧ wedgeEmbed x₀ p.1 B ∈ 𝓖 }) }
          have hO_open : IsOpen O := by
            rw [wedge_isOpen_iff]
            intro i
            let 𝓖i : Set (Set (X i)) := { B ∈ 𝓑' i m | x₀ i ∉ closure B ∧ wedgeEmbed x₀ i B ∈ 𝓖 }
            have hx₀_not : x₀ i ∉ closure (⋃₀ 𝓖i) := by
              rw [h𝓑'cp i m 𝓖i (fun B hB => hB.1)]
              rintro ⟨_, ⟨B, ⟨_, hnotcl, _⟩, rfl⟩, hxB⟩
              exact hnotcl hxB
            have hEq : wedgeBranch O i = (closure (⋃₀ 𝓖i))ᶜ := by
              ext x; simp only [wedgeBranch, O, mem_ofPred_eq, mem_compl_iff]
              split_ifs with hx
              · subst hx; simp [hx₀_not]
              · rfl
            rw [hEq]; exact isClosed_closure.isOpen_compl
          rw [mem_closure_iff] at hq
          obtain ⟨r, hrO, S, hS𝓖, hrS⟩ := hq O hO_open trivial
          obtain ⟨i, B, hBim, hnotcl, rfl⟩ := h𝓖 hS𝓖
          obtain ⟨z, hzB, rfl⟩ := hrS
          exact (hrO (subset_closure ⟨B, ⟨hBim, hnotcl, hS𝓖⟩, hzB⟩)).elim
        | some p =>
          rcases p with ⟨i, y⟩
          let 𝓖i : Set (Set (X i)) := { B ∈ 𝓑' i m | x₀ i ∉ closure B ∧ wedgeEmbed x₀ i B ∈ 𝓖 }
          have hy_cl : y.1 ∈ closure (⋃₀ 𝓖i) := by
            rw [mem_closure_iff]
            intro U hU hyU
            let U' : Set (X i) := U \ {x₀ i}
            rw [mem_closure_iff] at hq
            obtain ⟨r, ⟨z, hzU', rfl⟩, S, hS𝓖, hzS⟩ :=
              hq (wedgeEmbed x₀ i U')
                (wedgeEmbed_isOpen x₀ i (hU.sdiff isClosed_singleton) (fun h => h.2 rfl))
                ⟨y, ⟨hyU, y.2⟩, rfl⟩
            obtain ⟨j, B, hBjm, hnotcl, rfl⟩ := h𝓖 hS𝓖
            obtain ⟨z', hz'B, heq⟩ := hzS
            have hji : j = i := congrArg Sigma.fst (Option.some.inj heq).symm
            subst hji
            cases heq
            exact ⟨z'.1, hzU'.1, B, ⟨hBjm, hnotcl, hS𝓖⟩, hz'B⟩
          rw [h𝓑'cp i m 𝓖i (fun B hB => hB.1)] at hy_cl
          obtain ⟨_, ⟨B, ⟨_, _, hBG⟩, rfl⟩, hyB⟩ := hy_cl
          refine ⟨closure (wedgeEmbed x₀ i B), mem_image_of_mem _ hBG, ?_⟩
          rw [mem_closure_iff]
          intro O hO hyO
          have hOi : IsOpen (wedgeBranch O i) := (wedge_isOpen_iff.mp hO) i
          have hyOi : y.1 ∈ wedgeBranch O i := by simp [wedgeBranch, y.2, hyO]
          rw [mem_closure_iff] at hyB
          obtain ⟨z, hzO, hzB⟩ := hyB (wedgeBranch O i \ {x₀ i})
            (hOi.sdiff isClosed_singleton) ⟨hyOi, y.2⟩
          have hzO1 : some ⟨i, ⟨z, hzO.2⟩⟩ ∈ O := by
            have h := hzO.1
            simp only [wedgeBranch, mem_ofPred_eq] at h
            split_ifs at h with hEq
            · exact (hzO.2 hEq).elim
            · exact h
          exact ⟨some ⟨i, ⟨z, hzO.2⟩⟩, hzO1, ⟨z, hzO.2⟩, hzB, rfl⟩
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

end PointedWedge

end Research.StratifiableSigmaWedge
