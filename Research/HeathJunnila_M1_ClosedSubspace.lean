import Targets
import Proofs.L_0002
import Proofs.L_0003
import Proofs.L_0004
import Proofs.L_0008

/-!
# Heath–Junnila (1981): Every `M₂` / `M₃` Space Embeds as a Closed Subspace of an `M₁` Space

This file formalizes the classic theorem of Heath & Junnila (Proc. AMS 83, 1981)
and its exact equivalence with Ceder's 1961 open problem `Tinf` (`M₃ ⇒ M₁`):

1. `HeathJunnila X := X × Option ℕ` equipped with `heathJunnilaTopology X`:
   * Every `(x, some n)` is isolated.
   * Basic open neighborhoods of `(x, none)` are
     `B(U, N) := (U × {none}) ∪ { (y, some n) | y ∈ U ∧ N ≤ n }` (`U` open in `X`, `x ∈ U`).
2. `heathJunnila_t3Space`: `T3Space X → T3Space (HeathJunnila X)`.
3. `heathJunnila_isM1`: **Every `M₂` space `X` (and hence every `M₃` / stratifiable space `X`)
   yields an `M₁` space `HeathJunnila X`!**
4. `heathJunnila_isClosedEmbedding`: `x ↦ (x, none)` is a closed topological embedding of `X`
   into `HeathJunnila X`.
5. `Tinf_iff_closed_subspace_M1`:
   `MSpace.Goals.Tinf_M3_imp_M1 ↔ ∀ (Z : Type) [TopologicalSpace Z], MSpace.IsM1 Z → ∀ F : Set Z, IsClosed F → MSpace.IsM1 ↥F`.
-/

namespace Research.HeathJunnilaTheorem

open MSpace Set Topology

section HeathJunnilaSpace

/-- The Heath–Junnila space `X × Option ℕ` (`none` = limit copy of `X`,
`some n` = `n`-th isolated layer). -/
abbrev HeathJunnila (X : Type) : Type := X × Option ℕ

/-- Basic neighborhood `B(U, N) = (U × {none}) ∪ { (y, some n) | y ∈ U ∧ N ≤ n }`. -/
def hjBasic {X : Type} (U : Set X) (N : ℕ) : Set (HeathJunnila X) :=
  { p | p.1 ∈ U ∧ match p.2 with | none => True | some n => N ≤ n }

/-- The Heath–Junnila topology on `X × Option ℕ`:
every `(x, some n)` is isolated, while `(x, none)` has basic neighborhoods `hjBasic U N`. -/
@[instance_reducible]
def heathJunnilaTopology (X : Type) [TopologicalSpace X] :
    TopologicalSpace (HeathJunnila X) where
  IsOpen S :=
    ∀ x : X, (x, none) ∈ S → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ N : ℕ, hjBasic U N ⊆ S
  isOpen_univ := fun _ _ => ⟨univ, isOpen_univ, trivial, 0, fun _ _ => trivial⟩
  isOpen_inter := fun S₁ S₂ h₁ h₂ x ⟨hx1, hx2⟩ => by
    obtain ⟨U₁, hU₁, hxU₁, N₁, hsub₁⟩ := h₁ x hx1
    obtain ⟨U₂, hU₂, hxU₂, N₂, hsub₂⟩ := h₂ x hx2
    refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hxU₁, hxU₂⟩, max N₁ N₂, fun p hp => ?_⟩
    rcases p with ⟨y, o⟩
    cases o with
    | none => exact ⟨hsub₁ ⟨hp.1.1, trivial⟩, hsub₂ ⟨hp.1.2, trivial⟩⟩
    | some n =>
      exact ⟨hsub₁ ⟨hp.1.1, le_trans (le_max_left N₁ N₂) hp.2⟩,
             hsub₂ ⟨hp.1.2, le_trans (le_max_right N₁ N₂) hp.2⟩⟩
  isOpen_sUnion := fun 𝓢 h𝓢 x ⟨S, hS𝓢, hxS⟩ => by
    obtain ⟨U, hU, hxU, N, hsub⟩ := h𝓢 S hS𝓢 x hxS
    exact ⟨U, hU, hxU, N, hsub.trans (subset_sUnion_of_mem hS𝓢)⟩

/-- Characterization of open sets in `heathJunnilaTopology X`. -/
theorem hj_isOpen_iff {X : Type} [TopologicalSpace X] {S : Set (HeathJunnila X)} :
    @IsOpen (HeathJunnila X) (heathJunnilaTopology X) S ↔
      ∀ x : X, (x, none) ∈ S → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ N : ℕ, hjBasic U N ⊆ S :=
  Iff.rfl

/-- Every `(x, some n)` is isolated in `HeathJunnila X`. -/
theorem hj_isolated_isOpen {X : Type} [TopologicalSpace X] (_x : X) (n : ℕ) :
    @IsOpen (HeathJunnila X) (heathJunnilaTopology X) {(_x, some n)} :=
  hj_isOpen_iff.mpr fun _ hy => by simp at hy

/-- `hjBasic U N` is open whenever `U` is open in `X`. -/
theorem hjBasic_isOpen {X : Type} [TopologicalSpace X] {U : Set X} (hU : IsOpen U) (N : ℕ) :
    @IsOpen (HeathJunnila X) (heathJunnilaTopology X) (hjBasic U N) :=
  hj_isOpen_iff.mpr fun _ hx => ⟨U, hU, hx.1, N, Subset.rfl⟩

/-- `hjBasic K N` is closed whenever `K` is closed in `X`. -/
theorem hjBasic_isClosed {X : Type} [TopologicalSpace X] {K : Set X} (hK : IsClosed K) (N : ℕ) :
    @IsClosed (HeathJunnila X) (heathJunnilaTopology X) (hjBasic K N) := by
  let : TopologicalSpace (HeathJunnila X) := heathJunnilaTopology X
  rw [← isOpen_compl_iff, hj_isOpen_iff]
  intro x hx
  have hxK : x ∉ K := fun h => hx ⟨h, trivial⟩
  refine ⟨Kᶜ, hK.isOpen_compl, hxK, 0, fun p hp hpK => hp.1 hpK.1⟩

/-- `HeathJunnila X` is `T3Space` whenever `X` is `T3Space`. -/
theorem heathJunnila_t3Space {X : Type} [TopologicalSpace X] [T3Space X] :
    @T3Space (HeathJunnila X) (heathJunnilaTopology X) := by
  let : TopologicalSpace (HeathJunnila X) := heathJunnilaTopology X
  have hT1 : T1Space (HeathJunnila X) := ⟨fun p => by
    rw [← isOpen_compl_iff, hj_isOpen_iff]
    cases p with
    | mk x o =>
      cases o with
      | none =>
        intro y hy
        have hyx : y ≠ x := fun h => hy (by simp [h])
        refine ⟨{x}ᶜ, isClosed_singleton.isOpen_compl, hyx, 0, fun q hq hqx => ?_⟩
        rw [mem_singleton_iff] at hqx
        cases hqx
        exact hq.1 rfl
      | some n =>
        intro y _
        refine ⟨univ, isOpen_univ, trivial, n + 1, fun q hq hqn => ?_⟩
        rw [mem_singleton_iff] at hqn
        cases hqn
        simp only [hjBasic, mem_ofPred_eq] at hq
        omega⟩
  have hReg : RegularSpace (HeathJunnila X) := by
    refine RegularSpace.of_exists_mem_nhds_isClosed_subset fun p s hs => ?_
    obtain ⟨S, hSs, hSopen, hpS⟩ := mem_nhds_iff.mp hs
    cases p with
    | mk x o =>
      cases o with
      | none =>
        obtain ⟨U, hUopen, hxU, N, hsub⟩ := hj_isOpen_iff.mp hSopen x hpS
        obtain ⟨K, hKnhds, hKclosed, hKU⟩ := exists_mem_nhds_isClosed_subset (hUopen.mem_nhds hxU)
        obtain ⟨V, hVK, hVopen, hxV⟩ := mem_nhds_iff.mp hKnhds
        refine ⟨hjBasic K N,
          Filter.mem_of_superset ((hjBasic_isOpen hVopen N).mem_nhds ⟨hxV, trivial⟩)
            (fun q hq => ⟨hVK hq.1, hq.2⟩),
          hjBasic_isClosed hKclosed N,
          fun q hq => hSs (hsub ⟨hKU hq.1, hq.2⟩)⟩
      | some n =>
        exact ⟨{(x, some n)}, (hj_isolated_isOpen x n).mem_nhds rfl, isClosed_singleton,
          (singleton_subset_iff.mpr hpS).trans hSs⟩
  exact ⟨⟩

/-- **Heath–Junnila (1981) Main Theorem:**
For EVERY `M₂` space `X`, `HeathJunnila X` is an `M₁` space! -/
theorem heathJunnila_isM1_of_isM2 {X : Type} [TopologicalSpace X] (hM2 : MSpace.IsM2 X) :
    @MSpace.IsM1 (HeathJunnila X) (heathJunnilaTopology X) := by
  have hT3X : T3Space X := hM2.1
  let : TopologicalSpace (HeathJunnila X) := heathJunnilaTopology X
  have hT3 : T3Space (HeathJunnila X) := heathJunnila_t3Space
  obtain ⟨𝓑, hQB, 𝓑', h𝓑'_cp, rfl⟩ := hM2.2
  -- Closed `σ`-CP quasi-base `𝓒 k := closure '' 𝓑' k` on `X`
  let 𝓒 : ℕ → Set (Set X) := fun k => closure '' 𝓑' k
  have h𝓒_cp : ∀ k, MSpace.ClosurePreserving (𝓒 k) := by
    intro k 𝓖 h𝓖
    apply Subset.antisymm
    · intro x hx
      let 𝓖₀ : Set (Set X) := { B ∈ 𝓑' k | closure B ∈ 𝓖 }
      have hsub : ⋃₀ 𝓖 ⊆ closure (⋃₀ 𝓖₀) := by
        rintro y ⟨C, hC𝓖, hyC⟩
        obtain ⟨B, hBk, rfl⟩ := h𝓖 hC𝓖
        exact closure_mono (subset_sUnion_of_mem (show B ∈ 𝓖₀ from ⟨hBk, hC𝓖⟩)) hyC
      have hx' : x ∈ closure (⋃₀ 𝓖₀) := isClosed_closure.closure_subset (closure_mono hsub hx)
      rw [h𝓑'_cp k 𝓖₀ (fun B hB => hB.1)] at hx'
      obtain ⟨_, ⟨B, ⟨_, hBG⟩, rfl⟩, hxB⟩ := hx'
      exact ⟨closure (closure B), mem_image_of_mem _ hBG, subset_closure hxB⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  -- Open sets `O(C, N) := (interior C × {none}) ∪ { (y, some n) | y ∈ C ∧ N ≤ n }`
  let mkO : Set X → ℕ → Set (HeathJunnila X) := fun C N =>
    { p | match p.2 with | none => p.1 ∈ interior C | some n => p.1 ∈ C ∧ N ≤ n }
  have hmkO_open : ∀ C N, IsOpen (mkO C N) := by
    intro C N
    rw [hj_isOpen_iff]
    intro x hx
    refine ⟨interior C, isOpen_interior, hx, N, fun p hp => ?_⟩
    rcases p with ⟨y, o⟩
    cases o with
    | none => exact hp.1
    | some n => exact ⟨interior_subset hp.1, hp.2⟩
  -- Layer family `𝓛 : ℕ → Set (Set (HeathJunnila X))`:
  -- even `2 * n`: isolated layer `{ {(x, some n)} | x : X }`
  -- odd `2 * m + 1`: `{ mkO C N | C ∈ 𝓒 k }` where `(k, N) = Nat.unpair m`
  let 𝓛₀ : ℕ → Set (Set (HeathJunnila X)) := fun n =>
    { S | ∃ x : X, S = {(x, some n)} }
  let 𝓛₁ : ℕ → ℕ → Set (Set (HeathJunnila X)) := fun k N =>
    { S | ∃ C ∈ 𝓒 k, S = mkO C N }
  let 𝓛 : ℕ → Set (Set (HeathJunnila X)) := fun i =>
    if i % 2 = 0 then 𝓛₀ (i / 2) else 𝓛₁ (Nat.unpair (i / 2)).1 (Nat.unpair (i / 2)).2
  have h𝓛₀_cp : ∀ n, MSpace.ClosurePreserving (𝓛₀ n) := by
    intro n 𝓖 h𝓖
    apply Subset.antisymm
    · rintro ⟨x, o⟩ hx
      cases o with
      | none =>
        rw [mem_closure_iff] at hx
        obtain ⟨q, hqB, S, hS𝓖, hqS⟩ := hx (hjBasic univ (n + 1)) (hjBasic_isOpen isOpen_univ (n + 1)) ⟨trivial, trivial⟩
        obtain ⟨y, rfl⟩ := h𝓖 hS𝓖
        rw [mem_singleton_iff] at hqS
        subst hqS
        simp only [hjBasic, mem_ofPred_eq] at hqB
        omega
      | some m =>
        rw [mem_closure_iff] at hx
        obtain ⟨q, hqm, S, hS𝓖, hqS⟩ := hx {(x, some m)} (hj_isolated_isOpen x m) rfl
        rw [mem_singleton_iff] at hqm
        exact ⟨closure S, mem_image_of_mem _ hS𝓖, subset_closure (hqm ▸ hqS)⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  have h𝓛₁_cp : ∀ k N, MSpace.ClosurePreserving (𝓛₁ k N) := by
    intro k N 𝓖 h𝓖
    apply Subset.antisymm
    · rintro ⟨x, o⟩ hx
      cases o with
      | none =>
        let 𝓖X : Set (Set X) := { C ∈ 𝓒 k | mkO C N ∈ 𝓖 }
        have hxX : x ∈ closure (⋃₀ 𝓖X) := by
          rw [mem_closure_iff]
          intro U hU hxU
          rw [mem_closure_iff] at hx
          obtain ⟨⟨y, oy⟩, hyB, S, hS𝓖, hyS⟩ := hx (hjBasic U 0) (hjBasic_isOpen hU 0) ⟨hxU, trivial⟩
          obtain ⟨C, hCk, rfl⟩ := h𝓖 hS𝓖
          have hyC : y ∈ C := by
            cases oy with
            | none => exact interior_subset hyS
            | some _ => exact hyS.1
          exact ⟨y, hyB.1, C, ⟨hCk, hS𝓖⟩, hyC⟩
        rw [h𝓒_cp k 𝓖X (fun C hC => hC.1)] at hxX
        obtain ⟨_, ⟨C, ⟨hCk, hCG⟩, rfl⟩, hxclC⟩ := hxX
        obtain ⟨B, _, rfl⟩ := hCk
        have hxC : x ∈ closure B := isClosed_closure.closure_subset hxclC
        refine ⟨closure (mkO (closure B) N), mem_image_of_mem _ hCG, ?_⟩
        rw [mem_closure_iff]
        intro O hO hxO
        obtain ⟨U, hUopen, hxU, M, hMsub⟩ := hj_isOpen_iff.mp hO x hxO
        let m : ℕ := max N M
        exact ⟨(x, some m), hMsub ⟨hxU, le_max_right N M⟩, hxC, le_max_left N M⟩
      | some m =>
        rw [mem_closure_iff] at hx
        obtain ⟨q, hqm, S, hS𝓖, hqS⟩ := hx {(x, some m)} (hj_isolated_isOpen x m) rfl
        rw [mem_singleton_iff] at hqm
        exact ⟨closure S, mem_image_of_mem _ hS𝓖, subset_closure (hqm ▸ hqS)⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  refine ⟨hT3, ⋃ i, 𝓛 i, ?_, ⟨𝓛, ?_, rfl⟩⟩
  · apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro S hS
      obtain ⟨i, hSi⟩ := mem_iUnion.mp hS
      dsimp only [𝓛] at hSi
      split_ifs at hSi
      · obtain ⟨x, rfl⟩ := hSi; exact hj_isolated_isOpen x (i / 2)
      · obtain ⟨C, _, rfl⟩ := hSi; exact hmkO_open C _
    · rintro ⟨x, o⟩ S hxS hSopen
      cases o with
      | none =>
        obtain ⟨U, hUopen, hxU, N, hNsub⟩ := hj_isOpen_iff.mp hSopen x hxS
        obtain ⟨K, hKnhds, hKclosed, hKU⟩ := exists_mem_nhds_isClosed_subset (hUopen.mem_nhds hxU)
        obtain ⟨B, hB, hxB, hBK⟩ :=
          hQB x (interior K) isOpen_interior (mem_interior_iff_mem_nhds.mpr hKnhds)
        obtain ⟨k, hBk⟩ := mem_iUnion.mp hB
        let m : ℕ := Nat.pair k N
        refine ⟨mkO (closure B) N, mem_iUnion.mpr ⟨2 * m + 1, ?_⟩,
          interior_mono subset_closure hxB, ?_⟩
        · have hmod : (2 * m + 1) % 2 ≠ 0 := by omega
          have hdiv : (2 * m + 1) / 2 = m := by omega
          simp only [𝓛, hmod, ↓reduceIte, hdiv, m, Nat.unpair_pair]
          exact ⟨closure B, ⟨B, hBk, rfl⟩, rfl⟩
        · rintro ⟨y, oy⟩ hy
          have hclU : closure B ⊆ U := (closure_minimal (hBK.trans interior_subset) hKclosed).trans hKU
          cases oy with
          | none => exact hNsub ⟨hclU (interior_subset hy), trivial⟩
          | some n => exact hNsub ⟨hclU hy.1, hy.2⟩
      | some n =>
        refine ⟨{(x, some n)}, mem_iUnion.mpr ⟨2 * n, ?_⟩, rfl, singleton_subset_iff.mpr hxS⟩
        have hmod : (2 * n) % 2 = 0 := by omega
        have hdiv : (2 * n) / 2 = n := by omega
        simp only [𝓛, hmod, ↓reduceIte, hdiv]
        exact ⟨x, rfl⟩
  · intro i
    dsimp only [𝓛]
    split_ifs
    · exact h𝓛₀_cp (i / 2)
    · exact h𝓛₁_cp (Nat.unpair (i / 2)).1 (Nat.unpair (i / 2)).2

/-- Every `M₃` (stratifiable) space `X` yields an `M₁` space `HeathJunnila X`. -/
theorem heathJunnila_isM1_of_isM3 {X : Type} [TopologicalSpace X] (hM3 : MSpace.IsM3 X) :
    @MSpace.IsM1 (HeathJunnila X) (heathJunnilaTopology X) :=
  heathJunnila_isM1_of_isM2 (Proofs.L_0008.main X hM3)

/-- The canonical closed subspace `hjLimit X := { p : HeathJunnila X | p.2 = none }`. -/
def hjLimit (X : Type) : Set (HeathJunnila X) := { p | p.2 = none }

theorem hjLimit_isClosed (X : Type) [TopologicalSpace X] :
    @IsClosed (HeathJunnila X) (heathJunnilaTopology X) (hjLimit X) := by
  let : TopologicalSpace (HeathJunnila X) := heathJunnilaTopology X
  rw [← isOpen_compl_iff, hj_isOpen_iff]
  intro x hx
  exact (hx rfl).elim

/-- `X` is homeomorphic to the closed subspace `hjLimit X` of `HeathJunnila X`. -/
def hjLimitHomeomorph (X : Type) [tX : TopologicalSpace X] :
    @Homeomorph X ↥(hjLimit X) tX
      (@instTopologicalSpaceSubtype (HeathJunnila X) (fun p => p ∈ hjLimit X) (heathJunnilaTopology X)) :=
  letI : TopologicalSpace (HeathJunnila X) := heathJunnilaTopology X
  { toFun := fun x => ⟨(x, none), rfl⟩
    invFun := fun p => p.1.1
    left_inv := fun _ => rfl
    right_inv := fun p => by
      rcases p with ⟨⟨x, o⟩, ho⟩
      cases ho
      rfl
    continuous_toFun := by
      rw [continuous_induced_rng]
      rw [continuous_def]
      intro S hS
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      obtain ⟨U, hUopen, hxU, _, hsub⟩ := hj_isOpen_iff.mp hS x hx
      exact ⟨U, fun y hy => hsub ⟨hy, trivial⟩, hUopen, hxU⟩
    continuous_invFun := by
      rw [continuous_def]
      intro U hU
      rw [isOpen_induced_iff]
      refine ⟨hjBasic U 0, hjBasic_isOpen hU 0, ?_⟩
      ext ⟨⟨x, o⟩, ho⟩
      cases ho
      simp [hjBasic] }

end HeathJunnilaSpace

section EquivalenceWithClosedSubspaceM1

/-- Helper: `MSpace.IsM1` is preserved by homeomorphisms. -/
private theorem isM1_of_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hY : MSpace.IsM1 Y) : MSpace.IsM1 X := by
  have hT3Y : T3Space Y := hY.1
  have hT1X : T1Space X := ⟨fun x => by
    have hEq : ({x} : Set X) = e ⁻¹' {e x} := by ext z; simp [e.injective.eq_iff]
    rw [hEq]
    exact isClosed_singleton.preimage e.continuous⟩
  have hRegX : RegularSpace X := by
    refine RegularSpace.of_exists_mem_nhds_isClosed_subset fun x s hs => ?_
    obtain ⟨U, hUs, hUopen, hxU⟩ := mem_nhds_iff.mp hs
    have hU' : IsOpen (e.symm ⁻¹' U) := hUopen.preimage e.symm.continuous
    obtain ⟨K, hKnhds, hKclosed, hKU'⟩ :=
      exists_mem_nhds_isClosed_subset (hU'.mem_nhds (show e x ∈ e.symm ⁻¹' U by simpa using hxU))
    refine ⟨e ⁻¹' K, e.continuous.continuousAt.preimage_mem_nhds hKnhds,
      hKclosed.preimage e.continuous, fun z hz => hUs (by simpa using hKU' hz)⟩
  have hT3X : T3Space X := ⟨⟩
  obtain ⟨𝓑, h𝓑bas, 𝓑', h𝓑'cp, rfl⟩ := hY.2
  let 𝓑X' : ℕ → Set (Set X) := fun n => (fun V => e ⁻¹' V) '' 𝓑' n
  refine ⟨hT3X, ⋃ n, 𝓑X' n, ?_, ⟨𝓑X', ?_, rfl⟩⟩
  · apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro S hS
      obtain ⟨n, V, hVn, rfl⟩ := by simpa [𝓑X'] using hS
      exact (h𝓑bas.isOpen (mem_iUnion.mpr ⟨n, hVn⟩)).preimage e.continuous
    · intro x U hxU hUopen
      obtain ⟨V, hV, hexV, hVU⟩ :=
        h𝓑bas.exists_subset_of_mem_open (show e x ∈ e.symm ⁻¹' U by simpa using hxU)
          (hUopen.preimage e.symm.continuous)
      obtain ⟨n, hVn⟩ := mem_iUnion.mp hV
      exact ⟨e ⁻¹' V, mem_iUnion.mpr ⟨n, V, hVn, rfl⟩, hexV, fun z hz => by simpa using hVU hz⟩
  · intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro x hx
      let 𝓖Y : Set (Set Y) := { V ∈ 𝓑' n | e ⁻¹' V ∈ 𝓖 }
      have hsub : ⋃₀ 𝓖 ⊆ e ⁻¹' (⋃₀ 𝓖Y) := by
        rintro z ⟨S, hS𝓖, hzS⟩
        obtain ⟨V, hVn, rfl⟩ := h𝓖 hS𝓖
        exact ⟨V, ⟨hVn, hS𝓖⟩, hzS⟩
      have hex_cl : e x ∈ closure (⋃₀ 𝓖Y) := by
        have h1 : x ∈ closure (e ⁻¹' ⋃₀ 𝓖Y) := closure_mono hsub hx
        exact e.continuous.closure_preimage_subset (⋃₀ 𝓖Y) h1
      rw [h𝓑'cp n 𝓖Y (fun V hV => hV.1)] at hex_cl
      obtain ⟨_, ⟨V, ⟨_, hVG⟩, rfl⟩, hexV⟩ := hex_cl
      refine ⟨closure (e ⁻¹' V), mem_image_of_mem _ hVG, ?_⟩
      rw [← e.preimage_closure]
      exact hexV
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Helper: every closed subspace of a stratifiable space is stratifiable. -/
private theorem isStratifiable_closed_subtype {Z : Type} [TopologicalSpace Z]
    (hStrat : MSpace.IsStratifiable Z) {F : Set Z} (hF : IsClosed F) :
    MSpace.IsStratifiable ↥F := by
  have hT1Z : T1Space Z := hStrat.1
  have hT1F : T1Space ↥F := inferInstance
  obtain ⟨G, hGo, hGs, hGi, hGm⟩ := hStrat.2
  let GF : ℕ → Set ↥F → Set ↥F := fun n H => ((↑) : ↥F → Z) ⁻¹' G n (((↑) : ↥F → Z) '' H)
  refine ⟨hT1F, GF, ?_, ?_, ?_, ?_⟩
  · intro n H hH
    exact (hGo n _ (hF.isClosedMap_subtype_val H hH)).preimage continuous_subtype_val
  · intro n H hH x hx
    exact hGs n _ (hF.isClosedMap_subtype_val H hH) ⟨x, hx, rfl⟩
  · intro H hH
    apply Subset.antisymm
    · intro x hx
      have hxZ : (x : Z) ∈ ⋂ n, closure (G n (((↑) : ↥F → Z) '' H)) :=
        mem_iInter.mpr fun n =>
          continuous_subtype_val.closure_preimage_subset _ (mem_iInter.mp hx n)
      rw [hGi _ (hF.isClosedMap_subtype_val H hH)] at hxZ
      obtain ⟨y, hyH, hyx⟩ := hxZ
      exact (Subtype.ext hyx.symm) ▸ hyH
    · exact subset_iInter fun n x hx =>
        subset_closure (hGs n _ (hF.isClosedMap_subtype_val H hH) ⟨x, hx, rfl⟩)
  · intro n H K hH hK hHK
    exact preimage_mono (hGm n _ _ (hF.isClosedMap_subtype_val H hH)
      (hF.isClosedMap_subtype_val K hK) (image_mono hHK))

/-- **Heath–Junnila (1981) Equivalence Theorem:**
Ceder's open problem `Tinf` (`M₃ ⇒ M₁`) is equivalent to the Closed-Subspace `M₁`
Problem ("every closed subspace of every `M₁` space is `M₁`"). -/
theorem Tinf_iff_closed_subspace_M1 :
    MSpace.Goals.Tinf_M3_imp_M1 ↔
      ∀ (Z : Type) [TopologicalSpace Z], MSpace.IsM1 Z → ∀ F : Set Z, IsClosed F → MSpace.IsM1 ↥F := by
  constructor
  · intro hTinf Z _ hM1 F hF
    have hM3Z : MSpace.IsM3 Z := Proofs.L_0003.main Z (Proofs.L_0002.main Z hM1)
    have hStratZ : MSpace.IsStratifiable Z := (Proofs.L_0004.main Z).mp hM3Z
    have hStratF : MSpace.IsStratifiable ↥F := isStratifiable_closed_subtype hStratZ hF
    have hM3F : MSpace.IsM3 ↥F := (Proofs.L_0004.main ↥F).mpr hStratF
    exact hTinf ↥F hM3F
  · intro hClosed X _ hM3
    let : TopologicalSpace (HeathJunnila X) := heathJunnilaTopology X
    have hM1Z : MSpace.IsM1 (HeathJunnila X) := heathJunnila_isM1_of_isM3 hM3
    have hM1Lim : MSpace.IsM1 ↥(hjLimit X) := hClosed (HeathJunnila X) hM1Z (hjLimit X) (hjLimit_isClosed X)
    exact isM1_of_homeomorph (hjLimitHomeomorph X) hM1Lim

end EquivalenceWithClosedSubspaceM1

end Research.HeathJunnilaTheorem
