import Targets
import Defs.D_0001
import Defs.D_0007
import Defs.D_0011
import Specs.L_0031
import Proofs.L_0004
import Proofs.L_0017
import Proofs.L_0029
import Proofs.L_0032
import Proofs.R_0009
import Proofs.R_0010

/-!
# Refinement Stratifiability Theorem for Chen–Wang (`τ ≤ xtop α` on `Y ⊆ ℕ → α`)

In Chen–Wang (arXiv:1809.03763v2, Sections 6–7), the counterexample `(Y, τ)` is
constructed on a subspace `Y ⊆ X = ℕ → Q` by **refining** the Baire-type topology
`Defs.D_0011.xtop Q` (`τ ≤ xtop_Y`).

This file proves the **Refinement Stratifiability Theorem** and its direct reduction
to `Specs.L_0031` and `¬ MSpace.Goals.Tinf_M3_imp_M1`:

1. `isStratifiable_of_refinement`:
   If `τ₀` is stratifiable on `Y` and `τ ≤ τ₀` is a finer topology, then `(Y, τ)`
   is stratifiable as soon as there is a monotone `τ`-open operator `R n F ⊇ F`
   that separates every `τ`-closed `F` from its **`τ₀`-boundary** `closure[τ₀] F \ F`.
   (All points `x ∉ closure[τ₀] F` are separated automatically by `τ₀`!)
2. `isStratifiable_of_refinement_g`:
   `g`-function version: `g : ℕ → Y → Set Y` (`τ`-open, `y ∈ g n y`) only needs to
   separate `τ`-closed `F` from `closure[τ₀] F \ F` (no monotonicity in `n`, no
   `⋂ n, g n y = {y}`, and no `T1Space` proof needed!).
3. `isStratifiable_of_laminar_clopen_partition`:
   Any space with a decreasing laminar clopen partition `W n y` (`⋂ n, W n y = {y}`)
   is stratifiable (yielding `xtop_isStratifiable` and `xtop_subtype_isStratifiable`).
4. `xtop_subtype_refinement_L0031` & `xtop_subtype_refinement_not_Tinf`:
   End-to-end Chen–Wang reduction: for any subspace `Y : Set (ℕ → α)` and any
   refinement `τ ≤ xtop_Y` on `↥Y`, a boundary-separating `τ`-open `g`-function
   plus `¬ HasCPOuterBase y₀` immediately proves `Specs.L_0031.stmt` and
   `¬ MSpace.Goals.Tinf_M3_imp_M1`.
-/

namespace Research.ChenWangRefinement

open MSpace Set Topology

section GeneralRefinement

/-- **Refinement Stratifiability Theorem:**
Let `τ₀` be a stratifiable topology on `Y` and `τ ≤ τ₀` a finer topology (every
`τ₀`-open set is `τ`-open). If `R : ℕ → Set Y → Set Y` is a monotone `τ`-open
operator with `F ⊆ R n F` that separates every `τ`-closed `F` from `closure[τ₀] F \ F`,
then `(Y, τ)` is stratifiable. -/
theorem isStratifiable_of_refinement
    {Y : Type*} (τ₀ τ : TopologicalSpace Y) (hle : τ ≤ τ₀)
    (hStrat₀ : @MSpace.IsStratifiable Y τ₀)
    (R : ℕ → Set Y → Set Y)
    (hR_open : ∀ n F, @IsClosed Y τ F → @IsOpen Y τ (R n F))
    (hR_sub : ∀ n F, @IsClosed Y τ F → F ⊆ R n F)
    (hR_mono : ∀ n F K, @IsClosed Y τ F → @IsClosed Y τ K → F ⊆ K → R n F ⊆ R n K)
    (hR_bdry : ∀ F, @IsClosed Y τ F →
      ∀ x ∈ @closure Y τ₀ F \ F, ∃ n, x ∉ @closure Y τ (R n F)) :
    @MSpace.IsStratifiable Y τ := by
  have hT1₀ : @T1Space Y τ₀ := hStrat₀.1
  have hT1 : @T1Space Y τ := by
    refine @T1Space.mk Y τ fun x => ?_
    have hc₀ : @IsClosed Y τ₀ ({x} : Set Y) := @isClosed_singleton Y τ₀ hT1₀ x
    exact (@isOpen_compl_iff Y {x} τ).mp (hle _ ((@isOpen_compl_iff Y {x} τ₀).mpr hc₀))
  have hcl_le : ∀ S : Set Y, @closure Y τ S ⊆ @closure Y τ₀ S := by
    intro S x hx
    rw [@mem_closure_iff Y τ₀]
    intro O hO hxO
    rw [@mem_closure_iff Y τ] at hx
    exact hx O (hle O hO) hxO
  obtain ⟨G₀, hG₀_open, hG₀_sub, hG₀_inter, hG₀_mono⟩ := hStrat₀.2
  refine ⟨hT1, fun n F => G₀ n (@closure Y τ₀ F) ∩ R n F, ?_, ?_, ?_, ?_⟩
  · intro n F hF
    exact @IsOpen.inter Y τ _ _
      (hle _ (hG₀_open n (@closure Y τ₀ F) (@isClosed_closure Y τ₀ F)))
      (hR_open n F hF)
  · intro n F hF
    exact subset_inter
      ((@subset_closure Y τ₀ F).trans (hG₀_sub n (@closure Y τ₀ F) (@isClosed_closure Y τ₀ F)))
      (hR_sub n F hF)
  · intro F hF
    apply Subset.antisymm
    · intro x hx
      by_contra hxF
      by_cases hxcl₀ : x ∈ @closure Y τ₀ F
      · obtain ⟨n, hn⟩ := hR_bdry F hF x ⟨hxcl₀, hxF⟩
        have hxn : x ∈ @closure Y τ (G₀ n (@closure Y τ₀ F) ∩ R n F) := mem_iInter.mp hx n
        have hsub : @closure Y τ (G₀ n (@closure Y τ₀ F) ∩ R n F) ⊆ @closure Y τ (R n F) :=
          @closure_mono Y τ _ _ inter_subset_right
        exact hn (hsub hxn)
      · have hxnot : x ∉ ⋂ n, @closure Y τ₀ (G₀ n (@closure Y τ₀ F)) := by
          rw [hG₀_inter (@closure Y τ₀ F) (@isClosed_closure Y τ₀ F)]
          exact hxcl₀
        rw [mem_iInter] at hxnot
        push Not at hxnot
        obtain ⟨n, hn⟩ := hxnot
        have hxn : x ∈ @closure Y τ (G₀ n (@closure Y τ₀ F) ∩ R n F) := mem_iInter.mp hx n
        have hsub : @closure Y τ (G₀ n (@closure Y τ₀ F) ∩ R n F) ⊆
            @closure Y τ (G₀ n (@closure Y τ₀ F)) :=
          @closure_mono Y τ _ _ inter_subset_left
        exact hn (hcl_le _ (hsub hxn))
    · refine subset_iInter fun n => ?_
      exact (subset_inter
        ((@subset_closure Y τ₀ F).trans (hG₀_sub n (@closure Y τ₀ F) (@isClosed_closure Y τ₀ F)))
        (hR_sub n F hF)).trans (@subset_closure Y τ _)
  · intro n F K hF hK hFK
    exact inter_subset_inter
      (hG₀_mono n _ _ (@isClosed_closure Y τ₀ F) (@isClosed_closure Y τ₀ K)
        (@closure_mono Y τ₀ _ _ hFK))
      (hR_mono n F K hF hK hFK)

/-- **`g`-Function Refinement Stratifiability Theorem:**
If `τ₀` is stratifiable on `Y` and `τ ≤ τ₀` is finer, then any `g : ℕ → Y → Set Y`
with `IsOpen[τ] (g n y)` and `y ∈ g n y` that separates every `τ`-closed `F` from
`closure[τ₀] F \ F` makes `(Y, τ)` stratifiable. -/
theorem isStratifiable_of_refinement_g
    {Y : Type*} (τ₀ τ : TopologicalSpace Y) (hle : τ ≤ τ₀)
    (hStrat₀ : @MSpace.IsStratifiable Y τ₀)
    (g : ℕ → Y → Set Y)
    (hg_open : ∀ n y, @IsOpen Y τ (g n y) ∧ y ∈ g n y)
    (hg_bdry : ∀ F, @IsClosed Y τ F →
      ∀ x ∈ @closure Y τ₀ F \ F, ∃ n, x ∉ @closure Y τ (⋃ y ∈ F, g n y)) :
    @MSpace.IsStratifiable Y τ := by
  refine isStratifiable_of_refinement τ₀ τ hle hStrat₀
    (fun n F => ⋃ y ∈ F, g n y)
    (fun n F _ => @isOpen_biUnion Y Y τ _ _ fun y _ => (hg_open n y).1)
    (fun n F _ x hx => mem_biUnion hx (hg_open n x).2)
    (fun n F K _ _ hFK => biUnion_subset_biUnion_left hFK)
    hg_bdry

end GeneralRefinement

section LaminarAndXTop

/-- Any topological space with a decreasing laminar clopen partition `W n y`
satisfying `⋂ n, W n y = {y}` is stratifiable. -/
theorem isStratifiable_of_laminar_clopen_partition
    {Y : Type} [TopologicalSpace Y]
    (W : ℕ → Y → Set Y)
    (hmem : ∀ n y, y ∈ W n y)
    (hdec : ∀ n y, W (n + 1) y ⊆ W n y)
    (hpart : ∀ n x y, y ∈ W n x → W n y = W n x)
    (hinter : ∀ y, (⋂ n, W n y) = {y})
    (hW_clopen : ∀ n y, IsOpen (W n y) ∧ IsClosed (W n y))
    (hW_base : ∀ U : Set Y, IsOpen U → ∀ x ∈ U, ∃ n, W n x ⊆ U) :
    MSpace.IsStratifiable Y := by
  have hT1 : T1Space Y := ⟨fun y => by
    rw [← hinter y]
    exact isClosed_iInter fun n => (hW_clopen n y).2⟩
  refine ⟨hT1, ?_⟩
  refine Proofs.L_0017.main Y ⟨W, fun n y => ⟨(hW_clopen n y).1, hmem n y⟩, hdec, ?_⟩
  intro F hF x hxF
  obtain ⟨n, hn⟩ := hW_base Fᶜ hF.isOpen_compl x hxF
  refine ⟨n, ?_⟩
  intro hxcl
  rw [mem_closure_iff] at hxcl
  obtain ⟨w, hwWnx, hwU⟩ := hxcl (W n x) (hW_clopen n x).1 (hmem n x)
  simp only [mem_iUnion, exists_prop] at hwU
  obtain ⟨y, hyF, hwWny⟩ := hwU
  have h1 : W n w = W n x := hpart n x w hwWnx
  have h2 : W n w = W n y := hpart n y w hwWny
  have hyWnx : y ∈ W n x := (h2.symm.trans h1) ▸ hmem n y
  exact hn hyWnx hyF

/-- `(ℕ → α, Defs.D_0011.xtop α)` is stratifiable for any `q : ℕ ≃ α`. -/
theorem xtop_isStratifiable {α : Type} (q : ℕ ≃ α) :
    @MSpace.IsStratifiable (ℕ → α) (Defs.D_0011.xtop α) := by
  let : TopologicalSpace (ℕ → α) := Defs.D_0011.xtop α
  let W : ℕ → (ℕ → α) → Set (ℕ → α) := fun n x =>
    Defs.D_0007.H q (n + 1) (Defs.D_0007.code (n + 1) (fun k => q.symm (x k)))
  refine isStratifiable_of_laminar_clopen_partition W
    (fun _ _ => rfl)
    (fun n x y hy => by
      have hsame := (Defs.D_0007.mem_H_iff_same q (n + 2) (Nat.succ_pos _) y x).mp hy
      exact (Defs.D_0007.mem_H_iff_same q (n + 1) (Nat.succ_pos _) y x).mpr
        (fun k hk => hsame k (Nat.lt_succ_of_lt hk)))
    (fun n x y hy => by
      have hc : Defs.D_0007.code (n + 1) (fun k => q.symm (y k)) =
          Defs.D_0007.code (n + 1) (fun k => q.symm (x k)) := hy
      simp only [W, hc])
    (fun x => by
      ext y
      simp only [W, mem_iInter, mem_singleton_iff]
      constructor
      · intro hy
        funext k
        exact (Defs.D_0007.mem_H_iff_same q (k + 1) (Nat.succ_pos k) y x).mp (hy k) k (Nat.lt_succ_self k)
      · rintro rfl n; rfl)
    (fun n x => ⟨Defs.D_0011.H_isOpen q (n + 1) (Nat.succ_pos n) _,
      Defs.D_0011.H_isClosed q (n + 1) (Nat.succ_pos n) _⟩)
    (fun U hU x hx => by
      let : TopologicalSpace α := ⊥
      obtain ⟨I, t, ht_all, htU⟩ := isOpen_pi_iff.mp hU x hx
      let n : ℕ := I.sup id
      refine ⟨n, fun y hy => htU fun k hkI => ?_⟩
      have hkn : k < n + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hkI)
      have hsame := (Defs.D_0007.mem_H_iff_same q (n + 1) (Nat.succ_pos n) y x).mp hy k hkn
      rw [hsame]
      exact (ht_all k hkI).2)

/-- Any subspace `↥Y` of `(ℕ → α, Defs.D_0011.xtop α)` is stratifiable. -/
theorem xtop_subtype_isStratifiable {α : Type} (q : ℕ ≃ α) (Y : Set (ℕ → α)) :
    @MSpace.IsStratifiable ↥Y (@instTopologicalSpaceSubtype (ℕ → α) (fun x => x ∈ Y) (Defs.D_0011.xtop α)) := by
  let tX : TopologicalSpace (ℕ → α) := Defs.D_0011.xtop α
  let : TopologicalSpace ↥Y := @instTopologicalSpaceSubtype (ℕ → α) (fun x => x ∈ Y) tX
  let W : ℕ → ↥Y → Set ↥Y := fun n x =>
    ((↑) : ↥Y → ℕ → α) ⁻¹'
      Defs.D_0007.H q (n + 1) (Defs.D_0007.code (n + 1) (fun k => q.symm (x.1 k)))
  refine isStratifiable_of_laminar_clopen_partition W
    (fun _ _ => rfl)
    (fun n x y hy => by
      have hsame := (Defs.D_0007.mem_H_iff_same q (n + 2) (Nat.succ_pos _) y.1 x.1).mp hy
      exact (Defs.D_0007.mem_H_iff_same q (n + 1) (Nat.succ_pos _) y.1 x.1).mpr
        (fun k hk => hsame k (Nat.lt_succ_of_lt hk)))
    (fun n x y hy => by
      have hc : Defs.D_0007.code (n + 1) (fun k => q.symm (y.1 k)) =
          Defs.D_0007.code (n + 1) (fun k => q.symm (x.1 k)) := hy
      simp only [W, hc])
    (fun x => by
      ext y
      simp only [W, mem_iInter, mem_singleton_iff]
      constructor
      · intro hy
        apply Subtype.ext
        funext k
        exact (Defs.D_0007.mem_H_iff_same q (k + 1) (Nat.succ_pos k) y.1 x.1).mp (hy k) k (Nat.lt_succ_self k)
      · rintro rfl n; rfl)
    (fun n x => ⟨(Defs.D_0011.H_isOpen q (n + 1) (Nat.succ_pos n) _).preimage continuous_subtype_val,
      (Defs.D_0011.H_isClosed q (n + 1) (Nat.succ_pos n) _).preimage continuous_subtype_val⟩)
    (fun U hU x hx => by
      rw [isOpen_induced_iff] at hU
      obtain ⟨V, hVopen, rfl⟩ := hU
      let : TopologicalSpace α := ⊥
      obtain ⟨I, t, ht_all, htV⟩ := isOpen_pi_iff.mp hVopen x.1 hx
      let n : ℕ := I.sup id
      refine ⟨n, fun y hy => htV fun k hkI => ?_⟩
      have hkn : k < n + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hkI)
      have hsame := (Defs.D_0007.mem_H_iff_same q (n + 1) (Nat.succ_pos n) y.1 x.1).mp hy k hkn
      rw [hsame]
      exact (ht_all k hkI).2)

/-- **End-to-End Chen–Wang Subspace Refinement Criterion for `Specs.L_0031`:**
For any subspace `Y : Set (ℕ → α)` and any topology `τ` on `↥Y` finer than the
`xtop α` subspace topology, if `g : ℕ → ↥Y → Set ↥Y` is `τ`-open and separates
`τ`-closed sets from their `xtop`-subspace boundary, and some `y₀ : ↥Y` has
`¬ HasCPOuterBase y₀`, then `Specs.L_0031.stmt` holds. -/
theorem xtop_subtype_refinement_L0031
    {α : Type} (q : ℕ ≃ α) (Y : Set (ℕ → α))
    (τ : TopologicalSpace ↥Y)
    (hle : τ ≤ @instTopologicalSpaceSubtype (ℕ → α) (fun x => x ∈ Y) (Defs.D_0011.xtop α))
    (g : ℕ → ↥Y → Set ↥Y)
    (hg_open : ∀ n y, @IsOpen ↥Y τ (g n y) ∧ y ∈ g n y)
    (hg_bdry : ∀ F, @IsClosed ↥Y τ F →
      ∀ x ∈ @closure ↥Y (@instTopologicalSpaceSubtype (ℕ → α) (fun x => x ∈ Y) (Defs.D_0011.xtop α)) F \ F,
        ∃ n, x ∉ @closure ↥Y τ (⋃ y ∈ F, g n y))
    (y₀ : ↥Y)
    (hno : ¬ @Defs.D_0001.HasCPOuterBase ↥Y τ y₀) :
    Specs.L_0031.stmt := by
  let t₀ : TopologicalSpace ↥Y :=
    @instTopologicalSpaceSubtype (ℕ → α) (fun x => x ∈ Y) (Defs.D_0011.xtop α)
  have hStrat : @MSpace.IsStratifiable ↥Y τ :=
    isStratifiable_of_refinement_g t₀ τ hle (xtop_subtype_isStratifiable q Y) g hg_open hg_bdry
  let W : ℕ → Set ↥Y := fun n =>
    ((↑) : ↥Y → ℕ → α) ⁻¹'
      Defs.D_0007.H q (n + 1) (Defs.D_0007.code (n + 1) (fun k => q.symm (y₀.1 k)))
  have hW_clopen : ∀ n, @IsOpen ↥Y τ (W n) ∧ @IsClosed ↥Y τ (W n) ∧ y₀ ∈ W n := by
    intro n
    have ho₀ : @IsOpen ↥Y t₀ (W n) := by
      let : TopologicalSpace (ℕ → α) := Defs.D_0011.xtop α
      exact (Defs.D_0011.H_isOpen q (n + 1) (Nat.succ_pos n) _).preimage continuous_subtype_val
    have hc₀ : @IsClosed ↥Y t₀ (W n) := by
      let : TopologicalSpace (ℕ → α) := Defs.D_0011.xtop α
      exact (Defs.D_0011.H_isClosed q (n + 1) (Nat.succ_pos n) _).preimage continuous_subtype_val
    refine ⟨hle _ ho₀, ?_, rfl⟩
    exact (@isOpen_compl_iff ↥Y (W n) τ).mp (hle _ ((@isOpen_compl_iff ↥Y (W n) t₀).mpr hc₀))
  have hW_inter : (⋂ n, W n) = {y₀} := by
    ext y
    simp only [W, mem_iInter, mem_singleton_iff]
    constructor
    · intro hy
      apply Subtype.ext
      funext k
      exact (Defs.D_0007.mem_H_iff_same q (k + 1) (Nat.succ_pos k) y.1 y₀.1).mp (hy k) k (Nat.lt_succ_self k)
    · rintro rfl n; rfl
  exact ⟨↥Y, τ, hStrat, y₀, ⟨W, hW_clopen, hW_inter⟩, hno⟩

/-- **End-to-End Chen–Wang Subspace Refinement Refutation of `Tinf`:**
Direct refutation of `MSpace.Goals.Tinf_M3_imp_M1` from the hypotheses of
`xtop_subtype_refinement_L0031`. -/
theorem xtop_subtype_refinement_not_Tinf
    {α : Type} (q : ℕ ≃ α) (Y : Set (ℕ → α))
    (τ : TopologicalSpace ↥Y)
    (hle : τ ≤ @instTopologicalSpaceSubtype (ℕ → α) (fun x => x ∈ Y) (Defs.D_0011.xtop α))
    (g : ℕ → ↥Y → Set ↥Y)
    (hg_open : ∀ n y, @IsOpen ↥Y τ (g n y) ∧ y ∈ g n y)
    (hg_bdry : ∀ F, @IsClosed ↥Y τ F →
      ∀ x ∈ @closure ↥Y (@instTopologicalSpaceSubtype (ℕ → α) (fun x => x ∈ Y) (Defs.D_0011.xtop α)) F \ F,
        ∃ n, x ∉ @closure ↥Y τ (⋃ y ∈ F, g n y))
    (y₀ : ↥Y)
    (hno : ¬ @Defs.D_0001.HasCPOuterBase ↥Y τ y₀) :
    ¬ MSpace.Goals.Tinf_M3_imp_M1 := by
  have hL31 : Specs.L_0031.stmt :=
    xtop_subtype_refinement_L0031 q Y τ hle g hg_open hg_bdry y₀ hno
  have hL30 : Specs.L_0030.stmt := Proofs.R_0010.main hL31 Proofs.L_0032.main
  exact Proofs.R_0009.main Proofs.L_0029.main hL30 Proofs.L_0004.main

end LaminarAndXTop

end Research.ChenWangRefinement
