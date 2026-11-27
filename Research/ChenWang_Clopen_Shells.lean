import Targets
import Defs.D_0001
import Defs.D_0010
import Specs.L_0031
import Proofs.L_0004
import Proofs.L_0032

/-!
# Clopen-Family CP Characterization & Clopen-Shell Decomposition for `Specs.L_0031`

This file proves clean structural theorems for zero-dimensional / clopen-neighborhood
spaces targeting `Specs.L_0031`:

1. `closurePreserving_iff_sUnion_isClosed_of_clopen`:
   For any family `𝓕` of clopen sets, `MSpace.ClosurePreserving 𝓕` is equivalent to
   `∀ 𝓖 ⊆ 𝓕, IsClosed (⋃₀ 𝓖)`.
2. `isM1_of_clopen_basis_sUnion_closed`:
   A `T1Space` with a `σ`-sUnion-closed basis of clopen sets is automatically `T3Space`
   and `MSpace.IsM1`.
3. `isM1_of_countable_clopen_M1_cover`:
   Any `T3Space` covered by countably many clopen `M₁` subspaces is `M₁`.
4. `isM1_of_clopen_shells_and_hasCPOuterBase`:
   If `y₀` has a decreasing clopen sequence `W n` with `⋂ n, W n = {y₀}`, every clopen
   shell `A 0 = (W 0)ᶜ`, `A (n + 1) = W n \ W (n + 1)` is `M₁`, and `HasCPOuterBase y₀`
   (or `HasSigmaCPLocalBase y₀`), then `Y` is `M₁`.
5. `L0031_or_shell_not_isM1`:
   Dichotomy for any non-`M₁` stratifiable space `Y` with a clopen `G_δ` point `y₀`:
   either `(Y, y₀)` directly witnesses `Specs.L_0031.stmt`, or some clopen shell
   `A n` is already a non-`M₁` stratifiable space.
-/

namespace Research.ChenWangClopenShells

open MSpace Set Topology

section ClopenCP

variable {Y : Type*} [TopologicalSpace Y]

/-- For a family `𝓕` of clopen sets, `ClosurePreserving 𝓕` is equivalent to every
subunion `⋃₀ 𝓖` (`𝓖 ⊆ 𝓕`) being closed. -/
theorem closurePreserving_iff_sUnion_isClosed_of_clopen {𝓕 : Set (Set Y)}
    (hcl : ∀ S ∈ 𝓕, IsClosed S) :
    MSpace.ClosurePreserving 𝓕 ↔ ∀ 𝓖 ⊆ 𝓕, IsClosed (⋃₀ 𝓖) := by
  constructor
  · intro hcp 𝓖 h𝓖
    rw [← closure_eq_iff_isClosed, hcp 𝓖 h𝓖]
    ext x
    simp only [mem_sUnion, mem_image]
    constructor
    · rintro ⟨_, ⟨S, hS𝓖, rfl⟩, hxS⟩
      rw [(hcl S (h𝓖 hS𝓖)).closure_eq] at hxS
      exact ⟨S, hS𝓖, hxS⟩
    · rintro ⟨S, hS𝓖, hxS⟩
      exact ⟨closure S, ⟨S, hS𝓖, rfl⟩, subset_closure hxS⟩
  · intro hclosed 𝓖 h𝓖
    rw [(hclosed 𝓖 h𝓖).closure_eq]
    ext x
    simp only [mem_sUnion, mem_image]
    constructor
    · rintro ⟨S, hS𝓖, hxS⟩
      exact ⟨closure S, ⟨S, hS𝓖, rfl⟩, subset_closure hxS⟩
    · rintro ⟨_, ⟨S, hS𝓖, rfl⟩, hxS⟩
      rw [(hcl S (h𝓖 hS𝓖)).closure_eq] at hxS
      exact ⟨S, hS𝓖, hxS⟩

/-- A `T1Space` admitting a `σ`-sUnion-closed basis of clopen sets is automatically
`T3Space` and `MSpace.IsM1`. -/
theorem isM1_of_clopen_basis_sUnion_closed [T1Space Y]
    (𝓑' : ℕ → Set (Set Y))
    (hopen : ∀ n, ∀ S ∈ 𝓑' n, IsOpen S ∧ IsClosed S)
    (hclosed : ∀ n, ∀ 𝓖 ⊆ 𝓑' n, IsClosed (⋃₀ 𝓖))
    (hnhds : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ n, ∃ S ∈ 𝓑' n, y ∈ S ∧ S ⊆ U) :
    MSpace.IsM1 Y := by
  have hReg : RegularSpace Y := by
    refine RegularSpace.of_exists_mem_nhds_isClosed_subset fun y s hs => ?_
    obtain ⟨U, hUs, hUopen, hyU⟩ := mem_nhds_iff.mp hs
    obtain ⟨n, S, hSn, hyS, hSU⟩ := hnhds y U hUopen hyU
    exact ⟨S, (hopen n S hSn).1.mem_nhds hyS, (hopen n S hSn).2, hSU.trans hUs⟩
  have hT3 : T3Space Y := ⟨⟩
  refine ⟨hT3, ⋃ n, 𝓑' n, ?_, ⟨𝓑', fun n =>
    (closurePreserving_iff_sUnion_isClosed_of_clopen fun S hS => (hopen n S hS).2).mpr (hclosed n),
    rfl⟩⟩
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro S hS
    obtain ⟨n, hSn⟩ := mem_iUnion.mp hS
    exact (hopen n S hSn).1
  · intro y U hyU hUopen
    obtain ⟨n, S, hSn, hyS, hSU⟩ := hnhds y U hUopen hyU
    exact ⟨S, mem_iUnion.mpr ⟨n, hSn⟩, hyS, hSU⟩

end ClopenCP

section ClopenCoversAndShells

/-- Helper: embedding a CP family from a clopen subspace `C` into `Y` preserves `ClosurePreserving`. -/
private theorem closurePreserving_image_of_clopen {Y : Type*} [TopologicalSpace Y]
    {C : Set Y} (hC_open : IsOpen C) (hC_closed : IsClosed C)
    {𝓕 : Set (Set ↥C)} (h𝓕_cp : MSpace.ClosurePreserving 𝓕) :
    MSpace.ClosurePreserving ((fun B : Set ↥C => ((↑) : ↥C → Y) '' B) '' 𝓕) := by
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · intro z hz
    have hsubC : ⋃₀ 𝓖 ⊆ C := by
      rintro y ⟨S, hS𝓖, hyS⟩
      obtain ⟨B, _, rfl⟩ := h𝓖 hS𝓖
      obtain ⟨w, _, rfl⟩ := hyS
      exact w.2
    have hzC : z ∈ C := hC_closed.closure_subset (closure_mono hsubC hz)
    let 𝓖C : Set (Set ↥C) := { B ∈ 𝓕 | ((↑) : ↥C → Y) '' B ∈ 𝓖 }
    have hz_cl : (⟨z, hzC⟩ : ↥C) ∈ closure (⋃₀ 𝓖C) := by
      rw [mem_closure_iff]
      intro O hO hzO
      have hOY : IsOpen (((↑) : ↥C → Y) '' O) := hC_open.isOpenMap_subtype_val O hO
      rw [mem_closure_iff] at hz
      obtain ⟨y, ⟨w, hwO, rfl⟩, S, hS𝓖, hwS⟩ := hz _ hOY ⟨⟨z, hzC⟩, hzO, rfl⟩
      obtain ⟨B, hB𝓕, rfl⟩ := h𝓖 hS𝓖
      obtain ⟨w', hw'B, heq⟩ := hwS
      have hwB : w ∈ B := (Subtype.ext heq.symm) ▸ hw'B
      exact ⟨w, hwO, B, ⟨hB𝓕, hS𝓖⟩, hwB⟩
    rw [h𝓕_cp 𝓖C (fun B hB => hB.1)] at hz_cl
    obtain ⟨_, ⟨B, ⟨_, hBG⟩, rfl⟩, hzB⟩ := hz_cl
    refine ⟨closure (((↑) : ↥C → Y) '' B), mem_image_of_mem _ hBG, ?_⟩
    rw [mem_closure_iff]
    intro O hO hzO
    rw [mem_closure_iff] at hzB
    obtain ⟨w, hwO, hwB⟩ :=
      hzB (((↑) : ↥C → Y) ⁻¹' O) (hO.preimage continuous_subtype_val) hzO
    exact ⟨(w : Y), hwO, w, hwB, rfl⟩
  · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Any `T3Space` covered by countably many clopen `M₁` subspaces is `M₁`. -/
theorem isM1_of_countable_clopen_M1_cover {Y : Type*} [TopologicalSpace Y] [T3Space Y]
    (C : ℕ → Set Y)
    (hC_clopen : ∀ n, IsOpen (C n) ∧ IsClosed (C n))
    (hC_cover : (⋃ n, C n) = univ)
    (hC_M1 : ∀ n, MSpace.IsM1 ↥(C n)) :
    MSpace.IsM1 Y := by
  have hbas_ex : ∀ n, ∃ 𝓑' : ℕ → Set (Set ↥(C n)),
      TopologicalSpace.IsTopologicalBasis (⋃ m, 𝓑' m) ∧
      ∀ m, MSpace.ClosurePreserving (𝓑' m) := by
    intro n
    obtain ⟨_, 𝓑, h𝓑bas, 𝓑', h𝓑'cp, rfl⟩ := hC_M1 n
    exact ⟨𝓑', h𝓑bas, h𝓑'cp⟩
  choose 𝓑' h𝓑'bas h𝓑'cp using hbas_ex
  let 𝓛 : ℕ → Set (Set Y) := fun r =>
    (fun B : Set ↥(C (Nat.unpair r).1) => ((↑) : ↥(C (Nat.unpair r).1) → Y) '' B) ''
      𝓑' (Nat.unpair r).1 (Nat.unpair r).2
  refine ⟨inferInstance, ⋃ r, 𝓛 r, ?_, ⟨𝓛, fun r =>
    closurePreserving_image_of_clopen (hC_clopen _).1 (hC_clopen _).2 (h𝓑'cp _ _), rfl⟩⟩
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro S hS
    obtain ⟨r, B, hB, rfl⟩ := by simpa [𝓛] using hS
    exact (hC_clopen _).1.isOpenMap_subtype_val B ((h𝓑'bas _).isOpen (mem_iUnion.mpr ⟨_, hB⟩))
  · intro y U hyU hUopen
    have hycov : y ∈ ⋃ n, C n := hC_cover.symm ▸ trivial
    obtain ⟨n, hyCn⟩ := mem_iUnion.mp hycov
    let UC : Set ↥(C n) := ((↑) : ↥(C n) → Y) ⁻¹' U
    obtain ⟨B, hB, hyB, hBUC⟩ :=
      (h𝓑'bas n).exists_subset_of_mem_open (show (⟨y, hyCn⟩ : ↥(C n)) ∈ UC from hyU)
        (hUopen.preimage continuous_subtype_val)
    obtain ⟨m, hBm⟩ := mem_iUnion.mp hB
    refine ⟨((↑) : ↥(C n) → Y) '' B, mem_iUnion.mpr ⟨Nat.pair n m, ?_⟩,
      ⟨⟨y, hyCn⟩, hyB, rfl⟩, ?_⟩
    · dsimp only [𝓛]
      rw [Nat.unpair_pair]
      exact ⟨B, hBm, rfl⟩
    · rintro _ ⟨w, hwB, rfl⟩
      exact hBUC hwB

/-- Clopen shells around a decreasing clopen sequence `W : ℕ → Set Y`:
`clopenShell W 0 = (W 0)ᶜ`, `clopenShell W (n + 1) = W n \ W (n + 1)`. -/
def clopenShell {Y : Type*} (W : ℕ → Set Y) : ℕ → Set Y
  | 0 => (W 0)ᶜ
  | n + 1 => W n \ W (n + 1)

theorem clopenShell_clopen {Y : Type*} [TopologicalSpace Y] {W : ℕ → Set Y}
    (hW : ∀ n, IsOpen (W n) ∧ IsClosed (W n)) (n : ℕ) :
    IsOpen (clopenShell W n) ∧ IsClosed (clopenShell W n) := by
  cases n with
  | zero => exact ⟨(hW 0).2.isOpen_compl, (hW 0).1.isClosed_compl⟩
  | succ n => exact ⟨(hW n).1.sdiff (hW (n + 1)).2, (hW n).2.sdiff (hW (n + 1)).1⟩

theorem mem_clopenShell_of_ne {Y : Type*} {y₀ : Y} {W : ℕ → Set Y}
    (hW_inter : (⋂ n, W n) = {y₀}) {z : Y} (hz : z ≠ y₀) :
    ∃ n : ℕ, z ∈ clopenShell W n := by
  have hnot : ∃ k : ℕ, z ∉ W k := by
    by_contra hall
    push Not at hall
    have : z ∈ ⋂ n, W n := mem_iInter.mpr hall
    rw [hW_inter, mem_singleton_iff] at this
    exact hz this
  classical
  let k := Nat.find hnot
  have hk_not : z ∉ W k := Nat.find_spec hnot
  cases hk : k with
  | zero =>
    rw [hk] at hk_not
    exact ⟨0, hk_not⟩
  | succ m =>
    have hm_in : z ∈ W m := by
      by_contra hnotm
      have hle : k ≤ m := Nat.find_min' hnot hnotm
      omega
    rw [hk] at hk_not
    exact ⟨m + 1, hm_in, hk_not⟩

/-- **Clopen-Shell `M₁` Assembly Theorem:**
If `Y` is `T3Space`, `W n` is a clopen sequence with `⋂ n, W n = {y₀}`, every clopen
shell `clopenShell W n` is `M₁`, and `y₀` has `HasCPOuterBase y₀`, then `Y` is `M₁`. -/
theorem isM1_of_clopen_shells_and_hasCPOuterBase {Y : Type*} [TopologicalSpace Y] [T3Space Y]
    {y₀ : Y} (W : ℕ → Set Y)
    (hW : ∀ n, IsOpen (W n) ∧ IsClosed (W n) ∧ y₀ ∈ W n)
    (hW_inter : (⋂ n, W n) = {y₀})
    (hShell_M1 : ∀ n, MSpace.IsM1 ↥(clopenShell W n))
    (hcp : Defs.D_0001.HasCPOuterBase y₀) :
    MSpace.IsM1 Y := by
  obtain ⟨𝓥, h𝓥o, h𝓥b, h𝓥cp⟩ := hcp
  have hbas_ex : ∀ n, ∃ 𝓑' : ℕ → Set (Set ↥(clopenShell W n)),
      TopologicalSpace.IsTopologicalBasis (⋃ m, 𝓑' m) ∧
      ∀ m, MSpace.ClosurePreserving (𝓑' m) := by
    intro n
    obtain ⟨_, 𝓑, h𝓑bas, 𝓑', h𝓑'cp, rfl⟩ := hShell_M1 n
    exact ⟨𝓑', h𝓑bas, h𝓑'cp⟩
  choose 𝓑' h𝓑'bas h𝓑'cp using hbas_ex
  let 𝓛 : ℕ → Set (Set Y) := fun r =>
    match r with
    | 0 => 𝓥
    | k + 1 =>
      (fun B : Set ↥(clopenShell W (Nat.unpair k).1) =>
        ((↑) : ↥(clopenShell W (Nat.unpair k).1) → Y) '' B) ''
        𝓑' (Nat.unpair k).1 (Nat.unpair k).2
  refine ⟨inferInstance, ⋃ r, 𝓛 r, ?_, ⟨𝓛, ?_, rfl⟩⟩
  · apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro S hS
      obtain ⟨r, hSr⟩ := mem_iUnion.mp hS
      cases r with
      | zero => exact (h𝓥o S hSr).1
      | succ k =>
        obtain ⟨B, hB, rfl⟩ := hSr
        exact (clopenShell_clopen (fun n => ⟨(hW n).1, (hW n).2.1⟩) _).1.isOpenMap_subtype_val
          B ((h𝓑'bas _).isOpen (mem_iUnion.mpr ⟨_, hB⟩))
    · intro z U hzU hUopen
      by_cases hzy : z = y₀
      · subst hzy
        obtain ⟨V, hV, hVU⟩ := h𝓥b U hUopen hzU
        exact ⟨V, mem_iUnion.mpr ⟨0, hV⟩, (h𝓥o V hV).2, hVU⟩
      · obtain ⟨n, hzn⟩ := mem_clopenShell_of_ne hW_inter hzy
        let UC : Set ↥(clopenShell W n) := ((↑) : ↥(clopenShell W n) → Y) ⁻¹' U
        obtain ⟨B, hB, hzB, hBUC⟩ :=
          (h𝓑'bas n).exists_subset_of_mem_open (show (⟨z, hzn⟩ : ↥(clopenShell W n)) ∈ UC from hzU)
            (hUopen.preimage continuous_subtype_val)
        obtain ⟨m, hBm⟩ := mem_iUnion.mp hB
        refine ⟨((↑) : ↥(clopenShell W n) → Y) '' B, mem_iUnion.mpr ⟨Nat.pair n m + 1, ?_⟩,
          ⟨⟨z, hzn⟩, hzB, rfl⟩, ?_⟩
        · dsimp only [𝓛]
          rw [Nat.unpair_pair]
          exact ⟨B, hBm, rfl⟩
        · rintro _ ⟨w, hwB, rfl⟩
          exact hBUC hwB
  · intro r
    cases r with
    | zero => exact h𝓥cp
    | succ k =>
      have hcl := clopenShell_clopen (fun n => ⟨(hW n).1, (hW n).2.1⟩) (Nat.unpair k).1
      exact closurePreserving_image_of_clopen hcl.1 hcl.2 (h𝓑'cp _ _)

/-- **Clopen-Shell Dichotomy for `Specs.L_0031`:**
In ANY non-`M₁` stratifiable space `Y` with a clopen `G_δ` point `y₀` (`⋂ n, W n = {y₀}`),
either `(Y, y₀)` directly witnesses `Specs.L_0031.stmt`, OR some clopen shell
`clopenShell W n` is already a non-`M₁` space. -/
theorem L0031_or_shell_not_isM1 {Y : Type} [TopologicalSpace Y]
    (hStrat : MSpace.IsStratifiable Y) (hnotM1 : ¬ MSpace.IsM1 Y)
    {y₀ : Y} (W : ℕ → Set Y)
    (hW : ∀ n, IsOpen (W n) ∧ IsClosed (W n) ∧ y₀ ∈ W n)
    (hW_inter : (⋂ n, W n) = {y₀}) :
    Specs.L_0031.stmt ∨ ∃ n : ℕ, ¬ MSpace.IsM1 ↥(clopenShell W n) := by
  have hT3 : T3Space Y := ((Proofs.L_0004.main Y).mpr hStrat).1
  by_cases hcp : Defs.D_0001.HasCPOuterBase y₀
  · right
    by_contra hall
    push Not at hall
    exact hnotM1 (isM1_of_clopen_shells_and_hasCPOuterBase W hW hW_inter hall hcp)
  · left
    exact ⟨Y, inferInstance, hStrat, y₀, ⟨W, hW, hW_inter⟩, hcp⟩

end ClopenCoversAndShells

end Research.ChenWangClopenShells
