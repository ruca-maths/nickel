import Targets
import Defs.D_0001
import Defs.D_0010
import Specs.L_0031

/-!
# Localization & No-Go Structure Theorems for `HasCPOuterBase` and `Specs.L_0031`

This file proves general topological localization and necessary-condition theorems
for `Defs.D_0001.HasCPOuterBase` and `Specs.L_0031`:

1. `hasCPOuterBase_inter_clopen`: intersecting a CP outer base at `y₀` with a clopen
   neighborhood `W` preserves `HasCPOuterBase y₀` (every member lies inside `W`).
2. `hasCPOuterBase_iff_clopen_subtype`: `HasCPOuterBase y₀` in `Y` is equivalent to
   `HasCPOuterBase ⟨y₀, hy₀⟩` in any clopen subspace `W ∋ y₀`.
3. `not_hasCPOuterBase_local_escape`: if `¬ HasCPOuterBase y₀`, then inside EVERY
   clopen neighborhood `W` of `y₀`, every open outer base at `y₀` has a CP failure
   witness `z ∈ W \ {y₀}`.
4. `hasCPOuterBase_of_isolated_compl`: if every point `z ≠ y₀` is isolated, then
   `HasCPOuterBase y₀` holds unconditionally (in ANY topological space).
5. `hasCPOuterBase_of_clopen_nhd_isolated_compl` & `L0031_y_mem_closure_nonisolated`:
   in ANY `Specs.L_0031` counterexample `(Y, y₀)`, `y₀` MUST lie in the closure of the
   set of OTHER non-isolated points `{ z : Y | z ≠ y₀ ∧ ¬ IsOpen ({z} : Set Y) }`.
6. `hasCPOuterBase_of_no_nonisolated_hole_interior` (**No-Go Theorem 2**):
   In ANY topological space with a laminar open partition `W n y` (`⋂ n, W n y₀ = {y₀}`)
   and a neighborhood base `{ W n y₀ \ D | D ∈ Holes }` at `y₀`, if there exists `N`
   such that no hole `D ∈ Holes` contains a non-isolated point in `interior D ∩ W N y₀`,
   then `HasCPOuterBase y₀` holds.
   Contrapositively (`L0031_exists_nonisolated_hole_interior`), any laminar hole-carving
   witness to `Specs.L_0031` MUST have, inside EVERY `W N y₀`, a hole `D ∈ Holes` whose
   interior contains a non-isolated point `z ∈ W N y₀ \ {y₀}`.
-/

namespace Research.ChenWangOuterBaseLocalization

open MSpace Set Topology

section ClopenLocalization

variable {Y : Type*} [TopologicalSpace Y]

/-- Restricting a CP outer base at `y₀` to a clopen neighborhood `W` of `y₀`
produces a CP outer base at `y₀` whose members are all subsets of `W`. -/
theorem hasCPOuterBase_inter_clopen {y₀ : Y} {W : Set Y}
    (hW_open : IsOpen W) (hW_closed : IsClosed W) (hy₀W : y₀ ∈ W)
    (hcp : Defs.D_0001.HasCPOuterBase y₀) :
    ∃ 𝓥 : Set (Set Y),
      (∀ V ∈ 𝓥, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ W) ∧
      (∀ U : Set Y, IsOpen U → y₀ ∈ U → ∃ V ∈ 𝓥, V ⊆ U) ∧
      MSpace.ClosurePreserving 𝓥 := by
  obtain ⟨𝓥₀, h𝓥₀_open, h𝓥₀_base, h𝓥₀_cp⟩ := hcp
  refine ⟨{ S : Set Y | ∃ V ∈ 𝓥₀, S = V ∩ W }, ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨(h𝓥₀_open V hV).1.inter hW_open, ⟨(h𝓥₀_open V hV).2, hy₀W⟩, inter_subset_right⟩
  · intro U hU hy₀U
    obtain ⟨V, hV, hVU⟩ := h𝓥₀_base U hU hy₀U
    exact ⟨V ∩ W, ⟨V, hV, rfl⟩, inter_subset_left.trans hVU⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      let 𝓖₀ : Set (Set Y) := { V ∈ 𝓥₀ | V ∩ W ∈ 𝓖 }
      have hsub : ⋃₀ 𝓖 ⊆ (⋃₀ 𝓖₀) ∩ W := by
        rintro x ⟨S, hS𝓖, hxS⟩
        obtain ⟨V, hV, rfl⟩ := h𝓖 hS𝓖
        exact ⟨⟨V, ⟨hV, hS𝓖⟩, hxS.1⟩, hxS.2⟩
      have hz_inter := closure_mono hsub hz
      have hz_left : z ∈ closure (⋃₀ 𝓖₀) := closure_mono inter_subset_left hz_inter
      have hzW : z ∈ W := hW_closed.closure_subset (closure_mono inter_subset_right hz_inter)
      rw [h𝓥₀_cp 𝓖₀ (fun V hV => hV.1)] at hz_left
      obtain ⟨_, ⟨V, ⟨_, hVG⟩, rfl⟩, hzV⟩ := hz_left
      refine ⟨closure (V ∩ W), mem_image_of_mem _ hVG, ?_⟩
      rw [inter_comm]
      exact hW_open.inter_closure ⟨hzW, hzV⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- `HasCPOuterBase y₀` is a purely local property: it holds in `Y` if and only if
it holds in any clopen subspace `W` containing `y₀`. -/
theorem hasCPOuterBase_iff_clopen_subtype {y₀ : Y} {W : Set Y}
    (hW_open : IsOpen W) (hW_closed : IsClosed W) (hy₀W : y₀ ∈ W) :
    Defs.D_0001.HasCPOuterBase y₀ ↔
      Defs.D_0001.HasCPOuterBase (⟨y₀, hy₀W⟩ : W) := by
  constructor
  · intro hcp
    obtain ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩ :=
      hasCPOuterBase_inter_clopen hW_open hW_closed hy₀W hcp
    refine ⟨{ S : Set W | ∃ V ∈ 𝓥, S = ((↑) : W → Y) ⁻¹' V }, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      exact ⟨(h𝓥_open V hV).1.preimage continuous_subtype_val, (h𝓥_open V hV).2.1⟩
    · intro U hU hy₀U
      have hU_open_Y : IsOpen (((↑) : W → Y) '' U) := hW_open.isOpenMap_subtype_val U hU
      have hy₀_img : y₀ ∈ ((↑) : W → Y) '' U := ⟨⟨y₀, hy₀W⟩, hy₀U, rfl⟩
      obtain ⟨V, hV, hVU⟩ := h𝓥_base _ hU_open_Y hy₀_img
      refine ⟨((↑) : W → Y) ⁻¹' V, ⟨V, hV, rfl⟩, ?_⟩
      intro x hx
      obtain ⟨x', hx'U, hx'eq⟩ := hVU hx
      exact (Subtype.ext hx'eq.symm) ▸ hx'U
    · intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro z hz
        let 𝓖Y : Set (Set Y) := { V ∈ 𝓥 | ((↑) : W → Y) ⁻¹' V ∈ 𝓖 }
        have hzY : (z : Y) ∈ closure (⋃₀ 𝓖Y) := by
          rw [mem_closure_iff]
          intro O hO hzO
          have hz_sub : z ∈ closure (⋃₀ 𝓖) := hz
          rw [mem_closure_iff] at hz_sub
          obtain ⟨w, hwO, S, hS𝓖, hwS⟩ :=
            hz_sub (((↑) : W → Y) ⁻¹' O) (hO.preimage continuous_subtype_val) hzO
          obtain ⟨V, hV, rfl⟩ := h𝓖 hS𝓖
          exact ⟨(w : Y), hwO, V, ⟨hV, hS𝓖⟩, hwS⟩
        rw [h𝓥_cp 𝓖Y (fun V hV => hV.1)] at hzY
        obtain ⟨_, ⟨V, ⟨_, hVG⟩, rfl⟩, hzV⟩ := hzY
        refine ⟨closure (((↑) : W → Y) ⁻¹' V), mem_image_of_mem _ hVG, ?_⟩
        rw [mem_closure_iff]
        intro O hO hzO
        have hOY : IsOpen (((↑) : W → Y) '' O) := hW_open.isOpenMap_subtype_val O hO
        rw [mem_closure_iff] at hzV
        obtain ⟨x, ⟨w, hwO, rfl⟩, hxV⟩ := hzV _ hOY ⟨z, hzO, rfl⟩
        exact ⟨w, hwO, hxV⟩
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  · intro hcp
    obtain ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩ := hcp
    refine ⟨{ S : Set Y | ∃ V ∈ 𝓥, S = ((↑) : W → Y) '' V }, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      exact ⟨hW_open.isOpenMap_subtype_val V (h𝓥_open V hV).1, ⟨⟨y₀, hy₀W⟩, (h𝓥_open V hV).2, rfl⟩⟩
    · intro U hU hy₀U
      obtain ⟨V, hV, hVU⟩ :=
        h𝓥_base (((↑) : W → Y) ⁻¹' U) (hU.preimage continuous_subtype_val) hy₀U
      refine ⟨((↑) : W → Y) '' V, ⟨V, hV, rfl⟩, ?_⟩
      rintro _ ⟨x, hxV, rfl⟩
      exact hVU hxV
    · intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro z hz
        have hsubW : ⋃₀ 𝓖 ⊆ W := by
          rintro x ⟨S, hS𝓖, hxS⟩
          obtain ⟨V, _, rfl⟩ := h𝓖 hS𝓖
          obtain ⟨w, _, rfl⟩ := hxS
          exact w.2
        have hzW : z ∈ W := hW_closed.closure_subset (closure_mono hsubW hz)
        let 𝓖W : Set (Set W) := { V ∈ 𝓥 | ((↑) : W → Y) '' V ∈ 𝓖 }
        have hz_sub : (⟨z, hzW⟩ : W) ∈ closure (⋃₀ 𝓖W) := by
          rw [mem_closure_iff]
          intro O hO hzO
          have hOY : IsOpen (((↑) : W → Y) '' O) := hW_open.isOpenMap_subtype_val O hO
          rw [mem_closure_iff] at hz
          obtain ⟨x, ⟨w, hwO, rfl⟩, S, hS𝓖, hwS⟩ := hz _ hOY ⟨⟨z, hzW⟩, hzO, rfl⟩
          obtain ⟨V, hV, rfl⟩ := h𝓖 hS𝓖
          obtain ⟨w', hw'V, hw'eq⟩ := hwS
          have hwV : w ∈ V := (Subtype.ext hw'eq.symm) ▸ hw'V
          exact ⟨w, hwO, V, ⟨hV, hS𝓖⟩, hwV⟩
        rw [h𝓥_cp 𝓖W (fun V hV => hV.1)] at hz_sub
        obtain ⟨_, ⟨V, ⟨_, hVG⟩, rfl⟩, hzV⟩ := hz_sub
        refine ⟨closure (((↑) : W → Y) '' V), mem_image_of_mem _ hVG, ?_⟩
        rw [mem_closure_iff]
        intro O hO hzO
        rw [mem_closure_iff] at hzV
        obtain ⟨w, hwO, hwV⟩ :=
          hzV (((↑) : W → Y) ⁻¹' O) (hO.preimage continuous_subtype_val) hzO
        exact ⟨(w : Y), hwO, w, hwV, rfl⟩
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- If `¬ HasCPOuterBase y₀`, then for ANY clopen neighborhood `W` of `y₀` and ANY open
outer base `𝓥` at `y₀`, the restricted family `{ V ∩ W | V ∈ 𝓥 }` fails to be
closure-preserving at some point `z ∈ W \ {y₀}`. -/
theorem not_hasCPOuterBase_local_escape {y₀ : Y} {W : Set Y}
    (hW_open : IsOpen W) (hW_closed : IsClosed W) (hy₀W : y₀ ∈ W)
    (hno : ¬ Defs.D_0001.HasCPOuterBase y₀)
    (𝓥 : Set (Set Y))
    (h𝓥_open : ∀ V ∈ 𝓥, IsOpen V ∧ y₀ ∈ V)
    (h𝓥_base : ∀ U : Set Y, IsOpen U → y₀ ∈ U → ∃ V ∈ 𝓥, V ⊆ U) :
    ∃ 𝓖 ⊆ { S : Set Y | ∃ V ∈ 𝓥, S = V ∩ W },
      ∃ z ∈ W \ ({y₀} : Set Y),
        z ∈ closure (⋃₀ 𝓖) ∧ ∀ S ∈ 𝓖, z ∉ closure S := by
  let 𝓥W : Set (Set Y) := { S : Set Y | ∃ V ∈ 𝓥, S = V ∩ W }
  have hnot_cp : ¬ MSpace.ClosurePreserving 𝓥W := by
    intro hcp
    apply hno
    refine ⟨𝓥W, ?_, ?_, hcp⟩
    · rintro _ ⟨V, hV, rfl⟩
      exact ⟨(h𝓥_open V hV).1.inter hW_open, (h𝓥_open V hV).2, hy₀W⟩
    · intro U hU hy₀U
      obtain ⟨V, hV, hVU⟩ := h𝓥_base U hU hy₀U
      exact ⟨V ∩ W, ⟨V, hV, rfl⟩, inter_subset_left.trans hVU⟩
  unfold MSpace.ClosurePreserving at hnot_cp
  push Not at hnot_cp
  obtain ⟨𝓖, h𝓖, hne⟩ := hnot_cp
  have hsup : ⋃₀ (closure '' 𝓖) ⊆ closure (⋃₀ 𝓖) :=
    sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  have hnot_sub : ¬ closure (⋃₀ 𝓖) ⊆ ⋃₀ (closure '' 𝓖) :=
    fun hsub => hne (Subset.antisymm hsub hsup)
  rw [not_subset] at hnot_sub
  obtain ⟨z, hz_cl, hz_not⟩ := hnot_sub
  have hz_not_each : ∀ S ∈ 𝓖, z ∉ closure S :=
    fun S hS hzS => hz_not ⟨closure S, mem_image_of_mem _ hS, hzS⟩
  have hsubW : ⋃₀ 𝓖 ⊆ W := by
    rintro x ⟨S, hS𝓖, hxS⟩
    obtain ⟨V, _, rfl⟩ := h𝓖 hS𝓖
    exact hxS.2
  have hzW : z ∈ W := hW_closed.closure_subset (closure_mono hsubW hz_cl)
  have hzy₀ : z ≠ y₀ := by
    rintro rfl
    rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨S, hS𝓖⟩
    · simp at hz_cl
    · obtain ⟨V, hV, rfl⟩ := h𝓖 hS𝓖
      exact hz_not_each (V ∩ W) hS𝓖 (subset_closure ⟨(h𝓥_open V hV).2, hy₀W⟩)
  exact ⟨𝓖, h𝓖, z, ⟨hzW, hzy₀⟩, hz_cl, hz_not_each⟩

end ClopenLocalization

section IsolatedNoGo

variable {Y : Type*} [TopologicalSpace Y]

/-- **General Isolated-Complement No-Go Theorem:**
In ANY topological space `Y`, if every point `z ≠ y₀` is isolated, then `y₀`
admits a closure-preserving open outer base (namely the family of all open
neighborhoods of `y₀`). -/
theorem hasCPOuterBase_of_isolated_compl {y₀ : Y}
    (hiso : ∀ z : Y, z ≠ y₀ → IsOpen ({z} : Set Y)) :
    Defs.D_0001.HasCPOuterBase y₀ := by
  refine ⟨{ U : Set Y | IsOpen U ∧ y₀ ∈ U }, fun _ hU => hU, fun U hU hy₀ => ⟨U, ⟨hU, hy₀⟩, Subset.rfl⟩, ?_⟩
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · intro z hz
    by_cases hzy : z = y₀
    · subst hzy
      rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨U, hU⟩
      · simp at hz
      · exact ⟨closure U, mem_image_of_mem _ hU, subset_closure (h𝓖 hU).2⟩
    · rw [mem_closure_iff] at hz
      obtain ⟨w, hwz, U, hU, hwU⟩ := hz {z} (hiso z hzy) rfl
      rw [mem_singleton_iff] at hwz
      exact ⟨closure U, mem_image_of_mem _ hU, subset_closure (hwz ▸ hwU)⟩
  · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Local Isolated-Complement No-Go Theorem:
if `y₀` has a clopen neighborhood `W` in which every point `z ≠ y₀` is isolated,
then `HasCPOuterBase y₀` holds. -/
theorem hasCPOuterBase_of_clopen_nhd_isolated_compl {y₀ : Y} {W : Set Y}
    (hW_open : IsOpen W) (hW_closed : IsClosed W) (hy₀W : y₀ ∈ W)
    (hiso : ∀ z ∈ W, z ≠ y₀ → IsOpen ({z} : Set Y)) :
    Defs.D_0001.HasCPOuterBase y₀ := by
  rw [hasCPOuterBase_iff_clopen_subtype hW_open hW_closed hy₀W]
  apply hasCPOuterBase_of_isolated_compl
  intro z hzne
  have hne : (z : Y) ≠ y₀ := fun h => hzne (Subtype.ext h)
  have hEq : ({z} : Set W) = ((↑) : W → Y) ⁻¹' {(z : Y)} := by
    ext w
    simp [Subtype.ext_iff]
  rw [hEq]
  exact (hiso z.1 z.2 hne).preimage continuous_subtype_val

/-- **Necessary Condition for `Specs.L_0031`:**
Whenever `y₀` has a clopen neighborhood base of a single point `⋂ n, W n = {y₀}`
(or even just any clopen `W` containing `y₀`) and `¬ HasCPOuterBase y₀`, every clopen
neighborhood `W` of `y₀` contains a non-isolated point `z ≠ y₀`.
In particular, in any `Specs.L_0031` space with `W` clopen, `W n \ {y₀}` contains a
non-isolated point for every `n`. -/
theorem exists_nonisolated_in_clopen_of_not_hasCPOuterBase {y₀ : Y} {W : Set Y}
    (hW_open : IsOpen W) (hW_closed : IsClosed W) (hy₀W : y₀ ∈ W)
    (hno : ¬ Defs.D_0001.HasCPOuterBase y₀) :
    ∃ z ∈ W, z ≠ y₀ ∧ ¬ IsOpen ({z} : Set Y) := by
  by_contra h
  push Not at h
  exact hno (hasCPOuterBase_of_clopen_nhd_isolated_compl hW_open hW_closed hy₀W h)

end IsolatedNoGo

section LaminarHoleNoGo

variable {Y : Type*} [TopologicalSpace Y]

/-- **No-Go Theorem 2 (Laminar Hole-Interior Characterization):**
Let `W : ℕ → Y → Set Y` be a decreasing laminar open partition (`⋂ n, W n y₀ = {y₀}`),
and suppose `{ W n y₀ \ D | n : ℕ, D ∈ Holes }` is an open neighborhood base at `y₀`.
If there exists a level `N` such that no hole `D ∈ Holes` has a **non-isolated** point
in `interior D ∩ W N y₀`, then `Defs.D_0001.HasCPOuterBase y₀` holds!

This strictly generalizes `idealHoleSystem_hasCPOuterBase`: it applies to ANY
topological space (no `HoleSystem` or `T1Space` assumption needed), and allows
holes to meet non-isolated points as long as they do not contain a neighborhood of
any non-isolated point inside `W N y₀`. -/
theorem hasCPOuterBase_of_no_nonisolated_hole_interior
    (W : ℕ → Y → Set Y)
    (hmem : ∀ n y, y ∈ W n y)
    (hdec : ∀ n y, W (n + 1) y ⊆ W n y)
    (hpart : ∀ n x y, y ∈ W n x → W n y = W n x)
    (hW_open : ∀ n y, IsOpen (W n y))
    (y₀ : Y)
    (hinter : (⋂ n, W n y₀) = {y₀})
    (Holes : Set (Set Y))
    (hbasic_open : ∀ n, ∀ D ∈ Holes, IsOpen (W n y₀ \ D) ∧ y₀ ∈ W n y₀ \ D)
    (hbasic_base : ∀ U : Set Y, IsOpen U → y₀ ∈ U → ∃ n, ∃ D ∈ Holes, W n y₀ \ D ⊆ U)
    (hno_noniso : ∃ N : ℕ, ∀ D ∈ Holes, ∀ z ∈ W N y₀, z ∈ interior D → IsOpen ({z} : Set Y)) :
    Defs.D_0001.HasCPOuterBase y₀ := by
  have hanti : ∀ {m n : ℕ}, m ≤ n → ∀ y, W n y ⊆ W m y := by
    intro m n hmn y
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hdec _ y).trans ih
  obtain ⟨N, hN⟩ := hno_noniso
  refine ⟨{ S : Set Y | ∃ n, N ≤ n ∧ ∃ D ∈ Holes, S = W n y₀ \ D }, ?_, ?_, ?_⟩
  · rintro _ ⟨n, _, D, hD, rfl⟩
    exact hbasic_open n D hD
  · intro U hU hy₀U
    obtain ⟨m, D, hD, hsub⟩ := hbasic_base U hU hy₀U
    refine ⟨W (max m N) y₀ \ D, ⟨max m N, le_max_right m N, D, hD, rfl⟩, ?_⟩
    exact (sdiff_subset_sdiff_left (hanti (le_max_left m N) y₀)).trans hsub
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      by_cases hzy : z = y₀
      · subst hzy
        rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨S, hS𝓖⟩
        · simp at hz
        · obtain ⟨n, _, D, hD, rfl⟩ := h𝓖 hS𝓖
          exact ⟨closure (W n z \ D), mem_image_of_mem _ hS𝓖, subset_closure (hbasic_open n D hD).2⟩
      · by_cases hz_iso : IsOpen ({z} : Set Y)
        · rw [mem_closure_iff] at hz
          obtain ⟨w, hwz, S, hS𝓖, hwS⟩ := hz {z} hz_iso rfl
          rw [mem_singleton_iff] at hwz
          exact ⟨closure S, mem_image_of_mem _ hS𝓖, subset_closure (hwz ▸ hwS)⟩
        · have hz_not : z ∉ ⋂ n, W n y₀ := by rw [hinter]; exact hzy
          rw [mem_iInter] at hz_not
          push Not at hz_not
          obtain ⟨M, hzWM⟩ := hz_not
          rw [mem_closure_iff] at hz
          obtain ⟨w, hwWMz, S, hS𝓖, hwS⟩ := hz (W M z) (hW_open M z) (hmem M z)
          obtain ⟨n, hNn, D, hD, rfl⟩ := h𝓖 hS𝓖
          have hlt : n < M := by
            by_contra hge
            have hwWMy : w ∈ W M y₀ := hanti (not_lt.mp hge) y₀ hwS.1
            have h1 : W M w = W M z := hpart M z w hwWMz
            have h2 : W M w = W M y₀ := hpart M y₀ w hwWMy
            exact hzWM ((h1.symm.trans h2) ▸ hmem M z)
          have hwWnz : w ∈ W n z := hanti hlt.le z hwWMz
          have h1 : W n w = W n z := hpart n z w hwWnz
          have h2 : W n w = W n y₀ := hpart n y₀ w hwS.1
          have hzWny : z ∈ W n y₀ := (h1.symm.trans h2) ▸ hmem n z
          have hzWNy : z ∈ W N y₀ := hanti hNn y₀ hzWny
          have hz_not_int : z ∉ interior D := fun hint => hz_iso (hN D hD z hzWNy hint)
          refine ⟨closure (W n y₀ \ D), mem_image_of_mem _ hS𝓖, ?_⟩
          rw [mem_closure_iff]
          intro O hO hzO
          have hnot_sub : ¬ O ∩ W n y₀ ⊆ D := by
            intro hsub
            exact hz_not_int (mem_interior.mpr ⟨O ∩ W n y₀, hsub, hO.inter (hW_open n y₀), ⟨hzO, hzWny⟩⟩)
          rw [not_subset] at hnot_sub
          obtain ⟨x, ⟨hxO, hxWny⟩, hxD⟩ := hnot_sub
          exact ⟨x, hxO, hxWny, hxD⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Contrapositive of No-Go Theorem 2:
In any laminar hole-carving space with `¬ HasCPOuterBase y₀`, for EVERY `N : ℕ`,
there exists a hole `D ∈ Holes` and a **non-isolated** point `z ∈ W N y₀ \ {y₀}`
such that `z ∈ interior D`. -/
theorem exists_nonisolated_hole_interior_of_not_hasCPOuterBase
    (W : ℕ → Y → Set Y)
    (hmem : ∀ n y, y ∈ W n y)
    (hdec : ∀ n y, W (n + 1) y ⊆ W n y)
    (hpart : ∀ n x y, y ∈ W n x → W n y = W n x)
    (hW_open : ∀ n y, IsOpen (W n y))
    (y₀ : Y)
    (hinter : (⋂ n, W n y₀) = {y₀})
    (Holes : Set (Set Y))
    (hbasic_open : ∀ n, ∀ D ∈ Holes, IsOpen (W n y₀ \ D) ∧ y₀ ∈ W n y₀ \ D)
    (hbasic_base : ∀ U : Set Y, IsOpen U → y₀ ∈ U → ∃ n, ∃ D ∈ Holes, W n y₀ \ D ⊆ U)
    (hno : ¬ Defs.D_0001.HasCPOuterBase y₀) :
    ∀ N : ℕ, ∃ D ∈ Holes, ∃ z ∈ W N y₀, z ≠ y₀ ∧ ¬ IsOpen ({z} : Set Y) ∧ z ∈ interior D := by
  intro N
  by_contra h
  push Not at h
  apply hno
  refine hasCPOuterBase_of_no_nonisolated_hole_interior W hmem hdec hpart hW_open y₀ hinter
    Holes hbasic_open hbasic_base ⟨N, ?_⟩
  intro D hD z hzWN hint
  have hzy : z ≠ y₀ := by
    rintro rfl
    exact (hbasic_open N D hD).2.2 (interior_subset hint)
  by_contra hnot_iso
  exact h D hD z hzWN hzy hnot_iso hint

end LaminarHoleNoGo

end Research.ChenWangOuterBaseLocalization
