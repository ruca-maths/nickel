import Targets
import Defs.D_0001
import Specs.L_0031
import Proofs.L_0004
import Proofs.L_0017
import Proofs.L_0029
import Proofs.L_0032
import Proofs.R_0009
import Proofs.R_0010

/-!
# Master Reduction Criteria for `Specs.L_0031` and `¬ MSpace.Goals.Tinf_M3_imp_M1`

This file packages the exact sufficient conditions needed to resolve `Specs.L_0031`
(and hence `¬ Tinf` via the parent machine's verified reductions `R_0010`, `R_0009`,
`L_0032`, `L_0029`, `L_0004`) using a clopen `g`-function as in Chen–Wang Section 7
and an escape witness as in Chen–Wang Section 9 (Proposition 9.5):

1. `isStratifiable_of_clopen_g_function`:
   A monotone clopen `g`-function `g : ℕ → Y → Set Y` with `⋂ n, g n x = {x}` and
   the pointwise disjoint-neighborhood separation property automatically implies
   `T1Space Y` and `MSpace.IsStratifiable Y` (via `Proofs.L_0017`).
2. `not_hasCPOuterBase_of_escape`:
   If every open local base `𝓥` at `y₀` admits a subfamily `𝒢 ⊆ 𝓥` and a point `z`
   with `z ∈ closure (⋃₀ 𝒢)` and `∀ V ∈ 𝒢, z ∉ closure V`, then
   `¬ Defs.D_0001.HasCPOuterBase y₀`.
3. `L0031_of_clopen_g_function_and_escape`:
   Combines (1) and (2) to directly conclude `Specs.L_0031.stmt`.
4. `not_Tinf_of_clopen_g_function_and_escape`:
   Composes (3) with `Proofs.R_0010`, `Proofs.L_0032`, `Proofs.R_0009`,
   `Proofs.L_0029`, `Proofs.L_0004` to directly conclude `¬ MSpace.Goals.Tinf_M3_imp_M1`.
-/

namespace Research.ChenWangL0031

open MSpace Set Topology

/-- Theorem 1: A monotone clopen `g`-function with `⋂ n, g n x = {x}` and
pointwise disjoint-neighborhood separation yields `MSpace.IsStratifiable Y`. -/
theorem isStratifiable_of_clopen_g_function
    (Y : Type) [TopologicalSpace Y]
    (g : ℕ → Y → Set Y)
    (hg_clopen : ∀ n x, IsOpen (g n x) ∧ IsClosed (g n x) ∧ x ∈ g n x)
    (hg_dec : ∀ n x, g (n + 1) x ⊆ g n x)
    (hg_inter : ∀ x, (⋂ n, g n x) = {x})
    (hg_sep : ∀ H : Set Y, IsClosed H → ∀ x ∉ H,
      ∃ n, ∃ O : Set Y, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ H, Disjoint O (g n y)) :
    MSpace.IsStratifiable Y := by
  have hT1 : T1Space Y := ⟨fun x => by
    rw [← hg_inter x]
    exact isClosed_iInter fun n => (hg_clopen n x).2.1⟩
  refine ⟨hT1, Proofs.L_0017.main Y ⟨g, fun n x => ⟨(hg_clopen n x).1, (hg_clopen n x).2.2⟩,
    hg_dec, ?_⟩⟩
  intro H hH x hxH
  obtain ⟨n, O, hO_open, hxO, hO_disj⟩ := hg_sep H hH x hxH
  refine ⟨n, fun hx_cl => ?_⟩
  obtain ⟨w, hwO, hwU⟩ := mem_closure_iff.mp hx_cl O hO_open hxO
  obtain ⟨y, hyH, hwy⟩ := mem_iUnion₂.mp hwU
  exact Set.disjoint_left.mp (hO_disj y hyH) hwO hwy

/-- Theorem 2: Abstract escape criterion for `¬ Defs.D_0001.HasCPOuterBase y₀`. -/
theorem not_hasCPOuterBase_of_escape
    (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (hesc : ∀ 𝓥 : Set (Set Y),
      (∀ V ∈ 𝓥, IsOpen V ∧ y₀ ∈ V) →
      (∀ U : Set Y, IsOpen U → y₀ ∈ U → ∃ V ∈ 𝓥, V ⊆ U) →
      ∃ 𝒢 ⊆ 𝓥, ∃ z : Y, z ∈ closure (⋃₀ 𝒢) ∧ ∀ V ∈ 𝒢, z ∉ closure V) :
    ¬ Defs.D_0001.HasCPOuterBase y₀ := by
  rintro ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩
  obtain ⟨𝒢, h𝒢sub, z, hz_cl, hz_not⟩ := hesc 𝓥 h𝓥_open h𝓥_base
  rw [h𝓥_cp 𝒢 h𝒢sub] at hz_cl
  obtain ⟨_, ⟨V, hV𝒢, rfl⟩, hzV⟩ := hz_cl
  exact hz_not V hV𝒢 hzV

/-- Theorem 3 (Master Reduction of `Specs.L_0031.stmt`):
A space `Y` with a stratifiable clopen `g`-function and an escape point `y₀`
satisfies `Specs.L_0031.stmt`. -/
theorem L0031_of_clopen_g_function_and_escape
    (Y : Type) [TopologicalSpace Y]
    (g : ℕ → Y → Set Y)
    (hg_clopen : ∀ n x, IsOpen (g n x) ∧ IsClosed (g n x) ∧ x ∈ g n x)
    (hg_dec : ∀ n x, g (n + 1) x ⊆ g n x)
    (hg_inter : ∀ x, (⋂ n, g n x) = {x})
    (hg_sep : ∀ H : Set Y, IsClosed H → ∀ x ∉ H,
      ∃ n, ∃ O : Set Y, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ H, Disjoint O (g n y))
    (y₀ : Y)
    (hesc : ∀ 𝓥 : Set (Set Y),
      (∀ V ∈ 𝓥, IsOpen V ∧ y₀ ∈ V) →
      (∀ U : Set Y, IsOpen U → y₀ ∈ U → ∃ V ∈ 𝓥, V ⊆ U) →
      ∃ 𝒢 ⊆ 𝓥, ∃ z : Y, z ∈ closure (⋃₀ 𝒢) ∧ ∀ V ∈ 𝒢, z ∉ closure V) :
    Specs.L_0031.stmt := by
  refine ⟨Y, inferInstance,
    isStratifiable_of_clopen_g_function Y g hg_clopen hg_dec hg_inter hg_sep,
    y₀, ⟨fun n => g n y₀, fun n => hg_clopen n y₀, hg_inter y₀⟩,
    not_hasCPOuterBase_of_escape Y y₀ hesc⟩

/-- Theorem 4 (End-to-end refutation of `Tinf` from the `L_0031` criteria):
Composing `L0031_of_clopen_g_function_and_escape` with the verified reductions
`Proofs.R_0010`, `Proofs.L_0032`, `Proofs.R_0009`, `Proofs.L_0029`, `Proofs.L_0004`
directly yields `¬ MSpace.Goals.Tinf_M3_imp_M1`. -/
theorem not_Tinf_of_clopen_g_function_and_escape
    (Y : Type) [TopologicalSpace Y]
    (g : ℕ → Y → Set Y)
    (hg_clopen : ∀ n x, IsOpen (g n x) ∧ IsClosed (g n x) ∧ x ∈ g n x)
    (hg_dec : ∀ n x, g (n + 1) x ⊆ g n x)
    (hg_inter : ∀ x, (⋂ n, g n x) = {x})
    (hg_sep : ∀ H : Set Y, IsClosed H → ∀ x ∉ H,
      ∃ n, ∃ O : Set Y, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ H, Disjoint O (g n y))
    (y₀ : Y)
    (hesc : ∀ 𝓥 : Set (Set Y),
      (∀ V ∈ 𝓥, IsOpen V ∧ y₀ ∈ V) →
      (∀ U : Set Y, IsOpen U → y₀ ∈ U → ∃ V ∈ 𝓥, V ⊆ U) →
      ∃ 𝒢 ⊆ 𝓥, ∃ z : Y, z ∈ closure (⋃₀ 𝒢) ∧ ∀ V ∈ 𝒢, z ∉ closure V) :
    ¬ MSpace.Goals.Tinf_M3_imp_M1 := by
  have h31 : Specs.L_0031.stmt :=
    L0031_of_clopen_g_function_and_escape Y g hg_clopen hg_dec hg_inter hg_sep y₀ hesc
  have h30 : Specs.L_0030.stmt := Proofs.R_0010.main h31 Proofs.L_0032.main
  exact Proofs.R_0009.main Proofs.L_0029.main h30 Proofs.L_0004.main

end Research.ChenWangL0031
