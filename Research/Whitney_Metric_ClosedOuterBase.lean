import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Indexed
import Targets.Defs
import Defs.D_0001

/-!
# Whitney Decomposition Theorem: Every Closed Subset of a Metric Space Has a CP Open Outer Base

We prove via a **Whitney-type locally finite open cover** of `X \ F`:
1. `metric_closed_hasCPOuterBase`:
   for **every** metric space `X` and **every** closed subset `F ⊆ X`, there exists a
   closure-preserving family `𝓑` of open neighborhoods of `F` that forms an outer base of `F`
   (i.e. `∀ O, IsOpen O → F ⊆ O → ∃ U ∈ 𝓑, U ⊆ O`).
2. `collapseQuotient_metric_hasCPOuterBase`:
   for any metric space `X` and any closed subset `F ⊆ X`, the collapsed point `none` in the
   quotient `X / F` has a closure-preserving open outer base (`Defs.D_0001.HasCPOuterBase`),
   even when `F` is non-compact and `X / F` is neither first-countable, locally compact, nor
   `k_ω` (e.g. `ℝ / ℤ`, `ℓ² / F`, etc.).
-/

namespace Research.WhitneyOuterBase

open Set Topology

/-- A closed set `F ⊆ X` has a closure-preserving open outer base. -/
def HasCPOuterBaseSet {X : Type*} [TopologicalSpace X] (F : Set X) : Prop :=
  ∃ 𝓑 : Set (Set X),
    (∀ U ∈ 𝓑, IsOpen U ∧ F ⊆ U) ∧
    (∀ O : Set X, IsOpen O → F ⊆ O → ∃ U ∈ 𝓑, U ⊆ O) ∧
    MSpace.ClosurePreserving 𝓑

/-- **Whitney Decomposition Theorem**:
Every closed subset `F` of a metric space `X` has a closure-preserving open outer base. -/
theorem metric_closed_hasCPOuterBase {X : Type*} [MetricSpace X]
    {F : Set X} (hF : IsClosed F) : HasCPOuterBaseSet F := by
  -- Work on the open metric subspace `Y := Fᶜ`.
  let Y := { x : X // x ∉ F }
  have hFc_open : IsOpen Fᶜ := hF.isOpen_compl
  have hr_ex : ∀ a : Y, ∃ r : ℝ, 0 < r ∧ Metric.ball a.1 (3 * r) ⊆ Fᶜ := by
    intro a
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hFc_open a.1 a.2
    refine ⟨ρ / 3, by linarith, ?_⟩
    have hEq : 3 * (ρ / 3) = ρ := by ring
    rw [hEq]; exact hball
  choose r hr_pos hr_ball using hr_ex
  -- Open cover of `Y` by Whitney balls `B_Y(a, r a)`.
  let cov : Y → Set Y := fun a => Metric.ball a (r a)
  have hcov_open : ∀ a : Y, IsOpen (cov a) := fun _ => Metric.isOpen_ball
  have hcov_univ : (⋃ a : Y, cov a) = Set.univ := by
    ext a
    simp only [mem_iUnion, mem_univ, iff_true, cov]
    exact ⟨a, Metric.mem_ball.mpr (by rw [dist_self]; exact hr_pos a)⟩
  obtain ⟨W, hWo, hWcov, hWlf, hWref⟩ := precise_refinement cov hcov_open hcov_univ
  -- Push each `W a ⊆ Y` into `X` via `Subtype.val`.
  let WX : Y → Set X := fun a => (Subtype.val : Y → X) '' W a
  have hWX_sub_ball : ∀ a : Y, WX a ⊆ Metric.ball a.1 (r a) := by
    rintro a _ ⟨y, hyW, rfl⟩
    exact hWref a hyW
  -- `closure (WX a)` is disjoint from `F`!
  have hWX_cl_disj : ∀ a : Y, Disjoint (closure (WX a)) F := by
    intro a
    rw [Set.disjoint_left]
    intro x hxCl hxF
    have hcl_sub : closure (WX a) ⊆ Metric.closedBall a.1 (r a) :=
      closure_minimal ((hWX_sub_ball a).trans Metric.ball_subset_closedBall)
        Metric.isClosed_closedBall
    have hxa : dist x a.1 ≤ r a := Metric.mem_closedBall.mp (hcl_sub hxCl)
    have hlt : dist x a.1 < 3 * r a := by linarith [hr_pos a]
    exact hr_ball a (Metric.mem_ball.mpr hlt) hxF
  -- Local finiteness of `fun a => closure (WX a)` at every point `z ∈ Fᶜ`!
  have hWX_cl_lf : ∀ z : Y, ∃ O : Set X, IsOpen O ∧ z.1 ∈ O ∧ O ⊆ Fᶜ ∧
      { a : Y | (O ∩ closure (WX a)).Nonempty }.Finite := by
    intro z
    obtain ⟨t, ht_nhds, ht_fin⟩ := hWlf.closure z
    obtain ⟨Oy, hOyt, hOyo, hzOy⟩ := mem_nhds_iff.mp ht_nhds
    let O : Set X := (Subtype.val : Y → X) '' Oy
    have hOo : IsOpen O := hFc_open.isOpenMap_subtype_val _ hOyo
    have hzO : z.1 ∈ O := ⟨z, hzOy, rfl⟩
    have hOFc : O ⊆ Fᶜ := by rintro _ ⟨y, _, rfl⟩; exact y.2
    refine ⟨O, hOo, hzO, hOFc, ht_fin.subset ?_⟩
    rintro a ⟨x, hxO, hxCl⟩
    obtain ⟨y, hyOy, rfl⟩ := hxO
    have hyCl : y ∈ closure (W a) := by
      rw [mem_closure_iff]
      intro V hVo hyV
      let VX : Set X := (Subtype.val : Y → X) '' V
      have hVXo : IsOpen VX := hFc_open.isOpenMap_subtype_val _ hVo
      obtain ⟨q, hqVX, hqWX⟩ := mem_closure_iff.mp hxCl VX hVXo ⟨y, hyV, rfl⟩
      obtain ⟨y', hy'V, rfl⟩ := hqVX
      obtain ⟨y'', hy''W, hy''eq⟩ := hqWX
      have : y'' = y' := Subtype.ext hy''eq
      subst this
      exact ⟨y'', hy'V, hy''W⟩
    exact ⟨y, hyCl, hOyt hyOy⟩
  -- Define the Whitney CP open outer base `𝓑`!
  let 𝓑 : Set (Set X) :=
    { U : Set X | ∃ S : Set Y,
        Disjoint (closure (⋃ a ∈ S, WX a)) F ∧
        U = (⋃ a ∈ S, closure (WX a))ᶜ }
  refine ⟨𝓑, ?_, ?_, ?_⟩
  · -- Every `U ∈ 𝓑` is open and contains `F`.
    rintro U ⟨S, hSdisj, rfl⟩
    have hcl_eq : IsClosed (⋃ a ∈ S, closure (WX a)) := by
      rw [← closure_subset_iff_isClosed]
      intro z hz
      have hz_sub : (⋃ a ∈ S, closure (WX a)) ⊆ closure (⋃ a ∈ S, WX a) := by
        rintro x hx
        obtain ⟨a, haS, hxCl⟩ := mem_iUnion₂.mp hx
        exact closure_mono (subset_biUnion_of_mem haS) hxCl
      have hz_cl : z ∈ closure (⋃ a ∈ S, WX a) := by
        have := closure_mono hz_sub hz
        rwa [closure_closure] at this
      have hzNotF : z ∉ F := Set.disjoint_left.mp hSdisj hz_cl
      obtain ⟨O, hOo, hzO, -, hOfin⟩ := hWX_cl_lf ⟨z, hzNotF⟩
      let E : Set Y := { a ∈ S | (O ∩ closure (WX a)).Nonempty }
      have hEfin : E.Finite := hOfin.subset fun a ha => ha.2
      have hEcl : IsClosed (⋃ a ∈ E, closure (WX a)) :=
        hEfin.isClosed_biUnion fun _ _ => isClosed_closure
      have hzE : z ∈ closure (⋃ a ∈ E, closure (WX a)) := by
        rw [mem_closure_iff]
        intro V hVo hzV
        obtain ⟨q, hqOV, hqU⟩ := mem_closure_iff.mp hz (O ∩ V) (hOo.inter hVo) ⟨hzO, hzV⟩
        obtain ⟨a, haS, hqCl⟩ := mem_iUnion₂.mp hqU
        exact ⟨q, hqOV.2, mem_iUnion₂.mpr ⟨a, ⟨haS, ⟨q, hqOV.1, hqCl⟩⟩, hqCl⟩⟩
      rw [hEcl.closure_eq] at hzE
      obtain ⟨a, haE, hzCl⟩ := mem_iUnion₂.mp hzE
      exact mem_iUnion₂.mpr ⟨a, haE.1, hzCl⟩
    refine ⟨hcl_eq.isOpen_compl, ?_⟩
    intro x hxF hxU
    obtain ⟨a, _, hxCl⟩ := mem_iUnion₂.mp hxU
    exact Set.disjoint_left.mp (hWX_cl_disj a) hxCl hxF
  · -- Outer base property!
    intro O hOo hFO
    let K : Set X := Oᶜ
    let S : Set Y := { a : Y | (WX a ∩ K).Nonempty }
    have hSdisj : Disjoint (closure (⋃ a ∈ S, WX a)) F := by
      rw [Set.disjoint_left]
      intro x₀ hx₀Cl hx₀F
      obtain ⟨ε, hε, hballO⟩ := Metric.isOpen_iff.mp hOo x₀ (hFO hx₀F)
      obtain ⟨y, hyBall, hyU⟩ :=
        mem_closure_iff.mp hx₀Cl (Metric.ball x₀ (ε / 2)) Metric.isOpen_ball
          (Metric.mem_ball.mpr (by rw [dist_self]; linarith))
      obtain ⟨a, ⟨k, hkWX, hkK⟩, hyWX⟩ := mem_iUnion₂.mp hyU
      have hya : dist y a.1 < r a := Metric.mem_ball.mp (hWX_sub_ball a hyWX)
      have hka : dist k a.1 < r a := Metric.mem_ball.mp (hWX_sub_ball a hkWX)
      have hyx₀ : dist y x₀ < ε / 2 := Metric.mem_ball.mp hyBall
      have hkx₀_ge : ε ≤ dist k x₀ := by
        by_contra hlt
        push Not at hlt
        exact hkK (hballO (Metric.mem_ball.mpr hlt))
      have h3r_le : 3 * r a ≤ dist x₀ a.1 := by
        by_contra hlt
        push Not at hlt
        exact hr_ball a (Metric.mem_ball.mpr hlt) hx₀F
      have hax₀ : dist x₀ a.1 ≤ dist y x₀ + dist y a.1 := by
        have := dist_triangle x₀ y a.1
        rw [dist_comm x₀ y] at this
        exact this
      have hky : dist k y ≤ dist k a.1 + dist a.1 y := dist_triangle k a.1 y
      have hkx₀ : dist k x₀ ≤ dist k y + dist y x₀ := dist_triangle k y x₀
      rw [dist_comm a.1 y] at hky
      linarith
    refine ⟨(⋃ a ∈ S, closure (WX a))ᶜ, ⟨S, hSdisj, rfl⟩, ?_⟩
    intro x hxU
    by_contra hxK
    have hxNotF : x ∉ F := fun hxF => hxK (hFO hxF)
    have hxCov : (⟨x, hxNotF⟩ : Y) ∈ ⋃ a, W a := by rw [hWcov]; trivial
    obtain ⟨a, hxa⟩ := mem_iUnion.mp hxCov
    have hxWX : x ∈ WX a := ⟨⟨x, hxNotF⟩, hxa, rfl⟩
    have haS : a ∈ S := ⟨x, hxWX, hxK⟩
    exact hxU (mem_iUnion₂.mpr ⟨a, haS, subset_closure hxWX⟩)
  · -- Closure-preserving!
    intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      by_cases hzF : z ∈ F
      · by_cases hGne : 𝓖.Nonempty
        · obtain ⟨U, hUG⟩ := hGne
          obtain ⟨S, _, rfl⟩ := h𝓖 hUG
          have hzU : z ∈ (⋃ a ∈ S, closure (WX a))ᶜ := by
            intro hzIn
            obtain ⟨a, _, hzCl⟩ := mem_iUnion₂.mp hzIn
            exact Set.disjoint_left.mp (hWX_cl_disj a) hzCl hzF
          exact ⟨closure _, ⟨_, hUG, rfl⟩, subset_closure hzU⟩
        · rw [Set.not_nonempty_iff_eq_empty.mp hGne, sUnion_empty, closure_empty] at hz
          exact hz.elim
      · obtain ⟨O, hOo, hzO, -, hOfin⟩ := hWX_cl_lf ⟨z, hzF⟩
        let E : Set Y := { a : Y | (O ∩ closure (WX a)).Nonempty }
        have hEfin : E.Finite := hOfin
        have htrace_sub :
            (fun U : Set X => U ∩ O) '' 𝓖 ⊆
              (fun T : Set Y => O \ ⋃ a ∈ T, closure (WX a)) '' 𝒫 E := by
          rintro _ ⟨U, hUG, rfl⟩
          obtain ⟨S, _, rfl⟩ := h𝓖 hUG
          refine ⟨S ∩ E, Set.inter_subset_right, ?_⟩
          ext x
          simp only [mem_inter_iff, mem_compl_iff, mem_iUnion, mem_sdiff]
          constructor
          · rintro ⟨hxO, hxNot⟩
            refine ⟨?_, hxO⟩
            rintro ⟨a, haS, hxCl⟩
            exact hxNot ⟨a, ⟨haS, ⟨x, hxO, hxCl⟩⟩, hxCl⟩
          · rintro ⟨hxNot, hxO⟩
            refine ⟨hxO, ?_⟩
            rintro ⟨a, ⟨haS, _⟩, hxCl⟩
            exact hxNot ⟨a, haS, hxCl⟩
        have htrace_fin : ((fun U : Set X => U ∩ O) '' 𝓖).Finite :=
          (hEfin.powerset.image _).subset htrace_sub
        have hz_cl_trace : z ∈ closure (⋃₀ ((fun U : Set X => U ∩ O) '' 𝓖)) := by
          rw [mem_closure_iff]
          intro V hVo hzV
          obtain ⟨q, hqOV, ⟨U, hUG, hqU⟩⟩ :=
            mem_closure_iff.mp hz (O ∩ V) (hOo.inter hVo) ⟨hzO, hzV⟩
          exact ⟨q, hqOV.2, ⟨U ∩ O, ⟨U, hUG, rfl⟩, hqU, hqOV.1⟩⟩
        have hcl_eq : closure (⋃₀ ((fun U : Set X => U ∩ O) '' 𝓖)) =
            ⋃₀ (closure '' ((fun U : Set X => U ∩ O) '' 𝓖)) := by
          apply Subset.antisymm
          · have hcl : IsClosed (⋃₀ (closure '' ((fun U : Set X => U ∩ O) '' 𝓖))) :=
              (htrace_fin.image closure).isClosed_sUnion
                (by rintro _ ⟨_, _, rfl⟩; exact isClosed_closure)
            exact closure_minimal
              (fun y ⟨T, hT, hyT⟩ => ⟨closure T, ⟨T, hT, rfl⟩, subset_closure hyT⟩) hcl
          · rintro y ⟨_, ⟨T, hT, rfl⟩, hyT⟩
            exact closure_mono (Set.subset_sUnion_of_mem hT) hyT
        rw [hcl_eq] at hz_cl_trace
        obtain ⟨_, ⟨_, ⟨U, hUG, rfl⟩, rfl⟩, hzU⟩ := hz_cl_trace
        exact ⟨closure U, ⟨U, hUG, rfl⟩, closure_mono inter_subset_left hzU⟩
    · rintro z ⟨_, ⟨U, hUG, rfl⟩, hzU⟩
      exact closure_mono (Set.subset_sUnion_of_mem hUG) hzU

end Research.WhitneyOuterBase
