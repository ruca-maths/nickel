import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Indexed
import Targets.Defs
import Defs.D_0001

/-!
# Collapse Quotients `X / F` of Metric Spaces are `M₁`

For **any** metric space `X` and **any** closed subset `F ⊆ X`, we define the collapse quotient
`CollapseQuot X F := Option { x : X // x ∉ F }` (identifying `F` to the single point `none`)
with its canonical quotient topology, and prove:
1. `collapseProj_continuous`, `collapseProj_surjective`, `collapseProj_isClosedMap`.
2. `collapseQuot_t3Space`: `X / F` is `T₃`.
3. `collapseQuot_hasCPOuterBase_none`: the collapsed point `none` has a closure-preserving open
   outer base (`Defs.D_0001.HasCPOuterBase`), constructed via a Whitney decomposition of `X \ F`.
4. `collapseQuot_isM1`: **`X / F` is an `M₁`-space** (even when `F` is non-compact and `X / F`
   is neither first-countable, locally compact, nor `k_ω`, such as `ℝ / ℤ`, `ℝ^d / ℤ^d`, or
   infinite-dimensional Banach quotients `ℓ² / F`).
-/

namespace Research.CollapseQuotMetricM1

open Set Topology

/-- Underlying type of the collapse quotient `X / F`: `none` represents `F`, and `some ⟨x, hx⟩`
represents `x ∈ X \ F`. -/
abbrev CollapseQuot (X : Type*) (F : Set X) := Option { x : X // x ∉ F }

/-- Canonical projection `π : X → X / F`. -/
noncomputable def collapseProj {X : Type*} (F : Set X) (x : X) : CollapseQuot X F := by
  classical
  exact if h : x ∈ F then none else some ⟨x, h⟩

/-- Quotient topology on `X / F` coinduced by `collapseProj F`. -/
noncomputable instance instTopologicalSpaceCollapseQuot {X : Type*} [TopologicalSpace X]
    (F : Set X) : TopologicalSpace (CollapseQuot X F) :=
  TopologicalSpace.coinduced (collapseProj F) inferInstance

theorem collapseProj_continuous {X : Type*} [TopologicalSpace X] (F : Set X) :
    Continuous (collapseProj F) :=
  continuous_coinduced_rng

theorem collapseProj_eq_none_iff {X : Type*} (F : Set X) (x : X) :
    collapseProj F x = none ↔ x ∈ F := by
  classical
  unfold collapseProj
  by_cases h : x ∈ F
  · simp [h]
  · simp [h]

theorem collapseProj_eq_some_iff {X : Type*} (F : Set X) (x : X) (y : { x : X // x ∉ F }) :
    collapseProj F x = some y ↔ x = y.1 := by
  classical
  unfold collapseProj
  by_cases h : x ∈ F
  · simp only [dite_eq_left h, reduceCtorEq, false_iff]
    intro heq; exact y.2 (heq ▸ h)
  · simp only [dite_eq_right h, Option.some.injEq, Subtype.ext_iff]

theorem collapseProj_surjective {X : Type*} {F : Set X} (hFne : F.Nonempty) :
    Function.Surjective (collapseProj F) := by
  rintro (_ | ⟨x, hx⟩)
  · obtain ⟨x₀, hx₀⟩ := hFne
    exact ⟨x₀, (collapseProj_eq_none_iff F x₀).mpr hx₀⟩
  · exact ⟨x, (collapseProj_eq_some_iff F x ⟨x, hx⟩).mpr rfl⟩

theorem isOpen_collapseQuot_iff {X : Type*} [TopologicalSpace X] (F : Set X)
    (U : Set (CollapseQuot X F)) :
    IsOpen U ↔ IsOpen (collapseProj F ⁻¹' U) :=
  isOpen_coinduced

theorem isClosed_collapseQuot_iff {X : Type*} [TopologicalSpace X] (F : Set X)
    (C : Set (CollapseQuot X F)) :
    IsClosed C ↔ IsClosed (collapseProj F ⁻¹' C) := by
  rw [← isOpen_compl_iff, ← isOpen_compl_iff, isOpen_collapseQuot_iff]
  rfl

theorem collapseProj_isClosedMap {X : Type*} [TopologicalSpace X] {F : Set X} (hF : IsClosed F) :
    IsClosedMap (collapseProj F) := by
  intro C hC
  rw [isClosed_collapseQuot_iff]
  by_cases hCF : (C ∩ F).Nonempty
  · have hEq : collapseProj F ⁻¹' (collapseProj F '' C) = C ∪ F := by
      ext x
      constructor
      · rintro ⟨x', hx'C, hfx⟩
        by_cases hxF : x ∈ F
        · exact Or.inr hxF
        · have hx'NotF : x' ∉ F := by
            intro hx'F
            rw [(collapseProj_eq_none_iff F x').mpr hx'F] at hfx
            exact hxF ((collapseProj_eq_none_iff F x).mp hfx.symm)
          have h1 : collapseProj F x' = some ⟨x', hx'NotF⟩ :=
            (collapseProj_eq_some_iff F x' ⟨x', hx'NotF⟩).mpr rfl
          rw [h1] at hfx
          have heq : x = x' := (collapseProj_eq_some_iff F x ⟨x', hx'NotF⟩).mp hfx.symm
          exact Or.inl (heq ▸ hx'C)
      · rintro (hxC | hxF)
        · exact ⟨x, hxC, rfl⟩
        · obtain ⟨x', hx'C, hx'F⟩ := hCF
          refine ⟨x', hx'C, ?_⟩
          rw [(collapseProj_eq_none_iff F x').mpr hx'F, (collapseProj_eq_none_iff F x).mpr hxF]
    rw [hEq]
    exact hC.union hF
  · have hEq : collapseProj F ⁻¹' (collapseProj F '' C) = C := by
      ext x
      constructor
      · rintro ⟨x', hx'C, hfx⟩
        have hx'NotF : x' ∉ F := fun hx'F => hCF ⟨x', hx'C, hx'F⟩
        have h1 : collapseProj F x' = some ⟨x', hx'NotF⟩ :=
          (collapseProj_eq_some_iff F x' ⟨x', hx'NotF⟩).mpr rfl
        rw [h1] at hfx
        have heq : x = x' := (collapseProj_eq_some_iff F x ⟨x', hx'NotF⟩).mp hfx.symm
        exact heq ▸ hx'C
      · intro hxC
        exact ⟨x, hxC, rfl⟩
    rw [hEq]
    exact hC

/-- `CollapseQuot X F` is `T₃` whenever `X` is normal `T₁` and `F` is closed nonempty. -/
theorem collapseQuot_t3Space {X : Type*} [TopologicalSpace X] [T1Space X] [NormalSpace X]
    {F : Set X} (hF : IsClosed F) (hFne : F.Nonempty) :
    T3Space (CollapseQuot X F) := by
  have hf_cont := collapseProj_continuous F
  have hf_surj := collapseProj_surjective hFne
  have hf_closed := collapseProj_isClosedMap hF
  have hT1 : T1Space (CollapseQuot X F) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := hf_surj y
    have hEq : ({collapseProj F x} : Set (CollapseQuot X F)) = collapseProj F '' {x} := by simp
    rw [hEq]; exact hf_closed {x} isClosed_singleton⟩
  have hNorm : NormalSpace (CollapseQuot X F) := ⟨fun A B hA hB hdisj => by
    obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ :=
      normal_separation (hA.preimage hf_cont) (hB.preimage hf_cont) (hdisj.preimage (collapseProj F))
    refine ⟨(collapseProj F '' Uᶜ)ᶜ, (collapseProj F '' Vᶜ)ᶜ,
      (hf_closed _ hUo.isClosed_compl).isOpen_compl,
      (hf_closed _ hVo.isClosed_compl).isOpen_compl,
      ?_, ?_, ?_⟩
    · intro y hyA; rintro ⟨x, hxUc, rfl⟩; exact hxUc (hAU hyA)
    · intro y hyB; rintro ⟨x, hxVc, rfl⟩; exact hxVc (hBV hyB)
    · rw [Set.disjoint_left]
      intro y hy1 hy2
      obtain ⟨x, rfl⟩ := hf_surj y
      have hxU : x ∈ U := by by_contra h; exact hy1 ⟨x, h, rfl⟩
      have hxV : x ∈ V := by by_contra h; exact hy2 ⟨x, h, rfl⟩
      exact Set.disjoint_left.mp hUV hxU hxV⟩
  exact inferInstance

/-- Pushing a closure-preserving open outer base of `F` in `X` forward to `none` in `X / F`. -/
private theorem hasCPOuterBase_none_of_set_outerBase {X : Type*} [TopologicalSpace X]
    {F : Set X} (hF : IsClosed F) (hFne : F.Nonempty)
    {𝓑 : Set (Set X)}
    (hB_open : ∀ U ∈ 𝓑, IsOpen U ∧ F ⊆ U)
    (hB_base : ∀ O : Set X, IsOpen O → F ⊆ O → ∃ U ∈ 𝓑, U ⊆ O)
    (hB_cp : MSpace.ClosurePreserving 𝓑) :
    Defs.D_0001.HasCPOuterBase (none : CollapseQuot X F) := by
  let π := collapseProj F
  have hπ_cont : Continuous π := collapseProj_continuous F
  have hπ_surj : Function.Surjective π := collapseProj_surjective hFne
  have hπ_cl : IsClosedMap π := collapseProj_isClosedMap hF
  -- For any `U ⊇ F`, `π ⁻¹' (π '' U) = U`.
  have hpre_im : ∀ U : Set X, F ⊆ U → π ⁻¹' (π '' U) = U := by
    intro U hFU
    ext x
    constructor
    · rintro ⟨x', hx'U, hfx⟩
      by_cases hxF : x ∈ F
      · exact hFU hxF
      · have hx'NotF : x' ∉ F := by
          intro hx'F
          have h1 : π x' = none := (collapseProj_eq_none_iff F x').mpr hx'F
          rw [h1] at hfx
          exact hxF ((collapseProj_eq_none_iff F x).mp hfx.symm)
        have h1 : π x' = some ⟨x', hx'NotF⟩ :=
          (collapseProj_eq_some_iff F x' ⟨x', hx'NotF⟩).mpr rfl
        rw [h1] at hfx
        have heq : x = x' := (collapseProj_eq_some_iff F x ⟨x', hx'NotF⟩).mp hfx.symm
        exact heq ▸ hx'U
    · intro hxU; exact ⟨x, hxU, rfl⟩
  let 𝓥 : Set (Set (CollapseQuot X F)) := (fun U => π '' U) '' 𝓑
  refine ⟨𝓥, ?_, ?_, ?_⟩
  · rintro _ ⟨U, hUB, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [isOpen_collapseQuot_iff, hpre_im U (hB_open U hUB).2]
      exact (hB_open U hUB).1
    · obtain ⟨x₀, hx₀⟩ := hFne
      exact ⟨x₀, (hB_open U hUB).2 hx₀, (collapseProj_eq_none_iff F x₀).mpr hx₀⟩
  · intro W hWo hnoneW
    have hpre_o : IsOpen (π ⁻¹' W) := hWo.preimage hπ_cont
    have hF_sub : F ⊆ π ⁻¹' W := fun x hxF => by
      change collapseProj F x ∈ W; rw [(collapseProj_eq_none_iff F x).mpr hxF]; exact hnoneW
    obtain ⟨U, hUB, hUW⟩ := hB_base (π ⁻¹' W) hpre_o hF_sub
    refine ⟨π '' U, ⟨U, hUB, rfl⟩, ?_⟩
    rintro _ ⟨x, hxU, rfl⟩; exact hUW hxU
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · let 𝓑' : Set (Set X) := { U ∈ 𝓑 | π '' U ∈ 𝓖 }
      have hG_eq : ⋃₀ 𝓖 = π '' (⋃₀ 𝓑') := by
        ext y
        constructor
        · rintro ⟨V, hVG, hyV⟩
          obtain ⟨U, hUB, rfl⟩ := h𝓖 hVG
          obtain ⟨x, hxU, rfl⟩ := hyV
          exact ⟨x, ⟨U, ⟨hUB, hVG⟩, hxU⟩, rfl⟩
        · rintro ⟨x, ⟨U, ⟨_, hUG⟩, hxU⟩, rfl⟩
          exact ⟨π '' U, hUG, ⟨x, hxU, rfl⟩⟩
      intro y hy
      rw [hG_eq] at hy
      -- `π '' closure (⋃₀ 𝓑')` is closed and contains `π '' (⋃₀ 𝓑')`.
      have hcl_im : IsClosed (π '' closure (⋃₀ 𝓑')) := hπ_cl _ isClosed_closure
      have hy_im : y ∈ π '' closure (⋃₀ 𝓑') :=
        closure_minimal (image_mono subset_closure) hcl_im hy
      obtain ⟨x, hxCl, rfl⟩ := hy_im
      rw [hB_cp 𝓑' (fun _ h => h.1)] at hxCl
      obtain ⟨_, ⟨U, hUB', rfl⟩, hxClU⟩ := hxCl
      exact ⟨closure (π '' U), ⟨π '' U, hUB'.2, rfl⟩,
        image_closure_subset_closure_image hπ_cont ⟨x, hxClU, rfl⟩⟩
    · rintro y ⟨_, ⟨V, hVG, rfl⟩, hyV⟩
      exact closure_mono (Set.subset_sUnion_of_mem hVG) hyV

/-- **Whitney CP Open Outer Base + `M₁` Theorem for Metric Collapse Quotients `X / F`**:
For **every** metric space `X` and **every** nonempty closed subset `F ⊆ X`, the collapse
quotient `X / F` has a closure-preserving open outer base at the collapsed point `none`
and is an **`M₁`-space**. -/
theorem collapseQuot_metric_isM1 {X : Type*} [MetricSpace X]
    {F : Set X} (hF : IsClosed F) (hFne : F.Nonempty) :
    Defs.D_0001.HasCPOuterBase (none : CollapseQuot X F) ∧ MSpace.IsM1 (CollapseQuot X F) := by
  have hT3 : T3Space (CollapseQuot X F) := collapseQuot_t3Space hF hFne
  let π := collapseProj F
  have hπ_cont : Continuous π := collapseProj_continuous F
  have hπ_cl : IsClosedMap π := collapseProj_isClosedMap hF
  -- Step 1: Whitney CP open outer base of `F` in `X`.
  let Y := { x : X // x ∉ F }
  have hFc_open : IsOpen Fᶜ := hF.isOpen_compl
  have hr_ex : ∀ a : Y, ∃ r : ℝ, 0 < r ∧ Metric.ball a.1 (3 * r) ⊆ Fᶜ := by
    intro a
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hFc_open a.1 a.2
    refine ⟨ρ / 3, by linarith, ?_⟩
    have hEq : 3 * (ρ / 3) = ρ := by ring
    rw [hEq]; exact hball
  choose r hr_pos hr_ball using hr_ex
  let cov : Y → Set Y := fun a => Metric.ball a (r a)
  have hcov_univ : (⋃ a : Y, cov a) = Set.univ := by
    ext a; simp only [mem_iUnion, mem_univ, iff_true, cov]
    exact ⟨a, Metric.mem_ball.mpr (by rw [dist_self]; exact hr_pos a)⟩
  obtain ⟨W, hWo, hWcov, hWlf, hWref⟩ := precise_refinement cov (fun _ => Metric.isOpen_ball) hcov_univ
  let WX : Y → Set X := fun a => (Subtype.val : Y → X) '' W a
  have hWX_sub_ball : ∀ a : Y, WX a ⊆ Metric.ball a.1 (r a) := by
    rintro a _ ⟨y, hyW, rfl⟩; exact hWref a hyW
  have hWX_cl_disj : ∀ a : Y, Disjoint (closure (WX a)) F := by
    intro a; rw [Set.disjoint_left]; intro x hxCl hxF
    have hcl_sub : closure (WX a) ⊆ Metric.closedBall a.1 (r a) :=
      closure_minimal ((hWX_sub_ball a).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
    have hxa : dist x a.1 ≤ r a := Metric.mem_closedBall.mp (hcl_sub hxCl)
    exact hr_ball a (Metric.mem_ball.mpr (by linarith [hr_pos a])) hxF
  have hWX_cl_lf : ∀ z : Y, ∃ O : Set X, IsOpen O ∧ z.1 ∈ O ∧ O ⊆ Fᶜ ∧
      { a : Y | (O ∩ closure (WX a)).Nonempty }.Finite := by
    intro z
    obtain ⟨t, ht_nhds, ht_fin⟩ := hWlf.closure z
    obtain ⟨Oy, hOyt, hOyo, hzOy⟩ := mem_nhds_iff.mp ht_nhds
    let O : Set X := (Subtype.val : Y → X) '' Oy
    refine ⟨O, hFc_open.isOpenMap_subtype_val _ hOyo, ⟨z, hzOy, rfl⟩,
      by rintro _ ⟨y, _, rfl⟩; exact y.2, ht_fin.subset ?_⟩
    rintro a ⟨x, hxO, hxCl⟩
    obtain ⟨y, hyOy, rfl⟩ := hxO
    have hyCl : y ∈ closure (W a) := by
      rw [mem_closure_iff]; intro V hVo hyV
      let VX : Set X := (Subtype.val : Y → X) '' V
      obtain ⟨q, hqVX, hqWX⟩ := mem_closure_iff.mp hxCl VX (hFc_open.isOpenMap_subtype_val _ hVo) ⟨y, hyV, rfl⟩
      obtain ⟨y', hy'V, rfl⟩ := hqVX
      obtain ⟨y'', hy''W, hy''eq⟩ := hqWX
      have : y'' = y' := Subtype.ext hy''eq
      subst this; exact ⟨y'', hy'V, hy''W⟩
    exact ⟨y, hyCl, hOyt hyOy⟩
  let 𝓑F : Set (Set X) :=
    { U : Set X | ∃ S : Set Y, Disjoint (closure (⋃ a ∈ S, WX a)) F ∧
        U = (⋃ a ∈ S, closure (WX a))ᶜ }
  have hBF_open : ∀ U ∈ 𝓑F, IsOpen U ∧ F ⊆ U := by
    rintro U ⟨S, hSdisj, rfl⟩
    have hcl_eq : IsClosed (⋃ a ∈ S, closure (WX a)) := by
      rw [← closure_subset_iff_isClosed]; intro z hz
      have hz_sub : (⋃ a ∈ S, closure (WX a)) ⊆ closure (⋃ a ∈ S, WX a) := by
        rintro x hx; obtain ⟨a, haS, hxCl⟩ := mem_iUnion₂.mp hx
        exact closure_mono (subset_biUnion_of_mem haS) hxCl
      have hz_cl : z ∈ closure (⋃ a ∈ S, WX a) := by
        have := closure_mono hz_sub hz; rwa [closure_closure] at this
      have hzNotF : z ∉ F := Set.disjoint_left.mp hSdisj hz_cl
      obtain ⟨O, hOo, hzO, -, hOfin⟩ := hWX_cl_lf ⟨z, hzNotF⟩
      let E : Set Y := { a ∈ S | (O ∩ closure (WX a)).Nonempty }
      have hEcl : IsClosed (⋃ a ∈ E, closure (WX a)) :=
        (hOfin.subset (fun a (ha : a ∈ E) => ha.2)).isClosed_biUnion fun _ _ => isClosed_closure
      have hzE : z ∈ closure (⋃ a ∈ E, closure (WX a)) := by
        rw [mem_closure_iff]; intro V hVo hzV
        obtain ⟨q, hqOV, hqU⟩ := mem_closure_iff.mp hz (O ∩ V) (hOo.inter hVo) ⟨hzO, hzV⟩
        obtain ⟨a, haS, hqCl⟩ := mem_iUnion₂.mp hqU
        exact ⟨q, hqOV.2, mem_iUnion₂.mpr ⟨a, ⟨haS, ⟨q, hqOV.1, hqCl⟩⟩, hqCl⟩⟩
      rw [hEcl.closure_eq] at hzE
      obtain ⟨a, haE, hzCl⟩ := mem_iUnion₂.mp hzE
      exact mem_iUnion₂.mpr ⟨a, haE.1, hzCl⟩
    refine ⟨hcl_eq.isOpen_compl, fun x hxF hxU => ?_⟩
    obtain ⟨a, _, hxCl⟩ := mem_iUnion₂.mp hxU
    exact Set.disjoint_left.mp (hWX_cl_disj a) hxCl hxF
  have hBF_base : ∀ O : Set X, IsOpen O → F ⊆ O → ∃ U ∈ 𝓑F, U ⊆ O := by
    intro O hOo hFO
    let S : Set Y := { a : Y | (WX a ∩ Oᶜ).Nonempty }
    have hSdisj : Disjoint (closure (⋃ a ∈ S, WX a)) F := by
      rw [Set.disjoint_left]; intro x₀ hx₀Cl hx₀F
      obtain ⟨ε, hε, hballO⟩ := Metric.isOpen_iff.mp hOo x₀ (hFO hx₀F)
      obtain ⟨y, hyBall, hyU⟩ :=
        mem_closure_iff.mp hx₀Cl (Metric.ball x₀ (ε / 2)) Metric.isOpen_ball
          (Metric.mem_ball.mpr (by rw [dist_self]; linarith))
      obtain ⟨a, ⟨k, hkWX, hkK⟩, hyWX⟩ := mem_iUnion₂.mp hyU
      have hya : dist y a.1 < r a := Metric.mem_ball.mp (hWX_sub_ball a hyWX)
      have hka : dist k a.1 < r a := Metric.mem_ball.mp (hWX_sub_ball a hkWX)
      have hyx₀ : dist y x₀ < ε / 2 := Metric.mem_ball.mp hyBall
      have hkx₀_ge : ε ≤ dist k x₀ := by
        by_contra hlt; push Not at hlt; exact hkK (hballO (Metric.mem_ball.mpr hlt))
      have h3r_le : 3 * r a ≤ dist x₀ a.1 := by
        by_contra hlt; push Not at hlt; exact hr_ball a (Metric.mem_ball.mpr hlt) hx₀F
      have hax₀ : dist x₀ a.1 ≤ dist y x₀ + dist y a.1 := by
        have := dist_triangle x₀ y a.1; rw [dist_comm x₀ y] at this; exact this
      have hky : dist k y ≤ dist k a.1 + dist a.1 y := dist_triangle k a.1 y
      have hkx₀ : dist k x₀ ≤ dist k y + dist y x₀ := dist_triangle k y x₀
      rw [dist_comm a.1 y] at hky
      linarith
    refine ⟨(⋃ a ∈ S, closure (WX a))ᶜ, ⟨S, hSdisj, rfl⟩, fun x hxU => ?_⟩
    by_contra hxK
    have hxNotF : x ∉ F := fun hxF => hxK (hFO hxF)
    obtain ⟨a, hxa⟩ := mem_iUnion.mp (show (⟨x, hxNotF⟩ : Y) ∈ ⋃ a, W a by rw [hWcov]; trivial)
    exact hxU (mem_iUnion₂.mpr ⟨a, ⟨x, ⟨⟨x, hxNotF⟩, hxa, rfl⟩, hxK⟩, subset_closure ⟨⟨x, hxNotF⟩, hxa, rfl⟩⟩)
  have hBF_cp : MSpace.ClosurePreserving 𝓑F := by
    intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      by_cases hzF : z ∈ F
      · by_cases hGne : 𝓖.Nonempty
        · obtain ⟨U, hUG⟩ := hGne
          exact ⟨closure U, ⟨U, hUG, rfl⟩, subset_closure ((hBF_open U (h𝓖 hUG)).2 hzF)⟩
        · rw [Set.not_nonempty_iff_eq_empty.mp hGne, sUnion_empty, closure_empty] at hz
          exact hz.elim
      · obtain ⟨O, hOo, hzO, -, hOfin⟩ := hWX_cl_lf ⟨z, hzF⟩
        let E : Set Y := { a : Y | (O ∩ closure (WX a)).Nonempty }
        have htrace_sub :
            (fun U : Set X => U ∩ O) '' 𝓖 ⊆
              (fun T : Set Y => O \ ⋃ a ∈ T, closure (WX a)) '' 𝒫 E := by
          rintro _ ⟨U, hUG, rfl⟩
          obtain ⟨S, _, rfl⟩ := h𝓖 hUG
          refine ⟨S ∩ E, Set.inter_subset_right, ?_⟩
          ext x; simp only [mem_inter_iff, mem_compl_iff, mem_iUnion, mem_sdiff]
          constructor
          · rintro ⟨hxO, hxNot⟩; refine ⟨?_, hxO⟩
            rintro ⟨a, haS, hxCl⟩; exact hxNot ⟨a, ⟨haS, ⟨x, hxO, hxCl⟩⟩, hxCl⟩
          · rintro ⟨hxNot, hxO⟩; refine ⟨hxO, ?_⟩
            rintro ⟨a, ⟨haS, _⟩, hxCl⟩; exact hxNot ⟨a, haS, hxCl⟩
        have htrace_fin : ((fun U : Set X => U ∩ O) '' 𝓖).Finite :=
          (hOfin.powerset.image _).subset htrace_sub
        have hz_cl_trace : z ∈ closure (⋃₀ ((fun U : Set X => U ∩ O) '' 𝓖)) := by
          rw [mem_closure_iff]; intro V hVo hzV
          obtain ⟨q, hqOV, ⟨U, hUG, hqU⟩⟩ := mem_closure_iff.mp hz (O ∩ V) (hOo.inter hVo) ⟨hzO, hzV⟩
          exact ⟨q, hqOV.2, ⟨U ∩ O, ⟨U, hUG, rfl⟩, hqU, hqOV.1⟩⟩
        have hcl_eq : closure (⋃₀ ((fun U : Set X => U ∩ O) '' 𝓖)) =
            ⋃₀ (closure '' ((fun U : Set X => U ∩ O) '' 𝓖)) := by
          apply Subset.antisymm
          · have hcl : IsClosed (⋃₀ (closure '' ((fun U : Set X => U ∩ O) '' 𝓖))) :=
              (htrace_fin.image closure).isClosed_sUnion (by rintro _ ⟨_, _, rfl⟩; exact isClosed_closure)
            exact closure_minimal
              (fun y ⟨T, hT, hyT⟩ => ⟨closure T, ⟨T, hT, rfl⟩, subset_closure hyT⟩) hcl
          · rintro y ⟨_, ⟨T, hT, rfl⟩, hyT⟩; exact closure_mono (Set.subset_sUnion_of_mem hT) hyT
        rw [hcl_eq] at hz_cl_trace
        obtain ⟨_, ⟨_, ⟨U, hUG, rfl⟩, rfl⟩, hzU⟩ := hz_cl_trace
        exact ⟨closure U, ⟨U, hUG, rfl⟩, closure_mono inter_subset_left hzU⟩
    · rintro z ⟨_, ⟨U, hUG, rfl⟩, hzU⟩; exact closure_mono (Set.subset_sUnion_of_mem hUG) hzU
  have hCP_none : Defs.D_0001.HasCPOuterBase (none : CollapseQuot X F) :=
    hasCPOuterBase_none_of_set_outerBase hF hFne hBF_open hBF_base hBF_cp
  -- Step 2: Build a σ-CP open base of `X / F` by combining `𝓑_none` with shell-restricted
  -- locally finite refinements on `X \ F`!
  obtain ⟨𝓑₀, hB₀_open, hB₀_base, hB₀_cp⟩ := hCP_none
  -- Closed shells `H k` disjoint from `F` whose interiors cover `Fᶜ`:
  let H : ℕ → Set X := fun k => { x : X | ∀ p ∈ F, 1 / ((k : ℝ) + 1) ≤ dist x p }
  have hH_cl : ∀ k, IsClosed (H k) := fun k => by
    have hEq : H k = ⋂ p ∈ F, { x : X | 1 / ((k : ℝ) + 1) ≤ dist x p } := by
      ext x; simp [H]
    rw [hEq]
    exact isClosed_biInter fun p _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hH_disj : ∀ k, Disjoint (H k) F := by
    intro k; rw [Set.disjoint_left]; intro x hxH hxF
    have hle := hxH x hxF
    rw [dist_self] at hle
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hH_int_cov : ∀ x : X, x ∉ F → ∃ k, x ∈ interior (H k) := by
    intro x hxNotF
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hFc_open x hxNotF
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / ρ)
    refine ⟨k, mem_interior.mpr ⟨Metric.ball x (ρ / 2), ?_, Metric.isOpen_ball,
      Metric.mem_ball.mpr (by rw [dist_self]; linarith)⟩⟩
    intro q hq p hpF
    have hxp : ρ ≤ dist p x := by
      by_contra hlt; push Not at hlt; exact hball (Metric.mem_ball.mpr hlt) hpF
    have hqx : dist q x < ρ / 2 := Metric.mem_ball.mp hq
    have htri : dist p x ≤ dist q x + dist q p := by
      have := dist_triangle p q x
      rw [dist_comm p q] at this
      linarith
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h1 : 1 / ((k : ℝ) + 1) < ρ / 2 := by
      rw [div_lt_iff₀ hpos]
      have h2ρ : 2 < ρ * (k : ℝ) := by
        have := (div_lt_iff₀ hρ).mp hk; linarith
      nlinarith
    linarith
  -- Locally finite open refinements `V m` of `1/(2*(m+1))`-balls on `X`:
  have hrefX : ∀ m : ℕ, ∃ V : X → Set X,
      (∀ a, IsOpen (V a)) ∧ (⋃ a, V a) = Set.univ ∧ LocallyFinite V ∧
      (∀ a, V a ⊆ Metric.ball a (1 / (2 * ((m : ℝ) + 1)))) := by
    intro m
    have hcov : (⋃ a : X, Metric.ball a (1 / (2 * ((m : ℝ) + 1)))) = Set.univ := by
      ext a; simp only [mem_iUnion, mem_univ, iff_true]
      exact ⟨a, Metric.mem_ball.mpr (by rw [dist_self]; positivity)⟩
    exact precise_refinement (fun a : X => Metric.ball a (1 / (2 * ((m : ℝ) + 1))))
      (fun _ => Metric.isOpen_ball) hcov
  choose V hVo hVcov hVlf hVref using hrefX
  -- For `n = 0`: `𝓑₀`; for `n = code + 1` with `(m, k) = Nat.unpair code`:
  -- `𝓒 n := Set.range (fun a : X => π '' (V m a ∩ interior (H k)))`.
  let 𝓒 : ℕ → Set (Set (CollapseQuot X F)) := fun n =>
    match n with
    | 0 => 𝓑₀
    | code + 1 =>
      let p := Nat.unpair code
      Set.range (fun a : X => π '' (V p.1 a ∩ interior (H p.2)))
  -- Helper: for `U ⊆ Fᶜ`, `π ⁻¹' (π '' U) = U`.
  have hpre_im_disj : ∀ U : Set X, Disjoint U F → π ⁻¹' (π '' U) = U := by
    intro U hUF
    ext x
    constructor
    · rintro ⟨x', hx'U, hfx⟩
      have hx'NotF : x' ∉ F := Set.disjoint_left.mp hUF hx'U
      have h1 : π x' = some ⟨x', hx'NotF⟩ :=
        (collapseProj_eq_some_iff F x' ⟨x', hx'NotF⟩).mpr rfl
      rw [h1] at hfx
      exact ((collapseProj_eq_some_iff F x ⟨x', hx'NotF⟩).mp hfx.symm) ▸ hx'U
    · intro hxU; exact ⟨x, hxU, rfl⟩
  have hC_open : ∀ n, ∀ B ∈ 𝓒 n, IsOpen B := by
    intro n B hB
    cases n with
    | zero => exact (hB₀_open B hB).1
    | succ code =>
      obtain ⟨a, rfl⟩ := hB
      rw [isOpen_collapseQuot_iff, hpre_im_disj _ ((hH_disj (Nat.unpair code).2).mono_left (inter_subset_right.trans interior_subset))]
      exact (hVo _ a).inter isOpen_interior
  have hC_cp : ∀ n, MSpace.ClosurePreserving (𝓒 n) := by
    intro n
    cases n with
    | zero => exact hB₀_cp
    | succ code =>
      let m := (Nat.unpair code).1
      let k := (Nat.unpair code).2
      intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro y hy
        -- Every member of `𝓖` is contained in `π '' H k`, which is CLOSED in `X / F` and avoids `none`!
        have hG_sub_H : ⋃₀ 𝓖 ⊆ π '' H k := by
          rintro z ⟨B, hBG, hzB⟩
          obtain ⟨a, rfl⟩ := h𝓖 hBG
          obtain ⟨x, ⟨_, hxInt⟩, rfl⟩ := hzB
          exact ⟨x, interior_subset hxInt, rfl⟩
        have hyH : y ∈ π '' H k := closure_minimal hG_sub_H (hπ_cl _ (hH_cl k)) hy
        obtain ⟨x, hxH, rfl⟩ := hyH
        have hxNotF : x ∉ F := Set.disjoint_left.mp (hH_disj k) hxH
        -- On `Fᶜ`, `V m` is locally finite at `x`!
        obtain ⟨t, ht_nhds, ht_fin⟩ := hVlf m x
        obtain ⟨O, hOt, hOo, hxO⟩ := mem_nhds_iff.mp ht_nhds
        let O' : Set X := O ∩ Fᶜ
        have hO'o : IsOpen O' := hOo.inter hFc_open
        have hxO' : x ∈ O' := ⟨hxO, hxNotF⟩
        let Oy : Set (CollapseQuot X F) := π '' O'
        have hOyo : IsOpen Oy := by
          rw [isOpen_collapseQuot_iff, hpre_im_disj O' (Set.disjoint_left.mpr fun _ h => h.2)]
          exact hO'o
        have hxyO : π x ∈ Oy := ⟨x, hxO', rfl⟩
        let 𝓔 : Set (Set (CollapseQuot X F)) := { B ∈ 𝓖 | (Oy ∩ B).Nonempty }
        have hE_fin : 𝓔.Finite := by
          have hsub : 𝓔 ⊆ (fun a : X => π '' (V m a ∩ interior (H k))) '' { a : X | (V m a ∩ t).Nonempty } := by
            rintro B ⟨hBG, ⟨w, hwOy, hwB⟩⟩
            obtain ⟨a, rfl⟩ := h𝓖 hBG
            obtain ⟨q₁, hq₁O', rfl⟩ := hwOy
            obtain ⟨q₂, ⟨hq₂V, hq₂Int⟩, hfq⟩ := hwB
            have hq₁q₂ : q₁ = q₂ := by
              have hq₂NotF : q₂ ∉ F := Set.disjoint_left.mp (hH_disj k) (interior_subset hq₂Int)
              have h1 : π q₂ = some ⟨q₂, hq₂NotF⟩ :=
                (collapseProj_eq_some_iff F q₂ ⟨q₂, hq₂NotF⟩).mpr rfl
              rw [h1] at hfq
              exact (collapseProj_eq_some_iff F q₁ ⟨q₂, hq₂NotF⟩).mp hfq.symm
            subst hq₁q₂
            exact ⟨a, ⟨q₁, hq₂V, hOt hq₁O'.1⟩, rfl⟩
          exact (ht_fin.image _).subset hsub
        have hyE : π x ∈ closure (⋃₀ 𝓔) := by
          rw [mem_closure_iff]; intro W hWo hxW
          obtain ⟨w, hwOW, ⟨B, hBG, hwB⟩⟩ :=
            mem_closure_iff.mp hy (Oy ∩ W) (hOyo.inter hWo) ⟨hxyO, hxW⟩
          exact ⟨w, hwOW.2, ⟨B, ⟨hBG, ⟨w, hwOW.1, hwB⟩⟩, hwB⟩⟩
        have hEcl : IsClosed (⋃₀ (closure '' 𝓔)) :=
          (hE_fin.image closure).isClosed_sUnion (by rintro _ ⟨_, _, rfl⟩; exact isClosed_closure)
        have hy_in := closure_minimal
          (fun w (hw : w ∈ ⋃₀ 𝓔) => by
            obtain ⟨B, hBE, hwB⟩ := hw
            exact ⟨closure B, ⟨B, hBE, rfl⟩, subset_closure hwB⟩) hEcl hyE
        obtain ⟨_, ⟨B, hBE, rfl⟩, hyClB⟩ := hy_in
        exact ⟨closure B, ⟨B, hBE.1, rfl⟩, hyClB⟩
      · rintro y ⟨_, ⟨B, hBG, rfl⟩, hyB⟩
        exact closure_mono (Set.subset_sUnion_of_mem hBG) hyB
  refine ⟨⟨𝓑₀, hB₀_open, hB₀_base, hB₀_cp⟩, ⟨hT3, ⋃ n, 𝓒 n, ?_, ⟨𝓒, hC_cp, rfl⟩⟩⟩
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    (fun B hB => by obtain ⟨n, hBn⟩ := mem_iUnion.mp hB; exact hC_open n B hBn) ?_
  intro y W hyW hWo
  cases y with
  | none =>
    obtain ⟨B, hBB₀, hBW⟩ := hB₀_base W hWo hyW
    exact ⟨B, mem_iUnion.mpr ⟨0, hBB₀⟩, (hB₀_open B hBB₀).2, hBW⟩
  | some x =>
    have hpre_o : IsOpen (π ⁻¹' W) := hWo.preimage hπ_cont
    have hxW : x.1 ∈ π ⁻¹' W := by
      change collapseProj F x.1 ∈ W
      rw [(collapseProj_eq_some_iff F x.1 x).mpr rfl]; exact hyW
    obtain ⟨ε, hε, hballW⟩ := Metric.isOpen_iff.mp hpre_o x.1 hxW
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
    obtain ⟨k, hxk⟩ := hH_int_cov x.1 x.2
    obtain ⟨a, hxa⟩ := mem_iUnion.mp (show x.1 ∈ ⋃ a, V m a by rw [hVcov m]; trivial)
    let code := Nat.pair m k
    have hpair : Nat.unpair code = (m, k) := Nat.unpair_pair m k
    let B : Set (CollapseQuot X F) := π '' (V m a ∩ interior (H k))
    refine ⟨B, mem_iUnion.mpr ⟨code + 1, a, by simp only [hpair, B]⟩, ?_, ?_⟩
    · exact ⟨x.1, ⟨hxa, hxk⟩, (collapseProj_eq_some_iff F x.1 x).mpr rfl⟩
    · rintro _ ⟨q, ⟨hqV, _⟩, rfl⟩
      have hqa : dist q a < 1 / (2 * ((m : ℝ) + 1)) := Metric.mem_ball.mp (hVref m a hqV)
      have hxa' : dist x.1 a < 1 / (2 * ((m : ℝ) + 1)) := Metric.mem_ball.mp (hVref m a hxa)
      have hqx : dist q x.1 < ε := by
        have htri : dist q x.1 ≤ dist q a + dist a x.1 := dist_triangle q a x.1
        rw [dist_comm a x.1] at htri
        have h2 : 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * ((m : ℝ) + 1)) = 1 / ((m : ℝ) + 1) := by
          field_simp; ring
        have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        have h3 : 1 / ((m : ℝ) + 1) < ε := by
          rw [div_lt_iff₀ hpos]
          have h1ε : 1 < ε * (m : ℝ) := by
            have := (div_lt_iff₀ hε).mp hm; linarith
          nlinarith
        linarith
      exact hballW (Metric.mem_ball.mpr hqx)

end Research.CollapseQuotMetricM1
