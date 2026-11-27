import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Indexed
import Targets.Defs

/-!
# Morita–Hanai–Stone (1956): Perfect Images of Metric Spaces are `M₁`

We prove:
1. `closurePreserving_compl_sUnion_of_locallyFinite`:
   for any locally finite family `𝓗` of closed subsets of a topological space `Y`, the open family
   `{ (⋃₀ 𝓢)ᶜ | 𝓢 ⊆ 𝓗 }` is **closure-preserving** (because on an open neighborhood meeting only
   finitely many members of `𝓗`, the family has at most finitely many distinct traces).
2. `isM1_of_sigma_locallyFinite_star_closed_cover`:
   any `T₃` space admitting a countable sequence of locally finite closed covers `𝓗 n` whose
   stars `⋃ { H ∈ 𝓗 n | y ∈ H }` form a local base at every point `y` is an **`M₁`-space**.
3. `isM1_of_perfectMap_from_metricSpace` (**Morita–Hanai–Stone 1956**):
   every perfect continuous image `f : X → Y` (closed continuous surjection with compact fibers)
   of a metric space `X` is an **`M₁`-space** (with `T₃` deduced automatically).
-/

namespace Research.MoritaHanaiStone

open Set Topology

/-- A family `𝓗 : Set (Set Y)` is locally finite if every point has an open neighborhood
meeting only finitely many members of `𝓗`. -/
def IsLocallyFiniteSet {Y : Type*} [TopologicalSpace Y] (𝓗 : Set (Set Y)) : Prop :=
  ∀ z : Y, ∃ O : Set Y, IsOpen O ∧ z ∈ O ∧ { H ∈ 𝓗 | (O ∩ H).Nonempty }.Finite

/-- Any subfamily of a locally finite family of closed sets has closed union. -/
theorem isClosed_sUnion_of_locallyFinite {Y : Type*} [TopologicalSpace Y]
    {𝓗 : Set (Set Y)} (hH_cl : ∀ H ∈ 𝓗, IsClosed H) (hH_lf : IsLocallyFiniteSet 𝓗)
    {𝓢 : Set (Set Y)} (h𝓢 : 𝓢 ⊆ 𝓗) :
    IsClosed (⋃₀ 𝓢) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨O, hOo, hzO, hOfin⟩ := hH_lf z
  let 𝓔 : Set (Set Y) := { H ∈ 𝓢 | (O ∩ H).Nonempty }
  have hEfin : 𝓔.Finite := hOfin.subset fun H hH => ⟨h𝓢 hH.1, hH.2⟩
  let W : Set Y := O \ ⋃₀ 𝓔
  have hEcl : IsClosed (⋃₀ 𝓔) := hEfin.isClosed_sUnion fun H hH => hH_cl H (h𝓢 hH.1)
  have hWo : IsOpen W := hOo.sdiff hEcl
  have hzW : z ∈ W := by
    refine ⟨hzO, ?_⟩
    rintro ⟨H, hHE, hzH⟩
    exact hz ⟨H, hHE.1, hzH⟩
  refine Filter.mem_of_superset (hWo.mem_nhds hzW) ?_
  intro y hyW hyS
  obtain ⟨H, hHS, hyH⟩ := hyS
  exact hyW.2 ⟨H, ⟨hHS, ⟨y, hyW.1, hyH⟩⟩, hyH⟩

/-- **Key Closure-Preserving Lemma**:
For any locally finite family `𝓗` of subsets of `Y`, the family of complements
`𝓑 := { (⋃₀ 𝓢)ᶜ | 𝓢 ⊆ 𝓗 }` is closure-preserving. -/
theorem closurePreserving_compl_sUnion_of_locallyFinite {Y : Type*} [TopologicalSpace Y]
    {𝓗 : Set (Set Y)} (hH_lf : IsLocallyFiniteSet 𝓗) :
    MSpace.ClosurePreserving { B : Set Y | ∃ 𝓢 ⊆ 𝓗, B = (⋃₀ 𝓢)ᶜ } := by
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · intro z hz
    obtain ⟨O, hOo, hzO, hOfin⟩ := hH_lf z
    let 𝓔 : Set (Set Y) := { H ∈ 𝓗 | (O ∩ H).Nonempty }
    have hEfin : 𝓔.Finite := hOfin
    -- For every `B ∈ 𝓖`, `B ∩ O = O \ ⋃₀ (𝓢 ∩ 𝓔)`, so `{ B ∩ O | B ∈ 𝓖 }` is finite!
    have htrace_sub :
        (fun B : Set Y => B ∩ O) '' 𝓖 ⊆
          (fun 𝓣 : Set (Set Y) => O \ ⋃₀ 𝓣) '' 𝒫 𝓔 := by
      rintro _ ⟨B, hBG, rfl⟩
      obtain ⟨𝓢, h𝓢, rfl⟩ := h𝓖 hBG
      refine ⟨𝓢 ∩ 𝓔, Set.inter_subset_right, ?_⟩
      ext y
      simp only [mem_inter_iff, mem_compl_iff, mem_sUnion, mem_sdiff]
      constructor
      · rintro ⟨hyO, hyNot⟩
        refine ⟨?_, hyO⟩
        rintro ⟨H, hHS, hyH⟩
        exact hyNot ⟨H, ⟨hHS, ⟨h𝓢 hHS, ⟨y, hyO, hyH⟩⟩⟩, hyH⟩
      · rintro ⟨hyNot, hyO⟩
        refine ⟨hyO, ?_⟩
        rintro ⟨H, ⟨hHS, _⟩, hyH⟩
        exact hyNot ⟨H, hHS, hyH⟩
    have htrace_fin : ((fun B : Set Y => B ∩ O) '' 𝓖).Finite :=
      (hEfin.powerset.image _).subset htrace_sub
    have hz_cl_trace : z ∈ closure (⋃₀ ((fun B : Set Y => B ∩ O) '' 𝓖)) := by
      rw [mem_closure_iff]
      intro V hVo hzV
      obtain ⟨y, hyOV, ⟨B, hBG, hyB⟩⟩ :=
        mem_closure_iff.mp hz (O ∩ V) (hOo.inter hVo) ⟨hzO, hzV⟩
      exact ⟨y, hyOV.2, ⟨B ∩ O, ⟨B, hBG, rfl⟩, hyB, hyOV.1⟩⟩
    have hcl_eq : closure (⋃₀ ((fun B : Set Y => B ∩ O) '' 𝓖)) =
        ⋃₀ (closure '' ((fun B : Set Y => B ∩ O) '' 𝓖)) := by
      apply Subset.antisymm
      · have hcl : IsClosed (⋃₀ (closure '' ((fun B : Set Y => B ∩ O) '' 𝓖))) :=
          (htrace_fin.image closure).isClosed_sUnion (by rintro _ ⟨_, _, rfl⟩; exact isClosed_closure)
        exact closure_minimal (fun y ⟨T, hT, hyT⟩ => ⟨closure T, ⟨T, hT, rfl⟩, subset_closure hyT⟩) hcl
      · rintro y ⟨_, ⟨T, hT, rfl⟩, hyT⟩
        exact closure_mono (Set.subset_sUnion_of_mem hT) hyT
    rw [hcl_eq] at hz_cl_trace
    obtain ⟨_, ⟨_, ⟨B, hBG, rfl⟩, rfl⟩, hzB⟩ := hz_cl_trace
    exact ⟨closure B, ⟨B, hBG, rfl⟩, closure_mono inter_subset_left hzB⟩
  · rintro z ⟨_, ⟨B, hBG, rfl⟩, hzB⟩
    exact closure_mono (Set.subset_sUnion_of_mem hBG) hzB

/-- **Morita's `M₁` Criterion**:
Any `T₃` space with a countable sequence of locally finite closed covers `𝓗 n` whose stars
form a local base at every point is an `M₁`-space. -/
theorem isM1_of_sigma_locallyFinite_star_closed_cover {Y : Type*} [TopologicalSpace Y]
    [T3Space Y]
    (𝓗 : ℕ → Set (Set Y))
    (hH_cl : ∀ n, ∀ H ∈ 𝓗 n, IsClosed H)
    (hH_lf : ∀ n, IsLocallyFiniteSet (𝓗 n))
    (hH_cov : ∀ n, ⋃₀ (𝓗 n) = Set.univ)
    (hH_star : ∀ y : Y, ∀ W : Set Y, IsOpen W → y ∈ W →
      ∃ n, ∀ H ∈ 𝓗 n, y ∈ H → H ⊆ W) :
    MSpace.IsM1 Y := by
  let 𝓑' : ℕ → Set (Set Y) := fun n => { B : Set Y | ∃ 𝓢 ⊆ 𝓗 n, B = (⋃₀ 𝓢)ᶜ }
  have hB'_cp : ∀ n, MSpace.ClosurePreserving (𝓑' n) := fun n =>
    closurePreserving_compl_sUnion_of_locallyFinite (hH_lf n)
  refine ⟨inferInstance, ⋃ n, 𝓑' n, ?_, ⟨𝓑', hB'_cp, rfl⟩⟩
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro B hB
    obtain ⟨n, 𝓢, h𝓢, rfl⟩ := mem_iUnion.mp hB
    exact (isClosed_sUnion_of_locallyFinite (hH_cl n) (hH_lf n) h𝓢).isOpen_compl
  · intro y W hyW hWo
    obtain ⟨n, hn⟩ := hH_star y W hWo hyW
    let 𝓢 : Set (Set Y) := { H ∈ 𝓗 n | y ∉ H }
    let B : Set Y := (⋃₀ 𝓢)ᶜ
    refine ⟨B, mem_iUnion.mpr ⟨n, 𝓢, fun _ h => h.1, rfl⟩, ?_, ?_⟩
    · rintro ⟨H, hHS, hyH⟩
      exact hHS.2 hyH
    · intro w hwB
      have hwU : w ∈ ⋃₀ (𝓗 n) := by rw [hH_cov n]; trivial
      obtain ⟨H, hHn, hwH⟩ := hwU
      have hyH : y ∈ H := by
        by_contra hyNot
        exact hwB ⟨H, ⟨hHn, hyNot⟩, hwH⟩
      exact hn H hHn hyH hwH

/-- A closed continuous surjection from a normal `T₁` space lands in a `T₃` space. -/
private theorem t3Space_of_isClosedMap_normal {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T1Space X] [NormalSpace X]
    {f : X → Y} (hf_cont : Continuous f) (hf_surj : Function.Surjective f)
    (hf_closed : IsClosedMap f) : T3Space Y := by
  have hT1 : T1Space Y := ⟨fun y => by
    obtain ⟨x, rfl⟩ := hf_surj y
    have hEq : ({f x} : Set Y) = f '' {x} := by simp
    rw [hEq]; exact hf_closed {x} isClosed_singleton⟩
  have hNorm : NormalSpace Y := ⟨fun A B hA hB hdisj => by
    obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ :=
      normal_separation (hA.preimage hf_cont) (hB.preimage hf_cont) (hdisj.preimage f)
    refine ⟨(f '' Uᶜ)ᶜ, (f '' Vᶜ)ᶜ,
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

/-- **Morita–Hanai–Stone (1956)**:
Every perfect continuous image (closed continuous surjection with compact fibers) of a
metric space is an `M₁`-space. -/
theorem isM1_of_perfectMap_from_metricSpace {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
    {f : X → Y}
    (hf_cont : Continuous f)
    (hf_surj : Function.Surjective f)
    (hf_closed : IsClosedMap f)
    (hf_comp : ∀ y : Y, IsCompact (f ⁻¹' {y})) :
    MSpace.IsM1 Y := by
  have hT3 : T3Space Y := t3Space_of_isClosedMap_normal hf_cont hf_surj hf_closed
  -- For each `n`, take a locally finite open refinement `U n` of `{ ball x (1 / (2*(n+1))) }`.
  have href : ∀ n : ℕ, ∃ U : X → Set X,
      (∀ x, IsOpen (U x)) ∧
      (⋃ x, U x) = Set.univ ∧
      LocallyFinite U ∧
      (∀ x, U x ⊆ Metric.ball x (1 / (2 * ((n : ℝ) + 1)))) := by
    intro n
    have hcov : (⋃ x : X, Metric.ball x (1 / (2 * ((n : ℝ) + 1)))) = Set.univ := by
      ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      refine ⟨x, Metric.mem_ball.mpr ?_⟩
      rw [dist_self]; positivity
    exact precise_refinement (fun x : X => Metric.ball x (1 / (2 * ((n : ℝ) + 1))))
      (fun _ => Metric.isOpen_ball) hcov
  choose U hUo hUcov hUlf hUref using href
  let 𝓗 : ℕ → Set (Set Y) := fun n => Set.range (fun x : X => f '' closure (U n x))
  refine isM1_of_sigma_locallyFinite_star_closed_cover 𝓗 ?_ ?_ ?_ ?_
  · intro n H hH
    obtain ⟨x, rfl⟩ := hH
    exact hf_closed _ isClosed_closure
  · intro n y
    -- `LocallyFinite (fun x => closure (U n x))` on `X`, plus compactness of `f ⁻¹' {y}`!
    have hclf : LocallyFinite (fun x : X => closure (U n x)) := (hUlf n).closure
    have hopen_ex : ∀ p : X, ∃ O : Set X, IsOpen O ∧ p ∈ O ∧
        { x : X | (O ∩ closure (U n x)).Nonempty }.Finite := by
      intro p
      obtain ⟨t, ht_nhds, ht_fin⟩ := hclf p
      obtain ⟨O, hOt, hOo, hpO⟩ := mem_nhds_iff.mp ht_nhds
      exact ⟨O, hOo, hpO, ht_fin.subset fun x ⟨q, hqO, hqU⟩ => ⟨q, hqU, hOt hqO⟩⟩
    choose Ox hOxo hOxmem hOxfin using hopen_ex
    obtain ⟨s, hs⟩ := (hf_comp y).elim_finite_subcover Ox hOxo (fun p _ => mem_iUnion.mpr ⟨p, hOxmem p⟩)
    let O : Set X := ⋃ p ∈ s, Ox p
    have hOo : IsOpen O := isOpen_biUnion fun p _ => hOxo p
    let V : Set Y := (f '' Oᶜ)ᶜ
    have hVo : IsOpen V := (hf_closed _ hOo.isClosed_compl).isOpen_compl
    have hyV : y ∈ V := by
      rintro ⟨p, hpOc, rfl⟩
      exact hpOc (hs (mem_singleton (f p)))
    have hidx_fin : { x : X | (O ∩ closure (U n x)).Nonempty }.Finite := by
      have hsub : { x : X | (O ∩ closure (U n x)).Nonempty } ⊆
          ⋃ p ∈ (s : Set X), { x : X | (Ox p ∩ closure (U n x)).Nonempty } := by
        rintro x ⟨q, hqO, hqU⟩
        obtain ⟨p, hps, hqOx⟩ := mem_iUnion₂.mp hqO
        exact mem_iUnion₂.mpr ⟨p, hps, ⟨q, hqOx, hqU⟩⟩
      exact (s.finite_toSet.biUnion fun p _ => hOxfin p).subset hsub
    refine ⟨V, hVo, hyV, ?_⟩
    have hHsub : { H ∈ 𝓗 n | (V ∩ H).Nonempty } ⊆
        (fun x : X => f '' closure (U n x)) '' { x : X | (O ∩ closure (U n x)).Nonempty } := by
      rintro _ ⟨⟨x, rfl⟩, ⟨z, hzV, ⟨q, hqU, rfl⟩⟩⟩
      have hqO : q ∈ O := by
        by_contra hqOc
        exact hzV ⟨q, hqOc, rfl⟩
      exact ⟨x, ⟨q, hqO, hqU⟩, rfl⟩
    exact (hidx_fin.image _).subset hHsub
  · intro n
    ext y
    simp only [mem_sUnion, mem_univ, iff_true, 𝓗]
    obtain ⟨x, rfl⟩ := hf_surj y
    have hxU : x ∈ ⋃ a, U n a := by rw [hUcov n]; trivial
    obtain ⟨a, hxa⟩ := mem_iUnion.mp hxU
    exact ⟨f '' closure (U n a), ⟨a, rfl⟩, x, subset_closure hxa, rfl⟩
  · intro y W hWo hyW
    -- Compactness of `f ⁻¹' {y}` inside open `f ⁻¹' W` gives a uniform Lebesgue radius!
    have hpre_o : IsOpen (f ⁻¹' W) := hWo.preimage hf_cont
    have hrad : ∀ p : f ⁻¹' {y}, ∃ ε : ℝ, 0 < ε ∧ Metric.ball p.1 ε ⊆ f ⁻¹' W := by
      intro p
      have hpW : p.1 ∈ f ⁻¹' W := by
        change f p.1 ∈ W
        have hp : f p.1 = y := p.2
        rw [hp]; exact hyW
      exact Metric.isOpen_iff.mp hpre_o p.1 hpW
    choose ε hε_pos hε_sub using hrad
    obtain ⟨s, hs⟩ := (hf_comp y).elim_finite_subcover
      (fun p : f ⁻¹' {y} => Metric.ball p.1 (ε p / 2))
      (fun _ => Metric.isOpen_ball)
      (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, Metric.mem_ball.mpr (by rw [dist_self]; linarith [hε_pos ⟨p, hp⟩])⟩)
    -- Bound `1 / (n + 1)` below `ε p / 2` for all `p ∈ s`.
    have hex_n : ∃ n : ℕ, ∀ p ∈ s, 1 / ((n : ℝ) + 1) < ε p / 2 := by
      by_cases hsne : s.Nonempty
      · let δ : ℝ := s.inf' hsne (fun p => ε p / 2)
        have hδ_pos : 0 < δ := by
          rw [Finset.lt_inf'_iff]
          intro p _; linarith [hε_pos p]
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
        refine ⟨n, fun p hp => ?_⟩
        have hδ_le : δ ≤ ε p / 2 := Finset.inf'_le (fun p => ε p / 2) hp
        have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have h1 : 1 / ((n : ℝ) + 1) < δ := by
          rw [div_lt_iff₀ hnpos]
          have h1δ : 1 < δ * (n : ℝ) := by
            have := (div_lt_iff₀ hδ_pos).mp hn
            linarith
          nlinarith
        linarith
      · exact ⟨0, fun p hp => (hsne ⟨p, hp⟩).elim⟩
    obtain ⟨n, hn⟩ := hex_n
    refine ⟨n, fun H hHn hyH w hwH => ?_⟩
    obtain ⟨a, rfl⟩ := hHn
    obtain ⟨p, hpCl, hfp⟩ := hyH
    obtain ⟨q, hqCl, rfl⟩ := hwH
    have hp_fib : p ∈ f ⁻¹' {y} := hfp
    obtain ⟨r, hrs, hpr⟩ := mem_iUnion₂.mp (hs hp_fib)
    have hcl_sub : closure (U n a) ⊆ Metric.closedBall a (1 / (2 * ((n : ℝ) + 1))) :=
      closure_minimal ((hUref n a).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
    have hpa : dist p a ≤ 1 / (2 * ((n : ℝ) + 1)) := Metric.mem_closedBall.mp (hcl_sub hpCl)
    have hqa : dist q a ≤ 1 / (2 * ((n : ℝ) + 1)) := Metric.mem_closedBall.mp (hcl_sub hqCl)
    have hqp : dist q p ≤ 1 / ((n : ℝ) + 1) := by
      have h1 : dist q p ≤ dist q a + dist a p := dist_triangle q a p
      rw [dist_comm a p] at h1
      have h2 : 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
        field_simp; ring
      linarith
    have hpr_dist : dist p r.1 < ε r / 2 := Metric.mem_ball.mp hpr
    have hqr_dist : dist q r.1 < ε r := by
      have h1 : dist q r.1 ≤ dist q p + dist p r.1 := dist_triangle q p r.1
      linarith [hn r hrs]
    exact hε_sub r (Metric.mem_ball.mpr hqr_dist)

/-- **Morita–Hanai–Stone (1956), compact-boundary form**:
Every closed continuous image of a metric space whose fiber boundaries `frontier (f ⁻¹' {y})`
are compact is an `M₁`-space (via restriction to a closed metric subspace on which `f` is perfect). -/
theorem isM1_of_closedMap_compact_frontier_from_metricSpace {X Y : Type*} [MetricSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf_cont : Continuous f)
    (hf_surj : Function.Surjective f)
    (hf_closed : IsClosedMap f)
    (hf_front : ∀ y : Y, IsCompact (frontier (f ⁻¹' {y}))) :
    MSpace.IsM1 Y := by
  classical
  have hT3 : T3Space Y := t3Space_of_isClosedMap_normal hf_cont hf_surj hf_closed
  -- Pick one representative `rep y ∈ f ⁻¹' {y}` for each `y : Y`.
  choose rep hrep using hf_surj
  -- Define `X₀ := ⋃ y, if (frontier (f ⁻¹' {y})).Nonempty then frontier (f ⁻¹' {y}) else {rep y}`.
  let S : Y → Set X := fun y =>
    if (frontier (f ⁻¹' {y})).Nonempty then frontier (f ⁻¹' {y}) else {rep y}
  let X₀ : Set X := ⋃ y, S y
  have hS_sub : ∀ y, S y ⊆ f ⁻¹' {y} := by
    intro y
    by_cases hne : (frontier (f ⁻¹' {y})).Nonempty
    · simp only [S, ite_eq_left hne]
      have hcl : IsClosed (f ⁻¹' {y}) := isClosed_singleton.preimage hf_cont
      exact hcl.frontier_subset
    · simp only [S, ite_eq_right hne]
      exact Set.singleton_subset_iff.mpr (hrep y)
  have hX₀_cl : IsClosed X₀ := by
    rw [← isOpen_compl_iff]
    have hEq : X₀ᶜ = ⋃ y, (f ⁻¹' {y} \ S y) := by
      ext x
      simp only [mem_compl_iff, mem_iUnion, mem_sdiff, X₀]
      constructor
      · intro hx
        refine ⟨f x, rfl, fun hxS => hx ⟨f x, hxS⟩⟩
      · rintro ⟨y, hfy, hxNotS⟩ ⟨z, hxSz⟩
        have hfz : f x = z := hS_sub z hxSz
        have hfy' : f x = y := hfy
        rw [hfz] at hfy'
        subst hfy'
        exact hxNotS hxSz
    rw [hEq]
    refine isOpen_iUnion fun y => ?_
    have hfib_cl : IsClosed (f ⁻¹' {y}) := isClosed_singleton.preimage hf_cont
    by_cases hne : (frontier (f ⁻¹' {y})).Nonempty
    · simp only [S, ite_eq_left hne]
      have hdiff : f ⁻¹' {y} \ frontier (f ⁻¹' {y}) = interior (f ⁻¹' {y}) := by
        rw [frontier, hfib_cl.closure_eq, sdiff_sdiff_eq_self interior_subset]
      rw [hdiff]
      exact isOpen_interior
    · simp only [S, ite_eq_right hne]
      have hfront_empty : frontier (f ⁻¹' {y}) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hfib_open : IsOpen (f ⁻¹' {y}) := by
        rw [frontier, hfib_cl.closure_eq, Set.sdiff_eq_empty] at hfront_empty
        rw [← interior_eq_iff_isOpen]
        exact Subset.antisymm interior_subset hfront_empty
      exact hfib_open.sdiff isClosed_singleton
  let g : X₀ → Y := fun x => f x.1
  have hg_cont : Continuous g := hf_cont.comp continuous_subtype_val
  have hg_surj : Function.Surjective g := by
    intro y
    by_cases hne : (frontier (f ⁻¹' {y})).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hne' : (frontier (f ⁻¹' {y})).Nonempty := ⟨x, hx⟩
      have hxS : x ∈ S y := by simp only [S, ite_eq_left hne']; exact hx
      exact ⟨⟨x, mem_iUnion.mpr ⟨y, hxS⟩⟩, hS_sub y hxS⟩
    · have hxS : rep y ∈ S y := by simp only [S, ite_eq_right hne]; exact mem_singleton _
      exact ⟨⟨rep y, mem_iUnion.mpr ⟨y, hxS⟩⟩, hrep y⟩
  have hg_closed : IsClosedMap g := by
    intro F hF
    have hF_X : IsClosed ((Subtype.val : X₀ → X) '' F) :=
      hX₀_cl.isClosedEmbedding_subtypeVal.isClosedMap F hF
    have hEq : g '' F = f '' ((Subtype.val : X₀ → X) '' F) := by
      ext y; simp [g]
    rw [hEq]
    exact hf_closed _ hF_X
  have hg_comp : ∀ y : Y, IsCompact (g ⁻¹' {y}) := by
    intro y
    have hS_comp : IsCompact (S y) := by
      by_cases hne : (frontier (f ⁻¹' {y})).Nonempty
      · simp only [S, ite_eq_left hne]; exact hf_front y
      · simp only [S, ite_eq_right hne]; exact isCompact_singleton
    have hpre_eq : (Subtype.val : X₀ → X) '' (g ⁻¹' {y}) = S y := by
      ext x
      constructor
      · rintro ⟨⟨x, hxX₀⟩, hfx, rfl⟩
        obtain ⟨z, hxSz⟩ := mem_iUnion.mp hxX₀
        have hfz : f x = z := hS_sub z hxSz
        have hfy : f x = y := hfx
        rw [hfz] at hfy; subst hfy
        exact hxSz
      · intro hxS
        exact ⟨⟨x, mem_iUnion.mpr ⟨y, hxS⟩⟩, hS_sub y hxS, rfl⟩
    exact Topology.IsInducing.subtypeVal.isCompact_iff.mpr (hpre_eq ▸ hS_comp)
  exact isM1_of_perfectMap_from_metricSpace hg_cont hg_surj hg_closed hg_comp

/-- **Morita–Hanai–Stone (1956), first-countable fibers**:
For any closed continuous map `f : X → Y` from a metric space `X`, every point `y ∈ Y`
with a countable neighborhood base has compact fiber boundary `frontier (f ⁻¹' {y})`. -/
theorem isCompact_frontier_of_closedMap_firstCountable {X Y : Type*} [MetricSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf_cont : Continuous f) (hf_closed : IsClosedMap f)
    {y : Y} (hfc : (𝓝 y).IsCountablyGenerated) :
    IsCompact (frontier (f ⁻¹' {y})) := by
  by_cases hy_rng : ∃ x : X, f x = y
  · obtain ⟨x₀, rfl⟩ := hy_rng
    have hy_cl : IsClosed ({f x₀} : Set Y) := by
      have hEq : ({f x₀} : Set Y) = f '' {x₀} := by simp
      rw [hEq]; exact hf_closed {x₀} isClosed_singleton
    have hfib_cl : IsClosed (f ⁻¹' {f x₀}) := hy_cl.preimage hf_cont
    rw [isCompact_iff_isSeqCompact]
    by_contra hnot
    unfold IsSeqCompact at hnot
    push Not at hnot
    obtain ⟨p, hp_mem, hp_no⟩ := hnot
    obtain ⟨V, hV_basis, -⟩ := (𝓝 (f x₀)).exists_antitone_basis
    have hq_ex : ∀ n : ℕ, ∃ q : X,
        q ∈ Metric.ball (p n) (1 / ((n : ℝ) + 1)) ∧ f q ∈ V n ∧ f q ≠ f x₀ := by
      intro n
      let U : Set X := Metric.ball (p n) (1 / ((n : ℝ) + 1)) ∩ f ⁻¹' (interior (V n))
      have hUo : IsOpen U := Metric.isOpen_ball.inter (isOpen_interior.preimage hf_cont)
      have hpn_fib : f (p n) = f x₀ := hfib_cl.frontier_subset (hp_mem n)
      have hpn_U : p n ∈ U := by
        refine ⟨Metric.mem_ball.mpr (by rw [dist_self]; positivity), ?_⟩
        change f (p n) ∈ interior (V n)
        rw [hpn_fib]
        exact mem_interior_iff_mem_nhds.mpr (hV_basis.mem_of_mem trivial)
      have hnot_sub : ¬ U ⊆ f ⁻¹' {f x₀} := fun hsub =>
        (hp_mem n).2 (mem_interior.mpr ⟨U, hsub, hUo, hpn_U⟩)
      obtain ⟨q, hqU, hqNot⟩ := Set.not_subset.mp hnot_sub
      exact ⟨q, hqU.1, interior_subset hqU.2, hqNot⟩
    choose q hq_ball hq_V hq_ne using hq_ex
    have hQ_cl : IsClosed (Set.range q) := by
      rw [← isSeqClosed_iff_isClosed]
      intro u z hu hz
      let idx : ℕ → ℕ := fun k => (hu k).choose
      have hidx_eq : ∀ k, q (idx k) = u k := fun k => (hu k).choose_spec
      by_cases hfin : (Set.range idx).Finite
      · have hex : ∃ n₀, ∀ N, ∃ k ≥ N, idx k = n₀ := by
          by_contra hall
          push Not at hall
          choose N hN using hall
          let S : Finset ℕ := hfin.toFinset
          let M : ℕ := S.sup N + 1
          have hM_mem : idx M ∈ S := hfin.mem_toFinset.mpr ⟨M, rfl⟩
          have hle : N (idx M) ≤ S.sup N := Finset.le_sup hM_mem
          exact hN (idx M) M (by omega) rfl
        obtain ⟨n₀, hn₀⟩ := hex
        let φ : ℕ → ℕ := Nat.rec (hn₀ 0).choose (fun _ ih => (hn₀ (ih + 1)).choose)
        have hφ_strict : StrictMono φ := strictMono_nat_of_lt_succ fun k => by
          have := (hn₀ (φ k + 1)).choose_spec.1
          change φ k < (hn₀ (φ k + 1)).choose
          omega
        have hφ_val : ∀ k, u (φ k) = q n₀ := by
          intro k
          rw [← hidx_eq (φ k)]
          cases k with
          | zero => rw [(hn₀ 0).choose_spec.2]
          | succ m => rw [(hn₀ (φ m + 1)).choose_spec.2]
        have h1 : Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 z) :=
          hz.comp hφ_strict.tendsto_atTop
        have h2 : Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 (q n₀)) := by
          have hconst : u ∘ φ = fun _ => q n₀ := funext hφ_val
          rw [hconst]
          exact tendsto_const_nhds
        exact ⟨n₀, (tendsto_nhds_unique h1 h2).symm⟩
      · -- Infinitely many indices: build strictly increasing `φ` with `idx ∘ φ` strictly increasing!
        have hunb : ∀ M : ℕ, ∃ k ≥ M, M < idx k := by
          intro M
          by_contra h
          push Not at h
          apply hfin
          have hsub : Set.range idx ⊆ (Finset.range M).image idx ∪ Finset.range (M + 1) := by
            rintro n ⟨k, rfl⟩
            by_cases hk : k < M
            · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem idx (Finset.mem_range.mpr hk)))
            · have hle : idx k ≤ M := h k (Nat.le_of_not_lt hk)
              exact Or.inr (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)))
          exact ((Finset.finite_toSet _).union (Finset.finite_toSet _)).subset hsub
        let φ : ℕ → ℕ := Nat.rec 0 (fun _ ih => (hunb (max ih (idx ih) + 1)).choose)
        have hφ_strict : StrictMono φ := strictMono_nat_of_lt_succ fun k => by
          have h1 := (hunb (max (φ k) (idx (φ k)) + 1)).choose_spec.1
          change φ k < (hunb (max (φ k) (idx (φ k)) + 1)).choose
          omega
        have hidxφ_strict : StrictMono (idx ∘ φ) := strictMono_nat_of_lt_succ fun k => by
          have h2 := (hunb (max (φ k) (idx (φ k)) + 1)).choose_spec.2
          change idx (φ k) < idx ((hunb (max (φ k) (idx (φ k)) + 1)).choose)
          omega
        have hq_tend : Filter.Tendsto (fun k => q (idx (φ k))) Filter.atTop (𝓝 z) := by
          have hEq : (fun k => q (idx (φ k))) = u ∘ φ := funext fun k => hidx_eq (φ k)
          rw [hEq]
          exact hz.comp hφ_strict.tendsto_atTop
        have hp_tend : Filter.Tendsto (p ∘ (idx ∘ φ)) Filter.atTop (𝓝 z) := by
          rw [Metric.tendsto_atTop] at hq_tend ⊢
          intro ε hε
          obtain ⟨N₁, hN₁⟩ := hq_tend (ε / 2) (half_pos hε)
          obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / ε)
          refine ⟨max N₁ N₂, fun k hk => ?_⟩
          have h1 : dist (q (idx (φ k))) z < ε / 2 := hN₁ k (le_trans (le_max_left _ _) hk)
          have h2 : dist (p (idx (φ k))) (q (idx (φ k))) < 1 / ((idx (φ k) : ℝ) + 1) := by
            rw [dist_comm]; exact Metric.mem_ball.mp (hq_ball (idx (φ k)))
          have hk_le : k ≤ idx (φ k) := hidxφ_strict.id_le k
          have hN2_le : N₂ ≤ idx (φ k) := le_trans (le_trans (le_max_right _ _) hk) hk_le
          have hpos : (0 : ℝ) < (idx (φ k) : ℝ) + 1 := by positivity
          have h3 : 1 / ((idx (φ k) : ℝ) + 1) < ε / 2 := by
            rw [div_lt_iff₀ hpos]
            have h2ε : 2 < ε * (N₂ : ℝ) := by
              have := (div_lt_iff₀ hε).mp hN₂
              linarith
            have hN2_real : (N₂ : ℝ) ≤ (idx (φ k) : ℝ) := Nat.cast_le.mpr hN2_le
            nlinarith
          have htri : dist (p (idx (φ k))) z ≤
              dist (p (idx (φ k))) (q (idx (φ k))) + dist (q (idx (φ k))) z :=
            dist_triangle _ _ _
          change dist (p (idx (φ k))) z < ε
          linarith
        have hz_front : z ∈ frontier (f ⁻¹' {f x₀}) :=
          isClosed_frontier.mem_of_tendsto hp_tend (Filter.Eventually.of_forall fun k => hp_mem (idx (φ k)))
        exact (hp_no z hz_front (idx ∘ φ) hidxφ_strict hp_tend).elim
    have hcl_im : IsClosed (f '' Set.range q) := hf_closed _ hQ_cl
    have hy_cl : f x₀ ∈ closure (f '' Set.range q) := by
      rw [mem_closure_iff]
      intro W hWo hyW
      obtain ⟨n, -, hVnW⟩ := hV_basis.mem_iff.mp (hWo.mem_nhds hyW)
      exact ⟨f (q n), hVnW (hq_V n), ⟨q n, ⟨n, rfl⟩, rfl⟩⟩
    rw [hcl_im.closure_eq] at hy_cl
    obtain ⟨_, ⟨n, rfl⟩, hfn⟩ := hy_cl
    exact hq_ne n hfn
  · have hEq : f ⁻¹' {y} = ∅ := by
      ext x; simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact fun h => hy_rng ⟨x, h⟩
    rw [hEq, frontier_empty]
    exact isCompact_empty

/-- **Morita–Hanai–Stone (1956), full theorem**:
Every first-countable closed continuous image of a metric space is an `M₁`-space. -/
theorem isM1_of_closedMap_firstCountable_from_metricSpace {X Y : Type*} [MetricSpace X]
    [TopologicalSpace Y] [FirstCountableTopology Y] {f : X → Y}
    (hf_cont : Continuous f) (hf_surj : Function.Surjective f) (hf_closed : IsClosedMap f) :
    MSpace.IsM1 Y :=
  isM1_of_closedMap_compact_frontier_from_metricSpace hf_cont hf_surj hf_closed
    (fun _ => isCompact_frontier_of_closedMap_firstCountable hf_cont hf_closed inferInstance)

end Research.MoritaHanaiStone
