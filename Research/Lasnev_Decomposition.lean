import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Indexed
import Defs.D_0001

/-!
# Lašnev's Decomposition Theorem (1965) & Fréchet–Urysohn Property of Closed Metric Images

We prove:
1. `frechetUrysohn_of_closedMap_from_metricSpace`:
   every closed continuous image `Y` of a metric space `X` is **Fréchet–Urysohn**:
   for every `S : Set Y` and `z ∈ closure S`, there is a sequence `u : ℕ → Y` in `S`
   converging to `z`.
2. `isCountablyGenerated_nhds_of_compact_frontier`:
   for any closed continuous surjection `f : X → Y` from a metric space `X` onto `Y`,
   every `y : Y` whose fiber boundary `frontier (f ⁻¹' {y})` is compact has a countable
   decreasing open neighborhood base in `Y` (and hence `Defs.D_0001.HasCPOuterBase y`).
3. `lasnev_decomposition_completeMetric` (**Lašnev 1965**):
   for any closed continuous surjection `f : X → Y` from a complete metric space `X` onto `Y`,
   there is a sequence `D : ℕ → Set Y` of **closed discrete** subsets of `Y` such that every
   `y ∉ ⋃ n, D n` has compact fiber boundary `frontier (f ⁻¹' {y})`, countable neighborhood
   base `(𝓝 y).IsCountablyGenerated`, and a closure-preserving open outer base
   `Defs.D_0001.HasCPOuterBase y`.
-/

namespace Research.LasnevDecomposition

open Set Topology Filter

/-- Every closed continuous image of a metric space is **Fréchet–Urysohn**. -/
theorem frechetUrysohn_of_closedMap_from_metricSpace {X Y : Type*} [MetricSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf_cont : Continuous f) (hf_surj : Function.Surjective f) (hf_closed : IsClosedMap f)
    {S : Set Y} {z : Y} (hz : z ∈ closure S) :
    ∃ u : ℕ → Y, (∀ k, u k ∈ S) ∧ Tendsto u atTop (𝓝 z) := by
  have hne : (closure (f ⁻¹' S) ∩ f ⁻¹' {z}).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hcl_im : IsClosed (f '' closure (f ⁻¹' S)) := hf_closed _ isClosed_closure
    have hS_sub : S ⊆ f '' closure (f ⁻¹' S) := fun y hyS => by
      obtain ⟨x, rfl⟩ := hf_surj y
      exact ⟨x, subset_closure hyS, rfl⟩
    have hz_in : z ∈ f '' closure (f ⁻¹' S) := closure_minimal hS_sub hcl_im hz
    obtain ⟨x, hxCl, hfx⟩ := hz_in
    have hx_mem : x ∈ closure (f ⁻¹' S) ∩ f ⁻¹' {z} := ⟨hxCl, hfx⟩
    rw [hemp] at hx_mem
    exact hx_mem
  obtain ⟨x, hxCl, hfx⟩ := hne
  obtain ⟨v, hv_mem, hv_tend⟩ := mem_closure_iff_seq_limit.mp hxCl
  refine ⟨f ∘ v, fun k => hv_mem k, ?_⟩
  have hfx' : f x = z := hfx
  rw [← hfx']
  exact (hf_cont.tendsto x).comp hv_tend

/-- In a closed continuous image of a metric space, any point `y` whose fiber boundary
`frontier (f ⁻¹' {y})` is compact has a decreasing countable open local base and
`Defs.D_0001.HasCPOuterBase y`. -/
theorem hasDecreasingOpenBase_of_compact_frontier {X Y : Type*} [MetricSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf_cont : Continuous f) (hf_surj : Function.Surjective f) (hf_closed : IsClosedMap f)
    {y : Y} (hcomp : IsCompact (frontier (f ⁻¹' {y}))) :
    ∃ V : ℕ → Set Y,
      (∀ n, IsOpen (V n)) ∧
      (∀ n, y ∈ V n) ∧
      (∀ m n, m ≤ n → V n ⊆ V m) ∧
      (∀ W, IsOpen W → y ∈ W → ∃ n, V n ⊆ W) := by
  have hy_cl : IsClosed ({y} : Set Y) := by
    obtain ⟨x₀, rfl⟩ := hf_surj y
    have hEq : ({f x₀} : Set Y) = f '' {x₀} := by simp
    rw [hEq]; exact hf_closed {x₀} isClosed_singleton
  have hfib_cl : IsClosed (f ⁻¹' {y}) := hy_cl.preimage hf_cont
  let U : ℕ → Set X := fun n =>
    interior (f ⁻¹' {y}) ∪ ⋃ p ∈ frontier (f ⁻¹' {y}), Metric.ball p (1 / ((n : ℝ) + 1))
  have hUo : ∀ n, IsOpen (U n) := fun n =>
    isOpen_interior.union (isOpen_biUnion fun _ _ => Metric.isOpen_ball)
  have hfib_sub_U : ∀ n, f ⁻¹' {y} ⊆ U n := by
    intro n x hx
    by_cases hint : x ∈ interior (f ⁻¹' {y})
    · exact Or.inl hint
    · refine Or.inr (mem_iUnion₂.mpr ⟨x, ⟨subset_closure hx, hint⟩, ?_⟩)
      rw [Metric.mem_ball, dist_self]; positivity
  have hU_anti : ∀ m n, m ≤ n → U n ⊆ U m := by
    intro m n hmn x hx
    rcases hx with hint | hball
    · exact Or.inl hint
    · obtain ⟨p, hpF, hxp⟩ := mem_iUnion₂.mp hball
      refine Or.inr (mem_iUnion₂.mpr ⟨p, hpF, ?_⟩)
      rw [Metric.mem_ball] at hxp ⊢
      have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
        linarith
      linarith
  let V : ℕ → Set Y := fun n => (f '' (U n)ᶜ)ᶜ
  refine ⟨V,
    fun n => (hf_closed _ (hUo n).isClosed_compl).isOpen_compl,
    fun n => by rintro ⟨x, hxUc, rfl⟩; exact hxUc (hfib_sub_U n rfl),
    fun m n hmn => Set.compl_subset_compl.mpr (image_mono (Set.compl_subset_compl.mpr (hU_anti m n hmn))),
    ?_⟩
  intro W hWo hyW
  have hpre_o : IsOpen (f ⁻¹' W) := hWo.preimage hf_cont
  have hrad : ∀ p : frontier (f ⁻¹' {y}), ∃ ε : ℝ, 0 < ε ∧ Metric.ball p.1 ε ⊆ f ⁻¹' W := by
    intro p
    have hp_fib : f p.1 = y := hfib_cl.frontier_subset p.2
    have hpW : p.1 ∈ f ⁻¹' W := by change f p.1 ∈ W; rw [hp_fib]; exact hyW
    exact Metric.isOpen_iff.mp hpre_o p.1 hpW
  choose ε hε_pos hε_sub using hrad
  obtain ⟨s, hs⟩ := hcomp.elim_finite_subcover
    (fun p : frontier (f ⁻¹' {y}) => Metric.ball p.1 (ε p / 2))
    (fun _ => Metric.isOpen_ball)
    (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, Metric.mem_ball.mpr (by rw [dist_self]; linarith [hε_pos ⟨p, hp⟩])⟩)
  have hex_n : ∃ n : ℕ, ∀ p ∈ s, 1 / ((n : ℝ) + 1) < ε p / 2 := by
    by_cases hsne : s.Nonempty
    · let δ : ℝ := s.inf' hsne (fun p => ε p / 2)
      have hδ_pos : 0 < δ := by
        rw [Finset.lt_inf'_iff]; intro p _; linarith [hε_pos p]
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
      refine ⟨n, fun p hp => ?_⟩
      have hδ_le : δ ≤ ε p / 2 := Finset.inf'_le (fun p => ε p / 2) hp
      have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h1 : 1 / ((n : ℝ) + 1) < δ := by
        rw [div_lt_iff₀ hnpos]
        have h1δ : 1 < δ * (n : ℝ) := by
          have := (div_lt_iff₀ hδ_pos).mp hn; linarith
        nlinarith
      linarith
    · exact ⟨0, fun p hp => (hsne ⟨p, hp⟩).elim⟩
  obtain ⟨n, hn⟩ := hex_n
  refine ⟨n, fun z hzV => ?_⟩
  obtain ⟨x, rfl⟩ := hf_surj z
  have hxU : x ∈ U n := by
    by_contra hxUc; exact hzV ⟨x, hxUc, rfl⟩
  rcases hxU with hint | hball
  · have hfx : f x = y := interior_subset hint
    rw [hfx]; exact hyW
  · obtain ⟨p, hpF, hxp⟩ := mem_iUnion₂.mp hball
    obtain ⟨r, hrs, hpr⟩ := mem_iUnion₂.mp (hs hpF)
    have hxr : dist x r.1 < ε r := by
      have h1 : dist x r.1 ≤ dist x p + dist p r.1 := dist_triangle x p r.1
      have h2 : dist x p < 1 / ((n : ℝ) + 1) := Metric.mem_ball.mp hxp
      have h3 : dist p r.1 < ε r / 2 := Metric.mem_ball.mp hpr
      linarith [hn r hrs]
    exact hε_sub r (Metric.mem_ball.mpr hxr)

/-- A point with a decreasing countable open local base has a closure-preserving open outer base. -/
private theorem hasCPOuterBase_of_decreasing_open_base {Y : Type*} [TopologicalSpace Y] {y : Y}
    {V : ℕ → Set Y}
    (hVo : ∀ n, IsOpen (V n)) (hVm : ∀ n, y ∈ V n)
    (hVa : ∀ m n, m ≤ n → V n ⊆ V m)
    (hVb : ∀ W, IsOpen W → y ∈ W → ∃ n, V n ⊆ W) :
    Defs.D_0001.HasCPOuterBase y := by
  refine ⟨Set.range V, ?_, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩; exact ⟨hVo n, hVm n⟩
  · intro W hWo hyW
    obtain ⟨n, hn⟩ := hVb W hWo hyW
    exact ⟨V n, ⟨n, rfl⟩, hn⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      by_cases hGne : 𝓖.Nonempty
      · let S : Set ℕ := { n | V n ∈ 𝓖 }
        have hSne : S.Nonempty := by
          obtain ⟨B, hBG⟩ := hGne
          obtain ⟨n, rfl⟩ := h𝓖 hBG
          exact ⟨n, hBG⟩
        classical
        let n₀ := Nat.find hSne
        have hn₀ : V n₀ ∈ 𝓖 := Nat.find_spec hSne
        have hsub : ⋃₀ 𝓖 ⊆ V n₀ := by
          rintro w ⟨B, hBG, hwB⟩
          obtain ⟨n, rfl⟩ := h𝓖 hBG
          exact hVa n₀ n (Nat.find_min' hSne hBG) hwB
        exact ⟨closure (V n₀), ⟨V n₀, hn₀, rfl⟩, closure_mono hsub hz⟩
      · rw [Set.not_nonempty_iff_eq_empty.mp hGne, sUnion_empty, closure_empty] at hz
        exact hz.elim
    · rintro z ⟨_, ⟨B, hBG, rfl⟩, hzB⟩
      exact closure_mono (Set.subset_sUnion_of_mem hBG) hzB

/-- **Lašnev's Decomposition Theorem (1965)** for complete metric spaces:
For any closed continuous surjection `f : X → Y` from a complete metric space `X` onto `Y`,
there is a sequence `D : ℕ → Set Y` of closed discrete subsets such that every `y ∉ ⋃ n, D n`
has compact fiber boundary `frontier (f ⁻¹' {y})`, countable neighborhood base, and
`Defs.D_0001.HasCPOuterBase y`. -/
theorem lasnev_decomposition_completeMetric {X Y : Type*} [MetricSpace X] [CompleteSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf_cont : Continuous f) (hf_surj : Function.Surjective f) (hf_closed : IsClosedMap f) :
    ∃ D : ℕ → Set Y,
      (∀ n (S : Set Y), S ⊆ D n → IsClosed S) ∧
      (∀ y : Y, y ∉ ⋃ n, D n →
        IsCompact (frontier (f ⁻¹' {y})) ∧
        (𝓝 y).IsCountablyGenerated ∧
        Defs.D_0001.HasCPOuterBase y) := by
  have hT1Y : T1Space Y := ⟨fun y => by
    obtain ⟨x, rfl⟩ := hf_surj y
    have hEq : ({f x} : Set Y) = f '' {x} := by simp
    rw [hEq]; exact hf_closed {x} isClosed_singleton⟩
  have href : ∀ n : ℕ, ∃ U : X → Set X,
      (∀ x, IsOpen (U x)) ∧
      (⋃ x, U x) = Set.univ ∧
      LocallyFinite U ∧
      (∀ x, U x ⊆ Metric.ball x (1 / (2 * ((n : ℝ) + 1)))) := by
    intro n
    have hcov : (⋃ x : X, Metric.ball x (1 / (2 * ((n : ℝ) + 1)))) = Set.univ := by
      ext x; simp only [mem_iUnion, mem_univ, iff_true]
      exact ⟨x, Metric.mem_ball.mpr (by rw [dist_self]; positivity)⟩
    exact precise_refinement (fun x : X => Metric.ball x (1 / (2 * ((n : ℝ) + 1))))
      (fun _ => Metric.isOpen_ball) hcov
  choose U hUo hUcov hUlf hUref using href
  let D : ℕ → Set Y := fun n =>
    { y : Y | ∀ s : Finset X, ¬ (frontier (f ⁻¹' {y}) ⊆ ⋃ a ∈ s, U n a) }
  refine ⟨D, ?_, ?_⟩
  · -- Part 1: Every subset `S ⊆ D n` is CLOSED in `Y`!
    intro n S hSD
    rw [← closure_subset_iff_isClosed]
    intro z hz
    by_contra hzS
    -- Fréchet–Urysohn: pick `u : ℕ → Y` in `S` with `u k → z`.
    have hne : (closure (f ⁻¹' S) ∩ f ⁻¹' {z}).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hcl_im : IsClosed (f '' closure (f ⁻¹' S)) := hf_closed _ isClosed_closure
      have hS_sub : S ⊆ f '' closure (f ⁻¹' S) := fun y hyS => by
        obtain ⟨x, rfl⟩ := hf_surj y
        exact ⟨x, subset_closure hyS, rfl⟩
      obtain ⟨x, hxCl, hfx⟩ := closure_minimal hS_sub hcl_im hz
      have hx_mem : x ∈ closure (f ⁻¹' S) ∩ f ⁻¹' {z} := ⟨hxCl, hfx⟩
      rw [hemp] at hx_mem; exact hx_mem
    obtain ⟨x₀, hx₀Cl, hfx₀⟩ := hne
    obtain ⟨v, hv_mem, hv_tend⟩ := mem_closure_iff_seq_limit.mp hx₀Cl
    have hu_tend : Tendsto (f ∘ v) atTop (𝓝 z) := by
      have hfx₀' : f x₀ = z := hfx₀
      rw [← hfx₀']; exact (hf_cont.tendsto x₀).comp hv_tend
    -- Build the sequence `(k m, a m, p m)` by recursion on `m : ℕ`.
    classical
    let Triple := ℕ × X × X
    let State (m : ℕ) := { seq : Fin m → Triple //
      (∀ i, f (v (seq i).1) ∈ S) ∧
      (∀ i j, i < j → (seq i).1 < (seq j).1) ∧
      (∀ i j, i ≠ j → (seq i).2.1 ≠ (seq j).2.1) ∧
      (∀ i, (seq i).2.2 ∈ frontier (f ⁻¹' {f (v (seq i).1)})) ∧
      (∀ i, (seq i).2.2 ∈ U n (seq i).2.1) }
    have hnext_ex : ∀ (m : ℕ) (st : State m),
        ∃ st' : State (m + 1), ∀ i : Fin m, st'.1 i.castSucc = st.1 i := by
      intro m st
      let maxK : ℕ := if hm : 0 < m then (st.1 ⟨m - 1, by omega⟩).1 + 1 else 0
      let TY : Set Y := Set.range (fun i : Fin m => f (v (st.1 i).1))
      have hTY_cl : IsClosed TY := (Set.finite_range _).isClosed
      have hz_not_TY : z ∉ TY := by
        rintro ⟨i, hi⟩; exact hzS (hi ▸ st.2.1 i)
      obtain ⟨N, _⟩ :=
        Filter.eventually_atTop.mp (hu_tend.eventually (hTY_cl.isOpen_compl.mem_nhds hz_not_TY))
      let k := max maxK N
      have hkD : f (v k) ∈ D n := hSD (hv_mem k)
      let sA : Finset X := Finset.univ.image (fun i : Fin m => (st.1 i).2.1)
      obtain ⟨p, hpF, hpNot⟩ := Set.not_subset.mp (hkD sA)
      have hpU : p ∈ ⋃ a, U n a := by rw [hUcov n]; trivial
      obtain ⟨a, hpa⟩ := mem_iUnion.mp hpU
      have ha_ne : ∀ i : Fin m, a ≠ (st.1 i).2.1 := fun i heq =>
        hpNot (mem_iUnion₂.mpr ⟨a, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩, hpa⟩)
      have hk_gt : ∀ i : Fin m, (st.1 i).1 < k := fun i => by
        have hm : 0 < m := Nat.pos_of_ne_zero (by intro h; subst h; exact Fin.elim0 i)
        have hle_last : (st.1 i).1 ≤ (st.1 ⟨m - 1, by omega⟩).1 := by
          rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt i.2) with heq | hlt
          · have : i = ⟨m - 1, by omega⟩ := Fin.ext heq
            rw [this]
          · exact (st.2.2.1 i ⟨m - 1, by omega⟩ hlt).le
        have hmaxK : maxK = (st.1 ⟨m - 1, by omega⟩).1 + 1 := by
          simp only [maxK, dite_eq_left hm]
        have : maxK ≤ k := le_max_left _ _
        omega
      refine ⟨⟨Fin.snoc st.1 (k, a, p), ?_, ?_, ?_, ?_, ?_⟩, fun i => by simp only [Fin.snoc_castSucc]⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simp only [Fin.snoc_last]; exact hv_mem k
        · intro j; simp only [Fin.snoc_castSucc]; exact st.2.1 j
      · intro i j
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · refine Fin.lastCases (fun h => (lt_irrefl _ h).elim) (fun i' _ => ?_) i
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          exact hk_gt i'
        · refine Fin.lastCases (fun h => (Nat.not_lt.mpr (Nat.le_of_lt j'.2) h).elim) (fun i' h => ?_) i
          simp only [Fin.snoc_castSucc]
          exact st.2.2.1 i' j' h
      · intro i j
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · refine Fin.lastCases (fun h => (h rfl).elim) (fun i' _ => ?_) i
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          exact (ha_ne i').symm
        · refine Fin.lastCases (fun _ => ?_) (fun i' h => ?_) i
          · simp only [Fin.snoc_last, Fin.snoc_castSucc]
            exact ha_ne j'
          · simp only [Fin.snoc_castSucc]
            exact st.2.2.2.1 i' j' (fun e => h (congrArg Fin.castSucc e))
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last]; exact hpF
        · simp only [Fin.snoc_castSucc]; exact st.2.2.2.2.1 j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last]; exact hpa
        · simp only [Fin.snoc_castSucc]; exact st.2.2.2.2.2 j
    let stSeq : (m : ℕ) → State m := fun m =>
      Nat.rec ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, fun i => i.elim0⟩ (fun k stk => (hnext_ex k stk).choose) m
    have hst_agree : ∀ (m : ℕ) (i : Fin m), (stSeq (m + 1)).1 i.castSucc = (stSeq m).1 i :=
      fun m i => (hnext_ex m (stSeq m)).choose_spec i
    have hst_le : ∀ {m r : ℕ} (h : m ≤ r) (i : Fin m),
        (stSeq r).1 ⟨i.1, lt_of_lt_of_le i.2 h⟩ = (stSeq m).1 i := by
      intro m r h i
      induction h with
      | refl => rfl
      | @step k hmk ih =>
        rw [← ih]
        exact hst_agree k ⟨i.1, lt_of_lt_of_le i.2 hmk⟩
    let idx : ℕ → ℕ := fun m => ((stSeq (m + 1)).1 ⟨m, Nat.lt_succ_self m⟩).1
    let aSeq : ℕ → X := fun m => ((stSeq (m + 1)).1 ⟨m, Nat.lt_succ_self m⟩).2.1
    let pSeq : ℕ → X := fun m => ((stSeq (m + 1)).1 ⟨m, Nat.lt_succ_self m⟩).2.2
    have hidx_strict : StrictMono idx := by
      intro i j hij
      have h1 : (stSeq (j + 1)).1 ⟨i, by omega⟩ = (stSeq (i + 1)).1 ⟨i, Nat.lt_succ_self i⟩ :=
        hst_le (m := i + 1) (r := j + 1) (by omega) ⟨i, Nat.lt_succ_self i⟩
      have h2 := (stSeq (j + 1)).2.2.1 ⟨i, by omega⟩ ⟨j, Nat.lt_succ_self j⟩ hij
      simpa only [idx, h1] using h2
    have ha_inj : Function.Injective aSeq := by
      intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 : (stSeq (j + 1)).1 ⟨i, by omega⟩ = (stSeq (i + 1)).1 ⟨i, Nat.lt_succ_self i⟩ :=
          hst_le (m := i + 1) (r := j + 1) (by omega) ⟨i, Nat.lt_succ_self i⟩
        have h2 := (stSeq (j + 1)).2.2.2.1 ⟨i, by omega⟩ ⟨j, Nat.lt_succ_self j⟩
          (by intro e; exact hne (congrArg Fin.val e))
        exact h2 (by simpa only [aSeq, h1] using hij)
      · have h1 : (stSeq (i + 1)).1 ⟨j, by omega⟩ = (stSeq (j + 1)).1 ⟨j, Nat.lt_succ_self j⟩ :=
          hst_le (m := j + 1) (r := i + 1) (by omega) ⟨j, Nat.lt_succ_self j⟩
        have h2 := (stSeq (i + 1)).2.2.2.1 ⟨j, by omega⟩ ⟨i, Nat.lt_succ_self i⟩
          (by intro e; exact hne (congrArg Fin.val e).symm)
        exact h2 (by simpa only [aSeq, h1] using hij.symm)
    have hp_fib : ∀ m, f (pSeq m) = f (v (idx m)) := by
      intro m
      have hfib_cl : IsClosed (f ⁻¹' {f (v (idx m))}) := isClosed_singleton.preimage hf_cont
      exact hfib_cl.frontier_subset ((stSeq (m + 1)).2.2.2.2.1 ⟨m, Nat.lt_succ_self m⟩)
    have hp_U : ∀ m, pSeq m ∈ U n (aSeq m) := fun m =>
      (stSeq (m + 1)).2.2.2.2.2 ⟨m, Nat.lt_succ_self m⟩
    -- Since `U n` is locally finite and `aSeq` is injective, `P := Set.range pSeq` is CLOSED in `X`!
    have hP_cl : IsClosed (Set.range pSeq) := by
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨t, ht_nhds, ht_fin⟩ := hUlf n x
      obtain ⟨O, hOt, hOo, hxO⟩ := mem_nhds_iff.mp ht_nhds
      let E : Set ℕ := { m | pSeq m ∈ O }
      have hE_fin : E.Finite := by
        have hsub : aSeq '' E ⊆ { a | (U n a ∩ t).Nonempty } := by
          rintro _ ⟨m, hmO, rfl⟩
          exact ⟨pSeq m, hp_U m, hOt hmO⟩
        exact (ht_fin.subset hsub).of_finite_image (fun i _ j _ h => ha_inj h)
      have hPE_cl : IsClosed (pSeq '' E) := (hE_fin.image pSeq).isClosed
      let W : Set X := O \ (pSeq '' E)
      have hWo : IsOpen W := hOo.sdiff hPE_cl
      have hxW : x ∈ W := ⟨hxO, by rintro ⟨m, _, rfl⟩; exact hx ⟨m, rfl⟩⟩
      refine Filter.mem_of_superset (hWo.mem_nhds hxW) ?_
      rintro q ⟨hqO, hqNot⟩ ⟨m, rfl⟩
      exact hqNot ⟨m, hqO, rfl⟩
    -- Therefore `f '' Set.range pSeq` is CLOSED in `Y`, contains `f (v (idx m)) → z`, so `z ∈ f '' Set.range pSeq ⊆ S`, contradiction!
    have hcl_im : IsClosed (f '' Set.range pSeq) := hf_closed _ hP_cl
    have htend_sub : Tendsto (fun m => f (v (idx m))) atTop (𝓝 z) :=
      hu_tend.comp hidx_strict.tendsto_atTop
    have hz_im : z ∈ f '' Set.range pSeq :=
      hcl_im.mem_of_tendsto htend_sub (Filter.Eventually.of_forall fun m => ⟨pSeq m, ⟨m, rfl⟩, hp_fib m⟩)
    obtain ⟨_, ⟨m, rfl⟩, hfm⟩ := hz_im
    rw [hp_fib m] at hfm
    exact hzS (hfm ▸ hv_mem (idx m))
  · -- Part 2: Every `y ∉ ⋃ n, D n` has totally bounded (hence compact, since `X` is complete!) fiber boundary!
    intro y hyNot
    have hy_cov : ∀ n, ∃ s : Finset X, frontier (f ⁻¹' {y}) ⊆ ⋃ a ∈ s, U n a := by
      intro n
      by_contra h
      push Not at h
      exact hyNot (mem_iUnion.mpr ⟨n, h⟩)
    have htb : TotallyBounded (frontier (f ⁻¹' {y})) := by
      rw [Metric.totallyBounded_iff]
      intro ε hε
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 * ε))
      obtain ⟨s, hs⟩ := hy_cov n
      refine ⟨(s : Set X), s.finite_toSet, ?_⟩
      intro p hp
      obtain ⟨a, has, hpa⟩ := mem_iUnion₂.mp (hs hp)
      refine mem_iUnion₂.mpr ⟨a, has, ?_⟩
      have hdist : dist p a < 1 / (2 * ((n : ℝ) + 1)) := Metric.mem_ball.mp (hUref n a hpa)
      have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
      have hlt : 1 / (2 * ((n : ℝ) + 1)) < ε := by
        rw [div_lt_iff₀ hpos]
        have h1 : 1 < 2 * ε * (n : ℝ) := by
          have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ε)).mp hn
          linarith
        nlinarith
      exact Metric.mem_ball.mpr (lt_trans hdist hlt)
    have hcomp : IsCompact (frontier (f ⁻¹' {y})) :=
      isCompact_iff_totallyBounded_isComplete.mpr ⟨htb, isClosed_frontier.isComplete⟩
    obtain ⟨V, hVo, hVm, hVa, hVb⟩ :=
      hasDecreasingOpenBase_of_compact_frontier hf_cont hf_surj hf_closed hcomp
    have hfc : (𝓝 y).IsCountablyGenerated := by
      have hbasis : (𝓝 y).HasBasis (fun _ : ℕ => True) V := by
        refine Filter.hasBasis_iff.mpr fun W => ?_
        constructor
        · intro hW
          obtain ⟨O, hOW, hOo, hyO⟩ := mem_nhds_iff.mp hW
          obtain ⟨n, hn⟩ := hVb O hOo hyO
          exact ⟨n, trivial, hn.trans hOW⟩
        · rintro ⟨n, -, hn⟩
          exact Filter.mem_of_superset ((hVo n).mem_nhds (hVm n)) hn
      exact hbasis.isCountablyGenerated
    exact ⟨hcomp, hfc, hasCPOuterBase_of_decreasing_open_base hVo hVm hVa hVb⟩

end Research.LasnevDecomposition
