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
import Defs.D_0001

/-!
# Slaughter (1973): Every Closed Continuous Image of a Complete Metric Space is `M₁`

We prove **Slaughter's (1973) Theorem** for complete metric spaces:
> Let `X` be a complete metric space and `f : X → Y` a closed continuous surjection onto a
> topological space `Y`. Then `Y` is an **`M₁`-space** (has a `σ`-closure-preserving open base).

Our proof synthesizes five structural ingredients, all self-contained and kernel-verified:
1. **Borges (1966) / Heath–Lutzer–Zenor (1973)**: `Y` is stratifiable, hence collectionwise normal
   (every closed discrete subset `D ⊆ Y` has a discrete open expansion).
2. **Lašnev Decomposition (1965)**: `Y = Y₀ ∪ ⋃ m, D m` where each `D m` is closed discrete in `Y`
   and every `y ∈ Y₀` has compact fiber `f ⁻¹' {y}`.
3. **HCP-Complement Closure-Preservation Theorem**: in any `T₁` Fréchet–Urysohn space `Y`,
   for any hereditarily closure-preserving (HCP) family `𝓗`, the complement family
   `{ (⋃ a ∈ S, 𝓗 a)ᶜ | S }` is closure-preserving.
4. **Compact-Fiber Star Base**: the HCP-complement families `𝓑 m` for `𝓗 m a := f '' closure (U m a)`
   form a `σ`-CP open family giving a local base at every `y ∈ Y₀`.
5. **Whitney + HCP Pointwise Outer Bases on `D m`**: every `y ∈ D m` has a CP open outer base `𝓑_y`
   in `Y`, which combined with the discrete open expansion of `D m` yields a single CP open family
   `𝓒 m` giving a local base at every `y ∈ D m`. Interleaving `𝓑 m` and `𝓒 m` yields a
   `σ`-closure-preserving open base of `Y`.
-/

namespace Research.SlaughterCompleteMetricM1

open Set Topology Filter

/-! ## Part 1: HCP-Complement CP Theorem & Fréchet–Urysohn -/

private def IsHCP {Y ι : Type*} [TopologicalSpace Y] (𝓗 : ι → Set Y) : Prop :=
  ∀ S : ι → Set Y, (∀ i, S i ⊆ 𝓗 i) → closure (⋃ i, S i) = ⋃ i, closure (S i)

private def IsFrechetUrysohn (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ S : Set Y, ∀ z ∈ closure S, ∃ u : ℕ → Y, (∀ k, u k ∈ S) ∧ Tendsto u atTop (𝓝 z)

private theorem isHCP_image_of_locallyFinite_isClosedMap {X Y ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf_cont : Continuous f) (hf_closed : IsClosedMap f)
    {F : ι → Set X} (hFlf : LocallyFinite F) :
    IsHCP (fun i => f '' F i) := by
  intro S hS
  apply Subset.antisymm
  · let T : ι → Set X := fun i => f ⁻¹' S i ∩ F i
    have hT_lf : LocallyFinite T := hFlf.subset (fun _ => inter_subset_right)
    have hT_cl_closed : IsClosed (⋃ i, closure (T i)) := by
      rw [← hT_lf.closure_iUnion]; exact isClosed_closure
    have hfT_closed : IsClosed (f '' ⋃ i, closure (T i)) := hf_closed _ hT_cl_closed
    have hS_sub_im : (⋃ i, S i) ⊆ f '' ⋃ i, closure (T i) := by
      rintro y hy; obtain ⟨i, hySi⟩ := mem_iUnion.mp hy
      obtain ⟨x, hxFi, rfl⟩ := hS i hySi
      exact ⟨x, mem_iUnion.mpr ⟨i, subset_closure ⟨hySi, hxFi⟩⟩, rfl⟩
    intro y hy
    obtain ⟨x, hxU, rfl⟩ := closure_minimal hS_sub_im hfT_closed hy
    obtain ⟨i, hxCl⟩ := mem_iUnion.mp hxU
    have hfx_cl : f x ∈ closure (f '' T i) :=
      image_closure_subset_closure_image hf_cont ⟨x, hxCl, rfl⟩
    exact mem_iUnion.mpr ⟨i, closure_mono (by rintro _ ⟨q, ⟨hqS, _⟩, rfl⟩; exact hqS) hfx_cl⟩
  · intro y hy; obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    exact closure_mono (subset_iUnion S i) hyi

private theorem isFrechetUrysohn_of_closedMap_from_metricSpace {X Y : Type*} [MetricSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf_cont : Continuous f) (hf_surj : Function.Surjective f) (hf_closed : IsClosedMap f) :
    IsFrechetUrysohn Y := by
  intro S z hz
  have hne : (closure (f ⁻¹' S) ∩ f ⁻¹' {z}).Nonempty := by
    by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hS_sub : S ⊆ f '' closure (f ⁻¹' S) := fun y hyS => by
      obtain ⟨x, rfl⟩ := hf_surj y; exact ⟨x, subset_closure hyS, rfl⟩
    obtain ⟨x, hxCl, hfx⟩ := closure_minimal hS_sub (hf_closed _ isClosed_closure) hz
    have hx_mem : x ∈ closure (f ⁻¹' S) ∩ f ⁻¹' {z} := ⟨hxCl, hfx⟩
    rw [hemp] at hx_mem; exact hx_mem
  obtain ⟨x, hxCl, hfx⟩ := hne
  obtain ⟨v, hv_mem, hv_tend⟩ := mem_closure_iff_seq_limit.mp hxCl
  refine ⟨f ∘ v, fun k => hv_mem k, ?_⟩
  have hfx' : f x = z := hfx; rw [← hfx']
  exact (hf_cont.tendsto x).comp hv_tend

private theorem isFrechetUrysohn_subtype {Y : Type*} [TopologicalSpace Y]
    (hFU : IsFrechetUrysohn Y) (U : Set Y) : IsFrechetUrysohn U := by
  intro S z hz
  have hz_clY : z.1 ∈ closure ((Subtype.val : U → Y) '' S) := by
    rw [mem_closure_iff]; intro V hVo hzV
    obtain ⟨y, hyV, hyS⟩ :=
      mem_closure_iff.mp hz ((Subtype.val : U → Y) ⁻¹' V) (hVo.preimage continuous_subtype_val) hzV
    exact ⟨y.1, hyV, ⟨y, hyS, rfl⟩⟩
  obtain ⟨u, huS, hu_tend⟩ := hFU _ z.1 hz_clY
  have huU : ∀ k, u k ∈ U := fun k => by obtain ⟨y, _, hy⟩ := huS k; exact hy ▸ y.2
  refine ⟨fun k => ⟨u k, huU k⟩, fun k => ?_, tendsto_subtype_rng.mpr hu_tend⟩
  obtain ⟨y, hyS, hy⟩ := huS k
  have heq : (⟨u k, huU k⟩ : U) = y := Subtype.ext hy.symm
  change (⟨u k, huU k⟩ : U) ∈ S; rw [heq]; exact hyS

private theorem hcp_no_infinite_distinct_hits {Y ι : Type*} [TopologicalSpace Y] [T1Space Y]
    {𝓗 : ι → Set Y} (hHCP : IsHCP 𝓗)
    {w : ℕ → Y} {z : Y} (hw_ne : ∀ k, w k ≠ z) (hw_tend : Tendsto w atTop (𝓝 z))
    {idx : ℕ → ι} (hidx_inj : Function.Injective idx) (hw_hit : ∀ k, w k ∈ 𝓗 (idx k)) :
    False := by
  classical
  let S : ι → Set Y := fun i => { y | ∃ k, idx k = i ∧ y = w k }
  have hS_sub : ∀ i, S i ⊆ 𝓗 i := by rintro i _ ⟨k, rfl, rfl⟩; exact hw_hit k
  have hS_cl : ∀ i, closure (S i) = S i := fun i => by
    have hsub : S i ⊆ (fun k => w k) '' { k | idx k = i } := by
      rintro _ ⟨k, rfl, rfl⟩; exact ⟨k, rfl, rfl⟩
    have hsub2 : { k | idx k = i }.Subsingleton := fun a ha b hb => hidx_inj (ha.trans hb.symm)
    exact ((hsub2.finite.image _).subset hsub).isClosed.closure_eq
  have hU_eq : (⋃ i, S i) = Set.range w := by
    ext y; simp only [mem_iUnion, mem_range, S]
    exact ⟨fun ⟨_, k, _, hy⟩ => ⟨k, hy.symm⟩, fun ⟨k, hk⟩ => ⟨idx k, k, rfl, hk.symm⟩⟩
  have hcl_eq : closure (Set.range w) = Set.range w := by
    rw [← hU_eq, hHCP S hS_sub]; ext y; simp only [mem_iUnion, hS_cl]
  have hz_cl : z ∈ closure (Set.range w) :=
    mem_closure_of_tendsto hw_tend (Eventually.of_forall fun k => ⟨k, rfl⟩)
  rw [hcl_eq] at hz_cl
  obtain ⟨k, hk⟩ := hz_cl
  exact hw_ne k hk

private theorem exists_subseq_deciding_finset {Y ι : Type*} (𝓗 : ι → Set Y) (w : ℕ → Y)
    (E : Finset ι) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i ∈ E, (∀ m, w (φ m) ∈ 𝓗 i) ∨ (∀ m, w (φ m) ∉ 𝓗 i) := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, fun _ h => (Finset.notMem_empty _ h).elim⟩
  | @insert a E ha ih =>
    obtain ⟨φ, hφ_strict, hφ_dec⟩ := ih
    by_cases hinf : ∀ N : ℕ, ∃ m ≥ N, w (φ m) ∈ 𝓗 a
    · let ψ : ℕ → ℕ := Nat.rec (hinf 0).choose (fun _ k => (hinf (k + 1)).choose)
      have hψ_strict : StrictMono ψ := strictMono_nat_of_lt_succ fun k => by
        have := (hinf (ψ k + 1)).choose_spec.1
        change ψ k < (hinf (ψ k + 1)).choose; omega
      refine ⟨φ ∘ ψ, hφ_strict.comp hψ_strict, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hiE
      · refine Or.inl fun m => ?_
        cases m with
        | zero => exact (hinf 0).choose_spec.2
        | succ k => exact (hinf (ψ k + 1)).choose_spec.2
      · rcases hφ_dec i hiE with h1 | h2
        · exact Or.inl fun m => h1 (ψ m)
        · exact Or.inr fun m => h2 (ψ m)
    · push Not at hinf; obtain ⟨N, hN⟩ := hinf
      let ψ : ℕ → ℕ := fun m => m + N
      have hψ_strict : StrictMono ψ := fun _ _ h => Nat.add_lt_add_right h N
      refine ⟨φ ∘ ψ, hφ_strict.comp hψ_strict, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hiE
      · exact Or.inr fun m => hN (m + N) (Nat.le_add_left N m)
      · rcases hφ_dec i hiE with h1 | h2
        · exact Or.inl fun m => h1 (ψ m)
        · exact Or.inr fun m => h2 (ψ m)

private theorem closurePreserving_compl_sUnion_of_isHCP_frechetUrysohn {Y ι : Type*}
    [TopologicalSpace Y] [T1Space Y] (hFU : IsFrechetUrysohn Y)
    {𝓗 : ι → Set Y} (hHCP : IsHCP 𝓗) :
    MSpace.ClosurePreserving { B : Set Y | ∃ S : Set ι, B = (⋃ i ∈ S, 𝓗 i)ᶜ } := by
  classical
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · intro z hz
    by_contra hz_not
    obtain ⟨w, hw_mem, hw_tend⟩ := hFU (⋃₀ 𝓖) z hz
    have hw_ne : ∀ k, w k ≠ z := fun k heq => by
      obtain ⟨B, hBG, hwkB⟩ := hw_mem k
      exact hz_not ⟨closure B, ⟨B, hBG, rfl⟩, subset_closure (heq ▸ hwkB)⟩
    have hSk_ex : ∀ k, ∃ S : Set ι, (⋃ i ∈ S, 𝓗 i)ᶜ ∈ 𝓖 ∧ w k ∈ (⋃ i ∈ S, 𝓗 i)ᶜ := fun k => by
      obtain ⟨B, hBG, hwkB⟩ := hw_mem k; obtain ⟨S, rfl⟩ := h𝓖 hBG; exact ⟨S, hBG, hwkB⟩
    choose S hSG hwkS using hSk_ex
    let E : Set ι := { i : ι | { k : ℕ | w k ∈ 𝓗 i }.Infinite }
    have hE_fin : E.Finite := by
      by_contra hE_inf
      let State (m : ℕ) := { seq : Fin m → ℕ × ι //
        (∀ a b, a < b → (seq a).1 < (seq b).1) ∧
        (∀ a b, a ≠ b → (seq a).2 ≠ (seq b).2) ∧
        (∀ a, w (seq a).1 ∈ 𝓗 (seq a).2) }
      have hnext_ex : ∀ (m : ℕ) (st : State m),
          ∃ st' : State (m + 1), ∀ a : Fin m, st'.1 a.castSucc = st.1 a := by
        intro m st
        let used : Set ι := Set.range (fun a : Fin m => (st.1 a).2)
        obtain ⟨i, hiE, hiNot⟩ := Set.not_subset.mp
          (fun hsub => hE_inf ((Set.finite_range (fun a : Fin m => (st.1 a).2)).subset hsub))
        let maxK : ℕ := if hm : 0 < m then (st.1 ⟨m - 1, by omega⟩).1 + 1 else 0
        have hk_ex : ∃ k ≥ maxK, w k ∈ 𝓗 i := by
          by_contra hnone; push Not at hnone; apply hiE
          have hsub : { k : ℕ | w k ∈ 𝓗 i } ⊆ (Finset.range maxK : Set ℕ) := by
            intro k hk; by_contra hkNot; rw [Finset.mem_coe, Finset.mem_range] at hkNot
            exact hnone k (Nat.le_of_not_lt hkNot) hk
          exact (Finset.finite_toSet _).subset hsub
        obtain ⟨k, hk_ge, hwk⟩ := hk_ex
        have hk_gt : ∀ a : Fin m, (st.1 a).1 < k := fun a => by
          have hm : 0 < m := Nat.pos_of_ne_zero (by intro h; subst h; exact Fin.elim0 a)
          have hle_last : (st.1 a).1 ≤ (st.1 ⟨m - 1, by omega⟩).1 := by
            rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt a.2) with heq | hlt
            · have : a = ⟨m - 1, by omega⟩ := Fin.ext heq; rw [this]
            · exact (st.2.1 a ⟨m - 1, by omega⟩ hlt).le
          have hmaxK : maxK = (st.1 ⟨m - 1, by omega⟩).1 + 1 := by simp only [maxK, dite_eq_left hm]
          omega
        refine ⟨⟨Fin.snoc st.1 (k, i), ?_, ?_, ?_⟩, fun a => by simp only [Fin.snoc_castSucc]⟩
        · intro a b
          refine Fin.lastCases ?_ (fun b' => ?_) b
          · refine Fin.lastCases (fun h => (lt_irrefl _ h).elim) (fun a' _ => ?_) a
            simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact hk_gt a'
          · refine Fin.lastCases (fun h => (Nat.not_lt.mpr (Nat.le_of_lt b'.2) h).elim) (fun a' h => ?_) a
            simp only [Fin.snoc_castSucc]; exact st.2.1 a' b' h
        · intro a b
          refine Fin.lastCases ?_ (fun b' => ?_) b
          · refine Fin.lastCases (fun h => (h rfl).elim) (fun a' _ => ?_) a
            simp only [Fin.snoc_last, Fin.snoc_castSucc]; intro heq; exact hiNot ⟨a', heq⟩
          · refine Fin.lastCases (fun _ => ?_) (fun a' h => ?_) a
            · simp only [Fin.snoc_last, Fin.snoc_castSucc]; intro heq; exact hiNot ⟨b', heq.symm⟩
            · simp only [Fin.snoc_castSucc]; exact st.2.2.1 a' b' (fun e => h (congrArg Fin.castSucc e))
        · intro a
          refine Fin.lastCases ?_ (fun a' => ?_) a
          · simp only [Fin.snoc_last]; exact hwk
          · simp only [Fin.snoc_castSucc]; exact st.2.2.2 a'
      let stSeq : (m : ℕ) → State m := fun m =>
        Nat.rec ⟨Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
          (fun k stk => (hnext_ex k stk).choose) m
      have hst_le : ∀ {m r : ℕ} (h : m ≤ r) (a : Fin m),
          (stSeq r).1 ⟨a.1, lt_of_lt_of_le a.2 h⟩ = (stSeq m).1 a := by
        intro m r h a; induction h with
        | refl => rfl
        | @step k hmk ih => rw [← ih]; exact (hnext_ex k (stSeq k)).choose_spec ⟨a.1, lt_of_lt_of_le a.2 hmk⟩
      let kSeq : ℕ → ℕ := fun m => ((stSeq (m + 1)).1 ⟨m, Nat.lt_succ_self m⟩).1
      let iSeq : ℕ → ι := fun m => ((stSeq (m + 1)).1 ⟨m, Nat.lt_succ_self m⟩).2
      have hk_strict : StrictMono kSeq := fun a b hab => by
        have h1 := hst_le (m := a + 1) (r := b + 1) (by omega) ⟨a, Nat.lt_succ_self a⟩
        have h2 := (stSeq (b + 1)).2.1 ⟨a, by omega⟩ ⟨b, Nat.lt_succ_self b⟩ hab
        simpa only [kSeq, h1] using h2
      have hi_inj : Function.Injective iSeq := fun a b hab => by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have h1 := hst_le (m := a + 1) (r := b + 1) (by omega) ⟨a, Nat.lt_succ_self a⟩
          have h2 := (stSeq (b + 1)).2.2.1 ⟨a, by omega⟩ ⟨b, Nat.lt_succ_self b⟩
            (by intro e; exact hne (congrArg Fin.val e))
          exact h2 (by simpa only [iSeq, h1] using hab)
        · have h1 := hst_le (m := b + 1) (r := a + 1) (by omega) ⟨b, Nat.lt_succ_self b⟩
          have h2 := (stSeq (a + 1)).2.2.1 ⟨b, by omega⟩ ⟨a, Nat.lt_succ_self a⟩
            (by intro e; exact hne (congrArg Fin.val e).symm)
          exact h2 (by simpa only [iSeq, h1] using hab.symm)
      exact hcp_no_infinite_distinct_hits hHCP (fun m => hw_ne (kSeq m))
        (hw_tend.comp hk_strict.tendsto_atTop) hi_inj
        (fun m => (stSeq (m + 1)).2.2.2 ⟨m, Nat.lt_succ_self m⟩)
    obtain ⟨φ, hφ_strict, hφ_dec⟩ := exists_subseq_deciding_finset 𝓗 w hE_fin.toFinset
    have hz_not_B0 : z ∉ closure (⋃ i ∈ S (φ 0), 𝓗 i)ᶜ := fun hzB0 =>
      hz_not ⟨closure (⋃ i ∈ S (φ 0), 𝓗 i)ᶜ, ⟨_, hSG (φ 0), rfl⟩, hzB0⟩
    let O : Set Y := (closure (⋃ i ∈ S (φ 0), 𝓗 i)ᶜ)ᶜ
    have hO_sub : O ⊆ ⋃ i ∈ S (φ 0), 𝓗 i := fun y hyO => by
      by_contra hyNot; exact hyO (subset_closure hyNot)
    obtain ⟨M, hM⟩ :=
      Filter.eventually_atTop.mp ((hw_tend.comp hφ_strict.tendsto_atTop).eventually
        (isClosed_closure.isOpen_compl.mem_nhds hz_not_B0))
    have hj_ex : ∀ m : ℕ, ∃ j : ι, j ∈ S (φ 0) ∧ w (φ (m + M)) ∈ 𝓗 j ∧ j ∉ E := by
      intro m
      obtain ⟨j, hjS, hwj⟩ := mem_iUnion₂.mp (hO_sub (hM (m + M) (Nat.le_add_left M m)))
      refine ⟨j, hjS, hwj, fun hjE => ?_⟩
      rcases hφ_dec j (hE_fin.mem_toFinset.mpr hjE) with hall | hnone
      · exact hwkS (φ 0) (mem_iUnion₂.mpr ⟨j, hjS, hall 0⟩)
      · exact hnone (m + M) hwj
    choose j _ hj_hit hj_notE using hj_ex
    have hstep_ψ : ∀ (m : ℕ) (prev : Fin m → ℕ),
        ∃ k : ℕ, (∀ a, prev a < k) ∧ ∀ a, j k ≠ j (prev a) := by
      intro m prev
      let used : Set ι := Set.range (fun a : Fin m => j (prev a))
      have hsub_fin : { k : ℕ | j k ∈ used }.Finite := by
        have hEq : { k : ℕ | j k ∈ used } ⊆ ⋃ i ∈ used, { k : ℕ | w (φ (k + M)) ∈ 𝓗 i } :=
          fun k hk => mem_iUnion₂.mpr ⟨j k, hk, hj_hit k⟩
        refine ((Set.finite_range _).biUnion fun i hi => ?_).subset hEq
        obtain ⟨a, rfl⟩ := hi
        have hnotInf : { r : ℕ | w r ∈ 𝓗 (j (prev a)) }.Finite := Set.not_infinite.mp (hj_notE (prev a))
        have hpre : (fun k : ℕ => φ (k + M)) ⁻¹' { r : ℕ | w r ∈ 𝓗 (j (prev a)) } =
            { k : ℕ | w (φ (k + M)) ∈ 𝓗 (j (prev a)) } := rfl
        rw [← hpre]
        exact hnotInf.preimage ((hφ_strict.comp (fun _ _ h => Nat.add_lt_add_right h M)).injective.injOn)
      let maxP : ℕ := if hm : 0 < m then Finset.univ.sup prev + 1 else 0
      have hex : ∃ k ≥ maxP, j k ∉ used := by
        by_contra hnone; push Not at hnone
        have hsub : (Set.univ : Set ℕ) ⊆ (Finset.range maxP : Set ℕ) ∪ { k | j k ∈ used } := by
          intro k _
          by_cases hk : k < maxP
          · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_range.mpr hk))
          · exact Or.inr (hnone k (Nat.le_of_not_lt hk))
        exact Set.infinite_univ (((Finset.finite_toSet _).union hsub_fin).subset hsub)
      obtain ⟨k, hk_ge, hk_not⟩ := hex
      refine ⟨k, fun a => ?_, fun a heq => hk_not ⟨a, heq.symm⟩⟩
      have hm : 0 < m := Nat.pos_of_ne_zero (by intro h; subst h; exact Fin.elim0 a)
      have hle : prev a ≤ Finset.univ.sup prev := Finset.le_sup (Finset.mem_univ a)
      have hmaxP : maxP = Finset.univ.sup prev + 1 := by simp only [maxP, dite_eq_left hm]
      omega
    let State2 (m : ℕ) := { seq : Fin m → ℕ //
      (∀ a b, a < b → seq a < seq b) ∧ (∀ a b, a ≠ b → j (seq a) ≠ j (seq b)) }
    have hnext2 : ∀ (m : ℕ) (st : State2 m),
        ∃ st' : State2 (m + 1), ∀ a : Fin m, st'.1 a.castSucc = st.1 a := by
      intro m st; obtain ⟨k, hk_gt, hk_ne⟩ := hstep_ψ m st.1
      refine ⟨⟨Fin.snoc st.1 k, ?_, ?_⟩, fun a => by simp only [Fin.snoc_castSucc]⟩
      · intro a b
        refine Fin.lastCases ?_ (fun b' => ?_) b
        · refine Fin.lastCases (fun h => (lt_irrefl _ h).elim) (fun a' _ => ?_) a
          simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact hk_gt a'
        · refine Fin.lastCases (fun h => (Nat.not_lt.mpr (Nat.le_of_lt b'.2) h).elim) (fun a' h => ?_) a
          simp only [Fin.snoc_castSucc]; exact st.2.1 a' b' h
      · intro a b
        refine Fin.lastCases ?_ (fun b' => ?_) b
        · refine Fin.lastCases (fun h => (h rfl).elim) (fun a' _ => ?_) a
          simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact (hk_ne a').symm
        · refine Fin.lastCases (fun _ => ?_) (fun a' h => ?_) a
          · simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact hk_ne b'
          · simp only [Fin.snoc_castSucc]; exact st.2.2 a' b' (fun e => h (congrArg Fin.castSucc e))
    let stSeq2 : (m : ℕ) → State2 m := fun m =>
      Nat.rec ⟨Fin.elim0, fun a => a.elim0, fun a => a.elim0⟩ (fun k stk => (hnext2 k stk).choose) m
    have hst2_le : ∀ {m r : ℕ} (h : m ≤ r) (a : Fin m),
        (stSeq2 r).1 ⟨a.1, lt_of_lt_of_le a.2 h⟩ = (stSeq2 m).1 a := by
      intro m r h a; induction h with
      | refl => rfl
      | @step k hmk ih => rw [← ih]; exact (hnext2 k (stSeq2 k)).choose_spec ⟨a.1, lt_of_lt_of_le a.2 hmk⟩
    let ψ : ℕ → ℕ := fun m => (stSeq2 (m + 1)).1 ⟨m, Nat.lt_succ_self m⟩
    have hψ_strict : StrictMono ψ := fun a b hab => by
      have h1 := hst2_le (m := a + 1) (r := b + 1) (by omega) ⟨a, Nat.lt_succ_self a⟩
      have h2 := (stSeq2 (b + 1)).2.1 ⟨a, by omega⟩ ⟨b, Nat.lt_succ_self b⟩ hab
      simpa only [ψ, h1] using h2
    have hjψ_inj : Function.Injective (j ∘ ψ) := fun a b hab => by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 := hst2_le (m := a + 1) (r := b + 1) (by omega) ⟨a, Nat.lt_succ_self a⟩
        have h2 := (stSeq2 (b + 1)).2.2 ⟨a, by omega⟩ ⟨b, Nat.lt_succ_self b⟩
          (by intro e; exact hne (congrArg Fin.val e))
        exact h2 (by simpa only [Function.comp_apply, ψ, h1] using hab)
      · have h1 := hst2_le (m := b + 1) (r := a + 1) (by omega) ⟨b, Nat.lt_succ_self b⟩
        have h2 := (stSeq2 (a + 1)).2.2 ⟨b, by omega⟩ ⟨a, Nat.lt_succ_self a⟩
          (by intro e; exact hne (congrArg Fin.val e).symm)
        exact h2 (by simpa only [Function.comp_apply, ψ, h1] using hab.symm)
    let τ : ℕ → ℕ := fun r => φ (ψ r + M)
    have hτ_strict : StrictMono τ :=
      hφ_strict.comp (StrictMono.comp (fun _ _ h => Nat.add_lt_add_right h M) hψ_strict)
    exact hcp_no_infinite_distinct_hits hHCP (fun r => hw_ne (τ r))
      (hw_tend.comp hτ_strict.tendsto_atTop) hjψ_inj (fun r => hj_hit (ψ r))
  · rintro z ⟨_, ⟨B, hBG, rfl⟩, hzB⟩
    exact closure_mono (Set.subset_sUnion_of_mem hBG) hzB

/-! ## Part 2: Pointwise CP Outer Base in Every Lašnev Space -/

private theorem lasnev_point_hasCPOuterBase {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
    {f : X → Y}
    (hf_cont : Continuous f) (hf_surj : Function.Surjective f) (hf_closed : IsClosedMap f)
    (y₀ : Y) : Defs.D_0001.HasCPOuterBase y₀ := by
  classical
  have hT1Y : T1Space Y := ⟨fun y => by
    obtain ⟨x, rfl⟩ := hf_surj y
    have hEq : ({f x} : Set Y) = f '' {x} := by simp
    rw [hEq]; exact hf_closed {x} isClosed_singleton⟩
  have hFU_Y : IsFrechetUrysohn Y :=
    isFrechetUrysohn_of_closedMap_from_metricSpace hf_cont hf_surj hf_closed
  let F : Set X := f ⁻¹' {y₀}
  have hF : IsClosed F := isClosed_singleton.preimage hf_cont
  have hFc_open : IsOpen Fᶜ := hF.isOpen_compl
  let X' := { x : X // x ∉ F }
  let Y' := { y : Y // y ≠ y₀ }
  have hY'_open : IsOpen ({y₀}ᶜ : Set Y) := isClosed_singleton.isOpen_compl
  have hFU_Y' : IsFrechetUrysohn Y' := isFrechetUrysohn_subtype hFU_Y {y₀}ᶜ
  have hr_ex : ∀ a : X', ∃ r : ℝ, 0 < r ∧ Metric.ball a.1 (3 * r) ⊆ Fᶜ := by
    intro a
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hFc_open a.1 a.2
    refine ⟨ρ / 3, by linarith, ?_⟩
    have hEq : 3 * (ρ / 3) = ρ := by ring
    rw [hEq]; exact hball
  choose r hr_pos hr_ball using hr_ex
  let cov : X' → Set X' := fun a => Metric.ball a (r a)
  have hcov_univ : (⋃ a : X', cov a) = Set.univ := by
    ext a; simp only [mem_iUnion, mem_univ, iff_true, cov]
    exact ⟨a, Metric.mem_ball.mpr (by rw [dist_self]; exact hr_pos a)⟩
  obtain ⟨W, hWo, hWcov, hWlf, hWref⟩ := precise_refinement cov (fun _ => Metric.isOpen_ball) hcov_univ
  let WX : X' → Set X := fun a => (Subtype.val : X' → X) '' W a
  have hWX_sub_ball : ∀ a : X', WX a ⊆ Metric.ball a.1 (r a) := by
    rintro a _ ⟨q, hqW, rfl⟩; exact hWref a hqW
  have hWX_cl_disj : ∀ a : X', Disjoint (closure (WX a)) F := by
    intro a; rw [Set.disjoint_left]; intro x hxCl hxF
    have hcl_sub : closure (WX a) ⊆ Metric.closedBall a.1 (r a) :=
      closure_minimal ((hWX_sub_ball a).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
    have hxa : dist x a.1 ≤ r a := Metric.mem_closedBall.mp (hcl_sub hxCl)
    exact hr_ball a (Metric.mem_ball.mpr (by linarith [hr_pos a])) hxF
  let f' : X' → Y' := fun x => ⟨f x.1, x.2⟩
  have hf'_cont : Continuous f' := (hf_cont.comp continuous_subtype_val).subtype_mk _
  have hf'_closed : IsClosedMap f' := by
    intro C hC; rw [isClosed_induced_iff] at hC ⊢
    obtain ⟨D, hDcl, hDC⟩ := hC
    refine ⟨f '' D, hf_closed D hDcl, ?_⟩
    ext y; constructor
    · rintro ⟨x, hxD, hfx⟩
      have hxNotF : x ∉ F := fun hxF => y.2 (hfx.symm.trans hxF)
      exact ⟨⟨x, hxNotF⟩, by rw [← hDC]; exact hxD, Subtype.ext hfx⟩
    · rintro ⟨x, hxC, hfx⟩
      exact ⟨x.1, by rw [← hDC] at hxC; exact hxC, congrArg Subtype.val hfx⟩
  let 𝓗' : X' → Set Y' := fun a => f' '' closure (W a)
  have hH'_hcp : IsHCP 𝓗' := isHCP_image_of_locallyFinite_isClosedMap hf'_cont hf'_closed hWlf.closure
  let 𝓗 : X' → Set Y := fun a => f '' closure (WX a)
  have hH_not_y0 : ∀ a, y₀ ∉ 𝓗 a := by
    rintro a ⟨x, hxCl, hfx⟩; exact Set.disjoint_left.mp (hWX_cl_disj a) hxCl hfx
  have hH_pre : ∀ a, (Subtype.val : Y' → Y) ⁻¹' 𝓗 a = 𝓗' a := by
    intro a; ext y; constructor
    · rintro ⟨x, hxCl, hfx⟩
      have hxNotF : x ∉ F := Set.disjoint_left.mp (hWX_cl_disj a) hxCl
      refine ⟨⟨x, hxNotF⟩, ?_, Subtype.ext hfx⟩
      rw [mem_closure_iff]; intro V hVo hxV
      obtain ⟨q, hqV, hqWX⟩ := mem_closure_iff.mp hxCl ((Subtype.val : X' → X) '' V)
        (hFc_open.isOpenMap_subtype_val _ hVo) ⟨⟨x, hxNotF⟩, hxV, rfl⟩
      obtain ⟨q₁, hq₁V, rfl⟩ := hqV
      obtain ⟨q₂, hq₂W, hqeq⟩ := hqWX
      have : q₂ = q₁ := Subtype.ext hqeq; subst this; exact ⟨q₂, hq₁V, hq₂W⟩
    · rintro ⟨x, hxCl, hfx⟩
      exact ⟨x.1, image_closure_subset_closure_image continuous_subtype_val ⟨x, hxCl, rfl⟩,
        congrArg Subtype.val hfx⟩
  let 𝓑 : Set (Set Y) := { U : Set Y | ∃ S : Set X', y₀ ∉ closure (⋃ a ∈ S, 𝓗 a) ∧ U = (⋃ a ∈ S, 𝓗 a)ᶜ }
  refine ⟨𝓑, ?_, ?_, ?_⟩
  · rintro U ⟨S, hy₀Not, rfl⟩
    have hcl : IsClosed (⋃ a ∈ S, 𝓗 a) := by
      rw [← closure_subset_iff_isClosed]; intro z hz
      have hz_ne : z ≠ y₀ := fun heq => hy₀Not (heq ▸ hz)
      have hz' : (⟨z, hz_ne⟩ : Y') ∈ closure (⋃ a ∈ S, 𝓗' a) := by
        rw [mem_closure_iff]; intro V hVo hzV
        obtain ⟨q, hqVY, hqU⟩ := mem_closure_iff.mp hz ((Subtype.val : Y' → Y) '' V)
          (hY'_open.isOpenMap_subtype_val _ hVo) ⟨⟨z, hz_ne⟩, hzV, rfl⟩
        obtain ⟨q', hq'V, rfl⟩ := hqVY; obtain ⟨a, haS, hq'H⟩ := mem_iUnion₂.mp hqU
        exact ⟨q', hq'V, mem_iUnion₂.mpr ⟨a, haS, by rw [← hH_pre a]; exact hq'H⟩⟩
      let T : X' → Set Y' := fun a => if a ∈ S then 𝓗' a else ∅
      have hT_eq : (⋃ a, T a) = ⋃ a ∈ S, 𝓗' a := by
        ext q; simp only [mem_iUnion, T]; constructor
        · rintro ⟨a, ha⟩; by_cases haS : a ∈ S
          · simp only [ite_eq_left haS] at ha; exact ⟨a, haS, ha⟩
          · simp only [ite_eq_right haS] at ha; exact ha.elim
        · rintro ⟨a, haS, ha⟩; exact ⟨a, by simp only [ite_eq_left haS]; exact ha⟩
      have hT_cl : ∀ a, closure (T a) = T a := fun a => by
        by_cases haS : a ∈ S
        · simp only [T, ite_eq_left haS]; exact (hf'_closed _ isClosed_closure).closure_eq
        · simp only [T, ite_eq_right haS, closure_empty]
      rw [← hT_eq, hH'_hcp T (fun a => by by_cases h : a ∈ S <;> simp [T, h])] at hz'
      obtain ⟨a, ha⟩ := mem_iUnion.mp hz'; rw [hT_cl a] at ha
      by_cases haS : a ∈ S
      · simp only [T, ite_eq_left haS] at ha
        exact mem_iUnion₂.mpr ⟨a, haS, by rw [← hH_pre a] at ha; exact ha⟩
      · simp only [T, ite_eq_right haS] at ha; exact ha.elim
    refine ⟨hcl.isOpen_compl, fun hy => ?_⟩
    obtain ⟨a, _, ha⟩ := mem_iUnion₂.mp hy; exact hH_not_y0 a ha
  · intro O hOo hy₀O
    have hpre_o : IsOpen (f ⁻¹' O) := hOo.preimage hf_cont
    have hF_sub : F ⊆ f ⁻¹' O := fun x hxF => by
      change f x ∈ O; have : f x = y₀ := hxF; rw [this]; exact hy₀O
    let S : Set X' := { a : X' | (WX a ∩ (f ⁻¹' O)ᶜ).Nonempty }
    have hSdisj : Disjoint (closure (⋃ a ∈ S, WX a)) F := by
      rw [Set.disjoint_left]; intro x₀ hx₀Cl hx₀F
      obtain ⟨ε, hε, hballO⟩ := Metric.isOpen_iff.mp hpre_o x₀ (hF_sub hx₀F)
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
      rw [dist_comm a.1 y] at hky; linarith
    have hy₀Not : y₀ ∉ closure (⋃ a ∈ S, 𝓗 a) := by
      have hsub : (⋃ a ∈ S, 𝓗 a) ⊆ f '' closure (⋃ a ∈ S, WX a) := by
        rintro z hz; obtain ⟨a, haS, x, hxCl, rfl⟩ := mem_iUnion₂.mp hz
        exact ⟨x, closure_mono (subset_biUnion_of_mem haS) hxCl, rfl⟩
      intro hy₀Cl
      obtain ⟨x, hxCl, hfx⟩ := closure_minimal hsub (hf_closed _ isClosed_closure) hy₀Cl
      exact Set.disjoint_left.mp hSdisj hxCl hfx
    refine ⟨(⋃ a ∈ S, 𝓗 a)ᶜ, ⟨S, hy₀Not, rfl⟩, fun z hzU => ?_⟩
    by_contra hzNotO
    obtain ⟨x, rfl⟩ := hf_surj z
    have hxNotF : x ∉ F := fun hxF => hzNotO (hF_sub hxF)
    obtain ⟨a, hxa⟩ := mem_iUnion.mp (show (⟨x, hxNotF⟩ : X') ∈ ⋃ a, W a by rw [hWcov]; trivial)
    have hxWX : x ∈ WX a := ⟨⟨x, hxNotF⟩, hxa, rfl⟩
    exact hzU (mem_iUnion₂.mpr ⟨a, ⟨x, hxWX, hzNotO⟩, x, subset_closure hxWX, rfl⟩)
  · intro 𝓖 h𝓖; apply Subset.antisymm
    · intro z hz
      by_cases hz_eq : z = y₀
      · subst hz_eq
        by_cases hGne : 𝓖.Nonempty
        · obtain ⟨U, hUG⟩ := hGne; obtain ⟨S, _, rfl⟩ := h𝓖 hUG
          have hy₀U : z ∈ (⋃ a ∈ S, 𝓗 a)ᶜ := by
            intro hIn; obtain ⟨a, _, ha⟩ := mem_iUnion₂.mp hIn; exact hH_not_y0 a ha
          exact ⟨closure _, ⟨_, hUG, rfl⟩, subset_closure hy₀U⟩
        · rw [Set.not_nonempty_iff_eq_empty.mp hGne, sUnion_empty, closure_empty] at hz; exact hz.elim
      · let 𝓖' : Set (Set Y') := (fun U : Set Y => (Subtype.val : Y' → Y) ⁻¹' U) '' 𝓖
        have hG'_sub : 𝓖' ⊆ { B : Set Y' | ∃ S : Set X', B = (⋃ a ∈ S, 𝓗' a)ᶜ } := by
          rintro _ ⟨U, hUG, rfl⟩; obtain ⟨S, _, rfl⟩ := h𝓖 hUG; refine ⟨S, ?_⟩
          ext q; simp only [mem_preimage, mem_compl_iff, mem_iUnion]; constructor
          · intro h ⟨a, haS, hqH'⟩; exact h ⟨a, haS, by rw [← hH_pre a] at hqH'; exact hqH'⟩
          · intro h ⟨a, haS, hqH⟩; exact h ⟨a, haS, by rw [← hH_pre a]; exact hqH⟩
        have hz' : (⟨z, hz_eq⟩ : Y') ∈ closure (⋃₀ 𝓖') := by
          rw [mem_closure_iff]; intro V hVo hzV
          obtain ⟨q, hqVY, ⟨U, hUG, hqU⟩⟩ := mem_closure_iff.mp hz ((Subtype.val : Y' → Y) '' V)
            (hY'_open.isOpenMap_subtype_val _ hVo) ⟨⟨z, hz_eq⟩, hzV, rfl⟩
          obtain ⟨q', hq'V, rfl⟩ := hqVY
          exact ⟨q', hq'V, ⟨(Subtype.val : Y' → Y) ⁻¹' U, ⟨U, hUG, rfl⟩, hqU⟩⟩
        rw [closurePreserving_compl_sUnion_of_isHCP_frechetUrysohn hFU_Y' hH'_hcp 𝓖' hG'_sub] at hz'
        obtain ⟨_, ⟨_, ⟨U, hUG, rfl⟩, rfl⟩, hzCl⟩ := hz'
        exact ⟨closure U, ⟨U, hUG, rfl⟩, continuous_subtype_val.closure_preimage_subset U hzCl⟩
    · rintro z ⟨_, ⟨U, hUG, rfl⟩, hzU⟩; exact closure_mono (Set.subset_sUnion_of_mem hUG) hzU

/-! ## Part 3: Collectionwise Normality of Closed Metric Images (via Monotone Normality) -/

/-- Closed continuous images of metric spaces are collectionwise normal for closed discrete sets:
any closed discrete subset `D ⊆ Y` admits a discrete open expansion `W : D → Set Y`. -/
private theorem closedMetric_discrete_open_expansion {X Y : Type*} [MetricSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf_cont : Continuous f) (hf_surj : Function.Surjective f) (hf_closed : IsClosedMap f)
    {D : Set Y} (hD_disc : ∀ S : Set Y, S ⊆ D → IsClosed S) :
    ∃ W : D → Set Y,
      (∀ d : D, IsOpen (W d) ∧ d.1 ∈ W d) ∧
      (∀ z : Y, ∃ O : Set Y, IsOpen O ∧ z ∈ O ∧
        ∀ d₁ d₂ : D, (O ∩ W d₁).Nonempty → (O ∩ W d₂).Nonempty → d₁ = d₂) := by
  -- Metric space `X` has a monotone normality operator `HX A B` via `dist`!
  -- Specifically, for disjoint closed `A, B ⊆ X`:
  -- `HX A B := ⋃ n, (G n A \ closure (G n B))` where `G n C := ⋃ x ∈ C, ball x (1/(n+1))`!
  let GX : ℕ → Set X → Set X := fun n C => ⋃ x ∈ C, Metric.ball x (1 / ((n : ℝ) + 1))
  have hGX_open : ∀ n C, IsOpen (GX n C) := fun _ _ => isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hGX_sub : ∀ n C, C ⊆ GX n C := fun n C x hxC =>
    mem_iUnion₂.mpr ⟨x, hxC, Metric.mem_ball.mpr (by rw [dist_self]; positivity)⟩
  have hGX_anti : ∀ {m n} C, m ≤ n → GX n C ⊆ GX m C := fun {m n} C hmn x hx => by
    obtain ⟨y, hyC, hxy⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨y, hyC, Metric.mem_ball.mpr ?_⟩
    have h1 := Metric.mem_ball.mp hxy
    have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn; linarith
    linarith
  have hGX_mono : ∀ n {A B}, A ⊆ B → GX n A ⊆ GX n B := fun _ _ _ hAB => biUnion_subset_biUnion_left hAB
  have hGX_inter : ∀ C : Set X, IsClosed C → ∀ x ∉ C, ∃ n, x ∉ closure (GX n C) := by
    intro C hC x hxC
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hC.isOpen_compl x hxC
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
    refine ⟨n, fun hxCl => ?_⟩
    obtain ⟨q, hqBall, hqG⟩ := mem_closure_iff.mp hxCl (Metric.ball x (ε / 2)) Metric.isOpen_ball
      (Metric.mem_ball.mpr (by rw [dist_self]; linarith))
    obtain ⟨y, hyC, hqy⟩ := mem_iUnion₂.mp hqG
    have h1 : dist q x < ε / 2 := Metric.mem_ball.mp hqBall
    have h2 : dist q y < 1 / ((n : ℝ) + 1) := Metric.mem_ball.mp hqy
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : 1 / ((n : ℝ) + 1) < ε / 2 := by
      rw [div_lt_iff₀ hpos]
      have h2ε : 2 < ε * (n : ℝ) := by have := (div_lt_iff₀ hε).mp hn; linarith
      nlinarith
    have h4 : dist y x < ε := by
      have := dist_triangle y q x; rw [dist_comm y q] at this; linarith
    exact hball (Metric.mem_ball.mpr h4) hyC
  -- Monotone normality operator on `X`:
  let HX : Set X → Set X → Set X := fun A B => ⋃ n, (GX n A \ closure (GX n B))
  have hHX_open : ∀ A B, IsOpen (HX A B) := fun _ _ =>
    isOpen_iUnion fun n => (hGX_open n _).sdiff isClosed_closure
  have hHX_sub : ∀ A B, IsClosed B → Disjoint A B → A ⊆ HX A B := by
    intro A B hB hdisj x hxA
    obtain ⟨n, hn⟩ := hGX_inter B hB x (Set.disjoint_left.mp hdisj hxA)
    exact mem_iUnion.mpr ⟨n, hGX_sub n A hxA, hn⟩
  have hHX_disj : ∀ A₁ A₂ B₁ B₂, A₁ ⊆ B₂ → A₂ ⊆ B₁ → Disjoint (HX A₁ B₁) (HX A₂ B₂) := by
    intro A₁ A₂ B₁ B₂ h12 h21
    rw [Set.disjoint_left]; intro x hx1 hx2
    obtain ⟨m, hm1, hm2⟩ := mem_iUnion.mp hx1
    obtain ⟨n, hn1, hn2⟩ := mem_iUnion.mp hx2
    rcases le_total m n with hmn | hnm
    · exact hm2 (subset_closure (hGX_anti B₁ hmn (hGX_mono n h21 hn1)))
    · exact hn2 (subset_closure (hGX_anti B₂ hnm (hGX_mono m h12 hm1)))
  -- Push monotone normality operator to `Y`: `HY A B := (f '' (HX (f ⁻¹' A) (f ⁻¹' B))ᶜ)ᶜ`.
  let HY : Set Y → Set Y → Set Y := fun A B => (f '' (HX (f ⁻¹' A) (f ⁻¹' B))ᶜ)ᶜ
  have hHY_open : ∀ A B, IsOpen (HY A B) := fun _ _ =>
    (hf_closed _ (hHX_open _ _).isClosed_compl).isOpen_compl
  have hHY_sub : ∀ A B, IsClosed B → Disjoint A B → A ⊆ HY A B := by
    intro A B hB hdisj y hyA
    rintro ⟨x, hxNot, rfl⟩
    exact hxNot (hHX_sub _ _ (hB.preimage hf_cont) (hdisj.preimage f) hyA)
  have hHY_disj : ∀ A₁ A₂ B₁ B₂, A₁ ⊆ B₂ → A₂ ⊆ B₁ → Disjoint (HY A₁ B₁) (HY A₂ B₂) := by
    intro A₁ A₂ B₁ B₂ h12 h21
    rw [Set.disjoint_left]; intro y hy1 hy2
    obtain ⟨x, rfl⟩ := hf_surj y
    have hx1 : x ∈ HX (f ⁻¹' A₁) (f ⁻¹' B₁) := by by_contra h; exact hy1 ⟨x, h, rfl⟩
    have hx2 : x ∈ HX (f ⁻¹' A₂) (f ⁻¹' B₂) := by by_contra h; exact hy2 ⟨x, h, rfl⟩
    exact Set.disjoint_left.mp (hHX_disj _ _ _ _ (preimage_mono h12) (preimage_mono h21)) hx1 hx2
  -- Classic Heath–Lutzer–Zenor discrete open expansion of `D`:
  -- First separate each `d ∈ D` from `D \ {d}` by `U d := HY {d} (D \ {d})`,
  -- then shrink `W d := HY {d} (U d)ᶜ`! Wait: `U d` are pairwise disjoint, so `W d` are DISCRETE!
  have hT1Y : T1Space Y := ⟨fun y => by
    obtain ⟨x, rfl⟩ := hf_surj y
    have hEq : ({f x} : Set Y) = f '' {x} := by simp
    rw [hEq]; exact hf_closed {x} isClosed_singleton⟩
  let U : D → Set Y := fun d => HY {d.1} (D \ {d.1})
  have hU_open : ∀ d : D, IsOpen (U d) := fun _ => hHY_open _ _
  have hU_mem : ∀ d : D, d.1 ∈ U d := fun d =>
    hHY_sub {d.1} (D \ {d.1}) (hD_disc _ Set.sdiff_subset)
      (Set.disjoint_singleton_left.mpr fun h => h.2 rfl) (mem_singleton d.1)
  have hU_disj : ∀ d₁ d₂ : D, d₁ ≠ d₂ → Disjoint (U d₁) (U d₂) := fun d₁ d₂ hne =>
    hHY_disj {d₁.1} {d₂.1} (D \ {d₁.1}) (D \ {d₂.1})
      (Set.singleton_subset_iff.mpr ⟨d₁.2, fun e => hne (Subtype.ext e)⟩)
      (Set.singleton_subset_iff.mpr ⟨d₂.2, fun e => hne (Subtype.ext e.symm)⟩)
  -- For `W d`, use `HY {d.1} (U d)ᶜ` — wait: to make `{W d}` discrete at every `z ∉ D`,
  -- we use `W d := HY {d.1} (U d)ᶜ ∩ HY D ...`? No! Even simpler:
  -- Take `W d := U d ∩ HY {d.1} ((U d)ᶜ)`? No, `z ∉ D` might be in `closure (⋃ d, U d)`!
  -- To make `{W d}` discrete at `z ∉ D`:
  -- Let `V := HY D (∅)`? No! For each `d`, `W d := HY {d.1} (D \ {d.1})` ALREADY satisfies:
  -- For ANY `z ∉ D`, `z` and `D` are disjoint closed sets, so `O_z := HY {z} D` is disjoint from
  -- `HY D {z}` — wait: `W d` must be inside `HY {d} (D \ {d})`, AND for `z ∉ D`, we need `O_z`
  -- to meet at most ONE `W d`!
  -- **Classic Borges / HLZ trick (3 lines!):**
  -- Define `W d := HY {d.1} (D \ {d.1}) \ ...` NO:
  -- Define `W d := HY {d.1} (D \ {d.1})`? No, just use `HY` on `X`:
  -- In `X`, `f ⁻¹' D` is closed, and `{ f ⁻¹' {d.1} : d ∈ D }` is a DISCRETE closed family in `X`!
  -- Wait: IS `{ f ⁻¹' {d.1} : d ∈ D }` discrete in `X`?!
  -- YES!! Because `∀ S ⊆ D, IsClosed S`, so `∀ S ⊆ D, IsClosed (f ⁻¹' S)`!
  -- For any `x ∈ X`: `x` has an open nhd `f ⁻¹' (U d)` (if `f x = d`) or `f ⁻¹' Dᶜ` (if `f x ∉ D`)!
  -- Now in `Y`: for `z ∉ D`, `z ∈ Dᶜ` (open!). Take `O_z := HY {z} D`!
  --Wait: `O_z` is disjoint from `HY D {z}`, NOT from `HY {d} (D \ {d})`!
  -- UNLESS we intersect `W d` with `HY D {z}`? No, `W d` can't depend on `z`!
  -- **HLZ Theorem 2.2 (THE 2-LINE PROOF OF COLLECTIONWISE NORMALITY FROM MONOTONE NORMALITY!!):**
  -- Given pairwise disjoint open `U d ∋ d`, define:
  -- `W d := HY {d.1} (U d)ᶜ` — STILL might accumulate at `z ∉ ⋃ d, U d`?
  -- CHECK!! Suppose `z ∉ ⋃ d, U d`!!
  -- Then for EVERY `d : D`, `z ∈ (U d)ᶜ`, so `{z} ⊆ (U d)ᶜ`, AND `D ⊆ {z}ᶜ` (Wait: `z ∉ D` since `D ⊆ ⋃ d, U d`!)!
  -- Look at `O_z := HY {z} D`!!
  -- Compare `O_z = HY {z} D` with `W d = HY {d.1} (U d)ᶜ`!!
  -- 1. `{z} ⊆ (U d)ᶜ` (since `z ∉ U d`)!!
  -- 2. `{d.1} ⊆ D` (trivial!)!!
  -- THEREFORE BY `hHY_disj`:
  -- **`Disjoint (HY {z} D) (HY {d.1} (U d)ᶜ)` FOR EVERY `d : D` SIMULTANEOUSLY!!**
  -- AND IF `z ∈ U d₀` FOR SOME `d₀ : D`:
  -- Then `U d₀` is an OPEN NEIGHBORHOOD OF `z` THAT MEETS **ONLY `W d₀`** (since `W d ⊆ HY {d.1} (U d)ᶜ ⊆ U d`, wait: `HY {d.1} (U d)ᶜ` is disjoint from `(U d)ᶜ`, so `W d ⊆ U d`, and `{U d}` are PAIRWISE DISJOINT)!!
  -- **OH!! MY!! GOD!! THAT IS LITERALLY THE 5-LINE HLZ COLLECTIONWISE NORMALITY PROOF!!**
  let W : D → Set Y := fun d => HY {d.1} (U d)ᶜ
  have hW_sub_U : ∀ d : D, W d ⊆ U d := fun d y hyW => by
    by_contra hyNot
    have hdisj := hHY_disj {d.1} {y} (U d)ᶜ {d.1}
      Subset.rfl (Set.singleton_subset_iff.mpr hyNot)
    exact Set.disjoint_left.mp hdisj hyW
      (hHY_sub {y} {d.1} isClosed_singleton
        (Set.disjoint_singleton_left.mpr fun e => hyNot (e ▸ hU_mem d)) (mem_singleton y))
  refine ⟨W, fun d => ⟨hHY_open _ _, hHY_sub {d.1} (U d)ᶜ (hU_open d).isClosed_compl
    (Set.disjoint_singleton_left.mpr fun h => h (hU_mem d)) (mem_singleton d.1)⟩, ?_⟩
  intro z
  by_cases hzU : ∃ d₀ : D, z ∈ U d₀
  · obtain ⟨d₀, hzd₀⟩ := hzU
    refine ⟨U d₀, hU_open d₀, hzd₀, fun d₁ d₂ ⟨y₁, hy₁U, hy₁W⟩ ⟨y₂, hy₂U, hy₂W⟩ => ?_⟩
    have h1 : d₁ = d₀ := by
      by_contra hne
      exact Set.disjoint_left.mp (hU_disj d₀ d₁ (Ne.symm hne)) hy₁U (hW_sub_U d₁ hy₁W)
    have h2 : d₂ = d₀ := by
      by_contra hne
      exact Set.disjoint_left.mp (hU_disj d₀ d₂ (Ne.symm hne)) hy₂U (hW_sub_U d₂ hy₂W)
    exact h1.trans h2.symm
  · push Not at hzU
    have hzNotD : z ∉ D := fun hzD => hzU ⟨z, hzD⟩ (hU_mem ⟨z, hzD⟩)
    refine ⟨HY {z} D, hHY_open _ _,
      hHY_sub {z} D (hD_disc D Subset.rfl) (Set.disjoint_singleton_left.mpr hzNotD) (mem_singleton z),
      fun d₁ _ ⟨y₁, hy₁O, hy₁W⟩ _ => ?_⟩
    have hdisj := hHY_disj {z} {d₁.1} D (U d₁)ᶜ
      (Set.singleton_subset_iff.mpr (hzU d₁)) (Set.singleton_subset_iff.mpr d₁.2)
    exact (Set.disjoint_left.mp hdisj hy₁O hy₁W).elim

/-! ## Part 4: Slaughter's Theorem (1973) for Complete Metric Spaces -/

/-- **Slaughter (1973) for Complete Metric Spaces**:
Every closed continuous image `Y` of a complete metric space `X` is an **`M₁`-space**. -/
theorem slaughter_completeMetric_closedMap_isM1 {X Y : Type*} [MetricSpace X] [CompleteSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf_cont : Continuous f) (hf_surj : Function.Surjective f) (hf_closed : IsClosedMap f) :
    MSpace.IsM1 Y := by
  classical
  have hT1Y : T1Space Y := ⟨fun y => by
    obtain ⟨x, rfl⟩ := hf_surj y
    have hEq : ({f x} : Set Y) = f '' {x} := by simp
    rw [hEq]; exact hf_closed {x} isClosed_singleton⟩
  have hT3Y : T3Space Y := by
    have hNorm : NormalSpace Y := ⟨fun A B hA hB hdisj => by
      obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ :=
        normal_separation (hA.preimage hf_cont) (hB.preimage hf_cont) (hdisj.preimage f)
      refine ⟨(f '' Uᶜ)ᶜ, (f '' Vᶜ)ᶜ,
        (hf_closed _ hUo.isClosed_compl).isOpen_compl,
        (hf_closed _ hVo.isClosed_compl).isOpen_compl,
        fun y hyA ⟨x, hxUc, hfx⟩ => hxUc (hAU (by rw [Set.mem_preimage, hfx]; exact hyA)),
        fun y hyB ⟨x, hxVc, hfx⟩ => hxVc (hBV (by rw [Set.mem_preimage, hfx]; exact hyB)), ?_⟩
      rw [Set.disjoint_left]; intro y hy1 hy2
      obtain ⟨x, rfl⟩ := hf_surj y
      have hxU : x ∈ U := by by_contra h; exact hy1 ⟨x, h, rfl⟩
      have hxV : x ∈ V := by by_contra h; exact hy2 ⟨x, h, rfl⟩
      exact Set.disjoint_left.mp hUV hxU hxV⟩
    exact inferInstance
  have hFU_Y : IsFrechetUrysohn Y :=
    isFrechetUrysohn_of_closedMap_from_metricSpace hf_cont hf_surj hf_closed
  -- Step 1: Locally finite refinements `U m` of `1/(2*(m+1))`-balls in `X`.
  have href : ∀ m : ℕ, ∃ U : X → Set X,
      (∀ a, IsOpen (U a)) ∧ (⋃ a, U a) = Set.univ ∧ LocallyFinite U ∧
      (∀ a, U a ⊆ Metric.ball a (1 / (2 * ((m : ℝ) + 1)))) := by
    intro m
    have hcov : (⋃ a : X, Metric.ball a (1 / (2 * ((m : ℝ) + 1)))) = Set.univ := by
      ext a; simp only [mem_iUnion, mem_univ, iff_true]
      exact ⟨a, Metric.mem_ball.mpr (by rw [dist_self]; positivity)⟩
    exact precise_refinement (fun a : X => Metric.ball a (1 / (2 * ((m : ℝ) + 1))))
      (fun _ => Metric.isOpen_ball) hcov
  choose U hUo hUcov hUlf hUref using href
  -- Step 2: Lašnev closed discrete layers `D m` (fibers not finitely covered by `U m`).
  let D : ℕ → Set Y := fun m =>
    { y : Y | ∀ s : Finset X, ¬ (f ⁻¹' {y} ⊆ ⋃ a ∈ s, U m a) }
  have hD_disc : ∀ m (S : Set Y), S ⊆ D m → IsClosed S := by
    intro m S hSD
    rw [← closure_subset_iff_isClosed]; intro z hz; by_contra hzS
    have hne : (closure (f ⁻¹' S) ∩ f ⁻¹' {z}).Nonempty := by
      by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hS_sub : S ⊆ f '' closure (f ⁻¹' S) := fun y hyS => by
        obtain ⟨x, rfl⟩ := hf_surj y; exact ⟨x, subset_closure hyS, rfl⟩
      obtain ⟨x, hxCl, hfx⟩ := closure_minimal hS_sub (hf_closed _ isClosed_closure) hz
      have hx_mem : x ∈ closure (f ⁻¹' S) ∩ f ⁻¹' {z} := ⟨hxCl, hfx⟩
      rw [hemp] at hx_mem; exact hx_mem
    obtain ⟨x₀, hx₀Cl, hfx₀⟩ := hne
    obtain ⟨v, hv_mem, hv_tend⟩ := mem_closure_iff_seq_limit.mp hx₀Cl
    have hu_tend : Tendsto (f ∘ v) atTop (𝓝 z) := by
      have hfx₀' : f x₀ = z := hfx₀; rw [← hfx₀']; exact (hf_cont.tendsto x₀).comp hv_tend
    let Triple := ℕ × X × X
    let State (r : ℕ) := { seq : Fin r → Triple //
      (∀ i, f (v (seq i).1) ∈ S) ∧
      (∀ i j, i < j → (seq i).1 < (seq j).1) ∧
      (∀ i j, i ≠ j → (seq i).2.1 ≠ (seq j).2.1) ∧
      (∀ i, f (seq i).2.2 = f (v (seq i).1)) ∧
      (∀ i, (seq i).2.2 ∈ U m (seq i).2.1) }
    have hnext_ex : ∀ (r : ℕ) (st : State r),
        ∃ st' : State (r + 1), ∀ i : Fin r, st'.1 i.castSucc = st.1 i := by
      intro r st
      let maxK : ℕ := if hr : 0 < r then (st.1 ⟨r - 1, by omega⟩).1 + 1 else 0
      let TY : Set Y := Set.range (fun i : Fin r => f (v (st.1 i).1))
      have hz_not_TY : z ∉ TY := by rintro ⟨i, hi⟩; exact hzS (hi ▸ st.2.1 i)
      obtain ⟨N, _⟩ := Filter.eventually_atTop.mp
        (hu_tend.eventually ((Set.finite_range _).isClosed.isOpen_compl.mem_nhds hz_not_TY))
      let k := max maxK N
      let sA : Finset X := Finset.univ.image (fun i : Fin r => (st.1 i).2.1)
      obtain ⟨p, hpF, hpNot⟩ := Set.not_subset.mp (hSD (hv_mem k) sA)
      obtain ⟨a, hpa⟩ := mem_iUnion.mp (show p ∈ ⋃ a, U m a by rw [hUcov m]; trivial)
      have ha_ne : ∀ i : Fin r, a ≠ (st.1 i).2.1 := fun i heq =>
        hpNot (mem_iUnion₂.mpr ⟨a, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩, hpa⟩)
      have hk_gt : ∀ i : Fin r, (st.1 i).1 < k := fun i => by
        have hr : 0 < r := Nat.pos_of_ne_zero (by intro h; subst h; exact Fin.elim0 i)
        have hle_last : (st.1 i).1 ≤ (st.1 ⟨r - 1, by omega⟩).1 := by
          rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt i.2) with heq | hlt
          · have : i = ⟨r - 1, by omega⟩ := Fin.ext heq; rw [this]
          · exact (st.2.2.1 i ⟨r - 1, by omega⟩ hlt).le
        have hmaxK : maxK = (st.1 ⟨r - 1, by omega⟩).1 + 1 := by simp only [maxK, dite_eq_left hr]
        have : maxK ≤ k := le_max_left _ _; omega
      refine ⟨⟨Fin.snoc st.1 (k, a, p), ?_, ?_, ?_, ?_, ?_⟩, fun i => by simp only [Fin.snoc_castSucc]⟩
      · intro i; refine Fin.lastCases ?_ ?_ i
        · simp only [Fin.snoc_last]; exact hv_mem k
        · intro j; simp only [Fin.snoc_castSucc]; exact st.2.1 j
      · intro i j; refine Fin.lastCases ?_ (fun j' => ?_) j
        · refine Fin.lastCases (fun h => (lt_irrefl _ h).elim) (fun i' _ => ?_) i
          simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact hk_gt i'
        · refine Fin.lastCases (fun h => (Nat.not_lt.mpr (Nat.le_of_lt j'.2) h).elim) (fun i' h => ?_) i
          simp only [Fin.snoc_castSucc]; exact st.2.2.1 i' j' h
      · intro i j; refine Fin.lastCases ?_ (fun j' => ?_) j
        · refine Fin.lastCases (fun h => (h rfl).elim) (fun i' _ => ?_) i
          simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact (ha_ne i').symm
        · refine Fin.lastCases (fun _ => ?_) (fun i' h => ?_) i
          · simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact ha_ne j'
          · simp only [Fin.snoc_castSucc]; exact st.2.2.2.1 i' j' (fun e => h (congrArg Fin.castSucc e))
      · intro i; refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last]; exact hpF
        · simp only [Fin.snoc_castSucc]; exact st.2.2.2.2.1 j
      · intro i; refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last]; exact hpa
        · simp only [Fin.snoc_castSucc]; exact st.2.2.2.2.2 j
    let stSeq : (r : ℕ) → State r := fun r =>
      Nat.rec ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, fun i => i.elim0⟩ (fun k stk => (hnext_ex k stk).choose) r
    have hst_le : ∀ {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) (i : Fin r₁),
        (stSeq r₂).1 ⟨i.1, lt_of_lt_of_le i.2 h⟩ = (stSeq r₁).1 i := by
      intro r₁ r₂ h i; induction h with
      | refl => rfl
      | @step k hmk ih => rw [← ih]; exact (hnext_ex k (stSeq k)).choose_spec ⟨i.1, lt_of_lt_of_le i.2 hmk⟩
    let idx : ℕ → ℕ := fun r => ((stSeq (r + 1)).1 ⟨r, Nat.lt_succ_self r⟩).1
    let aSeq : ℕ → X := fun r => ((stSeq (r + 1)).1 ⟨r, Nat.lt_succ_self r⟩).2.1
    let pSeq : ℕ → X := fun r => ((stSeq (r + 1)).1 ⟨r, Nat.lt_succ_self r⟩).2.2
    have hidx_strict : StrictMono idx := fun i j hij => by
      have h1 := hst_le (r₁ := i + 1) (r₂ := j + 1) (by omega) ⟨i, Nat.lt_succ_self i⟩
      have h2 := (stSeq (j + 1)).2.2.1 ⟨i, by omega⟩ ⟨j, Nat.lt_succ_self j⟩ hij
      simpa only [idx, h1] using h2
    have ha_inj : Function.Injective aSeq := fun i j hij => by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 := hst_le (r₁ := i + 1) (r₂ := j + 1) (by omega) ⟨i, Nat.lt_succ_self i⟩
        have h2 := (stSeq (j + 1)).2.2.2.1 ⟨i, by omega⟩ ⟨j, Nat.lt_succ_self j⟩
          (by intro e; exact hne (congrArg Fin.val e))
        exact h2 (by simpa only [aSeq, h1] using hij)
      · have h1 := hst_le (r₁ := j + 1) (r₂ := i + 1) (by omega) ⟨j, Nat.lt_succ_self j⟩
        have h2 := (stSeq (i + 1)).2.2.2.1 ⟨j, by omega⟩ ⟨i, Nat.lt_succ_self i⟩
          (by intro e; exact hne (congrArg Fin.val e).symm)
        exact h2 (by simpa only [aSeq, h1] using hij.symm)
    have hp_fib : ∀ r, f (pSeq r) = f (v (idx r)) := fun r =>
      (stSeq (r + 1)).2.2.2.2.1 ⟨r, Nat.lt_succ_self r⟩
    have hp_U : ∀ r, pSeq r ∈ U m (aSeq r) := fun r =>
      (stSeq (r + 1)).2.2.2.2.2 ⟨r, Nat.lt_succ_self r⟩
    have hP_cl : IsClosed (Set.range pSeq) := by
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]; intro x hx
      obtain ⟨t, ht_nhds, ht_fin⟩ := hUlf m x
      obtain ⟨O, hOt, hOo, hxO⟩ := mem_nhds_iff.mp ht_nhds
      let E : Set ℕ := { r | pSeq r ∈ O }
      have hE_fin : E.Finite := by
        have hsub : aSeq '' E ⊆ { a | (U m a ∩ t).Nonempty } := by
          rintro _ ⟨r, hrO, rfl⟩; exact ⟨pSeq r, hp_U r, hOt hrO⟩
        exact (ht_fin.subset hsub).of_finite_image (fun i _ j _ h => ha_inj h)
      refine Filter.mem_of_superset ((hOo.sdiff (hE_fin.image pSeq).isClosed).mem_nhds
        ⟨hxO, by rintro ⟨r, _, rfl⟩; exact hx ⟨r, rfl⟩⟩) ?_
      rintro q ⟨hqO, hqNot⟩ ⟨r, rfl⟩; exact hqNot ⟨r, hqO, rfl⟩
    have hz_im : z ∈ f '' Set.range pSeq :=
      (hf_closed _ hP_cl).mem_of_tendsto (hu_tend.comp hidx_strict.tendsto_atTop)
        (Eventually.of_forall fun r => ⟨pSeq r, ⟨r, rfl⟩, hp_fib r⟩)
    obtain ⟨_, ⟨r, rfl⟩, hfm⟩ := hz_im
    rw [hp_fib r] at hfm; exact hzS (hfm ▸ hv_mem (idx r))
  -- Step 3: HCP-complement CP open families `𝓑 m` giving a local base at every `y ∉ ⋃ m, D m`.
  let 𝓗 : ℕ → X → Set Y := fun m a => f '' closure (U m a)
  have hH_hcp : ∀ m, IsHCP (𝓗 m) := fun m =>
    isHCP_image_of_locallyFinite_isClosedMap hf_cont hf_closed (hUlf m).closure
  let 𝓑 : ℕ → Set (Set Y) := fun m => { B : Set Y | ∃ S : Set X, B = (⋃ a ∈ S, 𝓗 m a)ᶜ }
  have hB_open : ∀ m, ∀ B ∈ 𝓑 m, IsOpen B := by
    rintro m B ⟨S, rfl⟩
    let T : X → Set Y := fun a => if a ∈ S then 𝓗 m a else ∅
    have hT_eq : (⋃ a, T a) = ⋃ a ∈ S, 𝓗 m a := by
      ext q; simp only [mem_iUnion, T]; constructor
      · rintro ⟨a, ha⟩; by_cases haS : a ∈ S
        · simp only [ite_eq_left haS] at ha; exact ⟨a, haS, ha⟩
        · simp only [ite_eq_right haS] at ha; exact ha.elim
      · rintro ⟨a, haS, ha⟩; exact ⟨a, by simp only [ite_eq_left haS]; exact ha⟩
    have hT_cl : ∀ a, closure (T a) = T a := fun a => by
      by_cases haS : a ∈ S
      · simp only [T, ite_eq_left haS]; exact (hf_closed _ isClosed_closure).closure_eq
      · simp only [T, ite_eq_right haS, closure_empty]
    have hcl : IsClosed (⋃ a ∈ S, 𝓗 m a) := by
      rw [← closure_eq_iff_isClosed, ← hT_eq, hH_hcp m T (fun a => by by_cases h : a ∈ S <;> simp [T, h])]
      ext q; simp only [mem_iUnion, hT_cl]
    exact hcl.isOpen_compl
  have hB_cp : ∀ m, MSpace.ClosurePreserving (𝓑 m) := fun m =>
    closurePreserving_compl_sUnion_of_isHCP_frechetUrysohn hFU_Y (hH_hcp m)
  -- Step 4: Discrete-expansion CP open families `𝓒 m` giving a local base at every `y ∈ D m`.
  choose Wexp hWexp_open hWexp_disc using fun m =>
    closedMetric_discrete_open_expansion hf_cont hf_surj hf_closed (hD_disc m)
  choose 𝓤 hU_open hU_base hU_cp using fun y : Y =>
    lasnev_point_hasCPOuterBase hf_cont hf_surj hf_closed y
  let 𝓒 : ℕ → Set (Set Y) := fun m =>
    { B : Set Y | ∃ d : D m, B ∈ 𝓤 d.1 ∧ B ⊆ Wexp m d }
  have hC_open : ∀ m, ∀ B ∈ 𝓒 m, IsOpen B := by
    rintro m B ⟨d, hBU, _⟩
    exact (hU_open d.1 B hBU).1
  have hC_cp : ∀ m, MSpace.ClosurePreserving (𝓒 m) := by
    intro m 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      obtain ⟨O, hOo, hzO, hOuniq⟩ := hWexp_disc m z
      obtain ⟨y₀, hy₀O, ⟨B₀, hB₀G, hy₀B₀⟩⟩ := mem_closure_iff.mp hz O hOo hzO
      obtain ⟨d₀, _, hB₀W⟩ := h𝓖 hB₀G
      have hOd₀ : (O ∩ Wexp m d₀).Nonempty := ⟨y₀, hy₀O, hB₀W hy₀B₀⟩
      let 𝓖₀ : Set (Set Y) := { B ∈ 𝓖 | B ∈ 𝓤 d₀.1 ∧ B ⊆ Wexp m d₀ }
      have hz_cl0 : z ∈ closure (⋃₀ 𝓖₀) := by
        rw [mem_closure_iff]; intro W hWo hzW
        obtain ⟨q, hqOW, ⟨B, hBG, hqB⟩⟩ :=
          mem_closure_iff.mp hz (O ∩ W) (hOo.inter hWo) ⟨hzO, hzW⟩
        obtain ⟨d, hBU, hBW⟩ := h𝓖 hBG
        have hd_eq : d = d₀ := hOuniq d d₀ ⟨q, hqOW.1, hBW hqB⟩ hOd₀
        subst hd_eq
        exact ⟨q, hqOW.2, ⟨B, ⟨hBG, hBU, hBW⟩, hqB⟩⟩
      rw [hU_cp d₀.1 𝓖₀ (fun _ h => h.2.1)] at hz_cl0
      obtain ⟨_, ⟨B, hBG₀, rfl⟩, hzB⟩ := hz_cl0
      exact ⟨closure B, ⟨B, hBG₀.1, rfl⟩, hzB⟩
    · rintro z ⟨_, ⟨B, hBG, rfl⟩, hzB⟩
      exact closure_mono (Set.subset_sUnion_of_mem hBG) hzB
  -- Step 5: Interleave `𝓑` and `𝓒` into a σ-CP open base of `Y`!
  let 𝓛 : ℕ → Set (Set Y) := fun n => if n % 2 = 0 then 𝓑 (n / 2) else 𝓒 (n / 2)
  have hL_cp : ∀ n, MSpace.ClosurePreserving (𝓛 n) := fun n => by
    by_cases h : n % 2 = 0
    · simp only [𝓛, ite_eq_left h]; exact hB_cp (n / 2)
    · simp only [𝓛, ite_eq_right h]; exact hC_cp (n / 2)
  refine ⟨hT3Y, ⋃ n, 𝓛 n, ?_, ⟨𝓛, hL_cp, rfl⟩⟩
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro B hB
    obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
    by_cases h : n % 2 = 0
    · simp only [𝓛, ite_eq_left h] at hBn; exact hB_open (n / 2) B hBn
    · simp only [𝓛, ite_eq_right h] at hBn; exact hC_open (n / 2) B hBn
  · intro y W hyW hWo
    by_cases hyD : ∃ m, y ∈ D m
    · obtain ⟨m, hym⟩ := hyD
      obtain ⟨V, hVU, hVW⟩ := hU_base y (W ∩ Wexp m ⟨y, hym⟩)
        (hWo.inter (hWexp_open m ⟨y, hym⟩).1) ⟨hyW, (hWexp_open m ⟨y, hym⟩).2⟩
      refine ⟨V, ?_, (hU_open y V hVU).2, hVW.trans inter_subset_left⟩
      refine mem_iUnion.mpr ⟨2 * m + 1, ?_⟩
      have hodd : ¬ (2 * m + 1) % 2 = 0 := by omega
      have hdiv : (2 * m + 1) / 2 = m := by omega
      simp only [𝓛, ite_eq_right hodd, hdiv]
      exact ⟨⟨y, hym⟩, hVU, hVW.trans inter_subset_right⟩
    · -- `y ∉ ⋃ m, D m`: `f ⁻¹' {y}` is compact in complete `X`!
      have hy_cov : ∀ m, ∃ s : Finset X, f ⁻¹' {y} ⊆ ⋃ a ∈ s, U m a := by
        intro m; by_contra h; push Not at h; exact hyD ⟨m, h⟩
      have htb : TotallyBounded (f ⁻¹' {y}) := by
        rw [Metric.totallyBounded_iff]; intro ε hε
        obtain ⟨m, hm⟩ := exists_nat_gt (1 / (2 * ε))
        obtain ⟨s, hs⟩ := hy_cov m
        refine ⟨(s : Set X), s.finite_toSet, fun p hp => ?_⟩
        obtain ⟨a, has, hpa⟩ := mem_iUnion₂.mp (hs hp)
        refine mem_iUnion₂.mpr ⟨a, has, Metric.mem_ball.mpr ?_⟩
        have hdist : dist p a < 1 / (2 * ((m : ℝ) + 1)) := Metric.mem_ball.mp (hUref m a hpa)
        have hpos : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
        have hlt : 1 / (2 * ((m : ℝ) + 1)) < ε := by
          rw [div_lt_iff₀ hpos]
          have h1 : 1 < 2 * ε * (m : ℝ) := by
            have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ε)).mp hm; linarith
          nlinarith
        exact lt_trans hdist hlt
      have hcomp : IsCompact (f ⁻¹' {y}) :=
        isCompact_iff_totallyBounded_isComplete.mpr
          ⟨htb, (isClosed_singleton.preimage hf_cont).isComplete⟩
      have hpre_o : IsOpen (f ⁻¹' W) := hWo.preimage hf_cont
      have hrad : ∀ p : f ⁻¹' {y}, ∃ ε : ℝ, 0 < ε ∧ Metric.ball p.1 ε ⊆ f ⁻¹' W := fun p =>
        Metric.isOpen_iff.mp hpre_o p.1 (by change f p.1 ∈ W; have hp : f p.1 = y := p.2; rw [hp]; exact hyW)
      choose ε hε_pos hε_sub using hrad
      obtain ⟨s, hs⟩ := hcomp.elim_finite_subcover
        (fun p : f ⁻¹' {y} => Metric.ball p.1 (ε p / 2))
        (fun _ => Metric.isOpen_ball)
        (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, Metric.mem_ball.mpr (by rw [dist_self]; linarith [hε_pos ⟨p, hp⟩])⟩)
      have hex_m : ∃ m : ℕ, ∀ p ∈ s, 1 / ((m : ℝ) + 1) < ε p / 2 := by
        by_cases hsne : s.Nonempty
        · let δ : ℝ := s.inf' hsne (fun p => ε p / 2)
          have hδ_pos : 0 < δ := by rw [Finset.lt_inf'_iff]; intro p _; linarith [hε_pos p]
          obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
          refine ⟨m, fun p hp => ?_⟩
          have hδ_le : δ ≤ ε p / 2 := Finset.inf'_le (fun p => ε p / 2) hp
          have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
          have h1 : 1 / ((m : ℝ) + 1) < δ := by
            rw [div_lt_iff₀ hpos]
            have h1δ : 1 < δ * (m : ℝ) := by have := (div_lt_iff₀ hδ_pos).mp hm; linarith
            nlinarith
          linarith
        · exact ⟨0, fun p hp => (hsne ⟨p, hp⟩).elim⟩
      obtain ⟨m, hm⟩ := hex_m
      let S : Set X := { a : X | y ∉ 𝓗 m a }
      refine ⟨(⋃ a ∈ S, 𝓗 m a)ᶜ, ?_, ?_, ?_⟩
      · refine mem_iUnion.mpr ⟨2 * m, ?_⟩
        have heven : (2 * m) % 2 = 0 := by omega
        have hdiv : (2 * m) / 2 = m := by omega
        simp only [𝓛, ite_eq_left heven, hdiv]
        exact ⟨S, rfl⟩
      · intro hyIn; obtain ⟨a, haS, hya⟩ := mem_iUnion₂.mp hyIn; exact haS hya
      · intro w hwB
        obtain ⟨q, rfl⟩ := hf_surj w
        obtain ⟨a, hqa⟩ := mem_iUnion.mp (show q ∈ ⋃ a, U m a by rw [hUcov m]; trivial)
        have hya : y ∈ 𝓗 m a := by
          by_contra hyNot
          exact hwB (mem_iUnion₂.mpr ⟨a, hyNot, q, subset_closure hqa, rfl⟩)
        obtain ⟨p, hpCl, hfp⟩ := hya
        obtain ⟨r, hrs, hpr⟩ := mem_iUnion₂.mp (hs hfp)
        have hcl_sub : closure (U m a) ⊆ Metric.closedBall a (1 / (2 * ((m : ℝ) + 1))) :=
          closure_minimal ((hUref m a).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
        have hpa : dist p a ≤ 1 / (2 * ((m : ℝ) + 1)) := Metric.mem_closedBall.mp (hcl_sub hpCl)
        have hqa' : dist q a ≤ 1 / (2 * ((m : ℝ) + 1)) := Metric.mem_closedBall.mp (hcl_sub (subset_closure hqa))
        have hqp : dist q p ≤ 1 / ((m : ℝ) + 1) := by
          have h1 : dist q p ≤ dist q a + dist a p := dist_triangle q a p
          rw [dist_comm a p] at h1
          have h2 : 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * ((m : ℝ) + 1)) = 1 / ((m : ℝ) + 1) := by
            field_simp; ring
          linarith
        have hqr : dist q r.1 < ε r := by
          have h1 : dist q r.1 ≤ dist q p + dist p r.1 := dist_triangle q p r.1
          have h2 : dist p r.1 < ε r / 2 := Metric.mem_ball.mp hpr
          linarith [hm r hrs]
        exact hε_sub r (Metric.mem_ball.mpr hqr)

end Research.SlaughterCompleteMetricM1
