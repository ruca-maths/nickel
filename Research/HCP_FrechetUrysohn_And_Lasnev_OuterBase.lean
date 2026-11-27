import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Indexed
import Targets.Defs
import Defs.D_0001

/-!
# HCP-Complement Closure-Preservation Theorem & CP Open Outer Bases in Every Lašnev Space

We prove:
1. `IsHCP`: a family `𝓗 : ι → Set Y` is **hereditarily closure-preserving (HCP)** if for every
   choice of subsets `S : ι → Set Y` with `∀ i, S i ⊆ 𝓗 i`, `closure (⋃ i, S i) = ⋃ i, closure (S i)`.
2. `isHCP_image_of_locallyFinite_isClosedMap`: the image under any closed continuous map `f : X → Y`
   of any locally finite family in `X` is HCP in `Y`.
3. `closurePreserving_compl_sUnion_of_isHCP_frechetUrysohn` (**HCP-Complement CP Theorem**):
   in any `T₁` Fréchet–Urysohn space `Y`, for any HCP family `𝓗 : ι → Set Y`, the family of
   complements `{ (⋃ i ∈ S, 𝓗 i)ᶜ | S : Set ι }` is **closure-preserving**.
4. `lasnev_every_point_hasCPOuterBase`:
   **every point `y` of every Lašnev space `Y` (closed continuous image of ANY metric space `X`,
   complete or not)** has a closure-preserving open outer base `Defs.D_0001.HasCPOuterBase y`!
   In particular, no Lašnev space can witness `Specs.L_0020` / `Specs.L_0030` / `Specs.L_0031`.
-/

namespace Research.HCPLasnev

open Set Topology Filter

/-- A family `𝓗 : ι → Set Y` is **hereditarily closure-preserving (HCP)** if every
selection `S i ⊆ 𝓗 i` satisfies `closure (⋃ i, S i) = ⋃ i, closure (S i)`. -/
def IsHCP {Y ι : Type*} [TopologicalSpace Y] (𝓗 : ι → Set Y) : Prop :=
  ∀ S : ι → Set Y, (∀ i, S i ⊆ 𝓗 i) → closure (⋃ i, S i) = ⋃ i, closure (S i)

/-- A space `Y` is **Fréchet–Urysohn** if every closure point is the limit of a sequence. -/
def IsFrechetUrysohn (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ S : Set Y, ∀ z ∈ closure S, ∃ u : ℕ → Y, (∀ k, u k ∈ S) ∧ Tendsto u atTop (𝓝 z)

/-- The image of a locally finite family under a closed continuous map is HCP. -/
theorem isHCP_image_of_locallyFinite_isClosedMap {X Y ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf_cont : Continuous f) (hf_closed : IsClosedMap f)
    {F : ι → Set X} (hFlf : LocallyFinite F) :
    IsHCP (fun i => f '' F i) := by
  intro S hS
  apply Subset.antisymm
  · let T : ι → Set X := fun i => f ⁻¹' S i ∩ F i
    have hT_sub : ∀ i, T i ⊆ F i := fun _ => inter_subset_right
    have hT_lf : LocallyFinite T := hFlf.subset hT_sub
    have hT_cl_closed : IsClosed (⋃ i, closure (T i)) := by
      rw [← hT_lf.closure_iUnion]
      exact isClosed_closure
    have hfT_closed : IsClosed (f '' ⋃ i, closure (T i)) := hf_closed _ hT_cl_closed
    have hS_sub_im : (⋃ i, S i) ⊆ f '' ⋃ i, closure (T i) := by
      rintro y hy
      obtain ⟨i, hySi⟩ := mem_iUnion.mp hy
      obtain ⟨x, hxFi, rfl⟩ := hS i hySi
      exact ⟨x, mem_iUnion.mpr ⟨i, subset_closure ⟨hySi, hxFi⟩⟩, rfl⟩
    have hcl_sub : closure (⋃ i, S i) ⊆ f '' ⋃ i, closure (T i) :=
      closure_minimal hS_sub_im hfT_closed
    intro y hy
    obtain ⟨x, hxU, rfl⟩ := hcl_sub hy
    obtain ⟨i, hxCl⟩ := mem_iUnion.mp hxU
    have hfx_cl : f x ∈ closure (f '' T i) :=
      image_closure_subset_closure_image hf_cont ⟨x, hxCl, rfl⟩
    have hfTi_sub : f '' T i ⊆ S i := by
      rintro _ ⟨q, ⟨hqS, _⟩, rfl⟩; exact hqS
    exact mem_iUnion.mpr ⟨i, closure_mono hfTi_sub hfx_cl⟩
  · intro y hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    exact closure_mono (subset_iUnion S i) hyi

/-- Every closed continuous image of a metric space is Fréchet–Urysohn. -/
theorem isFrechetUrysohn_of_closedMap_from_metricSpace {X Y : Type*} [MetricSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf_cont : Continuous f) (hf_surj : Function.Surjective f) (hf_closed : IsClosedMap f) :
    IsFrechetUrysohn Y := by
  intro S z hz
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
  obtain ⟨x, hxCl, hfx⟩ := hne
  obtain ⟨v, hv_mem, hv_tend⟩ := mem_closure_iff_seq_limit.mp hxCl
  refine ⟨f ∘ v, fun k => hv_mem k, ?_⟩
  have hfx' : f x = z := hfx
  rw [← hfx']
  exact (hf_cont.tendsto x).comp hv_tend

/-- Every subspace of a Fréchet–Urysohn space is Fréchet–Urysohn. -/
theorem isFrechetUrysohn_subtype {Y : Type*} [TopologicalSpace Y]
    (hFU : IsFrechetUrysohn Y) (U : Set Y) :
    IsFrechetUrysohn U := by
  intro S z hz
  have hz_clY : z.1 ∈ closure ((Subtype.val : U → Y) '' S) := by
    rw [mem_closure_iff]
    intro V hVo hzV
    obtain ⟨y, hyV, hyS⟩ :=
      mem_closure_iff.mp hz ((Subtype.val : U → Y) ⁻¹' V) (hVo.preimage continuous_subtype_val) hzV
    exact ⟨y.1, hyV, ⟨y, hyS, rfl⟩⟩
  obtain ⟨u, huS, hu_tend⟩ := hFU _ z.1 hz_clY
  have huU : ∀ k, u k ∈ U := fun k => by
    obtain ⟨y, _, hy⟩ := huS k
    exact hy ▸ y.2
  refine ⟨fun k => ⟨u k, huU k⟩, ?_, ?_⟩
  · intro k
    obtain ⟨y, hyS, hy⟩ := huS k
    have heq : (⟨u k, huU k⟩ : U) = y := Subtype.ext hy.symm
    change (⟨u k, huU k⟩ : U) ∈ S
    rw [heq]; exact hyS
  · exact tendsto_subtype_rng.mpr hu_tend

/-- Helper: in a `T₁` space with an HCP family `𝓗 : ι → Set Y`, a sequence `w : ℕ → Y`
converging to `z` with `∀ k, w k ≠ z` cannot hit infinitely many distinct `𝓗 i`! -/
private theorem hcp_no_infinite_distinct_hits {Y ι : Type*} [TopologicalSpace Y] [T1Space Y]
    {𝓗 : ι → Set Y} (hHCP : IsHCP 𝓗)
    {w : ℕ → Y} {z : Y} (hw_ne : ∀ k, w k ≠ z) (hw_tend : Tendsto w atTop (𝓝 z))
    {idx : ℕ → ι} (hidx_inj : Function.Injective idx) (hw_hit : ∀ k, w k ∈ 𝓗 (idx k)) :
    False := by
  classical
  let S : ι → Set Y := fun i => { y | ∃ k, idx k = i ∧ y = w k }
  have hS_sub : ∀ i, S i ⊆ 𝓗 i := by
    rintro i _ ⟨k, rfl, rfl⟩; exact hw_hit k
  have hS_cl : ∀ i, closure (S i) = S i := by
    intro i
    have hfin : (S i).Finite := by
      have hsub : S i ⊆ (fun k => w k) '' { k | idx k = i } := by
        rintro _ ⟨k, rfl, rfl⟩; exact ⟨k, rfl, rfl⟩
      have hsub2 : { k | idx k = i }.Subsingleton := fun a ha b hb => hidx_inj (ha.trans hb.symm)
      exact (hsub2.finite.image _).subset hsub
    exact hfin.isClosed.closure_eq
  have hU_eq : (⋃ i, S i) = Set.range w := by
    ext y; simp only [mem_iUnion, mem_range, S]
    exact ⟨fun ⟨_, k, _, hy⟩ => ⟨k, hy.symm⟩, fun ⟨k, hk⟩ => ⟨idx k, k, rfl, hk.symm⟩⟩
  have hcl_eq : closure (Set.range w) = Set.range w := by
    rw [← hU_eq, hHCP S hS_sub]
    ext y; simp only [mem_iUnion, hS_cl]
  have hz_cl : z ∈ closure (Set.range w) :=
    mem_closure_of_tendsto hw_tend (Eventually.of_forall fun k => ⟨k, rfl⟩)
  rw [hcl_eq] at hz_cl
  obtain ⟨k, hk⟩ := hz_cl
  exact hw_ne k hk

/-- Helper: given a finite set `E : Finset ι` and a sequence `w : ℕ → Y`, there is a
strictly increasing `φ : ℕ → ℕ` that decides membership in every `𝓗 i` (`i ∈ E`). -/
private theorem exists_subseq_deciding_finset {Y ι : Type*} (𝓗 : ι → Set Y) (w : ℕ → Y)
    (E : Finset ι) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i ∈ E, (∀ m, w (φ m) ∈ 𝓗 i) ∨ (∀ m, w (φ m) ∉ 𝓗 i) := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    exact ⟨id, strictMono_id, fun _ h => (Finset.notMem_empty _ h).elim⟩
  | @insert a E ha ih =>
    obtain ⟨φ, hφ_strict, hφ_dec⟩ := ih
    by_cases hinf : ∀ N : ℕ, ∃ m ≥ N, w (φ m) ∈ 𝓗 a
    · let ψ : ℕ → ℕ := Nat.rec (hinf 0).choose (fun _ k => (hinf (k + 1)).choose)
      have hψ_strict : StrictMono ψ := strictMono_nat_of_lt_succ fun k => by
        have := (hinf (ψ k + 1)).choose_spec.1
        change ψ k < (hinf (ψ k + 1)).choose
        omega
      refine ⟨φ ∘ ψ, hφ_strict.comp hψ_strict, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hiE
      · refine Or.inl fun m => ?_
        cases m with
        | zero => exact (hinf 0).choose_spec.2
        | succ k => exact (hinf (ψ k + 1)).choose_spec.2
      · rcases hφ_dec i hiE with h1 | h2
        · exact Or.inl fun m => h1 (ψ m)
        · exact Or.inr fun m => h2 (ψ m)
    · push Not at hinf
      obtain ⟨N, hN⟩ := hinf
      let ψ : ℕ → ℕ := fun m => m + N
      have hψ_strict : StrictMono ψ := fun _ _ h => Nat.add_lt_add_right h N
      refine ⟨φ ∘ ψ, hφ_strict.comp hψ_strict, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hiE
      · exact Or.inr fun m => hN (m + N) (Nat.le_add_left N m)
      · rcases hφ_dec i hiE with h1 | h2
        · exact Or.inl fun m => h1 (ψ m)
        · exact Or.inr fun m => h2 (ψ m)

/-- **HCP-Complement Closure-Preservation Theorem**:
In any `T₁` Fréchet–Urysohn space `Y`, for any HCP family `𝓗 : ι → Set Y`, the family
`𝓑 := { (⋃ i ∈ S, 𝓗 i)ᶜ | S : Set ι }` is **closure-preserving**. -/
theorem closurePreserving_compl_sUnion_of_isHCP_frechetUrysohn {Y ι : Type*}
    [TopologicalSpace Y] [T1Space Y] (hFU : IsFrechetUrysohn Y)
    {𝓗 : ι → Set Y} (hHCP : IsHCP 𝓗) :
    MSpace.ClosurePreserving { B : Set Y | ∃ S : Set ι, B = (⋃ i ∈ S, 𝓗 i)ᶜ } := by
  classical
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · intro z hz
    by_contra hz_not
    -- Fréchet–Urysohn: pick `w : ℕ → Y` in `⋃₀ 𝓖` converging to `z`.
    obtain ⟨w, hw_mem, hw_tend⟩ := hFU (⋃₀ 𝓖) z hz
    have hw_ne : ∀ k, w k ≠ z := fun k heq => by
      obtain ⟨B, hBG, hwkB⟩ := hw_mem k
      exact hz_not ⟨closure B, ⟨B, hBG, rfl⟩, subset_closure (heq ▸ hwkB)⟩
    -- For each `k`, pick `S k : Set ι` with `(⋃ i ∈ S k, 𝓗 i)ᶜ ∈ 𝓖` and `w k ∈ (⋃ i ∈ S k, 𝓗 i)ᶜ`.
    have hSk_ex : ∀ k, ∃ S : Set ι, (⋃ i ∈ S, 𝓗 i)ᶜ ∈ 𝓖 ∧ w k ∈ (⋃ i ∈ S, 𝓗 i)ᶜ := by
      intro k
      obtain ⟨B, hBG, hwkB⟩ := hw_mem k
      obtain ⟨S, rfl⟩ := h𝓖 hBG
      exact ⟨S, hBG, hwkB⟩
    choose S hSG hwkS using hSk_ex
    -- The set `E := { i : ι | { k | w k ∈ 𝓗 i }.Infinite }` must be FINITE by HCP!
    let E : Set ι := { i : ι | { k : ℕ | w k ∈ 𝓗 i }.Infinite }
    have hE_fin : E.Finite := by
      by_contra hE_inf
      -- Build pairwise distinct `idx m ∈ E` and `k m` with `w (k m) ∈ 𝓗 (idx m)` and `k` strictly increasing.
      let State (m : ℕ) := { seq : Fin m → ℕ × ι //
        (∀ a b, a < b → (seq a).1 < (seq b).1) ∧
        (∀ a b, a ≠ b → (seq a).2 ≠ (seq b).2) ∧
        (∀ a, w (seq a).1 ∈ 𝓗 (seq a).2) }
      have hnext_ex : ∀ (m : ℕ) (st : State m),
          ∃ st' : State (m + 1), ∀ a : Fin m, st'.1 a.castSucc = st.1 a := by
        intro m st
        let used : Set ι := Set.range (fun a : Fin m => (st.1 a).2)
        have hnot_sub : ¬ E ⊆ used := fun hsub => hE_inf ((Set.finite_range _).subset hsub)
        obtain ⟨i, hiE, hiNot⟩ := Set.not_subset.mp hnot_sub
        let maxK : ℕ := if hm : 0 < m then (st.1 ⟨m - 1, by omega⟩).1 + 1 else 0
        have hk_ex : ∃ k ≥ maxK, w k ∈ 𝓗 i := by
          by_contra hnone
          push Not at hnone
          apply hiE
          have hsub : { k : ℕ | w k ∈ 𝓗 i } ⊆ (Finset.range maxK : Set ℕ) := by
            intro k hk
            by_contra hkNot
            rw [Finset.mem_coe, Finset.mem_range] at hkNot
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
            simp only [Fin.snoc_last, Fin.snoc_castSucc]
            intro heq; exact hiNot ⟨a', heq⟩
          · refine Fin.lastCases (fun _ => ?_) (fun a' h => ?_) a
            · simp only [Fin.snoc_last, Fin.snoc_castSucc]
              intro heq; exact hiNot ⟨b', heq.symm⟩
            · simp only [Fin.snoc_castSucc]
              exact st.2.2.1 a' b' (fun e => h (congrArg Fin.castSucc e))
        · intro a
          refine Fin.lastCases ?_ (fun a' => ?_) a
          · simp only [Fin.snoc_last]; exact hwk
          · simp only [Fin.snoc_castSucc]; exact st.2.2.2 a'
      let stSeq : (m : ℕ) → State m := fun m =>
        Nat.rec ⟨Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
          (fun k stk => (hnext_ex k stk).choose) m
      have hst_agree : ∀ (m : ℕ) (a : Fin m), (stSeq (m + 1)).1 a.castSucc = (stSeq m).1 a :=
        fun m a => (hnext_ex m (stSeq m)).choose_spec a
      have hst_le : ∀ {m r : ℕ} (h : m ≤ r) (a : Fin m),
          (stSeq r).1 ⟨a.1, lt_of_lt_of_le a.2 h⟩ = (stSeq m).1 a := by
        intro m r h a; induction h with
        | refl => rfl
        | @step k hmk ih => rw [← ih]; exact hst_agree k ⟨a.1, lt_of_lt_of_le a.2 hmk⟩
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
    -- Pass to a subsequence `φ` deciding every `i ∈ hE_fin.toFinset`.
    obtain ⟨φ, hφ_strict, hφ_dec⟩ := exists_subseq_deciding_finset 𝓗 w hE_fin.toFinset
    -- Look at `B₀ := (⋃ i ∈ S (φ 0), 𝓗 i)ᶜ ∈ 𝓖`. Since `z ∉ closure B₀`, pick open `O ∋ z` disjoint from `B₀`.
    have hz_not_B0 : z ∉ closure (⋃ i ∈ S (φ 0), 𝓗 i)ᶜ := fun hzB0 =>
      hz_not ⟨closure (⋃ i ∈ S (φ 0), 𝓗 i)ᶜ, ⟨_, hSG (φ 0), rfl⟩, hzB0⟩
    let O : Set Y := (closure (⋃ i ∈ S (φ 0), 𝓗 i)ᶜ)ᶜ
    have hOo : IsOpen O := isClosed_closure.isOpen_compl
    have hO_sub : O ⊆ ⋃ i ∈ S (φ 0), 𝓗 i := by
      intro y hyO
      by_contra hyNot
      exact hyO (subset_closure hyNot)
    obtain ⟨M, hM⟩ :=
      Filter.eventually_atTop.mp ((hw_tend.comp hφ_strict.tendsto_atTop).eventually (hOo.mem_nhds hz_not_B0))
    -- For every `m ≥ M`, `w (φ m) ∈ 𝓗 (j m)` for some `j m ∈ S (φ 0)` with `j m ∉ E`!
    have hj_ex : ∀ m : ℕ, ∃ j : ι, j ∈ S (φ 0) ∧ w (φ (m + M)) ∈ 𝓗 j ∧ j ∉ E := by
      intro m
      have hm_in : w (φ (m + M)) ∈ ⋃ i ∈ S (φ 0), 𝓗 i := hO_sub (hM (m + M) (Nat.le_add_left M m))
      obtain ⟨j, hjS, hwj⟩ := mem_iUnion₂.mp hm_in
      refine ⟨j, hjS, hwj, fun hjE => ?_⟩
      rcases hφ_dec j (hE_fin.mem_toFinset.mpr hjE) with hall | hnone
      · exact hwkS (φ 0) (mem_iUnion₂.mpr ⟨j, hjS, hall 0⟩)
      · exact hnone (m + M) hwj
    choose j _ hj_hit hj_notE using hj_ex
    -- Each `j m ∉ E` hits only finitely many `w k`, so `Set.range j` is infinite!
    have hrange_inf : (Set.range j).Infinite := by
      intro hfin
      have hsub : (Set.univ : Set ℕ) ⊆ ⋃ i ∈ Set.range j, { m : ℕ | w (φ (m + M)) ∈ 𝓗 i } := by
        intro m _
        exact mem_iUnion₂.mpr ⟨j m, ⟨m, rfl⟩, hj_hit m⟩
      have hfin_u : (⋃ i ∈ Set.range j, { m : ℕ | w (φ (m + M)) ∈ 𝓗 i }).Finite := by
        refine hfin.biUnion fun i hi => ?_
        obtain ⟨m₀, rfl⟩ := hi
        have hnotInf : { k : ℕ | w k ∈ 𝓗 (j m₀) }.Finite := Set.not_infinite.mp (hj_notE m₀)
        have hpre : (fun m : ℕ => φ (m + M)) ⁻¹' { k : ℕ | w k ∈ 𝓗 (j m₀) } =
            { m : ℕ | w (φ (m + M)) ∈ 𝓗 (j m₀) } := rfl
        rw [← hpre]
        exact hnotInf.preimage ((hφ_strict.comp (fun _ _ h => Nat.add_lt_add_right h M)).injective.injOn)
      exact Set.infinite_univ (hfin_u.subset hsub)
    -- Extract strictly increasing `ψ` with `j ∘ ψ` injective!
    have hstep_ψ : ∀ (m : ℕ) (prev : Fin m → ℕ),
        ∃ k : ℕ, (∀ a, prev a < k) ∧ ∀ a, j k ≠ j (prev a) := by
      intro m prev
      let used : Set ι := Set.range (fun a : Fin m => j (prev a))
      have hsub_fin : { k : ℕ | j k ∈ used }.Finite := by
        have hEq : { k : ℕ | j k ∈ used } ⊆ ⋃ i ∈ used, { k : ℕ | w (φ (k + M)) ∈ 𝓗 i } := by
          intro k hk; exact mem_iUnion₂.mpr ⟨j k, hk, hj_hit k⟩
        refine ((Set.finite_range _).biUnion fun i hi => ?_).subset hEq
        obtain ⟨a, rfl⟩ := hi
        have hnotInf : { r : ℕ | w r ∈ 𝓗 (j (prev a)) }.Finite := Set.not_infinite.mp (hj_notE (prev a))
        have hpre : (fun k : ℕ => φ (k + M)) ⁻¹' { r : ℕ | w r ∈ 𝓗 (j (prev a)) } =
            { k : ℕ | w (φ (k + M)) ∈ 𝓗 (j (prev a)) } := rfl
        rw [← hpre]
        exact hnotInf.preimage ((hφ_strict.comp (fun _ _ h => Nat.add_lt_add_right h M)).injective.injOn)
      let maxP : ℕ := if hm : 0 < m then Finset.univ.sup prev + 1 else 0
      have hex : ∃ k ≥ maxP, j k ∉ used := by
        by_contra hnone
        push Not at hnone
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
      intro m st
      obtain ⟨k, hk_gt, hk_ne⟩ := hstep_ψ m st.1
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
    have hst2_agree : ∀ (m : ℕ) (a : Fin m), (stSeq2 (m + 1)).1 a.castSucc = (stSeq2 m).1 a :=
      fun m a => (hnext2 m (stSeq2 m)).choose_spec a
    have hst2_le : ∀ {m r : ℕ} (h : m ≤ r) (a : Fin m),
        (stSeq2 r).1 ⟨a.1, lt_of_lt_of_le a.2 h⟩ = (stSeq2 m).1 a := by
      intro m r h a; induction h with
      | refl => rfl
      | @step k hmk ih => rw [← ih]; exact hst2_agree k ⟨a.1, lt_of_lt_of_le a.2 hmk⟩
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

/-- **Every Point of Every Lašnev Space Has a CP Open Outer Base**:
For **any** metric space `X` (complete or not!) and **any** closed continuous surjection
`f : X → Y`, every point `y₀ ∈ Y` has a closure-preserving open outer base
`Defs.D_0001.HasCPOuterBase y₀`. -/
theorem lasnev_every_point_hasCPOuterBase {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
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
  -- Whitney locally finite cover of `X' = Fᶜ`.
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
  -- Restrict `f` to `f' : X' → Y'` (closed continuous surjection!).
  let f' : X' → Y' := fun x => ⟨f x.1, x.2⟩
  have hf'_cont : Continuous f' := (hf_cont.comp continuous_subtype_val).subtype_mk _
  have hf'_closed : IsClosedMap f' := by
    intro C hC
    rw [isClosed_induced_iff] at hC ⊢
    obtain ⟨D, hDcl, hDC⟩ := hC
    refine ⟨f '' D, hf_closed D hDcl, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hxD, hfx⟩
      have hxNotF : x ∉ F := by
        intro hxF; exact y.2 (hfx.symm.trans hxF)
      have hxC : (⟨x, hxNotF⟩ : X') ∈ C := by rw [← hDC]; exact hxD
      exact ⟨⟨x, hxNotF⟩, hxC, Subtype.ext hfx⟩
    · rintro ⟨x, hxC, hfx⟩
      have hxD : x.1 ∈ D := by rw [← hDC] at hxC; exact hxC
      exact ⟨x.1, hxD, congrArg Subtype.val hfx⟩
  -- `𝓗' a := f' '' closure (W a)` is HCP in `Y'`!
  let 𝓗' : X' → Set Y' := fun a => f' '' closure (W a)
  have hH'_hcp : IsHCP 𝓗' := isHCP_image_of_locallyFinite_isClosedMap hf'_cont hf'_closed hWlf.closure
  -- Push `𝓗' a` into `Y`: `𝓗 a := f '' closure (WX a)` (closed in `Y`, avoids `y₀`, and `Subtype.val ⁻¹' 𝓗 a = 𝓗' a`!).
  let 𝓗 : X' → Set Y := fun a => f '' closure (WX a)
  have hH_not_y0 : ∀ a, y₀ ∉ 𝓗 a := by
    rintro a ⟨x, hxCl, hfx⟩
    exact Set.disjoint_left.mp (hWX_cl_disj a) hxCl hfx
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
      have : q₂ = q₁ := Subtype.ext hqeq
      subst this; exact ⟨q₂, hq₁V, hq₂W⟩
    · rintro ⟨x, hxCl, hfx⟩
      refine ⟨x.1, ?_, congrArg Subtype.val hfx⟩
      exact image_closure_subset_closure_image continuous_subtype_val ⟨x, hxCl, rfl⟩
  -- Define the CP open outer base `𝓑` of `y₀` in `Y`!
  let 𝓑 : Set (Set Y) :=
    { U : Set Y | ∃ S : Set X',
        y₀ ∉ closure (⋃ a ∈ S, 𝓗 a) ∧
        U = (⋃ a ∈ S, 𝓗 a)ᶜ }
  refine ⟨𝓑, ?_, ?_, ?_⟩
  · -- Open and containing `y₀`:
    rintro U ⟨S, hy₀Not, rfl⟩
    have hcl : IsClosed (⋃ a ∈ S, 𝓗 a) := by
      rw [← closure_subset_iff_isClosed]
      intro z hz
      have hz_ne : z ≠ y₀ := fun heq => hy₀Not (heq ▸ hz)
      have hz' : (⟨z, hz_ne⟩ : Y') ∈ closure (⋃ a ∈ S, 𝓗' a) := by
        rw [mem_closure_iff]; intro V hVo hzV
        let VY : Set Y := (Subtype.val : Y' → Y) '' V
        have hVYo : IsOpen VY := hY'_open.isOpenMap_subtype_val _ hVo
        obtain ⟨q, hqVY, hqU⟩ := mem_closure_iff.mp hz VY hVYo ⟨⟨z, hz_ne⟩, hzV, rfl⟩
        obtain ⟨q', hq'V, rfl⟩ := hqVY
        obtain ⟨a, haS, hq'H⟩ := mem_iUnion₂.mp hqU
        have hq'H' : q' ∈ 𝓗' a := by rw [← hH_pre a]; exact hq'H
        exact ⟨q', hq'V, mem_iUnion₂.mpr ⟨a, haS, hq'H'⟩⟩
      -- By HCP of `𝓗'` in `Y'`, `⋃ a ∈ S, 𝓗' a` is closed in `Y'`!
      let T : X' → Set Y' := fun a => if a ∈ S then 𝓗' a else ∅
      have hT_eq : (⋃ a, T a) = ⋃ a ∈ S, 𝓗' a := by
        ext q; simp only [mem_iUnion, T]
        constructor
        · rintro ⟨a, ha⟩
          by_cases haS : a ∈ S
          · simp only [ite_eq_left haS] at ha; exact ⟨a, haS, ha⟩
          · simp only [ite_eq_right haS] at ha; exact ha.elim
        · rintro ⟨a, haS, ha⟩; exact ⟨a, by simp only [ite_eq_left haS]; exact ha⟩
      have hT_cl : ∀ a, closure (T a) = T a := fun a => by
        by_cases haS : a ∈ S
        · simp only [T, ite_eq_left haS]; exact (hf'_closed _ isClosed_closure).closure_eq
        · simp only [T, ite_eq_right haS, closure_empty]
      rw [← hT_eq, hH'_hcp T (fun a => by by_cases h : a ∈ S <;> simp [T, h])] at hz'
      obtain ⟨a, ha⟩ := mem_iUnion.mp hz'
      rw [hT_cl a] at ha
      by_cases haS : a ∈ S
      · simp only [T, ite_eq_left haS] at ha
        have hzH : z ∈ 𝓗 a := by rw [← hH_pre a] at ha; exact ha
        exact mem_iUnion₂.mpr ⟨a, haS, hzH⟩
      · simp only [T, ite_eq_right haS] at ha; exact ha.elim
    refine ⟨hcl.isOpen_compl, fun hy => ?_⟩
    obtain ⟨a, _, ha⟩ := mem_iUnion₂.mp hy
    exact hH_not_y0 a ha
  · -- Outer base at `y₀`:
    intro O hOo hy₀O
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
      rw [dist_comm a.1 y] at hky
      linarith
    have hy₀Not : y₀ ∉ closure (⋃ a ∈ S, 𝓗 a) := by
      have hsub : (⋃ a ∈ S, 𝓗 a) ⊆ f '' closure (⋃ a ∈ S, WX a) := by
        rintro z hz
        obtain ⟨a, haS, x, hxCl, rfl⟩ := mem_iUnion₂.mp hz
        exact ⟨x, closure_mono (subset_biUnion_of_mem haS) hxCl, rfl⟩
      have hcl_im : IsClosed (f '' closure (⋃ a ∈ S, WX a)) := hf_closed _ isClosed_closure
      intro hy₀Cl
      obtain ⟨x, hxCl, hfx⟩ := closure_minimal hsub hcl_im hy₀Cl
      exact Set.disjoint_left.mp hSdisj hxCl hfx
    refine ⟨(⋃ a ∈ S, 𝓗 a)ᶜ, ⟨S, hy₀Not, rfl⟩, fun z hzU => ?_⟩
    by_contra hzNotO
    obtain ⟨x, rfl⟩ := hf_surj z
    have hxNotF : x ∉ F := fun hxF => hzNotO (hF_sub hxF)
    obtain ⟨a, hxa⟩ := mem_iUnion.mp (show (⟨x, hxNotF⟩ : X') ∈ ⋃ a, W a by rw [hWcov]; trivial)
    have hxWX : x ∈ WX a := ⟨⟨x, hxNotF⟩, hxa, rfl⟩
    exact hzU (mem_iUnion₂.mpr ⟨a, ⟨x, hxWX, hzNotO⟩, x, subset_closure hxWX, rfl⟩)
  · -- Closure-preserving via `closurePreserving_compl_sUnion_of_isHCP_frechetUrysohn` on `Y'`!
    intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      by_cases hz_eq : z = y₀
      · subst hz_eq
        by_cases hGne : 𝓖.Nonempty
        · obtain ⟨U, hUG⟩ := hGne
          obtain ⟨S, _, rfl⟩ := h𝓖 hUG
          have hy₀U : z ∈ (⋃ a ∈ S, 𝓗 a)ᶜ := by
            intro hIn; obtain ⟨a, _, ha⟩ := mem_iUnion₂.mp hIn; exact hH_not_y0 a ha
          exact ⟨closure _, ⟨_, hUG, rfl⟩, subset_closure hy₀U⟩
        · rw [Set.not_nonempty_iff_eq_empty.mp hGne, sUnion_empty, closure_empty] at hz
          exact hz.elim
      · let 𝓖' : Set (Set Y') := (fun U : Set Y => (Subtype.val : Y' → Y) ⁻¹' U) '' 𝓖
        have hG'_sub : 𝓖' ⊆ { B : Set Y' | ∃ S : Set X', B = (⋃ a ∈ S, 𝓗' a)ᶜ } := by
          rintro _ ⟨U, hUG, rfl⟩
          obtain ⟨S, _, rfl⟩ := h𝓖 hUG
          refine ⟨S, ?_⟩
          ext q; simp only [mem_preimage, mem_compl_iff, mem_iUnion]
          constructor
          · intro h ⟨a, haS, hqH'⟩
            exact h ⟨a, haS, by rw [← hH_pre a] at hqH'; exact hqH'⟩
          · intro h ⟨a, haS, hqH⟩
            exact h ⟨a, haS, by rw [← hH_pre a]; exact hqH⟩
        have hz' : (⟨z, hz_eq⟩ : Y') ∈ closure (⋃₀ 𝓖') := by
          rw [mem_closure_iff]; intro V hVo hzV
          let VY : Set Y := (Subtype.val : Y' → Y) '' V
          obtain ⟨q, hqVY, ⟨U, hUG, hqU⟩⟩ :=
            mem_closure_iff.mp hz VY (hY'_open.isOpenMap_subtype_val _ hVo) ⟨⟨z, hz_eq⟩, hzV, rfl⟩
          obtain ⟨q', hq'V, rfl⟩ := hqVY
          exact ⟨q', hq'V, ⟨(Subtype.val : Y' → Y) ⁻¹' U, ⟨U, hUG, rfl⟩, hqU⟩⟩
        rw [closurePreserving_compl_sUnion_of_isHCP_frechetUrysohn hFU_Y' hH'_hcp 𝓖' hG'_sub] at hz'
        obtain ⟨_, ⟨_, ⟨U, hUG, rfl⟩, rfl⟩, hzCl⟩ := hz'
        exact ⟨closure U, ⟨U, hUG, rfl⟩,
          continuous_subtype_val.closure_preimage_subset U hzCl⟩
    · rintro z ⟨_, ⟨U, hUG, rfl⟩, hzU⟩
      exact closure_mono (Set.subset_sUnion_of_mem hUG) hzU

end Research.HCPLasnev
