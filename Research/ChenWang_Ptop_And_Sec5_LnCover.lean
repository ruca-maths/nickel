import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Basic.Countable.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Finset.Basic
import Defs.D_0001
import Defs.D_0007
import Defs.D_0009
import Defs.D_0012
import Defs.D_0024
import Defs.D_0025
import Defs.D_0028
import Defs.D_0029
import Defs.D_0030
import Defs.D_0031
import Defs.D_0032
import Proofs.L_0004
import Proofs.L_0029
import Proofs.L_0032
import Specs.L_0031
import Targets.Defs
import Targets.Goals

/-!
# Chen–Wang `ptop` Stratifiability, Refinement Bridge to `L_0031` / `¬ Tinf`, and Section 5 `lnc` Punctured Covers

Built directly on `Defs.D_0029`–`Defs.D_0032` (the corrected Chen–Wang topology `ptop`,
Proposition 3.4, Proposition 3.5.1–3.5.3, `lnc`, and Proposition 4.8):

1. `rho_secondCountable` / `rho_t3Space` / `ptop_secondCountable` /
   `ptop_t3Space` / `ptop_metrizable` / `ptop_isStratifiable` / `ptop_subtype_isStratifiable`:
   for any countable linear order `α` with `[NoMaxOrder α]` (in particular `Defs.D_0028.Node`),
   `(α, Defs.D_0009.rho α)` and the countable product `(ℕ → α, Defs.D_0029.ptop α)` (as well as
   every subspace `Y ⊆ ℕ → α`) are **second-countable, `T₃`, metrizable, and stratifiable**.
2. `ptop_subtype_refinement_isStratifiable` / `ptop_subtype_refinement_L0031_and_not_Tinf`:
   for any subspace `Y ⊆ ℕ → α` and any finer topology `τ ≤ ptop_Y` (the exact setting of
   Chen–Wang §6–§7!), separating `τ`-closed sets `F` from their **`ptop`-boundary**
   `closure_ptop F \ F` via a `τ`-open `g`-function suffices for `MSpace.IsStratifiable`;
   combining with `gfun q T (n + 1) y₀` (which is `ptop`-clopen and intersects to `{y₀}`) and
   `¬ HasCPOuterBase y₀` directly yields `Specs.L_0031.stmt` and `¬ MSpace.Goals.Tinf_M3_imp_M1`.
3. **Section 5 Punctured `lnc` Decomposition** (`lnc_diff_cover_point`, `lnc_diff_iUnion_eq`,
   `lnc_diff_clopen_disjoint`, `prop_4_8_star_clopen`):
   for any `Hcell q T n x ⊆ gfun q T m y0`, the punctured cell `gfun q T m y0 \ Hcell q T n x`
   is exhausted by `⋃ ℓ ≥ m, ⋃₀ lnc q T ℓ (gfun q T m y0 \ Hcell q T n x)` of pairwise disjoint
   `ptop`-clopen `gfun` cells, and the `prop_4_8` star around `Hcell q T n x` is a `ptop`-clopen
   neighborhood whose `Hcell` centers all lie inside `Hcell q T n x`.
-/

namespace Research.ChenWangPtopSec5

open Set Topology TopologicalSpace
open Defs.D_0003 Defs.D_0007 Defs.D_0009 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0029
  Defs.D_0030 Defs.D_0031 Defs.D_0032

/-! ## Part 1: `(α, rho α)` and `(ℕ → α, ptop α)` are Second-Countable, `T₃`, Metrizable, and Stratifiable -/

theorem rho_secondCountable (α : Type) [LinearOrder α] [Countable α] :
    @SecondCountableTopology α (rho α) := by
  let _ : TopologicalSpace α := rho α
  let 𝓢 : Set (Set α) := { s | ∃ a b : α, s = Set.Ico a b }
  have hScnt : 𝓢.Countable := by
    have hEq : 𝓢 = Set.range (fun p : α × α => Set.Ico p.1 p.2) := by
      ext s; simp only [𝓢, mem_ofPred_eq, mem_range, Prod.exists]
      exact ⟨fun ⟨a, b, h⟩ => ⟨a, b, h.symm⟩, fun ⟨a, b, h⟩ => ⟨a, b, h.symm⟩⟩
    rw [hEq]; exact Set.countable_range _
  exact ⟨⟨𝓢, hScnt, rfl⟩⟩

theorem rho_t3Space (α : Type) [LinearOrder α] [NoMaxOrder α] :
    @T3Space α (rho α) := by
  let _ : TopologicalSpace α := rho α
  have hT1 : T1Space α := ⟨fun x => by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    have hne : y ≠ x := hy
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Filter.mem_of_superset ((isOpen_Ico y x).mem_nhds ⟨le_rfl, hlt⟩)
        (fun z hz => ne_of_lt hz.2)
    · obtain ⟨b, hb⟩ := exists_gt y
      exact Filter.mem_of_superset ((isOpen_Ico y b).mem_nhds ⟨le_rfl, hb⟩)
        (fun z hz => ne_of_gt (lt_of_lt_of_le hgt hz.1))⟩
  have hReg : RegularSpace α := RegularSpace.of_exists_mem_nhds_isClosed_subset fun x U hU => by
    obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
    obtain ⟨b, hxb, hbV⟩ := rho_nhd hVo hxV
    exact ⟨Set.Ico x b, (isOpen_Ico x b).mem_nhds ⟨le_rfl, hxb⟩, isClosed_Ico x b, hbV.trans hVU⟩
  exact inferInstance

theorem ptop_secondCountable (α : Type) [LinearOrder α] [Countable α] :
    @SecondCountableTopology (ℕ → α) (ptop α) := by
  let _ : TopologicalSpace α := rho α
  have : SecondCountableTopology α := rho_secondCountable α
  change @SecondCountableTopology (ℕ → α) Pi.topologicalSpace
  exact inferInstance

theorem ptop_t3Space (α : Type) [LinearOrder α] [NoMaxOrder α] :
    @T3Space (ℕ → α) (ptop α) := by
  let _ : TopologicalSpace α := rho α
  have : T3Space α := rho_t3Space α
  change @T3Space (ℕ → α) Pi.topologicalSpace
  exact inferInstance

theorem ptop_metrizable (α : Type) [LinearOrder α] [Countable α] [NoMaxOrder α] :
    @MetrizableSpace (ℕ → α) (ptop α) := by
  let _ : TopologicalSpace (ℕ → α) := ptop α
  have : SecondCountableTopology (ℕ → α) := ptop_secondCountable α
  have : T3Space (ℕ → α) := ptop_t3Space α
  exact metrizableSpace_of_t3_secondCountable (ℕ → α)

/-- Every second-countable `T₃` space is stratifiable. -/
private theorem isStratifiable_of_secondCountable_t3 {X : Type*} [TopologicalSpace X]
    [T3Space X] [SecondCountableTopology X] :
    MSpace.IsStratifiable X := by
  classical
  obtain ⟨𝓑, hBcnt, _, hBbasis⟩ := exists_countable_basis X
  let P := { p : 𝓑 × 𝓑 // closure p.1.1 ⊆ p.2.1 }
  have : Countable 𝓑 := hBcnt.to_subtype
  have : Countable P := inferInstance
  by_cases hPne : Nonempty P
  · obtain ⟨e, he⟩ := exists_surjective_nat P
    let G : ℕ → Set X → Set X := fun n F =>
      (⋃ k ∈ Finset.range (n + 1), if Disjoint (e k).1.2.1 F then closure (e k).1.1.1 else ∅)ᶜ
    refine ⟨inferInstance, G, ?_, ?_, ?_, ?_⟩
    · intro n F _
      refine (isClosed_biUnion_finset fun k _ => ?_).isOpen_compl
      by_cases h : Disjoint (e k).1.2.1 F
      · simp only [ite_eq_left h]; exact isClosed_closure
      · simp only [ite_eq_right h]; exact isClosed_empty
    · intro n F _ x hxF hxIn
      obtain ⟨k, _, hxk⟩ := mem_iUnion₂.mp hxIn
      by_cases h : Disjoint (e k).1.2.1 F
      · simp only [ite_eq_left h] at hxk
        exact Set.disjoint_left.mp h ((e k).2 hxk) hxF
      · simp only [ite_eq_right h] at hxk; exact hxk
    · intro F hF
      apply Subset.antisymm
      · intro x hx
        by_contra hxF
        obtain ⟨U₂, hU₂mem, hxU₂, hU₂Fc⟩ := hBbasis.exists_subset_of_mem_open hxF hF.isOpen_compl
        obtain ⟨t, ht, htc, htU₂⟩ :=
          exists_mem_nhds_isClosed_subset ((hBbasis.isOpen hU₂mem).mem_nhds hxU₂)
        obtain ⟨U₁, hU₁mem, hxU₁, hU₁t⟩ :=
          hBbasis.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.mpr ht) isOpen_interior
        have hclU₁ : closure U₁ ⊆ U₂ := (closure_minimal (hU₁t.trans interior_subset) htc).trans htU₂
        let p : P := ⟨(⟨U₁, hU₁mem⟩, ⟨U₂, hU₂mem⟩), hclU₁⟩
        obtain ⟨k, hk⟩ := he p
        have hdisj : Disjoint (e k).1.2.1 F := by
          rw [hk]; exact Set.disjoint_left.mpr fun y hyU₂ hyF => hU₂Fc hyU₂ hyF
        have hxCl : x ∈ closure (G k F) := mem_iInter.mp hx k
        obtain ⟨y, hyU₁, hyG⟩ := mem_closure_iff.mp hxCl U₁ (hBbasis.isOpen hU₁mem) hxU₁
        apply hyG
        refine mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), ?_⟩
        rw [ite_eq_left hdisj, hk]
        exact subset_closure hyU₁
      · intro x hxF; rw [mem_iInter]; intro n
        apply subset_closure; intro hxIn
        obtain ⟨k, _, hxk⟩ := mem_iUnion₂.mp hxIn
        by_cases h : Disjoint (e k).1.2.1 F
        · simp only [ite_eq_left h] at hxk
          exact Set.disjoint_left.mp h ((e k).2 hxk) hxF
        · simp only [ite_eq_right h] at hxk; exact hxk
    · intro n F₁ F₂ _ _ hsub x hxG hxIn
      apply hxG
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxIn
      refine mem_iUnion₂.mpr ⟨k, hk, ?_⟩
      by_cases h₂ : Disjoint (e k).1.2.1 F₂
      · simp only [ite_eq_left h₂] at hxk
        have h₁ : Disjoint (e k).1.2.1 F₁ := h₂.mono_right hsub
        simp only [ite_eq_left h₁]; exact hxk
      · simp only [ite_eq_right h₂] at hxk; exact hxk.elim
  · have : IsEmpty X := ⟨fun x => by
      obtain ⟨U₂, hU₂mem, hxU₂, _⟩ := hBbasis.exists_subset_of_mem_open (mem_univ x) isOpen_univ
      obtain ⟨t, ht, htc, htU₂⟩ :=
        exists_mem_nhds_isClosed_subset ((hBbasis.isOpen hU₂mem).mem_nhds hxU₂)
      obtain ⟨U₁, hU₁mem, _, hU₁t⟩ :=
        hBbasis.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.mpr ht) isOpen_interior
      exact hPne ⟨⟨(⟨U₁, hU₁mem⟩, ⟨U₂, hU₂mem⟩), (closure_minimal (hU₁t.trans interior_subset) htc).trans htU₂⟩⟩⟩
    refine ⟨inferInstance, fun _ F => F, fun _ F _ => by
      have hEq : F = ∅ := Set.eq_empty_of_isEmpty F; rw [hEq]; exact isOpen_empty,
      fun _ _ _ => Subset.rfl, fun F _ => by
      have hEq : F = ∅ := Set.eq_empty_of_isEmpty F; rw [hEq]; simp [Set.iInter_const],
      fun _ _ _ _ _ h => h⟩

/-- `(ℕ → α, ptop α)` is **stratifiable** for every countable linear order `α` with `[NoMaxOrder α]`. -/
theorem ptop_isStratifiable (α : Type) [LinearOrder α] [Countable α] [NoMaxOrder α] :
    @MSpace.IsStratifiable (ℕ → α) (ptop α) := by
  let _ : TopologicalSpace (ℕ → α) := ptop α
  have : SecondCountableTopology (ℕ → α) := ptop_secondCountable α
  have : T3Space (ℕ → α) := ptop_t3Space α
  exact isStratifiable_of_secondCountable_t3

/-- Every subspace `Y ⊆ ℕ → α` equipped with the induced `ptop α` topology is **stratifiable**. -/
theorem ptop_subtype_isStratifiable (α : Type) [LinearOrder α] [Countable α] [NoMaxOrder α]
    (Y : Set (ℕ → α)) :
    @MSpace.IsStratifiable Y (TopologicalSpace.induced Subtype.val (ptop α)) := by
  let _ : TopologicalSpace (ℕ → α) := ptop α
  have : SecondCountableTopology (ℕ → α) := ptop_secondCountable α
  have : T3Space (ℕ → α) := ptop_t3Space α
  exact isStratifiable_of_secondCountable_t3

/-- `Defs.D_0028.Node` is countable, hence `(ℕ → Node, ptop Node)` and every subspace `Y ⊆ ℕ → Node`
are second-countable, `T₃`, metrizable, and stratifiable! -/
instance node_countable : Countable Defs.D_0028.Node :=
  Function.Injective.countable (f := fun s : Defs.D_0028.Node => s.val)
    (fun _ _ h => by cases ‹Defs.D_0028.Node›; cases ‹Defs.D_0028.Node›; congr)

theorem ptop_node_isStratifiable :
    @MSpace.IsStratifiable (ℕ → Defs.D_0028.Node) (ptop Defs.D_0028.Node) :=
  ptop_isStratifiable Defs.D_0028.Node

/-! ## Part 2: Refinement Stratifiability & Direct `L_0031` / `¬ Tinf` Bridge on `ptop` -/

/-- **Refinement Stratifiability Theorem on `ptop`**:
Let `Y ⊆ ℕ → α` (with `α` countable, `[NoMaxOrder α]`), let `τ₀` be the induced `ptop α` topology on
`Y`, and let `τ ≤ τ₀` be any finer topology on `Y`.
If there is a `τ`-open `g`-function `g : ℕ → Y → Set Y` that separates every `τ`-closed set `F`
from its **`τ₀`-boundary** `closure_{τ₀} F \ F`, then `(Y, τ)` is **stratifiable**. -/
theorem ptop_subtype_refinement_isStratifiable
    {α : Type} [LinearOrder α] [Countable α] [NoMaxOrder α]
    {Y : Set (ℕ → α)} {τ : TopologicalSpace Y}
    (hle : τ ≤ TopologicalSpace.induced Subtype.val (ptop α))
    (g : ℕ → Y → Set Y)
    (hg_open : ∀ n y, @IsOpen Y τ (g n y))
    (hg_mem : ∀ n y, y ∈ g n y)
    (hg_bdy : ∀ F : Set Y, @IsClosed Y τ F →
      ∀ x : Y, x ∈ @closure Y (TopologicalSpace.induced Subtype.val (ptop α)) F → x ∉ F →
        ∃ n, x ∉ @closure Y τ (⋃ y ∈ F, g n y)) :
    @MSpace.IsStratifiable Y τ := by
  let τ₀ : TopologicalSpace Y := TopologicalSpace.induced Subtype.val (ptop α)
  have hS₀ : @MSpace.IsStratifiable Y τ₀ := ptop_subtype_isStratifiable α Y
  have hT1₀ : @T1Space Y τ₀ := hS₀.1
  have hT1 : @T1Space Y τ :=
    @T1Space.mk Y τ (fun x => (@isOpen_compl_iff Y {x} τ).mp (hle _ (@isClosed_singleton Y τ₀ hT1₀ x).isOpen_compl))
  obtain ⟨_, G₀, hG₀o, hG₀sub, hG₀inter, hG₀mono⟩ := hS₀
  let G : ℕ → Set Y → Set Y := fun p F =>
    G₀ (Nat.unpair p).1 (@closure Y τ₀ F) ∩ (⋃ y ∈ F, g (Nat.unpair p).2 y)
  refine ⟨hT1, G, ?_, ?_, ?_, ?_⟩
  · intro p F _
    have h1 : @IsOpen Y τ (G₀ (Nat.unpair p).1 (@closure Y τ₀ F)) :=
      hle _ (hG₀o _ _ (@isClosed_closure Y τ₀ F))
    have h2 : @IsOpen Y τ (⋃ y ∈ F, g (Nat.unpair p).2 y) :=
      @isOpen_biUnion Y Y τ _ _ (fun y _ => hg_open _ y)
    exact @IsOpen.inter Y τ _ _ h1 h2
  · intro p F _ x hxF
    exact ⟨hG₀sub _ _ (@isClosed_closure Y τ₀ F) (@subset_closure Y τ₀ F _ hxF),
      mem_iUnion₂.mpr ⟨x, hxF, hg_mem _ x⟩⟩
  · intro F hF
    apply Subset.antisymm
    · intro x hx
      by_contra hxF
      by_cases hxCl₀ : x ∈ @closure Y τ₀ F
      · obtain ⟨k, hxk⟩ := hg_bdy F hF x hxCl₀ hxF
        have hxp : x ∈ @closure Y τ (G (Nat.pair 0 k) F) := mem_iInter.mp hx (Nat.pair 0 k)
        have hsub : G (Nat.pair 0 k) F ⊆ ⋃ y ∈ F, g k y := by
          simp only [G, Nat.unpair_pair]; exact inter_subset_right
        exact hxk (@closure_mono Y τ _ _ hsub _ hxp)
      · rw [← hG₀inter (@closure Y τ₀ F) (@isClosed_closure Y τ₀ F), mem_iInter] at hxCl₀
        push Not at hxCl₀
        obtain ⟨m, hxm⟩ := hxCl₀
        have hxp : x ∈ @closure Y τ (G (Nat.pair m 0) F) := mem_iInter.mp hx (Nat.pair m 0)
        have hsub : G (Nat.pair m 0) F ⊆ G₀ m (@closure Y τ₀ F) := by
          simp only [G, Nat.unpair_pair]; exact inter_subset_left
        have hxClτ : x ∈ @closure Y τ (G₀ m (@closure Y τ₀ F)) := @closure_mono Y τ _ _ hsub _ hxp
        have hxClτ₀ : x ∈ @closure Y τ₀ (G₀ m (@closure Y τ₀ F)) := by
          rw [@mem_closure_iff Y τ₀]; intro U hUo hxU
          exact (@mem_closure_iff Y τ).mp hxClτ U (hle U hUo) hxU
        exact hxm hxClτ₀
    · intro x hxF; rw [mem_iInter]; intro p
      exact @subset_closure Y τ _ _
        ⟨hG₀sub _ _ (@isClosed_closure Y τ₀ F) (@subset_closure Y τ₀ F _ hxF),
          mem_iUnion₂.mpr ⟨x, hxF, hg_mem _ x⟩⟩
  · intro p F₁ F₂ _ _ hsub
    exact inter_subset_inter
      (hG₀mono _ _ _ (@isClosed_closure Y τ₀ F₁) (@isClosed_closure Y τ₀ F₂)
        (@closure_mono Y τ₀ _ _ hsub))
      (iUnion₂_mono' fun y hy => ⟨y, hsub hy, Subset.rfl⟩)

private theorem gfun_one_sub_zero {α : Type} [LinearOrder α]
    {q : ℕ ≃ α} {T : Tree2 α} (hc : Compat2 q T) (x : ℕ → α) :
    gfun q T 1 x ⊆ gfun q T 0 x := by
  rintro z ⟨h1, h2⟩
  have hc' : hidx q 0 x ≤ hidx q 1 x := by
    show Defs.D_0007.code 0 (fun k => q.symm (x k)) ≤ hidx q 1 x
    simp [Defs.D_0007.code]
  have hab : lvl q 0 x ≤ lvl q 1 x := by unfold lvl; omega
  have ha := lvl_pos q 0 x
  refine ⟨fun k hk => by omega, fun k hk1 hk2 => ?_⟩
  rcases eq_or_lt_of_le hk1 with heq | hlt
  · subst heq
    have hz := h1 0 (by omega)
    obtain ⟨_, hxn⟩ := ibase_spec T ha (x 0)
    rcases eq_or_lt_of_le hxn.1 with he | hlt'
    · show z 0 ∈ Set.Ico (ibase T (lvl q 0 x) (x 0)) (T.child (ibase T (lvl q 0 x) (x 0)) (lvl q 0 x))
      rw [he]
      exact ⟨hz.1, lt_of_lt_of_le hz.2 (Tree2.child_le_child T _ ha hab)⟩
    · have := (prop_3_2_1' hc ha hlt' hxn.2).2.2 (lvl q 1 x) (lvl_pos _ _ _) hz
      exact ⟨this.1.le, this.2⟩
  · exact ival_mono T ha hab (x k) (h2 k (by omega) (by omega))

private theorem gfun_anti_all {α : Type} [LinearOrder α]
    {q : ℕ ≃ α} {T : Tree2 α} (hc : Compat2 q T) {m n : ℕ} (hmn : m ≤ n) (x : ℕ → α) :
    gfun q T n x ⊆ gfun q T m x := by
  cases m with
  | zero =>
    cases n with
    | zero => exact Subset.rfl
    | succ k =>
      exact (gfun_anti hc Nat.zero_lt_one (Nat.succ_le_succ (Nat.zero_le k)) x).trans
        (gfun_one_sub_zero hc x)
  | succ m' => exact gfun_anti hc (Nat.zero_lt_succ m') hmn x

/-- **Direct Bridge from a `ptop`-Refinement Model to `Specs.L_0031.stmt` and `¬ Tinf`**:
Given `q : ℕ ≃ α`, `T : Tree2 α`, `hc : Compat2 q T`, a subspace `Y ⊆ ℕ → α`, a basepoint `y₀ : Y`,
a refinement topology `τ ≤ ptop_Y` with a `ptop`-boundary-separating `g`-function, and
`¬ Defs.D_0001.HasCPOuterBase y₀`, we immediately obtain **`Specs.L_0031.stmt`** and
**`¬ MSpace.Goals.Tinf_M3_imp_M1`**! -/
theorem ptop_subtype_refinement_L0031_and_not_Tinf
    {α : Type} [LinearOrder α] [Countable α] [NoMaxOrder α]
    (q : ℕ ≃ α) (T : Tree2 α) (hc : Compat2 q T)
    {Y : Set (ℕ → α)} {τ : TopologicalSpace Y}
    (hle : τ ≤ TopologicalSpace.induced Subtype.val (ptop α))
    (g : ℕ → Y → Set Y)
    (hg_open : ∀ n y, @IsOpen Y τ (g n y))
    (hg_mem : ∀ n y, y ∈ g n y)
    (hg_bdy : ∀ F : Set Y, @IsClosed Y τ F →
      ∀ x : Y, x ∈ @closure Y (TopologicalSpace.induced Subtype.val (ptop α)) F → x ∉ F →
        ∃ n, x ∉ @closure Y τ (⋃ y ∈ F, g n y))
    (y₀ : Y) (hnotCP : ¬ @Defs.D_0001.HasCPOuterBase Y τ y₀) :
    Specs.L_0031.stmt ∧ ¬ MSpace.Goals.Tinf_M3_imp_M1 := by
  have hS : @MSpace.IsStratifiable Y τ :=
    ptop_subtype_refinement_isStratifiable hle g hg_open hg_mem hg_bdy
  let W : ℕ → Set Y := fun n => Subtype.val ⁻¹' gfun q T (n + 1) y₀.1
  have hW_clop : ∀ n, @IsOpen Y τ (W n) ∧ @IsClosed Y τ (W n) ∧ y₀ ∈ W n := fun n => by
    let τ₀ : TopologicalSpace Y := TopologicalSpace.induced Subtype.val (ptop α)
    have hpo : @IsOpen Y τ₀ (W n) := ⟨gfun q T (n + 1) y₀.1, gfun_isOpen_p q T (n + 1) y₀.1, rfl⟩
    have hpc : @IsOpen Y τ₀ (W n)ᶜ :=
      ⟨(gfun q T (n + 1) y₀.1)ᶜ, (gfun_isClosed_p q T (n + 1) y₀.1).isOpen_compl, rfl⟩
    refine ⟨hle _ hpo, (@isOpen_compl_iff Y (W n) τ).mp (hle _ hpc), mem_gfun q T (n + 1) y₀.1⟩
  have hW_inter : (⋂ n, W n) = {y₀} := by
    ext x; simp only [mem_iInter, mem_singleton_iff, W, mem_preimage]
    constructor
    · intro hx
      apply Subtype.ext
      by_contra hne
      let _ : TopologicalSpace (ℕ → α) := ptop α
      have : T3Space (ℕ → α) := ptop_t3Space α
      have hUo : IsOpen ({x.1}ᶜ : Set (ℕ → α)) := isClosed_singleton.isOpen_compl
      have hy₀U : y₀.1 ∈ ({x.1}ᶜ : Set (ℕ → α)) := fun h => hne h.symm
      obtain ⟨n, hn⟩ := prop_3_4 q T hc y₀.1 ({x.1}ᶜ) hUo hy₀U
      have hx1 : x.1 ∈ gfun q T n y₀.1 := by
        cases n with
        | zero => exact gfun_one_sub_zero hc y₀.1 (hx 0)
        | succ m => exact hx m
      exact hn hx1 rfl
    · intro h n; rw [h]; exact mem_gfun q T (n + 1) y₀.1
  have hL31 : Specs.L_0031.stmt := ⟨Y, τ, hS, y₀, ⟨W, hW_clop, hW_inter⟩, hnotCP⟩
  have hNotTinf : ¬ MSpace.Goals.Tinf_M3_imp_M1 := by
    intro hTinf
    have hM3 : @MSpace.IsM3 Y τ := @Proofs.L_0004.strat_to_m3 Y τ hS
    have hM1 : @MSpace.IsM1 Y τ := hTinf Y hM3
    have hSigCP := @Proofs.L_0029.main Y τ hM1 y₀
    have hCP := @Proofs.L_0032.main Y τ y₀ W hW_clop hW_inter hSigCP
    exact hnotCP hCP
  exact ⟨hL31, hNotTinf⟩

/-! ## Part 3: Section 5 Punctured `lnc` Covers on `gfun q T m y0 \ Hcell q T n x` -/

/-- For any `z ∈ gfun q T m y0 \ Hcell q T n x`, there is a level `ℓ ≥ m` such that
`gfun q T ℓ z ⊆ gfun q T m y0 \ Hcell q T n x`, hence `z` is covered by a member of
`lnc q T ℓ (gfun q T m y0 \ Hcell q T n x)`. -/
theorem lnc_diff_cover_point {α : Type} [LinearOrder α] [NoMaxOrder α]
    {q : ℕ ≃ α} {T : Tree2 α} (hc : Compat2 q T)
    {m n : ℕ} (hm : 0 < m) {x y0 z : ℕ → α}
    (hzG : z ∈ gfun q T m y0) (hzNotH : z ∉ Hcell q T n x) :
    ∃ ℓ, m ≤ ℓ ∧ ∃ S ∈ lnc q T ℓ (gfun q T m y0 \ Hcell q T n x), z ∈ S := by
  have hHcl : @IsClosed (ℕ → α) (ptop α) (Hcell q T n x) := Hcell_isClosed_p q T n x
  obtain ⟨ℓ₀, hℓ₀⟩ := prop_3_4 q T hc z (Hcell q T n x)ᶜ hHcl.isOpen_compl hzNotH
  let ℓ := max m ℓ₀
  have hsubG : gfun q T ℓ z ⊆ gfun q T m y0 := gfun_sub_of_mem hc hm (le_max_left m ℓ₀) hzG
  have hsubNotH : gfun q T ℓ z ⊆ (Hcell q T n x)ᶜ :=
    (gfun_anti_all hc (le_max_right m ℓ₀) z).trans hℓ₀
  obtain ⟨S, hS, hzS⟩ := lnc_exists hc ℓ (gfun q T m y0 \ Hcell q T n x) z
    (fun w hw => ⟨hsubG hw, hsubNotH hw⟩)
  exact ⟨ℓ, le_max_left m ℓ₀, S, hS, hzS (mem_gfun q T ℓ z)⟩

/-- **Section 5 Exhaustion Theorem**:
For any `m ≥ 1`, `gfun q T m y0 \ Hcell q T n x` is the **exact union** over `ℓ ≥ m` of
`⋃₀ lnc q T ℓ (gfun q T m y0 \ Hcell q T n x)`! -/
theorem lnc_diff_iUnion_eq {α : Type} [LinearOrder α] [NoMaxOrder α]
    {q : ℕ ≃ α} {T : Tree2 α} (hc : Compat2 q T)
    {m n : ℕ} (hm : 0 < m) (x y0 : ℕ → α) :
    (⋃ ℓ ≥ m, ⋃₀ lnc q T ℓ (gfun q T m y0 \ Hcell q T n x)) = gfun q T m y0 \ Hcell q T n x := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨ℓ, _, S, hS, hzS⟩ := mem_iUnion₂.mp hz
    exact lnc_sub hS hzS
  · rintro z ⟨hzG, hzNotH⟩
    obtain ⟨ℓ, hml, S, hS, hzS⟩ := lnc_diff_cover_point hc hm hzG hzNotH
    exact mem_iUnion₂.mpr ⟨ℓ, hml, S, hS, hzS⟩

/-- Every level `lnc q T ℓ (G \ H)` consists of pairwise disjoint `ptop`-clopen sets. -/
theorem lnc_diff_clopen_disjoint {α : Type} [LinearOrder α] [NoMaxOrder α]
    {q : ℕ ≃ α} {T : Tree2 α} (hc : Compat2 q T) (ℓ : ℕ) (G H : Set (ℕ → α)) :
    (∀ S ∈ lnc q T ℓ (G \ H), @IsOpen (ℕ → α) (ptop α) S ∧ @IsClosed (ℕ → α) (ptop α) S) ∧
    (∀ S₁ ∈ lnc q T ℓ (G \ H), ∀ S₂ ∈ lnc q T ℓ (G \ H), S₁ ≠ S₂ → Disjoint S₁ S₂) := by
  refine ⟨?_, fun S₁ hS₁ S₂ hS₂ hne => lnc_disjoint hc hS₁ hS₂ hne⟩
  rintro S ⟨x, rfl, -, -⟩
  exact ⟨gfun_isOpen_p q T ℓ x, gfun_isClosed_p q T ℓ x⟩

/-- **Corollary 4.9 (`prop_4_8` Star Clopen Neighborhood)**:
For `Hcell q T n x ⊆ gfun q T m y0` (`1 ≤ m ≤ n`), there exists `a ≥ n` such that for every
`ℓ ≥ a`, the star `U_ℓ := ⋃₀ {S ∈ lnc q T ℓ (gfun q T m y0) | (S ∩ Hcell q T n x).Nonempty}` is
a `ptop`-**clopen** neighborhood of `Hcell q T n x` contained in `gfun q T m y0`, and every
`gfun q T ℓ z` in this star has `Hcell q T ℓ z ⊆ Hcell q T n x`. -/
theorem prop_4_8_star_clopen {α : Type} [LinearOrder α] [NoMaxOrder α]
    {q : ℕ ≃ α} {T : Tree2 α} (hc : Compat2 q T)
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {x y0 : ℕ → α}
    (hx : Hcell q T n x ⊆ gfun q T m y0) :
    ∃ a, n ≤ a ∧ ∀ ℓ, a ≤ ℓ →
      let Star := {S | S ∈ lnc q T ℓ (gfun q T m y0) ∧ (S ∩ Hcell q T n x).Nonempty}
      Hcell q T n x ⊆ ⋃₀ Star ∧
      ⋃₀ Star ⊆ gfun q T m y0 ∧
      @IsOpen (ℕ → α) (ptop α) (⋃₀ Star) ∧
      @IsClosed (ℕ → α) (ptop α) (⋃₀ Star) ∧
      (∀ z, gfun q T ℓ z ∈ Star → Hcell q T ℓ z ⊆ Hcell q T n x) := by
  let _ : TopologicalSpace (ℕ → α) := ptop α
  obtain ⟨a, hna, ha⟩ := prop_4_8 hc hm hmn hx
  refine ⟨a, hna, fun ℓ hℓ => ?_⟩
  obtain ⟨hcov, hcent⟩ := ha ℓ hℓ
  have hdisc := lnc_discrete hc hm (hmn.trans (hna.trans hℓ)) y0
  refine ⟨hcov, ?_, ?_, ?_, fun z hz => hcent z hz.1 hz.2⟩
  · rintro w ⟨S, ⟨hS, _⟩, hwS⟩; exact lnc_sub hS hwS
  · exact isOpen_sUnion fun S hS => (hdisc.1 S hS.1).1
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hzNot
    obtain ⟨O, hOo, hzO, hOuniq⟩ := hdisc.2 z
    by_cases hex : ∃ S : {S // S ∈ lnc q T ℓ (gfun q T m y0)},
        (S.1 ∩ Hcell q T n x).Nonempty ∧ (S.1 ∩ O).Nonempty
    · obtain ⟨S₀, hS₀H, hS₀O⟩ := hex
      have hzNotS₀ : z ∉ S₀.1 := fun hzS₀ => hzNot ⟨S₀.1, ⟨S₀.2, hS₀H⟩, hzS₀⟩
      have hO'o : IsOpen (O \ S₀.1) := hOo.sdiff (hdisc.1 S₀.1 S₀.2).2
      refine Filter.mem_of_superset (hO'o.mem_nhds ⟨hzO, hzNotS₀⟩) ?_
      rintro w ⟨hwO, hwNotS₀⟩ ⟨S, ⟨hSlnc, _⟩, hwS⟩
      have hEq : S = S₀.1 := hOuniq ⟨S, hSlnc⟩ S₀ ⟨w, hwS, hwO⟩ hS₀O
      exact hwNotS₀ (hEq ▸ hwS)
    · push Not at hex
      refine Filter.mem_of_superset (hOo.mem_nhds hzO) ?_
      rintro w hwO ⟨S, ⟨hSlnc, hSH⟩, hwS⟩
      have hm : w ∈ S ∩ O := ⟨hwS, hwO⟩
      rw [hex ⟨S, hSlnc⟩ hSH] at hm; exact hm

end Research.ChenWangPtopSec5
