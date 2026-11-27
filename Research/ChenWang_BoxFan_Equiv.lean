import Targets
import Defs.D_0001
import Defs.D_0010
import Specs.L_0019
import Specs.L_0020
import Specs.L_0030
import Specs.L_0031
import Proofs.L_0002
import Proofs.L_0003
import Proofs.L_0004
import Proofs.L_0029
import Proofs.L_0032
import Proofs.R_0009
import Proofs.R_0010

/-!
# Exact Equivalence `Specs.L_0030.stmt ↔ Specs.L_0031.stmt` via `BoxFanGen`

The parent machine proved `R_0010` + `L_0032`:
  `Specs.L_0031.stmt → Specs.L_0030.stmt`
where `L_0031` adds the hypothesis that `y` admits a decreasing clopen sequence
`W n` with `⋂ n, W n = {y}` and weakens `¬ HasSigmaCPLocalBase y` to `¬ HasCPOuterBase y`.

This file proves the **exact converse** `Specs.L_0030.stmt → Specs.L_0031.stmt`
(and hence `Specs.L_0030.stmt ↔ Specs.L_0031.stmt`) using the **General Box-Fan**
construction `BoxFanGen Z := Option (ℕ × Z)` around a distinguished point `z₀ : Z`:

1. `boxFanGenTopology Z z₀`: each slice `k` carries the topology of `Z`, while basic
   neighborhoods of `none` are `{none} ∪ ⋃_{k ≥ N} ({k} × V_k)` with `V_k` open in `Z`
   containing `z₀`.
2. `boxFanGen_isStratifiable`: **Every** stratifiable space `(Z, z₀)` yields a
   stratifiable `BoxFanGen Z` (via the Heath–Lutzer–Zenor monotone normality operator
   `H_Z(A, B) := ⋃ n, (G'_Z n A \ closure (G'_Z n B))` built directly from `Z`'s
   stratification).
3. `boxFanGen_W_clopen` & `boxFanGen_W_inter`: `W n := {none} ∪ {some (k, z) | n ≤ k}`
   is clopen in `BoxFanGen Z` with `⋂ n, W n = {none}`.
4. `hasSigmaCPLocalBase_of_boxFanGen_hasCPOuterBase`: any single-layer CP open outer
   base at `none` in `BoxFanGen Z` slices across `k : ℕ` into a `σ`-CP open local
   base at `z₀` in `Z`.
5. `L0030_imp_L0031` & `L0030_iff_L0031`: `Specs.L_0030.stmt ↔ Specs.L_0031.stmt`.
   Thus the clopen `G_δ` point requirement in `Specs.L_0031` is completely free:
   resolving `L_0031` is logically equivalent to resolving `L_0030`.
-/

namespace Research.ChenWangBoxFanEquiv

open MSpace Set Topology

section BoxFanGenDef

/-- `BoxFanGen Z := Option (ℕ × Z)` attaches countably many clopen copies of `Z`
around the apex `none`. -/
abbrev BoxFanGen (Z : Type) : Type := Option (ℕ × Z)

/-- The `n`-th clopen shrinking neighborhood of `none` in `BoxFanGen Z`. -/
def boxFanGenW (Z : Type) (n : ℕ) : Set (BoxFanGen Z) :=
  { x | match x with | none => True | some (k, _) => n ≤ k }

/-- The box-fan topology on `BoxFanGen Z` relative to a basepoint `z₀ : Z`. -/
@[instance_reducible]
def boxFanGenTopology (Z : Type) [TopologicalSpace Z] (z₀ : Z) :
    TopologicalSpace (BoxFanGen Z) where
  IsOpen U :=
    (∀ k z, some (k, z) ∈ U →
      ∃ V : Set Z, IsOpen V ∧ z ∈ V ∧ ∀ w ∈ V, some (k, w) ∈ U) ∧
    (none ∈ U →
      ∃ N : ℕ, ∀ k, N ≤ k →
        ∃ V : Set Z, IsOpen V ∧ z₀ ∈ V ∧ ∀ w ∈ V, some (k, w) ∈ U)
  isOpen_univ :=
    ⟨fun _ _ _ => ⟨univ, isOpen_univ, trivial, fun _ _ => trivial⟩,
     fun _ => ⟨0, fun _ _ => ⟨univ, isOpen_univ, trivial, fun _ _ => trivial⟩⟩⟩
  isOpen_inter U₁ U₂ h₁ h₂ := by
    refine ⟨?_, ?_⟩
    · intro k z ⟨hz1, hz2⟩
      obtain ⟨V₁, hV₁, hzV₁, hsub₁⟩ := h₁.1 k z hz1
      obtain ⟨V₂, hV₂, hzV₂, hsub₂⟩ := h₂.1 k z hz2
      exact ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨hzV₁, hzV₂⟩, fun w ⟨h1, h2⟩ => ⟨hsub₁ w h1, hsub₂ w h2⟩⟩
    · intro ⟨hnone1, hnone2⟩
      obtain ⟨N₁, hN₁⟩ := h₁.2 hnone1
      obtain ⟨N₂, hN₂⟩ := h₂.2 hnone2
      refine ⟨max N₁ N₂, fun k hk => ?_⟩
      obtain ⟨V₁, hV₁, hzV₁, hsub₁⟩ := hN₁ k (le_trans (le_max_left N₁ N₂) hk)
      obtain ⟨V₂, hV₂, hzV₂, hsub₂⟩ := hN₂ k (le_trans (le_max_right N₁ N₂) hk)
      exact ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨hzV₁, hzV₂⟩, fun w ⟨h1, h2⟩ => ⟨hsub₁ w h1, hsub₂ w h2⟩⟩
  isOpen_sUnion S hS := by
    refine ⟨?_, ?_⟩
    · intro k z ⟨U, hUS, hzU⟩
      obtain ⟨V, hV, hzV, hsub⟩ := (hS U hUS).1 k z hzU
      exact ⟨V, hV, hzV, fun w hw => ⟨U, hUS, hsub w hw⟩⟩
    · intro ⟨U, hUS, hnoneU⟩
      obtain ⟨N, hN⟩ := (hS U hUS).2 hnoneU
      refine ⟨N, fun k hk => ?_⟩
      obtain ⟨V, hV, hzV, hsub⟩ := hN k hk
      exact ⟨V, hV, hzV, fun w hw => ⟨U, hUS, hsub w hw⟩⟩

/-- Every `boxFanGenW Z n` is clopen and contains `none`. -/
theorem boxFanGen_W_clopen (Z : Type) [TopologicalSpace Z] (z₀ : Z) (n : ℕ) :
    let : TopologicalSpace (BoxFanGen Z) := boxFanGenTopology Z z₀
    IsOpen (boxFanGenW Z n) ∧ IsClosed (boxFanGenW Z n) ∧ (none : BoxFanGen Z) ∈ boxFanGenW Z n := by
  let : TopologicalSpace (BoxFanGen Z) := boxFanGenTopology Z z₀
  refine ⟨⟨fun k _ hk => ⟨univ, isOpen_univ, trivial, fun _ _ => hk⟩,
           fun _ => ⟨n, fun _ hk => ⟨univ, isOpen_univ, trivial, fun _ _ => hk⟩⟩⟩,
          ?_, trivial⟩
  rw [← isOpen_compl_iff]
  exact ⟨fun k _ hk => ⟨univ, isOpen_univ, trivial, fun _ _ => hk⟩, fun h => absurd trivial h⟩

/-- The intersection of `boxFanGenW Z n` over all `n : ℕ` is `{none}`. -/
theorem boxFanGen_W_inter (Z : Type) :
    (⋂ n : ℕ, boxFanGenW Z n) = {(none : BoxFanGen Z)} := by
  ext x
  cases x with
  | none => simp [boxFanGenW]
  | some p =>
    rcases p with ⟨k, z⟩
    simp only [mem_iInter, mem_singleton_iff, reduceCtorEq, iff_false, not_forall]
    exact ⟨k + 1, by simp [boxFanGenW]⟩

/-- The slice embedding `z ↦ some (k, z)` is continuous and open. -/
theorem boxFanGen_slice_isOpen {Z : Type} [TopologicalSpace Z] (z₀ : Z) (k : ℕ)
    {V : Set Z} (hV : IsOpen V) :
    @IsOpen (BoxFanGen Z) (boxFanGenTopology Z z₀) { x | ∃ z ∈ V, x = some (k, z) } := by
  refine ⟨?_, fun ⟨_, _, h⟩ => by cases h⟩
  rintro k' z ⟨z', hz'V, heq⟩
  cases heq
  exact ⟨V, hV, hz'V, fun w hw => ⟨w, hw, rfl⟩⟩

/-- If `F` is closed in `BoxFanGen Z`, every slice `{ z : Z | some (k, z) ∈ F }` is closed in `Z`. -/
theorem boxFanGen_slice_isClosed {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    {F : Set (BoxFanGen Z)} (hF : @IsClosed (BoxFanGen Z) (boxFanGenTopology Z z₀) F) (k : ℕ) :
    IsClosed { z : Z | some (k, z) ∈ F } := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  have hopen : @IsOpen (BoxFanGen Z) (boxFanGenTopology Z z₀) Fᶜ :=
    (@isOpen_compl_iff (BoxFanGen Z) F (boxFanGenTopology Z z₀)).mpr hF
  obtain ⟨V, hVopen, hzV, hVsub⟩ := hopen.1 k z hz
  exact ⟨V, fun w hw hwF => hVsub w hw hwF, hVopen, hzV⟩

/-- `BoxFanGen Z` is `T1Space` whenever `Z` is `T1Space`. -/
theorem boxFanGen_t1Space {Z : Type} [TopologicalSpace Z] [T1Space Z] (z₀ : Z) :
    @T1Space (BoxFanGen Z) (boxFanGenTopology Z z₀) := by
  let : TopologicalSpace (BoxFanGen Z) := boxFanGenTopology Z z₀
  refine ⟨fun x => ?_⟩
  rw [← isOpen_compl_iff]
  cases x with
  | none =>
    exact ⟨fun k z _ => ⟨univ, isOpen_univ, trivial, fun _ _ h => by cases h⟩,
           fun h => absurd rfl h⟩
  | some p =>
    rcases p with ⟨k₀, z₁⟩
    refine ⟨?_, ?_⟩
    · intro k z hne
      by_cases hk : k = k₀
      · subst hk
        have hzne : z ≠ z₁ := fun h => hne (by simp [h])
        refine ⟨{z₁}ᶜ, isClosed_singleton.isOpen_compl, hzne, fun w hw heq => ?_⟩
        cases heq
        exact hw rfl
      · refine ⟨univ, isOpen_univ, trivial, fun w _ heq => ?_⟩
        cases heq
        exact hk rfl
    · intro _
      refine ⟨k₀ + 1, fun k hk => ⟨univ, isOpen_univ, trivial, fun w _ heq => ?_⟩⟩
      cases heq
      omega

end BoxFanGenDef

section Stratifiability

/-- **Key Theorem 1:** If `Z` is stratifiable, then `BoxFanGen Z` is stratifiable
for ANY choice of basepoint `z₀ : Z`. -/
theorem boxFanGen_isStratifiable {Z : Type} [TopologicalSpace Z]
    (hStrat : MSpace.IsStratifiable Z) (z₀ : Z) :
    @MSpace.IsStratifiable (BoxFanGen Z) (boxFanGenTopology Z z₀) := by
  classical
  have hT1Z : T1Space Z := hStrat.1
  obtain ⟨G₀, hG₀_open, hG₀_sub, hG₀_inter, hG₀_mono⟩ := hStrat.2
  -- Decreasing stratification `G' n H := ⋂ j ≤ n, G₀ j H` on `Z`
  let G' : ℕ → Set Z → Set Z := fun n H => ⋂ j ∈ Set.Iic n, G₀ j H
  have hG'_open : ∀ n H, IsClosed H → IsOpen (G' n H) := fun n H hH =>
    (Set.finite_Iic n).isOpen_biInter fun j _ => hG₀_open j H hH
  have hG'_sub : ∀ n H, IsClosed H → H ⊆ G' n H := fun n H hH x hx =>
    mem_iInter₂.mpr fun j _ => hG₀_sub j H hH hx
  have hG'_anti : ∀ {m n : ℕ}, m ≤ n → ∀ H, G' n H ⊆ G' m H := fun hmn H x hx =>
    mem_iInter₂.mpr fun j hj => mem_iInter₂.mp hx j (le_trans hj hmn)
  have hG'_mono : ∀ n H K, IsClosed H → IsClosed K → H ⊆ K → G' n H ⊆ G' n K :=
    fun n H K hH hK hHK x hx =>
      mem_iInter₂.mpr fun j hj => hG₀_mono j H K hH hK hHK (mem_iInter₂.mp hx j hj)
  have hG'_inter : ∀ H, IsClosed H → (⋂ n, closure (G' n H)) = H := by
    intro H hH
    apply Subset.antisymm
    · intro x hx
      rw [← hG₀_inter H hH]
      refine mem_iInter.mpr fun n => ?_
      have hsub : G' n H ⊆ G₀ n H := fun y hy => mem_iInter₂.mp hy n (Set.mem_Iic.mpr le_rfl)
      exact closure_mono hsub (mem_iInter.mp hx n)
    · exact subset_iInter fun n => (hG'_sub n H hH).trans subset_closure
  -- Heath–Lutzer–Zenor monotone normality operator on closed sets of `Z`
  let HZ : Set Z → Set Z → Set Z := fun A B => ⋃ n : ℕ, G' n A \ closure (G' n B)
  have hHZ_open : ∀ A B, IsClosed A → IsOpen (HZ A B) := fun A B hA =>
    isOpen_iUnion fun n => (hG'_open n A hA).sdiff isClosed_closure
  have hHZ_sub : ∀ A B, IsClosed A → IsClosed B → Disjoint A B → A ⊆ HZ A B := by
    intro A B hA hB hdisj x hxA
    have hxB : x ∉ B := Set.disjoint_left.mp hdisj hxA
    have hxnot : x ∉ ⋂ n, closure (G' n B) := by rw [hG'_inter B hB]; exact hxB
    rw [mem_iInter] at hxnot
    push Not at hxnot
    obtain ⟨n, hn⟩ := hxnot
    exact mem_iUnion.mpr ⟨n, hG'_sub n A hA hxA, hn⟩
  have hHZ_disj : ∀ A B, Disjoint (HZ A B) (HZ B A) := by
    intro A B
    rw [Set.disjoint_left]
    intro x hxAB hxBA
    obtain ⟨n, hnA, hnB⟩ := mem_iUnion.mp hxAB
    obtain ⟨m, hmB, hmA⟩ := mem_iUnion.mp hxBA
    rcases le_total n m with hnm | hmn
    · exact hnB (subset_closure (hG'_anti hnm B hmB))
    · exact hmA (subset_closure (hG'_anti hmn A hnA))
  have hHZ_mono : ∀ A₁ A₂ B, IsClosed A₁ → IsClosed A₂ → A₁ ⊆ A₂ → HZ A₁ B ⊆ HZ A₂ B := by
    intro A₁ A₂ B hA₁ hA₂ h12 x hx
    obtain ⟨n, hn1, hnB⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, hG'_mono n A₁ A₂ hA₁ hA₂ h12 hn1, hnB⟩
  -- Build the stratification `G` on `BoxFanGen Z`
  let : TopologicalSpace (BoxFanGen Z) := boxFanGenTopology Z z₀
  have hT1 : T1Space (BoxFanGen Z) := boxFanGen_t1Space z₀
  let slice : Set (BoxFanGen Z) → ℕ → Set Z := fun F k => { z : Z | some (k, z) ∈ F }
  let sliceG : ℕ → Set (BoxFanGen Z) → ℕ → Set Z := fun n F k =>
    if none ∈ F then
      if k < n then G' n (slice F k) else G' n (slice F k ∪ {z₀})
    else
      if z₀ ∈ slice F k then G' n (slice F k) else G' n (slice F k) ∩ HZ (slice F k) {z₀}
  let G : ℕ → Set (BoxFanGen Z) → Set (BoxFanGen Z) := fun n F =>
    { x | match x with
          | none => none ∈ F
          | some (k, z) => z ∈ sliceG n F k }
  have hsliceG_open : ∀ n F, IsClosed F → ∀ k, IsOpen (sliceG n F k) := by
    intro n F hF k
    have hFk : IsClosed (slice F k) := boxFanGen_slice_isClosed z₀ hF k
    dsimp only [sliceG]
    split_ifs
    · exact hG'_open n _ hFk
    · exact hG'_open n _ (hFk.union isClosed_singleton)
    · exact hG'_open n _ hFk
    · exact (hG'_open n _ hFk).inter (hHZ_open _ _ hFk)
  refine ⟨hT1, G, ?_, ?_, ?_, ?_⟩
  · -- Openness of `G n F`
    intro n F hF
    refine ⟨fun k z hz => ⟨sliceG n F k, hsliceG_open n F hF k, hz, fun _ hw => hw⟩, ?_⟩
    intro hnone
    have hnoneF : none ∈ F := hnone
    refine ⟨n, fun k hk => ⟨sliceG n F k, hsliceG_open n F hF k, ?_, fun _ hw => hw⟩⟩
    have hFk : IsClosed (slice F k) := boxFanGen_slice_isClosed z₀ hF k
    dsimp only [sliceG]
    have hnotlt : ¬ k < n := not_lt.mpr hk
    simp only [hnoneF, ↓reduceIte, hnotlt]
    exact hG'_sub n _ (hFk.union isClosed_singleton) (Or.inr rfl)
  · -- `F ⊆ G n F`
    intro n F hF x hxF
    cases x with
    | none => exact hxF
    | some p =>
      rcases p with ⟨k, z⟩
      have hFk : IsClosed (slice F k) := boxFanGen_slice_isClosed z₀ hF k
      change z ∈ sliceG n F k
      dsimp only [sliceG]
      split_ifs with hnone hkn hz₀
      · exact hG'_sub n _ hFk hxF
      · exact hG'_sub n _ (hFk.union isClosed_singleton) (Or.inl hxF)
      · exact hG'_sub n _ hFk hxF
      · refine ⟨hG'_sub n _ hFk hxF, hHZ_sub _ _ hFk isClosed_singleton ?_ hxF⟩
        exact Set.disjoint_singleton_right.mpr hz₀
  · -- `⋂ n, closure (G n F) = F`
    intro F hF
    apply Subset.antisymm
    · intro x hx
      by_contra hxF
      cases x with
      | none =>
        have hopen : IsOpen Fᶜ := hF.isOpen_compl
        obtain ⟨N, hN⟩ := hopen.2 hxF
        have hW_ex : ∀ k, N ≤ k → ∃ W : Set Z, IsOpen W ∧ z₀ ∈ W ∧ Disjoint W (sliceG 0 F k) := by
          intro k hk
          obtain ⟨V, hVopen, hz₀V, hVsub⟩ := hN k hk
          have hz₀_not : z₀ ∉ slice F k := fun h => hVsub z₀ hz₀V h
          have hFk : IsClosed (slice F k) := boxFanGen_slice_isClosed z₀ hF k
          refine ⟨HZ {z₀} (slice F k), hHZ_open _ _ isClosed_singleton,
            hHZ_sub _ _ isClosed_singleton hFk (Set.disjoint_singleton_left.mpr hz₀_not) rfl, ?_⟩
          dsimp only [sliceG]
          simp only [hxF, ↓reduceIte, hz₀_not]
          exact (hHZ_disj {z₀} (slice F k)).mono_right inter_subset_right
        let O : Set (BoxFanGen Z) :=
          { y | match y with
                | none => True
                | some (k, w) => ∃ hk : N ≤ k, w ∈ Classical.choose (hW_ex k hk) }
        have hO_open : IsOpen O := by
          refine ⟨?_, fun _ => ⟨N, fun k hk => ?_⟩⟩
          · rintro k w ⟨hk, hw⟩
            have hspec := Classical.choose_spec (hW_ex k hk)
            exact ⟨Classical.choose (hW_ex k hk), hspec.1, hw, fun u hu => ⟨hk, hu⟩⟩
          · have hspec := Classical.choose_spec (hW_ex k hk)
            exact ⟨Classical.choose (hW_ex k hk), hspec.1, hspec.2.1, fun u hu => ⟨hk, hu⟩⟩
        have hx0 : (none : BoxFanGen Z) ∈ closure (G 0 F) := mem_iInter.mp hx 0
        rw [mem_closure_iff] at hx0
        obtain ⟨y, hyO, hyG⟩ := hx0 O hO_open trivial
        cases y with
        | none => exact hxF hyG
        | some p =>
          rcases p with ⟨k, w⟩
          obtain ⟨hk, hw⟩ := hyO
          exact Set.disjoint_left.mp (Classical.choose_spec (hW_ex k hk)).2.2 hw hyG
      | some p =>
        rcases p with ⟨k, z⟩
        have hFk : IsClosed (slice F k) := boxFanGen_slice_isClosed z₀ hF k
        have hznot : z ∉ ⋂ n, closure (G' n (slice F k)) := by
          rw [hG'_inter _ hFk]; exact hxF
        rw [mem_iInter] at hznot
        push Not at hznot
        obtain ⟨m, hm⟩ := hznot
        let n : ℕ := max m (k + 1)
        have hxn : some (k, z) ∈ closure (G n F) := mem_iInter.mp hx n
        have hslice_sub : sliceG n F k ⊆ G' m (slice F k) := by
          dsimp only [sliceG]
          have hkn : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right m (k + 1))
          have hmn : m ≤ n := le_max_left m (k + 1)
          simp only [hkn, ↓reduceIte]
          split_ifs
          · exact hG'_anti hmn _
          · exact hG'_anti hmn _
          · exact inter_subset_left.trans (hG'_anti hmn _)
        rw [mem_closure_iff] at hm
        push Not at hm
        obtain ⟨V, hVopen, hzV, hVdisj⟩ := hm
        have hO_open : IsOpen { y : BoxFanGen Z | ∃ w ∈ V, y = some (k, w) } :=
          boxFanGen_slice_isOpen z₀ k hVopen
        rw [mem_closure_iff] at hxn
        obtain ⟨y, ⟨w, hwV, rfl⟩, hwG⟩ := hxn _ hO_open ⟨z, hzV, rfl⟩
        have hmem : w ∈ V ∩ G' m (slice F k) := ⟨hwV, hslice_sub hwG⟩
        rw [hVdisj] at hmem
        exact hmem
    · refine subset_iInter fun n x hxF => subset_closure ?_
      cases x with
      | none => exact hxF
      | some p =>
        rcases p with ⟨k, z⟩
        have hFk : IsClosed (slice F k) := boxFanGen_slice_isClosed z₀ hF k
        change z ∈ sliceG n F k
        dsimp only [sliceG]
        split_ifs with hnone hkn hz₀
        · exact hG'_sub n _ hFk hxF
        · exact hG'_sub n _ (hFk.union isClosed_singleton) (Or.inl hxF)
        · exact hG'_sub n _ hFk hxF
        · refine ⟨hG'_sub n _ hFk hxF, hHZ_sub _ _ hFk isClosed_singleton ?_ hxF⟩
          exact Set.disjoint_singleton_right.mpr hz₀
  · -- Monotonicity `F ⊆ K → G n F ⊆ G n K`
    intro n F K hF hK hFK x hx
    cases x with
    | none => exact hFK hx
    | some p =>
      rcases p with ⟨k, z⟩
      have hFk : IsClosed (slice F k) := boxFanGen_slice_isClosed z₀ hF k
      have hKk : IsClosed (slice K k) := boxFanGen_slice_isClosed z₀ hK k
      have hsubk : slice F k ⊆ slice K k := fun w hw => hFK hw
      change z ∈ sliceG n K k
      change z ∈ sliceG n F k at hx
      dsimp only [sliceG] at hx ⊢
      by_cases hnoneF : none ∈ F
      · have hnoneK : none ∈ K := hFK hnoneF
        simp only [hnoneF, hnoneK, ↓reduceIte] at hx ⊢
        split_ifs at hx ⊢
        · exact hG'_mono n _ _ hFk hKk hsubk hx
        · exact hG'_mono n _ _ (hFk.union isClosed_singleton) (hKk.union isClosed_singleton)
            (union_subset_union_left _ hsubk) hx
      · simp only [hnoneF, ↓reduceIte] at hx
        have hG'F : z ∈ G' n (slice F k) := by
          split_ifs at hx
          · exact hx
          · exact hx.1
        by_cases hnoneK : none ∈ K
        · simp only [hnoneK, ↓reduceIte]
          split_ifs
          · exact hG'_mono n _ _ hFk hKk hsubk hG'F
          · exact hG'_mono n _ _ hFk (hKk.union isClosed_singleton)
              (hsubk.trans subset_union_left) hG'F
        · simp only [hnoneK, ↓reduceIte]
          by_cases hzK : z₀ ∈ slice K k
          · simp only [hzK, ↓reduceIte]
            exact hG'_mono n _ _ hFk hKk hsubk hG'F
          · have hzF : z₀ ∉ slice F k := fun h => hzK (hsubk h)
            simp only [hzF, ↓reduceIte] at hx
            simp only [hzK, ↓reduceIte]
            exact ⟨hG'_mono n _ _ hFk hKk hsubk hx.1,
                   hHZ_mono _ _ {z₀} hFk hKk hsubk hx.2⟩

end Stratifiability

section OuterBaseEquivalence

/-- **Key Theorem 2:** If `none` has a single-layer CP open outer base in `BoxFanGen Z`,
then `z₀` has a `σ`-CP open local base in `Z`. -/
theorem hasSigmaCPLocalBase_of_boxFanGen_hasCPOuterBase
    {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    (hcp : @Defs.D_0001.HasCPOuterBase (BoxFanGen Z) (boxFanGenTopology Z z₀) none) :
    Defs.D_0010.HasSigmaCPLocalBase z₀ := by
  let : TopologicalSpace (BoxFanGen Z) := boxFanGenTopology Z z₀
  obtain ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩ := hcp
  let slice : ℕ → Set (BoxFanGen Z) → Set Z := fun k V => { z : Z | some (k, z) ∈ V }
  let 𝓑 : ℕ → Set (Set Z) := fun k =>
    { S : Set Z | ∃ V ∈ 𝓥, some (k, z₀) ∈ V ∧ S = slice k V }
  refine ⟨𝓑, ?_, ?_, ?_⟩
  · -- Each member of `𝓑 k` is open in `Z` and contains `z₀`
    rintro k _ ⟨V, hV, hz₀V, rfl⟩
    refine ⟨?_, hz₀V⟩
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨W, hWopen, hzW, hWsub⟩ := (h𝓥_open V hV).1.1 k z hz
    exact ⟨W, hWsub, hWopen, hzW⟩
  · -- Each layer `𝓑 k` is closure-preserving in `Z`
    intro k 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      let 𝓖' : Set (Set (BoxFanGen Z)) := { V ∈ 𝓥 | some (k, z₀) ∈ V ∧ slice k V ∈ 𝓖 }
      have hcl : some (k, z) ∈ closure (⋃₀ 𝓖') := by
        rw [mem_closure_iff]
        intro O hO hzO
        obtain ⟨W, hWopen, hzW, hWsub⟩ := hO.1 k z hzO
        rw [mem_closure_iff] at hz
        obtain ⟨w, hwW, S, hS𝓖, hwS⟩ := hz W hWopen hzW
        obtain ⟨V, hV, hz₀V, rfl⟩ := h𝓖 hS𝓖
        exact ⟨some (k, w), hWsub w hwW, V, ⟨hV, hz₀V, hS𝓖⟩, hwS⟩
      rw [h𝓥_cp 𝓖' (fun V hV => hV.1)] at hcl
      obtain ⟨_, ⟨V, ⟨hV, hz₀V, hVG⟩, rfl⟩, hzclV⟩ := hcl
      refine ⟨closure (slice k V), mem_image_of_mem _ hVG, ?_⟩
      rw [mem_closure_iff]
      intro W hWopen hzW
      rw [mem_closure_iff] at hzclV
      obtain ⟨y, ⟨w, hwW, rfl⟩, hwV⟩ := hzclV _ (boxFanGen_slice_isOpen z₀ k hWopen) ⟨z, hzW, rfl⟩
      exact ⟨w, hwW, hwV⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  · -- `⋃ k, 𝓑 k` is a local base at `z₀` in `Z`
    intro U hU hz₀U
    let U' : Set (BoxFanGen Z) :=
      { x | match x with | none => True | some (_, z) => z ∈ U }
    have hU'_open : IsOpen U' :=
      ⟨fun _ z hz => ⟨U, hU, hz, fun _ hw => hw⟩,
       fun _ => ⟨0, fun _ _ => ⟨U, hU, hz₀U, fun _ hw => hw⟩⟩⟩
    obtain ⟨V, hV, hVU'⟩ := h𝓥_base U' hU'_open trivial
    obtain ⟨N, hN⟩ := (h𝓥_open V hV).1.2 (h𝓥_open V hV).2
    obtain ⟨W, _, hz₀W, hWsub⟩ := hN N le_rfl
    refine ⟨N, slice N V, ⟨V, hV, hWsub z₀ hz₀W, rfl⟩, fun z hz => hVU' hz⟩

/-- **Converse of `R_0010` + `L_0032`:** `Specs.L_0030.stmt → Specs.L_0031.stmt`. -/
theorem L0030_imp_L0031 : Specs.L_0030.stmt → Specs.L_0031.stmt := by
  rintro ⟨Z, tZ, hStrat, z₀, hno⟩
  let : TopologicalSpace Z := tZ
  refine ⟨BoxFanGen Z, boxFanGenTopology Z z₀, boxFanGen_isStratifiable hStrat z₀, none,
    ⟨boxFanGenW Z, boxFanGen_W_clopen Z z₀, boxFanGen_W_inter Z⟩, ?_⟩
  intro hcp
  exact hno (hasSigmaCPLocalBase_of_boxFanGen_hasCPOuterBase z₀ hcp)

/-- **Exact Equivalence Theorem:** `Specs.L_0030.stmt ↔ Specs.L_0031.stmt`. -/
theorem L0030_iff_L0031 : Specs.L_0030.stmt ↔ Specs.L_0031.stmt :=
  ⟨L0030_imp_L0031, fun h => Proofs.R_0010.main h Proofs.L_0032.main⟩

/-- **Key Theorem 3 (Diagonalization Upgrade):**
If `none` has a single-layer CP open outer base in `BoxFanGen Z`, then `z₀` ALREADY
has a single-layer CP open outer base in `Z` (not merely a `σ`-CP local base!). -/
theorem hasCPOuterBase_of_boxFanGen_hasCPOuterBase
    {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    (hcp : @Defs.D_0001.HasCPOuterBase (BoxFanGen Z) (boxFanGenTopology Z z₀) none) :
    Defs.D_0001.HasCPOuterBase z₀ := by
  let : TopologicalSpace (BoxFanGen Z) := boxFanGenTopology Z z₀
  obtain ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩ := hcp
  let slice : ℕ → Set (BoxFanGen Z) → Set Z := fun k V => { z : Z | some (k, z) ∈ V }
  let 𝓑 : ℕ → Set (Set Z) := fun k =>
    { S : Set Z | ∃ V ∈ 𝓥, some (k, z₀) ∈ V ∧ S = slice k V }
  have h𝓑_open : ∀ k, ∀ S ∈ 𝓑 k, IsOpen S ∧ z₀ ∈ S := by
    rintro k _ ⟨V, hV, hz₀V, rfl⟩
    refine ⟨?_, hz₀V⟩
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨W, hWopen, hzW, hWsub⟩ := (h𝓥_open V hV).1.1 k z hz
    exact ⟨W, hWsub, hWopen, hzW⟩
  have h𝓑_cp : ∀ k, MSpace.ClosurePreserving (𝓑 k) := by
    intro k 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      let 𝓖' : Set (Set (BoxFanGen Z)) := { V ∈ 𝓥 | some (k, z₀) ∈ V ∧ slice k V ∈ 𝓖 }
      have hcl : some (k, z) ∈ closure (⋃₀ 𝓖') := by
        rw [mem_closure_iff]
        intro O hO hzO
        obtain ⟨W, hWopen, hzW, hWsub⟩ := hO.1 k z hzO
        rw [mem_closure_iff] at hz
        obtain ⟨w, hwW, S, hS𝓖, hwS⟩ := hz W hWopen hzW
        obtain ⟨V, hV, hz₀V, rfl⟩ := h𝓖 hS𝓖
        exact ⟨some (k, w), hWsub w hwW, V, ⟨hV, hz₀V, hS𝓖⟩, hwS⟩
      rw [h𝓥_cp 𝓖' (fun V hV => hV.1)] at hcl
      obtain ⟨_, ⟨V, ⟨hV, hz₀V, hVG⟩, rfl⟩, hzclV⟩ := hcl
      refine ⟨closure (slice k V), mem_image_of_mem _ hVG, ?_⟩
      rw [mem_closure_iff]
      intro W hWopen hzW
      rw [mem_closure_iff] at hzclV
      obtain ⟨y, ⟨w, hwW, rfl⟩, hwV⟩ := hzclV _ (boxFanGen_slice_isOpen z₀ k hWopen) ⟨z, hzW, rfl⟩
      exact ⟨w, hwW, hwV⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  by_contra hno
  have hU_ex : ∀ k : ℕ, ∃ U : Set Z, IsOpen U ∧ z₀ ∈ U ∧ ∀ S ∈ 𝓑 k, ¬ S ⊆ U := by
    intro k
    by_contra hall
    push Not at hall
    exact hno ⟨𝓑 k, h𝓑_open k, hall, h𝓑_cp k⟩
  choose U hU_open hz₀U hU_miss using hU_ex
  let UStar : Set (BoxFanGen Z) :=
    { x | match x with | none => True | some (k, z) => z ∈ U k }
  have hUStar_open : IsOpen UStar :=
    ⟨fun k z hz => ⟨U k, hU_open k, hz, fun _ hw => hw⟩,
     fun _ => ⟨0, fun k _ => ⟨U k, hU_open k, hz₀U k, fun _ hw => hw⟩⟩⟩
  obtain ⟨V, hV, hVUStar⟩ := h𝓥_base UStar hUStar_open trivial
  obtain ⟨N, hN⟩ := (h𝓥_open V hV).1.2 (h𝓥_open V hV).2
  obtain ⟨W, _, hz₀W, hWsub⟩ := hN N le_rfl
  exact hU_miss N (slice N V) ⟨V, hV, hWsub z₀ hz₀W, rfl⟩ (fun z hz => hVUStar hz)

/-- Converse direction: if `z₀` has a CP open outer base in `Z`, then `none` has
a CP open outer base in `BoxFanGen Z`. -/
theorem boxFanGen_hasCPOuterBase_of_hasCPOuterBase
    {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    (hcp : Defs.D_0001.HasCPOuterBase z₀) :
    @Defs.D_0001.HasCPOuterBase (BoxFanGen Z) (boxFanGenTopology Z z₀) none := by
  let : TopologicalSpace (BoxFanGen Z) := boxFanGenTopology Z z₀
  obtain ⟨𝓥Z, h𝓥Z_open, h𝓥Z_base, h𝓥Z_cp⟩ := hcp
  let mkBox : ℕ → (ℕ → Set Z) → Set (BoxFanGen Z) := fun N φ =>
    { x | match x with | none => True | some (k, z) => N ≤ k ∧ z ∈ φ k }
  refine ⟨{ S | ∃ N φ, (∀ k, φ k ∈ 𝓥Z) ∧ S = mkBox N φ }, ?_, ?_, ?_⟩
  · rintro _ ⟨N, φ, hφ, rfl⟩
    refine ⟨⟨fun k z ⟨hk, hz⟩ => ⟨φ k, (h𝓥Z_open (φ k) (hφ k)).1, hz, fun _ hw => ⟨hk, hw⟩⟩,
      fun _ => ⟨N, fun k hk => ⟨φ k, (h𝓥Z_open (φ k) (hφ k)).1, (h𝓥Z_open (φ k) (hφ k)).2,
        fun _ hw => ⟨hk, hw⟩⟩⟩⟩, trivial⟩
  · intro U hU hnoneU
    obtain ⟨N, hN⟩ := hU.2 hnoneU
    have hφ_ex : ∀ k : ℕ, ∃ V ∈ 𝓥Z, N ≤ k → ∀ w ∈ V, some (k, w) ∈ U := by
      intro k
      by_cases hk : N ≤ k
      · obtain ⟨W, hWopen, hz₀W, hWsub⟩ := hN k hk
        obtain ⟨V, hV, hVW⟩ := h𝓥Z_base W hWopen hz₀W
        exact ⟨V, hV, fun _ w hw => hWsub w (hVW hw)⟩
      · obtain ⟨V, hV, _⟩ := h𝓥Z_base univ isOpen_univ trivial
        exact ⟨V, hV, fun h => (hk h).elim⟩
    choose φ hφ hφ_sub using hφ_ex
    refine ⟨mkBox N φ, ⟨N, φ, hφ, rfl⟩, fun x hx => ?_⟩
    cases x with
    | none => exact hnoneU
    | some p => exact hφ_sub p.1 hx.1 p.2 hx.2
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro x hx
      cases x with
      | none =>
        rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨S, hS𝓖⟩
        · simp at hx
        · obtain ⟨N, φ, _, rfl⟩ := h𝓖 hS𝓖
          exact ⟨closure (mkBox N φ), mem_image_of_mem _ hS𝓖, subset_closure trivial⟩
      | some p =>
        rcases p with ⟨k, z⟩
        let 𝓖k : Set (Set Z) :=
          { V ∈ 𝓥Z | ∃ N φ, (∀ j, φ j ∈ 𝓥Z) ∧ N ≤ k ∧ φ k = V ∧ mkBox N φ ∈ 𝓖 }
        have hz_cl : z ∈ closure (⋃₀ 𝓖k) := by
          rw [mem_closure_iff]
          intro W hWopen hzW
          rw [mem_closure_iff] at hx
          obtain ⟨y, ⟨w, hwW, rfl⟩, S, hS𝓖, hwS⟩ :=
            hx _ (boxFanGen_slice_isOpen z₀ k hWopen) ⟨z, hzW, rfl⟩
          obtain ⟨N, φ, hφ, rfl⟩ := h𝓖 hS𝓖
          exact ⟨w, hwW, φ k, ⟨hφ k, N, φ, hφ, hwS.1, rfl, hS𝓖⟩, hwS.2⟩
        rw [h𝓥Z_cp 𝓖k (fun V hV => hV.1)] at hz_cl
        obtain ⟨_, ⟨V, ⟨_, N, φ, _, hNk, rfl, hS𝓖⟩, rfl⟩, hzV⟩ := hz_cl
        refine ⟨closure (mkBox N φ), mem_image_of_mem _ hS𝓖, ?_⟩
        rw [mem_closure_iff]
        intro O hO hzO
        obtain ⟨W, hWopen, hzW, hWsub⟩ := hO.1 k z hzO
        rw [mem_closure_iff] at hzV
        obtain ⟨w, hwW, hwφ⟩ := hzV W hWopen hzW
        exact ⟨some (k, w), hWsub w hwW, hNk, hwφ⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Exact pointwise characterization: `HasCPOuterBase none` in `BoxFanGen Z`
is equivalent to `HasCPOuterBase z₀` in `Z`. -/
theorem boxFanGen_hasCPOuterBase_iff
    {Z : Type} [TopologicalSpace Z] (z₀ : Z) :
    @Defs.D_0001.HasCPOuterBase (BoxFanGen Z) (boxFanGenTopology Z z₀) none ↔
      Defs.D_0001.HasCPOuterBase z₀ :=
  ⟨hasCPOuterBase_of_boxFanGen_hasCPOuterBase z₀,
   boxFanGen_hasCPOuterBase_of_hasCPOuterBase z₀⟩

/-- **Bypass of `L_0019` / Mizokami (2004):**
`Specs.L_0020.stmt → Specs.L_0031.stmt` directly via `BoxFanGen`! -/
theorem L0020_imp_L0031 : Specs.L_0020.stmt → Specs.L_0031.stmt := by
  rintro ⟨Z, tZ, hStrat, z₀, hno⟩
  let : TopologicalSpace Z := tZ
  refine ⟨BoxFanGen Z, boxFanGenTopology Z z₀, boxFanGen_isStratifiable hStrat z₀, none,
    ⟨boxFanGenW Z, boxFanGen_W_clopen Z z₀, boxFanGen_W_inter Z⟩, ?_⟩
  intro hcp
  exact hno (hasCPOuterBase_of_boxFanGen_hasCPOuterBase z₀ hcp)

/-- All three counterexample specifications on `origin/main` are logically equivalent:
`Specs.L_0020.stmt ↔ Specs.L_0031.stmt`. -/
theorem L0020_iff_L0031 : Specs.L_0020.stmt ↔ Specs.L_0031.stmt :=
  ⟨L0020_imp_L0031, fun ⟨Y, tY, hS, y, _, hno⟩ => ⟨Y, tY, hS, y, hno⟩⟩

/-- `Specs.L_0020.stmt ↔ Specs.L_0030.stmt`. -/
theorem L0020_iff_L0030 : Specs.L_0020.stmt ↔ Specs.L_0030.stmt :=
  L0020_iff_L0031.trans L0030_iff_L0031.symm

/-- **Direct Refutation of `Tinf` from `Specs.L_0020` (no `L_0019` / Mizokami 2004 needed!):** -/
theorem L0020_imp_not_Tinf : Specs.L_0020.stmt → ¬ MSpace.Goals.Tinf_M3_imp_M1 := by
  intro h20
  exact Proofs.R_0009.main Proofs.L_0029.main (L0020_iff_L0030.mp h20) Proofs.L_0004.main

/-- **Contrapositive:** `Tinf` (`M₃ → M₁`) directly implies `Specs.L_0019.stmt`
(every point of every `M₁` space has a CP open outer base), without Mizokami (2004). -/
theorem Tinf_imp_L0019 : MSpace.Goals.Tinf_M3_imp_M1 → Specs.L_0019.stmt := by
  intro hTinf X tX hM1 x
  let : TopologicalSpace X := tX
  by_contra hno
  have hM3 : MSpace.IsM3 X := Proofs.L_0003.main X (Proofs.L_0002.main X hM1)
  have hStrat : MSpace.IsStratifiable X := (Proofs.L_0004.main X).mp hM3
  exact L0020_imp_not_Tinf ⟨X, tX, hStrat, x, hno⟩ hTinf

/-- **Functorial `M₁` Characterization of `BoxFanGen`:**
`BoxFanGen Z` is `M₁` if and only if `Z` is `M₁` AND `z₀` has a CP open outer base in `Z`. -/
theorem boxFanGen_isM1_iff {Z : Type} [TopologicalSpace Z] (z₀ : Z) :
    @MSpace.IsM1 (BoxFanGen Z) (boxFanGenTopology Z z₀) ↔
      MSpace.IsM1 Z ∧ Defs.D_0001.HasCPOuterBase z₀ := by
  let : TopologicalSpace (BoxFanGen Z) := boxFanGenTopology Z z₀
  constructor
  · intro hM1
    have hsig : Defs.D_0010.HasSigmaCPLocalBase (none : BoxFanGen Z) :=
      Proofs.L_0029.main (BoxFanGen Z) hM1 none
    have hcp_none : Defs.D_0001.HasCPOuterBase (none : BoxFanGen Z) :=
      Proofs.L_0032.main (BoxFanGen Z) none (boxFanGenW Z) (boxFanGen_W_clopen Z z₀)
        (boxFanGen_W_inter Z) hsig
    have hcp_z₀ : Defs.D_0001.HasCPOuterBase z₀ :=
      hasCPOuterBase_of_boxFanGen_hasCPOuterBase z₀ hcp_none
    -- Extract `T3Space Z` and a `σ`-CP open basis on `Z` from slice `0`
    have hT3BF : T3Space (BoxFanGen Z) := hM1.1
    have hT1Z : T1Space Z := ⟨fun z => by
      have hcl : IsClosed ({some (0, z)} : Set (BoxFanGen Z)) := isClosed_singleton
      have hEq : ({z} : Set Z) = { w : Z | some (0, w) ∈ ({some (0, z)} : Set (BoxFanGen Z)) } := by
        ext w; simp
      rw [hEq]
      exact boxFanGen_slice_isClosed z₀ hcl 0⟩
    have hRegZ : RegularSpace Z := by
      refine RegularSpace.of_exists_mem_nhds_isClosed_subset fun z s hs => ?_
      obtain ⟨U, hUs, hUopen, hzU⟩ := mem_nhds_iff.mp hs
      have hOopen : IsOpen { x : BoxFanGen Z | ∃ w ∈ U, x = some (0, w) } :=
        boxFanGen_slice_isOpen z₀ 0 hUopen
      obtain ⟨T, hTnhds, hTclosed, hTsub⟩ :=
        exists_mem_nhds_isClosed_subset (hOopen.mem_nhds ⟨z, hzU, rfl⟩)
      obtain ⟨O', hO'T, hO'open, hzO'⟩ := mem_nhds_iff.mp hTnhds
      obtain ⟨W, hWopen, hzW, hWsub⟩ := hO'open.1 0 z hzO'
      refine ⟨{ w : Z | some (0, w) ∈ T },
        Filter.mem_of_superset (hWopen.mem_nhds hzW) (fun w hw => hO'T (hWsub w hw)),
        boxFanGen_slice_isClosed z₀ hTclosed 0, ?_⟩
      intro w hw
      obtain ⟨w', hw'U, heq⟩ := hTsub hw
      cases heq
      exact hUs hw'U
    have hT3Z : T3Space Z := ⟨⟩
    obtain ⟨𝓑, h𝓑_bas, 𝓑', h𝓑'_cp, rfl⟩ := hM1.2
    let slice0 : Set (BoxFanGen Z) → Set Z := fun V => { z : Z | some (0, z) ∈ V }
    let 𝓑Z' : ℕ → Set (Set Z) := fun n => slice0 '' 𝓑' n
    refine ⟨⟨hT3Z, ⋃ n, 𝓑Z' n, ?_, ⟨𝓑Z', ?_, rfl⟩⟩, hcp_z₀⟩
    · apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
      · rintro S hS
        obtain ⟨n, B, hBn, rfl⟩ := by simpa [𝓑Z'] using hS
        have hBopen : IsOpen B := h𝓑_bas.isOpen (mem_iUnion.mpr ⟨n, hBn⟩)
        rw [isOpen_iff_forall_mem_open]
        intro z hz
        obtain ⟨W, hWopen, hzW, hWsub⟩ := hBopen.1 0 z hz
        exact ⟨W, hWsub, hWopen, hzW⟩
      · intro z U hzU hUopen
        have hOopen : IsOpen { x : BoxFanGen Z | ∃ w ∈ U, x = some (0, w) } :=
          boxFanGen_slice_isOpen z₀ 0 hUopen
        obtain ⟨B, hB, hzB, hBO⟩ :=
          h𝓑_bas.exists_subset_of_mem_open
            (show some (0, z) ∈ { x : BoxFanGen Z | ∃ w ∈ U, x = some (0, w) } from ⟨z, hzU, rfl⟩)
            hOopen
        obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
        refine ⟨slice0 B, mem_iUnion.mpr ⟨n, B, hBn, rfl⟩, hzB, ?_⟩
        intro w hw
        obtain ⟨w', hw'U, heq⟩ := hBO hw
        cases heq
        exact hw'U
    · intro n 𝓖 h𝓖
      apply Subset.antisymm
      · intro z hz
        let 𝓖' : Set (Set (BoxFanGen Z)) := { B ∈ 𝓑' n | slice0 B ∈ 𝓖 }
        have hcl : some (0, z) ∈ closure (⋃₀ 𝓖') := by
          rw [mem_closure_iff]
          intro O hO hzO
          obtain ⟨W, hWopen, hzW, hWsub⟩ := hO.1 0 z hzO
          rw [mem_closure_iff] at hz
          obtain ⟨w, hwW, S, hS𝓖, hwS⟩ := hz W hWopen hzW
          obtain ⟨B, hBn, rfl⟩ := h𝓖 hS𝓖
          exact ⟨some (0, w), hWsub w hwW, B, ⟨hBn, hS𝓖⟩, hwS⟩
        rw [h𝓑'_cp n 𝓖' (fun B hB => hB.1)] at hcl
        obtain ⟨_, ⟨B, ⟨_, hBG⟩, rfl⟩, hzclB⟩ := hcl
        refine ⟨closure (slice0 B), mem_image_of_mem _ hBG, ?_⟩
        rw [mem_closure_iff]
        intro W hWopen hzW
        rw [mem_closure_iff] at hzclB
        obtain ⟨y, ⟨w, hwW, rfl⟩, hwB⟩ := hzclB _ (boxFanGen_slice_isOpen z₀ 0 hWopen) ⟨z, hzW, rfl⟩
        exact ⟨w, hwW, hwB⟩
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  · rintro ⟨hM1Z, hcp_z₀⟩
    have hM3Z : MSpace.IsM3 Z := Proofs.L_0003.main Z (Proofs.L_0002.main Z hM1Z)
    have hStratZ : MSpace.IsStratifiable Z := (Proofs.L_0004.main Z).mp hM3Z
    have hStratBF : MSpace.IsStratifiable (BoxFanGen Z) := boxFanGen_isStratifiable hStratZ z₀
    have hT3BF : T3Space (BoxFanGen Z) := ((Proofs.L_0004.main (BoxFanGen Z)).mpr hStratBF).1
    obtain ⟨𝓥none, h𝓥_open, h𝓥_base, h𝓥_cp⟩ :=
      boxFanGen_hasCPOuterBase_of_hasCPOuterBase z₀ hcp_z₀
    obtain ⟨𝓑Z, h𝓑Z_bas, 𝓑Z', h𝓑Z'_cp, rfl⟩ := hM1Z.2
    let embed : ℕ → Set Z → Set (BoxFanGen Z) := fun k B => { x | ∃ z ∈ B, x = some (k, z) }
    let 𝓑' : ℕ → Set (Set (BoxFanGen Z)) := fun n =>
      match n with
      | 0 => 𝓥none
      | m + 1 => embed (Nat.unpair m).1 '' 𝓑Z' (Nat.unpair m).2
    refine ⟨hT3BF, ⋃ n, 𝓑' n, ?_, ⟨𝓑', ?_, rfl⟩⟩
    · apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
      · rintro S hS
        obtain ⟨n, hSn⟩ := mem_iUnion.mp hS
        cases n with
        | zero => exact (h𝓥_open S hSn).1
        | succ m =>
          obtain ⟨B, hB, rfl⟩ := hSn
          exact boxFanGen_slice_isOpen z₀ (Nat.unpair m).1
            (h𝓑Z_bas.isOpen (mem_iUnion.mpr ⟨(Nat.unpair m).2, hB⟩))
      · intro x U hxU hUopen
        cases x with
        | none =>
          obtain ⟨V, hV, hVU⟩ := h𝓥_base U hUopen hxU
          exact ⟨V, mem_iUnion.mpr ⟨0, hV⟩, (h𝓥_open V hV).2, hVU⟩
        | some p =>
          rcases p with ⟨k, z⟩
          obtain ⟨W, hWopen, hzW, hWsub⟩ := hUopen.1 k z hxU
          obtain ⟨B, hB, hzB, hBW⟩ := h𝓑Z_bas.exists_subset_of_mem_open hzW hWopen
          obtain ⟨b, hBb⟩ := mem_iUnion.mp hB
          refine ⟨embed k B, mem_iUnion.mpr ⟨Nat.pair k b + 1, ?_⟩, ⟨z, hzB, rfl⟩, ?_⟩
          · dsimp only [𝓑']
            rw [Nat.unpair_pair]
            exact ⟨B, hBb, rfl⟩
          · rintro _ ⟨w, hwB, rfl⟩
            exact hWsub w (hBW hwB)
    · intro n
      cases n with
      | zero => exact h𝓥_cp
      | succ m =>
        intro 𝓖 h𝓖
        apply Subset.antisymm
        · intro x hx
          have hslice_closed : IsClosed { y : BoxFanGen Z | ∃ z : Z, y = some ((Nat.unpair m).1, z) } := by
            rw [← isOpen_compl_iff]
            refine ⟨?_, ?_⟩
            · intro k z hnot
              have hne : k ≠ (Nat.unpair m).1 := fun h => hnot ⟨z, by simp [h]⟩
              exact ⟨univ, isOpen_univ, trivial, fun w _ ⟨w', heq⟩ => by cases heq; exact hne rfl⟩
            · intro _
              refine ⟨(Nat.unpair m).1 + 1, fun k hk =>
                ⟨univ, isOpen_univ, trivial, fun w _ ⟨w', heq⟩ => by cases heq; omega⟩⟩
          have hsub_slice : ⋃₀ 𝓖 ⊆ { y : BoxFanGen Z | ∃ z : Z, y = some ((Nat.unpair m).1, z) } := by
            rintro y ⟨S, hS𝓖, hyS⟩
            obtain ⟨B, _, rfl⟩ := h𝓖 hS𝓖
            obtain ⟨z, _, rfl⟩ := hyS
            exact ⟨z, rfl⟩
          obtain ⟨z, rfl⟩ := hslice_closed.closure_subset (closure_mono hsub_slice hx)
          let 𝓖Z : Set (Set Z) := { B ∈ 𝓑Z' (Nat.unpair m).2 | embed (Nat.unpair m).1 B ∈ 𝓖 }
          have hz_cl : z ∈ closure (⋃₀ 𝓖Z) := by
            rw [mem_closure_iff]
            intro W hWopen hzW
            rw [mem_closure_iff] at hx
            obtain ⟨y, ⟨w, hwW, rfl⟩, S, hS𝓖, hwS⟩ :=
              hx _ (boxFanGen_slice_isOpen z₀ (Nat.unpair m).1 hWopen) ⟨z, hzW, rfl⟩
            obtain ⟨B, hBb, rfl⟩ := h𝓖 hS𝓖
            obtain ⟨w', hw'B, heq⟩ := hwS
            cases heq
            exact ⟨w, hwW, B, ⟨hBb, hS𝓖⟩, hw'B⟩
          rw [h𝓑Z'_cp (Nat.unpair m).2 𝓖Z (fun B hB => hB.1)] at hz_cl
          obtain ⟨_, ⟨B, ⟨_, hBG⟩, rfl⟩, hzB⟩ := hz_cl
          refine ⟨closure (embed (Nat.unpair m).1 B), mem_image_of_mem _ hBG, ?_⟩
          rw [mem_closure_iff]
          intro O hO hzO
          obtain ⟨W, hWopen, hzW, hWsub⟩ := hO.1 (Nat.unpair m).1 z hzO
          rw [mem_closure_iff] at hzB
          obtain ⟨w, hwW, hwB⟩ := hzB W hWopen hzW
          exact ⟨some ((Nat.unpair m).1, w), hWsub w hwW, w, hwB, rfl⟩
        · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

end OuterBaseEquivalence

end Research.ChenWangBoxFanEquiv
