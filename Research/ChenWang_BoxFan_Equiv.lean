import Targets
import Defs.D_0001
import Defs.D_0010
import Specs.L_0030
import Specs.L_0031
import Proofs.L_0032
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

end OuterBaseEquivalence

end Research.ChenWangBoxFanEquiv
