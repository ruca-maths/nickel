import Mathlib.Topology.Closure
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.LocallyFinite
import Mathlib.Data.Set.Finite.Basic
import Targets

namespace Work.L0028Helpers

open Set TopologicalSpace Filter

lemma regularClosed_closure_of_isOpen {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsOpen U) : IsClosed (closure U) ∧ closure (interior (closure U)) = closure U := by
  refine ⟨isClosed_closure, Subset.antisymm ?_ ?_⟩
  · exact closure_minimal interior_subset isClosed_closure
  · exact closure_mono (interior_maximal subset_closure hU)

lemma exists_regularClosed_cp_nhds_of_isOpen_singleton {X : Type*} [TopologicalSpace X]
    [T1Space X] {x : X} (hxOpen : IsOpen ({x} : Set X)) :
    ∃ 𝓚' : Set (Set X),
      (∀ K ∈ 𝓚', IsClosed K ∧ closure (interior K) = K ∧ x ∈ interior K) ∧
      (∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚', K ⊆ U) ∧
      MSpace.ClosurePreserving 𝓚' := by
  refine ⟨{{x}}, ?_, ?_, ?_⟩
  · intro K hK
    rcases mem_singleton_iff.1 hK with rfl
    refine ⟨isClosed_singleton, ?_, ?_⟩
    · rw [hxOpen.interior_eq, isClosed_singleton.closure_eq]
    · rw [hxOpen.interior_eq]; exact mem_singleton x
  · intro U _ hxU
    exact ⟨{x}, mem_singleton {x}, singleton_subset_iff.2 hxU⟩
  · intro 𝓖 h𝓖
    rcases (subset_singleton_iff_eq.1 h𝓖) with h | h <;> subst h <;> simp

lemma sigma_closed_discrete_dense_diff_singleton {X : Type*} [TopologicalSpace X] [T1Space X]
    {D : ℕ → Set X} (hDisc : ∀ n, ∀ A ⊆ D n, IsClosed A) (hDense : Dense (⋃ n, D n))
    {x : X} (hxNotOpen : ¬ IsOpen ({x} : Set X)) :
    (∀ n, ∀ A ⊆ D n \ {x}, IsClosed A) ∧ Dense (⋃ n, D n \ {x}) := by
  refine ⟨fun n A hA => hDisc n A (hA.trans sdiff_subset), ?_⟩
  have h : (⋃ n, D n \ {x}) = (⋃ n, D n) \ {x} := by
    ext y; simp only [mem_iUnion, Set.mem_sdiff]; tauto
  rw [h]
  have : (nhdsWithin x {x}ᶜ).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot,
      (dense_compl_singleton_iff_not_open.2 hxNotOpen).closure_eq]
    exact mem_univ x
  exact hDense.sdiff_singleton x

open Classical in
theorem discrete_open_expansion
    {X : Type} [TopologicalSpace X] [T3Space X] [ParacompactSpace X]
    (D : Set X) (hD : ∀ A ⊆ D, IsClosed A) :
    ∃ U : X → Set X, (∀ d ∈ D, IsOpen (U d) ∧ d ∈ U d) ∧
      (∀ x : X, ∃ N ∈ nhds x, {d | d ∈ D ∧ (U d ∩ N).Nonempty}.Subsingleton) := by
  let O : X → Set X := fun x => (D \ {x})ᶜ
  have hOopen : ∀ x, IsOpen (O x) := fun x => (hD (D \ {x}) sdiff_subset).isOpen_compl
  have hxO : ∀ x, x ∈ O x := fun x hx => hx.2 (mem_singleton x)
  have hOsub : ∀ x, (O x ∩ D).Subsingleton := by
    intro x y hy z hz
    have hyx : y = x := by by_contra hne; exact hy.1 ⟨hy.2, hne⟩
    have hzx : z = x := by by_contra hne; exact hz.1 ⟨hz.2, hne⟩
    rw [hyx, hzx]
  have hReg : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ closure W ⊆ O x := by
    intro x
    obtain ⟨F, ⟨hFx, hFclosed⟩, hFO⟩ :=
      (closed_nhds_basis x).mem_iff.1 ((hOopen x).mem_nhds (hxO x))
    exact ⟨interior F, isOpen_interior, mem_interior_iff_mem_nhds.2 hFx,
      (closure_minimal interior_subset hFclosed).trans hFO⟩
  choose W hWopen hxW hWcl using hReg
  have hWcover : (⋃ x : X, W x) = univ := eq_univ_iff_forall.2 (fun x => mem_iUnion.2 ⟨x, hxW x⟩)
  obtain ⟨β, V, hVopen, hVcover, hVlf, hVref⟩ :=
    ParacompactSpace.locallyFinite_refinement X W hWopen hWcover
  have hVcl_lf : LocallyFinite (fun b : β => closure (V b)) := hVlf.closure
  have hVcl_sub : ∀ b : β, (closure (V b) ∩ D).Subsingleton := by
    intro b
    obtain ⟨a, ha⟩ := hVref b
    exact (hOsub a).anti (inter_subset_inter_left D ((closure_mono ha).trans (hWcl a)))
  let U : X → Set X := fun d => (⋃ b : β, if d ∉ closure (V b) then closure (V b) else ∅)ᶜ
  refine ⟨U, ?_, ?_⟩
  · intro d _
    refine ⟨?_, ?_⟩
    · rw [isOpen_compl_iff]
      apply LocallyFinite.isClosed_iUnion
      · intro x
        obtain ⟨M, hM, hFin⟩ := hVcl_lf x
        refine ⟨M, hM, hFin.subset ?_⟩
        intro b ⟨y, hy1, hy2⟩
        by_cases hd : d ∈ closure (V b)
        · simp [hd] at hy1
        · simp [hd] at hy1; exact ⟨y, hy1, hy2⟩
      · intro b
        by_cases hd : d ∈ closure (V b)
        · simp [hd]
        · simp [hd, isClosed_closure]
    · intro hdU
      rcases mem_iUnion.1 hdU with ⟨b, hdb⟩
      by_cases hd : d ∈ closure (V b)
      · simp [hd] at hdb
      · simp [hd] at hdb
  · intro x
    have hxUniv : x ∈ (⋃ b : β, V b) := by rw [hVcover]; trivial
    rcases mem_iUnion.1 hxUniv with ⟨b₀, hxb₀⟩
    refine ⟨V b₀, (hVopen b₀).mem_nhds hxb₀, (hVcl_sub b₀).anti ?_⟩
    intro d ⟨hdD, y, hyU, hyV⟩
    refine ⟨?_, hdD⟩
    by_contra hnot
    apply hyU
    refine mem_iUnion.2 ⟨b₀, ?_⟩
    simp [hnot]
    exact subset_closure hyV

/-- 補題 L_0028a-2 (青): x の CP 開近傍基から正則閉 CP 閉近傍基を得る。 -/
lemma regularClosed_cp_nhds_of_open_cp_base {X : Type*} [TopologicalSpace X] [T3Space X]
    {x : X} {𝓞 : Set (Set X)}
    (hopen : ∀ O ∈ 𝓞, IsOpen O ∧ x ∈ O)
    (hbase : ∀ U : Set X, IsOpen U → x ∈ U → ∃ O ∈ 𝓞, O ⊆ U)
    (hcp : MSpace.ClosurePreserving 𝓞) :
    ∃ 𝓚' : Set (Set X),
      (∀ K ∈ 𝓚', IsClosed K ∧ closure (interior K) = K ∧ x ∈ interior K) ∧
      (∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚', K ⊆ U) ∧
      MSpace.ClosurePreserving 𝓚' := by
  refine ⟨closure '' 𝓞, ?_, ?_, ?_⟩
  · rintro K ⟨O, hO, rfl⟩
    obtain ⟨hO_open, hxO⟩ := hopen O hO
    refine ⟨isClosed_closure, (regularClosed_closure_of_isOpen hO_open).2, ?_⟩
    exact interior_maximal subset_closure hO_open hxO
  · intro U hU hxU
    obtain ⟨F, ⟨hF_nhds, hF_closed⟩, hFU⟩ := (closed_nhds_basis x).mem_iff.1 (hU.mem_nhds hxU)
    have hV_open : IsOpen (interior F) := isOpen_interior
    have hxV : x ∈ interior F := mem_interior_iff_mem_nhds.mpr hF_nhds
    have hVcl : closure (interior F) ⊆ U := (closure_minimal interior_subset hF_closed).trans hFU
    obtain ⟨O, hO, hOV⟩ := hbase (interior F) hV_open hxV
    exact ⟨closure O, ⟨O, hO, rfl⟩, (closure_mono hOV).trans hVcl⟩
  · intro 𝓖 h𝓖
    let 𝓖₀ : Set (Set X) := {O ∈ 𝓞 | closure O ∈ 𝓖}
    have h𝓖₀_sub : 𝓖₀ ⊆ 𝓞 := fun _ h => h.1
    have h𝓖_eq : 𝓖 = closure '' 𝓖₀ := by
      ext K
      constructor
      · intro hK
        obtain ⟨O, hO, rfl⟩ := h𝓖 hK
        exact ⟨O, ⟨hO, hK⟩, rfl⟩
      · rintro ⟨O, ⟨_, hcl⟩, rfl⟩
        exact hcl
    have hcl_eq : closure (⋃₀ 𝓖) = closure (⋃₀ 𝓖₀) := by
      rw [h𝓖_eq]
      apply Subset.antisymm
      · refine closure_minimal ?_ isClosed_closure
        rintro y ⟨_, ⟨O, hO, rfl⟩, hy⟩
        exact closure_mono (subset_sUnion_of_mem hO) hy
      · refine closure_mono ?_
        rintro y ⟨O, hO, hy⟩
        exact ⟨closure O, ⟨O, hO, rfl⟩, subset_closure hy⟩
    rw [hcl_eq, hcp 𝓖₀ h𝓖₀_sub]
    ext y
    constructor
    · rintro ⟨_, ⟨O, hO, rfl⟩, hy⟩
      refine ⟨closure O, ⟨closure O, hO.2, closure_closure⟩, hy⟩
    · rintro ⟨_, ⟨K, hK, rfl⟩, hy⟩
      rw [h𝓖_eq] at hK
      obtain ⟨O, hO, rfl⟩ := hK
      rw [closure_closure] at hy
      exact ⟨closure O, ⟨O, hO, rfl⟩, hy⟩

/-- 補題 L_0028c (青): CP 族の任意和閉包は再び CP 族である。 -/
lemma closurePreserving_sUnion_closure {X : Type*} [TopologicalSpace X] {𝓕 : Set (Set X)}
    (hcp : MSpace.ClosurePreserving 𝓕) :
    MSpace.ClosurePreserving {S : Set X | ∃ 𝓖 ⊆ 𝓕, S = ⋃₀ 𝓖} := by
  intro 𝓗 h𝓗
  apply Subset.antisymm
  · let 𝓖star : Set (Set X) := {F ∈ 𝓕 | ∃ H ∈ 𝓗, F ⊆ H}
    have hsub_union : ⋃₀ 𝓗 ⊆ ⋃₀ 𝓖star := by
      rintro y ⟨H, hH, hyH⟩
      obtain ⟨𝓖, h𝓖𝓕, hHeq⟩ := h𝓗 hH
      rw [hHeq] at hyH
      obtain ⟨F, hF𝓖, hyF⟩ := hyH
      exact ⟨F, ⟨h𝓖𝓕 hF𝓖, H, hH, hHeq ▸ subset_sUnion_of_mem hF𝓖⟩, hyF⟩
    have hcl_sub : closure (⋃₀ 𝓗) ⊆ ⋃₀ (closure '' 𝓖star) := by
      calc closure (⋃₀ 𝓗) ⊆ closure (⋃₀ 𝓖star) := closure_mono hsub_union
        _ = ⋃₀ (closure '' 𝓖star) := hcp 𝓖star (fun _ h => h.1)
    intro y hy
    obtain ⟨_, ⟨F, ⟨_, H, hH, hFH⟩, rfl⟩, hyF⟩ := hcl_sub hy
    exact ⟨closure H, ⟨H, hH, rfl⟩, closure_mono hFH hyF⟩
  · rintro y ⟨_, ⟨H, hH, rfl⟩, hy⟩
    exact closure_mono (subset_sUnion_of_mem hH) hy

/-- 補題 L_0028b (青): 減少開近傍列 W_n による層別 CP 統合補題。 -/
lemma closurePreserving_iUnion_of_shrinking {X : Type*} [TopologicalSpace X]
    {x : X} {W : ℕ → Set X} {𝓕 : ℕ → Set (Set X)}
    (hsep : ∀ y : X, y ≠ x → ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ ∃ N : ℕ, ∀ n ≥ N, Disjoint V (closure (W n)))
    (hcp : ∀ n, MSpace.ClosurePreserving (𝓕 n))
    (hsub : ∀ n, ∀ F ∈ 𝓕 n, F ⊆ closure (W n) ∧ x ∈ closure F) :
    MSpace.ClosurePreserving (⋃ n, 𝓕 n) := by
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · intro y hy
    by_cases hEmpty : 𝓖 = ∅
    · subst hEmpty; simp at hy
    · by_cases hyx : y = x
      · subst hyx
        obtain ⟨F, hF⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
        obtain ⟨n, hFn⟩ := mem_iUnion.mp (h𝓖 hF)
        exact ⟨closure F, ⟨F, hF, rfl⟩, (hsub n F hFn).2⟩
      · obtain ⟨V, hV_open, hyV, N, hVN⟩ := hsep y hyx
        let 𝓖_lt : Set (Set X) := {F ∈ 𝓖 | ∃ n < N, F ∈ 𝓕 n}
        let 𝓖_ge : Set (Set X) := {F ∈ 𝓖 | ∀ n < N, F ∉ 𝓕 n}
        have hdecomp : ⋃₀ 𝓖 = ⋃₀ 𝓖_lt ∪ ⋃₀ 𝓖_ge := by
          ext z
          simp only [mem_sUnion, mem_union, 𝓖_lt, 𝓖_ge, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨F, hF, hzF⟩
            by_cases h : ∃ n < N, F ∈ 𝓕 n
            · exact Or.inl ⟨F, ⟨hF, h⟩, hzF⟩
            · push Not at h; exact Or.inr ⟨F, ⟨hF, h⟩, hzF⟩
          · rintro (⟨F, ⟨hF, _⟩, hzF⟩ | ⟨F, ⟨hF, _⟩, hzF⟩)
            · exact ⟨F, hF, hzF⟩
            · exact ⟨F, hF, hzF⟩
        rw [hdecomp, closure_union] at hy
        have hnot_ge : y ∉ closure (⋃₀ 𝓖_ge) := by
          intro hy_ge
          rw [mem_closure_iff] at hy_ge
          obtain ⟨z, hzV, ⟨F, ⟨hF, hFnotlt⟩, hzF⟩⟩ := hy_ge V hV_open hyV
          obtain ⟨n, hFn⟩ := mem_iUnion.mp (h𝓖 hF)
          have hn_ge : n ≥ N := by
            by_contra hlt; push Not at hlt; exact hFnotlt n hlt hFn
          have hzW : z ∈ closure (W n) := (hsub n F hFn).1 hzF
          exact (Set.disjoint_left.mp (hVN n hn_ge) hzV) hzW
        have hy_lt : y ∈ closure (⋃₀ 𝓖_lt) := hy.resolve_right hnot_ge
        have hsub_fin : ⋃₀ 𝓖_lt ⊆ ⋃ n ∈ Set.Iio N, ⋃₀ (𝓖 ∩ 𝓕 n) := by
          rintro z ⟨F, ⟨hF, n, hnN, hFn⟩, hzF⟩
          exact mem_biUnion (show n ∈ Set.Iio N from hnN) ⟨F, ⟨hF, hFn⟩, hzF⟩
        have hy_fin : y ∈ closure (⋃ n ∈ Set.Iio N, ⋃₀ (𝓖 ∩ 𝓕 n)) :=
          closure_mono hsub_fin hy_lt
        rw [(Set.finite_Iio N).closure_biUnion] at hy_fin
        obtain ⟨n, _, hy_n⟩ := mem_iUnion₂.mp hy_fin
        rw [hcp n (𝓖 ∩ 𝓕 n) inter_subset_right] at hy_n
        obtain ⟨_, ⟨F, ⟨hF, _⟩, rfl⟩, hyF⟩ := hy_n
        exact ⟨closure F, ⟨F, hF, rfl⟩, hyF⟩
  · rintro y ⟨_, ⟨F, hF, rfl⟩, hy⟩
    exact closure_mono (subset_sUnion_of_mem hF) hy

end Work.L0028Helpers
