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

/-! ### かえる: Mizokami (1985) Lemma 5–6 の正則開細分・帰納法 -/

def IsRegularOpen {X : Type*} [TopologicalSpace X] (U : Set X) : Prop :=
  IsOpen U ∧ interior (closure U) = U

def RegularOpenRefinementStep_stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], MSpace.IsStratifiable X →
    ∀ {α β : Type} (U : α → Set X) (V : β → Set X),
      (∀ a, IsOpen (U a)) →
      (⋃ a, U a) = Set.univ →
      (∀ b, IsOpen (V b)) →
      LocallyFinite V →
      (∀ S : Set β, IsRegularOpen (⋃ b ∈ S, V b)) →
      ∃ (γ : Type) (W : γ → Set X),
        (∀ c, IsOpen (W c)) ∧
        (⋃ c, W c) = Set.univ ∧
        LocallyFinite W ∧
        (∀ c, ∃ a, W c ⊆ U a) ∧
        (∀ (S : Set β) (T : Set γ),
          IsRegularOpen ((⋃ b ∈ S, V b) ∪ (⋃ c ∈ T, W c)))

def RegularOpenDiscreteExpansionSeq_stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], MSpace.IsStratifiable X →
    ∀ (D : ℕ → Set X) (U : ℕ → X → Set X),
      (∀ n, ∀ A ⊆ D n, IsClosed A) →
      (∀ n, ∀ d ∈ D n, IsOpen (U n d) ∧ d ∈ U n d) →
      (∀ n, ∀ x : X, ∃ N ∈ nhds x, {d | d ∈ D n ∧ (U n d ∩ N).Nonempty}.Subsingleton) →
      ∃ V : ℕ → X → Set X,
        (∀ n, ∀ d ∈ D n, IsOpen (V n d) ∧ d ∈ V n d ∧ V n d ⊆ U n d) ∧
        (∀ N : ℕ, ∀ S : (k : Fin (N + 1)) → Set X, (∀ k, S k ⊆ D k.1) →
          IsRegularOpen (⋃ k : Fin (N + 1), ⋃ d ∈ S k, V k.1 d))

theorem isRegularOpen_iUnion_of_locallyFinite_disjoint_frontier
    {X ι : Type*} [TopologicalSpace X] {W : ι → Set X}
    (hW : ∀ i, IsRegularOpen (W i))
    (hlf : LocallyFinite W)
    (hdisj : Pairwise (fun i j => Disjoint (frontier (W i)) (frontier (W j))))
    (S : Set ι) :
    IsRegularOpen (⋃ i ∈ S, W i) := by
  classical
  have hOpen : IsOpen (⋃ i ∈ S, W i) := isOpen_biUnion (fun i _ => (hW i).1)
  refine ⟨hOpen, Subset.antisymm ?_ (interior_maximal subset_closure hOpen)⟩
  have hClSub : closure (⋃ i ∈ S, W i) ⊆ ⋃ i : ι, if i ∈ S then closure (W i) else ∅ := by
    apply closure_minimal
    · intro x hx
      rcases mem_iUnion₂.1 hx with ⟨i, hiS, hxi⟩
      exact mem_iUnion.2 ⟨i, by simp [hiS, subset_closure hxi]⟩
    · have hlf_sub : LocallyFinite (fun i : ι => if i ∈ S then closure (W i) else ∅) := by
        intro x
        obtain ⟨M, hM, hFin⟩ := hlf.closure x
        refine ⟨M, hM, hFin.subset ?_⟩
        intro i ⟨y, hy1, hy2⟩
        by_cases hi : i ∈ S
        · simp [hi] at hy1
          exact ⟨y, hy1, hy2⟩
        · simp [hi] at hy1
      apply hlf_sub.isClosed_iUnion
      intro i
      by_cases hi : i ∈ S
      · simp [hi, isClosed_closure]
      · simp [hi]
  intro p hp
  by_contra hpNot
  have hpCl : p ∈ closure (⋃ i ∈ S, W i) := interior_subset hp
  rcases mem_iUnion.1 (hClSub hpCl) with ⟨i₀, hi₀⟩
  have hi₀S : i₀ ∈ S := by
    by_contra hnot
    simp [hnot] at hi₀
  simp [hi₀S] at hi₀
  have hpFr₀ : p ∈ frontier (W i₀) := by
    refine ⟨hi₀, ?_⟩
    rw [(hW i₀).1.interior_eq]
    intro hpW₀
    exact hpNot (mem_iUnion₂.2 ⟨i₀, hi₀S, hpW₀⟩)
  let C : Set X := ⋃ i : ι, if i ∈ S ∧ i ≠ i₀ then closure (W i) else ∅
  have hCclosed : IsClosed C := by
    have hlf_C : LocallyFinite (fun i : ι => if i ∈ S ∧ i ≠ i₀ then closure (W i) else ∅) := by
      intro x
      obtain ⟨M, hM, hFin⟩ := hlf.closure x
      refine ⟨M, hM, hFin.subset ?_⟩
      intro i ⟨y, hy1, hy2⟩
      by_cases hi : i ∈ S ∧ i ≠ i₀
      · simp [hi] at hy1
        exact ⟨y, hy1, hy2⟩
      · simp [hi] at hy1
    apply hlf_C.isClosed_iUnion
    intro i
    by_cases hi : i ∈ S ∧ i ≠ i₀
    · simp [hi, isClosed_closure]
    · simp [hi]
  have hpNotC : p ∉ C := by
    intro hpC
    rcases mem_iUnion.1 hpC with ⟨i, hi⟩
    by_cases hcond : i ∈ S ∧ i ≠ i₀
    · simp [hcond] at hi
      have hpFri : p ∈ frontier (W i) := by
        refine ⟨hi, ?_⟩
        rw [(hW i).1.interior_eq]
        intro hpWi
        exact hpNot (mem_iUnion₂.2 ⟨i, hcond.1, hpWi⟩)
      exact Set.disjoint_left.1 (hdisj hcond.2) hpFri hpFr₀
    · simp [hcond] at hi
  have hO'sub : interior (closure (⋃ i ∈ S, W i)) \ C ⊆ closure (W i₀) := by
    intro y ⟨hyInt, hyNotC⟩
    rcases mem_iUnion.1 (hClSub (interior_subset hyInt)) with ⟨i, hi⟩
    by_cases hiS : i ∈ S
    · simp [hiS] at hi
      by_cases heq : i = i₀
      · rwa [heq] at hi
      · exfalso
        exact hyNotC (mem_iUnion.2 ⟨i, by simp [hiS, heq, hi]⟩)
    · simp [hiS] at hi
  have hpInt₀ : p ∈ interior (closure (W i₀)) :=
    mem_interior.2 ⟨interior (closure (⋃ i ∈ S, W i)) \ C, hO'sub,
      isOpen_interior.sdiff hCclosed, ⟨hp, hpNotC⟩⟩
  rw [(hW i₀).2] at hpInt₀
  exact hpNot (mem_iUnion₂.2 ⟨i₀, hi₀S, hpInt₀⟩)

private def PartialRegOpenExp {X : Type} [TopologicalSpace X]
    (D : ℕ → Set X) (U : ℕ → X → Set X) (n : ℕ) (V : Fin n → X → Set X) : Prop :=
  (∀ k : Fin n, ∀ d ∈ D k.1, IsOpen (V k d) ∧ d ∈ V k d ∧ V k d ⊆ U k.1 d) ∧
  (∀ k : Fin n, ∀ d, d ∉ D k.1 → V k d = ∅) ∧
  (∀ S : Fin n → Set X, (∀ k, S k ⊆ D k.1) →
    IsRegularOpen (⋃ k : Fin n, ⋃ d ∈ S k, V k d))

private def extendFin {X : Type} {n : ℕ}
    (V : Fin n → X → Set X) (V_new : X → Set X) : Fin (n + 1) → X → Set X :=
  fun k => if h : k.1 < n then V ⟨k.1, h⟩ else V_new

theorem regularOpenDiscreteExpansionSeq_of_step
    (hStep : RegularOpenRefinementStep_stmt) :
    RegularOpenDiscreteExpansionSeq_stmt := by
  classical
  intro X _ hStrat D U hD hU hUdisc
  have hAdvance : ∀ (n : ℕ) (V : Fin n → X → Set X),
      PartialRegOpenExp D U n V →
      ∃ V_new : X → Set X, PartialRegOpenExp D U (n + 1) (extendFin V V_new) := by
    intro n V ⟨hV1, hV2, hV3⟩
    let V_flat : Fin n × X → Set X := fun p => V p.1 p.2
    have hVflatOpen : ∀ p : Fin n × X, IsOpen (V_flat p) := by
      intro ⟨k, d⟩
      by_cases hd : d ∈ D k.1
      · exact (hV1 k d hd).1
      · rw [show V_flat (k, d) = ∅ from hV2 k d hd]
        exact isOpen_empty
    have hVflatLf : LocallyFinite V_flat := by
      intro x
      choose N hN hNsub using fun k : Fin n => hUdisc k.1 x
      have hNinter : (⋂ k : Fin n, N k) ∈ nhds x := Filter.iInter_mem.2 hN
      refine ⟨⋂ k : Fin n, N k, hNinter, ?_⟩
      have hSub : {p : Fin n × X | (V_flat p ∩ ⋂ k : Fin n, N k).Nonempty} ⊆
          ⋃ k : Fin n, Prod.mk k '' {d : X | d ∈ D k.1 ∧ (U k.1 d ∩ N k).Nonempty} := by
        intro ⟨k, d⟩ ⟨y, hyV, hyN⟩
        have hd : d ∈ D k.1 := by
          by_contra hnot
          have : V k d = ∅ := hV2 k d hnot
          dsimp [V_flat] at hyV
          rw [this] at hyV
          exact hyV
        refine mem_iUnion.2 ⟨k, d, ⟨hd, y, (hV1 k d hd).2.2 hyV, mem_iInter.1 hyN k⟩, rfl⟩
      refine (Set.finite_iUnion (fun k : Fin n => (hNsub k).finite.image (Prod.mk k))).subset hSub
    have hVflatReg : ∀ S_flat : Set (Fin n × X), IsRegularOpen (⋃ p ∈ S_flat, V_flat p) := by
      intro S_flat
      let S : Fin n → Set X := fun k => {d : X | d ∈ D k.1 ∧ (k, d) ∈ S_flat}
      have hEq : (⋃ p ∈ S_flat, V_flat p) = (⋃ k : Fin n, ⋃ d ∈ S k, V k d) := by
        ext y
        simp only [mem_iUnion, exists_prop]
        constructor
        · rintro ⟨⟨k, d⟩, hpS, hyV⟩
          have hd : d ∈ D k.1 := by
            by_contra hnot
            dsimp [V_flat] at hyV
            rw [hV2 k d hnot] at hyV
            exact hyV
          exact ⟨k, d, ⟨hd, hpS⟩, hyV⟩
        · rintro ⟨k, d, ⟨_, hpS⟩, hyV⟩
          exact ⟨(k, d), hpS, hyV⟩
      rw [hEq]
      exact hV3 S (fun k d hd => hd.1)
    let Cov : Option X → Set X
      | some d => if d ∈ D n then U n d else ∅
      | none => (D n)ᶜ
    have hCovOpen : ∀ a : Option X, IsOpen (Cov a) := by
      rintro (_ | d)
      · exact (hD n (D n) Subset.rfl).isOpen_compl
      · by_cases hd : d ∈ D n
        · simp [Cov, hd, (hU n d hd).1]
        · simp [Cov, hd]
    have hCovUniv : (⋃ a : Option X, Cov a) = Set.univ := by
      refine eq_univ_iff_forall.2 (fun x => ?_)
      by_cases hx : x ∈ D n
      · exact mem_iUnion.2 ⟨some x, by simp [Cov, hx, (hU n x hx).2]⟩
      · exact mem_iUnion.2 ⟨none, hx⟩
    obtain ⟨γ, W, hWopen, hWuniv, _, hWref, hWreg⟩ :=
      hStep X hStrat Cov V_flat hCovOpen hCovUniv hVflatOpen hVflatLf hVflatReg
    let V_new : X → Set X := fun d => if d ∈ D n then ⋃ c ∈ {c : γ | d ∈ W c}, W c else ∅
    refine ⟨V_new, ?_, ?_, ?_⟩
    · intro k d hd
      by_cases hk : k.1 < n
      · simp [extendFin, hk]
        exact hV1 ⟨k.1, hk⟩ d hd
      · have hkn : k.1 = n := Nat.le_antisymm (Nat.lt_succ_iff.1 k.2) (Nat.not_lt.1 hk)
        have hdn : d ∈ D n := hkn ▸ hd
        simp only [extendFin, hk, ↓reduceDIte, V_new, hdn, ↓reduceIte]
        refine ⟨isOpen_biUnion (fun c _ => hWopen c), ?_, ?_⟩
        · have hdW : d ∈ ⋃ c : γ, W c := by rw [hWuniv]; trivial
          rcases mem_iUnion.1 hdW with ⟨c, hdc⟩
          exact mem_iUnion₂.2 ⟨c, hdc, hdc⟩
        · intro y hy
          rcases mem_iUnion₂.1 hy with ⟨c, hdc, hyc⟩
          rcases hWref c with ⟨a, hWa⟩
          cases a with
          | none => exact False.elim ((hWa hdc) hdn)
          | some d' =>
            by_cases hd' : d' ∈ D n
            · simp only [Cov, hd', ↓reduceIte] at hWa
              have hdU' : d ∈ U n d' := hWa hdc
              obtain ⟨N, hN, hNsub⟩ := hUdisc n d
              have hdN : d ∈ N := mem_of_mem_nhds hN
              have hEqd : d' = d := hNsub ⟨hd', d, hdU', hdN⟩ ⟨hdn, d, (hU n d hdn).2, hdN⟩
              rw [hkn, ← hEqd]
              exact hWa hyc
            · simp only [Cov, hd', ↓reduceIte] at hWa
              exact False.elim (hWa hdc)
    · intro k d hd
      by_cases hk : k.1 < n
      · simp [extendFin, hk]
        exact hV2 ⟨k.1, hk⟩ d hd
      · have hkn : k.1 = n := Nat.le_antisymm (Nat.lt_succ_iff.1 k.2) (Nat.not_lt.1 hk)
        have hdn : d ∉ D n := hkn ▸ hd
        simp [extendFin, hk, V_new, hdn]
    · intro S hS
      let S_prev : Set (Fin n × X) :=
        {p : Fin n × X | p.2 ∈ S ⟨p.1.1, Nat.lt_succ_of_lt p.1.2⟩}
      let T_new : Set γ := {c : γ | ∃ d ∈ S ⟨n, Nat.lt_succ_self n⟩, d ∈ W c}
      have hEq : (⋃ k : Fin (n + 1), ⋃ d ∈ S k, extendFin V V_new k d) =
          (⋃ p ∈ S_prev, V_flat p) ∪ (⋃ c ∈ T_new, W c) := by
        ext y
        simp only [mem_union, mem_iUnion, exists_prop]
        constructor
        · rintro ⟨k, d, hdS, hy⟩
          by_cases hk : k.1 < n
          · simp only [extendFin, hk, ↓reduceDIte] at hy
            left
            refine ⟨(⟨k.1, hk⟩, d), ?_, hy⟩
            simpa [S_prev] using hdS
          · have hkn : k.1 = n := Nat.le_antisymm (Nat.lt_succ_iff.1 k.2) (Nat.not_lt.1 hk)
            have hkEq : k = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hkn
            have hdSn : d ∈ S ⟨n, Nat.lt_succ_self n⟩ := hkEq ▸ hdS
            have hdn : d ∈ D n := hS ⟨n, Nat.lt_succ_self n⟩ hdSn
            simp only [extendFin, hk, ↓reduceDIte, V_new, hdn, ↓reduceIte, mem_iUnion, exists_prop] at hy
            rcases hy with ⟨c, hdc, hyc⟩
            right
            exact ⟨c, ⟨d, hdSn, hdc⟩, hyc⟩
        · rintro (⟨⟨k, d⟩, hpS, hy⟩ | ⟨c, ⟨d, hdSn, hdc⟩, hyc⟩)
          · refine ⟨⟨k.1, Nat.lt_succ_of_lt k.2⟩, d, hpS, ?_⟩
            simpa [extendFin, k.2] using hy
          · have hdn : d ∈ D n := hS ⟨n, Nat.lt_succ_self n⟩ hdSn
            refine ⟨⟨n, Nat.lt_succ_self n⟩, d, hdSn, ?_⟩
            simp only [extendFin, Nat.lt_irrefl, ↓reduceDIte, V_new, hdn, ↓reduceIte, mem_iUnion, exists_prop]
            exact ⟨c, hdc, hyc⟩
      rw [hEq]
      exact hWreg S_prev T_new
  let seq : (n : ℕ) → {V : Fin n → X → Set X // PartialRegOpenExp D U n V} :=
    Nat.rec
      ⟨fun k => k.elim0, ⟨fun k => k.elim0, fun k => k.elim0, fun _ _ => by
        simp [IsRegularOpen]⟩⟩
      (fun n prev =>
        ⟨extendFin prev.1 (Classical.choose (hAdvance n prev.1 prev.2)),
         Classical.choose_spec (hAdvance n prev.1 prev.2)⟩)
  have hCoherent : ∀ (n m : ℕ) (h : m < n),
      (seq n).1 ⟨m, h⟩ = (seq (m + 1)).1 ⟨m, Nat.lt_succ_self m⟩ := by
    intro n
    induction n with
    | zero => intro m h; exact False.elim (Nat.not_lt_zero m h)
    | succ n ih =>
      intro m h
      by_cases hlt : m < n
      · have hstep : (seq (n + 1)).1 ⟨m, h⟩ = (seq n).1 ⟨m, hlt⟩ := by
          simp [seq, extendFin, hlt]
        rw [hstep, ih m hlt]
      · have heq : m = n := Nat.le_antisymm (Nat.lt_succ_iff.1 h) (Nat.not_lt.1 hlt)
        subst heq
        rfl
  let V_final : ℕ → X → Set X := fun n => (seq (n + 1)).1 ⟨n, Nat.lt_succ_self n⟩
  refine ⟨V_final, ?_, ?_⟩
  · intro n d hd
    exact (seq (n + 1)).2.1 ⟨n, Nat.lt_succ_self n⟩ d hd
  · intro N S hS
    have hEq : (⋃ k : Fin (N + 1), ⋃ d ∈ S k, V_final k.1 d) =
        (⋃ k : Fin (N + 1), ⋃ d ∈ S k, (seq (N + 1)).1 k d) := by
      congr 1
      funext k
      have hk := hCoherent (N + 1) k.1 k.2
      have hk' : (seq (N + 1)).1 k = (seq (k.1 + 1)).1 ⟨k.1, Nat.lt_succ_self k.1⟩ := by
        simpa using hk
      change (⋃ d ∈ S k, (seq (k.1 + 1)).1 ⟨k.1, Nat.lt_succ_self k.1⟩ d) =
        (⋃ d ∈ S k, (seq (N + 1)).1 k d)
      rw [← hk']
    rw [hEq]
    exact (seq (N + 1)).2.2.2 S hS

end Work.L0028Helpers
