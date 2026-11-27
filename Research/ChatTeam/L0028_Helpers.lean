import Mathlib.Topology.Closure
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Bases
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Analysis.Real.Cardinality
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

/-! ### 青: Mizokami (2003, arXiv:math/0312457) Lemma 1.5・Lemma 1.2 コア補題 -/

def shrinkingStrat {X : Type*} (G : Set X → ℕ → Set X) (H : Set X) (n : ℕ) : Set X :=
  ⋂ k ∈ Set.Iic n, G H k

lemma isOpen_shrinkingStrat {X : Type*} [TopologicalSpace X] {G : Set X → ℕ → Set X}
    (hopen : ∀ H n, IsOpen (G H n)) (H : Set X) (n : ℕ) :
    IsOpen (shrinkingStrat G H n) :=
  (Set.finite_Iic n).isOpen_biInter (fun k _ => hopen H k)

lemma shrinkingStrat_anti {X : Type*} {G : Set X → ℕ → Set X} {H : Set X} {m n : ℕ}
    (hmn : m ≤ n) : shrinkingStrat G H n ⊆ shrinkingStrat G H m := by
  intro y hy
  simp only [shrinkingStrat, mem_iInter] at hy ⊢
  intro k hkm
  exact hy k (le_trans hkm hmn)

lemma shrinkingStrat_mono {X : Type*} {G : Set X → ℕ → Set X}
    (hmono : ∀ ⦃H₁ H₂ : Set X⦄, H₁ ⊆ H₂ → ∀ n, G H₁ n ⊆ G H₂ n)
    {H₁ H₂ : Set X} (hsub : H₁ ⊆ H₂) (n : ℕ) :
    shrinkingStrat G H₁ n ⊆ shrinkingStrat G H₂ n := by
  intro y hy
  simp only [shrinkingStrat, mem_iInter] at hy ⊢
  intro k hk
  exact hmono hsub k (hy k hk)

lemma subset_shrinkingStrat {X : Type*} [TopologicalSpace X] {G : Set X → ℕ → Set X}
    (hsub : ∀ H, IsClosed H → ∀ n, H ⊆ G H n) {H : Set X} (hH : IsClosed H) (n : ℕ) :
    H ⊆ shrinkingStrat G H n := by
  intro y hy
  simp only [shrinkingStrat, mem_iInter]
  intro k _
  exact hsub H hH k hy

lemma iInter_closure_shrinkingStrat {X : Type*} [TopologicalSpace X] {G : Set X → ℕ → Set X}
    (hsub : ∀ H, IsClosed H → ∀ n, H ⊆ G H n)
    (hinter : ∀ H, IsClosed H → (⋂ n, closure (G H n)) = H)
    {H : Set X} (hH : IsClosed H) :
    (⋂ n, closure (shrinkingStrat G H n)) = H := by
  apply Subset.antisymm
  · intro y hy
    rw [← hinter H hH, mem_iInter]
    simp only [mem_iInter] at hy
    intro n
    have hle : shrinkingStrat G H n ⊆ G H n := by
      intro z hz
      simp only [shrinkingStrat, mem_iInter] at hz
      exact hz n (Set.mem_Iic.mpr le_rfl)
    exact closure_mono hle (hy n)
  · intro y hy
    simp only [mem_iInter]
    intro n
    exact subset_closure (subset_shrinkingStrat hsub hH n hy)

lemma mizokami_lemma_1_5 {X : Type*} [TopologicalSpace X] {G : Set X → ℕ → Set X}
    (hG_open : ∀ H n, IsOpen (G H n))
    (hG_sub : ∀ H, IsClosed H → ∀ n, H ⊆ G H n)
    (hG_inter : ∀ H, IsClosed H → (⋂ n, closure (G H n)) = H)
    (hG_mono : ∀ ⦃H₁ H₂ : Set X⦄, H₁ ⊆ H₂ → ∀ n, G H₁ n ⊆ G H₂ n)
    {M : Set X} (hM : IsClosed M)
    {𝓑 : Set (Set X)} (h𝓑_closed : ∀ B ∈ 𝓑, IsClosed B)
    (h𝓑_cp : MSpace.ClosurePreserving 𝓑) :
    ∃ S : Set X → Set X,
      (∀ B ∈ 𝓑, IsOpen (S B) ∧ S B ⊆ Mᶜ) ∧
      (∀ B ∈ 𝓑, B \ M ⊆ S B) ∧
      (∀ 𝓑' ⊆ 𝓑, closure (⋃ B ∈ 𝓑', S B) ∩ M ⊆ (⋃₀ 𝓑') ∩ M) := by
  let G' : Set X → ℕ → Set X := shrinkingStrat G
  let S : Set X → Set X := fun B => ⋃ n, G' B n \ closure (G' M n)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro B _
    refine ⟨isOpen_iUnion fun n => (isOpen_shrinkingStrat hG_open B n).sdiff isClosed_closure, ?_⟩
    rintro y ⟨_, ⟨n, rfl⟩, _, hy_notcl⟩ hyM
    exact hy_notcl (subset_closure (subset_shrinkingStrat hG_sub hM n hyM))
  · intro B hB y ⟨hyB, hyM⟩
    have hM_eq : (⋂ n, closure (G' M n)) = M := iInter_closure_shrinkingStrat hG_sub hG_inter hM
    rw [← hM_eq, mem_iInter] at hyM
    push Not at hyM
    obtain ⟨n, hn⟩ := hyM
    exact mem_iUnion.mpr ⟨n, subset_shrinkingStrat hG_sub (h𝓑_closed B hB) n hyB, hn⟩
  · intro 𝓑' h𝓑' y ⟨hy_cl, hyM⟩
    refine ⟨?_, hyM⟩
    let H : Set X := ⋃₀ 𝓑'
    have hH_closed : IsClosed H := by
      have hcp := h𝓑_cp 𝓑' h𝓑'
      have himg : ⋃₀ (closure '' 𝓑') = H := by
        ext z
        constructor
        · rintro ⟨_, ⟨B, hB, rfl⟩, hz⟩
          rw [(h𝓑_closed B (h𝓑' hB)).closure_eq] at hz
          exact ⟨B, hB, hz⟩
        · rintro ⟨B, hB, hz⟩
          exact ⟨closure B, ⟨B, hB, rfl⟩, subset_closure hz⟩
      rw [himg] at hcp
      rw [← hcp]
      exact isClosed_closure
    by_contra hyH
    have hH_eq : (⋂ k, closure (G' H k)) = H :=
      iInter_closure_shrinkingStrat hG_sub hG_inter hH_closed
    change y ∉ H at hyH
    rw [← hH_eq, mem_iInter] at hyH
    push Not at hyH
    obtain ⟨k, hk⟩ := hyH
    let V : Set X := G' M k \ closure (G' H k)
    have hV_open : IsOpen V := (isOpen_shrinkingStrat hG_open M k).sdiff isClosed_closure
    have hyV : y ∈ V := ⟨subset_shrinkingStrat hG_sub hM k hyM, hk⟩
    rw [mem_closure_iff] at hy_cl
    obtain ⟨z, ⟨hzM, hznotH⟩, hzU⟩ := hy_cl V hV_open hyV
    obtain ⟨B, hB, hzSB⟩ := mem_iUnion₂.mp hzU
    obtain ⟨n, hzB, hznotM⟩ := mem_iUnion.mp hzSB
    have hzH : z ∈ G' H n := shrinkingStrat_mono hG_mono (subset_sUnion_of_mem hB) n hzB
    rcases le_total k n with hkn | hnk
    · exact hznotH (subset_closure (shrinkingStrat_anti hkn hzH))
    · exact hznotM (subset_closure (shrinkingStrat_anti hnk hzM))

lemma mizokami_lemma_1_5_singleton {X : Type*} [TopologicalSpace X] [T1Space X]
    {G : Set X → ℕ → Set X}
    (hG_open : ∀ H n, IsOpen (G H n))
    (hG_sub : ∀ H, IsClosed H → ∀ n, H ⊆ G H n)
    (hG_inter : ∀ H, IsClosed H → (⋂ n, closure (G H n)) = H)
    (hG_mono : ∀ ⦃H₁ H₂ : Set X⦄, H₁ ⊆ H₂ → ∀ n, G H₁ n ⊆ G H₂ n)
    {x : X} {𝓑 : Set (Set X)}
    (h𝓑_closed : ∀ B ∈ 𝓑, IsClosed B)
    (h𝓑_cp : MSpace.ClosurePreserving 𝓑) :
    ∃ S : Set X → Set X,
      (∀ B ∈ 𝓑, IsOpen (S B) ∧ x ∉ S B) ∧
      (∀ B ∈ 𝓑, B \ {x} ⊆ S B) ∧
      (∀ 𝓑' ⊆ 𝓑, x ∈ closure (⋃ B ∈ 𝓑', S B) → ∃ B ∈ 𝓑', x ∈ B) := by
  obtain ⟨S, hopen, hsub, hcl⟩ :=
    mizokami_lemma_1_5 hG_open hG_sub hG_inter hG_mono isClosed_singleton h𝓑_closed h𝓑_cp
  refine ⟨S, ?_, hsub, ?_⟩
  · intro B hB
    exact ⟨(hopen B hB).1, fun hx => (hopen B hB).2 hx rfl⟩
  · intro 𝓑' h𝓑' hx
    have hmem := (hcl 𝓑' h𝓑' ⟨hx, rfl⟩).1
    exact mem_sUnion.mp hmem

def atomClosed {X : Type*} (𝓑 : Set (Set X)) (N : Set X) : Set X :=
  N ∩ ⋂ B ∈ {B ∈ 𝓑 | (N ∩ B).Nonempty}, B

lemma atomClosed_subset {X : Type*} (𝓑 : Set (Set X)) (N : Set X) :
    atomClosed 𝓑 N ⊆ N := inter_subset_left

lemma isClosed_atomClosed {X : Type*} [TopologicalSpace X]
    {𝓑 : Set (Set X)} (h𝓑_closed : ∀ B ∈ 𝓑, IsClosed B) {N : Set X} (hN : IsClosed N) :
    IsClosed (atomClosed 𝓑 N) :=
  hN.inter (isClosed_biInter fun B hB => h𝓑_closed B hB.1)

lemma atomClosed_subset_of_inter_nonempty {X : Type*} {𝓑 : Set (Set X)} {N B : Set X}
    (hB : B ∈ 𝓑) (hne : (atomClosed 𝓑 N ∩ B).Nonempty) : atomClosed 𝓑 N ⊆ B := by
  have hNB : (N ∩ B).Nonempty := hne.mono (inter_subset_inter_left B (atomClosed_subset 𝓑 N))
  intro y hy
  exact mem_iInter₂.mp hy.2 B ⟨hB, hNB⟩

def openAvoidingCP {X : Type*} (𝓑 : Set (Set X)) (F W : Set X) : Set X :=
  W \ ⋃₀ {B ∈ 𝓑 | Disjoint F B}

lemma isOpen_openAvoidingCP {X : Type*} [TopologicalSpace X]
    {𝓑 : Set (Set X)} (h𝓑_closed : ∀ B ∈ 𝓑, IsClosed B) (h𝓑_cp : MSpace.ClosurePreserving 𝓑)
    {F W : Set X} (hW : IsOpen W) : IsOpen (openAvoidingCP 𝓑 F W) := by
  have hsub : {B ∈ 𝓑 | Disjoint F B} ⊆ 𝓑 := fun _ h => h.1
  have hcl : IsClosed (⋃₀ {B ∈ 𝓑 | Disjoint F B}) := by
    have hcp := h𝓑_cp _ hsub
    have himg : ⋃₀ (closure '' {B ∈ 𝓑 | Disjoint F B}) = ⋃₀ {B ∈ 𝓑 | Disjoint F B} := by
      ext z
      constructor
      · rintro ⟨_, ⟨B, hB, rfl⟩, hz⟩
        rw [(h𝓑_closed B hB.1).closure_eq] at hz
        exact ⟨B, hB, hz⟩
      · rintro ⟨B, hB, hz⟩
        exact ⟨closure B, ⟨B, hB, rfl⟩, subset_closure hz⟩
    rw [himg] at hcp
    rw [← hcp]
    exact isClosed_closure
  exact hW.sdiff hcl

lemma subset_openAvoidingCP {X : Type*} {𝓑 : Set (Set X)} {F W : Set X}
    (hFW : F ⊆ W) : F ⊆ openAvoidingCP 𝓑 F W := by
  intro y hy
  refine ⟨hFW hy, ?_⟩
  rintro ⟨B, ⟨_, hdisj⟩, hyB⟩
  exact Set.disjoint_left.mp hdisj hy hyB

lemma disjoint_openAvoidingCP {X : Type*} {𝓑 : Set (Set X)} {F W B : Set X}
    (hB : B ∈ 𝓑) (hdisj : Disjoint F B) : Disjoint (openAvoidingCP 𝓑 F W) B := by
  refine Set.disjoint_left.mpr fun y hy hyB => hy.2 ?_
  exact ⟨B, ⟨hB, hdisj⟩, hyB⟩

/-! ### カエル: Shrinking Lemma ＆ 超限帰納法による SingleRegularOpenInsert ⇒ RegularOpenRefinementStep -/

def SingleRegularOpenInsert_paracompact_stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T3Space X] [ParacompactSpace X],
    ∀ {α : Type} (A : α → Set X),
      (∀ a, IsOpen (A a)) →
      LocallyFinite A →
      (∀ S : Set α, IsRegularOpen (⋃ a ∈ S, A a)) →
      ∀ (F G : Set X), IsClosed F → IsOpen G → F ⊆ G →
        ∃ W : Set X, IsRegularOpen W ∧ F ⊆ W ∧ closure W ⊆ G ∧
          ∀ S : Set α, IsRegularOpen (W ∪ (⋃ a ∈ S, A a))

theorem exists_locallyFinite_refinement_with_closed_shrinking
    {X α : Type} [TopologicalSpace X] [T3Space X] [ParacompactSpace X]
    (U : α → Set X) (hUopen : ∀ a, IsOpen (U a)) (hUuniv : (⋃ a, U a) = Set.univ) :
    ∃ (ι : Type) (G F : ι → Set X),
      (∀ i, IsOpen (G i)) ∧ LocallyFinite G ∧ (∀ i, ∃ a, G i ⊆ U a) ∧
      (∀ i, IsClosed (F i)) ∧ (∀ i, F i ⊆ G i) ∧ (⋃ i, F i) = Set.univ := by
  classical
  obtain ⟨ι, G, hGopen, hGuniv, hGlf, hGref⟩ :=
    ParacompactSpace.locallyFinite_refinement α U hUopen hUuniv
  have hKex : ∀ x : X, ∃ K : Set X, IsOpen K ∧ x ∈ K ∧ ∃ i : ι, closure K ⊆ G i := by
    intro x
    have hxG : x ∈ ⋃ i, G i := by rw [hGuniv]; trivial
    rcases mem_iUnion.1 hxG with ⟨i, hxi⟩
    obtain ⟨C, ⟨hCx, hCcl⟩, hCG⟩ :=
      (closed_nhds_basis x).mem_iff.1 ((hGopen i).mem_nhds hxi)
    exact ⟨interior C, isOpen_interior, mem_interior_iff_mem_nhds.2 hCx,
      i, (closure_minimal interior_subset hCcl).trans hCG⟩
  choose K hKopen hxK hKsub using hKex
  have hKuniv : (⋃ x : X, K x) = Set.univ :=
    eq_univ_iff_forall.2 (fun x => mem_iUnion.2 ⟨x, hxK x⟩)
  obtain ⟨κ, H, hHopen, hHuniv, hHlf, hHref⟩ :=
    ParacompactSpace.locallyFinite_refinement X K hKopen hKuniv
  let F : ι → Set X := fun i => ⋃ j : κ, if closure (H j) ⊆ G i then closure (H j) else ∅
  refine ⟨ι, G, F, hGopen, hGlf, hGref, ?_, ?_, ?_⟩
  · intro i
    have hlf_i : LocallyFinite (fun j : κ => if closure (H j) ⊆ G i then closure (H j) else ∅) := by
      intro x
      obtain ⟨M, hM, hFin⟩ := hHlf.closure x
      refine ⟨M, hM, hFin.subset ?_⟩
      intro j ⟨y, hy1, hy2⟩
      by_cases hsub : closure (H j) ⊆ G i
      · simp [hsub] at hy1
        exact ⟨y, hy1, hy2⟩
      · simp [hsub] at hy1
    apply hlf_i.isClosed_iUnion
    intro j
    by_cases hsub : closure (H j) ⊆ G i
    · simp [hsub, isClosed_closure]
    · simp [hsub]
  · intro i y hy
    dsimp only [F] at hy
    rcases mem_iUnion.1 hy with ⟨j, hj⟩
    by_cases hsub : closure (H j) ⊆ G i
    · simp [hsub] at hj
      exact hsub hj
    · simp [hsub] at hj
  · refine eq_univ_iff_forall.2 (fun x => ?_)
    have hxH : x ∈ ⋃ j : κ, H j := by rw [hHuniv]; trivial
    rcases mem_iUnion.1 hxH with ⟨j, hxj⟩
    rcases hHref j with ⟨y, hHjKy⟩
    rcases hKsub y with ⟨i, hKyGi⟩
    have hSub : closure (H j) ⊆ G i := (closure_mono hHjKy).trans hKyGi
    refine mem_iUnion.2 ⟨i, ?_⟩
    dsimp only [F]
    exact mem_iUnion.2 ⟨j, by simp [hSub, subset_closure hxj]⟩

private lemma exists_max_of_finite_nonempty
    {ι : Type*} (r : ι → ι → Prop) [IsWellOrder ι r]
    {S : Set ι} (hFin : S.Finite) (hNe : S.Nonempty) :
    ∃ m ∈ S, ∀ x ∈ S, x = m ∨ r x m := by
  classical
  have hNeF : hFin.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := hNe
    exact ⟨x, hFin.mem_toFinset.2 hx⟩
  suffices h : ∀ (F : Finset ι), F.Nonempty → ∃ m ∈ F, ∀ x ∈ F, x = m ∨ r x m by
    obtain ⟨m, hmF, hmax⟩ := h hFin.toFinset hNeF
    exact ⟨m, hFin.mem_toFinset.1 hmF, fun x hx => hmax x (hFin.mem_toFinset.2 hx)⟩
  intro F
  induction F using Finset.induction_on with
  | empty => intro h; exact False.elim (Finset.not_nonempty_empty h)
  | @insert a s _ ih =>
    intro _
    by_cases hs : s.Nonempty
    · obtain ⟨m, hmS, hmax⟩ := ih hs
      rcases trichotomous_of r a m with ham | rfl | hma
      · refine ⟨m, Finset.mem_insert_of_mem hmS, ?_⟩
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hxs
        · exact Or.inr ham
        · exact hmax x hxs
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hxs
        · exact Or.inl rfl
        · exact hmax x hxs
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hxs
        · exact Or.inl rfl
        · rcases hmax x hxs with rfl | hxm
          · exact Or.inr hma
          · exact Or.inr (IsTrans.trans x m a hxm hma)
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      refine ⟨a, Finset.mem_insert_self a ∅, ?_⟩
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · exact Or.inl rfl
      · exact False.elim (Finset.notMem_empty x hx')

open Classical in
private lemma isRegularOpen_union_of_wellOrder_local_step
    {X β ι : Type*} [TopologicalSpace X]
    (r : ι → ι → Prop) [IsWellOrder ι r]
    (V : β → Set X) (W : ι → Set X)
    (hVopen : ∀ b, IsOpen (V b)) (_hVlf : LocallyFinite V)
    (hVreg : ∀ S : Set β, IsRegularOpen (⋃ b ∈ S, V b))
    (T : Set ι)
    (hWopen : ∀ j ∈ T, IsOpen (W j))
    (hWlf : LocallyFinite (fun j : ι => if j ∈ T then W j else ∅))
    (hStepAt : ∀ j ∈ T, ∀ (S : Set β) (T' : Set ι),
      (∀ k ∈ T', k ∈ T ∧ r k j) →
      IsRegularOpen (W j ∪ (⋃ b ∈ S, V b) ∪ (⋃ k ∈ T', W k)))
    (S : Set β) :
    IsRegularOpen ((⋃ b ∈ S, V b) ∪ (⋃ j ∈ T, W j)) := by
  classical
  let U_tot : Set X := (⋃ b ∈ S, V b) ∪ (⋃ j ∈ T, W j)
  have hOpen : IsOpen U_tot :=
    (isOpen_biUnion (fun b _ => hVopen b)).union (isOpen_biUnion (fun j hj => hWopen j hj))
  refine ⟨hOpen, Subset.antisymm ?_ (interior_maximal subset_closure hOpen)⟩
  have hWclSub : closure (⋃ j ∈ T, W j) ⊆ ⋃ j : ι, if j ∈ T then closure (W j) else ∅ := by
    apply closure_minimal
    · intro y hy
      rcases mem_iUnion₂.1 hy with ⟨j, hjT, hyW⟩
      exact mem_iUnion.2 ⟨j, by simp [hjT, subset_closure hyW]⟩
    · have hlf_cl : LocallyFinite (fun j : ι => if j ∈ T then closure (W j) else ∅) := by
        intro x
        obtain ⟨M, hM, hFin⟩ := hWlf.closure x
        refine ⟨M, hM, hFin.subset ?_⟩
        intro j ⟨y, hy1, hy2⟩
        by_cases hj : j ∈ T
        · simp [hj] at hy1
          exact ⟨y, by simpa [hj] using hy1, hy2⟩
        · simp [hj] at hy1
      apply hlf_cl.isClosed_iUnion
      intro j
      by_cases hj : j ∈ T
      · simp [hj, isClosed_closure]
      · simp [hj]
  intro p hp
  obtain ⟨M, hM, hFinM⟩ := hWlf.closure p
  let O : Set X := interior (closure U_tot) ∩ interior M
  have hOopen : IsOpen O := isOpen_interior.inter isOpen_interior
  have hpO : p ∈ O := ⟨hp, mem_interior_iff_mem_nhds.2 hM⟩
  let T_fin : Set ι := {j : ι | j ∈ T ∧ (closure (W j) ∩ M).Nonempty}
  have hTfin : T_fin.Finite := by
    refine hFinM.subset ?_
    intro j ⟨hjT, y, hyCl, hyM⟩
    exact ⟨y, by simpa [hjT] using hyCl, hyM⟩
  have hOsub : O ⊆ closure ((⋃ b ∈ S, V b) ∪ (⋃ j ∈ T_fin, W j)) := by
    intro y ⟨hyInt, hyM⟩
    have hyCl : y ∈ closure (⋃ b ∈ S, V b) ∪ closure (⋃ j ∈ T, W j) := by
      rw [← closure_union]
      exact interior_subset hyInt
    rw [closure_union]
    rcases hyCl with hyV | hyW
    · exact Or.inl hyV
    · right
      rcases mem_iUnion.1 (hWclSub hyW) with ⟨j, hj⟩
      by_cases hjT : j ∈ T
      · simp [hjT] at hj
        have hjFin : j ∈ T_fin := ⟨hjT, y, hj, interior_subset hyM⟩
        exact closure_mono (subset_biUnion_of_mem hjFin) hj
      · simp [hjT] at hj
  by_cases hNe : T_fin.Nonempty
  · obtain ⟨j_max, hj_max, hmax⟩ := exists_max_of_finite_nonempty r hTfin hNe
    let T_lt : Set ι := {k : ι | k ∈ T_fin ∧ r k j_max}
    have hEqSub : ((⋃ b ∈ S, V b) ∪ (⋃ j ∈ T_fin, W j)) ⊆
        (W j_max ∪ (⋃ b ∈ S, V b) ∪ (⋃ k ∈ T_lt, W k)) := by
      intro y hy
      rcases hy with hyV | hyW
      · exact Or.inl (Or.inr hyV)
      · rcases mem_iUnion₂.1 hyW with ⟨j, hjFin, hyWj⟩
        rcases hmax j hjFin with rfl | hlt
        · exact Or.inl (Or.inl hyWj)
        · exact Or.inr (mem_iUnion₂.2 ⟨j, ⟨hjFin, hlt⟩, hyWj⟩)
    have hpInt : p ∈ interior (closure (W j_max ∪ (⋃ b ∈ S, V b) ∪ (⋃ k ∈ T_lt, W k))) :=
      mem_interior.2 ⟨O, hOsub.trans (closure_mono hEqSub), hOopen, hpO⟩
    have hReg := hStepAt j_max hj_max.1 S T_lt (fun k hk => ⟨hk.1.1, hk.2⟩)
    rw [hReg.2] at hpInt
    rcases hpInt with (hpW | hpV) | hpLt
    · exact Or.inr (mem_iUnion₂.2 ⟨j_max, hj_max.1, hpW⟩)
    · exact Or.inl hpV
    · rcases mem_iUnion₂.1 hpLt with ⟨k, hk, hpWk⟩
      exact Or.inr (mem_iUnion₂.2 ⟨k, hk.1.1, hpWk⟩)
  · rw [Set.not_nonempty_iff_eq_empty] at hNe
    have hOsubV : O ⊆ closure (⋃ b ∈ S, V b) := by
      simpa [hNe] using hOsub
    have hpV : p ∈ interior (closure (⋃ b ∈ S, V b)) :=
      mem_interior.2 ⟨O, hOsubV, hOopen, hpO⟩
    rw [(hVreg S).2] at hpV
    exact Or.inl hpV

theorem regularOpenRefinementStep_of_singleInsert_aux
    (hInsert : SingleRegularOpenInsert_paracompact_stmt)
    {X α β : Type} [TopologicalSpace X] [T3Space X] [ParacompactSpace X]
    (U : α → Set X) (V : β → Set X)
    (hUopen : ∀ a, IsOpen (U a)) (hUuniv : (⋃ a, U a) = Set.univ)
    (hVopen : ∀ b, IsOpen (V b)) (hVlf : LocallyFinite V)
    (hVreg : ∀ S : Set β, IsRegularOpen (⋃ b ∈ S, V b)) :
    ∃ (γ : Type) (W : γ → Set X),
      (∀ c, IsOpen (W c)) ∧ (⋃ c, W c) = Set.univ ∧
      LocallyFinite W ∧ (∀ c, ∃ a, W c ⊆ U a) ∧
      (∀ (S : Set β) (T : Set γ),
        IsRegularOpen ((⋃ b ∈ S, V b) ∪ (⋃ c ∈ T, W c))) := by
  classical
  obtain ⟨ι, G, F, hGopen, hGlf, hGref, hFcl, hFG, hFuniv⟩ :=
    exists_locallyFinite_refinement_with_closed_shrinking U hUopen hUuniv
  let r : ι → ι → Prop := WellOrderingRel
  have hwo : IsWellOrder ι r := WellOrderingRel.isWellOrder
  have hwf : WellFounded r := WellOrderingRel.isWellOrder.wf
  let GoodPrev (i : ι) (prev : (j : ι) → r j i → Set X) : Prop :=
    (∀ j (hj : r j i), IsOpen (prev j hj) ∧ F j ⊆ prev j hj ∧ closure (prev j hj) ⊆ G j) ∧
    (∀ (S : Set β) (T : Set {j : ι // r j i}),
      IsRegularOpen ((⋃ b ∈ S, V b) ∪ (⋃ q ∈ T, prev q.1 q.2)))
  have hStepEx : ∀ (i : ι) (prev : (j : ι) → r j i → Set X),
      GoodPrev i prev →
      ∃ Wi : Set X, IsRegularOpen Wi ∧ F i ⊆ Wi ∧ closure Wi ⊆ G i ∧
        ∀ (S : Set β) (T : Set {j : ι // r j i}),
          IsRegularOpen (Wi ∪ (⋃ b ∈ S, V b) ∪ (⋃ q ∈ T, prev q.1 q.2)) := by
    intro i prev ⟨hP1, hP2⟩
    let A : β ⊕ {j : ι // r j i} → Set X
      | Sum.inl b => V b
      | Sum.inr q => prev q.1 q.2
    have hAopen : ∀ a, IsOpen (A a) := by
      rintro (b | q)
      · exact hVopen b
      · exact (hP1 q.1 q.2).1
    have hAlf : LocallyFinite A := by
      intro x
      obtain ⟨M₁, hM₁, hFin₁⟩ := hVlf x
      obtain ⟨M₂, hM₂, hFin₂⟩ := hGlf x
      refine ⟨M₁ ∩ M₂, Filter.inter_mem hM₁ hM₂, ?_⟩
      have hSub : {a : β ⊕ {j : ι // r j i} | (A a ∩ (M₁ ∩ M₂)).Nonempty} ⊆
          (Sum.inl '' {b : β | (V b ∩ M₁).Nonempty}) ∪
          (Sum.inr '' {q : {j : ι // r j i} | (G q.1 ∩ M₂).Nonempty}) := by
        rintro (b | q) ⟨y, hyA, hy1, hy2⟩
        · exact Or.inl ⟨b, ⟨y, hyA, hy1⟩, rfl⟩
        · right
          refine ⟨q, ⟨y, ?_, hy2⟩, rfl⟩
          exact (hP1 q.1 q.2).2.2 (subset_closure hyA)
      have hFinQ : {q : {j : ι // r j i} | (G q.1 ∩ M₂).Nonempty}.Finite :=
        hFin₂.preimage (Subtype.val_injective.injOn)
      exact ((hFin₁.image Sum.inl).union (hFinQ.image Sum.inr)).subset hSub
    have hAreg : ∀ S : Set (β ⊕ {j : ι // r j i}), IsRegularOpen (⋃ a ∈ S, A a) := by
      intro S
      let S₁ : Set β := {b | Sum.inl b ∈ S}
      let S₂ : Set {j : ι // r j i} := {q | Sum.inr q ∈ S}
      have hEq : (⋃ a ∈ S, A a) = (⋃ b ∈ S₁, V b) ∪ (⋃ q ∈ S₂, prev q.1 q.2) := by
        ext y
        simp only [mem_union, mem_iUnion, exists_prop]
        constructor
        · rintro ⟨a | q, haS, hyA⟩
          · exact Or.inl ⟨a, haS, hyA⟩
          · exact Or.inr ⟨q, haS, hyA⟩
        · rintro (⟨b, hb, hy⟩ | ⟨q, hq, hy⟩)
          · exact ⟨Sum.inl b, hb, hy⟩
          · exact ⟨Sum.inr q, hq, hy⟩
      rw [hEq]
      exact hP2 S₁ S₂
    obtain ⟨Wi, hWiReg, hFiWi, hWiGi, hWiCompat⟩ :=
      hInsert X A hAopen hAlf hAreg (F i) (G i) (hFcl i) (hGopen i) (hFG i)
    refine ⟨Wi, hWiReg, hFiWi, hWiGi, ?_⟩
    intro S T
    let S_sum : Set (β ⊕ {j : ι // r j i}) := (Sum.inl '' S) ∪ (Sum.inr '' T)
    have hEq : (Wi ∪ (⋃ b ∈ S, V b) ∪ (⋃ q ∈ T, prev q.1 q.2)) =
        (Wi ∪ (⋃ a ∈ S_sum, A a)) := by
      ext y
      simp only [mem_union, mem_iUnion, exists_prop, S_sum, mem_image]
      constructor
      · rintro ((hyW | ⟨b, hb, hyV⟩) | ⟨q, hq, hyP⟩)
        · exact Or.inl hyW
        · exact Or.inr ⟨Sum.inl b, Or.inl ⟨b, hb, rfl⟩, hyV⟩
        · exact Or.inr ⟨Sum.inr q, Or.inr ⟨q, hq, rfl⟩, hyP⟩
      · rintro (hyW | ⟨a, (⟨b, hb, rfl⟩ | ⟨q, hq, rfl⟩), hyA⟩)
        · exact Or.inl (Or.inl hyW)
        · exact Or.inl (Or.inr ⟨b, hb, hyA⟩)
        · exact Or.inr ⟨q, hq, hyA⟩
    rw [hEq]
    exact hWiCompat S_sum
  let stepFn (i : ι) (prev : (j : ι) → r j i → Set X) : Set X :=
    if h : GoodPrev i prev then Classical.choose (hStepEx i prev h) else ∅
  let W : ι → Set X := hwf.fix stepFn
  have hAllGood : ∀ i : ι, GoodPrev i (fun j _ => W j) := by
    intro i
    refine hwf.induction (C := fun i => GoodPrev i (fun j _ => W j)) i ?_
    intro i ih
    have hSpec : ∀ j (hj : r j i),
        IsRegularOpen (W j) ∧ F j ⊆ W j ∧ closure (W j) ⊆ G j ∧
        ∀ (S : Set β) (T : Set {k : ι // r k j}),
          IsRegularOpen (W j ∪ (⋃ b ∈ S, V b) ∪ (⋃ q ∈ T, W q.1)) := by
      intro j hj
      have hWjeq : W j = stepFn j (fun k _ => W k) := WellFounded.fix_eq hwf stepFn j
      rw [hWjeq]
      dsimp only [stepFn]
      have hgood : GoodPrev j (fun k _ => W k) := ih j hj
      simp only [hgood, ↓reduceDIte]
      exact Classical.choose_spec (hStepEx j (fun k _ => W k) hgood)
    refine ⟨fun j hj => ⟨(hSpec j hj).1.1, (hSpec j hj).2.1, (hSpec j hj).2.2.1⟩, ?_⟩
    intro S T
    let T_ι : Set ι := Subtype.val '' T
    have hEqT : (⋃ q ∈ T, W q.1) = (⋃ j ∈ T_ι, W j) := by
      ext y
      simp only [mem_iUnion, exists_prop, T_ι, mem_image]
      constructor
      · rintro ⟨q, hqT, hy⟩; exact ⟨q.1, ⟨q, hqT, rfl⟩, hy⟩
      · rintro ⟨j, ⟨q, hqT, rfl⟩, hy⟩; exact ⟨q, hqT, hy⟩
    rw [hEqT]
    have hWlf_T : LocallyFinite (fun j : ι => if j ∈ T_ι then W j else ∅) := by
      intro x
      obtain ⟨M, hM, hFin⟩ := hGlf x
      refine ⟨M, hM, hFin.subset ?_⟩
      intro j ⟨y, hy1, hy2⟩
      by_cases hj : j ∈ T_ι
      · simp [hj] at hy1
        rcases hj with ⟨q, _, rfl⟩
        exact ⟨y, (hSpec q.1 q.2).2.2.1 (subset_closure hy1), hy2⟩
      · simp [hj] at hy1
    apply @isRegularOpen_union_of_wellOrder_local_step X β ι _ r hwo V W hVopen hVlf hVreg T_ι
    · intro j hj
      rcases hj with ⟨q, _, rfl⟩
      exact (hSpec q.1 q.2).1.1
    · exact hWlf_T
    · intro j hj S' T' hT'
      rcases hj with ⟨q, _, rfl⟩
      let T'_sub : Set {k : ι // r k q.1} := {p | p.1 ∈ T'}
      have hEq' : (⋃ k ∈ T', W k) = (⋃ p ∈ T'_sub, W p.1) := by
        ext y
        simp only [mem_iUnion, exists_prop, T'_sub]
        constructor
        · rintro ⟨k, hk, hy⟩; exact ⟨⟨k, (hT' k hk).2⟩, hk, hy⟩
        · rintro ⟨p, hp, hy⟩; exact ⟨p.1, hp, hy⟩
      rw [hEq']
      exact (hSpec q.1 q.2).2.2.2 S' T'_sub
  have hWspec : ∀ i : ι,
      IsRegularOpen (W i) ∧ F i ⊆ W i ∧ closure (W i) ⊆ G i ∧
      ∀ (S : Set β) (T : Set {k : ι // r k i}),
        IsRegularOpen (W i ∪ (⋃ b ∈ S, V b) ∪ (⋃ q ∈ T, W q.1)) := by
    intro i
    have hWieq : W i = stepFn i (fun k _ => W k) := WellFounded.fix_eq hwf stepFn i
    rw [hWieq]
    dsimp only [stepFn]
    have hgood := hAllGood i
    simp only [hgood, ↓reduceDIte]
    exact Classical.choose_spec (hStepEx i (fun k _ => W k) hgood)
  have hWlf : LocallyFinite W := by
    intro x
    obtain ⟨M, hM, hFin⟩ := hGlf x
    refine ⟨M, hM, hFin.subset ?_⟩
    intro i ⟨y, hyW, hyM⟩
    exact ⟨y, (hWspec i).2.2.1 (subset_closure hyW), hyM⟩
  refine ⟨ι, W, fun i => (hWspec i).1.1, ?_, hWlf, ?_, ?_⟩
  · refine eq_univ_iff_forall.2 (fun x => ?_)
    have hxF : x ∈ ⋃ i, F i := by rw [hFuniv]; trivial
    rcases mem_iUnion.1 hxF with ⟨i, hxi⟩
    exact mem_iUnion.2 ⟨i, (hWspec i).2.1 hxi⟩
  · intro i
    rcases hGref i with ⟨a, hGa⟩
    exact ⟨a, (subset_closure.trans (hWspec i).2.2.1).trans hGa⟩
  · intro S T
    have hWlf_T : LocallyFinite (fun j : ι => if j ∈ T then W j else ∅) := by
      intro x
      obtain ⟨M, hM, hFin⟩ := hWlf x
      refine ⟨M, hM, hFin.subset ?_⟩
      intro j ⟨y, hy1, hy2⟩
      by_cases hj : j ∈ T
      · simp [hj] at hy1; exact ⟨y, hy1, hy2⟩
      · simp [hj] at hy1
    apply @isRegularOpen_union_of_wellOrder_local_step X β ι _ r hwo V W hVopen hVlf hVreg T
    · intro j _; exact (hWspec j).1.1
    · exact hWlf_T
    · intro j _ S' T' hT'
      let T'_sub : Set {k : ι // r k j} := {p | p.1 ∈ T'}
      have hEq' : (⋃ k ∈ T', W k) = (⋃ p ∈ T'_sub, W p.1) := by
        ext y
        simp only [mem_iUnion, exists_prop, T'_sub]
        constructor
        · rintro ⟨k, hk, hy⟩; exact ⟨⟨k, (hT' k hk).2⟩, hk, hy⟩
        · rintro ⟨p, hp, hy⟩; exact ⟨p.1, hp, hy⟩
      rw [hEq']
      exact (hWspec j).2.2.2 S' T'_sub

/-! ### 青: Mizokami (2003, arXiv:math/0312457) Lemma 1.2 全文 -/

def IsDiscreteFamily {X ι : Type*} [TopologicalSpace X] (U : ι → Set X) : Prop :=
  ∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Set.Subsingleton {i : ι | (V ∩ U i).Nonempty}

lemma IsDiscreteFamily.mono {X ι : Type*} [TopologicalSpace X] {F U : ι → Set X}
    (hU : IsDiscreteFamily U) (hsub : ∀ i, F i ⊆ U i) : IsDiscreteFamily F := by
  intro x
  obtain ⟨V, hV_open, hxV, hsubsing⟩ := hU x
  refine ⟨V, hV_open, hxV, fun i hi j hj => hsubsing ?_ ?_⟩
  · exact hi.mono (inter_subset_inter_right V (hsub i))
  · exact hj.mono (inter_subset_inter_right V (hsub j))

lemma IsDiscreteFamily.isClosed_iUnion {X ι : Type*} [TopologicalSpace X] {F : ι → Set X}
    (hF_closed : ∀ i, IsClosed (F i)) (hF_disc : IsDiscreteFamily F) : IsClosed (⋃ i, F i) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨V, hV_open, hxV, hsubsing⟩ := hF_disc x
  by_cases hne : ({i : ι | (V ∩ F i).Nonempty}).Nonempty
  · obtain ⟨i₀, hi₀⟩ := hne
    have hV'_open : IsOpen (V \ F i₀) := hV_open.sdiff (hF_closed i₀)
    have hxV' : x ∈ V \ F i₀ := ⟨hxV, fun h => hx (mem_iUnion.mpr ⟨i₀, h⟩)⟩
    have hsub : V \ F i₀ ⊆ (⋃ i, F i)ᶜ := by
      intro y ⟨hyV, hynot⟩ hyU
      obtain ⟨i, hyFi⟩ := mem_iUnion.mp hyU
      have hi_eq : i = i₀ := hsubsing ⟨y, hyV, hyFi⟩ hi₀
      subst hi_eq
      exact hynot hyFi
    exact Filter.mem_of_superset (hV'_open.mem_nhds hxV') hsub
  · have hsub : V ⊆ (⋃ i, F i)ᶜ := by
      intro y hyV hyU
      obtain ⟨i, hyFi⟩ := mem_iUnion.mp hyU
      exact hne ⟨i, y, hyV, hyFi⟩
    exact Filter.mem_of_superset (hV_open.mem_nhds hxV) hsub

lemma IsDiscreteFamily.finite_mem {X ι : Type*} [TopologicalSpace X] {U : ι → Set X}
    (hU : IsDiscreteFamily U) (x : X) : Set.Finite {i : ι | x ∈ U i} := by
  obtain ⟨V, _, hxV, hsubsing⟩ := hU x
  refine hsubsing.finite.subset ?_
  intro i hi
  exact ⟨x, hxV, hi⟩

lemma exists_closed_exhaustion_interior {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {G : Set X → ℕ → Set X}
    (hG_open : ∀ H n, IsOpen (G H n))
    (hG_sub : ∀ H, IsClosed H → ∀ n, H ⊆ G H n)
    (hG_inter : ∀ H, IsClosed H → (⋂ n, closure (G H n)) = H)
    {U : Set X} (hU : IsOpen U) :
    ∃ K : ℕ → Set X, K 0 = ∅ ∧ (∀ k, IsClosed (K k)) ∧
      (∀ k, K k ⊆ interior (K (k + 1))) ∧ (∀ k, K k ⊆ U) ∧ (⋃ k, K k) = U := by
  let G' : Set X → ℕ → Set X := shrinkingStrat G
  let D : ℕ → Set X := fun k => (G' Uᶜ k)ᶜ
  have hD_closed : ∀ k, IsClosed (D k) := fun k => (isOpen_shrinkingStrat hG_open Uᶜ k).isClosed_compl
  have hD_sub : ∀ k, D k ⊆ U := by
    intro k y hy
    by_contra hyU
    exact hy (subset_shrinkingStrat hG_sub hU.isClosed_compl k hyU)
  have hD_cover : (⋃ k, D k) = U := by
    apply Subset.antisymm
    · exact iUnion_subset hD_sub
    · intro y hyU
      have hU_eq : (⋂ k, closure (G' Uᶜ k)) = Uᶜ :=
        iInter_closure_shrinkingStrat hG_sub hG_inter hU.isClosed_compl
      have hnot : y ∉ ⋂ k, closure (G' Uᶜ k) := by
        rw [hU_eq]
        exact fun h => h hyU
      rw [mem_iInter] at hnot
      push Not at hnot
      obtain ⟨k, hk⟩ := hnot
      exact mem_iUnion.mpr ⟨k, fun hyG => hk (subset_closure hyG)⟩
  have hstep_exists : ∀ (k : ℕ) (S : {A : Set X // IsClosed A ∧ A ⊆ U}),
      ∃ W : Set X, IsOpen W ∧ (S.1 ∪ D k) ⊆ W ∧ closure W ⊆ U := by
    intro k S
    have hcl : IsClosed (S.1 ∪ D k) := S.2.1.union (hD_closed k)
    have hsub : S.1 ∪ D k ⊆ U := union_subset S.2.2 (hD_sub k)
    exact normal_exists_closure_subset hcl hU hsub
  let recPair : ℕ → {A : Set X // IsClosed A ∧ A ⊆ U} :=
    Nat.rec ⟨∅, isClosed_empty, empty_subset U⟩
      (fun k S =>
        let W := Classical.choose (hstep_exists k S)
        have hW := Classical.choose_spec (hstep_exists k S)
        ⟨closure W, isClosed_closure, hW.2.2⟩)
  let K : ℕ → Set X := fun k => (recPair k).1
  refine ⟨K, rfl, fun k => (recPair k).2.1, ?_, fun k => (recPair k).2.2, ?_⟩
  · intro k
    let S := recPair k
    let W := Classical.choose (hstep_exists k S)
    have hW := Classical.choose_spec (hstep_exists k S)
    have hKsucc : K (k + 1) = closure W := rfl
    rw [hKsucc]
    have hKW : K k ⊆ W := subset_union_left.trans hW.2.1
    exact hKW.trans (interior_maximal subset_closure hW.1)
  · apply Subset.antisymm
    · exact iUnion_subset (fun k => (recPair k).2.2)
    · rw [← hD_cover]
      refine iUnion_subset fun k => ?_
      let S := recPair k
      let W := Classical.choose (hstep_exists k S)
      have hW := Classical.choose_spec (hstep_exists k S)
      have hDK : D k ⊆ K (k + 1) := subset_union_right.trans (hW.2.1.trans subset_closure)
      exact hDK.trans (subset_iUnion K (k + 1))

lemma monotone_of_subset_interior_succ {X : Type*} [TopologicalSpace X] {K : ℕ → Set X}
    (hstep : ∀ k, K k ⊆ interior (K (k + 1))) : ∀ {m n : ℕ}, m ≤ n → K m ⊆ K n := by
  intro m n hmn
  induction hmn with
  | refl => exact Subset.rfl
  | step _ ih => exact ih.trans ((hstep _).trans interior_subset)

theorem mizokami_lemma_1_2 {X α : Type*} [TopologicalSpace X] [NormalSpace X]
    {G : Set X → ℕ → Set X}
    (hG_open : ∀ H n, IsOpen (G H n))
    (hG_sub : ∀ H, IsClosed H → ∀ n, H ⊆ G H n)
    (hG_inter : ∀ H, IsClosed H → (⋂ n, closure (G H n)) = H)
    (hexp : ∀ (F : α → Set X), (∀ a, IsClosed (F a)) → IsDiscreteFamily F →
      ∃ W : α → Set X, (∀ a, IsOpen (W a) ∧ F a ⊆ W a) ∧ IsDiscreteFamily W)
    {𝓝 : ℕ → α → Set X}
    (h𝓝_closed : ∀ n a, IsClosed (𝓝 n a))
    (h𝓝_disc : ∀ n, IsDiscreteFamily (𝓝 n))
    (h𝓝_net : ∀ (y : X) (U : Set X), IsOpen U → y ∈ U → ∃ n a, y ∈ 𝓝 n a ∧ 𝓝 n a ⊆ U)
    {𝓑 : Set (Set X)} (h𝓑_closed : ∀ B ∈ 𝓑, IsClosed B) (h𝓑_cp : MSpace.ClosurePreserving 𝓑) :
    ∃ (F V : ℕ → ℕ → α → Set X),
      (∀ n k a, IsClosed (F n k a)) ∧
      (∀ n k, IsDiscreteFamily (F n k)) ∧
      (⋃ n, ⋃ k, ⋃ a, F n k a) = univ ∧
      (∀ n k a, IsOpen (V n k a) ∧ F n k a ⊆ V n k a) ∧
      (∀ n k, IsDiscreteFamily (V n k)) ∧
      (∀ y : X, Set.Finite {p : ℕ × ℕ × α | y ∈ V p.1 p.2.1 p.2.2}) ∧
      (∀ n k a, ∀ B ∈ 𝓑, (F n k a ∩ B).Nonempty → F n k a ⊆ B) ∧
      (∀ n k a, ∀ B ∈ 𝓑, Disjoint (F n k a) B → Disjoint (V n k a) B) := by
  let E : ℕ → α → Set X := fun n a => atomClosed 𝓑 (𝓝 n a)
  have hE_closed : ∀ n a, IsClosed (E n a) := fun n a => isClosed_atomClosed h𝓑_closed (h𝓝_closed n a)
  have hE_disc : ∀ n, IsDiscreteFamily (E n) :=
    fun n => (h𝓝_disc n).mono (fun a => atomClosed_subset 𝓑 (𝓝 n a))
  let E_layer : ℕ → Set X := fun n => ⋃ a, E n a
  have hElayer_closed : ∀ n, IsClosed (E_layer n) :=
    fun n => (hE_disc n).isClosed_iUnion (hE_closed n)
  have hE_cover : ∀ y : X, ∃ n a, y ∈ E n a := by
    intro y
    let 𝓑_y : Set (Set X) := {B ∈ 𝓑 | y ∉ B}
    have h𝓑y_closed : IsClosed (⋃₀ 𝓑_y) := by
      have hcp := h𝓑_cp 𝓑_y (fun _ h => h.1)
      have himg : ⋃₀ (closure '' 𝓑_y) = ⋃₀ 𝓑_y := by
        ext z
        constructor
        · rintro ⟨_, ⟨B, hB, rfl⟩, hz⟩
          rw [(h𝓑_closed B hB.1).closure_eq] at hz
          exact ⟨B, hB, hz⟩
        · rintro ⟨B, hB, hz⟩
          exact ⟨closure B, ⟨B, hB, rfl⟩, subset_closure hz⟩
      rw [himg] at hcp
      rw [← hcp]
      exact isClosed_closure
    let Uy : Set X := (⋃₀ 𝓑_y)ᶜ
    have hUy_open : IsOpen Uy := h𝓑y_closed.isOpen_compl
    have hyUy : y ∈ Uy := by
      rintro ⟨B, ⟨_, hynotB⟩, hyB⟩
      exact hynotB hyB
    obtain ⟨n, a, hyN, hNUy⟩ := h𝓝_net y Uy hUy_open hyUy
    refine ⟨n, a, hyN, ?_⟩
    simp only [mem_iInter]
    intro B ⟨hB, z, hzN, hzB⟩
    by_contra hynotB
    exact hNUy hzN ⟨B, ⟨hB, hynotB⟩, hzB⟩
  have hW_ex : ∀ n, ∃ W : α → Set X, (∀ a, IsOpen (W a) ∧ E n a ⊆ W a) ∧ IsDiscreteFamily W :=
    fun n => hexp (E n) (hE_closed n) (hE_disc n)
  let W : ℕ → α → Set X := fun n => Classical.choose (hW_ex n)
  have hW_spec : ∀ n, (∀ a, IsOpen (W n a) ∧ E n a ⊆ W n a) ∧ IsDiscreteFamily (W n) :=
    fun n => Classical.choose_spec (hW_ex n)
  let V₀ : ℕ → α → Set X := fun n a => openAvoidingCP 𝓑 (E n a) (W n a)
  let U : ℕ → Set X := fun n => (⋃ i ∈ Set.Iio n, E_layer i)ᶜ
  have hU_open : ∀ n, IsOpen (U n) :=
    fun n => ((Set.finite_Iio n).isClosed_biUnion (fun i _ => hElayer_closed i)).isOpen_compl
  have hK_ex : ∀ n, ∃ K : ℕ → Set X, K 0 = ∅ ∧ (∀ k, IsClosed (K k)) ∧
      (∀ k, K k ⊆ interior (K (k + 1))) ∧ (∀ k, K k ⊆ U n) ∧ (⋃ k, K k) = U n :=
    fun n => exists_closed_exhaustion_interior hG_open hG_sub hG_inter (hU_open n)
  let K : ℕ → ℕ → Set X := fun n => Classical.choose (hK_ex n)
  have hK0 : ∀ n, K n 0 = ∅ := fun n => (Classical.choose_spec (hK_ex n)).1
  have hK_closed : ∀ n k, IsClosed (K n k) := fun n => (Classical.choose_spec (hK_ex n)).2.1
  have hK_step : ∀ n k, K n k ⊆ interior (K n (k + 1)) :=
    fun n => (Classical.choose_spec (hK_ex n)).2.2.1
  have hK_sub : ∀ n k, K n k ⊆ U n := fun n => (Classical.choose_spec (hK_ex n)).2.2.2.1
  have hK_cover : ∀ n, (⋃ k, K n k) = U n := fun n => (Classical.choose_spec (hK_ex n)).2.2.2.2
  let F : ℕ → ℕ → α → Set X := fun n k a => E n a ∩ (K n (k + 1) \ interior (K n k))
  let V : ℕ → ℕ → α → Set X := fun n k a => openAvoidingCP 𝓑 (F n k a) ((V₀ n a ∩ U n) \ K n (k - 1))
  have hF_sub_E : ∀ n k a, F n k a ⊆ E n a := fun _ _ _ => inter_subset_left
  have hV_sub_W : ∀ n k a, V n k a ⊆ W n a := by
    intro n k a z hz
    exact hz.1.1.1.1
  refine ⟨F, V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n k a
    exact (hE_closed n a).inter ((hK_closed n (k + 1)).sdiff isOpen_interior)
  · intro n k
    exact (hE_disc n).mono (hF_sub_E n k)
  · ext y
    simp only [mem_univ, iff_true]
    classical
    have hex_n : ∃ n, y ∈ E_layer n := by
      obtain ⟨n, a, hy⟩ := hE_cover y
      exact ⟨n, mem_iUnion.mpr ⟨a, hy⟩⟩
    let n₀ := Nat.find hex_n
    have hn₀ : y ∈ E_layer n₀ := Nat.find_spec hex_n
    obtain ⟨a₀, hya₀⟩ := mem_iUnion.mp hn₀
    have hyU : y ∈ U n₀ := by
      intro hmem
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hmem
      exact Nat.find_min hex_n (Set.mem_Iio.mp hi) hyi
    have hex_m : ∃ m, y ∈ K n₀ m := by
      rw [← hK_cover n₀] at hyU
      exact mem_iUnion.mp hyU
    let m₀ := Nat.find hex_m
    have hm₀ : y ∈ K n₀ m₀ := Nat.find_spec hex_m
    have hm₀_pos : m₀ ≠ 0 := by
      intro h0
      rw [h0, hK0 n₀] at hm₀
      exact hm₀
    obtain ⟨k₀, hk₀⟩ := Nat.exists_eq_succ_of_ne_zero hm₀_pos
    have hynot : y ∉ interior (K n₀ k₀) := by
      intro hint
      have hyK : y ∈ K n₀ k₀ := interior_subset hint
      have hlt : k₀ < m₀ := by rw [hk₀]; exact Nat.lt_succ_self k₀
      exact Nat.find_min hex_m hlt hyK
    refine mem_iUnion.mpr ⟨n₀, mem_iUnion.mpr ⟨k₀, mem_iUnion.mpr ⟨a₀, hya₀, ?_, hynot⟩⟩⟩
    rw [Nat.succ_eq_add_one] at hk₀
    rwa [← hk₀]
  · intro n k a
    have hV₀_open : IsOpen (V₀ n a) := isOpen_openAvoidingCP h𝓑_closed h𝓑_cp ((hW_spec n).1 a).1
    have hbase_open : IsOpen ((V₀ n a ∩ U n) \ K n (k - 1)) :=
      (hV₀_open.inter (hU_open n)).sdiff (hK_closed n (k - 1))
    refine ⟨isOpen_openAvoidingCP h𝓑_closed h𝓑_cp hbase_open, subset_openAvoidingCP ?_⟩
    intro z ⟨hzE, hzKsucc, hznotint⟩
    refine ⟨⟨subset_openAvoidingCP ((hW_spec n).1 a).2 hzE, hK_sub n (k + 1) hzKsucc⟩, ?_⟩
    cases k with
    | zero =>
      change z ∉ K n 0
      rw [hK0 n]
      exact Set.notMem_empty z
    | succ m =>
      change z ∉ K n m
      intro hzm
      exact hznotint (hK_step n m hzm)
  · intro n k
    exact (hW_spec n).2.mono (hV_sub_W n k)
  · intro y
    obtain ⟨n₀, a₀, hya₀⟩ := hE_cover y
    have hyElayer : y ∈ E_layer n₀ := mem_iUnion.mpr ⟨a₀, hya₀⟩
    have hsub : {p : ℕ × ℕ × α | y ∈ V p.1 p.2.1 p.2.2} ⊆
        ⋃ n ∈ Set.Iic n₀, {p : ℕ × ℕ × α | p.1 = n ∧ y ∈ V n p.2.1 p.2.2} := by
      intro p hp
      have hn_le : p.1 ≤ n₀ := by
        by_contra hgt
        push Not at hgt
        have hyUn : y ∈ U p.1 := hp.1.1.2
        exact hyUn (mem_biUnion (Set.mem_Iio.mpr hgt) hyElayer)
      exact mem_biUnion (Set.mem_Iic.mpr hn_le) ⟨rfl, hp⟩
    refine ((Set.finite_Iic n₀).biUnion fun n _ => ?_).subset hsub
    by_cases hyUn : y ∈ U n
    · rw [← hK_cover n] at hyUn
      obtain ⟨m, hym⟩ := mem_iUnion.mp hyUn
      have hsub_k : {p : ℕ × ℕ × α | p.1 = n ∧ y ∈ V n p.2.1 p.2.2} ⊆
          ⋃ k ∈ Set.Iic m, {p : ℕ × ℕ × α | p.1 = n ∧ p.2.1 = k ∧ y ∈ W n p.2.2} := by
        intro p ⟨hp1, hpV⟩
        have hk_le : p.2.1 ≤ m := by
          by_contra hgt
          push Not at hgt
          have hle : m ≤ p.2.1 - 1 := Nat.le_sub_one_of_lt hgt
          have hyKm : y ∈ K n (p.2.1 - 1) := monotone_of_subset_interior_succ (hK_step n) hle hym
          exact hpV.1.2 hyKm
        exact mem_biUnion (Set.mem_Iic.mpr hk_le) ⟨hp1, rfl, hV_sub_W n p.2.1 p.2.2 hpV⟩
      refine ((Set.finite_Iic m).biUnion fun k _ => ?_).subset hsub_k
      have hfin_a : Set.Finite {a : α | y ∈ W n a} := (hW_spec n).2.finite_mem y
      have hbij : {p : ℕ × ℕ × α | p.1 = n ∧ p.2.1 = k ∧ y ∈ W n p.2.2} ⊆
          (fun a => (n, k, a)) '' {a : α | y ∈ W n a} := by
        rintro ⟨p1, p2, a⟩ ⟨rfl, rfl, ha⟩
        exact ⟨a, ha, rfl⟩
      exact (hfin_a.image _).subset hbij
    · have hemp : {p : ℕ × ℕ × α | p.1 = n ∧ y ∈ V n p.2.1 p.2.2} = ∅ := by
        ext p
        simp only [mem_empty_iff_false, iff_false]
        rintro ⟨_, hpV⟩
        exact hyUn hpV.1.1.2
      rw [hemp]
      exact finite_empty
  · intro n k a B hB hne
    have hEne : (E n a ∩ B).Nonempty := hne.mono (inter_subset_inter_left B (hF_sub_E n k a))
    exact (hF_sub_E n k a).trans (atomClosed_subset_of_inter_nonempty hB hEne)
  · intro n k a B hB hdisj
    exact disjoint_openAvoidingCP hB hdisj

/-! ### カエル (Round4): 局所特徴づけ・1個正規版・第二可算版 SingleRegularOpenInsert -/

private lemma closure_biUnion_eq_of_locallyFinite
    {X ι : Type*} [TopologicalSpace X]
    {C : ι → Set X} (hlf : LocallyFinite C) (S : Set ι) :
    closure (⋃ i ∈ S, C i) = ⋃ i ∈ S, closure (C i) := by
  classical
  refine Subset.antisymm ?_ (iUnion₂_subset (fun i hi => closure_mono (subset_biUnion_of_mem hi)))
  have hEq : (⋃ i ∈ S, closure (C i)) = (⋃ i : ι, if i ∈ S then closure (C i) else ∅) := by
    ext y
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, hiS, hy⟩; exact ⟨i, by simp [hiS, hy]⟩
    · rintro ⟨i, hy⟩
      by_cases hi : i ∈ S
      · simp [hi] at hy; exact ⟨i, hi, hy⟩
      · simp [hi] at hy
  rw [hEq]
  apply closure_minimal
  · intro y hy
    rcases mem_iUnion₂.1 hy with ⟨i, hiS, hyi⟩
    exact mem_iUnion.2 ⟨i, by simp [hiS, subset_closure hyi]⟩
  · have hlf_sub : LocallyFinite (fun i : ι => if i ∈ S then closure (C i) else ∅) := by
      intro x
      obtain ⟨M, hM, hFin⟩ := hlf.closure x
      refine ⟨M, hM, hFin.subset ?_⟩
      intro i ⟨y, hy1, hy2⟩
      by_cases hi : i ∈ S
      · simp [hi] at hy1; exact ⟨y, hy1, hy2⟩
      · simp [hi] at hy1
    apply hlf_sub.isClosed_iUnion
    intro i
    by_cases hi : i ∈ S
    · simp [hi, isClosed_closure]
    · simp [hi]

theorem isRegularOpen_iUnion_iff_frontier_escape
    {X ι : Type*} [TopologicalSpace X]
    (C : ι → Set X) (hCopen : ∀ i, IsOpen (C i)) (hlf : LocallyFinite C) :
    (∀ S : Set ι, IsRegularOpen (⋃ i ∈ S, C i)) ↔
      ∀ p : X, p ∉ interior (⋃ i ∈ {i : ι | p ∈ frontier (C i)}, closure (C i)) := by
  classical
  constructor
  · intro hReg p hp
    let S : Set ι := {i : ι | p ∈ frontier (C i)}
    have hpCl : p ∈ interior (closure (⋃ i ∈ S, C i)) := by
      rwa [closure_biUnion_eq_of_locallyFinite hlf S]
    rw [(hReg S).2] at hpCl
    rcases mem_iUnion₂.1 hpCl with ⟨i, hiS, hpi⟩
    have hnot : p ∉ interior (C i) := hiS.2
    rw [(hCopen i).interior_eq] at hnot
    exact hnot hpi
  · intro hEsc S
    have hOpen : IsOpen (⋃ i ∈ S, C i) := isOpen_biUnion (fun i _ => hCopen i)
    refine ⟨hOpen, Subset.antisymm ?_ (interior_maximal subset_closure hOpen)⟩
    intro p hp
    by_contra hpNot
    let K : Set X := ⋃ i : ι, if i ∈ S ∧ p ∉ closure (C i) then closure (C i) else ∅
    have hKcl : IsClosed K := by
      have hlf_K : LocallyFinite (fun i : ι => if i ∈ S ∧ p ∉ closure (C i) then closure (C i) else ∅) := by
        intro x
        obtain ⟨M, hM, hFin⟩ := hlf.closure x
        refine ⟨M, hM, hFin.subset ?_⟩
        intro i ⟨y, hy1, hy2⟩
        by_cases hcond : i ∈ S ∧ p ∉ closure (C i)
        · simp [hcond] at hy1; exact ⟨y, hy1, hy2⟩
        · simp [hcond] at hy1
      apply hlf_K.isClosed_iUnion
      intro i
      by_cases hcond : i ∈ S ∧ p ∉ closure (C i)
      · simp [hcond, isClosed_closure]
      · simp [hcond]
    have hpNotK : p ∉ K := by
      intro hpK
      dsimp only [K] at hpK
      rcases mem_iUnion.1 hpK with ⟨i, hi⟩
      by_cases hcond : i ∈ S ∧ p ∉ closure (C i)
      · simp [hcond] at hi
      · simp [hcond] at hi
    have hOsub : interior (closure (⋃ i ∈ S, C i)) \ K ⊆
        ⋃ i ∈ {i : ι | p ∈ frontier (C i)}, closure (C i) := by
      intro y ⟨hyInt, hyNotK⟩
      have hyCl : y ∈ ⋃ i ∈ S, closure (C i) := by
        rw [← closure_biUnion_eq_of_locallyFinite hlf S]
        exact interior_subset hyInt
      rcases mem_iUnion₂.1 hyCl with ⟨i, hiS, hyi⟩
      have hpiCl : p ∈ closure (C i) := by
        by_contra hnot
        exact hyNotK (mem_iUnion.2 ⟨i, by simp [hiS, hnot, hyi]⟩)
      have hpiFr : p ∈ frontier (C i) := by
        refine ⟨hpiCl, ?_⟩
        rw [(hCopen i).interior_eq]
        intro hpi
        exact hpNot (mem_iUnion₂.2 ⟨i, hiS, hpi⟩)
      exact mem_iUnion₂.2 ⟨i, hpiFr, hyi⟩
    exact hEsc p (mem_interior.2 ⟨interior (closure (⋃ i ∈ S, C i)) \ K,
      hOsub, isOpen_interior.sdiff hKcl, ⟨hp, hpNotK⟩⟩)

theorem singleInsert_iff_frontier_escape_cond
    {X α : Type*} [TopologicalSpace X]
    (A : α → Set X) (hAopen : ∀ a, IsOpen (A a)) (hAlf : LocallyFinite A)
    (hAreg : ∀ S : Set α, IsRegularOpen (⋃ a ∈ S, A a))
    (W : Set X) (hWopen : IsOpen W) :
    (IsRegularOpen W ∧ ∀ S : Set α, IsRegularOpen (W ∪ ⋃ a ∈ S, A a)) ↔
      ∀ p ∈ frontier W,
        p ∈ closure ((⋃ a ∈ {a : α | p ∈ frontier (A a)}, closure (A a))ᶜ \ closure W) := by
  classical
  let C : Option α → Set X
    | none => W
    | some a => A a
  have hCopen : ∀ o, IsOpen (C o) := by
    rintro (_ | a)
    · exact hWopen
    · exact hAopen a
  have hClf : LocallyFinite C := by
    intro x
    obtain ⟨M, hM, hFin⟩ := hAlf x
    refine ⟨M, hM, ?_⟩
    have hSub : {o : Option α | (C o ∩ M).Nonempty} ⊆
        insert none (Option.some '' {a : α | (A a ∩ M).Nonempty}) := by
      rintro (_ | a) ⟨y, hyC, hyM⟩
      · exact mem_insert none _
      · exact mem_insert_of_mem none ⟨a, ⟨y, hyC, hyM⟩, rfl⟩
    exact ((hFin.image Option.some).insert none).subset hSub
  have hEquivAll : (IsRegularOpen W ∧ ∀ S : Set α, IsRegularOpen (W ∪ ⋃ a ∈ S, A a)) ↔
      (∀ T : Set (Option α), IsRegularOpen (⋃ o ∈ T, C o)) := by
    constructor
    · rintro ⟨_, hWA⟩ T
      by_cases hnone : none ∈ T
      · let S : Set α := {a : α | some a ∈ T}
        have hEq : (⋃ o ∈ T, C o) = W ∪ ⋃ a ∈ S, A a := by
          ext y
          simp only [mem_union, mem_iUnion, exists_prop]
          constructor
          · rintro ⟨_ | a, hoT, hy⟩
            · exact Or.inl hy
            · exact Or.inr ⟨a, hoT, hy⟩
          · rintro (hyW | ⟨a, haS, hyA⟩)
            · exact ⟨none, hnone, hyW⟩
            · exact ⟨some a, haS, hyA⟩
        rw [hEq]; exact hWA S
      · let S : Set α := {a : α | some a ∈ T}
        have hEq : (⋃ o ∈ T, C o) = ⋃ a ∈ S, A a := by
          ext y
          simp only [mem_iUnion, exists_prop]
          constructor
          · rintro ⟨_ | a, hoT, hy⟩
            · exact False.elim (hnone hoT)
            · exact ⟨a, hoT, hy⟩
          · rintro ⟨a, haS, hyA⟩
            exact ⟨some a, haS, hyA⟩
        rw [hEq]; exact hAreg S
    · intro hAll
      refine ⟨?_, ?_⟩
      · have hEq : W = ⋃ o ∈ ({none} : Set (Option α)), C o := by
          ext y; simp [C]
        rw [hEq]; exact hAll {none}
      · intro S
        let T : Set (Option α) := insert none (Option.some '' S)
        have hEq : (W ∪ ⋃ a ∈ S, A a) = ⋃ o ∈ T, C o := by
          ext y
          simp only [mem_union, mem_iUnion, exists_prop, T, mem_insert_iff, mem_image]
          constructor
          · rintro (hyW | ⟨a, haS, hyA⟩)
            · exact ⟨none, Or.inl rfl, hyW⟩
            · exact ⟨some a, Or.inr ⟨a, haS, rfl⟩, hyA⟩
          · rintro ⟨_ | a, (h1 | ⟨b, hbS, h2⟩), hy⟩
            · exact Or.inl hy
            · cases h2
            · cases h1
            · cases Option.some.inj h2; exact Or.inr ⟨a, hbS, hy⟩
        rw [hEq]; exact hAll T
  rw [hEquivAll, isRegularOpen_iUnion_iff_frontier_escape C hCopen hClf]
  have hAesc := (isRegularOpen_iUnion_iff_frontier_escape A hAopen hAlf).1 hAreg
  constructor
  · intro hCesc p hpW
    have hEqSet : ((⋃ a ∈ {a : α | p ∈ frontier (A a)}, closure (A a))ᶜ \ closure W) =
        (⋃ o ∈ {o : Option α | p ∈ frontier (C o)}, closure (C o))ᶜ := by
      ext y
      simp only [Set.mem_sdiff, mem_compl_iff, mem_iUnion, exists_prop, not_exists, not_and]
      constructor
      · rintro ⟨h1, h2⟩ (_ | a) hfr
        · exact h2
        · exact h1 a hfr
      · intro h
        refine ⟨fun a ha => h (some a) ha, h none hpW⟩
    rw [hEqSet, mem_closure_iff]
    intro O hO hpO
    by_contra hEmp
    rw [Set.not_nonempty_iff_eq_empty] at hEmp
    have hOsub : O ⊆ ⋃ o ∈ {o : Option α | p ∈ frontier (C o)}, closure (C o) := by
      intro y hyO
      by_contra hnot
      have : y ∈ O ∩ (⋃ o ∈ {o : Option α | p ∈ frontier (C o)}, closure (C o))ᶜ := ⟨hyO, hnot⟩
      rw [hEmp] at this
      exact this
    exact hCesc p (mem_interior.2 ⟨O, hOsub, hO, hpO⟩)
  · intro hWesc p hpInt
    by_cases hpW : p ∈ frontier W
    · have hCl := hWesc p hpW
      rcases mem_closure_iff.1 hCl _ isOpen_interior hpInt with ⟨y, hyInt, hyNotA, hyNotW⟩
      have hyU := interior_subset hyInt
      rcases mem_iUnion₂.1 hyU with ⟨_ | a, hfr, hyC⟩
      · exact hyNotW hyC
      · exact hyNotA (mem_iUnion₂.2 ⟨a, hfr, hyC⟩)
    · have hSub : (⋃ o ∈ {o : Option α | p ∈ frontier (C o)}, closure (C o)) ⊆
          (⋃ a ∈ {a : α | p ∈ frontier (A a)}, closure (A a)) := by
        intro y hy
        rcases mem_iUnion₂.1 hy with ⟨_ | a, hfr, hyC⟩
        · exact False.elim (hpW hfr)
        · exact mem_iUnion₂.2 ⟨a, hfr, hyC⟩
      exact hAesc p (interior_mono hSub hpInt)

private lemma isRegularOpen_interior_closure {X : Type*} [TopologicalSpace X] (s : Set X) :
    IsRegularOpen (interior (closure s)) := by
  refine ⟨isOpen_interior, Subset.antisymm ?_ (interior_maximal subset_closure isOpen_interior)⟩
  exact interior_mono (closure_minimal interior_subset isClosed_closure)

theorem singleRegularOpenInsert_singleton_normal
    {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A F G : Set X} (hA : IsRegularOpen A)
    (hF : IsClosed F) (hG : IsOpen G) (hFG : F ⊆ G) :
    ∃ W : Set X, IsRegularOpen W ∧ F ⊆ W ∧ closure W ⊆ G ∧ IsRegularOpen (W ∪ A) := by
  obtain ⟨U₂, hU₂open, hFU₂, hU₂G⟩ := normal_exists_closure_subset hF hG hFG
  obtain ⟨U₁, hU₁open, hFU₁, hU₁U₂⟩ := normal_exists_closure_subset hF hU₂open hFU₂
  let W : Set X := interior (closure (U₁ ∪ (A ∩ U₂)))
  have hWreg : IsRegularOpen W := isRegularOpen_interior_closure (U₁ ∪ (A ∩ U₂))
  have hFW : F ⊆ W :=
    hFU₁.trans (interior_maximal (subset_union_left.trans subset_closure) hU₁open)
  have hWclG : closure W ⊆ G := by
    have hSub : U₁ ∪ (A ∩ U₂) ⊆ closure U₂ :=
      union_subset ((subset_closure.trans hU₁U₂).trans subset_closure)
        (inter_subset_right.trans subset_closure)
    have hWsub : W ⊆ closure U₂ := interior_subset.trans (closure_minimal hSub isClosed_closure)
    exact (closure_minimal hWsub isClosed_closure).trans hU₂G
  have hWAopen : IsOpen (W ∪ A) := hWreg.1.union hA.1
  refine ⟨W, hWreg, hFW, hWclG, hWAopen,
    Subset.antisymm ?_ (interior_maximal subset_closure hWAopen)⟩
  have hWAcl : closure (W ∪ A) ⊆ closure U₁ ∪ closure A := by
    apply closure_minimal _ (isClosed_closure.union isClosed_closure)
    refine union_subset ?_ (subset_closure.trans subset_union_right)
    calc W ⊆ closure (U₁ ∪ (A ∩ U₂)) := interior_subset
      _ = closure U₁ ∪ closure (A ∩ U₂) := closure_union
      _ ⊆ closure U₁ ∪ closure A := union_subset_union_right _ (closure_mono inter_subset_left)
  intro p hp
  by_cases hpU₂ : p ∈ U₂
  · left
    refine mem_interior.2 ⟨interior (closure (W ∪ A)) ∩ U₂, ?_, isOpen_interior.inter hU₂open, ⟨hp, hpU₂⟩⟩
    intro y ⟨hyInt, hyU₂⟩
    rcases hWAcl (interior_subset hyInt) with hyU₁ | hyA
    · exact closure_mono subset_union_left hyU₁
    · apply closure_mono subset_union_right
      rw [mem_closure_iff]
      intro N hN hyN
      rcases mem_closure_iff.1 hyA (N ∩ U₂) (hN.inter hU₂open) ⟨hyN, hyU₂⟩ with ⟨z, ⟨hzN, hzU₂⟩, hzA⟩
      exact ⟨z, hzN, hzA, hzU₂⟩
  · right
    have hpNotU₁ : p ∉ closure U₁ := fun h => hpU₂ (hU₁U₂ h)
    have hpIntA : p ∈ interior (closure A) := by
      refine mem_interior.2 ⟨interior (closure (W ∪ A)) \ closure U₁, ?_,
        isOpen_interior.sdiff isClosed_closure, ⟨hp, hpNotU₁⟩⟩
      intro y ⟨hyInt, hyNotU₁⟩
      rcases hWAcl (interior_subset hyInt) with hyU₁ | hyA
      · exact False.elim (hyNotU₁ hyU₁)
      · exact hyA
    rwa [hA.2] at hpIntA

theorem singleRegularOpenInsert_secondCountable
    {X : Type} [TopologicalSpace X] [NormalSpace X] [SecondCountableTopology X]
    {α : Type} (A : α → Set X)
    (hAopen : ∀ a, IsOpen (A a)) (hAlf : LocallyFinite A)
    (hAreg : ∀ S : Set α, IsRegularOpen (⋃ a ∈ S, A a))
    {F G : Set X} (hF : IsClosed F) (hG : IsOpen G) (hFG : F ⊆ G) :
    ∃ W : Set X, IsRegularOpen W ∧ F ⊆ W ∧ closure W ⊆ G ∧
      ∀ S : Set α, IsRegularOpen (W ∪ (⋃ a ∈ S, A a)) := by
  classical
  have hDisj : Disjoint F Gᶜ := Set.disjoint_compl_right_iff_subset.2 hFG
  obtain ⟨f, hfF, hfGc, _⟩ :=
    exists_continuous_zero_one_of_isClosed hF hG.isClosed_compl hDisj
  have hfCont : Continuous f := f.continuous
  obtain ⟨B₀, hB₀cnt, _, hB₀basis⟩ := TopologicalSpace.exists_countable_basis X
  let B₁ : Set (Set X) := {B ∈ B₀ | {a : α | (closure (A a) ∩ B).Nonempty}.Finite}
  have hB₁cnt : B₁.Countable := hB₀cnt.mono (fun _ h => h.1)
  have hB₁open : ∀ B ∈ B₁, IsOpen B := fun B hB => hB₀basis.isOpen hB.1
  let Bad (B : Set X) (S : Set α) : Set ℝ :=
    {t : ℝ | ∃ p ∈ B \ (⋃ a ∈ S, A a), (∀ x ∈ B \ (⋃ a ∈ S, A a), f x ≤ f p) ∧ f p = t}
  have hBadSub : ∀ B S, (Bad B S).Subsingleton := by
    intro B S t₁ ⟨p₁, hp₁, hmax₁, ht₁⟩ t₂ ⟨p₂, hp₂, hmax₂, ht₂⟩
    rw [← ht₁, ← ht₂]
    exact le_antisymm (hmax₂ p₁ hp₁) (hmax₁ p₂ hp₂)
  let E : Set ℝ :=
    ⋃ B ∈ B₁, ⋃ S ∈ {S : Set α | S ⊆ {a : α | (closure (A a) ∩ B).Nonempty}}, Bad B S
  have hEcnt : E.Countable := by
    refine hB₁cnt.biUnion (fun B hB => ?_)
    have hPowCnt : {S : Set α | S ⊆ {a : α | (closure (A a) ∩ B).Nonempty}}.Countable :=
      hB.2.powerset.countable
    exact hPowCnt.biUnion (fun S _ => (hBadSub B S).countable)
  have hIooUncnt : ¬ (Set.Ioo (0 : ℝ) 1).Countable := by simp
  have htEx : ∃ t₀ ∈ Set.Ioo (0 : ℝ) 1, t₀ ∉ E := by
    by_contra hAll
    push Not at hAll
    exact hIooUncnt (hEcnt.mono hAll)
  obtain ⟨t₀, ⟨ht₀_pos, ht₀_lt⟩, ht₀NotE⟩ := htEx
  let W : Set X := interior (closure (f ⁻¹' Set.Iio t₀))
  have hWreg : IsRegularOpen W := isRegularOpen_interior_closure (f ⁻¹' Set.Iio t₀)
  have hFW : F ⊆ W := by
    have hSub : F ⊆ f ⁻¹' Set.Iio t₀ := by
      intro x hx; show f x < t₀; rw [hfF hx]; exact ht₀_pos
    exact hSub.trans (interior_maximal subset_closure (isOpen_Iio.preimage hfCont))
  have hWclIic : closure W ⊆ f ⁻¹' Set.Iic t₀ := by
    have h1 : closure (f ⁻¹' Set.Iio t₀) ⊆ f ⁻¹' Set.Iic t₀ :=
      closure_minimal (fun x (hx : f x < t₀) => le_of_lt hx) (isClosed_Iic.preimage hfCont)
    exact closure_minimal (interior_subset.trans h1) (isClosed_Iic.preimage hfCont)
  have hWclG : closure W ⊆ G := by
    intro x hx
    by_contra hxGc
    have hle : f x ≤ t₀ := hWclIic hx
    rw [hfGc hxGc] at hle
    exact not_lt_of_ge hle ht₀_lt
  refine ⟨W, hWreg, hFW, hWclG, ?_⟩
  intro S
  have hOpen : IsOpen (W ∪ ⋃ a ∈ S, A a) := hWreg.1.union (isOpen_biUnion (fun a _ => hAopen a))
  refine ⟨hOpen, Subset.antisymm ?_ (interior_maximal subset_closure hOpen)⟩
  intro p hp
  by_contra hpNot
  have hpNotW : p ∉ W := fun h => hpNot (Or.inl h)
  have hpNotA : p ∉ ⋃ a ∈ S, A a := fun h => hpNot (Or.inr h)
  obtain ⟨M, hM, hFinM⟩ := hAlf.closure p
  have hOopen : IsOpen (interior (closure (W ∪ ⋃ a ∈ S, A a)) ∩ interior M) :=
    isOpen_interior.inter isOpen_interior
  have hpO : p ∈ interior (closure (W ∪ ⋃ a ∈ S, A a)) ∩ interior M :=
    ⟨hp, mem_interior_iff_mem_nhds.2 hM⟩
  obtain ⟨B, hBB₀, hpB, hBsub⟩ := hB₀basis.exists_subset_of_mem_open hpO hOopen
  have hBB₁ : B ∈ B₁ := ⟨hBB₀, hFinM.subset (fun a ⟨y, hyA, hyB⟩ =>
    ⟨y, hyA, interior_subset (hBsub hyB).2⟩)⟩
  let S_B : Set α := {a ∈ S | (closure (A a) ∩ B).Nonempty}
  have hSBsub : S_B ⊆ {a : α | (closure (A a) ∩ B).Nonempty} := fun _ h => h.2
  have hfp_eq : f p = t₀ := by
    have hge : t₀ ≤ f p := by
      by_contra hlt
      push Not at hlt
      exact hpNotW (interior_maximal subset_closure (isOpen_Iio.preimage hfCont) hlt)
    have hle : f p ≤ t₀ := by
      by_contra hgt
      push Not at hgt
      have hSubA : B ∩ f ⁻¹' Set.Ioi t₀ ⊆ closure (⋃ a ∈ S, A a) := by
        intro y ⟨hyB, hyGt⟩
        have hyCl : y ∈ closure W ∪ closure (⋃ a ∈ S, A a) := by
          rw [← closure_union]; exact interior_subset (hBsub hyB).1
        rcases hyCl with hyW | hyA
        · exact False.elim (not_lt_of_ge (hWclIic hyW) (show t₀ < f y from hyGt))
        · exact hyA
      have hpIntA : p ∈ interior (closure (⋃ a ∈ S, A a)) :=
        mem_interior.2 ⟨B ∩ f ⁻¹' Set.Ioi t₀, hSubA,
          (hB₁open B hBB₁).inter (isOpen_Ioi.preimage hfCont), ⟨hpB, hgt⟩⟩
      rw [(hAreg S).2] at hpIntA
      exact hpNotA hpIntA
    exact le_antisymm hle hge
  have hMax : ∀ x ∈ B \ (⋃ a ∈ S_B, A a), f x ≤ f p := by
    intro x ⟨hxB, hxNotSB⟩
    rw [hfp_eq]
    by_contra hgt
    push Not at hgt
    have hSubSB : B ∩ f ⁻¹' Set.Ioi t₀ ⊆ closure (⋃ a ∈ S_B, A a) := by
      intro y ⟨hyB, hyGt⟩
      have hyCl : y ∈ closure W ∪ closure (⋃ a ∈ S, A a) := by
        rw [← closure_union]; exact interior_subset (hBsub hyB).1
      rcases hyCl with hyW | hyA
      · exact False.elim (not_lt_of_ge (hWclIic hyW) (show t₀ < f y from hyGt))
      · rw [closure_biUnion_eq_of_locallyFinite hAlf S] at hyA
        rcases mem_iUnion₂.1 hyA with ⟨a, haS, hya⟩
        have haSB : a ∈ S_B := ⟨haS, y, hya, hyB⟩
        exact closure_mono (subset_biUnion_of_mem haSB) hya
    have hxIntSB : x ∈ interior (closure (⋃ a ∈ S_B, A a)) :=
      mem_interior.2 ⟨B ∩ f ⁻¹' Set.Ioi t₀, hSubSB,
        (hB₁open B hBB₁).inter (isOpen_Ioi.preimage hfCont), ⟨hxB, hgt⟩⟩
    rw [(hAreg S_B).2] at hxIntSB
    exact hxNotSB hxIntSB
  have hpDiff : p ∈ B \ (⋃ a ∈ S_B, A a) :=
    ⟨hpB, fun h => hpNotA (by
      rcases mem_iUnion₂.1 h with ⟨a, haSB, hpa⟩
      exact mem_iUnion₂.2 ⟨a, haSB.1, hpa⟩)⟩
  exact ht₀NotE (mem_iUnion₂.2 ⟨B, hBB₁, mem_iUnion₂.2 ⟨S_B, hSBsub, ⟨p, hpDiff, hMax, hfp_eq⟩⟩⟩)

end Work.L0028Helpers
