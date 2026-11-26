import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.Compactness.Paracompact
import Targets
import Proofs.L_0005
import Proofs.L_0008
import Proofs.L_0010

/-!
# Structural Theorems for M₃ / M₁ Spaces (Kernel-Verified)

This file formalizes four classical structural theorems in generalized metric
spaces that support the `M₃ ⇒ M₁` (`Tinf`) and `L_0028` / Ito / Mizokami
research tracks:

1. `M3_is_sigma_space` (Heath 1969): Every M₃ (stratifiable) space has a
   `σ`-discrete closed network.
2. `M3_closed_subset_has_cp_closed_nhds`: Every closed subset `F` of an M₃ space
   admits a closure-preserving closed neighborhood base (generalizing `L_0021`
   from points in M₁ spaces to arbitrary closed subsets in M₃ spaces).
3. `zero_dim_M1_has_cp_clopen_base`: Every point in a zero-dimensional M₁ space
   (having a `σ`-CP basis of clopen sets) admits a closure-preserving clopen
   (hence both open and regular-closed) neighborhood base (`L_0028` for
   zero-dimensional M₁ spaces).
4. `collectionwise_normal_of_paracompact_t3`: Every discrete family of closed
   sets in a paracompact `T3Space` (in particular, any M₃ space) admits a
   discrete open expansion with pairwise disjoint closures.
-/

namespace Research.M3M1

open MSpace Set TopologicalSpace Topology

/-- Theorem 1 (Heath 1969): Every M₃ space is a `σ`-space, i.e., it admits a
`σ`-discrete closed network `𝓝 : ℕ → Set (Set X)`. -/
theorem M3_is_sigma_space (X : Type) [TopologicalSpace X] (hM3 : MSpace.IsM3 X) :
    ∃ 𝓕 : ℕ → Set (Set X),
      (∀ m, ∀ H ∈ 𝓕 m, IsClosed H) ∧
      (∀ m, ∀ y : X, ∃ O : Set X, IsOpen O ∧ y ∈ O ∧
        ∀ H₁ ∈ 𝓕 m, ∀ H₂ ∈ 𝓕 m, (O ∩ H₁).Nonempty → (O ∩ H₂).Nonempty → H₁ = H₂) ∧
      (∀ x : X, ∀ U : Set X, IsOpen U → x ∈ U → ∃ m, ∃ H ∈ 𝓕 m, x ∈ H ∧ H ⊆ U) := by
  have : T3Space X := hM3.1
  have hM2 : MSpace.IsM2 X := Proofs.L_0008.main X hM3
  obtain ⟨_, 𝓑, h𝓑_qb, 𝓑', h𝓑'_cp, h𝓑_eq⟩ := hM2
  obtain ⟨G, hG_open, hG_sub, hG_inter, hG_mono⟩ := Proofs.L_0010.main X hM3
  let F : ℕ → Set X → Set X := fun k U => (G k Uᶜ)ᶜ
  have hF_closed : ∀ k U, IsOpen U → IsClosed (F k U) := fun k U hU =>
    (hG_open k Uᶜ hU.isClosed_compl).isClosed_compl
  have hF_sub : ∀ k U, IsOpen U → F k U ⊆ U := fun k U hU =>
    compl_subset_comm.mp (hG_sub k Uᶜ hU.isClosed_compl)
  have hF_mono : ∀ k U V, IsOpen U → IsOpen V → U ⊆ V → F k U ⊆ F k V :=
    fun k U V hU hV hUV =>
      compl_subset_compl.mpr
        (hG_mono k Vᶜ Uᶜ hV.isClosed_compl hU.isClosed_compl (compl_subset_compl.mpr hUV))
  have hF_cover : ∀ U, IsOpen U → ∀ x ∈ U, ∃ k, x ∈ F k U := by
    intro U hU x hx
    have hx' : x ∉ Uᶜ := fun h => h hx
    rw [← hG_inter Uᶜ hU.isClosed_compl, mem_iInter] at hx'
    push Not at hx'
    obtain ⟨k, hk⟩ := hx'
    exact ⟨k, fun h => hk (subset_closure h)⟩
  let 𝓒 : ℕ → Set (Set X) := fun n => closure '' 𝓑' n
  have h𝓒_sUnion_closed : ∀ n, ∀ 𝓖 ⊆ 𝓒 n, IsClosed (⋃₀ 𝓖) := by
    intro n 𝓖 h𝓖
    let 𝓖₀ : Set (Set X) := { B ∈ 𝓑' n | closure B ∈ 𝓖 }
    have himg : closure '' 𝓖₀ = 𝓖 := by
      ext C
      constructor
      · rintro ⟨B, hB, rfl⟩; exact hB.2
      · intro hC
        obtain ⟨B, hB, rfl⟩ := h𝓖 hC
        exact ⟨B, ⟨hB, hC⟩, rfl⟩
    have hcp := h𝓑'_cp n 𝓖₀ (fun _ h => h.1)
    rw [himg] at hcp
    rw [← hcp]
    exact isClosed_closure
  let M : ℕ → X → Set X := fun n x => ⋂₀ { C ∈ 𝓒 n | x ∈ C }
  let W : ℕ → X → Set X := fun n x => (⋃₀ { C ∈ 𝓒 n | x ∉ C })ᶜ
  let H : ℕ → ℕ → X → Set X := fun n k x => M n x ∩ F k (W n x)
  have hW_open : ∀ n x, IsOpen (W n x) := fun n x =>
    (h𝓒_sUnion_closed n { C ∈ 𝓒 n | x ∉ C } (fun _ h => h.1)).isOpen_compl
  have hW_mem : ∀ n x, x ∈ W n x := by
    intro n x ⟨C, ⟨_, hxC⟩, hxC'⟩; exact hxC hxC'
  have hM_mem : ∀ n x, x ∈ M n x := fun n x _ hC => hC.2
  have hM_closed : ∀ n x, IsClosed (M n x) := by
    intro n x
    refine isClosed_sInter fun C hC => ?_
    obtain ⟨B, _, rfl⟩ := hC.1
    exact isClosed_closure
  have hH_closed : ∀ n k x, IsClosed (H n k x) := fun n k x =>
    (hM_closed n x).inter (hF_closed k (W n x) (hW_open n x))
  have hH_equiv : ∀ n k a w, w ∈ H n k a → ∀ C ∈ 𝓒 n, w ∈ C ↔ a ∈ C := by
    intro n k a w hw C hC
    constructor
    · intro hwC
      by_contra haC
      exact (hF_sub k (W n a) (hW_open n a) hw.2) ⟨C, ⟨hC, haC⟩, hwC⟩
    · intro haC
      exact hw.1 C ⟨hC, haC⟩
  have hH_eq_of_equiv : ∀ n k a b, (∀ C ∈ 𝓒 n, a ∈ C ↔ b ∈ C) → H n k a = H n k b := by
    intro n k a b hab
    have hM : M n a = M n b := by
      dsimp only [M]; congr 1; ext C
      exact ⟨fun ⟨hC, ha⟩ => ⟨hC, (hab C hC).mp ha⟩, fun ⟨hC, hb⟩ => ⟨hC, (hab C hC).mpr hb⟩⟩
    have hW : W n a = W n b := by
      dsimp only [W]; congr 2; ext C
      exact ⟨fun ⟨hC, ha⟩ => ⟨hC, fun hb => ha ((hab C hC).mpr hb)⟩,
             fun ⟨hC, hb⟩ => ⟨hC, fun ha => hb ((hab C hC).mp ha)⟩⟩
    dsimp only [H]; rw [hM, hW]
  have hH_union_closed : ∀ n k (A : Set X), IsClosed (⋃ a ∈ A, H n k a) := by
    intro n k A
    rw [← closure_subset_iff_isClosed]
    intro z hz
    by_contra hnot
    by_cases hzF : z ∈ F k (W n z)
    · let O : Set X := W n z \ F k ({z}ᶜ)
      have hzc_open : IsOpen ({z}ᶜ : Set X) := isClosed_singleton.isOpen_compl
      have hO_open : IsOpen O := (hW_open n z).sdiff (hF_closed k ({z}ᶜ) hzc_open)
      have hO_mem : z ∈ O := ⟨hW_mem n z, fun h => (hF_sub k ({z}ᶜ) hzc_open h) rfl⟩
      obtain ⟨w, hwO, hwU⟩ := mem_closure_iff.mp hz O hO_open hO_mem
      obtain ⟨a, haA, hwH⟩ := mem_iUnion₂.mp hwU
      have h_imp : ∀ C ∈ 𝓒 n, a ∈ C → z ∈ C := by
        intro C hC haC
        have hwC : w ∈ C := (hH_equiv n k a w hwH C hC).mpr haC
        by_contra hzC
        exact hwO.1 ⟨C, ⟨hC, hzC⟩, hwC⟩
      have h_not_all : ¬ (∀ C ∈ 𝓒 n, z ∈ C → a ∈ C) := by
        intro hrev
        have heq : H n k a = H n k z :=
          hH_eq_of_equiv n k a z (fun C hC => ⟨h_imp C hC, hrev C hC⟩)
        have hzHz : z ∈ H n k z := ⟨hM_mem n z, hzF⟩
        rw [← heq] at hzHz
        exact hnot (mem_iUnion₂.mpr ⟨a, haA, hzHz⟩)
      push Not at h_not_all
      obtain ⟨C₀, hC₀, hzC₀, haC₀⟩ := h_not_all
      have hWa_sub : W n a ⊆ ({z}ᶜ : Set X) := by
        intro u hu huz
        rw [mem_singleton_iff] at huz; subst huz
        exact hu ⟨C₀, ⟨hC₀, haC₀⟩, hzC₀⟩
      exact hwO.2 (hF_mono k (W n a) ({z}ᶜ) (hW_open n a) hzc_open hWa_sub hwH.2)
    · let O : Set X := W n z \ F k (W n z)
      have hO_open : IsOpen O := (hW_open n z).sdiff (hF_closed k (W n z) (hW_open n z))
      have hO_mem : z ∈ O := ⟨hW_mem n z, hzF⟩
      obtain ⟨w, hwO, hwU⟩ := mem_closure_iff.mp hz O hO_open hO_mem
      obtain ⟨a, _, hwH⟩ := mem_iUnion₂.mp hwU
      have hWa_sub : W n a ⊆ W n z := by
        intro u hu ⟨C, ⟨hC, hzC⟩, huC⟩
        have haC : a ∉ C := fun haC => hwO.1 ⟨C, ⟨hC, hzC⟩, (hH_equiv n k a w hwH C hC).mpr haC⟩
        exact hu ⟨C, ⟨hC, haC⟩, huC⟩
      exact hwO.2 (hF_mono k (W n a) (W n z) (hW_open n a) (hW_open n z) hWa_sub hwH.2)
  let 𝓕' : ℕ → ℕ → Set (Set X) := fun n k => Set.range (H n k)
  refine ⟨fun m => 𝓕' (Nat.unpair m).1 (Nat.unpair m).2, ?_, ?_, ?_⟩
  · rintro m _ ⟨a, rfl⟩
    exact hH_closed (Nat.unpair m).1 (Nat.unpair m).2 a
  · intro m y
    set n := (Nat.unpair m).1
    set k := (Nat.unpair m).2
    by_cases hy : ∃ a : X, y ∈ H n k a
    · obtain ⟨a₀, hya₀⟩ := hy
      let A : Set X := { a : X | H n k a ≠ H n k a₀ }
      refine ⟨(⋃ a ∈ A, H n k a)ᶜ, (hH_union_closed n k A).isOpen_compl, ?_, ?_⟩
      · intro h
        obtain ⟨a, haA, hya⟩ := mem_iUnion₂.mp h
        have heq : H n k a = H n k a₀ :=
          hH_eq_of_equiv n k a a₀ (fun C hC =>
            (hH_equiv n k a y hya C hC).symm.trans (hH_equiv n k a₀ y hya₀ C hC))
        exact haA heq
      · rintro _ ⟨a₁, rfl⟩ _ ⟨a₂, rfl⟩ ⟨w₁, hw₁O, hw₁⟩ ⟨w₂, hw₂O, hw₂⟩
        have h1 : H n k a₁ = H n k a₀ := by
          by_contra hne
          exact hw₁O (mem_iUnion₂.mpr ⟨a₁, hne, hw₁⟩)
        have h2 : H n k a₂ = H n k a₀ := by
          by_contra hne
          exact hw₂O (mem_iUnion₂.mpr ⟨a₂, hne, hw₂⟩)
        exact h1.trans h2.symm
    · refine ⟨(⋃ a ∈ (univ : Set X), H n k a)ᶜ, (hH_union_closed n k univ).isOpen_compl, ?_, ?_⟩
      · intro h
        obtain ⟨a, _, hya⟩ := mem_iUnion₂.mp h
        exact hy ⟨a, hya⟩
      · rintro _ ⟨a₁, rfl⟩ _ ⟨a₂, rfl⟩ ⟨w₁, hw₁O, hw₁⟩ _
        exact (hw₁O (mem_iUnion₂.mpr ⟨a₁, mem_univ _, hw₁⟩)).elim
  · intro x U hU hxU
    obtain ⟨K, hK_nhds, hK_closed, hKU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hxU)
    obtain ⟨V, hVK, hV_open, hxV⟩ := mem_nhds_iff.mp hK_nhds
    obtain ⟨B, hB𝓑, hxintB, hBV⟩ := h𝓑_qb x V hV_open hxV
    rw [h𝓑_eq, mem_iUnion] at hB𝓑
    obtain ⟨n, hBn⟩ := hB𝓑
    obtain ⟨k, hxF⟩ := hF_cover (W n x) (hW_open n x) x (hW_mem n x)
    refine ⟨Nat.pair n k, H n k x, ?_, ⟨hM_mem n x, hxF⟩, ?_⟩
    · dsimp only; rw [Nat.unpair_pair]; exact ⟨x, rfl⟩
    · intro z hz
      have hC_mem : closure B ∈ 𝓒 n := ⟨B, hBn, rfl⟩
      have hxC : x ∈ closure B := subset_closure (interior_subset hxintB)
      have hzC : z ∈ closure B := hz.1 (closure B) ⟨hC_mem, hxC⟩
      exact hKU ((hK_closed.closure_subset_iff.mpr (hBV.trans hVK)) hzC)

/-- Theorem 2: Every closed subset `F` of an M₃ space admits a closure-preserving
closed neighborhood base (generalizing `L_0021` to arbitrary closed subsets). -/
theorem M3_closed_subset_has_cp_closed_nhds (X : Type) [TopologicalSpace X]
    (hM3 : MSpace.IsM3 X) (F : Set X) (hF : IsClosed F) :
    ∃ 𝓚 : Set (Set X),
      (∀ K ∈ 𝓚, IsClosed K ∧ F ⊆ interior K) ∧
      (∀ U : Set X, IsOpen U → F ⊆ U → ∃ K ∈ 𝓚, K ⊆ U) ∧
      MSpace.ClosurePreserving 𝓚 := by
  have : T3Space X := hM3.1
  have hM2 : MSpace.IsM2 X := Proofs.L_0008.main X hM3
  obtain ⟨_, 𝓑, h𝓑_qb, 𝓑', h𝓑'_cp, h𝓑_eq⟩ := hM2
  let A : ℕ → Set X := fun k => ⋃₀ (closure '' { B ∈ 𝓑' k | Disjoint (closure B) F })
  have hA_closed : ∀ k, IsClosed (A k) := by
    intro k
    change IsClosed (⋃₀ (closure '' { B ∈ 𝓑' k | Disjoint (closure B) F }))
    rw [← h𝓑'_cp k { B ∈ 𝓑' k | Disjoint (closure B) F } (fun _ h => h.1)]
    exact isClosed_closure
  have hA_disj : ∀ k, Disjoint (A k) F := by
    intro k
    rw [Set.disjoint_left]
    rintro y ⟨_, ⟨B, ⟨_, hdis⟩, rfl⟩, hyB⟩ hyF
    exact Set.disjoint_left.mp hdis hyB hyF
  let W : ℕ → Set X := fun n => ⋂ k ∈ Iic n, (A k)ᶜ
  have hW_open : ∀ n, IsOpen (W n) := fun n =>
    (finite_Iic n).isOpen_biInter (fun k _ => (hA_closed k).isOpen_compl)
  have hF_sub_W : ∀ n, F ⊆ W n := fun n x hxF =>
    mem_iInter₂.mpr (fun k _ hxA => Set.disjoint_left.mp (hA_disj k) hxA hxF)
  have hW_disj : ∀ k n, k ≤ n → ∀ B ∈ 𝓑' k, Disjoint (closure B) F →
      Disjoint (closure B) (W n) := by
    intro k n hkn B hBk hdis
    rw [Set.disjoint_left]
    intro y hyB hyW
    exact (mem_iInter₂.mp hyW k (mem_Iic.mpr hkn)) ⟨closure B, ⟨B, ⟨hBk, hdis⟩, rfl⟩, hyB⟩
  -- For each open U ⊇ F, define K U := ⋃ n, (⋃₀ (closure '' {B ∈ 𝓑' n | closure B ⊆ U})) ∩ closure (W n).
  let Kn : Set X → ℕ → Set X := fun U n =>
    (⋃₀ (closure '' { B ∈ 𝓑' n | closure B ⊆ U })) ∩ closure (W n)
  let K : Set X → Set X := fun U => ⋃ n : ℕ, Kn U n
  have hKn_closed : ∀ U n, IsClosed (Kn U n) := by
    intro U n
    refine IsClosed.inter ?_ isClosed_closure
    rw [← h𝓑'_cp n { B ∈ 𝓑' n | closure B ⊆ U } (fun _ h => h.1)]
    exact isClosed_closure
  -- Key localization: for z ∉ F, there is an open neighborhood O of z disjoint from closure (W n) for n ≥ m.
  have hloc_out : ∀ z, z ∉ F → ∃ m : ℕ, ∃ O : Set X, IsOpen O ∧ z ∈ O ∧
      ∀ n, m ≤ n → Disjoint O (closure (W n)) := by
    intro z hzF
    obtain ⟨N, hN_nhds, hN_closed, hNF⟩ :=
      exists_mem_nhds_isClosed_subset (hF.isOpen_compl.mem_nhds hzF)
    obtain ⟨V, hVN, hV_open, hzV⟩ := mem_nhds_iff.mp hN_nhds
    obtain ⟨B, hB𝓑, hzintB, hBV⟩ := h𝓑_qb z V hV_open hzV
    rw [h𝓑_eq, mem_iUnion] at hB𝓑
    obtain ⟨m, hBm⟩ := hB𝓑
    have hdisF : Disjoint (closure B) F := by
      rw [Set.disjoint_left]
      intro y hyB hyF
      exact hNF ((hN_closed.closure_subset_iff.mpr (hBV.trans hVN)) hyB) hyF
    refine ⟨m, interior B, isOpen_interior, hzintB, fun n hmn => ?_⟩
    have h1 : Disjoint (interior B) (W n) :=
      (hW_disj m n hmn B hBm hdisF).mono_left (interior_subset.trans subset_closure)
    exact h1.closure_right isOpen_interior
  let 𝓚 : Set (Set X) := { S : Set X | ∃ U : Set X, IsOpen U ∧ F ⊆ U ∧ S = K U }
  have hF_sub_intK : ∀ U, IsOpen U → F ⊆ U → F ⊆ interior (K U) := by
    intro U hU hFU x hxF
    obtain ⟨N, hN_nhds, hN_closed, hNU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds (hFU hxF))
    obtain ⟨V, hVN, hV_open, hxV⟩ := mem_nhds_iff.mp hN_nhds
    obtain ⟨B, hB𝓑, hxintB, hBV⟩ := h𝓑_qb x V hV_open hxV
    rw [h𝓑_eq, mem_iUnion] at hB𝓑
    obtain ⟨n, hBn⟩ := hB𝓑
    have hclB : closure B ⊆ U := (hN_closed.closure_subset_iff.mpr (hBV.trans hVN)).trans hNU
    have hsub : interior B ∩ W n ⊆ K U := by
      intro y ⟨hyB, hyW⟩
      exact mem_iUnion.mpr ⟨n, ⟨closure B, ⟨B, ⟨hBn, hclB⟩, rfl⟩,
        subset_closure (interior_subset hyB)⟩, subset_closure hyW⟩
    exact interior_maximal hsub (isOpen_interior.inter (hW_open n)) ⟨hxintB, hF_sub_W n hxF⟩
  have hK_cp : ∀ 𝓖 ⊆ 𝓚, closure (⋃₀ 𝓖) ⊆ ⋃₀ 𝓖 := by
    intro 𝓖 h𝓖 z hz
    by_cases hzF : z ∈ F
    · rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨S, hS⟩
      · simp at hz
      · obtain ⟨U, hU, hFU, rfl⟩ := h𝓖 hS
        exact ⟨K U, hS, interior_subset (hF_sub_intK U hU hFU hzF)⟩
    · obtain ⟨m, O, hO_open, hzO, hO_disj⟩ := hloc_out z hzF
      let 𝓖_U : Set (Set X) := { U : Set X | IsOpen U ∧ F ⊆ U ∧ K U ∈ 𝓖 }
      let Tn : ℕ → Set X := fun n =>
        closure (⋃₀ { B ∈ 𝓑' n | ∃ U ∈ 𝓖_U, closure B ⊆ U }) ∩ closure (W n)
      have hTn_closed : ∀ n, IsClosed (Tn n) := fun n => isClosed_closure.inter isClosed_closure
      have hTn_sub : ∀ n, Tn n ⊆ ⋃₀ 𝓖 := by
        intro n y ⟨hy1, hyW⟩
        rw [h𝓑'_cp n { B ∈ 𝓑' n | ∃ U ∈ 𝓖_U, closure B ⊆ U } (fun _ h => h.1)] at hy1
        obtain ⟨_, ⟨B, ⟨hBn, U, hU𝓖, hBU⟩, rfl⟩, hyB⟩ := hy1
        exact ⟨K U, hU𝓖.2.2, mem_iUnion.mpr ⟨n, ⟨closure B, ⟨B, ⟨hBn, hBU⟩, rfl⟩, hyB⟩, hyW⟩⟩
      have hsub : O ∩ ⋃₀ 𝓖 ⊆ ⋃ n ∈ Iio m, Tn n := by
        rintro y ⟨hyO, S, hS𝓖, hyS⟩
        obtain ⟨U, hU, hFU, rfl⟩ := h𝓖 hS𝓖
        obtain ⟨n, ⟨_, ⟨B, ⟨hBn, hBU⟩, rfl⟩, hyB⟩, hyW⟩ := mem_iUnion.mp hyS
        have hnm : n < m := by
          by_contra hnm
          exact Set.disjoint_left.mp (hO_disj n (not_lt.mp hnm)) hyO hyW
        refine mem_iUnion₂.mpr ⟨n, hnm, ?_, hyW⟩
        have hBmem : B ∈ { B ∈ 𝓑' n | ∃ U ∈ 𝓖_U, closure B ⊆ U } := ⟨hBn, U, ⟨hU, hFU, hS𝓖⟩, hBU⟩
        rw [h𝓑'_cp n { B ∈ 𝓑' n | ∃ U ∈ 𝓖_U, closure B ⊆ U } (fun _ h => h.1)]
        exact ⟨closure B, ⟨B, hBmem, rfl⟩, hyB⟩
      have hcl : IsClosed (⋃ n ∈ Iio m, Tn n) :=
        (finite_Iio m).isClosed_biUnion (fun n _ => hTn_closed n)
      have hz' := closure_minimal hsub hcl (hO_open.inter_closure ⟨hzO, hz⟩)
      obtain ⟨n, _, hzT⟩ := mem_iUnion₂.mp hz'
      exact hTn_sub n hzT
  refine ⟨𝓚, ?_, ?_, ?_⟩
  · rintro S ⟨U, hU, hFU, rfl⟩
    refine ⟨?_, hF_sub_intK U hU hFU⟩
    rw [← closure_subset_iff_isClosed]
    have h1 := hK_cp {K U} (singleton_subset_iff.mpr ⟨U, hU, hFU, rfl⟩)
    simpa only [sUnion_singleton] using h1
  · intro U hU hFU
    refine ⟨K U, ⟨U, hU, hFU, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨n, ⟨_, ⟨B, ⟨_, hBU⟩, rfl⟩, hzB⟩, _⟩ := mem_iUnion.mp hz
    exact hBU hzB
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      obtain ⟨S, hS, hzS⟩ := hK_cp 𝓖 h𝓖 hz
      exact ⟨closure S, mem_image_of_mem _ hS, subset_closure hzS⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Theorem 3: Every point in a zero-dimensional M₁ space (having a `σ`-CP basis
of clopen sets) admits a closure-preserving clopen (hence both open and
regular-closed) neighborhood base. -/
theorem zero_dim_M1_has_cp_clopen_base (X : Type) [TopologicalSpace X] [T3Space X]
    (𝓑' : ℕ → Set (Set X))
    (h𝓑'_cp : ∀ n, MSpace.ClosurePreserving (𝓑' n))
    (h𝓑'_clopen : ∀ n, ∀ B ∈ 𝓑' n, IsClopen B)
    (h𝓑'_basis : IsTopologicalBasis (⋃ n, 𝓑' n))
    (x : X) :
    ∃ 𝓚' : Set (Set X),
      (∀ K ∈ 𝓚', IsClopen K ∧ closure (interior K) = K ∧ x ∈ interior K) ∧
      (∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚', K ⊆ U) ∧
      MSpace.ClosurePreserving 𝓚' := by
  let A : ℕ → Set X := fun k => ⋃₀ { B ∈ 𝓑' k | x ∉ B }
  have hA_clopen : ∀ k, IsClopen (A k) := by
    intro k
    refine ⟨?_, isOpen_sUnion fun B hB => (h𝓑'_clopen k B hB.1).2⟩
    have himg : closure '' { B ∈ 𝓑' k | x ∉ B } = { B ∈ 𝓑' k | x ∉ B } := by
      ext C
      constructor
      · rintro ⟨B, hB, rfl⟩; rw [(h𝓑'_clopen k B hB.1).1.closure_eq]; exact hB
      · intro hC; exact ⟨C, hC, (h𝓑'_clopen k C hC.1).1.closure_eq⟩
    change IsClosed (⋃₀ { B ∈ 𝓑' k | x ∉ B })
    rw [← himg, ← h𝓑'_cp k { B ∈ 𝓑' k | x ∉ B } (fun _ h => h.1)]
    exact isClosed_closure
  have hxA : ∀ k, x ∉ A k := fun k ⟨B, hB, hxB⟩ => hB.2 hxB
  let W : ℕ → Set X := fun n => ⋂ k ∈ Iic n, (A k)ᶜ
  have hW_clopen : ∀ n, IsClopen (W n) := fun n =>
    ⟨isClosed_biInter fun k _ => (hA_clopen k).2.isClosed_compl,
     (finite_Iic n).isOpen_biInter fun k _ => (hA_clopen k).1.isOpen_compl⟩
  have hxW : ∀ n, x ∈ W n := fun n => mem_iInter₂.mpr (fun k _ => hxA k)
  let 𝓚' : Set (Set X) := { K : Set X | ∃ n, ∃ B ∈ 𝓑' n, x ∈ B ∧ K = B ∩ W n }
  refine ⟨𝓚', ?_, ?_, ?_⟩
  · rintro _ ⟨n, B, hBn, hxB, rfl⟩
    have hclop : IsClopen (B ∩ W n) := (h𝓑'_clopen n B hBn).inter (hW_clopen n)
    refine ⟨hclop, ?_, ?_⟩
    · rw [hclop.2.interior_eq, hclop.1.closure_eq]
    · rw [hclop.2.interior_eq]; exact ⟨hxB, hxW n⟩
  · intro U hU hxU
    obtain ⟨B, hB, hxB, hBU⟩ := h𝓑'_basis.exists_subset_of_mem_open hxU hU
    obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
    exact ⟨B ∩ W n, ⟨n, B, hBn, hxB, rfl⟩, inter_subset_left.trans hBU⟩
  · intro 𝓖 h𝓖
    suffices H : closure (⋃₀ 𝓖) ⊆ ⋃₀ 𝓖 by
      apply Subset.antisymm
      · intro z hz
        obtain ⟨K, hK, hzK⟩ := H hz
        exact ⟨closure K, mem_image_of_mem _ hK, subset_closure hzK⟩
      · exact sUnion_subset (by rintro _ ⟨K, hK, rfl⟩; exact closure_mono (subset_sUnion_of_mem hK))
    intro z hz
    by_cases hzx : z = x
    · subst hzx
      rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨K, hK⟩
      · simp at hz
      · obtain ⟨n, B, _, hxB, rfl⟩ := h𝓖 hK
        exact ⟨B ∩ W n, hK, hxB, hxW n⟩
    · obtain ⟨B', hB', hzB', hB'x⟩ :=
        h𝓑'_basis.exists_subset_of_mem_open hzx isClosed_singleton.isOpen_compl
      obtain ⟨m, hB'm⟩ := mem_iUnion.mp hB'
      have hxB' : x ∉ B' := fun h => hB'x h rfl
      have hdis : ∀ n, m ≤ n → Disjoint B' (W n) := by
        intro n hmn
        rw [Set.disjoint_left]
        intro y hyB' hyW
        exact (mem_iInter₂.mp hyW m (mem_Iic.mpr hmn)) ⟨B', ⟨hB'm, hxB'⟩, hyB'⟩
      let G : ℕ → Set (Set X) := fun n => { B ∈ 𝓑' n | x ∈ B ∧ B ∩ W n ∈ 𝓖 }
      let T : ℕ → Set X := fun n => closure (⋃₀ G n) ∩ W n
      have hT_closed : ∀ n, IsClosed (T n) := fun n => isClosed_closure.inter (hW_clopen n).1
      have hT_sub : ∀ n, T n ⊆ ⋃₀ 𝓖 := by
        intro n y ⟨hy1, hyW⟩
        rw [h𝓑'_cp n (G n) (fun _ h => h.1)] at hy1
        obtain ⟨_, ⟨B, hBG, rfl⟩, hyB⟩ := hy1
        rw [(h𝓑'_clopen n B hBG.1).1.closure_eq] at hyB
        exact ⟨B ∩ W n, hBG.2.2, hyB, hyW⟩
      have hsub : B' ∩ ⋃₀ 𝓖 ⊆ ⋃ n ∈ Iio m, T n := by
        rintro y ⟨hyB', K, hK, hyK⟩
        obtain ⟨n, B, hBn, hxB, rfl⟩ := h𝓖 hK
        have hnm : n < m := by
          by_contra hnm
          exact Set.disjoint_left.mp (hdis n (not_lt.mp hnm)) hyB' hyK.2
        refine mem_iUnion₂.mpr ⟨n, hnm, ?_, hyK.2⟩
        exact subset_closure ⟨B, ⟨hBn, hxB, hK⟩, hyK.1⟩
      have hcl : IsClosed (⋃ n ∈ Iio m, T n) :=
        (finite_Iio m).isClosed_biUnion (fun n _ => hT_closed n)
      have hz' := closure_minimal hsub hcl ((h𝓑'_clopen m B' hB'm).2.inter_closure ⟨hzB', hz⟩)
      obtain ⟨n, _, hzT⟩ := mem_iUnion₂.mp hz'
      exact hT_sub n hzT

/-- Theorem 4 (Collectionwise normality of paracompact `T3Space`s):
Every discrete family of closed sets `{F i | i : ι}` in a paracompact `T3Space`
admits a discrete open expansion `{O i | i : ι}` with pairwise disjoint closures. -/
theorem collectionwise_normal_of_paracompact_t3
    (X : Type) [TopologicalSpace X] [T3Space X] [ParacompactSpace X]
    {ι : Type} (F : ι → Set X)
    (hF_closed : ∀ i, IsClosed (F i))
    (hF_disc : ∀ y : X, ∃ U : Set X, IsOpen U ∧ y ∈ U ∧
      ∀ i j, (U ∩ F i).Nonempty → (U ∩ F j).Nonempty → i = j) :
    ∃ O : ι → Set X,
      (∀ i, IsOpen (O i) ∧ F i ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (closure (O i)) (closure (O j))) ∧
      (∀ y : X, ∃ N : Set X, IsOpen N ∧ y ∈ N ∧
        ∀ i j, (N ∩ closure (O i)).Nonempty → (N ∩ closure (O j)).Nonempty → i = j) := by
  classical
  choose W hW_open hW_mem hW_uniq using hF_disc
  have hshrink : ∀ z : X, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ closure U ⊆ W z := by
    intro z
    obtain ⟨K, hK_nhds, hK_closed, hKW⟩ :=
      exists_mem_nhds_isClosed_subset ((hW_open z).mem_nhds (hW_mem z))
    obtain ⟨U, hUK, hU_open, hzU⟩ := mem_nhds_iff.mp hK_nhds
    exact ⟨U, hU_open, hzU, (hK_closed.closure_subset_iff.mpr hUK).trans hKW⟩
  choose W' hW'_open hW'_mem hW'_cl using hshrink
  have hW'_cover : ⋃ z : X, W' z = univ :=
    eq_univ_of_forall fun z => mem_iUnion.mpr ⟨z, hW'_mem z⟩
  obtain ⟨v, hv_open, hv_cover, hv_lf, hv_sub⟩ :=
    precise_refinement W' hW'_open hW'_cover
  have hv_cl_sub : ∀ z, closure (v z) ⊆ W z := fun z =>
    (closure_mono (hv_sub z)).trans (hW'_cl z)
  let O₀ : ι → Set X := fun i =>
    (⋃ (z : X) (_ : Disjoint (closure (v z)) (F i)), closure (v z))ᶜ
  have hO₀_open : ∀ i, IsOpen (O₀ i) := by
    intro i
    rw [isOpen_compl_iff]
    have hlf : LocallyFinite
        (fun z : { z : X // Disjoint (closure (v z)) (F i) } => closure (v z.1)) :=
      hv_lf.closure.comp_injective Subtype.val_injective
    have heq : (⋃ (z : X) (_ : Disjoint (closure (v z)) (F i)), closure (v z)) =
        ⋃ z : { z : X // Disjoint (closure (v z)) (F i) }, closure (v z.1) := by
      ext y; simp
    rw [heq]
    exact hlf.isClosed_iUnion (fun _ => isClosed_closure)
  have hF_sub_O₀ : ∀ i, F i ⊆ O₀ i := by
    intro i y hyF hyU
    obtain ⟨z, hdis, hyz⟩ := mem_iUnion₂.mp hyU
    exact Set.disjoint_left.mp hdis hyz hyF
  have hv_hits : ∀ z i, (v z ∩ O₀ i).Nonempty → (W z ∩ F i).Nonempty := by
    intro z i ⟨w, hwv, hwO⟩
    have hnd : ¬ Disjoint (closure (v z)) (F i) := fun hdis =>
      hwO (mem_iUnion₂.mpr ⟨z, hdis, subset_closure hwv⟩)
    rw [Set.not_disjoint_iff] at hnd
    obtain ⟨u, huv, huF⟩ := hnd
    exact ⟨u, hv_cl_sub z huv, huF⟩
  have hsep : ∀ i : ι, ∃ U : Set X, IsOpen U ∧ F i ⊆ U ∧ closure U ⊆ O₀ i := by
    intro i
    have hcov : ∀ z : X, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ (closure U ⊆ O₀ i ∨ Disjoint U (F i)) := by
      intro z
      by_cases hz : z ∈ F i
      · obtain ⟨K, hK_nhds, hK_closed, hKO⟩ :=
          exists_mem_nhds_isClosed_subset ((hO₀_open i).mem_nhds (hF_sub_O₀ i hz))
        obtain ⟨U, hUK, hU_open, hzU⟩ := mem_nhds_iff.mp hK_nhds
        exact ⟨U, hU_open, hzU, Or.inl ((hK_closed.closure_subset_iff.mpr hUK).trans hKO)⟩
      · exact ⟨(F i)ᶜ, (hF_closed i).isOpen_compl, hz, Or.inr disjoint_compl_left⟩
    choose u hu_open hu_mem hu_prop using hcov
    have hu_cov : ⋃ z : X, u z = univ := eq_univ_of_forall fun z => mem_iUnion.mpr ⟨z, hu_mem z⟩
    obtain ⟨w, hw_open, hw_cov, hw_lf, hw_sub⟩ := precise_refinement u hu_open hu_cov
    let S : Set X := { z : X | closure (w z) ⊆ O₀ i }
    refine ⟨⋃ z ∈ S, w z, isOpen_biUnion fun z _ => hw_open z, ?_, ?_⟩
    · intro y hyF
      have hy_univ : y ∈ ⋃ z : X, w z := hw_cov.symm ▸ mem_univ y
      obtain ⟨z, hyz⟩ := mem_iUnion.mp hy_univ
      rcases hu_prop z with hcl | hdis
      · exact mem_iUnion₂.mpr ⟨z, (closure_mono (hw_sub z)).trans hcl, hyz⟩
      · exact (Set.disjoint_left.mp hdis (hw_sub z hyz) hyF).elim
    · have hlf_sub : LocallyFinite (fun z : S => w z.1) :=
        hw_lf.comp_injective Subtype.val_injective
      have heq : (⋃ z ∈ S, w z) = ⋃ z : S, w z.1 := by ext y; simp
      rw [heq, hlf_sub.closure_iUnion]
      intro y hy
      obtain ⟨z, hyz⟩ := mem_iUnion.mp hy
      exact z.2 hyz
  choose O hO_open hFO hO_cl using hsep
  refine ⟨O, fun i => ⟨hO_open i, hFO i⟩, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro y hyi hyj
    have hy_univ : y ∈ ⋃ z : X, v z := hv_cover.symm ▸ mem_univ y
    obtain ⟨z, hyz⟩ := mem_iUnion.mp hy_univ
    exact hij (hW_uniq z i j (hv_hits z i ⟨y, hyz, hO_cl i hyi⟩) (hv_hits z j ⟨y, hyz, hO_cl j hyj⟩))
  · intro y
    have hy_univ : y ∈ ⋃ z : X, v z := hv_cover.symm ▸ mem_univ y
    obtain ⟨z, hyz⟩ := mem_iUnion.mp hy_univ
    refine ⟨v z, hv_open z, hyz, fun i j ⟨w₁, hw₁v, hw₁i⟩ ⟨w₂, hw₂v, hw₂j⟩ => ?_⟩
    exact hW_uniq z i j
      (hv_hits z i ⟨w₁, hw₁v, hO_cl i hw₁i⟩)
      (hv_hits z j ⟨w₂, hw₂v, hO_cl j hw₂j⟩)

/-- Theorem 5 (Gruenhage–Ito characterization of M₁ spaces):
Every M₃ space in which every closed subset admits a closure-preserving open
neighborhood base is an M₁ space. -/
theorem M3_is_M1_of_closed_cp_outer_base (X : Type) [TopologicalSpace X]
    (hM3 : MSpace.IsM3 X)
    (hcp_base : ∀ F : Set X, IsClosed F →
      ∃ 𝓥 : Set (Set X),
        (∀ V ∈ 𝓥, IsOpen V ∧ F ⊆ V) ∧
        (∀ U : Set X, IsOpen U → F ⊆ U → ∃ V ∈ 𝓥, V ⊆ U) ∧
        MSpace.ClosurePreserving 𝓥) :
    MSpace.IsM1 X := by
  have : T3Space X := hM3.1
  have hpara : ParacompactSpace X :=
    Proofs.L_0005.main X ⟨inferInstance, Proofs.L_0010.main X hM3⟩
  obtain ⟨𝓕, h𝓕_closed, h𝓕_disc, h𝓕_net⟩ := M3_is_sigma_space X hM3
  -- For each m, expand the discrete closed family 𝓕 m to a discrete open family O m.
  have hexp : ∀ m : ℕ, ∃ O : ↥(𝓕 m) → Set X,
      (∀ H : ↥(𝓕 m), IsOpen (O H) ∧ H.1 ⊆ O H) ∧
      Pairwise (fun H₁ H₂ : ↥(𝓕 m) => Disjoint (closure (O H₁)) (closure (O H₂))) ∧
      (∀ y : X, ∃ N : Set X, IsOpen N ∧ y ∈ N ∧
        ∀ H₁ H₂ : ↥(𝓕 m), (N ∩ closure (O H₁)).Nonempty → (N ∩ closure (O H₂)).Nonempty → H₁ = H₂) := by
    intro m
    refine collectionwise_normal_of_paracompact_t3 X (fun H : ↥(𝓕 m) => H.1)
      (fun H => h𝓕_closed m H.1 H.2) ?_
    intro y
    obtain ⟨U, hU_open, hyU, hU_uniq⟩ := h𝓕_disc m y
    exact ⟨U, hU_open, hyU, fun H₁ H₂ h1 h2 => Subtype.ext (hU_uniq H₁.1 H₁.2 H₂.1 H₂.2 h1 h2)⟩
  choose O hO_open hO_disj hO_disc using hexp
  -- For each closed F, choose a CP open neighborhood base 𝓥 F.
  choose 𝓥 h𝓥_open h𝓥_base h𝓥_cp using fun F (hF : IsClosed F) => hcp_base F hF
  -- Define the m-th CP open family 𝓑' m.
  let 𝓑' : ℕ → Set (Set X) := fun m =>
    { V : Set X | ∃ H : ↥(𝓕 m), V ∈ 𝓥 H.1 (h𝓕_closed m H.1 H.2) ∧ V ⊆ O m H }
  refine ⟨inferInstance, ⋃ m, 𝓑' m, ?_, 𝓑', ?_, rfl⟩
  · -- IsTopologicalBasis (⋃ m, 𝓑' m)
    have hopen : ∀ V ∈ ⋃ m, 𝓑' m, IsOpen V := by
      intro V hV
      obtain ⟨m, H, hV𝓥, _⟩ := mem_iUnion.mp hV
      exact (h𝓥_open H.1 (h𝓕_closed m H.1 H.2) V hV𝓥).1
    refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    intro x U hxU hU_open
    obtain ⟨m, F, hFm, hxF, hFU⟩ := h𝓕_net x U hU_open hxU
    let H : ↥(𝓕 m) := ⟨F, hFm⟩
    have hUO_open : IsOpen (U ∩ O m H) := hU_open.inter (hO_open m H).1
    have hF_sub : F ⊆ U ∩ O m H := subset_inter hFU (hO_open m H).2
    obtain ⟨V, hV𝓥, hVsub⟩ := h𝓥_base F (h𝓕_closed m F hFm) (U ∩ O m H) hUO_open hF_sub
    refine ⟨V, mem_iUnion.mpr ⟨m, H, hV𝓥, hVsub.trans inter_subset_right⟩, ?_,
      hVsub.trans inter_subset_left⟩
    exact (h𝓥_open F (h𝓕_closed m F hFm) V hV𝓥).2 hxF
  · -- ∀ m, ClosurePreserving (𝓑' m)
    intro m 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      obtain ⟨N, hN_open, hyN, hN_uniq⟩ := hO_disc m y
      by_cases hhit : ∃ H : ↥(𝓕 m), (N ∩ closure (O m H)).Nonempty
      · obtain ⟨H₀, hH₀⟩ := hhit
        let 𝓖₀ : Set (Set X) := { V ∈ 𝓖 | V ∈ 𝓥 H₀.1 (h𝓕_closed m H₀.1 H₀.2) ∧ V ⊆ O m H₀ }
        have hsub : N ∩ ⋃₀ 𝓖 ⊆ ⋃₀ 𝓖₀ := by
          rintro z ⟨hzN, V, hV𝓖, hzV⟩
          obtain ⟨H, hV𝓥, hVO⟩ := h𝓖 hV𝓖
          have hHeq : H = H₀ :=
            hN_uniq H H₀ ⟨z, hzN, subset_closure (hVO hzV)⟩ hH₀
          subst hHeq
          exact ⟨V, ⟨hV𝓖, hV𝓥, hVO⟩, hzV⟩
        have hy0 : y ∈ closure (⋃₀ 𝓖₀) :=
          closure_mono hsub (hN_open.inter_closure ⟨hyN, hy⟩)
        rw [h𝓥_cp H₀.1 (h𝓕_closed m H₀.1 H₀.2) 𝓖₀ (fun _ h => h.2.1)] at hy0
        obtain ⟨_, ⟨V, hV, rfl⟩, hyV⟩ := hy0
        exact ⟨closure V, mem_image_of_mem _ hV.1, hyV⟩
      · exfalso
        obtain ⟨z, hzN, hzU⟩ := mem_closure_iff.mp hy N hN_open hyN
        obtain ⟨V, hV𝓖, hzV⟩ := hzU
        obtain ⟨H, _, hVO⟩ := h𝓖 hV𝓖
        exact hhit ⟨H, z, hzN, subset_closure (hVO hzV)⟩
    · exact sUnion_subset (by rintro _ ⟨V, hV, rfl⟩; exact closure_mono (subset_sUnion_of_mem hV))

end Research.M3M1
