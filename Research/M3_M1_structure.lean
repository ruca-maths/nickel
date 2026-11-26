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

/-- Pointwise closure-preserving open neighborhood base (outer base). -/
def HasCPOpenLocalBase {X : Type} [TopologicalSpace X] (p : X) : Prop :=
  ∃ 𝓥 : Set (Set X),
    (∀ V ∈ 𝓥, IsOpen V ∧ p ∈ V) ∧
    (∀ U : Set X, IsOpen U → p ∈ U → ∃ V ∈ 𝓥, V ⊆ U) ∧
    MSpace.ClosurePreserving 𝓥

/-- Helper: Every `M₃`-space admits a monotone decreasing stratification. -/
theorem exists_monotone_stratification (X : Type) [TopologicalSpace X] (hM3 : MSpace.IsM3 X) :
    ∃ G : ℕ → Set X → Set X,
      MSpace.IsStratification G ∧
      ∀ n H, IsClosed H → G (n + 1) H ⊆ G n H := by
  obtain ⟨G₀, hG₀_open, hG₀_sub, hG₀_inter, hG₀_mono⟩ := Proofs.L_0010.main X hM3
  let G : ℕ → Set X → Set X := fun n H => ⋂ k ∈ Iic n, G₀ k H
  refine ⟨G, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n H hH
    exact (finite_Iic n).isOpen_biInter fun k _ => hG₀_open k H hH
  · intro n H hH
    exact subset_iInter₂ fun k _ => hG₀_sub k H hH
  · intro H hH
    apply Subset.antisymm
    · intro z hz
      rw [← hG₀_inter H hH, mem_iInter]
      rw [mem_iInter] at hz
      intro n
      have hsub : G n H ⊆ G₀ n H := iInter₂_subset n (mem_Iic.mpr le_rfl)
      exact closure_mono hsub (hz n)
    · intro z hz
      rw [mem_iInter]
      intro n
      exact subset_closure (mem_iInter₂.mpr fun k _ => hG₀_sub k H hH hz)
  · intro n H K hH hK hHK z hz
    exact mem_iInter₂.mpr fun k hk => hG₀_mono k H K hH hK hHK (mem_iInter₂.mp hz k hk)
  · intro n H _ z hz
    exact mem_iInter₂.mpr fun k hk =>
      mem_iInter₂.mp hz k (mem_Iic.mpr (Nat.le_succ_of_le (mem_Iic.mp hk)))

/-- Theorem 6 (Ito's Expansion Lemma):
In an `M₃`-space `X`, let `F ⊆ X` be any subset, `𝓚` a CP closed neighborhood base of `F`,
and `E : ℕ → Set X` a sequence of closed discrete subsets of `X`
such that every `p ∈ ⋃ k, E k` has a CP open neighborhood base and every `K ∈ 𝓚`
satisfies `K ⊆ closure (interior K ∪ (K ∩ ⋃ k, E k))`.
Then `F` admits a CP open neighborhood base. -/
theorem closed_cp_outer_base_of_pointwise_cp_and_dense_trace
    (X : Type) [TopologicalSpace X] (hM3 : MSpace.IsM3 X)
    (F : Set X)
    (𝓚 : Set (Set X))
    (h𝓚_nhd : ∀ K ∈ 𝓚, IsClosed K ∧ F ⊆ interior K)
    (h𝓚_base : ∀ U : Set X, IsOpen U → F ⊆ U → ∃ K ∈ 𝓚, K ⊆ U)
    (h𝓚_cp : MSpace.ClosurePreserving 𝓚)
    (E : ℕ → Set X)
    (hE_disc : ∀ k, ∀ A ⊆ E k, IsClosed A)
    (hE_cp : ∀ k, ∀ p ∈ E k, HasCPOpenLocalBase p)
    (hK_trace : ∀ K ∈ 𝓚, K ⊆ closure (interior K ∪ (K ∩ ⋃ k, E k))) :
    ∃ 𝓥 : Set (Set X),
      (∀ V ∈ 𝓥, IsOpen V ∧ F ⊆ V) ∧
      (∀ U : Set X, IsOpen U → F ⊆ U → ∃ V ∈ 𝓥, V ⊆ U) ∧
      MSpace.ClosurePreserving 𝓥 := by
  classical
  have : T3Space X := hM3.1
  have hpara : ParacompactSpace X :=
    Proofs.L_0005.main X ⟨inferInstance, Proofs.L_0010.main X hM3⟩
  obtain ⟨G, hG, hG_dec⟩ := exists_monotone_stratification X hM3
  have hG_anti : ∀ {m n : ℕ} {H : Set X}, IsClosed H → m ≤ n → G n H ⊆ G m H := by
    intro m n H hH hmn
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hG_dec _ H hH).trans ih
  have hexp : ∀ k : ℕ, ∃ O : ↥(E k) → Set X,
      (∀ p : ↥(E k), IsOpen (O p) ∧ (p : X) ∈ O p) ∧
      Pairwise (fun p q : ↥(E k) => Disjoint (closure (O p)) (closure (O q))) ∧
      (∀ y : X, ∃ N : Set X, IsOpen N ∧ y ∈ N ∧
        ∀ p q : ↥(E k), (N ∩ closure (O p)).Nonempty → (N ∩ closure (O q)).Nonempty → p = q) := by
    intro k
    obtain ⟨O, hO1, hO2, hO3⟩ := collectionwise_normal_of_paracompact_t3 X
      (fun p : ↥(E k) => ({(p : X)} : Set X)) (fun _ => isClosed_singleton) (by
        intro y
        by_cases hy : y ∈ E k
        · refine ⟨(E k \ {y})ᶜ, (hE_disc k (E k \ {y}) sdiff_subset).isOpen_compl,
            fun h => h.2 rfl, ?_⟩
          intro p q ⟨w₁, hw₁, hw₁p⟩ ⟨w₂, hw₂, hw₂q⟩
          rw [mem_singleton_iff] at hw₁p hw₂q
          subst hw₁p; subst hw₂q
          have hp : (p : X) = y := by by_contra hne; exact hw₁ ⟨p.2, hne⟩
          have hq : (q : X) = y := by by_contra hne; exact hw₂ ⟨q.2, hne⟩
          exact Subtype.ext (hp.trans hq.symm)
        · refine ⟨(E k)ᶜ, (hE_disc k (E k) Subset.rfl).isOpen_compl, hy, ?_⟩
          intro p _ ⟨w₁, hw₁, hw₁p⟩ _
          rw [mem_singleton_iff] at hw₁p; subst hw₁p
          exact (hw₁ p.2).elim)
    exact ⟨O, fun p => ⟨(hO1 p).1, singleton_subset_iff.mp (hO1 p).2⟩, hO2, hO3⟩
  choose O hO_open hO_disj hO_disc using hexp
  have hcp_sub : ∀ (k : ℕ) (p : ↥(E k)), HasCPOpenLocalBase (p : X) :=
    fun k p => hE_cp k p.1 p.2
  choose 𝓤 h𝓤_open h𝓤_base h𝓤_cp using hcp_sub
  let Pairs : Type := { P : Set X × Set X // P.1 ∈ 𝓚 ∧ IsOpen P.2 ∧ P.1 ⊆ P.2 }
  have hpick : ∀ (P : Pairs) (k : ℕ) (p : ↥(E k)), (p : X) ∈ P.1.1 →
      ∃ V ∈ 𝓤 k p, V ⊆ P.1.2 ∩ O k p ∩ G k P.1.1 := by
    intro P k p hpK
    have hK_cl : IsClosed P.1.1 := (h𝓚_nhd P.1.1 P.2.1).1
    have hopen : IsOpen (P.1.2 ∩ O k p ∩ G k P.1.1) :=
      (P.2.2.1.inter (hO_open k p).1).inter (hG.1 k P.1.1 hK_cl)
    have hmem : (p : X) ∈ P.1.2 ∩ O k p ∩ G k P.1.1 :=
      ⟨⟨P.2.2.2 hpK, (hO_open k p).2⟩, hG.2.1 k P.1.1 hK_cl hpK⟩
    exact h𝓤_base k p _ hopen hmem
  let V : Pairs → (k : ℕ) → (p : ↥(E k)) → Set X := fun P k p =>
    if h : (p : X) ∈ P.1.1 then (hpick P k p h).choose else ∅
  have hV_open : ∀ P k p, IsOpen (V P k p) := by
    intro P k p
    dsimp only [V]
    split_ifs with h
    · exact (h𝓤_open k p _ (hpick P k p h).choose_spec.1).1
    · exact isOpen_empty
  have hV_mem_𝓤 : ∀ (P : Pairs) (k : ℕ) (p : ↥(E k)) (h : (p : X) ∈ P.1.1), V P k p ∈ 𝓤 k p := by
    intro P k p h
    dsimp only [V]; split_ifs
    exact (hpick P k p h).choose_spec.1
  have hV_sub : ∀ (P : Pairs) (k : ℕ) (p : ↥(E k)) (h : (p : X) ∈ P.1.1),
      V P k p ⊆ P.1.2 ∩ O k p ∩ G k P.1.1 := by
    intro P k p h
    dsimp only [V]; split_ifs
    exact (hpick P k p h).choose_spec.2
  have hV_has_p : ∀ (P : Pairs) (k : ℕ) (p : ↥(E k)) (h : (p : X) ∈ P.1.1),
      (p : X) ∈ V P k p := by
    intro P k p h
    exact (h𝓤_open k p _ (hV_mem_𝓤 P k p h)).2
  have hV_empty : ∀ (P : Pairs) (k : ℕ) (p : ↥(E k)), (p : X) ∉ P.1.1 → V P k p = ∅ := by
    intro P k p h
    dsimp only [V]; split_ifs; rfl
  let W : Pairs → Set X := fun P =>
    interior P.1.1 ∪ ⋃ k : ℕ, ⋃ p : ↥(E k), V P k p
  have hW_open : ∀ P, IsOpen (W P) := fun P =>
    isOpen_interior.union (isOpen_iUnion fun k => isOpen_iUnion fun p => hV_open P k p)
  have hW_F : ∀ P, F ⊆ W P := fun P =>
    (h𝓚_nhd P.1.1 P.2.1).2.trans subset_union_left
  have hW_sub_U : ∀ P, W P ⊆ P.1.2 := by
    intro P z hz
    rcases hz with hz_int | hz_u
    · exact P.2.2.2 (interior_subset hz_int)
    · obtain ⟨k, hz_k⟩ := mem_iUnion.mp hz_u
      obtain ⟨p, hz_p⟩ := mem_iUnion.mp hz_k
      by_cases hp : (p : X) ∈ P.1.1
      · exact (hV_sub P k p hp hz_p).1.1
      · rw [hV_empty P k p hp] at hz_p; exact hz_p.elim
  have hK_sub_clW : ∀ P, P.1.1 ⊆ closure (W P) := by
    intro P
    refine (hK_trace P.1.1 P.2.1).trans (closure_mono ?_)
    intro z hz
    rcases hz with hz_int | ⟨hzK, hzE⟩
    · exact Or.inl hz_int
    · obtain ⟨k, hzk⟩ := mem_iUnion.mp hzE
      right
      refine mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨z, hzk⟩, ?_⟩⟩
      exact hV_has_p P k ⟨z, hzk⟩ hzK
  refine ⟨Set.range W, ?_, ?_, ?_⟩
  · rintro _ ⟨P, rfl⟩
    exact ⟨hW_open P, hW_F P⟩
  · intro U hU hFU
    obtain ⟨K, hK𝓚, hKU⟩ := h𝓚_base U hU hFU
    let P : Pairs := ⟨(K, U), hK𝓚, hU, hKU⟩
    exact ⟨W P, ⟨P, rfl⟩, hW_sub_U P⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      let 𝓗 : Set Pairs := { P : Pairs | W P ∈ 𝓖 }
      have hG_eq : ⋃₀ 𝓖 = ⋃ P ∈ 𝓗, W P := by
        ext z
        constructor
        · rintro ⟨S, hS𝓖, hzS⟩
          obtain ⟨P, rfl⟩ := h𝓖 hS𝓖
          exact mem_iUnion₂.mpr ⟨P, hS𝓖, hzS⟩
        · intro hz
          obtain ⟨P, hP𝓗, hzP⟩ := mem_iUnion₂.mp hz
          exact ⟨W P, hP𝓗, hzP⟩
      rw [hG_eq] at hy
      let H : Set X := ⋃ P ∈ 𝓗, P.1.1
      have hH_closed : IsClosed H := by
        let 𝓚₀ : Set (Set X) := (fun P : Pairs => P.1.1) '' 𝓗
        have h𝓚₀_sub : 𝓚₀ ⊆ 𝓚 := by rintro _ ⟨P, _, rfl⟩; exact P.2.1
        have hH_eq : H = ⋃₀ 𝓚₀ := by ext z; simp [H, 𝓚₀]
        have himg : closure '' 𝓚₀ = 𝓚₀ := by
          ext K
          constructor
          · rintro ⟨K', hK', rfl⟩
            rw [(h𝓚_nhd K' (h𝓚₀_sub hK')).1.closure_eq]; exact hK'
          · intro hK
            exact ⟨K, hK, (h𝓚_nhd K (h𝓚₀_sub hK)).1.closure_eq⟩
        rw [hH_eq, ← himg, ← h𝓚_cp 𝓚₀ h𝓚₀_sub]
        exact isClosed_closure
      by_cases hyH : y ∈ H
      · obtain ⟨P, hP𝓗, hyP⟩ := mem_iUnion₂.mp hyH
        exact ⟨closure (W P), mem_image_of_mem _ hP𝓗, hK_sub_clW P hyP⟩
      · rw [← hG.2.2.1 H hH_closed, mem_iInter] at hyH
        push Not at hyH
        obtain ⟨N, hyN⟩ := hyH
        have hsplit : (⋃ P ∈ 𝓗, W P) ⊆
            H ∪ (⋃ k ∈ Iio N, ⋃ P ∈ 𝓗, ⋃ p : ↥(E k), V P k p) ∪ G N H := by
          intro z hz
          obtain ⟨P, hP𝓗, hzW⟩ := mem_iUnion₂.mp hz
          rcases hzW with hz_int | hz_u
          · exact Or.inl (Or.inl (mem_iUnion₂.mpr ⟨P, hP𝓗, interior_subset hz_int⟩))
          · obtain ⟨k, hz_k⟩ := mem_iUnion.mp hz_u
            obtain ⟨p, hz_p⟩ := mem_iUnion.mp hz_k
            by_cases hlt : k < N
            · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨k, hlt,
                mem_iUnion₂.mpr ⟨P, hP𝓗, mem_iUnion.mpr ⟨p, hz_p⟩⟩⟩))
            · right
              by_cases hp : (p : X) ∈ P.1.1
              · have hzG : z ∈ G k P.1.1 := (hV_sub P k p hp hz_p).2
                have hPH : P.1.1 ⊆ H := fun w hw => mem_iUnion₂.mpr ⟨P, hP𝓗, hw⟩
                have h1 : G k P.1.1 ⊆ G k H :=
                  hG.2.2.2 k P.1.1 H (h𝓚_nhd P.1.1 P.2.1).1 hH_closed hPH
                exact hG_anti hH_closed (not_lt.mp hlt) (h1 hzG)
              · rw [hV_empty P k p hp] at hz_p; exact hz_p.elim
        have hy_u := closure_mono hsplit hy
        rw [closure_union, closure_union] at hy_u
        rcases hy_u with (hyH' | hy_low) | hy_high
        · rw [hH_closed.closure_eq] at hyH'
          exact (hyN (subset_closure (hG.2.1 N H hH_closed hyH'))).elim
        · rw [(finite_Iio N).closure_biUnion] at hy_low
          obtain ⟨k, _, hyk⟩ := mem_iUnion₂.mp hy_low
          obtain ⟨M, hM_open, hyM, hM_uniq⟩ := hO_disc k y
          by_cases hhit : ∃ p : ↥(E k), (M ∩ closure (O k p)).Nonempty
          · obtain ⟨p₀, hp₀⟩ := hhit
            let 𝓖₀ : Set (Set X) :=
              { S : Set X | ∃ P ∈ 𝓗, ∃ hp : (p₀ : X) ∈ P.1.1, S = V P k p₀ }
            have hsubM : M ∩ (⋃ P ∈ 𝓗, ⋃ p : ↥(E k), V P k p) ⊆ ⋃₀ 𝓖₀ := by
              rintro z ⟨hzM, hzU⟩
              obtain ⟨P, hP𝓗, hzP⟩ := mem_iUnion₂.mp hzU
              obtain ⟨p, hzp⟩ := mem_iUnion.mp hzP
              by_cases hp : (p : X) ∈ P.1.1
              · have hzO : z ∈ O k p := (hV_sub P k p hp hzp).1.2
                have hpeq : p = p₀ := hM_uniq p p₀ ⟨z, hzM, subset_closure hzO⟩ hp₀
                subst hpeq
                exact ⟨V P k p, ⟨P, hP𝓗, hp, rfl⟩, hzp⟩
              · rw [hV_empty P k p hp] at hzp; exact hzp.elim
            have hy0 : y ∈ closure (⋃₀ 𝓖₀) :=
              closure_mono hsubM (hM_open.inter_closure ⟨hyM, hyk⟩)
            have h𝓖₀_sub : 𝓖₀ ⊆ 𝓤 k p₀ := by
              rintro S ⟨P, _, hp, rfl⟩; exact hV_mem_𝓤 P k p₀ hp
            rw [h𝓤_cp k p₀ 𝓖₀ h𝓖₀_sub] at hy0
            obtain ⟨_, ⟨S, ⟨P, hP𝓗, _, rfl⟩, rfl⟩, hyS⟩ := hy0
            refine ⟨closure (W P), mem_image_of_mem _ hP𝓗, ?_⟩
            refine closure_mono (fun z hz => Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨p₀, hz⟩⟩)) hyS
          · exfalso
            obtain ⟨z, hzM, hzU⟩ := mem_closure_iff.mp hyk M hM_open hyM
            obtain ⟨P, _, hzP⟩ := mem_iUnion₂.mp hzU
            obtain ⟨p, hzp⟩ := mem_iUnion.mp hzP
            by_cases hp : (p : X) ∈ P.1.1
            · exact hhit ⟨p, z, hzM, subset_closure (hV_sub P k p hp hzp).1.2⟩
            · rw [hV_empty P k p hp] at hzp; exact hzp.elim
        · exact (hyN hy_high).elim
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Theorem 7: If every closed subset of an `M₃`-space satisfies Ito's dense-trace
condition over points having CP open neighborhood bases, then `X` is `M₁`. -/
theorem M3_is_M1_of_pointwise_cp_and_dense_trace
    (X : Type) [TopologicalSpace X] (hM3 : MSpace.IsM3 X)
    (htrace : ∀ F : Set X, IsClosed F →
      ∃ (𝓚 : Set (Set X)) (E : ℕ → Set X),
        (∀ K ∈ 𝓚, IsClosed K ∧ F ⊆ interior K) ∧
        (∀ U : Set X, IsOpen U → F ⊆ U → ∃ K ∈ 𝓚, K ⊆ U) ∧
        MSpace.ClosurePreserving 𝓚 ∧
        (∀ k, ∀ A ⊆ E k, IsClosed A) ∧
        (∀ k, ∀ p ∈ E k, HasCPOpenLocalBase p) ∧
        (∀ K ∈ 𝓚, K ⊆ closure (interior K ∪ (K ∩ ⋃ k, E k)))) :
    MSpace.IsM1 X := by
  refine M3_is_M1_of_closed_cp_outer_base X hM3 fun F hF => ?_
  obtain ⟨𝓚, E, h1, h2, h3, h4, h5, h6⟩ := htrace F hF
  exact closed_cp_outer_base_of_pointwise_cp_and_dense_trace X hM3 F 𝓚 h1 h2 h3 E h4 h5 h6

/-- Theorem 8 (Conditional reduction of `Specs.L_0028`):
In an `M₃`-space `X` (in particular, any `M₁`-space), if a point `x : X` has a CP
closed neighborhood base `𝓚` and a `σ`-closed-discrete set `E = ⋃ k, E k`
of points having CP open neighborhood bases covers the non-regular boundary of each
`K ∈ 𝓚` (`K ⊆ closure (interior K ∪ (K ∩ ⋃ k, E k))`), then `x` has a CP
regular-closed neighborhood base (the conclusion of `Specs.L_0028`). -/
theorem L0028_of_boundary_cp_trace
    (X : Type) [TopologicalSpace X] (hM3 : MSpace.IsM3 X) (x : X)
    (𝓚 : Set (Set X))
    (h𝓚_nhd : ∀ K ∈ 𝓚, IsClosed K ∧ x ∈ interior K)
    (h𝓚_base : ∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚, K ⊆ U)
    (h𝓚_cp : MSpace.ClosurePreserving 𝓚)
    (E : ℕ → Set X)
    (hE_disc : ∀ k, ∀ A ⊆ E k, IsClosed A)
    (hE_cp : ∀ k, ∀ p ∈ E k, HasCPOpenLocalBase p)
    (hK_trace : ∀ K ∈ 𝓚, K ⊆ closure (interior K ∪ (K ∩ ⋃ k, E k))) :
    ∃ 𝓚' : Set (Set X),
      (∀ K ∈ 𝓚', IsClosed K ∧ closure (interior K) = K ∧ x ∈ interior K) ∧
      (∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚', K ⊆ U) ∧
      MSpace.ClosurePreserving 𝓚' := by
  have : T3Space X := hM3.1
  obtain ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩ :=
    closed_cp_outer_base_of_pointwise_cp_and_dense_trace X hM3 {x}
      𝓚 (fun K hK => ⟨(h𝓚_nhd K hK).1, singleton_subset_iff.mpr (h𝓚_nhd K hK).2⟩)
      (fun U hU hsub => h𝓚_base U hU (singleton_subset_iff.mp hsub))
      h𝓚_cp E hE_disc hE_cp hK_trace
  refine ⟨closure '' 𝓥, ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    have hVo := h𝓥_open V hV
    refine ⟨isClosed_closure, ?_, ?_⟩
    · apply Subset.antisymm
      · exact closure_minimal interior_subset isClosed_closure
      · exact closure_mono (interior_maximal subset_closure hVo.1)
    · exact interior_maximal subset_closure hVo.1 (singleton_subset_iff.mp hVo.2)
  · intro U hU hxU
    obtain ⟨K, hK_nhds, hK_closed, hKU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hxU)
    obtain ⟨W, hWK, hW_open, hxW⟩ := mem_nhds_iff.mp hK_nhds
    obtain ⟨V, hV, hVW⟩ := h𝓥_base W hW_open (singleton_subset_iff.mpr hxW)
    exact ⟨closure V, mem_image_of_mem _ hV,
      (hK_closed.closure_subset_iff.mpr (hVW.trans hWK)).trans hKU⟩
  · intro 𝓖 h𝓖
    let 𝓖₀ : Set (Set X) := { V ∈ 𝓥 | closure V ∈ 𝓖 }
    have himg : closure '' 𝓖₀ = 𝓖 := by
      ext K
      constructor
      · rintro ⟨V, hV, rfl⟩; exact hV.2
      · intro hK
        obtain ⟨V, hV, rfl⟩ := h𝓖 hK
        exact ⟨V, ⟨hV, hK⟩, rfl⟩
    have hcl_eq : ⋃₀ (closure '' 𝓖) = ⋃₀ 𝓖 := by
      ext z
      constructor
      · rintro ⟨C, ⟨K, hK, rfl⟩, hz⟩
        obtain ⟨V, _, rfl⟩ := h𝓖 hK
        rw [closure_closure] at hz
        exact ⟨closure V, hK, hz⟩
      · rintro ⟨K, hK, hz⟩
        exact ⟨closure K, mem_image_of_mem _ hK, subset_closure hz⟩
    have h𝓑_eq_aux : closure (⋃₀ (closure '' 𝓖₀)) = ⋃₀ (closure '' 𝓖₀) := by
      rw [← h𝓥_cp 𝓖₀ (fun _ h => h.1), closure_closure]
    rw [hcl_eq, ← himg, h𝓑_eq_aux]

/-- Helper: Every point with a countable open neighborhood base in a `T3Space`
admits a single-layer CP open neighborhood base. -/
theorem hasCPOpenLocalBase_of_countable_nhds (X : Type) [TopologicalSpace X] [T3Space X]
    (x : X) (B : ℕ → Set X)
    (hB_open : ∀ n, IsOpen (B n) ∧ x ∈ B n)
    (hB_base : ∀ U : Set X, IsOpen U → x ∈ U → ∃ n, B n ⊆ U) :
    HasCPOpenLocalBase x := by
  let V : ℕ → Set X := fun n => ⋂ k ∈ Iic n, B k
  have hV_open : ∀ n, IsOpen (V n) ∧ x ∈ V n := fun n =>
    ⟨(finite_Iic n).isOpen_biInter (fun k _ => (hB_open k).1),
     mem_iInter₂.mpr (fun k _ => (hB_open k).2)⟩
  have hV_sub_B : ∀ n, V n ⊆ B n := fun n _ hz => mem_iInter₂.mp hz n (mem_Iic.mpr le_rfl)
  have hV_anti : ∀ {m n : ℕ}, m ≤ n → V n ⊆ V m := fun hmn _ hz =>
    mem_iInter₂.mpr (fun k hk => mem_iInter₂.mp hz k (mem_Iic.mpr (le_trans (mem_Iic.mp hk) hmn)))
  refine ⟨Set.range V, ?_, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩; exact hV_open n
  · intro U hU hxU
    obtain ⟨n, hn⟩ := hB_base U hU hxU
    exact ⟨V n, ⟨n, rfl⟩, (hV_sub_B n).trans hn⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      by_cases hyx : y = x
      · subst hyx
        rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨U, hU⟩
        · simp at hy
        · obtain ⟨n, rfl⟩ := h𝓖 hU
          exact ⟨closure (V n), mem_image_of_mem _ hU, subset_closure (hV_open n).2⟩
      · obtain ⟨K, hK_nhds, hK_closed, hKsub⟩ :=
          exists_mem_nhds_isClosed_subset (isClosed_singleton.isOpen_compl.mem_nhds (Ne.symm hyx))
        obtain ⟨W, hWK, hW_open, hxW⟩ := mem_nhds_iff.mp hK_nhds
        obtain ⟨N, hNB⟩ := hB_base W hW_open hxW
        have hy_not_VN : y ∉ closure (V N) := by
          intro h
          have hyK : y ∈ K := (hK_closed.closure_subset_iff.mpr ((hV_sub_B N).trans (hNB.trans hWK))) h
          exact hKsub hyK rfl
        let 𝓖_low : Set (Set X) := { U ∈ 𝓖 | ∃ n < N, U = V n }
        have hsplit : ⋃₀ 𝓖 ⊆ ⋃₀ 𝓖_low ∪ V N := by
          rintro z ⟨U, hU𝓖, hzU⟩
          obtain ⟨n, rfl⟩ := h𝓖 hU𝓖
          by_cases hlt : n < N
          · exact Or.inl ⟨V n, ⟨hU𝓖, n, hlt, rfl⟩, hzU⟩
          · exact Or.inr (hV_anti (not_lt.mp hlt) hzU)
        have hy_u : y ∈ closure (⋃₀ 𝓖_low) ∪ closure (V N) := by
          rw [← closure_union]
          exact closure_mono hsplit hy
        rcases hy_u with hy_low | hy_high
        · have hfin : 𝓖_low.Finite := by
            refine ((finite_Iio N).image V).subset ?_
            rintro U ⟨_, n, hlt, rfl⟩
            exact ⟨n, hlt, rfl⟩
          rw [hfin.closure_sUnion] at hy_low
          obtain ⟨U, hU, hyU⟩ := mem_iUnion₂.mp hy_low
          exact ⟨closure U, mem_image_of_mem _ hU.1, hyU⟩
        · exact (hy_not_VN hy_high).elim
    · exact sUnion_subset (by rintro _ ⟨U, hU, rfl⟩; exact closure_mono (subset_sUnion_of_mem hU))

/-- Theorem 9: In any `M₃`-space `X` (without even assuming `M₁`), if `X \ {x}`
is a `σ`-closed-discrete union `⋃ k, E k` of first-countable points (for example,
isolated points, as in `S_ω` or countable/scattered `M₃`-spaces), then `x` admits
a CP regular-closed neighborhood base (and hence a CP open outer base). -/
theorem L0028_of_sigma_closed_discrete_firstCountable_compl
    (X : Type) [TopologicalSpace X] (hM3 : MSpace.IsM3 X) (x : X)
    (E : ℕ → Set X)
    (hE_disc : ∀ k, ∀ A ⊆ E k, IsClosed A)
    (hE_cover : ({x}ᶜ : Set X) ⊆ ⋃ k, E k)
    (hE_fc : ∀ k, ∀ p ∈ E k, ∃ B : ℕ → Set X,
      (∀ n, IsOpen (B n) ∧ p ∈ B n) ∧
      (∀ U : Set X, IsOpen U → p ∈ U → ∃ n, B n ⊆ U)) :
    ∃ 𝓚' : Set (Set X),
      (∀ K ∈ 𝓚', IsClosed K ∧ closure (interior K) = K ∧ x ∈ interior K) ∧
      (∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚', K ⊆ U) ∧
      MSpace.ClosurePreserving 𝓚' := by
  have : T3Space X := hM3.1
  obtain ⟨𝓚, h𝓚_nhd, h𝓚_base, h𝓚_cp⟩ :=
    M3_closed_subset_has_cp_closed_nhds X hM3 {x} isClosed_singleton
  refine L0028_of_boundary_cp_trace X hM3 x 𝓚
    (fun K hK => ⟨(h𝓚_nhd K hK).1, singleton_subset_iff.mp (h𝓚_nhd K hK).2⟩)
    (fun U hU hxU => h𝓚_base U hU (singleton_subset_iff.mpr hxU))
    h𝓚_cp E hE_disc
    (fun k p hp => by
      obtain ⟨B, hBo, hBb⟩ := hE_fc k p hp
      exact hasCPOpenLocalBase_of_countable_nhds X p B hBo hBb)
    (fun K hK y hyK => subset_closure ?_)
  by_cases hyx : y = x
  · exact Or.inl (hyx ▸ singleton_subset_iff.mp (h𝓚_nhd K hK).2)
  · exact Or.inr ⟨hyK, hE_cover hyx⟩

/-- Theorem 10: Every `M₁`-space admits a `σ`-closure-preserving basis of
regular open sets (`interior (closure R) = R`). -/
theorem M1_has_sigma_cp_regular_open_basis (X : Type) [TopologicalSpace X]
    (hM1 : MSpace.IsM1 X) :
    ∃ 𝓡' : ℕ → Set (Set X),
      (∀ n, ∀ R ∈ 𝓡' n, IsOpen R ∧ interior (closure R) = R) ∧
      (∀ n, MSpace.ClosurePreserving (𝓡' n)) ∧
      IsTopologicalBasis (⋃ n, 𝓡' n) := by
  have : T3Space X := hM1.1
  obtain ⟨_, 𝓑, h𝓑_basis, 𝓑', h𝓑'_cp, h𝓑_eq⟩ := hM1
  let reg : Set X → Set X := fun B => interior (closure B)
  have hreg_cl : ∀ n, ∀ B ∈ 𝓑' n, closure (reg B) = closure B := by
    intro n B hBn
    have hBo : IsOpen B := h𝓑_basis.isOpen (h𝓑_eq.symm ▸ mem_iUnion.mpr ⟨n, hBn⟩)
    apply Subset.antisymm
    · exact closure_minimal interior_subset isClosed_closure
    · exact closure_mono (interior_maximal subset_closure hBo)
  let 𝓡' : ℕ → Set (Set X) := fun n => reg '' 𝓑' n
  refine ⟨𝓡', ?_, ?_, ?_⟩
  · rintro n _ ⟨B, hBn, rfl⟩
    refine ⟨isOpen_interior, ?_⟩
    rw [hreg_cl n B hBn]
  · intro n 𝓖 h𝓖
    apply Subset.antisymm
    · let 𝓗 : Set (Set X) := { B ∈ 𝓑' n | reg B ∈ 𝓖 }
      have hsub : ⋃₀ 𝓖 ⊆ ⋃₀ (closure '' 𝓗) := by
        rintro z ⟨R, hR𝓖, hzR⟩
        obtain ⟨B, hBn, rfl⟩ := h𝓖 hR𝓖
        exact ⟨closure B, ⟨B, ⟨hBn, hR𝓖⟩, rfl⟩, interior_subset hzR⟩
      have hcl_H : closure (⋃₀ (closure '' 𝓗)) = ⋃₀ (closure '' 𝓗) := by
        rw [← h𝓑'_cp n 𝓗 (fun _ h => h.1), closure_closure]
      intro z hz
      have hz' : z ∈ ⋃₀ (closure '' 𝓗) := hcl_H ▸ closure_mono hsub hz
      obtain ⟨_, ⟨B, ⟨hBn, hB𝓖⟩, rfl⟩, hzB⟩ := hz'
      refine ⟨closure (reg B), mem_image_of_mem _ hB𝓖, ?_⟩
      rwa [hreg_cl n B hBn]
    · exact sUnion_subset (by rintro _ ⟨R, hR, rfl⟩; exact closure_mono (subset_sUnion_of_mem hR))
  · have hopen : ∀ R ∈ ⋃ n, 𝓡' n, IsOpen R := by
      intro R hR
      obtain ⟨n, B, _, rfl⟩ := mem_iUnion.mp hR
      exact isOpen_interior
    refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    intro x U hxU hU_open
    obtain ⟨K, hK_nhds, hK_closed, hKU⟩ := exists_mem_nhds_isClosed_subset (hU_open.mem_nhds hxU)
    obtain ⟨V, hVK, hV_open, hxV⟩ := mem_nhds_iff.mp hK_nhds
    obtain ⟨B, hB𝓑, hxB, hBV⟩ := h𝓑_basis.exists_subset_of_mem_open hxV hV_open
    rw [h𝓑_eq, mem_iUnion] at hB𝓑
    obtain ⟨n, hBn⟩ := hB𝓑
    have hBo : IsOpen B := h𝓑_basis.isOpen (h𝓑_eq.symm ▸ mem_iUnion.mpr ⟨n, hBn⟩)
    refine ⟨reg B, mem_iUnion.mpr ⟨n, B, hBn, rfl⟩,
      interior_maximal subset_closure hBo hxB, ?_⟩
    exact interior_subset.trans ((hK_closed.closure_subset_iff.mpr (hBV.trans hVK)).trans hKU)

/-- Theorem 11: Every open subspace of an `M₁`-space is an `M₁`-space. -/
theorem M1_open_subspace (X : Type) [TopologicalSpace X] (hM1 : MSpace.IsM1 X)
    (U : Set X) (hU : IsOpen U) :
    MSpace.IsM1 ↥U := by
  have : T3Space X := hM1.1
  obtain ⟨_, 𝓑, h𝓑_basis, 𝓑', h𝓑'_cp, h𝓑_eq⟩ := hM1
  let 𝓤' : ℕ → Set (Set ↥U) := fun n =>
    { S : Set ↥U | ∃ B ∈ 𝓑' n, B ⊆ U ∧ S = Subtype.val ⁻¹' B }
  refine ⟨inferInstance, ⋃ n, 𝓤' n, ?_, 𝓤', ?_, rfl⟩
  · have hopen : ∀ S ∈ ⋃ n, 𝓤' n, IsOpen S := by
      intro S hS
      obtain ⟨n, B, hBn, _, rfl⟩ := mem_iUnion.mp hS
      have hBo : IsOpen B := h𝓑_basis.isOpen (h𝓑_eq.symm ▸ mem_iUnion.mpr ⟨n, hBn⟩)
      exact hBo.preimage continuous_subtype_val
    refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    intro x O hxO hO_open
    obtain ⟨W, hW_open, rfl⟩ := isOpen_induced_iff.mp hO_open
    have hWU_open : IsOpen (W ∩ U) := hW_open.inter hU
    have hxWU : (x : X) ∈ W ∩ U := ⟨hxO, x.2⟩
    obtain ⟨B, hB𝓑, hxB, hBWU⟩ := h𝓑_basis.exists_subset_of_mem_open hxWU hWU_open
    rw [h𝓑_eq, mem_iUnion] at hB𝓑
    obtain ⟨n, hBn⟩ := hB𝓑
    refine ⟨Subtype.val ⁻¹' B, mem_iUnion.mpr ⟨n, B, hBn, hBWU.trans inter_subset_right, rfl⟩,
      hxB, fun y hy => (hBWU hy).1⟩
  · intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      let 𝓗 : Set (Set X) := { B ∈ 𝓑' n | B ⊆ U ∧ Subtype.val ⁻¹' B ∈ 𝓖 }
      have hval_sub : Subtype.val '' (⋃₀ 𝓖) ⊆ ⋃₀ 𝓗 := by
        rintro _ ⟨z, ⟨S, hS𝓖, hzS⟩, rfl⟩
        obtain ⟨B, hBn, hBU, rfl⟩ := h𝓖 hS𝓖
        exact ⟨B, ⟨hBn, hBU, hS𝓖⟩, hzS⟩
      have hy_img : (y : X) ∈ Subtype.val '' closure (⋃₀ 𝓖) := ⟨y, hy, rfl⟩
      have hy_cl : (y : X) ∈ closure (⋃₀ 𝓗) :=
        closure_mono hval_sub (image_closure_subset_closure_image continuous_subtype_val hy_img)
      rw [h𝓑'_cp n 𝓗 (fun _ h => h.1)] at hy_cl
      obtain ⟨_, ⟨B, ⟨hBn, hBU, hB𝓖⟩, rfl⟩, hyB⟩ := hy_cl
      refine ⟨closure (Subtype.val ⁻¹' B), mem_image_of_mem _ hB𝓖, ?_⟩
      rw [mem_closure_iff]
      intro O hO hyO
      obtain ⟨W, hW_open, rfl⟩ := isOpen_induced_iff.mp hO
      obtain ⟨z, ⟨hzW, hzU⟩, hzB⟩ :=
        mem_closure_iff.mp hyB (W ∩ U) (hW_open.inter hU) ⟨hyO, y.2⟩
      exact ⟨⟨z, hzU⟩, hzW, hzB⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Theorem 12 (Countable Closed Sum Theorem for `M₃`-spaces with CP outer bases):
If an `M₃`-space `X` is covered by countably many closed subsets `F : ℕ → Set X`
such that every closed subset contained in any `F k` admits a CP open outer base
in `X`, then `X` is an `M₁`-space. -/
theorem M3_is_M1_of_countable_closed_cover_with_cp_outer_bases
    (X : Type) [TopologicalSpace X] (hM3 : MSpace.IsM3 X)
    (F : ℕ → Set X) (hF_closed : ∀ k, IsClosed (F k))
    (hF_cover : ⋃ k, F k = univ)
    (hcp : ∀ k, ∀ A : Set X, IsClosed A → A ⊆ F k →
      ∃ 𝓥 : Set (Set X),
        (∀ V ∈ 𝓥, IsOpen V ∧ A ⊆ V) ∧
        (∀ U : Set X, IsOpen U → A ⊆ U → ∃ V ∈ 𝓥, V ⊆ U) ∧
        MSpace.ClosurePreserving 𝓥) :
    MSpace.IsM1 X := by
  have : T3Space X := hM3.1
  have hpara : ParacompactSpace X :=
    Proofs.L_0005.main X ⟨inferInstance, Proofs.L_0010.main X hM3⟩
  obtain ⟨𝓕, h𝓕_closed, h𝓕_disc, h𝓕_net⟩ := M3_is_sigma_space X hM3
  let 𝓝' : ℕ → Set (Set X) := fun r =>
    (fun H : Set X => H ∩ F (Nat.unpair r).2) '' 𝓕 (Nat.unpair r).1
  have h𝓝'_closed : ∀ r, ∀ A ∈ 𝓝' r, IsClosed A := by
    rintro r _ ⟨H, hH, rfl⟩
    exact (h𝓕_closed _ H hH).inter (hF_closed _)
  have h𝓝'_sub : ∀ r, ∀ A ∈ 𝓝' r, A ⊆ F (Nat.unpair r).2 := by
    rintro r _ ⟨H, _, rfl⟩
    exact inter_subset_right
  have h𝓝'_disc : ∀ r, ∀ y : X, ∃ O : Set X, IsOpen O ∧ y ∈ O ∧
      ∀ A₁ ∈ 𝓝' r, ∀ A₂ ∈ 𝓝' r, (O ∩ A₁).Nonempty → (O ∩ A₂).Nonempty → A₁ = A₂ := by
    intro r y
    obtain ⟨O, hO_open, hyO, hO_uniq⟩ := h𝓕_disc (Nat.unpair r).1 y
    refine ⟨O, hO_open, hyO, ?_⟩
    rintro _ ⟨H₁, hH₁, rfl⟩ _ ⟨H₂, hH₂, rfl⟩ ⟨w₁, hw₁O, hw₁⟩ ⟨w₂, hw₂O, hw₂⟩
    have hEq := hO_uniq H₁ hH₁ H₂ hH₂ ⟨w₁, hw₁O, hw₁.1⟩ ⟨w₂, hw₂O, hw₂.1⟩
    rw [hEq]
  have hexp : ∀ r : ℕ, ∃ O : ↥(𝓝' r) → Set X,
      (∀ A : ↥(𝓝' r), IsOpen (O A) ∧ A.1 ⊆ O A) ∧
      Pairwise (fun A₁ A₂ : ↥(𝓝' r) => Disjoint (closure (O A₁)) (closure (O A₂))) ∧
      (∀ y : X, ∃ N : Set X, IsOpen N ∧ y ∈ N ∧
        ∀ A₁ A₂ : ↥(𝓝' r), (N ∩ closure (O A₁)).Nonempty → (N ∩ closure (O A₂)).Nonempty → A₁ = A₂) := by
    intro r
    refine collectionwise_normal_of_paracompact_t3 X (fun A : ↥(𝓝' r) => A.1)
      (fun A => h𝓝'_closed r A.1 A.2) ?_
    intro y
    obtain ⟨U, hU_open, hyU, hU_uniq⟩ := h𝓝'_disc r y
    exact ⟨U, hU_open, hyU, fun A₁ A₂ h1 h2 => Subtype.ext (hU_uniq A₁.1 A₁.2 A₂.1 A₂.2 h1 h2)⟩
  choose O hO_open hO_disj hO_disc using hexp
  have hcp_r : ∀ (r : ℕ) (A : ↥(𝓝' r)),
      ∃ 𝓥 : Set (Set X),
        (∀ V ∈ 𝓥, IsOpen V ∧ A.1 ⊆ V) ∧
        (∀ U : Set X, IsOpen U → A.1 ⊆ U → ∃ V ∈ 𝓥, V ⊆ U) ∧
        MSpace.ClosurePreserving 𝓥 := fun r A =>
    hcp (Nat.unpair r).2 A.1 (h𝓝'_closed r A.1 A.2) (h𝓝'_sub r A.1 A.2)
  choose 𝓥 h𝓥_open h𝓥_base h𝓥_cp using hcp_r
  let 𝓑' : ℕ → Set (Set X) := fun r =>
    { V : Set X | ∃ A : ↥(𝓝' r), V ∈ 𝓥 r A ∧ V ⊆ O r A }
  refine ⟨inferInstance, ⋃ r, 𝓑' r, ?_, 𝓑', ?_, rfl⟩
  · have hopen : ∀ V ∈ ⋃ r, 𝓑' r, IsOpen V := by
      intro V hV
      obtain ⟨r, A, hV𝓥, _⟩ := mem_iUnion.mp hV
      exact (h𝓥_open r A V hV𝓥).1
    refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    intro x U hxU hU_open
    obtain ⟨m, H, hHm, hxH, hHU⟩ := h𝓕_net x U hU_open hxU
    have hx_univ : x ∈ ⋃ k, F k := hF_cover.symm ▸ mem_univ x
    obtain ⟨k, hxFk⟩ := mem_iUnion.mp hx_univ
    let r := Nat.pair m k
    have hAmem : H ∩ F k ∈ 𝓝' r := by
      dsimp only [𝓝', r]; rw [Nat.unpair_pair]
      exact ⟨H, hHm, rfl⟩
    let A : ↥(𝓝' r) := ⟨H ∩ F k, hAmem⟩
    have hUO_open : IsOpen (U ∩ O r A) := hU_open.inter (hO_open r A).1
    have hA_sub : A.1 ⊆ U ∩ O r A := subset_inter (inter_subset_left.trans hHU) (hO_open r A).2
    obtain ⟨V, hV𝓥, hVsub⟩ := h𝓥_base r A (U ∩ O r A) hUO_open hA_sub
    refine ⟨V, mem_iUnion.mpr ⟨r, A, hV𝓥, hVsub.trans inter_subset_right⟩,
      (h𝓥_open r A V hV𝓥).2 ⟨hxH, hxFk⟩, hVsub.trans inter_subset_left⟩
  · intro r 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      obtain ⟨N, hN_open, hyN, hN_uniq⟩ := hO_disc r y
      by_cases hhit : ∃ A : ↥(𝓝' r), (N ∩ closure (O r A)).Nonempty
      · obtain ⟨A₀, hA₀⟩ := hhit
        let 𝓖₀ : Set (Set X) := { V ∈ 𝓖 | V ∈ 𝓥 r A₀ ∧ V ⊆ O r A₀ }
        have hsub : N ∩ ⋃₀ 𝓖 ⊆ ⋃₀ 𝓖₀ := by
          rintro z ⟨hzN, V, hV𝓖, hzV⟩
          obtain ⟨A, hV𝓥, hVO⟩ := h𝓖 hV𝓖
          have hAeq : A = A₀ := hN_uniq A A₀ ⟨z, hzN, subset_closure (hVO hzV)⟩ hA₀
          subst hAeq
          exact ⟨V, ⟨hV𝓖, hV𝓥, hVO⟩, hzV⟩
        have hy0 : y ∈ closure (⋃₀ 𝓖₀) :=
          closure_mono hsub (hN_open.inter_closure ⟨hyN, hy⟩)
        rw [h𝓥_cp r A₀ 𝓖₀ (fun _ h => h.2.1)] at hy0
        obtain ⟨_, ⟨V, hV, rfl⟩, hyV⟩ := hy0
        exact ⟨closure V, mem_image_of_mem _ hV.1, hyV⟩
      · exfalso
        obtain ⟨z, hzN, hzU⟩ := mem_closure_iff.mp hy N hN_open hyN
        obtain ⟨V, hV𝓖, hzV⟩ := hzU
        obtain ⟨A, _, hVO⟩ := h𝓖 hV𝓖
        exact hhit ⟨A, z, hzN, subset_closure (hVO hzV)⟩
    · exact sUnion_subset (by rintro _ ⟨V, hV, rfl⟩; exact closure_mono (subset_sUnion_of_mem hV))

/-- Helper (Ceder 1961): The product `{B ×ˢ C | B ∈ 𝓑, C ∈ 𝓒}` of two
closure-preserving families is closure-preserving in `X × Y`. -/
theorem closurePreserving_prod {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {𝓑 : Set (Set X)} {𝓒 : Set (Set Y)}
    (h𝓑 : MSpace.ClosurePreserving 𝓑) (h𝓒 : MSpace.ClosurePreserving 𝓒) :
    MSpace.ClosurePreserving { S : Set (X × Y) | ∃ B ∈ 𝓑, ∃ C ∈ 𝓒, S = B ×ˢ C } := by
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · rintro ⟨x, y⟩ hxy
    let 𝓟 : Set (Set X × Set Y) :=
      { p : Set X × Set Y | p.1 ∈ 𝓑 ∧ p.2 ∈ 𝓒 ∧ p.1 ×ˢ p.2 ∈ 𝓖 }
    let 𝓟_in : Set (Set X × Set Y) := { p ∈ 𝓟 | x ∈ closure p.1 }
    let 𝓟_out : Set (Set X × Set Y) := { p ∈ 𝓟 | x ∉ closure p.1 }
    let 𝓑_out : Set (Set X) := Prod.fst '' 𝓟_out
    have h𝓑_out_sub : 𝓑_out ⊆ 𝓑 := by rintro _ ⟨p, hp, rfl⟩; exact hp.1.1
    have hx_not_cl : x ∉ closure (⋃₀ 𝓑_out) := by
      rw [h𝓑 𝓑_out h𝓑_out_sub]
      rintro ⟨_, ⟨B, ⟨p, hp, rfl⟩, rfl⟩, hxB⟩
      exact hp.2 hxB
    let Ux : Set X := (closure (⋃₀ 𝓑_out))ᶜ
    have hUx_open : IsOpen Ux := isClosed_closure.isOpen_compl
    have hxUx : x ∈ Ux := hx_not_cl
    let 𝓒_in : Set (Set Y) := Prod.snd '' 𝓟_in
    have h𝓒_in_sub : 𝓒_in ⊆ 𝓒 := by rintro _ ⟨p, hp, rfl⟩; exact hp.1.2.1
    have hy_cl : y ∈ closure (⋃₀ 𝓒_in) := by
      rw [mem_closure_iff]
      intro V hV hyV
      have hopen : IsOpen (Ux ×ˢ V) := hUx_open.prod hV
      obtain ⟨⟨x', y'⟩, ⟨hx'Ux, hy'V⟩, hzG⟩ :=
        mem_closure_iff.mp hxy (Ux ×ˢ V) hopen ⟨hxUx, hyV⟩
      obtain ⟨S, hS𝓖, hx'y'S⟩ := hzG
      obtain ⟨B, hB, C, hC, rfl⟩ := h𝓖 hS𝓖
      have hp_mem : (B, C) ∈ 𝓟 := ⟨hB, hC, hS𝓖⟩
      have hxB : x ∈ closure B := by
        by_contra hnot
        have hBout : B ∈ 𝓑_out := ⟨(B, C), ⟨hp_mem, hnot⟩, rfl⟩
        exact hx'Ux (subset_closure ⟨B, hBout, hx'y'S.1⟩)
      exact ⟨y', hy'V, C, ⟨(B, C), ⟨hp_mem, hxB⟩, rfl⟩, hx'y'S.2⟩
    rw [h𝓒 𝓒_in h𝓒_in_sub] at hy_cl
    obtain ⟨_, ⟨C, ⟨p, hp, rfl⟩, rfl⟩, hyC⟩ := hy_cl
    refine ⟨closure (p.1 ×ˢ p.2), mem_image_of_mem _ hp.1.2.2, ?_⟩
    rw [closure_prod_eq]
    exact ⟨hp.2, hyC⟩
  · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Theorem 13 (Ceder 1961): The product of two `M₁`-spaces is an `M₁`-space. -/
theorem M1_prod (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (hX : MSpace.IsM1 X) (hY : MSpace.IsM1 Y) :
    MSpace.IsM1 (X × Y) := by
  have : T3Space X := hX.1
  have : T3Space Y := hY.1
  obtain ⟨_, 𝓑, h𝓑_basis, 𝓑', h𝓑'_cp, h𝓑_eq⟩ := hX
  obtain ⟨_, 𝓒, h𝓒_basis, 𝓒', h𝓒'_cp, h𝓒_eq⟩ := hY
  let 𝓓' : ℕ → Set (Set (X × Y)) := fun r =>
    { S : Set (X × Y) | ∃ B ∈ 𝓑' (Nat.unpair r).1, ∃ C ∈ 𝓒' (Nat.unpair r).2, S = B ×ˢ C }
  refine ⟨inferInstance, ⋃ r, 𝓓' r, ?_, 𝓓', ?_, rfl⟩
  · have hopen : ∀ S ∈ ⋃ r, 𝓓' r, IsOpen S := by
      intro S hS
      obtain ⟨r, B, hB, C, hC, rfl⟩ := mem_iUnion.mp hS
      have hBo : IsOpen B := h𝓑_basis.isOpen (h𝓑_eq.symm ▸ mem_iUnion.mpr ⟨_, hB⟩)
      have hCo : IsOpen C := h𝓒_basis.isOpen (h𝓒_eq.symm ▸ mem_iUnion.mpr ⟨_, hC⟩)
      exact hBo.prod hCo
    refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    rintro ⟨x, y⟩ W hxyW hW_open
    obtain ⟨U, V, hU_open, hV_open, hxU, hyV, hUV⟩ :=
      isOpen_prod_iff.mp hW_open x y hxyW
    obtain ⟨B, hB𝓑, hxB, hBU⟩ := h𝓑_basis.exists_subset_of_mem_open hxU hU_open
    obtain ⟨C, hC𝓒, hyC, hCV⟩ := h𝓒_basis.exists_subset_of_mem_open hyV hV_open
    rw [h𝓑_eq, mem_iUnion] at hB𝓑
    rw [h𝓒_eq, mem_iUnion] at hC𝓒
    obtain ⟨m, hBm⟩ := hB𝓑
    obtain ⟨n, hCn⟩ := hC𝓒
    refine ⟨B ×ˢ C, mem_iUnion.mpr ⟨Nat.pair m n, ?_⟩, ⟨hxB, hyC⟩,
      (prod_mono hBU hCV).trans hUV⟩
    dsimp only [𝓓']; rw [Nat.unpair_pair]
    exact ⟨B, hBm, C, hCn, rfl⟩
  · intro r
    exact closurePreserving_prod (h𝓑'_cp (Nat.unpair r).1) (h𝓒'_cp (Nat.unpair r).2)

/-- Theorem 14: Closure-preserving open neighborhood bases are preserved under
finite products. -/
theorem hasCPOpenLocalBase_prod {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (hx : HasCPOpenLocalBase x) (hy : HasCPOpenLocalBase y) :
    HasCPOpenLocalBase (x, y) := by
  obtain ⟨𝓤, h𝓤_open, h𝓤_base, h𝓤_cp⟩ := hx
  obtain ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩ := hy
  refine ⟨{ S : Set (X × Y) | ∃ U ∈ 𝓤, ∃ V ∈ 𝓥, S = U ×ˢ V }, ?_, ?_,
    closurePreserving_prod h𝓤_cp h𝓥_cp⟩
  · rintro _ ⟨U, hU, V, hV, rfl⟩
    exact ⟨(h𝓤_open U hU).1.prod (h𝓥_open V hV).1, (h𝓤_open U hU).2, (h𝓥_open V hV).2⟩
  · intro W hW hxyW
    obtain ⟨U₀, V₀, hU₀, hV₀, hxU₀, hyV₀, hUV₀⟩ := isOpen_prod_iff.mp hW x y hxyW
    obtain ⟨U, hU, hUU₀⟩ := h𝓤_base U₀ hU₀ hxU₀
    obtain ⟨V, hV, hVV₀⟩ := h𝓥_base V₀ hV₀ hyV₀
    exact ⟨U ×ˢ V, ⟨U, hU, V, hV, rfl⟩, (prod_mono hUU₀ hVV₀).trans hUV₀⟩

/-- Theorem 15 (Countable Sum Theorem for `Ind = 0` on `σ`-closed-discrete normal spaces):
Every normal space `X` that is a countable union of closed discrete subsets `D n`
is strongly zero-dimensional: every closed `A` and open `U ⊇ A` are separated by
a clopen set `C` with `A ⊆ C ⊆ U`. -/
theorem sigma_closed_discrete_normal_is_strongly_zero_dim
    (X : Type) [TopologicalSpace X] [NormalSpace X]
    (D : ℕ → Set X) (hD_disc : ∀ n, ∀ S ⊆ D n, IsClosed S)
    (hD_cover : ⋃ n, D n = univ)
    (A U : Set X) (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ C : Set X, IsClopen C ∧ A ⊆ C ∧ C ⊆ U := by
  classical
  -- Inductively build pairs of disjoint closed sets (A n, B n) with separating open (G n, H n)
  have hstep : ∀ (n : ℕ) (P Q : Set X), IsClosed P → IsClosed Q → Disjoint P Q →
      ∃ G H : Set X, IsOpen G ∧ IsOpen H ∧
        P ∪ (D n \ Q) ⊆ G ∧ Q ∪ (D n ∩ Q) ⊆ H ∧ Disjoint (closure G) (closure H) := by
    intro n P Q hP hQ hPQ
    have h1 : IsClosed (P ∪ (D n \ Q)) := hP.union (hD_disc n (D n \ Q) sdiff_subset)
    have h2 : IsClosed (Q ∪ (D n ∩ Q)) := hQ.union (hD_disc n (D n ∩ Q) inter_subset_left)
    have hdisj : Disjoint (P ∪ (D n \ Q)) (Q ∪ (D n ∩ Q)) := by
      rw [Set.disjoint_left]
      rintro z (hzP | ⟨_, hzQ⟩) (hzQ' | ⟨_, hzQ'⟩)
      · exact Set.disjoint_left.mp hPQ hzP hzQ'
      · exact Set.disjoint_left.mp hPQ hzP hzQ'
      · exact hzQ hzQ'
      · exact hzQ hzQ'
    obtain ⟨G₁, H₁, hG₁, hH₁, hsub1, hsub2, hGH₁⟩ := normal_separation h1 h2 hdisj
    -- Shrink to get disjoint closures via normality
    obtain ⟨G, G', hG, hG', hsubG, hsubG', hGG'⟩ :=
      normal_separation h1 hG₁.isClosed_compl (disjoint_compl_right_iff.mpr hsub1)
    have hclG_sub : closure G ⊆ G₁ :=
      (hG'.isClosed_compl.closure_subset_iff.mpr (hGG'.subset_compl_right)).trans
        (compl_subset_comm.mp hsubG')
    obtain ⟨H, H', hH, hH', hsubH, hsubH', hHH'⟩ :=
      normal_separation h2 hH₁.isClosed_compl (disjoint_compl_right_iff.mpr hsub2)
    have hclH_sub : closure H ⊆ H₁ :=
      (hH'.isClosed_compl.closure_subset_iff.mpr (hHH'.subset_compl_right)).trans
        (compl_subset_comm.mp hsubH')
    exact ⟨G, H, hG, hH, hsubG, hsubH, hGH₁.mono hclG_sub hclH_sub⟩
  -- Define the inductive sequence of states
  let State : Type := { s : Set X × Set X // IsClosed s.1 ∧ IsClosed s.2 ∧ Disjoint s.1 s.2 }
  let nextState : ℕ → State → State := fun n s =>
    let h := hstep n s.1.1 s.1.2 s.2.1 s.2.2.1 s.2.2.2
    ⟨(closure h.choose, closure h.choose_spec.choose),
      isClosed_closure, isClosed_closure, h.choose_spec.choose_spec.2.2.2.2⟩
  let st : ℕ → State := fun n =>
    Nat.rec ⟨(A, Uᶜ), hA, hU.isClosed_compl, disjoint_compl_right_iff.mpr hAU⟩ nextState n
  let G : ℕ → Set X := fun n => (hstep n (st n).1.1 (st n).1.2 (st n).2.1 (st n).2.2.1 (st n).2.2.2).choose
  let H : ℕ → Set X := fun n =>
    (hstep n (st n).1.1 (st n).1.2 (st n).2.1 (st n).2.2.1 (st n).2.2.2).choose_spec.choose
  have hspec : ∀ n, IsOpen (G n) ∧ IsOpen (H n) ∧
      (st n).1.1 ∪ (D n \ (st n).1.2) ⊆ G n ∧
      (st n).1.2 ∪ (D n ∩ (st n).1.2) ⊆ H n ∧
      Disjoint (closure (G n)) (closure (H n)) := fun n =>
    (hstep n (st n).1.1 (st n).1.2 (st n).2.1 (st n).2.2.1 (st n).2.2.2).choose_spec.choose_spec
  have hst_succ_1 : ∀ n, (st (n + 1)).1.1 = closure (G n) := fun _ => rfl
  have hst_succ_2 : ∀ n, (st (n + 1)).1.2 = closure (H n) := fun _ => rfl
  have hG_mono : ∀ m n, m ≤ n → G m ⊆ G n := by
    intro m n hmn
    induction hmn with
    | refl => exact Subset.rfl
    | @step k _ ih =>
      exact ih.trans (subset_closure.trans ((hst_succ_1 k).symm ▸ subset_union_left.trans (hspec (k + 1)).2.2.1))
  have hH_mono : ∀ m n, m ≤ n → H m ⊆ H n := by
    intro m n hmn
    induction hmn with
    | refl => exact Subset.rfl
    | @step k _ ih =>
      exact ih.trans (subset_closure.trans ((hst_succ_2 k).symm ▸ subset_union_left.trans (hspec (k + 1)).2.2.2.1))
  let C : Set X := ⋃ n, G n
  let C' : Set X := ⋃ n, H n
  have hC_open : IsOpen C := isOpen_iUnion fun n => (hspec n).1
  have hC'_open : IsOpen C' := isOpen_iUnion fun n => (hspec n).2.1
  have hCC'_disj : Disjoint C C' := by
    rw [Set.disjoint_left]
    intro z hzC hzC'
    obtain ⟨m, hzm⟩ := mem_iUnion.mp hzC
    obtain ⟨n, hzn⟩ := mem_iUnion.mp hzC'
    have hzm' : z ∈ G (max m n) := hG_mono m (max m n) (le_max_left m n) hzm
    have hzn' : z ∈ H (max m n) := hH_mono n (max m n) (le_max_right m n) hzn
    exact Set.disjoint_left.mp (hspec (max m n)).2.2.2.2 (subset_closure hzm') (subset_closure hzn')
  have hCC'_cover : C ∪ C' = univ := by
    refine eq_univ_of_forall fun z => ?_
    have hzD : z ∈ ⋃ n, D n := hD_cover.symm ▸ mem_univ z
    obtain ⟨n, hzn⟩ := mem_iUnion.mp hzD
    by_cases hQ : z ∈ (st n).1.2
    · exact Or.inr (mem_iUnion.mpr ⟨n, (hspec n).2.2.2.1 (Or.inr ⟨hzn, hQ⟩)⟩)
    · exact Or.inl (mem_iUnion.mpr ⟨n, (hspec n).2.2.1 (Or.inr ⟨hzn, hQ⟩)⟩)
  have hC_eq_compl : C = C'ᶜ := by
    ext z
    constructor
    · intro hzC hzC'; exact Set.disjoint_left.mp hCC'_disj hzC hzC'
    · intro hznot
      have h := hCC'_cover.symm ▸ mem_univ z
      rcases h with hzC | hzC'
      · exact hzC
      · exact (hznot hzC').elim
  refine ⟨C, ⟨hC_eq_compl ▸ hC'_open.isClosed_compl, hC_open⟩, ?_, ?_⟩
  · intro z hzA
    exact mem_iUnion.mpr ⟨0, (hspec 0).2.2.1 (Or.inl hzA)⟩
  · intro z hzC
    by_contra hznotU
    have hzC' : z ∈ C' := mem_iUnion.mpr ⟨0, (hspec 0).2.2.2.1 (Or.inl hznotU)⟩
    exact Set.disjoint_left.mp hCC'_disj hzC hzC'

/-- Theorem 16 (Locality of CP open local bases):
In a `T3Space`, `HasCPOpenLocalBase` is a purely local property: for any open
neighborhood `U` of `x`, `x` has a CP open local base in `X` iff `⟨x, hxU⟩` has
a CP open local base in the subspace `↥U`. -/
theorem hasCPOpenLocalBase_iff_open_subspace (X : Type) [TopologicalSpace X] [T3Space X]
    (U : Set X) (hU : IsOpen U) (x : X) (hxU : x ∈ U) :
    HasCPOpenLocalBase x ↔ HasCPOpenLocalBase (⟨x, hxU⟩ : ↥U) := by
  constructor
  · rintro ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩
    refine ⟨{ S : Set ↥U | ∃ V ∈ 𝓥, V ⊆ U ∧ S = Subtype.val ⁻¹' V }, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, _, rfl⟩
      exact ⟨(h𝓥_open V hV).1.preimage continuous_subtype_val, (h𝓥_open V hV).2⟩
    · intro O hO hxO
      obtain ⟨W, hW_open, rfl⟩ := isOpen_induced_iff.mp hO
      have hxWU : x ∈ W ∩ U := ⟨hxO, hxU⟩
      obtain ⟨V, hV, hVWU⟩ := h𝓥_base (W ∩ U) (hW_open.inter hU) hxWU
      exact ⟨Subtype.val ⁻¹' V, ⟨V, hV, hVWU.trans inter_subset_right, rfl⟩,
        fun y hy => (hVWU hy).1⟩
    · intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro y hy
        let 𝓗 : Set (Set X) := { V ∈ 𝓥 | V ⊆ U ∧ Subtype.val ⁻¹' V ∈ 𝓖 }
        have hval_sub : Subtype.val '' (⋃₀ 𝓖) ⊆ ⋃₀ 𝓗 := by
          rintro _ ⟨z, ⟨S, hS𝓖, hzS⟩, rfl⟩
          obtain ⟨V, hV, hVU, rfl⟩ := h𝓖 hS𝓖
          exact ⟨V, ⟨hV, hVU, hS𝓖⟩, hzS⟩
        have hy_img : (y : X) ∈ Subtype.val '' closure (⋃₀ 𝓖) := ⟨y, hy, rfl⟩
        have hy_cl : (y : X) ∈ closure (⋃₀ 𝓗) :=
          closure_mono hval_sub (image_closure_subset_closure_image continuous_subtype_val hy_img)
        rw [h𝓥_cp 𝓗 (fun _ h => h.1)] at hy_cl
        obtain ⟨_, ⟨V, ⟨_, _, hV𝓖⟩, rfl⟩, hyV⟩ := hy_cl
        refine ⟨closure (Subtype.val ⁻¹' V), mem_image_of_mem _ hV𝓖, ?_⟩
        rw [mem_closure_iff]
        intro O hO hyO
        obtain ⟨W, hW_open, rfl⟩ := isOpen_induced_iff.mp hO
        obtain ⟨z, ⟨hzW, hzU⟩, hzV⟩ :=
          mem_closure_iff.mp hyV (W ∩ U) (hW_open.inter hU) ⟨hyO, y.2⟩
        exact ⟨⟨z, hzU⟩, hzW, hzV⟩
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  · rintro ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩
    obtain ⟨K, hK_nhds, hK_closed, hKU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hxU)
    obtain ⟨W₀, hW₀K, hW₀_open, hxW₀⟩ := mem_nhds_iff.mp hK_nhds
    have hW₀_cl : closure W₀ ⊆ U := (hK_closed.closure_subset_iff.mpr hW₀K).trans hKU
    let W : Set ↥U := Subtype.val ⁻¹' W₀
    refine ⟨{ S : Set X | ∃ V ∈ 𝓥, V ⊆ W ∧ S = Subtype.val '' V }, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, _, rfl⟩
      exact ⟨hU.isOpenMap_subtype_val V (h𝓥_open V hV).1, ⟨⟨x, hxU⟩, (h𝓥_open V hV).2, rfl⟩⟩
    · intro O hO hxO
      let O' : Set ↥U := Subtype.val ⁻¹' (O ∩ W₀)
      have hO'_open : IsOpen O' := (hO.inter hW₀_open).preimage continuous_subtype_val
      have hxO' : (⟨x, hxU⟩ : ↥U) ∈ O' := ⟨hxO, hxW₀⟩
      obtain ⟨V, hV, hVO'⟩ := h𝓥_base O' hO'_open hxO'
      refine ⟨Subtype.val '' V, ⟨V, hV, fun y hy => (hVO' hy).2, rfl⟩, ?_⟩
      rintro _ ⟨y, hyV, rfl⟩
      exact (hVO' hyV).1
    · intro 𝓖 h𝓖
      apply Subset.antisymm
      · intro y hy
        let 𝓗 : Set (Set ↥U) := { V ∈ 𝓥 | V ⊆ W ∧ Subtype.val '' V ∈ 𝓖 }
        have hsub_W₀ : ⋃₀ 𝓖 ⊆ W₀ := by
          rintro z ⟨S, hS𝓖, hzS⟩
          obtain ⟨V, _, hVW, rfl⟩ := h𝓖 hS𝓖
          obtain ⟨w, hwV, rfl⟩ := hzS
          exact hVW hwV
        have hyU : y ∈ U := hW₀_cl (closure_mono hsub_W₀ hy)
        let y' : ↥U := ⟨y, hyU⟩
        have hy'_cl : y' ∈ closure (⋃₀ 𝓗) := by
          rw [mem_closure_iff]
          intro O hO hy'O
          obtain ⟨M, hM_open, rfl⟩ := isOpen_induced_iff.mp hO
          obtain ⟨z, ⟨hzM, hzU⟩, hzG⟩ :=
            mem_closure_iff.mp hy (M ∩ U) (hM_open.inter hU) ⟨hy'O, hyU⟩
          obtain ⟨S, hS𝓖, hzS⟩ := hzG
          obtain ⟨V, hV, hVW, rfl⟩ := h𝓖 hS𝓖
          obtain ⟨w, hwV, rfl⟩ := hzS
          exact ⟨w, hzM, V, ⟨hV, hVW, hS𝓖⟩, hwV⟩
        rw [h𝓥_cp 𝓗 (fun _ h => h.1)] at hy'_cl
        obtain ⟨_, ⟨V, ⟨_, _, hV𝓖⟩, rfl⟩, hy'V⟩ := hy'_cl
        refine ⟨closure (Subtype.val '' V), mem_image_of_mem _ hV𝓖, ?_⟩
        exact image_closure_subset_closure_image continuous_subtype_val ⟨y', hy'V, rfl⟩
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Theorem 17: Closed-and-open continuous maps preserve pointwise CP open
neighborhood bases. -/
theorem hasCPOpenLocalBase_of_isClosedMap_isOpenMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf_cont : Continuous f) (hf_closed : IsClosedMap f) (hf_open : IsOpenMap f)
    {x : X} (hx : HasCPOpenLocalBase x) :
    HasCPOpenLocalBase (f x) := by
  obtain ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩ := hx
  refine ⟨(fun V => f '' V) '' 𝓥, ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨hf_open V (h𝓥_open V hV).1, ⟨x, (h𝓥_open V hV).2, rfl⟩⟩
  · intro O hO hfxO
    obtain ⟨V, hV, hVfO⟩ := h𝓥_base (f ⁻¹' O) (hO.preimage hf_cont) hfxO
    exact ⟨f '' V, ⟨V, hV, rfl⟩, image_subset_iff.mpr hVfO⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      let 𝓗 : Set (Set X) := { V ∈ 𝓥 | f '' V ∈ 𝓖 }
      have hsub : ⋃₀ 𝓖 ⊆ f '' closure (⋃₀ 𝓗) := by
        rintro z ⟨S, hS𝓖, hzS⟩
        obtain ⟨V, hV, rfl⟩ := h𝓖 hS𝓖
        obtain ⟨w, hwV, rfl⟩ := hzS
        exact ⟨w, subset_closure ⟨V, ⟨hV, hS𝓖⟩, hwV⟩, rfl⟩
      have hcl : IsClosed (f '' closure (⋃₀ 𝓗)) := hf_closed _ isClosed_closure
      have hy' : y ∈ f '' closure (⋃₀ 𝓗) := closure_minimal hsub hcl hy
      obtain ⟨w, hw_cl, rfl⟩ := hy'
      rw [h𝓥_cp 𝓗 (fun _ h => h.1)] at hw_cl
      obtain ⟨_, ⟨V, ⟨_, hV𝓖⟩, rfl⟩, hwV⟩ := hw_cl
      refine ⟨closure (f '' V), mem_image_of_mem _ hV𝓖, ?_⟩
      exact image_closure_subset_closure_image hf_cont ⟨w, hwV, rfl⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Theorem 18: Every `T3Space` image of an `M₁`-space under a closed-and-open
continuous surjection is an `M₁`-space. -/
theorem M1_of_isClosedMap_isOpenMap_surjective
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T3Space Y]
    (hX : MSpace.IsM1 X) {f : X → Y}
    (hf_cont : Continuous f) (hf_closed : IsClosedMap f) (hf_open : IsOpenMap f)
    (hf_surj : Function.Surjective f) :
    MSpace.IsM1 Y := by
  obtain ⟨_, 𝓑, h𝓑_basis, 𝓑', h𝓑'_cp, h𝓑_eq⟩ := hX
  let 𝓒' : ℕ → Set (Set Y) := fun n => (fun B => f '' B) '' 𝓑' n
  refine ⟨inferInstance, ⋃ n, 𝓒' n, ?_, 𝓒', ?_, rfl⟩
  · have hopen : ∀ S ∈ ⋃ n, 𝓒' n, IsOpen S := by
      intro S hS
      obtain ⟨n, B, hBn, rfl⟩ := mem_iUnion.mp hS
      have hBo : IsOpen B := h𝓑_basis.isOpen (h𝓑_eq.symm ▸ mem_iUnion.mpr ⟨n, hBn⟩)
      exact hf_open B hBo
    refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    intro y O hyO hO_open
    obtain ⟨x, rfl⟩ := hf_surj y
    obtain ⟨B, hB𝓑, hxB, hBfO⟩ :=
      h𝓑_basis.exists_subset_of_mem_open hyO (hO_open.preimage hf_cont)
    rw [h𝓑_eq, mem_iUnion] at hB𝓑
    obtain ⟨n, hBn⟩ := hB𝓑
    exact ⟨f '' B, mem_iUnion.mpr ⟨n, B, hBn, rfl⟩, ⟨x, hxB, rfl⟩, image_subset_iff.mpr hBfO⟩
  · intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      let 𝓗 : Set (Set X) := { B ∈ 𝓑' n | f '' B ∈ 𝓖 }
      have hsub : ⋃₀ 𝓖 ⊆ f '' closure (⋃₀ 𝓗) := by
        rintro z ⟨S, hS𝓖, hzS⟩
        obtain ⟨B, hBn, rfl⟩ := h𝓖 hS𝓖
        obtain ⟨w, hwB, rfl⟩ := hzS
        exact ⟨w, subset_closure ⟨B, ⟨hBn, hS𝓖⟩, hwB⟩, rfl⟩
      have hcl : IsClosed (f '' closure (⋃₀ 𝓗)) := hf_closed _ isClosed_closure
      have hy' : y ∈ f '' closure (⋃₀ 𝓗) := closure_minimal hsub hcl hy
      obtain ⟨w, hw_cl, rfl⟩ := hy'
      rw [h𝓑'_cp n 𝓗 (fun _ h => h.1)] at hw_cl
      obtain ⟨_, ⟨B, ⟨_, hB𝓖⟩, rfl⟩, hwB⟩ := hw_cl
      refine ⟨closure (f '' B), mem_image_of_mem _ hB𝓖, ?_⟩
      exact image_closure_subset_closure_image hf_cont ⟨w, hwB, rfl⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Theorem 19 (Locally `M₁` paracompact `T₃` spaces are `M₁`):
Every paracompact `T3Space` (in particular, every `M₃`-space) in which every
point has an open `M₁`-neighborhood is itself an `M₁`-space. -/
theorem M1_of_locally_M1 (X : Type) [TopologicalSpace X] [T3Space X] [ParacompactSpace X]
    (hloc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ MSpace.IsM1 ↥U) :
    MSpace.IsM1 X := by
  classical
  -- Shrink each U x by regularity so closure (W x) ⊆ U x
  have hshrink : ∀ x : X, ∃ U W : Set X, IsOpen U ∧ IsOpen W ∧ x ∈ W ∧
      closure W ⊆ U ∧ MSpace.IsM1 ↥U := by
    intro x
    obtain ⟨U, hU_open, hxU, hU_M1⟩ := hloc x
    obtain ⟨K, hK_nhds, hK_closed, hKU⟩ := exists_mem_nhds_isClosed_subset (hU_open.mem_nhds hxU)
    obtain ⟨W, hWK, hW_open, hxW⟩ := mem_nhds_iff.mp hK_nhds
    exact ⟨U, W, hU_open, hW_open, hxW, (hK_closed.closure_subset_iff.mpr hWK).trans hKU, hU_M1⟩
  choose U W hU_open hW_open hxW hW_cl hU_M1 using hshrink
  have hW_cov : ⋃ x : X, W x = univ := eq_univ_of_forall fun x => mem_iUnion.mpr ⟨x, hxW x⟩
  obtain ⟨v, hv_open, hv_cov, hv_lf, hv_sub⟩ := precise_refinement W hW_open hW_cov
  have hv_cl_sub : ∀ x : X, closure (v x) ⊆ U x := fun x =>
    (closure_mono (hv_sub x)).trans (hW_cl x)
  -- For each x, extract a σ-CP open basis 𝓑' x of ↥(U x)
  have hbasis : ∀ x : X, ∃ 𝓑' : ℕ → Set (Set ↥(U x)),
      (∀ n, MSpace.ClosurePreserving (𝓑' n)) ∧
      IsTopologicalBasis (⋃ n, 𝓑' n) := by
    intro x
    obtain ⟨_, 𝓑, h𝓑b, 𝓑', h𝓑'cp, h𝓑eq⟩ := hU_M1 x
    exact ⟨𝓑', h𝓑'cp, h𝓑eq ▸ h𝓑b⟩
  choose 𝓑' h𝓑'_cp h𝓑'_basis using hbasis
  -- Push forward open sets contained in v x to X
  let 𝓒' : ℕ → Set (Set X) := fun n =>
    { S : Set X | ∃ x : X, ∃ B ∈ 𝓑' x n, Subtype.val '' B ⊆ v x ∧ S = Subtype.val '' B }
  refine ⟨inferInstance, ⋃ n, 𝓒' n, ?_, 𝓒', ?_, rfl⟩
  · have hopen : ∀ S ∈ ⋃ n, 𝓒' n, IsOpen S := by
      intro S hS
      obtain ⟨n, x, B, hBn, _, rfl⟩ := mem_iUnion.mp hS
      have hBo : IsOpen B := (h𝓑'_basis x).isOpen (mem_iUnion.mpr ⟨n, hBn⟩)
      exact (hU_open x).isOpenMap_subtype_val B hBo
    refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    intro y O hyO hO_open
    have hy_univ : y ∈ ⋃ x : X, v x := hv_cov.symm ▸ mem_univ y
    obtain ⟨x, hyv⟩ := mem_iUnion.mp hy_univ
    have hyU : y ∈ U x := hv_cl_sub x (subset_closure hyv)
    let O' : Set ↥(U x) := Subtype.val ⁻¹' (O ∩ v x)
    have hO'_open : IsOpen O' := (hO_open.inter (hv_open x)).preimage continuous_subtype_val
    have hyO' : (⟨y, hyU⟩ : ↥(U x)) ∈ O' := ⟨hyO, hyv⟩
    obtain ⟨B, hB, hyB, hBO'⟩ := (h𝓑'_basis x).exists_subset_of_mem_open hyO' hO'_open
    obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
    refine ⟨Subtype.val '' B, mem_iUnion.mpr ⟨n, x, B, hBn, ?_, rfl⟩,
      ⟨⟨y, hyU⟩, hyB, rfl⟩, ?_⟩
    · rintro _ ⟨w, hwB, rfl⟩; exact (hBO' hwB).2
    · rintro _ ⟨w, hwB, rfl⟩; exact (hBO' hwB).1
  · intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      obtain ⟨N, hN_nhds, hN_fin⟩ := hv_lf y
      obtain ⟨M, hMN, hM_open, hyM⟩ := mem_nhds_iff.mp hN_nhds
      let F : Set X := { x : X | (M ∩ v x).Nonempty }
      have hF_fin : F.Finite := hN_fin.subset fun x ⟨w, hwM, hwv⟩ => ⟨w, hwv, hMN hwM⟩
      let 𝓖x : X → Set (Set X) := fun x =>
        { S ∈ 𝓖 | ∃ B ∈ 𝓑' x n, Subtype.val '' B ⊆ v x ∧ S = Subtype.val '' B }
      have hsub : M ∩ ⋃₀ 𝓖 ⊆ ⋃ x ∈ F, ⋃₀ 𝓖x x := by
        rintro z ⟨hzM, S, hS𝓖, hzS⟩
        obtain ⟨x, B, hBn, hBv, rfl⟩ := h𝓖 hS𝓖
        have hxF : x ∈ F := ⟨z, hzM, hBv hzS⟩
        exact mem_iUnion₂.mpr ⟨x, hxF, Subtype.val '' B, ⟨hS𝓖, B, hBn, hBv, rfl⟩, hzS⟩
      have hy' : y ∈ closure (⋃ x ∈ F, ⋃₀ 𝓖x x) :=
        closure_mono hsub (hM_open.inter_closure ⟨hyM, hy⟩)
      rw [hF_fin.closure_biUnion] at hy'
      obtain ⟨x, _, hyx⟩ := mem_iUnion₂.mp hy'
      have hsub_v : ⋃₀ 𝓖x x ⊆ v x := by
        rintro z ⟨S, ⟨_, B, _, hBv, rfl⟩, hzS⟩
        exact hBv hzS
      have hyU : y ∈ U x := hv_cl_sub x (closure_mono hsub_v hyx)
      let y' : ↥(U x) := ⟨y, hyU⟩
      let 𝓗 : Set (Set ↥(U x)) :=
        { B ∈ 𝓑' x n | Subtype.val '' B ⊆ v x ∧ Subtype.val '' B ∈ 𝓖x x }
      have hy'_cl : y' ∈ closure (⋃₀ 𝓗) := by
        rw [mem_closure_iff]
        intro O hO hy'O
        obtain ⟨W₀, hW₀_open, rfl⟩ := isOpen_induced_iff.mp hO
        obtain ⟨z, ⟨hzW₀, hzU⟩, hzG⟩ :=
          mem_closure_iff.mp hyx (W₀ ∩ U x) (hW₀_open.inter (hU_open x)) ⟨hy'O, hyU⟩
        obtain ⟨S, hSGx, hzS⟩ := hzG
        obtain ⟨hS𝓖, B, hBn, hBv, rfl⟩ := hSGx
        obtain ⟨w, hwB, rfl⟩ := hzS
        exact ⟨w, hzW₀, B, ⟨hBn, hBv, ⟨hS𝓖, B, hBn, hBv, rfl⟩⟩, hwB⟩
      rw [h𝓑'_cp x n 𝓗 (fun _ h => h.1)] at hy'_cl
      obtain ⟨_, ⟨B, ⟨_, _, hBGx⟩, rfl⟩, hy'B⟩ := hy'_cl
      refine ⟨closure (Subtype.val '' B), mem_image_of_mem _ hBGx.1, ?_⟩
      exact image_closure_subset_closure_image continuous_subtype_val ⟨y', hy'B, rfl⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Theorem 20 (Closed-discrete excision for `M₁`):
In an `M₃`-space `X`, if `D ⊆ X` is closed discrete, every point `p ∈ D` has a
`σ`-CP open local base in `X`, and `X \ D` is an `M₁`-space, then `X` is `M₁`. -/
theorem M3_is_M1_of_closed_discrete_sigmaCP_and_M1_compl
    (X : Type) [TopologicalSpace X] (hM3 : MSpace.IsM3 X)
    (D : Set X) (hD_disc : ∀ A ⊆ D, IsClosed A)
    (hD_scp : ∀ p ∈ D, ∃ 𝓤 : ℕ → Set (Set X),
      (∀ n, ∀ U ∈ 𝓤 n, IsOpen U ∧ p ∈ U) ∧
      (∀ n, MSpace.ClosurePreserving (𝓤 n)) ∧
      (∀ O : Set X, IsOpen O → p ∈ O → ∃ n, ∃ U ∈ 𝓤 n, U ⊆ O))
    (hcompl_M1 : MSpace.IsM1 ↥(Dᶜ)) :
    MSpace.IsM1 X := by
  classical
  have : T3Space X := hM3.1
  have hpara : ParacompactSpace X :=
    Proofs.L_0005.main X ⟨inferInstance, Proofs.L_0010.main X hM3⟩
  have hD_closed : IsClosed D := hD_disc D Subset.rfl
  obtain ⟨G, hG, _⟩ := exists_monotone_stratification X hM3
  -- Part 1: Discrete open expansion of D
  obtain ⟨O, hO1, hO2, hO3⟩ := collectionwise_normal_of_paracompact_t3 X
    (fun p : ↥D => ({(p : X)} : Set X)) (fun _ => isClosed_singleton) (by
      intro y
      by_cases hy : y ∈ D
      · refine ⟨(D \ {y})ᶜ, (hD_disc (D \ {y}) sdiff_subset).isOpen_compl, fun h => h.2 rfl, ?_⟩
        intro p q ⟨w₁, hw₁, hw₁p⟩ ⟨w₂, hw₂, hw₂q⟩
        rw [mem_singleton_iff] at hw₁p hw₂q; subst hw₁p; subst hw₂q
        have hp : (p : X) = y := by by_contra hne; exact hw₁ ⟨p.2, hne⟩
        have hq : (q : X) = y := by by_contra hne; exact hw₂ ⟨q.2, hne⟩
        exact Subtype.ext (hp.trans hq.symm)
      · refine ⟨Dᶜ, hD_closed.isOpen_compl, hy, ?_⟩
        intro p _ ⟨w₁, hw₁, hw₁p⟩ _
        rw [mem_singleton_iff] at hw₁p; subst hw₁p
        exact (hw₁ p.2).elim)
  have hO_open : ∀ p : ↥D, IsOpen (O p) ∧ (p : X) ∈ O p := fun p =>
    ⟨(hO1 p).1, singleton_subset_iff.mp (hO1 p).2⟩
  choose 𝓤 h𝓤_open h𝓤_cp h𝓤_base using fun p : ↥D => hD_scp p.1 p.2
  let 𝓐' : ℕ → Set (Set X) := fun n =>
    { S : Set X | ∃ p : ↥D, S ∈ 𝓤 p n ∧ S ⊆ O p }
  have h𝓐'_cp : ∀ n, MSpace.ClosurePreserving (𝓐' n) := by
    intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      obtain ⟨N, hN_open, hyN, hN_uniq⟩ := hO3 y
      by_cases hhit : ∃ p : ↥D, (N ∩ closure (O p)).Nonempty
      · obtain ⟨p₀, hp₀⟩ := hhit
        let 𝓖₀ : Set (Set X) := { S ∈ 𝓖 | S ∈ 𝓤 p₀ n ∧ S ⊆ O p₀ }
        have hsub : N ∩ ⋃₀ 𝓖 ⊆ ⋃₀ 𝓖₀ := by
          rintro z ⟨hzN, S, hS𝓖, hzS⟩
          obtain ⟨p, hS𝓤, hSO⟩ := h𝓖 hS𝓖
          have hpeq : p = p₀ := hN_uniq p p₀ ⟨z, hzN, subset_closure (hSO hzS)⟩ hp₀
          subst hpeq
          exact ⟨S, ⟨hS𝓖, hS𝓤, hSO⟩, hzS⟩
        have hy0 : y ∈ closure (⋃₀ 𝓖₀) :=
          closure_mono hsub (hN_open.inter_closure ⟨hyN, hy⟩)
        rw [h𝓤_cp p₀ n 𝓖₀ (fun _ h => h.2.1)] at hy0
        obtain ⟨_, ⟨S, hS, rfl⟩, hyS⟩ := hy0
        exact ⟨closure S, mem_image_of_mem _ hS.1, hyS⟩
      · exfalso
        obtain ⟨z, hzN, S, hS𝓖, hzS⟩ := mem_closure_iff.mp hy N hN_open hyN
        obtain ⟨p, _, hSO⟩ := h𝓖 hS𝓖
        exact hhit ⟨p, z, hzN, subset_closure (hSO hzS)⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  -- Part 2: Push forward σ-CP basis of Dᶜ restricted to (closure (G k D))ᶜ
  obtain ⟨_, 𝓑, h𝓑_basis, 𝓑', h𝓑'_cp, h𝓑_eq⟩ := hcompl_M1
  let W : ℕ → Set X := fun k => (closure (G k D))ᶜ
  have hW_open : ∀ k, IsOpen (W k) := fun k => isClosed_closure.isOpen_compl
  have hW_cl : ∀ k, closure (W k) ⊆ Dᶜ := by
    intro k z hz hzD
    have hzG : z ∈ G k D := hG.2.1 k D hD_closed hzD
    obtain ⟨w, hwG, hwW⟩ := mem_closure_iff.mp hz (G k D) (hG.1 k D hD_closed) hzG
    exact hwW (subset_closure hwG)
  let 𝓒' : ℕ → ℕ → Set (Set X) := fun k m =>
    { S : Set X | ∃ B ∈ 𝓑' m, Subtype.val '' B ⊆ W k ∧ S = Subtype.val '' B }
  have h𝓒'_cp : ∀ k m, MSpace.ClosurePreserving (𝓒' k m) := by
    intro k m 𝓖 h𝓖
    apply Subset.antisymm
    · intro y hy
      have hsub_W : ⋃₀ 𝓖 ⊆ W k := by
        rintro z ⟨S, hS𝓖, hzS⟩
        obtain ⟨B, _, hBW, rfl⟩ := h𝓖 hS𝓖
        exact hBW hzS
      have hyD : y ∈ Dᶜ := hW_cl k (closure_mono hsub_W hy)
      let y' : ↥(Dᶜ) := ⟨y, hyD⟩
      let 𝓗 : Set (Set ↥(Dᶜ)) :=
        { B ∈ 𝓑' m | Subtype.val '' B ⊆ W k ∧ Subtype.val '' B ∈ 𝓖 }
      have hy'_cl : y' ∈ closure (⋃₀ 𝓗) := by
        rw [mem_closure_iff]
        intro U hU hy'U
        obtain ⟨M, hM_open, rfl⟩ := isOpen_induced_iff.mp hU
        obtain ⟨z, ⟨hzM, hzD⟩, hzG⟩ :=
          mem_closure_iff.mp hy (M ∩ Dᶜ) (hM_open.inter hD_closed.isOpen_compl) ⟨hy'U, hyD⟩
        obtain ⟨S, hS𝓖, hzS⟩ := hzG
        obtain ⟨B, hBm, hBW, rfl⟩ := h𝓖 hS𝓖
        obtain ⟨w, hwB, rfl⟩ := hzS
        exact ⟨w, hzM, B, ⟨hBm, hBW, hS𝓖⟩, hwB⟩
      rw [h𝓑'_cp m 𝓗 (fun _ h => h.1)] at hy'_cl
      obtain ⟨_, ⟨B, ⟨_, _, hB𝓖⟩, rfl⟩, hy'B⟩ := hy'_cl
      refine ⟨closure (Subtype.val '' B), mem_image_of_mem _ hB𝓖, ?_⟩
      exact image_closure_subset_closure_image continuous_subtype_val ⟨y', hy'B, rfl⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  -- Combine 𝓐' and 𝓒' into a single ℕ-indexed σ-CP open basis
  let 𝓓' : ℕ → Set (Set X) := fun r =>
    match r with
    | 0 => ∅
    | r + 1 =>
      if r % 2 = 0 then 𝓐' (r / 2)
      else 𝓒' (Nat.unpair (r / 2)).1 (Nat.unpair (r / 2)).2
  refine ⟨inferInstance, ⋃ r, 𝓓' r, ?_, 𝓓', ?_, rfl⟩
  · have hopen : ∀ S ∈ ⋃ r, 𝓓' r, IsOpen S := by
      intro S hS
      obtain ⟨r, hr⟩ := mem_iUnion.mp hS
      cases r with
      | zero => exact hr.elim
      | succ r =>
        dsimp only [𝓓'] at hr
        split_ifs at hr with h
        · obtain ⟨p, hS𝓤, _⟩ := hr
          exact (h𝓤_open p (r / 2) S hS𝓤).1
        · obtain ⟨B, hBm, _, rfl⟩ := hr
          have hBo : IsOpen B := h𝓑_basis.isOpen (h𝓑_eq.symm ▸ mem_iUnion.mpr ⟨_, hBm⟩)
          exact hD_closed.isOpen_compl.isOpenMap_subtype_val B hBo
    refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    intro y U hyU hU_open
    by_cases hyD : y ∈ D
    · let p : ↥D := ⟨y, hyD⟩
      obtain ⟨n, S, hS𝓤, hSUO⟩ := h𝓤_base p (U ∩ O p) (hU_open.inter (hO_open p).1) ⟨hyU, (hO_open p).2⟩
      refine ⟨S, mem_iUnion.mpr ⟨2 * n + 1, ?_⟩, (h𝓤_open p n S hS𝓤).2, hSUO.trans inter_subset_left⟩
      dsimp only [𝓓']
      have hmod : (2 * n) % 2 = 0 := by omega
      have hdiv : (2 * n) / 2 = n := by omega
      simp only [hmod, ↓reduceIte, hdiv]
      exact ⟨p, hS𝓤, hSUO.trans inter_subset_right⟩
    · have hy_not_iInter : y ∉ ⋂ k, closure (G k D) := by
        rw [hG.2.2.1 D hD_closed]; exact hyD
      rw [mem_iInter] at hy_not_iInter
      push Not at hy_not_iInter
      obtain ⟨k, hyW⟩ := hy_not_iInter
      let U' : Set ↥(Dᶜ) := Subtype.val ⁻¹' (U ∩ W k)
      have hU'_open : IsOpen U' := (hU_open.inter (hW_open k)).preimage continuous_subtype_val
      have hyU' : (⟨y, hyD⟩ : ↥(Dᶜ)) ∈ U' := ⟨hyU, hyW⟩
      obtain ⟨B, hB𝓑, hyB, hBU'⟩ := h𝓑_basis.exists_subset_of_mem_open hyU' hU'_open
      rw [h𝓑_eq, mem_iUnion] at hB𝓑
      obtain ⟨m, hBm⟩ := hB𝓑
      let q := Nat.pair k m
      refine ⟨Subtype.val '' B, mem_iUnion.mpr ⟨(2 * q + 1) + 1, ?_⟩,
        ⟨⟨y, hyD⟩, hyB, rfl⟩, ?_⟩
      · dsimp only [𝓓']
        have hmod : (2 * q + 1) % 2 ≠ 0 := by omega
        have hdiv : (2 * q + 1) / 2 = q := by omega
        simp only [hmod, ↓reduceIte, hdiv, show Nat.unpair q = (k, m) from Nat.unpair_pair k m]
        exact ⟨B, hBm, fun _ ⟨w, hwB, hw⟩ => hw ▸ (hBU' hwB).2, rfl⟩
      · rintro _ ⟨w, hwB, rfl⟩; exact (hBU' hwB).1
  · intro r
    cases r with
    | zero =>
      intro 𝓖 h𝓖
      have hG_empty : 𝓖 = ∅ := subset_empty_iff.mp h𝓖
      subst hG_empty; simp
    | succ r =>
      dsimp only [𝓓']
      split_ifs
      · exact h𝓐'_cp (r / 2)
      · exact h𝓒'_cp (Nat.unpair (r / 2)).1 (Nat.unpair (r / 2)).2

/-- Helper: Preimages of a closure-preserving family under a continuous open map
remain closure-preserving (since `closure (f ⁻¹' S) = f ⁻¹' (closure S)`). -/
theorem closurePreserving_preimage_of_isOpenMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf_cont : Continuous f) (hf_open : IsOpenMap f)
    {𝓑 : Set (Set Y)} (h𝓑 : MSpace.ClosurePreserving 𝓑) :
    MSpace.ClosurePreserving ((fun B => f ⁻¹' B) '' 𝓑) := by
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · intro x hx
    let 𝓗 : Set (Set Y) := { B ∈ 𝓑 | f ⁻¹' B ∈ 𝓖 }
    have hsub : ⋃₀ 𝓖 ⊆ f ⁻¹' (⋃₀ 𝓗) := by
      rintro z ⟨S, hS𝓖, hzS⟩
      obtain ⟨B, hB, rfl⟩ := h𝓖 hS𝓖
      exact ⟨B, ⟨hB, hS𝓖⟩, hzS⟩
    have hx' : x ∈ closure (f ⁻¹' (⋃₀ 𝓗)) := closure_mono hsub hx
    rw [← hf_open.preimage_closure_eq_closure_preimage hf_cont] at hx'
    change f x ∈ closure (⋃₀ 𝓗) at hx'
    rw [h𝓑 𝓗 (fun _ h => h.1)] at hx'
    obtain ⟨_, ⟨B, ⟨_, hB𝓖⟩, rfl⟩, hfxB⟩ := hx'
    refine ⟨closure (f ⁻¹' B), mem_image_of_mem _ hB𝓖, ?_⟩
    rw [← hf_open.preimage_closure_eq_closure_preimage hf_cont]
    exact hfxB
  · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

/-- Helper: Finite products `Fin k → X i` of `M₁`-spaces have CP cylinder families. -/
private theorem closurePreserving_fin_pi
    (X : ℕ → Type) [∀ i, TopologicalSpace (X i)]
    (𝓑 : ∀ i, Set (Set (X i))) (h𝓑 : ∀ i, MSpace.ClosurePreserving (𝓑 i)) :
    ∀ k : ℕ, MSpace.ClosurePreserving
      { S : Set (∀ i : Fin k, X i.1) |
        ∃ B : ∀ i : Fin k, Set (X i.1), (∀ i, B i ∈ 𝓑 i.1) ∧ S = Set.univ.pi B }
  | 0 => by
    intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro x hx
      rcases 𝓖.eq_empty_or_nonempty with rfl | ⟨S, hS𝓖⟩
      · simp at hx
      · obtain ⟨B, _, rfl⟩ := h𝓖 hS𝓖
        refine ⟨closure (Set.univ.pi B), mem_image_of_mem _ hS𝓖, subset_closure ?_⟩
        intro i; exact i.elim0
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
  | k + 1 => by
    have ih := closurePreserving_fin_pi X 𝓑 h𝓑 k
    -- Identify `(∀ i : Fin (k + 1), X i.1)` with `(∀ i : Fin k, X i.1) × X k`
    let e : (∀ i : Fin (k + 1), X i.1) ≃ₜ (∀ i : Fin k, X i.1) × X k :=
      { toFun := fun f => (fun i => f i.castSucc, f (Fin.last k))
        invFun := fun p => Fin.lastCases p.2 p.1
        left_inv := fun f => by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simp
          · simp
        right_inv := fun ⟨g, y⟩ => by
          ext i
          · simp
          · simp
        continuous_toFun := by
          refine Continuous.prodMk ?_ (continuous_apply (Fin.last k))
          exact continuous_pi fun i => continuous_apply i.castSucc
        continuous_invFun := by
          refine continuous_pi fun i => ?_
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simp only [Fin.lastCases_last]
            exact continuous_snd
          · simp only [Fin.lastCases_castSucc]
            exact (continuous_apply j).comp continuous_fst }
    have hprod := closurePreserving_prod ih (h𝓑 k)
    have hpre := closurePreserving_preimage_of_isOpenMap e.continuous e.isOpenMap hprod
    intro 𝓖 h𝓖
    refine hpre 𝓖 (fun S hS => ?_)
    obtain ⟨B, hB, rfl⟩ := h𝓖 hS
    let S₁ : Set (∀ i : Fin k, X i.1) := Set.univ.pi (fun i => B i.castSucc)
    let S₂ : Set (X k) := B (Fin.last k)
    refine ⟨S₁ ×ˢ S₂, ⟨S₁, ⟨fun i => B i.castSucc, fun i => hB i.castSucc, rfl⟩,
      S₂, hB (Fin.last k), rfl⟩, ?_⟩
    ext f
    simp only [mem_preimage, mem_prod, S₁, S₂, Set.mem_pi, mem_univ, true_implies]
    change (∀ i : Fin k, f i.castSucc ∈ B i.castSucc) ∧ f (Fin.last k) ∈ B (Fin.last k) ↔ _
    constructor
    · rintro ⟨h1, h2⟩ i
      exact Fin.lastCases h2 h1 i
    · intro hf
      exact ⟨fun i => hf i.castSucc, hf (Fin.last k)⟩

/-- Theorem 21 (Ceder 1961): Every countable product `(i : ℕ) → X i` of
`M₁`-spaces is an `M₁`-space. -/
theorem M1_countable_pi (X : ℕ → Type) [∀ i, TopologicalSpace (X i)]
    (hM1 : ∀ i, MSpace.IsM1 (X i)) :
    MSpace.IsM1 (∀ i : ℕ, X i) := by
  have hT3 : ∀ i, T3Space (X i) := fun i => (hM1 i).1
  -- Extract a monotone σ-CP open basis 𝓑' i containing univ at every level
  have hbas : ∀ i : ℕ, ∃ 𝓑' : ℕ → Set (Set (X i)),
      (∀ n, MSpace.ClosurePreserving (𝓑' n)) ∧
      (∀ n, 𝓑' n ⊆ 𝓑' (n + 1)) ∧
      (∀ n, univ ∈ 𝓑' n) ∧
      IsTopologicalBasis (⋃ n, 𝓑' n) := by
    intro i
    obtain ⟨_, 𝓑, h𝓑b, 𝓑₀, h𝓑₀cp, h𝓑eq⟩ := hM1 i
    let 𝓑' : ℕ → Set (Set (X i)) := fun n => insert univ (⋃ k ≤ n, 𝓑₀ k)
    refine ⟨𝓑', ?_, ?_, fun _ => mem_insert _ _, ?_⟩
    · intro n 𝓖 h𝓖
      apply Subset.antisymm
      · intro y hy
        by_cases huniv : univ ∈ 𝓖
        · exact ⟨closure univ, mem_image_of_mem _ huniv, by simp⟩
        · have hsub : 𝓖 ⊆ ⋃ k ≤ n, 𝓑₀ k := fun S hS =>
            (mem_insert_iff.mp (h𝓖 hS)).resolve_left (fun h => huniv (h ▸ hS))
          have hcp_le : MSpace.ClosurePreserving (⋃ k ≤ n, 𝓑₀ k) := by
            intro 𝓗 h𝓗
            apply Subset.antisymm
            · intro z hz
              have hsplit : ⋃₀ 𝓗 ⊆ ⋃ k ∈ Iic n, ⋃₀ (𝓗 ∩ 𝓑₀ k) := by
                rintro w ⟨B, hB𝓗, hwB⟩
                obtain ⟨k, hk, hBk⟩ := mem_iUnion₂.mp (h𝓗 hB𝓗)
                exact mem_iUnion₂.mpr ⟨k, hk, B, ⟨hB𝓗, hBk⟩, hwB⟩
              have hz' := closure_mono hsplit hz
              rw [(finite_Iic n).closure_biUnion] at hz'
              obtain ⟨k, _, hzk⟩ := mem_iUnion₂.mp hz'
              rw [h𝓑₀cp k (𝓗 ∩ 𝓑₀ k) inter_subset_right] at hzk
              obtain ⟨_, ⟨B, hB, rfl⟩, hzB⟩ := hzk
              exact ⟨closure B, mem_image_of_mem _ hB.1, hzB⟩
            · exact sUnion_subset (by rintro _ ⟨B, hB, rfl⟩; exact closure_mono (subset_sUnion_of_mem hB))
          rw [hcp_le 𝓖 hsub] at hy
          exact hy
      · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))
    · intro n S hS
      rcases mem_insert_iff.mp hS with rfl | hS'
      · exact mem_insert _ _
      · right
        obtain ⟨k, hk, hSk⟩ := mem_iUnion₂.mp hS'
        exact mem_iUnion₂.mpr ⟨k, Nat.le_succ_of_le hk, hSk⟩
    · have hopen : ∀ S ∈ ⋃ n, 𝓑' n, IsOpen S := by
        intro S hS
        obtain ⟨n, hSn⟩ := mem_iUnion.mp hS
        rcases mem_insert_iff.mp hSn with rfl | hSn'
        · exact isOpen_univ
        · obtain ⟨k, _, hSk⟩ := mem_iUnion₂.mp hSn'
          exact h𝓑b.isOpen (h𝓑eq.symm ▸ mem_iUnion.mpr ⟨k, hSk⟩)
      refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
      intro x U hxU hU_open
      obtain ⟨B, hB𝓑, hxB, hBU⟩ := h𝓑b.exists_subset_of_mem_open hxU hU_open
      rw [h𝓑eq, mem_iUnion] at hB𝓑
      obtain ⟨n, hBn⟩ := hB𝓑
      exact ⟨B, mem_iUnion.mpr ⟨n, Or.inr (mem_iUnion₂.mpr ⟨n, le_rfl, hBn⟩)⟩, hxB, hBU⟩
  choose 𝓑' h𝓑'_cp h𝓑'_mono h𝓑'_univ h𝓑'_basis using hbas
  have h𝓑'_le : ∀ i {m n : ℕ}, m ≤ n → 𝓑' i m ⊆ 𝓑' i n := by
    intro i m n hmn
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact ih.trans (h𝓑'_mono i _)
  -- Projection π k : (∀ i : ℕ, X i) → (∀ i : Fin k, X i.1) is continuous and open
  let π : ∀ k : ℕ, (∀ i : ℕ, X i) → (∀ i : Fin k, X i.1) := fun k f i => f i.1
  have hπ_cont : ∀ k, Continuous (π k) := fun k => continuous_pi fun i => continuous_apply i.1
  have hπ_open : ∀ k, IsOpenMap (π k) := by
    intro k U hU
    rw [isOpen_iff_forall_mem_open]
    rintro g ⟨f, hfU, rfl⟩
    obtain ⟨I, t, ht_all, htU⟩ := isOpen_pi_iff.mp hU f hfU
    let V : Set (∀ i : Fin k, X i.1) :=
      Set.univ.pi fun i => if i.1 ∈ I then t i.1 else univ
    refine ⟨V, ?_, isOpen_set_pi Set.finite_univ fun i _ => ?_, ?_⟩
    · intro h hh
      let f' : ∀ i : ℕ, X i := fun j => if hj : j < k then h ⟨j, hj⟩ else f j
      refine ⟨f', htU ?_, ?_⟩
      · intro j hjI
        dsimp only [f']
        split_ifs with hjk
        · have hmem := hh ⟨j, hjk⟩ (mem_univ _)
          dsimp only at hmem
          have hjI' : j ∈ I := Finset.mem_coe.mp hjI
          split_ifs at hmem
          exact hmem
        · exact (ht_all j hjI).2
      · funext i
        dsimp only [π, f']
        simp [i.2]
    · split_ifs with hi
      · exact (ht_all i.1 hi).1
      · exact isOpen_univ
    · intro i _
      dsimp only [π]
      split_ifs with hi
      · exact (ht_all i.1 hi).2
      · exact mem_univ _
  let 𝓒' : ℕ → ℕ → Set (Set (∀ i : ℕ, X i)) := fun k n =>
    (fun S => π k ⁻¹' S) ''
      { S : Set (∀ i : Fin k, X i.1) |
        ∃ B : ∀ i : Fin k, Set (X i.1), (∀ i, B i ∈ 𝓑' i.1 n) ∧ S = Set.univ.pi B }
  let 𝓓' : ℕ → Set (Set (∀ i : ℕ, X i)) := fun r =>
    𝓒' (Nat.unpair r).1 (Nat.unpair r).2
  refine ⟨inferInstance, ⋃ r, 𝓓' r, ?_, 𝓓', ?_, rfl⟩
  · have hopen : ∀ S ∈ ⋃ r, 𝓓' r, IsOpen S := by
      intro S hS
      obtain ⟨r, _, ⟨B, hB, rfl⟩, rfl⟩ := mem_iUnion.mp hS
      refine (isOpen_set_pi Set.finite_univ fun i _ => ?_).preimage (hπ_cont _)
      exact (h𝓑'_basis i.1).isOpen (mem_iUnion.mpr ⟨_, hB i⟩)
    refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    intro f U hfU hU_open
    obtain ⟨I, t, ht_all, htU⟩ := isOpen_pi_iff.mp hU_open f hfU
    have hpick : ∀ i : ℕ, ∃ n : ℕ, ∃ B ∈ 𝓑' i n, f i ∈ B ∧ (i ∈ I → B ⊆ t i) := by
      intro i
      by_cases hi : i ∈ I
      · obtain ⟨B, hB, hfiB, hBt⟩ :=
          (h𝓑'_basis i).exists_subset_of_mem_open (ht_all i hi).2 (ht_all i hi).1
        obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
        exact ⟨n, B, hBn, hfiB, fun _ => hBt⟩
      · exact ⟨0, univ, h𝓑'_univ i 0, mem_univ _, fun h => (hi h).elim⟩
    choose n_of B_of hB_mem hB_f hB_sub using hpick
    let k : ℕ := I.sup id + 1
    let N : ℕ := (Finset.range k).sup n_of
    let B : ∀ i : Fin k, Set (X i.1) := fun i => B_of i.1
    have hB_in : ∀ i : Fin k, B i ∈ 𝓑' i.1 N := fun i =>
      h𝓑'_le i.1 (Finset.le_sup (f := n_of) (Finset.mem_range.mpr i.2)) (hB_mem i.1)
    refine ⟨π k ⁻¹' Set.univ.pi B, mem_iUnion.mpr ⟨Nat.pair k N, ?_⟩, ?_, ?_⟩
    · dsimp only [𝓓', 𝓒']; rw [Nat.unpair_pair]
      exact ⟨Set.univ.pi B, ⟨B, hB_in, rfl⟩, rfl⟩
    · intro i _; exact hB_f i.1
    · intro g hg
      refine htU fun j hjI => ?_
      have hjk : j < k := Nat.lt_succ_of_le (Finset.le_sup (f := id) hjI)
      exact hB_sub j hjI (hg ⟨j, hjk⟩ (mem_univ _))
  · intro r
    exact closurePreserving_preimage_of_isOpenMap (hπ_cont _) (hπ_open _)
      (closurePreserving_fin_pi X (fun i => 𝓑' i (Nat.unpair r).2)
        (fun i => h𝓑'_cp i (Nat.unpair r).2) (Nat.unpair r).1)

/-- Theorem 22: Any disjoint union `Σ i : ι, X i` of `M₁`-spaces is an `M₁`-space. -/
theorem M1_sigma {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (hM1 : ∀ i, MSpace.IsM1 (X i)) :
    MSpace.IsM1 (Σ i : ι, X i) := by
  have hT3 : ∀ i, T3Space (X i) := fun i => (hM1 i).1
  have : RegularSpace (Σ i : ι, X i) := RegularSpace.of_exists_mem_nhds_isClosed_subset <| by
    rintro ⟨i, x⟩ U hU
    obtain ⟨O, hOU, hO_open, hixO⟩ := mem_nhds_iff.mp hU
    have hpre_open : IsOpen (Sigma.mk i ⁻¹' O) := hO_open.preimage continuous_sigmaMk
    obtain ⟨K, hK_nhds, hK_closed, hKO⟩ :=
      exists_mem_nhds_isClosed_subset (hpre_open.mem_nhds hixO)
    obtain ⟨W, hWK, hW_open, hxW⟩ := mem_nhds_iff.mp hK_nhds
    refine ⟨Sigma.mk i '' K, ?_, isClosedMap_sigmaMk K hK_closed, ?_⟩
    · exact mem_nhds_iff.mpr ⟨Sigma.mk i '' W, image_mono hWK,
        isOpenMap_sigmaMk W hW_open, ⟨x, hxW, rfl⟩⟩
    · exact (image_subset_iff.mpr hKO).trans hOU
  have : T3Space (Σ i : ι, X i) := ⟨⟩
  have hbas : ∀ i : ι, ∃ 𝓑' : ℕ → Set (Set (X i)),
      (∀ n, MSpace.ClosurePreserving (𝓑' n)) ∧
      IsTopologicalBasis (⋃ n, 𝓑' n) := by
    intro i
    obtain ⟨_, 𝓑, h𝓑b, 𝓑', h𝓑'cp, h𝓑eq⟩ := hM1 i
    exact ⟨𝓑', h𝓑'cp, h𝓑eq ▸ h𝓑b⟩
  choose 𝓑' h𝓑'_cp h𝓑'_basis using hbas
  let 𝓒' : ℕ → Set (Set (Σ i : ι, X i)) := fun n =>
    { S : Set (Σ i : ι, X i) | ∃ i : ι, ∃ B ∈ 𝓑' i n, S = Sigma.mk i '' B }
  refine ⟨inferInstance, ⋃ n, 𝓒' n, ?_, 𝓒', ?_, rfl⟩
  · have hopen : ∀ S ∈ ⋃ n, 𝓒' n, IsOpen S := by
      intro S hS
      obtain ⟨n, i, B, hBn, rfl⟩ := mem_iUnion.mp hS
      have hBo : IsOpen B := (h𝓑'_basis i).isOpen (mem_iUnion.mpr ⟨n, hBn⟩)
      exact isOpenMap_sigmaMk B hBo
    refine isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    rintro ⟨i, x⟩ U hixU hU_open
    have hpre_open : IsOpen (Sigma.mk i ⁻¹' U) := hU_open.preimage continuous_sigmaMk
    obtain ⟨B, hB, hxB, hBU⟩ := (h𝓑'_basis i).exists_subset_of_mem_open hixU hpre_open
    obtain ⟨n, hBn⟩ := mem_iUnion.mp hB
    exact ⟨Sigma.mk i '' B, mem_iUnion.mpr ⟨n, i, B, hBn, rfl⟩,
      ⟨x, hxB, rfl⟩, image_subset_iff.mpr hBU⟩
  · intro n 𝓖 h𝓖
    apply Subset.antisymm
    · rintro ⟨i, x⟩ hix
      let 𝓗 : Set (Set (X i)) := { B ∈ 𝓑' i n | Sigma.mk i '' B ∈ 𝓖 }
      have hx_cl : x ∈ closure (⋃₀ 𝓗) := by
        rw [mem_closure_iff]
        intro O hO hxO
        obtain ⟨z, hzO, S, hS𝓖, hzS⟩ :=
          mem_closure_iff.mp hix (Sigma.mk i '' O) (isOpenMap_sigmaMk O hO) ⟨x, hxO, rfl⟩
        obtain ⟨y, hyO, rfl⟩ := hzO
        obtain ⟨j, B, hBn, rfl⟩ := h𝓖 hS𝓖
        obtain ⟨w, hwB, hEq⟩ := hzS
        cases hEq
        exact ⟨y, hyO, B, ⟨hBn, hS𝓖⟩, hwB⟩
      rw [h𝓑'_cp i n 𝓗 (fun _ h => h.1)] at hx_cl
      obtain ⟨_, ⟨B, ⟨_, hB𝓖⟩, rfl⟩, hxB⟩ := hx_cl
      refine ⟨closure (Sigma.mk i '' B), mem_image_of_mem _ hB𝓖, ?_⟩
      exact image_closure_subset_closure_image continuous_sigmaMk ⟨x, hxB, rfl⟩
    · exact sUnion_subset (by rintro _ ⟨S, hS, rfl⟩; exact closure_mono (subset_sUnion_of_mem hS))

end Research.M3M1
