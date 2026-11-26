import Mathlib.Data.Nat.Pairing
import Specs.L_0026
import Proofs.L_0002
import Proofs.L_0003
import Proofs.L_0010

namespace Proofs.L_0026

open MSpace Set Topology

theorem main : Specs.L_0026.stmt := by
  unfold Specs.L_0026.stmt
  intro X _ hM1
  have : T3Space X := hM1.1
  obtain ⟨𝓑, h𝓑_basis, 𝓑', h𝓑'_cp, h𝓑_eq⟩ := hM1.2
  have hM2 : MSpace.IsM2 X := Proofs.L_0002.main X hM1
  have hM3 : MSpace.IsM3 X := Proofs.L_0003.main X hM2
  obtain ⟨G, hG_open, hG_sub, hG_inter, hG_mono⟩ := Proofs.L_0010.main X hM3
  -- Dual closed stratification F k U := (G k Uᶜ)ᶜ for open sets U
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
  -- Closure-preserving closed families 𝓒 n := closure '' 𝓑' n
  let 𝓒 : ℕ → Set (Set X) := fun n => closure '' 𝓑' n
  have h𝓒_sUnion_closed : ∀ n, ∀ 𝓖 ⊆ 𝓒 n, IsClosed (⋃₀ 𝓖) := by
    intro n 𝓖 h𝓖
    let 𝓖₀ : Set (Set X) := { B ∈ 𝓑' n | closure B ∈ 𝓖 }
    have h𝓖₀_sub : 𝓖₀ ⊆ 𝓑' n := fun _ h => h.1
    have himg : closure '' 𝓖₀ = 𝓖 := by
      ext C
      constructor
      · rintro ⟨B, hB, rfl⟩
        exact hB.2
      · intro hC
        obtain ⟨B, hB, rfl⟩ := h𝓖 hC
        exact ⟨B, ⟨hB, hC⟩, rfl⟩
    have hcp := h𝓑'_cp n 𝓖₀ h𝓖₀_sub
    rw [himg] at hcp
    rw [← hcp]
    exact isClosed_closure
  -- Equivalence-class pieces M n x, W n x, H n k x
  let M : ℕ → X → Set X := fun n x => ⋂₀ { C ∈ 𝓒 n | x ∈ C }
  let W : ℕ → X → Set X := fun n x => (⋃₀ { C ∈ 𝓒 n | x ∉ C })ᶜ
  let H : ℕ → ℕ → X → Set X := fun n k x => M n x ∩ F k (W n x)
  have hW_open : ∀ n x, IsOpen (W n x) := fun n x =>
    (h𝓒_sUnion_closed n { C ∈ 𝓒 n | x ∉ C } (fun _ h => h.1)).isOpen_compl
  have hW_mem : ∀ n x, x ∈ W n x := by
    intro n x hx
    obtain ⟨C, ⟨_, hxC⟩, hxC'⟩ := hx
    exact hxC hxC'
  have hM_mem : ∀ n x, x ∈ M n x := by
    intro n x C hC
    exact hC.2
  have hH_equiv : ∀ n k a w, w ∈ H n k a → ∀ C ∈ 𝓒 n, w ∈ C ↔ a ∈ C := by
    intro n k a w hw C hC
    constructor
    · intro hwC
      by_contra haC
      have hwW : w ∈ W n a := hF_sub k (W n a) (hW_open n a) hw.2
      exact hwW ⟨C, ⟨hC, haC⟩, hwC⟩
    · intro haC
      exact hw.1 C ⟨hC, haC⟩
  have hH_eq_of_equiv : ∀ n k a b, (∀ C ∈ 𝓒 n, a ∈ C ↔ b ∈ C) → H n k a = H n k b := by
    intro n k a b hab
    have hM : M n a = M n b := by
      dsimp only [M]
      congr 1
      ext C
      exact ⟨fun ⟨hC, ha⟩ => ⟨hC, (hab C hC).mp ha⟩, fun ⟨hC, hb⟩ => ⟨hC, (hab C hC).mpr hb⟩⟩
    have hW : W n a = W n b := by
      dsimp only [W]
      congr 2
      ext C
      exact ⟨fun ⟨hC, ha⟩ => ⟨hC, fun hb => ha ((hab C hC).mpr hb)⟩,
             fun ⟨hC, hb⟩ => ⟨hC, fun ha => hb ((hab C hC).mp ha)⟩⟩
    dsimp only [H]
    rw [hM, hW]
  -- Any union of H n k a is closed
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
        rw [mem_singleton_iff] at huz
        subst huz
        exact hu ⟨C₀, ⟨hC₀, haC₀⟩, hzC₀⟩
      have hwF : w ∈ F k ({z}ᶜ) :=
        hF_mono k (W n a) ({z}ᶜ) (hW_open n a) hzc_open hWa_sub hwH.2
      exact hwO.2 hwF
    · let O : Set X := W n z \ F k (W n z)
      have hO_open : IsOpen O := (hW_open n z).sdiff (hF_closed k (W n z) (hW_open n z))
      have hO_mem : z ∈ O := ⟨hW_mem n z, hzF⟩
      obtain ⟨w, hwO, hwU⟩ := mem_closure_iff.mp hz O hO_open hO_mem
      obtain ⟨a, _, hwH⟩ := mem_iUnion₂.mp hwU
      have hWa_sub : W n a ⊆ W n z := by
        intro u hu ⟨C, ⟨hC, hzC⟩, huC⟩
        have haC : a ∉ C := by
          intro haC
          have hwC : w ∈ C := (hH_equiv n k a w hwH C hC).mpr haC
          exact hwO.1 ⟨C, ⟨hC, hzC⟩, hwC⟩
        exact hu ⟨C, ⟨hC, haC⟩, huC⟩
      have hwF : w ∈ F k (W n z) :=
        hF_mono k (W n a) (W n z) (hW_open n a) (hW_open n z) hWa_sub hwH.2
      exact hwO.2 hwF
  -- Pick one representative from each nonempty H n k a
  let P : ℕ → ℕ → Type := fun n k => { S : Set X // (∃ a : X, S = H n k a) ∧ S.Nonempty }
  let D' : ℕ → ℕ → Set X := fun n k => Set.range (fun S : P n k => S.2.2.some)
  have hD'_self : ∀ n k, ∀ e ∈ D' n k, e ∈ H n k e := by
    rintro n k _ ⟨S, rfl⟩
    obtain ⟨a, hSa⟩ := S.2.1
    have hmem : S.2.2.some ∈ H n k a := hSa ▸ S.2.2.some_mem
    have heq : H n k S.2.2.some = H n k a :=
      hH_eq_of_equiv n k S.2.2.some a (hH_equiv n k a S.2.2.some hmem)
    rw [heq]
    exact hmem
  have hD'_inj : ∀ n k, ∀ e₁ ∈ D' n k, ∀ e₂ ∈ D' n k, H n k e₁ = H n k e₂ → e₁ = e₂ := by
    rintro n k _ ⟨S₁, rfl⟩ _ ⟨S₂, rfl⟩ hH
    obtain ⟨a₁, hS₁⟩ := S₁.2.1
    obtain ⟨a₂, hS₂⟩ := S₂.2.1
    have hm₁ : S₁.2.2.some ∈ H n k a₁ := hS₁ ▸ S₁.2.2.some_mem
    have hm₂ : S₂.2.2.some ∈ H n k a₂ := hS₂ ▸ S₂.2.2.some_mem
    have h1 : S₁.1 = H n k S₁.2.2.some :=
      hS₁.trans (hH_eq_of_equiv n k S₁.2.2.some a₁ (hH_equiv n k a₁ S₁.2.2.some hm₁)).symm
    have h2 : S₂.1 = H n k S₂.2.2.some :=
      hS₂.trans (hH_eq_of_equiv n k S₂.2.2.some a₂ (hH_equiv n k a₂ S₂.2.2.some hm₂)).symm
    have hS : S₁ = S₂ := Subtype.ext (h1.trans (hH.trans h2.symm))
    rw [hS]
  have hD'_closed : ∀ n k, ∀ A ⊆ D' n k, IsClosed A := by
    intro n k A hA
    rw [← closure_subset_iff_isClosed]
    intro z hz
    have hA_sub : A ⊆ ⋃ e ∈ A, H n k e := fun e he =>
      mem_iUnion₂.mpr ⟨e, he, hD'_self n k e (hA he)⟩
    have hzU : z ∈ ⋃ e ∈ A, H n k e :=
      (hH_union_closed n k A).closure_subset_iff.mpr hA_sub hz
    obtain ⟨e₀, he₀A, hze₀⟩ := mem_iUnion₂.mp hzU
    let A' : Set X := A \ {e₀}
    have hA'_sub : A' ⊆ ⋃ e ∈ A', H n k e := fun e he =>
      mem_iUnion₂.mpr ⟨e, he, hD'_self n k e (hA he.1)⟩
    have hz_not_U' : z ∉ ⋃ e ∈ A', H n k e := by
      intro h
      obtain ⟨e, heA', hze⟩ := mem_iUnion₂.mp h
      have heq : H n k e = H n k e₀ :=
        hH_eq_of_equiv n k e e₀ (fun C hC =>
          (hH_equiv n k e z hze C hC).symm.trans (hH_equiv n k e₀ z hze₀ C hC))
      exact heA'.2 (hD'_inj n k e (hA heA'.1) e₀ (hA he₀A) heq)
    have hz_not_cl : z ∉ closure A' := fun h =>
      hz_not_U' ((hH_union_closed n k A').closure_subset_iff.mpr hA'_sub h)
    have hA_split : A ⊆ A' ∪ {e₀} := fun e he => by
      by_cases h : e = e₀
      · exact Or.inr h
      · exact Or.inl ⟨he, h⟩
    have hz_in : z ∈ closure A' ∪ closure ({e₀} : Set X) := by
      rw [← closure_union]
      exact closure_mono hA_split hz
    rcases hz_in with h | h
    · exact (hz_not_cl h).elim
    · rw [isClosed_singleton.closure_eq, mem_singleton_iff] at h
      exact h ▸ he₀A
  -- Reindex ℕ × ℕ by ℕ via Nat.unpair
  refine ⟨fun m => D' (Nat.unpair m).1 (Nat.unpair m).2, ?_, ?_⟩
  · intro m A hA
    exact hD'_closed (Nat.unpair m).1 (Nat.unpair m).2 A hA
  · rw [dense_iff_inter_open]
    intro U hU ⟨y, hyU⟩
    obtain ⟨K, hK_nhds, hK_closed, hKU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hyU)
    obtain ⟨V, hVK, hV_open, hyV⟩ := mem_nhds_iff.mp hK_nhds
    have hV_cl : closure V ⊆ U := (hK_closed.closure_subset_iff.mpr hVK).trans hKU
    obtain ⟨B, hB𝓑, hyB, hBV⟩ := h𝓑_basis.exists_subset_of_mem_open hyV hV_open
    rw [h𝓑_eq, mem_iUnion] at hB𝓑
    obtain ⟨n, hBn⟩ := hB𝓑
    obtain ⟨k, hyF⟩ := hF_cover (W n y) (hW_open n y) y (hW_mem n y)
    have hyH : y ∈ H n k y := ⟨hM_mem n y, hyF⟩
    let S : P n k := ⟨H n k y, ⟨y, rfl⟩, ⟨y, hyH⟩⟩
    let d : X := S.2.2.some
    have hd_mem : d ∈ H n k y := S.2.2.some_mem
    have hdU : d ∈ U := by
      have hC_mem : closure B ∈ 𝓒 n := ⟨B, hBn, rfl⟩
      have hdC : d ∈ closure B := hd_mem.1 (closure B) ⟨hC_mem, subset_closure hyB⟩
      exact hV_cl (closure_mono hBV hdC)
    have hdD : d ∈ ⋃ m, D' (Nat.unpair m).1 (Nat.unpair m).2 := by
      refine mem_iUnion.mpr ⟨Nat.pair n k, ?_⟩
      rw [Nat.unpair_pair]
      exact ⟨S, rfl⟩
    exact ⟨d, hdU, hdD⟩

end Proofs.L_0026
