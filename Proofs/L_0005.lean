import Mathlib.SetTheory.Cardinal.Order
import Specs.L_0005
import Proofs.L_0006

namespace Proofs.L_0005

open MSpace Set Topology

theorem main : Specs.L_0005.stmt := by
  unfold Specs.L_0005.stmt MSpace.Goals.T2b_stratifiable_paracompact
  intro X _ hX
  haveI : NormalSpace X := (Proofs.L_0006.main X hX).1
  obtain ⟨_, G, hGopen, hGsub, hGint, hGmono⟩ := hX
  -- 単調減少な stratification を構成
  let G' : ℕ → Set X → Set X := fun n H => ⋂ k ∈ Finset.range (n + 1), G k H
  have hG'open : ∀ n H, IsClosed H → IsOpen (G' n H) := fun n H hH =>
    isOpen_biInter_finset fun k _ => hGopen k H hH
  have hG'le : ∀ n H, G' n H ⊆ G n H := fun n H =>
    biInter_subset_of_mem (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hG'anti : ∀ n m H, n ≤ m → G' m H ⊆ G' n H := by
    intro n m H hnm x hx
    simp only [G', mem_iInter, Finset.mem_range] at hx ⊢
    intro k hk
    exact hx k (by omega)
  have hG'sub : ∀ n H, IsClosed H → H ⊆ G' n H := by
    intro n H hH x hx
    simp only [G', mem_iInter]
    intro k _
    exact hGsub k H hH hx
  have hG'int : ∀ H, IsClosed H → ⋂ n, closure (G' n H) = H := by
    intro H hH
    apply Subset.antisymm
    · calc ⋂ n, closure (G' n H)
          ⊆ ⋂ n, closure (G n H) := iInter_mono fun n => closure_mono (hG'le n H)
        _ = H := hGint H hH
    · exact subset_iInter fun n => (hG'sub n H hH).trans subset_closure
  have hG'mono : ∀ n H K, IsClosed H → IsClosed K → H ⊆ K → G' n H ⊆ G' n K := by
    intro n H K hH hK hHK x hx
    simp only [G', mem_iInter] at hx ⊢
    intro k hk
    exact hGmono k H K hH hK hHK (hx k hk)
  -- 開集合に対する単調な閉部分集合列 F n U
  let F : ℕ → Set X → Set X := fun n U => (G' n Uᶜ)ᶜ
  have hFclosed : ∀ n U, IsOpen U → IsClosed (F n U) := fun n U hU =>
    (hG'open n Uᶜ hU.isClosed_compl).isClosed_compl
  have hFsub : ∀ n U, IsOpen U → F n U ⊆ U := by
    intro n U hU x hx
    by_contra hxu
    exact hx (hG'sub n Uᶜ hU.isClosed_compl hxu)
  have hFmono : ∀ n U V, IsOpen U → IsOpen V → U ⊆ V → F n U ⊆ F n V := fun n U V hU hV hUV =>
    compl_subset_compl.2
      (hG'mono n Vᶜ Uᶜ hV.isClosed_compl hU.isClosed_compl (compl_subset_compl.2 hUV))
  have hFcov : ∀ U, IsOpen U → ∀ x ∈ U, ∃ n, x ∈ F n U := by
    intro U hU x hx
    have hx' : x ∉ ⋂ n, closure (G' n Uᶜ) := by
      rw [hG'int Uᶜ hU.isClosed_compl]
      exact fun h => h hx
    rw [mem_iInter] at hx'
    obtain ⟨n, hn⟩ := not_forall.1 hx'
    exact ⟨n, fun h => hn (subset_closure h)⟩
  -- パラコンパクト性の証明
  refine ⟨fun α s ho hcov => ?_⟩
  obtain ⟨lin, wf⟩ := exists_wellFoundedLT α
  letI : LinearOrder α := lin
  haveI : WellFoundedLT α := wf
  have hcov' : ∀ x : X, (setOf fun a : α => x ∈ s a).Nonempty :=
    fun x => iUnion_eq_univ_iff.1 hcov x
  let ind (x : X) : α := wellFounded_lt.min {a : α | x ∈ s a} (hcov' x)
  have mem_ind (x : X) : x ∈ s (ind x) :=
    wellFounded_lt.min_mem {a : α | x ∈ s a} (hcov' x)
  have notMem_of_lt_ind {x : X} {a : α} (hlt : a < ind x) : x ∉ s a :=
    fun hx => wellFounded_lt.not_lt_min {a : α | x ∈ s a} hx hlt
  -- ステップ 1: σ-離散な閉細分 C n a を構成
  let Wlt (a : α) : Set X := ⋃ (b : α) (_ : b < a), s b
  have hWlt_open (a : α) : IsOpen (Wlt a) :=
    isOpen_iUnion fun b => isOpen_iUnion fun _ => ho b
  let C (n : ℕ) (a : α) : Set X := F n (s a) \ Wlt a
  have hC_closed (n : ℕ) (a : α) : IsClosed (C n a) :=
    (hFclosed n (s a) (ho a)).sdiff (hWlt_open a)
  have hC_sub (n : ℕ) (a : α) : C n a ⊆ s a :=
    diff_subset.trans (hFsub n (s a) (ho a))
  have hC_cov (x : X) : ∃ n a, x ∈ C n a := by
    obtain ⟨n, hn⟩ := hFcov (s (ind x)) (ho (ind x)) x (mem_ind x)
    refine ⟨n, ind x, hn, ?_⟩
    simp only [Wlt, mem_iUnion, not_exists]
    exact fun b hlt => notMem_of_lt_ind hlt
  have hC_disj (n : ℕ) {a b : α} (hab : a ≠ b) : Disjoint (C n a) (C n b) := by
    rw [Set.disjoint_left]
    intro x hxa hxb
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact hxb.2 (mem_iUnion₂.2 ⟨a, hlt, hC_sub n a hxa⟩)
    · exact hxa.2 (mem_iUnion₂.2 ⟨b, hgt, hC_sub n b hxb⟩)
  have hC_lf (n : ℕ) : LocallyFinite (C n) := by
    intro x
    let N : Set X := s (ind x) \ F n (Wlt (ind x))
    have hN_open : IsOpen N :=
      (ho (ind x)).sdiff (hFclosed n (Wlt (ind x)) (hWlt_open (ind x)))
    have hxN : x ∈ N := by
      refine ⟨mem_ind x, fun h => ?_⟩
      have hW := hFsub n (Wlt (ind x)) (hWlt_open (ind x)) h
      simp only [Wlt, mem_iUnion] at hW
      obtain ⟨b, hlt, hxb⟩ := hW
      exact notMem_of_lt_ind hlt hxb
    refine ⟨N, hN_open.mem_nhds hxN, (Set.finite_singleton (ind x)).subset ?_⟩
    intro a ha
    rw [mem_singleton_iff]
    by_contra hne
    obtain ⟨y, hyC, hyN⟩ := ha
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsub : s a ⊆ Wlt (ind x) := fun z hz => mem_iUnion₂.2 ⟨a, hlt, hz⟩
      exact hyN.2 (hFmono n (s a) (Wlt (ind x)) (ho a) (hWlt_open (ind x)) hsub hyC.1)
    · exact hyC.2 (mem_iUnion₂.2 ⟨ind x, hgt, hyN.1⟩)
  -- ステップ 2: 各 n の離散閉族 C n を離散開族 W n へ膨らませる
  let K (n : ℕ) (a : α) : Set X := ⋃ (b : α) (_ : b ≠ a), C n b
  have hK_closed (n : ℕ) (a : α) : IsClosed (K n a) := by
    have hEq : K n a = ⋃ b : {b : α // b ≠ a}, C n b.1 := by
      ext y
      simp [K]
    rw [hEq]
    exact ((hC_lf n).comp_injective Subtype.val_injective).isClosed_iUnion fun b => hC_closed n b.1
  let H (n : ℕ) (a : α) : Set X := K n a ∪ (s a)ᶜ
  have hH_closed (n : ℕ) (a : α) : IsClosed (H n a) :=
    (hK_closed n a).union (ho a).isClosed_compl
  let D (n : ℕ) (a : α) : Set X := ⋃ k, (G' k (C n a) \ closure (G' k (H n a)))
  have hD_open (n : ℕ) (a : α) : IsOpen (D n a) :=
    isOpen_iUnion fun k => (hG'open k (C n a) (hC_closed n a)).sdiff isClosed_closure
  have hC_sub_D (n : ℕ) (a : α) : C n a ⊆ D n a := by
    intro x hx
    have hxH : x ∉ H n a := by
      rintro (hxK | hxs)
      · simp only [K, mem_iUnion] at hxK
        obtain ⟨b, hba, hxb⟩ := hxK
        exact Set.disjoint_left.1 (hC_disj n hba.symm) hx hxb
      · exact hxs (hC_sub n a hx)
    have hx' : x ∉ ⋂ k, closure (G' k (H n a)) := by
      rw [hG'int (H n a) (hH_closed n a)]
      exact hxH
    rw [mem_iInter] at hx'
    obtain ⟨k, hk⟩ := not_forall.1 hx'
    exact mem_iUnion.2 ⟨k, hG'sub k (C n a) (hC_closed n a) hx, hk⟩
  have hD_sub_s (n : ℕ) (a : α) : D n a ⊆ s a := by
    intro x hx
    obtain ⟨k, _, hnk⟩ := mem_iUnion.1 hx
    by_contra hxs
    exact hnk (subset_closure (hG'sub k (H n a) (hH_closed n a) (Or.inr hxs)))
  have hD_disj (n : ℕ) {a b : α} (hab : a ≠ b) : Disjoint (D n a) (D n b) := by
    rw [Set.disjoint_left]
    intro x hxa hxb
    obtain ⟨k, hka, hnka⟩ := mem_iUnion.1 hxa
    obtain ⟨l, hlb, hnlb⟩ := mem_iUnion.1 hxb
    rcases le_total k l with hkl | hlk
    · have hCbH : C n b ⊆ H n a := fun y hy => Or.inl (mem_iUnion₂.2 ⟨b, hab.symm, hy⟩)
      exact hnka (subset_closure
        (hG'mono k (C n b) (H n a) (hC_closed n b) (hH_closed n a) hCbH
          (hG'anti k l (C n b) hkl hlb)))
    · have hCaH : C n a ⊆ H n b := fun y hy => Or.inl (mem_iUnion₂.2 ⟨a, hab, hy⟩)
      exact hnlb (subset_closure
        (hG'mono l (C n a) (H n b) (hC_closed n a) (hH_closed n b) hCaH
          (hG'anti l k (C n a) hlk hka)))
  have hCn_closed (n : ℕ) : IsClosed (⋃ a, C n a) :=
    (hC_lf n).isClosed_iUnion (hC_closed n)
  have hDn_open (n : ℕ) : IsOpen (⋃ a, D n a) :=
    isOpen_iUnion (hD_open n)
  have hWQ : ∀ n : ℕ, ∃ (Wn Qn : Set X),
      IsOpen Wn ∧ IsOpen Qn ∧ (⋃ a, C n a) ⊆ Qn ∧
      closure Qn ⊆ Wn ∧ closure Wn ⊆ (⋃ a, D n a) := by
    intro n
    obtain ⟨Wn, hWn_open, hCn_sub_Wn, hclWn_sub_Dn⟩ :=
      normal_exists_closure_subset (hCn_closed n) (hDn_open n) (iUnion_mono (hC_sub_D n))
    obtain ⟨Qn, hQn_open, hCn_sub_Qn, hclQn_sub_Wn⟩ :=
      normal_exists_closure_subset (hCn_closed n) hWn_open hCn_sub_Wn
    exact ⟨Wn, Qn, hWn_open, hQn_open, hCn_sub_Qn, hclQn_sub_Wn, hclWn_sub_Dn⟩
  choose Wn Qn hWn_open hQn_open hCn_sub_Qn hclQn_sub_Wn hclWn_sub_Dn using hWQ
  let W (n : ℕ) (a : α) : Set X := D n a ∩ Wn n
  have hW_open (n : ℕ) (a : α) : IsOpen (W n a) := (hD_open n a).inter (hWn_open n)
  have hW_sub_s (n : ℕ) (a : α) : W n a ⊆ s a := inter_subset_left.trans (hD_sub_s n a)
  have hW_union (n : ℕ) : (⋃ a, W n a) = Wn n := by
    rw [← iUnion_inter]
    exact inter_eq_right.2 (subset_closure.trans (hclWn_sub_Dn n))
  have hW_lf (n : ℕ) : LocallyFinite (W n) := by
    intro x
    by_cases hxD : x ∈ ⋃ a, D n a
    · obtain ⟨a0, ha0⟩ := mem_iUnion.1 hxD
      refine ⟨D n a0, (hD_open n a0).mem_nhds ha0, (Set.finite_singleton a0).subset ?_⟩
      intro a ha
      rw [mem_singleton_iff]
      by_contra hne
      obtain ⟨y, ⟨hyDa, _⟩, hyDa0⟩ := ha
      exact Set.disjoint_left.1 (hD_disj n hne) hyDa hyDa0
    · have hxn : x ∈ (closure (Wn n))ᶜ := fun h => hxD (hclWn_sub_Dn n h)
      refine ⟨(closure (Wn n))ᶜ, isClosed_closure.isOpen_compl.mem_nhds hxn,
        Set.finite_empty.subset ?_⟩
      intro a ⟨y, ⟨_, hyW⟩, hyn⟩
      exact hyn (subset_closure hyW)
  -- ステップ 3: σ-離散開族 W n a から局所有限な開細分 T を構成
  let A (n : ℕ) : Set X := Wn n \ ⋃ j ∈ Finset.range n, closure (Qn j)
  have hA_open (n : ℕ) : IsOpen (A n) :=
    (hWn_open n).sdiff (isClosed_biUnion_finset fun _ _ => isClosed_closure)
  let T (p : ℕ × α) : Set X := A p.1 ∩ W p.1 p.2
  refine ⟨ℕ × α, T, fun p => (hA_open p.1).inter (hW_open p.1 p.2), ?_, ?_,
    fun p => ⟨p.2, inter_subset_right.trans (hW_sub_s p.1 p.2)⟩⟩
  · -- 被覆性
    refine eq_univ_of_forall fun x => ?_
    have hex : ∃ n, x ∈ closure (Qn n) := by
      obtain ⟨n, a, hxa⟩ := hC_cov x
      exact ⟨n, subset_closure (hCn_sub_Qn n (mem_iUnion.2 ⟨a, hxa⟩))⟩
    classical
    let n0 := Nat.find hex
    have hn0 : x ∈ closure (Qn n0) := Nat.find_spec hex
    have hxA : x ∈ A n0 := by
      refine ⟨hclQn_sub_Wn n0 hn0, fun h => ?_⟩
      simp only [mem_iUnion, Finset.mem_range] at h
      obtain ⟨j, hj, hxj⟩ := h
      exact Nat.find_min hex hj hxj
    have hxW : x ∈ ⋃ a, W n0 a := by
      rw [hW_union n0]
      exact hxA.1
    obtain ⟨a, ha⟩ := mem_iUnion.1 hxW
    exact mem_iUnion.2 ⟨(n0, a), hxA, ha⟩
  · -- 局所有限性
    intro x
    obtain ⟨n1, a1, hxC⟩ := hC_cov x
    have hxQ : x ∈ Qn n1 := hCn_sub_Qn n1 (mem_iUnion.2 ⟨a1, hxC⟩)
    have hN : ∀ n : ℕ, ∃ U ∈ 𝓝 x, {a : α | (W n a ∩ U).Nonempty}.Finite := fun n => hW_lf n x
    choose U hU_nhds hU_fin using hN
    let N : Set X := Qn n1 ∩ ⋂ n ∈ Finset.range (n1 + 1), U n
    have hN_nhds : N ∈ 𝓝 x :=
      Filter.inter_mem ((hQn_open n1).mem_nhds hxQ)
        ((Filter.biInter_finset_mem _).2 fun n _ => hU_nhds n)
    refine ⟨N, hN_nhds, ?_⟩
    have hfin : (⋃ n ∈ Finset.range (n1 + 1),
        ({n} : Set ℕ) ×ˢ {a : α | (W n a ∩ U n).Nonempty}).Finite :=
      (Finset.finite_toSet (Finset.range (n1 + 1))).biUnion fun n _ =>
        (Set.finite_singleton n).prod (hU_fin n)
    refine hfin.subset ?_
    rintro ⟨n, a⟩ ⟨y, ⟨hyA, hyW⟩, hyQ, hyU⟩
    have hn_le : n ≤ n1 := by
      by_contra hlt
      exact hyA.2 (mem_iUnion₂.2 ⟨n1, Finset.mem_range.2 (Nat.lt_of_not_ge hlt), subset_closure hyQ⟩)
    have hn_mem : n ∈ Finset.range (n1 + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hn_le)
    refine mem_iUnion₂.2 ⟨n, hn_mem, rfl, y, hyW, ?_⟩
    exact (mem_iInter₂.1 hyU) n hn_mem

end Proofs.L_0005
