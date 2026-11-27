import Targets

namespace ChildResearch.ClosureNetworkExpansion

open MSpace Set TopologicalSpace Topology

def HasCPClosureNetwork {X : Type} [TopologicalSpace X] (p : X) : Prop :=
  ∃ V : Set (Set X),
    (∀ W ∈ V, IsOpen W ∧ p ∈ closure W) ∧
    (∀ U : Set X, IsOpen U → p ∈ U → ∃ W ∈ V, W ⊆ U) ∧
    ClosurePreserving V

/-- Adapted from the Ito expansion proof on the Nickel research branch
`research/L0028-sublemmas`. A selected piece only needs to capture its
representative in closure. -/
theorem closed_cp_outer_base_of_closure_networks
    (X : Type) [TopologicalSpace X]
    (G : ℕ → Set X → Set X) (hG : MSpace.IsStratification G)
    (hG_dec : ∀ n H, IsClosed H → G (n + 1) H ⊆ G n H)
    (F : Set X)
    (𝓚 : Set (Set X))
    (h𝓚_nhd : ∀ K ∈ 𝓚, IsClosed K ∧ F ⊆ interior K)
    (h𝓚_base : ∀ U : Set X, IsOpen U → F ⊆ U → ∃ K ∈ 𝓚, K ⊆ U)
    (h𝓚_cp : MSpace.ClosurePreserving 𝓚)
    (E : ℕ → Set X)
    (O : (k : ℕ) → ↥(E k) → Set X)
    (hO_open : ∀ k (p : ↥(E k)), IsOpen (O k p) ∧ (p : X) ∈ O k p)
    (hO_disc : ∀ k y, ∃ N : Set X, IsOpen N ∧ y ∈ N ∧
      ∀ p q : ↥(E k), (N ∩ closure (O k p)).Nonempty →
        (N ∩ closure (O k q)).Nonempty → p = q)
    (hE_cp : ∀ k, ∀ p ∈ E k, HasCPClosureNetwork p)
    (hK_trace : ∀ K ∈ 𝓚, K ⊆ closure (interior K ∪ (K ∩ ⋃ k, E k))) :
    ∃ 𝓥 : Set (Set X),
      (∀ V ∈ 𝓥, IsOpen V ∧ F ⊆ V) ∧
      (∀ U : Set X, IsOpen U → F ⊆ U → ∃ V ∈ 𝓥, V ⊆ U) ∧
      MSpace.ClosurePreserving 𝓥 := by
  classical
  have hG_anti : ∀ {m n : ℕ} {H : Set X}, IsClosed H → m ≤ n → G n H ⊆ G m H := by
    intro m n H hH hmn
    induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact (hG_dec _ H hH).trans ih
  have hcp_sub : ∀ (k : ℕ) (p : ↥(E k)), HasCPClosureNetwork (p : X) :=
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
      (p : X) ∈ closure (V P k p) := by
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
    refine (hK_trace P.1.1 P.2.1).trans
      (closure_minimal ?_ isClosed_closure)
    intro z hz
    rcases hz with hz_int | ⟨hzK, hzE⟩
    · exact subset_closure (Or.inl hz_int)
    · obtain ⟨k, hzk⟩ := mem_iUnion.mp hzE
      exact closure_mono
        (fun w hw => Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨z, hzk⟩, hw⟩⟩))
        (hV_has_p P k ⟨z, hzk⟩ hzK)
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

end ChildResearch.ClosureNetworkExpansion
