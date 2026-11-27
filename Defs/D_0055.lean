import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card

namespace Defs.D_0055

/-!
自由集合の選択補題（Chen–Wang Prop 9.5 の補修 2、報告 §2 項目 7）。

単射な列 `s : ℕ → β` と、各点に高々 `n'` 個の点を割り当てる `F : β → Finset β`（有限位数の set mapping）
があれば、狭義単調な `φ` で、`i ≠ j` のとき `s (φ i) ∉ F (s (φ j))` となるものがある。

証明: `n'+1` 個の候補のうち、無限個の点から指されない候補が 1 つある（鳩の巣）。その候補を取り、
残りの「貯水池」を無限集合のまま保って再帰する。
-/

theorem free_step {β : Type*} {s : ℕ → β} (hs : Function.Injective s) {F : β → Finset β}
    {n' : ℕ} (hF : ∀ b, (F b).card ≤ n') (S : Set ℕ) (hS : S.Infinite) :
    ∃ a ∈ S, ∃ S' ⊆ S, S'.Infinite ∧ ∀ b ∈ S', a < b ∧ s a ∉ F (s b) ∧ s b ∉ F (s a) := by
  obtain ⟨C, hCS, hCcard⟩ := hS.exists_subset_card_eq (n' + 1)
  have key : ∀ b, ∃ c ∈ C, s c ∉ F (s b) := by
    intro b
    by_contra h
    push Not at h
    have h1 : C.card ≤ (F (s b)).card :=
      Finset.card_le_card_of_injOn s (fun c hc => h c hc) hs.injOn
    have h2 := hF (s b)
    omega
  obtain ⟨c, hc, hinf⟩ : ∃ c ∈ C, (S ∩ {b | s c ∉ F (s b)}).Infinite := by
    by_contra h
    push Not at h
    apply hS
    have hfin : (⋃ c ∈ C, S ∩ {b | s c ∉ F (s b)}).Finite :=
      Set.Finite.biUnion C.finite_toSet (fun c hc => h c hc)
    refine hfin.subset ?_
    intro b hb
    obtain ⟨c, hc, h⟩ := key b
    exact Set.mem_biUnion hc ⟨hb, h⟩
  have hfin1 : {b | s b ∈ F (s c)}.Finite := (F (s c)).finite_toSet.preimage hs.injOn
  have hfin2 : (Set.Iic c).Finite := Set.finite_Iic c
  refine ⟨c, hCS hc, (S ∩ {b | s c ∉ F (s b)}) \ ({b | s b ∈ F (s c)} ∪ Set.Iic c),
    fun b hb => hb.1.1, hinf.sdiff (hfin1.union hfin2), fun b hb => ?_⟩
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic,
    not_or] at hb
  exact ⟨not_le.mp hb.2.2, hb.1.2, hb.2.1⟩

/-- 自由集合の選択補題。 -/
theorem free_subseq {β : Type*} {s : ℕ → β} (hs : Function.Injective s) {F : β → Finset β}
    {n' : ℕ} (hF : ∀ b, (F b).card ≤ n') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i j, i ≠ j → s (φ i) ∉ F (s (φ j)) := by
  have step : ∀ S : {S : Set ℕ // S.Infinite}, ∃ a : ℕ, ∃ S' : {S : Set ℕ // S.Infinite},
      a ∈ S.1 ∧ S'.1 ⊆ S.1 ∧ ∀ b ∈ S'.1, a < b ∧ s a ∉ F (s b) ∧ s b ∉ F (s a) := by
    rintro ⟨S, hS⟩
    obtain ⟨a, ha, S', hS'S, hS'inf, h⟩ := free_step hs hF S hS
    exact ⟨a, ⟨S', hS'inf⟩, ha, hS'S, h⟩
  choose A N hA hN hAN using step
  let T : ℕ → {S : Set ℕ // S.Infinite} := fun k => N^[k] ⟨Set.univ, Set.infinite_univ⟩
  have hT : ∀ k, T (k + 1) = N (T k) := fun k => Function.iterate_succ_apply' N k _
  have hanti : ∀ i j, i ≤ j → (T j).1 ⊆ (T i).1 := by
    intro i j hij
    induction hij with
    | refl => exact Set.Subset.rfl
    | step _ ih => rw [hT]; exact (hN _).trans ih
  have key : ∀ i j, i < j → A (T i) < A (T j) ∧ s (A (T i)) ∉ F (s (A (T j))) ∧
      s (A (T j)) ∉ F (s (A (T i))) := by
    intro i j hij
    have hmem : A (T j) ∈ (T (i + 1)).1 := hanti (i + 1) j hij (hA _)
    rw [hT] at hmem
    exact hAN _ _ hmem
  refine ⟨fun k => A (T k), fun i j hij => (key i j hij).1, fun i j hij => ?_⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact (key i j h).2.1
  · exact (key j i h).2.2

end Defs.D_0055
