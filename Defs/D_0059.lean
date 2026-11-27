import Defs.D_0055

namespace Defs.D_0059

/-!
自由集合の選択補題の集合版（Chen–Wang Prop 9.5 の補修 2 を適用する形）。

`free_subset` : 無限集合 S ⊆ β と、各点に高々 n′ 個の点を割り当てる F : β → Finset β があれば、
無限部分集合 T ⊆ S で、T の相異なる 2 点 x, y について x ∉ F y となるものがある。
Prop 9.5 では β = 𝒜（mad family）、F(β) = β⁻（|β⁻| = n′）として使い、先に選んだ α_{h′} が
α_h⁻ に入らないように α_h を選ぶ（検証報告 §2 項目 7）。
-/

open Defs.D_0055

theorem free_subset {β : Type*} {S : Set β} (hS : S.Infinite) {F : β → Finset β} {n' : ℕ}
    (hF : ∀ b, (F b).card ≤ n') :
    ∃ T ⊆ S, T.Infinite ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x ∉ F y := by
  let e := hS.natEmbedding
  let s : ℕ → β := fun n => (e n : β)
  have hs : Function.Injective s := Subtype.val_injective.comp e.injective
  obtain ⟨φ, hφ, hfree⟩ := free_subseq hs hF
  refine ⟨Set.range (s ∘ φ), ?_, Set.infinite_range_of_injective (hs.comp hφ.injective), ?_⟩
  · rintro _ ⟨n, rfl⟩; exact (e (φ n)).2
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hfree i j (fun h => hij (by rw [h]))

end Defs.D_0059
