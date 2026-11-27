import Mathlib.Order.Zorn
import Mathlib.Data.Set.Finite.Basic

namespace Defs.D_0053

/-!
Chen–Wang §9 の組合せ論の部品: **mad family の存在**（Zorn）。

* `IsAD F` : F は ℕ の無限部分集合からなり、相異なる 2 元の共通部分は有限。
* `IsMAD F` : IsAD F で極大（ℕ の無限部分集合 b がすべての元と a.d. なら b ∈ F）。
* `exists_mad_extending` : IsAD F₀ なら F₀ を含む mad family がある。
論文の Prop 9.1 は mad family が ≤*-非有界であることを使う（未証明）。非有界な a.d. 族 F₀ を
これで延長すれば非有界な mad family が得られる（非有界性は部分族から上の族に遺伝する）。
-/

/-- 概互いに素な無限部分集合の族。 -/
def IsAD (F : Set (Set ℕ)) : Prop :=
  (∀ a ∈ F, a.Infinite) ∧ F.Pairwise (fun a b => (a ∩ b).Finite)

/-- 極大な概互いに素な族。 -/
def IsMAD (F : Set (Set ℕ)) : Prop :=
  IsAD F ∧ ∀ b : Set ℕ, b.Infinite → (∀ a ∈ F, (a ∩ b).Finite) → b ∈ F

theorem exists_mad_extending {F₀ : Set (Set ℕ)} (h₀ : IsAD F₀) :
    ∃ F, F₀ ⊆ F ∧ IsMAD F := by
  obtain ⟨F, hF₀F, hmax⟩ := zorn_subset_nonempty {F | IsAD F} (fun C hC hchain _ => by
    refine ⟨⋃₀ C, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro a ⟨s, hs, ha⟩; exact (hC hs).1 a ha
    · rintro a ⟨s, hs, ha⟩ b ⟨t, ht, hb⟩ hab
      rcases hchain.total hs ht with h | h
      · exact (hC ht).2 (h ha) hb hab
      · exact (hC hs).2 ha (h hb) hab) F₀ h₀
  refine ⟨F, hF₀F, hmax.prop, fun b hb hab => ?_⟩
  by_contra hbF
  have hAD : IsAD (insert b F) := by
    refine ⟨?_, ?_⟩
    · rintro a (rfl | ha)
      · exact hb
      · exact hmax.prop.1 a ha
    · rintro x (rfl | hx) y (rfl | hy) hxy
      · exact absurd rfl hxy
      · rw [Set.inter_comm]; exact hab y hy
      · exact hab x hx
      · exact hmax.prop.2 hx hy hxy
  have := hmax.eq_of_subset hAD (Set.subset_insert b F)
  exact hbF (this ▸ Set.mem_insert b F)

end Defs.D_0053
