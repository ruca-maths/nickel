import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.Order.Interval.Set.Infinite
import Defs.D_0044

namespace Defs.D_0045

/-!
稠密性の部品 1 の続き: `Defs.D_0044.close_box_sub` の仮定を満たす点 s′ は常に取れる
（`close_point_exists`）。s′ は z と座標 0 だけ異なり、s′0 は (z 0, child(z 0)(lvl ℓ z)) の中で
q-番号が任意の B 以上の点。そのとき g(m+1, s′) ⊆ g(ℓ, z)。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0044

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

theorem finite_small_index (B : ℕ) : {v : α | q.symm v < B}.Finite := by
  have : {v : α | q.symm v < B} = q '' {k | k < B} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h; exact ⟨q.symm v, h, q.apply_symm_apply v⟩
    · rintro ⟨k, hk, rfl⟩; rwa [q.symm_apply_apply]
  rw [this]; exact (Set.finite_lt_nat B).image _

theorem close_point_exists [DenselyOrdered α] (hc : Compat2 q T) {m ℓ : ℕ} (hm : 0 < m)
    (hmℓ : m + 1 ≤ ℓ) (z : ℕ → α) (B : ℕ) :
    ∃ s' : ℕ → α, (∀ k, k ≠ 0 → s' k = z k) ∧ z 0 < s' 0 ∧
      s' 0 < T.child (z 0) (lvl q ℓ z) ∧ B ≤ q.symm (s' 0) ∧
      gfun q T (m + 1) s' ⊆ gfun q T ℓ z := by
  have hQ : ∀ k : ℕ, ∃ c, T.QStar c (z k) := fun k => prop_2_2_4 T (z k)
  choose C hC using hQ
  set B' := B + lvl q ℓ z + ℓ + hidx q ℓ z + (Finset.range ℓ).sup C
  have hint : z 0 < T.child (z 0) (lvl q ℓ z) := T.lt_child _ _ (T.C_child _ _ (lvl_pos q ℓ z))
  obtain ⟨v, hv, hvB⟩ :=
    ((Set.Ioo_infinite hint).diff (finite_small_index (q := q) B')).nonempty
  simp only [Set.mem_setOf_eq, not_lt] at hvB
  set s' := Function.update z 0 v
  have h0 : ∀ k, k ≠ 0 → s' k = z k := fun k hk => Function.update_of_ne hk v z
  have hs0 : s' 0 = v := Function.update_self 0 v z
  have hcode : q.symm v ≤ hidx q (m + 1) s' := by
    have := code_ge (m + 1) (fun k => q.symm (s' k)) 0 (by omega)
    show q.symm v ≤ code (m + 1) (fun k => q.symm (s' k))
    simpa [hs0] using this
  refine ⟨s', h0, hs0 ▸ hv.1, hs0 ▸ hv.2, by rw [hs0]; omega, ?_⟩
  refine close_box_sub hc hmℓ h0 (hs0 ▸ hv.1) (hs0 ▸ hv.2) ?_ ?_ ?_
  · intro k _ hk
    have hle : C k ≤ (Finset.range ℓ).sup C := Finset.le_sup (f := C) (Finset.mem_range.mpr hk)
    exact prop_2_2_2 T (by unfold lvl; omega) (hC k)
  · unfold lvl; omega
  · omega

end Defs.D_0045
