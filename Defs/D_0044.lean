import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0033

namespace Defs.D_0044

/-!
稠密性（Chen–Wang Definition B.1 の宣言された閉包）の証明の部品 1:
**近い slab の箱は z の箱近傍に入る**。

z と座標 0 だけが異なり、s′0 ∈ (z 0, child(z 0)(lvl ℓ z)) となる点 s′ について、
lvl (m+1) s′ が lvl ℓ z 以上で、座標 m+1..ℓ−1 の z の値が Q*_{lvl (m+1) s′} に入り、
hidx が十分大きければ、g(m+1, s′) ⊆ g(ℓ, z)（`close_box_sub`）。
s′0 を z 0 の深い子孫に取れば hidx (m+1) s′ ≥ q⁻¹(s′0) は任意に大きくなるので、これらの条件は満たせる。

* `ibase_eq_of_QStar` : r ∈ Q*_a なら r を含む I_a 区間の左端は r 自身。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

theorem ibase_eq_of_QStar {a : ℕ} (ha : 0 < a) {r : α} (hr : T.QStar a r) : ibase T a r = r := by
  obtain ⟨h1, h2⟩ := ibase_spec T ha r
  exact (prop_2_2_1 T ha r).unique ⟨h1, h2⟩ ⟨hr, le_rfl, T.lt_child _ _ (T.C_child r a ha)⟩

theorem close_box_sub (hc : Compat2 q T) {m ℓ : ℕ} (hmℓ : m + 1 ≤ ℓ) {z s' : ℕ → α}
    (h0 : ∀ k, k ≠ 0 → s' k = z k) (hlt : z 0 < s' 0)
    (hlt2 : s' 0 < T.child (z 0) (lvl q ℓ z))
    (hQ : ∀ k, m + 1 ≤ k → k < ℓ → T.QStar (lvl q (m + 1) s') (z k))
    (hlv : lvl q ℓ z ≤ lvl q (m + 1) s')
    (hN : ℓ + hidx q ℓ z ≤ m + 1 + hidx q (m + 1) s') :
    gfun q T (m + 1) s' ⊆ gfun q T ℓ z := by
  have ha := lvl_pos q (m + 1) s'
  have hb := lvl_pos q ℓ z
  rintro y ⟨hy1, hy2⟩
  refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · by_cases hk0 : k = 0
    · subst hk0
      have := (prop_3_2_1' hc hb hlt hlt2).2.2 (lvl q (m + 1) s') ha (hy1 0 (by omega))
      exact ⟨le_of_lt this.1, this.2⟩
    · by_cases hkm : k < m + 1
      · have h := hy1 k hkm
        rw [h0 k hk0] at h
        exact ⟨h.1, lt_of_lt_of_le h.2 (T.child_le_child (z k) hb hlv)⟩
      · push_neg at hkm
        have h := hy2 k hkm (by omega)
        rw [h0 k hk0] at h
        unfold ival at h
        rw [ibase_eq_of_QStar ha (hQ k hkm hk)] at h
        exact ⟨h.1, lt_of_lt_of_le h.2 (T.child_le_child (z k) hb hlv)⟩
  · have hk0 : k ≠ 0 := by omega
    have h := hy2 k (by omega) (by omega)
    rw [h0 k hk0] at h
    exact ival_mono T hb hlv (z k) h

end Defs.D_0044
