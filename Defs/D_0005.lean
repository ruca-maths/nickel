import Mathlib.Order.Interval.Set.Basic
import Mathlib.Logic.Relation
import Defs.D_0003

namespace Defs.D_0005

/-!
Chen–Wang (arXiv 1809.03763v2) Proposition 2.2.3 と 2.2.5（`Defs.D_0003.Tree2` の上で）。

* 2.2.5: `p ∈ Q*_a`, `h ∈ Q*_b`, `1 ≤ a ≤ b` なら `[p, p_a)` と `[h, h_b)` は
  交わらないか `[h, h_b) ⊆ [p, p_a)`。論文は `b > a` とするが `a ≤ b` で成り立つ
  （`a = b` のときは 2.2.1 の互いに素から等号）。
* 2.2.3: `1 ≤ a ≤ b`, `p ∈ Q*_a` なら
  `⋃ {[h, h_b) : h ∈ Q*_b, [h, h_b) ⊆ [p, p_a)} = [p, p_a)`（点ごとの ↔ の形で述べる）。
  後半の `Q*_b ∩ (h, h_b) = ∅` は `Defs.D_0003.Tree2.not_mem_gap`。

論文の 2.2.3 の証明は「`(q_h, q_hb) ∩ Q*_b = ∅` なので `q_i, q_ia ∉ (q_h, q_hb)`、よって
`[q_h, q_hb) ⊆ [q_i, q_ia)`」であり、ここでもその通りに示せる（`q_ia ∈ Q*_b` に `a ≤ b` を使う）。
-/

open Defs.D_0003 Defs.D_0003.Tree2

variable {α : Type} [LinearOrder α]

/-- `p ∈ Q*_a`（a ≥ 1）なら `p_a ∈ Q*_b`（a ≤ b）。 -/
theorem child_mem_QStar (T : Tree2 α) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) {p : α}
    (hp : T.QStar a p) : T.QStar b (T.child p a) :=
  QStar.step p _ (prop_2_2_2 T hab hp) (T.C_child p a ha) (by rw [T.idx_child]; exact hab)

/-- Proposition 2.2.5（`a ≤ b` 版）。 -/
theorem prop_2_2_5 (T : Tree2 α) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) {p h : α}
    (hp : T.QStar a p) (hh : T.QStar b h) :
    Disjoint (Set.Ico p (T.child p a)) (Set.Ico h (T.child h b)) ∨
      Set.Ico h (T.child h b) ⊆ Set.Ico p (T.child p a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  by_cases hd : Disjoint (Set.Ico p (T.child p a)) (Set.Ico h (T.child h b))
  · exact Or.inl hd
  · right
    obtain ⟨x, hx, hx'⟩ := Set.not_disjoint_iff.mp hd
    have hpb : T.QStar b p := prop_2_2_2 T hab hp
    have hpab : T.QStar b (T.child p a) := child_mem_QStar T ha hab hp
    have h1 : p ≤ h := by
      by_contra hc
      exact not_mem_gap T hb hpb h ⟨not_le.mp hc, lt_of_le_of_lt hx.1 hx'.2⟩
    have h2 : T.child h b ≤ T.child p a := by
      by_contra hc
      exact not_mem_gap T hb hpab h ⟨lt_of_le_of_lt hx'.1 hx.2, not_le.mp hc⟩
    exact Set.Ico_subset_Ico h1 h2

/-- Proposition 2.2.3（`a ≤ b` 版）: `[p, p_a)` は、それに含まれる `I_b` の元で覆われる。 -/
theorem prop_2_2_3 (T : Tree2 α) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) {p : α}
    (hp : T.QStar a p) :
    ∀ x, x ∈ Set.Ico p (T.child p a) ↔
      ∃ h, T.QStar b h ∧ Set.Ico h (T.child h b) ⊆ Set.Ico p (T.child p a) ∧
        x ∈ Set.Ico h (T.child h b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  intro x
  constructor
  · intro hx
    obtain ⟨h, hh, hxh⟩ := prop_2_2_1_cover T hb x
    rcases prop_2_2_5 T ha hab hp hh with hd | hsub
    · exact absurd hxh (Set.disjoint_left.mp hd hx)
    · exact ⟨h, hh, hsub, hxh⟩
  · rintro ⟨h, _, hsub, hxh⟩
    exact hsub hxh

end Defs.D_0005
