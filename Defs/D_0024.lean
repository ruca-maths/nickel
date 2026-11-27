import Mathlib.Logic.Equiv.Defs
import Defs.D_0013

namespace Defs.D_0024

/-!
`Defs.D_0013.Compat` の矛盾と修正。

1. `not_compat` : D_0013 の `Compat q T` は**どの** `T : Tree2 α`, `q : ℕ ≃ α` でも成り立たない。
   `idx_lt_num`（`j < q⁻¹ (p_j)`）と `child_eq` から根以外の点の Q 番号はすべて 2 以上になるが、
   `q` は全単射なので番号 0 と 1 の両方が使われ、そのうち根でない方が矛盾する。
   したがって D_0013/D_0016/D_0018/D_0019 の `Compat` 仮定付きの定理は空虚に真であり、
   そのままでは Y の構成に使えない。
2. `Compat2` : `idx_lt_num` を `idx_le_num`（`j ≤ q⁻¹ (p_j)`）に弱めた版。
   `prop_3_2_1'` は同じ結論（`a < q⁻¹ r` を含む）が Compat2 から出ることを示す。
   D_0016/D_0018/D_0019 は Compat を prop_3_2_1 と num_child/desc_of_mem/shrink を通してしか
   使っていないので、`Compat` → `Compat2`, `prop_3_2_1` → `prop_3_2_1'` の置換で移植できるはず。
-/

open Relation Defs.D_0003 Defs.D_0013

section Inconsistent

variable {α : Type} [LinearOrder α]

theorem two_le_of_ne_root {q : ℕ ≃ α} {T : Tree2 α} (hc : Compat q T) (c : α)
    (hne : c ≠ T.root) : 2 ≤ q.symm c := by
  rcases (T.connected c).cases_tail with h | ⟨b, _, hbc⟩
  · exact absurd h hne
  · have h1 := T.idx_pos b c hbc
    have h2 := hc.idx_lt_num b (T.idx c) h1
    rw [Tree2.child_eq T hbc] at h2
    omega

/-- D_0013 の `Compat` は充足不能。 -/
theorem not_compat (q : ℕ ≃ α) (T : Tree2 α) : ¬ Compat q T := by
  intro hc
  by_cases h0 : q 0 = T.root
  · have h1 : q 1 ≠ T.root := by
      intro h1
      have := q.injective (h0.trans h1.symm)
      exact absurd this (by decide)
    have := two_le_of_ne_root hc (q 1) h1
    rw [Equiv.symm_apply_apply] at this
    omega
  · have := two_le_of_ne_root hc (q 0) h0
    rw [Equiv.symm_apply_apply] at this
    omega

end Inconsistent

section Compat2

variable {α : Type} [LinearOrder α]

/-- `Compat` の修正版（`idx_lt_num` を `≤` に弱めた）。 -/
structure Compat2 (q : ℕ ≃ α) (T : Tree2 α) : Prop where
  num_child : ∀ p c, T.C p c → q.symm p < q.symm c
  idx_le_num : ∀ p j, 0 < j → j ≤ q.symm (T.child p j)
  desc_of_mem : ∀ p r, p < r → r < T.child p 1 →
    ∃ l, 0 < l ∧ ReflTransGen T.C (T.child p l) r
  shrink : ∀ p u, p < u → ∃ a, 0 < a ∧ T.child p a < u

variable {q : ℕ ≃ α} {T : Tree2 α}

theorem num_desc_le' (hc : Compat2 q T) {y r : α} (h : ReflTransGen T.C y r) :
    q.symm y ≤ q.symm r := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (hc.num_child _ _ hbc).le

/-- Proposition 3.2.1（Compat2 版）。 -/
theorem prop_3_2_1' (hc : Compat2 q T) {a : ℕ} (ha : 0 < a) {p r : α}
    (h1 : p < r) (h2 : r < T.child p a) :
    q.symm p < q.symm r ∧ a < q.symm r ∧
      ∀ b, 0 < b → Set.Ico r (T.child r b) ⊆ Set.Ioo p (T.child p a) := by
  have hr1 : r < T.child p 1 :=
    lt_of_lt_of_le h2 (Tree2.child_le_child T p (by omega) ha)
  obtain ⟨l, hl0, hd⟩ := hc.desc_of_mem p r h1 hr1
  have hal : a < l := by
    by_contra hc'
    have hle : T.child p a ≤ T.child p l := Tree2.child_le_child T p hl0 (by omega)
    have := Tree2.desc_le T hd
    exact absurd (lt_of_le_of_lt (le_trans hle this) h2) (lt_irrefl _)
  have hnum := num_desc_le' hc hd
  refine ⟨lt_of_lt_of_le (hc.num_child p _ (T.C_child p l hl0)) hnum,
    lt_of_lt_of_le (lt_of_lt_of_le hal (hc.idx_le_num p l hl0)) hnum, ?_⟩
  intro b hb x hx
  have hd' : ReflTransGen T.C (T.child p l) (T.child r b) := hd.tail (T.C_child r b hb)
  exact ⟨lt_of_lt_of_le h1 hx.1, lt_trans hx.2 (desc_lt_child T ha hal hd')⟩

end Compat2

end Defs.D_0024
