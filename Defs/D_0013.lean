import Mathlib.Logic.Equiv.Defs
import Defs.D_0005

namespace Defs.D_0013

/-!
Chen–Wang (arXiv 1809.03763v2) Proposition 3.2.1 のための、木 `T : Tree2 α` と
番号付け `q : ℕ ≃ α`（Δ-order の Q = {q_i}）の両立公理。

* `num_child`   : 子の Q 番号は親より大きい（Prop 2.1.3）
* `idx_lt_num`  : `p_j` の Q 番号は j より大きい（Prop 2.1.1）
* `desc_of_mem` : `(p, p_1)` の点はある子 `p_l` の子孫（Construction 1 の B) と
  `(p, p_1) = ⋃_{l ≥ 2} [p_l, p_{l-1})` からの帰納法の木版）
* `shrink`      : `p_a → p`（a → ∞）。Prop 3.3.1（⋂ g(n,x) = {x}）用。

ℚ ∩ [0,1) 上にこれらを満たす `Tree2` と `q` が存在することは別途示す必要がある。

定理:
* `num_desc_le` : 子孫の Q 番号は大きい（以上）。
* `desc_lt_child` : `a < l` なら `p_l` の子孫は `p_a` より小さい。
* `prop_3_2_1` : `r ∈ (p, p_a)`（a ≥ 1）なら `q⁻¹ p < q⁻¹ r`, `a < q⁻¹ r`, 任意の b ≥ 1 で
  `[r, r_b) ⊆ (p, p_a)`。
-/

open Relation Defs.D_0003

variable {α : Type} [LinearOrder α]

structure Compat (q : ℕ ≃ α) (T : Tree2 α) : Prop where
  num_child : ∀ p c, T.C p c → q.symm p < q.symm c
  idx_lt_num : ∀ p j, 0 < j → j < q.symm (T.child p j)
  desc_of_mem : ∀ p r, p < r → r < T.child p 1 →
    ∃ l, 0 < l ∧ ReflTransGen T.C (T.child p l) r
  shrink : ∀ p u, p < u → ∃ a, 0 < a ∧ T.child p a < u

variable {q : ℕ ≃ α} {T : Tree2 α}

theorem num_desc_le (hc : Compat q T) {y r : α} (h : ReflTransGen T.C y r) :
    q.symm y ≤ q.symm r := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (hc.num_child _ _ hbc).le

theorem desc_lt_child (T : Tree2 α) {p r : α} {a l : ℕ} (ha : 0 < a) (hal : a < l)
    (h : ReflTransGen T.C (T.child p l) r) : r < T.child p a := by
  have hl : l - 1 + 1 = l := by omega
  have h1 : r < T.child p (l - 1) :=
    T.desc_lt p (l - 1) r (by omega) (by rw [hl]; exact h)
  exact lt_of_lt_of_le h1 (Tree2.child_le_child T p ha (by omega))

theorem prop_3_2_1 (hc : Compat q T) {a : ℕ} (ha : 0 < a) {p r : α}
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
  have hnum := num_desc_le hc hd
  refine ⟨lt_of_lt_of_le (hc.num_child p _ (T.C_child p l hl0)) hnum,
    lt_of_lt_of_le (lt_trans hal (hc.idx_lt_num p l hl0)) hnum, ?_⟩
  intro b hb x hx
  have hd' : ReflTransGen T.C (T.child p l) (T.child r b) := hd.tail (T.C_child r b hb)
  exact ⟨lt_of_lt_of_le h1 hx.1, lt_trans hx.2 (desc_lt_child T ha hal hd')⟩

end Defs.D_0013
