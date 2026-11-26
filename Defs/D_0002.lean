import Mathlib.Order.Interval.Set.Basic

namespace Defs.D_0002

/-!
Chen–Wang (arXiv 1809.03763v2) 第2節 Construction 1 の木構造の抽象化。

各点 `p` の「子」は収束列 `S_{lev p + 1}(p)` の項 `p_1 > p_2 > … → p`。
* `lev p` : `p ∈ S_{lev p}`
* `C p c` : `c ∈ S_{lev p + 1}(p)`
* `idx c` : `c = p_{idx c}`（子の番号、1 始まり）
公理:
* `lev_child` : `C p c → lev c = lev p + 1`
* `lt_child`  : `C p c → p < c`
* `gap`       : `C p c → lev q ≤ lev p → ¬ (p < q < c)`
  （論文の `S(q_i^n) ⊂ (q_i^n, q_i^0)` と `(q_i^n, q_i^0) ∩ ∪_{i≤n} S_i = ∅` から）
* `idx_pos`, `child_anti`, `child_inj` : 子の番号付け（番号が大きいほど `p` に近い）
-/

structure Tree (α : Type) [LinearOrder α] where
  lev : α → ℕ
  C : α → α → Prop
  idx : α → ℕ
  lev_child : ∀ p c, C p c → lev c = lev p + 1
  lt_child : ∀ p c, C p c → p < c
  gap : ∀ p c q, C p c → lev q ≤ lev p → ¬ (p < q ∧ q < c)
  idx_pos : ∀ p c, C p c → 0 < idx c
  child_anti : ∀ p c c', C p c → C p c' → idx c < idx c' → c' < c
  child_inj : ∀ p c c', C p c → C p c' → idx c = idx c' → c = c'

variable {α : Type} [LinearOrder α]

/-- `k < h < ki`（`C k ki`, `C h hj`）なら `[h, hj) ⊆ [k, ki)`。 -/
theorem nested_of_lt (T : Tree α) {k ki h hj : α}
    (hk : T.C k ki) (hh : T.C h hj) (h1 : k < h) (h2 : h < ki) :
    Set.Ico h hj ⊆ Set.Ico k ki := by
  have hlev : T.lev k < T.lev h := by
    by_contra hc
    exact T.gap k ki h hk (not_lt.mp hc) ⟨h1, h2⟩
  have hki : hj ≤ ki := by
    by_contra hc
    have := T.lev_child k ki hk
    exact T.gap h hj ki hh (by omega) ⟨h2, not_le.mp hc⟩
  intro x hx
  exact ⟨le_trans h1.le hx.1, lt_of_lt_of_le hx.2 hki⟩

/-- Chen–Wang Proposition 2.1.4: 区間族 `{[p, c) : C p c}` は laminar。
収束性も inf の存在も使わない。 -/
theorem prop_2_1_4 (T : Tree α) {k ki h hj : α}
    (hk : T.C k ki) (hh : T.C h hj) :
    Disjoint (Set.Ico k ki) (Set.Ico h hj) ∨
      Set.Ico k ki ⊆ Set.Ico h hj ∨ Set.Ico h hj ⊆ Set.Ico k ki := by
  rcases lt_trichotomy k h with hkh | rfl | hkh
  · by_cases h2 : h < ki
    · exact Or.inr (Or.inr (nested_of_lt T hk hh hkh h2))
    · left
      rw [Set.disjoint_left]
      intro x hx hx'
      exact h2 (lt_of_le_of_lt hx'.1 hx.2)
  · rcases le_total ki hj with h3 | h3
    · exact Or.inr (Or.inl (Set.Ico_subset_Ico_right h3))
    · exact Or.inr (Or.inr (Set.Ico_subset_Ico_right h3))
  · by_cases h2 : k < hj
    · exact Or.inr (Or.inl (nested_of_lt T hh hk hkh h2))
    · left
      rw [Set.disjoint_left]
      intro x hx hx'
      exact h2 (lt_of_le_of_lt hx.1 hx'.2)

end Defs.D_0002
