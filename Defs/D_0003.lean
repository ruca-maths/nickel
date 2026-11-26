import Mathlib.Order.Interval.Set.Basic
import Mathlib.Logic.Relation
import Defs.D_0002

namespace Defs.D_0003

/-!
Chen–Wang (arXiv 1809.03763v2) 第2節 Construction 2 と Proposition 2.2.1, 2.2.2, 2.2.4。

`Tree2` は `Defs.D_0002.Tree` に次を足したもの:
* `root`（= q₀ = 0）, `root_le` : 全点は root 以上（Q = ℚ ∩ [0,1)）
* `child p j`（j ≥ 1）: p の番号 j の子 `p_j`（`C p (child p j)`, `idx (child p j) = j`）
* `connected` : 全点は root の子孫（Q = ∪ S_n）
* `desc_lt` : `p_{j+1}` の子孫はすべて `p_j` より小さい
  （論文の `S(q_i^n) ⊂ (q_i^n, q_i^0)` を子孫に延ばしたもの）

`QStar a`（= Q*_a）: root を含み、`p ∈ Q*_a` かつ番号 `≤ a` の子 `c` なら `c ∈ Q*_a`。
`I_a = {[p, p_a) : p ∈ Q*_a}`。

Prop 2.2.1 の論文の証明（本文 228–231 行）は「q = q_{li}, i > a なら q ∈ [q_l, q_{la}) ∈ I_a」と
書くが、q_l ∉ Q*_a の場合が抜けている。ここでは祖先列で番号が初めて a を超える所で
区間を取る修正版の証明（`cover_aux`）を用いる。互いに素であることは論文では Note で済まされて
いるが、`not_mem_gap`（Q*_a の点は (p, p_a) に入らない）として gap から示す。
-/

open Relation

structure Tree2 (α : Type) [LinearOrder α] extends Defs.D_0002.Tree α where
  root : α
  child : α → ℕ → α
  C_child : ∀ p j, 0 < j → C p (child p j)
  idx_child : ∀ p j, idx (child p j) = j
  root_le : ∀ q, root ≤ q
  connected : ∀ q, ReflTransGen C root q
  desc_lt : ∀ p j r, 0 < j → ReflTransGen C (child p (j + 1)) r → r < child p j

variable {α : Type} [LinearOrder α]

namespace Tree2

/-- Q*_a。 -/
inductive QStar (T : Tree2 α) (a : ℕ) : α → Prop
  | root : QStar T a T.root
  | step : ∀ p c, QStar T a p → T.C p c → T.idx c ≤ a → QStar T a c

/-- I_a の元 `[p, p_a)`（p ∈ Q*_a）の和に q が入ること。 -/
def IUnion (T : Tree2 α) (a : ℕ) (q : α) : Prop :=
  ∃ p, T.QStar a p ∧ q ∈ Set.Ico p (T.child p a)

theorem child_eq (T : Tree2 α) {p c : α} (h : T.C p c) : T.child p (T.idx c) = c :=
  T.child_inj p _ c (T.C_child p _ (T.idx_pos p c h)) h (T.idx_child p _)

theorem desc_le (T : Tree2 α) {y r : α} (h : ReflTransGen T.C y r) : y ≤ r := by
  induction h with
  | refl => exact le_rfl
  | tail _ hc ih => exact le_trans ih (T.lt_child _ _ hc).le

theorem child_le_child (T : Tree2 α) (p : α) {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) :
    T.child p j ≤ T.child p i := by
  rcases lt_or_eq_of_le hij with h | rfl
  · refine (T.child_anti p _ _ (T.C_child p i hi) (T.C_child p j (by omega)) ?_).le
    rw [T.idx_child, T.idx_child]; exact h
  · exact le_rfl

/-- 被覆の不変量: q ∈ Q*_a か、ある z ∈ Q*_a と番号 i > a について q は z_i の子孫。 -/
theorem cover_aux (T : Tree2 α) (a : ℕ) (q : α) :
    T.QStar a q ∨ ∃ z i, T.QStar a z ∧ a < i ∧ ReflTransGen T.C (T.child z i) q := by
  induction T.connected q with
  | refl => exact Or.inl QStar.root
  | @tail b c _ hbc ih =>
    rcases ih with hq | ⟨z, i, hz, hi, hd⟩
    · by_cases hc : T.idx c ≤ a
      · exact Or.inl (QStar.step b c hq hbc hc)
      · refine Or.inr ⟨b, T.idx c, hq, by omega, ?_⟩
        rw [child_eq T hbc]
    · exact Or.inr ⟨z, i, hz, hi, hd.tail hbc⟩

/-- Proposition 2.2.1（被覆）: ∪ I_a = Q（a ≥ 1）。 -/
theorem prop_2_2_1_cover (T : Tree2 α) {a : ℕ} (ha : 0 < a) (q : α) : T.IUnion a q := by
  rcases cover_aux T a q with hq | ⟨z, i, hz, hi, hd⟩
  · exact ⟨q, hq, le_rfl, T.lt_child _ _ (T.C_child q a ha)⟩
  · refine ⟨z, hz, ?_, ?_⟩
    · exact le_trans (T.lt_child _ _ (T.C_child z i (by omega))).le (desc_le T hd)
    · have hi' : i = (i - 1) + 1 := by omega
      rw [hi'] at hd
      exact lt_of_lt_of_le (T.desc_lt z (i - 1) q (by omega) hd)
        (child_le_child T z ha (by omega))

/-- Q*_a の点は、どの p についても開区間 (p, p_a) に入らない。 -/
theorem not_mem_gap (T : Tree2 α) {a : ℕ} (ha : 0 < a) {r : α} (hr : T.QStar a r) :
    ∀ p, ¬ (p < r ∧ r < T.child p a) := by
  induction hr with
  | root => intro p h; exact absurd (T.root_le p) (not_le.mpr h.1)
  | step q c _ hqc hca ih =>
    intro p ⟨h1, h2⟩
    have hpa := T.C_child p a ha
    rcases lt_trichotomy q p with hqp | rfl | hpq
    · -- q < p < c: gap より lev q < lev p。すると lev c ≤ lev p で p < c < p_a は gap に反する
      have hlev : T.lev q < T.lev p := by
        by_contra hc
        exact T.gap q c p hqc (not_lt.mp hc) ⟨hqp, h1⟩
      have := T.lev_child q c hqc
      exact T.gap p _ c hpa (by omega) ⟨h1, h2⟩
    · -- c = q_{idx c} で idx c ≤ a なので c ≥ q_a
      have := child_le_child T q (T.idx_pos q c hqc) hca
      rw [child_eq T hqc] at this
      exact absurd h2 (not_lt.mpr this)
    · exact ih p ⟨hpq, lt_trans (T.lt_child q c hqc) h2⟩

/-- Proposition 2.2.1（互いに素）: I_a の相異なる元は交わらない。 -/
theorem prop_2_2_1_disjoint (T : Tree2 α) {a : ℕ} (ha : 0 < a) {p p' : α}
    (hp : T.QStar a p) (hp' : T.QStar a p') (hne : p ≠ p') :
    Disjoint (Set.Ico p (T.child p a)) (Set.Ico p' (T.child p' a)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rcases lt_or_gt_of_ne hne with h | h
  · exact not_mem_gap T ha hp' p ⟨h, lt_of_le_of_lt hx'.1 hx.2⟩
  · exact not_mem_gap T ha hp p' ⟨h, lt_of_le_of_lt hx.1 hx'.2⟩

/-- Proposition 2.2.1 をまとめた形: 各点は I_a のちょうど1つの元に入る。 -/
theorem prop_2_2_1 (T : Tree2 α) {a : ℕ} (ha : 0 < a) (q : α) :
    ∃! p, T.QStar a p ∧ q ∈ Set.Ico p (T.child p a) := by
  obtain ⟨p, hp, hq⟩ := prop_2_2_1_cover T ha q
  refine ⟨p, ⟨hp, hq⟩, ?_⟩
  rintro p' ⟨hp', hq'⟩
  by_contra hne
  exact Set.disjoint_left.mp (prop_2_2_1_disjoint T ha hp' hp hne) hq' hq

/-- Proposition 2.2.2: a ≤ b なら Q*_a ⊆ Q*_b。 -/
theorem prop_2_2_2 (T : Tree2 α) {a b : ℕ} (hab : a ≤ b) {q : α} (hq : T.QStar a q) :
    T.QStar b q := by
  induction hq with
  | root => exact QStar.root
  | step p c _ hpc hca ih => exact QStar.step p c ih hpc (le_trans hca hab)

/-- Proposition 2.2.4: ∪_a Q*_a = Q。 -/
theorem prop_2_2_4 (T : Tree2 α) (q : α) : ∃ a, T.QStar a q := by
  induction T.connected q with
  | refl => exact ⟨0, QStar.root⟩
  | @tail b c _ hbc ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨max a (T.idx c),
      QStar.step b c (prop_2_2_2 T (le_max_left _ _) ha) hbc (le_max_right _ _)⟩

end Tree2

end Defs.D_0003
