import Mathlib.Data.List.Lex
import Mathlib.Logic.Equiv.List
import Mathlib.Order.OrderDual
import Defs.D_0013

namespace Defs.D_0021

/-!
Chen–Wang の木構造の**具体的なモデル**と、`Defs.D_0013.Compat` の修正。

1. `not_compat` : D_0013 の `Compat q T` は**どの** `T : Tree2 α`, `q : ℕ ≃ α` でも成り立たない。
   `idx_lt_num`（`j < q⁻¹ (p_j)`）から根以外の点の Q 番号はすべて 2 以上になるが、
   `q` は全単射なので番号 0 と 1 の両方が使われ、そのうち根でない方が矛盾する。
   したがって D_0013/D_0016/D_0018/D_0019 の `Compat` 仮定付きの定理は空虚に真である。
2. `Compat2` : `idx_lt_num` を `idx_le_num`（`j ≤ q⁻¹ (p_j)`）に弱めた版。
   `prop_3_2_1'` は同じ結論（`a < q⁻¹ r` を含む）が Compat2 から出ることを示す。
3. モデル: `Node`（自然数のリスト）。`p` の番号 `j ≥ 1` の子は `p ++ [j-1]`。
   順序は辞書式で、先頭一致なら短い方が小さく、最初に異なる成分では成分の**大きい**方が小さい。
   これは最小元を持ち最大元を持たない可算稠密線形順序（ℚ ∩ [0,1) と順序同型）。
   `T : Tree2 Node`、`q : ℕ ≃ Node`（`q⁻¹ s = encode s.reverse`）について `Compat2 q T`。
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

section Model

/-- 順序の実体: 辞書式順序（成分は逆向きに比べる。先頭一致なら短い方が小さい）。 -/
def R (s t : List ℕ) : Prop := List.Lex (fun a b : ℕ => b < a) s t

theorem prefix_lt (p : List ℕ) (a : ℕ) (m : List ℕ) : R p (p ++ a :: m) := by
  induction p with
  | nil => exact List.Lex.nil
  | cons b p ih => exact List.Lex.cons ih

theorem app_lt (p : List ℕ) {a b : ℕ} (h : b < a) (m m' : List ℕ) :
    R (p ++ a :: m) (p ++ b :: m') := by
  induction p with
  | nil => exact List.Lex.rel h
  | cons c p ih => exact List.Lex.cons ih

theorem lt_cases (p q : List ℕ) (h : R p q) :
    (∃ a m, q = p ++ a :: m) ∨ ∀ r, R (p ++ r) q := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => cases h
    | cons a m => exact Or.inl ⟨a, m, rfl⟩
  | cons b p ih =>
    cases q with
    | nil => cases h
    | cons c q' =>
      cases h with
      | cons h' =>
        rcases ih q' h' with ⟨a, m, rfl⟩ | h2
        · exact Or.inl ⟨a, m, rfl⟩
        · exact Or.inr fun r => List.Lex.cons (h2 r)
      | rel h' => exact Or.inr fun r => List.Lex.rel h'

theorem root_le' (q : List ℕ) : q = [] ∨ R [] q := by
  cases q with
  | nil => exact Or.inl rfl
  | cons a m => exact Or.inr List.Lex.nil

/-- 子関係。 -/
def C (p c : List ℕ) : Prop := ∃ k : ℕ, c = p ++ [k]

/-- 子の番号（最後の成分 + 1、根は 0）。 -/
def idx (c : List ℕ) : ℕ :=
  match c.reverse with
  | [] => 0
  | k :: _ => k + 1

theorem idx_app (p : List ℕ) (k : ℕ) : idx (p ++ [k]) = k + 1 := by
  simp [idx]

def child (p : List ℕ) (j : ℕ) : List ℕ :=
  if j = 0 then [] else p ++ [j - 1]

theorem child_pos (p : List ℕ) {j : ℕ} (hj : 0 < j) : child p j = p ++ [j - 1] := by
  simp [child, Nat.pos_iff_ne_zero.mp hj]

theorem desc_app (x m : List ℕ) : ReflTransGen C x (x ++ m) := by
  induction m generalizing x with
  | nil => simpa using ReflTransGen.refl
  | cons b m ih =>
    have h := ih (x ++ [b])
    simp only [List.append_assoc, List.singleton_append] at h
    exact ReflTransGen.head ⟨b, rfl⟩ h

theorem desc_inv {x r : List ℕ} (h : ReflTransGen C x r) : ∃ m, r = x ++ m := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := hbc
    obtain ⟨m, hm⟩ := ih
    exact ⟨m ++ [k], by rw [hk, hm, List.append_assoc]⟩

/-- モデルの台集合。 -/
def Node : Type := List ℕ

instance : LinearOrder Node :=
  LinearOrder.lift' (fun s : Node => (s : List ℕᵒᵈ)) (fun _ _ h => h)

theorem lt_iff (s t : Node) : s < t ↔ R s t := Iff.rfl

theorem R_asymm {s t : List ℕ} (h1 : R s t) (h2 : R t s) : False :=
  lt_asymm (α := Node) ((lt_iff _ _).2 h1) ((lt_iff _ _).2 h2)

theorem gap' {p q : List ℕ} (k : ℕ) (hlev : q.length ≤ p.length)
    (h1 : R p q) (h2 : R q (p ++ [k])) : False := by
  rcases lt_cases p q h1 with ⟨a, m, hq⟩ | h
  · have : q.length = p.length + (m.length + 1) := by rw [hq]; simp
    omega
  · exact R_asymm h2 (h [k])

theorem desc_lt' (p : List ℕ) (j : ℕ) (r : List ℕ) (hj : 0 < j)
    (h : ReflTransGen C (child p (j + 1)) r) : R r (child p j) := by
  rw [child_pos p (by omega : 0 < j + 1)] at h
  rw [child_pos p hj]
  obtain ⟨m, hm⟩ := desc_inv h
  rw [hm, List.append_assoc, List.singleton_append]
  exact app_lt p (by omega) m []

/-- 木 T。 -/
def T : Tree2 Node where
  lev := fun s => List.length (α := ℕ) s
  C := C
  idx := idx
  lev_child := by
    rintro p c ⟨k, hk⟩
    show List.length (α := ℕ) c = List.length (α := ℕ) p + 1
    rw [hk]; simp
  lt_child := by
    rintro p c ⟨k, hk⟩
    rw [lt_iff, hk]; exact prefix_lt p k []
  gap := by
    rintro p c q ⟨k, hk⟩ hlev ⟨h1, h2⟩
    rw [lt_iff] at h1 h2
    rw [hk] at h2
    exact gap' k hlev h1 h2
  idx_pos := by
    rintro p c ⟨k, hk⟩
    show 0 < idx c
    rw [hk, idx_app]; omega
  child_anti := by
    rintro p c c' ⟨k, hk⟩ ⟨k', hk'⟩ hlt
    change idx c < idx c' at hlt
    rw [hk, hk', idx_app, idx_app] at hlt
    rw [lt_iff, hk, hk']
    exact app_lt p (by omega) [] []
  child_inj := by
    rintro p c c' ⟨k, hk⟩ ⟨k', hk'⟩ heq
    change idx c = idx c' at heq
    rw [hk, hk', idx_app, idx_app] at heq
    have : k = k' := by omega
    show (c : List ℕ) = c'
    rw [hk, hk', this]
  root := ([] : List ℕ)
  child := child
  C_child := by
    intro p j hj
    show C p (child p j)
    rw [child_pos p hj]
    exact ⟨j - 1, rfl⟩
  idx_child := by
    intro p j
    show idx (child p j) = j
    by_cases hj : j = 0
    · subst hj; simp [child, idx]
    · rw [child_pos p (Nat.pos_of_ne_zero hj), idx_app]; omega
  root_le := by
    intro q
    rcases root_le' q with h | h
    · show ([] : List ℕ) ≤ q
      rw [h]
    · exact le_of_lt ((lt_iff _ _).2 h)
  connected := by
    intro q
    have h := desc_app [] q
    rw [List.nil_append] at h
    exact h
  desc_lt := by
    intro p j r hj h
    exact (lt_iff _ _).2 (desc_lt' p j r hj h)

/-- 番号付け（リスト版）`qL⁻¹ s = encode s.reverse`。 -/
def qL : ℕ ≃ List ℕ where
  toFun n := (Denumerable.ofNat (List ℕ) n).reverse
  invFun s := Encodable.encode s.reverse
  left_inv n := by simp
  right_inv s := by simp

theorem qL_symm_app (p : List ℕ) (k : ℕ) :
    qL.symm (p ++ [k]) = Nat.pair k (Encodable.encode p.reverse) + 1 := by
  show Encodable.encode (p ++ [k]).reverse = _
  simp

theorem qL_symm (p : List ℕ) : qL.symm p = Encodable.encode p.reverse := rfl

/-- 番号付け `q : ℕ ≃ Node`。 -/
def q : ℕ ≃ Node := qL

theorem compat2 : Compat2 q T where
  num_child := by
    rintro p c ⟨k, hk⟩
    show qL.symm p < qL.symm c
    rw [hk, qL_symm_app, qL_symm p]
    exact Nat.lt_succ_of_le (Nat.right_le_pair _ _)
  idx_le_num := by
    intro p j hj
    show j ≤ qL.symm (child p j)
    rw [child_pos p hj, qL_symm_app]
    have := Nat.left_le_pair (j - 1) (Encodable.encode (List.reverse (α := ℕ) p))
    omega
  desc_of_mem := by
    intro p r h1 h2
    change R p r at h1
    change R r (child p 1) at h2
    rw [child_pos p (by omega)] at h2
    rcases lt_cases p r h1 with ⟨a, m, hr⟩ | h
    · refine ⟨a + 1, by omega, ?_⟩
      show ReflTransGen C (child p (a + 1)) r
      have hr' : r = (p ++ [a]) ++ m := by
        rw [List.append_assoc, List.singleton_append]; exact hr
      rw [child_pos p (by omega), hr']
      simpa using desc_app (p ++ [a]) m
    · exact (R_asymm h2 (h [0])).elim
  shrink := by
    intro p u h
    change R p u at h
    rcases lt_cases p u h with ⟨b, m, hu⟩ | h'
    · refine ⟨b + 2, by omega, ?_⟩
      show R (child p (b + 2)) u
      rw [child_pos p (by omega), hu]
      exact app_lt p (by omega) [] m
    · refine ⟨1, by omega, ?_⟩
      show R (child p 1) u
      rw [child_pos p (by omega)]
      exact h' [0]

end Model

end Defs.D_0021

