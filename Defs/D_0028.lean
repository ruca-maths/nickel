import Mathlib.Data.List.Lex
import Mathlib.Logic.Equiv.List
import Mathlib.Order.OrderDual
import Defs.D_0024

namespace Defs.D_0028

/-!
Chen–Wang の木構造の**具体的なモデル**（`Defs.D_0024.Compat2` の充足可能性）。

`Node`（自然数のリストを包む構造体、`Node.val : List ℕ`）。`p` の番号 `j ≥ 1` の子は
`⟨p.val ++ [j-1]⟩`。順序は辞書式で、先頭一致なら短い方が小さく、最初に異なる成分では成分の
**大きい**方が小さい（`List ℕᵒᵈ` の辞書式順序を `val` で引き戻したもの）。これは最小元を持ち
最大元を持たない可算稠密線形順序で、ℚ ∩ [0,1) と順序同型。
`T : Tree2 Node`、`q : ℕ ≃ Node`（`q⁻¹ s = encode s.val.reverse`）について `compat2 : Compat2 q T`。
以後 Construction 4 以降はこの `Node`, `T`, `q` の上で行えばよい。
-/

open Relation Defs.D_0003 Defs.D_0024

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

theorem R_irrefl (s : List ℕ) : ¬ R s s := by
  induction s with
  | nil => intro h; cases h
  | cons a s ih =>
    intro h
    cases h with
    | cons h' => exact ih h'
    | rel h' => exact lt_irrefl a h'

theorem R_trans {s t u : List ℕ} (h1 : R s t) (h2 : R t u) : R s u := by
  induction h1 generalizing u with
  | nil =>
    cases h2 with
    | cons _ => exact List.Lex.nil
    | rel _ => exact List.Lex.nil
  | cons h ih =>
    cases h2 with
    | cons h' => exact List.Lex.cons (ih h')
    | rel h' => exact List.Lex.rel h'
  | rel h =>
    cases h2 with
    | cons _ => exact List.Lex.rel h
    | rel h' => exact List.Lex.rel (lt_trans h' h)

theorem R_asymm {s t : List ℕ} (h1 : R s t) (h2 : R t s) : False :=
  R_irrefl s (R_trans h1 h2)

/-- 子関係（リスト版）。 -/
def CL (p c : List ℕ) : Prop := ∃ k : ℕ, c = p ++ [k]

/-- 子の番号（最後の成分 + 1、根は 0）。 -/
def idxL (c : List ℕ) : ℕ :=
  match c.reverse with
  | [] => 0
  | k :: _ => k + 1

theorem idxL_app (p : List ℕ) (k : ℕ) : idxL (p ++ [k]) = k + 1 := by
  simp [idxL]

def childL (p : List ℕ) (j : ℕ) : List ℕ :=
  if j = 0 then [] else p ++ [j - 1]

theorem childL_pos (p : List ℕ) {j : ℕ} (hj : 0 < j) : childL p j = p ++ [j - 1] := by
  simp [childL, Nat.pos_iff_ne_zero.mp hj]

theorem idxL_childL (p : List ℕ) (j : ℕ) : idxL (childL p j) = j := by
  by_cases hj : j = 0
  · subst hj; simp [childL, idxL]
  · rw [childL_pos p (Nat.pos_of_ne_zero hj), idxL_app]; omega

theorem descL_app (x m : List ℕ) : ReflTransGen CL x (x ++ m) := by
  induction m generalizing x with
  | nil => simpa using ReflTransGen.refl
  | cons b m ih =>
    have h := ih (x ++ [b])
    simp only [List.append_assoc, List.singleton_append] at h
    exact ReflTransGen.head ⟨b, rfl⟩ h

theorem descL_inv {x r : List ℕ} (h : ReflTransGen CL x r) : ∃ m, r = x ++ m := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := hbc
    obtain ⟨m, hm⟩ := ih
    exact ⟨m ++ [k], by rw [hk, hm, List.append_assoc]⟩

theorem gapL {p q : List ℕ} (k : ℕ) (hlev : q.length ≤ p.length)
    (h1 : R p q) (h2 : R q (p ++ [k])) : False := by
  rcases lt_cases p q h1 with ⟨a, m, hq⟩ | h
  · have : q.length = p.length + (m.length + 1) := by rw [hq]; simp
    omega
  · exact R_asymm h2 (h [k])

theorem descL_lt (p : List ℕ) (j : ℕ) (r : List ℕ) (hj : 0 < j)
    (h : ReflTransGen CL (childL p (j + 1)) r) : R r (childL p j) := by
  rw [childL_pos p (by omega : 0 < j + 1)] at h
  rw [childL_pos p hj]
  obtain ⟨m, hm⟩ := descL_inv h
  rw [hm, List.append_assoc, List.singleton_append]
  exact app_lt p (by omega) m []

theorem descL_of_mem (p r : List ℕ) (h1 : R p r) (h2 : R r (childL p 1)) :
    ∃ l, 0 < l ∧ ReflTransGen CL (childL p l) r := by
  rw [childL_pos p (by omega)] at h2
  rcases lt_cases p r h1 with ⟨a, m, hr⟩ | h
  · refine ⟨a + 1, by omega, ?_⟩
    have hr' : r = (p ++ [a]) ++ m := by
      rw [List.append_assoc, List.singleton_append]; exact hr
    rw [childL_pos p (by omega), hr']
    simpa using descL_app (p ++ [a]) m
  · exact (R_asymm h2 (h [0])).elim

theorem shrinkL (p u : List ℕ) (h : R p u) : ∃ a, 0 < a ∧ R (childL p a) u := by
  rcases lt_cases p u h with ⟨b, m, hu⟩ | h'
  · refine ⟨b + 2, by omega, ?_⟩
    rw [childL_pos p (by omega), hu]
    exact app_lt p (by omega) [] m
  · refine ⟨1, by omega, ?_⟩
    rw [childL_pos p (by omega)]
    exact h' [0]

/-- モデルの台集合。 -/
structure Node where
  val : List ℕ

theorem Node.val_inj : Function.Injective Node.val := by
  intro a b h
  cases a; cases b; cases h; rfl

theorem R_trich (s t : List ℕ) : s = t ∨ R s t ∨ R t s := by
  induction s generalizing t with
  | nil =>
    cases t with
    | nil => exact Or.inl rfl
    | cons b t => exact Or.inr (Or.inl List.Lex.nil)
  | cons a s ih =>
    cases t with
    | nil => exact Or.inr (Or.inr List.Lex.nil)
    | cons b t =>
      rcases lt_trichotomy a b with h | rfl | h
      · exact Or.inr (Or.inr (List.Lex.rel h))
      · rcases ih t with rfl | h | h
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (List.Lex.cons h))
        · exact Or.inr (Or.inr (List.Lex.cons h))
      · exact Or.inr (Or.inl (List.Lex.rel h))

noncomputable instance : LinearOrder Node where
  le s t := s = t ∨ R s.val t.val
  lt s t := R s.val t.val
  le_refl s := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | hab
    · exact hbc
    · rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr (R_trans hab hbc)
  lt_iff_le_not_ge a b := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (h' | h')
      · subst h'; exact R_irrefl _ h
      · exact R_asymm h h'
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1.symm) h2
      · exact h1
  le_antisymm a b hab hba := by
    rcases hab with rfl | hab
    · rfl
    · rcases hba with rfl | hba
      · rfl
      · exact (R_asymm hab hba).elim
  le_total a b := by
    rcases R_trich a.val b.val with h | h | h
    · exact Or.inl (Or.inl (Node.val_inj h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  toDecidableLE := Classical.decRel _

theorem lt_iff (s t : Node) : s < t ↔ R s.val t.val := Iff.rfl

theorem le_of_R_or_eq {s t : Node} (h : s.val = t.val ∨ R s.val t.val) : s ≤ t := by
  rcases h with h | h
  · exact le_of_eq (Node.val_inj h)
  · exact le_of_lt ((lt_iff s t).2 h)

/-- 木 T。 -/
noncomputable def T : Tree2 Node where
  lev := fun s => s.val.length
  C := fun p c => CL p.val c.val
  idx := fun c => idxL c.val
  lev_child := by
    rintro p c ⟨k, hk⟩
    show c.val.length = p.val.length + 1
    rw [hk]; simp
  lt_child := by
    rintro p c ⟨k, hk⟩
    rw [lt_iff, hk]; exact prefix_lt p.val k []
  gap := by
    rintro p c q ⟨k, hk⟩ hlev ⟨h1, h2⟩
    rw [lt_iff] at h1 h2
    rw [hk] at h2
    exact gapL k hlev h1 h2
  idx_pos := by
    rintro p c ⟨k, hk⟩
    show 0 < idxL c.val
    rw [hk, idxL_app]; omega
  child_anti := by
    rintro p c c' ⟨k, hk⟩ ⟨k', hk'⟩ hlt
    change idxL c.val < idxL c'.val at hlt
    rw [hk, hk', idxL_app, idxL_app] at hlt
    rw [lt_iff, hk, hk']
    exact app_lt p.val (by omega) [] []
  child_inj := by
    rintro p c c' ⟨k, hk⟩ ⟨k', hk'⟩ heq
    change idxL c.val = idxL c'.val at heq
    rw [hk, hk', idxL_app, idxL_app] at heq
    have : k = k' := by omega
    apply Node.val_inj
    rw [hk, hk', this]
  root := ⟨[]⟩
  child := fun p j => ⟨childL p.val j⟩
  C_child := by
    intro p j hj
    show CL p.val (childL p.val j)
    rw [childL_pos p.val hj]
    exact ⟨j - 1, rfl⟩
  idx_child := fun p j => idxL_childL p.val j
  root_le := by
    intro q
    apply le_of_R_or_eq
    cases q with
    | mk v =>
      cases v with
      | nil => exact Or.inl rfl
      | cons a m => exact Or.inr List.Lex.nil
  connected := by
    intro q
    have h := descL_app [] q.val
    rw [List.nil_append] at h
    have key : ∀ x y : List ℕ, ReflTransGen CL x y →
        ReflTransGen (fun p c : Node => CL p.val c.val) ⟨x⟩ ⟨y⟩ := by
      intro x y hxy
      induction hxy with
      | refl => exact ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail hbc
    exact key _ _ h
  desc_lt := by
    intro p j r hj h
    rw [lt_iff]
    have key : ∀ x y : Node, ReflTransGen (fun p c : Node => CL p.val c.val) x y →
        ReflTransGen CL x.val y.val := by
      intro x y hxy
      induction hxy with
      | refl => exact ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail hbc
    exact descL_lt p.val j r.val hj (key _ _ h)

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

/-- `Node` と `List ℕ` の同型。 -/
def nodeEquiv : Node ≃ List ℕ where
  toFun := Node.val
  invFun := Node.mk
  left_inv s := by cases s; rfl
  right_inv _ := rfl

/-- 番号付け `q : ℕ ≃ Node`。 -/
def q : ℕ ≃ Node := qL.trans nodeEquiv.symm

theorem q_symm (s : Node) : q.symm s = qL.symm s.val := rfl

theorem compat2 : Compat2 q T where
  num_child := by
    rintro p c ⟨k, hk⟩
    rw [q_symm, q_symm, hk, qL_symm_app, qL_symm p.val]
    exact Nat.lt_succ_of_le (Nat.right_le_pair _ _)
  idx_le_num := by
    intro p j hj
    show j ≤ qL.symm (childL p.val j)
    rw [childL_pos p.val hj, qL_symm_app]
    have := Nat.left_le_pair (j - 1) (Encodable.encode p.val.reverse)
    omega
  desc_of_mem := by
    intro p r h1 h2
    rw [lt_iff] at h1 h2
    obtain ⟨l, hl, hd⟩ := descL_of_mem p.val r.val h1 h2
    refine ⟨l, hl, ?_⟩
    have key : ∀ x y : List ℕ, ReflTransGen CL x y →
        ReflTransGen (fun p c : Node => CL p.val c.val) ⟨x⟩ ⟨y⟩ := by
      intro x y hxy
      induction hxy with
      | refl => exact ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail hbc
    exact key _ _ hd
  shrink := by
    intro p u h
    rw [lt_iff] at h
    obtain ⟨a, ha, h'⟩ := shrinkL p.val u.val h
    exact ⟨a, ha, (lt_iff _ _).2 h'⟩

end Defs.D_0028
