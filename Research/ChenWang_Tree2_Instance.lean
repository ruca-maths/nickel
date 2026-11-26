import Mathlib.Data.PNat.Basic
import Mathlib.Data.List.Lex
import Mathlib.Basic.Countable.Basic
import Mathlib.Topology.Bases
import Defs.D_0002
import Defs.D_0003
import Defs.D_0005
import Defs.D_0007
import Defs.D_0009
import Defs.D_0011

/-!
# Concrete Realization of Chen–Wang's `Tree2` (`Q`, `ρ'`, `ρ`, `H(n, c)`)

This file constructs a concrete, zero-`sorry` realization of the entire
Section 2–3 axiomatic foundation (`Defs.D_0002`, `D_0003`, `D_0005`, `D_0007`,
`D_0009`, `D_0011`) on the countable linear order

  `QTree := List (OrderDual PNat)`

equipped with the standard lexicographic order:
- `root := []` is the minimum element;
- the `j`-th child (`j ≥ 1`) of `p` is `p ++ [OrderDual.toDual ⟨j, hj⟩]`;
- `OrderDual` reverses the child order so `j < j' → child p j' < child p j`,
  and every proper prefix is smaller than its extensions (`p < child p j`).

We prove:
1. `noMaxOrder_QTree`: `NoMaxOrder QTree` (needed for `Defs.D_0009.isClosed_Ico` / `I_coD`).
2. `qtree_equiv_nat`: `Nonempty (ℕ ≃ QTree)` (instantiating `q : ℕ ≃ α` in `Defs.D_0007` / `D_0011`).
3. `qtreeTree2 : Defs.D_0003.Tree2 QTree`: full realization of all axioms of `Tree` and `Tree2`.
4. `qtree_I_coD`: `Defs.D_0009.I_coD` instantiated on `QTree`.
5. `qtree_two_points`: `∃ a b : QTree, a ≠ b` (needed for `Defs.D_0007.H_sub_index`).
-/

namespace Research.ChenWangTree

open Relation

/-- Concrete countable linear order realizing Chen–Wang's tree `Q`. -/
abbrev QTree : Type := List (OrderDual ℕ+)

private lemma list_lex_lt_append_singleton {α : Type*} [LinearOrder α] (u : List α) (x : α) :
    u < u ++ [x] := by
  induction u with
  | nil => exact List.Lex.nil
  | cons a as ih => exact List.Lex.cons ih

private lemma list_lex_nil_le {α : Type*} [LinearOrder α] (u : List α) :
    ([] : List α) ≤ u := by
  cases u with
  | nil => exact le_rfl
  | cons a as => exact le_of_lt List.Lex.nil

instance : NoMaxOrder QTree where
  exists_gt u := ⟨u ++ [OrderDual.toDual 1], list_lex_lt_append_singleton u _⟩

/-- Helper: `QTree` has at least two distinct elements. -/
theorem qtree_two_points : ∃ a b : QTree, a ≠ b :=
  ⟨[], [OrderDual.toDual 1], by simp⟩

/-- `QTree` is countably infinite, hence in bijection with `ℕ`. -/
theorem qtree_equiv_nat : Nonempty (ℕ ≃ QTree) := by
  have : Countable ℕ+ := Countable.of_equiv { n : ℕ // 0 < n } (Equiv.refl _)
  have : Countable (OrderDual ℕ+) := Countable.of_equiv ℕ+ OrderDual.ofDual.symm
  have : Countable QTree := inferInstance
  have : Infinite QTree := Infinite.of_injective (fun n : ℕ => List.replicate n (OrderDual.toDual 1))
    (fun m n h => by simpa using congrArg List.length h)
  exact ⟨(nonempty_equiv_of_countable (α := ℕ) (β := QTree)).some⟩

/-- The `j`-th child of `p` in `QTree` (for `j ≥ 1`; `[]` for `j = 0` so `qidx (qchild p 0) = 0`). -/
def qchild (p : QTree) (j : ℕ) : QTree :=
  if h : 0 < j then p ++ [OrderDual.toDual ⟨j, h⟩] else []

/-- Child relation `C p c`: `c` is `qchild p j` for some `j ≥ 1`. -/
def qC (p c : QTree) : Prop :=
  ∃ j : ℕ, 0 < j ∧ c = qchild p j

/-- Index of a node: the last coordinate (0 for the root `[]`). -/
def qidx (u : QTree) : ℕ :=
  match u.getLast? with
  | none => 0
  | some x => (OrderDual.ofDual x).1

private lemma qchild_pos (p : QTree) {j : ℕ} (hj : 0 < j) :
    qchild p j = p ++ [OrderDual.toDual ⟨j, hj⟩] := by
  simp [qchild, hj]

private lemma qidx_append_singleton (p : QTree) (x : OrderDual ℕ+) :
    qidx (p ++ [x]) = (OrderDual.ofDual x).1 := by
  simp [qidx]

private lemma qC_prefix_desc {p r : QTree} (h : ReflTransGen qC p r) :
    p <+: r := by
  induction h with
  | refl => exact List.prefix_rfl
  | tail _ hbc ih =>
    obtain ⟨j, hj, rfl⟩ := hbc
    rw [qchild_pos _ hj]
    exact ih.trans (List.prefix_append _ _)

private lemma list_lex_lt_of_prefix_of_len {α : Type*} [LinearOrder α]
    {p q : List α} (x : α) (h : p < q) (hlen : q.length ≤ p.length) :
    p ++ [x] < q := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => exact (lt_irrefl [] h).elim
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases q with
    | nil => exact (not_lt_of_ge (list_lex_nil_le _) h).elim
    | cons b bs =>
      have h' : List.Lex (· < ·) (a :: as) (b :: bs) := h
      cases h' with
      | rel hab =>
        exact List.Lex.rel hab
      | cons htail =>
        exact List.Lex.cons (ih htail (by simpa using hlen))

private lemma list_lex_append_lt_append {α : Type*} [LinearOrder α]
    (p : List α) {x y : α} (hxy : x < y) (t : List α) :
    p ++ (x :: t) < p ++ [y] := by
  induction p with
  | nil => exact List.Lex.rel hxy
  | cons a as ih => exact List.Lex.cons ih

/-- Concrete realization of `Defs.D_0003.Tree2` on `QTree`. -/
def qtreeTree2 : Defs.D_0003.Tree2 QTree where
  lev := List.length
  C := qC
  idx := qidx
  lev_child := by
    rintro p c ⟨j, hj, rfl⟩
    rw [qchild_pos p hj]
    simp
  lt_child := by
    rintro p c ⟨j, hj, rfl⟩
    rw [qchild_pos p hj]
    exact list_lex_lt_append_singleton p _
  gap := by
    rintro p c q ⟨j, hj, rfl⟩ hlev ⟨h1, h2⟩
    rw [qchild_pos p hj] at h2
    have hlt : p ++ [OrderDual.toDual ⟨j, hj⟩] < q :=
      list_lex_lt_of_prefix_of_len _ h1 hlev
    exact lt_asymm hlt h2
  idx_pos := by
    rintro p c ⟨j, hj, rfl⟩
    rw [qchild_pos p hj, qidx_append_singleton]
    exact hj
  child_anti := by
    rintro p c c' ⟨j, hj, rfl⟩ ⟨j', hj', rfl⟩ hlt
    rw [qchild_pos p hj, qchild_pos p hj'] at hlt ⊢
    rw [qidx_append_singleton, qidx_append_singleton] at hlt
    have hdual : OrderDual.toDual (⟨j', hj'⟩ : ℕ+) < OrderDual.toDual (⟨j, hj⟩ : ℕ+) := hlt
    exact list_lex_append_lt_append p hdual []
  child_inj := by
    rintro p c c' ⟨j, hj, rfl⟩ ⟨j', hj', rfl⟩ heq
    rw [qchild_pos p hj, qchild_pos p hj'] at heq ⊢
    rw [qidx_append_singleton, qidx_append_singleton] at heq
    subst heq
    rfl
  root := []
  child := qchild
  C_child := fun p j hj => ⟨j, hj, rfl⟩
  idx_child := by
    intro p j
    dsimp only [qchild]
    split_ifs with h
    · exact qidx_append_singleton p _
    · simp only [qidx, List.getLast?_nil]
      omega
  root_le := fun q => list_lex_nil_le q
  connected := by
    intro q
    induction q using List.reverseRecOn with
    | nil => exact ReflTransGen.refl
    | append_singleton xs x ih =>
      refine ih.tail ⟨(OrderDual.ofDual x).1, (OrderDual.ofDual x).2, ?_⟩
      rw [qchild_pos xs (OrderDual.ofDual x).2]
      rfl
  desc_lt := by
    rintro p j r hj hdesc
    have hpre : qchild p (j + 1) <+: r := qC_prefix_desc hdesc
    rw [qchild_pos p (Nat.succ_pos j)] at hpre
    rw [qchild_pos p hj]
    obtain ⟨t, rfl⟩ := hpre
    rw [List.append_assoc]
    have hdual : OrderDual.toDual (⟨j + 1, Nat.succ_pos j⟩ : ℕ+) <
        OrderDual.toDual (⟨j, hj⟩ : ℕ+) := Nat.lt_succ_self j
    exact list_lex_append_lt_append p hdual t

/-- Instantiation of `Defs.D_0009.I_coD` on `QTree`. -/
theorem qtree_I_coD {a : ℕ} (ha : 0 < a) :
    (∀ p, qtreeTree2.QStar a p →
      @IsOpen QTree (Defs.D_0009.rho QTree) (Set.Ico p (qtreeTree2.child p a)) ∧
        @IsClosed QTree (Defs.D_0009.rho QTree) (Set.Ico p (qtreeTree2.child p a))) ∧
    Defs.D_0009.IsDiscreteFam (Defs.D_0009.rho QTree)
      (fun p : {p : QTree // qtreeTree2.QStar a p} => Set.Ico p.1 (qtreeTree2.child p.1 a)) ∧
    (∀ x, ∃ p, qtreeTree2.QStar a p ∧ x ∈ Set.Ico p (qtreeTree2.child p a)) :=
  Defs.D_0009.I_coD qtreeTree2 ha

section XTopLemmas

variable {α : Type} (q : ℕ ≃ α)

/-- For each `n ≥ 1`, `{H q n c | c : ℕ}` is a discrete clopen partition of `(ℕ → α, xtop α)`. -/
theorem H_isDiscreteFam (n : ℕ) (hn : 0 < n) :
    Defs.D_0009.IsDiscreteFam (Defs.D_0011.xtop α) (fun c : ℕ => Defs.D_0007.H q n c) := by
  intro x
  obtain ⟨c₀, hx⟩ := Defs.D_0007.H_cover q n x
  refine ⟨Defs.D_0007.H q n c₀, Defs.D_0011.H_isOpen q n hn c₀, hx, ?_⟩
  intro c₁ c₂ ⟨w₁, hw₁, hw₁₀⟩ ⟨w₂, hw₂, hw₂₀⟩
  have h1 : c₁ = c₀ := by
    by_contra hne
    exact Set.disjoint_left.mp (Defs.D_0007.H_disjoint q n hne) hw₁ hw₁₀
  have h2 : c₂ = c₀ := by
    by_contra hne
    exact Set.disjoint_left.mp (Defs.D_0007.H_disjoint q n hne) hw₂ hw₂₀
  rw [h1, h2]

/-- `{H q n c | 0 < n, c : ℕ}` is a clopen topological basis of `(ℕ → α, xtop α)`. -/
theorem H_isTopologicalBasis :
    @TopologicalSpace.IsTopologicalBasis (ℕ → α) (Defs.D_0011.xtop α)
      { S : Set (ℕ → α) | ∃ n : ℕ, 0 < n ∧ ∃ c : ℕ, S = Defs.D_0007.H q n c } := by
  let : TopologicalSpace (ℕ → α) := Defs.D_0011.xtop α
  have hopen : ∀ S ∈ { S : Set (ℕ → α) | ∃ n : ℕ, 0 < n ∧ ∃ c : ℕ, S = Defs.D_0007.H q n c },
      IsOpen S := by
    rintro _ ⟨n, hn, c, rfl⟩
    exact Defs.D_0011.H_isOpen q n hn c
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds hopen ?_
  intro x U hxU hU_open
  let : TopologicalSpace α := ⊥
  obtain ⟨I, t, ht_all, htU⟩ := isOpen_pi_iff.mp hU_open x hxU
  let n : ℕ := I.sup id + 1
  have hn : 0 < n := Nat.succ_pos _
  let c : ℕ := Defs.D_0007.code n (fun k => q.symm (x k))
  refine ⟨Defs.D_0007.H q n c, ⟨n, hn, c, rfl⟩, rfl, ?_⟩
  intro y hy
  have hsame : ∀ k < n, y k = x k := (Defs.D_0007.mem_H_iff_same q n hn y x).mp hy
  refine htU fun k hkI => ?_
  have hkn : k < n := Nat.lt_succ_of_le (Finset.le_sup (f := id) hkI)
  rw [hsame k hkn]
  exact (ht_all k hkI).2

/-- For every `x : ℕ → α`, the clopen neighborhoods `H q (n + 1) (code (n + 1) (q.symm ∘ x))`
have intersection `{x}` (matching the clopen-sequence hypothesis of `Specs.L_0031`). -/
theorem H_inter_eq_singleton (x : ℕ → α) :
    (⋂ n : ℕ, Defs.D_0007.H q (n + 1) (Defs.D_0007.code (n + 1) (fun k => q.symm (x k)))) = {x} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro hy
    funext k
    exact (Defs.D_0007.mem_H_iff_same q (k + 1) (Nat.succ_pos k) y x).mp (hy k) k (Nat.lt_succ_self k)
  · rintro rfl n
    rfl

end XTopLemmas

end Research.ChenWangTree
