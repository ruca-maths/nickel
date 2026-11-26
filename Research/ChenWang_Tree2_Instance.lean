import Mathlib.Data.PNat.Basic
import Mathlib.Data.List.Lex
import Mathlib.Basic.Countable.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Regular
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

section RhoProdBridge

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0005 Defs.D_0007 Defs.D_0009 Defs.D_0011

variable {α : Type} [LinearOrder α]

/-- `(α, rho α)` is `T1Space` whenever `NoMaxOrder α`. -/
theorem rho_t1Space [NoMaxOrder α] : @T1Space α (rho α) := by
  let : TopologicalSpace α := rho α
  refine ⟨fun x => ?_⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  have hyx : y ≠ x := hy
  rcases lt_or_gt_of_ne hyx with hlt | hgt
  · refine ⟨Set.Ico y x, ?_, isOpen_Ico y x, ⟨le_rfl, hlt⟩⟩
    intro z hz hzx
    exact (lt_irrefl x (hzx ▸ hz.2)).elim
  · obtain ⟨u, hu⟩ := exists_gt y
    refine ⟨Set.Ico y u, ?_, isOpen_Ico y u, ⟨le_rfl, hu⟩⟩
    intro z hz hzx
    exact (not_le_of_gt hgt (hzx ▸ hz.1)).elim

/-- `(α, rho α)` is `T3Space` (regular + T₁) whenever `NoMaxOrder α`. -/
theorem rho_t3Space [NoMaxOrder α] : @T3Space α (rho α) := by
  let : TopologicalSpace α := rho α
  have : T1Space α := rho_t1Space
  have hbas : TopologicalSpace.IsTopologicalBasis { s : Set α | ∃ p q : α, s = Set.Ico p q } := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨p, q, rfl⟩; exact isOpen_Ico p q
    · intro x U hxU hU_open
      -- Induction on GenerateOpen
      have hgen : ∀ S, TopologicalSpace.GenerateOpen { s : Set α | ∃ p q : α, s = Set.Ico p q } S →
          ∀ y ∈ S, ∃ p q : α, y ∈ Set.Ico p q ∧ Set.Ico p q ⊆ S := by
        intro S hS
        induction hS with
        | basic s hs =>
          obtain ⟨p, q, rfl⟩ := hs
          exact fun y hy => ⟨p, q, hy, Set.Subset.rfl⟩
        | univ =>
          intro y _
          obtain ⟨u, hu⟩ := exists_gt y
          exact ⟨y, u, ⟨le_rfl, hu⟩, Set.subset_univ _⟩
        | inter s t _ _ ihs iht =>
          intro y ⟨hys, hyt⟩
          obtain ⟨p₁, q₁, hy1, h1⟩ := ihs y hys
          obtain ⟨p₂, q₂, hy2, h2⟩ := iht y hyt
          refine ⟨max p₁ p₂, min q₁ q₂, ⟨max_le hy1.1 hy2.1, lt_min hy1.2 hy2.2⟩, ?_⟩
          intro z hz
          exact ⟨h1 ⟨le_trans (le_max_left _ _) hz.1, lt_of_lt_of_le hz.2 (min_le_left _ _)⟩,
                 h2 ⟨le_trans (le_max_right _ _) hz.1, lt_of_lt_of_le hz.2 (min_le_right _ _)⟩⟩
        | sUnion F _ ih =>
          rintro y ⟨s, hsF, hys⟩
          obtain ⟨p, q, hy, hsub⟩ := ih s hsF y hys
          exact ⟨p, q, hy, hsub.trans (Set.subset_sUnion_of_mem hsF)⟩
      obtain ⟨p, q, hy, hsub⟩ := hgen U hU_open x hxU
      exact ⟨Set.Ico p q, ⟨p, q, rfl⟩, hy, hsub⟩
  have : RegularSpace α := RegularSpace.of_exists_mem_nhds_isClosed_subset fun x U hU => by
    obtain ⟨O, hOU, hO_open, hxO⟩ := mem_nhds_iff.mp hU
    obtain ⟨S, ⟨p, q, rfl⟩, hxS, hSO⟩ := hbas.exists_subset_of_mem_open hxO hO_open
    exact ⟨Set.Ico p q, (isOpen_Ico p q).mem_nhds hxS, isClosed_Ico p q, hSO.trans hOU⟩
  exact ⟨⟩

/-- The `ρ'`-product topology on `ℕ → α`. -/
@[instance_reducible]
def rhoProd (α : Type) [LinearOrder α] : TopologicalSpace (ℕ → α) :=
  @Pi.topologicalSpace ℕ (fun _ => α) (fun _ => rho α)

/-- Every `rhoProd`-open set is `xtop`-open (`xtop α ≤ rhoProd α`). -/
theorem xtop_le_rhoProd : xtop α ≤ rhoProd α := by
  intro U hU
  let : TopologicalSpace (ℕ → α) := xtop α
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  let : TopologicalSpace α := rho α
  obtain ⟨I, t, ht_all, htU⟩ := isOpen_pi_iff.mp hU x hx
  let n : ℕ := I.sup id + 1
  refine ⟨{ y : ℕ → α | ∀ k < n, y k = x k }, ?_, isOpen_cyl n x, fun _ _ => rfl⟩
  intro y hy
  refine htU fun k hkI => ?_
  have hkn : k < n := Nat.lt_succ_of_le (Finset.le_sup (f := id) hkI)
  rw [hy k hkn]
  exact (ht_all k hkI).2

/-- Multi-coordinate cylinder block in `ℕ → α` determined by `p : Fin n → α` and `a : Fin n → ℕ`. -/
def ICyl (T : Tree2 α) (n : ℕ) (a : Fin n → ℕ) (p : Fin n → α) : Set (ℕ → α) :=
  { x : ℕ → α | ∀ i : Fin n, x i.1 ∈ Set.Ico (p i) (T.child (p i) (a i)) }

/-- Each cylinder block `ICyl T n a p` is clopen in `rhoProd α` (and hence in `xtop α`). -/
theorem ICyl_clopen [NoMaxOrder α] (T : Tree2 α) (n : ℕ) (a : Fin n → ℕ) (p : Fin n → α) :
    @IsOpen (ℕ → α) (rhoProd α) (ICyl T n a p) ∧
    @IsClosed (ℕ → α) (rhoProd α) (ICyl T n a p) := by
  let : TopologicalSpace α := rho α
  have hEq : ICyl T n a p =
      ⋂ i : Fin n, (fun x : ℕ → α => x i.1) ⁻¹' Set.Ico (p i) (T.child (p i) (a i)) := by
    ext x; simp [ICyl]
  constructor
  · change IsOpen (ICyl T n a p)
    rw [hEq]
    exact isOpen_iInter_of_finite fun i => (isOpen_Ico _ _).preimage (continuous_apply i.1)
  · change IsClosed (ICyl T n a p)
    rw [hEq]
    exact isClosed_iInter fun i => (isClosed_Ico _ _).preimage (continuous_apply i.1)

/-- Multi-coordinate c.o.D partition: for `a i > 0`, `{ICyl T n a p | ∀ i, QStar (a i) (p i)}`
is a clopen discrete partition of `(ℕ → α, rhoProd α)`. -/
theorem ICyl_coD [NoMaxOrder α] (T : Tree2 α) (n : ℕ) (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (∀ p : { p : Fin n → α // ∀ i, T.QStar (a i) (p i) },
      @IsOpen (ℕ → α) (rhoProd α) (ICyl T n a p.1) ∧
      @IsClosed (ℕ → α) (rhoProd α) (ICyl T n a p.1)) ∧
    IsDiscreteFam (rhoProd α)
      (fun p : { p : Fin n → α // ∀ i, T.QStar (a i) (p i) } => ICyl T n a p.1) ∧
    (∀ x : ℕ → α, ∃! p : { p : Fin n → α // ∀ i, T.QStar (a i) (p i) }, x ∈ ICyl T n a p.1) := by
  have huniq : ∀ x : ℕ → α,
      ∃! p : { p : Fin n → α // ∀ i, T.QStar (a i) (p i) }, x ∈ ICyl T n a p.1 := by
    intro x
    have hcoord : ∀ i : Fin n, ∃ p : α, T.QStar (a i) p ∧ x i.1 ∈ Set.Ico p (T.child p (a i)) :=
      fun i => prop_2_2_1_cover T (ha i) (x i.1)
    choose p hp hx using hcoord
    refine ⟨⟨p, hp⟩, hx, ?_⟩
    rintro ⟨p', hp'⟩ hx'
    apply Subtype.ext
    funext i
    by_contra hne
    exact Set.disjoint_left.mp (prop_2_2_1_disjoint T (ha i) (hp' i) (hp i) hne) (hx' i) (hx i)
  refine ⟨fun p => ICyl_clopen T n a p.1, ?_, huniq⟩
  intro x
  obtain ⟨p₀, hxp₀, hp₀_uniq⟩ := huniq x
  refine ⟨ICyl T n a p₀.1, (ICyl_clopen T n a p₀.1).1, hxp₀, ?_⟩
  intro p₁ p₂ ⟨w₁, hw₁, hw₁₀⟩ ⟨w₂, hw₂, hw₂₀⟩
  have h1 : p₁ = p₀ := by
    apply Subtype.ext; funext i
    by_contra hne
    exact Set.disjoint_left.mp (prop_2_2_1_disjoint T (ha i) (p₁.2 i) (p₀.2 i) hne) (hw₁ i) (hw₁₀ i)
  have h2 : p₂ = p₀ := by
    apply Subtype.ext; funext i
    by_contra hne
    exact Set.disjoint_left.mp (prop_2_2_1_disjoint T (ha i) (p₂.2 i) (p₀.2 i) hne) (hw₂ i) (hw₂₀ i)
  rw [h1, h2]

/-- Multi-coordinate laminar refinement: if `0 < a i ≤ b i` for all `i`, every `ICyl T n b h`
is either disjoint from or contained in `ICyl T n a p`. -/
theorem ICyl_laminar (T : Tree2 α) (n : ℕ) (a b : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i)
    {p h : Fin n → α} (hp : ∀ i, T.QStar (a i) (p i)) (hh : ∀ i, T.QStar (b i) (h i)) :
    Disjoint (ICyl T n a p) (ICyl T n b h) ∨ ICyl T n b h ⊆ ICyl T n a p := by
  by_cases hd : Disjoint (ICyl T n a p) (ICyl T n b h)
  · exact Or.inl hd
  · right
    obtain ⟨x, hxa, hxb⟩ := Set.not_disjoint_iff.mp hd
    intro y hy i
    rcases prop_2_2_5 T (ha i) (hab i) (hp i) (hh i) with hdisj | hsub
    · exact (Set.disjoint_left.mp hdisj (hxa i) (hxb i)).elim
    · exact hsub (hy i)

/-- Bridge between Section 2 (`ICyl`) and Section 3 (`H q n c`):
For `n ≥ 1` and `a i > 0`, every `H q n c` is contained in a unique `ICyl T n a p`
with `∀ i, T.QStar (a i) (p i)`. -/
theorem H_subset_unique_ICyl (T : Tree2 α) (q : ℕ ≃ α)
    {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) (c : ℕ) :
    ∃! p : { p : Fin n → α // ∀ i, T.QStar (a i) (p i) }, H q n c ⊆ ICyl T n a p.1 := by
  obtain ⟨x₀, hx₀⟩ := H_nonempty q n hn c
  have hcoord : ∀ i : Fin n, ∃ p : α, T.QStar (a i) p ∧ x₀ i.1 ∈ Set.Ico p (T.child p (a i)) :=
    fun i => prop_2_2_1_cover T (ha i) (x₀ i.1)
  choose p₀ hp₀ hx₀p using hcoord
  refine ⟨⟨p₀, hp₀⟩, ?_, ?_⟩
  · intro x hx i
    have hc : c = code n (fun k => q.symm (x₀ k)) := hx₀.symm
    rw [hc] at hx
    have hsame : x i.1 = x₀ i.1 := (mem_H_iff_same q n hn x x₀).mp hx i.1 i.2
    rw [hsame]
    exact hx₀p i
  · rintro ⟨p, hp⟩ hsub
    apply Subtype.ext
    funext i
    by_contra hne
    exact Set.disjoint_left.mp (prop_2_2_1_disjoint T (ha i) (hp i) (hp₀ i) hne)
      (hsub hx₀ i) (hx₀p i)

end RhoProdBridge

end Research.ChenWangTree
