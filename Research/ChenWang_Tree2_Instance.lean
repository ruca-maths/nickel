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

section QTreeBasisAndShrinking

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0009

/-- Helper: if `x < y` in `List α` and `x` is not a prefix of `y`, then `x ++ [z] < y`
for ANY `z : α`. -/
private lemma list_lex_append_lt_of_not_prefix {α : Type*} [LinearOrder α]
    {x y : List α} (hxy : x < y) (hnot : ¬ x <+: y) (z : α) :
    x ++ [z] < y := by
  induction x generalizing y with
  | nil => exact (hnot (List.nil_prefix)).elim
  | cons a as ih =>
    cases y with
    | nil => exact (not_lt_of_ge (list_lex_nil_le _) hxy).elim
    | cons b bs =>
      have h' : List.Lex (· < ·) (a :: as) (b :: bs) := hxy
      cases h' with
      | rel hab => exact List.Lex.rel hab
      | cons htail =>
        have hnot' : ¬ as <+: bs := fun hp => hnot (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
        exact List.Lex.cons (ih htail hnot')

/-- Every node `x : QTree` eventually belongs to `qtreeTree2.QStar a`. -/
theorem qtree_mem_QStar (x : QTree) :
    ∃ a₀ : ℕ, 0 < a₀ ∧ ∀ a, a₀ ≤ a → qtreeTree2.QStar a x := by
  induction x using List.reverseRecOn with
  | nil =>
    exact ⟨1, Nat.one_pos, fun a _ => QStar.root⟩
  | append_singleton xs d ih =>
    obtain ⟨a₀, ha₀, hxs⟩ := ih
    let k : ℕ := (OrderDual.ofDual d).1
    have hk : 0 < k := (OrderDual.ofDual d).2
    refine ⟨max a₀ k, lt_of_lt_of_le ha₀ (le_max_left _ _), fun a ha => ?_⟩
    have hxs_a : qtreeTree2.QStar a xs := hxs a (le_trans (le_max_left _ _) ha)
    have hC : qtreeTree2.C xs (xs ++ [d]) := ⟨k, hk, by rw [qchild_pos xs hk]; rfl⟩
    have hidx : qtreeTree2.idx (xs ++ [d]) ≤ a := by
      change qidx (xs ++ [d]) ≤ a
      rw [qidx_append_singleton]
      exact le_trans (le_max_right _ _) ha
    exact QStar.step xs (xs ++ [d]) hxs_a hC hidx

/-- Shrinking property on `QTree`: for any `x < y`, there exists `a > 0` such that
`x ∈ QStar a` and `child x a < y` (so `[x, child x a) ⊆ [x, y)`). -/
theorem qtree_Ico_shrink {x y : QTree} (hxy : x < y) :
    ∃ a : ℕ, 0 < a ∧ qtreeTree2.QStar a x ∧ qtreeTree2.child x a < y := by
  obtain ⟨a₀, ha₀, hxQ⟩ := qtree_mem_QStar x
  by_cases hpre : x <+: y
  · obtain ⟨t, rfl⟩ := hpre
    cases t with
    | nil =>
      simp at hxy
    | cons d rest =>
      let k : ℕ := (OrderDual.ofDual d).1
      let a : ℕ := max a₀ (k + 1)
      have ha : 0 < a := lt_of_lt_of_le ha₀ (le_max_left _ _)
      refine ⟨a, ha, hxQ a (le_max_left _ _), ?_⟩
      change qchild x a < x ++ d :: rest
      rw [qchild_pos x ha]
      have hlt : k < a := lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _)
      have hdual : OrderDual.toDual (⟨a, ha⟩ : ℕ+) < d := hlt
      have hgen : ∀ l : QTree, l ++ [OrderDual.toDual ⟨a, ha⟩] < l ++ d :: rest := by
        intro l
        induction l with
        | nil => exact List.Lex.rel hdual
        | cons b bs ih => exact List.Lex.cons ih
      exact hgen x
  · refine ⟨a₀, ha₀, hxQ a₀ le_rfl, ?_⟩
    change qchild x a₀ < y
    rw [qchild_pos x ha₀]
    exact list_lex_append_lt_of_not_prefix hxy hpre _

/-- `{ [p, child p a) | 0 < a, p ∈ QStar a }` is a clopen topological basis for
`(QTree, Defs.D_0009.rho QTree)`. -/
theorem qtree_I_isTopologicalBasis :
    @TopologicalSpace.IsTopologicalBasis QTree (rho QTree)
      { S : Set QTree | ∃ a : ℕ, 0 < a ∧ ∃ p : QTree,
          qtreeTree2.QStar a p ∧ S = Set.Ico p (qtreeTree2.child p a) } := by
  let : TopologicalSpace QTree := rho QTree
  have hopen : ∀ S ∈ { S : Set QTree | ∃ a : ℕ, 0 < a ∧ ∃ p : QTree,
      qtreeTree2.QStar a p ∧ S = Set.Ico p (qtreeTree2.child p a) }, IsOpen S := by
    rintro _ ⟨a, _, p, _, rfl⟩
    exact isOpen_Ico p _
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds hopen ?_
  intro x U hxU hU_open
  have hgen : ∀ V : Set QTree, IsOpen V → ∀ y ∈ V, ∃ u v : QTree, y ∈ Set.Ico u v ∧ Set.Ico u v ⊆ V := by
    intro V hV
    induction hV with
    | basic s hs =>
      obtain ⟨u, v, rfl⟩ := hs
      exact fun y hy => ⟨u, v, hy, Set.Subset.rfl⟩
    | univ =>
      intro y _
      obtain ⟨v, hv⟩ := exists_gt y
      exact ⟨y, v, ⟨le_rfl, hv⟩, Set.subset_univ _⟩
    | inter s t _ _ ihs iht =>
      intro y ⟨hys, hyt⟩
      obtain ⟨u₁, v₁, hy1, h1⟩ := ihs y hys
      obtain ⟨u₂, v₂, hy2, h2⟩ := iht y hyt
      refine ⟨max u₁ u₂, min v₁ v₂, ⟨max_le hy1.1 hy2.1, lt_min hy1.2 hy2.2⟩, fun z hz => ?_⟩
      exact ⟨h1 ⟨le_trans (le_max_left _ _) hz.1, lt_of_lt_of_le hz.2 (min_le_left _ _)⟩,
             h2 ⟨le_trans (le_max_right _ _) hz.1, lt_of_lt_of_le hz.2 (min_le_right _ _)⟩⟩
    | sUnion F _ ih =>
      rintro y ⟨s, hsF, hys⟩
      obtain ⟨u, v, hy, hsub⟩ := ih s hsF y hys
      exact ⟨u, v, hy, hsub.trans (Set.subset_sUnion_of_mem hsF)⟩
  obtain ⟨u, v, hxu_v, hsub⟩ := hgen U hU_open x hxU
  obtain ⟨a, ha, hxQ, hchild_lt⟩ := qtree_Ico_shrink hxu_v.2
  refine ⟨Set.Ico x (qtreeTree2.child x a), ⟨a, ha, x, hxQ, rfl⟩,
    ⟨le_rfl, qtreeTree2.lt_child x _ (qtreeTree2.C_child x a ha)⟩, ?_⟩
  intro z hz
  exact hsub ⟨le_trans hxu_v.1 hz.1, lt_trans hz.2 hchild_lt⟩

/-- Multi-coordinate cylinder blocks `ICyl qtreeTree2 n (fun _ => a) p` form a clopen
topological basis for `(ℕ → QTree, rhoProd QTree)`. -/
theorem qtree_ICyl_isTopologicalBasis :
    @TopologicalSpace.IsTopologicalBasis (ℕ → QTree) (rhoProd QTree)
      { S : Set (ℕ → QTree) | ∃ n a : ℕ, 0 < a ∧ ∃ p : Fin n → QTree,
          (∀ i, qtreeTree2.QStar a (p i)) ∧ S = ICyl qtreeTree2 n (fun _ => a) p } := by
  let : TopologicalSpace (ℕ → QTree) := rhoProd QTree
  have hopen : ∀ S ∈ { S : Set (ℕ → QTree) | ∃ n a : ℕ, 0 < a ∧ ∃ p : Fin n → QTree,
      (∀ i, qtreeTree2.QStar a (p i)) ∧ S = ICyl qtreeTree2 n (fun _ => a) p }, IsOpen S := by
    rintro _ ⟨n, a, _, p, _, rfl⟩
    exact (ICyl_clopen qtreeTree2 n (fun _ => a) p).1
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds hopen ?_
  intro x U hxU hU_open
  let : TopologicalSpace QTree := rho QTree
  obtain ⟨I, t, ht_all, htU⟩ := isOpen_pi_iff.mp hU_open x hxU
  let n : ℕ := I.sup id + 1
  have hcoord : ∀ i : Fin n, ∃ a : ℕ, 0 < a ∧ qtreeTree2.QStar a (x i.1) ∧
      (i.1 ∈ I → Set.Ico (x i.1) (qtreeTree2.child (x i.1) a) ⊆ t i.1) := by
    intro i
    by_cases hi : i.1 ∈ I
    · obtain ⟨S, ⟨a, ha, p, hp, rfl⟩, hxi, hSt⟩ :=
        qtree_I_isTopologicalBasis.exists_subset_of_mem_open (ht_all i.1 hi).2 (ht_all i.1 hi).1
      obtain ⟨b, hb, hxQ, hchild_lt⟩ := qtree_Ico_shrink hxi.2
      refine ⟨b, hb, hxQ, fun _ z hz => hSt ⟨le_trans hxi.1 hz.1, lt_trans hz.2 hchild_lt⟩⟩
    · obtain ⟨a₀, ha₀, hxQ⟩ := qtree_mem_QStar (x i.1)
      exact ⟨a₀, ha₀, hxQ a₀ le_rfl, fun h => (hi h).elim⟩
  choose a ha hxQ hsub using hcoord
  let A : ℕ := (Finset.univ : Finset (Fin n)).sup a + 1
  have hA : 0 < A := Nat.succ_pos _
  have hleA : ∀ i : Fin n, a i ≤ A := fun i =>
    le_trans (Finset.le_sup (f := a) (Finset.mem_univ i)) (Nat.le_succ _)
  let p : Fin n → QTree := fun i => x i.1
  have hpQ : ∀ i : Fin n, qtreeTree2.QStar A (p i) := fun i =>
    prop_2_2_2 qtreeTree2 (hleA i) (hxQ i)
  refine ⟨ICyl qtreeTree2 n (fun _ => A) p, ⟨n, A, hA, p, hpQ, rfl⟩, ?_, ?_⟩
  · intro i
    exact ⟨le_rfl, qtreeTree2.lt_child (x i.1) _ (qtreeTree2.C_child (x i.1) A hA)⟩
  · intro y hy
    refine htU fun k hkI => ?_
    have hkn : k < n := Nat.lt_succ_of_le (Finset.le_sup (f := id) hkI)
    let i : Fin n := ⟨k, hkn⟩
    have hyi : y k ∈ Set.Ico (x k) (qtreeTree2.child (x k) A) := hy i
    have hle_child : qtreeTree2.child (x k) A ≤ qtreeTree2.child (x k) (a i) := by
      rcases eq_or_lt_of_le (hleA i) with heq | hlt
      · rw [heq]
      · exact le_of_lt (qtreeTree2.child_anti (x k) _ _
          (qtreeTree2.C_child (x k) (a i) (ha i)) (qtreeTree2.C_child (x k) A hA)
          (by rw [qtreeTree2.idx_child, qtreeTree2.idx_child]; exact hlt))
    exact hsub i hkI ⟨hyi.1, lt_of_lt_of_le hyi.2 hle_child⟩

/-- Every point `x : ℕ → QTree` is the intersection of a decreasing sequence of
`rhoProd QTree`-clopen cylinder blocks `ICyl qtreeTree2 (n + 1) (fun _ => n + 1) (p n)`. -/
theorem qtree_rhoProd_inter_eq_singleton (x : ℕ → QTree) :
    ∃ C : ℕ → Set (ℕ → QTree),
      (∀ n, @IsOpen (ℕ → QTree) (rhoProd QTree) (C n) ∧
            @IsClosed (ℕ → QTree) (rhoProd QTree) (C n) ∧
            x ∈ C n ∧ C (n + 1) ⊆ C n) ∧
      (⋂ n : ℕ, C n) = {x} := by
  have huniq : ∀ n : ℕ, ∃ p : Fin (n + 1) → QTree,
      (∀ i, qtreeTree2.QStar (n + 1) (p i)) ∧ x ∈ ICyl qtreeTree2 (n + 1) (fun _ => n + 1) p := by
    intro n
    obtain ⟨⟨p, hp⟩, hxp, _⟩ :=
      (ICyl_coD qtreeTree2 (n + 1) (fun _ => n + 1) (fun _ => Nat.succ_pos n)).2.2 x
    exact ⟨p, hp, hxp⟩
  choose p hpQ hxp using huniq
  let C : ℕ → Set (ℕ → QTree) := fun n => ICyl qtreeTree2 (n + 1) (fun _ => n + 1) (p n)
  refine ⟨C, fun n => ⟨(ICyl_clopen qtreeTree2 _ _ _).1, (ICyl_clopen qtreeTree2 _ _ _).2,
    hxp n, ?_⟩, ?_⟩
  · intro y hy i
    let i' : Fin (n + 2) := ⟨i.1, Nat.lt_succ_of_lt i.2⟩
    have hxi : x i.1 ∈ Set.Ico (p n i) (qtreeTree2.child (p n i) (n + 1)) := hxp n i
    have hxi' : x i.1 ∈ Set.Ico (p (n + 1) i') (qtreeTree2.child (p (n + 1) i') (n + 2)) :=
      hxp (n + 1) i'
    rcases Defs.D_0005.prop_2_2_5 qtreeTree2 (Nat.succ_pos n) (Nat.le_succ (n + 1))
        (hpQ n i) (hpQ (n + 1) i') with hdisj | hsub
    · exact (Set.disjoint_left.mp hdisj hxi hxi').elim
    · exact hsub (hy i')
  · ext y
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro hy
      funext k
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · obtain ⟨a, ha, hyQ, hchild_lt⟩ := qtree_Ico_shrink hlt
        let n : ℕ := max k a
        have hkn : k < n + 1 := Nat.lt_succ_of_le (le_max_left k a)
        have han : a ≤ n + 1 := le_trans (le_max_right k a) (Nat.le_succ n)
        let i : Fin (n + 1) := ⟨k, hkn⟩
        have hy_in : y k ∈ Set.Ico (p n i) (qtreeTree2.child (p n i) (n + 1)) := hy n i
        have hx_in : x k ∈ Set.Ico (p n i) (qtreeTree2.child (p n i) (n + 1)) := hxp n i
        have hy_a : y k ∈ Set.Ico (y k) (qtreeTree2.child (y k) a) :=
          ⟨le_rfl, qtreeTree2.lt_child _ _ (qtreeTree2.C_child _ a ha)⟩
        rcases Defs.D_0005.prop_2_2_5 qtreeTree2 ha han hyQ (hpQ n i) with hdisj | hsub
        · exact Set.disjoint_left.mp hdisj hy_a hy_in
        · exact not_lt_of_ge (le_of_lt hchild_lt) (hsub hx_in).2
      · obtain ⟨a, ha, hxQ, hchild_lt⟩ := qtree_Ico_shrink hgt
        let n : ℕ := max k a
        have hkn : k < n + 1 := Nat.lt_succ_of_le (le_max_left k a)
        have han : a ≤ n + 1 := le_trans (le_max_right k a) (Nat.le_succ n)
        let i : Fin (n + 1) := ⟨k, hkn⟩
        have hy_in : y k ∈ Set.Ico (p n i) (qtreeTree2.child (p n i) (n + 1)) := hy n i
        have hx_in : x k ∈ Set.Ico (p n i) (qtreeTree2.child (p n i) (n + 1)) := hxp n i
        have hx_a : x k ∈ Set.Ico (x k) (qtreeTree2.child (x k) a) :=
          ⟨le_rfl, qtreeTree2.lt_child _ _ (qtreeTree2.C_child _ a ha)⟩
        rcases Defs.D_0005.prop_2_2_5 qtreeTree2 ha han hxQ (hpQ n i) with hdisj | hsub
        · exact Set.disjoint_left.mp hdisj hx_a hx_in
        · exact not_lt_of_ge (le_of_lt hchild_lt) (hsub hy_in).2
    · rintro rfl n
      exact hxp n

end QTreeBasisAndShrinking

section CanonicalEnvelope

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0009

variable {α : Type} [LinearOrder α]

/-- Canonical `ICyl` parameter for `H q n c` at refinement level `max n (c + 1) > 0`. -/
noncomputable def envP (T : Tree2 α) (q : ℕ ≃ α) (n : ℕ) (hn : 0 < n) (c : ℕ) :
    { p : Fin n → α // ∀ i, T.QStar (max n (c + 1)) (p i) } :=
  Classical.choose (H_subset_unique_ICyl T q hn (fun _ => max n (c + 1))
    (fun _ => lt_of_lt_of_le (Nat.succ_pos c) (le_max_right n (c + 1))) c)

/-- Canonical `ICyl` envelope of `H q n c` in `(ℕ → α, rhoProd α)`. -/
noncomputable def Env (T : Tree2 α) (q : ℕ ≃ α) (n : ℕ) (hn : 0 < n) (c : ℕ) : Set (ℕ → α) :=
  ICyl T n (fun _ => max n (c + 1)) (envP T q n hn c).1

/-- Every `H q n c` is contained in its canonical `ICyl` envelope `Env T q n hn c`. -/
theorem H_subset_Env (T : Tree2 α) (q : ℕ ≃ α) (n : ℕ) (hn : 0 < n) (c : ℕ) :
    H q n c ⊆ Env T q n hn c :=
  (Classical.choose_spec (H_subset_unique_ICyl T q hn (fun _ => max n (c + 1))
    (fun _ => lt_of_lt_of_le (Nat.succ_pos c) (le_max_right n (c + 1))) c)).1

/-- Every canonical envelope `Env T q n hn c` is clopen in `rhoProd α` (and hence in `xtop α`). -/
theorem Env_clopen [NoMaxOrder α] (T : Tree2 α) (q : ℕ ≃ α) (n : ℕ) (hn : 0 < n) (c : ℕ) :
    @IsOpen (ℕ → α) (rhoProd α) (Env T q n hn c) ∧
    @IsClosed (ℕ → α) (rhoProd α) (Env T q n hn c) :=
  ICyl_clopen T n (fun _ => max n (c + 1)) (envP T q n hn c).1

/-- **Envelope Monotonicity (Proposition 3.1.4 + Proposition 2.2.5):**
Whenever `H q n' c' ⊆ H q n c`, the canonical `ICyl` envelopes satisfy
`Env T q n' hn' c' ⊆ Env T q n hn c`. -/
theorem Env_mono_of_H_subset (T : Tree2 α) (q : ℕ ≃ α) (hα : ∃ a b : α, a ≠ b)
    {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n') {c c' : ℕ}
    (hsub : H q n' c' ⊆ H q n c) :
    Env T q n' hn' c' ⊆ Env T q n hn c := by
  obtain ⟨hnn, hcc⟩ := H_sub_index q hα hn hn' hsub
  obtain ⟨x₀, hx₀'⟩ := H_nonempty q n' hn' c'
  have hx₀ : x₀ ∈ H q n c := hsub hx₀'
  have hx₀E : x₀ ∈ Env T q n hn c := H_subset_Env T q n hn c hx₀
  have hx₀E' : x₀ ∈ Env T q n' hn' c' := H_subset_Env T q n' hn' c' hx₀'
  have ha : 0 < max n (c + 1) := lt_of_lt_of_le (Nat.succ_pos c) (le_max_right n (c + 1))
  have hab : max n (c + 1) ≤ max n' (c' + 1) := max_le_max hnn (Nat.succ_le_succ hcc)
  intro y hy i
  let i' : Fin n' := ⟨i.1, lt_of_lt_of_le i.2 hnn⟩
  rcases Defs.D_0005.prop_2_2_5 T ha hab ((envP T q n hn c).2 i) ((envP T q n' hn' c').2 i') with
    hdisj | hIsub
  · exact (Set.disjoint_left.mp hdisj (hx₀E i) (hx₀E' i')).elim
  · exact hIsub (hy i')

/-- Parent-child monotonicity of canonical envelopes along `delta c j`. -/
theorem Env_succ_subset (T : Tree2 α) (q : ℕ ≃ α) (hα : ∃ a b : α, a ≠ b)
    {n : ℕ} (hn : 0 < n) (c j : ℕ) :
    Env T q (n + 1) (Nat.succ_pos n) (delta c j) ⊆ Env T q n hn c :=
  Env_mono_of_H_subset T q hα hn (Nat.succ_pos n) (H_succ_sub q n hn c j)

/-- On `QTree`, the canonical envelopes along any point `x : ℕ → QTree` shrink to `{x}`. -/
theorem qtree_Env_inter_eq_singleton (q : ℕ ≃ QTree) (x : ℕ → QTree) :
    (⋂ n : ℕ, Env qtreeTree2 q (n + 1) (Nat.succ_pos n)
      (code (n + 1) (fun k => q.symm (x k)))) = {x} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro hy
    funext k
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨a, ha, hyQ, hchild_lt⟩ := qtree_Ico_shrink hlt
      let n : ℕ := max k a
      let c : ℕ := code (n + 1) (fun j => q.symm (x j))
      have hkn : k < n + 1 := Nat.lt_succ_of_le (le_max_left k a)
      have han : a ≤ max (n + 1) (c + 1) :=
        le_trans (le_trans (le_max_right k a) (Nat.le_succ n)) (le_max_left _ _)
      let i : Fin (n + 1) := ⟨k, hkn⟩
      have hx_in : x k ∈ Set.Ico ((envP qtreeTree2 q (n + 1) (Nat.succ_pos n) c).1 i)
          (qtreeTree2.child ((envP qtreeTree2 q (n + 1) (Nat.succ_pos n) c).1 i) (max (n + 1) (c + 1))) :=
        H_subset_Env qtreeTree2 q (n + 1) (Nat.succ_pos n) c rfl i
      have hy_in : y k ∈ Set.Ico ((envP qtreeTree2 q (n + 1) (Nat.succ_pos n) c).1 i)
          (qtreeTree2.child ((envP qtreeTree2 q (n + 1) (Nat.succ_pos n) c).1 i) (max (n + 1) (c + 1))) :=
        hy n i
      have hy_a : y k ∈ Set.Ico (y k) (qtreeTree2.child (y k) a) :=
        ⟨le_rfl, qtreeTree2.lt_child _ _ (qtreeTree2.C_child _ a ha)⟩
      rcases Defs.D_0005.prop_2_2_5 qtreeTree2 ha han hyQ
          ((envP qtreeTree2 q (n + 1) (Nat.succ_pos n) c).2 i) with hdisj | hIsub
      · exact Set.disjoint_left.mp hdisj hy_a hy_in
      · exact not_lt_of_ge (le_of_lt hchild_lt) (hIsub hx_in).2
    · obtain ⟨a, ha, hxQ, hchild_lt⟩ := qtree_Ico_shrink hgt
      let n : ℕ := max k a
      let c : ℕ := code (n + 1) (fun j => q.symm (x j))
      have hkn : k < n + 1 := Nat.lt_succ_of_le (le_max_left k a)
      have han : a ≤ max (n + 1) (c + 1) :=
        le_trans (le_trans (le_max_right k a) (Nat.le_succ n)) (le_max_left _ _)
      let i : Fin (n + 1) := ⟨k, hkn⟩
      have hx_in : x k ∈ Set.Ico ((envP qtreeTree2 q (n + 1) (Nat.succ_pos n) c).1 i)
          (qtreeTree2.child ((envP qtreeTree2 q (n + 1) (Nat.succ_pos n) c).1 i) (max (n + 1) (c + 1))) :=
        H_subset_Env qtreeTree2 q (n + 1) (Nat.succ_pos n) c rfl i
      have hy_in : y k ∈ Set.Ico ((envP qtreeTree2 q (n + 1) (Nat.succ_pos n) c).1 i)
          (qtreeTree2.child ((envP qtreeTree2 q (n + 1) (Nat.succ_pos n) c).1 i) (max (n + 1) (c + 1))) :=
        hy n i
      have hx_a : x k ∈ Set.Ico (x k) (qtreeTree2.child (x k) a) :=
        ⟨le_rfl, qtreeTree2.lt_child _ _ (qtreeTree2.C_child _ a ha)⟩
      rcases Defs.D_0005.prop_2_2_5 qtreeTree2 ha han hxQ
          ((envP qtreeTree2 q (n + 1) (Nat.succ_pos n) c).2 i) with hdisj | hIsub
      · exact Set.disjoint_left.mp hdisj hx_a hx_in
      · exact not_lt_of_ge (le_of_lt hchild_lt) (hIsub hy_in).2
  · rintro rfl n
    exact H_subset_Env qtreeTree2 q (n + 1) (Nat.succ_pos n) _ rfl

end CanonicalEnvelope

end Research.ChenWangTree
