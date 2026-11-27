import Mathlib.Data.PNat.Basic
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Defs.D_0013

/-!
# Vacuity of `Defs.D_0013.Compat` and Repaired Realization on `QTree`

This standalone file establishes two results about the tree–enumeration compatibility
axioms in `Defs.D_0013` (Chen–Wang Proposition 3.2.1):

1. **Vacuity (Off-by-one bug in `Defs.D_0013.Compat`)**:
   `compat_not_exists` proves that for **every** linear order `α`, every
   `T : Defs.D_0003.Tree2 α`, and every bijection `q : ℕ ≃ α`,
   `¬ Defs.D_0013.Compat q T`.
   The reason is a 1-indexed vs. 0-indexed mismatch: `q 0` must be `T.root`
   (by `num_child` + `T.connected`), and `q 1` must be a descendant of some
   `T.child T.root j` with `j ≥ 1`, forcing `1 ≤ j < q.symm (T.child T.root j) ≤ 1`.

2. **Repaired Compatibility (`CompatRepaired`) & Concrete Witness on `QTree`**:
   Replacing the strict inequality `j < q.symm (T.child p j)` in `idx_lt_num`
   with the non-strict `j ≤ q.symm (T.child p j)` (`idx_le_num`, corresponding
   to `j < q.symm (T.child p j) + 1` in 1-based numbering):
   - preserves the **exact same conclusion** of Proposition 3.2.1
     (`prop_3_2_1_repaired`);
   - admits a concrete, kernel-verified witness `(QTree, qtreeTree2, qtreeEnum)`
     (`exists_compatRepaired_qtree`), constructed via the weight-graded order
     `qweight u = ∑ x ∈ u, (ofDual x).1`.
-/

namespace Research.ChenWangCompat

open Relation
open Defs.D_0003 Defs.D_0013

/-! ## Part 1: `Defs.D_0013.Compat` is unsatisfiable -/

/-- `Defs.D_0013.Compat q T` is vacuously false for every `α`, `T : Tree2 α`, and `q : ℕ ≃ α`,
due to the 0-indexed vs. 1-indexed off-by-one in `idx_lt_num`. -/
theorem compat_not_exists {α : Type} [LinearOrder α]
    (q : ℕ ≃ α) (T : Tree2 α) : ¬ Defs.D_0013.Compat q T := by
  intro hc
  let x : α := q 1
  have hx : q.symm x = 1 := q.symm_apply_apply 1
  have hconn : ReflTransGen T.C T.root x := T.connected x
  rcases ReflTransGen.cases_head hconn with hroot | ⟨c, hCc, hcx⟩
  · have h0 : q.symm T.root ≤ q.symm (q 0) :=
      Defs.D_0013.num_desc_le hc (T.connected (q 0))
    rw [q.symm_apply_apply 0, hroot, hx] at h0
    omega
  · let j : ℕ := T.idx c
    have hj : 0 < j := T.idx_pos T.root c hCc
    have hc_eq : c = T.child T.root j :=
      T.child_inj T.root c (T.child T.root j) hCc (T.C_child T.root j hj)
        (T.idx_child T.root j).symm
    have hlt : j < q.symm c := by
      rw [hc_eq]
      exact hc.idx_lt_num T.root j hj
    have hle : q.symm c ≤ q.symm x := Defs.D_0013.num_desc_le hc hcx
    omega

/-! ## Part 2: Repaired compatibility axioms and Proposition 3.2.1 -/

/-- Repaired 0-indexed compatibility axioms for `(q : ℕ ≃ α, T : Tree2 α)`:
`idx_lt_num` (`j < q.symm (T.child p j)`) is relaxed to `idx_le_num`
(`j ≤ q.symm (T.child p j)`), i.e., `j < q.symm (T.child p j) + 1`. -/
structure CompatRepaired {α : Type} [LinearOrder α] (q : ℕ ≃ α) (T : Tree2 α) : Prop where
  num_child : ∀ p c, T.C p c → q.symm p < q.symm c
  idx_le_num : ∀ p j, 0 < j → j ≤ q.symm (T.child p j)
  desc_of_mem : ∀ p r, p < r → r < T.child p 1 →
    ∃ l, 0 < l ∧ ReflTransGen T.C (T.child p l) r
  shrink : ∀ p u, p < u → ∃ a, 0 < a ∧ T.child p a < u

theorem num_desc_le_repaired {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}
    (hc : CompatRepaired q T) {y r : α} (h : ReflTransGen T.C y r) :
    q.symm y ≤ q.symm r := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (hc.num_child _ _ hbc).le

/-- Chen–Wang Proposition 3.2.1 holds with the exact same conclusion under `CompatRepaired`. -/
theorem prop_3_2_1_repaired {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}
    (hc : CompatRepaired q T) {a : ℕ} (ha : 0 < a) {p r : α}
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
  have hnum := num_desc_le_repaired hc hd
  refine ⟨lt_of_lt_of_le (hc.num_child p _ (T.C_child p l hl0)) hnum,
    lt_of_lt_of_le (lt_of_lt_of_le hal (hc.idx_le_num p l hl0)) hnum, ?_⟩
  intro b hb x hx
  have hd' : ReflTransGen T.C (T.child p l) (T.child r b) := hd.tail (T.C_child r b hb)
  exact ⟨lt_of_lt_of_le h1 hx.1, lt_trans hx.2 (Defs.D_0013.desc_lt_child T ha hal hd')⟩

/-! ## Part 3: Concrete `Tree2` on `QTree := List (OrderDual ℕ+)` -/

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
      | rel hab => exact List.Lex.rel hab
      | cons htail => exact List.Lex.cons (ih htail (by simpa using hlen))

private lemma list_lex_append_lt_append {α : Type*} [LinearOrder α]
    (p : List α) {x y : α} (hxy : x < y) (t : List α) :
    p ++ (x :: t) < p ++ [y] := by
  induction p with
  | nil => exact List.Lex.rel hxy
  | cons a as ih => exact List.Lex.cons ih

private lemma list_lex_append_lt_of_not_prefix {α : Type*} [LinearOrder α]
    {x y : List α} (hxy : x < y) (hnot : ¬ x <+: y) (t : List α) :
    x ++ t < y := by
  induction x generalizing y with
  | nil => exact (hnot List.nil_prefix).elim
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

/-- The `j`-th child of `p` in `QTree` (for `j ≥ 1`; `[]` for `j = 0`). -/
def qchild (p : QTree) (j : ℕ) : QTree :=
  if h : 0 < j then p ++ [OrderDual.toDual ⟨j, h⟩] else []

/-- Child relation `C p c` on `QTree`. -/
def qC (p c : QTree) : Prop :=
  ∃ j : ℕ, 0 < j ∧ c = qchild p j

/-- Index of a node in `QTree` (last coordinate, 0 for root `[]`). -/
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

private lemma qC_prefix_desc {p r : QTree} (h : ReflTransGen qC p r) : p <+: r := by
  induction h with
  | refl => exact List.prefix_rfl
  | tail _ hbc ih =>
    obtain ⟨j, hj, rfl⟩ := hbc
    rw [qchild_pos _ hj]
    exact ih.trans (List.prefix_append _ _)

/-- Concrete realization of `Defs.D_0003.Tree2` on `QTree`. -/
def qtreeTree2 : Tree2 QTree where
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
    exact lt_asymm (list_lex_lt_of_prefix_of_len _ h1 hlev) h2
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

/-! ## Part 4: Weight-graded enumeration `qtreeEnum : ℕ ≃ QTree` -/

/-- Sum of positive-integer entries of a `QTree` node. -/
def qweight (u : QTree) : ℕ :=
  (u.map (fun x => (OrderDual.ofDual x).1)).sum

private lemma qweight_cons (x : OrderDual ℕ+) (xs : QTree) :
    qweight (x :: xs) = (OrderDual.ofDual x).1 + qweight xs := rfl

private lemma qweight_append (u v : QTree) :
    qweight (u ++ v) = qweight u + qweight v := by
  simp [qweight, List.map_append, List.sum_append]

private lemma qweight_qchild (p : QTree) {j : ℕ} (hj : 0 < j) :
    qweight (qchild p j) = qweight p + j := by
  simp [qchild, hj, qweight]
  rfl

private lemma qweight_replicate_one (m : ℕ) :
    qweight (List.replicate m (OrderDual.toDual (1 : ℕ+))) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, qweight_cons, ih]
    change 1 + m = m + 1
    omega

private lemma length_le_qweight (u : QTree) : u.length ≤ qweight u := by
  induction u with
  | nil => simp [qweight]
  | cons x xs ih =>
    rw [List.length_cons, qweight_cons]
    have hx : 1 ≤ (OrderDual.ofDual x).1 := (OrderDual.ofDual x).2
    omega

private lemma mem_le_qweight {u : QTree} {x : OrderDual ℕ+} (hx : x ∈ u) :
    (OrderDual.ofDual x).1 ≤ qweight u := by
  induction u with
  | nil => cases hx
  | cons a as ih =>
    rw [qweight_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · omega
    · exact le_trans (ih hmem) (Nat.le_add_left _ _)

/-- Weight-graded strict linear order on `QTree`. -/
def qLt (u v : QTree) : Prop :=
  qweight u < qweight v ∨ (qweight u = qweight v ∧ u < v)

private lemma qLt_irrefl (u : QTree) : ¬ qLt u u := by
  rintro (h | ⟨_, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

private lemma qLt_trans {u v w : QTree} (h1 : qLt u v) (h2 : qLt v w) : qLt u w := by
  rcases h1 with h1 | ⟨he1, hl1⟩
  · rcases h2 with h2 | ⟨he2, _⟩
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl (he2 ▸ h1)
  · rcases h2 with h2 | ⟨he2, hl2⟩
    · exact Or.inl (he1.symm ▸ h2)
    · exact Or.inr ⟨he1.trans he2, lt_trans hl1 hl2⟩

private lemma qLt_trichotomous (u v : QTree) : qLt u v ∨ u = v ∨ qLt v u := by
  rcases lt_trichotomy (qweight u) (qweight v) with h | he | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy u v with hl | rfl | hl
    · exact Or.inl (Or.inr ⟨he, hl⟩)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr ⟨he.symm, hl⟩))
  · exact Or.inr (Or.inr (Or.inl h))

private lemma finite_bounded_entries (k : ℕ) :
    { x : OrderDual ℕ+ | (OrderDual.ofDual x).1 ≤ k }.Finite := by
  refine Set.Finite.of_finite_image (f := fun x : OrderDual ℕ+ => (OrderDual.ofDual x).1) ?_ ?_
  · refine (Finset.range (k + 1)).finite_toSet.subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hx))
  · intro x _ y _ hxy
    apply OrderDual.ofDual.injective
    exact Subtype.ext hxy

private lemma finite_bounded_len_entries (k : ℕ) :
    ∀ n : ℕ, { v : QTree | v.length ≤ n ∧ ∀ x ∈ v, (OrderDual.ofDual x).1 ≤ k }.Finite
  | 0 => by
    refine (Set.finite_singleton ([] : QTree)).subset ?_
    intro v ⟨hlen, _⟩
    exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
  | n + 1 => by
    have ih := finite_bounded_len_entries k n
    let A : Set (OrderDual ℕ+) := { x | (OrderDual.ofDual x).1 ≤ k }
    let S : Set QTree := { v | v.length ≤ n ∧ ∀ x ∈ v, (OrderDual.ofDual x).1 ≤ k }
    have hfin : ({([] : QTree)} ∪ (⋃ x ∈ A, (List.cons x) '' S)).Finite :=
      (Set.finite_singleton _).union ((finite_bounded_entries k).biUnion fun x _ => ih.image _)
    refine hfin.subset ?_
    intro v ⟨hlen, hmem⟩
    cases v with
    | nil => exact Or.inl rfl
    | cons a as =>
      refine Or.inr (Set.mem_iUnion₂.mpr ⟨a, hmem a List.mem_cons_self, as, ⟨?_, ?_⟩, rfl⟩)
      · exact Nat.le_of_succ_le_succ hlen
      · intro x hx
        exact hmem x (List.mem_cons_of_mem a hx)

private lemma finite_qweight_le (k : ℕ) : { v : QTree | qweight v ≤ k }.Finite := by
  refine (finite_bounded_len_entries k k).subset ?_
  intro v hv
  exact ⟨le_trans (length_le_qweight v) hv, fun x hx => le_trans (mem_le_qweight hx) hv⟩

/-- Initial segment of `QTree` strictly below `u` in `qLt`. -/
def predSet (u : QTree) : Set QTree := { v : QTree | qLt v u }

private lemma predSet_finite (u : QTree) : (predSet u).Finite := by
  refine (finite_qweight_le (qweight u)).subset ?_
  rintro v (h | ⟨h, _⟩)
  · exact le_of_lt h
  · exact le_of_eq h

/-- Rank of `u : QTree` in the weight-graded order `qLt`. -/
noncomputable def qrank (u : QTree) : ℕ :=
  (predSet_finite u).toFinset.card

private lemma qrank_strictMono {u v : QTree} (h : qLt u v) : qrank u < qrank v := by
  unfold qrank
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [Set.Finite.mem_toFinset] at hw ⊢
    exact qLt_trans hw h
  · intro heq
    have hu_in : u ∈ (predSet_finite v).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact h
    rw [← heq, Set.Finite.mem_toFinset] at hu_in
    exact qLt_irrefl u hu_in

private lemma qrank_injective : Function.Injective qrank := by
  intro u v h
  rcases qLt_trichotomous u v with hlt | heq | hgt
  · exact absurd h (ne_of_lt (qrank_strictMono hlt))
  · exact heq
  · exact absurd h (ne_of_gt (qrank_strictMono hgt))

private lemma le_qrank_of_le_qweight {u : QTree} {m : ℕ} (hm : m ≤ qweight u) :
    m ≤ qrank u := by
  classical
  let f : ℕ → QTree := fun i => List.replicate i (OrderDual.toDual (1 : ℕ+))
  have hf_inj : Set.InjOn f (Finset.range m : Set ℕ) := by
    intro i _ j _ hij
    have := congrArg List.length hij
    simpa [f] using this
  have hf_sub : (Finset.range m).image f ⊆ (predSet_finite u).toFinset := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    rw [Set.Finite.mem_toFinset]
    refine Or.inl ?_
    rw [qweight_replicate_one]
    exact lt_of_lt_of_le (Finset.mem_range.mp hi) hm
  calc
    m = (Finset.range m).card := (Finset.card_range m).symm
    _ = ((Finset.range m).image f).card := (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ (predSet_finite u).toFinset.card := Finset.card_le_card hf_sub

private lemma qrank_surjective : Function.Surjective qrank := by
  classical
  intro n
  let u : QTree := List.replicate (n + 1) (OrderDual.toDual (1 : ℕ+))
  have hnu : n < qrank u := by
    have hle : n + 1 ≤ qrank u := le_qrank_of_le_qweight (by rw [qweight_replicate_one])
    omega
  have himg_sub : (predSet_finite u).toFinset.image qrank ⊆ Finset.range (qrank u) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨v, hv, rfl⟩
    rw [Set.Finite.mem_toFinset] at hv
    exact Finset.mem_range.mpr (qrank_strictMono hv)
  have himg_card : ((predSet_finite u).toFinset.image qrank).card = (Finset.range (qrank u)).card := by
    rw [Finset.card_image_of_injective _ qrank_injective, Finset.card_range]
    rfl
  have himg_eq : (predSet_finite u).toFinset.image qrank = Finset.range (qrank u) :=
    Finset.eq_of_subset_of_card_le himg_sub (le_of_eq himg_card.symm)
  have hn_mem : n ∈ (predSet_finite u).toFinset.image qrank := by
    rw [himg_eq]
    exact Finset.mem_range.mpr hnu
  rcases Finset.mem_image.mp hn_mem with ⟨v, _, hv⟩
  exact ⟨v, hv⟩

/-- The weight-graded bijection `ℕ ≃ QTree`. -/
noncomputable def qtreeEnum : ℕ ≃ QTree :=
  (Equiv.ofBijective qrank ⟨qrank_injective, qrank_surjective⟩).symm

private lemma qtreeEnum_symm_eq (u : QTree) : qtreeEnum.symm u = qrank u := rfl

private lemma qC_desc_of_append (u rest : QTree) :
    ReflTransGen qtreeTree2.C u (u ++ rest) := by
  induction rest using List.reverseRecOn with
  | nil =>
    simpa using ReflTransGen.refl
  | append_singleton xs d ih =>
    rw [← List.append_assoc]
    refine ih.tail ⟨(OrderDual.ofDual d).1, (OrderDual.ofDual d).2, ?_⟩
    rw [qchild_pos _ (OrderDual.ofDual d).2]
    rfl

/-- `qtreeEnum` satisfies all four axioms of `CompatRepaired` with `qtreeTree2`. -/
theorem qtreeEnum_compatRepaired : CompatRepaired qtreeEnum qtreeTree2 where
  num_child := by
    rintro p c ⟨j, hj, rfl⟩
    rw [qtreeEnum_symm_eq, qtreeEnum_symm_eq]
    refine qrank_strictMono (Or.inl ?_)
    rw [qweight_qchild p hj]
    omega
  idx_le_num := by
    intro p j hj
    rw [qtreeEnum_symm_eq]
    refine le_qrank_of_le_qweight ?_
    change j ≤ qweight (qchild p j)
    rw [qweight_qchild p hj]
    omega
  desc_of_mem := by
    intro p r hpr hr1
    have hpre : p <+: r := by
      by_contra hnot
      have hlt : qtreeTree2.child p 1 < r := by
        change qchild p 1 < r
        rw [qchild_pos p Nat.one_pos]
        exact list_lex_append_lt_of_not_prefix hpr hnot _
      exact lt_asymm hlt hr1
    obtain ⟨t, rfl⟩ := hpre
    cases t with
    | nil => simp at hpr
    | cons d rest =>
      let l : ℕ := (OrderDual.ofDual d).1
      have hl : 0 < l := (OrderDual.ofDual d).2
      refine ⟨l, hl, ?_⟩
      have hch : qtreeTree2.child p l = p ++ [d] := by
        change qchild p l = p ++ [d]
        rw [qchild_pos p hl]
        rfl
      rw [hch]
      simpa [List.append_assoc] using qC_desc_of_append (p ++ [d]) rest
  shrink := by
    intro p u hpu
    by_cases hpre : p <+: u
    · obtain ⟨t, rfl⟩ := hpre
      cases t with
      | nil => simp at hpu
      | cons d rest =>
        let k : ℕ := (OrderDual.ofDual d).1
        refine ⟨k + 1, Nat.succ_pos k, ?_⟩
        change qchild p (k + 1) < p ++ d :: rest
        rw [qchild_pos p (Nat.succ_pos k)]
        have hdual : OrderDual.toDual (⟨k + 1, Nat.succ_pos k⟩ : ℕ+) < d := Nat.lt_succ_self k
        have hgen : ∀ l : QTree, l ++ [OrderDual.toDual ⟨k + 1, Nat.succ_pos k⟩] < l ++ d :: rest := by
          intro l
          induction l with
          | nil => exact List.Lex.rel hdual
          | cons b bs ih => exact List.Lex.cons ih
        exact hgen p
    · refine ⟨1, Nat.one_pos, ?_⟩
      change qchild p 1 < u
      rw [qchild_pos p Nat.one_pos]
      exact list_lex_append_lt_of_not_prefix hpu hpre _

/-- Concrete existence of a `CompatRepaired` enumeration on `QTree`. -/
theorem exists_compatRepaired_qtree :
    ∃ q : ℕ ≃ QTree, CompatRepaired q qtreeTree2 :=
  ⟨qtreeEnum, qtreeEnum_compatRepaired⟩

end Research.ChenWangCompat
