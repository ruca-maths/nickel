import Mathlib.Order.Interval.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Topology.Constructions
import Mathlib.Data.PNat.Basic
import Mathlib.Data.List.Lex
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Count
import Defs.D_0003
import Defs.D_0005
import Defs.D_0007
import Defs.D_0009
import Defs.D_0011

/-!
# Chen–Wang (arXiv:1809.03763v2) Section 3.2: Tree2–Enumeration Compatibility, Construction 3.2, and Proposition 3.2

This file formalizes the two missing Section 3.2 prerequisites noted by `architect-1` on `L_0031`,
built directly on top of `Defs.D_0002`–`Defs.D_0011` (zero `sorry`, standard axioms only):

1. **`Tree2Enum T q`**: Compatibility axioms between `T : Defs.D_0003.Tree2 α` and an enumeration
   `q : ℕ ≃ α` (corresponding to Proposition 2.1.1 and 2.1.3 of Chen–Wang):
   - `child_enum_gt`: every child has a strictly larger index than its parent;
   - `idx_le_enum`: every child's local child-index is at most its global enumeration index.
   From these two axioms alone we prove all three parts of **Proposition 3.2**:
   - `prop_3_2_1`: `q j ∈ (q i, child (q i) a) → i < j ∧ a < j ∧ [q j, child (q j) b) ⊆ (q i, child (q i) a)`;
   - `prop_3_2_2`: `q j ∉ [q i, child (q i) a) → i < j → Disjoint [q i, child (q i) a) [q j, child (q j) b)`;
   - `prop_3_2_3`: laminar property for `[q i, child (q i) a)` and `[q j, child (q j) b)` when `i < a ≤ b`.

2. **Construction 3.2 (`I`, `J`, `H_sub`, `g_sub`, `H_x`, `g_x`)** on `(ℕ → α, Defs.D_0011.xtop α)`:
   - For `n ≥ 1`, `c : ℕ` (0-indexed; paper's `i = c + 1`), set `a = n + c + 1`.
   - `I T q n c`: first-`n`-coordinate interval block `[p_k, child p_k a)` around the prefix of `H q n c`.
   - `J T n c r`: next-`(c + 1)`-coordinate interval block `[r j, child (r j) a)` (`r j ∈ QStar a`).
   - `H_sub T q n c r := H q n c ∩ J T n c r` and `g_sub T q n c r := I T q n c ∩ J T n c r`.
   - Pointwise `H_x T q n x` and `g_x T q n x` (Notes D1, D2, D4):
     partition of `H q n c`, `g_x ∩ H = H_x`, clopenness in `Defs.D_0011.xtop α`,
     invariance on `H_x`, and `⋂ n, H_x T q (n + 1) x = {x}`.
-/

namespace Research.ChenWangSec32

open Relation Set
open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0005 Defs.D_0007 Defs.D_0009 Defs.D_0011

section Prop32

variable {α : Type} [LinearOrder α]

/-- Compatibility between a `Tree2 α` and an enumeration `q : ℕ ≃ α` (Chen–Wang Prop 2.1.1 & 2.1.3). -/
structure Tree2Enum (T : Tree2 α) (q : ℕ ≃ α) : Prop where
  child_enum_gt : ∀ p c, T.C p c → q.symm p < q.symm c
  idx_le_enum : ∀ p c, T.C p c → T.idx c ≤ q.symm c

/-- Enumeration index is monotone along the descendant relation `ReflTransGen T.C`. -/
theorem enum_le_of_desc {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {p y : α} (h : ReflTransGen T.C p y) : q.symm p ≤ q.symm y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (E.child_enum_gt _ _ hbc).le

/-- Any `y ∈ (p, child p a)` (`a > 0`) is a descendant of `child p l` for some `l > a`. -/
theorem exists_child_desc_of_mem_Ioo (T : Tree2 α) {a : ℕ} (ha : 0 < a) {p y : α}
    (hy : y ∈ Set.Ioo p (T.child p a)) :
    ∃ l, a < l ∧ ReflTransGen T.C (T.child p l) y := by
  have aux : ∀ r, ReflTransGen T.C T.root r → p < r → r < T.child p a →
      ∃ c, T.C p c ∧ ReflTransGen T.C c r := by
    intro r hr
    induction hr with
    | refl =>
      intro hpr _
      exact absurd (T.root_le p) (not_le.mpr hpr)
    | @tail b c hrb hbc ih =>
      intro hpc hca
      rcases lt_trichotomy b p with hbp | rfl | hpb
      · -- `b < p < c < child p a` contradicts `gap`
        have hlev : T.lev b < T.lev p := by
          by_contra hnot
          exact T.gap b c p hbc (not_lt.mp hnot) ⟨hbp, hpc⟩
        have hlevc : T.lev c ≤ T.lev p := by
          have := T.lev_child b c hbc
          omega
        exact absurd ⟨hpc, hca⟩ (T.gap p (T.child p a) c (T.C_child p a ha) hlevc)
      · exact ⟨c, hbc, ReflTransGen.refl⟩
      · have hba : b < T.child p a := lt_trans (T.lt_child b c hbc) hca
        obtain ⟨c₀, hpc₀, hc₀b⟩ := ih hpb hba
        exact ⟨c₀, hpc₀, hc₀b.tail hbc⟩
  obtain ⟨c, hpc, hcy⟩ := aux y (T.connected y) hy.1 hy.2
  have hl : a < T.idx c := by
    by_contra hnot
    have hle : T.idx c ≤ a := not_lt.mp hnot
    have h1 : T.child p a ≤ T.child p (T.idx c) :=
      child_le_child T p (T.idx_pos p c hpc) hle
    rw [child_eq T hpc] at h1
    exact absurd (lt_of_le_of_lt (le_trans h1 (desc_le T hcy)) hy.2) (lt_irrefl _)
  refine ⟨T.idx c, hl, ?_⟩
  rwa [child_eq T hpc]

/-- Chen–Wang Proposition 3.2.1:
If `q j ∈ (q i, child (q i) a)` (`a > 0`, `b > 0`), then `i < j`, `a < j`, and
`[q j, child (q j) b) ⊆ (q i, child (q i) a)`. -/
theorem prop_3_2_1 {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {i j a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hmem : q j ∈ Set.Ioo (q i) (T.child (q i) a)) :
    i < j ∧ a < j ∧ Set.Ico (q j) (T.child (q j) b) ⊆ Set.Ioo (q i) (T.child (q i) a) := by
  obtain ⟨l, hal, hdesc⟩ := exists_child_desc_of_mem_Ioo T ha hmem
  have hcl : T.C (q i) (T.child (q i) l) := T.C_child (q i) l (by omega)
  have hle_j : q.symm (T.child (q i) l) ≤ j := by
    simpa only [Equiv.symm_apply_apply] using enum_le_of_desc E hdesc
  have hij : i < j := by
    have h1 : i < q.symm (T.child (q i) l) := by
      simpa only [Equiv.symm_apply_apply] using E.child_enum_gt (q i) (T.child (q i) l) hcl
    exact lt_of_lt_of_le h1 hle_j
  have haj : a < j := by
    have h1 : l ≤ q.symm (T.child (q i) l) := by
      have := E.idx_le_enum (q i) (T.child (q i) l) hcl
      rwa [T.idx_child] at this
    exact lt_of_lt_of_le hal (le_trans h1 hle_j)
  refine ⟨hij, haj, ?_⟩
  intro z hz
  refine ⟨lt_of_lt_of_le hmem.1 hz.1, ?_⟩
  have hz1 : z < T.child (q j) 1 :=
    lt_of_lt_of_le hz.2 (child_le_child T (q j) Nat.one_pos hb)
  have hdesc1 : ReflTransGen T.C (T.child (q i) l) (T.child (q j) 1) :=
    hdesc.tail (T.C_child (q j) 1 Nat.one_pos)
  have hl' : l = (l - 1) + 1 := by omega
  rw [hl'] at hdesc1
  have hlt1 : T.child (q j) 1 < T.child (q i) (l - 1) :=
    T.desc_lt (q i) (l - 1) (T.child (q j) 1) (by omega) hdesc1
  exact lt_trans hz1 (lt_of_lt_of_le hlt1 (child_le_child T (q i) ha (by omega)))

/-- Chen–Wang Proposition 3.2.2:
If `q j ∉ [q i, child (q i) a)` and `i < j` (`a, b > 0`), then
`[q i, child (q i) a)` and `[q j, child (q j) b)` are disjoint. -/
theorem prop_3_2_2 {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {i j a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hnot : q j ∉ Set.Ico (q i) (T.child (q i) a)) (hij : i < j) :
    Disjoint (Set.Ico (q i) (T.child (q i) a)) (Set.Ico (q j) (T.child (q j) b)) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  rcases lt_or_ge (q j) (q i) with hji | hij_le
  · have hqi_mem : q i ∈ Set.Ioo (q j) (T.child (q j) b) :=
      ⟨hji, lt_of_le_of_lt hxi.1 hxj.2⟩
    have hlt := (prop_3_2_1 E hb ha hqi_mem).1
    omega
  · have hle : T.child (q i) a ≤ q j := by
      by_contra hlt
      exact hnot ⟨hij_le, not_le.mp hlt⟩
    exact absurd (lt_of_lt_of_le hxi.2 (le_trans hle hxj.1)) (lt_irrefl _)

/-- Chen–Wang Proposition 3.2.3:
If `0 < a ≤ b` and `i < a` (which holds automatically for every coordinate of `H q n c`
with `a = n + c + 1` by `Defs.D_0007.code_ge`), then `[q i, child (q i) a)` and
`[q j, child (q j) b)` are either disjoint or `[q j, child (q j) b) ⊆ [q i, child (q i) a)`. -/
theorem prop_3_2_3 {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {i j a b : ℕ} (ha : 0 < a) (hab : a ≤ b) (hia : i < a) :
    Disjoint (Set.Ico (q i) (T.child (q i) a)) (Set.Ico (q j) (T.child (q j) b)) ∨
      Set.Ico (q j) (T.child (q j) b) ⊆ Set.Ico (q i) (T.child (q i) a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  by_cases hd : Disjoint (Set.Ico (q i) (T.child (q i) a)) (Set.Ico (q j) (T.child (q j) b))
  · exact Or.inl hd
  · right
    obtain ⟨x, hxi, hxj⟩ := Set.not_disjoint_iff.mp hd
    rcases lt_trichotomy (q i) (q j) with hij | heq | hji
    · have hmem : q j ∈ Set.Ioo (q i) (T.child (q i) a) :=
        ⟨hij, lt_of_le_of_lt hxj.1 hxi.2⟩
      exact (prop_3_2_1 E ha hb hmem).2.2.trans Set.Ioo_subset_Ico_self
    · rw [← heq]
      exact Set.Ico_subset_Ico_right (child_le_child T (q i) ha hab)
    · have hmem : q i ∈ Set.Ioo (q j) (T.child (q j) b) :=
        ⟨hji, lt_of_le_of_lt hxi.1 hxj.2⟩
      have hbi : b < i := (prop_3_2_1 E hb ha hmem).2.1
      omega

end Prop32

section Construction32

variable {α : Type} [LinearOrder α]

/-- Scale parameter `a = n + c + 1` (0-indexed `c` corresponds to paper's `i = c + 1`, so `a = n + i`). -/
def scale (n c : ℕ) : ℕ := n + c + 1

theorem scale_pos (n c : ℕ) : 0 < scale n c := by
  unfold scale; omega

/-- Canonical prefix coordinates of `H q n c`: `x k` is identical for all `x ∈ H q n c` (`k < n`). -/
noncomputable def prefixPt (q : ℕ ≃ α) (n : ℕ) (hn : 0 < n) (c : ℕ) (k : ℕ) : α :=
  (H_nonempty q n hn c).choose k

omit [LinearOrder α] in
theorem prefixPt_eq (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) {c : ℕ} {x : ℕ → α}
    (hx : x ∈ H q n c) {k : ℕ} (hk : k < n) :
    prefixPt q n hn c k = x k := by
  have hw := (H_nonempty q n hn c).choose_spec
  have h1 : code n (fun j => q.symm ((H_nonempty q n hn c).choose j)) = c := hw
  have h2 : code n (fun j => q.symm (x j)) = c := hx
  have h3 : (H_nonempty q n hn c).choose ∈ H q n (code n (fun j => q.symm (x j))) := by
    show code n _ = _; exact h1.trans h2.symm
  exact (mem_H_iff_same q n hn _ x).mp h3 k hk

omit [LinearOrder α] in
/-- Index bound from `Defs.D_0007.code_ge`: every prefix coordinate index is `< scale n c`. -/
theorem prefixPt_idx_lt_scale (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (c : ℕ) {k : ℕ} (hk : k < n) :
    q.symm (prefixPt q n hn c k) < scale n c := by
  have hw : code n (fun j => q.symm ((H_nonempty q n hn c).choose j)) = c :=
    (H_nonempty q n hn c).choose_spec
  have hle : q.symm (prefixPt q n hn c k) ≤ c :=
    calc q.symm (prefixPt q n hn c k)
        ≤ code n (fun j => q.symm ((H_nonempty q n hn c).choose j)) :=
          code_ge n (fun j => q.symm ((H_nonempty q n hn c).choose j)) k hk
      _ = c := hw
  unfold scale; omega

/-- Construction 3.2 `I(n, i)` (`i = c + 1`):
first-`n`-coordinate interval block `[p_k, child p_k a)` around the prefix of `H q n c`. -/
def Iblock (T : Tree2 α) (q : ℕ ≃ α) (n : ℕ) (hn : 0 < n) (c : ℕ) : Set (ℕ → α) :=
  { x | ∀ k < n, x k ∈ Set.Ico (prefixPt q n hn c k) (T.child (prefixPt q n hn c k) (scale n c)) }

/-- Construction 3.2 `J(n, i, l)` (`i = c + 1`):
next-`(c + 1)`-coordinate interval block `[r j, child (r j) a)` at coordinates `n .. n + c`. -/
def Jblock (T : Tree2 α) (n c : ℕ) (r : Fin (c + 1) → α) : Set (ℕ → α) :=
  { x | ∀ j : Fin (c + 1), x (n + j.1) ∈ Set.Ico (r j) (T.child (r j) (scale n c)) }

/-- Construction 3.2 `H(n, i, l) = H(n, i) ∩ J(n, i, l)`. -/
def Hsub (T : Tree2 α) (q : ℕ ≃ α) (n c : ℕ) (r : Fin (c + 1) → α) : Set (ℕ → α) :=
  H q n c ∩ Jblock T n c r

/-- Construction 3.2 `g(n, i, l) = I(n, i) ∩ J(n, i, l)`. -/
def gsub (T : Tree2 α) (q : ℕ ≃ α) (n : ℕ) (hn : 0 < n) (c : ℕ) (r : Fin (c + 1) → α) : Set (ℕ → α) :=
  Iblock T q n hn c ∩ Jblock T n c r

theorem H_subset_Iblock (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (c : ℕ) :
    H q n c ⊆ Iblock T q n hn c := by
  intro x hx k hk
  rw [prefixPt_eq q hn hx hk]
  exact ⟨le_rfl, T.lt_child _ _ (T.C_child _ _ (scale_pos n c))⟩

theorem Hsub_subset_gsub (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (c : ℕ)
    (r : Fin (c + 1) → α) :
    Hsub T q n c r ⊆ gsub T q n hn c r :=
  fun _ hx => ⟨H_subset_Iblock T q hn c hx.1, hx.2⟩

/-- Note D4 (block form): `g(n, i, l) ∩ H(n, i) = H(n, i, l)`. -/
theorem gsub_inter_H (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (c : ℕ)
    (r : Fin (c + 1) → α) :
    gsub T q n hn c r ∩ H q n c = Hsub T q n c r := by
  ext x
  simp only [gsub, Hsub, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨_, hJ⟩, hH⟩; exact ⟨hH, hJ⟩
  · rintro ⟨hH, hJ⟩; exact ⟨⟨H_subset_Iblock T q hn c hH, hJ⟩, hH⟩

/-- Partition of `H q n c` by `Hsub` over `r : Fin (c + 1) → { p // T.QStar (scale n c) p }`. -/
theorem Hsub_unique_cover (T : Tree2 α) (q : ℕ ≃ α) (n c : ℕ) {x : ℕ → α} (hx : x ∈ H q n c) :
    ∃! r : Fin (c + 1) → { p : α // T.QStar (scale n c) p },
      x ∈ Hsub T q n c (fun j => (r j).1) := by
  have ha := scale_pos n c
  have hcoord : ∀ j : Fin (c + 1),
      ∃ p : α, T.QStar (scale n c) p ∧ x (n + j.1) ∈ Set.Ico p (T.child p (scale n c)) :=
    fun j => prop_2_2_1_cover T ha (x (n + j.1))
  choose r hr hxJ using hcoord
  refine ⟨fun j => ⟨r j, hr j⟩, ⟨hx, hxJ⟩, ?_⟩
  intro r' hr'
  funext j
  apply Subtype.ext
  by_contra hne
  exact Set.disjoint_left.mp (prop_2_2_1_disjoint T ha (r' j).2 (hr j) hne) (hr'.2 j) (hxJ j)

omit [LinearOrder α] in
/-- Helper: every coordinate condition `x k ∈ S` is clopen in `xtop α` (since each coordinate is discrete). -/
private theorem isClopen_coord_xtop (k : ℕ) (S : Set α) :
    @IsOpen (ℕ → α) (xtop α) { x | x k ∈ S } ∧
    @IsClosed (ℕ → α) (xtop α) { x | x k ∈ S } := by
  let : TopologicalSpace α := ⊥
  let : DiscreteTopology α := ⟨rfl⟩
  have hEq : { x : ℕ → α | x k ∈ S } = (fun x : ℕ → α => x k) ⁻¹' S := rfl
  constructor
  · change IsOpen { x : ℕ → α | x k ∈ S }
    rw [hEq]
    exact (isOpen_discrete S).preimage (continuous_apply k)
  · change IsClosed { x : ℕ → α | x k ∈ S }
    rw [hEq]
    exact (isClosed_discrete S).preimage (continuous_apply k)

theorem Iblock_clopen (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (c : ℕ) :
    @IsOpen (ℕ → α) (xtop α) (Iblock T q n hn c) ∧
    @IsClosed (ℕ → α) (xtop α) (Iblock T q n hn c) := by
  let : TopologicalSpace (ℕ → α) := xtop α
  have hEq : Iblock T q n hn c =
      ⋂ k ∈ Finset.range n, { x : ℕ → α | x k ∈ Set.Ico (prefixPt q n hn c k)
        (T.child (prefixPt q n hn c k) (scale n c)) } := by
    ext x; simp [Iblock]
  rw [hEq]
  exact ⟨isOpen_biInter_finset (fun k _ => (isClopen_coord_xtop k _).1),
         isClosed_biInter (fun k _ => (isClopen_coord_xtop k _).2)⟩

theorem Jblock_clopen (T : Tree2 α) (n c : ℕ) (r : Fin (c + 1) → α) :
    @IsOpen (ℕ → α) (xtop α) (Jblock T n c r) ∧
    @IsClosed (ℕ → α) (xtop α) (Jblock T n c r) := by
  let : TopologicalSpace (ℕ → α) := xtop α
  have hEq : Jblock T n c r =
      ⋂ j : Fin (c + 1), { x : ℕ → α | x (n + j.1) ∈ Set.Ico (r j) (T.child (r j) (scale n c)) } := by
    ext x; simp [Jblock]
  rw [hEq]
  exact ⟨isOpen_iInter_of_finite (fun j => (isClopen_coord_xtop (n + j.1) _).1),
         isClosed_iInter (fun j => (isClopen_coord_xtop (n + j.1) _).2)⟩

theorem Hsub_clopen (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (c : ℕ)
    (r : Fin (c + 1) → α) :
    @IsOpen (ℕ → α) (xtop α) (Hsub T q n c r) ∧
    @IsClosed (ℕ → α) (xtop α) (Hsub T q n c r) := by
  let : TopologicalSpace (ℕ → α) := xtop α
  exact ⟨(H_isOpen q n hn c).inter (Jblock_clopen T n c r).1,
         (H_isClosed q n hn c).inter (Jblock_clopen T n c r).2⟩

theorem gsub_clopen (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (c : ℕ)
    (r : Fin (c + 1) → α) :
    @IsOpen (ℕ → α) (xtop α) (gsub T q n hn c r) ∧
    @IsClosed (ℕ → α) (xtop α) (gsub T q n hn c r) := by
  let : TopologicalSpace (ℕ → α) := xtop α
  exact ⟨(Iblock_clopen T q hn c).1.inter (Jblock_clopen T n c r).1,
         (Iblock_clopen T q hn c).2.inter (Jblock_clopen T n c r).2⟩

/-- Pointwise canonical `r_x` for `x : ℕ → α` at level `n ≥ 1`. -/
noncomputable def rOf (T : Tree2 α) (q : ℕ ≃ α) (n : ℕ) (x : ℕ → α) :
    Fin (code n (fun k => q.symm (x k)) + 1) → { p : α // T.QStar (scale n (code n (fun k => q.symm (x k)))) p } :=
  (Hsub_unique_cover T q n (code n (fun k => q.symm (x k))) rfl).choose

theorem mem_Hsub_rOf (T : Tree2 α) (q : ℕ ≃ α) (n : ℕ) (x : ℕ → α) :
    x ∈ Hsub T q n (code n (fun k => q.symm (x k))) (fun j => (rOf T q n x j).1) :=
  (Hsub_unique_cover T q n (code n (fun k => q.symm (x k))) rfl).choose_spec.1

/-- Note D1: pointwise `H(n, x)` (`n ≥ 1`). -/
noncomputable def Hx (T : Tree2 α) (q : ℕ ≃ α) (n : ℕ) (x : ℕ → α) : Set (ℕ → α) :=
  Hsub T q n (code n (fun k => q.symm (x k))) (fun j => (rOf T q n x j).1)

/-- Note D1: pointwise `g(n, x)` (`n ≥ 1`). -/
noncomputable def gx (T : Tree2 α) (q : ℕ ≃ α) (n : ℕ) (hn : 0 < n) (x : ℕ → α) : Set (ℕ → α) :=
  gsub T q n hn (code n (fun k => q.symm (x k))) (fun j => (rOf T q n x j).1)

theorem mem_Hx (T : Tree2 α) (q : ℕ ≃ α) (n : ℕ) (x : ℕ → α) : x ∈ Hx T q n x :=
  mem_Hsub_rOf T q n x

theorem Hx_subset_gx (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (x : ℕ → α) :
    Hx T q n x ⊆ gx T q n hn x :=
  Hsub_subset_gsub T q hn _ _

theorem mem_gx (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (x : ℕ → α) : x ∈ gx T q n hn x :=
  Hx_subset_gx T q hn x (mem_Hx T q n x)

/-- Note D4 (pointwise): `g(n, x) ∩ H(n, code n x) = H(n, x)`. -/
theorem gx_inter_H (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (x : ℕ → α) :
    gx T q n hn x ∩ H q n (code n (fun k => q.symm (x k))) = Hx T q n x :=
  gsub_inter_H T q hn _ _

theorem Hx_clopen (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (x : ℕ → α) :
    @IsOpen (ℕ → α) (xtop α) (Hx T q n x) ∧ @IsClosed (ℕ → α) (xtop α) (Hx T q n x) :=
  Hsub_clopen T q hn _ _

theorem gx_clopen (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) (x : ℕ → α) :
    @IsOpen (ℕ → α) (xtop α) (gx T q n hn x) ∧ @IsClosed (ℕ → α) (xtop α) (gx T q n hn x) :=
  gsub_clopen T q hn _ _

/-- Note D2: if `y ∈ H(n, x)`, then `H(n, y) = H(n, x)` and `g(n, y) = g(n, x)`. -/
theorem Hx_gx_eq_of_mem (T : Tree2 α) (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) {x y : ℕ → α}
    (hy : y ∈ Hx T q n x) :
    Hx T q n y = Hx T q n x ∧ gx T q n hn y = gx T q n hn x := by
  have hc : code n (fun k => q.symm (y k)) = code n (fun k => q.symm (x k)) := hy.1
  have hr : ∀ (j : Fin (code n (fun k => q.symm (x k)) + 1)),
      (rOf T q n y (j.cast (by rw [hc]))).1 = (rOf T q n x j).1 := by
    intro j
    let py : α := (rOf T q n y (j.cast (by rw [hc]))).1
    have hy1 : y (n + j.1) ∈ Set.Ico py (T.child py (scale n (code n (fun k => q.symm (x k))))) := by
      have h0 := (mem_Hsub_rOf T q n y).2 (j.cast (by rw [hc]))
      simpa only [py, Fin.val_cast, hc] using h0
    have hy2 := hy.2 j
    have hq1 : T.QStar (scale n (code n (fun k => q.symm (x k)))) py := by
      have h0 := (rOf T q n y (j.cast (by rw [hc]))).2
      simpa only [py, hc] using h0
    have hq2 := (rOf T q n x j).2
    show py = (rOf T q n x j).1
    by_contra hne
    exact Set.disjoint_left.mp (prop_2_2_1_disjoint T (scale_pos n _) hq1 hq2 hne) hy1 hy2
  have hJ : Jblock T n (code n (fun k => q.symm (y k))) (fun j => (rOf T q n y j).1) =
            Jblock T n (code n (fun k => q.symm (x k))) (fun j => (rOf T q n x j).1) := by
    ext z
    simp only [Jblock, Set.mem_ofPred_eq]
    constructor
    · intro hz j
      have h0 := hz (j.cast (by rw [hc]))
      have hrj := hr j
      simpa only [Fin.val_cast, hrj, hc] using h0
    · intro hz j
      let jx : Fin (code n (fun k => q.symm (x k)) + 1) := j.cast (by rw [hc])
      have h0 := hz jx
      have hjeq : jx.cast (by rw [hc]) = j := Fin.ext rfl
      have hrj : (rOf T q n y j).1 = (rOf T q n x jx).1 := by
        simpa only [hjeq] using hr jx
      simpa only [jx, Fin.val_cast, hrj, hc] using h0
  constructor
  · simp only [Hx, Hsub, hc, hJ]
  · simp only [gx, gsub, hc, hJ]

/-- Construction 7 intersection property for `H`: `⋂ n, H(n + 1, x) = {x}`. -/
theorem Hx_inter_eq_singleton (T : Tree2 α) (q : ℕ ≃ α) (x : ℕ → α) :
    (⋂ n : ℕ, Hx T q (n + 1) x) = {x} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro hy
    funext k
    have hk : y ∈ H q (k + 1) (code (k + 1) (fun j => q.symm (x j))) := (hy k).1
    exact (mem_H_iff_same q (k + 1) (Nat.succ_pos k) y x).mp hk k (Nat.lt_succ_self k)
  · intro hy n
    rw [hy]
    exact mem_Hx T q (n + 1) x

end Construction32

section Prop33And35

variable {α : Type} [LinearOrder α]

/-- Chen–Wang Proposition 3.3.8 (laminar property of `𝒢_n`):
If `c₁ < c₂` and `r₁, r₂` lie in `QStar (scale n c₁)` / `QStar (scale n c₂)`, then
`gsub c₁ r₁` and `gsub c₂ r₂` are either disjoint or `gsub c₂ r₂ ⊆ gsub c₁ r₁`. -/
theorem gsub_laminar {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {c₁ c₂ : ℕ} (hcc : c₁ < c₂)
    (r₁ : Fin (c₁ + 1) → { p : α // T.QStar (scale n c₁) p })
    (r₂ : Fin (c₂ + 1) → { p : α // T.QStar (scale n c₂) p }) :
    Disjoint (gsub T q n hn c₁ (fun j => (r₁ j).1)) (gsub T q n hn c₂ (fun j => (r₂ j).1)) ∨
      gsub T q n hn c₂ (fun j => (r₂ j).1) ⊆ gsub T q n hn c₁ (fun j => (r₁ j).1) := by
  by_cases hd : Disjoint (gsub T q n hn c₁ (fun j => (r₁ j).1)) (gsub T q n hn c₂ (fun j => (r₂ j).1))
  · exact Or.inl hd
  · right
    obtain ⟨w, hw1, hw2⟩ := Set.not_disjoint_iff.mp hd
    have ha : 0 < scale n c₁ := scale_pos n c₁
    have hab : scale n c₁ ≤ scale n c₂ := by unfold scale; omega
    intro z hz
    constructor
    · intro k hk
      have hidx : q.symm (prefixPt q n hn c₁ k) < scale n c₁ := prefixPt_idx_lt_scale q hn c₁ hk
      have h3 := prop_3_2_3 E (i := q.symm (prefixPt q n hn c₁ k))
        (j := q.symm (prefixPt q n hn c₂ k)) ha hab hidx
      simp only [Equiv.apply_symm_apply] at h3
      rcases h3 with hdisj | hsub
      · exact (Set.disjoint_left.mp hdisj (hw1.1 k hk) (hw2.1 k hk)).elim
      · exact hsub (hz.1 k hk)
    · intro j
      let j₂ : Fin (c₂ + 1) := ⟨j.1, by omega⟩
      rcases prop_2_2_5 T ha hab (r₁ j).2 (r₂ j₂).2 with hdisj | hsub
      · exact (Set.disjoint_left.mp hdisj (hw1.2 j) (hw2.2 j₂)).elim
      · exact hsub (hz.2 j₂)

/-- Chen–Wang Proposition 3.3.6 (strong form):
If `c₁ < c₂`, then `H q n c₁` is disjoint from `Iblock T q n hn c₂` (and hence from `⋃ 𝒢(n, c₂)`). -/
theorem H_disjoint_Iblock_of_lt {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {c₁ c₂ : ℕ} (hcc : c₁ < c₂) :
    Disjoint (H q n c₁) (Iblock T q n hn c₂) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hne : ∃ k < n, prefixPt q n hn c₁ k ≠ prefixPt q n hn c₂ k := by
    by_contra hall
    push Not at hall
    have hw1 := (H_nonempty q n hn c₁).choose_spec
    have hw2 := (H_nonempty q n hn c₂).choose_spec
    have heq : c₁ = c₂ := by
      have hsame : (H_nonempty q n hn c₁).choose ∈
          H q n (code n (fun k => q.symm ((H_nonempty q n hn c₂).choose k))) :=
        (mem_H_iff_same q n hn _ _).mpr (fun k hk => hall k hk)
      have h1 : code n (fun k => q.symm ((H_nonempty q n hn c₁).choose k)) = c₁ := hw1
      have h2 : code n (fun k => q.symm ((H_nonempty q n hn c₂).choose k)) = c₂ := hw2
      have h3 : code n (fun k => q.symm ((H_nonempty q n hn c₁).choose k)) =
                code n (fun k => q.symm ((H_nonempty q n hn c₂).choose k)) := hsame
      omega
    omega
  obtain ⟨k, hk, hkne⟩ := hne
  have hxk : x k = prefixPt q n hn c₁ k := (prefixPt_eq q hn hx1 hk).symm
  have hxI : prefixPt q n hn c₁ k ∈ Set.Ico (prefixPt q n hn c₂ k)
      (T.child (prefixPt q n hn c₂ k) (scale n c₂)) := by
    rw [← hxk]; exact hx2 k hk
  have hIoo : q (q.symm (prefixPt q n hn c₁ k)) ∈ Set.Ioo (q (q.symm (prefixPt q n hn c₂ k)))
      (T.child (q (q.symm (prefixPt q n hn c₂ k))) (scale n c₂)) := by
    simp only [Equiv.apply_symm_apply]
    exact ⟨lt_of_le_of_ne hxI.1 hkne.symm, hxI.2⟩
  have hgt : scale n c₂ < q.symm (prefixPt q n hn c₁ k) :=
    (prop_3_2_1 E (scale_pos n c₂) Nat.one_pos hIoo).2.1
  have hlt : q.symm (prefixPt q n hn c₁ k) < scale n c₁ :=
    prefixPt_idx_lt_scale q hn c₁ hk
  unfold scale at hgt hlt
  omega

/-- Chen–Wang Proposition 3.3.6 for `gsub`. -/
theorem H_disjoint_gsub_of_lt {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {c₁ c₂ : ℕ} (hcc : c₁ < c₂) (r₂ : Fin (c₂ + 1) → α) :
    Disjoint (H q n c₁) (gsub T q n hn c₂ r₂) :=
  (H_disjoint_Iblock_of_lt E hn hcc).mono_right Set.inter_subset_left

/-- Chen–Wang Proposition 3.3.6':
If `Hx n y ∩ gx n z` is nonempty and `Hx n y ≠ Hx n z`, then `code n z < code n y`. -/
theorem code_lt_of_Hx_inter_gx {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {y z : ℕ → α}
    (hinter : (Hx T q n y ∩ gx T q n hn z).Nonempty)
    (hne : Hx T q n y ≠ Hx T q n z) :
    code n (fun k => q.symm (z k)) < code n (fun k => q.symm (y k)) := by
  obtain ⟨w, hwy, hwz⟩ := hinter
  by_contra hnot
  rcases lt_or_eq_of_le (not_lt.mp hnot) with hlt | heq
  · exact Set.disjoint_left.mp (H_disjoint_gsub_of_lt E hn hlt _) hwy.1 hwz
  · have hwH : w ∈ H q n (code n (fun k => q.symm (z k))) := heq ▸ hwy.1
    have hwHz : w ∈ Hx T q n z := by
      rw [← gx_inter_H T q hn z]
      exact ⟨hwz, hwH⟩
    have e1 := (Hx_gx_eq_of_mem T q hn hwy).1
    have e2 := (Hx_gx_eq_of_mem T q hn hwHz).1
    exact hne (e1.symm.trans e2)

/-- Chen–Wang Proposition 3.3.4 (transitivity of `gx`):
If `y ∈ gx n x`, then `gx n y ⊆ gx n x`. -/
theorem gx_subset_of_mem_gx {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {x y : ℕ → α} (hy : y ∈ gx T q n hn x) :
    gx T q n hn y ⊆ gx T q n hn x := by
  by_cases hH : y ∈ Hx T q n x
  · rw [(Hx_gx_eq_of_mem T q hn hH).2]
  · have hne : Hx T q n y ≠ Hx T q n x := fun h => hH (h ▸ mem_Hx T q n y)
    have hlt : code n (fun k => q.symm (x k)) < code n (fun k => q.symm (y k)) :=
      code_lt_of_Hx_inter_gx E hn ⟨y, mem_Hx T q n y, hy⟩ hne
    rcases gsub_laminar E hn hlt (rOf T q n x) (rOf T q n y) with hdisj | hsub
    · exact (Set.disjoint_left.mp hdisj hy (mem_gx T q hn y)).elim
    · exact hsub

/-- Chen–Wang Proposition 3.3.5 (monotonicity of `gx` in `n`):
For `0 < n`, `gx (n + 1) x ⊆ gx n x`. -/
theorem gx_succ_subset {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) (x : ℕ → α) :
    gx T q (n + 1) (Nat.succ_pos n) x ⊆ gx T q n hn x := by
  set c₁ := code n (fun k => q.symm (x k))
  set c₂ := code (n + 1) (fun k => q.symm (x k))
  have hc : c₁ ≤ c₂ := code_mono n hn (fun k => q.symm (x k)) (n + 1) (Nat.le_succ n)
  have ha : 0 < scale n c₁ := scale_pos n c₁
  have hb : 0 < scale (n + 1) c₂ := scale_pos (n + 1) c₂
  have hab : scale n c₁ ≤ scale (n + 1) c₂ := by unfold scale; omega
  intro z hz
  constructor
  · intro k hk
    have hp1 : prefixPt q n hn c₁ k = x k := prefixPt_eq q hn rfl hk
    have hp2 : prefixPt q (n + 1) (Nat.succ_pos n) c₂ k = x k :=
      prefixPt_eq q (Nat.succ_pos n) rfl (Nat.lt_succ_of_lt hk)
    have hzk := hz.1 k (Nat.lt_succ_of_lt hk)
    rw [hp1]
    rw [hp2] at hzk
    exact Set.Ico_subset_Ico_right (child_le_child T (x k) ha hab) hzk
  · intro j
    by_cases hj0 : j.1 = 0
    · -- Coordinate `n`: `z n ∈ [x n, child (x n) b)`, while `x n ∈ [r₁ 0, child (r₁ 0) a)`
      have hzn : z (n + j.1) ∈ Set.Ico (x n) (T.child (x n) (scale (n + 1) c₂)) := by
        rw [hj0, Nat.add_zero]
        have hp2 : prefixPt q (n + 1) (Nat.succ_pos n) c₂ n = x n :=
          prefixPt_eq q (Nat.succ_pos n) rfl (Nat.lt_succ_self n)
        have h0 := hz.1 n (Nat.lt_succ_self n)
        rw [hp2] at h0
        exact h0
      have hxn : x n ∈ Set.Ico (rOf T q n x j).1 (T.child (rOf T q n x j).1 (scale n c₁)) := by
        have h0 := (mem_Hsub_rOf T q n x).2 j
        simpa only [hj0, Nat.add_zero] using h0
      rcases eq_or_lt_of_le hxn.1 with heq | hlt
      · rw [← heq] at hzn
        exact Set.Ico_subset_Ico_right (child_le_child T _ ha hab) hzn
      · have hIoo : q (q.symm (x n)) ∈ Set.Ioo (q (q.symm (rOf T q n x j).1))
            (T.child (q (q.symm (rOf T q n x j).1)) (scale n c₁)) := by
          simp only [Equiv.apply_symm_apply]
          exact ⟨hlt, hxn.2⟩
        have hsub := (prop_3_2_1 E ha hb hIoo).2.2
        simp only [Equiv.apply_symm_apply] at hsub
        exact Set.Ioo_subset_Ico_self (hsub hzn)
    · -- Coordinates `n + 1 .. n + c₁`: covered by `Jblock (n + 1) c₂ (rOf (n + 1) x)`
      let j₂ : Fin (c₂ + 1) := ⟨j.1 - 1, by omega⟩
      have hcoord : n + j.1 = (n + 1) + j₂.1 := by show n + j.1 = (n + 1) + (j.1 - 1); omega
      have h1 : x (n + j.1) ∈ Set.Ico (rOf T q n x j).1 (T.child (rOf T q n x j).1 (scale n c₁)) :=
        (mem_Hsub_rOf T q n x).2 j
      have h2 : x (n + j.1) ∈ Set.Ico (rOf T q (n + 1) x j₂).1
          (T.child (rOf T q (n + 1) x j₂).1 (scale (n + 1) c₂)) := by
        rw [hcoord]
        exact (mem_Hsub_rOf T q (n + 1) x).2 j₂
      rcases prop_2_2_5 T ha hab (rOf T q n x j).2 (rOf T q (n + 1) x j₂).2 with hdisj | hsub
      · exact (Set.disjoint_left.mp hdisj h1 h2).elim
      · rw [hcoord]
        exact hsub (hz.2 j₂)

/-- Chen–Wang Proposition 3.5.3 (nested `H`-chain convergence, used in Proposition 9.5):
If `n : ℕ → ℕ` is strictly increasing with `0 < n 0`, and `Hx (n (i + 1)) (y (i + 1)) ⊆ Hx (n i) (y i)`
for all `i`, then there exists a unique `t : ℕ → α` such that `⋂ i, Hx (n i) (y i) = {t}`. -/
theorem Hx_chain_inter_eq_singleton (T : Tree2 α) (q : ℕ ≃ α)
    (n : ℕ → ℕ) (hn_pos : ∀ i, 0 < n i) (hn_mono : StrictMono n)
    (y : ℕ → (ℕ → α)) (hchain : ∀ i, Hx T q (n (i + 1)) (y (i + 1)) ⊆ Hx T q (n i) (y i)) :
    ∃ t : ℕ → α, (⋂ i : ℕ, Hx T q (n i) (y i)) = {t} := by
  have hsub : ∀ {i j : ℕ}, i ≤ j → Hx T q (n j) (y j) ⊆ Hx T q (n i) (y i) := by
    intro i j hij
    induction hij with
    | refl => exact Subset.rfl
    | @step m _ ih => exact (hchain m).trans ih
  have hn_ge : ∀ k, k ≤ n k := fun k => hn_mono.id_le k
  have hagree : ∀ {i j k : ℕ}, i ≤ j → k < n i → y j k = y i k := by
    intro i j k hij hk
    have hyj : y j ∈ Hx T q (n i) (y i) := hsub hij (mem_Hx T q (n j) (y j))
    exact (mem_H_iff_same q (n i) (hn_pos i) (y j) (y i)).mp hyj.1 k hk
  let t : ℕ → α := fun k => y (k + 1) k
  refine ⟨t, ?_⟩
  ext w
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro hw
    funext k
    have hlt : k < n (k + 1) := lt_of_lt_of_le (Nat.lt_succ_self k) (hn_ge (k + 1))
    exact (mem_H_iff_same q (n (k + 1)) (hn_pos (k + 1)) w (y (k + 1))).mp (hw (k + 1)).1 k hlt
  · intro hw i
    rw [hw]
    let ci := code (n i) (fun k => q.symm (y i k))
    let m := max i (n i + ci + 1)
    have him : i ≤ m := le_max_left _ _
    have hym : y m ∈ Hx T q (n i) (y i) := hsub him (mem_Hx T q (n m) (y m))
    have ht_eq : ∀ k < n i + ci + 1, t k = y m k := by
      intro k hk
      have hkm : k + 1 ≤ m := by omega
      have hkn : k < n (k + 1) := lt_of_lt_of_le (Nat.lt_succ_self k) (hn_ge (k + 1))
      exact (hagree hkm hkn).symm
    constructor
    · show t ∈ H q (n i) ci
      have h1 : ∀ k < n i, t k = y m k := fun k hk => ht_eq k (by omega)
      have h2 : y m ∈ H q (n i) (code (n i) (fun k => q.symm (y i k))) := hym.1
      have h3 := (mem_H_iff_same q (n i) (hn_pos i) (y m) (y i)).mp h2
      exact (mem_H_iff_same q (n i) (hn_pos i) t (y i)).mpr (fun k hk => (h1 k hk).trans (h3 k hk))
    · intro j
      have hjlt : n i + j.1 < n i + ci + 1 := by omega
      rw [ht_eq (n i + j.1) hjlt]
      exact hym.2 j

end Prop33And35

section ConcreteQTreeEnum

/-- Concrete countable linear order realizing Chen–Wang's tree `Q`. -/
abbrev QTree : Type := List (OrderDual ℕ+)

private theorem list_lex_lt_append_singleton {β : Type*} [LinearOrder β] (u : List β) (x : β) :
    u < u ++ [x] := by
  induction u with
  | nil => exact List.Lex.nil
  | cons a as ih => exact List.Lex.cons ih

private theorem list_lex_nil_le {β : Type*} [LinearOrder β] (u : List β) :
    ([] : List β) ≤ u := by
  cases u with
  | nil => exact le_rfl
  | cons a as => exact le_of_lt List.Lex.nil

private theorem list_lex_append_lt_append {β : Type*} [LinearOrder β]
    (p : List β) {x y : β} (hxy : x < y) (v w : List β) :
    p ++ x :: v < p ++ y :: w := by
  induction p with
  | nil => exact List.Lex.rel hxy
  | cons a as ih => exact List.Lex.cons ih

private theorem list_lex_prefix_of_lt_append {β : Type*} [LinearOrder β]
    {p q : List β} {x : β} (h1 : p < q) (h2 : q < p ++ [x]) :
    ∃ r, q = p ++ r ∧ r ≠ [] := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => exact absurd h1 (lt_irrefl _)
    | cons b bs => exact ⟨b :: bs, rfl, List.cons_ne_nil _ _⟩
  | cons a as ih =>
    cases q with
    | nil => exact absurd h1 (not_lt.mpr (list_lex_nil_le _))
    | cons b bs =>
      rcases lt_trichotomy a b with hab | rfl | hba
      · exact absurd (lt_trans h2 (List.Lex.rel hab)) (lt_irrefl _)
      · have h1' : as < bs := by
          cases h1 with
          | rel h => exact absurd h (lt_irrefl _)
          | cons h => exact h
        have h2' : bs < as ++ [x] := by
          cases h2 with
          | rel h => exact absurd h (lt_irrefl _)
          | cons h => exact h
        obtain ⟨r, rfl, hr⟩ := ih h1' h2'
        exact ⟨r, rfl, hr⟩
      · exact absurd (lt_trans h1 (List.Lex.rel hba)) (lt_irrefl _)

instance : NoMaxOrder QTree where
  exists_gt u := ⟨u ++ [OrderDual.toDual 1], list_lex_lt_append_singleton u _⟩

/-- Concrete `Defs.D_0003.Tree2` structure on `QTree`. -/
def qtreeTree2 : Tree2 QTree where
  lev u := u.length
  C p c := ∃ j : ℕ+, c = p ++ [OrderDual.toDual j]
  idx u := match u.getLast? with
    | none => 0
    | some x => (OrderDual.ofDual x).val
  lev_child := by rintro p _ ⟨j, rfl⟩; simp
  lt_child := by rintro p _ ⟨j, rfl⟩; exact list_lex_lt_append_singleton p _
  gap := by
    rintro p _ q ⟨j, rfl⟩ hlev ⟨h1, h2⟩
    obtain ⟨r, rfl, hr⟩ := list_lex_prefix_of_lt_append h1 h2
    have hpos : 0 < r.length := List.length_pos_iff.mpr hr
    simp only [List.length_append] at hlev
    omega
  idx_pos := by rintro p _ ⟨j, rfl⟩; simp [j.pos]
  child_anti := by
    rintro p _ _ ⟨j, rfl⟩ ⟨j', rfl⟩ hlt
    simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast?_singleton, OrderDual.ofDual_toDual] at hlt
    exact list_lex_append_lt_append p (show OrderDual.toDual j' < OrderDual.toDual j from hlt) [] []
  child_inj := by
    rintro p _ _ ⟨j, rfl⟩ ⟨j', rfl⟩ heq
    simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast?_singleton, OrderDual.ofDual_toDual] at heq
    have : j = j' := PNat.eq heq
    rw [this]
  root := []
  child p j := if h : 0 < j then p ++ [OrderDual.toDual ⟨j, h⟩] else []
  C_child := by
    intro p j hj
    simp only [hj, ↓reduceDIte]
    exact ⟨⟨j, hj⟩, rfl⟩
  idx_child := by
    intro p j
    by_cases hj : 0 < j
    · simp only [hj, ↓reduceDIte, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
        List.getLast?_singleton]
      rfl
    · have : j = 0 := by omega
      subst this
      simp
  root_le := list_lex_nil_le
  connected := by
    intro u
    induction u using List.reverseRecOn with
    | nil => exact ReflTransGen.refl
    | append_singleton p x ih => exact ih.tail ⟨OrderDual.ofDual x, rfl⟩
  desc_lt := by
    intro p j r hj hdesc
    have hpref : ∀ w, ReflTransGen (fun a b : QTree => ∃ k : ℕ+, b = a ++ [OrderDual.toDual k])
        (p ++ [OrderDual.toDual ⟨j + 1, Nat.succ_pos j⟩]) w →
        ∃ v, w = p ++ OrderDual.toDual ⟨j + 1, Nat.succ_pos j⟩ :: v := by
      intro w hw
      induction hw with
      | refl => exact ⟨[], by simp⟩
      | @tail b c _ hbc ih =>
        obtain ⟨v, rfl⟩ := ih
        obtain ⟨k, rfl⟩ := hbc
        exact ⟨v ++ [OrderDual.toDual k], by simp [List.append_assoc]⟩
    simp only [Nat.succ_pos, hj, ↓reduceDIte] at hdesc ⊢
    obtain ⟨v, rfl⟩ := hpref r hdesc
    have hlt : OrderDual.toDual (⟨j + 1, Nat.succ_pos j⟩ : ℕ+) < OrderDual.toDual (⟨j, hj⟩ : ℕ+) :=
      show (⟨j, hj⟩ : ℕ+) < ⟨j + 1, Nat.succ_pos j⟩ from Nat.lt_succ_self j
    exact list_lex_append_lt_append p hlt v []

/-- Prefix-compatible injective encoding `QTree → ℕ`. -/
def encodeQTree (u : QTree) : ℕ :=
  u.foldl (fun acc x => Nat.pair (OrderDual.ofDual x).val acc + 1) 0

theorem encodeQTree_nil : encodeQTree [] = 0 := rfl

theorem encodeQTree_append_singleton (p : QTree) (x : OrderDual ℕ+) :
    encodeQTree (p ++ [x]) = Nat.pair (OrderDual.ofDual x).val (encodeQTree p) + 1 := by
  simp [encodeQTree]

theorem encodeQTree_injective : Function.Injective encodeQTree := by
  intro u v h
  induction u using List.reverseRecOn generalizing v with
  | nil =>
    cases v using List.reverseRecOn with
    | nil => rfl
    | append_singleton p x =>
      rw [encodeQTree_nil, encodeQTree_append_singleton] at h
      omega
  | append_singleton p x ih =>
    cases v using List.reverseRecOn with
    | nil =>
      rw [encodeQTree_nil, encodeQTree_append_singleton] at h
      omega
    | append_singleton q y =>
      rw [encodeQTree_append_singleton, encodeQTree_append_singleton] at h
      have hpair : Nat.pair (OrderDual.ofDual x).val (encodeQTree p) =
                   Nat.pair (OrderDual.ofDual y).val (encodeQTree q) := by omega
      have ⟨h1, h2⟩ := Nat.pair_eq_pair.mp hpair
      have hxy : x = y := OrderDual.ofDual.injective (PNat.eq h1)
      rw [ih h2, hxy]

private theorem nat_pair_lt_of_lt_left {a a' b : ℕ} (h : a < a') :
    Nat.pair a b < Nat.pair a' b := by
  unfold Nat.pair
  split_ifs with h1 h2 h3
  · omega
  · have hmul : b * b ≤ a' * a' := Nat.mul_le_mul (by omega) (by omega)
    omega
  · omega
  · have hmul : a * a ≤ a' * a' := Nat.mul_le_mul (by omega) (by omega)
    omega

private theorem nat_pair_ge_right (a b : ℕ) : b ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs with h
  · have hsq : b ≤ b * b := Nat.le_mul_self b
    omega
  · omega

theorem encodeQTree_range_infinite : (Set.range encodeQTree).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => encodeQTree [OrderDual.toDual ⟨k + 1, Nat.succ_pos k⟩])
  · intro a b hab
    have h1 := encodeQTree_injective hab
    have h2 : (OrderDual.toDual (⟨a + 1, Nat.succ_pos a⟩ : ℕ+)) =
              OrderDual.toDual (⟨b + 1, Nat.succ_pos b⟩ : ℕ+) := (List.cons.inj h1).1
    have h3 := congrArg (fun z => (OrderDual.ofDual z).val) h2
    simp only [OrderDual.ofDual_toDual] at h3
    omega
  · intro k
    exact ⟨_, rfl⟩

open scoped Classical in
/-- Order-preserving bijection `ℕ ≃ QTree` induced by `encodeQTree`. -/
noncomputable def qtreeEnum : ℕ ≃ QTree :=
  { toFun := fun m => (Nat.nth_mem_of_infinite encodeQTree_range_infinite m).choose
    invFun := fun u => Nat.count (· ∈ Set.range encodeQTree) (encodeQTree u)
    left_inv := fun m => by
      dsimp only
      have hspec : encodeQTree (Nat.nth_mem_of_infinite encodeQTree_range_infinite m).choose =
          Nat.nth (· ∈ Set.range encodeQTree) m :=
        (Nat.nth_mem_of_infinite encodeQTree_range_infinite m).choose_spec
      rw [hspec]
      exact Nat.count_nth_of_infinite encodeQTree_range_infinite m
    right_inv := fun u => by
      dsimp only
      apply encodeQTree_injective
      have hspec : encodeQTree (Nat.nth_mem_of_infinite encodeQTree_range_infinite
          (Nat.count (· ∈ Set.range encodeQTree) (encodeQTree u))).choose =
          Nat.nth (· ∈ Set.range encodeQTree)
            (Nat.count (· ∈ Set.range encodeQTree) (encodeQTree u)) :=
        (Nat.nth_mem_of_infinite encodeQTree_range_infinite _).choose_spec
      rw [hspec]
      exact Nat.nth_count (p := (· ∈ Set.range encodeQTree)) ⟨u, rfl⟩ }

/-- Concrete kernel-verified proof that `(QTree, qtreeTree2, qtreeEnum)` satisfies `Tree2Enum`. -/
theorem qtreeTree2Enum : Tree2Enum qtreeTree2 qtreeEnum := by
  classical
  have hinv : ∀ u : QTree,
      qtreeEnum.symm u = Nat.count (· ∈ Set.range encodeQTree) (encodeQTree u) := by
    intro u
    change Nat.count (· ∈ Set.range encodeQTree) (encodeQTree u) = _
    rfl
  constructor
  · rintro p _ ⟨j, rfl⟩
    rw [hinv p, hinv (p ++ [OrderDual.toDual j])]
    have hlt : encodeQTree p < encodeQTree (p ++ [OrderDual.toDual j]) := by
      rw [encodeQTree_append_singleton, OrderDual.ofDual_toDual]
      have := nat_pair_ge_right j.val (encodeQTree p)
      omega
    exact Nat.count_strict_mono (p := (· ∈ Set.range encodeQTree)) ⟨p, rfl⟩ hlt
  · rintro p _ ⟨j, rfl⟩
    rw [hinv (p ++ [OrderDual.toDual j])]
    have hidx : qtreeTree2.idx (p ++ [OrderDual.toDual j]) = j.val := by
      simp [qtreeTree2]
    rw [hidx]
    -- Construct `j.val` distinct elements of `Set.range encodeQTree` strictly below `encodeQTree (p ++ [j])`
    let f : ℕ → ℕ := fun k =>
      if hk : k = 0 then encodeQTree p
      else encodeQTree (p ++ [OrderDual.toDual ⟨k, Nat.pos_of_ne_zero hk⟩])
    have hf_inj : Set.InjOn f (Finset.range j.val : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_range] at ha hb
      by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0
      · omega
      · simp only [f, ha0, hb0, ↓reduceDIte] at hab
        have heq := encodeQTree_injective hab
        have hlen := congrArg List.length heq
        simp at hlen
      · simp only [f, ha0, hb0, ↓reduceDIte] at hab
        have heq := encodeQTree_injective hab
        have hlen := congrArg List.length heq
        simp at hlen
      · simp only [f, ha0, hb0, ↓reduceDIte] at hab
        have heq := encodeQTree_injective hab
        have hlast := congrArg List.getLast? heq
        simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
          List.getLast?_singleton, Option.some.injEq] at hlast
        exact congrArg (fun z => (OrderDual.ofDual z).val) hlast
    have hf_sub : (Finset.range j.val).image f ⊆
        (Finset.range (encodeQTree (p ++ [OrderDual.toDual j]))).filter
          (· ∈ Set.range encodeQTree) := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨k, hk, rfl⟩ := hm
      rw [Finset.mem_range] at hk
      rw [Finset.mem_filter, Finset.mem_range]
      by_cases hk0 : k = 0
      · simp only [f, hk0, ↓reduceDIte]
        refine ⟨?_, ⟨p, rfl⟩⟩
        rw [encodeQTree_append_singleton, OrderDual.ofDual_toDual]
        have := nat_pair_ge_right j.val (encodeQTree p)
        omega
      · simp only [f, hk0, ↓reduceDIte]
        refine ⟨?_, ⟨_, rfl⟩⟩
        rw [encodeQTree_append_singleton, encodeQTree_append_singleton]
        show Nat.pair k (encodeQTree p) + 1 < Nat.pair j.val (encodeQTree p) + 1
        have := nat_pair_lt_of_lt_left (b := encodeQTree p) hk
        omega
    rw [Nat.count_eq_card_filter_range]
    have hcard : ((Finset.range j.val).image f).card = j.val := by
      rw [Finset.card_image_of_injOn hf_inj, Finset.card_range]
    exact hcard ▸ Finset.card_le_card hf_sub

end ConcreteQTreeEnum

end Research.ChenWangSec32
