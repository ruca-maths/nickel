import Mathlib.Order.Interval.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Topology.Constructions
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

end Research.ChenWangSec32
