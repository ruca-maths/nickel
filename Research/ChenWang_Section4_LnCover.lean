import Mathlib.Order.Interval.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Defs.D_0003
import Defs.D_0005
import Defs.D_0007
import Defs.D_0009
import Defs.D_0011
import Defs.D_0012

/-!
# Chen–Wang (arXiv:1809.03763v2) Section 4: `Defs.D_0012` Bridge, Automatic Shrinking (Prop 3.3.1), Operation O1, Ln Covers, and Proposition 4.8 / Corollary 4.9

Built directly on top of `Defs.D_0003`, `Defs.D_0005`, `Defs.D_0007`, `Defs.D_0009`,
`Defs.D_0011`, and `Defs.D_0012` (`Hcell`, `gfun`, `hidx`, `lvl`, `ibase`, `ival`) with
zero `sorry` and standard axioms only.

Key results:
1. **Automatic shrinking without any extra `Tree2` axiom** (`Ico_inter_eq_singleton` &
   `gfun_inter_eq_singleton`, Proposition 3.3.1):
   For *every* `T : Tree2 α` and `q : ℕ ≃ α`, `⋂ a, [p, child p (a + 1)) = {p}` and
   `⋂ n, gfun q T (n + 1) x = {x}` follow directly from `Defs.D_0003.Tree2` alone.
2. **Propositions 3.2, 3.3, and 3.5.3 directly on `Defs.D_0012.Hcell` / `gfun`** under `Tree2Enum T q`:
   - `Hcell_gfun_eq_of_mem` (Note D2), `gfun_laminar` (Prop 3.3.8), `H_disjoint_gfun_of_lt` (Prop 3.3.6),
   - `hidx_lt_of_Hcell_inter_gfun` (Prop 3.3.6'), `gfun_trans` (Prop 3.3.4),
   - `gfun_antitone` (Prop 3.3.5), `Hcell_antitone`, `Hcell_chain_inter_eq_singleton` (Prop 3.5.3).
3. **Section 4 — Fact 4.0, Operation O1, Claim 4.1, Definition Ln, Fact \*, Proposition 4.8 & Corollary 4.9**:
   - `fact_4_0`: `0 < m ≤ l → (Hcell l y ∩ gfun m x).Nonempty → gfun l y ⊆ gfun m x`.
   - `IsMinWitness` / `lnCoverW` / `lnCoverG` / `lnCoverH`: clean non-recursive characterization
     of Operation O1 on any `n`-saturated set `B`.
   - `lnCoverG_isLnCover` & `lnCoverG_coD` (Claim 4.1.1–4.1.4): c.o.D partition and refinement property.
   - `isLnCover_subfamily` (Fact \*): every subfamily of an Ln cover is an Ln cover on its union.
   - `prop_4_8_and_cor_4_9` (Proposition 4.8 & Corollary 4.9, cited directly in Proposition 9.5):
     for any `Hcell q T n x₀ ⊆ B`, there exists `a ≥ n` such that for all `l ≥ a`, the restricted
     Ln cover `W' := { w ∈ lnCoverW l B | (gfun l w ∩ Hcell n x₀).Nonempty }` satisfies
     `⋃ w ∈ W', Hcell l w ⊆ Hcell n x₀ ⊆ ⋃ w ∈ W', gfun l w`.
-/

namespace Research.ChenWangSec4

open Relation Set
open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0005 Defs.D_0007 Defs.D_0009 Defs.D_0011 Defs.D_0012

section ShrinkingAndProp32

variable {α : Type} [LinearOrder α]

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
    | @tail b c _ hbc ih =>
      intro hpc hca
      rcases lt_trichotomy b p with hbp | rfl | hpb
      · have hlev : T.lev b < T.lev p := by
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
    have h1 : T.child p a ≤ T.child p (T.idx c) :=
      child_le_child T p (T.idx_pos p c hpc) (not_lt.mp hnot)
    rw [child_eq T hpc] at h1
    exact absurd (lt_of_le_of_lt (le_trans h1 (desc_le T hcy)) hy.2) (lt_irrefl _)
  refine ⟨T.idx c, hl, ?_⟩
  rwa [child_eq T hpc]

/-- Automatic interval shrinking on *any* `Defs.D_0003.Tree2 α` (no extra axiom needed):
`⋂ a, [p, child p (a + 1)) = {p}`. -/
theorem Ico_inter_eq_singleton (T : Tree2 α) (p : α) :
    (⋂ a : ℕ, Set.Ico p (T.child p (a + 1))) = {p} := by
  ext z
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro hz
    have h1 := hz 0
    rcases eq_or_lt_of_le h1.1 with heq | hlt
    · exact heq.symm
    · obtain ⟨l, hl, hdesc⟩ := exists_child_desc_of_mem_Ioo T Nat.one_pos ⟨hlt, h1.2⟩
      have hle : T.child p l ≤ z := desc_le T hdesc
      have hzl : z < T.child p l := by
        have h := (hz (l - 1)).2
        have hl' : l - 1 + 1 = l := by omega
        rwa [hl'] at h
      exact absurd (lt_of_le_of_lt hle hzl) (lt_irrefl _)
  · intro hz a
    rw [hz]
    exact ⟨le_rfl, T.lt_child _ _ (T.C_child p (a + 1) (Nat.succ_pos a))⟩

/-- Pointwise separation lemma: if `z ≠ p`, then `z ∉ [p, child p a)` for some `a > 0`. -/
theorem exists_not_mem_Ico_of_ne (T : Tree2 α) {p z : α} (hne : z ≠ p) :
    ∃ a : ℕ, 0 < a ∧ z ∉ Set.Ico p (T.child p a) := by
  by_contra hall
  push Not at hall
  have hmem : z ∈ (⋂ a : ℕ, Set.Ico p (T.child p (a + 1))) := by
    rw [Set.mem_iInter]
    intro a
    exact hall (a + 1) (Nat.succ_pos a)
  rw [Ico_inter_eq_singleton T p, Set.mem_singleton_iff] at hmem
  exact hne hmem

/-- Chen–Wang Proposition 3.3.1 on `Defs.D_0012.gfun` (without any extra axiom):
`⋂ n, gfun q T (n + 1) x = {x}`. -/
theorem gfun_inter_eq_singleton (q : ℕ ≃ α) (T : Tree2 α) (x : ℕ → α) :
    (⋂ n : ℕ, gfun q T (n + 1) x) = {x} := by
  ext z
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro hz
    funext k
    have hmem : z k ∈ (⋂ a : ℕ, Set.Ico (x k) (T.child (x k) (a + 1))) := by
      rw [Set.mem_iInter]
      intro a
      let m := max k a
      have hzm := (hz m).1 k (by omega)
      have hle : a + 1 ≤ lvl q (m + 1) x := by unfold lvl; omega
      exact Set.Ico_subset_Ico_right (child_le_child T (x k) (Nat.succ_pos a) hle) hzm
    rw [Ico_inter_eq_singleton T (x k), Set.mem_singleton_iff] at hmem
    exact hmem
  · intro hz n
    rw [hz]
    exact mem_gfun q T (n + 1) x

/-- Compatibility between `Tree2 α` and `q : ℕ ≃ α` (Chen–Wang Prop 2.1.1 & 2.1.3). -/
structure Tree2Enum (T : Tree2 α) (q : ℕ ≃ α) : Prop where
  child_enum_gt : ∀ p c, T.C p c → q.symm p < q.symm c
  idx_le_enum : ∀ p c, T.C p c → T.idx c ≤ q.symm c

theorem enum_le_of_desc {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {p y : α} (h : ReflTransGen T.C p y) : q.symm p ≤ q.symm y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (E.child_enum_gt _ _ hbc).le

/-- Chen–Wang Proposition 3.2.1. -/
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

/-- Chen–Wang Proposition 3.2.3. -/
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

end ShrinkingAndProp32

section D0012Bridge

variable {α : Type} [LinearOrder α]

/-- Two `ival T a` blocks sharing a point are identical. -/
theorem ival_eq_of_inter (T : Tree2 α) {a : ℕ} (ha : 0 < a) {r₁ r₂ w : α}
    (h1 : w ∈ ival T a r₁) (h2 : w ∈ ival T a r₂) :
    ival T a r₁ = ival T a r₂ := by
  have hq1 := (ibase_spec T ha r₁).1
  have hq2 := (ibase_spec T ha r₂).1
  have heq : ibase T a r₁ = ibase T a r₂ := by
    by_contra hne
    exact Set.disjoint_left.mp (prop_2_2_1_disjoint T ha hq1 hq2 hne) h1 h2
  simp only [ival, heq]

/-- If `0 < a ≤ b` and `ival T a r₁` intersects `ival T b r₂`, then `ival T b r₂ ⊆ ival T a r₁`. -/
theorem ival_subset_of_le_of_inter (T : Tree2 α) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    {r₁ r₂ w : α} (h1 : w ∈ ival T a r₁) (h2 : w ∈ ival T b r₂) :
    ival T b r₂ ⊆ ival T a r₁ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rcases prop_2_2_5 T ha hab (ibase_spec T ha r₁).1 (ibase_spec T hb r₂).1 with hdisj | hsub
  · exact (Set.disjoint_left.mp hdisj h1 h2).elim
  · exact hsub

omit [LinearOrder α] in
/-- `hidx q n x` agrees on any two points sharing their first `n` coordinates. -/
theorem hidx_eq_of_prefix (q : ℕ ≃ α) {n : ℕ} (hn : 0 < n) {x y : ℕ → α}
    (h : ∀ k < n, y k = x k) : hidx q n y = hidx q n x :=
  (code_eq_iff n hn _ _).mpr fun k hk => by rw [h k hk]

omit [LinearOrder α] in
/-- Coordinate index bound: for `k < n`, `q.symm (x k) < lvl q n x`. -/
theorem coord_idx_lt_lvl (q : ℕ ≃ α) (n : ℕ) (x : ℕ → α) {k : ℕ} (hk : k < n) :
    q.symm (x k) < lvl q n x := by
  have hle : q.symm (x k) ≤ hidx q n x := code_ge n (fun j => q.symm (x j)) k hk
  unfold lvl; omega

/-- Note D2 on `Defs.D_0012`: if `y ∈ Hcell q T n x` (`n > 0`), then `Hcell` and `gfun` coincide. -/
theorem Hcell_gfun_eq_of_mem (q : ℕ ≃ α) (T : Tree2 α) {n : ℕ} (hn : 0 < n) {x y : ℕ → α}
    (hy : y ∈ Hcell q T n x) :
    Hcell q T n y = Hcell q T n x ∧ gfun q T n y = gfun q T n x := by
  have hc : hidx q n y = hidx q n x := hidx_eq_of_prefix q hn hy.1
  have hl : lvl q n y = lvl q n x := by simp only [lvl, hc]
  have hival : ∀ k, n ≤ k → k < n + hidx q n x + 1 →
      ival T (lvl q n x) (y k) = ival T (lvl q n x) (x k) := fun k hk1 hk2 =>
    ival_eq_of_inter T (lvl_pos q n x) (mem_ival T (lvl_pos q n x) (y k)) (hy.2 k hk1 hk2)
  constructor
  · ext z
    simp only [Hcell, Set.mem_ofPred_eq, hc, hl]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun k hk => (h1 k hk).trans (hy.1 k hk),
        fun k hk1 hk2 => by rw [← hival k hk1 hk2]; exact h2 k hk1 hk2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun k hk => (h1 k hk).trans (hy.1 k hk).symm,
        fun k hk1 hk2 => by rw [hival k hk1 hk2]; exact h2 k hk1 hk2⟩
  · ext z
    simp only [gfun, Set.mem_ofPred_eq, hc, hl]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun k hk => by rw [← hy.1 k hk]; exact h1 k hk,
        fun k hk1 hk2 => by rw [← hival k hk1 hk2]; exact h2 k hk1 hk2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun k hk => by rw [hy.1 k hk]; exact h1 k hk,
        fun k hk1 hk2 => by rw [hival k hk1 hk2]; exact h2 k hk1 hk2⟩

/-- Same-`hidx` dichotomy: if `hidx q n x = hidx q n y`, then `gfun q T n x` and `gfun q T n y`
are either equal or disjoint. -/
theorem gfun_eq_or_disjoint_of_hidx_eq (q : ℕ ≃ α) (T : Tree2 α) {n : ℕ} (hn : 0 < n)
    {x y : ℕ → α} (hc : hidx q n x = hidx q n y) :
    gfun q T n x = gfun q T n y ∨ Disjoint (gfun q T n x) (gfun q T n y) := by
  by_cases hd : Disjoint (gfun q T n x) (gfun q T n y)
  · exact Or.inr hd
  · left
    obtain ⟨w, hwx, hwy⟩ := Set.not_disjoint_iff.mp hd
    have hpref : ∀ k < n, x k = y k :=
      (mem_H_iff_same q n hn x y).mp hc
    have hl : lvl q n x = lvl q n y := by simp only [lvl, hc]
    have hival : ∀ k, n ≤ k → k < n + hidx q n x + 1 →
        ival T (lvl q n x) (x k) = ival T (lvl q n y) (y k) := fun k hk1 hk2 => by
      rw [← hl]
      exact ival_eq_of_inter T (lvl_pos q n x) (hwx.2 k hk1 hk2)
        (by rw [hl]; exact hwy.2 k hk1 (hc ▸ hk2))
    ext z
    simp only [gfun, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun k hk => by rw [← hpref k hk, ← hl]; exact h1 k hk, fun k hk1 hk2 => ?_⟩
      rw [← hival k hk1 (hc.symm ▸ hk2)]
      exact h2 k hk1 (hc.symm ▸ hk2)
    · rintro ⟨h1, h2⟩
      refine ⟨fun k hk => by rw [hpref k hk, hl]; exact h1 k hk, fun k hk1 hk2 => ?_⟩
      rw [hival k hk1 hk2]
      exact h2 k hk1 (hc ▸ hk2)

/-- Chen–Wang Proposition 3.3.8 on `Defs.D_0012.gfun`. -/
theorem gfun_laminar {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} {x y : ℕ → α} (hcc : hidx q n x < hidx q n y) :
    Disjoint (gfun q T n x) (gfun q T n y) ∨ gfun q T n y ⊆ gfun q T n x := by
  by_cases hd : Disjoint (gfun q T n x) (gfun q T n y)
  · exact Or.inl hd
  · right
    obtain ⟨w, hwx, hwy⟩ := Set.not_disjoint_iff.mp hd
    have ha : 0 < lvl q n x := lvl_pos q n x
    have hab : lvl q n x ≤ lvl q n y := by unfold lvl; omega
    intro z hz
    constructor
    · intro k hk
      have h3 := prop_3_2_3 E (i := q.symm (x k)) (j := q.symm (y k)) ha hab
        (coord_idx_lt_lvl q n x hk)
      simp only [Equiv.apply_symm_apply] at h3
      rcases h3 with hdisj | hsub
      · exact (Set.disjoint_left.mp hdisj (hwx.1 k hk) (hwy.1 k hk)).elim
      · exact hsub (hz.1 k hk)
    · intro k hk1 hk2
      have hsub := ival_subset_of_le_of_inter T ha hab
        (hwx.2 k hk1 hk2) (hwy.2 k hk1 (by omega))
      exact hsub (hz.2 k hk1 (by omega))

/-- Chen–Wang Proposition 3.3.6 on `Defs.D_0012`:
If `hidx q n x < hidx q n y` (`n > 0`), then `H q n (hidx q n x)` is disjoint from `gfun q T n y`. -/
theorem H_disjoint_gfun_of_lt {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {x y : ℕ → α} (hcc : hidx q n x < hidx q n y) :
    Disjoint (H q n (hidx q n x)) (gfun q T n y) := by
  rw [Set.disjoint_left]
  intro w hwx hwy
  have hne : ∃ k < n, x k ≠ y k := by
    by_contra hall
    push Not at hall
    have : hidx q n x = hidx q n y := (code_eq_iff n hn _ _).mpr fun k hk => by rw [hall k hk]
    omega
  obtain ⟨k, hk, hkne⟩ := hne
  have hwk : w k = x k := (mem_H_iff_same q n hn w x).mp hwx k hk
  have hwI : x k ∈ Set.Ico (y k) (T.child (y k) (lvl q n y)) := by
    rw [← hwk]; exact hwy.1 k hk
  have hIoo : q (q.symm (x k)) ∈ Set.Ioo (q (q.symm (y k)))
      (T.child (q (q.symm (y k))) (lvl q n y)) := by
    simp only [Equiv.apply_symm_apply]
    exact ⟨lt_of_le_of_ne hwI.1 hkne.symm, hwI.2⟩
  have hgt : lvl q n y < q.symm (x k) := (prop_3_2_1 E (lvl_pos q n y) Nat.one_pos hIoo).2.1
  have hlt : q.symm (x k) < lvl q n x := coord_idx_lt_lvl q n x hk
  unfold lvl at hgt hlt
  omega

/-- Chen–Wang Proposition 3.3.6' on `Defs.D_0012`. -/
theorem hidx_lt_of_Hcell_inter_gfun {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {y z : ℕ → α}
    (hinter : (Hcell q T n y ∩ gfun q T n z).Nonempty)
    (hne : Hcell q T n y ≠ Hcell q T n z) :
    hidx q n z < hidx q n y := by
  obtain ⟨w, hwy, hwz⟩ := hinter
  by_contra hnot
  rcases lt_or_eq_of_le (not_lt.mp hnot) with hlt | heq
  · have hwH : w ∈ H q n (hidx q n y) :=
      (mem_H_iff_same q n hn w y).mpr hwy.1
    exact Set.disjoint_left.mp (H_disjoint_gfun_of_lt E hn hlt) hwH hwz
  · have hwH : w ∈ H q n (hidx q n z) := by
      rw [← heq]
      exact (mem_H_iff_same q n hn w y).mpr hwy.1
    have hwHz : w ∈ Hcell q T n z := by
      rw [← gfun_inter_H q T n hn z]
      exact ⟨hwz, hwH⟩
    have e1 := (Hcell_gfun_eq_of_mem q T hn hwy).1
    have e2 := (Hcell_gfun_eq_of_mem q T hn hwHz).1
    exact hne (e1.symm.trans e2)

/-- Chen–Wang Proposition 3.3.4 on `Defs.D_0012` (transitivity of `gfun`). -/
theorem gfun_trans {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {x y : ℕ → α} (hy : y ∈ gfun q T n x) :
    gfun q T n y ⊆ gfun q T n x := by
  by_cases hH : y ∈ Hcell q T n x
  · rw [(Hcell_gfun_eq_of_mem q T hn hH).2]
  · have hne : Hcell q T n y ≠ Hcell q T n x := fun h => hH (h ▸ mem_Hcell q T n y)
    have hlt : hidx q n x < hidx q n y :=
      hidx_lt_of_Hcell_inter_gfun E hn ⟨y, mem_Hcell q T n y, hy⟩ hne
    rcases gfun_laminar E hlt with hdisj | hsub
    · exact (Set.disjoint_left.mp hdisj hy (mem_gfun q T n y)).elim
    · exact hsub

/-- Chen–Wang Proposition 3.3.5 on `Defs.D_0012`: `gfun q T (n + 1) x ⊆ gfun q T n x`. -/
theorem gfun_succ_subset {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) (x : ℕ → α) :
    gfun q T (n + 1) x ⊆ gfun q T n x := by
  have hc : hidx q n x ≤ hidx q (n + 1) x := code_mono n hn _ (n + 1) (Nat.le_succ n)
  have ha : 0 < lvl q n x := lvl_pos q n x
  have hb : 0 < lvl q (n + 1) x := lvl_pos q (n + 1) x
  have hab : lvl q n x ≤ lvl q (n + 1) x := by unfold lvl; omega
  intro z hz
  constructor
  · intro k hk
    exact Set.Ico_subset_Ico_right (child_le_child T (x k) ha hab) (hz.1 k (Nat.lt_succ_of_lt hk))
  · intro k hk1 hk2
    rcases eq_or_lt_of_le hk1 with rfl | hlt
    · have hzn := hz.1 n (Nat.lt_succ_self n)
      have hxn : x n ∈ ival T (lvl q n x) (x n) := mem_ival T ha (x n)
      rcases eq_or_lt_of_le hxn.1 with heq | hlt'
      · rw [← heq] at hzn
        exact Set.Ico_subset_Ico_right (child_le_child T _ ha hab) hzn
      · have hIoo : q (q.symm (x n)) ∈ Set.Ioo (q (q.symm (ibase T (lvl q n x) (x n))))
            (T.child (q (q.symm (ibase T (lvl q n x) (x n)))) (lvl q n x)) := by
          simp only [Equiv.apply_symm_apply]
          exact ⟨hlt', hxn.2⟩
        have hsub := (prop_3_2_1 E ha hb hIoo).2.2
        simp only [Equiv.apply_symm_apply] at hsub
        exact Set.Ioo_subset_Ico_self (hsub hzn)
    · have hsub := ival_subset_of_le_of_inter T ha hab
        (mem_ival T ha (x k)) (mem_ival T hb (x k))
      exact hsub (hz.2 k hlt (by omega))

/-- General monotonicity in `n`: `0 < n ≤ m → gfun q T m x ⊆ gfun q T n x`. -/
theorem gfun_antitone {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) (x : ℕ → α) :
    gfun q T m x ⊆ gfun q T n x := by
  induction hnm with
  | refl => exact Subset.rfl
  | @step k hnk ih => exact (gfun_succ_subset E (lt_of_lt_of_le hn hnk) x).trans ih

/-- Monotonicity of `Hcell` in `n`: `0 < n ≤ m → Hcell q T m x ⊆ Hcell q T n x`. -/
theorem Hcell_antitone (q : ℕ ≃ α) (T : Tree2 α)
    {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) (x : ℕ → α) :
    Hcell q T m x ⊆ Hcell q T n x := by
  have hc : hidx q n x ≤ hidx q m x := code_mono n hn _ m hnm
  have ha : 0 < lvl q n x := lvl_pos q n x
  have hb : 0 < lvl q m x := lvl_pos q m x
  have hab : lvl q n x ≤ lvl q m x := by unfold lvl; omega
  intro z hz
  constructor
  · intro k hk
    exact hz.1 k (lt_of_lt_of_le hk hnm)
  · intro k hk1 hk2
    by_cases hkm : k < m
    · rw [hz.1 k hkm]
      exact mem_ival T ha (x k)
    · have hsub := ival_subset_of_le_of_inter T ha hab
        (mem_ival T ha (x k)) (mem_ival T hb (x k))
      exact hsub (hz.2 k (not_lt.mp hkm) (by omega))

/-- Chen–Wang Proposition 3.5.3 directly on `Defs.D_0012.Hcell`. -/
theorem Hcell_chain_inter_eq_singleton (q : ℕ ≃ α) (T : Tree2 α)
    (n : ℕ → ℕ) (hn_mono : StrictMono n)
    (y : ℕ → (ℕ → α)) (hchain : ∀ i, Hcell q T (n (i + 1)) (y (i + 1)) ⊆ Hcell q T (n i) (y i)) :
    ∃ t : ℕ → α, (⋂ i : ℕ, Hcell q T (n i) (y i)) = {t} := by
  have hsub : ∀ {i j : ℕ}, i ≤ j → Hcell q T (n j) (y j) ⊆ Hcell q T (n i) (y i) := by
    intro i j hij
    induction hij with
    | refl => exact Subset.rfl
    | @step m _ ih => exact (hchain m).trans ih
  have hn_ge : ∀ k, k ≤ n k := fun k => hn_mono.id_le k
  have hagree : ∀ {i j k : ℕ}, i ≤ j → k < n i → y j k = y i k := by
    intro i j k hij hk
    exact (hsub hij (mem_Hcell q T (n j) (y j))).1 k hk
  let t : ℕ → α := fun k => y (k + 1) k
  refine ⟨t, ?_⟩
  ext w
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro hw
    funext k
    exact (hw (k + 1)).1 k (lt_of_lt_of_le (Nat.lt_succ_self k) (hn_ge (k + 1)))
  · intro hw i
    rw [hw]
    let m := max i (n i + hidx q (n i) (y i) + 1)
    have hym : y m ∈ Hcell q T (n i) (y i) := hsub (le_max_left _ _) (mem_Hcell q T (n m) (y m))
    have ht_eq : ∀ k < n i + hidx q (n i) (y i) + 1, t k = y m k := fun k hk =>
      (hagree (by omega : k + 1 ≤ m) (lt_of_lt_of_le (Nat.lt_succ_self k) (hn_ge (k + 1)))).symm
    exact ⟨fun k hk => (ht_eq k (by omega)).trans (hym.1 k hk),
      fun k hk1 hk2 => by rw [ht_eq k hk2]; exact hym.2 k hk1 hk2⟩

end D0012Bridge

section Section4LnCovers

variable {α : Type} [LinearOrder α]

/-- Chen–Wang Fact 4.0:
If `0 < m ≤ l` and `Hcell q T l y ∩ gfun q T m x` is nonempty, then `gfun q T l y ⊆ gfun q T m x`. -/
theorem fact_4_0 {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {m l : ℕ} (hm : 0 < m) (hml : m ≤ l) {x y : ℕ → α}
    (hinter : (Hcell q T l y ∩ gfun q T m x).Nonempty) :
    gfun q T l y ⊆ gfun q T m x := by
  obtain ⟨z, hzy, hzx⟩ := hinter
  have hl : 0 < l := lt_of_lt_of_le hm hml
  rw [← (Hcell_gfun_eq_of_mem q T hl hzy).2]
  exact (gfun_antitone E hm hml z).trans (gfun_trans E hm hzx)

/-- `B` is `n`-saturated if `x ∈ B → gfun q T n x ⊆ B`. -/
def IsSaturated (q : ℕ ≃ α) (T : Tree2 α) (n : ℕ) (B : Set (ℕ → α)) : Prop :=
  ∀ x ∈ B, gfun q T n x ⊆ B

theorem isSaturated_gfun {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (y₀ : ℕ → α) :
    IsSaturated q T n (gfun q T m y₀) :=
  fun x hx => (gfun_antitone E hm hmn x).trans (gfun_trans E hm hx)

theorem isSaturated_mono {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {B : Set (ℕ → α)} (hB : IsSaturated q T m B) :
    IsSaturated q T n B :=
  fun x hx => (gfun_antitone E hm hmn x).trans (hB x hx)

/-- Non-recursive exact characterization of Operation O1:
`x ∈ B` is selected into `H^1_B = ⋃ ℋ(n, B, 0)` iff no `y ∈ B` with strictly smaller `hidx` covers `x`. -/
def IsMinWitness (q : ℕ ≃ α) (T : Tree2 α) (n : ℕ) (B : Set (ℕ → α)) (x : ℕ → α) : Prop :=
  x ∈ B ∧ ∀ y ∈ B, hidx q n y < hidx q n x → x ∉ gfun q T n y

/-- Operation O1 witness set `H^1_B`. -/
def lnCoverW (q : ℕ ≃ α) (T : Tree2 α) (n : ℕ) (B : Set (ℕ → α)) : Set (ℕ → α) :=
  { x | IsMinWitness q T n B x }

/-- Operation O1 cover `𝒢(n, B, 0) = { gfun q T n x | x ∈ lnCoverW }`. -/
noncomputable def lnCoverG (q : ℕ ≃ α) (T : Tree2 α) (n : ℕ) (B : Set (ℕ → α)) : Set (Set (ℕ → α)) :=
  (gfun q T n) '' lnCoverW q T n B

/-- Operation O1 `H`-family `ℋ(n, B, 0) = { Hcell q T n x | x ∈ lnCoverW }`. -/
noncomputable def lnCoverH (q : ℕ ≃ α) (T : Tree2 α) (n : ℕ) (B : Set (ℕ → α)) : Set (Set (ℕ → α)) :=
  (Hcell q T n) '' lnCoverW q T n B

/-- Definition Ln (Chen–Wang Section 4, Claim 4.1 conditions 1, 2, 4):
`𝒢` is a least-number cover (Ln cover) on `(n, B)` if:
1. Every `U ∈ 𝒢` is of the form `gfun q T n x` (hence clopen in `xtop α`) and `⋃₀ 𝒢 = B`;
2. Distinct members of `𝒢` are pairwise disjoint (hence `𝒢` is a c.o.D partition of `B`);
3. For every `l ≥ n` and `y` with `gfun q T l y ⊆ B`, there exists `U ∈ 𝒢` with `gfun q T l y ⊆ U`. -/
structure IsLnCover (q : ℕ ≃ α) (T : Tree2 α) (n : ℕ) (B : Set (ℕ → α))
    (𝒢 : Set (Set (ℕ → α))) : Prop where
  mem_gfun : ∀ U ∈ 𝒢, ∃ x, U = gfun q T n x
  sUnion_eq : ⋃₀ 𝒢 = B
  pairwiseDisjoint : 𝒢.PairwiseDisjoint id
  refines : ∀ l ≥ n, ∀ y, gfun q T l y ⊆ B → ∃ U ∈ 𝒢, gfun q T l y ⊆ U

/-- Claim 4.1.1: `⋃₀ lnCoverG q T n B = B` for any `n`-saturated `B`. -/
theorem lnCoverG_sUnion_eq {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {B : Set (ℕ → α)} (hB : IsSaturated q T n B) :
    ⋃₀ lnCoverG q T n B = B := by
  classical
  ext z
  simp only [Set.mem_sUnion, lnCoverG, Set.mem_image, lnCoverW, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hzx⟩
    exact hB x hx.1 hzx
  · intro hz
    have hex : ∃ c, ∃ y ∈ B, hidx q n y = c ∧ z ∈ gfun q T n y :=
      ⟨hidx q n z, z, hz, rfl, mem_gfun q T n z⟩
    let c₀ := Nat.find hex
    obtain ⟨y₀, hy₀B, hy₀c, hzy₀⟩ := Nat.find_spec hex
    refine ⟨gfun q T n y₀, ⟨y₀, ⟨hy₀B, ?_⟩, rfl⟩, hzy₀⟩
    intro y hyB hlt hy₀y
    have hzy : z ∈ gfun q T n y := gfun_trans E hn hy₀y hzy₀
    have hge : c₀ ≤ hidx q n y := Nat.find_min' hex ⟨y, hyB, rfl, hzy⟩
    omega

/-- Claim 4.1.2: distinct elements of `lnCoverG q T n B` are pairwise disjoint. -/
theorem lnCoverG_pairwiseDisjoint {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) (B : Set (ℕ → α)) :
    (lnCoverG q T n B).PairwiseDisjoint id := by
  rintro U ⟨x, hx, rfl⟩ V ⟨y, hy, rfl⟩ hne
  rcases lt_trichotomy (hidx q n x) (hidx q n y) with hlt | heq | hgt
  · rcases gfun_laminar E hlt with hdisj | hsub
    · exact hdisj
    · exact absurd (hsub (mem_gfun q T n y)) (hy.2 x hx.1 hlt)
  · rcases gfun_eq_or_disjoint_of_hidx_eq q T hn heq with heqG | hdisj
    · exact absurd heqG hne
    · exact hdisj
  · rcases gfun_laminar E hgt with hdisj | hsub
    · exact hdisj.symm
    · exact absurd (hsub (mem_gfun q T n x)) (hx.2 y hy.1 hgt)

/-- Claim 4.1 (conditions 1, 2, 4): `lnCoverG q T n B` is an Ln cover on `(n, B)`. -/
theorem lnCoverG_isLnCover {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {B : Set (ℕ → α)} (hB : IsSaturated q T n B) :
    IsLnCover q T n B (lnCoverG q T n B) where
  mem_gfun := by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩
  sUnion_eq := lnCoverG_sUnion_eq E hn hB
  pairwiseDisjoint := lnCoverG_pairwiseDisjoint E hn B
  refines := by
    intro l hl y hyB
    have hy : y ∈ ⋃₀ lnCoverG q T n B := by
      rw [lnCoverG_sUnion_eq E hn hB]
      exact hyB (mem_gfun q T l y)
    obtain ⟨U, ⟨x, hx, rfl⟩, hyU⟩ := Set.mem_sUnion.mp hy
    exact ⟨gfun q T n x, ⟨x, hx, rfl⟩, (gfun_antitone E hn hl y).trans (gfun_trans E hn hyU)⟩

/-- Claim 4.1.2 (topological c.o.D property): every `U ∈ lnCoverG q T n B` is clopen in `xtop α`,
and the family is discrete on `B` (every `z ∈ B` has a clopen neighborhood meeting at most one member). -/
theorem lnCoverG_coD {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {B : Set (ℕ → α)} (hB : IsSaturated q T n B) :
    (∀ U ∈ lnCoverG q T n B, @IsOpen (ℕ → α) (xtop α) U ∧ @IsClosed (ℕ → α) (xtop α) U) ∧
    (∀ z ∈ B, ∃ V, @IsOpen (ℕ → α) (xtop α) V ∧ z ∈ V ∧
      ∀ U₁ ∈ lnCoverG q T n B, ∀ U₂ ∈ lnCoverG q T n B,
        (U₁ ∩ V).Nonempty → (U₂ ∩ V).Nonempty → U₁ = U₂) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact gfun_isClopen q T n x
  · intro z hz
    rw [← lnCoverG_sUnion_eq E hn hB] at hz
    obtain ⟨V, ⟨x, hx, rfl⟩, hzV⟩ := Set.mem_sUnion.mp hz
    have hVmem : gfun q T n x ∈ lnCoverG q T n B := ⟨x, hx, rfl⟩
    refine ⟨gfun q T n x, (gfun_isClopen q T n x).1, hzV, ?_⟩
    intro U₁ hU₁ U₂ hU₂ ⟨w₁, hw₁U, hw₁V⟩ ⟨w₂, hw₂U, hw₂V⟩
    have h1 : U₁ = gfun q T n x := by
      by_contra hne
      exact Set.disjoint_left.mp (lnCoverG_pairwiseDisjoint E hn B hU₁ hVmem hne) hw₁U hw₁V
    have h2 : U₂ = gfun q T n x := by
      by_contra hne
      exact Set.disjoint_left.mp (lnCoverG_pairwiseDisjoint E hn B hU₂ hVmem hne) hw₂U hw₂V
    rw [h1, h2]

/-- Claim 4.1.3: `lnCoverW` is closed under `Hcell`, so `⋃₀ lnCoverH q T n B = lnCoverW q T n B`. -/
theorem lnCoverH_sUnion_eq {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {B : Set (ℕ → α)} (hB : IsSaturated q T n B) :
    ⋃₀ lnCoverH q T n B = lnCoverW q T n B := by
  ext z
  simp only [Set.mem_sUnion, lnCoverH, Set.mem_image, lnCoverW, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hzx⟩
    refine ⟨hB x hx.1 (Hcell_sub_gfun q T n x hzx), ?_⟩
    intro y hyB hlt hzy
    have hc : hidx q n z = hidx q n x := hidx_eq_of_prefix q hn hzx.1
    have hg : gfun q T n x = gfun q T n z := (Hcell_gfun_eq_of_mem q T hn hzx).2.symm
    have hxy : x ∈ gfun q T n y :=
      gfun_trans E hn hzy (hg ▸ mem_gfun q T n x)
    exact hx.2 y hyB (hc ▸ hlt) hxy
  · intro hz
    exact ⟨Hcell q T n z, ⟨z, hz, rfl⟩, mem_Hcell q T n z⟩

/-- Chen–Wang Fact \*: any subfamily `𝒢' ⊆ 𝒢` of an Ln cover on `(n, B)` is an Ln cover on `(n, ⋃₀ 𝒢')`. -/
theorem isLnCover_subfamily {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) {B : Set (ℕ → α)} {𝒢 𝒢' : Set (Set (ℕ → α))}
    (h𝒢 : IsLnCover q T n B 𝒢) (hsub : 𝒢' ⊆ 𝒢) :
    IsLnCover q T n (⋃₀ 𝒢') 𝒢' where
  mem_gfun := fun U hU => h𝒢.mem_gfun U (hsub hU)
  sUnion_eq := rfl
  pairwiseDisjoint := h𝒢.pairwiseDisjoint.subset hsub
  refines := by
    intro l hl y hy
    obtain ⟨U, hU, hyU⟩ := Set.mem_sUnion.mp (hy (mem_gfun q T l y))
    obtain ⟨x, rfl⟩ := h𝒢.mem_gfun U (hsub hU)
    exact ⟨gfun q T n x, hU, (gfun_antitone E hn hl y).trans (gfun_trans E hn hyU)⟩

/-- Chen–Wang Proposition 4.8 & Corollary 4.9 (directly cited in Proposition 9.5):
For any `0 < n` and `x₀ : ℕ → α`, there exists `a ≥ n` such that for *every* `l ≥ a` and *every* `w`,
if `gfun q T l w ∩ Hcell q T n x₀` is nonempty, then `Hcell q T l w ⊆ Hcell q T n x₀`.
Consequently, for any `m`-saturated `B` (`0 < m ≤ n`) containing `x₀` (e.g. `B = gfun q T m y₀`),
restricting the Ln cover `lnCoverW q T l B` to `W' := { w ∈ lnCoverW l B | (gfun l w ∩ Hcell n x₀).Nonempty }`
satisfies `⋃ w ∈ W', Hcell q T l w ⊆ Hcell q T n x₀ ⊆ ⋃ w ∈ W', gfun q T l w`. -/
theorem exists_level_Hcell_subset_of_inter {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {n : ℕ} (hn : 0 < n) (x₀ : ℕ → α) :
    ∃ a ≥ n, ∀ l ≥ a, ∀ w : ℕ → α,
      (gfun q T l w ∩ Hcell q T n x₀).Nonempty →
      Hcell q T l w ⊆ Hcell q T n x₀ := by
  classical
  let c₀ := hidx q n x₀
  -- For each `c < c₀`, pick a coordinate `k < n` where `H q n c` differs from `x₀`, and a shrinking level `a_c`
  have hsep : ∀ c < c₀, ∃ k < n, ∃ ac : ℕ, 0 < ac ∧
      ∀ w ∈ H q n c, x₀ k ∉ Set.Ico (w k) (T.child (w k) ac) := by
    intro c hc
    obtain ⟨w₀, hw₀⟩ := H_nonempty q n hn c
    have hne : ∃ k < n, x₀ k ≠ w₀ k := by
      by_contra hall
      push Not at hall
      have h1 : code n (fun j => q.symm (w₀ j)) = c := hw₀
      have h2 : code n (fun j => q.symm (x₀ j)) = code n (fun j => q.symm (w₀ j)) :=
        (code_eq_iff n hn _ _).mpr fun k hk => by rw [hall k hk]
      have : c₀ = c := h2.trans h1
      omega
    obtain ⟨k, hk, hkne⟩ := hne
    obtain ⟨ac, hac_pos, hac_not⟩ := exists_not_mem_Ico_of_ne T hkne
    refine ⟨k, hk, ac, hac_pos, fun w hw => ?_⟩
    have hwk : w k = w₀ k := by
      have hw' : w ∈ H q n (code n (fun j => q.symm (w₀ j))) := by
        have h1 : code n (fun j => q.symm (w₀ j)) = c := hw₀
        rwa [h1]
      exact (mem_H_iff_same q n hn w w₀).mp hw' k hk
    rwa [hwk]
  let aOf : ℕ → ℕ := fun c =>
    if h : c < c₀ then (hsep c h).choose_spec.2.choose else 0
  let a := max n ((Finset.range c₀).sup aOf)
  refine ⟨a, le_max_left _ _, fun l hl w ⟨z, hzw, hzx₀⟩ => ?_⟩
  have hnl : n ≤ l := le_trans (le_max_left _ _) hl
  have hzw_n : z ∈ gfun q T n w := gfun_antitone E hn hnl w hzw
  have hH_eq : Hcell q T n w = Hcell q T n x₀ := by
    by_contra hne
    have hlt : hidx q n w < c₀ :=
      hidx_lt_of_Hcell_inter_gfun E hn ⟨z, hzx₀, hzw_n⟩ (Ne.symm hne)
    let c := hidx q n w
    have hk_spec := (hsep c hlt).choose_spec
    let k := (hsep c hlt).choose
    have hk : k < n := hk_spec.1
    have hac_spec := hk_spec.2.choose_spec
    let ac := hk_spec.2.choose
    have hac_pos : 0 < ac := hac_spec.1
    have hac_le : ac ≤ a := by
      have hlt' : c < c₀ := hlt
      have h1 : ac = aOf c := by
        dsimp only [aOf]
        split_ifs
        rfl
      have h2 : aOf c ≤ (Finset.range c₀).sup aOf :=
        Finset.le_sup (f := aOf) (Finset.mem_range.mpr hlt')
      exact le_trans (h1 ▸ h2) (le_max_right _ _)
    have hzk : z k ∈ Set.Ico (w k) (T.child (w k) (lvl q l w)) :=
      hzw.1 k (lt_of_lt_of_le hk hnl)
    have hle_lvl : ac ≤ lvl q l w := by unfold lvl; omega
    have hzk' : z k ∈ Set.Ico (w k) (T.child (w k) ac) :=
      Set.Ico_subset_Ico_right (child_le_child T (w k) hac_pos hle_lvl) hzk
    rw [hzx₀.1 k hk] at hzk'
    exact hac_spec.2 w rfl hzk'
  exact (Hcell_antitone q T hn hnl w).trans hH_eq.subset

/-- Full Corollary 4.9 packaging with the Ln cover `lnCoverW q T l B`:
for every `l ≥ a`, the subfamily `W' = { w ∈ lnCoverW l B | (gfun l w ∩ Hcell n x₀).Nonempty }`
sandwiches `Hcell q T n x₀` between `⋃ w ∈ W', Hcell q T l w` and `⋃ w ∈ W', gfun q T l w`. -/
theorem prop_4_8_and_cor_4_9 {T : Tree2 α} {q : ℕ ≃ α} (E : Tree2Enum T q)
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {B : Set (ℕ → α)} (hB : IsSaturated q T m B)
    {x₀ : ℕ → α} (hx₀ : x₀ ∈ B) :
    ∃ a ≥ n, ∀ l ≥ a,
      let W' := { w ∈ lnCoverW q T l B | (gfun q T l w ∩ Hcell q T n x₀).Nonempty }
      (⋃ w ∈ W', Hcell q T l w) ⊆ Hcell q T n x₀ ∧
      Hcell q T n x₀ ⊆ (⋃ w ∈ W', gfun q T l w) := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  obtain ⟨a, ha, hmain⟩ := exists_level_Hcell_subset_of_inter E hn x₀
  refine ⟨a, ha, fun l hl => ?_⟩
  dsimp only
  have hml : m ≤ l := le_trans hmn (le_trans ha hl)
  have hl_pos : 0 < l := lt_of_lt_of_le hm hml
  have hBl : IsSaturated q T l B := isSaturated_mono E hm hml hB
  constructor
  · intro u hu
    simp only [Set.mem_iUnion, exists_prop] at hu
    obtain ⟨w, ⟨_, hinter⟩, huw⟩ := hu
    exact hmain l hl w hinter huw
  · intro z hz
    have hzB : z ∈ B :=
      hB x₀ hx₀ (gfun_antitone E hm hmn x₀ (Hcell_sub_gfun q T n x₀ hz))
    rw [← lnCoverG_sUnion_eq E hl_pos hBl] at hzB
    obtain ⟨U, ⟨w, hw, rfl⟩, hzw⟩ := Set.mem_sUnion.mp hzB
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨w, ⟨hw, ⟨z, hzw, hz⟩⟩, hzw⟩

end Section4LnCovers

end Research.ChenWangSec4
