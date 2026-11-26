import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0005
import Defs.D_0011

namespace Defs.D_0012

/-!
Chen–Wang (arXiv 1809.03763v2) Construction 3.2（本文 334–412 行）: H(n,i,l), g(n,i,l) と
g-関数 `g(n, x)`（Note D1/D4）。X = ℕ → α、番号付け `q : ℕ ≃ α`、木 `T : Tree2 α`。

添字の対応: `c := code n (q.symm ∘ x)` とすると x ∈ `H q n c`（= 論文の H(n, i), i = c + 1）。
論文の `a = n + i` は `lvl q n x := n + c + 1`。

* `ibase T a r` : `I_a` の中で r を含む区間 `[p, p_a)` の左端 p（a ≥ 1 なら存在、
  Prop 2.2.1 により一意。存在しないときは r 自身）。
* `ival T a r := [ibase T a r, (ibase T a r)_a)`。
* `Hcell q T n x` : 論文の H(n, x) = {q_{i1}}×…×{q_{in}}×[q_{l1}, q_{l1}a)×…×[q_{li}, q_{li}a)×X_{n+i}。
  先頭 n 座標は x と一致、続く i 座標は x の座標を含む I_a 区間に入る。
* `gfun q T n x` : 論文の g(n, x) = [q_{i1}, q_{i1}a)×…×[q_{in}, q_{in}a)×[q_{l1}, q_{l1}a)×…×X_{n+i}。
  先頭 n 座標は `[x k, (x k)_a)`、続く i 座標は `ival`。
定理:
* `mem_Hcell`, `mem_gfun`, `Hcell_sub_gfun` : x ∈ H(n,x) ⊆ g(n,x)。
* `gfun_isClopen`, `Hcell_isClopen` : ρ（D_0011 の xtop）で開かつ閉（有限個の座標で決まるため）。
* `gfun_inter_H` : Note D4 `g(n,x) ∩ H(n,i) = H(n,x)`（n ≥ 1）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0011

variable {α : Type} [LinearOrder α]

open Classical in
/-- `I_a` の中で `r` を含む区間の左端。 -/
noncomputable def ibase (T : Tree2 α) (a : ℕ) (r : α) : α :=
  if h : T.IUnion a r then Classical.choose h else r

/-- `r` を含む `I_a` の区間。 -/
noncomputable def ival (T : Tree2 α) (a : ℕ) (r : α) : Set α :=
  Set.Ico (ibase T a r) (T.child (ibase T a r) a)

theorem ibase_spec (T : Tree2 α) {a : ℕ} (ha : 0 < a) (r : α) :
    T.QStar a (ibase T a r) ∧ r ∈ ival T a r := by
  have h : T.IUnion a r := prop_2_2_1_cover T ha r
  unfold ival ibase
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem mem_ival (T : Tree2 α) {a : ℕ} (ha : 0 < a) (r : α) : r ∈ ival T a r :=
  (ibase_spec T ha r).2

variable (q : ℕ ≃ α) (T : Tree2 α)

/-- 論文の H(n, i) の番号（`x ∈ H q n (hidx q n x)`）。論文の i は `hidx + 1`。 -/
def hidx (n : ℕ) (x : ℕ → α) : ℕ := code n (fun k => q.symm (x k))

/-- 論文の a = n + i。 -/
def lvl (n : ℕ) (x : ℕ → α) : ℕ := n + hidx q n x + 1

theorem lvl_pos (n : ℕ) (x : ℕ → α) : 0 < lvl q n x := by
  unfold lvl; omega

/-- 論文の H(n, x)（Note D4）。 -/
noncomputable def Hcell (n : ℕ) (x : ℕ → α) : Set (ℕ → α) :=
  {z | (∀ k < n, z k = x k) ∧
    ∀ k, n ≤ k → k < n + hidx q n x + 1 → z k ∈ ival T (lvl q n x) (x k)}

/-- 論文の g(n, x)（Construction 3.2 C, Note D1/D4）。 -/
noncomputable def gfun (n : ℕ) (x : ℕ → α) : Set (ℕ → α) :=
  {z | (∀ k < n, z k ∈ Set.Ico (x k) (T.child (x k) (lvl q n x))) ∧
    ∀ k, n ≤ k → k < n + hidx q n x + 1 → z k ∈ ival T (lvl q n x) (x k)}

theorem mem_Hcell (n : ℕ) (x : ℕ → α) : x ∈ Hcell q T n x :=
  ⟨fun _ _ => rfl, fun k _ _ => mem_ival T (lvl_pos q n x) (x k)⟩

theorem Hcell_sub_gfun (n : ℕ) (x : ℕ → α) : Hcell q T n x ⊆ gfun q T n x := by
  rintro z ⟨h1, h2⟩
  refine ⟨fun k hk => ?_, h2⟩
  rw [h1 k hk]
  exact ⟨le_rfl, T.lt_child _ _ (T.C_child _ _ (lvl_pos q n x))⟩

theorem mem_gfun (n : ℕ) (x : ℕ → α) : x ∈ gfun q T n x :=
  Hcell_sub_gfun q T n x (mem_Hcell q T n x)

/-- 有限個の座標の条件で決まる集合は xtop で開かつ閉。 -/
theorem isClopen_fin (N : ℕ) (s : ℕ → Set α) :
    @IsOpen (ℕ → α) (xtop α) {z | ∀ k < N, z k ∈ s k} ∧
      @IsClosed (ℕ → α) (xtop α) {z | ∀ k < N, z k ∈ s k} := by
  letI : TopologicalSpace α := ⊥
  letI : DiscreteTopology α := ⟨rfl⟩
  have h : {z : ℕ → α | ∀ k < N, z k ∈ s k} = ⋂ k ∈ Finset.range N, (fun z => z k) ⁻¹' s k := by
    ext z; simp
  refine ⟨?_, ?_⟩
  · show IsOpen _
    rw [h]
    exact isOpen_biInter_finset (fun k _ => (isOpen_discrete _).preimage (continuous_apply k))
  · show IsClosed _
    rw [h]
    exact isClosed_biInter (fun k _ => (isClosed_discrete _).preimage (continuous_apply k))

theorem gfun_eq (n : ℕ) (x : ℕ → α) :
    gfun q T n x = {z | ∀ k < n + hidx q n x + 1, z k ∈
      (if k < n then Set.Ico (x k) (T.child (x k) (lvl q n x)) else ival T (lvl q n x) (x k))} := by
  ext z
  simp only [gfun, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ k hk
    split_ifs with h
    · exact h1 k h
    · exact h2 k (by omega) hk
  · intro h
    refine ⟨fun k hk => ?_, fun k hk hk' => ?_⟩
    · have := h k (by omega); rwa [if_pos hk] at this
    · have := h k hk'; rwa [if_neg (by omega)] at this

theorem Hcell_eq (n : ℕ) (x : ℕ → α) :
    Hcell q T n x = {z | ∀ k < n + hidx q n x + 1, z k ∈
      (if k < n then {x k} else ival T (lvl q n x) (x k))} := by
  ext z
  simp only [Hcell, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ k hk
    split_ifs with h
    · exact h1 k h
    · exact h2 k (by omega) hk
  · intro h
    refine ⟨fun k hk => ?_, fun k hk hk' => ?_⟩
    · have := h k (by omega); rwa [if_pos hk] at this
    · have := h k hk'; rwa [if_neg (by omega)] at this

theorem gfun_isClopen (n : ℕ) (x : ℕ → α) :
    @IsOpen (ℕ → α) (xtop α) (gfun q T n x) ∧ @IsClosed (ℕ → α) (xtop α) (gfun q T n x) := by
  rw [gfun_eq]; exact isClopen_fin _ _

theorem Hcell_isClopen (n : ℕ) (x : ℕ → α) :
    @IsOpen (ℕ → α) (xtop α) (Hcell q T n x) ∧ @IsClosed (ℕ → α) (xtop α) (Hcell q T n x) := by
  rw [Hcell_eq]; exact isClopen_fin _ _

/-- Note D4: `g(n, x) ∩ H(n, i) = H(n, x)`（n ≥ 1）。 -/
theorem gfun_inter_H (n : ℕ) (hn : 0 < n) (x : ℕ → α) :
    gfun q T n x ∩ H q n (hidx q n x) = Hcell q T n x := by
  ext z
  constructor
  · rintro ⟨⟨_, h2⟩, hz⟩
    refine ⟨?_, h2⟩
    have hz' : z ∈ H q n (code n (fun k => q.symm (x k))) := hz
    exact (mem_H_iff_same q n hn z x).1 hz'
  · intro hz
    refine ⟨Hcell_sub_gfun q T n x hz, ?_⟩
    show code n (fun k => q.symm (z k)) = code n (fun k => q.symm (x k))
    exact (code_eq_iff n hn _ _).2 (fun k hk => by rw [hz.1 k hk])

end Defs.D_0012
