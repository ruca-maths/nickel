import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0007

namespace Defs.D_0011

/-!
Chen–Wang (arXiv 1809.03763v2) 第2節末の位相 ρ（X = Π_n Q_n 上）。
本文: `B'_n = {B_n1 × … × B_nn × X_n : B_ni ∈ Q_i}`（B_ni は Q_i の**点**）を基とする位相。
すなわち各座標に離散位相を入れた積位相（Baire 空間型）。ρ′ の積ではない点に注意。

* `xtop α` : `ℕ → α` 上の、各成分離散の積位相（instance ではなく def）。
* `isOpen_cyl` : 先頭 n 座標を固定した柱状集合は開。
* `H_isOpen`, `H_isClosed` : D_0007 の `H q n c`（論文の H(n, c+1)）は ρ で開かつ閉（n ≥ 1）。
  これが Prop 3.1.2/3.1.3 の「距離 > 0」の位相的な代わりになる。
-/

open Defs.D_0007

variable {α : Type}

/-- 論文の ρ: 各成分に離散位相を入れた積位相。 -/
def xtop (α : Type) : TopologicalSpace (ℕ → α) :=
  @Pi.topologicalSpace ℕ (fun _ => α) (fun _ => ⊥)

/-- 先頭 `n` 座標を `y` に固定した柱状集合は開。 -/
theorem isOpen_cyl (n : ℕ) (y : ℕ → α) :
    @IsOpen (ℕ → α) (xtop α) {x | ∀ k < n, x k = y k} := by
  letI : TopologicalSpace α := ⊥
  letI : DiscreteTopology α := ⟨rfl⟩
  have h : {x : ℕ → α | ∀ k < n, x k = y k} = ⋂ k ∈ Finset.range n, (fun x => x k) ⁻¹' {y k} := by
    ext x; simp
  show IsOpen _
  rw [h]
  exact isOpen_biInter_finset (fun k _ => (isOpen_discrete _).preimage (continuous_apply k))

variable (q : ℕ ≃ α)

theorem H_isOpen (n : ℕ) (hn : 0 < n) (c : ℕ) :
    @IsOpen (ℕ → α) (xtop α) (H q n c) := by
  letI : TopologicalSpace (ℕ → α) := xtop α
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  refine ⟨{x | ∀ k < n, x k = y k}, ?_, isOpen_cyl n y, fun k _ => rfl⟩
  intro x hx
  have hc : c = code n (fun k => q.symm (y k)) := hy.symm
  rw [hc]
  exact (mem_H_iff_same q n hn x y).2 hx

theorem H_isClosed (n : ℕ) (hn : 0 < n) (c : ℕ) :
    @IsClosed (ℕ → α) (xtop α) (H q n c) := by
  letI : TopologicalSpace (ℕ → α) := xtop α
  have h : (H q n c)ᶜ = ⋃ c' ∈ {c' | c' ≠ c}, H q n c' := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨c', hc'⟩ := H_cover q n x
      exact ⟨c', fun h => hx (h ▸ hc'), hc'⟩
    · rintro ⟨c', hne, hc'⟩ hx
      exact Set.disjoint_left.1 (H_disjoint q n hne) hc' hx
  rw [← isOpen_compl_iff, h]
  exact isOpen_biUnion (fun c' _ => H_isOpen q n hn c')

end Defs.D_0011
