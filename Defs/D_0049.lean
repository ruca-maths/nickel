import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0048

namespace Defs.D_0049

/-!
稠密性の部品 5: **slab の元は branch 2 の穴の構成で「使ってよい元」**（`allowed_branch2`）。

穴の構成 HkO（k = 0, branch 2）で除く集合は、前の slab の穴のセル（自分の slab の中にしかない）と、
自分の slab の g[p₁, D1slabO c]。前者は slab c と交わらず、後者は branch 1 の外に届かない
（`Defs.D_0048.not_mem_gset_D1slabO`）。よって slab c の第 m+1 層の元 S は、その第 m+2 層の
被覆が無限なら常に許される。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0040 Defs.D_0048

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

theorem slabO_disjoint {i c : ℕ} (h : i ≠ c) :
    Disjoint (slabO q T m y0 i) (slabO q T m y0 c) := by
  rw [Set.disjoint_left]
  intro w hi hc'
  unfold slabO at hi hc'
  split_ifs at hi hc'
  · exact hi
  · exact hi
  · exact hc'
  · exact h (hi.1.symm.trans hc'.1)

theorem holeCells_sub_slab (a : ℕ → ℕ) (k r c : ℕ) (S : Set (ℕ → α)) :
    holeCells q T m a k r (slabO q T m y0 c ∩ S) ⊆ slabO q T m y0 c := by
  intro w hw
  simp only [holeCells, Set.mem_iUnion, exists_prop] at hw
  obtain ⟨Pv, ⟨hPv, -⟩, B, -, -, hwP⟩ := hw
  obtain ⟨S2, -, -, S3, -, -, hPe⟩ := hPv
  rw [hPe] at hwP
  exact hwP.1.1.1

theorem allowed_branch2 [Countable α] (hc : Compat2 q T) (hm : 0 < m) (a : ℕ → ℕ) {c p1 : ℕ}
    (hp : m + 2 ≤ p1) {S : Set (ℕ → α)} (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c))
    (hinf : (lncA q T (m + 2) (slabO q T m y0 c ∩ S)).Infinite)
    (prior0 : Set (ℕ → α)) (hprior : Disjoint prior0 (slabO q T m y0 c)) :
    S ∈ allowedO q T m y0 c (prior0 ∪ gset q T p1 (D1slabO q T m y0 a c)) := by
  set F := lncA q T (m + 2) (slabO q T m y0 c ∩ S)
  have hF : F.Countable ∧ F.Infinite := ⟨lncA_countable (by omega) _, hinf⟩
  set S2 := unlab F hF 0
  have hS2 : S2 ∈ F := unlab_mem F hF 0
  have hlab : lab F S2 ≠ 1 := by rw [lab_unlab]; omega
  obtain ⟨x, hx, hxe, -⟩ := id hS2
  have hxS2 : x ∈ S2 := by rw [hxe]; exact mem_gfun q T _ x
  refine ⟨hS, x, hx.2, hx.1, ?_⟩
  rintro (h | h)
  · exact Set.disjoint_left.mp hprior h hx.1
  · exact not_mem_gset_D1slabO hc hm a hp hS hS2 hlab hx.2 hxS2 h

end Defs.D_0049
