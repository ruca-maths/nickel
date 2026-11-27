import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0035

namespace Defs.D_0047

/-!
稠密性の部品 3: **Ln cover は無限族**（論文 Claim 5.7.3 の一般形）。

集合 A に「自由な」座標 k（A の点の第 k 座標を任意に変えても A に留まる）があり、
A の各点 x の箱 g(n, x) が第 k 座標を制約する（k < n + hidx n x + 1）なら、
lncA n A は無限（`lncA_infinite`）。有限個の箱の第 k 座標の区間はすべて右端を持ち、
Q には最大元がないので、その右端より大きい値を第 k 座標に持つ A の点が覆われない。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

/-- g(n, x) の第 k 座標の区間の右端。 -/
noncomputable def rEnd (q : ℕ ≃ α) (T : Tree2 α) (n k : ℕ) (x : ℕ → α) : α :=
  if k < n then T.child (x k) (lvl q n x) else T.child (ibase T (lvl q n x) (x k)) (lvl q n x)

theorem lt_rEnd {n k : ℕ} {x z : ℕ → α} (hk : k < n + hidx q n x + 1)
    (hz : z ∈ gfun q T n x) : z k < rEnd q T n k x := by
  unfold rEnd
  split_ifs with h
  · exact (hz.1 k h).2
  · exact (hz.2 k (by omega) hk).2

theorem lncA_infinite [NoMaxOrder α] (hc : Compat2 q T) {n : ℕ} {A : Set (ℕ → α)}
    (hA : A.Nonempty) (k : ℕ) (hfree : ∀ w ∈ A, ∀ t, Function.update w k t ∈ A)
    (hcon : ∀ x ∈ A, k < n + hidx q n x + 1) : (lncA q T n A).Infinite := by
  classical
  intro hfin
  obtain ⟨w, hw⟩ := hA
  haveI : Nonempty α := ⟨w 0⟩
  -- 各元の代表点
  have hrep : ∀ S ∈ lncA q T n A, ∃ x ∈ A, S = gfun q T n x := by
    rintro S ⟨x, hx, rfl, -⟩; exact ⟨x, hx, rfl⟩
  choose! rep hrepA hrepS using hrep
  -- 右端の有限集合の上界
  have hfinR : ((fun S => rEnd q T n k (rep S)) '' lncA q T n A).Finite := hfin.image _
  obtain ⟨t0, ht0⟩ : ∃ t0 : α, ∀ r ∈ (fun S => rEnd q T n k (rep S)) '' lncA q T n A, r ≤ t0 := by
    rcases hfinR.bddAbove with ⟨b, hb⟩
    exact ⟨max b (w k), fun r hr => le_trans (hb hr) (le_max_left _ _)⟩
  obtain ⟨t, ht⟩ := exists_gt t0
  set w' := Function.update w k t
  have hw'A : w' ∈ A := hfree w hw t
  have hw'g : w' ∈ gset q T n A := sub_gset n A hw'A
  rw [← lncA_sUnion hc n A] at hw'g
  obtain ⟨S, hS, hw'S⟩ := hw'g
  have hxS := hrepS S hS
  rw [hxS] at hw'S
  have h1 := lt_rEnd (hcon (rep S) (hrepA S hS)) hw'S
  have h2 := ht0 _ ⟨S, hS, rfl⟩
  have h3 : w' k = t := Function.update_self k t w
  rw [h3] at h1
  exact absurd (lt_trans h1 (lt_of_le_of_lt h2 ht)) (lt_irrefl _)

end Defs.D_0047
