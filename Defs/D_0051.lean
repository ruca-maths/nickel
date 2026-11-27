import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0047

namespace Defs.D_0051

/-!
稠密性の部品 7: 箱で定まる集合の「自由な座標」と Ln cover の無限性（`lncA_infinite_box`）。

* `gfun_free` : 第 k 座標が g(n, x) の制約範囲（< n + hidx n x + 1）の外なら、点の第 k 座標を変えても
  g(n, x) に留まる。`H_free` : H(m, c) は第 m 座標以降で自由。
* `lncA_infinite_box` : A ⊆ g(L, s)、L ≤ n、A が座標 n + hidx L s で自由なら lncA n A は無限
  （A の点 x では hidx L s ≤ hidx L x ≤ hidx n x なので、どの箱もその座標を制約する）。
これで `Defs.D_0050.Gd_nonempty` の無限性の仮定が、piece などの具体的な集合について外せる。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0047

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

/-- 第 k 座標について自由。 -/
def FreeAt (A : Set (ℕ → α)) (k : ℕ) : Prop := ∀ w ∈ A, ∀ t, Function.update w k t ∈ A

theorem FreeAt.inter {A B : Set (ℕ → α)} {k : ℕ} (hA : FreeAt A k) (hB : FreeAt B k) :
    FreeAt (A ∩ B) k := fun w hw t => ⟨hA w hw.1 t, hB w hw.2 t⟩

theorem gfun_free {n k : ℕ} (x : ℕ → α) (hk : n + hidx q n x + 1 ≤ k) :
    FreeAt (gfun q T n x) k := by
  intro w hw t
  rw [gfun_eq] at hw ⊢
  intro j hj
  rw [Function.update_of_ne (by omega)]
  exact hw j hj

theorem H_free {m k : ℕ} (hm : 0 < m) (hk : m ≤ k) (c : ℕ) : FreeAt (H q m c) k := by
  intro w hw t
  have : hidx q m (Function.update w k t) = hidx q m w :=
    (code_eq_iff m hm _ _).2 (fun j hj => by
      show q.symm (Function.update w k t j) = q.symm (w j)
      rw [Function.update_of_ne (by omega)])
  exact this.trans hw

theorem lncA_infinite_box [NoMaxOrder α] (hc : Compat2 q T) {L n : ℕ} (hL : 0 < L) (hLn : L ≤ n)
    {A : Set (ℕ → α)} {s : ℕ → α} (hA : A.Nonempty) (hsub : A ⊆ gfun q T L s)
    (hfree : FreeAt A (n + hidx q L s)) : (lncA q T n A).Infinite := by
  refine lncA_infinite hc hA (n + hidx q L s) hfree (fun x hx => ?_)
  have h1 : hidx q L s ≤ hidx q L x := hidx_le_of_mem_gfun hc hL (hsub hx)
  have h2 : hidx q L x ≤ hidx q n x := code_mono L hL _ n hLn
  omega

end Defs.D_0051
