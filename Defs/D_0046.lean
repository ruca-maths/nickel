import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0045
import Defs.D_0039

namespace Defs.D_0046

/-!
稠密性の部品 2: 近い点 s′（`Defs.D_0045.close_point_exists`）の箱 g(m+1, s′) は、s′ の slab
（H₀ の slab ではない）の第 m+1 層の Ln cover の元そのもの（`close_member`）。
よって近い slab の元（とその branch・piece・穴の構造すべて）が z の箱近傍 g(ℓ, z) に丸ごと入る。

鍵: slab の点 x で g(m+1, s′) ⊆ g(m+1, x) なら、座標 m で x m < s′ m だと
lvl (m+1) x < q⁻¹(s′ m)（Prop 3.2.1）だが、lvl (m+1) x ≥ q⁻¹(x 0) = q⁻¹(s′ 0) は大きいので矛盾。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025
  Defs.D_0031 Defs.D_0035 Defs.D_0036 Defs.D_0039

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

theorem close_member (hc : Compat2 q T) {m : ℕ} (hm : 0 < m) {y0 s' : ℕ → α}
    (hs'G : s' ∈ gfun q T m y0) (hne : hidx q m s' ≠ hidx q m y0)
    (hB : q.symm (s' m) < q.symm (s' 0)) :
    gfun q T (m + 1) s' ∈ lncA q T (m + 1) (slabO q T m y0 (hidx q m s')) := by
  have hslab : s' ∈ slabO q T m y0 (hidx q m s') := by
    unfold slabO; rw [if_neg hne]; exact ⟨rfl, hs'G⟩
  refine ⟨s', hslab, rfl, fun x hx hsub => ?_⟩
  have hx' : x ∈ slab q T m y0 (hidx q m s') := by
    unfold slabO at hx; rw [if_neg hne] at hx; exact hx
  -- x と s′ は先頭 m 座標が等しい
  have hfirst : ∀ k < m, x k = s' k := by
    have h1 : x ∈ H q m (code m (fun k => q.symm (s' k))) := hx'.1
    exact (mem_H_iff_same q m hm x s').1 h1
  have hs'x : s' ∈ gfun q T (m + 1) x := hsub (mem_gfun q T _ s')
  -- 座標 m も等しい
  have hm_eq : x m = s' m := by
    by_contra hne'
    have h := hs'x.1 m (by omega)
    have hlt : x m < s' m := lt_of_le_of_ne h.1 hne'
    have h1 := (prop_3_2_1' hc (lvl_pos q (m + 1) x) hlt h.2).2.1
    have h2 : q.symm (x 0) ≤ hidx q (m + 1) x := code_ge (m + 1) (fun k => q.symm (x k)) 0 (by omega)
    rw [hfirst 0 hm] at h2
    unfold lvl at h1
    omega
  have hidx_eq : hidx q (m + 1) x = hidx q (m + 1) s' :=
    (code_eq_iff (m + 1) (by omega) _ _).2 (fun k hk => by
      show q.symm (x k) = q.symm (s' k)
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with h | h
      · rw [hfirst k h]
      · rw [h, hm_eq])
  have := gfun_nested hc (le_of_eq hidx_eq.symm) ⟨s', mem_gfun q T _ s', hs'x⟩
  exact le_antisymm this hsub

end Defs.D_0046
