import Mathlib.Data.Set.Lattice
import Defs.D_0016
import Defs.D_0018

namespace Defs.D_0019

/-!
Chen–Wang (arXiv 1809.03763v2) Proposition 3.3.4 / 3.3.6′ / 3.3.8（本文 446–482 行）を
D_0012 の `gfun` について示す（n ≥ 1, `Compat q T`）。
* `hidx_lt_of_mem_gfun` : z ∈ g(n,x) で先頭 n 座標のどれかが x と違えば
  `lvl q n x < hidx q n z`（Prop 3.2.1 と Prop 3.1.5 から。3.3.6′ の番号の部分）。
* `hidx_le_of_mem_gfun` : z ∈ g(n,x) なら `hidx q n x ≤ hidx q n z`。
* `gfun_nested` : Prop 3.3.8（≤ 版）`hidx q n x ≤ hidx q n y` で g(n,x) ∩ g(n,y) ≠ ∅ なら
  g(n,y) ⊆ g(n,x)（先頭 n 座標は Prop 3.2.3、その先は Prop 2.2.5）。
* `gfun_trans` : Prop 3.3.4 `y ∈ g(n,x)` なら `g(n,y) ⊆ g(n,x)`。
-/

open Defs.D_0003 Defs.D_0005 Defs.D_0007 Defs.D_0012 Defs.D_0013 Defs.D_0016 Defs.D_0018

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

theorem hidx_lt_of_mem_gfun (hc : Compat q T) {n : ℕ} {x z : ℕ → α}
    (hz : z ∈ gfun q T n x) {k : ℕ} (hk : k < n) (hne : z k ≠ x k) :
    lvl q n x < hidx q n z := by
  have h := hz.1 k hk
  have hlt : x k < z k := lt_of_le_of_ne h.1 (fun e => hne e.symm)
  have h1 := (prop_3_2_1 hc (lvl_pos q n x) hlt h.2).2.1
  have h2 : q.symm (z k) ≤ hidx q n z := code_ge n (fun k => q.symm (z k)) k hk
  omega

theorem hidx_le_of_mem_gfun (hc : Compat q T) {n : ℕ} (hn : 0 < n) {x z : ℕ → α}
    (hz : z ∈ gfun q T n x) : hidx q n x ≤ hidx q n z := by
  by_cases h : ∀ k < n, z k = x k
  · have : hidx q n z = hidx q n x := (code_eq_iff n hn _ _).2 (fun k hk => by
      show q.symm (z k) = q.symm (x k); rw [h k hk])
    omega
  · push_neg at h
    obtain ⟨k, hk, hne⟩ := h
    have := hidx_lt_of_mem_gfun hc hz hk hne
    unfold lvl at this
    omega

theorem gfun_nested (hc : Compat q T) {n : ℕ} {x y : ℕ → α}
    (hxy : hidx q n x ≤ hidx q n y) (hne : (gfun q T n x ∩ gfun q T n y).Nonempty) :
    gfun q T n y ⊆ gfun q T n x := by
  obtain ⟨w, ⟨hw1, hw2⟩, ⟨hw1', hw2'⟩⟩ := hne
  have ha := lvl_pos q n x
  have hab : lvl q n x ≤ lvl q n y := by unfold lvl; omega
  rintro z ⟨hz1, hz2⟩
  refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · have hnum : q.symm (x k) ≤ lvl q n y := by
      have := code_ge n (fun k => q.symm (x k)) k hk
      have : q.symm (x k) ≤ hidx q n x := this
      unfold lvl; omega
    exact prop_3_2_3 hc ha hab hnum ⟨w k, hw1 k hk, hw1' k hk⟩ (hz1 k hk)
  · obtain ⟨hpa, -⟩ := ibase_spec T ha (x k)
    obtain ⟨hpb, -⟩ := ibase_spec T (lt_of_lt_of_le ha hab) (y k)
    rcases prop_2_2_5 T ha hab hpa hpb with hd | hs
    · exact absurd (hw2' k hk1 (by omega)) (Set.disjoint_left.mp hd (hw2 k hk1 hk2))
    · exact hs (hz2 k hk1 (by omega))

theorem gfun_trans (hc : Compat q T) {n : ℕ} (hn : 0 < n) {x y : ℕ → α}
    (hy : y ∈ gfun q T n x) : gfun q T n y ⊆ gfun q T n x :=
  gfun_nested hc (hidx_le_of_mem_gfun hc hn hy) ⟨y, hy, mem_gfun q T n y⟩

end Defs.D_0019
