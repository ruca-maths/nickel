import Mathlib.Data.Set.Lattice
import Defs.D_0012
import Defs.D_0013

namespace Defs.D_0018

/-!
Chen–Wang (arXiv 1809.03763v2) Proposition 3.3.1 / 3.3.5（本文 446–489 行）を
D_0012 の `gfun` について示す。
* `ival_mono` : 0 < a ≤ b なら `ival T b r ⊆ ival T a r`（Prop 2.2.5 から）。
* `gfun_succ_sub` : Prop 3.3.5 `g(n+1, x) ⊆ g(n, x)`（n ≥ 1, `Compat q T`）。
  座標 n では Prop 3.2.1 を直接使う（論文の 3.2.3 の番号条件は不要）。
* `gfun_anti` : 1 ≤ m ≤ n なら `g(n, x) ⊆ g(m, x)`。
* `gfun_iInter` : Prop 3.3.1 `⋂ n, g(n, x) = {x}`（`Compat.shrink` を使う）。
-/

open Defs.D_0003 Defs.D_0005 Defs.D_0007 Defs.D_0012 Defs.D_0013

variable {α : Type} [LinearOrder α]

theorem ival_mono (T : Tree2 α) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) (r : α) :
    ival T b r ⊆ ival T a r := by
  obtain ⟨hpa, hra⟩ := ibase_spec T ha r
  obtain ⟨hpb, hrb⟩ := ibase_spec T (lt_of_lt_of_le ha hab) r
  rcases prop_2_2_5 T ha hab hpa hpb with hd | hs
  · exact absurd hrb (Set.disjoint_left.mp hd hra)
  · exact hs

variable {q : ℕ ≃ α} {T : Tree2 α}

theorem gfun_succ_sub (hc : Compat q T) (n : ℕ) (hn : 0 < n) (x : ℕ → α) :
    gfun q T (n + 1) x ⊆ gfun q T n x := by
  rintro z ⟨h1, h2⟩
  have hc' : hidx q n x ≤ hidx q (n + 1) x := code_mono n hn _ (n + 1) (Nat.le_succ n)
  have hab : lvl q n x ≤ lvl q (n + 1) x := by unfold lvl; omega
  have ha := lvl_pos q n x
  refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · have := h1 k (by omega)
    exact ⟨this.1, lt_of_lt_of_le this.2 (Tree2.child_le_child T _ ha hab)⟩
  · rcases eq_or_lt_of_le hk1 with heq | hlt
    · subst heq
      have hz := h1 n (by omega)
      obtain ⟨_, hxn⟩ := ibase_spec T ha (x n)
      rcases eq_or_lt_of_le hxn.1 with he | hlt'
      · show z n ∈ Set.Ico (ibase T (lvl q n x) (x n)) (T.child (ibase T (lvl q n x) (x n)) (lvl q n x))
        rw [he]
        exact ⟨hz.1, lt_of_lt_of_le hz.2 (Tree2.child_le_child T _ ha hab)⟩
      · have := (prop_3_2_1 hc ha hlt' hxn.2).2.2 (lvl q (n + 1) x) (lvl_pos _ _ _) hz
        exact ⟨this.1.le, this.2⟩
    · exact ival_mono T ha hab (x k) (h2 k (by omega) (by omega))

theorem gfun_anti (hc : Compat q T) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (x : ℕ → α) :
    gfun q T n x ⊆ gfun q T m x := by
  induction hmn with
  | refl => exact fun _ h => h
  | @step n hle ih => exact (gfun_succ_sub hc n (lt_of_lt_of_le hm hle) x).trans ih

theorem gfun_iInter (hc : Compat q T) (x : ℕ → α) : (⋂ n, gfun q T n x) = {x} := by
  ext z
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    funext k
    by_contra hne
    have hlt : x k < z k := by
      have := (h (k + 1)).1 k (by omega)
      exact lt_of_le_of_ne this.1 (fun e => hne e.symm)
    obtain ⟨a, ha, hca⟩ := hc.shrink (x k) (z k) hlt
    have hk := (h (k + a)).1 k (by omega)
    have hle : a ≤ lvl q (k + a) x := by unfold lvl; omega
    exact absurd (lt_trans (lt_of_lt_of_le hk.2 (Tree2.child_le_child T _ ha hle)) hca)
      (lt_irrefl _)
  · rintro rfl n
    exact mem_gfun q T n z

end Defs.D_0018
