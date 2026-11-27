import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Equiv.Defs
import Defs.D_0012
import Defs.D_0024

namespace Defs.D_0025

/-!
D_0016（Prop 3.2.2/3.2.3）、D_0018（Prop 3.3.1/3.3.5）、D_0019（Prop 3.3.4/3.3.6′/3.3.8）を
充足可能な `Defs.D_0024.Compat2` の下に移植したもの（D_0013 の `Compat` は充足不能: D_0024.not_compat）。
証明は機械的置換（Compat → Compat2, prop_3_2_1 → prop_3_2_1'）。
-/

open Relation Defs.D_0003 Defs.D_0005 Defs.D_0007 Defs.D_0012 Defs.D_0024

variable {α : Type} [LinearOrder α]

theorem ival_mono (T : Tree2 α) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) (r : α) :
    ival T b r ⊆ ival T a r := by
  obtain ⟨hpa, hra⟩ := ibase_spec T ha r
  obtain ⟨hpb, hrb⟩ := ibase_spec T (lt_of_lt_of_le ha hab) r
  rcases prop_2_2_5 T ha hab hpa hpb with hd | hs
  · exact absurd hrb (Set.disjoint_left.mp hd hra)
  · exact hs

variable {q : ℕ ≃ α} {T : Tree2 α}

theorem prop_3_2_2 (hc : Compat2 q T) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {p r : α}
    (hr : r ∉ Set.Ico p (T.child p a)) (hnum : q.symm p < q.symm r) :
    Set.Ico p (T.child p a) ∩ Set.Ico r (T.child r b) = ∅ := by
  have _ := ha
  refine Set.eq_empty_of_forall_notMem ?_
  rintro x ⟨⟨hpx, hxpa⟩, ⟨hrx, hxrb⟩⟩
  rcases lt_or_ge r p with hrp | hpr
  · have h1 : T.child r 1 ≤ p := by
      by_contra h
      push_neg at h
      have := (prop_3_2_1' hc (a := 1) (by omega) hrp h).1
      exact absurd (lt_trans this hnum) (lt_irrefl _)
    exact absurd (lt_of_lt_of_le hxrb
      (le_trans (Tree2.child_le_child T r (by omega) hb) (le_trans h1 hpx))) (lt_irrefl _)
  · have : T.child p a ≤ r := by
      by_contra h
      push_neg at h
      exact hr ⟨hpr, h⟩
    exact absurd (lt_of_lt_of_le hxpa (le_trans this hrx)) (lt_irrefl _)

theorem prop_3_2_3 (hc : Compat2 q T) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) {p r : α}
    (hpb : q.symm p ≤ b)
    (hne : (Set.Ico p (T.child p a) ∩ Set.Ico r (T.child r b)).Nonempty) :
    Set.Ico r (T.child r b) ⊆ Set.Ico p (T.child p a) := by
  obtain ⟨x, ⟨hpx, hxpa⟩, ⟨hrx, hxrb⟩⟩ := hne
  rcases lt_trichotomy p r with hpr | rfl | hrp
  · have hrpa : r < T.child p a := lt_of_le_of_lt hrx hxpa
    intro y hy
    have := (prop_3_2_1' hc ha hpr hrpa).2.2 b (by omega) hy
    exact ⟨this.1.le, this.2⟩
  · intro y hy
    exact ⟨hy.1, lt_of_lt_of_le hy.2 (Tree2.child_le_child T p ha hab)⟩
  · exfalso
    have hprb : p < T.child r b := lt_of_le_of_lt hpx hxrb
    have := (prop_3_2_1' hc (by omega) hrp hprb).2.1
    omega

theorem gfun_succ_sub (hc : Compat2 q T) (n : ℕ) (hn : 0 < n) (x : ℕ → α) :
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
      · have := (prop_3_2_1' hc ha hlt' hxn.2).2.2 (lvl q (n + 1) x) (lvl_pos _ _ _) hz
        exact ⟨this.1.le, this.2⟩
    · exact ival_mono T ha hab (x k) (h2 k (by omega) (by omega))

theorem gfun_anti (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (x : ℕ → α) :
    gfun q T n x ⊆ gfun q T m x := by
  induction hmn with
  | refl => exact fun _ h => h
  | @step n hle ih => exact (gfun_succ_sub hc n (lt_of_lt_of_le hm hle) x).trans ih

theorem gfun_iInter (hc : Compat2 q T) (x : ℕ → α) : (⋂ n, gfun q T n x) = {x} := by
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

theorem hidx_lt_of_mem_gfun (hc : Compat2 q T) {n : ℕ} {x z : ℕ → α}
    (hz : z ∈ gfun q T n x) {k : ℕ} (hk : k < n) (hne : z k ≠ x k) :
    lvl q n x < hidx q n z := by
  have h := hz.1 k hk
  have hlt : x k < z k := lt_of_le_of_ne h.1 (fun e => hne e.symm)
  have h1 := (prop_3_2_1' hc (lvl_pos q n x) hlt h.2).2.1
  have h2 : q.symm (z k) ≤ hidx q n z := code_ge n (fun k => q.symm (z k)) k hk
  omega

theorem hidx_le_of_mem_gfun (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) {x z : ℕ → α}
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

theorem gfun_nested (hc : Compat2 q T) {n : ℕ} {x y : ℕ → α}
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

theorem gfun_trans (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) {x y : ℕ → α}
    (hy : y ∈ gfun q T n x) : gfun q T n y ⊆ gfun q T n x :=
  gfun_nested hc (hidx_le_of_mem_gfun hc hn hy) ⟨y, hy, mem_gfun q T n y⟩

end Defs.D_0025
