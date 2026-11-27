import Mathlib.Logic.Equiv.Defs
import Defs.D_0013

namespace Defs.D_0016

/-!
Chen–Wang (arXiv 1809.03763v2) Proposition 3.2.2 / 3.2.3（本文 413–445 行）の木版。
`Compat q T`（D_0013）の下で:
* `prop_3_2_2` : `r ∉ [p, p_a)`, `q⁻¹ p < q⁻¹ r`, a,b ≥ 1 なら `[p, p_a) ∩ [r, r_b) = ∅`。
* `prop_3_2_3` : 0 < a ≤ b, `q⁻¹ p ≤ b`（論文では Prop 3.1.5 の i ≥ i_k から出る条件）,
  `[p, p_a) ∩ [r, r_b) ≠ ∅` なら `[r, r_b) ⊆ [p, p_a)`。
-/

open Relation Defs.D_0003 Defs.D_0013

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

theorem prop_3_2_2 (hc : Compat q T) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {p r : α}
    (hr : r ∉ Set.Ico p (T.child p a)) (hnum : q.symm p < q.symm r) :
    Set.Ico p (T.child p a) ∩ Set.Ico r (T.child r b) = ∅ := by
  have _ := ha
  refine Set.eq_empty_of_forall_notMem ?_
  rintro x ⟨⟨hpx, hxpa⟩, ⟨hrx, hxrb⟩⟩
  rcases lt_or_ge r p with hrp | hpr
  · -- p ∈ (r, r_1) なら 3.2.1 で q⁻¹ r < q⁻¹ p となり矛盾。よって r_1 ≤ p。
    have h1 : T.child r 1 ≤ p := by
      by_contra h
      push_neg at h
      have := (prop_3_2_1 hc (a := 1) (by omega) hrp h).1
      exact absurd (lt_trans this hnum) (lt_irrefl _)
    exact absurd (lt_of_lt_of_le hxrb
      (le_trans (Tree2.child_le_child T r (by omega) hb) (le_trans h1 hpx))) (lt_irrefl _)
  · have : T.child p a ≤ r := by
      by_contra h
      push_neg at h
      exact hr ⟨hpr, h⟩
    exact absurd (lt_of_lt_of_le hxpa (le_trans this hrx)) (lt_irrefl _)

theorem prop_3_2_3 (hc : Compat q T) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) {p r : α}
    (hpb : q.symm p ≤ b)
    (hne : (Set.Ico p (T.child p a) ∩ Set.Ico r (T.child r b)).Nonempty) :
    Set.Ico r (T.child r b) ⊆ Set.Ico p (T.child p a) := by
  obtain ⟨x, ⟨hpx, hxpa⟩, ⟨hrx, hxrb⟩⟩ := hne
  rcases lt_trichotomy p r with hpr | rfl | hrp
  · have hrpa : r < T.child p a := lt_of_le_of_lt hrx hxpa
    intro y hy
    have := (prop_3_2_1 hc ha hpr hrpa).2.2 b (by omega) hy
    exact ⟨this.1.le, this.2⟩
  · intro y hy
    exact ⟨hy.1, lt_of_lt_of_le hy.2 (Tree2.child_le_child T p ha hab)⟩
  · exfalso
    have hprb : p < T.child r b := lt_of_le_of_lt hpx hxrb
    have := (prop_3_2_1 hc (by omega) hrp hprb).2.1
    omega

end Defs.D_0016
