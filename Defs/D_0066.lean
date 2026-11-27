import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0064
import Defs.D_0065

namespace Defs.D_0066

/-!
**敵対的な選択関数 `fcAdv`**（宣言された閉包の反例、検証報告 §11）。

層 n ≥ p₁ + 2 の族 lncA n A で「深い元」（`Defs.D_0064.deep_elem`）が取れるときはそれを選び、
それ以外は `firstC`（固定された列挙の番号 0 の元）を選ぶ。
* `weakFC_fcAdv` : fcAdv は ∅ か lncA の元を返す。
* `fcAdv_deep` : p₁+2 ≤ n、A ≠ ∅、ShiftOK A (n−1) k₀、k₀ < n なら fcAdv n A = g(n, c) で c は深い元の中心。
* `ShiftOK_inter`, `ShiftOK_gfun`, `ShiftOK_H` : ShiftOK は箱と H(m, c)（k₀ ≥ m）で成り立ち、交わりで保たれる。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0039 Defs.D_0040 Defs.D_0060 Defs.D_0064 Defs.D_0065

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

variable (q T) in
/-- 深い元の存在（選択関数の定義に使う命題）。 -/
def DeepWit (n k0 : ℕ) (A : Set (ℕ → α)) (c y : ℕ → α) : Prop :=
  c ∈ A ∧ y ∈ A ∧ gfun q T n c ∈ lncA q T n A ∧ c k0 = T.child (y k0) (lvl q n y) ∧
    (∀ k < n, k ≠ k0 → q.symm (c k) ≤ q.symm (y k)) ∧ (∀ y' ∈ A, lvl q n y ≤ lvl q n y')

open Classical in
variable (q T) in
/-- 敵対的な選択関数。 -/
noncomputable def fcAdv (p1 k0 : ℕ) (n : ℕ) (A : Set (ℕ → α)) : Set (ℕ → α) :=
  if h : p1 + 2 ≤ n ∧ ∃ c y, DeepWit q T n k0 A c y then gfun q T n h.2.choose
  else firstC q T n A

theorem weakFC_fcAdv (p1 k0 : ℕ) : WeakFC q T (fcAdv q T p1 k0) := by
  intro n A
  classical
  unfold fcAdv
  split_ifs with h
  · exact Or.inr h.2.choose_spec.choose_spec.2.2.1
  · exact firstC_cases n A

theorem fcAdv_deep (hc : Compat2 q T) {p1 k0 n : ℕ} {A : Set (ℕ → α)} (hn : p1 + 2 ≤ n)
    (hA : A.Nonempty) (hS : ShiftOK q T A (n - 1) k0) (hk0 : k0 < n) :
    ∃ c y, fcAdv q T p1 k0 n A = gfun q T n c ∧ DeepWit q T n k0 A c y := by
  classical
  have hex : ∃ c y, DeepWit q T n k0 A c y :=
    deep_elem hc hA (by omega) (by omega) hk0 hS
  have h : p1 + 2 ≤ n ∧ ∃ c y, DeepWit q T n k0 A c y := ⟨hn, hex⟩
  refine ⟨h.2.choose, h.2.choose_spec.choose, ?_, h.2.choose_spec.choose_spec⟩
  unfold fcAdv
  rw [dif_pos h]

theorem ShiftOK_inter {A B : Set (ℕ → α)} {N k0 : ℕ} (hA : ShiftOK q T A N k0)
    (hB : ShiftOK q T B N k0) : ShiftOK q T (A ∩ B) N k0 :=
  fun y hy t ht => ⟨hA y hy.1 t ht, hB y hy.2 t ht⟩

theorem ShiftOK_gfun (hc : Compat2 q T) {n' N k0 : ℕ} (hn' : 0 < n') (hn'N : n' ≤ N)
    (x : ℕ → α) : ShiftOK q T (gfun q T n' x) N k0 := by
  intro y hy t ht
  have hlv : lvl q n' x ≤ lvl q N y := by
    have h1 := hidx_le_of_mem_gfun hc hn' hy
    have h2 := code_mono n' hn' (fun k => q.symm (y k)) N hn'N
    unfold lvl hidx at *; omega
  have ha : 0 < lvl q n' x := lvl_pos q n' x
  refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · by_cases hkk : k = k0
    · subst hkk
      rw [Function.update_self]
      exact Ico_child_sub hc ha hlv (hy.1 k hk) ht
    · rw [Function.update_of_ne hkk]; exact hy.1 k hk
  · by_cases hkk : k = k0
    · subst hkk
      rw [Function.update_self]
      exact Ico_child_sub hc ha hlv (hy.2 k hk1 hk2) ht
    · rw [Function.update_of_ne hkk]; exact hy.2 k hk1 hk2

theorem ShiftOK_H {m N k0 : ℕ} (hm : 0 < m) (hk0 : m ≤ k0) (c : ℕ) :
    ShiftOK q T (H q m c) N k0 := by
  intro y hy t _
  have : hidx q m (Function.update y k0 t) = hidx q m y :=
    (code_eq_iff m hm _ _).2 (fun j hj => by
      show q.symm (Function.update y k0 t j) = q.symm (y j)
      rw [Function.update_of_ne (by omega)])
  exact this.trans hy

theorem ShiftOK_empty {N k0 : ℕ} : ShiftOK q T (∅ : Set (ℕ → α)) N k0 :=
  fun _ hy => absurd hy (Set.notMem_empty _)

theorem ShiftOK_lncA (hc : Compat2 q T) {n N k0 : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    {A S : Set (ℕ → α)} (hS : S ∈ lncA q T n A) : ShiftOK q T S N k0 := by
  obtain ⟨x, -, rfl, -⟩ := hS
  exact ShiftOK_gfun hc hn hnN x

theorem ShiftOK_slabO (hc : Compat2 q T) {m N k0 : ℕ} (hm : 0 < m) (hmN : m ≤ N)
    (hk0 : m ≤ k0) (y0 : ℕ → α) (c : ℕ) : ShiftOK q T (slabO q T m y0 c) N k0 := by
  classical
  unfold slabO
  split_ifs
  · exact ShiftOK_empty
  · exact ShiftOK_inter (ShiftOK_H hm hk0 c) (ShiftOK_gfun hc hm hmN y0)

end Defs.D_0066
