import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0063

namespace Defs.D_0064

/-!
**敵対的な firstC（深い元）と相棒の構成**（宣言された閉包の反例、検証報告 §11）。

* `code_le_of_le` / `hidx_le_of_qle` : code は各成分について単調。
* `qsymm_le_of_mem_Ico` : x ∈ [c, c_a) なら q⁻¹ c ≤ q⁻¹ x（c は x の祖先か x 自身）。
* `ShiftOK A N k0` : A の点の座標 k0 を [y k0, (y k0)_{lvl N y}) の中で動かしても A に留まる。
* `deep_elem` : A ≠ ∅、ShiftOK A N k0、N < n、k0 < n なら、lvl n を最小にする y ∈ A と、
  lncA n A の元 g(n, c) で c k0 = (y k0)_{lvl n y}（深い）、他の座標は y の祖先か y と同じものがある。
* `companion_of_deep` : そのとき u := c の座標 k0 を y k0 に戻した点は、k0 < p ≤ ph < n なら
  c ∈ g(ph, u)、lvl ph u ≤ lvl p c、u ∉ g(p, c) を満たす（Definition C で g(p, c) を呑み込む相棒）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0060

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

theorem delta_le {i j i' j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') : delta i j ≤ delta i' j' := by
  unfold delta
  have := tri_mono (show i + j ≤ i' + j' by omega)
  omega

theorem code_le_of_le : ∀ (n : ℕ) {v w : ℕ → ℕ}, (∀ k < n, v k ≤ w k) → code n v ≤ code n w
  | 0, _, _, _ => le_rfl
  | 1, _, _, h => h 0 (by omega)
  | n + 2, v, w, h => by
    show delta (code (n + 1) v) (v (n + 1)) ≤ delta (code (n + 1) w) (w (n + 1))
    exact delta_le (code_le_of_le (n + 1) (fun k hk => h k (by omega))) (h (n + 1) (by omega))

theorem hidx_le_of_qle {n : ℕ} {x y : ℕ → α} (h : ∀ k < n, q.symm (x k) ≤ q.symm (y k)) :
    hidx q n x ≤ hidx q n y := code_le_of_le n h

theorem qsymm_le_of_mem_Ico (hc : Compat2 q T) {a : ℕ} (ha : 0 < a) {c x : α}
    (h : x ∈ Set.Ico c (T.child c a)) : q.symm c ≤ q.symm x := by
  rcases eq_or_lt_of_le h.1 with he | hlt
  · rw [he]
  · exact (prop_3_2_1' hc ha hlt h.2).1.le

theorem lvl_lt_lvl {N n : ℕ} (hN : 0 < N) (hNn : N < n) (y : ℕ → α) :
    lvl q N y < lvl q n y := by
  have := code_mono N hN (fun k => q.symm (y k)) n hNn.le
  unfold lvl hidx; omega

theorem exists_min_lvl (n : ℕ) {A : Set (ℕ → α)} (hA : A.Nonempty) :
    ∃ y ∈ A, ∀ y' ∈ A, lvl q n y ≤ lvl q n y' := by
  classical
  have hex : ∃ N, ∃ y ∈ A, lvl q n y = N := ⟨_, hA.some, hA.some_mem, rfl⟩
  obtain ⟨y, hyA, hy⟩ := Nat.find_spec hex
  refine ⟨y, hyA, fun y' hy' => ?_⟩
  rw [hy]
  exact Nat.find_min' hex ⟨y', hy', rfl⟩

variable (q T) in
/-- 座標 k0 を右の小区間で動かしても A に留まる。 -/
def ShiftOK (A : Set (ℕ → α)) (N k0 : ℕ) : Prop :=
  ∀ y ∈ A, ∀ t ∈ Set.Ico (y k0) (T.child (y k0) (lvl q N y)), Function.update y k0 t ∈ A

theorem deep_elem (hc : Compat2 q T) {A : Set (ℕ → α)} (hA : A.Nonempty) {N n k0 : ℕ}
    (hN : 0 < N) (hNn : N < n) (hk0 : k0 < n) (hS : ShiftOK q T A N k0) :
    ∃ c y, c ∈ A ∧ y ∈ A ∧ gfun q T n c ∈ lncA q T n A ∧
      c k0 = T.child (y k0) (lvl q n y) ∧
      (∀ k < n, k ≠ k0 → q.symm (c k) ≤ q.symm (y k)) ∧
      (∀ y' ∈ A, lvl q n y ≤ lvl q n y') := by
  obtain ⟨y, hyA, hmin⟩ := exists_min_lvl (q := q) n hA
  set J := lvl q n y with hJ
  have hJ0 : 0 < J := lvl_pos q n y
  set e := Function.update y k0 (T.child (y k0) J) with he
  have heA : e ∈ A := by
    refine hS y hyA _ ⟨(T.lt_child _ _ (T.C_child _ _ hJ0)).le, ?_⟩
    refine T.child_anti _ _ _ (T.C_child _ _ (lvl_pos q N y)) (T.C_child _ _ hJ0) ?_
    rw [T.idx_child, T.idx_child]; exact lvl_lt_lvl hN hNn y
  obtain ⟨hEmem, heE⟩ := lncA_mem_spec hc (sub_gset (q := q) (T := T) n A heA)
  obtain ⟨c, hcA, hEc, -⟩ := hEmem
  rw [hEc] at heE
  have hn0 : 0 < n := by omega
  have hcy : lvl q n y ≤ lvl q n c := hmin c hcA
  have hek0 : e k0 = T.child (y k0) J := by simp [he]
  have hCy : T.C (y k0) (e k0) := hek0 ▸ T.C_child _ _ hJ0
  refine ⟨c, y, hcA, hyA, hEc ▸ (lncA_mem_spec hc (sub_gset (q := q) (T := T) n A heA)).1,
    ?_, ?_, hmin⟩
  · have h0 := heE.1 k0 hk0
    rcases eq_or_lt_of_le h0.1 with h | h
    · rw [h, hek0]
    · exfalso
      rcases shadow_cases hc (lvl_pos q n c) h h0.2 hCy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hek0, T.idx_child] at h2; omega
      · have h3 := (prop_3_2_1' hc (lvl_pos q n c) h1 h2).2.1
        have h4 := qsymm_lt_lvl (q := q) y hk0
        omega
  · intro k hk hne
    have h0 := heE.1 k hk
    have : e k = y k := by simp [he, hne]
    rw [this] at h0
    exact qsymm_le_of_mem_Ico hc (lvl_pos q n c) h0

/-- 深い元の相棒。 -/
theorem companion_of_deep (hc : Compat2 q T) {n p ph k0 : ℕ} (hk0p : k0 < p) (hpph : p ≤ ph)
    (hphn : ph < n) {c y : ℕ → α} (hck0 : c k0 = T.child (y k0) (lvl q n y))
    (hcy : ∀ k < n, k ≠ k0 → q.symm (c k) ≤ q.symm (y k)) :
    let u := Function.update c k0 (y k0)
    c ∈ gfun q T ph u ∧ lvl q ph u ≤ lvl q p c ∧ u ∉ gfun q T p c := by
  intro u
  have hJ0 : 0 < lvl q n y := lvl_pos q n y
  have huk0 : u k0 = y k0 := by simp [u]
  have huk : ∀ k, k ≠ k0 → u k = c k := fun k hk => by simp [u, hk]
  -- lvl ph u < lvl n y
  have hhu : hidx q ph u ≤ hidx q ph y := hidx_le_of_qle (fun k hk => by
    by_cases hkk : k = k0
    · rw [hkk, huk0]
    · rw [huk k hkk]; exact hcy k (by omega) hkk)
  have hhy : hidx q ph y ≤ hidx q n y :=
    code_mono ph (by omega) (fun k => q.symm (y k)) n hphn.le
  have hlt : lvl q ph u < lvl q n y := by unfold lvl at *; omega
  have hJc : lvl q n y ≤ q.symm (c k0) := by rw [hck0]; exact hc.idx_le_num _ _ hJ0
  have hcp := qsymm_lt_lvl (q := q) c hk0p
  refine ⟨⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩, by omega, ?_⟩
  · by_cases hkk : k = k0
    · subst hkk
      rw [huk0, hck0]
      refine ⟨(T.lt_child _ _ (T.C_child _ _ hJ0)).le, ?_⟩
      refine T.child_anti _ _ _ (T.C_child _ _ (lvl_pos q ph u)) (T.C_child _ _ hJ0) ?_
      rw [T.idx_child, T.idx_child]; exact hlt
    · rw [huk k hkk]; exact ⟨le_rfl, T.lt_child _ _ (T.C_child _ _ (lvl_pos q ph u))⟩
  · rw [← huk k (by omega)]; exact mem_ival T (lvl_pos q ph u) (u k)
  · intro hu
    have h := (hu.1 k0 hk0p).1
    rw [huk0, hck0] at h
    exact absurd h (not_le.mpr (T.lt_child _ _ (T.C_child _ _ hJ0)))

end Defs.D_0064
