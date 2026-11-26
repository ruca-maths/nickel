import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Lattice

namespace Defs.D_0007

/-!
Chen–Wang (arXiv 1809.03763v2) 第3節 Construction 3.1 と Proposition 3.1（集合論的な部分）。

* `Q` は `q : ℕ ≃ α` で番号付けされている（論文の `Q = {q_i : i ∈ ω}`）。
  `X = ℕ → α`（論文の `X = Π_n Q_n`。論文の第 `k` 座標 (k ≥ 1) は ここの `k - 1`）。
* Δ-順序（Figure I）: `delta i j = tri (i + j) + i`（`tri s = s(s+1)/2`）。
  論文の `l = (i+j-2)(i+j-1)/2 + i`（i, j ≥ 1）とは、番号をすべて 0 始まりにずらしたもの
  （論文の `(i, j, l)` ↔ ここの `(i-1, j-1, l-1)`）。
* `code n v`: 先頭 `n` 座標の番号列 `v 0, …, v (n-1)` の Δ-順序での番号。
  `code 1 v = v 0`, `code (n+2) v = delta (code (n+1) v) (v (n+1))`。
* `H n c = {x | code n (q.symm ∘ x) = c}`（論文の `H(n, c+1)`）。

示すこと（n ≥ 1）:
* `delta` は全単射（`delta_inj`, `delta_surj`）。
* `code_eq_iff`: `code n v = code n w ↔ ∀ k < n, v k = w k`。`code_surj`。
* Prop 3.1.1: `H n` は `X` の分割（`H_nonempty`, `H_cover`, `H_disjoint`）。
* Prop 3.1.3（集合部分）: `n ≤ n'` なら `H n' c' ⊆ H n c` か交わらない（`H_laminar`）。
* Prop 3.1.4: `H n' c' ⊆ H n c` なら `n ≤ n'` かつ `c ≤ c'`（`H_sub_index`。`α` が2点以上必要）。
* Prop 3.1.5: `v k ≤ code n v`（k < n）（`code_ge`）。
-/

/-- 三角数 `tri s = s(s+1)/2`。 -/
def tri : ℕ → ℕ
  | 0 => 0
  | s + 1 => tri s + s + 1

/-- Δ-順序の番号付け（0 始まり）。 -/
def delta (i j : ℕ) : ℕ := tri (i + j) + i

theorem tri_mono {s t : ℕ} (h : s ≤ t) : tri s ≤ tri t := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => simp only [tri]; omega

theorem le_tri (s : ℕ) : s ≤ tri s := by
  induction s with
  | zero => simp [tri]
  | succ s ih => simp only [tri]; omega

theorem delta_lt (i j : ℕ) : delta i j < tri (i + j + 1) := by
  simp only [delta, tri]; omega

theorem tri_le_delta (i j : ℕ) : tri (i + j) ≤ delta i j := by
  simp [delta]

theorem delta_sum_eq {i j i' j' : ℕ} (h : delta i j = delta i' j') : i + j = i' + j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := delta_lt i j
    have h2 := tri_mono (show i + j + 1 ≤ i' + j' by omega)
    have h3 := tri_le_delta i' j'
    omega
  · have h1 := delta_lt i' j'
    have h2 := tri_mono (show i' + j' + 1 ≤ i + j by omega)
    have h3 := tri_le_delta i j
    omega

theorem delta_inj {i j i' j' : ℕ} (h : delta i j = delta i' j') : i = i' ∧ j = j' := by
  have hs := delta_sum_eq h
  have h' : tri (i + j) + i = tri (i' + j') + i' := h
  rw [hs] at h'
  omega

theorem delta_surj (c : ℕ) : ∃ i j, delta i j = c := by
  induction c with
  | zero => exact ⟨0, 0, rfl⟩
  | succ c ih =>
    obtain ⟨i, j, h⟩ := ih
    rcases j with _ | j
    · refine ⟨0, i + 1, ?_⟩
      have h' : tri (i + 0) + i = c := h
      rw [Nat.add_zero] at h'
      show tri (0 + (i + 1)) + 0 = c + 1
      rw [Nat.zero_add, Nat.add_zero]
      show tri i + i + 1 = c + 1
      omega
    · refine ⟨i + 1, j, ?_⟩
      have : i + 1 + j = i + (j + 1) := by omega
      simp only [delta, this] at h ⊢
      omega

theorem delta_ge_left (i j : ℕ) : i ≤ delta i j := by simp [delta]

theorem delta_ge_right (i j : ℕ) : j ≤ delta i j := by
  have := le_tri (i + j); simp only [delta]; omega

/-- 先頭 `n` 座標の Δ-順序での番号。 -/
def code : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | 1, v => v 0
  | n + 2, v => delta (code (n + 1) v) (v (n + 1))

theorem code_succ (n : ℕ) (hn : 0 < n) (v : ℕ → ℕ) :
    code (n + 1) v = delta (code n v) (v n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

/-- `code n v` は先頭 `n` 座標で決まり、それらを決める。 -/
theorem code_eq_iff (n : ℕ) (hn : 0 < n) (v w : ℕ → ℕ) :
    code n v = code n w ↔ ∀ k < n, v k = w k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      show v 0 = w 0 ↔ ∀ k, k < 0 + 1 → v k = w k
      constructor
      · intro h k hk
        have : k = 0 := by omega
        subst this; exact h
      · intro h; exact h 0 (by omega)
    · rw [code_succ n hpos, code_succ n hpos]
      constructor
      · intro h k hk
        obtain ⟨h1, h2⟩ := delta_inj h
        by_cases hk' : k < n
        · exact (ih hpos).mp h1 k hk'
        · have : k = n := by omega
          subst this; exact h2
      · intro h
        have h1 : code n v = code n w := (ih hpos).mpr (fun k hk => h k (by omega))
        rw [h1, h (n) (by omega)]

/-- `code n` は全射（n ≥ 1）。値は先頭 `n` 座標以外で自由に選べる。 -/
theorem code_surj (n : ℕ) (hn : 0 < n) (c : ℕ) (w : ℕ → ℕ) :
    ∃ v : ℕ → ℕ, code n v = c ∧ ∀ k, n ≤ k → v k = w k := by
  induction n generalizing c with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      refine ⟨Function.update w 0 c, (by show Function.update w 0 c 0 = c; exact Function.update_self 0 c w), ?_⟩
      intro k hk
      rw [Function.update_of_ne (by omega)]
    · obtain ⟨i, j, hij⟩ := delta_surj c
      obtain ⟨v, hv, hvw⟩ := ih hpos i
      refine ⟨Function.update v n j, ?_, ?_⟩
      · rw [code_succ n hpos]
        have : code n (Function.update v n j) = code n v :=
          (code_eq_iff n hpos _ _).mpr (fun k hk => by rw [Function.update_of_ne (by omega)])
        rw [this, hv, Function.update_self, hij]
      · intro k hk
        rw [Function.update_of_ne (by omega)]
        exact hvw k (by omega)

/-- Proposition 3.1.5: 各座標の番号は `code` 以下。 -/
theorem code_ge (n : ℕ) (v : ℕ → ℕ) : ∀ k < n, v k ≤ code n v := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have : k = 0 := by omega
      subst this; exact le_rfl
    · rw [code_succ n hpos]
      by_cases hk' : k < n
      · exact le_trans (ih k hk') (delta_ge_left _ _)
      · have : k = n := by omega
        subst this; exact delta_ge_right _ _

/-- `code` は長さについて単調（Prop 3.1.4 の番号の部分）。 -/
theorem code_mono (n : ℕ) (hn : 0 < n) (v : ℕ → ℕ) : ∀ m, n ≤ m → code n v ≤ code m v := by
  intro m hm
  induction hm with
  | refl => exact le_rfl
  | @step m hle ih =>
    have hm0 : 0 < m := lt_of_lt_of_le hn hle
    rw [code_succ m hm0]
    exact le_trans ih (delta_ge_left _ _)

section H

variable {α : Type} (q : ℕ ≃ α)

/-- 論文の `H(n, c+1) = {q_{i_1}} × … × {q_{i_n}} × X_n`。 -/
def H (n c : ℕ) : Set (ℕ → α) := {x | code n (fun k => q.symm (x k)) = c}

theorem mem_H_iff_same (n : ℕ) (hn : 0 < n) (x y : ℕ → α) :
    (x ∈ H q n (code n (fun k => q.symm (y k)))) ↔ ∀ k < n, x k = y k := by
  show code n (fun k => q.symm (x k)) = code n (fun k => q.symm (y k)) ↔ _
  rw [code_eq_iff n hn]
  constructor
  · intro h k hk
    exact q.symm.injective (h k hk)
  · intro h k hk
    show q.symm (x k) = q.symm (y k)
    rw [h k hk]

/-- Prop 3.1.1: 各 `H n c` は空でない（n ≥ 1）。 -/
theorem H_nonempty (n : ℕ) (hn : 0 < n) (c : ℕ) : (H q n c).Nonempty := by
  obtain ⟨v, hv, -⟩ := code_surj n hn c (fun _ => 0)
  refine ⟨fun k => q (v k), ?_⟩
  show code n (fun k => q.symm (q (v k))) = c
  simp only [Equiv.symm_apply_apply]
  exact hv

/-- Prop 3.1.1: `H n` は `X` を覆う。 -/
theorem H_cover (n : ℕ) (x : ℕ → α) : ∃ c, x ∈ H q n c :=
  ⟨code n (fun k => q.symm (x k)), rfl⟩

/-- Prop 3.1.1: `H n` の元は互いに素。 -/
theorem H_disjoint (n : ℕ) {c c' : ℕ} (h : c ≠ c') : Disjoint (H q n c) (H q n c') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have e1 : code n (fun k => q.symm (x k)) = c := hx
  have e2 : code n (fun k => q.symm (x k)) = c' := hx'
  exact h (e1.symm.trans e2)

/-- Prop 3.1.3（集合部分）: `n ≤ n'` なら `H n' c' ⊆ H n c` か交わらない。 -/
theorem H_laminar {n n' : ℕ} (hn : 0 < n) (hnn : n ≤ n') (c c' : ℕ) :
    H q n' c' ⊆ H q n c ∨ Disjoint (H q n' c') (H q n c) := by
  by_cases hd : Disjoint (H q n' c') (H q n c)
  · exact Or.inr hd
  · left
    obtain ⟨y, hy0, hy'0⟩ := Set.not_disjoint_iff.mp hd
    have hy : code n' (fun k => q.symm (y k)) = c' := hy0
    have hy' : code n (fun k => q.symm (y k)) = c := hy'0
    intro x hx
    have hxy : ∀ k < n', x k = y k := by
      have := (mem_H_iff_same q n' (by omega) x y)
      rw [hy] at this
      exact this.mp hx
    have : x ∈ H q n (code n (fun k => q.symm (y k))) :=
      (mem_H_iff_same q n hn x y).mpr (fun k hk => hxy k (by omega))
    rwa [hy'] at this

/-- Prop 3.1.4: `H n' c' ⊆ H n c` なら `n ≤ n'` かつ `c ≤ c'`（`α` が2点以上のとき）。 -/
theorem H_sub_index (hα : ∃ a b : α, a ≠ b) {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n')
    {c c' : ℕ} (hsub : H q n' c' ⊆ H q n c) : n ≤ n' ∧ c ≤ c' := by
  classical
  obtain ⟨y, hy0⟩ := H_nonempty q n' hn' c'
  have hyc : code n (fun k => q.symm (y k)) = c := hsub hy0
  have hy : code n' (fun k => q.symm (y k)) = c' := hy0
  have hnn : n ≤ n' := by
    by_contra hnot
    have hlt : n' < n := Nat.lt_of_not_le hnot
    obtain ⟨a, b, hab⟩ := hα
    -- 座標 n' だけを y と異なる値に変えた点
    have hz : Function.update y n' (if y n' = a then b else a) ∈ H q n' c' := by
      have := (mem_H_iff_same q n' hn'
        (Function.update y n' (if y n' = a then b else a)) y).mpr
        (fun k hk => by rw [Function.update_of_ne (by omega)])
      rwa [hy] at this
    have hzc := hsub hz
    rw [← hyc] at hzc
    have := (mem_H_iff_same q n hn _ y).mp hzc n' hlt
    rw [Function.update_self] at this
    by_cases h1 : y n' = a
    · rw [if_pos h1, h1] at this
      exact hab this.symm
    · rw [if_neg h1] at this
      exact h1 this.symm
  refine ⟨hnn, ?_⟩
  rw [← hyc, ← hy]
  exact code_mono n hn _ n' hnn

/-- 親子関係: `H (n+1) (delta c j) ⊆ H n c`（Figure I の `P(n,i) × {q_j}`）。 -/
theorem H_succ_sub (n : ℕ) (hn : 0 < n) (c j : ℕ) : H q (n + 1) (delta c j) ⊆ H q n c := by
  intro x hx
  have hx' : code (n + 1) (fun k => q.symm (x k)) = delta c j := hx
  rw [code_succ n hn] at hx'
  exact (delta_inj hx').1

end H

end Defs.D_0007
