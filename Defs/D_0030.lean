import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0029

namespace Defs.D_0030

/-!
Chen–Wang (arXiv 1809.03763v2) Proposition 3.5.2, 3.5.3（位相 ρ = `Defs.D_0029.ptop`、ρ′ の積）。

* `isClosed_singleton_rho` : ρ′ で 1 点集合は閉（NoMaxOrder）。
* `Hcell_isClosed_p` : H(n, x) は ρ で閉。
* `prop_3_5_2` : Cl_ρ [H(n, y) − H(n+1, y)] = H(n, y)（DenselyOrdered, NoMaxOrder）。
* `prop_3_5_3` : n_i が狭義増加で H(n_{i+1}, y_{i+1}) ⊆ H(n_i, y_i) なら ⋂_i H(n_i, y_i) は 1 点。
  （集合論的な主張。位相は使わない。）
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0009 Defs.D_0012 Defs.D_0029

variable {α : Type} [LinearOrder α]

theorem isClosed_singleton_rho [NoMaxOrder α] (x : α) : @IsClosed α (rho α) {x} := by
  let _ : TopologicalSpace α := rho α
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  rcases lt_or_gt_of_ne (show y ≠ x from hy) with h | h
  · refine ⟨Set.Ico y x, ?_, isOpen_Ico y x, ⟨le_rfl, h⟩⟩
    intro w hw hwx
    rw [Set.mem_singleton_iff.mp hwx] at hw
    exact lt_irrefl _ hw.2
  · obtain ⟨b, hb⟩ := exists_gt y
    refine ⟨Set.Ico y b, ?_, isOpen_Ico y b, ⟨le_rfl, hb⟩⟩
    intro w hw hwx
    rw [Set.mem_singleton_iff.mp hwx] at hw
    exact absurd (lt_of_lt_of_le h hw.1) (lt_irrefl _)

variable (q : ℕ ≃ α) (T : Tree2 α)

theorem Hcell_isClosed_p [NoMaxOrder α] (n : ℕ) (x : ℕ → α) :
    @IsClosed (ℕ → α) (ptop α) (Hcell q T n x) := by
  rw [Hcell_eq]
  refine isClosed_fin_p _ _ (fun k _ => ?_)
  split_ifs
  · exact isClosed_singleton_rho _
  · exact isClosed_Ico _ _

/-- Proposition 3.5.2: Cl_ρ [H(n, y) − H(n+1, y)] = H(n, y)。 -/
theorem prop_3_5_2 [NoMaxOrder α] [DenselyOrdered α] (n : ℕ) (y : ℕ → α) :
    @closure (ℕ → α) (ptop α) (Hcell q T n y \ Hcell q T (n + 1) y) = Hcell q T n y := by
  let _ : TopologicalSpace α := rho α
  let _ : TopologicalSpace (ℕ → α) := ptop α
  apply le_antisymm
  · exact closure_minimal Set.diff_subset (Hcell_isClosed_p q T n y)
  · intro z hz
    rw [mem_closure_iff]
    intro V hVo hzV
    obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hVo z hzV
    have hb : ∃ b, z n < b ∧ (n ∈ I → Set.Ico (z n) b ⊆ u n) := by
      by_cases h0 : n ∈ I
      · obtain ⟨b, hb, hs⟩ := rho_nhd (hu n h0).1 (hu n h0).2
        exact ⟨b, hb, fun _ => hs⟩
      · obtain ⟨b, hb⟩ := exists_gt (z n)
        exact ⟨b, hb, fun h => absurd h h0⟩
    obtain ⟨b, hzb, hbs⟩ := hb
    have hzn : z n ∈ ival T (lvl q n y) (y n) := hz.2 n le_rfl (by omega)
    set e := T.child (ibase T (lvl q n y) (y n)) (lvl q n y)
    have hze : z n < e := hzn.2
    have hw : ∃ w, z n ≤ w ∧ w < min b e ∧ w ≠ y n := by
      by_cases hy : z n = y n
      · obtain ⟨w, hw1, hw2⟩ := exists_between (lt_min hzb hze)
        exact ⟨w, hw1.le, hw2, fun h => by rw [h, hy] at hw1; exact lt_irrefl _ hw1⟩
      · exact ⟨z n, le_rfl, lt_min hzb hze, hy⟩
    obtain ⟨w, hw1, hw2, hw3⟩ := hw
    refine ⟨Function.update z n w, ?_, ?_, ?_⟩
    · apply hsub
      intro a ha
      by_cases h : a = n
      · subst h
        rw [Function.update_self]
        exact hbs ha ⟨hw1, lt_of_lt_of_le hw2 (min_le_left _ _)⟩
      · rw [Function.update_of_ne h]
        exact (hu a ha).2
    · refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
      · rw [Function.update_of_ne (by omega)]
        exact hz.1 k hk
      · by_cases h : k = n
        · subst h
          rw [Function.update_self]
          exact ⟨le_trans hzn.1 hw1, lt_of_lt_of_le hw2 (min_le_right _ _)⟩
        · rw [Function.update_of_ne h]
          exact hz.2 k hk1 hk2
    · intro h
      have := h.1 n (by omega)
      rw [Function.update_self] at this
      exact hw3 this

/-- Proposition 3.5.3: 狭義増加の n_i と入れ子の H(n_i, y_i) の共通部分は 1 点。 -/
theorem prop_3_5_3 (ns : ℕ → ℕ) (hns : StrictMono ns) (ys : ℕ → ℕ → α)
    (hsub : ∀ i, Hcell q T (ns (i + 1)) (ys (i + 1)) ⊆ Hcell q T (ns i) (ys i)) :
    ∃ y : ℕ → α, (⋂ i, Hcell q T (ns i) (ys i)) = {y} := by
  have hanti : ∀ i j, i ≤ j → Hcell q T (ns j) (ys j) ⊆ Hcell q T (ns i) (ys i) := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | step _ ih => exact le_trans (hsub _) ih
  have hmem : ∀ i, ys i ∈ Hcell q T (ns i) (ys i) := fun i => mem_Hcell q T _ _
  have hge : ∀ i, i ≤ ns i := fun i => hns.id_le i
  -- 整合性: i ≤ j, k < ns i なら ys j k = ys i k
  have hcons : ∀ i j, i ≤ j → ∀ k < ns i, ys j k = ys i k :=
    fun i j hij k hk => (hanti i j hij (hmem j)).1 k hk
  refine ⟨fun k => ys (k + 1) k, ?_⟩
  ext z
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro hz
    funext k
    exact (hz (k + 1)).1 k (by have := hge (k + 1); omega)
  · rintro rfl i
    -- ys j は j ≥ i で十分大きければ問題の座標で y と一致する
    have key : ∀ j, i ≤ j → ∀ k < ns j, ys (k + 1) k = ys j k := by
      intro j hij k hk
      rcases le_total (k + 1) j with h | h
      · exact (hcons (k + 1) j h k (by have := hge (k + 1); omega)).symm
      · exact hcons j (k + 1) h k hk
    have hyi := hmem i
    refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
    · show ys (k + 1) k = ys i k
      exact key i le_rfl k hk
    · -- j を十分大きく取る
      set j := i + k + 1
      have hj : i ≤ j := by omega
      have hkj : k < ns j := by have := hge j; omega
      show ys (k + 1) k ∈ _
      rw [key j hj k hkj]
      exact (hanti i j hj (hmem j)).2 k hk1 hk2

end Defs.D_0030
