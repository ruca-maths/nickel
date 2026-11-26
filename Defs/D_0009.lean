import Mathlib.Topology.Order
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Logic.Relation
import Defs.D_0003

namespace Defs.D_0009

/-!
Chen–Wang (arXiv 1809.03763v2) 第2節冒頭の位相 ρ′ と、Construction 2 / Prop 2.2.1 の
「I_a は c.o.D（開閉集合からなる離散族）」の部分。

* `rho α` : 半開区間 `[p, q)` 全体で生成される位相（論文の ρ′。Q = ℚ ∩ [0,1) 上で使う）。
* `isOpen_Ico` : `[p, q)` は開。
* `isClosed_Ico` : `[p, q)` は閉（`NoMaxOrder` が要る。Q = ℚ ∩ [0,1) は最大元を持たない）。
* `IsDiscreteFam` : 族 `s : ι → Set α` が離散（各点に、高々1つの添字の元としか交わらない開近傍がある）。
* `I_clopen`, `I_discrete` : `I_a = {[p, p_a) : p ∈ Q*_a}`（a ≥ 1）は c.o.D。
  離散性は `prop_2_2_1`（I_a は分割）から、点を含む区間そのものを近傍に取って出る。
-/

open Defs.D_0003 Defs.D_0003.Tree2

variable {α : Type} [LinearOrder α]

/-- 論文の位相 ρ′: 半開区間 `[p, q)` で生成される位相。 -/
def rho (α : Type) [LinearOrder α] : TopologicalSpace α :=
  TopologicalSpace.generateFrom {s | ∃ p q : α, s = Set.Ico p q}

theorem isOpen_Ico (p q : α) : @IsOpen α (rho α) (Set.Ico p q) :=
  TopologicalSpace.GenerateOpen.basic _ ⟨p, q, rfl⟩

theorem isClosed_Ico [NoMaxOrder α] (p q : α) : @IsClosed α (rho α) (Set.Ico p q) := by
  letI := rho α
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rcases lt_or_ge x p with hxp | hpx
  · refine ⟨Set.Ico x p, ?_, isOpen_Ico x p, ⟨le_rfl, hxp⟩⟩
    intro y hy hy'
    exact absurd hy'.1 (not_le.mpr hy.2)
  · have hqx : q ≤ x := by
      by_contra h
      exact hx ⟨hpx, not_le.mp h⟩
    obtain ⟨y, hy⟩ := exists_gt x
    refine ⟨Set.Ico x y, ?_, isOpen_Ico x y, ⟨le_rfl, hy⟩⟩
    intro z hz hz'
    exact absurd (lt_of_lt_of_le hz'.2 (le_trans hqx hz.1)) (lt_irrefl _)

/-- 族 `s` が（位相 `t` で）離散。 -/
def IsDiscreteFam (t : TopologicalSpace α) {ι : Type} (s : ι → Set α) : Prop :=
  ∀ x : α, ∃ U : Set α, @IsOpen α t U ∧ x ∈ U ∧
    ∀ i j, (s i ∩ U).Nonempty → (s j ∩ U).Nonempty → s i = s j

/-- I_a の各元は ρ′ で開かつ閉。 -/
theorem I_clopen [NoMaxOrder α] (T : Tree2 α) (a : ℕ) (p : α) :
    @IsOpen α (rho α) (Set.Ico p (T.child p a)) ∧
      @IsClosed α (rho α) (Set.Ico p (T.child p a)) :=
  ⟨isOpen_Ico _ _, isClosed_Ico _ _⟩

/-- I_a（a ≥ 1）は ρ′ で離散族（`{p // p ∈ Q*_a}` で添字づけ）。 -/
theorem I_discrete (T : Tree2 α) {a : ℕ} (ha : 0 < a) :
    IsDiscreteFam (rho α)
      (fun p : {p : α // T.QStar a p} => Set.Ico p.1 (T.child p.1 a)) := by
  intro x
  obtain ⟨p, ⟨hp, hx⟩, _⟩ := prop_2_2_1 T ha x
  refine ⟨Set.Ico p (T.child p a), isOpen_Ico _ _, hx, ?_⟩
  have key : ∀ i : {p : α // T.QStar a p},
      (Set.Ico i.1 (T.child i.1 a) ∩ Set.Ico p (T.child p a)).Nonempty → i.1 = p := by
    rintro ⟨i, hi⟩ ⟨y, hy1, hy2⟩
    by_contra hne
    exact Set.disjoint_left.mp (prop_2_2_1_disjoint T ha hi hp hne) hy1 hy2
  intro i j hi hj
  simp only
  rw [key i hi, key j hj]

/-- I_a（a ≥ 1）は ρ′ で c.o.D であり、和は全体。 -/
theorem I_coD [NoMaxOrder α] (T : Tree2 α) {a : ℕ} (ha : 0 < a) :
    (∀ p, T.QStar a p →
      @IsOpen α (rho α) (Set.Ico p (T.child p a)) ∧
        @IsClosed α (rho α) (Set.Ico p (T.child p a))) ∧
    IsDiscreteFam (rho α)
      (fun p : {p : α // T.QStar a p} => Set.Ico p.1 (T.child p.1 a)) ∧
    (∀ x, ∃ p, T.QStar a p ∧ x ∈ Set.Ico p (T.child p a)) :=
  ⟨fun p _ => I_clopen T a p, I_discrete T ha, prop_2_2_1_cover T ha⟩

end Defs.D_0009
