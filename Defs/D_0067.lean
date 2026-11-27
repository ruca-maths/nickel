import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0066
import Defs.D_0049

namespace Defs.D_0067

/-!
反例の補助（一般化版）:
* `MixOK A k0` : A の 2 点 c, y について、c の座標 k0 を y k0 に替えても A に留まる。
  箱、H(m, c)（k0 ≥ m）、slab で成り立ち、交わりで保たれる。
* `branch_eq_of_pieces` : 同じ点を含む 2 つの piece は、branch 番号も piece 番号も一致する。
* `mem_HkOF` : HkOF の点は、ある slab の元の branch k+2 の piece（番号 ≥ p(k+2)）の G_d の箱 ∩ piece の点。
* `not_mem_HkOF_of_branch1` : branch 1 の piece の点は、どの slab の穴（HkOF、k = 0）にも入らない。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0040 Defs.D_0049 Defs.D_0062
  Defs.D_0065

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}
  {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)}

def MixOK (A : Set (ℕ → α)) (k0 : ℕ) : Prop :=
  ∀ c ∈ A, ∀ y ∈ A, Function.update c k0 (y k0) ∈ A

theorem MixOK_inter {A B : Set (ℕ → α)} {k0 : ℕ} (hA : MixOK A k0) (hB : MixOK B k0) :
    MixOK (A ∩ B) k0 :=
  fun c hc y hy => ⟨hA c hc.1 y hy.1, hB c hc.2 y hy.2⟩

theorem MixOK_gfun (n : ℕ) (x : ℕ → α) (k0 : ℕ) : MixOK (gfun q T n x) k0 := by
  intro c hc y hy
  refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · by_cases hkk : k = k0
    · subst hkk; rw [Function.update_self]; exact hy.1 k hk
    · rw [Function.update_of_ne hkk]; exact hc.1 k hk
  · by_cases hkk : k = k0
    · subst hkk; rw [Function.update_self]; exact hy.2 k hk1 hk2
    · rw [Function.update_of_ne hkk]; exact hc.2 k hk1 hk2

theorem MixOK_H (hm : 0 < m) {k0 : ℕ} (hk0 : m ≤ k0) (c : ℕ) : MixOK (H q m c) k0 := by
  intro w hw y _
  have : hidx q m (Function.update w k0 (y k0)) = hidx q m w :=
    (code_eq_iff m hm _ _).2 (fun j hj => by
      show q.symm (Function.update w k0 (y k0) j) = q.symm (w j)
      rw [Function.update_of_ne (by omega)])
  exact this.trans hw

theorem MixOK_slabO (hm : 0 < m) {k0 : ℕ} (hk0 : m ≤ k0) (c : ℕ) :
    MixOK (slabO q T m y0 c) k0 := by
  classical
  unfold slabO
  split_ifs
  · intro c' hc'; exact absurd hc' (Set.notMem_empty _)
  · exact MixOK_inter (MixOK_H hm hk0 c) (MixOK_gfun m y0 k0)

theorem MixOK_lncA {n : ℕ} {A S : Set (ℕ → α)} (hS : S ∈ lncA q T n A) (k0 : ℕ) :
    MixOK S k0 := by
  obtain ⟨x, -, rfl, -⟩ := hS
  exact MixOK_gfun n x k0

theorem branch_eq_of_pieces (hc : Compat2 q T) {c c' k k' : ℕ} {S S' : Set (ℕ → α)}
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c))
    (hS' : S' ∈ lncA q T (m + 1) (slabO q T m y0 c')) {Pv Pv' : Set (ℕ → α) × ℕ}
    (hP : Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) k)
    (hP' : Pv' ∈ pieces q T m (slabO q T m y0 c' ∩ S') k') {x : ℕ → α}
    (hx : x ∈ Pv.1) (hx' : x ∈ Pv'.1) : k = k' := by
  have hPP := piece_unique hc hS hS' hP hP' hx hx'
  obtain ⟨S2, hS2, hl2, S3, hS3, -, hPe⟩ := hP
  obtain ⟨S2', hS2', hl2', S3', hS3', -, hPe'⟩ := hP'
  have hxP := hx
  rw [hPe] at hx
  rw [hPe'] at hx'
  have hcc : c = c' := by
    by_contra hne
    exact Set.disjoint_left.mp (slabO_disjoint (q := q) (T := T) (m := m) (y0 := y0) hne)
      hx.1.1.1 hx'.1.1.1
  subst hcc
  have hSS : S = S' := lncA_unique hc hS hS' hx.1.1.2 hx'.1.1.2
  subst hSS
  have h22 : S2 = S2' := lncA_unique hc hS2 hS2' hx.1.2 hx'.1.2
  subst h22
  rw [← hl2, ← hl2']

theorem holeCellsF_sub_slab (a : ℕ → ℕ) (k r c : ℕ) (S : Set (ℕ → α)) :
    holeCellsF q T m fc a k r (slabO q T m y0 c ∩ S) ⊆ slabO q T m y0 c := by
  intro w hw
  simp only [holeCellsF, Set.mem_iUnion, exists_prop] at hw
  obtain ⟨Pv, ⟨hPv, -⟩, B, -, -, hwP⟩ := hw
  obtain ⟨S2, -, -, S3, -, -, hPe⟩ := hPv
  rw [hPe] at hwP
  exact hwP.1.1.1

theorem mem_HkOF {a p : ℕ → ℕ} {k : ℕ} {prevD : ℕ → Set (ℕ → α)} {c : ℕ} {x : ℕ → α}
    (hx : x ∈ HkOF q T m y0 fc a p k prevD c) :
    ∃ S Pv B, S ∈ lncA q T (m + 1) (slabO q T m y0 c) ∧
      Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) (k + 2) ∧ p (k + 2) ≤ Pv.2 ∧
      B ∈ GdF q T m fc a Pv.1 Pv.2 ∧ x ∈ B ∧ x ∈ Pv.1 := by
  unfold HkOF slabRec at hx
  obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp hx
  simp only [holeCellsF, Set.mem_iUnion, exists_prop] at hxS
  obtain ⟨Pv, ⟨hPv, hr⟩, B, hB, hxB, hxP⟩ := hxS
  exact ⟨S, Pv, B, hS.1, hPv, hr, hB, hxB, hxP⟩

theorem not_mem_HkOF_of_branch1 (hc : Compat2 q T) {c : ℕ} {S : Set (ℕ → α)}
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c)) {Pv : Set (ℕ → α) × ℕ}
    (hP : Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) 1) {u : ℕ → α} (hu : u ∈ Pv.1)
    (a p : ℕ → ℕ) (prevD : ℕ → Set (ℕ → α)) (c' : ℕ) :
    u ∉ HkOF q T m y0 fc a p 0 prevD c' := by
  intro h
  obtain ⟨S', Pv', -, hS', hP', -, -, -, huP'⟩ := mem_HkOF h
  have := branch_eq_of_pieces hc hS hS' hP hP' hu huP'
  omega

end Defs.D_0067
