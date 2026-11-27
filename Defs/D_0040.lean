import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0039

namespace Defs.D_0040

/-!
Chen–Wang の E(αk, p)（`Defs.D_0039.EsetO`）はセル位相で開かつ閉（`EsetO_SOpen`, `EsetO_SClosed`）。

鍵は次の 3 点:
* piece P = slab ∩ S ∩ S2 ∩ S3 は深さ m+3 以上のセルについて安定（`piece_stable`）。
* 点 x を含む piece は（slab・各層の元の一意性から）番号まで一意（`piece_unique`）。
* その piece の G_d の箱はすべて深さ ≤ max(m+5, α(m+v)+1) の箱（`Gd_level`）。
よって穴の和（任意の部分族の和）は局所有限で、セル位相で閉（`holes_SClosed`）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0032 Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

/-- 深さ ≥ n のセルについて安定。 -/
def Stable (q : ℕ ≃ α) (T : Tree2 α) (n : ℕ) (A : Set (ℕ → α)) : Prop :=
  ∀ w ∈ A, ∀ L, n ≤ L → Hcell q T L w ⊆ A

theorem Stable.inter {n n' : ℕ} {A B : Set (ℕ → α)} (hA : Stable q T n A) (hB : Stable q T n' B) :
    Stable q T (max n n') (A ∩ B) := fun w hw L hL =>
  Set.subset_inter (hA w hw.1 L (le_of_max_le_left hL)) (hB w hw.2 L (le_of_max_le_right hL))

theorem Stable.mono {n n' : ℕ} {A : Set (ℕ → α)} (hA : Stable q T n A) (h : n ≤ n') :
    Stable q T n' A := fun w hw L hL => hA w hw L (h.trans hL)

theorem stable_lncA (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) {A S : Set (ℕ → α)}
    (hS : S ∈ lncA q T n A) : Stable q T n S := by
  obtain ⟨x, -, rfl, -⟩ := hS
  intro w hw L hL
  exact (Hcell_sub_gfun q T L w).trans ((gfun_anti hc hn hL w).trans (gfun_trans hc hn hw))

theorem stable_H (hm : 0 < m) (c : ℕ) : Stable q T m (H q m c) := by
  intro w hw L hL z hz
  have : hidx q m z = hidx q m w := (code_eq_iff m hm _ _).2 (fun k hk => by
    show q.symm (z k) = q.symm (w k); rw [hz.1 k (by omega)])
  exact this.trans hw

theorem stable_gfun (hc : Compat2 q T) (hm : 0 < m) (y0 : ℕ → α) :
    Stable q T m (gfun q T m y0) := fun w hw L hL =>
  (Hcell_sub_gfun q T L w).trans ((gfun_anti hc hm hL w).trans (gfun_trans hc hm hw))

theorem stable_slabO (hc : Compat2 q T) (hm : 0 < m) (c : ℕ) :
    Stable q T m (slabO q T m y0 c) := by
  unfold slabO
  split_ifs
  · intro w hw; exact absurd hw id
  · have := (stable_H (q := q) (T := T) hm c).inter (stable_gfun hc hm y0)
    simpa [slab] using this

theorem mem_Hcell_symm {L : ℕ} (hL : 0 < L) {x w : ℕ → α} (h : w ∈ Hcell q T L x) :
    x ∈ Hcell q T L w := by
  rw [Hcell_eq_of_mem hL h]; exact mem_Hcell q T L x

/-- piece の安定性。 -/
theorem piece_stable (hc : Compat2 q T) (hm : 0 < m) {c k : ℕ} {S : Set (ℕ → α)}
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c)) {Pv : Set (ℕ → α) × ℕ}
    (hP : Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) k) : Stable q T (m + 3) Pv.1 := by
  obtain ⟨S2, hS2, -, S3, hS3, -, hPe⟩ := hP
  rw [hPe]
  have h1 := (stable_slabO (y0 := y0) hc hm c).inter (stable_lncA hc (by omega) hS)
  have h2 := h1.inter (stable_lncA hc (by omega) hS2)
  have h3 := h2.inter (stable_lncA hc (by omega) hS3)
  exact h3.mono (by omega)

/-- 点を含む piece は番号まで一意。 -/
theorem piece_unique (hc : Compat2 q T) {c c' k k' : ℕ} {S S' : Set (ℕ → α)}
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c))
    (hS' : S' ∈ lncA q T (m + 1) (slabO q T m y0 c')) {Pv Pv' : Set (ℕ → α) × ℕ}
    (hP : Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) k)
    (hP' : Pv' ∈ pieces q T m (slabO q T m y0 c' ∩ S') k') {x : ℕ → α}
    (hx : x ∈ Pv.1) (hx' : x ∈ Pv'.1) : Pv = Pv' := by
  obtain ⟨S2, hS2, -, S3, hS3, hv, hPe⟩ := hP
  obtain ⟨S2', hS2', -, S3', hS3', hv', hPe'⟩ := hP'
  rw [hPe] at hx; rw [hPe'] at hx'
  have hslab : ∀ {c'' : ℕ}, x ∈ slabO q T m y0 c'' → c'' = hidx q m x := by
    intro c'' h
    unfold slabO at h
    split_ifs at h
    · exact absurd h id
    · exact h.1.symm
  have hcc : c = c' := (hslab hx.1.1.1).trans (hslab hx'.1.1.1).symm
  subst hcc
  have hSS : S = S' := lncA_unique hc hS hS' hx.1.1.2 hx'.1.1.2
  subst hSS
  have h2 : S2 = S2' := lncA_unique hc hS2 hS2' hx.1.2 hx'.1.2
  subst h2
  have h3 : S3 = S3' := lncA_unique hc hS3 hS3' hx.2 hx'.2
  subst h3
  exact Prod.ext (hPe.trans hPe'.symm) (hv.trans hv'.symm)

/-- firstC は lncA の元か空。 -/
theorem firstC_cases (n : ℕ) (A : Set (ℕ → α)) :
    firstC q T n A = ∅ ∨ firstC q T n A ∈ lncA q T n A := by
  classical
  unfold firstC
  split_ifs with h
  · exact Or.inr (unlab_mem _ h 0)
  · exact Or.inl rfl

/-- G_d の箱の深さ。 -/
theorem Gd_level (hc : Compat2 q T) (a : ℕ → ℕ) (P : Set (ℕ → α)) (v : ℕ) {B : Set (ℕ → α)}
    (hB : B ∈ Gd q T m a P v) : Stable q T (max (m + 5) (a (m + v) + 1)) B := by
  unfold Gd at hB
  split_ifs at hB
  · obtain ⟨⟨S, -, rfl⟩, -⟩ := hB
    rcases firstC_cases (q := q) (T := T) (a (m + v) + 1) (S ∩ P) with h | h
    · rw [h]; intro w hw; exact absurd hw id
    · exact (stable_lncA hc (by omega) h).mono (le_max_right _ _)
  · obtain ⟨S, -, hB', -⟩ := hB
    exact (stable_lncA hc (by omega) hB').mono (le_max_left _ _)

variable (q T m y0)

/-- 穴の部分族の和（任意の (c, S) の述語 R で制限）。 -/
noncomputable def holeU (a : ℕ → ℕ) (k r : ℕ) (R : ℕ → Set (ℕ → α) → Prop) : Set (ℕ → α) :=
  ⋃ c, ⋃ S ∈ {S | R c S}, holeCells q T m a k r (slabO q T m y0 c ∩ S)

variable {q T m y0}

theorem mem_holeU {a : ℕ → ℕ} {k r : ℕ} {R : ℕ → Set (ℕ → α) → Prop} {x : ℕ → α} :
    x ∈ holeU q T m y0 a k r R ↔ ∃ c S, R c S ∧ ∃ Pv, (Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) k
      ∧ r ≤ Pv.2) ∧ ∃ B ∈ Gd q T m a Pv.1 Pv.2, x ∈ B ∩ Pv.1 := by
  simp only [holeU, holeCells, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

theorem holes_SOpen (hc : Compat2 q T) (hm : 0 < m) (a : ℕ → ℕ) (k r : ℕ)
    (R : ℕ → Set (ℕ → α) → Prop)
    (hR : ∀ c S, R c S → S ∈ lncA q T (m + 1) (slabO q T m y0 c)) :
    SOpen q T (holeU q T m y0 a k r R) := by
  intro x hx
  obtain ⟨c, S, hcs, Pv, ⟨hP, hr⟩, B, hB, hxB⟩ := mem_holeU.mp hx
  have hst := (Gd_level hc a Pv.1 Pv.2 hB).inter (piece_stable hc hm (hR c S hcs) hP)
  refine ⟨max (max (m + 5) (a (m + Pv.2) + 1)) (m + 3), by omega, fun w hw => ?_⟩
  exact mem_holeU.mpr ⟨c, S, hcs, Pv, ⟨hP, hr⟩, B, hB, hst x hxB _ le_rfl hw⟩

theorem holes_SClosed (hc : Compat2 q T) (hm : 0 < m) (a : ℕ → ℕ) (k r : ℕ)
    (R : ℕ → Set (ℕ → α) → Prop)
    (hR : ∀ c S, R c S → S ∈ lncA q T (m + 1) (slabO q T m y0 c)) :
    SClosed q T (holeU q T m y0 a k r R) := by
  intro x hx
  -- x を含む piece があればその番号で深さを決める
  by_cases hex : ∃ c S, R c S ∧ ∃ Pv, Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) k ∧ x ∈ Pv.1
  · obtain ⟨c0, S0, hcs0, Pv0, hP0, hx0⟩ := hex
    refine ⟨max (max (m + 5) (a (m + Pv0.2) + 1)) (m + 3), by omega, ?_⟩
    rw [Set.disjoint_left]
    intro w hw hwU
    obtain ⟨c, S, hcs, Pv, ⟨hP, hr⟩, B, hB, hwB⟩ := mem_holeU.mp hwU
    have hL0 : 0 < max (max (m + 5) (a (m + Pv0.2) + 1)) (m + 3) := by omega
    have hxw := mem_Hcell_symm hL0 hw
    have hxP : x ∈ Pv.1 := piece_stable hc hm (hR c S hcs) hP w hwB.2 _ (by omega) hxw
    have he := piece_unique hc (hR c S hcs) (hR c0 S0 hcs0) hP hP0 hxP hx0
    have hxB : x ∈ B := by
      have := Gd_level hc a Pv.1 Pv.2 hB w hwB.1 (max (max (m + 5) (a (m + Pv0.2) + 1)) (m + 3))
        (by rw [he]; omega)
      exact this hxw
    exact hx (mem_holeU.mpr ⟨c, S, hcs, Pv, ⟨hP, hr⟩, B, hB, hxB, hxP⟩)
  · push_neg at hex
    refine ⟨m + 3, by omega, ?_⟩
    rw [Set.disjoint_left]
    intro w hw hwU
    obtain ⟨c, S, hcs, Pv, ⟨hP, -⟩, B, -, hwB⟩ := mem_holeU.mp hwU
    have hxP : x ∈ Pv.1 :=
      piece_stable hc hm (hR c S hcs) hP w hwB.2 _ le_rfl (mem_Hcell_symm (by omega) hw)
    exact hex c S hcs Pv hP hxP

/-- slabRec で作った slab ごとの集合の和は holeU の形。 -/
theorem HkO_eq (a : ℕ → ℕ) (p : ℕ → ℕ) (k : ℕ) (prevD : ℕ → Set (ℕ → α)) :
    (⋃ c, HkO q T m y0 a p k prevD c) = holeU q T m y0 a (k + 2) (p (k + 2))
      (fun c S => S ∈ allowedO q T m y0 c
        (slabCum (fun c prior => ⋃ S ∈ allowedO q T m y0 c (prior ∪ prevD c),
          holeCells q T m a (k + 2) (p (k + 2)) (slabO q T m y0 c ∩ S)) c ∪ prevD c)) := by
  rfl

theorem EsetO_SOpen_SClosed (hc : Compat2 q T) (hm : 0 < m) (a : ℕ → ℕ) (p : ℕ → ℕ)
    (hp : ∀ k, 0 < p k) (k : ℕ) :
    SOpen q T (EsetO q T m y0 a p k) ∧ SClosed q T (EsetO q T m y0 a p k) := by
  induction k with
  | zero => exact ⟨gset_SOpen hc (hp 1) _, gset_SClosed hc (hp 1) _⟩
  | succ k ih =>
    rw [EsetO_succ, HkO_eq]
    have hR : ∀ c S, S ∈ allowedO q T m y0 c
        (slabCum (fun c prior => ⋃ S ∈ allowedO q T m y0 c (prior ∪ (EseqO q T m y0 a p k).2 c),
          holeCells q T m a (k + 2) (p (k + 2)) (slabO q T m y0 c ∩ S)) c ∪
            (EseqO q T m y0 a p k).2 c) →
        S ∈ lncA q T (m + 1) (slabO q T m y0 c) := fun c S h => h.1
    exact ⟨SOpen_union (gset_SOpen hc (hp _) _) (holes_SOpen hc hm a _ _ _ hR),
      SClosed_union (gset_SClosed hc (hp _) _) (holes_SClosed hc hm a _ _ _ hR)⟩

end Defs.D_0040
