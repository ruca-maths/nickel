import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0038

namespace Defs.D_0039

/-!
セル位相（H(n, x) を基とする超距離位相）での開・閉性と、Chen–Wang の E(αk, p) の修正版。

* `SOpen q T A` : ∀ x ∈ A, ∃ L, H(L, x) ⊆ A。`SClosed q T A` : ∀ x ∉ A, ∃ L, H(L, x) ∩ A = ∅。
  Theorem 1.a の g-関数 g(n+1, ·) が τ の g-関数であるためには、τ の開集合はすべて SOpen である
  必要がある（z ∈ H(n, x) ⇒ x ∈ g(n, z)）。論文の宣言する開閉集合がこれを満たすかを確かめる。
* `gfun_SOpen`, `gfun_SClosed`, `gset_SOpen`, `gset_SClosed`, `SOpen_iUnion`, `SClosed_union`。
* `slabO c` : 論文の slab H'(m, 1_j) は H(n, i) ∩ H₀ = ∅ のものだけ（c ≠ hidx m y₀）。
  Defs.D_0038 の `slab` は c = hidx m y₀（= H₀ 自身）も含んでいたので、ここで除いた版
  `D1slabO`, `D1O`, `EseqO`, `EsetO` を定義し直す（以後はこちらを使う）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0032 Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038

variable {α : Type} [LinearOrder α] (q : ℕ ≃ α) (T : Tree2 α)

def SOpen (A : Set (ℕ → α)) : Prop := ∀ x ∈ A, ∃ L, 0 < L ∧ Hcell q T L x ⊆ A

def SClosed (A : Set (ℕ → α)) : Prop := ∀ x ∉ A, ∃ L, 0 < L ∧ Disjoint (Hcell q T L x) A

variable {q T}

theorem SOpen_iUnion {ι : Type} {A : ι → Set (ℕ → α)} (h : ∀ i, SOpen q T (A i)) :
    SOpen q T (⋃ i, A i) := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨L, hL0, hL⟩ := h i x hi
  exact ⟨L, hL0, hL.trans (Set.subset_iUnion A i)⟩

theorem SOpen_union {A B : Set (ℕ → α)} (hA : SOpen q T A) (hB : SOpen q T B) :
    SOpen q T (A ∪ B) := by
  rintro x (hx | hx)
  · obtain ⟨L, h0, hL⟩ := hA x hx; exact ⟨L, h0, hL.trans Set.subset_union_left⟩
  · obtain ⟨L, h0, hL⟩ := hB x hx; exact ⟨L, h0, hL.trans Set.subset_union_right⟩

theorem SClosed_union {A B : Set (ℕ → α)} (hA : SClosed q T A) (hB : SClosed q T B) :
    SClosed q T (A ∪ B) := by
  intro x hx
  obtain ⟨L1, h10, h1⟩ := hA x (fun h => hx (Or.inl h))
  obtain ⟨L2, h20, h2⟩ := hB x (fun h => hx (Or.inr h))
  refine ⟨L1 + L2, by omega, Set.disjoint_union_right.mpr ⟨?_, ?_⟩⟩
  · exact h1.mono_left (Hcell_anti h10 (by omega) x)
  · exact h2.mono_left (Hcell_anti h20 (by omega) x)

theorem SClosed_mono_level {A : Set (ℕ → α)} {x : ℕ → α} {L L' : ℕ} (h0 : 0 < L)
    (hLL : L ≤ L') (h : Disjoint (Hcell q T L x) A) : Disjoint (Hcell q T L' x) A :=
  h.mono_left (Hcell_anti h0 hLL x)

theorem gfun_SOpen (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) (z : ℕ → α) :
    SOpen q T (gfun q T n z) :=
  fun x hx => ⟨n, hn, (Hcell_sub_gfun q T n x).trans (gfun_trans hc hn hx)⟩

/-- x ∉ g(n, z) なら H(n, x) ∩ g(n, z) = ∅。 -/
theorem Hcell_disj_gfun (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) {x z : ℕ → α}
    (hx : x ∉ gfun q T n z) : Disjoint (Hcell q T n x) (gfun q T n z) := by
  rw [Set.disjoint_left]
  intro w hw hwz
  apply hx
  have h := gfun_trans hc hn hwz
  rw [gfun_eq_of_mem_Hcell q T hn hw] at h
  exact h (mem_gfun q T n x)

theorem gfun_SClosed (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) (z : ℕ → α) :
    SClosed q T (gfun q T n z) := fun x hx => ⟨n, hn, Hcell_disj_gfun hc hn hx⟩

theorem gset_SOpen (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) (A : Set (ℕ → α)) :
    SOpen q T (gset q T n A) := by
  intro x hx
  obtain ⟨z, hzA, hxz⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨L, h0, hL⟩ := gfun_SOpen hc hn z x hxz
  exact ⟨L, h0, hL.trans (Set.subset_biUnion_of_mem (u := fun z => gfun q T n z) hzA)⟩

theorem gset_SClosed (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) (A : Set (ℕ → α)) :
    SClosed q T (gset q T n A) := by
  intro x hx
  refine ⟨n, hn, ?_⟩
  rw [Set.disjoint_left]
  intro w hw hwA
  obtain ⟨z, hzA, hwz⟩ := Set.mem_iUnion₂.mp hwA
  apply hx
  refine Set.mem_biUnion hzA ?_
  by_contra hxz
  exact Set.disjoint_left.mp (Hcell_disj_gfun hc hn hxz) hw hwz

/-! ### 修正版の D と E（H₀ の slab を除く） -/

variable (q T) (m : ℕ) (y0 : ℕ → α)

open Classical in
/-- 論文の slab H'(m, 1_j)（H₀ と交わらないもの）。 -/
noncomputable def slabO (c : ℕ) : Set (ℕ → α) :=
  if c = hidx q m y0 then ∅ else slab q T m y0 c

noncomputable def allowedO (c : ℕ) (prior : Set (ℕ → α)) : Set (Set (ℕ → α)) :=
  {S | S ∈ lncA q T (m + 1) (slabO q T m y0 c) ∧ (S ∩ (slabO q T m y0 c \ prior)).Nonempty}

noncomputable def D1slabO (a : ℕ → ℕ) : ℕ → Set (ℕ → α) :=
  slabRec (fun c prior => ⋃ S ∈ allowedO q T m y0 c prior,
    holeBoxesU q T m a 1 0 (slabO q T m y0 c ∩ S))

/-- 論文の D(1σ^α_1, G₁)。 -/
noncomputable def D1O (a : ℕ → ℕ) : Set (ℕ → α) := ⋃ c, D1slabO q T m y0 a c

/-- slab c の branch k+2 の穴の部分（Q2）。 -/
noncomputable def HkO (a : ℕ → ℕ) (p : ℕ → ℕ) (k : ℕ) (prevD : ℕ → Set (ℕ → α)) :
    ℕ → Set (ℕ → α) :=
  slabRec (fun c prior => ⋃ S ∈ allowedO q T m y0 c (prior ∪ prevD c),
    holeCells q T m a (k + 2) (p (k + 2)) (slabO q T m y0 c ∩ S))

noncomputable def EseqO (a : ℕ → ℕ) (p : ℕ → ℕ) : ℕ → Set (ℕ → α) × (ℕ → Set (ℕ → α))
  | 0 => (gset q T (p 1) (D1O q T m y0 a), fun c => gset q T (p 1) (D1slabO q T m y0 a c))
  | k + 1 =>
    let prev := EseqO a p k
    let Hk := HkO q T m y0 a p k prev.2
    (gset q T (p (k + 2)) prev.1 ∪ ⋃ c, Hk c, fun c => prev.2 c ∪ gset q T (p (k + 2)) (Hk c))

/-- 論文の E(α(k+1), p)（k ≥ 1 が E(α2) 以降。k = 0 は D(p₁, m^α) = g[p₁, D]）。 -/
noncomputable def EsetO (a : ℕ → ℕ) (p : ℕ → ℕ) (k : ℕ) : Set (ℕ → α) := (EseqO q T m y0 a p k).1

theorem EsetO_zero (a : ℕ → ℕ) (p : ℕ → ℕ) :
    EsetO q T m y0 a p 0 = gset q T (p 1) (D1O q T m y0 a) := rfl

theorem EsetO_succ (a : ℕ → ℕ) (p : ℕ → ℕ) (k : ℕ) :
    EsetO q T m y0 a p (k + 1) = gset q T (p (k + 2)) (EsetO q T m y0 a p k) ∪
      ⋃ c, HkO q T m y0 a p k (EseqO q T m y0 a p k).2 c := rfl

end Defs.D_0039
