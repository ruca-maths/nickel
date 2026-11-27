import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0046
import Defs.D_0050
import Defs.D_0051

namespace Defs.D_0056

/-!
稠密性の部品のまとめ 1: **D(1σ^α_1, G₁) は G_m で ρ-稠密**（Chen–Wang Prop 6.13 の Cl_ρ D ⊇ G_m の向き）。

`D1O_meets` : z ∈ G_m、ℓ ≥ m+1 なら D1O a ∩ g(ℓ, z) ≠ ∅（{g(ℓ, z)} は ρ の近傍基、Prop 3.4）。
証明: 近い点 s′（`Defs.D_0045.close_point_exists`）の箱 S′ = g(m+1, s′) は別の slab c′ の
第 m+1 層の元（`Defs.D_0046.close_member`）で S′ ⊆ g(ℓ, z)。
* S′ が D の構成で「使ってよい元」なら、branch 1・piece 5 の G_d の箱 B（`Defs.D_0050.Gd_nonempty`）
  が B ∩ piece ≠ ∅ で、その点は D1slabO c′ ⊆ D1O の点。
* 使ってよくないなら S′ ∩ slab ⊆ 前の slab の D の和 ⊆ D1O で、s′ 自身が D1O の点。
Ln cover の無限性は `Good`（箱の中にあり、その制約範囲の先で自由）の不変量で一括して示す。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0045 Defs.D_0046
  Defs.D_0047 Defs.D_0050 Defs.D_0051

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

/-- K 以降のすべての座標で自由。 -/
def FreeFrom (A : Set (ℕ → α)) (K : ℕ) : Prop := ∀ k, K ≤ k → FreeAt A k

variable (q T) in
/-- 箱 g(L, s) の中にあり、その制約範囲の先で自由。 -/
def Good (A : Set (ℕ → α)) (L : ℕ) (s : ℕ → α) : Prop :=
  A ⊆ gfun q T L s ∧ FreeFrom A (L + hidx q L s + 1)

theorem good_infinite [NoMaxOrder α] (hc : Compat2 q T) {A : Set (ℕ → α)} {L n : ℕ}
    {s : ℕ → α} (hL : 0 < L) (hLn : L < n) (hA : A.Nonempty) (hg : Good q T A L s) :
    (lncA q T n A).Infinite :=
  lncA_infinite_box hc hL hLn.le hA hg.1 (hg.2 _ (by omega))

theorem good_step (hc : Compat2 q T) {A : Set (ℕ → α)} {L L' : ℕ} {s x : ℕ → α}
    (hL : 0 < L) (hLL : L ≤ L') (hg : Good q T A L s) (hx : x ∈ A) :
    Good q T (A ∩ gfun q T L' x) L' x := by
  refine ⟨Set.inter_subset_right, fun k hk => FreeAt.inter (hg.2 k ?_) (gfun_free x (by omega))⟩
  have h1 := hidx_le_of_mem_gfun hc hL (hg.1 hx)
  have h2 : hidx q L x ≤ hidx q L' x := code_mono L hL _ L' hLL
  omega

theorem good_step' (hc : Compat2 q T) {A : Set (ℕ → α)} {L L' : ℕ} {s x : ℕ → α}
    (hL : 0 < L) (hLL : L ≤ L') (hg : Good q T A L s) (hx : x ∈ A) :
    Good q T (gfun q T L' x ∩ A) L' x := by
  rw [Set.inter_comm]; exact good_step hc hL hLL hg hx

theorem D1slabO_eq (m : ℕ) (y0 : ℕ → α) (a : ℕ → ℕ) (c : ℕ) :
    D1slabO q T m y0 a c = ⋃ S ∈ allowedO q T m y0 c (⋃ i ∈ Finset.range c, D1slabO q T m y0 a i),
      holeBoxesU q T m a 1 0 (slabO q T m y0 c ∩ S) := by
  conv_lhs => rw [D1slabO, slabRec, slabCum_eq]
  rfl

/-- D(1σ^α_1, G₁) は G_m の各点の箱近傍と交わる。 -/
theorem D1O_meets [Countable α] [DenselyOrdered α] [NoMaxOrder α] (hc : Compat2 q T) {m : ℕ}
    (hm : 0 < m) {y0 : ℕ → α} {a : ℕ → ℕ} (ha : StrictMono a) {z : ℕ → α}
    (hz : z ∈ gfun q T m y0) {ℓ : ℕ} (hℓ : m + 1 ≤ ℓ) :
    (D1O q T m y0 a ∩ gfun q T ℓ z).Nonempty := by
  obtain ⟨s', h0, hlt, -, hB, hsub⟩ := close_point_exists hc hm hℓ z (q.symm (z m) + 1)
  have hs'S : s' ∈ gfun q T (m + 1) s' := mem_gfun q T _ s'
  have hs'z : s' ∈ gfun q T ℓ z := hsub hs'S
  have hs'G : s' ∈ gfun q T m y0 := gfun_trans hc hm hz (gfun_anti hc hm (by omega) z hs'z)
  have hy0z : y0 0 ≤ z 0 := by
    rw [gfun_eq] at hz
    have := hz 0 (by omega)
    rw [ite_eq_left hm] at this
    exact this.1
  have hne : hidx q m s' ≠ hidx q m y0 := by
    intro h
    have h1 := (code_eq_iff m hm _ _).1 h 0 hm
    have h2 : s' 0 = y0 0 := q.symm.injective h1
    rw [h2] at hlt
    exact absurd hlt (not_lt.mpr hy0z)
  have hBm : q.symm (s' m) < q.symm (s' 0) := by
    rw [h0 m (by omega)]; omega
  have hmem := close_member hc hm hs'G hne hBm
  set c' := hidx q m s' with hc'
  set S' := gfun q T (m + 1) s' with hS'
  have hs'slab : s' ∈ slabO q T m y0 c' := by
    unfold slabO; rw [ite_eq_right hne]; exact ⟨rfl, hs'G⟩
  have hD1 : D1slabO q T m y0 a c' ⊆ D1O q T m y0 a := Set.subset_iUnion (D1slabO q T m y0 a) c'
  by_cases hall : S' ∈ allowedO q T m y0 c' (⋃ i ∈ Finset.range c', D1slabO q T m y0 a i)
  · -- 使ってよい元: branch 1, piece 5 の穴の箱
    set A1 := slabO q T m y0 c' ∩ S' with hA1
    have hgA1 : Good q T A1 (m + 1) s' := by
      have hslab : slabO q T m y0 c' = H q m c' ∩ gfun q T m y0 := by
        unfold slabO; rw [ite_eq_right hne]; rfl
      have hg0 : Good q T (H q m c' ∩ gfun q T m y0) m y0 :=
        ⟨Set.inter_subset_right, fun k hk =>
          FreeAt.inter (H_free hm (by omega) c') (gfun_free y0 (by omega))⟩
      have := good_step hc hm (by omega : m ≤ m + 1) hg0 (hslab ▸ hs'slab)
      rw [hA1, hslab]; exact this
    have hA1ne : s' ∈ A1 := ⟨hs'slab, hs'S⟩
    have h2inf := good_infinite hc (by omega) (by omega : m + 1 < m + 2) ⟨s', hA1ne⟩ hgA1
    have hF2 : (lncA q T (m + 2) A1).Countable ∧ (lncA q T (m + 2) A1).Infinite :=
      ⟨lncA_countable (by omega) A1, h2inf⟩
    set S2 := unlab (lncA q T (m + 2) A1) hF2 1 with hS2
    have hS2mem : S2 ∈ lncA q T (m + 2) A1 := unlab_mem _ hF2 1
    have hS2lab : lab (lncA q T (m + 2) A1) S2 = 1 := lab_unlab _ hF2 1
    obtain ⟨x2, hx2, hS2eq, -⟩ := hS2mem
    have hgA12 : Good q T (A1 ∩ S2) (m + 2) x2 := by
      rw [hS2eq]; exact good_step hc (by omega) (by omega) hgA1 hx2
    have hx2' : x2 ∈ A1 ∩ S2 := ⟨hx2, hS2eq ▸ mem_gfun q T _ x2⟩
    have h3inf := good_infinite hc (by omega) (by omega : m + 2 < m + 3) ⟨x2, hx2'⟩ hgA12
    have hF3 : (lncA q T (m + 3) (A1 ∩ S2)).Countable ∧ (lncA q T (m + 3) (A1 ∩ S2)).Infinite :=
      ⟨lncA_countable (by omega) _, h3inf⟩
    set S3 := unlab (lncA q T (m + 3) (A1 ∩ S2)) hF3 5 with hS3
    have hS3mem : S3 ∈ lncA q T (m + 3) (A1 ∩ S2) := unlab_mem _ hF3 5
    have hS3lab : lab (lncA q T (m + 3) (A1 ∩ S2)) S3 = 5 := lab_unlab _ hF3 5
    have hpiece : (A1 ∩ S2 ∩ S3, 5) ∈ pieces q T m A1 1 :=
      ⟨S2, unlab_mem _ hF2 1, hS2lab, S3, hS3mem, hS3lab.symm, rfl⟩
    obtain ⟨x3, hx3, hS3eq, -⟩ := hS3mem
    set P := A1 ∩ S2 ∩ S3 with hP
    have hgP : Good q T P (m + 3) x3 := by
      rw [hP, hS3eq]; exact good_step hc (by omega) (by omega) hgA12 hx3
    have hx3P : x3 ∈ P := ⟨hx3, hS3eq ▸ mem_gfun q T _ x3⟩
    have hav : m + 5 ≤ a (m + 5) := ha.id_le (m + 5)
    have h4 := good_infinite hc (by omega) (by omega : m + 3 < m + 4) ⟨x3, hx3P⟩ hgP
    have h5 : ∀ S4 ∈ lncA q T (m + 4) P, (lncA q T (m + 5) (S4 ∩ P)).Infinite := by
      rintro S4 ⟨x4, hx4, rfl, -⟩
      exact good_infinite hc (by omega) (by omega)
        ⟨x4, mem_gfun q T _ x4, hx4⟩ (good_step' hc (by omega) (by omega) hgP hx4)
    have h1 : ∀ S0 ∈ lncA q T (a (m + 5)) P,
        (lncA q T (a (m + 5) + 1) (S0 ∩ P)).Infinite := by
      rintro S0 ⟨x0, hx0, rfl, -⟩
      exact good_infinite hc (by omega) (by omega)
        ⟨x0, mem_gfun q T _ x0, hx0⟩ (good_step' hc (by omega) (by omega) hgP hx0)
    obtain ⟨B, hB, w, hwB, hwP⟩ :=
      Gd_nonempty hc a P 5 (by omega) hav h4 h5 h1
    have hwU : w ∈ holeBoxesU q T m a 1 0 A1 := by
      unfold holeBoxesU
      exact Set.mem_biUnion (x := (P, 5)) ⟨hpiece, Nat.zero_le _⟩ ⟨B, hB, hwB⟩
    have hwD : w ∈ D1slabO q T m y0 a c' := by
      rw [D1slabO_eq]; exact Set.mem_biUnion hall hwU
    exact ⟨w, hD1 hwD, hsub hwP.1.1.2⟩
  · -- 使ってよくない元: s′ は前の slab の D の点
    have hs'p : s' ∈ ⋃ i ∈ Finset.range c', D1slabO q T m y0 a i := by
      by_contra hn
      exact hall ⟨hmem, s', hs'S, hs'slab, hn⟩
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.mp hs'p
    exact ⟨s', Set.subset_iUnion (D1slabO q T m y0 a) i hi, hs'z⟩

end Defs.D_0056
