import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0040

namespace Defs.D_0048

/-!
稠密性の部品 4: **branch 1 の D の箱（を第 p 層まで広げたもの）は他の branch の点に届かない**
（`not_mem_gset_D1slabO`）。

slab c の第 m+1 層の元 S、その branch 元 S2（番号 ≠ 1）の点 w について、p ≥ m+2 なら
w ∉ g[p, D1slabO c]。D の箱はすべて、ある元 S'' の branch 1 の元 S2'' の中の点を代表に持つ深い箱で、
g(p, d) ⊆ g(m+2, d) ⊆ S2''。w ∈ S2'' なら S'' = S、S2'' = S2 となり番号が矛盾する。
これにより、近い slab の元は穴の構成（HkO, branch 2）で「使ってよい元」になる。
穴の構成の「前の slab の集合」はセル（自分の slab の中）なので、他の slab からの侵入は影響しない。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0040

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

/-- G_d の箱は piece の点を代表とする第 m+5 層以上の箱か空。 -/
theorem Gd_rep (a : ℕ → ℕ) (P : Set (ℕ → α)) (v : ℕ) {B : Set (ℕ → α)}
    (hB : B ∈ Gd q T m a P v) :
    B = ∅ ∨ ∃ L u, m + 5 ≤ L ∧ u ∈ P ∧ B = gfun q T L u := by
  unfold Gd at hB
  split_ifs at hB with hlev
  · obtain ⟨⟨S, -, rfl⟩, -⟩ := hB
    rcases firstC_cases (q := q) (T := T) (a (m + v) + 1) (S ∩ P) with h | h
    · exact Or.inl h
    · obtain ⟨u, hu, he, -⟩ := h
      exact Or.inr ⟨_, u, hlev, hu.2, he⟩
  · obtain ⟨S, -, hB', -⟩ := hB
    obtain ⟨u, hu, he, -⟩ := hB'
    exact Or.inr ⟨m + 5, u, le_rfl, hu.2, he⟩

theorem not_mem_gset_D1slabO (hc : Compat2 q T) (hm : 0 < m) (a : ℕ → ℕ) {c p : ℕ}
    (hp : m + 2 ≤ p) {S S2 : Set (ℕ → α)} (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c))
    (hS2 : S2 ∈ lncA q T (m + 2) (slabO q T m y0 c ∩ S))
    (hlab : lab (lncA q T (m + 2) (slabO q T m y0 c ∩ S)) S2 ≠ 1)
    {w : ℕ → α} (hwS : w ∈ S) (hwS2 : w ∈ S2) :
    w ∉ gset q T p (D1slabO q T m y0 a c) := by
  intro hw
  obtain ⟨d, hd, hwd⟩ := Set.mem_iUnion₂.mp hw
  -- d は許された元 S'' の branch 1 の piece の G_d の箱の中
  unfold D1slabO slabRec at hd
  obtain ⟨S'', hS''a, hdU⟩ := Set.mem_iUnion₂.mp hd
  simp only [holeBoxesU, Set.mem_iUnion, Set.mem_sUnion, exists_prop] at hdU
  obtain ⟨Pv, ⟨hPv, -⟩, B, hB, hdB⟩ := hdU
  obtain ⟨S2'', hS2'', hlab'', S3, hS3, -, hPe⟩ := hPv
  have hS'' : S'' ∈ lncA q T (m + 1) (slabO q T m y0 c) := hS''a.1
  -- B ⊆ S2''
  have hBS2 : B ⊆ S2'' := by
    rcases Gd_rep a Pv.1 Pv.2 hB with h | ⟨L, u, hL, hu, rfl⟩
    · rw [h]; exact Set.empty_subset _
    · rw [hPe] at hu
      exact stable_lncA hc (by omega) hS2'' u hu.1.2 L (by omega) |>.trans' (by
        intro y hy; exact hy) |> fun _ =>
        (gfun_anti hc (by omega) (show m + 2 ≤ L by omega) u).trans (by
          obtain ⟨x2, -, rfl, -⟩ := hS2''
          exact gfun_trans hc (by omega) hu.1.2)
  have hdS2 : d ∈ S2'' := hBS2 hdB
  -- g(p, d) ⊆ S2''
  have hgS2 : gfun q T p d ⊆ S2'' := by
    obtain ⟨x2, -, rfl, -⟩ := id hS2''
    exact (gfun_anti hc (by omega) hp d).trans (gfun_trans hc (by omega) hdS2)
  have hwS2'' : w ∈ S2'' := hgS2 hwd
  -- S2'' ⊆ S''
  have hS2S'' : S2'' ⊆ S'' := by
    obtain ⟨x2, hx2, rfl, -⟩ := id hS2''
    obtain ⟨x1, -, rfl, -⟩ := id hS''
    exact (gfun_anti hc (by omega) (show m + 1 ≤ m + 2 by omega) x2).trans
      (gfun_trans hc (by omega) hx2.2)
  have hSS : S'' = S := lncA_unique hc hS'' hS (hS2S'' hwS2'') hwS
  subst hSS
  have h22 : S2'' = S2 := lncA_unique hc hS2'' hS2 hwS2'' hwS2
  subst h22
  exact hlab hlab''

end Defs.D_0048
