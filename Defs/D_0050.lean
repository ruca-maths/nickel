import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0040

namespace Defs.D_0050

/-!
稠密性の部品 6: **piece の中に ch-set と交わる α の穴の箱がある**（`Gd_nonempty`）。

* `lncA_absorb` : S ∈ lncA n A、s ∈ A、g(n, s) が S と交われば g(n, s) ⊆ S（極大性）。
* ch-set の箱として番号 (j, l) = (α(v), α(v)+1) の箱 S5 を取る（j ≤ α v < l なので α ch-set の元）。
  S5 の点を含む第 α(m+v) 層の元 S0 は、極大性から S5 に含まれ、S0 ∩ P の第 α(m+v)+1 層の
  被覆の番号 0 の元 B（firstC）は空でなく B ⊆ S5、よって B ∈ G_d。各被覆が無限であることは仮定
  （`Defs.D_0047.lncA_infinite` で示せる）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0039 Defs.D_0040

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ}

theorem lncA_absorb (hc : Compat2 q T) {n : ℕ} {A S : Set (ℕ → α)} (hS : S ∈ lncA q T n A)
    {s : ℕ → α} (hs : s ∈ A) (hne : (gfun q T n s ∩ S).Nonempty) : gfun q T n s ⊆ S := by
  obtain ⟨x, -, rfl, hmax⟩ := hS
  rcases le_total (hidx q n x) (hidx q n s) with h | h
  · exact gfun_nested hc h (Set.inter_comm _ _ ▸ hne)
  · have hsub := gfun_nested hc h hne
    rw [hmax s hs hsub]

theorem Gd_nonempty [Countable α] (hc : Compat2 q T) (a : ℕ → ℕ) (P : Set (ℕ → α)) (v : ℕ)
    (hlev : m + 5 ≤ a (m + v) + 1) (hL0 : m + 5 ≤ a (m + v))
    (h4 : (lncA q T (m + 4) P).Infinite)
    (h5 : ∀ S4 ∈ lncA q T (m + 4) P, (lncA q T (m + 5) (S4 ∩ P)).Infinite)
    (h1 : ∀ S0 ∈ lncA q T (a (m + v)) P, (lncA q T (a (m + v) + 1) (S0 ∩ P)).Infinite) :
    ∃ B ∈ Gd q T m a P v, (B ∩ P).Nonempty := by
  have hF4 : (lncA q T (m + 4) P).Countable ∧ (lncA q T (m + 4) P).Infinite :=
    ⟨lncA_countable (by omega) _, h4⟩
  set S4 := unlab _ hF4 (a v)
  have hS4 : S4 ∈ lncA q T (m + 4) P := unlab_mem _ hF4 _
  have hF5 : (lncA q T (m + 5) (S4 ∩ P)).Countable ∧ (lncA q T (m + 5) (S4 ∩ P)).Infinite :=
    ⟨lncA_countable (by omega) _, h5 S4 hS4⟩
  set S5 := unlab _ hF5 (a v + 1)
  have hS5 : S5 ∈ lncA q T (m + 5) (S4 ∩ P) := unlab_mem _ hF5 _
  have hch : S5 ∈ chBoxes q T m a P v :=
    ⟨S4, hS4, hS5, Or.inl ⟨by rw [lab_unlab], by rw [lab_unlab]; omega⟩⟩
  obtain ⟨x, hx, hxe, -⟩ := id hS5
  have hxS5 : x ∈ S5 := by rw [hxe]; exact mem_gfun q T _ x
  -- x を含む第 L0 層の元 S0
  have hxg : x ∈ gset q T (a (m + v)) P := sub_gset _ _ hx.2
  obtain ⟨hS0, hxS0⟩ := lncA_mem_spec hc hxg
  set S0 := lncA_mem q T (a (m + v)) P x
  obtain ⟨s0, hs0P, hs0e, -⟩ := id hS0
  have hxs0 : x ∈ gfun q T (a (m + v)) s0 := hs0e ▸ hxS0
  -- s0 ∈ S4（極大性）
  have hs0S4 : gfun q T (m + 4) s0 ⊆ S4 :=
    lncA_absorb hc hS4 hs0P ⟨x, gfun_anti hc (by omega) (by omega) s0 hxs0, hx.1⟩
  have hs0S4' : s0 ∈ S4 := hs0S4 (mem_gfun q T _ s0)
  have hs0S5 : gfun q T (m + 5) s0 ⊆ S5 :=
    lncA_absorb hc hS5 ⟨hs0S4', hs0P⟩ ⟨x, gfun_anti hc (by omega) (by omega) s0 hxs0, hxS5⟩
  have hS0S5 : S0 ⊆ S5 := by
    rw [hs0e]; exact (gfun_anti hc (by omega) (by omega) s0).trans hs0S5
  -- B = firstC
  set B := firstC q T (a (m + v) + 1) (S0 ∩ P)
  have hB : B ∈ lncA q T (a (m + v) + 1) (S0 ∩ P) := firstC_mem (by omega) (h1 S0 hS0)
  obtain ⟨u, hu, hue, -⟩ := id hB
  have huB : u ∈ B := by rw [hue]; exact mem_gfun q T _ u
  have hBS0 : B ⊆ S0 := by
    rw [hue]
    exact (gfun_anti hc (by omega) (show a (m + v) ≤ a (m + v) + 1 by omega) u).trans
      (hs0e ▸ gfun_trans hc (by omega) (hs0e ▸ hu.1))
  refine ⟨B, ?_, u, huB, hu.2⟩
  unfold Gd
  rw [if_pos hlev]
  exact ⟨⟨S0, hS0, rfl⟩, u, huB, S5, hch, hS0S5 (hBS0 huB)⟩

end Defs.D_0050
