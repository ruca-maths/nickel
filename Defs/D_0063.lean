import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0061

namespace Defs.D_0063

/-!
**相棒の補題**（宣言された閉包の反例の穴 §11.4 の一部を塞ぐ）。

* `companion_not_mem_gset` : M ∈ lncA n D（M = g(n, d)）、d ∈ g(ph, u)、lvl ph u ≤ lvl n d、n ≤ ph、u ∉ M
  なら u ∉ g[n, D]。u を含む D の n-箱は ZZ+ で M を含み、M の極大性から M と一致してしまうため。
  よって相棒が E に入らないことは、M の外にあることと、E の残りの部分（穴のセル）の外にあることに帰着し、
  中間の slab からの D の箱の侵入を個別に調べる必要はない。
* `not_mem_closure_of_maxKill` : 判定法の極大箱版。D の極大な p₁-箱 M ごとに M ∩ g(ℓ, z) ⊆ K なら、
  z ∉ Cl_τ g[p₂, E(α, p, 0)]。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0034 Defs.D_0035 Defs.D_0039 Defs.D_0043 Defs.D_0060 Defs.D_0061

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

theorem companion_not_mem_gset (hc : Compat2 q T) {n ph : ℕ} (hn : 0 < n) (hnph : n ≤ ph)
    {D M : Set (ℕ → α)} (hM : M ∈ lncA q T n D) {d u : ℕ → α} (hMd : M = gfun q T n d)
    (hdu : d ∈ gfun q T ph u) (hlv : lvl q ph u ≤ lvl q n d) (huM : u ∉ M) :
    u ∉ gset q T n D := by
  intro hu
  obtain ⟨d', hd'D, hud'⟩ := Set.mem_iUnion₂.mp hu
  have h1 : M ⊆ gfun q T ph u := hMd ▸ gfun_sub_coarse hc hdu hlv
  have h2 : gfun q T ph u ⊆ gfun q T n u := gfun_anti hc hn hnph u
  have h3 : gfun q T n u ⊆ gfun q T n d' := gfun_trans hc hn hud'
  obtain ⟨x, -, hxM, hmax⟩ := hM
  have heq : gfun q T n d' = M := hmax d' hd'D (h1.trans (h2.trans h3))
  exact huM (heq ▸ h3 (mem_gfun q T n u))

/-- 判定法の極大箱版。 -/
theorem not_mem_closure_of_maxKill (hc : Compat2 q T) {A : Set (ℕ → ℕ)} {a : ℕ → ℕ}
    {p : ℕ → ℕ} (hp : AdmT m p) {z : ℕ → α} {U : Set (ℕ → α)}
    (hU : @IsOpen _ (tauT q T m y0 A) U) (hzU : z ∈ U) {ℓ : ℕ} (hUℓ : U ⊆ gfun q T ℓ z)
    {K : Set (ℕ → α)} (hUK : Disjoint U K)
    (hkill : ∀ M ∈ lncA q T (p 1) (D1O q T m y0 a), M ∩ gfun q T ℓ z ⊆ K) :
    z ∉ @closure _ (tauT q T m y0 A) (gset q T (p 2) (EsetO q T m y0 a p 0)) := by
  let _ := tauT q T m y0 A
  have hp1 : 0 < p 1 := lt_of_le_of_lt (Nat.zero_le _) (by have := hp.2.1; omega)
  have hp12 : p 2 = p 1 := hp.2.2.2.symm
  refine not_mem_closure_of_disjoint _ hU hzU ?_
  rw [Set.disjoint_left]
  intro w hwU hwS
  have hwS' : w ∈ gset q T (p 1) (D1O q T m y0 a) := by
    rw [hp12, EsetO_zero] at hwS
    exact gset_gsetT hc hp1 le_rfl _ hwS
  rw [← lncA_sUnion hc] at hwS'
  obtain ⟨M, hM, hwM⟩ := hwS'
  exact Set.disjoint_left.mp hUK hwU (hkill M hM ⟨hwM, hUℓ hwU⟩)

end Defs.D_0063
