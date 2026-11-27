import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0057
import Defs.D_0058
import Defs.D_0060
import Defs.D_0048

namespace Defs.D_0061

/-!
**宣言された閉包が破れるための判定法**（Chen–Wang Definition B.1 / Denotation 1、k = 0）。

z が穴の点で、τ-開集合
  U = g(ℓ, z) − E(α, p′, 1) − g[ph, g(ℓ′, x) − E(α, p, 1)] − ⋃_{(γ, p_γ) ∈ Γ} E(γ, p_γ, 1)
が z を含むとする。D(1σ^α_1, G₁) の各 G_d の箱 g(L, b) について、g(min(p₁, L), b) ∩ g(ℓ, z) が
切り離し集合 E(α, p′, 1) ∪ (Definition C の集合) ∪ ⋃ E(γ, p_γ, 1) に含まれれば、
z ∉ Cl_τ g[p₂, E(α, p, 0)]（`not_mem_closure_of_boxKill`）。

箱ごとの十分条件（すべて ZZ+ `Defs.D_0060.gfun_sub_coarse` から）:
* `kill_shell` : L ≤ p′₁ なら g(L, b) ⊆ E(α, p′, 1)（D の箱は E に含まれる）。
* `kill_gamma` : b ∈ g(P, c)、lvl P c ≤ lvl n b、c ∈ D(γ)、P = p_γ₁ なら g(n, b) ⊆ E(γ, p_γ, 1)。
* `kill_defC` : b ∈ g(ph, u)、lvl ph u ≤ lvl n b、u ∈ g(ℓ′, x) − E′ なら g(n, b) ⊆ g[ph, g(ℓ′, x) − E′]。
検証報告 §11 で、列挙（Δ-order）と mad family を選ぶとこれらの条件がすべての箱で成り立つ構成を述べる。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0029
  Defs.D_0031 Defs.D_0034 Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0043
  Defs.D_0040 Defs.D_0048 Defs.D_0056 Defs.D_0057 Defs.D_0060

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

/-- D の点は、D に含まれる G_d の箱 g(L, b)（L ≥ m+5）に入る。 -/
theorem mem_D1O_box {a : ℕ → ℕ} {d : ℕ → α} (hd : d ∈ D1O q T m y0 a) :
    ∃ L b, m + 5 ≤ L ∧ d ∈ gfun q T L b ∧ gfun q T L b ⊆ D1O q T m y0 a := by
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hd
  rw [D1slabO_eq] at hc
  obtain ⟨S, hS, hdS⟩ := Set.mem_iUnion₂.mp hc
  unfold holeBoxesU at hdS
  obtain ⟨Pv, hPv, B, hB, hdB⟩ := by
    simpa only [Set.mem_iUnion, Set.mem_sUnion, exists_prop] using hdS
  rcases Gd_rep a Pv.1 Pv.2 hB with he | ⟨L, b, hL, -, rfl⟩
  · rw [he] at hdB; exact absurd hdB (Set.notMem_empty d)
  · refine ⟨L, b, hL, hdB, fun w hw => ?_⟩
    refine Set.mem_iUnion.mpr ⟨c, ?_⟩
    rw [D1slabO_eq]
    refine Set.mem_iUnion₂.mpr ⟨S, hS, ?_⟩
    unfold holeBoxesU
    simp only [Set.mem_iUnion, Set.mem_sUnion, exists_prop]
    exact ⟨Pv, hPv, _, hB, hw⟩

theorem kill_shell {a : ℕ → ℕ} {p' : ℕ → ℕ} {L : ℕ} {b : ℕ → α}
    (hbox : gfun q T L b ⊆ D1O q T m y0 a) :
    gfun q T L b ⊆ EsetO q T m y0 a p' 1 :=
  hbox.trans (D1O_sub_EsetO m y0 a p' 1)

theorem kill_gamma (hc : Compat2 q T) {g pg : ℕ → ℕ} {n : ℕ} {b c : ℕ → α}
    (hbc : b ∈ gfun q T (pg 1) c) (hlv : lvl q (pg 1) c ≤ lvl q n b)
    (hcD : c ∈ D1O q T m y0 g) : gfun q T n b ⊆ EsetO q T m y0 g pg 1 := by
  refine (gfun_sub_coarse hc hbc hlv).trans ?_
  rw [EsetO_succ]
  refine Set.subset_union_of_subset_left (fun w hw => ?_) _
  have h1 : w ∈ EsetO q T m y0 g pg 0 := by rw [EsetO_zero]; exact Set.mem_biUnion hcD hw
  exact sub_gset _ _ h1

theorem kill_defC (hc : Compat2 q T) {ph n ℓ' : ℕ} {b u x : ℕ → α} {E' : Set (ℕ → α)}
    (hbu : b ∈ gfun q T ph u) (hlv : lvl q ph u ≤ lvl q n b)
    (hu : u ∈ gfun q T ℓ' x) (huE : u ∉ E') :
    gfun q T n b ⊆ gset q T ph (gfun q T ℓ' x \ E') :=
  (gfun_sub_coarse hc hbu hlv).trans (fun w hw => Set.mem_biUnion (show u ∈ gfun q T ℓ' x \ E' from
    ⟨hu, huE⟩) hw)

/-- **判定法**: 箱ごとの切り離しから、穴の点は宣言された閉包に入らない。 -/
theorem not_mem_closure_of_boxKill (hc : Compat2 q T) {A : Set (ℕ → ℕ)} {a : ℕ → ℕ}
    {p : ℕ → ℕ} (hp : AdmT m p) {z : ℕ → α} {U : Set (ℕ → α)}
    (hU : @IsOpen _ (tauT q T m y0 A) U) (hzU : z ∈ U) {ℓ : ℕ} (hUℓ : U ⊆ gfun q T ℓ z)
    {K : Set (ℕ → α)} (hUK : Disjoint U K)
    (hkill : ∀ L b, m + 5 ≤ L → gfun q T L b ⊆ D1O q T m y0 a →
      gfun q T (min (p 1) L) b ∩ gfun q T ℓ z ⊆ K) :
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
  obtain ⟨d, hdD, hwd⟩ := Set.mem_iUnion₂.mp hwS'
  obtain ⟨L, b, hL, hdb, hbox⟩ := mem_D1O_box hdD
  have hL0 : 0 < L := by omega
  have hwb : w ∈ gfun q T (min (p 1) L) b := by
    rcases le_total L (p 1) with h | h
    · rw [min_eq_right h]
      exact gfun_trans hc hL0 hdb (gfun_anti hc hL0 h d hwd)
    · rw [min_eq_left h]
      exact gfun_trans hc hp1 (gfun_anti hc hp1 h b hdb) hwd
  exact Set.disjoint_left.mp hUK hwU (hkill L b hL hbox ⟨hwb, hUℓ hwU⟩)

/-- 切り離し近傍は τ-開。 -/
theorem killNbhd_isOpen {A : Set (ℕ → ℕ)} {a : ℕ → ℕ} (ha : a ∈ A) {p p' : ℕ → ℕ}
    (hp : AdmT m p) (hp' : AdmT m p') {ℓ ℓ' ph : ℕ} (hℓ0 : 0 < ℓ) (hℓ' : m + 5 < ℓ')
    (hph : p 2 < ph) (z x : ℕ → α) (Γ : Finset ((ℕ → ℕ) × (ℕ → ℕ)))
    (hΓ : ∀ g ∈ Γ, g.1 ∈ A ∧ AdmT m g.2) :
    @IsOpen _ (tauT q T m y0 A)
      (gfun q T ℓ z ∩ (EsetO q T m y0 a p' 1)ᶜ ∩
        (gset q T ph (gfun q T ℓ' x \ EsetO q T m y0 a p 1))ᶜ ∩
        ⋂ g ∈ Γ, (EsetO q T m y0 g.1 g.2 1)ᶜ) := by
  let _ := tauT q T m y0 A
  refine IsOpen.inter (IsOpen.inter (IsOpen.inter ?_ ?_) ?_) ?_
  · exact isOpen_tau_of_mem (Or.inl (Or.inl ⟨ℓ, z, hℓ0, Or.inl rfl⟩))
  · exact isOpen_tau_of_mem (Or.inl (Or.inr ⟨a, ha, p', hp', 0, Or.inr rfl⟩))
  · exact isOpen_tau_of_mem (Or.inr ⟨a, ha, p, hp, 0, ℓ', ph, x, hℓ', hph, Or.inr rfl⟩)
  · refine isOpen_biInter_finset fun g hg => ?_
    exact isOpen_tau_of_mem (Or.inl (Or.inr ⟨g.1, (hΓ g hg).1, g.2, (hΓ g hg).2, 0, Or.inr rfl⟩))

/-- E(α, p, 1) の点 z は、ph が大きければ Definition C の集合 g[ph, g(ℓ′, x) − E(α, p, 1)] の外。 -/
theorem not_mem_defC_large [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m) {a p : ℕ → ℕ}
    (hp : AdmT m p) {z : ℕ → α} (hz : z ∈ EsetO q T m y0 a p 1) :
    ∃ N, ∀ ph, N ≤ ph → ∀ ℓ' x, z ∉ gset q T ph (gfun q T ℓ' x \ EsetO q T m y0 a p 1) := by
  have hp0 : ∀ j, 0 < p j := fun j => lt_of_lt_of_le hp.2.2.1 (hp.1 (Nat.zero_le j))
  have hEo := (EsetO_SOpen_SClosed (y0 := y0) hc hm a p hp0 1).1
  obtain ⟨N0, hN0⟩ := SOpen_preT hc hEo hz
  refine ⟨N0, fun ph hph ℓ' x hzC => ?_⟩
  obtain ⟨u, hu, hzu⟩ := Set.mem_iUnion₂.mp hzC
  exact hu.2 (hN0 ph hph u hzu)

end Defs.D_0061
