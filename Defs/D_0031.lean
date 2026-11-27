import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0025
import Defs.D_0030

namespace Defs.D_0031

/-!
Chen–Wang (arXiv 1809.03763v2) Construction 4（Operation O1、本文 540–720 行）の**閉じた形**。

論文の Operation O1 は、G_m の残りと交わる H(n, i, l) のうち番号 i が最小のものを順に取り、
対応する g(n, i, l) を G (n, m, 0) に加える帰納的構成である。G_n は laminar
（`Defs.D_0025.gfun_nested`: 交われば番号の小さい方が大きい方を含む）で、
真の包含 g(n,x) ⊊ g(n,y) は番号 `hidx` を真に減らすので、この構成の結果は
「G に含まれる g(n, ·) のうち**極大**なもの全体」と一致する（本文の各段階で、取られた g は
それを真に含む g(n,·) ⊆ G_m を持たない。逆に極大な g は、その番号の段階で必ず取られる）。
ここではこの閉じた形 `lnc q T n G` を定義とし、Claim 4.1, 4.3, 4.4 の内容を示す。
Construction 4 の帰納（Æ, Œ）で作られる G (n_b, m, 0) も、Claim 4.4.4 の細分性から
`lnc q T n_b G_m` と一致する（`lnc_refine`）。

* `ival_eq_of_mem`, `gfun_eq_of_mem_Hcell` : Note D2（x, z ∈ H(n, i, l) なら g(n, x) = g(n, z)）。
* `fact_4_0` : H(ℓ, x) ∩ g(m, y₀) ≠ ∅, ℓ ≥ m ≥ 1 なら g(ℓ, x) ⊆ g(m, y₀)。
* `lnc` : G に含まれる極大な g(n, x) 全体（Ln cover）。
* `lnc_exists` : g(n, x) ⊆ G なら、それを含む `lnc` の元がある。
* `lnc_disjoint` : `lnc` の相異なる元は交わらない。
* `lnc_sUnion` : G = g(m, y₀), n ≥ m ≥ 1 なら ⋃ lnc = G（Claim 4.1.1）。
* `lnc_discrete` : `lnc` は ρ（`Defs.D_0029.ptop`）で開閉集合からなる離散族（Claim 4.1.2）。
* `claim_4_1_4` : g(ℓ, x) ⊆ G_m, ℓ ≥ n ≥ m なら g(ℓ, x) はある `lnc n` の元に含まれる。
* `claim_4_4_5` : H(ℓ, x) ∩ G_m ≠ ∅, ℓ ≥ n ≥ m なら g(ℓ, x) はある `lnc n` の元に含まれる。
* `lnc_refine` : n_a ≤ n_b なら `lnc n_b` の元は `lnc n_a` の各元に含まれるか交わらない（Claim 4.4.4）。
* `lnc_refine_cover` : `lnc n_a` の元 S' は、それに含まれる `lnc n_b` の元の和（Claim 4.4.4）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0009 Defs.D_0012 Defs.D_0024
  Defs.D_0025 Defs.D_0029

variable {α : Type} [LinearOrder α] (q : ℕ ≃ α) (T : Tree2 α)

theorem ival_eq_of_mem {a : ℕ} (ha : 0 < a) {r s : α} (h : r ∈ ival T a s) :
    ival T a r = ival T a s := by
  obtain ⟨hr1, hr2⟩ := ibase_spec T ha r
  obtain ⟨hs1, -⟩ := ibase_spec T ha s
  by_cases he : ibase T a r = ibase T a s
  · unfold ival; rw [he]
  · exact absurd (Set.disjoint_left.mp (prop_2_2_1_disjoint T ha hr1 hs1 he) hr2 h) id

theorem hidx_eq_of_mem_Hcell {n : ℕ} (hn : 0 < n) {x z : ℕ → α} (hz : z ∈ Hcell q T n x) :
    hidx q n z = hidx q n x :=
  (code_eq_iff n hn _ _).2 (fun k hk => by show q.symm (z k) = q.symm (x k); rw [hz.1 k hk])

/-- Note D2: z ∈ H(n, x) なら g(n, z) = g(n, x)。 -/
theorem gfun_eq_of_mem_Hcell {n : ℕ} (hn : 0 < n) {x z : ℕ → α} (hz : z ∈ Hcell q T n x) :
    gfun q T n z = gfun q T n x := by
  have hh := hidx_eq_of_mem_Hcell q T hn hz
  have hl : lvl q n z = lvl q n x := by unfold lvl; rw [hh]
  ext w
  simp only [gfun, Set.mem_setOf_eq]
  rw [hh, hl]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
    · rw [← hz.1 k hk]; exact h1 k hk
    · rw [← ival_eq_of_mem T (lvl_pos q n x) (hz.2 k hk1 hk2)]; exact h2 k hk1 hk2
  · rintro ⟨h1, h2⟩
    refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
    · rw [hz.1 k hk]; exact h1 k hk
    · rw [ival_eq_of_mem T (lvl_pos q n x) (hz.2 k hk1 hk2)]; exact h2 k hk1 hk2

variable {q T}

/-- Fact 4.0: H(ℓ, x) ∩ g(m, y₀) ≠ ∅ かつ ℓ ≥ m ≥ 1 なら g(ℓ, x) ⊆ g(m, y₀)。 -/
theorem fact_4_0 (hc : Compat2 q T) {m ℓ : ℕ} (hm : 0 < m) (hml : m ≤ ℓ) {x y0 : ℕ → α}
    (h : (Hcell q T ℓ x ∩ gfun q T m y0).Nonempty) : gfun q T ℓ x ⊆ gfun q T m y0 := by
  obtain ⟨z, hz1, hz2⟩ := h
  rw [← gfun_eq_of_mem_Hcell q T (lt_of_lt_of_le hm hml) hz1]
  exact (gfun_anti hc hm hml z).trans (gfun_trans hc hm hz2)

/-- 強い意味での真の包含は番号を減らす。 -/
theorem hidx_lt_of_ssub (hc : Compat2 q T) {n : ℕ} {x y : ℕ → α}
    (hxy : gfun q T n x ⊆ gfun q T n y) (hne : gfun q T n y ≠ gfun q T n x) :
    hidx q n y < hidx q n x := by
  by_contra hge
  push_neg at hge
  have := gfun_nested hc hge ⟨x, mem_gfun q T n x, hxy (mem_gfun q T n x)⟩
  exact hne (le_antisymm this hxy)

variable (q T)

/-- Ln cover: G に含まれる極大な g(n, x) 全体。 -/
def lnc (n : ℕ) (G : Set (ℕ → α)) : Set (Set (ℕ → α)) :=
  {S | ∃ x, S = gfun q T n x ∧ S ⊆ G ∧
    ∀ y, S ⊆ gfun q T n y → gfun q T n y ⊆ G → gfun q T n y = S}

variable {q T}

theorem lnc_sub {n : ℕ} {G S : Set (ℕ → α)} (hS : S ∈ lnc q T n G) : S ⊆ G := by
  obtain ⟨x, -, hxG, -⟩ := hS
  exact hxG

theorem lnc_exists (hc : Compat2 q T) (n : ℕ) (G : Set (ℕ → α)) (x : ℕ → α)
    (hx : gfun q T n x ⊆ G) : ∃ S ∈ lnc q T n G, gfun q T n x ⊆ S := by
  suffices h : ∀ c, ∀ x, hidx q n x = c → gfun q T n x ⊆ G →
      ∃ S ∈ lnc q T n G, gfun q T n x ⊆ S from h _ x rfl hx
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro x hc' hxG
    by_cases hmax : ∀ y, gfun q T n x ⊆ gfun q T n y → gfun q T n y ⊆ G →
        gfun q T n y = gfun q T n x
    · exact ⟨gfun q T n x, ⟨x, rfl, hxG, hmax⟩, le_rfl⟩
    · push_neg at hmax
      obtain ⟨y, hxy, hyG, hne⟩ := hmax
      have hlt := hidx_lt_of_ssub hc hxy hne
      obtain ⟨S, hS, hyS⟩ := ih _ (hc' ▸ hlt) y rfl hyG
      exact ⟨S, hS, hxy.trans hyS⟩

theorem lnc_disjoint (hc : Compat2 q T) {n : ℕ} {G S S' : Set (ℕ → α)}
    (hS : S ∈ lnc q T n G) (hS' : S' ∈ lnc q T n G) (hne : S ≠ S') : Disjoint S S' := by
  obtain ⟨x, rfl, hxG, hxm⟩ := hS
  obtain ⟨y, rfl, hyG, hym⟩ := hS'
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hi
  have hi' := Set.nonempty_iff_ne_empty.mpr hi
  rcases le_total (hidx q n x) (hidx q n y) with h | h
  · have hyx := gfun_nested hc h hi'
    exact hne (hym x hyx hxG)
  · have hxy := gfun_nested hc h (Set.inter_comm _ _ ▸ hi')
    exact hne (hxm y hxy hyG).symm

/-- g(m, y₀) の点 x では、n ≥ m なら g(n, x) ⊆ g(m, y₀)。 -/
theorem gfun_sub_of_mem (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {x y0 : ℕ → α} (hx : x ∈ gfun q T m y0) : gfun q T n x ⊆ gfun q T m y0 :=
  (gfun_anti hc hm hmn x).trans (gfun_trans hc hm hx)

/-- Claim 4.1.1: ⋃ lnc(n, g(m, y₀)) = g(m, y₀)（n ≥ m ≥ 1）。 -/
theorem lnc_sUnion (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (y0 : ℕ → α) :
    ⋃₀ lnc q T n (gfun q T m y0) = gfun q T m y0 := by
  apply le_antisymm
  · rintro z ⟨S, hS, hz⟩
    exact lnc_sub hS hz
  · intro x hx
    obtain ⟨S, hS, hxS⟩ := lnc_exists hc n _ x (gfun_sub_of_mem hc hm hmn hx)
    exact ⟨S, hS, hxS (mem_gfun q T n x)⟩

/-- Claim 4.1.2: lnc(n, g(m, y₀)) は ρ で c.o.D。 -/
theorem lnc_discrete [NoMaxOrder α] (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (y0 : ℕ → α) :
    (∀ S ∈ lnc q T n (gfun q T m y0),
      @IsOpen (ℕ → α) (ptop α) S ∧ @IsClosed (ℕ → α) (ptop α) S) ∧
    IsDiscreteFam (ptop α)
      (fun S : {S // S ∈ lnc q T n (gfun q T m y0)} => S.1) := by
  refine ⟨fun S hS => ?_, fun z => ?_⟩
  · obtain ⟨x, rfl, -, -⟩ := hS
    exact ⟨gfun_isOpen_p q T n x, gfun_isClosed_p q T n x⟩
  · by_cases hz : z ∈ gfun q T m y0
    · rw [← lnc_sUnion hc hm hmn y0] at hz
      obtain ⟨S, hS, hzS⟩ := hz
      obtain ⟨x, rfl, -, -⟩ := id hS
      refine ⟨gfun q T n x, gfun_isOpen_p q T n x, hzS, ?_⟩
      have key : ∀ S' : {S // S ∈ lnc q T n (gfun q T m y0)},
          (S'.1 ∩ gfun q T n x).Nonempty → S'.1 = gfun q T n x := by
        intro S' h
        by_contra hne
        exact Set.not_disjoint_iff_nonempty_inter.mpr h (lnc_disjoint hc S'.2 hS hne)
      intro i j hi hj
      show i.1 = j.1
      rw [key i hi, key j hj]
    · refine ⟨(gfun q T m y0)ᶜ, (gfun_isClosed_p q T m y0).isOpen_compl, hz, ?_⟩
      intro i j hi
      exfalso
      obtain ⟨w, hw1, hw2⟩ := hi
      exact hw2 (lnc_sub i.2 hw1)

/-- Claim 4.1.4: g(ℓ, x) ⊆ g(m, y₀), ℓ ≥ n ≥ m ≥ 1 なら g(ℓ, x) ⊆ S ∈ lnc n。 -/
theorem claim_4_1_4 (hc : Compat2 q T) {m n ℓ : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hnl : n ≤ ℓ)
    {x y0 : ℕ → α} (h : gfun q T ℓ x ⊆ gfun q T m y0) :
    ∃ S ∈ lnc q T n (gfun q T m y0), gfun q T ℓ x ⊆ S := by
  have hx : x ∈ gfun q T m y0 := h (mem_gfun q T ℓ x)
  obtain ⟨S, hS, hxS⟩ := lnc_exists hc n _ x (gfun_sub_of_mem hc hm hmn hx)
  exact ⟨S, hS, (gfun_anti hc (lt_of_lt_of_le hm hmn) hnl x).trans hxS⟩

/-- Claim 4.4.5: H(ℓ, x) ∩ g(m, y₀) ≠ ∅, ℓ ≥ n ≥ m ≥ 1 なら g(ℓ, x) ⊆ S ∈ lnc n。 -/
theorem claim_4_4_5 (hc : Compat2 q T) {m n ℓ : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hnl : n ≤ ℓ)
    {x y0 : ℕ → α} (h : (Hcell q T ℓ x ∩ gfun q T m y0).Nonempty) :
    ∃ S ∈ lnc q T n (gfun q T m y0), gfun q T ℓ x ⊆ S :=
  claim_4_1_4 hc hm hmn hnl (fact_4_0 hc hm (hmn.trans hnl) h)

/-- Claim 4.4.4（前半）: n_a ≤ n_b なら lnc n_b の元は lnc n_a の元に含まれるか交わらない。 -/
theorem lnc_refine (hc : Compat2 q T) {m na nb : ℕ} (hm : 0 < m) (hma : m ≤ na) (hab : na ≤ nb)
    {y0 : ℕ → α} {S S' : Set (ℕ → α)} (hS : S ∈ lnc q T nb (gfun q T m y0))
    (hS' : S' ∈ lnc q T na (gfun q T m y0)) : S ⊆ S' ∨ Disjoint S S' := by
  obtain ⟨x, rfl, hxG, -⟩ := hS
  obtain ⟨S'', hS'', hsub⟩ := claim_4_1_4 hc hm hma hab hxG
  by_cases he : S'' = S'
  · exact Or.inl (he ▸ hsub)
  · exact Or.inr (Set.disjoint_of_subset_left hsub (lnc_disjoint hc hS'' hS' he))

/-- Claim 4.4.4（後半）: lnc n_a の元は、それに含まれる lnc n_b の元の和。 -/
theorem lnc_refine_cover (hc : Compat2 q T) {m na nb : ℕ} (hm : 0 < m) (hma : m ≤ na)
    (hab : na ≤ nb) {y0 : ℕ → α} {S' : Set (ℕ → α)} (hS' : S' ∈ lnc q T na (gfun q T m y0)) :
    ⋃₀ {S | S ∈ lnc q T nb (gfun q T m y0) ∧ S ⊆ S'} = S' := by
  apply le_antisymm
  · rintro z ⟨S, ⟨-, hS⟩, hz⟩
    exact hS hz
  · intro z hz
    have hzG : z ∈ gfun q T m y0 := lnc_sub hS' hz
    rw [← lnc_sUnion hc hm (hma.trans hab) y0] at hzG
    obtain ⟨S, hS, hzS⟩ := hzG
    rcases lnc_refine hc hm hma hab hS hS' with h | h
    · exact ⟨S, ⟨hS, h⟩, hzS⟩
    · exact absurd hz (Set.disjoint_left.mp h hzS)

end Defs.D_0031
