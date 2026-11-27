import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.Order.Interval.Set.Infinite
import Defs.D_0032

namespace Defs.D_0033

/-!
Chen–Wang (arXiv 1809.03763v2) §5 の前半（本文 835–1006 行）: Proposition 5.1, Corollary 5.2,
Construction 5 の集合 O(m, n, 1), Fact 5.4, 「Cl_ρ ∪G(m, n, 1) = g(n, i, l)」。

* `ival_sub_of_QStar` : p ∈ Q*_c, a ≤ c なら、[p, p_a) の点 w を含む I_c 区間は [p, p_a) に含まれる
  （論文 Prop 5.1 の Case 2 の長い場合分けの代わり。gap だけから出る）。
* `prop_5_1` : m ≤ n, m ≥ 1 なら、ある c があって、hidx m z ≥ c かつ H(m, z) ∩ g(n, x) ≠ ∅
  ⇒ g(m, z) ⊆ g(n, x)。（論文は m < n だが m ≤ n で成り立つ。）
* `cor_5_2` : 「悪い」z（H(m,z) ∩ g(n,x) ≠ ∅ かつ g(m,z) ⊄ g(n,x)）は hidx m z < c。
* `Obad m n x` : 悪い z の H(m, z) の和。`Oset m n x := g(n, x) − Obad`（論文の O(m, n, 1)）。
* `fact_5_4` : u ∈ O(m, n, 1) なら g(m, u) ⊆ O(m, n, 1)。よって lnc(m, O) は O を覆う（`Oset_lnc_cover`）。
* `Oset_closure` : Cl_ρ O(m, n, 1) = g(n, x)（ρ = ρ′ の積。DenselyOrdered, NoMaxOrder）。
  悪い H(m, z) は有限個の H(m, k)（k < c、先頭 m 座標を固定）に含まれ、それらは内部が空。
  ここで ρ が ρ′ の積であることが本質的に効く（離散積では偽）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0009 Defs.D_0012 Defs.D_0024 Defs.D_0025
  Defs.D_0029 Defs.D_0031 Defs.D_0032

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

theorem ival_sub_of_QStar {a c : ℕ} (ha : 0 < a) (hac : a ≤ c) {p w : α} (hp : T.QStar c p)
    (hw : w ∈ Set.Ico p (T.child p a)) : ival T c w ⊆ Set.Ico p (T.child p a) := by
  have hc : 0 < c := lt_of_lt_of_le ha hac
  obtain ⟨hr, hwr⟩ := ibase_spec T hc w
  set r := ibase T c w
  have he : T.QStar c (T.child p a) :=
    QStar.step p _ hp (T.C_child p a ha) (by rw [T.idx_child]; exact hac)
  have h1 : p ≤ r := by
    by_contra h
    push_neg at h
    exact not_mem_gap T hc hp r ⟨h, lt_of_le_of_lt hw.1 hwr.2⟩
  have h2 : T.child r c ≤ T.child p a := by
    by_contra h
    push_neg at h
    exact not_mem_gap T hc he r ⟨lt_of_le_of_lt hwr.1 hw.2, h⟩
  intro y hy
  exact ⟨le_trans h1 hy.1, lt_of_lt_of_le hy.2 h2⟩

/-- Proposition 5.1。 -/
theorem prop_5_1 (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (x : ℕ → α) :
    ∃ c, ∀ z, c ≤ hidx q m z → (Hcell q T m z ∩ gfun q T n x).Nonempty →
      gfun q T m z ⊆ gfun q T n x := by
  have hQ : ∀ j : ℕ, ∃ cj, T.QStar cj (x j) := fun j => prop_2_2_4 T (x j)
  choose C hC using hQ
  set a := lvl q n x
  have ha : 0 < a := lvl_pos q n x
  set c' := a + (Finset.range n).sup C
  have hc'Q : ∀ j < n, T.QStar c' (x j) := fun j hj =>
    prop_2_2_2 T (le_trans (Finset.le_sup (f := C) (Finset.mem_range.mpr hj)) (by omega)) (hC j)
  refine ⟨c' + n + hidx q n x, fun z hz hne => ?_⟩
  obtain ⟨w, hw1, hw2⟩ := hne
  set b := lvl q m z
  have hb : c' + n + hidx q n x < b := by unfold b lvl; omega
  have hab : a ≤ b := by omega
  intro y hy
  refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · by_cases hkm : k < m
    · have hyk := hy.1 k hkm
      have hwk : w k = z k := hw1.1 k hkm
      have hzk : z k ∈ Set.Ico (x k) (T.child (x k) a) := hwk ▸ hw2.1 k hk
      rcases eq_or_lt_of_le hzk.1 with he | hlt
      · rw [← he] at hyk
        exact ⟨hyk.1, lt_of_lt_of_le hyk.2 (T.child_le_child (x k) ha hab)⟩
      · have := (prop_3_2_1' hc ha hlt hzk.2).2.2 b (by omega) hyk
        exact ⟨le_of_lt this.1, this.2⟩
    · push_neg at hkm
      have hk' : k < m + hidx q m z + 1 := by unfold b lvl at hb; omega
      have hyk := hy.2 k hkm hk'
      have hwk := hw1.2 k hkm hk'
      rw [← ival_eq_of_mem T (lvl_pos q m z) hwk] at hyk
      have hc'pos : 0 < c' := by omega
      have := ival_mono T hc'pos (show c' ≤ b by omega) (w k) hyk
      exact ival_sub_of_QStar ha (by omega) (hc'Q k hk) (hw2.1 k hk) this
  · have hk' : k < m + hidx q m z + 1 := by unfold b lvl at hb; omega
    have hyk := hy.2 k (le_trans hmn hk1) hk'
    have hwk := hw1.2 k (le_trans hmn hk1) hk'
    rw [← ival_eq_of_mem T (lvl_pos q m z) hwk] at hyk
    have := ival_mono T ha hab (w k) hyk
    rwa [ival_eq_of_mem T ha (hw2.2 k hk1 hk2)] at this

/-- 悪い z。 -/
def IsBad (q : ℕ ≃ α) (T : Tree2 α) (m n : ℕ) (x z : ℕ → α) : Prop :=
  (Hcell q T m z ∩ gfun q T n x).Nonempty ∧ ¬ gfun q T m z ⊆ gfun q T n x

/-- Corollary 5.2: 悪い z の番号は有界。 -/
theorem cor_5_2 (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (x : ℕ → α) :
    ∃ c, ∀ z, IsBad q T m n x z → hidx q m z < c := by
  obtain ⟨c, hc'⟩ := prop_5_1 hc hm hmn x
  exact ⟨c, fun z hz => by by_contra h; push_neg at h; exact hz.2 (hc' z h hz.1)⟩

/-- 悪い H(m, z) の和。 -/
noncomputable def Obad (q : ℕ ≃ α) (T : Tree2 α) (m n : ℕ) (x : ℕ → α) : Set (ℕ → α) :=
  ⋃ z ∈ {z | IsBad q T m n x z}, Hcell q T m z

/-- 論文の O(m, n, 1) = g(n, x) − ∪H(m, n, f)。 -/
noncomputable def Oset (q : ℕ ≃ α) (T : Tree2 α) (m n : ℕ) (x : ℕ → α) : Set (ℕ → α) :=
  gfun q T n x \ Obad q T m n x

/-- Fact 5.4: u ∈ O(m, n, 1) なら g(m, u) ⊆ O(m, n, 1)。 -/
theorem fact_5_4 (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m) {x u : ℕ → α}
    (hu : u ∈ Oset q T m n x) : gfun q T m u ⊆ Oset q T m n x := by
  obtain ⟨hug, hub⟩ := hu
  have hgood : gfun q T m u ⊆ gfun q T n x := by
    by_contra h
    exact hub (Set.mem_biUnion (x := u) ⟨⟨u, mem_Hcell q T m u, hug⟩, h⟩ (mem_Hcell q T m u))
  intro v hv
  refine ⟨hgood hv, fun hvb => ?_⟩
  obtain ⟨z, hz, hvz⟩ := Set.mem_iUnion₂.mp hvb
  apply hz.2
  rw [← gfun_eq_of_mem_Hcell q T hm hvz]
  exact (gfun_trans hc hm hv).trans hgood

/-- lnc(m, O(m, n, 1)) は O(m, n, 1) を覆う（論文の ∪G(m, n, ∗) = O(m, n, 1)）。 -/
theorem Oset_lnc_cover (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m) (x : ℕ → α) :
    ⋃₀ lnc q T m (Oset q T m n x) = Oset q T m n x := by
  apply le_antisymm
  · rintro z ⟨S, hS, hz⟩; exact lnc_sub hS hz
  · intro u hu
    obtain ⟨S, hS, huS⟩ := lnc_exists hc m _ u (fact_5_4 hc hm hu)
    exact ⟨S, hS, huS (mem_gfun q T m u)⟩

/-- Cl_ρ O(m, n, 1) = g(n, x)。 -/
theorem Oset_closure [NoMaxOrder α] [DenselyOrdered α] (hc : Compat2 q T) {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) (x : ℕ → α) :
    @closure (ℕ → α) (ptop α) (Oset q T m n x) = gfun q T n x := by
  let _ : TopologicalSpace α := rho α
  let _ : TopologicalSpace (ℕ → α) := ptop α
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  apply le_antisymm
  · exact closure_minimal Set.diff_subset (gfun_isClosed_p q T n x)
  · obtain ⟨c, hcb⟩ := cor_5_2 hc hm hmn x
    intro y hy
    rw [mem_closure_iff]
    intro V hVo hyV
    obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hVo y hyV
    have hb : ∃ b, y 0 < b ∧ (0 ∈ I → Set.Ico (y 0) b ⊆ u 0) := by
      by_cases h0 : 0 ∈ I
      · obtain ⟨b, hb, hs⟩ := rho_nhd (hu 0 h0).1 (hu 0 h0).2
        exact ⟨b, hb, fun _ => hs⟩
      · obtain ⟨b, hb⟩ := exists_gt (y 0)
        exact ⟨b, hb, fun h => absurd h h0⟩
    obtain ⟨b, hyb, hbs⟩ := hb
    have hy0 := hy.1 0 hn
    set e := min b (T.child (x 0) (lvl q n x))
    have hye : y 0 < e := lt_min hyb hy0.2
    -- 番号 < c の点は有限個なので、(y 0, e) から番号 ≥ c の点 v が取れる
    have hfin : {v : α | q.symm v < c}.Finite := by
      have : {v : α | q.symm v < c} = q '' {k | k < c} := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_image]
        constructor
        · intro h; exact ⟨q.symm v, h, q.apply_symm_apply v⟩
        · rintro ⟨k, hk, rfl⟩; rwa [q.symm_apply_apply]
      rw [this]; exact (Set.finite_lt_nat c).image _
    obtain ⟨v, hv, hvc⟩ := ((Set.Ioo_infinite hye).diff hfin).nonempty
    simp only [Set.mem_setOf_eq, not_lt] at hvc
    refine ⟨Function.update y 0 v, ?_, ?_, ?_⟩
    · apply hsub
      intro k hk
      by_cases h : k = 0
      · subst h
        rw [Function.update_self]
        exact hbs hk ⟨hv.1.le, lt_of_lt_of_le hv.2 (min_le_left _ _)⟩
      · rw [Function.update_of_ne h]; exact (hu k hk).2
    · refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
      · by_cases h : k = 0
        · subst h
          rw [Function.update_self]
          exact ⟨le_trans hy0.1 hv.1.le, lt_of_lt_of_le hv.2 (min_le_right _ _)⟩
        · rw [Function.update_of_ne h]; exact hy.1 k hk
      · rw [Function.update_of_ne (by omega)]; exact hy.2 k hk1 hk2
    · intro hb'
      obtain ⟨z, hz, hvz⟩ := Set.mem_iUnion₂.mp hb'
      have hzc := hcb z hz
      have h1 : hidx q m (Function.update y 0 v) = hidx q m z := hidx_eq_of_mem_Hcell q T hm hvz
      have h2 : q.symm (Function.update y 0 v 0) ≤ hidx q m (Function.update y 0 v) :=
        code_ge m (fun k => q.symm (Function.update y 0 v k)) 0 hm
      rw [Function.update_self] at h2
      omega

end Defs.D_0033
