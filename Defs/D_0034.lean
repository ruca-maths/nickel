import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.Topology.Bases
import Defs.D_0033

namespace Defs.D_0034

/-!
Chen–Wang (arXiv 1809.03763v2) Theorem 1.a（本文 TeX 4927–5040 行）の**一般的な骨格**。

論文の τ は「g(l, x), E(αk, p_k), g[p, U] とそれらの補集合を開とする」位相、すなわち
これらを部分基とする位相である。Theorem 1.a の証明の 3 は、閉集合 H を部分基の補集合の
有限和で覆い、各部分基の元について「x ∈ S ⇒ ある n で x ∉ Cl_τ g[n, Y − S]」を示すことに帰着する。
ここではこの帰着を一般の位相で示し（`subbase_crit`）、さらに ρ 由来の部分基
（g(l, x') とその補集合）は**任意の**より細かい位相でこの条件を満たすことを示す（`gfun_subbasic`,
`gfun_compl_subbasic`）。よって τ の stratifiable 性は、追加の部分基（E や g[p, U]）についての
条件（論文の Prop 7.3–7.5）だけに帰着する（`strat_of_extra`）。

* `subbase_crit` : t = generateFrom S、g が t-開・x ∈ g n x・n について減少。各 s ∈ S, x ∈ s に
  ある n で x ∉ closure (⋃_{y ∉ s} g n y) なら、任意の閉集合 H と x ∉ H にある n で
  x ∉ closure (⋃_{y ∈ H} g n y)（L_0017 の仮定の形）。
* `gfun_coord_eq` : x を固定すると、n が大きければ x ∈ g(n, z) ⇒ z の先頭 N 座標は x と一致
  （ρ での半 stratifiable 性。Prop 3.2.1 から）。
* `gfun_subbasic`, `gfun_compl_subbasic` : x ∈ g(l, x')（resp. x ∉ g(l, x')）なら、ある n で
  g(n, x) は g(l, x') の外（resp. 中）の点 z の g(n, z) すべてと交わらない。
* `strat_of_extra` : 追加の部分基族 𝓔 を加えた位相 t でも g(n+1, ·) は L_0017 の仮定を満たす、
  ただし 𝓔 の各元について部分基条件を仮定する。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0009 Defs.D_0012 Defs.D_0024 Defs.D_0025
  Defs.D_0029 Defs.D_0031

section General

variable {X : Type}

theorem subbase_crit (t : TopologicalSpace X) (S : Set (Set X)) (ht : t = .generateFrom S)
    (g : ℕ → X → Set X) (hopen : ∀ n x, @IsOpen X t (g n x)) (hdec : ∀ n x, g (n + 1) x ⊆ g n x)
    (hS : ∀ s ∈ S, ∀ x ∈ s, ∃ n, x ∉ @closure X t (⋃ y ∈ sᶜ, g n y))
    (H : Set X) (hH : @IsClosed X t H) (x : X) (hx : x ∉ H) :
    ∃ n, x ∉ @closure X t (⋃ y ∈ H, g n y) := by
  let _ : TopologicalSpace X := t
  have hanti : ∀ x, Antitone (fun n => g n x) := fun x => antitone_nat_of_succ_le (hdec · x)
  have hb := TopologicalSpace.isTopologicalBasis_of_subbasis ht
  obtain ⟨B, ⟨f, ⟨hf, hfS⟩, rfl⟩, hxB, hBH⟩ :=
    hb.exists_subset_of_mem_open (show x ∈ Hᶜ from hx) hH.isOpen_compl
  have hn : ∀ s ∈ f, ∃ n, x ∉ closure (⋃ y ∈ sᶜ, g n y) :=
    fun s hs => hS s (hfS hs) x (hxB s hs)
  choose! N hN using hn
  refine ⟨hf.toFinset.sup N, fun hcl => ?_⟩
  have hsub : (⋃ y ∈ H, g (hf.toFinset.sup N) y) ⊆ ⋃ s ∈ f, ⋃ y ∈ sᶜ, g (N s) y := by
    intro w hw
    obtain ⟨y, hyH, hwy⟩ := Set.mem_iUnion₂.mp hw
    have : y ∉ ⋂₀ f := fun h => hBH h hyH
    rw [Set.mem_sInter] at this
    push_neg at this
    obtain ⟨s, hs, hys⟩ := this
    have hle : N s ≤ hf.toFinset.sup N := Finset.le_sup (f := N) (hf.mem_toFinset.mpr hs)
    exact Set.mem_iUnion₂.mpr ⟨s, hs, Set.mem_iUnion₂.mpr ⟨y, hys, hanti y hle hwy⟩⟩
  have := closure_mono hsub hcl
  rw [hf.closure_biUnion] at this
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp this
  exact hN s hs hxs

end General

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

/-- ρ での半 stratifiable 性: n が大きければ x ∈ g(n, z) ⇒ z の先頭 N 座標は x と一致。 -/
theorem gfun_coord_eq (hc : Compat2 q T) (x : ℕ → α) (N : ℕ) :
    ∃ n0, ∀ n, n0 ≤ n → ∀ z, x ∈ gfun q T n z → ∀ k < N, z k = x k := by
  refine ⟨N + (Finset.range N).sup (fun k => q.symm (x k)), fun n hn z hz k hk => ?_⟩
  by_contra hne
  have h := hz.1 k (by omega)
  have hlt : z k < x k := lt_of_le_of_ne h.1 hne
  have h1 := (prop_3_2_1' hc (lvl_pos q n z) hlt h.2).2.1
  have h2 : q.symm (x k) ≤ (Finset.range N).sup (fun k => q.symm (x k)) :=
    Finset.le_sup (f := fun k => q.symm (x k)) (Finset.mem_range.mpr hk)
  unfold lvl at h1
  omega

/-- g(l, x') への所属は先頭 l + hidx + 1 座標で決まる。 -/
theorem mem_gfun_of_coord {l : ℕ} {x' x z : ℕ → α} (hx : x ∈ gfun q T l x')
    (h : ∀ k < l + hidx q l x' + 1, z k = x k) : z ∈ gfun q T l x' := by
  rw [gfun_eq] at hx ⊢
  intro k hk
  rw [h k hk]
  exact hx k hk

/-- 部分基 g(l, x') の条件。 -/
theorem gfun_subbasic (hc : Compat2 q T) {l : ℕ} (hl : 0 < l) {x' x : ℕ → α}
    (hx : x ∈ gfun q T l x') :
    ∃ n0, ∀ n, n0 ≤ n → ∀ z, z ∉ gfun q T l x' → Disjoint (gfun q T n x) (gfun q T n z) := by
  obtain ⟨n1, hn1⟩ := gfun_coord_eq hc x (l + hidx q l x' + 1)
  refine ⟨n1 + l, fun n hn z hz => ?_⟩
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hi
  have hi' := Set.nonempty_iff_ne_empty.mpr hi
  rcases le_total (hidx q n x) (hidx q n z) with h | h
  · have hzx := gfun_nested hc h hi'
    exact hz (gfun_sub_of_mem hc hl (by omega) hx (hzx (mem_gfun q T n z)))
  · have hxz := gfun_nested hc h (Set.inter_comm _ _ ▸ hi')
    exact hz (mem_gfun_of_coord hx (hn1 n (by omega) z (hxz (mem_gfun q T n x))))

/-- Prop 3.4 の一様版: n が十分大きければ g(n, x) ⊆ U。 -/
theorem prop_3_4_eventually [NoMaxOrder α] (hc : Compat2 q T) (x : ℕ → α) (U : Set (ℕ → α))
    (hU : @IsOpen (ℕ → α) (ptop α) U) (hx : x ∈ U) :
    ∃ n0, ∀ n, n0 ≤ n → gfun q T n x ⊆ U := by
  let _ : TopologicalSpace α := rho α
  let _ : TopologicalSpace (ℕ → α) := ptop α
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU x hx
  have hb : ∀ a : ℕ, ∃ b, a ∈ I → x a < b ∧ Set.Ico (x a) b ⊆ u a := by
    intro a
    by_cases ha : a ∈ I
    · obtain ⟨b, h1, h2⟩ := rho_nhd (hu a ha).1 (hu a ha).2
      exact ⟨b, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨x a, fun h => absurd h ha⟩
  choose b hb using hb
  have hA : ∀ a : ℕ, ∃ A, a ∈ I → 0 < A ∧ T.child (x a) A < b a := by
    intro a
    by_cases ha : a ∈ I
    · obtain ⟨A, h1, h2⟩ := hc.shrink (x a) (b a) (hb a ha).1
      exact ⟨A, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose A hA using hA
  refine ⟨I.sup (fun a => a + 1 + A a), fun n hn z hz => ?_⟩
  apply hsub
  intro a ha
  have hle : a + 1 + A a ≤ I.sup (fun a => a + 1 + A a) :=
    Finset.le_sup (f := fun a => a + 1 + A a) ha
  have hza := hz.1 a (by omega)
  apply (hb a ha).2
  refine ⟨hza.1, lt_of_lt_of_le hza.2 ?_⟩
  refine le_trans (T.child_le_child (x a) (hA a ha).1 ?_) (hA a ha).2.le
  unfold lvl; omega

/-- 部分基 X − g(l, x') の条件。 -/
theorem gfun_compl_subbasic [NoMaxOrder α] (hc : Compat2 q T) {l : ℕ} (hl : 0 < l)
    {x' x : ℕ → α} (hx : x ∉ gfun q T l x') :
    ∃ n0, ∀ n, n0 ≤ n → ∀ z, z ∈ gfun q T l x' → Disjoint (gfun q T n x) (gfun q T n z) := by
  obtain ⟨n1, hn1⟩ := prop_3_4_eventually hc x (gfun q T l x')ᶜ
    (gfun_isClosed_p q T l x').isOpen_compl hx
  refine ⟨n1 + l + 1, fun n hn z hz => ?_⟩
  have hn1' : gfun q T n x ⊆ (gfun q T l x')ᶜ :=
    hn1 n (by omega)
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hi
  have hi' := Set.nonempty_iff_ne_empty.mpr hi
  rcases le_total (hidx q n x) (hidx q n z) with h | h
  · have hzx := gfun_nested hc h hi'
    exact hn1' (hzx (mem_gfun q T n z)) (gfun_sub_of_mem hc hl (by omega) hz (mem_gfun q T n z))
  · have hxz := gfun_nested hc h (Set.inter_comm _ _ ▸ hi')
    exact hn1' (mem_gfun q T n x) (gfun_sub_of_mem hc hl (by omega) hz (hxz (mem_gfun q T n x)))

/-- 開集合 u と交わらない集合の閉包は u と交わらない。 -/
theorem not_mem_closure_of_disjoint {X : Type} (t : TopologicalSpace X) {u s : Set X} {x : X}
    (hu : @IsOpen X t u) (hx : x ∈ u) (hd : Disjoint u s) : x ∉ @closure X t s := by
  let _ : TopologicalSpace X := t
  intro h
  have := closure_minimal (Set.subset_compl_iff_disjoint_left.mpr hd) hu.isClosed_compl h
  exact this hx

/-- ρ 由来の部分基。 -/
def rhoSub (q : ℕ ≃ α) (T : Tree2 α) : Set (Set (ℕ → α)) :=
  {s | ∃ l x', 0 < l ∧ (s = gfun q T l x' ∨ s = (gfun q T l x')ᶜ)}

/-- 追加の部分基 𝓔 を加えた位相での g-関数の条件（Theorem 1.a の帰着）。 -/
theorem strat_of_extra [NoMaxOrder α] (hc : Compat2 q T) (E : Set (Set (ℕ → α)))
    (t : TopologicalSpace (ℕ → α)) (ht : t = .generateFrom (rhoSub q T ∪ E))
    (hE : ∀ s ∈ E, ∀ x ∈ s, ∃ n, x ∉ @closure _ t (⋃ y ∈ sᶜ, gfun q T (n + 1) y)) :
    (∀ n x, @IsOpen _ t (gfun q T (n + 1) x) ∧ x ∈ gfun q T (n + 1) x) ∧
    (∀ n x, gfun q T (n + 1 + 1) x ⊆ gfun q T (n + 1) x) ∧
    (∀ H : Set (ℕ → α), @IsClosed _ t H → ∀ x, x ∉ H →
      ∃ n, x ∉ @closure _ t (⋃ y ∈ H, gfun q T (n + 1) y)) := by
  have hopen : ∀ n x, @IsOpen _ t (gfun q T (n + 1) x) := fun n x => by
    rw [ht]; exact TopologicalSpace.GenerateOpen.basic _ (Or.inl ⟨n + 1, x, by omega, Or.inl rfl⟩)
  have hdec : ∀ n x, gfun q T (n + 1 + 1) x ⊆ gfun q T (n + 1) x :=
    fun n x => gfun_anti hc (by omega) (by omega) x
  refine ⟨fun n x => ⟨hopen n x, mem_gfun q T _ x⟩, hdec, ?_⟩
  refine subbase_crit t _ ht (fun n x => gfun q T (n + 1) x) hopen hdec ?_
  rintro s (⟨l, x', hl, rfl | rfl⟩ | hs) x hx
  · obtain ⟨n0, hn0⟩ := gfun_subbasic hc hl hx
    refine ⟨n0, not_mem_closure_of_disjoint t (hopen n0 x) (mem_gfun q T _ x) ?_⟩
    rw [Set.disjoint_iUnion₂_right]
    exact fun z hz => hn0 (n0 + 1) (by omega) z hz
  · obtain ⟨n0, hn0⟩ := gfun_compl_subbasic hc hl hx
    refine ⟨n0, not_mem_closure_of_disjoint t (hopen n0 x) (mem_gfun q T _ x) ?_⟩
    rw [Set.disjoint_iUnion₂_right]
    exact fun z hz => hn0 (n0 + 1) (by omega) z (by simpa using hz)
  · exact hE s hs x hx

end Defs.D_0034
