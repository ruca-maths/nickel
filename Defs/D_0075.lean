import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0074

namespace Defs.D_0075

/-!
**Prop 8.3 の反例（帯による構成、τ・Δ-order・列挙 lab によらない）**。

`Defs.D_0074` の反例は D_0043 型の τ（中心 x ∈ E の Definition C の集合を含む）と敵対的な Δ-order
（`fcAdv`）を使っていた。ここでは V の作り方を変え、次の性質しか使わない反例を作る。
* G = g_c(b, y₀) が τ-開、E₁ = E(α,p,1) が τ-閉、各 E(P) := E(α, p[3 ↦ P], 2) が τ-開かつ τ-閉。
* 選択関数 fc は任意の妥当なもの（`WeakFC` かつ `ValidFC`。論文の firstC も含む）。

構成: R_i := α(m + 2i + p₃ + 5)、F := ⋃_i (E(R_i) − E(R_i + 1))、V := (G − E₁) − Cl_τ F。
* `same_slab`: 層 Q ≥ lvl(m, x) の箱 g(Q, e) が x を含めば、e は x と同じ slab にある。
* n = 2 の悪い点: K-trick の点 w ∈ g(R_i, c_B) は偶数の帯に入る（F ⊆ Cl F、V の外）。
* n = 3 の悪い点: 穴 c_B は奇数の帯 E(R_i + 1) − E(R_{i+1})（F と交わらない τ-開集合）に入り、V に入る。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0009 Defs.D_0012 Defs.D_0024 Defs.D_0025
  Defs.D_0029 Defs.D_0031 Defs.D_0034 Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039
  Defs.D_0040 Defs.D_0043 Defs.D_0049 Defs.D_0050 Defs.D_0051 Defs.D_0056 Defs.D_0060 Defs.D_0062
  Defs.D_0064 Defs.D_0065 Defs.D_0066 Defs.D_0067 Defs.D_0068 Defs.D_0070 Defs.D_0071 Defs.D_0072
  Defs.D_0073 Defs.D_0074

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

/-! ### 同じ slab の補題 -/

/-- 層 Q ≥ lvl(m, x) の箱 g(Q, e) が x を含めば、e の先頭 m 座標の符号は x と同じ（同じ slab）。 -/
theorem same_slab (hc : Compat2 q T) (hm : 0 < m) {Q : ℕ} {x e : ℕ → α}
    (hQ : lvl q m x ≤ Q) (hx : x ∈ gfun q T Q e) : hidx q m e = hidx q m x := by
  by_contra hne
  have hex : ∃ k < m, x k ≠ e k := by
    by_contra h
    apply hne
    refine (code_eq_iff m hm _ _).2 (fun k hk => ?_)
    show q.symm (e k) = q.symm (x k)
    by_contra h2
    exact h ⟨k, hk, fun h3 => h2 (by rw [h3])⟩
  obtain ⟨k, hk, hxe⟩ := hex
  have hkQ : k < Q := by unfold lvl at hQ; omega
  have hxk := hx.1 k hkQ
  have hlt : e k < x k := lt_of_le_of_ne hxk.1 (fun h => hxe h.symm)
  have h1 := (prop_3_2_1' hc (lvl_pos q Q e) hlt hxk.2).2.1
  have h2 := qsymm_lt_lvl (q := q) x hk
  have h3 : Q < lvl q Q e := by unfold lvl; omega
  omega

/-! ### 一般の選択関数での piece の組み立て -/

structure PieceDataG (q : ℕ ≃ α) (T : Tree2 α) (m : ℕ) (y0 : ℕ → α)
    (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) (a : ℕ → ℕ)
    (c : ℕ) (S : Set (ℕ → α)) (n v : ℕ) where
  S2 : Set (ℕ → α)
  S3 : Set (ℕ → α)
  M5 : Set (ℕ → α)
  S0 : Set (ℕ → α)
  x0 : ℕ → α
  cB : ℕ → α
  hS2 : S2 ∈ lncA q T (m + 2) (slabO q T m y0 c ∩ S)
  hS2lab : lab (lncA q T (m + 2) (slabO q T m y0 c ∩ S)) S2 = n
  hS3 : S3 ∈ lncA q T (m + 3) (slabO q T m y0 c ∩ S ∩ S2)
  hpiece : (slabO q T m y0 c ∩ S ∩ S2 ∩ S3, v) ∈ pieces q T m (slabO q T m y0 c ∩ S) n
  hM5 : M5 ∈ chBoxes q T m a (slabO q T m y0 c ∩ S ∩ S2 ∩ S3) v
  hS0 : S0 ∈ lncA q T (a (m + v)) (slabO q T m y0 c ∩ S ∩ S2 ∩ S3)
  hS0e : S0 = gfun q T (a (m + v)) x0
  hS0M5 : S0 ⊆ M5
  hgood : Good q T (S0 ∩ (slabO q T m y0 c ∩ S ∩ S2 ∩ S3)) (a (m + v)) x0
  hfc : fc (a (m + v) + 1) (S0 ∩ (slabO q T m y0 c ∩ S ∩ S2 ∩ S3)) =
    gfun q T (a (m + v) + 1) cB
  hcB : cB ∈ S0 ∩ (slabO q T m y0 c ∩ S ∩ S2 ∩ S3)
  hGd : gfun q T (a (m + v) + 1) cB ∈ GdF q T m fc a (slabO q T m y0 c ∩ S ∩ S2 ∩ S3) v

theorem piece_builderG [Countable α] [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m)
    {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} (hvfc : ValidFC q T fc)
    {a : ℕ → ℕ} (ha : StrictMono a) {c : ℕ} {S : Set (ℕ → α)}
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c)) (n v : ℕ) (hv : 5 ≤ v) :
    Nonempty (PieceDataG q T m y0 fc a c S n v) := by
  obtain ⟨x1, hx1, hSe, -⟩ := id hS
  have hc0 : c ≠ hidx q m y0 := by
    intro h; unfold slabO at hx1; rw [ite_eq_left h] at hx1; exact hx1
  have hslab : slabO q T m y0 c = H q m c ∩ gfun q T m y0 := by
    unfold slabO; rw [ite_eq_right hc0]; rfl
  set A1 := slabO q T m y0 c ∩ S with hA1
  have hgA1 : Good q T A1 (m + 1) x1 := by
    have hg0 : Good q T (H q m c ∩ gfun q T m y0) m y0 :=
      ⟨Set.inter_subset_right, fun k hk =>
        FreeAt.inter (H_free hm (by omega) c) (gfun_free y0 (by omega))⟩
    have := good_step hc hm (by omega : m ≤ m + 1) hg0 (hslab ▸ hx1)
    rw [hA1, hslab, hSe]; exact this
  have hA1ne : x1 ∈ A1 := ⟨hx1, hSe ▸ mem_gfun q T _ x1⟩
  have h2inf := good_infinite hc (by omega) (by omega : m + 1 < m + 2) ⟨x1, hA1ne⟩ hgA1
  have hF2 : (lncA q T (m + 2) A1).Countable ∧ (lncA q T (m + 2) A1).Infinite :=
    ⟨lncA_countable (by omega) A1, h2inf⟩
  set S2 := unlab (lncA q T (m + 2) A1) hF2 n with hS2
  have hS2mem : S2 ∈ lncA q T (m + 2) A1 := unlab_mem _ hF2 n
  have hS2lab : lab (lncA q T (m + 2) A1) S2 = n := lab_unlab _ hF2 n
  obtain ⟨x2, hx2, hS2eq, -⟩ := id hS2mem
  have hgA12 : Good q T (A1 ∩ S2) (m + 2) x2 := by
    rw [hS2eq]; exact good_step hc (by omega) (by omega) hgA1 hx2
  have hx2' : x2 ∈ A1 ∩ S2 := ⟨hx2, hS2eq ▸ mem_gfun q T _ x2⟩
  have h3inf := good_infinite hc (by omega) (by omega : m + 2 < m + 3) ⟨x2, hx2'⟩ hgA12
  have hF3 : (lncA q T (m + 3) (A1 ∩ S2)).Countable ∧ (lncA q T (m + 3) (A1 ∩ S2)).Infinite :=
    ⟨lncA_countable (by omega) _, h3inf⟩
  set S3 := unlab (lncA q T (m + 3) (A1 ∩ S2)) hF3 v with hS3
  have hS3mem : S3 ∈ lncA q T (m + 3) (A1 ∩ S2) := unlab_mem _ hF3 v
  have hS3lab : lab (lncA q T (m + 3) (A1 ∩ S2)) S3 = v := lab_unlab _ hF3 v
  have hpiece : (A1 ∩ S2 ∩ S3, v) ∈ pieces q T m A1 n :=
    ⟨S2, hS2mem, hS2lab, S3, hS3mem, hS3lab.symm, rfl⟩
  obtain ⟨x3, hx3, hS3eq, -⟩ := id hS3mem
  set P := A1 ∩ S2 ∩ S3 with hP
  have hgP : Good q T P (m + 3) x3 := by
    rw [hP, hS3eq]; exact good_step hc (by omega) (by omega) hgA12 hx3
  have hx3P : x3 ∈ P := ⟨hx3, hS3eq ▸ mem_gfun q T _ x3⟩
  have h4inf := good_infinite hc (by omega) (by omega : m + 3 < m + 4) ⟨x3, hx3P⟩ hgP
  have hF4 : (lncA q T (m + 4) P).Countable ∧ (lncA q T (m + 4) P).Infinite :=
    ⟨lncA_countable (by omega) _, h4inf⟩
  set S4 := unlab (lncA q T (m + 4) P) hF4 (a v) with hS4
  have hS4mem : S4 ∈ lncA q T (m + 4) P := unlab_mem _ hF4 _
  have hS4lab : lab (lncA q T (m + 4) P) S4 = a v := lab_unlab _ hF4 _
  obtain ⟨x4, hx4, hS4eq, -⟩ := id hS4mem
  have hg45 : Good q T (S4 ∩ P) (m + 4) x4 := by
    rw [hS4eq]; exact good_step' hc (by omega) (by omega) hgP hx4
  have hne45 : (S4 ∩ P).Nonempty := ⟨x4, by rw [hS4eq]; exact mem_gfun q T _ x4, hx4⟩
  have h5inf := good_infinite hc (by omega) (by omega : m + 4 < m + 5) hne45 hg45
  have hF5 : (lncA q T (m + 5) (S4 ∩ P)).Countable ∧ (lncA q T (m + 5) (S4 ∩ P)).Infinite :=
    ⟨lncA_countable (by omega) _, h5inf⟩
  set M5 := unlab (lncA q T (m + 5) (S4 ∩ P)) hF5 (a v + 1) with hM5
  have hM5mem : M5 ∈ lncA q T (m + 5) (S4 ∩ P) := unlab_mem _ hF5 _
  have hM5lab : lab (lncA q T (m + 5) (S4 ∩ P)) M5 = a v + 1 := lab_unlab _ hF5 _
  have hch : M5 ∈ chBoxes q T m a P v :=
    ⟨S4, hS4mem, hM5mem, Or.inl ⟨by rw [hS4lab], by rw [hM5lab]; omega⟩⟩
  obtain ⟨x5, hx5, hM5eq, -⟩ := id hM5mem
  have hav : m + v ≤ a (m + v) := ha.id_le _
  have hx5P : x5 ∈ P := hx5.2
  obtain ⟨hS0mem, hx5S0⟩ := lncA_mem_spec hc (sub_gset (q := q) (T := T) (a (m + v)) P hx5P)
  set S0 := lncA_mem q T (a (m + v)) P x5 with hS0
  obtain ⟨x0, hx0, hS0eq, -⟩ := id hS0mem
  have hS0sub5 : S0 ⊆ gfun q T (m + 5) x0 := by
    rw [hS0eq]; exact gfun_anti hc (by omega) (by omega) x0
  have hx0S4 : x0 ∈ S4 := by
    have h1 : gfun q T (m + 4) x0 ⊆ S4 :=
      lncA_absorb hc hS4mem hx0 ⟨x5, gfun_anti hc (by omega) (by omega) x0 (hS0eq ▸ hx5S0),
        hx5.1⟩
    exact h1 (mem_gfun q T _ x0)
  have hS0M5 : S0 ⊆ M5 := by
    refine hS0sub5.trans (lncA_absorb hc hM5mem ⟨hx0S4, hx0⟩ ⟨x5, hS0sub5 hx5S0, ?_⟩)
    rw [hM5eq]; exact mem_gfun q T _ x5
  have hgS0 : Good q T (S0 ∩ P) (a (m + v)) x0 := by
    rw [hS0eq]; exact good_step' hc (by omega) (by omega) hgP hx0
  have hne0 : (S0 ∩ P).Nonempty := ⟨x0, by rw [hS0eq]; exact mem_gfun q T _ x0, hx0⟩
  have hinf0 := good_infinite hc (by omega) (by omega : a (m + v) < a (m + v) + 1) hne0 hgS0
  have hmem := hvfc (a (m + v) + 1) (S0 ∩ P) (lncA_countable (by omega) _) hinf0
  obtain ⟨cB, hcB, hfce, -⟩ := hmem
  have hGd : gfun q T (a (m + v) + 1) cB ∈ GdF q T m fc a P v := by
    unfold GdF
    rw [ite_eq_left (by omega : m + 5 ≤ a (m + v) + 1)]
    exact ⟨⟨S0, hS0mem, hfce.symm⟩, cB, mem_gfun q T _ cB,
      Set.mem_sUnion.mpr ⟨M5, hch, hS0M5 hcB.1⟩⟩
  exact ⟨⟨S2, S3, M5, S0, x0, cB, hS2mem, hS2lab, hS3mem, hpiece, hch, hS0mem, hS0eq,
    hS0M5, hgS0, hfce, hcB, hGd⟩⟩

section pd

variable {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} {a : ℕ → ℕ} {c : ℕ} {S : Set (ℕ → α)} {n v : ℕ}

theorem ktrickG (pd : PieceDataG q T m y0 fc a c S n v) (hc : Compat2 q T) (ha : StrictMono a)
    (hm : 0 < m)
    {K1 : ℕ} (hK1 : K1 < lvl q (a (m + v) + 1) pd.cB) :
    ∃ w, w ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3) ∧
      w ∉ gfun q T (a (m + v) + 1) pd.cB ∧ ∀ k < K1, w k = pd.cB k := by
  have hcB := pd.hcB
  have hcS0 : pd.cB ∈ gfun q T (a (m + v)) pd.x0 := pd.hS0e ▸ hcB.1
  have hav : m + v ≤ a (m + v) := ha.id_le _
  have hlv0 : lvl q (a (m + v)) pd.x0 < lvl q (a (m + v) + 1) pd.cB := by
    have h1 := hidx_le_of_mem_gfun hc (by omega) hcS0
    have h2 := code_mono (a (m + v)) (by omega) (fun k => q.symm (pd.cB k)) (a (m + v) + 1)
      (by omega)
    unfold lvl hidx at *; omega
  set L := a (m + v) + 1 with hL
  set K := max K1 (lvl q (a (m + v)) pd.x0) with hK
  have hKlt : K < lvl q L pd.cB := max_lt hK1 hlv0
  have hKL : L ≤ K := by
    have : L ≤ lvl q (a (m + v)) pd.x0 := by unfold lvl; omega
    omega
  set b := ibase T (lvl q L pd.cB) (pd.cB K) with hb
  set w := Function.update pd.cB K (T.child b (lvl q L pd.cB)) with hw
  refine ⟨w, ?_, ?_, fun k hk => ?_⟩
  · exact pd.hgood.2 K (le_max_right _ _) _ hcB _
  · intro hwB
    have h := hwB.2 K hKL hKlt
    rw [hw, Function.update_self] at h
    exact absurd h.2 (lt_irrefl _)
  · rw [hw, Function.update_of_ne (by omega)]

/-- piece の G_d 箱で w を含むものは c_B の箱だけ。 -/
theorem not_mem_GdF_of_pdG (pd : PieceDataG q T m y0 fc a c S n v) (hc : Compat2 q T)
    (hwfc : WeakFC q T fc) (hL : m + 5 ≤ a (m + v) + 1) {w : ℕ → α}
    (hw : w ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3))
    (hwB : w ∉ gfun q T (a (m + v) + 1) pd.cB) {B : Set (ℕ → α)}
    (hB : B ∈ GdF q T m fc a (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3) v) : w ∉ B := by
  intro hwB'
  unfold GdF at hB
  rw [ite_eq_left hL] at hB
  obtain ⟨⟨S0', hS0', hBe⟩, -⟩ := hB
  rcases hwfc (a (m + v) + 1) (S0' ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3)) with
    h0 | ⟨u, hu, hue, -⟩
  · rw [hBe, h0] at hwB'; exact hwB'
  · have hwu : w ∈ gfun q T (a (m + v) + 1) u := by rw [hBe, hue] at hwB'; exact hwB'
    have hwS0' : w ∈ S0' := mem_lncA_of_box hc (by omega) (by omega) hS0' hu.1 hwu
    have hSS := lncA_unique hc pd.hS0 hS0' hw.1 hwS0'
    subst hSS
    rw [hBe, pd.hfc] at hwB'
    exact hwB hwB'

theorem not_mem_AllCells_of_pdG (pd : PieceDataG q T m y0 fc a c S n v) (hc : Compat2 q T)
    (hwfc : WeakFC q T fc)
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c)) (hL : m + 5 ≤ a (m + v) + 1) {w : ℕ → α}
    (hw : w ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3))
    (hwB : w ∉ gfun q T (a (m + v) + 1) pd.cB) (n' : ℕ) :
    w ∉ AllCells q T m y0 fc a n' := by
  rintro ⟨c', S', hS', Pv', hP', B', hB', hwB', hwP'⟩
  have hPP := piece_unique hc hS hS' pd.hpiece hP' hw.2 hwP'
  subst hPP
  exact not_mem_GdF_of_pdG pd hc hwfc hL hw hwB hB' hwB'

theorem not_mem_HkOF_of_pdG (pd : PieceDataG q T m y0 fc a c S n v) (hc : Compat2 q T)
    (hwfc : WeakFC q T fc)
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c)) (hL : m + 5 ≤ a (m + v) + 1) {w : ℕ → α}
    (hw : w ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3))
    (hwB : w ∉ gfun q T (a (m + v) + 1) pd.cB) (p : ℕ → ℕ) (k : ℕ)
    (prevD : ℕ → Set (ℕ → α)) (c' : ℕ) :
    w ∉ HkOF q T m y0 fc a p k prevD c' := by
  intro h
  obtain ⟨S', Pv', B', hS', hP', -, hB', hwB', hwP'⟩ := mem_HkOF h
  exact not_mem_AllCells_of_pdG pd hc hwfc hS hL hw hwB (k + 2)
    ⟨c', S', hS', Pv', hP', B', hB', hwB', hwP'⟩

theorem mem_RegionW_of_pdG (pd : PieceDataG q T m y0 fc a c S n v) {N : ℕ} (hN : N < v)
    {w : ℕ → α} (hw : w ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3)) :
    w ∈ RegionW q T m y0 a c S n N :=
  ⟨_, pd.hpiece, hN, pd.M5, pd.hM5, pd.hS0M5 hw.1, hw.2⟩

end pd

/-! ### 帯 -/

/-- p の 3 番目以降を P 以上に上げた列（E(α,·,2) の閾値 p₃ だけを P に変える）。 -/
def pP (p : ℕ → ℕ) (P : ℕ) : ℕ → ℕ := fun j => if j < 3 then p j else max (p j) P

theorem pP_lt3 {p : ℕ → ℕ} {P j : ℕ} (h : j < 3) : pP p P j = p j := by
  unfold pP; exact ite_eq_left h

theorem pP_3 {p : ℕ → ℕ} {P : ℕ} : pP p P 3 = max (p 3) P := by
  unfold pP; exact ite_eq_right (by omega)

theorem admT_pP {p : ℕ → ℕ} (hp : AdmT m p) (P : ℕ) : AdmT m (pP p P) := by
  obtain ⟨hmono, h1, h0, h12⟩ := hp
  refine ⟨fun i j hij => ?_, ?_, ?_, ?_⟩
  · have := hmono hij
    have hij' : i ≤ j := hij
    simp only [pP]
    split_ifs <;> omega
  · rw [pP_lt3 (by omega)]; exact h1
  · rw [pP_lt3 (by omega)]; exact h0
  · rw [pP_lt3 (by omega), pP_lt3 (by omega)]; exact h12

variable (q T m y0) in
/-- 論文の E(α3, P)（p₁, p₂ は p のまま）。 -/
noncomputable def EP (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) (a p : ℕ → ℕ) (P : ℕ) :
    Set (ℕ → α) :=
  EsetOF q T m y0 fc a (pP p P) 2

/-- 帯の境目 R_i = α(m + 2i + p₃ + 5)。 -/
def Rb (a p : ℕ → ℕ) (m i : ℕ) : ℕ := a (m + (2 * i + p 3 + 5))

variable (q T m y0) in
/-- 偶数の帯の和 F = ⋃_i (E(R_i) − E(R_i + 1))。 -/
noncomputable def Fband (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) (a p : ℕ → ℕ) : Set (ℕ → α) :=
  ⋃ i, (EP q T m y0 fc a p (Rb a p m i) \ EP q T m y0 fc a p (Rb a p m i + 1))

variable (q T m y0) in
/-- 反例の V = (G − E₁) − Cl_τ F。 -/
noncomputable def VcexB (τ : TopologicalSpace (ℕ → α)) (fc : ℕ → Set (ℕ → α) → Set (ℕ → α))
    (a p : ℕ → ℕ) (cc b : ℕ) : Set (ℕ → α) :=
  (gcBox q T cc b y0 \ EsetOF q T m y0 fc a p 1) ∩ (@closure _ τ (Fband q T m y0 fc a p))ᶜ

variable (q T m y0) in
/-- `FineS` の位相を一般の τ にしたもの。 -/
def FineST (τ : TopologicalSpace (ℕ → α)) (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) (a p : ℕ → ℕ)
    (k : ℕ) (V : Set (ℕ → α)) : Prop :=
  ∃ n, 1 ≤ n ∧ n ≤ k ∧ ∃ c S, S ∈ lncA q T (m + 1) (slabO q T m y0 c) ∧ ∃ N,
    ∀ x ∈ RegionW q T m y0 a c S n N,
      (x ∉ AllCells q T m y0 fc a n → x ∈ V) ∧
      (x ∈ HolesW q T m y0 fc a p n → x ∉ @closure _ τ V)

theorem fineS_iff_fineST {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} {A : Set (ℕ → ℕ)} {a p : ℕ → ℕ}
    {k : ℕ} {V : Set (ℕ → α)} :
    FineS q T m y0 fc A a p k V ↔ FineST q T m y0 (tauTF q T m y0 fc A) fc a p k V := Iff.rfl

section band

variable {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)}

theorem Rb_ge {a : ℕ → ℕ} (ha : StrictMono a) (p : ℕ → ℕ) (m i : ℕ) :
    m + (2 * i + p 3 + 5) ≤ Rb a p m i := ha.id_le _

theorem Rb_mono {a : ℕ → ℕ} (ha : StrictMono a) (p : ℕ → ℕ) (m : ℕ) {i j : ℕ} (h : i ≤ j) :
    Rb a p m i ≤ Rb a p m j := ha.monotone (by omega)

theorem Rb_gap {a : ℕ → ℕ} (ha : StrictMono a) (p : ℕ → ℕ) (m i : ℕ) :
    Rb a p m i + 2 ≤ Rb a p m (i + 1) := by
  unfold Rb
  have e : m + (2 * (i + 1) + p 3 + 5) = m + (2 * i + p 3 + 5) + 1 + 1 := by omega
  rw [e]
  have h1 := ha (show m + (2 * i + p 3 + 5) < m + (2 * i + p 3 + 5) + 1 by omega)
  have h2 := ha (show m + (2 * i + p 3 + 5) + 1 < m + (2 * i + p 3 + 5) + 1 + 1 by omega)
  omega

theorem EseqOF_pP1 (a p : ℕ → ℕ) (P : ℕ) :
    EseqOF q T m y0 fc a (pP p P) 1 = EseqOF q T m y0 fc a p 1 :=
  EseqOF_congr (q := q) (T := T) (m := m) (y0 := y0) (fc := fc) a 1
    (fun j hj => pP_lt3 (by omega))

theorem EP_eq (a p : ℕ → ℕ) (P : ℕ) :
    EP q T m y0 fc a p P = gset q T (max (p 3) P) (EsetOF q T m y0 fc a p 1) ∪
      ⋃ c, HkOF q T m y0 fc a (pP p P) 1 (EseqOF q T m y0 fc a p 1).2 c := by
  show gset q T (pP p P 3) (EseqOF q T m y0 fc a (pP p P) 1).1 ∪
      ⋃ c, HkOF q T m y0 fc a (pP p P) 1 (EseqOF q T m y0 fc a (pP p P) 1).2 c = _
  rw [EseqOF_pP1, pP_3]
  rfl

theorem EP_p3 (a p : ℕ → ℕ) : EP q T m y0 fc a p (p 3) = EsetOF q T m y0 fc a p 2 := by
  have h := EseqOF_congr (q := q) (T := T) (m := m) (y0 := y0) (fc := fc) a 2
    (p := pP p (p 3)) (p' := p) (fun j hj => by
      unfold pP
      split_ifs with h
      · rfl
      · have : j = 3 := by omega
        subst this; exact max_self _)
  unfold EP EsetOF
  rw [h]

/-- HkOF は閾値について単調減少。 -/
theorem HkOF_thr_mono {a p p' : ℕ → ℕ} {k : ℕ} {prevD : ℕ → Set (ℕ → α)} {c : ℕ}
    (h : p (k + 2) ≤ p' (k + 2)) :
    HkOF q T m y0 fc a p' k prevD c ⊆ HkOF q T m y0 fc a p k prevD c := by
  intro x hx
  unfold HkOF slabRec at hx
  obtain ⟨S, ⟨hS, z, hzS, hzc, hzn⟩, hxS⟩ := Set.mem_iUnion₂.mp hx
  simp only [holeCellsF, Set.mem_iUnion, exists_prop] at hxS
  obtain ⟨Pv, ⟨hPv, hr⟩, B, hB, hxB, hxP⟩ := hxS
  exact mem_HkOF_of_allowed hS hzS hzc (fun hz => hzn (Or.inr hz)) hPv (le_trans h hr) hB hxB hxP

theorem EP_anti (hc : Compat2 q T) {a p : ℕ → ℕ} (hp : AdmT m p) {P P' : ℕ} (h : P ≤ P') :
    EP q T m y0 fc a p P' ⊆ EP q T m y0 fc a p P := by
  have hp3 : 0 < p 3 := lt_of_lt_of_le hp.2.2.1 (hp.1 (by omega))
  rw [EP_eq, EP_eq]
  apply Set.union_subset_union
  · intro z hz
    obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.mp hz
    exact Set.mem_iUnion₂.mpr ⟨e, he,
      gfun_anti hc (lt_of_lt_of_le hp3 (le_max_left _ _)) (max_le_max le_rfl h) e hze⟩
  · refine Set.iUnion_mono fun c => HkOF_thr_mono ?_
    show pP p P 3 ≤ pP p P' 3
    rw [pP_3, pP_3]; exact max_le_max le_rfl h

/-- 箱 g(L, e) は、e を含む G_d の箱に含まれる。 -/
theorem mem_GdF_of_box (hc : Compat2 q T) (hwfc : WeakFC q T fc) {a : ℕ → ℕ}
    {P : Set (ℕ → α)} {v : ℕ} (hL : m + 5 ≤ a (m + v) + 1) {B : Set (ℕ → α)}
    (hB : B ∈ GdF q T m fc a P v) {e w : ℕ → α} (he : e ∈ B)
    (hw : w ∈ gfun q T (a (m + v) + 1) e) : w ∈ B := by
  unfold GdF at hB
  rw [ite_eq_left hL] at hB
  obtain ⟨⟨S0', hS0', hBe⟩, -⟩ := hB
  rcases hwfc (a (m + v) + 1) (S0' ∩ P) with h0 | ⟨u, hu, hue, -⟩
  · rw [hBe, h0] at he; exact absurd he (Set.notMem_empty _)
  · rw [hBe, hue] at he ⊢
    exact gfun_trans hc (by omega) he hw

theorem bad_of_pd {a : ℕ → ℕ} {V : Set (ℕ → α)} {c : ℕ}
    {S : Set (ℕ → α)} {n N v : ℕ} (hc : Compat2 q T) (hwfc : WeakFC q T fc)
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c))
    (hfine1 : ∀ x ∈ RegionW q T m y0 a c S n N, x ∉ AllCells q T m y0 fc a n → x ∈ V)
    (pd : PieceDataG q T m y0 fc a c S n v) (hNv : N < v) (hL : m + 5 ≤ a (m + v) + 1)
    {w : ℕ → α} (hw : w ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3))
    (hwB : w ∉ gfun q T (a (m + v) + 1) pd.cB) (hwV : w ∉ V) : False :=
  hwV (hfine1 w (mem_RegionW_of_pdG pd hNv hw)
    (not_mem_AllCells_of_pdG pd hc hwfc hS hL hw hwB n))

end band

/-! ### 主定理 -/

/-- **Prop 8.3 の反例（帯による構成）**。τ は「G が開、E₁ が閉、各 E(P) が開かつ閉」を満たす任意の位相、
選択関数 fc は任意の妥当なもの。 -/
theorem prop83_band [Countable α] [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m)
    {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} (hwfc : WeakFC q T fc) (hvfc : ValidFC q T fc)
    {a : ℕ → ℕ} (ha : StrictMono a) {p : ℕ → ℕ} (hp : AdmT m p)
    {cc : ℕ} (hcc : 0 < cc) (b : ℕ) (τ : TopologicalSpace (ℕ → α))
    (hG : @IsOpen _ τ (gcBox q T cc b y0))
    (hE1 : @IsClosed _ τ (EsetOF q T m y0 fc a p 1))
    (hEP : ∀ P, @IsOpen _ τ (EP q T m y0 fc a p P) ∧ @IsClosed _ τ (EP q T m y0 fc a p P)) :
    @IsOpen _ τ (VcexB q T m y0 τ fc a p cc b) ∧
    y0 ∈ VcexB q T m y0 τ fc a p cc b ∧
    gcBox q T cc b y0 \ EsetOF q T m y0 fc a p 2 ⊆ VcexB q T m y0 τ fc a p cc b ∧
    VcexB q T m y0 τ fc a p cc b ⊆ gcBox q T cc b y0 \ EsetOF q T m y0 fc a p 1 ∧
    ¬ FineST q T m y0 τ fc a p 3 (VcexB q T m y0 τ fc a p cc b) := by
  let _ := τ
  set E1 := EsetOF q T m y0 fc a p 1 with hE1def
  set E2 := EsetOF q T m y0 fc a p 2 with hE2def
  set G := gcBox q T cc b y0 with hGdef
  set F := Fband q T m y0 fc a p with hFdef
  set V := VcexB q T m y0 τ fc a p cc b with hVdef
  have hVe : V = (G \ E1) ∩ (closure F)ᶜ := rfl
  obtain ⟨hmono, hp15, hp0, hp12⟩ := id hp
  have hp23 : p 2 ≤ p 3 := hmono (by omega)
  have hE12 : E1 ⊆ E2 := EsetOF_sub_succ a p 1
  have hEP3 : EP q T m y0 fc a p (p 3) = E2 := EP_p3 a p
  have hFE2 : F ⊆ E2 := by
    intro z hz
    obtain ⟨i, hzi, -⟩ := Set.mem_iUnion.mp hz
    rw [← hEP3]
    have := Rb_ge ha p m i
    exact EP_anti hc hp (by omega) hzi
  have hE2c : IsClosed E2 := hEP3 ▸ (hEP (p 3)).2
  have hclF : closure F ⊆ E2 := closure_minimal hFE2 hE2c
  have hy0 : ∀ k, y0 ∉ EsetOF q T m y0 fc a p k := y0_not_mem_EsetOF hc hm hwfc a hp
  refine ⟨?_, ?_, ?_, Set.inter_subset_left, ?_⟩
  · rw [hVe, Set.sdiff_eq]
    exact (hG.inter hE1.isOpen_compl).inter isClosed_closure.isOpen_compl
  · exact ⟨⟨mem_gcBox_self hcc b y0, hy0 1⟩, fun h => hy0 2 (hclF h)⟩
  · rintro x ⟨hxG, hxE2⟩
    exact ⟨⟨hxG, fun h => hxE2 (hE12 h)⟩, fun h => hxE2 (hclF h)⟩
  · rintro ⟨n, hn1, hn3, c, S, hS, N, hfine⟩
    have hfine1 := fun x hx => (hfine x hx).1
    set i := N + c + lvl q b y0 + p 3 + 7 with hi
    have hRi := Rb_ge ha p m i
    have hRi1 := Rb_ge ha p m (i + 1)
    have hgap := Rb_gap ha p m i
    obtain rfl | rfl | rfl : n = 1 ∨ n = 2 ∨ n = 3 := by omega
    · -- n = 1: c_B ∈ D₁、K-trick の点は E₁ に入る
      set v := 2 * i + p 3 + 5 with hv
      have hav : m + v ≤ a (m + v) := ha.id_le _
      obtain ⟨pd⟩ := piece_builderG (y0 := y0) hc hm hvfc ha hS 1 v (by omega)
      have hcB := pd.hcB
      have hL5 : m + 5 ≤ a (m + v) + 1 := by omega
      have hcD : pd.cB ∈ D1OF q T m y0 fc a := by
        by_cases hal : S ∈ allowedO q T m y0 c (⋃ i ∈ Finset.range c, D1slabOF q T m y0 fc a i)
        · refine Set.mem_iUnion.mpr ⟨c, ?_⟩
          rw [D1slabOF_eq]
          refine Set.mem_iUnion₂.mpr ⟨S, hal, ?_⟩
          unfold holeBoxesUF
          simp only [Set.mem_iUnion, Set.mem_sUnion, exists_prop]
          exact ⟨_, ⟨pd.hpiece, Nat.zero_le _⟩, _, pd.hGd, mem_gfun q T _ _⟩
        · by_contra hnot
          apply hal
          refine ⟨hS, pd.cB, hcB.2.1.1.2, hcB.2.1.1.1, fun hpr => hnot ?_⟩
          obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.mp hpr
          exact Set.mem_iUnion.mpr ⟨j, hj⟩
      have hK : lvl q (p 1) pd.cB < lvl q (a (m + v) + 1) pd.cB :=
        lvl_lt_of_mem hc (by omega) (by omega) (mem_gfun q T _ _)
      obtain ⟨w, hw, hwB, hwk⟩ := ktrickG pd hc ha hm hK
      have hw0 : w ∈ EsetOF q T m y0 fc a p 0 := by
        rw [EsetOF_zero]
        exact Set.mem_iUnion₂.mpr ⟨pd.cB, hcD, gfun_mem_of_agree (mem_gfun q T _ _) hwk⟩
      exact bad_of_pd hc hwfc hS hfine1 pd (by omega) hL5 hw hwB
        (fun h => h.1.2 (EsetOF_sub_succ a p 0 hw0))
    · -- n = 2: K-trick の点は偶数の帯に入る
      set v := 2 * i + p 3 + 5 with hv
      have hav : m + v ≤ a (m + v) := ha.id_le _
      obtain ⟨pd⟩ := piece_builderG (y0 := y0) hc hm hvfc ha hS 2 v (by omega)
      have hcB := pd.hcB
      have hL5 : m + 5 ≤ a (m + v) + 1 := by omega
      have hR : Rb a p m i = a (m + v) := rfl
      have hcE1 : pd.cB ∈ E1 :=
        HkOF_sub_EsetOF_succ a p 0 c (mem_HkOF_of_allowed (k := 0) hS hcB.2.1.1.2 hcB.2.1.1.1
          (not_mem_gset_D1slabOF hc hwfc a (by omega) hS pd.hS2 (by rw [pd.hS2lab]; omega)
            hcB.2.1.1.2 hcB.2.1.2) pd.hpiece (show p 2 ≤ v by omega) pd.hGd
          (mem_gfun q T _ _) hcB.2)
      have hK : lvl q (a (m + v)) pd.cB < lvl q (a (m + v) + 1) pd.cB :=
        lvl_lt_of_mem hc (by omega) (by omega) (mem_gfun q T _ _)
      obtain ⟨w, hw, hwB, hwk⟩ := ktrickG pd hc ha hm hK
      have hwR : w ∈ gfun q T (a (m + v)) pd.cB := gfun_mem_of_agree (mem_gfun q T _ _) hwk
      by_cases hwE1 : w ∈ E1
      · exact bad_of_pd hc hwfc hS hfine1 pd (by omega) hL5 hw hwB (fun h => h.1.2 hwE1)
      have hws := slabO_hidx hw.2.1.1.1
      have hwF : w ∈ F := by
        refine Set.mem_iUnion.mpr ⟨i, ?_, ?_⟩
        · rw [EP_eq]
          have hmx : max (p 3) (Rb a p m i) = a (m + v) := by rw [hR]; exact max_eq_right (by omega)
          rw [hmx]
          exact Or.inl (Set.mem_iUnion₂.mpr ⟨pd.cB, hcE1, hwR⟩)
        · rw [EP_eq]
          rintro (h | h)
          · have hmx : max (p 3) (Rb a p m i + 1) = a (m + v) + 1 := by
              rw [hR]; exact max_eq_right (by omega)
            rw [hmx] at h
            obtain ⟨e, he, hwe⟩ := Set.mem_iUnion₂.mp h
            have hlvw : lvl q m w ≤ a (m + v) + 1 := by unfold lvl; rw [hws.1]; omega
            have hes := same_slab hc hm hlvw hwe
            replace he : e ∈ gset q T (p 2) (EsetOF q T m y0 fc a p 0) ∪ ⋃ c, HkOF q T m y0 fc a p 0 (EseqOF q T m y0 fc a p 0).2 c := he
            rcases he with he | he
            · obtain ⟨e0, he0, hee0⟩ := Set.mem_iUnion₂.mp he
              apply hwE1
              refine gset_sub_EsetOF_succ a p 0 (Set.mem_iUnion₂.mpr ⟨e0, he0, ?_⟩)
              exact gfun_trans hc (by omega) hee0 (gfun_anti hc (by omega) (by omega) e hwe)
            · obtain ⟨c', he'⟩ := Set.mem_iUnion.mp he
              have hec' := (slabO_hidx (HkOF_sub_slab he')).1
              have hcc' : c' = c := by rw [← hec', hes, hws.1]
              subst hcc'
              obtain ⟨S', Pv', B', hS', hP', -, hB', heB', heP'⟩ := mem_HkOF he'
              obtain ⟨S2', hS2', -, S3', hS3', -, hPe⟩ := id hP'
              have hwP' : w ∈ Pv'.1 := by
                rw [hPe] at heP' ⊢
                exact ⟨⟨⟨hw.2.1.1.1, mem_lncA_of_box hc (by omega) (by omega) hS' heP'.1.1.2 hwe⟩,
                  mem_lncA_of_box hc (by omega) (by omega) hS2' heP'.1.2 hwe⟩,
                  mem_lncA_of_box hc (by omega) (by omega) hS3' heP'.2 hwe⟩
              have hPP := piece_unique hc hS hS' pd.hpiece hP' hw.2 hwP'
              subst hPP
              exact not_mem_GdF_of_pdG pd hc hwfc hL5 hw hwB hB'
                (mem_GdF_of_box hc hwfc hL5 hB' heB' hwe)
          · obtain ⟨c', h'⟩ := Set.mem_iUnion.mp h
            exact not_mem_HkOF_of_pdG pd hc hwfc hS hL5 hw hwB _ _ _ c' h'
      exact bad_of_pd hc hwfc hS hfine1 pd (by omega) hL5 hw hwB
        (fun h => h.2 (subset_closure hwF))
    · -- n = 3: 穴 c_B は奇数の帯に入り、V に入る
      set v := Rb a p m i + 1 with hv
      have hav : m + v ≤ a (m + v) := ha.id_le _
      obtain ⟨pd⟩ := piece_builderG (y0 := y0) hc hm hvfc ha hS 3 v (by omega)
      have hcB := pd.hcB
      set L := a (m + v) + 1 with hLdef
      have hL5 : m + 5 ≤ L := by omega
      have hlvL : L < lvl q L pd.cB := by unfold lvl; omega
      have hcs := slabO_hidx hcB.2.1.1.1
      have hcase0 : pd.cB ∉ gset q T (p 2) (EsetOF q T m y0 fc a p 0) := by
        intro h
        obtain ⟨e0, he0, hce0⟩ := Set.mem_iUnion₂.mp h
        have hK : lvl q (p 2) e0 < lvl q L pd.cB := lvl_lt_of_mem hc (by omega) (by omega) hce0
        obtain ⟨w, hw, hwB, hwk⟩ := ktrickG pd hc ha hm hK
        have hwE : w ∈ E1 := gset_sub_EsetOF_succ a p 0
          (Set.mem_iUnion₂.mpr ⟨e0, he0, gfun_mem_of_agree hce0 hwk⟩)
        exact bad_of_pd hc hwfc hS hfine1 pd (by omega) hL5 hw hwB (fun h => h.1.2 hwE)
      have hcE1 : pd.cB ∉ E1 := by
        show pd.cB ∉ gset q T (p 2) (EsetOF q T m y0 fc a p 0) ∪ ⋃ c, HkOF q T m y0 fc a p 0 (EseqOF q T m y0 fc a p 0).2 c
        rintro (h | h)
        · exact hcase0 h
        · obtain ⟨c', h'⟩ := Set.mem_iUnion.mp h
          exact not_mem_HkOF_of_branch hc hS pd.hpiece hcB.2 a p 0 (by omega) _ c' h'
      have hnD : pd.cB ∉ (EseqOF q T m y0 fc a p 1).2 c := by
        show pd.cB ∉ gset q T (p 1) (D1slabOF q T m y0 fc a c) ∪
          gset q T (p 2) (HkOF q T m y0 fc a p 0 (EseqOF q T m y0 fc a p 0).2 c)
        rintro (h | h)
        · exact not_mem_gset_D1slabOF hc hwfc a (by omega) hS pd.hS2
            (by rw [pd.hS2lab]; omega) hcB.2.1.1.2 hcB.2.1.2 h
        · exact not_mem_gset_HkOF hc (by omega) hS pd.hS2 (by rw [pd.hS2lab]; omega) hcB.2.1.1.2
            hcB.2.1.2 h
      have hhole : ∀ u, u ∈ gfun q T L pd.cB → u ∈ slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3 →
          u ∈ HkOF q T m y0 fc a p 1 (EseqOF q T m y0 fc a p 1).2 c := fun u huB huP =>
        mem_HkOF_of_allowed (k := 1) hS hcB.2.1.1.2 hcB.2.1.1.1 hnD pd.hpiece
          (show p 3 ≤ v by omega) pd.hGd huB huP
      by_cases hcG : pd.cB ∈ G
      · set O := EP q T m y0 fc a p (Rb a p m i + 1) ∩ (EP q T m y0 fc a p (Rb a p m (i + 1)))ᶜ
          with hO
        have hOo : IsOpen O := (hEP _).1.inter (hEP _).2.isOpen_compl
        have hcO : pd.cB ∈ O := by
          constructor
          · rw [EP_eq]
            refine Or.inr (Set.mem_iUnion.mpr ⟨c, ?_⟩)
            exact mem_HkOF_of_allowed (k := 1) hS hcB.2.1.1.2 hcB.2.1.1.1 hnD pd.hpiece
              (show pP p (Rb a p m i + 1) 3 ≤ v by rw [pP_3]; omega) pd.hGd (mem_gfun q T _ _)
              hcB.2
          · rw [EP_eq]
            rintro (h | h)
            · have hmx : max (p 3) (Rb a p m (i + 1)) = Rb a p m (i + 1) := max_eq_right (by omega)
              rw [hmx] at h
              obtain ⟨e, he, hce⟩ := Set.mem_iUnion₂.mp h
              have hlvc : lvl q m pd.cB ≤ Rb a p m (i + 1) := by unfold lvl; rw [hcs.1]; omega
              have hes := same_slab hc hm hlvc hce
              replace he : e ∈ gset q T (p 2) (EsetOF q T m y0 fc a p 0) ∪ ⋃ c, HkOF q T m y0 fc a p 0 (EseqOF q T m y0 fc a p 0).2 c := he
              rcases he with he | he
              · obtain ⟨e0, he0, hee0⟩ := Set.mem_iUnion₂.mp he
                exact hcase0 (Set.mem_iUnion₂.mpr ⟨e0, he0,
                  gfun_trans hc (by omega) hee0 (gfun_anti hc (by omega) (by omega) e hce)⟩)
              · obtain ⟨c', he'⟩ := Set.mem_iUnion.mp he
                have hec' := (slabO_hidx (HkOF_sub_slab he')).1
                have hcc' : c' = c := by rw [← hec', hes, hcs.1]
                subst hcc'
                exact not_mem_gset_HkOF hc (by omega) hS pd.hS2 (by rw [pd.hS2lab]; omega)
                  hcB.2.1.1.2 hcB.2.1.2 (Set.mem_iUnion₂.mpr ⟨e, he', hce⟩)
            · obtain ⟨c', h'⟩ := Set.mem_iUnion.mp h
              obtain ⟨S', Pv', B', hS', hP', hidx', -, -, hcP'⟩ := mem_HkOF h'
              have hPP := piece_unique hc hS hS' pd.hpiece hP' hcB.2 hcP'
              subst hPP
              have : pP p (Rb a p m (i + 1)) 3 ≤ v := hidx'
              rw [pP_3] at this
              omega
        have hFO : F ⊆ Oᶜ := by
          intro z hz hzO
          obtain ⟨j, hzj, hzj1⟩ := Set.mem_iUnion.mp hz
          rcases le_or_gt j i with hji | hji
          · have := Rb_mono ha p m hji
            exact hzj1 (EP_anti hc hp (by omega) hzO.1)
          · exact hzO.2 (EP_anti hc hp (Rb_mono ha p m (by omega)) hzj)
        have hcF : pd.cB ∉ closure F := fun h => (closure_minimal hFO hOo.isClosed_compl h) hcO
        have hcV : pd.cB ∈ V := ⟨⟨hcG, hcE1⟩, hcF⟩
        have hcH : pd.cB ∈ HolesW q T m y0 fc a p 3 := by
          unfold HolesW
          rw [ite_eq_right (show (3:ℕ) ≠ 1 by omega)]
          exact Set.mem_iUnion.mpr ⟨c, hhole _ (mem_gfun q T _ _) hcB.2⟩
        exact (hfine _ (mem_RegionW_of_pdG pd (by omega) hcB)).2 hcH (subset_closure hcV)
      · -- c_B ∉ G: K-trick で G の外の穴でない点
        have hK : lvl q b y0 < lvl q L pd.cB := by omega
        obtain ⟨w, hw, hwB, hwk⟩ := ktrickG pd hc ha hm hK
        refine bad_of_pd hc hwfc hS hfine1 pd (by omega) hL5 hw hwB (fun hwV => hcG ?_)
        exact mem_gcBox_of_agree hwV.1.1 (fun k hk => (hwk k hk).symm)

variable (q T m y0) in
/-- 論文の fine により近い読み方。
* 穴でない点（どのセルにも入らない点）は V に入り、さらに E(αn, p_n)（Lean の `EsetOF (n-1)`）の外にある
  （論文の H − H(m₅σ) ⊆ U[α⁻ b n′, p′_n s] ⊆ V。g_c(b, s) の条件は落とす）。
* 穴は、論文の H(kσ) = (セル) − g[p_k, E(α(k−1))]（TeX 3886）にならい、HolesW から g[p_n, E(α(n−1))] を除いたもの。 -/
def FineP (τ : TopologicalSpace (ℕ → α)) (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) (a p : ℕ → ℕ)
    (k : ℕ) (V : Set (ℕ → α)) : Prop :=
  ∃ n, 1 ≤ n ∧ n ≤ k ∧ ∃ c S, S ∈ lncA q T (m + 1) (slabO q T m y0 c) ∧ ∃ N,
    ∀ x ∈ RegionW q T m y0 a c S n N,
      (x ∉ AllCells q T m y0 fc a n → x ∈ V ∧ x ∉ EsetOF q T m y0 fc a p (n - 1)) ∧
      (x ∈ HolesW q T m y0 fc a p n → x ∉ gset q T (p n) (EsetOF q T m y0 fc a p (n - 2)) →
        x ∉ @closure _ τ V)

/-! ### 主定理（論文により近い読み方 FineP） -/

/-- **Prop 8.3 の反例（帯による構成、読み方 FineP）**。τ は「G が開、E₁ が閉、各 E(P) が開かつ閉」を満たす任意の位相、
選択関数 fc は任意の妥当なもの。 -/
theorem prop83_band_P [Countable α] [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m)
    {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} (hwfc : WeakFC q T fc) (hvfc : ValidFC q T fc)
    {a : ℕ → ℕ} (ha : StrictMono a) {p : ℕ → ℕ} (hp : AdmT m p)
    {cc : ℕ} (hcc : 0 < cc) (b : ℕ) (τ : TopologicalSpace (ℕ → α))
    (hG : @IsOpen _ τ (gcBox q T cc b y0))
    (hE1 : @IsClosed _ τ (EsetOF q T m y0 fc a p 1))
    (hEP : ∀ P, @IsOpen _ τ (EP q T m y0 fc a p P) ∧ @IsClosed _ τ (EP q T m y0 fc a p P)) :
    @IsOpen _ τ (VcexB q T m y0 τ fc a p cc b) ∧
    y0 ∈ VcexB q T m y0 τ fc a p cc b ∧
    gcBox q T cc b y0 \ EsetOF q T m y0 fc a p 2 ⊆ VcexB q T m y0 τ fc a p cc b ∧
    VcexB q T m y0 τ fc a p cc b ⊆ gcBox q T cc b y0 \ EsetOF q T m y0 fc a p 1 ∧
    ¬ FineP q T m y0 τ fc a p 3 (VcexB q T m y0 τ fc a p cc b) := by
  let _ := τ
  set E1 := EsetOF q T m y0 fc a p 1 with hE1def
  set E2 := EsetOF q T m y0 fc a p 2 with hE2def
  set G := gcBox q T cc b y0 with hGdef
  set F := Fband q T m y0 fc a p with hFdef
  set V := VcexB q T m y0 τ fc a p cc b with hVdef
  have hVe : V = (G \ E1) ∩ (closure F)ᶜ := rfl
  obtain ⟨hmono, hp15, hp0, hp12⟩ := id hp
  have hp23 : p 2 ≤ p 3 := hmono (by omega)
  have hE12 : E1 ⊆ E2 := EsetOF_sub_succ a p 1
  have hEP3 : EP q T m y0 fc a p (p 3) = E2 := EP_p3 a p
  have hFE2 : F ⊆ E2 := by
    intro z hz
    obtain ⟨i, hzi, -⟩ := Set.mem_iUnion.mp hz
    rw [← hEP3]
    have := Rb_ge ha p m i
    exact EP_anti hc hp (by omega) hzi
  have hE2c : IsClosed E2 := hEP3 ▸ (hEP (p 3)).2
  have hclF : closure F ⊆ E2 := closure_minimal hFE2 hE2c
  have hy0 : ∀ k, y0 ∉ EsetOF q T m y0 fc a p k := y0_not_mem_EsetOF hc hm hwfc a hp
  refine ⟨?_, ?_, ?_, Set.inter_subset_left, ?_⟩
  · rw [hVe, Set.sdiff_eq]
    exact (hG.inter hE1.isOpen_compl).inter isClosed_closure.isOpen_compl
  · exact ⟨⟨mem_gcBox_self hcc b y0, hy0 1⟩, fun h => hy0 2 (hclF h)⟩
  · rintro x ⟨hxG, hxE2⟩
    exact ⟨⟨hxG, fun h => hxE2 (hE12 h)⟩, fun h => hxE2 (hclF h)⟩
  · rintro ⟨n, hn1, hn3, c, S, hS, N, hfine⟩
    have hfine1 := fun x hx h => ((hfine x hx).1 h).1
    set i := N + c + lvl q b y0 + p 3 + 7 with hi
    have hRi := Rb_ge ha p m i
    have hRi1 := Rb_ge ha p m (i + 1)
    have hgap := Rb_gap ha p m i
    obtain rfl | rfl | rfl : n = 1 ∨ n = 2 ∨ n = 3 := by omega
    · -- n = 1: c_B ∈ D₁、K-trick の点は E₁ に入る
      set v := 2 * i + p 3 + 5 with hv
      have hav : m + v ≤ a (m + v) := ha.id_le _
      obtain ⟨pd⟩ := piece_builderG (y0 := y0) hc hm hvfc ha hS 1 v (by omega)
      have hcB := pd.hcB
      have hL5 : m + 5 ≤ a (m + v) + 1 := by omega
      have hcD : pd.cB ∈ D1OF q T m y0 fc a := by
        by_cases hal : S ∈ allowedO q T m y0 c (⋃ i ∈ Finset.range c, D1slabOF q T m y0 fc a i)
        · refine Set.mem_iUnion.mpr ⟨c, ?_⟩
          rw [D1slabOF_eq]
          refine Set.mem_iUnion₂.mpr ⟨S, hal, ?_⟩
          unfold holeBoxesUF
          simp only [Set.mem_iUnion, Set.mem_sUnion, exists_prop]
          exact ⟨_, ⟨pd.hpiece, Nat.zero_le _⟩, _, pd.hGd, mem_gfun q T _ _⟩
        · by_contra hnot
          apply hal
          refine ⟨hS, pd.cB, hcB.2.1.1.2, hcB.2.1.1.1, fun hpr => hnot ?_⟩
          obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.mp hpr
          exact Set.mem_iUnion.mpr ⟨j, hj⟩
      have hK : lvl q (p 1) pd.cB < lvl q (a (m + v) + 1) pd.cB :=
        lvl_lt_of_mem hc (by omega) (by omega) (mem_gfun q T _ _)
      obtain ⟨w, hw, hwB, hwk⟩ := ktrickG pd hc ha hm hK
      have hw0 : w ∈ EsetOF q T m y0 fc a p 0 := by
        rw [EsetOF_zero]
        exact Set.mem_iUnion₂.mpr ⟨pd.cB, hcD, gfun_mem_of_agree (mem_gfun q T _ _) hwk⟩
      exact bad_of_pd hc hwfc hS hfine1 pd (by omega) hL5 hw hwB
        (fun h => h.1.2 (EsetOF_sub_succ a p 0 hw0))
    · -- n = 2: K-trick の点は偶数の帯に入る
      set v := 2 * i + p 3 + 5 with hv
      have hav : m + v ≤ a (m + v) := ha.id_le _
      obtain ⟨pd⟩ := piece_builderG (y0 := y0) hc hm hvfc ha hS 2 v (by omega)
      have hcB := pd.hcB
      have hL5 : m + 5 ≤ a (m + v) + 1 := by omega
      have hR : Rb a p m i = a (m + v) := rfl
      have hcE1 : pd.cB ∈ E1 :=
        HkOF_sub_EsetOF_succ a p 0 c (mem_HkOF_of_allowed (k := 0) hS hcB.2.1.1.2 hcB.2.1.1.1
          (not_mem_gset_D1slabOF hc hwfc a (by omega) hS pd.hS2 (by rw [pd.hS2lab]; omega)
            hcB.2.1.1.2 hcB.2.1.2) pd.hpiece (show p 2 ≤ v by omega) pd.hGd
          (mem_gfun q T _ _) hcB.2)
      have hK : lvl q (a (m + v)) pd.cB < lvl q (a (m + v) + 1) pd.cB :=
        lvl_lt_of_mem hc (by omega) (by omega) (mem_gfun q T _ _)
      obtain ⟨w, hw, hwB, hwk⟩ := ktrickG pd hc ha hm hK
      have hwR : w ∈ gfun q T (a (m + v)) pd.cB := gfun_mem_of_agree (mem_gfun q T _ _) hwk
      by_cases hwE1 : w ∈ E1
      · exact bad_of_pd hc hwfc hS hfine1 pd (by omega) hL5 hw hwB (fun h => h.1.2 hwE1)
      have hws := slabO_hidx hw.2.1.1.1
      have hwF : w ∈ F := by
        refine Set.mem_iUnion.mpr ⟨i, ?_, ?_⟩
        · rw [EP_eq]
          have hmx : max (p 3) (Rb a p m i) = a (m + v) := by rw [hR]; exact max_eq_right (by omega)
          rw [hmx]
          exact Or.inl (Set.mem_iUnion₂.mpr ⟨pd.cB, hcE1, hwR⟩)
        · rw [EP_eq]
          rintro (h | h)
          · have hmx : max (p 3) (Rb a p m i + 1) = a (m + v) + 1 := by
              rw [hR]; exact max_eq_right (by omega)
            rw [hmx] at h
            obtain ⟨e, he, hwe⟩ := Set.mem_iUnion₂.mp h
            have hlvw : lvl q m w ≤ a (m + v) + 1 := by unfold lvl; rw [hws.1]; omega
            have hes := same_slab hc hm hlvw hwe
            replace he : e ∈ gset q T (p 2) (EsetOF q T m y0 fc a p 0) ∪ ⋃ c, HkOF q T m y0 fc a p 0 (EseqOF q T m y0 fc a p 0).2 c := he
            rcases he with he | he
            · obtain ⟨e0, he0, hee0⟩ := Set.mem_iUnion₂.mp he
              apply hwE1
              refine gset_sub_EsetOF_succ a p 0 (Set.mem_iUnion₂.mpr ⟨e0, he0, ?_⟩)
              exact gfun_trans hc (by omega) hee0 (gfun_anti hc (by omega) (by omega) e hwe)
            · obtain ⟨c', he'⟩ := Set.mem_iUnion.mp he
              have hec' := (slabO_hidx (HkOF_sub_slab he')).1
              have hcc' : c' = c := by rw [← hec', hes, hws.1]
              subst hcc'
              obtain ⟨S', Pv', B', hS', hP', -, hB', heB', heP'⟩ := mem_HkOF he'
              obtain ⟨S2', hS2', -, S3', hS3', -, hPe⟩ := id hP'
              have hwP' : w ∈ Pv'.1 := by
                rw [hPe] at heP' ⊢
                exact ⟨⟨⟨hw.2.1.1.1, mem_lncA_of_box hc (by omega) (by omega) hS' heP'.1.1.2 hwe⟩,
                  mem_lncA_of_box hc (by omega) (by omega) hS2' heP'.1.2 hwe⟩,
                  mem_lncA_of_box hc (by omega) (by omega) hS3' heP'.2 hwe⟩
              have hPP := piece_unique hc hS hS' pd.hpiece hP' hw.2 hwP'
              subst hPP
              exact not_mem_GdF_of_pdG pd hc hwfc hL5 hw hwB hB'
                (mem_GdF_of_box hc hwfc hL5 hB' heB' hwe)
          · obtain ⟨c', h'⟩ := Set.mem_iUnion.mp h
            exact not_mem_HkOF_of_pdG pd hc hwfc hS hL5 hw hwB _ _ _ c' h'
      exact bad_of_pd hc hwfc hS hfine1 pd (by omega) hL5 hw hwB
        (fun h => h.2 (subset_closure hwF))
    · -- n = 3: 穴 c_B は奇数の帯に入り、V に入る
      set v := Rb a p m i + 1 with hv
      have hav : m + v ≤ a (m + v) := ha.id_le _
      obtain ⟨pd⟩ := piece_builderG (y0 := y0) hc hm hvfc ha hS 3 v (by omega)
      have hcB := pd.hcB
      set L := a (m + v) + 1 with hLdef
      have hL5 : m + 5 ≤ L := by omega
      have hlvL : L < lvl q L pd.cB := by unfold lvl; omega
      have hcs := slabO_hidx hcB.2.1.1.1
      have hcase0 : pd.cB ∉ gset q T (p 2) (EsetOF q T m y0 fc a p 0) := by
        intro h
        obtain ⟨e0, he0, hce0⟩ := Set.mem_iUnion₂.mp h
        have hK : lvl q (p 2) e0 < lvl q L pd.cB := lvl_lt_of_mem hc (by omega) (by omega) hce0
        obtain ⟨w, hw, hwB, hwk⟩ := ktrickG pd hc ha hm hK
        have hwE : w ∈ E1 := gset_sub_EsetOF_succ a p 0
          (Set.mem_iUnion₂.mpr ⟨e0, he0, gfun_mem_of_agree hce0 hwk⟩)
        exact bad_of_pd hc hwfc hS hfine1 pd (by omega) hL5 hw hwB (fun h => h.1.2 hwE)
      have hcE1 : pd.cB ∉ E1 := by
        show pd.cB ∉ gset q T (p 2) (EsetOF q T m y0 fc a p 0) ∪ ⋃ c, HkOF q T m y0 fc a p 0 (EseqOF q T m y0 fc a p 0).2 c
        rintro (h | h)
        · exact hcase0 h
        · obtain ⟨c', h'⟩ := Set.mem_iUnion.mp h
          exact not_mem_HkOF_of_branch hc hS pd.hpiece hcB.2 a p 0 (by omega) _ c' h'
      have hnD : pd.cB ∉ (EseqOF q T m y0 fc a p 1).2 c := by
        show pd.cB ∉ gset q T (p 1) (D1slabOF q T m y0 fc a c) ∪
          gset q T (p 2) (HkOF q T m y0 fc a p 0 (EseqOF q T m y0 fc a p 0).2 c)
        rintro (h | h)
        · exact not_mem_gset_D1slabOF hc hwfc a (by omega) hS pd.hS2
            (by rw [pd.hS2lab]; omega) hcB.2.1.1.2 hcB.2.1.2 h
        · exact not_mem_gset_HkOF hc (by omega) hS pd.hS2 (by rw [pd.hS2lab]; omega) hcB.2.1.1.2
            hcB.2.1.2 h
      have hhole : ∀ u, u ∈ gfun q T L pd.cB → u ∈ slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3 →
          u ∈ HkOF q T m y0 fc a p 1 (EseqOF q T m y0 fc a p 1).2 c := fun u huB huP =>
        mem_HkOF_of_allowed (k := 1) hS hcB.2.1.1.2 hcB.2.1.1.1 hnD pd.hpiece
          (show p 3 ≤ v by omega) pd.hGd huB huP
      by_cases hA : pd.cB ∈ gset q T (p 3) E1
      · -- c_B ∈ g[p₃, E₁]: 論文の穴でない。K-trick の点は E₂ に入る
        obtain ⟨e, he, hce⟩ := Set.mem_iUnion₂.mp hA
        have hK : lvl q (p 3) e < lvl q L pd.cB := lvl_lt_of_mem hc (by omega) (by omega) hce
        obtain ⟨w, hw, hwB, hwk⟩ := ktrickG pd hc ha hm hK
        have hwE2 : w ∈ E2 := gset_sub_EsetOF_succ a p 1
          (Set.mem_iUnion₂.mpr ⟨e, he, gfun_mem_of_agree hce hwk⟩)
        exact ((hfine w (mem_RegionW_of_pdG pd (by omega) hw)).1
          (not_mem_AllCells_of_pdG pd hc hwfc hS hL5 hw hwB 3)).2 hwE2
      by_cases hcG : pd.cB ∈ G
      · set O := EP q T m y0 fc a p (Rb a p m i + 1) ∩ (EP q T m y0 fc a p (Rb a p m (i + 1)))ᶜ
          with hO
        have hOo : IsOpen O := (hEP _).1.inter (hEP _).2.isOpen_compl
        have hcO : pd.cB ∈ O := by
          constructor
          · rw [EP_eq]
            refine Or.inr (Set.mem_iUnion.mpr ⟨c, ?_⟩)
            exact mem_HkOF_of_allowed (k := 1) hS hcB.2.1.1.2 hcB.2.1.1.1 hnD pd.hpiece
              (show pP p (Rb a p m i + 1) 3 ≤ v by rw [pP_3]; omega) pd.hGd (mem_gfun q T _ _)
              hcB.2
          · rw [EP_eq]
            rintro (h | h)
            · have hmx : max (p 3) (Rb a p m (i + 1)) = Rb a p m (i + 1) := max_eq_right (by omega)
              rw [hmx] at h
              obtain ⟨e, he, hce⟩ := Set.mem_iUnion₂.mp h
              have hlvc : lvl q m pd.cB ≤ Rb a p m (i + 1) := by unfold lvl; rw [hcs.1]; omega
              have hes := same_slab hc hm hlvc hce
              replace he : e ∈ gset q T (p 2) (EsetOF q T m y0 fc a p 0) ∪ ⋃ c, HkOF q T m y0 fc a p 0 (EseqOF q T m y0 fc a p 0).2 c := he
              rcases he with he | he
              · obtain ⟨e0, he0, hee0⟩ := Set.mem_iUnion₂.mp he
                exact hcase0 (Set.mem_iUnion₂.mpr ⟨e0, he0,
                  gfun_trans hc (by omega) hee0 (gfun_anti hc (by omega) (by omega) e hce)⟩)
              · obtain ⟨c', he'⟩ := Set.mem_iUnion.mp he
                have hec' := (slabO_hidx (HkOF_sub_slab he')).1
                have hcc' : c' = c := by rw [← hec', hes, hcs.1]
                subst hcc'
                exact not_mem_gset_HkOF hc (by omega) hS pd.hS2 (by rw [pd.hS2lab]; omega)
                  hcB.2.1.1.2 hcB.2.1.2 (Set.mem_iUnion₂.mpr ⟨e, he', hce⟩)
            · obtain ⟨c', h'⟩ := Set.mem_iUnion.mp h
              obtain ⟨S', Pv', B', hS', hP', hidx', -, -, hcP'⟩ := mem_HkOF h'
              have hPP := piece_unique hc hS hS' pd.hpiece hP' hcB.2 hcP'
              subst hPP
              have : pP p (Rb a p m (i + 1)) 3 ≤ v := hidx'
              rw [pP_3] at this
              omega
        have hFO : F ⊆ Oᶜ := by
          intro z hz hzO
          obtain ⟨j, hzj, hzj1⟩ := Set.mem_iUnion.mp hz
          rcases le_or_gt j i with hji | hji
          · have := Rb_mono ha p m hji
            exact hzj1 (EP_anti hc hp (by omega) hzO.1)
          · exact hzO.2 (EP_anti hc hp (Rb_mono ha p m (by omega)) hzj)
        have hcF : pd.cB ∉ closure F := fun h => (closure_minimal hFO hOo.isClosed_compl h) hcO
        have hcV : pd.cB ∈ V := ⟨⟨hcG, hcE1⟩, hcF⟩
        have hcH : pd.cB ∈ HolesW q T m y0 fc a p 3 := by
          unfold HolesW
          rw [ite_eq_right (show (3:ℕ) ≠ 1 by omega)]
          exact Set.mem_iUnion.mpr ⟨c, hhole _ (mem_gfun q T _ _) hcB.2⟩
        exact (hfine _ (mem_RegionW_of_pdG pd (by omega) hcB)).2 hcH hA (subset_closure hcV)
      · -- c_B ∉ G: K-trick で G の外の穴でない点
        have hK : lvl q b y0 < lvl q L pd.cB := by omega
        obtain ⟨w, hw, hwB, hwk⟩ := ktrickG pd hc ha hm hK
        refine bad_of_pd hc hwfc hS hfine1 pd (by omega) hL5 hw hwB (fun hwV => hcG ?_)
        exact mem_gcBox_of_agree hwV.1.1 (fun k hk => (hwk k hk).symm)

/-! ### 系: D_0043 型の τ、論文の字義どおりの τ、論文の Δ-order（firstC） -/

variable (q T m y0) in
/-- **論文の字義どおりの τ** の部分基: Definition C の集合 g[p_h, g(ℓ,x) − E] は中心 x ∉ E のときだけ。 -/
noncomputable def tauSubLit (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) (A : Set (ℕ → ℕ)) :
    Set (Set (ℕ → α)) :=
  rhoSub q T ∪
  {s | ∃ a ∈ A, ∃ p, AdmT m p ∧ ∃ k,
      s = EsetOF q T m y0 fc a p (k + 1) ∨ s = (EsetOF q T m y0 fc a p (k + 1))ᶜ} ∪
  {s | ∃ a ∈ A, ∃ p, AdmT m p ∧ ∃ k ℓ ph x, m + 5 < ℓ ∧ p (k + 2) < ph ∧
      x ∉ EsetOF q T m y0 fc a p (k + 1) ∧
      (s = gset q T ph (gfun q T ℓ x \ EsetOF q T m y0 fc a p (k + 1)) ∨
       s = (gset q T ph (gfun q T ℓ x \ EsetOF q T m y0 fc a p (k + 1)))ᶜ)}

variable (q T m y0) in
/-- 論文の字義どおりの τ。 -/
noncomputable def tauLit (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) (A : Set (ℕ → ℕ)) :
    TopologicalSpace (ℕ → α) :=
  .generateFrom (tauSubLit q T m y0 fc A)

theorem isOpen_tauLit_of_mem {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} {A : Set (ℕ → ℕ)}
    {s : Set (ℕ → α)} (hs : s ∈ tauSubLit q T m y0 fc A) :
    @IsOpen _ (tauLit q T m y0 fc A) s :=
  TopologicalSpace.GenerateOpen.basic _ hs

theorem isOpen_tauLit_of_ptop [NoMaxOrder α] (hc : Compat2 q T)
    {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} {A : Set (ℕ → ℕ)} {U : Set (ℕ → α)}
    (hU : @IsOpen _ (ptop α) U) : @IsOpen _ (tauLit q T m y0 fc A) U := by
  let _ := tauLit q T m y0 fc A
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨n0, hn0⟩ := prop_3_4_eventually hc x U hU hx
  exact ⟨gfun q T (n0 + 1) x, hn0 _ (by omega),
    isOpen_tauLit_of_mem (Or.inl (Or.inl ⟨n0 + 1, x, by omega, Or.inl rfl⟩)), mem_gfun q T _ x⟩

/-- 字義どおりの τ は D_0043 型の τ より粗い（部分基が含まれる）。 -/
theorem tauSubLit_sub (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) (A : Set (ℕ → ℕ)) :
    tauSubLit q T m y0 fc A ⊆ tauSubTF q T m y0 fc A := by
  rintro s ((h | h) | ⟨a, ha, p, hp, k, ℓ, ph, x, h1, h2, -, h3⟩)
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr ⟨a, ha, p, hp, k, ℓ, ph, x, h1, h2, h3⟩

/-- E(α, p, k+1)（p 許容）は τ の部分基で開かつ閉になる、という性質から帯の仮定を作る。 -/
theorem band_hyps_of_sub
    {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} {a : ℕ → ℕ}
    {p : ℕ → ℕ} (hp : AdmT m p) (τ : TopologicalSpace (ℕ → α))
    (hρ : ∀ U, @IsOpen _ (ptop α) U → @IsOpen _ τ U)
    (hE : ∀ p', AdmT m p' → ∀ k, @IsOpen _ τ (EsetOF q T m y0 fc a p' (k + 1)) ∧
      @IsOpen _ τ (EsetOF q T m y0 fc a p' (k + 1))ᶜ) (cc b : ℕ) :
    @IsOpen _ τ (gcBox q T cc b y0) ∧ @IsClosed _ τ (EsetOF q T m y0 fc a p 1) ∧
    ∀ P, @IsOpen _ τ (EP q T m y0 fc a p P) ∧ @IsClosed _ τ (EP q T m y0 fc a p P) :=
  ⟨hρ _ (gcBox_isOpen_p cc b y0), ⟨(hE p hp 0).2⟩,
    fun P => ⟨(hE (pP p P) (admT_pP hp P) 1).1, ⟨(hE (pP p P) (admT_pP hp P) 1).2⟩⟩⟩

/-- **系（論文の字義どおりの τ）**: どの妥当な Δ-order でも、Prop 8.3 は偽。 -/
theorem prop83_false_tauLit [Countable α] [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m)
    {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} (hwfc : WeakFC q T fc) (hvfc : ValidFC q T fc)
    {A : Set (ℕ → ℕ)} {a : ℕ → ℕ} (haA : a ∈ A) (ha : StrictMono a) {p : ℕ → ℕ}
    (hp : AdmT m p) {cc : ℕ} (hcc : 0 < cc) (b : ℕ) :
    let τ := tauLit q T m y0 fc A
    let V := VcexB q T m y0 τ fc a p cc b
    @IsOpen _ τ V ∧ y0 ∈ V ∧
    gcBox q T cc b y0 \ EsetOF q T m y0 fc a p 2 ⊆ V ∧
    V ⊆ gcBox q T cc b y0 \ EsetOF q T m y0 fc a p 1 ∧
    ¬ FineST q T m y0 τ fc a p 3 V ∧ ¬ FineP q T m y0 τ fc a p 3 V := by
  intro τ V
  obtain ⟨hG, hE1, hEP⟩ := band_hyps_of_sub (y0 := y0) hp τ
    (fun U hU => isOpen_tauLit_of_ptop hc hU)
    (fun p' hp' k => ⟨isOpen_tauLit_of_mem (Or.inl (Or.inr ⟨a, haA, p', hp', k, Or.inl rfl⟩)),
      isOpen_tauLit_of_mem (Or.inl (Or.inr ⟨a, haA, p', hp', k, Or.inr rfl⟩))⟩) cc b
  obtain ⟨h1, h2, h3, h4, h5⟩ := prop83_band hc hm hwfc hvfc ha hp hcc b τ hG hE1 hEP
  exact ⟨h1, h2, h3, h4, h5, (prop83_band_P hc hm hwfc hvfc ha hp hcc b τ hG hE1 hEP).2.2.2.2⟩

/-- **系（D_0043 型の τ、読み方 FineS）**: どの妥当な Δ-order でも、Prop 8.3 は偽。 -/
theorem prop83_false_tauTF [Countable α] [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m)
    {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} (hwfc : WeakFC q T fc) (hvfc : ValidFC q T fc)
    {A : Set (ℕ → ℕ)} {a : ℕ → ℕ} (haA : a ∈ A) (ha : StrictMono a) {p : ℕ → ℕ}
    (hp : AdmT m p) {cc : ℕ} (hcc : 0 < cc) (b : ℕ) :
    let τ := tauTF q T m y0 fc A
    let V := VcexB q T m y0 τ fc a p cc b
    @IsOpen _ τ V ∧ y0 ∈ V ∧
    gcBox q T cc b y0 \ EsetOF q T m y0 fc a p 2 ⊆ V ∧
    V ⊆ gcBox q T cc b y0 \ EsetOF q T m y0 fc a p 1 ∧
    ¬ FineS q T m y0 fc A a p 3 V ∧ ¬ FineP q T m y0 τ fc a p 3 V := by
  intro τ V
  obtain ⟨hG, hE1, hEP⟩ := band_hyps_of_sub (y0 := y0) hp τ
    (fun U hU => isOpen_tauF_of_ptop hc hU)
    (fun p' hp' k => ⟨isOpen_tauF_of_mem (Or.inl (Or.inr ⟨a, haA, p', hp', k, Or.inl rfl⟩)),
      isOpen_tauF_of_mem (Or.inl (Or.inr ⟨a, haA, p', hp', k, Or.inr rfl⟩))⟩) cc b
  obtain ⟨h1, h2, h3, h4, h5⟩ := prop83_band hc hm hwfc hvfc ha hp hcc b τ hG hE1 hEP
  exact ⟨h1, h2, h3, h4, h5, (prop83_band_P hc hm hwfc hvfc ha hp hcc b τ hG hE1 hEP).2.2.2.2⟩

theorem weakFC_firstC : WeakFC q T (firstC q T) := by
  intro n A
  classical
  unfold firstC
  split_ifs with h
  · exact Or.inr (unlab_mem _ h 0)
  · exact Or.inl rfl

/-- **系（論文の Δ-order = 固定した列挙 lab の先頭 firstC、字義どおりの τ）**。 -/
theorem prop83_false_tauLit_firstC [Countable α] [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m)
    {A : Set (ℕ → ℕ)} {a : ℕ → ℕ} (haA : a ∈ A) (ha : StrictMono a) {p : ℕ → ℕ}
    (hp : AdmT m p) {cc : ℕ} (hcc : 0 < cc) (b : ℕ) :
    let τ := tauLit q T m y0 (firstC q T) A
    let V := VcexB q T m y0 τ (firstC q T) a p cc b
    @IsOpen _ τ V ∧ y0 ∈ V ∧
    gcBox q T cc b y0 \ EsetO q T m y0 a p 2 ⊆ V ∧
    V ⊆ gcBox q T cc b y0 \ EsetO q T m y0 a p 1 ∧
    ¬ FineST q T m y0 τ (firstC q T) a p 3 V ∧ ¬ FineP q T m y0 τ (firstC q T) a p 3 V := by
  intro τ V
  have h := prop83_false_tauLit (y0 := y0) hc hm weakFC_firstC (validFC_firstC q T) haA ha hp
    hcc b
  dsimp only at h
  rw [← EsetOF_firstC]
  exact h

/-- **系（D_0043 の τ そのもの・固定した列挙 firstC）**: D_0043 の `tauT` で Prop 8.3 は偽。 -/
theorem prop83_false_tauT [Countable α] [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m)
    {A : Set (ℕ → ℕ)} {a : ℕ → ℕ} (haA : a ∈ A) (ha : StrictMono a) {p : ℕ → ℕ}
    (hp : AdmT m p) {cc : ℕ} (hcc : 0 < cc) (b : ℕ) :
    let τ := tauT q T m y0 A
    let V := VcexB q T m y0 τ (firstC q T) a p cc b
    @IsOpen _ τ V ∧ y0 ∈ V ∧
    gcBox q T cc b y0 \ EsetO q T m y0 a p 2 ⊆ V ∧
    V ⊆ gcBox q T cc b y0 \ EsetO q T m y0 a p 1 ∧
    ¬ FineST q T m y0 τ (firstC q T) a p 3 V ∧ ¬ FineP q T m y0 τ (firstC q T) a p 3 V := by
  intro τ V
  have h := prop83_false_tauTF (y0 := y0) hc hm weakFC_firstC (validFC_firstC q T) haA ha hp
    hcc b
  dsimp only at h
  rw [fineS_iff_fineST, tauTF_firstC] at h
  rw [← EsetOF_firstC]
  exact h

/-- **具体例**: D_0028 の具体的なモデル（Node, T, q）、m = 1、α = id、p = (1, 7, 7, …)、
論文の Δ-order（固定した列挙の先頭 firstC）、論文の字義どおりの τ。V は Prop 8.3 の仮定を満たすが fine でない。 -/
theorem prop83_false_concrete (A : Set (ℕ → ℕ)) (haA : (fun i => i) ∈ A)
    (y0 : ℕ → Defs.D_0028.Node) (b : ℕ) :
    let p : ℕ → ℕ := fun j => if j = 0 then 1 else 7
    let q := Defs.D_0028.q
    let T := Defs.D_0028.T
    let τ := tauLit q T 1 y0 (firstC q T) A
    let V := VcexB q T 1 y0 τ (firstC q T) (fun i => i) p 1 b
    AdmT 1 p ∧ @IsOpen _ τ V ∧ y0 ∈ V ∧
    gcBox q T 1 b y0 \ EsetO q T 1 y0 (fun i => i) p 2 ⊆ V ∧
    V ⊆ gcBox q T 1 b y0 \ EsetO q T 1 y0 (fun i => i) p 1 ∧
    ¬ FineST q T 1 y0 τ (firstC q T) (fun i => i) p 3 V ∧
    ¬ FineP q T 1 y0 τ (firstC q T) (fun i => i) p 3 V := by
  intro p q T τ V
  have : Countable Defs.D_0028.Node := Defs.D_0028.q.symm.injective.countable
  have hp : AdmT 1 p := by
    refine ⟨fun i j hij => ?_, ?_, ?_, ?_⟩
    · have : i ≤ j := hij
      show (if i = 0 then 1 else 7) ≤ (if j = 0 then 1 else 7)
      split_ifs <;> omega
    all_goals simp [p]
  exact ⟨hp, prop83_false_tauLit_firstC (m := 1) (y0 := y0) Defs.D_0028.compat2 Nat.one_pos haA
    (fun _ _ h => h) hp one_pos b⟩

end Defs.D_0075
