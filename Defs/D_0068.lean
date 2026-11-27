import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0067
import Defs.D_0050

namespace Defs.D_0068

/-!
**宣言された閉包の反例の本体**（一般化版、選択関数 `fcAdv q T p₁ m`）。

穴の点 z の性質を仮定として、z ∉ Cl_τ g[p₂, E(α, p, 0)] を示す（`not_mem_closure_cex`）。
z が E(α, p, 1) の点なら、宣言された閉包（k = 0）が破れる（`not_declaredClosureF_of_hole`）。
仮定:
* z は shift0 y₀ J の slab の元 S* = g(m+1, shift0 y₀ J) の点で、S* の branch 番号 ≠ 1 の元 S2 に入る。
* z ∉ HkO(p′)（p′₁ = p′₂ = p₁+1。z の piece 番号が p₁ なので成り立つ）。
* g(ℓ, z) の点で z と先頭 m 座標が一致するものは E(α, p, 1) に入る（z の穴の箱の中）。
* α の値は p₁ を取らない（L = p₁ + 1 の箱がない）。
近傍 U = g(ℓ, z) − E(α, p′, 1) − g[p₁+1, g(ℓ, z) − E(α, p, 1)]。D の極大な p₁-箱 M ごとに、
層 L ≤ p₁ なら M ⊆ D ⊆ E(α, p′, 1)、L ≥ p₁+2 なら深い元の相棒 u（`Defs.D_0064.companion_of_deep`）で
M ⊆ g[p₁+1, g(ℓ, z) − E(α, p, 1)]。u ∉ E は相棒の補題（`Defs.D_0063`）と branch の分離から、
u ∈ g(ℓ, z) は ZZ と、中心 c が z の slab の外にあること（LOC の帰結）から従う。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0034 Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0040 Defs.D_0043
  Defs.D_0050 Defs.D_0060 Defs.D_0062 Defs.D_0063 Defs.D_0064 Defs.D_0065 Defs.D_0066 Defs.D_0067

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

theorem slabO_hidx {c : ℕ} {x : ℕ → α} (h : x ∈ slabO q T m y0 c) :
    hidx q m x = c ∧ c ≠ hidx q m y0 := by
  classical
  unfold slabO at h
  split_ifs at h with hc
  · exact absurd h (Set.notMem_empty _)
  · exact ⟨h.1, hc⟩

theorem slabO_sub_Gm {c : ℕ} : slabO q T m y0 c ⊆ gfun q T m y0 := by
  classical
  intro x h
  unfold slabO at h
  split_ifs at h
  · exact absurd h (Set.notMem_empty _)
  · exact h.2

/-- y₀ は O の点を中心とする箱の点の箱に入らない。 -/
theorem y0_not_mem_box (hc : Compat2 q T) (hm : 0 < m) {c L n : ℕ} (hL : m ≤ L) (hn : m ≤ n)
    {u d : ℕ → α} (hu : u ∈ slabO q T m y0 c) (hd : d ∈ gfun q T L u) :
    y0 ∉ gfun q T n d := by
  intro hy
  have huG := slabO_sub_Gm hu
  have hdG : d ∈ gfun q T m y0 := gfun_trans hc hm huG (gfun_anti hc hm hL u hd)
  have hdk : ∀ k < m, d k = y0 k := fun k hk =>
    le_antisymm (hy.1 k (by omega)).1 (hdG.1 k hk).1
  have huk : ∀ k < m, u k = y0 k := fun k hk =>
    le_antisymm (hdk k hk ▸ (hd.1 k (by omega)).1) (huG.1 k hk).1
  have : hidx q m u = hidx q m y0 :=
    (code_eq_iff m hm _ _).2 (fun k hk => by show q.symm (u k) = q.symm (y0 k); rw [huk k hk])
  exact (slabO_hidx hu).2 ((slabO_hidx hu).1.symm.trans this)

/-- D の点の箱の出自（slab c の D に含まれる）。 -/
theorem mem_D1OF_box' {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} {a : ℕ → ℕ} {d : ℕ → α}
    (hd : d ∈ D1OF q T m y0 fc a) :
    ∃ c S Pv B, S ∈ allowedO q T m y0 c (⋃ i ∈ Finset.range c, D1slabOF q T m y0 fc a i) ∧
      Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) 1 ∧ B ∈ GdF q T m fc a Pv.1 Pv.2 ∧
      d ∈ B ∧ B ⊆ D1slabOF q T m y0 fc a c := by
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hd
  rw [D1slabOF_eq] at hc
  obtain ⟨S, hS, hdS⟩ := Set.mem_iUnion₂.mp hc
  unfold holeBoxesUF at hdS
  obtain ⟨Pv, hPv, B, hB, hdB⟩ := by
    simpa only [Set.mem_iUnion, Set.mem_sUnion, exists_prop] using hdS
  refine ⟨c, S, Pv, B, hS, hPv.1, hB, hdB, fun w hw => ?_⟩
  rw [D1slabOF_eq]
  refine Set.mem_iUnion₂.mpr ⟨S, hS, ?_⟩
  unfold holeBoxesUF
  simp only [Set.mem_iUnion, Set.mem_sUnion, exists_prop]
  exact ⟨Pv, hPv, B, hB, hw⟩

theorem D1slabOF_sub {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)} (a : ℕ → ℕ) (c : ℕ) :
    D1slabOF q T m y0 fc a c ⊆ D1OF q T m y0 fc a := Set.subset_iUnion _ c

section main

variable [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m) {p1 : ℕ}
include hc hm

/-- shift0 y₀ J の slab の branch ≠ 1 の点 z は g[n, D] に入らない（n ≥ m+2）。 -/
theorem z_not_mem_gsetD1 {J : ℕ} (hJ0 : 0 < J) (hJ : ∀ k, 0 < k → k < m → q.symm (y0 k) < J)
    {a : ℕ → ℕ} {cz : ℕ} {S S2 : Set (ℕ → α)} {z : ℕ → α}
    (hSe : S = gfun q T (m + 1) (shift0 T y0 J))
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 cz))
    (hS2 : S2 ∈ lncA q T (m + 2) (slabO q T m y0 cz ∩ S))
    (hlab : lab (lncA q T (m + 2) (slabO q T m y0 cz ∩ S)) S2 ≠ 1)
    (hzs : ∀ k < m, z k = shift0 T y0 J k) (hzc : z ∈ slabO q T m y0 cz)
    (hzS : z ∈ S) (hzS2 : z ∈ S2) {n : ℕ} (hn : m + 2 ≤ n) :
    z ∉ gset q T n (D1OF q T m y0 (fcAdv q T p1 m) a) := by
  intro hz
  obtain ⟨d, hdD, hzd⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨cB, SB, Pv, B, hSBa, hPv, hB, hdB, hBsub⟩ := mem_D1OF_box' hdD
  rcases GdF_rep (weakFC_fcAdv p1 m) hB with he | ⟨L, u, hL, huP, rfl⟩
  · rw [he] at hdB; exact absurd hdB (Set.notMem_empty _)
  have huslab : u ∈ slabO q T m y0 cB := by
    obtain ⟨S2', -, -, S3', -, -, hPe⟩ := hPv
    rw [hPe] at huP; exact huP.1.1.1
  rcases loc hc hm (show m ≤ n by omega) hJ0 hJ (hSe ▸ hzS) hzs hzd with hy | hds
  · exact y0_not_mem_box hc hm (by omega) (by omega) huslab hdB hy
  · -- d は z の slab（S の中）
    have hdc : d ∈ slabO q T m y0 cz := by
      have hdG : d ∈ gfun q T m y0 :=
        gfun_trans hc hm (slabO_sub_Gm huslab) (gfun_anti hc hm (by omega) u hdB)
      have hh : hidx q m d = hidx q m z :=
        (code_eq_iff m hm _ _).2 (fun k hk => by
          show q.symm (d k) = q.symm (z k); rw [hds k hk, hzs k hk])
      have hcz := slabO_hidx hzc
      classical
      unfold slabO; rw [if_neg hcz.2]
      exact ⟨hh.trans hcz.1, hdG⟩
    obtain ⟨hSd, hdSd⟩ := lncA_mem_spec hc (sub_gset (q := q) (T := T) (m + 1) _ hdc)
    have hzSd : z ∈ lncA_mem q T (m + 1) (slabO q T m y0 cz) d :=
      lncA_absorb hc hSd hdc ⟨d, mem_gfun q T _ d, hdSd⟩
        ((gfun_anti hc (by omega) (show m + 1 ≤ n by omega) d) hzd)
    have hSeq := lncA_unique hc hSd hS hzSd hzS
    have hdS : d ∈ S := hSeq ▸ hdSd
    rcases loc hc hm (show m ≤ L by omega) hJ0 hJ (hSe ▸ hdS) hds hdB with hy | hus
    · exact y0_not_mem_box hc hm (L := L) (n := L) (by omega) (by omega) huslab (mem_gfun q T L u) hy
    · have hcB : cB = cz := by
        have h1 := (slabO_hidx huslab).1
        have h2 : hidx q m u = hidx q m z :=
          (code_eq_iff m hm _ _).2 (fun k hk => by
            show q.symm (u k) = q.symm (z k); rw [hus k hk, hzs k hk])
        exact h1.symm.trans (h2.trans (slabO_hidx hzc).1)
      subst hcB
      exact not_mem_gset_D1slabOF hc (weakFC_fcAdv p1 m) a hn hS hS2 hlab hzS hzS2
        (Set.mem_biUnion (hBsub hdB) hzd)

/-- 極大な p₁-箱ごとの切り離し。 -/
theorem kill_max_cex {J : ℕ} (hJ0 : 0 < J) (hJ : ∀ k, 0 < k → k < m → q.symm (y0 k) < J)
    {a : ℕ → ℕ} (hgap : ∀ v, a (m + v) ≠ p1) {cz : ℕ} {S S2 : Set (ℕ → α)} {z : ℕ → α}
    (hSe : S = gfun q T (m + 1) (shift0 T y0 J))
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 cz))
    (hS2 : S2 ∈ lncA q T (m + 2) (slabO q T m y0 cz ∩ S))
    (hlab : lab (lncA q T (m + 2) (slabO q T m y0 cz ∩ S)) S2 ≠ 1)
    (hzs : ∀ k < m, z k = shift0 T y0 J k) (hzc : z ∈ slabO q T m y0 cz)
    (hzS : z ∈ S) (hzS2 : z ∈ S2) {p p' : ℕ → ℕ} (hp : AdmT m p) (hp1 : p 1 = p1)
    {ℓ : ℕ} (hℓ : m + 2 ≤ ℓ)
    {M : Set (ℕ → α)} (hM : M ∈ lncA q T p1 (D1OF q T m y0 (fcAdv q T p1 m) a))
    {w : ℕ → α} (hwM : w ∈ M) (hwz : w ∈ gfun q T ℓ z) :
    w ∈ EsetOF q T m y0 (fcAdv q T p1 m) a p' 1 ∨
      w ∈ gset q T (p1 + 1) (gfun q T ℓ z \ EsetOF q T m y0 (fcAdv q T p1 m) a p 1) := by
  set fc := fcAdv q T p1 m with hfcdef
  have hp15 : m + 5 < p1 := hp1 ▸ hp.2.1
  have hp1pos : 0 < p1 := by omega
  have hznot : z ∉ gset q T p1 (D1OF q T m y0 fc a) :=
    z_not_mem_gsetD1 hc hm hJ0 hJ hSe hS hS2 hlab hzs hzc hzS hzS2 (by omega)
  obtain ⟨d0, hd0, hMe, hmax⟩ := id hM
  obtain ⟨cB, SB, Pv, B, hSBa, hPv, hB, hd0B, hBsub⟩ := mem_D1OF_box' hd0
  have hSB : SB ∈ lncA q T (m + 1) (slabO q T m y0 cB) := hSBa.1
  have hBD : B ⊆ D1OF q T m y0 fc a := hBsub.trans (D1slabOF_sub a cB)
  -- 箱が lncA の元（L ≤ p₁）なら殻で切り離す
  have shell : ∀ L u, 0 < L → B = gfun q T L u → L ≤ p1 →
      w ∈ EsetOF q T m y0 fc a p' 1 := by
    intro L u hL0 hBe hL
    refine D1OF_sub_EsetOF a p' 1 (hBD ?_)
    rw [hBe] at hd0B ⊢
    have := hMe ▸ hwM
    exact gfun_trans hc hL0 hd0B (gfun_anti hc hL0 hL d0 this)
  rcases GdF_cases hB with ⟨hlev, S0, hS0, hBe⟩ | hch
  · set L := a (m + Pv.2) + 1 with hLdef
    by_cases hL : L ≤ p1
    · rcases weakFC_fcAdv p1 m L (S0 ∩ Pv.1) with h | h
      · have hB0 : B = ∅ := hBe.trans h
        rw [hB0] at hd0B; exact absurd hd0B (Set.notMem_empty _)
      · obtain ⟨u, -, hue, -⟩ := h
        exact Or.inl (shell L u (by omega) (hBe.trans hue) hL)
    · have hL2 : p1 + 2 ≤ L := by
        have := hgap Pv.2; omega
      obtain ⟨S2B, hS2B, hlabB, S3B, hS3B, hv, hPe⟩ := id hPv
      have hNL : 0 < L - 1 := by omega
      have hshift : ShiftOK q T (S0 ∩ Pv.1) (L - 1) m := by
        refine ShiftOK_inter (ShiftOK_lncA hc (n := a (m + Pv.2)) (by omega) (by omega) hS0) ?_
        rw [hPe]
        refine ShiftOK_inter (ShiftOK_inter (ShiftOK_inter
          (ShiftOK_slabO hc hm (by omega) le_rfl y0 cB)
          (ShiftOK_lncA hc (by omega) (by omega) hSB))
          (ShiftOK_lncA hc (by omega) (by omega) hS2B))
          (ShiftOK_lncA hc (by omega) (by omega) hS3B)
      have hmix : MixOK (S0 ∩ Pv.1) m := by
        refine MixOK_inter (MixOK_lncA hS0 m) ?_
        rw [hPe]
        exact MixOK_inter (MixOK_inter (MixOK_inter (MixOK_slabO hm le_rfl cB)
          (MixOK_lncA hSB m)) (MixOK_lncA hS2B m)) (MixOK_lncA hS3B m)
      have hAne : (S0 ∩ Pv.1).Nonempty := by
        obtain ⟨x0, hx0, hS0e, -⟩ := hS0
        exact ⟨x0, hS0e ▸ mem_gfun q T _ x0, hx0⟩
      obtain ⟨c, y, hfcc, hcA, hyA, -, hck0, hcy, -⟩ :=
        fcAdv_deep hc hL2 hAne hshift (show m < L by omega)
      have hBc : B = gfun q T L c := hBe.trans hfcc
      have hcD : c ∈ D1OF q T m y0 fc a := hBD (hBc ▸ mem_gfun q T L c)
      -- M = g(p₁, c)
      have hMc : M = gfun q T p1 c := by
        have hd0c : d0 ∈ gfun q T L c := hBc ▸ hd0B
        have h1 : gfun q T p1 d0 ⊆ gfun q T p1 c :=
          gfun_trans hc hp1pos (gfun_anti hc hp1pos (by omega) c hd0c)
        exact (hmax c hcD (hMe ▸ h1)).symm
      obtain ⟨hcu, hlvu, huM⟩ := companion_of_deep hc (k0 := m) (n := L) (p := p1) (ph := p1 + 1)
        (by omega) (by omega) (by omega) hck0 hcy
      set u := Function.update c m (y m) with hudef
      have huA : u ∈ S0 ∩ Pv.1 := hmix c hcA y hyA
      right
      have hMu : M ⊆ gfun q T (p1 + 1) u := hMc ▸ gfun_sub_coarse hc hcu hlvu
      refine Set.mem_biUnion (x := u) ⟨?_, ?_⟩ (hMu hwM)
      · -- u ∈ g(ℓ, z)
        have hzM : z ∉ M := fun h => hznot (lncA_sub_gset hM h)
        have hwc : w ∈ gfun q T p1 c := hMc ▸ hwM
        have hlt : lvl q ℓ z < lvl q p1 c := by
          by_contra h
          exact hzM (hMc ▸ center_mem_coarse hc hwz hwc (not_lt.mp h))
        have hcz : c ∈ gfun q T ℓ z := center_mem_coarse hc hwc hwz hlt.le
        have hk : ∃ k < m, c k ≠ z k := by
          by_contra hall
          push Not at hall
          have hcslab : hidx q m c = hidx q m z :=
            (code_eq_iff m hm _ _).2 (fun k hk => by
              show q.symm (c k) = q.symm (z k); rw [hall k hk])
          have hcP : c ∈ Pv.1 := hcA.2
          rw [hPe] at hcP
          have hcB : cB = cz := ((slabO_hidx hcP.1.1.1).1.symm.trans hcslab).trans
            (slabO_hidx hzc).1
          subst hcB
          have hcS : c ∈ S := by
            have : gfun q T ℓ z ⊆ S := by
              rw [hSe]
              exact (gfun_anti hc (by omega) (show m + 1 ≤ ℓ by omega) z).trans
                (gfun_trans hc (by omega) (hSe ▸ hzS))
            exact this hcz
          have hSS : SB = S := lncA_unique hc hSB hS hcP.1.1.2 hcS
          subst hSS
          have hcS2 : c ∈ S2 := by
            obtain ⟨x2, -, hx2, -⟩ := id hS2
            have : gfun q T ℓ z ⊆ S2 := by
              rw [hx2]
              exact (gfun_anti hc (by omega) (show m + 2 ≤ ℓ by omega) z).trans
                (gfun_trans hc (by omega) (hx2 ▸ hzS2))
            exact this hcz
          have h22 : S2B = S2 := lncA_unique hc hS2B hS2 hcP.1.2 hcS2
          subst h22
          exact hlab hlabB
        obtain ⟨k, hkm, hck⟩ := hk
        have hck' : c k ∈ Set.Ico (z k) (T.child (z k) (lvl q ℓ z)) := hcz.1 k (by omega)
        have hlt2 : z k < c k := lt_of_le_of_ne hck'.1 (Ne.symm hck)
        have h3 := (prop_3_2_1' hc (lvl_pos q ℓ z) hlt2 hck'.2).2.1
        have huk : u k = c k := by simp [hudef, show k ≠ m by omega]
        have h4 : q.symm (u k) < lvl q (p1 + 1) u := qsymm_lt_lvl u (by omega)
        rw [huk] at h4
        exact center_mem_coarse hc (hMu hwM) hwz (by omega)
      · -- u ∉ E(α, p, 1)
        intro huE
        rw [EsetOF_succ] at huE
        rcases huE with h | h
        · rw [EsetOF_zero, show p (0 + 2) = p1 by rw [← hp.2.2.2]; exact hp1, hp1] at h
          have h' := gset_gsetT hc hp1pos le_rfl _ h
          exact companion_not_mem_gset hc hp1pos (by omega) hM hMc hcu hlvu (hMc ▸ huM) h'
        · obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp h
          exact not_mem_HkOF_of_branch1 hc hSB hPv huA.2 a p _ c' hc'
  · obtain ⟨S4, -, hBl, -⟩ := hch
    obtain ⟨u, -, hue, -⟩ := hBl
    exact Or.inl (shell (m + 5) u (by omega) hue (by omega))

/-- **反例の本体**: z の性質から、宣言された閉包（k = 0）が破れる。 -/
theorem not_declaredClosureF_cex {J : ℕ} (hJ0 : 0 < J)
    (hJ : ∀ k, 0 < k → k < m → q.symm (y0 k) < J)
    {a : ℕ → ℕ} (hgap : ∀ v, a (m + v) ≠ p1) {cz : ℕ} {S S2 : Set (ℕ → α)} {z : ℕ → α}
    (hSe : S = gfun q T (m + 1) (shift0 T y0 J))
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 cz))
    (hS2 : S2 ∈ lncA q T (m + 2) (slabO q T m y0 cz ∩ S))
    (hlab : lab (lncA q T (m + 2) (slabO q T m y0 cz ∩ S)) S2 ≠ 1)
    (hzs : ∀ k < m, z k = shift0 T y0 J k) (hzc : z ∈ slabO q T m y0 cz)
    (hzS : z ∈ S) (hzS2 : z ∈ S2) {p p' : ℕ → ℕ} (hp : AdmT m p) (hp1 : p 1 = p1)
    (hp' : AdmT m p') (hp'1 : p' 1 = p1 + 1)
    (hz1 : z ∈ EsetOF q T m y0 (fcAdv q T p1 m) a p 1)
    (hz2 : ∀ c, z ∉ HkOF q T m y0 (fcAdv q T p1 m) a p' 0
      (EseqOF q T m y0 (fcAdv q T p1 m) a p' 0).2 c)
    {ℓ : ℕ} (hℓ : m + 5 < ℓ)
    (hcell : ∀ u ∈ gfun q T ℓ z, (∀ k < m, u k = z k) →
      u ∈ EsetOF q T m y0 (fcAdv q T p1 m) a p 1) :
    ∀ A, a ∈ A → ¬ DeclaredClosureF q T m y0 (fcAdv q T p1 m) A := by
  intro A ha hDC
  set fc := fcAdv q T p1 m with hfcdef
  have hp15 : m + 5 < p1 := hp1 ▸ hp.2.1
  have hp2 : p 2 = p1 := hp.2.2.2.symm.trans hp1
  have hz := hDC a ha p hp 0 hz1
  refine not_mem_closure_of_maxKillF hc hp
    (killNbhd_isOpenF (fc := fc) ha hp hp' (ℓ := ℓ) (ℓ' := ℓ) (ph := p1 + 1) (by omega) hℓ
      (by omega) z z) ?_ (Set.inter_subset_left.trans (Set.inter_subset_left)) (K :=
      EsetOF q T m y0 fc a p' 1 ∪ gset q T (p1 + 1) (gfun q T ℓ z \ EsetOF q T m y0 fc a p 1))
    ?_ ?_ hz
  · refine ⟨⟨mem_gfun q T ℓ z, ?_⟩, ?_⟩
    · intro h
      rw [EsetOF_succ] at h
      rcases h with h | h
      · rw [EsetOF_zero, show p' (0 + 2) = p1 + 1 by rw [← hp'.2.2.2]; exact hp'1, hp'1] at h
        have h' := gset_gsetT hc (by omega) le_rfl _ h
        exact z_not_mem_gsetD1 hc hm hJ0 hJ hSe hS hS2 hlab hzs hzc hzS hzS2 (by omega) h'
      · obtain ⟨c, hc'⟩ := Set.mem_iUnion.mp h
        exact hz2 c hc'
    · intro h
      obtain ⟨u, hu, hzu⟩ := Set.mem_iUnion₂.mp h
      refine hu.2 (hcell u hu.1 (fun k hk => le_antisymm (hzu.1 k (by omega)).1
        (hu.1.1 k (by omega)).1))
  · rw [Set.disjoint_left]
    rintro w ⟨⟨-, h1⟩, h2⟩ (h | h)
    · exact h1 h
    · exact h2 h
  · intro M hM w hw
    exact kill_max_cex hc hm hJ0 hJ hgap hSe hS hS2 hlab hzs hzc hzS hzS2 hp hp1
      (by omega) (by rw [hp1] at hM; exact hM) hw.1 hw.2

end main

end Defs.D_0068
