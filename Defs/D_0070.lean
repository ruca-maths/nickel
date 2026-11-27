import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0068

namespace Defs.D_0070

/-!
**宣言された閉包の破れ（k = 1、一般の穴の点）**。Prop 8.3 の反例の第一段。

z を任意の slab の元の branch 3 の穴のセルの点（branch 2 ではない元に入る）とし、
z ∉ g[p₃, E(α, p, 1)] とする。α の値は区間 [p₁, p₃] を避ける（箱の層は ≤ p₁ か ≥ p₃+2）。
選択関数 fcAdv q T p₃ m のもとで、z ∉ Cl_τ g[p₃, E(α, p, 1)]（`not_mem_closure_k1`）。
E(α, p, 1) の極大な p₃-箱 M は、
* g[p₂, E(α, p, 0)] の点の箱なら M ⊆ E(α, p, 1) ⊆ E(α, p′, 2)（殻）、
* branch 2 の穴のセルの点の箱なら、その穴の箱は深いので、相棒の箱で Definition C の集合
  g[p₃+1, g(ℓ, z) − E(α, p, 2)] に呑まれる。
LOC の代わりに z ∉ g[p₃, E(α, p, 1)] を仮定するので、z の slab は任意。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0034 Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0040 Defs.D_0043
  Defs.D_0050 Defs.D_0060 Defs.D_0062 Defs.D_0063 Defs.D_0064 Defs.D_0065 Defs.D_0066 Defs.D_0067
  Defs.D_0068

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}
  {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)}

theorem EseqOF_congr (a : ℕ → ℕ) {p p' : ℕ → ℕ} :
    ∀ k, (∀ j ≤ k + 1, p j = p' j) →
      EseqOF q T m y0 fc a p k = EseqOF q T m y0 fc a p' k := by
  intro k
  induction k with
  | zero => intro h; simp only [EseqOF, h 1 le_rfl]
  | succ k ih =>
    intro h
    have hprev := ih (fun j hj => h j (by omega))
    simp only [EseqOF, hprev, h (k + 2) le_rfl, HkOF]

/-- HkOF の点の分解（セル全体が HkOF に入ることつき）。 -/
theorem mem_HkOF' {a p : ℕ → ℕ} {k : ℕ} {prevD : ℕ → Set (ℕ → α)} {c : ℕ} {x : ℕ → α}
    (hx : x ∈ HkOF q T m y0 fc a p k prevD c) :
    ∃ S Pv B, S ∈ lncA q T (m + 1) (slabO q T m y0 c) ∧
      Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) (k + 2) ∧ p (k + 2) ≤ Pv.2 ∧
      B ∈ GdF q T m fc a Pv.1 Pv.2 ∧ x ∈ B ∧ x ∈ Pv.1 ∧
      (∀ x' ∈ B, x' ∈ Pv.1 → x' ∈ HkOF q T m y0 fc a p k prevD c) := by
  unfold HkOF slabRec at hx
  obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp hx
  simp only [holeCellsF, Set.mem_iUnion, exists_prop] at hxS
  obtain ⟨Pv, ⟨hPv, hr⟩, B, hB, hxB, hxP⟩ := hxS
  refine ⟨S, Pv, B, hS.1, hPv, hr, hB, hxB, hxP, fun x' hx'B hx'P => ?_⟩
  unfold HkOF slabRec
  refine Set.mem_iUnion₂.mpr ⟨S, hS, ?_⟩
  simp only [holeCellsF, Set.mem_iUnion, exists_prop]
  exact ⟨Pv, ⟨hPv, hr⟩, B, hB, hx'B, hx'P⟩

theorem not_mem_HkOF_of_branch (hc : Compat2 q T) {c b : ℕ} {S : Set (ℕ → α)}
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c)) {Pv : Set (ℕ → α) × ℕ}
    (hP : Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) b) {u : ℕ → α} (hu : u ∈ Pv.1)
    (a p : ℕ → ℕ) (k : ℕ) (hkb : k + 2 ≠ b) (prevD : ℕ → Set (ℕ → α)) (c' : ℕ) :
    u ∉ HkOF q T m y0 fc a p k prevD c' := by
  intro h
  obtain ⟨S', Pv', -, hS', hP', -, -, -, huP'⟩ := mem_HkOF h
  exact hkb (branch_eq_of_pieces hc hS hS' hP hP' hu huP').symm

/-- 一般の層の判定法（極大箱版）。 -/
theorem not_mem_closure_of_maxKillGen (hc : Compat2 q T) {A : Set (ℕ → ℕ)} {n : ℕ}
    {D : Set (ℕ → α)} {z : ℕ → α} {U : Set (ℕ → α)}
    (hU : @IsOpen _ (tauTF q T m y0 fc A) U) (hzU : z ∈ U) {ℓ : ℕ} (hUℓ : U ⊆ gfun q T ℓ z)
    {K : Set (ℕ → α)} (hUK : Disjoint U K)
    (hkill : ∀ M ∈ lncA q T n D, M ∩ gfun q T ℓ z ⊆ K) :
    z ∉ @closure _ (tauTF q T m y0 fc A) (gset q T n D) := by
  let _ := tauTF q T m y0 fc A
  refine not_mem_closure_of_disjoint _ hU hzU ?_
  rw [Set.disjoint_left]
  intro w hwU hwS
  rw [← lncA_sUnion hc] at hwS
  obtain ⟨M, hM, hwM⟩ := hwS
  exact Set.disjoint_left.mp hUK hwU (hkill M hM ⟨hwM, hUℓ hwU⟩)

section k1

variable [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m)
include hc hm

/-- 極大な p₃-箱ごとの切り離し（k = 1）。 -/
theorem kill_max_k1 {a : ℕ → ℕ} (ha : StrictMono a) {p p' : ℕ → ℕ} (hp : AdmT m p)
    (hp13 : p 1 < p 3)
    (hgap : ∀ v, a (m + v) < p 1 ∨ p 3 < a (m + v))
    (hpp' : ∀ j ≤ 2, p j = p' j)
    {cz : ℕ} {S S2 : Set (ℕ → α)} {z : ℕ → α}
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 cz))
    (hS2 : S2 ∈ lncA q T (m + 2) (slabO q T m y0 cz ∩ S))
    (hlab : lab (lncA q T (m + 2) (slabO q T m y0 cz ∩ S)) S2 ≠ 2)
    (hzc : z ∈ slabO q T m y0 cz) (hzS : z ∈ S) (hzS2 : z ∈ S2)
    (hzS1 : z ∉ gset q T (p 3) (EsetOF q T m y0 (fcAdv q T (p 3) m) a p 1))
    {ℓ : ℕ} (hℓ : m + 2 ≤ ℓ)
    {M : Set (ℕ → α)} (hM : M ∈ lncA q T (p 3) (EsetOF q T m y0 (fcAdv q T (p 3) m) a p 1))
    {w : ℕ → α} (hwM : w ∈ M) (hwz : w ∈ gfun q T ℓ z) :
    w ∈ EsetOF q T m y0 (fcAdv q T (p 3) m) a p' 2 ∨
      w ∈ gset q T (p 3 + 1)
        (gfun q T ℓ z \ EsetOF q T m y0 (fcAdv q T (p 3) m) a p 2) := by
  set fc := fcAdv q T (p 3) m with hfcdef
  set P3 := p 3 with hP3
  have hp15 : m + 5 < p 1 := hp.2.1
  have hp12 : p 1 = p 2 := hp.2.2.2
  have hP3pos : 0 < P3 := by omega
  have hE1eq : EsetOF q T m y0 fc a p 1 = EsetOF q T m y0 fc a p' 1 := by
    unfold EsetOF; rw [EseqOF_congr a 1 (fun j hj => hpp' j hj)]
  obtain ⟨e0, he0, hMe, hmax⟩ := id hM
  have he0' := he0
  rw [EsetOF_succ] at he0'
  rcases he0' with he1 | he1
  · -- 殻
    left
    obtain ⟨e1, he1E, he0e1⟩ := Set.mem_iUnion₂.mp he1
    have hp2pos : 0 < p (0 + 2) := by show 0 < p 2; omega
    have hwE : w ∈ gset q T (p (0 + 2)) (EsetOF q T m y0 fc a p 0) := by
      have h1 : M ⊆ gfun q T (p (0 + 2)) e1 := by
        rw [hMe]
        exact (gfun_anti hc hp2pos (by show p 2 ≤ p 3; omega) e0).trans
          (gfun_trans hc hp2pos he0e1)
      exact Set.mem_biUnion he1E (h1 hwM)
    have hwE1 : w ∈ EsetOF q T m y0 fc a p 1 := by rw [EsetOF_succ]; exact Or.inl hwE
    rw [hE1eq] at hwE1
    rw [EsetOF_succ]
    exact Or.inl (sub_gset _ _ hwE1)
  · obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp he1
    obtain ⟨S', Pv', B', hS', hPv', hr, hB', he0B', he0P', hcell'⟩ := mem_HkOF' hc'
    have hv' : p 2 ≤ Pv'.2 := hr
    have hav : m + Pv'.2 ≤ a (m + Pv'.2) := ha.id_le _
    set L := a (m + Pv'.2) + 1 with hLdef
    have hL2 : P3 + 2 ≤ L := by
      rcases hgap Pv'.2 with h | h
      · omega
      · omega
    have hB'' := hB'
    unfold GdF at hB''
    rw [if_pos (by omega : m + 5 ≤ a (m + Pv'.2) + 1)] at hB''
    obtain ⟨⟨S0, hS0, hBe⟩, -⟩ := hB''
    obtain ⟨S2B, hS2B, hlabB, S3B, hS3B, hvB, hPe⟩ := id hPv'
    have hshift : ShiftOK q T (S0 ∩ Pv'.1) (L - 1) m := by
      refine ShiftOK_inter (ShiftOK_lncA hc (n := a (m + Pv'.2)) (by omega) (by omega) hS0) ?_
      rw [hPe]
      refine ShiftOK_inter (ShiftOK_inter (ShiftOK_inter
        (ShiftOK_slabO hc hm (by omega) le_rfl y0 c')
        (ShiftOK_lncA hc (by omega) (by omega) hS'))
        (ShiftOK_lncA hc (by omega) (by omega) hS2B))
        (ShiftOK_lncA hc (by omega) (by omega) hS3B)
    have hmix : MixOK (S0 ∩ Pv'.1) m := by
      refine MixOK_inter (MixOK_lncA hS0 m) ?_
      rw [hPe]
      exact MixOK_inter (MixOK_inter (MixOK_inter (MixOK_slabO hm le_rfl c')
        (MixOK_lncA hS' m)) (MixOK_lncA hS2B m)) (MixOK_lncA hS3B m)
    have hAne : (S0 ∩ Pv'.1).Nonempty := by
      obtain ⟨x0, hx0, hS0e, -⟩ := hS0
      exact ⟨x0, by rw [hS0e]; exact mem_gfun q T _ x0, hx0⟩
    obtain ⟨c, y, hfcc, hcA, hyA, -, hck0, hcy, -⟩ :=
      fcAdv_deep hc (p1 := P3) hL2 hAne hshift (show m < L by omega)
    have hBc : B' = gfun q T L c := hBe.trans hfcc
    have hcB : c ∈ B' := hBc ▸ mem_gfun q T L c
    have hcE : c ∈ EsetOF q T m y0 fc a p 1 := by
      rw [EsetOF_succ]
      exact Or.inr (Set.mem_iUnion.mpr ⟨c', hcell' c hcB hcA.2⟩)
    have hMc : M = gfun q T P3 c := by
      have he0c : e0 ∈ gfun q T L c := hBc ▸ he0B'
      have h1 : gfun q T P3 e0 ⊆ gfun q T P3 c :=
        gfun_trans hc hP3pos (gfun_anti hc hP3pos (by omega) c he0c)
      exact (hmax c hcE (hMe ▸ h1)).symm
    obtain ⟨hcu, hlvu, huM⟩ := companion_of_deep hc (k0 := m) (n := L) (p := P3)
      (ph := P3 + 1) (by omega) (by omega) (by omega) hck0 hcy
    set u := Function.update c m (y m) with hudef
    have huA : u ∈ S0 ∩ Pv'.1 := hmix c hcA y hyA
    right
    have hMu : M ⊆ gfun q T (P3 + 1) u := hMc ▸ gfun_sub_coarse hc hcu hlvu
    refine Set.mem_biUnion (x := u) ⟨?_, ?_⟩ (hMu hwM)
    · have hzM : z ∉ M := fun h => hzS1 (lncA_sub_gset hM h)
      have hwc : w ∈ gfun q T P3 c := hMc ▸ hwM
      have hlt : lvl q ℓ z < lvl q P3 c := by
        by_contra h
        exact hzM (hMc ▸ center_mem_coarse hc hwz hwc (not_lt.mp h))
      have hcz : c ∈ gfun q T ℓ z := center_mem_coarse hc hwc hwz hlt.le
      have hk : ∃ k < m, c k ≠ z k := by
        by_contra hall
        push Not at hall
        have hcslab : hidx q m c = hidx q m z :=
          (code_eq_iff m hm _ _).2 (fun k hk => by
            show q.symm (c k) = q.symm (z k); rw [hall k hk])
        have hcP : c ∈ Pv'.1 := hcA.2
        rw [hPe] at hcP
        have hcB' : c' = cz := ((slabO_hidx hcP.1.1.1).1.symm.trans hcslab).trans
          (slabO_hidx hzc).1
        subst hcB'
        have hcS : c ∈ S := by
          obtain ⟨x1, -, hx1, -⟩ := id hS
          have : gfun q T ℓ z ⊆ S := by
            rw [hx1]
            exact (gfun_anti hc (by omega) (show m + 1 ≤ ℓ by omega) z).trans
              (gfun_trans hc (by omega) (hx1 ▸ hzS))
          exact this hcz
        have hSS : S' = S := lncA_unique hc hS' hS hcP.1.1.2 hcS
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
      have h4 : q.symm (u k) < lvl q (P3 + 1) u := qsymm_lt_lvl u (by omega)
      rw [huk] at h4
      exact center_mem_coarse hc (hMu hwM) hwz (by omega)
    · intro huE
      rw [EsetOF_succ] at huE
      rcases huE with h | h
      · exact companion_not_mem_gset hc hP3pos (by omega) hM hMc hcu hlvu (hMc ▸ huM) h
      · obtain ⟨c'', hc''⟩ := Set.mem_iUnion.mp h
        exact not_mem_HkOF_of_branch hc hS' hPv' huA.2 a p 1 (by omega) _ c'' hc''

/-- **k = 1 の宣言された閉包の破れ**: 穴の点 z（branch ≠ 2 の元、z ∉ g[p₃, E(α, p, 1)]）は
g[p₃, E(α, p, 1)] の τ-閉包に入らない。 -/
theorem not_mem_closure_k1 {A : Set (ℕ → ℕ)} {a : ℕ → ℕ} (haA : a ∈ A) (ha : StrictMono a)
    {p p' : ℕ → ℕ} (hp : AdmT m p) (hp' : AdmT m p') (hp13 : p 1 < p 3)
    (hgap : ∀ v, a (m + v) < p 1 ∨ p 3 < a (m + v))
    (hpp' : ∀ j ≤ 2, p j = p' j) (hp'3 : p 3 ≤ p' 3)
    {cz : ℕ} {S S2 : Set (ℕ → α)} {z : ℕ → α}
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 cz))
    (hS2 : S2 ∈ lncA q T (m + 2) (slabO q T m y0 cz ∩ S))
    (hlab : lab (lncA q T (m + 2) (slabO q T m y0 cz ∩ S)) S2 ≠ 2)
    (hzc : z ∈ slabO q T m y0 cz) (hzS : z ∈ S) (hzS2 : z ∈ S2)
    (hzS1 : z ∉ gset q T (p 3) (EsetOF q T m y0 (fcAdv q T (p 3) m) a p 1))
    (hz2 : ∀ c, z ∉ HkOF q T m y0 (fcAdv q T (p 3) m) a p' 1
      (EseqOF q T m y0 (fcAdv q T (p 3) m) a p' 1).2 c)
    {ℓ : ℕ} (hℓ : m + 5 < ℓ)
    (hcell : ∀ u ∈ gfun q T ℓ z, (∀ k < m, u k = z k) →
      u ∈ EsetOF q T m y0 (fcAdv q T (p 3) m) a p 2) :
    z ∉ @closure _ (tauTF q T m y0 (fcAdv q T (p 3) m) A)
      (gset q T (p 3) (EsetOF q T m y0 (fcAdv q T (p 3) m) a p 1)) := by
  set fc := fcAdv q T (p 3) m with hfcdef
  have hp15 : m + 5 < p 1 := hp.2.1
  have hE1eq : EsetOF q T m y0 fc a p 1 = EsetOF q T m y0 fc a p' 1 := by
    unfold EsetOF; rw [EseqOF_congr a 1 (fun j hj => hpp' j hj)]
  have hU : @IsOpen _ (tauTF q T m y0 fc A)
      (gfun q T ℓ z ∩ (EsetOF q T m y0 fc a p' 2)ᶜ ∩
        (gset q T (p 3 + 1) (gfun q T ℓ z \ EsetOF q T m y0 fc a p 2))ᶜ) := by
    let _ := tauTF q T m y0 fc A
    refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
    · exact isOpen_tauF_of_mem (Or.inl (Or.inl ⟨ℓ, z, by omega, Or.inl rfl⟩))
    · exact isOpen_tauF_of_mem (Or.inl (Or.inr ⟨a, haA, p', hp', 1, Or.inr rfl⟩))
    · exact isOpen_tauF_of_mem (Or.inr ⟨a, haA, p, hp, 1, ℓ, p 3 + 1, z, hℓ, (by show p 3 < p 3 + 1; omega), Or.inr rfl⟩)
  refine not_mem_closure_of_maxKillGen hc hU ?_ (Set.inter_subset_left.trans Set.inter_subset_left)
    (K := EsetOF q T m y0 fc a p' 2 ∪
      gset q T (p 3 + 1) (gfun q T ℓ z \ EsetOF q T m y0 fc a p 2)) ?_ ?_
  · refine ⟨⟨mem_gfun q T ℓ z, ?_⟩, ?_⟩
    · intro h
      rw [EsetOF_succ] at h
      rcases h with h | h
      · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.mp h
        rw [← hE1eq] at he
        exact hzS1 (Set.mem_biUnion he (gfun_anti hc (show 0 < p 3 by omega) hp'3 e hze))
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
    exact kill_max_k1 hc hm ha hp hp13 hgap hpp' hS hS2 hlab hzc hzS hzS2 hzS1 (by omega)
      hM hw.1 hw.2

end k1

end Defs.D_0070
