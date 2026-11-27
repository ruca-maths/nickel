import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0068
import Defs.D_0056
import Defs.D_0046

namespace Defs.D_0069

/-!
**宣言された閉包は偽（選択関数 fcAdv のとき）**。Chen–Wang Definition B.1 / Denotation 1 の反例。

`declaredClosureF_false` : Compat2、Countable、NoMaxOrder、m > 0 のもとで、狭義単調な α と
m + 5 < p₁、α(m + v) ≠ p₁（すべての v）を満たす p₁ について、妥当な選択関数 `fcAdv q T p₁ m`
（`validFC_fcAdv`）をとると、α を含むどの 𝒜 についても宣言された閉包（k = 0）は成り立たない。
穴の点 z は、shift0 y₀ J の slab の元 S = g(m+1, shift0 y₀ J) の branch 2・piece 番号 p₁ の
ch-box (α p₁, α p₁+1) の中の S0 の、fcAdv による深い穴の箱の中心。z の性質を
`Defs.D_0068.not_declaredClosureF_cex` の仮定として確かめる。
`declaredClosureF_false_example` : α(i) = 2i+1、p₁ = 2m+6 の具体例。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0040 Defs.D_0043 Defs.D_0046
  Defs.D_0049 Defs.D_0050 Defs.D_0051 Defs.D_0056 Defs.D_0060 Defs.D_0062 Defs.D_0064 Defs.D_0065
  Defs.D_0066 Defs.D_0067 Defs.D_0068

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

theorem validFC_fcAdv [Countable α] (p1 k0 : ℕ) : ValidFC q T (fcAdv q T p1 k0) := by
  intro n A hcnt hinf
  classical
  unfold fcAdv
  split_ifs with h
  · exact h.2.choose_spec.choose_spec.2.2.1
  · exact validFC_firstC (q := q) (T := T) n A hcnt hinf

theorem declaredClosureF_false [Countable α] [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m)
    {a : ℕ → ℕ} (ha : StrictMono a) {p1 : ℕ} (hp1 : m + 5 < p1)
    (hgap : ∀ v, a (m + v) ≠ p1) :
    ∀ A, a ∈ A → ¬ DeclaredClosureF q T m y0 (fcAdv q T p1 m) A := by
  set fc := fcAdv q T p1 m with hfcdef
  -- 許容列
  set p : ℕ → ℕ := fun j => if j = 0 then 1 else p1 with hpdef
  set p' : ℕ → ℕ := fun j => if j = 0 then 1 else p1 + 1 with hp'def
  have hp : AdmT m p := by
    refine ⟨fun i j hij => ?_, by simp [hpdef]; omega, by simp [hpdef], by simp [hpdef]⟩
    simp only [hpdef]; split_ifs <;> omega
  have hp' : AdmT m p' := by
    refine ⟨fun i j hij => ?_, by simp [hp'def]; omega, by simp [hp'def], by simp [hp'def]⟩
    simp only [hp'def]; split_ifs <;> omega
  have hp1e : p 1 = p1 := by simp [hpdef]
  have hp2e : p 2 = p1 := by simp [hpdef]
  have hp'1e : p' 1 = p1 + 1 := by simp [hp'def]
  have hp'2e : p' 2 = p1 + 1 := by simp [hp'def]
  -- 近い slab の元 S
  set J := lvl q (m + 1) y0 + 1 with hJdef
  have hJ0 : 0 < J := by omega
  have hJ : ∀ k, 0 < k → k < m → q.symm (y0 k) < J := fun k _ hk => by
    have := qsymm_lt_lvl (q := q) y0 (show k < m + 1 by omega); omega
  set s := shift0 T y0 J with hsdef
  have hlvm : lvl q m y0 < J := by have := lvl_lt_lvl (q := q) hm (by omega : m < m + 1) y0; omega
  have hsG : s ∈ gfun q T m y0 :=
    shift0_box_sub hc (m := m) hm hlvm (mem_gfun q T (m + 1) s)
  have hs0 : s 0 = T.child (y0 0) J := shift0_zero y0 J
  have hne : hidx q m s ≠ hidx q m y0 := by
    intro h
    have h1 := (code_eq_iff m hm _ _).1 h 0 hm
    have h2 : s 0 = y0 0 := q.symm.injective h1
    rw [hs0] at h2
    exact absurd h2 (ne_of_gt (T.lt_child _ _ (T.C_child _ _ hJ0)))
  have hsm : s m = y0 m := shift0_ne y0 J (by omega)
  have hBm : q.symm (s m) < q.symm (s 0) := by
    rw [hsm, hs0]
    have h1 := qsymm_lt_lvl (q := q) y0 (show m < m + 1 by omega)
    have h2 := hc.idx_le_num (y0 0) J hJ0
    omega
  set cz := hidx q m s with hczdef
  set S := gfun q T (m + 1) s with hSdef
  have hS : S ∈ lncA q T (m + 1) (slabO q T m y0 cz) := close_member hc hm hsG hne hBm
  have hslab : slabO q T m y0 cz = H q m cz ∩ gfun q T m y0 := by
    unfold slabO; rw [ite_eq_right hne]; rfl
  have hsslab : s ∈ slabO q T m y0 cz := by rw [hslab]; exact ⟨rfl, hsG⟩
  -- Good の鎖
  set A1 := slabO q T m y0 cz ∩ S with hA1
  have hgA1 : Good q T A1 (m + 1) s := by
    have hg0 : Good q T (H q m cz ∩ gfun q T m y0) m y0 :=
      ⟨Set.inter_subset_right, fun k hk =>
        FreeAt.inter (H_free hm (by omega) cz) (gfun_free y0 (by omega))⟩
    have := good_step hc hm (by omega : m ≤ m + 1) hg0 (hslab ▸ hsslab)
    rw [hA1, hslab]; exact this
  have hA1ne : s ∈ A1 := ⟨hsslab, mem_gfun q T _ s⟩
  have h2inf := good_infinite hc (by omega) (by omega : m + 1 < m + 2) ⟨s, hA1ne⟩ hgA1
  have hF2 : (lncA q T (m + 2) A1).Countable ∧ (lncA q T (m + 2) A1).Infinite :=
    ⟨lncA_countable (by omega) A1, h2inf⟩
  set S2 := unlab (lncA q T (m + 2) A1) hF2 2 with hS2
  have hS2mem : S2 ∈ lncA q T (m + 2) A1 := unlab_mem _ hF2 2
  have hS2lab : lab (lncA q T (m + 2) A1) S2 = 2 := lab_unlab _ hF2 2
  obtain ⟨x2, hx2, hS2eq, -⟩ := id hS2mem
  have hgA12 : Good q T (A1 ∩ S2) (m + 2) x2 := by
    rw [hS2eq]; exact good_step hc (by omega) (by omega) hgA1 hx2
  have hx2' : x2 ∈ A1 ∩ S2 := ⟨hx2, hS2eq ▸ mem_gfun q T _ x2⟩
  have h3inf := good_infinite hc (by omega) (by omega : m + 2 < m + 3) ⟨x2, hx2'⟩ hgA12
  have hF3 : (lncA q T (m + 3) (A1 ∩ S2)).Countable ∧ (lncA q T (m + 3) (A1 ∩ S2)).Infinite :=
    ⟨lncA_countable (by omega) _, h3inf⟩
  set S3 := unlab (lncA q T (m + 3) (A1 ∩ S2)) hF3 p1 with hS3
  have hS3mem : S3 ∈ lncA q T (m + 3) (A1 ∩ S2) := unlab_mem _ hF3 p1
  have hS3lab : lab (lncA q T (m + 3) (A1 ∩ S2)) S3 = p1 := lab_unlab _ hF3 p1
  have hpiece : (A1 ∩ S2 ∩ S3, p1) ∈ pieces q T m A1 2 :=
    ⟨S2, hS2mem, hS2lab, S3, hS3mem, hS3lab.symm, rfl⟩
  obtain ⟨x3, hx3, hS3eq, -⟩ := id hS3mem
  set P := A1 ∩ S2 ∩ S3 with hP
  have hgP : Good q T P (m + 3) x3 := by
    rw [hP, hS3eq]; exact good_step hc (by omega) (by omega) hgA12 hx3
  have hx3P : x3 ∈ P := ⟨hx3, hS3eq ▸ mem_gfun q T _ x3⟩
  have h4inf := good_infinite hc (by omega) (by omega : m + 3 < m + 4) ⟨x3, hx3P⟩ hgP
  have hF4 : (lncA q T (m + 4) P).Countable ∧ (lncA q T (m + 4) P).Infinite :=
    ⟨lncA_countable (by omega) _, h4inf⟩
  set S4 := unlab (lncA q T (m + 4) P) hF4 (a p1) with hS4
  have hS4mem : S4 ∈ lncA q T (m + 4) P := unlab_mem _ hF4 _
  have hS4lab : lab (lncA q T (m + 4) P) S4 = a p1 := lab_unlab _ hF4 _
  obtain ⟨x4, hx4, hS4eq, -⟩ := id hS4mem
  have hg45 : Good q T (S4 ∩ P) (m + 4) x4 := by
    rw [hS4eq]; exact good_step' hc (by omega) (by omega) hgP hx4
  have hne45 : (S4 ∩ P).Nonempty := ⟨x4, by rw [hS4eq]; exact mem_gfun q T _ x4, hx4⟩
  have h5inf := good_infinite hc (by omega) (by omega : m + 4 < m + 5) hne45 hg45
  have hF5 : (lncA q T (m + 5) (S4 ∩ P)).Countable ∧ (lncA q T (m + 5) (S4 ∩ P)).Infinite :=
    ⟨lncA_countable (by omega) _, h5inf⟩
  set M5 := unlab (lncA q T (m + 5) (S4 ∩ P)) hF5 (a p1 + 1) with hM5
  have hM5mem : M5 ∈ lncA q T (m + 5) (S4 ∩ P) := unlab_mem _ hF5 _
  have hM5lab : lab (lncA q T (m + 5) (S4 ∩ P)) M5 = a p1 + 1 := lab_unlab _ hF5 _
  have hch : M5 ∈ chBoxes q T m a P p1 :=
    ⟨S4, hS4mem, hM5mem, Or.inl ⟨by rw [hS4lab], by rw [hM5lab]; omega⟩⟩
  obtain ⟨x5, hx5, hM5eq, -⟩ := id hM5mem
  -- 穴の層
  have hav : m + p1 ≤ a (m + p1) := ha.id_le _
  set L := a (m + p1) + 1 with hLdef
  have hx5P : x5 ∈ P := hx5.2
  obtain ⟨hS0mem, hx5S0⟩ := lncA_mem_spec hc (sub_gset (q := q) (T := T) (a (m + p1)) P hx5P)
  set S0 := lncA_mem q T (a (m + p1)) P x5 with hS0
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
  -- 深い穴の箱
  obtain ⟨S2B, hS2B, -, S3B, hS3B, -, hPe⟩ := id hpiece
  have hshift : ShiftOK q T (S0 ∩ P) (L - 1) m := by
    refine ShiftOK_inter (ShiftOK_lncA hc (n := a (m + p1)) (by omega) (by omega) hS0mem) ?_
    refine ShiftOK_inter (ShiftOK_inter (ShiftOK_inter
      (ShiftOK_slabO hc hm (by omega) le_rfl y0 cz)
      (ShiftOK_lncA hc (by omega) (by omega) hS))
      (ShiftOK_lncA hc (by omega) (by omega) hS2mem))
      (ShiftOK_lncA hc (by omega) (by omega) hS3mem)
  have hne0 : (S0 ∩ P).Nonempty := ⟨x0, by rw [hS0eq]; exact mem_gfun q T _ x0, hx0⟩
  obtain ⟨z, y, hfcz, hzA, -, -, -, -, -⟩ :=
    fcAdv_deep hc (p1 := p1) (show p1 + 2 ≤ L by omega) hne0 hshift (show m < L by omega)
  set B := gfun q T L z with hBdef
  have hzB : z ∈ B := mem_gfun q T L z
  have hzP : z ∈ P := hzA.2
  have hBGd : B ∈ GdF q T m fc a P p1 := by
    unfold GdF
    rw [if_pos (by omega : m + 5 ≤ a (m + p1) + 1)]
    exact ⟨⟨S0, hS0mem, hfcz.symm⟩, z, hzB, Set.mem_sUnion.mpr ⟨M5, hch, hS0M5 hzA.1⟩⟩
  -- z の性質
  have hzc : z ∈ slabO q T m y0 cz := hzP.1.1.1
  have hzS : z ∈ S := hzP.1.1.2
  have hzS2 : z ∈ S2 := hzP.1.2
  have hzs : ∀ k < m, z k = s k := by
    have h1 : hidx q m z = hidx q m s := (slabO_hidx hzc).1
    intro k hk
    exact q.symm.injective ((code_eq_iff m hm _ _).1 h1 k hk)
  have hlab : lab (lncA q T (m + 2) (slabO q T m y0 cz ∩ S)) S2 ≠ 1 := by
    rw [← hA1, hS2lab]; omega
  -- prior と prevD
  have hpieceE : (P, p1) ∈ pieces q T m (slabO q T m y0 cz ∩ S) (0 + 2) := hpiece
  have hcellmem : ∀ u, u ∈ B → u ∈ P → u ∈ HkOF q T m y0 fc a p 0
      (EseqOF q T m y0 fc a p 0).2 cz := by
    intro u huB huP
    unfold HkOF slabRec
    refine Set.mem_iUnion₂.mpr ⟨S, ⟨hS, z, hzS, hzc, ?_⟩, ?_⟩
    · rintro (h | h)
      · rw [slabCum_eq] at h
        obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp h
        have hi' : i ≠ cz := by
          have := Finset.mem_range.mp hi; omega
        unfold slabRec at hzi
        obtain ⟨S', -, hzS'⟩ := Set.mem_iUnion₂.mp hzi
        exact Set.disjoint_left.mp (slabO_disjoint (q := q) (T := T) (m := m) (y0 := y0) hi')
          (holeCellsF_sub_slab a _ _ i S' hzS') hzc
      · exact not_mem_gset_D1slabOF hc (weakFC_fcAdv p1 m) a (p := p 1) (by rw [hp1e]; omega)
          hS hS2mem hlab hzS hzS2 h
    · simp only [holeCellsF, Set.mem_iUnion, exists_prop]
      exact ⟨(P, p1), ⟨hpieceE, by rw [show p (0 + 2) = p1 from hp2e]⟩, B, hBGd, huB, huP⟩
  have hz1 : z ∈ EsetOF q T m y0 fc a p 1 := by
    rw [EsetOF_succ]
    exact Or.inr (Set.mem_iUnion.mpr ⟨cz, hcellmem z hzB hzP⟩)
  have hz2 : ∀ c, z ∉ HkOF q T m y0 fc a p' 0 (EseqOF q T m y0 fc a p' 0).2 c := by
    intro c hzc'
    obtain ⟨S', Pv', -, hS', hP', hr, -, -, hzP'⟩ := mem_HkOF hzc'
    have := piece_unique hc hS hS' hpieceE hP' hzP hzP'
    rw [← this] at hr
    simp only [hp'2e] at hr
    omega
  -- 穴の箱の中のセル
  set ℓ := L + m + 6 with hℓdef
  have hcell : ∀ u ∈ gfun q T ℓ z, (∀ k < m, u k = z k) →
      u ∈ EsetOF q T m y0 fc a p 1 := by
    intro u hu huz
    have huB : u ∈ B := gfun_sub_coarse hc (mem_gfun q T L z)
      (le_of_lt (lvl_lt_lvl (q := q) (by omega) (by omega : L < ℓ) z)) hu
    have huG : u ∈ gfun q T m y0 :=
      gfun_trans hc hm (slabO_sub_Gm hzc) (gfun_anti hc hm (by omega) z hu)
    have huc : u ∈ slabO q T m y0 cz := by
      rw [hslab]
      refine ⟨?_, huG⟩
      have : hidx q m u = hidx q m z := (code_eq_iff m hm _ _).2 (fun k hk => by
        show q.symm (u k) = q.symm (z k); rw [huz k hk])
      exact this.trans (slabO_hidx hzc).1
    have hbox : ∀ {n : ℕ} {X : Set (ℕ → α)} {Y : Set (ℕ → α)}, 0 < n → n ≤ L →
        X ∈ lncA q T n Y → z ∈ X → u ∈ X := by
      intro n X Y hn hnL hX hzX
      obtain ⟨xX, -, hXe, -⟩ := hX
      rw [hXe] at hzX ⊢
      exact gfun_trans hc hn hzX (gfun_anti hc hn hnL z huB)
    have huP : u ∈ P :=
      ⟨⟨⟨huc, hbox (by omega) (by omega) hS hzS⟩, hbox (by omega) (by omega) hS2mem hzS2⟩,
        hbox (by omega) (by omega) hS3mem hzP.2⟩
    rw [EsetOF_succ]
    exact Or.inr (Set.mem_iUnion.mpr ⟨cz, hcellmem u huB huP⟩)
  exact not_declaredClosureF_cex hc hm hJ0 hJ hgap rfl hS hS2mem hlab hzs hzc hzS hzS2 hp hp1e
    hp' hp'1e hz1 hz2 (by omega) hcell

/-- 具体例: α(i) = 2i + 1、p₁ = 2m + 6。 -/
theorem declaredClosureF_false_example [Countable α] [NoMaxOrder α] (hc : Compat2 q T)
    (hm : 0 < m) :
    ValidFC q T (fcAdv q T (2 * m + 6) m) ∧
      ∀ A, (fun i => 2 * i + 1) ∈ A → ¬ DeclaredClosureF q T m y0 (fcAdv q T (2 * m + 6) m) A :=
  ⟨validFC_fcAdv _ _, declaredClosureF_false hc hm (fun i j h => by show 2 * i + 1 < 2 * j + 1; omega)
    (by omega) (fun v => by omega)⟩

end Defs.D_0069
