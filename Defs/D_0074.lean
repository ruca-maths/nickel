import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0073

namespace Defs.D_0074

/-!
**Prop 8.3 の反例（頑健な読み方）**。`Defs.D_0073` の反例 V について、fine の読み方を次のように弱めても
V は fine でない（`prop83_counterexampleS`）。

`FineS` では「穴でない点は V に入る」の穴として全セル `AllCells n`（branch n のすべての piece の G_d 箱のセル）を、
「穴は Cl_τ V に入らない」の穴として `HolesW n`（HkOF (n−2)、n = 1 では ∅）を使う。
`HolesW n ⊆ AllCells n`（`HolesW_sub_AllCells`）なので、論文の穴の集合 H(m₅σ^α_1, −βγ, q_n z) が
領域の中でこの二つの間にあれば、論文の fine は `FineS` を含意する。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0009 Defs.D_0012 Defs.D_0024 Defs.D_0025
  Defs.D_0029 Defs.D_0031 Defs.D_0034 Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039
  Defs.D_0040 Defs.D_0043 Defs.D_0049 Defs.D_0050 Defs.D_0051 Defs.D_0056 Defs.D_0060 Defs.D_0062
  Defs.D_0064 Defs.D_0065 Defs.D_0066 Defs.D_0067 Defs.D_0068 Defs.D_0070 Defs.D_0071 Defs.D_0072
  Defs.D_0073

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

section fine

variable (q T m y0)

/-- branch n のすべての piece の G_d 箱のセル。 -/
def AllCells (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) (a : ℕ → ℕ) (n : ℕ) : Set (ℕ → α) :=
  {x | ∃ c' S', S' ∈ lncA q T (m + 1) (slabO q T m y0 c') ∧
    ∃ Pv ∈ pieces q T m (slabO q T m y0 c' ∩ S') n, ∃ B ∈ GdF q T m fc a Pv.1 Pv.2,
      x ∈ B ∧ x ∈ Pv.1}

/-- fine の弱い形: ある n ≤ k、元、閾値 N について、領域の全セルの外の点は V に入り、
HkOF の穴の点は Cl_τ V に入らない。 -/
def FineS (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) (A : Set (ℕ → ℕ)) (a p : ℕ → ℕ) (k : ℕ)
    (V : Set (ℕ → α)) : Prop :=
  ∃ n, 1 ≤ n ∧ n ≤ k ∧ ∃ c S, S ∈ lncA q T (m + 1) (slabO q T m y0 c) ∧ ∃ N,
    ∀ x ∈ RegionW q T m y0 a c S n N,
      (x ∉ AllCells q T m y0 fc a n → x ∈ V) ∧
      (x ∈ HolesW q T m y0 fc a p n → x ∉ @closure _ (tauTF q T m y0 fc A) V)

end fine

theorem HolesW_sub_AllCells (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) (a p : ℕ → ℕ) {n : ℕ}
    (hn1 : 1 ≤ n) :
    HolesW q T m y0 fc a p n ⊆ AllCells q T m y0 fc a n := by
  unfold HolesW
  split_ifs with hn
  · exact Set.empty_subset _
  · intro x hx
    obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp hx
    obtain ⟨S', Pv, B, hS', hP, -, hB, hxB, hxP⟩ := mem_HkOF hc'
    have h : n - 2 + 2 = n := by omega
    rw [h] at hP; exact ⟨c', S', hS', Pv, hP, B, hB, hxB, hxP⟩

theorem not_mem_AllCells_of_pd {a : ℕ → ℕ} {P3 c : ℕ} {S : Set (ℕ → α)} {n v : ℕ}
    (pd : PieceData q T m y0 a P3 c S n v) (hc : Compat2 q T)
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c)) (hL : m + 5 ≤ a (m + v) + 1) {w : ℕ → α}
    (hw : w ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3))
    (hwB : w ∉ gfun q T (a (m + v) + 1) pd.cB) (n' : ℕ) :
    w ∉ AllCells q T m y0 (fcAdv q T P3 m) a n' := by
  rintro ⟨c', S', hS', Pv', hP', B', hB', hwB', hwP'⟩
  have hPP := piece_unique hc hS hS' pd.hpiece hP' hw.2 hwP'
  subst hPP
  have hB'' : B' ∈ GdF q T m (fcAdv q T P3 m) a (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3) v := hB'
  unfold GdF at hB''
  rw [ite_eq_left hL] at hB''
  obtain ⟨⟨S0', hS0', hBe⟩, -⟩ := hB''
  rcases weakFC_fcAdv (q := q) (T := T) P3 m (a (m + v) + 1)
      (S0' ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3)) with h0 | ⟨u, hu, hue, -⟩
  · rw [hBe, h0] at hwB'; exact hwB'
  · have hwu : w ∈ gfun q T (a (m + v) + 1) u := by rw [hBe, hue] at hwB'; exact hwB'
    have hwS0' : w ∈ S0' := mem_lncA_of_box hc (by omega) (by omega) hS0' hu.1 hwu
    have hSS := lncA_unique hc pd.hS0 hS0' hw.1 hwS0'
    subst hSS
    rw [hBe, pd.hfc] at hwB'
    exact hwB hwB'

/-- **Prop 8.3 の反例**（頑健な読み方 `FineS`）。 -/
theorem prop83_counterexampleS [Countable α] [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m)
    {A : Set (ℕ → ℕ)} {a : ℕ → ℕ} (haA : a ∈ A) (ha : StrictMono a) {p : ℕ → ℕ}
    (hp : AdmT m p) (hp13 : p 1 < p 3) (hgap : ∀ v, a (m + v) < p 1 ∨ p 3 < a (m + v))
    {cc : ℕ} (hcc : 0 < cc) (b : ℕ) :
    @IsOpen _ (tauTF q T m y0 (fcAdv q T (p 3) m) A) (Vcex q T m y0 A a p cc b) ∧
    y0 ∈ Vcex q T m y0 A a p cc b ∧
    gcBox q T cc b y0 \ EsetOF q T m y0 (fcAdv q T (p 3) m) a p 2 ⊆ Vcex q T m y0 A a p cc b ∧
    Vcex q T m y0 A a p cc b ⊆ gcBox q T cc b y0 \ EsetOF q T m y0 (fcAdv q T (p 3) m) a p 1 ∧
    ¬ FineS q T m y0 (fcAdv q T (p 3) m) A a p 3 (Vcex q T m y0 A a p cc b) := by
  set fc := fcAdv q T (p 3) m with hfcdef
  let τ := tauTF q T m y0 fc A
  set E1 := EsetOF q T m y0 fc a p 1 with hE1
  set E2 := EsetOF q T m y0 fc a p 2 with hE2
  set G := gcBox q T cc b y0 with hG
  set S1 := gset q T (p 3) E1 with hS1
  set V := Vcex q T m y0 A a p cc b with hV
  have hVe : V = (G \ E1) ∩ (@closure _ τ S1)ᶜ := rfl
  have hfc : WeakFC q T fc := weakFC_fcAdv (p 3) m
  have hp15 : m + 5 < p 1 := hp.2.1
  have hp12 : p 1 = p 2 := hp.2.2.2
  have hp23 : p 2 ≤ p 3 := hp.1 (by omega)
  have hE12 : E1 ⊆ E2 := EsetOF_sub_succ a p 1
  have hS1E2 : S1 ⊆ E2 := gset_sub_EsetOF_succ (fc := fc) a p 1
  have hE2c : @IsClosed _ τ E2 := by
    let _ := τ
    rw [← isOpen_compl_iff]
    exact isOpen_tauF_of_mem (Or.inl (Or.inr ⟨a, haA, p, hp, 1, Or.inr rfl⟩))
  have hclE2 : @closure _ τ S1 ⊆ E2 := by
    let _ := τ
    exact closure_minimal hS1E2 hE2c
  have hy0 : ∀ k, y0 ∉ EsetOF q T m y0 fc a p k := y0_not_mem_EsetOF hc hm hfc a hp
  refine ⟨?_, ?_, ?_, Set.inter_subset_left, ?_⟩
  · -- 開
    let _ := τ
    rw [hVe, Set.sdiff_eq]
    refine IsOpen.inter (IsOpen.inter (isOpen_tauF_of_ptop hc (gcBox_isOpen_p cc b y0)) ?_)
      isClosed_closure.isOpen_compl
    exact isOpen_tauF_of_mem (Or.inl (Or.inr ⟨a, haA, p, hp, 0, Or.inr rfl⟩))
  · -- y₀ ∈ V
    exact ⟨⟨mem_gcBox_self hcc b y0, hy0 1⟩, fun h => hy0 2 (hclE2 h)⟩
  · -- G − E₂ ⊆ V
    rintro x ⟨hxG, hxE2⟩
    exact ⟨⟨hxG, fun h => hxE2 (hE12 h)⟩, fun h => hxE2 (hclE2 h)⟩
  · -- V は fine でない
    rintro ⟨n, hn1, hn3, c, S, hS, N, hfine⟩
    set v := N + 5 + p 3 + lvl q b y0 + 1 with hv
    have hav : m + v ≤ a (m + v) := ha.id_le _
    set L := a (m + v) + 1 with hLdef
    have hL : p 3 + 2 ≤ L := by omega
    have hL5 : m + 5 ≤ a (m + v) + 1 := by omega
    obtain ⟨pd⟩ := piece_builder (P3 := p 3) hc hm ha hS n v hL (by omega)
    have hcB := pd_cB_mem pd
    have hlvL : L < lvl q L pd.cB := by unfold lvl; omega
    -- 穴でない領域の点 w ∉ V は fine に反する
    have hbad : ∀ w, w ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3) →
        w ∉ gfun q T L pd.cB → w ∉ V → False := fun w hw hwB hwV =>
      hwV ((hfine w (mem_RegionW_of_pd pd (by omega) hw)).1
        (not_mem_AllCells_of_pd pd hc hS hL5 hw hwB n))
    -- 場合 A: c_B ∈ g[p₃, E₁]
    have hcaseA : pd.cB ∉ S1 := by
      intro hcS1
      obtain ⟨e, he, hce⟩ := Set.mem_iUnion₂.mp hcS1
      have hK : lvl q (p 3) e < lvl q L pd.cB := lvl_lt_of_mem hc (by omega) (by omega) hce
      obtain ⟨w, hw, hwB, hwk⟩ := ktrick pd hc ha hm hK
      have hwS1 : w ∈ S1 := Set.mem_iUnion₂.mpr ⟨e, he, gfun_mem_of_agree hce hwk⟩
      exact hbad w hw hwB (fun hwV => hwV.2 (subset_closure hwS1))
    obtain rfl | rfl | rfl : n = 1 ∨ n = 2 ∨ n = 3 := by omega
    · -- n = 1: c_B ∈ D₁ ⊆ E₁
      apply hcaseA
      refine sub_gset _ _ (D1OF_sub_EsetOF a p 1 (Set.mem_iUnion.mpr ⟨c, ?_⟩))
      rw [D1slabOF_eq]
      by_cases hal : S ∈ allowedO q T m y0 c (⋃ i ∈ Finset.range c, D1slabOF q T m y0 fc a i)
      · refine Set.mem_iUnion₂.mpr ⟨S, hal, ?_⟩
        unfold holeBoxesUF
        simp only [Set.mem_iUnion, Set.mem_sUnion, exists_prop]
        exact ⟨_, ⟨pd.hpiece, Nat.zero_le _⟩, _, pd.hGd, mem_gfun q T _ _⟩
      · exfalso
        apply hal
        refine ⟨hS, pd.cB, hcB.2.1.1.2, hcB.2.1.1.1, fun hpr => hcaseA ?_⟩
        obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.mp hpr
        exact sub_gset _ _ (D1OF_sub_EsetOF a p 1 (Set.mem_iUnion.mpr ⟨i, hi⟩))
    · -- n = 2: c_B は branch 2 の穴 ⊆ E₁
      apply hcaseA
      refine sub_gset _ _ (HkOF_sub_EsetOF_succ a p 0 c ?_)
      refine mem_HkOF_of_allowed (k := 0) hS hcB.2.1.1.2 hcB.2.1.1.1 ?_ pd.hpiece
        (show p 2 ≤ v by omega) pd.hGd (mem_gfun q T _ _) hcB.2
      exact not_mem_gset_D1slabOF hc hfc a (by omega) hS pd.hS2 (by rw [pd.hS2lab]; omega)
        hcB.2.1.1.2 hcB.2.1.2
    · -- n = 3
      have hnD : pd.cB ∉ (EseqOF q T m y0 fc a p 1).2 c := by
        show pd.cB ∉ gset q T (p 1) (D1slabOF q T m y0 fc a c) ∪
          gset q T (p 2) (HkOF q T m y0 fc a p 0 (EseqOF q T m y0 fc a p 0).2 c)
        rintro (h | h)
        · exact not_mem_gset_D1slabOF hc hfc a (by omega) hS pd.hS2
            (by rw [pd.hS2lab]; omega) hcB.2.1.1.2 hcB.2.1.2 h
        · exact not_mem_gset_HkOF hc (by omega) hS pd.hS2 (by rw [pd.hS2lab]; omega) hcB.2.1.1.2
            hcB.2.1.2 h
      have hhole : ∀ u, u ∈ gfun q T L pd.cB → u ∈ slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3 →
          u ∈ HkOF q T m y0 fc a p 1 (EseqOF q T m y0 fc a p 1).2 c := fun u huB huP =>
        mem_HkOF_of_allowed (k := 1) hS hcB.2.1.1.2 hcB.2.1.1.1 hnD pd.hpiece
          (show p 3 ≤ v by omega) pd.hGd huB huP
      by_cases hcG : pd.cB ∈ G
      · -- c_B ∈ V かつ c_B は穴
        have hcE1 : pd.cB ∉ E1 := fun h => hcaseA (sub_gset _ _ h)
        set p' : ℕ → ℕ := fun j => if j ≤ 2 then p j else max (p j) (v + 1) with hp'def
        have hp' : AdmT m p' := by
          refine ⟨fun i j hij => ?_, ?_, ?_, ?_⟩
          · simp only [hp'def]
            have := hp.1 hij
            split_ifs <;> omega
          all_goals (have := hp.2.2.1; simp only [hp'def]; split_ifs <;> omega)
        have hz2 : ∀ c', pd.cB ∉ HkOF q T m y0 fc a p' 1 (EseqOF q T m y0 fc a p' 1).2 c' := by
          intro c' h
          obtain ⟨S', Pv', B', hS', hP', hidx', -, -, hcP'⟩ := mem_HkOF h
          have hPP := piece_unique hc hS hS' pd.hpiece hP' hcB.2 hcP'
          subst hPP
          have : p' 3 ≤ v := hidx'
          simp only [hp'def] at this
          split_ifs at this <;> omega
        have hncl : pd.cB ∉ @closure _ τ S1 :=
          not_mem_closure_k1 hc hm haA ha hp hp' hp13 hgap
            (fun j hj => by simp only [hp'def]; rw [ite_eq_left hj]) (by simp only [hp'def]; split_ifs <;> omega)
            hS pd.hS2 (by rw [pd.hS2lab]; omega) hcB.2.1.1.1 hcB.2.1.1.2 hcB.2.1.2 hcaseA hz2
            (show m + 5 < L by omega)
            (fun u hu hum => HkOF_sub_EsetOF_succ a p 1 c
              (hhole u hu (inP_of_box pd hc hm hS hL5 hu hum)))
        have hcV : pd.cB ∈ V := ⟨⟨hcG, hcE1⟩, hncl⟩
        have hcH : pd.cB ∈ HolesW q T m y0 fc a p 3 := by
          unfold HolesW
          rw [ite_eq_right (show (3:ℕ) ≠ 1 by omega)]
          exact Set.mem_iUnion.mpr ⟨c, hhole _ (mem_gfun q T _ _) hcB.2⟩
        let _ := τ
        exact (hfine _ (mem_RegionW_of_pd pd (by omega) hcB)).2 hcH (subset_closure hcV)
      · -- c_B ∉ G: K-trick で G の外の穴でない点
        have hK : lvl q b y0 < lvl q L pd.cB := by
          have : lvl q b y0 ≤ v := by omega
          omega
        obtain ⟨w, hw, hwB, hwk⟩ := ktrick pd hc ha hm hK
        refine hbad w hw hwB (fun hwV => hcG ?_)
        exact mem_gcBox_of_agree hwV.1.1 (fun k hk => (hwk k hk).symm)

/-- 具体例: α(i) = 3i+1、p = (1, 3m+20, 3m+20, 3m+21, 3m+21, …)。fcAdv は妥当な選択関数（`Defs.D_0069.validFC_fcAdv`）。 -/
theorem prop83_counterexampleS_example [Countable α] [NoMaxOrder α] (hc : Compat2 q T)
    (hm : 0 < m) (A : Set (ℕ → ℕ)) (haA : (fun i => 3 * i + 1) ∈ A) {cc : ℕ} (hcc : 0 < cc)
    (b : ℕ) :
    let p : ℕ → ℕ := fun j => if j = 0 then 1 else if j ≤ 2 then 3 * m + 20 else 3 * m + 21
    AdmT m p ∧
    @IsOpen _ (tauTF q T m y0 (fcAdv q T (p 3) m) A)
      (Vcex q T m y0 A (fun i => 3 * i + 1) p cc b) ∧
    y0 ∈ Vcex q T m y0 A (fun i => 3 * i + 1) p cc b ∧
    gcBox q T cc b y0 \ EsetOF q T m y0 (fcAdv q T (p 3) m) (fun i => 3 * i + 1) p 2 ⊆
      Vcex q T m y0 A (fun i => 3 * i + 1) p cc b ∧
    Vcex q T m y0 A (fun i => 3 * i + 1) p cc b ⊆
      gcBox q T cc b y0 \ EsetOF q T m y0 (fcAdv q T (p 3) m) (fun i => 3 * i + 1) p 1 ∧
    ¬ FineS q T m y0 (fcAdv q T (p 3) m) A (fun i => 3 * i + 1) p 3
      (Vcex q T m y0 A (fun i => 3 * i + 1) p cc b) := by
  intro p
  have hp : AdmT m p := by
    refine ⟨fun i j hij => ?_, ?_, ?_, ?_⟩
    · show (if i = 0 then 1 else if i ≤ 2 then 3 * m + 20 else 3 * m + 21) ≤
        (if j = 0 then 1 else if j ≤ 2 then 3 * m + 20 else 3 * m + 21)
      have : i ≤ j := hij
      split_ifs <;> omega
    all_goals (simp [p] <;> omega)
  exact ⟨hp, prop83_counterexampleS hc hm haA (fun i j h => by show 3 * i + 1 < 3 * j + 1; omega)
    hp (by simp [p])
    (fun v => by simp [p]; omega) hcc b⟩

end Defs.D_0074
