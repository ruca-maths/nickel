import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0062
import Defs.D_0063
import Defs.D_0048

namespace Defs.D_0065

/-!
一般化版（選択関数 fc、`Defs.D_0062`）の構造補題。D_0048, D_0056, D_0057, D_0061, D_0063 の移植。

* `WeakFC fc` : fc n A は ∅ か lncA n A の元。
* `GdF_cases`, `GdF_rep`, `D1slabOF_eq`, `mem_D1OF_box`, `not_mem_gset_D1slabOF`,
  `D1OF_sub_EsetOF`, `EsetOF_zero`, `EsetOF_succ`。
* `not_mem_closure_of_maxKillF`, `killNbhd_isOpenF` : 判定法と切り離し近傍の τ-開性（一般化版）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0034 Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0040 Defs.D_0043
  Defs.D_0048 Defs.D_0062

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}
  {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)}

variable (q T) in
def WeakFC (fc : ℕ → Set (ℕ → α) → Set (ℕ → α)) : Prop :=
  ∀ n A, fc n A = ∅ ∨ fc n A ∈ lncA q T n A

theorem GdF_cases {a : ℕ → ℕ} {P : Set (ℕ → α)} {v : ℕ} {B : Set (ℕ → α)}
    (hB : B ∈ GdF q T m fc a P v) :
    (m + 5 ≤ a (m + v) + 1 ∧ ∃ S ∈ lncA q T (a (m + v)) P, B = fc (a (m + v) + 1) (S ∩ P)) ∨
      B ∈ chBoxes q T m a P v := by
  unfold GdF at hB
  split_ifs at hB with hlev
  · obtain ⟨⟨S, hS, rfl⟩, -⟩ := hB
    exact Or.inl ⟨hlev, S, hS, rfl⟩
  · exact Or.inr hB

theorem GdF_rep (hfc : WeakFC q T fc) {a : ℕ → ℕ} {P : Set (ℕ → α)} {v : ℕ}
    {B : Set (ℕ → α)} (hB : B ∈ GdF q T m fc a P v) :
    B = ∅ ∨ ∃ L u, m + 5 ≤ L ∧ u ∈ P ∧ B = gfun q T L u := by
  rcases GdF_cases hB with ⟨hlev, S, -, rfl⟩ | hB'
  · rcases hfc (a (m + v) + 1) (S ∩ P) with h | h
    · exact Or.inl h
    · obtain ⟨u, hu, he, -⟩ := h
      exact Or.inr ⟨_, u, hlev, hu.2, he⟩
  · obtain ⟨S, -, hB'', -⟩ := hB'
    obtain ⟨u, hu, he, -⟩ := hB''
    exact Or.inr ⟨m + 5, u, le_rfl, hu.2, he⟩

theorem D1slabOF_eq (a : ℕ → ℕ) (c : ℕ) :
    D1slabOF q T m y0 fc a c =
      ⋃ S ∈ allowedO q T m y0 c (⋃ i ∈ Finset.range c, D1slabOF q T m y0 fc a i),
        holeBoxesUF q T m fc a 1 0 (slabO q T m y0 c ∩ S) := by
  conv_lhs => rw [D1slabOF, slabRec, slabCum_eq]
  rfl

/-- D の点は、D に含まれる G_d の箱に入る（箱の出自つき）。 -/
theorem mem_D1OF_box {a : ℕ → ℕ} {d : ℕ → α} (hd : d ∈ D1OF q T m y0 fc a) :
    ∃ c S Pv B, S ∈ allowedO q T m y0 c (⋃ i ∈ Finset.range c, D1slabOF q T m y0 fc a i) ∧
      Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) 1 ∧ B ∈ GdF q T m fc a Pv.1 Pv.2 ∧
      d ∈ B ∧ B ⊆ D1OF q T m y0 fc a := by
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hd
  rw [D1slabOF_eq] at hc
  obtain ⟨S, hS, hdS⟩ := Set.mem_iUnion₂.mp hc
  unfold holeBoxesUF at hdS
  obtain ⟨Pv, hPv, B, hB, hdB⟩ := by
    simpa only [Set.mem_iUnion, Set.mem_sUnion, exists_prop] using hdS
  refine ⟨c, S, Pv, B, hS, hPv.1, hB, hdB, fun w hw => ?_⟩
  refine Set.mem_iUnion.mpr ⟨c, ?_⟩
  rw [D1slabOF_eq]
  refine Set.mem_iUnion₂.mpr ⟨S, hS, ?_⟩
  unfold holeBoxesUF
  simp only [Set.mem_iUnion, Set.mem_sUnion, exists_prop]
  exact ⟨Pv, hPv, B, hB, hw⟩

theorem not_mem_gset_D1slabOF (hc : Compat2 q T) (hfc : WeakFC q T fc) (a : ℕ → ℕ) {c p : ℕ}
    (hp : m + 2 ≤ p) {S S2 : Set (ℕ → α)} (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c))
    (hS2 : S2 ∈ lncA q T (m + 2) (slabO q T m y0 c ∩ S))
    (hlab : lab (lncA q T (m + 2) (slabO q T m y0 c ∩ S)) S2 ≠ 1)
    {w : ℕ → α} (hwS : w ∈ S) (hwS2 : w ∈ S2) :
    w ∉ gset q T p (D1slabOF q T m y0 fc a c) := by
  intro hw
  obtain ⟨d, hd, hwd⟩ := Set.mem_iUnion₂.mp hw
  unfold D1slabOF slabRec at hd
  obtain ⟨S'', hS''a, hdU⟩ := Set.mem_iUnion₂.mp hd
  simp only [holeBoxesUF, Set.mem_iUnion, Set.mem_sUnion, exists_prop] at hdU
  obtain ⟨Pv, ⟨hPv, -⟩, B, hB, hdB⟩ := hdU
  obtain ⟨S2'', hS2'', hlab'', S3, hS3, -, hPe⟩ := hPv
  have hS'' : S'' ∈ lncA q T (m + 1) (slabO q T m y0 c) := hS''a.1
  have hBS2 : B ⊆ S2'' := by
    rcases GdF_rep hfc hB with h | ⟨L, u, hL, hu, rfl⟩
    · rw [h]; exact Set.empty_subset _
    · rw [hPe] at hu
      refine (gfun_anti hc (by omega) (show m + 2 ≤ L by omega) u).trans ?_
      obtain ⟨x2, -, rfl, -⟩ := hS2''
      exact gfun_trans hc (by omega) hu.1.2
  have hdS2 : d ∈ S2'' := hBS2 hdB
  have hgS2 : gfun q T p d ⊆ S2'' := by
    obtain ⟨x2, -, rfl, -⟩ := id hS2''
    exact (gfun_anti hc (by omega) hp d).trans (gfun_trans hc (by omega) hdS2)
  have hwS2'' : w ∈ S2'' := hgS2 hwd
  have hS2S'' : S2'' ⊆ S'' := by
    obtain ⟨x2, hx2, rfl, -⟩ := id hS2''
    obtain ⟨x1, -, rfl, -⟩ := id hS''
    exact (gfun_anti hc (by omega) (show m + 1 ≤ m + 2 by omega) x2).trans
      (gfun_trans hc (by omega) hx2.2)
  have hSS : S'' = S := lncA_unique hc hS'' hS (hS2S'' hwS2'') hwS
  subst hSS
  have h22 : S2'' = S2 := lncA_unique hc hS2'' hS2 hwS2'' hwS2
  subst h22
  exact hlab hlab''

theorem EsetOF_zero (a p : ℕ → ℕ) :
    EsetOF q T m y0 fc a p 0 = gset q T (p 1) (D1OF q T m y0 fc a) := rfl

theorem EsetOF_succ (a p : ℕ → ℕ) (k : ℕ) :
    EsetOF q T m y0 fc a p (k + 1) = gset q T (p (k + 2)) (EsetOF q T m y0 fc a p k) ∪
      ⋃ c, HkOF q T m y0 fc a p k (EseqOF q T m y0 fc a p k).2 c := rfl

theorem D1OF_sub_EsetOF (a p : ℕ → ℕ) : ∀ k, D1OF q T m y0 fc a ⊆ EsetOF q T m y0 fc a p k
  | 0 => by rw [EsetOF_zero]; exact sub_gset _ _
  | k + 1 => by
    rw [EsetOF_succ]
    exact (D1OF_sub_EsetOF a p k).trans ((sub_gset _ _).trans Set.subset_union_left)

theorem isOpen_tauF_of_mem {A : Set (ℕ → ℕ)} {s : Set (ℕ → α)}
    (hs : s ∈ tauSubTF q T m y0 fc A) : @IsOpen _ (tauTF q T m y0 fc A) s :=
  TopologicalSpace.GenerateOpen.basic _ hs

theorem killNbhd_isOpenF {A : Set (ℕ → ℕ)} {a : ℕ → ℕ} (ha : a ∈ A) {p p' : ℕ → ℕ}
    (hp : AdmT m p) (hp' : AdmT m p') {ℓ ℓ' ph : ℕ} (hℓ0 : 0 < ℓ) (hℓ' : m + 5 < ℓ')
    (hph : p 2 < ph) (z x : ℕ → α) :
    @IsOpen _ (tauTF q T m y0 fc A)
      (gfun q T ℓ z ∩ (EsetOF q T m y0 fc a p' 1)ᶜ ∩
        (gset q T ph (gfun q T ℓ' x \ EsetOF q T m y0 fc a p 1))ᶜ) := by
  let _ := tauTF q T m y0 fc A
  refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
  · exact isOpen_tauF_of_mem (Or.inl (Or.inl ⟨ℓ, z, hℓ0, Or.inl rfl⟩))
  · exact isOpen_tauF_of_mem (Or.inl (Or.inr ⟨a, ha, p', hp', 0, Or.inr rfl⟩))
  · exact isOpen_tauF_of_mem (Or.inr ⟨a, ha, p, hp, 0, ℓ', ph, x, hℓ', hph, Or.inr rfl⟩)

/-- 判定法の極大箱版（一般化版）。 -/
theorem not_mem_closure_of_maxKillF (hc : Compat2 q T) {A : Set (ℕ → ℕ)} {a : ℕ → ℕ}
    {p : ℕ → ℕ} (hp : AdmT m p) {z : ℕ → α} {U : Set (ℕ → α)}
    (hU : @IsOpen _ (tauTF q T m y0 fc A) U) (hzU : z ∈ U) {ℓ : ℕ} (hUℓ : U ⊆ gfun q T ℓ z)
    {K : Set (ℕ → α)} (hUK : Disjoint U K)
    (hkill : ∀ M ∈ lncA q T (p 1) (D1OF q T m y0 fc a), M ∩ gfun q T ℓ z ⊆ K) :
    z ∉ @closure _ (tauTF q T m y0 fc A) (gset q T (p 2) (EsetOF q T m y0 fc a p 0)) := by
  let _ := tauTF q T m y0 fc A
  have hp1 : 0 < p 1 := lt_of_le_of_lt (Nat.zero_le _) (by have := hp.2.1; omega)
  have hp12 : p 2 = p 1 := hp.2.2.2.symm
  refine not_mem_closure_of_disjoint _ hU hzU ?_
  rw [Set.disjoint_left]
  intro w hwU hwS
  have hwS' : w ∈ gset q T (p 1) (D1OF q T m y0 fc a) := by
    rw [hp12, EsetOF_zero] at hwS
    exact gset_gsetT hc hp1 le_rfl _ hwS
  rw [← lncA_sUnion hc] at hwS'
  obtain ⟨M, hM, hwM⟩ := hwS'
  exact Set.disjoint_left.mp hUK hwU (hkill M hM ⟨hwM, hUℓ hwU⟩)

end Defs.D_0065
