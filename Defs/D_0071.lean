import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0070
import Defs.D_0056

namespace Defs.D_0071

/-!
**piece の組み立て**（Prop 8.3 の反例の部品）。任意の slab c の元 S、branch 番号 n、piece 番号 v について、
branch n の元 S2、piece 番号 v の元 S3（piece P = A1 ∩ S2 ∩ S3、A1 = slabO c ∩ S）、
ch-box M5（ラベル (α v, α v + 1)）、M5 に含まれる第 α(m+v) 層の元 S0 = g(α(m+v), x0)、
fcAdv の深い箱 B = g(L, c_B)（L = α(m+v)+1 ≥ p₃+2、B ∈ G_d(P, v)）を作る（`piece_builder`）。
Ln cover の無限性は `Defs.D_0056.Good` で処理する。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0040 Defs.D_0050 Defs.D_0051
  Defs.D_0056 Defs.D_0060 Defs.D_0062 Defs.D_0064 Defs.D_0065 Defs.D_0066 Defs.D_0067 Defs.D_0068

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

/-- 組み立ての結果。 -/
structure PieceData (q : ℕ ≃ α) (T : Tree2 α) (m : ℕ) (y0 : ℕ → α) (a : ℕ → ℕ) (P3 : ℕ)
    (c : ℕ) (S : Set (ℕ → α)) (n v : ℕ) where
  S2 : Set (ℕ → α)
  S3 : Set (ℕ → α)
  M5 : Set (ℕ → α)
  S0 : Set (ℕ → α)
  x0 : ℕ → α
  cB : ℕ → α
  yB : ℕ → α
  hS2 : S2 ∈ lncA q T (m + 2) (slabO q T m y0 c ∩ S)
  hS2lab : lab (lncA q T (m + 2) (slabO q T m y0 c ∩ S)) S2 = n
  hS3 : S3 ∈ lncA q T (m + 3) (slabO q T m y0 c ∩ S ∩ S2)
  hpiece : (slabO q T m y0 c ∩ S ∩ S2 ∩ S3, v) ∈ pieces q T m (slabO q T m y0 c ∩ S) n
  hM5 : M5 ∈ chBoxes q T m a (slabO q T m y0 c ∩ S ∩ S2 ∩ S3) v
  hS0 : S0 ∈ lncA q T (a (m + v)) (slabO q T m y0 c ∩ S ∩ S2 ∩ S3)
  hS0e : S0 = gfun q T (a (m + v)) x0
  hx0 : x0 ∈ slabO q T m y0 c ∩ S ∩ S2 ∩ S3
  hS0M5 : S0 ⊆ M5
  hgood : Good q T (S0 ∩ (slabO q T m y0 c ∩ S ∩ S2 ∩ S3)) (a (m + v)) x0
  hfc : fcAdv q T P3 m (a (m + v) + 1) (S0 ∩ (slabO q T m y0 c ∩ S ∩ S2 ∩ S3)) =
    gfun q T (a (m + v) + 1) cB
  hdeep : DeepWit q T (a (m + v) + 1) m (S0 ∩ (slabO q T m y0 c ∩ S ∩ S2 ∩ S3)) cB yB
  hGd : gfun q T (a (m + v) + 1) cB ∈
    GdF q T m (fcAdv q T P3 m) a (slabO q T m y0 c ∩ S ∩ S2 ∩ S3) v

theorem piece_builder [Countable α] [NoMaxOrder α] (hc : Compat2 q T) (hm : 0 < m)
    {a : ℕ → ℕ} (ha : StrictMono a) {P3 c : ℕ} {S : Set (ℕ → α)}
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c)) (n v : ℕ) (hL : P3 + 2 ≤ a (m + v) + 1)
    (hv : 5 ≤ v) :
    Nonempty (PieceData q T m y0 a P3 c S n v) := by
  obtain ⟨x1, hx1, hSe, -⟩ := id hS
  have hc0 : c ≠ hidx q m y0 := by
    intro h; unfold slabO at hx1; rw [if_pos h] at hx1; exact hx1
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
  obtain ⟨S2B, hS2B, -, S3B, hS3B, -, hPe⟩ := id hpiece
  have hshift : ShiftOK q T (S0 ∩ P) (a (m + v) + 1 - 1) m := by
    refine ShiftOK_inter (ShiftOK_lncA hc (n := a (m + v)) (by omega) (by omega) hS0mem) ?_
    refine ShiftOK_inter (ShiftOK_inter (ShiftOK_inter
      (ShiftOK_slabO hc hm (by omega) le_rfl y0 c)
      (ShiftOK_lncA hc (by omega) (by omega) hS))
      (ShiftOK_lncA hc (by omega) (by omega) hS2mem))
      (ShiftOK_lncA hc (by omega) (by omega) hS3mem)
  have hne0 : (S0 ∩ P).Nonempty := ⟨x0, by rw [hS0eq]; exact mem_gfun q T _ x0, hx0⟩
  obtain ⟨cB, yB, hfcz, hdeep⟩ :=
    fcAdv_deep hc (p1 := P3) hL hne0 hshift (show m < a (m + v) + 1 by omega)
  have hGd : gfun q T (a (m + v) + 1) cB ∈ GdF q T m (fcAdv q T P3 m) a P v := by
    unfold GdF
    rw [if_pos (by omega : m + 5 ≤ a (m + v) + 1)]
    exact ⟨⟨S0, hS0mem, hfcz.symm⟩, cB, mem_gfun q T _ cB,
      Set.mem_sUnion.mpr ⟨M5, hch, hS0M5 hdeep.1.1⟩⟩
  exact ⟨⟨S2, S3, M5, S0, x0, cB, yB, hS2mem, hS2lab, hS3mem, hpiece, hch, hS0mem, hS0eq, hx0,
    hS0M5, hgS0, hfcz, hdeep, hGd⟩⟩

end Defs.D_0071
