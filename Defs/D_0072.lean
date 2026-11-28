import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0071

namespace Defs.D_0072

/-!
**K-trick・穴の補題・E ∩ H₀ = ∅**（Prop 8.3 の反例の部品）。

`PieceData`（`Defs.D_0071`）の深い穴の箱 B = g(L, c_B)（L = α(m+v)+1）について:
* `ktrick` : 任意の K₁ < lvl L c_B について、S0 ∩ P の点 w ∉ B で先頭 K₁ 座標が c_B と一致するものがある。
* `inP_of_box` : B の点で先頭 m 座標が c_B と一致するものは piece P の点。
* `not_mem_HkOF_of_pd` : (S0 ∩ P) − B の点はどの穴（HkOF）にも入らない。
* `not_mem_gset_HkOF` : branch が k+2 でない点は、同じ slab の穴 HkOF k の g[N, ·] に入らない。
* `mem_HkOF_of_allowed` : slab c の元 S に prevD c の外の点があれば、S の穴のセルは HkOF に入る。
* `y0_not_mem_EsetOF` : y₀ はどの E にも入らない（E ∩ H₀ = ∅）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0040 Defs.D_0043 Defs.D_0049 Defs.D_0050
  Defs.D_0051 Defs.D_0056 Defs.D_0060 Defs.D_0062 Defs.D_0064 Defs.D_0065 Defs.D_0066 Defs.D_0067
  Defs.D_0068 Defs.D_0070 Defs.D_0071

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

theorem gfun_mem_of_agree {n : ℕ} {u x w : ℕ → α} (hx : x ∈ gfun q T n u)
    (h : ∀ k < lvl q n u, w k = x k) : w ∈ gfun q T n u := by
  have hn : n < lvl q n u := by unfold lvl; omega
  refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · rw [h k (by omega)]; exact hx.1 k hk
  · rw [h k hk2]; exact hx.2 k hk1 hk2

theorem gfun_chain (hc : Compat2 q T) {N L : ℕ} (hN : 0 < N) (hNL : N ≤ L) {w u x : ℕ → α}
    (hw : w ∈ gfun q T L u) (hu : u ∈ gfun q T N x) : w ∈ gfun q T N x :=
  gfun_trans hc hN hu (gfun_anti hc hN hNL u hw)

theorem mem_lncA_of_box (hc : Compat2 q T) {N L : ℕ} (hN : 0 < N) (hNL : N ≤ L)
    {X Y : Set (ℕ → α)} (hX : X ∈ lncA q T N Y) {u w : ℕ → α} (hu : u ∈ X)
    (hw : w ∈ gfun q T L u) : w ∈ X := by
  obtain ⟨xX, -, rfl, -⟩ := hX
  exact gfun_chain hc hN hNL hw hu

theorem lvl_mono (hc : Compat2 q T) {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) {e x : ℕ → α}
    (hx : x ∈ gfun q T n e) : lvl q n e ≤ lvl q N x := by
  have h1 := hidx_le_of_mem_gfun hc hn hx
  have h2 := code_mono n hn (fun k => q.symm (x k)) N hnN
  unfold lvl hidx at *; omega

section pd

variable {a : ℕ → ℕ} {P3 c : ℕ} {S : Set (ℕ → α)} {n v : ℕ}

theorem pd_cB_mem (pd : PieceData q T m y0 a P3 c S n v) :
    pd.cB ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3) := pd.hdeep.1

theorem pd_mem_region (pd : PieceData q T m y0 a P3 c S n v) {w : ℕ → α}
    (hw : w ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3)) : w ∈ pd.M5 := pd.hS0M5 hw.1

theorem ktrick (pd : PieceData q T m y0 a P3 c S n v) (hc : Compat2 q T) (ha : StrictMono a)
    (hm : 0 < m) {K1 : ℕ} (hK1 : K1 < lvl q (a (m + v) + 1) pd.cB) :
    ∃ w, w ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3) ∧
      w ∉ gfun q T (a (m + v) + 1) pd.cB ∧ ∀ k < K1, w k = pd.cB k := by
  have hcB := pd_cB_mem pd
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

theorem inP_of_box (pd : PieceData q T m y0 a P3 c S n v) (hc : Compat2 q T) (hm : 0 < m)
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c)) (hL : m + 5 ≤ a (m + v) + 1) {u : ℕ → α}
    (hu : u ∈ gfun q T (a (m + v) + 1) pd.cB) (hum : ∀ k < m, u k = pd.cB k) :
    u ∈ slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3 := by
  have hcB := (pd_cB_mem pd).2
  have hcs := slabO_hidx hcB.1.1.1
  have hslab : slabO q T m y0 c = H q m c ∩ gfun q T m y0 := by
    unfold slabO; rw [ite_eq_right hcs.2]; rfl
  have huc : u ∈ slabO q T m y0 c := by
    rw [hslab]
    refine ⟨?_, gfun_chain hc hm (by omega) hu (slabO_sub_Gm hcB.1.1.1)⟩
    show hidx q m u = c
    have : hidx q m u = hidx q m pd.cB := (code_eq_iff m hm _ _).2 (fun k hk => by
      show q.symm (u k) = q.symm (pd.cB k); rw [hum k hk])
    exact this.trans hcs.1
  exact ⟨⟨⟨huc, mem_lncA_of_box hc (by omega) (by omega) hS hcB.1.1.2 hu⟩,
    mem_lncA_of_box hc (by omega) (by omega) pd.hS2 hcB.1.2 hu⟩,
    mem_lncA_of_box hc (by omega) (by omega) pd.hS3 hcB.2 hu⟩

theorem not_mem_HkOF_of_pd (pd : PieceData q T m y0 a P3 c S n v) (hc : Compat2 q T)
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c)) (hL : m + 5 ≤ a (m + v) + 1) {w : ℕ → α}
    (hw : w ∈ pd.S0 ∩ (slabO q T m y0 c ∩ S ∩ pd.S2 ∩ pd.S3))
    (hwB : w ∉ gfun q T (a (m + v) + 1) pd.cB) (p : ℕ → ℕ) (k : ℕ)
    (prevD : ℕ → Set (ℕ → α)) (c' : ℕ) :
    w ∉ HkOF q T m y0 (fcAdv q T P3 m) a p k prevD c' := by
  intro h
  obtain ⟨S', Pv', B', hS', hP', -, hB', hwB', hwP'⟩ := mem_HkOF h
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

end pd

section holes

variable {fc : ℕ → Set (ℕ → α) → Set (ℕ → α)}

theorem HkOF_sub_slab {a p : ℕ → ℕ} {k : ℕ} {prevD : ℕ → Set (ℕ → α)} {i : ℕ} :
    HkOF q T m y0 fc a p k prevD i ⊆ slabO q T m y0 i := by
  intro x hx
  obtain ⟨S, Pv, B, -, hP, -, -, -, hxP⟩ := mem_HkOF hx
  obtain ⟨S2, -, -, S3, -, -, hPe⟩ := hP
  rw [hPe] at hxP; exact hxP.1.1.1

theorem not_mem_gset_HkOF (hc : Compat2 q T) {a p : ℕ → ℕ} {k c N : ℕ}
    {prevD : ℕ → Set (ℕ → α)} (hN : m + 2 ≤ N) {S S2 : Set (ℕ → α)}
    (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c))
    (hS2 : S2 ∈ lncA q T (m + 2) (slabO q T m y0 c ∩ S))
    (hlab : lab (lncA q T (m + 2) (slabO q T m y0 c ∩ S)) S2 ≠ k + 2) {w : ℕ → α}
    (hwS : w ∈ S) (hwS2 : w ∈ S2) :
    w ∉ gset q T N (HkOF q T m y0 fc a p k prevD c) := by
  intro hw
  obtain ⟨d, hd, hwd⟩ := Set.mem_iUnion₂.mp hw
  obtain ⟨S', Pv, B, hS', hP, -, -, -, hdP⟩ := mem_HkOF hd
  obtain ⟨S2', hS2', hlab', S3', -, -, hPe⟩ := hP
  rw [hPe] at hdP
  have hwS2' : w ∈ S2' := mem_lncA_of_box hc (by omega) hN hS2' hdP.1.2 hwd
  have hS2'S' : S2' ⊆ S' := by
    obtain ⟨x2, hx2, rfl, -⟩ := id hS2'
    obtain ⟨x1, -, rfl, -⟩ := id hS'
    exact (gfun_anti hc (by omega) (by omega) x2).trans (gfun_trans hc (by omega) hx2.2)
  have hSS : S' = S := lncA_unique hc hS' hS (hS2'S' hwS2') hwS
  subst hSS
  have h22 : S2' = S2 := lncA_unique hc hS2' hS2 hwS2' hwS2
  subst h22
  exact hlab hlab'

theorem mem_HkOF_of_allowed {a p : ℕ → ℕ} {k c : ℕ} {prevD : ℕ → Set (ℕ → α)}
    {S : Set (ℕ → α)} (hS : S ∈ lncA q T (m + 1) (slabO q T m y0 c)) {x : ℕ → α}
    (hxS : x ∈ S) (hxc : x ∈ slabO q T m y0 c) (hxD : x ∉ prevD c)
    {Pv : Set (ℕ → α) × ℕ} (hP : Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) (k + 2))
    (hPv : p (k + 2) ≤ Pv.2) {B : Set (ℕ → α)} (hB : B ∈ GdF q T m fc a Pv.1 Pv.2)
    {u : ℕ → α} (huB : u ∈ B) (huP : u ∈ Pv.1) : u ∈ HkOF q T m y0 fc a p k prevD c := by
  unfold HkOF slabRec
  refine Set.mem_iUnion₂.mpr ⟨S, ⟨hS, x, hxS, hxc, ?_⟩, ?_⟩
  · rintro (h | h)
    · rw [slabCum_eq] at h
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp h
      have hxs : x ∈ slabO q T m y0 i :=
        HkOF_sub_slab (fc := fc) (a := a) (p := p) (k := k) (prevD := prevD) hxi
      exact Set.disjoint_left.mp (slabO_disjoint (ne_of_lt (Finset.mem_range.mp hi))) hxs hxc
    · exact hxD h
  · simp only [holeCellsF, Set.mem_iUnion, exists_prop]
    exact ⟨Pv, ⟨hP, hPv⟩, B, hB, huB, huP⟩

theorem EsetOF_sub_succ (a p : ℕ → ℕ) (k : ℕ) :
    EsetOF q T m y0 fc a p k ⊆ EsetOF q T m y0 fc a p (k + 1) := by
  rw [EsetOF_succ]; exact (sub_gset _ _).trans Set.subset_union_left

theorem gset_sub_EsetOF_succ (a p : ℕ → ℕ) (k : ℕ) :
    gset q T (p (k + 2)) (EsetOF q T m y0 fc a p k) ⊆ EsetOF q T m y0 fc a p (k + 1) := by
  rw [EsetOF_succ]; exact Set.subset_union_left

theorem HkOF_sub_EsetOF_succ (a p : ℕ → ℕ) (k c : ℕ) :
    HkOF q T m y0 fc a p k (EseqOF q T m y0 fc a p k).2 c ⊆ EsetOF q T m y0 fc a p (k + 1) := by
  rw [EsetOF_succ]; exact (Set.subset_iUnion (fun c => HkOF q T m y0 fc a p k _ c) c).trans
    Set.subset_union_right

/-! ### E ∩ H₀ = ∅ -/

variable (q T m y0) in
/-- O の点を中心とする第 N ≥ m 層の箱に入る点の集合。 -/
def OBox (X : Set (ℕ → α)) : Prop :=
  ∀ x ∈ X, ∃ c N u, m ≤ N ∧ u ∈ slabO q T m y0 c ∧ x ∈ gfun q T N u

theorem OBox_gset (hc : Compat2 q T) (hm : 0 < m) {p : ℕ} (hp : m ≤ p) {X : Set (ℕ → α)}
    (hX : OBox q T m y0 X) : OBox q T m y0 (gset q T p X) := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨c, N, u, hN, hu, heu⟩ := hX e he
  have h0 : 0 < min p N := lt_min (by omega) (by omega)
  refine ⟨c, min p N, u, le_min hp hN, hu, ?_⟩
  exact gfun_trans hc h0 (gfun_anti hc h0 (min_le_right _ _) u heu)
    (gfun_anti hc h0 (min_le_left _ _) e hxe)

theorem OBox_D1OF (hfc : WeakFC q T fc) (a : ℕ → ℕ) : OBox q T m y0 (D1OF q T m y0 fc a) := by
  intro d hd
  obtain ⟨c, S, Pv, B, -, hP, hB, hdB, -⟩ := mem_D1OF_box hd
  rcases GdF_rep hfc hB with h | ⟨L, u, hL, hu, rfl⟩
  · rw [h] at hdB; exact absurd hdB (Set.notMem_empty _)
  · obtain ⟨S2, -, -, S3, -, -, hPe⟩ := hP
    rw [hPe] at hu
    exact ⟨c, L, u, by omega, hu.1.1.1, hdB⟩

theorem OBox_EsetOF (hc : Compat2 q T) (hm : 0 < m) (hfc : WeakFC q T fc) (a : ℕ → ℕ)
    {p : ℕ → ℕ} (hp : AdmT m p) : ∀ k, OBox q T m y0 (EsetOF q T m y0 fc a p k)
  | 0 => by
    rw [EsetOF_zero]; exact OBox_gset hc hm (by have := hp.2.1; omega) (OBox_D1OF hfc a)
  | k + 1 => by
    rw [EsetOF_succ]
    rintro x (hx | hx)
    · have hpk : p 1 ≤ p (k + 2) := hp.1 (by omega)
      exact OBox_gset hc hm (by have := hp.2.1; omega) (OBox_EsetOF hc hm hfc a hp k) x hx
    · obtain ⟨c, hxc⟩ := Set.mem_iUnion.mp hx
      exact ⟨c, m, x, le_rfl, HkOF_sub_slab hxc, mem_gfun q T m x⟩

theorem y0_not_mem_OBox (hc : Compat2 q T) (hm : 0 < m) {X : Set (ℕ → α)}
    (hX : OBox q T m y0 X) : y0 ∉ X := by
  intro hy
  obtain ⟨c, N, u, hN, hu, hyu⟩ := hX y0 hy
  exact y0_not_mem_box hc hm hN le_rfl hu hyu (mem_gfun q T m y0)

theorem y0_not_mem_EsetOF (hc : Compat2 q T) (hm : 0 < m) (hfc : WeakFC q T fc) (a : ℕ → ℕ)
    {p : ℕ → ℕ} (hp : AdmT m p) (k : ℕ) : y0 ∉ EsetOF q T m y0 fc a p k :=
  y0_not_mem_OBox hc hm (OBox_EsetOF hc hm hfc a hp k)

end holes

end Defs.D_0072
