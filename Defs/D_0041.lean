import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Defs.D_0040

namespace Defs.D_0041

/-!
Chen–Wang (arXiv 1809.03763v2) §7 の位相 τ と **Theorem 1.a（g-関数の条件）**。

τ は論文の Definition A–C で「開かつ閉」と宣言される集合で生成する:
* ρ 由来の部分基 `rhoSub q T`（g(l, x') とその補集合）。
* E(α(k+1), p)（k ≥ 0。論文の E(α2) 以降）とその補集合（Definition A.2, B.1）。
* Definition C の g[p_h, g(ℓ, x) − E(α(k+1), p)]（ℓ > m+5, p_h > p(k+2)）とその補集合。
  論文の Definition C は x ∈ E の場合を除外していない（TeX 3938–3946 行）。
ここで α は mad family 𝒜 の元の列挙、p は許容列（単調で p 1 > m+5）。

主定理 `theorem_1a`: g(n+1, ·) は τ で開、x を含み、減少し、閉集合 H と x ∉ H に対し
ある n で x ∉ Cl_τ ⋃_{y ∈ H} g(n+1, y)（Specs.L_0017 の仮定の形。T₁ 性 `tau_t1` と合わせて
L_0017 から stratifiable）。論文の証明（TeX 5010–5040）は閉集合 Y − (g(ℓ,x) ∩ E) の場合を
Prop 7.3–7.5 に帰着しているが、その帰着は書かれていない。ここでは Definition C の集合を使って
直接示す（`E_case`）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0009 Defs.D_0012 Defs.D_0024
  Defs.D_0025 Defs.D_0029 Defs.D_0030 Defs.D_0031 Defs.D_0032 Defs.D_0034 Defs.D_0035 Defs.D_0036
  Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0040

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

/-- 許容列。 -/
def Adm (m : ℕ) (p : ℕ → ℕ) : Prop := Monotone p ∧ m + 5 < p 1 ∧ 0 < p 0

variable (q T m y0)

/-- τ の部分基。`A` は mad family（の元の列挙の集合）。 -/
noncomputable def tauSub (A : Set (ℕ → ℕ)) : Set (Set (ℕ → α)) :=
  rhoSub q T ∪
  {s | ∃ a ∈ A, ∃ p, Adm m p ∧ ∃ k,
      s = EsetO q T m y0 a p (k + 1) ∨ s = (EsetO q T m y0 a p (k + 1))ᶜ} ∪
  {s | ∃ a ∈ A, ∃ p, Adm m p ∧ ∃ k ℓ ph x, m + 5 < ℓ ∧ p (k + 2) < ph ∧
      (s = gset q T ph (gfun q T ℓ x \ EsetO q T m y0 a p (k + 1)) ∨
       s = (gset q T ph (gfun q T ℓ x \ EsetO q T m y0 a p (k + 1)))ᶜ)}

noncomputable def tau (A : Set (ℕ → ℕ)) : TopologicalSpace (ℕ → α) :=
  .generateFrom (tauSub q T m y0 A)

variable {q T m y0}

/-! ### 補助 -/

/-- 先頭の座標が一致すればセルに入る。 -/
theorem mem_Hcell_of_coord {L : ℕ} {x z : ℕ → α}
    (h : ∀ k < L + hidx q L x + 1, z k = x k) : z ∈ Hcell q T L x := by
  rw [Hcell_eq] at ⊢
  intro k hk
  rw [h k hk]
  split_ifs
  · rfl
  · exact mem_ival T (lvl_pos q L x) (x k)

/-- SOpen な A の点 x について、N が大きければ x ∈ g(N, u) ⇒ u ∈ A。 -/
theorem SOpen_pre (hc : Compat2 q T) {A : Set (ℕ → α)} (hA : SOpen q T A) {x : ℕ → α}
    (hx : x ∈ A) : ∃ N0, ∀ N, N0 ≤ N → ∀ u, x ∈ gfun q T N u → u ∈ A := by
  obtain ⟨L, -, hL⟩ := hA x hx
  obtain ⟨n1, hn1⟩ := gfun_coord_eq hc x (L + hidx q L x + 1)
  exact ⟨n1, fun N hN u hu => hL (mem_Hcell_of_coord (hn1 N hN u hu))⟩

/-- SClosed な A の外の点 x について、N が大きければ x ∉ g[N, A]。 -/
theorem SClosed_pre (hc : Compat2 q T) {A : Set (ℕ → α)} (hA : SClosed q T A) {x : ℕ → α}
    (hx : x ∉ A) : ∃ N0, ∀ N, N0 ≤ N → x ∉ gset q T N A := by
  obtain ⟨L, -, hL⟩ := hA x hx
  obtain ⟨n1, hn1⟩ := gfun_coord_eq hc x (L + hidx q L x + 1)
  refine ⟨n1, fun N hN hxN => ?_⟩
  obtain ⟨e, heA, hxe⟩ := Set.mem_iUnion₂.mp hxN
  exact Set.disjoint_left.mp hL (mem_Hcell_of_coord (hn1 N hN e hxe)) heA

theorem gset_gset (hc : Compat2 q T) {ph n : ℕ} (hph : 0 < ph) (hn : ph ≤ n) (A : Set (ℕ → α)) :
    gset q T n (gset q T ph A) ⊆ gset q T ph A := by
  intro w hw
  obtain ⟨u, hu, hwu⟩ := Set.mem_iUnion₂.mp hw
  obtain ⟨a, ha, hua⟩ := Set.mem_iUnion₂.mp hu
  exact Set.mem_biUnion ha (gfun_trans hc hph hua ((gfun_anti hc hph hn u) hwu))

/-- EseqO は p の先頭 k+2 項（添字 ≤ k+1）だけで決まる。 -/
theorem EseqO_congr (a : ℕ → ℕ) {p p' : ℕ → ℕ} :
    ∀ k, (∀ j ≤ k + 1, p j = p' j) → EseqO q T m y0 a p k = EseqO q T m y0 a p' k := by
  intro k
  induction k with
  | zero => intro h; simp only [EseqO, h 1 le_rfl]
  | succ k ih =>
    intro h
    have hprev := ih (fun j hj => h j (by omega))
    simp only [EseqO, hprev, h (k + 2) le_rfl, HkO]

/-- x を含む piece の番号より大きい r では、x は穴の和に入らない。 -/
theorem not_mem_holeU_large (hc : Compat2 q T) (a : ℕ → ℕ) (x : ℕ → α) :
    ∃ r0, ∀ r, r0 ≤ r → ∀ k (R : ℕ → Set (ℕ → α) → Prop),
      (∀ c S, R c S → S ∈ lncA q T (m + 1) (slabO q T m y0 c)) →
      x ∉ holeU q T m y0 a k r R := by
  classical
  by_cases hex : ∃ c S k' Pv, S ∈ lncA q T (m + 1) (slabO q T m y0 c) ∧
      Pv ∈ pieces q T m (slabO q T m y0 c ∩ S) k' ∧ x ∈ Pv.1
  · obtain ⟨c0, S0, k0, Pv0, hS0, hP0, hx0⟩ := hex
    refine ⟨Pv0.2 + 1, fun r hr k R hR hx => ?_⟩
    obtain ⟨c, S, hcs, Pv, ⟨hP, hrv⟩, B, -, hxB⟩ := mem_holeU.mp hx
    have := piece_unique hc (hR c S hcs) hS0 hP hP0 hxB.2 hx0
    rw [this] at hrv
    omega
  · push_neg at hex
    refine ⟨0, fun r _ k R hR hx => ?_⟩
    obtain ⟨c, S, hcs, Pv, ⟨hP, -⟩, B, -, hxB⟩ := mem_holeU.mp hx
    exact hex c S k Pv (hR c S hcs) hP hxB.2

theorem isOpen_tau_of_mem {A : Set (ℕ → ℕ)} {s : Set (ℕ → α)} (hs : s ∈ tauSub q T m y0 A) :
    @IsOpen _ (tau q T m y0 A) s := TopologicalSpace.GenerateOpen.basic _ hs

theorem isClosed_tau_of_compl_mem {A : Set (ℕ → ℕ)} {s : Set (ℕ → α)}
    (hs : sᶜ ∈ tauSub q T m y0 A) : @IsClosed _ (tau q T m y0 A) s := by
  letI := tau q T m y0 A
  exact ⟨isOpen_tau_of_mem hs⟩

/-! ### Theorem 1.a の各部分基についての条件 -/

variable [NoMaxOrder α]

/-- E(α(k+1), p) の点 x（論文で欠けている場合）。 -/
theorem E_case (hc : Compat2 q T) (hm : 0 < m) {A : Set (ℕ → ℕ)} {a : ℕ → ℕ} (ha : a ∈ A)
    {p : ℕ → ℕ} (hp : Adm m p) (k : ℕ) {x : ℕ → α} (hx : x ∈ EsetO q T m y0 a p (k + 1)) :
    ∃ n, x ∉ @closure _ (tau q T m y0 A)
      (⋃ y ∈ (EsetO q T m y0 a p (k + 1))ᶜ, gfun q T (n + 1) y) := by
  set E := EsetO q T m y0 a p (k + 1)
  have hp0 : ∀ j, 0 < p j := fun j => lt_of_lt_of_le hp.2.2 (hp.1 (Nat.zero_le j))
  have hEo := (EsetO_SOpen_SClosed (y0 := y0) hc hm a p hp0 (k + 1)).1
  obtain ⟨N1, hN1⟩ := SOpen_pre hc hEo hx
  set ℓ := m + 6
  set ph := N1 + p (k + 2) + 1
  set U := gfun q T ℓ x \ E
  have hxs : x ∉ gset q T ph U := by
    intro h
    obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp h
    exact hu.2 (hN1 ph (by omega) u hxu)
  have hsub : (gset q T ph U)ᶜ ∈ tauSub q T m y0 A :=
    Or.inr ⟨a, ha, p, hp, k, ℓ, ph, x, by omega, by omega, Or.inr rfl⟩
  obtain ⟨n0, hn0⟩ := gfun_subbasic hc (show 0 < ℓ by omega) (mem_gfun q T ℓ x)
  set n1 := n0 + ph + ℓ
  -- W = g(n1+1, x) ∩ (g[ph, U])ᶜ
  have hW : @IsOpen _ (tau q T m y0 A) (gfun q T (n1 + 1) x ∩ (gset q T ph U)ᶜ) := by
    refine @IsOpen.inter _ (tau q T m y0 A) _ _ ?_ (isOpen_tau_of_mem hsub)
    exact isOpen_tau_of_mem (Or.inl (Or.inl ⟨n1 + 1, x, by omega, Or.inl rfl⟩))
  refine ⟨n1, not_mem_closure_of_disjoint _ hW ⟨mem_gfun q T _ x, hxs⟩ ?_⟩
  rw [Set.disjoint_iUnion₂_right]
  intro z hz
  rw [Set.disjoint_left]
  rintro w ⟨hwx, hwU⟩ hwz
  by_cases hzl : z ∈ gfun q T ℓ x
  · apply hwU
    have hzU : z ∈ U := ⟨hzl, hz⟩
    exact Set.mem_biUnion hzU ((gfun_anti hc (by omega) (by omega) z) hwz)
  · have hd := hn0 (n1 + 1) (by omega) z hzl
    exact Set.disjoint_left.mp hd hwx hwz

/-- E(α(k+1), p) の外の点 x（Prop 7.3）。 -/
theorem Ecompl_case (hc : Compat2 q T) (hm : 0 < m) {A : Set (ℕ → ℕ)} {a : ℕ → ℕ} (ha : a ∈ A)
    {p : ℕ → ℕ} (hp : Adm m p) (k : ℕ) {x : ℕ → α} (hx : x ∉ EsetO q T m y0 a p (k + 1)) :
    ∃ n, x ∉ @closure _ (tau q T m y0 A)
      (⋃ y ∈ (EsetO q T m y0 a p (k + 1))ᶜᶜ, gfun q T (n + 1) y) := by
  letI := tau q T m y0 A
  have hp0 : ∀ j, 0 < p j := fun j => lt_of_lt_of_le hp.2.2 (hp.1 (Nat.zero_le j))
  have hEc := (EsetO_SOpen_SClosed (y0 := y0) hc hm a p hp0 (k + 1)).2
  obtain ⟨N1, hN1⟩ := SClosed_pre hc hEc hx
  obtain ⟨r0, hr0⟩ := not_mem_holeU_large (m := m) (y0 := y0) hc a x
  set N := N1 + r0 + p (k + 2) + 1 with hNdef
  set p3 : ℕ → ℕ := fun j => if j ≤ k + 2 then p j else N + j with hp3def
  have hp3 : Adm m p3 := by
    refine ⟨fun i j hij => ?_, ?_, ?_⟩
    · simp only [hp3def]
      split_ifs with h1 h2 h2
      · exact hp.1 hij
      · have := hp.1 (show i ≤ k + 2 from h1); omega
      · omega
      · omega
    · simp only [hp3def, show (1 : ℕ) ≤ k + 2 by omega, ite_true]; exact hp.2.1
    · simp only [hp3def, show (0 : ℕ) ≤ k + 2 by omega, ite_true]; exact hp.2.2
  have hsame : EsetO q T m y0 a p3 (k + 1) = EsetO q T m y0 a p (k + 1) := by
    unfold EsetO
    rw [EseqO_congr (p := p3) (p' := p) a (k + 1)
      (fun j hj => by simp only [hp3def, show j ≤ k + 2 by omega, ite_true])]
  have hclosed : @IsClosed _ (tau q T m y0 A) (EsetO q T m y0 a p3 (k + 2)) :=
    isClosed_tau_of_compl_mem (Or.inl (Or.inr ⟨a, ha, p3, hp3, k + 1, Or.inr rfl⟩))
  have hsubE : gset q T (N + k + 3) (EsetO q T m y0 a p (k + 1)) ⊆ EsetO q T m y0 a p3 (k + 2) := by
    rw [EsetO_succ q T m y0 a p3 (k + 1), hsame]
    have : p3 (k + 1 + 2) = N + k + 3 := by
      simp only [hp3def, show ¬ (k + 1 + 2 ≤ k + 2) by omega, ite_false]; omega
    rw [this]
    exact Set.subset_union_left
  refine ⟨N + k + 2, fun hcl => ?_⟩
  have h1 : (⋃ y ∈ (EsetO q T m y0 a p (k + 1))ᶜᶜ, gfun q T (N + k + 2 + 1) y) ⊆
      EsetO q T m y0 a p3 (k + 2) := by
    rw [compl_compl]; exact hsubE
  have hxE' := closure_minimal (X := ℕ → α) h1 hclosed hcl
  rw [EsetO_succ q T m y0 a p3 (k + 1)] at hxE'
  rcases hxE' with h | h
  · rw [hsame] at h
    have : p3 (k + 1 + 2) = N + k + 3 := by
      simp only [hp3def, show ¬ (k + 1 + 2 ≤ k + 2) by omega, ite_false]; omega
    rw [this] at h
    exact hN1 (N + k + 3) (by omega) h
  · rw [HkO_eq] at h
    have hR : ∀ c S, S ∈ allowedO q T m y0 c
        (slabCum (fun c prior => ⋃ S ∈ allowedO q T m y0 c
          (prior ∪ (EseqO q T m y0 a p3 (k + 1)).2 c),
          holeCells q T m a (k + 1 + 2) (p3 (k + 1 + 2)) (slabO q T m y0 c ∩ S)) c ∪
            (EseqO q T m y0 a p3 (k + 1)).2 c) →
        S ∈ lncA q T (m + 1) (slabO q T m y0 c) := fun c S h => h.1
    have : p3 (k + 1 + 2) = N + k + 3 := by
      simp only [hp3def, show ¬ (k + 1 + 2 ≤ k + 2) by omega, ite_false]; omega
    exact hr0 (p3 (k + 1 + 2)) (by omega) _ _ hR h

/-- Definition C の集合 g[ph, U] の点。 -/
theorem C_case (hc : Compat2 q T) {A : Set (ℕ → ℕ)} {ph : ℕ} (hph : 0 < ph)
    {U : Set (ℕ → α)} {x : ℕ → α} (hx : x ∈ gset q T ph U) :
    ∃ n, x ∉ @closure _ (tau q T m y0 A) (⋃ y ∈ (gset q T ph U)ᶜ, gfun q T (n + 1) y) := by
  obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨n0, hn0⟩ := gfun_subbasic hc hph hxu
  refine ⟨n0, not_mem_closure_of_disjoint _
    (isOpen_tau_of_mem (Or.inl (Or.inl ⟨n0 + 1, x, by omega, Or.inl rfl⟩)))
    (mem_gfun q T _ x) ?_⟩
  rw [Set.disjoint_iUnion₂_right]
  intro z hz
  exact hn0 (n0 + 1) (by omega) z (fun h => hz (Set.mem_biUnion hu h))

/-- Definition C の集合の補集合の点（Prop 7.5）。 -/
theorem Ccompl_case (hc : Compat2 q T) {A : Set (ℕ → ℕ)} {ph : ℕ} (hph : 0 < ph)
    {U : Set (ℕ → α)} (hcl : @IsClosed _ (tau q T m y0 A) (gset q T ph U)) {x : ℕ → α}
    (hx : x ∉ gset q T ph U) :
    ∃ n, x ∉ @closure _ (tau q T m y0 A) (⋃ y ∈ (gset q T ph U)ᶜᶜ, gfun q T (n + 1) y) := by
  letI := tau q T m y0 A
  refine ⟨ph, fun h => hx ?_⟩
  rw [compl_compl] at h
  exact closure_minimal (X := ℕ → α) (gset_gset hc hph (by omega) U) hcl h

/-- **Theorem 1.a**: g(n+1, ·) は τ の stratifying g-関数（Specs.L_0017 の仮定）。 -/
theorem theorem_1a (hc : Compat2 q T) (hm : 0 < m) (A : Set (ℕ → ℕ)) :
    (∀ n x, @IsOpen _ (tau q T m y0 A) (gfun q T (n + 1) x) ∧ x ∈ gfun q T (n + 1) x) ∧
    (∀ n x, gfun q T (n + 1 + 1) x ⊆ gfun q T (n + 1) x) ∧
    (∀ H : Set (ℕ → α), @IsClosed _ (tau q T m y0 A) H → ∀ x, x ∉ H →
      ∃ n, x ∉ @closure _ (tau q T m y0 A) (⋃ y ∈ H, gfun q T (n + 1) y)) := by
  have ht : tau q T m y0 A = .generateFrom (rhoSub q T ∪
      ({s | ∃ a ∈ A, ∃ p, Adm m p ∧ ∃ k,
        s = EsetO q T m y0 a p (k + 1) ∨ s = (EsetO q T m y0 a p (k + 1))ᶜ} ∪
      {s | ∃ a ∈ A, ∃ p, Adm m p ∧ ∃ k ℓ ph x, m + 5 < ℓ ∧ p (k + 2) < ph ∧
        (s = gset q T ph (gfun q T ℓ x \ EsetO q T m y0 a p (k + 1)) ∨
         s = (gset q T ph (gfun q T ℓ x \ EsetO q T m y0 a p (k + 1)))ᶜ)})) := by
    unfold tau tauSub; rw [Set.union_assoc]
  refine strat_of_extra hc _ _ ht ?_
  rintro s (⟨a, ha, p, hp, k, rfl | rfl⟩ | ⟨a, ha, p, hp, k, ℓ, ph, x', hℓ, hph, rfl | rfl⟩) x hx
  · exact E_case hc hm ha hp k hx
  · exact Ecompl_case hc hm ha hp k hx
  · exact C_case hc (show 0 < ph by have := hp.2.1; have := hp.1 (show 1 ≤ k + 2 by omega); omega) hx
  · have hph0 : 0 < ph := by have := hp.2.1; have := hp.1 (show 1 ≤ k + 2 by omega); omega
    exact Ccompl_case hc hph0 (isClosed_tau_of_compl_mem
      (Or.inr ⟨a, ha, p, hp, k, ℓ, ph, x', hℓ, hph, Or.inr rfl⟩)) hx

theorem ptop_isOpen_ne (x : ℕ → α) (k : ℕ) : @IsOpen _ (ptop α) {w : ℕ → α | w k ≠ x k} := by
  letI : TopologicalSpace α := rho α
  have h1 : IsOpen ({x k}ᶜ : Set α) := (isClosed_singleton_rho (x k)).isOpen_compl
  exact h1.preimage (continuous_apply (A := fun _ : ℕ => α) k)

/-- τ は T₁。 -/
theorem tau_t1 (hc : Compat2 q T) (A : Set (ℕ → ℕ)) : @T1Space _ (tau q T m y0 A) := by
  letI := tau q T m y0 A
  refine ⟨fun x => ?_⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  have hne : z ≠ x := hz
  obtain ⟨k, hk⟩ : ∃ k, z k ≠ x k := by
    by_contra h; push_neg at h; exact hne (funext h)
  obtain ⟨n0, hn0⟩ := prop_3_4_eventually hc z _ (ptop_isOpen_ne x k) hk
  refine ⟨gfun q T (n0 + 1) z, fun w hw hwx => ?_,
    isOpen_tau_of_mem (Or.inl (Or.inl ⟨n0 + 1, z, by omega, Or.inl rfl⟩)), mem_gfun q T _ z⟩
  rw [Set.mem_singleton_iff.mp hwx] at hw
  exact hn0 (n0 + 1) (by omega) hw rfl

end Defs.D_0041
