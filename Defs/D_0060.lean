import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0044

namespace Defs.D_0060

/-!
箱 g(n, x) の層をまたぐ入れ子性（稠密性の証明の幾何的な基礎）。

* `qsymm_lt_lvl` : k < n なら q⁻¹(x k) < lvl n x。
* `ival_eq_of_mem` : s ∈ I_a(r) なら I_a(s) = I_a(r)（I_a の区間の一意性）。
* `ival_sub` : a ≤ A なら I_A(r) ⊆ I_a(r)（細分）。
* `Ico_child_sub` : x ∈ [u, u_a), a ≤ A なら [x, x_A) ⊆ [u, u_a)。
* **`gfun_sub_coarse`（ZZ+）**: x ∈ g(n, u) かつ lvl n u ≤ lvl N x なら g(N, x) ⊆ g(n, u)。
  粗い箱がより細かい箱の中心を含めば、その箱全体を含む（超距離空間の球の性質の類似）。
* **`center_mem_coarse`（ZZ）**: 細かい箱 g(N, s) の点を含む粗い箱（lvl ≤ lvl N s）は中心 s を含む。
* `parent_unique`, `shadow_cases` : 木の親の一意性と、t の子 w = t_J が u の影 (u, u_a) に入る場合の分類。
* `shift0 t J` : 座標 0 を t 0 の番号 J の子にずらした点。**`shift0_box_sub`（CLOSE）**: J > lvl ℓ t なら
  g(m+1, shift0 t J) ⊆ g(ℓ, t)。
* **`loc`（局所化）**: s = shift0 t J の slab（先頭 m 座標が s と一致）の点 x ∈ g(m+1, s) を含む箱 g(n, u)
  （n ≥ m）は、t を含むか、中心 u が s の slab にある。稠密性の証拠点を 2 段（z → x* → w）でずらすと、
  w を含む箱は z を含むか、x* の slab か w の slab に中心を持つものに限られる。
-/

open Defs.D_0002 Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0005 Defs.D_0007 Defs.D_0012 Defs.D_0024
  Defs.D_0025 Defs.D_0044

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

theorem qsymm_lt_lvl {n k : ℕ} (x : ℕ → α) (hk : k < n) : q.symm (x k) < lvl q n x := by
  have := code_ge n (fun k => q.symm (x k)) k hk
  unfold lvl hidx; omega

theorem ival_eq_of_mem {a : ℕ} (ha : 0 < a) {r s : α} (h : s ∈ ival T a r) :
    ival T a s = ival T a r := by
  have h1 := ibase_spec T ha s
  have h2 := ibase_spec T ha r
  have : ibase T a s = ibase T a r := (prop_2_2_1 T ha s).unique ⟨h1.1, h1.2⟩ ⟨h2.1, h⟩
  unfold ival; rw [this]

theorem ival_sub {a A : ℕ} (ha : 0 < a) (haA : a ≤ A) (r : α) : ival T A r ⊆ ival T a r := by
  have hA : 0 < A := lt_of_lt_of_le ha haA
  rcases prop_2_2_5 T ha haA (ibase_spec T ha r).1 (ibase_spec T hA r).1 with h | h
  · exact absurd (Set.disjoint_left.mp h (ibase_spec T ha r).2 (ibase_spec T hA r).2) id
  · exact h

theorem Ico_child_sub (hc : Compat2 q T) {a A : ℕ} (ha : 0 < a) (haA : a ≤ A) {u x : α}
    (hx : x ∈ Set.Ico u (T.child u a)) : Set.Ico x (T.child x A) ⊆ Set.Ico u (T.child u a) := by
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h; exact Set.Ico_subset_Ico le_rfl (child_le_child T u ha haA)
  · intro y hy
    have := (prop_3_2_1' hc ha h hx.2).2.2 A (by omega) hy
    exact ⟨this.1.le, this.2⟩

/-- [c, c_A) ∋ x と [u, u_a) ∋ x で、q⁻¹ u < a ≤ A なら [c, c_A) ⊆ [u, u_a)。 -/
theorem Ico_cell_sub (hc : Compat2 q T) {a A : ℕ} (ha : 0 < a) (haA : a ≤ A) {u c x : α}
    (hu : q.symm u < a) (hxu : x ∈ Set.Ico u (T.child u a)) (hxc : x ∈ Set.Ico c (T.child c A)) :
    Set.Ico c (T.child c A) ⊆ Set.Ico u (T.child u a) := by
  have hA : 0 < A := lt_of_lt_of_le ha haA
  rcases prop_2_1_4 T.toTree (T.C_child u a ha) (T.C_child c A hA) with h | h | h
  · exact absurd (Set.disjoint_left.mp h hxu hxc) id
  · -- [u, u_a) ⊆ [c, c_A)
    have huc : u ∈ Set.Ico c (T.child c A) := h ⟨le_rfl, T.lt_child _ _ (T.C_child u a ha)⟩
    rcases eq_or_lt_of_le huc.1 with he | hlt
    · subst he; exact Set.Ico_subset_Ico le_rfl (child_le_child T c ha haA)
    · have := (prop_3_2_1' hc hA hlt huc.2).2.1
      omega
  · exact h

/-- **ZZ+**: 粗い箱が細かい箱の中心を含めば、細かい箱全体を含む。 -/
theorem gfun_sub_coarse (hc : Compat2 q T) {n N : ℕ}
    {u x : ℕ → α} (hx : x ∈ gfun q T n u) (hlv : lvl q n u ≤ lvl q N x) :
    gfun q T N x ⊆ gfun q T n u := by
  intro y hy
  have ha : 0 < lvl q n u := lvl_pos q n u
  have hA : 0 < lvl q N x := lvl_pos q N x
  have hna : n < lvl q n u := by unfold lvl; omega
  refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · have hxk := hx.1 k hk
    by_cases hkN : k < N
    · exact Ico_child_sub hc ha hlv hxk (hy.1 k hkN)
    · have hyk := hy.2 k (not_lt.mp hkN) (by show k < lvl q N x; omega)
      have hcx := (ibase_spec T hA (x k)).2
      exact Ico_cell_sub hc ha hlv (qsymm_lt_lvl u hk) hxk hcx hyk
  · have hk' : k < lvl q n u := hk2
    have hxk := hx.2 k hk1 hk2
    rw [← ival_eq_of_mem ha hxk]
    by_cases hkN : k < N
    · have hcx := (ibase_spec T ha (x k)).2
      exact Ico_child_sub hc ha hlv hcx (hy.1 k hkN)
    · exact ival_sub ha hlv (x k) (hy.2 k (not_lt.mp hkN) (by show k < lvl q N x; omega))

/-- **ZZ**: 細かい箱 g(N, s) の点を含む粗い箱は、その中心 s を含む。 -/
theorem center_mem_coarse (hc : Compat2 q T) {n N : ℕ} {u s x : ℕ → α}
    (hxs : x ∈ gfun q T N s) (hxu : x ∈ gfun q T n u) (hlv : lvl q n u ≤ lvl q N s) :
    s ∈ gfun q T n u := by
  have ha : 0 < lvl q n u := lvl_pos q n u
  have hA : 0 < lvl q N s := lvl_pos q N s
  have hna : n < lvl q n u := by unfold lvl; omega
  refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · have hxk := hxu.1 k hk
    have hsk : s k ∈ Set.Ico (s k) (T.child (s k) (lvl q N s)) :=
      ⟨le_rfl, T.lt_child _ _ (T.C_child _ _ hA)⟩
    by_cases hkN : k < N
    · exact Ico_cell_sub hc ha hlv (qsymm_lt_lvl u hk) hxk (hxs.1 k hkN) hsk
    · have hxk' := hxs.2 k (not_lt.mp hkN) (by show k < lvl q N s; omega)
      have hcs := (ibase_spec T hA (s k)).2
      exact Ico_cell_sub hc ha hlv (qsymm_lt_lvl u hk) hxk hxk' hcs
  · have hk' : k < lvl q n u := hk2
    have hxk := hxu.2 k hk1 hk2
    rw [← ival_eq_of_mem ha hxk]
    by_cases hkN : k < N
    · -- x k ∈ [s k, (s k)_A)、c := ibase a (x k)
      have hxsk := hxs.1 k hkN
      have hcx := (ibase_spec T ha (x k))
      set c := ibase T (lvl q n u) (x k) with hcdef
      show s k ∈ Set.Ico c (T.child c (lvl q n u))
      rcases prop_2_1_4 T.toTree (T.C_child (s k) _ hA) (T.C_child c _ ha) with h | h | h
      · exact absurd (Set.disjoint_left.mp h hxsk hcx.2) id
      · exact h ⟨le_rfl, T.lt_child _ _ (T.C_child _ _ hA)⟩
      · have hcs : c ∈ Set.Ico (s k) (T.child (s k) (lvl q N s)) :=
          h ⟨le_rfl, T.lt_child _ _ (T.C_child _ _ ha)⟩
        rcases eq_or_lt_of_le hcs.1 with he | hlt
        · rw [← he]; exact ⟨le_rfl, T.lt_child _ _ (T.C_child _ _ ha)⟩
        · exact absurd ⟨hlt, lt_of_lt_of_le hcs.2 (child_le_child T (s k) ha hlv)⟩
            (not_mem_gap T ha hcx.1 (s k))
    · have hxsk := hxs.2 k (not_lt.mp hkN) (by show k < lvl q N s; omega)
      have h1 : ival T (lvl q N s) (x k) = ival T (lvl q N s) (s k) := ival_eq_of_mem hA hxsk
      have h2 : s k ∈ ival T (lvl q N s) (x k) := by rw [h1]; exact mem_ival T hA (s k)
      exact ival_sub ha hlv (x k) h2

/-- 親の一意性。 -/
theorem parent_unique {b b' c : α} (h : T.C b c) (h' : T.C b' c) : b = b' := by
  have hl := T.lev_child b c h
  have hl' := T.lev_child b' c h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact T.gap b c b' h (by omega) ⟨hlt, T.lt_child b' c h'⟩
  · exact T.gap b' c b h' (by omega) ⟨hlt, T.lt_child b c h⟩

/-- 影の補題: u < w < u_a で w = t_J（C t w）なら、u = t かつ a < J、または u < t < u_a。 -/
theorem shadow_cases (hc : Compat2 q T) {a : ℕ} (ha : 0 < a) {u w t : α}
    (h1 : u < w) (h2 : w < T.child u a) (htw : T.C t w) :
    (u = t ∧ a < T.idx w) ∨ (u < t ∧ t < T.child u a) := by
  have hw1 : w < T.child u 1 := lt_of_lt_of_le h2 (child_le_child T u (by omega) ha)
  obtain ⟨l, hl0, hd⟩ := hc.desc_of_mem u w h1 hw1
  have hal : a < l := by
    by_contra hc'
    have hle : T.child u a ≤ T.child u l := child_le_child T u hl0 (by omega)
    exact absurd (lt_of_le_of_lt (le_trans hle (desc_le T hd)) h2) (lt_irrefl _)
  rcases Relation.ReflTransGen.cases_tail hd with he | ⟨b, hb, hbw⟩
  · left
    have hC : T.C u w := he ▸ T.C_child u l hl0
    have hut := parent_unique hC htw
    refine ⟨hut, ?_⟩
    rw [he, T.idx_child]; exact hal
  · right
    have hbt := parent_unique hbw htw
    subst hbt
    have hle := desc_le T hb
    exact ⟨lt_of_lt_of_le (T.lt_child _ _ (T.C_child u l hl0)) hle,
      lt_trans (T.lt_child _ _ hbw) h2⟩

variable (T) in
/-- 座標 0 を t 0 の番号 J の子にずらした点。 -/
noncomputable def shift0 (t : ℕ → α) (J : ℕ) : ℕ → α := Function.update t 0 (T.child (t 0) J)

theorem shift0_zero (t : ℕ → α) (J : ℕ) : shift0 T t J 0 = T.child (t 0) J := by
  simp [shift0]

theorem shift0_ne (t : ℕ → α) (J : ℕ) {k : ℕ} (hk : k ≠ 0) : shift0 T t J k = t k := by
  simp [shift0, hk]

/-- **CLOSE**: J > lvl ℓ t なら g(m+1, shift0 t J) ⊆ g(ℓ, t)。 -/
theorem shift0_box_sub (hc : Compat2 q T) {ℓ m J : ℕ} (hℓ : 0 < ℓ) {t : ℕ → α}
    (hJ : lvl q ℓ t < J) : gfun q T (m + 1) (shift0 T t J) ⊆ gfun q T ℓ t := by
  have hJ0 : 0 < J := by have := lvl_pos q ℓ t; omega
  have hs0 := shift0_zero (T := T) t J
  have hmem : shift0 T t J ∈ gfun q T ℓ t := by
    refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
    · by_cases hk0 : k = 0
      · subst hk0
        rw [hs0]
        refine ⟨(T.lt_child _ _ (T.C_child _ _ hJ0)).le, ?_⟩
        refine T.child_anti _ _ _ (T.C_child _ _ (lvl_pos q ℓ t)) (T.C_child _ _ hJ0) ?_
        rw [T.idx_child, T.idx_child]; exact hJ
      · rw [shift0_ne t J hk0]
        exact ⟨le_rfl, T.lt_child _ _ (T.C_child _ _ (lvl_pos q ℓ t))⟩
    · rw [shift0_ne t J (by omega)]
      exact mem_ival T (lvl_pos q ℓ t) (t k)
  refine gfun_sub_coarse hc hmem ?_
  have h1 : J ≤ q.symm (shift0 T t J 0) := by rw [hs0]; exact hc.idx_le_num _ J hJ0
  have h2 := qsymm_lt_lvl (q := q) (shift0 T t J) (show 0 < m + 1 by omega)
  omega

/-- 兄弟 slab の排除: u 0 = s 0（= t 0 の番号 J の子）で、座標 1..m−1 の s k ∈ [u k, (u k)_a) なら u k = s k。 -/
theorem sibling_eq (hc : Compat2 q T) {m n J : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hJ0 : 0 < J)
    {t u : ℕ → α} (hJ : ∀ k, 0 < k → k < m → q.symm (t k) < J)
    (hu0 : u 0 = shift0 T t J 0)
    (hin : ∀ k < m, shift0 T t J k ∈ Set.Ico (u k) (T.child (u k) (lvl q n u))) :
    ∀ k < m, u k = shift0 T t J k := by
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0; exact hu0
  · rcases eq_or_lt_of_le (hin k hk).1 with he | hlt
    · exact he
    · exfalso
      have h1 := (prop_3_2_1' hc (lvl_pos q n u) hlt (hin k hk).2).2.1
      rw [shift0_ne t J hk0] at h1
      have h2 := hJ k (by omega) hk
      have h3 : J ≤ q.symm (u 0) := by
        rw [hu0, shift0_zero]; exact hc.idx_le_num _ J hJ0
      have h4 := qsymm_lt_lvl (q := q) u (show 0 < n by omega)
      omega

/-- **LOC（局所化）**: s = shift0 t J の slab の点 x ∈ g(m+1, s) を含む箱 g(n, u)（n ≥ m）は、
t を含むか、中心 u が s の slab にある（先頭 m 座標が s と一致）。 -/
theorem loc (hc : Compat2 q T) {m n J : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hJ0 : 0 < J)
    {t : ℕ → α} (hJ : ∀ k, 0 < k → k < m → q.symm (t k) < J)
    {x u : ℕ → α} (hx : x ∈ gfun q T (m + 1) (shift0 T t J))
    (hxs : ∀ k < m, x k = shift0 T t J k) (hxu : x ∈ gfun q T n u) :
    t ∈ gfun q T n u ∨ ∀ k < m, u k = shift0 T t J k := by
  set s := shift0 T t J with hsdef
  have hs0 : s 0 = T.child (t 0) J := shift0_zero t J
  have hC : T.C (t 0) (s 0) := hs0 ▸ T.C_child _ _ hJ0
  have hidxs : T.idx (s 0) = J := by rw [hs0, T.idx_child]
  have hJs : J ≤ q.symm (s 0) := by rw [hs0]; exact hc.idx_le_num _ J hJ0
  have hsA : q.symm (s 0) < lvl q (m + 1) s := qsymm_lt_lvl s (by omega)
  have ha : 0 < lvl q n u := lvl_pos q n u
  have hn0 : 0 < n := by omega
  by_cases hlv : lvl q n u ≤ lvl q (m + 1) s
  · have hsu := center_mem_coarse hc hx hxu hlv
    have h0 := hsu.1 0 hn0
    rcases le_or_gt (u 0) (t 0) with h | h
    · left
      refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
      · by_cases hk0 : k = 0
        · subst hk0
          exact ⟨h, lt_trans (hs0 ▸ T.lt_child _ _ (T.C_child _ _ hJ0)) h0.2⟩
        · have := hsu.1 k hk
          rwa [hsdef, shift0_ne t J hk0] at this
      · have := hsu.2 k hk1 hk2
        rwa [hsdef, shift0_ne t J (by omega)] at this
    · right
      rcases eq_or_lt_of_le h0.1 with he | hlt
      · exact sibling_eq hc hm hmn hJ0 hJ he (fun k hk => hsu.1 k (by omega))
      · exfalso
        rcases shadow_cases hc ha hlt h0.2 hC with ⟨he, -⟩ | ⟨hlt2, -⟩
        · exact absurd he (ne_of_gt h)
        · exact absurd hlt2 (not_lt.mpr h.le)
  · right
    have hx0 : x 0 = s 0 := hxs 0 hm
    have h0 := hxu.1 0 hn0
    rw [hx0] at h0
    rcases eq_or_lt_of_le h0.1 with he | hlt
    · refine sibling_eq hc hm hmn hJ0 hJ he (fun k hk => ?_)
      have := hxu.1 k (by omega)
      rwa [hxs k hk] at this
    · exfalso
      rcases shadow_cases hc ha hlt h0.2 hC with ⟨-, hlt2⟩ | ⟨hlt2, hlt3⟩
      · rw [hidxs] at hlt2; omega
      · have h1 := (prop_3_2_1' hc ha hlt2 hlt3).2.1
        have h2 := hc.num_child _ _ hC
        omega

end Defs.D_0060
