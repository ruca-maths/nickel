import Mathlib.Topology.Basic
import Mathlib.Data.Set.Lattice.Indexed
import Defs.D_0033

/-!
# Chen–Wang §5 Part 2: Structural, Monotonicity, Refinement, and Density Properties of `Oset` (`Defs.D_0033`)

Built directly on `Defs.D_0033` (`prop_5_1`, `cor_5_2`, `Obad`, `Oset`, `fact_5_4`,
`Oset_lnc_cover`, `Oset_closure`):

1. `Oset_isOpen_p`: `Oset q T m n x` is **`ptop`-open** (union of `lnc q T m (Oset q T m n x)`).
2. `Obad_inter_gfun_isClosed_p` & `Obad_inter_gfun_empty_interior_p`:
   the bad locus `Obad q T m n x ∩ gfun q T n x` is `ptop`-**closed** and **nowhere dense**
   (empty `ptop`-interior) in `gfun q T n x`.
3. `Oset_mem_of_hidx_ge`:
   for the uniform bound `c` of `prop_5_1`, every `z ∈ gfun q T n x` with `c ≤ hidx q m z`
   automatically belongs to `Oset q T m n x`.
4. `Oset_mono_of_gfun_sub` & `Oset_mono_level`:
   **monotonicity of `Oset`**: if `gfun q T n' x' ⊆ gfun q T n x`, then
   `Oset q T m n' x' ⊆ Oset q T m n x`; in particular `Oset q T m n' x ⊆ Oset q T m n x`
   for `1 ≤ n ≤ n'`.
5. `Oset_lnc_cover_ge` & `Oset_lnc_refine` & `Oset_lnc_refine_cover`:
   for every `k ≥ m ≥ 1`, `lnc q T k (Oset q T m n x)` covers `Oset q T m n x`, consists of
   pairwise disjoint `ptop`-clopen sets, and refines `lnc q T m (Oset q T m n x)` cleanly
   (each member of `lnc k` is either contained in or disjoint from each member of `lnc m`).
6. `Oset_contains_lnc_in_open`:
   for every `ptop`-open set `V` meeting `gfun q T n x`, there exist `k ≥ m` and
   `S ∈ lnc q T k (Oset q T m n x)` with `S ⊆ V` (dense basis of `lnc` cells inside `Oset`).
-/

namespace Research.ChenWangSec5Oset

open Set Topology
open Defs.D_0003 Defs.D_0009 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0029 Defs.D_0031
  Defs.D_0033

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

/-- `Oset q T m n x` is **`ptop`-open** for all `m ≥ 1`. -/
theorem Oset_isOpen_p (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m) (x : ℕ → α) :
    @IsOpen (ℕ → α) (ptop α) (Oset q T m n x) := by
  let _ : TopologicalSpace (ℕ → α) := ptop α
  rw [← Oset_lnc_cover hc hm x]
  refine isOpen_sUnion ?_
  rintro S ⟨u, rfl, -, -⟩
  exact gfun_isOpen_p q T m u

/-- The bad locus `Obad q T m n x ∩ gfun q T n x` is `ptop`-closed. -/
theorem Obad_inter_gfun_isClosed_p [NoMaxOrder α] (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m)
    (x : ℕ → α) :
    @IsClosed (ℕ → α) (ptop α) (Obad q T m n x ∩ gfun q T n x) := by
  let _ : TopologicalSpace (ℕ → α) := ptop α
  have hEq : Obad q T m n x ∩ gfun q T n x = gfun q T n x \ Oset q T m n x := by
    ext z; simp only [Oset, mem_inter_iff, mem_sdiff, not_and, not_not]
    exact ⟨fun ⟨hb, hg⟩ => ⟨hg, fun _ => hb⟩, fun ⟨hg, h⟩ => ⟨h hg, hg⟩⟩
  rw [hEq]
  exact (gfun_isClosed_p q T n x).sdiff (Oset_isOpen_p hc hm x)

/-- The bad locus `Obad q T m n x ∩ gfun q T n x` has empty `ptop`-interior (nowhere dense). -/
theorem Obad_inter_gfun_empty_interior_p [NoMaxOrder α] [DenselyOrdered α] (hc : Compat2 q T)
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (x : ℕ → α) :
    @interior (ℕ → α) (ptop α) (Obad q T m n x ∩ gfun q T n x) = ∅ := by
  let _ : TopologicalSpace (ℕ → α) := ptop α
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨V, hVsub, hVo, hzV⟩ := mem_interior.mp hz
  have hzG : z ∈ gfun q T n x := (hVsub hzV).2
  rw [← Oset_closure hc hm hmn x] at hzG
  obtain ⟨w, hwV, hwO⟩ := mem_closure_iff.mp hzG V hVo hzV
  exact hwO.2 (hVsub hwV).1

/-- For the uniform bound `c` of `prop_5_1`, every `z ∈ gfun q T n x` with `c ≤ hidx q m z`
belongs to `Oset q T m n x`. -/
theorem Oset_mem_of_hidx_ge (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (x : ℕ → α) :
    ∃ c, ∀ z, z ∈ gfun q T n x → c ≤ hidx q m z → z ∈ Oset q T m n x := by
  obtain ⟨c, hcb⟩ := cor_5_2 hc hm hmn x
  refine ⟨c, fun z hzG hzc => ⟨hzG, fun hzBad => ?_⟩⟩
  obtain ⟨w, hwBad, hzw⟩ := mem_iUnion₂.mp hzBad
  have hEq : hidx q m z = hidx q m w := hidx_eq_of_mem_Hcell q T hm hzw
  have hlt := hcb w hwBad
  omega

/-- **Monotonicity of `Oset`**: if `gfun q T n' x' ⊆ gfun q T n x`, then
`Oset q T m n' x' ⊆ Oset q T m n x`. -/
theorem Oset_mono_of_gfun_sub (hc : Compat2 q T) {m n n' : ℕ} (hm : 0 < m) {x x' : ℕ → α}
    (hsub : gfun q T n' x' ⊆ gfun q T n x) :
    Oset q T m n' x' ⊆ Oset q T m n x := by
  intro u hu
  have hu_gfun : gfun q T m u ⊆ gfun q T n' x' :=
    (fact_5_4 hc hm hu).trans sdiff_subset
  refine ⟨hsub hu.1, fun huBad => ?_⟩
  obtain ⟨z, hzBad, huz⟩ := mem_iUnion₂.mp huBad
  apply hzBad.2
  rw [← gfun_eq_of_mem_Hcell q T hm huz]
  exact hu_gfun.trans hsub

/-- Level monotonicity: for `1 ≤ m` and `1 ≤ n ≤ n'`, `Oset q T m n' x ⊆ Oset q T m n x`. -/
theorem Oset_mono_level (hc : Compat2 q T) {m n n' : ℕ} (hm : 0 < m) (hn : 0 < n) (hnn' : n ≤ n')
    (x : ℕ → α) :
    Oset q T m n' x ⊆ Oset q T m n x :=
  Oset_mono_of_gfun_sub hc hm (gfun_anti hc hn hnn' x)

/-- For every `k ≥ m ≥ 1`, `lnc q T k (Oset q T m n x)` covers `Oset q T m n x`. -/
theorem Oset_lnc_cover_ge (hc : Compat2 q T) {m n k : ℕ} (hm : 0 < m) (hmk : m ≤ k) (x : ℕ → α) :
    ⋃₀ lnc q T k (Oset q T m n x) = Oset q T m n x := by
  apply le_antisymm
  · rintro z ⟨S, hS, hz⟩; exact lnc_sub hS hz
  · intro u hu
    have hsub : gfun q T k u ⊆ Oset q T m n x :=
      (gfun_anti hc hm hmk u).trans (fact_5_4 hc hm hu)
    obtain ⟨S, hS, huS⟩ := lnc_exists hc k _ u hsub
    exact ⟨S, hS, huS (mem_gfun q T k u)⟩

/-- Refinement of `lnc` on `Oset`: for `1 ≤ m ≤ k`, every `S ∈ lnc q T k (Oset q T m n x)` is
either contained in or disjoint from every `S' ∈ lnc q T m (Oset q T m n x)`. -/
theorem Oset_lnc_refine (hc : Compat2 q T) {m n k : ℕ} (hm : 0 < m) (hmk : m ≤ k) {x : ℕ → α}
    {S S' : Set (ℕ → α)} (hS : S ∈ lnc q T k (Oset q T m n x))
    (hS' : S' ∈ lnc q T m (Oset q T m n x)) :
    S ⊆ S' ∨ Disjoint S S' := by
  obtain ⟨u, rfl, huO, -⟩ := hS
  have hu_mem : u ∈ Oset q T m n x := huO (mem_gfun q T k u)
  obtain ⟨S'', hS'', huS''⟩ := lnc_exists hc m _ u (fact_5_4 hc hm hu_mem)
  have hsub : gfun q T k u ⊆ S'' := (gfun_anti hc hm hmk u).trans huS''
  by_cases hEq : S'' = S'
  · exact Or.inl (hEq ▸ hsub)
  · exact Or.inr (Set.disjoint_of_subset_left hsub (lnc_disjoint hc hS'' hS' hEq))

/-- Each `S' ∈ lnc q T m (Oset q T m n x)` is the exact union of those `S ∈ lnc q T k (Oset q T m n x)`
contained in `S'` (for `1 ≤ m ≤ k`). -/
theorem Oset_lnc_refine_cover (hc : Compat2 q T) {m n k : ℕ} (hm : 0 < m) (hmk : m ≤ k)
    {x : ℕ → α} {S' : Set (ℕ → α)} (hS' : S' ∈ lnc q T m (Oset q T m n x)) :
    ⋃₀ { S | S ∈ lnc q T k (Oset q T m n x) ∧ S ⊆ S' } = S' := by
  apply le_antisymm
  · rintro z ⟨S, ⟨-, hSS'⟩, hzS⟩; exact hSS' hzS
  · intro z hzS'
    have hzO : z ∈ Oset q T m n x := lnc_sub hS' hzS'
    rw [← Oset_lnc_cover_ge hc hm hmk x] at hzO
    obtain ⟨S, hS, hzS⟩ := hzO
    rcases Oset_lnc_refine hc hm hmk hS hS' with hsub | hdisj
    · exact ⟨S, ⟨hS, hsub⟩, hzS⟩
    · exact (Set.disjoint_left.mp hdisj hzS hzS').elim

/-- **Density of `lnc` cells inside `Oset`**:
For any `ptop`-open set `V` meeting `gfun q T n x`, there exist `k ≥ m` and a `ptop`-clopen cell
`S ∈ lnc q T k (V ∩ Oset q T m n x)` (so `S` is nonempty and `S ⊆ V ∩ Oset q T m n x`). -/
theorem Oset_contains_lnc_in_open [NoMaxOrder α] [DenselyOrdered α] (hc : Compat2 q T)
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {x : ℕ → α}
    {V : Set (ℕ → α)} (hVo : @IsOpen (ℕ → α) (ptop α) V)
    (hne : (V ∩ gfun q T n x).Nonempty) :
    ∃ k ≥ m, ∃ S ∈ lnc q T k (V ∩ Oset q T m n x), S.Nonempty ∧ S ⊆ V ∩ Oset q T m n x := by
  let _ : TopologicalSpace (ℕ → α) := ptop α
  obtain ⟨z, hzV, hzG⟩ := hne
  rw [← Oset_closure hc hm hmn x] at hzG
  obtain ⟨u, huV, huO⟩ := mem_closure_iff.mp hzG V hVo hzV
  obtain ⟨ℓ, hℓ⟩ := prop_3_4 q T hc u (V ∩ Oset q T m n x) (hVo.inter (Oset_isOpen_p hc hm x)) ⟨huV, huO⟩
  let k := max m ℓ
  have hsub_O : gfun q T k u ⊆ Oset q T m n x :=
    (gfun_anti hc hm (le_max_left m ℓ) u).trans (fact_5_4 hc hm huO)
  have hsub_V : gfun q T k u ⊆ V := by
    cases ℓ with
    | zero =>
      have h10 : gfun q T 1 u ⊆ gfun q T 0 u := by
        rintro w ⟨h1, h2⟩
        have hc' : hidx q 0 u ≤ hidx q 1 u := by
          show Defs.D_0007.code 0 (fun j => q.symm (u j)) ≤ hidx q 1 u
          simp [Defs.D_0007.code]
        have hab : lvl q 0 u ≤ lvl q 1 u := by unfold lvl; omega
        have ha := lvl_pos q 0 u
        refine ⟨fun j hj => by omega, fun j hj1 hj2 => ?_⟩
        rcases eq_or_lt_of_le hj1 with heq | hlt
        · subst heq
          have hw := h1 0 (by omega)
          obtain ⟨_, hu0⟩ := ibase_spec T ha (u 0)
          rcases eq_or_lt_of_le hu0.1 with he | hlt'
          · show w 0 ∈ Set.Ico (ibase T (lvl q 0 u) (u 0))
              (T.child (ibase T (lvl q 0 u) (u 0)) (lvl q 0 u))
            rw [he]
            exact ⟨hw.1, lt_of_lt_of_le hw.2 (Tree2.child_le_child T _ ha hab)⟩
          · have := (prop_3_2_1' hc ha hlt' hu0.2).2.2 (lvl q 1 u) (lvl_pos _ _ _) hw
            exact ⟨this.1.le, this.2⟩
        · exact ival_mono T ha hab (u j) (h2 j (by omega) (by omega))
      have hk1 : 1 ≤ k := le_trans hm (le_max_left m 0)
      exact ((gfun_anti hc Nat.zero_lt_one hk1 u).trans h10).trans (hℓ.trans inter_subset_left)
    | succ ℓ' =>
      exact (gfun_anti hc (Nat.zero_lt_succ ℓ') (le_max_right m (ℓ' + 1)) u).trans
        (hℓ.trans inter_subset_left)
  obtain ⟨S, hS, huS⟩ := lnc_exists hc k (V ∩ Oset q T m n x) u
    (fun w hw => ⟨hsub_V hw, hsub_O hw⟩)
  exact ⟨k, le_max_left m ℓ, S, hS, ⟨u, huS (mem_gfun q T k u)⟩, lnc_sub hS⟩

end Research.ChenWangSec5Oset
