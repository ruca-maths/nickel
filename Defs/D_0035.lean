import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.Basic.Denumerable
import Mathlib.Data.List.OfFn
import Defs.D_0034

namespace Defs.D_0035

/-!
Chen–Wang (arXiv 1809.03763v2) §6 の土台: 一般の集合 A の Ln cover（Note Ln, Corollary 4.7）。

論文の「(n, H) の Ln (sub)cover」は {g(n, x) : x ∈ H} の部分族で、和を変えずに互いに素にしたもの。
G_n の laminar 性から、これは {g(n, x) : x ∈ A} の**極大元**全体 `lncA q T n A` と一致する。

* `gset q T n A` : 論文の g[n, A] = ⋃_{x ∈ A} g(n, x)。
* `lncA` と `lncA_exists`, `lncA_disjoint`, `lncA_sUnion`（⋃ lncA = g[n, A]）。
* `lncA_mem` : x ∈ g[n, A] を含む lncA の元（一意）。
* `gkey`, `gfun_eq_of_gkey` : g(n, x) は有限個の点のリストで決まる。
* `gfam_countable` : {g(n, x)} は可算（α が可算のとき）。
* `lab` : 可算無限族の元への番号（全単射 ℕ ≃ 族 を固定したもの）。論文の Δ-order の代わり。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031

variable {α : Type} [LinearOrder α] (q : ℕ ≃ α) (T : Tree2 α)

/-- 論文の g[n, A]。 -/
noncomputable def gset (n : ℕ) (A : Set (ℕ → α)) : Set (ℕ → α) := ⋃ x ∈ A, gfun q T n x

/-- A の点の g(n, ·) のうち極大なもの全体。 -/
def lncA (n : ℕ) (A : Set (ℕ → α)) : Set (Set (ℕ → α)) :=
  {S | ∃ x ∈ A, S = gfun q T n x ∧ ∀ y ∈ A, S ⊆ gfun q T n y → gfun q T n y = S}

variable {q T}

theorem lncA_exists (hc : Compat2 q T) (n : ℕ) (A : Set (ℕ → α)) {x : ℕ → α} (hx : x ∈ A) :
    ∃ S ∈ lncA q T n A, gfun q T n x ⊆ S := by
  suffices h : ∀ c, ∀ x ∈ A, hidx q n x = c → ∃ S ∈ lncA q T n A, gfun q T n x ⊆ S from
    h _ x hx rfl
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro x hx hc'
    by_cases hmax : ∀ y ∈ A, gfun q T n x ⊆ gfun q T n y → gfun q T n y = gfun q T n x
    · exact ⟨gfun q T n x, ⟨x, hx, rfl, hmax⟩, le_rfl⟩
    · push_neg at hmax
      obtain ⟨y, hyA, hxy, hne⟩ := hmax
      have hlt := hidx_lt_of_ssub hc hxy hne
      obtain ⟨S, hS, hyS⟩ := ih _ (hc' ▸ hlt) y hyA rfl
      exact ⟨S, hS, hxy.trans hyS⟩

theorem lncA_disjoint (hc : Compat2 q T) {n : ℕ} {A S S' : Set (ℕ → α)}
    (hS : S ∈ lncA q T n A) (hS' : S' ∈ lncA q T n A) (hne : S ≠ S') : Disjoint S S' := by
  obtain ⟨x, hxA, rfl, hxm⟩ := hS
  obtain ⟨y, hyA, rfl, hym⟩ := hS'
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hi
  have hi' := Set.nonempty_iff_ne_empty.mpr hi
  rcases le_total (hidx q n x) (hidx q n y) with h | h
  · exact hne (hym x hxA (gfun_nested hc h hi'))
  · exact hne (hxm y hyA (gfun_nested hc h (Set.inter_comm _ _ ▸ hi'))).symm

theorem lncA_sub_gset {n : ℕ} {A S : Set (ℕ → α)} (hS : S ∈ lncA q T n A) :
    S ⊆ gset q T n A := by
  obtain ⟨x, hxA, rfl, -⟩ := hS
  exact fun z hz => Set.mem_biUnion hxA hz

theorem lncA_sUnion (hc : Compat2 q T) (n : ℕ) (A : Set (ℕ → α)) :
    ⋃₀ lncA q T n A = gset q T n A := by
  apply le_antisymm
  · rintro z ⟨S, hS, hz⟩; exact lncA_sub_gset hS hz
  · intro z hz
    obtain ⟨x, hxA, hzx⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨S, hS, hxS⟩ := lncA_exists hc n A hxA
    exact ⟨S, hS, hxS hzx⟩

/-- A ⊆ g[n, A]。 -/
theorem sub_gset (n : ℕ) (A : Set (ℕ → α)) : A ⊆ gset q T n A :=
  fun x hx => Set.mem_biUnion hx (mem_gfun q T n x)

theorem lncA_unique (hc : Compat2 q T) {n : ℕ} {A S S' : Set (ℕ → α)} {z : ℕ → α}
    (hS : S ∈ lncA q T n A) (hS' : S' ∈ lncA q T n A) (hz : z ∈ S) (hz' : z ∈ S') : S = S' := by
  by_contra hne
  exact Set.disjoint_left.mp (lncA_disjoint hc hS hS' hne) hz hz'

open Classical in
/-- g[n, A] の点 z を含む lncA の元。 -/
noncomputable def lncA_mem (q : ℕ ≃ α) (T : Tree2 α) (n : ℕ) (A : Set (ℕ → α)) (z : ℕ → α) :
    Set (ℕ → α) :=
  if h : ∃ S ∈ lncA q T n A, z ∈ S then h.choose else ∅

theorem lncA_mem_spec (hc : Compat2 q T) {n : ℕ} {A : Set (ℕ → α)} {z : ℕ → α}
    (hz : z ∈ gset q T n A) : lncA_mem q T n A z ∈ lncA q T n A ∧ z ∈ lncA_mem q T n A z := by
  have h : ∃ S ∈ lncA q T n A, z ∈ S := by
    rw [← lncA_sUnion hc n A] at hz
    obtain ⟨S, hS, hzS⟩ := hz
    exact ⟨S, hS, hzS⟩
  unfold lncA_mem
  rw [dif_pos h]
  exact h.choose_spec

theorem lncA_mem_eq (hc : Compat2 q T) {n : ℕ} {A S : Set (ℕ → α)} {z : ℕ → α}
    (hS : S ∈ lncA q T n A) (hz : z ∈ S) : lncA_mem q T n A z = S := by
  have hz' : z ∈ gset q T n A := lncA_sub_gset hS hz
  obtain ⟨h1, h2⟩ := lncA_mem_spec hc hz'
  exact lncA_unique hc h1 hS h2 hz

/-! ### 可算性と番号付け -/

variable (q T)

/-- g(n, x) を決める有限データ。 -/
noncomputable def gkey (n : ℕ) (x : ℕ → α) : List α :=
  List.ofFn (fun k : Fin (n + hidx q n x + 1) =>
    if (k : ℕ) < n then x k else ibase T (lvl q n x) (x k))

variable {q T}

theorem gfun_eq_of_gkey {n : ℕ} (hn : 0 < n) {x x' : ℕ → α} (h : gkey q T n x = gkey q T n x') :
    gfun q T n x = gfun q T n x' := by
  have hlen : n + hidx q n x + 1 = n + hidx q n x' + 1 := by
    have := congrArg List.length h
    simpa [gkey] using this
  have hpt : ∀ k (hk : k < n + hidx q n x + 1),
      (if k < n then x k else ibase T (lvl q n x) (x k)) =
        (if k < n then x' k else ibase T (lvl q n x') (x' k)) := by
    intro k hk
    have h1 := congrArg (fun l => l[k]?) h
    simp only [gkey, List.getElem?_ofFn] at h1
    simpa [List.ofFnNthVal, hk, show k < n + hidx q n x' + 1 by omega] using h1
  have hfirst : ∀ k < n, x k = x' k := fun k hk => by
    have := hpt k (by omega); simpa [hk] using this
  have hh : hidx q n x = hidx q n x' :=
    (code_eq_iff n hn _ _).2 (fun k hk => by show q.symm (x k) = q.symm (x' k); rw [hfirst k hk])
  have hl : lvl q n x = lvl q n x' := by unfold lvl; rw [hh]
  rw [gfun_eq, gfun_eq, hh, hl]
  ext z
  simp only [Set.mem_setOf_eq]
  refine forall_congr' fun k => forall_congr' fun hk => ?_
  split_ifs with hkn
  · rw [hfirst k hkn]
  · have := hpt k (by omega)
    simp only [hkn, if_false] at this
    unfold ival
    rw [hl] at this
    rw [this]

/-- 第 n 層の g 集合の族は可算。 -/
theorem gfam_countable [Countable α] (n : ℕ) (hn : 0 < n) :
    {S : Set (ℕ → α) | ∃ x, S = gfun q T n x}.Countable := by
  classical
  let F : List α → Set (ℕ → α) := fun l =>
    if h : ∃ x, gkey q T n x = l then gfun q T n h.choose else ∅
  refine (Set.countable_range F).mono ?_
  rintro S ⟨x, rfl⟩
  refine ⟨gkey q T n x, ?_⟩
  have h : ∃ x', gkey q T n x' = gkey q T n x := ⟨x, rfl⟩
  simp only [F, dif_pos h]
  exact gfun_eq_of_gkey hn h.choose_spec

theorem lncA_countable [Countable α] {n : ℕ} (hn : 0 < n) (A : Set (ℕ → α)) :
    (lncA q T n A).Countable :=
  (gfam_countable n hn).mono (by rintro S ⟨x, -, rfl, -⟩; exact ⟨x, rfl⟩)

/-- 可算無限集合と ℕ の全単射（1 つ固定）。 -/
noncomputable def denEq {β : Type} (F : Set β) (h : F.Countable ∧ F.Infinite) : F ≃ ℕ :=
  haveI : Countable F := h.1.to_subtype
  haveI : Infinite F := h.2.to_subtype
  haveI : Encodable F := Encodable.ofCountable F
  @Denumerable.eqv F (Denumerable.ofEncodableOfInfinite F)

open Classical in
/-- 可算無限族の元への番号。論文の Δ-order の代わり。 -/
noncomputable def lab {β : Type} (F : Set β) (S : β) : ℕ :=
  if h : F.Countable ∧ F.Infinite ∧ S ∈ F then denEq F ⟨h.1, h.2.1⟩ ⟨S, h.2.2⟩ else 0

/-- 番号から元へ。 -/
noncomputable def unlab {β : Type} (F : Set β) (hF : F.Countable ∧ F.Infinite) (k : ℕ) : β :=
  ((denEq F hF).symm k).1

theorem unlab_mem {β : Type} (F : Set β) (hF : F.Countable ∧ F.Infinite) (k : ℕ) :
    unlab F hF k ∈ F := ((denEq F hF).symm k).2

theorem lab_unlab {β : Type} (F : Set β) (hF : F.Countable ∧ F.Infinite) (k : ℕ) :
    lab F (unlab F hF k) = k := by
  classical
  unfold lab
  rw [dif_pos ⟨hF.1, hF.2, unlab_mem F hF k⟩]
  show denEq F hF ((denEq F hF).symm k) = k
  exact Equiv.apply_symm_apply _ _

theorem unlab_lab {β : Type} {F : Set β} (hF : F.Countable ∧ F.Infinite) {S : β} (hS : S ∈ F) :
    unlab F hF (lab F S) = S := by
  classical
  unfold lab unlab
  rw [dif_pos ⟨hF.1, hF.2, hS⟩]
  show ((denEq F hF).symm (denEq F hF ⟨S, hS⟩)).1 = S
  rw [Equiv.symm_apply_apply]

theorem lab_inj {β : Type} {F : Set β} (hF : F.Countable ∧ F.Infinite) {S S' : β}
    (hS : S ∈ F) (hS' : S' ∈ F) (h : lab F S = lab F S') : S = S' := by
  rw [← unlab_lab hF hS, ← unlab_lab hF hS', h]

end Defs.D_0035
