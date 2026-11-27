import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0035

namespace Defs.D_0036

/-!
Chen–Wang (arXiv 1809.03763v2) Construction 6.1 A–B（TeX 2922–3040 行）の入れ子構造。

G_m = g(m, y₀), H₀ = H(m, y₀), O(m, y₀) = G_m − H₀。点 x ∈ O について:
* `slab q T m y0 c := H(m, c) ∩ G_m`（論文の H'(m, 1_j)。番号 1_j は H(m, ·) の符号 c で、Δ-order は c の大小）。
* `A1 x` : slab ∩（第 m+1 層の Ln cover の x を含む元）= 論文の H(m₁, jz)。
* `A2 x` : A1 ∩（第 m+2 層の Ln cover of A1 の元）= H(m₂, jz_n)。branch 番号 `br x` = n。
* `A3 x` : A2 ∩（第 m+3 層の Ln cover of A2 の元）= H(m₃, jz^n_v)。piece 番号 `pc x` = v。
番号は Δ-order の代わりに `Defs.D_0035.lab`（族ごとの全単射）を使う。

定理: x ∈ A3 x ⊆ A2 x ⊆ A1 x ⊆ slab、および z ∈ A_i x ⇒ A_i z = A_i x（整合性、分割であること）、
`br`, `pc` も同じ piece 内で一定。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035

variable {α : Type} [LinearOrder α] (q : ℕ ≃ α) (T : Tree2 α) (m : ℕ) (y0 : ℕ → α)

noncomputable def slab (c : ℕ) : Set (ℕ → α) := H q m c ∩ gfun q T m y0

noncomputable def M1 (x : ℕ → α) : Set (ℕ → α) :=
  lncA_mem q T (m + 1) (slab q T m y0 (hidx q m x)) x

noncomputable def A1 (x : ℕ → α) : Set (ℕ → α) :=
  slab q T m y0 (hidx q m x) ∩ M1 q T m y0 x

noncomputable def M2 (x : ℕ → α) : Set (ℕ → α) :=
  lncA_mem q T (m + 2) (A1 q T m y0 x) x

noncomputable def A2 (x : ℕ → α) : Set (ℕ → α) := A1 q T m y0 x ∩ M2 q T m y0 x

noncomputable def br (x : ℕ → α) : ℕ := lab (lncA q T (m + 2) (A1 q T m y0 x)) (M2 q T m y0 x)

noncomputable def M3 (x : ℕ → α) : Set (ℕ → α) :=
  lncA_mem q T (m + 3) (A2 q T m y0 x) x

noncomputable def A3 (x : ℕ → α) : Set (ℕ → α) := A2 q T m y0 x ∩ M3 q T m y0 x

noncomputable def pc (x : ℕ → α) : ℕ := lab (lncA q T (m + 3) (A2 q T m y0 x)) (M3 q T m y0 x)

variable {q T m y0}

theorem mem_slab {x : ℕ → α} (hx : x ∈ gfun q T m y0) : x ∈ slab q T m y0 (hidx q m x) :=
  ⟨rfl, hx⟩

theorem slab_eq_of_mem {c : ℕ} {z : ℕ → α} (hz : z ∈ slab q T m y0 c) : hidx q m z = c := hz.1

theorem M1_spec (hc : Compat2 q T) {x : ℕ → α} (hx : x ∈ gfun q T m y0) :
    M1 q T m y0 x ∈ lncA q T (m + 1) (slab q T m y0 (hidx q m x)) ∧ x ∈ M1 q T m y0 x :=
  lncA_mem_spec hc (sub_gset _ _ (mem_slab hx))

theorem mem_A1 (hc : Compat2 q T) {x : ℕ → α} (hx : x ∈ gfun q T m y0) : x ∈ A1 q T m y0 x :=
  ⟨mem_slab hx, (M1_spec hc hx).2⟩

theorem A1_eq (hc : Compat2 q T) {x z : ℕ → α} (hx : x ∈ gfun q T m y0)
    (hz : z ∈ A1 q T m y0 x) : A1 q T m y0 z = A1 q T m y0 x := by
  have hs : hidx q m z = hidx q m x := slab_eq_of_mem hz.1
  have hM : M1 q T m y0 z = M1 q T m y0 x := by
    unfold M1; rw [hs]; exact lncA_mem_eq hc (M1_spec hc hx).1 hz.2
  unfold A1; rw [hM, hs]

theorem M2_spec (hc : Compat2 q T) {x : ℕ → α} (hx : x ∈ gfun q T m y0) :
    M2 q T m y0 x ∈ lncA q T (m + 2) (A1 q T m y0 x) ∧ x ∈ M2 q T m y0 x :=
  lncA_mem_spec hc (sub_gset _ _ (mem_A1 hc hx))

theorem mem_A2 (hc : Compat2 q T) {x : ℕ → α} (hx : x ∈ gfun q T m y0) : x ∈ A2 q T m y0 x :=
  ⟨mem_A1 hc hx, (M2_spec hc hx).2⟩

theorem A2_sub_A1 (x : ℕ → α) : A2 q T m y0 x ⊆ A1 q T m y0 x := Set.inter_subset_left

theorem A1_eq_of_A2 (hc : Compat2 q T) {x z : ℕ → α} (hx : x ∈ gfun q T m y0)
    (hz : z ∈ A2 q T m y0 x) : A1 q T m y0 z = A1 q T m y0 x := A1_eq hc hx hz.1

theorem M2_eq (hc : Compat2 q T) {x z : ℕ → α} (hx : x ∈ gfun q T m y0)
    (hz : z ∈ A2 q T m y0 x) : M2 q T m y0 z = M2 q T m y0 x := by
  unfold M2; rw [A1_eq_of_A2 hc hx hz]; exact lncA_mem_eq hc (M2_spec hc hx).1 hz.2

theorem A2_eq (hc : Compat2 q T) {x z : ℕ → α} (hx : x ∈ gfun q T m y0)
    (hz : z ∈ A2 q T m y0 x) : A2 q T m y0 z = A2 q T m y0 x := by
  unfold A2; rw [A1_eq_of_A2 hc hx hz, M2_eq hc hx hz]

theorem br_eq (hc : Compat2 q T) {x z : ℕ → α} (hx : x ∈ gfun q T m y0)
    (hz : z ∈ A2 q T m y0 x) : br q T m y0 z = br q T m y0 x := by
  unfold br; rw [A1_eq_of_A2 hc hx hz, M2_eq hc hx hz]

theorem M3_spec (hc : Compat2 q T) {x : ℕ → α} (hx : x ∈ gfun q T m y0) :
    M3 q T m y0 x ∈ lncA q T (m + 3) (A2 q T m y0 x) ∧ x ∈ M3 q T m y0 x :=
  lncA_mem_spec hc (sub_gset _ _ (mem_A2 hc hx))

theorem mem_A3 (hc : Compat2 q T) {x : ℕ → α} (hx : x ∈ gfun q T m y0) : x ∈ A3 q T m y0 x :=
  ⟨mem_A2 hc hx, (M3_spec hc hx).2⟩

theorem A3_sub_A2 (x : ℕ → α) : A3 q T m y0 x ⊆ A2 q T m y0 x := Set.inter_subset_left

theorem M3_eq (hc : Compat2 q T) {x z : ℕ → α} (hx : x ∈ gfun q T m y0)
    (hz : z ∈ A3 q T m y0 x) : M3 q T m y0 z = M3 q T m y0 x := by
  unfold M3; rw [A2_eq hc hx hz.1]; exact lncA_mem_eq hc (M3_spec hc hx).1 hz.2

theorem A3_eq (hc : Compat2 q T) {x z : ℕ → α} (hx : x ∈ gfun q T m y0)
    (hz : z ∈ A3 q T m y0 x) : A3 q T m y0 z = A3 q T m y0 x := by
  unfold A3; rw [A2_eq hc hx hz.1, M3_eq hc hx hz]

theorem pc_eq (hc : Compat2 q T) {x z : ℕ → α} (hx : x ∈ gfun q T m y0)
    (hz : z ∈ A3 q T m y0 x) : pc q T m y0 z = pc q T m y0 x := by
  unfold pc; rw [A2_eq hc hx hz.1, M3_eq hc hx hz]

theorem br_eq_of_A3 (hc : Compat2 q T) {x z : ℕ → α} (hx : x ∈ gfun q T m y0)
    (hz : z ∈ A3 q T m y0 x) : br q T m y0 z = br q T m y0 x := br_eq hc hx hz.1

/-- A3 の 2 つは一致するか交わらない（G_m の分割）。 -/
theorem A3_disj_or_eq (hc : Compat2 q T) {x x' : ℕ → α} (hx : x ∈ gfun q T m y0)
    (hx' : x' ∈ gfun q T m y0) :
    A3 q T m y0 x = A3 q T m y0 x' ∨ Disjoint (A3 q T m y0 x) (A3 q T m y0 x') := by
  by_cases h : (A3 q T m y0 x ∩ A3 q T m y0 x').Nonempty
  · obtain ⟨w, hw, hw'⟩ := h
    have hwG : w ∈ gfun q T m y0 := hw.1.1.1.2
    exact Or.inl ((A3_eq hc hx hw).symm.trans (A3_eq hc hx' hw'))
  · exact Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h))

end Defs.D_0036
