import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0036

namespace Defs.D_0037

/-!
Chen–Wang (arXiv 1809.03763v2) ℜ1（1'th Ln family）, ℜ2（α ch-set）, Construction 6.1 B1–B2
（TeX 2380–2480, 2990–3040 行）の定義。

論文の H(·) は §5 以降「Ln cover の元 ∩ 被覆される集合」の意味で使われる（例: H(m₃, x^i) =
g(m₃, x^i) ∩ H(m₂, x)）。ここでは一貫して `cov n A := lncA q T n A`、部分 = 元 ∩ A とする。
Δ-order の「最初」は `Defs.D_0035.unlab … 0`、番号は `lab`。α : ℕ → ℕ は mad family の元の
増加列挙（α(i) = i 番目の元）。論文の添字は 1 始まりだがここでは 0 始まり。

piece P（番号 v）について:
* `firstC n A` : cov n A の番号 0 の元（可算無限でなければ ∅）。
* `holeBoxes α P v` : ℜ1 の 1'th Ln family: S ∈ cov (α(m+v)) P ごとに firstC (α(m+v)+1) (S ∩ P)。
* `chBoxes α P v` : ℜ2 の α ch-set の箱: S ∈ cov (m+4) P（番号 j）、S' ∈ cov (m+5) (S ∩ P)
  （番号 l）で (j ≤ α v ∧ α v < l) ∨ (α v < j ∧ l ≤ α v)。
* `Gd α P v` : B2 の G_d(v₁^α, jz^n_v): m+5 ≤ α(m+v)+1 なら holeBoxes のうち ⋃ chBoxes と交わるもの、
  そうでなければ chBoxes。
* `Gm1 α P v` : B2 の G_{-1}: cov (α(m+v)+1) P の元で ⋃ Gd と交わらないもの。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0036

variable {α : Type} [LinearOrder α] (q : ℕ ≃ α) (T : Tree2 α) (m : ℕ)

open Classical in
/-- cov n A の番号 0 の元。 -/
noncomputable def firstC (n : ℕ) (A : Set (ℕ → α)) : Set (ℕ → α) :=
  if h : (lncA q T n A).Countable ∧ (lncA q T n A).Infinite then unlab (lncA q T n A) h 0 else ∅

/-- ℜ1: 1'th Ln family（箱の族）。 -/
def holeBoxes (a : ℕ → ℕ) (P : Set (ℕ → α)) (v : ℕ) : Set (Set (ℕ → α)) :=
  {B | ∃ S ∈ lncA q T (a (m + v)) P, B = firstC q T (a (m + v) + 1) (S ∩ P)}

/-- ℜ2: α ch-set の箱。 -/
def chBoxes (a : ℕ → ℕ) (P : Set (ℕ → α)) (v : ℕ) : Set (Set (ℕ → α)) :=
  {B | ∃ S ∈ lncA q T (m + 4) P, B ∈ lncA q T (m + 5) (S ∩ P) ∧
    ((lab (lncA q T (m + 4) P) S ≤ a v ∧ a v < lab (lncA q T (m + 5) (S ∩ P)) B) ∨
     (a v < lab (lncA q T (m + 4) P) S ∧ lab (lncA q T (m + 5) (S ∩ P)) B ≤ a v))}

open Classical in
/-- B2: G_d。 -/
noncomputable def Gd (a : ℕ → ℕ) (P : Set (ℕ → α)) (v : ℕ) : Set (Set (ℕ → α)) :=
  if m + 5 ≤ a (m + v) + 1 then
    {B | B ∈ holeBoxes q T m a P v ∧ (B ∩ ⋃₀ chBoxes q T m a P v).Nonempty}
  else chBoxes q T m a P v

/-- B2: G_{-1}。 -/
def Gm1 (a : ℕ → ℕ) (P : Set (ℕ → α)) (v : ℕ) : Set (Set (ℕ → α)) :=
  {B | B ∈ lncA q T (a (m + v) + 1) P ∧ Disjoint B (⋃₀ Gd q T m a P v)}

variable {q T m}

theorem firstC_mem [Countable α] {n : ℕ} (hn : 0 < n) {A : Set (ℕ → α)}
    (hinf : (lncA q T n A).Infinite) : firstC q T n A ∈ lncA q T n A := by
  classical
  have h : (lncA q T n A).Countable ∧ (lncA q T n A).Infinite := ⟨lncA_countable hn A, hinf⟩
  unfold firstC
  rw [dif_pos h]
  exact unlab_mem _ h 0

end Defs.D_0037
