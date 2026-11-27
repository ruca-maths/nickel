import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0052

namespace Defs.D_0062

/-!
**Ln cover の「最初の元」を任意の選択関数にした一般化版**（タスク 2: 宣言された閉包の列挙依存性）。

論文の Δ-order は 𝒥(n,i) の列挙が任意（TeX 760–800）なので、Ln cover の最初の元は任意に選べる。
`Defs.D_0037.firstC`（固定された列挙 `lab` の番号 0 の元）を選択関数 `fc : ℕ → Set (ℕ → α) → Set (ℕ → α)`
に置き換えて、G_d・D・E・τ・宣言された閉包を定義し直す（`…F`）。
`fc := firstC q T` のとき元の定義と一致する（`EsetOF_firstC`, `tauTF_firstC`, `declaredClosureF_firstC`）。
選択関数の妥当性は `ValidFC`（被覆が可算無限なら fc n A ∈ lncA n A）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0034 Defs.D_0035 Defs.D_0036 Defs.D_0037 Defs.D_0038 Defs.D_0039 Defs.D_0043 Defs.D_0052

variable {α : Type} [LinearOrder α] (q : ℕ ≃ α) (T : Tree2 α) (m : ℕ) (y0 : ℕ → α)
  (fc : ℕ → Set (ℕ → α) → Set (ℕ → α))

/-- 選択関数の妥当性。 -/
def ValidFC : Prop :=
  ∀ n A, (lncA q T n A).Countable → (lncA q T n A).Infinite → fc n A ∈ lncA q T n A

def holeBoxesF (a : ℕ → ℕ) (P : Set (ℕ → α)) (v : ℕ) : Set (Set (ℕ → α)) :=
  {B | ∃ S ∈ lncA q T (a (m + v)) P, B = fc (a (m + v) + 1) (S ∩ P)}

open Classical in
noncomputable def GdF (a : ℕ → ℕ) (P : Set (ℕ → α)) (v : ℕ) : Set (Set (ℕ → α)) :=
  if m + 5 ≤ a (m + v) + 1 then
    {B | B ∈ holeBoxesF q T m fc a P v ∧ (B ∩ ⋃₀ chBoxes q T m a P v).Nonempty}
  else chBoxes q T m a P v

noncomputable def holeBoxesUF (a : ℕ → ℕ) (k r : ℕ) (A1 : Set (ℕ → α)) : Set (ℕ → α) :=
  ⋃ Pv ∈ {Pv | Pv ∈ pieces q T m A1 k ∧ r ≤ Pv.2}, ⋃₀ GdF q T m fc a Pv.1 Pv.2

noncomputable def holeCellsF (a : ℕ → ℕ) (k r : ℕ) (A1 : Set (ℕ → α)) : Set (ℕ → α) :=
  ⋃ Pv ∈ {Pv | Pv ∈ pieces q T m A1 k ∧ r ≤ Pv.2},
    ⋃ B ∈ GdF q T m fc a Pv.1 Pv.2, B ∩ Pv.1

noncomputable def D1slabOF (a : ℕ → ℕ) : ℕ → Set (ℕ → α) :=
  slabRec (fun c prior => ⋃ S ∈ allowedO q T m y0 c prior,
    holeBoxesUF q T m fc a 1 0 (slabO q T m y0 c ∩ S))

noncomputable def D1OF (a : ℕ → ℕ) : Set (ℕ → α) := ⋃ c, D1slabOF q T m y0 fc a c

noncomputable def HkOF (a : ℕ → ℕ) (p : ℕ → ℕ) (k : ℕ) (prevD : ℕ → Set (ℕ → α)) :
    ℕ → Set (ℕ → α) :=
  slabRec (fun c prior => ⋃ S ∈ allowedO q T m y0 c (prior ∪ prevD c),
    holeCellsF q T m fc a (k + 2) (p (k + 2)) (slabO q T m y0 c ∩ S))

noncomputable def EseqOF (a : ℕ → ℕ) (p : ℕ → ℕ) : ℕ → Set (ℕ → α) × (ℕ → Set (ℕ → α))
  | 0 => (gset q T (p 1) (D1OF q T m y0 fc a), fun c => gset q T (p 1) (D1slabOF q T m y0 fc a c))
  | k + 1 =>
    let prev := EseqOF a p k
    let Hk := HkOF q T m y0 fc a p k prev.2
    (gset q T (p (k + 2)) prev.1 ∪ ⋃ c, Hk c, fun c => prev.2 c ∪ gset q T (p (k + 2)) (Hk c))

noncomputable def EsetOF (a : ℕ → ℕ) (p : ℕ → ℕ) (k : ℕ) : Set (ℕ → α) :=
  (EseqOF q T m y0 fc a p k).1

noncomputable def tauSubTF (A : Set (ℕ → ℕ)) : Set (Set (ℕ → α)) :=
  rhoSub q T ∪
  {s | ∃ a ∈ A, ∃ p, AdmT m p ∧ ∃ k,
      s = EsetOF q T m y0 fc a p (k + 1) ∨ s = (EsetOF q T m y0 fc a p (k + 1))ᶜ} ∪
  {s | ∃ a ∈ A, ∃ p, AdmT m p ∧ ∃ k ℓ ph x, m + 5 < ℓ ∧ p (k + 2) < ph ∧
      (s = gset q T ph (gfun q T ℓ x \ EsetOF q T m y0 fc a p (k + 1)) ∨
       s = (gset q T ph (gfun q T ℓ x \ EsetOF q T m y0 fc a p (k + 1)))ᶜ)}

noncomputable def tauTF (A : Set (ℕ → ℕ)) : TopologicalSpace (ℕ → α) :=
  .generateFrom (tauSubTF q T m y0 fc A)

def DeclaredClosureF (A : Set (ℕ → ℕ)) : Prop :=
  ∀ a ∈ A, ∀ p, AdmT m p → ∀ k,
    @closure _ (tauTF q T m y0 fc A) (gset q T (p (k + 2)) (EsetOF q T m y0 fc a p k)) ⊇
      EsetOF q T m y0 fc a p (k + 1)

/-! ### fc := firstC で元の定義に戻る -/

theorem GdF_firstC : GdF q T m (firstC q T) = Gd q T m := rfl

theorem D1slabOF_firstC : D1slabOF q T m y0 (firstC q T) = D1slabO q T m y0 := rfl

theorem HkOF_firstC : HkOF q T m y0 (firstC q T) = HkO q T m y0 := rfl

theorem EseqOF_firstC (a p : ℕ → ℕ) :
    ∀ k, EseqOF q T m y0 (firstC q T) a p k = EseqO q T m y0 a p k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [EseqOF, EseqO, ih, HkOF_firstC]

theorem EsetOF_firstC : EsetOF q T m y0 (firstC q T) = EsetO q T m y0 := by
  funext a p k
  unfold EsetOF EsetO
  rw [EseqOF_firstC]

theorem tauTF_firstC : tauTF q T m y0 (firstC q T) = tauT q T m y0 := by
  funext A
  unfold tauTF tauSubTF tauT tauSubT
  rw [EsetOF_firstC]

theorem declaredClosureF_firstC (A : Set (ℕ → ℕ)) :
    DeclaredClosureF q T m y0 (firstC q T) A ↔ DeclaredClosure q T m y0 A := by
  unfold DeclaredClosureF DeclaredClosure
  rw [EsetOF_firstC, tauTF_firstC]

theorem validFC_firstC [Countable α] : ValidFC q T (firstC q T) := by
  intro n A hc hinf
  classical
  unfold firstC
  rw [dif_pos ⟨hc, hinf⟩]
  exact unlab_mem _ _ 0

end Defs.D_0062
