import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0043

namespace Defs.D_0052

/-!
**Chen–Wang の宣言された閉包（Definition B.1 / Denotation 1）の形式的な主張**。

論文は E(αk, p_k) = Cl_τ g[p_k, E(αn, p_n)] と「宣言」する（k = n+1）。生成位相 τ
（`Defs.D_0043.tauT`、論文に忠実な許容列）で閉包が実際にそうなるかが、Prop 8.3 の Case 2
（TeX 5389–5850）、したがって Theorem 1.b の論文の証明の成否を決める。

* `DeclaredClosure q T m y0 A` : 族 A の各 α、許容列 p、k について、
  Cl_τ g[p (k+2), E(α(k+1), p)] = E(α(k+2), p)。
  ⊆ は E(α(k+2), p) が τ で閉（宣言）であることから常に成り立つ（`declaredClosure_sub`）。
  ⊇（穴のセルが箱の閉包に入る = 稠密性）が未解決の核心。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025
  Defs.D_0031 Defs.D_0035 Defs.D_0039 Defs.D_0040 Defs.D_0043

variable {α : Type} [LinearOrder α]

/-- 宣言された閉包が生成位相で成り立つという主張。 -/
def DeclaredClosure (q : ℕ ≃ α) (T : Tree2 α) (m : ℕ) (y0 : ℕ → α) (A : Set (ℕ → ℕ)) : Prop :=
  ∀ a ∈ A, ∀ p, AdmT m p → ∀ k,
    @closure _ (tauT q T m y0 A) (gset q T (p (k + 2)) (EsetO q T m y0 a p k)) ⊇
      EsetO q T m y0 a p (k + 1)

variable {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

/-- 逆向きの包含は常に成り立つ（k ≥ 1 で E は宣言により閉）。 -/
theorem declaredClosure_sub {A : Set (ℕ → ℕ)} {a : ℕ → ℕ} (ha : a ∈ A) {p : ℕ → ℕ}
    (hp : AdmT m p) (k : ℕ) :
    @closure _ (tauT q T m y0 A) (gset q T (p (k + 3)) (EsetO q T m y0 a p (k + 1))) ⊆
      EsetO q T m y0 a p (k + 2) := by
  letI := tauT q T m y0 A
  apply closure_minimal
  · rw [EsetO_succ q T m y0 a p (k + 1)]; exact Set.subset_union_left
  · exact isClosed_tau_of_compl_mem (Or.inl (Or.inr ⟨a, ha, p, hp, k + 1, Or.inr rfl⟩))

end Defs.D_0052
