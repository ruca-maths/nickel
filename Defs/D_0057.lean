import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0056

namespace Defs.D_0057

/-!
稠密性の部品のまとめ 2: **宣言された閉包は ρ では成り立つ**。

* `D1O_sub_EsetO` : D(1σ^α_1, G₁) ⊆ E(α(k+1), p)（すべての k）。
* `gsetE_meets` : z ∈ G_m、ℓ ≥ m+1 なら g[p(k+2), E(α(k+1), p)] ∩ g(ℓ, z) ≠ ∅。
  {g(ℓ, z)} は ρ の近傍基（`Defs.D_0029.prop_3_4`）なので、g[p(k+2), E(α(k+1))] は G_m で ρ-稠密。
  特に Definition B.1 の閉包の主張（`Defs.D_0052.DeclaredClosure`）の ρ 版は成り立つ。
  τ 版で残るのは、z の τ-近傍（E(β) とその補集合、Definition C の集合とその補集合の有限個の交わり）
  がこれらの近い点を必ず含むことだけ。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0039 Defs.D_0056

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

theorem D1O_sub_EsetO (m : ℕ) (y0 : ℕ → α) (a p : ℕ → ℕ) :
    ∀ k, D1O q T m y0 a ⊆ EsetO q T m y0 a p k
  | 0 => by rw [EsetO_zero]; exact sub_gset _ _
  | k + 1 => by
    rw [EsetO_succ]
    exact (D1O_sub_EsetO m y0 a p k).trans ((sub_gset _ _).trans Set.subset_union_left)

theorem gsetE_meets [Countable α] [DenselyOrdered α] [NoMaxOrder α] (hc : Compat2 q T) {m : ℕ}
    (hm : 0 < m) {y0 : ℕ → α} {a : ℕ → ℕ} (ha : StrictMono a) (p : ℕ → ℕ) (k : ℕ)
    {z : ℕ → α} (hz : z ∈ gfun q T m y0) {ℓ : ℕ} (hℓ : m + 1 ≤ ℓ) :
    (gset q T (p (k + 2)) (EsetO q T m y0 a p k) ∩ gfun q T ℓ z).Nonempty := by
  obtain ⟨w, hw, hwz⟩ := D1O_meets hc hm ha hz hℓ
  exact ⟨w, sub_gset _ _ (D1O_sub_EsetO m y0 a p k hw), hwz⟩

end Defs.D_0057
