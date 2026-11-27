import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0043
import Defs.D_0052

namespace Defs.D_0058

/-!
τ-閉包の判定法（宣言された閉包 `Defs.D_0052.DeclaredClosure` の τ 版への帰着）。

`mem_closure_tauT_of` : 点列（一般にフィルター F に沿った族）w が S に入り、z に ρ で収束し
（各 g(ℓ, z) に最終的に入る）、さらに次の 3 条件を満たせば z ∈ Cl_τ S。
1. z が E(β(k+1), p′) に入るが、その ρ-開な部分 g[p′(k+2), E(β(k+1−1))] には入らない（穴のセルだけ）
   なら、w は最終的に E(β(k+1), p′) に入る。
2. z ∉ E(β(k+1), p′) なら、w は最終的に E(β(k+1), p′) の外。
3. z が Definition C の集合 g[ph, g(ℓ, x) − E] の外なら、w も最終的にその外。
ρ 由来の部分基（g(l, x′) とその補集合）、Definition C の集合そのもの、E の ρ-開な部分は
すべて ρ-開なので、ρ-収束から自動的に従う。よって稠密性の証明は、上の 3 条件
（E(β) とその補集合、Definition C の補集合）だけを調べればよい。
-/

open Filter Topology Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0009 Defs.D_0012
  Defs.D_0024 Defs.D_0025 Defs.D_0029 Defs.D_0031 Defs.D_0034 Defs.D_0035 Defs.D_0039
  Defs.D_0043

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α} {m : ℕ} {y0 : ℕ → α}

/-- 生成位相での閉包の判定（部分基の各元に最終的に入る族）。 -/
theorem mem_closure_generateFrom_of {X ι : Type*} {B : Set (Set X)} {S : Set X} {z : X}
    (F : Filter ι) [F.NeBot] (w : ι → X) (hwS : ∀ᶠ i in F, w i ∈ S)
    (hB : ∀ s ∈ B, z ∈ s → ∀ᶠ i in F, w i ∈ s) :
    z ∈ @closure X (.generateFrom B) S := by
  let _ : TopologicalSpace X := .generateFrom B
  have ht : Tendsto w F (𝓝 z) := by
    rw [TopologicalSpace.nhds_generateFrom]
    refine tendsto_iInf.2 fun s => tendsto_iInf.2 fun hs => tendsto_principal.2 ?_
    exact hB s hs.2 hs.1
  exact mem_closure_of_tendsto ht hwS

theorem gset_isOpen_p (n : ℕ) (A : Set (ℕ → α)) : @IsOpen _ (ptop α) (gset q T n A) := by
  let _ := ptop α
  exact isOpen_biUnion fun x _ => gfun_isOpen_p q T n x

variable [NoMaxOrder α]

/-- ρ-開集合には、z に ρ で収束する族が最終的に入る。 -/
theorem eventually_of_rhoOpen (hc : Compat2 q T) {ι : Type*} {F : Filter ι}
    {w : ι → (ℕ → α)} {z : ℕ → α}
    (hρ : ∀ ℓ, 0 < ℓ → ∀ᶠ i in F, w i ∈ gfun q T ℓ z) {U : Set (ℕ → α)}
    (hU : @IsOpen _ (ptop α) U) (hz : z ∈ U) : ∀ᶠ i in F, w i ∈ U := by
  obtain ⟨n0, hn0⟩ := prop_3_4_eventually hc z U hU hz
  exact (hρ (n0 + 1) (by omega)).mono fun i hi => hn0 (n0 + 1) (by omega) hi

/-- **τ-閉包の判定法**。 -/
theorem mem_closure_tauT_of (hc : Compat2 q T) {A : Set (ℕ → ℕ)} {S : Set (ℕ → α)}
    {z : ℕ → α} {ι : Type*} (F : Filter ι) [F.NeBot] (w : ι → (ℕ → α))
    (hwS : ∀ᶠ i in F, w i ∈ S)
    (hρ : ∀ ℓ, 0 < ℓ → ∀ᶠ i in F, w i ∈ gfun q T ℓ z)
    (hE1 : ∀ a ∈ A, ∀ p, AdmT m p → ∀ k, z ∈ EsetO q T m y0 a p (k + 1) →
      z ∉ gset q T (p (k + 2)) (EsetO q T m y0 a p k) →
      ∀ᶠ i in F, w i ∈ EsetO q T m y0 a p (k + 1))
    (hE2 : ∀ a ∈ A, ∀ p, AdmT m p → ∀ k, z ∉ EsetO q T m y0 a p (k + 1) →
      ∀ᶠ i in F, w i ∉ EsetO q T m y0 a p (k + 1))
    (hC : ∀ a ∈ A, ∀ p, AdmT m p → ∀ k ℓ ph x, m + 5 < ℓ → p (k + 2) < ph →
      z ∉ gset q T ph (gfun q T ℓ x \ EsetO q T m y0 a p (k + 1)) →
      ∀ᶠ i in F, w i ∉ gset q T ph (gfun q T ℓ x \ EsetO q T m y0 a p (k + 1))) :
    z ∈ @closure _ (tauT q T m y0 A) S := by
  refine mem_closure_generateFrom_of F w hwS fun s hs hzs => ?_
  have hopen := fun {U : Set (ℕ → α)} (hU : @IsOpen _ (ptop α) U) (hz : z ∈ U) =>
    eventually_of_rhoOpen hc hρ hU hz
  rcases hs with (⟨l, x', -, rfl | rfl⟩ | ⟨a, ha, p, hp, k, rfl | rfl⟩) |
      ⟨a, ha, p, hp, k, ℓ, ph, x, hℓ, hph, rfl | rfl⟩
  · exact hopen (gfun_isOpen_p q T l x') hzs
  · exact hopen (gfun_isClosed_p q T l x').isOpen_compl hzs
  · by_cases hg : z ∈ gset q T (p (k + 2)) (EsetO q T m y0 a p k)
    · refine (hopen (gset_isOpen_p _ _) hg).mono fun i hi => ?_
      rw [EsetO_succ]; exact Or.inl hi
    · exact hE1 a ha p hp k hzs hg
  · exact hE2 a ha p hp k hzs
  · exact hopen (gset_isOpen_p _ _) hzs
  · exact hC a ha p hp k ℓ ph x hℓ hph hzs

end Defs.D_0058
