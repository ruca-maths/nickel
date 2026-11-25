-- Mathlib 全体ではなく必要な部分だけを import する（メモリ 8GB 級の環境で検証を速くするため）
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Bases
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Metrizable.Basic

/-!
# T0: M₁・M₂・M₃ 空間と関連概念の定義（ロック領域・人間のみ編集）

このファイルは研究の「仕様」そのものである。Lean カーネルが保証するのは
「ここに書いた定義について証明が正しい」ことだけなので、定義が意図した数学と
一致しているかは人間が原典と照合して承認する（`tools/research.sh approve-targets`）。

## 要原典確認の点（承認前に必ず確認すること）
* Ceder (1961) は M₁・M₂・M₃ を正則 T₁ 空間として定義している、という前提で
  `T3Space`（= T₀ + 正則 ⇒ T₁ かつ正則）を課している。
* pair-base の対 `(P₁, P₂)` は「`P₁` が開集合で `P₁ ⊆ P₂`」とした（`P₂` は任意の集合）。
* stratification は Borges の閉集合版（Gruenhage のハンドブックの形）を採用し、
  単調減少性 `G (n+1) H ⊆ G n H` は課していない（取り直せるので同値）。
* closure-preserving は **任意の** 部分族について定義する（有限部分族ではない）。
-/

universe u

namespace MSpace

open Set TopologicalSpace

section Families

variable {X : Type u} [TopologicalSpace X]

/-- 族 `𝓕` が closure-preserving：任意の部分族 `𝓖 ⊆ 𝓕` について
`closure (⋃₀ 𝓖) = ⋃₀ (closure '' 𝓖)`。（`⊇` は常に成り立つ。） -/
def ClosurePreserving (𝓕 : Set (Set X)) : Prop :=
  ∀ 𝓖 ⊆ 𝓕, closure (⋃₀ 𝓖) = ⋃₀ (closure '' 𝓖)

/-- 族 `𝓑` が σ-closure-preserving：可算個の closure-preserving 族の和集合。 -/
def SigmaClosurePreserving (𝓑 : Set (Set X)) : Prop :=
  ∃ 𝓑' : ℕ → Set (Set X), (∀ n, ClosurePreserving (𝓑' n)) ∧ 𝓑 = ⋃ n, 𝓑' n

/-- quasi-base：各点 `x` と `x` の開近傍 `U` に対し、`x ∈ int B ⊆ B ⊆ U` となる
`B ∈ 𝓑` がある（`B` は開集合とは限らない）。 -/
def IsQuasiBase (𝓑 : Set (Set X)) : Prop :=
  ∀ x : X, ∀ U : Set X, IsOpen U → x ∈ U → ∃ B ∈ 𝓑, x ∈ interior B ∧ B ⊆ U

/-- pair-base：対 `(P₁, P₂)` の族で、`P₁` は開、`P₁ ⊆ P₂`、かつ各点 `x` と
開近傍 `U` に対し `x ∈ P₁ ⊆ P₂ ⊆ U` となる対がある。 -/
def IsPairBase (𝓟 : Set (Set X × Set X)) : Prop :=
  (∀ p ∈ 𝓟, IsOpen p.1 ∧ p.1 ⊆ p.2) ∧
  ∀ x : X, ∀ U : Set X, IsOpen U → x ∈ U → ∃ p ∈ 𝓟, x ∈ p.1 ∧ p.2 ⊆ U

/-- 対の族 `𝓟` が cushioned：任意の部分族 `𝓠 ⊆ 𝓟` について
`closure (⋃_{p ∈ 𝓠} p.1) ⊆ ⋃_{p ∈ 𝓠} p.2`。 -/
def Cushioned (𝓟 : Set (Set X × Set X)) : Prop :=
  ∀ 𝓠 ⊆ 𝓟, closure (⋃ p ∈ 𝓠, p.1) ⊆ ⋃ p ∈ 𝓠, p.2

/-- σ-cushioned：可算個の cushioned 族の和集合。 -/
def SigmaCushioned (𝓟 : Set (Set X × Set X)) : Prop :=
  ∃ 𝓟' : ℕ → Set (Set X × Set X), (∀ n, Cushioned (𝓟' n)) ∧ 𝓟 = ⋃ n, 𝓟' n

/-- stratification（Borges, 閉集合版）：各 `n` と閉集合 `H` に開集合 `G n H` を対応させ、
`H ⊆ G n H`、`⋂ n, closure (G n H) = H`、`H ⊆ K ⇒ G n H ⊆ G n K` を満たす。 -/
def IsStratification (G : ℕ → Set X → Set X) : Prop :=
  (∀ n H, IsClosed H → IsOpen (G n H)) ∧
  (∀ n H, IsClosed H → H ⊆ G n H) ∧
  (∀ H, IsClosed H → ⋂ n, closure (G n H) = H) ∧
  (∀ n H K, IsClosed H → IsClosed K → H ⊆ K → G n H ⊆ G n K)

end Families

/-- M₁ 空間（Ceder）：正則 T₁ で、σ-closure-preserving な開基を持つ。 -/
def IsM1 (X : Type u) [TopologicalSpace X] : Prop :=
  T3Space X ∧ ∃ 𝓑 : Set (Set X), IsTopologicalBasis 𝓑 ∧ SigmaClosurePreserving 𝓑

/-- M₂ 空間（Ceder）：正則 T₁ で、σ-closure-preserving な quasi-base を持つ。 -/
def IsM2 (X : Type u) [TopologicalSpace X] : Prop :=
  T3Space X ∧ ∃ 𝓑 : Set (Set X), IsQuasiBase 𝓑 ∧ SigmaClosurePreserving 𝓑

/-- M₃ 空間（Ceder の原定義）：正則 T₁ で、σ-cushioned な pair-base を持つ。 -/
def IsM3 (X : Type u) [TopologicalSpace X] : Prop :=
  T3Space X ∧ ∃ 𝓟 : Set (Set X × Set X), IsPairBase 𝓟 ∧ SigmaCushioned 𝓟

/-- stratifiable 空間（Borges）：T₁ で stratification を持つ。 -/
def IsStratifiable (X : Type u) [TopologicalSpace X] : Prop :=
  T1Space X ∧ ∃ G : ℕ → Set X → Set X, IsStratification G

/-- 完全正規：正規で、すべての閉集合が Gδ。 -/
def IsPerfectlyNormal (X : Type u) [TopologicalSpace X] : Prop :=
  NormalSpace X ∧ ∀ C : Set X, IsClosed C → IsGδ C

end MSpace
