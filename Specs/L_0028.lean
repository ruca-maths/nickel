import Targets

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0028
open MSpace Set Topology

def stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], MSpace.IsM1 X → (∃ D : ℕ → Set X, (∀ n, ∀ A ⊆ D n, IsClosed A) ∧ Dense (⋃ n, D n)) → ∀ x : X, (∃ 𝓚 : Set (Set X), (∀ K ∈ 𝓚, IsClosed K ∧ x ∈ interior K) ∧ (∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚, K ⊆ U) ∧ MSpace.ClosurePreserving 𝓚) → ∃ 𝓚' : Set (Set X), (∀ K ∈ 𝓚', IsClosed K ∧ closure (interior K) = K ∧ x ∈ interior K) ∧ (∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚', K ⊆ U) ∧ MSpace.ClosurePreserving 𝓚'

end Specs.L_0028
