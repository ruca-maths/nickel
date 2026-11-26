import Targets

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0023
open MSpace Set Topology

def stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], MSpace.IsM1 X → ∃ D : ℕ → Set X, (∀ n, ∀ A ⊆ D n, IsClosed A) ∧ Dense (⋃ n, D n)

end Specs.L_0023
