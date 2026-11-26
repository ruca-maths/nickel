import Targets
import Defs.D_0001

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0022
open MSpace Set Topology

def stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], MSpace.IsM1 X → (∀ x : X, ∃ 𝓚 : Set (Set X), (∀ K ∈ 𝓚, IsClosed K ∧ x ∈ interior K) ∧ (∀ U : Set X, IsOpen U → x ∈ U → ∃ K ∈ 𝓚, K ⊆ U) ∧ MSpace.ClosurePreserving 𝓚) → ∀ x : X, Defs.D_0001.HasCPOuterBase x

end Specs.L_0022
