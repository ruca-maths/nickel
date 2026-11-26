import Targets
import Defs.D_0001

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0019
open MSpace Set Topology

def stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], MSpace.IsM1 X → ∀ x : X, Defs.D_0001.HasCPOuterBase x

end Specs.L_0019
