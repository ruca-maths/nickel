import Targets
import Defs.D_0010

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0029
open MSpace Set Topology

def stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], MSpace.IsM1 X → ∀ x : X, Defs.D_0010.HasSigmaCPLocalBase x

end Specs.L_0029
