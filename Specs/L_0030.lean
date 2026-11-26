import Targets
import Defs.D_0010

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0030
open MSpace Set Topology

def stmt : Prop :=
  ∃ (Y : Type) (_ : TopologicalSpace Y), MSpace.IsStratifiable Y ∧ ∃ y : Y, ¬ Defs.D_0010.HasSigmaCPLocalBase y

end Specs.L_0030
