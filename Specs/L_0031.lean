import Targets
import Defs.D_0001

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0031
open MSpace Set Topology

def stmt : Prop :=
  ∃ (Y : Type) (_ : TopologicalSpace Y), MSpace.IsStratifiable Y ∧ ∃ y : Y, (∃ W : ℕ → Set Y, (∀ n, IsOpen (W n) ∧ IsClosed (W n) ∧ y ∈ W n) ∧ (⋂ n, W n) = {y}) ∧ ¬ Defs.D_0001.HasCPOuterBase y

end Specs.L_0031
