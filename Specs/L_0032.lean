import Targets
import Defs.D_0001
import Defs.D_0010

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0032
open MSpace Set Topology

def stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (x : X) (W : ℕ → Set X), (∀ n, IsOpen (W n) ∧ IsClosed (W n) ∧ x ∈ W n) → (⋂ n, W n) = {x} → Defs.D_0010.HasSigmaCPLocalBase x → Defs.D_0001.HasCPOuterBase x

end Specs.L_0032
