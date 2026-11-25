import Targets

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0010
open MSpace Set Topology

def stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], IsM3 X → ∃ G : ℕ → Set X → Set X, IsStratification G

end Specs.L_0010
