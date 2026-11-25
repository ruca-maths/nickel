import Targets

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0011
open MSpace Set Topology

def stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], T3Space X → (∃ G : ℕ → Set X → Set X, IsStratification G) → ∃ 𝓑 : Set (Set X), IsQuasiBase 𝓑 ∧ SigmaClosurePreserving 𝓑

end Specs.L_0011
