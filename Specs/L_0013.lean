import Targets

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0013
open MSpace Set Topology

def stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], IsStratifiable X → ∀ W : ℕ → Set X, (∀ n, IsOpen (W n)) → ⋃ n, W n = univ → ∃ W' : ℕ → Set X, (∀ n, IsOpen (W' n)) ∧ (∀ n, W' n ⊆ W n) ∧ LocallyFinite W' ∧ ⋃ n, W' n = univ

end Specs.L_0013
