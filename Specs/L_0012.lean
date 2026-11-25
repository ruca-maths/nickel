import Targets

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0012
open MSpace Set Topology

def stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], IsStratifiable X → ∀ (ι : Type) (u : ι → Set X), (∀ i, IsOpen (u i)) → ⋃ i, u i = univ → ∃ (β : Type) (v : ℕ → β → Set X), (∀ n b, IsOpen (v n b)) ∧ (∀ n, LocallyFinite (v n)) ∧ (∀ n b, ∃ i, v n b ⊆ u i) ∧ ⋃ n, ⋃ b, v n b = univ

end Specs.L_0012
