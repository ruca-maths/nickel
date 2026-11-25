import Targets

-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。
namespace Specs.L_0014
open MSpace Set Topology

def stmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X], T1Space X → (∃ G : ℕ → Set X → Set X, IsStratification G) → ∃ g : ℕ → X → Set X, (∀ n x, IsOpen (g n x) ∧ x ∈ g n x) ∧ (∀ n x, g (n + 1) x ⊆ g n x) ∧ (∀ H : Set X, IsClosed H → ∀ x, x ∉ H → ∃ n, x ∉ closure (⋃ y ∈ H, g n y))

end Specs.L_0014
