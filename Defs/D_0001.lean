import Targets

namespace Defs.D_0001

open Set

/-- 点 `x` の closure-preserving な外基（outer base, Ito 1985 / Mizokami の用法）。
`x` を含む開集合の族 `𝓥` で、`x` の任意の開近傍 `U` に対し `V ⊆ U` となる `V ∈ 𝓥` があり、
`𝓥` が（任意部分族について）closure-preserving であるもの。
Chen–Wang 第8–9節の「近傍基 V_y（各 V_λ は開）」と同じ形。 -/
def HasCPOuterBase {X : Type*} [TopologicalSpace X] (x : X) : Prop :=
  ∃ 𝓥 : Set (Set X),
    (∀ V ∈ 𝓥, IsOpen V ∧ x ∈ V) ∧
    (∀ U : Set X, IsOpen U → x ∈ U → ∃ V ∈ 𝓥, V ⊆ U) ∧
    MSpace.ClosurePreserving 𝓥

end Defs.D_0001
