import Targets

namespace Defs.D_0010

open Set

/-- 点 `x` の σ-closure-preserving な開局所基（Tamano 1989 の問い・Chen–Wang 第1節の σ 版）。
`x` を含む開集合の族の列 `𝓑 n` で、各層が（任意部分族について）closure-preserving であり、
`x` の任意の開近傍 `U` に対し、ある層のある元 `V ⊆ U` があるもの。 -/
def HasSigmaCPLocalBase {X : Type*} [TopologicalSpace X] (x : X) : Prop :=
  ∃ 𝓑 : ℕ → Set (Set X),
    (∀ n, ∀ V ∈ 𝓑 n, IsOpen V ∧ x ∈ V) ∧
    (∀ n, MSpace.ClosurePreserving (𝓑 n)) ∧
    (∀ U : Set X, IsOpen U → x ∈ U → ∃ n, ∃ V ∈ 𝓑 n, V ⊆ U)

end Defs.D_0010
