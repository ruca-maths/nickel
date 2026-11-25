import Specs.L_0010
import Specs.L_0011
import Specs.L_0008

namespace Proofs.R_0001

theorem main : Specs.L_0010.stmt → Specs.L_0011.stmt → Specs.L_0008.stmt := by
  intro h1 h2
  unfold Specs.L_0010.stmt at h1
  unfold Specs.L_0011.stmt at h2
  unfold Specs.L_0008.stmt MSpace.Goals.T3_M3_imp_M2
  intro X _ hX
  exact ⟨hX.1, h2 X hX.1 (h1 X hX)⟩

end Proofs.R_0001
