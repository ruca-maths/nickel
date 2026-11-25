import Specs.L_0014
import Specs.L_0015
import Specs.L_0016
import Specs.L_0011

namespace Proofs.R_0003

theorem main : Specs.L_0014.stmt → Specs.L_0015.stmt → Specs.L_0016.stmt → Specs.L_0011.stmt := by
  intro h1 h2 h3
  unfold Specs.L_0011.stmt
  intro X _ hT3 hG
  exact h3 X (h2 X hT3 (h1 X inferInstance hG))

end Proofs.R_0003
