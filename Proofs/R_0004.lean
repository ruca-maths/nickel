import Specs.L_0017
import Specs.L_0018
import Specs.L_0015
import Proofs.L_0011

namespace Proofs.R_0004

theorem main : Specs.L_0017.stmt → Specs.L_0018.stmt → Specs.L_0015.stmt := by
  intro h1 h2
  unfold Specs.L_0015.stmt
  intro X _ hT3 hg
  exact h2 X hT3 (Proofs.L_0011.main X hT3 (h1 X hg))

end Proofs.R_0004
