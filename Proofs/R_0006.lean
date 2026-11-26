import Specs.L_0021
import Specs.L_0022
import Specs.L_0019

namespace Proofs.R_0006

theorem main : Specs.L_0021.stmt → Specs.L_0022.stmt → Specs.L_0019.stmt := by
  unfold Specs.L_0021.stmt Specs.L_0022.stmt Specs.L_0019.stmt
  intro hA hB X _ hM x
  exact hB X hM (hA X hM) x

end Proofs.R_0006
