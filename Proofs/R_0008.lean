import Specs.L_0026
import Specs.L_0027
import Specs.L_0028
import Specs.L_0022

namespace Proofs.R_0008

theorem main : Specs.L_0026.stmt → Specs.L_0027.stmt → Specs.L_0028.stmt → Specs.L_0022.stmt := by
  unfold Specs.L_0026.stmt Specs.L_0027.stmt Specs.L_0028.stmt Specs.L_0022.stmt
  intro hA hB hC X _ hM hK x
  obtain ⟨𝓚, h1, h2, h3⟩ := hC X hM (hA X hM) x (hK x)
  exact hB X x 𝓚 h1 h2 h3

end Proofs.R_0008
