import Specs.L_0031
import Specs.L_0032
import Specs.L_0030

namespace Proofs.R_0010

theorem main : Specs.L_0031.stmt → Specs.L_0032.stmt → Specs.L_0030.stmt := by
  intro h1 h2
  unfold Specs.L_0031.stmt at h1
  unfold Specs.L_0032.stmt at h2
  unfold Specs.L_0030.stmt
  obtain ⟨Y, tY, hS, y, ⟨W, hW, hWy⟩, hno⟩ := h1
  exact ⟨Y, tY, hS, y, fun hs => hno (@h2 Y tY y W hW hWy hs)⟩

end Proofs.R_0010
