import Specs.L_0029
import Specs.L_0030
import Specs.L_0004
import Specs.L_0009

namespace Proofs.R_0009

theorem main : Specs.L_0029.stmt → Specs.L_0030.stmt → Specs.L_0004.stmt → ¬ Specs.L_0009.stmt := by
  intro h1 h2 h4 hT
  unfold Specs.L_0029.stmt at h1
  unfold Specs.L_0030.stmt at h2
  unfold Specs.L_0004.stmt MSpace.Goals.T2a_M3_iff_stratifiable at h4
  unfold Specs.L_0009.stmt MSpace.Goals.Tinf_M3_imp_M1 at hT
  obtain ⟨Y, tY, hS, y, hy⟩ := h2
  exact hy (h1 Y (hT Y ((h4 Y).2 hS)) y)

end Proofs.R_0009
