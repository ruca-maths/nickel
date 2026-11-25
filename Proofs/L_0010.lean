import Specs.L_0010
import Proofs.L_0004

namespace Proofs.L_0010

theorem main : Specs.L_0010.stmt := by
  unfold Specs.L_0010.stmt
  intro X _ h
  have h4 := Proofs.L_0004.main
  unfold Specs.L_0004.stmt MSpace.Goals.T2a_M3_iff_stratifiable at h4
  exact ((h4 X).mp h).2

end Proofs.L_0010
