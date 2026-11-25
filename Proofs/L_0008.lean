import Specs.L_0008
import Proofs.R_0001
import Proofs.L_0010
import Proofs.L_0011

-- 機械生成: 帰着 R_0001 と子補題の証明の合成
namespace Proofs.L_0008

theorem main : Specs.L_0008.stmt :=
  Proofs.R_0001.main Proofs.L_0010.main Proofs.L_0011.main

end Proofs.L_0008
