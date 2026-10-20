module

public import ComparisonActualHighWallThetaZeroSelectedScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set
set_option autoImplicit false
namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock cl' cu' Az' Ct' D' Bclock' : ℝ}

def weakenConstants {n : ℕ}
    (P : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    ActualThetaZeroOverlapMinimum n m delta cl' cu' Az' C0 Ct' D' Bclock' where
  data := P.data
  lam := P.lam
  hlam := P.hlam
  hld := P.hld
  alpha := P.alpha
  minimum := P.minimum
  xs := P.xs
  z := P.z
  hxs := P.hxs
  hscale := P.hscale
  hsxs := P.hsxs
  hz := P.hz
  hzxs := P.hzxs.trans (mul_le_mul_of_nonneg_right hAz P.hxs.le)
  hdD := P.hdD.trans hD
  hupper := P.hupper
  hlower := P.hlower
  htest := P.htest.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCt
      (laplaceComparisonStrength_pos P.data.d P.hlam P.xs).le)
      (sq_nonneg P.xs))
  regular := by
    intro r hr
    have Hr : 0 ≤ r := P.data.hrbounds.1.le.trans (P.hz.1.trans hr.1)
    exact ⟨(mul_le_mul_of_nonneg_right hcl Hr).trans (P.regular r hr).1,
      (P.regular r hr).2.trans (mul_le_mul_of_nonneg_right hcu Hr)⟩
  hT := P.hT.trans hB

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
