module

public import ComparisonActualHighWallThetaZeroErrorTransport
public import ComparisonNativeClockRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  (Q:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

theorem bare_matrix_pullback_constant {r:ℝ} (hr:r∈Icc Q.data.rmin 1):
    Q.data.thetaZeroHighOnlyData.b (Q.alpha.val.val r)=Q.data.T := by
  have H:=inverseConstraint_mass_mem Q.data.hr Q.data.hc Q.data.hk
    Q.data.hkc Q.alpha hr
  change wallBareMatrix Q.data.T Q.data.epsilon 0 Q.data.s (Q.alpha.val.val r)=Q.data.T
  simp [wallBareMatrix,not_lt.mpr H.1]

theorem bare_field_pullback_zero (r:ℝ):
    Q.data.thetaZeroHighOnlyData.h (Q.alpha.val.val r)=0 := rfl

theorem bare_pullback_clock_regularity:
    NativePullbackClockRegularity Q.alpha.val.val
      Q.data.thetaZeroHighOnlyData.b Q.data.thetaZeroHighOnlyData.h
      Q.data.rmin 1 := by
  apply NativePullbackClockRegularity.smooth 0 0
  · apply LipschitzOnWith.of_dist_le_mul
    intro r hr t ht
    rw [Q.bare_matrix_pullback_constant hr,Q.bare_matrix_pullback_constant ht]
    simp
  · apply LipschitzOnWith.of_dist_le_mul
    intro r hr t ht
    rw [Q.bare_field_pullback_zero,Q.bare_field_pullback_zero]
    simp

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
