module

public import ComparisonActualHighWallStarClockDistinct
public import ComparisonCriticalPositiveWallGradientCore
public import ComparisonStationarityDensityScaling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Hierarchy

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_positive_wall_radius_scalar_clock_exact
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc M.data.rmin 1) :
    actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r) =
      comparisonNativeScalarClock 0 M.data.T (M.data.g r) r (M.radiusS r) := by
  have hlow : M.data.s ≤ M.alpha.val.val r := by
    have H := M.alpha.val.property.2 hr.1
    simpa only [M.alpha.property.1] using H
  have hu : M.alpha.val.val r∈Icc M.data.s 1 :=
    ⟨hlow,(M.alpha.val.property.1 r).2⟩
  have hcomp := M.high_mass_clock_compensation hu
  rw [M.data.wallRadius_inverse M.alpha hr] at hcomp
  change actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r) -
      M.data.T*M.radiusS r = M.data.g r*(r-M.radiusS r) at hcomp
  unfold comparisonNativeScalarClock
  linarith only [hcomp]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
