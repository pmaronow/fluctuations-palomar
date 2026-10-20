module

public import ComparisonCriticalPositiveWallGradientCore

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 8000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem critical_wall_strength_scaled_identity
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : M.xs=M.data.d) (t : ℝ) :
    M.data.g (M.xs*t)/M.xs^2=laplaceComparisonShape t := by
  rw [hfixed,comparison_strength_scaled_parameter_identity]
  have hd:=M.data.hd.ne'
  field_simp

theorem critical_wall_slope_scaled_identity
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : M.xs=M.data.d) (t : ℝ) :
    comparisonLogSlope M.data.g (M.xs*t)=laplaceComparisonSlope t := by
  rw [hfixed,comparison_slope_scaled_parameter_identity
    M.data.hd.ne' (sq_pos_of_pos M.data.hd).ne']
  have hd:=M.data.hd.ne'
  field_simp

theorem critical_wall_scaled_gradient_exact
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : M.xs=M.data.d) {t : ℝ} (ht : t≠0) :
    M.actualVirtualScaledGradient t =
      comparisonScaledStationarity (laplaceComparisonShape t)
        (laplaceComparisonSlope t) t (M.actualScaledRadiusSpin t) -
      laplaceComparisonShape t*laplaceComparisonSlope t/t*
        (M.wallRadiusPointDefect (M.xs*t)/M.xs^2) := by
  rw [show M.actualVirtualScaledGradient t =
      radiusComparisonGradient M.data.g M.alpha.val.val
        (orderedPathS (n+1) M.bf M.hf) (orderedPathB (n+1) M.bf M.hf)
        (M.xs*t)/M.xs^3 from rfl]
  rw [comparison_gradient_scaled_exact M.data.g M.alpha.val.val
      (orderedPathS (n+1) M.bf M.hf) (orderedPathB (n+1) M.bf M.hf)
      M.hxs.ne' ht (laplaceComparisonStrength_pos M.data.d
        (sq_pos_of_pos M.data.hd) _).ne',
    M.critical_wall_strength_scaled_identity hfixed t,
    M.critical_wall_slope_scaled_identity hfixed t]
  rfl

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
