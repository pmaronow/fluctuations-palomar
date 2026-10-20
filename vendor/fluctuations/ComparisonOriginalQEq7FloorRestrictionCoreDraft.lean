module

public import ComparisonActualHighWallThetaZeroErrorTransport
public import ComparisonActualHighWallThetaZeroPositiveFloorThermal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem eq7_error_density_nonneg_core {u : ℝ}
    (hu : u ∈ Ioc (0:ℝ) 1) :
    0 ≤ Q.data.thetaZeroErrorDensity Q.lam Q.alpha u := by
  have hcoef := Q.data.theta_zero_coefficient_bounds Q.hlam Q.alpha u
  have hvar := (orderedPath_SK_bounds (n+1) Q.data.hn
    Q.sweepBf Q.sweepHf Q.sweep_bf_monotone
    Q.sweep_hf_monotone hu).2.2.1
  change 0 ≤ Q.data.thetaZeroCoefficient Q.lam Q.alpha u *
    ((orderedPathB (n+1) Q.sweepBf Q.sweepHf u-
      (orderedPathS (n+1) Q.sweepBf Q.sweepHf u)^2)+
      (orderedPathS (n+1) Q.sweepBf Q.sweepHf u-
        Q.sweepRadius u)^2)
  exact mul_nonneg hcoef.1
    (add_nonneg (sub_nonneg.mpr hvar) (sq_nonneg _))

theorem Potential.eq7_positive_full_floor_restrict_core
    (P : Q.Potential) {lo hi : ℝ}
    (hlo : Q.data.s ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) :
    (∫u in lo..hi,
      P.positiveSet.indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u)*
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      (∫u in Q.data.s..hi,
        P.positiveSet.indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) := by
  let f := fun u => P.positiveSet.indicator (fun _ => (1:ℝ))
    (Q.shiftedNativeModel.R u)*
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u
  have hlo1 : lo ≤ 1 := hlohi.trans hhi
  have hi0 := (Q.error_mask_intervalIntegrable P.positiveSet
    P.positiveSet_measurable).mono_set (by
      rw [uIcc_of_le hlo,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc Q.data.hs.1.le hlo1)
  have hi1 := (Q.error_mask_intervalIntegrable P.positiveSet
    P.positiveSet_measurable).mono_set (by
      rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (Q.data.hs.1.le.trans hlo) hhi)
  have Hadd := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  have hLow : 0 ≤ ∫u in Q.data.s..lo,f u := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hlo
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hu0 : u ∈ Ioc (0:ℝ) 1 :=
      ⟨Q.data.hs.1.trans_le hu.1,hu.2.trans hlo1⟩
    have hmask : 0 ≤ P.positiveSet.indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u) :=
      indicator_nonneg (fun _ _ => zero_le_one) _
    exact mul_nonneg hmask (Q.eq7_error_density_nonneg_core hu0)
  dsimp only [f] at Hadd hLow ⊢
  simp only [Q.shiftedNativeModel_radius] at hLow ⊢
  linarith only [Hadd,hLow]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
