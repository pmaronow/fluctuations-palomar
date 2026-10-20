module

public import SKProof.Port.ComparisonActualOriginalQClocks
public import SKProof.Port.ComparisonActualOriginalQPairedFarSchedule
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
theorem radius_mixed_clock_eq_nativeScalarClock
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc M.data.rmin 1) :
    actualMixedClock (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r)=
      comparisonNativeScalarClock (M.h (M.alpha.val.val r)) (M.b (M.alpha.val.val r))
        (laplaceComparisonStrength M.data.d M.lam r) r
        (orderedPathS (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r)) := by
  have hinv := M.sweepRadius_inverse hr

  have H := M.inherited_mixed_clock_eq_nativeScalarClock (M.alpha.val.property.1 r)
  change M.sweepRadius (M.alpha.val.val r)=r at hinv
  have hmass : M.data.s≤M.alpha.val.val r := by
    have HH:=M.alpha.val.property.2 hr.1
    rw [M.alpha.property.1] at HH
    exact HH
  have he : M.sweepCoefficient (M.alpha.val.val r)=laplaceComparisonStrength M.data.d M.lam (M.sweepRadius (M.alpha.val.val r)) := by
    change omittedStrengthCoefficient M.data.d M.data.s M.sweepRadius M.lam (M.alpha.val.val r)=_
    rw [omittedStrengthCoefficient,ite_eq_left hmass]
  rw [he,hinv] at H
  exact H
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
