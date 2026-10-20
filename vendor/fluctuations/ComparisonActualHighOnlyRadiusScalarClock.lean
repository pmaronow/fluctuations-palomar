module

public import ComparisonActualHighOnlyClocks
public import ComparisonActualHighOnlyPairedFarSchedule

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
theorem radius_mixed_clock_eq_nativeScalarClock
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r)=
      comparisonNativeScalarClock (M.h (M.alpha.val.val r)) (M.b (M.alpha.val.val r))
        (laplaceComparisonStrength M.context.d M.lam r) r
        (orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r)) := by
  have hinv := omittedSweepQuantile_inverse zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hr
  have H := M.inherited_mixed_clock_eq_nativeScalarClock (M.alpha.val.property.1 r)
  change M.R (M.alpha.val.val r)=r at hinv
  have hmass : M.data.s≤M.alpha.val.val r := by
    have HH:=M.alpha.val.property.2 hr.1
    rw [M.alpha.property.1] at HH
    exact HH
  have he : M.coefficient (M.alpha.val.val r)=laplaceComparisonStrength M.context.d M.lam (M.R (M.alpha.val.val r)) := by
    change omittedStrengthCoefficient M.data.d M.data.s M.R M.lam (M.alpha.val.val r)=_
    rw [omittedStrengthCoefficient,ite_eq_left hmass]
  rw [he,hinv] at H
  exact H
end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
