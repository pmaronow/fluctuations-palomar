module

public import ComparisonNativeActualMeanRawUpper
public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ} {n : ℕ}

theorem radius_mixed_clock_eq_nativeScalarClock
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r)=
      comparisonNativeScalarClock (M.h (M.alpha.val.val r)) (M.b (M.alpha.val.val r))
        (laplaceComparisonStrength M.context.d M.lam r) r
        (orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r)) := by
  have hinv := comparisonSweepQuantile_inverse M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hr
  have H := M.inherited_mixed_clock_eq_nativeScalarClock (M.alpha.val.property.1 r)
  change M.R (M.alpha.val.val r)=r at hinv
  rw [hinv] at H
  exact H

theorem rescaled_radius_scalar_gap_integrableOn
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {T : ℝ} (hT : 0 < T) (alpha : boundedMassProfiles) (a b : ℝ) :
    IntegrableOn (fun t=>(orderedPathS (n+1) M.bf M.hf (M.alpha.val.val (M.xs*t))-
      scalarCovarianceResponse hT alpha (actualMixedClock (n+1) M.bf M.hf
        (M.alpha.val.val (M.xs*t))))/M.xs^3) (Icc a b) := by
  let u := fun t=>M.alpha.val.val (M.xs*t)
  have hu t : u t∈Icc (0:ℝ) 1 := M.alpha.val.property.1 _
  have hum : Monotone u := fun s t hst=>
    M.alpha.val.property.2 (mul_le_mul_of_nonneg_left hst M.hxs.le)
  have hS : Monotone (fun t=>orderedPathS (n+1) M.bf M.hf (u t)) :=
    fun s t hst=>M.mass_mean_monotone (hu s) (hu t) (hum hst)
  have hK : Monotone (fun t=>actualMixedClock (n+1) M.bf M.hf (u t)) := by
    intro s t hst
    exact add_le_add (M.inherited_hf_monotone (hu s) (hu t) (hum hst))
      (mul_le_mul (M.inherited_bf_monotone (hu s) (hu t) (hum hst)) (hS hst)
        (M.mass_mean_nonneg (hu s)) (NNReal.coe_nonneg _))
  have hKi : IntegrableOn (fun t=>actualMixedClock (n+1) M.bf M.hf (u t)/T) (Icc a b) :=
    ((hK.monotoneOn _).integrableOn_isCompact (μ:=volume) isCompact_Icc).div_const T
  have hG : IntegrableOn (fun t=>scalarPlantedEnergy hT alpha
      (actualMixedClock (n+1) M.bf M.hf (u t)/T)) (Icc a b) := by
    apply Integrable.of_bound
      ((scalarPlantedEnergy_continuous hT alpha).comp_aestronglyMeasurable
        hKi.aestronglyMeasurable) 1
    filter_upwards [] with t
    rw [Real.norm_eq_abs,abs_of_nonneg (scalarPlantedEnergy_bounds hT alpha _).1]
    exact (scalarPlantedEnergy_bounds hT alpha _).2
  exact (((hS.monotoneOn _).integrableOn_isCompact (μ:=volume) isCompact_Icc).sub hG).div_const _

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
