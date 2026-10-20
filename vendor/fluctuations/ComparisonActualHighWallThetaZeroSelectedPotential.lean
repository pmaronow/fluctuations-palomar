module

public import ComparisonActualHighWallThetaZeroDensityBasics
public import ComparisonActualHighWallPotential

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  (Q:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

def controlFactor:ℝ→ℝ:=
  inverseControlFactor Q.data.rmin (fun r=>
    inverseControlWeight Q.alpha.val.val Q.data.k Q.data.M r*
      comparisonCapSlope Q.data.N delta (comparisonSmallMass Q.data.N Q.data.E)
        (comparisonConstraintLength Q.data.N Q.data.E Q.data.d) Q.data.E Q.data.d
        (Q.alpha.val.val r))

structure Potential where
  H:ℝ→ℝ
  hH:AbsolutelyContinuousOnInterval H Q.data.rmin 1
  hD:∀ᵐr,r∈Icc Q.data.rmin 1→HasDerivAt H
    (Q.controlFactor r*radiusComparisonGradient
      (laplaceComparisonStrength Q.data.d Q.lam) Q.alpha.val.val
      (orderedPathS n Q.sweepBf Q.sweepHf)
      (orderedPathB n Q.sweepBf Q.sweepHf) r) r
  hbang:∀ᵐr,r∈Icc Q.data.rmin 1→H r<0→
    deriv Q.alpha.val.val r=Q.data.M (Q.alpha.val.val r)
  hfloor:∀ᵐr,r∈Icc Q.data.rmin 1→0<H r→
    deriv Q.alpha.val.val r=Q.data.k r
  hzero:∀ᵐr,r∈Icc Q.data.rmin 1→H r=0→
    radiusComparisonGradient (laplaceComparisonStrength Q.data.d Q.lam)
      Q.alpha.val.val (orderedPathS n Q.sweepBf Q.sweepHf)
      (orderedPathB n Q.sweepBf Q.sweepHf) r=0 ∧
    orderedPathS n Q.sweepBf Q.sweepHf (Q.alpha.val.val r)≤r ∧
    (orderedPathS n Q.sweepBf Q.sweepHf (Q.alpha.val.val r)-r)^2≤
      orderedPathB n Q.sweepBf Q.sweepHf (Q.alpha.val.val r)-
        (orderedPathS n Q.sweepBf Q.sweepHf (Q.alpha.val.val r))^2

theorem inverse_minimum (beta:Q.data.Profile):
    inverseCompensatedPressure Q.data.hr Q.data.hs1 Q.data.hc Q.data.hk
      Q.data.hkc Q.data.hm Q.data.hM
      (laplaceComparisonStrength Q.data.d Q.lam)
      (laplaceComparisonStrength_contDiff Q.data.d Q.lam).continuous n
      Q.data.thetaZeroHighOnlyData.b Q.data.thetaZeroHighOnlyData.h 0 Q.alpha ≤
    inverseCompensatedPressure Q.data.hr Q.data.hs1 Q.data.hc Q.data.hk
      Q.data.hkc Q.data.hm Q.data.hM
      (laplaceComparisonStrength Q.data.d Q.lam)
      (laplaceComparisonStrength_contDiff Q.data.d Q.lam).continuous n
      Q.data.thetaZeroHighOnlyData.b Q.data.thetaZeroHighOnlyData.h 0 beta:=by
  have H:=Q.minimum beta
  rw [Q.data.theta_zero_objective_eq_omitted Q.lam Q.hlam Q.hld Q.alpha,
    Q.data.theta_zero_objective_eq_omitted Q.lam Q.hlam Q.hld beta,
    omittedComparisonSweepObjective_eq_inverse Q.data.hr
      ⟨Q.data.hs.1.le,Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
      Q.data.hm Q.data.hM n Q.data.thetaZeroHighOnlyData.b
      Q.data.thetaZeroHighOnlyData.h Q.data.d Q.lam Q.alpha,
    omittedComparisonSweepObjective_eq_inverse Q.data.hr
      ⟨Q.data.hs.1.le,Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
      Q.data.hm Q.data.hM n Q.data.thetaZeroHighOnlyData.b
      Q.data.thetaZeroHighOnlyData.h Q.data.d Q.lam beta] at H
  exact H

theorem exists_potential : Nonempty Q.Potential := by
  let a:=Q.data
  let g:=laplaceComparisonStrength a.d Q.lam
  have hr0:0≤a.rmin ∧ a.rmin≤(1/4:ℝ):=
    ⟨a.hrbounds.1.le,a.hrbounds.2.1.trans (by linarith [a.hd1])⟩
  have hs0:0≤a.s ∧ a.s≤(1/4:ℝ):=⟨a.hs.1.le,a.hs.2⟩
  have had (beta:a.Profile):
      MonotoneOn (fun u=>a.thetaZeroHighOnlyData.b u-
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          g (laplaceComparisonStrength_contDiff a.d Q.lam).continuous beta) u) (Icc (0:ℝ) 1) ∧
      MonotoneOn (fun u=>a.thetaZeroHighOnlyData.h u+
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          (fun r=>g r*r) ((laplaceComparisonStrength_contDiff a.d Q.lam).continuous.mul continuous_id) beta) u)
        (Icc (0:ℝ) 1) ∧
      0≤a.thetaZeroHighOnlyData.b 0-
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          g (laplaceComparisonStrength_contDiff a.d Q.lam).continuous beta) 0 ∧
      0≤a.thetaZeroHighOnlyData.h 0+
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          (fun r=>g r*r) ((laplaceComparisonStrength_contDiff a.d Q.lam).continuous.mul continuous_id) beta) 0:=by
    have H:=(a.thetaZeroShiftedParentData Q.lam Q.hlam Q.hld).clockAdmissible beta
    rw [←a.theta_zero_coefficient_eq_original beta Q.lam,
      a.theta_zero_field_coefficient_eq_original beta Q.lam]
    exact ⟨H.1,H.2.1,H.2.2.1 0 ⟨le_rfl,zero_le_one⟩,
      H.2.2.2 0 ⟨le_rfl,zero_le_one⟩⟩
  obtain ⟨H,hH,hD,hbang,hzero⟩:=comparison_minimum_contact_potential
    (r₀:=a.rmin) (u₀:=a.s) (N:=a.N) (δ:=delta)
    (U:=comparisonSmallMass a.N a.E)
    (L:=comparisonConstraintLength a.N a.E a.d) (E:=a.E) (d:=a.d)
    a.hN a.hU a.hL (min_le_left _ _) a.hE a.hd.le a.hq hr0 hs0 n a.hn
    g Q.alpha (laplaceComparisonStrength_contDiff a.d Q.lam)
    (fun r _=>laplaceComparisonStrength_pos a.d Q.hlam r)
    (fun r _=>⟨(laplaceComparisonStrength_logSlope_mem a.hd.ne' Q.hlam.ne' r).1,
      (laplaceComparisonStrength_logSlope_mem a.hd.ne' Q.hlam.ne' r).2.le⟩)
    a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h
    (fun beta=>(had beta).1) (fun beta=>(had beta).2.1)
    (fun beta=>(had beta).2.2.1) (fun beta=>(had beta).2.2.2)
    Q.inverse_minimum
  obtain ⟨HB,HF⟩:=a.theta_zero_inverse_clock_eq Q.alpha Q.lam
  dsimp only [g] at hD hzero
  dsimp only [ActualHighWallData.Profile,ActualHighWallData.k,ActualHighWallData.M,
    concreteWallFloor,concreteWallCap,ActualHighWallData.N] at hD hzero HB HF
  rw [HB,HF] at hD hzero
  refine ⟨⟨H,hH,?_,?_,?_,?_⟩⟩
  · exact hD
  · filter_upwards [hbang] with r hr hri hneg
    exact (hr hri).1 hneg
  · filter_upwards [hbang] with r hr hri hpos
    exact (hr hri).2 hpos
  · exact hzero

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
