module

public import ComparisonActualHighWallThetaZeroSelectedRadius
public import ComparisonActualHighOnlyConditionalErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  (Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

def radiusErrorDensity (r:ℝ):ℝ:=
  laplaceComparisonStrength Q.data.d Q.lam r*
    (Q.radiusThermal r+(Q.radiusS r-r)^2)

theorem coefficient_measurable:Measurable Q.sweepCoefficient:=by
  have hg:Measurable (fun u=>laplaceComparisonStrength Q.data.d Q.lam (Q.sweepRadius u)):=
    (laplaceComparisonStrength_contDiff Q.data.d Q.lam).continuous.measurable.comp
      (omittedSweepQuantile_continuous Q.data.hr
        ⟨Q.data.hs.1.le,Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
        Q.data.hm Q.data.hM Q.alpha).measurable
  convert hg.indicator (s:={u:ℝ|Q.data.s≤u})
    (measurableSet_le measurable_const measurable_id) using 1
  funext u
  simp only [sweepCoefficient,
    omittedStrengthCoefficient,Set.indicator_apply,mem_ofPred_eq]

theorem error_intervalIntegrable:
    IntervalIntegrable (Q.data.thetaZeroErrorDensity Q.lam Q.alpha) volume 0 1 := by
  have hR:=omittedSweepQuantile_monotone Q.data.hr
    ⟨Q.data.hs.1.le,Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
    Q.data.hm Q.data.hM Q.alpha
  have hquad:=actual_quadratic_integrable (n+1) Q.data.hn Q.sweepBf Q.sweepHf
    Q.sweep_bf_monotone Q.sweep_hf_monotone Q.sweepRadius (hR.monotoneOn _)
    (fun u _=>(Q.data.theta_zero_radius_bounds Q.alpha u).1)
  exact intervalIntegrable_bounded_measurable_mul Q.coefficient_measurable Q.hlam.le
    (fun u _=>Q.data.theta_zero_coefficient_bounds Q.hlam Q.alpha u)
    (hquad.1.add hquad.2)

theorem error_mask_intervalIntegrable (F:Set ℝ) (hF:MeasurableSet F):
    IntervalIntegrable (fun u=>F.indicator (fun _=>(1:ℝ)) (Q.sweepRadius u)*
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) volume 0 1 := by
  have hmask:Measurable (fun u=>F.indicator (fun _=>(1:ℝ)) (Q.sweepRadius u)):=
    (measurable_const.indicator hF).comp
      (omittedSweepQuantile_continuous Q.data.hr
        ⟨Q.data.hs.1.le,Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
        Q.data.hm Q.data.hM Q.alpha).measurable
  exact intervalIntegrable_bounded_measurable_mul hmask zero_le_one
    (fun u _=>by by_cases h:Q.sweepRadius u∈F <;> simp [h]) Q.error_intervalIntegrable

theorem error_density_radius {r:ℝ} (hr:r∈Icc Q.data.rmin 1):
    Q.data.thetaZeroErrorDensity Q.lam Q.alpha (Q.alpha.val.val r)=
      Q.radiusErrorDensity r := by
  have hmass:=inverseConstraint_mass_mem Q.data.hr Q.data.hc
    Q.data.hk Q.data.hkc Q.alpha hr
  have hinv:=Q.shiftedNativeModel.R_inverse hr
  change Q.sweepRadius (Q.alpha.val.val r)=r at hinv
  simp only [ActualHighWallData.thetaZeroErrorDensity,
    ActualHighWallData.thetaZeroCoefficient,omittedStrengthCoefficient,
    ite_eq_left hmass.1,hinv,radiusErrorDensity,radiusThermal,radiusS,radiusB]

theorem error_mask_radius_integral (F:Set ℝ) (hF:MeasurableSet F):
    (∫u in (0:ℝ)..1,F.indicator (fun _=>(1:ℝ)) (Q.sweepRadius u)*
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u)=
      ∫r in Icc Q.data.rmin 1,deriv Q.alpha.val.val r*
        F.indicator (fun _=>(1:ℝ)) r*Q.radiusErrorDensity r := by
  let f:=fun u=>F.indicator (fun _=>(1:ℝ)) (Q.sweepRadius u)*
    Q.data.thetaZeroErrorDensity Q.lam Q.alpha u
  have hi:=Q.error_mask_intervalIntegrable F hF
  have hilo:=hi.mono_set (by
    rw [uIcc_of_le Q.data.hs.1.le,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl Q.data.hs1)
  have hihi:=hi.mono_set (by
    rw [uIcc_of_le Q.data.hs1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc Q.data.hs.1.le le_rfl)
  have hlow:(∫u in (0:ℝ)..Q.data.s,f u)=0:=by
    apply Eq.trans ?_ (intervalIntegral.integral_zero:
      (∫u in (0:ℝ)..Q.data.s,(0:ℝ))=0)
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne Q.data.s] with u hus hu
    have huu:u∈Ioc (0:ℝ) Q.data.s:=by
      simpa only [uIoc_of_le Q.data.hs.1.le] using hu
    dsimp only [f]
    rw [Q.data.theta_zero_error_density_low Q.lam Q.alpha
      (lt_of_le_of_ne huu.2 hus),mul_zero]
  have H:=Q.shiftedNativeModel.mass_radius_cell_substitution f
    (show Q.data.s∈Icc Q.data.s 1 from ⟨le_rfl,Q.data.hs1⟩)
    (show (1:ℝ)∈Icc Q.data.s 1 from ⟨Q.data.hs1,le_rfl⟩) Q.data.hs1
  rw [Q.shiftedNativeModel.R_left,Q.shiftedNativeModel.R_one] at H
  change (∫u in (0:ℝ)..1,f u)=_
  rw [←intervalIntegral.integral_add_adjacent_intervals hilo hihi,hlow,zero_add,H]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  have hinv:=Q.shiftedNativeModel.R_inverse hr
  change Q.sweepRadius (Q.alpha.val.val r)=r at hinv
  dsimp only [f]
  rw [hinv,Q.error_density_radius hr]
  ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
