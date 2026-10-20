module

public import ComparisonActualHighOnlyConditionalDensityBasics
public import ComparisonActualHighOnlyOffFloorWeighted
public import ComparisonActualHighOnlyOuterFloorThermalMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def comparisonErrorDensity
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (u : ℝ) : ℝ :=
  a.coefficient u*((orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)+
    (orderedPathS (n+1) a.bf a.hf u-a.R u)^2)

def radiusErrorDensity
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (r : ℝ) : ℝ :=
  laplaceComparisonStrength a.data.d a.lam r*(a.radiusThermal r+(a.radiusS r-r)^2)

theorem original_sweep_density_eq_error_integral
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    a.data.originalSweepDensity a.lam a.alpha=∫u in 0..1,a.comparisonErrorDensity u := rfl

theorem comparisonErrorDensity_nonneg
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) : 0≤a.comparisonErrorDensity u :=
  mul_nonneg (a.coefficient_nonneg u)
    (add_nonneg (a.actual_thermal_nonneg_on_unit hu) (sq_nonneg _))

theorem comparisonErrorDensity_intervalIntegrable
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntervalIntegrable a.comparisonErrorDensity volume 0 1 := by
  have H:=intervalIntegrable_bounded_measurable_mul a.coefficient_measurable a.hlam.le
    (fun u _=>show a.coefficient u∈Icc (0:ℝ) a.lam from ⟨a.coefficient_nonneg u,a.coefficient_le_lam u⟩)
    (a.original_thermal_intervalIntegrable.add a.mass_squared_mismatch_intervalIntegrable)
  exact H

theorem error_mask_intervalIntegrable
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (F : Set ℝ) (hF : MeasurableSet F) :
    IntervalIntegrable (fun u=>F.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) volume 0 1 := by
  have hmask : Measurable (fun u=>F.indicator (fun _=>(1:ℝ)) (a.R u)):=
    (measurable_const.indicator hF).comp
      (omittedSweepQuantile_continuous zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
        a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha).measurable
  exact intervalIntegrable_bounded_measurable_mul hmask zero_le_one
    (fun u _=>by by_cases h:a.R u∈F <;> simp [h]) a.comparisonErrorDensity_intervalIntegrable

theorem comparisonErrorDensity_low_zero
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u<a.data.s) : a.comparisonErrorDensity u=0 := by
  unfold comparisonErrorDensity coefficient ActualHighOnlyComparisonData.coefficient omittedStrengthCoefficient
  rw [ite_eq_right (not_le.mpr hu),zero_mul]

theorem comparisonErrorDensity_radius
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    a.comparisonErrorDensity (a.alpha.val.val r)=a.radiusErrorDensity r := by
  have hmass:=inverseConstraint_mass_mem zero_le_one a.data.hc a.data.hk a.data.hkc a.alpha hr
  have hinv:=a.shiftedNativeModel.R_inverse hr
  change a.R (a.alpha.val.val r)=r at hinv
  simp only [comparisonErrorDensity,coefficient,ActualHighOnlyComparisonData.coefficient,
    omittedStrengthCoefficient,ite_eq_left hmass.1,hinv,radiusErrorDensity,radiusThermal,radiusS,radiusB]

theorem original_error_mask_radius_integral
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (F : Set ℝ) (hF : MeasurableSet F) :
    (∫u in 0..1,F.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u)=
      ∫r in Icc (0:ℝ) 1,deriv a.alpha.val.val r*F.indicator (fun _=>(1:ℝ)) r*a.radiusErrorDensity r := by
  let f:=fun u=>F.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u
  have hi:=a.error_mask_intervalIntegrable F hF
  have hilo:=hi.mono_set (by
    rw [uIcc_of_le a.data.hs.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl a.data.hs1)
  have hihi:=hi.mono_set (by
    rw [uIcc_of_le a.data.hs1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc a.data.hs.1 le_rfl)
  have hlow:(∫u in 0..a.data.s,f u)=0:=by
    apply Eq.trans ?_ (intervalIntegral.integral_zero : (∫u in (0:ℝ)..a.data.s,(0:ℝ))=0)
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne a.data.s] with u hus hu
    have huu:u∈Ioc (0:ℝ) a.data.s:=by simpa only [uIoc_of_le a.data.hs.1] using hu
    have hlt:u<a.data.s:=lt_of_le_of_ne huu.2 hus
    dsimp only [f]
    rw [a.comparisonErrorDensity_low_zero hlt,mul_zero]
  have H:=a.shiftedNativeModel.mass_radius_cell_substitution f
    (show a.data.s∈Icc a.data.s 1 from ⟨le_rfl,a.data.hs1⟩)
    (show (1:ℝ)∈Icc a.data.s 1 from ⟨a.data.hs1,le_rfl⟩) a.data.hs1
  rw [a.shiftedNativeModel.R_left,a.shiftedNativeModel.R_one] at H
  change (∫u in 0..1,f u)=_
  rw [←intervalIntegral.integral_add_adjacent_intervals hilo hihi,hlow,zero_add,H]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  have hinv:=a.shiftedNativeModel.R_inverse hr
  change a.R (a.alpha.val.val r)=r at hinv
  dsimp only [f]
  rw [hinv,a.comparisonErrorDensity_radius hr]
  ring

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
