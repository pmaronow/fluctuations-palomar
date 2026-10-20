module

public import ComparisonPhysicalGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal
section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

include hc hk hkc hm hM in
theorem comparisonSweep_mass_substitution (α : inverseIntegralConstraints 0 0 k M)
    (F : ℝ → ℝ) :
    (∫u in (0:ℝ)..1,F u)=∫r in Icc (0:ℝ) 1,deriv α.val.val r*F (α.val.val r) := by
  have himage := inverseConstraint_image zero_le_one hm hM α
  rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc,
    ←himage,lipschitz_interval_integral_image zero_le_one
      (inverseIntegralConstraints_lipschitz hm hM α.property)
      (inverseConstraint_strictMonoOn hc hk hkc α.property).injOn,himage]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards [] with r _
  rw [abs_of_nonneg (comparisonSweep_density_nonneg α r)]

theorem comparisonSweep_weighted_mismatch_substitution
    (α : inverseIntegralConstraints 0 0 k M) (S w : ℝ → ℝ) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    (∫u in (0:ℝ)..1,w (R u)*(S u-R u)^2)=
      ∫r in Icc (0:ℝ) 1,deriv α.val.val r*w r*(S (α.val.val r)-r)^2 := by
  dsimp only
  rw [comparisonSweep_mass_substitution hc hk hkc hm hM α]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  dsimp only
  rw [comparisonSweepQuantile_inverse hc hk hkc hm hM α hr]
  ring

theorem comparisonSweep_weighted_thermal_substitution
    (α : inverseIntegralConstraints 0 0 k M) (S B w : ℝ → ℝ) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    (∫u in (0:ℝ)..1,w (R u)*(B u-(S u)^2))=
      ∫r in Icc (0:ℝ) 1,deriv α.val.val r*w r*(B (α.val.val r)-(S (α.val.val r))^2) := by
  dsimp only
  rw [comparisonSweep_mass_substitution hc hk hkc hm hM α]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  dsimp only
  rw [comparisonSweepQuantile_inverse hc hk hkc hm hM α hr]
  ring

end
end OAI.SKFluctuations.LaplaceWindowFormalization
