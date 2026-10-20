module

public import ComparisonPositiveScalarCalibration
public import ComparisonPhysicalGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 3000000

section
variable {origin u0 c : ℝ} {k M : ℝ→ℝ}
    (hr : origin≤1) (hc : 0<c) (hk : ContinuousOn k (Icc origin 1))
    (hkc : ∀r∈Icc origin 1,c≤k r) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparison_calibration_mass_origin_le_one
    (alpha : inverseIntegralConstraints origin u0 k M) : u0≤1 := by
  have hh := (alpha.val.property.1 origin).2
  simpa only [alpha.property.1] using hh

def comparisonCalibrationConstrainedRadius
    (alpha : inverseIntegralConstraints origin u0 k M) (u : ℝ) : ℝ :=
  IccExtend (comparison_calibration_mass_origin_le_one alpha)
    (constrainedQuantileMap hr hc hk hkc hm hM alpha) u

theorem comparison_calibration_constrained_radius_continuous
    (alpha : inverseIntegralConstraints origin u0 k M) :
    Continuous (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha) :=
  (constrainedQuantileMap hr hc hk hkc hm hM alpha).continuous.Icc_extend'
    (h:=comparison_calibration_mass_origin_le_one alpha)

theorem comparison_calibration_constrained_radius_inverse
    (alpha : inverseIntegralConstraints origin u0 k M) {r : ℝ} (hri : r∈Icc origin 1) :
    comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha (alpha.val.val r)=r := by
  have hu : alpha.val.val r∈Icc u0 1 := (inverseConstraintMap alpha ⟨r,hri⟩).property
  rw [comparisonCalibrationConstrainedRadius,IccExtend_of_mem _ _ hu]
  exact congrArg Subtype.val ((inverseConstraintOrderIso hr hc hk hkc hm hM alpha).symm_apply_apply ⟨r,hri⟩)

include hr hc hk hkc hm hM in
theorem comparison_calibration_shifted_mass_substitution
    (alpha : inverseIntegralConstraints origin u0 k M) (F : ℝ→ℝ) :
    (∫u in u0..1,F u)=∫r in Icc origin 1,deriv alpha.val.val r*F (alpha.val.val r) := by
  have hu0 : u0≤1 := by
    have hh := (alpha.val.property.1 origin).2
    simpa only [alpha.property.1] using hh
  have himage := inverseConstraint_image hr hm hM alpha
  rw [intervalIntegral.integral_of_le hu0,←integral_Icc_eq_integral_Ioc,
    ←himage,lipschitz_interval_integral_image hr
      (inverseIntegralConstraints_lipschitz hm hM alpha.property)
      (inverseConstraint_strictMonoOn hc hk hkc alpha.property).injOn]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards [] with r _
  rw [abs_of_nonneg alpha.val.property.2.deriv_nonneg]

theorem comparison_calibration_floor_mass_exact
    (alpha : inverseIntegralConstraints origin u0 k M) (H : ℝ→ℝ) :
    (∫u in u0..1,(comparisonCalibrationFloor H
      (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha)).indicator (fun _=>(1:ℝ)) u)=
      ∫r in Icc origin 1,({r | 0<H r}).indicator (deriv alpha.val.val) r := by
  rw [comparison_calibration_shifted_mass_substitution hr hc hk hkc hm hM alpha]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hri
  have he : alpha.val.val r∈comparisonCalibrationFloor H
      (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha) ↔ 0<H r := by
    change 0<H (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha (alpha.val.val r)) ↔ 0<H r
    rw [comparison_calibration_constrained_radius_inverse hr hc hk hkc hm hM alpha hri]
  by_cases hh : 0<H r
  · simp only [Set.indicator_of_mem (he.mpr hh),Set.indicator_of_mem
      (show r∈{r | 0<H r} from hh),mul_one]
  · simp only [Set.indicator_of_notMem (show alpha.val.val r∉comparisonCalibrationFloor H
        (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha) from fun h=>hh (he.mp h)),
      Set.indicator_of_notMem (show r∉{r | 0<H r} from hh),mul_zero]

theorem comparison_calibration_native_floor_mass_le
    (alpha : inverseIntegralConstraints origin u0 k M) (H : ℝ→ℝ)
    (hH : Measurable H)
    (hfloor : ∀ᵐ r,r∈Icc origin 1→0<H r→deriv alpha.val.val r=k r) :
    (∫u in u0..1,(comparisonCalibrationFloor H
      (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha)).indicator (fun _=>(1:ℝ)) u)≤
      ∫r in origin..1,k r := by
  rw [comparison_calibration_floor_mass_exact hr hc hk hkc hm hM alpha,
    intervalIntegral.integral_of_le hr,←integral_Icc_eq_integral_Ioc]
  have hLip := inverseIntegralConstraints_lipschitz hm hM alpha.property
  have hLipU : LipschitzOnWith ⟨M 1,hM⟩ alpha.val.val (uIcc origin 1) := by
    simpa only [uIcc_of_le hr] using hLip
  have hi : IntegrableOn (deriv alpha.val.val) (Icc origin 1) := by
    have hh := hLipU.absolutelyContinuousOnInterval.intervalIntegrable_deriv
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hr (by simp)).mp hh
  have hs : MeasurableSet {r | 0<H r} := measurableSet_lt measurable_const hH
  apply integral_mono_ae (hi.indicator hs) hk.integrableOn_Icc
  filter_upwards [ae_restrict_of_ae hfloor,ae_restrict_mem measurableSet_Icc] with r hfl hri
  change ({s | 0<H s}).indicator (deriv alpha.val.val) r≤k r
  by_cases hh : 0<H r
  · rw [Set.indicator_of_mem (show r∈{s | 0<H s} from hh)]
    exact (hfl hri hh).le
  · rw [Set.indicator_of_notMem (show r∉{s | 0<H s} from hh)]
    exact hc.le.trans (hkc r hri)

theorem comparison_calibration_native_floor_integrable
    (alpha : inverseIntegralConstraints origin u0 k M) (H : ℝ→ℝ) (hH : Measurable H) :
    IntervalIntegrable ((comparisonCalibrationFloor H
      (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha)).indicator (fun _=>(1:ℝ)))
      volume u0 1 := by
  have hs : MeasurableSet (comparisonCalibrationFloor H
      (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha)) :=
    measurableSet_lt measurable_const (hH.comp
      (comparison_calibration_constrained_radius_continuous hr hc hk hkc hm hM alpha).measurable)
  have hi : IntervalIntegrable (fun _ : ℝ=>(1:ℝ)) volume u0 1 := intervalIntegrable_const
  exact ⟨hi.1.indicator hs,hi.2.indicator hs⟩

theorem comparison_calibration_native_floor_on_band
    {N delta U a z : ℝ} (hN : 0<N) (hU : 0<U) (horigin : 0≤origin)
    (alpha : inverseIntegralConstraints origin u0 k M) (H : ℝ→ℝ) (hH : Measurable H)
    (hfloor : ∀ᵐ r,r∈Icc origin 1→0<H r→deriv alpha.val.val r=comparisonFloor N delta U r)
    (ha : u0≤a) (haz : a≤z) (hz : z≤1) :
    let f := (comparisonCalibrationFloor H
      (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha)).indicator (fun _=>(1:ℝ))
    IntervalIntegrable f volume a z ∧ (∫u in a..z,f u)≤N^(-delta)*U := by
  let f := (comparisonCalibrationFloor H
    (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha)).indicator (fun _=>(1:ℝ))
  have hi := comparison_calibration_native_floor_integrable hr hc hk hkc hm hM alpha H hH
  have hglobal : (∫u in u0..1,f u)≤N^(-delta)*U := by
    rw [comparison_calibration_floor_mass_exact hr hc hk hkc hm hM alpha]
    exact comparisonFloor_region_mass hN hU ⟨horigin,hr⟩ {r | 0<H r}
      (measurableSet_lt measurable_const hH) alpha.val.val hfloor
  have hsub : uIcc a z⊆uIcc u0 1 := by
    rw [uIcc_of_le haz,uIcc_of_le (comparison_calibration_mass_origin_le_one alpha)]
    exact Icc_subset_Icc ha hz
  refine ⟨hi.mono hsub le_rfl,?_⟩
  exact (intervalIntegral.integral_mono_interval ha haz hz
    (Eventually.of_forall fun _=>Set.indicator_nonneg (fun _ _=>by norm_num) _) hi).trans hglobal

end
end OAI.SKFluctuations.LaplaceWindowFormalization
