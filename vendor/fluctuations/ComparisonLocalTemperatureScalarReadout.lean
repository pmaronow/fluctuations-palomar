module

public import ComparisonLocalTemperatureScalarGlobalCompactness
public import ComparisonScalarClosureIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy GaussianCalculus Scalar
open scoped Topology
set_option maxHeartbeats 2200000

theorem comparison_local_scalar_response_eq_rescaled {T S : ℝ} (hT : 0<T)
    (alpha : boundedMassProfiles) (x t : ℝ) :
    comparisonLocalScalarResponse hT S alpha x t =
      comparisonRescaledScalarResponse (scalarCovarianceResponse hT alpha) S x t := by
  rw [comparison_local_scalar_response_covariance]
  simp only [comparisonRescaledScalarResponse,mul_assoc]

theorem comparison_local_scalar_limit_response_deriv {R σ t : ℝ}
    (F : ℝ→ℝ) (hF : IntegrableOn F (Icc (0:ℝ) R)) (ht : t∈Ioo (0:ℝ) R) :
    HasDerivAt (fun q=>∫r in 0..q,(σ+∫s in 0..r,F s))
      (σ+∫s in 0..t,F s) t := by
  have hR : 0≤R := ht.1.le.trans ht.2.le
  have hFc : ContinuousOn (fun r=>∫s in 0..r,F s) (Icc (0:ℝ) R) := by
    simpa only [uIcc_of_le hR] using intervalIntegral.continuousOn_primitive_interval
      (show IntegrableOn F (uIcc (0:ℝ) R) by simpa only [uIcc_of_le hR] using hF)
  have hpc : ContinuousOn (fun r=>σ+∫s in 0..r,F s) (Icc (0:ℝ) R) := by
    intro r hr
    exact continuousWithinAt_const.add (hFc r hr)
  have hi : IntervalIntegrable (fun r=>σ+∫s in 0..r,F s) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).mpr
      (hpc.integrableOn_Icc.mono_set (fun r hr=>⟨hr.1.le,hr.2.trans ht.2.le⟩))
  have hpm : AEStronglyMeasurable (fun r=>σ+∫s in 0..r,F s) (volume.restrict (Icc (0:ℝ) R)) :=
    hpc.aestronglyMeasurable measurableSet_Icc
  exact intervalIntegral.integral_hasDerivAt_right hi
    (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hpm
      (Icc_mem_nhds ht.1 ht.2)) (hpc.continuousAt (Icc_mem_nhds ht.1 ht.2))

theorem comparison_local_scalar_limit_response_right_deriv {R σ t : ℝ}
    (F : ℝ→ℝ) (hF : IntegrableOn F (Icc (0:ℝ) R)) (ht : t∈Ico (0:ℝ) R) :
    HasDerivWithinAt (fun q=>∫r in 0..q,(σ+∫s in 0..r,F s))
      (σ+∫s in 0..t,F s) (Ici t) t := by
  have hR : 0≤R := ht.1.trans ht.2.le
  have hFc : ContinuousOn (fun r=>∫s in 0..r,F s) (Icc (0:ℝ) R) := by
    simpa only [uIcc_of_le hR] using intervalIntegral.continuousOn_primitive_interval
      (show IntegrableOn F (uIcc (0:ℝ) R) by simpa only [uIcc_of_le hR] using hF)
  have hpc : ContinuousOn (fun r=>σ+∫s in 0..r,F s) (Icc (0:ℝ) R) := by
    intro r hr
    exact continuousWithinAt_const.add (hFc r hr)
  have hi : IntervalIntegrable (fun r=>σ+∫s in 0..r,F s) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      (hpc.integrableOn_Icc.mono_set (fun r hr=>⟨hr.1.le,hr.2.trans ht.2.le⟩))
  have hsmallc := (hpc.mono (Icc_subset_Icc ht.1 le_rfl))
  have hcont : ContinuousWithinAt (fun r=>σ+∫s in 0..r,F s) (Ici t) t := by
    simpa only [ContinuousWithinAt,nhdsWithin_Icc_eq_nhdsGE ht.2] using
      hsmallc t ⟨le_rfl,ht.2.le⟩
  have hm : StronglyMeasurableAtFilter (fun r=>σ+∫s in 0..r,F s) (𝓝[Ici t] t) volume := by
    simpa only [nhdsWithin_Icc_eq_nhdsGE ht.2] using
      hsmallc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
  exact intervalIntegral.integral_hasDerivWithinAt_right hi
    (hm.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)) (hcont.mono Ioi_subset_Ici_self)

theorem comparison_local_scalar_limit_slope_right_deriv {R σ A B t : ℝ}
    (U : ℝ→ℝ) (hUi : IntegrableOn U (Icc (0:ℝ) R)) (hUm : Measurable U)
    (ht : t∈Icc (0:ℝ) R) (hc : ContinuousWithinAt U (Ici t) t) :
    HasDerivWithinAt (fun q=>σ+∫s in 0..q,(A*s-B*U s)) (A*t-B*U t) (Ici t) t := by
  have hid : IntegrableOn (fun s : ℝ=>s) (Icc (0:ℝ) R) := continuous_id.integrableOn_Icc
  have hFi : IntegrableOn (fun s=>A*s-B*U s) (Icc (0:ℝ) R) :=
    (hid.const_mul A).sub (hUi.const_mul B)
  have hi : IntervalIntegrable (fun s=>A*s-B*U s) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      (hFi.mono_set
        (fun s hs=>⟨hs.1.le,hs.2.trans ht.2⟩))
  have hm : StronglyMeasurableAtFilter (fun s=>A*s-B*U s) (𝓝[Ici t] t) volume :=
    ((measurable_id.const_mul A).sub (hUm.const_mul B)).stronglyMeasurable.stronglyMeasurableAtFilter
  have hcont : ContinuousWithinAt (fun s=>A*s-B*U s) (Ici t) t :=
    (continuousWithinAt_id.const_mul A).sub (hc.const_mul B)
  exact (intervalIntegral.integral_hasDerivWithinAt_right hi
    (hm.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)) (hcont.mono Ioi_subset_Ici_self)).const_add σ

theorem comparison_local_scalar_native_ode_coefficients {T S : ℝ}
    (hT : 0<T) (hS : 0<S) (beta : boundedMassProfiles) :
    0<S^3*(scalarTailSpatialJet hT beta 4 0 0)^2 ∧
    0<2*S^2*(scalarTailSpatialJet hT beta 2 0 0)^3 ∧
    (S^3*(scalarTailSpatialJet hT beta 4 0 0)^2)/
      (2*S^2*(scalarTailSpatialJet hT beta 2 0 0)^3)=
        (S/T)*scalarInitialDensityConstant hT beta := by
  have h4 : scalarTailSpatialJet hT beta 4 0 0<0 :=
    scalarProfileJet_four_zero_neg (rescaledMassProfile beta hT)
      (fun s=>(beta.property.1 (s/T)).2) _ _
  have h2 : 0<scalarTailSpatialJet hT beta 2 0 0 :=
    scalarProfileJet_curvature_pos (rescaledMassProfile beta hT)
      (fun s=>(beta.property.1 (s/T)).2) _ _ _
  refine ⟨mul_pos (pow_pos hS 3) (sq_pos_of_ne_zero h4.ne),by positivity,?_⟩
  have he : (scalarTailJet hT beta 0).H 0 0=scalarTailSpatialJet hT beta 2 0 0 := rfl
  rw [scalarInitialDensityConstant,he]
  field_simp

end OAI.SKFluctuations.LaplaceWindowFormalization
