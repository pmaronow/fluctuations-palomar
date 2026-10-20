module

public import ComparisonNativeInnerPhysicalBand
public import ComparisonNativeFloorRestoration
public import ComparisonNativeCapMismatch
public import ComparisonNativeBroadFamilyAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

namespace NativeBandModel

theorem ordinary_cap_length_le_D0 (m : NativeBandModel) {r : ℝ} (hr : r ∈ m.ordinaryCaps) :
    sSup (ordConnectedComponent m.capSet r)-sInf (ordConnectedComponent m.capSet r)≤ m.D0 := by
  obtain ⟨ha,har,hrz,hz,heq,_,_⟩ := wholeCap_component_endpoints m.hopen
    (m.hcapSet.trans Ioo_subset_Icc_self) hr.1
  have hbang : ∀ᵐ t,t ∈ Icc (0:ℝ) 1 → m.H t<0 → deriv m.alpha.val.val t=
      comparisonCap m.N m.delta m.U m.Lcap m.E m.d (m.alpha.val.val t) := by
    simpa only [←m.hMdef] using m.hbang
  have htravel := potential_comparison_cap_interval_travel (zero_lt_one.trans_le m.hN)
    m.hU m.hLcap m.hE m.hd (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    (inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property)
    (fun t _=>m.alpha.val.property.1 t) hbang ha hz (har.trans hrz).le
    (fun t ht=>m.hnegative t (ordConnectedComponent_subset (heq.symm ▸ ht)))
  have hW : 0≤(m.Lcap/m.N^m.delta)*Real.log ((1+m.U)/m.U) := by
    have hp := m.D0_pos
    have hlogU : 0<Real.log ((1+m.U)/m.U) := Real.log_pos ((lt_div_iff₀ m.hU).mpr (by linarith))
    have hN : 0 < m.N := zero_lt_one.trans_le m.hN
    exact mul_nonneg (div_nonneg m.hLcap.le (Real.rpow_pos_of_pos hN _).le) hlogU.le
  have hh := mul_le_mul_of_nonneg_right (show (1:ℝ)≤9*Real.log m.N by linarith [m.hlog]) hW
  dsimp [D0]
  nlinarith [htravel.2.1]

theorem ordinary_mismatch_ae_radius (m : NativeBandModel) :
    ∀ᵐ r,r ∈ Icc (0:ℝ) 1 → r ∈ m.ordinarySupport → 
      (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r)^2≤
        16*m.D0^2+2*m.thermal (m.alpha.val.val r) := by
  have hmom := comparisonVariableEndpoint_radius_moments m.hc m.hk m.hkc m.hm m.hM
    (m.n+1) (by omega) m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  filter_upwards [m.hzero,volume.ae_ne (0:ℝ)] with r hz hr0 hr hs
  rcases hs.2 with hc|hcontact
  · obtain ⟨ha,har,hrz,hz,heq,_,_⟩ := wholeCap_component_endpoints m.hopen
      (m.hcapSet.trans Ioo_subset_Icc_self) hc.1
    have hboundary : (m.H (sInf (ordConnectedComponent m.capSet r))=0 ∧
        m.H (sSup (ordConnectedComponent m.capSet r))=0) ∨
        (sInf (ordConnectedComponent m.capSet r)=0 ∧ m.H (sSup (ordConnectedComponent m.capSet r))=0) ∨
        (m.H (sInf (ordConnectedComponent m.capSet r))=0 ∧ sSup (ordConnectedComponent m.capSet r)=1) := by
      rcases (m.hcomponent r hc.1).2 with h|h
      · exact Or.inl ⟨(m.hcomponent r hc.1).1,h⟩
      · exact Or.inr (Or.inr ⟨(m.hcomponent r hc.1).1,h⟩)
    have hm := native_actual_cap_mismatch_endpoint_cases m ha hz ⟨har,hrz⟩ hboundary (m.hnegative r hc.1)
    have hlen := m.ordinary_cap_length_le_D0 hc
    have hsquare := pow_le_pow_left₀ (sub_nonneg.mpr (har.trans hrz).le) hlen 2
    nlinarith
  · have hrp : 0<r := lt_of_le_of_ne hr.1 hr0.symm
    have hb := hmom.2.2 r hr
    have hp := laplaceComparisonStrength_logSlope_mem m.hd.ne' m.hlam.ne' r
    have hm := (comparison_gradient_contact_mismatch hrp (laplaceComparisonStrength_pos m.d m.hlam r)
      ⟨hp.1,hp.2.le⟩ hb.1.1 hb.2.1 (hz hr hcontact)).2
    change (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r)^2≤
      orderedPathB (m.n+1) m.bf m.hf (m.alpha.val.val r)-
        (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r))^2 at hm
    dsimp [thermal]
    nlinarith [sq_nonneg m.D0,sq_nonneg (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r)]

theorem ordinary_mismatch_ae_mass (m : NativeBandModel) :
    ∀ᵐ u,u ∈ Icc (0:ℝ) 1 → m.R u ∈ m.ordinarySupport → 
      (orderedPathS (m.n+1) m.bf m.hf u-m.R u)^2≤16*m.D0^2+2*m.thermal u := by
  have hh := ae_inverse_pullback (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    (fun u (_ : u ∈ Icc (0:ℝ) 1)=>comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u)
    (fun u hu=>comparisonSweepQuantile_mass_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hu)
    m.ordinary_mismatch_ae_radius
  filter_upwards [hh] with u hu hui hs
  have h := hu hui hs
  simpa only [comparisonSweepQuantile_mass_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hui] using h

theorem ordinary_mask_mass_le (m : NativeBandModel)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag≤ m.bandMass) :
    (∫u in 0..1,m.ordinaryMask (m.R u))≤ m.bandMass := by
  have hR := (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable
  have hb : IntervalIntegrable (fun u=>(Ioo m.ag m.zg).indicator (fun _=>(1:ℝ)) (m.R u)) volume 0 1 := by
    simpa only [mul_one,Function.comp_apply,NativeBandModel.R] using intervalIntegrable_bounded_measurable_mul
      ((measurable_const.indicator measurableSet_Ioo).comp hR) (show (0:ℝ)≤1 by norm_num)
      (fun u _=>by by_cases h:m.R u ∈ Ioo m.ag m.zg <;> simp [h]) (intervalIntegrable_const (c:=(1:ℝ)))
  have hle : (∫u in 0..1,m.ordinaryMask (m.R u))≤
      ∫u in 0..1,(Ioo m.ag m.zg).indicator (fun _=>(1:ℝ)) (m.R u) := by
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one]
    apply integral_mono_of_nonneg _ ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hb) _
    · exact ae_of_all _ (fun u=>indicator_nonneg (fun _ _=>zero_le_one) _)
    · exact ae_of_all _ (fun u=>by
        change m.ordinarySupport.indicator (fun _=>(1:ℝ)) (m.R u)≤(Ioo m.ag m.zg).indicator (fun _=>1) (m.R u)
        by_cases hs:m.R u ∈ m.ordinarySupport
        · rw [indicator_of_mem hs,indicator_of_mem hs.1]
        · rw [indicator_of_notMem hs];exact indicator_nonneg (fun _ _=>zero_le_one) _)
  have hsub : Ioo m.ag m.zg⊆Icc (0:ℝ) 1 := Ioo_subset_Icc_self.trans (Icc_subset_Icc m.hag.le m.hzg)
  rw [nativeActual_radius_mask_mass m _ measurableSet_Ioo hsub] at hle
  have hac : AbsolutelyContinuousOnInterval m.alpha.val.val m.ag m.zg := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le m.hagz] using
      (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property).mono (Icc_subset_Icc m.hag.le m.hzg)
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le m.hagz,hac.integral_deriv_eq_sub] at hle
  exact hle.trans hband

end NativeBandModel

theorem actual_native_ordinary_error_le_thermal
    (m : NativeBandModel) (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag≤ m.bandMass) :
    (∫u in 0..1,m.ordinaryMask (m.R u)*m.comparisonErrorDensity u)≤
      3*(∫u in 0..1,m.ordinaryMask (m.R u)*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u)+
      16*m.lam*m.D0^2*m.bandMass := by
  have hR := (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable
  have he := ((laplaceComparisonStrength_contDiff m.d m.lam).continuous.measurable).comp hR
  have hm := m.ordinaryMask_composed_measurable
  have hmb u : m.ordinaryMask (m.R u) ∈ Icc (0:ℝ) 1 := by
    unfold NativeBandModel.ordinaryMask
    by_cases h:m.R u ∈ m.ordinarySupport <;> simp [h]
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hT := physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
  have hiW : IntervalIntegrable (fun u=>m.ordinaryMask (m.R u)*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u) volume 0 1 := intervalIntegrable_bounded_measurable_mul (hm.mul he) m.hlam.le
    (fun u _=>⟨mul_nonneg (hmb u).1 (laplaceComparisonStrength_pos m.d m.hlam _).le,
      (mul_le_mul_of_nonneg_right (hmb u).2 (laplaceComparisonStrength_pos m.d m.hlam _).le).trans
        (by simpa only [one_mul] using laplaceComparisonStrength_le m.d m.hlam.le (m.R u))⟩) hT
  have hiM : IntervalIntegrable (fun u=>m.ordinaryMask (m.R u)) volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hm
      (show (0:ℝ)≤1 by norm_num) (fun u _=>hmb u) (intervalIntegrable_const (c:=(1:ℝ)))
  have hiUpper : IntervalIntegrable (fun u=>3*(m.ordinaryMask (m.R u)*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u)+(16*m.lam*m.D0^2)*m.ordinaryMask (m.R u)) volume 0 1 := (hiW.const_mul 3).add (hiM.const_mul (16*m.lam*m.D0^2))
  have hle : (∫u in 0..1,m.ordinaryMask (m.R u)*m.comparisonErrorDensity u)≤
      ∫u in 0..1,3*(m.ordinaryMask (m.R u)*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u)+
        (16*m.lam*m.D0^2)*m.ordinaryMask (m.R u) := by
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one]
    apply integral_mono_of_nonneg _ ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiUpper) _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hp := orderedPath_SK_bounds (m.n+1) (by omega) m.bf m.hf
        (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu
      have ht : 0 ≤ m.thermal u := sub_nonneg.mpr hp.2.2.1
      exact mul_nonneg (hmb u).1 (mul_nonneg (laplaceComparisonStrength_pos m.d m.hlam _).le
        (add_nonneg ht (sq_nonneg _)))
    · filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae m.ordinary_mismatch_ae_mass] with u hu hmis
      by_cases hs:m.R u ∈ m.ordinarySupport
      · have hh := hmis (Ioc_subset_Icc_self hu) hs
        have hmul := mul_le_mul_of_nonneg_left hh (laplaceComparisonStrength_pos m.d m.hlam (m.R u)).le
        have hstr := mul_le_mul_of_nonneg_right (laplaceComparisonStrength_le m.d m.hlam.le (m.R u)) (sq_nonneg m.D0)
        simp only [NativeBandModel.ordinaryMask,indicator_of_mem hs,one_mul,NativeBandModel.comparisonErrorDensity]
        nlinarith
      · simp only [NativeBandModel.ordinaryMask,indicator_of_notMem hs,zero_mul,mul_zero,zero_add,le_refl]
  have hmass := mul_le_mul_of_nonneg_left (m.ordinary_mask_mass_le hband)
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤16) m.hlam.le) (sq_nonneg m.D0))
  rw [intervalIntegral.integral_add (hiW.const_mul 3) (hiM.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hle
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
