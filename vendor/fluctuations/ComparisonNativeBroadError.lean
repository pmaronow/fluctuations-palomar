module

public import ComparisonNativeBroadDyadicCount
public import ComparisonNativeLocalOrdinaryError
public import ComparisonNativeWholeCapThermalCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

theorem nativeBroadSlice_mask_mass_eq (m:NativeBandModel) (g:NativeBroadSliceGeometry m) :
    (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u))=
      ∫r in Ioo g.a g.b,deriv m.alpha.val.val r :=
  nativeActual_radius_mask_mass m _ measurableSet_Ioo
    (Ioo_subset_Icc_self.trans (Icc_subset_Icc (m.hag.le.trans g.haGroup) (g.hbGroup.trans m.hzg)))

theorem actual_native_broad_slice_error_le_thermal (m:NativeBandModel) (g:NativeBroadSliceGeometry m) :
    (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)≤
      3*m.groupStrength*(∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.thermal u)+
      16*m.groupStrength*(g.capZ-g.capA)^2*(∫r in Ioo g.a g.b,deriv m.alpha.val.val r) := by
  let mask := fun u=>(Ioo g.a g.b).indicator (fun _=>(1:ℝ)) (m.R u)
  have hm : Measurable mask := (measurable_const.indicator measurableSet_Ioo).comp
    (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable
  have hmb u : mask u∈Icc (0:ℝ) 1 := by by_cases h:m.R u∈Ioo g.a g.b <;> simp [mask,h]
  have hiT := nativeActualThermal_mask_integrable m (Ioo g.a g.b) measurableSet_Ioo
  have hiM : IntervalIntegrable mask volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hm zero_le_one
      (fun u _=>hmb u) (intervalIntegrable_const (c:=(1:ℝ)))
  have hiUpper := (hiT.const_mul (3*m.groupStrength)).add
    (hiM.const_mul (16*m.groupStrength*(g.capZ-g.capA)^2))
  have hle : (∫u in 0..1,mask u*m.comparisonErrorDensity u)≤
      ∫u in 0..1,(3*m.groupStrength)*(mask u*m.thermal u)+
        (16*m.groupStrength*(g.capZ-g.capA)^2)*mask u := by
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one]
    apply integral_mono_of_nonneg _ ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiUpper) _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact mul_nonneg (hmb u).1 (mul_nonneg (laplaceComparisonStrength_pos m.d m.hlam _).le
        (add_nonneg (nativeActualThermal_nonneg m hu) (sq_nonneg _)))
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      by_cases hs:m.R u∈Ioo g.a g.b
      · have hcap : m.R u∈Ioo g.capA g.capZ := (Ioo_subset_Ioo g.haCap g.hbCap) hs
        have hmis := native_actual_cap_mismatch_endpoint_cases m g.ha g.hz hcap g.hboundary
          (g.hnegative _ hcap)
        rw [comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha (Ioc_subset_Icc_self hu)] at hmis
        have hT0 := nativeActualThermal_nonneg m hu
        have he0 := (laplaceComparisonStrength_pos m.d m.hlam (m.R u)).le
        have hstrength := m.strength_le_groupStrength
          (Ioo_subset_Icc_self ((Ioo_subset_Ioo g.haGroup g.hbGroup) hs))
        have hb : m.thermal u+(orderedPathS (m.n+1) m.bf m.hf u-m.R u)^2≤
            3*m.thermal u+16*(g.capZ-g.capA)^2 := by nlinarith
        have hmul := mul_le_mul_of_nonneg_left hb he0
        have hmul' := mul_le_mul_of_nonneg_right hstrength
          (add_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) hT0)
            (mul_nonneg (by norm_num : (0:ℝ)≤16) (sq_nonneg (g.capZ-g.capA))))
        simp only [mask,indicator_of_mem hs,one_mul,mul_one,NativeBandModel.comparisonErrorDensity]
        nlinarith
      · simp only [mask,indicator_of_notMem hs,zero_mul,mul_zero,add_zero,le_refl]
  rw [intervalIntegral.integral_add (hiT.const_mul _) (hiM.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hle
  have hmass := nativeBroadSlice_mask_mass_eq m g
  simpa only [mask,hmass] using hle

theorem actual_native_outer_broad_slice_error_bound
    (m:NativeBandModel) (s:NativeBandRefinement m) (g:NativeBroadSliceGeometry m)
    {cl cu Az z0:ℝ} (hcl:0< cl) (hcu:0< cu) (hAz:0≤ Az) (hz0:z0∈Icc (0:ℝ) 1)
    (hzxs:z0≤ Az*m.xs) (htravel:nativeCapTravel m≤ m.xs)
    (hregular:∀r∈Icc z0 1,cl*r≤ m.alpha.val.val r ∧ m.alpha.val.val r≤ cu*r)
    (houter:2*cu*(Az+1)*m.xs≤ m.alpha.val.val g.capZ)
    (hstrict:∀j,∀i<(s.as j).length,partitionPoint 0 (s.as j) i< partitionPoint 0 (s.as j) (i+1))
    {cut:ℝ} (hcut:0< cut) (hsmall:2*cut< m.U) (hleft:m.cutRadius≤ m.ag)
    (hupper:m.xs+m.alpha.val.val m.zg≤ m.y) (hlog:Real.log (1/cut)≤ m.Lside)
    (hraw:∀ᶠ j in atTop,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>ProbabilityTheory.gaussianReal 0 (m.q 0 a)) id measurable_id≤ m.Q) :
    let width := ∫r in Ioo g.a g.b,deriv m.alpha.val.val r
    let loss := m.Ko^2+25*(1+g.scale/m.U)*Real.log ((1+m.U)/m.U)+1
    let D := nativeOuterBroadDiameter m g cl cu
    (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)≤
      3*m.groupStrength*(nativeConditionalLedgerBudget 1 width cut D
        (108*loss*(Real.log m.N)^2/(m.P*m.rho)*Real.log (width/cut))
        (54*loss*(Real.log m.N)^2*width/(m.P*m.rho^2)) (m.reverse D) m.Lside)+
      16*m.groupStrength*(nativeOuterBroadTravel m g cl cu)^2*width := by
  dsimp only
  have ht := actual_native_outer_broad_slice_comparison m s g hcl hcu hAz hz0 hzxs htravel hregular
    houter hstrict hcut hsmall hleft hupper hlog hraw
  have hmis := actual_native_broad_slice_error_le_thermal m g
  let c:NativeActualCapInterval m := ⟨g.capA,g.capZ,g.ha,g.haz,g.hz,g.hnegative⟩
  have hcap := le_min (actual_native_cap_travel m c)
    (actual_native_outer_broad_cap_local_travel m g hcl hcu hAz hz0 hzxs htravel hregular houter)
  have hsq := pow_le_pow_left₀ (sub_nonneg.mpr g.haz.le) hcap 2
  have hwidth0 : 0≤∫r in Ioo g.a g.b,deriv m.alpha.val.val r :=
    m.hU.le.trans (g.hscale.trans g.hmass)
  have hterm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (by norm_num : (0:ℝ)≤16) m.groupStrength_pos.le)) hwidth0
  have hmain := mul_le_mul_of_nonneg_left ht
    (mul_nonneg (by norm_num : (0:ℝ)≤3) m.groupStrength_pos.le)
  exact hmis.trans (add_le_add hmain hterm)

theorem native_actual_quantile_regular_upper (m:NativeBandModel) {cl Az z0 u:ℝ}
    (hcl:0< cl) (hAz:0≤ Az) (hz0:z0∈Icc (0:ℝ) 1) (hzxs:z0≤ Az*m.xs)
    (hregular:∀r∈Icc z0 1,cl*r≤ m.alpha.val.val r) (hu:u∈Icc (0:ℝ) 1) :
    m.R u≤ Az*m.xs+u/cl := by
  by_cases hr:z0≤ m.R u
  · have hR := comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u
    have hh := hregular (m.R u) ⟨hr,hR.2⟩
    rw [comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hu] at hh
    have hb : m.R u≤ u/cl := (le_div_iff₀ hcl).mpr (by simpa only [mul_comm] using hh)
    exact hb.trans (le_add_of_nonneg_left (mul_nonneg hAz m.hxs.le))
  · exact (le_of_not_ge hr).trans (hzxs.trans
      (le_add_of_nonneg_right (div_nonneg hu.1 hcl.le)))

theorem actual_native_near_zero_error_of_normalized_B (m:NativeBandModel)
    {K cl Az z0:ℝ} (hK:0≤ K) (hcl:0< cl) (hAz:0≤ Az) (hz0:z0∈Icc (0:ℝ) 1)
    (hzxs:z0≤ Az*m.xs) (hregular:∀r∈Icc z0 1,cl*r≤ m.alpha.val.val r)
    (hB:∀u∈Ioc (0:ℝ) 1,orderedPathB (m.n+1) m.bf m.hf u≤ K*(m.xs+u)^2) :
    (∫u in 0..1,(nativeBroadNearZero m).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)≤
      8*m.lam*m.U*(K*(m.xs+8*m.U)^2+(Az*m.xs+8*m.U/cl)^2) := by
  let mask := fun u=>(nativeBroadNearZero m).indicator (fun _=>(1:ℝ)) (m.R u)
  let C := m.lam*(K*(m.xs+8*m.U)^2+(Az*m.xs+8*m.U/cl)^2)
  have hC : 0≤ C := mul_nonneg m.hlam.le (add_nonneg (mul_nonneg hK (sq_nonneg _)) (sq_nonneg _))
  have hm : Measurable mask := (measurable_const.indicator measurableSet_Ioo).comp
    (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable
  have hmb u : mask u∈Icc (0:ℝ) 1 := by by_cases h:m.R u∈nativeBroadNearZero m <;> simp [mask,h]
  have hiM : IntervalIntegrable mask volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hm zero_le_one
      (fun u _=>hmb u) (intervalIntegrable_const (c:=(1:ℝ)))
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hle : (∫u in 0..1,mask u*m.comparisonErrorDensity u)≤∫u in 0..1,C*mask u := by
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one]
    apply integral_mono_of_nonneg _ ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hiM.const_mul C)) _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact mul_nonneg (hmb u).1 (mul_nonneg (laplaceComparisonStrength_pos m.d m.hlam _).le
        (add_nonneg (nativeActualThermal_nonneg m hu) (sq_nonneg _)))
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      by_cases hs:m.R u∈nativeBroadNearZero m
      · have hv : min (8*m.U) 1∈Icc (0:ℝ) 1 :=
          ⟨(lt_min (mul_pos (by norm_num) m.hU) zero_lt_one).le,min_le_right _ _⟩
        have hum := (native_mass_slice_quantile_mem m (by norm_num) hv (Ioc_subset_Icc_self hu)).mp hs
        have hu8 : u≤8*m.U := hum.2.le.trans (min_le_left _ _)
        have hR := comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u
        have hRup := (native_actual_quantile_regular_upper m hcl hAz hz0 hzxs hregular
          (Ioc_subset_Icc_self hu)).trans (add_le_add le_rfl (div_le_div_of_nonneg_right hu8 hcl.le))
        have hRsq := pow_le_pow_left₀ hR.1 hRup 2
        have hxs0 := add_nonneg m.hxs.le hu.1.le
        have hxssq := pow_le_pow_left₀ hxs0 (add_le_add le_rfl hu8) 2
        have hraw := (hB u hu).trans (mul_le_mul_of_nonneg_left hxssq hK)
        have hp := orderedPath_SK_bounds (m.n+1) (by omega) m.bf m.hf
          (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu
        have hbracket : m.thermal u+(orderedPathS (m.n+1) m.bf m.hf u-m.R u)^2≤
            K*(m.xs+8*m.U)^2+(Az*m.xs+8*m.U/cl)^2 := by
          dsimp [NativeBandModel.thermal]
          nlinarith [mul_nonneg hp.1 hR.1]
        have hmul := mul_le_mul_of_nonneg_left hbracket (laplaceComparisonStrength_pos m.d m.hlam (m.R u)).le
        have hsum0 : 0≤K*(m.xs+8*m.U)^2+(Az*m.xs+8*m.U/cl)^2 :=
          add_nonneg (mul_nonneg hK (sq_nonneg (m.xs+8*m.U)))
            (sq_nonneg (Az*m.xs+8*m.U/cl))
        have hstrength := mul_le_mul_of_nonneg_right (laplaceComparisonStrength_le m.d m.hlam.le (m.R u))
          hsum0
        simp only [mask,indicator_of_mem hs,one_mul,mul_one,NativeBandModel.comparisonErrorDensity]
        exact hmul.trans hstrength
      · simp only [mask,indicator_of_notMem hs,zero_mul,mul_zero,le_refl]
  rw [intervalIntegral.integral_const_mul] at hle
  have hmasses := mul_le_mul_of_nonneg_left (nativeBroadNearZero_mass_le m) hC
  have hfinal := hle.trans hmasses
  dsimp [C,mask] at hfinal
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
