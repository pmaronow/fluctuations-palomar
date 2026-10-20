module

public import ComparisonNativePositiveBroadFrame
public import ComparisonNativeBroadError
public import ComparisonNativeRawMasterRefinement

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4800000
attribute [local instance] Classical.propDecidable

theorem actual_native_positive_broad_slice_comparison
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBroadSliceGeometry m)
    {cut : ℝ} (hcut : 0< cut) (hmargin : 2*cut<∫r in Ioo g.a g.b,deriv m.alpha.val.val r)
    (hleft : m.cutRadius≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg≤ m.y)
    (hlog : Real.log (1/cut)≤ m.Lside)
    (hraw : ∀j,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>ProbabilityTheory.gaussianReal 0 (m.q 0 a)) id measurable_id≤ m.Q) :
    let width := ∫r in Ioo g.a g.b,deriv m.alpha.val.val r
    let loss := m.Ko^2+25*(1+g.scale/m.U)*Real.log ((1+m.U)/m.U)+1
    (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.thermal u)≤
      nativeConditionalLedgerBudget 1 width cut m.D0
        (108*loss*(Real.log m.N)^2/(m.P*m.rho)*Real.log (width/cut))
        (54*loss*(Real.log m.N)^2*width/(m.P*m.rho^2)) (m.reverse m.D0) m.Lside := by
  dsimp only
  obtain ⟨N,f,hs,hA,hZ,hscale,hwidth⟩ := exists_actual_native_positive_broad_slice_frame m s g
    hcut hmargin hleft hupper hlog hraw
  have hn := f.thermal_le_native_budget hcut
  simpa only [NativeBroadFrame.AS,NativeBroadFrame.AC,NativeBroadFrame.loss,
    hs,hscale,hwidth] using hn

theorem actual_native_calibrated_positive_broad_slice_comparison
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBroadSliceGeometry m)
    {cut : ℝ} (hcut : 0< cut) (hsmall : 2*cut< m.U)
    (hleft : m.cutRadius≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg≤ m.y)
    (hlog : Real.log (1/cut)≤ m.Lside)
    (hraw : ∀j,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>ProbabilityTheory.gaussianReal 0 (m.q 0 a)) id measurable_id≤ m.Q) :
    let width := ∫r in Ioo g.a g.b,deriv m.alpha.val.val r
    let loss := m.Ko^2+25*(1+g.scale/m.U)*Real.log ((1+m.U)/m.U)+1
    (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.thermal u)≤
      nativeConditionalLedgerBudget 1 width cut m.D0
        (108*loss*(Real.log m.N)^2/(m.P*m.rho)*Real.log (width/cut))
        (54*loss*(Real.log m.N)^2*width/(m.P*m.rho^2)) (m.reverse m.D0) m.Lside :=
  actual_native_positive_broad_slice_comparison m s g hcut
    (hsmall.trans_le (g.hscale.trans g.hmass)) hleft hupper hlog hraw

theorem actual_native_calibrated_positive_broad_slice_comparison_of_eventual_raw
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBroadSliceGeometry m)
    {cut : ℝ} (hcut : 0< cut) (hsmall : 2*cut< m.U)
    (hleft : m.cutRadius≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg≤ m.y)
    (hlog : Real.log (1/cut)≤ m.Lside)
    (hraw : ∀ᶠ j in atTop,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>ProbabilityTheory.gaussianReal 0 (m.q 0 a)) id measurable_id≤ m.Q) :
    let width := ∫r in Ioo g.a g.b,deriv m.alpha.val.val r
    let loss := m.Ko^2+25*(1+g.scale/m.U)*Real.log ((1+m.U)/m.U)+1
    (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.thermal u)≤
      nativeConditionalLedgerBudget 1 width cut m.D0
        (108*loss*(Real.log m.N)^2/(m.P*m.rho)*Real.log (width/cut))
        (54*loss*(Real.log m.N)^2*width/(m.P*m.rho^2)) (m.reverse m.D0) m.Lside := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hraw
  exact actual_native_calibrated_positive_broad_slice_comparison m (s.tail N) g
    hcut hsmall hleft hupper hlog (fun j=>hN (j+N) (by omega))

theorem actual_native_positive_outer_broad_slice_comparison
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBroadSliceGeometry m)
    {cl cu Az z0 : ℝ}
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hz0 : z0∈Icc (0:ℝ) 1)
    (hzxs : z0≤ Az*m.xs) (htravel : nativeCapTravel m≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r≤ m.alpha.val.val r ∧ m.alpha.val.val r≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs≤ m.alpha.val.val g.capZ)
    {cut : ℝ} (hcut : 0< cut) (hsmall : 2*cut< m.U)
    (hleft : m.cutRadius≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg≤ m.y)
    (hlog : Real.log (1/cut)≤ m.Lside)
    (hraw : ∀ᶠ j in atTop,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>ProbabilityTheory.gaussianReal 0 (m.q 0 a)) id measurable_id≤ m.Q) :
    let width := ∫r in Ioo g.a g.b,deriv m.alpha.val.val r
    let loss := m.Ko^2+25*(1+g.scale/m.U)*Real.log ((1+m.U)/m.U)+1
    let D := nativeOuterBroadDiameter m g cl cu
    (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.thermal u)≤
      nativeConditionalLedgerBudget 1 width cut D
        (108*loss*(Real.log m.N)^2/(m.P*m.rho)*Real.log (width/cut))
        (54*loss*(Real.log m.N)^2*width/(m.P*m.rho^2)) (m.reverse D) m.Lside := by
  dsimp only
  obtain ⟨N,hN⟩ := eventually_atTop.mp hraw
  let st := s.tail N
  obtain ⟨j,f,hs,hA,hZ,hscale,hwidth⟩ := exists_actual_native_positive_broad_slice_frame m st g
    hcut (hsmall.trans_le (g.hscale.trans g.hmass)) hleft hupper hlog
    (fun t=>hN (t+N) (by omega))
  let c : NativeActualCapInterval m := ⟨g.capA,g.capZ,g.ha,g.haz,g.hz,g.hnegative⟩
  have hglobal := actual_native_cap_travel m c
  have hlocal := actual_native_outer_broad_cap_local_travel m g hcl hcu hAz hz0 hzxs htravel
    hregular houter
  have hcap : 9*Real.log m.N*(f.capZ-f.capA)≤ nativeOuterBroadDiameter m g cl cu := by
    rw [hA,hZ]
    exact mul_le_mul_of_nonneg_left (le_min hglobal hlocal)
      (by linarith [m.hlog] : 0≤9*Real.log m.N)
  have hn := f.thermal_le_native_budget_with_diameter (nativeOuterBroadDiameter m g cl cu)
    (nativeOuterBroadDiameter_pos m g hcl hcu) hcap hcut
  simpa only [NativeBroadFrame.AS,NativeBroadFrame.AC,NativeBroadFrame.loss,hs,hscale,hwidth] using hn

theorem actual_native_positive_outer_broad_slice_error_bound
    (m:NativeBandModel) (s:NativeBandRefinement m) (g:NativeBroadSliceGeometry m)
    {cl cu Az z0:ℝ} (hcl:0< cl) (hcu:0< cu) (hAz:0≤ Az) (hz0:z0∈Icc (0:ℝ) 1)
    (hzxs:z0≤ Az*m.xs) (htravel:nativeCapTravel m≤ m.xs)
    (hregular:∀r∈Icc z0 1,cl*r≤ m.alpha.val.val r ∧ m.alpha.val.val r≤ cu*r)
    (houter:2*cu*(Az+1)*m.xs≤ m.alpha.val.val g.capZ)
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
  have ht := actual_native_positive_outer_broad_slice_comparison m s g hcl hcu hAz hz0 hzxs htravel hregular
    houter hcut hsmall hleft hupper hlog hraw
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

end OAI.SKFluctuations.LaplaceWindowFormalization
