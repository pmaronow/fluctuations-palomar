module

public import ComparisonNativeOuterComparableFrame
public import ComparisonNativePositiveBroadConsumers

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace NativeBroadFrame

theorem thermal_le_native_outer_comparable_budget_with_diameter
    {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (g : NativeBroadSliceGeometry m)
    (hslice : f.slice=Ioo g.a g.b) (hwidth : f.width=∫r in Ioo g.a g.b,deriv m.alpha.val.val r)
    {cl cu Az z0 : ℝ} (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hz0 : z0∈Icc (0:ℝ) 1) (hzxs : z0 ≤ Az*m.xs) (htravel : nativeCapTravel m ≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs ≤ m.alpha.val.val g.capZ)
    (D : ℝ) (hD : 0 < D) (hcap : 9*Real.log m.N*(f.capZ-f.capA) ≤ D) (hcut : 0 < cut) :
    (∫u in 0..1,f.slice.indicator (fun _=>1) (m.R u)*m.thermal u) ≤
      nativeConditionalLedgerBudget 1 f.width cut D
        (108*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/(m.P*m.rho)*Real.log (f.width/cut))
        (54*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2*f.width/(m.P*m.rho^2))
        (m.reverse D) m.Lside := by
  let VS:=108*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/(m.P*m.rho)*Real.log (f.width/cut)
  let TC:=54*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2*f.width/(m.P*m.rho^2)
  let C:=66+64*m.Lside+65536*(1+m.Lside)^2
  have hC : 0 ≤ C:=by have hL:=m.hLside;dsimp [C];positivity
  have Hdiam:=nativeBroadChosenDiameter_tendsto m s D
  have Hrev : Tendsto (fun j=>m.reverse (nativeBroadChosenDiameter m s D j)) atTop (𝓝 (m.reverse D)):=
    (Hdiam.rpow_const (Or.inl hD.ne')).mul_const _
  apply le_of_forall_pos_le_add
  intro t ht
  let err:=t/(48+C+1)
  have herr : 0 < err:=by dsimp [err];positivity
  have HS:=f.outer_comparable_sideFilled_eventually g hslice hwidth hcl hcu hAz hz0 hzxs htravel hregular houter hcut herr
  have HT:=f.outer_comparable_unionFilled_eventually g hslice hwidth hcl hcu hAz hz0 hzxs htravel hregular houter herr
  have Hupper : ∀ᶠ j in atTop,f.defect j ≤ nativeConditionalLedgerBudget 1 (f.widths j) cut
      (nativeBroadChosenDiameter m s D j) (VS+err) (TC+err)
      (m.reverse (nativeBroadChosenDiameter m s D j)) m.Lside:=by
    filter_upwards [HS,HT] with j hsj htj
    have H:=f.finite_budget_with_diameter D hD hcap hcut j
    unfold nativeConditionalLedgerBudget at H ⊢
    have Ht:=mul_le_mul_of_nonneg_left (by simpa only [div_mul_eq_mul_div] using htj : f.unionFilled j ≤ TC+err) hC
    have Hv:=mul_le_mul_of_nonneg_left hsj (by norm_num : (0:ℝ) ≤ 48)
    exact H.trans (add_le_add (add_le_add (add_le_add (add_le_add Hv le_rfl) le_rfl) Ht) le_rfl)
  have Hlim : Tendsto (fun j=>nativeConditionalLedgerBudget 1 (f.widths j) cut
      (nativeBroadChosenDiameter m s D j) (VS+err) (TC+err)
      (m.reverse (nativeBroadChosenDiameter m s D j)) m.Lside) atTop
      (𝓝 (nativeConditionalLedgerBudget 1 f.width cut D (VS+err) (TC+err) (m.reverse D) m.Lside)):=by
    unfold nativeConditionalLedgerBudget
    exact (((tendsto_const_nhds.add
      ((f.hwidthlim.const_mul _).mul (Hdiam.pow 2))).add
      ((f.hwidthlim.const_mul 32).mul Hrev)).add tendsto_const_nhds).add tendsto_const_nhds
  have Hlimit:=le_of_tendsto_of_tendsto f.defect_tendsto Hlim Hupper
  have Herr : (48+C)*err ≤ t:=by
    dsimp [err]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < 48+C+1)).mpr
    nlinarith
  dsimp only [VS,TC] at Hlimit
  unfold nativeConditionalLedgerBudget at Hlimit ⊢
  dsimp only [C] at Herr
  nlinarith only [Hlimit,Herr]

end NativeBroadFrame

theorem actual_native_outer_comparable_broad_slice_comparison
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBroadSliceGeometry m)
    {cl cu Az z0 : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hz0 : z0∈Icc (0:ℝ) 1)
    (hzxs : z0 ≤ Az*m.xs) (htravel : nativeCapTravel m ≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs ≤ m.alpha.val.val g.capZ)
    {cut : ℝ} (hcut : 0 < cut) (hsmall : 2*cut < m.U)
    (hleft : m.cutRadius ≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hlog : Real.log (1/cut) ≤ m.Lside)
    (hraw : ∀ᶠ j in atTop,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id ≤ m.Q) :
    let width:=∫r in Ioo g.a g.b,deriv m.alpha.val.val r
    let D:=nativeOuterBroadDiameter m g cl cu
    (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.thermal u) ≤
      nativeConditionalLedgerBudget 1 width cut D
        (108*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/(m.P*m.rho)*Real.log (width/cut))
        (54*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2*width/(m.P*m.rho^2))
        (m.reverse D) m.Lside := by
  dsimp only
  obtain ⟨N,hN⟩:=eventually_atTop.mp hraw
  let st:=s.tail N
  obtain ⟨j,f,hs,hA,hZ,hscale,hwidth⟩:=exists_actual_native_positive_broad_slice_frame m st g
    hcut (hsmall.trans_le (g.hscale.trans g.hmass)) hleft hupper hlog
    (fun t=>hN (t+N) (by omega))
  let c : NativeActualCapInterval m:=⟨g.capA,g.capZ,g.ha,g.haz,g.hz,g.hnegative⟩
  have Hglobal:=actual_native_cap_travel m c
  have Hlocal:=actual_native_outer_broad_cap_local_travel m g hcl hcu hAz hz0 hzxs htravel hregular houter
  have Hcap : 9*Real.log m.N*(f.capZ-f.capA) ≤ nativeOuterBroadDiameter m g cl cu:=by
    rw [hA,hZ]
    exact mul_le_mul_of_nonneg_left (le_min Hglobal Hlocal)
      (by linarith [m.hlog] : 0 ≤ 9*Real.log m.N)
  have H:=f.thermal_le_native_outer_comparable_budget_with_diameter g hs hwidth
    hcl hcu hAz hz0 hzxs htravel hregular houter (nativeOuterBroadDiameter m g cl cu)
    (nativeOuterBroadDiameter_pos m g hcl hcu) Hcap hcut
  simpa only [hs,hwidth] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
