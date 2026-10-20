module

public import ComparisonNativeOuterComparableColumnTransport
public import ComparisonNativeBroadLocalDiameter

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace NativeBroadFrame

theorem outer_comparable_sideFilled_eventually
    {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (g : NativeBroadSliceGeometry m)
    (hslice : f.slice=Ioo g.a g.b) (hwidth : f.width=∫r in Ioo g.a g.b,deriv m.alpha.val.val r)
    {cl cu Az z0 : ℝ} (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hz0 : z0∈Icc (0:ℝ) 1) (hzxs : z0 ≤ Az*m.xs) (htravel : nativeCapTravel m ≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs ≤ m.alpha.val.val g.capZ)
    (hcut : 0 < cut) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ j in atTop,f.sideFilled j ≤
      (108*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/(m.P*m.rho))*
        Real.log (f.width/cut)+eps := by
  let moving:=fun j r=>comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (f.selected j) (fun _=>(0:Fin 1))
      (fun u=>sideSquareColumn (nativeBroadPoints (f.widths j)) cut (f.widths j) u.val) r
  let coeff:=sideSquareColumn (nativeBroadPoints f.width) cut f.width 0
  let C:=27*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/m.P
  have hCoeff : 0 ≤ coeff:=sideSquareColumn_nonneg _ f.hwidth 0
  have hMeas j : Measurable (moving j):=
    comparisonNativeUnitColumnWeight_measurable m.hc m.hk m.hkc m.hm m.hM m.q m.alpha
      (s.as j) (f.selected j) (fun _=>(0:Fin 1)) _
  have hBound j r : ‖moving j r‖ ≤ 2/cut:=by
    have hp:=f.point_geometry hcut j
    have H:=comparisonNativeUnitColumnWeight_side_bound m.hc m.hk m.hkc m.hm m.hM
      m.q m.alpha (s.as j) (s.ho j) (f.selected j) (fun _=>(0:Fin 1))
      (nativeBroadPoints (f.widths j)) hp.1 hp.2.1 hcut (f.hwidths j) hp.2.2.1 r
    change moving j r∈Icc (0:ℝ) (2/cut) at H
    simpa only [Real.norm_eq_abs,abs_of_nonneg H.1] using H.2
  have hCols : Tendsto (fun j=>∫r in Ioo m.ag m.zg,
      |moving j r-(Ioo g.a g.b).indicator (fun _=>coeff) r|) atTop (𝓝 0):=by
    simpa only [moving,coeff,fixedSliceContactWeight,Fin.sum_univ_one,indicator_zero,add_zero,hslice]
      using f.hsideColumns
  have hColsMass : f.width*coeff ≤ 2*Real.log (f.width/cut):=by
    have hwidthPos : 0 < f.width:=by linarith [f.hwidth]
    have H:=sideSquareColumn_mass_sum_le (nativeBroadPoints f.width) 1
      (by simp [nativeBroadPoints]) (by simp [nativeBroadPoints]) hcut f.hwidth
      (fun u=>by
        have hu : u.val=0:=by omega
        simpa [hu,nativeBroadPoints] using hwidthPos)
    simpa [Fin.sum_univ_one,nativeBroadPoints,coeff] using H
  have hP:=m.P_pos
  have hRho:=m.rho_pos
  have HC : 0 ≤ C:=by
    dsimp [C]
    exact div_nonneg (by positivity [native_outer_comparable_trace_constant_nonneg hcl hcu]) hP.le
  have Htrace:=actual_native_outer_comparable_moving_column_trace_eventually m s g
    hcl hcu hAz hz0 hzxs htravel hregular houter moving hMeas
    (by positivity : 0 ≤ 2/cut) hCoeff hBound f.hsupportSide hCols
    (show 0 < eps*m.rho/8 by positivity)
  have Hmesh:=(tendsto_order.mp s.hmesh).2 (eps*m.rho*cut/8) (by positivity)
  filter_upwards [Htrace,Hmesh] with j hj hmesh
  rw [←hwidth] at hj
  change (∫r,deriv m.alpha.val.val r*moving j r∂s.mu j) ≤ C*coeff*f.width+eps*m.rho/8 at hj
  have Hlog:=mul_le_mul_of_nonneg_left hColsMass HC
  have HtraceFinal : (∫r,deriv m.alpha.val.val r*moving j r∂s.mu j) ≤
      (2*C)*Real.log (f.width/cut)+eps*m.rho/8:=by
    nlinarith only [hj,Hlog]
  unfold sideFilled
  apply (div_le_iff₀ hRho).mpr
  have Hmeshnorm : 4*s.mesh j/cut ≤ eps*m.rho/2:=by
    apply (div_le_iff₀ hcut).mpr
    nlinarith only [hmesh]
  have HE : ((108*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/(m.P*m.rho))*
      Real.log (f.width/cut)+eps)*m.rho=
      (108*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/m.P)*Real.log (f.width/cut)+eps*m.rho:=by
    field_simp
  rw [HE]
  rw [show 108*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/m.P=4*C by dsimp [C];ring]
  change 2*(∫r,deriv m.alpha.val.val r*moving j r∂s.mu j)+4*s.mesh j/cut ≤ _
  nlinarith only [HtraceFinal,Hmeshnorm,mul_pos heps hRho]

theorem outer_comparable_unionFilled_eventually
    {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (g : NativeBroadSliceGeometry m)
    (hslice : f.slice=Ioo g.a g.b) (hwidth : f.width=∫r in Ioo g.a g.b,deriv m.alpha.val.val r)
    {cl cu Az z0 : ℝ} (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hz0 : z0∈Icc (0:ℝ) 1) (hzxs : z0 ≤ Az*m.xs) (htravel : nativeCapTravel m ≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs ≤ m.alpha.val.val g.capZ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ j in atTop,f.unionFilled j ≤
      (54*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/(m.P*m.rho^2))*f.width+eps := by
  let moving:=fun j r=>comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (f.selected j) (fun _=>(0:Fin 1)) (fun _=>1) r
  let C:=27*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/m.P
  have hMeas j : Measurable (moving j):=
    comparisonNativeUnitColumnWeight_measurable m.hc m.hk m.hkc m.hm m.hM m.q m.alpha
      (s.as j) (f.selected j) (fun _=>(0:Fin 1)) _
  have hBound j r : ‖moving j r‖ ≤ 1:=by
    have H:=radiusCellEnergyDensity_mem_Icc_bound m.R
      (comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha)
      (s.as j) (s.ho j) (nativeSelectedColumn (f.selected j) (fun _=>(0:Fin 1)) (fun _=>1)) (show (0:ℝ) ≤ 1 by norm_num)
      (fun i=>by unfold nativeSelectedColumn;split_ifs <;> norm_num) r
    change moving j r∈Icc (0:ℝ) 1 at H
    simpa only [Real.norm_eq_abs,abs_of_nonneg H.1] using H.2
  have hCols : Tendsto (fun j=>∫r in Ioo m.ag m.zg,
      |moving j r-(Ioo g.a g.b).indicator (fun _=>1) r|) atTop (𝓝 0):=by
    simpa only [moving,fixedSliceContactWeight,Fin.sum_univ_one,indicator_zero,add_zero,hslice]
      using f.hmaskColumns
  have hRho:=m.rho_pos
  have Htrace:=actual_native_outer_comparable_moving_column_trace_eventually m s g
    hcl hcu hAz hz0 hzxs htravel hregular houter moving hMeas
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1) hBound f.hsupportMask hCols
    (show 0 < eps*m.rho^2/8 by positivity)
  have Hmesh:=(tendsto_order.mp s.hmesh).2 (eps*m.rho^2/8) (by positivity)
  filter_upwards [Htrace,Hmesh] with j hj hmesh
  rw [←hwidth,mul_one] at hj
  change (∫r,deriv m.alpha.val.val r*moving j r∂s.mu j) ≤ C*f.width+eps*m.rho^2/8 at hj
  unfold unionFilled
  apply (div_le_iff₀ (sq_pos_of_pos hRho)).mpr
  have HE : ((54*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/(m.P*m.rho^2))*f.width+eps)*m.rho^2=
      (54*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/m.P)*f.width+eps*m.rho^2:=by
    have hP:=m.P_pos
    field_simp
  rw [HE]
  rw [show 54*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/m.P=2*C by dsimp [C];ring]
  change 2*(∫r,deriv m.alpha.val.val r*moving j r∂s.mu j)+2*s.mesh j ≤ _
  nlinarith only [hj,hmesh,mul_pos heps (sq_pos_of_pos hRho)]

end NativeBroadFrame
end OAI.SKFluctuations.LaplaceWindowFormalization
