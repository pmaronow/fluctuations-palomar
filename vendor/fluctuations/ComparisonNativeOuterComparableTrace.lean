module

public import ComparisonNativeWholeCapEndpointGeometry
public import ComparisonNativeBroadFrameConstruction
public import ComparisonCapSideTraceLocalizedBroad
public import ComparisonCapSideTraceAggregate

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators

def nativeOuterComparableTraceConstant (cl cu : ℝ) : ℝ :=
  (max 1 (10*cu/cl))^2*(8*cu/cl)

theorem native_outer_comparable_trace_constant_nonneg {cl cu : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) : 0 ≤ nativeOuterComparableTraceConstant cl cu := by
  unfold nativeOuterComparableTraceConstant
  positivity

theorem actual_native_outer_slice_density_length_le
    (m : NativeBandModel) (g : NativeBroadSliceGeometry m) {cl cu Az z0 : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hz0 : z0∈Icc (0:ℝ) 1)
    (hzxs : z0 ≤ Az*m.xs) (htravel : nativeCapTravel m ≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs ≤ m.alpha.val.val g.capZ) :
    m.M g.ceiling*(g.capZ-g.capA) ≤
      nativeOuterComparableTraceConstant cl cu*(∫r in Ioo g.a g.b,deriv m.alpha.val.val r) := by
  let c : NativeActualCapInterval m:=⟨g.capA,g.capZ,g.ha,g.haz,g.hz,g.hnegative⟩
  let K:=max 1 (10*cu/cl)
  let kappa:=cl/(2*cu)
  have hK : 1 ≤ K:=le_max_left _ _
  have hk : 0 < kappa:=by dsimp [kappa];positivity
  have hv : 0 < g.scale:=m.hU.trans_le g.hscale
  have HA0 : 0 ≤ m.alpha.val.val g.capA:=(m.alpha.val.property.1 _).1
  have Hfloor:=actual_native_outer_cap_mass_floor m c hcl hcu hAz hz0 hzxs htravel hregular houter
  change kappa*m.alpha.val.val g.capZ ≤ m.alpha.val.val g.capA at Hfloor
  have Hscale:=nativeBroadSlice_scale_le_cap_mass m g
  have HA : kappa*g.scale ≤ m.alpha.val.val g.capA:=
    (mul_le_mul_of_nonneg_left Hscale hk.le).trans Hfloor
  have HAhi : m.alpha.val.val g.capA ≤ 4*g.scale:=
    ((m.alpha.val.property.2 g.haCap).trans (m.alpha.val.property.2 g.hab.le)).trans
      (g.hceilingMass.trans g.hcomparable)
  have HZ : m.alpha.val.val g.capZ ≤ (8*cu/cl)*g.scale:=by
    have H:=Hfloor.trans HAhi
    have HH : m.alpha.val.val g.capZ ≤ (4*g.scale)/kappa:=
      (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using H)
    convert HH using 1
    dsimp [kappa]
    field_simp
    ring
  have HKk : (5:ℝ) ≤ K*kappa:=by
    have H:=mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (10*cu/cl)) hk.le
    have HE : (10*cu/cl)*kappa=5:=by dsimp [kappa];field_simp;ring
    rw [HE] at H
    exact H
  have Hband : g.ceiling+m.U ≤ K*(m.alpha.val.val g.capA+m.U):=by
    have H1:=mul_le_mul_of_nonneg_left HA (zero_le_one.trans hK)
    have H2:=mul_le_mul_of_nonneg_right HKk hv.le
    have H3 : 0 ≤ K*m.U:=mul_nonneg (zero_le_one.trans hK) m.hU.le
    nlinarith [g.hcomparable,g.hscale]
  have HR:=comparisonCap_common_mass_band_ratio (δ:=m.delta)
    (zero_lt_one.trans_le m.hN) m.hU m.hLcap m.hE m.hd.le HA0 hK Hband
    (u:=m.alpha.val.val g.capA) (v:=g.ceiling) le_rfl le_rfl g.hceiling.1
  have HMa : 0 < m.M (m.alpha.val.val g.capA):=by
    rw [congrFun m.hMdef (m.alpha.val.val g.capA)]
    exact (comparisonCap_first_term (δ:=m.delta) (zero_lt_one.trans_le m.hN) m.hU m.hLcap m.hE m.hd.le HA0).1
  have HR' : m.M g.ceiling ≤ K^2*m.M (m.alpha.val.val g.capA):=by
    rw [←congrFun m.hMdef g.ceiling,←congrFun m.hMdef (m.alpha.val.val g.capA)] at HR
    simpa only [mul_comm] using (div_le_iff₀ HMa).mp HR
  have Hmass:=comparison_cap_mass_lower m.hm m.hM m.alpha m.H m.hbang g.ha g.haz.le g.hz g.hnegative
  have H1:=mul_le_mul_of_nonneg_right HR' (sub_nonneg.mpr g.haz.le)
  have H2:=mul_le_mul_of_nonneg_left Hmass (sq_nonneg K)
  have H3:=mul_le_mul_of_nonneg_left (HZ.trans
    (mul_le_mul_of_nonneg_left g.hmass (by positivity : 0 ≤ 8*cu/cl))) (sq_nonneg K)
  unfold nativeOuterComparableTraceConstant
  dsimp only [K] at *
  nlinarith only [H1,H2,H3,HA0]

theorem actual_native_outer_comparable_slice_weighted_trace_eventually
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBroadSliceGeometry m)
    {cl cu Az z0 : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hz0 : z0∈Icc (0:ℝ) 1)
    (hzxs : z0 ≤ Az*m.xs) (htravel : nativeCapTravel m ≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs ≤ m.alpha.val.val g.capZ)
    (w : ℝ→ℝ) (hw : Measurable w) {W : ℝ} (hW : 0 ≤ W)
    (hwb : ∀r∈Ioo g.a g.b,0 ≤ w r ∧ w r ≤ W) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ j in atTop,
      (∫r in Ioo g.a g.b,deriv m.alpha.val.val r*w r∂s.mu j) ≤
        (27*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/m.P)*W*
          (∫r in Ioo g.a g.b,deriv m.alpha.val.val r)+eps := by
  let C:=27*(Real.log m.N)^2/m.P
  let A:=Ioo g.a g.b
  have hA : MeasurableSet A:=measurableSet_Ioo
  have hAcap : A⊆Ioo g.capA g.capZ:=fun r hr=>⟨g.haCap.trans_lt hr.1,hr.2.trans_le g.hbCap⟩
  have hAgroup : A⊆Ioo m.ag m.zg:=fun r hr=>⟨g.haGroup.trans_lt hr.1,hr.2.trans_le g.hbGroup⟩
  have Hoverlap : max g.capA m.ag < min g.capZ m.zg:=
    (max_le g.haCap g.haGroup).trans_lt (g.hab.trans_le (le_min g.hbCap g.hbGroup))
  have hMV : 0 ≤ m.M g.ceiling:=by
    rw [congrFun m.hMdef g.ceiling]
    exact (comparisonCap_first_term (δ:=m.delta) (zero_lt_one.trans_le m.hN) m.hU m.hLcap m.hE m.hd.le g.hceiling.1).1.le
  have hden : ∀ᵐ r,r∈A → deriv m.alpha.val.val r ≤ m.M g.ceiling:=by
    filter_upwards [m.hbang] with r hr hrA
    have hrc:=hAcap hrA
    rw [hr ⟨g.ha.trans hrc.1.le,hrc.2.le.trans g.hz⟩ (g.hnegative r hrc)]
    exact m.hm (m.alpha.val.property.1 r) g.hceiling
      ((m.alpha.val.property.2 (le_of_lt hrA.2)).trans g.hceilingMass)
  have hsmall : 0 < eps/(m.M g.ceiling*W+1):=by positivity
  have Htrace:=comparisonPhysicalLocalizedCapMeasure_eventually m.hc m.hk m.hkc m.hm m.hM
    m.hN m.hlog m.hd m.hnd m.hlam m.hld m.n m.dphys m.e m.b m.h m.hb m.hlb m.hh m.hh0
    m.alpha m.H m.multiplier m.hH m.hJ m.hD g.ha g.haz g.hz m.hag m.hzg Hoverlap
    g.hboundary g.hnegative A hAcap hAgroup s.as s.mesh s.ho s.he s.hm s.hm0 s.hmesh hsmall
  have Hnormal:=actual_native_outer_slice_density_length_le m g hcl hcu hAz hz0 hzxs htravel hregular houter
  have hC : 0 ≤ C:=by dsimp [C];exact div_nonneg (by positivity) m.P_pos.le
  filter_upwards [Htrace] with j hj
  let : IsFiniteMeasure (s.mu j):=by unfold NativeBandRefinement.mu;infer_instance
  have hdom : s.mu j ≤ volume:=
    (comparisonPhysicalRadiusMeasure_le_compact_volume m.hc m.hk m.hkc m.hm m.hM
      m.n m.dphys m.e m.d m.lam m.b m.h m.alpha (s.as j) (s.ho j)).trans Measure.restrict_le_self
  have Hdens:=cap_bounded_density_trace_le (s.mu j) hdom m.alpha.val.val w
    m.alpha.val.property.2 hw A hA hMV hW hden hwb
  have Hμ:=mul_le_mul_of_nonneg_left hj (mul_nonneg hMV hW)
  have HE : (9*Real.log m.N)*(g.capZ-g.capA)/
      ((m.n+1:ℝ)*(((1/3)/Real.log m.N)*laplaceComparisonStrength m.d m.lam m.zg))=
      C*(g.capZ-g.capA):=by
    dsimp [C,NativeBandModel.P]
    field_simp [(laplaceComparisonStrength_pos m.d m.hlam m.zg).ne']
    ring
  rw [HE] at Hμ
  change m.M g.ceiling*W*(s.mu j).real A ≤
    m.M g.ceiling*W*(C*(g.capZ-g.capA)+eps/(m.M g.ceiling*W+1)) at Hμ
  have Hn:=mul_le_mul_of_nonneg_left Hnormal (mul_nonneg hC hW)
  have Herr : m.M g.ceiling*W*(eps/(m.M g.ceiling*W+1)) ≤ eps:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < m.M g.ceiling*W+1)).mpr
    nlinarith
  rw [show 27*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/m.P=
    C*nativeOuterComparableTraceConstant cl cu by dsimp [C];ring]
  dsimp only [A] at *
  nlinarith only [Hdens,Hμ,Hn,Herr]

theorem actual_native_outer_comparable_slice_trace_eventually
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBroadSliceGeometry m)
    {cl cu Az z0 : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hz0 : z0∈Icc (0:ℝ) 1)
    (hzxs : z0 ≤ Az*m.xs) (htravel : nativeCapTravel m ≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs ≤ m.alpha.val.val g.capZ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ j in atTop,
      (∫r in Ioo g.a g.b,deriv m.alpha.val.val r∂s.mu j) ≤
        (27*nativeOuterComparableTraceConstant cl cu*(Real.log m.N)^2/m.P)*
          (∫r in Ioo g.a g.b,deriv m.alpha.val.val r)+eps := by
  simpa only [mul_one] using actual_native_outer_comparable_slice_weighted_trace_eventually
    m s g hcl hcu hAz hz0 hzxs htravel hregular houter (fun _=>1) measurable_const
    (by norm_num : (0:ℝ) ≤ 1) (fun _ _=>by norm_num) heps

end OAI.SKFluctuations.LaplaceWindowFormalization
