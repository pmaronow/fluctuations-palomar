module

public import ComparisonBroadPhysicalTrace
public import ComparisonNativePositiveBroadConsumers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000

def nativeBroadPhysicalTraceCoefficient (N A K R L : ℝ) : ℝ :=
  5184*A*K*R*(Real.log N)^2*L+
    (66+64*L+65536*(1+L)^2)*216*A*K*R^2*(Real.log N)^2

theorem native_broad_slice_mass_bounds (m : NativeBandModel) (g : NativeBroadSliceGeometry m) :
    0 < (∫r in Ioo g.a g.b,deriv m.alpha.val.val r) ∧
      (∫r in Ioo g.a g.b,deriv m.alpha.val.val r) ≤ 4*g.scale ∧
      (∫r in Ioo g.a g.b,deriv m.alpha.val.val r) ≤ 1 := by
  have he := native_actual_inverse_slice_mass m (m.hag.le.trans g.haGroup)
    g.hab.le (g.hbGroup.trans m.hzg)
  have ha := (m.alpha.val.property.1 g.a).1
  refine ⟨m.hU.trans_le (g.hscale.trans g.hmass),?_,?_⟩
  · rw [he]
    linarith [g.hceilingMass.trans g.hcomparable]
  · rw [he]
    linarith [(m.alpha.val.property.1 g.b).2]

theorem native_broad_cap_width_le_D0 (m : NativeBandModel) (g : NativeBroadSliceGeometry m) :
    g.capZ-g.capA ≤ m.D0 := by
  let c : NativeActualCapInterval m := ⟨g.capA,g.capZ,g.ha,g.haz,g.hz,g.hnegative⟩
  have hc : g.capZ-g.capA ≤ nativeCapTravel m := actual_native_cap_travel m c
  have ht := (nativeCapTravel_pos m).le
  change g.capZ-g.capA ≤ 9*Real.log m.N*nativeCapTravel m
  nlinarith [m.hlog]

theorem actual_native_broad_physical_trace_error
    (m : NativeBandModel) (g : NativeBroadSliceGeometry m)
    (hraw : NativeBandRawMaster m)
    {cut K R : ℝ} (hcut : 0 < cut) (hsmall : 2*cut < m.U)
    (hleft : m.cutRadius ≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hlog : Real.log (1/cut) ≤ m.Lside)
    (hUeq : m.U=comparisonSmallMass m.N m.E)
    (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hstrength : m.N*m.groupStrength ≤ K*m.P) (hratio : g.scale ≤ R*m.rho) :
    let width := ∫r in Ioo g.a g.b,deriv m.alpha.val.val r
    let A := m.Ko^2+1+50*Real.log ((1+m.U)/m.U)
    (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
      3*nativeBroadPhysicalTraceCoefficient m.N A K R m.Lside*m.E+
      (244+192*m.Lside)*m.groupStrength*width*m.D0^2+
      96*m.groupStrength*width*m.reverse m.D0+48*m.groupStrength*cut := by
  dsimp only
  let width := ∫r in Ioo g.a g.b,deriv m.alpha.val.val r
  let loss := m.Ko^2+25*(1+g.scale/m.U)*Real.log ((1+m.U)/m.U)+1
  let A := m.Ko^2+1+50*Real.log ((1+m.U)/m.U)
  have hw := native_broad_slice_mass_bounds m g
  have hlogU : 0 ≤ Real.log ((1+m.U)/m.U) :=
    (Real.log_pos ((lt_div_iff₀ m.hU).mpr (by linarith))).le
  have hv : 0 < g.scale := m.hU.trans_le g.hscale
  have hU := m.hU
  have hloss : 0 ≤ loss := by dsimp [loss]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlossA : loss ≤ A*g.scale/m.U := comparison_broad_loss_normalized m.hU g.hscale
  have hside : Real.log (width/cut) ≤ m.Lside :=
    comparison_broad_side_log_le hw.1 hw.2.2 hcut hlog
  have ht := comparison_broad_weighted_trace_cost
    (zero_lt_one.trans_le m.hN) m.hE hUeq m.groupStrength_pos m.P_pos hv m.rho_pos
    hw.1.le hloss hA hK hR (show (0:ℝ) ≤ 4 by norm_num) m.hLside
    hstrength hlossA hratio hw.2.1 hside
  change m.groupStrength*(48*(108*loss*(Real.log m.N)^2/(m.P*m.rho)*Real.log (width/cut))+
    (66+64*m.Lside+65536*(1+m.Lside)^2)*(54*loss*(Real.log m.N)^2*width/(m.P*m.rho^2))) ≤
    _ at ht
  have ht' : m.groupStrength*(48*(108*loss*(Real.log m.N)^2/(m.P*m.rho)*Real.log (width/cut))+
    (66+64*m.Lside+65536*(1+m.Lside)^2)*(54*loss*(Real.log m.N)^2*width/(m.P*m.rho^2))) ≤
    nativeBroadPhysicalTraceCoefficient m.N A K R m.Lside*m.E := by
    convert ht using 1
    unfold nativeBroadPhysicalTraceCoefficient
    ring
  obtain ⟨s,hs⟩ := exists_nativeRawMasterRefinement m hraw
  have hthermal := actual_native_calibrated_positive_broad_slice_comparison_of_eventual_raw
    m s g hcut hsmall hleft hupper hlog hs
  dsimp only at hthermal
  have herr := actual_native_broad_slice_error_le_thermal m g
  have hcap := pow_le_pow_left₀ (sub_nonneg.mpr g.haz.le) (native_broad_cap_width_le_D0 m g) 2
  have hcapCost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcap (show 0 ≤ 16*m.groupStrength by have := m.groupStrength_pos; positivity)) hw.1.le
  have hmain := mul_le_mul_of_nonneg_left hthermal
    (show 0 ≤ 3*m.groupStrength by have := m.groupStrength_pos; positivity)
  unfold nativeConditionalLedgerBudget at hmain
  norm_num only [Nat.cast_one, mul_one] at hmain
  change (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
    3*nativeBroadPhysicalTraceCoefficient m.N A K R m.Lside*m.E+
    (244+192*m.Lside)*m.groupStrength*width*m.D0^2+
    96*m.groupStrength*width*m.reverse m.D0+48*m.groupStrength*cut
  dsimp only [width, loss] at ht' ⊢
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
