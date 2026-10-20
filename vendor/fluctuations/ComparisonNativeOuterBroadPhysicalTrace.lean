module

public import ComparisonNativeInnerBroadPhysicalRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000

theorem actual_native_outer_broad_physical_trace_error
    (m : NativeBandModel) (g : NativeBroadSliceGeometry m)
    (hraw : NativeBandRawMaster m)
    {cl cu Az z0 : ℝ} (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hz0 : z0∈Icc (0:ℝ) 1) (hzxs : z0 ≤ Az*m.xs)
    (htravel : nativeCapTravel m ≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs ≤ m.alpha.val.val g.capZ)
    {cut K R : ℝ} (hcut : 0 < cut) (hsmall : 2*cut < m.U)
    (hleft : m.cutRadius ≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hlog : Real.log (1/cut) ≤ m.Lside)
    (hUeq : m.U=comparisonSmallMass m.N m.E)
    (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hstrength : m.N*m.groupStrength ≤ K*m.P) (hratio : g.scale ≤ R*m.rho) :
    let width := ∫r in Ioo g.a g.b,deriv m.alpha.val.val r
    let A := m.Ko^2+1+50*Real.log ((1+m.U)/m.U)
    let D := nativeOuterBroadDiameter m g cl cu
    (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
      3*nativeBroadPhysicalTraceCoefficient m.N A K R m.Lside*m.E+
      (244+192*m.Lside)*m.groupStrength*width*D^2+
      96*m.groupStrength*width*m.reverse D+48*m.groupStrength*cut := by
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
  have herr := actual_native_positive_outer_broad_slice_error_bound m s g
    hcl hcu hAz hz0 hzxs htravel hregular houter hcut hsmall hleft hupper hlog hs
  dsimp only at herr
  have hDp := nativeOuterBroadDiameter_pos m g hcl hcu
  have htpos : 0 ≤ nativeOuterBroadTravel m g cl cu := by
    have hh := (mul_pos_iff_of_pos_left (show 0 < 9*Real.log m.N by linarith [m.hlog])).mp hDp
    exact hh.le
  have hcap : nativeOuterBroadTravel m g cl cu ≤ nativeOuterBroadDiameter m g cl cu := by
    change _ ≤ 9*Real.log m.N*nativeOuterBroadTravel m g cl cu
    nlinarith [m.hlog]
  have hcap2 := pow_le_pow_left₀ htpos hcap 2
  have hcapCost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcap2 (show 0 ≤ 16*m.groupStrength by have := m.groupStrength_pos; positivity)) hw.1.le
  unfold nativeConditionalLedgerBudget at herr
  norm_num only [Nat.cast_one,mul_one] at herr
  dsimp only [width,loss] at ht' ⊢
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
