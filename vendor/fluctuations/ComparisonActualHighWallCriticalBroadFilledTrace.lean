module

public import ComparisonActualHighWallCriticalBroadMovingTrace

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (cap : ShiftedCapInterval a P)

theorem cropped_filled_eventually
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ag zg l z v V K cut : ℝ} (hag : a.data.rmin<ag) (hzg : zg≤1)
    (hl : cap.left≤l) (hz : z≤cap.right) (hlz : l<z)
    (hagL : ag≤l) (hzG : z≤zg)
    (hboundary : (P.H cap.left=0 ∨ cap.left=a.data.rmin) ∧ (P.H cap.right=0 ∨ cap.right=1))
    (hK : 1≤K) (hUv : (comparisonSmallMass a.data.N a.data.E)≤v) (hV : V∈Icc (0:ℝ) 1) (hVv : V≤K*v)
    (hcal : a.data.d^3*(comparisonConstraintLength a.data.N a.data.E a.data.d)*(comparisonSmallMass a.data.N a.data.E)≤a.data.E)
    (hAV : ∀r∈Ioo l z,a.alpha.val.val r≤V)
    (hslice : v≤∫r in Ioo l z,deriv a.alpha.val.val r)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) (hcut : 0<cut)
    (hw : 2*cut≤∫r in Ioo l z,deriv a.alpha.val.val r)
    (hwidths : ∀j,2*cut≤physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) 0
      (cap.croppedRows l z (as j))) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    let m:=a.shiftedNativeModel
    let width:=∫r in Ioo l z,deriv a.alpha.val.val r
    let widths:=fun j=>physicalWindowMass (sampleClockSteps m.q 0 (as j)) 0 (cap.croppedRows l z (as j))
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d (a.data.d^2) zg)
    let F:=a.criticalBroadTraceLoss K v V
    ∀ᶠj in atTop,
      (2*(∫r,deriv a.alpha.val.val r*m.unitColumn (as j) (cap.croppedRows l z (as j)) (fun _=>(0:Fin 1))
        (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val) r
          ∂m.radiusMeasure dphys e (as j) (ho j))+4*mesh j/cut)/a.alpha.val.val l≤
        (4*C*F/a.alpha.val.val l)*Real.log (width/cut)+epsilon ∧
      (2*(∫r,deriv a.alpha.val.val r*m.unitColumn (as j) (cap.croppedRows l z (as j)) (fun _=>(0:Fin 1))
        (fun _=>1) r∂m.radiusMeasure dphys e (as j) (ho j))+2*mesh j)/(a.alpha.val.val l)^2≤
        (2*C*F/(a.alpha.val.val l)^2)*width+epsilon := by
  dsimp only
  let m:=a.shiftedNativeModel
  let width:=∫r in Ioo l z,deriv a.alpha.val.val r
  let J:=fun j=>cap.croppedRows l z (as j)
  let widths:=fun j=>physicalWindowMass (sampleClockSteps m.q 0 (as j)) 0 (J j)
  let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d (a.data.d^2) zg)
  let F:=a.criticalBroadTraceLoss K v V
  let beta:=sideSquareColumn (nativeBroadPoints width) cut width 0
  have hl0:=hag.trans_le hagL
  have hz1:=hzG.trans hzg
  have hl1:=hlz.le.trans hz1
  have hpos : 0<width:=by linarith [hw]
  have hW j : 0<widths j:=by linarith [hwidths j]
  have hpoint : ∀u:Fin 1,nativeBroadPoints width u.val<nativeBroadPoints width (u.val+1):=by
    intro u
    have hu : u.val=0:=by omega
    simpa only [hu,nativeBroadPoints,ite_true,show (1:ℕ)≠0 by omega,ite_false,Nat.zero_add] using hpos
  have hbeta : 0≤beta:=sideSquareColumn_nonneg _ hw _
  have hbetaB : beta≤2/cut:=by
    exact sideSquareColumn_le_two_inv (nativeBroadPoints width) 1 (δ:=cut) (width:=width)
      (by simp [nativeBroadPoints]) (by simp [nativeBroadPoints]) hcut hw hpoint 0
  have hmass : beta*width≤2*Real.log (width/cut):=by
    have HH:=sideSquareColumn_mass_sum_le (nativeBroadPoints width) 1 (δ:=cut) (width:=width)
      (by simp [nativeBroadPoints]) (by simp [nativeBroadPoints]) hcut hw hpoint
    simpa [beta, nativeBroadPoints, mul_comm] using HH
  have hC0 : 0≤C:=div_nonneg (by positivity) (mul_nonneg (by positivity) (laplaceComparisonStrength_pos a.data.d (sq_pos_of_pos a.data.hd) zg).le)
  have hF0 : 0≤F:=by
    have Hlog : 0≤Real.log ((1+(comparisonSmallMass a.data.N a.data.E))/(comparisonSmallMass a.data.N a.data.E)):=
      Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
    have hv:=a.data.hU.trans_le hUv
    have hMV : 0≤a.data.M V := (comparisonCap_first_term (δ:=delta) a.data.hN a.data.hU a.data.hL a.data.hE a.data.hd.le hV.1).1.le
    dsimp only [F,criticalBroadTraceLoss]
    exact add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (by have hu:=a.data.hU;positivity)) Hlog)
      (div_nonneg (mul_nonneg hMV a.data.hrbounds.1.le) hv.le)
  have hdata j i (hi:i∈J j):=cap.croppedRows_data hl hz (as j) (ho j) i hi
  have hsideL1:=cap.croppedRows_side_L1 hl0 hz1 hl hz as mesh ho he hm hm0 hlim
    hag.le hzg hcut hw hwidths
  have hbinary:=m.binary_column_L1_of_support_eventually as ho (fun _=>1) J (fun _ _=>(0:Fin 1))
    (fun j i hi=>(hdata j i hi).1) (Ioo l z)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (a.data.hrbounds.1.le.trans hag.le) hzg)
      (cap.croppedRows_support_ae hl0 hz1 hl hz as mesh ho he hm hm0 hlim))
  let moving:=fun j=>m.unitColumn (as j) (J j) (fun _=>(0:Fin 1))
    (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val)
  let mask:=fun j=>m.unitColumn (as j) (J j) (fun _=>(0:Fin 1)) (fun _=>1)
  have hmoveB j r : ‖moving j r‖≤2/cut:=by
    have HH:=m.unitColumn_side_bound (as j) (ho j) (J j) (fun _=>(0:Fin 1))
      (nativeBroadPoints (widths j)) (by simp [nativeBroadPoints]) (by simp [nativeBroadPoints])
      hcut (show 2*cut ≤ widths j from hwidths j) (fun u=>by
        have hu:u.val=0:=by omega
        simpa only [hu,nativeBroadPoints,ite_true,show (1:ℕ)≠0 by omega,ite_false,Nat.zero_add] using hW j) r
    change 0 ≤ moving j r ∧ moving j r ≤ 2/cut at HH
    simpa only [Real.norm_eq_abs,abs_of_nonneg HH.1] using HH.2
  have hmaskB j r : ‖mask j r‖≤1:=by
    rw [show mask j r=m.unitColumn (as j) (J j) (fun _=>(0:Fin 1)) (fun _=>1) r from rfl,
      m.unitColumn_binary_eq_support (as j) (ho j) (J j) _ (fun i hi=>(hdata j i hi).1)]
    simp only [Set.indicator_apply]
    split_ifs <;> norm_num
  have hsMove j : ∀ᵐr,r∉Ioo ag zg→moving j r=0:=
    m.unitColumn_support_band (as j) (J j) (fun _=>(0:Fin 1)) _
      (fun i hi=>hagL.trans (hdata j i hi).2.2.2.1)
      (fun i hi=>(hdata j i hi).2.2.2.2.1.trans hzG)
  have hsMask j : ∀ᵐr,r∉Ioo ag zg→mask j r=0:=
    m.unitColumn_support_band (as j) (J j) (fun _=>(0:Fin 1)) _
      (fun i hi=>hagL.trans (hdata j i hi).2.2.2.1)
      (fun i hi=>(hdata j i hi).2.2.2.2.1.trans hzG)
  have hrho : 0<a.alpha.val.val l:=m.profile_pos hl0 hl1
  let errS:=epsilon*a.alpha.val.val l/8
  let errC:=epsilon*(a.alpha.val.val l)^2/8
  have Hs:=cap.cropped_moving_trace_eventually hN hlog hnd dphys e hag hzg hl hz hlz hagL hzG
    hboundary hK hUv hV hVv hcal hAV hslice as mesh ho he hm hm0 hlim
    moving (fun j=>m.unitColumn_measurable _ _ _ _) hbeta hbetaB hmoveB hsMove hsideL1
    (epsilon:=errS) (by dsimp only [errS];positivity)
  have Hc:=cap.cropped_moving_trace_eventually hN hlog hnd dphys e hag hzg hl hz hlz hagL hzG
    hboundary hK hUv hV hVv hcal hAV hslice as mesh ho he hm hm0 hlim
    mask (fun j=>m.unitColumn_measurable _ _ _ _) (beta:=1) zero_le_one le_rfl hmaskB hsMask hbinary.2
    (epsilon:=errC) (by dsimp only [errC];positivity)
  have HM:=hlim.eventually (gt_mem_nhds (show 0 < min (epsilon*a.alpha.val.val l*cut/8)
      (epsilon*(a.alpha.val.val l)^2/8) by positivity))
  filter_upwards [Hs,Hc,HM] with j hs hc hmj
  have hmS:=hmj.le.trans (min_le_left _ _)
  have hmC:=hmj.le.trans (min_le_right _ _)
  have HP:=mul_le_mul_of_nonneg_left hmass (mul_nonneg hC0 hF0)
  have Hside : (∫r,deriv a.alpha.val.val r*moving j r∂m.radiusMeasure dphys e (as j) (ho j))≤
      2*C*F*Real.log (width/cut)+errS:=by
    apply hs.trans
    convert add_le_add_right HP errS using 1 <;> dsimp only [C,F,beta,width] <;> ring
  have HmS : 4*mesh j/cut≤epsilon*a.alpha.val.val l/2:=by
    apply (div_le_iff₀ hcut).mpr
    nlinarith only [hmS]
  constructor
  · apply (div_le_iff₀ hrho).mpr
    have HE : ((4*C*F/a.alpha.val.val l)*Real.log (width/cut)+epsilon)*a.alpha.val.val l=
        4*C*F*Real.log (width/cut)+epsilon*a.alpha.val.val l:=by field_simp
    rw [HE]
    dsimp only [errS,moving,m,J,widths] at Hside
    have Hpay : 0 ≤ epsilon*a.alpha.val.val l := by positivity
    linarith only [Hside,HmS,Hpay]
  · apply (div_le_iff₀ (sq_pos_of_pos hrho)).mpr
    have HE : ((2*C*F/(a.alpha.val.val l)^2)*width+epsilon)*(a.alpha.val.val l)^2=
        2*C*F*width+epsilon*(a.alpha.val.val l)^2:=by field_simp
    rw [HE]
    have Hunion : (∫ r,deriv a.alpha.val.val r*mask j r ∂m.radiusMeasure dphys e (as j) (ho j))
        ≤ C*F*width+errC := by
      convert hc using 1 <;> dsimp only [C,F,width,errC,mask] <;> ring
    dsimp only [errC,mask,m,J] at Hunion
    have Hpay : 0 ≤ epsilon*(a.alpha.val.val l)^2 := by positivity
    linarith only [Hunion,hmC,Hpay]

end ActualHighWallOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
