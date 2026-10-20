module

public import ComparisonActualHighOnlyBroadCapFiniteBudget
public import ComparisonActualHighOnlyBroadFilledTrace

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 36000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (cap : ShiftedCapInterval a P)

theorem cropped_thermal_le_budget
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ag zg l z v V K cut Q y Lside : ℝ} (hag : 0< ag) (hzg : zg≤1)
    (hl : cap.left≤ l) (hz : z≤ cap.right) (hlz : l< z) (hagL : ag≤ l) (hzG : z≤ zg)
    (hboundary : (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1))
    (hK : 1≤ K) (hUv : a.data.U≤ v) (hV : V∈Icc (0:ℝ) 1) (hVv : V≤ K*v)
    (hcal : a.data.d^3*a.data.L*a.data.U≤ a.data.E)
    (hAV : ∀r∈Ioo l z,a.alpha.val.val r≤ V) (hslice : v≤∫r in Ioo l z,deriv a.alpha.val.val r)
    (ell : ℕ) (hell : 2< ell) (hQ : 1≤ Q) (hY : a.xs+a.alpha.val.val z≤ y)
    (hLside : 0≤ Lside) (hcut : 0< cut) (hlogcut : Real.log (1/cut)≤ Lside)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (hw : 2*cut≤∫r in Ioo l z,deriv a.alpha.val.val r)
    (hwidths : ∀j,2*cut≤ physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) 0
      (cap.croppedRows l z (as j)))
    (hraw : ∀j,physicalRawRatio (n+1) ell (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) 0 a.xs
      (Measure.pi fun k=> gaussianReal 0 (a.shiftedNativeModel.q 0 k)) id measurable_id≤ Q) :
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg)
    let F:=(K+1)^2*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)
    let width:=∫r in Ioo l z,deriv a.alpha.val.val r
    let reverse:=a.canonicalMassDiameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
      ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
    (∫r in Ioo l z,deriv a.alpha.val.val r*a.shiftedNativeModel.thermal (a.alpha.val.val r))≤
      nativeConditionalLedgerBudget 1 width cut a.canonicalMassDiameter
        ((4*C*F/a.alpha.val.val l)*Real.log (width/cut))
        ((2*C*F/(a.alpha.val.val l)^2)*width) reverse Lside := by
  dsimp only
  let m:=a.shiftedNativeModel
  let J:=fun j=> cap.croppedRows l z (as j)
  let widths:=fun j=> physicalWindowMass (sampleClockSteps m.q 0 (as j)) 0 (J j)
  let width:=∫r in Ioo l z,deriv a.alpha.val.val r
  let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg)
  let F:=(K+1)^2*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)
  let VS:=(4*C*F/a.alpha.val.val l)*Real.log (width/cut)
  let TC:=(2*C*F/(a.alpha.val.val l)^2)*width
  let Cnode:=2*ClockTree.errorJetVariation 2 0 0*clockVariationBound (physicalFeatureCoordinateBound n) m.q
  let diam:=fun j=> a.canonicalMassDiameter+2*(mesh j*Cnode)
  let rev:=fun d : ℝ=> d^(((ell:ℝ)-2)/((ell:ℝ)-1))*((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  have hl0:=hag.trans_le hagL
  have hz1:=hzG.trans hzg
  have hdata j i (hi:i∈J j):=cap.croppedRows_data hl hz (as j) (ho j) i hi
  have hy : 0≤ y:=(add_nonneg a.hxs.le (a.alpha.val.property.1 z).1).trans hY
  have hCn : 0≤ Cnode:=mul_nonneg (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg (physicalFeatureCoordinateBound n) m.q
      (completedPathClock_monotone (n+1) m.hbf m.hhf))
  have htravel : 0< a.cavityCapTravel:=by
    unfold cavityCapTravel
    exact mul_pos (div_pos a.data.hL (Real.rpow_pos_of_pos a.data.hN _))
      (Real.log_pos ((one_lt_div a.data.hU).mpr (by linarith)))
  have hD0 : 0< a.canonicalMassDiameter:=mul_pos (by linarith : 0<9*Real.log a.data.N) htravel
  have hD j : 0≤ diam j:=add_nonneg hD0.le (mul_nonneg (by norm_num) (mul_nonneg (hm0 j) hCn))
  have hrev0 j : 0≤ rev (diam j):=
    mul_nonneg (Real.rpow_nonneg (hD j) _)
      (Real.rpow_nonneg (mul_nonneg (by positivity) (pow_nonneg hy ell)) _)
  have hdlim : Tendsto diam atTop (𝓝 a.canonicalMassDiameter):=by
    simpa only [diam,zero_mul,mul_zero,add_zero] using ((hlim.mul_const Cnode).const_mul 2).const_add a.canonicalMassDiameter
  have hrevlim : Tendsto (fun j=> rev (diam j)) atTop (𝓝 (rev a.canonicalMassDiameter)):=
    (hdlim.rpow_const (Or.inl hD0.ne')).mul_const _
  have hwlim:=cap.croppedRows_mass_tendsto hl0 hz1 hl hz as mesh ho he hm hm0 hlim
  have hdeflim:=cap.croppedRows_original_defect_tendsto hl0 hz1 hl hz as mesh ho he hm hm0 hlim
  let Cbudget:=66+64*Lside+65536*(1+Lside)^2
  have hCb : 0≤ Cbudget:=by dsimp only [Cbudget];positivity
  apply le_of_forall_pos_le_add
  intro t ht
  let err:=t/(48+Cbudget+1)
  have herr : 0< err:=div_pos ht (by linarith)
  have Hfilled:=cap.cropped_filled_eventually hN hlog hnd dphys e hag hzg hl hz hlz hagL hzG
    hboundary hK hUv hV hVv hcal hAV hslice as mesh ho he hm hm0 hlim hcut hw hwidths herr
  have Hupper : ∀ᶠj in atTop,m.selectedDefect (as j) (J j)≤
      nativeConditionalLedgerBudget 1 (widths j) cut (diam j) (VS+err) (TC+err) (rev (diam j)) Lside:=by
    filter_upwards [Hfilled] with j hj
    have hsideLog : Real.log (widths j/cut)≤ Lside:=by
      apply (Real.log_le_log (div_pos (by linarith [hwidths j]) hcut)
        (div_le_div_of_nonneg_right (physicalWindowMass_mem_Icc_one _
          (sampleClockSteps_ordered m.q _ (ho j)) _).2 hcut.le)).trans hlogcut
    have HH:=cap.cropped_conditional_finite_budget hN hlog hnd hboundary hl0 hz1 hlz.le hl hz
      dphys e (as j) (ho j) (he j) (hm j) (hm0 j) ell hell hY hcut hLside (hwidths j) hsideLog
    let Qj:=physicalRawRatio (n+1) ell (sampleClockSteps m.q 0 (as j)) 0 a.xs
      (Measure.pi fun k=> gaussianReal 0 (m.q 0 k)) id measurable_id
    have hQj : 0≤ Qj:=zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)
    have Hq:=pow_le_pow_left₀ (mul_nonneg (by norm_num) hQj)
      (mul_le_mul_of_nonneg_left (hraw j) (by norm_num : (0:ℝ)≤2)) (2*ell)
    have Hqprod:=mul_le_mul_of_nonneg_right Hq (pow_nonneg hy ell)
    have hEll : (0:ℝ)<(ell:ℝ)-1:=by
      have HE : (2:ℝ)< ell:=by exact_mod_cast hell
      linarith
    have HR:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hQj) _) (pow_nonneg hy ell))
      Hqprod (div_nonneg zero_le_one hEll.le))
      (Real.rpow_nonneg (hD j) (((ell:ℝ)-2)/((ell:ℝ)-1)))
    have hWj : 0≤ widths j:=(physicalWindowMass_mem_Icc_one _ (sampleClockSteps_ordered m.q _ (ho j)) _).1
    have HV:=mul_le_mul_of_nonneg_left hj.1 (by norm_num : (0:ℝ)≤48)
    have HT:=mul_le_mul_of_nonneg_left hj.2 hCb
    have Hrev:=mul_le_mul_of_nonneg_left HR (show 0≤32*widths j by positivity)
    unfold nativeConditionalLedgerBudget at HH ⊢
    dsimp only [Cbudget,VS,TC,diam,rev,widths,J,C,F,Qj,Cnode] at HV HT Hrev HH ⊢
    nlinarith only [HH,HV,HT,Hrev]
  have HlimUpper : Tendsto (fun j=> nativeConditionalLedgerBudget 1 (widths j) cut (diam j)
      (VS+err) (TC+err) (rev (diam j)) Lside) atTop
      (𝓝 (nativeConditionalLedgerBudget 1 width cut a.canonicalMassDiameter
        (VS+err) (TC+err) (rev a.canonicalMassDiameter) Lside)):=by
    unfold nativeConditionalLedgerBudget
    exact (((tendsto_const_nhds.add ((hwlim.const_mul _).mul (hdlim.pow 2))).add
      ((hwlim.const_mul 32).mul hrevlim)).add tendsto_const_nhds).add tendsto_const_nhds
  have Hlimit:=le_of_tendsto_of_tendsto hdeflim HlimUpper Hupper
  have Herr : (48+Cbudget)*err≤ t:=by
    dsimp only [err]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<48+Cbudget+1)).mpr
    nlinarith only [ht]
  unfold nativeConditionalLedgerBudget at Hlimit ⊢
  dsimp only [VS,TC,rev,C,F,Cbudget] at Hlimit Herr ⊢
  nlinarith only [Hlimit,Herr]

end ActualHighOnlyOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
