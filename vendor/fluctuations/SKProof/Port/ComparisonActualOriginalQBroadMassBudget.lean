module

public import ComparisonActualHighWallThetaZeroBroadThermalBudgetPositiveOrigin
public import SKProof.Port.ComparisonActualOriginalQOrdinaryGroupData
public import ComparisonActualHighWallThetaZeroRetainedRaw
public import SKProof.Port.OriginalQHighOnlyBridge
public import SKProof.Port.ComparisonActualOriginalQBroadAtDiameterFiniteBudget
public import SKProof.Port.ComparisonActualOriginalQBroadDensityLengthTrace
public import SKProof.Port.ComparisonActualOriginalQCanonicalMassBudgets

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 38000000
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
theorem constraint_length_calibration
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) :
    a.data.d^3*a.data.L*a.data.U ≤ a.data.E := by
  let N := a.data.N
  let d := a.data.d
  let E := a.data.E
  have hN : 0 < N := a.data.hN
  have hd : 0 < d := a.data.hd
  have hE : 0 < E := a.data.hE
  have hs : (Real.sqrt N)^2 = N := Real.sq_sqrt hN.le
  have hs3 : (Real.sqrt N)^3 = N*Real.sqrt N := by
    calc
      _ = (Real.sqrt N)^2*Real.sqrt N := by ring
      _ = _ := by rw [hs]
  have hL : a.data.L ≤ (comparisonLowerScale N E d)^3/d^2 := min_le_right _ _
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ d^3))
    a.data.hU.le
  have he : d^3*((comparisonLowerScale N E d)^3/d^2)*a.data.U =
      Real.sqrt N*E^2/d^2 := by
    change d^3*((comparisonLowerScale N E d)^3/d^2)*comparisonSmallMass N E = _
    unfold comparisonLowerScale comparisonSmallMass
    rw [div_pow,mul_pow,hs3]
    field_simp
  rw [he] at hmul
  have hupper : Real.sqrt N*E ≤ d^2 := a.hupper
  have hr : Real.sqrt N*E^2/d^2 ≤ E := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith
  exact hmul.trans hr

namespace ShiftedCapInterval
variable {a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (cap : ShiftedCapInterval a P)

private theorem cropped_moving_trace_y2
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ag zg l z v V K beta B : ℝ} (hag : a.data.rmin<ag) (hzg : zg≤1)
    (hl : cap.left≤l) (hz : z≤cap.right) (hlz : l<z)
    (hagL : ag≤l) (hzG : z≤zg)
    (hboundary : (P.H cap.left=0 ∨ cap.left=a.data.rmin) ∧ (P.H cap.right=0 ∨ cap.right=1))
    (hK : 1≤K) (hUv : a.data.U≤v) (hV : V∈Icc (0:ℝ) 1) (hVv : V≤K*v)
    (hcal : a.data.d^3*a.data.L*a.data.U≤a.data.E)
    (hAV : ∀r∈Ioo l z,a.alpha.val.val r≤V)
    (hslice : v≤∫r in Ioo l z,deriv a.alpha.val.val r)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (moving : ℕ→ℝ→ℝ) (hmeas : ∀j,Measurable (moving j))
    (hbeta : 0≤beta) (hbetaB : beta≤B) (hmoveB : ∀j r,‖moving j r‖≤B)
    (hsupport : ∀j,∀ᵐr,r∉Ioo ag zg→moving j r=0)
    (hcolumns : Tendsto (fun j=>∫r in Ioo ag zg,
      |moving j r-(Ioo l z).indicator (fun _=>beta) r|) atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg)
    ∀ᶠj in atTop,(∫r,deriv a.alpha.val.val r*moving j r
      ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      C*(K+1)^2*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)*
        (beta*(∫r in Ioo l z,deriv a.alpha.val.val r))+epsilon := by
  let m:=a.shiftedNativeModel
  let fixed:=(Ioo l z).indicator (fun _ : ℝ=>beta)
  let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg)
  let coef:=C*(K+1)^2*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)
  have hfixedM : Measurable fixed:=measurable_const.indicator measurableSet_Ioo
  have hfixedB r : ‖fixed r‖≤B:=by
    by_cases hr:r∈Ioo l z
    · rw [show fixed r=beta from indicator_of_mem hr _,Real.norm_eq_abs,abs_of_nonneg hbeta]
      exact hbetaB
    · rw [show fixed r=0 from indicator_of_notMem hr _,norm_zero]
      exact hbeta.trans hbetaB
  have herror:=m.inverse_weight_L1_tendsto hag hzg fixed hfixedM moving hmeas
    hfixedB hmoveB hcolumns
  have hfixedI:=m.radiusWeight_integrableOn hag hzg (Ioo ag zg) measurableSet_Ioo
    (Subset.refl _) fixed hfixedM hfixedB
  have hmoveI j:=m.radiusWeight_integrableOn hag hzg (Ioo ag zg) measurableSet_Ioo
    (Subset.refl _) (moving j) (hmeas j) (hmoveB j)
  have hsA : Ioo l z⊆Ioo ag zg:=Ioo_subset_Ioo hagL hzG
  have hcapA : Ioo l z⊆Ioo cap.left cap.right:=Ioo_subset_Ioo hl hz
  have hoverlap : max cap.left ag < min cap.right zg:=by
    have HH:=max_le hl hagL
    have HR:=le_min hz hzG
    exact HH.trans_lt (hlz.trans_le HR)
  let loss := (K+1)^2*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)
  have hv : 0<v := a.data.hU.trans_le hUv
  have hlogU : 0≤Real.log ((1+a.data.U)/a.data.U) :=
    Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
  have hloss : 0≤loss :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (by have hU:=a.data.hU; positivity)) hlogU
  have hMV : 0≤a.data.M V :=
    (comparisonCap_first_term (δ:=delta) a.data.hN a.data.hU a.data.hL a.data.hE
      a.data.hd.le hV.1).1.le
  have hprofile := comparisonCap_broad_length_multiplier_le (δ:=delta)
    a.data.hN a.data.hU a.data.hL a.data.hE a.data.hd.le hV.1 hK hUv hVv hcal
  change a.data.M V/v*(a.data.L/a.data.N^delta)≤(K+1)^2*(1+v/a.data.U) at hprofile
  have hprofile' : a.data.M V*(a.data.L/a.data.N^delta) ≤ (K+1)^2*(1+v/a.data.U)*v := by
    apply (div_le_iff₀ hv).mp
    convert hprofile using 1 <;> ring
  have hlength := (P.cap_interval_travel a cap.hleft cap.hlt.le cap.hright cap.negative).2.1
  have hdensity : a.data.M V*(cap.right-cap.left) ≤ loss*(∫r in Ioo l z,deriv a.alpha.val.val r) := by
    calc
      a.data.M V*(cap.right-cap.left) ≤
          a.data.M V*((a.data.L/a.data.N^delta)*Real.log ((1+a.data.U)/a.data.U)) :=
        mul_le_mul_of_nonneg_left hlength hMV
      _ = (a.data.M V*(a.data.L/a.data.N^delta))*Real.log ((1+a.data.U)/a.data.U) := by ring
      _ ≤ ((K+1)^2*(1+v/a.data.U)*v)*Real.log ((1+a.data.U)/a.data.U) :=
        mul_le_mul_of_nonneg_right hprofile' hlogU
      _ = loss*v := by dsimp only [loss]; ring
      _ ≤ loss*(∫r in Ioo l z,deriv a.alpha.val.val r) := mul_le_mul_of_nonneg_left hslice hloss
  have hfixed:=cap.broad_unit_trace_at_density_length hN hlog hnd dphys e (a.data.rmin_nonneg.trans_lt hag) hzg hoverlap hboundary
    hK hUv hV hVv hcal (Ioo l z) measurableSet_Ioo hcapA hsA hAV hslice
    hloss hdensity as mesh ho hend hmesh hmesh0 hlim
    (div_pos (show 0<epsilon/2 by positivity) (by linarith : 0<beta+1))
  dsimp only [loss] at hfixed
  filter_upwards [hfixed,(tendsto_order.mp herror).2 (epsilon/2) (by positivity)] with j hj he
  let mu:=m.radiusMeasure dphys e (as j) (ho j)
  have hdom : mu≤volume:=m.radiusMeasure_le_volume dphys e (as j) (ho j)
  have hfixedGlobal : (∫r in Ioo ag zg,deriv a.alpha.val.val r*fixed r∂mu)=
      ∫r,deriv a.alpha.val.val r*fixed r∂mu:=by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [show fixed r=0 from indicator_of_notMem (fun HH=>hr (hsA HH)) _,mul_zero]
  have hmoveGlobal : (∫r in Ioo ag zg,deriv a.alpha.val.val r*moving j r∂mu)=
      ∫r,deriv a.alpha.val.val r*moving j r∂mu:=by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [ae_mono hdom (hsupport j)] with r hr hrd
    rw [hr hrd,mul_zero]
  have H:=dominated_setIntegral_difference_le (Ioo ag zg) (Ioo ag zg) (Subset.refl _) mu hdom
    (fun r=>deriv a.alpha.val.val r*fixed r) (fun r=>deriv a.alpha.val.val r*moving j r)
    hfixedI (hmoveI j)
  rw [hfixedGlobal,hmoveGlobal] at H
  have hfixedEq : (∫r,deriv a.alpha.val.val r*fixed r∂mu)=
      beta*(∫r in Ioo l z,deriv a.alpha.val.val r∂mu):=by
    have heq : (fun r=>deriv a.alpha.val.val r*fixed r)=
        (Ioo l z).indicator (fun r=>beta*deriv a.alpha.val.val r):=by
      funext r
      by_cases hr:r∈Ioo l z <;> simp [fixed,hr,mul_comm]
    rw [heq,integral_indicator measurableSet_Ioo,integral_const_mul]
  have Hj:=mul_le_mul_of_nonneg_left hj hbeta
  have herr : beta*((epsilon/2)/(beta+1))≤epsilon/2:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<beta+1)).mpr
    nlinarith
  rw [hfixedEq] at H
  have HA:=le_abs_self ((∫r,deriv a.alpha.val.val r*moving j r∂mu)-
    beta*(∫r in Ioo l z,deriv a.alpha.val.val r∂mu))
  nlinarith

private theorem cropped_filled_y2
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ag zg l z v V K cut : ℝ} (hag : a.data.rmin<ag) (hzg : zg≤1)
    (hl : cap.left≤l) (hz : z≤cap.right) (hlz : l<z)
    (hagL : ag≤l) (hzG : z≤zg)
    (hboundary : (P.H cap.left=0 ∨ cap.left=a.data.rmin) ∧ (P.H cap.right=0 ∨ cap.right=1))
    (hK : 1≤K) (hUv : a.data.U≤v) (hV : V∈Icc (0:ℝ) 1) (hVv : V≤K*v)
    (hcal : a.data.d^3*a.data.L*a.data.U≤a.data.E)
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
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg)
    let F:=(K+1)^2*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)
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
  let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg)
  let F:=(K+1)^2*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)
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
  have hC0 : 0≤C:=div_nonneg (by positivity) (mul_nonneg (by positivity) (laplaceComparisonStrength_pos a.data.d a.hlam zg).le)
  have hF0 : 0≤F:=by
    have Hlog : 0≤Real.log ((1+a.data.U)/a.data.U):=
      Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
    have hv:=a.data.hU.trans_le hUv
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (by have hu:=a.data.hU;positivity)) Hlog
  have hdata j i (hi:i∈J j):=cap.croppedRows_data hl hz (as j) (ho j) i hi
  have hsideL1:=cap.croppedRows_side_L1 hl0 hz1 hl hz as mesh ho he hm hm0 hlim
    hag.le hzg hcut hw hwidths
  have hbinary:=m.binary_column_L1_of_support_eventually as ho (fun _=>1) J (fun _ _=>(0:Fin 1))
    (fun j i hi=>(hdata j i hi).1) (Ioo l z)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (a.data.rmin_nonneg.trans hag.le) hzg)
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
  have Hs:=cropped_moving_trace_y2 cap hN hlog hnd dphys e hag hzg hl hz hlz hagL hzG
    hboundary hK hUv hV hVv hcal hAV hslice as mesh ho he hm hm0 hlim
    moving (fun j=>m.unitColumn_measurable _ _ _ _) hbeta hbetaB hmoveB hsMove hsideL1
    (epsilon:=errS) (by dsimp only [errS];positivity)
  have Hc:=cropped_moving_trace_y2 cap hN hlog hnd dphys e hag hzg hl hz hlz hagL hzG
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

private theorem cropped_thermal_y2
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ag zg l z v V K cut Q y Lside : ℝ} (hag : a.data.rmin< ag) (hzg : zg≤1)
    (hl : cap.left≤ l) (hz : z≤ cap.right) (hlz : l< z) (hagL : ag≤ l) (hzG : z≤ zg)
    (hboundary : (P.H cap.left=0 ∨ cap.left=a.data.rmin) ∧ (P.H cap.right=0 ∨ cap.right=1))
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
  have Hfilled:=cropped_filled_y2 cap hN hlog hnd dphys e hag hzg hl hz hlz hagL hzG
    hboundary hK hUv hV hVv hcal hAV hslice as mesh ho he hm hm0 hlim hcut hw hwidths herr
  have Hupper : ∀ᶠj in atTop,m.selectedDefect (as j) (J j)≤
      nativeConditionalLedgerBudget 1 (widths j) cut (diam j) (VS+err) (TC+err) (rev (diam j)) Lside:=by
    filter_upwards [Hfilled] with j hj
    have hsideLog : Real.log (widths j/cut)≤ Lside:=by
      apply (Real.log_le_log (div_pos (by linarith [hwidths j]) hcut)
        (div_le_div_of_nonneg_right (physicalWindowMass_mem_Icc_one _
          (sampleClockSteps_ordered m.q _ (ho j)) _).2 hcut.le)).trans hlogcut
    have hcap : ∀s∈Ioo cap.left cap.right,∀t∈Ioo cap.left cap.right,s≤t→
        a.radiusS t-a.radiusS s≤a.canonicalMassDiameter := by
      intro s hs t ht hst
      rcases hboundary.1 with hc | hw
      · exact (cap.interior_radiusS_increment hN hlog hnd hc hboundary.2 hs ht hst).trans
          (mul_le_mul_of_nonneg_left cap.travel (show 0≤9*Real.log a.data.N by linarith))
      · have hS0 := (a.radius_moments.2.2 s ⟨cap.hleft.trans hs.1.le,hs.2.le.trans cap.hright⟩).1.1
        have hSt : a.radiusS t≤cap.right := by
          rcases hboundary.2 with hc | hr
          · exact P.cap_point_mean_le_right cap.hleft cap.hright ht hc (cap.negative t ht)
          · rw [hr]
            exact (a.radius_moments.2.2 t ⟨cap.hleft.trans ht.1.le,ht.2.le.trans cap.hright⟩).1.2
        have htravel := cap.travel
        rw [hw] at htravel
        have horigin := a.rmin_le_cavityCapTravel
        have hprice := mul_le_mul_of_nonneg_right
          (show (2:ℝ)≤9*Real.log a.data.N by linarith) a.cavityCapTravel_nonneg
        change _≤9*Real.log a.data.N*a.cavityCapTravel
        linarith only [hS0,hSt,htravel,horigin,hprice]
    have HH:=cap.cropped_conditional_finite_budget_at_diameter hD0.le hcap hN hlog hnd hboundary
      (a.data.rmin_nonneg.trans_lt hl0) hz1 hlz.le hl hz
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

end ShiftedCapInterval

end ActualThetaZeroOverlapMinimum
open ActualThetaZeroOverlapMinimum

theorem eventually_actual_broad_mass_budget_original_q
    (ell : ℕ) (hell : 2< ell) (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta<3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤ Az) (hC0 : 0 < C0) (hCt : 0≤ Ct) :
    ∃Q : ℝ,1≤ Q ∧ ∀ᶠn in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.data.s≤1/4 → a.data.s≤ a.xs → ∀P : a.Potential,
      ∀cap : ShiftedCapInterval a P,∀l z v Lside cut : ℝ,
      (P.H cap.left=0 ∨ cap.left=a.data.rmin) ∧ (P.H cap.right=0 ∨ cap.right=1) →
      0< l → l< z → cap.left≤ l → z≤ cap.right →
      0< v → v≤1 → a.data.s< v/2 → a.data.U≤ v →
      v/2≤ a.alpha.val.val l → a.alpha.val.val z≤ min (4*v) 1 →
      v≤∫r in Ioo l z,deriv a.alpha.val.val r →
      0≤ Lside → 0 < cut → 2*cut< a.data.U → Real.log (1/cut)≤ Lside →
      (∫r in Ioo l z,deriv a.alpha.val.val r*a.shiftedNativeModel.thermal (a.alpha.val.val r))≤
        a.canonicalBroadMassBudget ell Q Lside cut v (∫r in Ioo l z,deriv a.alpha.val.val r) := by
  have horder : ell-1+1=ell:=by omega
  obtain ⟨Craw,hCraw,Hraw⟩:=eventually_actual_theta_zero_original_boundary_raw (ell-1) Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  let Q:=max 1 (Real.sqrt (2*Craw))
  have hQ : 1≤ Q:=le_max_left _ _
  have Hdepth:=(tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  refine ⟨Q,hQ,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hraw,Hdepth,Hlog] with n hnRaw hnDepth hnLog
  intro a hs hsxs P cap l z v Lside cut hcontacts hl0 hlz hclL hzcap hv hv1 hsV hUv hlmass hzmass
    hwidth hLside hcut hcutU hlogcut
  have hz1:=hzcap.trans cap.hright
  have hN : 1≤ a.data.N:=by dsimp only [ActualHighWallData.N];exact_mod_cast Nat.succ_pos n
  have hlog : 1≤ Real.log a.data.N:=hnLog
  have hnd : 1/a.data.N≤ a.data.d:=by
    have HH:=hnDepth a.data.E a.data.d a.data.hE a.data.hd a.hlower
    have HS : comparisonLowerScale (n+1:ℕ) a.data.E a.data.d≤ a.data.d:=by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.data.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact HH.trans HS
  have hlOrigin : a.data.rmin<l := by
    by_contra H
    have Hmass := a.alpha.val.property.2 (le_of_not_gt H)
    rw [a.alpha.property.1] at Hmass
    linarith only [hlmass,hsV,Hmass]
  let m:=a.shiftedNativeModel
  let zg:=m.R (min (16*v) 1)
  have hzg : zg≤1:=(m.R_bounds _).2
  have hzG : z≤ zg:=by
    calc
      z=m.R (a.alpha.val.val z):=(m.R_inverse ⟨hlOrigin.le.trans hlz.le,hz1⟩).symm
      _≤ m.R (min (16*v) 1):=m.R_monotone (hzmass.trans (min_le_min_right 1 (by nlinarith)))
  have hV : min (4*v) 1∈Icc (0:ℝ) 1:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have hAV r (hr:r∈Ioo l z) : a.alpha.val.val r≤ min (4*v) 1:=
    (a.alpha.val.property.2 hr.2.le).trans hzmass
  have hY : a.xs+a.alpha.val.val z≤ a.canonicalMassHeight v:=by
    have HH:=hzmass.trans (min_le_min_right 1 (by nlinarith : (4:ℝ)*v≤16*v))
    dsimp only [canonicalMassHeight]
    linarith only [HH]
  obtain ⟨us,hus,_,_,hraw⟩:=hnRaw a (⟨1,by norm_num⟩:PositiveMass) le_rfl [] (by simp)
  let grid:=fun j=> finiteCutMasses us j
  let mesh:=fun j : ℕ=>((j+1:ℕ):ℝ)⁻¹
  have ho j : MassOrdered 0 (grid j):=finiteCutMasses_ordered us hus j
  have he j : partitionEnd 0 (grid j)=1:=finiteCutMasses_end us hus j
  have hmesh j : PartitionMesh (mesh j) 0 (grid j):=finiteCutMasses_mesh us hus j
  have hm0 j : 0 ≤ mesh j:=by positivity
  have hlim : Tendsto mesh atTop (𝓝 0):=uniformMasses_mesh_tendsto
  have Hwidth:=cap.croppedRows_mass_tendsto hlOrigin hz1 hclL hzcap grid mesh ho he hmesh hm0 hlim
  have HwidthCut : ∀ᶠj in atTop,2*cut≤ physicalWindowMass (sampleClockSteps m.q 0 (grid j)) 0
      (cap.croppedRows l z (grid j)):=Hwidth.eventually
    (eventually_ge_nhds (hcutU.trans_le (hUv.trans hwidth)))
  have HrawQ : ∀ᶠj in atTop,physicalRawRatio (n+1) ell (sampleClockSteps m.q 0 (grid j)) 0 a.xs
      (Measure.pi fun k=> gaussianReal 0 (m.q 0 k)) id measurable_id≤ Q:=by
    filter_upwards [hraw] with j hj
    dsimp only at hj
    rw [horder] at hj
    have Hsqrt:=Real.sq_sqrt (show 0≤2*Craw by positivity)
    have Hpos:=Real.sqrt_nonneg (2*Craw)
    apply le_trans _ (le_max_right 1 (Real.sqrt (2*Craw)))
    nlinarith only [hj.1,Hsqrt,Hpos]
  obtain ⟨J0,hJ0⟩:=eventually_atTop.mp (HwidthCut.and HrawQ)
  have hshift : StrictMono (fun j : ℕ=> j+J0):=fun i j hij=> Nat.add_lt_add_right hij J0
  have HH:=ShiftedCapInterval.cropped_thermal_y2 cap hN hlog hnd
    (Fintype.card (FeatureIndex (n+1))-1) (cavityCanonicalFeatureEquiv n)
    hlOrigin hzg hclL hzcap hlz le_rfl hzG hcontacts (by norm_num : (1:ℝ)≤4) hUv hV
    (min_le_left _ _) a.constraint_length_calibration hAV hwidth ell hell hQ hY hLside hcut hlogcut
    (fun j=> grid (j+J0)) (fun j=> mesh (j+J0)) (fun j=> ho (j+J0)) (fun j=> he (j+J0))
    (fun j=> hmesh (j+J0)) (fun j=> hm0 (j+J0)) (hlim.comp hshift.tendsto_atTop)
    (hcutU.le.trans (hUv.trans hwidth)) (fun j=>(hJ0 (j+J0) (by omega)).1)
    (fun j=>(hJ0 (j+J0) (by omega)).2)
  let width:=∫r in Ioo l z,deriv a.alpha.val.val r
  let power:=a.canonicalMassPower v
  let F:=25*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)
  let loss:=(32:ℝ)^2+F+1
  have hP : 0< power:=by
    dsimp only [power,canonicalMassPower]
    exact mul_pos a.data.hN (laplaceComparisonStrength_pos a.data.d a.hlam _)
  have hrho : 0< a.alpha.val.val l:=m.profile_pos hlOrigin (hlz.le.trans hz1)
  have hV4 : 0< v/4:=by positivity
  have hRho : v/4≤ a.alpha.val.val l:=by linarith
  have hF : 0≤ F:=by
    have HL : 0 ≤ Real.log ((1+a.data.U)/a.data.U):=
      Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
    have HU := a.data.hU
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) HL
  have hloss : 0≤ loss:=by dsimp only [loss];positivity
  have hwidth0 : 0≤ width:=hv.le.trans hwidth
  have hlog0 : 0≤ Real.log (width/cut):=Real.log_nonneg
    ((one_le_div hcut).mpr (by have HH:=hcutU.le.trans (hUv.trans hwidth);linarith))
  have HVS : 108*F*(Real.log a.data.N)^2/(power*a.alpha.val.val l)*Real.log (width/cut)≤
      108*loss*(Real.log a.data.N)^2/(power*(v/4))*Real.log (width/cut):=by
    apply mul_le_mul_of_nonneg_right _ hlog0
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (show F≤ loss by dsimp only [loss];linarith) (by norm_num : (0:ℝ)≤108)) (sq_nonneg _))
      (mul_nonneg hP.le hrho.le)).trans
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hP hV4)
      (mul_le_mul_of_nonneg_left hRho hP.le)
  have HTC : 54*F*(Real.log a.data.N)^2*width/(power*(a.alpha.val.val l)^2)≤
      54*loss*(Real.log a.data.N)^2*width/(power*(v/4)^2):=by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show F≤ loss by dsimp only [loss];linarith)
        (by norm_num : (0:ℝ)≤54)) (sq_nonneg _)) hwidth0) (mul_nonneg hP.le (sq_nonneg _))).trans
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hP (sq_pos_of_pos hV4))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV4.le hRho 2) hP.le)
  have Hbcoeff : 0≤66+64*Lside+65536*(1+Lside)^2:=by positivity
  have HV:=mul_le_mul_of_nonneg_left HVS (by norm_num : (0:ℝ)≤48)
  have HT:=mul_le_mul_of_nonneg_left HTC Hbcoeff
  apply HH.trans
  have HVeq : 4*(27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg))*
      ((4+1)^2*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U))/a.alpha.val.val l*Real.log (width/cut)=
      108*F*(Real.log a.data.N)^2/(power*a.alpha.val.val l)*Real.log (width/cut) := by
    dsimp only [F,power,canonicalMassPower,zg,m,ActualHighWallData.N]
    rw [show a.shiftedNativeModel.R=a.sweepRadius from rfl]
    push_cast
    field_simp
    <;> ring
  have HTeq : 2*(27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg))*
      ((4+1)^2*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U))/(a.alpha.val.val l)^2*width=
      54*F*(Real.log a.data.N)^2*width/(power*(a.alpha.val.val l)^2) := by
    dsimp only [F,power,canonicalMassPower,zg,m,ActualHighWallData.N]
    rw [show a.shiftedNativeModel.R=a.sweepRadius from rfl]
    push_cast
    field_simp
    <;> ring
  rw [HVeq,HTeq]
  unfold canonicalBroadMassBudget nativeConditionalLedgerBudget
  dsimp only [F,loss,power,width,canonicalMassPower,canonicalMassReverse,canonicalMassHeight] at HV HT ⊢
  nlinarith only [HV,HT]

end OAI.SKFluctuations.LaplaceWindowFormalization
