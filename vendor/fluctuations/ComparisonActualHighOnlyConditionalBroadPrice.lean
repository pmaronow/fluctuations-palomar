module

public import ComparisonActualHighOnlyConditionalOrdinaryPrice
public import ComparisonNativeInnerBroadPhysicalRates
public import ComparisonActualHighOnlyMassBudgetScale
public import ComparisonNativeInnerStrengthDistortion
public import ComparisonNativeOrdinaryPhysicalRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 24000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_actual_conditional_broad_budget_price_high_only
    (ell : ℕ) (hell : 2 < ell) (Q Cv : ℝ) (hQ : 1≤Q) (hCv : 0≤Cv)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0≤Az) (hC0 : 0 < C0)
    (horder : (delta+2)/((ell:ℝ)-1)≤delta) :
    ∀ᶠn:ℕ in atTop,∀a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.d≤1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1≤a.data.N → ∀v width:ℝ,0 < v → v≤1 → a.data.U≤v → v≤Cv*a.xs →
      0≤width → width≤4*v → width≤1 →
      3*a.lam*a.canonicalBroadMassBudget ell Q (10*Real.log a.data.N) (a.data.N^(-(10:ℝ))) v width+
        16*a.lam*a.canonicalMassDiameter^2*width≤a.data.N^(6*delta)*a.data.E := by
  let K:=max 1 ((Az+1/cl)*(1+16*Cv))
  let C:=1+16*Cv
  let Fcoef:=nativeBinScalePolynomial (108*32^2) (54*32^2) 10 64
  have hK:1≤K:=le_max_left _ _
  have hC:0≤C:=by dsimp [C];positivity
  have hsR:Tendsto (fun n:ℕ=>((n+1:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hbin:=hsR.eventually (comparison_log_loss_eventually (C:=Fcoef) (p:=4)
    (nativeBinScalePolynomial_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hdelta)
  have Hlog:=hsR.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  have HJ:=hsR.eventually (comparison_capLogFactor_eventually hdelta)
  have Hcore:=hsR.eventually (comparison_inner_error_core_eventually (Q:=Q) hdelta hC)
  have Hcut:=hsR.eventually (comparison_ordinary_cutoff_eventually (Q:=Q) (P0:=1) (V0:=16)
    (by norm_num) (by norm_num) (by norm_num : (3:ℝ)≤10))
  have HK:=hsR.eventually (comparison_log_loss_eventually (C:=K) (p:=0) (zero_le_one.trans hK) hdelta)
  have Htwo:=hsR.eventually (comparison_log_loss_eventually (C:=2) (p:=0) (by norm_num) hdelta)
  have Htrace:=hsR.eventually (native_broad_trace_coefficient_eventually (Ko:=32) (K:=K) (R:=4) (S:=10)
    hdelta (by norm_num) (zero_le_one.trans hK) (by norm_num) (by norm_num))
  have Hcoef:=hsR.eventually (comparison_log_loss_eventually (C:=(340+192*10)*K) (p:=1) (by positivity) hdelta)
  have Hthree:=hsR.eventually (comparison_log_loss_eventually (C:=3) (p:=0) (by norm_num) hdelta)
  filter_upwards [Hbin,Hlog,HJ,Hcore,Hcut,HK,Htwo,Htrace,Hcoef,Hthree,
    eventually_actual_minimum_physical_scalar_data_high_only hm hC0] with n hnBin hnLog hnJ hnCore hnCut hnK hnTwo hnTrace hnCoef hnThree hnScalar
  intro a hd1 hxs hyN v width hv hv1 hUv hvA hw hwidthBound hwidth1
  have hscalar:=hnScalar a hd1
  have hxs0:=a.hxs
  have hU0:=a.data.hU
  have hL0:=a.data.hL
  have hE0:=a.data.hE
  have hlam0:=a.hlam
  have hN0:=a.data.hN
  have hlogPos:0 < Real.log a.data.N:=by linarith
  have hN:1≤a.data.N:=by exact_mod_cast Nat.succ_pos n
  let P:=a.canonicalMassPower v
  let Y:=a.canonicalMassHeight v
  let Dm:=a.canonicalMassDiameter
  let J:=9*Real.log a.data.N*Real.log ((1+a.data.U)/a.data.U)/a.data.N^delta
  let F:=nativeBinScaleLoss (10*Real.log a.data.N) (108*32^2*(Real.log a.data.N)^2)
    (54*32^2*(Real.log a.data.N)^2) (16*v) (v/4)
  have hP:0 < P:=a.canonical_mass_power_pos v
  have hY:0 < Y:=by dsimp [Y,canonicalMassHeight];positivity
  have hYbound:Y≤C*a.xs:=a.canonical_mass_height_le hCv hvA
  have hY_N:Y≤a.data.N:=by dsimp [Y,canonicalMassHeight];linarith [min_le_right (16*v) 1]
  have hV_A:16*v≤C*a.xs:=by dsimp [C];nlinarith only [hvA,a.hxs]
  have hJ:0≤J:=by
    have H:0≤Real.log ((1+a.data.U)/a.data.U):=Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
    dsimp [J];positivity
  have hJ1:J≤1:=hnJ a.data.U a.data.hU hscalar.2.2.2.2.1 hscalar.2.2.2.1
  have hD:0 < Dm:=by
    have H:0 < Real.log ((1+a.data.U)/a.data.U):=Real.log_pos ((one_lt_div a.data.hU).mpr (by linarith))
    dsimp [Dm,canonicalMassDiameter,cavityCapTravel];positivity
  have hDJ:Dm=J*a.data.L:=by dsimp [Dm,canonicalMassDiameter,cavityCapTravel,J];ring
  have hF:0≤F:=by dsimp [F,nativeBinScaleLoss];positivity
  have hFpoly:F≤Fcoef*(Real.log a.data.N)^4:=by
    apply nativeBinScaleLoss_le_log_polynomial hnLog (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      le_rfl le_rfl le_rfl
    field_simp
    norm_num
  have hFpow:F≤a.data.N^delta:=hFpoly.trans (by simpa only [Real.rpow_natCast,Real.rpow_ofNat] using hnBin)
  have hStrength:a.data.N*(a.data.N^(-delta)*a.lam)≤K*P:=
    a.canonical_conditional_inner_strength_high_only hdelta.le hcl hAz hCv hxs hv hvA
  have hratio:Y/Dm≤a.data.N^(delta+2):=comparison_physical_reverse_ratio hN hnLog a.data.hU
    hscalar.2.2.2.2.1 hscalar.2.2.2.2.2.2.2.1 hY.le hY_N
  have hprice:=comparison_inner_ledger_with_strength_distortion hell hN a.data.hE a.hlam hP hK hStrength
    (show comparisonSmallMass a.data.N a.data.E≤16*v by change a.data.U≤16*v;linarith)
    (hxs ▸ hV_A) hY (hxs ▸ hYbound) hD hQ hC hJ a.data.hL.le (min_le_left _ _)
    (hxs ▸ hscalar.2.2.2.2.2.1) hDJ.le hratio horder
  have hCore:=hnCore a.data.E F J delta a.data.hE.le hF hFpow hJ hJ1 le_rfl
  have hCoreK:=mul_le_mul_of_nonneg_left hCore (zero_le_one.trans hK)
  have hPN:P≤a.data.N:=by
    have H:laplaceComparisonStrength a.data.d a.lam (a.R (min (16*v) 1))≤1:=
      (laplaceComparisonStrength_le _ a.hlam.le _).trans (by nlinarith [a.hld,a.data.hd,hd1])
    exact (mul_le_mul_of_nonneg_left H a.data.hN.le).trans_eq (mul_one _)
  have hCut:=hnCut P Y (16*v) a.lam a.data.E hP.le (by simpa only [one_mul] using hPN) hY.le hY_N (by positivity)
    (by linarith) a.hlam.le (by nlinarith [a.hld,a.data.hd,hd1]) hscalar.2.1

  let L:=10*Real.log a.data.N
  let A:=32^2+1+50*Real.log ((1+a.data.U)/a.data.U)
  let loss:=32^2+25*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)+1
  let Rm:=a.canonicalMassReverse ell Q v
  have hL:0≤L:=by dsimp [L];positivity
  have hLoss:0≤loss:=by
    have HL:0≤Real.log ((1+a.data.U)/a.data.U):=Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
    dsimp [loss];positivity
  have hA:0≤A:=by
    have HL:0≤Real.log ((1+a.data.U)/a.data.U):=Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
    dsimp [A];positivity
  have hNorm:loss≤A*v/a.data.U:=comparison_broad_loss_normalized a.data.hU hUv
  have hstrength':a.data.N*a.lam≤(K*a.data.N^delta)*P:=by
    have H:=mul_le_mul_of_nonneg_left hStrength (Real.rpow_nonneg a.data.hN.le delta)
    have he:a.data.N^delta*(a.data.N*(a.data.N^(-delta)*a.lam))=a.data.N*a.lam:=by
      rw [Real.rpow_neg a.data.hN.le];field_simp
    rw [he] at H
    nlinarith only [H]
  have hSideLog:Real.log (width/a.data.N^(-(10:ℝ)))≤L:=by
    by_cases hwidth:0<width
    · exact (comparison_broad_side_log_le hwidth hwidth1 (Real.rpow_pos_of_pos a.data.hN _)
        (by rw [(comparison_physical_cutoff_log (C:=10) a.data.hN).2])).trans_eq rfl
    · have hz:width=0:=le_antisymm (le_of_not_gt hwidth) hw
      rw [hz,zero_div,Real.log_zero]
      exact hL
  have htrace:=comparison_broad_weighted_trace_cost a.data.hN a.data.hE rfl a.hlam hP hv
    (show 0<v/4 by positivity) hw hLoss hA (show 0≤K*a.data.N^delta by positivity)
    (by norm_num : (0:ℝ)≤4) (by norm_num : (0:ℝ)≤4) hL hstrength' hNorm
    (by linarith : v≤4*(v/4)) hwidthBound hSideLog
  have htrace':a.lam*(48*(108*loss*(Real.log a.data.N)^2/(P*(v/4))*Real.log (width/a.data.N^(-(10:ℝ))))+
      (66+64*L+65536*(1+L)^2)*(54*loss*(Real.log a.data.N)^2*width/(P*(v/4)^2)))≤
      nativeBroadPhysicalTraceCoefficient a.data.N A (K*a.data.N^delta) 4 L*a.data.E:=by
    convert htrace using 1
    unfold nativeBroadPhysicalTraceCoefficient
    ring
  have htraceCoef:=hnTrace a.data.U 32 L (K*a.data.N^delta) a.data.hU hscalar.2.2.2.2.1
    hscalar.2.2.2.1 (by norm_num) le_rfl hL le_rfl (by positivity) le_rfl
  have htraceSaved:=mul_le_mul_of_nonneg_right htraceCoef a.data.hE.le
  have hRnonneg:0≤Rm:=by dsimp [Rm,canonicalMassReverse];positivity
  have hnoise:0≤2*((Q^2*Y)/(P*(16*v)^2))^((2:ℝ)/3)+3/(P*(16*v)^2):=by positivity
  have hwidthBig:width≤16*v:=by linarith only [hwidthBound,hv]
  have hRem:a.lam*width*(Dm^2+Rm)≤K*comparisonInnerPhysicalCore a.data.N delta a.data.E Q C J delta:=by
    have H1:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidthBig a.hlam.le)
      (add_nonneg (sq_nonneg Dm) hRnonneg)
    have H2:=mul_nonneg (show 0≤a.lam*(16*v) by positivity) hnoise
    dsimp only [Rm,canonicalMassReverse,comparisonReverseMoment,P,Y,Dm] at H1 H2 hprice ⊢
    nlinarith only [H1,H2,hprice]
  let F1:=(340+192*L)*K/3
  have hF1:0≤F1:=by dsimp [F1];positivity
  have hF1Bound:F1≤a.data.N^delta:=by
    have H:(340+192*L)*K≤((340+192*10)*K)*Real.log a.data.N:=by
      dsimp only [L]
      have HH:=mul_le_mul_of_nonneg_right hnLog (show 0≤340*K by positivity)
      nlinarith only [HH]
    have Hcoeff:((340+192*10)*K)*Real.log a.data.N≤a.data.N^delta:=by simpa only [Real.rpow_one] using hnCoef
    have HP:0≤a.data.N^delta:=Real.rpow_nonneg a.data.hN.le _
    dsimp [F1]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr
    nlinarith only [H,Hcoeff,HP]
  have hCore:=hnCore a.data.E F1 J delta a.data.hE.le hF1 hF1Bound hJ hJ1 le_rfl
  have hDiam:=mul_le_mul_of_nonneg_left hRem (show 0≤340+192*L by positivity)
  have hDnonneg:0≤16*J^2*C*a.data.N^(2*delta)*a.data.E:=by positivity
  have hcutFactor:0≤((Q^2*Y)^2*P*(16*v)^2)^((1:ℝ)/3):=Real.rpow_nonneg (by positivity) _
  have hCutSmall:48*a.lam*a.data.N^(-(10:ℝ))≤a.data.E:=by
    have HP:0≤a.lam*a.data.N^(-(10:ℝ)):=by positivity
    have Hcost:54*( ((Q^2*Y)^2*P*(16*v)^2)^((1:ℝ)/3)+2)*(a.lam*a.data.N^(-(10:ℝ)))≤a.data.E:=by
      convert hCut using 1 <;> ring
    have Hprod:=mul_le_mul_of_nonneg_right (show 2≤((Q^2*Y)^2*P*(16*v)^2)^((1:ℝ)/3)+2 by linarith) HP
    nlinarith only [Hcost,Hprod,HP]
  have hRemDrop:a.lam*((244+192*L)*width*Dm^2+96*width*Rm)≤(340+192*L)*(a.lam*width*(Dm^2+Rm)):=by
    have HD0:0≤a.lam*width*Dm^2:=by positivity
    have HR0:0≤(244+192*L)*a.lam*width*Rm:=by positivity
    nlinarith only [HD0,HR0]
  have hDiam':=hRemDrop.trans hDiam
  have hFull:3*a.lam*a.canonicalBroadMassBudget ell Q L (a.data.N^(-(10:ℝ))) v width+
      16*a.lam*Dm^2*width≤a.data.N^(5*delta)*a.data.E+a.data.N^(2*delta)*a.data.E+a.data.E:=by
    unfold canonicalBroadMassBudget nativeConditionalLedgerBudget
    dsimp only [F1,Rm,loss,L,A,Dm,P] at htrace' htraceSaved hDiam' hCore hCutSmall hDnonneg ⊢
    norm_num only [Nat.cast_one,mul_one]
    nlinarith only [htrace',htraceSaved,hDiam',hCore,hCutSmall,hDnonneg]
  simp only [Real.rpow_zero,mul_one] at hnThree
  have hp25:=mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN (show 2*delta≤5*delta by linarith)) a.data.hE.le
  have hp15:=mul_le_mul_of_nonneg_right (Real.one_le_rpow hN (show 0≤5*delta by linarith)) a.data.hE.le
  have hsum:=mul_le_mul_of_nonneg_right hnThree (show 0≤a.data.N^(5*delta)*a.data.E by positivity)
  have he:a.data.N^delta*(a.data.N^(5*delta)*a.data.E)=a.data.N^(6*delta)*a.data.E:=by
    rw [←mul_assoc,←Real.rpow_add a.data.hN];congr 2;ring
  rw [he] at hsum
  exact hFull.trans (by nlinarith only [hp25,hp15,hsum])

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
