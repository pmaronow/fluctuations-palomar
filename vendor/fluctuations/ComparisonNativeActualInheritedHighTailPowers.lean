module

public import ComparisonNativeActualInheritedHighTailEnvelopeSecond
public import ComparisonSignedCavityHighProfileNearTwoAbsorption
public import ComparisonSignedCavityActualFactorRawCalibration

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_shell_history_original_high_envelope_powers
    (Bclock Temp Cf : ℝ) (hTemp : 0≤Temp) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0<c) (hcouter : 2*cu*(Az+1)≤c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (T epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        (∀u,M.b u=historyMatrixClock T epsilon shell ts u) → (∀u,M.h u=historyFieldClock ts u) →
        M.xs^2≤Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let Cerr:=Cavity.actualLowErrorComparisonConstant
          (4*Cf+2*Temp) Temp
        ∀U : ℕ,U≤as.length → 2*c*M.canonicalDirectTestBandScale≤partitionPoint 0 as U →
        ∀theta : ℝ,1≤theta → theta≤2 → 2-theta≤actualMassSavingExponent m delta/128 →
          ClockTree.edgeBudget 0 as (fun j=>(nativeOriginalHighTailEnvelope n U M.bf M.hf as Cerr j)^theta)+
            M.canonicalDirectTestBandScale*ClockTree.edgeBudget 0 as
              (nativeOriginalHighTailEnvelope n U M.bf M.hf as Cerr)≤
            M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  have Hsecond:=eventually_actual_shell_history_original_high_envelope_second
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Hscale:=(tendsto_add_atTop_nat 1).eventually
    (Cavity.eventually_actual_minimum_inverse_size_le_scale
      (D:=D) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) Bclock hm hC0)
  let eta:=actualMassSavingExponent m delta
  have heta : 0<eta:=actualMassSavingExponent_pos hm hdelta
  have Hcoef:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2) (d:=1) (q:=-eta/128) (r:=-eta/256)
      zero_lt_one (by linarith))
  filter_upwards [Hsecond,Hscale,Hcoef] with n hnSecond hnScale hnCoef
  intro M T epsilon shell ts hb hh hsmall hW1 us hus
  filter_upwards [hnSecond M T epsilon shell ts hb hh hsmall hW1 us hus] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U hU hmass theta htheta1 htheta2 hdeficit
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let Cerr:=Cavity.actualLowErrorComparisonConstant
    (4*Cf+2*Temp) Temp
  let R:=nativeOriginalHighTailEnvelope n U M.bf M.hf as Cerr
  let B:=M.context.N^(-eta/32)*(M.xs^2/W)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have he : partitionEnd 0 as=1:=finiteCutMasses_end us hus jGrid
  have hW : 0<W:=M.canonical_direct_test_band_pos
  have hN1 : 1≤M.context.N:=by unfold NativeOverlapContext.N;exact_mod_cast (by omega : 1≤n+1)
  have hB : 0≤B:=by dsimp [B];positivity
  have hCerr : 0≤Cerr:=Cavity.actualLowErrorComparisonConstant_nonneg _ hTemp
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighTailEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg hCerr (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hmoment : ClockTree.edgeBudget 0 as (fun j=>(R j)^2)≤B^2 := by
    simpa only [R,B,W,Cerr,eta,neg_div] using hgrid U hU hmass
  have Htheta:=native_edgeBudget_real_moment_le ho he R hR
    (show 0<theta from zero_lt_one.trans_le htheta1) htheta2 hB Hmoment
  have HBtheta : B^theta≤M.context.N^(-eta/128)*M.xs^2 := by
    have H:=Cavity.native_high_profile_near_two_absorption hN1 M.hxs M.canonical_direct_test_band_ge_scale
      (hnScale M) heta htheta1 htheta2 hdeficit
    simpa only [B,W,mul_div_assoc] using H
  have Hfirst:=native_edgeBudget_real_moment_le ho he R hR
    (show (0:ℝ)<1 by norm_num) (show (1:ℝ)≤2 by norm_num) hB Hmoment
  simp only [Real.rpow_one] at Hfirst
  have HWfirst:=mul_le_mul_of_nonneg_left Hfirst hW.le
  have HWB : W*B=M.context.N^(-eta/32)*M.xs^2 := by
    dsimp only [B]
    field_simp
  rw [HWB] at HWfirst
  have Hweak:=mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN1 (show -eta/32≤-eta/128 by linarith)) (sq_nonneg M.xs)
  have Hc : 2*M.context.N^(-eta/128)≤M.context.N^(-eta/256) := by
    simpa only [NativeOverlapContext.N,one_mul] using hnCoef
  have Hrate:=mul_le_mul_of_nonneg_right Hc (sq_nonneg M.xs)
  have Htotal:=add_le_add (Htheta.trans HBtheta) (HWfirst.trans Hweak)
  dsimp only [R,W,Cerr,as,eta] at Htotal Hrate ⊢
  simp only [neg_div] at Htotal Hrate ⊢
  nlinarith only [Htotal,Hrate]

end OAI.SKFluctuations.LaplaceWindowFormalization
