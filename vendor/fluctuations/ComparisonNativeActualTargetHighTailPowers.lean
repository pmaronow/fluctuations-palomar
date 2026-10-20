module

public import ComparisonNativeActualRegularTargetHighTail
public import ComparisonNativeHighTailL1Transfer
public import ComparisonNativeHighTailOmittedSite
public import ComparisonNativeHighTailComparisonEnvelope
public import ComparisonSignedCavityHighProfileNearTwoAbsorption
public import ComparisonSignedCavityActualFactorRawCalibration

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_regular_sampled_original_target_high_tail_second
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0<c) (hcouter : 2*cu*(Az+1)≤c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.xs^2≤Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀U : ℕ,U≤as.length → 2*c*M.xs≤partitionPoint 0 as U →
          ClockTree.edgeBudget 0 as
            (fun j=>if j<U then 0 else (nativeOriginalCutLowErrorRadius n M.bf M.hf as j)^2)≤
            M.context.N^(-(actualMassSavingExponent m delta/8))*
              (M.xs^4/M.canonicalDirectTestBandScale^2) := by
  have Htail:=eventually_actual_regular_target_thermal_tail
    (D:=D) (Cs:=Cs) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let eta:=actualMassSavingExponent m delta
  have heta : 0<eta:=actualMassSavingExponent_pos hm hdelta
  have Hcoef:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2) (d:=1) (q:=-eta/4) (r:=-eta/8)
      zero_lt_one (by linarith))
  filter_upwards [Htail,Hcoef] with n hnTail hnCoef
  intro M hclock hsmall hW1 us hus
  let q:=2*c*M.xs
  let A:=M.context.N^(-eta/8)*(M.xs^4/M.canonicalDirectTestBandScale^2)
  have hA : 0<A:=by have :=M.hxs;have :=M.canonical_direct_test_band_pos;dsimp [A];positivity
  have hq0 : 0≤q:=by have :=M.hxs;dsimp [q];positivity
  by_cases hq1 : q≤1
  swap
  · apply Eventually.of_forall
    intro jGrid
    dsimp only
    intro U hU hqU
    exact False.elim (hq1 (hqU.trans (partitionPoint_mem (finiteCutMasses us jGrid)
      (finiteCutMasses_ordered us hus jGrid) U).2))
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf:=toNNReal_monotoneOn had.1
  have hhf:=toNNReal_monotoneOn had.2.1
  have Hmesh : Tendsto (fun j : ℕ=>((j+1:ℕ):ℝ)⁻¹*(3*physicalBApproximationConstant n M.bf M.hf+1)) atTop (𝓝 0) := by
    simpa only [zero_mul] using uniformMasses_mesh_tendsto.mul_const (3*physicalBApproximationConstant n M.bf M.hf+1)
  have Hfine:=Hmesh.eventually (eventually_le_nhds (show (0:ℝ)<A/2 by positivity))
  have Horiginal:=hnTail M hclock hsmall hW1 q le_rfl hq1
  have Hc : 2*M.context.N^(-eta/4)≤M.context.N^(-eta/8) := by
    simpa only [NativeOverlapContext.N,mul_one,one_mul,neg_div] using hnCoef
  have Hrate:=mul_le_mul_of_nonneg_right Hc
    (show 0≤M.xs^4/M.canonicalDirectTestBandScale^2 by positivity)
  have Horiginal' : (∫s in q..1,orderedPathB (n+1) M.bf M.hf s-(orderedPathS (n+1) M.bf M.hf s)^2)≤A/2 := by
    dsimp only [A,eta] at Hrate ⊢
    simp only [neg_div] at Hrate Horiginal ⊢
    linarith only [Horiginal,Hrate]
  filter_upwards [Hfine] with jGrid hjGrid
  dsimp only
  intro U hU hqU
  have Hsample:=native_original_high_second_edgeBudget_le_thermal_add_mesh n M.bf M.hf hbf hhf
    (finiteCutMasses_ordered us hus jGrid) (finiteCutMasses_end us hus jGrid)
    (finiteCutMasses_mesh us hus jGrid) ⟨hq0,hq1⟩ U hU hqU
  dsimp only [A,eta] at hjGrid Horiginal'
  simp only [neg_div] at hjGrid Horiginal' ⊢
  linarith only [Hsample,Horiginal',hjGrid]

theorem eventually_actual_regular_original_target_high_envelope_second
    (Bclock Temp Cf : ℝ) (hTemp : 0≤Temp) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0<c) (hcouter : 2*cu*(Az+1)≤c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.xs^2≤Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let Cerr:=Cavity.actualLowErrorComparisonConstant
          (4*Cf+2*Temp) Temp
        ∀U : ℕ,U≤as.length → 2*c*M.xs≤partitionPoint 0 as U →
          ClockTree.edgeBudget 0 as (fun j=>(nativeOriginalHighTailEnvelope n U M.bf M.hf as Cerr j)^2)≤
            (M.context.N^(-(actualMassSavingExponent m delta/32))*
              (M.xs^2/M.canonicalDirectTestBandScale))^2 := by
  have Hraw:=eventually_actual_regular_sampled_original_target_high_tail_second
    (D:=D) (Cs:=Cs) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Hsite:=eventually_actual_minimum_high_tail_site_le
    (D:=D) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) Bclock hm hdelta hC0
  let eta:=actualMassSavingExponent m delta
  let Cerr:=Cavity.actualLowErrorComparisonConstant
    (4*Cf+2*Temp) Temp
  have hCerr : 0≤Cerr:=Cavity.actualLowErrorComparisonConstant_nonneg _ hTemp
  have heta : 0<eta:=actualMassSavingExponent_pos hm hdelta
  have Hcoef:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2*Cerr) (d:=1) (q:=-eta/16) (r:=-eta/32)
      zero_lt_one (by linarith))
  filter_upwards [Hraw,Hsite,Hcoef] with n hnRaw hnSite hnCoef
  intro M hclock hsmall hW1 us hus
  filter_upwards [hnRaw M hclock hsmall hW1 us hus] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U hU hmass
  let as:=finiteCutMasses us jGrid
  let B:=M.context.N^(-eta/16)*(M.xs^2/M.canonicalDirectTestBandScale)
  have hB : 0≤B:=by have :=M.hxs;have :=M.canonical_direct_test_band_pos;dsimp [B];positivity
  have hsiteB : 1/M.context.N≤B := by simpa only [B,eta,neg_div] using hnSite M hW1
  have HBsq : B^2=M.context.N^(-eta/8)*(M.xs^4/M.canonicalDirectTestBandScale^2) := by
    have Hpow : (M.context.N^(-eta/16))^2=M.context.N^(-eta/8) := by
      rw [←Real.rpow_mul_natCast M.context.hN.le]
      congr 1
      push_cast
      ring
    dsimp only [B]
    rw [mul_pow,Hpow,div_pow,←pow_mul]
  have Hsecond : ClockTree.edgeBudget 0 as
      (fun j=>if j<U then 0 else (nativeOriginalCutLowErrorRadius n M.bf M.hf as j)^2)≤B^2 := by
    rw [HBsq]
    simpa only [eta,neg_div] using hgrid U hU hmass
  have Henvelope:=native_high_tail_envelope_second_le (finiteCutMasses_ordered us hus jGrid)
    (finiteCutMasses_end us hus jGrid) U (nativeOriginalCutLowErrorRadius n M.bf M.hf as)
    (fun _=>Real.sqrt_nonneg _) hCerr (show 0≤1/M.context.N by positivity) hB hsiteB Hsecond
  have Hc : 2*Cerr*M.context.N^(-eta/16)≤M.context.N^(-eta/32) := by
    simpa only [NativeOverlapContext.N,one_mul] using hnCoef
  have Hscaled:=mul_le_mul_of_nonneg_right Hc
    (show 0≤M.xs^2/M.canonicalDirectTestBandScale by have :=M.hxs;have :=M.canonical_direct_test_band_pos;positivity)
  have Hnorm : 2*Cerr*B≤M.context.N^(-eta/32)*(M.xs^2/M.canonicalDirectTestBandScale) := by
    simpa only [B,mul_assoc] using Hscaled
  simpa only [nativeOriginalHighTailEnvelope,Cerr,as,eta,NativeOverlapContext.N,neg_div] using
    Henvelope.trans (pow_le_pow_left₀ (by positivity : 0≤2*Cerr*B) Hnorm 2)

theorem eventually_actual_regular_original_target_high_envelope_powers
    (Bclock Temp Cf : ℝ) (hTemp : 0≤Temp) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0<c) (hcouter : 2*cu*(Az+1)≤c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.xs^2≤Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let Cerr:=Cavity.actualLowErrorComparisonConstant
          (4*Cf+2*Temp) Temp
        ∀U : ℕ,U≤as.length → 2*c*M.xs≤partitionPoint 0 as U →
        ∀theta : ℝ,1≤theta → theta≤2 → 2-theta≤actualMassSavingExponent m delta/128 →
          ClockTree.edgeBudget 0 as (fun j=>(nativeOriginalHighTailEnvelope n U M.bf M.hf as Cerr j)^theta)+
            M.canonicalDirectTestBandScale*ClockTree.edgeBudget 0 as
              (nativeOriginalHighTailEnvelope n U M.bf M.hf as Cerr)≤
            M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  have Hsecond:=eventually_actual_regular_original_target_high_envelope_second
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
  intro M hclock hsmall hW1 us hus
  filter_upwards [hnSecond M hclock hsmall hW1 us hus] with jGrid hgrid
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
