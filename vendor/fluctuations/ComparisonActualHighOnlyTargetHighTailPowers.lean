module

public import ComparisonActualHighOnlyTargetHighTailThermal
public import ComparisonNativeHighTailL1Transfer
public import ComparisonNativeHighTailOmittedSite
public import ComparisonNativeHighTailComparisonEnvelope
public import ComparisonSignedCavityHighProfileNearTwoAbsorption
public import ComparisonActualHighOnlyNaturalSourceCalibration
public import ComparisonActualHighOnlyCriticalScaleNumerics

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 13000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem native_high_tail_site_normalized_le_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0<C0) (hW1 : M.canonicalDirectTestBandScale≤1) :
    (1/M.data.N)/(M.xs^2/M.canonicalDirectTestBandScale)≤
      C0^2*M.data.N^(-(2:ℝ)/3-2*m) := by
  have hN:=M.data.hN
  have hx:=M.hxs
  have hW:=M.canonical_direct_test_band_pos
  have H:=M.canonical_high_mass_inverse_power hC0 2
  have H' : 1/(M.data.N^((1:ℝ)/3)*M.xs^2)≤C0^2*M.data.N^(-2*m) := by
    simpa only [Nat.cast_ofNat,show (2:ℝ)/6=1/3 by norm_num] using H
  have HE : (1/M.data.N)/(M.xs^2/M.canonicalDirectTestBandScale)=
      M.canonicalDirectTestBandScale*(M.data.N^(-(2:ℝ)/3)*
        (1/(M.data.N^((1:ℝ)/3)*M.xs^2))) := by
    have Hpow : M.data.N^(-(2:ℝ)/3)*M.data.N=
        M.data.N^((1:ℝ)/3) := by
      calc
        _=M.data.N^(-(2:ℝ)/3)*M.data.N^(1:ℝ) := by rw [Real.rpow_one]
        _=M.data.N^(-(2:ℝ)/3+1) := (Real.rpow_add hN _ _).symm
        _=M.data.N^((1:ℝ)/3) := by congr 1;norm_num
    field_simp
    simpa only [mul_comm,neg_div] using Hpow.symm
  rw [HE]
  have Hscaled:=mul_le_mul_of_nonneg_left H' (Real.rpow_nonneg hN.le (-(2:ℝ)/3))
  have Hfirst:=mul_le_of_le_one_left
    (show 0≤M.data.N^(-(2:ℝ)/3)*(1/(M.data.N^((1:ℝ)/3)*M.xs^2)) by positivity) hW1
  have Hfinal : M.data.N^(-(2:ℝ)/3)*(C0^2*M.data.N^(-2*m))=
      C0^2*M.data.N^(-(2:ℝ)/3-2*m) := by
    rw [mul_left_comm,←Real.rpow_add hN]
    congr 1
    ring_nf
  exact Hfirst.trans (Hscaled.trans_eq Hfinal)

theorem eventually_actual_minimum_high_tail_site_le_high_only
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0<C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.canonicalDirectTestBandScale≤1 →
        1/M.data.N≤M.data.N^(-(actualMassSavingExponent m delta/16))*
          (M.xs^2/M.canonicalDirectTestBandScale) := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0<eta:=actualMassSavingExponent_pos hm hdelta
  have he1:=(actualMassSavingExponent_bounds m delta).1
  have Hcoef:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^2) (d:=1)
      (q:=-(2:ℝ)/3-2*m) (r:=-eta/16) zero_lt_one (by dsimp only [eta] at *;linarith))
  filter_upwards [Hcoef] with n hn
  intro M hW1
  have H:=(native_high_tail_site_normalized_le_high_only M hC0 hW1).trans
    (show C0^2*M.data.N^(-(2:ℝ)/3-2*m)≤M.data.N^(-eta/16) by
      simpa only [ActualHighOnlyComparisonData.N,one_mul] using hn)
  have htarget : 0<M.xs^2/M.canonicalDirectTestBandScale:=by
    have :=M.hxs;have :=M.canonical_direct_test_band_pos;positivity
  simpa only [eta,neg_div] using (div_le_iff₀ htarget).mp H

end OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 24000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_regular_sampled_original_target_high_tail_second_high_only
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0<c) (hcouter : 2*cu*(Az+1)≤c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        M.xs^2≤Cs*laplaceComparisonStrength M.data.d M.lam M.xs →
        M.canonicalDirectTestBandScale≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀U : ℕ,U≤as.length → 2*c*M.xs≤partitionPoint 0 as U →
          ClockTree.edgeBudget 0 as
            (fun j=>if j<U then 0 else (nativeOriginalCutLowErrorRadius n M.bf M.hf as j)^2)≤
            M.data.N^(-(actualMassSavingExponent m delta/8))*
              (M.xs^4/M.canonicalDirectTestBandScale^2) := by
  have Htail:=eventually_actual_regular_target_thermal_tail_high_only
    (D:=D) (Cs:=Cs) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let eta:=actualMassSavingExponent m delta
  have heta : 0<eta:=actualMassSavingExponent_pos hm hdelta
  have Hcoef:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2) (d:=1) (q:=-eta/4) (r:=-eta/8)
      zero_lt_one (by linarith))
  filter_upwards [Htail,Hcoef] with n hnTail hnCoef
  intro M hclock hs hsxs hsomit hsmall hW1 us hus
  let q:=2*c*M.xs
  let A:=M.data.N^(-eta/8)*(M.xs^4/M.canonicalDirectTestBandScale^2)
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
  have hbf:=M.bf_monotone
  have hhf:=M.hf_monotone
  have Hmesh : Tendsto (fun j : ℕ=>((j+1:ℕ):ℝ)⁻¹*(3*physicalBApproximationConstant n M.bf M.hf+1)) atTop (𝓝 0) := by
    simpa only [zero_mul] using uniformMasses_mesh_tendsto.mul_const (3*physicalBApproximationConstant n M.bf M.hf+1)
  have Hfine:=Hmesh.eventually (eventually_le_nhds (show (0:ℝ)<A/2 by positivity))
  have Horiginal:=hnTail M hclock hs hsxs hsomit hsmall hW1 q le_rfl hq1
  have Hc : 2*M.data.N^(-eta/4)≤M.data.N^(-eta/8) := by
    simpa only [ActualHighOnlyComparisonData.N,mul_one,one_mul,neg_div] using hnCoef
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

theorem eventually_actual_regular_original_target_high_envelope_second_high_only
    (Bclock Temp Cf : ℝ) (hTemp : 0≤Temp) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0<c) (hcouter : 2*cu*(Az+1)≤c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        M.xs^2≤Cs*laplaceComparisonStrength M.data.d M.lam M.xs →
        M.canonicalDirectTestBandScale≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let Cerr:=Cavity.actualLowErrorComparisonConstant
          (4*Cf+2*Temp) Temp
        ∀U : ℕ,U≤as.length → 2*c*M.xs≤partitionPoint 0 as U →
          ClockTree.edgeBudget 0 as (fun j=>(nativeOriginalHighTailEnvelope n U M.bf M.hf as Cerr j)^2)≤
            (M.data.N^(-(actualMassSavingExponent m delta/32))*
              (M.xs^2/M.canonicalDirectTestBandScale))^2 := by
  have Hraw:=eventually_actual_regular_sampled_original_target_high_tail_second_high_only
    (D:=D) (Cs:=Cs) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Hsite:=eventually_actual_minimum_high_tail_site_le_high_only
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
  intro M hclock hs hsxs hsomit hsmall hW1 us hus
  filter_upwards [hnRaw M hclock hs hsxs hsomit hsmall hW1 us hus] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U hU hmass
  let as:=finiteCutMasses us jGrid
  let B:=M.data.N^(-eta/16)*(M.xs^2/M.canonicalDirectTestBandScale)
  have hB : 0≤B:=by have :=M.hxs;have :=M.canonical_direct_test_band_pos;dsimp [B];positivity
  have hsiteB : 1/M.data.N≤B := by simpa only [B,eta,neg_div] using hnSite M hW1
  have HBsq : B^2=M.data.N^(-eta/8)*(M.xs^4/M.canonicalDirectTestBandScale^2) := by
    have Hpow : (M.data.N^(-eta/16))^2=M.data.N^(-eta/8) := by
      rw [←Real.rpow_mul_natCast M.data.hN.le]
      congr 1
      push_cast
      ring_nf
    dsimp only [B]
    rw [mul_pow,Hpow,div_pow,←pow_mul]
  have Hsecond : ClockTree.edgeBudget 0 as
      (fun j=>if j<U then 0 else (nativeOriginalCutLowErrorRadius n M.bf M.hf as j)^2)≤B^2 := by
    rw [HBsq]
    simpa only [eta,neg_div] using hgrid U hU hmass
  have Henvelope:=native_high_tail_envelope_second_le (finiteCutMasses_ordered us hus jGrid)
    (finiteCutMasses_end us hus jGrid) U (nativeOriginalCutLowErrorRadius n M.bf M.hf as)
    (fun _=>Real.sqrt_nonneg _) hCerr (show 0≤1/M.data.N by positivity) hB hsiteB Hsecond
  have Hc : 2*Cerr*M.data.N^(-eta/16)≤M.data.N^(-eta/32) := by
    simpa only [ActualHighOnlyComparisonData.N,one_mul] using hnCoef
  have Hscaled:=mul_le_mul_of_nonneg_right Hc
    (show 0≤M.xs^2/M.canonicalDirectTestBandScale by have :=M.hxs;have :=M.canonical_direct_test_band_pos;positivity)
  have Hnorm : 2*Cerr*B≤M.data.N^(-eta/32)*(M.xs^2/M.canonicalDirectTestBandScale) := by
    simpa only [B,mul_assoc] using Hscaled
  simpa only [nativeOriginalHighTailEnvelope,Cerr,as,eta,ActualHighOnlyComparisonData.N,neg_div] using
    Henvelope.trans (pow_le_pow_left₀ (by positivity : 0≤2*Cerr*B) Hnorm 2)

theorem eventually_actual_regular_original_target_high_envelope_powers_high_only
    (Bclock Temp Cf : ℝ) (hTemp : 0≤Temp) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0<c) (hcouter : 2*cu*(Az+1)≤c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        M.xs^2≤Cs*laplaceComparisonStrength M.data.d M.lam M.xs →
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
            M.data.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  have Hsecond:=eventually_actual_regular_original_target_high_envelope_second_high_only
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Hscale:=(tendsto_add_atTop_nat 1).eventually
    (Cavity.eventually_actual_high_only_inverse_size_le_scale
      (D:=D) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (Bclock:=Bclock) hm hC0)
  let eta:=actualMassSavingExponent m delta
  have heta : 0<eta:=actualMassSavingExponent_pos hm hdelta
  have Hcoef:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2) (d:=1) (q:=-eta/128) (r:=-eta/256)
      zero_lt_one (by linarith))
  filter_upwards [Hsecond,Hscale,Hcoef] with n hnSecond hnScale hnCoef
  intro M hclock hs hsxs hsomit hsmall hW1 us hus
  filter_upwards [hnSecond M hclock hs hsxs hsomit hsmall hW1 us hus] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U hU hmass theta htheta1 htheta2 hdeficit
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let Cerr:=Cavity.actualLowErrorComparisonConstant
    (4*Cf+2*Temp) Temp
  let R:=nativeOriginalHighTailEnvelope n U M.bf M.hf as Cerr
  let B:=M.data.N^(-eta/32)*(M.xs^2/W)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have he : partitionEnd 0 as=1:=finiteCutMasses_end us hus jGrid
  have hW : 0<W:=M.canonical_direct_test_band_pos
  have hN1 : 1≤M.data.N:=by unfold ActualHighOnlyComparisonData.N;exact_mod_cast (by omega : 1≤n+1)
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
  have HBtheta : B^theta≤M.data.N^(-eta/128)*M.xs^2 := by
    have H:=Cavity.native_high_profile_near_two_absorption hN1 M.hxs M.canonical_direct_test_band_ge_scale
      (hnScale M) heta htheta1 htheta2 hdeficit
    simpa only [B,W,mul_div_assoc] using H
  have Hfirst:=native_edgeBudget_real_moment_le ho he R hR
    (show (0:ℝ)<1 by norm_num) (show (1:ℝ)≤2 by norm_num) hB Hmoment
  simp only [Real.rpow_one] at Hfirst
  have HWfirst:=mul_le_mul_of_nonneg_left Hfirst hW.le
  have HWB : W*B=M.data.N^(-eta/32)*M.xs^2 := by
    dsimp only [B]
    field_simp
  rw [HWB] at HWfirst
  have Hweak:=mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN1 (show -eta/32≤-eta/128 by linarith)) (sq_nonneg M.xs)
  have Hc : 2*M.data.N^(-eta/128)≤M.data.N^(-eta/256) := by
    simpa only [ActualHighOnlyComparisonData.N,one_mul] using hnCoef
  have Hrate:=mul_le_mul_of_nonneg_right Hc (sq_nonneg M.xs)
  have Htotal:=add_le_add (Htheta.trans HBtheta) (HWfirst.trans Hweak)
  dsimp only [R,W,Cerr,as,eta] at Htotal Hrate ⊢
  simp only [neg_div] at Htotal Hrate ⊢
  nlinarith only [Htotal,Hrate]

end OAI.SKFluctuations.LaplaceWindowFormalization
