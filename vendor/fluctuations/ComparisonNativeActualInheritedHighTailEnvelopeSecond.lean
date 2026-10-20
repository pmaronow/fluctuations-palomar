module

public import ComparisonNativeActualShellHistoryThermalBounds
public import ComparisonNativeHighTailOmittedSite
public import ComparisonNativeHighTailComparisonEnvelope

@[expose] public section

noncomputable section
set_option maxHeartbeats 17000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_shell_history_original_high_envelope_second
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
          ClockTree.edgeBudget 0 as (fun j=>(nativeOriginalHighTailEnvelope n U M.bf M.hf as Cerr j)^2)≤
            (M.context.N^(-(actualMassSavingExponent m delta/32))*
              (M.xs^2/M.canonicalDirectTestBandScale))^2 := by
  have Hraw:=eventually_actual_shell_history_sampled_original_high_tail_second
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
  intro M T epsilon shell ts hb hh hsmall hW1 us hus
  filter_upwards [hnRaw M T epsilon shell ts hb hh hsmall hW1 us hus] with jGrid hgrid
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

end OAI.SKFluctuations.LaplaceWindowFormalization
