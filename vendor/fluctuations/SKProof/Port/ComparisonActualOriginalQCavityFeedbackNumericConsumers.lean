module

public import ComparisonSignedCavityActualConstantSourceFeedbackAbsorption
public import SKProof.Port.ComparisonActualOriginalQCavityCategoryInterfaces
public import SKProof.Port.ComparisonActualOriginalQLowB0OriginalConstantConsumerSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0FullModulusConsumerSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0WeightedConsumerSourceAlong
public import SKProof.Port.ComparisonActualOriginalQCavityEarlyNumericConsumers
public import SKProof.Port.ComparisonActualOriginalQCavityTargetReadoutConsumers
public import SKProof.Port.ComparisonActualOriginalQPullbackFourProducers
public import SKProof.Port.ComparisonActualOriginalQCavityConsumerPrimitives
public import SKProof.Port.ComparisonActualOriginalQComparableBandStarBond
public import SKProof.Port.ComparisonActualOriginalQSquareConsumerActualSharpFourTerminalAlong
public import SKProof.Port.ComparisonActualOriginalQTargetRefinement

@[expose] public section
noncomputable section
set_option autoImplicit false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem nativeActualConstantSourceErrorEnvelope_nonneg_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp cK W : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {star U : ℕ} (hs : star<U) (hU : U≤as.length)
    (hW : 0<W) (hcK : 0<cK) (depth : ℕ) :
    0≤nativeActualConstantSourceErrorEnvelope_original_q M hs hU W Temp cK depth := by
  unfold nativeActualConstantSourceErrorEnvelope_original_q
  exact List.sum_nonneg (by intro a ha;obtain ⟨j,_,rfl⟩:=List.mem_map.mp ha;positivity)

theorem actual_minimum_constant_source_susceptibility_feedback_absorption_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Tstar cK cS gamma sharpSaving terminalSaving W Cs Cbond : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {star U : ℕ} (hs : star<U) (hU : U≤as.length)
    (ho : MassOrdered 0 as) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (hW : 0<W) (hxW : M.xs≤W) (hcK : 0<cK) (hcS : 0<cS)
    (hgamma : 0≤gamma) (hterminal : 0≤terminalSaving) (depth : ℕ)
    (Hsource : |nativeActualMinimumConstantJointSource_original_q M as star U|≤
      nativeActualConstantSourceKnownEnvelope_original_q M hs hU W Temp cK gamma sharpSaving terminalSaving depth)
    (Hsusc :
      let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |Tstar*chi^2-1|≤Cs*W^2+|nativeActualMinimumConstantJointSource_original_q M as star U|/(cS*W))
    (Hbond :
      let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |1-(M.sweepBf (partitionPoint 0 as star):ℝ)*chi^2|≤|Tstar*chi^2-1|+Cbond*W^2)
    (Hsmall : (Temp/cS)*(6*(depth:ℝ)/(Real.exp (-4*Temp)*cK))*
      ((n+1:ℕ):ℝ)^(-sharpSaving/2)≤1/2) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let feedback:=(Temp/cS)*(6*(depth:ℝ)/(Real.exp (-4*Temp)*cK))*((n+1:ℕ):ℝ)^(-sharpSaving/2)
    |Tstar*chi^2-1|≤
      2*(Cs+(Temp/cS)*(6*(depth:ℝ)+13)+feedback*Cbond)*W^2+
      2*((Temp/cS)*nativeActualConstantSourceErrorEnvelope_original_q M hs hU W Temp cK depth+
        |nativeActualConstantSourceRemainder_original_q M as star U|/(cS*W)) := by
  dsimp only at Hsusc Hbond ⊢
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let bstar:=(M.sweepBf (partitionPoint 0 as star):ℝ)
  let N:=((n+1:ℕ):ℝ)
  let feedback:=(Temp/cS)*(6*(depth:ℝ)/(Real.exp (-4*Temp)*cK))*N^(-sharpSaving/2)
  let E:=nativeActualConstantSourceErrorEnvelope_original_q M hs hU W Temp cK depth
  let R:=|nativeActualConstantSourceRemainder_original_q M as star U|
  have hbT : bstar≤Temp:=by
    have H:=M.inherited_total_clock_le htotal _ (partitionPoint_mem as ho star)
    dsimp only [bstar]
    linarith [NNReal.coe_nonneg (M.sweepHf (partitionPoint 0 as star))]
  have hTemp : 0≤Temp:=(NNReal.coe_nonneg _).trans hbT
  have hfeedback : 0≤feedback:=by dsimp only [feedback,N];positivity
  have Hcoarse:=Hsource.trans (nativeActualConstantSourceKnownEnvelope_le_coarse_original_q M hs hU
    hW hcK hgamma hterminal depth)
  have HD:=constant_source_coarse_division_le (b:=bstar) (T:=Temp) (c:=cS)
    (D:=Real.exp (-4*Temp)*cK) (q:=N^(-sharpSaving/2))
    (J:=|1-bstar*chi^2|) (E:=E) (R:=R) depth (NNReal.coe_nonneg _) hbT
    hW M.hxs.le hxW hcS (by positivity) (by dsimp only [N];positivity) (abs_nonneg _)
    (nativeActualConstantSourceErrorEnvelope_nonneg_original_q M hs hU hW hcK depth)
  have Hgap:=Hsusc.trans (add_le_add le_rfl
    ((div_le_div_of_nonneg_right Hcoarse (mul_pos hcS hW).le).trans HD))
  have HJ:=mul_le_mul_of_nonneg_left Hbond hfeedback
  have HE : |Tstar*chi^2-1|≤(Cs+(Temp/cS)*(6*(depth:ℝ)+13))*W^2+
      feedback*(|Tstar*chi^2-1|+Cbond*W^2)+(Temp/cS)*E+R/(cS*W):=by
    change _≤Cs*W^2+((Temp/cS)*((6*(depth:ℝ)/(Real.exp (-4*Temp)*cK))*
      N^(-sharpSaving/2)*|1-bstar*chi^2|+(6*(depth:ℝ)+13)*W^2+E)+R/(cS*W)) at Hgap
    dsimp only [feedback] at HJ
    nlinarith
  have HF:=susceptibility_absorption_with_literal_correction Hsmall
    (show |Tstar*chi^2-1|≤(Cs+(Temp/cS)*(6*(depth:ℝ)+13))*W^2+
      feedback*(|Tstar*chi^2-1|+Cbond*W^2)+((Temp/cS)*E+R/(cS*W)) by linarith [HE])
  exact HF

end OAI.SKFluctuations.Cavity

