module

public import ComparisonSignedCavityActualTargetGCutResponseAlong
public import SKProof.Port.ComparisonActualOriginalQPullbackFourProducers
public import SKProof.Port.ComparisonActualOriginalQTargetGCutEnvelope
public import SKProof.Port.ComparisonActualOriginalQTargetGCutDensity
public import SKProof.Port.ComparisonActualOriginalQInheritedTargetScalarCutClock
public import SKProof.Port.ComparisonActualOriginalQTargetGCutResponse
public import ComparisonSignedCavityActualTargetGCutResponse

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_target_G_cut_thermal_comparison_along_original_q
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (Bclock Temp Cf Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C R : ℝ,0 < C ∧ 0 < R ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs → ActualOriginalQSmallSourceClocks M Temp Cf→M.xs≤1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i U V : ℕ),i < U→U≤V→V≤as.length→
        ∀x W : ℝ,M.xs≤x→partitionPoint 0 as i≤Ccut*x→
          M.xs≤W→partitionPoint 0 as V≤Couter*W→
          let band:=(∫u in partitionPoint 0 as U..partitionPoint 0 as V,
            Real.sqrt (orderedPathB (dim n+1) M.sweepBf M.sweepHf u-(orderedPathS (dim n+1) M.sweepBf M.sweepHf u)^2))+3/(dim n+1:ℕ)
          let tail:=(∫u in partitionPoint 0 as V..1,
            Real.sqrt (orderedPathB (dim n+1) M.sweepBf M.sweepHf u-(orderedPathS (dim n+1) M.sweepBf M.sweepHf u)^2))+3/(dim n+1:ℕ)
          abs (nativeActualTargetLongitudinalResponse_original_q M as i U-nativeActualTargetLongitudinalResponse_original_q M as i V)≤
              C*x*(band+R*W*tail) ∧
          abs (nativeActualTargetConditionalResponse_original_q M as i U-nativeActualTargetConditionalResponse_original_q M as i V)≤
              C*x*(band+R*W*tail) := by
  obtain ⟨C,R,hC,hR,H⟩:=eventually_actual_minimum_inherited_target_G_cut_thermal_comparison_original_q
    (D:=D) Bclock Temp Cf Ccut Couter hTemp hCf hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  exact ⟨C,R,hC,hR,hdim.eventually H⟩

end OAI.SKFluctuations.Cavity
