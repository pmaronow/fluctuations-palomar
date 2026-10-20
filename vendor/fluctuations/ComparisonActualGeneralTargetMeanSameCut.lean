module

public import ComparisonActualGeneralTargetMeanBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

 theorem actual_general_target_mean_same_cut_cubic_of_original_reader_prices
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp d Cm Cr Ct : ℝ} (hd : 0 ≤ d) (hCr : 0 ≤ Cr)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ) (hi : i < U) (hU : U ≤ as.length)
    (Hmean : |actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i U| ≤ Cm*d^3)
    (Hresponse : |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i U| ≤ Cr*d^3)
    (HTaylor : |actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i U| ≤ Ct*d^3) :
    |nativePhysicalResourceCenter n bf hf as i-
      nativeOriginalScalarPairMean as (nativeContinuumMixedClock n bf hf as) i| ≤
        (Cm+2*Temp*Cr+Ct)*d^3 := by
  have Htransport : |actualGeneralTargetMeanTransportError (n:=n) bf hf as i U U| ≤ (0:ℝ)*d^3:=by
    simp [actualGeneralTargetMeanTransportError]
  have H:=actual_general_target_mean_cubic_of_original_reader_prices bf hf hbf hhf hd hCr
    htotal as i U U hi hU ho Hmean Hresponse Htransport HTaylor
  simpa only [add_zero] using H

end OAI.SKFluctuations.Cavity
