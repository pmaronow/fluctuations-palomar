module

public import ComparisonActualGeneralTargetContinuousModulus
public import ComparisonActualHighWallRadiusScalarIntegrability

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 20000000

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Cm Cr Ctaylor : ℝ}

theorem actual_original_target_mass_continuous_modulus
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (P : ℝ→ℝ) (hP : Continuous P) (hP0 : ∀x,0≤x→0≤P x)
    (hCr : 0≤Cr)
    (u : PositiveMass)
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (hu : u∈us)
    (U : ℕ→ℕ)
    (Hprice : ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let i:=retainedMassPrefixIndex u.val as
      i<U k ∧ U k≤as.length ∧
      |actualGeneralTargetOriginalMeanCorrection (n:=n) M.bf M.hf as i (U k)|≤
        Cm*M.data.d^4 ∧
      |actualGeneralTargetLongitudinalResponse (n:=n) M.bf M.hf as i (U k)|≤
        Cr*P (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)) ∧
      |actualGeneralTargetOriginalTaylorPart (n:=n) M.bf M.hf as i (U k)|≤
        Ctaylor*P (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))) :
    |orderedPathS (n+1) M.bf M.hf u.val-
      scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha)
        (actualMixedClock (n+1) M.bf M.hf u.val)|≤
      Cm*M.data.d^4+(2*M.data.T*Cr+Ctaylor)*
        P (Real.sqrt (orderedPathB (n+1) M.bf M.hf u.val-
          (orderedPathS (n+1) M.bf M.hf u.val)^2)+1/M.data.N) := by
  have H := actual_general_target_continuum_continuous_modulus M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)
    (M.data.root_field_zero M.alpha) M.data.hTpos M.data.hd.le hCr
    P hP hP0 (M.data.total_clock_le M.alpha) us hus u hu U Hprice
  simpa only [ActualHighWallData.scalarMassProfile,ActualHighWallData.N] using H

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
