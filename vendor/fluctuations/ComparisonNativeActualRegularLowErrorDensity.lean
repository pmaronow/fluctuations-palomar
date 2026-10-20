module

public import ComparisonNativeActualLowErrorDensityProducer
public import ComparisonNativeActualRegularStrongInitialMassError

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum

theorem actualOriginalLowErrorDensitySaving_regular_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (a : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn : ℕ in atTop,
      (a n).xs^2 ≤ Cs*laplaceComparisonStrength (a n).context.d (a n).lam (a n).xs)
    (hWlim : Tendsto (fun n=>(a n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hclock : ∀n,NativePullbackClockRegularity (a n).alpha.val.val (a n).b (a n).h 0 1)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(a n).actualOriginalLowErrorDensitySaving C) atTop (𝓝 0) := by
  have HI:=regular_minimum_strong_initial_mass_error_ratio_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs a hsmall hWlim hclock C hC
  have Hinv : Tendsto (fun n : ℕ=>1/((n+1:ℕ):ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  simpa only [actualOriginalLowErrorDensitySaving,add_zero] using HI.add Hinv

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
