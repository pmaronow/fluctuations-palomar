module

public import ComparisonNativeActualHighMassCriticalRates
public import ComparisonActualHighOnlyHighMassSharpScale
public import ComparisonActualHighOnlyCriticalScaleNumerics

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_direct_test_cap_strong_rate
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs) :
    (a.data.E/a.data.d^3)*(a.canonicalDirectTestBandScale^2/a.xs^4) ≤
      (Cs+1)^2*C0^3*a.data.N^(-3*m) := by
  have H:=mass_cap_strong_normalization a.data.hN a.data.hE a.data.hd a.hxs
    a.canonical_direct_test_band_pos.le (show 0 ≤ Cs+1 by linarith) a.hscale
    (a.canonical_direct_test_band_geometry hCs hsmall).1
  apply H.trans
  have HH:=mul_le_mul_of_nonneg_left (a.canonical_high_mass_critical_ratio hC0) (sq_nonneg (Cs+1))
  simpa only [mul_div_assoc,mul_assoc] using HH

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
