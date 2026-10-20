module

public import ComparisonNativeActualBroadMassNormalization
public import ComparisonActualHighOnlyMassBandScale

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
theorem canonical_mass_trace_log_le
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) :
    Real.log ((1+a.data.U)/a.data.U) ≤
      (1+Real.log (1+D^2))*Real.log a.data.N := by
  have hE : a.data.E ≤ D^2 := by
    have Hsqrt : 1 ≤ Real.sqrt a.data.N := (Real.one_le_sqrt).mpr hN
    have HE : a.data.E ≤ a.data.d^2 := by nlinarith [a.hupper,a.data.hE]
    exact HE.trans (pow_le_pow_left₀ a.data.hd.le a.hdD 2)
  have he : (1+a.data.U)/a.data.U=1+a.data.N*a.data.E := by
    unfold ActualHighOnlyComparisonData.U comparisonSmallMass
    field_simp [a.data.hE.ne']
    ring
  have hsize : 1+a.data.N*a.data.E ≤ a.data.N*(1+D^2) := by
    nlinarith [mul_le_mul_of_nonneg_left hE a.data.hN.le]
  have hNE : 0 < a.data.N*a.data.E := mul_pos a.data.hN a.data.hE
  have hl := Real.log_le_log (show 0 < 1+a.data.N*a.data.E by linarith) hsize
  rw [he]
  apply hl.trans
  rw [Real.log_mul a.data.hN.ne' (by positivity : (1+D^2:ℝ)≠0)]
  have hlogD : 0 ≤ Real.log (1+D^2) := Real.log_nonneg (by nlinarith [sq_nonneg D])
  nlinarith [mul_nonneg hlogD (sub_nonneg.mpr hlog)]

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
