module

public import ComparisonSignedCavityActualLowErrorSaving

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem actual_low_error_omitted_site_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    Tendsto (fun n=>(1/(dim n+1:ℕ):ℝ)/(a n).xs^2) atTop (𝓝 0) := by
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < (2:ℝ)/3+2*m by positivity)).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Hlim:=Hpow.const_mul (C0^2)
  simp only [mul_zero] at Hlim
  apply squeeze_zero (fun n=>by have hx:=(a n).hxs;positivity)
    (fun n=>actual_low_error_omitted_site_ratio_le (a n) hC0)
  simpa only [NativeOverlapContext.N,Function.comp_def] using Hlim

end OAI.SKFluctuations.Cavity
